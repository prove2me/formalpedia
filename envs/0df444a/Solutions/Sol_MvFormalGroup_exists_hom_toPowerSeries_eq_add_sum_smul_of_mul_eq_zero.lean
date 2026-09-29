-- Prove2me | solution 1 for MvFormalGroup.exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/787bdafe-10da-53f2-a73b-4046c850907a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u

namespace TSQ

section Generic

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

abbrev Xl (n : ℕ) (R : Type u) [CommRing R] : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R :=
  fun l => X (Sum.inl l)

abbrev Xr (n : ℕ) (R : Type u) [CommRing R] : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R :=
  fun l => X (Sum.inr l)

theorem constantCoeff_Xl (i : Fin n) : (Xl n R i).constantCoeff = 0 := constantCoeff_X _
theorem constantCoeff_Xr (i : Fin n) : (Xr n R i).constantCoeff = 0 := constantCoeff_X _

def app {τ : Type} (T : Fin n → MvPowerSeries (Fin n) R) (a : Fin n → MvPowerSeries τ R) :
    Fin n → MvPowerSeries τ R :=
  fun j => subst a (T j)

theorem app_apply {τ : Type} (T : Fin n → MvPowerSeries (Fin n) R)
    (a : Fin n → MvPowerSeries τ R) (j : Fin n) : app T a j = subst a (T j) := rfl

theorem constantCoeff_app {τ : Type} {T : Fin n → MvPowerSeries (Fin n) R}
    {a : Fin n → MvPowerSeries τ R}
    (hT : ∀ j, (T j).constantCoeff = 0) (ha : ∀ j, (a j).constantCoeff = 0) (j : Fin n) :
    (app T a j).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha (hT j)

theorem app_app {τ : Type} {T U : Fin n → MvPowerSeries (Fin n) R}
    {a : Fin n → MvPowerSeries τ R}
    (hU : ∀ j, (U j).constantCoeff = 0) (ha : ∀ j, (a j).constantCoeff = 0) :
    app (app T U) a = app T (app U a) := by
  funext j
  simp only [app_apply]
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hU)
    (hasSubst_of_constantCoeff_zero ha)]
  rfl

theorem app_X_left {τ : Type} (a : Fin n → MvPowerSeries τ R)
    (ha : ∀ j, (a j).constantCoeff = 0) :
    app (fun i => (X i : MvPowerSeries (Fin n) R)) a = a := by
  funext j
  simp only [app_apply]
  rw [subst_X (hasSubst_of_constantCoeff_zero ha)]

theorem app_X_right (T : Fin n → MvPowerSeries (Fin n) R) :
    app T (fun i => (X i : MvPowerSeries (Fin n) R)) = T := by
  funext j
  simp only [app_apply]
  rw [subst_self]
  rfl

theorem map_app {τ : Type} (f : R →+* S) {T : Fin n → MvPowerSeries (Fin n) R}
    {a : Fin n → MvPowerSeries τ R} (ha : ∀ j, (a j).constantCoeff = 0) (j : Fin n) :
    MvPowerSeries.map f (app T a j) =
      app (fun i => MvPowerSeries.map f (T i)) (fun i => MvPowerSeries.map f (a i)) j := by
  simp only [app_apply]
  rw [map_subst (hasSubst_of_constantCoeff_zero ha)]

theorem map_Xl (f : R →+* S) (l : Fin n) : MvPowerSeries.map f (Xl n R l) = Xl n S l := by
  simp [Xl]

theorem map_Xr (f : R →+* S) (l : Fin n) : MvPowerSeries.map f (Xr n R l) = Xr n S l := by
  simp [Xr]

theorem map_elim_app_Xl_Xr (f : R →+* S) (T : Fin n → MvPowerSeries (Fin n) R)
    (s : Fin n ⊕ Fin n) :
    MvPowerSeries.map f (Sum.elim (app T (Xl n R)) (app T (Xr n R)) s) =
      Sum.elim (app (fun i => MvPowerSeries.map f (T i)) (Xl n S))
        (app (fun i => MvPowerSeries.map f (T i)) (Xr n S)) s := by
  rcases s with j | j
  · simp only [Sum.elim_inl]
    rw [map_app f (constantCoeff_Xl (R := R))]
    congr 1
    funext l
    exact map_Xl f l
  · simp only [Sum.elim_inr]
    rw [map_app f (constantCoeff_Xr (R := R))]
    congr 1
    funext l
    exact map_Xr f l

theorem map_subst_of_constantCoeff {σ τ : Type} [Finite σ] (f : R →+* S)
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, (a s).constantCoeff = 0) (g : MvPowerSeries σ R) :
    MvPowerSeries.map f (subst a g) =
      subst (fun s => MvPowerSeries.map f (a s)) (MvPowerSeries.map f g) :=
  map_subst (hasSubst_of_constantCoeff_zero ha) g

end Generic

section LawApp

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

def lawApp {τ : Type} (L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R)
    (a b : Fin n → MvPowerSeries τ R) : Fin n → MvPowerSeries τ R :=
  fun k => subst (Sum.elim a b) (L k)

theorem lawApp_apply {τ : Type} (L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R)
    (a b : Fin n → MvPowerSeries τ R) (k : Fin n) :
    lawApp L a b k = subst (Sum.elim a b) (L k) := rfl

theorem elim_constantCoeff {τ : Type} {a b : Fin n → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    ∀ s, (Sum.elim a b s).constantCoeff = 0 := by
  rintro (j | j)
  exacts [ha j, hb j]

theorem constantCoeff_lawApp {τ : Type} {L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R}
    {a b : Fin n → MvPowerSeries τ R} (hL : ∀ k, (L k).constantCoeff = 0)
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (k : Fin n) :
    (lawApp L a b k).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim ha hb) (elim_constantCoeff ha hb) (hL k)

theorem lawApp_Xl_Xr (L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R) :
    lawApp L (Xl n R) (Xr n R) = L := by
  funext k
  rw [lawApp_apply]
  have : (Sum.elim (Xl n R) (Xr n R)) = (X : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) R) := by
    funext s; rcases s with j | j <;> rfl
  rw [this, subst_self]
  rfl

theorem subst_elim_app_Xl {τ : Type} {T : Fin n → MvPowerSeries (Fin n) R}
    {a b : Fin n → MvPowerSeries τ R} (hT : ∀ j, (T j).constantCoeff = 0)
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (j : Fin n) :
    subst (Sum.elim a b) (app T (Xl n R) j) = app T a j := by
  rw [app_apply, app_apply,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (constantCoeff_Xl (R := R)))
      (MvFormalGroup.hasSubst_elim ha hb)]
  congr 1
  funext l
  exact subst_X (MvFormalGroup.hasSubst_elim ha hb) (Sum.inl l)

theorem subst_elim_app_Xr {τ : Type} {T : Fin n → MvPowerSeries (Fin n) R}
    {a b : Fin n → MvPowerSeries τ R} (hT : ∀ j, (T j).constantCoeff = 0)
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (j : Fin n) :
    subst (Sum.elim a b) (app T (Xr n R) j) = app T b j := by
  rw [app_apply, app_apply,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (constantCoeff_Xr (R := R)))
      (MvFormalGroup.hasSubst_elim ha hb)]
  congr 1
  funext l
  exact subst_X (MvFormalGroup.hasSubst_elim ha hb) (Sum.inr l)

theorem subst_elim_lawApp_app {τ : Type} {L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R}
    {T : Fin n → MvPowerSeries (Fin n) R} {a b : Fin n → MvPowerSeries τ R}
    (hT : ∀ j, (T j).constantCoeff = 0)
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (k : Fin n) :
    subst (Sum.elim a b) (lawApp L (app T (Xl n R)) (app T (Xr n R)) k) =
      lawApp L (app T a) (app T b) k := by
  rw [lawApp_apply, lawApp_apply,
    subst_comp_subst_apply
      (MvFormalGroup.hasSubst_elim (constantCoeff_app hT (constantCoeff_Xl (R := R)))
        (constantCoeff_app hT (constantCoeff_Xr (R := R))))
      (MvFormalGroup.hasSubst_elim ha hb)]
  congr 1
  funext s
  rcases s with j | j
  · exact subst_elim_app_Xl hT ha hb j
  · exact subst_elim_app_Xr hT ha hb j

theorem subst_elim_lawApp {τ τ' : Type} {L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R}
    {a₀ b₀ : Fin n → MvPowerSeries τ R} (ha₀ : ∀ j, (a₀ j).constantCoeff = 0)
    (hb₀ : ∀ j, (b₀ j).constantCoeff = 0) {c : τ → MvPowerSeries τ' R} (hc : HasSubst c)
    (k : Fin n) :
    subst c (lawApp L a₀ b₀ k) = lawApp L (fun j => subst c (a₀ j)) (fun j => subst c (b₀ j)) k := by
  rw [lawApp_apply, lawApp_apply,
    subst_comp_subst_apply (MvFormalGroup.hasSubst_elim ha₀ hb₀) hc]
  congr 1
  funext s
  rcases s with j | j <;> rfl

theorem map_lawApp {τ : Type} (f : R →+* S) (L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R)
    {a b : Fin n → MvPowerSeries τ R} (ha : ∀ j, (a j).constantCoeff = 0)
    (hb : ∀ j, (b j).constantCoeff = 0) (k : Fin n) :
    MvPowerSeries.map f (lawApp L a b k) =
      lawApp (fun i => MvPowerSeries.map f (L i)) (fun j => MvPowerSeries.map f (a j))
        (fun j => MvPowerSeries.map f (b j)) k := by
  rw [lawApp_apply, lawApp_apply, map_subst (MvFormalGroup.hasSubst_elim ha hb)]
  congr 1
  funext s
  rcases s with j | j <;> rfl

theorem coeff_single_lawApp {τ : Type} (F : MvFormalGroup n R)
    {a b : Fin n → MvPowerSeries τ R} (ha : ∀ j, (a j).constantCoeff = 0)
    (hb : ∀ j, (b j).constantCoeff = 0) (k : Fin n) (t : τ) :
    coeff (Finsupp.single t 1) (lawApp F.toPowerSeries a b k) =
      coeff (Finsupp.single t 1) (a k) + coeff (Finsupp.single t 1) (b k) := by
  classical
  rw [lawApp_apply, MvFormalGroup.coeff_single_subst (elim_constantCoeff ha hb),
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem coeff_inl_app_Xl {T : Fin n → MvPowerSeries (Fin n) R}
    (hT : ∀ j, (T j).constantCoeff = 0) (k j : Fin n) :
    coeff (Finsupp.single (Sum.inl j) 1) (app T (Xl n R) k) = coeff (Finsupp.single j 1) (T k) := by
  classical
  rw [app_apply, MvFormalGroup.coeff_single_subst (constantCoeff_Xl (R := R))]
  simp only [Xl, coeff_index_single_X, Sum.inl.injEq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem coeff_inl_app_Xr {T : Fin n → MvPowerSeries (Fin n) R}
    (hT : ∀ j, (T j).constantCoeff = 0) (k j : Fin n) :
    coeff (Finsupp.single (Sum.inl j) 1) (app T (Xr n R) k) = 0 := by
  classical
  rw [app_apply, MvFormalGroup.coeff_single_subst (constantCoeff_Xr (R := R))]
  simp only [Xr, coeff_index_single_X, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero]

theorem coeff_inr_app_Xl {T : Fin n → MvPowerSeries (Fin n) R}
    (hT : ∀ j, (T j).constantCoeff = 0) (k j : Fin n) :
    coeff (Finsupp.single (Sum.inr j) 1) (app T (Xl n R) k) = 0 := by
  classical
  rw [app_apply, MvFormalGroup.coeff_single_subst (constantCoeff_Xl (R := R))]
  simp only [Xl, coeff_index_single_X, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero]

theorem coeff_inr_app_Xr {T : Fin n → MvPowerSeries (Fin n) R}
    (hT : ∀ j, (T j).constantCoeff = 0) (k j : Fin n) :
    coeff (Finsupp.single (Sum.inr j) 1) (app T (Xr n R) k) = coeff (Finsupp.single j 1) (T k) := by
  classical
  rw [app_apply, MvFormalGroup.coeff_single_subst (constantCoeff_Xr (R := R))]
  simp only [Xr, coeff_index_single_X, Sum.inr.injEq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

end LawApp

section Transport

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

def transportT (L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R)
    (Φ Ψ : Fin n → MvPowerSeries (Fin n) R) : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R :=
  app Ψ (lawApp L (app Φ (Xl n R)) (app Φ (Xr n R)))

theorem transportT_def (L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R)
    (Φ Ψ : Fin n → MvPowerSeries (Fin n) R) :
    transportT L Φ Ψ = app Ψ (lawApp L (app Φ (Xl n R)) (app Φ (Xr n R))) := rfl

variable {L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R} {Φ Ψ : Fin n → MvPowerSeries (Fin n) R}

theorem constantCoeff_lawApp_app (hL : ∀ k, (L k).constantCoeff = 0)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) :
    ∀ k, (lawApp L (app Φ (Xl n R)) (app Φ (Xr n R)) k).constantCoeff = 0 :=
  constantCoeff_lawApp hL (constantCoeff_app hΦ0 (constantCoeff_Xl (R := R)))
    (constantCoeff_app hΦ0 (constantCoeff_Xr (R := R)))

theorem constantCoeff_transportT (hL : ∀ k, (L k).constantCoeff = 0)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0) (i : Fin n) :
    (transportT L Φ Ψ i).constantCoeff = 0 :=
  constantCoeff_app hΨ0 (constantCoeff_lawApp_app hL hΦ0) i

theorem lawApp_transportT (hL : ∀ k, (L k).constantCoeff = 0)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) {τ : Type} {a b : Fin n → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    lawApp (transportT L Φ Ψ) a b = app Ψ (lawApp L (app Φ a) (app Φ b)) := by
  funext i
  rw [lawApp_apply, transportT_def, app_apply, app_apply,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (constantCoeff_lawApp_app hL hΦ0))
      (MvFormalGroup.hasSubst_elim ha hb)]
  congr 1
  funext k
  exact subst_elim_lawApp_app hΦ0 ha hb k

theorem app_app_cancel (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0) (hΦΨ : ∀ i, subst Ψ (Φ i) = X i)
    {τ : Type} {c : Fin n → MvPowerSeries τ R} (hc : ∀ j, (c j).constantCoeff = 0) :
    app Φ (app Ψ c) = c := by
  rw [← app_app hΨ0 hc]
  have : app Φ Ψ = fun i => (X i : MvPowerSeries (Fin n) R) := funext hΦΨ
  rw [this, app_X_left c hc]

theorem app_lawApp_transportT (hL : ∀ k, (L k).constantCoeff = 0)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0)
    (hΦΨ : ∀ i, subst Ψ (Φ i) = X i) {τ : Type} {a b : Fin n → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    app Φ (lawApp (transportT L Φ Ψ) a b) = lawApp L (app Φ a) (app Φ b) := by
  rw [lawApp_transportT hL hΦ0 ha hb,
    app_app_cancel hΨ0 hΦΨ
      (constantCoeff_lawApp hL (constantCoeff_app hΦ0 ha) (constantCoeff_app hΦ0 hb))]

abbrev X3a (n : ℕ) (R : Type u) [CommRing R] : Fin n → MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R :=
  fun l => X (Sum.inl l)
abbrev X3b (n : ℕ) (R : Type u) [CommRing R] : Fin n → MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R :=
  fun l => X (Sum.inr (Sum.inl l))
abbrev X3c (n : ℕ) (R : Type u) [CommRing R] : Fin n → MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R :=
  fun l => X (Sum.inr (Sum.inr l))

theorem constantCoeff_X3a (l : Fin n) : (X3a n R l).constantCoeff = 0 := constantCoeff_X _
theorem constantCoeff_X3b (l : Fin n) : (X3b n R l).constantCoeff = 0 := constantCoeff_X _
theorem constantCoeff_X3c (l : Fin n) : (X3c n R l).constantCoeff = 0 := constantCoeff_X _

def transport (F : MvFormalGroup n R) (Φ Ψ : Fin n → MvPowerSeries (Fin n) R)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0)
    (hΨΦ : ∀ i, subst Φ (Ψ i) = X i) (hΦΨ : ∀ i, subst Ψ (Φ i) = X i) : MvFormalGroup n R where
  toPowerSeries := transportT F.toPowerSeries Φ Ψ
  constantCoeff_eq_zero := constantCoeff_transportT F.constantCoeff_eq_zero hΦ0 hΨ0
  coeff_single_inl := by
    classical
    intro i j
    have hLA := constantCoeff_lawApp_app (L := F.toPowerSeries) F.constantCoeff_eq_zero hΦ0
    show coeff (Finsupp.single (Sum.inl j) 1)
        (subst (lawApp F.toPowerSeries (app Φ (Xl n R)) (app Φ (Xr n R))) (Ψ i)) = _
    rw [MvFormalGroup.coeff_single_subst hLA (Ψ i)]
    have hk : ∀ k, coeff (Finsupp.single (Sum.inl j) 1)
        (lawApp F.toPowerSeries (app Φ (Xl n R)) (app Φ (Xr n R)) k) =
        coeff (Finsupp.single j 1) (Φ k) := by
      intro k
      rw [coeff_single_lawApp F (constantCoeff_app hΦ0 (constantCoeff_Xl (R := R)))
        (constantCoeff_app hΦ0 (constantCoeff_Xr (R := R))),
        coeff_inl_app_Xl hΦ0, coeff_inl_app_Xr hΦ0, add_zero]
    simp_rw [hk]
    rw [← MvFormalGroup.coeff_single_subst hΦ0 (Ψ i) j, hΨΦ i, coeff_index_single_X]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  coeff_single_inr := by
    classical
    intro i j
    have hLA := constantCoeff_lawApp_app (L := F.toPowerSeries) F.constantCoeff_eq_zero hΦ0
    show coeff (Finsupp.single (Sum.inr j) 1)
        (subst (lawApp F.toPowerSeries (app Φ (Xl n R)) (app Φ (Xr n R))) (Ψ i)) = _
    rw [MvFormalGroup.coeff_single_subst hLA (Ψ i)]
    have hk : ∀ k, coeff (Finsupp.single (Sum.inr j) 1)
        (lawApp F.toPowerSeries (app Φ (Xl n R)) (app Φ (Xr n R)) k) =
        coeff (Finsupp.single j 1) (Φ k) := by
      intro k
      rw [coeff_single_lawApp F (constantCoeff_app hΦ0 (constantCoeff_Xl (R := R)))
        (constantCoeff_app hΦ0 (constantCoeff_Xr (R := R))),
        coeff_inr_app_Xl hΦ0, coeff_inr_app_Xr hΦ0, zero_add]
    simp_rw [hk]
    rw [← MvFormalGroup.coeff_single_subst hΦ0 (Ψ i) j, hΨΦ i, coeff_index_single_X]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  assoc := by
    intro i
    have hF := F.constantCoeff_eq_zero
    have hG0 : ∀ k, (transportT F.toPowerSeries Φ Ψ k).constantCoeff = 0 :=
      constantCoeff_transportT hF hΦ0 hΨ0
    have ha := constantCoeff_X3a (n := n) (R := R)
    have hb := constantCoeff_X3b (n := n) (R := R)
    have hc := constantCoeff_X3c (n := n) (R := R)
    show lawApp (transportT F.toPowerSeries Φ Ψ)
        (lawApp (transportT F.toPowerSeries Φ Ψ) (X3a n R) (X3b n R)) (X3c n R) i =
      lawApp (transportT F.toPowerSeries Φ Ψ) (X3a n R)
        (lawApp (transportT F.toPowerSeries Φ Ψ) (X3b n R) (X3c n R)) i
    rw [lawApp_transportT hF hΦ0 (constantCoeff_lawApp hG0 ha hb) hc,
      lawApp_transportT hF hΦ0 ha (constantCoeff_lawApp hG0 hb hc),
      app_lawApp_transportT hF hΦ0 hΨ0 hΦΨ ha hb,
      app_lawApp_transportT hF hΦ0 hΨ0 hΦΨ hb hc]
    have hmid : lawApp F.toPowerSeries (lawApp F.toPowerSeries (app Φ (X3a n R)) (app Φ (X3b n R)))
        (app Φ (X3c n R)) =
      lawApp F.toPowerSeries (app Φ (X3a n R))
        (lawApp F.toPowerSeries (app Φ (X3b n R)) (app Φ (X3c n R))) := by
      funext k
      exact MvFormalGroup.subst_elim_assoc F (constantCoeff_app hΦ0 ha) (constantCoeff_app hΦ0 hb)
        (constantCoeff_app hΦ0 hc) k
    rw [hmid]

theorem transport_toPowerSeries (F : MvFormalGroup n R) (Φ Ψ : Fin n → MvPowerSeries (Fin n) R)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0)
    (hΨΦ : ∀ i, subst Φ (Ψ i) = X i) (hΦΨ : ∀ i, subst Ψ (Φ i) = X i) :
    (transport F Φ Ψ hΦ0 hΨ0 hΨΦ hΦΨ).toPowerSeries = transportT F.toPowerSeries Φ Ψ := rfl

def transportHom (F : MvFormalGroup n R) (Φ Ψ : Fin n → MvPowerSeries (Fin n) R)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0)
    (hΨΦ : ∀ i, subst Φ (Ψ i) = X i) (hΦΨ : ∀ i, subst Ψ (Φ i) = X i) :
    (transport F Φ Ψ hΦ0 hΨ0 hΨΦ hΦΨ).Hom F where
  toPowerSeries := Φ
  constantCoeff_eq_zero := hΦ0
  subst_eq := by
    intro i
    show app Φ (transportT F.toPowerSeries Φ Ψ) i =
      lawApp F.toPowerSeries (app Φ (Xl n R)) (app Φ (Xr n R)) i
    conv_lhs => rw [← lawApp_Xl_Xr (transportT F.toPowerSeries Φ Ψ)]
    rw [app_lawApp_transportT F.constantCoeff_eq_zero hΦ0 hΨ0 hΦΨ (constantCoeff_Xl (R := R))
      (constantCoeff_Xr (R := R))]

def transportInv (F : MvFormalGroup n R) (Φ Ψ : Fin n → MvPowerSeries (Fin n) R)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0)
    (hΨΦ : ∀ i, subst Φ (Ψ i) = X i) (hΦΨ : ∀ i, subst Ψ (Φ i) = X i) :
    F.Hom (transport F Φ Ψ hΦ0 hΨ0 hΨΦ hΦΨ) where
  toPowerSeries := Ψ
  constantCoeff_eq_zero := hΨ0
  subst_eq := by
    intro i
    show app Ψ F.toPowerSeries i =
      lawApp (transportT F.toPowerSeries Φ Ψ) (app Ψ (Xl n R)) (app Ψ (Xr n R)) i
    rw [lawApp_transportT F.constantCoeff_eq_zero hΦ0 (constantCoeff_app hΨ0 (constantCoeff_Xl (R := R)))
      (constantCoeff_app hΨ0 (constantCoeff_Xr (R := R))),
      app_app_cancel hΨ0 hΦΨ (constantCoeff_Xl (R := R)),
      app_app_cancel hΨ0 hΦΨ (constantCoeff_Xr (R := R)), lawApp_Xl_Xr]

end Transport

end TSQ

namespace TSQ
section SqZero
variable {R : Type} [CommRing R] {d : ℕ} {κ : Type} [Fintype κ]
  (j : κ → R) (hj : ∀ k k', j k * j k' = 0)
  (η : κ → Fin d → MvPowerSeries (Fin d) R) (hη : ∀ k i, constantCoeff (η k i) = 0)

def PhiT : Fin d → MvPowerSeries (Fin d) R := fun i => X i + ∑ k, j k • η k i

def PsiT : Fin d → MvPowerSeries (Fin d) R := fun i => X i - ∑ k, j k • η k i

include hη in
theorem constantCoeff_PhiT (i : Fin d) : constantCoeff (PhiT j η i) = 0 := by
  rw [PhiT, map_add, constantCoeff_X, zero_add, map_sum]
  exact Finset.sum_eq_zero fun k _ => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, hη, mul_zero]

include hη in
theorem constantCoeff_PsiT (i : Fin d) : constantCoeff (PsiT j η i) = 0 := by
  rw [PsiT, map_sub, constantCoeff_X, zero_sub, neg_eq_zero, map_sum]
  exact Finset.sum_eq_zero fun k _ => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, hη, mul_zero]

theorem PsiT_eq : PsiT j η = fun i => X i + ∑ k, j k • (fun i k => -η k i) i k := by
  funext i; simp [PsiT, PhiT, sub_eq_add_neg, Finset.sum_neg_distrib]

theorem PhiT_eq : PhiT j η = fun i => X i + ∑ k, j k • (fun i k => η k i) i k := rfl

include hj in

theorem smul_subst_pert {σ τ : Type} [Fintype σ] [Fintype τ] (A : σ → MvPowerSeries τ R) (hA : ∀ s, constantCoeff (A s) = 0)
    (B : σ → κ → MvPowerSeries τ R) (k : κ) (g : MvPowerSeries σ R) :
    j k • subst (fun s => A s + ∑ k', j k' • B s k') g = j k • subst A g := by
  rw [MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv j hj g A hA B, smul_add, Finset.smul_sum]
  simp only [smul_smul, hj, zero_smul, Finset.sum_const_zero, add_zero]

include hj hη in
theorem subst_PhiT_PsiT (i : Fin d) : subst (PhiT j η) (PsiT j η i) = X i := by
  have hS : HasSubst (PhiT j η) := hasSubst_of_constantCoeff_zero (constantCoeff_PhiT j η hη)
  rw [PsiT, ← coe_substAlgHom hS, map_sub, map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X hS]
  rw [PhiT_eq]
  simp only [smul_subst_pert j hj (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => constantCoeff_X _) _ _ _]
  have : (fun s : Fin d => (X s : MvPowerSeries (Fin d) R)) = X := rfl
  simp only [this, subst_self, id_eq, add_sub_cancel_right]

include hj hη in
theorem subst_PsiT_PhiT (i : Fin d) : subst (PsiT j η) (PhiT j η i) = X i := by
  have hS : HasSubst (PsiT j η) := hasSubst_of_constantCoeff_zero (constantCoeff_PsiT j η hη)
  rw [PhiT, ← coe_substAlgHom hS, map_add, map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X hS]
  rw [PsiT_eq]
  simp only [smul_subst_pert j hj (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => constantCoeff_X _) _ _ _]
  have : (fun s : Fin d => (X s : MvPowerSeries (Fin d) R)) = X := rfl
  simp only [this, subst_self, id_eq, smul_neg, Finset.sum_neg_distrib]
  abel

theorem transport_isComm (F : MvFormalGroup d R) [F.IsComm] (Φ Ψ : Fin d → MvPowerSeries (Fin d) R)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0)
    (hΨΦ : ∀ i, subst Φ (Ψ i) = X i) (hΦΨ : ∀ i, subst Ψ (Φ i) = X i) :
    (transport F Φ Ψ hΦ0 hΨ0 hΨΦ hΦΨ).IsComm := by
  constructor
  intro i
  have hcomm : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ R), (∀ q, (a q).constantCoeff = 0) → (∀ q, (b q).constantCoeff = 0) →
      lawApp F.toPowerSeries a b = lawApp F.toPowerSeries b a := by
    intro τ a b ha hb
    funext k
    rw [lawApp_apply, lawApp_apply]
    conv_lhs => rw [← MvFormalGroup.IsComm.comm (F := F) k]
    rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim (constantCoeff_Xr (n := d) (R := R)) (constantCoeff_Xl (n := d) (R := R)))
        (MvFormalGroup.hasSubst_elim ha hb)]
    congr 1
    funext s
    rcases s with q | q
    · exact subst_X (MvFormalGroup.hasSubst_elim ha hb) (Sum.inr q)
    · exact subst_X (MvFormalGroup.hasSubst_elim ha hb) (Sum.inl q)
  show lawApp (transportT F.toPowerSeries Φ Ψ) (Xr d R) (Xl d R) i = transportT F.toPowerSeries Φ Ψ i
  rw [lawApp_transportT F.constantCoeff_eq_zero hΦ0 (constantCoeff_Xr (R := R)) (constantCoeff_Xl (R := R)),
    hcomm _ _ (constantCoeff_app hΦ0 (constantCoeff_Xr (R := R))) (constantCoeff_app hΦ0 (constantCoeff_Xl (R := R)))]
  rfl

end SqZero
end TSQ

open TSQ in
theorem solution
    {R : Type} [CommRing R] {d : ℕ} {κ : Type} [Fintype κ]
    (j : κ → R) (hj : ∀ k k', j k * j k' = 0)
    (η : κ → Fin d → MvPowerSeries (Fin d) R) (hη : ∀ k i, constantCoeff (η k i) = 0)
    (F : MvFormalGroup d R) :
    ∃ (F' : MvFormalGroup d R) (Φ : F.Hom F') (Ψ : F'.Hom F),
      (∀ i, Φ.toPowerSeries i = X i - ∑ k, j k • η k i) ∧
      (∀ i, Ψ.toPowerSeries i = X i + ∑ k, j k • η k i) ∧
      Ψ.comp Φ = MvFormalGroup.Hom.id F ∧ Φ.comp Ψ = MvFormalGroup.Hom.id F' ∧
      (F.IsComm → F'.IsComm) ∧
      (∀ l, F'.toPowerSeries l = F.toPowerSeries l + ∑ k, j k •
          (∑ i, subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i) * pderivLin (Sum.inl i) (F.toPowerSeries l)
          + ∑ i, subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i) * pderivLin (Sum.inr i) (F.toPowerSeries l)
          - subst F.toPowerSeries (η k l))) := by
  classical
  have hΦ0 := TSQ.constantCoeff_PhiT j η hη
  have hΨ0 := TSQ.constantCoeff_PsiT j η hη
  have hΨΦ := TSQ.subst_PhiT_PsiT j hj η hη
  have hΦΨ := TSQ.subst_PsiT_PhiT j hj η hη

  let F' : MvFormalGroup d R := TSQ.transport F (TSQ.PhiT j η) (TSQ.PsiT j η) hΦ0 hΨ0 hΨΦ hΦΨ
  let Φ : F.Hom F' := TSQ.transportInv F (TSQ.PhiT j η) (TSQ.PsiT j η) hΦ0 hΨ0 hΨΦ hΦΨ
  let Ψ : F'.Hom F := TSQ.transportHom F (TSQ.PhiT j η) (TSQ.PsiT j η) hΦ0 hΨ0 hΨΦ hΦΨ
  refine ⟨F', Φ, Ψ, fun i => rfl, fun i => rfl, ?_, ?_, fun hc => ?_, ?_⟩
  · apply MvFormalGroup.Hom.ext
    funext i
    exact hΦΨ i
  · apply MvFormalGroup.Hom.ext
    funext i
    exact hΨΦ i
  · haveI := hc
    exact TSQ.transport_isComm F _ _ hΦ0 hΨ0 hΨΦ hΦΨ
  ·
    intro l
    show subst (TSQ.lawApp F.toPowerSeries (TSQ.app (TSQ.PhiT j η) (TSQ.Xl d R)) (TSQ.app (TSQ.PhiT j η) (TSQ.Xr d R))) (TSQ.PsiT j η l) = _

    have hW0 := TSQ.constantCoeff_lawApp_app (L := F.toPowerSeries) F.constantCoeff_eq_zero hΦ0
    have hfam : (Sum.elim (TSQ.app (TSQ.PhiT j η) (TSQ.Xl d R)) (TSQ.app (TSQ.PhiT j η) (TSQ.Xr d R)) : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) =
        fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) R) + ∑ k, j k • (fun s k => Sum.elim
          (fun i => subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i))
          (fun i => subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i)) s) s k := by
      funext s
      rcases s with i | i
      · show subst (TSQ.Xl d R) (X i + ∑ k, j k • η k i) = _
        rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero (TSQ.constantCoeff_Xl (R := R))), map_add, map_sum]
        simp only [map_smul, coe_substAlgHom, subst_X (hasSubst_of_constantCoeff_zero (TSQ.constantCoeff_Xl (R := R))), Sum.elim_inl]
      · show subst (TSQ.Xr d R) (X i + ∑ k, j k • η k i) = _
        rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero (TSQ.constantCoeff_Xr (R := R))), map_add, map_sum]
        simp only [map_smul, coe_substAlgHom, subst_X (hasSubst_of_constantCoeff_zero (TSQ.constantCoeff_Xr (R := R))), Sum.elim_inr]
    have hW : ∀ m, TSQ.lawApp F.toPowerSeries (TSQ.app (TSQ.PhiT j η) (TSQ.Xl d R)) (TSQ.app (TSQ.PhiT j η) (TSQ.Xr d R)) m =
        F.toPowerSeries m + ∑ k, j k • (∑ i, subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i) * pderivLin (Sum.inl i) (F.toPowerSeries m)
          + ∑ i, subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i) * pderivLin (Sum.inr i) (F.toPowerSeries m)) := by
      intro m
      rw [TSQ.lawApp_apply, hfam, MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv j hj _ _ (fun _ => constantCoeff_X _) _]
      have : (fun s : Fin d ⊕ Fin d => (X s : MvPowerSeries (Fin d ⊕ Fin d) R)) = X := rfl
      simp only [this, subst_self, id_eq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

    have hS : HasSubst (TSQ.lawApp F.toPowerSeries (TSQ.app (TSQ.PhiT j η) (TSQ.Xl d R)) (TSQ.app (TSQ.PhiT j η) (TSQ.Xr d R))) :=
      hasSubst_of_constantCoeff_zero hW0
    rw [TSQ.PsiT, ← coe_substAlgHom hS, map_sub, map_sum]
    simp only [map_smul, coe_substAlgHom, subst_X hS]
    rw [hW l]
    have hW' : TSQ.lawApp F.toPowerSeries (TSQ.app (TSQ.PhiT j η) (TSQ.Xl d R)) (TSQ.app (TSQ.PhiT j η) (TSQ.Xr d R)) =
        fun m => F.toPowerSeries m + ∑ k, j k • (fun m k => (∑ i, subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i) * pderivLin (Sum.inl i) (F.toPowerSeries m)
          + ∑ i, subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (η k i) * pderivLin (Sum.inr i) (F.toPowerSeries m))) m k := funext hW
    rw [hW']
    simp only [TSQ.smul_subst_pert j hj F.toPowerSeries F.constantCoeff_eq_zero _ _ _, smul_sub, Finset.sum_sub_distrib]
    abel

end

end S_MvFormalGroup_exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero
end P2MW
export P2MW.S_MvFormalGroup_exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero (solution)
