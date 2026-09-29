-- Prove2me | solution 1 for MvFormalGroup.exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c765941a-b9d4-5d30-b12c-e589459a67ac

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u

namespace P2mFGGlue

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

section Pullback

variable {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
  (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
  (hcomm : q'.comp p' = q''.comp p'')
  (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')

include hcomm hpb in

theorem eq_of_proj_eq {b₁ b₂ : B} (h' : p' b₁ = p' b₂) (h'' : p'' b₁ = p'' b₂) : b₁ = b₂ := by
  have hc : q' (p' b₂) = q'' (p'' b₂) := by
    have := congrArg (fun g : B →+* A => g b₂) hcomm
    simpa using this
  obtain ⟨b, -, huniq⟩ := hpb (p' b₂) (p'' b₂) hc
  exact (huniq b₁ ⟨h', h''⟩).trans (huniq b₂ ⟨rfl, rfl⟩).symm

include hcomm hpb in

theorem mv_eq_of_proj_eq {τ : Type} {g₁ g₂ : MvPowerSeries τ B}
    (h' : MvPowerSeries.map p' g₁ = MvPowerSeries.map p' g₂)
    (h'' : MvPowerSeries.map p'' g₁ = MvPowerSeries.map p'' g₂) : g₁ = g₂ := by
  ext e
  apply eq_of_proj_eq p' p'' q' q'' hcomm hpb
  · have := congrArg (coeff e) h'
    simpa only [coeff_map] using this
  · have := congrArg (coeff e) h''
    simpa only [coeff_map] using this

noncomputable def glue {τ : Type} (f' : MvPowerSeries τ A') (f'' : MvPowerSeries τ A'')
    (h : MvPowerSeries.map q' f' = MvPowerSeries.map q'' f'') : MvPowerSeries τ B :=
  show ((τ →₀ ℕ) → B) from fun e =>
    Classical.choose (hpb (coeff e f') (coeff e f'')
      (by
        have := congrArg (coeff e) h
        simpa only [coeff_map] using this))

theorem coeff_glue {τ : Type} (f' : MvPowerSeries τ A') (f'' : MvPowerSeries τ A'')
    (h : MvPowerSeries.map q' f' = MvPowerSeries.map q'' f'') (e : τ →₀ ℕ) :
    p' (coeff e (glue p' p'' q' q'' hpb f' f'' h)) = coeff e f' ∧
      p'' (coeff e (glue p' p'' q' q'' hpb f' f'' h)) = coeff e f'' :=
  (Classical.choose_spec (hpb (coeff e f') (coeff e f'')
      (by
        have := congrArg (coeff e) h
        simpa only [coeff_map] using this))).1

theorem map_glue_left {τ : Type} (f' : MvPowerSeries τ A') (f'' : MvPowerSeries τ A'')
    (h : MvPowerSeries.map q' f' = MvPowerSeries.map q'' f'') :
    MvPowerSeries.map p' (glue p' p'' q' q'' hpb f' f'' h) = f' := by
  ext e
  rw [coeff_map]
  exact (coeff_glue p' p'' q' q'' hpb f' f'' h e).1

theorem map_glue_right {τ : Type} (f' : MvPowerSeries τ A') (f'' : MvPowerSeries τ A'')
    (h : MvPowerSeries.map q' f' = MvPowerSeries.map q'' f'') :
    MvPowerSeries.map p'' (glue p' p'' q' q'' hpb f' f'' h) = f'' := by
  ext e
  rw [coeff_map]
  exact (coeff_glue p' p'' q' q'' hpb f' f'' h e).2

include hcomm hpb in

theorem constantCoeff_eq_zero_of_proj {τ : Type} {g : MvPowerSeries τ B}
    (h' : (MvPowerSeries.map p' g).constantCoeff = 0)
    (h'' : (MvPowerSeries.map p'' g).constantCoeff = 0) : g.constantCoeff = 0 := by
  apply eq_of_proj_eq p' p'' q' q'' hcomm hpb
  · rw [constantCoeff_map] at h'
    rw [h', map_zero]
  · rw [constantCoeff_map] at h''
    rw [h'', map_zero]

end Pullback

section HomSides

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

def homL (L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R) (T : Fin n → MvPowerSeries (Fin n) R)
    (i : Fin n) : MvPowerSeries (Fin n ⊕ Fin n) R :=
  subst L (T i)

def homR (M : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R) (T : Fin n → MvPowerSeries (Fin n) R)
    (i : Fin n) : MvPowerSeries (Fin n ⊕ Fin n) R :=
  subst (Sum.elim (app T (Xl n R)) (app T (Xr n R))) (M i)

theorem hom_iff (F G : MvFormalGroup n R) (T : Fin n → MvPowerSeries (Fin n) R) (i : Fin n) :
    subst F.toPowerSeries (T i) =
        subst (Sum.elim (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R))
          (T j)) fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) R)) (T j))
          (G.toPowerSeries i) ↔
      homL F.toPowerSeries T i = homR G.toPowerSeries T i :=
  Iff.rfl

theorem map_homL (f : R →+* S) {L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R}
    (hL : ∀ i, (L i).constantCoeff = 0) (T : Fin n → MvPowerSeries (Fin n) R) (i : Fin n) :
    MvPowerSeries.map f (homL L T i) =
      homL (fun k => MvPowerSeries.map f (L k)) (fun k => MvPowerSeries.map f (T k)) i := by
  simp only [homL]
  rw [map_subst_of_constantCoeff f hL]

theorem map_homR (f : R →+* S) (M : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R)
    {T : Fin n → MvPowerSeries (Fin n) R} (hT : ∀ i, (T i).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map f (homR M T i) =
      homR (fun k => MvPowerSeries.map f (M k)) (fun k => MvPowerSeries.map f (T k)) i := by
  simp only [homR]
  have h0 : ∀ s, (Sum.elim (app T (Xl n R)) (app T (Xr n R)) s).constantCoeff = 0 := by
    rintro (j | j)
    · exact constantCoeff_app hT (constantCoeff_Xl (R := R)) j
    · exact constantCoeff_app hT (constantCoeff_Xr (R := R)) j
  rw [map_subst_of_constantCoeff f h0]
  congr 1
  funext s
  exact map_elim_app_Xl_Xr f T s

end HomSides

section HomGlue

variable {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
  (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
  (hcomm : q'.comp p' = q''.comp p'')
  (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')

include hcomm hpb in
theorem existsUnique_hom {n : ℕ} (G₁ G₂ : MvFormalGroup n B)
    (α' : (G₁.map p').Hom (G₂.map p')) (α'' : (G₁.map p'').Hom (G₂.map p''))
    (hα : ∀ i, MvPowerSeries.map q' (α'.toPowerSeries i) =
      MvPowerSeries.map q'' (α''.toPowerSeries i)) :
    ∃! α : G₁.Hom G₂,
      (∀ i, MvPowerSeries.map p' (α.toPowerSeries i) = α'.toPowerSeries i) ∧
      (∀ i, MvPowerSeries.map p'' (α.toPowerSeries i) = α''.toPowerSeries i) := by

  let T : Fin n → MvPowerSeries (Fin n) B :=
    fun i => glue p' p'' q' q'' hpb (α'.toPowerSeries i) (α''.toPowerSeries i) (hα i)
  have hT' : ∀ i, MvPowerSeries.map p' (T i) = α'.toPowerSeries i := fun i =>
    map_glue_left p' p'' q' q'' hpb _ _ (hα i)
  have hT'' : ∀ i, MvPowerSeries.map p'' (T i) = α''.toPowerSeries i := fun i =>
    map_glue_right p' p'' q' q'' hpb _ _ (hα i)
  have hT0 : ∀ i, (T i).constantCoeff = 0 := by
    intro i
    apply constantCoeff_eq_zero_of_proj p' p'' q' q'' hcomm hpb
    · rw [hT']
      exact α'.constantCoeff_eq_zero i
    · rw [hT'']
      exact α''.constantCoeff_eq_zero i
  have hTsub : ∀ i, homL G₁.toPowerSeries T i = homR G₂.toPowerSeries T i := by
    intro i
    apply mv_eq_of_proj_eq p' p'' q' q'' hcomm hpb
    · rw [map_homL p' G₁.constantCoeff_eq_zero, map_homR p' _ hT0]
      have h1 : (fun k => MvPowerSeries.map p' (T k)) = α'.toPowerSeries := funext hT'
      rw [h1]
      exact (hom_iff (G₁.map p') (G₂.map p') α'.toPowerSeries i).mp (α'.subst_eq i)
    · rw [map_homL p'' G₁.constantCoeff_eq_zero, map_homR p'' _ hT0]
      have h1 : (fun k => MvPowerSeries.map p'' (T k)) = α''.toPowerSeries := funext hT''
      rw [h1]
      exact (hom_iff (G₁.map p'') (G₂.map p'') α''.toPowerSeries i).mp (α''.subst_eq i)
  let α : G₁.Hom G₂ :=
    { toPowerSeries := T
      constantCoeff_eq_zero := hT0
      subst_eq := fun i => (hom_iff G₁ G₂ T i).mpr (hTsub i) }
  refine ⟨α, ⟨hT', hT''⟩, ?_⟩
  rintro β ⟨hβ', hβ''⟩
  apply MvFormalGroup.Hom.ext
  funext i
  apply mv_eq_of_proj_eq p' p'' q' q'' hcomm hpb
  · rw [hβ' i]
    exact (hT' i).symm
  · rw [hβ'' i]
    exact (hT'' i).symm

end HomGlue

section MatrixTuple

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

def mulVecT {τ : Type} (M : Matrix (Fin n) (Fin n) R) (T : Fin n → MvPowerSeries τ R) :
    Fin n → MvPowerSeries τ R :=
  fun i => ∑ j, M i j • T j

theorem mulVecT_apply {τ : Type} (M : Matrix (Fin n) (Fin n) R) (T : Fin n → MvPowerSeries τ R)
    (i : Fin n) : mulVecT M T i = ∑ j, M i j • T j := rfl

theorem constantCoeff_mulVecT {τ : Type} (M : Matrix (Fin n) (Fin n) R)
    {T : Fin n → MvPowerSeries τ R} (hT : ∀ j, (T j).constantCoeff = 0) (i : Fin n) :
    (mulVecT M T i).constantCoeff = 0 := by
  rw [mulVecT_apply, ← coeff_zero_eq_constantCoeff_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, coeff_zero_eq_constantCoeff_apply, hT j, smul_zero]

theorem subst_mulVecT {τ τ' : Type} (M : Matrix (Fin n) (Fin n) R) (T : Fin n → MvPowerSeries τ R)
    {a : τ → MvPowerSeries τ' R} (ha : HasSubst a) (i : Fin n) :
    subst a (mulVecT M T i) = mulVecT M (fun j => subst a (T j)) i := by
  simp only [mulVecT_apply]
  rw [← coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

theorem mulVecT_mulVecT {τ : Type} (M N : Matrix (Fin n) (Fin n) R)
    (T : Fin n → MvPowerSeries τ R) : mulVecT M (mulVecT N T) = mulVecT (M * N) T := by
  funext i
  simp only [mulVecT_apply, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem mulVecT_one {τ : Type} (T : Fin n → MvPowerSeries τ R) : mulVecT 1 T = T := by
  funext i
  simp only [mulVecT_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem linearPart_mulVecT {m : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (T : Fin n → MvPowerSeries (Fin m) R) :
    MvFormalGroup.linearPart (mulVecT M T) = M * MvFormalGroup.linearPart T := by
  ext i j
  simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.mul_apply, mulVecT_apply,
    map_sum, map_smul, smul_eq_mul]

theorem map_smul' {τ : Type} (f : R →+* S) (r : R) (g : MvPowerSeries τ R) :
    MvPowerSeries.map f (r • g) = f r • MvPowerSeries.map f g := by
  ext e
  simp only [coeff_map, map_smul, smul_eq_mul, map_mul]

theorem map_mulVecT {τ : Type} (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (T : Fin n → MvPowerSeries τ R) (i : Fin n) :
    MvPowerSeries.map f (mulVecT M T i) =
      mulVecT (M.map f) (fun j => MvPowerSeries.map f (T j)) i := by
  simp only [mulVecT_apply, map_sum, map_smul', Matrix.map_apply]

theorem linearPart_X' :
    MvFormalGroup.linearPart (fun i : Fin n => (X i : MvPowerSeries (Fin n) R)) = 1 := by
  classical
  ext i j
  simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.one_apply]
  rw [coeff_index_single_X]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem exists_inverse_of_isUnit_linearPart (Φ : Fin n → MvPowerSeries (Fin n) R)
    (h0 : ∀ i, (Φ i).constantCoeff = 0) (hU : IsUnit (MvFormalGroup.linearPart Φ)) :
    ∃ Ψ : Fin n → MvPowerSeries (Fin n) R,
      (∀ i, (Ψ i).constantCoeff = 0) ∧
      (∀ i, subst Φ (Ψ i) = X i) ∧
      (∀ i, subst Ψ (Φ i) = X i) := by
  obtain ⟨Mu, hMu⟩ := hU
  set M := MvFormalGroup.linearPart Φ with hM
  let N : Matrix (Fin n) (Fin n) R := ↑Mu⁻¹
  have hNM : N * M = 1 := by rw [← hMu]; exact Units.inv_mul Mu
  have hMN : M * N = 1 := by rw [← hMu]; exact Units.mul_inv Mu

  let Φ₁ : Fin n → MvPowerSeries (Fin n) R := mulVecT N Φ
  have hΦ₁0 : ∀ i, (Φ₁ i).constantCoeff = 0 := constantCoeff_mulVecT N h0
  have hΦ₁1 : MvFormalGroup.linearPart Φ₁ = 1 := by
    show MvFormalGroup.linearPart (mulVecT N Φ) = 1
    rw [linearPart_mulVecT, hNM]
  obtain ⟨Ψ₁, hΨ₁0, hΦΨ₁, hΨΦ₁⟩ :=
    MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one Φ₁ hΦ₁0 hΦ₁1

  let Xn : Fin n → MvPowerSeries (Fin n) R := fun i => X i
  have hXn0 : ∀ i, (Xn i).constantCoeff = 0 := fun i => constantCoeff_X i
  let L : Fin n → MvPowerSeries (Fin n) R := mulVecT N Xn
  have hL0 : ∀ i, (L i).constantCoeff = 0 := constantCoeff_mulVecT N hXn0
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero hL0
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero h0
  have hΨ₁ : HasSubst Ψ₁ := hasSubst_of_constantCoeff_zero hΨ₁0
  let Ψ : Fin n → MvPowerSeries (Fin n) R := fun i => subst L (Ψ₁ i)
  have hΨ0 : ∀ i, (Ψ i).constantCoeff = 0 := fun i =>
    constantCoeff_subst_eq_zero hL hL0 (hΨ₁0 i)
  have hΨ : HasSubst Ψ := hasSubst_of_constantCoeff_zero hΨ0

  have hLΦ : (fun j => subst Φ (L j)) = Φ₁ := by
    funext j
    show subst Φ (mulVecT N Xn j) = mulVecT N Φ j
    rw [subst_mulVecT N Xn hΦ]
    congr 1
    funext k
    exact subst_X hΦ k
  refine ⟨Ψ, hΨ0, ?_, ?_⟩
  · intro i
    show subst Φ (subst L (Ψ₁ i)) = X i
    rw [subst_comp_subst_apply hL hΦ, hLΦ, hΦΨ₁]
  · intro i

    have hΦeq : Φ = mulVecT M Φ₁ := by
      show Φ = mulVecT M (mulVecT N Φ)
      rw [mulVecT_mulVecT, hMN, mulVecT_one]
    have hΨΦ₁' : ∀ k, subst Ψ (Φ₁ k) = L k := by
      intro k
      have : subst Ψ (Φ₁ k) = subst L (subst Ψ₁ (Φ₁ k)) := by
        rw [subst_comp_subst_apply hΨ₁ hL]
      rw [this, hΨΦ₁, subst_X hL]
    rw [hΦeq, subst_mulVecT M Φ₁ hΨ]
    have hfam : (fun k => subst Ψ (Φ₁ k)) = L := funext hΨΦ₁'
    rw [hfam]
    show mulVecT M (mulVecT N Xn) i = X i
    rw [mulVecT_mulVecT, hMN, mulVecT_one]

end MatrixTuple

section Lift

variable {A'' A : Type u} [CommRing A''] [CommRing A] (q : A'' →+* A) {n : ℕ}

theorem exists_lift (hq : Function.Surjective q) (φ : Fin n → MvPowerSeries (Fin n) A)
    (h0 : ∀ i, (φ i).constantCoeff = 0) :
    ∃ Φ : Fin n → MvPowerSeries (Fin n) A'',
      (∀ i, (Φ i).constantCoeff = 0) ∧ ∀ i, MvPowerSeries.map q (Φ i) = φ i := by
  classical
  let Φ : Fin n → MvPowerSeries (Fin n) A'' := fun i =>
    show ((Fin n →₀ ℕ) → A'') from fun e =>
      if e = 0 then 0 else Function.surjInv hq (coeff e (φ i))
  have hcoeff : ∀ i e, coeff e (Φ i) = if e = 0 then 0 else Function.surjInv hq (coeff e (φ i)) :=
    fun _ _ => rfl
  refine ⟨Φ, fun i => ?_, fun i => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, hcoeff, if_pos rfl]
  · ext e
    rw [coeff_map, hcoeff]
    by_cases he : e = 0
    · subst he
      rw [if_pos rfl, map_zero, coeff_zero_eq_constantCoeff_apply, h0]
    · rw [if_neg he, Function.surjInv_eq hq]

theorem linearPart_map (Φ : Fin n → MvPowerSeries (Fin n) A'') :
    MvFormalGroup.linearPart (fun i => MvPowerSeries.map q (Φ i)) =
      (MvFormalGroup.linearPart Φ).map q := by
  ext i j
  simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.map_apply, coeff_map]

theorem isUnit_linearPart_of_map [IsLocalHom q] (Φ : Fin n → MvPowerSeries (Fin n) A'')
    (hU : IsUnit (MvFormalGroup.linearPart (fun i => MvPowerSeries.map q (Φ i)))) :
    IsUnit (MvFormalGroup.linearPart Φ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [linearPart_map, Matrix.isUnit_iff_isUnit_det] at hU
  have : q (MvFormalGroup.linearPart Φ).det = ((MvFormalGroup.linearPart Φ).map q).det := by
    rw [RingHom.map_det]
    rfl
  rw [← this] at hU
  exact IsUnit.of_map q _ hU

end Lift

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

theorem map_constantCoeff (f : R →+* S) {T : Fin n → MvPowerSeries (Fin n) R}
    (hT : ∀ i, (T i).constantCoeff = 0) (i : Fin n) :
    (MvPowerSeries.map f (T i)).constantCoeff = 0 := by
  rw [constantCoeff_map, hT i, map_zero]

theorem map_inverse (f : R →+* S) {T U : Fin n → MvPowerSeries (Fin n) R}
    (hT : ∀ i, (T i).constantCoeff = 0) (hUT : ∀ i, subst T (U i) = X i) (i : Fin n) :
    subst (fun j => MvPowerSeries.map f (T j)) (MvPowerSeries.map f (U i)) = X i := by
  rw [← map_subst (hasSubst_of_constantCoeff_zero hT), hUT i, map_X]

theorem transport_map (f : R →+* S) (F : MvFormalGroup n R) (Φ Ψ : Fin n → MvPowerSeries (Fin n) R)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0)
    (hΨΦ : ∀ i, subst Φ (Ψ i) = X i) (hΦΨ : ∀ i, subst Ψ (Φ i) = X i) :
    (transport F Φ Ψ hΦ0 hΨ0 hΨΦ hΦΨ).map f =
      transport (F.map f) (fun i => MvPowerSeries.map f (Φ i)) (fun i => MvPowerSeries.map f (Ψ i))
        (map_constantCoeff f hΦ0) (map_constantCoeff f hΨ0)
        (map_inverse f hΦ0 hΨΦ) (map_inverse f hΨ0 hΦΨ) := by
  apply MvFormalGroup.ext
  funext i
  show MvPowerSeries.map f (transportT F.toPowerSeries Φ Ψ i) =
    transportT (fun k => MvPowerSeries.map f (F.toPowerSeries k))
      (fun i => MvPowerSeries.map f (Φ i)) (fun i => MvPowerSeries.map f (Ψ i)) i
  rw [transportT_def, transportT_def,
    map_app f (constantCoeff_lawApp_app (L := F.toPowerSeries) F.constantCoeff_eq_zero hΦ0)]
  congr 1
  funext k
  rw [map_lawApp f F.toPowerSeries (constantCoeff_app hΦ0 (constantCoeff_Xl (R := R)))
    (constantCoeff_app hΦ0 (constantCoeff_Xr (R := R)))]
  congr 1
  · funext j
    rw [map_app f (constantCoeff_Xl (R := R))]
    congr 1
    funext l
    exact map_Xl f l
  · funext j
    rw [map_app f (constantCoeff_Xr (R := R))]
    congr 1
    funext l
    exact map_Xr f l

theorem transport_eq_of_hom (F₁ F : MvFormalGroup n R) (Φ Ψ : Fin n → MvPowerSeries (Fin n) R)
    (hΦ0 : ∀ i, (Φ i).constantCoeff = 0) (hΨ0 : ∀ i, (Ψ i).constantCoeff = 0)
    (hΨΦ : ∀ i, subst Φ (Ψ i) = X i) (hΦΨ : ∀ i, subst Ψ (Φ i) = X i)
    (hhom : ∀ i, subst F₁.toPowerSeries (Φ i) =
      lawApp F.toPowerSeries (app Φ (Xl n R)) (app Φ (Xr n R)) i) :
    transport F Φ Ψ hΦ0 hΨ0 hΨΦ hΦΨ = F₁ := by
  apply MvFormalGroup.ext
  funext i
  show app Ψ (lawApp F.toPowerSeries (app Φ (Xl n R)) (app Φ (Xr n R))) i = F₁.toPowerSeries i
  have h1 : lawApp F.toPowerSeries (app Φ (Xl n R)) (app Φ (Xr n R)) = app Φ F₁.toPowerSeries :=
    funext fun k => (hhom k).symm
  rw [h1, ← app_app hΦ0 F₁.constantCoeff_eq_zero]
  have h2 : app Ψ Φ = fun i => (X i : MvPowerSeries (Fin n) R) := funext hΨΦ
  rw [h2, app_X_left _ F₁.constantCoeff_eq_zero]

end Transport

section LawGlue

variable {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
  (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
  (hcomm : q'.comp p' = q''.comp p'')
  (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')

omit hcomm hpb in
theorem map_assocL {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    {T : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R} (hT : ∀ k, (T k).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map f (lawApp T (lawApp T (X3a n R) (X3b n R)) (X3c n R) i) =
      lawApp (fun k => MvPowerSeries.map f (T k))
        (lawApp (fun k => MvPowerSeries.map f (T k)) (X3a n S) (X3b n S)) (X3c n S) i := by
  have ha := constantCoeff_X3a (n := n) (R := R)
  have hb := constantCoeff_X3b (n := n) (R := R)
  have hc := constantCoeff_X3c (n := n) (R := R)
  rw [map_lawApp f T (constantCoeff_lawApp hT ha hb) hc]
  congr 1
  · funext k
    rw [map_lawApp f T ha hb]
    congr 1 <;> funext l <;> simp [X3a, X3b]
  · funext l; simp [X3c]

omit hcomm hpb in
theorem map_assocR {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    {T : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R} (hT : ∀ k, (T k).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map f (lawApp T (X3a n R) (lawApp T (X3b n R) (X3c n R)) i) =
      lawApp (fun k => MvPowerSeries.map f (T k)) (X3a n S)
        (lawApp (fun k => MvPowerSeries.map f (T k)) (X3b n S) (X3c n S)) i := by
  have ha := constantCoeff_X3a (n := n) (R := R)
  have hb := constantCoeff_X3b (n := n) (R := R)
  have hc := constantCoeff_X3c (n := n) (R := R)
  rw [map_lawApp f T ha (constantCoeff_lawApp hT hb hc)]
  congr 1
  · funext l; simp [X3a]
  · funext k
    rw [map_lawApp f T hb hc]
    congr 1 <;> funext l <;> simp [X3b, X3c]

include hcomm hpb in

theorem exists_law_glue {n : ℕ} (F' : MvFormalGroup n A') (F₂ : MvFormalGroup n A'')
    (h : F'.map q' = F₂.map q'') :
    ∃ G : MvFormalGroup n B, G.map p' = F' ∧ G.map p'' = F₂ := by
  classical
  have hi : ∀ i, MvPowerSeries.map q' (F'.toPowerSeries i) = MvPowerSeries.map q'' (F₂.toPowerSeries i) :=
    fun i => congrFun (congrArg MvFormalGroup.toPowerSeries h) i
  let T : Fin n → MvPowerSeries (Fin n ⊕ Fin n) B :=
    fun i => glue p' p'' q' q'' hpb (F'.toPowerSeries i) (F₂.toPowerSeries i) (hi i)
  have hT' : ∀ i, MvPowerSeries.map p' (T i) = F'.toPowerSeries i := fun i =>
    map_glue_left p' p'' q' q'' hpb _ _ (hi i)
  have hT'' : ∀ i, MvPowerSeries.map p'' (T i) = F₂.toPowerSeries i := fun i =>
    map_glue_right p' p'' q' q'' hpb _ _ (hi i)
  have hT0 : ∀ i, (T i).constantCoeff = 0 := by
    intro i
    apply constantCoeff_eq_zero_of_proj p' p'' q' q'' hcomm hpb
    · rw [hT']; exact F'.constantCoeff_eq_zero i
    · rw [hT'']; exact F₂.constantCoeff_eq_zero i
  have hfam' : (fun k => MvPowerSeries.map p' (T k)) = F'.toPowerSeries := funext hT'
  have hfam'' : (fun k => MvPowerSeries.map p'' (T k)) = F₂.toPowerSeries := funext hT''
  have hδ : ∀ (f : B →+* A') (i j : Fin n),
      f (if i = j then (1 : B) else 0) = if i = j then 1 else 0 := by
    intro f i j; split_ifs <;> simp
  have hδ' : ∀ (f : B →+* A'') (i j : Fin n),
      f (if i = j then (1 : B) else 0) = if i = j then 1 else 0 := by
    intro f i j; split_ifs <;> simp
  let G : MvFormalGroup n B :=
    { toPowerSeries := T
      constantCoeff_eq_zero := hT0
      coeff_single_inl := by
        intro i j
        apply eq_of_proj_eq p' p'' q' q'' hcomm hpb
        · rw [hδ, ← coeff_map, hT']; exact F'.coeff_single_inl i j
        · rw [hδ', ← coeff_map, hT'']; exact F₂.coeff_single_inl i j
      coeff_single_inr := by
        intro i j
        apply eq_of_proj_eq p' p'' q' q'' hcomm hpb
        · rw [hδ, ← coeff_map, hT']; exact F'.coeff_single_inr i j
        · rw [hδ', ← coeff_map, hT'']; exact F₂.coeff_single_inr i j
      assoc := by
        intro i
        show lawApp T (lawApp T (X3a n B) (X3b n B)) (X3c n B) i =
          lawApp T (X3a n B) (lawApp T (X3b n B) (X3c n B)) i
        apply mv_eq_of_proj_eq p' p'' q' q'' hcomm hpb
        · rw [map_assocL p' hT0, map_assocR p' hT0, hfam']
          exact F'.assoc i
        · rw [map_assocL p'' hT0, map_assocR p'' hT0, hfam'']
          exact F₂.assoc i }
  refine ⟨G, ?_, ?_⟩
  · exact MvFormalGroup.ext hfam'
  · exact MvFormalGroup.ext hfam''

end LawGlue

end P2mFGGlue

open P2mFGGlue in
theorem solution
    {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
    (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
    (hcomm : q'.comp p' = q''.comp p'')
    (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')
    (n : ℕ) :
    (Function.Surjective q'' → IsLocalHom q'' →
      ∀ (F' : MvFormalGroup n A') (F'' : MvFormalGroup n A'')
        (φ : (F'.map q').Hom (F''.map q'')),
        IsUnit (MvFormalGroup.linearPart φ.toPowerSeries) →
        ∃ (G : MvFormalGroup n B) (Φ : (G.map p'').Hom F'') (Ψ : F''.Hom (G.map p'')),
          G.map p' = F' ∧
          Ψ.comp Φ = MvFormalGroup.Hom.id (G.map p'') ∧
          Φ.comp Ψ = MvFormalGroup.Hom.id F'' ∧
          ∀ i, MvPowerSeries.map q'' (Φ.toPowerSeries i) = φ.toPowerSeries i) ∧
    (∀ (G₁ G₂ : MvFormalGroup n B)
        (α' : (G₁.map p').Hom (G₂.map p')) (α'' : (G₁.map p'').Hom (G₂.map p'')),
        (∀ i, MvPowerSeries.map q' (α'.toPowerSeries i) =
          MvPowerSeries.map q'' (α''.toPowerSeries i)) →
        ∃! α : G₁.Hom G₂,
          (∀ i, MvPowerSeries.map p' (α.toPowerSeries i) = α'.toPowerSeries i) ∧
          (∀ i, MvPowerSeries.map p'' (α.toPowerSeries i) = α''.toPowerSeries i)) := by
  refine ⟨?_, fun G₁ G₂ α' α'' hα => existsUnique_hom p' p'' q' q'' hcomm hpb G₁ G₂ α' α'' hα⟩
  intro hq hloc F' F'' φ hφ
  haveI := hloc

  obtain ⟨Φt, hΦt0, hΦtq⟩ := exists_lift q'' hq φ.toPowerSeries φ.constantCoeff_eq_zero
  have hΦeq : (fun i => MvPowerSeries.map q'' (Φt i)) = φ.toPowerSeries := funext hΦtq
  have hΦtU : IsUnit (MvFormalGroup.linearPart Φt) :=
    isUnit_linearPart_of_map q'' Φt (by rw [hΦeq]; exact hφ)
  obtain ⟨Ψt, hΨt0, hΨΦ, hΦΨ⟩ := exists_inverse_of_isUnit_linearPart Φt hΦt0 hΦtU

  let G'' : MvFormalGroup n A'' := transport F'' Φt Ψt hΦt0 hΨt0 hΨΦ hΦΨ
  have hred : G''.map q'' = F'.map q' := by
    show (transport F'' Φt Ψt hΦt0 hΨt0 hΨΦ hΦΨ).map q'' = F'.map q'
    rw [transport_map]
    apply transport_eq_of_hom
    intro i
    have key := φ.subst_eq i
    rw [← hΦeq] at key
    exact key

  obtain ⟨G, hG', hG''⟩ := exists_law_glue p' p'' q' q'' hcomm hpb F' G'' hred.symm
  let ΦH : G''.Hom F'' := transportHom F'' Φt Ψt hΦt0 hΨt0 hΨΦ hΦΨ
  let ΨH : F''.Hom G'' := transportInv F'' Φt Ψt hΦt0 hΨt0 hΨΦ hΦΨ
  refine ⟨G,
    { toPowerSeries := Φt
      constantCoeff_eq_zero := hΦt0
      subst_eq := fun i => by rw [hG'']; exact ΦH.subst_eq i },
    { toPowerSeries := Ψt
      constantCoeff_eq_zero := hΨt0
      subst_eq := fun i => by rw [hG'']; exact ΨH.subst_eq i },
    hG', ?_, ?_, hΦtq⟩
  · apply MvFormalGroup.Hom.ext
    funext i
    exact hΨΦ i
  · apply MvFormalGroup.Hom.ext
    funext i
    exact hΦΨ i

end

end S_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective
end P2MW
export P2MW.S_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective (solution)
