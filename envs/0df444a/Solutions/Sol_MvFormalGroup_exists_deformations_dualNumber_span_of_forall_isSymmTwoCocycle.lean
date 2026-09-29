-- Prove2me | solution 1 for MvFormalGroup.exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4cef9066-1c24-54d2-8955-8f876c8d1d9e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Theorems.Thm_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace P2mFGTangentDict

universe u

section General

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {g : ℕ} {τ : Type*}

theorem map_toPowerSeries (F : MvFormalGroup g R) (f : R →+* S) (i : Fin g) :
    (F.map f).toPowerSeries i = MvPowerSeries.map f (F.toPowerSeries i) := rfl

theorem map_toPowerSeries_fun (F : MvFormalGroup g R) (f : R →+* S) :
    (F.map f).toPowerSeries = fun i => MvPowerSeries.map f (F.toPowerSeries i) := rfl

private theorem _root_.P2mFGTangentDict.map_map (F : MvFormalGroup g R) (f : R →+* S) (f' : S →+* T) :
    (F.map f).map f' = F.map (f'.comp f) := by
  ext i d
  simp [map_toPowerSeries, MvPowerSeries.map_map]

p2m_export "P2mFGTangentDict" "map_map"
private theorem _root_.P2mFGTangentDict.map_id (F : MvFormalGroup g R) : F.map (RingHom.id R) = F := by
  ext i d
  simp [map_toPowerSeries]

p2m_export "P2mFGTangentDict" "map_id"

theorem isComm_map (F : MvFormalGroup g R) [F.IsComm] (f : R →+* S) : (F.map f).IsComm := by
  constructor
  intro i
  have hz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
    rintro (j | j) <;> simp [constantCoeff_X]
  have key := congrArg (MvPowerSeries.map f) (MvFormalGroup.IsComm.comm (F := F) i)
  rw [map_subst (hasSubst_of_constantCoeff_zero hz)] at key
  have hfam : (fun s => MvPowerSeries.map f ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s)) =
      Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S))
        fun j => X (Sum.inl j) := by
    funext s
    rcases s with j | j <;> simp
  rw [hfam] at key
  exact key

theorem map_subst_elim (F : MvFormalGroup g R) (f : R →+* S)
    {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin g) :
    MvPowerSeries.map f (subst (Sum.elim a b) (F.toPowerSeries i)) =
      subst (Sum.elim (fun j => MvPowerSeries.map f (a j)) fun j => MvPowerSeries.map f (b j))
        ((F.map f).toPowerSeries i) := by
  rw [map_subst (MvFormalGroup.hasSubst_elim ha hb), map_toPowerSeries]
  congr 1
  funext s
  rcases s with j | j <;> rfl

end General

section Dual

variable {k : Type u} [CommRing k] {τ : Type*}

local notation "𝔻" => DualNumber k
local notation "ιk" => TrivSqZeroExt.inlHom k k
set_option quotPrecheck false in
local notation "φk" => (TrivSqZeroExt.fstHom k k k).toRingHom

open DualNumber

theorem fst_comp_inl : (φk).comp (ιk) = RingHom.id k := by
  ext x
  rfl

def sndSeries (Ψ : MvPowerSeries τ (DualNumber k)) : MvPowerSeries τ k :=
  fun d => TrivSqZeroExt.snd (Ψ d)

theorem coeff_sndSeries (Ψ : MvPowerSeries τ 𝔻) (d : τ →₀ ℕ) :
    coeff d (sndSeries Ψ) = TrivSqZeroExt.snd (coeff d Ψ) := rfl

theorem map_fst_lift (q : MvPowerSeries τ k) :
    MvPowerSeries.map φk (MvPowerSeries.map ιk q) = q := by
  rw [MvPowerSeries.map_map, fst_comp_inl, MvPowerSeries.map_id]
  rfl

theorem coeff_eps_smul (Ψ : MvPowerSeries τ 𝔻) (d : τ →₀ ℕ) :
    coeff d ((ε : 𝔻) • Ψ) = ε * coeff d Ψ := rfl

theorem map_fst_eps_smul (Ψ : MvPowerSeries τ 𝔻) :
    MvPowerSeries.map φk ((ε : 𝔻) • Ψ) = 0 := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_map, coeff_eps_smul, map_mul]
  simp

theorem eps_smul_eps_smul (Ψ : MvPowerSeries τ 𝔻) : (ε : 𝔻) • (ε : 𝔻) • Ψ = 0 := by
  rw [smul_smul, eps_mul_eps, zero_smul]

theorem constantCoeff_lift (q : MvPowerSeries τ k) :
    (MvPowerSeries.map ιk q).constantCoeff = TrivSqZeroExt.inl q.constantCoeff :=
  constantCoeff_map _ _

theorem constantCoeff_eps_smul_lift {q : MvPowerSeries τ k} (hq : q.constantCoeff = 0) :
    ((ε : 𝔻) • MvPowerSeries.map ιk q).constantCoeff = 0 := by
  rw [constantCoeff_smul, constantCoeff_lift, hq]
  simp

theorem eq_lift_add_eps_smul (Ψ : MvPowerSeries τ 𝔻) :
    Ψ = MvPowerSeries.map ιk (MvPowerSeries.map φk Ψ) + (ε : 𝔻) • MvPowerSeries.map ιk (sndSeries Ψ) := by
  refine MvPowerSeries.ext fun d => ?_
  rw [map_add, coeff_map, coeff_map, coeff_eps_smul, coeff_map, coeff_sndSeries]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

theorem eq_eps_smul_of_map_fst_eq_zero {Ψ : MvPowerSeries τ 𝔻}
    (h : MvPowerSeries.map φk Ψ = 0) :
    Ψ = (ε : 𝔻) • MvPowerSeries.map ιk (sndSeries Ψ) := by
  conv_lhs => rw [eq_lift_add_eps_smul Ψ, h, map_zero, zero_add]

theorem subst_lift_lift {σ : Type*} {a : σ → MvPowerSeries τ k} (ha : HasSubst a)
    (q : MvPowerSeries σ k) :
    subst (fun s => MvPowerSeries.map ιk (a s)) (MvPowerSeries.map ιk q) =
      MvPowerSeries.map ιk (subst a q) := by
  rw [map_subst ha]

theorem eps_smul_subst_lift {σ : Type*} {a : σ → MvPowerSeries τ 𝔻} (ha : HasSubst a)
    {a₀ : σ → MvPowerSeries τ k} (h : ∀ s, MvPowerSeries.map φk (a s) = a₀ s)
    (q : MvPowerSeries σ k) :
    (ε : 𝔻) • subst a (MvPowerSeries.map ιk q) = (ε : 𝔻) • MvPowerSeries.map ιk (subst a₀ q) := by
  have hfst : MvPowerSeries.map φk (subst a (MvPowerSeries.map ιk q)) = subst a₀ q := by
    rw [map_subst ha, map_fst_lift]
    congr 1
    funext s
    exact h s
  conv_lhs => rw [eq_lift_add_eps_smul (subst a (MvPowerSeries.map ιk q)), hfst, smul_add,
    eps_smul_eps_smul, add_zero]

theorem map_lift_X {σ : Type*} (s : σ) :
    MvPowerSeries.map ιk (X s : MvPowerSeries σ k) = X s := map_X _ _

variable {n : ℕ} (F₀ : MvFormalGroup n k)

set_option quotPrecheck false in

local notation "L" => MvFormalGroup.map (TrivSqZeroExt.inlHom k k) F₀

scoped instance isComm_lift {F₀ : MvFormalGroup n k} [F₀.IsComm] :
    (MvFormalGroup.map (TrivSqZeroExt.inlHom k k) F₀).IsComm :=
  isComm_map F₀ _

theorem lift_toPowerSeries (i : Fin n) :
    (L).toPowerSeries i = MvPowerSeries.map ιk (F₀.toPowerSeries i) := rfl

theorem constantCoeff_L (j : Fin n) : ((L).toPowerSeries j).constantCoeff = 0 :=
  (L).constantCoeff_eq_zero j

theorem map_fst_L : (L).map φk = F₀ := by
  rw [map_map, fst_comp_inl, map_id]

theorem subst_elim_X_X {R : Type*} [CommRing R] (G : MvFormalGroup n R) (i : Fin n) :
    subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R))
      fun l => X (Sum.inr l)) (G.toPowerSeries i) = G.toPowerSeries i := by
  have hX : (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R))
      fun l => X (Sum.inr l)) = X := by
    funext s
    rcases s with l | l <;> rfl
  rw [hX, subst_self]
  rfl

def tr (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) :
    Fin n → MvPowerSeries (Fin n ⊕ Fin n) 𝔻 :=
  fun i => subst (Sum.elim (L).toPowerSeries
    fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) ((L).toPowerSeries i)

theorem tr_apply (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) (i : Fin n) :
    tr F₀ Γ i = subst (Sum.elim (L).toPowerSeries
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) ((L).toPowerSeries i) := rfl

theorem map_fst_subst_elim {w v : Fin n → MvPowerSeries τ 𝔻} {w₀ v₀ : Fin n → MvPowerSeries τ k}
    (hw : ∀ j, (w j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0)
    (hw₀ : ∀ j, MvPowerSeries.map φk (w j) = w₀ j) (hv₀ : ∀ j, MvPowerSeries.map φk (v j) = v₀ j)
    (i : Fin n) :
    MvPowerSeries.map φk (subst (Sum.elim w v) ((L).toPowerSeries i)) =
      subst (Sum.elim w₀ v₀) (F₀.toPowerSeries i) := by
  rw [map_subst_elim (L) φk hw hv i, map_fst_L]
  congr 1
  funext s
  rcases s with j | j
  · exact hw₀ j
  · exact hv₀ j

theorem map_fst_subst_elim_eps {w : Fin n → MvPowerSeries τ 𝔻} {w₀ : Fin n → MvPowerSeries τ k}
    (hw : ∀ j, (w j).constantCoeff = 0) (hw₀ : ∀ j, MvPowerSeries.map φk (w j) = w₀ j)
    (hw₀' : ∀ j, (w₀ j).constantCoeff = 0)
    {γ : Fin n → MvPowerSeries τ k} (hγ : ∀ l, (γ l).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map φk (subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (γ l))
      ((L).toPowerSeries i)) = w₀ i := by
  rw [map_fst_subst_elim F₀ hw (fun l => constantCoeff_eps_smul_lift (hγ l)) hw₀
    (fun l => map_fst_eps_smul _) i]
  exact MvFormalGroup.subst_elim_zero_right F₀ hw₀' i

theorem map_fst_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map φk (tr F₀ Γ i) = F₀.toPowerSeries i :=
  map_fst_subst_elim_eps F₀ (constantCoeff_L F₀) (fun j => by rw [lift_toPowerSeries, map_fst_lift])
    F₀.constantCoeff_eq_zero hΓ i

theorem constantCoeff_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0) (i : Fin n) :
    (tr F₀ Γ i).constantCoeff = 0 :=
  MvFormalGroup.constantCoeff_subst_elim (L) (constantCoeff_L F₀)
    (fun l => constantCoeff_eps_smul_lift (hΓ l)) i

theorem subst_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0)
    {P Q : Fin n → MvPowerSeries τ 𝔻} {P₀ Q₀ : Fin n → MvPowerSeries τ k}
    (hP : ∀ j, (P j).constantCoeff = 0) (hQ : ∀ j, (Q j).constantCoeff = 0)
    (hP₀ : ∀ j, MvPowerSeries.map φk (P j) = P₀ j) (hQ₀ : ∀ j, MvPowerSeries.map φk (Q j) = Q₀ j)
    (i : Fin n) :
    subst (Sum.elim P Q) (tr F₀ Γ i) =
      subst (Sum.elim (fun j => subst (Sum.elim P Q) ((L).toPowerSeries j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim P₀ Q₀) (Γ l)))
        ((L).toPowerSeries i) := by
  have hPQ : HasSubst (Sum.elim P Q) := MvFormalGroup.hasSubst_elim hP hQ
  rw [tr_apply, MvFormalGroup.subst_subst_elim (L) (constantCoeff_L F₀)
    (fun l => constantCoeff_eps_smul_lift (hΓ l)) hPQ i]
  congr 1
  funext s
  rcases s with j | l
  · rfl
  · show subst (Sum.elim P Q) ((ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) =
      (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim P₀ Q₀) (Γ l))
    rw [subst_smul hPQ, eps_smul_subst_lift hPQ (a₀ := Sum.elim P₀ Q₀)]
    rintro (j | j)
    · exact hP₀ j
    · exact hQ₀ j

theorem eps_pow_eq_zero {m : ℕ} (hm : 2 ≤ m) : (ε : 𝔻) ^ m = 0 :=
  pow_eq_zero_of_le hm eps_pow_two

theorem finsuppProd_eps_smul_eq_zero {σ : Type*} (w : σ → MvPowerSeries τ 𝔻)
    {d : σ →₀ ℕ} (hd : 2 ≤ d.degree) :
    (d.prod fun s m => ((ε : 𝔻) • w s) ^ m) = 0 := by
  classical
  have h1 : (d.prod fun s m => ((ε : 𝔻) • w s) ^ m) =
      (d.prod fun s m => (MvPowerSeries.C (ε : 𝔻) : MvPowerSeries τ 𝔻) ^ m) *
        d.prod fun s m => (w s) ^ m := by
    unfold Finsupp.prod
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    show ((ε : 𝔻) • w s) ^ (d s) = (MvPowerSeries.C (ε : 𝔻)) ^ (d s) * (w s) ^ (d s)
    rw [smul_eq_C_mul, mul_pow]
  have h2 : (d.prod fun s m => (MvPowerSeries.C (ε : 𝔻) : MvPowerSeries τ 𝔻) ^ m) = 0 := by
    unfold Finsupp.prod
    rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, ← map_pow, eps_pow_eq_zero hd,
      map_zero]
  rw [h1, h2, zero_mul]

theorem subst_elim_eps_eps {u v : Fin n → MvPowerSeries τ k}
    (hu : ∀ j, (u j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0) (i : Fin n) :
    subst (Sum.elim (fun j => (ε : 𝔻) • MvPowerSeries.map ιk (u j))
      fun j => (ε : 𝔻) • MvPowerSeries.map ιk (v j)) ((L).toPowerSeries i) =
      (ε : 𝔻) • MvPowerSeries.map ιk (u i + v i) := by
  classical
  set c : Fin n ⊕ Fin n → MvPowerSeries τ 𝔻 := Sum.elim
    (fun j => (ε : 𝔻) • MvPowerSeries.map ιk (u j))
    fun j => (ε : 𝔻) • MvPowerSeries.map ιk (v j) with hc
  have hc0 : ∀ s, (c s).constantCoeff = 0 := by
    rintro (j | j)
    · exact constantCoeff_eps_smul_lift (hu j)
    · exact constantCoeff_eps_smul_lift (hv j)
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0

  set w : Fin n ⊕ Fin n → MvPowerSeries τ 𝔻 := Sum.elim
    (fun j => MvPowerSeries.map ιk (u j)) fun j => MvPowerSeries.map ιk (v j) with hw
  have hcw : ∀ s, c s = (ε : 𝔻) • w s := by
    rintro (j | j) <;> rfl
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_subst hsc,
    finsum_eq_finsetSum_of_support_subset _
      (s := Finset.univ.image fun s : Fin n ⊕ Fin n => Finsupp.single s 1) (fun d hd => ?_),
    Finset.sum_image (fun a _ b _ hab => Finsupp.single_left_injective one_ne_zero hab)]
  · have hterm : ∀ s : Fin n ⊕ Fin n,
        coeff (Finsupp.single s 1) ((L).toPowerSeries i) •
          coeff e ((Finsupp.single s 1).prod fun s' m => (c s') ^ m) =
        coeff (Finsupp.single s 1) ((L).toPowerSeries i) * coeff e (c s) := by
      intro s
      rw [Finsupp.prod_single_index (h := fun s' m => (c s') ^ m) (pow_zero (c s)), pow_one,
        smul_eq_mul]
    simp only [hterm]
    rw [Fintype.sum_sum_type]
    simp only [lift_toPowerSeries, coeff_map, F₀.coeff_single_inl, F₀.coeff_single_inr]
    simp only [apply_ite, map_one, map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    show coeff e (c (Sum.inl i)) + coeff e (c (Sum.inr i)) = _
    rw [hc]
    simp only [Sum.elim_inl, Sum.elim_inr, map_add, smul_add]
  ·
    by_contra hmem
    apply hd
    rcases Nat.lt_trichotomy d.degree 1 with hlt | heq | hgt
    · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
      subst hd0
      rw [coeff_zero_eq_constantCoeff_apply, (L).constantCoeff_eq_zero i, zero_smul]
    · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = d := by
        have hmem' : d ∈ {d' : Fin n ⊕ Fin n →₀ ℕ | d'.degree = 1} := heq
        rw [← Finsupp.range_single_one] at hmem'
        exact hmem'
      exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ a)) hmem
    · have hz : (d.prod fun s' m => (c s') ^ m) = 0 := by
        have : (d.prod fun s' m => (c s') ^ m) = d.prod fun s' m => ((ε : 𝔻) • w s') ^ m :=
          Finsupp.prod_congr fun s' _ => by rw [hcw]
        rw [this]
        exact finsuppProd_eps_smul_eq_zero w (by omega)
      rw [hz, map_zero, smul_zero]

theorem subst_elim_eps_assoc [F₀.IsComm] {w : Fin n → MvPowerSeries τ 𝔻}
    (hw : ∀ j, (w j).constantCoeff = 0) {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    (fun i => subst (Sum.elim (fun j => subst
        (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l)) ((L).toPowerSeries j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (b l)) ((L).toPowerSeries i)) =
    fun i => subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l + b l))
      ((L).toPowerSeries i) := by
  funext i
  rw [MvFormalGroup.subst_elim_assoc (L) hw (fun l => constantCoeff_eps_smul_lift (ha l))
    (fun l => constantCoeff_eps_smul_lift (hb l)) i]
  have hin : (fun j => subst (Sum.elim (fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (b l)) ((L).toPowerSeries j)) =
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l + b l) :=
    funext fun j => subst_elim_eps_eps F₀ ha hb j
  rw [hin]

theorem subst_translate {σ : Type*} {w : Fin n → MvPowerSeries τ 𝔻}
    (hw : ∀ j, (w j).constantCoeff = 0)
    {γ : Fin n → MvPowerSeries τ k} (hγ : ∀ l, (γ l).constantCoeff = 0)
    {s : τ → MvPowerSeries σ 𝔻} (hs : HasSubst s) {s₀ : τ → MvPowerSeries σ k}
    (hs₀ : ∀ t, MvPowerSeries.map φk (s t) = s₀ t) (i : Fin n) :
    subst s (subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (γ l))
      ((L).toPowerSeries i)) =
      subst (Sum.elim (fun j => subst s (w j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst s₀ (γ l))) ((L).toPowerSeries i) := by
  rw [MvFormalGroup.subst_subst_elim (L) hw (fun l => constantCoeff_eps_smul_lift (hγ l)) hs i]
  refine congrArg (fun c => subst (Sum.elim _ c) ((L).toPowerSeries i)) (funext fun l => ?_)
  rw [subst_smul hs, eps_smul_subst_lift hs hs₀]

theorem tr_zero (i : Fin n) :
    tr F₀ (fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) i = (L).toPowerSeries i := by
  rw [tr_apply]
  have hf : (fun _ : Fin n => (ε : 𝔻) • MvPowerSeries.map ιk (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) =
      fun _ => 0 := by
    funext l
    rw [map_zero, smul_zero]
  rw [hf]
  exact MvFormalGroup.subst_elim_zero_right (L) (constantCoeff_L F₀) i

theorem lift_smul (a : k) (q : MvPowerSeries τ k) :
    MvPowerSeries.map ιk (a • q) = a • MvPowerSeries.map ιk q := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_map, coeff_smul]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

section Linear

local notation "𝔼" => TrivSqZeroExt k (k × k)
local notation "ιE" => TrivSqZeroExt.inlHom k (k × k)

theorem algHom_comp_inlE (ψ : 𝔼 →ₐ[k] 𝔻) : ψ.toRingHom.comp ιE = ιk := by
  refine RingHom.ext fun x => ?_
  exact ψ.commutes x

theorem algHom_comp_inlD (ψ : 𝔻 →ₐ[k] 𝔻) : ψ.toRingHom.comp ιk = ιk := by
  refine RingHom.ext fun x => ?_
  exact ψ.commutes x

theorem map_algHom_smul {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (e : R) (Ψ : MvPowerSeries τ R) :
    MvPowerSeries.map f (e • Ψ) = f e • MvPowerSeries.map f Ψ := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_map, coeff_smul, coeff_smul, coeff_map, map_mul]

theorem map_algHom_liftE (ψ : 𝔼 →ₐ[k] 𝔻) (q : MvPowerSeries τ k) :
    MvPowerSeries.map ψ.toRingHom (MvPowerSeries.map ιE q) = MvPowerSeries.map ιk q := by
  rw [MvPowerSeries.map_map, algHom_comp_inlE]

theorem four_maps (x : 𝔼) :
    TrivSqZeroExt.map (LinearMap.fst k k k + LinearMap.snd k k k) x +
      TrivSqZeroExt.map (0 : k × k →ₗ[k] k) x =
    TrivSqZeroExt.map (LinearMap.fst k k k) x + TrivSqZeroExt.map (LinearMap.snd k k k) x := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

theorem four_maps_series (Q : MvPowerSeries τ 𝔼) :
    MvPowerSeries.map (TrivSqZeroExt.map (LinearMap.fst k k k + LinearMap.snd k k k)).toRingHom Q +
      MvPowerSeries.map (TrivSqZeroExt.map (0 : k × k →ₗ[k] k)).toRingHom Q =
    MvPowerSeries.map (TrivSqZeroExt.map (LinearMap.fst k k k)).toRingHom Q +
      MvPowerSeries.map (TrivSqZeroExt.map (LinearMap.snd k k k)).toRingHom Q := by
  refine MvPowerSeries.ext fun d => ?_
  simp only [map_add, coeff_map]
  exact four_maps _

theorem map_algHom_translate₂ (ψ : 𝔼 →ₐ[k] 𝔻)
    {Θ Θ' : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΘ : ∀ l, (Θ l).constantCoeff = 0) (hΘ' : ∀ l, (Θ' l).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map ψ.toRingHom (subst (Sum.elim
      (MvFormalGroup.map (TrivSqZeroExt.inlHom k (k × k)) F₀).toPowerSeries
      fun l => (TrivSqZeroExt.inr ((1 : k), (0 : k)) : 𝔼) • MvPowerSeries.map ιE (Θ l) +
        (TrivSqZeroExt.inr ((0 : k), (1 : k)) : 𝔼) • MvPowerSeries.map ιE (Θ' l))
      ((MvFormalGroup.map (TrivSqZeroExt.inlHom k (k × k)) F₀).toPowerSeries i)) =
    subst (Sum.elim (L).toPowerSeries
      fun l => ψ (TrivSqZeroExt.inr ((1 : k), (0 : k))) • MvPowerSeries.map ιk (Θ l) +
        ψ (TrivSqZeroExt.inr ((0 : k), (1 : k))) • MvPowerSeries.map ιk (Θ' l))
      ((L).toPowerSeries i) := by
  have hLE0 : ∀ j, ((MvFormalGroup.map (TrivSqZeroExt.inlHom k (k × k)) F₀).toPowerSeries j).constantCoeff = 0 :=
    (MvFormalGroup.map (TrivSqZeroExt.inlHom k (k × k)) F₀).constantCoeff_eq_zero
  have hfam0 : ∀ l, ((TrivSqZeroExt.inr ((1 : k), (0 : k)) : 𝔼) • MvPowerSeries.map ιE (Θ l) +
      (TrivSqZeroExt.inr ((0 : k), (1 : k)) : 𝔼) • MvPowerSeries.map ιE (Θ' l)).constantCoeff = 0 := by
    intro l
    rw [map_add, constantCoeff_smul, constantCoeff_smul, constantCoeff_map, constantCoeff_map,
      hΘ l, hΘ' l]
    simp
  rw [map_subst_elim _ ψ.toRingHom hLE0 hfam0 i, map_map, algHom_comp_inlE]
  refine congrArg (fun c => subst c ((L).toPowerSeries i)) ?_
  refine congrArg₂ Sum.elim (funext fun j => ?_) (funext fun l => ?_)
  · rw [map_toPowerSeries, map_toPowerSeries, MvPowerSeries.map_map, algHom_comp_inlE]
  · rw [map_add, map_algHom_smul, map_algHom_smul, map_algHom_liftE, map_algHom_liftE]
    rfl

theorem tr_add_add {Θ Θ' : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΘ : ∀ l, (Θ l).constantCoeff = 0) (hΘ' : ∀ l, (Θ' l).constantCoeff = 0) (i : Fin n) :
    tr F₀ (fun l => Θ l + Θ' l) i + (L).toPowerSeries i = tr F₀ Θ i + tr F₀ Θ' i := by
  have key := four_maps_series (subst (Sum.elim
      (MvFormalGroup.map (TrivSqZeroExt.inlHom k (k × k)) F₀).toPowerSeries
      fun l => (TrivSqZeroExt.inr ((1 : k), (0 : k)) : 𝔼) • MvPowerSeries.map ιE (Θ l) +
        (TrivSqZeroExt.inr ((0 : k), (1 : k)) : 𝔼) • MvPowerSeries.map ιE (Θ' l))
      ((MvFormalGroup.map (TrivSqZeroExt.inlHom k (k × k)) F₀).toPowerSeries i))
  rw [map_algHom_translate₂ F₀ _ hΘ hΘ' i, map_algHom_translate₂ F₀ _ hΘ hΘ' i,
    map_algHom_translate₂ F₀ _ hΘ hΘ' i, map_algHom_translate₂ F₀ _ hΘ hΘ' i] at key
  have e1 : (fun l => (TrivSqZeroExt.map (LinearMap.fst k k k + LinearMap.snd k k k))
        (TrivSqZeroExt.inr ((1 : k), (0 : k))) • MvPowerSeries.map ιk (Θ l) +
      (TrivSqZeroExt.map (LinearMap.fst k k k + LinearMap.snd k k k))
        (TrivSqZeroExt.inr ((0 : k), (1 : k))) • MvPowerSeries.map ιk (Θ' l)) =
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Θ l + Θ' l) := by
    funext l
    simp only [TrivSqZeroExt.map_inr, LinearMap.add_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, add_zero, zero_add, map_add, smul_add]
    rfl
  have e0 : (fun l => (TrivSqZeroExt.map (0 : k × k →ₗ[k] k))
        (TrivSqZeroExt.inr ((1 : k), (0 : k))) • MvPowerSeries.map ιk (Θ l) +
      (TrivSqZeroExt.map (0 : k × k →ₗ[k] k))
        (TrivSqZeroExt.inr ((0 : k), (1 : k))) • MvPowerSeries.map ιk (Θ' l)) =
      fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) 𝔻) := by
    funext l
    simp only [TrivSqZeroExt.map_inr, LinearMap.zero_apply, TrivSqZeroExt.inr_zero, zero_smul,
      add_zero]
  have e2 : (fun l => (TrivSqZeroExt.map (LinearMap.fst k k k))
        (TrivSqZeroExt.inr ((1 : k), (0 : k))) • MvPowerSeries.map ιk (Θ l) +
      (TrivSqZeroExt.map (LinearMap.fst k k k))
        (TrivSqZeroExt.inr ((0 : k), (1 : k))) • MvPowerSeries.map ιk (Θ' l)) =
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Θ l) := by
    funext l
    simp only [TrivSqZeroExt.map_inr, LinearMap.fst_apply, TrivSqZeroExt.inr_zero, zero_smul,
      add_zero]
    rfl
  have e3 : (fun l => (TrivSqZeroExt.map (LinearMap.snd k k k))
        (TrivSqZeroExt.inr ((1 : k), (0 : k))) • MvPowerSeries.map ιk (Θ l) +
      (TrivSqZeroExt.map (LinearMap.snd k k k))
        (TrivSqZeroExt.inr ((0 : k), (1 : k))) • MvPowerSeries.map ιk (Θ' l)) =
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Θ' l) := by
    funext l
    simp only [TrivSqZeroExt.map_inr, LinearMap.snd_apply, TrivSqZeroExt.inr_zero, zero_smul,
      zero_add]
    rfl
  rw [e1, e0, e2, e3, MvFormalGroup.subst_elim_zero_right (L) (constantCoeff_L F₀) i] at key
  rw [tr_apply, tr_apply, tr_apply]
  exact key

theorem tr_add_sub {Θ Θ' : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΘ : ∀ l, (Θ l).constantCoeff = 0) (hΘ' : ∀ l, (Θ' l).constantCoeff = 0) (i : Fin n) :
    tr F₀ (fun l => Θ l + Θ' l) i - (L).toPowerSeries i =
      (tr F₀ Θ i - (L).toPowerSeries i) + (tr F₀ Θ' i - (L).toPowerSeries i) := by
  have h := tr_add_add F₀ hΘ hΘ' i
  linear_combination h

theorem tr_smul_sub (a : k) {Θ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΘ : ∀ l, (Θ l).constantCoeff = 0) (i : Fin n) :
    tr F₀ (fun l => a • Θ l) i - (L).toPowerSeries i = a • (tr F₀ Θ i - (L).toPowerSeries i) := by
  set lam : 𝔻 →ₐ[k] 𝔻 := TrivSqZeroExt.map (a • (LinearMap.id : k →ₗ[k] k)) with hlam

  have hmap : MvPowerSeries.map lam.toRingHom (tr F₀ Θ i) = tr F₀ (fun l => a • Θ l) i := by
    rw [tr_apply, tr_apply, map_subst_elim (L) lam.toRingHom (constantCoeff_L F₀)
      (fun l => constantCoeff_eps_smul_lift (hΘ l)) i, map_map, algHom_comp_inlD]
    refine congrArg (fun c => subst c ((L).toPowerSeries i)) ?_
    refine congrArg₂ Sum.elim (funext fun j => ?_) (funext fun l => ?_)
    · rw [lift_toPowerSeries, MvPowerSeries.map_map, algHom_comp_inlD]
    · rw [map_algHom_smul, MvPowerSeries.map_map, algHom_comp_inlD, lift_smul]
      have hle : lam.toRingHom (ε : 𝔻) = a • (ε : 𝔻) := by
        show lam (TrivSqZeroExt.inr 1) = a • (ε : 𝔻)
        rw [hlam, TrivSqZeroExt.map_inr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
          mul_one]
        exact DualNumber.inr_eq_smul_eps a
      rw [hle, smul_assoc, smul_comm]

  have hfst : ∀ d, TrivSqZeroExt.fst (coeff d (tr F₀ Θ i)) = coeff d (F₀.toPowerSeries i) := by
    intro d
    have h := congrArg (coeff d) (map_fst_tr F₀ hΘ i)
    rw [coeff_map] at h
    exact h
  rw [← hmap]
  refine MvPowerSeries.ext fun d => ?_
  rw [map_sub, coeff_map, lift_toPowerSeries, coeff_map]
  show _ = a • (coeff d (tr F₀ Θ i) - coeff d (MvPowerSeries.map ιk (F₀.toPowerSeries i)))
  rw [coeff_map]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [hlam, hfst d]
  · simp [hlam]

theorem tr_sum_sub {ι' : Type*} (s : Finset ι') (c : ι' → k)
    (Θ : ι' → Fin n → MvPowerSeries (Fin n ⊕ Fin n) k)
    (hΘ : ∀ m l, (Θ m l).constantCoeff = 0) (i : Fin n) :
    tr F₀ (fun l => ∑ m ∈ s, c m • Θ m l) i - (L).toPowerSeries i =
      ∑ m ∈ s, c m • (tr F₀ (Θ m) i - (L).toPowerSeries i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [tr_zero, sub_self]
  | @insert a s ha ih =>
    have hs0 : ∀ l, (∑ m ∈ s, c m • Θ m l).constantCoeff = 0 := by
      intro l
      rw [map_sum]
      exact Finset.sum_eq_zero fun m _ => by rw [constantCoeff_smul, hΘ m l, smul_zero]
    have ha0 : ∀ l, (c a • Θ a l).constantCoeff = 0 := fun l => by
      rw [constantCoeff_smul, hΘ a l, smul_zero]
    have hfun : (fun l => ∑ m ∈ insert a s, c m • Θ m l) =
        fun l => c a • Θ a l + ∑ m ∈ s, c m • Θ m l :=
      funext fun l => Finset.sum_insert ha
    rw [hfun, Finset.sum_insert ha, tr_add_sub F₀ ha0 hs0 i, ih,
      tr_smul_sub F₀ (c a) (hΘ a) i]

end Linear

section Iso

theorem subst_elim_X_X' {R : Type*} [CommRing R] (q : MvPowerSeries (Fin n ⊕ Fin n) R) :
    subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R))
      fun l => X (Sum.inr l)) q = q := by
  have hX : (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R))
      fun l => X (Sum.inr l)) = X := by
    funext s
    rcases s with l | l <;> rfl
  rw [hX, subst_self]
  rfl

variable {F₀}

def transHom [F₀.IsComm] {Γa Γb : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓa : ∀ l, (Γa l).constantCoeff = 0) (hΓb : ∀ l, (Γb l).constantCoeff = 0)
    {g : Fin n → MvPowerSeries (Fin n) k} (hg : ∀ l, (g l).constantCoeff = 0)
    (hrel : ∀ l, Γb l = Γa l + F₀.addCoboundary (g l))
    (D₁ D₂ : MvFormalGroup n 𝔻) (hD₁ : D₁.toPowerSeries = tr F₀ Γa)
    (hD₂ : D₂.toPowerSeries = tr F₀ Γb) : D₁.Hom D₂ where
  toPowerSeries i := subst (Sum.elim (fun l => (X l : MvPowerSeries (Fin n) 𝔻))
    fun l => (ε : 𝔻) • MvPowerSeries.map ιk (g l)) ((L).toPowerSeries i)
  constantCoeff_eq_zero i :=
    MvFormalGroup.constantCoeff_subst_elim (L) (fun l => constantCoeff_X _)
      (fun l => constantCoeff_eps_smul_lift (hg l)) i
  subst_eq := by
    intro i
    have hL0 := constantCoeff_L F₀
    have hXn : ∀ l : Fin n, ((X l : MvPowerSeries (Fin n) 𝔻)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hεg : ∀ l, ((ε : 𝔻) • MvPowerSeries.map ιk (g l)).constantCoeff = 0 :=
      fun l => constantCoeff_eps_smul_lift (hg l)
    have hθ0 : ∀ j, (subst (Sum.elim (fun l => (X l : MvPowerSeries (Fin n) 𝔻))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (g l)) ((L).toPowerSeries j)).constantCoeff = 0 :=
      MvFormalGroup.constantCoeff_subst_elim (L) hXn hεg
    have hXl : ∀ l : Fin n, ((X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hXr : ∀ l : Fin n, ((X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    rw [hD₁, hD₂]

    have hΓa' : ∀ l, ((ε : 𝔻) • MvPowerSeries.map ιk (Γa l)).constantCoeff = 0 :=
      fun l => constantCoeff_eps_smul_lift (hΓa l)
    have hsT : HasSubst (tr F₀ Γa) := hasSubst_of_constantCoeff_zero (constantCoeff_tr F₀ hΓa)
    rw [subst_translate F₀ hXn hg hsT (map_fst_tr F₀ hΓa) i]
    have hθX : (fun j => subst (tr F₀ Γa) (X j : MvPowerSeries (Fin n) 𝔻)) = tr F₀ Γa :=
      funext fun j => subst_X hsT j
    rw [hθX]
    have hgF : ∀ l, (subst F₀.toPowerSeries (g l)).constantCoeff = 0 := fun l =>
      constantCoeff_subst_eq_zero F₀.hasSubst_toPowerSeries F₀.constantCoeff_eq_zero (hg l)
    have lhs := congrFun (subst_elim_eps_assoc F₀ hL0 hΓa hgF) i
    rw [show tr F₀ Γa = fun j => subst (Sum.elim (L).toPowerSeries
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γa l)) ((L).toPowerSeries j) from rfl, lhs]

    have hsX2 : ∀ (f : Fin n → Fin n ⊕ Fin n),
        HasSubst (fun l => (X (f l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻)) :=
      fun f => hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hθl : (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
        (subst (Sum.elim (fun l => (X l : MvPowerSeries (Fin n) 𝔻))
          fun l => (ε : 𝔻) • MvPowerSeries.map ιk (g l)) ((L).toPowerSeries j))) =
        fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
          fun l => (ε : 𝔻) • MvPowerSeries.map ιk
            (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
          ((L).toPowerSeries j) := by
      funext j
      rw [subst_translate F₀ hXn hg (hsX2 Sum.inl) (fun l => map_X _ _) j]
      refine congrArg (fun c => subst (Sum.elim c _) ((L).toPowerSeries j)) (funext fun l => ?_)
      exact subst_X (hsX2 Sum.inl) l
    have hθr : (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
        (subst (Sum.elim (fun l => (X l : MvPowerSeries (Fin n) 𝔻))
          fun l => (ε : 𝔻) • MvPowerSeries.map ιk (g l)) ((L).toPowerSeries j))) =
        fun j => subst (Sum.elim (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
          fun l => (ε : 𝔻) • MvPowerSeries.map ιk
            (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
          ((L).toPowerSeries j) := by
      funext j
      rw [subst_translate F₀ hXn hg (hsX2 Sum.inr) (fun l => map_X _ _) j]
      refine congrArg (fun c => subst (Sum.elim c _) ((L).toPowerSeries j)) (funext fun l => ?_)
      exact subst_X (hsX2 Sum.inr) l
    rw [hθl, hθr]
    have hgl : ∀ l, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)).constantCoeff = 0 :=
      fun l => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
        (fun l => constantCoeff_X _) (hg l)
    have hgr : ∀ l, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)).constantCoeff = 0 :=
      fun l => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
        (fun l => constantCoeff_X _) (hg l)
    have hθl0 : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
        ((L).toPowerSeries j)).constantCoeff = 0 :=
      MvFormalGroup.constantCoeff_subst_elim (L) hXl (fun l => constantCoeff_eps_smul_lift (hgl l))
    have hθr0 : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
        ((L).toPowerSeries j)).constantCoeff = 0 :=
      MvFormalGroup.constantCoeff_subst_elim (L) hXr (fun l => constantCoeff_eps_smul_lift (hgr l))
    have hred_l : ∀ j, MvPowerSeries.map φk (subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
        ((L).toPowerSeries j)) = (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ Fin n) k) :=
      map_fst_subst_elim_eps F₀ hXl (fun l => map_X _ _) (fun l => constantCoeff_X _) hgl
    have hred_r : ∀ j, MvPowerSeries.map φk (subst (Sum.elim
        (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
        ((L).toPowerSeries j)) = (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k) :=
      map_fst_subst_elim_eps F₀ hXr (fun l => map_X _ _) (fun l => constantCoeff_X _) hgr
    rw [show tr F₀ Γb i = subst (Sum.elim (L).toPowerSeries
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γb l)) ((L).toPowerSeries i) from rfl,
      subst_translate F₀ hL0 hΓb (MvFormalGroup.hasSubst_elim hθl0 hθr0)
        (s₀ := Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
          fun l => X (Sum.inr l))
        (by rintro (j | j); exacts [hred_l j, hred_r j]) i]
    simp only [subst_elim_X_X']

    rw [show (fun j => subst (Sum.elim
        (fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
          fun l => (ε : 𝔻) • MvPowerSeries.map ιk
            (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
          ((L).toPowerSeries j))
        fun j => subst (Sum.elim (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
          fun l => (ε : 𝔻) • MvPowerSeries.map ιk
            (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
          ((L).toPowerSeries j)) ((L).toPowerSeries j)) =
      fun j => subst (Sum.elim (L).toPowerSeries
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l) +
           subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)))
        ((L).toPowerSeries j) from by
      funext j
      rw [MvFormalGroup.subst_elim_exchange (L) hXl (fun l => constantCoeff_eps_smul_lift (hgl l))
        hXr (fun l => constantCoeff_eps_smul_lift (hgr l)) j]
      refine congrArg (fun c => subst c ((L).toPowerSeries j)) ?_
      refine congrArg₂ Sum.elim (funext fun j' => subst_elim_X_X (L) j') (funext fun l => ?_)
      exact subst_elim_eps_eps F₀ hgl hgr l]
    have hglr : ∀ l, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l) +
        subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (g l)).constantCoeff = 0 := by
      intro l
      rw [map_add, hgl l, hgr l, add_zero]
    have rhs := congrFun (subst_elim_eps_assoc F₀ hL0 hglr hΓb) i
    rw [rhs]
    refine congrArg (fun c => subst (Sum.elim _ c) ((L).toPowerSeries i)) (funext fun l => ?_)
    rw [hrel l]
    unfold MvFormalGroup.addCoboundary
    congr 2
    ring

theorem map_fst_transHom [F₀.IsComm] {Γa Γb : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓa : ∀ l, (Γa l).constantCoeff = 0) (hΓb : ∀ l, (Γb l).constantCoeff = 0)
    {g : Fin n → MvPowerSeries (Fin n) k} (hg : ∀ l, (g l).constantCoeff = 0)
    (hrel : ∀ l, Γb l = Γa l + F₀.addCoboundary (g l))
    (D₁ D₂ : MvFormalGroup n 𝔻) (hD₁ : D₁.toPowerSeries = tr F₀ Γa)
    (hD₂ : D₂.toPowerSeries = tr F₀ Γb) (i : Fin n) :
    MvPowerSeries.map φk ((transHom hΓa hΓb hg hrel D₁ D₂ hD₁ hD₂).toPowerSeries i) = X i :=
  map_fst_subst_elim_eps F₀ (fun l => constantCoeff_X _) (fun l => map_X _ _)
    (fun l => constantCoeff_X _) hg i

theorem isSymmTwoCocycle_add {Γ₁ Γ₂ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (h₁ : F₀.IsSymmTwoCocycle Γ₁) (h₂ : F₀.IsSymmTwoCocycle Γ₂) :
    F₀.IsSymmTwoCocycle (Γ₁ + Γ₂) := by
  have hA : ∀ l : Fin n, ((X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB := MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC := MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  refine ⟨by rw [map_add, h₁.constantCoeff_eq_zero, h₂.constantCoeff_eq_zero, add_zero], ?_, ?_⟩
  · rw [subst_add (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)),
      h₁.symm, h₂.symm]
  · rw [subst_add (MvFormalGroup.hasSubst_elim hFAB hC), subst_add (MvFormalGroup.hasSubst_elim hA hB),
      subst_add (MvFormalGroup.hasSubst_elim hA hFBC), subst_add (MvFormalGroup.hasSubst_elim hB hC)]
    have e₁ := h₁.cocycle
    have e₂ := h₂.cocycle
    linear_combination e₁ + e₂

theorem isSymmTwoCocycle_smul (a : k) {Γ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (h : F₀.IsSymmTwoCocycle Γ) : F₀.IsSymmTwoCocycle (a • Γ) := by
  have hA : ∀ l : Fin n, ((X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB := MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC := MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  refine ⟨by rw [constantCoeff_smul, h.constantCoeff_eq_zero, smul_zero], ?_, ?_⟩
  · rw [subst_smul (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)),
      h.symm]
  · rw [subst_smul (MvFormalGroup.hasSubst_elim hFAB hC), subst_smul (MvFormalGroup.hasSubst_elim hA hB),
      subst_smul (MvFormalGroup.hasSubst_elim hA hFBC), subst_smul (MvFormalGroup.hasSubst_elim hB hC),
      ← smul_add, ← smul_add, h.cocycle]

theorem isSymmTwoCocycle_sum {ι' : Type*} (s : Finset ι') (c : ι' → k)
    {Γ : ι' → MvPowerSeries (Fin n ⊕ Fin n) k} (h : ∀ m, F₀.IsSymmTwoCocycle (Γ m)) :
    F₀.IsSymmTwoCocycle (∑ m ∈ s, c m • Γ m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MvFormalGroup.IsSymmTwoCocycle.zero F₀
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSymmTwoCocycle_add (isSymmTwoCocycle_smul (c a) (h a)) ih

end Iso

end Dual

end P2mFGTangentDict
p2m_reactivate "P2MW.S_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle.P2mFGTangentDict"

universe u

open P2mFGTangentDict in
theorem solution
    {k : Type u} [CommRing k] {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm]
    (r : ℕ) (Γ : Fin r → MvPowerSeries (Fin n ⊕ Fin n) k) (hΓ : ∀ j, F₀.IsSymmTwoCocycle (Γ j))
    (hspan : ∀ Γ' : MvPowerSeries (Fin n ⊕ Fin n) k, F₀.IsSymmTwoCocycle Γ' →
      ∃ (c : Fin r → k) (g : MvPowerSeries (Fin n) k), MvPowerSeries.constantCoeff g = 0 ∧
        Γ' = ∑ j, c j • Γ j + F₀.addCoboundary g) :
    ∃ (d : ℕ) (D : Fin d → MvFormalGroup n (DualNumber k)),
      d ≤ n * r ∧
      (∀ j, (D j).IsComm ∧ (D j).map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀) ∧
      ∀ (F : MvFormalGroup n (DualNumber k)) [F.IsComm],
        F.map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀ →
        ∃ (c : Fin d → k) (G : MvFormalGroup n (DualNumber k)) (θ : G.Hom F),
          (∀ i, G.toPowerSeries i =
            MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i) +
              ∑ j, c j • ((D j).toPowerSeries i -
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i))) ∧
          ∀ i, MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom (θ.toPowerSeries i) =
            MvPowerSeries.X i := by
  classical
  obtain ⟨H1, H2⟩ :=
    MvFormalGroup.exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq F₀
  choose Dlaw hDcomm hDred hDtps using H1

  have htr : ∀ (Θ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) (i : Fin n),
      MvPowerSeries.subst
        (Sum.elim (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries j))
          fun j => (DualNumber.eps : DualNumber k) •
            MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Θ j))
        (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i)) = tr F₀ Θ i := by
    intro Θ i
    rw [tr_apply, map_toPowerSeries_fun]

  let sng : Fin n → Fin r → Fin n → MvPowerSeries (Fin n ⊕ Fin n) k :=
    fun i₀ j l => if l = i₀ then Γ j else 0
  have hsng : ∀ i₀ j l, F₀.IsSymmTwoCocycle (sng i₀ j l) := by
    intro i₀ j l
    by_cases hl : l = i₀
    · simp only [sng, hl, if_true]; exact hΓ j
    · simp only [sng, hl, if_false]; exact MvFormalGroup.IsSymmTwoCocycle.zero F₀
  let e : Fin n × Fin r ≃ Fin (n * r) := finProdFinEquiv
  let D : Fin (n * r) → MvFormalGroup n (DualNumber k) :=
    fun m => Dlaw (sng (e.symm m).1 (e.symm m).2) (hsng _ _)
  refine ⟨n * r, D, le_rfl, fun m => ⟨hDcomm _ _, hDred _ _⟩, ?_⟩
  intro F _ hF
  obtain ⟨ΓF, hΓF, hFt⟩ := H2 F hF
  choose cc gg hgg0 hdec using fun l => hspan (ΓF l) (hΓF l)

  let Γ' : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := fun l => ∑ j, cc l j • Γ j
  have hΓ' : ∀ l, F₀.IsSymmTwoCocycle (Γ' l) := fun l => isSymmTwoCocycle_sum _ _ hΓ
  have hΓ'0 : ∀ l, (Γ' l).constantCoeff = 0 := fun l => (hΓ' l).constantCoeff_eq_zero
  have hΓF0 : ∀ l, (ΓF l).constantCoeff = 0 := fun l => (hΓF l).constantCoeff_eq_zero
  have hG : (Dlaw Γ' hΓ').toPowerSeries = tr F₀ Γ' := funext fun i => by rw [hDtps, htr]
  have hFT : F.toPowerSeries = tr F₀ ΓF := funext fun i => by rw [hFt, htr]
  have hrel : ∀ l, ΓF l = Γ' l + F₀.addCoboundary (gg l) := hdec
  refine ⟨fun m => cc (e.symm m).1 (e.symm m).2, Dlaw Γ' hΓ',
    transHom hΓ'0 hΓF0 hgg0 hrel _ F hG hFT, fun i => ?_,
    map_fst_transHom hΓ'0 hΓF0 hgg0 hrel _ F hG hFT⟩

  rw [hDtps, htr]
  have hsum : ∑ m : Fin (n * r), cc (e.symm m).1 (e.symm m).2 •
      ((D m).toPowerSeries i - MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i)) =
      ∑ q : Fin n × Fin r, cc q.1 q.2 •
        (tr F₀ (sng q.1 q.2) i - MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i)) := by
    refine Fintype.sum_equiv e.symm _ _ fun m => ?_
    simp only [D]
    rw [hDtps, htr]
  have hlin := tr_sum_sub F₀ ((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin r)))
    (fun q => cc q.1 q.2) (fun q => sng q.1 q.2) (fun q l => (hsng q.1 q.2 l).constantCoeff_eq_zero) i
  rw [hsum, ← lift_toPowerSeries, ← Finset.univ_product_univ, ← hlin]
  have hΓ'sng : (fun l => ∑ q ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin r)),
      cc q.1 q.2 • sng q.1 q.2 l) = Γ' := by
    funext l
    rw [Finset.sum_product]
    simp only [sng, smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  rw [hΓ'sng, add_sub_cancel]

end
p2m_reactivate "P2MW.S_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle.P2mFGTangentDict"

end S_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle
end P2MW
export P2MW.S_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle (solution)
