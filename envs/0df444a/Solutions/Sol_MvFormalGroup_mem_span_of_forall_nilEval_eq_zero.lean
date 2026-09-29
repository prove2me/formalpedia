-- Prove2me | solution 1 for MvFormalGroup.mem_span_of_forall_nilEval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ae95a296-f7f7-5eb8-bd6f-789ef17ba3d2

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero

set_option autoImplicit false

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "nilEval map mk"
namespace NilDetermined
p2m_open "MvFormalGroup"

set_option linter.unusedSectionVars false

variable {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]

local notation "R" => MvPowerSeries σ B

noncomputable def box (n : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => n

omit [DecidableEq σ] in
@[scoped simp] theorem box_apply (n : ℕ) (i : σ) : box (σ := σ) n i = n := rfl

omit [DecidableEq σ] in
theorem le_box_iff {n : ℕ} {m : σ →₀ ℕ} : m ≤ box n ↔ ∀ i, m i ≤ n :=
  ⟨fun h i => h i, fun h i => h i⟩

noncomputable def deep (n : ℕ) : Ideal R where
  carrier := {φ | ∀ m ≤ box n, coeff m φ = 0}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := fun {φ ψ} hφ hψ m hm => by
    show coeff m (φ + ψ) = 0
    rw [map_add, hφ m hm, hψ m hm, add_zero]
  smul_mem' := fun c φ hφ m hm => by
    show coeff m (c * φ) = 0
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun pq hpq => ?_
    have hle : pq.2 ≤ m := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      rw [← hpq]; exact le_add_self
    rw [hφ pq.2 (hle.trans hm), mul_zero]

theorem mem_deep {n : ℕ} {φ : R} : φ ∈ deep n ↔ ∀ m ≤ box (σ := σ) n, coeff m φ = 0 := Iff.rfl

theorem deep_anti {n n' : ℕ} (h : n ≤ n') : deep (σ := σ) (B := B) n' ≤ deep n := by
  intro φ hφ m hm
  exact hφ m (fun i => (hm i).trans h)

theorem trunc_sub_mem (n : ℕ) (φ : R) : ((trunc' B (box n) φ : MvPolynomial σ B) : R) - φ ∈ deep n := by
  intro m hm
  rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hm, sub_self]

noncomputable def maxIdeal : Ideal R := Ideal.span (Set.range (X : σ → R))

theorem constantCoeff_eq_zero_of_mem_maxIdeal {φ : R} (hφ : φ ∈ maxIdeal) : constantCoeff φ = 0 := by
  refine Submodule.span_induction (p := fun φ _ => constantCoeff φ = 0) ?_ (map_zero _) ?_ ?_ hφ
  · rintro _ ⟨i, rfl⟩; exact constantCoeff_X i
  · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
  · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]

theorem maxIdeal_le_jacobson : maxIdeal (σ := σ) (B := B) ≤ (⊥ : Ideal R).jacobson := by
  intro φ hφ
  rw [Ideal.mem_jacobson_bot]
  intro ψ
  rw [isUnit_iff_constantCoeff, map_add, map_mul, constantCoeff_eq_zero_of_mem_maxIdeal hφ, zero_mul, zero_add,
    map_one]
  exact isUnit_one

noncomputable def ordGe (d : ℕ) : Ideal R where
  carrier := {φ | ∀ m : σ →₀ ℕ, Finsupp.degree m < d → coeff m φ = 0}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := fun {φ ψ} hφ hψ m hm => by
    show coeff m (φ + ψ) = 0
    rw [map_add, hφ m hm, hψ m hm, add_zero]
  smul_mem' := fun c φ hφ m hm => by
    show coeff m (c * φ) = 0
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun pq hpq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    have : Finsupp.degree pq.2 ≤ Finsupp.degree m := by
      rw [← hpq, map_add]; exact le_add_self
    rw [hφ pq.2 (this.trans_lt hm), mul_zero]

theorem ordGe_mul_le (d d' : ℕ) : ordGe (σ := σ) (B := B) d * ordGe d' ≤ ordGe (d + d') := by
  rw [Ideal.mul_le]
  intro φ hφ ψ hψ m hm
  show coeff m (φ * ψ) = 0
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  have hdeg : Finsupp.degree pq.1 + Finsupp.degree pq.2 < d + d' := by
    rw [← map_add, hpq]; exact hm
  by_cases h1 : Finsupp.degree pq.1 < d
  · rw [hφ pq.1 h1, zero_mul]
  · have h2 : Finsupp.degree pq.2 < d' := by omega
    rw [hψ pq.2 h2, mul_zero]

theorem maxIdeal_le_ordGe_one : maxIdeal (σ := σ) (B := B) ≤ ordGe 1 := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩ m hm
  show coeff m (X i) = 0
  have hm0 : m = 0 := by
    have : Finsupp.degree m = 0 := by omega
    exact (Finsupp.degree_eq_zero_iff m).mp this
  rw [hm0, coeff_zero_X]

theorem maxIdeal_pow_le_ordGe (d : ℕ) : maxIdeal (σ := σ) (B := B) ^ d ≤ ordGe d := by
  induction d with
  | zero =>
      intro φ _ m hm
      exact absurd hm (Nat.not_lt_zero _)
  | succ d ih =>
      rw [pow_succ]
      exact (Ideal.mul_mono ih maxIdeal_le_ordGe_one).trans (ordGe_mul_le d 1)

theorem degree_le_of_le_box {n : ℕ} {m : σ →₀ ℕ} (hm : m ≤ box n) : Finsupp.degree m ≤ Fintype.card σ * n := by
  rw [Finsupp.degree_apply]
  calc ∑ i ∈ m.support, m i ≤ ∑ i ∈ m.support, n := Finset.sum_le_sum fun i _ => hm i
    _ = m.support.card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card σ * n := Nat.mul_le_mul_right _ (Finset.card_le_univ _)

theorem ordGe_le_deep (n : ℕ) : ordGe (σ := σ) (B := B) (Fintype.card σ * n + 1) ≤ deep n := by
  intro φ hφ m hm
  exact hφ m (Nat.lt_succ_of_le (degree_le_of_le_box hm))

theorem maxIdeal_pow_le_deep (n : ℕ) : maxIdeal (σ := σ) (B := B) ^ (Fintype.card σ * n + 1) ≤ deep n :=
  (maxIdeal_pow_le_ordGe _).trans (ordGe_le_deep n)

noncomputable def highPart (i : σ) (n : ℕ) (φ : R) : R := fun m => if n + 1 ≤ m i then coeff m φ else 0

theorem coeff_highPart (i : σ) (n : ℕ) (φ : R) (m : σ →₀ ℕ) :
    coeff m (highPart i n φ) = if n + 1 ≤ m i then coeff m φ else 0 := rfl

theorem X_pow_dvd_highPart (i : σ) (n : ℕ) (φ : R) : (X i : R) ^ (n + 1) ∣ highPart i n φ := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [coeff_highPart, if_neg (not_le.mpr hm)]

theorem X_pow_mem_maxIdeal_pow (i : σ) (n : ℕ) : (X i : R) ^ (n + 1) ∈ maxIdeal ^ (n + 1) := by
  have h : (X i : R) ∈ maxIdeal := Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.pow_mem_pow h _

theorem highPart_mem (i : σ) (n : ℕ) (φ : R) : highPart i n φ ∈ maxIdeal ^ (n + 1) := by
  obtain ⟨ψ, hψ⟩ := X_pow_dvd_highPart i n φ
  rw [hψ]
  exact Ideal.mul_mem_right _ _ (X_pow_mem_maxIdeal_pow i n)

theorem mem_pow_of_support (n : ℕ) (s : Finset σ) :
    ∀ φ : R, (∀ m : σ →₀ ℕ, coeff m φ ≠ 0 → ∃ j ∈ s, n + 1 ≤ m j) → φ ∈ maxIdeal ^ (n + 1) := by
  induction s using Finset.induction_on with
  | empty =>
      intro φ hφ
      have : φ = 0 := by
        ext m
        by_contra h
        obtain ⟨j, hj, -⟩ := hφ m h
        simp at hj
      rw [this]; exact Ideal.zero_mem _
  | insert i s hi ih =>
      intro φ hφ
      have hsplit : φ = highPart i n φ + (φ - highPart i n φ) := by ring
      rw [hsplit]
      refine Ideal.add_mem _ (highPart_mem i n φ) (ih _ fun m hm => ?_)
      rw [map_sub, coeff_highPart] at hm
      split_ifs at hm with hle
      · exact absurd (sub_self _) hm
      · rw [sub_zero] at hm
        obtain ⟨j, hj, hnj⟩ := hφ m hm
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact absurd hnj hle
        · exact ⟨j, hj, hnj⟩

theorem deep_le_pow (n : ℕ) : deep (σ := σ) (B := B) n ≤ maxIdeal ^ (n + 1) := by
  intro φ hφ
  refine mem_pow_of_support n Finset.univ φ fun m hm => ?_
  by_contra h
  exact hm (hφ m fun i => Nat.lt_succ_iff.mp (Nat.lt_of_not_le fun hle => h ⟨i, Finset.mem_univ i, hle⟩))

theorem nilEval_mk (L : Ideal R) (M : ℕ) (φ : R) :
    MvFormalGroup.nilEval M φ (fun i => Ideal.Quotient.mk L (X i)) =
      Ideal.Quotient.mk L ((trunc' B (box M) φ : MvPolynomial σ B) : R) := by
  unfold MvFormalGroup.nilEval
  have key : ∀ P : MvPolynomial σ B,
      MvPolynomial.aeval (fun i => Ideal.Quotient.mk L (X i)) P = Ideal.Quotient.mkₐ B L (P : R) := by
    intro P
    have h : (MvPolynomial.aeval fun i => Ideal.Quotient.mk L (X i)) =
        (Ideal.Quotient.mkₐ B L).comp (MvPolynomial.coeToMvPowerSeries.algHom B) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
        MvPolynomial.coe_X]
      rfl
    rw [h]
    rfl
  exact key _

end MvFormalGroup.NilDetermined
p2m_reactivate "P2MW.S_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero.MvFormalGroup P2MW.S_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero.MvFormalGroup.NilDetermined"
p2m_reactivate "P2MW.S_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero.MvFormalGroup"

open MvFormalGroup.NilDetermined in
theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
    (S : Set (MvPowerSeries σ B)) (G : MvPowerSeries σ B)
    (hG : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : σ → C, (∀ i, s i ∈ J) → (∀ φ ∈ S, MvFormalGroup.nilEval n φ s = 0) → MvFormalGroup.nilEval n G s = 0) :
    G ∈ Ideal.span S := by
  haveI : IsNoetherianRing (MvPowerSeries σ B) := MvPowerSeries.isNoetherianRing_of_finite
  set K : Ideal (MvPowerSeries σ B) := Ideal.span S with hK

  have hstep : ∀ n : ℕ, G ∈ K ⊔ deep n := by
    intro n
    set L : Ideal (MvPowerSeries σ B) := K ⊔ deep n with hL
    set M : ℕ := Fintype.card σ * n + n with hM
    have hnM : n ≤ M := Nat.le_add_left _ _

    have hJ : (maxIdeal.map (Ideal.Quotient.mk L)) ^ (M + 1) = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      calc maxIdeal ^ (M + 1) ≤ maxIdeal ^ (Fintype.card σ * n + 1) :=
            Ideal.pow_le_pow_right (by omega)
        _ ≤ deep n := maxIdeal_pow_le_deep n
        _ ≤ L := le_sup_right
    have hs : ∀ i, Ideal.Quotient.mk L (X i) ∈ maxIdeal.map (Ideal.Quotient.mk L) :=
      fun i => Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

    have hev : ∀ φ : MvPowerSeries σ B,
        MvFormalGroup.nilEval M φ (fun i => Ideal.Quotient.mk L (X i)) = Ideal.Quotient.mk L φ := by
      intro φ
      rw [nilEval_mk, Ideal.Quotient.eq]
      exact le_sup_right (α := Ideal (MvPowerSeries σ B)) (deep_anti hnM (trunc_sub_mem M φ))
    have hS : ∀ φ ∈ S, MvFormalGroup.nilEval M φ (fun i => Ideal.Quotient.mk L (X i)) = 0 := by
      intro φ hφ
      rw [hev, Ideal.Quotient.eq_zero_iff_mem]
      exact le_sup_left (α := Ideal (MvPowerSeries σ B)) (Ideal.subset_span hφ)
    have := hG (MvPowerSeries σ B ⧸ L) (maxIdeal.map (Ideal.Quotient.mk L)) M hJ
      (fun i => Ideal.Quotient.mk L (X i : MvPowerSeries σ B)) hs hS
    rwa [hev, Ideal.Quotient.eq_zero_iff_mem] at this

  have hmem : Ideal.Quotient.mk K G ∈
      (⨅ i : ℕ, maxIdeal (σ := σ) (B := B) ^ i • ⊤ : Submodule (MvPowerSeries σ B) (MvPowerSeries σ B ⧸ K)) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.Quotient.algebraMap_eq]
    have hGi : G ∈ K ⊔ maxIdeal ^ i := by
      refine (sup_le_sup_left ?_ K) (hstep i)
      exact (deep_le_pow i).trans (Ideal.pow_le_pow_right (Nat.le_succ i))
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hGi
    rw [← hyz, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hy, zero_add]
    exact Ideal.mem_map_of_mem _ hz
  rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ maxIdeal_le_jacobson, Submodule.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hmem

end S_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero
end P2MW
export P2MW.S_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero (solution)
