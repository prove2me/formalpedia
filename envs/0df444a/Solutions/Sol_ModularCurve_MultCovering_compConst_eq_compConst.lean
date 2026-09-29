-- Prove2me | solution 1 for ModularCurve.MultCovering.compConst_eq_compConst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7c87f0af-a5cc-5877-ac6e-050a08a60d8f

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_compConst_eq_compConst

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ Φ'' : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (hΓ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
      ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p], Nonempty (ChartCtx p A)) :
    compConst Φ s hs = compConst Φ'' s hs := by
  classical
  have hp : p.Prime := Fact.out

  have coord : ∀ {v : Fin r → ↥(modularFunctionFieldBar (1 * p))} (hv : LinearIndependent (AlgebraicClosure ℚ) v) (c : Fin r → (AlgebraicClosure ℚ))
      (x : ↥(modularFunctionFieldBar (1 * p))) (hx : x ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range v)) (heq : x = ∑ k, c k • v k) (k : Fin r),
      hv.repr ⟨x, hx⟩ k = c k := by
    intro v hv c x hx heq k
    have h1 := hv.linearCombination_repr ⟨x, hx⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by exact zero_smul _ _)] at h1
    have h2 : ∑ i, (hv.repr ⟨x, hx⟩ i - c i) • v i = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← heq]; exact h1
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ h2 k)
  have expand : ∀ {v : Fin r → ↥(modularFunctionFieldBar (1 * p))} (hv : LinearIndependent (AlgebraicClosure ℚ) v) (x : ↥(modularFunctionFieldBar (1 * p)))
      (hx : x ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range v)), x = ∑ k, hv.repr ⟨x, hx⟩ k • v k := by
    intro v hv x hx
    have h1 := hv.linearCombination_repr ⟨x, hx⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by exact zero_smul _ _)] at h1
    exact h1.symm

  have hmem1 : ∀ i, Φ''.t i ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range Φ.t) := fun i => by
    rw [Φ.t_basis.2, ← Φ''.t_basis.2]; exact Submodule.subset_span ⟨i, rfl⟩
  have hmem2 : ∀ i, Φ.t i ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range Φ''.t) := fun i => by
    rw [Φ''.t_basis.2, ← Φ.t_basis.2]; exact Submodule.subset_span ⟨i, rfl⟩
  set V : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) := fun i j => Φ.t_basis.1.repr ⟨Φ''.t i, hmem1 i⟩ j with hV_def
  set Vi : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) := fun i j => Φ''.t_basis.1.repr ⟨Φ.t i, hmem2 i⟩ j with hVi_def
  have hV : ∀ i, Φ''.t i = ∑ j, V i j • Φ.t j := fun i => expand Φ.t_basis.1 (Φ''.t i) (hmem1 i)
  have hVi : ∀ i, Φ.t i = ∑ j, Vi i j • Φ''.t j := fun i => expand Φ''.t_basis.1 (Φ.t i) (hmem2 i)

  have hVA : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p → ∀ i j, V i j ∈ A ∧ Vi i j ∈ A := by
    intro A hA i j
    haveI : CharP (IsLocalRing.ResidueField ↥A) p := by
      rw [CharP.charP_iff_prime_eq_zero hp]
      have h1 : (((⟨(p : (AlgebraicClosure ℚ)), natCast_mem A p⟩ : ↥A)) : (AlgebraicClosure ℚ)) ∈ A.nonunits := hA
      rw [ValuationSubring.coe_mem_nonunits_iff] at h1
      have h2 : IsLocalRing.residue ↥A ⟨(p : (AlgebraicClosure ℚ)), natCast_mem A p⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).2 h1
      have h3 : (⟨(p : (AlgebraicClosure ℚ)), natCast_mem A p⟩ : ↥A) = (p : ↥A) := Subtype.ext (by push_cast; rfl)
      rw [h3, map_natCast] at h2
      exact h2
    obtain ⟨Γ⟩ := hΓ A hA
    obtain ⟨hintΦ, -⟩ := Φ.t_inf A hA Γ
    obtain ⟨hintΦ'', -⟩ := Φ''.t_inf A hA Γ
    exact ⟨mem_of_eq_sum_smul_goodFamily p A hA Γ Φ (V i) (Φ''.t i) (hintΦ'' i) (hV i) j,
      mem_of_eq_sum_smul_goodFamily p A hA Γ Φ'' (Vi i) (Φ.t i) (hintΦ i) (hVi i) j⟩

  have hs_t : ∀ (Ψ : FamCtx p r) (i : Fin r), s i = ∑ j, linkMatrix Ψ s hs i j • Ψ.t j := fun Ψ i =>
    expand Ψ.t_basis.1 (s i) (mem_span_range_goodFamily Ψ s hs i)
  have ht_s : ∀ (Ψ : FamCtx p r) (i : Fin r), Ψ.t i = ∑ j, linkMatrixInv Ψ s hs i j • s j := fun Ψ i =>
    expand hs.1 (Ψ.t i) (goodFamily_mem_span_range Ψ s hs i)

  have hlink : ∀ (Ψ Ψ' : FamCtx p r) (W : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)), (∀ i, Ψ.t i = ∑ j, W i j • Ψ'.t j) →
      (∀ i k, linkMatrix Ψ' s hs i k = ∑ j, linkMatrix Ψ s hs i j * W j k) ∧
      (∀ i k, linkMatrixInv Ψ s hs i k = ∑ j, W i j * linkMatrixInv Ψ' s hs j k) := by
    intro Ψ Ψ' W hW
    constructor
    · intro i k
      rw [linkMatrix_apply]
      apply coord Ψ'.t_basis.1 (fun k => ∑ j, linkMatrix Ψ s hs i j * W j k) (s i)
      rw [hs_t Ψ i]
      simp_rw [hW, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    · intro i k
      rw [linkMatrixInv_apply]
      apply coord hs.1 (fun k => ∑ j, W i j * linkMatrixInv Ψ' s hs j k) (Ψ.t i)
      rw [hW i]
      simp_rw [ht_s Ψ', Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
  obtain ⟨hM1, hMi1⟩ := hlink Φ Φ'' Vi hVi
  obtain ⟨hM2, hMi2⟩ := hlink Φ'' Φ V hV

  have hset : {B : ℕ | ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ i j, (p : (AlgebraicClosure ℚ)) ^ B * linkMatrix Φ s hs i j ∈ A ∧ (p : (AlgebraicClosure ℚ)) ^ B * linkMatrixInv Φ s hs i j ∈ A}
      = {B : ℕ | ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ i j, (p : (AlgebraicClosure ℚ)) ^ B * linkMatrix Φ'' s hs i j ∈ A ∧ (p : (AlgebraicClosure ℚ)) ^ B * linkMatrixInv Φ'' s hs i j ∈ A} := by
    ext B
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h A hA i j
      constructor
      · rw [hM1 i j, Finset.mul_sum]
        exact sum_mem fun k _ => by rw [← mul_assoc]; exact mul_mem (h A hA i k).1 (hVA A hA k j).2
      · rw [hMi2 i j, Finset.mul_sum]
        exact sum_mem fun k _ => by rw [mul_left_comm]; exact mul_mem (hVA A hA i k).1 (h A hA k j).2
    · intro h A hA i j
      constructor
      · rw [hM2 i j, Finset.mul_sum]
        exact sum_mem fun k _ => by rw [← mul_assoc]; exact mul_mem (h A hA i k).1 (hVA A hA k j).1
      · rw [hMi1 i j, Finset.mul_sum]
        exact sum_mem fun k _ => by rw [mul_left_comm]; exact mul_mem (hVA A hA i k).2 (h A hA k j).2
  have hbud : linkBudget Φ s hs = linkBudget Φ'' s hs := by
    unfold linkBudget; rw [hset]
  rw [compConst_eq, compConst_eq, hbud]

end S_ModularCurve_MultCovering_compConst_eq_compConst
end P2MW
export P2MW.S_ModularCurve_MultCovering_compConst_eq_compConst (solution)
