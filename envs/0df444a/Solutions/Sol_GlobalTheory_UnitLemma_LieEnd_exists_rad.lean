-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.exists_rad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:50.411541+00:00
-- url     : https://prove2.me/submissions/d2533120-d2e1-467f-a61c-84d89329eda1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ}
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution (B : InvAlg K) (h : B.gramDet 1 = 0) :
    ∃ y : B.A, y ≠ 0 ∧ ∀ z, Algebra.trace K.E B.A (y * z) = 0 := by
  classical
  set b := Module.finBasis K.E B.A
  have h' : (Matrix.of fun i j => B.herm 1 (b i) (b j)).det = 0 := h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h'
  have hj : ∀ j, Algebra.trace K.E B.A ((∑ i, v i • b i) * B.σ (b j)) = 0 := by
    intro j
    have hvj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, InvAlg.herm, one_mul, Pi.zero_apply] at hvj
    rw [Finset.sum_mul, map_sum]
    simpa [smul_mul_assoc] using hvj
  refine ⟨∑ i, v i • b i, fun h0 => hv0 (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent v h0 i), ?_⟩
  intro z
  have hz : z = ∑ j, K.c (b.repr (B.σ z) j) • B.σ (b j) := by
    conv_lhs => rw [← B.σ_σ z, ← b.sum_repr (B.σ z)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg]
  rw [hz, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [mul_smul_comm, map_smul, hj, smul_zero]
end GlobalTheory.UnitLemma.LieEnd
