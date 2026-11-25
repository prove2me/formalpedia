-- Prove2me | solution 1 for GlobalTheory.EtIsom.detH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:09:38.791596+00:00
-- url     : https://prove2.me/submissions/d75f0a65-bf77-4679-a720-4f17aa5d552c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_T_jacquetRallis_invK_regular_iff_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.EtIsom
theorem _root_.solution (hG : A.IsGen τ p) {a : A.K} (ha : IsUnit a) :
    (Matrix.of fun i k : Fin r => Algebra.trace F A.K (τ ^ ((i : ℕ) + (k : ℕ)) * a)).det ≠ 0 := by
  have hinj := (GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p 0 hG).1.1
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ e : Fin r → F, (Matrix.of fun i k : Fin r => Algebra.trace F A.K (τ ^ ((i : ℕ) + (k : ℕ)) * a)) *ᵥ e =
      (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * (a * ∑ k, e k • τ ^ (k : ℕ)))) := by
    intro e
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, pow_add, mul_comm]
    ring_nf
  intro e e' h
  rw [key, key] at h
  have h1 := ha.mul_left_cancel (hinj h)
  have h2 := Fintype.linearIndependent_iff.mp hG.1 (e - e') (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  exact sub_eq_zero.mp (h2 i)
end GlobalTheory.EtIsom
