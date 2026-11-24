-- Prove2me | solution 1 for GlobalTheory.CNorm.pIdx_of_ker_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:20.47807+00:00
-- url     : https://prove2.me/submissions/dd0e5eb4-e407-450e-b1a2-5c06c6ee51bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexTopOfGroupFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardQuotSpanAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormCoeffMinpolyLeOneOfNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Theorems.Thm_GlobalTheory_CNorm_pIdx_range_of_injective
import Theorems.Thm_GlobalTheory_CNorm_pTor_range_of_injective
import Theorems.Thm_GlobalTheory_CNorm_pTor_pIdx_subgroup_int
import Theorems.Thm_GlobalTheory_CNorm_pIdx_pTor_ker_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (p : ℕ) (hp : 0 < p) {A B : Type} [CommGroup A] [CommGroup B]
    (j : A →* B) (hj : Function.Injective j) (g : B →* Multiplicative ℤ) (hk : g.ker = j.range)
    (hg : g.range ≠ ⊥) (N : ℕ) (hN : N ≠ 0) (h1 : pTor p (⊤ : Subgroup A) ≠ 0)
    (h2 : pIdx p (⊤ : Subgroup A) = N * pTor p (⊤ : Subgroup A)) :
    pTor p (⊤ : Subgroup B) ≠ 0 ∧ pIdx p (⊤ : Subgroup B) = p * N * pTor p (⊤ : Subgroup B) := by
  obtain ⟨r1, r2⟩ := pTor_pIdx_subgroup_int p hp g.range hg
  have k1 : pTor p g.ker = pTor p (⊤ : Subgroup A) := by
    rw [hk, pTor_range_of_injective p j hj]
  have k2 : pIdx p g.ker = N * pTor p (⊤ : Subgroup A) := by
    rw [hk, pIdx_range_of_injective p j hj, h2]
  obtain ⟨-, a2, a3⟩ := pIdx_pTor_ker_range p B (Multiplicative ℤ) g
    (by rw [k2]; exact mul_ne_zero hN h1) (by rw [k1]; exact h1) (by rw [r2]; exact hp.ne')
    (by rw [r1]; exact one_ne_zero)
  refine ⟨a2, ?_⟩
  rw [k1, k2, r1, r2] at a3
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h1)
  linarith
end GlobalTheory.CNorm
