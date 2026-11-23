-- Prove2me | solution 1 for GlobalTheory.faithfulSMul_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:07.543983+00:00
-- url     : https://prove2.me/submissions/558495e7-224f-4fd3-9224-ce2239e19abb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (G : Type*) [Group G]
variable {R S A A' : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing A']
  [Algebra R S] [Algebra R A] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
  [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A'] [SMulCommClass G S A']
omit [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A']
  [SMulCommClass G S A']
namespace GlobalTheory
theorem _root_.solution [Module.Flat R S] [FaithfulSMul R A]
    (f : A →ₐ[R] A') (hb : IsBaseChange S f.toLinearMap) : FaithfulSMul S A' := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S) (Algebra.linearMap R A)
    (FaithfulSMul.algebraMap_injective R A)
  have : ⇑(algebraMap S A') =
      hb.equiv ∘ (Algebra.linearMap R A).lTensor S ∘ (TensorProduct.rid R S).symm := by
    ext s
    simp [IsBaseChange.equiv_tmul, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact hb.equiv.injective.comp (h.comp (TensorProduct.rid R S).symm.injective)
end GlobalTheory
