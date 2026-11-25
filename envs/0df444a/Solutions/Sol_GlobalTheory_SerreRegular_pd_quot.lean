-- Prove2me | solution 1 for GlobalTheory.SerreRegular.pd_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:19:01.490429+00:00
-- url     : https://prove2.me/submissions/a1bfc17f-b7d0-41c6-9b78-9e9d03c81acc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SerreRegular_pd_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
open GlobalTheory.SerreRegular
namespace GlobalTheory.SerreRegular
theorem _root_.solution {A : Type} [CommRing A] [IsNoetherianRing A] {x : A} (hx : IsSMulRegular A x)
    (n : ℕ) (M : ModuleCat.{0} A) [Module.Finite A M] (hM : IsSMulRegular M x)
    (h : HasProjectiveDimensionLE M n) :
    HasProjectiveDimensionLE (ModuleCat.of (A ⧸ Ideal.span {x}) ((A ⧸ Ideal.span {x}) ⊗[A] M)) n := by
  refine pd_baseChange (fun N => IsSMulRegular N x) ?_ n M hM h
  intro N r f hf hN
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    funext i
    exact hx (congrFun (congrArg Subtype.val hab) i)
  · have e1 : Function.Exact (LinearMap.toSpanSingleton A A x) (Ideal.span {x}).mkQ := by
      intro y
      simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine lTensor_injective_of_exact_of_exact_of_rTensor_injective e1
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map f) hf ?_
      (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))
    have e2 : ∀ t, TensorProduct.lid A N ((LinearMap.toSpanSingleton A A x).rTensor N t) =
        x • TensorProduct.lid A N t := by
      intro t
      induction t with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb, smul_add]
      | tmul a m => simp [smul_smul, mul_comm]
    intro a b hab
    apply (TensorProduct.lid A N).injective
    apply hN
    simp only [← e2, hab]
end GlobalTheory.SerreRegular
