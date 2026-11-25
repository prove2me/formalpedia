-- Prove2me | solution 1 for GlobalTheory.tensor_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:57:58.519618+00:00
-- url     : https://prove2.me/submissions/c13e2f30-c4c8-4625-bfc1-98f680b19906

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
variable {K : Type u} [CommRing K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']
namespace GlobalTheory
theorem _root_.solution {D e h ε : Module.End K V} {D' e' h' : Module.End K V'}
    (hh : 1 - e = D * h + h * D) (hDe : D * e = 0) (heD : e * D = 0) (hDε : D * ε = -(ε * D))
    (hεe : ε * e = e * ε) (hεh : ε * h = -(h * ε)) (hεε : ε * ε = 1)
    (hh' : 1 - e' = D' * h' + h' * D') :
    (1 : Module.End K (V ⊗[K] V')) - TensorProduct.map e e' =
      (TensorProduct.map D 1 + TensorProduct.map ε D') *
          (TensorProduct.map h 1 + TensorProduct.map (ε * e) h') +
        (TensorProduct.map h 1 + TensorProduct.map (ε * e) h') *
          (TensorProduct.map D 1 + TensorProduct.map ε D') := by
  have a1 : D * (ε * e) = 0 := by rw [← mul_assoc, hDε, neg_mul, mul_assoc, hDe]; simp
  have a2 : ε * (ε * e) = e := by rw [← mul_assoc, hεε, one_mul]
  have a3 : ε * e * D = 0 := by rw [mul_assoc, heD, mul_zero]
  have a4 : ε * e * ε = e := by rw [mul_assoc, ← hεe, a2]
  have a5 : D * h = 1 - e - h * D := by rw [hh]; abel
  have a6 : D' * h' = 1 - e' - h' * D' := by rw [hh']; abel
  simp only [mul_add, add_mul, ← TensorProduct.map_mul, a1, a2, a3, a4, a5, a6, hεh]
  refine TensorProduct.ext' fun x y => ?_
  simp only [LinearMap.sub_apply, LinearMap.add_apply, TensorProduct.map_tmul, Module.End.one_apply,
    LinearMap.zero_apply, LinearMap.neg_apply, mul_one, one_mul, sub_tmul, tmul_sub, neg_tmul,
    zero_tmul]
  abel
end GlobalTheory
