-- Prove2me | solution 1 for GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:53.754774+00:00
-- url     : https://prove2.me/submissions/4309f60b-c5ce-41a2-b637-1122f3562352

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RangeComapIncludeRightField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RangeComapIncludeRightFieldStatement
import Theorems.Thm_GlobalTheory_range_comap_includeRight_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k], Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  first | exact @GlobalTheory.range_comap_includeRight_field | exact GlobalTheory.range_comap_includeRight_field | (intros; apply GlobalTheory.range_comap_includeRight_field <;> assumption)
end _root_.GlobalTheory.T
