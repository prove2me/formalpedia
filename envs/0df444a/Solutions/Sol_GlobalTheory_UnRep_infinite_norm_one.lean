-- Prove2me | solution 1 for GlobalTheory.UnRep.infinite_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:06.543468+00:00
-- url     : https://prove2.me/submissions/9e95d432-305e-4811-88a7-790ae4a9d655

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
import Theorems.Thm_GlobalTheory_NormOneInfinite_normOne_infinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) : {l : E | l * c l = 1}.Infinite := by
  first
  | exact @_root_.GlobalTheory.NormOneInfinite.normOne_infinite
  | exact _root_.GlobalTheory.NormOneInfinite.normOne_infinite
  | (apply _root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormOneInfinite.normOne_infinite ..)
end GlobalTheory.UnRep
