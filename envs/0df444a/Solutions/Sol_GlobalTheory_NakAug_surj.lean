-- Prove2me | solution 1 for GlobalTheory.NakAug.surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:41.179481+00:00
-- url     : https://prove2.me/submissions/c221e999-f591-4508-84fc-8eb0a971bfe1

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanSubMemSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalSurjectiveOfCotangentSpanTop
import Theorems.Thm_GlobalTheory_PowerIdealSurjectivity_aeval_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.NakAug
namespace GlobalTheory.NakAug
theorem _root_.solution : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first
  | exact @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | (apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective ..)
end GlobalTheory.NakAug
