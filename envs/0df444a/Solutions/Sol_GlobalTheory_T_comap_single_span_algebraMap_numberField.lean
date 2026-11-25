-- Prove2me | solution 1 for GlobalTheory.T.comap_single_span_algebraMap_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:18:51.686427+00:00
-- url     : https://prove2.me/submissions/f680a025-1d80-498c-854b-0943d3f8b699

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ComapSingleSpanAlgebraMapNumberField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ComapSingleSpanAlgebraMapNumberFieldStatement
import Theorems.Thm_GlobalTheory_comap_single_span_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι), (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) = Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  first | exact @GlobalTheory.comap_single_span_algebraMap | exact GlobalTheory.comap_single_span_algebraMap | (intros; apply GlobalTheory.comap_single_span_algebraMap <;> assumption)
end _root_.GlobalTheory.T
