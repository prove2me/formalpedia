-- Prove2me | solution 1 for GlobalTheory.T.exists_base_near_of_decomposition_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:42:47.568733+00:00
-- url     : https://prove2.me/submissions/6a0d3522-54cf-42d5-b55e-ebf7cf6fd654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBaseNearOfDecompositionFixed
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBaseNearOfDecompositionFixedStatement
import Theorems.Thm_GlobalTheory_exists_base_near_of_dec_fixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by
  first | exact @GlobalTheory.exists_base_near_of_dec_fixed | exact GlobalTheory.exists_base_near_of_dec_fixed | (intros; apply GlobalTheory.exists_base_near_of_dec_fixed <;> assumption)
end _root_.GlobalTheory.T
