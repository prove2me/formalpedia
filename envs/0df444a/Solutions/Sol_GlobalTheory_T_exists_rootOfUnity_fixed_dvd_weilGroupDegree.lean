-- Prove2me | solution 1 for GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:38.927037+00:00
-- url     : https://prove2.me/submissions/65f58cf4-6d8a-4a55-af1a-3e4c35f610d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRootOfUnityFixedDvdWeilGroupDegree
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRootOfUnityFixedDvdWeilGroupDegreeStatement
import Theorems.Thm_GlobalTheory_exists_fixed_dvd_deg


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
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (k : ℕ), 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ := by
  first | exact @GlobalTheory.exists_fixed_dvd_deg | exact GlobalTheory.exists_fixed_dvd_deg | (intros; apply GlobalTheory.exists_fixed_dvd_deg <;> assumption)
end _root_.GlobalTheory.T
