-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OM.SchDiff.contDiff_iter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:10.979874+00:00
-- url     : https://prove2.me/submissions/05085a74-63ca-407e-8939-9cabb4c92b6c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OM GlobalTheory.CompanionTheory.OM.SchDiff
variable {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.CompanionTheory.OM.SchDiff
theorem _root_.solution {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (iteratedFDeriv ℝ n F) :=
  hF.iteratedFDeriv_right (by norm_cast)
end GlobalTheory.CompanionTheory.OM.SchDiff
