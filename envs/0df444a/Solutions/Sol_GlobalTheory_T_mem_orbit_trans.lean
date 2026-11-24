-- Prove2me | solution 1 for GlobalTheory.T.mem_orbit_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:26.330972+00:00
-- url     : https://prove2.me/submissions/3e36b6a3-5004-43f2-9042-94aedce72d51

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_OrbitTrans
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_OrbitTransStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_orbit_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x y w : X.left), y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans <;> assumption)
end _root_.GlobalTheory.T
