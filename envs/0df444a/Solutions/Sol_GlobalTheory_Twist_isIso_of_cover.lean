-- Prove2me | solution 1 for GlobalTheory.Twist.isIso_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:38.481899+00:00
-- url     : https://prove2.me/submissions/9dc1d873-1aa3-419d-a7ae-ef92c1044225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Theorems.Thm_GlobalTheory_Twist_bijective_app_of_cover
import Theorems.Thm_GlobalTheory_Twist_isIso_of_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res le_iSup_inf unitMod homOfLinear isoOfLinear toMod)
open GlobalTheory
open GlobalTheory.Twist
variable {X Y : Scheme.{0}}
variable {F G : X.Modules}
namespace GlobalTheory.Twist
theorem _root_.solution (φ : F ⟶ G) {ι : Type*} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (h : ∀ (k : ι) (W : X.Opens), W ≤ U k → Function.Bijective (φ.app W)) : IsIso φ :=
  isIso_of_bijective φ fun V => bijective_app_of_cover φ hU V fun k W _ hW => h k W hW
end GlobalTheory.Twist
