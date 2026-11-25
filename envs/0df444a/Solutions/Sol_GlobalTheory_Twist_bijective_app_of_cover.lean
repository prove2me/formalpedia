-- Prove2me | solution 1 for GlobalTheory.Twist.bijective_app_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:12.985365+00:00
-- url     : https://prove2.me/submissions/302e6ac7-4e63-4b20-b421-b546f48a93c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Theorems.Thm_GlobalTheory_Twist_app_resM
import Theorems.Thm_GlobalTheory_Twist_sec_ext_of_cover
import Theorems.Thm_GlobalTheory_Twist_exists_sec_of_cover

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
    (V : X.Opens) (h : ∀ (k : ι) (W : X.Opens), W ≤ V → W ≤ U k → Function.Bijective (φ.app W)) :
    Function.Bijective (φ.app V) := by
  constructor
  · intro s t e
    refine sec_ext_of_cover (fun k => V ⊓ U k) (fun _ => inf_le_left) (le_iSup_inf hU V)
      fun k => (h k _ inf_le_left inf_le_right).1 ?_
    rw [app_resM, app_resM, e]
  · intro t
    choose s hs using fun k => (h k _ inf_le_left inf_le_right).2
      (resM G (inf_le_left : V ⊓ U k ≤ V) t)
    obtain ⟨r, hr⟩ := exists_sec_of_cover (fun k => V ⊓ U k) (fun _ => inf_le_left)
      (le_iSup_inf hU V) s fun k l =>
        (h k _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)).1 (by
          rw [app_resM, app_resM, hs, hs, resM_resM, resM_resM])
    refine ⟨r, sec_ext_of_cover (fun k => V ⊓ U k) (fun _ => inf_le_left) (le_iSup_inf hU V)
      fun k => ?_⟩
    rw [← app_resM, hr, hs]
end GlobalTheory.Twist
