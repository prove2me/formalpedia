-- Prove2me | solution 1 for GlobalTheory.Twist.isQuasicoherent_of_locally_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:52.315881+00:00
-- url     : https://prove2.me/submissions/b6895b04-1bea-4c6b-ba70-f2c5c17d86d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_restrict


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
theorem _root_.solution {ι : Type} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (e : ∀ k : ι, F.restrict (U k).ι ≅ G.restrict (U k).ι)
    [F.IsQuasicoherent] : G.IsQuasicoherent := by
  refine QCoh.isQuasicoherent_of_restrict G (fun k => (U k).ι) (fun x => ?_) fun k => ?_
  · obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hU.ge (Set.mem_univ x))
    exact ⟨l, by rwa [Scheme.Opens.opensRange_ι]⟩
  · exact (SheafOfModules.isQuasicoherent (U k).toScheme.ringCatSheaf).prop_of_iso (e k)
      (inferInstanceAs (F.restrict (U k).ι).IsQuasicoherent)
end GlobalTheory.Twist
