-- Prove2me | solution 1 for GlobalTheory.Twist.isFiniteType_of_locally_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:11.809449+00:00
-- url     : https://prove2.me/submissions/7354a4f1-ebe3-4a15-8835-edb682a3bd33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Theorems.Thm_GlobalTheory_Descent_finite


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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.Twist
theorem _root_.solution {ι : Type} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (e : ∀ (k : ι) (W : X.Opens), W ≤ U k → (F.restrict W.ι ≅ G.restrict W.ι))
    [hF : F.IsFiniteType] : G.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := hF.exists_localGeneratorsData
  exact ⟨generatorsOfLocallyIso hU e σ, ⟨fun p => ⟨(hσ.isFiniteType p.1).finite⟩⟩⟩
end GlobalTheory.Twist
