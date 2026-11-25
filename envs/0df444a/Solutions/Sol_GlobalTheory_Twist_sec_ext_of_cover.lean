-- Prove2me | solution 1 for GlobalTheory.Twist.sec_ext_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:05.075982+00:00
-- url     : https://prove2.me/submissions/e71077bf-810a-4e32-9276-1a1c517e3523

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso

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
theorem _root_.solution {ι : Type*} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) {s t : Γ(F, V)} (h : ∀ k, resM F (hW k) s = resM F (hW k) t) : s = t :=
  (abSheaf F).eq_of_locally_eq' W V (fun k => homOfLE (hW k)) hc s t h
end GlobalTheory.Twist
