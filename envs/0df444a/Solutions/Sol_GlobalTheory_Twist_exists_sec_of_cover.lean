-- Prove2me | solution 1 for GlobalTheory.Twist.exists_sec_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:09:53.793802+00:00
-- url     : https://prove2.me/submissions/7f3b9ade-1c55-4b74-a161-7a576fde327b

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
    (hc : V ≤ iSup W) (s : ∀ k, Γ(F, W k))
    (h : ∀ k l, resM F (inf_le_left : W k ⊓ W l ≤ W k) (s k) =
      resM F (inf_le_right : W k ⊓ W l ≤ W l) (s l)) :
    ∃ t : Γ(F, V), ∀ k, resM F (hW k) t = s k :=
  ((abSheaf F).existsUnique_gluing' W V (fun k => homOfLE (hW k)) hc s h).exists
end GlobalTheory.Twist
