-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.existsUnique_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:15.835801+00:00
-- url     : https://prove2.me/submissions/94154f75-11f6-4af5-be3e-8ec82a362510

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
open GlobalTheory.AbLaw.SecOn
open GlobalTheory.LB
variable {L M H : LB X} {V W : X.Opens}
namespace GlobalTheory.AbLaw.SecOn
theorem _root_.solution {I : Type} (O : I → X.Opens) (hO : ∀ a, O a ≤ V) (hc : V ≤ ⨆ a, O a)
    (s : ∀ a, SecOn M (O a))
    (h : ∀ a b, restrict M (inf_le_left : O a ⊓ O b ≤ O a) (s a) =
      restrict M (inf_le_right : O a ⊓ O b ≤ O b) (s b)) :
    ∃! t : SecOn M V, ∀ a, restrict M (hO a) t = s a :=
  TopCat.Sheaf.existsUnique_gluing' (C := Ab.{0}) ⟨secPresheaf M, isSheaf_secPresheaf M⟩ O V
    (fun a => homOfLE (hO a)) hc s h
end GlobalTheory.AbLaw.SecOn
