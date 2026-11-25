-- Prove2me | solution 1 for GlobalTheory.AffGlue.secEquiv_resM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:17.399461+00:00
-- url     : https://prove2.me/submissions/b814a702-c0a3-453b-b824-b7d94ae91984

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AffGlue
attribute [instance] Data.grp Data.mod
variable {T : Scheme.{0}} (D : Data T)
variable {D}
namespace GlobalTheory.AffGlue
theorem _root_.solution (hD : (famPresheaf D).IsSheaf) {V V' : T.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V) (s : Γ(toModules D hD, V)) :
    secEquiv hD hV' (GlobalTheory.Twist.resM (toModules D hD) h s) = D.ρ hV hV' h (secEquiv hD hV s) :=
  (fam_rel D (show fam D V from s) ⟨V, hV, le_rfl⟩ ⟨V', hV', h⟩ h).symm
end GlobalTheory.AffGlue
