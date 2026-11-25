-- Prove2me | solution 1 for GlobalTheory.ZJ.Core.Test.exists_isGt_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:17.468508+00:00
-- url     : https://prove2.me/submissions/e0c1ba0f-9c2b-4d3f-8615-f1af535fa43f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian
import Theorems.Thm_GlobalTheory_ZJ_exists_fac_residue
import Theorems.Thm_GlobalTheory_gtBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
namespace Core.Test
theorem _root_.solution {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (K : Type) [Field K] (r : Sp K ⟶ Sp τ.V) (hr : Set.range r = {IsLocalRing.closedPoint τ.V}) :
    ∃ (G₁ : Over (Sp K)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (E : SplitExt (Sp K)) (φ : G₁.left ⟶ τ.H.left),
      E.IsGt G₁ ∧ IsGrpPullback G₁ τ.H r φ := by
  obtain ⟨s, rfl⟩ := exists_fac_residue τ.V K r hr
  obtain ⟨S, hS⟩ := τ.split
  obtain ⟨E, -, -, -, -, hE⟩ := gtBaseChange _ _ s S _ hS
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact ⟨_, _, Functor.isCommMonObj_obj, E, _, hE,
    (isGrpPullback_pullback _ s).comp (isGrpPullback_pullback τ.H _)⟩
end Core.Test
end GlobalTheory.ZJ
