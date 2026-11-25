-- Prove2me | solution 1 for MainStatements.Hodge.Pf.AXO.HO1_eq_zero_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:42.080474+00:00
-- url     : https://prove2.me/submissions/2937aad4-9383-4a60-9301-1e0eea72b06b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_GlobalTheory_CatCoh_H1_eq_zero_of_isInitial


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.AXO
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
namespace MainStatements.Hodge.Pf.AXO
theorem _root_.solution [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s) : c = 0 := by
  let T0 : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  refine H1.eq_zero_of_isInitial (F := OAff s) (T₀ := op T0) ?_ c
  exact Limits.IsInitial.ofUniqueHom (fun V ↦ (homOfLE (show V.unop ≤ T0 from
    show V.unop.1 ≤ ⊤ from le_top)).op) (fun _ _ ↦ Subsingleton.elim _ _)
end MainStatements.Hodge.Pf.AXO
