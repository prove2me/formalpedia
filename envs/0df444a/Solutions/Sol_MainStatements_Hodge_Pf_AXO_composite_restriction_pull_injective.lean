-- Prove2me | solution 1 for MainStatements.Hodge.Pf.AXO.composite_restriction_pull_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:42.156245+00:00
-- url     : https://prove2.me/submissions/206c3230-d1b8-431d-8139-793e2e60ca2c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_restrict_pull1_injective_of_sep_glue
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_comma_of_basis
import Theorems.Thm_GlobalTheory_CechDR_exists_triple_below_two
import Theorems.Thm_GlobalTheory_CechDR_hasLoc_OAff
import Theorems.Thm_GlobalTheory_CechDR_triple_cover_affine
import Theorems.Thm_GlobalTheory_sep_of_factoring_cover


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
theorem _root_.solution (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  have k : ∀ c, (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := fun c ↦ by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
  rw [k, k] at e
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s''
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s'') _ H (triple_cover_affine ψ φ s'')
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s'') _ H (triple_cover_affine ψ φ s'')
    (exists_triple_below_two ψ φ s'')
  rw [CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg e]
end MainStatements.Hodge.Pf.AXO
