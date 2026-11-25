-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.cechTripleRestrictComposite_injective_cohomology_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:20.272959+00:00
-- url     : https://prove2.me/submissions/b0e443bd-d929-4586-a8fc-54b8435581cc

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_cechTripleRestrictComposite_comp_pairRestrict
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  rw [cechTripleRestrictComposite_comp_pairRestrict, cechTripleRestrictComposite_comp_pairRestrict] at e
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s''
  have hcov := triple_cover_affine ψ φ s''
  have hdir := exists_triple_below_two ψ φ s''
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s'') _ H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s'') _ H hcov hdir
  rw [_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg e]
end GlobalTheory.CompanionTheory.HopfSys
