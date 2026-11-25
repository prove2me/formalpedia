-- Prove2me | solution 1 for GlobalTheory.CechDR.cechTripleRestrictComposite_injective_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:12.097364+00:00
-- url     : https://prove2.me/submissions/d5b80b21-ab34-4a0f-bb42-eb84c890dfdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Theorems.Thm_GlobalTheory_CechDR_restrict_bijective_two_of_basis
import Theorems.Thm_GlobalTheory_CechDR_triple_cover_affine
import Theorems.Thm_GlobalTheory_CechDR_exists_triple_below_two
import Theorems.Thm_GlobalTheory_CechDR_cechTripleRestrictComposite_pairRes_second

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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
variable {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
variable (ψ φ)
variable {ψ φ}
variable (ψ φ)
namespace GlobalTheory.CechDR
theorem _root_.solution (s'' : X'' ⟶ Sp R'') : Function.Injective (pullHyp2 (cechTripleRestrictComposite ψ φ s'')) := by
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective_two (ψ ≫ φ) s'').2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective_two (ψ ≫ φ) s'').2 y
  rw [cechTripleRestrictComposite_pairRes_second, cechTripleRestrictComposite_pairRes_second] at e
  rw [(restrict_bijective_two_of_basis s'' _ (triple_cover_affine ψ φ s'')
    (exists_triple_below_two ψ φ s'')).1 e]
end GlobalTheory.CechDR
