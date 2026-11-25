-- Prove2me | solution 1 for GlobalTheory.CechDR.cechTriple_restrict_restrict_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:28:34.549805+00:00
-- url     : https://prove2.me/submissions/8e7a2285-432d-4ae7-ab8f-fd63fe2d19f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_comp
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_eq_of_natTrans


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
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
namespace GlobalTheory.CechDR
theorem _root_.solution (a : HH1 s'') :
    pullHyp1 (cechTripleRestrictFirst ψ φ s'') (pullHyp1 (pairRes ψ s'') a) =
      pullHyp1 (cechTripleRestrictComposite ψ φ s'') (pullHyp1 (pairRes (ψ ≫ φ) s'') a) := by
  rw [← pullHyp1_comp, ← pullHyp1_comp]
  exact pullHyp1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a
end GlobalTheory.CechDR
