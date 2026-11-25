-- Prove2me | solution 1 for GlobalTheory.CechDR.cechTripleRestrictComposite_pairRes_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:49.889844+00:00
-- url     : https://prove2.me/submissions/987225f5-5051-4b36-98ab-fe6257700e1d

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
variable {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
variable (ψ φ)
variable {ψ φ}
variable (ψ φ)
namespace GlobalTheory.CechDR
theorem _root_.solution (s'' : X'' ⟶ Sp R'') (c : HH1 s'') :
    pullHyp1 (cechTripleRestrictComposite ψ φ s'') (pullHyp1 (pairRes (ψ ≫ φ) s'') c) =
      pullHyp1 (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))) c := by
  rw [← pullHyp1_comp]
  exact pullHyp1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
end GlobalTheory.CechDR
