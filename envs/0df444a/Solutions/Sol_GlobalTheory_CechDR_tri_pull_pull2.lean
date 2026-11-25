-- Prove2me | solution 1 for GlobalTheory.CechDR.tri_pull_pull2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:33.416954+00:00
-- url     : https://prove2.me/submissions/22c00800-a7f2-43fa-86c4-d1f6e2be8fb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_pullHyp2_comp
import Theorems.Thm_GlobalTheory_CechDR_pullHyp2_eq_of_natTrans


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
theorem _root_.solution (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HH2 s) :
    pullHyp2 (cechTripleRestrictComposite ψ φ s'') (pullHyp2 (pairPull h'') a) =
      pullHyp2 (cechTriplePullbackSecond h') (pullHyp2 (pairPull h) a) := by
  rw [← pullHyp2_comp, ← pullHyp2_comp]
  exact pullHyp2_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
    ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
      erw [mp_id]
      exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
        U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a
end GlobalTheory.CechDR
