-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:35.466211+00:00
-- url     : https://prove2.me/submissions/19b17d64-ad84-4d1d-976b-eeccfcfbdf42

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZero
import Theorems.Thm_GlobalTheory_CompanionTheory_FirstOrderNbhd_mul_eq_zero_of_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FirstOrderNbhd
namespace GlobalTheory.CompanionTheory.FirstOrderNbhd
theorem _root_.solution : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (e : Sp R ⟶ U)
    [IsClosedImmersion e] (i' : Sp R ⟶ (e.ker ^ 2).subscheme),
    i' ≫ (e.ker ^ 2).subschemeι = e → ∀ a b : Γ((e.ker ^ 2).subscheme, ⊤),
    i'.appTop a = 0 → i'.appTop b = 0 → a * b = 0 := by
  intro R _ U e _ i' hi a b ha hb
  exact mul_eq_zero_of_lift e i' hi a b ha hb
end GlobalTheory.CompanionTheory.FirstOrderNbhd
