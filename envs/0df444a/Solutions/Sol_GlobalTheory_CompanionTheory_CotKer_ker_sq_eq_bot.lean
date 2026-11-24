-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotKer.ker_sq_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:34.882264+00:00
-- url     : https://prove2.me/submissions/a4e46e12-480a-4058-acc7-e2cd8584a998

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMap
import Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_mul_eq_zero_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotKer
namespace GlobalTheory.CompanionTheory.CotKer
theorem _root_.solution {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) : (spMap q).ker ^ 2 = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    Scheme.Hom.ker_apply, pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  exact (Submodule.mem_bot _).mpr (mul_eq_zero_top q hq a b ha hb)
end GlobalTheory.CompanionTheory.CotKer
