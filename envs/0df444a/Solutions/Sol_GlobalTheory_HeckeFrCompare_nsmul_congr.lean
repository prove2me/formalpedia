-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.nsmul_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:59.629495+00:00
-- url     : https://prove2.me/submissions/2c9321a8-46c5-4220-9688-cee0b1cc73d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution {A M : Type} [AddCommGroup A] [Monoid M] (f : A → M) (hadd : ∀ a b, f (a + b) = f a * f b)
    (N : ℕ) (hN : ∀ a, f (N • a) = 1) {m n : ℕ} (h : m ≡ n [MOD N]) (a : A) : f (m • a) = f (n • a) := by
  have key : ∀ k : ℕ, f (k • a) = f ((k % N) • a) := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k N, add_smul, hadd, mul_smul, hN, _root_.mul_one]
  rw [key m, key n, h]
end GlobalTheory.HeckeFrCompare
