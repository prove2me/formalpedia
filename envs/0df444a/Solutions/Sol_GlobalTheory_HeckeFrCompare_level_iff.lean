-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.level_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:18:54.636696+00:00
-- url     : https://prove2.me/submissions/7b20e447-e80a-4acc-8ad2-2c01dfeaf960

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_nsmul_congr

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
theorem _root_.solution {A M P P' : Type} [AddCommGroup A] [Monoid M] (f : A → M) (hadd : ∀ a b, f (a + b) = f a * f b)
    (N : ℕ) (hN : ∀ a, f (N • a) = 1) {p : ℕ} (hp : p.Coprime N) (hN0 : N ≠ 0) (i : M → P) (i' : M → P')
    (g : P → P') :
    (∀ p' : ℕ, p * p' ≡ 1 [MOD N] → ∀ a, g (i (f (p' • a))) = i' (f a)) ↔ ∀ a, g (i (f a)) = i' (f (p • a)) := by
  refine ⟨fun h a => ?_, fun h p' hp' a => ?_⟩
  · obtain ⟨p', hp'⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hp hN0
    have hp' : p * p' ≡ 1 [MOD N] := hp'.2
    rw [← h p' hp', smul_smul, nsmul_congr f hadd N hN (mul_comm p p' ▸ hp'), one_smul]
  · rw [h, smul_smul, nsmul_congr f hadd N hN hp', one_smul]
end GlobalTheory.HeckeFrCompare
