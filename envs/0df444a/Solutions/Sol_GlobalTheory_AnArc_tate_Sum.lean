-- Prove2me | solution 1 for GlobalTheory.AnArc.tate_Sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:29.751605+00:00
-- url     : https://prove2.me/submissions/e86b62b3-becc-49d4-9528-a080f86eca40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_tate_exponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (τ₀ w : ℂ) (v : (tate τ₀).V) : (tate τ₀).Sum 1 (0 : ℤ) 1 w v =
    ∑' μ : ℤ, eTwoPi (μ ^ 2 * (τ₀ + 2 * w) / 2 + μ * v.1 (1 : ℤ)) := by
  refine tsum_congr fun μ : ℤ => ?_
  obtain ⟨l, z⟩ : (ℤ →+ ℂ) × (Fin 0 → ℂ) := v
  have h1 : l (@HAdd.hAdd ℤ ℤ ℤ _ 0 ((1 : ℕ) • μ)) = μ * l 1 := by simpa using map_zsmul l μ 1
  rw [tate_exponent]
  change (psiInt τ₀ μ : ℂ) ^ 1 * eTwoPi (TInt τ₀ μ 0) * eTwoPi (l (@HAdd.hAdd ℤ ℤ ℤ _ 0 ((1 : ℕ) • μ))) * 1 *
      eTwoPi (w * ((μ ^ 2 : ℤ) : ℂ)) =
    eTwoPi (μ ^ 2 * (τ₀ + 2 * w) / 2 + μ * l 1)
  rw [h1]
  simp only [coe_psiInt, pow_one, mul_one, TInt_apply, ← e_add]
  congr 1; push_cast; ring
end GlobalTheory.AnArc
