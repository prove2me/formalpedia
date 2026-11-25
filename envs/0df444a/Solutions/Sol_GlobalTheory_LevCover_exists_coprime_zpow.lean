-- Prove2me | solution 1 for GlobalTheory.LevCover.exists_coprime_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:53.785025+00:00
-- url     : https://prove2.me/submissions/f05c7cc5-6c99-407e-b248-9b55cbd7caf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsObjTwistBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsoDifferBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
namespace GlobalTheory.LevCover
theorem _root_.solution {N : ℕ} (hN : 0 < N) {ζ ξ : kˣ} (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) :
    ∃ ν : ℤ, IsCoprime ν (N : ℤ) ∧ ξ = ζ ^ ν := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one (ξ := (ξ : k))
    (by rw [← Units.val_pow_eq_pow_val, hξ.pow_eq_one, Units.val_one])
  have hξi : ξ = ζ ^ i := Units.ext (by rw [Units.val_pow_eq_pow_val, hi])
  have hcop : i.Coprime N := (hζ.pow_iff_coprime hN i).1 (by rw [← hξi]; exact hξ)
  exact ⟨i, Nat.isCoprime_iff_coprime.2 hcop, by rw [hξi, zpow_natCast]⟩
end GlobalTheory.LevCover
