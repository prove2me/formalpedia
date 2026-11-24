-- Prove2me | solution 1 for GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:43:54.765799+00:00
-- url     : https://prove2.me/submissions/9dcd8148-0fa6-4ede-8255-a8fcf2efb810

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLevelGoodAtAllPrimesAndIdx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevelAllPrimes
open GlobalTheory.HostModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LevelAllPrimes
namespace _root_.GlobalTheory.LevelAllPrimes
theorem _root_.solution (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {c : ℕ} (hc : Nat.Coprime c H.d)
    (ho : Odd (c ^ 2 + H.d)) :
    IsCoprime ((c : 𝓞 E) + H.rt) (c - H.rt) := by
  have h2 : Nat.Coprime 2 (c ^ 2 + H.d) := (Nat.coprime_two_left).2 ho
  have hc' : Nat.Coprime c (c ^ 2 + H.d) := by
    rw [sq, add_comm]
    exact (Nat.coprime_add_mul_right_right c H.d c).2 hc
  have hcop : IsCoprime ((2 * c : ℕ) : ℤ) ((c ^ 2 + H.d : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul h2 hc')
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (Int.cast : ℤ → 𝓞 E) huv
  push_cast at key
  refine ⟨(u : 𝓞 E) + v * (c - H.rt), u, ?_⟩
  linear_combination key - (v : 𝓞 E) * H.rt_sq
end _root_.GlobalTheory.LevelAllPrimes
end GlobalTheory.LevelAllPrimes
