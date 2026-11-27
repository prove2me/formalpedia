-- Prove2me | solution 1 for GlobalTheory.T.tateIsometry_of_finiteLevel_isometries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:39.939901+00:00
-- url     : https://prove2.me/submissions/ab287ad9-5dbc-4fb5-84de-cbcfc16d3d10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsometryOfFiniteLevelIsometries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsometryOfFiniteLevelIsometriesStatement
import Theorems.Thm_GlobalTheory_TateTower_tateIso_of_levels


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (k : ℕ) (z : K) (κ : Type) (lam : κ → D.La) (y : κ → Q), 0 < k → (∀ n, 0 < n → Finite {x : Q // x ^ n = 1}) → (∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c → e n (x ^ m) (x' ^ m) (c ^ m)) → (∀ m, 0 < m → ∃ (ζ : Kˣ) (ev : D.La → Q), IsPrimitiveRoot ζ (k * m) ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = (k * m) • c) ∧ (∀ x, x ^ (k * m) = 1 ↔ ∃ a, ev a = x) ∧ (∀ a c, e (k * m) (ev a) (ev c) (ζ ^ D.EF a c)) ∧ (ζ : K) ^ m = z ∧ ∀ i, ev (lam i) ^ m = y i) → ∃ I : TateIso D K Q act e, (I.ζ k : K) = z ∧ ∀ i, I.ev k (lam i) = y i := by
  first | exact @GlobalTheory.TateTower.tateIso_of_levels | exact GlobalTheory.TateTower.tateIso_of_levels | (intros; apply GlobalTheory.TateTower.tateIso_of_levels <;> assumption)
end _root_.GlobalTheory.T
