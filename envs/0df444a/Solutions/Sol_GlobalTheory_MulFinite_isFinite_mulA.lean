-- Prove2me | solution 1 for GlobalTheory.MulFinite.isFinite_mulA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:12:56.649594+00:00
-- url     : https://prove2.me/submissions/3664b362-d67b-4f15-b064-c1a5651e5263

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Theorems.Thm_GlobalTheory_MulFinite_isFinite_of_relAmple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial
namespace GlobalTheory.MulFinite
theorem _root_.solution :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → PolBaseChangeSt → (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left := by
  intro h _ _ S P n hn
  have H := h S P n
  rw [← Nat.cast_pow] at H
  obtain ⟨α, hα⟩ := H
  have := P.isAb.proper
  exact isFinite_of_relAmple P.A P.L P.isLB P.ample _ (n ^ 2) (by positivity) α hα
end GlobalTheory.MulFinite
