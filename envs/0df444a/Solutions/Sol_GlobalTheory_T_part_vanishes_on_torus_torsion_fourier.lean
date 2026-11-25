-- Prove2me | solution 1 for GlobalTheory.T.part_vanishes_on_torus_torsion_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:03.397237+00:00
-- url     : https://prove2.me/submissions/7a330174-cb32-4419-bcfe-3b7a7c751d64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PartVanishesOnTorusTorsionFourier
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PartVanishesOnTorusTorsionFourierStatement
import Theorems.Thm_GlobalTheory_TorsionFourier_part_vanishes_on_torsion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (d n : ℕ), (n : k) ≠ 0 → ∀ φ : (Φ.H d).Sec, (∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + n • w) → α = β) → (∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ α ψ, Φ.IsPart α φ ψ → ∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus ψ) := by
  first | exact @GlobalTheory.TorsionFourier.part_vanishes_on_torsion | exact GlobalTheory.TorsionFourier.part_vanishes_on_torsion | (intros; apply GlobalTheory.TorsionFourier.part_vanishes_on_torsion <;> assumption)
end _root_.GlobalTheory.T
