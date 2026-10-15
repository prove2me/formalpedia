-- Prove2me | solution 1 for OAI.DoublingHilbert.exists_energy_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:32:08.821174+00:00
-- url     : https://prove2.me/submissions/1604d9b7-7a78-4daf-b858-9bc7de1d607f

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Energy.lean:L295-L322
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.exists_energy_parameters. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy

-- ---- from OAI.Geometry.DoublingHilbert.Energy ----
namespace OAI

/-! Anisotropic energy bounds and arbitrarily small-energy period grids. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

section ProbabilityEnergy
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end ProbabilityEnergy

section Energies
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end Energies

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

theorem horizontalCoefficient_pos {D : ℝ} (hD : 0 ≤ D) : 0 < horizontalCoefficient D := by
  unfold horizontalCoefficient
  positivity

theorem verticalCoefficient_pos {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) :
    0 < verticalCoefficient D C := by
  unfold verticalCoefficient
  positivity

section AnisotropicEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end AnisotropicEnergy
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section
section NearMaxGrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end NearMaxGrid
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

/-- The order of choices is essential: the strip width follows the compact barrier,
then the base error and the unused radius are made small. -/
theorem exists_energy_parameters {D C η : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ W : ℕ, 0 < W ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      2 * (η / 8) + 16 * C * D ^ 2 / (W : ℝ) +
        ((W : ℝ) ^ 2 * horizontalCoefficient D + verticalCoefficient D C) * t < η := by
  obtain ⟨W, hW⟩ := exists_nat_gt (max 1 (64 * C * D ^ 2 / η))
  have hW1 : (1 : ℝ) < W := (le_max_left _ _).trans_lt hW
  have hWpos : 0 < W := by exact_mod_cast (lt_trans zero_lt_one hW1)
  have hWR : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hbig : 64 * C * D ^ 2 / η < W := (le_max_right _ _).trans_lt hW
  have hterm : 16 * C * D ^ 2 / (W : ℝ) < η / 4 := by
    apply (div_lt_iff₀ hWR).mpr
    have hh := (div_lt_iff₀ hη).mp hbig
    nlinarith
  let K := (W : ℝ) ^ 2 * horizontalCoefficient D + verticalCoefficient D C
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) (horizontalCoefficient_pos hD).le)
      (verticalCoefficient_pos hD hC)
  let t := min 1 (η / (4 * K))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : K * t ≤ η / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * K)).mp (min_le_right 1 (η / (4 * K)))
    change t * (4 * K) ≤ η at hh
    linarith
  exact ⟨W, hWpos, t, ht, ht1, by change 2 * (η / 8) + _ + K * t < η; linarith⟩

section SmallEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end SmallEnergy
end
end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter

theorem solution {D C η : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ W : ℕ, 0 < W ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      2 * (η / 8) + 16 * C * D ^ 2 / (W : ℝ) +
        ((W : ℝ) ^ 2 * horizontalCoefficient D + verticalCoefficient D C) * t < η := by
  first
    | exact OAI.DoublingHilbert.exists_energy_parameters hD hC hη
    | exact OAI.DoublingHilbert.exists_energy_parameters
    | (apply OAI.DoublingHilbert.exists_energy_parameters <;> assumption)
    | (intros; apply OAI.DoublingHilbert.exists_energy_parameters <;> assumption)
