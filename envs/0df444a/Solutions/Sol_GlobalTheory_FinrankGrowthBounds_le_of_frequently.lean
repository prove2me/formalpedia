-- Prove2me | solution 1 for GlobalTheory.FinrankGrowthBounds.le_of_frequently
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:08:07.083049+00:00
-- url     : https://prove2.me/submissions/9e2bbd93-47a8-414b-a098-a4d1e21d1da8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow

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
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
namespace GlobalTheory.FinrankGrowthBounds
theorem _root_.solution {a b g : ℕ} (h : ∀ M : ℕ, ∃ n, M ≤ n ∧ a * n ^ g ≤ b * (n + 8) ^ g) :
    a ≤ b := by
  by_contra hab
  push Not at hab
  have ht : Tendsto (fun n : ℕ => (b : ℝ) * (1 + 8 / (n : ℝ)) ^ g) atTop (𝓝 ((b : ℝ) * (1 + 0) ^ g)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 8)).pow g).const_mul _
  have hlt : (b : ℝ) * (1 + 0) ^ g < a := by simpa using hab
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually_lt_const hlt)
  obtain ⟨n, hn, hle⟩ := h (M + 1)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 := hM n (by omega)
  have h2 : (1 + 8 / (n : ℝ)) = (n + 8) / n := by field_simp
  rw [h2, div_pow, ← mul_div_assoc, div_lt_iff₀ (pow_pos hn0 g)] at h1
  have h3 : (a : ℝ) * n ^ g ≤ b * (n + 8) ^ g := by exact_mod_cast hle
  linarith
end GlobalTheory.FinrankGrowthBounds
