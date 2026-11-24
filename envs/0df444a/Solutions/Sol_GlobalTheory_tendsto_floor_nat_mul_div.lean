-- Prove2me | solution 1 for GlobalTheory.tendsto_floor_nat_mul_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:50.950752+00:00
-- url     : https://prove2.me/submissions/4d3411fd-e3e0-415a-9646-1e8f78fdf6c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)
namespace GlobalTheory
theorem _root_.solution (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (⌊(n + 1 : ℝ) * x⌋ : ℝ) / (n + 1)) Filter.atTop (𝓝 x) := by
  have h := (tendsto_const_nhds (x := x)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds (fun n => ?_) fun n => ?_
  · have hn : (0 : ℝ) < n + 1 := by positivity
    simp only
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn]
    linarith [Int.lt_floor_add_one ((n + 1 : ℝ) * x)]
  · have hn : (0 : ℝ) < n + 1 := by positivity
    simp only
    rw [div_le_iff₀ hn]
    linarith [Int.floor_le ((n + 1 : ℝ) * x)]
end GlobalTheory
