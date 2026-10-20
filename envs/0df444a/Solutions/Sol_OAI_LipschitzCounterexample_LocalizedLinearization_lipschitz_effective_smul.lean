-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalizedLinearization.lipschitz_effective_smul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:36:04.772297+00:00
-- url     : https://prove2.me/submissions/44fbd4e5-c222-4338-a2b8-2e7ba1d0a51d

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
universe uM uE
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem solution (p : M → E) (φ : M → ℝ) {A B C P : ℝ≥0}
    (hp : LipschitzWith C p) (hφ : LipschitzWith B φ)
    (hA : ∀ x, |φ x| ≤ A) (hP : ∀ x, φ x ≠ 0 → ‖p x‖ ≤ P) :
    LipschitzWith (A*C+B*P) (fun x => φ x • p x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have hpd : ‖p x - p y‖ ≤ C * dist x y := by rw [← dist_eq_norm]; exact hp.dist_le_mul x y
  have hφd : |φ x - φ y| ≤ B * dist x y := by rw [← Real.dist_eq]; exact hφ.dist_le_mul x y
  have hd := dist_nonneg (x := x) (y := y)
  have key : ∀ w : M, ‖p w‖ ≤ P → ∀ v : M, (φ x • p x - φ y • p y = φ v • (p x - p y) + (φ x - φ y) • p w) →
      ‖φ x • p x - φ y • p y‖ ≤ ((A * C + B * P : ℝ≥0) : ℝ) * dist x y := by
    intro w hw v hv
    rw [hv]
    calc ‖φ v • (p x - p y) + (φ x - φ y) • p w‖ ≤ ‖φ v • (p x - p y)‖ + ‖(φ x - φ y) • p w‖ := norm_add_le _ _
      _ = |φ v| * ‖p x - p y‖ + |φ x - φ y| * ‖p w‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ A * (C * dist x y) + (B * dist x y) * P :=
          add_le_add (mul_le_mul (hA v) hpd (norm_nonneg _) A.coe_nonneg)
            (mul_le_mul hφd hw (norm_nonneg _) (by positivity))
      _ = _ := by push_cast; ring
  by_cases hy : φ y ≠ 0
  · exact key y (hP y hy) x (by rw [smul_sub, sub_smul]; abel)
  · by_cases hx : φ x ≠ 0
    · exact key x (hP x hx) y (by rw [smul_sub, sub_smul]; abel)
    · push_neg at hx hy
      rw [hx, hy]; simp; positivity

