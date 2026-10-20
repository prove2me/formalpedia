-- Prove2me | solution 1 for OAI.LipschitzCounterexample.SeparatingStages.support_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:43:24.668906+00:00
-- url     : https://prove2.me/submissions/a56b53f5-c8d4-4b5f-94f6-b357d620f9cb

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
universe uIndex uOtherIndex
open scoped BigOperators InnerProductSpace Topology ENNReal


theorem solution {k : ℕ} (hk : 0 < k) {s t : CubeSpace k} (j : Fin k)
    (hst : 2/(k : ℝ) < |s j-t j|) (a : Label k) :
    normalized k s a = 0 ∨ normalized k t a = 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨h1, h2⟩ := hne
  have key : ∀ u : CubeSpace k, normalized k u a ≠ 0 → |(k:ℝ) * u j - ((a j : ℤ) : ℝ)| < 1 := by
    intro u hu
    have hG : G k u a ≠ 0 := by
      intro h0
      apply hu
      change ‖G k u‖⁻¹ * G k u a = 0
      rw [h0, mul_zero]
    rw [G_apply] at hG
    have hpj : psi ((k:ℝ) * u j - ((a j : ℤ) : ℝ)) ≠ 0 :=
      fun h0 => hG (Finset.prod_eq_zero (Finset.mem_univ j) h0)
    have hnn : 0 ≤ psi ((k:ℝ) * u j - ((a j : ℤ) : ℝ)) := expNegInvGlue.nonneg _
    exact psi_pos_iff.mp (lt_of_le_of_ne hnn (Ne.symm hpj))
  have hs := key s h1
  have ht := key t h2
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have h3 : |(k:ℝ) * (s j - t j)| < 2 := by
    calc |(k:ℝ) * (s j - t j)|
        = |((k:ℝ) * s j - ((a j : ℤ) : ℝ)) - ((k:ℝ) * t j - ((a j : ℤ) : ℝ))| := by ring_nf
      _ ≤ |(k:ℝ) * s j - ((a j : ℤ) : ℝ)| + |(k:ℝ) * t j - ((a j : ℤ) : ℝ)| := abs_sub _ _
      _ < 2 := by linarith
  rw [abs_mul, abs_of_pos hkpos] at h3
  rw [div_lt_iff₀ hkpos] at hst
  linarith

