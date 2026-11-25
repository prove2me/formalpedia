-- Prove2me | solution 1 for GlobalTheory.AnDim.le_analyticDim_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:31.848744+00:00
-- url     : https://prove2.me/submissions/dc15a040-6fe3-4e3c-81a5-808afbf274c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_GlobalTheory_AnDim_le_analyticDim
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution {A : FinHolAtlas d X} {T : Set X} {k : ℕ} :
    (k : WithBot ℕ∞) ≤ analyticDim A T ↔ ∃ n, k ≤ n ∧ (regularLocus A T n).Nonempty := by
  refine ⟨fun h => ?_, fun ⟨n, hk, hn⟩ => le_trans (by exact_mod_cast hk) (le_analyticDim hn)⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ n, (regularLocus A T n).Nonempty → n < k := fun n hn =>
    lt_of_not_ge fun hk => hn.ne_empty (hcon n hk)
  cases k with
  | zero =>
    have : analyticDim A T ≤ ⊥ := iSup₂_le fun n hn => absurd (hlt n hn) (Nat.not_lt_zero n)
    exact absurd (h.trans this) (by simp)
  | succ k =>
    have : analyticDim A T ≤ (k : WithBot ℕ∞) :=
      iSup₂_le fun n hn => by exact_mod_cast Nat.lt_succ_iff.1 (hlt n hn)
    have h2 : k + 1 ≤ k := by exact_mod_cast h.trans this
    omega
end GlobalTheory.AnDim
