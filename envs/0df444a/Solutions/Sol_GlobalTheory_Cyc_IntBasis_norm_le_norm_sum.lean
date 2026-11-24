-- Prove2me | solution 1 for GlobalTheory.Cyc.IntBasis.norm_le_norm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:57.017163+00:00
-- url     : https://prove2.me/submissions/460af918-40c4-479a-9440-60452b47902d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.IntBasis
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → Om l)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → f a ≠ 0 → f b ≠ 0 → ‖f a‖ ≠ ‖f b‖) :
    ∀ a ∈ s, ‖f a‖ ≤ ‖∑ b ∈ s, f b‖ := by
  classical
  intro a ha
  by_cases hfa : f a = 0
  · rw [hfa, norm_zero]
    exact norm_nonneg _
  have hat : a ∈ s.filter (fun b => f b ≠ 0) := Finset.mem_filter.2 ⟨ha, hfa⟩
  rw [← Finset.sum_filter_ne_zero s,
    IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne ⟨a, hat⟩]
  · exact Finset.le_sup' (fun b => ‖f b‖) hat
  · intro b hb c hc hbc
    have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
    have hc' := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
    exact h b hb'.1 c hc'.1 hbc hb'.2 hc'.2
end GlobalTheory.Cyc.IntBasis
