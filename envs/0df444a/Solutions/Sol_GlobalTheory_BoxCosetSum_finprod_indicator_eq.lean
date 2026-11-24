-- Prove2me | solution 1 for GlobalTheory.BoxCosetSum.finprod_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:36.149568+00:00
-- url     : https://prove2.me/submissions/485e5930-a07b-4c0c-8bf7-36dddc4c536c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite
import Theorems.Thm_GlobalTheory_BoxCosetSum_eventually_evalV_mem_integers
import Theorems.Thm_GlobalTheory_BoxCosetSum_mem_boxSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.BoxCosetSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.BoxCosetSum
theorem _root_.solution (κ : Type) [Finite κ]
    (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F)
    (r y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))) =
      Set.indicator {z | z - r ∈ boxSub κ B} (fun _ => (1 : ℂ)) y := by
  have key : ∀ v, ((fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}) ↔
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ B v := by
    intro v
    simp only [Set.mem_setOf_eq, Pi.sub_apply, map_sub]
  by_cases h : y - r ∈ boxSub κ B
  · rw [Set.indicator_of_mem (show y ∈ {z | z - r ∈ boxSub κ B} from h)]
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [Set.indicator_of_mem ((key v).2 fun i => h i v), Pi.one_apply]
  · rw [Set.indicator_of_notMem (show y ∉ {z | z - r ∈ boxSub κ B} from h)]
    rw [mem_boxSub] at h
    push_neg at h
    obtain ⟨i0, v0, hv0⟩ := h
    apply finprod_eq_zero _ v0
    · rw [Set.indicator_of_notMem]
      rw [key v0]
      exact fun H => hv0 (H i0)
    · have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
        Filter.eventually_cofinite.1 hBf
      have hI : (⋃ i, {v | ¬ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ v.adicCompletionIntegers F}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (eventually_evalV_mem_integers ((y - r) i))
      refine (hT.union hI).subset ?_
      intro v hv
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
      apply hv
      dsimp only
      rw [Set.indicator_of_mem, Pi.one_apply]
      rw [key v]
      intro i
      have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := hc.2 i
      rw [← hc.1] at h2
      exact h2
end GlobalTheory.BoxCosetSum
