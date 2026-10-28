-- Prove2me | solution 1 for OAI.Rokhlin.mixing_all_finite_orders
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:01:27.166842+00:00
-- url     : https://prove2.me/submissions/11179382-952f-46fc-9f74-c9a152832036
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Rokhlin
import Definitions.Def_OAIQ3Ro001
import Theorems.Thm_OAI_Rokhlin_sequential_mixing_all

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω]
lemma timeMap_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T n = (T : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

lemma layoutTime_gap_bound {k : ℕ} (g : Fin (k-1) → ℕ+) (i j : Fin k) (hij : i<j) :
    ∃ q : Fin (k-1), layoutTime g i+(g q:ℕ) ≤ layoutTime g j := by
  classical
  let q : Fin (k-1) := ⟨i.val,by have := j.isLt; have := hij; omega⟩
  let s : Finset (Fin (k-1)) := Finset.univ.filter (fun t => t.val < i.val)
  let t : Finset (Fin (k-1)) := Finset.univ.filter (fun t => t.val < j.val)
  have hqs : q ∉ s := by simp [s,q]
  have hsub : insert q s ⊆ t := by
    intro l hl
    rcases Finset.mem_insert.mp hl with h | h
    · subst l; simpa [t,q] using hij
    · have hl := (Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans hl hij⟩
  refine ⟨q,?_⟩
  have hei : layoutTime g i = ∑ l ∈ s, (g l:ℕ) := by simp [layoutTime,s,Finset.sum_filter]
  have hej : layoutTime g j = ∑ l ∈ t, (g l:ℕ) := by simp [layoutTime,t,Finset.sum_filter]
  rw [hei,hej,add_comm,←Finset.sum_insert (f := fun l => (g l:ℕ)) hqs]
  exact Finset.sum_le_sum_of_subset hsub

lemma mixing_nat_of_IsMixing (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (h : IsMixing μ T) :
    ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)) := by
  intro s t hs ht
  have hc : Tendsto (fun n : ℕ => (n:ℤ)) atTop (comap Int.natAbs atTop) := by
    rw [tendsto_comap_iff]
    change Tendsto (fun n : ℕ => Int.natAbs (n:ℤ)) atTop atTop
    exact tendsto_id
  have hh := (h s t hs ht).comp hc
  change Tendsto (fun n : ℕ => μ (s ∩ timeMap T (n:ℤ) ⁻¹' t)) atTop (𝓝 (μ s*μ t)) at hh
  simpa only [timeMap_nat] using hh

lemma mixingOfOrder_of_sequential (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (k : ℕ)
    (hseq : SequentialMixing μ T k) : MixingOfOrder μ T k := by
  classical
  intro A hA
  by_contra hn
  have hbad : ∃ s : Set ENNReal, s ∈ 𝓝 (∏ i, μ (A i)) ∧
      ¬∀ᶠ g : Fin (k-1) → ℕ+ in atTop,
        μ (⋂ i, timeMap T (layoutTime g i : ℤ) ⁻¹' A i) ∈ s := by
    rw [Filter.tendsto_def] at hn
    push Not at hn
    obtain ⟨s,hs,hout⟩ := hn
    exact ⟨s,hs,hout⟩
  obtain ⟨s,hs,hbad⟩ := hbad
  have hex (r : ℕ) : ∃ g : Fin (k-1) → ℕ+, (∀ j, r < (g j:ℕ)) ∧
      μ (⋂ i, timeMap T (layoutTime g i : ℤ) ⁻¹' A i) ∉ s := by
    have hfreq : ∃ᶠ g : Fin (k-1) → ℕ+ in atTop,
        μ (⋂ i, timeMap T (layoutTime g i : ℤ) ⁻¹' A i) ∉ s := Filter.not_eventually.mp hbad
    obtain ⟨g,hg,hout⟩ := frequently_atTop.1 hfreq (fun _ => (⟨r+1,by omega⟩ : ℕ+))
    exact ⟨g,fun j => by have := hg j; change r+1 ≤ (g j:ℕ) at this; omega,hout⟩
  choose g hg hout using hex
  let d r i := layoutTime (g r) i
  have hd : Spaced d := by
    intro r i j hij
    obtain ⟨q,hq⟩ := layoutTime_gap_bound (g r) i j hij
    have hh := hg r q
    dsimp [d]
    omega
  have ht := hseq d hd A hA
  have he := ht.eventually hs
  obtain ⟨r,hr⟩ := he.exists
  apply hout r
  change μ (⋂ i, (T^[layoutTime (g r) i]) ⁻¹' A i) ∈ s at hr
  simpa only [timeMap_nat] using hr
end

open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω]

theorem mixing_all_finite_orders_oai (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (h_pres : MeasurePreserving T μ μ) (h_mix : IsMixing μ T) :
    ∀ k : ℕ, 3 ≤ k → MixingOfOrder μ T k := by
  intro k _
  exact mixingOfOrder_of_sequential μ T k
    (sequential_mixing_all μ T h_pres (mixing_nat_of_IsMixing μ T h_mix) k)

end Rokhlin

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Rokhlin.mixing_all_finite_orders_oai.{u_1} := @OAI.Rokhlin.mixing_all_finite_orders_oai.{u_1}
