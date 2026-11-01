-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:23:53.969303+00:00
-- url     : https://prove2.me/submissions/66c9a4de-12d7-4de4-9f0b-fcb9e82d45a5

import Mathlib
import Definitions.Def_OAIQ053K012
import Definitions.Def_OAIQ053K023
import Definitions.Def_OAIQ053K026
import Definitions.Def_OAIQ053K032
import Definitions.Def_OAIQ053K039
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_selectCompleted_spec_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_SumLaws
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem expect_sumMix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω ⊕ Ξ → ℝ) :
    (sumMix θ hθ0 hθ1 μ ν).expect f =
      θ*μ.expect (fun ω => f (.inl ω))+(1-θ)*ν.expect (fun ξ => f (.inr ξ)) := by
  simp only [expect, sumMix, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    mul_assoc, Finset.mul_sum]

theorem property_sumMix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (R : Ω ⊕ Ξ → Prop)
    (hμ : ∀ ω, 0 < μ.weight ω → R (.inl ω))
    (hν : ∀ ξ, 0 < ν.weight ξ → R (.inr ξ)) :
    ∀ z, 0 < (sumMix θ hθ0 hθ1 μ ν).weight z → R z := by
  intro z hz
  cases z with
  | inl ω =>
    apply hμ ω
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) (μ.nonneg ω)
    simp only [sumMix, Sum.elim_inl, heq, mul_zero] at hz
    exact lt_irrefl _ hz
  | inr ξ =>
    apply hν ξ
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) (ν.nonneg ξ)
    simp only [sumMix, Sum.elim_inr, heq, mul_zero] at hz
    exact lt_irrefl _ hz

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_WeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]
open MarginalRounding

omit [DecidableEq I] in
theorem up_pos {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < up p i j r := by
  exact lt_min (sub_pos.mpr (mem_fractional p i |>.mp hi).2)
    (div_pos (mem_fractional p j |>.mp hj).1 hr)
omit [DecidableEq I] in
theorem down_pos {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < down p i j r := by
  exact lt_min (mem_fractional p i |>.mp hi).1
    (div_pos (sub_pos.mpr (mem_fractional p j |>.mp hj).2) hr)

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_Conditioning
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

 theorem exists_support_le_expect (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ∃ ω, 0 < μ.weight ω ∧ f ω ≤ μ.expect f := by
  classical
  have hn : ∃ ω, 0 < μ.weight ω := by
    by_contra h
    push Not at h
    have hz : ∀ ω, μ.weight ω=0 := fun ω => le_antisymm (h ω) (μ.nonneg ω)
    have ht := μ.total
    simp only [hz, sum_const_zero] at ht
    norm_num at ht
  by_contra h
  push Not at h
  have hs : μ.expect (fun _ => μ.expect f) < μ.expect f := by
    apply sum_lt_sum
    · intro ω _
      by_cases hp : 0 < μ.weight ω
      · exact mul_le_mul_of_nonneg_left (h ω hp).le (μ.nonneg ω)
      · rw [le_antisymm (le_of_not_gt hp) (μ.nonneg ω), zero_mul, zero_mul]
    · obtain ⟨ω,hω⟩ := hn
      exact ⟨ω, mem_univ _, mul_lt_mul_of_pos_left (h ω hω) hω⟩
  rw [expect_const] at hs
  exact lt_irrefl _ hs

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_WeightedPartial
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding
open MarginalRounding
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_partial_law (p β : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hβ : ∀ i, 0 < β i) :
    ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
      ∃ (μ : FiniteLaw Ω) (Q : Ω → I → ℝ),
        (∀ ω, 0 < μ.weight ω →
          (∀ i, 0 ≤ Q ω i) ∧ (∀ i, Q ω i ≤ 1) ∧
          (fractional (Q ω)).card ≤ 1 ∧ (∑ i, β i*Q ω i)=∑ i, β i*p i) ∧
        (∀ i, μ.expect (fun ω => Q ω i)=p i) ∧
        (∀ i j, i ≠ j → μ.expect (fun ω => Q ω i*Q ω j) ≤ p i*p j) := by
  classical
  suffices h : ∀ n : ℕ, ∀ p : I → ℝ, (fractional p).card=n →
      (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1) →
      ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
        ∃ (μ : FiniteLaw Ω) (Q : Ω → I → ℝ),
          (∀ ω, 0 < μ.weight ω →
            (∀ i, 0 ≤ Q ω i) ∧ (∀ i, Q ω i ≤ 1) ∧
            (fractional (Q ω)).card ≤ 1 ∧ (∑ i, β i*Q ω i)=∑ i, β i*p i) ∧
          (∀ i, μ.expect (fun ω => Q ω i)=p i) ∧
          (∀ i j, i ≠ j → μ.expect (fun ω => Q ω i*Q ω j) ≤ p i*p j) by
    exact h _ p rfl hp0 hp1
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hn hp0 hp1
    by_cases hsmall : (fractional p).card ≤ 1
    · refine ⟨PUnit, inferInstance, FiniteLaw.dirac PUnit.unit, fun _ => p, ?_, ?_, ?_⟩
      · exact fun _ _ => ⟨hp0, hp1, hsmall, rfl⟩
      · intro i; exact FiniteLaw.expect_dirac _ _
      · intro i j _; exact le_of_eq (FiniteLaw.expect_dirac _ _)
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (lt_of_not_ge hsmall)
    let r : ℝ := β i/β j
    have hr : 0 < r := div_pos (hβ i) (hβ j)
    let u := up p i j r
    let d := down p i j r
    have hu : 0 < u := up_pos hr hi hj
    have hd : 0 < d := down_pos hr hi hj
    have bud := move_bounds hp0 hp1 hij hr (show -d ≤ u by linarith) (le_refl u)
    have bdd := move_bounds hp0 hp1 hij hr (le_refl (-d)) (show -d ≤ u by linarith)
    obtain ⟨Ω, instΩ, hexμ⟩ := ih _ (hn ▸ up_smaller hr hij hi hj) (move p i j r u) rfl bud.1 bud.2
    let := instΩ
    obtain ⟨μ, Q, hsμ, hmμ, hpμ⟩ := hexμ
    obtain ⟨Ξ, instΞ, hexν⟩ := ih _ (hn ▸ down_smaller hr hij hi hj) (move p i j r (-d)) rfl bdd.1 bdd.2
    let := instΞ
    obtain ⟨ν, R, hsν, hmν, hpν⟩ := hexν
    let θ : ℝ := d/(u+d)
    have hθ0 : 0 ≤ θ := (div_pos hd (add_pos hu hd)).le
    have hθ1 : θ ≤ 1 := (div_le_one (add_pos hu hd)).mpr (by linarith)
    have hwμ : (∑ k, β k*move p i j r u k)=∑ k, β k*p k := weighted_sum β p (ne_of_gt (hβ j)) u
    have hwν : (∑ k, β k*move p i j r (-d) k)=∑ k, β k*p k := weighted_sum β p (ne_of_gt (hβ j)) (-d)
    refine ⟨Ω ⊕ Ξ, inferInstance, FiniteLaw.sumMix θ hθ0 hθ1 μ ν, Sum.elim Q R, ?_, ?_, ?_⟩
    · apply FiniteLaw.property_sumMix θ hθ0 hθ1 μ ν
      · intro ω hω
        simpa only [Sum.elim_inl, hwμ] using hsμ ω hω
      · intro ξ hξ
        simpa only [Sum.elim_inr, hwν] using hsν ξ hξ
    · intro k
      rw [FiniteLaw.expect_sumMix]
      simp only [Sum.elim_inl, Sum.elim_inr, hmμ, hmν]
      exact endpoint_mean p i j k r hu hd
    · intro k l hkl
      rw [FiniteLaw.expect_sumMix]
      simp only [Sum.elim_inl, Sum.elim_inr]
      calc
        _ ≤ θ*(move p i j r u k*move p i j r u l)+
            (1-θ)*(move p i j r (-d) k*move p i j r (-d) l) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpμ k l hkl) hθ0)
            (mul_le_mul_of_nonneg_left (hpν k l hkl) (sub_nonneg.mpr hθ1))
        _ ≤ p k*p l := endpoint_pair p i j hkl hr.le hu hd

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_ExactRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.RationalWeightedStep.real_fractional _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding
open Finset MarginalRounding
variable {I : Type} [Fintype I] [DecidableEq I]

theorem exact_law (p : I → ℝ) (K : ℕ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i=K) :
    ∃ μ : FiniteLaw (Finset I),
      (∀ S, 0 < μ.weight S → S.card=K) ∧
      (∀ i, μ.prob (fun S => i ∈ S)=p i) ∧
      (∀ i j, i ≠ j → μ.expect (fun S => indicator S i*indicator S j) ≤ p i*p j) := by
  classical
  obtain ⟨Ω,instΩ,hex⟩ := exists_partial_law p (fun _ => 1) hp0 hp1 (by intro i; norm_num)
  let := instΩ
  obtain ⟨μ,Q,hs,hm,hp⟩ := hex
  have hsumq : ∀ ω, 0 < μ.weight ω → (∑ i, Q ω i)=K := by
    intro ω hω
    simpa only [one_mul,hsum] using (hs ω hω).2.2.2
  have hint : ∀ ω, 0 < μ.weight ω → ∀ i, Q ω i=0 ∨ Q ω i=1 := by
    intro ω hω i
    have hb := hs ω hω
    apply nonfractional_integral hb.1 hb.2.1
    intro hi
    obtain ⟨j,hj,hji⟩ := second_fractional hb.1 hb.2.1 (hsumq ω hω) hi
    have hh : 1 < (fractional (Q ω)).card := one_lt_card.mpr ⟨j,hj,i,hi,hji⟩
    omega
  let S := fun ω => univ.filter (fun i => Q ω i=1)
  have hbit : ∀ ω, 0 < μ.weight ω → ∀ i, indicator (S ω) i=Q ω i := by
    intro ω hω i
    rcases hint ω hω i with h | h <;> simp only [indicator,S,mem_filter,mem_univ,true_and,h] <;> norm_num
  have hcard : ∀ ω, 0 < μ.weight ω → (S ω).card=K := by
    intro ω hω
    have he : ((S ω).card:ℝ)=∑ i, Q ω i := by
      calc
        _ = ∑ i, indicator (S ω) i := by simp only [indicator,sum_boole,filter_univ_mem]
        _ = _ := sum_congr rfl (fun i _ => hbit ω hω i)
    exact_mod_cast he.trans (hsumq ω hω)
  refine ⟨μ.map S,?_,?_,?_⟩
  · intro A hA
    obtain ⟨ω,hω,rfl⟩ := μ.support_map S A hA
    exact hcard ω hω
  · intro i
    change (μ.map S).expect (fun A => indicator A i)=p i
    rw [FiniteLaw.expect_map]
    exact (μ.expect_congr_support (fun ω hω => hbit ω hω i)).trans (hm i)
  · intro i j hij
    rw [FiniteLaw.expect_map]
    have he : μ.expect (fun ω => indicator (S ω) i*indicator (S ω) j)=
        μ.expect (fun ω => Q ω i*Q ω j) := μ.expect_congr_support (fun ω hω => by rw [hbit ω hω,hbit ω hω])
    rw [he]
    exact hp i j hij

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_AssignmentCopies
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.CopyState.mem_localSet _root_.OAI.MetricKMedian.CopyState.mem_own _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type} [Fintype F] [DecidableEq F] {Δ : ℕ}

omit [Fintype F] [DecidableEq F] in
theorem embedSlots_injective (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : Function.Injective (embedSlots n hn) := by
  rintro ⟨a,h⟩ ⟨b,k⟩ he
  have hab : a=b := congrArg Prod.fst he
  subst b
  have hhk : h=k := Fin.ext (congrArg (fun x : Copy (F := F) Δ => x.2.val) he)
  subst k
  rfl

theorem activeSlots_mass (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) (g : ℝ) :
    mass g (activeSlots n hn)=∑ a, g*(n a:ℝ) := by
  rw [mass,activeSlots,card_image_of_injective _ (embedSlots_injective n hn),card_univ,Fintype.card_sigma]
  rw [Nat.cast_sum,mul_sum]
  simp only [Fintype.card_fin]

theorem assignment_copies (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) (r d : F → ℝ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hr0 : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a ≤ g*(n a:ℝ)) (hsum : ∑ a, r a=1) :
    ∃ S : Finset (Copy (F := F) Δ), S ⊆ activeSlots n hn ∧ mass g S=1 ∧
      PhysicalPotential.cost g (fun a => d a.1) S ≤ ∑ a, r a*d a := by
  classical
  let p : (Σ a, Fin (n a)) → ℝ := fun a => r a.1/(g*(n a.1:ℝ))
  have hzero : ∀ a, n a=0 → r a=0 := by
    intro a ha
    apply le_antisymm _ (hr0 a)
    simpa only [ha,Nat.cast_zero,mul_zero] using hr1 a
  have hp0 : ∀ a, 0 ≤ p a := fun a => div_nonneg (hr0 a.1) (mul_nonneg hg.le (Nat.cast_nonneg _))
  have hp1 : ∀ a, p a ≤ 1 := by
    intro a
    have hn0 : 0 < (n a.1:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt a.2.isLt)
    exact (div_le_one (mul_pos hg hn0)).mpr (hr1 a.1)
  have hcancel : ∀ a, (n a:ℝ)*(r a/(g*(n a:ℝ)))=r a/g := by
    intro a
    by_cases ha : n a=0
    · simp only [ha,hzero a ha,Nat.cast_zero,mul_zero,zero_div]
    · have hnz : (n a:ℝ) ≠ 0 := by exact_mod_cast ha
      field_simp
  have hps : ∑ a, p a=(Δ:ℝ) := by
    rw [Fintype.sum_sigma]
    simp only [p,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hcancel]
    rw [← sum_div,hsum]
    exact (div_eq_iff hg.ne').mpr (by nlinarith only [hunit])
  obtain ⟨μ,hcard,hm,_⟩ := WeightedRounding.exact_law p Δ hp0 hp1 hps
  let cost := fun S : Finset (Σ a, Fin (n a)) => g*∑ a ∈ S, d a.1
  have hcost : μ.expect cost=∑ a, r a*d a := by
    have he : ∀ S, cost S=∑ a, (if a ∈ S then (1:ℝ) else 0)*(g*d a.1) := by
      intro S
      simp only [cost,ite_mul,one_mul,zero_mul,sum_ite_mem,univ_inter,mul_sum]
    change μ.expect (fun S => cost S)=_
    simp_rw [he]
    rw [FiniteLaw.expect_sum]
    have hm' : ∀ a, μ.expect (fun S => if a ∈ S then (1:ℝ) else 0)=p a := hm
    simp only [FiniteLaw.expect_mul_right,hm']
    rw [Fintype.sum_sigma]
    simp only [p,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    apply sum_congr rfl
    intro a _
    calc
      _ = ((n a:ℝ)*(r a/(g*(n a:ℝ))))*g*d a := by ring
      _ = _ := by rw [hcancel]; field_simp
  obtain ⟨S,hS,hC⟩ := μ.exists_support_le_expect cost
  refine ⟨S.image (embedSlots n hn),Finset.image_subset_image (subset_univ S),?_,?_⟩
  · rw [mass,card_image_of_injective _ (embedSlots_injective n hn),hcard S hS]
    exact hunit
  · rw [PhysicalPotential.cost,sum_image (fun a _ b _ he => embedSlots_injective n hn he)]
    change (∑ a ∈ S, g*d a.1) ≤ ∑ a, r a*d a
    rw [← mul_sum]
    exact hC.trans_eq hcost

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalGridRound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}

attribute [local instance] OAI.MetricKMedian.FixedBatch.RationalParameters.rationalGridRoundCopyOrder
theorem nearest_spec (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) :
    q.nearest d A c ⊆ A ∧ (q.nearest d A c).card=q.Δ :=
  ⟨(takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).1,
    (takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).2.1⟩

theorem radius_spec (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) :
    (∀ i∈q.nearest d A c, d c i.1 ≤ q.radius d A hA c) ∧
      ∃ i∈q.nearest d A c, q.radius d A hA c=d c i.1 := by
  constructor
  · intro i hi
    exact le_max' ((q.nearest d A c).image (fun a : Copy (F := F) q.Δ => d c a.1))
      (d c i.1) (mem_image.mpr ⟨i,hi,rfl⟩)
  · obtain ⟨i,hi,he⟩ := mem_image.mp (max'_mem
      ((q.nearest d A c).image (fun a : Copy (F := F) q.Δ => d c a.1))
        ((q.nearest_nonempty d A hA c).image _))
    exact ⟨i,hi,he.symm⟩

variable [Fintype F]

theorem roundCounts_spec_s53_oai (hτ : τ<1) (hj : 0<j)
    (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (n : F → ℕ) (hn : ∀ a, n a ≤ q.Δ) (hm : 1 ≤ ∑ a, (q.g:ℝ)*(n a:ℝ))
    (r : Fin j → F → ℝ) (hr0 : ∀ c a, 0 ≤ r c a)
    (hr1 : ∀ c a, r c a ≤ (q.g:ℝ)*(n a:ℝ)) (hrsum : ∀ c, ∑ a, r c a=1) :
    ∃ O : Finset F, q.roundCounts d₀ d n=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (∑ a, (q.g:ℝ)*(n a:ℝ))+(q.allowance:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,∑ a, r c a*(d c a:ℝ)) := by
  let A := activeSlots n hn
  have hAm : 1 ≤ mass (q.g:ℝ) A := by rw [activeSlots_mass]; exact hm
  have hA : q.Δ ≤ A.card := by
    rw [← q.unit] at hAm
    exact_mod_cast (mul_le_mul_iff_right₀ q.gpos).mp hAm
  let B := q.nearest d A
  have hB : ∀ c, (B c).Nonempty := q.nearest_nonempty d A hA
  have hBc : ∀ c, (B c).card=q.Δ := fun c => (q.nearest_spec d A hA c).2
  have hBA : ∀ c, B c ⊆ A := fun c => (q.nearest_spec d A hA c).1
  have hBm : ∀ c, mass (q.g:ℝ) (B c)=1 := by intro c; rw [mass,hBc,q.unit]
  let R := q.radius d A hA
  have hdR : ∀ c i, i∈B c → d c i.1 ≤ R c := fun c => (q.radius_spec d A hA c).1
  have hatt : ∀ c, ∃ i∈B c, R c=d c i.1 := fun c => (q.radius_spec d A hA c).2
  have hR : ∀ c, 0 ≤ R c := by
    intro c
    obtain ⟨i,hi,he⟩ := hatt c
    rw [he]
    exact_mod_cast (hd c i.1 ▸ dist_nonneg)
  have hcost : ∀ c, PhysicalPotential.cost (q.g:ℝ)
      (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c) ≤
        ∑ a, r c a*(d c a:ℝ) := by
    intro c
    obtain ⟨S,hS,hmS,hcS⟩ := assignment_copies n hn (r c) (fun a => (d c a:ℝ))
      q.gpos q.unit (hr0 c) (hr1 c) (hrsum c)
    have hSc : S.card=q.Δ := by
      have he : (q.g:ℝ)*(S.card:ℝ)=(q.g:ℝ)*(q.Δ:ℝ) := hmS.trans q.unit.symm
      exact_mod_cast (mul_left_cancel₀ q.gpos.ne' he)
    have hl := (takeNearest_spec (fun a => d c a.1) q.Δ A hA).2.2 S hS hSc
    have hlR : (∑ a∈B c,(d c a.1:ℝ)) ≤ ∑ a∈S,(d c a.1:ℝ) := by exact_mod_cast hl
    calc
      _ = (q.g:ℝ)*∑ a∈B c,(d c a.1:ℝ) := by simp only [PhysicalPotential.cost,hd,mul_sum]
      _ ≤ (q.g:ℝ)*∑ a∈S,(d c a.1:ℝ) := mul_le_mul_of_nonneg_left hlR q.gpos.le
      _ ≤ _ := by simpa only [← mul_sum,PhysicalPotential.cost] using hcS
  obtain ⟨O,hO,hnO,hcard,hscore⟩ := q.selectCompleted_spec_s53 hτ hj d₀ d location client hd₀ hd
    A B R hB hAm hBA hR hBm hdR hatt
  refine ⟨O,?_,hnO,?_,hscore.trans ?_⟩
  · unfold roundCounts
    rw [dite_eq_left hn]
    change (if hA : q.Δ ≤ A.card then _ else none)=_
    rw [dite_eq_left hA]
    exact hO
  · simpa only [A,activeSlots_mass] using hcard
  · apply mul_le_mul_of_nonneg_left (sum_le_sum (fun c _ => hcost c))
    apply div_nonneg _ (sub_pos.mpr hτ).le
    have hτ0 : 0 ≤ τ := by
      have hh := q.failure
      have hnum : 0 ≤ (q.T:ℝ)*(96*(q.Δ:ℝ)^2*(q.β:ℝ)/
          ((2*(q.h:ℝ)*(q.g:ℝ))*(q.φ:ℝ)^2*(q.g:ℝ))) := by
        have hg := q.gpos; have hh := q.hpos; have hβ := q.βpos
        positivity
      exact hnum.trans hh
    positivity

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53_oai := @OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53_oai
