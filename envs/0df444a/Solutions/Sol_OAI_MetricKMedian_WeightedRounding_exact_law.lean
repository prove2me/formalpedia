-- Prove2me | solution 1 for OAI.MetricKMedian.WeightedRounding.exact_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:40:50.606196+00:00
-- url     : https://prove2.me/submissions/6e2ad4c8-8f0c-4378-9522-f8d259aa2c5c

import Mathlib
import Definitions.Def_OAIQ035K012
import Definitions.Def_OAIQ035K029
import Definitions.Def_OAIQ035K035

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_SumLaws
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedRounding
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedPartial
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_ExactRounding
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

theorem exact_law_oai (p : I → ℝ) (K : ℕ) (hp0 : ∀ i, 0 ≤ p i)
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

theorem solution : type_of% @OAI.MetricKMedian.WeightedRounding.exact_law_oai := @OAI.MetricKMedian.WeightedRounding.exact_law_oai
