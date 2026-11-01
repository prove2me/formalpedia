-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:37:44.071572+00:00
-- url     : https://prove2.me/submissions/7cceef10-1532-404a-81c8-81017fdc1c7c

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K049
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_marginal_error_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteLaws
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem prob_congr (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω ↔ F ω) : μ.prob E = μ.prob F := by
  exact le_antisymm (μ.prob_mono fun ω => (hEF ω).mp) (μ.prob_mono fun ω => (hEF ω).mpr)

end FiniteLaw

namespace BatchRemainder

theorem pointwise {E : Type*} [DecidableEq E] (A : Finset E)
    (b : E → ℝ) {D K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ e ∈ A, -K ≤ b e) (hD : D ≤ K)
    (hzero : A = ∅ → D ≤ 0) (hone : ∀ e, A = {e} → D ≤ b e) :
    D ≤ (∑ e ∈ A, b e) + 2 * K * (A.offDiag.card : ℝ) := by
  rcases lt_or_ge A.card 2 with hsmall | hlarge
  · have hc : A.card ≤ 1 := by omega
    by_cases h : A = ∅
    · simpa only [h, Finset.sum_empty, Finset.offDiag_empty, Finset.card_empty,
        Nat.cast_zero, mul_zero, add_zero] using hzero h
    · have hpos : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
      obtain ⟨e, ha⟩ := Finset.card_eq_one.mp (show A.card = 1 by omega)
      simpa only [ha, Finset.sum_singleton, Finset.offDiag_singleton,
        Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] using hone e ha
  · have hsum := Finset.sum_le_sum hb
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hn : (2:ℝ) ≤ A.card := by exact_mod_cast hlarge
    have hcard : (A.offDiag.card : ℝ) = (A.card : ℝ) * ((A.card : ℝ) - 1) := by
      rw [Finset.offDiag_card]
      have hrewrite : A.card * A.card - A.card = A.card * (A.card - 1) := by
        simp only [Nat.mul_sub_left_distrib, mul_one]
      rw [hrewrite, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcard]
    have hquad : (A.card : ℝ) + 1 ≤ 2 * (A.card : ℝ) * ((A.card : ℝ) - 1) := by
      nlinarith only [hn, sq_nonneg ((A.card : ℝ) - 2)]
    have hmul := mul_le_mul_of_nonneg_left hquad hK
    nlinarith only [hsum, hD, hmul]

theorem expect_selected_sum {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ) :
    μ.expect (fun ω => ∑ e ∈ A ω, b e) =
      ∑ e, μ.prob (fun ω => e ∈ A ω) * b e := by
  have hsum : ∀ ω, (∑ e ∈ A ω, b e) = ∑ e, (if e ∈ A ω then (1:ℝ) else 0) * b e := by
    intro ω
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
    simp only [Finset.filter_univ_mem]
  simp_rw [hsum, FiniteLaw.expect_sum, FiniteLaw.expect_mul_right]
  rfl

theorem expect_pair_count {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) :
    μ.expect (fun ω => (Finset.card (A ω).offDiag : ℝ)) =
      ∑ p ∈ (Finset.univ : Finset E).offDiag,
        μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
  have hset : ∀ ω, (A ω).offDiag =
      (Finset.univ : Finset E).offDiag.filter (fun p => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
    intro ω
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hsum : ∀ ω, (Finset.card (A ω).offDiag : ℝ) =
      ∑ p ∈ (Finset.univ : Finset E).offDiag, if p.1 ∈ A ω ∧ p.2 ∈ A ω then (1:ℝ) else 0 := by
    intro ω
    rw [hset, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  simp_rw [hsum, FiniteLaw.expect_sum]
  rfl

theorem expectation_le {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ) (D : Ω → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ e, -K ≤ b e) (hD : ∀ ω, D ω ≤ K)
    (hzero : ∀ ω, A ω = ∅ → D ω ≤ 0)
    (hone : ∀ ω e, A ω = {e} → D ω ≤ b e) :
    μ.expect D ≤ (∑ e, μ.prob (fun ω => e ∈ A ω) * b e) +
      2 * K * ∑ p ∈ (Finset.univ : Finset E).offDiag,
        μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
  have h := μ.expect_mono (fun ω => pointwise (A ω) b hK (fun e _ => hb e)
    (hD ω) (hzero ω) (hone ω))
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_mul,
    expect_selected_sum, expect_pair_count] at h
  exact h

end BatchRemainder
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRealTransfer
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseBernoulli.cast_flag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem product_indicator (q : Fin n → Bool) (S : Finset (Fin n)) :
    (∏ i∈S, flag q i)=(if ∀ i∈S, q i=true then (1:ℚ) else 0) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi,ih]
    simp only [mem_insert,forall_eq_or_imp]
    cases hq : q i <;> simp [flag,hq]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.BatchRemainder
open Finset

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]

theorem generator_estimate (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ)
    (D : Ω → ℝ) {K lam δ J : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hb : ∀ e, |b e| ≤ K) (hD : ∀ ω, D ω ≤ K)
    (hzero : ∀ ω, A ω=∅ → D ω ≤ 0)
    (hone : ∀ ω e, A ω={e} → D ω ≤ b e)
    (hfirst : ∀ e, |μ.prob (fun ω => e ∈ A ω)-lam| ≤ δ)
    (hpair : ∀ e f, e ≠ f → μ.prob (fun ω => e ∈ A ω ∧ f ∈ A ω) ≤ J) :
    μ.expect D ≤ lam*(∑ e, b e)+(Fintype.card E:ℝ)*K*δ+
      2*K*((univ : Finset E).offDiag.card:ℝ)*J := by
  have hfirstsum : (∑ e, μ.prob (fun ω => e ∈ A ω)*b e) ≤
      lam*(∑ e, b e)+(Fintype.card E:ℝ)*K*δ := by
    have hpoint : ∀ e, μ.prob (fun ω => e ∈ A ω)*b e ≤ lam*b e+K*δ := by
      intro e
      have habs : |(μ.prob (fun ω => e ∈ A ω)-lam)*b e| ≤ δ*K := by
        rw [abs_mul]
        exact mul_le_mul (hfirst e) (hb e) (abs_nonneg _) hδ
      have hle := (le_abs_self ((μ.prob (fun ω => e ∈ A ω)-lam)*b e)).trans habs
      nlinarith only [hle]
    have hsum := sum_le_sum (fun e (_ : e ∈ (univ : Finset E)) => hpoint e)
    simpa only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      using hsum
  have hpairSum : (∑ p ∈ (univ : Finset E).offDiag,
      μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω)) ≤ ((univ : Finset E).offDiag.card:ℝ)*J := by
    calc
      _ ≤ ∑ _p ∈ (univ : Finset E).offDiag, J :=
        sum_le_sum (fun p hp => hpair p.1 p.2 (mem_offDiag.mp hp).2.2)
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hbase := expectation_le μ A b D hK (fun e => (abs_le.mp (hb e)).1) hD hzero hone
  have hj := mul_le_mul_of_nonneg_left hpairSum (by positivity : 0 ≤ 2*K)
  nlinarith only [hbase, hfirstsum, hj]

end MetricKMedian.BatchRemainder

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseFiltered
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseBernoulli.cast_flag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem cylinder (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    (run (d := d) p hp n).real.prob (fun q => ∀ i∈S, q i=true)=((∏ i∈S,p i:ℚ):ℝ) := by
  calc
    _ = (run (d := d) p hp n).real.expect (fun q => ((∏ i∈S,flag q i:ℚ):ℝ)) := by
      unfold FiniteLaw.prob
      congr 1
      funext q
      rw [product_indicator]
      split_ifs <;> norm_num
    _ = _ := by rw [SparseIntegerLaw.real_expect,subset_moment p hp S hS]

theorem real_pair (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hd : 2 ≤ d) (e f : Fin n) (hef : e≠f) :
    (run (d := d) p hp n).real.prob (fun q => q e=true ∧ q f=true)=(p e:ℝ)*(p f:ℝ) := by
  have he := cylinder (d := d) p hp {e,f} (by simpa [hef] using hd)
  simpa only [mem_insert,mem_singleton,forall_eq_or_imp,forall_eq,prod_pair hef,Rat.cast_mul] using he

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRealExpectation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_def (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.expectation f=∑ i : Fin μ.length, (μ.law.rational.weight i:ℝ)*f μ.states[i.val] := rfl

theorem expectation_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℝ) :
    (μ.bindIndexed κ).expectation f=
      ∑ a, (μ.law.rational.weight a:ℝ)*(κ a).expectation f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  calc
    _ = ∑ z, (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val] := by
      unfold expectation realIndex
      change (∑ i, (((ρ.integer.reindex finSigmaFinEquiv).rational.weight i):ℝ)*
        f ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
          (κ z.1).states[z.2.val]))[i.val])) = _
      simp only [Vector.getElem_ofFn]
      change (∑ i, (ρ.integer.rational.weight (finSigmaFinEquiv.symm i):ℝ)*
        f (κ (finSigmaFinEquiv.symm i).1).states[(finSigmaFinEquiv.symm i).2.val]) = _
      simp only [RationalLaw.integer_weight]
      exact (finSigmaFinEquiv (n := fun a => (κ a).length)).symm.sum_comp
        (fun z : Sigma (fun a : Fin μ.length => Fin (κ a).length) =>
          (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val])
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [ρ,RationalLaw.sigma,Rat.cast_mul,mul_assoc,← mul_sum,expectation_def]

theorem expectation_map (μ : SparseIntegerLaw α) (g : α → β) (f : β → ℝ) :
    (μ.map g).expectation f=μ.expectation (fun a => f (g a)) := by
  simp only [expectation_def,map,Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMixture
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_mix (μ ν : SparseIntegerLaw α) (f : α → ℝ) :
    (mix μ ν).expectation f=(1/2)*μ.expectation f+(1/2)*ν.expectation f := by
  rw [mix,expectation_bindIndexed]
  change (∑ a : Fin 2, ((1/2:ℚ):ℝ)*(if a.val=0 then μ else ν).expectation f)=_
  norm_num [Fin.sum_univ_two]

theorem real_expect_all [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.real.expect f=μ.expectation f := by
  rw [real,FiniteLaw.expect_map]
  rfl

theorem prob_mix [Fintype α] [DecidableEq α] (μ ν : SparseIntegerLaw α)
    (P : α → Prop) [DecidablePred P] :
    (mix μ ν).real.prob P=(1/2)*μ.real.prob P+(1/2)*ν.real.prob P := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_mix]

theorem prob_map [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : SparseIntegerLaw α) (f : α → β) (P : β → Prop) [DecidablePred P] :
    (μ.map f).real.prob P=μ.real.prob (fun a => P (f a)) := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePhysicalBatch
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

theorem balanced_eq (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) :
    balanced Z C ω=PhysicalBatchLaw.balanced Z C ω := by
  ext e
  simp only [balanced,PhysicalBatchLaw.balanced,FiniteLaw.selected,mem_inter,mem_filter]

theorem unbalanced_eq (Z : Finset (Fin n)) (ω : Fin n → Bool) :
    unbalanced Z ω=PhysicalBatchLaw.unbalanced Z ω := rfl

theorem prob_eq (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (R : Finset (Fin n) → Prop) [DecidablePred R] :
    (law Z C p q hp hq).real.prob R=
      (1/2)*(SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
      (1/2)*(SparseBernoulli.run (d := 4) q hq n).real.prob
        (fun ω => R (PhysicalBatchLaw.unbalanced Z ω)) := by
  rw [law,SparseIntegerLaw.prob_mix,SparseIntegerLaw.prob_map,SparseIntegerLaw.prob_map]
  apply congrArg₂ (fun x y : ℝ => (1/2)*x+(1/2)*y)
  · apply FiniteLaw.prob_congr
    intro ω
    rw [balanced_eq]
  · apply FiniteLaw.prob_congr
    intro ω
    rw [unbalanced_eq]

theorem pair_le (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (e f : Fin n) (hef : e≠f) :
    (law Z C p q hp hq).real.prob (fun A => e∈A ∧ f∈A) ≤
      ((p:ℝ)^2+(q e:ℝ)*(q f:ℝ))/2 := by
  rw [prob_eq]
  have hb : (SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
      (fun ω => e∈PhysicalBatchLaw.balanced Z C ω ∧ f∈PhysicalBatchLaw.balanced Z C ω) ≤ (p:ℝ)^2 := by
    calc
      _ ≤ (SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
          (fun ω => ω e=true ∧ ω f=true) := by
        apply FiniteLaw.prob_mono
        intro ω h
        simp only [PhysicalBatchLaw.balanced,FiniteLaw.selected,mem_inter,mem_filter,mem_univ,true_and] at h
        exact ⟨h.1.1.1,h.2.1.1⟩
      _ = _ := by rw [SparseBernoulli.real_pair _ _ (by norm_num : 2 ≤ 4) e f hef,pow_two]
  have hu : (SparseBernoulli.run (d := 4) q hq n).real.prob
      (fun ω => e∈PhysicalBatchLaw.unbalanced Z ω ∧ f∈PhysicalBatchLaw.unbalanced Z ω) ≤
        (q e:ℝ)*(q f:ℝ) := by
    rw [← SparseBernoulli.real_pair q hq (by norm_num : 2 ≤ 4) e f hef]
    apply FiniteLaw.prob_mono
    intro ω h
    exact ⟨(mem_filter.mp h.1).2.1,(mem_filter.mp h.2).2.1⟩
  linarith only [hb,hu]

end MetricKMedian.SparsePhysicalBatch

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseEnumeratedBatch
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem pair_le (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (e f : E) (hef : e≠f) :
    (law enum Z C p q hp hq).real.prob (fun A => e∈A ∧ f∈A) ≤
      ((p:ℝ)^2+(q e:ℝ)*(q f:ℝ))/2 := by
  rw [law,SparseIntegerLaw.prob_map]
  have hh := SparsePhysicalBatch.pair_le (Z.map enum.symm.toEmbedding)
    (fun a => (C (enum a)).map enum.symm.toEmbedding) p (fun a => q (enum a)) hp
    (fun a => hq (enum a)) (enum.symm e) (enum.symm f) (fun h => hef (enum.symm.injective h))
  simpa only [mem_map_equiv,Equiv.apply_symm_apply] using hh

end MetricKMedian.SparseEnumeratedBatch

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseEnumeratedEstimate
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem relevant_generator_estimate_s53_oai (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (b : E → ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ K Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    (D : Finset E → ℝ)
    (hb : ∀ e ∈ R, |b e| ≤ K) (hD : ∀ A, D A ≤ K)
    (hzero : ∀ A, A ∩ R=∅ → D A ≤ 0)
    (hone : ∀ A e, A ∩ R={e} → D A ≤ b e) :
    (law enum Z C p q hp hq0).real.expect D ≤
      ((p:ℝ)/2)*(∑ e ∈ R, b e)+(R.card:ℝ)*K*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
        2*K*((univ : Finset R).offDiag.card:ℝ)*Q^2 := by
  let A' : Finset E → Finset R := fun A => univ.filter (fun e : R => e.val ∈ A)
  have hzero' : ∀ A, A' A=∅ → A ∩ R=∅ := by
    intro A ha
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have he' : (⟨e, (mem_inter.mp he).2⟩ : R) ∈ A' A := by
      simp only [A', mem_filter, mem_univ, true_and]
      exact (mem_inter.mp he).1
    rw [ha] at he'
    exact notMem_empty _ he'
  have hone' : ∀ A (e : R), A' A={e} → A ∩ R={e.val} := by
    intro A e ha
    ext f
    constructor
    · intro hf
      have hf' : (⟨f, (mem_inter.mp hf).2⟩ : R) ∈ A' A := by
        simp only [A', mem_filter, mem_univ, true_and]
        exact (mem_inter.mp hf).1
      rw [ha, mem_singleton] at hf'
      simpa only [mem_singleton] using congrArg Subtype.val hf'
    · intro hf
      have hfval : f=e.val := mem_singleton.mp hf
      subst f
      have he : e ∈ A' A := by rw [ha]; exact mem_singleton_self _
      exact mem_inter.mpr ⟨(mem_filter.mp he).2, e.property⟩
  have hfirst : ∀ e : R,
      |(law enum Z C p q hp hq0).real.prob (fun A => e ∈ A' A)-(p:ℝ)/2| ≤
        (N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2 := by
    intro e
    simpa only [A', mem_filter, mem_univ, true_and] using
      marginal_error_s53 enum Z C p q hp hq0 hφ hq hC hself e.val
  have hpair : ∀ e f : R, e ≠ f →
      (law enum Z C p q hp hq0).real.prob (fun A => e ∈ A' A ∧ f ∈ A' A) ≤ Q^2 := by
    intro e f hef
    have h2 := pair_le enum Z C p q hp hq0 e.val f.val
      (show e.val ≠ f.val from fun h => hef (Subtype.ext h))
    have hpp : (p:ℝ)^2 ≤ Q^2 := (sq_le_sq₀ (by exact_mod_cast hp.1) hQ).mpr hpQ
    have hqq := mul_le_mul (hqQ e.val) (hqQ f.val) (show (0:ℝ) ≤ q f.val by exact_mod_cast (hq0 f.val).1) hQ
    simp only [A', mem_filter, mem_univ, true_and]
    nlinarith only [h2, hpp, hqq]
  have h := BatchRemainder.generator_estimate (law enum Z C p q hp hq0).real A'
    (fun e : R => b e.val) D hK (by
      have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp.1
      positivity)
    (fun e => hb e.val e.property) hD (fun A ha => hzero A (hzero' A ha))
    (fun A e ha => hone A e.val (hone' A e ha)) hfirst hpair
  simpa only [Fintype.card_coe, sum_coe_sort] using h

end MetricKMedian.SparseEnumeratedBatch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate_s53_oai := @OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate_s53_oai
