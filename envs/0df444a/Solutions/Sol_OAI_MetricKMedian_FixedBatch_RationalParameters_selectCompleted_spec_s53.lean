-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:24:20.32399+00:00
-- url     : https://prove2.me/submissions/1236c4dc-5ce9-4b34-9dc1-9e385ce53daf

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K040
import Definitions.Def_OAIQ053K043
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_completed_expectation_s53
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_completion_s53
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_mass_s53
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_step_count_tail_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem prob_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : 0 ≤ μ.prob E := by
  apply μ.expect_nonneg
  intro ω
  split_ifs <;> norm_num

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRealExpectation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight
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

theorem expectation_const (μ : SparseIntegerLaw α) (c : ℝ) :
    μ.expectation (fun _ => c)=c := μ.realIndex.expect_const c

theorem expectation_add (μ : SparseIntegerLaw α) (f g : α → ℝ) :
    μ.expectation (fun a => f a+g a)=μ.expectation f+μ.expectation g :=
  μ.realIndex.expect_add _ _

theorem expectation_mono (μ : SparseIntegerLaw α) (f g : α → ℝ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val] ≤ g μ.states[i.val]) :
    μ.expectation f ≤ μ.expectation g := by
  simp only [expectation_def]
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h i) (by exact_mod_cast μ.law.rational.nonneg i)

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

theorem expectation_dirac (a : α) (f : α → ℝ) :
    (dirac a).expectation f=f a := by
  simp only [expectation_def,dirac,IntegerLaw.rational]
  norm_num

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem expectation_step (κ : ℕ → α → SparseIntegerLaw α) (a : α) (t : ℕ)
    (V : History α → ℝ) :
    (tree κ a (t+1)).expectation V=
      (tree κ a t).expectation (fun h => (κ t h.1).expectation (fun s => V (extend h s))) := by
  rw [tree,SparseIntegerLaw.expectation_bindIndexed]
  simp_rw [branch,SparseIntegerLaw.expectation_map]
  rfl

end MetricKMedian.SparseHistories
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalCompletedCost
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Completion.Rational
open Finset PhysicalPotential CopyState Analytic Preparation
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

omit [LinearOrder F] [Fintype F] in
theorem score_nonneg (d : Fin j → F → ℚ) (hd : ∀ c f, 0 ≤ d c f) (O : Finset F) :
    0 ≤ score d O := by
  apply sum_nonneg
  intro c _
  split_ifs with h
  · obtain ⟨f,_,he⟩ := mem_image.mp (min'_mem (O.image (d c)) (h.image _))
    rw [← he]
    exact hd c f
  · exact le_rfl

end MetricKMedian.Completion.Rational
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

theorem taperAt_le (t : ℕ) : (q.taperAt t:ℝ) ≤ 1/2 := by
  unfold taperAt
  split_ifs with ht
  · exact q.taper_le _
  · norm_num

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBoundedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem count_tail_up_to (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (size : α → ℝ) (c ρ : ℝ)
    (T : ℕ)
    (hstep : ∀ t < T, ∀ i : ℕ, ∀ hi : i < (tree κ a t).length,
      (κ t (tree κ a t).states[i].1).expectation
        (fun s => if size (tree κ a t).states[i].1+c < size s then 1 else 0) ≤ ρ)
    :
    (tree κ a T).expectation (fun h => if size a+(T:ℝ)*c < size h.1 then 1 else 0) ≤
      (T:ℝ)*ρ := by
  classical
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,Nat.cast_zero,zero_mul,add_zero,
      lt_self_iff_false,ite_false,le_refl]
  | succ t ih =>
    have hi := ih (fun r hr => hstep r (hr.trans (Nat.lt_succ_self t)))
    rw [expectation_step]
    have hs : ∀ i : Fin (tree κ a t).length,
        (κ t (tree κ a t).states[i.val].1).expectation
          (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0) ≤
        (if size a+(t:ℝ)*c < size (tree κ a t).states[i.val].1 then 1 else 0)+ρ := by
      intro i
      let z := (tree κ a t).states[i.val].1
      have hp : ∀ s, (if size a+((t+1:ℕ):ℝ)*c < size s then (1:ℝ) else 0) ≤
          (if size a+(t:ℝ)*c < size z then 1 else 0)+
            (if size z+c < size s then 1 else 0) := by
        intro s
        split_ifs <;> push_cast at * <;> linarith
      have he := SparseIntegerLaw.expectation_mono (κ t z)
        (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0)
        (fun s => (if size a+(t:ℝ)*c < size z then 1 else 0)+
          (if size z+c < size s then 1 else 0)) (fun b => hp _)
      rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at he
      exact he.trans (add_le_add le_rfl (hstep t (Nat.lt_succ_self t) i.val i.isLt))
    have he := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation
        (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0))
      (fun z => (if size a+(t:ℝ)*c < size z.1 then 1 else 0)+ρ) hs
    rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at he
    exact he.trans (by push_cast; nlinarith only [hi])

end MetricKMedian.SparseHistories
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalHistoryCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] in

theorem histories_count_tail (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (histories d g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => if mass (g:ℝ) A+(T:ℝ)*(4/((g:ℝ)*(β:ℝ))) < mass (g:ℝ) z.1.1 then 1 else 0) ≤
      (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))) := by
  let κ := fun t => step (Δ := Δ) d g β p φ (P t) hp0 hφ0 hupper
  apply SparseHistories.count_tail_up_to κ (A,none)
    (fun s => mass (g:ℝ) s.1) (4/((g:ℝ)*(β:ℝ)))
    (96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))) T
  intro t ht i hi
  have hm := histories_mass_s53 d g β p φ P hp0 hφ0 hupper A t hg.le hunit hA ⟨i,hi⟩
  exact step_count_tail_s53 d location hd g β p φ (P t) hp0 hφ0 hupper
    (SparseHistories.tree κ (A,none) t).states[i].1
    hg hg1 hp hφ hφ1 hβ hunit (hP t ht) (hP1 t ht) hm hsmall

end MetricKMedian.RationalPhysicalKernel
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

 theorem condition_support (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (ω : Ω) :
    0 < (condition μ P hP).weight ω ↔ P ω ∧ 0 < μ.weight ω := by
  change 0 < (if P ω then μ.weight ω/μ.prob P else 0) ↔ P ω ∧ 0 < μ.weight ω
  split_ifs with hp
  · simp only [hp, true_and]
    exact div_pos_iff_of_pos_right hP
  · simp [hp]

 theorem condition_expect_le (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    (condition μ P hP).expect f ≤ μ.expect f/μ.prob P := by
  have he : (condition μ P hP).expect f=
      μ.expect (fun ω => if P ω then f ω else 0)/μ.prob P := by
    unfold expect condition
    simp only [sum_div]
    apply sum_congr rfl
    intro ω _
    split_ifs <;> simp [div_mul_eq_mul_div]
  rw [he]
  apply div_le_div_of_nonneg_right _ hP.le
  apply μ.expect_mono
  intro ω
  split_ifs
  · exact le_rfl
  · exact hf ω

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

theorem select_success (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    ∃ ω, 0 < μ.weight ω ∧ P ω ∧ f ω ≤ μ.expect f/μ.prob P := by
  obtain ⟨ω,hω,hfω⟩ := (condition μ P hP).exists_support_le_expect f
  obtain ⟨hp,hw⟩ := (condition_support μ P hP ω).mp hω
  exact ⟨ω,hw,hp,hfω.trans (condition_expect_le μ P hP f hf)⟩

 theorem select_success_bound (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (f : Ω → ℝ) {p C : ℝ} (hp : 0 < p) (hP : p ≤ μ.prob P)
    (hf : ∀ ω, 0 ≤ f ω) (hE : μ.expect f ≤ C) :
    ∃ ω, 0 < μ.weight ω ∧ P ω ∧ f ω ≤ C/p := by
  obtain ⟨ω,hw,hgood,hcost⟩ := select_success μ P (hp.trans_le hP) f hf
  refine ⟨ω,hw,hgood,hcost.trans ?_⟩
  exact (div_le_div_of_nonneg_right hE (prob_nonneg μ P)).trans
    (div_le_div_of_nonneg_left ((μ.expect_nonneg hf).trans hE) hp hP)

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSelect
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSelect
variable {α : Type}

theorem best_spec (P : α → Bool) (cost : α → ℚ) (L : List α) :
    (best P cost L=none ↔ ∀ a∈L,P a=false) ∧
    ∀ a, best P cost L=some a → a∈L ∧ P a=true ∧ ∀ b∈L,P b=true → cost a ≤ cost b := by
  induction L with
  | nil => simp [best]
  | cons a L ih =>
    by_cases ha : P a=true
    · cases hb : best P cost L with
      | none =>
        have hL := ih.1.mp hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro b h
          have he : a=b := Option.some.inj h
          subst b
          refine ⟨List.mem_cons_self,ha,?_⟩
          intro b hmem hP
          rcases List.mem_cons.mp hmem with he | he
          · subst b; exact le_rfl
          · have hf := hL b he
            rw [hP] at hf
            contradiction
      | some b =>
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro z hz
          by_cases hab : cost a ≤ cost b
          · simp only [ite_eq_left hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_self,ha,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_rfl
            · exact hab.trans (hmin z he hP)
          · simp only [ite_eq_right hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_of_lt (lt_of_not_ge hab)
            · exact hmin z he hP
    · have haf : P a=false := Bool.eq_false_iff.mpr ha
      simp only [best,haf,Bool.false_eq_true,ite_false]
      constructor
      · rw [ih.1]
        constructor
        · intro h b hb
          rcases List.mem_cons.mp hb with he | he
          · subst b; exact haf
          · exact h b he
        · intro h b hb
          exact h b (List.mem_cons_of_mem a hb)
      · intro b hb
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
        intro z hz hP
        rcases List.mem_cons.mp hz with he | he
        · subst z
          rw [haf] at hP
          contradiction
        · exact hmin z he hP

theorem choose_spec (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ)
    (a : α) (ha : choose μ P cost=some a) :
    P a=true ∧ ∀ i : Fin μ.length, P μ.states[i.val]=true → cost a ≤ cost μ.states[i.val] := by
  have hs := (best_spec P cost μ.states.toList).2 a ha
  refine ⟨hs.2.1,fun i hi => hs.2.2 _ ?_ hi⟩
  exact Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt)

theorem choose_bound (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ)
    {p C : ℝ} (hp : 0 < p)
    (hP : p ≤ μ.realIndex.prob (fun i => P μ.states[i.val]=true))
    (hcost : ∀ a,0 ≤ cost a)
    (hE : μ.expectation (fun a => (cost a:ℝ)) ≤ C) :
    ∃ a, choose μ P cost=some a ∧ P a=true ∧ (cost a:ℝ) ≤ C/p := by
  obtain ⟨i,_hi,hgood,hbound⟩ := μ.realIndex.select_success_bound
    (fun i => P μ.states[i.val]=true) (fun i => (cost μ.states[i.val]:ℝ)) hp hP
    (fun i => by exact_mod_cast hcost _) hE
  cases hb : choose μ P cost with
  | none =>
    have hz := (best_spec P cost μ.states.toList).1.mp hb _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt))
    rw [hgood] at hz
    contradiction
  | some a =>
    obtain ⟨ha,hmin⟩ := choose_spec μ P cost a hb
    refine ⟨a,rfl,ha,?_⟩
    exact (show (cost a:ℝ) ≤ (cost μ.states[i.val]:ℝ) by exact_mod_cast hmin i hgood).trans hbound

end MetricKMedian.SparseSelect
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalHistorySelection
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

local instance rationalHistorySelectionCopyOrder_r73e450_1 : LinearOrder (Copy (F := F) q.Δ) := copyOrder
theorem selectCompleted_spec_s53_oai (hτ : τ<1) (hj : 0<j)
    (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
    (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    ∃ O : Finset F, q.selectCompleted d₀ d R A B hB=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ mass (q.g:ℝ) A+(q.allowance:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,
        PhysicalPotential.cost (q.g:ℝ)
          (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)) := by
  let μ := q.tree d₀ A
  let good := fun a : Fin μ.length => mass (q.g:ℝ) μ.states[a.val].1.1 ≤
    mass (q.g:ℝ) A+(q.allowance:ℝ)
  have hfail : μ.realIndex.prob (fun a => ¬ good a) ≤ τ := by
    have hc := histories_count_tail d₀ location hd₀ q.g q.β q.probabilityQ q.φ q.taperAt
      q.probabilityQ_pos.le (by exact_mod_cast q.φpos.le) q.probabilityQ_le A q.T
      q.gpos q.gle (by exact_mod_cast q.probabilityQ_pos) q.φpos q.φle q.βpos q.unit
      (fun t _ => q.taperAt_pos t) (fun t _ => q.taperAt_le t) hA (by
        simpa only [probabilityQ,Rat.cast_mul,Rat.cast_ofNat] using q.count)
    have he : (q.allowance:ℝ)=(q.T:ℝ)*(4/((q.g:ℝ)*(q.β:ℝ))) := by
      simp only [allowance,Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
    have hf : μ.realIndex.prob (fun a => ¬ good a) ≤
      (q.T:ℝ)*(96*(q.Δ:ℝ)^2*(q.β:ℝ)/((q.probabilityQ:ℝ)*(q.φ:ℝ)^2*(q.g:ℝ))) := by
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      unfold FiniteLaw.prob SparseIntegerLaw.expectation
      apply congrArg μ.realIndex.expect
      funext a
      simp only [good,he,not_le]
      rfl
    exact hf.trans (by simpa only [probabilityQ,Rat.cast_mul,Rat.cast_ofNat] using q.failure)
  have hprob : 1-τ ≤ μ.realIndex.prob (fun a => q.completedGood d R A B hB μ.states[a.val]=true) := by
    have hc := μ.realIndex.prob_compl good
    have hp : 1-τ ≤ μ.realIndex.prob good := by linarith only [hc,hfail]
    apply hp.trans (μ.realIndex.prob_mono ?_)
    intro a ha
    have hs := histories_completion_s53 d₀ d location client hd₀ hd q.g q.β q.probabilityQ q.φ
      q.taperAt q.probabilityQ_pos.le (by exact_mod_cast q.φpos.le) q.probabilityQ_le A B R hB
      q.T (fun t => Real.exp (-(t:ℝ)*(q.h:ℝ))) q.gpos q.unit
      (fun t _ => q.taperAt_pos t) (fun t _ => q.taperAt_le t) hA hBA hR hm hdR a
    simp only [completedGood,decide_eq_true_eq]
    refine ⟨hs.2.1 hj,?_⟩
    have hh := hs.1.trans ha
    dsimp only [mass] at hh
    exact_mod_cast hh
  obtain ⟨z,hz,hgood,hcost⟩ := SparseSelect.choose_bound μ (q.completedGood d R A B hB)
    (fun z => score d (completed d R B hB q.g q.β z)) (sub_pos.mpr hτ) hprob
    (fun z => score_nonneg d (fun c f => by exact_mod_cast (hd c f ▸ dist_nonneg)) _)
    (q.completed_expectation_s53 d₀ d location client hd₀ hd A B R hB hA hBA hR hm hdR hatt)
  have hgood' := of_decide_eq_true hgood
  refine ⟨completed d R B hB q.g q.β z,?_,hgood'.1,?_,?_⟩
  · change Option.map _ (SparseSelect.choose μ _ _)=_
    rw [hz]
    rfl
  · dsimp only [mass]
    exact_mod_cast hgood'.2
  · exact hcost.trans_eq (by ring)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53_oai := @OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53_oai
