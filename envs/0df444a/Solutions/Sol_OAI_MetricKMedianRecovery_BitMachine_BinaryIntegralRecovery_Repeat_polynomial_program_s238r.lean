-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:09:39.642892+00:00
-- url     : https://prove2.me/submissions/5a7b3009-7dfa-4f8c-8778-3e392e827ec1

import Mathlib
import Definitions.Def_Q238L021
import Definitions.Def_Q238L040
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_result_guarantee_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_output_success_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Repeat_amplified_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Repeat_run_source_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma menuConstant_pos (kappa : ℝ) (hk : 0 < kappa) : 0 < menuConstant kappa hk := by
  have hM : (0 : ℝ) < firstSize kappa := by
    dsimp [firstSize]
    positivity
  unfold menuConstant
  refine lt_min (div_pos zero_lt_one (mul_pos (by norm_num) hM)) ?_
  exact lt_min (by positivity) (by norm_num)

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.NearClients
variable {V : Type*}

variable [PseudoMetricSpace V]

lemma progressConstant_pos (kappa : ℝ) (hk : 0 < kappa) : 0 < progressConstant kappa := by
  unfold progressConstant
  positivity

end MetricKMedianRecovery.NearClients

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingRate
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus

lemma samplingRate_pos : 0 < samplingRate := by
  exact mul_pos (mul_pos (pow_pos (NearClients.progressConstant_pos mainKappa mainKappa_pos) _)
    (menuConstant_pos mainKappa mainKappa_pos)) (Real.rpow_pos_of_pos (by norm_num) _)

lemma samplingBound_eq (m : ℕ) : samplingBound m = samplingRate^m := by
  have hh : (2:ℝ)^(-((10/(9*mainKappa)+1)*m)) =
      ((2:ℝ)^(-(10/(9*mainKappa)+1)))^m := by
    rw [← neg_mul,Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  simp only [samplingBound, samplingRate, hh, mul_pow, pow_mul]

lemma sampling_exponential : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
    Real.exp (-C*m) ≤ (1/2:ℝ)^(2*m) * samplingBound m := by
  let r := (1/2:ℝ)^2 * samplingRate
  have hr : 0 < r := mul_pos (by norm_num) samplingRate_pos
  refine ⟨1+|Real.log r|,by positivity,?_⟩
  intro m
  rw [samplingBound_eq, pow_mul, ← mul_pow]
  change Real.exp (-(1+|Real.log r|)*(m:ℝ)) ≤ r^m
  conv_rhs => rw [← Real.exp_log hr,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hl := neg_abs_le (Real.log r)
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n) (bits) :
    output δ D F S Δ s colors label q c r0 y0 bits⊆F ∧
      (output δ D F S Δ s colors label q c r0 y0 bits).card=S.card ∧
      (output δ D F S Δ s colors label q c r0 y0 bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · split
    · exact ⟨hSF,rfl,hS⟩
    · rename_i v xs hb
      let P:=BlueDP.makePlan _ _ _ _ _ r0 y0 v xs hb
      have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
        change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
        exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
      exact (result_guarantee_s238r δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius P.sel P.dst c q
        P.selected_injective (fun j=>(P.selection j).1) (fun j=>(P.selection j).2.2) P.destination_count hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma best_mem (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    best δ D S xs=S ∨ best δ D S xs∈xs := OrderedMaximum.mem _ _ _
lemma best_property (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (P : Finset (Fin n)→Prop) (hS : P S) (hxs : ∀ U∈xs,P U) : P (best δ D S xs) := by
  rcases best_mem δ D S xs with h|h
  · rwa [h]
  · exact hxs _ h
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionExponential
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling Guided

lemma completion_exponential : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 0 < m →
    Real.exp (-c*m) ≤ (1/(32*Real.exp 1))^m*(3/197:ℝ) := by
  let r : ℝ := (1/(32*Real.exp 1))*(3/197)
  have hr : 0 < r := by dsimp [r] <;> positivity
  refine ⟨1+|Real.log r|,by positivity,?_⟩
  intro m hm
  have he : Real.exp (-(1+|Real.log r|)*(m:ℝ)) ≤ r^m := by
    conv_rhs => rw [← Real.exp_log hr,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hl := neg_abs_le (Real.log r)
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  apply he.trans
  dsimp only [r]
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpow := pow_le_pow_of_le_one (show (0:ℝ) ≤ 3/197 by norm_num)
    (show (3/197:ℝ) ≤ 1 by norm_num) hm
  simpa only [pow_one] using hpow

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Failure
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FailureBudget

lemma failure_pos {g : ℝ} (hg : 0 < g) (e N : ℕ) : 0 < failure g e N := by
  unfold failure
  positivity

lemma failure_log {g : ℝ} (hg : 0 < g) (e N : ℕ) :
    Real.log (1/failure g e N) = Real.log (24/g) + (e:ℝ)*Real.log ((N:ℝ)+2) := by
  have hb : (0:ℝ) < (N:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have he : 1/failure g e N = (24/g)*((N:ℝ)+2)^e := by unfold failure; field_simp
  rw [he,Real.log_mul (div_ne_zero (by norm_num) hg.ne') (pow_ne_zero _ hb.ne'),Real.log_pow]

end MetricKMedianRecovery.FailureBudget

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_AffineLogBound
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LogPolynomial

lemma amplification_polynomial (c A g : ℝ) (e : ℕ) (hc : 0 ≤ c) (hg : 0 < g) :
    ∃ K d : ℕ, ∀ N L : ℕ, (L:ℝ) ≤ A*Real.log ((N:ℝ)+2) →
      ⌈Real.log (1/FailureBudget.failure g e N)/Real.exp (-c*L)⌉₊ ≤ K*(N+2)^d := by
  let m := ⌈c*A⌉₊
  let K := ⌈|Real.log (24/g)|+(e:ℝ)+1⌉₊
  refine ⟨K,m+1,?_⟩
  intro N L hL
  let b : ℝ := (N:ℝ)+2
  have hb : 0 < b := by dsimp [b] <;> positivity
  have hb1 : 1 ≤ b := by dsimp [b] <;> linarith [Nat.cast_nonneg (α := ℝ) N]
  have hlog : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hexp : Real.exp (c*L) ≤ b^m := by
    have hmul : c*(L:ℝ) ≤ (m:ℝ)*Real.log b := by
      calc
        _ ≤ c*(A*Real.log b) := mul_le_mul_of_nonneg_left hL hc
        _ = (c*A)*Real.log b := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlog
    calc
      _ ≤ Real.exp ((m:ℝ)*Real.log b) := Real.exp_le_exp.mpr hmul
      _ = b^m := by rw [Real.exp_nat_mul,Real.exp_log hb]
  have hlogb : Real.log b ≤ b := (Real.log_le_sub_one_of_pos hb).trans (by linarith)
  have hq : Real.log (1/FailureBudget.failure g e N) ≤
      (|Real.log (24/g)|+(e:ℝ))*b := by
    rw [FailureBudget.failure_log hg]
    have hconst : Real.log (24/g) ≤ |Real.log (24/g)| * b := by
      exact (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hb1)
    nlinarith [mul_le_mul_of_nonneg_left hlogb (Nat.cast_nonneg (α := ℝ) e)]
  have hnonneg : 0 ≤ (|Real.log (24/g)|+(e:ℝ))*b := by positivity
  have hdiv : Real.log (1/FailureBudget.failure g e N)/Real.exp (-c*L) ≤
      (|Real.log (24/g)|+(e:ℝ))*b^(m+1) := by
    rw [show -c*(L:ℝ) = -(c*L) by ring,Real.exp_neg,div_inv_eq_mul]
    calc
      _ ≤ ((|Real.log (24/g)|+(e:ℝ))*b)*Real.exp (c*L) :=
        mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
      _ ≤ ((|Real.log (24/g)|+(e:ℝ))*b)*b^m := mul_le_mul_of_nonneg_left hexp hnonneg
      _ = _ := by ring
  have hK : |Real.log (24/g)|+(e:ℝ)+1 ≤ (K:ℝ) := Nat.le_ceil _
  have hreal : Real.log (1/FailureBudget.failure g e N)/Real.exp (-c*L) ≤
      (K:ℝ)*b^(m+1) := by
    apply hdiv.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb.le _)
    linarith
  apply Nat.ceil_le.mpr
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,b] using hreal

end MetricKMedianRecovery.LogPolynomial

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape Completion FiniteSampling
variable {n m H : ℕ}
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (hn : n≤H) (hm : m≤H) (hH : 1≤H)
  (hp : s.leaves.length≤H) (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
lemma candidates_property (P : Finset (Fin n)→Prop)
    (hz : ∀ q,P (zero δ D F S Δ s hn hH hp seed q))
    (hb : ∀ q c b,P (positive δ D F S Δ s hn hm hp r0 y0 seed q c b)) :
    ∀ U∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed,P U := by
  intro U hU
  rcases List.mem_append.mp hU with hz'|hb'
  · obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz'
    exact hz q
  · obtain ⟨q,_,hq⟩:=List.mem_flatMap.mp hb'
    obtain ⟨c,_,hc⟩:=List.mem_flatMap.mp hq
    obtain ⟨b,rfl⟩:=List.mem_ofFn.mp hc
    exact hb q c b
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_DesignatedBranchSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (q : ℕ) (bits) :
    output δ D F S Δ s colors q bits⊆F ∧
      (output δ D F S Δ s colors q bits).card=S.card ∧
      (output δ D F S Δ s colors q bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
      change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
      exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
    exact (result_guarantee_s238r δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius
      (Fin.elim0 : Fin 0→Fin n) Fin.elim0 0 q (fun i=>Fin.elim0 i) (fun i=>Fin.elim0 i)
      (fun i=>Fin.elim0 i) (by simp) hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryFeasible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open Completion FiniteSampling
variable {n m H : ℕ} [PseudoMetricSpace (Fin n)]
variable (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
  (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
  (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n)
  (hn : n≤H) (hm : m≤H) (hH : 1≤H) (hp : s.leaves.length≤H)
  (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
include hδ hSF hS hΔ hbound
lemma candidates_feasible : ∀ U∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed,
    U⊆F ∧ U.card=S.card ∧ U.Nonempty := by
  apply candidates_property
  · intro q
    exact BinaryZeroBranch.output_feasible δ hδ D F S hSF hS Δ hΔ hbound s _ q.val _
  · intro q c b
    exact BinaryObservableBranch.output_feasible δ hδ D F S hSF hS Δ hΔ hbound s _ _ q.val c.val r0 y0 _
lemma result_feasible : result δ D F S Δ s hn hm hH hp r0 y0 seed⊆F ∧
    (result δ D F S Δ s hn hm hH hp r0 y0 seed).card=S.card ∧
    (result δ D F S Δ s hn hm hH hp r0 y0 seed).Nonempty := by
  exact BinaryMetricBest.best_property δ D S _ _ ⟨hSF,rfl,hS⟩
    (candidates_feasible δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryFeasible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open Completion Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
variable (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
  (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ)
  (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n)
  (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
  (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool)
include hδ hSF hS hbound
lemma optionOutput_feasible (w : Option (RationalSampling.State n)) :
    optionOutput δ D F S Δ m hm r0 y0 complete w⊆F ∧
    (optionOutput δ D F S Δ m hm r0 y0 complete w).card=S.card ∧
    (optionOutput δ D F S Δ m hm r0 y0 complete w).Nonempty := by
  cases w with
  | none=>exact ⟨hSF,rfl,hS⟩
  | some s=>
    unfold optionOutput
    simp only [Option.elim_some]
    split_ifs with hp
    · exact BinaryRecovery.result_feasible δ hδ D F S hSF hS Δ (by positivity) hbound s _ _ _ hp r0 y0 complete
    · exact ⟨hSF,rfl,hS⟩
lemma candidates_feasible : ∀ U∈candidates δ D F S Δ P m hm r0 y0 sample complete,
    U⊆F ∧ U.card=S.card ∧ U.Nonempty := by
  intro U hU
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hU
  exact optionOutput_feasible δ hδ D F S hSF hS Δ hbound m hm r0 y0 complete _
lemma result_feasible : result δ D F S Δ P m hm r0 y0 sample complete⊆F ∧
    (result δ D F S Δ P m hm r0 y0 sample complete).card=S.card ∧
    (result δ D F S Δ P m hm r0 y0 sample complete).Nonempty :=
  BinaryMetricBest.best_property δ D S _ _ ⟨hSF,rfl,hS⟩
    (candidates_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 sample complete)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n) (seed : Fin (count D Δ m)→Bool) :
    output δ D F S Δ P m hm r0 y0 seed⊆F ∧ (output δ D F S Δ P m hm r0 y0 seed).card=S.card ∧
      (output δ D F S Δ P m hm r0 y0 seed).Nonempty :=
  BinaryIntegralRecovery.result_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 _ _
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open Completion Sampling Sampling.Comparison FiniteSampling
lemma output_exponential : ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℚ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (_hPeq : (P:ℝ)=comparisonCost D C.assign)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (_hP : 0 < comparisonCost D C.assign) (_hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n),
    Real.exp (-c*C.bad.card)≤probability (fun seed:Fin (count D Δ C.bad.card)→Bool=>realCost D
      (output δ D F S Δ P C.bad.card hm r0 y0 seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  obtain ⟨c,hc,hsample⟩:=sampling_exponential
  obtain ⟨d,hd,hcompletion⟩:=completion_exponential
  refine ⟨c+d,add_pos hc hd,?_⟩
  intro n _ δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound P hPeq hsep hP hm0 hm r0 y0
  calc
    _=Real.exp (-c*C.bad.card)*Real.exp (-d*C.bad.card) := by rw [←Real.exp_add]; congr 1;ring
    _≤((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card)*((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)) :=
      mul_le_mul (hsample C.bad.card) (hcompletion C.bad.card hm0) (Real.exp_nonneg _)
        ((Real.exp_nonneg _).trans (hsample C.bad.card))
    _≤_ := output_success_s238r δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound P hPeq hsep hP hm0 hm r0 y0
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAmplified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n) (t : ℕ) (seed : Fin t→Fin (Fair.count D Δ m)→Bool) :
    output δ D F S Δ P m hm r0 y0 t seed⊆F ∧ (output δ D F S Δ P m hm r0 y0 t seed).card=S.card ∧
      (output δ D F S Δ P m hm r0 y0 t seed).Nonempty := by
  apply BinaryMetricBest.best_property δ D S _ (fun U=>U⊆F ∧ U.card=S.card ∧ U.Nonempty) ⟨hSF,rfl,hS⟩
  intro U hU
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hU
  exact Fair.output_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 (seed i)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open Completion Sampling Sampling.Comparison FiniteSampling
open Polynomial
lemma polynomial_program_s238r_oai (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℚ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (_hPeq : (P:ℝ)=comparisonCost D C.assign)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (_hP : 0 < comparisonCost D C.assign) (_hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n) (N : ℕ) (g : List Bool)
    (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
    (∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool,
      run Q d (Fair.pack δ D F S Δ P C.bad.card g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
        BinaryFinSet.encode (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed)) ∧
    (∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool,
      output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed⊆F ∧
      (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed).card=S.card ∧
      (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed).Nonempty) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
      (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
        realCost D (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed)≤
          (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
      realCost D (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed))≤
        (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  obtain ⟨c,hc,hexp⟩:=Fair.output_exponential
  obtain ⟨K,b,hb⟩:=LogPolynomial.amplification_polynomial c A IntegralAssembly.gamma e hc.le IntegralAssembly.gamma_pos_s238r
  obtain ⟨d,hd⟩:=run_source_s238r A
  let Q : Polynomial ℕ:=Polynomial.C K*(X+2)^b
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F S O C hD hSF hOF hS Δ hΔ hcap hbound P hPeq hsep hP hm0 hm r0 y0 N g hN hlog
  have hcount : ⌈Real.log (1/FailureBudget.failure IntegralAssembly.gamma e N)/
      Real.exp (-c*C.bad.card)⌉₊≤Q.eval g.length := by
    apply (hb N C.bad.card hlog).trans
    simp only [Q,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_ofNat]
    exact Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.add_le_add_right hN 2) b)
  have ht : Real.log (1/FailureBudget.failure IntegralAssembly.gamma e N)/Real.exp (-c*C.bad.card)≤((Q.eval g.length:ℕ):ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcount)
  have hh:=amplified_s238r δ hδ D F S hSF hS Δ hbound P C.bad.card hm r0 y0
    (by positivity : (0:ℝ)≤(197/100:ℝ)*comparisonCost D C.assign) (Real.exp_pos _)
    (hexp δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound P hPeq hsep hP hm0 hm r0 y0)
    (FailureBudget.failure_pos IntegralAssembly.gamma_pos_s238r e N) (Q.eval g.length) ht
  exact ⟨hd Q δ D F S Δ P C.bad.card hm hcap g N hN hlog r0 y0,
    output_feasible δ hδ D F S hSF hS Δ hbound P C.bad.card hm r0 y0 _,hh.2⟩
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r_oai
