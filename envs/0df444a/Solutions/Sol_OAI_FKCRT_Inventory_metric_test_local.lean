-- Prove2me | solution 1 for OAI.FKCRT.Inventory.metric_test_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T18:38:25.249933+00:00
-- url     : https://prove2.me/submissions/5f11fa18-7e9e-4c49-8b85-f56d43a1458e

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_OAIQ021F004

section
-- module Solutions.OAIQ021_FK.FKMaps_WalkBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma interpolation_apply (N : ℕ) (a : Fin (N+1) → ℝ) (t : unitInterval) :
    interpolation N a t = ∑ i : Fin (N+1), a i * hat N i.val t := by
  simp [interpolation]


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PathCLT
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma hat_gridPoint {N : ℕ} (hN : 0 < N) (i j : Fin (N+1)) :
    hat N j.val (gridPoint N i) = if i = j then 1 else 0 := by
  have hNR : (N:ℝ) ≠ 0 := by positivity
  change max 0 (1-|(N:ℝ)*((i.val:ℝ)/(N:ℝ))-(j.val:ℝ)|) = _
  rw [mul_div_cancel₀ _ hNR]
  split_ifs with hij
  · subst j
    simp
  · have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hab : 1 ≤ |(i.val:ℝ)-(j.val:ℝ)| := by
      rcases lt_or_gt_of_ne hn with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast Nat.le_of_lt h))]
        have hh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt h))]
        have hh : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
        linarith
    exact max_eq_left (by linarith)

lemma interpolation_gridPoint {N : ℕ} (hN : 0 < N) (a : Fin (N+1) → ℝ)
    (i : Fin (N+1)) : interpolation N a (gridPoint N i) = a i := by
  classical
  simp only [interpolation_apply,hat_gridPoint hN]
  simp

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Offspring
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureForallFinHAddNatHMulOfNatIidBridgeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma CriticalEvenOffspring.integrable_step (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => (k : ℝ) - 1) p.law.toMeasure :=
  p.integrable_id.sub (integrable_const 1)


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TreeCode
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


theorem CriticalEvenOffspring.stream_hits_negative (p : CriticalEvenOffspring)
    (j : ℕ) (hj : 0 < j) :
    ∀ᵐ ω ∂p.streamLaw, ∃ n, integerSum ω n=-(j:ℤ) := by
  let X : ℕ → (ℕ → ℕ) → ℝ := fun n ω => (ω n:ℝ)-1
  have hm (n : ℕ) : StronglyMeasurable (X n) := by fun_prop
  let ℱ := Filtration.natural X hm
  let S : ℕ → (ℕ → ℕ) → ℤ := fun n ω => (j:ℤ)+integerSum ω (n+1)
  have hM : Martingale (fun n ω => (S n ω:ℝ)) ℱ p.streamLaw := by
    have h := independent_sum_martingale X hm
      (fun n => (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).integrable_comp_of_integrable p.integrable_step)
      (iIndepFun_infinitePi (X := fun _ (k : ℕ) => (k:ℝ)-1) (fun _ => by fun_prop)) (fun n => by
        change (∫ ω, ((fun k : ℕ => (k:ℝ)-1) (ω n)) ∂p.streamLaw)=0
        exact ((measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).hasLaw.integral_comp
          (f := fun k : ℕ => (k:ℝ)-1) (by fun_prop)).trans p.integral_step)
    convert (martingale_const ℱ p.streamLaw (j:ℝ)).add h using 1
    all_goals try with_reducible_and_instances rfl
    ext n ω
    simp [S,integerSum,X]
  have hS : StronglyAdapted ℱ S := by
    intro n
    have h : Measurable[ℱ n] (fun ω => Int.floor (S n ω:ℝ)) :=
      Int.measurable_floor.comp (hM.stronglyMeasurable n).measurable
    simpa only [Int.floor_intCast] using h.stronglyMeasurable
  have h₀ (ω : ℕ → ℕ) : 0 ≤ S 0 ω := by
    dsimp [S]
    simp only [integerSum_succ,integerSum_zero,zero_add]
    omega
  have hstep (n : ℕ) (ω : ℕ → ℕ) : S n ω-1 ≤ S (n+1) ω := by
    dsimp [S]
    rw [integerSum_succ ω (n+1)]
    omega
  have hone : ∀ᵐ k ∂p.law.toMeasure, k≠1 := by
    rw [ae_iff]
    simpa using (show p.law.toMeasure {1}=0 by
      simp [p.even_support 1 (by decide)])
  have hall : ∀ᵐ ω ∂p.streamLaw, ∀ n, ω n≠1 := by
    rw [ae_all_iff]
    intro n
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).quasiMeasurePreserving.tendsto_ae hone
  have hjump : ∀ᵐ ω ∂p.streamLaw, ∃ᶠ n in atTop, S (n+1) ω≠S n ω := by
    filter_upwards [hall] with ω hω
    apply Filter.Frequently.of_forall
    intro n hn
    have h := hω (n+1)
    dsimp [S] at hn
    rw [integerSum_succ ω (n+1)] at hn
    omega
  filter_upwards [integer_martingale_hits_zero hS hM h₀ hstep hjump] with ω hω
  obtain ⟨n,hn⟩ := hω
  exact ⟨n+1,by dsimp [S] at hn; omega⟩


lemma reverseFirst_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (reverseFirst n) p.streamLaw p.streamLaw := by
  refine ⟨by unfold reverseFirst; fun_prop,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (reverseIndex_involutive n).injective


lemma integerSum_reverseFirst (x : ℕ → ℕ) (n k : ℕ) (hk : k ≤ n) :
    integerSum (reverseFirst n x) k=integerSum x n-integerSum x (n-k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < n := by omega
    have he : n-k=(n-(k+1))+1 := by omega
    have he' : n-1-k=n-(k+1) := by omega
    rw [integerSum_succ,ih (by omega)]
    simp only [reverseFirst,reverseIndex,ite_eq_left hk',he']
    rw [he,integerSum_succ]
    ring


lemma firstHitBelow_iff_reverse_survival (x : ℕ → ℕ) (j n : ℕ) :
    firstHitBelow x j n ↔ integerSum (reverseFirst n x) n=-(j:ℤ) ∧
      negativeSurvival (reverseFirst n x) n := by
  have he : integerSum (reverseFirst n x) n=integerSum x n := by
    simp [integerSum_reverseFirst x n n le_rfl]
  rw [he]
  constructor
  · rintro ⟨hx,hfirst⟩
    refine ⟨hx,?_⟩
    intro k hk hkn
    rw [integerSum_reverseFirst x n k hkn,hx]
    have h := hfirst (n-k) (by omega)
    omega
  · rintro ⟨hx,hs⟩
    refine ⟨hx,?_⟩
    intro k hkn
    have h := hs (n-k) (by omega) (by omega)
    rw [integerSum_reverseFirst x n (n-k) (by omega)] at h
    have he' : n-(n-k)=k := by omega
    rw [he',hx] at h
    omega


lemma measurable_integerSum (n : ℕ) : Measurable (fun x : ℕ → ℕ => integerSum x n) := by
  unfold integerSum
  fun_prop


lemma measurableSet_firstHitBelow (j n : ℕ) : MeasurableSet {x | firstHitBelow x j n} := by
  unfold firstHitBelow
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_integerSum n) measurable_const).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_integerSum k))


lemma measurableSet_survival_endpoint (j n : ℕ) :
    MeasurableSet {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} := by
  unfold negativeSurvival
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_integerSum n) measurable_const).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_integerSum k) measurable_const)


lemma CriticalEvenOffspring.survival_endpoint_eq_firstHit (p : CriticalEvenOffspring)
    (j n : ℕ) :
    p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n}=
      p.streamLaw {x | firstHitBelow x j n} := by
  rw [← (reverseFirst_preserving p n).measure_preimage (measurableSet_survival_endpoint j n).nullMeasurableSet]
  congr 1
  ext x
  exact (firstHitBelow_iff_reverse_survival x j n).symm


lemma exists_firstHitBelow (x : ℕ → ℕ) (j : ℕ) (_hj : 0 < j)
    (hex : ∃ n, integerSum x n=-(j:ℤ)) : ∃ n, firstHitBelow x j n := by
  classical
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  intro k hk
  have h0 : 0 ≤ (j:ℤ)+integerSum x 0 := by simp
  have hs (r : ℕ) : (j:ℤ)+integerSum x r-1 ≤ (j:ℤ)+integerSum x (r+1) := by
    rw [integerSum_succ]
    omega
  have hn (r : ℕ) (hr : r ≤ k) : (j:ℤ)+integerSum x r≠0 := by
    have h := Nat.find_min hex (by omega : r < Nat.find hex)
    omega
  have hpos := integer_path_nonneg_before_zero (fun r => (j:ℤ)+integerSum x r)
    h0 hs k (fun r hr => hn r hr.le)
  have hne := hn k le_rfl
  omega


lemma firstHitBelow_disjoint (j : ℕ) :
    Pairwise (fun n m => Disjoint {x | firstHitBelow x j n} {x | firstHitBelow x j m}) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · have hh := hm.2 n h
    rw [hn.1] at hh
    exact (lt_irrefl _ hh)
  · have hh := hn.2 m h
    rw [hm.1] at hh
    exact (lt_irrefl _ hh)


theorem CriticalEvenOffspring.negative_potential_one (p : CriticalEvenOffspring)
    (j : ℕ) (hj : 0 < j) :
    (∑' n, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n})=1 := by
  simp_rw [p.survival_endpoint_eq_firstHit]
  rw [← measure_iUnion (firstHitBelow_disjoint j) (measurableSet_firstHitBelow j)]
  apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (measurableSet_firstHitBelow j))).mp
  filter_upwards [p.stream_hits_negative j hj] with x hx
  obtain ⟨n,hn⟩ := exists_firstHitBelow x j hj hx
  exact Set.mem_iUnion.mpr ⟨n,hn⟩


lemma measurable_truncateStream (n : ℕ) : Measurable (truncateStream n) := by
  apply Measurable.of_eval
  intro k
  unfold truncateStream
  split_ifs <;> fun_prop


lemma integerSum_truncateStream (x : ℕ → ℕ) {k n : ℕ} (hkn : k ≤ n) :
    integerSum (truncateStream n x) k=integerSum x k := by
  unfold integerSum
  apply Finset.sum_congr rfl
  intro i hi
  simp [truncateStream,show i<n from lt_of_lt_of_le (Finset.mem_range.mp hi) hkn]


lemma CriticalEvenOffspring.truncate_indep_next (p : CriticalEvenOffspring) (n : ℕ) :
    IndepFun (truncateStream n) (fun x : ℕ → ℕ => x n) p.streamLaw := by
  classical
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) {n} := by simp
  have h := hi.indepFun_finset (Finset.range n) {n} hd (fun k => measurable_pi_apply k)
  let f : ((Finset.range n) → ℕ) → (ℕ → ℕ) :=
    fun x k => if hk : k<n then x ⟨k,Finset.mem_range.mpr hk⟩ else 0
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    dsimp [f]
    split_ifs <;> fun_prop
  have hh := h.comp hf (measurable_pi_apply ⟨n,by simp⟩)
  exact hh


lemma CriticalEvenOffspring.prefix_inter_next (p : CriticalEvenOffspring)
    (n r : ℕ) (E : Set (ℕ → ℕ)) (hE : MeasurableSet E)
    (htr : (truncateStream n) ⁻¹' E=E) :
    p.streamLaw (E ∩ {x | x n=r})=p.streamLaw E*p.law r := by
  have h := (p.truncate_indep_next n).measure_inter_preimage_eq_mul E {r} hE
    (measurableSet_singleton _)
  rw [htr] at h
  have he := (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).measure_preimage
    (measurableSet_singleton r).nullMeasurableSet
  change p.streamLaw ((fun x => x n) ⁻¹' {r})=p.law.toMeasure {r} at he
  rw [he] at h
  simpa only [Set.preimage,Set.mem_singleton_iff,p.law_singleton,p.law_apply] using h


lemma survival_endpoint_truncate (j n : ℕ) :
    (truncateStream n) ⁻¹' {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n}=
    {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} := by
  ext x
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [negativeSurvival,integerSum_truncateStream x le_rfl]
  constructor <;> rintro ⟨he,hs⟩ <;> refine ⟨he,?_⟩
  · intro k hk hkn
    simpa only [integerSum_truncateStream x hkn] using hs k hk hkn
  · intro k hk hkn
    simpa only [integerSum_truncateStream x hkn] using hs k hk hkn


lemma CriticalEvenOffspring.negative_potential_zero (p : CriticalEvenOffspring) :
    (∑' n, p.streamLaw {x | integerSum x n=0 ∧ negativeSurvival x n})=1 := by
  rw [tsum_eq_single 0]
  · have he : {x | integerSum x 0=0 ∧ negativeSurvival x 0}=(Set.univ : Set (ℕ → ℕ)) := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true,integerSum_zero,true_and]
      intro k hk hkn
      omega
    rw [he,measure_univ]
  · intro n hn
    have he : {x | integerSum x n=0 ∧ negativeSurvival x n}=(∅ : Set (ℕ → ℕ)) := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
      intro hx hs
      have h := hs n (Nat.pos_of_ne_zero hn) le_rfl
      omega
    rw [he,measure_empty]


lemma CriticalEvenOffspring.negative_potential (p : CriticalEvenOffspring) (j : ℕ) :
    (∑' n, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n})=1 := by
  cases j with
  | zero => simpa using p.negative_potential_zero
  | succ j => exact p.negative_potential_one _ (by omega)

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_LadderRecords
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma measurableSet_weakLadderHit (n k : ℕ) : MeasurableSet {x | weakLadderHit x n k} := by
  unfold weakLadderHit negativeSurvival
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_lt (measurable_integerSum j) measurable_const).inter
    (measurableSet_eq_fun (measurable_integerSum (n+1)) measurable_const)


lemma weakLadderHit_decomposition (n k : ℕ) :
    {x | weakLadderHit x n k}=⋃ j : ℕ,
      {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=j+k+1} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  constructor
  · rintro ⟨hs,he⟩
    have hn : integerSum x n ≤ 0 := by
      cases n with
      | zero => simp
      | succ n => exact (hs _ (by omega) le_rfl).le
    refine ⟨(-integerSum x n).toNat,⟨?_,hs⟩,?_⟩
    · rw [Int.toNat_of_nonneg (by omega)]
      omega
    · rw [integerSum_succ] at he
      have hj := Int.toNat_of_nonneg (show 0 ≤ -integerSum x n by omega)
      omega
  · rintro ⟨j,⟨he,hs⟩,hx⟩
    refine ⟨hs,?_⟩
    rw [integerSum_succ,he,hx]
    push_cast
    ring


lemma weakLadderHit_decomposition_disjoint (n k : ℕ) :
    Pairwise (fun j l : ℕ => Disjoint
      ({x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=j+k+1})
      ({x | integerSum x n=-(l:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=l+k+1})) := by
  intro j l hjl
  apply Set.disjoint_left.mpr
  intro x hj hl
  exact hjl (by have := hj.1.1; have := hl.1.1; omega)


lemma CriticalEvenOffspring.weakLadderHit_mass (p : CriticalEvenOffspring) (n k : ℕ) :
    p.streamLaw {x | weakLadderHit x n k}=
    ∑' j : ℕ, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} * p.law (j+k+1) := by
  rw [weakLadderHit_decomposition,measure_iUnion (weakLadderHit_decomposition_disjoint n k)]
  · apply tsum_congr
    intro j
    exact p.prefix_inter_next n (j+k+1) _ (measurableSet_survival_endpoint j n)
      (survival_endpoint_truncate j n)
  · intro j
    exact (measurableSet_survival_endpoint j n).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)


theorem CriticalEvenOffspring.weakLadder_overshoot_mass (p : CriticalEvenOffspring) (k : ℕ) :
    (∑' n, p.streamLaw {x | weakLadderHit x n k})=∑' j : ℕ, p.law (j+k+1) := by
  simp_rw [p.weakLadderHit_mass]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro j
  rw [ENNReal.tsum_mul_right,p.negative_potential,one_mul]


lemma CriticalEvenOffspring.variance_eq_second_sub_one (p : CriticalEvenOffspring) :
    p.variance=(∑' k : ℕ, (k:ℝ)^2*p.mass k)-1 := by
  have he : (fun k : ℕ => ((k:ℝ)-1)^2*p.mass k)=
      (fun k : ℕ => (k:ℝ)^2*p.mass k-2*((k:ℝ)*p.mass k)+p.mass k) := by
    funext k
    ring
  rw [variance,he]
  rw [Summable.tsum_add (p.second.sub (p.mean.summable.mul_left 2)) p.total.summable,
    Summable.tsum_sub p.second (p.mean.summable.mul_left 2),tsum_mul_left,p.mean.tsum_eq,p.total.tsum_eq]
  ring


lemma measurable_streamShift (n : ℕ) : Measurable (streamShift n) := by
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply _


lemma CriticalEvenOffspring.streamShift_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (streamShift n) p.streamLaw p.streamLaw := by
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hinj : Function.Injective (fun k : ℕ => n+k) := by intro a b h; dsimp at h; omega
  have h := (hi.precomp hinj).map_fun_eq_infinitePi_map (fun k => measurable_pi_apply (n+k))
  refine ⟨measurable_streamShift n,?_⟩
  change p.streamLaw.map (fun ω i => ω (n+i))=p.streamLaw
  rw [h]
  unfold CriticalEvenOffspring.streamLaw
  congr 1
  funext k
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) (n+k)).map_eq


lemma CriticalEvenOffspring.truncate_indep_shift (p : CriticalEvenOffspring) (n : ℕ) :
    IndepFun (truncateStream n) (streamShift n) p.streamLaw := by
  classical
  apply IndepFun.indepFun_process (measurable_truncateStream n) (fun k => measurable_pi_apply (n+k))
  intro I
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) (I.image (fun k => n+k)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    have := Finset.mem_range.mp hk
    omega
  have h := hi.indepFun_finset (Finset.range n) (I.image (fun k => n+k)) hd
    (fun k => measurable_pi_apply k)
  let f : ((Finset.range n) → ℕ) → (ℕ → ℕ) :=
    fun x k => if hk : k<n then x ⟨k,Finset.mem_range.mpr hk⟩ else 0
  let g : (I.image (fun k => n+k) → ℕ) → (I → ℕ) :=
    fun x k => x ⟨n+k,Finset.mem_image.mpr ⟨k,k.property,rfl⟩⟩
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    dsimp [f]
    split_ifs <;> fun_prop
  have hg : Measurable g := by fun_prop
  exact h.comp hf hg


lemma CriticalEvenOffspring.prefix_inter_shift (p : CriticalEvenOffspring)
    (n : ℕ) (E F : Set (ℕ → ℕ)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (htr : (truncateStream n) ⁻¹' E=E) :
    p.streamLaw (E ∩ (streamShift n) ⁻¹' F)=p.streamLaw E*p.streamLaw F := by
  have h := (p.truncate_indep_shift n).measure_inter_preimage_eq_mul E F hE hF
  rw [htr,(p.streamShift_preserving n).measure_preimage hF.nullMeasurableSet] at h
  exact h


lemma weakLadderHit_truncate (n k : ℕ) :
    (truncateStream (n+1)) ⁻¹' {x | weakLadderHit x n k}={x | weakLadderHit x n k} := by
  ext x
  change weakLadderHit (truncateStream (n+1) x) n k ↔ weakLadderHit x n k
  simp only [weakLadderHit,negativeSurvival,integerSum_truncateStream x le_rfl]
  constructor <;> rintro ⟨hs,he⟩ <;> refine ⟨?_,he⟩
  · intro j hj hjn
    simpa only [integerSum_truncateStream x (by omega : j ≤ n+1)] using hs j hj hjn
  · intro j hj hjn
    simpa only [integerSum_truncateStream x (by omega : j ≤ n+1)] using hs j hj hjn


lemma weakLadderHit_unique {x : ℕ → ℕ} {n k m l : ℕ}
    (hn : weakLadderHit x n k) (hm : weakLadderHit x m l) : n=m ∧ k=l := by
  have he : n=m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hh := hm.1 (n+1) (by omega) (by omega)
      rw [hn.2] at hh
      omega
    · have hh := hn.1 (m+1) (by omega) (by omega)
      rw [hm.2] at hh
      omega
  refine ⟨he,?_⟩
  subst m
  have := hn.2
  have := hm.2
  omega


lemma weakLadderHit_pairwise : Pairwise (fun a b : ℕ × ℕ =>
    Disjoint {x | weakLadderHit x a.1 a.2} {x | weakLadderHit x b.1 b.2}) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x ha hb
  have h := weakLadderHit_unique ha hb
  exact hab (Prod.ext h.1 h.2)


lemma CriticalEvenOffspring.ae_weakLadderHit (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, ∃ n k, weakLadderHit x n k := by
  have he : {x | ∃ n k, weakLadderHit x n k}=⋃ a : ℕ×ℕ,{x | weakLadderHit x a.1 a.2} := by
    ext x
    simp
  apply (mem_ae_iff_prob_eq_one (show MeasurableSet {x | ∃ n k, weakLadderHit x n k} from by
    rw [he]; exact MeasurableSet.iUnion fun a => measurableSet_weakLadderHit a.1 a.2)).mpr
  rw [he,measure_iUnion weakLadderHit_pairwise (fun a => measurableSet_weakLadderHit a.1 a.2),
    ENNReal.tsum_prod',ENNReal.tsum_comm]
  simp_rw [p.weakLadder_overshoot_mass]
  exact p.ladder_total


lemma measurableSet_hasWeakLadder : MeasurableSet {x : ℕ → ℕ | ∃ n, 0 ≤ integerSum x (n+1)} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun n => measurableSet_le measurable_const (measurable_integerSum (n+1))


lemma measurable_ladderIndex : Measurable ladderIndex := by
  classical
  apply measurable_find (fun x => ladderPredicate_exists x)
  intro n
  unfold ladderPredicate
  simp only [Set.ofPred_or,Set.ofPred_and,← Set.compl_ofPred]
  exact (measurableSet_le measurable_const (measurable_integerSum (n+1))).union
    (measurableSet_hasWeakLadder.compl.inter (MeasurableSet.const _))


lemma ladderIndex_eq_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderIndex x=n := by
  classical
  apply (Nat.find_eq_iff (ladderPredicate_exists x)).mpr
  refine ⟨Or.inl (by rw [h.2]; positivity),?_⟩
  intro j hj
  rintro (hj' | hj')
  · have hh := h.1 (j+1) (by omega) (by omega)
    omega
  · exact hj'.1 ⟨n,by rw [h.2]; positivity⟩


lemma measurable_ladderOvershoot : Measurable ladderOvershoot := by
  have hs : Measurable (fun x : ℕ → ℕ => (x,ladderIndex x+1)) :=
    measurable_id.prodMk (measurable_ladderIndex.add_const 1)
  have he : Measurable (fun z : (ℕ → ℕ)×ℕ => integerSum z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_integerSum n
  exact (measurable_of_countable (f := Int.toNat)).comp (he.comp hs)


lemma ladderOvershoot_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderOvershoot x=k := by
  rw [ladderOvershoot,ladderIndex_eq_of_hit h,h.2,Int.toNat_natCast]


lemma ladderTail_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderTail x=streamShift (n+1) x := by
  rw [ladderTail,ladderIndex_eq_of_hit h]


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightCoding
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma reverse_record_iff (S : ℕ → ℤ) {a b j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    j ∈ reverseRecords S a b ↔ b-j ∈ weakRecords (reversedPath S b) (b-a) := by
  rw [mem_reverseRecords,mem_weakRecords]
  constructor
  · rintro ⟨_,_,hrec⟩
    refine ⟨by omega,by omega,?_⟩
    intro k hk
    have hr := hrec (b-k) (by omega) (by omega)
    dsimp [reversedPath]
    have he : b-(b-j)=j := by omega
    rw [he]
    omega
  · rintro ⟨_,_,hrec⟩
    refine ⟨haj,hjb,?_⟩
    intro r hjr hrb
    have hr := hrec (b-r) (by omega)
    dsimp [reversedPath] at hr
    have he : b-(b-r)=r := by omega
    have he' : b-(b-j)=j := by omega
    rw [he,he'] at hr
    omega


lemma reverse_record_filter_card (S : ℕ → ℤ) (a b : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    ((reverseRecords S a b).filter P).card=
      ((weakRecords (reversedPath S b) (b-a)).filter fun k => P (b-k)).card := by
  classical
  apply Finset.card_bij (fun j _ => b-j)
  · intro j hj
    obtain ⟨hrec,hP⟩ := Finset.mem_filter.mp hj
    obtain ⟨haj,hjb,_⟩ := (mem_reverseRecords S a b j).mp hrec
    refine Finset.mem_filter.mpr ⟨(reverse_record_iff S haj hjb).mp hrec,?_⟩
    convert hP using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · intro j hj k hk he
    have hjb := ((mem_reverseRecords S a b j).mp (Finset.mem_filter.mp hj).1).2.1
    have hkb := ((mem_reverseRecords S a b k).mp (Finset.mem_filter.mp hk).1).2.1
    omega
  · intro k hk
    obtain ⟨hrec,hP⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1,hkba,_⟩ := (mem_weakRecords _ _ _).mp hrec
    refine ⟨b-k,?_,by omega⟩
    refine Finset.mem_filter.mpr ⟨?_,hP⟩
    apply (reverse_record_iff S (by omega : a ≤ b-k) (by omega : b-k < b)).mpr
    convert hrec using 1
    all_goals try with_reducible_and_instances rfl
    omega


lemma recordHeight_dual (S : ℕ → ℤ) (a b : ℕ) :
    recordHeight S a b=(weakRecords (reversedPath S b) (b-a)).card := by
  simpa [recordHeight] using reverse_record_filter_card S a b (fun _ => True)


lemma weakRecords_congr_prefix {S T : ℕ → ℤ} {n : ℕ}
    (he : ∀ k, k ≤ n → S k=T k) : weakRecords S n=weakRecords T n := by
  ext k
  simp only [mem_weakRecords]
  constructor <;> rintro ⟨hk,hkn,hr⟩ <;> refine ⟨hk,hkn,?_⟩
  · intro j hj
    rw [← he j (by omega),← he k hkn]
    exact hr j hj
  · intro j hj
    rw [he j (by omega),he k hkn]
    exact hr j hj


lemma height_eq_recordHeight {N : ℕ} (d : Fin N → Fin N) {j : ℕ} (hj : j ≤ N) :
    height d j=recordHeight (walk d) 0 j := by
  classical
  unfold height recordHeight
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    obtain ⟨_,hkj,hrec⟩ := Finset.mem_filter.mp hk
    apply (mem_reverseRecords ..).mpr
    refine ⟨Nat.zero_le _,hkj,?_⟩
    intro r hkr hrj
    exact hrec ⟨r,by omega⟩ hkr hrj
  · intro k _ l _ he
    exact Fin.ext he
  · intro k hk
    obtain ⟨_,hkj,hrec⟩ := (mem_reverseRecords ..).mp hk
    refine ⟨⟨k,by omega⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkj,fun r hr hjr => hrec r.val hr hjr⟩


lemma prefixMaximum_congr {S T : ℕ → ℤ} {N : ℕ} (h : ∀ k, k ≤ N → S k=T k) :
    prefixMaximum S N=prefixMaximum T N := by
  unfold prefixMaximum
  apply Finset.sup'_congr _ rfl
  intro k hk
  exact h k (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk)


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma integerSum_arrayStream_bridge {N : ℕ} (d : Bridge N) {k : ℕ} (hk : k ≤ N) :
    integerSum (arrayStream (bridgeEmbedding N d)) k=walk d.val k := by
  unfold integerSum walk
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val,by
    have hh := Finset.mem_filter.mp hi
    exact hh.2⟩ : Fin k))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun z : Fin k => z.val) he)
  · intro i _
    exact ⟨⟨i.val,i.isLt.trans_le hk⟩,by simp [i.isLt],rfl⟩
  · intro i hi
    have hi' : i.val<k := (Finset.mem_filter.mp hi).2
    simp only [arrayStream,dite_eq_left (hi'.trans_le hk),bridgeEmbedding]
    rfl

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightTightness
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma recordHeight_congr_prefix {S T : ℕ → ℤ} {N j : ℕ} (hj : j ≤ N)
    (hST : ∀ k ≤ N, S k=T k) : recordHeight S 0 j=recordHeight T 0 j := by
  unfold recordHeight
  congr 1
  ext k
  simp only [mem_reverseRecords]
  constructor <;> rintro ⟨hk0,hkj,hk⟩ <;> refine ⟨hk0,hkj,?_⟩ <;> intro r hkr hrj
  · rw [← hST k (by omega),← hST r (by omega)]
    exact hk r hkr hrj
  · rw [hST k (by omega),hST r (by omega)]
    exact hk r hkr hrj

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_GraphWedge
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal
namespace FKCRT.GraphWedge
variable {A B V : Type*} (G : SimpleGraph A) (K : SimpleGraph B) (H : SimpleGraph V)

/-- Each original edge belongs to exactly one block; a collapsed loop may
have zero cost in either retraction. This local statement implies the full
global, all-edge metric lower bound. -/
lemma retraction_pair_edist_le (r : V→A) (s : V→B)
    (h : ∀ {u v},H.Adj u v → G.edist (r u) (r v)+K.edist (s u) (s v) ≤ 1)
    (u v : V) : G.edist (r u) (r v)+K.edist (s u) (s v) ≤ H.edist u v := by
  unfold SimpleGraph.edist
  apply le_iInf
  intro w
  change G.edist (r u) (r v)+K.edist (s u) (s v) ≤ (w.length:ℕ∞)
  induction w with
  | nil => simp
  | @cons u x v hadj w ih =>
    calc
      G.edist (r u) (r v)+K.edist (s u) (s v) ≤
          (G.edist (r u) (r x)+G.edist (r x) (r v))+
          (K.edist (s u) (s x)+K.edist (s x) (s v)) :=
        add_le_add (G.edist_triangle) (K.edist_triangle)
      _=(G.edist (r u) (r x)+K.edist (s u) (s x))+
          (G.edist (r x) (r v)+K.edist (s x) (s v)) := by ac_rfl
      _≤1+(w.length:ℕ∞) := add_le_add (h hadj) ih
      _=((SimpleGraph.Walk.cons hadj w).length:ℕ∞) := by simp [add_comm]

lemma hom_edist_le {A V : Type*} {G : SimpleGraph A} {H : SimpleGraph V}
    (i : G→g H) (x y : A) : H.edist (i x) (i y) ≤ G.edist x y := by
  unfold SimpleGraph.edist
  apply le_iInf
  intro w
  change H.edist (i x) (i y) ≤ (w.length:ℕ∞)
  simpa only [SimpleGraph.Walk.length_map] using (w.map i).edist_le

namespace Data
variable {G K H}

lemma cost_le (D : Data G K H) {u v : V} (h : H.Adj u v) :
    G.edist (D.retractLeft u) (D.retractLeft v)+
      K.edist (D.retractRight u) (D.retractRight v) ≤ 1 := by
  rcases D.edge h with ⟨h,h'⟩|⟨h',h⟩
  · rw [h',SimpleGraph.edist_self,add_zero,SimpleGraph.edist_eq_one_iff_adj.mpr h]
  · rw [h',SimpleGraph.edist_self,zero_add,SimpleGraph.edist_eq_one_iff_adj.mpr h]

/-- Attachments cannot shorten distances within any block. -/
theorem edist_left (D : Data G K H) (x y : A) : H.edist (D.left x) (D.left y)=G.edist x y := by
  apply le_antisymm (hom_edist_le D.left x y)
  have h := retraction_pair_edist_le G K H D.retractLeft D.retractRight D.cost_le (D.left x) (D.left y)
  simpa only [D.left_left,D.right_left,SimpleGraph.edist_self,add_zero] using h

theorem edist_right (D : Data G K H) (x y : B) : H.edist (D.right x) (D.right y)=K.edist x y := by
  apply le_antisymm (hom_edist_le D.right x y)
  have h := retraction_pair_edist_le G K H D.retractLeft D.retractRight D.cost_le (D.right x) (D.right y)
  simpa only [D.right_right,D.left_right,SimpleGraph.edist_self,zero_add] using h

/-- Distances between blocks add exactly through their shared pole. -/
theorem edist_cross (D : Data G K H) (x : A) (y : B) :
    H.edist (D.left x) (D.right y)=G.edist x D.poleLeft+K.edist D.poleRight y := by
  apply le_antisymm
  · calc
      H.edist (D.left x) (D.right y) ≤
        H.edist (D.left x) (D.left D.poleLeft)+H.edist (D.left D.poleLeft) (D.right y) :=
          H.edist_triangle
      _=_ := by rw [D.edist_left,D.shared,D.edist_right]
  · have h := retraction_pair_edist_le G K H D.retractLeft D.retractRight D.cost_le (D.left x) (D.right y)
    simpa only [D.left_left,D.right_right,D.right_left,D.left_right] using h

end Data
end FKCRT.GraphWedge
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionGeometry
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions _root_.OAI.FKCRT.rootedMap_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal

namespace FKCRT

lemma excursionDist_nonneg {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) : 0 ≤ excursionDist e s t := by
  have h1 := interval_inf_le_left he s t
  have h2 := interval_inf_le_right he s t
  dsimp [excursionDist, two_mul]
  linarith

lemma excursionDist_eq_of_zero_left {e : unitInterval → ℝ} (he : Continuous e)
    {s t : unitInterval} (hst : excursionDist e s t = 0) (u : unitInterval) :
    excursionDist e s u = excursionDist e t u := by
  have h1 := excursionDist_triangle he s t u
  have h2 := excursionDist_triangle he t s u
  rw [excursionDist_comm e t s, hst] at h2
  rw [hst] at h1
  linarith

lemma excursionDist_zero_of_eqvGen {e : unitInterval → ℝ} (he : Continuous e)
    {s t : unitInterval}
    (hst : Relation.EqvGen (fun s t => excursionDist e s t = 0) s t) :
    excursionDist e s t = 0 := by
  induction hst with
  | rel s t h => exact h
  | refl s => exact excursionDist_self e s
  | symm s t _ h => simpa only [excursionDist_comm e t s] using h
  | trans s t u _ _ h1 h2 =>
      have h3 := excursionDist_triangle he s t u
      have h4 := excursionDist_nonneg he s u
      rw [h1, h2] at h3
      linarith


lemma treeProjection_surjective (e : unitInterval → ℝ) :
    Function.Surjective (treeProjection e) := Quotient.mk_surjective

lemma excursionDist_out {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) :
    excursionDist e (treeProjection e s).out (treeProjection e t).out =
      excursionDist e s t := by
  unfold treeProjection
  rw [excursionDist_eq_of_zero_left he
    (excursionDist_zero_of_eqvGen he (Quotient.mk_out (s := Relation.EqvGen.setoid (fun s t => excursionDist e s t = 0)) s))]
  rw [excursionDist_comm e s, excursionDist_eq_of_zero_left he
    (excursionDist_zero_of_eqvGen he (Quotient.mk_out (s := Relation.EqvGen.setoid (fun s t => excursionDist e s t = 0)) t)), excursionDist_comm]

lemma unitInterval_dist_le_of_mem_uIcc {r s t : unitInterval} (hr : r ∈ uIcc s t) :
    dist r s ≤ dist t s := by
  change |(r : ℝ) - (s : ℝ)| ≤ |(t : ℝ) - (s : ℝ)|
  rcases le_total s t with h | h
  · rw [uIcc_of_le h] at hr
    have h1 : (s : ℝ) ≤ (r : ℝ) := hr.1
    have h2 : (r : ℝ) ≤ (t : ℝ) := hr.2
    rw [abs_of_nonneg (sub_nonneg.mpr h1),
      abs_of_nonneg (sub_nonneg.mpr (h1.trans h2))]
    linarith
  · rw [uIcc_of_ge h] at hr
    have h1 : (t : ℝ) ≤ (r : ℝ) := hr.1
    have h2 : (r : ℝ) ≤ (s : ℝ) := hr.2
    rw [abs_of_nonpos (sub_nonpos.mpr h2),
      abs_of_nonpos (sub_nonpos.mpr (h1.trans h2))]
    linarith

lemma treeProjection_continuous {e : unitInterval → ℝ} (he : Continuous e) :
    @Continuous _ _ inferInstance
      (excursionTreeMetric he).toUniformSpace.toTopologicalSpace (treeProjection e) := by
  let : MetricSpace (ExcursionTree e) := excursionTreeMetric he
  apply Metric.continuous_iff.mpr
  intro s ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp he s (ε / 4) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  change excursionDist e (treeProjection e t).out (treeProjection e s).out < ε
  rw [excursionDist_out he]
  have h1 : e t < e s + ε / 4 := by
    have := (abs_lt.mp (h t ht)).2
    linarith
  have h2 : e s - ε / 4 ≤ sInf (e '' uIcc t s) := by
    apply le_csInf (nonempty_uIcc.image e)
    rintro _ ⟨r, hr, rfl⟩
    rw [uIcc_comm] at hr
    have hd : dist r s < δ := (unitInterval_dist_le_of_mem_uIcc hr).trans_lt ht
    have := (abs_lt.mp (h r hd)).1
    linarith
  dsimp [excursionDist]
  linarith


lemma excursionTree_topology {e : unitInterval → ℝ} (he : Continuous e) :
    (excursionTreeMetric he).toUniformSpace.toTopologicalSpace =
      TopologicalSpace.coinduced (treeProjection e) inferInstance := by
  let m : MetricSpace (ExcursionTree e) := excursionTreeMetric he
  let t : TopologicalSpace (ExcursionTree e) := m.toUniformSpace.toTopologicalSpace
  have hc : Continuous (treeProjection e) := treeProjection_continuous he
  exact (hc.isClosedMap.isQuotientMap hc (treeProjection_surjective e)).isCoinducing.eq_coinduced

lemma excursionTree_compact {e : unitInterval → ℝ} (he : Continuous e) :
    @CompactSpace (ExcursionTree e) (excursionTreeMetric he).toUniformSpace.toTopologicalSpace := by
  let m : MetricSpace (ExcursionTree e) := excursionTreeMetric he
  let t : TopologicalSpace (ExcursionTree e) := m.toUniformSpace.toTopologicalSpace
  have hc : Continuous (treeProjection e) := treeProjection_continuous he
  apply isCompact_univ_iff.mp
  have h := isCompact_univ.image hc
  rwa [image_univ, (treeProjection_surjective e).range_eq] at h

lemma unitInterval_volume_univ : (volume : Measure unitInterval) univ = 1 := by
  rw [volume_set_coe_def, comap_subtype_coe_apply measurableSet_Icc,
    Set.image_univ, Subtype.range_coe]
  rw [Real.volume_Icc]
  norm_num


lemma treeSpace_mass_univ (e : unitInterval → ℝ) :
    (treeSpace e).mass univ = 1 := by
  let t : TopologicalSpace (ExcursionTree e) :=
    TopologicalSpace.coinduced (treeProjection e) inferInstance
  let ms : MeasurableSpace (ExcursionTree e) := borel _
  let bs : BorelSpace (ExcursionTree e) := ⟨rfl⟩
  have hc : Continuous (treeProjection e) := continuous_iff_coinduced_le.mpr le_rfl
  change (Measure.map (treeProjection e) (volume : Measure unitInterval)) univ = 1
  rw [Measure.map_apply hc.measurable MeasurableSet.univ, preimage_univ,
    unitInterval_volume_univ]

/-- A continuous excursion codes a compact metric probability space. No
positivity or endpoint hypotheses are required for this validity statement. -/
lemma treeSpace_valid {e : unitInterval → ℝ} (he : Continuous e) : (treeSpace e).Valid := by
  refine ⟨excursionTreeMetric he, ?_⟩
  refine ⟨fun _ _ => rfl, excursionTree_compact he, ?_, treeSpace_mass_univ e⟩
  change @borel _ (TopologicalSpace.coinduced (treeProjection e) inferInstance) =
    @borel _ (excursionTreeMetric he).toUniformSpace.toTopologicalSpace
  rw [excursionTree_topology he]


lemma interval_inf_sub_le {e f : unitInterval → ℝ}
    (he : Continuous e) (s t : unitInterval) {ε : ℝ}
    (h : ∀ r, e r - f r ≤ ε) :
    sInf (e '' uIcc s t) - sInf (f '' uIcc s t) ≤ ε := by
  have hi : sInf (e '' uIcc s t) - ε ≤ sInf (f '' uIcc s t) := by
    apply le_csInf (nonempty_uIcc.image f)
    rintro _ ⟨r, hr, rfl⟩
    have h1 := csInf_le (interval_image_bddBelow he s t) (mem_image_of_mem e hr)
    have h2 := h r
    linarith
  linarith

lemma interval_inf_abs_sub_le {e f : unitInterval → ℝ}
    (he : Continuous e) (hf : Continuous f) (s t : unitInterval) {ε : ℝ}
    (h : ∀ r, |e r - f r| ≤ ε) :
    |sInf (e '' uIcc s t) - sInf (f '' uIcc s t)| ≤ ε := by
  apply abs_le.mpr
  constructor
  · have hi := interval_inf_sub_le (f := e) hf s t (ε := ε)
      (fun r => by have := (abs_le.mp (h r)).1; linarith)
    linarith
  · exact interval_inf_sub_le he s t (fun r => (abs_le.mp (h r)).2)

/-- Deterministic four-times-sup-norm distortion bound for excursion coding. -/
lemma excursionDist_abs_sub_le {e f : unitInterval → ℝ}
    (he : Continuous e) (hf : Continuous f) (s t : unitInterval) {ε : ℝ}
    (h : ∀ r, |e r - f r| ≤ ε) :
    |excursionDist e s t - excursionDist f s t| ≤ 4 * ε := by
  have hs := abs_le.mp (h s)
  have ht := abs_le.mp (h t)
  have hi := abs_le.mp (interval_inf_abs_sub_le he hf s t h)
  apply abs_le.mpr
  dsimp [excursionDist]
  constructor <;> linarith


lemma levyProkhorovEDist_map_le_of_dist {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y] [PseudoMetricSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure Z) {f g : Z → Y}
    (hf : Measurable f) (hg : Measurable g) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ z, dist (f z) (g z) ≤ ε) :
    levyProkhorovEDist (μ.map f) (μ.map g) ≤ ENNReal.ofReal ε := by
  apply levyProkhorovEDist_le_of_forall
  intro r B hr hrt hB
  have hεr : ε < r.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hε hrt.ne).mp hr
  have hBg : MeasurableSet (Metric.thickening r.toReal B) :=
    Metric.isOpen_thickening.measurableSet
  constructor
  · apply le_trans _ le_self_add
    rw [Measure.map_apply hf hB, Measure.map_apply hg hBg]
    apply measure_mono
    intro z hz
    exact Metric.mem_thickening_iff.mpr ⟨f z, hz,
      (by rw [dist_comm]; exact (hfg z).trans_lt hεr)⟩
  · apply le_trans _ le_self_add
    rw [Measure.map_apply hg hB, Measure.map_apply hf hBg]
    apply measure_mono
    intro z hz
    exact Metric.mem_thickening_iff.mpr ⟨g z, hz, (hfg z).trans_lt hεr⟩

/-- A common coding with distortion at most `2ε` and a common mass gives
GHP distance at most `ε`. The metric-quotient gluing is supplied by Mathlib. -/
lemma ghpEDist_le_of_coding {X Y : MetricMeasureData}
    (hX : X.Valid) (hY : Y.Valid) {Z : Type} [Nonempty Z] [MeasurableSpace Z]
    (μ : Measure Z) (f : Z → X.Carrier) (g : Z → Y.Carrier)
    (hf : @Measurable _ _ inferInstance X.measurableSpace f)
    (hg : @Measurable _ _ inferInstance Y.measurableSpace g)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hmf : @Measure.map _ _ inferInstance X.measurableSpace f μ = X.mass)
    (hmg : @Measure.map _ _ inferInstance Y.measurableSpace g μ = Y.mass)
    {ε : ℝ} (hε : 0 < ε)
    (hfg : ∀ s t, |X.distance (f s) (f t) - Y.distance (g s) (g t)| ≤ 2 * ε) :
    ghpEDist X Y ≤ ENNReal.ofReal ε := by
  obtain ⟨mX, hdX, _, hbX, _⟩ := hX
  obtain ⟨mY, hdY, _, hbY, _⟩ := hY
  let : MetricSpace X.Carrier := mX
  let : MetricSpace Y.Carrier := mY
  let : MeasurableSpace X.Carrier := X.measurableSpace
  let : MeasurableSpace Y.Carrier := Y.measurableSpace
  let : BorelSpace X.Carrier := ⟨hbX⟩
  let : BorelSpace Y.Carrier := ⟨hbY⟩
  have hfg' : ∀ s t, |dist (f s) (f t) - dist (g s) (g t)| ≤ 2 * ε := by
    simpa only [hdX, hdY] using hfg
  let m := Metric.glueMetricApprox f g ε hε hfg'
  have hm : Amalgamates X Y m.toPseudoMetricSpace := ⟨hdX, hdY⟩
  apply (iInf_le (fun m : {m : PseudoMetricSpace (X.Carrier ⊕ Y.Carrier) //
      Amalgamates X Y m} => ambientCost X Y m.val) ⟨m.toPseudoMetricSpace, hm⟩).trans
  let : MetricSpace (X.Carrier ⊕ Y.Carrier) := m
  let : MeasurableSpace (X.Carrier ⊕ Y.Carrier) := borel _
  let : BorelSpace (X.Carrier ⊕ Y.Carrier) := ⟨rfl⟩
  have hclose : ∀ z, dist (Sum.inl (f z) : X.Carrier ⊕ Y.Carrier) (Sum.inr (g z)) = ε :=
    Metric.glueDist_glued_points f g ε
  have hml : Measurable (Sum.inl : X.Carrier → X.Carrier ⊕ Y.Carrier) :=
    continuous_inl.measurable
  have hmr : Measurable (Sum.inr : Y.Carrier → X.Carrier ⊕ Y.Carrier) :=
    continuous_inr.measurable
  apply max_le
  · apply Metric.hausdorffEDist_le_of_mem_edist
    · rintro _ ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := hsf x
      refine ⟨Sum.inr (g z), mem_range_self _, ?_⟩
      rw [edist_dist, hclose]
    · rintro _ ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := hsg y
      refine ⟨Sum.inl (f z), mem_range_self _, ?_⟩
      rw [edist_comm, edist_dist, hclose]
  · change levyProkhorovEDist (X.mass.map Sum.inl) (Y.mass.map Sum.inr) ≤ _
    rw [← hmf, ← hmg, Measure.map_map hml hf, Measure.map_map hmr hg]
    apply levyProkhorovEDist_map_le_of_dist μ (hml.comp hf) (hmr.comp hg) hε.le
    exact fun z => (hclose z).le


lemma degreeMass_univ {n : ℕ} (M : RootedMap n) : degreeMass M univ = 1 := by
  simp only [degreeMass, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [show (↑(2 * (n + 1)) : ℝ) * (1 / (2 * (n + 1) : ℝ)) = 1 by
    push_cast
    field_simp]
  simp

lemma mapSpace_valid {n : ℕ} {scale : ℝ} (hscale : 0 < scale) (M : RootedMap n) :
    (mapSpace scale M).Valid := by
  let m := mapMetric hscale M
  let : MetricSpace (Vertex M) := m
  let : TopologicalSpace (Vertex M) := m.toUniformSpace.toTopologicalSpace
  have hc : @CompactSpace (Vertex M) m.toUniformSpace.toTopologicalSpace :=
    @Finite.compactSpace (Vertex M) m.toUniformSpace.toTopologicalSpace inferInstance
  refine ⟨m, fun _ _ => rfl, hc, ?_, degreeMass_univ M⟩
  change ⊤ = @borel (Vertex M) m.toUniformSpace.toTopologicalSpace
  exact borel_eq_top_of_discrete.symm


lemma treeProjection_measurable (e : unitInterval → ℝ) :
    @Measurable _ _ inferInstance (treeSpace e).measurableSpace (treeProjection e) := by
  let t : TopologicalSpace (ExcursionTree e) :=
    TopologicalSpace.coinduced (treeProjection e) inferInstance
  let ms : MeasurableSpace (ExcursionTree e) := borel _
  let bs : BorelSpace (ExcursionTree e) := ⟨rfl⟩
  have hc : Continuous (treeProjection e) := continuous_iff_coinduced_le.mpr le_rfl
  exact hc.measurable

/-- The excursion-to-measured-tree map preserves the exact uniform-time mass. -/
lemma ghpEDist_treeSpace_le {e f : unitInterval → ℝ}
    (he : Continuous e) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t, |e t - f t| ≤ ε) :
    ghpEDist (treeSpace e) (treeSpace f) ≤ ENNReal.ofReal (2 * ε) := by
  apply ghpEDist_le_of_coding (treeSpace_valid he) (treeSpace_valid hf) volume
    (treeProjection e) (treeProjection f) (treeProjection_measurable e)
    (treeProjection_measurable f) (treeProjection_surjective e)
    (treeProjection_surjective f) rfl rfl (by positivity)
  intro s t
  change |excursionDist e (treeProjection e s).out (treeProjection e t).out -
    excursionDist f (treeProjection f s).out (treeProjection f t).out| ≤ _
  rw [excursionDist_out he, excursionDist_out hf]
  convert excursionDist_abs_sub_le he hf s t h using 1 <;> first | rfl | ring

lemma IsGHPTest.continuous_treeSpace {F : MetricMeasureData → ℝ} (hF : IsGHPTest F) :
    Continuous (fun e : C(unitInterval, ℝ) => F (treeSpace e)) := by
  apply Metric.continuous_iff.mpr
  intro e ε hε
  obtain ⟨δ, hδ, hh⟩ := hF.2 (treeSpace e) (treeSpace_valid e.continuous) ε hε
  refine ⟨δ / 4, by positivity, ?_⟩
  intro f hfe
  rw [Real.dist_eq]
  apply hh (treeSpace f) (treeSpace_valid f.continuous)
  apply lt_of_le_of_lt (ghpEDist_treeSpace_le e.continuous f.continuous
    (show 0 < δ / 4 by positivity) ?_) ?_
  · intro t
    have hpoint := ContinuousMap.dist_apply_le_dist (f := f) (g := e) t
    rw [Real.dist_eq, abs_sub_comm] at hpoint
    exact hpoint.trans hfe.le
  · apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
    linarith

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreCompression
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma formPerm_append_comm (v z : List α) (hn : (v++z).Nodup) :
    (v++z).formPerm=(z++v).formPerm := by
  have h := List.formPerm_rotate (v++z) hn v.length
  rw [List.rotate_append_length_eq] at h
  exact h.symm

omit [Fintype α] in
/-- Cutting any nonempty successful insertion interval is a literal
one-vertex split of the original rotation. No random root/rotation is used. -/
lemma StackMatching.empty_interval_rotation {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hcomp : z++u=b::R) :
    (u++((a::L)++z)).formPerm*turns M.first=
      swap a b*((a::L).formPerm*(b::R).formPerm*turns M.first) := by
  have he : (u++((a::L)++z)).formPerm=((a::L)++(b::R)).formPerm := by
    rw [formPerm_append_comm u _ hn,List.append_assoc,hcomp]
  have hh : ((a::L)++(b::R)).Nodup := by
    rw [← hcomp,← List.append_assoc]
    exact (List.perm_append_comm).nodup_iff.mp hn
  rw [he]
  have h := formPerm_cut a b L R (by simpa only [List.cons_append] using hh)
  change (a::(L++b::R)).formPerm*turns M.first=_
  rw [h]
  simp only [mul_assoc]

/-- The first dart following the successful subword and its first dart are
literally in the same original rotation vertex. This is the pole identity. -/
theorem StackMatching.empty_interval_pole {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R) :
    vertex ((u++((a::L)++z)).formPerm*turns M.first) a=
      vertex ((u++((a::L)++z)).formPerm*turns M.first) b := by
  rw [M.empty_interval_rotation u L z a b R hn hcomp]
  let D := M.empty_interval_wedge u L z a b R hn hv hcomp
  have hD := D.shared
  dsimp only [D,StackMatching.empty_interval_wedge,PermutationWedge.data,
    PermutationWedge.inclusionHom,PermutationWedge.flipInclusionHom,
    PermutationWedge.inclusion,PermutationWedge.flipInclusion,sideMk] at hD
  exact hD

end FKCRT.Inventory
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

lemma fullRetract_mk {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (a : α) (ha : a∈S) (d : α) :
    fullRetract hp a ha (vertex p d)=
      (if hd : d∈S then sideMk p S d hd else sideMk p S a ha) := by
  classical
  rfl

lemma fullRetract_inclusion {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (a : α) (ha : a∈S) (x : Side p S) :
    fullRetract hp a ha (fullInclusion p S x)=x := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_left d.property

lemma fullRetract_edge {p e : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (he : ∀ d,e d∈S ↔ d∈S) (a : α) (ha : a∈S)
    {x y : Vertex p} (hxy : (dartGraph e p).Adj x y) :
    (sideGraph e p S he).edist (fullRetract hp a ha x) (fullRetract hp a ha y)≤1 := by
  classical
  have forward (d : α) (hne : vertex p d≠vertex p (e d)) :
      (sideGraph e p S he).edist (fullRetract hp a ha (vertex p d))
        (fullRetract hp a ha (vertex p (e d)))≤1 := by
    rw [fullRetract_mk,fullRetract_mk]
    by_cases hd : d∈S
    · rw [dite_eq_left hd,dite_eq_left ((he d).mpr hd)]
      apply (SimpleGraph.edist_eq_one_iff_adj.mpr ?_).le
      refine ⟨fun h => hne (congrArg (fullInclusion p S) h),Or.inl ⟨d,hd,rfl,rfl⟩⟩
    · rw [dite_eq_right hd,dite_eq_right (fun h => hd ((he d).mp h)),SimpleGraph.edist_self]
      exact zero_le_one
  rcases hxy.2 with ⟨d,rfl,rfl⟩|⟨d,rfl,rfl⟩
  · exact forward d hxy.1
  · rw [SimpleGraph.edist_comm]
    exact forward d hxy.1.symm

/-- Other invariant components, including isolated deleted darts, cannot
shorten distances in a retained component. -/
theorem fullInclusion_edist {p e : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (he : ∀ d,e d∈S ↔ d∈S)
    (x y : Side p S) :
    (dartGraph e p).edist (fullInclusion p S x) (fullInclusion p S y)=
      (sideGraph e p S he).edist x y := by
  apply le_antisymm (GraphWedge.hom_edist_le (fullInclusionHom he) x y)
  obtain ⟨a,ha⟩ := Quotient.exists_rep x
  have h := GraphWedge.retraction_pair_edist_le (sideGraph e p S he)
    (⊥ : SimpleGraph Unit) (dartGraph e p) (fullRetract hp a.val a.property)
    (fun _ => ()) (by
      intro u v huv
      simpa only [SimpleGraph.edist_self,add_zero] using fullRetract_edge hp he a.val a.property huv)
    (fullInclusion p S x) (fullInclusion p S y)
  change (sideGraph e p S he).edist x y≤
    (dartGraph e p).edist (fullInclusion p S x) (fullInclusion p S y)
  simpa only [fullRetract_inclusion,SimpleGraph.edist_self,add_zero] using h

end FKCRT.PermutationWedge
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

lemma turns_filter_on (E : List (α×α)) (hn : (endpoints E).Nodup)
    (p : α→Bool) (hp : ∀ e∈E,p e.1=p e.2) (d : α) (hd : p d=true) :
    turns (E.filter (fun e => p e.1)) d=turns E d := by
  have hs : E.filter (fun e => p e.1)<+E := List.filter_sublist
  have hn' := hn.sublist (hs.flatMap _)
  by_cases hm : d∈endpoints E
  · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hm
    · have hf : e∈E.filter (fun e => p e.1) := List.mem_filter.mpr ⟨he,hd⟩
      exact (turns_pair hn' e hf).1.trans (turns_pair hn e he).1.symm
    · have hf : e∈E.filter (fun e => p e.1) := List.mem_filter.mpr ⟨he,(hp e he).trans hd⟩
      exact (turns_pair hn' e hf).2.trans (turns_pair hn e he).2.symm
  · rw [turns_fixed_of_notMem hm,turns_fixed_of_notMem]
    exact fun h => hm ((hs.flatMap _).subset h)

omit [DecidableEq α] in
lemma perm_preserves_of_fixed {p : Perm α} {S : Set α} (h : ∀ d∈S,p d=d) :
    ∀ d,p d∈S ↔ d∈S := by
  intro d
  constructor
  · intro hd
    have hh : p (p d)=p d := h _ hd
    exact p.injective hh ▸ hd
  · intro hd
    simpa only [h d hd] using hd

end FKCRT.MapCycles
namespace FKCRT.Inventory.StackMatching
open MapCycles
variable {α : Type*} [DecidableEq α] {w : α→TypedLetter} {l : List α}

lemma filter_first (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hpi : p i=true) :
    turns (M.filter hn p hp).first i=turns M.first i := by
  have hE : (endpoints M.first).Nodup :=
    (M.covers.nodup_iff.mpr hn).sublist ((List.sublist_append_left _ _).flatMap _)
  exact turns_filter_on M.first hE p (fun e he => M.pair_mask hn p hp e (List.mem_append_left _ he)) i hpi

lemma filter_mate_on (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hpi : p i=true) :
    (M.filter hn p hp).mate i=M.mate i := by
  change turns (M.first.filter (fun e => p e.1)++M.second.filter (fun e => p e.1)) i=_
  rw [← List.filter_append]
  exact turns_filter_on _ (M.covers.nodup_iff.mpr hn) p (M.pair_mask hn p hp) i hpi

lemma filter_mate_fixed (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hpi : p i=false) :
    (M.filter hn p hp).mate i=i := by
  apply turns_fixed_of_notMem
  intro h
  have hh := (M.filter hn p hp).covers.mem_iff.mp h
  exact Bool.noConfusion (hpi.symm.trans (List.mem_filter.mp hh).2)

lemma filter_first_fixed (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hpi : p i=false) :
    turns (M.filter hn p hp).first i=i := by
  apply turns_fixed_of_notMem
  intro h
  have h' : i∈endpoints ((M.filter hn p hp).first++(M.filter hn p hp).second) := by
    rw [endpoints_append]
    exact List.mem_append_left _ h
  have hf := (M.filter hn p hp).covers.mem_iff.mp h'
  exact Bool.noConfusion (hpi.symm.trans (List.mem_filter.mp hf).2)

end FKCRT.Inventory.StackMatching
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.GraphWedge
lemma iso_edist {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (E : G ≃g H) (x y : α) : H.edist (E x) (E y)=G.edist x y := by
  apply le_antisymm (hom_edist_le E.toHom x y)
  simpa using hom_edist_le E.symm.toHom (E x) (E y)
end FKCRT.GraphWedge
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] [DecidableEq α] in
lemma StackMatching.cast_first {w : α→TypedLetter} {l l' : List α}
    (h : l=l') (M : StackMatching w l) : (h ▸ M).first=M.first := by cases h;rfl

/-- Removing any genuine successful interval preserves *all-edge* distances
between retained darts, not just spanning-tree distances. The resulting
rotation is that of the original ordered word with the interval deleted. -/
theorem StackMatching.delete_interval_distance {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (x y : α) (hx : x∉a::L) (hy : y∉a::L) :
    let D := M.deleteInterval hn hv
    let s := (u++((a::L)++z)).formPerm*turns M.first
    let r := (u++z).formPerm*turns D.first
    (dartGraph M.mate s).edist (vertex s x) (vertex s y)=
      (dartGraph D.mate r).edist (vertex r x) (vertex r y) := by
  let S : Set α := {d | d∈a::L}
  let keep : α→Bool := fun d => decide (d∉a::L)
  have hpres := M.empty_interval_preserves hn hv
  have hk : ∀ d∈u++((a::L)++z),keep (M.mate d)=keep d := by
    intro d _
    simp only [keep,decide_eq_decide]
    exact not_congr (hpres.1 d)
  let D := M.deleteInterval hn hv
  have hDfirst : D.first=(M.filter hn keep hk).first := StackMatching.cast_first _ _
  have hDmate : D.mate=(M.filter hn keep hk).mate := StackMatching.cast_mate _ _
  have hd : (a::L).Disjoint (b::R) := by
    have hh : ((a::L)++(b::R)).Nodup := by
      rw [← hcomp,← List.append_assoc]
      exact List.perm_append_comm.nodup_iff.mp hn
    exact List.disjoint_iff_ne.mpr (List.nodup_append.mp hh).2.2
  have hnu : (u++z).Nodup := by
    exact hn.sublist (List.Sublist.append (List.Sublist.refl u) (List.sublist_append_right _ _))
  have hrotate : (u++z).formPerm=(b::R).formPerm := by
    rw [formPerm_append_comm u z hnu,hcomp]
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  let r := (u++z).formPerm*turns D.first
  have hp : ∀ d,p d∈S ↔ d∈S := by
    intro d
    simp only [p,S,Set.mem_ofPred_eq,mul_apply,List.formPerm_mem_iff_mem,
      formPerm_other_mem_iff hd,hpres.2]
  have hfixed (d : α) (hd' : d∈a::L) : r d=d := by
    have hf : turns D.first d=d := by
      rw [hDfirst]
      exact M.filter_first_fixed hn keep hk d (by simp only [keep,decide_eq_false_iff_not,not_not];exact hd')
    simp only [r,mul_apply,hf,hrotate]
    exact List.formPerm_apply_of_notMem (fun h => List.disjoint_left.mp hd hd' h)
  have hr : ∀ d,r d∈S ↔ d∈S := perm_preserves_of_fixed hfixed
  have hep : ∀ d,D.mate d∈S ↔ d∈S := by
    apply perm_preserves_of_fixed
    intro d hd'
    rw [hDmate]
    exact M.filter_mate_fixed hn keep hk d (by simp only [keep,decide_eq_false_iff_not,not_not];exact hd')
  have hpq (d : α) (hd' : d∈Sᶜ) : p d=r d := by
    have hf : turns D.first d=turns M.first d := by
      rw [hDfirst]
      exact M.filter_first hn keep hk d (by exact decide_eq_true hd')
    have hnd : turns M.first d∉a::L := fun h => hd' ((hpres.2 d).mp h)
    have hnr : (b::R).formPerm (turns M.first d)∉a::L := fun h => hnd ((formPerm_other_mem_iff hd _).mp h)
    simp only [p,r,mul_apply,hf,hrotate,List.formPerm_apply_of_notMem hnr]
  have hef (d : α) (hd' : d∈Sᶜ) : M.mate d=D.mate d := by
    rw [hDmate]
    exact (M.filter_mate_on hn keep hk d (by exact decide_eq_true hd')).symm
  let E := sideGraphCongr (fun d => not_congr (hp d)) (fun d => not_congr (hr d))
    (fun d => not_congr (hpres.1 d)) (fun d => not_congr (hep d)) hpq hef
  dsimp only
  rw [M.empty_interval_rotation u L z a b R hn hcomp]
  change (dartGraph M.mate (swap a b*p)).edist _ _=(dartGraph D.mate r).edist _ _
  calc
    _=(sideGraph M.mate p Sᶜ (fun d => not_congr (hpres.1 d))).edist
      (sideMk p Sᶜ x hx) (sideMk p Sᶜ y hy) :=
        (M.empty_interval_wedge u L z a b R hn hv hcomp).edist_right _ _
    _=(sideGraph D.mate r Sᶜ (fun d => not_congr (hep d))).edist
      (sideMk r Sᶜ x hx) (sideMk r Sᶜ y hy) := (GraphWedge.iso_edist E _ _).symm
    _=_ := (fullInclusion_edist (fun d => not_congr (hr d))
      (fun d => not_congr (hep d)) (sideMk r Sᶜ x hx) (sideMk r Sᶜ y hy)).symm

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Each genuine inserted successful word has precisely one metric gate in
its complement in the original all-edge map. This equality is in the original
graph, not an independently postulated block-tree metric. -/
theorem StackMatching.empty_interval_gate {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (x y : α) (hx : x∈a::L) (hy : y∉a::L) :
    let s := (u++((a::L)++z)).formPerm*turns M.first
    (dartGraph M.mate s).edist (vertex s x) (vertex s y)=
      (dartGraph M.mate s).edist (vertex s x) (vertex s a)+
      (dartGraph M.mate s).edist (vertex s a) (vertex s y) := by
  dsimp only
  rw [M.empty_interval_rotation u L z a b R hn hcomp]
  let S : Set α := {d | d∈a::L}
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  let D := M.empty_interval_wedge u L z a b R hn hv hcomp
  let xx := sideMk p S x hx
  let yy := sideMk p Sᶜ y hy
  change _ = _+_
  have hl := D.edist_left xx D.poleLeft
  have hr := D.edist_right D.poleRight yy
  have hc := D.edist_cross xx yy
  rw [← D.shared] at hr
  dsimp only [D,StackMatching.empty_interval_wedge,PermutationWedge.data,
    PermutationWedge.inclusionHom,PermutationWedge.flipInclusionHom,
    PermutationWedge.inclusion,PermutationWedge.flipInclusion,xx,yy] at hl hr hc
  exact hc.trans (congrArg₂ (·+·) hl.symm hr.symm)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α]

lemma StackMatching.distance_cast {w : α→TypedLetter} {l l' : List α}
    (h : l=l') (M : StackMatching w l) (x y : α) :
    (h ▸ M).distance x y=M.distance x y := by cases h;rfl

/-- Erasing a possibly empty successful interval does not shorten any
retained all-edge distance. Both vertices are kept literal dart vertices. -/
lemma StackMatching.erase_distance [Fintype α] {w : α→TypedLetter}
    (u v z : List α) (M : StackMatching w (u++(v++z)))
    (hn : (u++(v++z)).Nodup) (hv : stackTypedRun (v.map w) []=some [])
    (hc : u++z≠[]) (x y : α) (hx : x∈u++z) (hy : y∈u++z) :
    ∃ D : StackMatching w (u++z),M.distance x y=D.distance x y := by
  cases v with
  | nil =>
    refine ⟨(by simpa only [List.nil_append] using M),?_⟩
    rfl
  | cons a L =>
    have hcomp : z++u≠[] := by
      intro h
      obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp h
      exact hc rfl
    obtain ⟨b,R,hR⟩ := List.exists_cons_of_ne_nil hcomp
    refine ⟨M.deleteInterval hn hv,?_⟩
    exact M.delete_interval_distance u L z a b R hn hv hR x y
      (fun h => List.disjoint_left.mp (complement_disjoint_interval u (a::L) z hn) hx h)
      (fun h => List.disjoint_left.mp (complement_disjoint_interval u (a::L) z hn) hy h)

omit [DecidableEq α] in
lemma core_sublist_insert (l : List (α×List α)) : l.map Prod.fst <+ dartInsert l := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons p l ih =>
    change p.1::l.map Prod.fst <+ p.1::(p.2++dartInsert l)
    exact (ih.trans (List.sublist_append_right _ _)).cons_cons _

/-- Iterated exact preservation of INTERIOR CORE distances under all its
actual successful corner insertions, including trivial leaf intervals.
No stochastic estimate and no replacement metric is assumed. -/
theorem StackMatching.core_distance [Fintype α] {w : α→TypedLetter}
    (p : List α) (l : List (α×List α))
    (M : StackMatching w (p++dartInsert l)) (hn : (p++dartInsert l).Nodup)
    (he : ∀ c∈l,stackTypedRun (c.2.map w) []=some [])
    (hc : p++l.map Prod.fst≠[]) (x y : α)
    (hx : x∈p++l.map Prod.fst) (hy : y∈p++l.map Prod.fst) :
    ∃ D : StackMatching w (p++l.map Prod.fst),M.distance x y=D.distance x y := by
  induction l generalizing p with
  | nil =>
    refine ⟨M,?_⟩
    rfl
  | cons c l ih =>
    let q := p++[c.1]
    have hword : p++dartInsert (c::l)=q++(c.2++dartInsert l) := by
      simp only [q,dartInsert,List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append]
    let M' : StackMatching w (q++(c.2++dartInsert l)) := hword ▸ M
    have hn' : (q++(c.2++dartInsert l)).Nodup := hword ▸ hn
    have he' : stackTypedRun (c.2.map w) []=some [] := he c (by simp)
    have hcore : p++(c::l).map Prod.fst=q++l.map Prod.fst := by
      simp only [q,List.map_cons,List.append_assoc,List.singleton_append]
    have hsub : q++l.map Prod.fst <+ q++dartInsert l :=
      List.Sublist.append (List.Sublist.refl _) (core_sublist_insert _)
    have hx' : x∈q++dartInsert l := hsub.subset (hcore ▸ hx)
    have hy' : y∈q++dartInsert l := hsub.subset (hcore ▸ hy)
    have hnon : q++dartInsert l≠[] := List.ne_nil_of_mem hx'
    obtain ⟨D,hD⟩ := M'.erase_distance q c.2 (dartInsert l) hn' he' hnon x y hx' hy'
    have hnD : (q++dartInsert l).Nodup :=
      hn'.sublist (List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _))
    obtain ⟨E,hE⟩ := ih q D hnD (fun t ht => he t (by simp [ht]))
      (hcore ▸ hc) (hcore ▸ hx) (hcore ▸ hy)
    refine ⟨hcore.symm ▸ E,?_⟩
    rw [StackMatching.distance_cast]
    exact (M.distance_cast hword x y).symm.trans (hD.trans hE)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- All-edge distances inside inserted words are unchanged in the ambient
map, and agree with the actual isolated typed matching of that word. -/
theorem StackMatching.keep_interval_distance {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (x y : α) (hx : x∈a::L) (hy : y∈a::L) :
    M.distance x y=(M.keepInterval hn hv).distance x y := by
  let S : Set α := {d | d∈a::L}
  let keep : α→Bool := fun d => decide (d∈a::L)
  have hpres := M.empty_interval_preserves hn hv
  have hk : ∀ d∈u++((a::L)++z),keep (M.mate d)=keep d := by
    intro d _
    simp only [keep,decide_eq_decide]
    exact hpres.1 d
  let D := M.keepInterval hn hv
  have hDfirst : D.first=(M.filter hn keep hk).first := StackMatching.cast_first _ _
  have hDmate : D.mate=(M.filter hn keep hk).mate := StackMatching.cast_mate _ _
  have hd : (a::L).Disjoint (b::R) := by
    have hh : ((a::L)++(b::R)).Nodup := by
      rw [← hcomp,← List.append_assoc]
      exact List.perm_append_comm.nodup_iff.mp hn
    exact List.disjoint_iff_ne.mpr (List.nodup_append.mp hh).2.2
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  let r := (a::L).formPerm*turns D.first
  have hp : ∀ d,p d∈S ↔ d∈S := by
    intro d
    simp only [p,S,Set.mem_ofPred_eq,mul_apply,List.formPerm_mem_iff_mem,
      formPerm_other_mem_iff hd,hpres.2]
  have hfixed (d : α) (hd' : d∉a::L) : r d=d := by
    have hf : turns D.first d=d := by
      rw [hDfirst]
      exact M.filter_first_fixed hn keep hk d (by exact decide_eq_false hd')
    simp only [r,mul_apply,hf,List.formPerm_apply_of_notMem hd']
  have hrC : ∀ d,r d∈Sᶜ ↔ d∈Sᶜ := perm_preserves_of_fixed hfixed
  have hr : ∀ d,r d∈S ↔ d∈S := by
    intro d
    exact not_iff_not.mp (hrC d)
  have hepC : ∀ d,D.mate d∈Sᶜ ↔ d∈Sᶜ := by
    apply perm_preserves_of_fixed
    intro d hd'
    rw [hDmate]
    exact M.filter_mate_fixed hn keep hk d (by exact decide_eq_false hd')
  have hep : ∀ d,D.mate d∈S ↔ d∈S := fun d => not_iff_not.mp (hepC d)
  have hpq (d : α) (hd' : d∈S) : p d=r d := by
    have hf : turns D.first d=turns M.first d := by
      rw [hDfirst]
      exact M.filter_first hn keep hk d (by exact decide_eq_true hd')
    have hnr : turns M.first d∉b::R := fun h =>
      List.disjoint_left.mp hd ((hpres.2 d).mpr hd') h
    simp only [p,r,mul_apply,hf,List.formPerm_apply_of_notMem hnr]
  have hef (d : α) (hd' : d∈S) : M.mate d=D.mate d := by
    rw [hDmate]
    exact (M.filter_mate_on hn keep hk d (by exact decide_eq_true hd')).symm
  let E := sideGraphCongr hp hr hpres.1 hep hpq hef
  unfold StackMatching.distance
  rw [M.empty_interval_rotation u L z a b R hn hcomp]
  change (dartGraph M.mate (swap a b*p)).edist _ _=(dartGraph D.mate r).edist _ _
  calc
    _=(sideGraph M.mate p S hpres.1).edist (sideMk p S x hx) (sideMk p S y hy) :=
      (M.empty_interval_wedge u L z a b R hn hv hcomp).edist_left _ _
    _=(sideGraph D.mate r S hep).edist (sideMk r S x hx) (sideMk r S y hy) :=
      (GraphWedge.iso_edist E _ _).symm
    _=_ := (fullInclusion_edist hr hep (sideMk r S x hx) (sideMk r S y hy)).symm

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreWords
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

theorem dartGraph_embedding_edist (f : α → β) (hf : Function.Injective f)
    {p e : Perm α} {q a : Perm β}
    (hp : ∀ x,q (f x)=f (p x)) (he : ∀ x,a (f x)=f (e x)) (x y : α) :
    (dartGraph a q).edist (vertex q (f x)) (vertex q (f y))=
      (dartGraph e p).edist (vertex p x) (vertex p y) := by
  calc
    _=(sideGraph a q (Set.range f) (perm_preserves_range f he)).edist
        (sideMk q (Set.range f) (f x) ⟨x,rfl⟩) (sideMk q (Set.range f) (f y) ⟨y,rfl⟩) :=
      fullInclusion_edist (perm_preserves_range f hp) (perm_preserves_range f he) _ _
    _=_ := GraphWedge.iso_edist (dartGraphEmbeddingIso f hf hp he) (vertex p x) (vertex p y)

end FKCRT.PermutationWedge
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma formPerm_map_on (l : List α) (hn : l.Nodup) (f : α → β) (hf : Function.Injective f)
    (x : α) (hx : x∈l) : (l.map f).formPerm (f x)=f (l.formPerm x) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hx
  simp only [List.get_eq_getElem]
  have hmap := List.formPerm_apply_getElem (l.map f) (hn.map hf) i.val (by simp)
  simpa only [List.getElem_map,List.length_map,List.formPerm_apply_getElem l hn] using hmap

lemma StackMatching.unique_first {w : α → TypedLetter} {l : List α}
    (M D : StackMatching w l) (hn : l.Nodup) : turns M.first=turns D.first := by
  obtain ⟨hE,_hF⟩ := typed_matchings_unique w l hn M.first M.second D.first D.second
    M.first_arches M.second_arches D.first_arches D.second_arches M.covers D.covers
    M.first_types M.second_types D.first_types D.second_types
  exact turns_perm hE ((M.covers.nodup_iff.mpr hn).sublist (by
    rw [endpoints_append];exact List.sublist_append_left _ _))

lemma StackMatching.unique_distance {w : α → TypedLetter} {l : List α}
    (M D : StackMatching w l) (hn : l.Nodup) (x y : α) : M.distance x y=D.distance x y := by
  unfold StackMatching.distance
  rw [M.unique_mate D hn,M.unique_first D hn]


lemma turns_map_total (f : α → β) (hf : Function.Injective f) (E : List (α×α))
    (hn : (endpoints E).Nodup) (i : α) :
    turns (E.map (Prod.map f f)) (f i)=f (turns E i) := by
  by_cases hi : i∈endpoints E
  · exact turns_map_on f hf E hn i hi
  · have hfi : f i∉endpoints (E.map (Prod.map f f)) := by
      rw [endpoints_map]
      intro h
      obtain ⟨j,hj,hji⟩ := List.mem_map.mp h
      exact hi (hf hji ▸ hj)
    rw [turns_fixed_of_notMem hi,turns_fixed_of_notMem hfi]

lemma StackMatching.map_first {w : α → TypedLetter} {l : List α}
    (M : StackMatching w l) (hn : l.Nodup) (f : α → β) (hf : Function.Injective f)
    (v : β → TypedLetter) (hv : ∀ i∈l,v (f i)=w i) (i : α) :
    turns (M.map f v hv).first (f i)=f (turns M.first i) := by
  apply turns_map_total f hf _ _ i
  exact (M.covers.nodup_iff.mpr hn).sublist (by
    rw [endpoints_append];exact List.sublist_append_left _ _)

lemma StackMatching.map_distance_of_full [Fintype α] [Fintype β]
    {w : α → TypedLetter} {l : List α}
    (M : StackMatching w l) (hn : l.Nodup) (hl : ∀ i,i∈l)
    (f : α → β) (hf : Function.Injective f) (v : β → TypedLetter)
    (hv : ∀ i∈l,v (f i)=w i) (i j : α) :
    (M.map f v hv).distance (f i) (f j)=M.distance i j := by
  apply dartGraph_embedding_edist f hf
  · intro x
    change (l.map f).formPerm (turns (M.map f v hv).first (f x))=
      f (l.formPerm (turns M.first x))
    rw [M.map_first hn f hf v hv,formPerm_map_on l hn f hf _ (hl _)]
  · intro x
    exact M.map_mate hn f hf v hv x (hl x)

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSingletonClass _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSpace _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreLabel

lemma rootLaw_by_size (P : Parameters) (F : ℕ→ℝ≥0∞) :
    (∑' c : CoreLabel,rootLaw P c*F c.arity)=
      ∑' k : ℕ,(actualOffspring P).law k*F k := by
  change (∑' c : CoreLabel,ENNReal.ofReal (rootMass P c)*F c.arity)=_
  rw [rootMass_by_size]
  have he := Function.Injective.tsum_eq (f := fun k : ℕ => (actualOffspring P).law k*F k)
    (by intro i j hij; dsimp only at hij; omega : Function.Injective (fun k : ℕ => 2*k)) (by
      intro k hk
      by_contra h
      apply hk
      change (actualOffspring P).law k*F k=0
      rw [FKCRT.TreeCoding.CriticalEvenOffspring.law_apply]
      change ENNReal.ofReal (FKCRT.BlockCritical.doubleMass (actualBlockMass P) k)*F k=0
      rw [FKCRT.BlockCritical.doubleMass_outside _ _ h]
      simp)
  rw [← he]
  apply tsum_congr
  intro k
  rw [FKCRT.TreeCoding.CriticalEvenOffspring.law_apply]
  congr 2
  exact (FKCRT.BlockCritical.doubleMass_even (actualBlockMass P) k).symm

end CoreLabel
end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineMoments
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable
namespace CoreLabel

lemma root_fiber (P : Parameters) (k : ℕ) :
    (∑' c : CoreLabel,if c.arity=k then rootLaw P c else 0)=(actualOffspring P).law k := by
  have h := rootLaw_by_size P (fun j => if j=k then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero,tsum_ite_eq] using h

lemma markLaw_apply (P : Parameters) (k : ℕ) (h : ∃ c : CoreLabel,c.arity=k) (c : CoreLabel) :
    markLaw P k c=(if c.arity=k then rootLaw P c else 0)*((actualOffspring P).law k)⁻¹ := by
  rw [markLaw,dite_eq_left h,PMF.filter_apply]
  simp only [Set.indicator_apply,Set.mem_ofPred_eq,root_fiber]

lemma offspring_pos_attainable (P : Parameters) (c : CoreLabel) :
    0<(actualOffspring P).law c.arity := by
  rw [← root_fiber]
  exact (rootLaw_pos P c).trans_le (by
    simpa using ENNReal.le_tsum (f := fun d : CoreLabel => if d.arity=c.arity then rootLaw P d else 0) c)

end CoreLabel
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma measurable_ladderType : Measurable ladderType := by
  have he : Measurable (fun z : (ℕ → ℕ)×ℕ => z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_pi_apply n
  exact (he.comp (measurable_id.prodMk measurable_ladderIndex)).prodMk
    measurable_ladderOvershoot

lemma weakLadderHit_terminal_lt {x : ℕ → ℕ} {n l : ℕ}
    (h : weakLadderHit x n l) : l < x n := by
  have hn : integerSum x n ≤ 0 := by
    cases n with
    | zero => simp
    | succ n => exact (h.1 _ (by omega) le_rfl).le
  have he := h.2
  rw [integerSum_succ] at he
  omega

lemma ladderType_of_hit {x : ℕ → ℕ} {n l : ℕ} (h : weakLadderHit x n l) :
    ladderType x=(x n,l) := by
  simp only [ladderType,ladderIndex_eq_of_hit h,ladderOvershoot_of_hit h]

lemma measurableSet_ladderTypeHit (n k l : ℕ) :
    MeasurableSet {x | weakLadderHit x n l ∧ x n=k} :=
  (measurableSet_weakLadderHit n l).inter
    (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

lemma ladderTypeHit_truncate (n k l : ℕ) :
    (truncateStream (n+1)) ⁻¹' {x | weakLadderHit x n l ∧ x n=k}=
      {x | weakLadderHit x n l ∧ x n=k} := by
  rw [show {x | weakLadderHit x n l ∧ x n=k}=
    {x | weakLadderHit x n l} ∩ {x | x n=k} by rfl,Set.preimage_inter,
    weakLadderHit_truncate]
  congr 1
  ext x
  simp [truncateStream]

lemma ladderTypeHit_endpoint (n k l : ℕ) (hl : l<k) :
    {x | weakLadderHit x n l ∧ x n=k}=
      {x | integerSum x n= -((k-l-1:ℕ):ℤ) ∧ negativeSurvival x n} ∩ {x | x n=k} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,weakLadderHit,integerSum_succ]
  constructor
  · rintro ⟨⟨hs,he⟩,hx⟩
    refine ⟨⟨?_,hs⟩,hx⟩
    omega
  · rintro ⟨⟨he,hs⟩,hx⟩
    refine ⟨⟨hs,?_⟩,hx⟩
    omega

lemma CriticalEvenOffspring.ladderTypeHit_mass (p : CriticalEvenOffspring) (k l : ℕ) :
    (∑' n,p.streamLaw {x | weakLadderHit x n l ∧ x n=k})=
      if l<k then p.law k else 0 := by
  split_ifs with hl
  · simp_rw [ladderTypeHit_endpoint _ _ _ hl,p.prefix_inter_next _ _ _
      (measurableSet_survival_endpoint _ _) (survival_endpoint_truncate _ _)]
    rw [ENNReal.tsum_mul_right,p.negative_potential,one_mul]
  · have he : ∀ n,{x | weakLadderHit x n l ∧ x n=k}=(∅ : Set (ℕ → ℕ)) := by
      intro n
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hh,hk⟩
      exact hl (hk ▸ weakLadderHit_terminal_lt hh)
    simp only [he,measure_empty,tsum_zero]

/-- The exact spine pair has probability p(k) for each of its k possible child slots,
and is independent of the infinite future. -/
lemma CriticalEvenOffspring.ladderType_slice (p : CriticalEvenOffspring)
    (k l : ℕ) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw ({x | ladderType x=(k,l)} ∩ ladderTail ⁻¹' F)=
      (if l<k then p.law k else 0)*p.streamLaw F := by
  have he : ({x | ladderType x=(k,l)} ∩ ladderTail ⁻¹' F : Set (ℕ → ℕ)) =ᵐ[p.streamLaw]
      ⋃ n : ℕ, {x | weakLadderHit x n l ∧ x n=k} ∩ (streamShift (n+1)) ⁻¹' F := by
    filter_upwards [p.ae_weakLadderHit] with x hx
    apply propext
    obtain ⟨n,j,hh⟩ := hx
    constructor
    · rintro ⟨ht,hxF⟩
      change ladderType x=(k,l) at ht
      rw [ladderType_of_hit hh,Prod.mk.injEq] at ht
      obtain ⟨hk,rfl⟩ := ht
      exact Set.mem_iUnion.mpr ⟨n,⟨hh,hk⟩,by
        simpa only [Set.mem_preimage,← ladderTail_of_hit hh] using hxF⟩
    · intro hm
      obtain ⟨m,⟨hm,hk⟩,hxF⟩ := Set.mem_iUnion.mp hm
      refine ⟨by change ladderType x=(k,l); rw [ladderType_of_hit hm,hk],?_⟩
      simpa only [Set.mem_preimage,ladderTail_of_hit hm] using hxF
  rw [measure_congr he,measure_iUnion]
  · simp_rw [p.prefix_inter_shift (n := _)
      (hE := measurableSet_ladderTypeHit _ _ _) (hF := hF)
      (htr := ladderTypeHit_truncate _ _ _)]
    rw [ENNReal.tsum_mul_right,p.ladderTypeHit_mass]
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hn hm
    exact hnm (weakLadderHit_unique hn.1.1 hm.1.1).1
  · intro n
    exact (measurableSet_ladderTypeHit n k l).inter ((measurable_streamShift (n+1)) hF)

instance instIsProbabilityMeasureProdNatSpineLaw (p : CriticalEvenOffspring) : IsProbabilityMeasure p.spineLaw :=
  Measure.isProbabilityMeasure_map (measurable_ladderType.aemeasurable)

lemma CriticalEvenOffspring.spineLaw_singleton (p : CriticalEvenOffspring) (k l : ℕ) :
    p.spineLaw {(k,l)}=if l<k then p.law k else 0 := by
  rw [CriticalEvenOffspring.spineLaw,Measure.map_apply measurable_ladderType (measurableSet_singleton _)]
  change p.streamLaw {x | ladderType x=(k,l)}=_
  simpa
    using p.ladderType_slice k l Set.univ MeasurableSet.univ

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.spine_lintegral_fst (p : CriticalEvenOffspring) :
    (∫⁻ z : ℕ×ℕ,(z.1:ℝ≥0∞) ∂p.spineLaw)=ENNReal.ofReal (p.variance+1) := by
  rw [lintegral_countable',ENNReal.tsum_prod']
  simp_rw [p.spineLaw_singleton,mul_ite,mul_zero]
  have he (k : ℕ) : (∑' l : ℕ,if l<k then (k:ℝ≥0∞)*p.law k else 0)=
      (k:ℝ≥0∞)^2*p.law k := by
    rw [tsum_eq_sum (s := Finset.range k)]
    · simp only [Finset.sum_ite_of_true (fun l hl => Finset.mem_range.mp hl),Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [pow_two,mul_assoc]
    · intro l hl
      simp only [Finset.mem_range] at hl
      simp [hl]
  simp_rw [he]
  rw [p.variance_eq_second_sub_one,sub_add_cancel,
    ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (sq_nonneg _) (p.nonneg k)) p.second]
  apply tsum_congr
  intro k
  simp only [p.law_apply,ENNReal.ofReal_mul (sq_nonneg (k:ℝ)),ENNReal.ofReal_pow (Nat.cast_nonneg k)]
  norm_cast

lemma CriticalEvenOffspring.spine_integrable_fst (p : CriticalEvenOffspring) :
    Integrable (fun z : ℕ×ℕ => (z.1:ℝ)) p.spineLaw := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_natCast,ENNReal.ofReal_natCast]
  rw [p.spine_lintegral_fst]
  exact ENNReal.ofReal_lt_top

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma integerSum_congr_prefix {x y : ℕ → ℕ} {N : ℕ} (h : ∀ k<N,x k=y k) :
    ∀ k≤N,integerSum x k=integerSum y k := by
  intro k hk
  unfold integerSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)]

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma listStream_get {l : List ℕ} {k : ℕ} (hk : k < l.length) : listStream l k=l[k] := by
  simp [listStream,List.getElem?_eq_getElem hk]

lemma integerSum_listStream (l : List ℕ) {k : ℕ} (hk : k ≤ l.length) :
    integerSum (listStream l) k=prefixSum (PlaneTree.incrementWord l) k := by
  induction k with
  | zero => simp [prefixSum]
  | succ k ih =>
    rw [integerSum_succ,ih (by omega),listStream_get (by omega)]
    unfold prefixSum
    rw [List.take_succ_eq_append_getElem (by simpa [PlaneTree.incrementWord] using (show k < l.length by omega)),List.sum_append]
    simp only [PlaneTree.incrementWord,List.getElem_map,List.sum_cons,List.sum_nil,add_zero]
    omega

lemma integerSum_listStream_length (l : List ℕ) :
    integerSum (listStream l) l.length=(PlaneTree.incrementWord l).sum := by
  rw [integerSum_listStream l le_rfl,prefixSum,List.take_of_length_le (by simp [PlaneTree.incrementWord])]

lemma listStream_append_prefix (l r : List ℕ) : ∀ k < l.length,listStream (l++r) k=listStream l k := by
  intro k hk
  simp [listStream,List.getElem?_append_left hk]

lemma prefixSum_reverse_nat (l : List ℕ) {j : ℕ} (_hj : j ≤ l.length) :
    prefixSum (PlaneTree.incrementWord l.reverse) j=
      (PlaneTree.incrementWord l).sum-prefixSum (PlaneTree.incrementWord l) (l.length-j) := by
  rw [PlaneTree.incrementWord,List.map_reverse,prefixSum]
  rw [List.take_reverse,List.sum_reverse]
  change ((PlaneTree.incrementWord l).drop _).sum=_
  rw [sum_drop]
  simp [PlaneTree.incrementWord]

lemma list_reverse_prefix_max (l : List ℕ) (h : ∀ j ≤ l.length,0 ≤ prefixSum (PlaneTree.incrementWord l) j) :
    ∀ j ≤ l.length,integerSum (listStream l.reverse) j ≤ integerSum (listStream l.reverse) l.length := by
  intro j hj
  rw [integerSum_listStream _ (by simpa using hj),prefixSum_reverse_nat l hj,
    integerSum_listStream _ (by simp),prefixSum_reverse_nat l le_rfl]
  simp only [Nat.sub_self,prefixSum,List.take_zero,List.sum_nil,sub_zero]
  exact sub_le_self _ (h _ (by omega))

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma record_count_reverse (x : ℕ → ℕ) (v : ℕ) :
    (weakRecords (integerSum (reverseFirst v x)) v).card=recordHeight (integerSum x) 0 v := by
  rw [recordHeight_dual,Nat.sub_zero]
  congr 1
  exact weakRecords_congr_prefix (fun k hk => integerSum_reverseFirst x v k hk)

lemma reverseFirst_prefix_congr {x y : ℕ → ℕ} {N v : ℕ} (hv : v≤N)
    (h : ∀ k<N,x k=y k) : ∀ k<v,reverseFirst v x k=reverseFirst v y k := by
  intro k hk
  simp only [reverseFirst]
  simp only [reverseIndex,ite_eq_left hk]
  exact h _ (by omega)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma integerSum_list_append (a b : List ℕ) {j : ℕ} (hj : j ≤ b.length) :
    integerSum (listStream (a++b)) (a.length+j)=
      (PlaneTree.incrementWord a).sum+integerSum (listStream b) j := by
  rw [integerSum_listStream _ (by simpa using hj),integerSum_listStream _ hj,
    PlaneTree.incrementWord_append]
  unfold prefixSum
  rw [List.take_append,List.sum_append]
  simp only [PlaneTree.incrementWord,List.length_map,Nat.add_sub_cancel_left]
  rw [List.take_of_length_le (by simp only [List.length_map]; omega)]

lemma reverse_word_strict_negative (l : List ℕ) (h : PlaneTree.SuffixNegative l)
    {j : ℕ} (hj : 0 < j) (hjl : j ≤ l.length) :
    integerSum (listStream l.reverse) j < 0 := by
  rw [integerSum_listStream _ (by simpa using hjl),prefixSum_reverse_nat l hjl]
  have hh := h (l.length-j) (by omega)
  rw [PlaneTree.incrementWord,List.map_drop,sum_drop] at hh
  exact hh

lemma reverseFirst_list_prefix (l : List ℕ) {v : ℕ} (hv : v ≤ l.length) :
    ∀ k < v,reverseFirst v (listStream l) k=listStream (l.take v).reverse k := by
  intro k hk
  simp only [reverseFirst,reverseIndex,ite_eq_left hk]
  rw [listStream_get (by omega),listStream_get (by simp only [List.length_reverse,List.length_take]; omega),List.getElem_reverse]
  simp only [List.length_take,Nat.min_eq_left hv]
  rw [List.getElem_take]

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
namespace PlaneTree

lemma forest_properties (fs : List PlaneTree) :
    (incrementWord (forestDegrees fs)).sum= -(fs.length:ℤ) ∧ SuffixNegative (forestDegrees fs) := by
  induction fs with
  | nil => simp [forestDegrees,incrementWord,SuffixNegative]
  | cons f fs ih =>
    have hp := f.degrees_properties
    change (incrementWord (f.degrees++forestDegrees fs)).sum= -((f::fs).length:ℤ) ∧ _
    constructor
    · rw [incrementWord_append,List.sum_append,hp.1,ih.1]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; omega
    · change SuffixNegative (f.degrees++forestDegrees fs)
      exact suffixNegative_append hp.2 ih.2 (by rw [ih.1]; omega)

end PlaneTree
end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MarkedSpines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma codeSpineSum_one {N : ℕ} (d : Code N) {v : ℕ} (hv : v≤N) :
    codeSpineSum (fun _ => 1) d v=(height d.val v:ℝ) := by
  unfold codeSpineSum recordSpineSum
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 1
  rw [record_count_reverse]
  apply Eq.trans (recordHeight_congr_prefix hv (fun k hk => integerSum_arrayStream_bridge ⟨d.val,d.property.1⟩ hk))
  exact (height_eq_recordHeight d.val hv).symm

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.spine_integrable_dom (p : CriticalEvenOffspring) (b : ℕ×ℕ → ℝ)
    (hb : ∀ z,|b z| ≤ z.1) : Integrable b p.spineLaw := by
  exact p.spine_integrable_fst.mono' (measurable_of_countable b).aestronglyMeasurable
    (ae_of_all _ (fun z =>  by simpa only [Real.norm_eq_abs] using hb z))

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

variable {A : Type*} [MeasurableSpace A]

omit [MeasurableSpace A] in
lemma markedSpineSum_deterministic {N : ℕ} (b : ℕ×ℕ → ℝ) (d : Code N) {v : ℕ}
    (hv : v ≤ N) (a : Fin N → A) :
    markedSpineSum (fun z _ => b z) d hv a=codeSpineSum b d v := by
  unfold markedSpineSum codeSpineSum recordSpineSum
  exact Finset.sum_coe_sort _ (fun t => b (recordTypeAt (reverseFirst v (arrayStream (codeEmbedding N d))) t))

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreMetric
attribute [-instance] _root_.OAI.FKCRT.Inventory.CoreTree.instDecidableEqNode _root_.OAI.FKCRT.Inventory.CoreTree.instFintypeNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace FKCRT.Inventory
open MapCycles PermutationWedge TreeCoding
attribute [local instance] Classical.propDecidable

namespace Core

lemma distance_le (c : Core) (i j : Fin c.val.length) :
    c.graph.dist (vertex c.rotation i) (vertex c.rotation j) ≤ c.val.length := by
  have hc : Fintype.card (PermutationWedge.Vertex c.rotation) ≤ c.val.length := by
    simpa using Fintype.card_le_of_surjective (vertex c.rotation) Quotient.mk_surjective
  by_cases h : c.graph.Reachable (vertex c.rotation i) (vertex c.rotation j)
  · obtain ⟨p,hp,he⟩ := h.exists_path_of_dist
    exact he ▸ (hp.length_lt.le.trans hc)
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable h]
    omega

lemma increment_le (c : Core) (j : Fin c.val.length) : c.increment j ≤ c.val.length :=
  c.distance_le _ _

end Core

lemma coreIncrement_nonneg (z : ℕ×ℕ) (a : CoreLabel) : 0 ≤ coreIncrement z a := by
  cases a <;> simp only [coreIncrement]
  · rfl
  · split_ifs <;> positivity

lemma coreIncrement_bound (z : ℕ×ℕ) (a : CoreLabel) : |coreIncrement z a|≤z.1 := by
  rw [abs_of_nonneg (coreIncrement_nonneg z a)]
  cases a with
  | none => simp [coreIncrement]
  | some c =>
    simp only [coreIncrement]
    split_ifs with h
    · exact_mod_cast (c.increment_le _).trans h.1.le
    · positivity

lemma coreIncrement_integrable (P : Parameters) (z : ℕ×ℕ) :
    Integrable (coreIncrement z) (CoreLabel.markLaw P z.1).toMeasure := by
  apply (integrable_const (z.1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using coreIncrement_bound z a)

lemma coreIncrement_mean_bound (P : Parameters) (z : ℕ×ℕ) :
    |∫ a,coreIncrement z a ∂(CoreLabel.markLaw P z.1).toMeasure|≤z.1 := by
  have h := norm_integral_le_of_norm_le_const (μ := (CoreLabel.markLaw P z.1).toMeasure)
    (f := coreIncrement z) (C := (z.1:ℝ))
    (ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using coreIncrement_bound z a))
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,one_mul,mul_one] using h

lemma metricMean_integrable (P : Parameters) :
    Integrable (fun z => ∫ a,coreIncrement z a ∂(CoreLabel.markLaw P z.1).toMeasure)
      (actualOffspring P).spineLaw :=
  (actualOffspring P).spine_integrable_dom _ (coreIncrement_mean_bound P)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma vertex_perm_apply (p : Perm α) (x : α) : vertex p (p x)=vertex p x :=
  Quotient.sound (SameCycle.symm ⟨1,by simp⟩)

lemma StackMatching.reachable_first {w : α→TypedLetter} {l : List α}
    (M : StackMatching w l) (hn : l.Nodup) (p : Perm α) (x : α) :
    (dartGraph M.mate p).Reachable (vertex p x) (vertex p (turns M.first x)) := by
  by_cases hx : x∈endpoints M.first
  · rw [turns_sublist_apply (M.covers.nodup_iff.mpr hn) (List.sublist_append_left _ _) hx]
    by_cases he : vertex p x=vertex p (M.mate x)
    · rw [he]; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨he,Or.inl ⟨x,rfl,rfl⟩⟩
  · rw [turns_fixed_of_notMem hx]

/-- A genuine successful matching's cyclic tour connects its actual rotation
vertices by original edges; disconnected-distance default values never enter
any isolated-core metric. -/
theorem StackMatching.connected [Fintype α] {w : α→TypedLetter} {l : List α}
    (M : StackMatching w l) (hn : l.Nodup) (hall : ∀ x,x∈l) (hne : l≠[]) :
    (dartGraph M.mate (l.formPerm*turns M.first)).Connected := by
  let p := l.formPerm*turns M.first
  obtain ⟨a,_ha⟩ := List.exists_mem_of_ne_nil l hne
  have hturn : turns M.first*turns M.first=1 :=
    turns_self ((M.covers.nodup_iff.mpr hn).sublist (by
      rw [endpoints_append];exact List.sublist_append_left _ _))
  have htour (x : α) : vertex p (l.formPerm x)=vertex p (turns M.first x) := by
    have he : l.formPerm x=p (turns M.first x) := by
      change l.formPerm x=(l.formPerm*turns M.first*turns M.first) x
      rw [mul_assoc,hturn,mul_one]
    rw [he,vertex_perm_apply]
  refine {preconnected := ?_,nonempty := ⟨vertex p a⟩}
  intro u v
  induction u using Quotient.inductionOn with | h d =>
    induction v using Quotient.inductionOn with | h e =>
      obtain ⟨k,hk⟩ := (sameCycle_formPerm_of_mem hn (hall d) (hall e)).exists_nat_pow_eq
      rw [← hk]
      have hp (j : ℕ) : (dartGraph M.mate p).Reachable
          (vertex p d) (vertex p ((l.formPerm^j) d)) := by
        induction j with
        | zero => exact SimpleGraph.Reachable.refl _
        | succ j ih =>
          rw [pow_succ',mul_apply,htour]
          exact ih.trans (M.reachable_first hn p _)
      exact hp k

namespace Core
lemma graph_connected (c : Core) : c.graph.Connected :=
  c.matching.connected (List.nodup_finRange _) List.mem_finRange (by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_finRange,List.length_nil] at hh
    exact (coreWord_pos _ c.property).ne' hh)

lemma distance_eq_nat (c : Core) (x y : Fin c.val.length) :
    c.matching.distance x y=(c.graph.dist (vertex c.rotation x) (vertex c.rotation y):ℕ∞) := by
  exact (SimpleGraph.Reachable.coe_dist_eq_edist (c.graph_connected.preconnected _ _)).symm
end Core
end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma StackMatching.distance_comm {w : α→TypedLetter} {l : List α}
    (M : StackMatching w l) (x y : α) : M.distance x y=M.distance y x :=
  SimpleGraph.edist_comm

/-- Fix one canonical isolated core matching; deleting all its successful
corner intervals gives its distances simultaneously at every pair of darts. -/
theorem StackMatching.core_distance_eq {w : α→TypedLetter}
    (l : List (α×List α)) (M : StackMatching w (dartInsert l))
    (hn : (dartInsert l).Nodup)
    (he : ∀ c∈l,stackTypedRun (c.2.map w) []=some [])
    (D : StackMatching w (l.map Prod.fst)) (x y : α)
    (hx : x∈l.map Prod.fst) (hy : y∈l.map Prod.fst) :
    M.distance x y=D.distance x y := by
  obtain ⟨E,hE⟩ := M.core_distance [] l hn he (List.ne_nil_of_mem hx) x y hx hy
  exact hE.trans (E.unique_distance D ((core_sublist_insert l).nodup hn) x y)

/-- Exact gate additivity in the actual full graph with the inserted component
replaced only by its genuine isolated matching. -/
theorem StackMatching.interval_distance_sum {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (D : StackMatching w (a::L)) (x y : α) (hx : x∈a::L) (hy : y∉a::L) :
    M.distance y x=M.distance y b+D.distance a x := by
  have hp := M.empty_interval_pole u L z a b R hn hv hcomp
  have hg := M.empty_interval_gate u L z a b R hn hv hcomp x y hx hy
  change M.distance x y=M.distance x a+M.distance a y at hg
  rw [M.distance_comm x y,M.distance_comm x a,M.distance_comm a y,add_comm] at hg
  have hpb : M.distance y a=M.distance y b := by
    dsimp only [StackMatching.distance]
    rw [hp]
  rw [hpb] at hg
  have hi := M.keep_interval_distance u L z a b R hn hv hcomp a x (by simp) hx
  have hD := (M.keepInterval hn hv).unique_distance D hn.of_append_right.of_append_left a x
  exact hg.trans (congrArg (fun d => M.distance y b+d) (hi.trans hD))

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open MapCycles PermutationWedge TreeCoding
attribute [local instance] Classical.propDecidable

lemma oneLink_rotation : oneLinkCore.rotation=1 := by
  unfold Core.rotation
  rw [oneLinkCore.matching.unique_first oneLinkMatching (List.nodup_finRange _)]
  change (List.finRange 2).formPerm*turns [(0,1)]= (1 : Perm (Fin 2))
  decide

lemma oneLink_mate : oneLinkCore.matching.mate 0=1 := by
  rw [oneLinkCore.matching.unique_mate oneLinkMatching (List.nodup_finRange _)]
  rfl

lemma oneLink_increment : oneLinkCore.increment 0=1 := by
  apply SimpleGraph.dist_eq_one_iff_adj.mpr
  change (vertex oneLinkCore.rotation oneLinkCore.entry ≠
    vertex oneLinkCore.rotation ((List.finRange 2).formPerm 0)) ∧ _
  have hc : (List.finRange 2).formPerm 0=(1:Fin 2) := rfl
  have he : oneLinkCore.entry=(0:Fin 2) := rfl
  rw [hc,he]
  refine ⟨?_,Or.inl ⟨0,rfl,?_⟩⟩
  · intro h
    have hh := Quotient.exact h
    change oneLinkCore.rotation.SameCycle 0 1 at hh
    rw [oneLink_rotation,sameCycle_one] at hh
    exact (by decide : (0:Fin 2)≠1) hh
  · rw [oneLink_mate]
    exact congrArg (vertex oneLinkCore.rotation) hc.symm

lemma coreIncrement_oneLink : coreIncrement (2,1) (some oneLinkCore)=1 := by
  rw [coreIncrement,dite_eq_left (by decide)]
  change (oneLinkCore.increment 0 : ℝ)=1
  rw [oneLink_increment]
  norm_num

lemma coreIncrement_mean_pos (P : Parameters) :
    0 < ∫ a,coreIncrement (2,1) a ∂(CoreLabel.markLaw P 2).toMeasure := by
  apply (integral_pos_iff_support_of_nonneg (coreIncrement_nonneg (2,1))
    (coreIncrement_integrable P (2,1))).mpr
  have hs : {some oneLinkCore} ⊆ Function.support (coreIncrement (2,1)) := by
    intro a ha
    rcases ha with rfl
    change coreIncrement (2,1) (some oneLinkCore)≠0
    rw [coreIncrement_oneLink]
    exact one_ne_zero
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    CoreLabel.markLaw_apply P 2 ⟨some oneLinkCore,rfl⟩]
  simp only [CoreLabel.arity,oneLinkCore,List.length_cons,List.length_nil,zero_add,
    Nat.reduceAdd,ite_true]
  apply ENNReal.mul_pos
  · exact (CoreLabel.rootLaw_pos P _).ne'
  · exact ENNReal.inv_ne_zero.mpr (PMF.apply_ne_top _ _)

/-- Strict positivity follows from the positive-mass one-link block and its
nontrivial corner, not from an assumed metric scaling constant. -/
theorem metricMean_pos (P : Parameters) : 0 < metricMean P := by
  apply (integral_pos_iff_support_of_nonneg
    (fun z => integral_nonneg (coreIncrement_nonneg z)) (metricMean_integrable P)).mpr
  have hs : {(2,1)} ⊆ Function.support
      (fun z => ∫ a,coreIncrement z a ∂(CoreLabel.markLaw P z.1).toMeasure) := by
    intro z hz
    rcases hz with rfl
    exact (coreIncrement_mean_pos P).ne'
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [CriticalEvenOffspring.spineLaw_singleton,ite_eq_left (by decide : (1:ℕ)<2)]
  exact CoreLabel.offspring_pos_attainable P (some oneLinkCore)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma childDart_injective {c : Core} (ts : Fin c.val.length→ CoreTree) (i : Fin c.val.length) :
    Function.Injective (childDart ts i) := by
  intro x y h
  exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2

lemma coreDart_injective {c : Core} (ts : Fin c.val.length→ CoreTree) :
    Function.Injective (coreDart ts) := Sum.inl_injective

lemma darts_branch (c : Core) (ts : Fin c.val.length→ CoreTree) :
    (branch c ts).darts=dartInsert (dartCorners c ts) := by
  simp only [darts,dartInsert,dartCorners,List.flatMap_map]

lemma darts_mem (t : CoreTree) (d : t.Dart) : d∈t.darts := by
  induction t with
  | leaf => exact d.elim
  | branch c ts ih =>
    cases d with
    | inl i => exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_cons_self⟩
    | inr d =>
      obtain ⟨i,d⟩ := d
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,by
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d,ih i d,rfl⟩)⟩

lemma darts_nodup (t : CoreTree) : t.darts.Nodup := by
  induction t with
  | leaf => exact List.nodup_nil
  | branch c ts ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro i _
      refine List.nodup_cons.mpr ⟨?_,(ih i).map (childDart_injective ts i)⟩
      intro h
      obtain ⟨x,_,hx⟩ := List.mem_map.mp h
      cases hx
    · refine (List.nodup_finRange c.val.length).imp (fun {i j} hij => ?_)
      change List.Disjoint (coreDart ts i::_) (coreDart ts j::_)
      intro x hx hy
      rcases List.mem_cons.mp hx with hx|hx
      · subst x
        rcases List.mem_cons.mp hy with h|h
        · exact hij (Sum.inl.inj h)
        · obtain ⟨e,_,h⟩ := List.mem_map.mp h
          cases h
      · obtain ⟨d,_,rfl⟩ := List.mem_map.mp hx
        rcases List.mem_cons.mp hy with h|h
        · cases h
        · obtain ⟨e,_,h⟩ := List.mem_map.mp h
          exact hij (congrArg Sigma.fst (Sum.inr.inj h)).symm

lemma child_empty (c : Core) (ts : Fin c.val.length→ CoreTree)
    (p : (branch c ts).Dart × List (branch c ts).Dart) (hp : p∈dartCorners c ts) :
    stackTypedRun (p.2.map (branch c ts).dartLabel) []=some [] := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  simpa only [List.map_map,dartLabel,childDart,Function.comp_def,darts_word] using (ts i).word_empty

lemma core_darts (c : Core) (ts : Fin c.val.length→ CoreTree) :
    (dartCorners c ts).map Prod.fst=(List.finRange _).map (coreDart ts) := by
  simp [dartCorners,List.map_map,Function.comp_def]

/-- Exact original graph metric on core darts before/after all substitutions. -/
theorem core_distance (c : Core) (ts : Fin c.val.length→ CoreTree)
    (i j : Fin c.val.length) :
    (branch c ts).matching.distance (coreDart ts i) (coreDart ts j)=c.matching.distance i j := by
  let Q := c.matching.map (coreDart ts) (branch c ts).dartLabel (fun _ _ => rfl)
  let D : StackMatching (branch c ts).dartLabel ((dartCorners c ts).map Prod.fst) :=
    (core_darts c ts).symm ▸ Q
  let M : StackMatching (branch c ts).dartLabel (dartInsert (dartCorners c ts)) :=
    darts_branch c ts ▸ (branch c ts).matching
  have h := M.core_distance_eq (dartCorners c ts) (darts_branch c ts ▸ (branch c ts).darts_nodup)
    (child_empty c ts) D (coreDart ts i) (coreDart ts j)
    (by rw [core_darts];exact List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
    (by rw [core_darts];exact List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩)
  have he := (branch c ts).matching.distance_cast (darts_branch c ts) (coreDart ts i) (coreDart ts j)
  have hD := Q.distance_cast (core_darts c ts).symm (coreDart ts i) (coreDart ts j)
  change D.distance _ _=Q.distance _ _ at hD
  change M.distance _ _=(branch c ts).matching.distance _ _ at he
  rw [he,hD] at h
  exact h.trans (c.matching.map_distance_of_full (List.nodup_finRange _) List.mem_finRange
    (coreDart ts) (coreDart_injective ts) (branch c ts).dartLabel (fun _ _ => rfl) i j)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma dartInsert_append (A B : List (α×List α)) :
    dartInsert (A++B)=dartInsert A++dartInsert B :=
  List.flatMap_append

/-- The entry dart following a child interval is exactly the next isolated
core dart in cyclic order, including the last-slot wrap to the root. -/
theorem corner_complement_head (A B : List (α×List α)) (d : α) (v : List α)
    (hn : (dartInsert (A++(d,v)::B)).Nodup) :
    ∃ R,dartInsert B++(dartInsert A++[d])=
      ((A++(d,v)::B).map Prod.fst).formPerm d::R := by
  let L := (A++(d,v)::B).map Prod.fst
  have hcn : L.Nodup := (core_sublist_insert _).nodup hn
  have hrot : L.formPerm=(d::((B++A).map Prod.fst)).formPerm := by
    dsimp [L]
    rw [List.map_append,List.map_cons]
    rw [formPerm_append_comm _ _ (by simpa [L] using hcn)]
    simp only [List.cons_append,List.map_append]
  rw [← List.append_assoc,← dartInsert_append,hrot]
  cases hba : B++A with
  | nil =>
    refine ⟨[],?_⟩
    simp [dartInsert]
  | cons e es =>
    have hn' : (d::e.1::es.map Prod.fst).Nodup := by
      have hh := (List.nodup_append.mp (show (A.map Prod.fst++d::B.map Prod.fst).Nodup by
        simpa [L] using hcn))
      have hh' : ((d::B.map Prod.fst)++A.map Prod.fst).Nodup :=
        List.nodup_append.mpr ⟨hh.2.1,hh.1,fun a ha b hb => (hh.2.2 b hb a ha).symm⟩
      simpa only [List.cons_append,← List.map_append,hba,List.map_cons] using hh'
    refine ⟨e.2++dartInsert es++[d],?_⟩
    rw [List.map_cons,List.formPerm_apply_head _ _ _ hn']
    simp only [dartInsert,List.flatMap_cons,List.cons_append,List.append_assoc]

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma core_next (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    ((dartCorners c ts).map Prod.fst).formPerm (coreDart ts i)=coreDart ts (nextSlot c i) := by
  rw [core_darts]
  exact formPerm_map_on _ (List.nodup_finRange _) (coreDart ts) (coreDart_injective ts) _ (List.mem_finRange _)

/-- Exact all-edge ancestor step for arbitrary literal child darts. -/
theorem child_distance_sum (c : Core) (ts : Fin c.val.length → CoreTree)
    (i r : Fin c.val.length) (a x : (ts i).Dart) (L : List (ts i).Dart)
    (hhead : (ts i).darts=a::L) :
    (branch c ts).matching.distance (coreDart ts r) (childDart ts i x)=
      c.matching.distance r (nextSlot c i)+(ts i).matching.distance a x := by
  let v := (ts i).darts.map (childDart ts i)
  have hm : (coreDart ts i,v)∈dartCorners c ts := List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩
  obtain ⟨A,B,hAB⟩ := List.mem_iff_append.mp hm
  have hv : v=childDart ts i a::L.map (childDart ts i) := by simp only [v,hhead,List.map_cons]
  let u := dartInsert A++[coreDart ts i]
  let z := dartInsert B
  have hw : (branch c ts).darts=u++((childDart ts i a::L.map (childDart ts i))++z) := by
    rw [darts_branch,hAB]
    simp only [dartInsert,List.flatMap_append,List.flatMap_cons,List.cons_append,hv,u,z,List.append_assoc,
      List.nil_append]
  let M : StackMatching (branch c ts).dartLabel (u++((childDart ts i a::L.map (childDart ts i))++z)) :=
    hw ▸ (branch c ts).matching
  have hn := hw ▸ (branch c ts).darts_nodup
  have he : stackTypedRun ((childDart ts i a::L.map (childDart ts i)).map (branch c ts).dartLabel) []=some [] := by
    rw [← hv]
    exact child_empty c ts _ hm
  obtain ⟨R,hR⟩ := corner_complement_head A B (coreDart ts i) v
    (by rw [← hAB,← darts_branch];exact (branch c ts).darts_nodup)
  rw [← hAB,core_next] at hR
  let Q₀ := (ts i).matching.map (childDart ts i) (branch c ts).dartLabel (fun _ _ => rfl)
  let Q : StackMatching (branch c ts).dartLabel
      (childDart ts i a::L.map (childDart ts i)) := hv ▸ Q₀
  have hx : childDart ts i x∈childDart ts i a::L.map (childDart ts i) := by
    rw [← hv]
    exact List.mem_map.mpr ⟨x,(ts i).darts_mem x,rfl⟩
  have hr : coreDart ts r∉childDart ts i a::L.map (childDart ts i) := by
    rw [← hv]
    intro h
    obtain ⟨y,_,hy⟩ := List.mem_map.mp h
    cases hy
  have hg := M.interval_distance_sum u (L.map (childDart ts i)) z (childDart ts i a)
    (coreDart ts (nextSlot c i)) R hn he hR Q (childDart ts i x) (coreDart ts r) hx hr
  have hp (x y : (branch c ts).Dart) : M.distance x y=(branch c ts).matching.distance x y :=
    (branch c ts).matching.distance_cast hw x y
  have hq : Q.distance (childDart ts i a) (childDart ts i x)=
      (ts i).matching.distance a x := by
    rw [show Q.distance _ _=Q₀.distance (childDart ts i a) (childDart ts i x) from
      Q₀.distance_cast hv _ _]
    exact (ts i).matching.map_distance_of_full (ts i).darts_nodup (ts i).darts_mem
      (childDart ts i) (childDart_injective ts i) (branch c ts).dartLabel (fun _ _ => rfl) a x
  rw [hp,hp,hq,core_distance] at hg
  exact hg

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma pole_some (c : Core) (ts : Fin c.val.length → CoreTree) (v : (branch c ts).Node) :
    ∃ d,(branch c ts).pole v=some d := by
  cases v <;> exact ⟨_,rfl⟩

lemma darts_head (c : Core) (ts : Fin c.val.length → CoreTree) :
    ∃ L,(branch c ts).darts=coreDart ts c.entry::L := by
  have h := List.drop_eq_getElem_cons (l := List.finRange c.val.length) (i := 0)
    (by simpa using coreWord_pos c.val c.property)
  have he : (List.finRange c.val.length)[0]'(by simpa using coreWord_pos c.val c.property)=c.entry := by
    apply Fin.ext
    simp [Core.entry]
  rw [List.drop_zero,he] at h
  rw [darts,h,List.flatMap_cons]
  exact ⟨_,rfl⟩

lemma pole_none_of_leaf (t : CoreTree) (h : t=leaf) (v : t.Node) : t.pole v=none := by
  subst t
  rfl

lemma route_zero_of_leaf (t : CoreTree) (h : t=leaf) (v : t.Node) : t.routeLength v=0 := by
  subst t
  rfl

lemma pole_some_of_ne_leaf (t : CoreTree) (h : t≠leaf) (v : t.Node) : ∃ d,t.pole v=some d := by
  cases t with
  | leaf => exact False.elim (h rfl)
  | branch c ts => exact pole_some c ts v

/-- The route length sums the genuine isolated-core graph distances along
the strict ancestor chain. It equals the original full-map graph distance
from the root pole, rather than a postulated replacement metric. -/
theorem distance_root_pole (t : CoreTree) (v : t.Node) (a b : t.Dart)
    (ha : t.rootDart=some a) (hb : t.pole v=some b) :
    t.matching.distance a b=(t.routeLength v : ℕ∞) := by
  induction t with
  | leaf => cases a
  | branch c ts ih =>
    have ha' : coreDart ts c.entry=a := Option.some.inj ha
    subst a
    cases v with
    | inl u =>
      have hb' : coreDart ts c.entry=b := Option.some.inj hb
      subst b
      exact SimpleGraph.edist_self
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases ht : ts i with
      | leaf =>
        have hn := pole_none_of_leaf (ts i) ht v
        have hr := route_zero_of_leaf (ts i) ht v
        have hb' : coreDart ts (nextSlot c i)=b := by simpa only [pole,hn,Option.map_none,Option.getD_none,Option.some.injEq] using hb
        subst b
        rw [core_distance,Core.distance_eq_nat]
        change (c.increment i:ℕ∞)=((c.increment i+(ts i).routeLength v:ℕ):ℕ∞)
        rw [hr,Nat.add_zero]
      | branch d us =>
        have hs := pole_some_of_ne_leaf (ts i) (by rw [ht];exact CoreTree.noConfusion) v
        obtain ⟨b',hb'⟩ := hs
        have hsroot : ∃ a' L,(ts i).rootDart=some a' ∧ (ts i).darts=a'::L := by
          rw [ht]
          obtain ⟨L,hL⟩ := darts_head d us
          exact ⟨_,L,rfl,hL⟩
        obtain ⟨a',L,ha',hL⟩ := hsroot
        have hbb : childDart ts i b'=b := by
          simpa only [pole,hb',Option.map_some,Option.getD_some,Option.some.injEq] using hb
        subst b
        rw [child_distance_sum c ts i c.entry a' b' L hL,ih i v a' b' ha' hb',Core.distance_eq_nat]
        change (c.increment i:ℕ∞)+((ts i).routeLength v:ℕ∞)=
          ((c.increment i+(ts i).routeLength v:ℕ):ℕ∞)
        exact_mod_cast (rfl : c.increment i+(ts i).routeLength v=c.increment i+(ts i).routeLength v)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma child_interval (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (a : (ts i).Dart) (L : List (ts i).Dart)
    (hhead : (ts i).darts=a::L) :
    ∃ u z R,(branch c ts).darts=u++((childDart ts i a::L.map (childDart ts i))++z) ∧
      z++u=coreDart ts (nextSlot c i)::R := by
  let v := (ts i).darts.map (childDart ts i)
  have hm : (coreDart ts i,v)∈dartCorners c ts := List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩
  obtain ⟨A,B,hAB⟩ := List.mem_iff_append.mp hm
  have hv : v=childDart ts i a::L.map (childDart ts i) := by simp only [v,hhead,List.map_cons]
  obtain ⟨R,hR⟩ := corner_complement_head A B (coreDart ts i) v
    (by rw [← hAB,← darts_branch];exact (branch c ts).darts_nodup)
  rw [← hAB,core_next] at hR
  refine ⟨dartInsert A++[coreDart ts i],dartInsert B,R,?_,hR⟩
  rw [darts_branch,hAB]
  simp only [dartInsert,List.flatMap_append,List.flatMap_cons,List.cons_append,hv,List.append_assoc,
    List.nil_append]

/-- Isometry of every nonempty inserted child, in its original all-edge
metric. No root-distance-only surrogate is used. -/
theorem child_internal_distance (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (a x y : (ts i).Dart) (L : List (ts i).Dart)
    (hhead : (ts i).darts=a::L) :
    (branch c ts).matching.distance (childDart ts i x) (childDart ts i y)=
      (ts i).matching.distance x y := by
  obtain ⟨u,z,R,hw,hR⟩ := child_interval c ts i a L hhead
  let M : StackMatching (branch c ts).dartLabel (u++((childDart ts i a::L.map (childDart ts i))++z)) :=
    hw ▸ (branch c ts).matching
  have hn := hw ▸ (branch c ts).darts_nodup
  have hv : (ts i).darts.map (childDart ts i)=childDart ts i a::L.map (childDart ts i) := by
    rw [hhead,List.map_cons]
  have he : stackTypedRun ((childDart ts i a::L.map (childDart ts i)).map (branch c ts).dartLabel) []=some [] := by
    rw [← hv,List.map_map]
    change stackTypedRun ((ts i).darts.map (ts i).dartLabel) []=some []
    rw [darts_word];exact (ts i).word_empty
  let Q₀ := (ts i).matching.map (childDart ts i) (branch c ts).dartLabel (fun _ _ => rfl)
  let Q : StackMatching (branch c ts).dartLabel
      (childDart ts i a::L.map (childDart ts i)) := hv ▸ Q₀
  have hm (d : (ts i).Dart) : childDart ts i d∈childDart ts i a::L.map (childDart ts i) := by
    rw [← hv];exact List.mem_map.mpr ⟨d,(ts i).darts_mem d,rfl⟩
  have hg := M.keep_interval_distance u (L.map (childDart ts i)) z (childDart ts i a)
    (coreDart ts (nextSlot c i)) R hn he hR (childDart ts i x) (childDart ts i y) (hm x) (hm y)
  have hu := (M.keepInterval hn he).unique_distance Q hn.of_append_right.of_append_left
    (childDart ts i x) (childDart ts i y)
  rw [((branch c ts).matching.distance_cast hw _ _)] at hg
  rw [hu,Q₀.distance_cast hv _ _] at hg
  exact hg.trans ((ts i).matching.map_distance_of_full (ts i).darts_nodup (ts i).darts_mem
      (childDart ts i) (childDart_injective ts i) (branch c ts).dartLabel (fun _ _ => rfl) x y)

lemma child_gate_distance (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (a x : (ts i).Dart) (L : List (ts i).Dart)
    (hhead : (ts i).darts=a::L) (y : (branch c ts).Dart)
    (hy : ∀ d : (ts i).Dart,childDart ts i d≠y) :
    (branch c ts).matching.distance (childDart ts i x) y=
      (ts i).matching.distance x a+
        (branch c ts).matching.distance (coreDart ts (nextSlot c i)) y := by
  obtain ⟨u,z,R,hw,hR⟩ := child_interval c ts i a L hhead
  let M : StackMatching (branch c ts).dartLabel (u++((childDart ts i a::L.map (childDart ts i))++z)) :=
    hw ▸ (branch c ts).matching
  have hn := hw ▸ (branch c ts).darts_nodup
  have hv : (ts i).darts.map (childDart ts i)=childDart ts i a::L.map (childDart ts i) := by
    rw [hhead,List.map_cons]
  have he : stackTypedRun ((childDart ts i a::L.map (childDart ts i)).map (branch c ts).dartLabel) []=some [] := by
    rw [← hv,List.map_map]
    change stackTypedRun ((ts i).darts.map (ts i).dartLabel) []=some []
    rw [darts_word];exact (ts i).word_empty
  have hx : childDart ts i x∈childDart ts i a::L.map (childDart ts i) := by
    rw [← hv];exact List.mem_map.mpr ⟨x,(ts i).darts_mem x,rfl⟩
  have hyn : y∉childDart ts i a::L.map (childDart ts i) := by
    rw [← hv];rintro h
    obtain ⟨d,_,hd⟩ := List.mem_map.mp h
    exact hy d hd
  have hg := M.empty_interval_gate u (L.map (childDart ts i)) z (childDart ts i a)
    (coreDart ts (nextSlot c i)) R hn he hR (childDart ts i x) y hx hyn
  have hp := M.empty_interval_pole u (L.map (childDart ts i)) z (childDart ts i a)
    (coreDart ts (nextSlot c i)) R hn he hR
  change M.distance (childDart ts i x) y=M.distance (childDart ts i x) (childDart ts i a)+
    M.distance (childDart ts i a) y at hg
  have hp' : M.distance (childDart ts i a) y=M.distance (coreDart ts (nextSlot c i)) y := by
    dsimp only [StackMatching.distance]
    rw [hp]
  rw [hp'] at hg
  have hh (r s : (branch c ts).Dart) : M.distance r s=(branch c ts).matching.distance r s :=
    (branch c ts).matching.distance_cast hw r s
  rw [hh,hh,hh,child_internal_distance c ts i a x a L hhead] at hg
  exact hg

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma root_and_head (t : CoreTree) (h : t≠leaf) :
    ∃ a L,t.rootDart=some a ∧ t.darts=a::L := by
  cases t with
  | leaf => exact False.elim (h rfl)
  | branch c ts =>
    obtain ⟨L,hL⟩ := darts_head c ts
    exact ⟨_,L,rfl,hL⟩

lemma core_to_childPole (c : Core) (ts : Fin c.val.length → CoreTree)
    (i r : Fin c.val.length) (v : (ts i).Node) :
    (branch c ts).matching.distance (coreDart ts r) (childPole c ts i v)=
      c.matching.distance r (nextSlot c i)+((ts i).routeLength v:ℕ∞) := by
  by_cases ht : ts i=leaf
  · have hp := pole_none_of_leaf (ts i) ht v
    have hr := route_zero_of_leaf (ts i) ht v
    simp only [childPole,hp,Option.map_none,Option.getD_none,hr,Nat.cast_zero,add_zero]
    exact core_distance c ts r (nextSlot c i)
  · obtain ⟨b,hb⟩ := pole_some_of_ne_leaf (ts i) ht v
    obtain ⟨a,L,ha,hL⟩ := root_and_head (ts i) ht
    simp only [childPole,hb,Option.map_some,Option.getD_some]
    rw [child_distance_sum c ts i r a b L hL,distance_root_pole (ts i) v a b ha hb]

lemma childPole_not_child (c : Core) (ts : Fin c.val.length → CoreTree)
    (i j : Fin c.val.length) (hij : i≠j) (v : (ts j).Node) (d : (ts i).Dart) :
    childDart ts i d≠childPole c ts j v := by
  unfold childPole
  cases hp : (ts j).pole v with
  | none => simp only [Option.map_none,Option.getD_none];intro h;cases h
  | some b =>
    simp only [Option.map_some,Option.getD_some]
    intro h
    exact hij (congrArg Sigma.fst (Sum.inr.inj h))

/-- The exact three-piece route between distinct child components. -/
theorem between_childPoles (c : Core) (ts : Fin c.val.length → CoreTree)
    (i j : Fin c.val.length) (hij : i≠j) (v : (ts i).Node) (w : (ts j).Node) :
    (branch c ts).matching.distance (childPole c ts i v) (childPole c ts j w)=
      ((ts i).routeLength v:ℕ∞)+c.matching.distance (nextSlot c i) (nextSlot c j)+
        ((ts j).routeLength w:ℕ∞) := by
  by_cases ht : ts i=leaf
  · have hp := pole_none_of_leaf (ts i) ht v
    have hr := route_zero_of_leaf (ts i) ht v
    simp only [childPole,hp,Option.map_none,Option.getD_none,hr,Nat.cast_zero,zero_add]
    exact core_to_childPole c ts j (nextSlot c i) w
  · obtain ⟨b,hb⟩ := pole_some_of_ne_leaf (ts i) ht v
    obtain ⟨a,L,ha,hL⟩ := root_and_head (ts i) ht
    have he : childPole c ts i v=childDart ts i b := by simp only [childPole,hb,Option.map_some,Option.getD_some]
    rw [he,child_gate_distance c ts i a b L hL _ (childPole_not_child c ts i j hij w)]
    rw [(ts i).matching.distance_comm b a,distance_root_pole (ts i) v a b ha hb,
      core_to_childPole c ts j (nextSlot c i) w,add_assoc]

lemma within_childPoles (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (v w : (ts i).Node) (a b : (ts i).Dart)
    (ha : (ts i).pole v=some a) (hb : (ts i).pole w=some b) :
    (branch c ts).matching.distance (childPole c ts i v) (childPole c ts i w)=
      (ts i).matching.distance a b := by
  have hn : ts i≠leaf := by intro h;rw [pole_none_of_leaf (ts i) h v] at ha;cases ha
  obtain ⟨r,L,_,hL⟩ := root_and_head (ts i) hn
  simp only [childPole,ha,hb,Option.map_some,Option.getD_some]
  exact child_internal_distance c ts i r a b L hL

lemma distance_eq_nat (t : CoreTree) (a b : t.Dart) :
    t.matching.distance a b=
      ((dartGraph t.matching.mate (t.darts.formPerm*turns t.matching.first)).dist
        (vertex _ a) (vertex _ b):ℕ∞) := by
  have hn : t.darts≠[] := List.ne_nil_of_mem (t.darts_mem a)
  have hc := t.matching.connected t.darts_nodup t.darts_mem hn
  exact (SimpleGraph.Reachable.coe_dist_eq_edist (hc.preconnected _ _)).symm

lemma realDistance_comm (t : CoreTree) (a b : t.Dart) : t.realDistance a b=t.realDistance b a := by
  dsimp [realDistance]
  rw [SimpleGraph.dist_comm]

lemma realDistance_self (t : CoreTree) (a : t.Dart) : t.realDistance a a=0 := by
  simp [realDistance]

lemma real_root_distance (t : CoreTree) (v : t.Node) (a b : t.Dart)
    (ha : t.rootDart=some a) (hb : t.pole v=some b) :
    t.realDistance a b=t.routeLength v := by
  have h := distance_root_pole t v a b ha hb
  rw [distance_eq_nat] at h
  dsimp only [realDistance]
  exact_mod_cast h

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

namespace Core

lemma realDistance_nonneg (c : Core) (i j : Fin c.val.length) : 0 ≤ c.realDistance i j := Nat.cast_nonneg _

lemma corner_distance_le (c : Core) (i j : Fin c.val.length) :
    c.realDistance (CoreTree.nextSlot c i) (CoreTree.nextSlot c j)≤(c.increment i:ℝ)+c.increment j := by
  have h := c.graph_connected.dist_triangle (u := vertex c.rotation (CoreTree.nextSlot c i))
    (v := vertex c.rotation c.entry) (w := vertex c.rotation (CoreTree.nextSlot c j))
  rw [SimpleGraph.dist_comm (u := vertex c.rotation (CoreTree.nextSlot c i)) (v := vertex c.rotation c.entry)] at h
  dsimp only [realDistance,increment,CoreTree.nextSlot]
  exact_mod_cast h

end Core
namespace CoreTree

lemma maxDegree_core (c : Core) (ts : Fin c.val.length → CoreTree) :
    c.val.length≤(branch c ts).maxDegree := le_max_left _ _

lemma maxDegree_child (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    (ts i).maxDegree≤(branch c ts).maxDegree :=
  (Finset.le_sup (f := fun i => (ts i).maxDegree) (Finset.mem_univ i)).trans (le_max_right _ _)

lemma real_between_childPoles (c : Core) (ts : Fin c.val.length → CoreTree)
    (i j : Fin c.val.length) (hij : i≠j) (v : (ts i).Node) (w : (ts j).Node) :
    (branch c ts).realDistance (childPole c ts i v) (childPole c ts j w)=
      ((ts i).routeLength v:ℝ)+c.realDistance (nextSlot c i) (nextSlot c j)+
        ((ts j).routeLength w:ℝ) := by
  have h := between_childPoles c ts i j hij v w
  rw [distance_eq_nat,Core.distance_eq_nat] at h
  dsimp only [realDistance,Core.realDistance]
  exact_mod_cast h

lemma real_within_childPoles (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (v w : (ts i).Node) (a b : (ts i).Dart)
    (ha : (ts i).pole v=some a) (hb : (ts i).pole w=some b) :
    (branch c ts).realDistance (childPole c ts i v) (childPole c ts i w)=
      (ts i).realDistance a b := by
  have h := within_childPoles c ts i v w a b ha hb
  rw [distance_eq_nat,distance_eq_nat] at h
  dsimp only [realDistance]
  exact_mod_cast h

lemma commonRoute_leaf (t : CoreTree) (h : t=leaf) (v w : t.Node) : t.commonRoute v w=0 := by
  subst t;rfl

/-- Exact source two-pole comparison: the only error lies inside the last
common ancestor's actual isolated core. All distances use all original edges. -/
theorem pole_comparison (t : CoreTree) (v w : t.Node) (a b : t.Dart)
    (ha : t.pole v=some a) (hb : t.pole w=some b) :
    |t.realDistance a b-((t.routeLength v:ℝ)+t.routeLength w-2*t.commonRoute v w)|≤2*t.maxDegree := by
  induction t with
  | leaf => cases a
  | branch c ts ih =>
    cases v with
    | inl u =>
      have hroot : coreDart ts c.entry=a := Option.some.inj ha
      subst a
      rw [real_root_distance (branch c ts) w _ b rfl hb]
      simp only [routeLength,commonRoute,Nat.cast_zero,zero_add,mul_zero,sub_zero,sub_self,abs_zero]
      positivity
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases w with
      | inl u =>
        have hroot : coreDart ts c.entry=b := Option.some.inj hb
        subst b
        rw [realDistance_comm,real_root_distance (branch c ts) (.inr ⟨i,v⟩) _ a rfl ha]
        simp only [routeLength,commonRoute,Nat.cast_zero,add_zero,mul_zero,sub_zero,sub_self,abs_zero]
        positivity
      | inr w =>
        obtain ⟨j,w⟩ := w
        have ha' : childPole c ts i v=a := Option.some.inj ha
        have hb' : childPole c ts j w=b := Option.some.inj hb
        subst a;subst b
        by_cases hij : i=j
        · subst j
          by_cases ht : ts i=leaf
          · have hpv := pole_none_of_leaf (ts i) ht v
            have hpw := pole_none_of_leaf (ts i) ht w
            have hrv := route_zero_of_leaf (ts i) ht v
            have hrw := route_zero_of_leaf (ts i) ht w
            have hcr := commonRoute_leaf (ts i) ht v w
            simp only [childPole,hpv,hpw,Option.map_none,Option.getD_none,realDistance_self,
              routeLength,commonRoute,dite_true,hrv,hrw,hcr,Nat.add_zero]
            norm_num [two_mul]
          · obtain ⟨a,ha⟩ := pole_some_of_ne_leaf (ts i) ht v
            obtain ⟨b,hb⟩ := pole_some_of_ne_leaf (ts i) ht w
            rw [real_within_childPoles c ts i v w a b ha hb]
            have hh := ih i v w a b ha hb
            have hm : ((ts i).maxDegree:ℝ)≤(branch c ts).maxDegree := Nat.cast_le.mpr (maxDegree_child c ts i)
            simp only [routeLength,commonRoute,dite_true,Nat.cast_add]
            convert hh.trans (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤2)) using 1
            all_goals try with_reducible_and_instances rfl
            first | rfl | ring_nf
        · rw [real_between_childPoles c ts i j hij v w]
          have hnonneg := c.realDistance_nonneg (nextSlot c i) (nextSlot c j)
          have hupper := c.corner_distance_le i j
          have hbi : (c.increment i:ℝ) ≤ c.val.length := Nat.cast_le.mpr (c.increment_le i)
          have hbj : (c.increment j:ℝ) ≤ c.val.length := Nat.cast_le.mpr (c.increment_le j)
          have hm : (c.val.length:ℝ)≤(branch c ts).maxDegree := Nat.cast_le.mpr (maxDegree_core c ts)
          simp only [routeLength,commonRoute,dite_eq_right hij,Nat.cast_add,Nat.cast_zero,mul_zero,sub_zero]
          apply abs_le.mpr
          constructor <;> linarith

end CoreTree
end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FKCRT.TreeCoding

lemma recordTypeAt_congr_prefix {x y : ℕ → ℕ} {N t : ℕ}
    (h : ∀ k  <  N,x k=y k) (ht0 : 0 < t) (htN : t ≤ N) :
    recordTypeAt x t=recordTypeAt y t := by
  have hS := integerSum_congr_prefix h
  unfold recordTypeAt
  rw [h (t-1) (by omega),hS t htN,prefixMaximum_congr (fun k hk => hS k (by omega))]

lemma record_boundary (x y : ℕ → ℕ) {n m : ℕ} (hnm : n ≤ m)
    (hxy : ∀ k  <  n,x k=y k)
    (hmax : ∀ k  ≤  n,integerSum x k ≤ integerSum x n)
    (hmid : ∀ k,n < k → k ≤ m → integerSum y k < integerSum x n)
    (hfin : integerSum x n ≤ integerSum y (m+1)) :
    weakRecords (integerSum y) (m+1)=insert (m+1) (weakRecords (integerSum x) n) ∧
    recordTypeAt y (m+1)=(y m,(integerSum y (m+1)-integerSum x n).toNat) := by
  have hS (k) (hk : k ≤ n) : integerSum x k=integerSum y k := integerSum_congr_prefix hxy k hk
  have hmaxy (k) (hk : k ≤ m) : integerSum y k ≤ integerSum x n := by
    by_cases hkn : k ≤ n
    · rw [← hS k hkn];exact hmax k hkn
    · exact (hmid k (by omega) hk).le
  have hp : prefixMaximum (integerSum y) m=integerSum x n := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun k hk => hmaxy k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    · rw [hS n le_rfl]
      exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega))
  refine ⟨?_,by simp only [recordTypeAt,Nat.add_sub_cancel,hp]⟩
  rw [weakRecords_congr_prefix hS]
  ext k
  simp only [mem_weakRecords,Finset.mem_insert]
  constructor
  · rintro ⟨hk0,hkm,hrec⟩
    by_cases hkn : k ≤ n
    · exact Or.inr ⟨hk0,hkn,hrec⟩
    · left
      by_contra he
      have hh := hrec n (by omega)
      rw [← hS n le_rfl] at hh
      have := hmid k (by omega) (by omega)
      omega
  · rintro (rfl | ⟨hk0,hkn,hrec⟩)
    · refine ⟨by omega,le_rfl,?_⟩
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · rfl
      · exact (hmaxy j (by omega)).trans hfin
    · exact ⟨hk0,hkn.trans (by omega),hrec⟩

end FKCRT.TreeCoding
namespace FKCRT.Inventory
open TreeCoding

lemma labelProfileSum_empty (b : (ℕ×ℕ) → CoreLabel → ℝ) : labelProfileSum b []=0 := by
  simp [labelProfileSum,weakRecords]

lemma labelProfileSum_attach (b : (ℕ×ℕ) → CoreLabel → ℝ) (a f : List CoreLabel) (c : CoreLabel)
    {i : ℕ} (ha : ∀ j  ≤  a.length,0 ≤ prefixSum (PlaneTree.incrementWord (a.map CoreLabel.arity)) j)
    (hf : PlaneTree.SuffixNegative (f.map CoreLabel.arity))
    (hfs : (PlaneTree.incrementWord (f.map CoreLabel.arity)).sum= -(i:ℤ))
    (hik : i < c.arity) :
    labelProfileSum b (c::(f++a))=labelProfileSum b a+b (c.arity,c.arity-1-i) c := by
  let aa := a.map CoreLabel.arity
  let ff := f.map CoreLabel.arity
  let x := listStream aa.reverse
  let y := listStream ((aa.reverse++ff.reverse)++[c.arity])
  let n := a.length
  let m := a.length+f.length
  have hp : ∀ j  <  n,x j=y j := by
    intro j hj
    dsimp [x,y,n,aa] at *
    rw [List.append_assoc]
    exact (listStream_append_prefix _ _ j (by simpa using hj)).symm
  have hS : integerSum x n=(PlaneTree.incrementWord aa).sum := by
    dsimp [x,n,aa]
    convert integerSum_listStream_length (a.map CoreLabel.arity).reverse using 1  <;>
      simp [PlaneTree.incrementWord]
  have hm : ∀ j  ≤  m,integerSum y j=integerSum (listStream (aa.reverse++ff.reverse)) j := by
    intro j hj
    apply integerSum_congr_prefix (N := m) _ j hj
    intro r hr
    exact listStream_append_prefix _ _ r (by simpa [m,aa,ff] using hr)
  have hmid : ∀ j,n < j → j ≤ m → integerSum y j < integerSum x n := by
    intro j hj hjm
    rw [hm j hjm]
    have hsub : j-n ≤ ff.reverse.length := by dsimp [ff,m,n] at *;simp at *;omega
    have he : j=aa.reverse.length+(j-n) := by dsimp [aa,n] at *;simp only [List.length_reverse,List.length_map];omega
    rw [he,integerSum_list_append _ _ hsub]
    rw [show (PlaneTree.incrementWord aa.reverse).sum=(PlaneTree.incrementWord aa).sum by simp [PlaneTree.incrementWord],hS]
    exact add_lt_of_neg_right _ (reverse_word_strict_negative ff hf (by omega) (by simpa using hsub))
  have hfinal : integerSum y (m+1)=integerSum x n+((c.arity:ℤ)-1-i) := by
    dsimp [y,m]
    have he : a.length+f.length+1=(((aa.reverse++ff.reverse)++[c.arity])).length := by simp [aa,ff,Nat.add_assoc]
    rw [he,integerSum_listStream_length,PlaneTree.incrementWord_append,PlaneTree.incrementWord_append]
    simp only [List.sum_append,PlaneTree.incrementWord,List.map_reverse,List.sum_reverse,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [hS]
    unfold PlaneTree.incrementWord
    unfold PlaneTree.incrementWord at hfs
    dsimp only [ff]
    rw [hfs]
    omega
  have hy : y m=c.arity := by
    dsimp [y,m]
    rw [listStream_get (by simp [aa,ff]),List.getElem_append_right (by simp [aa,ff])]
    simp [aa,ff]
  have hmax : ∀ j  ≤  n,integerSum x j ≤ integerSum x n := by
    simpa only [x,n,aa,List.length_map] using list_reverse_prefix_max aa (by simpa [aa] using ha)
  obtain ⟨hr,ht⟩ := record_boundary x y (by dsimp [n,m];omega) hp hmax hmid (by rw [hfinal];omega)
  rw [hy,hfinal,show (integerSum x n+((c.arity:ℤ)-1-i)-integerSum x n).toNat=c.arity-1-i by omega] at ht
  have hword : ((c::(f++a)).map CoreLabel.arity).reverse=(aa.reverse++ff.reverse)++[c.arity] := by
    simp [aa,ff,List.reverse_append]
  unfold labelProfileSum
  rw [hword,show (c::(f++a)).length=m+1 by simp [m,Nat.add_comm]]
  change (∑ r ∈ weakRecords (integerSum y) (m+1),
    b (recordTypeAt y r) ((c::(f++a)).reverse[r-1]?.getD none))=_
  rw [hr,Finset.sum_insert (by intro h;have := (mem_weakRecords _ _ _).mp h;omega)]
  rw [ht]
  have hlast : ((c::(f++a)).reverse[m]?.getD none)=c := by
    simp only [List.reverse_cons,List.reverse_append]
    rw [List.getElem?_append_right (by simp [m])]
    simp [m]
  simp only [Nat.add_sub_cancel,hlast]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hb := (mem_weakRecords _ _ _).mp hr
  rw [← recordTypeAt_congr_prefix hp (by omega) hb.2.1]
  congr 1
  simp only [List.reverse_cons,List.reverse_append,List.append_assoc]
  rw [List.getElem?_append_left (by dsimp [n] at hb;simp;omega)]

lemma toCode_labelProfile (T : CoreTree) (b : (ℕ×ℕ) → CoreLabel → ℝ) {v : ℕ}
    (hv : v ≤ T.labels.length) :
    markedSpineSum b T.toCode hv (fun i => T.labels[i.val])=labelProfileSum b (T.labels.take v) := by
  let l := T.labels.map CoreLabel.arity
  let x := reverseFirst v (arrayStream (codeEmbedding T.labels.length T.toCode))
  let y := listStream (l.take v).reverse
  have hxy : ∀ k  <  v,x k=y k := by
    have hh : ∀ k  <  T.labels.length,arrayStream (codeEmbedding T.labels.length T.toCode) k=listStream l k := by
      intro k hk
      rw [listStream_get (by simpa [l] using hk)]
      simp only [arrayStream,dite_eq_left hk,l,List.getElem_map]
      rfl
    intro k hk
    exact (reverseFirst_prefix_congr hv hh k hk).trans (reverseFirst_list_prefix l (by simpa [l] using hv) k hk)
  unfold markedSpineSum labelProfileSum
  have hlen : (T.labels.take v).length=v := by simp [Nat.min_eq_left hv]
  rw [hlen,List.map_take]
  change _=(∑ r ∈ weakRecords (integerSum y) v,_)
  rw [← weakRecords_congr_prefix (integerSum_congr_prefix hxy)]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro r _
  have hb := (mem_weakRecords _ _ _).mp r.property
  change b (recordTypeAt x r.val) _=b (recordTypeAt y r.val) _
  rw [recordTypeAt_congr_prefix hxy (by omega) hb.2.1]
  congr 1
  rw [List.getElem?_eq_getElem (by simp [hlen];omega),List.getElem_reverse]
  simp only [hlen]
  rw [List.getElem_take]
  congr 1
  simp only [spineRecordVertex]
  omega

end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open TreeCoding
attribute [local instance] Classical.propDecidable

lemma before_length (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    (before c ts i).length=i.val := by simp [before]

lemma labels_take_child (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length)
    {v : ℕ} (hv : v≤(ts i).labels.length) :
    (branch c ts).labels.take (1+((before c ts i).flatMap labels).length+v)=
      some c::((before c ts i).flatMap labels++(ts i).labels.take v) := by
  rw [labels_split c ts i]
  rw [show 1+((before c ts i).flatMap labels).length+v=
    (((before c ts i).flatMap labels).length+v)+1 by omega,List.take_succ_cons]
  rw [List.append_assoc,List.take_append]
  congr 1
  rw [List.take_of_length_le (by omega),Nat.add_sub_cancel_left,List.take_append_of_le_length hv]

lemma forest_labels_degrees (fs : List CoreTree) :
    (fs.flatMap labels).map CoreLabel.arity=PlaneTree.forestDegrees (fs.map shape) := by
  simp only [PlaneTree.forestDegrees,List.flatMap_map,List.map_flatMap]
  congr 1
  funext t
  exact t.shape_degrees.symm

lemma forest_labels_properties (fs : List CoreTree) :
    (PlaneTree.incrementWord ((fs.flatMap labels).map CoreLabel.arity)).sum= -(fs.length:ℤ) ∧
    PlaneTree.SuffixNegative ((fs.flatMap labels).map CoreLabel.arity) := by
  rw [forest_labels_degrees]
  simpa only [List.length_map] using PlaneTree.forest_properties (fs.map shape)

lemma labels_take_nonneg (t : CoreTree) {v : ℕ} (hv : v<t.labels.length) :
    ∀ j≤(t.labels.take v).length,
      0≤prefixSum (PlaneTree.incrementWord ((t.labels.take v).map CoreLabel.arity)) j := by
  intro j hj
  have hjv : j≤v := hj.trans (List.length_take_le _ _)
  have h := t.degrees_excursion.2 j (by simpa [PlaneTree.incrementWord,degrees] using hjv.trans_lt hv)
  simpa only [PlaneTree.incrementWord,degrees,List.map_take,prefixSum,List.take_take,Nat.min_eq_left hjv] using h

lemma nodeSpine_profile (b : (ℕ×ℕ) → CoreLabel → ℝ) (t : CoreTree) (v : t.Node) :
    labelProfileSum b (t.labels.take (t.nodeIndex v))=t.nodeSpine b v := by
  induction t with
  | leaf => exact labelProfileSum_empty b
  | branch c ts ih =>
    cases v with
    | inl u => exact labelProfileSum_empty b
    | inr v =>
      obtain ⟨i,v⟩ := v
      change labelProfileSum b ((branch c ts).labels.take (1+((before c ts i).flatMap labels).length+(ts i).nodeIndex v))=_
      rw [labels_take_child c ts i (nodeIndex_bound _ _).le]
      have hp := forest_labels_properties (before c ts i)
      rw [before_length] at hp
      rw [labelProfileSum_attach b ((ts i).labels.take ((ts i).nodeIndex v)) ((before c ts i).flatMap labels) (some c) (labels_take_nonneg _ (nodeIndex_bound _ _)) hp.2 hp.1 i.isLt,ih i v]
      exact add_comm _ _

lemma nodeSpine_marked (b : (ℕ×ℕ) → CoreLabel → ℝ) (t : CoreTree) (v : t.Node) :
    t.nodeSpine b v=markedSpineSum b t.toCode (t.nodeIndex_bound v).le (fun i => t.labels[i.val]) := by
  rw [toCode_labelProfile,nodeSpine_profile]

lemma coreIncrement_slot (c : Core) (i : Fin c.val.length) :
    coreIncrement (c.val.length,c.val.length-1-i.val) (some c)=(c.increment i:ℝ) := by
  dsimp only [coreIncrement]
  rw [dite_eq_left (by constructor;rfl;omega)]
  congr 2
  apply Fin.ext
  dsimp
  omega

lemma nodeSpine_metric (t : CoreTree) (v : t.Node) :
    t.nodeSpine coreIncrement v=(t.routeLength v:ℝ) := by
  induction t with
  | leaf => simp [nodeSpine,routeLength]
  | branch c ts ih =>
    cases v with
    | inl u => simp [nodeSpine,routeLength]
    | inr v =>
      obtain ⟨i,v⟩ := v
      simp only [nodeSpine,coreIncrement_slot,routeLength,Nat.cast_add,ih]

/-- The actual original-map pole distance is the same marked ancestor sum
appearing in the conditioned-code uniform LLN, not a separately sampled tree. -/
theorem routeLength_marked (t : CoreTree) (v : t.Node) :
    (t.routeLength v:ℝ)=markedSpineSum coreIncrement t.toCode (t.nodeIndex_bound v).le
      (fun i => t.labels[i.val]) := by
  rw [← nodeSpine_metric,nodeSpine_marked]

lemma nodeSpine_one (t : CoreTree) (v : t.Node) : t.nodeSpine (fun _ _ => 1) v=(t.depth v:ℝ) := by
  induction t with
  | leaf => simp [nodeSpine,depth]
  | branch c ts ih =>
    cases v with
    | inl u => simp [nodeSpine,depth]
    | inr v =>
      obtain ⟨i,v⟩ := v
      simp only [nodeSpine,depth,Nat.cast_add,Nat.cast_one,ih]

lemma depth_height (t : CoreTree) (v : t.Node) :
    t.depth v=height t.toCode.val (t.nodeIndex v) := by
  have h := nodeSpine_marked (fun _ _ => 1) t v
  rw [nodeSpine_one,markedSpineSum_deterministic,codeSpineSum_one t.toCode (nodeIndex_bound _ _).le] at h
  exact_mod_cast h

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
attribute [local instance] Classical.propDecidable

lemma routeLength_root (t : CoreTree) : t.routeLength t.root=0 := by cases t <;> rfl

lemma same_child_between (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length)
    (v w : (ts i).Node) (u : (branch c ts).Node)
    (h₁ : (branch c ts).nodeIndex (.inr ⟨i,v⟩)≤(branch c ts).nodeIndex u)
    (h₂ : (branch c ts).nodeIndex u≤(branch c ts).nodeIndex (.inr ⟨i,w⟩)) :
    ∃ z : (ts i).Node,u=.inr ⟨i,z⟩ ∧ (ts i).nodeIndex v≤(ts i).nodeIndex z ∧
      (ts i).nodeIndex z≤(ts i).nodeIndex w := by
  cases u with
  | inl a => simp only [nodeIndex] at h₁;omega
  | inr u =>
    obtain ⟨j,z⟩ := u
    have hi := children_order c ts i j v z h₁
    have hj := children_order c ts j i z w h₂
    obtain rfl := le_antisymm hi hj
    exact ⟨z,rfl,by simpa only [nodeIndex,Nat.add_le_add_iff_left] using h₁,
      by simpa only [nodeIndex,Nat.add_le_add_iff_left] using h₂⟩

/-- Every intervening preorder vertex remains below the last common ancestor. -/
lemma commonRoute_le_intervening (t : CoreTree) (v w u : t.Node)
    (h₁ : t.nodeIndex v≤t.nodeIndex u) (h₂ : t.nodeIndex u≤t.nodeIndex w) :
    t.commonRoute v w≤t.routeLength u := by
  induction t with
  | leaf => simp [commonRoute,routeLength]
  | branch c ts ih =>
    cases v with
    | inl a => exact Nat.zero_le _
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases w with
      | inl a => exact Nat.zero_le _
      | inr w =>
        obtain ⟨j,w⟩ := w
        by_cases hij : i=j
        · subst j
          obtain ⟨z,rfl,hz₁,hz₂⟩ := same_child_between c ts i v w u h₁ h₂
          simpa only [commonRoute,dite_true,routeLength,Nat.add_le_add_iff_left] using ih i v w z hz₁ hz₂
        · simp only [commonRoute,dite_eq_right hij]
          exact Nat.zero_le _

/-- One intervening vertex is either the ancestor itself or the first node
of its selected right-hand child, costing at most one maximum core degree. -/
lemma exists_intervening_low (t : CoreTree) (v w : t.Node) (h : t.nodeIndex v≤t.nodeIndex w) :
    ∃ u : t.Node,t.nodeIndex v≤t.nodeIndex u ∧ t.nodeIndex u≤t.nodeIndex w ∧
      t.routeLength u≤t.commonRoute v w+t.maxDegree := by
  induction t with
  | leaf => exact ⟨v,le_rfl,h,by simp [routeLength,commonRoute]⟩
  | branch c ts ih =>
    cases v with
    | inl a => exact ⟨.inl a,le_rfl,h,by simp [routeLength,commonRoute]⟩
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases w with
      | inl a =>
        simp only [nodeIndex] at h
        omega
      | inr w =>
        obtain ⟨j,w⟩ := w
        by_cases hij : i=j
        · subst j
          have hvw : (ts i).nodeIndex v≤(ts i).nodeIndex w := by simpa only [nodeIndex,Nat.add_le_add_iff_left] using h
          obtain ⟨u,hu₁,hu₂,hu⟩ := ih i v w hvw
          refine ⟨.inr ⟨i,u⟩,by simpa only [nodeIndex,Nat.add_le_add_iff_left] using hu₁,
            by simpa only [nodeIndex,Nat.add_le_add_iff_left] using hu₂,?_⟩
          have hm := maxDegree_child c ts i
          simp only [routeLength,commonRoute,dite_true]
          omega
        · have hij' : i<j := lt_of_le_of_ne (children_order c ts i j v w h) hij
          refine ⟨.inr ⟨j,(ts j).root⟩,(children_index_strict c ts i j hij' v (ts j).root).le,?_,?_⟩
          · simp only [nodeIndex,nodeIndex_root]
            omega
          · simp only [routeLength,routeLength_root,Nat.add_zero,commonRoute,dite_eq_right hij,Nat.zero_add]
            exact (c.increment_le j).trans (maxDegree_core c ts)

/-- A walk minimum can be used without assuming a probabilistic law at a
random ancestor. This is the deterministic all-poles comparison after the
uniform same-code ancestral estimate. -/
theorem pole_walk_comparison (t : CoreTree) (v w m : t.Node) (a b : t.Dart)
    (ha : t.pole v=some a) (hb : t.pole w=some b)
    (hm₁ : t.nodeIndex v≤t.nodeIndex m) (hm₂ : t.nodeIndex m≤t.nodeIndex w)
    (W : t.Node → ℝ) {α ε : ℝ} (hα : 0≤α)
    (herr : ∀ u,|(t.routeLength u:ℝ)-α*W u|≤ε)
    (hmin : ∀ u,t.nodeIndex v≤t.nodeIndex u → t.nodeIndex u≤t.nodeIndex w → W m≤W u) :
    |t.realDistance a b-α*(W v+W w-2*W m)|≤4*(t.maxDegree:ℝ)+4*ε := by
  have hp := abs_le.mp (t.pole_comparison v w a b ha hb)
  have hlow : (t.commonRoute v w:ℝ)≤t.routeLength m := Nat.cast_le.mpr (commonRoute_le_intervening t v w m hm₁ hm₂)
  obtain ⟨u,hu₁,hu₂,hu⟩ := exists_intervening_low t v w (hm₁.trans hm₂)
  have hhi : (t.routeLength u:ℝ)≤(t.commonRoute v w:ℝ)+t.maxDegree := by exact_mod_cast hu
  have hv := abs_le.mp (herr v)
  have hw := abs_le.mp (herr w)
  have hM := abs_le.mp (herr m)
  have hU := abs_le.mp (herr u)
  have hmul := mul_le_mul_of_nonneg_left (hmin u hu₁ hu₂) hα
  apply abs_le.mpr
  constructor <;> linarith

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CornerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma child_vertexConstant {A : Type*} (c : Core) (ts : Fin c.val.length → CoreTree)
    (f : (branch c ts).Dart → A) (hf : (branch c ts).VertexConstant f)
    (i : Fin c.val.length) : (ts i).VertexConstant (f ∘ childDart ts i) := by
  intro a b hab
  have hn : ts i≠leaf := by
    intro h
    have hh : Nonempty (ts i).Dart := ⟨a⟩
    rw [h] at hh
    exact not_nonempty_empty hh
  obtain ⟨r,L,_,hL⟩ := root_and_head (ts i) hn
  apply hf
  rw [child_internal_distance c ts i r a b L hL,hab]

lemma child_root_value {A : Type*} (c : Core) (ts : Fin c.val.length → CoreTree)
    (f : (branch c ts).Dart → A) (hf : (branch c ts).VertexConstant f)
    (i : Fin c.val.length) :
    (((ts i).rootDart).map (f ∘ childDart ts i)).getD (f (coreDart ts (nextSlot c i)))=
      f (coreDart ts (nextSlot c i)) := by
  by_cases ht : ts i=leaf
  · have hr : (ts i).rootDart=none := by rw [ht];rfl
    rw [hr]
    rfl
  · obtain ⟨a,L,ha,hL⟩ := root_and_head (ts i) ht
    rw [ha,Option.map_some,Option.getD_some]
    apply hf
    rw [(branch c ts).matching.distance_comm,child_distance_sum c ts i (nextSlot c i) a a L hL]
    simp only [StackMatching.distance,SimpleGraph.edist_self,add_zero]

/-- Exact original degree incidence counting. The extra preorder root has
one additional root atom; no size-biased measure is postulated. -/
theorem sum_poles {A : Type*} [AddCommMonoid A] (t : CoreTree) (f : t.Dart → A)
    (hf : t.VertexConstant f) (r : A) :
    (∑ v : t.Node,((t.pole v).map f).getD r)=
      (t.rootDart.map f).getD r+∑ d : t.Dart,f d := by
  induction t generalizing r with
  | leaf =>
    change Empty → A at f
    change (∑ _v : PUnit,r)=r+∑ d : Empty,f d
    simp only [Fintype.sum_unique,Fintype.sum_empty,add_zero]
  | branch c ts ih =>
    change (Fin c.val.length ⊕ (Σ i : Fin c.val.length,(ts i).Dart)) → A at f
    change (∑ v : PUnit ⊕ (Σ i : Fin c.val.length,(ts i).Node),_)=_
    rw [Fintype.sum_sum_type,Fintype.sum_sigma]
    simp only [Fintype.sum_unique,pole,rootDart]
    have hx (i : Fin c.val.length) :
        (∑ v : (ts i).Node,f (childPole c ts i v))=
          f (coreDart ts (nextSlot c i))+∑ d : (ts i).Dart,f (childDart ts i d) := by
      have hh := ih i (f ∘ childDart ts i) (child_vertexConstant c ts f hf i)
        (f (coreDart ts (nextSlot c i)))
      have hp (v : (ts i).Node) : f (childPole c ts i v)=
          (((ts i).pole v).map (f ∘ childDart ts i)).getD (f (coreDart ts (nextSlot c i))) := by
        unfold childPole
        cases (ts i).pole v <;> rfl
      simp_rw [hp]
      exact hh.trans (congrArg (fun z => z+∑ d : (ts i).Dart,f (childDart ts i d))
        (child_root_value c ts f hf i))
    change f (coreDart ts c.entry)+(∑ i,∑ v,f (childPole c ts i v))=
      f (coreDart ts c.entry)+∑ d : Fin c.val.length ⊕ (Σ i : Fin c.val.length,(ts i).Dart),f d
    simp_rw [hx]
    rw [Finset.sum_add_distrib,Fintype.sum_sum_type,Fintype.sum_sigma]
    congr 1
    congr 1
    exact Equiv.sum_comp (List.finRange c.val.length).formPerm (f ∘ coreDart ts)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma dartGraph_eq_spanning {n : ℕ} (a s : Perm (Dart n)) :
    dartGraph a s=spanningGraph a s Set.univ := by
  ext x y
  change (x≠y ∧ ((∃ d,orbit s d=x ∧ orbit s (a d)=y) ∨
    (∃ d,orbit s d=y ∧ orbit s (a d)=x))) ↔ _
  simp only [spanningGraph,SimpleGraph.fromRel_adj,Set.mem_univ,true_and]

lemma matchingCanonical_word {n : ℕ} (w : SuccessfulWord n)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) :
    (matchingCanonical w D).word=w := by
  apply Subtype.ext
  exact matchingWord_of_matchings w.val D.first D.second D.first_arches D.second_arches
    D.covers D.first_types D.second_types

/-- The quotient representative used by the main statement is a genuine rooted
relabelling of the matching map, not merely a map with the same size or law. -/
theorem matching_rooted_intertwine {n : ℕ} (w : SuccessfulWord n)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) :
    let M := ((rootedWordEquiv n).symm w).1
    ∃ r : Perm (Dart n),r 0=0 ∧ (∀ d,reversal M (r d)=r (D.mate d)) ∧
      (∀ d,rotation M (r d)=r (((List.finRange (2*(n+1))).formPerm*turns D.first) d)) := by
  dsimp only
  let x := (rootedWordEquiv n).symm w
  have hw : (rootedTreeNormal x).word=w := (rootedWordEquiv n).apply_symm_apply w
  have hh : matchingCanonical w D=rootedTreeNormal x :=
    CanonicalTreeMap.word_injective ((matchingCanonical_word w D).trans hw.symm)
  have hi := canonicalizeTree_iso x.1.out x.2.val x.2.property
  change MapIso (rootedTreeNormal x).toMap x.1.out at hi
  rw [← hh] at hi
  exact hi

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*}

lemma listDartEquiv_get (l : List α) (hn : l.Nodup) (hl : ∀ d,d∈l) {N : ℕ}
    (hN : l.length=N) (i : Fin N) :
    listDartEquiv l hn hl hN i=l[i.val]'(by omega) := rfl

lemma listDartEquiv_list (l : List α) (hn : l.Nodup) (hl : ∀ d,d∈l) {N : ℕ}
    (hN : l.length=N) : (List.finRange N).map (listDartEquiv l hn hl hN)=l := by
  apply List.ext_getElem
  · simp [hN]
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_finRange,listDartEquiv_get,Fin.val_cast]

lemma listDartEquiv_labels (l : List α) (hn : l.Nodup) (hl : ∀ d,d∈l) {N : ℕ}
    (hN : l.length=N) (v : α → TypedLetter) (w : Fin N → TypedLetter)
    (hw : l.map v=List.ofFn w) (i : Fin N) : v (listDartEquiv l hn hl hN i)=w i := by
  have hi : i.val<l.length := by omega
  have hi' : i.val<(l.map v).length := by simpa using hi
  have h := congrArg (fun a : List TypedLetter => a[i.val]?) hw
  simpa only [List.getElem?_eq_getElem hi',List.getElem_map,
    List.getElem?_eq_getElem (show i.val<(List.ofFn w).length by simp),List.getElem_ofFn,
    Option.some.injEq,← listDartEquiv_get l hn hl hN i] using h

variable [DecidableEq α]

/-- Literal finite-word normalization simultaneously intertwines edge and
vertex permutations of the original multigraph. -/
theorem StackMatching.word_intertwine {v : α → TypedLetter} {l : List α}
    (M : StackMatching v l) (hn : l.Nodup) (hl : ∀ d,d∈l) {n : ℕ}
    (w : FKCRT.SuccessfulWord n) (hw : l.map v=List.ofFn w.val)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) :
    ∃ e : FKCRT.Dart n ≃ α,
      (∀ i,M.mate (e i)=e (D.mate i)) ∧
      (∀ i,(l.formPerm*turns M.first) (e i)=
        e (((List.finRange (2*(n+1))).formPerm*turns D.first) i)) := by
  have hN : l.length=2*(n+1) := by
    have h := congrArg List.length hw
    simpa only [List.length_map,List.length_ofFn] using h
  let e := listDartEquiv l hn hl hN
  have he : (List.finRange (2*(n+1))).map e=l := listDartEquiv_list l hn hl hN
  have hv (i : FKCRT.Dart n) (_hi : i∈List.finRange (2*(n+1))) : v (e i)=w.val i :=
    listDartEquiv_labels l hn hl hN v w.val hw i
  let Q := D.map e v hv
  let R : StackMatching v l := he ▸ Q
  have hm : M.mate=Q.mate := (M.unique_mate R hn).trans (Q.cast_mate he)
  have hf : turns M.first=turns Q.first := (M.unique_first R hn).trans
    (congrArg turns (Q.cast_first he))
  refine ⟨e,?_,?_⟩
  · intro i
    rw [hm]
    exact D.map_mate (List.nodup_finRange _) e e.injective v hv i (List.mem_finRange i)
  · intro i
    change l.formPerm (turns M.first (e i))=e ((List.finRange _).formPerm (turns D.first i))
    rw [hf,D.map_first (List.nodup_finRange _) e e.injective v hv]
    rw [← he]
    exact formPerm_map_on _ (List.nodup_finRange _) e e.injective _ (List.mem_finRange _)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- The actual FK representative and the recursively glued literal map are
isomorphic on their original darts, simultaneously for edges and vertices. -/
theorem realized_intertwine (t : CoreTree) {n : ℕ} (w : FKCRT.SuccessfulWord n)
    (hw : t.word=List.ofFn w.val) :
    let M := ((FKCRT.rootedWordEquiv n).symm w).1
    ∃ e : t.Dart ≃ FKCRT.Dart n,
      (∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d)) ∧
      (∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) := by
  let D := StackMatching.ofEmpty (w := w.val) (l := List.finRange (2*(n+1)))
    (by simpa only [← List.ofFn_eq_map] using w.property)
  obtain ⟨e,he,hp⟩ := t.matching.word_intertwine t.darts_nodup t.darts_mem w
    (t.darts_word.trans hw) D
  obtain ⟨r,_hr,hrE,hrV⟩ := FKCRT.matching_rooted_intertwine w D
  refine ⟨e.symm.trans r,?_,?_⟩
  · intro d
    change FKCRT.reversal _ (r (e.symm d))=r (e.symm (t.matching.mate d))
    rw [hrE]
    apply congrArg r
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using (he (e.symm d)).symm
  · intro d
    change FKCRT.rotation _ (r (e.symm d))=r (e.symm ((t.darts.formPerm*turns t.matching.first) d))
    rw [hrV]
    apply congrArg r
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using (hp (e.symm d)).symm

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma pole_root (t : CoreTree) : t.pole t.root=t.rootDart := by cases t <;> rfl

lemma wordNodeEquiv_root (t : CoreTree) : t.wordNodeEquiv t.root=0 := by
  apply Fin.ext
  exact t.nodeIndex_root

lemma vertexConstant_of_intertwine {A : Type*} (t : CoreTree) {n : ℕ}
    (M : FKCRT.RootedMap n) (e : t.Dart ≃ FKCRT.Dart n)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (f : FKCRT.Vertex M → A) :
    t.VertexConstant (fun d => f (orbit (FKCRT.rotation M) (e d))) := by
  intro a b hab
  change (dartGraph t.matching.mate (t.darts.formPerm*turns t.matching.first)).edist
    (vertex _ a) (vertex _ b)=0 at hab
  have hh := SimpleGraph.edist_eq_zero_iff.mp hab
  exact congrArg (f ∘ dartVertexEquiv e hp) hh

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma realizedPole_some (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (v : t.Node) (a : t.Dart) (ha : t.pole v=some a) :
    t.realizedPole M e v=orbit (FKCRT.rotation M) (e a) := by
  simp only [realizedPole,ha,Option.map_some,Option.getD_some]

/-- Exact uniform nonroot-preorder mass equals original uniform dart mass.
The finite root atom is cancelled, not ignored asymptotically. -/
theorem nonroot_dirac_eq (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) :
    let : MeasurableSpace (FKCRT.Vertex M) := ⊤
    (∑ i : Fin t.word.length,Measure.dirac (t.nonrootVertex M e i))=
      ∑ d : FKCRT.Dart n,Measure.dirac (orbit (FKCRT.rotation M) d) := by
  let : MeasurableSpace (FKCRT.Vertex M) := ⊤
  let r := orbit (FKCRT.rotation M) 0
  let f := fun d : t.Dart => Measure.dirac (orbit (FKCRT.rotation M) (e d))
  have hf : t.VertexConstant f := t.vertexConstant_of_intertwine M e hp Measure.dirac
  have hh := t.sum_poles f hf (Measure.dirac r)
  have hs := t.wordNodeEquiv.symm.sum_comp (fun v => ((t.pole v).map f).getD (Measure.dirac r))
  rw [Fin.sum_univ_succ] at hs
  have hr : t.wordNodeEquiv.symm 0=t.root :=
    t.wordNodeEquiv.symm_apply_eq.mpr t.wordNodeEquiv_root.symm
  rw [hr,t.pole_root] at hs
  have hz := hs.trans hh
  have hv (v : t.Node) : ((t.pole v).map f).getD (Measure.dirac r)=
      Measure.dirac (t.realizedPole M e v) := by
    dsimp [realizedPole]
    cases t.pole v <;> rfl
  have hroot : (t.rootDart.map f).getD (Measure.dirac r)=Measure.dirac (t.realizedPole M e t.root) := by
    rw [← t.pole_root]
    exact hv t.root
  rw [hroot] at hz
  simp_rw [hv] at hz
  have hsum : (∑ d : t.Dart,f d)=∑ d : FKCRT.Dart n,Measure.dirac (orbit (FKCRT.rotation M) d) :=
    e.sum_comp (fun d => Measure.dirac (orbit (FKCRT.rotation M) d))
  rw [hsum] at hz
  apply Measure.ext
  intro s hs
  have hh' := congrArg (fun μ : Measure (FKCRT.Vertex M) => μ s) hz
  simp only [Measure.add_apply] at hh'
  apply (ENNReal.add_left_inj (measure_ne_top (Measure.dirac (t.realizedPole M e t.root)) s)).mp
  simpa only [add_comm,nonrootVertex] using hh'

/-- Every original vertex is reached by a nonroot pole, even in the presence
of loops and coincident poles. -/
theorem nonrootVertex_surjective (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) :
    Function.Surjective (t.nonrootVertex M e) := by
  intro v
  classical
  by_contra h
  have hn : ∀ i,t.nonrootVertex M e i≠v := by simpa only [not_exists] using h
  let : MeasurableSpace (FKCRT.Vertex M) := ⊤
  have hm := congrArg (fun μ : Measure (FKCRT.Vertex M) => μ {v}) (t.nonroot_dirac_eq M e hp)
  have hz : (∑ i : Fin t.word.length,Measure.dirac (t.nonrootVertex M e i)) {v}=0 := by
    simp only [Measure.finsetSum_apply,Measure.dirac_apply' _ (MeasurableSet.singleton v),
      Set.indicator_apply,Set.mem_singleton_iff]
    simp [hn]
  rw [hz] at hm
  obtain ⟨d,hd⟩ := Quotient.mk_surjective v
  have hh : (1:ℝ≥0∞)≤(∑ a : FKCRT.Dart n,Measure.dirac (orbit (FKCRT.rotation M) a)) {v} := by
    rw [Measure.finsetSum_apply]
    calc
      1=Measure.dirac (orbit (FKCRT.rotation M) d) {v} := by
        rw [show orbit (FKCRT.rotation M) d=v from hd]
        simp
      _≤∑ a : FKCRT.Dart n,Measure.dirac (orbit (FKCRT.rotation M) a) {v} :=
        Finset.single_le_sum (f := fun a : FKCRT.Dart n =>
          Measure.dirac (orbit (FKCRT.rotation M) a) {v})
          (fun _ _ => by positivity) (Finset.mem_univ d)
  rw [← hm] at hh
  exact not_le_of_gt zero_lt_one hh

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_FiniteLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

namespace Inventory.CoreTree

lemma successfulMarked_word (n : ℕ) (w : SuccessfulWord n) :
    ((markedWordEquiv (2*(n+1))) (successfulMarkedEquiv n w)).val.val=List.ofFn w.val := by
  simp only [successfulMarkedEquiv,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

end Inventory.CoreTree

end FKCRT
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MeasuredCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace FKCRT
attribute [local instance] Classical.propDecidable

lemma timeCell_measurable (N : ℕ) (hN : 0<N) : Measurable (timeCell N hN) := by
  apply measurable_to_countable
  intro t
  have he : timeCell N hN ⁻¹' {timeCell N hN t}=
      {s : unitInterval | min ⌊(N:ℝ)*s⌋₊ (N-1)=(timeCell N hN t).val} := by
    ext s
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq,Fin.ext_iff,timeCell]
  rw [he]
  exact measurableSet_eq_fun ((Nat.measurable_floor.comp
    (measurable_const.mul measurable_subtype_coe)).min measurable_const) measurable_const

lemma timeCell_of_lt_one (N : ℕ) (hN : 0<N) (t : unitInterval) (ht : (t:ℝ)<1) :
    (timeCell N hN t).val=⌊(N:ℝ)*t⌋₊ := by
  dsimp [timeCell]
  apply min_eq_left
  have hf : ⌊(N:ℝ)*t⌋₊<N := (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) t.property.1)).mpr (by
    have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
    nlinarith)
  omega

lemma timeCell_eq_iff (N : ℕ) (hN : 0<N) (t : unitInterval) (ht : (t:ℝ)<1) (i : Fin N) :
    timeCell N hN t=i ↔ (i.val:ℝ)/(N:ℝ)≤t ∧ (t:ℝ)<(i.val+1:ℝ)/(N:ℝ) := by
  rw [Fin.ext_iff,timeCell_of_lt_one N hN t ht,Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) t.property.1)]
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  rw [div_le_iff₀ hp,lt_div_iff₀ hp]
  rw [mul_comm (t:ℝ)]

lemma cell_volume (N : ℕ) (hN : 0<N) (i : Fin N) :
    (volume : Measure unitInterval) {t | (i.val:ℝ)/(N:ℝ)≤t ∧ (t:ℝ)<(i.val+1:ℝ)/(N:ℝ)}=
      ENNReal.ofReal (1/(N:ℝ)) := by
  rw [volume_set_coe_def,comap_subtype_coe_apply measurableSet_Icc]
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hi : (i.val+1:ℝ)≤N := by exact_mod_cast i.isLt
  have he : Subtype.val '' {t : unitInterval | (i.val:ℝ)/(N:ℝ)≤t ∧
      (t:ℝ)<(i.val+1:ℝ)/(N:ℝ)}=Ico ((i.val:ℝ)/(N:ℝ)) ((i.val+1:ℝ)/(N:ℝ)) := by
    ext t
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro ht
      refine ⟨⟨t,?_⟩,ht,rfl⟩
      constructor
      · exact (div_nonneg (Nat.cast_nonneg _) hp.le).trans ht.1
      · exact ht.2.le.trans ((div_le_one hp).mpr hi)
  rw [he,Real.volume_Ico]
  congr 1
  field_simp
  ring

lemma timeCell_mass (N : ℕ) (hN : 0<N) (i : Fin N) :
    ((volume : Measure unitInterval).map (timeCell N hN)) {i}=ENNReal.ofReal (1/(N:ℝ)) := by
  rw [Measure.map_apply (timeCell_measurable N hN) (measurableSet_singleton i)]
  have he : timeCell N hN ⁻¹' {i}=ᵐ[volume]
      {t : unitInterval | (i.val:ℝ)/(N:ℝ)≤t ∧ (t:ℝ)<(i.val+1:ℝ)/(N:ℝ)} := by
    have hne : ∀ᵐ t : unitInterval ∂volume,t≠1 := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with t ht
    have ht' : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (fun h => ht (Subtype.ext h))
    exact propext (timeCell_eq_iff N hN t ht' i)
  rw [measure_congr he,cell_volume N hN i]

lemma timeCell_map (N : ℕ) (hN : 0<N) :
    (volume : Measure unitInterval).map (timeCell N hN)=
      ∑ i : Fin N,ENNReal.ofReal (1/(N:ℝ)) • Measure.dirac i := by
  apply Measure.ext_of_singleton
  intro i
  rw [timeCell_mass N hN i]
  simp [Measure.finsetSum_apply,Pi.single_apply]

lemma timeCell_surjective (N : ℕ) (hN : 0<N) : Function.Surjective (timeCell N hN) := by
  intro i
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  let t : unitInterval := ⟨(i.val:ℝ)/(N:ℝ),by constructor;positivity;exact (div_le_one hp).mpr (by exact_mod_cast i.isLt.le)⟩
  refine ⟨t,(timeCell_eq_iff N hN t (by dsimp [t];exact (div_lt_one hp).mpr (by exact_mod_cast i.isLt)) i).mpr ⟨le_rfl,?_⟩⟩
  dsimp [t]
  exact (div_lt_div_iff_of_pos_right hp).mpr (by linarith)

lemma timeCell_mono (N : ℕ) (hN : 0<N) : Monotone (timeCell N hN) := by
  intro s t hst
  change min ⌊(N:ℝ)*s⌋₊ (N-1) ≤ min ⌊(N:ℝ)*t⌋₊ (N-1)
  exact min_le_min (Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _))) le_rfl

lemma timeCell_bounds (N : ℕ) (hN : 0<N) (t : unitInterval) :
    ((timeCell N hN t).val:ℝ)/(N:ℝ)≤t ∧
      (t:ℝ)≤((timeCell N hN t).val+1:ℝ)/(N:ℝ) := by
  by_cases ht : (t:ℝ)<1
  · have hh := (timeCell_eq_iff N hN t ht (timeCell N hN t)).mp rfl
    exact ⟨hh.1,hh.2.le⟩
  · have ht : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    subst t
    have he : (timeCell N hN 1).val=N-1 := by simp [timeCell]
    rw [he]
    have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
    have he' : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast (show N-1+1=N by omega)
    constructor
    · exact (div_le_one hn).mpr (by linarith)
    · change (1:ℝ)≤_
      rw [he',div_self hn.ne']

lemma cellPoint_bounds (N : ℕ) (hN : 0<N) (i : Fin N) :
    (i.val:ℝ)/N ≤ cellPoint N hN i ∧
      (cellPoint N hN i:ℝ)≤(i.val+1:ℝ)/N := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hi : (i.val:ℝ)≤N := by exact_mod_cast i.isLt.le
  change _≤(i.val+1:ℝ)/(N+1:ℝ) ∧ (i.val+1:ℝ)/(N+1:ℝ)≤_
  constructor
  · apply (div_le_div_iff₀ hn (by positivity)).mpr
    nlinarith
  · apply div_le_div_of_nonneg_left (by positivity) hn
    linarith

lemma cellPoint_close (N : ℕ) (hN : 0<N) (t : unitInterval) :
    dist (cellPoint N hN (timeCell N hN t)) t≤1/(N:ℝ) := by
  have ht := timeCell_bounds N hN t
  have hp := cellPoint_bounds N hN (timeCell N hN t)
  have he : (((timeCell N hN t).val:ℝ)+1)/(N:ℝ)-((timeCell N hN t).val:ℝ)/(N:ℝ)=1/(N:ℝ) := by ring
  rw [Subtype.dist_eq,Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith

lemma cellPoint_mono (N : ℕ) (hN : 0<N) : Monotone (cellPoint N hN) := by
  intro i j hij
  change (i.val+1:ℝ)/(N+1:ℝ)≤(j.val+1:ℝ)/(N+1:ℝ)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory Set
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma timeVertex_measurable (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length) :
    @Measurable _ _ inferInstance ⊤ (t.timeVertex M e ht) := by
  let : MeasurableSpace (FKCRT.Vertex M) := ⊤
  exact (measurable_of_finite (t.nonrootVertex M e)).comp (FKCRT.timeCell_measurable _ ht)

lemma timeVertex_surjective (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) :
    Function.Surjective (t.timeVertex M e ht) :=
  (t.nonrootVertex_surjective M e hp).comp (FKCRT.timeCell_surjective _ ht)

/-- No asymptotic replacement of the degree measure is needed. -/
theorem timeVertex_mass (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (hlen : t.word.length=2*(n+1)) :
    @Measure.map _ _ inferInstance ⊤ (t.timeVertex M e ht) volume=FKCRT.degreeMass M := by
  let : MeasurableSpace (FKCRT.Vertex M) := ⊤
  change (volume : Measure unitInterval).map ((t.nonrootVertex M e) ∘ FKCRT.timeCell t.word.length ht)=_
  rw [← Measure.map_map (measurable_of_finite (t.nonrootVertex M e))
    (FKCRT.timeCell_measurable _ ht),FKCRT.timeCell_map]
  rw [Measure.map_finset_sum' (measurable_of_finite (t.nonrootVertex M e)).aemeasurable]
  simp only [Measure.map_smul,
    Measure.map_dirac' (measurable_of_finite (t.nonrootVertex M e))]
  rw [← Finset.smul_sum,t.nonroot_dirac_eq M e hp]
  rw [FKCRT.degreeMass,← Finset.smul_sum]
  congr 1
  rw [hlen]
  norm_num

lemma realized_distance_of (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n)
    (he : ∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d))
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) (a b : t.Dart) :
    ((FKCRT.graph M Set.univ).dist (orbit (FKCRT.rotation M) (e a))
      (orbit (FKCRT.rotation M) (e b)):ℝ)=t.realDistance a b := by
  have hh := dartGraph_embedding_edist e e.injective hp he a b
  rw [FKCRT.dartGraph_eq_spanning] at hh
  change (FKCRT.graph M Set.univ).edist _ _=t.matching.distance a b at hh
  change (FKCRT.graph M Set.univ).edist (orbit (FKCRT.rotation M) (e a))
    (orbit (FKCRT.rotation M) (e b))=t.matching.distance a b at hh
  rw [t.distance_eq_nat a b] at hh
  have hr : (FKCRT.graph M Set.univ).Reachable
      (orbit (FKCRT.rotation M) (e a)) (orbit (FKCRT.rotation M) (e b)) := by
    apply SimpleGraph.edist_ne_top_iff_reachable.mp
    rw [hh]
    exact ENat.natCast_ne_top _
  rw [← SimpleGraph.Reachable.coe_dist_eq_edist hr] at hh
  dsimp only [realDistance]
  exact_mod_cast hh

end FKCRT.Inventory.CoreTree
end


noncomputable section
open Set
namespace FKCRT
attribute [local instance] Classical.propDecidable

lemma cellPoint_interval_near (N : ℕ) (hN : 0<N) (s t : unitInterval) (hst : s ≤ t)
    (i : Fin N) (hsi : timeCell N hN s ≤  i) (hit : i ≤  timeCell N hN t) :
    ∃ u∈uIcc s t,dist (cellPoint N hN i) u ≤ 1/(N:ℝ) := by
  let p := cellPoint N hN i
  by_cases hs : p < s
  · refine ⟨s,left_mem_uIcc,?_⟩
    have hh := cellPoint_close N hN s
    have ho := cellPoint_mono N hN hsi
    change (cellPoint N hN (timeCell N hN s):ℝ) ≤ (p:ℝ) at ho
    rw [Subtype.dist_eq,Real.dist_eq] at hh ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr (show (p:ℝ) ≤ s from hs.le))]
    have hh' := (abs_le.mp hh).1
    linarith
  · by_cases ht : t<p
    · refine ⟨t,right_mem_uIcc,?_⟩
      have hh := cellPoint_close N hN t
      have ho := cellPoint_mono N hN hit
      change (p:ℝ) ≤ (cellPoint N hN (timeCell N hN t):ℝ) at ho
      rw [Subtype.dist_eq,Real.dist_eq] at hh ⊢
      rw [abs_of_nonneg (sub_nonneg.mpr (show (t:ℝ) ≤ p from ht.le))]
      have hh' := (abs_le.mp hh).2
      linarith
    · refine ⟨p,?_,?_⟩
      · rw [uIcc_of_le hst]
        exact ⟨le_of_not_gt hs,le_of_not_gt ht⟩
      · change dist p p ≤ _
        rw [dist_self]
        positivity

lemma sampled_minimum_error (N : ℕ) (hN : 0<N) (f : C(unitInterval,ℝ))
    {η : ℝ} (hmod : ∀ s t,dist s t ≤ 1/(N:ℝ) → |f s-f t| ≤ η)
    (s t : unitInterval) (hst : s ≤ t) (m : Fin N)
    (hsm : timeCell N hN s ≤  m) (hmt : m ≤  timeCell N hN t)
    (hm : ∀ i,timeCell N hN s ≤  i → i ≤  timeCell N hN t →
      f (cellPoint N hN m) ≤ f (cellPoint N hN i)) :
    |f (cellPoint N hN m)-sInf (f '' uIcc s t)| ≤ η := by
  obtain ⟨u,hu,hdu⟩ := cellPoint_interval_near N hN s t hst m hsm hmt
  have hi := csInf_le (interval_image_bddBelow f.continuous s t) (mem_image_of_mem f hu)
  have hmdu := abs_le.mp (hmod _ _ hdu)
  have hl : f (cellPoint N hN m)-η ≤ sInf (f '' uIcc s t) := by
    apply le_csInf (nonempty_uIcc.image f)
    rintro _ ⟨r,hr,rfl⟩
    rw [uIcc_of_le hst] at hr
    have hmr := hm (timeCell N hN r) (timeCell_mono N hN hr.1) (timeCell_mono N hN hr.2)
    have hclose := abs_le.mp (hmod _ _ (cellPoint_close N hN r))
    linarith
  apply abs_le.mpr
  constructor <;> linarith

/-- Discrete positive preorder samples and their exact equal-mass coding
approximate the continuous interval-minimum metric with its own modulus. -/
theorem sampled_excursion_error (N : ℕ) (hN : 0<N) (f : C(unitInterval,ℝ))
    {η : ℝ} (hmod : ∀ s t,dist s t ≤ 1/(N:ℝ) → |f s-f t| ≤ η)
    (s t : unitInterval) (hst : s ≤ t) (m : Fin N)
    (hsm : timeCell N hN s ≤  m) (hmt : m ≤  timeCell N hN t)
    (hm : ∀ i,timeCell N hN s ≤  i → i ≤  timeCell N hN t →
      f (cellPoint N hN m) ≤ f (cellPoint N hN i)) :
    |(f (cellPoint N hN (timeCell N hN s))+f (cellPoint N hN (timeCell N hN t))-
      2*f (cellPoint N hN m))-excursionDist f s t| ≤ 4*η := by
  have h₁ := abs_le.mp (hmod _ _ (cellPoint_close N hN s))
  have h₂ := abs_le.mp (hmod _ _ (cellPoint_close N hN t))
  have h₃ := abs_le.mp (sampled_minimum_error N hN f hmod s t hst m hsm hmt hm)
  dsimp only [excursionDist]
  apply abs_le.mpr
  constructor <;> linarith

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory Set
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma wordNodeEquiv_val (t : CoreTree) (v : t.Node) : (t.wordNodeEquiv v).val=t.nodeIndex v := rfl
lemma nodeIndex_wordNodeEquiv_symm (t : CoreTree) (i : Fin (t.word.length+1)) :
    t.nodeIndex (t.wordNodeEquiv.symm i)=i.val := by
  exact congrArg Fin.val (t.wordNodeEquiv.apply_symm_apply i)

lemma nodePoint_nonroot (t : CoreTree) (ht : 0<t.word.length) (i : Fin t.word.length) :
    t.nodePoint (t.wordNodeEquiv.symm i.succ)=FKCRT.cellPoint t.word.length ht i := by
  apply Subtype.ext
  simp only [nodePoint,t.wordNodeEquiv.apply_symm_apply,Fin.val_succ,FKCRT.cellPoint,Nat.cast_add,Nat.cast_one]

lemma normalized_pole_comparison (t : CoreTree) (v w m : t.Node) (a b : t.Dart)
    (ha : t.pole v=some a) (hb : t.pole w=some b)
    (hm₁ : t.nodeIndex v ≤ t.nodeIndex m) (hm₂ : t.nodeIndex m ≤ t.nodeIndex w)
    (f : t.Node → ℝ) {scale ε : ℝ} (hs : 0 < scale)
    (herr : ∀ u,|scale*(t.routeLength u:ℝ)-f u| ≤ ε)
    (hmin : ∀ u,t.nodeIndex v ≤ t.nodeIndex u → t.nodeIndex u ≤ t.nodeIndex w → f m ≤ f u) :
    |scale*t.realDistance a b-(f v+f w-2*f m)| ≤ 4*scale*(t.maxDegree:ℝ)+4*ε := by
  have he : ∀ u,|(t.routeLength u:ℝ)-(1/scale)*f u| ≤ ε/scale := by
    intro u
    have heq : (t.routeLength u:ℝ)-(1/scale)*f u=(scale*(t.routeLength u:ℝ)-f u)/scale := by
      field_simp
    rw [heq,abs_div,abs_of_pos hs]
    exact div_le_div_of_nonneg_right (herr u) hs.le
  have hh := t.pole_walk_comparison v w m a b ha hb hm₁ hm₂ f
    (α := 1/scale) (ε := ε/scale) (by positivity) he hmin
  calc
    |scale*t.realDistance a b-(f v+f w-2*f m)|=
        |scale*(t.realDistance a b-(1/scale)*(f v+f w-2*f m))| := by
      congr 1
      field_simp
    _=scale*|t.realDistance a b-(1/scale)*(f v+f w-2*f m)| := by rw [abs_mul,abs_of_pos hs]
    _ ≤ scale*(4*(t.maxDegree:ℝ)+4*(ε/scale)) := mul_le_mul_of_nonneg_left hh hs.le
    _=4*scale*(t.maxDegree:ℝ)+4*ε := by field_simp

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory Set
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma exists_positive_index (t : CoreTree) (v : t.Node) (hv : 0<t.nodeIndex v) :
    ∃ i : Fin t.word.length,t.wordNodeEquiv.symm i.succ=v := by
  have hb := (t.wordNodeEquiv v).isLt
  rw [wordNodeEquiv_val] at hb
  let i : Fin t.word.length := ⟨t.nodeIndex v-1,by omega⟩
  refine ⟨i,t.wordNodeEquiv.symm_apply_eq.mpr ?_⟩
  apply Fin.ext
  change t.nodeIndex v-1+1=t.nodeIndex v
  omega

lemma time_distortion_ordered (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (he : ∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d))
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (f : C(unitInterval,ℝ)) {scale ε η : ℝ} (hs : 0 < scale)
    (herr : ∀ v,|scale*(t.routeLength v:ℝ)-f (t.nodePoint v)| ≤ ε)
    (hmod : ∀ s u,dist s u ≤ 1/(t.word.length:ℝ) → |f s-f u| ≤ η)
    (s u : unitInterval) (hsu : s ≤ u) :
    |scale*((FKCRT.graph M Set.univ).dist (t.timeVertex M e ht s)
      (t.timeVertex M e ht u):ℝ)-FKCRT.excursionDist f s u| ≤
        4*scale*(t.maxDegree:ℝ)+4*ε+4*η := by
  let i := FKCRT.timeCell t.word.length ht s
  let j := FKCRT.timeCell t.word.length ht u
  have hij : i ≤ j := FKCRT.timeCell_mono _ ht hsu
  obtain ⟨k,hk,hmin⟩ := Finset.exists_min_image (Finset.Icc i j)
    (fun k => f (FKCRT.cellPoint t.word.length ht k)) ⟨i,Finset.mem_Icc.mpr ⟨le_rfl,hij⟩⟩
  have hki := (Finset.mem_Icc.mp hk).1
  have hkj := (Finset.mem_Icc.mp hk).2
  let v := t.wordNodeEquiv.symm i.succ
  let w := t.wordNodeEquiv.symm j.succ
  let m := t.wordNodeEquiv.symm k.succ
  have hv : t.nodeIndex v=i.val+1 := t.nodeIndex_wordNodeEquiv_symm i.succ
  have hw : t.nodeIndex w=j.val+1 := t.nodeIndex_wordNodeEquiv_symm j.succ
  have hm : t.nodeIndex m=k.val+1 := t.nodeIndex_wordNodeEquiv_symm k.succ
  have hvm : t.nodeIndex v ≤ t.nodeIndex m := by rw [hv,hm];omega
  have hmw : t.nodeIndex m ≤ t.nodeIndex w := by rw [hm,hw];omega
  have hn : t≠leaf := by intro h;subst t;simp [word] at ht
  obtain ⟨a,ha⟩ := t.pole_some_of_ne_leaf hn v
  obtain ⟨b,hb⟩ := t.pole_some_of_ne_leaf hn w
  have hm' : ∀ z,t.nodeIndex v ≤ t.nodeIndex z → t.nodeIndex z ≤ t.nodeIndex w →
      f (t.nodePoint m) ≤ f (t.nodePoint z) := by
    intro z hz₁ hz₂
    obtain ⟨r,hr⟩ := t.exists_positive_index z (by omega)
    subst z
    rw [t.nodePoint_nonroot ht k,t.nodePoint_nonroot ht r]
    apply hmin r
    rw [Finset.mem_Icc]
    simp only [v,w,t.nodeIndex_wordNodeEquiv_symm,Fin.val_succ] at hz₁ hz₂
    constructor <;> omega
  have hd := t.normalized_pole_comparison v w m a b ha hb hvm hmw
    (fun z => f (t.nodePoint z)) hs herr hm'
  have hgrid := FKCRT.sampled_excursion_error t.word.length ht f hmod s u hsu k hki hkj
    (fun r hr₁ hr₂ => hmin r (Finset.mem_Icc.mpr ⟨hr₁,hr₂⟩))
  have hvp : t.nodePoint v=FKCRT.cellPoint t.word.length ht i := t.nodePoint_nonroot ht i
  have hwp : t.nodePoint w=FKCRT.cellPoint t.word.length ht j := t.nodePoint_nonroot ht j
  have hmp : t.nodePoint m=FKCRT.cellPoint t.word.length ht k := t.nodePoint_nonroot ht k
  simp only [hvp,hwp,hmp] at hd
  change |scale*((FKCRT.graph M Set.univ).dist (t.realizedPole M e v)
    (t.realizedPole M e w):ℝ)-FKCRT.excursionDist f s u| ≤ _
  rw [t.realizedPole_some M e v a ha,t.realizedPole_some M e w b hb,
    t.realized_distance_of M e he hp a b]
  exact (abs_sub_le _ _ _).trans (add_le_add hd hgrid)

/-- Uniform measured-space distortion from actual marked ancestral error,
actual largest core, and the modulus of the chosen continuous path. -/
theorem time_distortion (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (he : ∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d))
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (f : C(unitInterval,ℝ)) {scale ε η : ℝ} (hs : 0 < scale)
    (herr : ∀ v,|scale*(t.routeLength v:ℝ)-f (t.nodePoint v)| ≤ ε)
    (hmod : ∀ s u,dist s u ≤ 1/(t.word.length:ℝ) → |f s-f u| ≤ η)
    (s u : unitInterval) :
    |scale*((FKCRT.graph M Set.univ).dist (t.timeVertex M e ht s)
      (t.timeVertex M e ht u):ℝ)-FKCRT.excursionDist f s u| ≤
        4*scale*(t.maxDegree:ℝ)+4*ε+4*η := by
  rcases le_total s u with h | h
  · exact t.time_distortion_ordered M e ht he hp f hs herr hmod s u h
  · rw [SimpleGraph.dist_comm,FKCRT.excursionDist_comm]
    exact t.time_distortion_ordered M e ht he hp f hs herr hmod u s h

/-- The measured comparison is oriented from the fixed continuous-tree
space, precisely as required in the continuity tests. -/
theorem ghp_tree_map_bound (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (he : ∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d))
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (hlen : t.word.length=2*(n+1)) (f : C(unitInterval,ℝ))
    {scale ε η δ : ℝ} (hs : 0 < scale) (hδ : 0<δ)
    (herr : ∀ v,|scale*(t.routeLength v:ℝ)-f (t.nodePoint v)| ≤ ε)
    (hmod : ∀ s u,dist s u ≤ 1/(t.word.length:ℝ) → |f s-f u| ≤ η)
    (hsmall : 4*scale*(t.maxDegree:ℝ)+4*ε+4*η ≤ 2*δ) :
    FKCRT.ghpEDist (FKCRT.treeSpace f) (FKCRT.mapSpace scale M) ≤ ENNReal.ofReal δ := by
  apply FKCRT.ghpEDist_le_of_coding (FKCRT.treeSpace_valid f.continuous)
    (FKCRT.mapSpace_valid hs M) (volume : Measure unitInterval)
    (FKCRT.treeProjection f) (t.timeVertex M e ht)
    (FKCRT.treeProjection_measurable f) (t.timeVertex_measurable M e ht)
    (FKCRT.treeProjection_surjective f) (t.timeVertex_surjective M e ht hp)
    rfl (t.timeVertex_mass M e ht hp hlen) hδ
  intro s u
  change |FKCRT.excursionDist f (FKCRT.treeProjection f s).out (FKCRT.treeProjection f u).out-
    scale*((FKCRT.graph M Set.univ).dist _ _:ℝ)| ≤ _
  rw [FKCRT.excursionDist_out f.continuous,abs_sub_comm]
  exact (t.time_distortion M e ht he hp f hs herr hmod s u).trans hsmall

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_GHPBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory.CoreTree
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma nodePoint_gridPoint (t : CoreTree) (v : t.Node) :
    t.nodePoint v=gridPoint t.labels.length ⟨t.nodeIndex v,(t.nodeIndex_bound v).trans_le (Nat.le_succ _)⟩ := by
  apply Subtype.ext
  simp only [nodePoint,wordNodeEquiv_val,gridPoint,labels_length,Nat.cast_add,Nat.cast_one]

lemma heightCode_nodePoint (p : CriticalEvenOffspring) (t : CoreTree) (v : t.Node) :
    heightCode p t.toCode (t.nodePoint v)=p.sigma*(t.depth v:ℝ)/(2*Real.sqrt t.labels.length) := by
  rw [nodePoint_gridPoint,heightCode,interpolation_gridPoint (List.length_pos_iff.mpr t.labels_nonempty),← depth_height]

/-- Normalized marked error is evaluated at exactly the same coding mesh. -/
lemma route_heightCode_fit (p : CriticalEvenOffspring) (t : CoreTree) (β scale a : ℝ)
    (hs : 0 ≤ scale)
    (herr : ∀ v,|(t.routeLength v:ℝ)-β*t.depth v| ≤ a*Real.sqrt t.labels.length) :
    ∀ v,|scale*(t.routeLength v:ℝ)-
      ((scale*β*2*Real.sqrt t.labels.length/p.sigma) • heightCode p t.toCode) (t.nodePoint v)| ≤
        scale*a*Real.sqrt t.labels.length := by
  intro v
  rw [ContinuousMap.smul_apply,smul_eq_mul,heightCode_nodePoint]
  have hσ := p.sigma_pos
  have hn : 0<Real.sqrt (t.labels.length:ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast List.length_pos_iff.mpr t.labels_nonempty)
  have he : scale*(t.routeLength v:ℝ)-
      (scale*β*2*Real.sqrt t.labels.length/p.sigma)*(p.sigma*(t.depth v:ℝ)/(2*Real.sqrt t.labels.length))=
        scale*((t.routeLength v:ℝ)-β*t.depth v) := by field_simp
  rw [he,abs_mul,abs_of_nonneg hs]
  exact (mul_le_mul_of_nonneg_left (herr v) hs).trans_eq (by ring)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory.CoreTree
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma code_marks_of_labels (t : CoreTree) (x : MarkedCode t.labels.length)
    (hx : t.labels=List.ofFn x.val.2) :
    t.toCode=x.val.1 ∧ (fun i : Fin t.labels.length => t.labels[i.val])=x.val.2 := by
  have ha : (fun i : Fin t.labels.length => t.labels[i.val])=x.val.2 := by
    funext i
    have hd := congrArg (fun l : List CoreLabel => l[i.val]?) hx
    rw [List.getElem?_eq_getElem i.isLt,List.getElem?_ofFn,dite_eq_left i.isLt] at hd
    exact Option.some.inj hd
  refine ⟨?_,ha⟩
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (t.labels[i.val]).arity=(x.val.1.val i).val
  rw [show t.labels[i.val]=x.val.2 i from congrFun ha i,x.property]

lemma marked_route_error {N : ℕ} (x : MarkedCode N) (β R : ℝ)
    (h : ∀ j : Fin N,|markedSpineSum coreIncrement x.val.1 j.isLt.le x.val.2-
      β*height x.val.1.val j.val| ≤ R) :
    ∀ v : (ofMarkedCode x).Node,
      |((ofMarkedCode x).routeLength v:ℝ)-β*(ofMarkedCode x).depth v| ≤ R := by
  generalize ht : ofMarkedCode x=t at *
  have hs := ofMarkedCode_size x
  rw [ht] at hs
  subst N
  have hl := ofMarkedCode_labels x
  rw [ht] at hl
  obtain ⟨hd,ha⟩ := code_marks_of_labels t x hl
  intro v
  rw [routeLength_marked,depth_height,hd,ha]
  exact h ⟨t.nodeIndex v,t.nodeIndex_bound v⟩

lemma marked_heightCode {N : ℕ} (p : CriticalEvenOffspring) (x : MarkedCode N) :
    heightCode p (ofMarkedCode x).toCode=heightCode p x.val.1 := by
  generalize ht : ofMarkedCode x=t
  have hs := ofMarkedCode_size x
  rw [ht] at hs
  subst N
  have hl := ofMarkedCode_labels x
  rw [ht] at hl
  rw [(code_marks_of_labels t x hl).1]

lemma ofMarkedCode_word_successful (n : ℕ) (x : MarkedCode (2*(n+1)+1)) :
    (ofMarkedCode x).word=List.ofFn ((successfulMarkedEquiv n).symm x).val := by
  have h := successfulMarked_word n ((successfulMarkedEquiv n).symm x)
  rw [(successfulMarkedEquiv n).apply_symm_apply] at h
  exact h

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma crtScale_pos (P : Parameters) : 0 < crtScale P :=
  div_pos (actualOffspring P).sigma_pos (by have h := metricMean_pos P; positivity)

lemma edgeScale_pos (P : Parameters) (n : ℕ) : 0<edgeScale P n :=
  div_pos (crtScale_pos P) (Real.sqrt_pos.mpr (by positivity))

lemma heightFactor_pos (n : ℕ) : 0<heightFactor n := Real.sqrt_pos.mpr (by positivity)
lemma heightFactor_tendsto : Tendsto heightFactor atTop (𝓝 1) := by
  have hh : Tendsto (fun n : ℕ => 1/(2*((n:ℝ)+1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num))
  have hs := ((tendsto_const_nhds.add hh (a := (1:ℝ))).sqrt)
  change Tendsto (fun n : ℕ => Real.sqrt (1+1/(2*((n:ℝ)+1)))) atTop (𝓝 1)
  simpa only [add_zero,Real.sqrt_one] using hs

lemma sqrt_size_ratio (n : ℕ) :
    Real.sqrt ((2*(n+1)+1:ℕ):ℝ)=heightFactor n*Real.sqrt 2*Real.sqrt ((n:ℝ)+1) := by
  have hn : 0 ≤ (n:ℝ)+1 := by positivity
  have hh : 0 ≤ 1+1/(2*((n:ℝ)+1)) := by positivity
  have h₁ := Real.sq_sqrt (show 0 ≤ ((2*(n+1)+1:ℕ):ℝ) by positivity)
  have h₂ := Real.sq_sqrt hh
  have h₃ := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h₄ := Real.sq_sqrt hn
  have he : (heightFactor n*Real.sqrt 2*Real.sqrt ((n:ℝ)+1))^2=((2*(n+1)+1:ℕ):ℝ) := by
    rw [mul_pow,mul_pow,h₃,h₄]
    change (Real.sqrt (1+1/(2*((n:ℝ)+1))))^2*2*((n:ℝ)+1)=_
    rw [h₂]
    push_cast
    field_simp
  nlinarith [Real.sqrt_nonneg ((2*(n+1)+1:ℕ):ℝ),show 0 ≤ heightFactor n*Real.sqrt 2*Real.sqrt ((n:ℝ)+1) by
    exact mul_nonneg (mul_nonneg (heightFactor_pos n).le (Real.sqrt_nonneg 2)) (Real.sqrt_nonneg _)]

lemma edgeScale_heightFactor (P : Parameters) (n : ℕ) :
    edgeScale P n*metricMean P*2*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)/(actualOffspring P).sigma=heightFactor n := by
  rw [sqrt_size_ratio]
  have hσ := (actualOffspring P).sigma_pos
  have hβ := metricMean_pos P
  have h₂ : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hn : 0<Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  unfold edgeScale crtScale
  field_simp

lemma edgeScale_sqrt_size_tendsto (P : Parameters) :
    Tendsto (fun n => edgeScale P n*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)) atTop
      (𝓝 ((actualOffspring P).sigma/(2*metricMean P))) := by
  have he (n : ℕ) : edgeScale P n*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)=
      heightFactor n*((actualOffspring P).sigma/(2*metricMean P)) := by
    have h := edgeScale_heightFactor P n
    have hσ := (actualOffspring P).sigma_pos
    have hβ := metricMean_pos P
    field_simp at h ⊢
    nlinarith
  simp_rw [he]
  simpa only [one_mul] using heightFactor_tendsto.mul_const ((actualOffspring P).sigma/(2*metricMean P))

end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology NNReal
namespace FKCRT.Inventory.CoreTree
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- The same measured relation compares to a nearby deterministic path;
this avoids presuming a triangle inequality for the presentation distance. -/
theorem marked_nearby_ghp_bound (P : Parameters) (n : ℕ)
    (x : MarkedCode (2*(n+1)+1)) (f : C(unitInterval,ℝ)) (a r η δ : ℝ) (hδ : 0<δ)
    (herr : ∀ j : Fin (2*(n+1)+1),
      |markedSpineSum coreIncrement x.val.1 j.isLt.le x.val.2-metricMean P*height x.val.1.val j.val| ≤
        a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ))
    (hprox : dist (actualHeight P n x.val) f ≤ r)
    (hmod : ∀ s u,dist s u ≤ 1/(2*((n:ℝ)+1)) → |f s-f u| ≤ η)
    (hsmall : 4*edgeScale P n*((ofMarkedCode x).maxDegree:ℝ)+
      4*(edgeScale P n*a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)+r)+4*η ≤ 2*δ) :
    FKCRT.ghpEDist (FKCRT.treeSpace f)
      (FKCRT.mapSpace (edgeScale P n) ((FKCRT.rootedWordEquiv n).symm
        ((successfulMarkedEquiv n).symm x)).1) ≤ ENNReal.ofReal δ := by
  let t := ofMarkedCode x
  have hsize := ofMarkedCode_size x
  have hw := ofMarkedCode_word_successful n x
  have hlen : t.word.length=2*(n+1) := by rw [hw,List.length_ofFn]
  have he : ∀ v : t.Node,|(t.routeLength v:ℝ)-metricMean P*t.depth v| ≤ a*Real.sqrt t.labels.length := by
    rw [hsize]
    exact marked_route_error x _ _ herr
  have hpath : ((edgeScale P n*metricMean P*2*Real.sqrt t.labels.length/(actualOffspring P).sigma) •
      heightCode (actualOffspring P) t.toCode)=actualHeight P n x.val := by
    simp only [t,hsize,marked_heightCode,edgeScale_heightFactor,actualHeight]
  have hfit := t.route_heightCode_fit (actualOffspring P) (metricMean P) (edgeScale P n) a
    (edgeScale_pos P n).le he
  rw [hpath] at hfit
  have hb : ∀ v : t.Node,|edgeScale P n*(t.routeLength v:ℝ)-f (t.nodePoint v)| ≤
      edgeScale P n*a*Real.sqrt t.labels.length+r := by
    intro v
    have hp := (ContinuousMap.dist_apply_le_dist (f := actualHeight P n x.val) (g := f) (t.nodePoint v)).trans hprox
    rw [Real.dist_eq] at hp
    exact (abs_sub_le _ _ _).trans (add_le_add (hfit v) hp)
  obtain ⟨e,he',hp⟩ := t.realized_intertwine _ hw
  apply t.ghp_tree_map_bound _ e (by omega) he' hp hlen f (edgeScale_pos P n) hδ hb
  · intro s u hsu
    apply hmod s u
    simpa only [hlen,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hsu
  · simpa only [t,hsize] using hsmall

end FKCRT.Inventory.CoreTree
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- Local deterministic stability at every continuous limit path. This is
the missing compact-cover interface, with the original map, exact degree
mass, positive source normalization, and true bad events. -/
theorem metric_test_local_oai (P : Parameters) (F : FKCRT.MetricMeasureData → ℝ)
    (hF : FKCRT.IsGHPTest F) (ε : ℝ) (hε : 0<ε) (f : C(unitInterval,ℝ)) :
    ∃ r : ℝ,0 < r ∧ ∃ a : ℝ,0<a ∧ ∃ N : ℕ,∀ n≥N,∀ x : ActualDraw n,
      dist (actualHeight P n x) f < r → x∉metricBad P n a →
      |FKCRT.markedMapTest (edgeScale P n) n F x-F (FKCRT.treeSpace (actualHeight P n x))| ≤ ε := by
  obtain ⟨δ,hδ,hcont⟩ := hF.2 (FKCRT.treeSpace f) (FKCRT.treeSpace_valid f.continuous) (ε/2) (half_pos hε)
  obtain ⟨r₀,hr₀,hG⟩ := Metric.continuousAt_iff.mp (hF.continuous_treeSpace.continuousAt (x := f)) (ε/2) (half_pos hε)
  let L := (actualOffspring P).sigma/(2*metricMean P)+1
  have hL : 0<L := by dsimp [L];have hβ := metricMean_pos P;have hσ := (actualOffspring P).sigma_pos; positivity
  let r := min r₀ (δ/16)
  let a := δ/(32*(L+1))
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have ha : 0<a := by dsimp [a];positivity
  have hLbound : ∀ᶠ n in atTop,edgeScale P n*Real.sqrt ((2*(n+1)+1:ℕ):ℝ) ≤ L := by
    exact ((edgeScale_sqrt_size_tendsto P).eventually (gt_mem_nhds (by dsimp [L];linarith))).mono (fun _ h => h.le)
  obtain ⟨ζ,hζ,hmod⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) (δ/16) (by positivity)
  have hmesh : Tendsto (fun n : ℕ => 1/(2*((n:ℝ)+1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hLbound.and (hmesh.eventually (gt_mem_nhds hζ)))
  refine ⟨r,hr,a,ha,N,?_⟩
  intro n hn x hx hbad
  have hcompat : ∀ i,(x.2 i).arity=(x.1.val i).val := by
    by_contra hc
    exact hbad (Or.inl (Or.inl hc))
  let y : CoreTree.MarkedCode (2*(n+1)+1) := ⟨x,hcompat⟩
  have hcore : ((CoreTree.ofMarkedCode y).maxDegree:ℝ) ≤ a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ) := by
    by_contra hc
    exact hbad (Or.inl (Or.inr ⟨hcompat,lt_of_not_ge hc⟩))
  have herr : ∀ j : Fin (2*(n+1)+1),|markedSpineSum coreIncrement x.1 j.isLt.le x.2-
      metricMean P*height x.1.val j.val| ≤ a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ) := by
    intro j
    by_contra hc
    exact hbad (Or.inr ⟨j,lt_of_not_ge hc⟩)
  have hghp := CoreTree.marked_nearby_ghp_bound P n y f a r (δ/16) (δ/2) (half_pos hδ) herr hx.le
    (fun s u hsu => by
      have hh := hmod (hsu.trans_lt (hN n hn).2)
      simpa only [Real.dist_eq] using hh.le) ?_
  · have htest := hcont _ (FKCRT.mapSpace_valid (edgeScale_pos P n) _)
      (hghp.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (half_lt_self hδ)))
    have htree := hG (hx.trans_le (min_le_left _ _))
    rw [Real.dist_eq] at htree
    rw [FKCRT.markedMapTest,dite_eq_left hcompat]
    have ht := abs_sub_le
      (F (FKCRT.mapSpace (edgeScale P n) ((FKCRT.rootedWordEquiv n).symm ((CoreTree.successfulMarkedEquiv n).symm y)).1))
      (F (FKCRT.treeSpace f)) (F (FKCRT.treeSpace (actualHeight P n x)))
    rw [abs_sub_comm (F (FKCRT.treeSpace f))] at ht
    linarith
  have hb₁ := mul_le_mul_of_nonneg_left hcore (edgeScale_pos P n).le
  have hb₂ := mul_le_mul_of_nonneg_left (hN n hn).1 ha.le
  have har : 8*a*L≤δ/4 := by
    have hh : a*(32*(L+1))=δ := by
      dsimp [a]
      field_simp
    nlinarith [mul_nonneg ha.le hL.le]
  have hrδ : r≤δ/16 := min_le_right _ _
  nlinarith

end FKCRT.Inventory
end

end OAI
end

theorem solution : type_of% @OAI.FKCRT.Inventory.metric_test_local_oai := @OAI.FKCRT.Inventory.metric_test_local_oai
