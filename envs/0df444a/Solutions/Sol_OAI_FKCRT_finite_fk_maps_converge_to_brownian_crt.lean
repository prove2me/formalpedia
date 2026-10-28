-- Prove2me | solution 1 for OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T18:47:01.235155+00:00
-- url     : https://prove2.me/submissions/0e176c49-20a8-4b80-9910-05fb8b990220

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_OAIQ021F004
import Theorems.Thm_OAI_FKCRT_Inventory_actual_map_tests

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
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSingletonClassCode _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma rotateBridge_add {N : ℕ} [NeZero N] (a b : Fin N) (d : Bridge N) :
    rotateBridge a (rotateBridge b d) = rotateBridge (a+b) d := by
  apply Subtype.ext
  funext i
  simp [rotateBridge, rotateDegrees, add_assoc]


lemma goodRotation_of_code {N : ℕ} [NeZero N] (d : Bridge N)
    (hd : IsTreeCode d.val) : goodRotation d = 0 := by
  apply d.unique_good_rotation.unique (goodRotation_spec d)
  simpa using hd


@[simp] lemma canonicalCode_of_code {N : ℕ} [NeZero N] (d : Code N) :
    canonicalCode (⟨d.val, d.property.1⟩ : Bridge N) = d := by
  apply Subtype.ext
  change (rotateBridge (goodRotation ⟨d.val, d.property.1⟩) _).val = d.val
  rw [goodRotation_of_code _ d.property, rotateBridge_zero]


lemma goodRotation_add {N : ℕ} [NeZero N] (d : Bridge N) (m : Fin N) :
    goodRotation (rotateBridge m d) + m = goodRotation d := by
  apply d.unique_good_rotation.unique _ (goodRotation_spec d)
  rw [← rotateBridge_add]
  exact goodRotation_spec (rotateBridge m d)


@[simp] lemma canonicalCode_rotate {N : ℕ} [NeZero N] (d : Bridge N) (m : Fin N) :
    canonicalCode (rotateBridge m d) = canonicalCode d := by
  apply Subtype.ext
  change (rotateBridge _ (rotateBridge m d)).val = (rotateBridge _ d).val
  rw [rotateBridge_add, goodRotation_add]


theorem canonicalCode_weighted_sum (p : CriticalEvenOffspring)
    {N : ℕ} [NeZero N] (F : Code N → ℝ) :
    ∑ d : Bridge N, bridgeWeight p d * F (canonicalCode d) =
      (N : ℝ) * ∑ d : Code N, codeWeight p d * F d := by
  classical
  have h := weighted_unique_rotation (rotateBridge (N := N))
    (fun d => bridgeWeight p d * F (canonicalCode d))
    (fun d => IsTreeCode d.val)
    (fun m d => by rw [bridgeWeight_rotate, canonicalCode_rotate])
    (fun d => d.unique_good_rotation)
  rw [Fintype.card_fin] at h
  rw [h]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun d : Bridge N => IsTreeCode d.val) _ (by simp)]
  let e : Code N ≃ {d : Bridge N // IsTreeCode d.val} := {
    toFun := fun d => ⟨⟨d.val, d.property.1⟩, d.property⟩
    invFun := fun d => ⟨d.val.val, d.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro d _
  change bridgeWeight p ⟨d.val, d.property.1⟩ *
    F (canonicalCode ⟨d.val, d.property.1⟩) = codeWeight p d * F d
  rw [canonicalCode_of_code]
  rfl


theorem canonicalCode_expectation (p : CriticalEvenOffspring) (n : ℕ)
    (F : Code (2*n+1) → ℝ) :
    ∑ d : Bridge (2*n+1), (bridgeWeight p d / bridgePartition p (2*n+1)) *
      F (canonicalCode d) =
    ∑ d : Code (2*n+1), (codeWeight p d / codePartition p (2*n+1)) * F d := by
  let : NeZero (2*n+1) := ⟨by omega⟩
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div, canonicalCode_weighted_sum,
    codePartition_cyclic p (by omega)]
  rw [mul_div_mul_left _ _ (by positivity : ((2*n+1 : ℕ) : ℝ) ≠ 0)]


lemma CriticalEvenOffspring.iid_bridge_singleton (p : CriticalEvenOffspring)
    {N : ℕ} (b : Bridge N) :
    (p.iidLaw N).real {bridgeEmbedding N b} = bridgeWeight p b := by
  rw [measureReal_def, iidLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [p.law_singleton, ENNReal.toReal_ofReal (p.nonneg _)]
  rfl


lemma CriticalEvenOffspring.bridge_integral_eq (p : CriticalEvenOffspring) (N : ℕ)
    (F : (Fin N → ℕ) → ℝ) :
    ∫ d, F d ∂cond (p.iidLaw N) {d | totalStep d = -1} =
      ∑ b : Bridge N, (bridgeWeight p b / bridgePartition p N) * F (bridgeEmbedding N b) := by
  classical
  have hset : {d : Fin N → ℕ | totalStep d = -1} = ⋃ b : Bridge N, {bridgeEmbedding N b} := by
    rw [totalStep_bridge_range]
    ext d
    simp
  have hdis : Pairwise (fun b c : Bridge N => Disjoint ({bridgeEmbedding N b} : Set (Fin N → ℕ))
      {bridgeEmbedding N c}) := by
    intro b c hbc
    exact Set.disjoint_singleton.mpr ((bridgeEmbedding N).injective.ne hbc)
  have hi (b : Bridge N) : IntegrableOn F {bridgeEmbedding N b} (p.iidLaw N) :=
    IntegrableOn.of_finite (Set.finite_singleton _)
  rw [ProbabilityTheory.cond,integral_smul_measure,hset,integral_iUnion_fintype (fun _ => measurableSet_singleton _) hdis hi]
  simp only [integral_singleton,smul_eq_mul,ENNReal.toReal_inv]
  rw [← hset,← measureReal_def,← p.bridgePartition_eq_iid,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [p.iid_bridge_singleton]
  ring


lemma bridgeFromArray_spec {N : ℕ} (d : Fin N → ℕ) (hd : totalStep d = -1) :
    bridgeEmbedding N (bridgeFromArray d hd)=d :=
  ((totalStep_bridge_range N) ▸ hd : d ∈ Set.range (bridgeEmbedding N)).choose_spec


@[simp] lemma bridgeFromArray_embedding {N : ℕ} (b : Bridge N) (hd : totalStep (bridgeEmbedding N b) = -1) :
    bridgeFromArray (bridgeEmbedding N b) hd=b := by
  exact (bridgeEmbedding N).injective (bridgeFromArray_spec _ _)


lemma arrayTree_embedding (n : ℕ) (b : Bridge (2*n+1)) :
    arrayTree n (bridgeEmbedding (2*n+1) b)=canonicalCode b := by
  simp [arrayTree,totalStep_bridge]


theorem CriticalEvenOffspring.arrayTree_expectation (p : CriticalEvenOffspring)
    (n : ℕ) (F : Code (2*n+1) → ℝ) :
    ∫ d, F (arrayTree n d) ∂cond (p.iidLaw (2*n+1)) {d | totalStep d = -1} =
      ∑ b : Code (2*n+1), (codeWeight p b / codePartition p (2*n+1))*F b := by
  rw [p.bridge_integral_eq]
  simp only [arrayTree_embedding]
  exact canonicalCode_expectation p n F


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
-- module Solutions.OAIQ021_FK.FKMaps_HeightBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.code_integral (p : CriticalEvenOffspring) (n : ℕ)
    (F : Code (2*n+1) → ℝ) :
    (∫ d,F d ∂p.codeLaw n)=∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1))*F d := by
  rw [codeLaw,integral_map (measurable_of_countable (arrayTree n)).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable]
  exact p.arrayTree_expectation n F

end FKCRT.TreeCoding
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

lemma fkWeight_pos {n : ℕ} {q : ℝ} (hq : 0 < q) (M : RootedMap n)
    (A : Finset (Edge M)) : 0 < fkWeight q M A := Real.rpow_pos_of_pos hq _

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MapEncoding
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT

lemma partition_pos {q : ℝ} (hq : 0<q) (n : ℕ) : 0<partition q n := by
  classical
  unfold partition
  apply Finset.sum_pos
  · intro M _
    apply Finset.sum_pos
    · intro A _
      exact fkWeight_pos hq M A
    · exact Finset.univ_nonempty
  · exact Finset.univ_nonempty

end FKCRT
end



/-! The exact edge-reversal tour of the rotation-system maps. -/



/-! A genuine multigraph spanning tree has one complete edge-reversal tour.
This is the converse direction of the source's finite encoding, proved
without invoking a topological thickening or assuming planarity. -/



/-! Exact reconstruction in the rotation-system convention. The
Euler equalities on the two coloured matchings are equivalent to their
noncrossing property; maximum orbit counts are proved for stack matchings
in `WorkNoncrossing`, rather than postulated for a map. -/

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Matching
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.Inventory.instMeasurableSingletonClassListOrder _root_.OAI.FKCRT.Inventory.instMeasurableSingletonClassOrder _root_.OAI.FKCRT.Inventory.instMeasurableSpaceListOrder _root_.OAI.FKCRT.Inventory.instMeasurableSpaceOrder _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
variable {N : ℕ}

lemma mem_liveAt (a : Perm (Fin N)) (k : ℕ) (x : Fin N) :
    x∈liveAt a k ↔ x.val<k ∧ k≤(a x).val := by simp [liveAt]

lemma liveAt_sorted (a : Perm (Fin N)) (k : ℕ) : (liveAt a k).Pairwise (·>·) := by
  exact ((List.pairwise_lt_finRange N).filter _).reverse

lemma liveAt_zero (a : Perm (Fin N)) : liveAt a 0=[] := by simp [liveAt]

lemma liveAt_open (a : Perm (Fin N)) (ha : Function.Involutive a) (i : Fin N)
    (hi : i < a i) : liveAt a (i.val+1)=i::liveAt a i.val := by
  have hs : (i::liveAt a i.val).Pairwise (·>·) :=
    List.pairwise_cons.mpr ⟨fun x hx => (mem_liveAt a i.val x).mp hx |>.1,liveAt_sorted a _⟩
  apply List.Pairwise.eq_of_mem_iff (liveAt_sorted a _) hs
  intro x
  rw [mem_liveAt,List.mem_cons,mem_liveAt]
  have hx : a x=i → x=a i := fun h => by rw [← h,ha]
  constructor
  · rintro ⟨h1,h2⟩
    by_cases hxi : x=i
    · exact Or.inl hxi
    · exact Or.inr ⟨by have := Fin.val_ne_of_ne hxi; omega,by omega⟩
  · rintro (rfl|⟨h1,h2⟩)
    · exact ⟨by omega,hi⟩
    · refine ⟨by omega,?_⟩
      by_contra hh
      have he : a x=i := Fin.ext (by omega)
      have he' := hx he
      subst x
      have hi' : i.val<(a i).val := hi
      omega

lemma liveAt_close (a : Perm (Fin N)) (ha : Function.Involutive a) (i : Fin N)
    (hi : a i < i) : liveAt a (i.val+1)=(liveAt a i.val).erase (a i) := by
  apply List.Pairwise.eq_of_mem_iff (liveAt_sorted a _) ((liveAt_sorted a _).sublist List.erase_sublist)
  intro x
  rw [mem_liveAt,(liveAt_sorted a _).nodup.mem_erase_iff,mem_liveAt]
  have hx : x=a i ↔ a x=i := by
    constructor
    · intro h; rw [h,ha]
    · intro h; rw [← h,ha]
  have hi' : (a i).val < i.val := hi
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨?_,?_,by omega⟩
    · intro he; have := hx.mp he; subst x; rw [ha] at h2; omega
    · by_contra h
      have he : x=i := Fin.ext (by omega)
      subst x
      omega
  · rintro ⟨h1,h2,h3⟩
    refine ⟨by omega,?_⟩
    by_contra h
    have he : a x=i := Fin.ext (by omega)
    exact h1 (hx.mpr he)

lemma liveAt_mate (a : Perm (Fin N)) (ha : Function.Involutive a) (i : Fin N)
    (hi : a i < i) : a i∈liveAt a i.val := by rw [mem_liveAt,ha]; exact ⟨hi,le_rfl⟩

lemma pop_map_erase {α : Type*} [DecidableEq α] (c : α→Bool) (s : List α) (x : α)
    (hx : x∈s) (hfirst : ∀ t u,s=t++x::u → ∀ y∈t,c y≠c x) :
    pop (some (c x)) (s.map c)=some ((s.erase x).map c) := by
  induction s with
  | nil => simp at hx
  | cons y s ih =>
    by_cases hy : y=x
    · subst y; simp [pop,eligible]
    · have hxs : x∈s := List.mem_of_ne_of_mem (Ne.symm hy) hx
      obtain ⟨t,u,htu⟩ := List.mem_iff_append.mp hxs
      have hcy := hfirst (y::t) u (by rw [htu]; rfl) y (by simp)
      have hh := ih hxs (by
        intro t u he z hz
        exact hfirst (y::t) u (by rw [he]; rfl) z (List.mem_cons_of_mem y hz))
      simp [pop,eligible,Ne.symm hcy,hy,hh]

/-- For noncrossing same-colour arcs, the literal typed stack is the list of
live openers in reverse chronological order. No choice of a stack matching
is assumed. -/
lemma matching_step_live (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ x,a x≠x) (c : Fin N→Bool) (hc : ∀ x,c (a x)=c x)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False) (i : Fin N) :
    stackTypedStep ((liveAt a i.val).map c)
      (if i < a i then .burger (c i) else .order (c i))=
        some ((liveAt a (i.val+1)).map c) := by
  by_cases hi : i < a i
  · rw [ite_eq_left hi,liveAt_open a ha i hi]
    rfl
  · have hlt : a i < i := lt_of_le_of_ne (le_of_not_gt hi) (hf i)
    rw [ite_eq_right hi,stackTypedStep,liveAt_close a ha i hlt,← hc i]
    apply pop_map_erase c _ _ (liveAt_mate a ha i hlt)
    intro t u he y hy hcy
    have hs := liveAt_sorted a i.val
    rw [he,List.pairwise_append] at hs
    have hiy : a i<y := hs.2.2 y hy (a i) (by simp)
    have hym : y∈liveAt a i.val := he ▸ List.mem_append_left _ hy
    obtain ⟨hy1,hy2⟩ := (mem_liveAt a i.val y).mp hym
    have hneq : a y≠i := fun hh => (ne_of_lt hiy) (by rw [← hh,ha])
    have hy3 : i < a y := by have := Fin.val_ne_of_ne hneq; change (i : ℕ)<(a y : ℕ); omega
    exact hn (a i) y hcy.symm hiy (by rwa [ha]) (by rwa [ha])

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
variable {N : ℕ}

lemma liveAt_first_colour (a : Perm (Fin N)) (ha : Function.Involutive a)
    (c : Fin N→Bool)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False)
    (i : Fin N) (_hi : a i < i) :
    ∀ t u,liveAt a i.val=t++a i::u → ∀ y∈t,c y≠c (a i) := by
  intro t u he y hy hcy
  have hs := liveAt_sorted a i.val
  rw [he,List.pairwise_append] at hs
  have hiy : a i < y := hs.2.2 y hy (a i) (by simp)
  have hym : y∈liveAt a i.val := he ▸ List.mem_append_left _ hy
  obtain ⟨hy1,hy2⟩ := (mem_liveAt a i.val y).mp hym
  have hneq : a y≠i := fun hh => (ne_of_lt hiy) (by rw [← hh,ha])
  have hy3 : i < a y := by have := Fin.val_ne_of_ne hneq; change (i : ℕ)<(a y : ℕ); omega
  exact hn (a i) y hcy.symm hiy (by rwa [ha]) (by rwa [ha])

lemma head_map_eq_of_first {α : Type*} (c : α→Bool) (s : List α) (x : α)
    (hx : x∈s) (hfirst : ∀ t u,s=t++x::u → ∀ y∈t,c y≠c x) :
    (s.map c).head?=some (c x) ↔ s.head?=some x := by
  obtain ⟨t,u,rfl⟩ := List.mem_iff_append.mp hx
  cases t with
  | nil => simp
  | cons y t =>
    have hh := hfirst (y::t) u rfl y (by simp)
    have hy : y≠x := fun he => hh (congrArg c he)
    simp [hh,hy]

lemma head_eq_iff_greatest {α : Type*} [LinearOrder α] (s : List α)
    (hs : s.Pairwise (·>·)) (x : α) (hx : x∈s) :
    s.head?=some x ↔ ∀ y∈s,y≤x := by
  cases s with
  | nil => simp at hx
  | cons z s =>
    simp only [List.head?_cons,Option.some.injEq]
    constructor
    · rintro rfl y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact le_rfl
      · exact ((List.pairwise_cons.mp hs).1 y hy).le
    · intro hh
      have hz := hh z (by simp)
      rcases List.mem_cons.mp hx with rfl|hx
      · rfl
      · exact False.elim (not_lt_of_ge hz ((List.pairwise_cons.mp hs).1 x hx))

/-- The source's flexible-mark obstruction, with the strict first-occurrence
order and both closing endpoints retained exactly. -/
theorem flexibleClosing_iff_no_later_cross (a : Perm (Fin N)) (ha : Function.Involutive a)
    (c : Fin N→Bool) (hc : ∀ x,c (a x)=c x)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False)
    (i : Fin N) (hi : a i < i) :
    flexibleClosing ((liveAt a i.val).map c) (.order (c i)) ↔
      ¬∃ j : Fin N,a i < j ∧ j < i ∧ i < a j := by
  change (List.map c (liveAt a i.val)).head?=some (c i) ↔ _
  rw [← hc i,head_map_eq_of_first c _ _ (liveAt_mate a ha i hi)
    (liveAt_first_colour a ha c hn i hi),
    head_eq_iff_greatest _ (liveAt_sorted a _) _ (liveAt_mate a ha i hi)]
  constructor
  · intro hh ⟨j,h1,h2,h3⟩
    exact not_lt_of_ge (hh j ((mem_liveAt a _ j).mpr ⟨h2,h3.le⟩)) h1
  · intro hh j hj
    by_contra h
    obtain ⟨h2,h3⟩ := (mem_liveAt a _ j).mp hj
    have h1 : a i < j := lt_of_not_ge h
    have hne : a j≠i := fun he => (ne_of_lt h1) (by rw [← he,ha])
    have h4 : i < a j := by have := Fin.val_ne_of_ne hne; change i.val<(a j).val; omega
    exact hh ⟨j,h1,h2,h4⟩

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

lemma flexibleCount_ofFn {N : ℕ} (w : Fin N→TypedLetter) (S : Fin (N+1)→List Bool)
    (hs : ∀ i,stackTypedStep (S i.castSucc) (w i)=some (S i.succ)) :
    flexibleCount (List.ofFn w) (S 0)=
      ∑ i,if flexibleClosing (S i.castSucc) (w i) then 1 else 0 := by
  induction N with
  | zero => simp [flexibleCount]
  | succ N ih =>
    have h0 := hs 0
    simp only [Fin.castSucc_zero] at h0
    rw [List.ofFn_succ,flexibleCount,h0,Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero]
    congr 1
    exact ih (fun i => w i.succ) (fun i => S i.succ) (fun i => hs i.succ)

/-- The complete flexible exponent of the actual identified word is the
number of its matched pairs with no later-first crossing edge. -/
theorem matching_flexibleCount {N : ℕ} (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ x,a x≠x) (c : Fin N→Bool) (hc : ∀ x,c (a x)=c x)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False) :
    flexibleCount (List.ofFn (fun i => if i<a i then .burger (c i) else .order (c i))) []=
      ∑ i : Fin N,if a i < i ∧ ¬∃ j : Fin N,a i < j ∧ j < i ∧ i < a j then 1 else 0 := by
  let w : Fin N→TypedLetter := fun i => if i<a i then .burger (c i) else .order (c i)
  let S : Fin (N+1)→List Bool := fun i => (liveAt a i.val).map c
  have hs : ∀ i,stackTypedStep (S i.castSucc) (w i)=some (S i.succ) :=
    matching_step_live a ha hf c hc hn
  have hS : S 0=[] := by simp [S,liveAt_zero]
  rw [← hS,flexibleCount_ofFn w S hs]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i<a i
  · have hn' : ¬a i < i := not_lt_of_ge hi.le
    simp [w,hi,flexibleClosing,hn']
  · have hlt : a i < i := lt_of_le_of_ne (le_of_not_gt hi) (hf i)
    have hh := flexibleClosing_iff_no_later_cross a ha c hc hn i hlt
    change (if flexibleClosing ((liveAt a i.val).map c)
      (if i<a i then .burger (c i) else .order (c i)) then 1 else 0)=_
    simp only [ite_eq_right hi,hh,hlt,true_and]

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
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma StackMatching.unique_first {w : α → TypedLetter} {l : List α}
    (M D : StackMatching w l) (hn : l.Nodup) : turns M.first=turns D.first := by
  obtain ⟨hE,_hF⟩ := typed_matchings_unique w l hn M.first M.second D.first D.second
    M.first_arches M.second_arches D.first_arches D.second_arches M.covers D.covers
    M.first_types M.second_types D.first_types D.second_types
  exact turns_perm hE ((M.covers.nodup_iff.mpr hn).sublist (by
    rw [endpoints_append];exact List.sublist_append_left _ _))

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSingletonClass _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSpace _root_.OAI.FKCRT.Inventory.CoreTree.instDecidableEqDart _root_.OAI.FKCRT.Inventory.CoreTree.instDecidableEqNode _root_.OAI.FKCRT.Inventory.CoreTree.instFintypeDart _root_.OAI.FKCRT.Inventory.CoreTree.instFintypeNode _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreTree

/-- Exact cancellation of the τ powers, including every leaf. This is the
pointwise branching density, not merely a generating-function identity. -/
theorem productMass_eq (t r τ : ℝ) (hτ : τ≠0) (T : CoreTree) :
    T.productMass t r τ=wordMonomial t r T.word/τ := by
  induction T with
  | leaf => simp [productMass,word,wordMonomial_nil]
  | branch c ts ih =>
    change (wordMonomial t (r*τ) c.val/τ)*(∏ i,(ts i).productMass t r τ)=_
    have hw := wordMonomial_corners t r c (fun i => (ts i).toWord)
    change wordMonomial t r (branch c ts).word=
      wordMonomial t r c.val*∏ i,wordMonomial t r (ts i).word at hw
    rw [hw]
    simp_rw [ih]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    simp only [wordMonomial,mul_pow]
    field_simp

end CoreTree

end FKCRT.Inventory
end


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreLabel

lemma mass_nonneg {t r τ : ℝ} (ht : 0≤t) (hr : 0 ≤ r) (hτ : 0≤τ) (c : CoreLabel) :
    0 ≤ mass t r τ c := by
  cases c with
  | none => exact div_nonneg zero_le_one hτ
  | some c =>
    exact div_nonneg (mul_nonneg (pow_nonneg ht _) (pow_nonneg (mul_nonneg hr hτ) _)) hτ

end CoreLabel
namespace CoreTree

lemma productMass_labels (t r τ : ℝ) (T : CoreTree) :
    T.productMass t r τ=(T.labels.map (CoreLabel.mass t r τ)).prod := by
  induction T with
  | leaf => simp [productMass,labels,CoreLabel.mass]
  | branch c ts ih =>
    rw [productMass,labels_branch,List.map_cons,List.prod_cons]
    congr 1
    simp only [List.flatMap_def,List.map_flatten,List.prod_flatten,List.map_ofFn,List.prod_ofFn,Function.comp_def]
    exact Finset.prod_congr rfl (fun i _ => ih i)

end CoreTree
end FKCRT.Inventory
end


noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreLabel

lemma rootMass_nonneg (P : Parameters) (c : CoreLabel) : 0 ≤ rootMass P c :=
  mass_nonneg (flexParameter_pos P).le (Real.sqrt_nonneg _) (emptyTotal_pos P).le c

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
-- module Solutions.OAIQ021_FK.FKMaps_PlanarActivity
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace FKCRT.GraphMerge
variable {V : Type*} (G : SimpleGraph V)

lemma sup_edge_reachable_of_reachable {u v : V} (h : G.Reachable u v) (x y : V) :
    (G⊔SimpleGraph.edge u v).Reachable x y ↔ G.Reachable x y := by
  constructor
  · intro hh
    obtain ⟨p⟩ := hh
    induction p with
    | nil => exact .refl _
    | @cons x z y ha p ih =>
      rcases ha with ha | ha
      · exact ha.reachable.trans ih
      · rcases (SimpleGraph.edge_adj _ _ _ _).mp ha with ⟨⟨rfl,rfl⟩ | ⟨rfl,rfl⟩,hne⟩
        · exact h.trans ih
        · exact h.symm.trans ih
  · exact fun hh => hh.mono le_sup_left

lemma card_sup_edge_of_reachable [Finite V] {u v : V} (h : G.Reachable u v) :
    Nat.card (G⊔SimpleGraph.edge u v).ConnectedComponent=Nat.card G.ConnectedComponent := by
  apply Nat.card_congr
  exact componentEquiv _ G.connectedComponentMk Quot.mk_surjective
    (fun x y => (sup_edge_reachable_of_reachable G h x y).trans SimpleGraph.ConnectedComponent.eq.symm)

end FKCRT.GraphMerge
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma components_insert_of_reachable (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a)
    (h : (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    submapComponents a s (insert e A)=submapComponents a s A := by
  simp only [submapComponents,spanningGraph_insert a s ha]
  exact GraphMerge.card_sup_edge_of_reachable _ h

lemma submapDefect_monotone (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) : Monotone (submapDefect a s ha) := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro A e he
  let p := s*partialReversal a ha A
  have hnew : s*partialReversal a ha (insert e A)=p*swap e.out (a e.out) := by
    rw [partialReversal_insert a ha A e he,← mul_assoc]
  have hnc : p e.out ≠ p (a e.out) := fun hh => hf e.out (p.injective hh).symm
  by_cases hr : (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))
  · have hk := components_insert_of_reachable a s ha A e hr
    have hb := card_orbit_mul_swap_le p e.out (a e.out)
    simp only [submapDefect,Finset.card_insert_of_notMem he,hnew,hk] at ⊢
    change (A.card:ℤ) - _ + 2*(_ : ℤ) - (Nat.card (Orbit p):ℤ) ≤ _
    omega
  · have hk := components_insert_of_not_reachable a s ha A e hr
    have hn : ¬p.SameCycle e.out (a e.out) := fun hh =>
      hr (spanningGraph_reachable_of_sameCycle a s ha A hh)
    have hc := MapCycles.card_orbits_swap_of_not_sameCycle p
      (a := p e.out) (b := p (a e.out)) (by
        simpa only [sameCycle_apply_left,sameCycle_apply_right] using hn)
    rw [← mul_swap_eq_swap_mul] at hc
    change Nat.card (Orbit (p*swap e.out (a e.out)))+1=Nat.card (Orbit p) at hc
    simp only [submapDefect,Finset.card_insert_of_notMem he,hnew] at ⊢
    change (A.card:ℤ) - _ + 2*(_ : ℤ) - (Nat.card (Orbit p):ℤ) ≤ _
    omega

lemma submapDefect_empty (a s : Perm (Dart n)) (ha : Function.Involutive a) :
    submapDefect a s ha ∅=0 := by
  simp [submapDefect,submapComponents_empty,partialReversal_empty]
  omega

lemma partialReversal_univ (a : Perm (Dart n)) (ha : Function.Involutive a) :
    partialReversal a ha Finset.univ=a := by
  apply Equiv.ext
  intro d
  simp [partialReversal_apply]

lemma submapDefect_univ (M : LabelledMap n) :
    submapDefect M.val.1 M.val.2 M.property.1 Finset.univ=0 := by
  have hk : submapComponents M.val.1 M.val.2 Finset.univ=1 := by
    dsimp [submapComponents]
    simp only [Finset.coe_univ]
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨M.property.2.2.1.preconnected.subsingleton_connectedComponent,
      ⟨(spanningGraph M.val.1 M.val.2 univ).connectedComponentMk (orbit M.val.2 0)⟩⟩
  have he := M.property.2.2.2
  simp only [submapDefect,Finset.card_univ,reversal_card _ M.property.1 M.property.2.1,
    hk,partialReversal_univ]
  omega

/-- Exact planar spanning-subgraph Euler identity. This derives every
subgraph's zero genus from the full-map Euler equality. -/
theorem planar_boundary_card (M : LabelledMap n) (A : Finset (Orbit M.val.1)) :
    Nat.card (Orbit (M.val.2*partialReversal M.val.1 M.property.1 A)) +
      Nat.card (Orbit M.val.2) = 2*submapComponents M.val.1 M.val.2 A+A.card := by
  have hm := submapDefect_monotone M.val.1 M.val.2 M.property.1 M.property.2.1
  have hlo := hm (Finset.empty_subset A)
  have hhi := hm (Finset.subset_univ A)
  rw [submapDefect_empty] at hlo
  rw [submapDefect_univ] at hhi
  simp only [submapDefect] at hlo hhi
  omega

end FKCRT
end


noncomputable section
open scoped BigOperators
namespace FKCRT
variable {n : ℕ}

lemma fkWeight_eq_boundary (q : ℝ) (hq : 0 ≤ q) (M : RootedMap n)
    (A : Finset (Edge M)) :
    fkWeight q M A = Real.sqrt q ^ Nat.card (Orbit (rotation M *
      partialReversal (reversal M) M.out.property.1 A)) := by
  have hh := planar_boundary_card M.out A
  have hh' : (Nat.card (Orbit (rotation M * partialReversal (reversal M) M.out.property.1 A)) : ℝ) +
      (Nat.card (Vertex M) : ℝ) = 2*(clusterCount M A : ℝ)+(A.card : ℝ) := by
    exact_mod_cast hh
  rw [fkWeight,Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hq]
  congr 1
  linarith

/-- Exact finite FK-to-loop normalization, not an asymptotic equivalence. -/
theorem fk_marginal_loopPolynomial (q : ℝ) (hq : 0 < q) (M : RootedMap n) :
    (∑ A : Finset (Edge M),fkWeight q M A) = Real.sqrt q * loopPolynomial (Real.sqrt q) M := by
  rw [loopPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [fkWeight_eq_boundary q hq.le]
  let b := Nat.card (Orbit (rotation M * partialReversal (reversal M) M.out.property.1 A))
  change Real.sqrt q ^ b= Real.sqrt q * Real.sqrt q ^ ((b : ℤ)-1)
  have ht : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  calc
    Real.sqrt q ^ b = Real.sqrt q ^ (1+((b : ℤ)-1)) := by
      rw [show 1+((b : ℤ)-1)=(b : ℤ) by omega,zpow_natCast]
    _ = _ := by rw [zpow_add₀ ht,zpow_one]

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma residualPartition_initial (t : ℝ) (M : RootedMap n) :
    residualPartition t (reversal M) (rotation M) ∅ Finset.univ = loopPolynomial t M := by
  simp only [residualPartition,Finset.powerset_univ,loopPolynomial]
  apply Finset.sum_congr rfl
  intro A _
  have hh := planar_boundary_card M.out A
  simp only [residualWeight,Finset.empty_union,submapComponents_empty]
  congr 1
  change Nat.card (Orbit (rotation M*partialReversal (reversal M) M.out.property.1 A)) +
    Nat.card (Orbit (rotation M))=2*submapComponents (reversal M) (rotation M) A+A.card at hh
  omega

lemma residualPartition_terminal (t : ℝ) (a s : Perm (Dart n)) (C : Finset (Orbit a))
    (hC : submapComponents a s C=1) : residualPartition t a s C ∅=1 := by
  simp [residualPartition,residualWeight,hC]

lemma residualWeight_contract (t : ℝ) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C B : Finset (Orbit a)) (e : Orbit a) (he : e∉B)
    (hn : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    residualWeight t a s C (insert e B)=residualWeight t a s (insert e C) B := by
  have hk := components_insert_of_not_reachable a s ha C e hn
  simp only [residualWeight,Finset.card_insert_of_notMem he,Finset.union_insert,Finset.insert_union]
  congr 1
  omega

/-- A nonloop edge may be deleted or contracted without a multiplicative
factor; even in the presence of loops and parallel edges. -/
theorem residual_delete_contract (t : ℝ) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a) (he : e∉R)
    (hn : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    residualPartition t a s C (insert e R)=
      residualPartition t a s C R+residualPartition t a s (insert e C) R := by
  rw [residualPartition,Finset.sum_powerset_insert he]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  exact residualWeight_contract t a s ha C B e
    (fun h => he (Finset.mem_powerset.mp hB h)) hn

lemma residualWeight_loop (t : ℝ) (ht : t≠0) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C B : Finset (Orbit a)) (e : Orbit a) (he : e∉B)
    (hl : (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    residualWeight t a s C (insert e B)=t*residualWeight t a s C B := by
  have hl' := hl.mono (spanningGraph_mono a s (show (C : Set (Orbit a)) ⊆ (C∪B : Finset (Orbit a)) from
    fun _ h => Finset.mem_union_left _ h))
  have hk := components_insert_of_reachable a s ha (C∪B) e hl'
  simp only [residualWeight,Finset.card_insert_of_notMem he,Finset.union_insert,hk]
  rw [show (2*(submapComponents a s (C∪B) : ℤ)+(↑(B.card+1):ℤ)-(submapComponents a s C : ℤ)-1) =
      1+(2*(submapComponents a s (C∪B) : ℤ)+(B.card : ℤ)-(submapComponents a s C : ℤ)-1) by omega,
    zpow_add₀ ht,zpow_one]

/-- A loop has precisely the source factor 1+t. -/
theorem residual_loop (t : ℝ) (ht : t≠0) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a) (he : e∉R)
    (hl : (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    residualPartition t a s C (insert e R)=(1+t)*residualPartition t a s C R := by
  rw [residualPartition,Finset.sum_powerset_insert he]
  have hh : (∑ B∈R.powerset,residualWeight t a s C (insert e B))=
      t*residualPartition t a s C R := by
    rw [residualPartition,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    exact residualWeight_loop t ht a s ha C B e (fun h => he (Finset.mem_powerset.mp hB h)) hl
  rw [hh]
  change residualPartition t a s C R+t*residualPartition t a s C R=_
  ring

lemma residual_bridge_pair (t : ℝ) (ht : t≠0) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a)
    (hb : ¬(spanningGraph a s ((C∪R : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out))) :
    residualPartition t a s C R=t*residualPartition t a s (insert e C) R := by
  have hn : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) :=
    fun h => hb (h.mono (spanningGraph_mono a s (fun _ hx => Finset.mem_union_left _ hx)))
  have hk := components_insert_of_not_reachable a s ha C e hn
  rw [residualPartition,residualPartition,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hn' : ¬(spanningGraph a s ((C∪B : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out)) := by
    intro hh
    apply hb
    exact hh.mono (spanningGraph_mono a s (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_right _ (Finset.mem_powerset.mp hB hx)))
  have hk' := components_insert_of_not_reachable a s ha (C∪B) e hn'
  simp only [residualWeight,Finset.insert_union]
  rw [show (2*(submapComponents a s (C∪B) : ℤ)+(B.card : ℤ)-(submapComponents a s C : ℤ)-1)=
    1+(2*(submapComponents a s (insert e (C∪B)) : ℤ)+(B.card : ℤ)-
      (submapComponents a s (insert e C) : ℤ)-1) by omega,zpow_add₀ ht,zpow_one]

/-- A bridge has precisely the source factor 1+t; no residual-map
isomorphism or unproved rank axiom is used. -/
theorem residual_bridge (t : ℝ) (ht : t≠0) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a) (he : e∉R)
    (hb : ¬(spanningGraph a s ((C∪R : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out))) :
    residualPartition t a s C (insert e R)=(1+t)*residualPartition t a s (insert e C) R := by
  have hn : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) :=
    fun h => hb (h.mono (spanningGraph_mono a s (fun _ hx => Finset.mem_union_left _ hx)))
  rw [residual_delete_contract t a s ha C R e he hn,residual_bridge_pair t ht a s ha C R e hb]
  ring

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma spanningGraph_edge_reachable (a s : Perm (Dart n)) (A : Finset (Orbit a))
    (e : Orbit a) (he : e∈A) :
    (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) := by
  by_cases hh : orbit s e.out=orbit s (a e.out)
  · rw [hh]
  · apply SimpleGraph.Adj.reachable
    refine ⟨hh,Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
    change orbit a e.out∈A
    simpa only [show orbit a e.out=e from Quotient.out_eq e] using he

lemma Multiforest.insert {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A : Finset (Orbit a)} (h : Multiforest a s A) (e : Orbit a)
    (hn : ¬(spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    Multiforest a s (insert e A) := by
  have hne : orbit s e.out≠orbit s (a e.out) := fun hh => hn (hh ▸ SimpleGraph.Reachable.refl _)
  have hends : ∀ f∈A,edgeEnds a s e≠edgeEnds a s f := by
    intro f hf heq
    have hr := spanningGraph_edge_reachable a s A f hf
    rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩|⟨h1,h2⟩
    · exact hn (h1 ▸ h2 ▸ hr)
    · exact hn (h1 ▸ h2 ▸ hr.symm)
  refine ⟨?_,?_,?_⟩
  · rw [spanningGraph_insert a s ha]
    exact h.1.sup_edge_of_not_reachable hn
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl|hf
    · exact hne
    · exact h.2.1 f hf
  · intro f hf g hg hfg
    rcases Finset.mem_insert.mp hf with hfe|hfA
    · subst f
      rcases Finset.mem_insert.mp hg with hge|hgA
      · exact hge.symm
      · exact False.elim (hends g hgA hfg)
    · rcases Finset.mem_insert.mp hg with hge|hgA
      · subst g
        exact False.elim (hends f hfA hfg.symm)
      · exact h.2.2 hfA hgA hfg

/-- The residual graph stays connected when an edge whose endpoints are
already connected is removed. -/
lemma spanningGraph_connected_erase (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a)
    (hc : (spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a))).Connected)
    (hr : (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    (spanningGraph a s (A : Set (Orbit a))).Connected := by
  rw [spanningGraph_insert a s ha] at hc
  refine {preconnected := ?_,nonempty := hc.nonempty}
  intro x y
  exact (GraphMerge.sup_edge_reachable_of_reachable _ hr x y).mp (hc.preconnected x y)

lemma treeExtensions_terminal (a s : Perm (Dart n)) (C : Finset (Orbit a))
    (hf : Multiforest a s C) (hc : (spanningGraph a s (C : Set (Orbit a))).Connected) :
    treeExtensions a s C ∅={C} := by
  ext T
  rw [mem_treeExtensions,Finset.mem_singleton,Finset.union_empty]
  constructor
  · exact fun h => Finset.Subset.antisymm h.2.1 h.1
  · rintro rfl
    exact ⟨le_rfl,le_rfl,hf,hc⟩

lemma treeExtensions_split (a s : Perm (Dart n)) (C R : Finset (Orbit a)) (e : Orbit a)
    (heC : e∉C) (heR : e∉R) :
    treeExtensions a s C (insert e R) = treeExtensions a s C R ∪ treeExtensions a s (insert e C) R ∧
    Disjoint (treeExtensions a s C R) (treeExtensions a s (insert e C) R) := by
  constructor
  · ext T
    simp only [mem_treeExtensions,Finset.mem_union]
    constructor
    · rintro ⟨hC,hT,hf,hc⟩
      by_cases he : e∈T
      · exact Or.inr ⟨Finset.insert_subset_iff.mpr ⟨he,hC⟩,by simpa [Finset.insert_union,Finset.union_insert] using hT,hf,hc⟩
      · refine Or.inl ⟨hC,?_,hf,hc⟩
        intro x hx
        rcases Finset.mem_union.mp (hT hx) with h|h
        · exact Finset.mem_union_left _ h
        · rcases Finset.mem_insert.mp h with rfl|h
          · exact False.elim (he hx)
          · exact Finset.mem_union_right _ h
    · rintro (⟨hC,hT,hf,hc⟩|⟨hC,hT,hf,hc⟩)
      · exact ⟨hC,hT.trans (by intro x hx; simpa only [Finset.union_insert] using Finset.mem_insert_of_mem hx),hf,hc⟩
      · exact ⟨(Finset.subset_insert e C).trans hC,by simpa [Finset.insert_union,Finset.union_insert] using hT,hf,hc⟩
  · apply Finset.disjoint_left.mpr
    intro T hT hT'
    obtain ⟨_,hsub,_,_⟩ := (mem_treeExtensions a s C R T).mp hT
    obtain ⟨hC,_,_,_⟩ := (mem_treeExtensions a s (insert e C) R T).mp hT'
    have hh := hsub (hC (Finset.mem_insert_self _ _))
    exact (Finset.notMem_union.mpr ⟨heC,heR⟩) hh

lemma treeExtensions_loop (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a) (he : e∉C)
    (hl : (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    treeExtensions a s (insert e C) R=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  obtain ⟨hC,_,hf,_⟩ := (mem_treeExtensions a s (insert e C) R T).mp hT
  have heT := hC (Finset.mem_insert_self _ _)
  have hCT : C⊆T.erase e := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => he (h ▸ hx),hC (Finset.mem_insert_of_mem hx)⟩
  have hf' : Multiforest a s (insert e (T.erase e)) := by rwa [Finset.insert_erase heT]
  exact hf'.insert_not_reachable ha (Finset.notMem_erase _ _)
    (hl.mono (spanningGraph_mono a s hCT))

lemma treeExtensions_bridge (a s : Perm (Dart n))
    (C R : Finset (Orbit a)) (e : Orbit a)
    (hb : ¬(spanningGraph a s ((C∪R : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out))) : treeExtensions a s C R=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  obtain ⟨_,hT,_,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  exact hb ((hc.preconnected _ _).mono (spanningGraph_mono a s hT))

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma explorationActivity_empty (a s : Perm (Dart n)) (select : EdgeSelector a)
    (C T : Finset (Orbit a)) (k : ℕ) : explorationActivity a s select C ∅ T k=0 := by
  cases k <;> simp [explorationActivity]

/-- The source deletion/contraction expansion is valid for arbitrary
history-dependent edge selection. It counts every genuine spanning tree
once, including bridge/loop degeneracies. No activity expansion is assumed. -/
theorem adaptive_activity_expansion (t : ℝ) (ht : t≠0)
    (a s : Perm (Dart n)) (ha : Function.Involutive a) (select : EdgeSelector a)
    (k : ℕ) (C R : Finset (Orbit a)) (hk : R.card≤k)
    (hd : Disjoint C R) (hf : Multiforest a s C)
    (hc : (spanningGraph a s ((C∪R : Finset (Orbit a)) : Set (Orbit a))).Connected) :
    residualPartition t a s C R =
      ∑ T∈treeExtensions a s C R,(1+t)^explorationActivity a s select C R T k := by
  induction k generalizing C R with
  | zero =>
    have hR : R=∅ := Finset.card_eq_zero.mp (by omega)
    subst R
    have hc' : (spanningGraph a s (C : Set (Orbit a))).Connected := by simpa using hc
    have hC : submapComponents a s C=1 := by
      apply Nat.card_eq_one_iff_unique.mpr
      exact ⟨hc'.preconnected.subsingleton_connectedComponent,⟨(spanningGraph a s (C : Set _)).connectedComponentMk (orbit s 0)⟩⟩
    rw [residualPartition_terminal t a s C hC,treeExtensions_terminal a s C hf hc']
    simp [explorationActivity]
  | succ k ih =>
    by_cases hR : R.Nonempty
    · let e := (select C R hR).val
      let R' := R.erase e
      have heR : e∈R := (select C R hR).property
      have heC : e∉C := fun h => Finset.disjoint_left.mp hd h heR
      have hen : e∉R' := Finset.notMem_erase _ _
      have hins : insert e R'=R := Finset.insert_erase heR
      have hk' : R'.card≤k := by
        have hh := Finset.card_erase_add_one heR
        dsimp [R']
        omega
      have hd0 : Disjoint C R' := hd.mono_right (Finset.erase_subset _ _)
      have hd1 : Disjoint (insert e C) R' := Finset.disjoint_insert_left.mpr ⟨hen,hd0⟩
      have hs := treeExtensions_split a s C R' e heC hen
      rw [hins] at hs
      have hc1 : (spanningGraph a s (((insert e C)∪R' : Finset (Orbit a)) : Set (Orbit a))).Connected := by
        simpa only [Finset.insert_union,← Finset.union_insert,hins] using hc
      by_cases hl : (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))
      · have hc0 : (spanningGraph a s ((C∪R' : Finset (Orbit a)) : Set (Orbit a))).Connected := by
          apply spanningGraph_connected_erase a s ha (C∪R') e
          · simpa only [← Finset.union_insert,hins] using hc
          · exact hl.mono (spanningGraph_mono a s (fun _ h => Finset.mem_union_left _ h))
        have hempty := treeExtensions_loop a s ha C R' e heC hl
        have hext : treeExtensions a s C R=treeExtensions a s C R' := by simpa only [hempty,Finset.union_empty] using hs.1
        have hr := residual_loop t ht a s ha C R' e hen hl
        rw [hins] at hr
        rw [hr,ih C R' hk' hd0 hf hc0,hext,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        have heq : explorationActivity a s select C R T (k+1)=
            1+explorationActivity a s select C R' T k := by
          simp only [explorationActivity,dite_eq_left hR]
          change (if _ then _ else _)=_
          rw [ite_eq_left hl]
        rw [heq,pow_add,pow_one]
      · have hf1 := hf.insert ha e hl
        by_cases hb : ¬(spanningGraph a s ((C∪R' : Finset (Orbit a)) : Set (Orbit a))).Reachable
            (orbit s e.out) (orbit s (a e.out))
        · have hempty := treeExtensions_bridge a s C R' e hb
          have hext : treeExtensions a s C R=treeExtensions a s (insert e C) R' := by simpa only [hempty,Finset.empty_union] using hs.1
          have hr := residual_bridge t ht a s ha C R' e hen hb
          rw [hins] at hr
          rw [hr,ih (insert e C) R' hk' hd1 hf1 hc1,hext,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _
          have heq : explorationActivity a s select C R T (k+1)=
              1+explorationActivity a s select (insert e C) R' T k := by
            simp only [explorationActivity,dite_eq_left hR]
            change (if _ then _ else _)=_
            rw [ite_eq_right hl,ite_eq_left hb]
          rw [heq,pow_add,pow_one]
        · have hc0 : (spanningGraph a s ((C∪R' : Finset (Orbit a)) : Set (Orbit a))).Connected := by
            apply spanningGraph_connected_erase a s ha (C∪R') e
            · simpa only [← Finset.union_insert,hins] using hc
            · exact not_not.mp hb
          have hr := residual_delete_contract t a s ha C R' e hen hl
          rw [hins] at hr
          rw [hr,ih C R' hk' hd0 hf hc0,ih (insert e C) R' hk' hd1 hf1 hc1,hs.1,Finset.sum_union hs.2]
          congr 1
          · apply Finset.sum_congr rfl
            intro T hT
            have heT : e∉T := by
              intro h
              have hh := ((mem_treeExtensions a s C R' T).mp hT).2.1 h
              exact (Finset.notMem_union.mpr ⟨heC,hen⟩) hh
            congr 1
            simp only [explorationActivity,dite_eq_left hR]
            change _=(if _ then _ else _)
            rw [ite_eq_right hl,ite_eq_right hb,ite_eq_right heT]
          · apply Finset.sum_congr rfl
            intro T hT
            have heT : e∈T := ((mem_treeExtensions a s (insert e C) R' T).mp hT).1 (Finset.mem_insert_self _ _)
            congr 1
            simp only [explorationActivity,dite_eq_left hR]
            change _=(if _ then _ else _)
            rw [ite_eq_right hl,ite_eq_right hb,ite_eq_left heT]
    · have hemp : R=∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      subst R
      have hc' : (spanningGraph a s (C : Set (Orbit a))).Connected := by simpa using hc
      have hC : submapComponents a s C=1 := by
        apply Nat.card_eq_one_iff_unique.mpr
        exact ⟨hc'.preconnected.subsingleton_connectedComponent,⟨(spanningGraph a s (C : Set _)).connectedComponentMk (orbit s 0)⟩⟩
      rw [residualPartition_terminal t a s C hC,treeExtensions_terminal a s C hf hc']
      simp [explorationActivity_empty]

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TourActivity
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma partial_tour_eq_outside (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hC : C⊆T) (hT : T⊆C∪R) (d : Dart n)
    (hd : orbit a d∉R) : (s*partialReversal a ha C) d=(s*partialReversal a ha T) d := by
  have hh : orbit a d∈C ↔ orbit a d∈T := ⟨fun h => hC h,fun h => by
    rcases Finset.mem_union.mp (hT h) with h|h
    · exact h
    · exact False.elim (hd h)⟩
  simp only [mul_apply,partialReversal_apply,hh]

lemma partial_tour_prefix (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hC : C⊆T) (hT : T⊆C∪R) (k : ℕ)
    (hk : ∀ j<k,orbit a (((s*partialReversal a ha T)^j) 0)∉R) :
    ((s*partialReversal a ha C)^k) 0=((s*partialReversal a ha T)^k) 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',mul_apply,ih (fun j hj => hk j (by omega)),pow_succ',mul_apply]
    exact partial_tour_eq_outside a s ha C R T hC hT _ (hk k (by omega))

/-- The next chosen edge is exactly the first undecided edge of *every*
completed tree tour. In particular it depends only on previous choices. -/
theorem tourSelector_first (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hR : R.Nonempty) (hC : C⊆T) (hT : T⊆C∪R)
    (ht : ∀ d e,(s*partialReversal a ha T).SameCycle d e) :
    ∃ k : ℕ, orbit a (((s*partialReversal a ha T)^k) 0)=(tourSelector a s ha C R hR).val ∧
      orbit a (((s*partialReversal a ha T)^k) 0)∈R ∧
      ∀ j<k,orbit a (((s*partialReversal a ha T)^j) 0)∉R := by
  have hex : ∃ k : ℕ,orbit a (((s*partialReversal a ha T)^k) 0)∈R := by
    obtain ⟨e,he⟩ := hR
    obtain ⟨k,hk⟩ := (ht 0 e.out).exists_nat_pow_eq
    exact ⟨k,by rw [hk,show orbit a e.out=e from Quotient.out_eq e]; exact he⟩
  let k := Nat.find hex
  have hk : orbit a (((s*partialReversal a ha T)^k) 0)∈R := Nat.find_spec hex
  have hlt : ∀ j<k,orbit a (((s*partialReversal a ha T)^j) 0)∉R :=
    fun j hj => Nat.find_min hex hj
  have heq := partial_tour_prefix a s ha C R T hC hT k hlt
  have hex' : ∃ j : ℕ,orbit a (((s*partialReversal a ha C)^j) 0)∈R :=
    ⟨k,by rw [heq]; exact hk⟩
  have hfind : Nat.find hex'=k := by
    apply le_antisymm (Nat.find_min' hex' (by rw [heq]; exact hk))
    by_contra hh
    have hj : Nat.find hex'<k := by omega
    have heq' := partial_tour_prefix a s ha C R T hC hT (Nat.find hex') (fun i hi => hlt i (lt_trans hi hj))
    exact hlt _ hj (heq' ▸ Nat.find_spec hex')
  refine ⟨k,?_,hk,hlt⟩
  simp only [tourSelector,dite_eq_left hex',hfind,heq]

/-- Exact rooted-tour adaptive expansion of the finite FK loop polynomial. -/
theorem loopPolynomial_tour_activity (t : ℝ) (ht : t≠0) (M : RootedMap n) :
    loopPolynomial t M = ∑ T∈treeExtensions (reversal M) (rotation M) ∅ Finset.univ,
      (1+t)^explorationActivity (reversal M) (rotation M)
        (tourSelector (reversal M) (rotation M) M.out.property.1) ∅ Finset.univ T (n+1) := by
  rw [← residualPartition_initial]
  apply adaptive_activity_expansion t ht (reversal M) (rotation M) M.out.property.1
  · rw [Finset.card_univ,reversal_card (reversal M) M.out.property.1 M.out.property.2.1]
  · simp
  · refine ⟨?_,by simp,?_⟩
    · have he : spanningGraph (reversal M) (rotation M) (∅ : Finset (Edge M))=⊥ := by
        ext v w
        simp [spanningGraph]
      rw [he]
      exact SimpleGraph.isAcyclic_bot
    · intro e he
      simp at he
  · convert M.out.property.2.2.1 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply heq_of_eq
    congr 1
    ext e
    simp
    trivial

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma Multiforest.edgeEnds_mem_iff {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A T : Finset (Orbit a)} (h : Multiforest a s T) (hA : A⊆T)
    {e : Orbit a} (he : e∈T) :
    edgeEnds a s e∈(spanningGraph a s (A : Set (Orbit a))).edgeSet ↔ e∈A := by
  constructor
  · intro hh
    obtain ⟨f,hf,hfe⟩ := spanningGraph_edgeSet_subset a s ha A hh
    have hfe' := h.2.2 (hA hf) he hfe
    exact hfe' ▸ hf
  · intro heA
    apply (SimpleGraph.mem_edgeSet _).mpr
    refine ⟨h.2.1 e he,Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
    change orbit a e.out∈A
    simpa only [show orbit a e.out=e from Quotient.out_eq e] using heA

/-- A subtree connects two vertices precisely when it retains every edge of
 their unique tree path, expressed without choosing that path. -/
theorem Multiforest.reachable_iff_all_cuts {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {C T : Finset (Orbit a)} (h : Multiforest a s T) (hC : C⊆T)
    (hc : (spanningGraph a s (T : Set (Orbit a))).Connected) (u v : Orbit s) :
    (spanningGraph a s (C : Set (Orbit a))).Reachable u v ↔
      ∀ e∈T, e∉C → (spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable u v := by
  constructor
  · intro hr e _ he
    apply hr.mono (spanningGraph_mono a s _)
    intro f hf
    exact Finset.mem_erase.mpr ⟨fun hfe => he (hfe ▸ hf),hC hf⟩
  · intro hall
    let G := spanningGraph a s (T : Set (Orbit a))
    have ht : G.IsTree := ⟨hc,h.1⟩
    obtain ⟨p,hp,hunique⟩ := ht.existsUnique_path u v
    suffices htransfer : ∀ z∈p.edges,z∈(spanningGraph a s (C : Set (Orbit a))).edgeSet from
      (p.transfer _ htransfer).reachable
    intro z hz
    obtain ⟨e,he,rfl⟩ := spanningGraph_edgeSet_subset a s ha T (p.edges_subset_edgeSet hz)
    apply (h.edgeEnds_mem_iff ha hC he).mpr
    by_contra heC
    let q := (hall e he heC).some.toPath
    have hle := spanningGraph_mono a s (show (T.erase e : Set (Orbit a))⊆(T : Set (Orbit a)) from Finset.erase_subset _ _)
    have hq : (q.val.mapLe hle).IsPath := q.property.mapLe hle
    have heq := hunique _ hq
    have hez : edgeEnds a s e∈(q.val.mapLe hle).edges := heq ▸ hz
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hez
    have hh := q.val.edges_subset_edgeSet hez
    exact Finset.notMem_erase e T ((h.edgeEnds_mem_iff ha (Finset.erase_subset _ _) he).mp hh)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma spanningGraph_reachable_mono_relation (a s : Perm (Dart n))
    (ha : Function.Involutive a) (A B : Finset (Orbit a))
    (h : ∀ e∈B,(spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)))
    {u v : Orbit s} (hr : (spanningGraph a s (B : Set (Orbit a))).Reachable u v) :
    (spanningGraph a s (A : Set (Orbit a))).Reachable u v := by
  apply SimpleGraph.ConnectedComponent.eq.mp
  apply GraphMerge.reachable_eq_of_adj_eq _ _ _ hr
  intro x y hxy
  obtain ⟨e,he,heq⟩ := spanningGraph_edgeSet_subset a s ha B ((SimpleGraph.mem_edgeSet _).mpr hxy)
  have hh := h e he
  rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact SimpleGraph.ConnectedComponent.sound (h1 ▸ h2 ▸ hh)
  · exact SimpleGraph.ConnectedComponent.sound (h2 ▸ h1 ▸ hh.symm)

lemma Multiforest.erase_components_two {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {T : Finset (Orbit a)} (h : Multiforest a s T)
    (hc : (spanningGraph a s (T : Set (Orbit a))).Connected) {e : Orbit a} (he : e∈T) :
    submapComponents a s (T.erase e)=2 := by
  have h1 := h.components_card ha
  have h2 := (h.mono (Finset.erase_subset e T)).components_card ha
  have hcard : submapComponents a s T=1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨hc.preconnected.subsingleton_connectedComponent,⟨(spanningGraph a s (T : Set _)).connectedComponentMk (orbit s 0)⟩⟩
  rw [Finset.card_erase_of_mem he] at h2
  have hp := Finset.card_pos.mpr ⟨e,he⟩
  omega

lemma Multiforest.erase_component_dichotomy {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {T : Finset (Orbit a)} (h : Multiforest a s T)
    (hc : (spanningGraph a s (T : Set (Orbit a))).Connected) {e : Orbit a} (he : e∈T)
    (v : Orbit s) :
    (spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable v (orbit s e.out) ∨
    (spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable v (orbit s (a e.out)) := by
  let G := spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))
  let x := G.connectedComponentMk (orbit s e.out)
  let y := G.connectedComponentMk (orbit s (a e.out))
  have hne : y≠x := by
    intro hh
    have hf : Multiforest a s (Insert.insert e (T.erase e)) := by rwa [Finset.insert_erase he]
    exact hf.insert_not_reachable ha (Finset.notMem_erase _ _) (SimpleGraph.ConnectedComponent.eq.mp hh.symm)
  have hh : Nat.card G.ConnectedComponent=2 := h.erase_components_two ha hc he
  obtain ⟨z,hz,hzu⟩ := (Nat.card_eq_two_iff' x).mp hh
  have hy : y=z := hzu y hne
  by_cases hv : G.connectedComponentMk v=x
  · exact Or.inl (SimpleGraph.ConnectedComponent.eq.mp hv)
  · exact Or.inr (SimpleGraph.ConnectedComponent.eq.mp ((hzu _ hv).trans hy.symm))

/-- A residual edge is a bridge exactly when no retained edge crosses its
fundamental tree cut. No simplicity assumption on the original map. -/
theorem Multiforest.residual_bridge_iff {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {T B : Finset (Orbit a)} (h : Multiforest a s T)
    (hc : (spanningGraph a s (T : Set (Orbit a))).Connected) {e : Orbit a} (he : e∈T)
    (hB : T.erase e⊆B) :
    ¬(spanningGraph a s (B : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) ↔
      ∀ f∈B,(spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
        (orbit s f.out) (orbit s (a f.out)) := by
  let G := spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))
  constructor
  · intro hn f hf
    have hsub := spanningGraph_mono a s hB
    have hfr := spanningGraph_edge_reachable a s B f hf
    rcases h.erase_component_dichotomy ha hc he (orbit s f.out) with hf1|hf1 <;>
      rcases h.erase_component_dichotomy ha hc he (orbit s (a f.out)) with hf2|hf2
    · exact hf1.trans hf2.symm
    · exact False.elim (hn ((hf1.symm.mono hsub).trans (hfr.trans (hf2.mono hsub))))
    · exact False.elim (hn ((hf2.symm.mono hsub).trans (hfr.symm.trans (hf1.mono hsub))))
    · exact hf1.trans hf2.symm
  · intro hall hr
    have hf : Multiforest a s (Insert.insert e (T.erase e)) := by rwa [Finset.insert_erase he]
    exact hf.insert_not_reachable ha (Finset.notMem_erase _ _)
      (spanningGraph_reachable_mono_relation a s ha (T.erase e) B hall hr)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma fundamentalCross_symm (a s : Perm (Dart n)) (T : Finset (Orbit a)) (e f : Orbit a) :
    FundamentalCross a s T e f ↔ FundamentalCross a s T f e := or_comm

lemma fundamentalCross_tree (a s : Perm (Dart n)) (T : Finset (Orbit a))
    {e f : Orbit a} (he : e∈T) (hne : e≠f) :
    FundamentalCross a s T e f ↔
      ¬(spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
        (orbit s f.out) (orbit s (a f.out)) := by
  constructor
  · rintro (h|h)
    · exact h.2
    · exact False.elim (h.2 (spanningGraph_edge_reachable a s (T.erase f) e (Finset.mem_erase.mpr ⟨hne,he⟩)))
  · exact fun h => Or.inl ⟨he,h⟩

lemma fundamentalCross_nontree (a s : Perm (Dart n)) (T : Finset (Orbit a))
    {e f : Orbit a} (he : e∉T) :
    FundamentalCross a s T e f ↔ f∈T ∧
      ¬(spanningGraph a s ((T.erase f : Finset (Orbit a)) : Set (Orbit a))).Reachable
        (orbit s e.out) (orbit s (a e.out)) := by
  simp only [FundamentalCross,he,false_and,false_or]

/-- Exact non-tree forced-loop condition, in terms of the undecided edges. -/
theorem treeExtension_loop_iff_no_cross (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hT : T∈treeExtensions a s C R) (hd : Disjoint C R)
    {e : Orbit a} (he : e∉T) :
    (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) ↔
      ∀ f∈R,¬FundamentalCross a s T e f := by
  obtain ⟨hCT,hTR,hf,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  rw [hf.reachable_iff_all_cuts ha hCT hc]
  constructor
  · intro hh f hfR hfc
    rw [fundamentalCross_nontree a s T he] at hfc
    exact hfc.2 (hh f hfc.1 (fun hfC => Finset.disjoint_left.mp hd hfC hfR))
  · intro hh f hfT hfC
    have hfR : f∈R := (Finset.mem_union.mp (hTR hfT)).resolve_left hfC
    by_contra hn
    exact hh f hfR ((fundamentalCross_nontree a s T he).mpr ⟨hfT,hn⟩)

/-- Exact tree forced-bridge condition. The contracted/deleted state is the
one used by the genuine adaptive FK polynomial recursion. -/
theorem treeExtension_bridge_iff_no_cross (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hT : T∈treeExtensions a s C R) (hd : Disjoint C R)
    {e : Orbit a} (he : e∈T) (heR : e∈R) :
    ¬(spanningGraph a s ((C∪R.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out)) ↔
      ∀ f∈R.erase e,¬FundamentalCross a s T e f := by
  obtain ⟨hCT,hTR,hf,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  have hsub : T.erase e⊆C∪R.erase e := by
    intro f hfT
    obtain ⟨hne,hfT⟩ := Finset.mem_erase.mp hfT
    rcases Finset.mem_union.mp (hTR hfT) with hh|hh
    · exact Finset.mem_union_left _ hh
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne,hh⟩)
  rw [hf.residual_bridge_iff ha hc he hsub]
  constructor
  · intro hh f hfR hcross
    have hne : e≠f := (Finset.mem_erase.mp hfR).1.symm
    exact (fundamentalCross_tree a s T he hne).mp hcross (hh f (Finset.mem_union_right _ hfR))
  · intro hh f hfB
    rcases Finset.mem_union.mp hfB with hfC|hfR
    · apply spanningGraph_edge_reachable a s (T.erase e) f
      refine Finset.mem_erase.mpr ⟨?_,hCT hfC⟩
      intro hfe
      exact Finset.disjoint_left.mp hd (hfe ▸ hfC) heR
    · have hne : e≠f := (Finset.mem_erase.mp hfR).1.symm
      by_contra hn
      exact hh f hfR ((fundamentalCross_tree a s T he hne).mpr hn)

lemma fundamental_cut_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (e : Orbit a) (he : e∈T) :
    s*partialReversal a ha (T.erase e)=(s*partialReversal a ha T)*swap e.out (a e.out) := by
  have hh := partialReversal_insert a ha (T.erase e) e (Finset.notMem_erase _ _)
  rw [Finset.insert_erase he] at hh
  rw [hh]
  simp [mul_assoc]

/-- Fundamental tree cuts are exactly the two cycles obtained by cutting the
tour at the two darts of that edge. This is the algebraic contour-cut identity. -/
theorem fundamentalCross_tour_cut (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (hT : Multiforest a s T) {e f : Orbit a}
    (he : e∈T) (hne : e≠f) :
    FundamentalCross a s T e f ↔
      ¬((s*partialReversal a ha T)*swap e.out (a e.out)).SameCycle f.out (a f.out) := by
  rw [fundamentalCross_tree a s T he hne,← fundamental_cut_tour a s ha T e he]
  exact not_congr ((hT.mono (Finset.erase_subset _ _)).sameCycle_iff_reachable ha _ _).symm

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma disjoint_formPerm_action (U V : List α) (hn : (U++V).Nodup) :
    (∀ x∈U,(U.formPerm*V.formPerm) x=U.formPerm x) ∧
      (∀ x∈V,(U.formPerm*V.formPerm) x=V.formPerm x) := by
  have hd := List.disjoint_iff_ne.mpr (List.nodup_append.mp hn).2.2
  constructor
  · intro x hx
    rw [mul_apply,List.formPerm_apply_of_notMem (fun h => List.disjoint_left.mp hd hx h)]
  · intro x hx
    rw [mul_apply,List.formPerm_apply_of_notMem (fun h =>
      List.disjoint_left.mp hd h (V.formPerm_apply_mem_of_mem hx))]

lemma disjoint_formPerm_sameCycle (U V : List α) (hn : (U++V).Nodup)
    (hc : ∀ x,x∈U++V) (x y : α) :
    (U.formPerm*V.formPerm).SameCycle x y ↔ (x∈U ↔ y∈U) := by
  have ⟨hU,hV⟩ := disjoint_formPerm_action U V hn
  have hd := List.disjoint_iff_ne.mpr (List.nodup_append.mp hn).2.2
  constructor
  · intro h
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
      exact hk ▸ (pow_eq_on_list _ U hU hx k).2
    · intro hy
      obtain ⟨k,hk⟩ := h.symm.exists_nat_pow_eq
      exact hk ▸ (pow_eq_on_list _ U hU hy k).2
  · intro hh
    by_cases hx : x∈U
    · exact sameCycle_of_list _ hn.of_append_left hU hx (hh.mp hx)
    · have hy : y∉U := fun h => hx (hh.mpr h)
      exact sameCycle_of_list _ hn.of_append_right hV
        ((List.mem_append.mp (hc x)).resolve_left hx)
        ((List.mem_append.mp (hc y)).resolve_left hy)

/-- Cutting a cyclic tour at x,z separates precisely its two contour
intervals, including intervals with no interior darts. -/
theorem swap_tour_sameCycle (p : Perm α) (x z : α) (L R : List α)
    (he : orbitList p x=x::(L++z::R)) (hc : ∀ d e,p.SameCycle d e) (y w : α) :
    (swap x z*p).SameCycle y w ↔ (y∈x::L ↔ w∈x::L) := by
  have hn := nodup_orbitList p x
  rw [he] at hn
  have hp : p=(x::(L++z::R)).formPerm := by
    apply Equiv.ext
    intro d
    have hd := (mem_orbitList p x d).mpr (hc x d)
    simpa only [he] using orbitList_action p x d hd
  rw [hp,swap_mul_formPerm_cut x z L R hn]
  apply disjoint_formPerm_sameCycle _ _ hn
  intro d
  simpa only [he,List.cons_append] using (mem_orbitList p x d).mpr (hc x d)

/-- Right and left cuts have the same partition on darts other than the two
cut endpoints, which is exactly what is needed for distinct paired edges. -/
theorem tour_swap_sameCycle (p : Perm α) (x z : α) (L R : List α)
    (he : orbitList p x=x::(L++z::R)) (hc : ∀ d e,p.SameCycle d e)
    (y w : α) (hyx : y≠x) (hyz : y≠z) (hwx : w≠x) (hwz : w≠z) :
    (p*swap x z).SameCycle y w ↔ (y∈L ↔ w∈L) := by
  have hconj : p*swap x z=swap x z*(swap x z*p)*(swap x z)⁻¹ := by
    simp [← mul_assoc]
  rw [hconj,sameCycle_conj]
  simp only [swap_inv,swap_apply_of_ne_of_ne hyx hyz,swap_apply_of_ne_of_ne hwx hwz]
  rw [swap_tour_sameCycle p x z L R he hc y w]
  simp only [List.mem_cons,hyx,hwx,false_or]

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [Fintype α] [LinearOrder α]

omit [Fintype α] in
lemma ordered_two_sublist {l : List α} (hs : l.Pairwise (·<·))
    {x z : α} (hx : x∈l) (hz : z∈l) (hxz : x<z) : [x,z]<+l := by
  apply List.sublist_of_subperm_of_pairwise (r := (·≤·))
  · apply List.subperm_of_subset (by simpa using ne_of_lt hxz)
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> assumption
  · simpa using le_of_lt hxz
  · exact hs.imp (fun h => le_of_lt h)

omit [Fintype α] in
lemma ordered_middle {U L R : List α} {x z y : α}
    (hs : (U++x::(L++z::R)).Pairwise (·<·))
    (hy : y∈U++x::(L++z::R)) : y∈L ↔ x<y ∧ y<z := by
  have hU := (List.pairwise_append.mp hs).2.2
  have hx := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1
  have hLR := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2
  have hL := (List.pairwise_append.mp hLR).2.2
  have hz := (List.pairwise_cons.mp (List.pairwise_append.mp hLR).2.1).1
  constructor
  · intro hyL
    exact ⟨hx y (List.mem_append_left _ hyL),hL y hyL z (by simp)⟩
  · rintro ⟨hxy,hyz⟩
    simp only [List.mem_append,List.mem_cons] at hy
    rcases hy with hyU|rfl|hyL|rfl|hyR
    · exact False.elim ((not_lt_of_ge (hU y hyU x (by simp)).le) hxy)
    · exact False.elim ((lt_irrefl _) hxy)
    · exact hyL
    · exact False.elim ((lt_irrefl _) hyz)
    · exact False.elim ((not_lt_of_ge (hz y hyR).le) hyz)

/-- An ordered cyclic tour, cut at x<z, separates the strict linear interval
(x,z) from its complement, on all other darts. -/
theorem ordered_tour_cut (l : List α) (hs : l.Pairwise (·<·)) (hc : ∀ x,x∈l)
    (x z : α) (hxz : x<z) (y w : α)
    (hyx : y≠x) (hyz : y≠z) (hwx : w≠x) (hwz : w≠z) :
    (l.formPerm*swap x z).SameCycle y w ↔ ((x<y ∧ y<z) ↔ (x<w ∧ w<z)) := by
  have hn : l.Nodup := hs.imp (fun h => ne_of_lt h)
  have hsub := ordered_two_sublist hs (hc x) (hc z) hxz
  obtain ⟨U,K,hK,hsub⟩ := cons_sublist_split hsub
  obtain ⟨L,R,hR,_⟩ := cons_sublist_split hsub
  have he : l=U++x::(L++z::R) := by rw [hK,hR]
  have hp : l.formPerm=(x::(L++z::(R++U))).formPerm := by
    rw [he,formPerm_append_comm U _ (he ▸ hn)]
    simp only [List.cons_append,List.append_assoc]
  have hrot : orbitList l.formPerm x=x::(L++z::(R++U)) := by
    rw [hp,orbitList_formPerm]
    have hh := (List.perm_append_comm (l₁ := U) (l₂ := x::(L++z::R))).nodup_iff.mp (he ▸ hn)
    simpa only [List.cons_append,List.append_assoc] using hh
  have hcycle : ∀ d e,l.formPerm.SameCycle d e := by
    intro d e
    exact sameCycle_of_list _ hn (fun _ _ => rfl) (hc d) (hc e)
  rw [tour_swap_sameCycle l.formPerm x z L (R++U) hrot hcycle y w hyx hyz hwx hwz]
  exact iff_congr (ordered_middle (he ▸ hs) (he ▸ hc y)) (ordered_middle (he ▸ hs) (he ▸ hc w))

end FKCRT.MapCycles
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma edgeFirst_lt (a p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) (e : Orbit a) :
    edgeFirst a p hp e<2*(n+1) :=
  lt_of_le_of_lt (min_le_left _ _) ((tourNumbering p hp).symm e.out).isLt

lemma edgeFirst_orbit (a p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) (e : Orbit a) :
    orbit a ((p^edgeFirst a p hp e) 0)=e := by
  have hr (d : Dart n) : (p^((tourNumbering p hp).symm d).val) 0=d :=
    (tourNumbering p hp).apply_symm_apply d
  unfold edgeFirst
  by_cases hh : ((tourNumbering p hp).symm e.out).val≤((tourNumbering p hp).symm (a e.out)).val
  · rw [min_eq_left hh,hr]
    exact Quotient.out_eq e
  · rw [min_eq_right (by omega),hr,orbit_perm]
    exact Quotient.out_eq e

lemma edgeFirst_injective (a p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) :
    Function.Injective (edgeFirst a p hp) := by
  intro e f hef
  rw [← edgeFirst_orbit a p hp e,← edgeFirst_orbit a p hp f,hef]

lemma edgeFirst_le_position (a p : Perm (Dart n)) (ha : Function.Involutive a)
    (hp : ∀ d e,p.SameCycle d e) (i : Dart n) :
    edgeFirst a p hp (orbit a ((p^i.val) 0)) ≤ i.val := by
  let d := (p^i.val) 0
  have hd : orbit a d=orbit a d := rfl
  rcases (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp hd with hh|hh
  · have hr : (tourNumbering p hp).symm (orbit a d).out=i := by
      apply (tourNumbering p hp).injective
      simpa only [Equiv.apply_symm_apply,tourNumbering_apply] using hh.symm
    exact le_trans (min_le_left _ _) (by rw [hr])
  · have hr : (tourNumbering p hp).symm (a (orbit a d).out)=i := by
      apply (tourNumbering p hp).injective
      simpa only [Equiv.apply_symm_apply,tourNumbering_apply] using hh.symm
    exact le_trans (min_le_right _ _) (by rw [hr])

/-- The adaptive tour selector is the least first occurrence in every
completed tree tour, with no choice-dependent ordering assumed. -/
theorem tourSelector_least (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hR : R.Nonempty) (hC : C⊆T) (hT : T⊆C∪R)
    (ht : ∀ d e,(s*partialReversal a ha T).SameCycle d e) :
    ∀ f∈R,edgeFirst a (s*partialReversal a ha T) ht (tourSelector a s ha C R hR).val≤
      edgeFirst a (s*partialReversal a ha T) ht f := by
  obtain ⟨k,heq,hk,hbefore⟩ := tourSelector_first a s ha C R T hR hC hT ht
  have hkf (f : Orbit a) (hf : f∈R) : k≤edgeFirst a (s*partialReversal a ha T) ht f := by
    by_contra hh
    exact hbefore (edgeFirst a (s*partialReversal a ha T) ht f) (by omega) (by rw [edgeFirst_orbit]; exact hf)
  have hklt : k<2*(n+1) := by
    obtain ⟨f,hf⟩ := hR
    exact lt_of_le_of_lt (hkf f hf) (edgeFirst_lt _ _ _ f)
  intro f hf
  have hh := edgeFirst_le_position a (s*partialReversal a ha T) ha ht (⟨k,hklt⟩ : Dart n)
  simp only [heq] at hh
  exact hh.trans (hkf f hf)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma treeExtension_next (a s : Perm (Dart n)) (C R T : Finset (Orbit a))
    (hT : T∈treeExtensions a s C R) (e : Orbit a) :
    T∈treeExtensions a s (if e∈T then insert e C else C) (R.erase e) := by
  obtain ⟨hC,hR,hf,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  rw [mem_treeExtensions]
  by_cases he : e∈T
  · rw [ite_eq_left he]
    refine ⟨Finset.insert_subset_iff.mpr ⟨he,hC⟩,?_,hf,hc⟩
    intro f hf
    by_cases hfe : f=e
    · exact Finset.mem_union_left _ (hfe ▸ Finset.mem_insert_self _ _)
    · rcases Finset.mem_union.mp (hR hf) with h|h
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hfe,h⟩)
  · rw [ite_eq_right he]
    refine ⟨hC,?_,hf,hc⟩
    intro f hf
    rcases Finset.mem_union.mp (hR hf) with h|h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun hfe => he (hfe ▸ hf),h⟩)

lemma explorationActivity_step_cross (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (select : EdgeSelector a) (C R T : Finset (Orbit a)) (hR : R.Nonempty)
    (hT : T∈treeExtensions a s C R) (hd : Disjoint C R) (k : ℕ) :
    explorationActivity a s select C R T (k+1)=
      (if ∀ f∈R.erase (select C R hR).val,¬FundamentalCross a s T (select C R hR).val f then 1 else 0)+
      explorationActivity a s select (if (select C R hR).val∈T then insert (select C R hR).val C else C)
        (R.erase (select C R hR).val) T k := by
  let e := (select C R hR).val
  have heR : e∈R := (select C R hR).property
  have heC : e∉C := fun h => Finset.disjoint_left.mp hd h heR
  have ⟨hCT,hTR,hf,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  by_cases he : e∈T
  · have hl : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) := by
      intro hh
      have hf' : Multiforest a s (insert e (T.erase e)) := by rwa [Finset.insert_erase he]
      apply hf'.insert_not_reachable ha (Finset.notMem_erase _ _) (hh.mono (spanningGraph_mono a s _))
      intro f hfc
      exact Finset.mem_erase.mpr ⟨fun hfe => heC (hfe ▸ hfc),hCT hfc⟩
    have hb := treeExtension_bridge_iff_no_cross a s ha C R T hT hd he heR
    dsimp [e] at hl hb he
    simp only [explorationActivity,dite_eq_left hR]
    change (if _ then _ else if _ then _ else _)=_
    simp only [ite_eq_right hl,hb]
    simp only [he,ite_true]
    split_ifs <;> simp
  · have hb : (spanningGraph a s ((C∪R.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
        (orbit s e.out) (orbit s (a e.out)) := by
      apply (hc.preconnected _ _).mono (spanningGraph_mono a s _)
      intro f hft
      rcases Finset.mem_union.mp (hTR hft) with hh|hh
      · exact Finset.mem_union_left _ hh
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun hfe => he (hfe ▸ hft),hh⟩)
    have hs : ¬FundamentalCross a s T e e := by simp [FundamentalCross,he]
    have hl := treeExtension_loop_iff_no_cross a s ha C R T hT hd he
    have heq : (∀ f∈R,¬FundamentalCross a s T e f) ↔
        ∀ f∈R.erase e,¬FundamentalCross a s T e f := by
      constructor
      · exact fun h f hf => h f (Finset.mem_of_mem_erase hf)
      · intro h f hf
        by_cases hfe : f=e
        · exact hfe ▸ hs
        · exact h f (Finset.mem_erase.mpr ⟨hfe,hf⟩)
    rw [heq] at hl
    dsimp [e] at hl hb he
    simp only [explorationActivity,dite_eq_left hR]
    change (if _ then _ else if _ then _ else _)=_
    simp only [hl]
    simp only [hb,not_true_eq_false,ite_false,he]
    split_ifs <;> simp

/-- Any increasing adaptive selector counts exactly the active edges of the
completed branch. This is an equality for the original forced-choice count. -/
theorem explorationActivity_eq_orderedActive (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (select : EdgeSelector a) (T : Finset (Orbit a)) (rank : Orbit a→ℕ)
    (hi : Function.Injective rank)
    (hmin : ∀ C R hR, T∈treeExtensions a s C R →
      ∀ f∈R,rank (select C R hR).val ≤ rank f)
    (k : ℕ) (C R : Finset (Orbit a)) (hk : R.card≤k)
    (hT : T∈treeExtensions a s C R) (hd : Disjoint C R)
    (hsuf : ∀ e∈R,∀ f,rank e < rank f → f∈R) :
    explorationActivity a s select C R T k=(R.filter (OrderedActive a s T rank)).card := by
  induction k generalizing C R with
  | zero =>
    have hR : R=∅ := Finset.card_eq_zero.mp (by omega)
    subst R
    simp [explorationActivity]
  | succ k ih =>
    by_cases hR : R.Nonempty
    · let e := (select C R hR).val
      have heR : e∈R := (select C R hR).property
      let R' := R.erase e
      let C' := if e∈T then insert e C else C
      have hmin' : ∀ f∈R,rank e ≤ rank f := hmin C R hR hT
      have hact : (∀ f∈R',¬FundamentalCross a s T e f) ↔ OrderedActive a s T rank e := by
        constructor
        · intro hh f hlt
          apply hh f (Finset.mem_erase.mpr ⟨fun hfe => by rw [hfe] at hlt; omega,hsuf e heR f hlt⟩)
        · intro hh f hf
          obtain ⟨hne,hfR⟩ := Finset.mem_erase.mp hf
          have hle := hmin' f hfR
          have hneq : rank e≠rank f := fun heq => hne (hi heq).symm
          exact hh f (by omega)
      have hk' : R'.card≤k := by
        have hh := Finset.card_erase_add_one heR
        dsimp [R']
        omega
      have hd' : Disjoint C' R' := by
        dsimp [C',R']
        split_ifs
        · exact Finset.disjoint_insert_left.mpr ⟨Finset.notMem_erase _ _,hd.mono_right (Finset.erase_subset _ _)⟩
        · exact hd.mono_right (Finset.erase_subset _ _)
      have hs' : ∀ g∈R',∀ f,rank g < rank f → f∈R' := by
        intro g hg f hgf
        have hgR := Finset.mem_of_mem_erase hg
        have hge := hmin' g hgR
        exact Finset.mem_erase.mpr ⟨fun hfe => by rw [hfe] at hgf; omega,hsuf g hgR f hgf⟩
      have hrec := ih C' R' hk' (treeExtension_next a s C R T hT e) hd' hs'
      rw [explorationActivity_step_cross a s ha select C R T hR hT hd k]
      change (if _ then 1 else 0)+explorationActivity a s select C' R' T k=_
      change (if ∀ f∈R',¬FundamentalCross a s T e f then 1 else 0)+_=_
      simp only [hact,hrec]
      conv_rhs => rw [← Finset.insert_erase heR]
      by_cases h : OrderedActive a s T rank e
      · rw [ite_eq_left h,Finset.filter_insert,ite_eq_left h,
          Finset.card_insert_of_notMem (by simp)]
        exact Nat.add_comm _ _
      · rw [ite_eq_right h,Finset.filter_insert,ite_eq_right h,zero_add]
    · have he : R=∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      subst R
      simp [explorationActivity]

/-- Specialization to the actual rooted-tour selector. Thus the exponent in
`loopPolynomial_tour_activity` is the exact ordered fundamental activity. -/
theorem tourActivity_eq_card (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (hT : T∈treeExtensions a s ∅ Finset.univ) :
    explorationActivity a s (tourSelector a s ha) ∅ Finset.univ T (Fintype.card (Orbit a)) =
      (Finset.univ.filter (OrderedActive a s T
        (edgeFirst a (s*partialReversal a ha T) (treeExtension_tour a s ha ∅ Finset.univ T hT)))).card := by
  apply explorationActivity_eq_orderedActive a s ha _ T _ (edgeFirst_injective _ _ _)
  · intro C R hR h f hf
    have hh := (mem_treeExtensions a s C R T).mp h
    exact tourSelector_least a s ha C R T hR hh.1 hh.2.1 _ f hf
  · simp
  · exact hT
  · simp
  · intro e he f hlt
    exact Finset.mem_univ f

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CanonicalBijection
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords
variable {n : ℕ}

lemma sameCycle_edge_out (a p : Perm (Dart n)) (ha : Function.Involutive a) (y : Dart n) :
    p.SameCycle (orbit a y).out (a (orbit a y).out) ↔ p.SameCycle y (a y) := by
  rcases (MapFinite.mk_eq_iff_involution a ha y (orbit a y)).mp rfl with hh|hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh,ha]
    exact ⟨SameCycle.symm,SameCycle.symm⟩

/-- Exact fundamental-cut incidence for a selected tree edge in canonical
rooted tour order. All representative choices have been removed. -/
theorem fundamentalCross_tree_chord (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (hT : Multiforest a s T)
    (ht : s*partialReversal a ha T=(List.finRange (2*(n+1))).formPerm)
    (x y : Opener a) (hx : orbit a x.val∈T) (hne : x≠y) :
    FundamentalCross a s T (orbit a x.val) (orbit a y.val) ↔ Cross a x y := by
  have hneq : orbit a x.val≠orbit a y.val := fun h => hne (orbit_opener_injective a ha h)
  rw [fundamentalCross_tour_cut a s ha T hT hx hneq,ht,edgeSwap_eq a ha x.val,
    sameCycle_edge_out a _ ha y.val]
  obtain ⟨h1,h2,h3,h4⟩ := opener_endpoints_ne a ha y x hne.symm
  rw [ordered_tour_cut _ (List.pairwise_lt_finRange _) List.mem_finRange x.val (a x.val)
    x.property y.val (a y.val) h1 h2 h3 h4]
  have hx' := x.property
  have hy' := y.property
  have hv1 := Fin.val_ne_of_ne h1
  have hv2 := Fin.val_ne_of_ne h2
  have hv3 := Fin.val_ne_of_ne h3
  have hv4 := Fin.val_ne_of_ne h4
  unfold Cross
  simp only [Fin.lt_def] at hx' hy' ⊢
  omega

/-- In a genuine planar two-colour canonical tour, fundamental incidence is
exactly alternating chords. The dual maximal-orbit condition excludes
crossings between two non-tree edges. -/
theorem fundamentalCross_iff_chord (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (hT : Multiforest a s T)
    (ht : s*partialReversal a ha T=(List.finRange (2*(n+1))).formPerm)
    (hdual : Nat.card (Orbit (partialReversal a ha Tᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+Tᶜ.card)
    (x y : Opener a) (hne : x≠y) :
    FundamentalCross a s T (orbit a x.val) (orbit a y.val) ↔ Cross a x y := by
  by_cases hx : orbit a x.val∈T
  · exact fundamentalCross_tree_chord a s ha T hT ht x y hx hne
  by_cases hy : orbit a y.val∈T
  · rw [fundamentalCross_symm]
    exact (fundamentalCross_tree_chord a s ha T hT ht y x hy hne.symm).trans or_comm
  have hnc : ¬Cross a x y := by
    rintro (hh|hh)
    · exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange Tᶜ hdual
        x.val y.val (Finset.mem_compl.mpr hx) (Finset.mem_compl.mpr hy) hh.1 hh.2.1 hh.2.2
    · exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange Tᶜ hdual
        y.val x.val (Finset.mem_compl.mpr hy) (Finset.mem_compl.mpr hx) hh.1 hh.2.1 hh.2.2
  simp only [FundamentalCross,hx,hy,false_and,or_self,hnc]

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords Inventory
variable {n : ℕ}

lemma canonical_tourNumbering (p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e)
    (he : p=(List.finRange (2*(n+1))).formPerm) : tourNumbering p hp=1 := by
  apply (tourNumbering_unique p hp 1 rfl ?_).symm
  intro i
  rw [he,formPerm_finRange_eq_rotate]
  rfl

lemma edgeFirst_canonical (a p : Perm (Dart n)) (ha : Function.Involutive a)
    (hp : ∀ d e,p.SameCycle d e) (he : p=(List.finRange (2*(n+1))).formPerm)
    (x : Opener a) : edgeFirst a p hp (orbit a x.val)=x.val.val := by
  rw [edgeFirst,canonical_tourNumbering p hp he]
  have hh := (MapFinite.mk_eq_iff_involution a ha x.val (orbit a x.val)).mp rfl
  have hx := x.property
  rcases hh with hh|hh
  · conv_rhs => rw [hh]
    rw [hh] at hx
    exact min_eq_left hx.le
  · conv_rhs => rw [hh]
    rw [hh,ha] at hx
    exact min_eq_right hx.le

/-- The ordered fundamental activity of any edge is precisely the absence
of a later-first chord crossing. -/
theorem orderedActive_chord (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (T : Finset (Orbit a)) (hT : Multiforest a s T)
    (hp : ∀ d e,(s*partialReversal a ha T).SameCycle d e)
    (ht : s*partialReversal a ha T=(List.finRange (2*(n+1))).formPerm)
    (hdual : Nat.card (Orbit (partialReversal a ha Tᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+Tᶜ.card)
    (x : Opener a) :
    OrderedActive a s T (edgeFirst a (s*partialReversal a ha T) hp) (orbit a x.val) ↔
      ¬∃ j : Dart n,x.val < j ∧ j < a x.val ∧ a x.val < a j := by
  constructor
  · intro h ⟨j,hxj,hjx,haxj⟩
    let y : Opener a := ⟨j,(hjx.trans haxj)⟩
    have hne : x≠y := fun h => (ne_of_lt hxj) (congrArg Subtype.val h)
    apply h (orbit a y.val)
    · rw [edgeFirst_canonical a _ ha hp ht x,edgeFirst_canonical a _ ha hp ht y]
      exact hxj
    · exact (fundamentalCross_iff_chord a s ha T hT ht hdual x y hne).mpr (Or.inl ⟨hxj,hjx,haxj⟩)
  · intro h f hxf hcross
    obtain ⟨y,rfl⟩ := opener_orbit_surjective a ha hf f
    rw [edgeFirst_canonical a _ ha hp ht x,edgeFirst_canonical a _ ha hp ht y] at hxf
    have hxy : x.val < y.val := hxf
    have hne : x≠y := fun he => (ne_of_lt hxy) (congrArg Subtype.val he)
    rcases (fundamentalCross_iff_chord a s ha T hT ht hdual x y hne).mp hcross with hh|hh
    · exact h ⟨y.val,hh⟩
    · exact (not_lt_of_ge hxy.le) hh.1

/-- Counting openers or their matching closers gives the identical activity
exponent, including deterministic one-edge cases. -/
lemma sum_closers_eq_openers (a : Perm (Dart n)) (ha : Function.Involutive a) :
    (∑ i : Dart n,if a i < i ∧ ¬∃ j : Dart n,a i < j ∧ j < i ∧ i < a j then 1 else 0)=
      ∑ x : Opener a,if ¬∃ j : Dart n,x.val < j ∧ j < a x.val ∧ a x.val < a j then 1 else 0 := by
  have hswap := Equiv.sum_comp a (fun i : Dart n =>
    if a i < i ∧ ¬∃ j : Dart n,a i < j ∧ j < i ∧ i < a j then (1:ℕ) else 0)
  rw [← hswap]
  trans ∑ i : Dart n,if i < a i then
    (if ¬∃ j : Dart n,i < j ∧ j < a i ∧ a i < a j then (1:ℕ) else 0) else 0
  · apply Finset.sum_congr rfl
    intro i _
    rw [ha]
    by_cases hi : i < a i <;> simp [hi]
  · rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords Inventory
variable {n : ℕ}

/-- The actual adaptive FK expansion exponent is the number of flexible
closing positions in the true identified word. No weight identity is assumed. -/
theorem canonical_activity_eq_flexible (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (ht : M.val.2*partialReversal M.val.1 M.property.1 T=(List.finRange (2*(n+1))).formPerm) :
    explorationActivity M.val.1 M.val.2 (tourSelector M.val.1 M.val.2 M.property.1)
      ∅ Finset.univ T (Fintype.card (Orbit M.val.1))=
      flexibleCount (List.ofFn (matchingWord M.val.1 T)) [] := by
  let a := M.val.1
  let s := M.val.2
  let ha := M.property.1
  let hf := M.property.2.1
  have hp := treeExtension_tour a s ha ∅ Finset.univ T hT
  have hforest : Multiforest a s T := (mem_treeExtensions a s ∅ Finset.univ T).mp hT |>.2.2.1
  obtain ⟨hmax,hdual⟩ := canonical_tour_maximal M T ht
  have hnc : ∀ x y : Dart n,decide (orbit a x∈T)=decide (orbit a y∈T) →
      x < y → y < a x → a x < a y → False := by
    intro x y hh hxy hyx haxy
    have hh' : (orbit a x∈T) ↔ (orbit a y∈T) := by simpa only [decide_eq_decide] using hh
    by_cases hx : orbit a x∈T
    · exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange T hmax x y hx (hh'.mp hx) hxy hyx haxy
    · have hy : orbit a y∉T := fun h => hx (hh'.mpr h)
      exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange Tᶜ hdual x y
        (Finset.mem_compl.mpr hx) (Finset.mem_compl.mpr hy) hxy hyx haxy
  have hw := matching_flexibleCount a ha hf (fun i => decide (orbit a i∈T))
    (fun i => by rw [orbit_perm]) hnc
  change flexibleCount (List.ofFn (matchingWord a T)) []=_ at hw
  rw [tourActivity_eq_card M.val.1 M.val.2 M.property.1 T hT,hw,sum_closers_eq_openers a ha]
  have he := Equiv.sum_comp (openerOrbitEquiv a ha hf)
    (fun e : Orbit a => if OrderedActive a s T (edgeFirst a (s*partialReversal a ha T) hp) e then (1:ℕ) else 0)
  rw [Finset.card_filter]
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  have hh := orderedActive_chord a s ha hf T hforest hp ht hdual x
  change (if OrderedActive a s T (edgeFirst a (s*partialReversal a ha T) hp) (orbit a x.val) then 1 else 0)=_
  rw [hh]
  split_ifs <;> rfl

end FKCRT
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

lemma offspring_zero_unattainable (P : Parameters) (k : ℕ)
    (h : ¬∃ c : CoreLabel,c.arity=k) : (actualOffspring P).law k=0 := by
  rw [← root_fiber]
  have hc (c : CoreLabel) : c.arity≠k := fun hc => h ⟨c,hc⟩
  simp only [ite_eq_right (hc _),tsum_zero]

lemma offspring_pos_attainable (P : Parameters) (c : CoreLabel) :
    0<(actualOffspring P).law c.arity := by
  rw [← root_fiber]
  exact (rootLaw_pos P c).trans_le (by
    simpa using ENNReal.le_tsum (f := fun d : CoreLabel => if d.arity=c.arity then rootLaw P d else 0) c)

/-- Exact disintegration identity. The marks are independent draws from
this kernel after the actual offspring array is fixed. -/
theorem offspring_mul_mark (P : Parameters) (k : ℕ) (c : CoreLabel) :
    (actualOffspring P).law k*markLaw P k c=if c.arity=k then rootLaw P c else 0 := by
  by_cases h : ∃ d : CoreLabel,d.arity=k
  · rw [markLaw_apply P k h]
    by_cases hc : c.arity=k
    · rw [ite_eq_left hc]
      have hk := offspring_pos_attainable P c
      rw [hc] at hk
      rw [mul_comm (rootLaw P c),← mul_assoc,ENNReal.mul_inv_cancel hk.ne'
        ((actualOffspring P).law.apply_ne_top k),one_mul]
    · simp [hc]
  · rw [offspring_zero_unattainable P k h,zero_mul,ite_eq_right (fun hc => h ⟨c,hc⟩)]

/-- The finite product form used in the source's conditional marked law. -/
theorem product_disintegration (P : Parameters) {I : Type*} [Fintype I]
    (d : I→ℕ) (a : I → CoreLabel) :
    (∏ i,(actualOffspring P).law (d i))*(∏ i,markLaw P (d i) (a i))=
      if ∀ i,(a i).arity=d i then ∏ i,rootLaw P (a i) else 0 := by
  rw [← Finset.prod_mul_distrib]
  simp_rw [offspring_mul_mark]
  by_cases h : ∀ i,(a i).arity=d i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

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

lemma CriticalEvenOffspring.spine_integrable_dom (p : CriticalEvenOffspring) (b : ℕ×ℕ → ℝ)
    (hb : ∀ z,|b z| ≤ z.1) : Integrable b p.spineLaw := by
  exact p.spine_integrable_fst.mono' (measurable_of_countable b).aestronglyMeasurable
    (ae_of_all _ (fun z =>  by simpa only [Real.norm_eq_abs] using hb z))

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ConditionedTrees
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma CriticalEvenOffspring.code_singleton (p : CriticalEvenOffspring) (n : ℕ)
    (d : Code (2*n+1)) : p.codeLaw n {d}=ENNReal.ofReal (codeWeight p d/codePartition p (2*n+1)) := by
  rw [← ofReal_measureReal,← integral_indicator_one (measurableSet_singleton d),p.code_integral]
  simp [Set.indicator]

lemma CriticalEvenOffspring.marked_singleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : CriticalEvenOffspring) (κ : ℕ → PMF A) (n : ℕ)
    (d : Code (2*n+1)) (a : Fin (2*n+1) → A) :
    p.markedCodeLaw (fun k => (κ k).toMeasure) n {(d,a)}=
      ENNReal.ofReal (codeWeight p d/codePartition p (2*n+1)) * ∏ i,κ (d.val i).val (a i) := by
  have he : ({(d,a)} : Set (Code (2*n+1)×(Fin (2*n+1) → A)))={d}×ˢ{a} := by ext x;simp
  rw [he,CriticalEvenOffspring.markedCodeLaw,Measure.compProd_apply_prod
    (measurableSet_singleton _) (measurableSet_singleton _),lintegral_singleton]
  simp only [codeMarkKernel,Kernel.coe_mk,codeMarkLaw,Measure.pi_singleton ]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [p.code_singleton,mul_comm]

end FKCRT.TreeCoding
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- The actual conditioned independent marking density, with no change of
root distribution and no appeal to a conditional GW law as a hypothesis. -/
theorem actual_marked_singleton (P : Parameters) (n : ℕ)
    (d : Code (2*n+1)) (a : Fin (2*n+1) → CoreLabel) :
    (actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) n {(d,a)}=
      (if ∀ i,(a i).arity=(d.val i).val then ∏ i,CoreLabel.rootLaw P (a i) else 0)/
        ENNReal.ofReal (codePartition (actualOffspring P) (2*n+1)) := by
  rw [CriticalEvenOffspring.marked_singleton,ENNReal.ofReal_div_of_pos
    (codePartition_odd_pos _ n)]
  have hw : ENNReal.ofReal (codeWeight (actualOffspring P) d)=
      ∏ i,(actualOffspring P).law (d.val i).val := by
    unfold codeWeight
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => (actualOffspring P).nonneg _)]
    simp only [CriticalEvenOffspring.law_apply]
  rw [hw]
  simp only [div_eq_mul_inv]
  rw [mul_right_comm,CoreLabel.product_disintegration]
  by_cases h : ∀ i,(a i).arity=(d.val i).val
  · rw [ite_eq_left h,ite_eq_left h]
  · rw [ite_eq_right h,ite_eq_right h]

end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

namespace CoreTree

lemma rootMass_product (P : Parameters) {N : ℕ} (x : MarkedCode N) :
    (∏ i,CoreLabel.rootMass P (x.val.2 i))=
      wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P)) (ofMarkedCode x).word/emptyTotal P := by
  have h := (ofMarkedCode x).productMass_eq (flexParameter P)
    (Real.sqrt (radiusParameter P)) (emptyTotal P) (emptyTotal_pos P).ne'
  rw [productMass_labels,ofMarkedCode_labels,List.map_ofFn,List.prod_ofFn] at h
  exact h

lemma rootLaw_product (P : Parameters) {N : ℕ} (x : MarkedCode N) :
    (∏ i,CoreLabel.rootLaw P (x.val.2 i))=ENNReal.ofReal
      (wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P)) (ofMarkedCode x).word/emptyTotal P) := by
  rw [← rootMass_product]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => CoreLabel.rootMass_nonneg P _)]
  rfl

end CoreTree

/-- Complete pointwise finite-law density, now expressed in the word of the
original map bijection. Every leaf, every admissible arity and the common
normalizing factor are retained. -/
theorem actual_marked_word_density (P : Parameters) (n : ℕ)
    (x : CoreTree.MarkedCode (2*n+1)) :
    (actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) n {x.val}=
      ENNReal.ofReal (wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P))
        ((CoreTree.markedWordEquiv (2*n)) x).val.val/emptyTotal P)/
          ENNReal.ofReal (codePartition (actualOffspring P) (2*n+1)) := by
  rw [actual_marked_singleton P n x.val.1 x.val.2,ite_eq_left x.property,
    CoreTree.rootLaw_product P x]
  rfl

/-- There is no positive mass on inconsistent marks. In particular the
arbitrary mark at an impossible offspring value is irrelevant. -/
theorem actual_marked_compatible (P : Parameters) (n : ℕ) :
    ∀ᵐ x ∂(actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) n,
      ∀ i,(x.2 i).arity=(x.1.val i).val := by
  rw [ae_iff_of_countable]
  intro x hx
  by_contra hc
  have h := actual_marked_singleton P n x.1 x.2
  rw [ite_eq_right hc,ENNReal.zero_div] at h
  exact hx h

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_RootedLaw
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma CanonicalTreeMap.tree (X : CanonicalTreeMap n) :
    X.A∈treeExtensions X.a X.s ∅ Finset.univ := treeExtension_of_tour X.toMap X.A X.tour_connected

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma edge_reachable_rep (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Set (Orbit a)) (d : Dart n) :
    (spanningGraph a s A).Reachable (orbit s (orbit a d).out) (orbit s (a (orbit a d).out)) ↔
      (spanningGraph a s A).Reachable (orbit s d) (orbit s (a d)) := by
  rcases (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp rfl with hh|hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh,ha]
    exact ⟨SimpleGraph.Reachable.symm,SimpleGraph.Reachable.symm⟩

lemma relabelEdges_erase (r a : Perm (Dart n)) (A : Finset (Orbit a))
    (e : Orbit (relabelPerm r a)) :
    relabelEdges r a (A.erase (relabelOrbit r a e))=(relabelEdges r a A).erase e := by
  ext f
  simp only [mem_relabelEdges,Finset.mem_erase]
  exact and_congr_left fun _ => not_congr (relabelOrbit r a).injective.eq_iff

lemma fundamentalCross_relabel (r a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (e f : Orbit (relabelPerm r a)) :
    FundamentalCross (relabelPerm r a) (relabelPerm r s) (relabelEdges r a T) e f ↔
      FundamentalCross a s T (relabelOrbit r a e) (relabelOrbit r a f) := by
  have hr (A : Finset (Orbit a)) (g : Orbit (relabelPerm r a)) :
      (spanningGraph (relabelPerm r a) (relabelPerm r s) (relabelEdges r a A : Set _)).Reachable
        (orbit (relabelPerm r s) g.out) (orbit (relabelPerm r s) (relabelPerm r a g.out)) ↔
      (spanningGraph a s (A : Set _)).Reachable (orbit s (relabelOrbit r a g).out)
        (orbit s (a (relabelOrbit r a g).out)) := by
    induction g using Quotient.inductionOn with
    | _ d =>
      change (spanningGraph (relabelPerm r a) (relabelPerm r s) (relabelEdges r a A : Set _)).Reachable
        (orbit (relabelPerm r s) (orbit (relabelPerm r a) d).out)
        (orbit (relabelPerm r s) (relabelPerm r a (orbit (relabelPerm r a) d).out)) ↔ (spanningGraph a s (A : Set _)).Reachable
        (orbit s (orbit a (r d)).out) (orbit s (a (orbit a (r d)).out))
      rw [edge_reachable_rep (relabelPerm r a) _ (relabelPerm_involutive r a ha),edge_reachable_rep a s ha]
      have he : (relabelEdges r a A : Set _)=(relabelOrbit r a) ⁻¹' (A : Set _) := by ext x; simp
      rw [he]
      have hh := @SimpleGraph.Iso.reachable_iff _ _ _ _ (spanningGraphRelabel r a s (A : Set _))
        (orbit (relabelPerm r s) d) (orbit (relabelPerm r s) (relabelPerm r a d))
      change (spanningGraph a s (A : Set _)).Reachable
        (relabelOrbit r s (orbit (relabelPerm r s) d))
        (relabelOrbit r s (orbit (relabelPerm r s) (relabelPerm r a d))) ↔ _ at hh
      simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hh.symm
  unfold FundamentalCross
  rw [mem_relabelEdges,mem_relabelEdges,← relabelEdges_erase,← relabelEdges_erase,hr,hr]

lemma edgeFirst_rep (a p : Perm (Dart n)) (ha : Function.Involutive a)
    (hp : ∀ d e,p.SameCycle d e) (d : Dart n) :
    edgeFirst a p hp (orbit a d)=min ((tourNumbering p hp).symm d).val
      ((tourNumbering p hp).symm (a d)).val := by
  unfold edgeFirst
  rcases (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp rfl with hh|hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh,ha]
    exact min_comm _ _

lemma canonicalizeTree_rank (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (e : Orbit (canonicalizeTree M T hT).a) :
    edgeFirst (canonicalizeTree M T hT).a
      ((canonicalizeTree M T hT).s*partialReversal _ (canonicalizeTree M T hT).valid.1
        (canonicalizeTree M T hT).A) (canonicalizeTree M T hT).tour_connected e =
    edgeFirst M.val.1 (M.val.2*partialReversal M.val.1 M.property.1 T)
      (treeExtension_tour _ _ _ _ _ _ hT)
      (relabelOrbit (tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
        (treeExtension_tour _ _ _ _ _ _ hT)) M.val.1 e) := by
  let p := M.val.2*partialReversal M.val.1 M.property.1 T
  let hp := treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT
  let r := tourNumbering p hp
  let X := canonicalizeTree M T hT
  induction e using Quotient.inductionOn with
  | _ d =>
    have hh := edgeFirst_rep X.a (X.s*partialReversal X.a X.valid.1 X.A)
      X.valid.1 X.tour_connected d
    rw [canonical_tourNumbering _ _ X.tour] at hh
    change edgeFirst X.a (X.s*partialReversal X.a X.valid.1 X.A) X.tour_connected (orbit X.a d)=_
    rw [hh]
    change min d.val ((relabelPerm r M.val.1) d).val = edgeFirst M.val.1 p hp (orbit M.val.1 (r d))
    rw [edgeFirst_rep M.val.1 p M.property.1]
    change min d.val (r.symm (M.val.1 (r d))).val=min (r.symm (r d)).val (r.symm (M.val.1 (r d))).val
    rw [Equiv.symm_apply_apply]

/-- Forced FK exponents are unchanged by the true rooted normal form. -/
theorem canonicalizeTree_activity (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ) :
    explorationActivity (canonicalizeTree M T hT).a (canonicalizeTree M T hT).s
      (tourSelector (canonicalizeTree M T hT).a (canonicalizeTree M T hT).s (canonicalizeTree M T hT).valid.1) ∅ Finset.univ
      (canonicalizeTree M T hT).A (Fintype.card (Orbit (canonicalizeTree M T hT).a)) =
    explorationActivity M.val.1 M.val.2 (tourSelector M.val.1 M.val.2 M.property.1) ∅ Finset.univ
      T (Fintype.card (Orbit M.val.1)) := by
  let X := canonicalizeTree M T hT
  let r := tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
    (treeExtension_tour _ _ _ _ _ _ hT)
  rw [tourActivity_eq_card _ _ X.valid.1 _ X.tree,tourActivity_eq_card _ _ M.property.1 _ hT]
  apply Finset.card_equiv (relabelOrbit r M.val.1)
  intro e
  change Orbit X.a at e
  change (e∈Finset.univ.filter (OrderedActive X.a X.s X.A
    (edgeFirst X.a (X.s*partialReversal X.a X.valid.1 X.A) X.tour_connected))) ↔
    ((relabelOrbit r M.val.1 e)∈Finset.univ.filter (OrderedActive M.val.1 M.val.2 T
      (edgeFirst M.val.1 (M.val.2*partialReversal M.val.1 M.property.1 T)
        (treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT))))
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  unfold OrderedActive
  constructor
  · intro h f hlt
    have hf := h ((relabelOrbit r M.val.1).symm f)
    rw [canonicalizeTree_rank M T hT e] at hf
    have hrr := canonicalizeTree_rank M T hT ((relabelOrbit r M.val.1).symm f)
    rw [hrr] at hf
    have hef : relabelOrbit (tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
        (treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT)) M.val.1
        ((relabelOrbit r M.val.1).symm f)=f := (relabelOrbit r M.val.1).apply_symm_apply f
    rw [hef] at hf
    exact fun hh => hf hlt ((fundamentalCross_relabel r M.val.1 M.val.2 M.property.1 T e _).mpr
      (by simpa only [Equiv.apply_symm_apply] using hh))
  · intro h f hlt
    rw [canonicalizeTree_rank M T hT e,canonicalizeTree_rank M T hT f] at hlt
    exact fun hh => h _ hlt ((fundamentalCross_relabel r M.val.1 M.val.2 M.property.1 T e f).mp hh)

end FKCRT
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
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open Inventory
variable {n : ℕ}

lemma rootedWord_activity (x : RootedSpanningTree n) :
    treeActivity x=flexibleCount (List.ofFn (rootedWordEquiv n x).val) [] := by
  let X := canonicalizeTree x.1.out x.2.val x.2.property
  have hn : Fintype.card (Orbit x.1.out.val.1)=n+1 :=
    reversal_card x.1.out.val.1 x.1.out.property.1 x.1.out.property.2.1
  have h1 := canonicalizeTree_activity x.1.out x.2.val x.2.property
  have h2 := canonical_activity_eq_flexible X.toMap X.A X.tree X.tour
  rw [hn] at h1
  exact h1.symm.trans h2

/-- Full finite weighted pushforward. An arbitrary observable on the actual
rooted map quotient is retained; this is stronger than a partition equality. -/
theorem loopPolynomial_word_transport (t : ℝ) (ht : t≠0) (F : RootedMap n→ℝ) :
    (∑ M : RootedMap n,F M*loopPolynomial t M)=
      ∑ w : SuccessfulWord n,
        F ((rootedWordEquiv n).symm w).1 * (1+t)^flexibleCount (List.ofFn w.val) [] := by
  have hs : (∑ M : RootedMap n,F M*loopPolynomial t M)=
      ∑ x : RootedSpanningTree n,F x.1*(1+t)^treeActivity x := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro M _
    rw [loopPolynomial_tour_activity t ht,Finset.mul_sum]
    change (∑ T∈treeExtensions (reversal M) (rotation M) ∅ Finset.univ,
      F M*(1+t)^explorationActivity (reversal M) (rotation M)
        (tourSelector (reversal M) (rotation M) M.out.property.1) ∅ Finset.univ T (n+1))=_
    exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
  rw [hs]
  have hh := Equiv.sum_comp (rootedWordEquiv n) (fun w : SuccessfulWord n =>
    F ((rootedWordEquiv n).symm w).1*(1+t)^flexibleCount (List.ofFn w.val) [])
  rw [← hh]
  apply Finset.sum_congr rfl
  intro x _
  rw [Equiv.symm_apply_apply,rootedWord_activity]

/-- Exact FK marginal on *unlabelled rooted* maps, with the original cluster
weight. The common sqrt(q) factor is explicit, not absorbed into the law. -/
theorem fk_word_transport (q : ℝ) (hq : 0<q) (F : RootedMap n→ℝ) :
    (∑ M : RootedMap n, ∑ A : Finset (Edge M),F M*fkWeight q M A)=
      Real.sqrt q * ∑ w : SuccessfulWord n,
        F ((rootedWordEquiv n).symm w).1 * (1+Real.sqrt q)^flexibleCount (List.ofFn w.val) [] := by
  simp_rw [← Finset.mul_sum,fk_marginal_loopPolynomial q hq]
  calc
    _=Real.sqrt q*(∑ M : RootedMap n,F M*loopPolynomial (Real.sqrt q) M) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      ring
    _=_ := congrArg (Real.sqrt q*·) (loopPolynomial_word_transport _ (ne_of_gt (Real.sqrt_pos.mpr hq)) F)

end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable
namespace FKCRT
open Inventory

lemma Parameters.ofQ_ratio (q : ℝ) (hq : 4<q) :
    2*(Parameters.ofQ q hq).p/(1-(Parameters.ofQ q hq).p)=Real.sqrt q := by
  have hs : 0<Real.sqrt q+2 := by positivity
  dsimp [Parameters.ofQ]
  field_simp
  ring

end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace FKCRT
open Inventory

lemma partition_typedPartition (q : ℝ) (hq : 0<q) (n : ℕ) :
    partition q n=Real.sqrt q*typedPartition q n := by
  simpa only [partition,typedPartition,one_mul] using fk_word_transport q hq (n:=n) (fun _ => 1)

lemma typedPartition_pos (q : ℝ) (hq : 0<q) (n : ℕ) : 0 < typedPartition q n := by
  have h := partition_pos hq n
  rw [partition_typedPartition q hq n] at h
  exact pos_of_mul_pos_right h (Real.sqrt_nonneg q)

/-- The original all-edge metric and normalized degree measure are retained
under the exact finite word pushforward. This is a finite identity, not the
unproved GHP limit. -/
theorem finiteExpectation_typed (q : ℝ) (hq : 0<q) (scale : ℝ) (n : ℕ)
    (F : MetricMeasureData→ℝ) :
    finiteExpectation q scale n F=
      ∑ w : SuccessfulWord n,
        ((1+Real.sqrt q)^flexibleCount (List.ofFn w.val) []/typedPartition q n)*
          F (mapSpace scale ((rootedWordEquiv n).symm w).1) := by
  unfold finiteExpectation
  have h := fk_word_transport q hq (n:=n) (fun M => F (mapSpace scale M))
  have hs : Real.sqrt q≠0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hnum : (∑ M : RootedMap n,∑ A : Finset (Edge M),
      fkWeight q M A*F (mapSpace scale M))=
      Real.sqrt q*∑ w : SuccessfulWord n,
        (1+Real.sqrt q)^flexibleCount (List.ofFn w.val) []*F (mapSpace scale ((rootedWordEquiv n).symm w).1) := by
    calc
      _=(∑ M : RootedMap n,∑ A : Finset (Edge M),F (mapSpace scale M)*fkWeight q M A) := by
        apply Finset.sum_congr rfl
        intro M _
        apply Finset.sum_congr rfl
        intro A _
        exact mul_comm _ _
      _=_ := h
      _=_ := by
        congr 1
        apply Finset.sum_congr rfl
        intro w _
        exact mul_comm _ _
  simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
  rw [hnum,partition_typedPartition q hq n,mul_div_mul_left _ _ hs]

end FKCRT
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

lemma finite_atomic_of_ae_range {X I : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable X] [Fintype I]
    (μ : Measure X) (f : I→X) (hf : Function.Injective f)
    (hs : ∀ᵐ x ∂μ,x∈Set.range f) :
    μ=∑ i : I, μ {f i} • Measure.dirac (f i) := by
  apply Measure.ext_of_singleton
  intro x
  by_cases hx : x∈Set.range f
  · obtain ⟨i,rfl⟩ := hx
    simp only [Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply',
      measurableSet_singleton,Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply,smul_eq_mul]
    simp only [hf.eq_iff,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · have hz : μ {x}=0 := by
      rw [ae_iff_of_countable] at hs
      exact not_not.mp (fun hn => hx (hs x hn))
    rw [hz]
    symm
    simp only [Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply',
      measurableSet_singleton,Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun h => hx ⟨i,h⟩),mul_zero]

namespace Inventory.CoreTree

lemma successfulMarked_word (n : ℕ) (w : SuccessfulWord n) :
    ((markedWordEquiv (2*(n+1))) (successfulMarkedEquiv n w)).val.val=List.ofFn w.val := by
  simp only [successfulMarkedEquiv,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

end Inventory.CoreTree

/-- The genuine independently marked conditioned tree law is exactly a
finite atomic law indexed by the successful words of the original map
bijection, not just proportional formal generating functions. -/
theorem actual_marked_atomic (P : Parameters) (n : ℕ) :
    (actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) (n+1)=
      ∑ w : SuccessfulWord n,
        (ENNReal.ofReal (wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P))
          (List.ofFn w.val)/emptyTotal P)/
          ENNReal.ofReal (codePartition (actualOffspring P) (2*(n+1)+1))) •
          Measure.dirac (CoreTree.successfulMarkedEquiv n w).val := by
  let f : SuccessfulWord n → Code (2*(n+1)+1)×(Fin (2*(n+1)+1)→ CoreLabel) :=
    fun w => (CoreTree.successfulMarkedEquiv n w).val
  have hf : Function.Injective f := Subtype.val_injective.comp (CoreTree.successfulMarkedEquiv n).injective
  have hs : ∀ᵐ x ∂(actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) (n+1),
      x∈Set.range f := by
    filter_upwards [actual_marked_compatible P (n+1)] with x hx
    exact ⟨(CoreTree.successfulMarkedEquiv n).symm ⟨x,hx⟩,
      congrArg Subtype.val ((CoreTree.successfulMarkedEquiv n).apply_symm_apply ⟨x,hx⟩)⟩
  rw [finite_atomic_of_ae_range _ f hf hs]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [actual_marked_word_density P (n+1),CoreTree.successfulMarked_word]

end FKCRT
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

lemma atomic_normalize {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : I → X) (w : I → ℝ)
    (hw : ∀ i,0 ≤ w i) {K : ℝ} (hK : 0 ≤ K)
    (h : μ=∑ i,ENNReal.ofReal (K*w i) • Measure.dirac (f i))
    (hs : 0 < ∑ i,w i) :
    μ=∑ i,ENNReal.ofReal (w i/(∑ j,w j)) • Measure.dirac (f i) := by
  have hm := congrArg (fun ν : Measure X => ν Set.univ) h
  simp only [measure_univ,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one] at hm
  have hm' : (1 : ℝ)=K*∑ i,w i := by
    have hh : ENNReal.ofReal (1 : ℝ)=ENNReal.ofReal (∑ i,K*w i) := by
      simpa only [ENNReal.ofReal_one,ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg hK (hw i))] using hm
    have ht := congrArg ENNReal.toReal hh
    rw [ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun i _ => mul_nonneg hK (hw i)))] at ht
    simpa only [Finset.mul_sum] using ht
  have hK' : K=(∑ i,w i)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hs.ne').mpr hm'.symm
  rw [h,hK']
  congr 1
  apply funext
  intro i
  rw [div_eq_mul_inv,mul_comm]

lemma actual_marked_normalized (q : ℝ) (hq : 4<q) (n : ℕ) :
    (actualOffspring (Parameters.ofQ q hq)).markedCodeLaw
      (fun k => (CoreLabel.markLaw (Parameters.ofQ q hq) k).toMeasure) (n+1)=
      ∑ w : SuccessfulWord n,
        ENNReal.ofReal ((1+Real.sqrt q)^flexibleCount (List.ofFn w.val) []/typedPartition q n) •
          Measure.dirac (CoreTree.successfulMarkedEquiv n w).val := by
  let P := Parameters.ofQ q hq
  let K := (Real.sqrt (radiusParameter P))^(2*(n+1))/emptyTotal P/
    codePartition (actualOffspring P) (2*(n+1)+1)
  have hK : 0 ≤ K := le_of_lt (div_pos (div_pos
    (pow_pos (Real.sqrt_pos.mpr (radiusParameter_pos P)) _) (emptyTotal_pos P))
    (codePartition_odd_pos (actualOffspring P) (n+1)))
  apply atomic_normalize _ _ _ (fun _ => pow_nonneg (by positivity) _) hK _
    (typedPartition_pos q (by linarith) n)
  rw [actual_marked_atomic P n]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [← ENNReal.ofReal_div_of_pos (codePartition_odd_pos (actualOffspring P) (n+1))]
  congr 1
  change (flexParameter P)^flexibleCount (List.ofFn w.val) []*
    (Real.sqrt (radiusParameter P))^(List.ofFn w.val).length/emptyTotal P/
      codePartition (actualOffspring P) (2*(n+1)+1)=_
  rw [List.length_ofFn]
  have hp : flexParameter P=1+Real.sqrt q := by
    exact congrArg (fun t : ℝ => 1+t) (Parameters.ofQ_ratio q hq)
  rw [hp]
  dsimp [K]
  ring

end FKCRT
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

lemma markedMapTest_word (scale : ℝ) (n : ℕ) (F : MetricMeasureData → ℝ)
    (w : SuccessfulWord n) :
    markedMapTest scale n F (CoreTree.successfulMarkedEquiv n w).val=
      F (mapSpace scale ((rootedWordEquiv n).symm w).1) := by
  rw [markedMapTest,dite_eq_left (CoreTree.successfulMarkedEquiv n w).property]
  exact congrArg (fun u : SuccessfulWord n =>
    F (mapSpace scale ((rootedWordEquiv n).symm u).1))
      ((CoreTree.successfulMarkedEquiv n).symm_apply_apply w)

/-- The full original finite FK observable is the integral under the true
independently marked conditioned GW law. No law identification or
normalizing constant remains as a hypothesis. -/
theorem finiteExpectation_marked (q : ℝ) (hq : 4<q) (scale : ℝ) (n : ℕ)
    (F : MetricMeasureData → ℝ) :
    finiteExpectation q scale n F=
      ∫ x,markedMapTest scale n F x ∂(actualOffspring (Parameters.ofQ q hq)).markedCodeLaw
        (fun k => (CoreLabel.markLaw (Parameters.ofQ q hq) k).toMeasure) (n+1) := by
  rw [actual_marked_normalized q hq n]
  rw [integral_finsetSum_measure (fun w _ =>
    (integrable_dirac (f := markedMapTest scale n F) (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure,integral_dirac,smul_eq_mul,markedMapTest_word]
  rw [finiteExpectation_typed q (by linarith)]
  apply Finset.sum_congr rfl
  intro w _
  rw [ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (by positivity) _)
    (typedPartition_pos q (by linarith) n).le)]

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreMetric
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

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Convergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT
open Inventory

/-- GHP convergence of the finite FK laws to the
standard Brownian-excursion CRT, through every positive edge count. -/
theorem finite_fk_maps_converge_to_brownian_crt_oai : MainStatement := by
  intro q hq
  let P := Parameters.ofQ q hq
  refine ⟨crtScale P,crtScale_pos P,?_⟩
  intro Ω mΩ μ hμ B hB hI F hF
  have hh := actual_map_tests P hB hI F hF
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact finiteExpectation_marked q hq (edgeScale P n) n F

end FKCRT
end

end OAI
end

theorem solution : type_of% @OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt_oai := @OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt_oai
