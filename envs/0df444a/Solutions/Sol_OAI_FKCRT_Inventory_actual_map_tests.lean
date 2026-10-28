-- Prove2me | solution 1 for OAI.FKCRT.Inventory.actual_map_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T18:38:14.083422+00:00
-- url     : https://prove2.me/submissions/ef034964-8a1e-47c7-b82a-f0d0222da2c5

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_OAIQ021F004
import Theorems.Thm_OAI_FKCRT_Inventory_actualHeight_CLT
import Theorems.Thm_OAI_FKCRT_Inventory_metric_test_local
import Theorems.Thm_OAI_FKCRT_TreeCoding_CriticalEvenOffspring_jointCode_vervaat_CLT
import Theorems.Thm_OAI_FKCRT_TreeCoding_CriticalEvenOffspring_uniform_degree_spine_limit

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

lemma integral_lipschitz_approx_bound {E Ω : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → E} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {F : E → ℝ} {M : ℝ} (hM : ∀ x y, dist (F x) (F y) ≤ M)
    {L : ℝ≥0} (hL : LipschitzWith L F) {δ : ℝ} (hδ : 0 ≤ δ) :
    |(∫ ω, F (X ω) ∂μ) - ∫ ω, F (Y ω) ∂μ| ≤
      L*δ + M*μ.real {ω | δ ≤ dist (X ω) (Y ω)} := by
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let x₀ := X (Classical.choice hne)
  have h_int (Z : Ω → E) (hZ : AEMeasurable Z μ) : Integrable (fun ω => F (Z ω)) μ := by
    refine Integrable.of_bound ((hL.continuous.measurable.comp_aemeasurable hZ).aestronglyMeasurable)
      (‖F x₀‖+M) (ae_of_all μ (fun ω => ?_))
    have h := hM (Z ω) x₀
    rw [Real.dist_eq] at h
    simpa only [Real.norm_eq_abs] using
      (show |F (Z ω)| ≤ |F x₀|+M from by linarith [abs_sub_abs_le_abs_sub (F (Z ω)) (F x₀)])
  have hi : Integrable (fun ω => F (X ω)-F (Y ω)) μ :=
    (h_int X hX).sub (h_int Y hY)
  have his := hi.norm
  have hset : NullMeasurableSet {ω | dist (X ω) (Y ω) < δ} μ :=
    nullMeasurableSet_lt (hX.dist hY) aemeasurable_const
  rw [← integral_sub (h_int X hX) (h_int Y hY), ← Real.norm_eq_abs]
  calc
    ‖∫ ω, F (X ω)-F (Y ω) ∂μ‖ ≤ ∫ ω, ‖F (X ω)-F (Y ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = (∫ ω in {ω | dist (X ω) (Y ω) < δ}, ‖F (X ω)-F (Y ω)‖ ∂μ) +
        ∫ ω in {ω | δ ≤ dist (X ω) (Y ω)}, ‖F (X ω)-F (Y ω)‖ ∂μ := by
      symm
      simpa only [Set.compl_ofPred, not_lt] using integral_add_compl₀ hset his
    _ ≤ (∫ _ in {ω | dist (X ω) (Y ω) < δ}, (L : ℝ)*δ ∂μ) +
        ∫ _ in {ω | δ ≤ dist (X ω) (Y ω)}, M ∂μ := by
      apply add_le_add
      · apply setIntegral_mono_on₀ his.integrableOn integrableOn_const hset
        intro ω hω
        rw [← dist_eq_norm]
        exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hω.le L.coe_nonneg)
      · apply setIntegral_mono his.integrableOn integrableOn_const
        intro ω
        exact hM _ _
    _ = (L:ℝ)*δ*μ.real {ω | dist (X ω) (Y ω) < δ} +
        M*μ.real {ω | δ ≤ dist (X ω) (Y ω)} := by
      simp only [integral_const, measureReal_restrict_apply, MeasurableSet.univ,
        Set.univ_inter, smul_eq_mul]
      ring
    _ ≤ _ := by
      exact add_le_add (by
        calc (L:ℝ)*δ*μ.real {ω | dist (X ω) (Y ω) < δ}
            ≤ (L:ℝ)*δ*1 := mul_le_mul_of_nonneg_left measureReal_le_one (mul_nonneg L.coe_nonneg hδ)
          _ = (L:ℝ)*δ := mul_one _) le_rfl

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


lemma CriticalEvenOffspring.stream_restrict_law (p : CriticalEvenOffspring) (N : ℕ) :
    HasLaw (fun ω : ℕ → ℕ => fun i : Fin N => ω i.val) (p.iidLaw N) p.streamLaw := by
  refine ⟨(Measurable.of_eval (fun index => measurable_pi_apply index.val)).aemeasurable, ?_⟩
  simpa only [streamLaw, iidLaw, Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => p.law.toMeasure)
      (@Fin.val_injective N))


lemma CriticalEvenOffspring.iid_site_incompatible (p : CriticalEvenOffspring)
    (N : ℕ) (j : ℤ) (hj : ¬Even ((N : ℤ) + j)) :
    (p.iidLaw N).real {d | totalStep d = j} = 0 := by
  rw [measureReal_eq_zero_iff]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [p.iid_ae_even N] with d hd
  intro heq
  apply hj
  have heven : Even (∑ i, d i : ℕ) := Finset.even_sum d (fun i _ => hd i)
  have hcast : Even ((∑ i, d i : ℕ) : ℤ) := by exact_mod_cast heven
  have hs : (N : ℤ) + j = (∑ i, d i : ℕ) := by
    rw [totalStep_eq_sum_sub] at heq
    omega
  rwa [hs]


theorem CriticalEvenOffspring.iid_site_uniform_bound (p : CriticalEvenOffspring) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (j : ℤ),
      Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} ≤ C := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  have hs := p.sigma_pos
  refine ⟨Real.sqrt (Real.pi / c) / (p.sigma * Real.pi), by positivity, ?_⟩
  intro n j
  by_cases hj : Even (((n+1 : ℕ) : ℤ) + j)
  · have hnorm : ‖∫ t : ℝ, p.siteFourier n j t‖ ≤ Real.sqrt (Real.pi / c) := by
      have hbound : ∀ᵐ t ∂volume, ‖p.siteFourier n j t‖ ≤ Real.exp (-c*t^2) := by
        apply ae_of_all
        intro t
        simpa only [siteFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
          p.cutoff_gaussian_bound hg n t
      simpa only [integral_gaussian] using
        norm_integral_le_of_norm_le (integrable_exp_neg_mul_sq hc) hbound
    rw [p.siteFourier_probability n j hj, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)] at hnorm
    rw [le_div_iff₀ (mul_pos p.sigma_pos Real.pi_pos)]
    nlinarith
  · rw [p.iid_site_incompatible _ _ hj, mul_zero]
    positivity


lemma totalStep_succAbove {N : ℕ} (d : Fin (N+1) → ℕ) (i : Fin (N+1)) :
    totalStep d = (d i : ℤ) - 1 + totalStep (fun j => d (i.succAbove j)) := by
  exact Fin.sum_univ_succAbove (fun j => ((d j : ℤ) - 1)) i


lemma CriticalEvenOffspring.iid_coordinate_site (p : CriticalEvenOffspring)
    (N : ℕ) (i : Fin (N+1)) (k : ℕ) (j : ℤ) :
    (p.iidLaw (N+1)).real {d | d i = k ∧ totalStep d = j} =
      p.mass k * (p.iidLaw N).real {d | totalStep d = j - ((k : ℤ) - 1)} := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℕ) i
  have hp : MeasurePreserving e (p.iidLaw (N+1)) (p.law.toMeasure.prod (p.iidLaw N)) :=
    measurePreserving_piFinSuccAbove (fun _ => p.law.toMeasure) i
  have hset : {d : Fin (N+1) → ℕ | d i = k ∧ totalStep d = j} =
      e ⁻¹' (({k} : Set ℕ) ×ˢ {d : Fin N → ℕ | totalStep d = j - ((k : ℤ) - 1)}) := by
    ext d
    change (d i = k ∧ totalStep d = j) ↔
      (d i = k ∧ totalStep (fun a => d (i.succAbove a)) = j - ((k : ℤ) - 1))
    rw [totalStep_succAbove d i]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> refine ⟨h₁, ?_⟩ <;>
      rw [h₁] at * <;> omega
  rw [measureReal_def, hset, hp.measure_preimage (by measurability),
    Measure.prod_prod, ENNReal.toReal_mul, p.law_singleton,
    ENNReal.toReal_ofReal (p.nonneg _)]
  rfl


lemma CriticalEvenOffspring.law_real_set (p : CriticalEvenOffspring) (s : Set ℕ) :
    p.law.toMeasure.real s = ∑' k, s.indicator p.mass k := by
  classical
  rw [measureReal_def, p.law.toMeasure_apply (Set.to_countable s).measurableSet,
    ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro k
    by_cases hk : k ∈ s <;> simp [hk, p.nonneg]
  · intro k
    by_cases hk : k ∈ s <;> simp [hk]


lemma real_measure_coordinate_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℕ) (hf : Measurable f)
    (s : Set Ω) (hs : MeasurableSet s) :
    μ.real s = ∑' k : ℕ, μ.real {ω | f ω = k ∧ ω ∈ s} := by
  have hu : s = ⋃ k : ℕ, {ω | f ω = k ∧ ω ∈ s} := by ext ω; simp
  have hd : Pairwise (fun k l : ℕ => Disjoint {ω | f ω = k ∧ ω ∈ s}
      {ω | f ω = l ∧ ω ∈ s}) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro ω hω hω'
    exact hkl (hω.1.symm.trans hω'.1)
  conv_lhs => rw [measureReal_def, hu,
    measure_iUnion hd (fun k => (hf (measurableSet_singleton k)).inter hs),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  rfl


lemma CriticalEvenOffspring.iid_coordinate_tail_sum (p : CriticalEvenOffspring)
    (N : ℕ) (i : Fin (N+1)) (R : ℝ) (j : ℤ) :
    (p.iidLaw (N+1)).real {d | R < (d i : ℝ) ∧ totalStep d = j} =
      ∑' k : ℕ, if R < (k : ℝ) then p.mass k *
        (p.iidLaw N).real {d | totalStep d = j - ((k : ℤ) - 1)} else 0 := by
  rw [real_measure_coordinate_decomposition _ (fun d => d i) (measurable_pi_apply i) _
    (by measurability)]
  simp only [Set.mem_ofPred_eq]
  apply tsum_congr
  intro k
  by_cases hk : R < (k : ℝ)
  · rw [ite_eq_left hk]
    have hs : {d : Fin (N+1) → ℕ | d i = k ∧ R < (d i : ℝ) ∧ totalStep d = j} =
        {d | d i = k ∧ totalStep d = j} := by
      ext d
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₁.symm ▸ hk, h₂⟩
    rw [hs, p.iid_coordinate_site]
  · rw [ite_eq_right hk]
    have hs : {d : Fin (N+1) → ℕ | d i = k ∧ R < (d i : ℝ) ∧ totalStep d = j} = ∅ := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h₁ h₂ _
      exact hk (h₁ ▸ h₂)
    rw [hs, measureReal_empty]


lemma CriticalEvenOffspring.iid_coordinate_tail_bound (p : CriticalEvenOffspring)
    {C : ℝ} (hC : ∀ (n : ℕ) (j : ℤ),
      Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} ≤ C)
    (n : ℕ) (i : Fin (n+2)) (R : ℝ) (j : ℤ) :
    Real.sqrt (n+1) * (p.iidLaw (n+2)).real
        {d | R < (d i : ℝ) ∧ totalStep d = j} ≤
      C * p.law.toMeasure.real {k | R < (k : ℝ)} := by
  rw [p.iid_coordinate_tail_sum (n+1) i R j, p.law_real_set, ← tsum_mul_left, ← tsum_mul_left]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hmass : Summable (fun k : ℕ => if R < (k : ℝ) then p.mass k else 0) :=
    p.total.summable.of_nonneg_of_le
      (fun k => by split_ifs <;> simp [p.nonneg])
      (fun k => by split_ifs <;> simp [p.nonneg])
  have hm : Summable (fun k : ℕ => if R < (k : ℝ) then p.mass k *
      (p.iidLaw (n+1)).real {d | totalStep d = j - ((k : ℤ) - 1)} else 0) := by
    apply p.total.summable.of_nonneg_of_le
    · intro k
      split_ifs
      · exact mul_nonneg (p.nonneg _) measureReal_nonneg
      · rfl
    · intro k
      split_ifs
      · exact mul_le_of_le_one_right (p.nonneg _) measureReal_le_one
      · exact p.nonneg _
  apply Summable.tsum_le_tsum _ (hm.mul_left _) (hmass.mul_left _)
  intro k
  split_ifs
  · have h := mul_le_mul_of_nonneg_left (hC n (j - ((k : ℤ) - 1))) (p.nonneg k)
    nlinarith
  · simp


lemma CriticalEvenOffspring.iid_max_tail_bound (p : CriticalEvenOffspring)
    {C : ℝ} (hC : ∀ (n : ℕ) (j : ℤ),
      Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} ≤ C)
    (n : ℕ) (R : ℝ) (j : ℤ) :
    Real.sqrt (n+1) * (p.iidLaw (n+2)).real
        {d | (∃ i, R < (d i : ℝ)) ∧ totalStep d = j} ≤
      (n+2 : ℝ) * C * p.law.toMeasure.real {k | R < (k : ℝ)} := by
  have hu : {d : Fin (n+2) → ℕ | (∃ i, R < (d i : ℝ)) ∧ totalStep d = j} =
      ⋃ i : Fin (n+2), {d | R < (d i : ℝ) ∧ totalStep d = j} := by
    ext d
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    aesop
  rw [hu]
  calc
    _ ≤ Real.sqrt (n+1) * ∑ i : Fin (n+2), (p.iidLaw (n+2)).real
        {d | R < (d i : ℝ) ∧ totalStep d = j} :=
      mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le _) (Real.sqrt_nonneg _)
    _ ≤ ∑ _i : Fin (n+2), C * p.law.toMeasure.real {k | R < (k : ℝ)} := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact p.iid_coordinate_tail_bound hC n i R j
    _ = _ := by simp [Nat.cast_add, Nat.cast_ofNat, mul_assoc]


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BridgeLimit
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

lemma integral_tendsto_of_tendstoInDistribution
    {ι E Ω' : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ∀ i, Measure (Ω i)} {ν : Measure Ω'} [∀ i, IsProbabilityMeasure (μ i)]
    [IsProbabilityMeasure ν] {l : Filter ι} {X : ∀ i, Ω i → E} {Y : Ω' → E}
    (h : TendstoInDistribution X l Y μ ν) {F : E → ℝ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) :
    Tendsto (fun i => ∫ ω, F (X i ω) ∂μ i) l (𝓝 (∫ ω, F (Y ω) ∂ν)) := by
  let f : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hF M hM
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto f
  change Tendsto (fun i => ∫ x, f x ∂(μ i).map (X i)) l
    (𝓝 (∫ x, f x ∂ν.map Y)) at hh
  simp_rw [integral_map (h.forall_aemeasurable _) f.continuous.aestronglyMeasurable,
    integral_map h.aemeasurable_limit f.continuous.aestronglyMeasurable] at hh
  exact hh

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


lemma codePartition_nonneg (p : CriticalEvenOffspring) (N : ℕ) :
    0 ≤ codePartition p N := Finset.sum_nonneg (fun d _ => codeWeight_nonneg p d)


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


lemma measurable_ladderTail : Measurable ladderTail := by
  apply Measurable.of_eval
  intro k
  have hs : Measurable (fun x : ℕ → ℕ => (x,ladderIndex x+1+k)) :=
    measurable_id.prodMk ((measurable_ladderIndex.add_const 1).add_const k)
  have he : Measurable (fun z : (ℕ → ℕ)×ℕ => z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_pi_apply n
  exact he.comp hs


lemma ladderOvershoot_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderOvershoot x=k := by
  rw [ladderOvershoot,ladderIndex_eq_of_hit h,h.2,Int.toNat_natCast]


lemma ladderTail_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderTail x=streamShift (n+1) x := by
  rw [ladderTail,ladderIndex_eq_of_hit h]


lemma CriticalEvenOffspring.ladder_slice_mass (p : CriticalEvenOffspring)
    (k : ℕ) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw ({x | ladderOvershoot x=k} ∩ ladderTail ⁻¹' F)=
      p.ladderLaw k*p.streamLaw F := by
  have he : ({x | ladderOvershoot x=k} ∩ ladderTail ⁻¹' F : Set (ℕ → ℕ)) =ᵐ[p.streamLaw]
      ⋃ n : ℕ, {x | weakLadderHit x n k} ∩ (streamShift (n+1)) ⁻¹' F := by
    filter_upwards [p.ae_weakLadderHit] with x hx
    apply propext
    obtain ⟨n,l,hh⟩ := hx
    constructor
    · intro hm
      have hl : l=k := (ladderOvershoot_of_hit hh).symm.trans hm.1
      subst l
      exact Set.mem_iUnion.mpr ⟨n,hh,by simpa only [Set.mem_preimage,← ladderTail_of_hit hh] using hm.2⟩
    · intro hm
      obtain ⟨m,hm,hxF⟩ := Set.mem_iUnion.mp hm
      exact ⟨ladderOvershoot_of_hit hm,by simpa only [Set.mem_preimage,ladderTail_of_hit hm] using hxF⟩
  rw [measure_congr he,measure_iUnion]
  · simp_rw [p.prefix_inter_shift (n := _)
      (hE := measurableSet_weakLadderHit _ _) (hF := hF) (htr := weakLadderHit_truncate _ _)]
    rw [ENNReal.tsum_mul_right,p.weakLadder_overshoot_mass]
    rfl
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hn hm
    exact hnm (weakLadderHit_unique hn.1 hm.1).1
  · intro n
    exact (measurableSet_weakLadderHit n k).inter ((measurable_streamShift (n+1)) hF)


lemma countable_slice_rectangle {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (ν : Measure β) (q : PMF ℕ) (Y : Ω → ℕ) (T : Ω → β)
    (hY : Measurable Y) (hT : Measurable T)
    (h : ∀ k E, MeasurableSet E → μ ({x | Y x=k} ∩ T ⁻¹' E)=q k*ν E)
    (A : Set ℕ) (E : Set β) (hA : MeasurableSet A) (hE : MeasurableSet E) :
    μ (Y ⁻¹' A ∩ T ⁻¹' E)=q.toMeasure A*ν E := by
  classical
  have he : Y ⁻¹' A ∩ T ⁻¹' E=⋃ k ∈ A, {x | Y x=k} ∩ T ⁻¹' E := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨Y x,hx.1,rfl,hx.2⟩
    · rintro ⟨k,hk,he,hx⟩
      exact ⟨he.symm ▸ hk,hx⟩
  rw [he,measure_biUnion (Set.to_countable A)]
  · simp_rw [h _ E hE]
    rw [ENNReal.tsum_mul_right]
    congr 1
    rw [tsum_subtype,PMF.toMeasure_apply _ hA]
  · intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro x hk hl
    exact hkl (hk.1.symm.trans hl.1)
  · intro k _
    exact (measurableSet_eq_fun hY measurable_const).inter (hT hE)


lemma CriticalEvenOffspring.ladder_rectangle (p : CriticalEvenOffspring)
    (A : Set ℕ) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw (ladderOvershoot ⁻¹' A ∩ ladderTail ⁻¹' F)=
      p.ladderLaw.toMeasure A*p.streamLaw F :=
  countable_slice_rectangle p.streamLaw p.streamLaw p.ladderLaw ladderOvershoot ladderTail
    measurable_ladderOvershoot measurable_ladderTail p.ladder_slice_mass A F ((Set.to_countable A).measurableSet) hF


lemma CriticalEvenOffspring.ladderTail_preserving (p : CriticalEvenOffspring) :
    MeasurePreserving ladderTail p.streamLaw p.streamLaw := by
  refine ⟨measurable_ladderTail,?_⟩
  apply Measure.ext
  intro F hF
  rw [Measure.map_apply measurable_ladderTail hF]
  simpa using p.ladder_rectangle Set.univ F hF


lemma renewalCount_spec {τ : ℕ → ℕ} (h₀ : τ 0=0) (n : ℕ) :
    τ (renewalCount τ n) ≤ n :=
  Nat.findGreatest_spec (P := fun r => τ r ≤ n) (Nat.zero_le n) (by simp [h₀])


lemma le_renewalCount_iff {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0)
    (r n : ℕ) : r ≤ renewalCount τ n ↔ τ r ≤ n := by
  constructor
  · intro h
    exact (hτ.monotone h).trans (renewalCount_spec h₀ n)
  · intro h
    exact Nat.le_findGreatest ((hτ.le_apply (x := r)).trans h) h


lemma renewalCount_succ_gt {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0)
    (n : ℕ) : n < τ (renewalCount τ n+1) := by
  rw [← not_le,← le_renewalCount_iff hτ h₀]
  omega


lemma renewalCount_mono {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) :
    Monotone (renewalCount τ) := by
  intro m n hmn
  rw [le_renewalCount_iff hτ h₀]
  exact (renewalCount_spec h₀ m).trans hmn


lemma renewalCount_at {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) (r : ℕ) :
    renewalCount τ (τ r)=r := by
  apply le_antisymm
  · exact hτ.le_iff_le.mp (renewalCount_spec h₀ (τ r))
  · exact (le_renewalCount_iff hτ h₀ r (τ r)).mpr le_rfl


lemma LadderEnumeration.le_level {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (k : ℕ) : S k ≤ S (τ (renewalCount τ k)) := by
  have hk := renewalCount_spec h.zero k
  by_cases he : τ (renewalCount τ k)=k
  · rw [he]
  · exact (h.between _ k (lt_of_le_of_ne hk he) (renewalCount_succ_gt h.strictMono h.zero k)).le


lemma LadderEnumeration.maximum {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) {k n : ℕ} (hkn : k ≤ n) :
    S k ≤ S (τ (renewalCount τ n)) :=
  (h.le_level k).trans (h.level_mono (renewalCount_mono h.strictMono h.zero hkn))


lemma LadderEnumeration.record_at {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (r : ℕ) {k : ℕ} (hk : k ≤ τ r) :
    S k ≤ S (τ r) := by
  simpa only [renewalCount_at h.strictMono h.zero] using h.maximum hk


lemma LadderEnumeration.records {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    weakRecords S n=(Finset.Icc 1 (renewalCount τ n)).image τ := by
  classical
  ext k
  rw [mem_weakRecords,Finset.mem_image]
  constructor
  · rintro ⟨hk1,hkn,hrec⟩
    let r := renewalCount τ k
    have hr : τ r=k := by
      by_contra he
      have hlt := lt_of_le_of_ne (renewalCount_spec h.zero k) he
      exact not_lt_of_ge (hrec (τ r) (renewalCount_spec h.zero k))
        (h.between r k hlt (renewalCount_succ_gt h.strictMono h.zero k))
    refine ⟨r,Finset.mem_Icc.mpr ⟨?_,?_⟩,hr⟩
    · by_contra hn
      have : r=0 := by omega
      rw [this,h.zero] at hr
      omega
    · exact (le_renewalCount_iff h.strictMono h.zero r n).mpr (hr ▸ hkn)
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨hr1,hrn⟩ := Finset.mem_Icc.mp hr
    refine ⟨?_,(le_renewalCount_iff h.strictMono h.zero r n).mp hrn,fun j hj => h.record_at r hj⟩
    exact hr1.trans h.strictMono.le_apply


lemma LadderEnumeration.card_records {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    (weakRecords S n).card=renewalCount τ n := by
  classical
  rw [h.records,Finset.card_image_of_injective _ h.strictMono.injective,Nat.card_Icc]
  omega


lemma ladderTime_strictMono (x : ℕ → ℕ) : StrictMono (ladderTime x) := by
  apply strictMono_nat_of_lt_succ
  intro r
  dsimp [ladderTime]
  omega


lemma streamShift_add (a b : ℕ) (x : ℕ → ℕ) :
    streamShift a (streamShift b x)=streamShift (b+a) x := by
  funext k
  change x (b+(a+k))=x ((b+a)+k)
  rw [Nat.add_assoc]


lemma ladderTail_iterate (x : ℕ → ℕ) (r : ℕ) :
    ladderTail^[r] x=streamShift (ladderTime x r) x := by
  induction r with
  | zero =>
    change x=(fun k => x (0+k))
    funext k
    rw [Nat.zero_add]
  | succ r ih =>
    rw [Function.iterate_succ_apply',ladderTail,ih,streamShift_add,ladderTime,ih]


lemma integerSum_shift (x : ℕ → ℕ) (a k : ℕ) :
    integerSum (streamShift a x) k=integerSum x (a+k)-integerSum x a := by
  unfold integerSum streamShift
  rw [Finset.sum_range_add]
  ring


lemma CriticalEvenOffspring.ae_all_ladders (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, HasAllLadders x := by
  rw [show HasAllLadders=(fun x => ∀ r, ∃ n k, weakLadderHit (ladderTail^[r] x) n k) from rfl,
    ae_all_iff]
  intro r
  exact (p.ladderTail_preserving.iterate r).quasiMeasurePreserving.ae p.ae_weakLadderHit


lemma ladderTime_step_level {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    integerSum x (ladderTime x (r+1))-integerSum x (ladderTime x r)=
      (renewalIncrement r x:ℤ) := by
  obtain ⟨n,k,h⟩ := hx r
  have hidx := ladderIndex_eq_of_hit h
  have hval := ladderOvershoot_of_hit h
  change _=(ladderOvershoot (ladderTail^[r] x):ℤ)
  rw [hval,ladderTime,hidx,← integerSum_shift,← ladderTail_iterate]
  exact h.2


lemma ladderTime_between {x : ℕ → ℕ} (hx : HasAllLadders x) (r k : ℕ)
    (hlo : ladderTime x r<k) (hhi : k<ladderTime x (r+1)) :
    integerSum x k < integerSum x (ladderTime x r) := by
  obtain ⟨n,j,h⟩ := hx r
  have hidx := ladderIndex_eq_of_hit h
  have hhi' : k<ladderTime x r+(n+1) := by simpa only [ladderTime,hidx] using hhi
  have hs := h.1 (k-ladderTime x r) (by omega) (by omega)
  rw [ladderTail_iterate,integerSum_shift,Nat.add_sub_of_le hlo.le] at hs
  omega


lemma ladderTime_enumeration {x : ℕ → ℕ} (hx : HasAllLadders x) :
    LadderEnumeration (integerSum x) (ladderTime x) := by
  refine ⟨rfl,ladderTime_strictMono x,?_,ladderTime_between hx⟩
  apply monotone_nat_of_le_succ
  intro r
  have := ladderTime_step_level hx r
  dsimp only [Function.comp_apply]
  omega


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightCoding
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


lemma CriticalEvenOffspring.ae_reverse_ladders (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, ∀ b, HasAllLadders (reverseFirst b x) := by
  rw [ae_all_iff]
  intro b
  exact (reverseFirst_preserving p b).quasiMeasurePreserving.ae p.ae_all_ladders


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


lemma integral_standard_gaussian_complex :
    (∫ t : ℝ, Complex.exp (-(t : ℂ)^2/2)) = (Real.sqrt (2 * Real.pi) : ℂ) := by
  have heq (t : ℝ) : Complex.exp (-(t : ℂ)^2/2) =
      (Real.exp (-(1/2 : ℝ)*t^2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [integral_complex_ofReal, integral_gaussian]
  congr 2
  ring


lemma CriticalEvenOffspring.bridgeFourier_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, p.bridgeFourier n t) atTop
      (𝓝 (Real.sqrt (2 * Real.pi) : ℂ)) := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  have hden : Tendsto (fun n : ℕ => p.sigma * Real.sqrt (n+1)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).const_mul_atTop
        p.sigma_pos
  have hp (t : ℝ) : Tendsto (fun n => p.bridgeFourier n t) atTop
      (𝓝 (Complex.exp (-(t : ℂ)^2/2))) := by
    have hr : Tendsto (fun n : ℕ => t / (p.sigma * Real.sqrt (n+1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have he := ((Complex.continuous_ofReal.tendsto 0).comp hr).mul_const Complex.I
    have hex := Complex.continuous_exp.tendsto 0 |>.comp (by simpa using he)
    simpa [bridgeFourier] using (p.cutoff_pointwise t).mul hex
  have hm (n : ℕ) : AEStronglyMeasurable (p.bridgeFourier n) volume := by
    exact ((p.cutoff_measurable n).mul (by fun_prop)).aestronglyMeasurable
  have hn (n : ℕ) : ∀ᵐ t ∂volume, ‖p.bridgeFourier n t‖ ≤ Real.exp (-c*t^2) := by
    apply ae_of_all
    intro t
    simpa only [bridgeFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
      p.cutoff_gaussian_bound hg n t
  have hi := tendsto_integral_of_dominated_convergence (μ := volume)
    (fun t : ℝ => Real.exp (-c*t^2)) hm (integrable_exp_neg_mul_sq hc) hn
      (ae_of_all _ hp)
  simpa only [integral_standard_gaussian_complex] using hi


lemma CriticalEvenOffspring.bridgeFourier_integral (p : CriticalEvenOffspring) (n : ℕ) :
    (∫ t : ℝ, p.bridgeFourier n t) =
      (p.sigma * Real.sqrt (n+1)) •
        ∫ t : ℝ in -(Real.pi/2)..Real.pi/2,
          Complex.exp ((t : ℂ) * Complex.I) *
            (charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t))^(n+1) := by
  let A := (p.sigma * Real.pi / 2) * Real.sqrt (n+1)
  let scale := p.sigma * Real.sqrt (n+1)
  let f : ℝ → ℂ := fun t =>
    (charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1)))^(n+1) *
      Complex.exp ((t / scale : ℝ) * Complex.I)
  have hsqrt : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hscale : 0 < scale := mul_pos p.sigma_pos hsqrt
  have hA : 0 ≤ A := mul_nonneg
    (div_nonneg (mul_nonneg p.sigma_pos.le Real.pi_pos.le) (by norm_num)) hsqrt.le
  have heq : p.bridgeFourier n = (Icc (-A) A).indicator f := by
    ext t
    simp only [bridgeFourier, fourierCutoff, Set.indicator_apply, mem_Icc, ← abs_le]
    split_ifs <;> simp [f, scale]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self hA)]
  have hlo : -(Real.pi/2) * scale = -A := by dsimp [scale, A]; ring
  have hhi : (Real.pi/2) * scale = A := by dsimp [scale, A]; ring
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (a := -(Real.pi/2)) (b := Real.pi/2) f scale
  rw [hlo, hhi] at hsub
  rw [← hsub]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [f]
  rw [mul_div_cancel_right₀ _ hscale.ne']
  have ht : t * scale / Real.sqrt (n+1) = p.sigma * t := by
    dsimp [scale]
    field_simp
  rw [ht, mul_comm]


lemma CriticalEvenOffspring.bridgeFourier_partition (p : CriticalEvenOffspring) (n : ℕ) :
    (∫ t : ℝ, p.bridgeFourier (2*n) t) =
      (p.sigma * Real.sqrt (2*n+1) * Real.pi * bridgePartition p (2*n+1) : ℝ) := by
  have hpar : Even (((2*n+1 : ℕ) : ℤ) + (-1)) := by
    refine ⟨n, ?_⟩
    push_cast
    ring
  have hi := spanTwo_inversion (p.iidLaw (2*n+1)) totalStep
    (totalStep_measurable _) (-1) (p.iid_totalStep_parity _ hpar)
  simp only [Int.cast_neg, Int.cast_one, neg_neg, one_mul, p.iid_charFun] at hi
  rw [p.bridgeFourier_integral, hi, ← p.bridgePartition_eq_iid]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  push_cast
  ring


lemma CriticalEvenOffspring.bridgePartition_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => Real.sqrt (2*n+1) * bridgePartition p (2*n+1)) atTop
      (𝓝 (Real.sqrt (2*Real.pi) / (p.sigma * Real.pi))) := by
  have hsub : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (p.bridgeFourier_limit.comp hsub)
  change Tendsto (fun n : ℕ => (∫ t : ℝ, p.bridgeFourier (2*n) t).re)
    atTop (𝓝 (Real.sqrt (2*Real.pi))) at h
  simp only [p.bridgeFourier_partition, Complex.ofReal_re] at h
  have hdiv := h.div_const (p.sigma * Real.pi)
  convert hdiv using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  have hs := p.sigma_pos.ne'
  have hpi := Real.pi_pos.ne'
  field_simp


theorem CriticalEvenOffspring.codePartition_asymptotic (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => (2*n+1 : ℝ) * Real.sqrt (2*n+1) *
      codePartition p (2*n+1)) atTop (𝓝 (2 / (p.sigma * Real.sqrt (2*Real.pi)))) := by
  have hc : Real.sqrt (2*Real.pi) / (p.sigma * Real.pi) =
      2 / (p.sigma * Real.sqrt (2*Real.pi)) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    have hsp : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
    field_simp [p.sigma_pos.ne', Real.pi_pos.ne', hsp.ne']
    nlinarith
  rw [← hc]
  convert p.bridgePartition_limit using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [codePartition_cyclic p (by omega)]
  push_cast
  ring


lemma CriticalEvenOffspring.squareTail_tendsto (p : CriticalEvenOffspring) :
    Tendsto p.squareTail atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence p.second
    (f := fun R : ℝ => fun k : ℕ => if R < (k : ℝ) then (k : ℝ)^2 * p.mass k else 0)
    (g := fun _ => (0 : ℝ)) (𝓕 := atTop) ?_ ?_
  · change Tendsto (fun R : ℝ => ∑' k : ℕ,
      if R < (k : ℝ) then (k : ℝ)^2 * p.mass k else 0) atTop (𝓝 0)
    simpa only [tsum_apply, tsum_zero] using h
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (k : ℝ)] with R hR
    simp [not_lt.mpr hR]
  · apply Eventually.of_forall
    intro R k
    split_ifs
    · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (p.nonneg k))]
    · simp [mul_nonneg (sq_nonneg _) (p.nonneg k)]


lemma CriticalEvenOffspring.squareTail_bound (p : CriticalEvenOffspring)
    (R : ℝ) (hR : 0 ≤ R) :
    R^2 * p.law.toMeasure.real {k | R < (k : ℝ)} ≤ p.squareTail R := by
  rw [p.law_real_set, ← tsum_mul_left]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hs : Summable (fun k : ℕ => if R < (k : ℝ) then p.mass k else 0) :=
    p.total.summable.of_nonneg_of_le
      (fun k => by split_ifs <;> simp [p.nonneg])
      (fun k => by split_ifs <;> simp [p.nonneg])
  have hs₂ : Summable (fun k : ℕ => if R < (k : ℝ) then (k : ℝ)^2 * p.mass k else 0) :=
    p.second.of_nonneg_of_le
      (fun k => by split_ifs <;> simp [mul_nonneg (sq_nonneg _) (p.nonneg k)])
      (fun k => by split_ifs <;> simp [mul_nonneg (sq_nonneg _) (p.nonneg k)])
  apply Summable.tsum_le_tsum _ (hs.mul_left _) hs₂
  intro k
  split_ifs with hk
  · exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hR (Nat.cast_nonneg k)).mpr hk.le) (p.nonneg k)
  · simp


theorem CriticalEvenOffspring.sqrt_tail_small (p : CriticalEvenOffspring)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n+1 : ℝ) *
      p.law.toMeasure.real {k | ε * Real.sqrt (n+1) < (k : ℝ)}) atTop (𝓝 0) := by
  have hR : Tendsto (fun n : ℕ => ε * Real.sqrt (n+1)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).const_mul_atTop hε
  have hlim := (p.squareTail_tendsto.comp hR).div_const (ε^2)
  simp only [zero_div] at hlim
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  rw [le_div_iff₀ (sq_pos_of_pos hε)]
  have h := p.squareTail_bound (ε * Real.sqrt (n+1)) (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h
  dsimp only [Function.comp_apply] at *
  nlinarith


theorem codeEventMass_cyclic (p : CriticalEvenOffspring) {N : ℕ} [NeZero N]
    (E : (Fin N → Fin N) → Prop)
    (hE : ∀ (m : Fin N) d, E (rotateDegrees m d) ↔ E d) :
    bridgeEventMass p N E = (N : ℝ) * codeEventMass p N E := by
  classical
  have h := weighted_unique_rotation (rotateBridge (N := N))
    (fun d => if E d.val then bridgeWeight p d else 0)
    (fun d => IsTreeCode d.val)
    (fun m d => by
      change (if E (rotateDegrees m d.val) then bridgeWeight p (rotateBridge m d) else 0) = _
      rw [hE, bridgeWeight_rotate])
    (fun d => d.unique_good_rotation)
  rw [Fintype.card_fin] at h
  change (∑ d : Bridge N, if E d.val then bridgeWeight p d else 0) = _
  rw [h]
  congr 1
  rw [← Finset.sum_filter]
  unfold codeEventMass
  rw [Finset.sum_subtype (p := fun d : Bridge N => IsTreeCode d.val) _ (by simp)]
  let e : Code N ≃ {d : Bridge N // IsTreeCode d.val} := {
    toFun := fun d => ⟨⟨d.val, d.property.1⟩, d.property⟩
    invFun := fun d => ⟨d.val.val, d.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Equiv.sum_comp e (fun d => if E d.val.val then bridgeWeight p d.val else 0)).symm


lemma CriticalEvenOffspring.bridgeEventMass_eq_iid (p : CriticalEvenOffspring)
    (N : ℕ) (E : (Fin N → ℕ) → Prop) :
    bridgeEventMass p N (fun d => E (fun i => (d i).val)) =
      (p.iidLaw N).real {d | totalStep d = -1 ∧ E d} := by
  classical
  let s : Bridge N → Set (Fin N → ℕ) := fun b =>
    if E (bridgeEmbedding N b) then {bridgeEmbedding N b} else ∅
  have hset : {d : Fin N → ℕ | totalStep d = -1 ∧ E d} = ⋃ b, s b := by
    ext d
    constructor
    · rintro ⟨h₁, h₂⟩
      have hr : d ∈ Set.range (bridgeEmbedding N) := by
        rw [← totalStep_bridge_range]
        exact h₁
      obtain ⟨b, rfl⟩ := hr
      exact mem_iUnion.mpr ⟨b, by simp [s, h₂]⟩
    · intro hd
      obtain ⟨b, hb⟩ := mem_iUnion.mp hd
      dsimp [s] at hb
      split_ifs at hb with hE
      · have heq : d = bridgeEmbedding N b := hb
        exact ⟨heq ▸ totalStep_bridge b, heq ▸ hE⟩
      · exact hb.elim
  have hd : Pairwise (fun b c => Disjoint (s b) (s c)) := by
    intro b c hbc
    dsimp [s]
    split_ifs
    · exact Set.disjoint_singleton.mpr ((bridgeEmbedding N).injective.ne hbc)
    all_goals simp
  have hm (b : Bridge N) : MeasurableSet (s b) := by dsimp [s]; split_ifs <;> measurability
  rw [hset, measureReal_iUnion_fintype hd hm]
  unfold bridgeEventMass
  apply Finset.sum_congr rfl
  intro b _
  change (if E (bridgeEmbedding N b) then bridgeWeight p b else 0) = _
  dsimp [s]
  split_ifs
  · exact (p.iid_bridge_singleton b).symm
  · simp


lemma codeEventProbability_eq_bridge (p : CriticalEvenOffspring) {N : ℕ} (hN : 0 < N)
    (E : (Fin N → Fin N) → Prop)
    (hE : letI : NeZero N := ⟨hN.ne'⟩
      ∀ (m : Fin N) d, E (rotateDegrees m d) ↔ E d) :
    codeEventProbability p N E = bridgeEventMass p N E / bridgePartition p N := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [codeEventMass_cyclic p E hE, codePartition_cyclic p hN, mul_div_mul_left]
  · rfl
  · exact_mod_cast hN.ne'


lemma maxDegree_rotation {N : ℕ} [NeZero N] (R : ℝ) (m : Fin N)
    (d : Fin N → Fin N) :
    (∃ i, R < ((rotateDegrees m d i).val : ℝ)) ↔ ∃ i, R < ((d i).val : ℝ) := by
  change (∃ i, R < ((d (i+m)).val : ℝ)) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i+m, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i-m, by simpa using hi⟩


lemma code_max_probability_eq_iid (p : CriticalEvenOffspring) {N : ℕ} (hN : 0 < N)
    (R : ℝ) :
    codeEventProbability p N (fun d => ∃ i, R < ((d i).val : ℝ)) =
      (p.iidLaw N).real {d | (∃ i, R < (d i : ℝ)) ∧ totalStep d = -1} /
        (p.iidLaw N).real {d | totalStep d = -1} := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [codeEventProbability_eq_bridge p hN _ (by
    intro m d
    exact maxDegree_rotation R m d), p.bridgePartition_eq_iid,
    p.bridgeEventMass_eq_iid N (fun d => ∃ i, R < (d i : ℝ))]
  congr 2
  ext d
  exact and_comm


theorem CriticalEvenOffspring.conditioned_max_degree (p : CriticalEvenOffspring)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => codeEventProbability p (2*n+1)
      (fun d => ∃ i, ε * Real.sqrt (2*n+1) < ((d i).val : ℝ))) atTop (𝓝 0) := by
  obtain ⟨C, hCpos, hC⟩ := p.iid_site_uniform_bound
  have hsub : Tendsto (fun n : ℕ => 2*n+2) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have htail := (p.sqrt_tail_small ε hε).comp hsub
  have hnum : Tendsto (fun n : ℕ => Real.sqrt (2*n+3) *
      (p.iidLaw (2*n+3)).real
        {d | (∃ i, ε * Real.sqrt (2*n+3) < (d i : ℝ)) ∧ totalStep d = -1})
      atTop (𝓝 0) := by
    have hupper := htail.const_mul (2*C)
    simp only [mul_zero] at hupper
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      add_assoc, show (2:ℝ)+1=3 by norm_num] at hupper
    apply squeeze_zero (fun n => by positivity) (fun n => ?_) hupper
    have hb := p.iid_max_tail_bound hC (2*n+1) (ε * Real.sqrt (2*n+3)) (-1)
    have hs : Real.sqrt (2*n+3) ≤ 2 * Real.sqrt (2*n+2) := by
      have h₁ := Real.sq_sqrt (show 0 ≤ (2*n+3 : ℝ) by positivity)
      have h₂ := Real.sq_sqrt (show 0 ≤ (2*n+2 : ℝ) by positivity)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith [Real.sqrt_nonneg (2*n+3), Real.sqrt_nonneg (2*n+2)]
    have hh := mul_le_mul_of_nonneg_right hs
      (show 0 ≤ (p.iidLaw (2*n+3)).real
        {d | (∃ i, ε * Real.sqrt (2*n+3) < (d i : ℝ)) ∧ totalStep d = -1} from
          measureReal_nonneg)
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] at hb
    nlinarith
  have hden := p.bridgePartition_limit.comp (tendsto_add_atTop_nat 1)
  have hden' : Tendsto (fun n : ℕ => Real.sqrt (2*n+3) *
      (p.iidLaw (2*n+3)).real {d | totalStep d = -1}) atTop
      (𝓝 (Real.sqrt (2*Real.pi) / (p.sigma * Real.pi))) := by
    convert hden using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    dsimp only [Function.comp_apply]
    rw [p.bridgePartition_eq_iid]
    congr 2; push_cast; ring
  have hB : Real.sqrt (2*Real.pi) / (p.sigma * Real.pi) ≠ 0 := by
    exact ne_of_gt (div_pos (Real.sqrt_pos.mpr (by positivity))
      (mul_pos p.sigma_pos Real.pi_pos))
  have hratio := hnum.div hden' hB
  simp only [zero_div] at hratio
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert hratio using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  dsimp only [Pi.div_apply]
  rw [code_max_probability_eq_iid p (by omega), mul_div_mul_left]
  · congr 2; push_cast; ring_nf; rfl
  · exact (Real.sqrt_pos.mpr (by positivity)).ne'


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

lemma measurable_streamPrefix (N : ℕ) : Measurable (streamPrefix N) :=
  Measurable.of_eval (fun index => measurable_pi_apply index.val)

lemma CriticalEvenOffspring.streamPrefix_hasLaw (p : CriticalEvenOffspring) (N : ℕ) :
    HasLaw (streamPrefix N) (p.iidLaw N) p.streamLaw := p.stream_restrict_law N

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma odd_size_tendsto : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
  tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id

lemma odd_sqrt_tendsto : Tendsto (fun n : ℕ => Real.sqrt ((2*n+1:ℕ):ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp odd_size_tendsto)

end FKCRT.TreeCoding
end


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

lemma CriticalEvenOffspring.code_probability_le_stream (p : CriticalEvenOffspring) (n : ℕ)
    (E : Set (Code (2*n+1))) (A : Set (ℕ → ℕ))
    (hEA : ∀ d ∈ E, ∀ x, streamPrefix (2*n+1) x=codeEmbedding (2*n+1) d → x∈A) :
    (p.codeLaw n).real E ≤ p.streamLaw.real A / codePartition p (2*n+1) := by
  classical
  let N := 2*n+1
  let C : Code N → Set (ℕ → ℕ) := fun d => if d∈E then
    streamPrefix N ⁻¹' {codeEmbedding N d} else ∅
  have hm (d) : MeasurableSet (C d) := by
    dsimp [C]
    split_ifs
    · exact (measurableSet_singleton _).preimage (measurable_streamPrefix N)
    · exact MeasurableSet.empty
  have hd : Pairwise (fun d e => Disjoint (C d) (C e)) := by
    intro d e hde
    dsimp [C]
    split_ifs <;> try simp
    exact (Set.disjoint_singleton.mpr ((codeEmbedding N).injective.ne hde)).preimage _
  have he (d : Code N) : p.streamLaw.real (C d) = if d∈E then codeWeight p d else 0 := by
    dsimp [C]
    split_ifs
    · rw [(p.streamPrefix_hasLaw N).measurePreserving (measurable_streamPrefix N) |>.measureReal_preimage
        (measurableSet_singleton _).nullMeasurableSet]
      exact p.iid_bridge_singleton ⟨d.val,d.property.1⟩
    · simp
  have hb : (∑ d : Code N, if d∈E then codeWeight p d else 0) ≤ p.streamLaw.real A := by
    rw [← show p.streamLaw.real (⋃ d, C d)=∑ d : Code N, if d∈E then codeWeight p d else 0 by
      rw [measureReal_iUnion_fintype hd hm]; simp only [he]]
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    rintro x ⟨_,⟨d,rfl⟩,hx⟩
    dsimp [C] at hx
    split_ifs at hx with hE
    · exact hEA d hE x hx
    · exact hx.elim
  rw [← integral_indicator_one (μ := p.codeLaw n) (show MeasurableSet E from trivial),p.code_integral]
  apply (le_div_iff₀ (codePartition_odd_pos p n)).mpr
  have heq : (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
      E.indicator (fun _ => (1:ℝ)) d)*codePartition p (2*n+1)=
      ∑ d : Code (2*n+1), if d∈E then codeWeight p d else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [Set.indicator]
    split_ifs
    · field_simp [(codePartition_odd_pos p n).ne']
    · simp
  change (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
    E.indicator (fun _ => (1:ℝ)) d)*codePartition p (2*n+1) ≤ _
  rw [heq]
  exact hb

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


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- Converging together with varying sample spaces and actual probability laws. -/
theorem tendstoInDistribution_of_close {E Ω' : Type*} {Ω : ℕ → Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n, Measure (Ω n)} {ν : Measure Ω'} [∀ n, IsProbabilityMeasure (μ n)]
    [IsProbabilityMeasure ν] {X Y : ∀ n, Ω n → E} {Z : Ω' → E}
    (hXZ : TendstoInDistribution X atTop Z μ ν)
    (hY : ∀ n, AEMeasurable (Y n) (μ n))
    (hclose : ∀ ε>0, Tendsto (fun n => (μ n).real {ω | ε < dist (X n ω) (Y n ω)}) atTop (𝓝 0)) :
    TendstoInDistribution Y atTop Z μ ν := by
  refine ⟨hY,hXZ.aemeasurable_limit,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  have hZ := hXZ.aemeasurable_limit
  have hmid := tendsto_iff_forall_lipschitz_integral_tendsto.mp hXZ.tendsto F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ x,F x ∂(μ n).map (Y n)) atTop (𝓝 (∫ x,F x ∂ν.map Z))
  change Tendsto (fun n => ∫ x,F x ∂(μ n).map (X n)) atTop (𝓝 (∫ x,F x ∂ν.map Z)) at hmid
  simp_rw [integral_map (hY _) hL.continuous.aestronglyMeasurable,
    integral_map hZ hL.continuous.aestronglyMeasurable]
  simp_rw [integral_map (hXZ.forall_aemeasurable _) hL.continuous.aestronglyMeasurable,
    integral_map hZ hL.continuous.aestronglyMeasurable] at hmid
  have hM0 : 0≤M := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure ν
    simpa using hM (Z ω) (Z ω)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(4*((L:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hLd : (L:ℝ)*δ ≤ ε/4 := by
    dsimp [δ]; rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0<4*((L:ℝ)+1))]
    nlinarith [L.coe_nonneg]
  have htail := (hclose (δ/2) (half_pos hδ)).const_mul M
  simp only [mul_zero] at htail
  filter_upwards [htail.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/4)),
    (Metric.tendsto_nhds.mp hmid) (ε/4) (by positivity)] with n hn hnmid
  have he := integral_lipschitz_approx_bound (hY n) (hXZ.forall_aemeasurable n) hM hL hδ.le
  have hs : (μ n).real {ω | δ ≤ dist (Y n ω) (X n ω)} ≤
      (μ n).real {ω | δ/2 < dist (X n ω) (Y n ω)} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change δ ≤ dist (Y n ω) (X n ω) at hω
    change δ/2 < dist (X n ω) (Y n ω)
    rw [dist_comm] at hω
    exact lt_of_lt_of_le (by linarith) hω
  have hh := mul_le_mul_of_nonneg_left hs hM0
  have ht := abs_sub_le (∫ ω,F (Y n ω) ∂μ n) (∫ ω,F (X n ω) ∂μ n) (∫ ω,F (Z ω) ∂ν)
  rw [Real.dist_eq] at hnmid ⊢
  linarith

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionGeometry
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
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma continuous_standardExcursion {Ω : Type} {B : Fin 3 → ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hB : ∀ i,Continuous (B i · ω)) : Continuous (standardExcursion B ω) := by
  unfold standardExcursion
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro i _
  apply Continuous.pow
  apply Continuous.sub
  · exact (hB i).comp (continuous_subtype_val.subtype_mk _)
  · exact continuous_subtype_val.mul continuous_const

lemma standardExcursion_ae_continuous {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P,Continuous (standardExcursion B ω) := by
  filter_upwards [ae_all_iff.mpr (fun i => (hB i).cont)] with ω hω
  exact continuous_standardExcursion hω

lemma excursionPath_ae_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P,(excursionPath B ω : unitInterval → ℝ)=standardExcursion B ω := by
  filter_upwards [standardExcursion_ae_continuous hB] with ω hω
  funext t
  exact ContinuousMap.mkD_apply_of_continuous hω

end FKCRT.TreeCoding
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

lemma CriticalEvenOffspring.ladderType_rectangle (p : CriticalEvenOffspring)
    (A : Set (ℕ×ℕ)) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw (ladderType ⁻¹' A ∩ ladderTail ⁻¹' F)=p.spineLaw A*p.streamLaw F := by
  classical
  have he : ladderType ⁻¹' A ∩ ladderTail ⁻¹' F=
      ⋃ z ∈ A,{x | ladderType x=z} ∩ ladderTail ⁻¹' F := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨ladderType x,hx.1,rfl,hx.2⟩
    · rintro ⟨z,hz,he,hx⟩
      exact ⟨he.symm ▸ hz,hx⟩
  rw [he,measure_biUnion (Set.to_countable A)]
  · simp_rw [p.ladderType_slice _ _ F hF,ENNReal.tsum_mul_right]
    congr 1
    simp_rw [← p.spineLaw_singleton]
    exact tsum_measure_preimage_singleton (Set.to_countable A) (fun _ _ => measurableSet_singleton _)
  · intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro x hk hl
    exact hkl (hk.1.symm.trans hl.1)
  · intro k _
    exact (measurableSet_eq_fun measurable_ladderType measurable_const).inter (measurable_ladderTail hF)

lemma CriticalEvenOffspring.ladderType_indep_tail (p : CriticalEvenOffspring) :
    IndepFun ladderType ladderTail p.streamLaw := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A F hA hF
  rw [p.ladderTail_preserving.measure_preimage hF.nullMeasurableSet]
  rw [← Measure.map_apply measurable_ladderType hA]
  exact p.ladderType_rectangle A F hF

lemma CriticalEvenOffspring.ladderTypes_iid (p : CriticalEvenOffspring) :
    iIndepFun (fun i x => ladderType (ladderTail^[i] x)) p.streamLaw :=
  regenerative_iIndepFun p.streamLaw ladderType ladderTail measurable_ladderType
    p.ladderTail_preserving p.ladderType_indep_tail

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

lemma CriticalEvenOffspring.spine_integral_fst (p : CriticalEvenOffspring) :
    (∫ z : ℕ×ℕ,(z.1:ℝ) ∂p.spineLaw)=p.variance+1 := by
  calc
    _ = (∫⁻ z : ℕ×ℕ, ENNReal.ofReal (z.1:ℝ) ∂p.spineLaw).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun z => Nat.cast_nonneg z.1))
        (measurable_of_countable _).aestronglyMeasurable
    _ = _ := by
      simp only [ENNReal.ofReal_natCast]
      rw [p.spine_lintegral_fst,ENNReal.toReal_ofReal (by linarith [p.variance_pos])]

lemma CriticalEvenOffspring.ladderType_hasLaw (p : CriticalEvenOffspring) :
    HasLaw ladderType p.spineLaw p.streamLaw :=
  ⟨measurable_ladderType.aemeasurable,rfl⟩

lemma CriticalEvenOffspring.ladderTypes_hasLaw (p : CriticalEvenOffspring) (i : ℕ) :
    HasLaw (fun x => ladderType (ladderTail^[i] x)) p.spineLaw p.streamLaw := by
  exact p.ladderType_hasLaw.comp (p.ladderTail_preserving.iterate i).hasLaw

/-- A genuinely sampled spine's bounded labels satisfy a two-sided Hoeffding bound.
The label mean is the exact p(k)-per-child-slot spine expectation. -/
lemma CriticalEvenOffspring.spine_label_deviation (p : CriticalEvenOffspring)
    (b : ℕ×ℕ → ℝ) (a d : ℝ) (hb : ∀ z,b z∈Set.Icc a d)
    (h : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    p.streamLaw.real {x | r≤|∑ i ∈ Finset.range h,
      (b (ladderType (ladderTail^[i] x)) - ∫ z,b z ∂p.spineLaw)|} ≤
      2*Real.exp (-r^2/(2*h*((d-a)/2)^2)) := by
  let Y : ℕ → (ℕ → ℕ) → ℝ := fun i x =>
    b (ladderType (ladderTail^[i] x)) - ∫ z,b z ∂p.spineLaw
  have hi : iIndepFun Y p.streamLaw := p.ladderTypes_iid.comp
    (fun _ z => b z - ∫ z,b z ∂p.spineLaw) (fun _ => measurable_of_countable _)
  have hg : ∀ i,HasSubgaussianMGF (Y i) ((‖d-a‖₊/2)^2) p.streamLaw := by
    intro i
    have hm : Measurable (fun x => b (ladderType (ladderTail^[i] x))) :=
      (measurable_of_countable b).comp (measurable_ladderType.comp (measurable_ladderTail.iterate i))
    have hx := hasSubgaussianMGF_of_mem_Icc (μ := p.streamLaw) hm.aemeasurable
      (Eventually.of_forall (fun x => hb (ladderType (ladderTail^[i] x))))
    have he : (∫ x,b (ladderType (ladderTail^[i] x)) ∂p.streamLaw)=∫ z,b z ∂p.spineLaw :=
      (p.ladderTypes_hasLaw i).integral_comp (measurable_of_countable b).aestronglyMeasurable
    simpa only [he] using hx
  have hp := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (n := h) hi (fun i _ => hg i) hr
  have hn := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (n := h) (hi.comp (fun _ t => -t) (fun _ => measurable_neg))
    (fun i _ => (hg i).neg) hr
  have hs : {x | r≤|∑ i∈Finset.range h,Y i x|} ⊆
      {x | r≤∑ i∈Finset.range h,Y i x} ∪ {x | r≤∑ i∈Finset.range h,-Y i x} := by
    intro x hx
    change r≤|_| at hx
    rcases le_abs.mp hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq,Finset.sum_neg_distrib] using hx)
  have hle := (measureReal_mono (μ := p.streamLaw) hs).trans (measureReal_union_le _ _)
  change _≤_ at hp hn
  push_cast at hp hn
  simp only [Real.norm_eq_abs,div_pow,sq_abs] at hp hn
  dsimp only [Y, Function.comp_apply] at hp hn hle
  simp only [div_pow]
  exact hle.trans (by linarith)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma prefixMaximum_eq_ladder {S : ℕ → ℤ} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    prefixMaximum S n=S (τ (renewalCount τ n)) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun k hk => h.maximum (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  · exact Finset.le_sup' S (Finset.mem_range.mpr (by have := renewalCount_spec h.zero n; omega))

lemma renewalCount_before {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) (r : ℕ) :
    renewalCount τ (τ (r+1)-1)=r := by
  apply le_antisymm
  · have ht : τ (r+1)-1<τ (r+1) := by have : r+1≤τ (r+1) := hτ.le_apply; omega
    have := (le_renewalCount_iff hτ h₀ (r+1) (τ (r+1)-1)).not.mpr (not_le_of_gt ht)
    omega
  · apply (le_renewalCount_iff hτ h₀ r (τ (r+1)-1)).mpr
    have ht : τ r<τ (r+1) := hτ (Nat.lt_succ_self r)
    omega

lemma recordTypeAt_ladder {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    recordTypeAt x (ladderTime x (r+1))=ladderType (ladderTail^[r] x) := by
  have hh := ladderTime_enumeration hx
  have hsum := ladderTime_step_level hx r
  unfold recordTypeAt ladderType
  rw [prefixMaximum_eq_ladder hh,renewalCount_before hh.strictMono hh.zero]
  apply Prod.ext
  · rw [ladderTail_iterate]
    change x (ladderTime x (r+1)-1)=x (ladderTime x r+ladderIndex (streamShift (ladderTime x r) x))
    congr 1
    rw [ladderTime,ladderTail_iterate]
    omega
  · change (integerSum x (ladderTime x (r+1))-integerSum x (ladderTime x r)).toNat=_
    rw [hsum,Int.toNat_natCast]
    rfl

lemma recordSpineSum_eq {x : ℕ → ℕ} (hx : HasAllLadders x) (b : ℕ×ℕ → ℝ) (v : ℕ) :
    recordSpineSum b x v=∑ i∈Finset.range (renewalCount (ladderTime x) v),
      b (ladderType (ladderTail^[i] x)) := by
  have he := ladderTime_enumeration hx
  rw [recordSpineSum,he.records,Finset.sum_image]
  · have hs : Finset.Icc 1 (renewalCount (ladderTime x) v)=
        (Finset.range (renewalCount (ladderTime x) v)).image (fun i => i+1) := by
      ext i
      simp only [Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
      constructor
      · intro hi
        exact ⟨i-1,by omega,by omega⟩
      · rintro ⟨j,hj,rfl⟩
        omega
    rw [hs,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      rw [recordTypeAt_ladder hx]
    · intro i _ j _ hij
      exact Nat.add_right_cancel hij
  · exact fun _ _ _ _ hij => he.strictMono.injective hij

lemma integerSum_congr_prefix {x y : ℕ → ℕ} {N : ℕ} (h : ∀ k<N,x k=y k) :
    ∀ k≤N,integerSum x k=integerSum y k := by
  intro k hk
  unfold integerSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)]

lemma recordSpineSum_congr_prefix {x y : ℕ → ℕ} {N : ℕ}
    (h : ∀ k<N,x k=y k) (b : ℕ×ℕ → ℝ) :
    recordSpineSum b x N=recordSpineSum b y N := by
  have hS := integerSum_congr_prefix h
  unfold recordSpineSum
  rw [weakRecords_congr_prefix hS]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨ht0,htN,_⟩ := (mem_weakRecords _ _ _).mp ht
  have he : recordTypeAt x t=recordTypeAt y t := by
    unfold recordTypeAt
    rw [h (t-1) (by omega),hS t htN,prefixMaximum_congr (fun k hk => hS k (by omega))]
  rw [he]

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma record_count_reverse (x : ℕ → ℕ) (v : ℕ) :
    (weakRecords (integerSum (reverseFirst v x)) v).card=recordHeight (integerSum x) 0 v := by
  rw [recordHeight_dual,Nat.sub_zero]
  congr 1
  exact weakRecords_congr_prefix (fun k hk => integerSum_reverseFirst x v k hk)

lemma CriticalEvenOffspring.record_spine_bound (p : CriticalEvenOffspring)
    (b : ℕ×ℕ → ℝ) (a d : ℝ) (hb : ∀ z,b z∈Set.Icc a d)
    (N K : ℕ) {r : ℝ} (hr : 0 < r) :
    p.streamLaw.real {x | ∃ v≤N,
      (weakRecords (integerSum (reverseFirst v x)) v).card≤K ∧
      r≤|recordSpineSum b (reverseFirst v x) v-
        (∫ z,b z ∂p.spineLaw)*(weakRecords (integerSum (reverseFirst v x)) v).card|} ≤
      (N+1:ℝ)*K*2*Real.exp (-r^2/(2*K*((d-a)/2)^2)) := by
  let E : ℕ → Set (ℕ → ℕ) := fun h => {x | r≤|∑ i∈Finset.range h,
    (b (ladderType (ladderTail^[i] x)) - ∫ z,b z ∂p.spineLaw)|}
  have hE (h) : MeasurableSet (E h) := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_of_countable b).comp (measurable_ladderType.comp
      (measurable_ladderTail.iterate i))).sub measurable_const
  let A : Fin (N+1) → Fin K → Set (ℕ → ℕ) := fun v h => reverseFirst v.val ⁻¹' E (h.val+1)
  have hsub : ∀ᵐ x ∂p.streamLaw,
      (∃ v≤N,(weakRecords (integerSum (reverseFirst v x)) v).card≤K ∧
        r≤|recordSpineSum b (reverseFirst v x) v-
          (∫ z,b z ∂p.spineLaw)*(weakRecords (integerSum (reverseFirst v x)) v).card|) →
        x∈⋃ v,⋃ h,A v h := by
    filter_upwards [p.ae_reverse_ladders] with x hx
    rintro ⟨v,hv,hK,hbad⟩
    have hen := ladderTime_enumeration (hx v)
    rw [recordSpineSum_eq (hx v),hen.card_records] at hbad
    rw [hen.card_records] at hK
    let h := renewalCount (ladderTime (reverseFirst v x)) v
    have hh0 : 0<h := by
      by_contra hn
      have he : h=0 := by omega
      change r≤|(∑ i∈Finset.range h,b (ladderType (ladderTail^[i] (reverseFirst v x)))) -
        (∫ z,b z ∂p.spineLaw)*h| at hbad
      simp only [he,Finset.range_zero,Finset.sum_empty,Nat.cast_zero,mul_zero,sub_self,abs_zero] at hbad
      exact hr.not_ge hbad
    apply Set.mem_iUnion.mpr
    refine ⟨⟨v,by omega⟩,Set.mem_iUnion.mpr ⟨⟨h-1,by change h≤K at hK; omega⟩,?_⟩⟩
    change reverseFirst v x∈E (h-1+1)
    rw [Nat.sub_add_cancel hh0]
    change r≤|∑ i∈Finset.range h,(b (ladderType (ladderTail^[i] (reverseFirst v x)))-_)|
    simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_comm] using hbad
  have hu := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  change _≤p.streamLaw.real (⋃ v,⋃ h,A v h) at hu
  apply hu.trans
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    ∑ v : Fin (N+1),p.streamLaw.real (⋃ h,A v h) ≤
        ∑ _v : Fin (N+1),∑ _h : Fin K,2*Real.exp (-r^2/(2*K*((d-a)/2)^2)) := by
      apply Finset.sum_le_sum
      intro v _
      apply (measureReal_iUnion_fintype_le _).trans
      apply Finset.sum_le_sum
      intro h _
      have hm : p.streamLaw.real (A v h)=p.streamLaw.real (E (h.val+1)) :=
        (reverseFirst_preserving p v.val).measureReal_preimage (hE _).nullMeasurableSet
      rw [hm]
      apply (p.spine_label_deviation b a d hb (h.val+1) r hr.le).trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hk : (h.val+1:ℝ)≤K := by exact_mod_cast Nat.succ_le_iff.mpr h.isLt
      have hc2 := sq_nonneg ((d-a)/2)
      by_cases hzero : ((d-a)/2)^2=0
      · simp only [hzero,mul_zero,div_zero,le_refl]
      · have hc : 0<((d-a)/2)^2 := lt_of_le_of_ne hc2 (Ne.symm hzero)
        simp only [neg_div,Nat.cast_add,Nat.cast_one]
        apply neg_le_neg
        change r^2/(2*K*((d-a)/2)^2) ≤ r^2/(2*(h.val+1)*((d-a)/2)^2)
        exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) (by nlinarith)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; push_cast; ring

lemma reverseFirst_prefix_congr {x y : ℕ → ℕ} {N v : ℕ} (hv : v≤N)
    (h : ∀ k<N,x k=y k) : ∀ k<v,reverseFirst v x k=reverseFirst v y k := by
  intro k hk
  simp only [reverseFirst]
  simp only [reverseIndex,ite_eq_left hk]
  exact h _ (by omega)

lemma CriticalEvenOffspring.code_spine_bound (p : CriticalEvenOffspring)
    (b : ℕ×ℕ → ℝ) (a d : ℝ) (hb : ∀ z,b z∈Set.Icc a d)
    (n K : ℕ) {r : ℝ} (hr : 0 < r) :
    (p.codeLaw n).real {c | ∃ v≤2*n+1,height c.val v≤K ∧
      r≤|codeSpineSum b c v-(∫ z,b z ∂p.spineLaw)*height c.val v|} ≤
      ((2*n+1:ℕ)+1:ℝ)*K*2*Real.exp (-r^2/(2*K*((d-a)/2)^2))/codePartition p (2*n+1) := by
  apply (p.code_probability_le_stream n _ _ ?_).trans
  · exact div_le_div_of_nonneg_right (p.record_spine_bound b a d hb (2*n+1) K hr)
      (codePartition_nonneg p _)
  · rintro c ⟨v,hv,hK,hbad⟩ x hx
    have hp : ∀ k<2*n+1,x k=arrayStream (codeEmbedding (2*n+1) c) k := by
      intro k hk
      have := congrFun hx ⟨k,hk⟩
      simpa [streamPrefix,arrayStream,hk] using this
    have hS : ∀ k≤2*n+1,integerSum x k=walk c.val k := by
      intro k hk
      rw [integerSum_congr_prefix hp k hk]
      exact integerSum_arrayStream_bridge ⟨c.val,c.property.1⟩ hk
    have hh : (weakRecords (integerSum (reverseFirst v x)) v).card=height c.val v := by
      rw [record_count_reverse,recordHeight_congr_prefix hv hS,← height_eq_recordHeight c.val hv]
    refine ⟨v,hv,hh.symm ▸ hK,?_⟩
    rw [hh,recordSpineSum_congr_prefix (reverseFirst_prefix_congr hv hp)]
    exact hbad

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma distribution_norm_tight {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Ω : ℕ → Type*} {Ω' : Type*} [∀ n,MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n,Measure (Ω n)} {ν : Measure Ω'} [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n,Ω n → E} {Y : Ω' → E} (h : TendstoInDistribution X atTop Y μ ν)
    (hm : ∀ n,Measurable (X n)) {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,(μ n).real {x | C<‖X n x‖}≤η := by
  let G : ℕ → E → ℝ := fun j z => min 1 (‖z‖/(j+1:ℝ))
  have hG (j) : Continuous (G j) := continuous_const.min (continuous_norm.div_const _)
  have hG0 (j z) : 0≤G j z := le_min (by norm_num) (by positivity)
  have hG1 (j z) : |G j z|≤1 := by rw [abs_of_nonneg (hG0 j z)]; exact min_le_left _ _
  have ht : Tendsto (fun j : ℕ => ∫ x,G j (Y x) ∂ν) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω' => (1:ℝ))
      (F := fun j x => G j (Y x)) (f := fun _ =>0)
      (fun j => ((hG j).measurable.comp_aemeasurable h.aemeasurable_limit).aestronglyMeasurable)
      (integrable_const _) (fun j => ae_of_all ν (fun z => hG1 j (Y z))) (by
        apply ae_of_all
        intro z
        have hh : Tendsto (fun j : ℕ => ‖Y z‖/(j+1:ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa only [G,min_eq_right (by norm_num : (0:ℝ)≤1)] using
          (tendsto_const_nhds.min hh (f := fun _ : ℕ => (1:ℝ))))
    simpa only [integral_zero] using hh
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds (half_pos hη))).exists
  have hx := integral_tendsto_of_tendstoInDistribution h (hG j) (hG1 j)
  refine ⟨j+1,by positivity,?_⟩
  filter_upwards [hx.eventually (gt_mem_nhds (hj.trans (half_lt_self hη)))] with n hn
  apply le_of_lt (lt_of_le_of_lt ?_ hn)
  let A := {x : Ω n | (j+1:ℝ)<‖X n x‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hm n).norm
  rw [← integral_indicator_one hA]
  have hi : Integrable (fun x => G j (X n x)) (μ n) :=
    Integrable.of_bound ((hG j).measurable.comp (hm n)).aestronglyMeasurable 1
      (ae_of_all _ (fun x => hG1 j (X n x)))
  apply integral_mono ((integrable_const (1:ℝ)).indicator hA) hi
  intro x
  by_cases hx : x∈A
  · rw [Set.indicator_of_mem hx]
    exact le_min le_rfl ((le_div_iff₀ (by positivity : (0:ℝ)<j+1)).mpr (by simpa using hx.le))
  · rw [Set.indicator_of_notMem hx]
    exact hG0 j _

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitIntervalProd_solutions_2
local instance instBorelSpaceContinuousMapElemRealUnitIntervalProd_solutions_2 : BorelSpace C(unitInterval,ℝ×ℝ) := ⟨rfl⟩

lemma code_height_le_norm {N : ℕ} (hN : 0<N) (p : CriticalEvenOffspring) (d : Code N)
    {v : ℕ} (hv : v≤N) :
    (height d.val v:ℝ)≤(2/p.sigma)*Real.sqrt (N:ℝ)*‖jointCode p.sigma d‖ := by
  have hσ := p.sigma_pos
  have h := ContinuousMap.norm_coe_le_norm (jointCode p.sigma d) (gridPoint N ⟨v,by omega⟩)
  have he : (jointCode p.sigma d (gridPoint N ⟨v,by omega⟩)).2=
      p.sigma*height d.val v/(2*Real.sqrt N) := by
    change (interpolation N _ (gridPoint N ⟨v,by omega⟩))=_
    exact interpolation_gridPoint hN _ _
  have h2 : ‖(jointCode p.sigma d (gridPoint N ⟨v,by omega⟩)).2‖≤‖jointCode p.sigma d‖ :=
    (norm_snd_le _).trans h
  rw [he,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at h2
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hb := (div_le_iff₀ (by positivity : 0<2*Real.sqrt (N:ℝ))).mp h2
  have hg : (height d.val v:ℝ)*p.sigma ≤
      ((2/p.sigma)*Real.sqrt (N:ℝ)*‖jointCode p.sigma d‖)*p.sigma := by
    calc
      _ = p.sigma*(height d.val v:ℝ) := by ring
      _ ≤ ‖jointCode p.sigma d‖*(2*Real.sqrt N) := hb
      _ = _ := by field_simp
  exact (mul_le_mul_iff_left₀ p.sigma_pos).mp hg

lemma CriticalEvenOffspring.code_height_tight (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      (p.codeLaw n).real {d | ∃ v≤2*n+1,C*Real.sqrt ((2*n+1:ℕ):ℝ)<height d.val v}≤η := by
  have hσ := p.sigma_pos
  obtain ⟨C,hC,hlim⟩ := distribution_norm_tight (p.jointCode_vervaat_CLT hB)
    (fun _ => measurable_of_countable _) hη
  refine ⟨(2/p.sigma)*C,by positivity,?_⟩
  filter_upwards [hlim] with n hn
  apply (measureReal_mono ?_).trans hn
  rintro d ⟨v,hv,hbad⟩
  change C<‖jointCode p.sigma d‖
  have he := code_height_le_norm (by omega : 0<2*n+1) p d hv
  have hs : 0<Real.sqrt ((2*n+1:ℕ):ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hc : 0<2/p.sigma := by positivity
  apply (mul_lt_mul_iff_right₀ (mul_pos hc hs)).mp
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hbad.trans_le he

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma polynomial_exp_sqrt {κ : ℝ} (hκ : 0<κ) (k : ℕ) :
    Tendsto (fun n : ℕ => (Real.sqrt ((2*n+1:ℕ):ℝ))^k *
      Real.exp (-κ*Real.sqrt ((2*n+1:ℕ):ℝ))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (odd_sqrt_tendsto.const_mul_atTop hκ)).div_const (κ^k)
  simp only [zero_div] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [Function.comp_apply,mul_pow,neg_mul]
  field_simp

lemma CriticalEvenOffspring.code_spine_exp_vanish (p : CriticalEvenOffspring)
    {κ : ℝ} (hκ : 0<κ) (C : ℝ) :
    Tendsto (fun n : ℕ => 2*(C+1)*(((2*n+1:ℕ):ℝ)+1)*Real.sqrt ((2*n+1:ℕ):ℝ)*
      Real.exp (-κ*Real.sqrt ((2*n+1:ℕ):ℝ))/codePartition p (2*n+1)) atTop (𝓝 0) := by
  have h := ((polynomial_exp_sqrt hκ 6).add (polynomial_exp_sqrt hκ 4)).const_mul (2*(C+1))
  have hpos : 0<2/(p.sigma*Real.sqrt (2*Real.pi)) :=
    div_pos (by norm_num) (mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by positivity)))
  have ht := h.div p.codePartition_asymptotic hpos.ne'
  simp only [zero_add,mul_zero,zero_div] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  set s := Real.sqrt ((2*n+1:ℕ):ℝ)
  have hs : s^2=((2*n+1:ℕ):ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : s≠0 := (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<((2*n+1:ℕ):ℝ))).ne'
  have hsn : (2*n+1:ℝ)=s^2 := by rw [hs]; push_cast; rfl
  change _=2*(C+1)*(s^6*Real.exp (-κ*s)+s^4*Real.exp (-κ*s))/
    ((2*n+1:ℝ)*Real.sqrt (2*n+1)*codePartition p (2*n+1))
  rw [show Real.sqrt (2*n+1:ℝ)=s by congr 1; push_cast; rfl,hsn,← hs]
  field_simp

lemma spine_exp_ceiling_bound {C R ε s : ℝ} (hC : 0<C) (hR : 0<R)
    (hε : 0<ε) (hs : 1 ≤ s) :
    (⌈C*s⌉₊:ℝ)*2*Real.exp (-(ε*s)^2/(2*⌈C*s⌉₊*R^2)) ≤
      2*(C+1)*s*Real.exp (-(ε^2/(2*(C+1)*R^2))*s) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hK : (⌈C*s⌉₊:ℝ)≤(C+1)*s := by
    have h := (Nat.ceil_lt_add_one (mul_nonneg hC.le hs0.le)).le
    nlinarith
  have hK0 : 0<(⌈C*s⌉₊:ℝ) := (mul_pos hC hs0).trans_le (Nat.le_ceil _)
  have he : -(ε*s)^2/(2*⌈C*s⌉₊*R^2) ≤ -(ε^2/(2*(C+1)*R^2))*s := by
    rw [neg_div,neg_mul]
    apply neg_le_neg
    apply (le_div_iff₀ (by positivity : 0<2*(⌈C*s⌉₊:ℝ)*R^2)).mpr
    have heq : (ε^2/(2*(C+1)*R^2))*s*(2*(C+1)*s*R^2)=(ε*s)^2 := by
      field_simp
    calc
      _ ≤ (ε^2/(2*(C+1)*R^2))*s*(2*(C+1)*s*R^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg R)]
      _ = _ := heq
  apply mul_le_mul (by nlinarith : (⌈C*s⌉₊:ℝ)*2≤2*(C+1)*s)
    (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by positivity)

/-- All-vertex bounded ancestral sums under the actual conditioned code law.
The centering is the derived spine expectation, not an assumed path average. -/
theorem CriticalEvenOffspring.uniform_bounded_spine_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (b : ℕ×ℕ → ℝ) {R ε : ℝ} (hR : 0<R) (hb : ∀ z,|b z|≤R) (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real {c | ∃ v≤2*n+1,
      ε*Real.sqrt ((2*n+1:ℕ):ℝ)< |codeSpineSum b c v-(∫ z,b z ∂p.spineLaw)*height c.val v|})
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  intro η hη
  obtain ⟨C,hC,htight⟩ := p.code_height_tight hB (by positivity : 0<η/3)
  let κ := ε^2/(2*(C+1)*R^2)
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hlim := p.code_spine_exp_vanish hκ C
  filter_upwards [htight,hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/3))] with n hn hln
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let K := ⌈C*s⌉₊
  let A := {c : Code N | ∃ v≤N,C*s<height c.val v}
  let D := {c : Code N | ∃ v≤N,height c.val v≤K ∧
      ε*s≤|codeSpineSum b c v-(∫ z,b z ∂p.spineLaw)*height c.val v|}
  have hs : 1 ≤ s := by
    change 1≤Real.sqrt (N:ℝ)
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    dsimp [N]
    norm_num
  have hsub : {c : Code N | ∃ v≤N,ε*s< |codeSpineSum b c v-(∫ z,b z ∂p.spineLaw)*height c.val v|}
      ⊆ A∪D := by
    rintro c ⟨v,hv,hbad⟩
    by_cases hh : C*s<(height c.val v:ℝ)
    · exact Or.inl ⟨v,hv,hh⟩
    · exact Or.inr ⟨v,hv,by exact_mod_cast (not_lt.mp hh).trans (Nat.le_ceil (C*s)),hbad.le⟩
  have hbound := p.code_spine_bound b (-R) R (fun z => abs_le.mp (hb z)) n K
    (mul_pos hε (lt_of_lt_of_le zero_lt_one hs))
  have hbd : (p.codeLaw n).real D ≤
      2*(C+1)*((N:ℝ)+1)*s*Real.exp (-κ*s)/codePartition p N := by
    apply hbound.trans
    simp only [sub_neg_eq_add,show (R+R)/2=R by ring]
    apply div_le_div_of_nonneg_right _ (codePartition_nonneg p N)
    have he := mul_le_mul_of_nonneg_left (spine_exp_ceiling_bound hC hR hε hs)
      (by positivity : 0≤(N:ℝ)+1)
    dsimp [K,κ] at *
    nlinarith
  have hh := (measureReal_mono (μ := p.codeLaw n) hsub).trans (measureReal_union_le A D)
  change (p.codeLaw n).real A≤η/3 at hn
  change 2*(C+1)*((N:ℝ)+1)*s*Real.exp (-κ*s)/codePartition p N<η/3 at hln
  exact hh.trans_lt (by linarith [hbd.trans_lt hln])

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

lemma spineTail_nonneg (m : ℕ) (z : ℕ×ℕ) : 0 ≤ spineTail m z := by
  unfold spineTail; split_ifs  <;>  positivity

lemma spineTail_le (m : ℕ) (z : ℕ×ℕ) : spineTail m z ≤ z.1 := by
  unfold spineTail; split_ifs
  · exact le_rfl
  · positivity

lemma spineTrunc_bound (m : ℕ) (b : ℕ×ℕ → ℝ) (hb : ∀ z,|b z| ≤ z.1) (z : ℕ×ℕ) :
    |spineTrunc m b z| ≤ m := by
  unfold spineTrunc
  split_ifs with h
  · exact (hb z).trans (by exact_mod_cast h)
  · simp

lemma spineTrunc_tail_bound (m : ℕ) (b : ℕ×ℕ → ℝ) (hb : ∀ z,|b z| ≤ z.1) (z : ℕ×ℕ) :
    |b z-spineTrunc m b z| ≤ spineTail m z := by
  by_cases h : z.1 ≤ m
  · simp [spineTrunc,spineTail,h,not_lt.mpr h]
  · simp [spineTrunc,spineTail,h,lt_of_not_ge h,hb]

lemma CriticalEvenOffspring.spine_integrable_dom (p : CriticalEvenOffspring) (b : ℕ×ℕ → ℝ)
    (hb : ∀ z,|b z| ≤ z.1) : Integrable b p.spineLaw := by
  exact p.spine_integrable_fst.mono' (measurable_of_countable b).aestronglyMeasurable
    (ae_of_all _ (fun z =>  by simpa only [Real.norm_eq_abs] using hb z))

lemma CriticalEvenOffspring.spine_tail_integral_tendsto (p : CriticalEvenOffspring) :
    Tendsto (fun m =>  ∫ z,spineTail m z ∂p.spineLaw) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := p.spineLaw) (f := fun _ => (0:ℝ)) (fun z : ℕ×ℕ =>  (z.1:ℝ))
    (fun m =>  (measurable_of_countable (spineTail m)).aestronglyMeasurable)
    p.spine_integrable_fst
    (fun m =>  ae_of_all _ (fun z =>  by simpa only [Real.norm_eq_abs,abs_of_nonneg (spineTail_nonneg m z)] using spineTail_le m z))
    (ae_of_all _ (fun z =>  by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop z.1] with m hm
      simp [spineTail,not_lt.mpr hm]))
  simpa using hh

lemma codeSpineSum_sub {N : ℕ} (d : Code N) (b c : ℕ×ℕ → ℝ) (v : ℕ) :
    codeSpineSum (fun z =>  b z-c z) d v=codeSpineSum b d v-codeSpineSum c d v := by
  simp [codeSpineSum,recordSpineSum,Finset.sum_sub_distrib]

lemma CriticalEvenOffspring.spineTrunc_integral_error (p : CriticalEvenOffspring)
    (m : ℕ) (b : ℕ×ℕ → ℝ) (hb : ∀ z,|b z| ≤ z.1) :
    |(∫ z,b z ∂p.spineLaw)-(∫ z,spineTrunc m b z ∂p.spineLaw)| ≤ ∫ z,spineTail m z ∂p.spineLaw := by
  have hi := p.spine_integrable_dom b hb
  have hj := p.spine_integrable_dom (spineTrunc m b) (fun z =>  by
    unfold spineTrunc; split_ifs  <;>  simp [hb z])
  rw [← integral_sub hi hj]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono (hi.sub hj).abs (p.spine_integrable_dom (spineTail m) (fun z =>  by
    rw [abs_of_nonneg (spineTail_nonneg m z)]; exact spineTail_le m z))
  exact spineTrunc_tail_bound m b hb

lemma spineTail_eq (m : ℕ) : spineTail m=(fun z =>  (z.1:ℝ)-spineTrunc m (fun z =>  (z.1:ℝ)) z) := by
  funext z
  by_cases h : z.1 ≤ m  <;>  simp [spineTail,spineTrunc,h,not_lt.mpr,lt_of_not_ge]

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma spineRecordVertex_injective {N : ℕ} (d : Code N) {v : ℕ} (hv : v ≤ N) :
    Function.Injective (spineRecordVertex d hv) := by
  intro t u he
  have ht := spineRecord_bounds d v t
  have hu := spineRecord_bounds d v u
  apply Subtype.ext
  have h := congrArg Fin.val he
  dsimp [spineRecordVertex] at h
  omega

lemma spineRecordType_fst {N : ℕ} (d : Code N) {v : ℕ} (hv : v ≤ N) (t : SpineRecords d v) :
    (spineRecordType d v t).1=(d.val (spineRecordVertex d hv t)).val := by
  have ht := spineRecord_bounds d v t
  have hlt : t.val-1 < v := by omega
  have he : v-1-(t.val-1)=v-t.val := by omega
  simp [spineRecordType,recordTypeAt,reverseFirst,reverseIndex,hlt,he,arrayStream,
    show v-t.val < N by omega,codeEmbedding,bridgeEmbedding,spineRecordVertex]
  rfl

lemma spineRecords_card {N : ℕ} (d : Code N) {v : ℕ} (hv : v ≤ N) :
    Fintype.card (SpineRecords d v)=height d.val v := by
  have h := codeSpineSum_one d hv
  simp only [codeSpineSum,recordSpineSum,Finset.sum_const,nsmul_eq_mul,mul_one] at h
  rw [Fintype.card_coe]
  exact_mod_cast h

variable {A : Type*} [MeasurableSpace A]

omit [MeasurableSpace A] in
lemma markedSpineSum_deterministic {N : ℕ} (b : ℕ×ℕ → ℝ) (d : Code N) {v : ℕ}
    (hv : v ≤ N) (a : Fin N → A) :
    markedSpineSum (fun z _ => b z) d hv a=codeSpineSum b d v := by
  unfold markedSpineSum codeSpineSum recordSpineSum
  exact Finset.sum_coe_sort _ (fun t => b (recordTypeAt (reverseFirst v (arrayStream (codeEmbedding N d))) t))

lemma measurable_markedSpineSum {N : ℕ} (b : (ℕ×ℕ) → A → ℝ)
    (hb : ∀ z,Measurable (b z)) (d : Code N) {v : ℕ} (hv : v ≤ N) :
    Measurable (markedSpineSum b d hv) := by
  exact Finset.measurable_sum _ (fun t _ => (hb _).comp (measurable_pi_apply _))

/-- Conditional on the actual tree, distinct ancestors carry independent correctly sampled marks. -/
lemma markedSpine_iIndep {N : ℕ} (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (d : Code N) {v : ℕ} (hv : v ≤ N) :
    iIndepFun (fun t : SpineRecords d v => fun a : Fin N → A => a (spineRecordVertex d hv t))
      (codeMarkLaw κ d) := by
  exact (iIndepFun_pi (μ := fun i => κ (d.val i).val)
    (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).precomp (spineRecordVertex_injective d hv)

lemma markedSpine_hasLaw {N : ℕ} (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (d : Code N) {v : ℕ} (hv : v ≤ N) (t : SpineRecords d v) :
    HasLaw (fun a : Fin N → A => a (spineRecordVertex d hv t))
      (κ (spineRecordType d v t).1) (codeMarkLaw κ d) := by
  rw [spineRecordType_fst d hv t]
  exact (measurePreserving_eval (fun i => κ (d.val i).val) _).hasLaw

/-- Bounded random marks concentrate round their conditional ancestral means. -/
lemma markedSpine_deviation {N : ℕ} (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ}
    (hbound : ∀ z a,|b z a| ≤ R) (d : Code N) {v : ℕ} (hv : v ≤ N)
    {r : ℝ} (hr : 0 ≤ r) :
    (codeMarkLaw κ d).real {a | r ≤ |markedSpineSum b d hv a-
      codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v|} ≤
        2*Real.exp (-r^2/(2*(height d.val v)*R^2)) := by
  let Y : SpineRecords d v → (Fin N → A) → ℝ := fun t a =>
    b (spineRecordType d v t) (a (spineRecordVertex d hv t))-
      ∫ a,b (spineRecordType d v t) a ∂κ (spineRecordType d v t).1
  have hind : iIndepFun Y (codeMarkLaw κ d) :=
    (markedSpine_iIndep κ d hv).comp (fun t a => b (spineRecordType d v t) a-
      ∫ a,b (spineRecordType d v t) a ∂κ (spineRecordType d v t).1)
      (fun t => (hb _).sub measurable_const)
  have hG : ∀ t,HasSubgaussianMGF (Y t) ((‖(R:ℝ)-(-R)‖₊/2)^2) (codeMarkLaw κ d) := by
    intro t
    have hh := hasSubgaussianMGF_of_mem_Icc (μ := codeMarkLaw κ d)
      ((hb _).comp (measurable_pi_apply _)).aemeasurable
      (ae_of_all _ (fun a => abs_le.mp (hbound (spineRecordType d v t) (a (spineRecordVertex d hv t)))))
    have he := (markedSpine_hasLaw κ d hv t).integral_comp (hb (spineRecordType d v t)).aestronglyMeasurable
    rw [he] at hh
    simpa only [Function.comp_def,Y] using hh
  have hp := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ) hind (fun t _ => hG t) hr
  have hn := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ)
    (hind.comp (fun _ x => -x) (fun _ => measurable_neg)) (fun t _ => (hG t).neg) hr
  have he (a : Fin N → A) : markedSpineSum b d hv a-
      codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v=∑ t,Y t a := by
    rw [← markedSpineSum_deterministic (A := A) _ d hv a]
    unfold markedSpineSum
    exact (Finset.sum_sub_distrib _ _).symm
  have hsub : {a : Fin N → A | r ≤ |markedSpineSum b d hv a-
      codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v|} ⊆
      {a | r ≤ ∑ t,Y t a} ∪ {a | r ≤ ∑ t,-Y t a} := by
    intro a ha
    change r ≤ |_| at ha
    rw [he] at ha
    rcases le_abs.mp ha with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq,Finset.sum_neg_distrib] using h)
  have hle := (measureReal_mono (μ := codeMarkLaw κ d) hsub).trans (measureReal_union_le _ _)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hp hn
  push_cast at hp hn
  simp only [Real.norm_eq_abs,div_pow,sq_abs,show (R- -R)^2/2^2=R^2 by ring,
    spineRecords_card d hv,Function.comp_def] at hp hn
  simp only [mul_assoc]
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

variable {A : Type*} [MeasurableSpace A]

lemma compProd_real_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    {E : Set (α×β)} (hE : MeasurableSet E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x,(κ x).real (Prod.mk x ⁻¹' E) ≤ C) : (μ ⊗ₘ κ).real E ≤ C := by
  have he : (μ ⊗ₘ κ) E ≤ ENNReal.ofReal C := by
    rw [Measure.compProd_apply hE]
    calc
      _ ≤ ∫⁻ _,ENNReal.ofReal C ∂μ := lintegral_mono (fun x => by
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (hb x))
      _ = _ := by simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hC)

lemma CriticalEvenOffspring.markedCodeLaw_fst (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (n : ℕ) (E : Set (Code (2*n+1))) :
    (p.markedCodeLaw κ n).real (Prod.fst ⁻¹' E)=(p.codeLaw n).real E := by
  have hh : Prod.fst ⁻¹' E=E×ˢ(Set.univ : Set (Fin (2*n+1) → A)) := by ext x; simp
  unfold Measure.real
  rw [hh,CriticalEvenOffspring.markedCodeLaw,Measure.compProd_apply_prod (Set.to_countable E).measurableSet MeasurableSet.univ]
  simp

lemma measurable_marked_spine_joint {N : ℕ} (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z))
    {v : ℕ} (hv : v ≤ N) :
    Measurable (fun x : Code N × (Fin N → A) => markedSpineSum b x.1 hv x.2) :=
  measurable_from_prod_countable_right (fun d => measurable_markedSpineSum b hb d hv)

omit [MeasurableSpace A] in
lemma markedSpineSum_zero_height {N : ℕ} (b : (ℕ×ℕ) → A → ℝ) (d : Code N)
    {v : ℕ} (hv : v ≤ N) (hh : height d.val v=0) (a : Fin N → A) :
    markedSpineSum b d hv a=0 := by
  have hc : Fintype.card (SpineRecords d v)=0 := (spineRecords_card d hv).trans hh
  let : IsEmpty (SpineRecords d v) := Fintype.card_eq_zero_iff.mp hc
  simp [markedSpineSum]

lemma marked_short_spine_bound {N : ℕ} (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z a,|b z a| ≤ R) (d : Code N) (K : ℕ) {r : ℝ} (hr : 0 < r) :
    (codeMarkLaw κ d).real {a | ∃ v : Fin (N+1),height d.val v.val ≤ K ∧
      r ≤ |markedSpineSum b d (Nat.le_of_lt_succ v.isLt) a-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|} ≤
      (N+1:ℝ)*2*Real.exp (-r^2/(2*K*R^2)) := by
  let E : Fin (N+1) → Set (Fin N → A) := fun v => {a | height d.val v.val ≤ K ∧
    r ≤ |markedSpineSum b d (Nat.le_of_lt_succ v.isLt) a-
      codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|}
  have he : {a | ∃ v : Fin (N+1),height d.val v.val ≤ K ∧
      r ≤ |markedSpineSum b d (Nat.le_of_lt_succ v.isLt) a-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|}=⋃ v,E v := by ext a; simp [E]
  rw [he]
  apply (measureReal_iUnion_fintype_le E).trans
  calc
    _ ≤ ∑ _ : Fin (N+1),2*Real.exp (-r^2/(2*K*R^2)) := Finset.sum_le_sum (by
      intro v _
      by_cases hh : height d.val v.val ≤ K
      · by_cases h0 : height d.val v.val=0
        · have hE : E v=∅ := by
            ext a
            have hz := markedSpineSum_zero_height b d (Nat.le_of_lt_succ v.isLt) h0 a
            have hm := markedSpineSum_zero_height (fun z (_ : A) => ∫ a,b z a ∂κ z.1) d
              (Nat.le_of_lt_succ v.isLt) h0 a
            rw [markedSpineSum_deterministic] at hm
            simp [E,hz,hm,not_le.mpr hr]
          rw [hE,measureReal_empty]
          positivity
        · have hpos : 0 < (height d.val v.val:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
          have hKpos : 0 < (K:ℝ) := hpos.trans_le (by exact_mod_cast hh)
          have hm := markedSpine_deviation κ b hb hbound d (Nat.le_of_lt_succ v.isLt) hr.le
          have hes : E v={a | r ≤ |markedSpineSum b d (Nat.le_of_lt_succ v.isLt) a-
            codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|} := by ext a; simp [E,hh]
          rw [hes]
          apply hm.trans
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
          rw [neg_div,neg_div]
          apply neg_le_neg
          apply div_le_div_of_nonneg_left (sq_nonneg r) (by positivity)
          have hle : (height d.val v.val:ℝ) ≤ K := by exact_mod_cast hh
          nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg R)]
      · have hE : E v=∅ := by ext a; simp [E,hh]
        rw [hE,measureReal_empty]
        positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

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
-- module Solutions.OAIQ021_FK.FKMaps_MarkedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma marked_exp_vanish {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (((2*n+1:ℕ):ℝ)+1)*Real.exp (-κ*Real.sqrt ((2*n+1:ℕ):ℝ)))
      atTop (𝓝 0) := by
  have h := (polynomial_exp_sqrt hκ 2).add (polynomial_exp_sqrt hκ 0)
  simp only [zero_add] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [Real.sq_sqrt (by positivity)]
  simp only [pow_zero,one_mul]
  ring


variable {A : Type*} [MeasurableSpace A]

lemma CriticalEvenOffspring.marked_short_unconditional_bound (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z a,|b z a| ≤ R) (n K : ℕ) {r : ℝ} (hr : 0 < r) :
    (p.markedCodeLaw κ n).real {x | ∃ v : Fin (2*n+2),height x.1.val v.val ≤ K ∧
      r ≤ |markedSpineSum b x.1 (by omega : v.val ≤ 2*n+1) x.2-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) x.1 v.val|} ≤
      ((2*n+1:ℕ)+1:ℝ)*2*Real.exp (-r^2/(2*K*R^2)) := by
  refine compProd_real_bound (p.codeLaw n) (codeMarkKernel κ (2*n+1)) ?_ (by positivity) ?_
  · simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro v
    have hh : MeasurableSet {x : Code (2*n+1) × (Fin (2*n+1) → A) | height x.1.val v.val ≤ K} :=
      (Set.to_countable {d : Code (2*n+1) | height d.val v.val ≤ K}).measurableSet.preimage measurable_fst
    exact hh.inter (measurableSet_le measurable_const
      (((measurable_marked_spine_joint b hb (by omega : v.val ≤ 2*n+1)).sub
        ((measurable_of_countable (fun d : Code (2*n+1) => codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val)).comp measurable_fst)).abs))
  · intro d
    change (codeMarkLaw κ d).real {a | ∃ v : Fin (2*n+2),height d.val v.val ≤ K ∧
      r ≤ |markedSpineSum b d (by omega : v.val ≤ 2*n+1) a-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|} ≤ _
    simpa only [Nat.add_assoc,show 1+1=2 by rfl] using marked_short_spine_bound κ b hb hR hbound d K hr

/-- Random marks are negligible relative to their conditional path means, uniformly over vertices. -/
lemma CriticalEvenOffspring.uniform_mark_noise (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z a,|b z a| ≤ R) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (p.markedCodeLaw κ n).real {x | ∃ v : Fin (2*n+2),
      ε*Real.sqrt ((2*n+1:ℕ):ℝ) < |markedSpineSum b x.1 (by omega : v.val ≤ 2*n+1) x.2-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) x.1 v.val|}) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  intro η hη
  obtain ⟨C,hC,htight⟩ := p.code_height_tight hB (by positivity : 0 < η/3)
  let δ := ε^2/(2*(C+1)*R^2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlim := (marked_exp_vanish hδ).const_mul 2
  simp only [mul_zero] at hlim
  filter_upwards [htight,hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/3))] with n hn hl
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let K := ⌈C*s⌉₊
  let E0 := {d : Code N | ∃ v ≤ N,C*s < height d.val v}
  let E1 := {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),height x.1.val v.val ≤ K ∧
      ε*s ≤ |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) x.1 v.val|}
  have hsub : {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),ε*s <
      |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) x.1 v.val|} ⊆ (Prod.fst ⁻¹' E0)∪E1 := by
    rintro x ⟨v,hv⟩
    by_cases hh : C*s < (height x.1.val v.val:ℝ)
    · exact Or.inl ⟨v.val,Nat.le_of_lt_succ v.isLt,hh⟩
    · exact Or.inr ⟨v,by exact_mod_cast (not_lt.mp hh).trans (Nat.le_ceil (C*s)),hv.le⟩
  have hs : 1 ≤ s := by
    change 1 ≤ Real.sqrt (N:ℝ)
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    dsimp [N]; norm_num
  have hK : (K:ℝ) ≤ (C+1)*s := by
    have h := (Nat.ceil_lt_add_one (mul_nonneg hC.le (lt_of_lt_of_le zero_lt_one hs).le)).le
    dsimp [K]; nlinarith
  have hK0 : 0 < (K:ℝ) := (mul_pos hC (lt_of_lt_of_le zero_lt_one hs)).trans_le (Nat.le_ceil _)
  have he : -(ε*s)^2/(2*K*R^2) ≤ -δ*s := by
    rw [neg_div,neg_mul]
    apply neg_le_neg
    apply (le_div_iff₀ (by positivity : 0 < 2*(K:ℝ)*R^2)).mpr
    have heq : δ*s*(2*(C+1)*s*R^2)=(ε*s)^2 := by dsimp [δ]; field_simp
    calc
      _ ≤ δ*s*(2*(C+1)*s*R^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg R)]
      _ = _ := heq
  have hbnd : (p.markedCodeLaw κ n).real E1 ≤ 2*((N:ℝ)+1)*Real.exp (-δ*s) := by
    apply (p.marked_short_unconditional_bound κ b hb hR hbound n K
      (mul_pos hε (lt_of_lt_of_le zero_lt_one hs))).trans
    change ((N:ℝ)+1)*2*Real.exp (-(ε*s)^2/(2*K*R^2)) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity : 0 ≤ ((N:ℝ)+1)*2)]
  have hprob := (measureReal_mono (μ := p.markedCodeLaw κ n) hsub).trans (measureReal_union_le _ _)
  rw [p.markedCodeLaw_fst] at hprob
  change (p.codeLaw n).real E0 ≤ η/3 at hn
  simp only [← mul_assoc] at hl
  change 2*(((2*n+1:ℕ):ℝ)+1)*Real.exp (-δ*Real.sqrt ((2*n+1:ℕ):ℝ)) < η/3 at hl
  change 2*((N:ℝ)+1)*Real.exp (-δ*s) < η/3 at hl
  exact hprob.trans_lt (by linarith)

lemma markMean_bound (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) {R : ℝ} (hb : ∀ z a,|b z a| ≤ R) (z : ℕ×ℕ) :
    |∫ a,b z a ∂κ z.1| ≤ R := by
  have h := norm_integral_le_of_norm_le_const (μ := κ z.1) (f := b z) (C := R)
    (ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using hb z a))
  simpa [Real.norm_eq_abs,Measure.real] using h

/-- The bounded marked theorem with the source's genuine spine mean. -/
theorem CriticalEvenOffspring.uniform_bounded_marked_spine (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z a,|b z a| ≤ R) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (p.markedCodeLaw κ n).real {x | ∃ v : Fin (2*n+2),
      ε*Real.sqrt ((2*n+1:ℕ):ℝ) < |markedSpineSum b x.1 (by omega : v.val ≤ 2*n+1) x.2-
        (∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|}) atTop (𝓝 0) := by
  let bm := fun z => ∫ a,b z a ∂κ z.1
  have h ε' (hε' : 0 < ε') := p.uniform_mark_noise hB κ b hb hR hbound hε'
  have ht := p.uniform_bounded_spine_limit hB bm hR (markMean_bound κ b hbound) (by positivity : 0 < ε/2)
  have hn := h (ε/2) (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa only [zero_add] using hn.add ht)
    (fun _ => measureReal_nonneg)
  intro n
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let E0 := {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),(ε/2)*s <
      |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-codeSpineSum bm x.1 v.val|}
  let E1 := {d : Code N | ∃ v ≤ N,(ε/2)*s <
      |codeSpineSum bm d v-(∫ z,bm z ∂p.spineLaw)*height d.val v|}
  have hsub : {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),ε*s <
      |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-(∫ z,bm z ∂p.spineLaw)*height x.1.val v.val|}
      ⊆ E0 ∪ (Prod.fst ⁻¹' E1) := by
    rintro x ⟨v,hv⟩
    by_contra hnot
    simp only [Set.mem_union,not_or] at hnot
    have h0 : |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-codeSpineSum bm x.1 v.val| ≤ (ε/2)*s := by
      by_contra hn; exact hnot.1 ⟨v,lt_of_not_ge hn⟩
    have h1 : |codeSpineSum bm x.1 v.val-(∫ z,bm z ∂p.spineLaw)*height x.1.val v.val| ≤ (ε/2)*s := by
      by_contra hn; exact hnot.2 ⟨v.val,Nat.le_of_lt_succ v.isLt,lt_of_not_ge hn⟩
    have hh := abs_sub_le (markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2)
      (codeSpineSum bm x.1 v.val) ((∫ z,bm z ∂p.spineLaw)*height x.1.val v.val)
    linarith
  have hh := (measureReal_mono (μ := p.markedCodeLaw κ n) hsub).trans (measureReal_union_le _ _)
  rw [p.markedCodeLaw_fst] at hh
  exact hh

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
variable {A : Type*} [MeasurableSpace A]

lemma measurable_markedTrunc (m : ℕ) (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) (z : ℕ×ℕ) :
    Measurable (markedTrunc m b z) := by
  unfold markedTrunc; split_ifs
  · exact hb z
  · exact measurable_const

omit [MeasurableSpace A] in
lemma markedTrunc_bound (m : ℕ) (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z a,|b z a| ≤ z.1) (z : ℕ×ℕ) (a : A) :
    |markedTrunc m b z a| ≤ m := by
  exact spineTrunc_bound m (fun z => b z a) (fun z => hb z a) z

lemma markedTrunc_mean (κ : ℕ → Measure A) (m : ℕ) (b : (ℕ×ℕ) → A → ℝ) (z : ℕ×ℕ) :
    (∫ a,markedTrunc m b z a ∂κ z.1)=spineTrunc m (fun z => ∫ a,b z a ∂κ z.1) z := by
  unfold markedTrunc spineTrunc
  split_ifs <;> simp

omit [MeasurableSpace A] in
lemma markedSpineSum_sub {N : ℕ} (b c : (ℕ×ℕ) → A → ℝ) (d : Code N)
    {v : ℕ} (hv : v ≤ N) (a : Fin N → A) :
    markedSpineSum (fun z a => b z a-c z a) d hv a=markedSpineSum b d hv a-markedSpineSum c d hv a := by
  unfold markedSpineSum
  exact Finset.sum_sub_distrib _ _

omit [MeasurableSpace A] in
lemma markedSpineSum_abs_dom {N : ℕ} (b : (ℕ×ℕ) → A → ℝ) (c : ℕ×ℕ → ℝ)
    (hb : ∀ z a,|b z a| ≤ c z) (d : Code N) {v : ℕ} (hv : v ≤ N) (a : Fin N → A) :
    |markedSpineSum b d hv a| ≤ codeSpineSum c d v := by
  rw [← markedSpineSum_deterministic c d hv a]
  unfold markedSpineSum
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun t _ => hb _ _))

lemma marked_spine_tail_control {N : ℕ} (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (d : Code N)
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z a,|b z a| ≤ z.1) (m : ℕ)
    {v : ℕ} (hv : v ≤ N) (a : Fin N → A) :
    |markedSpineSum b d hv a-(∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height d.val v| ≤
      |markedSpineSum (markedTrunc m b) d hv a-
        (∫ z,∫ a,markedTrunc m b z a ∂κ z.1 ∂p.spineLaw)*height d.val v|+
      |codeSpineSum (fun z => (z.1:ℝ)) d v-(p.variance+1)*height d.val v|+
      |codeSpineSum (spineTrunc m (fun z => (z.1:ℝ))) d v-
        (∫ z,spineTrunc m (fun z => (z.1:ℝ)) z ∂p.spineLaw)*height d.val v|+
      2*(∫ z,spineTail m z ∂p.spineLaw)*height d.val v := by
  let bm := fun z => ∫ a,b z a ∂κ z.1
  have hbm : ∀ z,|bm z| ≤ z.1 := by
    intro z
    have hh := norm_integral_le_of_norm_le_const (μ := κ z.1) (f := b z) (C := (z.1:ℝ))
      (ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using hb z a))
    simpa [bm,Real.norm_eq_abs,Measure.real] using hh
  let h : ℝ := height d.val v
  have h0 : 0 ≤ h := by dsimp [h]; positivity
  have hd := markedSpineSum_abs_dom (fun z a => b z a-markedTrunc m b z a) (spineTail m)
    (fun z a => spineTrunc_tail_bound m (fun z => b z a) (fun z => hb z a) z) d hv a
  rw [markedSpineSum_sub] at hd
  have he := p.spineTrunc_integral_error m bm hbm
  have hmean : (fun z => ∫ a,markedTrunc m b z a ∂κ z.1)=spineTrunc m bm := by
    funext z; exact markedTrunc_mean κ m b z
  have hi : (∫ z,spineTail m z ∂p.spineLaw)=p.variance+1-
      ∫ z,spineTrunc m (fun z => (z.1:ℝ)) z ∂p.spineLaw := by
    rw [spineTail_eq,integral_sub p.spine_integrable_fst (p.spine_integrable_dom _ (fun z => by
      unfold spineTrunc; split_ifs <;> simp)),p.spine_integral_fst]
  have hs : codeSpineSum (spineTail m) d v=codeSpineSum (fun z => (z.1:ℝ)) d v-
      codeSpineSum (spineTrunc m (fun z => (z.1:ℝ))) d v := by rw [spineTail_eq,codeSpineSum_sub]
  rw [hmean]
  change |markedSpineSum b d hv a-(∫ z,bm z ∂p.spineLaw)*h| ≤
    |markedSpineSum (markedTrunc m b) d hv a-(∫ z,spineTrunc m bm z ∂p.spineLaw)*h|+_+_+_
  have he1 := abs_add_le (markedSpineSum (markedTrunc m b) d hv a-(∫ z,spineTrunc m bm z ∂p.spineLaw)*h)
    ((markedSpineSum b d hv a-markedSpineSum (markedTrunc m b) d hv a)-
      ((∫ z,bm z ∂p.spineLaw)-(∫ z,spineTrunc m bm z ∂p.spineLaw))*h)
  have he2 := abs_sub (markedSpineSum b d hv a-markedSpineSum (markedTrunc m b) d hv a)
      (((∫ z,bm z ∂p.spineLaw)-(∫ z,spineTrunc m bm z ∂p.spineLaw))*h)
  rw [abs_mul,abs_of_nonneg h0] at he2
  have he3 := mul_le_mul_of_nonneg_right he h0
  have hsum : markedSpineSum (markedTrunc m b) d hv a-(∫ z,spineTrunc m bm z ∂p.spineLaw)*h+
    ((markedSpineSum b d hv a-markedSpineSum (markedTrunc m b) d hv a)-
      ((∫ z,bm z ∂p.spineLaw)-(∫ z,spineTrunc m bm z ∂p.spineLaw))*h)=
    markedSpineSum b d hv a-(∫ z,bm z ∂p.spineLaw)*h := by ring
  rw [hs] at hd
  rw [hsum] at he1
  have hK := le_abs_self (codeSpineSum (fun z => (z.1:ℝ)) d v-(p.variance+1)*h)
  have hk := neg_le_abs (codeSpineSum (spineTrunc m (fun z => (z.1:ℝ))) d v-
    (∫ z,spineTrunc m (fun z => (z.1:ℝ)) z ∂p.spineLaw)*h)
  nlinarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- The source's full uniform marked ancestral theorem, under the actual conditional
independent-mark law, with only the offspring second moment. -/
theorem CriticalEvenOffspring.uniform_integrable_marked_spine (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {A : Type*} [MeasurableSpace A] (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hbmeas : ∀ z,Measurable (b z)) (hb : ∀ z a,|b z a| ≤ z.1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (p.markedCodeLaw κ n).real {x | ∃ v : Fin (2*n+1),
      ε*Real.sqrt ((2*n+1:ℕ):ℝ) < |markedSpineSum b x.1 v.isLt.le x.2-
        (∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|})
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ =>  ha.trans_le measureReal_nonneg)
  intro η hη
  obtain ⟨C,hC,hheight⟩ := p.code_height_tight hB (by positivity : 0 < η/4)
  obtain ⟨m,hm⟩ := (p.spine_tail_integral_tendsto.eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < ε/(8*C)))).exists
  have ht0 : 0 ≤ ∫ z,spineTail m z ∂p.spineLaw := integral_nonneg (spineTail_nonneg m)
  have hK := p.uniform_degree_spine_limit hB (by positivity : 0 < ε/4)
  have hbR := p.uniform_bounded_marked_spine hB κ (markedTrunc m b)
    (measurable_markedTrunc m b hbmeas) (R := (m:ℝ)+1) (by positivity)
    (fun z a => (markedTrunc_bound m b hb z a).trans (by linarith))
    (by positivity : 0 < ε/4)
  have hkR := p.uniform_bounded_spine_limit hB (spineTrunc m (fun z =>  (z.1:ℝ)))
    (R := (m:ℝ)+1) (by positivity) (fun z => 
      (spineTrunc_bound m (fun z =>  (z.1:ℝ)) (fun z =>  by simp) z).trans (by linarith))
    (by positivity : 0 < ε/4)
  filter_upwards [hheight,hK.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/4)),
    hbR.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/4)),
    hkR.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/4))] with n hh hK hbR hkR
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let A0 := {d : Code N | ∃ v ≤ N,C*s < height d.val v}
  let A1 := {d : Code N | ∃ v < N,(ε/4)*s < 
    |codeSpineSum (fun z =>  (z.1:ℝ)) d v-(p.variance+1)*height d.val v|}
  let A2 := {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),(ε/4)*s <
    |markedSpineSum (markedTrunc m b) x.1 (Nat.le_of_lt_succ v.isLt) x.2-
      (∫ z,∫ a,markedTrunc m b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|}
  let A3 := {d : Code N | ∃ v ≤ N,(ε/4)*s < 
    |codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) d v-
      (∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw)*height d.val v|}
  have hsub : {x : Code N × (Fin N → A) | ∃ v : Fin N,ε*s <
      |markedSpineSum b x.1 v.isLt.le x.2-(∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|}
      ⊆ ((Prod.fst ⁻¹' A0)∪(Prod.fst ⁻¹' A1))∪(A2∪(Prod.fst ⁻¹' A3)) := by
    rintro x ⟨v,hbad⟩
    by_contra hn
    simp only [Set.mem_union,not_or] at hn
    have hhv : (height x.1.val v.val:ℝ) ≤ C*s := by
      by_contra h; exact hn.1.1 ⟨v.val,v.isLt.le,lt_of_not_ge h⟩
    have hKv : |codeSpineSum (fun z =>  (z.1:ℝ)) x.1 v.val-(p.variance+1)*height x.1.val v.val| ≤ (ε/4)*s := by
      by_contra h; exact hn.1.2 ⟨v.val,v.isLt,lt_of_not_ge h⟩
    have hbv : |markedSpineSum (markedTrunc m b) x.1 v.isLt.le x.2-
        (∫ z,∫ a,markedTrunc m b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val| ≤ (ε/4)*s := by
      by_contra h; exact hn.2.1 ⟨⟨v.val,by omega⟩,lt_of_not_ge h⟩
    have hkv : |codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) x.1 v.val-
        (∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw)*height x.1.val v.val| ≤ (ε/4)*s := by
      by_contra h; exact hn.2.2 ⟨v.val,v.isLt.le,lt_of_not_ge h⟩
    have ht : 2*(∫ z,spineTail m z ∂p.spineLaw)*height x.1.val v.val ≤ (ε/4)*s := by
      have hm' : (∫ z,spineTail m z ∂p.spineLaw)*(8*C) ≤ ε := (le_div_iff₀ (by positivity)).mp hm.le
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have h1 := mul_le_mul_of_nonneg_left hhv (show 0 ≤ 2*(∫ z,spineTail m z ∂p.spineLaw) by positivity)
      have h2 := mul_le_mul_of_nonneg_right hm' hs
      nlinarith
    have hc := marked_spine_tail_control p κ x.1 b hb m v.isLt.le x.2
    linarith
  have hprob : (p.markedCodeLaw κ n).real {x : Code N × (Fin N → A) | ∃ v : Fin N,ε*s <
        |markedSpineSum b x.1 v.isLt.le x.2-(∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|} ≤
      (p.codeLaw n).real A0+(p.codeLaw n).real A1+(p.markedCodeLaw κ n).real A2+(p.codeLaw n).real A3 := by
    apply (measureReal_mono hsub).trans
    have h01 := measureReal_union_le (μ := p.markedCodeLaw κ n) (Prod.fst ⁻¹' A0) (Prod.fst ⁻¹' A1)
    have h23 := measureReal_union_le (μ := p.markedCodeLaw κ n) A2 (Prod.fst ⁻¹' A3)
    have htop := measureReal_union_le (μ := p.markedCodeLaw κ n)
      ((Prod.fst ⁻¹' A0)∪(Prod.fst ⁻¹' A1)) (A2∪(Prod.fst ⁻¹' A3))
    rw [p.markedCodeLaw_fst,p.markedCodeLaw_fst] at h01
    rw [p.markedCodeLaw_fst] at h23
    linarith
  change (p.codeLaw n).real A0 ≤ η/4 at hh
  change (p.codeLaw n).real A1 < η/4 at hK
  change (p.markedCodeLaw κ n).real A2 < η/4 at hbR
  change (p.codeLaw n).real A3 < η/4 at hkR
  exact hprob.trans_lt (by linarith)

end FKCRT.TreeCoding
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

/-- Actual all-core labels satisfy the previously proved marked finite-variance
uniform ancestral law, not a bounded-size or exponential-moment substitute. -/
theorem actual_uniform_metric_spine (P : Parameters)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => ((actualOffspring P).markedCodeLaw
      (fun k => (CoreLabel.markLaw P k).toMeasure) n).real {x | ∃ v : Fin (2*n+1),
        ε*Real.sqrt ((2*n+1:ℕ):ℝ) < |markedSpineSum coreIncrement x.1 v.isLt.le x.2-
          metricMean P*height x.1.val v.val|}) atTop (𝓝 0) :=
  (actualOffspring P).uniform_integrable_marked_spine hB
    (fun k => (CoreLabel.markLaw P k).toMeasure) coreIncrement (fun _ => measurable_of_countable _)
    coreIncrement_bound hε

end FKCRT.Inventory
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

lemma maxDegree_le_iff (t : CoreTree) (K : ℕ) :
    t.maxDegree ≤ K ↔ ∀ a∈t.labels,a.arity ≤ K := by
  induction t with
  | leaf => simp [maxDegree,labels,CoreLabel.arity]
  | branch c ts ih =>
    simp only [maxDegree,max_le_iff,Finset.sup_le_iff,Finset.mem_univ,forall_true_left,ih]
    rw [labels_branch]
    simp only [List.mem_cons,List.mem_flatMap,List.mem_ofFn,forall_eq_or_imp,
      CoreLabel.arity]
    constructor
    · rintro ⟨hc,ht⟩
      refine ⟨hc,?_⟩
      rintro a ⟨l,⟨i,rfl⟩,ha⟩
      exact ht i a ha
    · rintro ⟨hc,ht⟩
      exact ⟨hc,fun i a ha => ht a ⟨_,⟨i,rfl⟩,ha⟩⟩

lemma maxDegree_le_ofMarkedCode {N : ℕ} (x : MarkedCode N) :
    (ofMarkedCode x).maxDegree ≤ Finset.univ.sup (fun i => (x.val.1.val i).val) := by
  rw [maxDegree_le_iff,ofMarkedCode_labels]
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  rw [x.property i]
  exact Finset.le_sup (f := fun i => (x.val.1.val i).val) (Finset.mem_univ i)

lemma maxDegree_large_ofMarkedCode {N : ℕ} (x : MarkedCode N) {R : ℝ}
    (hR : 0 ≤ R) (h : R<((ofMarkedCode x).maxDegree:ℝ)) :
    ∃ i,R<((x.val.1.val i).val:ℝ) := by
  by_contra hh
  push Not at hh
  have hb : (↑(Finset.univ.sup (fun i => (x.val.1.val i).val) : ℕ):ℝ) ≤ R := by
    apply Finset.sup_induction (p := fun v : ℕ => (v:ℝ) ≤ R) (by simpa using hR)
    · intro a ha b hb
      rw [Nat.cast_max]
      exact max_le ha hb
    · intro i _
      exact hh i
  have hm : ((ofMarkedCode x).maxDegree:ℝ) ≤ (↑(Finset.univ.sup (fun i => (x.val.1.val i).val) : ℕ):ℝ) :=
    Nat.cast_le.mpr (maxDegree_le_ofMarkedCode x)
  linarith

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable
lemma CriticalEvenOffspring.code_event_probability (p : CriticalEvenOffspring) (n : ℕ)
    (E : (Fin (2*n+1) → Fin (2*n+1)) → Prop) :
    (p.codeLaw n).real {d | E d.val}=codeEventProbability p (2*n+1) E := by
  rw [← integral_indicator_one (μ := p.codeLaw n) (show MeasurableSet {d | E d.val} from trivial),p.code_integral]
  unfold codeEventProbability codeEventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : E d.val <;> simp [Set.indicator,h]

lemma CriticalEvenOffspring.actual_max_degree (p : CriticalEvenOffspring) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real
      {d | ∃ i,ε*Real.sqrt ((2*n+1:ℕ):ℝ)<((d.val i).val:ℝ)}) atTop (𝓝 0) := by
  have h := p.conditioned_max_degree ε hε
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [p.code_event_probability n (fun d => ∃ i,ε*Real.sqrt ((2*n+1:ℕ):ℝ)<((d i).val:ℝ))]
  congr 2
  norm_cast
end FKCRT.TreeCoding
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- The actual largest core has vanishing square-root scale, under the
original compatible marked law. Impossible marks are not sampled. -/
theorem actual_max_core (P : Parameters) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => ((actualOffspring P).markedCodeLaw
      (fun k => (CoreLabel.markLaw P k).toMeasure) n).real
      {x | ∃ h : ∀ i,(x.2 i).arity=(x.1.val i).val,
        ε*Real.sqrt ((2*n+1:ℕ):ℝ)<((CoreTree.ofMarkedCode ⟨x,h⟩).maxDegree:ℝ)}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ((actualOffspring P).actual_max_degree hε)
  intro n
  rw [← (actualOffspring P).markedCodeLaw_fst (fun k => (CoreLabel.markLaw P k).toMeasure)]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx
  obtain ⟨h,hx⟩ := hx
  exact CoreTree.maxDegree_large_ofMarkedCode ⟨x,h⟩ (by positivity) hx
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
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- A compact-cover transfer lemma for varying discrete approximations. The
local hypothesis is deterministic; only the stated error events vanish in
probability. No independent coupling or random-cut independence is used. -/
theorem local_probability_transfer {E Ω' : Type*} {Ω : ℕ → Type*}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    [∀ n,MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n,Measure (Ω n)} {ν : Measure Ω'} [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n,Ω n → E} {Z : Ω' → E} (h : TendstoInDistribution X atTop Z μ ν)
    (hm : ∀ n,Measurable (X n)) (Y : ∀ n,Ω n → ℝ) (G : E → ℝ)
    (Bad : ∀ n,ℝ → Set (Ω n))
    (hBad : ∀ a,0<a → Tendsto (fun n => (μ n).real (Bad n a)) atTop (𝓝 0))
    (hloc : ∀ ε,0<ε → ∀ f : E,∃ r : ℝ,0 < r ∧ ∃ a : ℝ,0<a ∧ ∃ N : ℕ,
      ∀ n≥N,∀ x : Ω n,dist (X n x) f < r → x∉Bad n a → |Y n x-G (X n x)| ≤ ε) :
    ∀ ε,0<ε → Tendsto (fun n => (μ n).real {x | ε < |Y n x-G (X n x)|}) atTop (𝓝 0) := by
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  have : IsProbabilityMeasure (ν.map Z) := Measure.isProbabilityMeasure_map h.aemeasurable_limit
  obtain ⟨K,hK,hKμ⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := ν.map Z)) (ENNReal.ofReal (η/4)) (ENNReal.ofReal_pos.mpr (by positivity))
  have hKμ' := hKμ (ν.map Z) (Set.mem_singleton _)
  choose r hr a ha N hfit using hloc ε hε
  obtain ⟨S,hSK,hS,hcover⟩ := hK.elim_finite_subcover_image
    (fun f (_ : f∈K) => Metric.isOpen_ball (x := f) (ε := r f)) (by
      intro f hf
      simp only [Set.mem_iUnion]
      exact ⟨f,hf,Metric.mem_ball_self (hr f)⟩)
  let I := hS.toFinset
  let O : Set E := ⋃ f∈I,Metric.ball f (r f)
  have hO : IsOpen O := isOpen_iUnion (fun f => isOpen_iUnion (fun _ => Metric.isOpen_ball))
  have hKO : K⊆O := by simpa only [O,I,Set.Finite.mem_toFinset] using hcover
  have hclosed := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hO.isClosed_compl
  have hlim : limsup (fun n => (μ n) ((X n) ⁻¹' Oᶜ)) atTop≤ENNReal.ofReal (η/4) := by
    simpa only [ProbabilityMeasure.coe_mk,Measure.map_apply (hm _) hO.measurableSet.compl] using
      hclosed.trans ((measure_mono (Set.compl_subset_compl.mpr hKO)).trans hKμ')
  have hev : ∀ᶠ n in atTop,(μ n).real ((X n) ⁻¹' Oᶜ)<η/2 := by
    have hh : ∀ᶠ n in atTop,(μ n) ((X n) ⁻¹' Oᶜ)<ENNReal.ofReal (η/2) :=
      eventually_lt_of_limsup_lt (hlim.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (half_pos hη)).mpr (by linarith)))
    filter_upwards [hh] with n hn
    rw [← ofReal_measureReal] at hn
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hn
  have hsum : Tendsto (fun n => ∑ f∈I,(μ n).real (Bad n (a f))) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum I (fun f _ => hBad (a f) (ha f))
  have hN : ∀ᶠ n in atTop,∀ f∈I,N f≤n := by
    exact (eventually_all_finset I).mpr (fun f _ => eventually_ge_atTop (N f))
  filter_upwards [hev,hsum.eventually (gt_mem_nhds (half_pos hη)),hN] with n hn hn' hNn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  have hs : {x | ε < |Y n x-G (X n x)|}⊆(X n) ⁻¹' Oᶜ ∪ ⋃ f∈I,Bad n (a f) := by
    intro x hx
    by_cases hxO : X n x∈O
    · right
      obtain ⟨f,hf,hxf⟩ := Set.mem_iUnion₂.mp hxO
      apply Set.mem_iUnion₂.mpr
      refine ⟨f,hf,?_⟩
      by_contra hbad
      exact not_lt_of_ge (hfit f n (hNn f hf) x hxf hbad) hx
    · exact Or.inl hxO
  have hh := (measureReal_mono (μ := μ n) hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add le_rfl (measureReal_biUnion_finset_le I (fun f => Bad n (a f)))))
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma metricBad_limit (P : Parameters)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) {a : ℝ} (ha : 0<a) :
    Tendsto (fun n => (actualDrawLaw P n).real (metricBad P n a)) atTop (𝓝 0) := by
  have hcore := (actual_max_core P ha).comp (tendsto_add_atTop_nat 1)
  have herr := (actual_uniform_metric_spine P hB ha).comp (tendsto_add_atTop_nat 1)
  have ht := hcore.add herr
  simp only [zero_add] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  have hc : (actualDrawLaw P n).real {x | ¬∀ i,(x.2 i).arity=(x.1.val i).val}=0 := by
    unfold Measure.real
    rw [ae_iff.mp (actual_marked_compatible P (n+1)),ENNReal.toReal_zero]
  apply (measureReal_union_le _ _).trans
  apply add_le_add _ le_rfl
  apply (measureReal_union_le _ _).trans
  rw [hc,zero_add]
  exact le_rfl

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
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable
attribute [local instance] OAI.FKCRT.Inventory.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_1
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_1 : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

/-- The original map observable converges under its exact marked code law. -/
theorem actual_map_tests_oai (P : Parameters)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) μ)
    (hI : iIndepFun (fun i ω t => B i t ω) μ)
    (F : FKCRT.MetricMeasureData → ℝ) (hF : FKCRT.IsGHPTest F) :
    Tendsto (fun n => ∫ x,FKCRT.markedMapTest (edgeScale P n) n F x ∂actualDrawLaw P n)
      atTop (𝓝 (FKCRT.brownianExpectation μ B F)) := by
  have hp := local_probability_transfer (actualHeight_CLT P hB hI)
    (fun _ => measurable_of_countable _) (fun n => FKCRT.markedMapTest (edgeScale P n) n F)
    (fun f => F (FKCRT.treeSpace f)) (metricBad P)
    (fun a ha => metricBad_limit P (hB 0) ha) (metric_test_local P F hF)
  have hh := (actualHeight_CLT P hB hI).continuous_comp hF.continuous_treeSpace
  have hy : TendstoInDistribution (fun n => FKCRT.markedMapTest (edgeScale P n) n F) atTop
      (fun ω => F (FKCRT.treeSpace (excursionPath B ω))) (actualDrawLaw P) μ := by
    apply tendstoInDistribution_of_close hh (fun _ => (measurable_of_countable _).aemeasurable)
    intro ε hε
    simpa only [Function.comp_def,Real.dist_eq,abs_sub_comm] using hp ε hε
  obtain ⟨C,hC⟩ := hF.1
  have hC0 : 0≤C := (abs_nonneg (F (FKCRT.treeSpace (0 : C(unitInterval,ℝ))))).trans (hC _)
  let clip : ℝ → ℝ := fun x => max (-C) (min C x)
  have hclip : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hclipB : ∀ x,‖clip x‖≤C := by
    intro x
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
  have hclipId : ∀ x,|x|≤C → clip x=x := by
    intro x hx
    rw [abs_le] at hx
    exact max_eq_right (hx.1.trans_eq (min_eq_right hx.2).symm) |>.trans (min_eq_right hx.2)
  have hY : ∀ n x,clip (FKCRT.markedMapTest (edgeScale P n) n F x)=
      FKCRT.markedMapTest (edgeScale P n) n F x := by
    intro n x
    apply hclipId
    unfold FKCRT.markedMapTest
    split
    · exact hC _
    · simpa only [abs_zero] using hC0
  have hz : ∀ ω,clip (F (FKCRT.treeSpace (excursionPath B ω)))=F (FKCRT.treeSpace (excursionPath B ω)) :=
    fun _ => hclipId _ (hC _)
  have hi := integral_tendsto_of_tendstoInDistribution hy hclip hclipB
  simp only [hY,hz] at hi
  have he : (fun ω => F (FKCRT.treeSpace (excursionPath B ω)))=ᵐ[μ]
      (fun ω => F (FKCRT.treeSpace (FKCRT.standardExcursion B ω))) := by
    filter_upwards [excursionPath_ae_eq hB] with ω hω
    exact congrArg (fun e => F (FKCRT.treeSpace e)) hω
  simpa only [integral_congr_ae he,FKCRT.brownianExpectation] using hi

end FKCRT.Inventory
end

end OAI
end

theorem solution : type_of% @OAI.FKCRT.Inventory.actual_map_tests_oai := @OAI.FKCRT.Inventory.actual_map_tests_oai
