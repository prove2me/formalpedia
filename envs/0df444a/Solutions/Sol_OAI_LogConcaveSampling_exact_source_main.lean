-- Prove2me | solution 1 for OAI.LogConcaveSampling.exact_source_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:42:16.599683+00:00
-- url     : https://prove2.me/submissions/4b380be1-2bdd-428a-8812-73237b082fa3

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_eventually_subpolynomial_sampler

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ContinuousFirstOrderReply
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling

theorem Admissible.continuous_firstOrderReply {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : Continuous (firstOrderReply V) := by
  have hg : Continuous (gradient V) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hV.smooth.continuous_fderiv (by norm_num))
  exact hV.smooth.continuous.prodMk hg

theorem OracleAlgorithm.measurable_history {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) {V : Point d → ℝ} (hV : Admissible V) (n : ℕ) :
    Measurable (fun ω => A.history V ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      by_cases hn : n < q
      · have hr : Measurable (fun ω =>
            firstOrderReply V (A.query ⟨n, hn⟩ (ω, A.history V ω n))) :=
          hV.continuous_firstOrderReply.measurable.comp
            ((A.query_measurable ⟨n, hn⟩).comp (measurable_id.prodMk ih))
        apply Measurable.of_eval
        intro i
        by_cases hi : i = ⟨n, hn⟩
        · simpa [history, hn, Function.update_apply, hi] using hr
        · simpa [history, hn, Function.update_apply, hi, Function.comp_def] using
            (measurable_pi_apply i).comp ih
      · simpa [history, hn] using ih

theorem OracleAlgorithm.measurable_run {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) {V : Point d → ℝ} (hV : Admissible V) :
    Measurable (A.run V) :=
  A.output_measurable.comp (measurable_id.prodMk (A.measurable_history hV q))

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem Admissible.contDiff_gradient {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : ContDiff ℝ 1 (gradient V) := by
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
    (hV.smooth.fderiv_right (by norm_num))

theorem Admissible.quadratic_bounds {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) :
    ‖x‖ ^ 2 / 2 ≤ V x ∧ V x ≤ ‖x‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => V (t • x)
  let g : ℝ → ℝ := fun t => inner ℝ x (gradient V (t • x))
  let h : ℝ → ℝ := fun t => inner ℝ x (fderiv ℝ (gradient V) (t • x) x)
  have hp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • x) x t := fun t => by
    simpa using (hasDerivAt_id t).smul_const x
  have hdg := hV.contDiff_gradient.differentiable (by norm_num)
  have hf : ∀ t, HasDerivAt f (g t) t := by
    intro t
    have hh := ((hV.smooth.differentiable (by norm_num) (t • x)).hasFDerivAt).comp_hasDerivAt t (hp t)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    change inner ℝ x (gradient V (t • x)) = fderiv ℝ V (t • x) x
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (t • x)).hasFDerivAt.comp_hasDerivAt t (hp t)
    simpa [g, h, Function.comp_def] using
      (hasDerivAt_const t x).inner ℝ hh
  have ht := quadratic_bounds_of_hasDerivAt hf hg
    (fun t => hV.hessian_bounds (t • x) x)
  dsimp only [f, g] at ht
  rw [zero_smul, one_smul, hV.value_zero, hV.gradient_zero, inner_zero_right, zero_add] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem Admissible.integrable_exp_neg {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : Integrable (fun x => Real.exp (-V x)) := by
  apply (integrable_gaussian_envelope d (b := 1 / 2) (by norm_num)).mono'
    ((Real.continuous_exp.comp hV.smooth.continuous.neg).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply, Pi.neg_apply]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (hV.quadratic_bounds x).1
    linarith

theorem Admissible.partition_ne_top {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : partition V ≠ ⊤ := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    hV.integrable_exp_neg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-V x)).le)).2
      hV.integrable_exp_neg

theorem Admissible.partition_pos {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : 0 < partition V := by
  have hm : Measurable (gibbsDensity V) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hV.smooth.continuous.neg)).measurable
  rw [partition, lintegral_pos_iff_support hm]
  have hs : Function.support (gibbsDensity V) = Set.univ := by
    ext x
    simp [Function.mem_support, gibbsDensity, not_le_of_gt (Real.exp_pos (-V x))]
  rw [hs]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

theorem Admissible.isProbabilityMeasure_gibbs {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : IsProbabilityMeasure (gibbs V) := by
  constructor
  rw [gibbs, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hV.partition_pos.ne' hV.partition_ne_top

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_UnitUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling

lemma pi_snoc_law {X : Type*} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => ν)).prod ν).map (fun p => Fin.snoc (α := fun _ : Fin (n+1) => X) p.1 p.2) =
      Measure.pi (fun _ : Fin (n+1) => ν) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm.map_eq
  have hs := Measure.prod_swap (μ := Measure.pi (fun _ : Fin n => ν)) (ν := ν)
  rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext p
  exact (Fin.insertNth_last' p.2 p.1).symm

end LogConcaveSampling

namespace LogConcaveSampling
open ProbabilityTheory

lemma unitUniform_Iic {a : ℝ} (_ha : 0 ≤ a) (ha' : a ≤ 1) :
    unitUniform (Set.Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_apply measurableSet_Iic]
  have hh : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 a := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Icc]
    constructor
    · intro hx; exact ⟨hx.2.1,hx.1⟩
    · intro hx; exact ⟨hx.2,hx.1,hx.2.trans ha'⟩
  rw [hh,Real.volume_Icc,sub_zero]

variable {E : Type*} [MeasurableSpace E]

lemma measurable_acceptanceEvent {a : E → ℝ} (ha : Measurable a) :
    MeasurableSet (acceptanceEvent a) := measurableSet_le measurable_snd (ha.comp measurable_fst)

theorem accepted_measure (ν : Measure E) [IsProbabilityMeasure ν] {a : E → ℝ}
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1) :
    (((ν.prod unitUniform).restrict (acceptanceEvent a)).map Prod.fst) =
      ν.withDensity (fun x => ENNReal.ofReal (a x)) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (hs.preimage measurable_fst),
    Measure.prod_apply ((hs.preimage measurable_fst).inter (measurable_acceptanceEvent ha)),
    withDensity_apply _ hs]
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' s ∩ acceptanceEvent a) = Set.Iic (a x) := by
      ext t
      simp [acceptanceEvent,hx]
    rw [he]
    exact unitUniform_Iic (ha0 x) (ha1 x)
  · have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' s ∩ acceptanceEvent a) = ∅ := by
      ext t
      simp [acceptanceEvent,hx]
    rw [he,measure_empty,Set.indicator_of_notMem hx]

omit [MeasurableSpace E] in
lemma rejectionPick_snoc (a : E → ℝ) (fallback : E) (n : ℕ) (tape : Fin n → E × ℝ) (z : E × ℝ) :
    rejectionPick a fallback (n+1) (Fin.snoc tape z) =
      if z.2 ≤ a z.1 then z.1 else rejectionPick a fallback n tape := by
  simp only [rejectionPick,Fin.snoc_last,Fin.snoc_castSucc]

theorem rejection_law_succ (ν : Measure E) [IsProbabilityMeasure ν] {a : E → ℝ}
    (ha : Measurable a) (fallback : E) (n : ℕ) :
    (Measure.pi (fun _ : Fin (n+1) => ν.prod unitUniform)).map (rejectionPick a fallback (n+1)) =
      (((ν.prod unitUniform).restrict (acceptanceEvent a)).map Prod.fst) +
      ((ν.prod unitUniform) (acceptanceEvent a)ᶜ) •
        (Measure.pi (fun _ : Fin n => ν.prod unitUniform)).map (rejectionPick a fallback n) := by
  rw [← pi_snoc_law (ν.prod unitUniform) n,
    Measure.map_map (measurable_rejectionPick ha fallback (n+1)) (measurable_fin_snoc n)]
  ext s hs
  rw [Measure.map_apply ((measurable_rejectionPick ha fallback (n+1)).comp (measurable_fin_snoc n)) hs,
    Measure.add_apply,Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (hs.preimage measurable_fst),Measure.smul_apply,
    Measure.map_apply (measurable_rejectionPick ha fallback n) hs,smul_eq_mul]
  have he : (rejectionPick a fallback (n+1) ∘ (fun p => Fin.snoc p.1 p.2)) ⁻¹' s =
      (Set.univ ×ˢ (Prod.fst ⁻¹' s ∩ acceptanceEvent a)) ∪
      ((rejectionPick a fallback n ⁻¹' s) ×ˢ (acceptanceEvent a)ᶜ) := by
    ext ⟨t,z⟩
    simp only [Set.mem_preimage,Function.comp_apply,rejectionPick_snoc,Set.mem_union,
      Set.mem_prod,Set.mem_univ,true_and,Set.mem_inter_iff,Set.mem_compl_iff,acceptanceEvent,Set.mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he,measure_union]
  · rw [Measure.prod_prod,Measure.prod_prod,measure_univ,one_mul,mul_comm]
  · apply Set.disjoint_left.mpr
    rintro p ⟨_,_,hp⟩ ⟨_,hn⟩
    exact hn hp
  · exact (hs.preimage (measurable_rejectionPick ha fallback n)).prod (measurable_acceptanceEvent ha).compl

lemma rejection_failure_mass (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {a : E → ℝ} (ha : Measurable a) {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (hacc : (((ν.prod unitUniform).restrict (acceptanceEvent a)).map Prod.fst) =
      ENNReal.ofReal p • μ) :
    (ν.prod unitUniform) (acceptanceEvent a)ᶜ = ENNReal.ofReal (1-p) := by
  have he : (ν.prod unitUniform) (acceptanceEvent a) = ENNReal.ofReal p := by
    have hh := congrArg (fun η : Measure E => η Set.univ) hacc
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,Set.preimage_univ,
      Measure.restrict_apply_univ,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using hh
  rw [measure_compl (measurable_acceptanceEvent ha) (measure_ne_top _ _),measure_univ,he]
  exact by simpa using (ENNReal.ofReal_sub 1 hp0).symm

theorem capped_rejection_tv (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {a : E → ℝ} (ha : Measurable a) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hacc : (((ν.prod unitUniform).restrict (acceptanceEvent a)).map Prod.fst) =
      ENNReal.ofReal p • μ) (fallback : E) (n : ℕ) :
    TVAtMost ((Measure.pi (fun _ : Fin n => ν.prod unitUniform)).map
      (rejectionPick a fallback n)) μ ((1-p)^n) := by
  let out := fun n => (Measure.pi (fun _ : Fin n => ν.prod unitUniform)).map
    (rejectionPick a fallback n)
  have ho : ∀ n, IsProbabilityMeasure (out n) := fun n => Measure.isProbabilityMeasure_map (measurable_rejectionPick ha fallback n).aemeasurable
  have hor : ∀ n s, 0 ≤ (out n).real s ∧ (out n).real s ≤ 1 := by
    intro n s
    have := ho n
    exact ⟨measureReal_nonneg,measureReal_le_one⟩
  have hμr : ∀ s, 0 ≤ μ.real s ∧ μ.real s ≤ 1 := fun s =>
    ⟨measureReal_nonneg,measureReal_le_one⟩
  have hrec : ∀ n s, MeasurableSet s →
      (out (n+1)).real s = p * μ.real s + (1-p) * (out n).real s := by
    intro n s _
    have he := rejection_law_succ ν ha fallback n
    rw [hacc,rejection_failure_mass ν μ ha hp0 hp1 hacc] at he
    change (out (n+1)) = _ at he
    rw [he,Measure.real,Measure.add_apply,ENNReal.toReal_add]
    · simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hp0,ENNReal.toReal_ofReal (sub_nonneg.mpr hp1),Measure.real]
      rfl
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · have := ho n
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  intro s hs
  change |(out n).real s-μ.real s| ≤ _
  induction n with
  | zero =>
      simpa only [pow_zero] using (abs_sub_le_iff.mpr
        ⟨by linarith [(hor 0 s).2,(hμr s).1],by linarith [(hor 0 s).1,(hμr s).2]⟩)
  | succ n ih =>
      rw [hrec n s hs]
      have he : p*μ.real s+(1-p)*(out n).real s-μ.real s =
          (1-p)*((out n).real s-μ.real s) := by ring
      rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hp1),pow_succ']
      exact mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianProposalPotential
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma gaussianProposalPotential_eq (d : ℕ) (x : Point d) :
    gaussianProposalPotential d x = ‖x‖^2/2 := by
  simp [gaussianProposalPotential]

lemma partition_comparison {d : ℕ} {V : Point d → ℝ} (hV : Admissible V) :
    (2:ℝ)^(- (d:ℤ)) * (partition (gaussianProposalPotential d)).toReal ≤
      (partition V).toReal ∧
    (partition V).toReal ≤ (partition (gaussianProposalPotential d)).toReal := by
  have hB := gaussianProposalPotential_admissible d
  rw [partition_toReal hV.integrable_exp_neg,partition_toReal hB.integrable_exp_neg]
  constructor
  · have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure (Point d))
      (fun x => Real.exp (-gaussianProposalPotential d x)) (2:ℝ) (hR := by norm_num)
    simp only [finrank_euclideanSpace_fin,smul_eq_mul] at hs
    have hh : Integrable (fun x : Point d => Real.exp (-gaussianProposalPotential d ((2:ℝ) • x))) := by
      convert integrable_gaussian_envelope d (b := 2) (by norm_num) using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      rw [gaussianProposalPotential_eq,norm_smul,Real.norm_of_nonneg (by norm_num)]
      congr 1
      ring
    rw [zpow_neg,zpow_natCast,← hs]
    apply integral_mono hh hV.integrable_exp_neg
    intro x
    apply Real.exp_le_exp.mpr
    rw [gaussianProposalPotential_eq,norm_smul,Real.norm_of_nonneg (by norm_num)]
    have ht := (hV.quadratic_bounds x).2
    nlinarith [sq_nonneg ‖x‖]
  · apply integral_mono hV.integrable_exp_neg hB.integrable_exp_neg
    intro x
    apply Real.exp_le_exp.mpr
    rw [gaussianProposalPotential_eq]
    linarith [(hV.quadratic_bounds x).1]

lemma gaussianAcceptance_bounds {d : ℕ} {V : Point d → ℝ} (hV : Admissible V) (x : Point d) :
    0 ≤ gaussianAcceptance V x ∧ gaussianAcceptance V x ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  apply Real.exp_le_one_iff.mpr
  rw [gaussianProposalPotential_eq]
  linarith [(hV.quadratic_bounds x).1]

lemma gaussian_accepted_measure {d : ℕ} {V : Point d → ℝ} (hV : Admissible V) :
    (((gibbs (gaussianProposalPotential d)).prod unitUniform).restrict
      (acceptanceEvent (gaussianAcceptance V))).map Prod.fst =
      ENNReal.ofReal ((partition V).toReal/(partition (gaussianProposalPotential d)).toReal) • gibbs V := by
  have hB := gaussianProposalPotential_admissible d
  have := hB.isProbabilityMeasure_gibbs
  rw [accepted_measure _ (measurable_gaussianAcceptance hV)
    (fun x => (gaussianAcceptance_bounds hV x).1) (fun x => (gaussianAcceptance_bounds hV x).2)]
  rw [gibbs,withDensity_smul_measure,← withDensity_mul]
  · have he : gibbsDensity (gaussianProposalPotential d) *
        (fun x => ENNReal.ofReal (gaussianAcceptance V x)) = gibbsDensity V := by
      funext x
      simp only [Pi.mul_apply,gibbsDensity,gaussianAcceptance,← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 2
      ring
    rw [he,gibbs,smul_smul]
    congr 1
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hB.partition_pos.ne' hB.partition_ne_top),
      ENNReal.ofReal_toReal hV.partition_ne_top,ENNReal.ofReal_toReal hB.partition_ne_top,div_eq_mul_inv]
    rw [mul_right_comm,ENNReal.mul_inv_cancel hV.partition_pos.ne' hV.partition_ne_top,one_mul]
  · exact (Real.continuous_exp.comp hB.smooth.continuous.neg).measurable.ennreal_ofReal
  · exact (measurable_gaussianAcceptance hV).ennreal_ofReal

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GibbsProportional
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling

lemma eq_gibbs_of_proportional {d : ℕ} {V : Point d → ℝ} {ν : Measure (Point d)}
    [IsProbabilityMeasure ν] {C : ℝ≥0∞}
    (h : ν = C • volume.withDensity (gibbsDensity V)) : ν = gibbs V := by
  have hm := congrArg (fun μ : Measure (Point d) => μ Set.univ) h
  rw [measure_univ, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul] at hm
  have hc : C = (partition V)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hm.symm
  rw [h, hc]
  rfl

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_TranscriptRejection
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling

lemma transcriptRejection_eq {d : ℕ} (V : Point d → ℝ) (q : ℕ) (tape : Fin q → Point d × ℝ) :
    transcriptRejection q (tape,fun i => V (tape i).1) =
      rejectionPick (gaussianAcceptance V) 0 q tape := by
  induction q with
  | zero => rfl
  | succ n ih =>
      simp only [transcriptRejection,rejectionPick,gaussianAcceptance]
      congr 1
      exact ih _

lemma finiteRejection_history {d q : ℕ} (V : Point d → ℝ) (tape : Fin q → Point d × ℝ)
    (n : ℕ) (i : Fin q) (hi : i.val < n) :
    (finiteRejectionAlgorithm d q).history V tape n i = firstOrderReply V (tape i).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [OracleAlgorithm.history]
      split_ifs with hn
      · by_cases he : i = ⟨n,hn⟩
        · subst i
          simp [finiteRejectionAlgorithm]
        · rw [Function.update_of_ne he]
          exact ih (by have hne : i.val ≠ n := fun h => he (Fin.ext h); omega)
      · apply ih
        omega

lemma finiteRejection_run {d q : ℕ} (V : Point d → ℝ) (tape : Fin q → Point d × ℝ) :
    (finiteRejectionAlgorithm d q).run V tape = rejectionPick (gaussianAcceptance V) 0 q tape := by
  change transcriptRejection q (tape,_) = _
  have hh : (fun i => ((finiteRejectionAlgorithm d q).history V tape q i).1) =
      fun i => V (tape i).1 := by
    funext i
    rw [finiteRejection_history V tape q i i.isLt]
    rfl
  rw [hh,transcriptRejection_eq]

lemma rejection_failure_bound {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1-p)^n * (1+(n:ℝ)*p) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,Nat.cast_add,Nat.cast_one]
      have hnon : 0 ≤ (1-p)^n := pow_nonneg (sub_nonneg.mpr hp1) _
      have hs : (1-p)*(1+((n:ℝ)+1)*p) ≤ 1+(n:ℝ)*p := by
        have hh : 0 ≤ ((n:ℝ)+1)*p^2 := by positivity
        nlinarith
      have h := mul_le_mul_of_nonneg_left hs hnon
      nlinarith

theorem finite_dimension_sampler (d : ℕ) : CanSample d (10*2^d) := by
  let q := 10*2^d
  let ν := gibbs (gaussianProposalPotential d)
  have hB := gaussianProposalPotential_admissible d
  have := hB.isProbabilityMeasure_gibbs
  refine ⟨Fin q → Point d × ℝ,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),
    Measure.pi (fun _ : Fin q => ν.prod unitUniform),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),finiteRejectionAlgorithm d q,?_⟩
  intro V hV
  refine ⟨(finiteRejectionAlgorithm d q).measurable_run hV,?_⟩
  have := hV.isProbabilityMeasure_gibbs
  let p := (partition V).toReal/(partition (gaussianProposalPotential d)).toReal
  have hZ : 0 < (partition (gaussianProposalPotential d)).toReal :=
    ENNReal.toReal_pos hB.partition_pos.ne' hB.partition_ne_top
  have hp0 : 0 ≤ p := div_nonneg ENNReal.toReal_nonneg hZ.le
  have hp1 : p ≤ 1 := (div_le_one hZ).mpr (partition_comparison hV).2
  have hpl : (2:ℝ)^(-(d:ℤ)) ≤ p := (le_div_iff₀ hZ).mpr (partition_comparison hV).1
  have hq : (10:ℝ) ≤ (q:ℝ)*p := by
    have hh := mul_le_mul_of_nonneg_left hpl (show (0:ℝ) ≤ (q:ℝ) by positivity)
    dsimp [q] at hh ⊢
    norm_num only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,zpow_neg,zpow_natCast] at hh ⊢
    have hpow : (2:ℝ)^d ≠ 0 := by positivity
    field_simp at hh
    nlinarith
  have hfail : (1-p)^q ≤ 1/10 := by
    have h := rejection_failure_bound hp0 hp1 q
    have hnon : 0 ≤ (1-p)^q := pow_nonneg (sub_nonneg.mpr hp1) q
    nlinarith
  have htv := capped_rejection_tv ν (gibbs V) (measurable_gaussianAcceptance hV)
    hp0 hp1 (gaussian_accepted_measure hV) 0 q
  have he : (finiteRejectionAlgorithm d q).run V = rejectionPick (gaussianAcceptance V) 0 q :=
    funext (finiteRejection_run V)
  rw [he]
  exact fun s hs => (htv s hs).trans hfail

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MapProdFiberLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling

lemma map_prod_eq_of_fiber_law {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f g : A × B → C} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ b, μ.map (fun a => f (a,b)) = μ.map (fun a => g (a,b))) :
    (μ.prod ν).map f = (μ.prod ν).map g := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply_symm (hs.preimage hf), Measure.prod_apply_symm (hs.preimage hg)]
  apply lintegral_congr
  intro b
  have hb := congrArg (fun κ : Measure C => κ s) (h b)
  rw [Measure.map_apply (f := fun a => f (a,b)) (by fun_prop) hs,
    Measure.map_apply (f := fun a => g (a,b)) (by fun_prop) hs] at hb
  exact hb

lemma map_prod_eq_of_constant_fiber_law {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [SFinite ν]
    {η : Measure C} {f : A × B → C} (hf : Measurable f)
    (h : ∀ a, ν.map (fun b => f (a,b)) = η) : (μ.prod ν).map f = η := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hs.preimage hf)]
  have hh (a : A) : ν (Prod.mk a ⁻¹' (f ⁻¹' s)) = η s := by
    have ha := congrArg (fun κ : Measure C => κ s) (h a)
    rw [Measure.map_apply (f := fun b => f (a,b)) (by fun_prop) hs] at ha
    exact ha
  simp_rw [hh]
  simp

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_RotationIsometry
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

theorem rotation_entry_eq {d : ℕ} (O : Rotations d) (i j : Fin d) :
    (O : Matrix (Fin d) (Fin d) ℝ) i j =
      (rotationIsometry O (EuclideanSpace.single j 1)) i := by
  simp [rotationIsometry_apply, EuclideanSpace.single]

@[fun_prop] theorem measurable_sphereSection {d : ℕ} :
    Measurable (fun p : Point d × Point d => sphereSection p.1 p.2) := by
  let : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))
  let : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  have he : IsClosedEmbedding (fun O : Rotations d => (O : Matrix (Fin d) (Fin d) ℝ)) :=
    (isClosed_unitary (R := Matrix (Fin d) (Fin d) ℝ)).isClosedEmbedding_subtypeVal
  apply he.measurableEmbedding.measurable_comp_iff.mp
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  change Measurable (fun p : Point d × Point d =>
    (sphereSection p.1 p.2 : Matrix (Fin d) (Fin d) ℝ) i j)
  simp_rw [rotation_entry_eq, sphereSection_apply]
  fun_prop

@[fun_prop] theorem measurable_sphereSection_left {d : ℕ} (w : Point d) :
    Measurable (sphereSection w) := by
  have measurable_pair : Measurable (fun vector : Point d => (w, vector)) :=
    measurable_const.prodMk measurable_id
  have measurable_composition : Measurable
      ((fun pair : Point d × Point d => sphereSection pair.1 pair.2) ∘
        (fun vector : Point d => (w, vector))) :=
    (measurable_sphereSection (d := d)).comp measurable_pair
  exact measurable_composition

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MapProdSecondFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling

lemma map_prod_eq_of_second_fiber_law {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f g : A × B → C} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ a, ν.map (fun b => f (a,b)) = ν.map (fun b => g (a,b))) :
    (μ.prod ν).map f = (μ.prod ν).map g := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply (hs.preimage hf), Measure.prod_apply (hs.preimage hg)]
  apply lintegral_congr
  intro a
  have ha := congrArg (fun κ : Measure C => κ s) (h a)
  rw [Measure.map_apply (f := fun b => f (a,b)) (by fun_prop) hs,
    Measure.map_apply (f := fun b => g (a,b)) (by fun_prop) hs] at ha
  exact ha

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_RevealRotation
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling.LowerBound
open ProbabilityTheory
open scoped RealInnerProductSpace

theorem measurable_complementSection {d : ℕ} (E : Submodule ℝ (Point d)) :
    Measurable (fun p : Eᗮ × Eᗮ => complementSection E p.1 p.2) := by
  have h₁ : Measurable (fun p : Eᗮ × Eᗮ => ((p.1 : Point d), (p.2 : Point d))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)
  have h₂ := (measurable_sphereSection (d := d)).comp h₁
  exact h₂.subtype_mk

lemma complement_haar_orbit_eq {d : ℕ} (E : Submodule ℝ (Point d)) {x y : Eᗮ}
    (h : ‖x‖ = ‖y‖) :
    (subspaceHaar E).map (fun O => complementIsometry E O x) =
    (subspaceHaar E).map (fun O => complementIsometry E O y) := by
  let P := complementSection E x y
  have hP : complementIsometry E P x = y := complementSection_sends E h
  calc
    _ = ((subspaceHaar E).map (· * P)).map (fun O => complementIsometry E O x) := by
      rw [map_mul_right_eq_self]
    _ = _ := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext O
      change complementIsometry E (O * P) x = complementIsometry E O y
      rw [complementIsometry_mul, hP]

theorem complementary_gaussian_radius_haar_direction {d : ℕ}
    (E : Submodule ℝ (Point d)) {w : Eᗮ} (hw : ‖w‖ = 1) :
    ((subspaceHaar E).prod (stdGaussian Eᗮ)).map
      (fun p => ‖p.2‖ • complementIsometry E p.1 w) = stdGaussian Eᗮ := by
  have hf : Measurable (fun p : subspaceStabilizer E × Eᗮ =>
      ‖p.2‖ • complementIsometry E p.1 w) := by fun_prop
  have hg : Measurable (fun p : subspaceStabilizer E × Eᗮ =>
      complementIsometry E p.1 p.2) := by fun_prop
  calc
    _ = ((subspaceHaar E).prod (stdGaussian Eᗮ)).map
        (fun p => complementIsometry E p.1 p.2) := by
      apply map_prod_eq_of_fiber_law hf hg
      intro y
      have hxy : ‖(‖y‖ • w)‖ = ‖y‖ := by simp [norm_smul, hw]
      have h := complement_haar_orbit_eq E hxy
      simpa only [map_smul] using h
    _ = _ := by
      apply map_prod_eq_of_constant_fiber_law hg
      intro O
      exact stdGaussian_map (complementIsometry E O)

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

@[fun_prop] theorem measurable_complementSection_left {d : ℕ}
    (E : Submodule ℝ (Point d)) (w : Eᗮ) : Measurable (complementSection E w) := by
  have hg : Measurable (fun v : Eᗮ => (w,v)) := measurable_const.prodMk measurable_id
  have h := (measurable_complementSection E).comp hg
  exact h

@[fun_prop] theorem measurable_revealComplement {d : ℕ}
    (E : Submodule ℝ (Point d)) (w : Eᗮ) : Measurable (revealComplement E w) := by
  unfold revealComplement
  apply Measurable.mul
  · exact (measurable_complementSection_left E w).comp (by fun_prop)
  · exact (continuous_residualInclusion E w).measurable.comp measurable_snd

theorem revealComplement_law {d : ℕ} (E : Submodule ℝ (Point d)) (w : Eᗮ) :
    ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
      (revealComplement E w) = subspaceHaar E := by
  let ν := ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
    (revealComplement E w)
  have hν : IsProbabilityMeasure ν :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability))
  have hi : ν.IsMulLeftInvariant := by
    constructor
    intro P
    change ν.map (P * ·) = ν
    dsimp only [ν]
    have hf : Measurable (fun p : subspaceStabilizer E ×
        subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d)) =>
        complementSection E w (complementIsometry E P (complementIsometry E p.1 w)) *
          residualInclusion E w p.2) := by
      apply Measurable.mul
      · exact (measurable_complementSection_left E w).comp (by fun_prop)
      · exact (continuous_residualInclusion E w).measurable.comp measurable_snd
    rw [Measure.map_map (by fun_prop) (measurable_revealComplement E w)]
    calc
      _ = ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
          (fun p => complementSection E w (complementIsometry E P (complementIsometry E p.1 w)) *
            residualInclusion E w p.2) := by
        apply map_prod_eq_of_second_fiber_law (by fun_prop) hf
        intro T
        let C := complementCocycle E w P (complementIsometry E T w)
          (LinearIsometryEquiv.norm_map _ _)
        have hg : Measurable (fun h : subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d)) =>
            complementSection E w (complementIsometry E P (complementIsometry E T w)) *
              residualInclusion E w h) := by fun_prop
        calc
          _ = ((subspaceHaar (E ⊔ ℝ ∙ (w : Point d))).map (C * ·)).map
              (fun h => complementSection E w (complementIsometry E P (complementIsometry E T w)) *
                residualInclusion E w h) := by
            rw [Measure.map_map hg (by fun_prop)]
            congr 1
            funext h
            apply Subtype.ext
            simp only [Function.comp_apply, revealComplement, Subgroup.coe_mul,
              C, complementCocycle, residualInclusion, Subgroup.coe_inv]
            group
          _ = _ := by rw [map_mul_left_eq_self]
      _ = ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
          (revealComplement E w) := by
        apply map_prod_eq_of_fiber_law hf (measurable_revealComplement E w)
        intro h
        calc
          _ = ((subspaceHaar E).map (P * ·)).map (fun T => revealComplement E w (T,h)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            congr 1
            funext T
            simp only [Function.comp_apply, revealComplement, complementIsometry_mul]
          _ = _ := by rw [map_mul_left_eq_self]
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (subspaceHaar E)
  have hm := congrArg (fun μ : Measure (subspaceStabilizer E) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : ν.haarScalarFactor (subspaceHaar E) = 1 := ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

theorem stdGaussian_orthogonalProjection (E : Submodule ℝ H) :
    (stdGaussian H).map E.orthogonalProjectionOnto = stdGaussian E := by
  apply Measure.ext_of_charFunDual
  ext L
  let x := (InnerProductSpace.toDual ℝ E).symm L
  have hx : L = innerSL ℝ x := by
    ext y
    exact (InnerProductSpace.toDual_symm_apply (x := y) (y := L)).symm
  have hc : L.comp E.orthogonalProjectionOnto = innerSL ℝ (x : H) := by
    ext y
    rw [hx]
    exact E.inner_orthogonalProjectionOnto_eq_of_mem_left x y
  rw [charFunDual_map, charFunDual_stdGaussian, charFunDual_stdGaussian, hc, hx]
  simp only [innerSL_apply_norm, Submodule.norm_coe]

theorem ae_stdGaussian_ne_zero_of_unit {w : H} (hw : ‖w‖ = 1) :
    ∀ᵐ x ∂stdGaussian H, x ≠ 0 := by
  let L : StrongDual ℝ H := innerSL ℝ w
  have hm : (stdGaussian H).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
    simp [L, hw]
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have ha : ∀ᵐ y : ℝ ∂(stdGaussian H).map L, y ≠ 0 := by
    rw [hm, ae_iff]
    simp
  have hb : ∀ᵐ x ∂stdGaussian H, L x ≠ 0 :=
    (ae_map_iff L.continuous.measurable.aemeasurable (measurableSet_singleton 0).compl).mp ha
  filter_upwards [hb] with x hx
  intro h
  simp [h] at hx

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
lemma normalizedDirection_scale {w x : H} (hx : ‖x‖ = 1) {r : ℝ} (hr : 0 < r) :
    normalizedDirection w (r • x) = x := by
  have hxn : x ≠ 0 := by intro h; simp [h] at hx
  rw [normalizedDirection, ite_eq_right (smul_ne_zero hr.ne' hxn), norm_smul, hx,
    Real.norm_eq_abs, abs_of_pos hr, mul_one, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_PrefixSpace
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling.LowerBound
open ProbabilityTheory

theorem complementary_gaussian_direction_law {d : ℕ} (E : Submodule ℝ (Point d))
    {w : Eᗮ} (hw : ‖w‖ = 1) :
    (stdGaussian Eᗮ).map (normalizedDirection w) =
      (subspaceHaar E).map (fun O => complementIsometry E O w) := by
  have hn := ae_stdGaussian_ne_zero_of_unit hw
  have hp : ∀ᵐ p ∂(subspaceHaar E).prod (stdGaussian Eᗮ), p.2 ≠ 0 :=
    Measure.quasiMeasurePreserving_snd.ae hn
  calc
    _ = (((subspaceHaar E).prod (stdGaussian Eᗮ)).map
        (fun p => ‖p.2‖ • complementIsometry E p.1 w)).map (normalizedDirection w) := by
      rw [complementary_gaussian_radius_haar_direction E hw]
    _ = ((subspaceHaar E).prod (stdGaussian Eᗮ)).map
        (fun p => complementIsometry E p.1 w) := by
      rw [Measure.map_map (measurable_normalizedDirection w) (by fun_prop)]
      apply Measure.map_congr
      filter_upwards [hp] with p hp
      exact normalizedDirection_scale (by simpa using hw) (norm_pos_iff.mpr hp)
    _ = _ := by
      change Measure.map ((fun O => complementIsometry E O w) ∘ Prod.fst) _ = _
      rw [← Measure.map_map (f := Prod.fst) (g := fun O => complementIsometry E O w)
        (by fun_prop) measurable_fst]
      simp

theorem projected_gaussian_direction_law {d : ℕ} (E : Submodule ℝ (Point d))
    {w : Eᗮ} (hw : ‖w‖ = 1) :
    (stdGaussian (Point d)).map
      (fun g => normalizedDirection w (Eᗮ.orthogonalProjectionOnto g)) =
      (subspaceHaar E).map (fun O => complementIsometry E O w) := by
  change Measure.map (normalizedDirection w ∘ Eᗮ.orthogonalProjectionOnto) _ = _
  rw [← Measure.map_map (f := Eᗮ.orthogonalProjectionOnto)
    (g := normalizedDirection w) (measurable_normalizedDirection w) (by fun_prop),
    stdGaussian_orthogonalProjection, complementary_gaussian_direction_law E hw]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling
namespace LowerBound

lemma prefixSpace_mono (d : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    prefixSpace d k ≤ prefixSpace d l := by
  intro x hx i hi
  exact hx i (hkl.trans hi)

lemma prefixSpace_succ {d k : ℕ} (hk : k < d) :
    prefixSpace d (k+1) = prefixSpace d k ⊔ ℝ ∙ coordinateVector ⟨k,hk⟩ := by
  apply le_antisymm
  · intro x hx
    have ht : x - (x ⟨k,hk⟩) • coordinateVector ⟨k,hk⟩ ∈ prefixSpace d k := by
      intro i hi
      by_cases hik : i.val = k
      · have he : i = ⟨k,hk⟩ := Fin.ext hik
        simp [he]
      · have hki : k+1 ≤ i.val := by omega
        have hine : i ≠ ⟨k,hk⟩ := by intro h; apply hik; exact congrArg Fin.val h
        simp [hx i hki, coordinateVector_apply, hine]
    have hs : x ⟨k,hk⟩ • coordinateVector ⟨k,hk⟩ ∈ ℝ ∙ coordinateVector ⟨k,hk⟩ :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    convert (prefixSpace d k ⊔ ℝ ∙ coordinateVector ⟨k,hk⟩).add_mem
      ((le_sup_left : prefixSpace d k ≤ _ ) ht) ((le_sup_right : ℝ ∙ coordinateVector ⟨k,hk⟩ ≤ _) hs)
      using 1
    all_goals try with_reducible_and_instances rfl
    module
  · apply sup_le
    · exact prefixSpace_mono d (Nat.le_succ k)
    · apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      intro i hi
      have hine : i ≠ ⟨k,hk⟩ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
      simp [coordinateVector_apply, hine]

end LowerBound
end LogConcaveSampling

namespace LogConcaveSampling.LowerBound
open ProbabilityTheory

@[fun_prop] theorem measurable_gaussianSection {d : ℕ}
    (E : Submodule ℝ (Point d)) (e : Eᗮ) : Measurable (gaussianSection E e) := by
  exact (measurable_complementSection_left E e).comp
    ((measurable_normalizedDirection e).comp (by fun_prop))

@[fun_prop] theorem measurable_gaussianForward {d : ℕ}
    (E : Submodule ℝ (Point d)) (e : Eᗮ) : Measurable (gaussianForward E e) := by
  unfold gaussianForward
  exact ((measurable_gaussianSection E e).comp measurable_fst).mul
    ((continuous_residualInclusion E e).measurable.comp measurable_snd)

theorem gaussianForward_law {d : ℕ} (E : Submodule ℝ (Point d))
    {e : Eᗮ} (he : ‖e‖ = 1) :
    ((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
      (gaussianForward E e) = subspaceHaar E := by
  calc
    _ = ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
        (revealComplement E e) := by
      ext s hs
      rw [Measure.map_apply (measurable_gaussianForward E e) hs,
        Measure.map_apply (measurable_revealComplement E e) hs,
        Measure.prod_apply_symm (hs.preimage (measurable_gaussianForward E e)),
        Measure.prod_apply_symm (hs.preimage (measurable_revealComplement E e))]
      apply lintegral_congr
      intro h
      have hM : (stdGaussian (Point d)).map (fun g => gaussianForward E e (g,h)) =
          (subspaceHaar E).map (fun O => revealComplement E e (O,h)) := by
        have hm : Measurable (fun v : Eᗮ => complementSection E e v * residualInclusion E e h) :=
          (measurable_complementSection_left E e).mul_const _
        have hl := congrArg (fun μ : Measure Eᗮ => μ.map
          (fun v => complementSection E e v * residualInclusion E e h))
          (projected_gaussian_direction_law E he)
        rw [Measure.map_map hm (by fun_prop), Measure.map_map hm (by fun_prop)] at hl
        exact hl
      have ha := congrArg (fun μ : Measure (subspaceStabilizer E) => μ s) hM
      rw [Measure.map_apply (f := fun g => gaussianForward E e (g,h)) (by fun_prop) hs,
        Measure.map_apply (f := fun O => revealComplement E e (O,h)) (by fun_prop) hs] at ha
      exact ha
    _ = _ := revealComplement_law E e

@[fun_prop] theorem measurable_gaussianBackward {d : ℕ}
    (E : Submodule ℝ (Point d)) (e w : Eᗮ) : Measurable (gaussianBackward E e w) := by
  unfold gaussianBackward
  fun_prop

theorem gaussianBackward_law {d : ℕ} (E : Submodule ℝ (Point d))
    {e : Eᗮ} (he : ‖e‖ = 1) (w : Eᗮ) :
    ((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
      (gaussianBackward E e w) = subspaceHaar E := by
  calc
    _ = ((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
        (fun p => complementSection E e w * (gaussianForward E e p)⁻¹) := by
      apply map_prod_eq_of_second_fiber_law (measurable_gaussianBackward E e w) (by fun_prop)
      intro g
      calc
        _ = ((subspaceHaar (E ⊔ ℝ ∙ (e : Point d))).map Inv.inv).map
            (fun h => complementSection E e w * (gaussianForward E e (g,h))⁻¹) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
          funext h
          apply Subtype.ext
          simp only [Function.comp_apply, gaussianForward, gaussianBackward,
            residualInclusion, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        _ = _ := by rw [Measure.map_inv_eq_self]
    _ = (((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
        (gaussianForward E e)).map (fun O => complementSection E e w * O⁻¹) := by
      rw [Measure.map_map (by fun_prop) (measurable_gaussianForward E e)]
      rfl
    _ = _ := by
      rw [gaussianForward_law E he]
      simpa only [div_eq_mul_inv] using
        (Measure.map_div_left_eq_self (subspaceHaar E) (complementSection E e w))

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma remainingHaar_fixes {d : ℕ} (E : Submodule ℝ (Point d)) :
    ∀ᵐ H ∂remainingHaar E, H ∈ subspaceStabilizer E := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (subspaceStabilizer_isClosed E).measurableSet).mpr
  exact Filter.Eventually.of_forall Subtype.property

@[fun_prop] lemma measurable_ambientBackward {d : ℕ}
    (E : Submodule ℝ (Point d)) (e w : Eᗮ) : Measurable (ambientBackward E e w) := by
  unfold ambientBackward
  fun_prop

lemma ambientBackward_law {d : ℕ} (E : Submodule ℝ (Point d))
    {e : Eᗮ} (he : ‖e‖ = 1) (w : Eᗮ) :
    ((stdGaussian (Point d)).prod (remainingHaar (E ⊔ ℝ ∙ (e : Point d)))).map
      (ambientBackward E e w) = remainingHaar E := by
  have hp := Measure.map_prod_map (stdGaussian (Point d))
    (subspaceHaar (E ⊔ ℝ ∙ (e : Point d))) measurable_id measurable_subtype_coe
  rw [Measure.map_id] at hp
  unfold remainingHaar
  rw [hp, Measure.map_map (measurable_ambientBackward E e w) (by fun_prop)]
  calc
    _ = (((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
        (gaussianBackward E e w)).map Subtype.val := by
      rw [Measure.map_map measurable_subtype_coe (measurable_gaussianBackward E e w)]
      rfl
    _ = _ := by rw [gaussianBackward_law E he]

@[fun_prop] lemma measurable_inverseFrameUpdate {d k : ℕ} (hk : k < d) :
    Measurable (fun p : Frames d × Point d × Point d => inverseFrameUpdate hk p.1 p.2.1 p.2.2) := by
  unfold inverseFrameUpdate
  apply Measurable.prodMk
  · apply Measurable.mul (by fun_prop)
    apply measurable_subtype_coe.comp
    exact (measurable_complementSection_left _ _).comp (by fun_prop)
  · fun_prop

theorem inverseFrameUpdate_law {d k : ℕ} (hk : k < d) (F : Frames d) (x : Point d) :
    ((stdGaussian (Point d)).prod (remainingHaar (prefixSpace d (k+1)))).map
      (fun p => frameCompletion (inverseFrameUpdate hk F x p.1) p.2) =
    (remainingHaar (prefixSpace d k)).map (frameCompletion F) := by
  let E := prefixSpace d k
  let e := prefixUnit hk
  let w := flagDirection hk (rotationIsometry F.1⁻¹ x)
  have hg : (stdGaussian (Point d)).map (rotationIsometry F.2⁻¹) = stdGaussian (Point d) :=
    stdGaussian_map (rotationIsometry F.2⁻¹)
  have hP := Measure.map_prod_map (stdGaussian (Point d))
    (remainingHaar (prefixSpace d (k+1))) (by fun_prop : Measurable (rotationIsometry F.2⁻¹))
      measurable_id
  rw [hg, Measure.map_id] at hP
  have hl := congrArg (fun μ : Measure (Rotations d) => μ.map (frameCompletion F))
    (ambientBackward_law E (norm_prefixUnit hk) w)
  have hEq : E ⊔ ℝ ∙ (e : Point d) = prefixSpace d (k+1) := (prefixSpace_succ hk).symm
  rw [hEq, Measure.map_map (by fun_prop) (measurable_ambientBackward E e w)] at hl
  rw [hP, Measure.map_map (by fun_prop) (by fun_prop)] at hl
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext p
  simp only [Function.comp_apply, frameCompletion,
    inverseFrameUpdate, ambientBackward, E, e, w]
  group; rfl

lemma remainingHaar_map_inv {d : ℕ} (E : Submodule ℝ (Point d)) :
    (remainingHaar E).map Inv.inv = remainingHaar E := by
  unfold remainingHaar
  rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
  calc
    _ = ((subspaceHaar E).map Inv.inv).map Subtype.val := by
      rw [Measure.map_map measurable_subtype_coe (by fun_prop)]
      rfl
    _ = _ := by rw [Measure.map_inv_eq_self]

@[fun_prop] lemma measurable_forwardFrameUpdate {d k : ℕ} (hk : k < d) :
    Measurable (fun p : Frames d × Point d × Point d => forwardFrameUpdate hk p.1 p.2.1 p.2.2) := by
  unfold forwardFrameUpdate
  have h := (measurable_inverseFrameUpdate hk).comp
    (show Measurable (fun p : Frames d × Point d × Point d => (p.1.swap,p.2)) by fun_prop)
  exact h.snd.prodMk h.fst

theorem forwardFrameUpdate_law {d k : ℕ} (hk : k < d) (F : Frames d) (y : Point d) :
    ((stdGaussian (Point d)).prod (remainingHaar (prefixSpace d (k+1)))).map
      (fun p => frameCompletion (forwardFrameUpdate hk F y p.1) p.2) =
    (remainingHaar (prefixSpace d k)).map (frameCompletion F) := by
  have hl := congrArg (fun μ : Measure (Rotations d) => μ.map Inv.inv)
    (inverseFrameUpdate_law hk F.swap y)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hl
  have hP := Measure.map_prod_map (stdGaussian (Point d))
    (remainingHaar (prefixSpace d (k+1))) measurable_id (by fun_prop : Measurable (Inv.inv : Rotations d → _))
  rw [Measure.map_id, remainingHaar_map_inv] at hP
  rw [hP, Measure.map_map (by fun_prop) (by fun_prop)]
  change ((stdGaussian (Point d)).prod (remainingHaar (prefixSpace d (k+1)))).map
    (fun p => frameCompletion (forwardFrameUpdate hk F y p.1) p.2⁻¹) = _
  simp only [forwardFrameUpdate, frameCompletion_swap]
  simp only [Function.comp_def] at hl
  rw [hl]
  calc
    _ = ((remainingHaar (prefixSpace d k)).map Inv.inv).map (frameCompletion F) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1; funext H
      simp [frameCompletion, mul_assoc]
    _ = _ := by rw [remainingHaar_map_inv]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

lemma mem_frameSpace {d : ℕ} (O : Rotations d) (E : Submodule ℝ (Point d)) (x : Point d) :
    x ∈ frameSpace O E ↔ rotationIsometry O⁻¹ x ∈ E := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [rotationIsometry_inv_apply]
    change (rotationIsometry O).symm (rotationIsometry O y) ∈ E
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact hy
  · intro hx
    refine ⟨rotationIsometry O⁻¹ x,hx,?_⟩
    simp only [LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv,
      rotationIsometry_inv_apply, LinearIsometryEquiv.apply_symm_apply]

lemma frameSpace_mul {d : ℕ} (O P : Rotations d) (E : Submodule ℝ (Point d)) :
    frameSpace (O*P) E = frameSpace O (frameSpace P E) := by
  ext x
  simp only [mem_frameSpace, _root_.mul_inv_rev, rotationIsometry_mul]

lemma frameSpace_sup {d : ℕ} (O : Rotations d) (E F : Submodule ℝ (Point d)) :
    frameSpace O (E ⊔ F) = frameSpace O E ⊔ frameSpace O F := Submodule.map_sup _ _ _

lemma frameSpace_line {d : ℕ} (O : Rotations d) (x : Point d) :
    frameSpace O (ℝ ∙ x) = ℝ ∙ rotationIsometry O x := by
  simp only [frameSpace, Submodule.map_span, Set.image_singleton,
    LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv]

lemma frameSpace_fixed {d : ℕ} (E : Submodule ℝ (Point d))
    {O : Rotations d} (hO : O ∈ subspaceStabilizer E) : frameSpace O E = E := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    change rotationIsometry O y ∈ E
    rw [hO y hy]
    exact hy
  · intro x hx
    exact ⟨x,hx,hO x hx⟩

lemma frameSpace_mono {d : ℕ} (O : Rotations d) {E F : Submodule ℝ (Point d)}
    (h : E ≤ F) : frameSpace O E ≤ frameSpace O F := Submodule.map_mono h

lemma complementSection_frameSpace {d : ℕ} (E : Submodule ℝ (Point d))
    {e w : Eᗮ} (h : ‖e‖ = ‖w‖) :
    frameSpace (complementSection E e w).1 (E ⊔ ℝ ∙ (e : Point d)) =
      E ⊔ ℝ ∙ (w : Point d) := by
  rw [frameSpace_sup, frameSpace_fixed E (complementSection E e w).property, frameSpace_line]
  have hs := congrArg Subtype.val (complementSection_sends E h)
  change rotationIsometry (complementSection E e w).1 e = w at hs
  rw [hs]

lemma flagSection_frameSpace {d k : ℕ} (hk : k < d) (x : Point d) :
    frameSpace (complementSection (prefixSpace d k) (prefixUnit hk) (flagDirection hk x)).1
      (prefixSpace d (k+1)) = prefixSpace d k ⊔ ℝ ∙ (flagDirection hk x : Point d) := by
  rw [prefixSpace_succ hk]
  exact complementSection_frameSpace (prefixSpace d k)
    (e := prefixUnit hk) (w := flagDirection hk x) (by rw [norm_prefixUnit, norm_flagDirection])

lemma vector_mem_flagDirection {d k : ℕ} (hk : k < d) (x : Point d) :
    x ∈ prefixSpace d k ⊔ ℝ ∙ (flagDirection hk x : Point d) := by
  let E := prefixSpace d k
  have ht : ((Eᗮ.orthogonalProjectionOnto x : Eᗮ) : Point d) ∈
      ℝ ∙ (flagDirection hk x : Point d) := by
    change _ ∈ ℝ ∙ ((normalizedDirection (prefixUnit hk) (Eᗮ.orthogonalProjectionOnto x) : Eᗮ) : Point d)
    by_cases hn : Eᗮ.orthogonalProjectionOnto x = 0
    · simp [hn]
    · have hs := (ℝ ∙ ((normalizedDirection (prefixUnit hk) (Eᗮ.orthogonalProjectionOnto x) : Eᗮ) : Point d)).smul_mem
        ‖Eᗮ.orthogonalProjectionOnto x‖ (Submodule.mem_span_singleton_self _)
      simpa only [normalizedDirection, ite_eq_right hn, Submodule.coe_smul_of_tower, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn), one_smul] using hs
  have hp : E.starProjection x ∈ E := E.starProjection_apply_mem x
  have hs := (E ⊔ ℝ ∙ (flagDirection hk x : Point d)).add_mem
    ((le_sup_left : E ≤ _) hp) ((le_sup_right : ℝ ∙ _ ≤ _) ht)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  exact (E.starProjection_add_starProjection_orthogonal x).symm

lemma flagDirection_mem_span {d k : ℕ} (hk : k < d) (x : Point d)
    (hn : (prefixSpace d k)ᗮ.orthogonalProjectionOnto x ≠ 0) :
    (flagDirection hk x : Point d) ∈ prefixSpace d k ⊔ ℝ ∙ x := by
  let E := prefixSpace d k
  have hx : x ∈ E ⊔ ℝ ∙ x := (le_sup_right : ℝ ∙ x ≤ _) (Submodule.mem_span_singleton_self x)
  have hp : E.starProjection x ∈ E ⊔ ℝ ∙ x :=
    (le_sup_left : E ≤ _) (E.starProjection_apply_mem x)
  have ht := (E ⊔ ℝ ∙ x).sub_mem hx hp
  rw [← Submodule.starProjection_orthogonal_val] at ht
  have hs := (E ⊔ ℝ ∙ x).smul_mem ‖Eᗮ.orthogonalProjectionOnto x‖⁻¹ ht
  simp only [flagDirection, normalizedDirection, ite_eq_right hn]
  exact hs

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

@[fun_prop] lemma measurable_extendFrame {d k : ℕ} (hk : k < d) :
    Measurable (fun p : Rotations d × Point d => extendFrame hk p.1 p.2) := by
  unfold extendFrame
  apply Measurable.mul measurable_fst
  apply measurable_subtype_coe.comp
  exact (measurable_complementSection_left _ _).comp (by fun_prop)

lemma inverseFrameUpdate_eq {d k : ℕ} (hk : k < d) (F : Frames d) (x g : Point d) :
    inverseFrameUpdate hk F x g = (extendFrame hk F.1 x, extendFrame hk F.2 g) := rfl

lemma forwardFrameUpdate_eq {d k : ℕ} (hk : k < d) (F : Frames d) (y g : Point d) :
    forwardFrameUpdate hk F y g = (extendFrame hk F.1 g, extendFrame hk F.2 y) := rfl

lemma frameSpace_extendFrame {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) :
    frameSpace (extendFrame hk O x) (prefixSpace d (k+1)) =
      frameSpace O (prefixSpace d k) ⊔
        ℝ ∙ rotationIsometry O (flagDirection hk (rotationIsometry O⁻¹ x) : Point d) := by
  rw [extendFrame, frameSpace_mul, flagSection_frameSpace, frameSpace_sup, frameSpace_line]

lemma frameSpace_le_extendFrame {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) :
    frameSpace O (prefixSpace d k) ≤ frameSpace (extendFrame hk O x) (prefixSpace d (k+1)) := by
  rw [frameSpace_extendFrame]
  exact le_sup_left

lemma mem_frameSpace_extendFrame {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) :
    x ∈ frameSpace (extendFrame hk O x) (prefixSpace d (k+1)) := by
  rw [extendFrame, frameSpace_mul, flagSection_frameSpace, mem_frameSpace]
  exact vector_mem_flagDirection hk _

lemma frameSpace_extendFrame_le {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d)
    (hn : (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ x) ≠ 0) :
    frameSpace (extendFrame hk O x) (prefixSpace d (k+1)) ≤
      frameSpace O (prefixSpace d k) ⊔ ℝ ∙ x := by
  rw [extendFrame, frameSpace_mul, flagSection_frameSpace]
  have hs : prefixSpace d k ⊔ ℝ ∙ (flagDirection hk (rotationIsometry O⁻¹ x) : Point d) ≤
      prefixSpace d k ⊔ ℝ ∙ rotationIsometry O⁻¹ x := by
    apply sup_le le_sup_left
    exact Submodule.span_le.mpr (by
      intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact flagDirection_mem_span hk _ hn)
  have h := frameSpace_mono O hs
  simp only [frameSpace_sup, frameSpace_line, rotationIsometry_inv_apply,
    LinearIsometryEquiv.apply_symm_apply] at h
  rw [frameSpace_sup, frameSpace_line]
  simpa only [rotationIsometry_inv_apply] using h

lemma ae_frameGaussian_nonzero {d k : ℕ} (hk : k < d) (O : Rotations d) :
    ∀ᵐ g ∂stdGaussian (Point d),
      (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ g) ≠ 0 := by
  have h := ae_stdGaussian_ne_zero_of_unit (norm_prefixUnit hk)
  rw [← stdGaussian_orthogonalProjection (prefixSpace d k)ᗮ] at h
  have hp : ∀ᵐ x ∂stdGaussian (Point d), (prefixSpace d k)ᗮ.orthogonalProjectionOnto x ≠ 0 :=
    (ae_map_iff (by fun_prop) (measurableSet_singleton 0).compl).mp h
  rw [← stdGaussian_map (rotationIsometry O⁻¹)] at hp
  exact (ae_map_iff (by fun_prop) ((measurableSet_singleton 0).compl.preimage (by fun_prop))).mp hp

lemma mem_frameSpace_of_projection_zero {d k : ℕ} (O : Rotations d) (x : Point d)
    (hz : (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ x) = 0) :
    x ∈ frameSpace O (prefixSpace d k) := by
  rw [mem_frameSpace]
  have hz' := congrArg Subtype.val hz
  change (prefixSpace d k)ᗮ.starProjection (rotationIsometry O⁻¹ x) = 0 at hz'
  rw [Submodule.starProjection_orthogonal_val, sub_eq_zero] at hz'
  rw [hz']
  exact Submodule.starProjection_apply_mem _ _

lemma mem_frameSpace_filledExtend {d k : ℕ} (hk : k < d) (O : Rotations d) (x g : Point d) :
    x ∈ frameSpace (extendFrame hk O (filledObservation (k := k) O x g)) (prefixSpace d (k+1)) := by
  unfold filledObservation
  split_ifs with hz
  · exact frameSpace_le_extendFrame hk O g (mem_frameSpace_of_projection_zero O x hz)
  · exact mem_frameSpace_extendFrame hk O x

lemma frameSpace_filledExtend_le {d k : ℕ} (hk : k < d) (O : Rotations d) (x g : Point d)
    (hg : (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ g) ≠ 0) :
    frameSpace (extendFrame hk O (filledObservation (k := k) O x g)) (prefixSpace d (k+1)) ≤
      (frameSpace O (prefixSpace d k) ⊔ ℝ ∙ x) ⊔ ℝ ∙ g := by
  unfold filledObservation
  split_ifs with hx
  · exact (frameSpace_extendFrame_le hk O g hg).trans (sup_le_sup le_sup_left le_rfl)
  · exact (frameSpace_extendFrame_le hk O x hx).trans le_sup_left

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_FrameTransport
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling.LowerBound

lemma frameCompletion_apply {d : ℕ} (F : Frames d) (H : Rotations d) (x : Point d) :
    rotationIsometry (frameCompletion F H) x =
      rotationIsometry F.1 (rotationIsometry H (rotationIsometry F.2⁻¹ x)) := by
  simp only [frameCompletion, rotationIsometry_mul]

lemma frameCompletion_eq_transport {d : ℕ} (E : Submodule ℝ (Point d))
    (F : Frames d) {H : Rotations d} (hH : H ∈ subspaceStabilizer E)
    {x : Point d} (hx : x ∈ frameSpace F.2 E) :
    rotationIsometry (frameCompletion F H) x = frameTransport F x := by
  rw [frameCompletion_apply, hH _ ((mem_frameSpace F.2 E x).mp hx)]
  simp only [frameTransport, frameCompletion_apply, rotationIsometry_one]

lemma frameTransport_swap {d : ℕ} (F : Frames d) (x : Point d) :
    frameTransport F.swap x = (frameTransport F).symm x := by
  unfold frameTransport
  rw [← rotationIsometry_inv_apply]
  have h : frameCompletion F.swap 1 = (frameCompletion F 1)⁻¹ := by
    simpa only [inv_one] using frameCompletion_swap F 1
  rw [h]

lemma frameCompletion_symm_eq_transport {d : ℕ} (E : Submodule ℝ (Point d))
    (F : Frames d) {H : Rotations d} (hH : H ∈ subspaceStabilizer E)
    {x : Point d} (hx : x ∈ frameSpace F.1 E) :
    (rotationIsometry (frameCompletion F H)).symm x = (frameTransport F).symm x := by
  rw [← rotationIsometry_inv_apply, ← frameCompletion_swap]
  rw [frameCompletion_eq_transport E F.swap ((subspaceStabilizer E).inv_mem hH) hx,
    frameTransport_swap]

lemma frameTransport_preimage_mem {d : ℕ} (E : Submodule ℝ (Point d))
    (F : Frames d) {x : Point d} (hx : x ∈ frameSpace F.1 E) :
    (frameTransport F).symm x ∈ frameSpace F.2 E := by
  rw [mem_frameSpace] at hx ⊢
  rw [← frameTransport_swap, frameTransport, frameCompletion_apply, rotationIsometry_one]
  simp only [rotationIsometry_inv_apply]
  change (rotationIsometry F.2).symm (rotationIsometry F.2 ((rotationIsometry F.1).symm x)) ∈ E
  rw [LinearIsometryEquiv.symm_apply_apply]
  simpa only [rotationIsometry_inv_apply] using hx

lemma extendFrame_relative_mem {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) :
    O⁻¹ * extendFrame hk O x ∈ subspaceStabilizer (prefixSpace d k) := by
  simpa only [extendFrame, inv_mul_cancel_left] using
    (complementSection (prefixSpace d k) (prefixUnit hk)
      (flagDirection hk (rotationIsometry O⁻¹ x))).property

lemma compatibleFrames_reconstruct {d : ℕ} (E : Submodule ℝ (Point d))
    {F F' : Frames d} (h : CompatibleFrames E F F') {H : Rotations d}
    (hH : H ∈ subspaceStabilizer E) :
    ∃ H' ∈ subspaceStabilizer E, frameCompletion F' H = frameCompletion F H' := by
  refine ⟨(F.1⁻¹*F'.1)*H*(F.2⁻¹*F'.2)⁻¹,
    (subspaceStabilizer E).mul_mem ((subspaceStabilizer E).mul_mem h.1 hH)
      ((subspaceStabilizer E).inv_mem h.2),?_⟩
  unfold frameCompletion
  group

lemma compatibleFrames_inverseUpdate {d k : ℕ} (hk : k < d) (F : Frames d) (x g : Point d) :
    CompatibleFrames (prefixSpace d k) F (inverseFrameUpdate hk F x g) := by
  rw [inverseFrameUpdate_eq]
  exact ⟨extendFrame_relative_mem hk _ _, extendFrame_relative_mem hk _ _⟩

lemma compatibleFrames_forwardUpdate {d k : ℕ} (hk : k < d) (F : Frames d) (y g : Point d) :
    CompatibleFrames (prefixSpace d k) F (forwardFrameUpdate hk F y g) := by
  rw [forwardFrameUpdate_eq]
  exact ⟨extendFrame_relative_mem hk _ _, extendFrame_relative_mem hk _ _⟩

lemma subspaceStabilizer_anti {d : ℕ} {E F : Submodule ℝ (Point d)} (h : E ≤ F) :
    subspaceStabilizer F ≤ subspaceStabilizer E := by
  intro O hO x hx
  exact hO x (h hx)

lemma compatibleFrames_mono {d : ℕ} {E G : Submodule ℝ (Point d)} (h : E ≤ G)
    {F F' : Frames d} (hc : CompatibleFrames G F F') : CompatibleFrames E F F' :=
  ⟨subspaceStabilizer_anti h hc.1, subspaceStabilizer_anti h hc.2⟩

lemma compatibleFrames_trans {d : ℕ} {E : Submodule ℝ (Point d)} {F F' F'' : Frames d}
    (h : CompatibleFrames E F F') (h' : CompatibleFrames E F' F'') :
    CompatibleFrames E F F'' := by
  constructor
  · have hm := (subspaceStabilizer E).mul_mem h.1 h'.1
    simpa only [mul_assoc, mul_inv_cancel_left] using hm
  · have hm := (subspaceStabilizer E).mul_mem h.2 h'.2
    simpa only [mul_assoc, mul_inv_cancel_left] using hm

end LogConcaveSampling.LowerBound

open MeasureTheory ProbabilityTheory

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_StateLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling

lemma map_prod_eq_of_conditional_law {S A B C : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure S} {ν : Measure A} {η : Measure B}
    [SFinite μ] [SFinite ν] [SFinite η]
    {f : S × A → C} {g : S × B → C}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s, ν.map (fun a => f (s,a)) = η.map (fun b => g (s,b))) :
    (μ.prod ν).map f = (μ.prod η).map g := by
  ext t ht
  rw [Measure.map_apply hf ht, Measure.map_apply hg ht,
    Measure.prod_apply (ht.preimage hf), Measure.prod_apply (ht.preimage hg)]
  apply lintegral_congr
  intro s
  have hs := congrArg (fun κ : Measure C => κ t) (h s)
  rw [Measure.map_apply (f := fun a => f (s,a)) (by fun_prop) ht,
    Measure.map_apply (f := fun b => g (s,b)) (by fun_prop) ht] at hs
  exact hs

theorem eliminate_fresh_residual {S T R H C : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace R]
    [MeasurableSpace H] [MeasurableSpace C]
    {μ : Measure S} {γ : Measure R} {η η' : Measure H}
    [SFinite μ] [SFinite γ] [SFinite η] [SFinite η']
    {step : S × R → T} {f : T × H → C} {g : S × H → C}
    (hstep : Measurable step) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s, (γ.prod η').map (fun p => f (step (s,p.1),p.2)) =
      η.map (fun h => g (s,h))) :
    (((μ.prod γ).map step).prod η').map f = (μ.prod η).map g := by
  have hp := Measure.map_prod_map (μ.prod γ) η' hstep measurable_id
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map hf (by fun_prop)]
  have ha := Measure.prodAssoc_prod (μ := μ) (ν := γ) (τ := η')
  calc
    _ = (μ.prod (γ.prod η')).map (fun p => f (step (p.1,p.2.1),p.2.2)) := by
      rw [← ha, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
      rfl
    _ = _ := map_prod_eq_of_conditional_law (by fun_prop) hg h

section Iteration
variable {S : ℕ → Type*} {R H C : Type*}
    [∀ n, MeasurableSpace (S n)] [MeasurableSpace R] [MeasurableSpace H] [MeasurableSpace C]

lemma stateLaw_probability (μ : Measure (S 0)) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (step : (n : ℕ) → S n × R → S (n+1)) (hstep : ∀ n, Measurable (step n)) (n : ℕ) :
    IsProbabilityMeasure (stateLaw μ γ step n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    have := ih
    exact (Measure.isProbabilityMeasure_map_iff (hstep n).aemeasurable).mpr inferInstance

theorem stateLaw_completion (μ : Measure (S 0)) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (step : (n : ℕ) → S n × R → S (n+1)) (hstep : ∀ n, Measurable (step n))
    (η : ℕ → Measure H) [∀ n, IsProbabilityMeasure (η n)]
    (f : (n : ℕ) → S n × H → C) (hf : ∀ n, Measurable (f n))
    (N : ℕ)
    (hlocal : ∀ n < N, ∀ s : S n,
      (γ.prod (η (n+1))).map (fun p => f (n+1) (step n (s,p.1),p.2)) =
        (η n).map (fun h => f n (s,h))) :
    ((stateLaw μ γ step N).prod (η N)).map (f N) = (μ.prod (η 0)).map (f 0) := by
  have hprob (j : ℕ) := stateLaw_probability μ γ step hstep j
  have h : ∀ n ≤ N, ((stateLaw μ γ step n).prod (η n)).map (f n) =
      (μ.prod (η 0)).map (f 0) := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      change ((((stateLaw μ γ step n).prod γ).map (step n)).prod (η (n+1))).map
        (f (n+1)) = _
      rw [eliminate_fresh_residual (hstep n) (hf (n+1)) (hf n) (hlocal n (by omega))]
      exact ih (by omega)
  exact h N le_rfl

end Iteration
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_RoundFrames
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling.LowerBound

@[fun_prop] lemma measurable_inverse_frameTransport {d : ℕ} :
    Measurable (fun p : Frames d × Point d => (frameTransport p.1).symm p.2) := by
  simp only [← frameTransport_swap]
  have h := (measurable_frameTransport (d := d)).comp
    (show Measurable (fun p : Frames d × Point d => (p.1.swap,p.2)) by fun_prop)
  exact h

@[fun_prop] lemma measurable_roundFrames {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d) :
    Measurable (fun p : (Frames d × Point d) × (Point d × Point d × Point d) =>
      roundFrames hk Λ p.1.1 p.1.2 p.2) := by
  let Z := (Frames d × Point d) × (Point d × Point d × Point d)
  let f : Z → Frames d := fun p => inverseFrameUpdate (Nat.lt_of_succ_lt hk) p.1.1 p.1.2 p.2.1
  have hf : Measurable f := (measurable_inverseFrameUpdate (Nat.lt_of_succ_lt hk)).comp
    (f := fun p : Z => (p.1.1,p.1.2,p.2.1)) ((measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd.fst))
  let u : Z → Point d := fun p => (frameTransport (f p)).symm p.1.2
  have hu : Measurable u := (measurable_inverse_frameTransport (d := d)).comp
    (f := fun p : Z => (f p,p.1.2)) (hf.prodMk measurable_fst.snd)
  let y : Z → Point d := fun p => Λ (u p)
  have hy : Measurable y := Λ.continuous.measurable.comp (f := u) hu
  let z : Z → Point d := fun p => filledObservation (k := k+1) (f p).2 (y p) p.2.2.1
  have hz : Measurable z := (measurable_filledObservation (d := d) (k := k+1)).comp
    (f := fun p : Z => ((f p).2,y p,p.2.2.1)) (hf.snd.prodMk (hy.prodMk measurable_snd.snd.fst))
  change Measurable (fun p : Z => forwardFrameUpdate hk (f p) (z p) p.2.2.2)
  exact (measurable_forwardFrameUpdate hk).comp
    (f := fun p : Z => (f p,z p,p.2.2.2)) (hf.prodMk (hz.prodMk measurable_snd.snd.snd))

lemma filledForward_law {d k : ℕ} (hk : k < d) (F : Frames d) (y : Point d) :
    (((stdGaussian (Point d)).prod (stdGaussian (Point d))).prod
      (remainingHaar (prefixSpace d (k+1)))).map
        (fun p => frameCompletion (forwardFrameUpdate hk F
          (filledObservation (k := k) F.2 y p.1.1) p.1.2) p.2) =
      (remainingHaar (prefixSpace d k)).map (frameCompletion F) := by
  have ha := Measure.prodAssoc_prod (μ := stdGaussian (Point d)) (ν := stdGaussian (Point d))
    (τ := remainingHaar (prefixSpace d (k+1)))
  calc
    _ = ((stdGaussian (Point d)).prod ((stdGaussian (Point d)).prod
        (remainingHaar (prefixSpace d (k+1))))).map
        (fun p => frameCompletion (forwardFrameUpdate hk F
          (filledObservation (k := k) F.2 y p.1) p.2.1) p.2.2) := by
      rw [← ha, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
      rfl
    _ = _ := by
      apply map_prod_eq_of_constant_fiber_law (by fun_prop)
      intro g
      exact forwardFrameUpdate_law hk F (filledObservation (k := k) F.2 y g)

theorem roundFrames_law {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) :
    (((stdGaussian (Point d)).prod ((stdGaussian (Point d)).prod (stdGaussian (Point d)))).prod
      (remainingHaar (prefixSpace d (k+2)))).map
        (fun p => frameCompletion (roundFrames hk Λ F x p.1) p.2) =
      (remainingHaar (prefixSpace d k)).map (frameCompletion F) := by
  let f : (Point d × Point d × Point d) × Rotations d → Rotations d :=
    fun p => frameCompletion (roundFrames hk Λ F x p.1) p.2
  let g : Point d × Rotations d → Rotations d :=
    fun p => frameCompletion (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x p.1) p.2
  have hf : Measurable f := (measurable_frameCompletion (d := d)).comp
    (f := fun p : (Point d × Point d × Point d) × Rotations d =>
      (roundFrames hk Λ F x p.1,p.2))
    (((measurable_roundFrames hk Λ).comp
      (f := fun p : (Point d × Point d × Point d) × Rotations d => ((F,x),p.1))
      (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have hg : Measurable g := by unfold g; fun_prop
  have hh (z : Point d) :
      (((stdGaussian (Point d)).prod (stdGaussian (Point d))).prod
        (remainingHaar (prefixSpace d (k+2)))).map (fun p => f ((z,p.1),p.2)) =
        (remainingHaar (prefixSpace d (k+1))).map (fun h => g (z,h)) := by
    exact filledForward_law hk (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x z)
      (Λ ((frameTransport (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x z)).symm x))
  have he := eliminate_fresh_residual (μ := stdGaussian (Point d))
    (γ := (stdGaussian (Point d)).prod (stdGaussian (Point d)))
    (η := remainingHaar (prefixSpace d (k+1)))
    (η' := remainingHaar (prefixSpace d (k+2)))
    (step := id) measurable_id hf hg hh
  rw [Measure.map_id] at he
  exact he.trans (inverseFrameUpdate_law (Nat.lt_of_succ_lt hk) F x)

lemma roundFrames_compatible {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d) :
    CompatibleFrames (prefixSpace d k) F (roundFrames hk Λ F x r) := by
  unfold roundFrames
  exact compatibleFrames_trans (compatibleFrames_inverseUpdate _ _ _ _)
    (compatibleFrames_mono (prefixSpace_mono d (Nat.le_succ k))
      (compatibleFrames_forwardUpdate _ _ _ _))

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

@[fun_prop] lemma measurable_roundCoordinate {d k : ℕ} (hk : k+1 < d) :
    Measurable (fun p : (Frames d × Point d) × Point d => roundCoordinate hk p.1.1 p.1.2 p.2) := by
  let Z := (Frames d × Point d) × Point d
  let f : Z → Frames d := fun p => inverseFrameUpdate (Nat.lt_of_succ_lt hk) p.1.1 p.1.2 p.2
  have hf : Measurable f := (measurable_inverseFrameUpdate (Nat.lt_of_succ_lt hk)).comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  change Measurable (fun p : Z => (frameTransport (f p)).symm p.1.2)
  exact (measurable_inverse_frameTransport (d := d)).comp
    (f := fun p : Z => (f p,p.1.2)) (hf.prodMk measurable_fst.snd)

lemma roundCoordinate_mem {d k : ℕ} (hk : k+1 < d) (F : Frames d) (x g : Point d) :
    roundCoordinate hk F x g ∈
      frameSpace (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x g).2 (prefixSpace d (k+1)) := by
  apply frameTransport_preimage_mem
  exact mem_frameSpace_extendFrame _ _ _

lemma replyCoordinate_mem {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d) :
    Λ (roundCoordinate hk F x r.1) ∈ frameSpace (roundFrames hk Λ F x r).2 (prefixSpace d (k+2)) :=
  mem_frameSpace_filledExtend hk _ _ _

theorem roundReply_correct {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d)
    {H : Rotations d} (hH : H ∈ subspaceStabilizer (prefixSpace d (k+2))) :
    linearReply Λ (frameCompletion (roundFrames hk Λ F x r) H) x =
      (⟪roundCoordinate hk F x r.1, Λ (roundCoordinate hk F x r.1)⟫ / 2,
        frameTransport (roundFrames hk Λ F x r) (Λ (roundCoordinate hk F x r.1))) := by
  let F₁ := inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x r.1
  have hc : CompatibleFrames (prefixSpace d (k+1)) F₁ (roundFrames hk Λ F x r) :=
    compatibleFrames_forwardUpdate hk _ _ _
  obtain ⟨H',hH',he⟩ := compatibleFrames_reconstruct _ hc
    (subspaceStabilizer_anti (prefixSpace_mono d (Nat.le_succ (k+1))) hH)
  have hq : (rotationIsometry (frameCompletion (roundFrames hk Λ F x r) H)).symm x =
      roundCoordinate hk F x r.1 := by
    rw [he]
    exact frameCompletion_symm_eq_transport _ F₁ hH' (mem_frameSpace_extendFrame _ _ _)
  unfold linearReply
  simp only [hq]
  rw [frameCompletion_eq_transport _ _ hH (replyCoordinate_mem hk Λ F x r)]

theorem roundFrames_span_growth {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d)
    (hq : (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry F.2⁻¹ r.1) ≠ 0)
    (hr : (prefixSpace d (k+1))ᗮ.orthogonalProjectionOnto
      (rotationIsometry (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x r.1).2⁻¹ r.2.1) ≠ 0) :
    frameSpace (roundFrames hk Λ F x r).2 (prefixSpace d (k+2)) ≤
      ((frameSpace F.2 (prefixSpace d k) ⊔ ℝ ∙ r.1) ⊔
        (frameSpace F.2 (prefixSpace d k) ⊔ ℝ ∙ r.1).map Λ.toLinearMap) ⊔ ℝ ∙ r.2.1 := by
  let F₁ := inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x r.1
  let K := frameSpace F.2 (prefixSpace d k) ⊔ ℝ ∙ r.1
  have hK : frameSpace F₁.2 (prefixSpace d (k+1)) ≤ K :=
    frameSpace_extendFrame_le _ _ _ hq
  have hu : roundCoordinate hk F x r.1 ∈ K := hK (roundCoordinate_mem hk F x r.1)
  have hΛ : Λ (roundCoordinate hk F x r.1) ∈ K.map Λ.toLinearMap := ⟨_,hu,rfl⟩
  have hy : ℝ ∙ Λ (roundCoordinate hk F x r.1) ≤ K.map Λ.toLinearMap := by
    apply Submodule.span_le.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hΛ
  exact (frameSpace_filledExtend_le hk F₁.2 _ _ hr).trans
    (sup_le_sup (sup_le_sup hK hy) le_rfl)

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TapeSnocEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling

lemma seedTapeSnoc_law {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    (μ : Measure Ω) (γ : Measure R) [SFinite μ] [SigmaFinite γ] (n : ℕ) :
    (((μ.prod (Measure.pi (fun _ : Fin n => γ))).prod γ).map (seedTapeSnoc n)) =
      μ.prod (Measure.pi (fun _ : Fin (n+1) => γ)) := by
  change ((μ.prod (Measure.pi (fun _ : Fin n => γ))).prod γ).map
    (((MeasurableEquiv.refl Ω).prodCongr (tapeSnocEquiv n)) ∘ MeasurableEquiv.prodAssoc) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.prodAssoc_prod]
  have h := Measure.map_prod_map μ ((Measure.pi (fun _ : Fin n => γ)).prod γ)
    measurable_id (tapeSnocEquiv n).measurable
  rw [Measure.map_id] at h
  change (μ.prod ((Measure.pi (fun _ : Fin n => γ)).prod γ)).map (Prod.map id (tapeSnocEquiv n)) = _
  rw [← h]
  have ht : (tapeSnocEquiv (R := R) n : (Fin n → R) × R → _) =
    fun p => Fin.snoc (α := fun _ : Fin (n+1) => R) p.1 p.2 := by funext p; exact tapeSnocEquiv_apply n p
  rw [ht, pi_snoc_law]

section Run
variable {S : ℕ → Type*} {Ω R : Type*}
  [∀ n, MeasurableSpace (S n)] [MeasurableSpace Ω] [MeasurableSpace R]

lemma measurable_stateRun (init : Ω → S 0) (hi : Measurable init)
    (step : (n : ℕ) → S n × R → S (n+1)) (hs : ∀ n, Measurable (step n)) (n : ℕ) :
    Measurable (stateRun init step n) := by
  induction n with
  | zero => exact hi.comp measurable_fst
  | succ n ih =>
    apply (hs n).comp
    exact (ih.comp (measurable_fst.prodMk (Measurable.of_eval
      (fun index => (measurable_pi_apply index.castSucc).comp measurable_snd)))).prodMk
        (by fun_prop)

lemma stateRun_law (μ : Measure Ω) (γ : Measure R) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (init : Ω → S 0) (hi : Measurable init)
    (step : (n : ℕ) → S n × R → S (n+1)) (hs : ∀ n, Measurable (step n)) (n : ℕ) :
    (μ.prod (Measure.pi (fun _ : Fin n => γ))).map (stateRun init step n) =
      stateLaw (μ.map init) γ step n := by
  induction n with
  | zero =>
    change (μ.prod (Measure.pi (fun _ : Fin 0 => γ))).map (init ∘ Prod.fst) = μ.map init
    rw [← Measure.map_map hi measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  | succ n ih =>
    rw [← seedTapeSnoc_law μ γ n, Measure.map_map (measurable_stateRun init hi step hs (n+1))
      (seedTapeSnoc n).measurable]
    change _ = (((stateLaw (μ.map init) γ step n).prod γ).map (step n))
    rw [← ih]
    have h := Measure.map_prod_map (μ.prod (Measure.pi (fun _ : Fin n => γ))) γ
      (measurable_stateRun init hi step hs n) measurable_id
    rw [Measure.map_id] at h
    rw [h, Measure.map_map (hs n) ((measurable_stateRun init hi step hs n).prodMap measurable_id)]
    congr 1
    funext p
    exact stateRun_snoc init step n p

lemma stateRun_ae_invariant (μ : Measure Ω) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (init : Ω → S 0) (hi : Measurable init)
    (step : (n : ℕ) → S n × R → S (n+1)) (hs : ∀ n, Measurable (step n))
    (P : (n : ℕ) → S n → Prop) (N : ℕ)
    (good : (n : ℕ) → S n × R → Prop)
    (hgood : ∀ n, MeasurableSet {z | good n z})
    (hgood_ae : ∀ n < N, ∀ s, ∀ᵐ r ∂γ, good n (s,r))
    (h0 : ∀ ω, P 0 (init ω))
    (hstep : ∀ n < N, ∀ s r, P n s → good n (s,r) → P (n+1) (step n (s,r))) :
    ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin N => γ)), P N (stateRun init step N p) := by
  have h : ∀ n ≤ N, ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin n => γ)),
      P n (stateRun init step n p) := by
    intro n hn
    induction n with
    | zero => exact Filter.Eventually.of_forall (fun p => h0 p.1)
    | succ n ih =>
      rw [← seedTapeSnoc_law μ γ n, (seedTapeSnoc n).measurableEmbedding.ae_map_iff]
      simp only [stateRun_snoc]
      have hg : ∀ᵐ p ∂(μ.prod (Measure.pi (fun _ : Fin n => γ))).prod γ,
          good n (stateRun init step n p.1,p.2) := by
        apply (Measure.ae_prod_iff_ae_ae ((hgood n).preimage
          ((measurable_stateRun init hi step hs n).prodMap measurable_id))).mpr
        exact Filter.Eventually.of_forall (fun p => hgood_ae n (by omega) _)
      filter_upwards [hg, Measure.quasiMeasurePreserving_fst.ae (ih (by omega))] with p hp hP
      exact hstep n (by omega) _ _ hP hp
  exact h N le_rfl

end Run
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_LinearHistory
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling.LowerBound
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma remainingHaar_bot (d : ℕ) : remainingHaar (⊥ : Submodule ℝ (Point d)) = rotationHaar d := by
  have hmem (P : Rotations d) : P ∈ subspaceStabilizer (⊥ : Submodule ℝ (Point d)) := by
    intro x hx
    have hx' : x = 0 := hx
    simp [hx']
  have hi : (remainingHaar (⊥ : Submodule ℝ (Point d))).IsMulLeftInvariant := by
    constructor
    intro P
    change ((subspaceHaar (⊥ : Submodule ℝ (Point d))).map Subtype.val).map (P * ·) = _
    let P' : subspaceStabilizer (⊥ : Submodule ℝ (Point d)) := ⟨P,hmem P⟩
    rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
    calc
      _ = ((subspaceHaar (⊥ : Submodule ℝ (Point d))).map (P' * ·)).map Subtype.val := by
        rw [Measure.map_map measurable_subtype_coe (by fun_prop)]
        rfl
      _ = _ := by rw [map_mul_left_eq_self]; rfl
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    (remainingHaar (⊥ : Submodule ℝ (Point d))) (rotationHaar d)
  have hmass := congrArg (fun μ : Measure (Rotations d) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hmass
  have hc : (remainingHaar (⊥ : Submodule ℝ (Point d))).haarScalarFactor (rotationHaar d) = 1 :=
    ENNReal.coe_injective hmass.symm
  rwa [hc, one_smul] at h

lemma measurable_linearHistory {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (n : ℕ) :
    Measurable (fun p : Ω × Rotations d => linearHistory A Λ p.2 p.1 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [linearHistory]
    split_ifs with hn
    · have hq := (A.query_measurable ⟨n,hn⟩).comp (measurable_fst.prodMk ih)
      have hr := (measurable_linearReply Λ).comp (measurable_snd.prodMk hq)
      apply Measurable.of_eval
      intro j
      by_cases hj : j = ⟨n,hn⟩
      · subst j
        simpa only [Function.update_self, Function.comp_def] using hr
      · simpa only [Function.update_of_ne hj, Function.comp_def] using (measurable_pi_apply j).comp ih
    · exact ih

lemma measurable_initialRevealState {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ} :
    Measurable (initialRevealState (Ω := Ω) (d := d) (q := q)) := by
  unfold initialRevealState
  fun_prop

lemma measurable_revealStep {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) (n : ℕ) :
    Measurable (revealStep A Λ hd n) := by
  let Z := RevealState Ω d q n × RoundRandom d
  have hseed : Measurable (fun p : Z => p.1.1) := measurable_fst.fst
  have hframe : Measurable (fun p : Z => p.1.2.1) := measurable_fst.snd.fst
  have hhist : Measurable (fun p : Z => p.1.2.2.1) := measurable_fst.snd.snd.fst
  have htape : Measurable (fun p : Z => Fin.snoc (α := fun _ : Fin (n+1) => Point d × Point d)
      p.1.2.2.2 (p.2.1,p.2.2.1)) := measurable_fin_snoc n |>.comp
    (measurable_fst.snd.snd.snd.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst))
  unfold revealStep
  split_ifs with hn
  · have hk : 2*n+1 < d := by omega
    let x : Z → Point d := fun p => A.query ⟨n,hn⟩ (p.1.1,p.1.2.2.1)
    have hx : Measurable x := (A.query_measurable _).comp (hseed.prodMk hhist)
    let F : Z → Frames d := fun p => roundFrames hk Λ p.1.2.1 (x p) p.2
    have hF : Measurable F := (measurable_roundFrames hk Λ).comp
      (f := fun p : Z => ((p.1.2.1,x p),p.2)) ((hframe.prodMk hx).prodMk measurable_snd)
    let u : Z → Point d := fun p => roundCoordinate hk p.1.2.1 (x p) p.2.1
    have hu : Measurable u := (measurable_roundCoordinate hk).comp
      (f := fun p : Z => ((p.1.2.1,x p),p.2.1)) ((hframe.prodMk hx).prodMk measurable_snd.fst)
    have hΛu : Measurable (fun p : Z => Λ (u p)) := Λ.continuous.measurable.comp hu
    have hreply : Measurable (fun p : Z => (⟪u p,Λ (u p)⟫ / 2,frameTransport (F p) (Λ (u p)))) :=
      ((hu.inner hΛu).div_const 2).prodMk ((measurable_frameTransport (d := d)).comp
        (f := fun p : Z => (F p,Λ (u p))) (hF.prodMk hΛu))
    have hupdate : Measurable (fun p : Z => Function.update p.1.2.2.1 ⟨n,hn⟩
        (⟪u p,Λ (u p)⟫ / 2,frameTransport (F p) (Λ (u p)))) := by
      apply Measurable.of_eval
      intro j
      by_cases hj : j = ⟨n,hn⟩
      · subst j; simpa only [Function.update_self, Function.comp_def] using hreply
      · simpa only [Function.update_of_ne hj, Function.comp_def] using (measurable_pi_apply j).comp hhist
    exact hseed.prodMk (hF.prodMk (hupdate.prodMk htape))
  · exact hseed.prodMk (hframe.prodMk (hhist.prodMk htape))

lemma initial_historyConsistent {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (ω : Ω) :
    HistoryConsistent A Λ 0 (initialRevealState ω) := by
  intro H hH
  rfl

lemma revealStep_historyConsistent {Ω : Type*} [MeasurableSpace Ω] {d q n : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) (hn : n < q)
    (s : RevealState Ω d q n) (r : RoundRandom d) (hs : HistoryConsistent A Λ n s) :
    HistoryConsistent A Λ (n+1) (revealStep A Λ hd n (s,r)) := by
  have hk : 2*n+1 < d := by omega
  let x := A.query ⟨n,hn⟩ (s.1,s.2.2.1)
  let F := roundFrames hk Λ s.2.1 x r
  intro H hH
  have hH₂ : H ∈ subspaceStabilizer (prefixSpace d (2*n+2)) := by
    simpa only [Nat.mul_add, Nat.mul_one] using hH
  have hH₀ : H ∈ subspaceStabilizer (prefixSpace d (2*n)) :=
    subspaceStabilizer_anti (prefixSpace_mono d (by omega)) hH₂
  obtain ⟨H',hH',he⟩ := compatibleFrames_reconstruct _ (roundFrames_compatible hk Λ s.2.1 x r) hH₀
  have hh : s.2.2.1 = linearHistory A Λ (frameCompletion F H) s.1 n := by
    rw [he]
    exact hs H' hH'
  change (revealStep A Λ hd n (s,r)).2.2.1 =
    linearHistory A Λ (frameCompletion (revealStep A Λ hd n (s,r)).2.1 H)
      (revealStep A Λ hd n (s,r)).1 (n+1)
  simp only [revealStep, dite_eq_left hn, linearHistory]
  rw [← hh]
  congr 1
  exact (roundReply_correct hk Λ s.2.1 x r hH₂).symm

lemma measurable_completeRevealState {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ} (n : ℕ) :
    Measurable (completeRevealState (Ω := Ω) (d := d) (q := q) n) :=
  measurable_fst.fst.prodMk ((measurable_frameCompletion (d := d)).comp
    (f := fun p : RevealState Ω d q n × Rotations d => (p.1.2.1,p.2))
    (measurable_fst.snd.fst.prodMk measurable_snd))

lemma revealStep_completion_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (n : ℕ) (hn : n < q) (s : RevealState Ω d q n) :
    ((roundRandomLaw d).prod (remainingHaar (prefixSpace d (2*(n+1))))).map
      (fun p => completeRevealState (n+1) (revealStep A Λ hd n (s,p.1),p.2)) =
      (remainingHaar (prefixSpace d (2*n))).map (fun h => completeRevealState n (s,h)) := by
  have hk : 2*n+1 < d := by omega
  have he := congrArg (fun ν : Measure (Rotations d) => ν.map (fun O => (s.1,O)))
    (roundFrames_law hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)))
  have hf : Measurable (fun p : RoundRandom d × Rotations d =>
      frameCompletion (roundFrames hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) p.1) p.2) :=
    (measurable_frameCompletion (d := d)).comp
      (f := fun p : RoundRandom d × Rotations d =>
        (roundFrames hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) p.1,p.2))
      (((measurable_roundFrames hk Λ).comp
        (f := fun p : RoundRandom d × Rotations d =>
          ((s.2.1,A.query ⟨n,hn⟩ (s.1,s.2.2.1)),p.1))
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  rw [Measure.map_map (by fun_prop) hf, Measure.map_map (by fun_prop) (by fun_prop)] at he
  simpa only [completeRevealState,revealStep,dite_eq_left hn,roundRandomLaw,
    Nat.mul_add,Nat.mul_one,Function.comp_def] using he

theorem revealState_completion_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    ((stateLaw (μ.map (initialRevealState (d := d) (q := q))) (roundRandomLaw d)
        (revealStep A Λ hd) q).prod (remainingHaar (prefixSpace d (2*q)))).map
      (completeRevealState q) = μ.prod (rotationHaar d) := by
  have hi := measurable_initialRevealState (Ω := Ω) (d := d) (q := q)
  haveI : IsProbabilityMeasure (μ.map (initialRevealState (d := d) (q := q))) := Measure.isProbabilityMeasure_map hi.aemeasurable
  rw [stateLaw_completion _ _ _ (measurable_revealStep A Λ hd)
    (fun n => remainingHaar (prefixSpace d (2*n)))
    (fun n => completeRevealState (Ω := Ω) (d := d) (q := q) n)
    (fun n => measurable_completeRevealState n) q
    (fun n hn s => revealStep_completion_law A Λ hd n hn s)]
  simp only [Nat.mul_zero, prefixSpace_zero, remainingHaar_bot]
  have hp := Measure.map_prod_map μ (rotationHaar d) hi measurable_id
  rw [Measure.map_id] at hp
  rw [hp,Measure.map_map (measurable_completeRevealState 0) (hi.prodMap measurable_id)]
  convert (Measure.map_id (μ := μ.prod (rotationHaar d))) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext p
  simp [completeRevealState,initialRevealState,frameCompletion]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma measurable_finishFrame {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d) : Measurable (finishFrame A hd) := by
  apply (measurable_inverseFrameUpdate hd).comp
    (f := fun p : RevealState Ω d q q × Point d =>
      (p.1.2.1,A.output (p.1.1,p.1.2.2.1),p.2))
  exact measurable_fst.snd.fst.prodMk
    ((A.output_measurable.comp (measurable_fst.fst.prodMk measurable_fst.snd.snd.fst)).prodMk measurable_snd)

lemma measurable_finishComplete {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d) : Measurable (finishComplete A hd) := by
  exact measurable_fst.fst.fst.prodMk ((measurable_frameCompletion (d := d)).comp
    (f := fun p : (RevealState Ω d q q × Point d) × Rotations d =>
      (finishFrame A hd p.1,p.2))
    (((measurable_finishFrame A hd).comp measurable_fst).prodMk measurable_snd))

lemma finishComplete_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d)
    (ν : Measure (RevealState Ω d q q)) [IsProbabilityMeasure ν] :
    ((ν.prod (stdGaussian (Point d))).prod
      (remainingHaar (prefixSpace d (2*q+1)))).map (finishComplete A hd) =
      (ν.prod (remainingHaar (prefixSpace d (2*q)))).map (completeRevealState q) := by
  have hlocal (s : RevealState Ω d q q) :
      ((stdGaussian (Point d)).prod (remainingHaar (prefixSpace d (2*q+1)))).map
          (fun p => finishComplete A hd ((s,p.1),p.2)) =
        (remainingHaar (prefixSpace d (2*q))).map
          (fun h => completeRevealState q (s,h)) := by
    have he := congrArg (fun η : Measure (Rotations d) => η.map (fun O => (s.1,O)))
      (inverseFrameUpdate_law hd s.2.1 (A.output (s.1,s.2.2.1)))
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] at he
    exact he
  have he := eliminate_fresh_residual (μ := ν) (γ := stdGaussian (Point d))
    (η := remainingHaar (prefixSpace d (2*q)))
    (η' := remainingHaar (prefixSpace d (2*q+1)))
    (step := id) measurable_id (measurable_finishComplete A hd)
    (measurable_completeRevealState q) hlocal
  rwa [Measure.map_id] at he

lemma finishCoordinate_mem {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d) (p : RevealState Ω d q q × Point d)
    (hg : (prefixSpace d (2*q))ᗮ.orthogonalProjectionOnto (rotationIsometry p.1.2.1.2⁻¹ p.2) ≠ 0) :
    finishCoordinate A hd p ∈ frameSpace p.1.2.1.2 (prefixSpace d (2*q)) ⊔ ℝ ∙ p.2 := by
  have hx : A.output (p.1.1,p.1.2.2.1) ∈ frameSpace (finishFrame A hd p).1
      (prefixSpace d (2*q+1)) := by
    simp only [finishFrame,inverseFrameUpdate_eq]
    exact mem_frameSpace_extendFrame hd _ _
  have hu := frameTransport_preimage_mem _ (finishFrame A hd p) hx
  have hb := frameSpace_extendFrame_le hd p.1.2.1.2 p.2 hg
  exact hb hu

lemma finishCoordinate_correct {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q < d)
    (s : RevealState Ω d q q) (g : Point d) (hs : HistoryConsistent A Λ q s)
    {H : Rotations d} (hH : H ∈ subspaceStabilizer (prefixSpace d (2*q+1))) :
    finishCoordinate A hd (s,g) =
      (rotationIsometry (finishComplete A hd ((s,g),H)).2).symm
        (A.output (s.1,linearHistory A Λ (finishComplete A hd ((s,g),H)).2 s.1 q)) := by
  have hH₀ : H ∈ subspaceStabilizer (prefixSpace d (2*q)) :=
    subspaceStabilizer_anti (prefixSpace_mono d (Nat.le_succ _)) hH
  obtain ⟨H',hH',he⟩ := compatibleFrames_reconstruct _
    (compatibleFrames_inverseUpdate hd s.2.1 (A.output (s.1,s.2.2.1)) g) hH₀
  have hh : s.2.2.1 = linearHistory A Λ (finishComplete A hd ((s,g),H)).2 s.1 q := by
    change s.2.2.1 = linearHistory A Λ (frameCompletion (finishFrame A hd (s,g)) H) s.1 q
    rw [finishFrame,he]
    exact hs H' hH'
  rw [← hh]
  symm
  apply frameCompletion_symm_eq_transport _ (finishFrame A hd (s,g)) hH
  simp only [finishFrame,inverseFrameUpdate_eq]
  exact mem_frameSpace_extendFrame hd _ _

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma powerHull_mono_base (L : E →ₗ[ℝ] E) (n : ℕ) {K K' : Submodule ℝ E} (h : K ≤ K') :
    powerHull L n K ≤ powerHull L n K' := by
  induction n with
  | zero => exact h
  | succ n ih => exact sup_le_sup h (Submodule.map_mono ih)

lemma le_powerHull (L : E →ₗ[ℝ] E) (n : ℕ) (K : Submodule ℝ E) : K ≤ powerHull L n K := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_sup_left

lemma powerHull_le_succ (L : E →ₗ[ℝ] E) (n : ℕ) (K : Submodule ℝ E) :
    powerHull L n K ≤ powerHull L (n+1) K := by
  induction n with
  | zero => exact le_sup_left
  | succ n ih => exact sup_le_sup le_rfl (Submodule.map_mono ih)

lemma tapeHull_snoc {n : ℕ} (t : Fin n → E × E) (a b : E) :
    tapeHull (Fin.snoc (α := fun _ : Fin (n+1) => E × E) t (a,b)) =
      (tapeHull t ⊔ ℝ ∙ a) ⊔ ℝ ∙ b := by
  unfold tapeHull
  simp only [← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
    · refine Fin.lastCases ?_ (fun j => ?_) i hi
      · simp only [Fin.snoc_last]; intro h; exact Or.inl (Or.inr h.symm)
      · simp only [Fin.snoc_castSucc]; intro h; exact Or.inl (Or.inl (Or.inl ⟨j,h⟩))
    · refine Fin.lastCases ?_ (fun j => ?_) i hi
      · simp only [Fin.snoc_last]; intro h; exact Or.inr h.symm
      · simp only [Fin.snoc_castSucc]; intro h; exact Or.inl (Or.inl (Or.inr ⟨j,h⟩))
  · rintro (((⟨i,hi⟩ | ⟨i,hi⟩) | h) | h)
    · exact Or.inl ⟨i.castSucc, by simpa only [Fin.snoc_castSucc] using hi⟩
    · exact Or.inr ⟨i.castSucc, by simpa only [Fin.snoc_castSucc] using hi⟩
    · exact Or.inl ⟨Fin.last n, by simpa only [Fin.snoc_last] using h.symm⟩
    · exact Or.inr ⟨Fin.last n, by simpa only [Fin.snoc_last] using h.symm⟩

lemma powerHull_round_growth (L : E →ₗ[ℝ] E) {n : ℕ} {K : Submodule ℝ E}
    {t : Fin n → E × E} (hK : K ≤ powerHull L n (tapeHull t)) (a b : E) :
    ((K ⊔ ℝ ∙ a) ⊔ (K ⊔ ℝ ∙ a).map L) ⊔ ℝ ∙ b ≤
      powerHull L (n+1) (tapeHull (Fin.snoc (α := fun _ : Fin (n+1) => E × E) t (a,b))) := by
  rw [tapeHull_snoc]
  let K' := (tapeHull t ⊔ ℝ ∙ a) ⊔ ℝ ∙ b
  have hbase : tapeHull t ≤ K' := le_sup_left.trans le_sup_left
  have ha : ℝ ∙ a ≤ K' := le_sup_right.trans le_sup_left
  have hb : ℝ ∙ b ≤ K' := le_sup_right
  have hK' : K ⊔ ℝ ∙ a ≤ powerHull L n K' := sup_le
    (hK.trans (powerHull_mono_base L n hbase)) (ha.trans (le_powerHull L n K'))
  exact sup_le (sup_le (hK'.trans (powerHull_le_succ L n K'))
    ((Submodule.map_mono hK').trans le_sup_right)) (hb.trans (le_powerHull L (n+1) K'))

end
end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma measurable_frameProjection (d k : ℕ) :
    Measurable (fun p : Rotations d × Point d =>
      (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry p.1⁻¹ p.2)) := by
  fun_prop

lemma measurableSet_roundGood {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q+1 ≤ d) (n : ℕ) :
    MeasurableSet {p | roundGood A hd n p} := by
  unfold roundGood
  split_ifs with hn
  · let Z := RevealState Ω d q n × RoundRandom d
    have hk : 2*n < d := by omega
    let x : Z → Point d := fun p => A.query ⟨n,hn⟩ (p.1.1,p.1.2.2.1)
    have hx : Measurable x := (A.query_measurable _).comp
      (measurable_fst.fst.prodMk measurable_fst.snd.snd.fst)
    let F : Z → Frames d := fun p => inverseFrameUpdate hk p.1.2.1 (x p) p.2.1
    have hF : Measurable F := (measurable_inverseFrameUpdate hk).comp
      (f := fun p : Z => (p.1.2.1,x p,p.2.1))
      (measurable_fst.snd.fst.prodMk (hx.prodMk measurable_snd.fst))
    have h₁ : Measurable (fun p : Z =>
        (prefixSpace d (2*n))ᗮ.orthogonalProjectionOnto (rotationIsometry p.1.2.1.2⁻¹ p.2.1)) :=
      (measurable_frameProjection d (2*n)).comp
      (f := fun p : Z => (p.1.2.1.2,p.2.1))
      (measurable_fst.snd.fst.snd.prodMk measurable_snd.fst)
    have h₂ : Measurable (fun p : Z =>
        (prefixSpace d (2*n+1))ᗮ.orthogonalProjectionOnto (rotationIsometry (F p).2⁻¹ p.2.2.1)) :=
      (measurable_frameProjection d (2*n+1)).comp
      (f := fun p : Z => ((F p).2,p.2.2.1)) (hF.snd.prodMk measurable_snd.snd.fst)
    exact ((measurableSet_singleton 0).compl.preimage h₁).inter
      ((measurableSet_singleton 0).compl.preimage h₂)
  · exact MeasurableSet.univ

lemma ae_roundGood {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q+1 ≤ d) (n : ℕ) (hn : n < q)
    (s : RevealState Ω d q n) : ∀ᵐ r ∂roundRandomLaw d, roundGood A hd n (s,r) := by
  have hk : 2*n < d := by omega
  have hk' : 2*n+1 < d := by omega
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_roundGood A hd n).preimage (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [ae_frameGaussian_nonzero hk s.2.1.2] with g hg
  have h := (Measure.quasiMeasurePreserving_fst
    (μ := stdGaussian (Point d)) (ν := stdGaussian (Point d))).ae
    (ae_frameGaussian_nonzero hk'
      (inverseFrameUpdate hk s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) g).2)
  filter_upwards [h] with r hr
  simpa only [roundGood,dite_eq_left hn, id_eq] using And.intro hg hr

lemma revealStep_spanConsistent {Ω : Type*} [MeasurableSpace Ω] {d q n : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (hn : n < q) (s : RevealState Ω d q n) (r : RoundRandom d)
    (hs : SpanConsistent Λ n s) (hg : roundGood A hd n (s,r)) :
    SpanConsistent Λ (n+1) (revealStep A Λ hd n (s,r)) := by
  have hk : 2*n+1 < d := by omega
  simp only [roundGood,dite_eq_left hn] at hg
  have h := (roundFrames_span_growth hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) r hg.1 hg.2).trans
    (powerHull_round_growth Λ.toLinearMap hs r.1 r.2.1)
  have hF : (revealStep A Λ hd n (s,r)).2.1 =
      roundFrames hk Λ s.2.1 (A.query ⟨n,hn⟩ (s.1,s.2.2.1)) r := by
    simp only [revealStep,dite_eq_left hn]
  have ht : (revealStep A Λ hd n (s,r)).2.2.2 =
      Fin.snoc (α := fun _ : Fin (n+1) => Point d × Point d) s.2.2.2 (r.1,r.2.1) := by
    simp only [revealStep,dite_eq_left hn]
  unfold SpanConsistent
  rw [hF,ht,show 2*(n+1) = 2*n+2 by omega]
  exact h

lemma revealRun_historyConsistent {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (n : ℕ) (hn : n ≤ q) (p : Ω × (Fin n → RoundRandom d)) :
    HistoryConsistent A Λ n (stateRun initialRevealState (revealStep A Λ hd) n p) := by
  induction n with
  | zero => exact initial_historyConsistent A Λ p.1
  | succ n ih =>
    exact revealStep_historyConsistent A Λ hd (by omega) _ _ (ih (by omega) _)

lemma revealRun_spanConsistent {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin q => roundRandomLaw d)),
      SpanConsistent Λ q (stateRun initialRevealState (revealStep A Λ hd) q p) := by
  apply stateRun_ae_invariant μ (roundRandomLaw d) initialRevealState
    measurable_initialRevealState (revealStep A Λ hd) (measurable_revealStep A Λ hd)
    (fun n => SpanConsistent Λ n) q (roundGood A hd) (measurableSet_roundGood A hd)
    (ae_roundGood A hd)
  · intro ω
    simp [SpanConsistent,initialRevealState,frameSpace,prefixSpace_zero,powerHull]
  · intro n hn s r hs hg
    exact revealStep_spanConsistent A Λ hd hn s r hs hg

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma orbitHull_mono {ι : Type*} (L : E →ₗ[ℝ] E) {m n : ℕ} (hmn : m ≤ n) (t : ι → E) :
    orbitHull L m t ≤ orbitHull L n t := by
  apply Submodule.span_mono
  rintro v ⟨i,j,hj,rfl⟩
  exact ⟨i,j,hj.trans hmn,rfl⟩

lemma map_orbitHull_le_succ {ι : Type*} (L : E →ₗ[ℝ] E) (n : ℕ) (t : ι → E) :
    (orbitHull L n t).map L ≤ orbitHull L (n+1) t := by
  rw [orbitHull,Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro v ⟨u,⟨i,j,hj,rfl⟩,rfl⟩
  apply Submodule.subset_span
  refine ⟨i,j+1,Nat.succ_le_succ hj,?_⟩
  exact (Function.iterate_succ_apply' L j (t i)).symm

lemma span_range_le_orbitHull {ι : Type*} (L : E →ₗ[ℝ] E) (n : ℕ) (t : ι → E) :
    Submodule.span ℝ (Set.range t) ≤ orbitHull L n t := by
  apply Submodule.span_le.mpr
  rintro v ⟨i,rfl⟩
  exact Submodule.subset_span ⟨i,0,Nat.zero_le n,rfl⟩

lemma powerHull_le_orbitHull {ι : Type*} (L : E →ₗ[ℝ] E) (n : ℕ) (t : ι → E)
    {K : Submodule ℝ E} (hK : K ≤ Submodule.span ℝ (Set.range t)) :
    powerHull L n K ≤ orbitHull L n t := by
  induction n with
  | zero => exact hK.trans (span_range_le_orbitHull L 0 t)
  | succ n ih =>
    exact sup_le (hK.trans (span_range_le_orbitHull L (n+1) t))
      ((Submodule.map_mono ih).trans (map_orbitHull_le_succ L n t))

end
end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_CouplingNoise
attribute [-instance] _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling.LowerBound

lemma measurable_couplingState {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    Measurable (couplingState A Λ hd) := by
  exact (((measurable_stateRun initialRevealState measurable_initialRevealState
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q).comp
    measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd

lemma couplingState_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    (couplingLaw μ d q).map (couplingState A Λ hd) =
      ((stateLaw (μ.map initialRevealState) (roundRandomLaw d)
        (revealStep A Λ hd) q).prod (stdGaussian (Point d))).prod
        (remainingHaar (prefixSpace d (2*q+1))) := by
  rw [← stateRun_law μ (roundRandomLaw d) initialRevealState measurable_initialRevealState
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q]
  have hr := measurable_stateRun initialRevealState measurable_initialRevealState
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q
  simp only [couplingLaw]
  rw [← Measure.map_id (μ := stdGaussian (Point d)),
    Measure.map_prod_map _ _ hr measurable_id,
    ← Measure.map_id (μ := remainingHaar (prefixSpace d (2*q+1))),
    Measure.map_prod_map _ _ (hr.prodMap measurable_id) measurable_id]
  simp only [Measure.map_id]
  rfl

theorem coupling_complete_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    (couplingLaw μ d q).map (finishComplete A (by omega) ∘ couplingState A Λ hd) =
      μ.prod (rotationHaar d) := by
  rw [← Measure.map_map (measurable_finishComplete A (by omega)) (measurable_couplingState A Λ hd),
    couplingState_law]
  have : IsProbabilityMeasure
      (μ.map (initialRevealState (Ω := Ω) (d := d) (q := q))) :=
    Measure.isProbabilityMeasure_map (measurable_initialRevealState (Ω := Ω) (d := d) (q := q)).aemeasurable
  have := stateLaw_probability (μ.map initialRevealState) (roundRandomLaw d)
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q
  rw [finishComplete_law, revealState_completion_law μ A Λ hd]

lemma revealRun_tape {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (n : ℕ) (p : Ω × (Fin n → RoundRandom d)) :
    (stateRun initialRevealState (revealStep A Λ hd) n p).2.2.2 =
      fun i => ((p.2 i).1,(p.2 i).2.1) := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have ht : (stateRun initialRevealState (revealStep A Λ hd) (n+1) p).2.2.2 =
        Fin.snoc (α := fun _ : Fin (n+1) => Point d × Point d)
          (stateRun initialRevealState (revealStep A Λ hd) n (p.1,Fin.init p.2)).2.2.2
          ((p.2 (Fin.last n)).1,(p.2 (Fin.last n)).2.1) := by
      simp only [stateRun,revealStep]
      split_ifs <;> rfl
    rw [ht,ih]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.init]

lemma tapeHull_le_couplingColumns {Ω : Type*} {d q : ℕ} (p : CouplingNoise Ω d q) :
    tapeHull (fun i => ((p.1.1.2 i).1,(p.1.1.2 i).2.1)) ⊔ ℝ ∙ p.1.2 ≤
      Submodule.span ℝ (Set.range (couplingColumns p)) := by
  apply sup_le
  · apply Submodule.span_le.mpr
    rintro v (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · apply Submodule.subset_span
      exact ⟨(Fin.castAdd q i).castSucc, by simp only [couplingColumns,Fin.snoc_castSucc,Fin.append_left]⟩
    · apply Submodule.subset_span
      exact ⟨(Fin.natAdd q i).castSucc, by simp only [couplingColumns,Fin.snoc_castSucc,Fin.append_right]⟩
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    apply Submodule.subset_span
    exact ⟨Fin.last (q+q), by simp [couplingColumns]⟩

theorem coupling_output_span {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    ∀ᵐ p ∂couplingLaw μ d q,
      finishCoordinate A (by omega) (couplingState A Λ hd p).1 ∈
        orbitHull Λ.toLinearMap (q+q) (couplingColumns p) := by
  let ν := μ.prod (Measure.pi (fun _ : Fin q => roundRandomLaw d))
  let f := stateRun initialRevealState (revealStep A Λ hd) q
  have hf : Measurable f := measurable_stateRun initialRevealState measurable_initialRevealState
    (revealStep A Λ hd) (measurable_revealStep A Λ hd) q
  have hg : ∀ᵐ p ∂ν.prod (stdGaussian (Point d)),
      (prefixSpace d (2*q))ᗮ.orthogonalProjectionOnto (rotationIsometry (f p.1).2.1.2⁻¹ p.2) ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_singleton 0).compl.preimage
      ((measurable_frameProjection d (2*q)).comp
        (f := fun p => ((f p.1).2.1.2,p.2))
        ((hf.comp measurable_fst).snd.fst.snd.prodMk measurable_snd)))).mpr
    exact Filter.Eventually.of_forall (fun p => ae_frameGaussian_nonzero (by omega) (f p).2.1.2)
  have hs := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := stdGaussian (Point d))).ae
    (revealRun_spanConsistent μ A Λ hd)
  have hboth : ∀ᵐ p ∂ν.prod (stdGaussian (Point d)),
      finishCoordinate A (by omega) (f p.1,p.2) ∈
        powerHull Λ.toLinearMap q (tapeHull (fun i => ((p.1.2 i).1,(p.1.2 i).2.1))) ⊔ ℝ ∙ p.2 := by
    filter_upwards [hg,hs] with p hp hsp
    have h := finishCoordinate_mem A (by omega) (f p.1,p.2) hp
    have hh := sup_le_sup hsp (le_refl (ℝ ∙ p.2)) h
    simpa only [revealRun_tape] using hh
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := ν.prod (stdGaussian (Point d)))
    (ν := remainingHaar (prefixSpace d (2*q+1)))).ae hboth] with p hp
  have hbase := tapeHull_le_couplingColumns p
  have hpow := (powerHull_le_orbitHull Λ.toLinearMap q (couplingColumns p)
    (le_sup_left.trans hbase)).trans (orbitHull_mono Λ.toLinearMap (show q ≤ q+q by omega) _)
  have hlast : ℝ ∙ p.1.2 ≤ orbitHull Λ.toLinearMap (q+q) (couplingColumns p) :=
    (le_sup_right.trans hbase).trans (span_range_le_orbitHull _ _ _)
  exact sup_le hpow hlast hp

theorem coupling_output_correct {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d) :
    ∀ᵐ p ∂couplingLaw μ d q,
      finishCoordinate A (by omega) (couplingState A Λ hd p).1 =
      (rotationIsometry (finishComplete A (by omega) (couplingState A Λ hd p)).2).symm
        (A.output ((finishComplete A (by omega) (couplingState A Λ hd p)).1,
          linearHistory A Λ (finishComplete A (by omega) (couplingState A Λ hd p)).2
            (finishComplete A (by omega) (couplingState A Λ hd p)).1 q)) := by
  filter_upwards [(Measure.quasiMeasurePreserving_snd
    (μ := (μ.prod (Measure.pi (fun _ : Fin q => roundRandomLaw d))).prod (stdGaussian (Point d)))
    (ν := remainingHaar (prefixSpace d (2*q+1)))).ae
    (remainingHaar_fixes (prefixSpace d (2*q+1)))] with p hp
  exact finishCoordinate_correct A Λ (by omega) _ _
    (revealRun_historyConsistent A Λ hd q le_rfl p.1.1) hp

end LogConcaveSampling.LowerBound

open WithLp

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PiAppendLaw
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory
open WithLp

namespace LogConcaveSampling
lemma pi_append_law {E : Type*} [MeasurableSpace E] (γ : Measure E) [SigmaFinite γ]
    (m n : ℕ) :
    ((Measure.pi (fun _ : Fin m => γ)).prod (Measure.pi (fun _ : Fin n => γ))).map
      (fun p => Fin.append p.1 p.2) = Measure.pi (fun _ : Fin (m+n) => γ) := by
  have hsum := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n => γ)
  have he := measurePreserving_piCongrLeft (fun _ : Fin (m+n) => γ) finSumFinEquiv
  have h := (he.comp hsum).map_eq
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext p i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi]

lemma pi_transpose_law {ι κ E : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace E]
    (γ : Measure E) [IsProbabilityMeasure γ] :
    (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => γ))).map
      (fun x j i => x i j) = Measure.pi (fun _ : κ => Measure.pi (fun _ : ι => γ)) := by
  have h₁ := Measure.infinitePi_map_curry_symm (fun (_ : ι) (_ : κ) => γ)
  have h₃ := Measure.infinitePi_map_curry (fun (_ : κ) (_ : ι) => γ)
  have h₂ := (measurePreserving_piCongrLeft (fun _ : κ × ι => γ) (Equiv.prodComm ι κ)).map_eq
  simp only [Measure.infinitePi_eq_pi] at h₁ h₃
  rw [← h₂,← h₁,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h₃
  convert h₃ using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma stdGaussian_ofLp (d : ℕ) :
    (stdGaussian (Point d)).map ofLp = Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

lemma gaussianColumns_rows_law (d b : ℕ) :
    (Measure.pi (fun _ : Fin b => stdGaussian (Point d))).map
      (fun a k i => a i k) =
      Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin b => gaussianReal 0 1)) := by
  have h := (measurePreserving_pi
    (fun _ : Fin b => stdGaussian (Point d))
    (fun _ : Fin b => Measure.pi (fun _ : Fin d => gaussianReal 0 1))
    (fun _ => ⟨by fun_prop, stdGaussian_ofLp d⟩ : ∀ _ : Fin b,
      MeasurePreserving (ofLp : Point d → Fin d → ℝ) _ _)).map_eq
  have ht := pi_transpose_law (ι := Fin b) (κ := Fin d) (gaussianReal 0 1)
  rw [← h,Measure.map_map (by fun_prop) (by fun_prop)] at ht
  exact ht

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_Theta
attribute [-instance] _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory
open WithLp

namespace LogConcaveSampling.LowerBound

lemma roundGaussianPair_law (d : ℕ) :
    MeasurePreserving (fun r : RoundRandom d => (r.1,r.2.1)) (roundRandomLaw d)
      ((stdGaussian (Point d)).prod (stdGaussian (Point d))) := by
  exact (MeasurePreserving.id (stdGaussian (Point d))).prod measurePreserving_fst

lemma roundTapeColumns_law (d q : ℕ) :
    MeasurePreserving (fun r : Fin q → RoundRandom d =>
      Fin.append (fun i => (r i).1) (fun i => (r i).2.1))
      (Measure.pi (fun _ : Fin q => roundRandomLaw d))
      (Measure.pi (fun _ : Fin (q+q) => stdGaussian (Point d))) := by
  have h₁ := measurePreserving_pi (fun _ : Fin q => roundRandomLaw d)
    (fun _ : Fin q => (stdGaussian (Point d)).prod (stdGaussian (Point d)))
    (fun _ => roundGaussianPair_law d)
  have h₂ := measurePreserving_arrowProdEquivProdArrow (Point d) (Point d) (Fin q)
    (fun _ => stdGaussian (Point d)) (fun _ => stdGaussian (Point d))
  have h₃ : MeasurePreserving (fun p : (Fin q → Point d) × (Fin q → Point d) =>
      Fin.append p.1 p.2)
      ((Measure.pi (fun _ : Fin q => stdGaussian (Point d))).prod
        (Measure.pi (fun _ : Fin q => stdGaussian (Point d))))
      (Measure.pi (fun _ : Fin (q+q) => stdGaussian (Point d))) :=
    ⟨by fun_prop,pi_append_law _ q q⟩
  exact h₃.comp (h₂.comp h₁)

theorem couplingColumns_law {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (couplingColumns (Ω := Ω) (d := d) (q := q)) (couplingLaw μ d q)
      (Measure.pi (fun _ : Fin (q+q+1) => stdGaussian (Point d))) := by
  have h₀ : MeasurePreserving (fun p : CouplingNoise Ω d q => (p.1.1.2,p.1.2))
      (couplingLaw μ d q)
      ((Measure.pi (fun _ : Fin q => roundRandomLaw d)).prod (stdGaussian (Point d))) :=
    (measurePreserving_snd.prod (MeasurePreserving.id _)).comp measurePreserving_fst
  have h₁ := (roundTapeColumns_law d q).prod (MeasurePreserving.id (stdGaussian (Point d)))
  have h₂ : MeasurePreserving
      (fun p : (Fin (q+q) → Point d) × Point d =>
        Fin.snoc (α := fun _ : Fin (q+q+1) => Point d) p.1 p.2)
      ((Measure.pi (fun _ : Fin (q+q) => stdGaussian (Point d))).prod (stdGaussian (Point d)))
      (Measure.pi (fun _ : Fin (q+q+1) => stdGaussian (Point d))) :=
    ⟨measurable_fin_snoc _,pi_snoc_law _ _⟩
  exact h₂.comp (h₁.comp h₀)

end LogConcaveSampling.LowerBound

open scoped BigOperators

namespace LogConcaveSampling.LowerBound

theorem sum_half_grid_cos_eq_zero {d l : ℕ} (hl : 0 < l) (hld : l < 2 * d) :
    ∑ k ∈ Finset.range d, Real.cos ((l : ℝ) * theta d k) = 0 := by
  have hd : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hldr : (l : ℝ) < 2 * d := by exact_mod_cast hld
  let a : ℝ := l * Real.pi / d
  have ha : 0 < a / 2 := by dsimp [a]; positivity
  have hap : a / 2 < Real.pi := by
    dsimp [a]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_lt_iff₀ hdr).mpr
    nlinarith [Real.pi_pos]
  have hs : Real.sin (a / 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ha hap).ne'
  have h := Real.sin_mul_sum_cos d a (a / 2)
  have harg₁ : (d : ℝ) * a / 2 = l * Real.pi / 2 := by dsimp [a]; field_simp
  have harg₂ : ((d : ℝ) - 1) * a / 2 + a / 2 = l * Real.pi / 2 := by
    dsimp [a]; field_simp; ring
  rw [harg₁, harg₂] at h
  have hz : Real.sin (l * Real.pi / 2) * Real.cos (l * Real.pi / 2) = 0 := by
    have hh := Real.sin_two_mul (l * Real.pi / 2)
    rw [show 2 * ((l : ℝ) * Real.pi / 2) = l * Real.pi by ring,
      Real.sin_nat_mul_pi] at hh
    linarith
  rw [hz] at h
  have hsum := (mul_eq_zero.mp h).resolve_left hs
  convert! hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  dsimp [a, theta]
  ring

theorem sum_half_grid_cos_sq {d j : ℕ} (hj : 0 < j) (hjd : j < d) :
    ∑ k ∈ Finset.range d, (Real.cos ((j : ℝ) * theta d k)) ^ 2 = (d : ℝ) / 2 := by
  have hz := sum_half_grid_cos_eq_zero (l := 2 * j) (by omega) (by omega : 2 * j < 2 * d)
  simp_rw [Real.cos_sq]
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  have harg : ∀ k, 2 * ((j : ℝ) * theta d k) = ((2 * j : ℕ) : ℝ) * theta d k := by
    intro k
    push_cast
    ring
  simp_rw [harg]
  rw [← Finset.sum_div, hz]
  simp

theorem sum_half_grid_cos_mul_of_lt {d j k : ℕ} (hkj : k < j) (hjd : j + k < 2 * d) :
    ∑ a ∈ Finset.range d,
      Real.cos ((j : ℝ) * theta d a) * Real.cos ((k : ℝ) * theta d a) = 0 := by
  have hs := sum_half_grid_cos_eq_zero (l := j + k) (by omega) hjd
  have hd := sum_half_grid_cos_eq_zero (l := j - k) (by omega) (by omega : j - k < 2 * d)
  have hpoint : ∀ a : ℕ,
      2 * (Real.cos ((j : ℝ) * theta d a) * Real.cos ((k : ℝ) * theta d a)) =
        Real.cos (((j - k : ℕ) : ℝ) * theta d a) +
        Real.cos (((j + k : ℕ) : ℝ) * theta d a) := by
    intro a
    rw [← mul_assoc, Real.two_mul_cos_mul_cos, Nat.cast_sub hkj.le, Nat.cast_add]
    congr 2 <;> ring
  have hh : 2 * (∑ a ∈ Finset.range d,
      Real.cos ((j : ℝ) * theta d a) * Real.cos ((k : ℝ) * theta d a)) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, hd, hs, add_zero]
  linarith

theorem sum_half_grid_cos_mul {d j k : ℕ} (hne : j ≠ k) (hjd : j + k < 2 * d) :
    ∑ a ∈ Finset.range d,
      Real.cos ((j : ℝ) * theta d a) * Real.cos ((k : ℝ) * theta d a) = 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · simpa only [mul_comm] using sum_half_grid_cos_mul_of_lt h (by omega : k + j < 2 * d)
  · exact sum_half_grid_cos_mul_of_lt h hjd

theorem sum_half_grid_cos_triple_of_le {d n j k : ℕ}
    (hkj : k ≤ j) (hn : j + k < n) (hnd : n + j + k < 2 * d) :
    ∑ a ∈ Finset.range d,
      Real.cos ((n : ℝ) * theta d a) * Real.cos ((j : ℝ) * theta d a) *
        Real.cos ((k : ℝ) * theta d a) = 0 := by
  have hs := sum_half_grid_cos_mul (d := d) (j := n) (k := j + k) (by omega) (by omega)
  have hd := sum_half_grid_cos_mul (d := d) (j := n) (k := j - k) (by omega) (by omega)
  have hpoint : ∀ a : ℕ,
      2 * (Real.cos ((n : ℝ) * theta d a) * Real.cos ((j : ℝ) * theta d a) *
        Real.cos ((k : ℝ) * theta d a)) =
      Real.cos ((n : ℝ) * theta d a) * Real.cos (((j - k : ℕ) : ℝ) * theta d a) +
      Real.cos ((n : ℝ) * theta d a) * Real.cos (((j + k : ℕ) : ℝ) * theta d a) := by
    intro a
    have h := Real.two_mul_cos_mul_cos ((j : ℝ) * theta d a) ((k : ℝ) * theta d a)
    rw [Nat.cast_sub hkj, Nat.cast_add, sub_mul, add_mul, ← mul_add, ← h]
    ring
  have hh : 2 * (∑ a ∈ Finset.range d,
      Real.cos ((n : ℝ) * theta d a) * Real.cos ((j : ℝ) * theta d a) *
        Real.cos ((k : ℝ) * theta d a)) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, hd, hs, add_zero]
  linarith

theorem sum_half_grid_cos_triple {d q j k : ℕ}
    (hj : j ≤ q) (hk : k ≤ q) (hqd : 4 * q + 1 < 2 * d) :
    ∑ a ∈ Finset.range d,
      Real.cos (((2 * q + 1 : ℕ) : ℝ) * theta d a) * Real.cos ((j : ℝ) * theta d a) *
        Real.cos ((k : ℝ) * theta d a) = 0 := by
  rcases le_total k j with h | h
  · exact sum_half_grid_cos_triple_of_le h (by omega) (by omega)
  · convert! sum_half_grid_cos_triple_of_le (d := d) (n := 2 * q + 1) h
      (by omega : k + j < 2 * q + 1) (by omega : 2 * q + 1 + k + j < 2 * d) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro a _
    ring

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

theorem sum_half_grid_cos_sq_ite {d j : ℕ} (hj : j < d) :
    ∑ k ∈ Finset.range d, Real.cos ((j : ℝ) * theta d k) ^ 2 =
      if j = 0 then (d : ℝ) else (d : ℝ) / 2 := by
  by_cases h : j = 0
  · subst j
    simp
  · rw [ite_eq_right h]
    have hd := sum_half_grid_cos_eq_zero (d := d) (l := 2 * j) (by omega) (by omega)
    have hpoint : ∀ k : ℕ, 2 * Real.cos ((j : ℝ) * theta d k) ^ 2 =
        1 + Real.cos (((2 * j : ℕ) : ℝ) * theta d k) := by
      intro k
      rw [Nat.cast_mul, Nat.cast_ofNat]
      have hc := Real.cos_two_mul ((j : ℝ) * theta d k)
      rw [← mul_assoc] at hc
      linarith
    have hh : 2 * (∑ k ∈ Finset.range d, Real.cos ((j : ℝ) * theta d k) ^ 2) = d := by
      rw [Finset.mul_sum]
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib, hd]
      simp
    linarith

theorem cosineAmplitude_pos (j : ℕ) : 0 < cosineAmplitude j := by
  unfold cosineAmplitude
  split_ifs <;> positivity

theorem cosineAmplitude_sq_le_two (j : ℕ) : cosineAmplitude j ^ 2 ≤ 2 := by
  unfold cosineAmplitude
  split_ifs <;> norm_num

theorem cosineColumn_orthonormal {d j l : ℕ} (hd : 0 < d) (hj : j < d) (hl : l < d) :
    ∑ k ∈ Finset.range d, cosineColumn d j k * cosineColumn d l k =
      if j = l then (1 : ℝ) else 0 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdr.le
  have hp : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hdr).ne'
  have hcoeff : ∀ k : ℕ, cosineColumn d j k * cosineColumn d l k =
      (cosineAmplitude j * cosineAmplitude l / d) *
        (Real.cos ((j : ℝ) * theta d k) * Real.cos ((l : ℝ) * theta d k)) := by
    intro k
    simp only [cosineColumn]
    field_simp [hp, hdr.ne']
    rw [hs]
    ring
  simp_rw [hcoeff]
  rw [← Finset.mul_sum]
  by_cases h : j = l
  · subst l
    rw [ite_eq_left rfl]
    simp_rw [← pow_two]
    rw [sum_half_grid_cos_sq_ite hj]
    unfold cosineAmplitude
    split_ifs
    all_goals field_simp
    all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · rw [ite_eq_right h, sum_half_grid_cos_mul h (by omega), mul_zero]

theorem cosineColumn_sq_le {d j k : ℕ} (hd : 0 < d) :
    cosineColumn d j k ^ 2 ≤ 2 / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdr.le
  unfold cosineColumn
  rw [div_pow, mul_pow, hs]
  apply div_le_div_of_nonneg_right _ hdr.le
  have hc : Real.cos ((j : ℝ) * theta d k) ^ 2 ≤ 1 := by
    nlinarith [Real.cos_le_one ((j : ℝ) * theta d k),
      Real.neg_one_le_cos ((j : ℝ) * theta d k)]
  calc
    _ ≤ cosineAmplitude j ^ 2 * 1 := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ ≤ 2 := by simpa using cosineAmplitude_sq_le_two j

theorem cosineColumn_product_le {d j l k : ℕ} (hd : 0 < d) :
    |cosineColumn d j k * cosineColumn d l k| ≤ 2 / d := by
  have hj := cosineColumn_sq_le (j := j) (k := k) hd
  have hl := cosineColumn_sq_le (j := l) (k := k) hd
  have h := mul_self_nonneg (|cosineColumn d j k| - |cosineColumn d l k|)
  rw [abs_mul]
  nlinarith [sq_abs (cosineColumn d j k), sq_abs (cosineColumn d l k)]

theorem cosineColumn_weighted_orthogonal {d q j l : ℕ}
    (hj : j ≤ q) (hl : l ≤ q) (hqd : 4 * q + 1 < 2 * d) :
    ∑ k ∈ Finset.range d, weight d (2*q+1) k * cosineColumn d j k * cosineColumn d l k = 0 := by
  have hpoint : ∀ k : ℕ,
      weight d (2*q+1) k * cosineColumn d j k * cosineColumn d l k =
      (cosineAmplitude j * cosineAmplitude l / (Real.sqrt d) ^ 2) *
      (Real.cos (((2*q+1 : ℕ) : ℝ) * theta d k) *
        Real.cos ((j : ℝ) * theta d k) * Real.cos ((l : ℝ) * theta d k)) := by
    intro k
    simp only [cosineColumn, weight]
    ring
  simp_rw [hpoint]
  rw [← Finset.mul_sum, sum_half_grid_cos_triple hj hl hqd, mul_zero]

end LogConcaveSampling.LowerBound

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LogConcaveSampling.LowerBound

theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  change (∫ x : ℝ, ((fun y : ℝ => y) ^ 4) x ∂gaussianReal 0 v) = _
  rw [← iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v)
    (by simp) 4, mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  let f : ℝ → ℝ := fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)
  have hf : ∀ t, HasDerivAt f ((v : ℝ) * t * f t) t := by
    intro t
    convert! ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2).exp using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [f]
    ring
  have h1 : deriv f = fun t => v * t * f t := funext fun t => (hf t).deriv
  have h2 : deriv (fun t => (v : ℝ) * t * f t) =
      fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t := by
    funext t
    convert! (((hasDerivAt_id t).const_mul (v : ℝ)).mul (hf t)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    ring
  have h3 : deriv (fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t) =
      fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t := by
    funext t
    convert! ((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ) ^ 2)).const_add
      (v : ℝ) |>.mul (hf t)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq, Pi.pow_apply]
    ring
  have h4 : deriv (fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t) 0 =
      3 * (v : ℝ) ^ 2 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).const_mul (3 * (v : ℝ) ^ 2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul ((v : ℝ) ^ 3))).mul (hf 0)).deriv
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp [f]
  change iteratedDeriv 4 f 0 = _
  rw [iteratedDeriv_succ', h1, iteratedDeriv_succ', h2,
    iteratedDeriv_succ', h3, iteratedDeriv_one, h4]

theorem integral_pow_two_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
  simpa using h

private theorem holder_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  constructor
  change (↑(4 : ℝ≥0) : ℝ≥0∞)⁻¹ + (↑(4 : ℝ≥0) : ℝ≥0∞)⁻¹ = (↑(2 : ℝ≥0) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
  norm_num

section RandomVariables
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {X Y : Ω → ℝ} {v w : ℝ≥0}

theorem gaussian_memLp (hX : HasLaw X (gaussianReal 0 v) P) (p : ℝ≥0) :
    MemLp X p P := by
  have h := memLp_id_gaussianReal (μ := 0) (v := v) p
  rw [← hX.map_eq] at h
  exact h.comp_of_map hX.aemeasurable

theorem gaussian_integral_sq (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 2 ∂P = (v : ℝ) := by
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v := hX.integral_comp (by fun_prop)
    _ = _ := integral_pow_two_gaussianReal v

theorem gaussian_integral_fourth (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 4 ∂P = 3 * (v : ℝ) ^ 2 := by
  calc
    _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v := hX.integral_comp (by fun_prop)
    _ = _ := integral_pow_four_gaussianReal v

theorem gaussian_sq_memLp (hX : HasLaw X (gaussianReal 0 v) P) :
    MemLp (fun ω => X ω ^ 2) 2 P := by
  let : ENNReal.HolderTriple 4 4 2 := holder_four_four_two
  have h4 : MemLp X (4 : ℝ≥0∞) P := by simpa using gaussian_memLp hX 4
  simp only [pow_two]
  exact h4.mul h4

theorem gaussian_sq_variance [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) :
    Var[fun ω => X ω ^ 2; P] = 2 * (v : ℝ) ^ 2 := by
  rw [variance_eq_sub (gaussian_sq_memLp hX), gaussian_integral_sq hX]
  simp only [Pi.pow_apply, ← pow_mul]
  rw [show 2 * 2 = 4 from rfl, gaussian_integral_fourth hX]
  ring

theorem independent_gaussian_product_variance [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) (hY : HasLaw Y (gaussianReal 0 w) P)
    (hXY : IndepFun X Y P) :
    Var[fun ω => X ω * Y ω; P] = (v : ℝ) * w := by
  let : ENNReal.HolderTriple 4 4 2 := holder_four_four_two
  have h4X : MemLp X (4 : ℝ≥0∞) P := by simpa using gaussian_memLp hX 4
  have h4Y : MemLp Y (4 : ℝ≥0∞) P := by simpa using gaussian_memLp hY 4
  have hmem : MemLp (fun ω => X ω * Y ω) 2 P := by
    have h := h4Y.mul (r := 2) h4X
    have e : (fun ω => X ω * Y ω) = X * Y := by funext ω; simp [mul_comm]
    rw [e]; exact h
  rw [variance_eq_sub hmem]
  have hmean : ∫ ω, X ω * Y ω ∂P = 0 := by
    rw [hXY.integral_fun_mul_eq_mul_integral hX.aemeasurable.aestronglyMeasurable
      hY.aemeasurable.aestronglyMeasurable, hX.integral_eq, integral_id_gaussianReal]
    simp
  have hsq := (hXY.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
    (hX.aemeasurable.pow_const 2).aestronglyMeasurable
    (hY.aemeasurable.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def, id_eq] at hsq
  rw [gaussian_integral_sq hX, gaussian_integral_sq hY] at hsq
  simpa only [Pi.pow_apply, mul_pow, hmean, zero_pow (by decide : 2 ≠ 0), sub_zero] using hsq

end RandomVariables
end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped BigOperators

theorem gaussianRow_coordinate_law {b : ℕ} (i : Fin b) :
    HasLaw (fun x : Fin b → ℝ => x i) (gaussianReal 0 1) (gaussianRow b) :=
  (measurePreserving_eval (fun _ : Fin b => gaussianReal 0 1) i).hasLaw

theorem gaussianRow_coordinates_independent {b : ℕ} :
    iIndepFun (fun i (x : Fin b → ℝ) => x i) (gaussianRow b) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem gaussianRow_product_memLp {b : ℕ} (i j : Fin b) :
    MemLp (fun x : Fin b → ℝ => x i * x j) 2 (gaussianRow b) := by
  let : ENNReal.HolderTriple 4 4 2 := holder_four_four_two
  have hi : MemLp (fun x : Fin b → ℝ => x i) (4 : ℝ≥0∞) (gaussianRow b) := by
    simpa using gaussian_memLp (gaussianRow_coordinate_law i) 4
  have hj : MemLp (fun x : Fin b → ℝ => x j) (4 : ℝ≥0∞) (gaussianRow b) := by
    simpa using gaussian_memLp (gaussianRow_coordinate_law j) 4
  have h := hj.mul (r := 2) hi
  have e : (fun x : Fin b → ℝ => x i * x j) = (fun x : Fin b → ℝ => x i) * (fun x : Fin b → ℝ => x j) := by funext x; simp [mul_comm]
  rw [e]; exact h

theorem gaussianRow_product_mean {b : ℕ} (i j : Fin b) :
    ∫ x : Fin b → ℝ, x i * x j ∂gaussianRow b = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simpa [← pow_two] using
      gaussian_integral_sq (gaussianRow_coordinate_law i)
  · rw [ite_eq_right h, (gaussianRow_coordinates_independent.indepFun h).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable, (gaussianRow_coordinate_law i).integral_eq,
      integral_id_gaussianReal, zero_mul]

theorem gaussianRow_product_variance {b : ℕ} (i j : Fin b) :
    Var[fun x : Fin b → ℝ => x i * x j; gaussianRow b] = if i = j then 2 else 1 := by
  by_cases h : i = j
  · subst j
    simpa [← pow_two] using
      gaussian_sq_variance (gaussianRow_coordinate_law i)
  · rw [ite_eq_right h]
    simpa using independent_gaussian_product_variance (gaussianRow_coordinate_law i)
      (gaussianRow_coordinate_law j) (gaussianRow_coordinates_independent.indepFun h)

theorem gaussianRowSum_memLp {d b : ℕ} (c : Fin d → ℝ) (i j : Fin b) :
    MemLp (gaussianRowSum c i j) 2 (gaussianRows d b) := by
  apply memLp_finsetSum
  intro k _
  exact ((gaussianRow_product_memLp i j).const_mul (c k)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianRow b) k)

theorem gaussianRowSum_mean {d b : ℕ} (c : Fin d → ℝ) (i j : Fin b) :
    ∫ x, gaussianRowSum c i j x ∂gaussianRows d b =
      (if i = j then 1 else 0) * ∑ k, c k := by
  unfold gaussianRowSum
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    have hrow : ∀ k : Fin d,
        ∫ x : Fin d → Fin b → ℝ, x k i * x k j ∂gaussianRows d b =
          if i = j then 1 else 0 := by
      intro k
      calc
        _ = ∫ y : Fin b → ℝ, y i * y j ∂gaussianRow b :=
          (measurePreserving_eval (fun _ : Fin d => gaussianRow b) k).hasLaw.integral_comp
            (by fun_prop)
        _ = _ := gaussianRow_product_mean i j
    simp_rw [hrow]
    rw [← Finset.sum_mul, mul_comm]
  · intro k _
    exact (((gaussianRow_product_memLp i j).const_mul (c k)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => gaussianRow b) k)).integrable (by norm_num)

theorem gaussianRowSum_variance {d b : ℕ} (c : Fin d → ℝ) (i j : Fin b) :
    Var[gaussianRowSum c i j; gaussianRows d b] =
      (if i = j then 2 else 1) * ∑ k, (c k) ^ 2 := by
  have h := variance_sum_pi (μ := fun _ : Fin d => gaussianRow b)
    (X := fun k (y : Fin b → ℝ) => c k * (y i * y j))
    (fun k => (gaussianRow_product_memLp i j).const_mul (c k))
  simp only [variance_const_mul, gaussianRow_product_variance] at h
  convert! h using 1
  · congr 1
    ext x
    simp [gaussianRowSum]
  · rw [← Finset.sum_mul, mul_comm]

theorem gaussianRowSum_variance_le {d b : ℕ} (hd : 0 < d) (c : Fin d → ℝ)
    (hc : ∀ k, |c k| ≤ 2 / d) (i j : Fin b) :
    Var[gaussianRowSum c i j; gaussianRows d b] ≤ 8 / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [gaussianRowSum_variance]
  have hfactor : (if i = j then (2 : ℝ) else 1) ≤ 2 := by split_ifs <;> norm_num
  have hsum : (∑ k, (c k) ^ 2) ≤ d * (2 / d : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin d, (2 / d : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hc k)
      _ = _ := by simp
  have hn : 0 ≤ ∑ k, (c k) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ 2 * ∑ k, (c k) ^ 2 := mul_le_mul_of_nonneg_right hfactor hn
    _ ≤ 2 * (d * (2 / d : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 8 / d := by field_simp; ring

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped BigOperators

theorem rowDeviationEnergy_nonneg {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) (x : Fin d → Fin b → ℝ) :
    0 ≤ rowDeviationEnergy c a z x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rowDeviationEnergy_measurable {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) : Measurable (rowDeviationEnergy c a z) := by
  unfold rowDeviationEnergy gaussianRowSum
  fun_prop

theorem rowDeviationEnergy_integrable {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) :
    Integrable (rowDeviationEnergy c a z) (gaussianRows d b) := by
  apply integrable_finsetSum
  intro i _
  exact ((gaussianRowSum_memLp (c i) (a i) (z i)).sub (memLp_const _)).integrable_sq

theorem rowDeviationEnergy_mean {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) :
    ∫ x, rowDeviationEnergy c a z x ∂gaussianRows d b =
      ∑ i, Var[gaussianRowSum (c i) (a i) (z i); gaussianRows d b] := by
  unfold rowDeviationEnergy
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [variance_eq_integral (gaussianRowSum_memLp (c i) (a i) (z i)).aestronglyMeasurable.aemeasurable,
      gaussianRowSum_mean]
  · intro i _
    exact ((gaussianRowSum_memLp (c i) (a i) (z i)).sub (memLp_const _)).integrable_sq

theorem rowDeviationEnergy_mean_le {ι : Type*} [Fintype ι] {d b : ℕ}
    (hd : 0 < d) (c : ι → Fin d → ℝ) (a z : ι → Fin b)
    (hc : ∀ i k, |c i k| ≤ 2 / d) :
    ∫ x, rowDeviationEnergy c a z x ∂gaussianRows d b ≤
      8 * Fintype.card ι / d := by
  rw [rowDeviationEnergy_mean]
  calc
    _ ≤ ∑ _ : ι, (8 : ℝ) / d :=
      Finset.sum_le_sum fun i _ => gaussianRowSum_variance_le hd (c i) (hc i) (a i) (z i)
    _ = _ := by simp; ring

theorem rowDeviationEnergy_tail {ι : Type*} [Fintype ι] {d b : ℕ}
    (hd : 0 < d) (c : ι → Fin d → ℝ) (a z : ι → Fin b)
    (hc : ∀ i k, |c i k| ≤ 2 / d) {T : ℝ} (hT : 0 < T) :
    (gaussianRows d b).real {x | T ≤ rowDeviationEnergy c a z x} ≤
      (8 * Fintype.card ι / d) / T := by
  apply (le_div_iff₀ hT).mpr
  rw [mul_comm]
  exact (mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (rowDeviationEnergy_nonneg c a z))
    (rowDeviationEnergy_integrable c a z) T).trans
    (rowDeviationEnergy_mean_le hd c a z hc)

end LogConcaveSampling.LowerBound

open scoped BigOperators
open Matrix

namespace LogConcaveSampling.LowerBound

theorem matrixEnergy_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) : 0 ≤ matrixEnergy M := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem quadratic_form_bound_of_energy {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (hM : matrixEnergy M ≤ τ ^ 2)
    (x : ι → ℝ) : |dotProduct x (M *ᵥ x)| ≤ τ * dotProduct x x := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => M p.1 p.2) (fun p => x p.1 * x p.2)
  have ht : (∑ p : ι × ι, M p.1 p.2 * (x p.1 * x p.2)) =
      dotProduct x (M *ᵥ x) := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : (∑ p : ι × ι, (x p.1 * x p.2) ^ 2) = (dotProduct x x) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [mul_pow]
    rw [← Finset.sum_mul_sum]
    simp only [dotProduct, pow_two]
  rw [ht, hs, Fintype.sum_prod_type] at hcs
  have hnon : 0 ≤ dotProduct x x := by
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hle : (dotProduct x (M *ᵥ x)) ^ 2 ≤ (τ * dotProduct x x) ^ 2 := by
    calc
      _ ≤ matrixEnergy M * (dotProduct x x) ^ 2 := hcs
      _ ≤ τ ^ 2 * (dotProduct x x) ^ 2 := mul_le_mul_of_nonneg_right hM (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hτ hnon)).mp (by simpa using hle)

theorem gram_control_on_column_span {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] [DecidableEq κ] (B : Matrix κ ι ℝ) (p : κ → ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 2)
    (hG : matrixEnergy (B.transpose * B - 1) ≤ τ ^ 2)
    (hT : matrixEnergy (B.transpose * diagonal p * B) ≤ τ ^ 2) :
    ∀ u ∈ Submodule.span ℝ (Set.range B.col),
      |dotProduct u (diagonal p *ᵥ u)| ≤ 2 * τ * dotProduct u u := by
  intro u hu
  rw [← Matrix.range_mulVecLin] at hu
  obtain ⟨x, rfl⟩ := hu
  change |dotProduct (B *ᵥ x) (diagonal p *ᵥ (B *ᵥ x))| ≤
    2 * τ * dotProduct (B *ᵥ x) (B *ᵥ x)
  have hg := quadratic_form_bound_of_energy (B.transpose * B - 1) hτ hG x
  have ht := quadratic_form_bound_of_energy (B.transpose * diagonal p * B) hτ hT x
  have hgram : dotProduct x ((B.transpose * B - 1) *ᵥ x) =
      dotProduct (B *ᵥ x) (B *ᵥ x) - dotProduct x x := by
    rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec,
      dotProduct_transpose_mulVec]
  have hstat : dotProduct x ((B.transpose * diagonal p * B) *ᵥ x) =
      dotProduct (B *ᵥ x) (diagonal p *ᵥ (B *ᵥ x)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hgram] at hg
  rw [hstat] at ht
  have hnorm : dotProduct x x ≤ 2 * dotProduct (B *ᵥ x) (B *ᵥ x) := by
    have hx : 0 ≤ dotProduct x x := by
      exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have hlow := (abs_le.mp hg).1
    nlinarith
  calc
    _ ≤ τ * dotProduct x x := ht
    _ ≤ _ := by nlinarith

end LogConcaveSampling.LowerBound

open scoped BigOperators
open Polynomial

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_WeightedEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open scoped BigOperators
open Polynomial

namespace LogConcaveSampling.LowerBound

theorem spectral_power_span_eq_cosine_span {κ : Type*} (angles g : κ → ℝ) (q : ℕ) :
    Submodule.span ℝ {v : κ → ℝ | ∃ j ≤ q,
      v = fun k => g k * ((3 + Real.cos (angles k)) / 2) ^ j} =
    Submodule.span ℝ {v : κ → ℝ | ∃ j ≤ q,
      v = fun k => g k * Real.cos ((j : ℝ) * angles k)} := by
  let ev := weightedEvaluation (fun k => Real.cos (angles k)) g
  let T := Polynomial.Chebyshev.chebyshevTsequence ℝ
  have hp := spectralPowers.span_degreeLE (m := q) (fun i _ =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (spectralPowers.ne_zero i)))
  have ht := T.span_degreeLE (m := q) (fun i _ =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (T.ne_zero i)))
  have heq := congrArg (Submodule.map ev) (hp.trans ht.symm)
  rw [Submodule.map_span, Submodule.map_span] at heq
  convert! heq using 1
  · congr 1
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨spectralPowers j, ⟨j, hj, rfl⟩, ?_⟩
      ext k
      simp only [ev, weightedEvaluation, spectralPowers,
        LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      congr 2
      ring
    · rintro ⟨p, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨j, hj, ?_⟩
      ext k
      simp only [ev, weightedEvaluation, spectralPowers,
        LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      congr 2
      ring
  · congr 1
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨T j, ⟨j, hj, rfl⟩, ?_⟩
      ext k
      simp [ev, weightedEvaluation, T, Polynomial.Chebyshev.chebyshevTsequence,
        Polynomial.Chebyshev.T_real_cos]
    · rintro ⟨p, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨j, hj, ?_⟩
      ext k
      simp [ev, weightedEvaluation, T, Polynomial.Chebyshev.chebyshevTsequence,
        Polynomial.Chebyshev.T_real_cos]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem blockCoefficient_bound {d q : ℕ} (hd : 0 < d)
    (v : Bool × BlockIndex q × BlockIndex q) (k : Fin d) : |blockCoefficient d q v k| ≤ 2 / d := by
  obtain ⟨t, i, j⟩ := v
  cases t
  · simpa [blockCoefficient] using cosineColumn_product_le (j := i.2) (l := j.2) (k := k) hd
  · simp only [blockCoefficient, ↓reduceIte]
    rw [mul_assoc, abs_mul]
    calc
      _ ≤ 1 * |cosineColumn d i.2 k * cosineColumn d j.2 k| :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
      _ ≤ _ := by simpa using cosineColumn_product_le (j := i.2) (l := j.2) (k := k) hd

theorem blockCoefficient_sum {d q : ℕ} (hqd : 4*q+1 < 2*d)
    (v : Bool × BlockIndex q × BlockIndex q) :
    ∑ k, blockCoefficient d q v k =
      if v.1 then 0 else if v.2.1.2 = v.2.2.2 then 1 else 0 := by
  have hd : 0 < d := by omega
  have hj : (v.2.1.2 : ℕ) ≤ q := by omega
  have hl : (v.2.2.2 : ℕ) ≤ q := by omega
  obtain ⟨t, i, j⟩ := v
  cases t
  · simp only [blockCoefficient, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [Fin.sum_univ_eq_sum_range (fun k => cosineColumn d i.2 k * cosineColumn d j.2 k) d]
    have h := cosineColumn_orthonormal hd
      (by have := i.2.isLt; omega : (i.2 : ℕ) < d)
      (by have := j.2.isLt; omega : (j.2 : ℕ) < d)
    simpa only [Fin.ext_iff] using h
  · simp only [blockCoefficient, ↓reduceIte]
    rw [Fin.sum_univ_eq_sum_range (fun k => weight d (2*q+1) k * cosineColumn d i.2 k * cosineColumn d j.2 k) d]
    exact cosineColumn_weighted_orthogonal hj hl hqd

theorem blockGram_entry {d q : ℕ} (x : Fin d → Fin (q+1) → ℝ) (i j : BlockIndex q) :
    ((blockMatrix x).transpose * blockMatrix x) i j =
      gaussianRowSum (blockCoefficient d q (false,i,j)) i.1 j.1 x := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, blockMatrix, blockCoefficient,
    Bool.false_eq_true, ↓reduceIte, one_mul, gaussianRowSum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem blockWeightedGram_entry {d q : ℕ} (x : Fin d → Fin (q+1) → ℝ) (i j : BlockIndex q) :
    ((blockMatrix x).transpose * Matrix.diagonal (fun k : Fin d => weight d (2*q+1) k) * blockMatrix x) i j =
      gaussianRowSum (blockCoefficient d q (true,i,j)) i.1 j.1 x := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, blockMatrix,
    blockCoefficient, ↓reduceIte, gaussianRowSum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem block_total_energy_eq {d q : ℕ} (hqd : 4*q+1 < 2*d)
    (x : Fin d → Fin (q+1) → ℝ) :
    matrixEnergy ((blockMatrix x).transpose * blockMatrix x - 1) +
      matrixEnergy ((blockMatrix x).transpose * Matrix.diagonal
        (fun k : Fin d => weight d (2*q+1) k) * blockMatrix x) =
      rowDeviationEnergy (blockCoefficient d q) (blockLeft q) (blockRight q) x := by
  have heq (i j : BlockIndex q) : (if i = j then (1 : ℝ) else 0) =
      (if i.1 = j.1 then 1 else 0) * (if i.2 = j.2 then 1 else 0) := by
    obtain ⟨i,a⟩ := i
    obtain ⟨j,b⟩ := j
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [matrixEnergy, rowDeviationEnergy, Matrix.sub_apply, Matrix.one_apply,
    blockGram_entry, blockWeightedGram_entry, heq,
    Fintype.sum_prod_type, Fintype.sum_bool, blockLeft, blockRight,
    blockCoefficient_sum hqd, Bool.false_eq_true, ↓reduceIte, mul_zero, sub_zero]
  rw [add_comm]
  rfl

theorem blockTolerance_pos {d q : ℕ} (hd : 0 < d) : 0 < blockTolerance d q := by
  unfold blockTolerance
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem block_good_event {d q : ℕ} (hqd : 4*q+1 < 2*d)
    (hτ : blockTolerance d q ≤ 1/2) :
    ∃ G : Set (Fin d → Fin (q+1) → ℝ), MeasurableSet G ∧
      (99 : ℝ)/100 ≤ (gaussianRows d (q+1)).real G ∧
      ∀ x ∈ G, ∀ u ∈ Submodule.span ℝ (Set.range (blockMatrix x).col),
        |dotProduct u (Matrix.diagonal (fun k : Fin d => weight d (2*q+1) k) *ᵥ u)| ≤
          2 * blockTolerance d q * dotProduct u u := by
  have hd : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have htpos := blockTolerance_pos (q := q) hd
  let E := rowDeviationEnergy (blockCoefficient d q) (blockLeft q) (blockRight q)
  have hE := rowDeviationEnergy_measurable (blockCoefficient d q) (blockLeft q) (blockRight q)
  let G : Set (Fin d → Fin (q+1) → ℝ) := {x | E x < (blockTolerance d q)^2}
  have hG : MeasurableSet G := hE measurableSet_Iio
  refine ⟨G,hG,?_,?_⟩
  · have hbad := rowDeviationEnergy_tail hd (blockCoefficient d q) (blockLeft q)
      (blockRight q) (blockCoefficient_bound hd) (sq_pos_of_pos htpos)
    have hconst : (8 * (Fintype.card (Bool × BlockIndex q × BlockIndex q) : ℝ) / d) /
        (blockTolerance d q)^2 = 1/100 := by
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, BlockIndex,
        blockTolerance, div_pow, Real.sq_sqrt hdr.le]
      have hq : (q : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hconst] at hbad
    have hcompl : Gᶜ = {x | (blockTolerance d q)^2 ≤ E x} := by ext x; simp [G]
    have hm := measureReal_compl hG (μ := gaussianRows d (q+1))
    rw [probReal_univ, hcompl] at hm
    change (gaussianRows d (q+1)).real {x | (blockTolerance d q)^2 ≤ E x} ≤ 1/100 at hbad
    linarith
  · intro x hx
    have hx' : E x < (blockTolerance d q)^2 := hx
    have he := block_total_energy_eq hqd x
    have h₁ := matrixEnergy_nonneg ((blockMatrix x).transpose * blockMatrix x - 1)
    have h₂ := matrixEnergy_nonneg ((blockMatrix x).transpose * Matrix.diagonal
      (fun k : Fin d => weight d (2*q+1) k) * blockMatrix x)
    apply gram_control_on_column_span (blockMatrix x) _ htpos.le hτ
    · change _ = E x at he
      linarith
    · change _ = E x at he
      linarith

theorem block_span_eq_krylov {d q : ℕ} (hd : 0 < d) (x : Fin d → Fin (q+1) → ℝ) :
    Submodule.span ℝ (Set.range (blockMatrix x).col) = krylovSpace x := by
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  have heq (i : Fin (q+1)) := spectral_power_span_eq_cosine_span
    (fun k : Fin d => theta d k) (fun k => x k i) q
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨⟨i,j⟩,rfl⟩
    have hcos : (fun k : Fin d => x k i * Real.cos ((j : ℝ) * theta d k)) ∈
        Submodule.span ℝ {v : Fin d → ℝ | ∃ l ≤ q,
          v = fun k => x k i * Real.cos ((l : ℝ) * theta d k)} :=
      Submodule.subset_span ⟨j,by omega,rfl⟩
    rw [← heq i] at hcos
    have hle : Submodule.span ℝ {v : Fin d → ℝ | ∃ l ≤ q,
        v = fun k => x k i * ((3 + Real.cos (theta d k))/2)^l} ≤ krylovSpace x := by
      apply Submodule.span_le.mpr
      rintro v ⟨l,hl,rfl⟩
      exact Submodule.subset_span ⟨i,l,hl,rfl⟩
    have h := (krylovSpace x).smul_mem (cosineAmplitude j / Real.sqrt d) (hle hcos)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ext k
    simp only [Matrix.col, Matrix.transpose_apply, blockMatrix, cosineColumn, Pi.smul_apply, smul_eq_mul]
    ring
  · apply Submodule.span_le.mpr
    rintro v ⟨i,j,hj,rfl⟩
    have hpow : (fun k : Fin d => x k i * eigenvalue d k ^ j) ∈
        Submodule.span ℝ {v : Fin d → ℝ | ∃ l ≤ q,
          v = fun k => x k i * ((3 + Real.cos (theta d k))/2)^l} :=
      Submodule.subset_span ⟨j,hj,rfl⟩
    rw [heq i] at hpow
    have hle : Submodule.span ℝ {v : Fin d → ℝ | ∃ l ≤ q,
        v = fun k => x k i * Real.cos ((l : ℝ) * theta d k)} ≤
        Submodule.span ℝ (Set.range (blockMatrix x).col) := by
      apply Submodule.span_le.mpr
      rintro v ⟨l,hl,rfl⟩
      have ha : cosineAmplitude l ≠ 0 := (cosineAmplitude_pos l).ne'
      have h := (Submodule.span ℝ (Set.range (blockMatrix x).col)).smul_mem
        (Real.sqrt d / cosineAmplitude l)
        (Submodule.subset_span (Set.mem_range_self (i, (⟨l,by omega⟩ : Fin (q+1)))))
      convert! h using 1
      all_goals try with_reducible_and_instances rfl
      ext k
      simp only [Matrix.col, Matrix.transpose_apply, blockMatrix, cosineColumn, Pi.smul_apply, smul_eq_mul]
      field_simp
    exact hle hpow

theorem lower_span_statistic {d q : ℕ} (hqd : 4*q+1 < 2*d)
    (hτ : blockTolerance d q ≤ 1/2) :
    ∃ G : Set (Fin d → Fin (q+1) → ℝ), MeasurableSet G ∧
      (99 : ℝ)/100 ≤ (gaussianRows d (q+1)).real G ∧
      ∀ x ∈ G, ∀ u ∈ krylovSpace x,
        |dotProduct u (Matrix.diagonal (fun k : Fin d => weight d (2*q+1) k) *ᵥ u)| ≤
          2 * blockTolerance d q * dotProduct u u := by
  obtain ⟨G,hG,hm,hu⟩ := block_good_event hqd hτ
  refine ⟨G,hG,hm,?_⟩
  intro x hx u hu'
  apply hu x hx u
  rw [block_span_eq_krylov (by omega)]
  exact hu'

end LogConcaveSampling.LowerBound

open scoped BigOperators

namespace LogConcaveSampling.LowerBound

theorem spectralDecay_pos : 0 < spectralDecay := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [spectralDecay]
  nlinarith [Real.sqrt_nonneg 2]

theorem spectralDecay_lt_one : spectralDecay < 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [spectralDecay]
  nlinarith [Real.sqrt_nonneg 2]

theorem hasSum_geometric_cos {t : ℝ} (ht : |t| < 1) (θ : ℝ) :
    HasSum (fun j : ℕ => t ^ j * Real.cos ((j : ℝ) * θ))
      ((1 - t * Real.cos θ) / (1 - 2 * t * Real.cos θ + t ^ 2)) := by
  let z : ℂ := (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hz : ‖z‖ < 1 := by
    simpa [z, norm_mul, Complex.norm_exp] using ht
  have hs := Complex.hasSum_re (hasSum_geometric_of_norm_lt_one hz)
  have hterm : ∀ j : ℕ, (z ^ j).re = t ^ j * Real.cos ((j : ℝ) * θ) := by
    intro j
    have hexp : Complex.exp ((θ : ℂ) * Complex.I) ^ j =
        Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    simp only [z, mul_pow, hexp, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
  simp_rw [hterm] at hs
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl
  rw [Complex.inv_re]
  simp only [z, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re, Complex.normSq_apply,
    Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.exp_ofReal_mul_I_im]
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem reciprocal_spectrum_fourier (θ : ℝ) :
    2 / (3 + Real.cos θ) =
      (1 / Real.sqrt 2) *
        (2 * (∑' j : ℕ, (-spectralDecay) ^ j * Real.cos ((j : ℝ) * θ)) - 1) := by
  have ht : |-spectralDecay| < 1 := by
    rw [abs_neg, abs_of_pos spectralDecay_pos]
    exact spectralDecay_lt_one
  rw [(hasSum_geometric_cos ht θ).tsum_eq]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num)
  have hc : 0 < 3 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
  have hd : 0 < 1 - 2 * (-spectralDecay) * Real.cos θ + (-spectralDecay) ^ 2 := by
    have h := Real.neg_one_le_cos θ
    have hr := spectralDecay_pos
    have hr' := spectralDecay_lt_one
    nlinarith [sq_pos_of_pos (show 0 < 1 - spectralDecay by linarith)]
  have hr : 1 + spectralDecay ^ 2 = 6 * spectralDecay := by
    dsimp [spectralDecay]
    nlinarith
  have hr' : 1 - spectralDecay ^ 2 = 4 * Real.sqrt 2 * spectralDecay := by
    dsimp [spectralDecay]
    nlinarith
  symm
  calc
    _ = (1 - spectralDecay ^ 2) /
        (Real.sqrt 2 * (1 - 2 * (-spectralDecay) * Real.cos θ + (-spectralDecay) ^ 2)) := by
      have hd' : 1 + spectralDecay * Real.cos θ * 2 + spectralDecay ^ 2 ≠ 0 := by nlinarith
      ring_nf
      field_simp [hp.ne', hd']
      ring
    _ = (4 * Real.sqrt 2 * spectralDecay) /
        (Real.sqrt 2 * (2 * spectralDecay * (3 + Real.cos θ))) := by
      rw [hr']
      congr 2
      nlinarith
    _ = 2 / (3 + Real.cos θ) := by
      field_simp [hp.ne', spectralDecay_pos.ne', hc.ne']
      ring

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

theorem cosineCorrelation_abs_le (d n j : ℕ) : |cosineCorrelation d n j| ≤ d := by
  unfold cosineCorrelation
  calc
    _ ≤ ∑ k ∈ Finset.range d,
        |Real.cos ((n : ℝ) * theta d k) * Real.cos ((j : ℝ) * theta d k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans
        (Real.abs_cos_le_one _)
    _ = _ := by simp

theorem cosineCorrelation_diagonal {d n : ℕ} (hn : 0 < n) (hnd : n < d) :
    cosineCorrelation d n n = (d : ℝ) / 2 := by
  simpa only [cosineCorrelation, ← pow_two] using sum_half_grid_cos_sq hn hnd

theorem cosineCorrelation_zero {d n j : ℕ} (hne : n ≠ j) (hjn : n + j < 2 * d) :
    cosineCorrelation d n j = 0 := sum_half_grid_cos_mul hne hjn

theorem summable_weighted_cosineCorrelation (d n N : ℕ) :
    Summable (fun j : ℕ => (-spectralDecay) ^ (j + N) * cosineCorrelation d n (j + N)) := by
  have hg := (summable_geometric_of_lt_one spectralDecay_pos.le spectralDecay_lt_one).mul_left
    ((d : ℝ) * spectralDecay ^ N)
  apply hg.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos spectralDecay_pos]
  calc
    _ ≤ spectralDecay ^ (j+N) * d :=
      mul_le_mul_of_nonneg_left (cosineCorrelation_abs_le d n (j+N)) (pow_nonneg spectralDecay_pos.le _)
    _ = _ := by rw [pow_add]; ring

theorem reciprocal_spectrum_statistic_series {d n : ℕ} (hn : 0 < n) (hnd : n < d) :
    (∑ k ∈ Finset.range d, weight d n k / eigenvalue d k) =
      Real.sqrt 2 * ∑' j : ℕ, (-spectralDecay) ^ j * cosineCorrelation d n j := by
  have ht : |-spectralDecay| < 1 := by
    rw [abs_neg, abs_of_pos spectralDecay_pos]
    exact spectralDecay_lt_one
  have hswap : (∑' j : ℕ, (-spectralDecay) ^ j * cosineCorrelation d n j) =
      ∑ k ∈ Finset.range d, Real.cos ((n : ℝ) * theta d k) *
        ∑' j : ℕ, (-spectralDecay) ^ j * Real.cos ((j : ℝ) * theta d k) := by
    simp only [cosineCorrelation, Finset.mul_sum]
    have hs := Summable.tsum_finsetSum (s := Finset.range d)
      (f := fun k (j : ℕ) => Real.cos ((n : ℝ) * theta d k) *
        ((-spectralDecay) ^ j * Real.cos ((j : ℝ) * theta d k)))
      (fun k _ => (hasSum_geometric_cos ht (theta d k)).summable.mul_left _)
    simp_rw [← mul_assoc] at hs
    convert! hs using 1
    · congr 1
      ext j
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp_rw [mul_assoc, tsum_mul_left]
  rw [hswap]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpoint : ∀ k : ℕ, weight d n k / eigenvalue d k =
      Real.sqrt 2 * (Real.cos ((n : ℝ) * theta d k) *
        ∑' j : ℕ, (-spectralDecay) ^ j * Real.cos ((j : ℝ) * theta d k)) -
      (1 / Real.sqrt 2) * Real.cos ((n : ℝ) * theta d k) := by
    intro k
    have hden : 0 < 3 + Real.cos (theta d k) := by linarith [Real.neg_one_le_cos (theta d k)]
    have h := reciprocal_spectrum_fourier (theta d k)
    unfold weight eigenvalue
    rw [div_div_eq_mul_div, mul_div_assoc, h]
    have hrel : 2 / Real.sqrt 2 = Real.sqrt 2 := by
      apply (div_eq_iff hsqrt_pos.ne').mpr
      nlinarith
    calc
      _ = (2 / Real.sqrt 2) * (Real.cos ((n : ℝ) * theta d k) *
            ∑' j : ℕ, (-spectralDecay) ^ j * Real.cos ((j : ℝ) * theta d k)) -
          (1 / Real.sqrt 2) * Real.cos ((n : ℝ) * theta d k) := by ring
      _ = _ := by rw [hrel]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_half_grid_cos_eq_zero hn (by omega), mul_zero, sub_zero]

theorem reciprocal_spectrum_statistic_initial_sum {d n : ℕ} (hn : 0 < n) (hnd : n < d) :
    (∑ j ∈ Finset.range (2*d-n), (-spectralDecay) ^ j * cosineCorrelation d n j) =
      (-spectralDecay) ^ n * ((d : ℝ) / 2) := by
  rw [Finset.sum_eq_single n]
  · rw [cosineCorrelation_diagonal hn hnd]
  · intro j hj hne
    rw [cosineCorrelation_zero (Ne.symm hne) (by have := Finset.mem_range.mp hj; omega), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem reciprocal_spectrum_statistic_remainder {d n : ℕ} (hn : 0 < n) (hnd : n < d) :
    |(∑ k ∈ Finset.range d, weight d n k / eigenvalue d k) -
      (d : ℝ) / Real.sqrt 2 * (-spectralDecay) ^ n| ≤
      Real.sqrt 2 * d * spectralDecay ^ (2*d-n) / (1 - spectralDecay) := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsplit := (summable_weighted_cosineCorrelation d n 0).sum_add_tsum_nat_add (2*d-n)
  simp only [Nat.add_zero] at hsplit
  rw [reciprocal_spectrum_statistic_initial_sum hn hnd] at hsplit
  rw [reciprocal_spectrum_statistic_series hn hnd, ← hsplit]
  have hlead : Real.sqrt 2 * ((-spectralDecay)^n * ((d : ℝ)/2)) =
      (d : ℝ) / Real.sqrt 2 * (-spectralDecay)^n := by
    field_simp
    rw [hsqrt]
    ring
  rw [mul_add, hlead, add_sub_cancel_left, abs_mul, abs_of_pos hsqrt_pos]
  have htail : |∑' j : ℕ, (-spectralDecay)^(j+(2*d-n)) * cosineCorrelation d n (j+(2*d-n))| ≤
      ((d : ℝ) * spectralDecay^(2*d-n)) / (1-spectralDecay) := by
    have hg := (summable_geometric_of_lt_one spectralDecay_pos.le spectralDecay_lt_one).mul_left
      ((d : ℝ) * spectralDecay^(2*d-n))
    calc
      _ ≤ ∑' j : ℕ, ‖(-spectralDecay) ^ (j+(2*d-n)) * cosineCorrelation d n (j+(2*d-n))‖ :=
        norm_tsum_le_tsum_norm (summable_weighted_cosineCorrelation d n (2*d-n)).norm
      _ ≤ ∑' j : ℕ, ((d : ℝ) * spectralDecay^(2*d-n)) * spectralDecay^j := by
        apply Summable.tsum_le_tsum _ (summable_weighted_cosineCorrelation d n (2*d-n)).norm hg
        intro j
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos spectralDecay_pos]
        calc
          _ ≤ spectralDecay^(j+(2*d-n)) * d :=
            mul_le_mul_of_nonneg_left (cosineCorrelation_abs_le d n _) (pow_nonneg spectralDecay_pos.le _)
          _ = _ := by rw [pow_add]; ring
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one spectralDecay_pos.le spectralDecay_lt_one]; rfl
  calc
    _ ≤ Real.sqrt 2 * (((d : ℝ) * spectralDecay^(2*d-n)) / (1-spectralDecay)) :=
      mul_le_mul_of_nonneg_left htail hsqrt_pos.le
    _ = _ := by ring

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

theorem targetVariance_le_one (d k : ℕ) : (targetVariance d k : ℝ) ≤ 1 := by
  change (eigenvalue d k)⁻¹ ≤ 1
  exact inv_le_one_of_one_le₀ (eigenvalue_bounds d k).1

theorem targetGaussian_coordinate_law {d : ℕ} (k : Fin d) :
    HasLaw (fun x : Fin d → ℝ => x k) (gaussianReal 0 (targetVariance d k)) (targetGaussian d) :=
  (measurePreserving_eval (fun k : Fin d => gaussianReal 0 (targetVariance d k)) k).hasLaw

theorem diagonalStatistic_memLp {d : ℕ} (c : Fin d → ℝ) :
    MemLp (diagonalStatistic c) 2 (targetGaussian d) := by
  apply memLp_finsetSum
  intro k _
  exact (gaussian_sq_memLp (targetGaussian_coordinate_law k)).const_mul (c k)

theorem targetGaussian_statistic_mean {d : ℕ} (c : Fin d → ℝ) :
    ∫ u, diagonalStatistic c u ∂targetGaussian d = ∑ k, c k / eigenvalue d k := by
  unfold diagonalStatistic
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, gaussian_integral_sq (targetGaussian_coordinate_law _)]
    rfl
  · intro k _
    exact ((gaussian_sq_memLp (targetGaussian_coordinate_law k)).const_mul (c k)).integrable
      (by norm_num)

theorem targetGaussian_statistic_variance {d : ℕ} (c : Fin d → ℝ) :
    Var[diagonalStatistic c; targetGaussian d] =
      ∑ k, (c k)^2 * (2 * ((targetVariance d k : ℝ)^2)) := by
  have h := variance_sum_pi (μ := fun k : Fin d => gaussianReal 0 (targetVariance d k))
    (X := fun k (y : ℝ) => c k * y^2)
    (fun k => (gaussian_sq_memLp (HasLaw.id (μ := gaussianReal 0 (targetVariance d k)))).const_mul (c k))
  have hvar (k : Fin d) : Var[fun y : ℝ => y^2; gaussianReal 0 (targetVariance d k)] =
      2 * (targetVariance d k : ℝ)^2 :=
    gaussian_sq_variance (X := fun y : ℝ => y) HasLaw.id
  simp only [variance_const_mul, hvar] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext u
  simp [diagonalStatistic]

theorem targetGaussian_statistic_variance_le {d : ℕ} (c : Fin d → ℝ)
    (hc : ∀ k, |c k| ≤ 1) : Var[diagonalStatistic c; targetGaussian d] ≤ 2*d := by
  rw [targetGaussian_statistic_variance]
  calc
    _ ≤ ∑ _ : Fin d, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have hsq : (c k)^2 ≤ 1 := by simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (c k)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hc k)
      have hv := targetVariance_le_one d k
      have hn := (targetVariance d k).coe_nonneg
      have hv2 : (targetVariance d k : ℝ)^2 ≤ 1 := by nlinarith
      calc
        _ ≤ 1 * (2 * ((targetVariance d k : ℝ)^2)) := mul_le_mul_of_nonneg_right hsq (by positivity)
        _ ≤ 2 := by nlinarith
    _ = _ := by simp; ring

theorem targetGaussian_norm_mean_le (d : ℕ) :
    ∫ u, diagonalStatistic (fun _ : Fin d => 1) u ∂targetGaussian d ≤ d := by
  rw [targetGaussian_statistic_mean]
  calc
    _ ≤ ∑ _ : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have h := targetVariance_le_one d k
      change (eigenvalue d k)⁻¹ ≤ 1 at h
      simpa only [one_div] using h
    _ = _ := by simp

theorem lower_target_statistic {d q : ℕ} (hn : 2*q+1 < d) :
    |(∫ u, diagonalStatistic (fun k : Fin d => weight d (2*q+1) k) u ∂targetGaussian d) -
      (d : ℝ) / Real.sqrt 2 * (-spectralDecay)^(2*q+1)| ≤
        Real.sqrt 2 * d * spectralDecay^(2*d-(2*q+1)) / (1-spectralDecay) ∧
    Var[diagonalStatistic (fun k : Fin d => weight d (2*q+1) k); targetGaussian d] ≤ 2*d ∧
    (∫ u, diagonalStatistic (fun _ : Fin d => 1) u ∂targetGaussian d) ≤ d ∧
    Var[diagonalStatistic (fun _ : Fin d => 1); targetGaussian d] ≤ 2*d := by
  refine ⟨?_, targetGaussian_statistic_variance_le _ (fun _ => Real.abs_cos_le_one _),
    targetGaussian_norm_mean_le d, targetGaussian_statistic_variance_le _ (by simp)⟩
  rw [targetGaussian_statistic_mean,
    Fin.sum_univ_eq_sum_range (fun k => weight d (2*q+1) k / eigenvalue d k) d]
  exact reciprocal_spectrum_statistic_remainder (by omega) hn

theorem real_chebyshev {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω - ∫ z, X z ∂μ|} ≤ Var[X;μ] / c^2 := by
  have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
    (meas_ge_le_variance_div_sq hX hc)
  change (μ {ω | c ≤ |X ω - ∫ z, X z ∂μ|}).toReal ≤ _
  simpa only [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] using h

theorem separationEvent_measurable (d q : ℕ) : MeasurableSet (separationEvent d q) := by
  have hN : Measurable (diagonalStatistic (fun _ : Fin d => 1)) := by
    unfold diagonalStatistic; fun_prop
  have hS : Measurable (diagonalStatistic (fun k : Fin d => weight d (2*q+1) k)) := by
    unfold diagonalStatistic; fun_prop
  exact (measurableSet_le hN measurable_const).inter (measurableSet_lt measurable_const hS.abs)

theorem target_separation_tail {d q : ℕ} (hd : 0 < d)
    (hsep : separationThreshold d q <
      |∫ u, diagonalStatistic (fun k : Fin d => weight d (2*q+1) k) u ∂targetGaussian d|) :
    (targetGaussian d).real (separationEvent d q)ᶜ ≤ 2/(d : ℝ) +
      2*d / (|∫ u, diagonalStatistic (fun k : Fin d => weight d (2*q+1) k) u ∂targetGaussian d| -
        separationThreshold d q)^2 := by
  let N : (Fin d → ℝ) → ℝ := diagonalStatistic (fun _ : Fin d => 1)
  let S : (Fin d → ℝ) → ℝ := diagonalStatistic (fun k : Fin d => weight d (2*q+1) k)
  let m := ∫ u, S u ∂targetGaussian d
  let a := ∫ u, N u ∂targetGaussian d
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : a ≤ d := targetGaussian_norm_mean_le d
  have hS : Var[S;targetGaussian d] ≤ 2*d :=
    targetGaussian_statistic_variance_le _ (fun _ => Real.abs_cos_le_one _)
  have hN : Var[N;targetGaussian d] ≤ 2*d :=
    targetGaussian_statistic_variance_le _ (by simp)
  have hrad : 0 < |m| - separationThreshold d q := sub_pos.mpr hsep
  have h₁ := real_chebyshev (diagonalStatistic_memLp (fun _ : Fin d => 1)) hdr
  have h₂ := real_chebyshev
    (diagonalStatistic_memLp (fun k : Fin d => weight d (2*q+1) k)) hrad
  have hsub : (separationEvent d q)ᶜ ⊆
      {u | (d : ℝ) ≤ |N u - a|} ∪ {u | |m| - separationThreshold d q ≤ |S u - m|} := by
    intro u hu
    change ¬ (N u ≤ 2*d ∧ separationThreshold d q < |S u|) at hu
    by_cases hnu : N u ≤ 2*d
    · right
      have hsu : |S u| ≤ separationThreshold d q := le_of_not_gt (fun h => hu ⟨hnu,h⟩)
      have habs := abs_sub_abs_le_abs_sub m (S u)
      rw [abs_sub_comm m (S u)] at habs
      change |m| - separationThreshold d q ≤ |S u-m|
      linarith only [habs,hsu]
    · left
      have habs := le_abs_self (N u-a)
      have hnu' := lt_of_not_ge hnu
      change (d : ℝ) ≤ |N u - a|
      linarith only [habs,hnu',ha]
  calc
    _ ≤ (targetGaussian d).real ({u | (d : ℝ) ≤ |N u-a|} ∪
        {u | |m|-separationThreshold d q ≤ |S u-m|}) := measureReal_mono hsub
    _ ≤ (targetGaussian d).real {u | (d : ℝ) ≤ |N u-a|} +
        (targetGaussian d).real {u | |m|-separationThreshold d q ≤ |S u-m|} :=
      measureReal_union_le _ _
    _ ≤ Var[N;targetGaussian d]/(d : ℝ)^2 +
        Var[S;targetGaussian d]/(|m|-separationThreshold d q)^2 := add_le_add h₁ h₂
    _ ≤ 2*d/(d : ℝ)^2 + 2*d/(|m|-separationThreshold d q)^2 := by
      exact add_le_add (div_le_div_of_nonneg_right hN (sq_nonneg _))
        (div_le_div_of_nonneg_right hS (sq_nonneg _))
    _ = _ := by
      congr 1
      field_simp

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_SpectrumOperator
attribute [-instance] _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling.LowerBound

theorem diagonalStatistic_eq_dotProduct {d : ℕ} (c u : Fin d → ℝ) :
    diagonalStatistic c u = dotProduct u (Matrix.diagonal c *ᵥ u) := by
  simp only [diagonalStatistic, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem normStatistic_eq_dotProduct {d : ℕ} (u : Fin d → ℝ) :
    diagonalStatistic (fun _ => 1) u = dotProduct u u := by
  simp [diagonalStatistic, dotProduct, pow_two]

theorem separationThreshold_eq {d q : ℕ} (hd : 0 < d) :
    2 * blockTolerance d q * (2*d) = separationThreshold d q := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := Real.sq_sqrt hdr.le
  have hsn : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  unfold blockTolerance separationThreshold
  field_simp
  nlinarith

theorem algorithm_span_separation_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d q : ℕ}
    (hqd : 4*q+1 < 2*d) (ht : blockTolerance d q ≤ 1/2)
    {rows : Ω → Fin d → Fin (q+1) → ℝ}
    (hrows : HasLaw rows (gaussianRows d (q+1)) P) (U : Ω → Fin d → ℝ)
    (hU : ∀ᵐ ω ∂P, U ω ∈ krylovSpace (rows ω)) :
    P.real {ω | U ω ∈ separationEvent d q} ≤ 1/100 := by
  obtain ⟨G,hG,hm,hgood⟩ := lower_span_statistic hqd ht
  have hsub : {ω | U ω ∈ separationEvent d q} ≤ᵐ[P] {ω | rows ω ∈ Gᶜ} := by
    filter_upwards [hU] with ω hu
    intro hsep
    change rows ω ∉ G
    intro hg
    have hstat := hgood (rows ω) hg (U ω) hu
    rw [← diagonalStatistic_eq_dotProduct, ← normStatistic_eq_dotProduct] at hstat
    have hn := hsep.1
    have hs := hsep.2
    have hbound : 2 * blockTolerance d q * diagonalStatistic (fun _ => 1) (U ω) ≤
        separationThreshold d q := by
      rw [← separationThreshold_eq (by omega : 0 < d)]
      exact mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) (blockTolerance_pos (q := q) (by omega : 0 < d)).le)
    exact (not_lt_of_ge (hstat.trans hbound)) hs
  have hmono := ENNReal.toReal_mono (measure_ne_top P {ω | rows ω ∈ Gᶜ})
    (measure_mono_ae hsub)
  change P.real {ω | U ω ∈ separationEvent d q} ≤ P.real {ω | rows ω ∈ Gᶜ} at hmono
  have hlaw : P.real {ω | rows ω ∈ Gᶜ} = (gaussianRows d (q+1)).real Gᶜ :=
    hrows.measureReal_eq hG.compl
  rw [hlaw, measureReal_compl hG, probReal_univ] at hmono
  linarith

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace
open Matrix WithLp

lemma spectrumOperator_symmetric (d : ℕ) :
    (spectrumOperator d).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (spectrumOperator d x) y = inner ℝ x (spectrumOperator d y)
  simp only [PiLp.inner_apply, Real.inner_apply, spectrumOperator_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma quadraticOperator_symmetric {d : ℕ} (O : Rotations d) :
    (quadraticOperator O).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ ((rotationIsometry O) (spectrumOperator d ((rotationIsometry O).symm x))) y =
    inner ℝ x ((rotationIsometry O) (spectrumOperator d ((rotationIsometry O).symm y)))
  rw [← (rotationIsometry O).apply_symm_apply y, ← (rotationIsometry O).apply_symm_apply x]
  simp only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]
  exact spectrumOperator_symmetric d _ _

lemma quadraticOperator_bounds {d : ℕ} (O : Rotations d) (x : Point d) :
    ‖x‖^2 ≤ inner ℝ x (quadraticOperator O x) ∧
      inner ℝ x (quadraticOperator O x) ≤ 2 * ‖x‖^2 := by
  let y := (rotationIsometry O).symm x
  have hinner : inner ℝ x (quadraticOperator O x) =
      ∑ k : Fin d, eigenvalue d k * (y k)^2 := by
    change inner ℝ x ((rotationIsometry O) (spectrumOperator d y)) = _
    rw [← (rotationIsometry O).apply_symm_apply x]
    simp only [LinearIsometryEquiv.inner_map_map, PiLp.inner_apply, Real.inner_apply,
      spectrumOperator_apply]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [y]
    ring
  have hnorm : ‖x‖^2 = ∑ k : Fin d, (y k)^2 := by
    rw [← (rotationIsometry O).symm.norm_map x, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  rw [hinner, hnorm, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro k _
    have hb := (eigenvalue_bounds d k).1
    nlinarith [sq_nonneg (y k)]
  · apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (eigenvalue_bounds d k).2 (sq_nonneg _)

lemma quadraticPotential_hasGradientAt {d : ℕ} (O : Rotations d) (x : Point d) :
    HasGradientAt (quadraticPotential O) (quadraticOperator O x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := ((hasFDerivAt_id x).inner ℝ (quadraticOperator O).hasFDerivAt).const_smul (1 / 2 : ℝ)
  convert! hd using 1
  · ext y
    simp only [quadraticPotential, Pi.smul_apply, smul_eq_mul, id_eq]
    ring
  ext y
  have hs := quadraticOperator_symmetric O x y
  change inner ℝ (quadraticOperator O x) y = inner ℝ x (quadraticOperator O y) at hs
  change inner ℝ (quadraticOperator O x) y =
    (1 / 2 : ℝ) * (inner ℝ x (quadraticOperator O y) + inner ℝ y (quadraticOperator O x))
  rw [← hs, real_inner_comm y (quadraticOperator O x)]
  ring

@[simp] theorem quadraticPotential_gradient {d : ℕ} (O : Rotations d) :
    gradient (quadraticPotential O) = quadraticOperator O :=
  gradient_eq (quadraticPotential_hasGradientAt O)

theorem quadraticPotential_admissible {d : ℕ} (O : Rotations d) :
    Admissible (quadraticPotential O) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (contDiff_id.inner ℝ (quadraticOperator O).contDiff).div_const 2
  · simp [quadraticPotential]
  · simp
  · intro x v
    rw [quadraticPotential_gradient, (quadraticOperator O).fderiv]
    exact quadraticOperator_bounds O v

theorem quadratic_firstOrderReply {d : ℕ} (O : Rotations d) (x : Point d) :
    firstOrderReply (quadraticPotential O) x =
      (inner ℝ x (quadraticOperator O x) / 2, quadraticOperator O x) := by
  simp [firstOrderReply, quadraticPotential]

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_DensityCoefficient
attribute [-instance] _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling.LowerBound
open Matrix WithLp ProbabilityTheory
open scoped RealInnerProductSpace

lemma targetVariance_ne_zero (d k : ℕ) : targetVariance d k ≠ 0 := by
  apply ne_of_gt
  change 0 < (eigenvalue d k)⁻¹
  apply inv_pos.mpr
  linarith [(eigenvalue_bounds d k).1]

lemma gaussianPDF_targetVariance (d k : ℕ) (x : ℝ) :
    gaussianPDF 0 (targetVariance d k) x =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi*(targetVariance d k : ℝ)))⁻¹) *
        ENNReal.ofReal (Real.exp (-(eigenvalue d k * x^2) / 2)) := by
  unfold gaussianPDF gaussianPDFReal
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 2
  apply congrArg Real.exp
  change -(x - 0)^2 / (2 * (eigenvalue d k)⁻¹) = -(eigenvalue d k * x^2) / 2
  simp only [sub_zero, div_mul_eq_div_div, div_inv_eq_mul]
  ring

lemma targetGaussian_density (d : ℕ) :
    targetGaussian d = (volume : Measure (Fin d → ℝ)).withDensity
      (fun x => densityCoefficient d *
        ENNReal.ofReal (Real.exp (-(∑ k : Fin d, eigenvalue d k * (x k)^2) / 2))) := by
  have hg (k : Fin d) : gaussianReal 0 (targetVariance d k) =
      volume.withDensity (gaussianPDF 0 (targetVariance d k)) :=
    gaussianReal_of_var_ne_zero _ (targetVariance_ne_zero d k)
  have (k : Fin d) : IsProbabilityMeasure
      (volume.withDensity (gaussianPDF 0 (targetVariance d k))) := by
    rw [← hg k]
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  unfold targetGaussian
  simp_rw [hg]
  rw [pi_withDensity_fin _ _ (fun _ => measurable_gaussianPDF _ _)]
  congr 1
  ext x
  simp_rw [gaussianPDF_targetVariance]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

lemma quadraticPotential_eq_spectral {d : ℕ} (O : Rotations d) (x : Point d) :
    quadraticPotential O x =
      (∑ k : Fin d, eigenvalue d k * ((rotationIsometry O).symm x k)^2) / 2 := by
  unfold quadraticPotential
  congr 1
  change inner ℝ x ((rotationIsometry O)
    (spectrumOperator d ((rotationIsometry O).symm x))) = _
  rw [← (rotationIsometry O).apply_symm_apply x]
  simp only [LinearIsometryEquiv.inner_map_map, PiLp.inner_apply, Real.inner_apply,
      spectrumOperator_apply, LinearIsometryEquiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem quadratic_gibbs_eq_gaussian {d : ℕ} (O : Rotations d) :
    (targetGaussian d).map (fun u => rotationIsometry O (toLp 2 u)) =
      gibbs (quadraticPotential O) := by
  haveI : IsProbabilityMeasure ((targetGaussian d).map (fun u => rotationIsometry O (toLp 2 u))) :=
    Measure.isProbabilityMeasure_map (Continuous.measurable (by fun_prop)).aemeasurable
  apply eq_gibbs_of_proportional (C := densityCoefficient d)
  let e : (Fin d → ℝ) ≃ᵐ Point d :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).trans (rotationIsometry O).toMeasurableEquiv
  have he : MeasurePreserving e volume volume :=
    (rotationIsometry O).measurePreserving.comp (PiLp.volume_preserving_toLp (Fin d))
  change (targetGaussian d).map e = _
  rw [targetGaussian_density, map_withDensity_of_measurePreserving e he (by fun_prop)]
  have hfun : (fun y : Point d => densityCoefficient d *
        ENNReal.ofReal (Real.exp (-(∑ k : Fin d, eigenvalue d k * (e.symm y k)^2)/2))) =
      densityCoefficient d • gibbsDensity (quadraticPotential O) := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, gibbsDensity, quadraticPotential_eq_spectral]
    simp only [neg_div]
    rfl
  rw [hfun, withDensity_smul]
  exact (Real.continuous_exp.comp
    (quadraticPotential_admissible O).smooth.continuous.neg).measurable.ennreal_ofReal

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling

theorem TVAtMost.map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ ν : Measure E} {ε : ℝ} (h : TVAtMost μ ν ε)
    {f : E → F} (hf : Measurable f) : TVAtMost (μ.map f) (ν.map f) ε := by
  intro s hs
  simpa only [Measure.real, Measure.map_apply hf hs] using h (f ⁻¹' s) (hs.preimage hf)

end LogConcaveSampling

namespace LogConcaveSampling
lemma prob_prod_event_lower {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set (X × Y)} (hs : MeasurableSet s) {a : ℝ}
    (h : ∀ y, a ≤ μ.real ((fun x => (x,y)) ⁻¹' s)) : a ≤ (μ.prod ν).real s := by
  have h' : ENNReal.ofReal a ≤ (μ.prod ν) s := by
    rw [Measure.prod_apply_symm hs]
    calc
      _ = ∫⁻ _ : Y, ENNReal.ofReal a ∂ν := by simp
      _ ≤ _ := lintegral_mono (fun y =>
        (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mpr (h y))
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (μ.prod ν) s)).mp h'
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_HardEigenOutput
attribute [-instance] _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling.LowerBound
open WithLp
open scoped RealInnerProductSpace

lemma spectrum_iterate_apply {d : ℕ} (j : ℕ) (x : Point d) (k : Fin d) :
    ((spectrumOperator d).toLinearMap^[j]) x k = x k * eigenvalue d k ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change spectrumOperator d (((spectrumOperator d).toLinearMap^[j]) x) k = _
    rw [spectrumOperator_apply,ih,pow_succ]
    ring

lemma orbitHull_in_krylov {d r : ℕ} (a : Fin (r+1) → Point d) {u : Point d}
    (hu : u ∈ orbitHull (spectrumOperator d).toLinearMap r a) :
    ofLp u ∈ krylovSpace (fun k i => a i k) := by
  let coord : Point d →ₗ[ℝ] (Fin d → ℝ) :=
    {toFun := ofLp, map_add' := by intros; rfl, map_smul' := by intros; rfl}
  have h : orbitHull (spectrumOperator d).toLinearMap r a ≤
      (krylovSpace (fun k i => a i k)).comap coord := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,j,hj,rfl⟩
    apply Submodule.subset_span
    refine ⟨i,j,hj,?_⟩
    funext k
    exact spectrum_iterate_apply j (a i) k
  exact h hu

lemma linearReply_eq_quadratic {d : ℕ} (O : Rotations d) (x : Point d) :
    linearReply (spectrumOperator d) O x = firstOrderReply (quadraticPotential O) x := by
  rw [quadratic_firstOrderReply]
  apply Prod.ext
  · change ⟪(rotationIsometry O).symm x, spectrumOperator d ((rotationIsometry O).symm x)⟫ / 2 = _
    have h := (rotationIsometry O).inner_map_map ((rotationIsometry O).symm x)
      (spectrumOperator d ((rotationIsometry O).symm x))
    simpa only [LinearIsometryEquiv.apply_symm_apply, quadraticOperator,
      ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe] using congrArg (fun z : ℝ => z/2) h.symm
  · rfl

lemma linearHistory_eq_quadratic {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (O : Rotations d) (ω : Ω) (n : ℕ) :
    linearHistory A (spectrumOperator d) O ω n = A.history (quadraticPotential O) ω n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [linearHistory,OracleAlgorithm.history,ih,linearReply_eq_quadratic]

lemma measurable_hardEigenOutput {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) : Measurable (hardEigenOutput A) := by
  have hr : Measurable (fun p : Ω × Rotations d => A.run (quadraticPotential p.2) p.1) := by
    simpa only [OracleAlgorithm.run,← linearHistory_eq_quadratic,Function.comp_def] using
      A.output_measurable.comp (measurable_fst.prodMk (measurable_linearHistory A (spectrumOperator d) q))
  have haction : Measurable (fun p : Rotations d × Point d => (rotationIsometry p.1).symm p.2) := by
    have hh := (continuous_rotation_apply (d := d)).measurable.comp
      (f := fun p : Rotations d × Point d => (p.1⁻¹,p.2))
      (measurable_fst.inv.prodMk measurable_snd)
    simpa only [Function.comp_def,rotationIsometry_inv_apply] using hh
  exact (measurable_ofLp 2 _).comp (f := fun p : Ω × Rotations d =>
    (rotationIsometry p.2).symm (A.run (quadraticPotential p.2) p.1))
    (haction.comp (f := fun p : Ω × Rotations d =>
      (p.2,A.run (quadraticPotential p.2) p.1)) (measurable_snd.prodMk hr))

theorem hard_algorithm_separation {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (hd : 2*q+1 ≤ d) (hqd : 4*(q+q)+1 < 2*d) (ht : blockTolerance d (q+q) ≤ 1/2) :
    (μ.prod (rotationHaar d)).real {p | hardEigenOutput A p ∈ separationEvent d (q+q)} ≤ 1/100 := by
  let P := couplingLaw μ d q
  let U : CouplingNoise Ω d q → Fin d → ℝ := fun p =>
    ofLp (finishCoordinate A (by omega) (couplingState A (spectrumOperator d) hd p).1)
  let rows : CouplingNoise Ω d q → Fin d → Fin (q+q+1) → ℝ := fun p k i => couplingColumns p i k
  have hrows : HasLaw rows (gaussianRows d (q+q+1)) P := by
    have he : MeasurePreserving (fun a : Fin (q+q+1) → Point d => fun k i => a i k)
        (Measure.pi (fun _ : Fin (q+q+1) => stdGaussian (Point d))) (gaussianRows d (q+q+1)) :=
      ⟨by fun_prop,gaussianColumns_rows_law d (q+q+1)⟩
    exact (he.comp (couplingColumns_law μ)).hasLaw
  have hU : ∀ᵐ p ∂P, U p ∈ krylovSpace (rows p) := by
    filter_upwards [coupling_output_span μ A (spectrumOperator d) hd] with p hp
    exact orbitHull_in_krylov (couplingColumns p) hp
  have hb := algorithm_span_separation_bound hqd ht hrows U hU
  have he : ∀ᵐ p ∂P, U p = hardEigenOutput A
      (finishComplete A (by omega) (couplingState A (spectrumOperator d) hd p)) := by
    filter_upwards [coupling_output_correct μ A (spectrumOperator d) hd] with p hp
    simpa only [hardEigenOutput,OracleAlgorithm.run,linearHistory_eq_quadratic] using congrArg ofLp hp
  have hmeas : MeasurableSet {p | hardEigenOutput A p ∈ separationEvent d (q+q)} :=
    (separationEvent_measurable d (q+q)).preimage (measurable_hardEigenOutput A)
  rw [← coupling_complete_law μ A (spectrumOperator d) hd,
    Measure.real,Measure.map_apply
      ((measurable_finishComplete A (by omega)).comp (measurable_couplingState A (spectrumOperator d) hd)) hmeas]
  change P.real {p | hardEigenOutput A (finishComplete A (by omega) (couplingState A (spectrumOperator d) hd p)) ∈ separationEvent d (q+q)} ≤ _
  have hs : {p | hardEigenOutput A (finishComplete A (by omega) (couplingState A (spectrumOperator d) hd p)) ∈ separationEvent d (q+q)}
      =ᵐ[P] {p | U p ∈ separationEvent d (q+q)} := by
    filter_upwards [he] with p hp
    exact congrArg (fun z : Fin d → ℝ => z ∈ separationEvent d (q+q)) hp.symm
  rwa [measureReal_congr hs]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma quadratic_gibbs_eigenframe {d : ℕ} (O : Rotations d) :
    (gibbs (quadraticPotential O)).map (fun x => ofLp ((rotationIsometry O).symm x)) =
      targetGaussian d := by
  rw [← quadratic_gibbs_eq_gaussian O,Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply,WithLp.ofLp_toLp]
  exact Measure.map_id

lemma hardEigenOutput_tv {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (h : ∀ O : Rotations d, TVAtMost (μ.map (A.run (quadraticPotential O)))
      (gibbs (quadraticPotential O)) (1/10)) (O : Rotations d) :
    TVAtMost (μ.map (fun ω => hardEigenOutput A (ω,O))) (targetGaussian d) (1/10) := by
  have hr : Measurable (A.run (quadraticPotential O)) := by
    change Measurable (fun ω : Ω => A.output (ω,A.history (quadraticPotential O) ω q))
    simp_rw [← linearHistory_eq_quadratic A O]
    exact A.output_measurable.comp (f := fun ω : Ω =>
      (ω,linearHistory A (spectrumOperator d) O ω q))
      (measurable_id.prodMk ((measurable_linearHistory A (spectrumOperator d) q).comp
        (f := fun ω : Ω => (ω,O)) (measurable_id.prodMk measurable_const)))
  have ht := (h O).map (f := fun x => ofLp ((rotationIsometry O).symm x)) (by fun_prop)
  rwa [quadratic_gibbs_eigenframe,Measure.map_map (by fun_prop) hr] at ht

theorem canSample_target_separation_bound {d q : ℕ}
    (hd : 2*q+1 ≤ d) (hqd : 4*(q+q)+1 < 2*d) (ht : blockTolerance d (q+q) ≤ 1/2)
    (h : CanSample d q) : (targetGaussian d).real (separationEvent d (q+q)) ≤ 11/100 := by
  obtain ⟨Ω,mΩ,μ,hμ,A,hA⟩ := h
  have hTV := hardEigenOutput_tv μ A (fun O => (hA _ (quadraticPotential_admissible O)).2)
  have hevent := hard_algorithm_separation μ A hd hqd ht
  have hm : MeasurableSet {p | hardEigenOutput A p ∈ separationEvent d (q+q)} :=
    (separationEvent_measurable d (q+q)).preimage (measurable_hardEigenOutput A)
  have hlower := prob_prod_event_lower μ (rotationHaar d) hm
    (a := (targetGaussian d).real (separationEvent d (q+q)) - 1/10) (fun O => by
      have hh := hTV O _ (separationEvent_measurable d (q+q))
      have hb : Measurable (fun ω : Ω => hardEigenOutput A (ω,O)) :=
        (measurable_hardEigenOutput A).comp (f := fun ω : Ω => (ω,O))
          (measurable_id.prodMk measurable_const)
      rw [Measure.real,Measure.map_apply hb (separationEvent_measurable d (q+q))] at hh
      have hh' := (abs_le.mp hh).1
      change -(1/10 : ℝ) ≤ μ.real {ω | hardEigenOutput A (ω,O) ∈ separationEvent d (q+q)} - _ at hh'
      change _ ≤ μ.real {ω | hardEigenOutput A (ω,O) ∈ separationEvent d (q+q)}
      linarith)
  linarith

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma spectralDecay_bounds : (1/8 : ℝ) ≤ spectralDecay ∧ spectralDecay ≤ 1/4 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h' := Real.sqrt_nonneg (2 : ℝ)
  dsimp [spectralDecay]
  constructor <;> nlinarith

theorem target_mean_lower {d r : ℕ} (hn : 2*r+1 < d) :
    (d : ℝ) / (4 * 8^(2*r+1)) ≤
      |∫ u, diagonalStatistic (fun k : Fin d => weight d (2*r+1) k) u ∂targetGaussian d| := by
  let n := 2*r+1
  let m := ∫ u, diagonalStatistic (fun k : Fin d => weight d (2*r+1) k) u ∂targetGaussian d
  have hr := (lower_target_statistic hn).1
  have hp : 0 < spectralDecay := spectralDecay_pos
  have hb := spectralDecay_bounds
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hp2 : spectralDecay^2 ≤ 1/16 := by nlinarith
  have hpow : spectralDecay^(2*d-n) ≤ spectralDecay^(n+2) :=
    pow_le_pow_of_le_one hp.le spectralDecay_lt_one.le (by dsimp [n]; omega)
  have hrem : Real.sqrt 2 * d * spectralDecay^(2*d-n) / (1-spectralDecay) ≤
      (d : ℝ) * spectralDecay^n / 4 := by
    calc
      _ ≤ 2 * d * spectralDecay^(n+2) / (1/2) := by
        apply div_le_div₀ (by positivity)
        · gcongr
        · norm_num
        · linarith
      _ = 4 * d * spectralDecay^n * spectralDecay^2 := by rw [pow_add]; ring
      _ ≤ (d : ℝ) * spectralDecay^n / 4 := by
        have hh := mul_le_mul_of_nonneg_left hp2 (mul_nonneg hd (pow_nonneg hp.le n))
        nlinarith
  have hlead : (d : ℝ) * spectralDecay^n / 2 ≤ |(d : ℝ) / Real.sqrt 2 * (-spectralDecay)^n| := by
    rw [abs_mul,abs_div,abs_pow,abs_neg,abs_of_nonneg hd,abs_of_pos hs,abs_of_pos hp]
    calc
      _ = ((d : ℝ)/2) * spectralDecay^n := by ring
      _ ≤ _ := by gcongr
  have htri := abs_sub_abs_le_abs_sub ((d : ℝ) / Real.sqrt 2 * (-spectralDecay)^n) m
  rw [abs_sub_comm] at htri
  have hmean : (d : ℝ) * spectralDecay^n / 4 ≤ |m| := by
    change |m - (d : ℝ) / Real.sqrt 2 * (-spectralDecay)^n| ≤ _ at hr
    linarith only [hr,hrem,hlead,htri]
  calc
    _ = (d : ℝ) * (1/8)^n / 4 := by rw [div_pow]; simp only [one_pow]; field_simp; rfl
    _ ≤ (d : ℝ) * spectralDecay^n / 4 := by gcongr; exact hb.1
    _ ≤ _ := hmean

lemma lower_denominator (q : ℕ) : (4 : ℝ) * 8^(2*(q+q)+1) = 2^(12*q+5) := by
  rw [show (4 : ℝ) = 2^2 by norm_num, show (8 : ℝ) = 2^3 by norm_num,
    ← pow_mul,← pow_add]
  congr 1
  omega

lemma polynomial_threshold_le_pow (q : ℕ) :
    160 * ((q+q : ℕ)+1 : ℝ)^2 + 20 ≤ (2 : ℝ)^(2*q+10) := by
  have hq : ((q+q : ℕ)+1 : ℝ) ≤ (2 : ℝ)^(q+1) := by
    have h := (Nat.lt_two_pow_self (n := q)).succ_le
    have hh : (q : ℝ)+1 ≤ (2 : ℝ)^q := by exact_mod_cast h
    push_cast
    rw [pow_succ]
    linarith
  have hp : (1 : ℝ) ≤ 2^(2*q+2) := one_le_pow₀ (by norm_num)
  have hsq : (((q+q : ℕ)+1 : ℝ)^2) ≤ (2 : ℝ)^(2*q+2) := by
    calc
      _ ≤ ((2 : ℝ)^(q+1))^2 := by gcongr
      _ = _ := by rw [← pow_mul]; congr 1; omega
  calc
    _ ≤ 180 * (2 : ℝ)^(2*q+2) := by nlinarith
    _ ≤ 256 * (2 : ℝ)^(2*q+2) := by gcongr; norm_num
    _ = _ := by rw [show 256 = (2:ℝ)^8 by norm_num,← pow_add]; congr 1; omega

lemma sqrt_exponential_lower {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) :
    (2 : ℝ)^(32*(q+1)) ≤ Real.sqrt d := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  have hh : (2 : ℝ)^(64*(q+1)) ≤ d := by exact_mod_cast hd
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [← pow_mul]
  congr 1
  omega

lemma target_large_mean {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) (hn : 2*(q+q)+1 < d) :
    separationThreshold d (q+q) + 20 * Real.sqrt d ≤
      |∫ u, diagonalStatistic (fun k : Fin d => weight d (2*(q+q)+1) k) u ∂targetGaussian d| := by
  have hm := target_mean_lower hn
  rw [lower_denominator] at hm
  have hs := sqrt_exponential_lower hd
  have hcoeff := polynomial_threshold_le_pow q
  have hp : (2 : ℝ)^(2*q+10) * 2^(12*q+5) ≤ Real.sqrt d := by
    calc
      _ = (2 : ℝ)^(14*q+15) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2^(32*(q+1)) := by apply pow_le_pow_right₀ (by norm_num); omega
      _ ≤ _ := hs
  have hh : (160 * (((q+q : ℕ)+1 : ℝ))^2 + 20) * 2^(12*q+5) ≤ Real.sqrt d :=
    le_trans (mul_le_mul_of_nonneg_right hcoeff (by positivity)) hp
  have hh' := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg (d : ℝ))
  rw [← sq,Real.sq_sqrt (Nat.cast_nonneg d)] at hh'
  calc
    _ = (160 * (((q+q : ℕ)+1 : ℝ))^2 + 20) * Real.sqrt d := by
      unfold separationThreshold
      push_cast
      ring
    _ ≤ (d : ℝ) / 2^(12*q+5) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [hh']
    _ ≤ _ := hm

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma exponential_dimension_bounds {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) :
    100 ≤ d ∧ 2*(q+q)+1 < d ∧ 2*q+1 ≤ d ∧ 4*(q+q)+1 < 2*d := by
  have hlin := (Nat.lt_two_pow_self (n := 64*(q+1))).trans_le hd
  have hexp : 2^64 ≤ 2^(64*(q+1)) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h100 : 100 ≤ d := le_trans (by norm_num : 100 ≤ 2^64) (hexp.trans hd)
  omega

lemma exponential_tolerance {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) :
    blockTolerance d (q+q) ≤ 1/2 := by
  have hpos : 0 < d := by have := (exponential_dimension_bounds hd).1; omega
  have hs := sqrt_exponential_lower hd
  have hcoeff := polynomial_threshold_le_pow q
  have hp : (2 : ℝ)^(2*q+10) ≤ 2^(32*(q+1)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hh : 80 * (((q+q : ℕ)+1 : ℝ))^2 ≤ Real.sqrt d := by
    have hsq := sq_nonneg (((q+q : ℕ)+1 : ℝ))
    linarith
  unfold blockTolerance
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hpos))).mpr
  push_cast at hh ⊢
  linarith

theorem target_event_large {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) :
    9/10 ≤ (targetGaussian d).real (separationEvent d (q+q)) := by
  have hb := exponential_dimension_bounds hd
  have hpos : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hpos
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdr
  have hm := target_large_mean hd hb.2.1
  let m := |∫ u, diagonalStatistic (fun k : Fin d => weight d (2*(q+q)+1) k) u ∂targetGaussian d|
  have hmargin : 20 * Real.sqrt d ≤ m - separationThreshold d (q+q) := by
    dsimp [m]; linarith only [hm]
  have hsep : separationThreshold d (q+q) < m := by linarith
  have htail := target_separation_tail hpos hsep
  have hden : 400 * (d : ℝ) ≤ (m-separationThreshold d (q+q))^2 := by
    calc
      _ = (20 * Real.sqrt (d : ℝ))^2 := by rw [mul_pow,Real.sq_sqrt hdr.le]; ring
      _ ≤ _ := by gcongr
  have h₁ : 2/(d : ℝ) ≤ 1/50 := by
    apply (div_le_iff₀ hdr).mpr
    have hh : (100 : ℝ) ≤ d := by exact_mod_cast hb.1
    linarith
  have h₂ : 2*d/(m-separationThreshold d (q+q))^2 ≤ 1/200 := by
    apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hsep))).mpr
    linarith
  rw [measureReal_compl (separationEvent_measurable d (q+q)),probReal_univ] at htail
  change 1 - (targetGaussian d).real (separationEvent d (q+q)) ≤ 2/(d : ℝ) +
    2*d/(m-separationThreshold d (q+q))^2 at htail
  linarith

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

theorem not_canSample_exponential {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) : ¬ CanSample d q := by
  intro h
  have hb := exponential_dimension_bounds hd
  have h₁ := canSample_target_separation_bound hb.2.2.1 hb.2.2.2 (exponential_tolerance hd) h
  have h₂ := target_event_large hd
  linarith

lemma exponential_of_small_log {d q : ℕ} (hd : 2^128 ≤ d)
    (hq : (q : ℝ) < (128 * Real.log 2)⁻¹ * Real.log d) : 2^(64*(q+1)) ≤ d := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hdp : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hdp
  have hd' : (2 : ℝ)^128 ≤ d := by exact_mod_cast hd
  have hlog : 128 * Real.log (2 : ℝ) ≤ Real.log d := by
    have hh := Real.log_le_log (by positivity) hd'
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hq' : 128 * Real.log (2 : ℝ) * q < Real.log d := by
    have hh := mul_lt_mul_of_pos_left hq (show 0 < 128 * Real.log (2 : ℝ) by positivity)
    rwa [← mul_assoc,mul_inv_cancel₀ (by positivity),one_mul] at hh
  have hx : Real.log ((2 : ℝ)^(64*(q+1))) ≤ Real.log d := by
    rw [Real.log_pow]
    push_cast
    nlinarith only [hlog,hq']
  have hexp := (Real.log_le_log_iff (by positivity) hdr).mp hx
  exact_mod_cast hexp

theorem source_logarithmic_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ENNReal.ofReal (c * Real.log (d : ℝ)) ≤ (queryComplexity d).toENNReal := by
  refine ⟨(128 * Real.log 2)⁻¹, by positivity, 2^128, by norm_num, ?_⟩
  intro d hd
  have hfeasible : ∀ q : ℕ, CanSample d q → (128 * Real.log 2)⁻¹ * Real.log d ≤ q := by
    intro q hq
    by_contra hh
    exact not_canSample_exponential (exponential_of_small_log hd (lt_of_not_ge hh)) hq
  unfold queryComplexity
  rw [sInf_image]
  simp only [ENat.toENNReal_iInf]
  apply le_iInf
  intro q
  apply le_iInf
  intro hq
  simpa only [ENat.toENNReal_coe,ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal (hfeasible q hq)

end LogConcaveSampling.LowerBound

end LowerProof

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subpolynomial upper bounds and logarithmic lower bounds for exact first-order sampling, with optimal dimension exponent zero. -/

section

noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory
open scoped Topology ENNReal

lemma CanSample.queryComplexity_le {d q : ℕ} (hq : CanSample d q) :
    (queryComplexity d).toENNReal≤ENNReal.ofReal (q:ℝ) := by
  have hle : queryComplexity d≤(q:ℕ∞) := sInf_le ⟨q,hq,rfl⟩
  simpa only [ENat.toENNReal_coe,ENNReal.ofReal_natCast] using ENat.toENNReal_mono hle

theorem source_subpolynomial_upper :
    ∀ ε : ℝ,0<ε → ∃ C : ℝ,∀ d : ℕ,2≤d →
      (queryComplexity d).toENNReal≤ENNReal.ofReal (C*(d:ℝ)^ε) := by
  intro ε hε
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp (eventually_subpolynomial_sampler hε)
  let C : ℝ := (10*2^d₀:ℕ)+1
  have hC : 1≤C := by dsimp [C]; have := (Nat.cast_nonneg (10*2^d₀) : (0:ℝ)≤_); linarith
  refine ⟨C,?_⟩
  intro d hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
  have hp : 1≤(d:ℝ)^ε := Real.one_le_rpow hd1 hε.le
  by_cases hlarge : d₀≤d
  · obtain ⟨q,hq,hqbound⟩ := hd₀ d hlarge
    exact hq.queryComplexity_le.trans (ENNReal.ofReal_le_ofReal
      (hqbound.trans (by nlinarith)))
  · have hsmall : d≤d₀ := by omega
    have hpow : (10*2^d:ℕ)≤10*2^d₀ := by gcongr <;> norm_num
    have hq : ((10*2^d:ℕ):ℝ)≤C := by dsimp [C]; exact_mod_cast (by omega : 10*2^d≤10*2^d₀+1)
    exact (finite_dimension_sampler d).queryComplexity_le.trans
      (ENNReal.ofReal_le_ofReal (hq.trans (by nlinarith)))

theorem source_exponent_zero : ExponentBound 0 := by
  refine ⟨le_rfl,?_⟩
  intro ε hε
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp (eventually_subpolynomial_sampler hε)
  refine ⟨d₀,?_⟩
  intro d hd
  obtain ⟨q,hq,hqbound⟩ := hd₀ d hd
  simpa only [zero_add] using hq.queryComplexity_le.trans (ENNReal.ofReal_le_ofReal hqbound)

theorem source_gammaStar_zero : gammaStar=0 := by
  apply le_antisymm
  · exact csInf_le ⟨0,fun _ h => h.1⟩ source_exponent_zero
  · exact le_csInf ⟨0,source_exponent_zero⟩ (fun _ h => h.1)

theorem exact_source_main_oai :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      (queryComplexity d).toENNReal ≤ ENNReal.ofReal (C * (d : ℝ) ^ ε)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ENNReal.ofReal (c * Real.log (d : ℝ)) ≤ (queryComplexity d).toENNReal) ∧
    gammaStar = 0 := by
  exact ⟨source_subpolynomial_upper,LowerBound.source_logarithmic_lower,source_gammaStar_zero⟩

end LogConcaveSampling

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.exact_source_main_oai := @OAI.LogConcaveSampling.exact_source_main_oai
