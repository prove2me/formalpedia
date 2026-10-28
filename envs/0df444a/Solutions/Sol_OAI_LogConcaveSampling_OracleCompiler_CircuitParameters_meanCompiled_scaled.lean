-- Prove2me | solution 1 for OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:46:30.13404+00:00
-- url     : https://prove2.me/submissions/cd38b422-3f08-4296-a757-a5dc90fafca1

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_PoincareVectorVariance
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem poincare_vector_variance {d e : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (hm : Appell.HasMoments μ) {f : Point d → Point e} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hK : LipschitzWith K f) :
    Integrable (fun z => ‖f z-∫w,f w ∂μ‖^2) μ ∧
      (∫z,‖f z-∫w,f w ∂μ‖^2 ∂μ)≤(e:ℝ)*β*(K:ℝ)^2 := by
  classical
  let b := EuclideanSpace.basisFun (Fin e) ℝ
  have hi : Integrable f μ := (Appell.HasGrowth.lipschitz hK).integrable hf.continuous.aestronglyMeasurable hm
  have hg : Appell.HasGrowth (fun z => f z-∫w,f w ∂μ) := by
    simpa only [sub_eq_add_neg] using (Appell.HasGrowth.lipschitz hK).add
      (Appell.HasGrowth.const (-(∫w,f w ∂μ)))
  have hisq := (hg.norm.pow 2).integrable ((hf.continuous.sub continuous_const).norm.pow 2).aestronglyMeasurable hm
  have hmj (j : Fin e) : MemLp (fun z => inner ℝ (b j) (f z)) 2 μ :=
    (Appell.HasGrowth.lipschitz ((innerSL ℝ (b j)).lipschitz.comp hK)).memLp
      (by fun_prop) hm
  have hei (j : Fin e) : Integrable (fun z => (inner ℝ (b j) (f z-∫w,f w ∂μ))^2) μ := by
    have h := (hmj j).sub (memLp_const (inner ℝ (b j) (∫w,f w ∂μ)))
    convert h.integrable_sq using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [inner_sub_right,Pi.sub_apply]
  have hv (j : Fin e) : (∫z,(inner ℝ (b j) (f z-∫w,f w ∂μ))^2 ∂μ)≤β*(K:ℝ)^2 := by
    have h := hP.lipschitz_variance hβ ((innerSL ℝ (b j)).contDiff.comp hf)
      ((innerSL ℝ (b j)).lipschitz.comp hK) (hmj j)
    simp only [NNReal.coe_mul,coe_nnnorm,innerSL_apply_norm,b.norm_eq_one,one_mul] at h
    change Var[fun z => inner ℝ (b j) (f z);μ]≤β*(K:ℝ)^2 at h
    rw [variance_eq_integral (hmj j).aemeasurable] at h
    simpa only [inner_sub_right,integral_inner hi] using h
  refine ⟨hisq,?_⟩
  calc
    _ = ∫z,∑j : Fin e,(inner ℝ (b j) (f z-∫w,f w ∂μ))^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [Real.norm_eq_abs,sq_abs] using (b.sum_sq_norm_inner_right (f z-∫w,f w ∂μ)).symm
    _ = ∑j : Fin e,∫z,(inner ℝ (b j) (f z-∫w,f w ∂μ))^2 ∂μ := integral_finsetSum _ (fun j _ => hei j)
    _ ≤ ∑_j : Fin e,β*(K:ℝ)^2 := Finset.sum_le_sum (fun j _ => hv j)
    _ = _ := by simp; ring

theorem poincare_sq_norm_center {d : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (hm : Appell.HasMoments μ) :
    Integrable (fun z => ‖z-∫w,w ∂μ‖^2) μ ∧
      (∫z,‖z-∫w,w ∂μ‖^2 ∂μ)≤(d:ℝ)*β := by
  simpa using poincare_vector_variance hβ hP hm (f:=id) contDiff_id (LipschitzWith.id)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

lemma poincare_integral_norm_center_sharp {d : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (hm : Appell.HasMoments μ) :
    (∫z,‖z-∫w,w ∂μ‖ ∂μ)≤Real.sqrt ((d:ℝ)*β) := by
  have hg : Appell.HasGrowth (fun z : Point d => z-∫w,w ∂μ) := by
    simpa only [sub_eq_add_neg,id_eq] using
      (Appell.HasGrowth.lipschitz (LipschitzWith.id (α:=Point d))).add
        (Appell.HasGrowth.const (-(∫w,w ∂μ)))
  have hlp : MemLp (fun z : Point d => ‖z-∫w,w ∂μ‖) 2 μ :=
    hg.norm.memLp (by fun_prop) hm
  have hh := integral_mul_sq_le hlp (memLp_const (1:ℝ) (μ:=μ))
  simp only [mul_one,one_pow,integral_const,probReal_univ,smul_eq_mul] at hh
  apply (Real.le_sqrt (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)).mpr
  exact hh.trans (poincare_sq_norm_center hβ hP hm).2

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)

include hF hr hl hρ0 hρ1

lemma conditionalFieldMean_center_error_sharp (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r
      (ρ • y-((1-ρ^2)*r) • conditionalFieldMean F x r ρ y)‖ ≤
      ((lam:ℝ)*r)*Real.sqrt ((d:ℝ)*((Real.pi^2/2)*(1-ρ^2))) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hh := norm_integral_sub_map_mean_le (primitiveField_lipschitz hF x hr)
    (conditional_identity_integrable hF x hr hl hρ0 hρ1 y)
  have hb := poincare_integral_norm_center_sharp
    (mul_nonneg (by positivity) (probability_time hρ0 hρ1).1.le)
    (conditionalLaw_hasPoincare hF x hr hl hρ0 hρ1 y)
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  have hg := hh.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg lam.coe_nonneg hr))
  simpa only [conditional_mean_identity hF x hr hl hρ0 hρ1 y,
    NNReal.coe_mul,NNReal.coe_mk,conditionalFieldMean] using hg

lemma conditionalFieldMean_center_zero_bound (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r 0‖ ≤
      2*((lam:ℝ)*r)*(Real.pi*Real.sqrt d+‖y‖+r*‖primitiveField F x r 0‖) := by
  let M := conditionalFieldMean F x r ρ y
  let c := primitiveField F x r 0
  let z := ρ • y-((1-ρ^2)*r) • M
  have he := conditionalFieldMean_center_error_sharp hF x hr hl hρ0 hρ1 y
  have ht := probability_time hρ0 hρ1
  have hs : Real.sqrt ((d:ℝ)*((Real.pi^2/2)*(1-ρ^2)))≤Real.pi*Real.sqrt d := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
    have hb := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤(d:ℝ)*(Real.pi^2/2))
    nlinarith [Real.pi_pos,sq_nonneg Real.pi]
  have hz : ‖z‖≤‖y‖+r*‖M‖ := by
    calc
      _ ≤ ‖ρ • y‖+‖((1-ρ^2)*r) • M‖ := norm_sub_le _ _
      _ = ρ*‖y‖+((1-ρ^2)*r)*‖M‖ := by simp only [norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hρ0,abs_of_nonneg (mul_nonneg ht.1.le hr)]
      _ ≤ _ := add_le_add (mul_le_of_le_one_left (norm_nonneg _) hρ1.le)
        (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hr ht.2) (norm_nonneg _))
  have hc := (primitiveField_lipschitz hF x hr).dist_le_mul z 0
  simp only [dist_eq_norm,sub_zero,NNReal.coe_mul,NNReal.coe_mk] at hc
  have hh : ‖M-c‖≤((lam:ℝ)*r)*(Real.pi*Real.sqrt d)+( (lam:ℝ)*r)*(‖y‖+r*‖M‖) := by
    calc
      _ ≤ ‖M-primitiveField F x r z‖+‖primitiveField F x r z-c‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add (he.trans (mul_le_mul_of_nonneg_left hs (by positivity)))
        (hc.trans (mul_le_mul_of_nonneg_left hz (by positivity)))
  have hm : ‖M‖≤‖M-c‖+‖c‖ := norm_le_norm_sub_add _ _
  have hh' := hh.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm hr)) (by positivity : 0≤(lam:ℝ)*r)))
  have hb := mul_le_mul_of_nonneg_right hl (norm_nonneg (M-c))
  dsimp [M,c] at hh' hb ⊢
  nlinarith
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianAffineNormMoment
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped NNReal

lemma conditionalFieldMean_at_zero {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (y : Point d) :
    conditionalFieldMean F x r 0 y=primitiveExpectedField F x r := by
  have he : conditionalPotential F x r 0 y=primitivePotential F x r := by
    funext z
    simp [conditionalPotential,primitivePotential]
  simp only [conditionalFieldMean,he,primitiveExpectedField]

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hl in
lemma terminal_mean_error (z : Point d) :
    ‖primitiveField F x r z-primitiveExpectedField F x r‖≤
      2*((lam:ℝ)*r)*(Real.pi*Real.sqrt d+‖z‖+r*‖primitiveField F x r 0‖) := by
  have he := conditionalFieldMean_center_zero_bound hF x hr hl (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)<1) (0:Point d)
  rw [conditionalFieldMean_at_zero,norm_zero,add_zero] at he
  have hc := (primitiveField_lipschitz hF x hr).dist_le_mul z 0
  simp only [dist_eq_norm,sub_zero,NNReal.coe_mul,NNReal.coe_mk] at hc
  have hh := (norm_sub_le_norm_sub_add_norm_sub (primitiveField F x r z)
    (primitiveField F x r 0) (primitiveExpectedField F x r)).trans
    (add_le_add hc (by simpa only [norm_sub_rev] using he))
  have hz := mul_nonneg (mul_nonneg lam.coe_nonneg hr) (norm_nonneg z)
  nlinarith

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Program
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

namespace LogConcaveSampling.OracleCompiler

namespace Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {d q : ℕ}

lemma history_tail (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    (n : ℕ) (i : Fin q) (hi : n ≤ i.val) : A.history V ω n i = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
      exact ih (by omega)
    · exact ih (by omega)

lemma history_stable (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    {m n : ℕ} (hmn : m ≤ n) (i : Fin q) (hi : i.val < m) :
    A.history V ω n i = A.history V ω m i := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    simp only [history]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
      exact ih
    · exact ih

lemma prefix_zero (h : Transcript d q) : mask 0 h = 0 := by
  funext i
  simp [mask]

lemma prefix_full (h : Transcript d q) : mask q h = h := by
  funext i
  simp [mask, i.isLt]

lemma prefix_succ (n : ℕ) (hn : n < q) (h : Transcript d q) :
    mask (n+1) h = Function.update (mask n h) ⟨n,hn⟩ (h ⟨n,hn⟩) := by
  funext i
  by_cases hi : i = ⟨n,hn⟩
  · subst i
    simp [mask]
  · rw [Function.update_of_ne hi]
    simp only [mask]
    have hne : i.val ≠ n := by intro he; exact hi (Fin.ext he)
    have he : (i.val < n+1) ↔ (i.val < n) := by omega
    simp only [he]

lemma history_eq_prefix (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    {n : ℕ} (hn : n ≤ q) : A.history V ω n = mask n (A.history V ω q) := by
  funext i
  simp only [mask]
  split_ifs with hi
  · exact (A.history_stable V ω hn i hi).symm
  · exact A.history_tail V ω n i (by omega)

lemma history_spec (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) (i : Fin q) :
    A.history V ω q i =
      firstOrderReply V (A.query i (ω, mask i.val (A.history V ω q))) := by
  rw [A.history_stable V ω (m := i.val+1) (by omega) i (by omega)]
  rw [history, dite_eq_left i.isLt]
  simp only [Function.update_self]
  rw [A.history_eq_prefix V ω (by omega)]

lemma history_unique (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    (h : Transcript d q)
    (hh : ∀ i, h i = firstOrderReply V (A.query i (ω, mask i.val h))) :
    A.history V ω q = h := by
  have hp : ∀ n ≤ q, A.history V ω n = mask n h := by
    intro n hn
    induction n with
    | zero => simp [history, prefix_zero]
    | succ n ih =>
      have hnq : n < q := by omega
      rw [history, dite_eq_left hnq, ih (by omega), prefix_succ n hnq h, hh ⟨n,hnq⟩]
  simpa only [prefix_full] using hp q le_rfl

lemma measurable_history (A : Program Ω d q O) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) (n : ℕ) :
    Measurable (A.history V · n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · apply Measurable.of_eval
      intro i
      by_cases hi : i = ⟨n,hn⟩
      · subst i
        simp only [Function.update_self]
        exact hV.comp ((A.query_measurable _).comp (measurable_id.prodMk ih))
      · simp only [Function.update_of_ne hi]
        exact (measurable_pi_apply i).comp ih
    · exact ih

lemma measurable_run (A : Program Ω d q O) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) : Measurable (A.run V) :=
  A.output_measurable.comp (measurable_id.prodMk (A.measurable_history V hV q))

end Program
end LogConcaveSampling.OracleCompiler

namespace LogConcaveSampling.OracleCompiler.Program
variable {Ω O R : Type*} [MeasurableSpace Ω] [MeasurableSpace O] [MeasurableSpace R]
  {d q r : ℕ}

lemma leftTrace_prefix_left (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    leftTrace (mask n (Fin.append h k)) = mask n h := by
  funext i
  simp [leftTrace, mask]

lemma leftTrace_prefix_right (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    leftTrace (mask (q+n) (Fin.append h k)) = h := by
  funext i
  have hi : i.val < q+n := by omega
  simp [leftTrace, mask, hi]

lemma rightTrace_prefix_right (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    rightTrace (mask (q+n) (Fin.append h k)) = mask n k := by
  funext i
  simp [rightTrace, mask]

lemma seq_history (A : Program Ω d q O) (B : Program (Ω × O) d r R)
    (V : Point d → ℝ) (ω : Ω) :
    (A.seq B).history V ω (q+r) =
      Fin.append (A.history V ω q) (B.history V (ω,A.run V ω) r) := by
  apply history_unique
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, seq, Fin.addCases_left, Fin.val_castAdd,
      leftTrace_prefix_left]
    exact A.history_spec V ω j
  · simp only [Fin.append_right, seq, Fin.addCases_right, Fin.val_natAdd,
      leftTrace_prefix_right, rightTrace_prefix_right]
    exact B.history_spec V (ω,A.run V ω) j

lemma seq_run (A : Program Ω d q O) (B : Program (Ω × O) d r R)
    (V : Point d → ℝ) (ω : Ω) :
    (A.seq B).run V ω = B.run V (ω,A.run V ω) := by
  unfold run
  rw [seq_history]
  simp only [seq, leftTrace_append, rightTrace_append]
  rfl

lemma map_history (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f)
    (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    (A.map f hf).history V ω n = A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    rfl

lemma map_run (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f)
    (V : Point d → ℝ) (ω : Ω) : (A.map f hf).run V ω = f (ω,A.run V ω) := by
  unfold run
  rw [map_history]
  rfl

lemma seedMap_history {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) (V : Point d → ℝ) (ω : Ξ) (n : ℕ) :
    (A.seedMap f hf).history V ω n = A.history V (f ω) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    rfl

lemma seedMap_run {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) (V : Point d → ℝ) (ω : Ξ) :
    (A.seedMap f hf).run V ω = A.run V (f ω) := by
  unfold run
  rw [seedMap_history]
  rfl

end LogConcaveSampling.OracleCompiler.Program

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma slot_energy (c : ℝ) (a : ι → ℝ)
    (hc : c ^ 2 * (∑ i, a i ^ 2) - 2 * c + 1 = 0) (g : ι → E) :
    (∑ i, ‖slotTransform c a g i‖ ^ 2) + ‖slotSum a g‖ ^ 2 =
      ∑ i, ‖g i‖ ^ 2 := by
  let S := slotSum a g
  have hi : ∑ i, a i * inner ℝ (g i) S = ‖S‖ ^ 2 := by
    simp_rw [← real_inner_smul_left]
    rw [← sum_inner]
    exact real_inner_self_eq_norm_sq S
  have hsum : (∑ i, ‖slotTransform c a g i‖ ^ 2) =
      (∑ i, ‖g i‖ ^ 2) - (2 * c) * (∑ i, a i * inner ℝ (g i) S) +
        c ^ 2 * (∑ i, a i ^ 2) * ‖S‖ ^ 2 := by
    simp only [slotTransform, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_smul_right]
    dsimp only [S]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hsum, hi]
  change _ + ‖S‖ ^ 2 = _
  nlinarith [mul_eq_zero_of_left hc (‖S‖ ^ 2)]

lemma dual_restored_left (c : ℝ) (a : ι → ℝ) (L : StrongDual ℝ (ι → E)) (j : ι) :
    ((L.comp (restored c a)).comp (ContinuousLinearMap.inl ℝ (ι → E) E)).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => E) j) =
      L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) j) -
        (c * a j) • ∑ i, a i • L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.single_apply]
  have h : restored c a (Pi.single j x,0) =
      Pi.single j x - (c * a j) • ∑ i, a i • Pi.single i x := by
    ext k
    simp [slotTransform, slotSum, Pi.single_apply, smul_smul, mul_comm, mul_left_comm]
  rw [h, map_sub, map_smul, map_sum]
  simp

lemma dual_restored_right (c : ℝ) (a : ι → ℝ) (L : StrongDual ℝ (ι → E)) :
    (L.comp (restored c a)).comp (ContinuousLinearMap.inr ℝ (ι → E) E) =
      -(∑ i, a i • L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)) := by
  ext x
  have h : restored c a (0,x) = -(∑ i, a i • Pi.single i x) := by
    ext k
    simp [slotTransform, slotSum, Pi.single_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [h, map_neg, map_sum]
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem restored_gaussian (c : ℝ) (a : ι → ℝ)
    (hc : c ^ 2 * (∑ i, a i ^ 2) - 2 * c + 1 = 0) :
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E)).map
      (restored c a) = Measure.pi (fun _ : ι => stdGaussian E) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_pi, charFunDual_pi]
  simp_rw [dual_restored_left, dual_restored_right, charFunDual_stdGaussian,
    ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  let D := InnerProductSpace.toDual ℝ E
  let l := fun i => L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)
  have he := slot_energy c a hc (fun i => D.symm (l i))
  simp only [slotTransform, slotSum, ← map_smul, ← map_sum, ← map_sub,
    LinearIsometryEquiv.norm_map] at he
  simp only [norm_neg]
  norm_cast
  dsimp only [l] at he
  simp only [← Finset.sum_div, Finset.sum_neg_distrib]
  linarith

omit [DecidableEq ι] in
lemma sqrtCoefficient_equation (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (sqrtCoefficient a) ^ 2 * (∑ i, a i ^ 2) - 2 * sqrtCoefficient a + 1 = 0 := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr ha)
  have hpos : 0 < 1 + Real.sqrt (1 - ∑ i, a i ^ 2) := by positivity
  unfold sqrtCoefficient
  field_simp
  nlinarith

theorem sqrt_restored_gaussian (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E)).map
      (restored (sqrtCoefficient a) a) = Measure.pi (fun _ : ι => stdGaussian E) :=
  restored_gaussian _ _ (sqrtCoefficient_equation a ha)

end LogConcaveSampling.SeedCompiler

namespace LogConcaveSampling.SeedCompiler
variable {ι E O : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma absorption_pathwise {r D : ℝ} (v : ι → ℝ)
    (M : E → (ι → E) → O) (hM : ShiftInvariant r v M)
    (x : E) (c : ℝ) (g : ι → E) (z : E) :
    M (x + (r / (2 * D)) • z)
        (slotTransform c (fun i => v i / (2 * D)) g) =
      M x (restored c (fun i => v i / (2 * D)) (g,z)) := by
  have h := hM x ((1 / (2 * D)) • z)
    (restored c (fun i => v i / (2 * D)) (g,z))
  have hx : r • ((1 / (2 * D)) • z) = (r / (2 * D)) • z := by
    rw [smul_smul]; congr 1; ring
  have hs : (fun i => restored c (fun i => v i / (2 * D)) (g,z) i +
      v i • ((1 / (2 * D)) • z)) = slotTransform c (fun i => v i / (2 * D)) g := by
    funext i
    simp only [restored_apply, smul_smul]
    have hc : v i * (1 / (2 * D)) = v i / (2 * D) := by ring
    rw [hc, sub_add_cancel]
  simpa only [hx, hs] using h

omit [DecidableEq ι] in
lemma normalized_shift_bound {D : ℝ} (hD : 0 < D) (v : ι → ℝ)
    (hv : (∑ i, v i ^ 2) ≤ D ^ 2) :
    (∑ i, (v i / (2 * D)) ^ 2) ≤ 1 / 4 := by
  simp only [div_pow, ← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hD))).mpr
  nlinarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace O]

theorem restored_with_anchors {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [SFinite μ] (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (μ.prod ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E))).map
      (Prod.map id (restored (sqrtCoefficient a) a)) =
      μ.prod (Measure.pi (fun _ : ι => stdGaussian E)) := by
  rw [← Measure.map_prod_map μ _ measurable_id (by fun_prop), Measure.map_id,
    sqrt_restored_gaussian a ha]

end LogConcaveSampling.SeedCompiler

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TerminalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.SeedCompiler
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators

variable {Ω A ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem restored_from_joint_law (κ : Measure Ω) [SFinite κ] (μ : Measure A) [SFinite μ]
    (anchor : Ω → A) (noise : Ω → E) (ha : Measurable anchor) (hz : Measurable noise)
    (hlaw : κ.map (fun w => (anchor w,noise w))=μ.prod (stdGaussian E))
    (a : ι → ℝ) (ha2 : (∑i,a i^2)≤1) :
    (κ.prod (Measure.pi fun _ : ι => stdGaussian E)).map
      (fun z => (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1)))=
        μ.prod (Measure.pi fun _ : ι => stdGaussian E) := by
  let γ : Measure (ι → E) := Measure.pi fun _ => stdGaussian E
  have hAZ : MeasurePreserving (fun w => (anchor w,noise w)) κ (μ.prod (stdGaussian E)) :=
    ⟨ha.prodMk hz,hlaw⟩
  have hp := hAZ.prod (MeasurePreserving.id γ)
  have hs := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ:=stdGaussian E) (ν:=γ))
  have ht := hs.comp ((measurePreserving_prodAssoc μ (stdGaussian E) γ).comp hp)
  have hr : MeasurePreserving (Prod.map id (restored (sqrtCoefficient a) a))
      (μ.prod (γ.prod (stdGaussian E))) (μ.prod γ) :=
    ⟨by fun_prop,restored_with_anchors μ a ha2⟩
  exact (hr.comp ht).map_eq

end LogConcaveSampling.SeedCompiler

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Squared
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

lemma lift_fst (ν : Measure Ω) [SFinite ν] (κ : Measure (A × B)) [IsFiniteMeasure κ]
    (T : Ω → A) (hT : Measurable T) : (lift ν κ T hT).fst=ν := by
  exact Measure.fst_compProd _ _

theorem lift_map (ν : Measure Ω) [SFinite ν] (κ : Measure (A × B)) [IsFiniteMeasure κ]
    (T : Ω → A) (hT : Measurable T) (hlaw : ν.map T=κ.fst) :
    (lift ν κ T hT).map (fun z => (T z.1,z.2))=κ := by
  calc
    _ = κ.fst ⊗ₘ κ.condKernel := by
      ext s hs
      have hm : Measurable (fun z : Ω × B => (T z.1,z.2)) := by fun_prop
      rw [Measure.map_apply hm hs]
      rw [lift,Measure.compProd_apply (hs.preimage (by fun_prop)),Measure.compProd_apply hs]
      simp only [Kernel.comap_apply]
      rw [←hlaw]
      rw [lintegral_map (Kernel.measurable_kernel_prodMk_left (κ := κ.condKernel) hs) hT]
      rfl
    _ = κ := Measure.disintegrate κ κ.condKernel

lemma lift_integrable (ν : Measure Ω) [SFinite ν]
    (κ : Measure (A × B)) [IsFiniteMeasure κ] (T : Ω → A) (hT : Measurable T)
    (hlaw : ν.map T=κ.fst) (f : A × B → ℝ) (hf : Integrable f κ) :
    Integrable (fun z => f (T z.1,z.2)) (lift ν κ T hT) ∧
      (∫z,f (T z.1,z.2) ∂lift ν κ T hT)=∫z,f z ∂κ := by
  have hm : Measurable (fun z : Ω × B => (T z.1,z.2)) := by fun_prop
  have he := lift_map ν κ T hT hlaw
  have hi : Integrable f ((lift ν κ T hT).map (fun z => (T z.1,z.2))) := by rw [he]; exact hf
  exact ⟨hi.comp_measurable hm,(integral_map hm.aemeasurable hi.aestronglyMeasurable).symm.trans
    (by rw [he])⟩
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function SeedCompiler
open scoped BigOperators

variable {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

theorem absorb_coupling (κ : Measure Ω) [IsProbabilityMeasure κ]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure E)
    (anchor : Ω → A) (noise center : Ω → E)
    (ha : Measurable anchor) (hz : Measurable noise) (hc : Measurable center)
    (hlaw : κ.map (fun w => (anchor w,noise w))=μ.prod (stdGaussian E))
    (x : A → E) (hx : Measurable x) {r D K S B : ℝ}
    (hD : 0<D) (hK : 0≤K) (v : Fin k → ℝ) (hv : (∑i,v i^2)≤D^2)
    (M : E → (Fin k → E) → E) (hm : Measurable (uncurry M))
    (hshift : ShiftInvariant r v M)
    (hLip : ∀x y g,‖M x g-M y g‖≤K*‖x-y‖)
    (Q : A → E → E) (hQ : Measurable (uncurry Q))
    (hci : Integrable (fun w => ‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2) κ)
    (hce : (∫w,‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2 ∂κ)≤S)
    (π : Measure ((A × (Fin k → E)) × E)) [IsProbabilityMeasure π]
    (hπ : π.fst=μ.prod (Measure.pi fun _ : Fin k => stdGaussian E))
    (hπnoise : π.map (fun z => (z.1.1,z.2))=μ.prod ν)
    (hbi : Integrable (fun z => ‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2) π)
    (hbe : (∫z,‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2 ∂π)≤B) :
    let a := fun i => v i/(2*D)
    let P := slotTransform (sqrtCoefficient a) a
    ∃Λ : Measure ((Ω × (Fin k → E)) × E),IsProbabilityMeasure Λ ∧
      Λ.fst=κ.prod (Measure.pi fun _ : Fin k => stdGaussian E) ∧
      Λ.map (fun z => (anchor z.1.1,z.2))=μ.prod ν ∧
      Integrable (fun z => ‖M (center z.1.1) (P z.1.2)-Q (anchor z.1.1) z.2‖^2) Λ ∧
      (∫z,‖M (center z.1.1) (P z.1.2)-Q (anchor z.1.1) z.2‖^2 ∂Λ)≤2*K^2*S+2*B := by
  dsimp only
  let a := fun i => v i/(2*D)
  let γ : Measure (Fin k → E) := Measure.pi fun _ => stdGaussian E
  let T : Ω × (Fin k → E) → A × (Fin k → E) := fun z =>
    (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1))
  have hT : Measurable T := by
    exact (ha.comp measurable_fst).prodMk ((restored (sqrtCoefficient a) a).measurable.comp
      (measurable_snd.prodMk (hz.comp measurable_fst)))
  have hTlaw : (κ.prod γ).map T=π.fst := by
    rw [hπ]
    exact restored_from_joint_law κ μ anchor noise ha hz hlaw a
      ((normalized_shift_bound hD v hv).trans (by norm_num))
  let Λ := lift (κ.prod γ) π T hT
  have hΛ : Λ.fst=κ.prod γ := lift_fst _ _ _ _
  have hΛmap := lift_map (κ.prod γ) π T hT hTlaw
  have hC₀ := hci.comp_fst γ
  have hC : Integrable (fun z : (Ω × (Fin k → E)) × E =>
      ‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2) Λ := by
    have h : Integrable (fun z : Ω × (Fin k → E) =>
      ‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2) Λ.fst := by
      rw [hΛ]; exact hC₀
    exact h.comp_measurable measurable_fst
  have hCeq : (∫z : (Ω × (Fin k → E)) × E,
      ‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2 ∂Λ)=
      ∫w,‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2 ∂κ := by
    have hmf : Measurable (fun z : Ω × (Fin k → E) =>
      ‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2) := by
      exact ((hc.sub ((hx.comp ha).add (hz.const_smul _))).norm.pow_const 2).comp measurable_fst
    rw [←integral_map measurable_fst.aemeasurable hmf.aestronglyMeasurable]
    change (∫z : Ω × (Fin k → E),‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2 ∂Λ.fst)=_
    rw [hΛ,integral_prod _ hC₀]
    simp only [integral_const,probReal_univ,one_smul]
  have hJ := lift_integrable (κ.prod γ) π T hT hTlaw
    (fun z => ‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2) hbi
  have hmP : Measurable (slotTransform (sqrtCoefficient a) a : (Fin k → E) → _) := by
    unfold slotTransform slotSum; fun_prop
  have hmeas : Measurable (fun z : (Ω × (Fin k → E)) × E =>
      ‖M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2)-Q (anchor z.1.1) z.2‖^2) := by
    exact ((hm.comp ((hc.comp (measurable_fst.comp measurable_fst)).prodMk
      (hmP.comp (measurable_snd.comp measurable_fst)))).sub
      (hQ.comp ((ha.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))).norm.pow_const 2
  have hbound (z : (Ω × (Fin k → E)) × E) :
      ‖M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2)-Q (anchor z.1.1) z.2‖^2≤
        2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
        2*‖M (x (T z.1).1) (T z.1).2-Q (T z.1).1 z.2‖^2 := by
    have he₀ := hLip (center z.1.1) (x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)
      (slotTransform (sqrtCoefficient a) a z.1.2)
    have heq := absorption_pathwise (D:=D) v M hshift (x (anchor z.1.1)) (sqrtCoefficient a) z.1.2 (noise z.1.1)
    rw [heq] at he₀
    have he := he₀
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2))
      (M (x (T z.1).1) (T z.1).2) (Q (anchor z.1.1) z.2)
    have hp := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (mul_nonneg hK (norm_nonneg _)) (norm_nonneg _))).2
      (ht.trans (add_le_add he (le_refl _)))
    change _≤2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
      2*‖M (x (T z.1).1) (T z.1).2-Q (anchor z.1.1) z.2‖^2
    nlinarith [sq_nonneg (K*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖-
      ‖M (x (T z.1).1) (T z.1).2-Q (anchor z.1.1) z.2‖)]
  have hdom := (hC.const_mul (2*K^2)).add (hJ.1.const_mul 2)
  have hi := hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs,abs_sq,Pi.add_apply] using hbound z))
  refine ⟨Λ,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),hΛ,?_,hi,(integral_mono hi hdom hbound).trans ?_⟩
  · rw [←hπnoise,←hΛmap,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · change (∫z : (Ω × (Fin k → E)) × E,
        2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
        2*‖M (x (T z.1).1) (T z.1).2-Q (T z.1).1 z.2‖^2 ∂Λ)≤_
    rw [integral_add (hC.const_mul _) (hJ.1.const_mul _),integral_const_mul,integral_const_mul,hCeq,hJ.2]
    exact add_le_add (mul_le_mul_of_nonneg_left hce (by positivity))
      (mul_le_mul_of_nonneg_left hbe (by norm_num))
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators NNReal

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W]
  {d : ℕ}

theorem SquaredAt.of_joint (Λ : Measure W) [IsProbabilityMeasure Λ]
    (μ : Measure Ω) (ν : Measure Γ) (T : W → Ω) (U : W → Γ)
    (hT : Measurable T) (hU : Measurable U) (hl : Λ.map T=μ) (hr : Λ.map U=ν)
    (f : Ω → Point d) (g : Γ → Point d) (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hi : Integrable (fun w => ‖f (T w)-g (U w)‖^2) Λ)
    (he : (∫w,‖f (T w)-g (U w)‖^2 ∂Λ)≤B) : SquaredAt μ ν f g B := by
  let J : W → Ω × Γ := fun w => (T w,U w)
  have hJ : Measurable J := hT.prodMk hU
  have hm : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) := by fun_prop
  refine ⟨Λ.map J,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),?_,?_,?_,?_⟩
  · change (Λ.map J).map Prod.fst=μ
    rw [Measure.map_map measurable_fst hJ]
    exact hl
  · change (Λ.map J).map Prod.snd=ν
    rw [Measure.map_map measurable_snd hJ]
    exact hr
  · exact (integrable_map_measure hm.aestronglyMeasurable hJ.aemeasurable).mpr hi
  · rw [integral_map hJ.aemeasurable hm.aestronglyMeasurable]
    exact he

lemma SquaredAt.mono {μ : Measure Ω} {ν : Measure Γ} {f : Ω → Point d} {g : Γ → Point d}
    {B C : ℝ} (h : SquaredAt μ ν f g B) (hBC : B≤C) : SquaredAt μ ν f g C := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  exact ⟨κ,hκ,hl,hr,hi,he.trans hBC⟩

lemma SquaredAt.reindex {Ω' Γ' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Γ']
    {μ : Measure Ω} {ν : Measure Γ} {f : Ω → Point d} {g : Γ → Point d}
    {B : ℝ} (h : SquaredAt μ ν f g B) (T : Ω → Ω') (U : Γ → Γ')
    (hT : Measurable T) (hU : Measurable U)
    (f' : Ω' → Point d) (g' : Γ' → Point d) (hf' : Measurable f') (hg' : Measurable g')
    (hfe : ∀z,f' (T z)=f z) (hge : ∀z,g' (U z)=g z) :
    SquaredAt (μ.map T) (ν.map U) f' g' B := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  have := hκ
  refine SquaredAt.of_joint κ (μ.map T) (ν.map U) (T ∘ Prod.fst) (U ∘ Prod.snd)
    (hT.comp measurable_fst) (hU.comp measurable_snd) ?_ ?_ f' g' hf' hg' ?_ ?_
  · rw [←Measure.map_map hT measurable_fst]; exact congrArg (Measure.map T) hl
  · rw [←Measure.map_map hU measurable_snd]; exact congrArg (Measure.map U) hr
  · simpa only [Function.comp_apply,hfe,hge] using hi
  · simpa only [Function.comp_apply,hfe,hge] using he

end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set
open scoped BigOperators

variable {I β E : Type*} [Fintype I] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β}

omit [CompleteSpace E] in
lemma norm_weighted_sum_sq (w : I → ℝ) (v : I → E) :
    ‖∑i,w i • v i‖^2≤(∑i,|w i|)*(∑i,|w i| *‖v i‖^2) := by
  have h := norm_sum_le Finset.univ (fun i => w i • v i)
  simp only [norm_smul,Real.norm_eq_abs] at h
  apply (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r:=fun i => |w i| * ‖v i‖) (f:=fun i => |w i|) (g:=fun i => |w i| *‖v i‖^2)
  · exact fun i _ => abs_nonneg _
  · exact fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  · intro index _; exact le_of_eq (by ring)

end LogConcaveSampling.RMSIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChainTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}

lemma weighted_sum_sq_varying (w : I → ℝ) (f : I → Ω → E) (B : I → ℝ)
    (hm : ∀i,AEStronglyMeasurable (f i) μ)
    (hi : ∀i,Integrable (fun y => ‖f i y‖^2) μ)
    (hB : ∀i,(∫y,‖f i y‖^2 ∂μ)≤B i) :
    Integrable (fun y => ‖∑i,w i • f i y‖^2) μ ∧
      (∫y,‖∑i,w i • f i y‖^2 ∂μ)≤(∑i,|w i|)*(∑i,|w i| *B i) := by
  have hw0 : 0≤∑i,|w i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : Integrable (fun y => (∑i,|w i|)*(∑i,|w i| *‖f i y‖^2)) μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hmeas : AEStronglyMeasurable (fun y => ‖∑i,w i • f i y‖^2) μ := by
    have h := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => (hm i).const_smul (w i))).norm.pow 2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
  have ho : Integrable (fun y => ‖∑i,w i • f i y‖^2) μ :=
    hs.mono' hmeas (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_weighted_sum_sq w (fun i => f i y)))
  refine ⟨ho,(integral_mono ho hs (fun y => norm_weighted_sum_sq w (fun i => f i y))).trans ?_⟩
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _))) hw0
  · exact fun i _ => (hi i).const_mul _
end LogConcaveSampling.RMSIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_AbsorbFixed
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function SeedCompiler
open scoped Classical BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}

theorem SquaredAt.absorb_fixed (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Point d) (hf : Measurable f) (c b : Point d) {r D K S B τ : ℝ}
    (hD : 0<D) (hK : 0≤K) (v : Fin k → ℝ) (hv : (∑i,v i^2)≤D^2)
    (M : Point d → (Fin k → Point d) → Point d) (hm : Measurable (uncurry M))
    (hshift : ShiftInvariant r v M)
    (hLip : ∀x y g,‖M x g-M y g‖≤K*‖x-y‖)
    (hC : SquaredAt μ (stdGaussian (Point d)) f (fun g => c+(r/(2*D)) • g) S)
    (hM : SquaredAt (Measure.pi fun _ : Fin k => stdGaussian (Point d)) (stdGaussian (Point d))
      (M c) (fun g => b+τ • g) B) :
    SquaredAt (μ.prod (Measure.pi fun _ : Fin k => stdGaussian (Point d))) (stdGaussian (Point d))
      (fun z => M (f z.1) (slotTransform (sqrtCoefficient (fun i => v i/(2*D)))
        (fun i => v i/(2*D)) z.2)) (fun g => b+τ • g) (2*K^2*S+2*B) := by
  let γ := stdGaussian (Point d)
  let θ := Measure.pi fun _ : Fin k => γ
  obtain ⟨κ,hκ,hcl,hcr,hci,hce⟩ := hC
  let := hκ
  have hMR := hM.reindex (fun g => ((),g)) id (by fun_prop) measurable_id
    (fun z : Unit × (Fin k → Point d) => M c z.2) (fun g => b+τ • g)
    (hm.comp (measurable_const.prodMk measurable_snd)) (by fun_prop) (by intro; rfl) (by intro; rfl)
  rw [←Measure.dirac_prod (),Measure.map_id] at hMR
  obtain ⟨π,hπ,hpl,hpr,hpi,hpe⟩ := hMR
  let := hπ
  have hlaw : κ.map (fun z : Ω × Point d => ((),z.2))=(Measure.dirac ()).prod γ := by
    dsimp only [γ]
    rw [Measure.dirac_prod,←hcr]
    change _=(κ.map Prod.snd).map (Prod.mk ())
    rw [Measure.map_map (by fun_prop) measurable_snd]
    rfl
  have hnoise : π.map (fun z : (Unit × (Fin k → Point d)) × Point d => (z.1.1,z.2))=
      (Measure.dirac ()).prod γ := by
    dsimp only [γ]
    rw [Measure.dirac_prod,←hpr]
    change _=(π.map Prod.snd).map (Prod.mk ())
    rw [Measure.map_map (by fun_prop) measurable_snd]
    rfl
  obtain ⟨Λ,hΛ,hLl,hLr,hLi,hLe⟩ := absorb_coupling κ (Measure.dirac ()) γ
    (fun _ => ()) Prod.snd (fun z => f z.1) measurable_const measurable_snd
    (hf.comp measurable_fst) hlaw (fun _ => c) measurable_const hD hK v hv M hm hshift hLip
    (fun _ g => b+τ • g) (by fun_prop) hci hce π hpl hnoise hpi hpe
  let := hΛ
  let T : ((Ω × Point d) × (Fin k → Point d)) × Point d → Ω × (Fin k → Point d) :=
    fun z => (z.1.1.1,z.1.2)
  have hT : Measurable T := by unfold T; fun_prop
  have hTl : Λ.map T=μ.prod θ := by
    change Λ.map ((Prod.map Prod.fst id) ∘ Prod.fst)=_
    rw [←Measure.map_map (by fun_prop) measurable_fst]
    change Λ.fst.map (Prod.map Prod.fst id)=_
    rw [hLl,←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
    change κ.fst.prod θ=μ.prod θ
    rw [hcl]
  have hLright : Λ.map Prod.snd=γ := by
    have H := congrArg (Measure.map Prod.snd) hLr
    rw [Measure.map_map measurable_snd (by fun_prop),Measure.map_snd_prod] at H
    simpa only [Function.comp_def,measure_univ,one_smul] using H
  exact SquaredAt.of_joint Λ (μ.prod θ) γ T Prod.snd hT measurable_snd hTl hLright
    _ _ (hm.comp ((hf.comp measurable_fst).prodMk (by
      dsimp only [slotTransform,slotSum]; fun_prop))) (by fun_prop) hLi hLe
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

variable {ι : Type*} [Fintype ι] {Ω Γ : ι → Type*}
  [∀i,MeasurableSpace (Ω i)] [∀i,MeasurableSpace (Γ i)] {d : ℕ}

theorem SquaredAt.weighted_pi (μ : ∀i,Measure (Ω i)) (ν : ∀i,Measure (Γ i))
    [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (f : ∀i,Ω i → Point d) (g : ∀i,Γ i → Point d)
    (hf : ∀i,Measurable (f i)) (hg : ∀i,Measurable (g i))
    (w B : ι → ℝ) (h : ∀i,SquaredAt (μ i) (ν i) (f i) (g i) (B i)) :
    SquaredAt (Measure.pi μ) (Measure.pi ν)
      (fun z => ∑i,w i • f i (z i)) (fun z => ∑i,w i • g i (z i))
      ((∑i,|w i|)*(∑i,|w i| * B i)) := by
  choose κ hκ hl hr hi he using h
  let : ∀i,IsProbabilityMeasure (κ i) := hκ
  let Λ := Measure.pi κ
  let T : (∀i,Ω i × Γ i) → (∀i,Ω i) := fun z i => (z i).1
  let U : (∀i,Ω i × Γ i) → (∀i,Γ i) := fun z i => (z i).2
  have hT : Measurable T := by unfold T; fun_prop
  have hU : Measurable U := by unfold U; fun_prop
  have hTl : Λ.map T=Measure.pi μ :=
    (measurePreserving_pi κ μ (fun i => ⟨measurable_fst,hl i⟩)).map_eq
  have hUl : Λ.map U=Measure.pi ν :=
    (measurePreserving_pi κ ν (fun i => ⟨measurable_snd,hr i⟩)).map_eq
  have hm (i : ι) : Measurable (fun z : Ω i × Γ i => f i z.1-g i z.2) := by fun_prop
  have hip (i : ι) : Integrable (fun z : ∀i,Ω i × Γ i => ‖f i (z i).1-g i (z i).2‖^2) Λ :=
    (measurePreserving_eval κ i).integrable_comp_of_integrable (hi i)
  have hep (i : ι) : (∫z : ∀i,Ω i × Γ i,‖f i (z i).1-g i (z i).2‖^2 ∂Λ)≤B i := by
    exact ((measurePreserving_eval κ i).hasLaw.integral_comp
      ((hm i).norm.pow_const 2).aestronglyMeasurable).trans_le (he i)
  have hs := RMSIntegral.weighted_sum_sq_varying w
    (fun i (z : ∀i,Ω i × Γ i) => f i (z i).1-g i (z i).2) B
    (fun i => ((hm i).comp (measurable_pi_apply i)).aestronglyMeasurable) hip hep
  have hid (z : ∀i,Ω i × Γ i) :
      (∑i,w i • f i (T z i))-(∑i,w i • g i (U z i))=
        ∑i,w i • (f i (z i).1-g i (z i).2) := by
    simp only [T,U,smul_sub,Finset.sum_sub_distrib]
  refine SquaredAt.of_joint Λ (Measure.pi μ) (Measure.pi ν) T U hT hU hTl hUl
    _ _ (by fun_prop) (by fun_prop) ?_ ?_
  · simpa only [hid] using hs.1
  · simpa only [hid] using hs.2
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W] {d : ℕ}

theorem SquaredAt.common_noise {μ : Measure Ω} {ν : Measure Γ}
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (h : SquaredAt μ ν f g B) (ρ : Measure W) [IsProbabilityMeasure ρ]
    (hnoise : W → Point d) (hm : Measurable hnoise) :
    SquaredAt (μ.prod ρ) (ν.prod ρ) (fun z => f z.1+hnoise z.2)
      (fun z => g z.1+hnoise z.2) B := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  let := hκ
  let T : (Ω × Γ) × W → Ω × W := Prod.map Prod.fst id
  let U : (Ω × Γ) × W → Γ × W := Prod.map Prod.snd id
  have hT : Measurable T := by fun_prop
  have hU : Measurable U := by fun_prop
  have hTl : (κ.prod ρ).map T=μ.prod ρ := by
    rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
    change κ.fst.prod ρ=μ.prod ρ
    rw [hl]
  have hUl : (κ.prod ρ).map U=ν.prod ρ := by
    rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id]
    change κ.snd.prod ρ=ν.prod ρ
    rw [hr]
  have hcost (z : (Ω × Γ) × W) :
      ‖(f (T z).1+hnoise (T z).2)-(g (U z).1+hnoise (U z).2)‖^2=‖f z.1.1-g z.1.2‖^2 := by
    dsimp only [T,U,Prod.map]; rw [add_sub_add_right_eq_sub]
  refine SquaredAt.of_joint (κ.prod ρ) (μ.prod ρ) (ν.prod ρ) T U hT hU hTl hUl
    _ _ (by fun_prop) (by fun_prop) ?_ ?_
  · simpa only [hcost] using hi.comp_fst ρ
  · simp_rw [hcost]
    rw [integral_prod _ (hi.comp_fst ρ)]
    simpa only [integral_const,probReal_univ,one_smul] using he
end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ReanchorWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators

variable {I E Ω : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma reanchorWeight_budget (w : I → I → ℝ) {A : ℝ}
    (hw : ∀i,∑j,|w i j|≤A) (s i : I) : ∑j,|reanchorWeight w s i j|≤2*A := by
  calc
    _ ≤ ∑j,(|w i j|+|w s j|) := Finset.sum_le_sum (fun j _ => abs_sub _ _)
    _ = (∑j,|w i j|)+(∑j,|w s j|) := Finset.sum_add_distrib
    _ ≤ 2*A := by linarith [hw i,hw s]

end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Picard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma weight_nonneg (E : MeanTree X d) : 0≤weight E := by
  cases E
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
lemma centersBound_sumFin (A : ℝ) (k : ℕ) (E : Fin k → MeanTree X d)
    (hE : ∀i,centersBound A (E i)) : centersBound A (sumFin k E) := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => exact (centersBound_add _ _ _).2 ⟨hE 0,ih _ (fun i => hE i.succ)⟩
lemma centersBound_sumFamily {I : Type*} [Fintype I] (A : ℝ) (E : I → MeanTree X d)
    (hE : ∀i,centersBound A (E i)) : centersBound A (sumFamily E) := by
  exact centersBound_sumFin A _ _ (fun i => hE _)
lemma centersBound_conditional {A r t : ℝ} {x y : MeanTree X d}
    (hx : centersBound A x) (hy : centersBound A y)
    (hw : weight x+|r*t| * weight y≤A) : centersBound A (conditional r t x y) := by
  simp only [conditional,centersBound_mean,weight_add,weight_scale,centersBound_add,centersBound_scale]
  exact ⟨hw,hx,hy⟩

lemma weight_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    {B C : ℝ} (hC : 0≤C) (hw : ∀i,∑j,|w i j|≤B)
    (hφ : ∀i E,weight (φ i E)≤C) (N : ℕ) (i : I) :
    weight (picard w φ a N i)≤weight (a i)+B*C := by
  have hB : 0≤B := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans (hw i)
  cases N with
  | zero => simpa only [picard] using (le_add_of_nonneg_right (a:=weight (a i)) (mul_nonneg hB hC))
  | succ N =>
    simp only [picard,weight_add,weight_sumFamily,weight_scale]
    apply add_le_add_right
    calc
      _≤∑j,|w i j| * C := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hφ j _) (abs_nonneg _))
      _=(∑j,|w i j|)*C := (Finset.sum_mul _ _ _).symm
      _≤B*C := mul_le_mul_of_nonneg_right (hw i) hC

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CircuitD
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

lemma circuitD_nonneg {d : ℕ} (F : Point d → ℝ) (x : Point d) : 0 ≤ circuitD F x := by
  unfold circuitD; positivity
lemma field_zero_eq_gradient {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) :
    primitiveField F x r 0=gradient F x := by simp [primitiveField]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped Classical BigOperators NNReal

variable {d : ℕ}

lemma circuitD_change {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x y : Point d) : circuitD F y ≤ circuitD F x+(lam:ℝ)*‖y-x‖ := by
  have he := hF.gradient_lipschitz.dist_le_mul y x
  rw [dist_eq_norm,dist_eq_norm] at he
  have hn := norm_le_norm_add_norm_sub (gradient F x) (gradient F y)
  rw [norm_sub_rev] at hn
  dsimp [circuitD]
  linarith

lemma primitiveExpectedField_growth {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) :
    ‖primitiveExpectedField F x r‖≤(2*Real.pi+2)*circuitD F x := by
  have he := terminal_mean_error hF x hr hl (0:Point d)
  rw [norm_zero,add_zero,field_zero_eq_gradient] at he
  have hn := norm_le_norm_add_norm_sub (gradient F x) (primitiveExpectedField F x r)
  have h₁ := mul_le_mul_of_nonneg_right hL (show 0≤2*Real.pi*Real.sqrt d by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hl (show 0≤2*‖gradient F x‖ by positivity)
  have h₃ := mul_nonneg (show 0≤2*Real.pi by positivity) (norm_nonneg (gradient F x))
  dsimp [circuitD]
  nlinarith [Real.sqrt_nonneg (d:ℝ)]

namespace MeanTree
variable {X : Type*} [MeasurableSpace X]

theorem eval_circuitD_bound {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (z : X) {A B : ℝ} (hB : 0≤B)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1)
    (E : MeanTree X d) (hw : weight E≤A) (hweights : centersBound A E)
    (hb : circuitD F x+(lam:ℝ)*‖base E z-x‖≤B)
    (hc : centers (fun r b => 0 ≤ r ∧ (lam:ℝ)*r^2≤1/2 ∧ (lam:ℝ)*r≤1 ∧
      circuitD F x+(lam:ℝ)*‖b z-x‖≤B) E) :
    circuitD F (E.eval F z)≤((depth E:ℝ)+1)*B := by
  induction E with | node k b hm a r C ih =>
    have hchild (i : Fin k) := ih i (hweights i).1 (hweights i).2 (hc i).1.2.2.2 (hc i).2
    have hd (i : Fin k) : (depth (C i):ℝ)+1≤(depth (node k b hm a r C):ℝ) := by
      exact_mod_cast (Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i))
    have hmean (i : Fin k) : ‖primitiveExpectedField F ((C i).eval F z) (r i)‖≤
        (2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B := by
      apply (primitiveExpectedField_growth hF _ (hc i).1.1 (hc i).1.2.1 (hc i).1.2.2.1).trans
      exact (mul_le_mul_of_nonneg_left
        ((hchild i).trans (mul_le_mul_of_nonneg_right (hd i) hB)) (by positivity)).trans_eq (by ring)
    have hs : ‖∑i,a i • primitiveExpectedField F ((C i).eval F z) (r i)‖≤
        (∑i,|a i|)*((2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B) := by
      apply (norm_sum_le _ _).trans
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hmean i) (abs_nonneg _))
    have hn : ‖(node k b hm a r C).eval F z-x‖≤‖b z-x‖+
        (∑i,|a i|)*((2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B) := by
      change ‖b z+(∑i,a i • primitiveExpectedField F ((C i).eval F z) (r i))-x‖≤_
      rw [add_sub_right_comm]
      exact (norm_add_le _ _).trans (add_le_add le_rfl hs)
    have hD := (circuitD_change hF x ((node k b hm a r C).eval F z)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hn lam.coe_nonneg))
    change (∑i,|a i|)≤A at hw
    have hmcoef := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw lam.coe_nonneg)
      (show 0≤2*Real.pi+2 by positivity)
    have hcoef : (lam:ℝ)*(∑i,|a i|)*(2*Real.pi+2)≤1 := hmcoef.trans hsmall
    have hh := mul_le_mul_of_nonneg_right hcoef
      (show 0≤(depth (node k b hm a r C):ℝ)*B by positivity)
    change circuitD F x+(lam:ℝ)*‖b z-x‖≤B at hb
    nlinarith
end MeanTree
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Expression
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory

namespace LogConcaveSampling.OracleCompiler

namespace Expression
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compile_run (C : Expression X d) (V : Point d → ℝ)
    (x : X) (g : Fin C.slots → Point d) : C.compile.run V (x,g)=C.eval V x g := by
  induction C with
  | noise b hb n => rfl
  | add a C k q M P hP T hC hT =>
    simp only [compile,Program.seq_run,Program.seedMap_run,Program.map_run,eval]
    rw [hC,hT]

theorem measurable_eval (C : Expression X d) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) :
    Measurable (fun z : X × (Fin C.slots → Point d) => C.eval V z.1 z.2) := by
  have hr := C.compile.measurable_run V hV
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact (compile_run C V z.1 z.2).symm

end Expression
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory

variable {Ω O R Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
  [MeasurableSpace R] [MeasurableSpace Ξ] {d q r : ℕ}

namespace Equivariant
variable {A : Program Ω d q O} {f : Ω → Ω} {τ : O → O}

theorem history (hA : A.Equivariant f τ) (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    A.history V (f ω) n=A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Program.history,ih]
    split_ifs with hn
    · rw [hA.query]
    · rfl

theorem run (hA : A.Equivariant f τ) (V : Point d → ℝ) (ω : Ω) :
    A.run V (f ω)=τ (A.run V ω) := by
  unfold Program.run
  rw [hA.history,hA.output]

end Equivariant

end LogConcaveSampling.OracleCompiler.Program

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Expression
open MeasureTheory

variable {E : Type*} [MeasurableSpace E]

lemma split_slots_preserving (μ : Measure E) [SigmaFinite μ] (c k : ℕ) :
    MeasurePreserving
      (fun g : Fin (c+k) → E =>
        ((fun i : Fin c => g (Fin.castAdd k i)),fun i : Fin k => g (Fin.natAdd c i)))
      (Measure.pi fun _ => μ) ((Measure.pi fun _ : Fin c => μ).prod (Measure.pi fun _ : Fin k => μ)) := by
  have H := (measurePreserving_sumPiEquivProdPi (fun _ : Fin c ⊕ Fin k => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (c+k) => μ) finSumFinEquiv).symm
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end LogConcaveSampling.OracleCompiler.Expression

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChildNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

lemma coefficient_energy {k : ℕ} (a : Fin k → ℝ) :
    (∑i,a i^2)≤(∑i,|a i|)^2 := by
  simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
    (s:=Finset.univ) (fun i _ => abs_nonneg (a i))

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem weighted_gaussian_law (a : ι → ℝ) (n : ℝ) (ha : (∑i,a i^2)=n^2) :
    (Measure.pi fun _ : ι => stdGaussian E).map (fun g => ∑i,a i • g i)=
      (stdGaussian E).map (fun z => n • z) := by
  let S : (ι → E) →L[ℝ] E := ∑i,a i • ContinuousLinearMap.proj i
  let T : E →L[ℝ] E := n • ContinuousLinearMap.id ℝ E
  have hS (g : ι → E) : S g=∑i,a i • g i := by simp [S]
  have hT0 (z : E) : T z=n • z := by simp [T]
  simp_rw [←hS,←hT0]
  change (Measure.pi fun _ : ι => stdGaussian E).map S=(stdGaussian E).map T
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map,charFunDual_map,charFunDual_pi]
  have hL (i : ι) : (L.comp S).comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)=a i • L := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, hS, map_sum, map_smul, ContinuousLinearMap.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · simp
  have hT : L.comp T=n • L := by ext z; simp [T]
  simp_rw [hL,hT,charFunDual_stdGaussian]
  rw [←Complex.exp_sum]
  simp only [norm_smul,Real.norm_eq_abs]
  congr 1
  norm_cast
  simp only [mul_pow,sq_abs,←Finset.sum_div,Finset.sum_neg_distrib,←Finset.sum_mul,ha]

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma declaredNoise_energy {k : ℕ} {A : ℝ} (hA : 0<A) (n : ℝ) (a : Fin k → ℝ)
    (ha : (∑i,|a i|)≤A) : (declaredNoise n A)^2*(∑i,a i^2)≤n^2/4 := by
  have hw : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have he := (coefficient_energy a).trans (pow_le_pow_left₀ hw ha 2)
  change (n/(2*A))^2*(∑i,a i^2)≤n^2/4
  rw [div_pow,div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<(2*A)^2)]
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg n)
  nlinarith

lemma declaredReserve_variance {k : ℕ} {A : ℝ} (hA : 0<A) (n : ℝ) (a : Fin k → ℝ)
    (ha : (∑i,|a i|)≤A) :
    (declaredReserve n A a)^2+(declaredNoise n A)^2*(∑i,a i^2)=n^2 := by
  have he := declaredNoise_energy hA n a ha
  rw [declaredReserve,Real.sq_sqrt (by nlinarith [sq_nonneg n])]
  ring

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma appendSlots_preserving {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (c k : ℕ) :
    MeasurePreserving (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2)
      ((Measure.pi fun _ : Fin c => μ).prod (Measure.pi fun _ : Fin k => μ))
      (Measure.pi fun _ : Fin (c+k) => μ) := by
  have hm : Measurable (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2) := by
    apply Measurable.of_eval
    intro i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.append_left,Fin.append_right] <;> fun_prop
  refine ⟨hm,?_⟩
  rw [←(Expression.split_slots_preserving μ c k).map_eq,Measure.map_map hm
    (Expression.split_slots_preserving μ c k).measurable]
  have he : (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2) ∘
      (fun g : Fin (c+k) → E => ((fun i => g (Fin.castAdd k i)),fun i => g (Fin.natAdd c i)))=id := by
    funext g; exact Fin.append_castAdd_natAdd
  rw [he,Measure.map_id]

lemma finPi_head_preserving {k : ℕ} {E : Fin (k+1) → Type*} [∀i,MeasurableSpace (E i)]
    (μ : ∀i,Measure (E i)) [∀i,SigmaFinite (μ i)] :
    MeasurePreserving (fun z : ∀i,E i => (z 0,fun i : Fin k => z i.succ))
      (Measure.pi μ) ((μ 0).prod (Measure.pi fun i : Fin k => μ i.succ)) := by
  exact measurePreserving_piFinSuccAbove (m:=fun i => inferInstance) μ 0

lemma concatTerms_preserving (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d) :
    MeasurePreserving (concatTerms D k a C M E)
      ((rowLaw C M).prod (Measure.pi fun _ : Fin E.slots => stdGaussian (Point d)))
      (Measure.pi fun _ : Fin (compileTerms D k a C M E).slots => stdGaussian (Point d)) := by
  induction k with
  | zero =>
    change MeasurePreserving Prod.snd ((rowLaw C M).prod
      (Measure.pi fun _ : Fin E.slots => stdGaussian (Point d))) _
    exact measurePreserving_snd
  | succ k ih =>
    let γ := stdGaussian (Point d)
    let μc := Measure.pi fun _ : Fin (C 0).slots => γ
    let μm := Measure.pi fun _ : Fin (M 0).slots => γ
    let μr := rowLaw (fun i : Fin k => C i.succ) (fun i : Fin k => M i.succ)
    let μe := Measure.pi fun _ : Fin E.slots => γ
    have h₁ := (finPi_head_preserving (fun i =>
      (Measure.pi fun _ : Fin (C i).slots => γ).prod
      (Measure.pi fun _ : Fin (M i).slots => γ))).prod (MeasurePreserving.id μe)
    have h₂ := (measurePreserving_prodAssoc (μc.prod μm) μr μe).comp h₁
    have h₃ := ((MeasurePreserving.id (μc.prod μm)).prod
      (ih (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ))).comp h₂
    have h₄ := (measurePreserving_prodAssoc μc μm
      (Measure.pi fun _ : Fin (compileTerms D k (fun i => a i.succ)
        (fun i => C i.succ) (fun i => M i.succ) E).slots => γ)).comp h₃
    have h₅ := ((MeasurePreserving.id μc).prod (appendSlots_preserving γ _ _)).comp h₄
    exact (appendSlots_preserving γ _ _).comp h₅

lemma leftBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.leftBlock (Fin.append x (Fin.append y z))=x := by
  funext i; exact Fin.append_left _ _ i
lemma middleBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.middleBlock (Fin.append x (Fin.append y z))=y := by
  funext i
  change Fin.append x (Fin.append y z) (Fin.natAdd c (Fin.castAdd t i))=y i
  rw [Fin.append_right,Fin.append_left]
lemma rightBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.rightBlock (Fin.append x (Fin.append y z))=z := by
  funext i
  change Fin.append x (Fin.append y z) (Fin.natAdd c (Fin.natAdd k i))=z i
  rw [Fin.append_right,Fin.append_right]

lemma eval_concatTerms (V : Point d → ℝ) (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (x : X) (z : RowTape C M × (Fin E.slots → Point d)) :
    (compileTerms D k a C M E).eval V x (concatTerms D k a C M E z)=
      (∑i,a i • (M i).program.run V ((C i).eval V x (z.1 i).1,(M i).damping D (z.1 i).2))+
        E.eval V x z.2 := by
  induction k with
  | zero => simp [compileTerms,concatTerms]
  | succ k ih =>
    simp only [compileTerms,concatTerms,Expression.eval,leftBlock_append,middleBlock_append,
      rightBlock_append,ih,Fin.sum_univ_succ,add_assoc]
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowGaussian
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {d k : ℕ}

lemma measurable_rowGaussian (a : Fin k → ℝ) (τ ρ n : ℝ) :
    Measurable (rowGaussian (d:=d) a τ ρ n) := by
  unfold rowGaussian; fun_prop

theorem rowGaussian_law (a : Fin k → ℝ) (τ ρ n : ℝ) (hn : n≠0)
    (hv : ρ^2+τ^2*(∑i,a i^2)=n^2) :
    ((Measure.pi fun _ : Fin k => stdGaussian (Point d)).prod
      (Measure.pi fun _ : Fin 1 => stdGaussian (Point d))).map (rowGaussian a τ ρ n)=
      stdGaussian (Point d) := by
  let w : Fin (k+1) → ℝ := Fin.append (fun i => a i*τ) (fun _ => ρ)
  have hw : (∑i,w i^2)=n^2 := by
    simp only [w,Fin.sum_univ_add,Fin.append_left,Fin.append_right,mul_pow,←Finset.sum_mul,
      Fin.sum_univ_one]
    nlinarith only [hv]
  have hsum := weighted_gaussian_law (E:=Point d) w n hw
  have he (z : (Fin k → Point d) × (Fin 1 → Point d)) :
      (∑i,w i • Fin.append z.1 z.2 i)=(∑i,a i • (τ • z.1 i))+ρ • z.2 0 := by
    simp only [w,Fin.sum_univ_add,Fin.append_left,Fin.append_right,mul_smul,Fin.sum_univ_one]
  have hh := congrArg (Measure.map (fun z : Point d => n⁻¹ • z)) hsum
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at hh
  have hright : (fun z : Point d => n⁻¹ • z) ∘ (fun z => n • z)=id := by
    funext z; simp [smul_smul,hn]
  rw [hright,Measure.map_id] at hh
  rw [←(appendSlots_preserving (stdGaussian (Point d)) k 1).map_eq,
    Measure.map_map (by fun_prop) (appendSlots_preserving (stdGaussian (Point d)) k 1).measurable] at hh
  simp only [Function.comp_def,he] at hh
  exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d k : ℕ}

theorem compileTerms_squared (V : Point d → ℝ) (hV : Measurable (firstOrderReply V))
    {D τ ρ n : ℝ} (hD : 0<D) (hn : n≠0) (a r K S B : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d)
    (b : X → Point d) (hb : Measurable b) (x : X) (c m : Fin k → Point d)
    (hv : ρ^2+τ^2*(∑i,a i^2)=n^2)
    (hK : ∀i,0≤K i) (hvshift : ∀i,(∑j,(M i).shift j^2)≤D^2)
    (hshift : ∀i,ShiftInvariant (r i) (M i).shift (fun c g => (M i).program.run V (c,g)))
    (hLip : ∀i u v g,‖(M i).program.run V (u,g)-(M i).program.run V (v,g)‖≤K i*‖u-v‖)
    (hC : ∀i,SquaredAt (Measure.pi fun _ : Fin (C i).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((C i).eval V x) (fun g => c i+(r i/(2*D)) • g) (S i))
    (hM : ∀i,SquaredAt (Measure.pi fun _ : Fin (M i).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) (fun g => (M i).program.run V (c i,g)) (fun g => m i+τ • g) (B i)) :
    SquaredAt (Measure.pi fun _ : Fin (compileTerms D k a C M (.noise b hb ρ)).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileTerms D k a C M (.noise b hb ρ)).eval V x)
      (fun g => (∑i,a i • m i)+b x+n • g)
      ((∑i,|a i|)*(∑i,|a i| * (2*(K i)^2*S i+2*B i))) := by
  let γ := stdGaussian (Point d)
  let A i := fun z : (Fin (C i).slots → Point d) × (Fin (M i).slots → Point d) =>
    (M i).program.run V ((C i).eval V x z.1,(M i).damping D z.2)
  have hcmeas (i) : Measurable ((C i).eval V x) :=
    ((C i).measurable_eval V hV).comp (measurable_const.prodMk measurable_id)
  have hameas (i) : Measurable (A i) :=
    ((M i).program.measurable_run V hV).comp
      (((hcmeas i).comp measurable_fst).prodMk ((M i).measurable_damping D |>.comp measurable_snd))
  have ha (i) : SquaredAt
      ((Measure.pi fun _ : Fin (C i).slots => γ).prod (Measure.pi fun _ : Fin (M i).slots => γ)) γ
      (A i) (fun g => m i+τ • g) (2*(K i)^2*S i+2*B i) :=
    SquaredAt.absorb_fixed _ _ (hcmeas i) (c i) (m i) hD (hK i) (M i).shift (hvshift i)
      (fun c g => (M i).program.run V (c,g)) ((M i).program.measurable_run V hV)
      (hshift i) (hLip i) (hC i) (hM i)
  have hrow := SquaredAt.weighted_pi _ _ A (fun i g => m i+τ • g) hameas
    (by intro; fun_prop) a (fun i => 2*(K i)^2*S i+2*B i) ha
  have hfrow : Measurable (fun z : RowTape C M => ∑i,a i • A i (z i)) := by fun_prop
  have hgrow : Measurable (fun z : Fin k → Point d => ∑i,a i • (m i+τ • z i)) := by fun_prop
  have hext := hrow.common_noise hfrow hgrow (Measure.pi fun _ : Fin 1 => γ)
    (fun z => b x+ρ • z 0) (by fun_prop)
  have hout : Measurable ((compileTerms D k a C M (.noise b hb ρ)).eval V x) :=
    ((compileTerms D k a C M (.noise b hb ρ)).measurable_eval V hV).comp
      (measurable_const.prodMk measurable_id)
  have hfin := hext.reindex (concatTerms D k a C M (.noise b hb ρ)) (rowGaussian a τ ρ n)
    (concatTerms_preserving D k a C M (.noise b hb ρ)).measurable
    (measurable_rowGaussian a τ ρ n) _ (fun g => (∑i,a i • m i)+b x+n • g) hout (by fun_prop)
    (by intro z; exact eval_concatTerms V D k a C M (.noise b hb ρ) x z)
    (by
      intro z
      dsimp only [rowGaussian]
      rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
      simp only [smul_add,Finset.sum_add_distrib]
      abel)
  have hcmap : Measure.map (concatTerms D k a C M (.noise b hb ρ))
      ((Measure.pi fun i => (Measure.pi fun _ : Fin (C i).slots => γ).prod
        (Measure.pi fun _ : Fin (M i).slots => γ)).prod (Measure.pi fun _ : Fin 1 => γ))=
      (Measure.pi fun _ : Fin (compileTerms D k a C M (.noise b hb ρ)).slots => γ) :=
    (concatTerms_preserving D k a C M (.noise b hb ρ)).map_eq
  have hgmap : Measure.map (rowGaussian a τ ρ n)
      ((Measure.pi fun _ : Fin k => γ).prod (Measure.pi fun _ : Fin 1 => γ))=γ :=
    rowGaussian_law a τ ρ n hn hv
  rw [hcmap,hgmap] at hfin
  exact hfin
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclared_squared (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A : ℝ} (hD : 0<D) (hA : 0<A)
    (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (K : ℝ → ℝ → ℝ) (B : ℝ → ℝ → Point d → ℝ)
    (hK : ∀r τ,P r τ → 0≤K r τ)
    (hvshift : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤D^2)
    (hshift : ∀r τ,P r τ → ShiftInvariant r (M r τ).shift (fun c g => (M r τ).program.run V (c,g)))
    (hLip : ∀r τ,P r τ → ∀u v g,‖(M r τ).program.run V (u,g)-(M r τ).program.run V (v,g)‖≤K r τ*‖u-v‖)
    (hM : ∀r τ,P r τ → ∀c,SquaredAt
      (Measure.pi fun _ : Fin (M r τ).slots => stdGaussian (Point d)) (stdGaussian (Point d))
      (fun g => (M r τ).program.run V (c,g)) (fun g => primitiveExpectedField F c r+τ • g) (B r τ c))
    (E : MeanTree X d) (n : ℝ) (x : X) (hE : DeclaredValid D A P E n) :
    SquaredAt (Measure.pi fun _ : Fin (compileDeclared D A M E n).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileDeclared D A M E n).eval V x)
      (fun g => E.eval F x+n • g) (declaredError F D A K B E n x) := by
  induction E generalizing n with
  | node k b hb a r C ih =>
    obtain ⟨hn,hw,hc⟩ := hE
    have hi (i) := ih i (r i/(2*D)) (hc i).2
    have hh := compileTerms_squared V hV hD hn.ne' a r
      (fun i => K (r i) (declaredNoise n A))
      (fun i => declaredError F D A K B (C i) (r i/(2*D)) x)
      (fun i => B (r i) (declaredNoise n A) ((C i).eval F x))
      (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) b hb x
      (fun i => (C i).eval F x) (fun i => primitiveExpectedField F ((C i).eval F x) (r i))
      (declaredReserve_variance hA n a hw)
      (fun i => hK _ _ (hc i).1) (fun i => hvshift _ _ (hc i).1)
      (fun i => hshift _ _ (hc i).1) (fun i => hLip _ _ (hc i).1) hi
      (fun i => hM _ _ (hc i).1 _)
    have he : (fun g => (node k b hb a r C).eval F x+n • g)=
        (fun g => (∑i,a i • primitiveExpectedField F ((C i).eval F x) (r i))+b x+n • g) := by
      funext g
      simp only [eval,add_comm (b x)]
    rw [he]
    exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclaredRoot_squared (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A Af : ℝ} (hD : 0<D) (hA : 0<A) (hAf : 0<Af)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (K : Bool → ℝ → ℝ → ℝ) (B : Bool → ℝ → ℝ → Point d → ℝ)
    (hK : ∀s r τ,P s r τ → 0≤K s r τ)
    (hvshift : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2)≤D^2)
    (hshift : ∀s r τ,P s r τ → ShiftInvariant r (M s r τ).shift (fun c g => (M s r τ).program.run V (c,g)))
    (hLip : ∀s r τ,P s r τ → ∀u v g,‖(M s r τ).program.run V (u,g)-(M s r τ).program.run V (v,g)‖≤K s r τ*‖u-v‖)
    (hM : ∀s r τ,P s r τ → ∀c,SquaredAt
      (Measure.pi fun _ : Fin (M s r τ).slots => stdGaussian (Point d)) (stdGaussian (Point d))
      (fun g => (M s r τ).program.run V (c,g)) (fun g => primitiveExpectedField F c r+τ • g) (B s r τ c))
    (E : MeanTree X d) (n : ℝ) (x : X) (hE : DeclaredRootValid D A Af (P true) (P false) E n) :
    SquaredAt (Measure.pi fun _ : Fin (compileDeclaredRoot D A Af (M true) (M false) E n).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileDeclaredRoot D A Af (M true) (M false) E n).eval V x)
      (fun g => E.eval F x+n • g) (declaredRootError F D A Af (K true) (K false) (B true) (B false) E n x) := by
  cases E with | node k b hb a r C =>
    obtain ⟨hn,hw,hc⟩ := hE
    have hi (i) := compileDeclared_squared F V hV hD hA (P false) (M false) (K false) (B false)
      (hK false) (hvshift false) (hshift false) (hLip false) (hM false) (C i) (r i/(2*D)) x (hc i).2
    have hh := compileTerms_squared V hV hD hn.ne' a r
      (fun i => K true (r i) (declaredNoise n Af))
      (fun i => declaredError F D A (K false) (B false) (C i) (r i/(2*D)) x)
      (fun i => B true (r i) (declaredNoise n Af) ((C i).eval F x))
      (fun i => compileDeclared D A (M false) (C i) (r i/(2*D)))
      (fun i => M true (r i) (declaredNoise n Af)) b hb x
      (fun i => (C i).eval F x) (fun i => primitiveExpectedField F ((C i).eval F x) (r i))
      (declaredReserve_variance hAf n a hw)
      (fun i => hK _ _ _ (hc i).1) (fun i => hvshift _ _ _ (hc i).1)
      (fun i => hshift _ _ _ (hc i).1) (fun i => hLip _ _ _ (hc i).1) hi
      (fun i => hM _ _ _ (hc i).1 _)
    have he : (fun g => (node k b hb a r C).eval F x+n • g)=
        (fun g => (∑i,a i • primitiveExpectedField F ((C i).eval F x) (r i))+b x+n • g) := by
      funext g
      simp only [eval,add_comm (b x)]
    rw [he]
    exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

omit [MeasurableSpace X] in
lemma DirectCenter.radius {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 ≤ r) (_hT0 : 0≤T) (_hT1 : T<1)
    (hb : DirectCenter r T v x Y G r' b) :
    r*Real.sqrt (1-T^2) ≤ r' ∧ r' ≤ r := by
  obtain ⟨ρ,hρ,θ,hθ,rfl,hb⟩ := hb
  have hρsq : ρ^2≤T^2 := pow_le_pow_left₀ hρ.1 hρ.2 2
  have hlo := Real.sqrt_le_sqrt (show 1-T^2≤1-ρ^2 by linarith)
  have hhi : Real.sqrt (1-ρ^2)≤1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [sq_nonneg ρ]⟩
  exact ⟨mul_le_mul_of_nonneg_left hlo hr,(mul_le_mul_of_nonneg_left hhi hr).trans_eq (mul_one r)⟩

omit [MeasurableSpace X] in
lemma DirectCenter.radius_pos {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 < r) (hT0 : 0≤T) (hT1 : T<1)
    (hb : DirectCenter r T v x Y G r' b) : 0 < r' := by
  have ht : 0<1-T^2 := by nlinarith
  exact lt_of_lt_of_le (mul_pos hr (Real.sqrt_pos.mpr ht)) (hb.radius hr.le hT0 hT1).1

omit [MeasurableSpace X] in
lemma oriented_norm (Y G : X → Point d) (θ : ℝ) (z : X) :
    ‖oriented Y G θ z‖≤‖Y z‖+|θ| *‖G z‖ := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  have hc := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg (Y z))
  have hs := mul_le_mul_of_nonneg_right (Real.abs_sin_le_abs (x:=θ)) (norm_nonneg (G z))
  linarith

omit [MeasurableSpace X] in
lemma DirectCenter.norm_displacement {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 ≤ r) (_hT0 : 0≤T) (hT1 : T≤1)
    (hb : DirectCenter r T v x Y G r' b) (z : X) :
    ‖b z-x z‖ ≤ r*(‖Y z‖+v*‖G z‖) := by
  obtain ⟨ρ,hρ,θ,hθ,hr',rfl⟩ := hb
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg hr,abs_of_nonneg hρ.1]
  have hY : ‖oriented Y G θ z‖≤‖Y z‖+v*‖G z‖ :=
    by
      have h := oriented_norm Y G θ z
      have hmul := mul_le_mul_of_nonneg_right hθ (norm_nonneg (G z))
      linarith
  have hρ1 := hρ.2.trans hT1
  exact (mul_le_mul_of_nonneg_left hY (mul_nonneg hr hρ.1)).trans
    (by nlinarith [mul_nonneg hr (show 0≤‖Y z‖+v*‖G z‖ by
      have hv := (abs_nonneg θ).trans hθ
      positivity)])

lemma rootScales_add (P : ℝ → Prop) (E B : MeanTree X d)
    (hE : rootScales P E) (hB : rootScales P B) : rootScales P (add E B) := by
  cases E with | node k b hb a r C =>
    cases B with | node l c hc v s D =>
      intro i
      exact Fin.addCases (fun j => by simpa [add] using hE j)
        (fun j => by simpa [add] using hB j) i
lemma rootScales_sumFin (P : ℝ → Prop) (k : ℕ) (E : Fin k → MeanTree X d)
    (hE : ∀i,rootScales P (E i)) : rootScales P (sumFin k E) := by
  induction k with
  | zero => exact rootScales_anchor _ _ _
  | succ k ih => exact rootScales_add P _ _ (hE 0) (ih _ (fun i => hE i.succ))
lemma rootScales_sumFamily {I : Type*} [Fintype I] (P : ℝ → Prop)
    (E : I → MeanTree X d) (hE : ∀i,rootScales P (E i)) : rootScales P (sumFamily E) :=
  rootScales_sumFin P _ _ (fun _ => hE _)

lemma meanCircuit_final_radius (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (xE yE : MeanTree X d)
    (G : X → Point d) (hG : Measurable G) :
    rootScales (fun r' => r'=r*Real.sqrt (1-T^2))
      (meanCircuit r T h ψ s n m N nc Nc e xE yE (anchor G hG)) := by
  apply rootScales_add
  · exact (rootScales_scale _ _ _).2 (rootScales_anchor _ _ _)
  · apply rootScales_sumFamily
    intro j
    apply (rootScales_scale _ _ _).2
    intro i
    rfl

lemma declaredValid_of_radius_bounds {D A lo hi n : ℝ} (hD : 0<D) (hlo : 0<lo)
    (P : ℝ → ℝ → Prop) (E : MeanTree X d) (hw : weight E≤A) (hC : centersBound A E)
    (hscale : centers (fun r _ => lo ≤ r ∧ r≤hi) E)
    (hn : lo/(2*D)≤n ∧ n≤hi/(2*D))
    (hP : ∀r q,lo ≤ r → r≤hi → lo/(2*D)≤q → q≤hi/(2*D) → P r (declaredNoise q A)) :
    DeclaredValid D A P E n := by
  induction E generalizing n with | node k b hb a r C ih =>
    refine ⟨lt_of_lt_of_le (div_pos hlo (by positivity)) hn.1,hw,?_⟩
    intro i
    refine ⟨hP _ _ (hscale i).1.1 (hscale i).1.2 hn.1 hn.2,?_⟩
    exact ih i (hC i).1 (hC i).2 (hscale i).2
      ⟨div_le_div_of_nonneg_right (hscale i).1.1 (by positivity),
       div_le_div_of_nonneg_right (hscale i).1.2 (by positivity)⟩

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma child_depth_le (k : ℕ) (b : X → Point d) (hb : Measurable b)
    (a r : Fin k → ℝ) (C : Fin k → MeanTree X d) (i : Fin k) :
    depth (C i)+1≤depth (.node k b hb a r C) :=
  Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i)

lemma centerValues_of_bounds {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (z : X) {A B : ℝ} (hB : 0≤B)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1) (M : ℕ)
    (E : MeanTree X d) (hweights : centersBound A E) (hd : depth E≤M)
    (hc : centers (fun r b => 0 ≤ r ∧ (lam:ℝ)*r^2≤1/2 ∧ (lam:ℝ)*r≤1 ∧
      circuitD F x+(lam:ℝ)*‖b z-x‖≤B) E) :
    centerValues F ((M:ℝ)*B) E z := by
  induction E with | node k b hm a r C ih =>
    intro i
    have hdi := (child_depth_le k b hm a r C i).trans hd
    have hdi' : ((depth (C i):ℝ)+1)≤(M:ℝ) := by exact_mod_cast hdi
    refine ⟨?_,ih i (hweights i).2 (by omega) (hc i).2⟩
    apply (eval_circuitD_bound hF x z hB hsmall (C i) (hweights i).1
      (hweights i).2 (hc i).1.2.2.2 (hc i).2).trans
    exact mul_le_mul_of_nonneg_right hdi' hB

omit [MeasurableSpace X] in
lemma directCenter_scalar_bounds {r T v r' : ℝ} {x Y G b : X → Point d}
    {lam : ℝ≥0} (hr : 0 ≤ r) (hT : 0≤T) (hT1 : T<1)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hb : DirectCenter r T v x Y G r' b) :
    0 ≤ r' ∧ (lam:ℝ)*r'^2≤1/2 ∧ (lam:ℝ)*r'≤1 := by
  have hrad := hb.radius hr hT hT1
  have hr' : 0 ≤ r' := (mul_nonneg hr (Real.sqrt_nonneg _)).trans hrad.1
  exact ⟨hr',(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr' hrad.2 2) lam.coe_nonneg).trans hl,
    (mul_le_mul_of_nonneg_left hrad.2 lam.coe_nonneg).trans hL⟩

theorem centerValues_of_direct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T v A : ℝ} (hr : 0 ≤ r) (hT : 0≤T) (hT1 : T<1) (hv : 0≤v)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1)
    (x Y G : X → Point d) (z : X) (M : ℕ) (E : MeanTree X d)
    (hweights : centersBound A E) (hd : depth E≤M)
    (hc : centers (DirectCenter r T v x Y G) E) :
    centerValues F ((M:ℝ)*(circuitD F (x z)+(lam:ℝ)*r*(‖Y z‖+v*‖G z‖))) E z := by
  apply centerValues_of_bounds hF (x z) z (by positivity [circuitD_nonneg F (x z)])
    hsmall M E hweights hd
  apply centers_mono E (fun r' b hb => ?_) hc
  have hs := directCenter_scalar_bounds hr hT hT1 hl hL hb
  refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
  have hdisp := mul_le_mul_of_nonneg_left (hb.norm_displacement hr hT hT1.le z) lam.coe_nonneg
  linarith
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem declaredError_uniform (F : Point d → ℝ) (D : ℝ) {A L R : ℝ}
    (_hA : 0≤A) (hR : 0≤R) (hc : 4*A^2*L^2≤1)
    (K : ℝ → ℝ → ℝ) (B : ℝ → ℝ → Point d → ℝ)
    (E : MeanTree X d) (n : ℝ) (x : X) (hw : weight E≤A) (hweights : centersBound A E)
    (hE : ErrorLimits F D A K B L R E n x) :
    declaredError F D A K B E n x≤4*A^2*R := by
  induction E generalizing n with | node k b hb a r C ih =>
    have hchild (i : Fin k) := ih i (r i/(2*D)) (hweights i).1 (hweights i).2 (hE i).2.2
    have hterm (i : Fin k) :
        2*(K (r i) (declaredNoise n A))^2*declaredError F D A K B (C i) (r i/(2*D)) x+
          2*B (r i) (declaredNoise n A) ((C i).eval F x)≤2*L^2*(4*A^2*R)+2*R := by
      have h₁ := mul_le_mul_of_nonneg_left (hchild i) (show 0≤2*(K (r i) (declaredNoise n A))^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_right (hE i).1 (show 0≤2*(4*A^2*R) by positivity)
      linarith [(hE i).2.1]
    have hs0 : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin k) _ => mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg (a i)))
    rw [←Finset.sum_mul] at hsum
    have htot := mul_le_mul_of_nonneg_left hsum hs0
    change (∑i,|a i|)≤A at hw
    have hs := pow_le_pow_left₀ hs0 hw 2
    have hsq := mul_le_mul_of_nonneg_right hs (show 0≤2*L^2*(4*A^2*R)+2*R by positivity)
    have hcon := mul_le_mul_of_nonneg_right hc (show 0≤2*A^2*R by positivity)
    change (∑i,|a i|)*(∑i,|a i| *_)≤_
    nlinarith

theorem declaredRootError_bound (F : Point d → ℝ) (D A : ℝ) {Af L H e Q : ℝ}
    (hAf : 0<Af) (hH : 0≤H)
    (Kf Ki : ℝ → ℝ → ℝ) (Bf Bi : ℝ → ℝ → Point d → ℝ)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (n : ℝ) (x : X) (hw : (∑i,|a i|)≤Af)
    (hK : ∀i,(Kf (r i) (declaredNoise n Af))^2≤L^2)
    (hB : ∀i,Bf (r i) (declaredNoise n Af) ((C i).eval F x)≤(declaredNoise n Af)^2*e^2*Q^2)
    (hchild : ∀i,declaredError F D A Ki Bi (C i) (r i/(2*D)) x≤H) :
    declaredRootError F D A Af Kf Ki Bf Bi (.node k b hb a r C) n x≤
      2*Af^2*L^2*H+n^2*e^2*Q^2/2 := by
  have hterm (i : Fin k) :
      2*(Kf (r i) (declaredNoise n Af))^2*declaredError F D A Ki Bi (C i) (r i/(2*D)) x+
        2*Bf (r i) (declaredNoise n Af) ((C i).eval F x)≤
      2*L^2*H+2*(declaredNoise n Af)^2*e^2*Q^2 := by
    have h₁ := mul_le_mul_of_nonneg_left (hchild i) (show 0≤2*(Kf (r i) (declaredNoise n Af))^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (hK i) (show 0≤2*H by positivity)
    linarith [hB i]
  have hs0 : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin k) _ => mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg (a i)))
  rw [←Finset.sum_mul] at hsum
  have htot := mul_le_mul_of_nonneg_left hsum hs0
  have hs := pow_le_pow_left₀ hs0 hw 2
  have hsq := mul_le_mul_of_nonneg_right hs
    (show 0≤2*L^2*H+2*(declaredNoise n Af)^2*e^2*Q^2 by positivity)
  have hid : Af^2*(declaredNoise n Af)^2=n^2/4 := by
    unfold declaredNoise
    field_simp [ne_of_gt hAf]
    ring
  change (∑i,|a i|)*(∑i,|a i| *_)≤_
  nlinarith [mul_nonneg (sq_nonneg e) (sq_nonneg Q)]
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma normalizedErrorLimits (F : Point d → ℝ) {D A hi n L e Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hn : 0≤n) (hhi : n≤hi/(2*D))
    (K : ℝ → ℝ → ℝ) (hK : ∀r τ,0 ≤ r → r≤hi → 0≤τ →
      τ≤declaredNoise (hi/(2*D)) A → (K r τ)^2≤L^2)
    (E : MeanTree X d) (x : X)
    (hs : centers (fun r _ => 0 ≤ r ∧ r≤hi) E) (hc : centerValues F Q E x) :
    ErrorLimits F D A K (fun _ τ c => τ^2*e^2*(circuitD F c)^2)
      L ((declaredNoise (hi/(2*D)) A)^2*e^2*Q^2) E n x := by
  induction E generalizing n with | node k b hb a r C ih =>
    have ht0 : 0≤declaredNoise n A := by unfold declaredNoise; positivity
    have ht : declaredNoise n A≤declaredNoise (hi/(2*D)) A :=
      div_le_div_of_nonneg_right hhi (by positivity)
    intro i
    refine ⟨hK _ _ (hs i).1.1 (hs i).1.2 ht0 ht,?_,?_⟩
    · have hnoise := pow_le_pow_left₀ ht0 ht 2
      have hvalue := pow_le_pow_left₀ (circuitD_nonneg F _) (hc i).1 2
      exact mul_le_mul (mul_le_mul_of_nonneg_right hnoise (sq_nonneg e)) hvalue
        (sq_nonneg _) (by positivity)
    · exact ih i (div_nonneg (hs i).1.1 (by positivity))
        (div_le_div_of_nonneg_right (hs i).1.2 (by positivity)) (hs i).2 (hc i).2

theorem declaredError_normalized (F : Point d → ℝ) {D A hi n L e Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hn : 0≤n) (hhi : n≤hi/(2*D))
    (hcon : 4*A^2*L^2≤1)
    (K : ℝ → ℝ → ℝ) (hK : ∀r τ,0 ≤ r → r≤hi → 0≤τ →
      τ≤declaredNoise (hi/(2*D)) A → (K r τ)^2≤L^2)
    (E : MeanTree X d) (x : X) (hw : weight E≤A) (hc : centersBound A E)
    (hs : centers (fun r _ => 0 ≤ r ∧ r≤hi) E) (hv : centerValues F Q E x) :
    declaredError F D A K (fun _ τ c => τ^2*e^2*(circuitD F c)^2) E n x≤
      (hi/(2*D))^2*e^2*Q^2 := by
  have he := declaredError_uniform F D hA.le (by positivity) hcon K
    (fun _ τ c => τ^2*e^2*(circuitD F c)^2) E n x hw hc
    (normalizedErrorLimits F hD hA hn hhi K hK E x hs hv)
  have hid : 4*A^2*((declaredNoise (hi/(2*D)) A)^2*e^2*Q^2)=
      (hi/(2*D))^2*e^2*Q^2 := by
    unfold declaredNoise
    field_simp [hA.ne',hD.ne']
    ring
  rwa [hid] at he

theorem declaredRootError_normalized (F : Point d → ℝ) {D A Af hi n Li Lf ei ef Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hAf : 0<Af) (hcon : 4*A^2*Li^2≤1)
    (Ki Kf : ℝ → ℝ → ℝ)
    (hKi : ∀r τ,0 ≤ r → r≤hi → 0≤τ → τ≤declaredNoise (hi/(2*D)) A → (Ki r τ)^2≤Li^2)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (x : X) (hw : (∑i,|a i|)≤Af)
    (hc : centersBound A (.node k b hb a r C))
    (hs : centers (fun r _ => 0 ≤ r ∧ r≤hi) (.node k b hb a r C))
    (hv : centerValues F Q (.node k b hb a r C) x)
    (hKf : ∀i,(Kf (r i) (declaredNoise n Af))^2≤Lf^2) :
    declaredRootError F D A Af Kf Ki
      (fun _ τ c => τ^2*ef^2*(circuitD F c)^2)
      (fun _ τ c => τ^2*ei^2*(circuitD F c)^2) (.node k b hb a r C) n x≤
      (2*Af^2*Lf^2*(hi/(2*D))^2*ei^2+n^2*ef^2/2)*Q^2 := by
  have hierr (i : Fin k) := declaredError_normalized F (e := ei) hD hA
    (div_nonneg (hs i).1.1 (by positivity))
    (div_le_div_of_nonneg_right (hs i).1.2 (by positivity)) hcon Ki hKi (C i) x
    (hc i).1 (hc i).2 (hs i).2 (hv i).2
  have he := declaredRootError_bound F D A hAf (by positivity) Kf Ki
    (fun _ τ c => τ^2*ef^2*(circuitD F c)^2)
    (fun _ τ c => τ^2*ei^2*(circuitD F c)^2) k b hb a r C n x hw hKf
    (fun i => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (circuitD_nonneg F _) (hv i).1 2) (by positivity)) hierr
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenterValuesMono
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
lemma centerValues_mono {F : Point d → ℝ} {Q Q' : ℝ} (h : Q≤Q') (E : MeanTree X d) (x : X) :
    centerValues F Q E x → centerValues F Q' E x := by
  induction E with | node k b hb a r C ih =>
    intro he i
    exact ⟨(he i).1.trans h,ih i (he i).2⟩
end LogConcaveSampling.MeanTree

end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CentersBoundPicard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma centersBound_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    {A B C W : ℝ} (_hB : 0≤B) (hC : 0≤C) (hw : ∀i,∑j,|w i j|≤B)
    (hφw : ∀i E,weight (φ i E)≤C)
    (haw : ∀i,weight (a i)≤W) (ha : ∀i,centersBound A (a i))
    (hφ : ∀i E,weight E≤W+B*C → centersBound A E → centersBound A (φ i E))
    (N : ℕ) (i : I) : centersBound A (picard w φ a N i) := by
  induction N generalizing i with
  | zero => exact ha i
  | succ N ih =>
    apply (centersBound_add _ _ _).2
    refine ⟨ha i,centersBound_sumFamily _ _ (fun j => ?_)⟩
    apply (centersBound_scale _ _ _).2
    apply hφ j _ ?_ (ih j)
    exact (weight_picard w φ a hC hw hφw N j).trans (add_le_add_left (haw j) _)

lemma probability_weights {r T h P A : ℝ} (hr : 0 ≤ r) (hP : 0≤P) (n N : ℕ)
    (s : ProbabilityNode T h n)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hw : ∀i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (x y : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y)
    (hA : r*(weight y+P*r)≤A) (i : ProbabilityNode T h n) :
    weight (probability r T h n N s x y i)≤weight y+P*r ∧
      centersBound A (probability r T h n N s x y i) := by
  have hc (j : ProbabilityNode T h n) (E : MeanTree X d) :
      weight (scale (-r) (conditional r (probabilityNodeTime T h n j) x E)) ≤ r := by
    simp [abs_of_nonneg hr]
  constructor
  · exact weight_picard _ _ _ hr hw hc N i
  · apply centersBound_picard _ _ _ hP hr hw hc (fun _ => le_rfl) (fun _ => hy) ?_ N i
    intro j E hE hEb
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx hEb
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    calc
      r*|probabilityNodeTime T h n j| * weight E ≤ r*weight E := by
        nlinarith [weight_nonneg E,mul_le_mul_of_nonneg_left (ht j) hr]
      _ ≤ r*(weight y+P*r) := mul_le_mul_of_nonneg_left hE hr
      _≤A := hA

lemma harmonic_weights {r ρ v H A : ℝ} (hr : 0 ≤ r) (hρ : |ρ|≤1) (hH : 0≤H)
    (n N : ℕ) (hw : ∀i,∑j,|harmonicWeight n v i j|≤H)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+H*r)≤A) (i : Fin (n+1)) :
    weight (harmonic r ρ v n N x y g i)≤weight y+weight g+H*r ∧
      centersBound A (harmonic r ρ v n N x y g i) := by
  have hc (j : Fin (n+1)) (E : MeanTree X d) :
      weight (scale ρ (scale (-r) (conditional r ρ x E))) ≤ r := by
    simp only [weight_scale,weight_conditional,abs_neg,abs_of_nonneg hr,mul_one]
    nlinarith
  have ha (j : Fin (n+1)) : weight (add (scale (Real.cos (v*probabilityNodes n j)) y)
      (scale (Real.sin (v*probabilityNodes n j)) g))≤weight y+weight g := by
    simp only [weight_add,weight_scale]
    exact add_le_add
      (by nlinarith [Real.abs_cos_le_one (v*probabilityNodes n j),weight_nonneg y])
      (by nlinarith [Real.abs_sin_le_one (v*probabilityNodes n j),weight_nonneg g])
  constructor
  · exact (weight_picard _ _ _ hr hw hc N i).trans (add_le_add_left (ha i) _)
  · apply centersBound_picard _ _ _ hH hr hw hc ha
      (fun _ => (centersBound_add _ _ _).2 ⟨(centersBound_scale _ _ _).2 hy,(centersBound_scale _ _ _).2 hg⟩) ?_ N i
    intro j E hE hEb
    apply (centersBound_scale _ _ _).2
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx hEb
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    calc
      r*|ρ| * weight E ≤ r*weight E := by nlinarith [weight_nonneg E,mul_le_mul_of_nonneg_left hρ hr]
      _ ≤ r*(weight y+weight g+H*r) := mul_le_mul_of_nonneg_left hE hr
      _≤A := hA

lemma kernelCorrection_weights {r T h v P H A : ℝ} (hr : 0 ≤ r) (hP : 0≤P) (hH : 0≤H)
    (n N : ℕ) (s e : ProbabilityNode T h n)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (hhw : ∀i,∑j,|harmonicWeight n v i j|≤H)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+(2*P+H)*r)≤A) :
    weight (kernelCorrection r T h v n N s e x y g)≤P*r ∧
      centersBound A (kernelCorrection r T h v n N s e x y g) := by
  have hB : r*(weight y+P*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    nlinarith [weight_nonneg g]
  have hb := probability_weights hr hP n N e ht (hpw e) x y hxw hx hy hB s
  let b := probability r T h n N e x y s
  have hW : r*(weight b+weight g+H*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    dsimp only [b]
    nlinarith [hb.1]
  have hw := harmonic_weights hr (ht s) hH n N hhw x b g hxw hx hb.2 hg hW (Fin.last n)
  let w := harmonic r (probabilityNodeTime T h n s) v n N x b g (Fin.last n)
  have hF : r*(weight w+P*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    dsimp only [w]
    nlinarith [hw.1,hb.1]
  have hf (j : ProbabilityNode T h n) := probability_weights hr hP n N s ht (hpw s) x w hxw hx hw.2 hF j
  constructor
  · simp only [kernelCorrection,weight_sumFamily,weight_scale,weight_conditional,abs_neg,abs_of_nonneg hr,mul_one]
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hpw s e) hr
  · unfold kernelCorrection
    change centersBound A (sumFamily (fun j => scale (reanchorWeight (probabilityWeight T h n) s e j) (scale (-r) (conditional r (probabilityNodeTime T h n j) x (probability r T h n N s x w j)))))
    apply centersBound_sumFamily
    intro j
    apply (centersBound_scale _ _ _).2
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx (hf j).2
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    apply le_trans _ hF
    calc
      r*|probabilityNodeTime T h n j| * weight (probability r T h n N s x w j)
        ≤r*weight (probability r T h n N s x w j) := by
          nlinarith [weight_nonneg (probability r T h n N s x w j),mul_le_mul_of_nonneg_left (ht j) hr]
      _ ≤ r*(weight w+P*r) := mul_le_mul_of_nonneg_left (hf j).1 hr

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma kernelQuadrature_weights {r T h ψ P H A Q S : ℝ}
    (hr : 0 ≤ r) (hP : 0≤P) (hH : 0≤H) (_hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h n) (w : ProbabilityNode T h n → ℝ)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight n (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|w j|≤Q) (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+(2*P+H)*r)≤A) :
    weight (kernelQuadrature r T h ψ n m N e w x y g)≤Q*S*(P*r) ∧
      centersBound A (kernelQuadrature r T h ψ n m N e w x y g) := by
  have hc (j : ProbabilityNode T h n) (k : Fin (m+1)) :=
    kernelCorrection_weights hr hP hH n N j e ht hpw (hhw k) x y g hxw hx hy hg hA
  have ha (j : ProbabilityNode T h n) : weight (kernelAction r T h ψ n m N j e x y g)≤S*(P*r) := by
    simp only [kernelAction,weight_sumFamily,weight_scale]
    calc
      _≤∑k,|derivativeWeight (angleNodes m) k/ψ| * (P*r) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hc j k).1 (abs_nonneg _))
      _=(∑k,|derivativeWeight (angleNodes m) k/ψ|)*(P*r) := (Finset.sum_mul _ _ _).symm
      _≤S*(P*r) := mul_le_mul_of_nonneg_right hsw (mul_nonneg hP hr)
  constructor
  · simp only [kernelQuadrature,weight_sumFamily,weight_scale]
    calc
      _≤∑j,|w j| * (S*(P*r)) := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _))
      _=(∑j,|w j|)*(S*(P*r)) := (Finset.sum_mul _ _ _).symm
      _≤Q*(S*(P*r)) := mul_le_mul_of_nonneg_right hqw (by positivity)
      _=Q*S*(P*r) := by ring
  · apply centersBound_sumFamily
    intro j
    apply (centersBound_scale _ _ _).2
    apply centersBound_sumFamily
    intro k
    exact (centersBound_scale _ _ _).2 (hc j k).2

lemma velocity_weights {r T h ψ s P H A Q S : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A p.1) (hg : centersBound A p.2)
    (hA : r*(weight p.1+weight p.2+(2*P+H)*r)≤A) :
    weight (velocity r T h ψ s n m N e x p).1+
      weight (velocity r T h ψ s n m N e x p).2≤(Q*S*P+2)/s ∧
    centersBound A (velocity r T h ψ s n m N e x p).1 ∧
      centersBound A (velocity r T h ψ s n m N e x p).2 := by
  have hk := kernelQuadrature_weights hr.le hP hH hQ hS n.succ m N e _ ht hpw hhw hqw hsw x p.1 p.2 hxw hx hy hg hA
  have hA0 : 0≤A := (mul_nonneg hr.le (by positivity [weight_nonneg p.1,weight_nonneg p.2])).trans hA
  constructor
  · simp only [velocity,weight_scale,weight_add,weight_conditional,weight_mean,
      abs_neg,abs_one,one_mul,abs_inv,abs_mul,abs_of_pos hr,abs_of_pos hs]
    apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_left hk.1 (by positivity)) _)
    have he : (r*s)⁻¹*(Q*S*(P*r))+s⁻¹*(1+1)=(Q*S*P+2)/s := by field_simp; ring
    exact he.le
  · constructor
    · exact (centersBound_scale _ _ _).2 hk.2
    · dsimp only [velocity]
      apply (centersBound_scale _ _ _).2
      apply (centersBound_add _ _ _).2
      constructor
      · apply centersBound_conditional hx hy
        rw [hxw,zero_add,abs_mul,abs_of_pos hr]
        calc
          r*|T| * weight p.1 ≤ r*weight p.1 := by nlinarith [weight_nonneg p.1,mul_le_mul_of_nonneg_left hT hr.le]
          _ ≤ r*(weight p.1+weight p.2+(2*P+H)*r) := by
            apply mul_le_mul_of_nonneg_left _ hr.le
            linarith [weight_nonneg p.2,mul_nonneg (show 0≤2*P+H by positivity) hr.le]
          _≤A := hA
      · apply (centersBound_scale _ _ _).2
        exact (centersBound_mean _ _ _).2 ⟨by simpa [hxw] using hA0,hx⟩

lemma weight_velocity_input_independent (r T h ψ s : ℝ) (n m N : ℕ)
    (e : ProbabilityNode T h (n+1)) (x z : MeanTree X d)
    (p q : MeanTree X d × MeanTree X d) :
    weight (velocity r T h ψ s n m N e x p).1+weight (velocity r T h ψ s n m N e x p).2=
    weight (velocity r T h ψ s n m N e z q).1+weight (velocity r T h ψ s n m N e z q).2 := by
  simp only [velocity,weight_scale,weight_add,weight_mean,weight_conditional,
    kernelQuadrature,kernelAction,kernelCorrection,weight_sumFamily]

lemma velocity_root_weights {r T h ψ s P H Q S : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) :
    weight (velocity r T h ψ s n m N e x p).1+
      weight (velocity r T h ψ s n m N e x p).2≤(Q*S*P+2)/s := by
  rw [weight_velocity_input_independent r T h ψ s n m N e x zero p (zero,zero)]
  exact (velocity_weights (A:=r*((2*P+H)*r)) hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw
    zero (zero,zero) (by simp) (by simp) (by simp) (by simp) (by simp)).1

lemma pairPicard_weights {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) {B K : ℝ} (hB : 0≤B) (hK : 0≤K)
    (hw : ∀i,∑j,|w i j|≤B)
    (hφ : ∀p,weight (φ p).1+weight (φ p).2≤K) (N : ℕ) (i : I) :
    weight (pairPicard w φ a N i).1+weight (pairPicard w φ a N i).2≤
      weight a.1+weight a.2+B*K := by
  cases N with
  | zero => simpa only [pairPicard] using le_add_of_nonneg_right (a:=weight a.1+weight a.2) (mul_nonneg hB hK)
  | succ N =>
    simp only [pairPicard,weight_add,weight_sumFamily,weight_scale]
    have he : (∑j,|w i j| * weight (φ (pairPicard w φ a N j)).1)+
        (∑j,|w i j| * weight (φ (pairPicard w φ a N j)).2)≤B*K := by
      rw [←Finset.sum_add_distrib]
      calc
        _≤∑j,|w i j| * K := Finset.sum_le_sum (fun j _ => by rw [←mul_add]; exact mul_le_mul_of_nonneg_left (hφ _) (abs_nonneg _))
        _=(∑j,|w i j|)*K := (Finset.sum_mul _ _ _).symm
        _≤B*K := mul_le_mul_of_nonneg_right (hw i) hK
    linarith

lemma centersBound_pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) {A B K : ℝ} (hB : 0≤B) (hK : 0≤K)
    (hw : ∀i,∑j,|w i j|≤B)
    (hφw : ∀p,weight (φ p).1+weight (φ p).2≤K)
    (ha : centersBound A a.1 ∧ centersBound A a.2)
    (hφ : ∀p,weight p.1+weight p.2≤weight a.1+weight a.2+B*K →
      centersBound A p.1 → centersBound A p.2 →
      centersBound A (φ p).1 ∧ centersBound A (φ p).2) (N : ℕ) (i : I) :
    centersBound A (pairPicard w φ a N i).1 ∧ centersBound A (pairPicard w φ a N i).2 := by
  induction N generalizing i with
  | zero => exact ha
  | succ N ih =>
    have hstep (j : I) := hφ _ (pairPicard_weights w φ a hB hK hw hφw N j) (ih j).1 (ih j).2
    exact ⟨(centersBound_add _ _ _).2 ⟨ha.1,centersBound_sumFamily _ _ (fun j => (centersBound_scale _ _ _).2 (hstep j).1)⟩,
      (centersBound_add _ _ _).2 ⟨ha.2,centersBound_sumFamily _ _ (fun j => (centersBound_scale _ _ _).2 (hstep j).2)⟩⟩
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem centeringStates_weights {r T h ψ s P H Q S B A : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r)≤A)
    (i : Fin (nc+1)) :
    weight (centeringStates r T h ψ s n m N nc Nc e x y g i).1+
      weight (centeringStates r T h ψ s n m N nc Nc e x y g i).2≤
        weight y+weight g+B*((Q*S*P+2)/s) ∧
    centersBound A (centeringStates r T h ψ s n m N nc Nc e x y g i).1 ∧
      centersBound A (centeringStates r T h ψ s n m N nc Nc e x y g i).2 := by
  have hK : 0≤(Q*S*P+2)/s := by positivity
  have hφ := velocity_root_weights (X:=X) (d:=d) hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw x
  constructor
  · exact pairPicard_weights _ _ (y,g) hB hK hcw hφ Nc i
  · apply centersBound_pairPicard _ _ (y,g) hB hK hcw hφ ⟨hy,hg⟩ _ Nc i
    intro p hp hpy hpg
    exact (velocity_weights hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw x p hxw hx hpy hpg
      ((mul_le_mul_of_nonneg_left (add_le_add_left hp _) hr.le).trans hA)).2

theorem meanCircuit_weights {r T h ψ s P H Q S B A : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (hout : ∑j,|Quadrature.weight (probabilityNodes nc) j 0 1|≤B)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r)≤A) :
    weight (meanCircuit r T h ψ s n m N nc Nc e x y g)≤|s| * weight g+B ∧
      centersBound A (meanCircuit r T h ψ s n m N nc Nc e x y g) := by
  have hz := centeringStates_weights hr hs hT hP hH hQ hS hB n m N nc Nc e ht hpw hhw hqw hsw hcw x y g hxw hx hy hg hA
  constructor
  · simpa only [meanCircuit,weight_add,weight_scale,weight_sumFamily,weight_conditional,mul_one]
      using add_le_add_right hout (|s| * weight g)
  · apply (centersBound_add _ _ _).2
    refine ⟨(centersBound_scale _ _ _).2 hg,centersBound_sumFamily _ _ ?_⟩
    intro j
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx (hz j).2.1
    rw [hxw,zero_add,abs_mul,abs_of_pos hr]
    calc
      r*|T| * weight (centeringStates r T h ψ s n m N nc Nc e x y g j).1
          ≤r*weight (centeringStates r T h ψ s n m N nc Nc e x y g j).1 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hr.le) (weight_nonneg (centeringStates r T h ψ s n m N nc Nc e x y g j).1)
      _ ≤ r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r) := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        have hb := (hz j).1
        linarith [weight_nonneg (centeringStates r T h ψ s n m N nc Nc e x y g j).2,
          mul_nonneg (show 0≤2*P+H by positivity) hr.le]
      _≤A := hA
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CompileDeclaredRootNormalized
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclaredRoot_normalized (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A Af hi n Li Lf ei ef Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hAf : 0<Af) (hLi : 0≤Li) (hLf : 0≤Lf)
    (hcon : 4*A^2*Li^2≤1)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hshift : ∀s r τ,P s r τ → ShiftInvariant r (M s r τ).shift
      (fun c g => (M s r τ).program.run V (c,g)))
    (henergy : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2)≤D^2)
    (hLipi : ∀r τ,P false r τ → ∀u v g,
      ‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (hLipf : ∀r τ,P true r τ → ∀u v g,
      ‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hMi : ∀r τ,P false r τ → ∀c,SquaredAt (gaussianTape d (M false r τ).slots)
      (stdGaussian (Point d)) (fun g => (M false r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (τ^2*ei^2*(circuitD F c)^2))
    (hMf : ∀r τ,P true r τ → ∀c,SquaredAt (gaussianTape d (M true r τ).slots)
      (stdGaussian (Point d)) (fun g => (M true r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (τ^2*ef^2*(circuitD F c)^2))
    (E : MeanTree X d) (x : X) (hE : DeclaredRootValid D A Af (P true) (P false) E n)
    (hc : centersBound A E) (hs : centers (fun r _ => 0 ≤ r ∧ r≤hi) E)
    (hv : centerValues F Q E x) :
    SquaredAt (gaussianTape d (compileDeclaredRoot D A Af (M true) (M false) E n).slots)
      (stdGaussian (Point d)) ((compileDeclaredRoot D A Af (M true) (M false) E n).eval V x)
      (fun g => E.eval F x+n • g)
      ((2*Af^2*Lf^2*(hi/(2*D))^2*ei^2+n^2*ef^2/2)*Q^2) := by
  let K : Bool → ℝ → ℝ → ℝ := fun s _ _ => if s then Lf else Li
  let B : Bool → ℝ → ℝ → Point d → ℝ := fun s _ τ c =>
    τ^2*(if s then ef else ei)^2*(circuitD F c)^2
  have hK : ∀s r τ,P s r τ → 0≤K s r τ := by
    intro s r τ _; cases s <;> assumption
  have hLip : ∀s r τ,P s r τ → ∀u v g,
      ‖(M s r τ).program.run V (u,g)-(M s r τ).program.run V (v,g)‖≤K s r τ*‖u-v‖ := by
    intro s; cases s; exact hLipi; exact hLipf
  have hM : ∀s r τ,P s r τ → ∀c,SquaredAt (gaussianTape d (M s r τ).slots)
      (stdGaussian (Point d)) (fun g => (M s r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (B s r τ c) := by
    intro s; cases s; exact hMi; exact hMf
  have hh := compileDeclaredRoot_squared F V hV hD hA hAf P M K B
    hK henergy hshift hLip hM E n x hE
  apply hh.mono
  cases E with | node k b hb a r C =>
    exact declaredRootError_normalized F hD hA hAf hcon (K false) (K true)
      (fun _ _ _ _ _ _ => le_rfl) k b hb a r C x hE.2.1 hc hs hv (fun _ => le_rfl)
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma literalMean_weights {r T h ψ σ P H Q S B A Af : ℝ}
    (hr : 0 < r) (hσ : 0<σ) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (hout : ∑j,|Quadrature.weight (probabilityNodes nc) j 0 1|≤B)
    (hA₁ : 2*B*(Q*S*P+2)≤A) (hA₂ : 2*P+H≤A) (hAf : B≤Af) :
    weight (literalMean (d:=d) r T h ψ σ n m N nc Nc e)≤Af ∧
      centersBound (A*(r/σ+r^2)) (literalMean (d:=d) r T h ψ σ n m N nc Nc e) := by
  have hbound : r*(B*((Q*S*P+2)/(σ/2))+(2*P+H)*r)≤A*(r/σ+r^2) := by
    have h₁ := mul_le_mul_of_nonneg_right hA₁ (show 0 ≤ r/σ by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hA₂ (sq_nonneg r)
    have he : r*(B*((Q*S*P+2)/(σ/2))+(2*P+H)*r)=
        (2*B*(Q*S*P+2))*(r/σ)+(2*P+H)*r^2 := by field_simp
    rw [he]
    nlinarith
  have hh := meanCircuit_weights (d:=d) (X:=MeanInput d) hr (by positivity : 0<σ/2) hT
    hP hH hQ hS hB n m N nc Nc e ht hpw hhw hqw hsw hcw hout
    (anchor Prod.fst (by fun_prop)) (anchor (fun z => z.2.1) (by fun_prop))
    (anchor (fun z => z.2.2) (by fun_prop)) (by simp) (by simp) (by simp) (by simp)
    (by simpa only [weight_anchor,zero_add] using hbound)
  simp only [weight_anchor,mul_zero,zero_add] at hh
  exact ⟨hh.1.trans hAf,hh.2⟩
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma declaredRootValid_of_radius_bounds {D A Af lo hi n : ℝ} (hD : 0<D) (hlo : 0<lo)
    (Pf Pi : ℝ → ℝ → Prop) (E : MeanTree X d) (hn : 0<n)
    (hw : weight E≤Af) (hC : centersBound A E)
    (hscale : centers (fun r _ => lo ≤ r ∧ r≤hi) E)
    (hfinal : rootScales (fun r => Pf r (declaredNoise n Af)) E)
    (hPi : ∀r q,lo ≤ r → r≤hi → lo/(2*D)≤q → q≤hi/(2*D) → Pi r (declaredNoise q A)) :
    DeclaredRootValid D A Af Pf Pi E n := by
  cases E with | node k b hb a r C =>
    refine ⟨hn,hw,?_⟩
    intro i
    refine ⟨hfinal i,?_⟩
    exact declaredValid_of_radius_bounds hD hlo Pi (C i) (hC i).1 (hC i).2 (hscale i).2
      ⟨div_le_div_of_nonneg_right (hscale i).1.1 (by positivity),
       div_le_div_of_nonneg_right (hscale i).1.2 (by positivity)⟩ hPi
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanSize
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable {d : ℕ}

lemma MeanSize.nonneg {lam q r σ : ℝ} (hlam : 0 ≤ lam) (h : MeanSize lam q r σ) : 0 ≤ q :=
  (mul_nonneg hlam (sq_nonneg r)).trans h.2.2.2.1

lemma internal_meanSize {lam Q r R D A r' n : ℝ}
    (hlam : 0 ≤ lam) (hQ : 0 ≤ Q) (hr : 0 < r) (hr1 : r ≤ 1)
    (hR : 0 < R) (hD : 0 < D) (hA : 0 < A)
    (hl : lam*r^2 ≤ Q) (hlo : r*R ≤ r') (hhi : r' ≤ r)
    (hn : r*R/(2*D) ≤ n) :
    MeanSize lam (Q+4*D*lam*A/R) r' (declaredNoise n A) := by
  have hr' : 0 < r' := (mul_pos hr hR).trans_le hlo
  have hn0 : 0 < n := (div_pos (mul_pos hr hR) (by positivity)).trans_le hn
  have hτ : 0 < declaredNoise n A := by unfold declaredNoise; positivity
  have hloτ : r*R/(4*D*A) ≤ declaredNoise n A := by
    have hh := div_le_div_of_nonneg_right hn (show 0 ≤ 2*A by positivity)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  refine ⟨hr',hhi.trans hr1,hτ,?_,?_⟩
  · have he := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hhi 2) hlam).trans hl
    exact he.trans (le_add_of_nonneg_right (by positivity))
  · have hh := mul_le_mul_of_nonneg_left hloτ (show 0 ≤ 4*D*lam*A/R by positivity)
    have hid : (4*D*lam*A/R)*(r*R/(4*D*A))=lam*r := by field_simp
    rw [hid] at hh
    have hrh := mul_le_mul_of_nonneg_left hhi hlam
    have hQt := mul_nonneg hQ hτ.le
    nlinarith

namespace CircuitParameters
variable (C : CircuitParameters)
lemma meanCenterBudget_small {lam q r σ : ℝ} (h : MeanSize lam q r σ) (hA : 0 ≤ C.A) :
    lam*C.meanCenterBudget r σ ≤ 2*C.A*q := by
  have hs : lam*r/σ ≤ q := (div_le_iff₀ h.2.2.1).2 h.2.2.2.2
  have hh := mul_le_mul_of_nonneg_left (add_le_add hs h.2.2.2.1) hA
  unfold meanCenterBudget
  convert! hh using 1 <;> ring

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Quadrature FinitePicard
open scoped Classical BigOperators NNReal

lemma fixedProbabilityBudget_spec (n : ℕ) : 0≤fixedProbabilityBudget n ∧
    ∀{T h : ℝ},0<T → T<1 → 0<h →
      ∀i : ProbabilityNode T h (n+1),∑j,|probabilityWeight T h (n+1) i j|≤fixedProbabilityBudget n :=
  (probabilityWeight_budget (n+1) (Nat.succ_pos n)).choose_spec

lemma fixedCenteringBudget_spec (n : ℕ) : 0≤fixedCenteringBudget n ∧
    (∀i,∑j,|centeringWeight n i j|≤fixedCenteringBudget n) ∧
    (∑j,|Quadrature.weight (probabilityNodes n) j 0 1|≤fixedCenteringBudget n) := by
  have h₁ : 0≤∑i : Fin (n+1),∑j,|centeringWeight n i j| := by positivity
  have h₂ : 0≤∑j : Fin (n+1),|Quadrature.weight (probabilityNodes n) j 0 1| := by positivity
  refine ⟨by unfold fixedCenteringBudget; positivity,?_,?_⟩
  · intro i
    have he := Finset.single_le_sum (fun j (_ : j∈Finset.univ) =>
      show 0≤∑k,|centeringWeight n j k| by positivity) (Finset.mem_univ i)
    unfold fixedCenteringBudget
    linarith
  · unfold fixedCenteringBudget
    linarith

namespace CircuitParameters
variable (C : CircuitParameters)

lemma actualA_pos : 0<C.actualA := by
  have hP := (fixedProbabilityBudget_spec C.n).1
  have hB := (fixedCenteringBudget_spec C.nc).1
  have hQ : 0≤C.quadratureBudget := by unfold quadratureBudget; positivity
  have hS : 0≤C.derivativeBudget := by unfold derivativeBudget; positivity
  unfold actualA
  positivity
lemma actualAf_pos : 0<C.actualAf := by
  have hP := (fixedProbabilityBudget_spec C.n).1
  have hB := (fixedCenteringBudget_spec C.nc).1
  unfold actualAf
  positivity

lemma angle_mem (hψ : 0≤C.ψ) (j : Fin (C.m+1)) :
    C.ψ*angleNodes C.m j∈Set.Icc (0:ℝ) 1 := by
  have hj : 0≤angleNodes C.m j := by simp [angleNodes]
  have hv : C.v≤1 := by
    have hR : Real.sqrt (1-C.T^2)≤1 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by norm_num,by nlinarith [sq_nonneg C.T]⟩
    nlinarith [C.angle_small]
  exact ⟨mul_nonneg hψ hj,(le_abs_self _).trans ((C.angle_bound j).trans hv)⟩

lemma meanTree_actual_weights {d : ℕ} {r σ : ℝ} (hr : 0 < r) (hσ : 0<σ)
    (hψ : 0≤C.ψ) : weight (C.meanTree (d:=d) r σ)≤C.actualAf ∧
    centersBound (C.actualA*(r/σ+r^2)) (C.meanTree (d:=d) r σ) := by
  have hT0 : 0<C.T := by linarith [C.T_lower]
  have hP := fixedProbabilityBudget_spec C.n
  have hB := fixedCenteringBudget_spec C.nc
  have hP0 := hP.1
  have hB0 := hB.1
  have hQ : 0≤C.quadratureBudget := by unfold quadratureBudget; positivity
  have hS : 0≤C.derivativeBudget := by unfold derivativeBudget; positivity
  have hh := (harmonicWeight_budget (C.n+1) (Nat.succ_pos C.n)).choose_spec
  apply literalMean_weights hr hσ (by rw [abs_of_pos hT0]; exact C.T_upper.le)
    (by positivity : 0≤2*fixedProbabilityBudget C.n) (fixedHarmonicBudget C.n).coe_nonneg
    hQ hS hB.1 C.n C.m C.N C.nc C.Nc C.meanEndpoint
  · intro j
    have ht := probabilityNodeTime_mem hT0 C.T_upper C.h_pos (Nat.succ_pos C.n) j
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans C.T_upper.le
  · intro a i
    exact reanchorWeight_budget _ (hP.2 hT0 C.T_upper C.h_pos) a i
  · intro k i
    exact hh _ (C.angle_mem hψ k).1 (C.angle_mem hψ k).2 i
  · exact le_rfl
  · exact le_rfl
  · exact hB.2.1
  · exact hB.2.2
  · unfold actualA
    have h := (fixedHarmonicBudget C.n).coe_nonneg
    linarith [hP.1]
  · unfold actualA
    have he : 0≤2*fixedCenteringBudget C.nc*
      (C.quadratureBudget*C.derivativeBudget*(2*fixedProbabilityBudget C.n)+2) := by positivity
    linarith
  · unfold actualAf
    linarith [hP.1]

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanCorrect
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable {d : ℕ}

lemma MeanSize.mono {lam q q' r σ : ℝ} (h : MeanSize lam q r σ) (hq : q≤q') :
    MeanSize lam q' r σ :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1.trans hq,
    h.2.2.2.2.trans (mul_le_mul_of_nonneg_right hq h.2.2.1.le)⟩

lemma final_mean_size {lam q r σ R Af : ℝ} (hlam : 0≤lam)
    (h : MeanSize lam q r σ) (hR : 0<R) (hR1 : R≤1) (hAf : 0<Af) :
    MeanSize lam ((1+4*Af)*R*q) (r*R) (declaredNoise (Real.sqrt 3*σ/2) Af) := by
  have hr := h.1
  have hσ := h.2.2.1
  have hq := h.nonneg hlam
  have hroot : 1≤Real.sqrt 3 := by norm_num
  have hn : 0<declaredNoise (Real.sqrt 3*σ/2) Af := by unfold declaredNoise; positivity
  have hrR : r*R ≤ r := mul_le_of_le_one_right h.1.le hR1
  have hR2 : R^2≤R := by nlinarith
  have hsq := mul_le_mul_of_nonneg_right h.2.2.2.1 (sq_nonneg R)
  have hqR := mul_le_mul_of_nonneg_left hR2 hq
  have hAfR : R*q≤(1+4*Af)*R*q := by nlinarith [mul_nonneg hR.le hq]
  refine ⟨mul_pos h.1 hR,hrR.trans h.2.1,hn,?_,?_⟩
  · nlinarith [hsq]
  · have hσ : σ/(4*Af)≤declaredNoise (Real.sqrt 3*σ/2) Af := by
      unfold declaredNoise
      have hh := mul_le_mul_of_nonneg_right hroot h.2.2.1.le
      apply (le_div_iff₀ (by positivity : 0<2*Af)).2
      calc
        σ/(4*Af)*(2*Af)=σ/2 := by field_simp; ring
        _≤Real.sqrt 3*σ/2 := by linarith
    have hs := mul_le_mul_of_nonneg_right h.2.2.2.2 hR.le
    have ht := mul_le_mul_of_nonneg_left hσ (show 0≤4*Af*R*q by positivity)
    have hid : (4*Af*R*q)*(σ/(4*Af))=q*σ*R := by field_simp
    rw [hid] at ht
    have he : 4*Af*R*q≤(1+4*Af)*R*q := by nlinarith [mul_nonneg hR.le hq]
    have hh := mul_le_mul_of_nonneg_right he hn.le
    nlinarith

namespace CircuitParameters
variable (C : CircuitParameters)

lemma residual_pos : 0<Real.sqrt (1-C.T^2) := by
  apply Real.sqrt_pos.mpr
  nlinarith [C.T_lower,C.T_upper]
lemma residual_le_one : Real.sqrt (1-C.T^2)≤1 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by norm_num,by nlinarith [sq_nonneg C.T]⟩

theorem meanTree_valid {lam q r σ : ℝ} (hlam : 0≤lam) (hs : MeanSize lam q r σ)
    (hD : 0<C.D) (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf) :
    DeclaredRootValid C.D (C.meanCenterBudget r σ) C.Af
      (MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q))
      (MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))))
      (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hr := hs.1
  have hσ := hs.2.2.1
  have hb : 0<C.meanCenterBudget r σ := by unfold meanCenterBudget; positivity
  have hR := C.residual_pos
  have hq := hs.nonneg hlam
  have hw := C.meanTree_actual_weights (d:=d) hs.1 hs.2.2.1 hψ
  rw [←hA,←hAf] at hw
  have hg := (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
  apply declaredRootValid_of_radius_bounds hD (mul_pos hs.1 hR) _ _ _ (by positivity) hw.1 hw.2
  · exact centers_mono _ (fun r' b h => h.radius hs.1.le (by linarith [C.T_lower]) C.T_upper) hg
  · have hf := meanCircuit_final_radius (d:=d) r C.T C.h C.ψ (σ/2) C.n C.m C.N C.nc C.Nc C.meanEndpoint
      (anchor Prod.fst (by fun_prop)) (anchor (fun z : MeanInput d => z.2.1) (by fun_prop))
      (fun z : MeanInput d => z.2.2) (by fun_prop)
    cases he : C.meanTree (d:=d) r σ with | node k b hb a rr cc =>
      change ∀i, MeanSize _ _ (rr i) _
      have hf' : ∀i,rr i=r*Real.sqrt (1-C.T^2) := by
        change rootScales (fun r' => r'=r*Real.sqrt (1-C.T^2)) (C.meanTree r σ) at hf
        rw [he] at hf
        exact hf
      intro i
      rw [hf' i]
      exact final_mean_size hlam hs hR C.residual_le_one hAf0
  · intro r' n hlo hhi hn _
    apply (internal_meanSize hlam hq hs.1 hs.2.1 hR hD hb hs.2.2.2.1 hlo hhi hn).mono
    have hsmall := C.meanCenterBudget_small hs hA0.le
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤4*C.D/Real.sqrt (1-C.T^2) by positivity)
    have hx : 0≤C.D*C.A*q/Real.sqrt (1-C.T^2) := by positivity
    nlinarith [show (4*C.D/Real.sqrt (1-C.T^2))*(lam*C.meanCenterBudget r σ)=
      4*C.D*lam*C.meanCenterBudget r σ/Real.sqrt (1-C.T^2) by ring,
      show (4*C.D/Real.sqrt (1-C.T^2))*(2*C.A*q)=8*(C.D*C.A*q/Real.sqrt (1-C.T^2)) by ring,
      show q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))=q+16*(C.D*C.A*q/Real.sqrt (1-C.T^2)) by ring]

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PairGauge
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeanTree MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

namespace OracleCompiler.CircuitParameters
variable (C : CircuitParameters)
lemma meanTree_centerValues {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r σ : ℝ} (hr : 0 < r) (hσ : 0<σ) (hψ : 0≤C.ψ)
    (hA : C.A=C.actualA) (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2)≤1)
    (x Y G : Point d) :
    centerValues F (2*(depth (C.meanTree (d:=d) r σ):ℝ)*pairGauge (circuitD F x) (Y,G))
      (C.meanTree r σ) (x,(Y,G)) := by
  have hT : 0≤C.T := by linarith [C.T_lower]
  have hw := (C.meanTree_actual_weights (d:=d) hr hσ hψ).2
  rw [←hA] at hw
  have hg := (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
  have hh := centerValues_of_direct hF hr.le hT C.T_upper C.v_nonneg hl hL hsmall
    Prod.fst (fun z : MeanInput d => z.2.1) (fun z : MeanInput d => z.2.2) (x,(Y,G))
    (depth (C.meanTree r σ)) (C.meanTree r σ) hw le_rfl hg
  apply centerValues_mono _ _ _ hh
  have hv : C.v≤1 := by nlinarith [C.angle_small,C.residual_le_one]
  have hY : ‖Y‖≤‖(Y,G)‖ := show ‖Y‖ ≤ max ‖Y‖ ‖G‖ from le_max_left _ _
  have hG : ‖G‖≤‖(Y,G)‖ := show ‖G‖ ≤ max ‖Y‖ ‖G‖ from le_max_right _ _
  have hc := circuitD_nonneg F x
  have hvG := mul_le_of_le_one_left (norm_nonneg G) hv
  have hlr := mul_le_of_le_one_left (show 0≤‖Y‖+C.v*‖G‖ by positivity [C.v_nonneg]) hL
  have he : circuitD F x+(lam:ℝ)*r*(‖Y‖+C.v*‖G‖)≤2*pairGauge (circuitD F x) (Y,G) := by
    change circuitD F x+(lam:ℝ)*r*(‖Y‖+C.v*‖G‖)≤2*(1+circuitD F x+‖(Y,G)‖)
    linarith
  have hmult := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (depth (C.meanTree (d:=d) r σ)): (0:ℝ)≤_)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hmult

end OracleCompiler.CircuitParameters
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_ShiftInvariant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory MeanTree Coupling SeedCompiler
open scoped Classical BigOperators NNReal

variable {d : ℕ}

lemma MeanBudget.shiftInvariant {B : ℕ} {r : ℝ} {S : SeedProgram d}
    (h : MeanBudget B r S) (F : Point d → ℝ) :
    ShiftInvariant r S.shift (fun c g => S.program.run F (c,g)) := by
  intro x Δ g
  exact (h.equiv Δ).run F (x,g)

namespace CircuitParameters
variable (C : CircuitParameters)
lemma meanCompiled_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r σ : ℝ} (hs : MeanSize lam q r σ) (hl : q≤1/2)
    (hL : (lam:ℝ)*r≤1) (hD : 0<C.D) (hψ : 0≤C.ψ)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2)≤1)
    (hcon : 4*(C.meanCenterBudget r σ)^2*((lam:ℝ)*Ki)^2≤1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y G : Point d) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi
      (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,(Y,G)))
      (fun g => (C.meanTree r σ).eval F (x,(Y,G))+(Real.sqrt 3*σ/2) • g)
      ((2*C.Af^2*((lam:ℝ)*Kf)^2*(r/(2*C.D))^2*ei^2+(Real.sqrt 3*σ/2)^2*ef^2/2)*
        (2*(depth (C.meanTree (d:=d) r σ):ℝ)*pairGauge (circuitD F x) (Y,G))^2) := by
  have hr := hs.1
  have hn := hs.2.2.1
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) else
    MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  have hb (s : Bool) (r τ : ℝ) := hbudget s r τ
  have hV : Measurable (firstOrderReply F) := hF.smooth.continuous.measurable.prodMk
    hF.gradient_lipschitz.continuous.measurable
  have hv := C.meanTree_valid (d:=d) lam.coe_nonneg hs hD hψ hA hAf
  have hw := C.meanTree_actual_weights (d:=d) hs.1 hs.2.2.1 hψ
  rw [←hAf,←hA] at hw
  have hg := (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
  have hrs : centers (fun r' _ => 0 ≤ r' ∧ r' ≤ r) (C.meanTree (d:=d) r σ) :=
    centers_mono _ (fun r' b hb => ⟨(hb.radius_pos hs.1 (by linarith [C.T_lower]) C.T_upper).le,
      (hb.radius hs.1.le (by linarith [C.T_lower]) C.T_upper).2⟩) hg
  exact compileDeclaredRoot_normalized F F hV hD
    (by unfold meanCenterBudget; rw [hA]; positivity [C.actualA_pos])
    (by rw [hAf]; exact C.actualAf_pos) (mul_nonneg lam.coe_nonneg hKi) (mul_nonneg lam.coe_nonneg hKf)
    hcon P M (fun s r τ _ => (hb s r τ).shiftInvariant F)
    (fun s r τ _ => (hb s r τ).energy.trans hBD) hi.lip hf.lip hi.error hf.error
    (C.meanTree r σ) (x,(Y,G)) hv hw.2 hrs
    (C.meanTree_centerValues hF hs.1 hs.2.2.1 hψ hA (hs.2.2.2.1.trans hl) hL hsmall x Y G)

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory
open scoped Classical

lemma physicalCoefficient_bound {lam r s D Af K ei ef q n : ℝ}
    (hl : 0 ≤ lam) (hr : 0 ≤ r) (hs : 0 < s) (hD : 1 ≤ D) (hAf : 0 ≤ Af)
    (hK : 0 ≤ K) (hi : 0 ≤ ei) (hf : 0 ≤ ef) (hq : lam*r ≤ q*s)
    (hn : 0 ≤ n) (hns : n ≤ s) :
    2*Af^2*(lam*K)^2*(r/(2*D))^2*ei^2+n^2*ef^2/2 ≤
      2*s^2*(Af*K*q*ei+ef)^2 := by
  have hD0 : 0 < 2*D := by linarith
  have hq0 : 0 ≤ q := by nlinarith [mul_nonneg hl hr]
  have hab : lam*r/(2*D) ≤ q*s := by
    apply (div_le_iff₀ hD0).2
    have hh := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 2*D) (mul_nonneg hq0 hs.le)
    nlinarith
  have ha : 0 ≤ Af*K*(lam*r/(2*D))*ei := by positivity
  have hb : Af*K*(lam*r/(2*D))*ei ≤ s*(Af*K*q*ei) := by
    have hh := mul_le_mul_of_nonneg_left hab (show 0 ≤ Af*K*ei by positivity)
    nlinarith
  have hc : n*ef ≤ s*ef := mul_le_mul_of_nonneg_right hns hf
  have ha2 := pow_le_pow_left₀ ha hb 2
  have hb2 := pow_le_pow_left₀ (mul_nonneg hn hf) hc 2
  have hid : Af^2*(lam*K)^2*(r/(2*D))^2*ei^2=(Af*K*(lam*r/(2*D))*ei)^2 := by ring
  have hid2 : 2*Af^2*(lam*K)^2*(r/(2*D))^2*ei^2=2*(Af*K*(lam*r/(2*D))*ei)^2 := by nlinarith [hid]
  rw [hid2]
  nlinarith [mul_nonneg (show 0 ≤ Af*K*q*ei by positivity) hf]

lemma physicalError_bound {c s a dep ρ : ℝ} (_hs : 0 ≤ s) (_ha : 0 ≤ a) (hd : 0 ≤ dep)
    (hc : c ≤ 2*s^2*a^2) :
    c*(dep*ρ)^2 ≤ (2*s*(1+dep)*a)^2*ρ^2 := by
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (dep*ρ))
  have hdep : 2*dep^2 ≤ (2*(1+dep))^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_right hdep (show 0 ≤ s^2*a^2*ρ^2 by positivity)
  nlinarith

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree MeasureTheory ProbabilityTheory Coupling SeedCompiler
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

lemma meanCompiled_scaled_oai {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r σ : ℝ} (hs : MeanSize lam q r σ) (hl : q ≤ 1/2)
    (hL : (lam:ℝ)*r ≤ 1) (hD : 1 ≤ C.D) (hψ : 0 ≤ C.ψ)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 ≤ ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.meanCenterBudget r σ)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y G : Point d) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi
      (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2)
    let a := 2*(1+2*(depth (C.meanTree (d:=d) r σ):ℝ))*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,(Y,G)))
      (fun g => (C.meanTree r σ).eval F (x,(Y,G))+(Real.sqrt 3*σ/2) • g)
      ((σ*a)^2*(pairGauge (circuitD F x) (Y,G))^2) := by
  have hAf0 : 0 ≤ C.Af := by rw [hAf]; exact C.actualAf_pos.le
  have hn : Real.sqrt 3*σ/2 ≤ σ := by
    have hh : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg (3:ℝ)]
    nlinarith [mul_le_mul_of_nonneg_right hh hs.2.2.1.le]
  have hc := physicalCoefficient_bound lam.coe_nonneg hs.1.le hs.2.2.1 hD hAf0 hKf hei hef
    hs.2.2.2.2 (show 0 ≤ Real.sqrt 3*σ/2 by positivity [hs.2.2.1]) hn
  have hb := physicalError_bound hs.2.2.1.le
    (show 0 ≤ C.Af*Kf*q*ei+ef by positivity [hs.nonneg lam.coe_nonneg])
    (show 0 ≤ 2*(depth (C.meanTree (d:=d) r σ):ℝ) by positivity)
    (ρ:=pairGauge (circuitD F x) (Y,G)) hc
  have hp := C.meanCompiled_squared hF hs hl hL (by linarith) hψ hA hAf hKf hKi hsmall hcon
    Mf Mi B hBD hbudget hf hi x Y G
  apply hp.mono
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled_oai := @OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled_oai
