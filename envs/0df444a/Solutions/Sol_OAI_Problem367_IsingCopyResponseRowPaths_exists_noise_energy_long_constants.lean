-- Prove2me | solution 1 for OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:22.887204+00:00
-- url     : https://prove2.me/submissions/35475a32-f3ad-43b1-bbe7-39f323b00f95

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingCopySpectral_forwardOperator_pow_bound
import Theorems.Thm_OAI_Problem367_IsingOrientedPath_measure_extensionAverage_gt_le_double_exp_common

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal

namespace Problem367
namespace CavityPair

variable {ψ : ℝ → ℝ} {θ : ℝ≥0}

theorem solve_swap (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) :
    solve hψ hθ z.swap = (solve hψ hθ z).swap := by
  apply solve_eq hψ hθ
  exact ⟨(solve_spec hψ hθ z).2, (solve_spec hψ hθ z).1⟩

end CavityPair
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Homeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem cavityFromSites_swap {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) : cavityFromSites h0 h1 z.swap = (cavityFromSites h0 h1 z).swap :=
  CavityPair.solve_swap (lipschitzWith_cavityMessage h0 h1.le) h1 z

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CoupledAttenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367

theorem cavity_pair_sub_abs_le
    {theta x y x' y' H K H' K' M : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hx : x + cavityMessage theta y = H)
    (hy : y + cavityMessage theta x = K)
    (hx' : x' + cavityMessage theta y' = H')
    (hy' : y' + cavityMessage theta x' = K')
    (hH : |H - H'| ≤ M) (hK : |K - K'| ≤ M) :
    |x - x'| ≤ M / (1 - theta) := by
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hminus : 1 - theta ≠ 0 := by linarith
  have hplus : 1 + theta ≠ 0 := by linarith
  have hdist := CavityPair.stability_fst
    (lipschitzWith_cavityMessage hθ0 hθ1.le)
    (show (⟨theta, hθ0⟩ : ℝ≥0) < 1 from hθ1) hx hy hx' hy'
  change dist x x' ≤ (dist H H' + theta * dist K K') / (1 - theta ^ 2) at hdist
  have habs : |x - x'| ≤
      (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := by
    simpa only [Real.dist_eq, NNReal.coe_mk] using hdist
  calc
    |x - x'| ≤ (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := habs
    _ ≤ (M + theta * M) / (1 - theta ^ 2) := by gcongr
    _ = M / (1 - theta) := by
      field_simp
      ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Transitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem exists_treeAut_to_root {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = ⟨[], List.IsChain.nil⟩ := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil => exact ⟨TreeAut.refl d, rfl⟩
  | cons a w ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.tail
    obtain ⟨g, hg⟩ := ih hw'
    refine ⟨(prefixTreeAut a).trans g, ?_⟩
    change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
    have hflip : prefixFlip a ⟨a :: w, hw⟩ = ⟨w, hw'⟩ := by
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord]
    rw [hflip]
    exact hg

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Array
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

theorem field_reverse (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H w v = (cavityFromSites h0 h1 (H v, H w)).2 := by
  exact congrArg Prod.fst (cavityFromSites_swap h0 h1 (H v, H w))

theorem field_spec (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H v w + cavityMessage theta (field h0 h1 H w v) = H v := by
  rw [field_reverse h0 h1 H v w]
  exact (cavityFromSites_spec h0 h1 (H v, H w)).1

theorem field_sub_abs_le (h0 : 0 ≤ theta) (h1 : theta < 1)
    {H H' : TreeVertex d → ℝ} {M : ℝ} (v w : TreeVertex d)
    (hv : |H v - H' v| ≤ M) (hw : |H w - H' w| ≤ M) :
    |field h0 h1 H v w - field h0 h1 H' v w| ≤ M / (1 - theta) :=
  cavity_pair_sub_abs_le h0 h1
    (field_spec h0 h1 H v w) (field_spec h0 h1 H w v)
    (field_spec h0 h1 H' v w) (field_spec h0 h1 H' w v) hv hw

end Problem367.CavityArray

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CopyDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

theorem pullback_ae {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) (f : Lp ℝ 2 μ) :
    pullback hp f =ᵐ[ν] fun z => f (p z) :=
  Lp.coeFn_compMeasurePreserving f hp

theorem operator_ae {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (f : Lp ℝ 2 μ) :
    operator hp hq f =ᵐ[ν] fun z => f (p z) - f (q z) := by
  have hd := Lp.coeFn_sub (pullback hp f) (pullback hq f)
  exact hd.trans ((pullback_ae hp f).sub (pullback_ae hq f))

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ShiftedFieldVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {G : Ω → ℝ} {beta : ℝ}

lemma continuous_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Continuous (responseAttenuation theta) := by
  have ht := lipschitzWith_tanh_response.continuous
  exact (continuous_const.sub (ht.pow 2)).div
    (continuous_const.sub (continuous_const.mul (ht.pow 2)))
    (fun z => ne_of_gt (attenuation_denominator_pos hθ z))

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ShiftedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

lemma shiftedLossCoefficient_pos {theta beta : ℝ} (hθ : theta ^ 2 < 1) :
    0 < shiftedLossCoefficient theta beta := by
  apply div_pos (sub_pos.mpr hθ)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ThresholdArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma branching_pos {d : ℕ} (hd : 3 ≤ d) : 0 < (d : ℝ) - 1 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma threshold_sqrt_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < Real.sqrt ((d : ℝ) - 1) :=
  Real.sqrt_pos.2 (branching_pos hd)

lemma threshold_iff_branching_sq {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (htheta : 0 ≤ theta) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
  have hb := (branching_pos hd).le
  have hs := threshold_sqrt_pos hd
  calc
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
        theta * Real.sqrt ((d : ℝ) - 1) ≤ 1 := le_div_iff₀ hs
    _ ↔ (theta * Real.sqrt ((d : ℝ) - 1)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg htheta hs.le) (by norm_num)).symm
    _ ↔ ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hb, one_pow, mul_comm]

lemma tanh_threshold_iff_branching_sq {d : ℕ} {beta : ℝ}
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta) :
    Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * Real.tanh beta ^ 2 ≤ 1 :=
  threshold_iff_branching_sq hd (tanh_nonneg_of_beta_nonneg hbeta)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SideSignalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma sideSignalLossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < sideSignalLossCoefficient theta := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  exact mul_pos (mul_pos (shiftedLossCoefficient_pos hθsq) (sub_pos.mpr hθsq))
    (sq_pos_of_pos hθ0)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ComponentSignalAttenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

theorem lossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < lossCoefficient theta :=
  lt_min (div_pos (sideSignalLossCoefficient_pos hθ0 hθ1) (by norm_num)) (by norm_num)

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_NoisePathConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367

theorem half_path_cut_admissible {n m : ℕ} (hn : 8 ≤ n) (hm : n / 2 ≤ m) :
    let k := m / 2 - 1
    let L := m - m / 2
    k + 1 + L = m ∧
      (n : ℝ) / 8 - 1 ≤ (k + 1 : ℕ) ∧ (n : ℝ) / 8 ≤ (L : ℝ) := by
  dsimp only
  have hk : m / 2 - 1 + 1 = m / 2 := by omega
  rw [hk]
  refine ⟨by omega, ?_, ?_⟩
  · have hround : n ≤ 8 * (m / 2) + 8 := by omega
    have hr : (n : ℝ) ≤ 8 * (m / 2 : ℕ) + 8 := by exact_mod_cast hround
    linarith
  · have hround : n ≤ 8 * (m - m / 2) := by omega
    have hr : (n : ℝ) ≤ 8 * (m - m / 2 : ℕ) := by exact_mod_cast hround
    linarith

theorem criticalNoise_constants_positive {d : ℕ} {beta : ℝ}
    (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) :
    0 < criticalNoiseEta d beta ∧ 0 < criticalNoiseLengthConstant beta ∧
      1 < criticalNoiseTailBase d ∧ 0 < 1 / (2 * ((d : ℝ) - 1)) := by
  have hb1 : 1 < (d : ℝ) - 1 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hθ : 0 < Real.tanh beta := by
    by_contra h
    have hz := le_antisymm (not_lt.mp h) (tanh_nonneg_of_beta_nonneg hb)
    simp [hz] at hcritical
  have hγ := ComponentSignalAttenuation.lossCoefficient_pos hθ (Real.tanh_lt_one beta)
  refine ⟨lt_min (div_pos hγ (by norm_num))
    (div_pos (Real.log_pos hb1) (by norm_num)), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · exact Real.one_lt_rpow hb1 (by norm_num)
  · have : 0 < (d : ℝ) - 1 := zero_lt_one.trans hb1
    positivity

theorem criticalNoise_length_admissible {d n : ℕ} {beta ω : ℝ}
    (_hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : criticalNoiseLengthConstant beta / ω ≤ (n : ℝ)) :
    8 ≤ n ∧ 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) * (ω * ((n : ℝ) / 4)) := by
  have hθ : 0 < Real.tanh beta := by
    by_contra h
    have hz := le_antisymm (not_lt.mp h) (tanh_nonneg_of_beta_nonneg hb)
    simp [hz] at hcritical
  have hγ := ComponentSignalAttenuation.lossCoefficient_pos hθ (Real.tanh_lt_one beta)
  have hlarge := (div_le_iff₀ hω).mp hn
  have hlow : (8 : ℝ) ≤ criticalNoiseLengthConstant beta := le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hω1 (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  have hnR : (8 : ℝ) ≤ n := by nlinarith
  refine ⟨by exact_mod_cast hnR, ?_⟩
  have hfrac : 32 * Real.log 2 / ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) ≤
      (n : ℝ) * ω := (le_max_right _ _).trans hlarge
  have h := (div_le_iff₀ hγ).mp hfrac
  nlinarith

theorem criticalNoise_threshold_eq (d : ℕ) (beta ω : ℝ) (n : ℕ) :
    Real.exp (-(criticalNoiseEta d beta * ω) * ((n : ℝ) / 4)) =
      Real.exp (-((criticalNoiseEta d beta / 4) * ω) * n) := by congr 1; ring

theorem criticalNoise_tail_eq {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    Real.exp (-(((d : ℝ) - 1) ^ (((n : ℝ) / 4) / 4)) /
      (2 * ((d : ℝ) - 1))) =
      Real.exp (-(1 / (2 * ((d : ℝ) - 1))) * criticalNoiseTailBase d ^ n) := by
  have hb : 0 ≤ (d : ℝ) - 1 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hp : ((d : ℝ) - 1) ^ (((n : ℝ) / 4) / 4) = criticalNoiseTailBase d ^ n := by
    rw [show ((n : ℝ) / 4) / 4 = (1 / 16 : ℝ) * n by ring,
      Real.rpow_mul hb, Real.rpow_natCast]
    rfl
  rw [hp]
  congr 1
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_DependentWeight
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367
namespace DependentWeight

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

theorem integral_mul_le_of_exceptional_set
    {z g : Ω → ℝ} {s : Set Ω} {a M : ℝ}
    (hs : MeasurableSet s) (hz : Integrable z μ)
    (hzg : Integrable (fun x => z x * g x) μ)
    (ha : 0 ≤ a)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x)
    (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hg_good : ∀ᵐ x ∂μ, x ∉ s → g x ≤ a) :
    (∫ x, z x * g x ∂μ) ≤ a * (∫ x, z x ∂μ) + M * μ.real s := by
  have hind : Integrable (s.indicator (fun _ : Ω => M)) μ :=
    (integrable_const M).indicator hs
  have hpoint : (fun x => z x * g x) ≤ᵐ[μ]
      (fun x => a * z x + s.indicator (fun _ : Ω => M) x) := by
    filter_upwards [hz_nonneg, hz_bound, hg_bound, hg_good] with x hz0 hzM hg1 hga
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
      have hprod : z x * g x ≤ M :=
        (mul_le_mul_of_nonneg_left hg1 hz0).trans (by simpa using hzM)
      exact hprod.trans (le_add_of_nonneg_left (mul_nonneg ha hz0))
    · simp only [Set.indicator_of_notMem hxs, add_zero]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hga hxs) hz0
  calc
    (∫ x, z x * g x ∂μ) ≤
        ∫ x, a * z x + s.indicator (fun _ : Ω => M) x ∂μ :=
      integral_mono_ae hzg ((hz.const_mul a).add hind) hpoint
    _ = a * (∫ x, z x ∂μ) + M * μ.real s := by
      rw [integral_add (hz.const_mul a) hind, integral_const_mul,
        integral_indicator_const M hs]
      simp [smul_eq_mul, mul_comm]

theorem integral_mul_le_of_exceptional_probability
    {z g : Ω → ℝ} {s : Set Ω} {a M ε : ℝ}
    (hs : MeasurableSet s) (hz : Integrable z μ)
    (hzg : Integrable (fun x => z x * g x) μ)
    (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x)
    (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hg_good : ∀ᵐ x ∂μ, x ∉ s → g x ≤ a)
    (hprob : μ.real s ≤ ε) :
    (∫ x, z x * g x ∂μ) ≤ a * (∫ x, z x ∂μ) + M * ε := by
  exact (integral_mul_le_of_exceptional_set hs hz hzg ha hz_nonneg hz_bound
    hg_bound hg_good).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprob hM))

theorem integral_mul_le_of_tail_probability
    {z g : Ω → ℝ} {a M ε : ℝ}
    (hz : Integrable z μ) (hg : Measurable g)
    (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x)
    (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hprob : μ.real {x | a < g x} ≤ ε) :
    (∫ x, z x * g x ∂μ) ≤ a * (∫ x, z x ∂μ) + M * ε := by
  have hnorm : ∀ᵐ x ∂μ, ‖g x‖ ≤ (1 : ℝ) := by
    filter_upwards [hg_nonneg, hg_bound] with x hx0 hx1
    simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  refine integral_mul_le_of_exceptional_probability
    (measurableSet_lt measurable_const hg) hz
    (hz.mul_bdd hg.aestronglyMeasurable hnorm) ha hM
    hz_nonneg hz_bound hg_bound ?_ hprob
  exact Filter.Eventually.of_forall (fun x hx => le_of_not_gt hx)

end DependentWeight
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LocalColorAutomorphisms
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

lemma prefixColorList_on_subtree {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    prefixColorList stem p (stem ++ w) = stem ++ w.map p := by
  induction stem with
  | nil => rfl
  | cons a r ih => simp [prefixColorList, ih]

lemma prefixColorList_eq_of_length_le {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) (hw : w.length ≤ stem.length) :
    prefixColorList stem p w = w := by
  induction stem generalizing w with
  | nil =>
    have hw' : w = [] := List.length_eq_zero_iff.mp (by simpa using hw)
    simp [hw']
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w =>
      have hw' : w.length ≤ r.length := by simpa using hw
      by_cases h : a = b <;> simp [prefixColorList, h, ih w hw']

theorem prefixColorAut_fixes_ball {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) (hu : u.1.length ≤ stem.length) :
    (prefixColorAut stem p hp).toEquiv u = u := by
  apply Subtype.ext
  exact prefixColorList_eq_of_length_le stem p u.1 hu

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_WeightedOrbitAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.WeightedOrbitAverage

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_weight_mul_comp
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (weight F : Ω → ℝ) (hw : ∀ᵐ ω ∂μ, weight (T ω) = weight ω) :
    (∫ ω, weight ω * F (T ω) ∂μ) = ∫ ω, weight ω * F ω ∂μ := by
  calc
    (∫ ω, weight ω * F (T ω) ∂μ) =
        ∫ ω, weight (T ω) * F (T ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with ω hω
      rw [hω]
    _ = ∫ ω, weight ω * F ω ∂μ :=
      hT.integral_comp T.measurableEmbedding (fun ω => weight ω * F ω)

theorem integrable_weight_mul_comp
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (weight F : Ω → ℝ) (hw : ∀ᵐ ω ∂μ, weight (T ω) = weight ω)
    (hF : Integrable (fun ω => weight ω * F ω) μ) :
    Integrable (fun ω => weight ω * F (T ω)) μ := by
  apply ((hT.integrable_comp hF.aestronglyMeasurable).2 hF).congr
  filter_upwards [hw] with ω hω
  simp only [Function.comp_def, hω]

theorem integral_weight_mul_average [Fintype ι]
    (weight : Ω → ℝ) (F : ι → Ω → ℝ)
    (hF : ∀ i, Integrable (fun ω => weight ω * F i ω) μ) :
    (∫ ω, weight ω * average F ω ∂μ) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ ω, weight ω * F i ω ∂μ := by
  have heq : (fun ω => weight ω * average F ω) =
      fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, weight ω * F i ω := by
    funext ω
    simp only [average, ← Finset.mul_sum]
    ring
  rw [heq, integral_const_mul, integral_finsetSum _ (fun i _ => hF i)]

theorem integral_weight_mul_orbit_average [Fintype ι] [Nonempty ι]
    (T : ι → Ω ≃ᵐ Ω) (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (weight F : Ω → ℝ)
    (hw : ∀ i, ∀ᵐ ω ∂μ, weight (T i ω) = weight ω)
    (hF : Integrable (fun ω => weight ω * F ω) μ) :
    (∫ ω, weight ω * average (fun i ω => F (T i ω)) ω ∂μ) =
      ∫ ω, weight ω * F ω ∂μ := by
  rw [integral_weight_mul_average weight _
    (fun i => integrable_weight_mul_comp (T i) (hT i) weight F (hw i) hF)]
  simp only [integral_weight_mul_comp (T _) (hT _) weight F (hw _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end Problem367.WeightedOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_CopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem ae_observation_sub_bound_of_shared_progressive_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {m m' : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (hm' : IsStronglyProgressive G m')
    (hb : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ 1)
    (hb' : ∀ t, ∀ᵐ ω ∂P, |m' t ω| ≤ 1)
    {x x' w : Ω → ℝ} (t : ℝ≥0)
    (hx : ∀ᵐ ω ∂P, x ω = w ω + nnrealTimePrimitive m t ω)
    (hx' : ∀ᵐ ω ∂P, x' ω = w ω + nnrealTimePrimitive m' t ω) :
    ∀ᵐ ω ∂P, |x ω - x' ω| ≤ 2 * (t : ℝ) := by
  have hL := ae_lipschitzWith_nnrealTimePrimitive hm (C := 1) hb
  have hL' := ae_lipschitzWith_nnrealTimePrimitive hm' (C := 1) hb'
  filter_upwards [hL, hL', hx, hx'] with ω hω hω' hxω hxω'
  have h1 : |nnrealTimePrimitive m t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω.dist_le_mul t 0
  have h2 : |nnrealTimePrimitive m' t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω'.dist_le_mul t 0
  rw [hxω, hxω']
  have heq : (w ω + nnrealTimePrimitive m t ω) -
      (w ω + nnrealTimePrimitive m' t ω) =
      nnrealTimePrimitive m t ω - nnrealTimePrimitive m' t ω := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

theorem HasFreeIsingLaw.gibbsField_bound_of_observation_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {X : Ω → TreeVertex d → ℝ}
    (hX : IdentDistrib X (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))) :
    ∀ᵐ ω ∂P, |Real.artanh (infiniteGibbsSpinMean beta v (X ω)) - X ω v| ≤
      (d : ℝ) * beta := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hmeas := (ha.comp (measurable_infiniteGibbsSpinMean beta v)).sub
    (measurable_pi_apply v)
  apply hX.symm.ae_snd (measurableSet_le hmeas.abs measurable_const)
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.gaussian_posterior_field_bound hbeta t v] with p heq hp
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [heq]
  exact hp.2

theorem HasFreeIsingLaw.gibbsField_copy_bound_of_shared_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    ∀ᵐ ω ∂P,
      |Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))| ≤
          2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hobs := ae_observation_sub_bound_of_shared_progressive_innovation hm hm'
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _))
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _)) t hx hx'
  have hl := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw
  have hr := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw'
  filter_upwards [hobs, hl, hr] with ω hobsω hlω hrω
  have htriangle := abs_sub_le
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)))
    (X v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  have htriangle' := abs_sub_le (X v t ω) (X' v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  rw [abs_sub_comm (X' v t ω)] at htriangle'
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingConditionalCopyBounds

open PlantedSymmetry IsingObservationInnovation WienerSampler

theorem progressive_leftObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.1 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_fst.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.1 v).continuous)

theorem progressive_rightObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.2 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_snd.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.2 v).continuous)

section Copies

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
variable {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]

theorem ae_innovationMap_copies (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      innovationMap beta q.2.1 = q.1 ∧ innovationMap beta q.2.2 = q.1 := by
  have hgraph : ∀ᵐ q : Paths d × Paths d ∂rho ⊗ₘ eta,
      innovationMap beta q.2 = q.1 := by
    rw [hjoint, graphLaw]
    apply (ae_map_iff
      ((measurable_innovationMap beta).prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun
        ((measurable_innovationMap beta).comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have hleft := (measurePreserving_conditionalCopy_fst rho eta).quasiMeasurePreserving.ae hgraph
  have hright := (measurePreserving_conditionalCopy_snd rho eta).quasiMeasurePreserving.ae hgraph
  filter_upwards [hleft, hright] with q hl hr
  exact ⟨hl, hr⟩

theorem identDistrib_observation_copies
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) :
    IdentDistrib (fun q : CopySpace d => fun i => q.2.1 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    IdentDistrib (fun q : CopySpace d => fun i => q.2.2 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨hl, hr⟩ := measurePreserving_observation_copies hjoint
  have heval := hasLaw_observationLaw_eval μ t
  have hobs : HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  exact ⟨(heval.comp hl.hasLaw).identDistrib hobs,
    (heval.comp hr.hasLaw).identDistrib hobs⟩

theorem ae_all_innovation_identities (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta), ∀ v t,
      q.2.1 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q ∧
      q.2.2 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q := by
  filter_upwards [ae_innovationMap_copies hjoint] with q hq
  intro v t
  have hl := congrArg (fun x : Paths d => x v t) hq.1
  have hr := congrArg (fun x : Paths d => x v t) hq.2
  change q.2.1 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q = q.1 v t at hl
  change q.2.2 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q = q.1 v t at hr
  constructor <;> linarith

theorem ae_fieldDifference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ q ∂rho ⊗ₘ (eta ×ₖ eta),
      |fieldDifference beta v t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  obtain ⟨hl, hr⟩ := identDistrib_observation_copies hμ hjoint t
  have hx := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  simpa only [fieldDifference, IsingObservationInnovation.posterior] using
    hμ.gibbsField_copy_bound_of_shared_innovation hbeta
      progressive_leftObservation progressive_rightObservation t v hl hr hx hx'

end Copies

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyStationarity
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyStationarity

open IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem posterior_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun x => posterior beta v t (relabel g x)) =ᵐ[observationLaw μ]
      posterior beta (g.toEquiv.symm v) t := by
  have hm (w : TreeVertex d) : Measurable (posterior beta w t) :=
    (measurable_infiniteGibbsSpinMean beta w).comp
      (Measurable.of_eval (fun i => measurable_evaluation i t))
  apply (ae_map_iff measurable_uniformObservation.aemeasurable
    (measurableSet_eq_fun ((hm v).comp (measurable_relabel g))
      (hm (g.toEquiv.symm v)))).mpr
  have hmB (s : ℝ≥0) : Measurable (fun u => WienerSampler.sample u s) :=
    WienerSampler.measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  have h := ArrayPosteriorStationarity.posterior_version_relabel_ae hμ uniform01
    (fun s u => WienerSampler.sample u s) hmB
    (fun s w => IsingInnovation.posterior_eq_condExp hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB s w) g t v
  exact h

omit [IsProbabilityMeasure μ] in
theorem field_array_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) (t : ℝ≥0) :
    (fun x v => field beta v t (relabel g x)) =ᵐ[observationLaw μ]
      (fun x => relabel g (fun v => field beta v t x)) := by
  filter_upwards [ae_all_iff.mpr (fun v => posterior_relabel_ae hμ g t v)] with x hx
  funext v
  exact congrArg Real.artanh (hx v)

theorem measurable_sitePair (beta : ℝ) (t : ℝ≥0) :
    Measurable (sitePair (d := d) beta t) := by
  have hm (v : TreeVertex d) : Measurable (field beta v t) := by
    have hp : Measurable (posterior beta v t) :=
      (measurable_infiniteGibbsSpinMean beta v).comp
        (Measurable.of_eval (fun i => measurable_evaluation i t))
    unfold field Real.artanh
    exact ((measurable_const.add hp).div (measurable_const.sub hp)).sqrt.log
  exact (Measurable.of_eval (fun v => (hm v).comp (measurable_fst.comp measurable_snd))).prodMk
    (Measurable.of_eval (fun v => (hm v).comp (measurable_snd.comp measurable_snd)))

end Problem367.IsingCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordAction
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

theorem wordAut_root {d : ℕ} (w : List (Fin d))
    (hw : w.IsChain (· ≠ ·)) :
    (wordAut w).toEquiv ⟨[], List.IsChain.nil⟩ = ⟨w, hw⟩ := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change prefixFlip c ((wordAut w).toEquiv ⟨[], List.IsChain.nil⟩) = _
    rw [ih hw.tail]
    apply Subtype.ext
    cases w with
    | nil => rfl
    | cons a w =>
      simp [prefixFlip, prefixFlipWord, (List.isChain_cons_cons.mp hw).1]

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredEdgeLifts
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.pathValue_succ _root_.OAI.Problem367.ColoredPathAverage.pathValue_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped InnerProductSpace
namespace Problem367.ColoredEdgeLifts
variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

section Adjoint
variable [CompleteSpace E]

theorem tailLift_adjoint_apply (hd : 0 < d) (y : EdgeSpace d E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint y =
      (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • ∑ i, y i := by
  apply ext_inner_left 𝕜
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, tailLift_apply, inner_smul_left, inner_smul_right, inner_sum,
    RCLike.conj_ofReal, Finset.mul_sum]

theorem forwardOperator_apply (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (r : ℝ) (y : EdgeSpace d E) (i : Fin d) :
    forwardOperator hd S r y i = (r : 𝕜) • ∑ j ∈ Finset.univ.erase i, S i (y j) := by
  change (((d : ℝ) * r : ℝ) : 𝕜) •
    (headLift hd S ((tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint y) i) -
      (r : 𝕜) • reversal S y i = _
  rw [headLift_apply, tailLift_adjoint_apply, map_smul, reversal_apply]
  simp only [smul_smul]
  have hscalar : (((d : ℝ) * r : ℝ) : 𝕜) *
      ((((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) * (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜)) = (r : 𝕜) := by
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    norm_cast
    rw [← pow_two, inv_pow, Real.sq_sqrt hdreal.le]
    field_simp
  rw [hscalar, ← smul_sub, map_sum]
  congr 1
  exact (Finset.sum_erase_eq_sub (f := fun j => S i (y j)) (Finset.mem_univ i)).symm

end Adjoint

end Problem367.ColoredEdgeLifts

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredEdgeDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.ColoredEdgeLifts
open NonbacktrackingComplement

lemma degree_decay_parameters {d : ℕ} (hd : 3 ≤ d) :
    let q := (Real.sqrt ((d : ℝ) - 1))⁻¹
    0 < q ∧ q < 1 ∧ q ^ 2 = ((d : ℝ) - 1)⁻¹ ∧
      1 + q ^ 2 = (d : ℝ) * ((d : ℝ) - 1)⁻¹ ∧
      vertexRate q = 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  dsimp only
  have hb := branching_pos hd
  have hs := threshold_sqrt_pos hd
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 := Real.sq_sqrt hb.le
  have hs1 : 1 < Real.sqrt ((d : ℝ) - 1) := by nlinarith
  have hq2 : (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ 2 = ((d : ℝ) - 1)⁻¹ := by
    rw [inv_pow, hs2]
  refine ⟨inv_pos.mpr hs, (inv_lt_one₀ hs).mpr hs1, hq2, ?_, ?_⟩
  · rw [hq2]
    field_simp
    ring
  · unfold vertexRate
    rw [hq2]
    field_simp
    nlinarith

end Problem367.ColoredEdgeLifts

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem cavityObservable_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun x => cavityObservable hbeta t v w (relabel g x)) =ᵐ[observationLaw μ]
      cavityObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [field_array_relabel_ae hμ g t] with x hx
  unfold cavityObservable
  rw [hx]
  rfl

theorem observableDifference_ae {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    (observableDifference (beta := beta) hf : Lp ℝ 2 (copies beta μ)) =ᵐ[copies beta μ]
      (fun q => f q.2.1 - f q.2.2) := by
  obtain ⟨hp, hq⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have h := CopyDifference.operator_ae hp hq (hf.toLp f)
  filter_upwards [h, hp.quasiMeasurePreserving.ae hf.coeFn_toLp,
    hq.quasiMeasurePreserving.ae hf.coeFn_toLp] with q hq' hl hr
  exact hq'.trans (congrArg₂ (fun a b : ℝ => a - b) hl hr)

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyGeodesicCorrelations
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem cavityLogObservable_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun x => cavityLogObservable hbeta t v w (relabel g x)) =ᵐ[observationLaw μ]
      cavityLogObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [cavityObservable_relabel_ae hμ hbeta g t v w] with x hx
  exact congrArg (fun z => Real.log (responseAttenuation (Real.tanh beta) z)) hx

theorem cavityLogDifference_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun q => cavityLogDifference hbeta t v w (copyRelabel g q)) =ᵐ[copies beta μ]
      cavityLogDifference hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae
    (cavityLogObservable_relabel_ae hμ hbeta g t v w),
    hr.quasiMeasurePreserving.ae
    (cavityLogObservable_relabel_ae hμ hbeta g t v w)] with q hq hq'
  exact congrArg₂ (fun x y : ℝ => x - y) hq hq'

theorem memLp_cavityLogDifference
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (cavityLogDifference hbeta t v w) 2 (copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  exact ((memLp_cavityLogObservable hμ hbeta t v w).comp_measurePreserving hl).sub
    ((memLp_cavityLogObservable hμ hbeta t v w).comp_measurePreserving hr)

theorem cavityLogVector_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) =ᵐ[copies beta μ]
      cavityLogDifference hbeta t v w :=
  observableDifference_ae (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)

theorem inner_cavityLogVector_eq_integral
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w u z : TreeVertex d) :
    inner ℝ (cavityLogVector hμ hbeta t v w) (cavityLogVector hμ hbeta t u z) =
      ∫ q, cavityLogDifference hbeta t v w q * cavityLogDifference hbeta t u z q
        ∂copies beta μ := by
  change inner ℝ (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ))
    (cavityLogVector hμ hbeta t u z : Lp ℝ 2 (copies beta μ)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cavityLogVector_ae hμ hbeta t v w,
    cavityLogVector_ae hμ hbeta t u z] with q hq hq'
  simp [hq, hq', mul_comm]

theorem inner_cavityLogVector_map
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w u z : TreeVertex d) :
    inner ℝ (cavityLogVector hμ hbeta t (g.toEquiv v) (g.toEquiv w))
      (cavityLogVector hμ hbeta t (g.toEquiv u) (g.toEquiv z)) =
    inner ℝ (cavityLogVector hμ hbeta t v w) (cavityLogVector hμ hbeta t u z) := by
  rw [inner_cavityLogVector_eq_integral, inner_cavityLogVector_eq_integral]
  have hmem := (memLp_cavityLogDifference hμ hbeta t v w).integrable_mul
    (memLp_cavityLogDifference hμ hbeta t u z)
  calc
    _ = ∫ q, cavityLogDifference hbeta t v w (copyRelabel g.symm q) *
        cavityLogDifference hbeta t u z (copyRelabel g.symm q) ∂copies beta μ := by
      apply integral_congr_ae
      filter_upwards [cavityLogDifference_relabel_ae hμ hbeta g.symm t v w,
        cavityLogDifference_relabel_ae hμ hbeta g.symm t u z] with q hq hq'
      exact (congrArg₂ (fun x y : ℝ => x * y) hq hq').symm
    _ = _ := (measurePreserving_copies_relabel hμ g.symm).hasLaw.integral_comp
      hmem.aestronglyMeasurable

theorem differenceReflection_cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (c : Fin d) (t : ℝ≥0) (v w : TreeVertex d) :
    differenceReflection hμ c (cavityLogVector hμ hbeta t v w) =
      cavityLogVector hμ hbeta t (prefixFlip c v) (prefixFlip c w) := by
  apply Subtype.ext
  change koopmanL2 (copyRelabel (prefixTreeAut c))
    (measurePreserving_copies_relabel hμ (prefixTreeAut c))
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) = _
  apply Lp.ext
  have hp := measurePreserving_copies_relabel hμ (prefixTreeAut c)
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) hp,
    hp.quasiMeasurePreserving.ae (cavityLogVector_ae hμ hbeta t v w),
    cavityLogDifference_relabel_ae hμ hbeta (prefixTreeAut c) t v w,
    cavityLogVector_ae hμ hbeta t (prefixFlip c v) (prefixFlip c w)]
    with q hq hq' hq'' hq'''
  exact hq.trans (hq'.trans (hq''.trans hq'''.symm))

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedTransitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem exists_treeAut_map_common_stem {d : ℕ} (n : ℕ) :
    ∀ (stem s t : List (Fin d)) (_ : s.length = n) (_ : t.length = n)
      (hs : (stem ++ s).IsChain (· ≠ ·)) (_ : (stem ++ t).IsChain (· ≠ ·)),
    ∃ g : TreeAut d,
      (g.toEquiv ⟨stem ++ s, hs⟩).1 = stem ++ t ∧
      ∀ u : TreeVertex d, u.1.length ≤ stem.length → g.toEquiv u = u := by
  induction n with
  | zero =>
    intro stem s t hslen htlen hs ht
    have hs0 : s = [] := List.length_eq_zero_iff.mp hslen
    have ht0 : t = [] := List.length_eq_zero_iff.mp htlen
    subst s
    subst t
    exact ⟨TreeAut.refl d, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro stem s t hslen htlen hs ht
    cases s with
    | nil => simp at hslen
    | cons a s =>
      cases t with
      | nil => simp at htlen
      | cons b t =>
        have hslen' : s.length = n := by simpa using hslen
        have htlen' : t.length = n := by simpa using htlen
        let p : Equiv.Perm (Fin d) := Equiv.swap a b
        have hp : ∀ c ∈ stem.getLast?, p c = c := by
          intro c hc
          apply Equiv.swap_apply_of_ne_of_ne
          · exact (List.isChain_append.mp hs).2.2 c hc a (by simp)
          · exact (List.isChain_append.mp ht).2.2 c hc b (by simp)
        let g₁ := prefixColorAut stem p hp
        have hmid : ((stem ++ [b]) ++ s.map p).IsChain (· ≠ ·) := by
          have h := (g₁.toEquiv ⟨stem ++ a :: s, hs⟩).2
          change (prefixColorList stem p (stem ++ a :: s)).IsChain (· ≠ ·) at h
          simpa [prefixColorList_on_subtree, p, List.append_assoc] using h
        have htarget : ((stem ++ [b]) ++ t).IsChain (· ≠ ·) := by
          simpa only [List.append_assoc, List.singleton_append] using ht
        obtain ⟨g₂, hg₂, hfix₂⟩ := ih (stem ++ [b]) (s.map p) t
          (by simpa using hslen') htlen' hmid htarget
        refine ⟨g₁.trans g₂, ?_, ?_⟩
        · have hg₁ : g₁.toEquiv ⟨stem ++ a :: s, hs⟩ =
              ⟨(stem ++ [b]) ++ s.map p, hmid⟩ := by
            apply Subtype.ext
            simp [g₁, prefixColorList_on_subtree, p, List.append_assoc]
          change (g₂.toEquiv (g₁.toEquiv ⟨stem ++ a :: s, hs⟩)).1 = _
          rw [hg₁, hg₂]
          simp [List.append_assoc]
        · intro u hu
          change g₂.toEquiv (g₁.toEquiv u) = u
          have hfix₁ : g₁.toEquiv u = u := prefixColorAut_fixes_ball stem p hp u hu
          rw [hfix₁]
          apply hfix₂
          simp only [List.length_append, List.length_singleton]
          omega

theorem exists_rootFixing_treeAut_map {d : ℕ} (u v : TreeVertex d)
    (hlen : u.1.length = v.1.length) :
    ∃ g : TreeAut d, g.toEquiv u = v ∧
      g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩ := by
  obtain ⟨g, hmap, hfix⟩ := exists_treeAut_map_common_stem u.1.length
    [] u.1 v.1 rfl hlen.symm u.2 v.2
  refine ⟨g, ?_, hfix ⟨[], List.IsChain.nil⟩ (by simp)⟩
  apply Subtype.ext
  exact hmap

theorem exists_treeAut_map_adjacent_pair {d : ℕ} {u v x y : TreeVertex d}
    (huv : treeAdj u v) (hxy : treeAdj x y) :
    ∃ g : TreeAut d, g.toEquiv u = x ∧ g.toEquiv v = y := by
  let root : TreeVertex d := ⟨[], List.IsChain.nil⟩
  have root_neighbor_length : ∀ w : TreeVertex d, treeAdj root w → w.1.length = 1 := by
    intro w hw
    rcases hw with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hl := congrArg List.length hc
      simpa [root] using hl
    · have hl := congrArg List.length hc
      simp [root] at hl
  obtain ⟨g, hgu⟩ := exists_treeAut_to_root u
  obtain ⟨h, hhx⟩ := exists_treeAut_to_root x
  have hgv : (g.toEquiv v).1.length = 1 := by
    apply root_neighbor_length
    dsimp only [root]
    rw [← hgu]
    exact (g.map_adj u v).2 huv
  have hhy : (h.toEquiv y).1.length = 1 := by
    apply root_neighbor_length
    dsimp only [root]
    rw [← hhx]
    exact (h.map_adj x y).2 hxy
  obtain ⟨k, hkv, hkroot⟩ := exists_rootFixing_treeAut_map (g.toEquiv v) (h.toEquiv y)
    (hgv.trans hhy.symm)
  refine ⟨(g.trans k).trans h.symm, ?_, ?_⟩
  · change h.toEquiv.symm (k.toEquiv (g.toEquiv u)) = x
    rw [hgu, hkroot, ← hhx]
    exact h.toEquiv.symm_apply_apply x
  · change h.toEquiv.symm (k.toEquiv (g.toEquiv v)) = y
    rw [hkv]
    exact h.toEquiv.symm_apply_apply y

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyEdgeVariance
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.pathValue_succ _root_.OAI.Problem367.ColoredPathAverage.pathValue_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor ColoredEdgeLifts

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem norm_cavityLogVector_sq_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    ‖cavityLogVector hμ hbeta t v w‖ ^ 2 =
      ∫ q, (cavityLogDifference hbeta t v w q) ^ 2 ∂copies beta μ := by
  rw [← real_inner_self_eq_norm_sq, inner_cavityLogVector_eq_integral]
  simp only [pow_two]

theorem norm_cavityLogVector_sq_eq_of_adj
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {u v x y : TreeVertex d} (huv : treeAdj u v) (hxy : treeAdj x y) :
    ‖cavityLogVector hμ hbeta t u v‖ ^ 2 =
      ‖cavityLogVector hμ hbeta t x y‖ ^ 2 := by
  obtain ⟨g, hgu, hgv⟩ := exists_treeAut_map_adjacent_pair huv hxy
  have h := inner_cavityLogVector_map hμ hbeta g t u v u v
  rw [hgu, hgv] at h
  simpa only [real_inner_self_eq_norm_sq] using h.symm

theorem norm_cavityLogEdgeVector_sq_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {u v : TreeVertex d} (huv : treeAdj u v) :
    ‖cavityLogEdgeVector hμ hbeta t‖ ^ 2 = (d : ℝ) *
      ∫ q, (cavityLogDifference hbeta t u v q) ^ 2 ∂copies beta μ := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ = ∑ _c : Fin d, ‖cavityLogVector hμ hbeta t u v‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      change ‖cavityLogVector hμ hbeta t TreeEscape.root
        (prefixFlip c TreeEscape.root)‖ ^ 2 = _
      exact norm_cavityLogVector_sq_eq_of_adj hμ hbeta t (Or.inl ⟨c, rfl⟩) huv
    _ = (d : ℝ) * ‖cavityLogVector hμ hbeta t u v‖ ^ 2 := by simp
    _ = _ := by rw [norm_cavityLogVector_sq_eq]

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathAverage
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.card_path _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Problem367.ColoredPathAverage

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

theorem forwardOperator_pow_apply [CompleteSpace E]
    (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (r : ℝ)
    (n : ℕ) (y : ColoredEdgeLifts.EdgeSpace d E) (i : Fin d) :
    (ColoredEdgeLifts.forwardOperator hd S r ^ n) y i =
      (r : 𝕜) ^ n • ∑ p : Path d n i, pathValue S y p := by
  induction n generalizing i with
  | zero =>
      change y i = (r : 𝕜) ^ 0 • ∑ _ : PUnit, y i
      simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp,
        ColoredEdgeLifts.forwardOperator_apply]
      simp_rw [ih, map_smul, map_sum]
      rw [← Finset.smul_sum, smul_smul, ← pow_succ']
      congr 1
      rw [show (∑ p : Path d (n + 1) i, pathValue S y p) =
          ∑ j : {j : Fin d // j ≠ i}, ∑ p : Path d n j.1, S i (pathValue S y p) from
        Fintype.sum_sigma _]
      exact Finset.sum_subtype (Finset.univ.erase i) (by simp) _

end Problem367.ColoredPathAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathEndpoints
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.card_path _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem prefixFlip_reduced_cons {d : ℕ} (c : Fin d) (w : List (Fin d))
    (h : (c :: w).IsChain (· ≠ ·)) :
    prefixFlip c ⟨w, h.tail⟩ = ⟨c :: w, h⟩ := by
  apply Subtype.ext
  cases w with
  | nil => rfl
  | cons a w =>
    simp [prefixFlip, prefixFlipWord, (List.isChain_cons_cons.mp h).1]

theorem prefixFlip_reduced_dropLast {d : ℕ} (c : Fin d) (w : List (Fin d))
    (h : (c :: w).IsChain (· ≠ ·)) (hw : w ≠ []) :
    prefixFlip c ⟨w.dropLast, h.tail.dropLast⟩ =
      ⟨(c :: w).dropLast, h.dropLast⟩ := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    cases w with
    | nil => rfl
    | cons b w =>
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord,
        (List.isChain_cons_cons.mp h).1]

namespace ColoredPathAverage

@[simp] theorem headVertex_succ {d n : ℕ} {i : Fin d} (p : Path d (n + 1) i) :
    headVertex p = prefixFlip i (headVertex p.2) := by
  symm
  exact prefixFlip_reduced_cons i (colors p.2) (colors_isChain p)

@[simp] theorem tailVertex_succ {d n : ℕ} {i : Fin d} (p : Path d (n + 1) i) :
    tailVertex p = prefixFlip i (tailVertex p.2) := by
  symm
  apply prefixFlip_reduced_dropLast i (colors p.2) (colors_isChain p)
  intro h
  have := colors_length p.2
  simp [h] at this

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem pathValue_eq_edgeVector {d : ℕ}
    (S : Fin d → E ≃ₗᵢ[𝕜] E) (A : TreeVertex d → TreeVertex d → E)
    (y : ColoredEdgeLifts.EdgeSpace d E)
    (hy : ∀ i, y i = A ⟨[], List.IsChain.nil⟩
      ⟨[i], List.IsChain.singleton i⟩)
    (hS : ∀ c v w, S c (A v w) = A (prefixFlip c v) (prefixFlip c w))
    {n : ℕ} {i : Fin d} (p : Path d n i) :
    pathValue S y p = A (tailVertex p) (headVertex p) := by
  induction n generalizing i with
  | zero => exact hy i
  | succ n ih =>
    rw [pathValue_succ, ih p.2, hS, tailVertex_succ, headVertex_succ]

end ColoredPathAverage

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyPathVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open ColoredPathAverage IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem pathValue_cavityLogEdgeVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {n : ℕ} {i : Fin d} (p : Path d n i) :
    pathValue (differenceReflection hμ) (cavityLogEdgeVector hμ hbeta t) p =
      cavityLogVector hμ hbeta t (tailVertex p) (headVertex p) := by
  apply pathValue_eq_edgeVector
  · intro i
    rfl
  · intro c v w
    exact differenceReflection_cavityLogVector hμ hbeta c t v w

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Problem367.ColoredPathAverage
open ColoredEdgeLifts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] {d : ℕ}

theorem inner_forwardOperator_pow_component_eq (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E)
    (i : Fin d) (c : ℝ)
    (h : ∀ p : Path d n i, inner ℝ (f i) (pathValue S f p) = c) :
    inner ℝ (f i)
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f i) = c := by
  rw [forwardOperator_pow_apply, inner_smul_right, inner_sum]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_path]
  have hd1 : 1 ≤ d := by omega
  have hb : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [Nat.cast_pow, Nat.cast_sub hd1, Nat.cast_one, ← mul_assoc,
    ← mul_pow, inv_mul_cancel₀ hb, one_pow, one_mul]

theorem inner_forwardOperator_pow_eq_card_mul (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c) :
    inner ℝ f
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f) =
        (d : ℝ) * c := by
  rw [PiLp.inner_apply]
  simp only [inner_forwardOperator_pow_component_eq hd S n f _ c (h _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem abs_pathCoefficient_le (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c B : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c)
    (hB : |inner ℝ f
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f)| ≤
        (d : ℝ) * B) : |c| ≤ B := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [inner_forwardOperator_pow_eq_card_mul hd S n f c h,
    abs_mul, abs_of_pos hdreal] at hB
  exact (mul_le_mul_iff_right₀ hdreal).mp hB

theorem abs_pathCoefficient_le_norm_pow (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c V : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c)
    (hsize : ‖f‖ ^ 2 ≤ (d : ℝ) * V) :
    |c| ≤ ‖forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n‖ * V := by
  apply abs_pathCoefficient_le hd S n f c _ h
  let A := forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n
  change |inner ℝ f (A f)| ≤ (d : ℝ) * (‖A‖ * V)
  calc
    |inner ℝ f (A f)| ≤ ‖f‖ * ‖A f‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f (A f)
    _ ≤ ‖f‖ * (‖A‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm f) (norm_nonneg f)
    _ = ‖A‖ * ‖f‖ ^ 2 := by ring
    _ ≤ ‖A‖ * ((d : ℝ) * V) :=
      mul_le_mul_of_nonneg_left hsize (norm_nonneg A)
    _ = _ := by ring

end Problem367.ColoredPathAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathPrefix
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.headVertex_succ _root_.OAI.Problem367.ColoredPathAverage.tailVertex_succ _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

namespace TreeAut

private theorem length_le_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) : (g.toEquiv v).1.length ≤ v.1.length := by
  suffices h : ∀ n (v : TreeVertex d), v.1.length = n →
      (g.toEquiv v).1.length ≤ n from h _ v rfl
  intro n
  induction n with
  | zero =>
      intro v hv
      have heq : v = ConnectedHull.root d :=
        Subtype.ext (List.length_eq_zero_iff.mp hv)
      rw [heq, hg]
      exact Nat.zero_le _
  | succ n ih =>
      intro v hv
      have hne : v.1 ≠ [] := by
        intro heq
        simp [heq] at hv
      have hp : (parentVertex v).1.length = n := by
        rw [parentVertex_length, hv]
        omega
      have hbound := ih (parentVertex v) hp
      have hadj := treeAdj_length
        ((g.map_adj _ _).mpr (treeAdj_parentVertex hne))
      omega

theorem length_eq_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) : (g.toEquiv v).1.length = v.1.length := by
  have hsymm : g.symm.toEquiv (ConnectedHull.root d) = ConnectedHull.root d := by
    change g.toEquiv.symm (ConnectedHull.root d) = ConnectedHull.root d
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact hg.symm
  apply Nat.le_antisymm (length_le_of_root_eq g hg v)
  simpa only [TreeAut.symm, Equiv.symm_apply_apply] using
    length_le_of_root_eq g.symm hsymm (g.toEquiv v)

theorem map_takeVertex_of_length_preserving {d : ℕ} (g : TreeAut d)
    (hg : ∀ v, (g.toEquiv v).1.length = v.1.length)
    (v : TreeVertex d) (n : ℕ) :
    g.toEquiv (ConnectedHull.takeVertex v n) =
      ConnectedHull.takeVertex (g.toEquiv v) n := by
  by_cases hn : n ≤ v.1.length
  · induction hn using Nat.decreasingInduction with
    | self =>
        rw [ConnectedHull.prefix_length, ← hg v, ConnectedHull.prefix_length]
    | of_succ k hk ih =>
        apply treeAdj_lower_unique
          ((g.map_adj _ _).mpr (ConnectedHull.prefix_adj v hk))
        · rw [ih]
          apply ConnectedHull.prefix_adj
          rw [hg]
          exact hk
        · rw [hg, hg]
          simp only [ConnectedHull.takeVertex, List.length_take]
          omega
        · rw [hg]
          simp only [ConnectedHull.takeVertex, List.length_take, hg]
          omega
  · have hv : ConnectedHull.takeVertex v n = v := by
      apply Subtype.ext
      exact (List.take_eq_self_iff v.1).mpr (by omega)
    have hgv : ConnectedHull.takeVertex (g.toEquiv v) n = g.toEquiv v := by
      apply Subtype.ext
      apply (List.take_eq_self_iff (g.toEquiv v).1).mpr
      rw [hg]
      omega
    rw [hv, hgv]

theorem map_takeVertex_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) (n : ℕ) :
    g.toEquiv (ConnectedHull.takeVertex v n) =
      ConnectedHull.takeVertex (g.toEquiv v) n :=
  map_takeVertex_of_length_preserving g (length_eq_of_root_eq g hg) v n

end TreeAut

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyFixedPathBound
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor
open ColoredEdgeLifts ColoredPathAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem inner_rooted_cavityLogVector_eq_of_length_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (a b : TreeVertex d) (hlen : a.1.length = b.1.length) (n : ℕ) :
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex a 1))
      (cavityLogVector hμ hbeta t (takeVertex a n) a) =
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex b 1))
      (cavityLogVector hμ hbeta t (takeVertex b n) b) := by
  obtain ⟨g, hga, hgroot⟩ := exists_rootFixing_treeAut_map a b hlen
  have hgroot' : g.toEquiv (root d) = root d := hgroot
  have hfirst := g.map_takeVertex_of_root_eq hgroot' a 1
  have hlast := g.map_takeVertex_of_root_eq hgroot' a n
  rw [hga] at hfirst hlast
  have h := inner_cavityLogVector_map hμ hbeta g t (root d) (takeVertex a 1)
    (takeVertex a n) a
  rw [hgroot', hfirst, hlast, hga] at h
  exact h.symm

theorem inner_pathValue_eq_rooted_cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {n : ℕ} {i : Fin d} (p : Path d n i)
    (v : TreeVertex d) (hlen : v.1.length = n + 1) :
    inner ℝ (cavityLogEdgeVector hμ hbeta t i)
      (pathValue (differenceReflection hμ) (cavityLogEdgeVector hμ hbeta t) p) =
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
      (cavityLogVector hμ hbeta t (takeVertex v n) v) := by
  rw [pathValue_cavityLogEdgeVector]
  change inner ℝ (cavityLogVector hμ hbeta t (root d) (prefixFlip i TreeEscape.root))
    (cavityLogVector hμ hbeta t (tailVertex p) (headVertex p)) = _
  have hfirst : takeVertex (headVertex p) 1 = prefixFlip i TreeEscape.root := by
    cases n <;> apply Subtype.ext <;> rfl
  have htail : tailVertex p = takeVertex (headVertex p) n := by
    apply Subtype.ext
    change (colors p).dropLast = (colors p).take n
    rw [List.dropLast_eq_take, colors_length]
    simp
  rw [← hfirst, htail]
  apply inner_rooted_cavityLogVector_eq_of_length_eq hμ hbeta t _ v _ n
  simpa only [headVertex, colors_length] using hlen.symm

theorem abs_inner_rooted_cavityLogVector_le_norm_pow
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 2 ≤ d) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (n : ℕ) (v : TreeVertex d) (hlen : v.1.length = n + 1)
    {u w : TreeVertex d} (huw : treeAdj u w) :
    |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
      (cavityLogVector hμ hbeta t (takeVertex v n) v)| ≤
      ‖forwardOperator (by omega : 0 < d) (differenceReflection hμ)
        ((d : ℝ) - 1)⁻¹ ^ n‖ *
        ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  apply abs_pathCoefficient_le_norm_pow hd (differenceReflection hμ) n
    (cavityLogEdgeVector hμ hbeta t)
  · intro i p
    exact inner_pathValue_eq_rooted_cavityLogVector hμ hbeta t p v hlen
  · exact (norm_cavityLogEdgeVector_sq_eq hμ hbeta t huw).le

theorem exists_rooted_cavityLogVector_correlation_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ≥0) (n : ℕ) (v : TreeVertex d),
      v.1.length = n + 1 → ∀ (u w : TreeVertex d), treeAdj u w →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
        (cavityLogVector hμ hbeta t (takeVertex v n) v)| ≤
        (K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n) *
          ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  obtain ⟨K, hK, hpow⟩ := forwardOperator_pow_bound hμ hd hbeta hthreshold
  refine ⟨K, hK, ?_⟩
  intro t n v hlen u w huw
  exact (abs_inner_rooted_cavityLogVector_le_norm_pow hμ (by omega) hbeta t n v
    hlen huw).trans (mul_le_mul_of_nonneg_right (hpow n)
      (integral_nonneg (fun q => sq_nonneg _)))

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationComparison
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

theorem kernel_graphLaw :
    ((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ =
      IsingConditionalCopyBounds.graphLaw beta μ :=
  ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367

theorem pathCorrelationKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (k : ℤ) :
    0 ≤ pathCorrelationKernel q k := by
  unfold pathCorrelationKernel
  positivity

theorem summable_pathCorrelationKernel {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (pathCorrelationKernel q) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hlin : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have hgeom : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hnat : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    simpa [add_mul] using hlin.add hgeom
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [pathCorrelationKernel] using hnat

theorem tsum_pathCorrelationKernel {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' k, pathCorrelationKernel q k) = 2 / (1 - q) ^ 2 - 1 := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hnat : HasSum (fun n : ℕ => ((n : ℝ) + 1) * q ^ n)
      (1 / (1 - q) ^ 2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hn
  have hpos : HasSum (fun n : ℕ => pathCorrelationKernel q (n : ℤ))
      (1 / (1 - q) ^ 2) := by
    simpa [pathCorrelationKernel] using hnat
  have hneg : HasSum (fun n : ℕ => pathCorrelationKernel q (-(n : ℤ)))
      (1 / (1 - q) ^ 2) := by
    simpa [pathCorrelationKernel] using hnat
  have h := (hpos.of_nat_of_neg hneg).tsum_eq
  simpa [pathCorrelationKernel, ← two_mul, div_eq_mul_inv] using h

open MeasureTheory

theorem integral_sum_sq_eq_sum_pair_moments
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ := by
  have hp : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => f i ω * f j ω) μ := by
    intro i hi j hj
    exact (hf i hi).integrable_mul (hf j hj)
  calc
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, f i ω * f j ω ∂μ := by
      congr 1
      funext ω
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ := by
      rw [integral_finsetSum s (fun i hi => integrable_finsetSum s (hp i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (hp i hi)

theorem integral_sum_sq_le_card_mul_of_pair_rows
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ) {a : ι → ι → ℝ} {K : ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, (∫ ω, f i ω * f j ω ∂μ) ≤ a i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, a i j ≤ K) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) ≤ (s.card : ℝ) * K := by
  rw [integral_sum_sq_eq_sum_pair_moments s f hf]
  calc
    ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ
        ≤ ∑ i ∈ s, ∑ j ∈ s, a i j :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ ≤ ∑ _i ∈ s, K := Finset.sum_le_sum hrow
    _ = (s.card : ℝ) * K := by simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_IndexedPathVariance
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Problem367

theorem sum_indexed_translate_le_tsum {ι : Type*}
    (s : Finset ι) (z : ι → ℤ) (hz : Set.InjOn z (s : Set ι))
    (i : ℤ) {c : ℤ → ℝ} (hc : ∀ k, 0 ≤ c k) (hsum : Summable c) :
    ∑ j ∈ s, c (z j - i) ≤ ∑' k, c k := by
  classical
  calc
    ∑ j ∈ s, c (z j - i) = ∑ k ∈ s.image (fun j => z j - i), c k := by
      symm
      apply Finset.sum_image
      intro a ha b hb hab
      apply hz ha hb
      exact sub_left_injective hab
    _ ≤ ∑' k, c k := Summable.sum_le_tsum _ (fun k _ => hc k) hsum

theorem integral_sum_sq_le_geometric_bound_of_injective_index
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (z : ι → ℤ) (hz : Set.InjOn z (s : Set ι))
    (f : ι → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      |∫ ω, f i ω * f j ω ∂μ| ≤ S * pathCorrelationKernel q (z j - z i)) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) ≤
      (s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have h := integral_sum_sq_le_card_mul_of_pair_rows s f hf
    (fun i hi j hj => (le_abs_self _).trans (hpair i hi j hj))
    (K := S * ∑' k, pathCorrelationKernel q k) (fun i _ => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_indexed_translate_le_tsum s z hz (z i)
        (pathCorrelationKernel_nonneg hq0) (summable_pathCorrelationKernel hq0 hq1)) hS)
  simpa only [tsum_pathCorrelationKernel hq0 hq1, mul_assoc] using h

theorem integral_sum_fin_sq_le_geometric_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (f : Fin n → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hpair : ∀ i j, |∫ ω, f i ω * f j ω ∂μ| ≤
      S * pathCorrelationKernel q ((j : ℤ) - (i : ℤ))) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (n : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have hinj : Function.Injective (fun i : Fin n => (i : ℤ)) := by
    intro i j hij
    exact Fin.ext (Int.ofNat.inj hij)
  simpa using integral_sum_sq_le_geometric_bound_of_injective_index
    Finset.univ (fun i : Fin n => (i : ℤ)) hinj.injOn f hq0 hq1 hS
    (fun i _ => hf i) (fun i _ j _ => hpair i j)

theorem integral_sum_fin_sq_le_ordered_geometric_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (f : Fin n → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hpair : ∀ i j, i ≤ j → |∫ ω, f i ω * f j ω ∂μ| ≤
      S * (((j.val - i.val : ℕ) : ℝ) + 1) * q ^ (j.val - i.val)) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (n : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  apply integral_sum_fin_sq_le_geometric_pair_bound f hq0 hq1 hS hf
  intro i j
  by_cases hij : i ≤ j
  · simpa only [pathCorrelationKernel,
      Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair i j hij
  · have hji : j ≤ i := le_of_not_ge hij
    have heq : (∫ ω, f i ω * f j ω ∂μ) = ∫ ω, f j ω * f i ω ∂μ := by
      congr 1
      funext ω
      exact mul_comm _ _
    rw [heq]
    simpa only [pathCorrelationKernel,
      Int.natAbs_natCast_sub_natCast_of_le hji, mul_assoc] using hpair j i hji

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathRerooting
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.headVertex_succ _root_.OAI.Problem367.ColoredPathAverage.tailVertex_succ _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem stripPrefixAut_of_append {d : ℕ} (stem : List (Fin d))
    (v : TreeVertex d) (s : List (Fin d)) (hv : v.1 = stem ++ s) :
    ((stripPrefixAut stem).toEquiv v).1 = s := by
  induction stem generalizing v with
  | nil =>
    change v.1 = s
    simpa only [List.nil_append] using hv
  | cons a stem ih =>
    change ((stripPrefixAut stem).toEquiv (prefixFlip a v)).1 = s
    apply ih
    simp [prefixFlip, prefixFlipWord, hv]

theorem stripPrefixAut_eq_drop {d : ℕ} (stem : List (Fin d))
    (v : TreeVertex d) (hpre : stem <+: v.1) :
    ((stripPrefixAut stem).toEquiv v).1 = v.1.drop stem.length := by
  obtain ⟨s, hs⟩ := hpre
  rw [stripPrefixAut_of_append stem v s hs.symm, ← hs]
  simp

theorem stripPrefixAut_takeVertex {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hi : i ≤ v.1.length) (hij : i ≤ j) :
    (stripPrefixAut (v.1.take i)).toEquiv (ConnectedHull.takeVertex v j) =
      ConnectedHull.takeVertex (dropVertex v i) (j - i) := by
  apply Subtype.ext
  have hpre : v.1.take i <+: (ConnectedHull.takeVertex v j).1 := by
    change v.1.take i <+: v.1.take j
    simpa only [List.take_take, Nat.min_eq_left hij] using
      List.take_prefix i (v.1.take j)
  rw [stripPrefixAut_eq_drop _ _ hpre]
  simp only [ConnectedHull.takeVertex, dropVertex, List.length_take,
    Nat.min_eq_left hi, List.drop_take]

theorem exists_treeAut_reroot_subsegment {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      ∀ k : ℕ, i ≤ k → k ≤ j + 1 →
        g.toEquiv (ConnectedHull.takeVertex v k) =
          ConnectedHull.takeVertex w (k - i) := by
  let w := ConnectedHull.takeVertex (dropVertex v i) (j - i + 1)
  refine ⟨w, stripPrefixAut (v.1.take i), ?_, ?_⟩
  · have hle : j - i + 1 ≤ v.1.length - i := by omega
    simp only [w, ConnectedHull.takeVertex, dropVertex, List.length_take,
      List.length_drop, Nat.min_eq_left hle]
  · intro k hik hkj
    rw [stripPrefixAut_takeVertex v (by omega) hik]
    apply Subtype.ext
    change (v.1.drop i).take (k - i) =
      ((v.1.drop i).take (j - i + 1)).take (k - i)
    rw [List.take_take, Nat.min_eq_left (by omega : k - i ≤ j - i + 1)]

theorem exists_treeAut_reroot_edge_pair {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      g.toEquiv (ConnectedHull.takeVertex v i) = ConnectedHull.root d ∧
      g.toEquiv (ConnectedHull.takeVertex v (i + 1)) = ConnectedHull.takeVertex w 1 ∧
      g.toEquiv (ConnectedHull.takeVertex v j) = ConnectedHull.takeVertex w (j - i) ∧
      g.toEquiv (ConnectedHull.takeVertex v (j + 1)) = w := by
  obtain ⟨w, g, hlen, hmap⟩ := exists_treeAut_reroot_subsegment v hij hj
  refine ⟨w, g, hlen, ?_, ?_, hmap j hij (by omega), ?_⟩
  · simpa using hmap i le_rfl (by omega)
  · simpa using hmap (i + 1) (by omega) (by omega)
  · have h := hmap (j + 1) (by omega) le_rfl
    have hk : j + 1 - i = w.1.length := by omega
    rw [hk, ConnectedHull.prefix_length] at h
    exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordCancellation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.TreeKoopman

theorem wordAut_append_apply {d : ℕ} (u w : List (Fin d)) (v : TreeVertex d) :
    (wordAut (u ++ w)).toEquiv v =
      (wordAut u).toEquiv ((wordAut w).toEquiv v) := by
  induction u with
  | nil => rfl
  | cons c u ih =>
    change prefixFlip c ((wordAut (u ++ w)).toEquiv v) =
      prefixFlip c ((wordAut u).toEquiv ((wordAut w).toEquiv v))
    rw [ih]

theorem wordAut_reverse_left_apply {d : ℕ} (w : List (Fin d)) (v : TreeVertex d) :
    (wordAut w.reverse).toEquiv ((wordAut w).toEquiv v) = v := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [List.reverse_cons, wordAut_append_apply]
    change (wordAut w.reverse).toEquiv
      (prefixFlip c (prefixFlip c ((wordAut w).toEquiv v))) = v
    rw [prefixFlip_twice, ih]

theorem wordAut_reverse_right_apply {d : ℕ} (w : List (Fin d)) (v : TreeVertex d) :
    (wordAut w).toEquiv ((wordAut w.reverse).toEquiv v) = v := by
  simpa only [List.reverse_reverse] using wordAut_reverse_left_apply w.reverse v

theorem wordAut_reverse_apply_eq_symm {d : ℕ} (w : List (Fin d)) (v : TreeVertex d) :
    (wordAut w.reverse).toEquiv v = (wordAut w).toEquiv.symm v := by
  apply (wordAut w).toEquiv.injective
  rw [wordAut_reverse_right_apply, Equiv.apply_symm_apply]

theorem wordAut_append_reverse_suffix {d : ℕ} (u w : TreeVertex d) :
    (wordAut (u.1 ++ w.1)).toEquiv (reverseVertex w) = u := by
  rw [wordAut_append_apply]
  have hw : reverseVertex w =
      (wordAut w.1.reverse).toEquiv ⟨[], List.IsChain.nil⟩ :=
    (wordAut_root w.1.reverse (reverseVertex w).2).symm
  rw [hw, wordAut_reverse_right_apply, wordAut_root u.1 u.2]

theorem wordAut_apply_reverse_prefix {d : ℕ} (v : TreeVertex d) (k : ℕ) :
    (wordAut v.1).toEquiv (ConnectedHull.takeVertex (reverseVertex v) k) =
      ConnectedHull.takeVertex v (v.1.length - k) := by
  let u : TreeVertex d := ConnectedHull.takeVertex v (v.1.length - k)
  let w : TreeVertex d := ⟨v.1.drop (v.1.length - k), v.2.drop _⟩
  have hsplit : u.1 ++ w.1 = v.1 := List.take_append_drop _ _
  have hrev : ConnectedHull.takeVertex (reverseVertex v) k = reverseVertex w := by
    apply Subtype.ext
    exact List.take_reverse
  calc
    (wordAut v.1).toEquiv (ConnectedHull.takeVertex (reverseVertex v) k) =
        (wordAut (u.1 ++ w.1)).toEquiv (reverseVertex w) := by rw [hsplit, hrev]
    _ = u := wordAut_append_reverse_suffix u w

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathReverseRerooting
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.headVertex_succ _root_.OAI.Problem367.ColoredPathAverage.tailVertex_succ _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

open ConnectedHull

namespace TreeKoopman

theorem wordAut_reverse_apply_prefix {d : ℕ} (v : TreeVertex d) (k : ℕ) :
    (wordAut v.1.reverse).toEquiv (takeVertex v k) =
      takeVertex (reverseVertex v) (v.1.length - k) := by
  have h := wordAut_apply_reverse_prefix (reverseVertex v) k
  rw [reverseVertex_twice] at h
  simpa only [reverseVertex, List.length_reverse] using h

end TreeKoopman

theorem exists_treeAut_reverse_subsegment {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      ∀ k : ℕ, i ≤ k → k ≤ j + 1 →
        g.toEquiv (takeVertex v k) = takeVertex w (j + 1 - k) := by
  obtain ⟨u, g, hlen, hmap⟩ := exists_treeAut_reroot_subsegment v hij hj
  let w := TreeKoopman.reverseVertex u
  let h := TreeKoopman.wordAut u.1.reverse
  refine ⟨w, g.trans h, ?_, ?_⟩
  · simpa only [w, TreeKoopman.reverseVertex, List.length_reverse] using hlen
  · intro k hik hkj
    change h.toEquiv (g.toEquiv (takeVertex v k)) = _
    rw [hmap k hik hkj]
    change (TreeKoopman.wordAut u.1.reverse).toEquiv (takeVertex u (k - i)) = _
    rw [TreeKoopman.wordAut_reverse_apply_prefix]
    have hindex : u.1.length - (k - i) = j + 1 - k := by omega
    rw [hindex]

theorem exists_treeAut_reroot_reverse_edge_pair {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      g.toEquiv (takeVertex v (j + 1)) = root d ∧
      g.toEquiv (takeVertex v j) = takeVertex w 1 ∧
      g.toEquiv (takeVertex v (i + 1)) = takeVertex w (j - i) ∧
      g.toEquiv (takeVertex v i) = w := by
  obtain ⟨w, g, hlen, hmap⟩ := exists_treeAut_reverse_subsegment v hij hj
  refine ⟨w, g, hlen, ?_, ?_, ?_, ?_⟩
  · simpa using hmap (j + 1) (by omega) le_rfl
  · simpa using hmap j hij (by omega)
  · have h := hmap (i + 1) (by omega) (by omega)
    have hindex : j + 1 - (i + 1) = j - i := by omega
    simpa only [hindex] using h
  · have h := hmap i le_rfl (by omega)
    have hindex : j + 1 - i = w.1.length := by omega
    rw [hindex, prefix_length] at h
    exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyPathVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor
open ConnectedHull
open scoped NNReal

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

private theorem inner_path_pair_bound_of_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ}
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (v : TreeVertex d) {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    |inner ℝ (cavityLogVector hμ hbeta t (takeVertex v i) (takeVertex v (i + 1)))
      (cavityLogVector hμ hbeta t (takeVertex v j) (takeVertex v (j + 1)))| ≤
        (K * S) * pathCorrelationKernel q ((j : ℤ) - (i : ℤ)) := by
  obtain ⟨w, g, hlen, hi, hi1, hj0, hj1⟩ :=
    exists_treeAut_reroot_edge_pair v hij hj
  have hm := inner_cavityLogVector_map hμ hbeta g t
    (takeVertex v i) (takeVertex v (i + 1))
    (takeVertex v j) (takeVertex v (j + 1))
  rw [hi, hi1, hj0, hj1] at hm
  rw [← hm]
  have hlag : ((j : ℤ) - (i : ℤ)).natAbs = j - i := by
    rw [← Int.natCast_sub hij]
    rfl
  calc
    _ ≤ K * (((j - i : ℕ) : ℝ) + 1) * q ^ (j - i) * S := hroot _ w hlen
    _ = _ := by rw [pathCorrelationKernel, hlag]; ring

private theorem inner_reverse_path_pair_bound_of_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ}
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (v : TreeVertex d) {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    |inner ℝ (cavityLogVector hμ hbeta t (takeVertex v (i + 1)) (takeVertex v i))
      (cavityLogVector hμ hbeta t (takeVertex v (j + 1)) (takeVertex v j))| ≤
        (K * S) * pathCorrelationKernel q ((j : ℤ) - (i : ℤ)) := by
  obtain ⟨w, g, hlen, hi, hi1, hj0, hj1⟩ :=
    exists_treeAut_reroot_reverse_edge_pair v hij hj
  have hm := inner_cavityLogVector_map hμ hbeta g t
    (takeVertex v (j + 1)) (takeVertex v j)
    (takeVertex v (i + 1)) (takeVertex v i)
  rw [hi, hi1, hj0, hj1] at hm
  rw [real_inner_comm, ← hm]
  have hlag : ((j : ℤ) - (i : ℤ)).natAbs = j - i := by
    rw [← Int.natCast_sub hij]
    rfl
  calc
    _ ≤ K * (((j - i : ℕ) : ℝ) + 1) * q ^ (j - i) * S := hroot _ w hlen
    _ = _ := by rw [pathCorrelationKernel, hlag]; ring

private theorem integral_image_path_sq_bound_of_root_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ} (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hS : 0 ≤ S)
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (g : TreeAut d) (v : TreeVertex d) :
    (∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))) ω) ^ 2
        ∂copies beta μ) ≤
      (K * (2 / (1 - q) ^ 2 - 1)) * (v.1.length : ℝ) * S := by
  have h := integral_sum_fin_sq_le_ordered_geometric_pair_bound
    (fun i => cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))))
    hq0 hq1 (mul_nonneg hK hS)
    (fun i => memLp_cavityLogDifference hμ hbeta t _ _)
    (fun i j hij => by
      rw [← inner_cavityLogVector_eq_integral hμ hbeta t,
        inner_cavityLogVector_map]
      have hpair := inner_path_pair_bound_of_le hμ hbeta t hroot v hij j.isLt
      simpa only [pathCorrelationKernel,
        Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair)
  calc
    _ ≤ (v.1.length : ℝ) * (K * S) * (2 / (1 - q) ^ 2 - 1) := h
    _ = _ := by ring

private theorem integral_image_reverse_path_sq_bound_of_root_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ} (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hS : 0 ≤ S)
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (g : TreeAut d) (v : TreeVertex d) :
    (∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)) ω) ^ 2
        ∂copies beta μ) ≤
      (K * (2 / (1 - q) ^ 2 - 1)) * (v.1.length : ℝ) * S := by
  have h := integral_sum_fin_sq_le_ordered_geometric_pair_bound
    (fun i => cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)))
    hq0 hq1 (mul_nonneg hK hS)
    (fun i => memLp_cavityLogDifference hμ hbeta t _ _)
    (fun i j hij => by
      rw [← inner_cavityLogVector_eq_integral hμ hbeta t,
        inner_cavityLogVector_map]
      have hpair := inner_reverse_path_pair_bound_of_le hμ hbeta t hroot v hij j.isLt
      simpa only [pathCorrelationKernel,
        Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair)
  calc
    _ ≤ (v.1.length : ℝ) * (K * S) * (2 / (1 - q) ^ 2 - 1) := h
    _ = _ := by ring

theorem exists_cavityLog_path_variance_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w →
      ∀ (g : TreeAut d) (v : TreeVertex d),
      ((∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
          (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))) ω) ^ 2
            ∂copies beta μ) ≤
        C * (v.1.length : ℝ) *
          ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ) ∧
      ((∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
          (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)) ω) ^ 2
            ∂copies beta μ) ≤
        C * (v.1.length : ℝ) *
          ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_rooted_cavityLogVector_correlation_bound hμ hd hbeta hthreshold
  let q := (Real.sqrt ((d : ℝ) - 1))⁻¹
  have hq0 : 0 ≤ q := (ColoredEdgeLifts.degree_decay_parameters hd).1.le
  have hq1 : q < 1 := (ColoredEdgeLifts.degree_decay_parameters hd).2.1
  have hmass : 0 ≤ 2 / (1 - q) ^ 2 - 1 := by
    rw [← tsum_pathCorrelationKernel hq0 hq1]
    exact tsum_nonneg (pathCorrelationKernel_nonneg hq0)
  refine ⟨K * (2 / (1 - q) ^ 2 - 1), mul_nonneg hK hmass, ?_⟩
  intro t u w huw g v
  have hS : 0 ≤ ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hroot := fun n x hx => hbound t n x hx u w huw
  exact ⟨integral_image_path_sq_bound_of_root_bound hμ hbeta t hK hq0 hq1 hS
      hroot g v,
    integral_image_reverse_path_sq_bound_of_root_bound hμ hbeta t hK hq0 hq1 hS
      hroot g v⟩

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyPathBounds
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.headVertex_succ _root_.OAI.Problem367.ColoredPathAverage.tailVertex_succ _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCopyPathBounds

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem edgeLogBound_nonneg (hbeta : 0 ≤ beta) (T : ℝ≥0) :
    0 ≤ edgeLogBound d beta T := by
  have hden : 0 < 1 - Real.tanh beta := sub_pos.mpr (Real.tanh_lt_one beta)
  unfold edgeLogBound
  positivity

theorem measurable_edgeLogDifference (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (v w : TreeVertex d) : Measurable (edgeLogDifference hbeta t v w) := by
  have h0 := tanh_nonneg_of_beta_nonneg hbeta
  have h1 := Real.tanh_lt_one beta
  have hs : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  have hl := (lipschitzWith_log_responseAttenuation hs).continuous.measurable
  have hc := CavityArray.measurable_field_apply h0 h1 v w
  exact (hl.comp (hc.comp (measurable_fst.comp (measurable_sitePair beta t)))).sub
    (hl.comp (hc.comp (measurable_snd.comp (measurable_sitePair beta t))))

theorem ae_all_siteDifference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) :
    ∀ᵐ q ∂copies beta μ, ∀ v : TreeVertex d,
      |(sitePair beta t q).1 v - (sitePair beta t q).2 v| ≤
        2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
  apply ae_all_iff.mpr
  intro v
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have h := IsingConditionalCopyBounds.ae_fieldDifference_bound hμ hbeta
    kernel_graphLaw t v
  filter_upwards [h] with q hq
  have ht' : (t : ℝ) ≤ (T : ℝ) := ht
  exact hq.trans (by linarith)

theorem ae_edgeLogDifference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (v w : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ,
      |edgeLogDifference hbeta t v w q| ≤ edgeLogBound d beta T := by
  have h0 := tanh_nonneg_of_beta_nonneg hbeta
  have h1 := Real.tanh_lt_one beta
  have hs : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  filter_upwards [ae_all_siteDifference_bound hμ hbeta ht] with q hq
  have hc := CavityArray.field_sub_abs_le h0 h1 v w (hq v) (hq w)
  have hl := (lipschitzWith_log_responseAttenuation hs).dist_le_mul
    (CavityArray.field h0 h1 (sitePair beta t q).1 v w)
    (CavityArray.field h0 h1 (sitePair beta t q).2 v w)
  apply (show |edgeLogDifference hbeta t v w q| ≤
    2 * |CavityArray.field h0 h1 (sitePair beta t q).1 v w -
      CavityArray.field h0 h1 (sitePair beta t q).2 v w| from by
        simpa only [edgeLogDifference, Real.dist_eq, NNReal.coe_ofNat] using hl).trans
  exact mul_le_mul_of_nonneg_left hc (by norm_num)

theorem measurable_pathLogDifference {ι : Type*}
    (hbeta : 0 ≤ beta) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) :
    Measurable (pathLogDifference hbeta t s e) :=
  Finset.measurable_fun_sum s (fun i _ =>
    measurable_edgeLogDifference hbeta t (e i).1 (e i).2)

theorem ae_pathLogDifference_bound {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) :
    ∀ᵐ q ∂copies beta μ,
      |pathLogDifference hbeta t s e q| ≤ (s.card : ℝ) * edgeLogBound d beta T := by
  classical
  have hall : ∀ᵐ q ∂copies beta μ, ∀ i ∈ s,
      |edgeLogDifference hbeta t (e i).1 (e i).2 q| ≤ edgeLogBound d beta T :=
    (ae_ball_iff s.finite_toSet.countable).mpr (fun i _ =>
      ae_edgeLogDifference_bound hμ hbeta ht (e i).1 (e i).2)
  filter_upwards [hall] with q hq
  calc
    |pathLogDifference hbeta t s e q| ≤
        ∑ i ∈ s, |edgeLogDifference hbeta t (e i).1 (e i).2 q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, edgeLogBound d beta T := Finset.sum_le_sum hq
    _ = (s.card : ℝ) * edgeLogBound d beta T := by simp

theorem ae_pathLogDifference_sq_bound {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) :
    ∀ᵐ q ∂copies beta μ,
      pathLogDifference hbeta t s e q ^ 2 ≤
        (s.card : ℝ) ^ 2 * edgeLogBound d beta T ^ 2 := by
  filter_upwards [ae_pathLogDifference_bound hμ hbeta ht s e] with q hq
  have hb : 0 ≤ (s.card : ℝ) * edgeLogBound d beta T :=
    mul_nonneg (Nat.cast_nonneg _) (edgeLogBound_nonneg hbeta T)
  simpa only [sq_abs, mul_pow] using (sq_le_sq₀ (abs_nonneg _) hb).mpr hq

theorem memLp_pathLogDifference {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    (p : ℝ≥0∞) : MemLp (pathLogDifference hbeta t s e) p (copies beta μ) := by
  apply MemLp.of_bound (measurable_pathLogDifference hbeta t s e).aestronglyMeasurable
    ((s.card : ℝ) * edgeLogBound d beta t)
  simpa only [Real.norm_eq_abs] using ae_pathLogDifference_bound hμ hbeta le_rfl s e

theorem integrable_pathLogDifference_sq {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d) :
    Integrable (fun q => pathLogDifference hbeta t s e q ^ 2) (copies beta μ) :=
  (memLp_pathLogDifference hμ hbeta t s e 2).integrable_sq

end Problem367.IsingCopyPathBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyPathWeightNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyPathBounds
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem edgeLogDifference_eq_cavityLogDifference
    (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d) :
    edgeLogDifference hbeta t v w =
      IsingCopySpectral.cavityLogDifference hbeta t v w := rfl

theorem edgeLogDifference_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun q => edgeLogDifference hbeta t v w (copyRelabel g q)) =ᵐ[copies beta μ]
      edgeLogDifference hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) :=
  IsingCopySpectral.cavityLogDifference_relabel_ae hμ hbeta g t v w

theorem pathLogDifference_relabel_ae {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) :
    (fun q => pathLogDifference hbeta t s e (copyRelabel g q)) =ᵐ[copies beta μ]
      pathLogDifference hbeta t s
        (fun i => (g.toEquiv.symm (e i).1, g.toEquiv.symm (e i).2)) := by
  have hall := (ae_ball_iff s.finite_toSet.countable).mpr
    (fun i (_hi : i ∈ s) => edgeLogDifference_relabel_ae hμ hbeta g t (e i).1 (e i).2)
  filter_upwards [hall] with q hq
  exact Finset.sum_congr rfl (fun i hi => hq i hi)

theorem pathLogDifference_relabel_eq_ae {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d)
    (hfix : ∀ i ∈ s, g.toEquiv (e i).1 = (e i).1 ∧
      g.toEquiv (e i).2 = (e i).2) :
    (fun q => pathLogDifference hbeta t s e (copyRelabel g q)) =ᵐ[copies beta μ]
      pathLogDifference hbeta t s e := by
  filter_upwards [pathLogDifference_relabel_ae hμ hbeta g t s e] with q hq
  apply hq.trans
  apply Finset.sum_congr rfl
  intro i hi
  have hleft : g.toEquiv.symm (e i).1 = (e i).1 := by
    simpa only [(hfix i hi).1] using g.toEquiv.symm_apply_apply (e i).1
  have hright : g.toEquiv.symm (e i).2 = (e i).2 := by
    simpa only [(hfix i hi).2] using g.toEquiv.symm_apply_apply (e i).2
  simp only [hleft, hright]

theorem pathLogDifference_sq_relabel_eq_ae {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d)
    (hfix : ∀ i ∈ s, g.toEquiv (e i).1 = (e i).1 ∧
      g.toEquiv (e i).2 = (e i).2) :
    (fun q => pathLogDifference hbeta t s e (copyRelabel g q) ^ 2) =ᵐ[copies beta μ]
      (fun q => pathLogDifference hbeta t s e q ^ 2) :=
  (pathLogDifference_relabel_eq_ae hμ hbeta g t s e hfix).fun_comp (fun x : ℝ => x ^ 2)

end Problem367.IsingCopyPathBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyWeightedCut
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyWeightedCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds

theorem measurable_observationCopy {d : ℕ} (left : Bool) :
    Measurable (observationCopy (d := d) left) := by
  cases left
  · exact measurable_snd.comp measurable_snd
  · exact measurable_fst.comp measurable_snd

theorem measurePreserving_observationCopy {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ] (left : Bool) :
    MeasurePreserving (observationCopy left) (copies beta μ) (observationLaw μ) := by
  obtain ⟨hl, hr⟩ := IsingCopyStationarity.measurePreserving_observations
    (beta := beta) (μ := μ)
  cases left
  · exact hr
  · exact hl

end Problem367.IsingCopyWeightedCut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_OrbitAverage
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.TreeOrbitAverage

theorem exists_extension_map {d : ℕ} {stem : List (Fin d)} {n : ℕ}
    (s t : Extension stem n) :
    ∃ g : TreeAut d, g.toEquiv (endpoint s) = endpoint t ∧ FixesStemBall stem g := by
  obtain ⟨g, hmap, hfix⟩ := exists_treeAut_map_common_stem n stem s.1 t.1
    s.2.1 t.2.1 s.2.2 t.2.2
  exact ⟨g, Subtype.ext hmap, hfix⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_weight_mul_extension_average
    {d : ℕ} {stem : List (Fin d)} {n : ℕ} (s₀ : Extension stem n)
    (act : TreeAut d → Ω ≃ᵐ Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (weight : Ω → ℝ) (F : TreeVertex d → Ω → ℝ)
    (hw : ∀ g, FixesStemBall stem g → ∀ᵐ ω ∂μ, weight (act g ω) = weight ω)
    (hcov : ∀ g, FixesStemBall stem g → ∀ v, ∀ᵐ ω ∂μ,
      F v (act g ω) = F (g.toEquiv v) ω)
    (hF : Integrable (fun ω => weight ω * F (endpoint s₀) ω) μ) :
    (∫ ω, weight ω * F (endpoint s₀) ω ∂μ) =
      ∫ ω, weight ω * WeightedOrbitAverage.average
        (fun s : Extension stem n => F (endpoint s)) ω ∂μ := by
  classical
  let : Nonempty (Extension stem n) := ⟨s₀⟩
  choose g hg hfix using fun s : Extension stem n => exists_extension_map s₀ s
  have hcov' : ∀ s : Extension stem n, ∀ᵐ ω ∂μ,
      F (endpoint s₀) (act (g s) ω) = F (endpoint s) ω := by
    intro s
    simpa only [hg s] using hcov (g s) (hfix s) (endpoint s₀)
  calc
    (∫ ω, weight ω * F (endpoint s₀) ω ∂μ) =
        ∫ ω, weight ω * WeightedOrbitAverage.average
          (fun s : Extension stem n => fun ω => F (endpoint s₀) (act (g s) ω)) ω ∂μ :=
      (WeightedOrbitAverage.integral_weight_mul_orbit_average
        (fun s => act (g s)) (fun s => hact (g s)) weight (F (endpoint s₀))
        (fun s => hw (g s) (hfix s)) hF).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hcov'] with ω hω
      congr 1
      unfold WeightedOrbitAverage.average
      congr 1
      exact Finset.sum_congr rfl (fun s _ => hω s)

end Problem367.TreeOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyOrbitAverage
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.IsingCopyOrbitAverage

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem measurePreserving_copyAction
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) :
    MeasurePreserving (copyAction g) (copies beta μ) (copies beta μ) :=
  IsingCopyStationarity.measurePreserving_copies_relabel hμ g.symm

end Problem367.IsingCopyOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_LogWeightedOrbitCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal BigOperators

namespace Problem367.IsingLogWeightedOrbitCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open IsingCopyPathBounds IsingCopyWeightedCut IsingCopyOrbitAverage
open IsingRootAttenuation IsingRootWeightedCut TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem pathLogDifference_sq_copyAction_invariant {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    {stem : List (Fin d)}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length)
    (g : TreeAut d) (hg : FixesStemBall stem g) :
    ∀ᵐ q ∂copies beta μ,
      pathLogDifference hbeta t s e (copyAction g q) ^ 2 =
        pathLogDifference hbeta t s e q ^ 2 := by
  have hfix (v : TreeVertex d) (hv : v.1.length ≤ stem.length) :
      g.symm.toEquiv v = v := by
    change g.toEquiv.symm v = v
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hg v hv]
  exact pathLogDifference_sq_relabel_eq_ae hμ hbeta g.symm t s e
    (fun i hi => ⟨hfix _ (hstem i hi).1, hfix _ (hstem i hi).2⟩)

end Problem367.IsingLogWeightedOrbitCut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds ConnectedHull

theorem measurable_attenuation {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    Measurable (attenuation hb t inward v) := by
  unfold attenuation
  exact Finset.measurable_prod _ (fun i _ =>
    (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
      (measurable_cavityObservable hb t _ _))

theorem attenuation_mem_Icc {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (x : Paths d) :
    0 ≤ attenuation hb t inward v x ∧ attenuation hb t inward v x ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ =>
      (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
  · exact Finset.prod_le_one
      (fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
      (fun i _ => responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedPathWeights
attribute [-simp] _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.TreeOrbitAverage.suffixVertex_length
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity IsingCopyPathBounds IsingCopyWeightedCut
open IsingCopyOrbitAverage IsingLogWeightedOrbitCut TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem edge_map (inward : Bool) (v : TreeVertex d) (i : ℕ)
    (g : TreeAut d) (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d) :
    edge inward (g.toEquiv v) i =
      (g.toEquiv (edge inward v i).1, g.toEquiv (edge inward v i).2) := by
  cases inward <;> simp only [edge, Bool.false_eq_true, ↓reduceIte]
  all_goals rw [g.map_takeVertex_of_root_eq hg, g.map_takeVertex_of_root_eq hg]

omit [IsProbabilityMeasure μ] in
theorem attenuation_relabel_ae [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (g : TreeAut d) (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    (fun x => attenuation hb t inward v (relabel g.symm x)) =ᵐ[observationLaw μ]
      attenuation hb t inward (g.toEquiv v) := by
  have he (i : ℕ) := cavityObservable_relabel_ae hμ hb g.symm t
    (edge inward v i).1 (edge inward v i).2
  filter_upwards [ae_all_iff.mpr he] with x hx
  unfold attenuation
  rw [g.length_eq_of_root_eq hg v]
  apply Finset.prod_congr rfl
  intro i hi
  rw [edge_map inward v i g hg]
  exact congrArg (responseAttenuation (Real.tanh beta)) (hx i)

theorem measurable_extensionAverage (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (stem : List (Fin d)) (n : ℕ) :
    Measurable (extensionAverage hb t inward stem n) := by
  unfold extensionAverage WeightedOrbitAverage.average
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun s _ =>
    (measurable_attenuation hb t inward (endpoint s)).pow_const 2)

theorem extensionAverage_mem_Icc (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) {stem : List (Fin d)} {n : ℕ}
    (s₀ : Extension stem n) (x : Paths d) :
    0 ≤ extensionAverage hb t inward stem n x ∧
      extensionAverage hb t inward stem n x ≤ 1 := by
  classical
  let : Nonempty (Extension stem n) := ⟨s₀⟩
  have hcard : (Fintype.card (Extension stem n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hbnd (s : Extension stem n) : attenuation hb t inward (endpoint s) x ^ 2 ≤ 1 :=
    pow_le_one₀ (attenuation_mem_Icc hb t inward (endpoint s) x).1
      (attenuation_mem_Icc hb t inward (endpoint s) x).2
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun s _ => sq_nonneg _)
  · have hs : (∑ s : Extension stem n, attenuation hb t inward (endpoint s) x ^ 2) ≤
        (Fintype.card (Extension stem n) : ℝ) := by
      simpa using (Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbnd s))
    exact (mul_le_mul_of_nonneg_left hs
      (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq (inv_mul_cancel₀ hcard)

theorem integral_log_weight_mul_extension_average {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    (left inward : Bool) {stem : List (Fin d)} {n : ℕ}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length) (s₀ : Extension stem n) :
    (∫ q, pathLogDifference hb t s e q ^ 2 *
      attenuation hb t inward (endpoint s₀) (observationCopy left q) ^ 2 ∂copies beta μ) =
      ∫ q, pathLogDifference hb t s e q ^ 2 *
        extensionAverage hb t inward stem n (observationCopy left q) ∂copies beta μ := by
  apply TreeOrbitAverage.integral_weight_mul_extension_average s₀ copyAction
    (measurePreserving_copyAction hμ) (fun q => pathLogDifference hb t s e q ^ 2)
    (fun v q => attenuation hb t inward v (observationCopy left q) ^ 2)
    (pathLogDifference_sq_copyAction_invariant hμ hb t s e hstem)
  · intro g hg v
    have hr : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d :=
      hg (ConnectedHull.root d) (Nat.zero_le _)
    have h := (measurePreserving_observationCopy (beta := beta) (μ := μ) left).quasiMeasurePreserving.ae
      (attenuation_relabel_ae hμ hb g hr t inward v)
    filter_upwards [h] with q hq
    have hobs : observationCopy left (copyAction g q) =
        relabel g.symm (observationCopy left q) := by cases left <;> rfl
    rw [hobs, hq]
  · apply (integrable_pathLogDifference_sq hμ hb t s e).mul_bdd
      (((measurable_attenuation hb t inward (endpoint s₀)).comp
        (measurable_observationCopy left)).pow_const 2).aestronglyMeasurable
    filter_upwards [] with q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (attenuation_mem_Icc hb t inward _ _).1
      (attenuation_mem_Icc hb t inward _ _).2

theorem integral_log_weight_mul_le_of_tail {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) (left inward : Bool)
    {stem : List (Fin d)} {n : ℕ}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length) (s₀ : Extension stem n)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (htail : (observationLaw μ)
      {x | a < extensionAverage hb t inward stem n x} ≤ ENNReal.ofReal ε) :
    (∫ q, pathLogDifference hb t s e q ^ 2 *
      attenuation hb t inward (endpoint s₀) (observationCopy left q) ^ 2 ∂copies beta μ) ≤
      a * (∫ q, pathLogDifference hb t s e q ^ 2 ∂copies beta μ) +
        ((s.card : ℝ) ^ 2 * edgeLogBound d beta T ^ 2) * ε := by
  rw [integral_log_weight_mul_extension_average hμ hb t s e left inward hstem s₀]
  have hprob : (copies beta μ)
      {q | a < extensionAverage hb t inward stem n (observationCopy left q)} ≤
        ENNReal.ofReal ε := by
    have hp := (measurePreserving_observationCopy (beta := beta) (μ := μ) left).measure_preimage
      ((measurable_extensionAverage hb t inward stem n) (measurableSet_Ioi (a := a))).nullMeasurableSet
    exact hp.trans_le htail
  exact DependentWeight.integral_mul_le_of_tail_probability
    (integrable_pathLogDifference_sq hμ hb t s e)
    ((measurable_extensionAverage hb t inward stem n).comp (measurable_observationCopy left))
    ha (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Filter.Eventually.of_forall fun q => sq_nonneg _)
    (ae_pathLogDifference_sq_bound hμ hb ht s e)
    (Filter.Eventually.of_forall fun q => (extensionAverage_mem_Icc hb t inward s₀ _).1)
    (Filter.Eventually.of_forall fun q => (extensionAverage_mem_Icc hb t inward s₀ _).2)
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob).trans_eq (ENNReal.toReal_ofReal hε))

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedPrefixWeights
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds IsingCopyWeightedCut TreeOrbitAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem takeVertex_takeVertex_of_le (v : TreeVertex d) {i p : ℕ} (hi : i ≤ p) :
    takeVertex (takeVertex v p) i = takeVertex v i := by
  apply Subtype.ext
  simp [takeVertex, List.take_take, Nat.min_eq_left hi]

theorem edge_takeVertex (inward : Bool) (v : TreeVertex d) {i p : ℕ} (hi : i < p) :
    edge inward (takeVertex v p) i = edge inward v i := by
  cases inward <;> simp only [edge, Bool.false_eq_true, ↓reduceIte]
  all_goals rw [takeVertex_takeVertex_of_le v (by omega),
    takeVertex_takeVertex_of_le v (by omega)]

theorem logSum_prefix (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (v : TreeVertex d) (p : ℕ) :
    logSum hb t inward (takeVertex v p) (Finset.range p) =
      logSum hb t inward v (Finset.range p) := by
  funext q
  unfold logSum pathLogDifference
  apply Finset.sum_congr rfl
  intro i hi
  rw [edge_takeVertex inward v (Finset.mem_range.mp hi)]

theorem prefix_edges_in_stem (inward : Bool) (v : TreeVertex d) {p : ℕ}
    (hp : p ≤ v.1.length) :
    ∀ i ∈ Finset.range p, (edge inward v i).1.1.length ≤ (v.1.take p).length ∧
      (edge inward v i).2.1.length ≤ (v.1.take p).length := by
  intro i hi
  have hi' := Finset.mem_range.mp hi
  cases inward <;> simp only [edge, Bool.false_eq_true, ↓reduceIte,
    takeVertex, List.length_take, Nat.min_eq_left hp]
  all_goals constructor <;> omega

theorem exists_logSum_prefix_variance_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w →
      ∀ (inward : Bool) (v : TreeVertex d) (p : ℕ), p ≤ v.1.length →
      (∫ q, logSum hb t inward v (Finset.range p) q ^ 2 ∂copies beta μ) ≤
        C * (p : ℝ) * ∫ q, cavityLogDifference hb t u w q ^ 2 ∂copies beta μ := by
  obtain ⟨C, hC, h⟩ := exists_cavityLog_path_variance_bound hμ hd hb hthreshold
  refine ⟨C, hC, ?_⟩
  intro t u w huw inward v p hp
  have hv := h t u w huw (TreeAut.refl d) (takeVertex v p)
  have hlen : (takeVertex v p).1.length = p := by
    exact List.length_take_of_le hp
  simp only [TreeAut.refl, Equiv.refl_apply] at hv
  have hf (q : IsingConditionalCopyBounds.CopySpace d) :
      (∑ i : Fin (takeVertex v p).1.length, cavityLogDifference hb t
        (takeVertex (takeVertex v p) i) (takeVertex (takeVertex v p) (i + 1)) q) =
      ∑ i ∈ Finset.range (takeVertex v p).1.length, cavityLogDifference hb t
        (takeVertex (takeVertex v p) i) (takeVertex (takeVertex v p) (i + 1)) q :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => cavityLogDifference hb t
      (takeVertex (takeVertex v p) i) (takeVertex (takeVertex v p) (i + 1)) q) _
  have hr (q : IsingConditionalCopyBounds.CopySpace d) :
      (∑ i : Fin (takeVertex v p).1.length, cavityLogDifference hb t
        (takeVertex (takeVertex v p) (i + 1)) (takeVertex (takeVertex v p) i) q) =
      ∑ i ∈ Finset.range (takeVertex v p).1.length, cavityLogDifference hb t
        (takeVertex (takeVertex v p) (i + 1)) (takeVertex (takeVertex v p) i) q :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => cavityLogDifference hb t
      (takeVertex (takeVertex v p) (i + 1)) (takeVertex (takeVertex v p) i) q) _
  simp_rw [hf, hr] at hv
  rw [← logSum_prefix hb t inward v p]
  cases inward
  · simpa only [logSum, pathLogDifference, edge, Bool.false_eq_true, ↓reduceIte,
      edgeLogDifference_eq_cavityLogDifference, Fin.sum_univ_eq_sum_range,
      hlen, TreeAut.refl, Equiv.refl_apply] using hv.2
  · simpa only [logSum, pathLogDifference, edge, ↓reduceIte,
      edgeLogDifference_eq_cavityLogDifference, Fin.sum_univ_eq_sum_range,
      hlen, TreeAut.refl, Equiv.refl_apply] using hv.1

theorem integral_prefix_weight_mul_le_of_tail
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (left inward : Bool) (v : TreeVertex d)
    {p : ℕ} (hp : p ≤ v.1.length) {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (htail : observationLaw μ
      {x | a < extensionAverage hb t inward (v.1.take p) (v.1.length - p) x} ≤
        ENNReal.ofReal ε) :
    (∫ q, logSum hb t inward v (Finset.range p) q ^ 2 *
      attenuation hb t inward v (observationCopy left q) ^ 2 ∂copies beta μ) ≤
      a * (∫ q, logSum hb t inward v (Finset.range p) q ^ 2 ∂copies beta μ) +
        ((p : ℝ) ^ 2 * edgeLogBound d beta T ^ 2) * ε := by
  simpa only [logSum, endpoint_extensionAt, Finset.card_range] using
    integral_log_weight_mul_le_of_tail hμ hb ht (Finset.range p) (edge inward v)
      left inward (prefix_edges_in_stem inward v hp) (extensionAt v p) ha hε htail

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedNoiseSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds IsingCopyWeightedCut

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem integrable_weightedLog
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (s : Finset ℕ) (left : Bool) :
    Integrable (fun q => logSum hb t inward v s q ^ 2 *
      attenuation hb t inward v (observationCopy left q) ^ 2) (copies beta μ) := by
  apply (integrable_pathLogDifference_sq hμ hb t s (edge inward v)).mul_bdd
    (((measurable_attenuation hb t inward v).comp
      (measurable_observationCopy left)).pow_const 2).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_one₀ (attenuation_mem_Icc hb t inward v _).1
    (attenuation_mem_Icc hb t inward v _).2

theorem logSum_split (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (v : TreeVertex d) {p : ℕ} (hp : p ≤ v.1.length)
    (q : IsingConditionalCopyBounds.CopySpace d) :
    logSum hb t inward v (Finset.range v.1.length) q =
      logSum hb t inward v (Finset.range p) q +
      logSum hb t inward v (Finset.Ico p v.1.length) q :=
  (Finset.sum_range_add_sum_Ico
    (fun i => edgeLogDifference hb t (edge inward v i).1 (edge inward v i).2 q) hp).symm

theorem weightedLogEnergy_split_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) {p : ℕ}
    (hp : p ≤ v.1.length) (left : Bool) :
    weightedLogEnergy (μ := μ) hb t inward v (Finset.range v.1.length) left ≤
      2 * (weightedLogEnergy (μ := μ) hb t inward v (Finset.range p) left +
        weightedLogEnergy (μ := μ) hb t inward v (Finset.Ico p v.1.length) left) := by
  have hi₁ := integrable_weightedLog hμ hb t inward v (Finset.range p) left
  have hi₂ := integrable_weightedLog hμ hb t inward v (Finset.Ico p v.1.length) left
  have hall := integrable_weightedLog hμ hb t inward v (Finset.range v.1.length) left
  unfold weightedLogEnergy
  rw [← integral_add hi₁ hi₂, ← integral_const_mul]
  apply integral_mono hall ((hi₁.add hi₂).const_mul 2)
  intro q
  dsimp only [Pi.add_apply]
  rw [logSum_split hb t inward v hp q]
  have hs : (logSum hb t inward v (Finset.range p) q +
      logSum hb t inward v (Finset.Ico p v.1.length) q) ^ 2 ≤
      2 * (logSum hb t inward v (Finset.range p) q ^ 2 +
        logSum hb t inward v (Finset.Ico p v.1.length) q ^ 2) := by
    nlinarith [sq_nonneg (logSum hb t inward v (Finset.range p) q -
      logSum hb t inward v (Finset.Ico p v.1.length) q)]
  calc
    _ ≤ (2 * (logSum hb t inward v (Finset.range p) q ^ 2 +
        logSum hb t inward v (Finset.Ico p v.1.length) q ^ 2)) *
      attenuation hb t inward v (observationCopy left q) ^ 2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by ring

theorem noiseEnergy_eq_weightedLogEnergy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    IsingCopyResponseRowPaths.noiseEnergy (μ := μ) hb t v =
      weightedLogEnergy (μ := μ) hb t false v (Finset.range v.1.length) true +
      weightedLogEnergy (μ := μ) hb t false v (Finset.range v.1.length) false := by
  rw [weightedLogEnergy, weightedLogEnergy, ← integral_add
    (integrable_weightedLog hμ hb t false v (Finset.range v.1.length) true)
    (integrable_weightedLog hμ hb t false v (Finset.range v.1.length) false)]
  apply integral_congr_ae
  filter_upwards [] with q
  change (attenuation hb t false v (observationCopy true q) ^ 2 +
      attenuation hb t false v (observationCopy false q) ^ 2) *
      logSum hb t false v (Finset.range v.1.length) q ^ 2 = _
  ring

theorem noiseEnergy_le_four_half_weights
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {p : ℕ} (hp : p ≤ v.1.length) :
    IsingCopyResponseRowPaths.noiseEnergy (μ := μ) hb t v ≤ 2 *
      (weightedLogEnergy (μ := μ) hb t false v (Finset.range p) true +
       weightedLogEnergy (μ := μ) hb t false v (Finset.range p) false +
       weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) true +
       weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) false) := by
  rw [noiseEnergy_eq_weightedLogEnergy hμ hb t v]
  have hl := weightedLogEnergy_split_le hμ hb t false v hp true
  have hr := weightedLogEnergy_split_le hμ hb t false v hp false
  linarith

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_PathReversalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingOrientedPath
open ConnectedHull TreeKoopman IsingCopySpectral IsingCopyStationarity
open IsingObservationInnovation IsingObservationFactor IsingCopyPathBounds
open IsingCopyWeightedCut

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem edge_reverse_inverse (v : TreeVertex d) (i : ℕ) (hi : i < v.1.length) :
    ((wordAut v.1).toEquiv.symm (edge false v i).1,
      (wordAut v.1).toEquiv.symm (edge false v i).2) =
      edge true (reverseVertex v) (v.1.length - 1 - i) := by
  change ((wordAut v.1).toEquiv.symm (takeVertex v (i + 1)),
    (wordAut v.1).toEquiv.symm (takeVertex v i)) =
    (takeVertex (reverseVertex v) (v.1.length - 1 - i),
      takeVertex (reverseVertex v) (v.1.length - 1 - i + 1))
  rw [← wordAut_reverse_apply_eq_symm, ← wordAut_reverse_apply_eq_symm,
    wordAut_reverse_apply_prefix, wordAut_reverse_apply_prefix]
  have hleft : v.1.length - (i + 1) = v.1.length - 1 - i := by omega
  have hright : v.1.length - i = v.1.length - 1 - i + 1 := by omega
  rw [hleft, hright]

theorem edge_reverse_inverse_oriented (inward : Bool)
    (v : TreeVertex d) (i : ℕ) (hi : i < v.1.length) :
    ((wordAut v.1).toEquiv.symm (edge inward v i).1,
      (wordAut v.1).toEquiv.symm (edge inward v i).2) =
      edge (!inward) (reverseVertex v) (v.1.length - 1 - i) := by
  cases inward
  · exact edge_reverse_inverse v i hi
  · exact congrArg Prod.swap (edge_reverse_inverse v i hi)

omit [IsProbabilityMeasure μ] in
theorem attenuation_reverse_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    (fun x => attenuation hb t inward v (relabel (wordAut v.1) x)) =ᵐ[observationLaw μ]
      attenuation hb t (!inward) (reverseVertex v) := by
  have hnat := ae_all_iff.mpr (fun i : ℕ => cavityObservable_relabel_ae
    hμ hb (wordAut v.1) t (edge inward v i).1 (edge inward v i).2)
  filter_upwards [hnat] with x hx
  unfold attenuation
  have hlen : (reverseVertex v).1.length = v.1.length := List.length_reverse
  rw [hlen]
  apply Finset.prod_bij (fun i _ => v.1.length - 1 - i)
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨v.1.length - 1 - j, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    have he := edge_reverse_inverse_oriented inward v i (Finset.mem_range.mp hi)
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    dsimp only [Prod.fst, Prod.snd] at hl hr
    rw [hx i, hl, hr]

theorem attenuation_copies_reverse_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ,
      attenuation hb t inward v (copyRelabel (wordAut v.1) q).2.1 =
        attenuation hb t (!inward) (reverseVertex v) q.2.1 ∧
      attenuation hb t inward v (copyRelabel (wordAut v.1) q).2.2 =
        attenuation hb t (!inward) (reverseVertex v) q.2.2 := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae (attenuation_reverse_relabel_ae hμ hb t inward v),
    hr.quasiMeasurePreserving.ae (attenuation_reverse_relabel_ae hμ hb t inward v)] with q hq hq'
  exact ⟨hq, hq'⟩

theorem logSum_suffix_reverse_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (p : ℕ) (hp : p ≤ v.1.length) :
    (fun q => logSum hb t inward v (Finset.Ico p v.1.length)
      (copyRelabel (wordAut v.1) q)) =ᵐ[copies beta μ]
      logSum hb t (!inward) (reverseVertex v) (Finset.range (v.1.length - p)) := by
  have hnat := ae_all_iff.mpr (fun i : ℕ => edgeLogDifference_relabel_ae
    hμ hb (wordAut v.1) t (edge inward v i).1 (edge inward v i).2)
  filter_upwards [hnat] with q hq
  unfold logSum pathLogDifference
  apply Finset.sum_bij (fun i _ => v.1.length - 1 - i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    apply Finset.mem_range.mpr
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨v.1.length - 1 - j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro i hi
    have he := edge_reverse_inverse_oriented inward v i (Finset.mem_Ico.mp hi).2
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    dsimp only [Prod.fst, Prod.snd] at hl hr
    rw [hq i, hl, hr]

theorem attenuation_observationCopy_reverse_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (left : Bool) :
    (fun q => attenuation hb t inward v
      (observationCopy left (copyRelabel (wordAut v.1) q))) =ᵐ[copies beta μ]
      (fun q => attenuation hb t (!inward) (reverseVertex v) (observationCopy left q)) := by
  filter_upwards [attenuation_copies_reverse_ae hμ hb t inward v] with q hq
  cases left
  · exact hq.2
  · exact hq.1

theorem integral_suffix_sq_mul_attenuation_reverse
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (p : ℕ) (hp : p ≤ v.1.length)
    (left : Bool) (k : ℕ) :
    (∫ q, logSum hb t inward v (Finset.Ico p v.1.length) q ^ 2 *
      attenuation hb t inward v (observationCopy left q) ^ k ∂copies beta μ) =
      ∫ q, logSum hb t (!inward) (reverseVertex v) (Finset.range (v.1.length - p)) q ^ 2 *
        attenuation hb t (!inward) (reverseVertex v) (observationCopy left q) ^ k
          ∂copies beta μ := by
  have hf := ((measurable_pathLogDifference hb t (Finset.Ico p v.1.length)
    (edge inward v)).pow_const 2).mul
      (((measurable_attenuation hb t inward v).comp
        (measurable_observationCopy left)).pow_const k)
  calc
    _ = ∫ q, logSum hb t inward v (Finset.Ico p v.1.length)
        (copyRelabel (wordAut v.1) q) ^ 2 * attenuation hb t inward v
        (observationCopy left (copyRelabel (wordAut v.1) q)) ^ k ∂copies beta μ :=
      ((measurePreserving_copies_relabel hμ (wordAut v.1)).hasLaw.integral_comp
        hf.aestronglyMeasurable).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [logSum_suffix_reverse_ae hμ hb t inward v p hp,
        attenuation_observationCopy_reverse_ae hμ hb t inward v left] with q hlog hatt
      rw [hlog, hatt]

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_NoiseTwoTails
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds IsingCopyWeightedCut TreeKoopman

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_noiseEnergy_bound_of_two_tails
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t T : ℝ≥0), t ≤ T →
      ∀ (u w : TreeVertex d), treeAdj u w → ∀ (v : TreeVertex d) (p : ℕ),
      p ≤ v.1.length → ∀ (a ε : ℝ), 0 ≤ a → 0 ≤ ε →
      observationLaw μ
        {x | a < extensionAverage hb t false (v.1.take p) (v.1.length - p) x} ≤
          ENNReal.ofReal ε →
      observationLaw μ
        {x | a < extensionAverage hb t true ((reverseVertex v).1.take (v.1.length - p)) p x} ≤
          ENNReal.ofReal ε →
      IsingCopyResponseRowPaths.noiseEnergy (μ := μ) hb t v ≤
        4 * a * C * (v.1.length : ℝ) *
          (∫ q, cavityLogDifference hb t u w q ^ 2 ∂copies beta μ) +
        4 * edgeLogBound d beta T ^ 2 * (v.1.length : ℝ) ^ 2 * ε := by
  obtain ⟨C, hC, hv⟩ := exists_logSum_prefix_variance_bound hμ hd hb hthreshold
  refine ⟨C, hC, ?_⟩
  intro t T ht u w huw v p hp a ε ha hε htail₁ htail₂
  let S := ∫ q, cavityLogDifference hb t u w q ^ 2 ∂copies beta μ
  let M := edgeLogBound d beta T
  let A := a * (C * (p : ℝ) * S) + ((p : ℝ) ^ 2 * M ^ 2) * ε
  let B := a * (C * ((v.1.length - p : ℕ) : ℝ) * S) +
    (((v.1.length - p : ℕ) : ℝ) ^ 2 * M ^ 2) * ε
  have hprefix (left : Bool) :
      weightedLogEnergy (μ := μ) hb t false v (Finset.range p) left ≤ A := by
    exact (integral_prefix_weight_mul_le_of_tail hμ hb ht left false v hp ha hε htail₁).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hv t u w huw false v p hp) ha) le_rfl)
  have hlen : (reverseVertex v).1.length = v.1.length := List.length_reverse
  have hq : v.1.length - p ≤ (reverseVertex v).1.length := by rw [hlen]; omega
  have htail₂' : observationLaw μ
      {x | a < extensionAverage hb t true ((reverseVertex v).1.take (v.1.length - p))
        ((reverseVertex v).1.length - (v.1.length - p)) x} ≤ ENNReal.ofReal ε := by
    simpa only [hlen, Nat.sub_sub_self hp] using htail₂
  have hsuffix (left : Bool) :
      weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) left ≤ B := by
    unfold weightedLogEnergy
    rw [integral_suffix_sq_mul_attenuation_reverse hμ hb t false v p hp left 2]
    exact (integral_prefix_weight_mul_le_of_tail hμ hb ht left true (reverseVertex v)
      hq ha hε htail₂').trans (add_le_add
        (mul_le_mul_of_nonneg_left (hv t u w huw true (reverseVertex v) _ hq) ha) le_rfl)
  have hsum : (p : ℝ) + ((v.1.length - p : ℕ) : ℝ) = (v.1.length : ℝ) := by
    exact_mod_cast Nat.add_sub_of_le hp
  have hsquares : (p : ℝ) ^ 2 + ((v.1.length - p : ℕ) : ℝ) ^ 2 ≤
      (v.1.length : ℝ) ^ 2 := by
    have hpq : 0 ≤ (p : ℝ) * ((v.1.length - p : ℕ) : ℝ) := by positivity
    nlinarith
  calc
    _ ≤ 2 *
      (weightedLogEnergy (μ := μ) hb t false v (Finset.range p) true +
       weightedLogEnergy (μ := μ) hb t false v (Finset.range p) false +
       weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) true +
       weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) false) :=
      noiseEnergy_le_four_half_weights hμ hb t v hp
    _ ≤ 2 * (A + A + B + B) := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add (hprefix true) (hprefix false))
        (hsuffix true)) (hsuffix false)) (by norm_num)
    _ = 4 * a * C * (v.1.length : ℝ) * S +
        4 * M ^ 2 * ((p : ℝ) ^ 2 + ((v.1.length - p : ℕ) : ℝ) ^ 2) * ε := by
      rw [← hsum]
      dsimp only [A, B]
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquares (by positivity)) hε

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyNoiseLongBound
attribute [-simp] _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingOrientedPath IsingCopyPathBounds IsingCopySmallLogLoss TreeKoopman

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_noise_energy_long_constants_oai
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0) :
    ∃ B E c a q C₀ : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ 0 < c ∧ 0 < a ∧ 1 < q ∧ 0 < C₀ ∧
      ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * (logVariance hb μ u w t) *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)) := by
  have hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
    apply (tanh_threshold_iff_branching_sq hd hb).mpr
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using hcritical.le
  obtain ⟨C, hC, hraw⟩ := exists_noiseEnergy_bound_of_two_tails hμ hd hb hthreshold
  obtain ⟨hη, hlengthC, hbase, hdecay⟩ := criticalNoise_constants_positive hd hb hcritical
  let K := Real.exp (4 * beta / (1 - Real.tanh beta))
  refine ⟨4 * K * C, 4 * edgeLogBound d beta T ^ 2,
    criticalNoiseEta d beta / 4, 1 / (2 * ((d : ℝ) - 1)), criticalNoiseTailBase d,
    criticalNoiseLengthConstant beta, by positivity, by positivity,
    div_pos hη (by norm_num), hdecay, hbase, hlengthC, ?_⟩
  intro t ht htT u w huw v hn
  let n := v.1.length
  let ω := min (Real.sqrt (t : ℝ)) 1
  have hω : 0 < ω := lt_min (Real.sqrt_pos.2 (show 0 < (t : ℝ) from ht)) zero_lt_one
  obtain ⟨hn8, hlength⟩ := criticalNoise_length_admissible hd hb hcritical hω
    (min_le_right _ _) hn
  have htail (inward : Bool) (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·))
      (m : ℕ) (hm : n / 2 ≤ m) :
      (observationLaw μ) {x | K *
        Real.exp (-((criticalNoiseEta d beta / 4) * ω) * n) <
          extensionAverage hb t inward stem m x} ≤
        ENNReal.ofReal (Real.exp (-(1 / (2 * ((d : ℝ) - 1))) * criticalNoiseTailBase d ^ n)) := by
    obtain ⟨hsum, hlevel, htail⟩ := half_path_cut_admissible hn8 hm
    have hlevel' : ((n : ℝ) / 4) / 2 - 1 ≤ (m / 2 - 1 + 1 : ℕ) := by
      convert hlevel using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have htail' : ((n : ℝ) / 4) / 2 ≤ (m - m / 2 : ℕ) := by
      convert htail using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have h := measure_extensionAverage_gt_le_double_exp_common hμ hb hd hcritical ht
      inward stem hstem (m / 2 - 1) (m - m / 2) hη.le
      (show 0 ≤ (n : ℝ) / 4 by positivity)
      (min_le_left _ _) (min_le_right _ _) hlevel' htail' hlength
    simpa only [hsum, criticalNoise_threshold_eq, criticalNoise_tail_eq hd] using h
  have hv : v.1.IsChain (· ≠ ·) := v.2
  have hvr : (reverseVertex v).1.IsChain (· ≠ ·) := (reverseVertex v).2
  have h := hraw t T htT u w huw v (n / 2) (by dsimp [n]; omega)
    (K * Real.exp (-((criticalNoiseEta d beta / 4) * ω) * n))
    (Real.exp (-(1 / (2 * ((d : ℝ) - 1))) * criticalNoiseTailBase d ^ n))
    (by positivity) (Real.exp_pos _).le
    (htail false (v.1.take (n / 2)) (hv.take _) (n - n / 2) (by omega))
    (htail true ((reverseVertex v).1.take (n - n / 2)) (hvr.take _) (n / 2) le_rfl)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [logVariance, cavityLogDifference, n, ω]
  ring

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants_oai := @OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants_oai
