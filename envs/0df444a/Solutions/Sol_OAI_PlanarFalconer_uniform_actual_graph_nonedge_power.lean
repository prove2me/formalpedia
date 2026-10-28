-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_graph_nonedge_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:30:00.980523+00:00
-- url     : https://prove2.me/submissions/75804ccc-f21d-4e50-b1c5-a9481dc7f60e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_graph_amplitude_E

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem DyadicSquare.dist_le (Q : DyadicSquare) (hQ : 0 ≤ Q.side)
    {z w : Plane} (hz : z ∈ Q.carrier) (hw : w ∈ Q.carrier) :
    dist z w ≤ 2 * Q.side := by
  have h0 : |z 0 - w 0| ≤ Q.side := by
    apply abs_le.mpr; constructor <;> linarith [hz.1,hz.2.1,hw.1,hw.2.1]
  have h1 : |z 1 - w 1| ≤ Q.side := by
    apply abs_le.mpr; constructor <;>
      linarith [hz.2.2.1,hz.2.2.2,hw.2.2.1,hw.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq z w
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h0
  have hs1 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [dist_nonneg (x := z) (y := w)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_ScaledDyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem DyadicSquare.center_mem (Q : DyadicSquare) (hQ : 0 < Q.side) : Q.center ∈ Q.carrier := by
  simp only [center,carrier,mem_ofPred_eq,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · linarith
  · exact ⟨by linarith,by linarith,by linarith⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_FrostmanProfileCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransformSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem angular_integrand_norm (r : ℝ) (ω : UnitCircle) (x : Plane)
    (b : Plane → UnitCircle → ℂ) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω‖ =
      ‖b x ω‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SchwartzFourierMomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace

 theorem schwartz_iteratedDeriv_integrable (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    Integrable (iteratedDeriv n (φ : ℝ → ℂ)) := by
  apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 n).mono'
    ((φ.smooth ⊤).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).aestronglyMeasurable
  filter_upwards with x
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

 theorem schwartz_fourier_weighted_pointwise (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (ξ : ℝ) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤ fourierDerivativeL1 φ n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤)
    (fun k _ => schwartz_iteratedDeriv_integrable φ k) (n := n) (by simp)) ξ
  have hh := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n (φ : ℝ → ℂ)) ξ
  have hh' : ‖𝓕 (iteratedDeriv n (φ : ℝ → ℂ)) ξ‖ ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    simpa using! hh
  rw [he] at hh'
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one] at hh'
  have hh'' : (2*Real.pi)^n * (‖ξ‖^n*‖𝓕 φ ξ‖) ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_pow,Real.norm_eq_abs,SchwartzMap.fourier_coe]
    ring
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n)).mpr (by simpa [mul_comm] using hh'')

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CompactStationaryAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem complex_iteratedDeriv_tsupport (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset).trans ih

 theorem compact_derivative_integral_bound (φ : 𝓢(ℝ,ℂ)) {a b C : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C) :
    (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) ≤ C*(b-a) := by
  have he : (∫ x in Icc a b, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) =
      ∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply norm_eq_zero.mpr
    by_contra hn
    exact hx (hs (complex_iteratedDeriv_tsupport _ n (subset_closure hn)))
  have hh := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun x : ℝ => ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)
    (s := Icc a b) (C := C) (by simp) (Filter.Eventually.of_forall (fun x => by simpa using hC x))
  rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hh
  simpa [Real.volume_Icc,Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr hab] using hh

 theorem compact_fourierDerivativeL1_bound (φ : 𝓢(ℝ,ℂ)) {a b C D : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n) :
    fourierDerivativeL1 φ n ≤ C*(b-a)*D^n/(2*Real.pi)^n := by
  unfold fourierDerivativeL1
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (C*D^n)*(b-a) := compact_derivative_integral_bound φ hab hs n hC
    _ = _ := by ring

 theorem compact_smooth_to_schwartz {f : ℝ → ℂ} {a b : ℝ}
    (hs : tsupport f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = f := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  exact ⟨hc.toSchwartzMap hf,rfl⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCoordinateInverse
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem quarterTurn_smul (r : ℝ) (v : Plane) : quarterTurn (r • v) = r • quarterTurn v := by
  ext i
  fin_cases i <;> simp [quarterTurn]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphAngularCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem sourceDirection_add_arctan (φ z : ℝ) :
    sourceDirection (φ+Real.arctan z) =
      (Real.sqrt (1+z^2))⁻¹ • (sourceDirection φ+z • quarterTurn (sourceDirection φ)) := by
  ext i
  fin_cases i <;>
    simp [sourceDirection, quarterTurn, Complex.orthonormalBasisOneI_repr_apply,
      Real.cos_add, Real.sin_add, Real.cos_arctan, Real.sin_arctan,
      -Complex.ofReal_sin, -Complex.ofReal_cos] <;> ring

theorem sourceDirection_sub_arctan (φ z : ℝ) :
    sourceDirection (φ-Real.arctan z) =
      (Real.sqrt (1+z^2))⁻¹ • (sourceDirection φ-z • quarterTurn (sourceDirection φ)) := by
  simpa only [Real.arctan_neg, neg_sq, neg_smul, sub_eq_add_neg] using
    sourceDirection_add_arctan φ (-z)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ENNReal

theorem sourcePlaneWave_norm (r : ℝ) (ω : UnitCircle) (x : Plane) :
    ‖sourcePlaneWave r ω x‖ = 1 := by
  simpa only [sourcePlaneWave, mul_one, norm_one] using angular_integrand_norm r ω x (fun _ _ => 1)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalPhase
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_phase_affine (z s : ℝ) (x y : Plane) :
    graphA z x+s • graphB z y = (1/2:ℝ) • (x+s • y) + z • graphDerivative s x y := by
  ext i
  fin_cases i <;> simp [graphA,graphB,graphDerivative,quarterTurn] <;> ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphAngleCharts
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric Filter
open scoped ContDiff Topology

theorem graphComplexCoordinate_norm (η : Plane) : ‖graphComplexCoordinate η‖ = ‖η‖ :=
  Complex.orthonormalBasisOneI.repr.symm.norm_map η

theorem graphPlaneAngle_eq_arg (η : Plane) :
    graphPlaneAngle η = Complex.arg (graphComplexCoordinate η) := by
  change Complex.arg (Complex.equivRealProd.symm (graphPlaneEquiv.symm η)) = _
  congr 1
  apply Complex.orthonormalBasisOneI.repr.injective
  ext i
  fin_cases i <;> simp [graphPlaneEquiv, graphComplexCoordinate,
    Complex.orthonormalBasisOneI_repr_apply]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalSupports
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_directions_sum (φ z : ℝ) :
    sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z) =
      (2/Real.sqrt (1+z^2)) • sourceDirection φ := by
  rw [sourceDirection_add_arctan, sourceDirection_sub_arctan, ← smul_add]
  have he (u v : Plane) : (u+v)+(u-v) = (2:ℝ) • u := by
    simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm]
  rw [he, smul_smul]
  congr 1
  ring

theorem graph_directions_sum_norm (φ z : ℝ) :
    ‖sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z)‖ =
      2/Real.sqrt (1+z^2) := by
  rw [graph_directions_sum, norm_smul, Real.norm_eq_abs, norm_sourceDirection,
    mul_one, abs_of_nonneg (by positivity)]

theorem graph_parameter_bound (φ z : ℝ)
    (hc : 1/2 ≤ ‖sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z)‖) :
    Real.sqrt (1+z^2) ≤ 4 ∧ |z| ≤ 4 := by
  rw [graph_directions_sum_norm] at hc
  have hs : 0 < Real.sqrt (1+z^2) := by positivity
  have hh := (le_div_iff₀ hs).mp hc
  have hb : Real.sqrt (1+z^2) ≤ 4 := by linarith
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1+z^2)
  exact ⟨hb, by nlinarith [sq_abs z, abs_nonneg z]⟩

theorem graph_plus_support_parameter (φ z : ℝ)
    (hc : (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ∈
      tsupport circleGraphSignPlus) :
    |z| ≤ 4 := by
  have hh := circleGraphSignPlus_tsupport hc
  change 1 ≤ ‖(sourceUnitDirection (φ+Real.arctan z) : Plane) +
    (sourceUnitDirection (φ-Real.arctan z) : Plane)‖ at hh
  apply (graph_parameter_bound φ z _).2
  change 1/2 ≤ ‖(sourceUnitDirection (φ+Real.arctan z) : Plane) +
    (sourceUnitDirection (φ-Real.arctan z) : Plane)‖
  linarith

theorem graph_minus_support_parameter (φ z : ℝ)
    (hc : (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z+Real.pi)) ∈
      tsupport circleGraphSignMinus) : |z| ≤ 4 := by
  have hh := circleGraphSignMinus_tsupport hc
  change 1 ≤ ‖sourceDirection (φ+Real.arctan z) -
    sourceDirection (φ-Real.arctan z+Real.pi)‖ at hh
  rw [sourceDirection_add_pi, sub_neg_eq_add] at hh
  exact (graph_parameter_bound φ z (by linarith)).2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualTransport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphFourKernel_weight_ne_zero (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane) (r : ℝ) (u v : UnitCircle)
    (h : graphFourKernel b W x r u v ≠ 0) : W (u,v) ≠ 0 := by
  intro hz
  exact h (by simp [graphFourKernel, graphFourAmplitude, hz])

theorem graphProductWeight_parameter (plus : Bool) (n j k : ℕ) (φ z : ℝ)
    (h : graphProductWeight plus n j k
      (sourceUnitDirection (φ+Real.arctan z),
        sourceUnitDirection (φ-Real.arctan z+(if plus then 0 else Real.pi))) ≠ 0) :
    |z| ≤ 4 := by
  cases plus
  · apply graph_minus_support_parameter φ z
    apply subset_closure
    intro hz
    exact h (by simp [graphProductWeight, hz])
  · apply graph_plus_support_parameter φ z
    apply subset_closure
    intro hz
    exact h (by simp [graphProductWeight, hz])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphRotatedWeights
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphRotatedDistanceWeight_parameter (axis : ℝ) (n j k : ℕ) (φ z : ℝ)
    (h : graphRotatedDistanceWeight axis n j k
      (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ≠ 0) :
    |z| ≤ 4 := by
  rw [graphRotatedDistanceWeight_eq] at h
  have hu : sourceConeCircle axis (sourceUnitDirection (φ+Real.arctan z)) ≠ 0 := by
    intro hz; exact h (by simp [hz])
  have hv : sourceConeCircle axis (sourceUnitDirection (φ-Real.arctan z)) ≠ 0 := by
    intro hz; exact h (by simp [hz])
  have hb := sourceConeCircle_plus_nondegenerate axis _ _ (subset_closure hu) (subset_closure hv)
  exact (graph_parameter_bound φ z ((by norm_num : (1/2:ℝ) ≤ 6/5).trans hb)).2

theorem graphSourceWeight_parameter (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    (φ z : ℝ)
    (h : graphSourceWeight distance plus axis n j k
      (sourceUnitDirection (φ+Real.arctan z),
        sourceUnitDirection (φ-Real.arctan z+graphSourceChartAxis distance plus)) ≠ 0) :
    |z| ≤ 4 := by
  cases distance
  · exact graphProductWeight_parameter plus n j k φ z h
  · apply graphRotatedDistanceWeight_parameter axis n j k φ z
    simpa only [graphSourceWeight, graphSourceChartAxis, ↓reduceIte, add_zero] using h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_LinearNonstationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff RealInnerProductSpace

 theorem compact_fourier_nonstationary {f : ℝ → ℂ} {a z C D ξ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a z) (haz : a ≤ z)
    (hξ : ξ ≠ 0) (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n f x‖ ≤ C*D^n) :
    ‖𝓕 f ξ‖ ≤ C*(z-a)*D^n/((2*Real.pi)^n*‖ξ‖^n) := by
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hs hf
  have hs' : tsupport (φ : ℝ → ℂ) ⊆ Icc a z := by simpa [hφ] using hs
  have hC' : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n := by simpa [hφ] using hC
  have hh := (schwartz_fourier_weighted_pointwise φ n ξ).trans
    (compact_fourierDerivativeL1_bound φ haz hs' n hC')
  rw [SchwartzMap.fourier_coe,hφ] at hh
  have hpos : 0 < ‖ξ‖^n := pow_pos (norm_pos_iff.mpr hξ) _
  have hi : ‖𝓕 f ξ‖ ≤ (C*(z-a)*D^n/(2*Real.pi)^n)/‖ξ‖^n :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm (‖𝓕 f ξ‖)] using hh)
  simpa [div_div] using hi

 theorem compact_linear_phase_bound {f : ℝ → ℂ} {a z C D ξ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a z) (haz : a ≤ z)
    (hξ : ξ ≠ 0) (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n f x‖ ≤ C*D^n) :
    ‖∫ x : ℝ, Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(x:ℂ)*(ξ:ℂ))*f x‖ ≤
      C*(z-a)*D^n/((2*Real.pi)^n*‖ξ‖^n) := by
  have he : 𝓕 f ξ = ∫ x : ℝ,
      Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(x:ℂ)*(ξ:ℂ))*f x := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with x
    simp only [Real.inner_apply, smul_eq_mul]
    push_cast
    congr 2
    ring
  rw [← he]
  exact compact_fourier_nonstationary hf hs haz hξ n hC

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphActualFrequencySupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphSourceWeight_sqrt_bound (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    (φ z : ℝ)
    (h : graphSourceWeight distance plus axis n j k
      (sourceUnitDirection (φ+Real.arctan z),
        sourceUnitDirection (φ-Real.arctan z+graphSourceChartAxis distance plus)) ≠ 0) :
    Real.sqrt (1+z^2) ≤ 4 := by
  apply (graph_parameter_bound φ z _).1
  cases distance
  · cases plus
    · have hs : (sourceUnitDirection (φ+Real.arctan z),
          sourceUnitDirection (φ-Real.arctan z+Real.pi)) ∈ tsupport circleGraphSignMinus := by
        apply subset_closure
        intro hz
        exact h (by simp [graphSourceWeight, graphSourceChartAxis, graphProductWeight, hz])
      have hh := circleGraphSignMinus_tsupport hs
      change 1 ≤ ‖sourceDirection (φ+Real.arctan z)-sourceDirection (φ-Real.arctan z+Real.pi)‖ at hh
      rw [sourceDirection_add_pi, sub_neg_eq_add] at hh
      linarith
    · have hs : (sourceUnitDirection (φ+Real.arctan z),
          sourceUnitDirection (φ-Real.arctan z)) ∈ tsupport circleGraphSignPlus := by
        apply subset_closure
        intro hz
        exact h (by simp [graphSourceWeight, graphSourceChartAxis, graphProductWeight, hz])
      have hh := circleGraphSignPlus_tsupport hs
      change 1 ≤ ‖sourceDirection (φ+Real.arctan z)+sourceDirection (φ-Real.arctan z)‖ at hh
      linarith
  · have he : graphRotatedDistanceWeight axis n j k
        (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ≠ 0 := by
      simpa only [graphSourceWeight, graphSourceChartAxis, ↓reduceIte, add_zero] using h
    rw [graphRotatedDistanceWeight_eq] at he
    have hu : sourceConeCircle axis (sourceUnitDirection (φ+Real.arctan z)) ≠ 0 := by
      intro hz; exact he (by simp [hz])
    have hv : sourceConeCircle axis (sourceUnitDirection (φ-Real.arctan z)) ≠ 0 := by
      intro hz; exact he (by simp [hz])
    have hh := sourceConeCircle_plus_nondegenerate axis _ _ (subset_closure hu) (subset_closure hv)
    exact (by norm_num : (1/2:ℝ) ≤ 6/5).trans hh

theorem graphActualTransport_frequency_support
    (b : Fin 4 → Plane → UnitCircle → ℂ) (x : Fin 4 → Plane)
    (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (R : ℝ) (p : ℝ × Plane)
    (hp : graphTransport (graphFourKernel b (graphSourceWeight distance plus axis n j k) x)
      Ψ R (graphSourceChartAxis distance plus) p ≠ 0) :
    1/8 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ 8 ∧ |p.1| ≤ 4 := by
  have hb : Ψ (‖p.2‖*Real.sqrt (1+p.1^2)/2) ≠ 0 := by
    intro hz; exact hp (by simp [graphTransport, hz])
  have hf : graphFourKernel b (graphSourceWeight distance plus axis n j k) x
      (R*(‖p.2‖*Real.sqrt (1+p.1^2)/2))
      (sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1))
      (sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+graphSourceChartAxis distance plus)) ≠ 0 := by
    intro hz; exact hp (by simp [graphTransport, hz])
  have hw := graphFourKernel_weight_ne_zero b _ x _ _ _ hf
  have hs := graphSourceWeight_sqrt_bound distance plus axis n j k _ _ hw
  have hz := graphSourceWeight_parameter distance plus axis n j k _ _ hw
  have hr := hsupp _ hb
  have hlow : 1 ≤ Real.sqrt (1+p.1^2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg p.1]
  refine ⟨?_,?_,hz⟩
  · nlinarith [hr.1, mul_le_mul_of_nonneg_left hs (norm_nonneg p.2)]
  · nlinarith [hr.2, mul_le_mul_of_nonneg_left hlow (norm_nonneg p.2)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphFourSymbolDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem graphSmoothDomain_isOpen : IsOpen graphSmoothDomain :=
  isOpen_ne_fun continuous_fst continuous_const

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_PlaneFourierNonstationary
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap

theorem plane_schwartz_fourier_weighted (φ : 𝓢(Plane,ℂ)) (n : ℕ)
    (ξ : Plane) (hξ : ξ ≠ 0) :
    (2*Real.pi)^n*‖ξ‖^n*‖𝓕 (φ : Plane → ℂ) ξ‖ ≤
      ∫ x : Plane, ‖iteratedFDeriv ℝ n (φ : Plane → ℂ) x‖ := by
  have hi (j : ℕ) : Integrable (iteratedFDeriv ℝ j (φ : Plane → ℂ)) := by
    apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 j).mono'
      ((φ.smooth ⊤).continuous_iteratedFDeriv (m := j)
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).aestronglyMeasurable
    filter_upwards with x
    simp
  have he := congrFun (Real.fourier_iteratedFDeriv (N := (⊤:ℕ∞))
    (φ.smooth ⊤) (fun j _ => hi j) (n := n) (by simp)) ξ
  have hb : ‖𝓕 (iteratedFDeriv ℝ n (φ : Plane → ℂ)) ξ‖ ≤
      ∫ x : Plane, ‖iteratedFDeriv ℝ n (φ : Plane → ℂ) x‖ := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ Plane) (iteratedFDeriv ℝ n (φ : Plane → ℂ)) ξ
  let L := VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 (φ : Plane → ℂ)) ξ n
  have hl : ‖L‖ ≤ ∫ x : Plane, ‖iteratedFDeriv ℝ n (φ : Plane → ℂ) x‖ := by
    simpa only [he] using hb
  have hv := (L.le_opNorm (fun _ => ξ)).trans
    (mul_le_mul_of_nonneg_right hl (by positivity))
  have hinner : innerSL ℝ ξ ξ = ‖ξ‖^2 := real_inner_self_eq_norm_sq ξ
  have hv' : ((2*Real.pi)^n*‖ξ‖^n*‖𝓕 (φ : Plane → ℂ) ξ‖)*‖ξ‖^n ≤
      (∫ x : Plane, ‖iteratedFDeriv ℝ n (φ : Plane → ℂ) x‖)*‖ξ‖^n := by
    simpa [L,VectorFourier.fourierPowSMulRight_apply, norm_smul,
      hinner,Finset.prod_const,
      abs_pow,abs_norm,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      pow_two,mul_pow,mul_assoc,mul_left_comm,mul_comm] using hv
  exact (mul_le_mul_iff_left₀ (pow_pos (norm_pos_iff.mpr hξ) n)).mp hv'

theorem plane_compact_fourier_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Metric.closedBall (0:Plane) 8) (n : ℕ) {C D : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*D^n) (ξ : Plane) (hξ : ξ ≠ 0) :
    ‖𝓕 f ξ‖ ≤ (C*D^n*volume.real (Metric.closedBall (0:Plane) 8))/
      ((2*Real.pi)^n*‖ξ‖^n) := by
  have hc : HasCompactSupport f :=
    (isCompact_closedBall (0:Plane) 8).of_isClosed_subset isClosed_closure hs
  let φ := hc.toSchwartzMap hf
  have hw := plane_schwartz_fourier_weighted φ n ξ hξ
  change (2*Real.pi)^n*‖ξ‖^n*‖𝓕 f ξ‖ ≤ ∫ x, ‖iteratedFDeriv ℝ n f x‖ at hw
  have hz (x : Plane) (hx : x ∉ Metric.closedBall (0:Plane) 8) :
      ‖iteratedFDeriv ℝ n f x‖ = 0 := by
    apply norm_eq_zero.mpr
    apply Function.notMem_support.mp
    intro hm
    exact hx (hs (support_iteratedFDeriv_subset n hm))
  have he := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun x : Plane => ‖iteratedFDeriv ℝ n f x‖)
    (s := Metric.closedBall (0:Plane) 8) (C := C*D^n)
    (isCompact_closedBall (0:Plane) 8).measure_lt_top
    (Filter.Eventually.of_forall (fun x => by simpa using hb x))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at he
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n*‖ξ‖^n)).mpr
    (by simpa only [mul_comm (‖𝓕 f ξ‖)] using hw.trans he)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem dyadic_power_real (N : ℕ) (s : ℝ) :
    ((2 : ℝ)^N)^s = (2 : ℝ)^((N : ℝ)*s) := by
  rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFixedCutoffs
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff ComplexConjugate

theorem graph_plane_axis_all (η : Plane) :
    ‖η‖ • sourceDirection (graphPlaneAngle η) = η := by
  rw [graphPlaneAngle_eq_arg]
  have he := congrArg Complex.orthonormalBasisOneI.repr
    (Complex.norm_mul_cos_add_sin_mul_I (graphComplexCoordinate η))
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.real_smul, LinearIsometryEquiv.map_smul,
    graphComplexCoordinate_norm, graphComplexCoordinate,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map, sourceDirection] using he

theorem graphNormalizedAxis_eq_all {η : Plane} (hη : η ≠ 0) :
    graphNormalizedAxis η = sourceDirection (graphPlaneAngle η) := by
  calc
    graphNormalizedAxis η = ‖η‖⁻¹ • (‖η‖ • sourceDirection (graphPlaneAngle η)) :=
      congrArg (fun v : Plane => ‖η‖⁻¹ • v) (graph_plane_axis_all η).symm
    _ = _ := by rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hη), one_smul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

theorem graphAmplitudeCompact_isCompact : IsCompact graphAmplitudeCompact :=
  ((isCompact_closedBall (0:Plane) 8).prod isCompact_Icc).inter_right
    (isClosed_le continuous_const continuous_fst.norm)

theorem graphAmplitudePullback_norm_transport (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (Ψ : ℝ → ℝ) (R : ℝ) (p : Plane × ℝ) :
    ‖graphAmplitudePullback b x distance plus axis δ j k Ψ p‖ =
      ‖graphTransport (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
        Ψ R (graphSourceChartAxis distance plus) (p.2,p.1)‖ := by
  simp only [graphAmplitudePullback,graphShellJacobian,graphTransport,graphFourKernel,
    norm_smul,norm_mul,sourcePlaneWave_norm,one_mul,mul_one,Complex.norm_real]
  ring

theorem graphAmplitudePullback_tsupport (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    tsupport (graphAmplitudePullback b x distance plus axis δ j k Ψ) ⊆ graphAmplitudeCompact := by
  apply closure_minimal _ graphAmplitudeCompact_isCompact.isClosed
  intro p hp
  have hn : graphTransport
      (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
      Ψ 1 (graphSourceChartAxis distance plus) (p.2,p.1) ≠ 0 := by
    intro he
    apply hp
    apply norm_eq_zero.mp
    rw [graphAmplitudePullback_norm_transport b x distance plus axis δ j k Ψ 1 p,he,norm_zero]
  have hb := graphActualTransport_frequency_support b x distance plus axis (angularBinCount δ) j k hsupp 1 (p.2,p.1) hn
  refine ⟨⟨?_,abs_le.mp hb.2.2⟩,hb.1⟩
  simpa only [mem_closedBall,dist_zero_right] using hb.2.1

theorem GraphDerivativeBound.global_smooth {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact) :
    ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 ≠ 0
  · exact (hf.smooth p hp).contDiffAt (graphSmoothDomain_isOpen.mem_nhds hp)
  · have hn : p ∉ tsupport f := by
      intro hmem
      have hlo : (1:ℝ)/8 ≤ ‖p.1‖ := (hs hmem).2
      rw [not_ne_iff.mp hp,norm_zero] at hlo
      norm_num at hlo
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with q hq
    exact image_eq_zero_of_notMem_tsupport hq

theorem GraphDerivativeBound.global_bound {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (j : ℕ) (hj : j ≤ n) (p : Plane × ℝ) :
    ‖iteratedFDeriv ℝ j f p‖ ≤ C*D^j := by
  by_cases hp : p ∈ graphAmplitudeCompact
  · apply hf.bound j hj p.1 p.2 _ (abs_le.mpr hp.1.2) hp.2
    simpa only [mem_closedBall,dist_zero_right] using hp.1.1
  · have hz : iteratedFDeriv ℝ j f p = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      exact hp (hs (support_iteratedFDeriv_subset j hmem))
    rw [hz,norm_zero]
    exact mul_nonneg hC (pow_nonneg hD j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeRepresentative
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem graph_directions_chartZ (φ z : ℝ) :
    graphChartZ (sourceDirection (φ+Real.arctan z)) (sourceDirection (φ-Real.arctan z)) = z := by
  let u := sourceDirection (φ+Real.arctan z)
  let v := sourceDirection (φ-Real.arctan z)
  have hn : 0 < ‖u+v‖ := by rw [graph_directions_sum_norm]; positivity
  have hd := graph_chart_difference u v (norm_sourceDirection _) (norm_sourceDirection _) (norm_pos_iff.mp hn)
  have he : u-v = z • quarterTurn (u+v) := by
    dsimp [u,v]
    rw [graph_directions_sum, quarterTurn_smul, sourceDirection_add_arctan, sourceDirection_sub_arctan]
    module
  have hq : quarterTurn (u+v) ≠ 0 := by rw [← norm_ne_zero_iff,graph_quarterTurn_norm]; exact hn.ne'
  exact (smul_left_injective ℝ hq) (hd.symm.trans he)

theorem graph_directions_chartAxis (φ z : ℝ) :
    graphChartAxis (sourceDirection (φ+Real.arctan z)) (sourceDirection (φ-Real.arctan z)) = sourceDirection φ := by
  rw [graphChartAxis, graph_directions_sum_norm, graph_directions_sum, smul_smul,
    inv_mul_cancel₀ (by positivity : (2:ℝ)/Real.sqrt (1+z^2) ≠ 0), one_smul]

theorem graphSourceEndpoints_signed (distance plus : Bool) (p : Plane × ℝ) :
    graphSourceSign distance plus • ((graphSourceEndpoints distance plus p).2:Plane) =
      sourceDirection (graphPlaneAngle p.1-Real.arctan p.2) := by
  cases distance <;> cases plus <;>
    simp [graphSourceEndpoints,graphSourceSign,graphSourceChartAxis,sourceUnitDirection,sourceDirection_add_pi]

theorem graphSourceEndpoints_coordinates (distance plus : Bool) {p : Plane × ℝ} (hp : p.1 ≠ 0) :
    graphChartZ ((graphSourceEndpoints distance plus p).1:Plane)
        (graphSourceSign distance plus • ((graphSourceEndpoints distance plus p).2:Plane)) = p.2 ∧
    graphChartAxis ((graphSourceEndpoints distance plus p).1:Plane)
        (graphSourceSign distance plus • ((graphSourceEndpoints distance plus p).2:Plane)) = graphNormalizedAxis p.1 := by
  rw [graphSourceEndpoints_signed]
  change graphChartZ (sourceDirection _) _ = _ ∧ graphChartAxis (sourceDirection _) _ = _
  rw [graph_directions_chartZ, graph_directions_chartAxis,graphNormalizedAxis_eq_all hp]
  exact ⟨rfl,rfl⟩

theorem graphAmplitudePullback_weight_nonzero (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (Ψ : ℝ → ℝ) {p : Plane × ℝ}
    (hp : graphAmplitudePullback b x distance plus axis δ j k Ψ p ≠ 0) :
    graphSourceWeight distance plus axis (angularBinCount δ) j k (graphSourceEndpoints distance plus p) ≠ 0 := by
  intro hz
  apply hp
  change graphSourceWeight distance plus axis (angularBinCount δ) j k
    (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2),
      sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+graphSourceChartAxis distance plus)) = 0 at hz
  simp [graphAmplitudePullback,graphFourAmplitude,hz]

theorem GraphSourceRepresentative.amplitude_coordinates
    {distance plus : Bool} {axis δ : ℝ} {j k : ℕ} {q : UnitCircle × UnitCircle}
    (hq : GraphSourceRepresentative distance plus axis δ j k q)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (x : Fin 4 → Plane)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {p : Plane × ℝ} (hp : graphAmplitudePullback b x distance plus axis δ j k Ψ p ≠ 0) :
    |p.2-graphChartZ (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))|+
      dist (graphNormalizedAxis p.1) (graphChartAxis (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))) ≤ 112*δ := by
  have hs := graphAmplitudePullback_tsupport b x distance plus axis δ j k hsupp (subset_closure hp)
  have hlo : (1:ℝ)/8 ≤ ‖p.1‖ := hs.2
  have hn : p.1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw := hq.2 _ (subset_closure (graphAmplitudePullback_weight_nonzero b x distance plus axis δ j k Ψ hp))
  rw [(graphSourceEndpoints_coordinates distance plus hn).1,
    (graphSourceEndpoints_coordinates distance plus hn).2] at hw
  exact hw

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem graph_nonedge_scale_gain (N : ℕ) (sig v p : ℝ) :
    graphNonedgeDerivativeScale N sig (v-p) /
      ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))) = ((2:ℝ)^N)^(-26*sig) := by
  simp only [graphNonedgeDerivativeScale,dyadic_power_real,
    ← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_sub (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgePerturbation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem graphA_norm_bound (z : ℝ) (v : Plane) :
    ‖graphA z v‖ ≤ (1+|z|)/2*‖v‖ := by
  calc
    _ = (1/2:ℝ)*‖v-z • quarterTurn v‖ := by simp [graphA,norm_smul]
    _ ≤ (1/2:ℝ)*(‖v‖+‖z • quarterTurn v‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = _ := by rw [norm_smul,Real.norm_eq_abs,graph_quarterTurn_norm]; ring

theorem graphB_norm_bound (z : ℝ) (v : Plane) :
    ‖graphB z v‖ ≤ (1+|z|)/2*‖v‖ := by
  simpa only [graphA,graphB,neg_smul,sub_neg_eq_add,abs_neg] using graphA_norm_bound (-z) v

theorem graphA_perturbation_identity (z z₀ : ℝ) (v v₀ : Plane) :
    graphA z v-graphA z₀ v₀ = graphA z (v-v₀) + ((z₀-z)/2) • quarterTurn v₀ := by
  ext i
  fin_cases i <;> simp [graphA,quarterTurn] <;> ring

theorem graphB_perturbation_identity (z z₀ : ℝ) (v v₀ : Plane) :
    graphB z v-graphB z₀ v₀ = graphB z (v-v₀) + ((z-z₀)/2) • quarterTurn v₀ := by
  ext i
  fin_cases i <;> simp [graphB,quarterTurn] <;> ring

theorem graphA_perturbation_bound (z z₀ : ℝ) (v v₀ : Plane) :
    ‖graphA z v-graphA z₀ v₀‖ ≤
      (1+|z|)/2*‖v-v₀‖+|z-z₀|/2*‖v₀‖ := by
  rw [graphA_perturbation_identity]
  apply (norm_add_le _ _).trans
  apply add_le_add (graphA_norm_bound _ _) (le_of_eq _)
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_sub_comm,abs_of_pos (by norm_num : (0:ℝ)<2),graph_quarterTurn_norm]

theorem graphB_perturbation_bound (z z₀ : ℝ) (v v₀ : Plane) :
    ‖graphB z v-graphB z₀ v₀‖ ≤
      (1+|z|)/2*‖v-v₀‖+|z-z₀|/2*‖v₀‖ := by
  rw [graphB_perturbation_identity]
  apply (norm_add_le _ _).trans
  apply add_le_add (graphB_norm_bound _ _) (le_of_eq _)
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),graph_quarterTurn_norm]

theorem graph_vector_perturbation (s z z₀ : ℝ) (v w v₀ w₀ : Plane) (hs : |s| = 1)
    {δ θ ℓ : ℝ} (_hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (_hℓ : 0 ≤ ℓ)
    (hz : |z| ≤ 4) (hmove : |z-z₀| ≤ θ)
    (hv : ‖v-v₀‖ ≤ 4*δ) (hw : ‖w-w₀‖ ≤ 4*δ)
    (hv₀ : ‖v₀‖ ≤ ℓ) (hw₀ : ‖w₀‖ ≤ ℓ) :
    ‖(graphA z v+s • graphB z w)-(graphA z₀ v₀+s • graphB z₀ w₀)‖ ≤ 20*δ+θ*ℓ := by
  have he : (graphA z v+s • graphB z w)-(graphA z₀ v₀+s • graphB z₀ w₀) =
      (graphA z v-graphA z₀ v₀)+s • (graphB z w-graphB z₀ w₀) := by rw [smul_sub]; abel
  rw [he]
  have htri := norm_add_le (graphA z v-graphA z₀ v₀) (s • (graphB z w-graphB z₀ w₀))
  rw [norm_smul,Real.norm_eq_abs,hs,one_mul] at htri
  apply htri.trans
  have hA := graphA_perturbation_bound z z₀ v v₀
  have hB := graphB_perturbation_bound z z₀ w w₀
  have hcoeff : (1+|z|)/2 ≤ 5/2 := by linarith
  have h1 := mul_le_mul hcoeff hv (norm_nonneg _) (by norm_num : (0:ℝ)≤5/2)
  have h2 := mul_le_mul hcoeff hw (norm_nonneg _) (by norm_num : (0:ℝ)≤5/2)
  have h3 := mul_le_mul (div_le_div_of_nonneg_right hmove (by norm_num : (0:ℝ)≤2)) hv₀
    (norm_nonneg _) (by positivity : 0 ≤ θ/2)
  have h4 := mul_le_mul (div_le_div_of_nonneg_right hmove (by norm_num : (0:ℝ)≤2)) hw₀
    (norm_nonneg _) (by positivity : 0 ≤ θ/2)
  nlinarith

theorem graphDerivative_norm_bound (s : ℝ) (v w : Plane) (hs : |s| = 1) :
    ‖graphDerivative s v w‖ ≤ (‖v‖+‖w‖)/2 := by
  calc
    _ = (1/2:ℝ)*‖-quarterTurn v+s • quarterTurn w‖ := by rw [graphDerivative,norm_smul]; norm_num
    _ ≤ (1/2:ℝ)*(‖-quarterTurn v‖+‖s • quarterTurn w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = _ := by rw [norm_neg,norm_smul,Real.norm_eq_abs,hs,one_mul,graph_quarterTurn_norm,graph_quarterTurn_norm]; ring

theorem graphDerivative_sub (s : ℝ) (v w v₀ w₀ : Plane) :
    graphDerivative s v w-graphDerivative s v₀ w₀ = graphDerivative s (v-v₀) (w-w₀) := by
  ext i
  fin_cases i <;> simp [graphDerivative,quarterTurn] <;> ring

theorem graph_scalar_perturbation (s : ℝ) (v w v₀ w₀ e e₀ : Plane) (hs : |s| = 1)
    {δ θ ℓ : ℝ} (_hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (_hℓ : 0 ≤ ℓ)
    (he : ‖e‖ = 1) (hmove : ‖e-e₀‖ ≤ θ)
    (hv : ‖v-v₀‖ ≤ 4*δ) (hw : ‖w-w₀‖ ≤ 4*δ)
    (hv₀ : ‖v₀‖ ≤ ℓ) (hw₀ : ‖w₀‖ ≤ ℓ) :
    |inner ℝ e (graphDerivative s v w)-inner ℝ e₀ (graphDerivative s v₀ w₀)| ≤ 4*δ+θ*ℓ := by
  have hid : inner ℝ e (graphDerivative s v w)-inner ℝ e₀ (graphDerivative s v₀ w₀) =
      inner ℝ e (graphDerivative s v w-graphDerivative s v₀ w₀) +
        inner ℝ (e-e₀) (graphDerivative s v₀ w₀) := by rw [inner_sub_right,inner_sub_left]; ring
  have hder : ‖graphDerivative s v w-graphDerivative s v₀ w₀‖ ≤ 4*δ := by
    rw [graphDerivative_sub]
    exact (graphDerivative_norm_bound s _ _ hs).trans (by linarith)
  have hder₀ : ‖graphDerivative s v₀ w₀‖ ≤ ℓ :=
    (graphDerivative_norm_bound s v₀ w₀ hs).trans (by linarith)
  rw [hid]
  calc
    _ ≤ |inner ℝ e (graphDerivative s v w-graphDerivative s v₀ w₀)| +
        |inner ℝ (e-e₀) (graphDerivative s v₀ w₀)| := abs_add_le _ _
    _ ≤ ‖e‖*‖graphDerivative s v w-graphDerivative s v₀ w₀‖ +
        ‖e-e₀‖*‖graphDerivative s v₀ w₀‖ := add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ 4*δ+θ*ℓ := by
      rw [he,one_mul]
      exact add_le_add hder (mul_le_mul hmove hder₀ (norm_nonneg _) hθ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeGradient
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_four_endpoint_errors (P : Fin 4 → DyadicSquare) (x : Fin 4 → Plane)
    {δ : ℝ} (hP : ∀ a, 0 < (P a).side) (hδ : ∀ a, (P a).side ≤ δ)
    (hx : ∀ a, x a ∈ (P a).carrier) (a b : Fin 4) :
    ‖(x a-x b)-((P a).center-(P b).center)‖ ≤ 4*δ := by
  have ha := (P a).dist_le (hP a).le (hx a) ((P a).center_mem (hP a))
  have hb := (P b).dist_le (hP b).le (hx b) ((P b).center_mem (hP b))
  have he := dist_sub_sub_le (x a) (x b) (P a).center (P b).center
  rw [dist_eq_norm] at he
  exact he.trans (by linarith [hδ a,hδ b])

theorem graph_vector_nonedge_lower (R s z z₀ : ℝ) (v w v₀ w₀ : Plane)
    {S ε : ℝ} (hR : 0 ≤ R)
    (herr : ‖(graphA z v+s • graphB z w)-(graphA z₀ v₀+s • graphB z₀ w₀)‖ ≤ ε)
    (hsmall : ε ≤ S/2) (hfail : S < ‖graphA z₀ v₀+s • graphB z₀ w₀‖) :
    R*S/2 ≤ ‖R • innerSL ℝ (graphA z v+s • graphB z w)‖ := by
  have htri := norm_le_norm_add_norm_sub (graphA z v+s • graphB z w) (graphA z₀ v₀+s • graphB z₀ w₀)
  have hlo : S/2 ≤ ‖graphA z v+s • graphB z w‖ := by linarith
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hR,innerSL_apply_norm]
  nlinarith

theorem graph_scalar_nonedge_lower (R s : ℝ) (v w v₀ w₀ e e₀ : Plane)
    {S ε r : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (hr : 1/8 ≤ r)
    (herr : |inner ℝ e (graphDerivative s v w)-inner ℝ e₀ (graphDerivative s v₀ w₀)| ≤ ε)
    (hsmall : ε ≤ S/2) (hfail : S < |inner ℝ e₀ (graphDerivative s v₀ w₀)|) :
    R*S/16 ≤ |R*inner ℝ (r • e) (graphDerivative s v w)| := by
  have htri := abs_sub_abs_le_abs_sub (inner ℝ e₀ (graphDerivative s v₀ w₀))
    (inner ℝ e (graphDerivative s v w))
  rw [abs_sub_comm] at htri
  have hlo : S/2 ≤ |inner ℝ e (graphDerivative s v w)| := by linarith
  have hprod := mul_le_mul hr hlo (by positivity : (0:ℝ)≤S/2) (by linarith : 0 ≤ r)
  rw [real_inner_smul_left,abs_mul,abs_mul,abs_of_nonneg hR,abs_of_nonneg (by linarith : 0 ≤ r)]
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeErrorScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem graph_representative_error_small {sig C : ℝ} (hsig : 0 < sig) (_hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p θ ℓ : ℝ, 0 ≤ θ → 0 ≤ ℓ →
      θ ≤ graphUncappedAngularScale N sig (p-a) → ℓ ≤ C*(2:ℝ)^(-a) →
      20*(2:ℝ)^(-p)+θ*ℓ ≤ ((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))/2 := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by positivity : 0 < 20*sig) (2*(20+C))
  refine ⟨N₀,?_⟩
  intro N hN a p θ ℓ _hθ hℓ hθbound hℓbound
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := by positivity
  have h10 : 1 ≤ R^(10*sig) := Real.one_le_rpow hR (by positivity)
  have hpow : R^(30*sig) = R^(20*sig)*R^(10*sig) := by
    rw [← Real.rpow_add hRpos]
    congr 1
    ring
  have he : graphUncappedAngularScale N sig (p-a)*(C*(2:ℝ)^(-a)) = C*(2:ℝ)^(-p)*R^(10*sig) := by
    dsimp [graphUncappedAngularScale,R]
    calc
      _ = C*((2:ℝ)^(-(p-a))*(2:ℝ)^(-a))*((2:ℝ)^N)^(10*sig) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        congr 3
        ring
  have hprod := mul_le_mul hθbound hℓbound hℓ (graphUncappedAngularScale_pos N sig (p-a)).le
  rw [he] at hprod
  have hconst : 2*(20+C) ≤ R^(20*sig) := hN₀ N hN
  have hgain := mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ (2:ℝ)^(-p)*R^(10*sig))
  have hone := mul_le_mul_of_nonneg_left h10 (by positivity : 0 ≤ (2:ℝ)^(-p))
  change _ ≤ ((2:ℝ)^(-p)*R^(30*sig))/2
  rw [hpow]
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphParentDiameter
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_two_parent_diameter (X Y : DyadicSquare) {a : ℝ}
    (hX : 0 < X.side) (hY : 0 < Y.side)
    (hXa : X.side ≤ (2:ℝ)^(-a)) (hYa : Y.side ≤ (2:ℝ)^(-a))
    (hsep : dist X.center Y.center ≤ 2000*(2:ℝ)^(-a))
    {x y : Plane} (hx : x ∈ X.carrier ∪ Y.carrier) (hy : y ∈ X.carrier ∪ Y.carrier) :
    dist x y ≤ 2004*(2:ℝ)^(-a) := by
  have cross {x y : Plane} (hx : x ∈ X.carrier) (hy : y ∈ Y.carrier) :
      dist x y ≤ 2004*(2:ℝ)^(-a) := by
    have h₁ := X.dist_le hX.le hx (X.center_mem hX)
    have h₂ := Y.dist_le hY.le (Y.center_mem hY) hy
    have ht := dist_triangle4 x X.center Y.center y
    linarith
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have ht := X.dist_le hX.le hx hy
    have hp : 0 < (2:ℝ)^(-a) := by positivity
    linarith
  · exact cross hx hy
  · rw [dist_comm]; exact cross hy hx
  · have ht := Y.dist_le hY.le hx hy
    have hp : 0 < (2:ℝ)^(-a) := by positivity
    linarith

theorem dyadic_four_center_differences (X Y : DyadicSquare) (P : Fin 4 → DyadicSquare) {a : ℝ}
    (hX : 0 < X.side) (hY : 0 < Y.side)
    (hXa : X.side ≤ (2:ℝ)^(-a)) (hYa : Y.side ≤ (2:ℝ)^(-a))
    (hsep : dist X.center Y.center ≤ 2000*(2:ℝ)^(-a))
    (hP : ∀ i, 0 < (P i).side) (hparent : ∀ i, (P i).carrier ⊆ X.carrier ∪ Y.carrier)
    (i j : Fin 4) : ‖(P i).center-(P j).center‖ ≤ 2004*(2:ℝ)^(-a) := by
  simpa only [dist_eq_norm] using dyadic_two_parent_diameter X Y hX hY hXa hYa hsep
    (hparent i ((P i).center_mem (hP i))) (hparent j ((P j).center_mem (hP j)))

theorem graph_source_parent_center_bounds (distance : Bool) (X Y : DyadicSquare)
    (P : Fin 4 → DyadicSquare) {a : ℝ}
    (hX : 0 < X.side) (hY : 0 < Y.side)
    (hXa : X.side ≤ (2:ℝ)^(-a)) (hYa : Y.side ≤ (2:ℝ)^(-a))
    (hsep : distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a))
    (hP : ∀ l, 0 < (P l).side)
    (hparent : ∀ l, (P l).carrier ⊆ (graphSlotParent distance X Y l).carrier) :
    ‖(P 0).center-(P 1).center‖ ≤ 2004*(2:ℝ)^(-a) ∧
    ‖(P 2).center-(P 3).center‖ ≤ 2004*(2:ℝ)^(-a) := by
  have hm (l : Fin 4) := hparent l ((P l).center_mem (hP l))
  cases distance
  · have h₀ := hm 0
    have h₁ := hm 1
    have h₂ := hm 2
    have h₃ := hm 3
    norm_num [graphSlotParent] at h₀ h₁ h₂ h₃
    have hx := X.dist_le hX.le h₀ h₁
    have hy := Y.dist_le hY.le h₂ h₃
    rw [dist_eq_norm] at hx hy
    have hp : 0 < (2:ℝ)^(-a) := by positivity
    constructor <;> linarith
  · have hu : ∀ l, (P l).carrier ⊆ X.carrier ∪ Y.carrier := by
      intro l x hx
      have hh := hparent l hx
      by_cases hl : l = 0 ∨ l = 3
      · exact Or.inl (by simpa [graphSlotParent,hl] using hh)
      · exact Or.inr (by simpa [graphSlotParent,hl] using hh)
    exact ⟨dyadic_four_center_differences X Y P hX hY hXa hYa (hsep rfl) hP hu 0 1,
      dyadic_four_center_differences X Y P hX hY hXa hYa (hsep rfl) hP hu 2 3⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualNonedgeGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem uniform_graph_actual_nonedge_geometry {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p c₀ : ℝ, 0 < c₀ →
    ∀ P : Fin 4 → DyadicSquare, (∀ i, 0 < (P i).side) →
    (∀ i, (P i).side ≤ (2:ℝ)^(-p)) →
    ‖(P 0).center-(P 1).center‖ ≤ 2004*(2:ℝ)^(-a) →
    ‖(P 2).center-(P 3).center‖ ≤ 2004*(2:ℝ)^(-a) →
    ∀ (distance plus : Bool) (axis : ℝ) (j k : ℕ) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative distance plus axis (graphAngularScale N sig (p-a) c₀) j k q →
    ∀ (b : Fin 4 → Plane → UnitCircle → ℂ) (x : Fin 4 → Plane),
    (∀ i, x i ∈ (P i).carrier) →
    ∀ Ψ : ℝ → ℝ, (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) →
    ∀ η : Plane, ∀ z : ℝ,
    graphAmplitudePullback b x distance plus axis (graphAngularScale N sig (p-a) c₀) j k Ψ (η,z) ≠ 0 →
    let s := graphSourceSign distance plus
    let z₀ := graphRepresentativeZ distance plus q
    let e₀ := graphRepresentativeAxis distance plus q
    let v₀ := (P 0).center-(P 1).center
    let w₀ := (P 2).center-(P 3).center
    ‖(graphA z (x 0-x 1)+s • graphB z (x 2-x 3))-(graphA z₀ v₀+s • graphB z₀ w₀)‖ ≤
      graphNonedgeThreshold N sig p/2 ∧
    |inner ℝ (graphNormalizedAxis η) (graphDerivative s (x 0-x 1) (x 2-x 3))-
      inner ℝ e₀ (graphDerivative s v₀ w₀)| ≤ graphNonedgeThreshold N sig p/2 := by
  obtain ⟨N₀,hN₀⟩ := graph_representative_error_small (C := 112*2004) hsig (by norm_num)
  refine ⟨N₀,?_⟩
  intro N hN a p c₀ hc P hP hPp hc₀ hc₁ distance plus axis j k q hq b x hx Ψ hsupp η z hf
  dsimp only
  let δ := graphAngularScale N sig (p-a) c₀
  let ℓ := 2004*(2:ℝ)^(-a)
  have hδ : 0 ≤ δ := (graphAngularScale_pos N sig (p-a) hc).le
  have hℓ : 0 ≤ ℓ := by dsimp [ℓ]; positivity
  have hsmall : 20*(2:ℝ)^(-p)+(112*δ)*ℓ ≤ graphNonedgeThreshold N sig p/2 := by
    have he := hN₀ N hN a p δ (112*ℓ) hδ (by positivity) (min_le_right _ _)
      (by dsimp [ℓ]; ring_nf; exact le_rfl)
    dsimp only [graphNonedgeThreshold]
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hmove := hq.amplitude_coordinates b x hsupp hf
  have hzmove : |z-graphRepresentativeZ distance plus q| ≤ 112*δ :=
    (le_add_of_nonneg_right (dist_nonneg)).trans hmove
  have hemove : ‖graphNormalizedAxis η-graphRepresentativeAxis distance plus q‖ ≤ 112*δ := by
    rw [← dist_eq_norm]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans hmove
  have hs : |graphSourceSign distance plus| = 1 := by
    rcases graphSourceSign_cases distance plus with he | he <;> rw [he] <;> norm_num
  have hv := dyadic_four_endpoint_errors P x hP hPp hx 0 1
  have hw := dyadic_four_endpoint_errors P x hP hPp hx 2 3
  have hsupport := graphAmplitudePullback_tsupport b x distance plus axis δ j k hsupp (subset_closure hf)
  have hz : |z| ≤ 4 := abs_le.mpr hsupport.1.2
  have hlo : (1:ℝ)/8 ≤ ‖η‖ := hsupport.2
  have hη : η ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : ‖graphNormalizedAxis η‖ = 1 := by
    rw [graphNormalizedAxis_eq_all hη,norm_sourceDirection]
  constructor
  · exact (graph_vector_perturbation _ z _ _ _ _ _ hs (by positivity) (by positivity) hℓ
      hz hzmove hv hw hc₀ hc₁).trans hsmall
  · apply (graph_scalar_perturbation _ _ _ _ _ _ _ hs (by positivity) (by positivity) hℓ
      he hemove hv hw hc₀ hc₁).trans
    exact (by nlinarith [show (0:ℝ) ≤ (2:ℝ)^(-p) by positivity] :
      4*(2:ℝ)^(-p)+(112*δ)*ℓ ≤ 20*(2:ℝ)^(-p)+(112*δ)*ℓ).trans hsmall

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSliceDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem graph_z_slice_derivative_le {f : (Plane × ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (η : Plane) (z : ℝ) (n : ℕ) :
    ‖iteratedDeriv n (fun t => f (η,t)) z‖ ≤ ‖iteratedFDeriv ℝ n f (η,z)‖ := by
  let g : (Plane × ℝ) → ℂ := fun p => f (p+(η,0))
  let L : ℝ →L[ℝ] (Plane × ℝ) := ContinuousLinearMap.inr ℝ Plane ℝ
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun t => f (η,t)) = g ∘ L := by funext t; simp [g,L]
  rw [he,← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    L.iteratedFDeriv_comp_right hg z (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hn : ‖L‖ = 1 := ContinuousLinearMap.norm_inr ℝ Plane ℝ
  simp only [hn,Finset.prod_const_one,mul_one]
  dsimp only [g]
  rw [iteratedFDeriv_comp_add_right]
  simp [L]

theorem graph_z_slice_tsupport {f : (Plane × ℝ) → ℂ}
    (hs : tsupport f ⊆ graphAmplitudeCompact) (η : Plane) :
    tsupport (fun t => f (η,t)) ⊆ Icc (-4:ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro z hz
  exact (hs (subset_closure hz)).1.2

theorem GraphDerivativeBound.z_slice {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (η : Plane) :
    ContDiff ℝ ∞ (fun z => f (η,z)) ∧
      tsupport (fun z => f (η,z)) ⊆ Icc (-4:ℝ) 4 ∧
      ∀ j ≤ n, ∀ z, ‖iteratedDeriv j (fun t => f (η,t)) z‖ ≤ C*D^j := by
  have hg := hf.global_smooth hs
  refine ⟨hg.comp (contDiff_const.prodMk contDiff_id),graph_z_slice_tsupport hs η,?_⟩
  intro j hj z
  exact (graph_z_slice_derivative_le hg η z j).trans (hf.global_bound hs hC hD j hj (η,z))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphZNonstationary
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem compact_affine_phase_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Icc (-4:ℝ) 4) {C D τ : ℝ} (hτ : τ ≠ 0) (b : ℝ) (n : ℕ)
    (hb : ∀ z, ‖iteratedDeriv n f z‖ ≤ C*D^n) :
    ‖∫ z : ℝ, Complex.exp (Complex.I*((b+τ*z):ℂ))*f z‖ ≤ 8*C*D^n/|τ|^n := by
  let ξ := -τ/(2*Real.pi)
  have hξ : ξ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hτ) (by positivity)
  have he := compact_linear_phase_bound hf hs (by norm_num) hξ n hb
  have hphase (z : ℝ) : Complex.exp (Complex.I*((b+τ*z):ℂ))*f z =
      Complex.exp (Complex.I*(b:ℂ)) *
        (Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(z:ℂ)*(ξ:ℂ))*f z) := by
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    dsimp [ξ]
    push_cast
    field_simp
  simp_rw [hphase]
  rw [integral_const_mul,norm_mul]
  have hnorm : ‖Complex.exp (Complex.I*(b:ℂ))‖ = 1 := by
    rw [mul_comm Complex.I]
    exact Complex.norm_exp_ofReal_mul_I b
  rw [hnorm,one_mul]
  apply he.trans_eq
  have hd : (2*Real.pi)^n*‖ξ‖^n = |τ|^n := by
    rw [← mul_pow]
    congr 1
    dsimp [ξ]
    rw [abs_div,abs_neg,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    field_simp
  rw [hd]
  ring

theorem graph_z_nonstationary_bound {f : (Plane × ℝ) → ℂ} {C D : ℝ} (n : ℕ)
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (R s : ℝ) (v w η : Plane)
    (hτ : R*inner ℝ η (graphDerivative s v w) ≠ 0) :
    ‖∫ z : ℝ, Complex.exp (Complex.I*((R*inner ℝ η (graphA z v+s • graphB z w)):ℂ))*f (η,z)‖ ≤
      8*C*D^n/|R*inner ℝ η (graphDerivative s v w)|^n := by
  obtain ⟨hsm,hsupp,hder⟩ := hf.z_slice hs hC hD η
  have he := compact_affine_phase_bound hsm hsupp hτ
    (R*inner ℝ η ((1/2:ℝ) • (v+s • w))) n (hder n le_rfl)
  have hphase (z : ℝ) : R*inner ℝ η (graphA z v+s • graphB z w) =
      R*inner ℝ η ((1/2:ℝ) • (v+s • w)) + (R*inner ℝ η (graphDerivative s v w))*z := by
    simp only [graph_phase_affine,inner_add_right,real_inner_smul_right]
    ring
  simpa only [← Complex.ofReal_mul,← Complex.ofReal_add,hphase] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphZNonedgeScale
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_z_nonedge_scale_bound {f : (Plane × ℝ) → ℂ} {C : ℝ} (n N : ℕ)
    (sig v p s : ℝ) (x y η : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (hτ : ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)))/16 ≤
      |(2:ℝ)^v*inner ℝ η (graphDerivative s x y)|) :
    ‖∫ z : ℝ, Complex.exp (Complex.I*Complex.ofReal ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      8*C*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  let τ := (2:ℝ)^v*inner ℝ η (graphDerivative s x y)
  let G := (2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))
  let E := graphNonedgeDerivativeScale N sig (v-p)
  have hG : 0 < G := by dsimp [G]; positivity
  have hE : 0 < E := by dsimp [E,graphNonedgeDerivativeScale]; positivity
  have hτpos : 0 < |τ| := (by positivity : 0 < G/16).trans_le hτ
  have hτne : τ ≠ 0 := abs_pos.mp hτpos
  have he := graph_z_nonstationary_bound n hf hs hC hE.le ((2:ℝ)^v) s x y η hτne
  have hratio : E/|τ| ≤ 16*((2:ℝ)^N)^(-26*sig) := by
    calc
      _ ≤ E/(G/16) := div_le_div_of_nonneg_left hE.le (by positivity) hτ
      _ = 16*(E/G) := by field_simp
      _ = _ := by rw [graph_nonedge_scale_gain]
  calc
    _ ≤ 8*C*E^n/|τ|^n := by simpa only [Complex.ofReal_mul] using he
    _ = 8*C*(E/|τ|)^n := by rw [div_pow]; ring
    _ ≤ 8*C*(16*((2:ℝ)^N)^(-26*sig))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio _) (by positivity)
    _ = 8*C*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphZIntegratedNonedge
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_phase_amplitude_continuous {f : (Plane × ℝ) → ℂ}
    (hf : Continuous f) (R s : ℝ) (x y : Plane) :
    Continuous (fun q : Plane × ℝ =>
      Complex.exp (Complex.I*Complex.ofReal (R*inner ℝ q.1
        (graphA q.2 x+s • graphB q.2 y)))*f q) := by
  apply Continuous.mul _ hf
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Complex.continuous_ofReal.comp
  apply continuous_const.mul
  apply continuous_fst.inner
  unfold graphA graphB
  fun_prop

theorem graph_z_integrated_nonedge_bound {f : (Plane × ℝ) → ℂ} {C : ℝ}
    (n N : ℕ) (sig v p s : ℝ) (x y : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (hτ : ∀ η : Plane, (∃ z, f (η,z) ≠ 0) →
      ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)))/16 ≤
        |(2:ℝ)^v*inner ℝ η (graphDerivative s x y)|) :
    ‖∫ z : ℝ, ∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
      ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      (8*C*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ))) *
        volume.real (Metric.closedBall (0:Plane) 8) := by
  let F : Plane → ℝ → ℂ := fun η z => Complex.exp (Complex.I*Complex.ofReal
    ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)
  have hc : Continuous F.uncurry :=
    graph_phase_amplitude_continuous (hf.global_smooth hs).continuous _ _ _ _
  have hcompact : HasCompactSupport f :=
    graphAmplitudeCompact_isCompact.of_isClosed_subset isClosed_closure hs
  have hFc : HasCompactSupport F.uncurry := hcompact.mul_left
  have hswap := integral_integral_swap_of_hasCompactSupport hc hFc
    (μ := (volume : Measure Plane)) (ν := (volume : Measure ℝ))
  change ‖∫ z, ∫ η, F η z‖ ≤ _
  rw [← hswap]
  have hzero (η : Plane) (hη : η ∉ Metric.closedBall (0:Plane) 8) :
      (∫ z, F η z) = 0 := by
    have hz (z : ℝ) : f (η,z) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hη (hs hm).1.1
    simp [F,hz]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hb (η : Plane) : ‖∫ z, F η z‖ ≤
      8*C*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
    by_cases hn : ∃ z, f (η,z) ≠ 0
    · exact graph_z_nonedge_scale_bound n N sig v p s x y η hf hs hC (hτ η hn)
    · have hz (z : ℝ) : f (η,z) = 0 := by simpa using not_exists.mp hn z
      simp only [F,hz,mul_zero,integral_zero,norm_zero]
      positivity
  have : Fact (volume (Metric.closedBall (0:Plane) 8) < ⊤) :=
    ⟨(isCompact_closedBall (0:Plane) 8).measure_lt_top⟩
  have he := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Metric.closedBall (0:Plane) 8))
    (Filter.Eventually.of_forall hb)
  simpa only [Measure.real,Measure.restrict_apply_univ] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphEtaNonstationary
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff FourierTransform

theorem plane_compact_linear_phase_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Metric.closedBall (0:Plane) 8) (n : ℕ) {C D : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*D^n) (q : Plane) (hq : q ≠ 0) :
    ‖∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal (inner ℝ η q))*f η‖ ≤
      (C*D^n*volume.real (Metric.closedBall (0:Plane) 8))/‖q‖^n := by
  let ξ := (-(2*Real.pi)⁻¹) • q
  have hξ : ξ ≠ 0 := smul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by positivity))) hq
  have he := plane_compact_fourier_bound hf hs n hb ξ hξ
  have hphase : 𝓕 f ξ = ∫ η : Plane,
      Complex.exp (Complex.I*Complex.ofReal (inner ℝ η q))*f η := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with η
    simp only [ξ,real_inner_smul_right,smul_eq_mul]
    congr 2
    push_cast
    field_simp
  rw [hphase] at he
  have hd : (2*Real.pi)^n*‖ξ‖^n = ‖q‖^n := by
    rw [← mul_pow]
    congr 1
    simp [ξ,norm_smul,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    field_simp
  simpa only [hd] using he

theorem graph_eta_slice_derivative_le {f : (Plane × ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (η : Plane) (z : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun e => f (e,z)) η‖ ≤ ‖iteratedFDeriv ℝ n f (η,z)‖ := by
  let g : (Plane × ℝ) → ℂ := fun p => f (p+(0,z))
  let L : Plane →L[ℝ] (Plane × ℝ) := ContinuousLinearMap.inl ℝ Plane ℝ
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun e => f (e,z)) = g ∘ L := by funext e; simp [g,L]
  rw [he,L.iteratedFDeriv_comp_right hg η (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hn : ‖L‖ = 1 := ContinuousLinearMap.norm_inl ℝ Plane ℝ
  simp only [hn,Finset.prod_const_one,mul_one]
  dsimp only [g]
  rw [iteratedFDeriv_comp_add_right]
  simp [L]

theorem graph_eta_nonstationary_bound {f : (Plane × ℝ) → ℂ} {C D : ℝ} (n : ℕ)
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (R s z : ℝ) (x y : Plane)
    (hq : R • (graphA z x+s • graphB z y) ≠ 0) :
    ‖∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
      (R*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      (C*D^n*volume.real (Metric.closedBall (0:Plane) 8))/
        ‖R • (graphA z x+s • graphB z y)‖^n := by
  have hg := hf.global_smooth hs
  have hs' : tsupport (fun η => f (η,z)) ⊆ Metric.closedBall (0:Plane) 8 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro η hη
    exact (hs (subset_closure hη)).1.1
  have he := plane_compact_linear_phase_bound
    (hg.comp (contDiff_id.prodMk contDiff_const)) hs' n
    (fun η => (graph_eta_slice_derivative_le hg η z n).trans
      (hf.global_bound hs hC hD n le_rfl (η,z)))
    (R • (graphA z x+s • graphB z y)) hq
  simpa only [real_inner_smul_right, Function.comp_apply, id_eq] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphEtaIntegratedNonedge
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_eta_nonedge_scale_bound {f : (Plane × ℝ) → ℂ} {C : ℝ} (n N : ℕ)
    (sig v p s z : ℝ) (x y : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (hq : ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)))/2 ≤
      ‖((2:ℝ)^v) • (graphA z x+s • graphB z y)‖) :
    ‖∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
      ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      C*volume.real (Metric.closedBall (0:Plane) 8)*2^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  let q := ((2:ℝ)^v) • (graphA z x+s • graphB z y)
  let G := (2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))
  let E := graphNonedgeDerivativeScale N sig (v-p)
  have hG : 0 < G := by dsimp [G]; positivity
  have hE : 0 < E := by dsimp [E,graphNonedgeDerivativeScale]; positivity
  have hqpos : 0 < ‖q‖ := (by positivity : 0 < G/2).trans_le hq
  have hqne : q ≠ 0 := norm_pos_iff.mp hqpos
  have he := graph_eta_nonstationary_bound n hf hs hC hE.le ((2:ℝ)^v) s z x y hqne
  have hratio : E/‖q‖ ≤ 2*((2:ℝ)^N)^(-26*sig) := by
    calc
      _ ≤ E/(G/2) := div_le_div_of_nonneg_left hE.le (by positivity) hq
      _ = 2*(E/G) := by field_simp
      _ = _ := by rw [graph_nonedge_scale_gain]
  calc
    _ ≤ (C*E^n*volume.real (Metric.closedBall (0:Plane) 8))/‖q‖^n := he
    _ = (C*volume.real (Metric.closedBall (0:Plane) 8))*(E/‖q‖)^n := by
      rw [div_pow]; ring
    _ ≤ (C*volume.real (Metric.closedBall (0:Plane) 8))*(2*((2:ℝ)^N)^(-26*sig))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio _) (by positivity)
    _ = C*volume.real (Metric.closedBall (0:Plane) 8)*2^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
      ring

theorem graph_eta_integrated_nonedge_bound {f : (Plane × ℝ) → ℂ} {C : ℝ}
    (n N : ℕ) (sig v p s : ℝ) (x y : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (hq : ∀ z : ℝ, (∃ η, f (η,z) ≠ 0) →
      ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)))/2 ≤
        ‖((2:ℝ)^v) • (graphA z x+s • graphB z y)‖) :
    ‖∫ z : ℝ, ∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
      ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      8*C*volume.real (Metric.closedBall (0:Plane) 8)*2^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  let F : ℝ → ℂ := fun z => ∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
    ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)
  have hzero (z : ℝ) (hz : z ∉ Icc (-4:ℝ) 4) : F z = 0 := by
    have he (η : Plane) : f (η,z) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hz (hs hm).1.2
    simp [F,he]
  have hb (z : ℝ) : ‖F z‖ ≤
      C*volume.real (Metric.closedBall (0:Plane) 8)*2^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
    by_cases hn : ∃ η, f (η,z) ≠ 0
    · exact graph_eta_nonedge_scale_bound n N sig v p s z x y hf hs hC (hq z hn)
    · have hz (η : Plane) : f (η,z) = 0 := by simpa using not_exists.mp hn η
      simp only [F,hz,mul_zero,integral_zero,norm_zero]
      positivity
  change ‖∫ z, F z‖ ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have he := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (s := Icc (-4:ℝ) 4) (by simp) (Filter.Eventually.of_forall hb)
  apply he.trans_eq
  simp [Measure.real,Real.volume_Icc]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeIntegralErrors
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphPointIntegral_nonedge_of_errors {f : Plane × ℝ → ℂ} {C : ℝ}
    (n N : ℕ) (sig v p s z₀ : ℝ) (x y v₀ w₀ e₀ : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (herr : ∀ η z, f (η,z) ≠ 0 →
      ‖(graphA z x+s • graphB z y)-(graphA z₀ v₀+s • graphB z₀ w₀)‖ ≤ graphNonedgeThreshold N sig p/2 ∧
      |inner ℝ (graphNormalizedAxis η) (graphDerivative s x y)-
        inner ℝ e₀ (graphDerivative s v₀ w₀)| ≤ graphNonedgeThreshold N sig p/2)
    (hfail : GraphNonedge N sig p s z₀ e₀ v₀ w₀) :
    ‖graphPointIntegral f v s x y‖ ≤
      8*C*volume.real (Metric.closedBall (0:Plane) 8)*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  rcases hfail with hvec | hscalar
  · have hg : ∀ z : ℝ, (∃ η, f (η,z) ≠ 0) →
        ((2:ℝ)^v*graphNonedgeThreshold N sig p)/2 ≤ ‖((2:ℝ)^v) • (graphA z x+s • graphB z y)‖ := by
      intro z hz
      obtain ⟨η,hη⟩ := hz
      have he := graph_vector_nonedge_lower ((2:ℝ)^v) s z z₀ x y v₀ w₀ (by positivity)
        (herr η z hη).1 le_rfl hvec
      simpa only [norm_smul,innerSL_apply_norm] using he
    have hi := graph_eta_integrated_nonedge_bound n N sig v p s x y hf hs hC hg
    apply hi.trans
    have hp : (2:ℝ)^n ≤ 16^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
  · have hg : ∀ η : Plane, (∃ z, f (η,z) ≠ 0) →
        ((2:ℝ)^v*graphNonedgeThreshold N sig p)/16 ≤ |(2:ℝ)^v*inner ℝ η (graphDerivative s x y)| := by
      intro η hη
      obtain ⟨z,hz⟩ := hη
      have hlo : (1:ℝ)/8 ≤ ‖η‖ := (hs (subset_closure hz)).2
      have hn : η ≠ 0 := norm_pos_iff.mp (by linarith)
      have he := graph_scalar_nonedge_lower ((2:ℝ)^v) s x y v₀ w₀ (graphNormalizedAxis η) e₀
        (by positivity) (by dsimp [graphNonedgeThreshold]; positivity) hlo (herr η z hz).2 le_rfl hscalar
      have hid : ‖η‖ • graphNormalizedAxis η = η := by
        rw [graphNormalizedAxis,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn),one_smul]
      rwa [hid] at he
    have hi := graph_z_integrated_nonedge_bound n N sig v p s x y hf hs hC hg
    exact hi.trans_eq (by ring)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphInheritedNonedge
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_graph_nonedge_bound {sig : ℝ} (hsig : 0 < sig) (K n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ l, ‖h l (x l)‖ ≤ 1) →
    ∀ a p v : ℝ, 0 ≤ v-p → p-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) →
    ∀ (distance plus : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ P : Fin 4 → DyadicSquare, (∀ l, 0 < (P l).side) →
    (∀ l, (P l).side ≤ (2:ℝ)^(-p)) →
    (∀ l, (P l).carrier ⊆ (graphSlotParent distance X Y l).carrier) → (∀ l, x l ∈ (P l).carrier) →
    ∀ (axis : ℝ) (j₁ j₂ : ℕ) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ q →
    GraphNonedge N sig p (graphSourceSign distance plus) (graphRepresentativeZ distance plus q)
      (graphRepresentativeAxis distance plus q) ((P 0).center-(P 1).center) ((P 2).center-(P 3).center) →
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
      N lam sig J i (h l)
    ‖graphPointIntegral
      (graphAmplitudePullback b x distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ Ψ)
      v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)‖ ≤
      8*A*volume.real (Metric.closedBall (0:Plane) 8)*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  obtain ⟨A,hA,N₁,hamp⟩ := uniform_actual_graph_amplitude_E hsig K n hΨ hc hcap
  obtain ⟨N₂,hgeom⟩ := uniform_graph_actual_nonedge_geometry hsig
  refine ⟨A,hA,max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx a p v hu ht hLu
    distance plus X Y hX hY hXa hYa hsep P hP hPp hparent hxp axis j₁ j₂ q hq hfail
  let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
    N lam sig J i (h l)
  have hf := hamp N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
    (p-a) (v-p) hu ht hLu distance plus axis j₁ j₂
  have hs := graphAmplitudePullback_tsupport b x distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ hsupp
  have hcent := graph_source_parent_center_bounds distance X Y P hX hY hXa hYa hsep hP hparent
  have hg := hgeom N ((le_max_right _ _).trans hN) a p c₀ hc
    P hP hPp hcent.1 hcent.2 distance plus axis j₁ j₂ q hq b x hxp Ψ hsupp
  exact graphPointIntegral_nonedge_of_errors n N sig v p _ _ _ _ _ _ _ hf hs hA hg hfail

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphInheritedNonedgePower
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_graph_nonedge_power_oai {sig : ℝ} (hsig : 0 < sig) (K : ℕ) (T : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ l, ‖h l (x l)‖ ≤ 1) →
    ∀ a p v : ℝ, 0 ≤ v-p → p-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) →
    ∀ (distance plus : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ P : Fin 4 → DyadicSquare, (∀ l, 0 < (P l).side) →
    (∀ l, (P l).side ≤ (2:ℝ)^(-p)) →
    (∀ l, (P l).carrier ⊆ (graphSlotParent distance X Y l).carrier) → (∀ l, x l ∈ (P l).carrier) →
    ∀ (axis : ℝ) (j₁ j₂ : ℕ) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ q →
    GraphNonedge N sig p (graphSourceSign distance plus) (graphRepresentativeZ distance plus q)
      (graphRepresentativeAxis distance plus q) ((P 0).center-(P 1).center) ((P 2).center-(P 3).center) →
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
      N lam sig J i (h l)
    ‖graphPointIntegral
      (graphAmplitudePullback b x distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ Ψ)
      v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)‖ ≤
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((T+1)/(26*sig))
  have hn' : T+1 < 26*sig*(n:ℝ) := by
    simpa only [mul_comm (n:ℝ) (26*sig)] using
      (div_lt_iff₀ (by positivity : (0:ℝ) < 26*sig)).mp hn
  have hgap : 0 < 26*sig*(n:ℝ)-T := by linarith
  obtain ⟨A,hA,N₁,hbound⟩ := uniform_actual_graph_nonedge_bound hsig K n hΨ hsupp hc hcap
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hgap
    (8*A*volume.real (Metric.closedBall (0:Plane) 8)*16^n)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx a p v hu ht hLu
    distance plus X Y hX hY hXa hYa hsep P hP hPp hparent hxp axis j₁ j₂ q hq hfail
  have hi := hbound N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
    a p v hu ht hLu distance plus X Y hX hY hXa hYa hsep P hP hPp hparent hxp axis j₁ j₂ q hq hfail
  apply hi.trans
  calc
    _ ≤ ((2:ℝ)^N)^(26*sig*(n:ℝ)-T)*((2:ℝ)^N)^(-26*sig*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN)) (by positivity)
    _ = ((2:ℝ)^N)^(-T) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_graph_nonedge_power_oai := @OAI.PlanarFalconer.uniform_actual_graph_nonedge_power_oai
