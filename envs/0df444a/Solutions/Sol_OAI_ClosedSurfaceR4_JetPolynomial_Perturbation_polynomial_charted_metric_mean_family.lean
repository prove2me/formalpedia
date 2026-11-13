-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:48:56.131545+00:00
-- url     : https://prove2.me/submissions/f41e0d7d-d17a-40e5-9906-d363831c023b

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Definitions.Def_OAIQ249SI012

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_dot {n : ℕ} {F G : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q ⬝ᵥ G q) p = coordDeriv v F p ⬝ᵥ G p + F p ⬝ᵥ coordDeriv v G p := by
  have hf (i : Fin n) := ((ContinuousLinearMap.proj i : Ambient n →L[ℝ] ℂ).hasFDerivAt.comp p
    hF.hasFDerivAt)
  have hg (i : Fin n) := ((ContinuousLinearMap.proj i : Ambient n →L[ℝ] ℂ).hasFDerivAt.comp p
    hG.hasFDerivAt)
  have hs := (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => (hf i).fun_mul (hg i)).fderiv
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply] at hs
  unfold coordDeriv dotProduct
  rw [hs]
  simp only [sum_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

section Gram
variable {n : ℕ}

lemma second_dot_split (X Y W Z : Ambient n) :
    W ⬝ᵥ Z = liftX X Y (X ⬝ᵥ W) (Y ⬝ᵥ W) * (X ⬝ᵥ Z) +
      liftY X Y (X ⬝ᵥ W) (Y ⬝ᵥ W) * (Y ⬝ᵥ Z) + normalPart X Y W ⬝ᵥ Z := by
  simp only [normalPart, tangentLift, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

lemma dot_normal_tangentLift (X Y B : Ambient n) (hX : X ⬝ᵥ B = 0) (hY : Y ⬝ᵥ B = 0)
    (ux uy : ℂ) : B ⬝ᵥ tangentLift X Y ux uy = 0 := by
  simp only [tangentLift, dotProduct_add, dotProduct_smul, smul_eq_mul,
    dotProduct_comm B X, dotProduct_comm B Y, hX, hY, mul_zero, add_zero]

lemma normalPart_dot_reconstruct (X Y W Z V : Ambient n) (hD : gramDet X Y ≠ 0)
    (ux uy : ℂ) (hZ : Z = tangentLift X Y ux uy + V) :
    normalPart X Y W ⬝ᵥ Z = normalPart X Y W ⬝ᵥ V := by
  rw [hZ, dotProduct_add, dot_normal_tangentLift X Y _
    (dot_normalPart_left X Y W hD) (dot_normalPart_right X Y W hD), zero_add]

end Gram

section CoordinateCalculus
variable {n : ℕ}

lemma contDiff_coordDeriv {G : Field n} (hG : ContDiff ℝ ∞ G) (v : Base) :
    ContDiff ℝ ∞ (coordDeriv v G) :=
  (hG.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

lemma second_coordDeriv {G : Field n} {p : Base}
    (hG : DifferentiableAt ℝ (fderiv ℝ G) p) (v w : Base) :
    coordDeriv v (coordDeriv w G) p = fderiv ℝ (fderiv ℝ G) p v w := by
  have h := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ G q) w) p) v = _
  rw [h]
  simp

lemma second_coordDeriv_comm {G : Field n} (hG : ContDiff ℝ ∞ G)
    (p v w : Base) : coordDeriv v (coordDeriv w G) p = coordDeriv w (coordDeriv v G) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) p :=
    ((hG.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  rw [second_coordDeriv hd, second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hG.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w



lemma linearizedMetric_covector {G Z : Field n} (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    linearizedMetric G Z v w p =
      coordDeriv v (covector G Z w) p + coordDeriv w (covector G Z v) p -
        2 * (coordDeriv v (coordDeriv w G) p ⬝ᵥ Z p) := by
  unfold covector
  rw [partial_dot (((contDiff_coordDeriv hG w).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt) hZ,
    partial_dot (((contDiff_coordDeriv hG v).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt) hZ,
    second_coordDeriv_comm hG p w v]
  unfold linearizedMetric
  ring

lemma linearizedMetric_connection {G Z : Field n} (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    linearizedMetric G Z v w p =
      coordDeriv v (covector G Z w) p + coordDeriv w (covector G Z v) p -
      2 * (connectionX G v w p * covector G Z dx p +
        connectionY G v w p * covector G Z dy p) - 2 * (secondForm G v w p ⬝ᵥ Z p) := by
  rw [linearizedMetric_covector hG hZ]
  unfold connectionX connectionY secondForm covector
  rw [second_dot_split (coordDeriv dx G p) (coordDeriv dy G p)
    (coordDeriv v (coordDeriv w G) p) (Z p)]
  ring

lemma covector_reconstruct {G V : Field n} {ux uy : Scalar} {p : Base}
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hX : coordDeriv dx G p ⬝ᵥ V p = 0) (hY : coordDeriv dy G p ⬝ᵥ V p = 0) :
    let Z : Field n := fun q => tangentLift (coordDeriv dx G q) (coordDeriv dy G q) (ux q) (uy q) + V q
    covector G Z dx p = ux p ∧ covector G Z dy p = uy p := by
  simp only [covector, dotProduct_add, dot_tangentLift_left _ _ hD,
    dot_tangentLift_right _ _ hD, hX, hY, add_zero, and_self]

end CoordinateCalculus

section Phase
variable {n : ℕ}


lemma conjugatedMetric_connection (τ : ℝ) {G Z : Field n}
    (hG : ContDiff ℝ ∞ G) {p : Base} (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    conjugatedMetric τ G Z v w p =
      coordDeriv v (covector G Z w) p + coordDeriv w (covector G Z v) p -
      2 * (connectionX G v w p * covector G Z dx p +
        connectionY G v w p * covector G Z dy p) + (Complex.I / (τ : ℂ)) *
      ((v.1 : ℂ) * covector G Z w p + (w.1 : ℂ) * covector G Z v p) -
      2 * (secondForm G v w p ⬝ᵥ Z p) := by
  unfold conjugatedMetric
  rw [linearizedMetric_connection hG hZ]
  ring

end Phase

section Elimination
variable {n : ℕ}


lemma covector_reconstruct_eventually {G V : Field n} {ux uy : Scalar} {p : Base}
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0) :
    covector G (reconstruct G ux uy V) dx =ᶠ[nhds p] ux ∧
      covector G (reconstruct G ux uy V) dy =ᶠ[nhds p] uy := by
  have hh : ∀ᶠ q in nhds p, covector G (reconstruct G ux uy V) dx q = ux q ∧
      covector G (reconstruct G ux uy V) dy q = uy q := by
    filter_upwards [hD, hX, hY] with q hDq hXq hYq
    exact covector_reconstruct hDq hXq hYq
  exact ⟨hh.mono fun _ h => h.1, hh.mono fun _ h => h.2⟩

lemma secondForm_dot_reconstruct {G V : Field n} {ux uy : Scalar} {p : Base}
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    secondForm G v w p ⬝ᵥ reconstruct G ux uy V p = secondForm G v w p ⬝ᵥ V p := by
  exact normalPart_dot_reconstruct _ _ _ _ _ hD (ux p) (uy p) rfl

lemma conjugatedMetric_reconstruct_xx (τ : ℝ) {G V : Field n} {ux uy : Scalar}
    (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (reconstruct G ux uy V) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0) :
    conjugatedMetric τ G (reconstruct G ux uy V) dx dx p =
      2 * ((Complex.I / (τ : ℂ)) * ux p + coordDeriv dx ux p -
        connectionTerm G ux uy dx dx p - secondForm G dx dx p ⬝ᵥ V p) := by
  obtain ⟨hx, hy⟩ := covector_reconstruct_eventually hD hX hY (ux := ux) (uy := uy)
  rw [conjugatedMetric_connection τ hG hZ, secondForm_dot_reconstruct hD.self_of_nhds]
  simp only [coordDeriv, hx.fderiv_eq, hx.self_of_nhds,
    hy.self_of_nhds, connectionTerm]
  simp only [dx, Complex.ofReal_one, one_mul]
  ring

lemma conjugatedMetric_reconstruct_xy (τ : ℝ) {G V : Field n} {ux uy : Scalar}
    (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (reconstruct G ux uy V) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0) :
    conjugatedMetric τ G (reconstruct G ux uy V) dx dy p =
      (Complex.I / (τ : ℂ)) * uy p + coordDeriv dx uy p + coordDeriv dy ux p -
        2 * connectionTerm G ux uy dx dy p - 2 * (secondForm G dx dy p ⬝ᵥ V p) := by
  obtain ⟨hx, hy⟩ := covector_reconstruct_eventually hD hX hY (ux := ux) (uy := uy)
  rw [conjugatedMetric_connection τ hG hZ, secondForm_dot_reconstruct hD.self_of_nhds]
  simp only [coordDeriv, hx.fderiv_eq, hy.fderiv_eq, hx.self_of_nhds,
    hy.self_of_nhds, connectionTerm]
  simp only [dx, dy, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero]
  ring

lemma conjugatedMetric_reconstruct_yy (τ : ℝ) {G V : Field n} {ux uy : Scalar}
    (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (reconstruct G ux uy V) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0) :
    conjugatedMetric τ G (reconstruct G ux uy V) dy dy p =
      2 * (coordDeriv dy uy p - connectionTerm G ux uy dy dy p -
        secondForm G dy dy p ⬝ᵥ V p) := by
  obtain ⟨hx, hy⟩ := covector_reconstruct_eventually hD hX hY (ux := ux) (uy := uy)
  rw [conjugatedMetric_connection τ hG hZ, secondForm_dot_reconstruct hD.self_of_nhds]
  simp only [coordDeriv, hy.fderiv_eq, hx.self_of_nhds,
    hy.self_of_nhds, connectionTerm]
  simp only [dy, Complex.ofReal_zero, zero_mul, add_zero, mul_zero]
  ring


lemma dot_normalElimination (G V₀ : Field n) (ux uy hyy : Scalar) (p v w : Base) :
    secondForm G v w p ⬝ᵥ normalElimination G V₀ ux uy hyy p =
      secondForm G v w p ⬝ᵥ V₀ p + secondRatio G v w p *
        (coordDeriv dy uy p - connectionTerm G ux uy dy dy p - hyy p / 2) := by
  simp only [normalElimination, dotProduct_add, dotProduct_smul, smul_eq_mul, secondRatio]
  ring

lemma dot_normalElimination_yy (G V₀ : Field n) (ux uy hyy : Scalar) (p : Base)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0)
    (hV : goodSecond G p ⬝ᵥ V₀ p = 0) :
    secondForm G dy dy p ⬝ᵥ normalElimination G V₀ ux uy hyy p =
      coordDeriv dy uy p - connectionTerm G ux uy dy dy p - hyy p / 2 := by
  rw [dot_normalElimination]
  change goodSecond G p ⬝ᵥ V₀ p +
    (goodSecond G p ⬝ᵥ goodSecond G p) / (goodSecond G p ⬝ᵥ goodSecond G p) * _ = _
  rw [hV, div_self hb, one_mul, zero_add]

lemma normalElimination_perp {G V₀ : Field n} {ux uy hyy : Scalar} {p : Base}
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hX : coordDeriv dx G p ⬝ᵥ V₀ p = 0)
    (hY : coordDeriv dy G p ⬝ᵥ V₀ p = 0) :
    coordDeriv dx G p ⬝ᵥ normalElimination G V₀ ux uy hyy p = 0 ∧
    coordDeriv dy G p ⬝ᵥ normalElimination G V₀ ux uy hyy p = 0 := by
  simp only [normalElimination, dotProduct_add, dotProduct_smul, smul_eq_mul, hX, hY,
    goodSecond, secondForm, dot_normalPart_left _ _ _ hD, dot_normalPart_right _ _ _ hD,
    mul_zero, zero_add, and_self]

lemma normalElimination_perp_eventually {G V₀ : Field n} {ux uy hyy : Scalar} {p : Base}
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V₀ q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V₀ q = 0) :
    (∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ normalElimination G V₀ ux uy hyy q = 0) ∧
    (∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ normalElimination G V₀ ux uy hyy q = 0) := by
  have hh : ∀ᶠ q in nhds p,
      coordDeriv dx G q ⬝ᵥ normalElimination G V₀ ux uy hyy q = 0 ∧
      coordDeriv dy G q ⬝ᵥ normalElimination G V₀ ux uy hyy q = 0 := by
    filter_upwards [hD, hX, hY] with q hd hx hy
    exact normalElimination_perp hd hx hy
  exact ⟨hh.mono fun _ h => h.1, hh.mono fun _ h => h.2⟩



theorem normalElimination_residual (τ : ℝ) {G V₀ : Field n} {ux uy hxx hxy hyy : Scalar}
    (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (reconstruct G ux uy (normalElimination G V₀ ux uy hyy)) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V₀ q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V₀ q = 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0)
    (hV : goodSecond G p ⬝ᵥ V₀ p = 0) :
    let Z := reconstruct G ux uy (normalElimination G V₀ ux uy hyy)
    (conjugatedMetric τ G Z dx dx p - hxx p =
      2 * ((Complex.I / (τ : ℂ)) * ux p + reducedLx G ux uy p - reducedKx G V₀ hxx hyy p)) ∧
    (conjugatedMetric τ G Z dx dy p - hxy p =
      (Complex.I / (τ : ℂ)) * uy p + reducedLy G ux uy p - reducedKy G V₀ hxy hyy p) ∧
    conjugatedMetric τ G Z dy dy p = hyy p := by
  obtain ⟨hx, hy⟩ := normalElimination_perp_eventually hD hX hY
    (ux := ux) (uy := uy) (hyy := hyy)
  constructor
  · rw [conjugatedMetric_reconstruct_xx τ hG hZ hD hx hy, dot_normalElimination]
    unfold reducedLx reducedKx
    ring
  constructor
  · rw [conjugatedMetric_reconstruct_xy τ hG hZ hD hx hy, dot_normalElimination]
    unfold reducedLy reducedKy
    ring
  · rw [conjugatedMetric_reconstruct_yy τ hG hZ hD hx hy,
      dot_normalElimination_yy G V₀ ux uy hyy p hb hV]
    ring

end Elimination

section Parametrix
variable {n : ℕ}


lemma conjugating_inverse {τ : ℝ} (hτ : τ ≠ 0) :
    (Complex.I / (τ : ℂ)) * ((τ : ℂ) / Complex.I) = 1 := by
  have htc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  field_simp

lemma firstParametrix_residual {τ : ℝ} (hτ : τ ≠ 0) {G V₀ : Field n}
    {hxx hxy hyy : Scalar} (hG : ContDiff ℝ ∞ G) {p : Base}
    (hZ : DifferentiableAt ℝ (firstParametrix τ G V₀ hxx hxy hyy) p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V₀ q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V₀ q = 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0)
    (hV : goodSecond G p ⬝ᵥ V₀ p = 0) :
    let ux := firstCovectorX τ G V₀ hxx hyy
    let uy := firstCovectorY τ G V₀ hxy hyy
    let Z := firstParametrix τ G V₀ hxx hxy hyy
    (conjugatedMetric τ G Z dx dx p - hxx p = 2 * reducedLx G ux uy p) ∧
    (conjugatedMetric τ G Z dx dy p - hxy p = reducedLy G ux uy p) ∧
    conjugatedMetric τ G Z dy dy p = hyy p := by
  obtain ⟨hxx', hxy', hyy'⟩ := normalElimination_residual τ hG hZ hD hX hY hb hV
    (hxx := hxx) (hxy := hxy) (hyy := hyy)
  refine ⟨hxx'.trans ?_, hxy'.trans ?_, hyy'⟩
  · simp only [firstCovectorX, ← mul_assoc, conjugating_inverse hτ, one_mul]
    ring
  · simp only [firstCovectorY, ← mul_assoc, conjugating_inverse hτ, one_mul]
    ring

end Parametrix

section LinearStructure
variable {n : ℕ}

lemma reducedLx_mul (G : Field n) {ux uy : Scalar} {p : Base}
    (hx : DifferentiableAt ℝ ux p) (hy : DifferentiableAt ℝ uy p) (a : ℂ) :
    reducedLx G (fun q => a * ux q) (fun q => a * uy q) p = a * reducedLx G ux uy p := by
  unfold reducedLx
  rw [partial_const_mul hx, partial_const_mul hy, connectionTerm_mul, connectionTerm_mul]
  ring

lemma reducedLy_mul (G : Field n) {ux uy : Scalar} {p : Base}
    (hx : DifferentiableAt ℝ ux p) (hy : DifferentiableAt ℝ uy p) (a : ℂ) :
    reducedLy G (fun q => a * ux q) (fun q => a * uy q) p = a * reducedLy G ux uy p := by
  unfold reducedLy
  rw [partial_const_mul hx, partial_const_mul hy, partial_const_mul hy,
    connectionTerm_mul, connectionTerm_mul]
  ring


theorem residual_modeApprox_succ (τ : ℝ) {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (j : ℕ) :
    residual τ G h (modeApprox τ G V h (j + 1)) p =
      - residual τ G (residual τ G h (modeApprox τ G V h j))
        (zeroParametrix τ G (residual τ G h (modeApprox τ G V h j))) p := by
  have hZ := contDiffAt_modeApprox τ hG hV hh hD hb j
  have hW := contDiffAt_zeroParametrix τ hG (contDiffAt_residual τ hG hZ hh) hD hb
  simp only [modeApprox, residual,
    conjugatedD_sub τ G (hZ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hW.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  abel



lemma contDiffAt_reducedLx {G : Field n} {ux uy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (reducedLx G ux uy) p := by
  exact ((contDiffAt_coordDeriv hx dx).sub (contDiffAt_connectionTerm hG hx hy hD dx dx)).sub
    ((contDiffAt_secondRatio hG hD hb dx dx).mul
      ((contDiffAt_coordDeriv hy dy).sub (contDiffAt_connectionTerm hG hx hy hD dy dy)))

lemma contDiffAt_reducedLy {G : Field n} {ux uy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (reducedLy G ux uy) p := by
  exact (((contDiffAt_coordDeriv hy dx).add (contDiffAt_coordDeriv hx dy)).sub
    (contDiffAt_const.mul (contDiffAt_connectionTerm hG hx hy hD dx dy))).sub
    ((contDiffAt_const.mul (contDiffAt_secondRatio hG hD hb dx dy)).mul
      ((contDiffAt_coordDeriv hy dy).sub (contDiffAt_connectionTerm hG hx hy hD dy dy)))

lemma contDiffAt_errorGenerator {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (errorGenerator G V h) p := by
  have hx := contDiffAt_reducedKx hG hV (contDiffAt_pi.mp hh 0) (contDiffAt_pi.mp hh 2) hD hb
  have hy := contDiffAt_reducedKy hG hV (contDiffAt_pi.mp hh 1) (contDiffAt_pi.mp hh 2) hD hb
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_const.mul (contDiffAt_reducedLx hG hx hy hD hb)
  · exact contDiffAt_reducedLy hG hx hy hD hb
  · exact contDiffAt_const



theorem residual_initialAmplitude {τ : ℝ} (hτ : τ ≠ 0) {G V : Field n}
    {h : Tensor} (hG : ContDiff ℝ ∞ G) {p : Base}
    (hVsm : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0)
    (hV : goodSecond G p ⬝ᵥ V p = 0) :
    residual τ G h (initialAmplitude τ G V h) p =
      ((τ : ℂ) / Complex.I) • errorGenerator G V h p := by
  have hs := contDiffAt_initialAmplitude τ hG.contDiffAt hVsm hh hD.self_of_nhds hb
  have hx := contDiffAt_reducedKx hG.contDiffAt hVsm (contDiffAt_pi.mp hh 0)
    (contDiffAt_pi.mp hh 2) hD.self_of_nhds hb
  have hy := contDiffAt_reducedKy hG.contDiffAt hVsm (contDiffAt_pi.mp hh 1)
    (contDiffAt_pi.mp hh 2) hD.self_of_nhds hb
  obtain ⟨hxx, hxy, hyy⟩ := firstParametrix_residual hτ hG
    (hs.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hD hX hY hb hV
  have hlx := reducedLx_mul G (hx.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hy.differentiableAt (by simp)) ((τ : ℂ) / Complex.I)
  have hly := reducedLy_mul G (hx.differentiableAt (by simp))
    (hy.differentiableAt (by simp)) ((τ : ℂ) / Complex.I)
  unfold firstCovectorX firstCovectorY component at hxx hxy
  rw [hlx] at hxx
  rw [hly] at hxy
  unfold component at hyy
  unfold residual conjugatedD initialAmplitude errorGenerator component
  ext i
  fin_cases i
  · simpa [residual, conjugatedD, tensorOf, initialAmplitude, errorGenerator,
      mul_assoc, mul_left_comm] using hxx
  · simpa [residual, conjugatedD, tensorOf, initialAmplitude, errorGenerator] using hxy
  · simp [tensorOf, hyy]

lemma reducedKx_zero_mul (G : Field n) (hxx hyy : Scalar) (a : ℂ) :
    reducedKx G (fun _ => 0) (fun q => a * hxx q) (fun q => a * hyy q) =
      fun q => a * reducedKx G (fun _ => 0) hxx hyy q := by
  funext q
  simp only [reducedKx, dotProduct_zero]
  ring

lemma reducedKy_zero_mul (G : Field n) (hxy hyy : Scalar) (a : ℂ) :
    reducedKy G (fun _ => 0) (fun q => a * hxy q) (fun q => a * hyy q) =
      fun q => a * reducedKy G (fun _ => 0) hxy hyy q := by
  funext q
  simp only [reducedKy, dotProduct_zero]
  ring

lemma errorGenerator_zero_mul (G : Field n) {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (a : ℂ) :
    errorGenerator G (fun _ => 0) (fun q => a • h q) p =
      a • errorGenerator G (fun _ => 0) h p := by
  have hx := contDiffAt_reducedKx (V := fun _ => 0) hG contDiffAt_const (contDiffAt_pi.mp hh 0)
    (contDiffAt_pi.mp hh 2) hD hb
  have hy := contDiffAt_reducedKy (V := fun _ => 0) hG contDiffAt_const (contDiffAt_pi.mp hh 1)
    (contDiffAt_pi.mp hh 2) hD hb
  have hcx (i : Fin 3) : component (fun q => a • h q) i = fun q => a * component h i q := rfl
  simp only [errorGenerator, hcx, reducedKx_zero_mul, reducedKy_zero_mul]
  ext i
  fin_cases i
  · simp [tensorOf]
    unfold component
    rw [reducedLx_mul G (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp)) a]
    ring
  · simp [tensorOf]
    exact reducedLy_mul G (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp)) a
  · simp [tensorOf]

lemma reducedLx_congr (G : Field n) {ux uy vx vy : Scalar} {p : Base}
    (hx : ux =ᶠ[nhds p] vx) (hy : uy =ᶠ[nhds p] vy) :
    reducedLx G ux uy p = reducedLx G vx vy p := by
  simp only [reducedLx, coordDeriv, hx.fderiv_eq, hy.fderiv_eq, connectionTerm,
    hx.self_of_nhds, hy.self_of_nhds]

lemma reducedLy_congr (G : Field n) {ux uy vx vy : Scalar} {p : Base}
    (hx : ux =ᶠ[nhds p] vx) (hy : uy =ᶠ[nhds p] vy) :
    reducedLy G ux uy p = reducedLy G vx vy p := by
  simp only [reducedLy, coordDeriv, hx.fderiv_eq, hy.fderiv_eq, connectionTerm,
    hx.self_of_nhds, hy.self_of_nhds]


lemma errorGenerator_congr (G V : Field n) {h k : Tensor} {p : Base}
    (he : h =ᶠ[nhds p] k) : errorGenerator G V h p = errorGenerator G V k p := by
  have hx : reducedKx G V (component h 0) (component h 2) =ᶠ[nhds p]
      reducedKx G V (component k 0) (component k 2) := by
    filter_upwards [he] with q hq
    simp only [reducedKx, component, hq]
  have hy : reducedKy G V (component h 1) (component h 2) =ᶠ[nhds p]
      reducedKy G V (component k 1) (component k 2) := by
    filter_upwards [he] with q hq
    simp only [reducedKy, component, hq]
  unfold errorGenerator tensorOf
  dsimp only
  rw [reducedLx_congr G hx hy, reducedLy_congr G hx hy]


lemma contDiffAt_errorHierarchy {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (j : ℕ) :
    ContDiffAt ℝ ∞ (errorHierarchy G V h j) p := by
  induction j with
  | zero => exact contDiffAt_errorGenerator hG hV hh hD hb
  | succ j ih => exact contDiffAt_errorGenerator hG contDiffAt_const ih hD hb





theorem residual_modeApprox_power {τ : ℝ} (hτ : τ ≠ 0) {G V : Field n}
    {h : Tensor} (hG : ContDiff ℝ ∞ G) {U : Set Base} (hU : IsOpen U)
    (hVsm : ContDiffOn ℝ ∞ V U) (hh : ContDiffOn ℝ ∞ h U)
    (hD : ∀ q ∈ U, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0)
    (hX : ∀ q ∈ U, coordDeriv dx G q ⬝ᵥ V q = 0)
    (hY : ∀ q ∈ U, coordDeriv dy G q ⬝ᵥ V q = 0)
    (hb : ∀ q ∈ U, goodSecond G q ⬝ᵥ goodSecond G q ≠ 0)
    (hV : ∀ q ∈ U, goodSecond G q ⬝ᵥ V q = 0) (j : ℕ) :
    ∀ p ∈ U, residual τ G h (modeApprox τ G V h j) p =
      ((-((τ : ℂ) / Complex.I)) ^ j * ((τ : ℂ) / Complex.I)) • errorHierarchy G V h j p := by
  have hDe (p : Base) (hp : p ∈ U) : ∀ᶠ q in nhds p, gramDet (coordDeriv dx G q) (coordDeriv dy G q) ≠ 0 :=
    by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hD q hq
  have hXe (p : Base) (hp : p ∈ U) : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ V q = 0 :=
    by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hX q hq
  have hYe (p : Base) (hp : p ∈ U) : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ V q = 0 :=
    by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hY q hq
  have hvAt (p : Base) (hp : p ∈ U) : ContDiffAt ℝ ∞ V p := (hVsm p hp).contDiffAt (hU.mem_nhds hp)
  have hhAt (p : Base) (hp : p ∈ U) : ContDiffAt ℝ ∞ h p := (hh p hp).contDiffAt (hU.mem_nhds hp)
  induction j with
  | zero =>
    intro p hp
    simpa only [modeApprox, errorHierarchy, pow_zero, one_mul] using
      residual_initialAmplitude hτ hG (hvAt p hp) (hhAt p hp) (hDe p hp)
        (hXe p hp) (hYe p hp) (hb p hp) (hV p hp)
  | succ j ih =>
    intro p hp
    let a : ℂ := (-((τ : ℂ) / Complex.I)) ^ j * ((τ : ℂ) / Complex.I)
    have hre : residual τ G h (modeApprox τ G V h j) =ᶠ[nhds p]
        fun q => a • errorHierarchy G V h j q := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact ih q hq
    have hs := contDiffAt_modeApprox τ hG.contDiffAt (hvAt p hp) (hhAt p hp) (hD p hp) (hb p hp) j
    have hr := contDiffAt_residual τ hG.contDiffAt hs (hhAt p hp)
    have hzeroX : ∀ᶠ q in nhds p, coordDeriv dx G q ⬝ᵥ (0 : Ambient n) = 0 :=
      Filter.Eventually.of_forall fun q => dotProduct_zero _
    have hzeroY : ∀ᶠ q in nhds p, coordDeriv dy G q ⬝ᵥ (0 : Ambient n) = 0 :=
      Filter.Eventually.of_forall fun q => dotProduct_zero _
    rw [residual_modeApprox_succ τ hG.contDiffAt (hvAt p hp) (hhAt p hp) (hD p hp) (hb p hp)]
    rw [show zeroParametrix τ G (residual τ G h (modeApprox τ G V h j)) =
      initialAmplitude τ G (fun _ => 0) (residual τ G h (modeApprox τ G V h j)) from rfl]
    rw [residual_initialAmplitude hτ hG contDiffAt_const hr (hDe p hp)
      hzeroX hzeroY (hb p hp) (dotProduct_zero _)]
    rw [errorGenerator_congr G (fun _ => 0) hre]
    rw [errorGenerator_zero_mul G hG.contDiffAt
      (contDiffAt_errorHierarchy hG.contDiffAt (hvAt p hp) (hhAt p hp) (hD p hp) (hb p hp) j)
      (hD p hp) (hb p hp) a]
    simp only [smul_smul, ← neg_smul, errorHierarchy]
    congr 1
    dsimp [a]
    ring


end LinearStructure

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith


lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

lemma WeightedBound.neg {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun x => -f x) := by
  simpa using hb.const_smul hU hf (-1)

lemma WeightedBound.sub {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (C + D) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hbf.add hU hs hf hg.neg (hbg.neg hU hg)

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)



lemma WeightedBound.comp {U : Set E} {V : Set F} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {s C D : ℝ} {m : ℕ} {f : E → F} {g : F → G} (hs : 0 < s) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hbf : WeightedBound U s m C f)
    (hbg : ∀ j ≤ m, ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ D) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ (C / s) ^ i := by
    have hp : C ≤ C ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hC hi1
    calc
      _ ≤ C / s ^ i := hbf.deriv_le hs (hij.trans hj) hx
      _ ≤ C ^ i / s ^ i := div_le_div_of_nonneg_right hp (pow_nonneg hs.le _)
      _ = _ := (div_pow C s i).symm
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx
    (fun i hij => hbg i (hij.trans hj) x hx) hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * D * (C / s) ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      gcongr




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma WeightedBound.const_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun x => a * f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul]
  calc
    _ = ‖a‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg a)

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

lemma WeightedBound.dot {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : E → ι → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m ((Fintype.card ι : ℝ) * (2 ^ m * C * D))
      (fun x => dotProduct (f x) (g x)) := by
  have hfsm (i : ι) := contDiffOn_pi.mp hf i
  have hgsm (i : ι) := contDiffOn_pi.mp hg i
  have hh := WeightedBound.finset_sum hU hs Finset.univ (fun _ : ι => 2 ^ m * C * D)
    (fun i x => f x i * g x i) (fun i _ => (hfsm i).mul (hgsm i)) (fun i _ =>
      (hbf.component hU hs hC hf i).mul hU hs hC hD (hfsm i) (hgsm i)
        (hbg.component hU hs hD hg i))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, dotProduct] using hh

lemma WeightedBound.complex_smul_pi {ι : Type*} [Fintype ι] {U : Set E}
    (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → ι → ℂ} (hs : 0 < s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun x => a • f x) := by
  apply WeightedBound.pi hU hs (mul_nonneg (norm_nonneg _) hC)
  · intro i
    exact contDiffOn_const.mul (contDiffOn_pi.mp hf i)
  · intro i
    exact (hb.component hU hs.le hC hf i).const_mul hU (contDiffOn_pi.mp hf i) a

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



lemma ModeDomain.connectionX {G : Field n} {U : Set Base} (h : ModeDomain G U) (v w : Base) :
    ContDiffOn ℝ ∞ (connectionX G v w) U := by
  intro p hp
  exact (contDiffAt_connectionX (h.smoothAt hp) (h.determinant p hp) v w).contDiffWithinAt

lemma ModeDomain.connectionY {G : Field n} {U : Set Base} (h : ModeDomain G U) (v w : Base) :
    ContDiffOn ℝ ∞ (connectionY G v w) U := by
  intro p hp
  exact (contDiffAt_connectionY (h.smoothAt hp) (h.determinant p hp) v w).contDiffWithinAt

lemma ModeDomain.secondRatio {G : Field n} {U : Set Base} (h : ModeDomain G U) (v w : Base) :
    ContDiffOn ℝ ∞ (secondRatio G v w) U := by
  intro p hp
  exact (contDiffAt_secondRatio (h.smoothAt hp) (h.determinant p hp) (h.good p hp) v w).contDiffWithinAt

lemma contDiffOn_coordDeriv {U : Set Base} (hU : IsOpen U) {f : Scalar}
    (hf : ContDiffOn ℝ ∞ f U) (v : Base) : ContDiffOn ℝ ∞ (coordDeriv v f) U := by
  intro p hp
  exact (contDiffAt_coordDeriv ((hf p hp).contDiffAt (hU.mem_nhds hp)) v).contDiffWithinAt

lemma contDiffOn_connectionTerm {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {ux uy : Scalar} (hx : ContDiffOn ℝ ∞ ux U) (hy : ContDiffOn ℝ ∞ uy U) (v w : Base) :
    ContDiffOn ℝ ∞ (connectionTerm G ux uy v w) U :=
  ((h.connectionX v w).mul hx).add ((h.connectionY v w).mul hy)


lemma ModeCoefficientBound.mono_order {G : Field n} {U : Set Base} {s K : ℝ} {m r : ℕ}
    (h : ModeCoefficientBound G U s m K) (hr : r ≤ m) : ModeCoefficientBound G U s r K :=
  ⟨h.xxX.mono_order hr, h.xxY.mono_order hr, h.xyX.mono_order hr, h.xyY.mono_order hr,
    h.yyX.mono_order hr, h.yyY.mono_order hr, h.ratioxx.mono_order hr, h.ratioxy.mono_order hr⟩

lemma weighted_connectionTerm {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {ux uy : Scalar} (hs : 0 ≤ s) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hx : ContDiffOn ℝ ∞ ux U) (hy : ContDiffOn ℝ ∞ uy U) (v w : Base)
    (hΓx : WeightedBound U s m K (connectionX G v w))
    (hΓy : WeightedBound U s m K (connectionY G v w))
    (hbx : WeightedBound U s m C ux) (hby : WeightedBound U s m C uy) :
    WeightedBound U s m (2 ^ (m + 1) * K * C) (connectionTerm G ux uy v w) := by
  have h1 := hΓx.mul h.isOpen.uniqueDiffOn hs hK hC (h.connectionX v w) hx hbx
  have h2 := hΓy.mul h.isOpen.uniqueDiffOn hs hK hC (h.connectionY v w) hy hby
  have hh := h1.add h.isOpen.uniqueDiffOn hs ((h.connectionX v w).mul hx)
    ((h.connectionY v w).mul hy) h2
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  rw [pow_succ]
  ring

lemma weighted_dx {U : Set Base} (hU : IsOpen U) {s C : ℝ} {m : ℕ} {f : Scalar}
    (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (coordDeriv dx f) := by
  unfold coordDeriv
  simpa [dx, Prod.norm_def] using hb.directional hU hs hf dx

lemma weighted_dy {U : Set Base} (hU : IsOpen U) {s C : ℝ} {m : ℕ} {f : Scalar}
    (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (coordDeriv dy f) := by
  unfold coordDeriv
  simpa [dy, Prod.norm_def] using hb.directional hU hs hf dy

lemma weighted_mono_div_scale {U : Set Base} {s C : ℝ} {m : ℕ} {f : Scalar}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) f := by
  apply (hb.mono_order (Nat.le_succ m)).mono_const
  exact (le_div_iff₀ hs).2 (mul_le_of_le_one_right hC hs1)


lemma reducedConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ reducedConstant m K := by
  unfold reducedConstant
  positivity

lemma weighted_reducedLx {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {ux uy : Scalar} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ModeCoefficientBound G U s m K)
    (hx : ContDiffOn ℝ ∞ ux U) (hy : ContDiffOn ℝ ∞ uy U)
    (hbx : WeightedBound U s (m + 1) C ux) (hby : WeightedBound U s (m + 1) C uy) :
    WeightedBound U s m (reducedConstant m K * (C / s)) (reducedLx G ux uy) := by
  have hc0 : 0 ≤ C / s := div_nonneg hC hs.le
  have hux := weighted_mono_div_scale hs hs1 hC hbx
  have huy := weighted_mono_div_scale hs hs1 hC hby
  have hxx := weighted_connectionTerm h hs.le hK hc0 hx hy dx dx hc.xxX hc.xxY hux huy
  have hyy := weighted_connectionTerm h hs.le hK hc0 hx hy dy dy hc.yyX hc.yyY hux huy
  have dxsm := contDiffOn_coordDeriv h.isOpen hx dx
  have dysm := contDiffOn_coordDeriv h.isOpen hy dy
  have xxsm := contDiffOn_connectionTerm h hx hy dx dx
  have yysm := contDiffOn_connectionTerm h hx hy dy dy
  have hd1 := (weighted_dx h.isOpen hs hx hbx).sub h.isOpen.uniqueDiffOn hs.le dxsm xxsm hxx
  have hd2 := (weighted_dy h.isOpen hs hy hby).sub h.isOpen.uniqueDiffOn hs.le dysm yysm hyy
  have hp := hc.ratioxx.mul h.isOpen.uniqueDiffOn hs.le hK (by positivity)
    (h.secondRatio dx dx) (dysm.sub yysm) hd2
  have hh := hd1.sub h.isOpen.uniqueDiffOn hs.le (dxsm.sub xxsm)
    ((h.secondRatio dx dx).mul (dysm.sub yysm)) hp
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  unfold reducedConstant
  ring

lemma weighted_reducedLy {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {ux uy : Scalar} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ModeCoefficientBound G U s m K)
    (hx : ContDiffOn ℝ ∞ ux U) (hy : ContDiffOn ℝ ∞ uy U)
    (hbx : WeightedBound U s (m + 1) C ux) (hby : WeightedBound U s (m + 1) C uy) :
    WeightedBound U s m (2 * reducedConstant m K * (C / s)) (reducedLy G ux uy) := by
  have hc0 : 0 ≤ C / s := div_nonneg hC hs.le
  have hux := weighted_mono_div_scale hs hs1 hC hbx
  have huy := weighted_mono_div_scale hs hs1 hC hby
  have hxy := weighted_connectionTerm h hs.le hK hc0 hx hy dx dy hc.xyX hc.xyY hux huy
  have hyy := weighted_connectionTerm h hs.le hK hc0 hx hy dy dy hc.yyX hc.yyY hux huy
  have dxsm := contDiffOn_coordDeriv h.isOpen hy dx
  have dysm := contDiffOn_coordDeriv h.isOpen hx dy
  have yysm := contDiffOn_coordDeriv h.isOpen hy dy
  have cxysm := contDiffOn_connectionTerm h hx hy dx dy
  have cyysm := contDiffOn_connectionTerm h hx hy dy dy
  have hxy2 := hxy.const_mul h.isOpen.uniqueDiffOn cxysm 2
  have hterm := (weighted_dx h.isOpen hs hy hby).add h.isOpen.uniqueDiffOn hs.le dxsm dysm
    (weighted_dy h.isOpen hs hx hbx)
  have hterm2 := hterm.sub h.isOpen.uniqueDiffOn hs.le (dxsm.add dysm) (contDiffOn_const.mul cxysm) hxy2
  have hdiff := (weighted_dy h.isOpen hs hy hby).sub h.isOpen.uniqueDiffOn hs.le yysm cyysm hyy
  have hprod := hc.ratioxy.mul h.isOpen.uniqueDiffOn hs.le hK (by positivity)
    (h.secondRatio dx dy) (yysm.sub cyysm) hdiff
  have hprod2 := hprod.const_mul h.isOpen.uniqueDiffOn ((h.secondRatio dx dy).mul (yysm.sub cyysm)) 2
  have hh := hterm2.sub h.isOpen.uniqueDiffOn hs.le
    ((dxsm.add dysm).sub (contDiffOn_const.mul cxysm))
    (contDiffOn_const.mul ((h.secondRatio dx dy).mul (yysm.sub cyysm))) hprod2
  have hin : WeightedBound U s m
      ((C / s + C / s + 2 * (2 ^ (m + 1) * K * (C / s))) +
        2 * (2 ^ m * K * (C / s + 2 ^ (m + 1) * K * (C / s))))
      (reducedLy G ux uy) := by
    unfold reducedLy
    simpa only [Complex.norm_ofNat, mul_assoc] using hh
  convert hin using 1
  all_goals try with_reducible_and_instances rfl
  try rfl
  unfold reducedConstant
  ring

lemma contDiffOn_reducedKx {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {a b : Scalar} (hV : ContDiffOn ℝ ∞ V U)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (reducedKx G V a b) U := by
  intro p hp
  exact (contDiffAt_reducedKx (h.smoothAt hp) ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((ha p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hb p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp)).contDiffWithinAt

lemma contDiffOn_reducedKy {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {a b : Scalar} (hV : ContDiffOn ℝ ∞ V U)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (reducedKy G V a b) U := by
  intro p hp
  exact (contDiffAt_reducedKy (h.smoothAt hp) ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((ha p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hb p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp)).contDiffWithinAt

lemma contDiffOn_errorGenerator {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (errorGenerator G V f) U := by
  intro p hp
  exact (contDiffAt_errorGenerator (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp)).contDiffWithinAt

lemma contDiffOn_errorHierarchy {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) (q : ℕ) :
    ContDiffOn ℝ ∞ (errorHierarchy G V f q) U := by
  intro p hp
  exact (contDiffAt_errorHierarchy (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp) q).contDiffWithinAt


lemma weighted_tensor_complex_smul {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun p => a • f p) := by
  apply WeightedBound.pi hU hs (mul_nonneg (norm_nonneg _) hC)
  · intro i
    exact contDiffOn_const.mul (contDiffOn_pi.mp hf i)
  · intro i
    exact (hb.component hU hs.le hC hf i).const_mul hU (contDiffOn_pi.mp hf i) a




lemma FullModeCoefficientBound.mono_order {G : Field n} {U : Set Base} {s K : ℝ} {m r : ℕ}
    (h : FullModeCoefficientBound G U s m K) (hr : r ≤ m) : FullModeCoefficientBound G U s r K :=
  ⟨h.toModeCoefficientBound.mono_order hr, h.secondxx.mono_order hr, h.secondxy.mono_order hr⟩

lemma weighted_half {U : Set Base} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : Scalar} (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => f p / 2) := by
  have hh := hb.const_mul hU hf (1 / 2)
  have hh' : WeightedBound U s m (C / 2) (fun p => f p / 2) := by
    convert hh using 1
    · norm_num
      ring
    · funext p
      ring
  exact hh'.mono_const (by linarith)

lemma targetConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ targetConstant n m K := by
  unfold targetConstant
  positivity

lemma weighted_reducedK {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 ≤ s) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : FullModeCoefficientBound G U s m K) (hf : ContDiffOn ℝ ∞ f U)
    (hV : ContDiffOn ℝ ∞ V U) (hb : WeightedBound U s m C f) (hbV : WeightedBound U s m C V) :
    WeightedBound U s m (targetConstant n m K * C)
      (reducedKx G V (component f 0) (component f 2)) ∧
    WeightedBound U s m (targetConstant n m K * C)
      (reducedKy G V (component f 1) (component f 2)) := by
  have hsm (i : Fin 3) : ContDiffOn ℝ ∞ (component f i) U := contDiffOn_pi.mp hf i
  have hbcomp (i : Fin 3) := hb.component h.isOpen.uniqueDiffOn hs hC hf i
  have hbx := hc.secondxx.dot h.isOpen.uniqueDiffOn hs hK hC (h.secondForm dx dx) hV hbV
  have hby := hc.secondxy.dot h.isOpen.uniqueDiffOn hs hK hC (h.secondForm dx dy) hV hbV
  have bxsm : ContDiffOn ℝ ∞ (fun p => secondForm G dx dx p ⬝ᵥ V p) U := by
    intro p hp
    exact (contDiffAt_dot ((h.secondForm dx dx p hp).contDiffAt (h.isOpen.mem_nhds hp))
      ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))).contDiffWithinAt
  have bysm : ContDiffOn ℝ ∞ (fun p => secondForm G dx dy p ⬝ᵥ V p) U := by
    intro p hp
    exact (contDiffAt_dot ((h.secondForm dx dy p hp).contDiffAt (h.isOpen.mem_nhds hp))
      ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))).contDiffWithinAt
  have hmulx := hc.ratioxx.mul h.isOpen.uniqueDiffOn hs hK hC (h.secondRatio dx dx)
    (hsm 2) (hbcomp 2)
  have hmuly := hc.ratioxy.mul h.isOpen.uniqueDiffOn hs hK hC (h.secondRatio dx dy)
    (hsm 2) (hbcomp 2)
  have hhalf := weighted_half h.isOpen.uniqueDiffOn hC (hsm 0) (hbcomp 0)
  have hxa := hhalf.add h.isOpen.uniqueDiffOn hs ((hsm 0).div_const 2) bxsm hbx
  have hxr := weighted_half h.isOpen.uniqueDiffOn (by positivity)
    ((h.secondRatio dx dx).mul (hsm 2)) hmulx
  have hxx := hxa.sub h.isOpen.uniqueDiffOn hs (((hsm 0).div_const 2).add bxsm)
    (((h.secondRatio dx dx).mul (hsm 2)).div_const 2) hxr
  have hy2 := hby.const_mul h.isOpen.uniqueDiffOn bysm 2
  have hya := (hbcomp 1).add h.isOpen.uniqueDiffOn hs (hsm 1) (contDiffOn_const.mul bysm) hy2
  have hyy := hya.sub h.isOpen.uniqueDiffOn hs ((hsm 1).add (contDiffOn_const.mul bysm))
    ((h.secondRatio dx dy).mul (hsm 2)) hmuly
  constructor
  · apply hxx.mono_const
    simp only [targetConstant, Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    nlinarith [show 0 ≤ (n : ℝ) * (2 ^ m * K * C) by positivity]
  · convert hyy using 1
    · simp only [targetConstant, Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one, Complex.norm_ofNat]
      ring
    · rfl


lemma fullErrorConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ fullErrorConstant n m K :=
  mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK))
    (targetConstant_nonneg n (m + 1) hK)

lemma fullErrorConstant_mono {m r : ℕ} (hmr : m ≤ r) (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    fullErrorConstant n m K ≤ fullErrorConstant n r K := by
  unfold fullErrorConstant reducedConstant targetConstant
  gcongr <;> norm_num

lemma weighted_errorGenerator {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : FullModeCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (fullErrorConstant n m K * C / s) (errorGenerator G V f) := by
  have hsm (i : Fin 3) : ContDiffOn ℝ ∞ (component f i) U := contDiffOn_pi.mp hf i
  have hxb := (weighted_reducedK h hs.le hK hC hc hf hV hb hbV).1
  have hyb := (weighted_reducedK h hs.le hK hC hc hf hV hb hbV).2
  have hxsm := contDiffOn_reducedKx h hV (hsm 0) (hsm 2)
  have hysm := contDiffOn_reducedKy h hV (hsm 1) (hsm 2)
  have hc0 : 0 ≤ targetConstant n (m + 1) K * C :=
    mul_nonneg (targetConstant_nonneg _ _ hK) hC
  have hxx := weighted_reducedLx h hs hs1 hK hc0 (hc.toModeCoefficientBound.mono_order (Nat.le_succ m))
    hxsm hysm hxb hyb
  have hyy := weighted_reducedLy h hs hs1 hK hc0 (hc.toModeCoefficientBound.mono_order (Nat.le_succ m))
    hxsm hysm hxb hyb
  have hx2 := hxx.const_mul h.isOpen.uniqueDiffOn (by
    intro p hp
    exact (contDiffAt_reducedLx (h.smoothAt hp)
      ((hxsm p hp).contDiffAt (h.isOpen.mem_nhds hp))
      ((hysm p hp).contDiffAt (h.isOpen.mem_nhds hp))
      (h.determinant p hp) (h.good p hp)).contDiffWithinAt) 2
  have hfsm := contDiffOn_errorGenerator h hV hf
  have hcomponent : ∀ i : Fin 3, WeightedBound U s m (fullErrorConstant n m K * C / s)
      (component (errorGenerator G V f) i) := by
    intro i
    fin_cases i
    · convert hx2 using 1
      · simp only [Complex.norm_ofNat, fullErrorConstant]
        ring
      · rfl
    · convert hyy using 1
      · unfold fullErrorConstant
        ring
      · rfl
    · exact (weightedBound_zero U s m).mono_const (by
        exact div_nonneg (mul_nonneg (fullErrorConstant_nonneg n m hK) hC) hs.le)
  exact WeightedBound.pi h.isOpen.uniqueDiffOn hs
    (div_nonneg (mul_nonneg (fullErrorConstant_nonneg n m hK) hC) hs.le)
    (fun i => contDiffOn_pi.mp hfsm i) hcomponent



theorem weighted_errorHierarchy {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U) (q m : ℕ)
    (hc : FullModeCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m ((fullErrorConstant n (m + q) K / s) ^ (q + 1) * C)
      (errorHierarchy G V f q) := by
  induction q generalizing m with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, pow_one, div_mul_eq_mul_div, errorHierarchy] using
      weighted_errorGenerator h hs hs1 hK hC hc hf hV hb hbV
  | succ q ih =>
    have hm : m + 1 + q + 1 = m + (q + 1) + 1 := by omega
    have iht := ih (m + 1) (hm ▸ hc) (hm ▸ hb) (hm ▸ hbV)
    have han : 0 ≤ fullErrorConstant n (m + 1 + q) K / s :=
      div_nonneg (fullErrorConstant_nonneg n _ hK) hs.le
    have hn : 0 ≤ (fullErrorConstant n (m + 1 + q) K / s) ^ (q + 1) * C :=
      mul_nonneg (pow_nonneg han _) hC
    have hbase := weighted_errorGenerator h hs hs1 hK hn
      (hc.mono_order (by omega)) (contDiffOn_errorHierarchy h hV hf q)
      (V := fun _ => 0) contDiffOn_const iht ((weightedBound_zero U s (m + 1)).mono_const hn)
    change WeightedBound U s m _ (errorGenerator G (fun _ => 0) (errorHierarchy G V f q))
    apply hbase.mono_const
    have he : m + 1 + q = m + (q + 1) := by omega
    rw [he]
    calc
      _ = (fullErrorConstant n m K / s) *
          ((fullErrorConstant n (m + (q + 1)) K / s) ^ (q + 1) * C) := by ring
      _ ≤ (fullErrorConstant n (m + (q + 1)) K / s) *
          ((fullErrorConstant n (m + (q + 1)) K / s) ^ (q + 1) * C) := by
        apply mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (fullErrorConstant_mono (Nat.le_add_right m (q + 1)) n hK) hs.le)
        exact mul_nonneg (pow_nonneg (div_nonneg (fullErrorConstant_nonneg n _ hK) hs.le) _) hC
      _ = _ := by ring



theorem weighted_residual_modeApprox {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : FullModeCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m (fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C)
      (residual τ G f (modeApprox τ G V f q)) := by
  have hbound := weighted_errorHierarchy h hs hs1 hK hC hf hVsm q m hc hb hbV
  have hn : 0 ≤ (fullErrorConstant n (m + q) K / s) ^ (q + 1) * C :=
    mul_nonneg (pow_nonneg (div_nonneg (fullErrorConstant_nonneg n _ hK) hs.le) _) hC
  have hsm := contDiffOn_errorHierarchy h hVsm hf q
  have hh := weighted_tensor_complex_smul h.isOpen.uniqueDiffOn hs hn hsm hbound
    ((-((τ : ℂ) / Complex.I)) ^ q * ((τ : ℂ) / Complex.I))
  have hnorm : ‖(-((τ : ℂ) / Complex.I)) ^ q * ((τ : ℂ) / Complex.I)‖ = τ ^ (q + 1) := by
    simp only [norm_mul, norm_pow, norm_neg, norm_div, Complex.norm_I, div_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ, pow_succ]
  rw [hnorm] at hh
  have hconstant : τ ^ (q + 1) * ((fullErrorConstant n (m + q) K / s) ^ (q + 1) * C) =
      fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C := by
    rw [div_pow, div_pow]
    ring
  rw [hconstant] at hh
  apply hh.congr
  intro p hp
  exact residual_modeApprox_power (ne_of_gt hτ) hG h.isOpen hVsm hf h.determinant
    hX hY h.good hV q p hp


lemma ModeDomain.tangentDualX {G : Field n} {U : Set Base} (h : ModeDomain G U) :
    ContDiffOn ℝ ∞ (tangentDualX G) U := by
  intro p hp
  exact (contDiffAt_tangentLift (contDiffAt_coordDeriv (h.smoothAt hp) dx)
    (contDiffAt_coordDeriv (h.smoothAt hp) dy) contDiffAt_const contDiffAt_const
    (h.determinant p hp)).contDiffWithinAt

lemma ModeDomain.tangentDualY {G : Field n} {U : Set Base} (h : ModeDomain G U) :
    ContDiffOn ℝ ∞ (tangentDualY G) U := by
  intro p hp
  exact (contDiffAt_tangentLift (contDiffAt_coordDeriv (h.smoothAt hp) dx)
    (contDiffAt_coordDeriv (h.smoothAt hp) dy) contDiffAt_const contDiffAt_const
    (h.determinant p hp)).contDiffWithinAt

lemma ModeDomain.normalDual {G : Field n} {U : Set Base} (h : ModeDomain G U) :
    ContDiffOn ℝ ∞ (normalDual G) U := by
  intro p hp
  have hb := contDiffAt_secondForm (h.smoothAt hp) (h.determinant p hp) dy dy
  unfold ClosedSurfaceR4.SmallModes.normalDual
  change ContDiffWithinAt ℝ ∞ (fun q => (ClosedSurfaceR4.SmallModes.secondForm G dy dy q ⬝ᵥ ClosedSurfaceR4.SmallModes.secondForm G dy dy q)⁻¹ • ClosedSurfaceR4.SmallModes.secondForm G dy dy q) U p
  simpa only [one_div, Pi.smul_def'] using
    ((contDiffAt_cdiv (a := fun _ => (1 : ℂ)) contDiffAt_const (contDiffAt_dot hb hb)
      (h.good p hp)).smul hb).contDiffWithinAt (s := U)



lemma ReconstructionCoefficientBound.mono_order {G : Field n} {U : Set Base} {s K : ℝ} {m r : ℕ}
    (h : ReconstructionCoefficientBound G U s m K) (hr : r ≤ m) :
    ReconstructionCoefficientBound G U s r K :=
  ⟨h.toFullModeCoefficientBound.mono_order hr, h.dualx.mono_order hr,
    h.dualy.mono_order hr, h.dualn.mono_order hr⟩

lemma weighted_smul_field {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f : Scalar} {V : Field n} (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hbf : WeightedBound U s m C f) (hbV : WeightedBound U s m D V) :
    WeightedBound U s m (2 ^ m * C * D) (fun p => f p • V p) := by
  apply WeightedBound.pi hU hs (by positivity)
  · intro i
    exact hf.mul (contDiffOn_pi.mp hV i)
  · intro i
    exact hbf.mul hU hs.le hC hD hf (contDiffOn_pi.mp hV i) (hbV.component hU hs.le hD hV i)



lemma contDiffOn_amplitudeCorrection {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (amplitudeCorrection G V f) U := by
  have hx := contDiffOn_reducedKx h hV (contDiffOn_pi.mp hf 0) (contDiffOn_pi.mp hf 2)
  have hy := contDiffOn_reducedKy h hV (contDiffOn_pi.mp hf 1) (contDiffOn_pi.mp hf 2)
  exact ((hx.smul h.tangentDualX).add (hy.smul h.tangentDualY)).add
    (((contDiffOn_coordDeriv h.isOpen hy dy).sub (contDiffOn_connectionTerm h hx hy dy dy)).smul h.normalDual)


lemma amplitudeConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ amplitudeConstant n m K := by
  unfold amplitudeConstant
  exact mul_nonneg (by positivity) (targetConstant_nonneg _ _ hK)

lemma weighted_amplitudeCorrection {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (amplitudeConstant n m K * C / s) (amplitudeCorrection G V f) := by
  have hks := weighted_reducedK h hs.le hK hC hc.toFullModeCoefficientBound hf hV hb hbV
  have hx := contDiffOn_reducedKx h hV (contDiffOn_pi.mp hf 0) (contDiffOn_pi.mp hf 2)
  have hy := contDiffOn_reducedKy h hV (contDiffOn_pi.mp hf 1) (contDiffOn_pi.mp hf 2)
  have hn : 0 ≤ targetConstant n (m + 1) K * C := mul_nonneg (targetConstant_nonneg _ _ hK) hC
  have hcn := div_nonneg hn hs.le
  have hxm := weighted_mono_div_scale hs hs1 hn hks.1
  have hym := weighted_mono_div_scale hs hs1 hn hks.2
  have htx := weighted_smul_field h.isOpen.uniqueDiffOn hs hcn hK hx h.tangentDualX hxm
    (hc.dualx.mono_order (Nat.le_succ m))
  have hty := weighted_smul_field h.isOpen.uniqueDiffOn hs hcn hK hy h.tangentDualY hym
    (hc.dualy.mono_order (Nat.le_succ m))
  have ht := htx.add h.isOpen.uniqueDiffOn hs.le (hx.smul h.tangentDualX) (hy.smul h.tangentDualY) hty
  have hΓ := weighted_connectionTerm h hs.le hK hcn hx hy dy dy
    (hc.yyX.mono_order (Nat.le_succ m)) (hc.yyY.mono_order (Nat.le_succ m)) hxm hym
  have hd := (weighted_dy h.isOpen hs hy hks.2).sub h.isOpen.uniqueDiffOn hs.le
    (contDiffOn_coordDeriv h.isOpen hy dy) (contDiffOn_connectionTerm h hx hy dy dy) hΓ
  have hnormal := weighted_smul_field h.isOpen.uniqueDiffOn hs (by positivity) hK
    ((contDiffOn_coordDeriv h.isOpen hy dy).sub (contDiffOn_connectionTerm h hx hy dy dy))
    h.normalDual hd (hc.dualn.mono_order (Nat.le_succ m))
  have hh := ht.add h.isOpen.uniqueDiffOn hs.le
    ((hx.smul h.tangentDualX).add (hy.smul h.tangentDualY))
    (((contDiffOn_coordDeriv h.isOpen hy dy).sub (contDiffOn_connectionTerm h hx hy dy dy)).smul h.normalDual)
    hnormal
  convert hh using 1
  · unfold amplitudeConstant
    ring
  · rfl

lemma initialConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ initialConstant n m K := by
  unfold initialConstant
  exact add_nonneg (by positivity) (amplitudeConstant_nonneg _ _ hK)

lemma weighted_reconstructedLeading {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : ReconstructionCoefficientBound G U s m K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s m C f) (hbV : WeightedBound U s m C V) :
    WeightedBound U s m (C + 2 ^ m * C * K)
      (fun p => V p - (f p 2 / 2) • normalDual G p) := by
  have hf2 := contDiffOn_pi.mp hf 2
  have hhalf := weighted_half h.isOpen.uniqueDiffOn hC hf2
    (hb.component h.isOpen.uniqueDiffOn hs.le hC hf 2)
  have hn := weighted_smul_field h.isOpen.uniqueDiffOn hs hC hK (hf2.div_const 2) h.normalDual
    hhalf hc.dualn
  exact hbV.sub h.isOpen.uniqueDiffOn hs.le hV ((hf2.div_const 2).smul h.normalDual) hn

lemma weighted_scaledAmplitudeCorrection {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (amplitudeConstant n m K * C)
      (fun p => ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p) := by
  have hcorr := weighted_amplitudeCorrection h hs hs1 hK hC hc hf hV hb hbV
  have hsm := contDiffOn_amplitudeCorrection h hV hf
  have hsmall := hcorr.complex_smul_pi h.isOpen.uniqueDiffOn hs
    (div_nonneg (mul_nonneg (amplitudeConstant_nonneg _ _ hK) hC) hs.le)
    hsm ((τ : ℂ) / Complex.I)
  have hnorm : ‖(τ : ℂ) / Complex.I‖ = τ := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  rw [hnorm] at hsmall
  apply hsmall.mono_const
  calc
    _ ≤ s * (amplitudeConstant n m K * C / s) :=
      mul_le_mul_of_nonneg_right hτs
        (div_nonneg (mul_nonneg (amplitudeConstant_nonneg _ _ hK) hC) hs.le)
    _ = _ := by field_simp

lemma weighted_initialAmplitude_expanded {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (initialConstant n m K * C) (fun p => V p - (f p 2 / 2) • normalDual G p +
        ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p) := by
  have hvn := weighted_reconstructedLeading h hs hK hC (hc.mono_order (Nat.le_succ m))
    hf hV (hb.mono_order (Nat.le_succ m)) (hbV.mono_order (Nat.le_succ m))
  have hsmall := weighted_scaledAmplitudeCorrection hτ h hs hτs hs1 hK hC hc hf hV hb hbV
  have hf2 := contDiffOn_pi.mp hf 2
  have hlead : ContDiffOn ℝ ∞ (fun p => V p - (f p 2 / 2) • normalDual G p) U :=
    hV.sub ((hf2.div_const 2).smul h.normalDual)
  have hsc : ContDiffOn ℝ ∞ (fun p => ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p) U :=
    by
    simpa only [Pi.smul_def'] using
      (contDiffOn_const (c := (τ : ℂ) / Complex.I)).smul (contDiffOn_amplitudeCorrection h hV hf)
  have hsum : WeightedBound U s m (C + 2 ^ m * C * K + amplitudeConstant n m K * C)
      (fun p => V p - (f p 2 / 2) • normalDual G p +
        ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p) :=
    hvn.add h.isOpen.uniqueDiffOn hs.le hlead hsc hsmall
  have he : C + 2 ^ m * C * K + amplitudeConstant n m K * C = initialConstant n m K * C := by
    unfold initialConstant
    ring
  rw [he] at hsum
  exact hsum

lemma weighted_initialAmplitude {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hb : WeightedBound U s (m + 1) C f) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (initialConstant n m K * C) (initialAmplitude τ G V f) := by
  have hh := weighted_initialAmplitude_expanded hτ h hs hτs hs1 hK hC hc hf hV hb hbV
  exact hh.congr (fun p hp => initialAmplitude_expansion τ (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp)) (h.determinant p hp) (h.good p hp))



lemma weighted_initialAmplitude_free_sub {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : ReconstructionCoefficientBound G U s (m + 1) K)
    (hV : ContDiffOn ℝ ∞ V U) (hbV : WeightedBound U s (m + 1) C V) :
    WeightedBound U s m (amplitudeConstant n m K * (τ / s) * C)
      (fun p => initialAmplitude τ G V (fun _ => 0) p - V p) := by
  have hz : WeightedBound U s (m + 1) C (fun _ : Base => (0 : Fin 3 → ℂ)) :=
    (weightedBound_zero U s (m + 1)).mono_const hC
  have hcorr := weighted_amplitudeCorrection h hs hs1 hK hC hc contDiffOn_const hV hz hbV
  have hsm := contDiffOn_amplitudeCorrection h hV (f := fun _ => 0) contDiffOn_const
  have hh := hcorr.complex_smul_pi h.isOpen.uniqueDiffOn hs
    (div_nonneg (mul_nonneg (amplitudeConstant_nonneg _ _ hK) hC) hs.le)
    hsm ((τ : ℂ) / Complex.I)
  have hnorm : ‖(τ : ℂ) / Complex.I‖ = τ := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  rw [hnorm] at hh
  have he : τ * (amplitudeConstant n m K * C / s) =
      amplitudeConstant n m K * (τ / s) * C := by ring
  rw [he] at hh
  apply hh.congr
  intro p hp
  dsimp only
  rw [initialAmplitude_expansion τ (f := fun _ => 0) (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp)) contDiffAt_const
    (h.determinant p hp) (h.good p hp)]
  simp

lemma contDiffOn_residual (τ : ℝ) {G Z : Field n} {U : Set Base} (h : ModeDomain G U)
    {f : Tensor} (hZ : ContDiffOn ℝ ∞ Z U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (residual τ G f Z) U := by
  intro p hp
  exact (contDiffAt_residual τ (h.smoothAt hp)
    ((hZ p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))).contDiffWithinAt

lemma freeModeConstant_nonneg (n m q : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ freeModeConstant n m K q := by
  induction q with
  | zero => exact amplitudeConstant_nonneg _ _ hK
  | succ q ih => exact add_nonneg ih (mul_nonneg (initialConstant_nonneg _ _ hK)
      (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _))




theorem weighted_modeApprox_free_sub {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 1) K)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m (freeModeConstant n m K q * (τ / s) * C)
      (fun p => modeApprox τ G V (fun _ => 0) q p - V p) := by
  induction q with
  | zero =>
    simpa only [Nat.add_zero, freeModeConstant, modeApprox] using
      weighted_initialAmplitude_free_sub hτ h hs hs1 hK hC hc hVsm hbV
  | succ q ih =>
    have hi := ih (hc.mono_order (by omega)) (hbV.mono_order (by omega))
    have hm : m + 1 + q + 1 = m + (q + 1) + 1 := by omega
    have hce : ReconstructionCoefficientBound G U s (m + 1 + q + 1) K := hm ▸ hc
    have hbe : WeightedBound U s (m + 1 + q + 1) C V := hm ▸ hbV
    have hzero : WeightedBound U s (m + 1 + q + 1) C (fun _ : Base => (0 : Fin 3 → ℂ)) :=
      (weightedBound_zero U s _).mono_const hC
    have hr := weighted_residual_modeApprox hτ hG h hs hs1 hK hC
      contDiffOn_const hVsm hX hY hV q (m + 1) hce.toFullModeCoefficientBound hzero hbe
    have hrsm := contDiffOn_residual τ h (contDiffOn_modeApprox τ h hVsm (f := fun _ => 0) contDiffOn_const q)
      (f := fun _ => 0) contDiffOn_const
    have hn : 0 ≤ fullErrorConstant n (m + 1 + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C :=
      mul_nonneg (mul_nonneg (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _)
        (pow_nonneg (div_nonneg hτ.le hs.le) _)) hC
    have hp := weighted_initialAmplitude hτ h hs hτs hs1 hK hn
      (hc.mono_order (by omega)) hrsm (V := fun _ => 0) contDiffOn_const hr
      ((weightedBound_zero U s (m + 1)).mono_const hn)
    have hp' : WeightedBound U s m
        (initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * (τ / s) * C)
        (zeroParametrix τ G (residual τ G (fun _ => 0) (modeApprox τ G V (fun _ => 0) q))) := by
      apply hp.mono_const
      have hpow : (τ / s) ^ (q + 1) ≤ τ / s := by
        simpa only [pow_one] using pow_le_pow_of_le_one (div_nonneg hτ.le hs.le)
          ((div_le_one hs).2 hτs) (Nat.le_add_left 1 q)
      calc
        _ = (initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * C) *
          (τ / s) ^ (q + 1) := by ring
        _ ≤ (initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * C) *
          (τ / s) := mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (mul_nonneg (initialConstant_nonneg _ _ hK)
              (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _)) hC)
        _ = _ := by ring
    have hpSm := contDiffOn_initialAmplitude τ h (V := fun _ => 0) contDiffOn_const hrsm
    have hh := hi.sub h.isOpen.uniqueDiffOn hs.le
      ((contDiffOn_modeApprox τ h hVsm (f := fun _ => 0) contDiffOn_const q).sub hVsm) hpSm hp'
    have he : freeModeConstant n m K q * (τ / s) * C +
        initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1) * (τ / s) * C =
        freeModeConstant n m K (q + 1) * (τ / s) * C := by
      simp only [freeModeConstant]
      ring
    rw [he] at hh
    apply hh.congr
    intro p hp
    simp only [modeApprox, zeroParametrix]
    abel

end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GradientBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma gradientAmplitude_sub_leading {n : ℕ} (τ : ℝ) (Z V : Field n) (v p : Base) :
    gradientAmplitude τ Z v p - (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • V p =
      coordDeriv v Z p + (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • (Z p - V p) := by
  simp only [gradientAmplitude, smul_sub]
  abel

lemma weighted_modeApprox_free {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 1) K)
    (hbV : WeightedBound U s (m + q + 1) C V) :
    WeightedBound U s m ((1 + freeModeConstant n m K q) * C)
      (modeApprox τ G V (fun _ => 0) q) := by
  have he := weighted_modeApprox_free_sub hτ hG h hs hτs hs1 hK hC hVsm hX hY hV q m hc hbV
  have hz := contDiffOn_modeApprox τ h hVsm (f := fun _ => 0) contDiffOn_const q
  have hv := hbV.mono_order (show m ≤ m + q + 1 by omega)
  have ha := hv.add h.isOpen.uniqueDiffOn hs.le hVsm (hz.sub hVsm) he
  have ha' : WeightedBound U s m (C + freeModeConstant n m K q * (τ / s) * C)
      (modeApprox τ G V (fun _ => 0) q) := ha.congr (fun _ _ => by dsimp only; abel)
  apply ha'.mono_const
  have hrat : τ / s ≤ 1 := (div_le_one hs).2 hτs
  have hnon := mul_nonneg (freeModeConstant_nonneg n m q hK) hC
  nlinarith [mul_le_mul_of_nonneg_left hrat hnon]

lemma gradientErrorConstant_pos (n m q : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 < gradientErrorConstant n m K q := by
  have h1 := freeModeConstant_nonneg n (m + 1) q hK
  have h0 := freeModeConstant_nonneg n m q hK
  unfold gradientErrorConstant
  linarith




theorem weighted_gradientAmplitude_free_error {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {G V : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hVsm : ContDiffOn ℝ ∞ V U)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 2) K)
    (hbV : WeightedBound U s (m + q + 2) C V)
    (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m (gradientErrorConstant n m K q * (C / s))
      (fun p => gradientAmplitude τ (modeApprox τ G V (fun _ => 0) q) v p -
        (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • V p) := by
  have hm : m + 1 + q + 1 = m + q + 2 := by omega
  have hc' : ReconstructionCoefficientBound G U s (m + 1 + q + 1) K := hm.symm ▸ hc
  have hb' : WeightedBound U s (m + 1 + q + 1) C V := hm.symm ▸ hbV
  have hbZ := weighted_modeApprox_free hτ hG h hs hτs hs1 hK hC hVsm hX hY hV q (m + 1) hc' hb'
  have hZsm := contDiffOn_modeApprox τ h hVsm (f := fun _ => 0) contDiffOn_const q
  have hd := hbZ.directional h.isOpen hs hZsm v
  have hdn : 0 ≤ (1 + freeModeConstant n (m + 1) K q) * C / s := by
    exact div_nonneg (mul_nonneg (by linarith [freeModeConstant_nonneg n (m + 1) q hK]) hC) hs.le
  have hd' : WeightedBound U s m ((1 + freeModeConstant n (m + 1) K q) * C / s)
      (coordDeriv v (modeApprox τ G V (fun _ => 0) q)) := by
    exact hd.mono_const (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hv hdn)
  have he := weighted_modeApprox_free_sub hτ hG h hs hτs hs1 hK hC hVsm hX hY hV q m
    (hc.mono_order (by omega)) (hbV.mono_order (by omega))
  have hen := mul_nonneg (mul_nonneg (freeModeConstant_nonneg n m q hK)
    (div_nonneg hτ.le hs.le)) hC
  have he' := he.complex_smul_pi h.isOpen.uniqueDiffOn hs hen (hZsm.sub hVsm)
    (Complex.I / (τ : ℂ) * (v.1 : ℂ))
  have hnorm : ‖Complex.I / (τ : ℂ) * (v.1 : ℂ)‖ ≤ 1 / τ := by
    rw [norm_mul, norm_div]
    simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    exact mul_le_of_le_one_right (div_nonneg zero_le_one hτ.le)
      (by simpa only [Real.norm_eq_abs] using (norm_fst_le v).trans hv)
  have he'' : WeightedBound U s m (freeModeConstant n m K q * C / s)
      (fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) •
        (modeApprox τ G V (fun _ => 0) q p - V p)) := by
    apply he'.mono_const
    calc
      _ ≤ (1 / τ) * (freeModeConstant n m K q * (τ / s) * C) :=
        mul_le_mul_of_nonneg_right hnorm hen
      _ = _ := by field_simp [ne_of_gt hτ]
  have hsc : ContDiffOn ℝ ∞ (fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) •
      (modeApprox τ G V (fun _ => 0) q p - V p)) U := by
    simpa only [Pi.smul_def'] using
      (contDiffOn_const (c := Complex.I / (τ : ℂ) * (v.1 : ℂ))).smul (hZsm.sub hVsm)
  have ha := hd'.add h.isOpen.uniqueDiffOn hs.le (contDiffOn_coordDeriv_vector h.isOpen hZsm v) hsc he''
  have heq : (1 + freeModeConstant n (m + 1) K q) * C / s + freeModeConstant n m K q * C / s =
      gradientErrorConstant n m K q * (C / s) := by unfold gradientErrorConstant; ring
  rw [heq] at ha
  exact ha.congr (fun p _ => gradientAmplitude_sub_leading τ _ V v p)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticError
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.WeightedEstimates

lemma weighted_conjugate {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {Z : Base → CVec n} (hs : 0 < s) (hC : 0 ≤ C)
    (hZ : ContDiffOn ℝ ∞ Z U) (hbZ : WeightedBound U s m C Z) :
    WeightedBound U s m C (fun p => conjugate (Z p)) := by
  apply WeightedBound.pi hU hs hC
  · intro i
    exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hZ i)
  · intro i
    have hh := (hbZ.component hU hs.le hC hZ i).linear hU hs.le
      (contDiffOn_pi.mp hZ i) Complex.conjCLE.toContinuousLinearMap
    apply hh.mono_const
    apply mul_le_of_le_one_left hC
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp



lemma halfReCLM_norm_le : ‖halfReCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [halfReCLM_apply]
  simp only [norm_div, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), one_mul]
  have hr := Complex.abs_re_le_norm z
  linarith [norm_nonneg z]

lemma weighted_zeroPair {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {A B : Base → CVec n} (hs : 0 < s)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hbA : WeightedBound U s m C A) (hbB : WeightedBound U s m D B) :
    WeightedBound U s m ((n : ℝ) * (2 ^ m * C * D))
      (fun p => zeroPair (A p) (B p)) := by
  have hc := contDiffOn_conjugate hB
  have hbc := weighted_conjugate hU hs hD hB hbB
  have hd := hbA.dot hU hs.le hC hD hA hc hbc
  have hds : ContDiffOn ℝ ∞ (fun p => A p ⬝ᵥ conjugate (B p)) U :=
    ContDiffOn.sum (fun i _ => (contDiffOn_pi.mp hA i).mul (contDiffOn_pi.mp hc i))
  have hh := hd.linear hU hs.le hds halfReCLM
  simp only [Fintype.card_fin] at hh
  have hn : 0 ≤ (n : ℝ) * (2 ^ m * C * D) := by positivity
  have hh' := hh.mono_const (mul_le_of_le_one_left hn halfReCLM_norm_le)
  simpa only [Function.comp_def, halfReCLM_apply, zeroPair, Fintype.card_fin] using hh'

lemma zeroPair_sub_left {n : ℕ} (A B C : CVec n) :
    zeroPair (A - B) C = zeroPair A C - zeroPair B C := by
  simp [zeroPair, sub_dotProduct, sub_div]

lemma zeroPair_sub_right {n : ℕ} (A B C : CVec n) :
    zeroPair A (B - C) = zeroPair A B - zeroPair A C := by
  have hc : conjugate (B - C) = conjugate B - conjugate C := by ext i; simp [conjugate]
  simp [zeroPair, hc, dotProduct_sub, sub_div]

lemma zeroPair_error_identity {n : ℕ} (A B Z W : CVec n) :
    zeroPair Z W - zeroPair A B = zeroPair (Z - A) W + zeroPair A (W - B) := by
  rw [zeroPair_sub_left, zeroPair_sub_right]
  ring




theorem weighted_zeroPair_error {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C D E F : ℝ} {m : ℕ} {A B Z W : Base → CVec n} (hs : 0 < s)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U)
    (hbA : WeightedBound U s m C A) (hbW : WeightedBound U s m D W)
    (heZ : WeightedBound U s m E (fun p => Z p - A p))
    (heW : WeightedBound U s m F (fun p => W p - B p)) :
    WeightedBound U s m ((n : ℝ) * 2 ^ m * (E * D + C * F))
      (fun p => zeroPair (Z p) (W p) - zeroPair (A p) (B p)) := by
  have h1 := weighted_zeroPair hU hs hE hD (hZ.sub hA) hW heZ hbW
  have h2 := weighted_zeroPair hU hs hC hF hA (hW.sub hB) hbA heW
  have hh := h1.add hU hs.le (contDiffOn_zeroPair (hZ.sub hA) hW)
    (contDiffOn_zeroPair hA (hW.sub hB)) h2
  have he : (n : ℝ) * (2 ^ m * E * D) + (n : ℝ) * (2 ^ m * C * F) =
      (n : ℝ) * 2 ^ m * (E * D + C * F) := by ring
  rw [he] at hh
  exact hh.congr (fun p _ => zeroPair_error_identity (A p) (B p) (Z p) (W p))

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanError
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates



lemma FreeCoefficient.sub {n : ℕ} {G V W : Field n} {U : Set Base}
    (hV : FreeCoefficient G U V) (hW : FreeCoefficient G U W) :
    FreeCoefficient G U (fun p => V p - W p) := by
  refine ⟨hV.smooth.sub hW.smooth, ?_, ?_, ?_⟩
  · intro p hp; simp [dotProduct_sub, hV.perpX p hp, hW.perpX p hp]
  · intro p hp; simp [dotProduct_sub, hV.perpY p hp, hW.perpY p hp]
  · intro p hp; simp [dotProduct_sub, hV.perpSecond p hp, hW.perpSecond p hp]


lemma weighted_leadingDerivative {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {V : Field n}
    {U : Set Base} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} (hs : 0 < s)
    (hC : 0 ≤ C) (hV : ContDiffOn ℝ ∞ V U) (hb : WeightedBound U s m C V)
    (v : Base) (hv : ‖v‖ ≤ 1) : WeightedBound U s m (C / τ) (leadingDerivative τ V v) := by
  have hh := hb.complex_smul_pi hU hs hC hV (Complex.I / (τ : ℂ) * (v.1 : ℂ))
  apply hh.mono_const
  have hn : ‖Complex.I / (τ : ℂ) * (v.1 : ℂ)‖ ≤ 1 / τ := by
    rw [norm_mul, norm_div]
    simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    exact mul_le_of_le_one_right (div_nonneg zero_le_one hτ.le)
      (by simpa only [Real.norm_eq_abs] using (norm_fst_le v).trans hv)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using mul_le_mul_of_nonneg_right hn hC

lemma weighted_gradient_free {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {G V : Field n}
    (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hV : FreeCoefficient G U V) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 2) K)
    (hbV : WeightedBound U s (m + q + 2) C V) (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m ((1 + gradientErrorConstant n m K q) * (C / τ))
      (gradientAmplitude τ (modeApprox τ G V (fun _ => 0) q) v) := by
  have he := weighted_gradientAmplitude_free_error hτ hG h hs hτs hs1 hK hC
    hV.smooth hV.perpX hV.perpY hV.perpSecond q m hc hbV v hv
  have hl := weighted_leadingDerivative hτ h.isOpen.uniqueDiffOn hs hC hV.smooth
    (hbV.mono_order (show m ≤ m + q + 2 by omega)) v hv
  have hE := (gradientErrorConstant_pos n m q hK).le
  have hZ := contDiffOn_modeApprox τ h hV.smooth (f := fun _ => 0) contDiffOn_const q
  have hsZ := contDiffOn_gradientAmplitude h.isOpen hZ τ v
  have hsL := contDiffOn_leadingDerivative τ hV.smooth v
  have ha := he.add h.isOpen.uniqueDiffOn hs.le (hsZ.sub hsL) hsL hl
  have ha' := ha.congr (fun p _ => (sub_add_cancel _ _).symm)
  apply ha'.mono_const
  have hdiv : C / s ≤ C / τ := div_le_div_of_nonneg_left hC hτ hτs
  nlinarith [mul_le_mul_of_nonneg_left hdiv hE]



lemma meanErrorConstant_nonneg (n m q : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ meanErrorConstant n m K q := by
  have hE := (gradientErrorConstant_pos n m q hK).le
  unfold meanErrorConstant
  positivity




theorem weighted_modeMeanError {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {G V W : Field n}
    (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C D : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hV : FreeCoefficient G U V) (hW : FreeCoefficient G U W) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 2) K)
    (hbV : WeightedBound U s (m + q + 2) C V)
    (hbW : WeightedBound U s (m + q + 2) D W)
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m (meanErrorConstant n m K q * (C * D / (s * τ)))
      (modeMeanError τ G V W q v w) := by
  have hE := (gradientErrorConstant_pos n m q hK).le
  have hZV := contDiffOn_modeApprox τ h hV.smooth (f := fun _ => 0) contDiffOn_const q
  have hZW := contDiffOn_modeApprox τ h hW.smooth (f := fun _ => 0) contDiffOn_const q
  have hA := contDiffOn_leadingDerivative τ hV.smooth v
  have hB := contDiffOn_leadingDerivative τ hW.smooth w
  have hZ := contDiffOn_gradientAmplitude h.isOpen hZV τ v
  have hY := contDiffOn_gradientAmplitude h.isOpen hZW τ w
  have hbA := weighted_leadingDerivative hτ h.isOpen.uniqueDiffOn hs hC hV.smooth
    (hbV.mono_order (show m ≤ m + q + 2 by omega)) v hv
  have hbY := weighted_gradient_free hτ hG h hs hτs hs1 hK hD hW q m hc hbW w hw
  have heZ := weighted_gradientAmplitude_free_error hτ hG h hs hτs hs1 hK hC
    hV.smooth hV.perpX hV.perpY hV.perpSecond q m hc hbV v hv
  have heY := weighted_gradientAmplitude_free_error hτ hG h hs hτs hs1 hK hD
    hW.smooth hW.perpX hW.perpY hW.perpSecond q m hc hbW w hw
  have hnC : 0 ≤ C / τ := div_nonneg hC hτ.le
  have hnD : 0 ≤ (1 + gradientErrorConstant n m K q) * (D / τ) := by positivity
  have hnE : 0 ≤ gradientErrorConstant n m K q * (C / s) := by positivity
  have hnF : 0 ≤ gradientErrorConstant n m K q * (D / s) := by positivity
  have hh := ClosedSurfaceR4.QuadraticMean.weighted_zeroPair_error h.isOpen.uniqueDiffOn hs
    hnC hnD hnE hnF hA hB hZ hY hbA hbY heZ heY
  have heq : (n : ℝ) * 2 ^ m *
      (gradientErrorConstant n m K q * (C / s) *
        ((1 + gradientErrorConstant n m K q) * (D / τ)) +
        C / τ * (gradientErrorConstant n m K q * (D / s))) =
      meanErrorConstant n m K q * (C * D / (s * τ)) := by
    unfold meanErrorConstant
    ring
  rw [heq] at hh
  exact hh

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanDifferences
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma gradientAmplitude_congr {n : ℕ} (τ : ℝ) {Z W : Field n} {p : Base}
    (he : Z =ᶠ[nhds p] W) (v : Base) : gradientAmplitude τ Z v p = gradientAmplitude τ W v p := by
  simp only [gradientAmplitude, coordDeriv, he.fderiv_eq, he.self_of_nhds]

lemma gradientAmplitude_sub {n : ℕ} (τ : ℝ) {Z W : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) (v : Base) :
    gradientAmplitude τ (fun p => Z p - W p) v p =
      gradientAmplitude τ Z v p - gradientAmplitude τ W v p := by
  rw [gradientAmplitude, partial_sub hZ hW]
  ext i
  simp only [gradientAmplitude, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma gradientAmplitude_free_sub {n : ℕ} (τ : ℝ) {G V W : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) (q : ℕ) (v : Base) :
    EqOn (gradientAmplitude τ (modeApprox τ G (fun p => V p - W p) (fun _ => 0) q) v)
      (fun p => gradientAmplitude τ (modeApprox τ G V (fun _ => 0) q) v p -
        gradientAmplitude τ (modeApprox τ G W (fun _ => 0) q) v p) U := by
  have he := modeApprox_sub τ hG h hV hW (f := fun _ => 0) (g := fun _ => 0)
    contDiffOn_const contDiffOn_const q
  simp only [sub_self] at he
  have hZ := contDiffOn_modeApprox τ h hV (f := fun _ => 0) contDiffOn_const q
  have hY := contDiffOn_modeApprox τ h hW (f := fun _ => 0) contDiffOn_const q
  intro p hp
  have hee := Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => he hz)
  rw [gradientAmplitude_congr τ hee,
    gradientAmplitude_sub τ (((hZ p hp).contDiffAt (h.isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (((hY p hp).contDiffAt (h.isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]

lemma leadingDerivative_sub {n : ℕ} (τ : ℝ) (V W : Field n) (v : Base) (p : Base) :
    leadingDerivative τ (fun p => V p - W p) v p =
      leadingDerivative τ V v p - leadingDerivative τ W v p := by
  simp only [leadingDerivative, smul_sub]

lemma contDiffOn_modeMeanError {n : ℕ} (τ : ℝ) {G V W : Field n} {U : Set Base}
    (h : ModeDomain G U) (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U)
    (q : ℕ) (v w : Base) : ContDiffOn ℝ ∞ (modeMeanError τ G V W q v w) U := by
  have hZ := contDiffOn_gradientAmplitude h.isOpen
    (contDiffOn_modeApprox τ h hV (f := fun _ => 0) contDiffOn_const q) τ v
  have hY := contDiffOn_gradientAmplitude h.isOpen
    (contDiffOn_modeApprox τ h hW (f := fun _ => 0) contDiffOn_const q) τ w
  exact (ClosedSurfaceR4.QuadraticMean.contDiffOn_zeroPair hZ hY).sub
    (ClosedSurfaceR4.QuadraticMean.contDiffOn_zeroPair
      (contDiffOn_leadingDerivative τ hV v) (contDiffOn_leadingDerivative τ hW w))

lemma modeMeanError_sub_left {n : ℕ} (τ : ℝ) {G V W Z : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) (q : ℕ) (v w : Base) :
    EqOn (modeMeanError τ G (fun p => V p - W p) Z q v w)
      (fun p => modeMeanError τ G V Z q v w p - modeMeanError τ G W Z q v w p) U := by
  intro p hp
  unfold modeMeanError
  rw [gradientAmplitude_free_sub τ hG h hV hW q v hp, leadingDerivative_sub,
    ClosedSurfaceR4.QuadraticMean.zeroPair_sub_left,
    ClosedSurfaceR4.QuadraticMean.zeroPair_sub_left]
  ring

lemma modeMeanError_sub_right {n : ℕ} (τ : ℝ) {G V W Z : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) (q : ℕ) (v w : Base) :
    EqOn (modeMeanError τ G Z (fun p => V p - W p) q v w)
      (fun p => modeMeanError τ G Z V q v w p - modeMeanError τ G Z W q v w p) U := by
  intro p hp
  unfold modeMeanError
  rw [gradientAmplitude_free_sub τ hG h hV hW q w hp, leadingDerivative_sub,
    ClosedSurfaceR4.QuadraticMean.zeroPair_sub_right,
    ClosedSurfaceR4.QuadraticMean.zeroPair_sub_right]
  ring

lemma modeMeanError_difference {n : ℕ} (τ : ℝ) {G V W : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) (q : ℕ) (v w : Base) :
    EqOn (fun p => modeMeanError τ G V V q v w p - modeMeanError τ G W W q v w p)
      (fun p => modeMeanError τ G (fun p => V p - W p) V q v w p +
        modeMeanError τ G W (fun p => V p - W p) q v w p) U := by
  intro p hp
  dsimp only
  rw [modeMeanError_sub_left τ hG h hV hW q v w hp,
    modeMeanError_sub_right τ hG h hV hW q v w hp]
  ring




theorem weighted_modeMeanError_difference {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {G V W : Field n}
    (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C D : ℝ} (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hV : FreeCoefficient G U V) (hW : FreeCoefficient G U W) (q m : ℕ)
    (hc : ReconstructionCoefficientBound G U s (m + q + 2) K)
    (hbV : WeightedBound U s (m + q + 2) C V)
    (hbW : WeightedBound U s (m + q + 2) C W)
    (hbDiff : WeightedBound U s (m + q + 2) D (fun p => V p - W p))
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m (2 * meanErrorConstant n m K q * (C * D / (s * τ)))
      (fun p => modeMeanError τ G V V q v w p - modeMeanError τ G W W q v w p) := by
  have h1 := weighted_modeMeanError hτ hG h hs hτs hs1 hK hD hC (hV.sub hW) hV q m
    hc hbDiff hbV v w hv hw
  have h2 := weighted_modeMeanError hτ hG h hs hτs hs1 hK hC hD hW (hV.sub hW) q m
    hc hbW hbDiff v w hv hw
  have hh := h1.add h.isOpen.uniqueDiffOn hs.le
    (contDiffOn_modeMeanError τ h (hV.smooth.sub hW.smooth) hV.smooth q v w)
    (contDiffOn_modeMeanError τ h hW.smooth (hV.smooth.sub hW.smooth) q v w) h2
  have he : meanErrorConstant n m K q * (D * C / (s * τ)) +
      meanErrorConstant n m K q * (C * D / (s * τ)) =
      2 * meanErrorConstant n m K q * (C * D / (s * τ)) := by ring
  rw [he] at hh
  exact hh.congr (modeMeanError_difference τ hG h hV.smooth hW.smooth q v w)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma weighted_linearIsometry {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set E} (hU : UniqueDiffOn ℝ U) {f : E → X} (hf : ContDiffOn ℝ ∞ f U)
    {s C : ℝ} {m : ℕ} (hb : WeightedBound U s m C f) (A : X →ₗᵢ[ℝ] Y) :
    WeightedBound U s m C (A ∘ f) := by
  intro j hj p hp
  rw [A.norm_iteratedFDerivWithin_comp_left (hf p hp) hU hp
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
  exact hb j hj p hp

lemma weighted_freeSeed {F : RField 4} {U : Set Base} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F U) {δ τ s C D : ℝ} {m : ℕ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D) {b : Base → ℝ}
    (hb : ContDiffOn ℝ ∞ b U) (hbb : WeightedBound U s m C b)
    (hbN : WeightedBound U s m D (freeNormal F)) :
    WeightedBound U s m ((Real.sqrt 2 * 2 ^ m * C * D) * (δ * τ)) (freeSeed δ τ b F) := by
  have hNc := (complexifyCLM 4).contDiff.comp_contDiffOn (contDiffOn_freeNormal hF h)
  have hbc := Complex.ofRealCLM.contDiff.comp_contDiffOn hb
  have hbNc := weighted_linearIsometry h.isOpen.uniqueDiffOn (contDiffOn_freeNormal hF h)
    hbN (complexifyLI 4)
  have hbbc := weighted_linearIsometry h.isOpen.uniqueDiffOn hb hbb Complex.ofRealLI
  have ha : WeightedBound U s m (2 ^ m * C * D)
      (fun p => (b p : ℂ) • complexify (freeNormal F p)) := by
    apply WeightedBound.pi h.isOpen.uniqueDiffOn hs (by positivity)
    · intro i; exact hbc.mul (contDiffOn_pi.mp hNc i)
    · intro i
      exact hbbc.mul h.isOpen.uniqueDiffOn hs.le hC hD hbc (contDiffOn_pi.mp hNc i)
        (hbNc.component h.isOpen.uniqueDiffOn hs.le hD hNc i)
  have hh := ha.complex_smul_pi h.isOpen.uniqueDiffOn hs (by positivity) (hbc.smul hNc)
    ((Real.sqrt 2 * δ * τ : ℝ) : ℂ)
  have he : ‖((Real.sqrt 2 * δ * τ : ℝ) : ℂ)‖ * (2 ^ m * C * D) =
      (Real.sqrt 2 * 2 ^ m * C * D) * (δ * τ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  rw [he] at hh
  apply hh.congr
  intro p hp
  ext i
  change ((Real.sqrt 2 * δ * τ * b p : ℝ) : ℂ) * complexify (freeNormal F p) i =
    ((Real.sqrt 2 * δ * τ : ℝ) : ℂ) * ((b p : ℂ) * complexify (freeNormal F p) i)
  push_cast
  ring



theorem weighted_normalizedMeanError {F : RField 4} {U : Set Base} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F U) {δ τ s K C D : ℝ} (hδ : 0 < δ) (hτ : 0 < τ)
    (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b U) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + q + 2) K)
    (hbb : WeightedBound U s (m + q + 2) C b)
    (hbN : WeightedBound U s (m + q + 2) D (freeNormal F))
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m (meanErrorConstant 4 m K q *
      (Real.sqrt 2 * 2 ^ (m + q + 2) * C * D) ^ 2 * (τ / s))
      (normalizedMeanError δ τ F b q v w) := by
  have hbV := weighted_freeSeed hF h hδ.le hτ.le hs hC hD hb hbb hbN
  have hV := freeSeed_isFree hF h δ τ hb
  have hh := weighted_modeMeanError hτ (contDiff_complexify hF) (h.complexDomain hF)
    hs hτs hs1 hK (by positivity) (by positivity) hV hV q m hc hbV hbV v w hv hw
  have hsm := contDiffOn_modeMeanError τ (h.complexDomain hF) hV.smooth hV.smooth q v w
  have hn := hh.const_smul h.isOpen.uniqueDiffOn hsm ((δ ^ 2)⁻¹)
  have he : |(δ ^ 2)⁻¹| * (meanErrorConstant 4 m K q *
      (((Real.sqrt 2 * 2 ^ (m + q + 2) * C * D) * (δ * τ)) *
        ((Real.sqrt 2 * 2 ^ (m + q + 2) * C * D) * (δ * τ)) / (s * τ))) =
      meanErrorConstant 4 m K q * (Real.sqrt 2 * 2 ^ (m + q + 2) * C * D) ^ 2 * (τ / s) := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
  rw [he] at hn
  exact hn

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma freeSeed_sub (δ τ : ℝ) (b c : Base → ℝ) (F : RField 4) :
    freeSeed δ τ (fun p => b p - c p) F = fun p => freeSeed δ τ b F p - freeSeed δ τ c F p := by
  ext p i
  simp only [freeSeed, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_sub]
  ring

theorem weighted_normalizedMeanError_difference {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) {δ τ s K C D B : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    {b c : Base → ℝ} (hb : ContDiffOn ℝ ∞ b U) (hcs : ContDiffOn ℝ ∞ c U) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + q + 2) K)
    (hbb : WeightedBound U s (m + q + 2) C b)
    (hbc : WeightedBound U s (m + q + 2) C c)
    (hbDiff : WeightedBound U s (m + q + 2) D (fun p => b p - c p))
    (hbN : WeightedBound U s (m + q + 2) B (freeNormal F))
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m (2 * meanErrorConstant 4 m K q *
      (Real.sqrt 2 * 2 ^ (m + q + 2) * B) ^ 2 * C * D * (τ / s))
      (fun p => normalizedMeanError δ τ F b q v w p - normalizedMeanError δ τ F c q v w p) := by
  have hbV := weighted_freeSeed hF h hδ.le hτ.le hs hC hB hb hbb hbN
  have hbW := weighted_freeSeed hF h hδ.le hτ.le hs hC hB hcs hbc hbN
  have hbD := weighted_freeSeed hF h hδ.le hτ.le hs hD hB (hb.sub hcs) hbDiff hbN
  rw [freeSeed_sub] at hbD
  have hV := freeSeed_isFree hF h δ τ hb
  have hW := freeSeed_isFree hF h δ τ hcs
  have hh := weighted_modeMeanError_difference hτ (contDiff_complexify hF) (h.complexDomain hF)
    hs hτs hs1 hK (by positivity) (by positivity) hV hW q m hc hbV hbW hbD v w hv hw
  have hsm := (contDiffOn_modeMeanError τ (h.complexDomain hF) hV.smooth hV.smooth q v w).sub
    (contDiffOn_modeMeanError τ (h.complexDomain hF) hW.smooth hW.smooth q v w)
  have hn := hh.const_smul h.isOpen.uniqueDiffOn hsm ((δ ^ 2)⁻¹)
  have he : |(δ ^ 2)⁻¹| * (2 * meanErrorConstant 4 m K q *
      (((Real.sqrt 2 * 2 ^ (m + q + 2) * C * B) * (δ * τ)) *
        ((Real.sqrt 2 * 2 ^ (m + q + 2) * D * B) * (δ * τ)) / (s * τ))) =
      2 * meanErrorConstant 4 m K q * (Real.sqrt 2 * 2 ^ (m + q + 2) * B) ^ 2 * C * D * (τ / s) := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
  rw [he] at hn
  apply hn.congr
  intro p hp
  dsimp only [normalizedMeanError, smul_eq_mul]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RootMean
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


lemma sqrt_difference {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.sqrt u - Real.sqrt v = (u - v) * rootDifferenceCoefficient ![u, v] := by
  have hh : Real.sqrt u + Real.sqrt v ≠ 0 := ne_of_gt
    (add_pos (Real.sqrt_pos.2 hu) (Real.sqrt_pos.2 hv))
  dsimp [rootDifferenceCoefficient]
  rw [← div_eq_mul_inv]
  apply (eq_div_iff hh).2
  nlinarith [Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.RootMean ClosedSurfaceR4.WeightedEstimates
open Set



lemma contDiffOn_meanTensor {V : Set Base} {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F V) {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b V)
    (δ τ : ℝ) (q : ℕ) : ContDiffOn ℝ ∞ (meanTensor δ τ F b q) V := by
  apply contDiffOn_pi.mpr
  intro i
  have hv := freeSeed_isFree hF h δ τ hb
  exact (contDiffOn_modeMeanError τ (h.complexDomain hF) hv.smooth hv.smooth q
    (firstDirection i) (secondDirection i)).const_smul ((δ ^ 2)⁻¹)

lemma weighted_meanTensor {V : Set Base} {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F V) {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b V)
    {δ τ s K C B : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) V s (m + q + 2) K)
    (hbb : WeightedBound V s (m + q + 2) C b)
    (hbN : WeightedBound V s (m + q + 2) B (freeNormal F)) :
    WeightedBound V s m
      (meanErrorConstant 4 m K q * (Real.sqrt 2 * 2 ^ (m + q + 2) * C * B) ^ 2 * (τ / s))
      (meanTensor δ τ F b q) := by
  have hm := contDiffOn_meanTensor hF h hb δ τ q
  have hM := meanErrorConstant_nonneg 4 m q hK
  apply WeightedBound.pi h.isOpen.uniqueDiffOn hs (by positivity)
    (fun i => contDiffOn_pi.mp hm i)
  intro i
  exact weighted_normalizedMeanError hF h hδ hτ hs hτs hs1 hK hC hB hb q m hc hbb hbN
    (firstDirection i) (secondDirection i) (firstDirection_norm i) (secondDirection_norm i)

lemma weighted_meanTensor_difference {V : Set Base} {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F V) {b c : Base → ℝ} (hb : ContDiffOn ℝ ∞ b V)
    (hcs : ContDiffOn ℝ ∞ c V) {δ τ s K C D B : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) V s (m + q + 2) K)
    (hbb : WeightedBound V s (m + q + 2) C b)
    (hbc : WeightedBound V s (m + q + 2) C c)
    (hbD : WeightedBound V s (m + q + 2) D (fun p => b p - c p))
    (hbN : WeightedBound V s (m + q + 2) B (freeNormal F)) :
    WeightedBound V s m (2 * meanErrorConstant 4 m K q *
      (Real.sqrt 2 * 2 ^ (m + q + 2) * B) ^ 2 * C * D * (τ / s))
      (fun p => meanTensor δ τ F b q p - meanTensor δ τ F c q p) := by
  have hM := meanErrorConstant_nonneg 4 m q hK
  have hm := (contDiffOn_meanTensor hF h hb δ τ q).sub
    (contDiffOn_meanTensor hF h hcs δ τ q)
  apply WeightedBound.pi h.isOpen.uniqueDiffOn hs (by positivity)
    (fun i => contDiffOn_pi.mp hm i)
  intro i
  exact weighted_normalizedMeanError_difference hF h hδ hτ hs hτs hs1 hK hC hD hB hb hcs q m
    hc hbb hbc hbD hbN (firstDirection i) (secondDirection i)
    (firstDirection_norm i) (secondDirection_norm i)



end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set

lemma weighted_coefficient {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A : Base → Tensor}
    {s J P C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hC : 0 ≤ C) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m C A) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * C)
      (coefficient Q e A) := by
  have hAe := hAB.comp_coordinates hV hU hs hs1 hJ hC he hA heU heB
  have hh := hQB.clm_apply hV hs.le hP (by positivity) hQ (hA.comp he heU) hAe
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  ring

lemma weighted_coefficient_difference {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A B : Base → Tensor}
    {s J P D : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hD : 0 ≤ D) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m D (A - B)) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * D)
      (fun p => coefficient Q e A p - coefficient Q e B p) := by
  apply (weighted_coefficient hU hV hs hs1 hJ hP hD hQ he heU (hA.sub hB) heB hQB hAB).congr
  intro p hp
  exact (map_sub (Q p) (A (e p)) (B (e p))).symm




end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set






variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}


lemma LocalBounds.amplitude_smooth (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (hρ : 0 < ρ) {A : Base → Tensor} (hA : ContDiffOn ℝ ∞ A U)
    (hball : InTrialBall U reference r A) :
    ContDiffOn ℝ ∞ (phaseAmplitude ψ (coefficient Q e A)) V := by
  have hR := coefficient_trial_range h.invInto h.margin hball
  exact contDiffOn_phaseAmplitude h.smoothPsi
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA)
    (fun p hp => hρ.trans_le (hR hp).1)



end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set
variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

lemma LocalBounds.transport_bound (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1)
    {m : ℕ} {D : ℝ} {g : Base → Tensor} (hD : 0 ≤ D) (hg : ContDiffOn ℝ ∞ g V)
    (hb : WeightedBound V s m D g) : WeightedBound U s m (outputFactor d m * D)
      (fun p => pullbackField χ p (g (χ p))) := by
  have hc := hb.comp_coordinates h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
    (d.chi_pos m) hD h.smoothChi hg h.chiInto (d.chi_bound m)
  have hchi := le_trans zero_le_one (d.chi_pos m)
  have hh := (d.pull_bound m).clm_apply h.openU.uniqueDiffOn hs.le
    (le_trans zero_le_one (d.pull_pos m)) (by positivity) h.smoothPullback
    (hg.comp h.smoothChi h.chiInto) hc
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  dsimp [outputFactor]
  ring

lemma LocalBounds.mean_smooth (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (hρ : 0 < ρ) {A : Base → Tensor} (hA : ContDiffOn ℝ ∞ A U)
    (hball : InTrialBall U reference r A) (δ : ℝ) (q : ℕ) (η : ℝ) :
    ContDiffOn ℝ ∞ (meanTerm δ s F ψ Q χ e q η A) U := by
  exact h.smoothPullback.clm_apply
    ((contDiffOn_meanTensor h.smoothF h.domain (h.amplitude_smooth hρ hA hball) δ (η * s) q).comp
      h.smoothChi h.chiInto)




end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.FiniteMean
open ClosedSurfaceR4.WeightedEstimates Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem MeanBounds.finset_sum {ι : Type*} {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} (hs : 0 ≤ s) {reference : E → F} {r : ℝ} {L : ℕ}
    (a : Finset ι) (T : ι → ℝ → (E → F) → E → F) (B K : ι → ℕ → ℝ → ℝ)
    (hT : ∀ i ∈ a, MeanBounds U s reference r L (T i) (B i) (K i)) :
    MeanBounds U s reference r L (fun η f x => ∑ i ∈ a, T i η f x)
      (fun m C => 1 + ∑ i ∈ a, B i m C) (fun m C => 1 + ∑ i ∈ a, K i m C) := by
  constructor
  · intro m C hC
    have hh : 0 ≤ ∑ i ∈ a, B i m C := Finset.sum_nonneg
      (fun i hi => le_trans zero_le_one ((hT i hi).B_pos m C hC))
    linarith
  · intro m C hC
    have hh : 0 ≤ ∑ i ∈ a, K i m C := Finset.sum_nonneg
      (fun i hi => le_trans zero_le_one ((hT i hi).K_pos m C hC))
    linarith
  · intro η hη hη1 f hf hball
    exact ContDiffOn.sum (fun i hi => (hT i hi).smooth η hη hη1 f hf hball)
  · intro η hη hη1 m C f hC hf hball hb
    have hh := WeightedBound.finset_sum hU hs a (fun i => η * B i m C)
      (fun i => T i η f) (fun i hi => (hT i hi).smooth η hη hη1 f hf hball)
      (fun i hi => (hT i hi).value η hη hη1 m C f hC hf hball hb)
    apply hh.mono_const
    rw [← Finset.mul_sum, mul_add, mul_one]
    linarith
  · intro η hη hη1 m C D f g hC hD hf hg hballf hballg hbf hbg hbd
    have hh := WeightedBound.finset_sum hU hs a (fun i => K i m C * η * D)
      (fun i => T i η f - T i η g)
      (fun i hi => ((hT i hi).smooth η hη hη1 f hf hballf).sub
        ((hT i hi).smooth η hη hη1 g hg hballg))
      (fun i hi => (hT i hi).difference η hη hη1 m C D f g hC hD hf hg hballf hballg hbf hbg hbd)
    have hbound : (∑ i ∈ a, K i m C * η * D) ≤ (1 + ∑ i ∈ a, K i m C) * η * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, add_mul, one_mul, add_mul]
      have hpos : 0 ≤ η * D := mul_nonneg hη.le hD
      linarith
    apply (hh.mono_const hbound).congr
    intro x hx
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]

end ClosedSurfaceR4.FiniteMean

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrixLinearity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the finite homogeneous correction in its initial amplitude. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma homogeneousLM_apply (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (j : ℕ) (z : E) :
    homogeneousLM A S j z = improve A S 0 z j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [homogeneousLM, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, ih, improve, sub_zero]

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedFreeLinearity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free seed and its finite perturbed correction are actual linear maps. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial
variable {n : ℕ} {G : Field n} {U : Set Base}

lemma perturbedFreeLM_apply (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (V : SupportedField (F := Ambient n) K) :
    perturbedFreeLM τ hG h K hKU R q V = perturbedFreeMode τ hG h K hKU R V q := by
  exact FiniteParametrix.homogeneousLM_apply _ _ q _

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMetricMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global supported metric mean fields for the actual charted free seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

lemma metricMeanField_apply (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact)
    (x : SmallModes.Base) :
    c.metricMeanField δ q b x = c.e.source.indicator
      (fun x => pullbackField c.e x (c.metricMeanInChart δ q b (c.e x))) x := rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff square-root trial amplitudes on the actual transported support.
These use the original tensor field and the inverse of its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

lemma trialAmplitude_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiffOn ℝ ∞ A c.e.source) (hball : InTrialBall c.e.source reference r A)
    (y : SmallModes.Base) :
    c.trialAmplitude ψ Q h hρ A y = phaseAmplitude ψ (coefficient Q c.e.symm A) y := by
  classical
  simp only [trialAmplitude, dite_eq_left (show ContDiffOn ℝ ∞ A c.e.source ∧
    InTrialBall c.e.source reference r A from ⟨hA,hball⟩)]
  rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedReciprocal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for the reciprocal operations occurring in
metric inversion and normal reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inv (j : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) x‖ =
      (j.factorial : ℝ)*‖x⁻¹‖^(j+1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have h := iteratedDerivWithin_one_div j isOpen_compl_singleton
    (show x ∈ ({0}ᶜ : Set ℝ) from hx)
  simp only [one_div] at h
  rw [h,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Real.norm_natCast,norm_zpow]
  have he : (-1-(j : ℤ)) = -((j+1 : ℕ) : ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,← inv_pow,← norm_inv]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both the input size and inverse denominator enter polynomially at each
fixed derivative order. There is no compact-range hypothesis. -/
theorem WeightedBound.inv_real {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} {f : E → ℝ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ x ∈ U, f x ≠ 0)
    (hInv : ∀ x ∈ U, ‖(f x)⁻¹‖ ≤ K) (hb : WeightedBound U s m C f) :
    WeightedBound U s m ((m.factorial : ℝ)^2*K^(m+1)*C^m) (fun x => (f x)⁻¹) := by
  have hV : UniqueDiffOn ℝ ({0}ᶜ : Set ℝ) := isOpen_compl_singleton.uniqueDiffOn
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) ({0}ᶜ) :=
    contDiffOn_id.inv (fun x hx => hx)
  have hD : 0 ≤ (m.factorial : ℝ)*K^(m+1) := by positivity
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) (f x)‖ ≤
        (m.factorial : ℝ)*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inv j (hne x hx)]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hj
    · exact (pow_le_pow_left₀ (norm_nonneg _) (hInv x hx) _).trans
        (pow_le_pow_right₀ hK (by omega))
    · positivity
    · positivity
  have hh := hb.comp hU hV hs hC hD hf hg (fun x hx => hne x hx) hd
  convert hh using 1 <;> first | rfl | ring

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedInverseSqrt
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for normalization by a positive square root. -/
noncomputable section
open Set Polynomial
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inverse_half (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) x‖ =
      ‖(descPochhammer ℝ j).eval (-1/2)‖*x^(-1/2-(j : ℝ)) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi hx,Real.iter_deriv_rpow_const]
  simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx _)]

lemma inverse_half_power_bound {x K : ℝ} (hx : 0 < x) (hK : 1 ≤ K)
    (hi : x⁻¹ ≤ K) {j m : ℕ} (hj : j ≤ m) :
    x^(-1/2-(j : ℝ)) ≤ K^(m+1) := by
  have he : x^(-1/2-(j : ℝ)) = (x⁻¹)^((j : ℝ)+1/2) := by
    rw [← Real.rpow_neg_one x,← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [he]
  have hj0 : 0 ≤ (j : ℝ)+1/2 := by positivity
  calc
    (x⁻¹)^((j : ℝ)+1/2) ≤ K^((j : ℝ)+1/2) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hx.le) hi hj0
    _ ≤ K^((m+1 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
      push_cast
      linarith)
    _ = K^(m+1) := Real.rpow_natCast _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_inverse_sqrt (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s C K : ℝ} {f : E → ℝ}, 0 < s → 1 ≤ C → 1 ≤ K →
      ContDiffOn ℝ ∞ f U → (∀ x ∈ U, 0 < f x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ K) → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ)*D*K^(m+1)*C^m)
        (fun x => (Real.sqrt (f x))⁻¹) := by
  let D : ℝ := 1+∑ j ∈ Finset.range (m+1), ‖(descPochhammer ℝ j).eval (-1/2)‖
  have hD : 1 ≤ D := by
    have hh : 0 ≤ ∑ j ∈ Finset.range (m+1), ‖(descPochhammer ℝ j).eval (-1/2)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp only [D]
    linarith
  have hDj {j : ℕ} (hj : j ≤ m) : ‖(descPochhammer ℝ j).eval (-1/2)‖ ≤ D := by
    have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m+1)) =>
      norm_nonneg ((descPochhammer ℝ i).eval (-1/2))) (Finset.mem_range.mpr (by omega : j < m+1))
    dsimp only [D]
    linarith
  refine ⟨D,hD,?_⟩
  intro U hU s C K f hs hC hK hf hpos hi hb
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) := by
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) (f x)‖ ≤ D*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inverse_half j (hpos x hx)]
    exact mul_le_mul (hDj hj) (inverse_half_power_bound (hpos x hx) hK (hi x hx) hj)
      (Real.rpow_nonneg (hpos x hx).le _) (zero_le_one.trans hD)
  have hbound := hb.comp hU isOpen_Ioi.uniqueDiffOn hs hC (by positivity : 0 ≤ D*K^(m+1))
    hf hg hpos hd
  have hbound' : WeightedBound U s m ((m.factorial : ℝ)*D*K^(m+1)*C^m)
      ((fun y : ℝ => y^(-1/2 : ℝ)) ∘ f) := by
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply hbound'.congr
  intro x hx
  simp only [Function.comp_apply,Real.sqrt_eq_rpow]
  rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg (hpos x hx).le]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedRealAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real scalar and vector products used in the quantitative normal formula. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real_dup2 {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2^m*C*D) (fun x => f x*g x) := by
  intro j hj x hx
  calc
    _ ≤ s^j*(∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*
        ‖iteratedFDerivWithin ℝ i f U x‖*‖iteratedFDerivWithin ℝ (j-i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2^j*C*D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FixedMeanSubstitution
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean correction for one fixed operator with derivative loss.
The smallness threshold is uniform in the operator; no infinite-dimensional
inverse or convergence of a derivative-losing iteration is asserted. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma rescaledMean_bounds {U : Set E} (hU : UniqueDiffOn ℝ U) {s : ℝ}
    {reference : E → F} {r η : ℝ} {L : ℕ} (hη : 0 < η)
    (A : (E → F) → E → F) (B K : ℕ → ℝ → ℝ)
    (hB : ∀ m C, 1 ≤ C → 1 ≤ B m C) (hK : ∀ m C, 1 ≤ C → 1 ≤ K m C)
    (hsm : ∀ f, ContDiffOn ℝ ∞ f U → InTrialBall U reference r f → ContDiffOn ℝ ∞ (A f) U)
    (hv : ∀ m C f, 1 ≤ C → ContDiffOn ℝ ∞ f U → InTrialBall U reference r f →
      WeightedBound U s (m + L) C f → WeightedBound U s m (η * B m C) (A f))
    (hd : ∀ m C D f g, 1 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      InTrialBall U reference r f → InTrialBall U reference r g →
      WeightedBound U s (m + L) C f → WeightedBound U s (m + L) C g →
      WeightedBound U s (m + L) D (f - g) →
      WeightedBound U s m (K m C * η * D) (A f - A g)) :
    MeanBounds U s reference r L (rescaledMean η A) B K := by
  refine ⟨hB, hK, ?_, ?_, ?_⟩
  · intro θ _ _ f hf hb
    exact (hsm f hf hb).const_smul (θ / η)
  · intro θ hθ _ m C f hC hf hb hbf
    have hh := (hv m C f hC hf hb hbf).const_smul hU (hsm f hf hb) (θ / η)
    change WeightedBound U s m _ (rescaledMean η A θ f) at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [abs_of_pos (div_pos hθ hη)]
    field_simp
  · intro θ hθ _ m C D f g hC hD hf hg hb hc hbf hbg hbd
    have hh := (hd m C D f g hC hD hf hg hb hc hbf hbg hbd).const_smul hU
      ((hsm f hf hb).sub (hsm g hg hc)) (θ / η)
    have he : (θ / η) • (A f - A g) = rescaledMean η A θ f - rescaledMean η A θ g :=
      smul_sub _ _ _
    change WeightedBound U s m _ ((θ / η) • (A f - A g)) at hh
    rw [he] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [abs_of_pos (div_pos hθ hη)]
    field_simp

end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma polynomialBound_id : HasPolynomialBound (fun x => x) := by
  exact ⟨1,1,le_rfl,fun x hx => ⟨zero_le_one.trans hx,by simp⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialRootBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit square-root and square-root-difference bounds from a reciprocal
positivity margin, without a compact-set derivative constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sqrtBudget_nonneg (m : ℕ) {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) :
    0 ≤ sqrtBudget m D B := by unfold sqrtBudget; positivity

lemma inverse_sqrt_le {x B : ℝ} (hx : 0 < x) (hB : 1 ≤ B) (hi : x⁻¹ ≤ B) :
    (Real.sqrt x)⁻¹ ≤ B := by
  have hh := inverse_half_power_bound hx hB hi (j := 0) (m := 0) (Nat.le_refl 0)
  have he : x^(-1/2 : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow,show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hx.le]
  simpa only [Nat.cast_zero,Nat.zero_add,sub_zero,pow_one,he] using hh

theorem polynomial_sqrt_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s B : ℝ} {f : E → ℝ}, 0 < s → 1 ≤ B →
      ContDiffOn ℝ ∞ f U → (∀ x ∈ U, 0 < f x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → WeightedBound U s m B f →
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (f x)) := by
  obtain ⟨D,hD,hbound⟩ := weighted_inverse_sqrt (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s B f hs hB hf hp hi hb
  have hr := hf.sqrt (fun x hx => (hp x hx).ne')
  have hi' := hr.inv (fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne')
  have hh := hb.mul_real_dup2 hU hs.le (zero_le_one.trans hB) (by positivity)
    hf hi' (hbound hU hs hB hB hf hp hi hb)
  apply hh.congr
  intro x hx
  change Real.sqrt (f x) = f x*(Real.sqrt (f x))⁻¹
  rw [← div_eq_mul_inv,eq_div_iff (Real.sqrt_pos.mpr (hp x hx)).ne']
  exact Real.mul_self_sqrt (hp x hx).le

theorem polynomial_root_bounds (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s B A : ℝ} {f g : E → ℝ}, 0 < s → 1 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      (∀ x ∈ U, 0 < f x) → (∀ x ∈ U, 0 < g x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → (∀ x ∈ U, (g x)⁻¹ ≤ B) →
      WeightedBound U s m B f → WeightedBound U s m B g →
      WeightedBound U s m A (f-g) →
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (f x)) ∧
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (g x)) ∧
      WeightedBound U s m (rootDifferenceBudget m D B*A)
        (fun x => Real.sqrt (f x)-Real.sqrt (g x)) := by
  obtain ⟨D,hD,hr⟩ := polynomial_sqrt_bound (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s B A f g hs hB hA hf hg hfp hgp hfi hgi hfb hgb hdiff
  have hrf := hf.sqrt (fun x hx => (hfp x hx).ne')
  have hrg := hg.sqrt (fun x hx => (hgp x hx).ne')
  have bF := hr hU hs hB hf hfp hfi hfb
  have bG := hr hU hs hB hg hgp hgi hgb
  have hS : 0 ≤ sqrtBudget m D B := sqrtBudget_nonneg m (zero_le_one.trans hD) (zero_le_one.trans hB)
  have hsum := bF.add hU hs.le hrf hrg bG
  have hsum' : WeightedBound U s m (1+2*sqrtBudget m D B)
      (fun x => Real.sqrt (f x)+Real.sqrt (g x)) := hsum.mono_const (by linarith)
  have hpos (x : E) (hx : x ∈ U) : 0 < Real.sqrt (f x)+Real.sqrt (g x) :=
    add_pos (Real.sqrt_pos.mpr (hfp x hx)) (Real.sqrt_pos.mpr (hgp x hx))
  have hinv (x : E) (hx : x ∈ U) :
      ‖(Real.sqrt (f x)+Real.sqrt (g x))⁻¹‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpos x hx))]
    exact ((inv_le_inv₀ (hpos x hx) (Real.sqrt_pos.mpr (hfp x hx))).mpr
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))).trans (inverse_sqrt_le (hfp x hx) hB (hfi x hx))
  have bInv := hsum'.inv_real hU hs (by linarith) hB (hrf.add hrg)
    (fun x hx => (hpos x hx).ne') hinv
  have hsmoothInv := (hrf.add hrg).inv (fun x hx => (hpos x hx).ne')
  have hh := hdiff.mul_real_dup2 hU hs.le hA (by positivity) (hf.sub hg) hsmoothInv bInv
  refine ⟨bF,bG,?_⟩
  have hh' : WeightedBound U s m (rootDifferenceBudget m D B*A)
      (fun x => (f x-g x)*(Real.sqrt (f x)+Real.sqrt (g x))⁻¹) := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    unfold rootDifferenceBudget
    ring
  apply hh'.congr
  intro x hx
  exact sqrt_difference (hfp x hx) (hgp x hx)

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAmplitudeBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the supported square-root amplitudes of the
metric decomposition, including their difference estimate. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polynomial_phaseAmplitude_bounds (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U : Set E}, UniqueDiffOn ℝ U → ∀ {s B A : ℝ} {ψ f g : E → ℝ},
      0 < s → 1 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      (∀ x ∈ U, 0 < f x) → (∀ x ∈ U, 0 < g x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → (∀ x ∈ U, (g x)⁻¹ ≤ B) →
      WeightedBound U s m B ψ → WeightedBound U s m B f → WeightedBound U s m B g →
      WeightedBound U s m A (f-g) →
      WeightedBound U s m (C*B^d) (phaseAmplitude ψ f) ∧
      WeightedBound U s m (C*B^d) (phaseAmplitude ψ g) ∧
      WeightedBound U s m (C*B^d*A) (fun x => phaseAmplitude ψ f x-phaseAmplitude ψ g x) := by
  obtain ⟨D,hD,hr⟩ := polynomial_root_bounds (E := E) m
  have hpoly : HasPolynomialBound (phaseAmplitudeBudget m D) := by
    unfold phaseAmplitudeBudget rootDifferenceBudget sqrtBudget
    repeat first
      | exact polynomialBound_id
      | apply HasPolynomialBound.add
      | apply HasPolynomialBound.mul
      | apply HasPolynomialBound.pow
      | (apply polynomialBound_const; positivity)
  obtain ⟨d,C,hC,hpoly⟩ := hpoly
  refine ⟨d,C,hC,?_⟩
  intro U hU s B A ψ f g hs hB hA hψ hf hg hfp hgp hfi hgi hbψ hbf hbg hdiff
  obtain ⟨bF,bG,bDiff⟩ := hr hU hs hB hA hf hg hfp hgp hfi hgi hbf hbg hdiff
  have hB0 := zero_le_one.trans hB
  have hS := sqrtBudget_nonneg m (zero_le_one.trans hD) hB0
  have hR : 0 ≤ rootDifferenceBudget m D B := by unfold rootDifferenceBudget; positivity
  have hleft : 2^m*B*sqrtBudget m D B ≤ phaseAmplitudeBudget m D B := by
    unfold phaseAmplitudeBudget
    have hn : 0 ≤ 2^m*B*rootDifferenceBudget m D B := by positivity
    linarith
  have hright : 2^m*B*rootDifferenceBudget m D B ≤ phaseAmplitudeBudget m D B := by
    unfold phaseAmplitudeBudget
    have hn : 0 ≤ 2^m*B*sqrtBudget m D B := by positivity
    linarith
  have hfroot := hf.sqrt (fun x hx => (hfp x hx).ne')
  have hgroot := hg.sqrt (fun x hx => (hgp x hx).ne')
  have hfa := hbψ.mul_real_dup2 hU hs.le hB0 hS hψ hfroot bF
  have hga := hbψ.mul_real_dup2 hU hs.le hB0 hS hψ hgroot bG
  refine ⟨hfa.mono_const (hleft.trans (hpoly B hB).2),
    hga.mono_const (hleft.trans (hpoly B hB).2),?_⟩
  have hda := hbψ.mul_real_dup2 hU hs.le hB0 (mul_nonneg hR hA) hψ (hfroot.sub hgroot) bDiff
  have hsize : 2^m*B*(rootDifferenceBudget m D B*A) ≤ C*B^d*A := by
    calc
      _ = (2^m*B*rootDifferenceBudget m D B)*A := by ring
      _ ≤ C*B^d*A := mul_le_mul_of_nonneg_right (hright.trans (hpoly B hB).2) hA
  apply (hda.mono_const hsize).congr
  intro x hx
  dsimp only [phaseAmplitude]
  ring

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFrameEnvelope
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single polynomial envelope for the actual reconstruction coefficients
and free normal. Its degree is chosen before any geometric bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4
open WeightedEstimates

namespace SmallModes

lemma ReconstructionCoefficientBound.mono_const {n : ℕ} {F : Field n}
    {U : Set Base} {s C D : ℝ} {m : ℕ}
    (h : ReconstructionCoefficientBound F U s m C) (hCD : C ≤ D) :
    ReconstructionCoefficientBound F U s m D :=
  ⟨⟨⟨h.xxX.mono_const hCD,h.xxY.mono_const hCD,h.xyX.mono_const hCD,
      h.xyY.mono_const hCD,h.yyX.mono_const hCD,h.yyY.mono_const hCD,
      h.ratioxx.mono_const hCD,h.ratioxy.mono_const hCD⟩,
      h.secondxx.mono_const hCD,h.secondxy.mono_const hCD⟩,
      h.dualx.mono_const hCD,h.dualy.mono_const hCD,h.dualn.mono_const hCD⟩

end SmallModes

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLocalAmplitude
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial square-root amplitudes for the actual local metric data. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

lemma coefficientBudget_polynomial (m : ℕ) : HasPolynomialBound (coefficientBudget m) := by
  unfold coefficientBudget
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

lemma inputFactor_le_coefficientBudget (d : Budgets U V s F ψ Q χ e)
    (m : ℕ) {B : ℝ} (hB : 1 ≤ B) (hi : d.inv m ≤ B) (hf : d.forms m ≤ B) :
    inputFactor d m ≤ coefficientBudget m B := by
  have hI := d.inv_pos m
  have hF := d.forms_pos m
  unfold inputFactor coefficientBudget
  gcongr

theorem polynomial_local_amplitude_bounds (m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
      {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base},
      ∀ (_h : LocalBounds U V s r ρ R reference F ψ Q χ e)
        (d : Budgets U V s F ψ Q χ e),
      0 < s → s ≤ 1 → 0 < ρ → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.inv m ≤ B → d.forms m ≤ B → d.psi m ≤ B →
    ∀ (A A' : Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ A' U →
      InTrialBall U reference r A → InTrialBall U reference r A' →
      WeightedBound U s m B A → WeightedBound U s m B A' →
      WeightedBound U s m D (A-A') →
      WeightedBound V s m (C*B^p) (phaseAmplitude ψ (coefficient Q e A)) ∧
      WeightedBound V s m (C*B^p) (phaseAmplitude ψ (coefficient Q e A')) ∧
      WeightedBound V s m (C*B^p*D)
        (fun x => phaseAmplitude ψ (coefficient Q e A) x-phaseAmplitude ψ (coefficient Q e A') x) := by
  obtain ⟨k,C₀,hC₀,hamp⟩ := polynomial_phaseAmplitude_bounds (E := Base) m
  let S := fun B : ℝ => 1+B+coefficientBudget m B*B
  have hSp : HasPolynomialBound S :=
    ((polynomialBound_const zero_le_one).add polynomialBound_id).add
      ((coefficientBudget_polynomial m).mul polynomialBound_id)
  have hpoly : HasPolynomialBound (fun B => C₀*(S B)^k*(1+coefficientBudget m B)) :=
    ((polynomialBound_const (zero_le_one.trans hC₀)).mul (hSp.pow k)).mul
      ((polynomialBound_const zero_le_one).add (coefficientBudget_polynomial m))
  obtain ⟨p,C,hC,hpoly⟩ := hpoly
  refine ⟨p,C,hC,?_⟩
  intro U V s r ρ R reference F ψ Q χ e h d hs hs1 hρ B hB hρB hi hf hψ A A' D hD hA hA' hball hball' hbA hbA' hbD
  have hB0 := zero_le_one.trans hB
  have hJ : 0 ≤ coefficientBudget m B := by unfold coefficientBudget; positivity
  have hS : 1 ≤ S B ∧ B ≤ S B ∧ coefficientBudget m B*B ≤ S B := by
    dsimp [S]
    have hh : 0 ≤ coefficientBudget m B*B := mul_nonneg hJ hB0
    constructor
    · linarith
    constructor <;> linarith
  have hfactor := inputFactor_le_coefficientBudget d m hB hi hf
  have hcoeff (T : Base → Tensor) (hT : ContDiffOn ℝ ∞ T U)
      (hbT : WeightedBound U s m B T) : WeightedBound V s m (S B) (coefficient Q e T) := by
    have hh := weighted_coefficient h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
      (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hB0 h.smoothQ h.smoothInv
      h.invInto hT (d.inv_bound m) (d.forms_bound m) hbT
    exact hh.mono_const ((mul_le_mul_of_nonneg_right hfactor hB0).trans hS.2.2)
  have hdiff := weighted_coefficient_difference h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
    (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hD h.smoothQ h.smoothInv
    h.invInto hA hA' (d.inv_bound m) (d.forms_bound m) hbD
  have hdiff' : WeightedBound V s m (coefficientBudget m B*D)
      ((coefficient Q e A)-(coefficient Q e A')) :=
    hdiff.mono_const (mul_le_mul_of_nonneg_right hfactor hD)
  have hpos (T : Base → Tensor) (ht : InTrialBall U reference r T) :
      ∀ x ∈ V, 0 < coefficient Q e T x :=
    fun x hx => hρ.trans_le (coefficient_trial_range h.invInto h.margin ht hx).1
  have hinv (T : Base → Tensor) (ht : InTrialBall U reference r T) :
      ∀ x ∈ V, (coefficient Q e T x)⁻¹ ≤ S B := by
    intro x hx
    exact ((inv_le_inv₀ (hpos T ht x hx) hρ).mpr
      (coefficient_trial_range h.invInto h.margin ht hx).1).trans (hρB.trans hS.2.1)
  obtain ⟨ha,ha',hd⟩ := hamp h.domain.isOpen.uniqueDiffOn hs hS.1 (mul_nonneg hJ hD)
    h.smoothPsi (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA)
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA')
    (hpos A hball) (hpos A' hball') (hinv A hball) (hinv A' hball')
    ((d.psi_bound m).mono_const (hψ.trans hS.2.1)) (hcoeff A hA hbA) (hcoeff A' hA' hbA') hdiff'
  have hsize := (hpoly B hB).2
  have hbase : C₀*(S B)^k ≤ C*B^p := by
    calc
      _ ≤ C₀*(S B)^k*(1+coefficientBudget m B) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ _ := hsize
  have hdiffsize : C₀*(S B)^k*(coefficientBudget m B*D) ≤ C*B^p*D := by
    calc
      _ ≤ (C₀*(S B)^k*(1+coefficientBudget m B))*D := by
        have hz : 0 ≤ C₀*(S B)^k := by positivity
        nlinarith [mul_nonneg hz hD]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsize hD
  exact ⟨ha.mono_const hbase,ha'.mono_const hbase,hd.mono_const hdiffsize⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialModeBudgets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite free and forced parametrices have polynomial budgets. These
are the actual constants used by the existing mode estimates. -/
noncomputable section
namespace ClosedSurfaceR4.SmallModes
open RealModes

theorem fullErrorConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (fullErrorConstant n m) := by
  unfold fullErrorConstant reducedConstant targetConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem amplitudeConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (amplitudeConstant n m) := by
  unfold amplitudeConstant targetConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem initialConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (initialConstant n m) := by
  unfold initialConstant
  exact ((polynomialBound_const (by positivity)).add
    ((polynomialBound_const (by positivity)).mul polynomialBound_id)).add
      (amplitudeConstant_polynomial n m)

theorem freeModeConstant_polynomial (n m q : ℕ) :
    HasPolynomialBound (fun x => freeModeConstant n m x q) := by
  induction q with
  | zero => exact amplitudeConstant_polynomial n m
  | succ q ih =>
    exact ih.add ((initialConstant_polynomial n m).mul
      ((fullErrorConstant_polynomial n (m+1+q)).pow (q+1)))

theorem gradientErrorConstant_polynomial (n m q : ℕ) :
    HasPolynomialBound (fun x => gradientErrorConstant n m x q) :=
  ((polynomialBound_const zero_le_one).add (freeModeConstant_polynomial n (m+1) q)).add
    (freeModeConstant_polynomial n m q)

theorem meanErrorConstant_polynomial (n m q : ℕ) :
    HasPolynomialBound (fun x => meanErrorConstant n m x q) := by
  unfold meanErrorConstant
  exact (((polynomialBound_const (Nat.cast_nonneg n)).mul
    (polynomialBound_const (by positivity))).mul
      (gradientErrorConstant_polynomial n m q)).mul
        ((polynomialBound_const (by positivity)).add (gradientErrorConstant_polynomial n m q))

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLocalMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative mean estimates for the actual local construction. The
power depends on the fixed derivative and accuracy orders only. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

lemma outputFactor_le_coefficientBudget (d : Budgets U V s F ψ Q χ e)
    (m : ℕ) {B : ℝ} (hB : 1 ≤ B) (hc : d.chi m ≤ B) (hp : d.pull m ≤ B) :
    outputFactor d m ≤ coefficientBudget m B := by
  have hχ := d.chi_pos m
  have hP := d.pull_pos m
  unfold outputFactor coefficientBudget
  gcongr

theorem polynomial_local_mean_estimates (q m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
      {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base},
      ∀ (_h : LocalBounds U V s r ρ R reference F ψ Q χ e)
        (d : Budgets U V s F ψ Q χ e),
      0 < s → s ≤ 1 → 0 < ρ → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.inv (m+q+2) ≤ B → d.forms (m+q+2) ≤ B → d.psi (m+q+2) ≤ B →
      d.mode (m+q+2) ≤ B → d.normal (m+q+2) ≤ B → d.chi m ≤ B → d.pull m ≤ B →
    ∀ δ η : ℝ, 0 < δ → 0 < η → η ≤ 1 →
    ∀ (A A' : Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ A' U →
      InTrialBall U reference r A → InTrialBall U reference r A' →
      WeightedBound U s (m+q+2) B A → WeightedBound U s (m+q+2) B A' →
      WeightedBound U s (m+q+2) D (A-A') →
      WeightedBound U s m (η*(C*B^p)) (meanTerm δ s F ψ Q χ e q η A) ∧
      WeightedBound U s m ((C*B^p)*η*D)
        (meanTerm δ s F ψ Q χ e q η A-meanTerm δ s F ψ Q χ e q η A') := by
  obtain ⟨a,C₀,hC₀,hamp⟩ := polynomial_local_amplitude_bounds (m+q+2)
  let Z := fun B : ℝ => meanErrorConstant 4 m B q *
    (Real.sqrt 2 * 2^(m+q+2)*B)^2*(C₀*B^a)^2
  have hZ : HasPolynomialBound Z :=
    ((meanErrorConstant_polynomial 4 m q).mul
      ((((polynomialBound_const (by positivity)).mul (polynomialBound_const (by positivity))).mul
        polynomialBound_id).pow 2)).mul
      (((polynomialBound_const (zero_le_one.trans hC₀)).mul (polynomialBound_id.pow a)).pow 2)
  obtain ⟨p,C,hC,hpoly⟩ := (polynomialBound_const zero_le_one).add
    (((polynomialBound_const (show (0:ℝ) ≤ 2 by norm_num)).mul (coefficientBudget_polynomial m)).mul hZ)
  refine ⟨p,C,hC,?_⟩
  intro U V s r ρ R reference F ψ Q χ e h d hs hs1 hρ B hB hρB hi hf hψ hm hn hχ hp δ η hδ hη hη1 A A' D hD hA hA' hball hball' hbA hbA' hbD
  obtain ⟨ha,ha',had⟩ := hamp h d hs hs1 hρ B hB hρB hi hf hψ A A' D hD hA hA' hball hball' hbA hbA' hbD
  have hB0 := zero_le_one.trans hB
  have hAB : 0 ≤ C₀*B^a := by positivity
  have hsa := h.amplitude_smooth hρ hA hball
  have hsb := h.amplitude_smooth hρ hA' hball'
  have hτs : η*s ≤ s := mul_le_of_le_one_left hs.le hη1
  have hcancel : η*s/s = η := mul_div_cancel_right₀ _ hs.ne'
  have hcoeff := (d.mode_bound (m+q+2)).mono_const hm
  have hnormal := (d.normal_bound (m+q+2)).mono_const hn
  have hval := weighted_meanTensor h.smoothF h.domain hsa hδ (mul_pos hη hs) hs hτs hs1
    hB0 hAB hB0 q m hcoeff ha hnormal
  have hval' : WeightedBound V s m (Z B*η)
      (meanTensor δ (η*s) F (phaseAmplitude ψ (coefficient Q e A)) q) := by
    convert hval using 1
    all_goals try with_reducible_and_instances rfl
    rw [hcancel]
    dsimp [Z]
    ring
  have hz : 0 ≤ Z B := by
    have hh := meanErrorConstant_nonneg 4 m q hB0
    dsimp [Z]
    positivity
  have hv := h.transport_bound d hs hs1 (mul_nonneg hz hη.le)
    (contDiffOn_meanTensor h.smoothF h.domain hsa δ (η*s) q) hval'
  have hdiff := weighted_meanTensor_difference h.smoothF h.domain hsa hsb hδ
    (mul_pos hη hs) hs hτs hs1 hB0 hAB (mul_nonneg hAB hD) hB0 q m hcoeff ha ha' had hnormal
  have hdiff' : WeightedBound V s m (2*Z B*D*η)
      (fun x => meanTensor δ (η*s) F (phaseAmplitude ψ (coefficient Q e A)) q x-
        meanTensor δ (η*s) F (phaseAmplitude ψ (coefficient Q e A')) q x) := by
    convert hdiff using 1
    all_goals try with_reducible_and_instances rfl
    rw [hcancel]
    dsimp [Z]
    ring
  have hd := h.transport_bound d hs hs1 (by positivity)
    ((contDiffOn_meanTensor h.smoothF h.domain hsa δ (η*s) q).sub
      (contDiffOn_meanTensor h.smoothF h.domain hsb δ (η*s) q)) hdiff'
  have hout := outputFactor_le_coefficientBudget d m hB hχ hp
  have hbudget : 1+2*coefficientBudget m B*Z B ≤ C*B^p := (hpoly B hB).2
  have hb0 : 0 ≤ coefficientBudget m B := by unfold coefficientBudget; positivity
  have hvalue : outputFactor d m*Z B ≤ C*B^p :=
    (mul_le_mul_of_nonneg_right hout hz).trans (by nlinarith [mul_nonneg hb0 hz])
  have hdifference : 2*outputFactor d m*Z B ≤ C*B^p := by
    have hh := mul_le_mul_of_nonneg_right hout (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hz)
    nlinarith
  constructor
  · apply hv.mono_const
    calc
      _ = η*(outputFactor d m*Z B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvalue hη.le
  · apply (hd.mono_const (show outputFactor d m*(2*Z B*D*η) ≤ C*B^p*η*D from by
      calc
        _ = (2*outputFactor d m*Z B)*(η*D) := by ring
        _ ≤ _ := by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hdifference (mul_nonneg hη.le hD))).congr
    intro x hx
    exact (map_sub (pullbackField χ x) _ _).symm

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLocalMeanProfile
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local mean operator has explicit polynomial majorants in the
geometric profile and the current tensor norm. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

theorem polynomial_local_mean_majorants (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
      {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base},
      ∀ (_h : LocalBounds U V s r ρ R reference F ψ Q χ e)
        (d : Budgets U V s F ψ Q χ e),
      0 < s → s ≤ 1 → 0 < ρ → ∀ G : ℕ → ℝ, (∀ m, 1 ≤ G m) →
      (∀ m, ρ⁻¹ ≤ G m ∧ d.inv (m+q+2) ≤ G m ∧ d.forms (m+q+2) ≤ G m ∧
        d.psi (m+q+2) ≤ G m ∧ d.mode (m+q+2) ≤ G m ∧ d.normal (m+q+2) ≤ G m ∧
        d.chi m ≤ G m ∧ d.pull m ≤ G m) →
      ∀ δ : ℝ, 0 < δ → MeanBounds U s reference r (q+2)
        (meanTerm δ s F ψ Q χ e q) (polynomialMeanProfile p C G) (polynomialMeanProfile p C G) := by
  classical
  choose p C hC hmean using fun m => polynomial_local_mean_estimates q m
  refine ⟨p,C,hC,?_⟩
  intro U V s r ρ R reference F ψ Q χ e h d hs hs1 hρ G hG hbounds δ hδ
  have hmajor (m : ℕ) (A : ℝ) (_hA : 1 ≤ A) : 1 ≤ polynomialMeanProfile p C G m A := by
    apply one_le_mul_of_one_le_of_one_le (hC m)
    apply one_le_pow₀
    exact (hG m).trans (le_add_of_nonneg_right ((zero_le_one.trans (le_max_left 1 A))))
  have happly (m : ℕ) (A : ℝ) (hA : 1 ≤ A) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
      (f g : Base → Tensor) (D : ℝ) (hD : 0 ≤ D)
      (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
      (hfball : InTrialBall U reference r f) (hgball : InTrialBall U reference r g)
      (hfb : WeightedBound U s (m+(q+2)) A f) (hgb : WeightedBound U s (m+(q+2)) A g)
      (hdb : WeightedBound U s (m+(q+2)) D (f-g)) := by
    let B := G m+max 1 A
    have hBG : G m ≤ B := le_add_of_nonneg_right (zero_le_one.trans (le_max_left 1 A))
    have hBA : A ≤ B := (le_max_right 1 A).trans
      (le_add_of_nonneg_left (zero_le_one.trans (hG m)))
    have hB : 1 ≤ B := (hG m).trans hBG
    obtain ⟨hρG,hi,hforms,hψ,hmode,hnormal,hχ,hpull⟩ := hbounds m
    have horders : m+(q+2) = m+q+2 := by omega
    rw [horders] at hfb hgb hdb
    exact hmean m h d hs hs1 hρ B hB (hρG.trans hBG) (hi.trans hBG) (hforms.trans hBG)
      (hψ.trans hBG) (hmode.trans hBG) (hnormal.trans hBG) (hχ.trans hBG) (hpull.trans hBG)
      δ η hδ hη hη1 f g D hD hf hg hfball hgball (hfb.mono_const hBA) (hgb.mono_const hBA) hdb
  refine ⟨hmajor,hmajor,?_,?_,?_⟩
  · intro η hη hη1 f hf hfball
    exact h.mean_smooth hρ hf hfball δ q η
  · intro η hη hη1 m A f hA hf hfball hb
    have hz : WeightedBound U s (m+(q+2)) 0 (f-f) := by
      apply (weightedBound_zero U s (m+(q+2)) (F := Tensor)).congr
      intro x hx
      simp
    exact (happly m A hA η hη hη1 f f 0 le_rfl hf hf hfball hfball hb hb hz).1
  · intro η hη hη1 m A D f g hA hD hf hg hfball hgball hfb hgb hdb
    exact (happly m A hA η hη hη1 f g D hD hf hg hfball hgball hfb hgb hdb).2

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UnperturbedFreeModeIdentity
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unperturbed supported solver is exactly the explicit finite
metric-mode parametrix, including its quadratic mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial
variable {n : ℕ} {G : Field n} {U : Set Base}

lemma perturbedFreeMode_zero (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (V : SupportedField (F := Ambient n) K) (q : ℕ) :
    (perturbedFreeMode τ hG h K hKU 0 V q : Field n) = modeApprox τ G V (fun _ => 0) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have he : (fun p => conjugatedD τ G
        (perturbedFreeMode τ hG h K hKU 0 V q) p) =
        residual τ G (fun _ => 0) (modeApprox τ G V (fun _ => 0) q) := by
      rw [ih]
      funext p
      simp only [residual, sub_zero]
    funext p
    change (perturbedFreeMode τ hG h K hKU 0 V q) p -
      initialAmplitude τ G (fun _ => 0)
        (fun y => conjugatedD τ G (perturbedFreeMode τ hG h K hKU 0 V q) y + 0 - 0) p = _
    simp only [add_zero, sub_zero, he]
    rw [show (perturbedFreeMode τ hG h K hKU 0 V q) p =
      modeApprox τ G V (fun _ => 0) q p from congrFun ih p]
    rfl

lemma perturbedFreeLM_zero (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (V : SupportedField (F := Ambient n) K) (q : ℕ) :
    (perturbedFreeLM τ hG h K hKU 0 q V : Field n) = modeApprox τ G V (fun _ => 0) q := by
  rw [perturbedFreeLM_apply]
  exact perturbedFreeMode_zero τ hG h K hKU V q

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.RealModes
open SmallModes
open JetPolynomial (SupportedField)
variable {F : RField 4} {U : Set Base}

lemma normalizedPerturbedMean_zero (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (q : ℕ) (b : SupportedField (F := ℝ) K) (v w p : Base) :
    normalizedPerturbedMean δ τ hF h K hKU 0 q b v w p =
      normalizedMeanError δ τ F b q v w p := by
  have he := perturbedFreeLM_zero τ (contDiff_complexify hF) (h.complexDomain hF)
    K hKU (supportedFreeSeed δ τ hF h K hKU b) q
  change δ⁻¹ ^ 2 *
    (QuadraticMean.zeroPair
      (gradientAmplitude τ (perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF)
        K hKU 0 q (supportedFreeSeed δ τ hF h K hKU b)) v p)
      (gradientAmplitude τ (perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF)
        K hKU 0 q (supportedFreeSeed δ τ hF h K hKU b)) w p) -
      QuadraticMean.zeroPair (leadingDerivative τ (freeSeed δ τ b F) v p)
        (leadingDerivative τ (freeSeed δ τ b F) w p)) = _
  rw [he]
  simp only [normalizedMeanError, modeMeanError, inv_pow]
  rfl

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P 0 G hG φ K τ s)

lemma operator_unperturbed : c.operator = 0 :=
  phaseChartPolynomialOperator_zero c.openO c.openU P c.smoothP hG c.mapsG K c.supportU
    c.smoothPhase τ c.e c.smoothForward c.smoothInverse c.supportChart

lemma metricMeanInChart_unperturbed (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) :
    c.metricMeanInChart δ q b = meanTensor δ τ c.realMap b q := by
  funext y k
  unfold metricMeanInChart
  rw [c.operator_unperturbed]
  exact normalizedPerturbedMean_zero δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) q b (firstDirection k) (secondDirection k) y

lemma combinedMeanField_unperturbed (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    c.combinedMeanField δ q b x = c.e.source.indicator
      (fun p => pullbackField c.e p (meanTensor δ τ c.realMap b q (c.e p))) x := by
  have hz : c.polynomialMeanField δ q b = 0 := by
    ext y k
    change normalizedPolynomialMean (P k) δ 0 G φ (c.originalFreeSeed δ q b) τ 0 y = 0
    simp [normalizedPolynomialMean, quadraticMeanCoefficient, conjugated]
  change c.metricMeanField δ q b x + (pushSupported planeCoordinateIsometry K (c.polynomialMeanField δ q b)) x = _
  rw [hz]
  change c.metricMeanField δ q b x + (0 : Tensor) = _
  rw [add_zero, metricMeanField_apply, c.metricMeanInChart_unperturbed]

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialChartedMetricMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual charted metric mean, with no
polynomial differential perturbation. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    {c : PolynomialSolveData P 0 G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

lemma mean_unperturbed (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (hs : 0 < (s : ℝ)) (δ : ℝ) (q : ℕ) {f : SmallModes.Base → Tensor}
    (hf : ContDiffOn ℝ ∞ f c.e.source) (hball : InTrialBall c.e.source reference r f) :
    d.mean hρ δ q f = c.e.source.indicator
      (meanTerm δ s c.realMap d.cutoff d.form c.e c.e.symm q (τ/s) f) := by
  have hamp : (d.amplitude hρ f : SmallModes.Base → ℝ) =
      phaseAmplitude d.cutoff (coefficient d.form c.e.symm f) :=
    funext (c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hf hball)
  funext x
  rw [mean, c.combinedMeanField_unperturbed]
  simp only [hamp]
  apply congrArg (fun a : SmallModes.Base → Tensor => c.e.source.indicator a x)
  funext y
  simp only [meanTerm, div_mul_cancel₀ τ hs.ne']

end ChartedMeanData

/-- The exponent and coefficient are uniform over the actual solver data;
only its explicitly supplied geometric profile varies. -/
theorem polynomial_charted_metric_mean (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P 0 G hG φ K τ s)
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ J : ℕ → ℝ, (∀ m, 1 ≤ J m) →
      (∀ m, ρ⁻¹ ≤ J m ∧ d.budgets.inv (m+q+2) ≤ J m ∧
        d.budgets.forms (m+q+2) ≤ J m ∧ d.budgets.psi (m+q+2) ≤ J m ∧
        d.budgets.mode (m+q+2) ≤ J m ∧ d.budgets.normal (m+q+2) ≤ J m ∧
        d.budgets.chi m ≤ J m ∧ d.budgets.pull m ≤ J m) →
      ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s reference r (q+2) (rescaledMean (τ/s) (d.mean hρ δ q))
        (polynomialMeanProfile p C J) (polynomialMeanProfile p C J) := by
  obtain ⟨p,C,hC,hm⟩ := polynomial_local_mean_majorants q
  refine ⟨p,C,hC,?_⟩
  intro n P τ G hG φ K s c r ρ R reference d hρ hτ hs hτs hs1 J hJ hbounds δ hδ
  have hη : 0 < τ/(s : ℝ) := div_pos hτ hs
  have hη1 : τ/(s : ℝ) ≤ 1 := (div_le_one₀ hs).mpr hτs
  have hl := hm d.localBounds d.budgets hs hs1 hρ J hJ hbounds δ hδ
  apply rescaledMean_bounds uniqueDiffOn_univ hη _ _ _ hl.B_pos hl.K_pos
  · intro f _ _
    exact (c.combinedMeanField δ q (d.amplitude hρ f)).contDiff.contDiffOn
  · intro m A f hA hf hball hbf
    have hfs := hf.mono (subset_univ c.e.source)
    have hb := fun x (_hx : x ∈ c.e.source) => hball x (mem_univ x)
    have hv := hl.value _ hη hη1 m A f hA hfs hb (hbf.restrict_open c.e.open_source)
    have heq := d.mean_unperturbed hρ hs δ q hfs hb
    have hv' : WeightedBound c.e.source s m ((τ/s)*polynomialMeanProfile p C J m A)
        (d.mean hρ δ q f) := by
      rw [heq]
      exact hv.congr (fun x hx => indicator_of_mem hx _)
    apply hv'.extend_support c.e.open_source
      ((c.combinedMeanField δ q (d.amplitude hρ f)).tsupport_subset.trans c.supportChart)
    exact mul_nonneg hη.le (zero_le_one.trans (hl.B_pos m A hA))
  · intro m A D f g hA hD hf hg hballf hballg hbf hbg hbd
    have hfs := hf.mono (subset_univ c.e.source)
    have hgs := hg.mono (subset_univ c.e.source)
    have hballf' := fun x (_hx : x ∈ c.e.source) => hballf x (mem_univ x)
    have hballg' := fun x (_hx : x ∈ c.e.source) => hballg x (mem_univ x)
    have hv := hl.difference _ hη hη1 m A D f g hA hD hfs hgs hballf' hballg'
      (hbf.restrict_open c.e.open_source) (hbg.restrict_open c.e.open_source)
      (hbd.restrict_open c.e.open_source)
    have heqf := d.mean_unperturbed hρ hs δ q hfs hballf'
    have heqg := d.mean_unperturbed hρ hs δ q hgs hballg'
    have hv' : WeightedBound c.e.source s m (polynomialMeanProfile p C J m A*(τ/s)*D)
        (d.mean hρ δ q f-d.mean hρ δ q g) := by
      rw [heqf, heqg]
      exact hv.congr (fun x hx => by simp only [Pi.sub_apply, indicator_of_mem hx])
    have hsupport : tsupport (d.mean hρ δ q f-d.mean hρ δ q g) ⊆ c.e.source :=
      (tsupport_sub _ _).trans (union_subset
        ((c.combinedMeanField δ q (d.amplitude hρ f)).tsupport_subset.trans c.supportChart)
        ((c.combinedMeanField δ q (d.amplitude hρ g)).tsupport_subset.trans c.supportChart))
    exact hv'.extend_support c.e.open_source hsupport
      (mul_nonneg (mul_nonneg (zero_le_one.trans (hl.K_pos m A hA)) hη.le) hD)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteMeanFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite local mean families retain polynomial majorants even when the
number of summands grows. The degree depends on the local estimate, not
on the number of charts. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma MeanBounds.mono_majorants {U : Set E} {s r : ℝ} {reference : E → F}
    {L : ℕ} {T : ℝ → (E → F) → E → F} {B K B' K' : ℕ → ℝ → ℝ}
    (h : MeanBounds U s reference r L T B K)
    (hB : ∀ m C, 1 ≤ C → B m C ≤ B' m C)
    (hK : ∀ m C, 1 ≤ C → K m C ≤ K' m C) :
    MeanBounds U s reference r L T B' K' := by
  refine ⟨fun m C hC => (h.B_pos m C hC).trans (hB m C hC),
    fun m C hC => (h.K_pos m C hC).trans (hK m C hC), h.smooth, ?_, ?_⟩
  · intro η hη hη1 m C f hC hf hb hnorm
    exact (h.value η hη hη1 m C f hC hf hb hnorm).mono_const
      (mul_le_mul_of_nonneg_left (hB m C hC) hη.le)
  · intro η hη hη1 m C D f g hC hD hf hg hbf hbg hnf hng hnd
    exact (h.difference η hη hη1 m C D f g hC hD hf hg hbf hbg hnf hng hnd).mono_const
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hK m C hC) hη.le) hD)

end ClosedSurfaceR4.FiniteMean

namespace ClosedSurfaceR4.PhaseMean
open WeightedEstimates FiniteMean
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma polynomialMeanProfile_sum_bound {ι : Type*} (a : Finset ι)
    (p : ℕ → ℕ) (C G : ℕ → ℝ) (m : ℕ) (A : ℝ)
    (hC : 0 ≤ C m) (hG : 1 ≤ G m) (ha : (a.card : ℝ) ≤ G m) :
    1 + ∑ _i ∈ a, polynomialMeanProfile p C G m A ≤
      polynomialMeanProfile (fun m => p m+1) (fun m => 1+C m) G m A := by
  classical
  let u := G m+max 1 A
  have hu : 1 ≤ u := hG.trans
    (le_add_of_nonneg_right (zero_le_one.trans (le_max_left 1 A)))
  have hau : (a.card : ℝ) ≤ u := ha.trans
    (le_add_of_nonneg_right (zero_le_one.trans (le_max_left 1 A)))
  have hp : 0 ≤ C m*u^(p m) := mul_nonneg hC (pow_nonneg (zero_le_one.trans hu) _)
  have hone : 1 ≤ u^(p m+1) := one_le_pow₀ hu
  simp only [polynomialMeanProfile, Finset.sum_const, nsmul_eq_mul]
  change 1+(a.card : ℝ)*(C m*u^(p m)) ≤ (1+C m)*u^(p m+1)
  calc
    _ ≤ 1+u*(C m*u^(p m)) := by linarith [mul_le_mul_of_nonneg_right hau hp]
    _ = 1+C m*u^(p m+1) := by rw [pow_succ]; ring
    _ ≤ u^(p m+1)+C m*u^(p m+1) := by linarith
    _ = _ := by ring

/-- A growing finite number of local terms costs one additional polynomial
power when its cardinality is included in the geometric profile. -/
theorem polynomial_finite_mean_family {ι : Type*} {U : Set E}
    (hU : UniqueDiffOn ℝ U) {s : ℝ} (hs : 0 ≤ s)
    {reference : E → F} {r : ℝ} {L : ℕ} (a : Finset ι)
    (T : ι → ℝ → (E → F) → E → F) (p : ℕ → ℕ) (C G : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (hG : ∀ m, 1 ≤ G m)
    (ha : ∀ m, (a.card : ℝ) ≤ G m)
    (hT : ∀ i ∈ a, MeanBounds U s reference r L (T i)
      (polynomialMeanProfile p C G) (polynomialMeanProfile p C G)) :
    MeanBounds U s reference r L (fun η f x => ∑ i ∈ a, T i η f x)
      (polynomialMeanProfile (fun m => p m+1) (fun m => 1+C m) G)
      (polynomialMeanProfile (fun m => p m+1) (fun m => 1+C m) G) := by
  apply (MeanBounds.finset_sum hU hs a T (fun _ => polynomialMeanProfile p C G)
    (fun _ => polynomialMeanProfile p C G) hT).mono_majorants
  · intro m A _
    exact polynomialMeanProfile_sum_bound a p C G m A (hC m) (hG m) (ha m)
  · intro m A _
    exact polynomialMeanProfile_sum_bound a p C G m A (hC m) (hG m) (ha m)

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialChartedMeanFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial estimates for arbitrary finite families of the actual
charted metric means. The cardinality enters the geometric profile. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

theorem polynomial_charted_metric_mean_family_oai (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {ι : Type*} [Fintype ι] {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
      {K : ι → Compacts Base} {s : ℝ≥0}
      (c : ∀ i, PolynomialSolveData P 0 G hG (φ i) (K i) τ s)
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ J : ℕ → ℝ, (∀ m, 1 ≤ J m) → (∀ m, (Fintype.card ι : ℝ) ≤ J m) →
      (∀ i m, ρ⁻¹ ≤ J m ∧ (d i).budgets.inv (m+q+2) ≤ J m ∧
        (d i).budgets.forms (m+q+2) ≤ J m ∧ (d i).budgets.psi (m+q+2) ≤ J m ∧
        (d i).budgets.mode (m+q+2) ≤ J m ∧ (d i).budgets.normal (m+q+2) ≤ J m ∧
        (d i).budgets.chi m ≤ J m ∧ (d i).budgets.pull m ≤ J m) →
      ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s reference r (q+2)
        (rescaledMean (τ/s) (chartedFamilyMean d hρ δ q))
        (polynomialMeanProfile p C J) (polynomialMeanProfile p C J) := by
  classical
  obtain ⟨p,C,hC,hm⟩ := polynomial_charted_metric_mean q
  refine ⟨fun m => p m+1,fun m => 1+C m,fun m => by linarith [hC m],?_⟩
  intro ι _ n P τ G hG φ K s c r ρ R reference d hρ hτ hs hτs hs1 J hJ hcard hb δ hδ
  have hlocal (i : ι) := hm (c i) (d i) hρ hτ hs hτs hs1 J hJ (hb i) δ hδ
  have hfamily := polynomial_finite_mean_family uniqueDiffOn_univ hs.le
    (reference := reference) (r := r) (L := q+2) (Finset.univ : Finset ι)
    (fun i => rescaledMean (τ/s) ((d i).mean hρ δ q)) p C J
    (fun m => zero_le_one.trans (hC m)) hJ (by simpa using hcard)
    (fun i _ => hlocal i)
  have he : rescaledMean (τ/s) (chartedFamilyMean d hρ δ q) =
      (fun θ f x => ∑ i ∈ (Finset.univ : Finset ι),
        rescaledMean (τ/s) ((d i).mean hρ δ q) θ f x) := by
    funext θ f x k
    simp [rescaledMean, chartedFamilyMean, Finset.mul_sum]
  rw [he]
  exact hfamily

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family_oai.{u_1} := @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family_oai.{u_1}
