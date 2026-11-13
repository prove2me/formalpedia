-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.originalFreeSeed_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:48:54.638117+00:00
-- url     : https://prove2.me/submissions/b64dfce7-5a06-467c-b4d5-b9eea639d173

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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

lemma weighted_reducedK_zero {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 ≤ s) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : ModeCoefficientBound G U s m K) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) :
    WeightedBound U s m ((1 + 2 ^ m * K) * C)
      (reducedKx G (fun _ => 0) (component f 0) (component f 2)) ∧
    WeightedBound U s m ((1 + 2 ^ m * K) * C)
      (reducedKy G (fun _ => 0) (component f 1) (component f 2)) := by
  have hsm (i : Fin 3) : ContDiffOn ℝ ∞ (component f i) U := contDiffOn_pi.mp hf i
  have hcomp (i : Fin 3) := hb.component h.isOpen.uniqueDiffOn hs hC hf i
  have hmulx := hc.ratioxx.mul h.isOpen.uniqueDiffOn hs hK hC (h.secondRatio dx dx)
    (hsm 2) (hcomp 2)
  have hmuly := hc.ratioxy.mul h.isOpen.uniqueDiffOn hs hK hC (h.secondRatio dx dy)
    (hsm 2) (hcomp 2)
  have hsubx := (hcomp 0).sub h.isOpen.uniqueDiffOn hs (hsm 0)
    ((h.secondRatio dx dx).mul (hsm 2)) hmulx
  have hsuby := (hcomp 1).sub h.isOpen.uniqueDiffOn hs (hsm 1)
    ((h.secondRatio dx dy).mul (hsm 2)) hmuly
  constructor
  · have hhalf := hsubx.const_mul h.isOpen.uniqueDiffOn
      ((hsm 0).sub ((h.secondRatio dx dx).mul (hsm 2))) (1 / 2)
    have hbound : WeightedBound U s m ((C + 2 ^ m * K * C) / 2)
        (reducedKx G (fun _ => 0) (component f 0) (component f 2)) := by
      convert hhalf using 1
      · norm_num
        ring
      · funext p
        simp only [reducedKx, component, dotProduct_zero, add_zero]
        ring
    apply hbound.mono_const
    nlinarith [show 0 ≤ 2 ^ m * K * C by positivity]
  · convert hsuby using 1
    · ring
    · funext p
      simp [reducedKy, component]


lemma errorConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ errorConstant m K := by
  unfold errorConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK)) (by positivity)

lemma weighted_errorGenerator_zero {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : ModeCoefficientBound G U s (m + 1) K)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (errorConstant m K * C / s) (errorGenerator G (fun _ => 0) f) := by
  have hsm (i : Fin 3) : ContDiffOn ℝ ∞ (component f i) U := contDiffOn_pi.mp hf i
  have hxb := (weighted_reducedK_zero h hs.le hK hC hc hf hb).1
  have hyb := (weighted_reducedK_zero h hs.le hK hC hc hf hb).2
  have hxsm := contDiffOn_reducedKx h (V := fun _ => 0) contDiffOn_const (hsm 0) (hsm 2)
  have hysm := contDiffOn_reducedKy h (V := fun _ => 0) contDiffOn_const (hsm 1) (hsm 2)
  have hc0 : 0 ≤ (1 + 2 ^ (m + 1) * K) * C := by positivity
  have hxx := weighted_reducedLx h hs hs1 hK hc0 (hc.mono_order (Nat.le_succ m))
    hxsm hysm hxb hyb
  have hyy := weighted_reducedLy h hs hs1 hK hc0 (hc.mono_order (Nat.le_succ m))
    hxsm hysm hxb hyb
  have hx2 := hxx.const_mul h.isOpen.uniqueDiffOn (by
    intro p hp
    exact (contDiffAt_reducedLx (h.smoothAt hp)
      ((hxsm p hp).contDiffAt (h.isOpen.mem_nhds hp))
      ((hysm p hp).contDiffAt (h.isOpen.mem_nhds hp))
      (h.determinant p hp) (h.good p hp)).contDiffWithinAt) 2
  have hfsm := contDiffOn_errorGenerator h (V := fun _ => 0) contDiffOn_const hf
  have hcomponent : ∀ i : Fin 3, WeightedBound U s m (errorConstant m K * C / s)
      (component (errorGenerator G (fun _ => 0) f) i) := by
    intro i
    fin_cases i
    · convert hx2 using 1
      · simp only [Complex.norm_ofNat, errorConstant]
        ring
      · rfl
    · convert hyy using 1
      · unfold errorConstant
        ring
      · rfl
    · exact (weightedBound_zero U s m).mono_const (by
        exact div_nonneg (mul_nonneg (errorConstant_nonneg m hK) hC) hs.le)
  exact WeightedBound.pi h.isOpen.uniqueDiffOn hs
    (div_nonneg (mul_nonneg (errorConstant_nonneg m hK) hC) hs.le)
    (fun i => contDiffOn_pi.mp hfsm i) hcomponent

lemma errorConstant_mono {m r : ℕ} (hmr : m ≤ r) {K : ℝ} (hK : 0 ≤ K) :
    errorConstant m K ≤ errorConstant r K := by
  unfold errorConstant reducedConstant
  gcongr <;> norm_num

lemma contDiffOn_errorHierarchy {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {V : Field n} {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) (q : ℕ) :
    ContDiffOn ℝ ∞ (errorHierarchy G V f q) U := by
  intro p hp
  exact (contDiffAt_errorHierarchy (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp)) ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp) q).contDiffWithinAt


theorem weighted_errorHierarchy_zero {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (q m : ℕ)
    (hc : ModeCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f) :
    WeightedBound U s m ((errorConstant (m + q) K / s) ^ (q + 1) * C)
      (errorHierarchy G (fun _ => 0) f q) := by
  induction q generalizing m with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, pow_one, div_mul_eq_mul_div, errorHierarchy] using
      weighted_errorGenerator_zero h hs hs1 hK hC hc hf hb
  | succ q ih =>
    have hce : ModeCoefficientBound G U s (m + 1 + q + 1) K := by
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      omega
    have hbe : WeightedBound U s (m + 1 + q + 1) C f := by
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      omega
    have iht := ih (m + 1) hce hbe
    have han : 0 ≤ errorConstant (m + 1 + q) K / s :=
      div_nonneg (errorConstant_nonneg _ hK) hs.le
    have hbase := weighted_errorGenerator_zero h hs hs1 hK
      (mul_nonneg (pow_nonneg han _) hC) (hc.mono_order (by omega))
      (contDiffOn_errorHierarchy h (V := fun _ => 0) contDiffOn_const hf q) iht
    change WeightedBound U s m _ (errorGenerator G (fun _ => 0) (errorHierarchy G (fun _ => 0) f q))
    apply hbase.mono_const
    have he : m + 1 + q = m + (q + 1) := by omega
    rw [he]
    calc
      _ = (errorConstant m K / s) *
          ((errorConstant (m + (q + 1)) K / s) ^ (q + 1) * C) := by ring
      _ ≤ (errorConstant (m + (q + 1)) K / s) *
          ((errorConstant (m + (q + 1)) K / s) ^ (q + 1) * C) := by
        apply mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (errorConstant_mono (Nat.le_add_right m (q + 1)) hK) hs.le)
        exact mul_nonneg (pow_nonneg (div_nonneg (errorConstant_nonneg _ hK) hs.le) _) hC
      _ = _ := by ring

lemma weighted_tensor_complex_smul {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {f : Tensor} (hs : 0 < s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun p => a • f p) := by
  apply WeightedBound.pi hU hs (mul_nonneg (norm_nonneg _) hC)
  · intro i
    exact contDiffOn_const.mul (contDiffOn_pi.mp hf i)
  · intro i
    exact (hb.component hU hs.le hC hf i).const_mul hU (contDiffOn_pi.mp hf i) a




theorem weighted_residual_modeApprox_zero {τ : ℝ} (hτ : 0 < τ)
    {G : Field n} (hG : ContDiff ℝ ∞ G) {U : Set Base} (h : ModeDomain G U)
    {s K C : ℝ} {f : Tensor} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (q m : ℕ)
    (hc : ModeCoefficientBound G U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 1) C f) :
    WeightedBound U s m (errorConstant (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C)
      (residual τ G f (modeApprox τ G (fun _ => 0) f q)) := by
  have hbound := weighted_errorHierarchy_zero h hs hs1 hK hC hf q m hc hb
  have hn : 0 ≤ (errorConstant (m + q) K / s) ^ (q + 1) * C :=
    mul_nonneg (pow_nonneg (div_nonneg (errorConstant_nonneg _ hK) hs.le) _) hC
  have hsm := contDiffOn_errorHierarchy h (V := fun _ => 0) contDiffOn_const hf q
  have hh := weighted_tensor_complex_smul h.isOpen.uniqueDiffOn hs hn hsm hbound
    ((-((τ : ℂ) / Complex.I)) ^ q * ((τ : ℂ) / Complex.I))
  have hnorm : ‖(-((τ : ℂ) / Complex.I)) ^ q * ((τ : ℂ) / Complex.I)‖ = τ ^ (q + 1) := by
    simp only [norm_mul, norm_pow, norm_neg, norm_div, Complex.norm_I, div_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ, pow_succ]
  rw [hnorm] at hh
  have hconstant : τ ^ (q + 1) * ((errorConstant (m + q) K / s) ^ (q + 1) * C) =
      errorConstant (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C := by
    rw [div_pow, div_pow]
    ring
  rw [hconstant] at hh
  apply hh.congr
  intro p hp
  exact residual_modeApprox_power (ne_of_gt hτ) hG h.isOpen contDiffOn_const hf h.determinant
    (fun _ _ => dotProduct_zero _) (fun _ _ => dotProduct_zero _) h.good
    (fun _ _ => dotProduct_zero _) q p hp

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

end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
attribute [-instance] _root_.instVAddIntReal_solutions
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


end ClosedSurfaceR4.RealModes

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

lemma WeightedBound.indicator_of_support {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    WeightedBound univ s m C (U.indicator f) := by
  classical
  apply WeightedBound.extend_support hU ((tsupport_indicator_subset hK hz).trans hKU) hC
  apply hb.congr
  intro x hx
  exact indicator_of_mem hx f

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedWeightedSeminorm_component {K : Compacts A} (s : ℝ≥0) (m j : ℕ)
    (hj : j ≤ m) (f : SupportedField (F := F) K) :
    (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤
      supportedWeightedSeminorm K s m f := by
  let q : ℕ → Seminorm ℝ (SupportedField (F := F) K) :=
    fun j => s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j
  have h : q j f ≤ (Finset.range (m + 1)).sup q f :=
    Seminorm.le_finset_sup_apply (show j ∈ Finset.range (m + 1) by simpa using hj)
  simpa only [q, supportedWeightedSeminorm, smul_apply, NNReal.smul_def,
    NNReal.coe_pow, smul_eq_mul] using h

lemma weightedBound_of_supportedSeminorm {K : Compacts A} (s : ℝ≥0) (m : ℕ)
    (f : SupportedField (F := F) K) :
    WeightedBound Set.univ s m (supportedWeightedSeminorm K s m f) f := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  calc
    (s : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f :=
      mul_le_mul_of_nonneg_left (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
        (pow_nonneg s.coe_nonneg _)
    _ ≤ _ := supportedWeightedSeminorm_component s m j hj f

lemma supportedSeminorm_le_of_weightedBound {K : Compacts A} {s : ℝ≥0} (hs : 0 < (s : ℝ))
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : SupportedField (F := F) K)
    (hb : WeightedBound Set.univ s m C f) : supportedWeightedSeminorm K s m f ≤ C := by
  apply Seminorm.finset_sup_apply_le hC
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C
  have hn : ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C / (s : ℝ) ^ j := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (div_nonneg hC (pow_nonneg s.coe_nonneg _)) j f).2
    intro x _
    simpa only [iteratedFDerivWithin_univ] using hb.deriv_le hs hjm (Set.mem_univ x)
  calc
    _ ≤ (s : ℝ) ^ j * (C / (s : ℝ) ^ j) := mul_le_mul_of_nonneg_left hn (pow_nonneg s.coe_nonneg _)
    _ = C := by field_simp [ne_of_gt hs]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedModeBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted seminorm bounds for the actual first geometric parametrix and
its conjugated metric residual. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma forcedModeLM_zero_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : ReconstructionCoefficientBound G U s (m + 1) B)
    (f : SupportedField (F := Fin 3 → ℂ) K) :
    supportedWeightedSeminorm K s m (forcedModeLM τ hG h K hKU 0 f) ≤
      initialConstant n m B * supportedWeightedSeminorm K s (m + 1) f := by
  let C := supportedWeightedSeminorm K s (m + 1) f
  have hC : 0 ≤ C := apply_nonneg _ _
  have hb := (weightedBound_of_supportedSeminorm s (m + 1) f).restrict_open h.isOpen
  have hv := weighted_initialAmplitude hτ h hs hτs hs1 hB hC hc
    f.contDiff.contDiffOn (V := fun _ => 0) contDiffOn_const hb
    ((weightedBound_zero U s (m + 1)).mono_const hC)
  have hg : WeightedBound Set.univ s m (initialConstant n m B * C)
      (forcedModeLM τ hG h K hKU 0 f) :=
    hv.extend_support h.isOpen
      ((forcedModeLM τ hG h K hKU 0 f).tsupport_subset.trans hKU)
      (mul_nonneg (initialConstant_nonneg _ _ hB) hC)
  exact supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (initialConstant_nonneg _ _ hB) hC) _ hg

/-- One geometric correction gains the factor `τ / s` with one derivative
of the forcing. This is the actual differential operator residual. -/
lemma geometric_defect_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : ModeCoefficientBound G U s (m + 1) B)
    (f : SupportedField (F := Fin 3 → ℂ) K) :
    supportedWeightedSeminorm K s m
      (conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f) ≤
      (τ / s) * errorConstant m B * supportedWeightedSeminorm K s (m + 1) f := by
  let C := supportedWeightedSeminorm K s (m + 1) f
  have hC : 0 ≤ C := apply_nonneg _ _
  have hb := (weightedBound_of_supportedSeminorm s (m + 1) f).restrict_open h.isOpen
  have hv := weighted_residual_modeApprox_zero hτ hG h hs hs1 hB hC
    f.contDiff.contDiffOn 0 m hc hb
  have hn : 0 ≤ errorConstant m B * (τ / s) * C :=
    mul_nonneg (mul_nonneg (errorConstant_nonneg _ hB) (div_nonneg hτ.le hs.le)) hC
  have hg : WeightedBound Set.univ s m (errorConstant m B * (τ / s) * C)
      (conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f) := by
    apply (show WeightedBound U s m (errorConstant m B * (τ / s) * C)
      (conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f) by
        change WeightedBound U s m (errorConstant m B * (τ / s) * C)
          (residual τ G f (modeApprox τ G (fun _ => 0) f 0))
        simpa only [Nat.add_zero, zero_add, pow_one] using hv).extend_support h.isOpen
      ((conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f).tsupport_subset.trans hKU) hn
  have hh := supportedSeminorm_le_of_weightedBound hs hn
    (conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f) hg
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [C]
  ring

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrix
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite parametrix improvement with derivative loss. This is a finite
algebraic iteration; no bounded inverse on one Banach space is assumed. -/
noncomputable section

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma residual_succ (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) (j : ℕ) :
    residual A S b z (j + 1) = -defect A S (residual A S b z j) := by
  simp only [residual, improve, map_sub, defect, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.id_apply]
  abel

lemma improve_difference (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) (j : ℕ) :
    improve A S b z (j + 1) - improve A S b z j = -S (residual A S b z j) := by
  simp only [improve, residual]
  abel

lemma boundProfile_nonneg {L : ℕ} {K C : ℕ → ℝ}
    (hK : ∀ m, 0 ≤ K m) (hC : ∀ m, 0 ≤ C m) (j m : ℕ) :
    0 ≤ boundProfile L K C j m := by
  induction j generalizing m with
  | zero => exact hC m
  | succ j ih => exact mul_nonneg (hK m) (ih (m + L))

/-- Each finite correction gains one small factor while paying only the
stated finite number of additional input derivatives. -/
theorem residual_bound (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (L : ℕ) (K C : ℕ → ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hK : ∀ m, 0 ≤ K m)
    (hdef : ∀ m f, p m (defect A S f) ≤ η * K m * p (m + L) f)
    (hinit : ∀ m, p m (A z - b) ≤ C m) (j m : ℕ) :
    p m (residual A S b z j) ≤ η ^ j * boundProfile L K C j m := by
  induction j generalizing m with
  | zero => simpa only [residual, improve, boundProfile, pow_zero, one_mul] using hinit m
  | succ j ih =>
    rw [residual_succ, map_neg_eq_map]
    calc
      _ ≤ η * K m * p (m + L) (residual A S b z j) := hdef m _
      _ ≤ η * K m * (η ^ j * boundProfile L K C j (m + L)) :=
        mul_le_mul_of_nonneg_left (ih (m + L)) (mul_nonneg hη (hK m))
      _ = _ := by simp only [boundProfile, pow_succ] <;> ring

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PerturbedParametrix
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding a differential perturbation to a finite parametrix: the two error
parameters add, while the prescribed finite derivative loss stays explicit. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma defect_add (A R : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (f : F) :
    defect (A + R) S f = defect A S f + R (S f) := by
  simp only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply]
  abel

theorem perturbed_defect_bound (A R : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E)
    (p : ℕ → Seminorm ℝ F) (L : ℕ) (K₀ K₁ : ℕ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₀ : ∀ m f, p m (defect A S f) ≤ a * K₀ m * p (m + L) f)
    (h₁ : ∀ m f, p m (R (S f)) ≤ b * K₁ m * p (m + L) f)
    (m : ℕ) (f : F) :
    p m (defect (A + R) S f) ≤ (a + b) * max (K₀ m) (K₁ m) * p (m + L) f := by
  rw [defect_add]
  calc
    _ ≤ p m (defect A S f) + p m (R (S f)) := map_add_le_add _ _ _
    _ ≤ a * K₀ m * p (m + L) f + b * K₁ m * p (m + L) f := add_le_add (h₀ m f) (h₁ m f)
    _ ≤ a * max (K₀ m) (K₁ m) * p (m + L) f +
        b * max (K₀ m) (K₁ m) * p (m + L) f := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (apply_nonneg _ _)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
          (apply_nonneg _ _)
    _ = _ := by ring

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedTupleOperators
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite tuples of supported linear operators, with actual weighted
seminorm bounds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A F E ι : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup E] [Module ℝ E]
  [Fintype ι]

lemma supportedWeightedSeminorm_mono {K : Compacts A} (s : ℝ≥0) {m r : ℕ} (hmr : m ≤ r)
    (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm K s m f ≤ supportedWeightedSeminorm K s r f := by
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact supportedWeightedSeminorm_component s r j (hjm.trans hmr) f

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GeometricPerturbedParametrix
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite improvement of the actual geometric parametrix in the presence
of a supported differential perturbation. The perturbation estimate is
stated with explicit derivative loss so that polynomial operators can be
inserted without a Banach-space inverse assumption. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma perturbed_geometric_defect_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (m : ℕ) (f : SupportedField (F := Fin 3 → ℂ) K) :
    supportedWeightedSeminorm K s m
      (FiniteParametrix.defect ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
        ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) f) ≤
      (τ / s + ε / τ ^ p) *
        max (errorConstant m (B m)) (D m * initialConstant n (m + L) (B (m + L))) *
        supportedWeightedSeminorm K s (m + (L + 1)) f := by
  apply FiniteParametrix.perturbed_defect_bound
    ((conjugatedDLM τ hG K).restrictScalars ℝ) R
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ)
    (fun r => supportedWeightedSeminorm K s r) (L + 1)
    (fun r => errorConstant r (B r))
    (fun r => D r * initialConstant n (r + L) (B (r + L)))
    (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  · intro r g
    have hh := geometric_defect_bound τ hG h K hKU hτ hs hs1 (hB r) r
      (hc r).toFullModeCoefficientBound.toModeCoefficientBound g
    calc
      _ ≤ (τ / s) * errorConstant r (B r) * supportedWeightedSeminorm K s (r + 1) g := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (supportedWeightedSeminorm_mono s (by omega) g)
        (mul_nonneg (div_nonneg hτ.le hs.le) (errorConstant_nonneg _ (hB r)))
  · intro r g
    calc
      _ ≤ ε / τ ^ p * D r * supportedWeightedSeminorm K s (r + L)
          (forcedModeLM τ hG h K hKU 0 g) := hR r _
      _ ≤ ε / τ ^ p * D r * (initialConstant n (r + L) (B (r + L)) *
          supportedWeightedSeminorm K s (r + L + 1) g) :=
        mul_le_mul_of_nonneg_left
          (forcedModeLM_zero_bound τ hG h K hKU hτ hs hτs hs1 (hB (r + L)) (r + L) (hc (r + L)) g)
          (mul_nonneg (div_nonneg hε (pow_nonneg hτ.le _)) (hD r))
      _ = _ := by rw [Nat.add_assoc]; ring

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedCoordinateChange
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric linear coordinate changes preserve the supported weighted
seminorms exactly. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedCoordinateEquiv_norm (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m : ℕ) (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm (K.map e e.continuous) s m (supportedCoordinateEquiv e K f) =
      supportedWeightedSeminorm K s m f := by
  apply le_antisymm
  · apply supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
    exact weightedBound_comp_isometry e.symm f.contDiff (weightedBound_of_supportedSeminorm s m f)
  · have hb := weightedBound_comp_isometry e (supportedCoordinateEquiv e K f).contDiff
      (weightedBound_of_supportedSeminorm s m (supportedCoordinateEquiv e K f))
    have hid : (supportedCoordinateEquiv e K f : B → F) ∘ e = (f : A → F) := by
      funext x
      change f (e.symm (e x)) = f x
      rw [e.symm_apply_apply]
    rw [hid] at hb
    exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _) f hb

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrixSize
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite parametrix improvement controls amplitudes as well as residuals. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma improve_sub_initial (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) (j : ℕ) :
    improve A S b z j - z = -∑ i ∈ Finset.range j, S (residual A S b z i) := by
  induction j with
  | zero => simp [improve]
  | succ j ih =>
    rw [Finset.sum_range_succ, neg_add]
    have h := improve_difference A S b z j
    rw [← ih]
    rw [← h]
    abel

lemma improve_sub_initial_bound (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (q : ℕ → Seminorm ℝ E) (L : ℕ) (K C B : ℕ → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (hK : ∀ m, 0 ≤ K m) (hB : ∀ m, 0 ≤ B m)
    (hdef : ∀ m f, p m (defect A S f) ≤ η * K m * p (m + L) f)
    (hS : ∀ m f, q m (S f) ≤ B m * p (m + L) f)
    (hinit : ∀ m, p m (A z - b) ≤ C m) (j m : ℕ) :
    q m (improve A S b z j - z) ≤
      ∑ i ∈ Finset.range j, B m * η ^ i * boundProfile L K C i (m + L) := by
  rw [improve_sub_initial, map_neg_eq_map]
  have hsum : q m (∑ i ∈ Finset.range j, S (residual A S b z i)) ≤
      ∑ i ∈ Finset.range j, q m (S (residual A S b z i)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (map_add_le_add _ _ _).trans (add_le_add ih le_rfl)
  apply hsum.trans
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ B m * p (m + L) (residual A S b z i) := hS m _
    _ ≤ B m * (η ^ i * boundProfile L K C i (m + L)) :=
      mul_le_mul_of_nonneg_left (residual_bound A S b z p L K C hη hK hdef hinit i (m + L)) (hB m)
    _ = _ := by ring

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrixPowers
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial residual already contains one small factor. Finite
improvement retains that factor in both residual and amplitude estimates. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.FiniteParametrix

lemma boundProfile_const_mul (L : ℕ) (K C : ℕ → ℝ) (a : ℝ) (j m : ℕ) :
    boundProfile L K (fun r => a * C r) j m = a * boundProfile L K C j m := by
  induction j generalizing m with
  | zero => rfl
  | succ j ih => rw [boundProfile, ih, boundProfile]; ring

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem improve_sub_initial_small (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (q : ℕ → Seminorm ℝ E) (L : ℕ) (K C B : ℕ → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hK : ∀ m, 0 ≤ K m)
    (hC : ∀ m, 0 ≤ C m) (hB : ∀ m, 0 ≤ B m)
    (hdef : ∀ m f, p m (defect A S f) ≤ η * K m * p (m + L) f)
    (hS : ∀ m f, q m (S f) ≤ B m * p (m + L) f)
    (hinit : ∀ m, p m (A z - b) ≤ η * C m) (j m : ℕ) :
    q m (improve A S b z j - z) ≤
      η * ∑ i ∈ Finset.range j, B m * boundProfile L K C i (m + L) := by
  have hh := improve_sub_initial_bound A S b z p q L K (fun r => η * C r) B
    hη hK hB hdef hS hinit j m
  apply hh.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [boundProfile_const_mul]
  calc
    _ = η * (B m * boundProfile L K C i (m + L)) * η ^ i := by ring
    _ ≤ η * (B m * boundProfile L K C i (m + L)) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hη hη1)
        (mul_nonneg hη (mul_nonneg (hB m) (boundProfile_nonneg hK hC i (m + L))))
    _ = _ := mul_one _

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedInitialMode
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported initial amplitudes with both forcing and a free normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma initialMode_free_bound (τ : ℝ) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : ReconstructionCoefficientBound G U s (m + 1) B)
    (V : SupportedField (F := Ambient n) K) :
    supportedWeightedSeminorm K s m (initialMode τ h K hKU V 0) ≤
      initialConstant n m B * supportedWeightedSeminorm K s (m + 1) V := by
  let C := supportedWeightedSeminorm K s (m + 1) V
  have hC : 0 ≤ C := apply_nonneg _ _
  have hv := weighted_initialAmplitude hτ h hs hτs hs1 hB hC hc
    (f := fun _ => 0) contDiffOn_const V.contDiff.contDiffOn
    ((weightedBound_zero U s (m + 1)).mono_const hC)
    ((weightedBound_of_supportedSeminorm s (m + 1) V).restrict_open h.isOpen)
  have hglobal : WeightedBound Set.univ s m (initialConstant n m B * C)
      (initialMode τ h K hKU V 0) :=
    hv.extend_support h.isOpen ((initialMode τ h K hKU V 0).tsupport_subset.trans hKU)
      (mul_nonneg (initialConstant_nonneg _ _ hB) hC)
  exact supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (initialConstant_nonneg _ _ hB) hC) _ hglobal

lemma initialMode_free_difference (τ : ℝ) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : ReconstructionCoefficientBound G U s (m + 1) B)
    (V : SupportedField (F := Ambient n) K) :
    supportedWeightedSeminorm K s m (initialMode τ h K hKU V 0 - V) ≤
      amplitudeConstant n m B * (τ / s) * supportedWeightedSeminorm K s (m + 1) V := by
  let C := supportedWeightedSeminorm K s (m + 1) V
  have hC : 0 ≤ C := apply_nonneg _ _
  have hv := weighted_initialAmplitude_free_sub hτ h hs hs1 hB hC hc V.contDiff.contDiffOn
    ((weightedBound_of_supportedSeminorm s (m + 1) V).restrict_open h.isOpen)
  have hn : 0 ≤ amplitudeConstant n m B * (τ / s) * C :=
    mul_nonneg (mul_nonneg (amplitudeConstant_nonneg _ _ hB) (div_nonneg hτ.le hs.le)) hC
  have hl : WeightedBound U s m (amplitudeConstant n m B * (τ / s) * C)
      (initialMode τ h K hKU V 0 - V) := hv
  have hg := hl.extend_support h.isOpen ((initialMode τ h K hKU V 0 - V).tsupport_subset.trans hKU) hn
  exact supportedSeminorm_le_of_weightedBound hs hn _ hg

lemma initialMode_free_residual (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : FullModeCoefficientBound G U s (m + 1) B)
    (V : SupportedField (F := Ambient n) K)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) :
    supportedWeightedSeminorm K s m (conjugatedDLM τ hG K (initialMode τ h K hKU V 0)) ≤
      fullErrorConstant n m B * (τ / s) * supportedWeightedSeminorm K s (m + 1) V := by
  let C := supportedWeightedSeminorm K s (m + 1) V
  have hC : 0 ≤ C := apply_nonneg _ _
  have hv := weighted_residual_modeApprox hτ hG h hs hs1 hB hC
    (f := fun _ => 0) contDiffOn_const V.contDiff.contDiffOn hX hY hV 0 m hc
    ((weightedBound_zero U s (m + 1)).mono_const hC)
    ((weightedBound_of_supportedSeminorm s (m + 1) V).restrict_open h.isOpen)
  have hn : 0 ≤ fullErrorConstant n m B * (τ / s) * C :=
    mul_nonneg (mul_nonneg (fullErrorConstant_nonneg _ _ hB) (div_nonneg hτ.le hs.le)) hC
  have hl : WeightedBound U s m (fullErrorConstant n m B * (τ / s) * C)
      (conjugatedDLM τ hG K (initialMode τ h K hKU V 0)) := by
    change WeightedBound U s m (fullErrorConstant n m B * (τ / s) * C)
      (conjugatedD τ G (initialAmplitude τ G V (fun _ => 0)))
    simp only [Nat.add_zero, zero_add, pow_one, modeApprox] at hv
    change WeightedBound U s m (fullErrorConstant n m B * (τ / s) * C)
      (fun p => conjugatedD τ G (initialAmplitude τ G V (fun _ => 0)) p - (0 : Fin 3 → ℂ)) at hv
    simpa only [sub_zero] using hv
  have hg := hl.extend_support h.isOpen
    ((conjugatedDLM τ hG K (initialMode τ h K hKU V 0)).tsupport_subset.trans hKU) hn
  exact supportedSeminorm_le_of_weightedBound hs hn _ hg

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbedFreeMode
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite correction of an actual supported free normal seed in the
presence of the polynomial differential perturbation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma perturbed_initial_free_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (V : SupportedField (F := Ambient n) K)
    (hX : ∀ x ∈ U, coordDeriv dx G x ⬝ᵥ V x = 0)
    (hY : ∀ x ∈ U, coordDeriv dy G x ⬝ᵥ V x = 0)
    (hV : ∀ x ∈ U, goodSecond G x ⬝ᵥ V x = 0) (m : ℕ) :
    supportedWeightedSeminorm K s m
      (((conjugatedDLM τ hG K).restrictScalars ℝ + R) (initialMode τ h K hKU V 0)) ≤
      (τ / s + ε / τ ^ p) *
        max (fullErrorConstant n m (B m)) (D m * initialConstant n (m + L) (B (m + L))) *
        supportedWeightedSeminorm K s (m + (L + 1)) V := by
  have h0 := initialMode_free_residual τ hG h K hKU hτ hs hs1 (hB m) m
    (hc m).toFullModeCoefficientBound V hX hY hV
  have h1 := hR m (initialMode τ h K hKU V 0)
  have hS := initialMode_free_bound τ h K hKU hτ hs hτs hs1 (hB (m + L))
    (m + L) (hc (m + L)) V
  have hnon : 0 ≤ ε / τ ^ p * D m := mul_nonneg (div_nonneg hε (pow_nonneg hτ.le _)) (hD m)
  have h1' := h1.trans (mul_le_mul_of_nonneg_left hS hnon)
  have h0' := h0.trans (mul_le_mul_of_nonneg_left
    (supportedWeightedSeminorm_mono s (show m + 1 ≤ m + (L + 1) by omega) V)
    (mul_nonneg (fullErrorConstant_nonneg _ _ (hB m)) (div_nonneg hτ.le hs.le)))
  change supportedWeightedSeminorm K s m
    (conjugatedDLM τ hG K (initialMode τ h K hKU V 0) + R (initialMode τ h K hKU V 0)) ≤ _
  calc
    _ ≤ supportedWeightedSeminorm K s m (conjugatedDLM τ hG K (initialMode τ h K hKU V 0)) +
        supportedWeightedSeminorm K s m (R (initialMode τ h K hKU V 0)) := map_add_le_add _ _ _
    _ ≤ fullErrorConstant n m (B m) * (τ / s) * supportedWeightedSeminorm K s (m + (L + 1)) V +
        (ε / τ ^ p * D m) * (initialConstant n (m + L) (B (m + L)) *
          supportedWeightedSeminorm K s (m + L + 1) V) := add_le_add h0' h1'
    _ ≤ (τ / s) * max (fullErrorConstant n m (B m)) (D m * initialConstant n (m + L) (B (m + L))) *
          supportedWeightedSeminorm K s (m + (L + 1)) V +
        (ε / τ ^ p) * max (fullErrorConstant n m (B m)) (D m * initialConstant n (m + L) (B (m + L))) *
          supportedWeightedSeminorm K s (m + (L + 1)) V := by
      rw [Nat.add_assoc]
      apply add_le_add
      · rw [mul_comm (fullErrorConstant n m (B m)) (τ / s)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (div_nonneg hτ.le hs.le)) (apply_nonneg (supportedWeightedSeminorm K s (m + (L + 1))) V)
      · rw [mul_assoc, ← mul_assoc (D m), mul_assoc (ε / τ ^ p)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (apply_nonneg (supportedWeightedSeminorm K s (m + (L + 1))) V))
          (div_nonneg hε (pow_nonneg hτ.le _))
    _ = _ := by ring

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbedFreeModeSize
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite perturbed free mode stays close to its original normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

theorem perturbedFreeMode_near_seed (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (V : SupportedField (F := Ambient n) K)
    (hX : ∀ x ∈ U, coordDeriv dx G x ⬝ᵥ V x = 0)
    (hY : ∀ x ∈ U, coordDeriv dy G x ⬝ᵥ V x = 0)
    (hV : ∀ x ∈ U, goodSecond G x ⬝ᵥ V x = 0) (q m : ℕ) :
    let η := τ / s + ε / τ ^ p
    let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
    let C := fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))) *
      supportedWeightedSeminorm K s (r + (L + 1)) V
    supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - V) ≤
      η * ((∑ i ∈ Finset.range q, initialConstant n m (B m) *
        FiniteParametrix.boundProfile (L + 1) κ C i (m + (L + 1))) +
        amplitudeConstant n m (B m) * supportedWeightedSeminorm K s (m + (L + 1)) V) := by
  let η := τ / s + ε / τ ^ p
  let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
  let C := fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))) *
    supportedWeightedSeminorm K s (r + (L + 1)) V
  have hη : 0 ≤ η := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hκ : ∀ r, 0 ≤ κ r := fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)
  have hC : ∀ r, 0 ≤ C r := fun r => mul_nonneg
    ((fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)) (apply_nonneg _ _)
  have hdef := perturbed_geometric_defect_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR
  have hinit := perturbed_initial_free_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR V hX hY hV
  have hS : ∀ r f, supportedWeightedSeminorm K s r (forcedModeLM τ hG h K hKU 0 f) ≤
      initialConstant n r (B r) * supportedWeightedSeminorm K s (r + (L + 1)) f := by
    intro r f
    apply (forcedModeLM_zero_bound τ hG h K hKU hτ hs hτs hs1 (hB r) r (hc r) f).trans
    exact mul_le_mul_of_nonneg_left (supportedWeightedSeminorm_mono s (by omega) f)
      (initialConstant_nonneg _ _ (hB r))
  have hfinite := FiniteParametrix.improve_sub_initial_small
    ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) 0 (initialMode τ h K hKU V 0)
    (fun r => supportedWeightedSeminorm K s r) (fun r => supportedWeightedSeminorm K s r)
    (L + 1) κ C (fun r => initialConstant n r (B r)) hη hsmall hκ hC
    (fun r => initialConstant_nonneg _ _ (hB r)) hdef hS
    (fun r => by simpa only [sub_zero, C, η, mul_assoc] using hinit r) q m
  have hseed := initialMode_free_difference τ h K hKU hτ hs hs1 (hB m) m (hc m) V
  have hseed' : supportedWeightedSeminorm K s m (initialMode τ h K hKU V 0 - V) ≤
      η * (amplitudeConstant n m (B m) * supportedWeightedSeminorm K s (m + (L + 1)) V) := by
    apply hseed.trans
    have hle : τ / s ≤ η := le_add_of_nonneg_right (div_nonneg hε (pow_nonneg hτ.le _))
    calc
      _ ≤ amplitudeConstant n m (B m) * η * supportedWeightedSeminorm K s (m + 1) V :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle
          (amplitudeConstant_nonneg _ _ (hB m))) (apply_nonneg _ _)
      _ ≤ amplitudeConstant n m (B m) * η * supportedWeightedSeminorm K s (m + (L + 1)) V :=
        mul_le_mul_of_nonneg_left (supportedWeightedSeminorm_mono s (by omega) V)
          (mul_nonneg (amplitudeConstant_nonneg _ _ (hB m)) hη)
      _ = _ := by ring
  change supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - V) ≤ _
  have heq : perturbedFreeMode τ hG h K hKU R V q - V =
      (perturbedFreeMode τ hG h K hKU R V q - initialMode τ h K hKU V 0) +
        (initialMode τ h K hKU V 0 - V) := by abel
  rw [heq]
  calc
    _ ≤ supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - initialMode τ h K hKU V 0) +
        supportedWeightedSeminorm K s m (initialMode τ h K hKU V 0 - V) := map_add_le_add _ _ _
    _ ≤ _ := (add_le_add hfinite hseed').trans_eq (by ring)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteProfileBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit terminal derivative orders in finite error profiles. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteParametrix

lemma boundProfile_terminal (L : ℕ) (K C f : ℕ → ℝ) (j m : ℕ) :
    boundProfile L K (fun r => C r * f (r + L)) j m =
      boundProfile L K C j m * f (m + (j + 1) * L) := by
  induction j generalizing m with
  | zero => simp only [boundProfile, zero_add, one_mul]
  | succ j ih =>
    rw [boundProfile, ih, boundProfile]
    have he : m + L + (j + 1) * L = m + (j + 1 + 1) * L := by ring
    rw [he, mul_assoc]

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbedFreeOrderBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite derivative orders and seed-independent constants for the free correction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

lemma finite_deviation_budget {n : ℕ} (K : Compacts Base) (s : ℝ≥0) (L q m : ℕ)
    (B κ γ : ℕ → ℝ) (hB : ∀ r, 0 ≤ B r) (hκ : ∀ r, 0 ≤ κ r) (hγ : ∀ r, 0 ≤ γ r)
    (V : SupportedField (F := Ambient n) K) :
    (∑ i ∈ Finset.range q, B m * FiniteParametrix.boundProfile L κ
      (fun r => γ r * supportedWeightedSeminorm K s (r + L) V) i (m + L)) ≤
    (∑ i ∈ Finset.range q, B m * FiniteParametrix.boundProfile L κ γ i (m + L)) *
      supportedWeightedSeminorm K s (m + (q + 1) * L) V := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [FiniteParametrix.boundProfile_terminal L κ γ
    (fun r => supportedWeightedSeminorm K s r V), ← mul_assoc]
  apply mul_le_mul_of_nonneg_left
  · apply supportedWeightedSeminorm_mono s _ V
    have hi' := Finset.mem_range.mp hi
    have hmul := Nat.mul_le_mul_right L (show i + 2 ≤ q + 1 by omega)
    convert Nat.add_le_add_left hmul m using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · exact mul_nonneg (hB m) (FiniteParametrix.boundProfile_nonneg hκ hγ i (m + L))

theorem perturbedFreeMode_near_seed_order (τ : ℝ) {n : ℕ} {G : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (V : SupportedField (F := Ambient n) K)
    (hX : ∀ x ∈ U, coordDeriv dx G x ⬝ᵥ V x = 0)
    (hY : ∀ x ∈ U, coordDeriv dy G x ⬝ᵥ V x = 0)
    (hV : ∀ x ∈ U, goodSecond G x ⬝ᵥ V x = 0) (q m : ℕ) :
    let η := τ / s + ε / τ ^ p
    let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
    let γ := fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
    supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - V) ≤
      η * ((∑ i ∈ Finset.range q, initialConstant n m (B m) *
        FiniteParametrix.boundProfile (L + 1) κ γ i (m + (L + 1))) + amplitudeConstant n m (B m)) *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
  dsimp only
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  apply (perturbedFreeMode_near_seed τ hG h K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR V hX hY hV q m).trans
  have hsum := finite_deviation_budget K s (L + 1) q m
    (fun r => initialConstant n r (B r))
    (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
    (fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
    (fun r => initialConstant_nonneg _ _ (hB r))
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)) V
  have hseed := mul_le_mul_of_nonneg_left
    (supportedWeightedSeminorm_mono s (show m + (L + 1) ≤ m + (q + 1) * (L + 1) by
      have hh := Nat.mul_le_mul_right (L + 1) (show 1 ≤ q + 1 by omega)
      omega) V) (amplitudeConstant_nonneg n m (hB m))
  calc
    _ ≤ (τ / s + ε / τ ^ p) * (_ * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V +
        amplitudeConstant n m (B m) * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V) :=
      mul_le_mul_of_nonneg_left (add_le_add hsum hseed) hη
    _ = _ := by ring

end ClosedSurfaceR4.SmallModes

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformFreeModeConstants
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit free-mode constants, independent of both short scales and
of the perturbation size. These constants are used before selecting scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

lemma freeModeBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (q m : ℕ) :
    0 ≤ freeModeBudget n L B D q m := by
  apply add_nonneg _ (amplitudeConstant_nonneg _ _ (hB m))
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (initialConstant_nonneg _ _ (hB m))
  exact FiniteParametrix.boundProfile_nonneg
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)) _ _

theorem freeModeBudget_bound {n : ℕ} {G : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε τ : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (q m : ℕ) (V : SupportedField (F := Ambient n) K) (hV : FreeCoefficient G U V) :
    supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) ≤
      (τ / s + ε / τ ^ p) * freeModeBudget n L B D q m *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
  rw [perturbedFreeLM_apply]
  exact perturbedFreeMode_near_seed_order τ hG h K hKU hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR V hV.perpX hV.perpY hV.perpSecond q m


theorem freeModeBudget_size {n : ℕ} {G : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε τ : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (q m : ℕ) (V : SupportedField (F := Ambient n) K) (hV : FreeCoefficient G U V) :
    supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V) ≤
      (1 + freeModeBudget n L B D q m) *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
  have hh := freeModeBudget_bound hG h K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q m V hV
  have hn : 0 ≤ freeModeBudget n L B D q m *
      supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V :=
    mul_nonneg (freeModeBudget_nonneg n L B D hB q m) (apply_nonneg _ _)
  have he : supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) ≤
      freeModeBudget n L B D q m * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
    apply hh.trans
    simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hsmall hn
  have hmono := supportedWeightedSeminorm_mono s
    (show m ≤ m + (q + 1) * (L + 1) by omega) V
  calc
    _ = supportedWeightedSeminorm K s m ((perturbedFreeLM τ hG h K hKU R q V - V) + V) := by
      rw [sub_add_cancel]
    _ ≤ supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) +
        supportedWeightedSeminorm K s m V := map_add_le_add _ _ _
    _ ≤ freeModeBudget n L B D q m * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V +
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := add_le_add he hmono
    _ = _ := by ring

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedNormalSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported normal seeds and the exact leading quadratic metric. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm weightedBound_of_supportedSeminorm
  supportedSeminorm_le_of_weightedBound)

lemma supportedFreeSeed_isFree (δ τ : ℝ) {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (b : SupportedField (F := ℝ) K) :
    FreeCoefficient (fun p => complexify (F p)) U (supportedFreeSeed δ τ hF h K hKU b) :=
  freeSeed_isFree hF h δ τ b.contDiff.contDiffOn

lemma supportedFreeSeed_bound {δ τ : ℝ} {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (b : SupportedField (F := ℝ) K)
    {s : ℝ≥0} {B D : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hs : 0 < (s : ℝ))
    (hB : 0 ≤ B) (hD : 0 ≤ D) (m : ℕ)
    (hb : supportedWeightedSeminorm K s m b ≤ B)
    (hN : WeightedBound U s m D (freeNormal F)) :
    supportedWeightedSeminorm K s m (supportedFreeSeed δ τ hF h K hKU b) ≤
      (Real.sqrt 2 * 2 ^ m * B * D) * (δ * τ) := by
  have hh := weighted_freeSeed hF h hδ hτ hs hB hD b.contDiff.contDiffOn
    (((weightedBound_of_supportedSeminorm s m b).mono_const hb).restrict_open h.isOpen) hN
  have hn : 0 ≤ (Real.sqrt 2 * 2 ^ m * B * D) * (δ * τ) := by positivity
  have hl : WeightedBound U s m ((Real.sqrt 2 * 2 ^ m * B * D) * (δ * τ))
      (supportedFreeSeed δ τ hF h K hKU b) := hh
  exact supportedSeminorm_le_of_weightedBound hs hn _
    (hl.extend_support h.isOpen ((supportedFreeSeed δ τ hF h K hKU b).tsupport_subset.trans hKU) hn)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CorrectedNormalSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit size and difference budgets for the actual corrected normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

theorem correctedNormalSeed_bound (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + 1) (B m))
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (q m : ℕ) (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hbN : WeightedBound U s (m + (q + 1) * (L + 1)) N (freeNormal F))
    (b : SupportedField (F := ℝ) K)
    (hb : supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) b ≤ A) :
    supportedWeightedSeminorm K s m (correctedNormalSeed δ τ hF h K hKU R q b) ≤
      correctedSeedBudget L B D q m N * A * (δ * τ) := by
  have hv := supportedFreeSeed_bound hF h K hKU b hδ hτ.le hs hA hN
    (m + (q + 1) * (L + 1)) hb hbN
  have ht := freeModeBudget_size (contDiff_complexify hF) (h.complexDomain hF)
    K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q m
    (supportedFreeSeed δ τ hF h K hKU b) (supportedFreeSeed_isFree δ τ hF h K hKU b)
  have hbudget := freeModeBudget_nonneg 4 L B D hB q m
  calc
    _ ≤ (1 + freeModeBudget 4 L B D q m) *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1))
          (supportedFreeSeed δ τ hF h K hKU b) := ht
    _ ≤ (1 + freeModeBudget 4 L B D q m) *
        ((Real.sqrt 2 * 2 ^ (m + (q + 1) * (L + 1)) * A * N) * (δ * τ)) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by dsimp only [correctedSeedBudget] <;> ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CorrectedSeedCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual corrected normal seed to the polynomial jet coordinates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma inverse_supportedCoordinateEquiv_norm {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A) {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m : ℕ)
    (f : SupportedField (F := F) (K.map e e.continuous)) :
    supportedWeightedSeminorm K s m ((supportedCoordinateEquiv e K).symm f) =
      supportedWeightedSeminorm (K.map e e.continuous) s m f := by
  have hh := supportedCoordinateEquiv_norm e K hs m ((supportedCoordinateEquiv e K).symm f)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedChartEquiv
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invertible local-chart transport on supported fields and their linear
operators. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma chartPull_bound (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) {s : ℝ≥0} {J : ℝ} {m : ℕ}
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hJ : 1 ≤ J)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (f : SupportedField (F := F) (chartSupport e K hK)) :
    supportedWeightedSeminorm K s m (chartPull e he K hK f) ≤
      (m.factorial : ℝ) * supportedWeightedSeminorm (chartSupport e K hK) s m f * J ^ m := by
  have hf := (weightedBound_of_supportedSeminorm s m f).restrict_open e.open_target
  have hb := hf.comp_coordinates e.open_source.uniqueDiffOn e.open_target.uniqueDiffOn hs hs1 hJ
    (apply_nonneg _ _) he f.contDiff.contDiffOn (fun _ hx => e.map_source hx) hderiv
  apply supportedSeminorm_le_of_weightedBound hs (by positivity)
  exact hb.indicator_of_support e.open_source K.isCompact.isClosed hK (by positivity)
    (chartPull_zero e K hK f)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free geometric amplitude in the original coordinates. The same
actual polynomial operator is conjugated into the phase chart, and the
resulting amplitude is transported back with controlled derivative loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open WeightedEstimates RealModes
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem originalFreeSeed_bound_oai {δ : ℝ} (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q m : ℕ) {A N : ℝ}
    (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hn : WeightedBound c.e.target s (m + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap))
    (b : SupportedField (F := ℝ) c.chartCompact)
    (hb : supportedWeightedSeminorm c.chartCompact s (m + (q + 1) * (tensorOrder P + 1)) b ≤ A) :
    supportedWeightedSeminorm K s m (c.originalFreeSeed δ q b) ≤
      ((m.factorial : ℝ) * c.J m ^ m * correctedSeedBudget (tensorOrder P) c.C c.D q m N) * A * (δ * τ) := by
  have hz := correctedNormalSeed_bound δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) hδ hτ hs hτs hs1 hε hsmall
    c.C c.D c.nonnegC c.nonnegD c.coefficients c.operator c.polynomial q m A N hA hN hn b hb
  unfold originalFreeSeed
  rw [inverse_supportedCoordinateEquiv_norm _ _ hs]
  have hp := chartPull_bound c.e c.smoothForward (modeSupport K) c.supportChart hs hs1
    (c.oneLEJ m) (c.coordinates m) (c.freeSeed δ q b)
  apply hp.trans
  calc
    _ ≤ (m.factorial : ℝ) *
        (correctedSeedBudget (tensorOrder P) c.C c.D q m N * A * (δ * τ)) * c.J m ^ m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _))
        (pow_nonneg (zero_le_one.trans (c.oneLEJ m)) _)
    _ = _ := by ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.originalFreeSeed_bound_oai := @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.originalFreeSeed_bound_oai
