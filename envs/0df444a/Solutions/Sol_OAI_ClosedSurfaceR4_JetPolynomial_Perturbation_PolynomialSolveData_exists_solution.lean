-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:22.504212+00:00
-- url     : https://prove2.me/submissions/57e0b8fd-6270-4cfe-8511-19ac6340c050

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


lemma unitMode_hasFDerivAt (τ : ℝ) (p : Base) :
    HasFDerivAt (unitMode τ)
      (unitMode τ p • ((Complex.I / (τ : ℂ)) •
        (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)))) p := by
  exact ((Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).hasFDerivAt.const_mul
    (Complex.I / (τ : ℂ))).cexp

lemma coordDeriv_unitMode (τ : ℝ) (p v : Base) :
    coordDeriv v (unitMode τ) p = unitMode τ p * (Complex.I / (τ : ℂ)) * (v.1 : ℂ) := by
  unfold coordDeriv
  rw [(unitMode_hasFDerivAt τ p).fderiv]
  simp [mul_assoc]

lemma coordDeriv_oscillate (τ : ℝ) {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v : Base) :
    coordDeriv v (oscillate τ Z) p = unitMode τ p •
      (coordDeriv v Z p + ((Complex.I / (τ : ℂ)) * (v.1 : ℂ)) • Z p) := by
  change coordDeriv v (fun q => unitMode τ q • Z q) p = _
  rw [partial_smul (unitMode_hasFDerivAt τ p).differentiableAt hZ, coordDeriv_unitMode]
  simp only [smul_add, smul_smul]
  rw [mul_assoc, add_comm]


lemma linearizedMetric_oscillate (τ : ℝ) {G Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    linearizedMetric G (oscillate τ Z) v w p =
      unitMode τ p * conjugatedMetric τ G Z v w p := by
  unfold conjugatedMetric linearizedMetric covector
  rw [coordDeriv_oscillate τ hZ w, coordDeriv_oscillate τ hZ v]
  simp only [dotProduct_smul, dotProduct_add, smul_eq_mul]
  ring

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



end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillationBounds
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

lemma norm_iteratedFDeriv_exp_real (j : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ j Complex.exp z‖ = ‖Complex.exp z‖ := by
  have h : ContDiffAt ℂ (j : ℕ∞ω) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

lemma norm_unitMode (τ : ℝ) (p : Base) : ‖unitMode τ p‖ = 1 := by
  have he : Complex.I / (τ : ℂ) * (p.1 : ℂ) = ((p.1 / τ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  unfold unitMode
  rw [he]
  exact Complex.norm_exp_ofReal_mul_I (p.1 / τ)

lemma contDiff_unitMode (τ : ℝ) : ContDiff ℝ ∞ (unitMode τ) := by
  have hL : ContDiff ℝ ∞ (fun p : Base => (Complex.I / (τ : ℂ)) * (p.1 : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).contDiff
  exact hL.cexp



lemma weighted_unitMode {U : Set Base} (hU : IsOpen U) {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    WeightedBound U τ m 1 (unitMode τ) := by
  let L : Base →L[ℝ] ℂ := (Complex.I / (τ : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ))
  have hL : ‖L‖ ≤ τ⁻¹ := by
    apply L.opNorm_le_bound (inv_nonneg.mpr hτ.le)
    intro p
    change ‖Complex.I / (τ : ℂ) * (p.1 : ℂ)‖ ≤ _
    simp only [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le,
      one_div]
    exact mul_le_mul_of_nonneg_left (norm_fst_le p) (inv_nonneg.mpr hτ.le)
  intro j hj p hp
  rw [iteratedFDerivWithin_of_isOpen j hU hp]
  have he : unitMode τ = Complex.exp ∘ L := rfl
  rw [he, L.iteratedFDeriv_comp_right (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)) p
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
  have hh := (iteratedFDeriv ℝ j Complex.exp (L p)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)
  have hnorm : ‖iteratedFDeriv ℝ j Complex.exp (L p)‖ = 1 := by
    rw [norm_iteratedFDeriv_exp_real]
    exact norm_unitMode τ p
  rw [hnorm] at hh
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul] at hh
  calc
    _ ≤ τ ^ j * ‖L‖ ^ j := mul_le_mul_of_nonneg_left hh (pow_nonneg hτ.le _)
    _ ≤ τ ^ j * (τ⁻¹) ^ j := by gcongr
    _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hτ.ne', one_pow]

lemma contDiffOn_oscillate {n : ℕ} {U : Set Base} {Z : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) : ContDiffOn ℝ ∞ (oscillate τ Z) U :=
  (contDiff_unitMode τ).contDiffOn.smul hZ



lemma weighted_oscillate {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {τ s C : ℝ} {m : ℕ} {Z : Field n} (hτ : 0 < τ) (hτs : τ ≤ s)
    (hC : 0 ≤ C) (hZ : ContDiffOn ℝ ∞ Z U) (hb : WeightedBound U s m C Z) :
    WeightedBound U τ m (2 ^ m * C) (oscillate τ Z) := by
  have hs : 0 ≤ s := hτ.le.trans hτs
  have hz := hb.shrink_scale hτ.le hτs
  apply WeightedBound.pi hU.uniqueDiffOn hτ (by positivity)
  · intro i
    exact contDiffOn_pi.mp (contDiffOn_oscillate hZ τ) i
  · intro i
    have hh := (weighted_unitMode hU hτ m).mul hU.uniqueDiffOn hτ.le (by norm_num) hC
      (contDiff_unitMode τ).contDiffOn (contDiffOn_pi.mp hZ i)
      (hz.component hU.uniqueDiffOn hτ.le hC hZ i)
    simpa only [mul_one, oscillate, Pi.smul_apply, smul_eq_mul] using hh

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedModes
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (realPartCLM)

lemma norm_realPartCLM_le (n : ℕ) : ‖realPartCLM n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Z
  rw [one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg Z)).2 fun i =>
    ((Complex.abs_re_le_norm (Z i)).trans (norm_le_pi_norm Z i))

lemma realOsc_eq_displacement (τ : ℝ) {n : ℕ} (Z : Field n) :
    realOsc τ Z = ClosedSurfaceR4.QuadraticMean.displacement τ Prod.fst Z := by
  funext p
  unfold realOsc ClosedSurfaceR4.QuadraticMean.displacement
    ClosedSurfaceR4.QuadraticMean.realMode oscillate
  congr 2
  simp only [unitMode, ClosedSurfaceR4.QuadraticMean.phase, Complex.ofReal_div]
  congr 1
  ring

lemma contDiffOn_realOsc {n : ℕ} {U : Set Base} {Z : Field n}
    (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) : ContDiffOn ℝ ∞ (realOsc τ Z) U :=
  (realPartCLM n).contDiff.comp_contDiffOn (contDiffOn_oscillate hZ τ)

lemma weighted_realPart {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {Z : Field n} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hZ : ContDiffOn ℝ ∞ Z U) (hb : WeightedBound U s m C Z) :
    WeightedBound U s m C (fun p => QuadraticMean.realPart (Z p)) := by
  have hh := hb.linear hU hs hZ (realPartCLM n)
  exact hh.mono_const (mul_le_of_le_one_left hC (norm_realPartCLM_le n))

lemma weighted_realOsc {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {τ s C : ℝ} {m : ℕ} {Z : Field n} (hτ : 0 < τ) (hτs : τ ≤ s)
    (hC : 0 ≤ C) (hZ : ContDiffOn ℝ ∞ Z U) (hb : WeightedBound U s m C Z) :
    WeightedBound U τ m (2 ^ m * C) (realOsc τ Z) :=
  weighted_realPart hU.uniqueDiffOn hτ.le (mul_nonneg (by positivity) hC)
    (contDiffOn_oscillate hZ τ) (weighted_oscillate hU hτ hτs hC hZ hb)

lemma coordDeriv_realPart {n : ℕ} {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v : Base) :
    coordDeriv v (fun q => QuadraticMean.realPart (Z q)) p = QuadraticMean.realPart (coordDeriv v Z p) := by
  exact congrArg (fun A : Base →L[ℝ] RVec n => A v)
    (((realPartCLM n).hasFDerivAt.comp p hZ.hasFDerivAt).fderiv)

lemma complexify_dot_realPart {n : ℕ} (X : RVec n) (Z : Ambient n) :
    (complexify X ⬝ᵥ Z).re = X ⬝ᵥ QuadraticMean.realPart Z := by
  simp [dotProduct, QuadraticMean.realPart, Complex.mul_re]


lemma realLinearized_realPart {n : ℕ} {F : RField n} {Z : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    realLinearized F (fun q => QuadraticMean.realPart (Z q)) v w p =
      (linearizedMetric (fun q => complexify (F q)) Z v w p).re := by
  simp only [realLinearized, linearizedMetric, coordDeriv_realPart hZ,
    coordDeriv_complexify hF, Complex.add_re, complexify_dot_realPart]

lemma realLinearized_realOsc {n : ℕ} {F : RField n} {Z : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v w : Base) :
    realLinearized F (realOsc τ Z) v w p =
      (unitMode τ p * conjugatedMetric τ (fun q => complexify (F q)) Z v w p).re := by
  have hO : DifferentiableAt ℝ (oscillate τ Z) p := by
    unfold oscillate
    exact (unitMode_hasFDerivAt τ p).differentiableAt.smul hZ
  unfold realOsc
  rw [realLinearized_realPart hF hO, linearizedMetric_oscillate τ hZ]

lemma realLinearized_residual {n : ℕ} {F : RField n} {Z : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (f : Tensor) :
    realLinearizedTensor F (realOsc τ Z) p - realOsc τ f p =
      realOsc τ (SmallModes.residual τ (fun q => complexify (F q)) f Z) p := by
  ext i
  fin_cases i <;>
    simp [realLinearizedTensor, realLinearized_realOsc hF hZ, realOsc, QuadraticMean.realPart,
      oscillate, SmallModes.residual, conjugatedD, tensorOf, mul_sub, Matrix.vecHead, Matrix.vecTail]




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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearizedTensor_apply {n : ℕ} (F U : RField n) (p : Base) (i : Fin 3) :
    realLinearizedTensor F U p i = realLinearized F U (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorCoordinates
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean

lemma evaluate_realLinearizedTensor {n : ℕ} (F X : RField n) (p v w : Base) :
    evaluate (realLinearizedTensor F X p) v w = realLinearized F X v w p := by
  simp only [realLinearized, derivative_base_decomposition F p v,
    derivative_base_decomposition F p w, derivative_base_decomposition X p v,
    derivative_base_decomposition X p w]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold evaluate
  simp only [realLinearizedTensor_apply, firstDirection, secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, realLinearized]
  ring



lemma realLinearizedTensor_comp {n : ℕ} {F X : RField n} {χ : Base → Base} {p : Base}
    (hF : DifferentiableAt ℝ F (χ p)) (hX : DifferentiableAt ℝ X (χ p))
    (hχ : DifferentiableAt ℝ χ p) :
    realLinearizedTensor (F ∘ χ) (X ∘ χ) p =
      pullbackField χ p (realLinearizedTensor F X (χ p)) := by
  ext i
  rw [realLinearizedTensor_apply]
  change realLinearized (F ∘ χ) (X ∘ χ) (firstDirection i) (secondDirection i) p =
    evaluate (realLinearizedTensor F X (χ p))
      (fderiv ℝ χ p (firstDirection i)) (fderiv ℝ χ p (secondDirection i))
  rw [evaluate_realLinearizedTensor]
  simp only [realLinearized, coordDeriv, fderiv_comp p hF hχ, fderiv_comp p hX hχ,
    ContinuousLinearMap.comp_apply]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ComplexPullback
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base dx dy)
open ClosedSurfaceR4.QuadraticMean (realMode)
open ClosedSurfaceR4.RealModes (base_decomposition)

lemma realMode_complexPullback (J : Base →L[ℝ] Base) (A : ComplexTensor) (θ : ℝ) :
    realMode θ (complexPullback J A) = pullback J (realMode θ A) := by
  unfold realMode
  rw [← map_smul, realPart_complexPullback]

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
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

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.SmallModes (coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (contDiffOn_dot)

lemma weighted_real_complex {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)




end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PullbackBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (complexify)
open ClosedSurfaceR4.QuadraticMean (weighted_real_complex)

lemma weighted_base_fst {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).1) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.fst ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ))

lemma weighted_base_snd {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).2) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.snd ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ))

lemma weighted_complexEvaluate {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → ComplexTensor} {v w : Base → Base} {s C D B : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hA : ContDiffOn ℝ ∞ A U) (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U)
    (hbA : WeightedBound U s m C A) (hbv : WeightedBound U s m D v)
    (hbw : WeightedBound U s m B w) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * B))
      (fun p => complexEvaluate (A p) (v p) (w p)) := by
  have hvc := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.fst
  have hvd := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.snd
  have hwc := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.fst
  have hwd := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.snd
  have hvcB := weighted_real_complex hU hs hD hv.fst (weighted_base_fst hU hs hD hv hbv)
  have hvdB := weighted_real_complex hU hs hD hv.snd (weighted_base_snd hU hs hD hv hbv)
  have hwcB := weighted_real_complex hU hs hB hw.fst (weighted_base_fst hU hs hB hw hbw)
  have hwdB := weighted_real_complex hU hs hB hw.snd (weighted_base_snd hU hs hB hw hbw)
  have h0s := ((contDiffOn_pi.mp hA 0).mul hvc).mul hwc
  have h1s := (contDiffOn_pi.mp hA 1).mul ((hvc.mul hwd).add (hvd.mul hwc))
  have h2s := ((contDiffOn_pi.mp hA 2).mul hvd).mul hwd
  have h0 := ((hbA.component hU hs hC hA 0).mul hU hs hC hD
    (contDiffOn_pi.mp hA 0) hvc hvcB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 0).mul hvc) hwc hwcB
  have h2 := ((hbA.component hU hs hC hA 2).mul hU hs hC hD
    (contDiffOn_pi.mp hA 2) hvd hvdB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 2).mul hvd) hwd hwdB
  have h11 := hvcB.mul hU hs hD hB hvc hwd hwdB
  have h12 := hvdB.mul hU hs hD hB hvd hwc hwcB
  have h1 := (hbA.component hU hs hC hA 1).mul hU hs hC (by positivity)
    (contDiffOn_pi.mp hA 1) ((hvc.mul hwd).add (hvd.mul hwc))
    (h11.add hU hs (hvc.mul hwd) (hvd.mul hwc) h12)
  have hh := (h0.add hU hs h0s h1s h1).add hU hs (h0s.add h1s) h2s h2
  convert hh using 1 <;> first | rfl | ring

lemma weighted_complexPullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → ComplexTensor} {e : Base → Base} {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U)
    (hbA : WeightedBound U s m C A)
    (hbe : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m D (coordDeriv v e)) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * D))
      (fun p => complexPullbackField e p (A p)) := by
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    (contDiffOn_pi.mp (contDiffOn_complexPullbackField_apply hU hA he))
  intro i
  exact weighted_complexEvaluate hU.uniqueDiffOn hs.le hC hD hD hA
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (firstDirection i))
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (secondDirection i)) hbA
    (hbe _ (firstDirection_norm i)) (hbe _ (secondDirection_norm i))

lemma weighted_complexify {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → Fin n → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C)
    (hA : ContDiffOn ℝ ∞ A U) (hb : WeightedBound U s m C A) :
    WeightedBound U s m C (fun p => complexify (A p)) := by
  apply WeightedBound.pi hU hs hC (contDiffOn_pi.mp (contDiffOn_complexify hA))
  intro i
  exact weighted_real_complex hU hs.le hC (contDiffOn_pi.mp hA i)
    (hb.component hU hs.le hC hA i)

lemma weighted_pullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → Tensor} {e : Base → Base} {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U)
    (hbA : WeightedBound U s m C A)
    (hbe : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m D (coordDeriv v e)) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * D))
      (fun p => pullbackField e p (A p)) := by
  have hb := weighted_complexPullbackField_apply hU hs hC hD
    (contDiffOn_complexify hA) he (weighted_complexify hU.uniqueDiffOn hs hC hA hbA) hbe
  have hr := RealModes.weighted_realPart hU.uniqueDiffOn hs.le (by positivity)
    (contDiffOn_complexPullbackField_apply hU (contDiffOn_complexify hA) he) hb
  simpa only [complexPullbackField, realPart_complexPullback, realPart_complexify, pullbackField] using hr

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SupportedCancellation
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
open Set ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)

lemma realLinearizedTensor_congr_right {n : ℕ} {F X Y : RField n} {p : Base}
    (h : X =ᶠ[nhds p] Y) : realLinearizedTensor F X p = realLinearizedTensor F Y p := by
  ext i
  simp only [realLinearizedTensor_apply, realLinearized, coordDeriv, h.fderiv_eq]

lemma realLinearizedTensor_zero_right {n : ℕ} (F : RField n) (p : Base) :
    realLinearizedTensor F (fun _ => 0) p = 0 := by
  ext i
  simp [realLinearizedTensor_apply, realLinearized, coordDeriv]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ExtendedCancellation
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

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter



lemma displacement_zero_value {n : ℕ} (τ : ℝ) (φ : Base → ℝ) {A : Field n}
    {p : Base} (hA : A p = 0) : displacement τ φ A p = 0 := by
  ext i
  simp [displacement, QuadraticMean.realMode, QuadraticMean.realPart, hA]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedSolve
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter

lemma contDiffOn_displacement {n : ℕ} {U : Set Base} {φ : Base → ℝ} {Z : Field n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (displacement τ φ Z) U := by
  have he : ContDiffOn ℝ ∞ (fun p => QuadraticMean.phase (φ p / τ)) U := by
    exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hφ.div_const τ)).mul contDiffOn_const).cexp
  exact (QuadraticMean.realPartCLM n).contDiff.comp_contDiffOn (he.smul hZ)



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_UniformMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.FiniteMean Set
open ClosedSurfaceR4.RootMean



lemma weighted_coordDeriv_of_jets {U : Set Base} (hU : IsOpen U)
    {f : Base → Base} (hf : ContDiffOn ℝ ∞ f U) {τ D : ℝ} {m : ℕ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ j, 1 ≤ j → j ≤ m + 1 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ j f U p‖ ≤ D) (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U τ m D (coordDeriv v f) := by
  have hd : WeightedBound U τ m D (fderivWithin ℝ f U) := by
    intro j hj p hp
    rw [norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hp]
    exact (mul_le_mul_of_nonneg_left (hb (j+1) (by omega) (by omega) p hp)
      (pow_nonneg hτ j)).trans (mul_le_of_le_one_left hD (pow_le_one₀ hτ hτ1))
  have hh := hd.clm_apply_const hU.uniqueDiffOn hτ
    (hf.fderivWithin hU.uniqueDiffOn le_rfl) v
  apply (hh.mono_const (mul_le_of_le_one_left hD hv)).congr
  intro p hp
  simp only [coordDeriv, fderivWithin_of_isOpen hU hp]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetCalculus
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient part of the mixed polynomial variation is the actual
low-jet chain rule, with the position coordinates held fixed. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

lemma variationLowJet_expansion (H : Base → Space) (p : Base) :
    variationLowJet H p = ∑ i : Fin 7 × Fin 4,
      jet H (lowWord i.1) i.2 p • lowBasis (.inr i) := by
  funext k
  cases k with
  | inl k => simp [variationLowJet, lowBasis]
  | inr k => simp [variationLowJet, lowBasis, Pi.single_apply]

lemma coefficient_variation_sum (c : LowJet × ℝ → ℝ) (G H : Base → Space) (z : Base × ℝ) :
    fderiv ℝ c (lowJet G z.1, z.2) (variationLowJet H z.1, 0) =
      ∑ i : Fin 7 × Fin 4, jet H (lowWord i.1) i.2 z.1 *
        fderiv ℝ c (lowJet G z.1, z.2) (lowBasis (.inr i), 0) := by
  let L : LowJet →L[ℝ] ℝ :=
    (fderiv ℝ c (lowJet G z.1, z.2)).comp (ContinuousLinearMap.inl ℝ LowJet ℝ)
  change L (variationLowJet H z.1) = _
  rw [variationLowJet_expansion, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

end ClosedSurfaceR4.JetPolynomial

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexJetDecomposition
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and imaginary parts commute with all actual ordered jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma complexJet_re {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    (complexJet H w a p).re = jet (realField H) w a p := by
  exact (congrFun (directional_clm Complex.reCLM (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p).symm

lemma complexJet_im {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    (complexJet H w a p).im = jet (imagField H) w a p := by
  exact (congrFun (directional_clm Complex.imCLM (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p).symm

lemma complexJet_decompose {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    complexJet H w a p = (jet (realField H) w a p : ℂ) +
      Complex.I * (jet (imagField H) w a p : ℂ) := by
  rw [← complexJet_re hH, ← complexJet_im hH]
  exact Complex.ext (by simp) (by simp)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexFirstVariation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex polynomial first variation is exactly the complexification
of the actual real differential. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma evalComplex_sumList {ι : Type*} (l : List ι) (f : ι → MixedExpression)
    (G : Base → Space) (J : JetData) (z : Base × ℝ) :
    (sumList l f).evalComplex G J z = (l.map (fun i => (f i).evalComplex G J z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, evalComplex, List.map_cons, List.sum_cons, ih]

lemma evalComplex_ofExpression (e : Expression) (G : Base → Space)
    (H : Base → Fin 4 → ℂ) (z : Base × ℝ) :
    (ofExpression e).evalComplex G (complexDirectionData G H) z = (e.eval G z : ℂ) := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [ofExpression, evalComplex, complexDirectionData, Fin.cases_zero,
      ih, Expression.eval, Complex.ofReal_mul]
  | add e f ihe ihf => simp only [ofExpression, evalComplex, ihe, ihf, Expression.eval, Complex.ofReal_add]

lemma complex_coefficient_variation (c : LowJet × ℝ → ℝ) (G : Base → Space)
    (H : Base → Fin 4 → ℂ) (z : Base × ℝ) :
    ((coeff c).differentiate 0).evalComplex G (complexDirectionData G H) z =
      ∑ i : Fin 7 × Fin 4, complexJet H (lowWord i.1) i.2 z.1 *
        (coefficientDerivative c i (lowJet G z.1, z.2) : ℂ) := by
  simp only [differentiate, evalComplex_sumList, evalComplex, complexDirectionData,
    Fin.cases_succ, ↓reduceIte]
  exact Finset.sum_map_toList _ _

private lemma complex_sum_decompose {ι : Type*} [Fintype ι] (a b d : ι → ℝ) :
    (∑ i, ((a i : ℂ) + Complex.I * (b i : ℂ)) * (d i : ℂ)) =
      (∑ i, a i * d i : ℝ) + Complex.I * (∑ i, b i * d i : ℝ) := by
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]

/-- This identity identifies the algebraic complex evaluation with the
actual real differential on the real and imaginary parts separately. -/
theorem complex_first_variation (e : Expression) (G : Base → Space)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    ((ofExpression e).differentiate 0).evalComplex G (complexDirectionData G H) z =
      (e.variation G (realField H) z : ℂ) +
        Complex.I * (e.variation G (imagField H) z : ℂ) := by
  induction e with
  | coeff c =>
    rw [ofExpression, complex_coefficient_variation]
    simp_rw [complexJet_decompose hH]
    rw [complex_sum_decompose]
    rw [Expression.variation, Expression.variation,
      coefficient_variation_sum, coefficient_variation_sum]
    rfl
  | atom w a e ih =>
    simp only [ofExpression, differentiate, ↓reduceIte, evalComplex,
      complexDirectionData, Fin.cases_zero, Fin.cases_succ, evalComplex_ofExpression, ih,
      Expression.variation]
    rw [complexJet_decompose hH]
    push_cast
    ring
  | add e f ihe ihf =>
    simp only [ofExpression, differentiate, evalComplex, ihe, ihf, Expression.variation,
      Complex.ofReal_add]
    ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ComplexifiedPolynomialOperator
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complexification of the actual supported polynomial linearization. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

namespace Expression

/-- The bundled operator is the same complex first variation whose
conjugated finite-jet estimates were proved above. -/
lemma complexVariationLM_apply {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (t : ℝ)
    (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    complexVariationLM hO hU he hG hQ K hKU t H p =
      ((ofExpression e).differentiate 0).evalComplex G (complexDirectionData G H) (p, t) := by
  change (e.variation G (realField H) (p, t) : ℂ) +
    Complex.I * (e.variation G (imagField H) (p, t) : ℂ) = _
  exact (complex_first_variation e G H.contDiff (p, t)).symm

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ConjugatedPolynomialOperator
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The oscillatory estimates apply to the actual conjugated polynomial
linearization on supported smooth fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma single_oscillatoryData (G : Base → Space) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ : ℝ) :
    oscillatoryData G (singlePhase φ) (singleDirection H) τ =
      complexDirectionData G (fun p => phase τ φ p • H p) := by
  funext i w a p
  fin_cases i
  · rfl
  · rfl
  · change iteratedDirectional (w.map coordinateVector)
      (fun q => phase τ (fun _ => 0) q * (0 : ℂ)) p = 0
    simp only [mul_zero, iteratedDirectional_zero]
  · change iteratedDirectional (w.map coordinateVector)
      (fun q => phase τ (fun _ => 0) q * (0 : ℂ)) p = 0
    simp only [mul_zero, iteratedDirectional_zero]

namespace Expression

lemma conjugatedVariationLM_apply {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (τ t : ℝ) (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    conjugatedVariationLM hO hU he hG hQ K hKU hφ τ t H p =
      conjugatedVariation e G (singlePhase φ) (singleDirection H) τ 0 (p, t) := by
  change phase τ (fun q => -φ q) p *
    complexVariationLM hO hU he hG hQ K hKU t (phaseLM K hφ τ H) p = _
  rw [complexVariationLM_apply, phase_neg_inv]
  change (phase τ φ p)⁻¹ * ((ofExpression e).differentiate 0).evalComplex G
    (complexDirectionData G (fun q => phase τ φ q • H q)) (p, t) = _
  rw [← single_oscillatoryData]
  simp only [conjugatedVariation, phaseProduct, singlePhase, Matrix.cons_val_zero]
  simp only [show ¬ (1 : Fin 3) ≤ 0 by decide, show ¬ (2 : Fin 3) ≤ 0 by decide,
    ↓reduceIte, mul_one]
  rfl

end Expression
end ClosedSurfaceR4.JetPolynomial

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationOperator
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugated derivative of the actual finite polynomial perturbation,
with its fixed scale loss and linear dependence on epsilon. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

lemma conjugatedLM_apply (hO : IsOpen O) (hU : IsOpen U) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ)
    (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    conjugatedLM hO hU P hP hG hQ K hKU hφ τ ε t H p =
      conjugated P ε G (singlePhase φ) (singleDirection H) τ 0 (p, t) := by
  simp only [conjugatedLM, LinearMap.sum_apply, LinearMap.smul_apply]
  have hsum := congrArg (fun f : Base → ℂ => f p)
    (map_sum (FunLike.coeAddMonoidHom (SupportedField (F := ℂ) K) Base ℂ)
      (fun l : Fin n => ε ^ (l.val + 1) •
        (P l).conjugatedVariationLM hO hU (hP l) hG hQ K hKU hφ τ t H) Finset.univ)
  simp only [FunLike.coeAddMonoidHom_apply, Finset.sum_apply] at hsum
  rw [hsum]
  simp only [smul_apply, Expression.conjugatedVariationLM_apply, conjugated]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearModes
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the real polynomial linearization from the complex conjugated
operator. This is the realization identity needed by forced cancellation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma first_variation_phase_factor (e : Expression) (G : Base → Space)
    (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ : ℝ) (z : Base × ℝ) :
    phase τ φ z.1 * conjugatedVariation e G (singlePhase φ) (singleDirection H) τ 0 z =
      ((ofExpression e).differentiate 0).evalComplex G
        (complexDirectionData G (fun p => phase τ φ p • H p)) z := by
  have hp : phaseProduct (singlePhase φ) τ 0 z.1 = phase τ φ z.1 := by
    simp [phaseProduct, singlePhase]
  rw [conjugatedVariation, hp, ← mul_assoc,
    mul_inv_cancel₀ (show phase τ φ z.1 ≠ 0 from Complex.exp_ne_zero _), one_mul,
    single_oscillatoryData]
  rfl

namespace Perturbation

lemma linearized_real_mode {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H) (τ t : ℝ) (p : Base) :
    linearized P ε G (realField (fun x => phase τ φ x • H x)) t p =
      (phase τ φ p * conjugated P ε G (singlePhase φ) (singleDirection H) τ 0 (p,t)).re := by
  have hs : ContDiff ℝ ∞ (fun x => phase τ φ x • H x) := (phase_smooth hφ τ).smul hH
  unfold linearized conjugated
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [show phase τ φ p * (ε ^ (l.val + 1) •
      conjugatedVariation (P l) G (singlePhase φ) (singleDirection H) τ 0 (p,t)) =
      ε ^ (l.val + 1) • (phase τ φ p *
        conjugatedVariation (P l) G (singlePhase φ) (singleDirection H) τ 0 (p,t)) by
    simp only [Complex.real_smul]; ring]
  rw [first_variation_phase_factor (P l) G φ H τ (p,t), complex_first_variation (P l) G hs]
  simp [-Complex.ofReal_pow]

lemma conjugatedLM_realization {n : ℕ} {O : Set LowJet} {U : Set Base}
    {G : Base → Space} (hO : IsOpen O) (hU : IsOpen U) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ)
    (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    linearized P ε G (realField (fun x => phase τ φ x • H x)) t p =
      (phase τ φ p * conjugatedLM hO hU P hP hG hQ K hKU hφ τ ε t H p).re := by
  rw [conjugatedLM_apply]
  exact linearized_real_mode P ε G hφ H.contDiff τ t p

end Perturbation
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

/-- Every prescribed finite residual accuracy is achieved by the actual
geometric correction algorithm. Only the derivative budget grows. -/
theorem perturbedMode_residual_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (f : SupportedField (F := Fin 3 → ℂ) K) (q m : ℕ) :
    let η := τ / s + ε / τ ^ p
    let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
    supportedWeightedSeminorm K s m
      (((conjugatedDLM τ hG K).restrictScalars ℝ + R)
        (perturbedMode τ hG h K hKU R f q) - f) ≤
      η ^ q * FiniteParametrix.boundProfile (L + 1) κ
        (fun r => η * κ r * supportedWeightedSeminorm K s (r + (L + 1)) f) q m := by
  dsimp only
  let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hκ : ∀ r, 0 ≤ κ r := fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)
  have hd := perturbed_geometric_defect_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR
  exact FiniteParametrix.residual_bound
    ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) f
    (forcedModeLM τ hG h K hKU 0 f) (fun r => supportedWeightedSeminorm K s r)
    (L + 1) κ _ hη hκ hd (fun r => hd r f) q m

end ClosedSurfaceR4.SmallModes

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateQuadraticExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the polynomial quadratic expansion into the same coordinates
and phase labels as the metric quadratic expansion. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ModulatedJets

lemma coordinate_phase_value (τ : ℝ) (φ : Base → ℝ) (x : Base) :
    QuadraticMean.phase (φ x / τ) = phase τ φ x := by
  simp only [QuadraticMean.phase, phase, Complex.ofReal_div]
  congr 1
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for tensor transport through phase charts. The
change of chart changes constants but introduces no scale loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma tensorChartBudget_nonneg (m : ℕ) {J D : ℝ} (hJ : 0 ≤ J) (hD : 0 ≤ D) :
    0 ≤ tensorChartBudget m J D := by unfold tensorChartBudget; positivity

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ArbitraryPhasePolynomial
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial conjugation estimate and its real realization for an
arbitrary smooth phase, before changing to a first-coordinate chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

lemma phaseCoordinatePolynomialOperator_realization
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (modeSupport K)) :
    coordinateRealLinearized P ε G (QuadraticMean.displacement τ (coordinatePhase φ) Z) 0 =
      QuadraticMean.displacement τ (coordinatePhase φ)
        (phaseCoordinatePolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε Z) := by
  let H := (supportedCoordinateEquiv planeCoordinateIsometry K).symm Z
  have hf : QuadraticMean.displacement τ (coordinatePhase φ) Z ∘ planeCoordinateIsometry =
      realField (fun x => phase τ φ x • H x) := by
    funext x a
    change (QuadraticMean.phase (φ (planeCoordinateIsometry.symm (planeCoordinateIsometry x)) / τ) *
      Z (planeCoordinateIsometry x) a).re = (phase τ φ x * H x a).re
    rw [planeCoordinateIsometry.symm_apply_apply, coordinate_phase_value]
    rfl
  funext p k
  change linearized (P k) ε G
      (QuadraticMean.displacement τ (coordinatePhase φ) Z ∘ planeCoordinateIsometry) 0
      (planeCoordinateIsometry.symm p) =
    (QuadraticMean.phase (φ (planeCoordinateIsometry.symm p) / τ) *
      conjugatedLM hO hU (P k) (hP k) hG hQ K hKU hφ τ ε 0 H (planeCoordinateIsometry.symm p)).re
  rw [coordinate_phase_value, hf, conjugatedLM_realization hO hU (P k) (hP k) hG hQ K hKU hφ τ ε 0 H]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartRealization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local-coordinate realization of the polynomial phase operator.
The operator is transported, so no transformed-polynomial assumption is used. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

lemma chart_displacement_pull (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts SmallModes.Base)
    (hK : (K : Set SmallModes.Base) ⊆ e.source) (φ : SmallModes.Base → ℝ)
    (hphase : ∀ x ∈ e.source, (e x).1 = φ x) (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK))
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    QuadraticMean.displacement τ φ (chartPull e he K hK Z) (e.symm y) =
      RealModes.realOsc τ Z y := by
  rw [RealModes.realOsc_eq_displacement]
  have hp := hphase (e.symm y) (e.map_target hy)
  rw [e.right_inv hy] at hp
  have hz : chartPull e he K hK Z (e.symm y) = Z y := by
    rw [chartPull_apply, Set.indicator_of_mem (e.map_target hy)]
    simp only [Function.comp_apply, e.right_inv hy]
  simp only [QuadraticMean.displacement, ← hp, hz]

lemma phaseChartPolynomialOperator_realization
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e (modeSupport K) hKe))
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    let X := QuadraticMean.displacement τ (coordinatePhase φ) (chartPull e he (modeSupport K) hKe Z)
    pullbackField e.symm y (coordinateRealLinearized P ε G X 0 (e.symm y)) =
      RealModes.realOsc τ (phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe Z) y := by
  dsimp only
  rw [phaseCoordinatePolynomialOperator_realization hO hU P hP hG hQ K hKU hφ τ ε]
  have hp := hphase (e.symm y) (e.map_target hy)
  rw [e.right_inv hy] at hp
  rw [RealModes.realOsc_eq_displacement]
  change pullbackField e.symm y (QuadraticMean.realMode (coordinatePhase φ (e.symm y) / τ)
      ((phaseCoordinatePolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε)
        (chartPull e he (modeSupport K) hKe Z) (e.symm y))) =
    QuadraticMean.realMode (y.1 / τ)
      (tensorChartPush e hi (modeSupport K) hKe
        ((phaseCoordinatePolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε)
          (chartPull e he (modeSupport K) hKe Z)) y)
  rw [tensorChartPush_apply, Set.indicator_of_mem hy, ← hp]
  exact (realMode_complexPullback (fderiv ℝ e.symm y) _ _).symm

lemma chart_metric_linearized (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)
    {F : RealModes.RField 4} (hF : ContDiff ℝ ∞ F) {φ : SmallModes.Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hphase : ∀ x ∈ e.source, (e x).1 = φ x) (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK))
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    let X := QuadraticMean.displacement τ φ (chartPull e he K hK Z)
    pullbackField e.symm y (RealModes.realLinearizedTensor F X (e.symm y)) =
      RealModes.realLinearizedTensor (F ∘ e.symm) (RealModes.realOsc τ Z) y := by
  let X := QuadraticMean.displacement τ φ (chartPull e he K hK Z)
  have hX : ContDiff ℝ ∞ X := contDiffOn_univ.mp
    (RealModes.contDiffOn_displacement hφ.contDiffOn (chartPull e he K hK Z).contDiff.contDiffOn τ)
  have hid : X ∘ e.symm =ᶠ[nhds y] RealModes.realOsc τ Z := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact chart_displacement_pull e he K hK φ hphase τ Z hz
  have hc := RealModes.realLinearizedTensor_comp (hF.differentiable (by simp) _)
    (hX.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) ((hi.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  exact hc.symm.trans (RealModes.realLinearizedTensor_congr_right hid)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartFullLinearization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact full conjugated linear operator in a local phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes

lemma realOsc_add_value {n : ℕ} (τ : ℝ) (Z W : SmallModes.Field n) (p : SmallModes.Base) :
    realOsc τ (Z + W) p = realOsc τ Z p + realOsc τ W p := by
  ext k
  simp [realOsc, SmallModes.oscillate, QuadraticMean.realPart, mul_add]

lemma realLinearized_conjugated_value {n : ℕ} {F : RField n} {Z : SmallModes.Field n}
    {p : SmallModes.Base} (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) :
    realLinearizedTensor F (realOsc τ Z) p =
      realOsc τ (SmallModes.conjugatedD τ (fun q => complexify (F q)) Z) p := by
  have hr := realLinearized_residual hF hZ τ (0 : SmallModes.Tensor)
  have hz : realOsc τ (0 : SmallModes.Tensor) p = 0 := by
    ext k
    simp [realOsc, SmallModes.oscillate, QuadraticMean.realPart]
  rw [hz, sub_zero] at hr
  have he : SmallModes.residual τ (fun q => complexify (F q)) 0 Z =
      SmallModes.conjugatedD τ (fun q => complexify (F q)) Z := by
    funext q
    simp only [SmallModes.residual, Pi.zero_apply, sub_zero]
  rwa [he] at hr

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean
variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

theorem phaseChartFullLinearization
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e (modeSupport K) hKe))
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    let X := QuadraticMean.displacement τ (coordinatePhase φ) (chartPull e he (modeSupport K) hKe Z)
    let F := (G ∘ planeCoordinateIsometry.symm) ∘ e.symm
    let R := phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe
    pullbackField e.symm y (coordinateFullLinearized P ε G X (e.symm y)) =
      RealModes.realOsc τ (SmallModes.conjugatedD τ (fun p => RealModes.complexify (F p)) Z + (R Z : SmallModes.Tensor)) y := by
  dsimp only
  change pullbackField e.symm y
    (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) _ (e.symm y) +
      coordinateRealLinearized P ε G _ 0 (e.symm y)) = _
  rw [map_add, chart_metric_linearized e he hi (modeSupport K) hKe
    (hG.comp planeCoordinateIsometry.symm.contDiff)
    (hφ.comp planeCoordinateIsometry.symm.contDiff) hphase τ Z hy,
    phaseChartPolynomialOperator_realization hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe hphase Z hy]
  have hF : DifferentiableAt ℝ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) y :=
    ((hG.comp planeCoordinateIsometry.symm.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).comp y
      ((hi.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  rw [RealModes.realLinearized_conjugated_value hF (Z.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) y) τ,
    RealModes.realOsc_add_value]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartDisplacement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real displacements and tensor targets transported through a permitted
phase chart, with their actual support and size estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)
    (φ : SmallModes.Base → ℝ) (hphase : ∀ x ∈ e.source, (e x).1 = φ x)

include hphase in
lemma chart_displacement_eq_indicator (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK)) :
    QuadraticMean.displacement τ φ (chartPull e he K hK Z) =
      e.source.indicator (RealModes.realOsc τ Z ∘ e) := by
  funext x
  by_cases hx : x ∈ e.source
  · rw [Set.indicator_of_mem hx]
    change QuadraticMean.displacement τ φ (chartPull e he K hK Z) x = RealModes.realOsc τ Z (e x)
    have hh := chart_displacement_pull e he K hK φ hphase τ Z (e.map_source hx)
    simpa only [e.left_inv hx] using hh
  · rw [Set.indicator_of_notMem hx]
    apply RealModes.displacement_zero_value
    rw [chartPull_apply, Set.indicator_of_notMem hx]

lemma chart_displacement_smooth_support (hφ : ContDiff ℝ ∞ φ) (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK)) :
    ContDiff ℝ ∞ (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) ∧
      tsupport (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) ⊆ K := by
  refine ⟨contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn
    (chartPull e he K hK Z).contDiff.contDiffOn τ), ?_⟩
  apply closure_minimal _ K.isCompact.isClosed
  intro x hx
  by_contra hn
  exact hx (RealModes.displacement_zero_value τ φ ((chartPull e he K hK Z).zero_on_compl hn))

include hphase in
lemma chart_displacement_bound {s : ℝ≥0} {τ C J : ℝ} {m : ℕ}
    (_hs : 0 < (s : ℝ)) (hτ : 0 < τ) (hτs : τ ≤ s) (hτ1 : τ ≤ 1)
    (hC : 0 ≤ C) (hJ : 1 ≤ J)
    (hcoords : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK))
    (hZ : supportedWeightedSeminorm (chartSupport e K hK) s m Z ≤ C) :
    WeightedBound Set.univ τ m ((m.factorial : ℝ) * (2 ^ m * C) * J ^ m)
      (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) := by
  have hr := RealModes.weighted_realOsc isOpen_univ hτ hτs hC Z.contDiff.contDiffOn
    ((weightedBound_of_supportedSeminorm s m Z).mono_const hZ)
  have hrs : ContDiffOn ℝ ∞ (RealModes.realOsc τ Z) e.target :=
    RealModes.contDiffOn_realOsc Z.contDiff.contDiffOn τ
  have hc := (hr.restrict_open e.open_target).comp_coordinates e.open_source.uniqueDiffOn
    e.open_target.uniqueDiffOn hτ hτ1 hJ (by positivity) he hrs (fun _ hx => e.map_source hx) hcoords
  have hz : ∀ x ∈ e.source, x ∉ (K : Set SmallModes.Base) → RealModes.realOsc τ Z (e x) = 0 := by
    intro x hx hn
    rw [RealModes.realOsc_eq_displacement]
    exact RealModes.displacement_zero_value τ Prod.fst (chartPull_zero e K hK Z x hx hn)
  rw [chart_displacement_eq_indicator e he K hK φ hphase]
  exact hc.indicator_of_support e.open_source K.isCompact.isClosed hK (by positivity) hz

include hphase in
lemma chart_forcing_realization (τ : ℝ) (f : SupportedField (F := ComplexTensor) K)
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    pullbackField e.symm y (QuadraticMean.displacement τ φ f (e.symm y)) =
      RealModes.realOsc τ (tensorChartPush e hi K hK f) y := by
  have hp := hphase (e.symm y) (e.map_target hy)
  rw [e.right_inv hy] at hp
  rw [RealModes.realOsc_eq_displacement]
  change pullbackField e.symm y (QuadraticMean.realMode (φ (e.symm y) / τ) (f (e.symm y))) =
    QuadraticMean.realMode (y.1 / τ) (tensorChartPush e hi K hK f y)
  rw [tensorChartPush_apply, Set.indicator_of_mem hy, ← hp]
  exact (realMode_complexPullback (fderiv ℝ e.symm y) _ _).symm

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartResidualBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a residual estimate back through its phase chart and extend
it globally using the already established compact support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open WeightedEstimates

lemma real_pullbackField_inverse {χ e : SmallModes.Base → SmallModes.Base} {x : SmallModes.Base}
    (hχ : DifferentiableAt ℝ χ x) (he : DifferentiableAt ℝ e (χ x))
    (hi : e ∘ χ =ᶠ[nhds x] id) (A : Tensor) :
    pullbackField χ x (pullbackField e (χ x) A) = A := by
  have hc := congrArg QuadraticMean.realPart
    (complexPullbackField_inverse hχ he hi (RealModes.complexify A))
  simpa only [complexPullbackField, realPart_complexPullback, realPart_complexify, pullbackField] using hc

lemma weighted_residual_from_chart
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {R : SmallModes.Base → Tensor} (hRs : tsupport R ⊆ e.source)
    {τ C J D : ℝ} {m : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hC : 0 ≤ C) (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hcoords : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.source τ m D (SmallModes.coordDeriv v e))
    (hsm : ContDiffOn ℝ ∞ (fun y => pullbackField e.symm y (R (e.symm y))) e.target)
    (hb : WeightedBound e.target τ m C (fun y => pullbackField e.symm y (R (e.symm y)))) :
    WeightedBound Set.univ τ m (JetPolynomial.tensorChartBudget m J D * C) R := by
  have hc := hb.comp_coordinates e.open_source.uniqueDiffOn e.open_target.uniqueDiffOn hτ hτ1 hJ hC
    he hsm (fun _ hx => e.map_source hx) hcoords
  have hp := weighted_pullbackField_apply e.open_source hτ (by positivity) hD
    (hsm.comp he (fun _ hx => e.map_source hx)) he hc hfield
  have hid (x : SmallModes.Base) (hx : x ∈ e.source) :
      pullbackField e x (pullbackField e.symm (e x) (R (e.symm (e x)))) = R x := by
    rw [e.left_inv hx]
    apply real_pullbackField_inverse
    · exact (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · exact (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · filter_upwards [e.open_source.mem_nhds hx] with z hz using e.left_inv hz
  have hl : WeightedBound e.source τ m (JetPolynomial.tensorChartBudget m J D * C) R := by
    have hh := hp.congr (fun x hx => (hid x hx).symm)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    unfold JetPolynomial.tensorChartBudget
    ring
  exact hl.extend_support e.open_source hRs
    (mul_nonneg (JetPolynomial.tensorChartBudget_nonneg m (zero_le_one.trans hJ) hD) hC)

end ClosedSurfaceR4.PhaseMean

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

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PerturbedForcedSize
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same finite forced correction has a scale-independent amplitude
budget. Only the finite number of required input derivatives grows. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

lemma forcedModeBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ)
    (hB : ∀ m, 0 ≤ B m) (q m : ℕ) : 0 ≤ forcedModeBudget n L B D q m := by
  apply add_nonneg (initialConstant_nonneg _ _ (hB m))
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (initialConstant_nonneg _ _ (hB m))
  exact FiniteParametrix.boundProfile_nonneg
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)) _ _

theorem perturbedMode_size (τ : ℝ) {n : ℕ} {G : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (f : SupportedField (F := Fin 3 → ℂ) K) (q m : ℕ) :
    supportedWeightedSeminorm K s m (perturbedMode τ hG h K hKU R f q) ≤
      forcedModeBudget n L B D q m *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) f := by
  let A := (conjugatedDLM τ hG K).restrictScalars ℝ + R
  let S := (forcedModeLM τ hG h K hKU 0).restrictScalars ℝ
  let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
  let N := fun r => κ r * supportedWeightedSeminorm K s (r + (L + 1)) f
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hκ : ∀ r, 0 ≤ κ r := fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)
  have hd := perturbed_geometric_defect_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR
  have hS : ∀ r g, supportedWeightedSeminorm K s r (S g) ≤
      initialConstant n r (B r) * supportedWeightedSeminorm K s (r + (L + 1)) g := by
    intro r g
    exact (forcedModeLM_zero_bound τ hG h K hKU hτ hs hτs hs1 (hB r) r (hc r) g).trans
      (mul_le_mul_of_nonneg_left (supportedWeightedSeminorm_mono s (by omega) g)
        (initialConstant_nonneg _ _ (hB r)))
  have hdev := FiniteParametrix.improve_sub_initial_small A S f (S f)
    (fun r => supportedWeightedSeminorm K s r) (fun r => supportedWeightedSeminorm K s r)
    (L + 1) κ N (fun r => initialConstant n r (B r)) hη hsmall hκ
    (fun r => mul_nonneg (hκ r) (apply_nonneg _ _))
    (fun r => initialConstant_nonneg _ _ (hB r)) hd hS (by
      intro r
      simpa only [A, S, N, κ, FiniteParametrix.defect, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearMap.id_apply, mul_assoc] using hd r f) q m
  have hsum := finite_deviation_budget K s (L + 1) q m
    (fun r => initialConstant n r (B r)) κ κ
    (fun r => initialConstant_nonneg _ _ (hB r)) hκ hκ f
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range q, initialConstant n m (B m) *
      FiniteParametrix.boundProfile (L + 1) κ N i (m + (L + 1)) := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (initialConstant_nonneg _ _ (hB m))
      (FiniteParametrix.boundProfile_nonneg hκ (fun r => mul_nonneg (hκ r) (apply_nonneg _ _)) _ _)
  have hdev' : supportedWeightedSeminorm K s m
      (perturbedMode τ hG h K hKU R f q - S f) ≤
      (∑ i ∈ Finset.range q, initialConstant n m (B m) *
        FiniteParametrix.boundProfile (L + 1) κ κ i (m + (L + 1))) *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) f := by
    exact hdev.trans ((mul_le_of_le_one_left hsum0 hsmall).trans hsum)
  have hinit : supportedWeightedSeminorm K s m (S f) ≤
      initialConstant n m (B m) * supportedWeightedSeminorm K s
        (m + (q + 1) * (L + 1)) f := (hS m f).trans (mul_le_mul_of_nonneg_left
    (supportedWeightedSeminorm_mono s (by
      have hm := Nat.mul_le_mul_right (L + 1) (show 1 ≤ q + 1 by omega)
      omega) f) (initialConstant_nonneg _ _ (hB m)))
  calc
    _ = supportedWeightedSeminorm K s m
        ((perturbedMode τ hG h K hKU R f q - S f) + S f) := by rw [sub_add_cancel]
    _ ≤ supportedWeightedSeminorm K s m (perturbedMode τ hG h K hKU R f q - S f) +
        supportedWeightedSeminorm K s m (S f) := map_add_le_add _ _ _
    _ ≤ _ := add_le_add hdev' hinit
    _ = _ := by dsimp only [forcedModeBudget, κ] <;> ring

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedForcedMode
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite perturbed correction algorithm applied to an actual local
phase chart, with real displacement, support, size and residual estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

theorem charted_forced_mode
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (hFc : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm))
    (hM : SmallModes.ModeDomain (fun p => RealModes.complexify
      (G (planeCoordinateIsometry.symm (e.symm p)))) e.target)
    {s : ℝ≥0} (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (C D J : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (hD : ∀ m, 0 ≤ D m) (hJ : ∀ m, 1 ≤ J m)
    (hcoords : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m)
    (hc : ∀ m, SmallModes.ReconstructionCoefficientBound
      (fun p => RealModes.complexify (G (planeCoordinateIsometry.symm (e.symm p))))
      e.target s (m + 1) (C m))
    (hR : ∀ m Z, supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s m
      (phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe Z) ≤
      ε / τ ^ tensorLoss P * D m *
        supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s (m + tensorOrder P) Z)
    (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q : ℕ) :
    let Kc := chartSupport e (modeSupport K) hKe
    let fc := tensorChartPush e hi (modeSupport K) hKe f
    let κ := fun m => max (SmallModes.errorConstant m (C m))
      (D m * SmallModes.initialConstant 4 (m + tensorOrder P) (C (m + tensorOrder P)))
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
      ContDiffOn ℝ ∞ (fun y => pullbackField e.symm y
        (coordinateFullLinearized P ε G X (e.symm y) +
          QuadraticMean.displacement τ (coordinatePhase φ) f (e.symm y))) e.target ∧
      (∀ m, WeightedBound Set.univ τ m
        ((m.factorial : ℝ) * (2 ^ m * (SmallModes.forcedModeBudget 4 (tensorOrder P) C D q m *
          supportedWeightedSeminorm Kc s (m + (q + 1) * (tensorOrder P + 1)) fc)) * J m ^ m) X) ∧
      (∀ m, WeightedBound e.target τ m
        (2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
          FiniteParametrix.boundProfile (tensorOrder P + 1) κ
            (fun r => κ r * supportedWeightedSeminorm Kc s (r + (tensorOrder P + 1)) fc) q m))
        (fun y => pullbackField e.symm y
          (coordinateFullLinearized P ε G X (e.symm y) +
            QuadraticMean.displacement τ (coordinatePhase φ) f (e.symm y)))) := by
  let Kc := chartSupport e (modeSupport K) hKe
  let fc := tensorChartPush e hi (modeSupport K) hKe f
  let Fc := (G ∘ planeCoordinateIsometry.symm) ∘ e.symm
  let Gc := fun p => RealModes.complexify (Fc p)
  have hGc : ContDiff ℝ ∞ Gc := (RealModes.complexifyCLM 4).contDiff.comp hFc
  let R := phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe
  let Z := SmallModes.perturbedMode τ hGc hM Kc (chartSupport_subset e (modeSupport K) hKe) R (-fc) q
  let A := (SmallModes.conjugatedDLM τ hGc Kc).restrictScalars ℝ + R
  let W := A Z + fc
  let X := QuadraticMean.displacement τ (coordinatePhase φ) (chartPull e he (modeSupport K) hKe Z)
  have hx := chart_displacement_smooth_support e he (modeSupport K) hKe (coordinatePhase φ)
    (hφ.comp planeCoordinateIsometry.symm.contDiff) τ Z
  have hid (y : SmallModes.Base) (hy : y ∈ e.target) :
      pullbackField e.symm y (coordinateFullLinearized P ε G X (e.symm y) +
        QuadraticMean.displacement τ (coordinatePhase φ) f (e.symm y)) = RealModes.realOsc τ W y := by
    rw [map_add, phaseChartFullLinearization hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe hphase Z hy,
      chart_forcing_realization e hi (modeSupport K) hKe (coordinatePhase φ) hphase τ f hy]
    change RealModes.realOsc τ _ y + RealModes.realOsc τ fc y = RealModes.realOsc τ W y
    rw [← RealModes.realOsc_add_value]
    rfl
  dsimp only
  refine ⟨X,hx.1,hx.2,?_,?_,?_⟩
  · exact (RealModes.contDiffOn_realOsc W.contDiff.contDiffOn τ).congr hid
  · intro m
    have hb := SmallModes.perturbedMode_size τ hGc hM Kc (chartSupport_subset e (modeSupport K) hKe)
      hτ hs hτs hs1 hε hsmall C D hC hD hc R hR (-fc) q m
    simp only [map_neg_eq_map] at hb
    exact chart_displacement_bound e he (modeSupport K) hKe (coordinatePhase φ) hphase
      hs hτ hτs (hτs.trans (show (s : ℝ) ≤ 1 from hs1))
      (mul_nonneg (SmallModes.forcedModeBudget_nonneg 4 (tensorOrder P) C D hC q m) (apply_nonneg _ _))
      (hJ m) (hcoords m) Z hb
  · intro m
    let κ := fun r => max (SmallModes.errorConstant r (C r))
      (D r * SmallModes.initialConstant 4 (r + tensorOrder P) (C (r + tensorOrder P)))
    let E := (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      FiniteParametrix.boundProfile (tensorOrder P + 1) κ
        (fun r => κ r * supportedWeightedSeminorm Kc s (r + (tensorOrder P + 1)) fc) q m
    have hr := SmallModes.perturbedMode_residual_bound τ hGc hM Kc (chartSupport_subset e (modeSupport K) hKe)
      hτ hs hτs hs1 hε C D hC hD hc R hR (-fc) q m
    have hb : supportedWeightedSeminorm Kc s m W ≤ E := by
      dsimp only at hr
      simp only [map_neg_eq_map, sub_neg_eq_add, mul_assoc] at hr
      rw [FiniteParametrix.boundProfile_const_mul] at hr
      simpa only [W,Z,A,E,κ,pow_succ,mul_assoc] using hr
    have hE : 0 ≤ E := (apply_nonneg _ _).trans hb
    have hw := RealModes.weighted_realOsc isOpen_univ hτ hτs hE W.contDiff.contDiffOn
      ((weightedBound_of_supportedSeminorm s m W).mono_const hb)
    apply (hw.restrict_open e.open_target).congr
    intro y hy
    exact hid y hy

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full linearized metric perturbation preserves the support of its
varying field, including every higher-jet polynomial term. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero_of_notMem {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X : RealModes.RField 4} {p : SmallModes.Base} (hp : p ∉ tsupport X) :
    coordinateFullLinearized P ε G X p = 0 := by
  have hx : X =ᶠ[nhds p] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hp
  have hc : (X ∘ planeCoordinateIsometry) =ᶠ[nhds (planeCoordinateIsometry.symm p)] (fun _ => 0) := by
    apply hx.comp_tendsto
    simpa only [planeCoordinateIsometry.apply_symm_apply] using
      (planeCoordinateIsometry.continuous.continuousAt (x := planeCoordinateIsometry.symm p)).tendsto
  have hn : planeCoordinateIsometry.symm p ∉ tsupport (X ∘ planeCoordinateIsometry) :=
    notMem_tsupport_iff_eventuallyEq.mpr hc
  have hm : RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X p = 0 := by
    rw [RealModes.realLinearizedTensor_congr_right hx, RealModes.realLinearizedTensor_zero_right]
  funext k
  simp only [coordinateFullLinearized, Pi.add_apply, hm, Pi.zero_apply, zero_add,
    coordinateRealLinearized, linearized]
  apply Finset.sum_eq_zero
  intro l _
  rw [(P k l).variation_zero_of_notMem G hn 0, mul_zero]

lemma fullLinearized_residual_tsupport {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X : RealModes.RField 4} {f : SmallModes.Tensor} {S : Set SmallModes.Base}
    (hS : IsClosed S) (hX : tsupport X ⊆ S) (hf : tsupport f ⊆ S)
    (τ : ℝ) (φ : SmallModes.Base → ℝ) :
    tsupport (fun p => coordinateFullLinearized P ε G X p + QuadraticMean.displacement τ φ f p) ⊆ S := by
  apply closure_minimal _ hS
  intro p hp
  by_contra hn
  apply hp
  change coordinateFullLinearized P ε G X p + QuadraticMean.displacement τ φ f p = 0
  rw [coordinateFullLinearized_zero_of_notMem P ε G (fun hx => hn (hX hx)),
    RealModes.displacement_zero_value τ φ (image_eq_zero_of_notMem_tsupport (fun hx => hn (hf hx))),
    add_zero]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalChartedForcedMode
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global residual estimates for the actual forced correction constructed
in a local phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean
variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

theorem global_charted_forced_mode
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (hFc : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm))
    (hM : SmallModes.ModeDomain (fun p => RealModes.complexify
      (G (planeCoordinateIsometry.symm (e.symm p)))) e.target)
    {s : ℝ≥0} (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (C D J : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (hD : ∀ m, 0 ≤ D m) (hJ : ∀ m, 1 ≤ J m)
    (hcoords : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m)
    (hc : ∀ m, SmallModes.ReconstructionCoefficientBound
      (fun p => RealModes.complexify (G (planeCoordinateIsometry.symm (e.symm p))))
      e.target s (m + 1) (C m))
    (hR : ∀ m Z, supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s m
      (phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe Z) ≤
      ε / τ ^ tensorLoss P * D m *
        supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s (m + tensorOrder P) Z)
    (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q : ℕ) :
    let Kc := chartSupport e (modeSupport K) hKe
    let fc := tensorChartPush e hi (modeSupport K) hKe f
    let κ := fun m => max (SmallModes.errorConstant m (C m))
      (D m * SmallModes.initialConstant 4 (m + tensorOrder P) (C (m + tensorOrder P)))
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m
        ((m.factorial : ℝ) * (2 ^ m * (SmallModes.forcedModeBudget 4 (tensorOrder P) C D q m *
          supportedWeightedSeminorm Kc s (m + (q + 1) * (tensorOrder P + 1)) fc)) * J m ^ m) X) ∧
      (∀ m, WeightedBound Set.univ τ m
        (tensorChartBudget m (J m) (J (m + 1)) *
          (2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
            FiniteParametrix.boundProfile (tensorOrder P + 1) κ
              (fun r => κ r * supportedWeightedSeminorm Kc s (r + (tensorOrder P + 1)) fc) q m)))
        (fun x => coordinateFullLinearized P ε G X x + QuadraticMean.displacement τ (coordinatePhase φ) f x)) := by
  obtain ⟨X,hX,hsp,hsm,hsize,hres⟩ := charted_forced_mode hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe
    hphase hFc hM hτ hs hτs hs1 hε hsmall C D J hC hD hJ hcoords hc hR f q
  dsimp only
  refine ⟨X,hX,hsp,hsize,?_⟩
  intro m
  let Kc := chartSupport e (modeSupport K) hKe
  let fc := tensorChartPush e hi (modeSupport K) hKe f
  let κ := fun r => max (SmallModes.errorConstant r (C r))
    (D r * SmallModes.initialConstant 4 (r + tensorOrder P) (C (r + tensorOrder P)))
  have hκ (r : ℕ) : 0 ≤ κ r := (SmallModes.errorConstant_nonneg r (hC r)).trans (le_max_left _ _)
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have herror : 0 ≤ 2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      FiniteParametrix.boundProfile (tensorOrder P + 1) κ
        (fun r => κ r * supportedWeightedSeminorm Kc s (r + (tensorOrder P + 1)) fc) q m) :=
    mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hη _)
      (FiniteParametrix.boundProfile_nonneg hκ (fun r => mul_nonneg (hκ r) (apply_nonneg _ _)) q m))
  have hsupp := (fullLinearized_residual_tsupport P ε G (modeSupport K).isCompact.isClosed hsp
    f.tsupport_subset τ (coordinatePhase φ)).trans hKe
  have hτ1 : τ ≤ 1 := hτs.trans (show (s : ℝ) ≤ 1 from hs1)
  have hfield := RealModes.weighted_coordDeriv_of_jets e.open_source he hτ.le hτ1
    (zero_le_one.trans (hJ (m + 1))) (hcoords (m + 1))
  exact weighted_residual_from_chart e he hi hsupp hτ hτ1 herror (hJ m)
    (zero_le_one.trans (hJ (m + 1))) (hcoords m) hfield hsm (hres m)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSolveData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric and quantitative data for the already constructed finite
polynomial phase solver. The operator bound here is supplied by
`phaseChartPolynomialOperator_bounds`; it concerns the actual transported
polynomial derivative. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem exists_solution_oai (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q : ℕ) :
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m (c.size f q m) X) ∧
      (∀ m, WeightedBound Set.univ τ m (c.residual f q m)
        (fun x => coordinateFullLinearized P ε G X x + QuadraticMean.displacement τ (coordinatePhase φ) f x)) := by
  exact global_charted_forced_mode c.openO c.openU P c.smoothP hG c.mapsG K c.supportU
    c.smoothPhase τ ε c.e c.smoothForward c.smoothInverse c.supportChart c.phase c.smoothMap c.domain
    hτ hs hτs hs1 hε hsmall c.C c.D c.J c.nonnegC c.nonnegD c.oneLEJ c.coordinates c.coefficients c.polynomial f q

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution_oai := @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution_oai
