-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:49.143372+00:00
-- url     : https://prove2.me/submissions/fcdffef6-334f-443d-ad38-a1e169b0c5b1

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_PhaseGeometry_anchored_polynomial_grid_phases

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseGrid
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

lemma same_color_difference (q : ℕ) {a b : ℤ}
    (he : (a : ZMod q) = (b : ZMod q)) : (q : ℤ) ∣ a - b := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp [he]

lemma divided_ne_abs_ge {q : ℕ} (hq : 0 < q) {a b : ℤ}
    (he : (q : ℤ) ∣ a - b) (hne : a ≠ b) : (q : ℝ) ≤ |(a : ℝ) - b| := by
  obtain ⟨k, hk⟩ := he
  have hk0 : k ≠ 0 := by intro hz; simp [hz] at hk; omega
  have hn : (1 : ℝ) ≤ |(k : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hk0)
  have heq : (a : ℝ) - b = q * (k : ℝ) := by exact_mod_cast hk
  rw [heq, abs_mul, abs_of_pos (by exact_mod_cast hq : (0 : ℝ) < q)]
  nlinarith [show (0 : ℝ) < q by exact_mod_cast hq]



theorem same_color_disjoint {q : ℕ} (hq : 0 < q) {h R : ℝ} (hh : 0 < h)
    (hR : 2 * R ≤ q) {a b : Index} (hne : a ≠ b)
    (he : color q a = color q b) : Disjoint (cell h R a) (cell h R b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  have hc1 : (a.1 : ZMod q) = (b.1 : ZMod q) := congrArg Prod.fst he
  have hc2 : (a.2 : ZMod q) = (b.2 : ZMod q) := congrArg Prod.snd he
  have hd (i j : ℤ) (hi : |x.1 - h * i| < R * h)
      (hj : |x.1 - h * j| < R * h) : |(i : ℝ) - j| < 2 * R := by
    have ht := abs_sub_le (x.1 - h * i) 0 (x.1 - h * j)
    have heq : (x.1 - h * i) - (x.1 - h * j) = -(h * ((i : ℝ) - j)) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hh] at ht
    simp only [sub_zero, zero_sub, abs_neg] at ht
    nlinarith
  have hdx := hd a.1 b.1 hxa.1 hxb.1
  have hdy : |(a.2 : ℝ) - b.2| < 2 * R := by
    have ht := abs_sub_le (x.2 - h * a.2) 0 (x.2 - h * b.2)
    have heq : (x.2 - h * a.2) - (x.2 - h * b.2) = -(h * ((a.2 : ℝ) - b.2)) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hh] at ht
    simp only [sub_zero, zero_sub, abs_neg] at ht
    nlinarith [hxa.2,hxb.2]
  by_cases ha : a.1 = b.1
  · have hb : a.2 ≠ b.2 := fun hb => hne (Prod.ext ha hb)
    have hy := divided_ne_abs_ge hq (same_color_difference q hc2) hb
    linarith
  · have hx := divided_ne_abs_ge hq (same_color_difference q hc1) ha
    linarith

lemma coordinate_floor_near {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |x - h * (⌊x/h⌋ : ℤ)| < h := by
  have hl := Int.floor_le (x/h)
  have hu := Int.lt_floor_add_one (x/h)
  have hlo : h * (⌊x/h⌋ : ℤ) ≤ x := by
    simpa [mul_comm] using (le_div_iff₀ hh).mp hl
  have hup : x < h * ((⌊x/h⌋ : ℤ) + 1) := by
    have ht := (div_lt_iff₀ hh).mp hu
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

lemma quantize_covers {h : ℝ} (hh : 0 < h) (x : Base) :
    x ∈ cell h 1 (quantize h x) := by
  exact ⟨by simpa [quantize] using coordinate_floor_near hh x.1,
    by simpa [quantize] using coordinate_floor_near hh x.2⟩

lemma floor_mem_interval {A h : ℝ} {N : ℕ} (hh : 0 < h)
    (hN : A/h + 1 ≤ N) {x : ℝ} (hx : |x| ≤ A) :
    ⌊x/h⌋ ∈ Finset.Icc (-(N : ℤ)) N := by
  rw [Finset.mem_Icc]
  have hlo : -A ≤ x := (abs_le.mp hx).1
  have hup : x ≤ A := (abs_le.mp hx).2
  have hfl := Int.floor_le (x/h)
  have hfu := Int.lt_floor_add_one (x/h)
  have hdlo : -A/h ≤ x/h := div_le_div_of_nonneg_right hlo hh.le
  have hdup : x/h ≤ A/h := div_le_div_of_nonneg_right hup hh.le
  constructor
  · have hr : -(N : ℝ) ≤ (⌊x/h⌋ : ℤ) := by rw [neg_div] at hdlo; linarith
    exact_mod_cast hr
  · have hr : ((⌊x/h⌋ : ℤ) : ℝ) ≤ N := by linarith
    exact_mod_cast hr

lemma finite_box_covers {A h : ℝ} {N : ℕ} (hh : 0 < h) (hN : A/h + 1 ≤ N)
    {x : Base} (hx : |x.1| ≤ A ∧ |x.2| ≤ A) :
    ∃ a ∈ box N, x ∈ cell h 1 a := by
  refine ⟨quantize h x, ?_, quantize_covers hh x⟩
  exact Finset.mem_product.mpr ⟨floor_mem_interval hh hN hx.1,
    floor_mem_interval hh hN hx.2⟩

lemma box_card (N : ℕ) : (box N).card = (2 * N + 1)^2 := by
  have hi : (Finset.Icc (-(N : ℤ)) N).card = 2*N+1 := by
    rw [Int.card_Icc]
    omega
  simp [box, hi, pow_two]



lemma box_card_bound {A h : ℝ} {N : ℕ} (hA : 0 ≤ A) (hh : 0 < h) (hh1 : h ≤ 1)
    (hN : (N : ℝ) ≤ A/h + 2) :
    ((box N).card : ℝ) ≤ ((2*A+5)/h)^2 := by
  rw [box_card]
  push_cast
  have hb : 2*(N : ℝ)+1 ≤ (2*A+5)/h := by
    apply (le_div_iff₀ hh).mpr
    have ht : (N : ℝ)*h ≤ A+2*h := by
      have hz := mul_le_mul_of_nonneg_right hN hh.le
      rw [add_mul, div_mul_cancel₀ _ hh.ne'] at hz
      linarith
    nlinarith
  have hlo : 0 ≤ (2*(N : ℝ)+1) := by positivity
  have hhi : 0 ≤ (2*A+5)/h := div_nonneg (by linarith only [hA]) hh.le
  exact (sq_le_sq₀ hlo hhi).mpr hb

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



lemma secondQuadratic_smul {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (w : ℝ) :
    secondQuadratic B (w • v) = w ^ 2 • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodPhases
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma continuous_secondQuadratic {n : ℕ} :
    Continuous (fun z : (Fin 3 → RVec n) × Base => secondQuadratic z.1 z.2) := by
  unfold secondQuadratic
  fun_prop

lemma isOpen_good {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} (hB : Continuous B) (hξ : Continuous ξ) :
    IsOpen {p : X | Good (B p) (ξ p)} := by
  change IsOpen ({p : X | ξ p ≠ 0} ∩
    {p : X | secondQuadratic (B p) (-(ξ p).2, (ξ p).1) ≠ 0})
  apply (isOpen_ne_fun hξ continuous_const).inter
  apply isOpen_ne_fun _ continuous_const
  exact continuous_secondQuadratic.comp (hB.prodMk ((hξ.snd.neg).prodMk hξ.fst))



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalProjection
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.NormalFrame

lemma gramDet_change_basis (X Y : RVec 4) (a b c d : ℝ) :
    NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) =
      (a*d-b*c)^2 * NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
  ring

lemma realNormalPart_linear (X Y : RVec 4) :
    IsLinearMap ℝ (realNormalPart X Y) := by
  constructor
  · intro W Z
    ext i
    simp [realNormalPart, dotProduct_add, Pi.add_apply]
    ring
  · intro s W
    ext i
    simp [realNormalPart, dotProduct_smul, Pi.smul_apply]
    ring

lemma realNormalPart_of_perp (X Y W : RVec 4) (hX : X ⬝ᵥ W = 0) (hY : Y ⬝ᵥ W = 0) :
    realNormalPart X Y W = W := by simp [realNormalPart, hX, hY]

lemma realNormalPart_self_left (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y X = 0 := by
  have hxy : Y ⬝ᵥ X = X ⬝ᵥ Y := dotProduct_comm _ _
  have ha : ((Y ⬝ᵥ Y) * (X ⬝ᵥ X) - (X ⬝ᵥ Y) * (Y ⬝ᵥ X)) /
      NormalFrame.gramDet X Y = 1 := by
    rw [hxy]
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  have hb : (X ⬝ᵥ X) * (Y ⬝ᵥ X) - (X ⬝ᵥ Y) * (X ⬝ᵥ X) = 0 := by rw [hxy]; ring
  simp [realNormalPart, ha, hb]

lemma realNormalPart_self_right (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y Y = 0 := by
  have ha : (Y ⬝ᵥ Y) * (X ⬝ᵥ Y) - (X ⬝ᵥ Y) * (Y ⬝ᵥ Y) = 0 := by ring
  have hb : ((X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) * (X ⬝ᵥ Y)) /
      NormalFrame.gramDet X Y = 1 := by
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  simp [realNormalPart, ha, hb]



lemma realNormalPart_change_basis (X Y W : RVec 4) (a b c d : ℝ)
    (hD : NormalFrame.gramDet X Y ≠ 0) (hdet : a*d-b*c ≠ 0) :
    realNormalPart (a • X + b • Y) (c • X + d • Y) W = realNormalPart X Y W := by
  let Z := realNormalPart (a • X + b • Y) (c • X + d • Y) W
  have hD' : NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) ≠ 0 := by
    rw [gramDet_change_basis]
    exact mul_ne_zero (pow_ne_zero 2 hdet) hD
  obtain ⟨hAZ, hBZ⟩ := realNormalPart_perp (a • X + b • Y) (c • X + d • Y) W hD'
  change (a • X + b • Y) ⬝ᵥ Z = 0 at hAZ
  change (c • X + d • Y) ⬝ᵥ Z = 0 at hBZ
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hAZ hBZ
  have hXZ : X ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (X ⬝ᵥ Z) = 0 by
      linear_combination d * hAZ - b * hBZ)).resolve_left hdet
  have hYZ : Y ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (Y ⬝ᵥ Z) = 0 by
      linear_combination a * hBZ - c * hAZ)).resolve_left hdet
  have hlin := realNormalPart_linear X Y
  have hA : realNormalPart X Y (a • X + b • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have hB : realNormalPart X Y (c • X + d • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have he : realNormalPart X Y Z = realNormalPart X Y W := by
    dsimp [Z]
    conv_lhs => arg 3; unfold realNormalPart
    rw [hlin.map_sub, hlin.map_sub, hlin.map_smul, hlin.map_smul, hA, hB]
    simp
  exact (realNormalPart_of_perp X Y Z hXZ hYZ).symm.trans he

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma real_second_coordDeriv {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) (v w : Base) :
    coordDeriv v (coordDeriv w F) p = fderiv ℝ (fderiv ℝ F) p v w := by
  have h := (hF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ F q) w) p) v = _
  rw [h]
  simp

lemma real_second_coordDeriv_comm {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) : coordDeriv v (coordDeriv w F) p = coordDeriv w (coordDeriv v F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  rw [real_second_coordDeriv hd, real_second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hF.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

lemma coordDeriv_eq_basis {n : ℕ} (F : RField n) (v p : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  conv_lhs => arg 1; rw [base_eq_basis v]
  simp [coordDeriv]

lemma second_coordDeriv_quadratic {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (v p : Base) : coordDeriv v (coordDeriv v F) p =
      (v.1^2) • coordDeriv dx (coordDeriv dx F) p +
      (2*v.1*v.2) • coordDeriv dx (coordDeriv dy F) p +
      (v.2^2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis v]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_quadratic {F : RField 4} (hF : ContDiff ℝ ∞ F) (v p : Base) :
    realSecondForm F v v p = secondQuadratic (realSecondTensor F p) v := by
  unfold realSecondForm
  rw [second_coordDeriv_quadratic hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [secondQuadratic, realSecondTensor, realSecondForm]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma second_coordDeriv_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v w p : Base) : coordDeriv v (coordDeriv w F) p =
      (v.1*w.1) • coordDeriv dx (coordDeriv dx F) p +
      (v.1*w.2+v.2*w.1) • coordDeriv dx (coordDeriv dy F) p +
      (v.2*w.2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis w]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    realSecondForm F v w p =
      (v.1*w.1) • realSecondTensor F p 0 +
      (v.1*w.2+v.2*w.1) • realSecondTensor F p 1 +
      (v.2*w.2) • realSecondTensor F p 2 := by
  unfold realSecondForm
  rw [second_coordDeriv_bilinear hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [realSecondTensor, realSecondForm]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (w p : Base) :
    coordDeriv w (F ∘ φ) p = fderiv ℝ F (φ p) (coordDeriv w φ p) := by
  simp only [coordDeriv,fderiv_comp p (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
    ContinuousLinearMap.comp_apply]

lemma second_coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base) :
    coordDeriv v (coordDeriv w (F ∘ φ)) p =
      coordDeriv (fderiv ℝ φ p v) (coordDeriv (fderiv ℝ φ p w) F) (φ p) +
      fderiv ℝ F (φ p) (coordDeriv v (coordDeriv w φ) p) := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD1 := ((hDF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (φ p)).hasFDerivAt.comp p
    ((hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt
  have hD2 := ((contDiffAt_coordDeriv (p := p) hφ.contDiffAt w).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hp := hD1.clm_apply hD2
  have he : (fun q => (fderiv ℝ F ∘ φ) q (coordDeriv w φ q)) = coordDeriv w (F ∘ φ) := by
    funext q
    exact (coordDeriv_comp_smooth hF hφ w q).symm
  rw [he] at hp
  have heval := congrArg (fun L => L v) hp.fderiv
  rw [real_second_coordDeriv ((hDF.differentiable (by simp)) (φ p))]
  simpa only [coordDeriv,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_apply,add_comm] using heval

lemma realNormalPart_fderiv {F : RField 4} (p v : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (fderiv ℝ F p v) = 0 := by
  change realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv v F p) = 0
  conv_lhs => arg 3; rw [coordDeriv_eq_basis F v p]
  have hl := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hl.map_add,hl.map_smul,hl.map_smul,realNormalPart_self_left _ _ hD,
    realNormalPart_self_right _ _ hD,smul_zero,smul_zero,add_zero]



lemma realSecondForm_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : (fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1 ≠ 0) :
    realSecondForm (F ∘ φ) v w p =
      realSecondForm F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p) := by
  unfold realSecondForm
  rw [coordDeriv_comp_smooth hF hφ,coordDeriv_comp_smooth hF hφ,
    second_coordDeriv_comp_smooth hF hφ]
  change realNormalPart (coordDeriv (fderiv ℝ φ p dx) F (φ p))
    (coordDeriv (fderiv ℝ φ p dy) F (φ p)) _ = _
  rw [coordDeriv_eq_basis F (fderiv ℝ φ p dx),coordDeriv_eq_basis F (fderiv ℝ φ p dy),
    realNormalPart_change_basis _ _ _ _ _ _ _ hD hdet]
  rw [(realNormalPart_linear _ _).map_add,realNormalPart_fderiv _ _ hD,add_zero]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma linear_apply_basis (A : Base →L[ℝ] Base) (v : Base) :
    A v = v.1 • A dx + v.2 • A dy := by
  calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
       _ = _ := by simp

lemma rotated_pullCovector (A : Base →L[ℝ] Base) (ξ : Base) :
    A (-(pullCovector A ξ).2,(pullCovector A ξ).1) = coordDet A • (-ξ.2,ξ.1) := by
  rw [linear_apply_basis]
  ext <;> simp [pullCovector,coordDet,Prod.smul_mk] <;> ring

lemma phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1) =
      (coordDet (fderiv ℝ φ p))^2 •
        secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1) := by
  rw [← realSecondForm_quadratic (hF.comp hφ),realSecondForm_comp_smooth hF hφ _ _ _ hD hdet,
    rotated_pullCovector,realSecondForm_quadratic hF,secondQuadratic_smul]

lemma norm_phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ =
      (coordDet (fderiv ℝ φ p))^2 *
        ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by
  rw [phase_length_comp_smooth hF hφ ξ p hD hdet,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

lemma norm_realSecondForm_le {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    ‖realSecondForm F v w p‖ ≤ 4*‖realSecondTensor F p‖*‖v‖*‖w‖ := by
  have h11 : |v.1*w.1| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_fst_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h22 : |v.2*w.2| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_snd_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h12 : |v.1*w.2+v.2*w.1| ≤ 2*‖v‖*‖w‖ := by
    have ha : |v.1*w.2| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_snd_le w)
        (abs_nonneg _) (norm_nonneg _)
    have hb : |v.2*w.1| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_fst_le w)
        (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (v.1*w.2) (v.2*w.1)]
  rw [realSecondForm_bilinear hF]
  calc
    _ ≤ (‖(v.1*w.1) • realSecondTensor F p 0‖+
        ‖(v.1*w.2+v.2*w.1) • realSecondTensor F p 1‖)+
        ‖(v.2*w.2) • realSecondTensor F p 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖*‖w‖*‖realSecondTensor F p‖+
        (2*‖v‖*‖w‖)*‖realSecondTensor F p‖)+‖v‖*‖w‖*‖realSecondTensor F p‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      gcongr
      · exact norm_le_pi_norm _ 0
      · exact norm_le_pi_norm _ 1
      · exact norm_le_pi_norm _ 2
    _ = _ := by ring

lemma norm_realSecondTensor_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖realSecondTensor (F ∘ φ) p‖ ≤
      4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
  have hbound (v : Base) (hv : ‖v‖ = 1) : ‖fderiv ℝ φ p v‖ ≤ ‖fderiv ℝ φ p‖ := by
    simpa only [hv,mul_one] using (fderiv ℝ φ p).le_opNorm v
  have hx : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have hy : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have hb (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖realSecondForm (F ∘ φ) v w p‖ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
    rw [realSecondForm_comp_smooth hF hφ _ _ _ hD hdet]
    calc
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p v‖*‖fderiv ℝ φ p w‖ :=
        norm_realSecondForm_le hF _ _ _
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖*‖fderiv ℝ φ p‖ := by
        gcongr
        · exact hbound v hv
        · exact hbound w hw
      _ = _ := by ring
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · exact hb dx dx hx hx
  · exact hb dx dy hx hy
  · exact hb dy dy hy hy

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JacobianBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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
open SmallModes PhaseGeometry Set Filter

lemma coordDet_comp (A B : Base →L[ℝ] Base) :
    coordDet (A.comp B) = coordDet A * coordDet B := by
  simp only [coordDet,ContinuousLinearMap.comp_apply]
  rw [linear_apply_basis A (B dx),linear_apply_basis A (B dy)]
  simp
  ring

lemma coordDet_id : coordDet (ContinuousLinearMap.id ℝ Base) = 1 := by
  simp [coordDet,dx,dy]

lemma continuous_coordDet : Continuous coordDet := by
  unfold coordDet
  fun_prop

lemma coordDet_fderiv_ne_zero_of_local_inverse {φ ψ : Base → Base} {U V : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) {p : Base} (hp : p ∈ U) :
    coordDet (fderiv ℝ φ p) ≠ 0 := by
  have hφp := ((hφ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hψp := ((hψ (φ p) (hmap hp)).contDiffAt (hV.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : ψ ∘ φ =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hinv hq
  have hcomp : (fderiv ℝ ψ (φ p)).comp (fderiv ℝ φ p) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p hψp hφp,he.fderiv_eq,fderiv_id]
  have hdet := congrArg coordDet hcomp
  rw [coordDet_comp,coordDet_id] at hdet
  intro hz
  simp [hz] at hdet



theorem compact_chart_jacobian_bounds {φ ψ : Base → Base} {U V K : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ p ∈ K, d ≤ |coordDet (fderiv ℝ φ p)| ∧ ‖fderiv ℝ φ p‖ ≤ C := by
  have hD : ContinuousOn (fderiv ℝ φ) K :=
    (hφ.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU
  have hd : ContinuousOn (fun p => |coordDet (fderiv ℝ φ p)|) K :=
    (continuous_coordDet.comp_continuousOn hD).abs
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hD
  by_cases hn : K.Nonempty
  · obtain ⟨p,hp,hm⟩ := hK.exists_isMinOn hn hd
    refine ⟨|coordDet (fderiv ℝ φ p)|,|C|+1,abs_pos.mpr ?_,by positivity,?_⟩
    · exact coordDet_fderiv_ne_zero_of_local_inverse hU hV hφ hψ hmap hinv (hKU hp)
    · intro q hq
      exact ⟨hm hq,(hC q hq).trans (by linarith [le_abs_self C])⟩
  · exact ⟨1,1,zero_lt_one,zero_lt_one,fun p hp => False.elim (hn ⟨p,hp⟩)⟩

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinateDomain_open (p : M) : IsOpen (coordinateDomain p) := by
  apply IsOpen.preimage planeCoordinates.symm.continuous
  simpa [extChartAt_target, planeModel] using (chartAt Plane p).open_target

lemma coordinateMap_smoothOn [IsManifold planeModel ∞ M] {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) :
    ContDiffOn ℝ ∞ (coordinateMap F p) (coordinateDomain p) := by
  apply ContMDiffOn.contDiffOn
  have hChart := contMDiffOn_extChartAt_symm (I := planeModel) (n := (∞ : ℕ∞ω)) p
  have h1 := hF.comp_contMDiffOn hChart
  have h2 := spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn h1
  exact h2.comp planeCoordinates.symm.contDiff.contMDiff.contMDiffOn
    (fun x hx => hx)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPullback
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma metricPullback_pos (g : SmoothMetric M) {φ : Base → M} {x : Base}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, Base) planeModel φ x)) {v : Base} (hv : v ≠ 0) :
    0 < metricPullback g φ x v v := by
  apply g.pos
  intro hz
  apply hv
  apply hi
  exact hz.trans (map_zero _).symm

lemma coordinateMetric_evaluate (g : SmoothMetric M) (p : M) (x v w : Base) :
    PhaseMean.evaluate (coordinateMetric g p x) v w =
      metricPullback g (coordinateInverse p) x v w := by
  let D : Base →L[ℝ] TangentSpace planeModel (coordinateInverse p x) :=
    mfderiv 𝓘(ℝ, Base) planeModel (coordinateInverse p) x
  change PhaseMean.evaluate (fun i => g.inner (coordinateInverse p x)
      (D (PhaseMean.firstDirection i)) (D (PhaseMean.secondDirection i))) v w =
    g.inner (coordinateInverse p x) (D v) (D w)
  have he (v : Base) : v = v.1 • dx + v.2 • dy := by
    ext <;> simp [dx,dy]
  conv_rhs => rw [he v, he w]
  simp only [PhaseMean.evaluate,
    PhaseMean.firstDirection, PhaseMean.secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead, Function.comp_apply,
    map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [g.symm _
    (D dy) (D dx)]
  dsimp
  ring

lemma tensor_positive_iff (H : PhaseMean.Tensor) :
    (∀ v : Base, v ≠ 0 → 0 < PhaseMean.evaluate H v v) ↔
      0 < H 0 ∧ 0 < H 0 * H 2 - (H 1)^2 := by
  constructor
  · intro h
    have h₀ : 0 < H 0 := by
      simpa [PhaseMean.evaluate] using h (1, 0) (by simp)
    have hv : (-H 1, H 0) ≠ (0 : Base) := by
      intro he
      have he' := congrArg Prod.snd he
      exact h₀.ne' he'
    have hh := h (-H 1, H 0) hv
    have he : PhaseMean.evaluate H (-H 1, H 0) (-H 1, H 0) = H 0 * (H 0 * H 2 - (H 1)^2) := by
      simp only [PhaseMean.evaluate]
      ring
    rw [he] at hh
    exact ⟨h₀, (mul_pos_iff_of_pos_left h₀).mp hh⟩
  · rintro ⟨h₀, hd⟩ v hv
    have he : H 0 * PhaseMean.evaluate H v v =
        (H 0 * v.1 + H 1 * v.2)^2 + (H 0 * H 2 - (H 1)^2) * v.2^2 := by
      simp only [PhaseMean.evaluate]
      ring
    apply (mul_pos_iff_of_pos_left h₀).mp
    rw [he]
    by_cases hv₂ : v.2 = 0
    · have hv₁ : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Prod.ext hz hv₂
      simp only [hv₂, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_pos_of_ne_zero (mul_ne_zero h₀.ne' hv₁)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hd (sq_pos_of_ne_zero hv₂))


end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]




theorem smooth_extension_near {F : M → V} {U : Set M} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ F U) {p : M} (hp : p ∈ U) :
    ∃ G : M → V, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ G ∧
      HasCompactSupport G ∧ tsupport G ⊆ U ∧ G =ᶠ[𝓝 p] F := by
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
    (hU.mem_nhds hp)
  let G : M → V := fun q => b q • F q
  have hs : tsupport G ⊆ tsupport b := tsupport_smul_subset_left _ _
  refine ⟨G, ?_, ?_, hs.trans hb, ?_⟩
  · apply contMDiff_of_tsupport
    intro q hq
    exact b.contMDiffAt.smul ((hF q (hb (hs hq))).contMDiffAt
      (hU.mem_nhds (hb (hs hq))))
  · exact b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport G) hs
  · filter_upwards [b.eventuallyEq_one] with q hq
    simp only [G, hq, Pi.one_apply, one_smul]

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma coordDeriv_eventuallyEq {n : ℕ} {F G : RField n} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v : Base) : coordDeriv v F =ᶠ[𝓝 p] coordDeriv v G := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun A : Base →L[ℝ] RVec n => A v) hq

lemma realSecondForm_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v w : Base) :
    (fun q => realSecondForm F v w q) =ᶠ[𝓝 p] (fun q => realSecondForm G v w q) := by
  filter_upwards [coordDeriv_eventuallyEq h dx, coordDeriv_eventuallyEq h dy,
    coordDeriv_eventuallyEq (coordDeriv_eventuallyEq h w) v] with q hx hy hxy
  simp only [realSecondForm, hx, hy, hxy]

lemma realSecondTensor_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) : realSecondTensor F =ᶠ[𝓝 p] realSecondTensor G := by
  filter_upwards [realSecondForm_eventuallyEq h dx dx, realSecondForm_eventuallyEq h dx dy,
    realSecondForm_eventuallyEq h dy dy] with q hxx hxy hyy
  ext i
  fin_cases i <;> simp [realSecondTensor, hxx, hxy, hyy]




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPatches
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma chartCoordinates_continuousOn (p : M) :
    ContinuousOn (chartCoordinates p) (chartAt Plane p).source :=
  planeCoordinates.continuous.comp_continuousOn (chartAt Plane p).continuousOn

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

lemma coordinateTransition_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p) (coordinateTransition q p).source := by
  apply ContMDiffOn.contDiffOn
  exact (coordinateChart_smoothOn q).comp
    ((coordinateChart_symm_smoothOn p).mono (fun x hx => hx.1)) (fun x hx => hx.2)

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_symm (q p : M) :
    (coordinateTransition q p).symm = coordinateTransition p q := by
  simp [coordinateTransition,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

lemma coordinateTransition_symm_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p).symm (coordinateTransition q p).target := by
  have h := coordinateTransition_smoothOn p q
  rw [← coordinateTransition_symm q p] at h
  exact h



theorem coordinateTransition_compact_bounds (q p : M) {K : Set SmallModes.Base}
    (hK : IsCompact K) (hKs : K ⊆ (coordinateTransition q p).source) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ x ∈ K, d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)| ∧
        ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ C := by
  let e := coordinateTransition q p
  exact compact_chart_jacobian_bounds e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun x hx => e.left_inv hx) hK hKs

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseWeights
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set



theorem uniform_good_perturbation {X : Type*} [TopologicalSpace X] {n : ℕ}
    {K : Set X} (hK : IsCompact K) {B : X → Fin 3 → RVec n} {ξ υ : X → Base}
    (hB : Continuous B) (hξ : Continuous ξ) (hυ : Continuous υ)
    (hgood : ∀ p ∈ K, Good (B p) (ξ p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ p ∈ K, Good (B p) (ξ p + t • υ p) := by
  let U : Set (X × ℝ) := {z | Good (B z.1) (ξ z.1 + z.2 • υ z.1)}
  have hU : IsOpen U := isOpen_good (hB.comp continuous_fst)
    ((hξ.comp continuous_fst).add (continuous_snd.smul (hυ.comp continuous_fst)))
  have hKU : K ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    simp only [mem_singleton_iff] at ht
    subst t
    simpa [U] using hgood p hp
  obtain ⟨V, W, hV, hW, hKV, h0W, hprod⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hKU
  obtain ⟨ε, hε, heW⟩ := Metric.isOpen_iff.mp hW 0 (h0W (by simp))
  refine ⟨ε, hε, fun t ht p hp => ?_⟩
  change (p, t) ∈ U
  apply hprod ⟨hKV hp, heW ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using ht




end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseStock
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean Set

lemma secondQuadratic_smul_form {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (a : ℝ) :
    secondQuadratic (a • B) v = a • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes



lemma dominant_power_ratio {ε a : ℝ} (ha : 1 ≤ a) (haε : 1 < ε * a)
    {i j : ℕ} (hij : i < j) : |a^i / a^j| < ε := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hp : a^(i+1) ≤ a^j := pow_le_pow_right₀ ha hij
  have ht : a^i / a^j ≤ 1 / a := by
    rw [div_le_div_iff₀ (pow_pos ha0 j) ha0]
    simpa [pow_succ] using hp
  have hε : 1 / a < ε := by
    rw [div_lt_iff₀ ha0]
    exact haε
  rw [abs_of_pos (div_pos (pow_pos ha0 i) (pow_pos ha0 j))]
  exact ht.trans_lt hε



end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes Set Metric




theorem universal_normalized_phase_margin {n : ℕ} {ε C : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (B : Fin 3 → RVec n) (ξ υ : Base),
      ‖B‖ = 1 → ‖ξ‖ ≤ C → ‖υ‖ ≤ C →
      ε ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ →
      ∀ t : ℝ, |t| < δ → Good B (ξ+t • υ) := by
  let K₀ : Set ((Fin 3 → RVec n) × Base) :=
    (sphere 0 1 ×ˢ closedBall 0 C) ∩
      {p | ε ≤ ‖secondQuadratic p.1 (-p.2.2,p.2.1)‖}
  have hc : Continuous (fun p : (Fin 3 → RVec n) × Base =>
      secondQuadratic p.1 (-p.2.2,p.2.1)) :=
    continuous_secondQuadratic.comp
      (continuous_fst.prodMk ((continuous_snd.snd.neg).prodMk continuous_snd.fst))
  have hK₀ : IsCompact K₀ := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).inter_right
    (isClosed_le continuous_const hc.norm)
  let K : Set (((Fin 3 → RVec n) × Base) × Base) := K₀ ×ˢ closedBall 0 C
  have hgood (p : ((Fin 3 → RVec n) × Base) × Base) (hp : p ∈ K) : Good p.1.1 p.1.2 := by
    have hn : secondQuadratic p.1.1 (-p.1.2.2,p.1.2.1) ≠ 0 :=
      norm_pos_iff.mp (hε.trans_le hp.1.2)
    refine ⟨?_,hn⟩
    intro hz
    apply hn
    simp [hz,secondQuadratic]
  obtain ⟨δ,hδ,hd⟩ := uniform_good_perturbation (K := K)
    (hK₀.prod (isCompact_closedBall _ _)) continuous_fst.fst continuous_fst.snd continuous_snd hgood
  refine ⟨δ,hδ,fun B ξ υ hB hξ hυ hm t ht => hd t ht ((B,ξ),υ) ?_⟩
  exact ⟨⟨⟨by simpa [mem_sphere,dist_zero_right] using hB,
    by simpa [mem_closedBall,dist_zero_right] using hξ⟩,hm⟩,
    by simpa [mem_closedBall,dist_zero_right] using hυ⟩



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LengthMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes Set Metric



theorem universal_normalized_length_margin {n : ℕ} {ε C : ℝ} (hε : 0 < ε) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∀ (B : Fin 3 → RVec n) (ξ υ : Base),
      ‖B‖ = 1 → ‖ξ‖ ≤ C → ‖υ‖ ≤ C →
      ε ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ →
      ∀ t : ℝ, |t| ≤ δ → κ ≤ ‖secondQuadratic B (-(ξ+t • υ).2,(ξ+t • υ).1)‖ := by
  obtain ⟨d,hd,hgood⟩ := universal_normalized_phase_margin (n := n) (C := C) hε
  let δ := d/2
  have hδ : 0 < δ := half_pos hd
  let K₀ : Set ((Fin 3 → RVec n) × Base) :=
    (sphere 0 1 ×ˢ closedBall 0 C) ∩ {p | ε ≤ ‖secondQuadratic p.1 (-p.2.2,p.2.1)‖}
  have hc : Continuous (fun p : (Fin 3 → RVec n) × Base =>
      secondQuadratic p.1 (-p.2.2,p.2.1)) :=
    continuous_secondQuadratic.comp
      (continuous_fst.prodMk ((continuous_snd.snd.neg).prodMk continuous_snd.fst))
  have hK₀ : IsCompact K₀ := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).inter_right
    (isClosed_le continuous_const hc.norm)
  let K : Set (((Fin 3 → RVec n) × Base) × (Base × ℝ)) :=
    K₀ ×ˢ (closedBall 0 C ×ˢ Icc (-δ) δ)
  have hK : IsCompact K := hK₀.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  let f : (((Fin 3 → RVec n) × Base) × (Base × ℝ)) → ℝ := fun p =>
    ‖secondQuadratic p.1.1 (-(p.1.2+p.2.2 • p.2.1).2,(p.1.2+p.2.2 • p.2.1).1)‖
  have hg : Continuous (fun p : (((Fin 3 → RVec n) × Base) × (Base × ℝ)) =>
      (p.1.1, (-(p.1.2+p.2.2 • p.2.1).2,(p.1.2+p.2.2 • p.2.1).1))) := by fun_prop
  have hf : Continuous f := (continuous_secondQuadratic.comp hg).norm
  have hpos : ∀ p ∈ K, 0 < f p := by
    intro p hp
    have hb : ‖p.1.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1.1
    have hξ : ‖p.1.2‖ ≤ C := by simpa only [mem_closedBall,dist_zero_right] using hp.1.1.2
    have hυ : ‖p.2.1‖ ≤ C := by simpa only [mem_closedBall,dist_zero_right] using hp.2.1
    have ht : |p.2.2| < d := (abs_le.mpr hp.2.2).trans_lt (by dsimp [δ] <;> linarith)
    exact norm_pos_iff.mpr (hgood p.1.1 p.1.2 p.2.1 hb hξ hυ hp.1.2 p.2.2 ht).2
  obtain ⟨κ,hκ,hb⟩ := hK.exists_forall_le' hf.continuousOn hpos
  refine ⟨δ,κ,hδ,hκ,fun B ξ υ hB hξ hυ hm t ht => ?_⟩
  apply hb ((B,ξ),(υ,t))
  exact ⟨⟨⟨by simpa [mem_sphere,dist_zero_right] using hB,
    by simpa [mem_closedBall,dist_zero_right] using hξ⟩,hm⟩,
    by simpa [mem_closedBall,dist_zero_right] using hυ,abs_le.mp ht⟩



theorem universal_relative_length_margin {n : ℕ} {ε C : ℝ} (hε : 0 < ε) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∀ (B : Fin 3 → RVec n) (ξ υ : Base),
      B ≠ 0 → ‖ξ‖ ≤ C → ‖υ‖ ≤ C →
      ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ →
      ∀ t : ℝ, |t| ≤ δ → κ*‖B‖ ≤ ‖secondQuadratic B (-(ξ+t • υ).2,(ξ+t • υ).1)‖ := by
  obtain ⟨δ,κ,hδ,hκ,hm⟩ := universal_normalized_length_margin (n := n) (C := C) hε
  refine ⟨δ,κ,hδ,hκ,fun B ξ υ hB hξ hυ hmargin t ht => ?_⟩
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hu : ‖(‖B‖⁻¹ : ℝ) • B‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn,inv_mul_cancel₀ hn.ne']
  have hmargin' : ε ≤ ‖secondQuadratic ((‖B‖⁻¹ : ℝ) • B) (-ξ.2,ξ.1)‖ := by
    rw [secondQuadratic_smul_form,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn]
    have hl := mul_le_mul_of_nonneg_left hmargin (inv_nonneg.mpr hn.le)
    simpa [mul_assoc,← mul_assoc (‖B‖⁻¹) ε,mul_comm (‖B‖⁻¹) ε,
      mul_assoc,inv_mul_cancel₀ hn.ne'] using hl
  have hh := hm _ ξ υ hu hξ hυ hmargin' t ht
  rw [secondQuadratic_smul_form,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn] at hh
  have hl := mul_le_mul_of_nonneg_left hh hn.le
  simpa [← mul_assoc,mul_inv_cancel₀ hn.ne',mul_comm κ ‖B‖] using hl

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma norm_secondQuadratic_rotated_smul {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base) (a : ℝ) :
    ‖secondQuadratic B (-(a • ξ).2,(a • ξ).1)‖ =
      a^2*‖secondQuadratic B (-ξ.2,ξ.1)‖ := by
  have he : (-(a • ξ).2,(a • ξ).1) = a • (-ξ.2,ξ.1) := by
    ext <;> simp [mul_neg]
  rw [he,secondQuadratic_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg a)]

lemma norm_secondQuadratic_rotated_neg {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base) :
    ‖secondQuadratic B (-(-ξ).2,(-ξ).1)‖ = ‖secondQuadratic B (-ξ.2,ξ.1)‖ := by
  simpa only [neg_one_smul,neg_sq,one_pow,one_mul] using
    norm_secondQuadratic_rotated_smul B ξ (-1)

lemma power_weight_length_pairs {n : ℕ} (B : Fin 3 → RVec n) (ξ υ : Base)
    {δ a κ : ℝ} (ha : 1 ≤ a) (haδ : 1 < δ*a)
    (hmargin : ∀ t : ℝ, |t| < δ → κ*‖B‖ ≤ ‖secondQuadratic B (-(ξ+t • υ).2,(ξ+t • υ).1)‖)
    {i j : ℕ} (hij : i < j) :
    κ*‖B‖ ≤ ‖secondQuadratic B (-(a^i • υ+a^j • ξ).2,(a^i • υ+a^j • ξ).1)‖ ∧
    κ*‖B‖ ≤ ‖secondQuadratic B (-(a^i • υ-a^j • ξ).2,(a^i • υ-a^j • ξ).1)‖ := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hp := dominant_power_ratio ha haδ hij
  have hpj : 1 ≤ a^j := one_le_pow₀ ha
  have hsq : 1 ≤ (a^j)^2 := by nlinarith
  have lift (v : Base) : ‖secondQuadratic B (-v.2,v.1)‖ ≤
      ‖secondQuadratic B (-(a^j • v).2,(a^j • v).1)‖ := by
    rw [norm_secondQuadratic_rotated_smul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (norm_nonneg (secondQuadratic B (-v.2,v.1)))
  have heplus : a^j • (ξ+(a^i/a^j) • υ) = a^i • υ+a^j • ξ := by
    rw [smul_add,smul_smul,mul_div_cancel₀ _ (pow_ne_zero j ha0.ne')]
    exact add_comm _ _
  have heminus : a^j • (ξ+(-(a^i/a^j)) • υ) = -(a^i • υ-a^j • ξ) := by
    rw [smul_add,smul_smul,mul_neg,mul_div_cancel₀ _ (pow_ne_zero j ha0.ne')]
    simp only [neg_smul]
    abel
  constructor
  · have hh := (hmargin _ hp).trans (lift _)
    simpa only [heplus] using hh
  · have hh := (hmargin (-(a^i/a^j)) (by simpa only [abs_neg] using hp)).trans (lift _)
    simpa only [heminus,norm_secondQuadratic_rotated_neg] using hh

lemma good_of_direction_length_pos {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    (h : 0 < ‖secondQuadratic B (-ξ.2,ξ.1)‖) : Good B ξ := by
  refine ⟨?_, norm_pos_iff.mp h⟩
  intro hξ
  simp [hξ,secondQuadratic] at h





theorem quantitative_labeled_phase_lengths_with_catalog {ι X : Type*} {n N : ℕ}
    (label : ι → Fin N) {ε C : ℝ} (hε : 0 < ε) :
    ∃ stock : Finset ℝ, ∃ W κ : ℝ, 0 < W ∧ 0 < κ ∧
      ∀ (B : X → Fin 3 → RVec n) (ξ : ι → X → Base) (active : ι → X → Prop),
      (∀ i j x, i ≠ j → active i x → active j x → label i ≠ label j) →
      (∀ i x, active i x → B x ≠ 0 ∧ ‖ξ i x‖ ≤ C ∧
        ε*‖B x‖ ≤ ‖secondQuadratic (B x) (-(ξ i x).2,(ξ i x).1)‖) →
      ∃ w : ι → ℝ, (∀ i, w i ∈ stock) ∧ (∀ i, 1 ≤ w i ∧ w i ≤ W) ∧
      ∀ i j x, i ≠ j → active i x → active j x →
        κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x+w j • ξ j x).2,(w i • ξ i x+w j • ξ j x).1)‖ ∧
        κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x-w j • ξ j x).2,(w i • ξ i x-w j • ξ j x).1)‖ ∧
        Good (B x) (w i • ξ i x+w j • ξ j x) ∧ Good (B x) (w i • ξ i x-w j • ξ j x) := by
  classical
  obtain ⟨δ,κ,hδ,hκ,hm⟩ := universal_relative_length_margin (n := n) (C := C) hε
  let a : ℝ := 1+1/δ
  have ha : 1 ≤ a := by dsimp [a] <;> linarith [one_div_pos.mpr hδ]
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have haδ : 1 < δ*a := by
    dsimp [a]
    rw [mul_add,mul_one,mul_one_div_cancel hδ.ne']
    linarith
  let stock : Finset ℝ := Finset.univ.image (fun j : Fin N => a^j.val)
  refine ⟨stock,a^N,κ,pow_pos ha0 N,hκ,?_⟩
  intro B ξ active hlabels hdata
  let w : ι → ℝ := fun i => a^(label i).val
  refine ⟨w,(fun i => Finset.mem_image.mpr ⟨label i,Finset.mem_univ _,rfl⟩),fun i => ⟨one_le_pow₀ ha,pow_le_pow_right₀ ha (label i).isLt.le⟩,?_⟩
  intro i j x hij hi hj
  have hw (i j : ι) (hi : active i x) (hj : active j x) (hl : (label i).val < (label j).val) :
      κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x+w j • ξ j x).2,(w i • ξ i x+w j • ξ j x).1)‖ ∧
      κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x-w j • ξ j x).2,(w i • ξ i x-w j • ξ j x).1)‖ := by
    exact power_weight_length_pairs (B x) (ξ j x) (ξ i x) ha haδ
      (fun t ht => hm (B x) (ξ j x) (ξ i x) (hdata j x hj).1
        (hdata j x hj).2.1 (hdata i x hi).2.1 (hdata j x hj).2.2 t ht.le) hl
  have hlengths :
      κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x+w j • ξ j x).2,(w i • ξ i x+w j • ξ j x).1)‖ ∧
      κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x-w j • ξ j x).2,(w i • ξ i x-w j • ξ j x).1)‖ := by
    have hne : (label i).val ≠ (label j).val := fun he => hlabels i j x hij hi hj (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hw i j hi hj hlt
    · obtain ⟨hp,hm⟩ := hw j i hj hi hgt
      constructor
      · simpa only [add_comm] using hp
      · have he : w j • ξ j x-w i • ξ i x = -(w i • ξ i x-w j • ξ j x) := by abel
        simpa only [he,norm_secondQuadratic_rotated_neg] using hm
  have hn : 0 < κ*‖B x‖ := mul_pos hκ (norm_pos_iff.mpr (hdata i x hi).1)
  exact ⟨hlengths.1,hlengths.2,good_of_direction_length_pos _ _ (hn.trans_le hlengths.1),
    good_of_direction_length_pos _ _ (hn.trans_le hlengths.2)⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CoordinateMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma norm_pullCovector_le (A : Base →L[ℝ] Base) (ξ : Base) :
    ‖pullCovector A ξ‖ ≤ 2*‖A‖*‖ξ‖ := by
  have hd : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have he : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have bound (v : Base) (hv : ‖v‖ = 1) : |ξ.1*(A v).1+ξ.2*(A v).2| ≤ 2*‖A‖*‖ξ‖ := by
    have hA : ‖A v‖ ≤ ‖A‖ := by simpa only [hv,mul_one] using A.le_opNorm v
    have h1 : |ξ.1*(A v).1| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le ξ)
        ((show |(A v).1| ≤ ‖A v‖ by simpa using norm_fst_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    have h2 : |ξ.2*(A v).2| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le ξ)
        ((show |(A v).2| ≤ ‖A v‖ by simpa using norm_snd_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (ξ.1*(A v).1) (ξ.2*(A v).2)]
  change max ‖ξ.1*(A dx).1+ξ.2*(A dx).2‖ ‖ξ.1*(A dy).1+ξ.2*(A dy).2‖ ≤ _
  simpa only [Real.norm_eq_abs,max_le_iff] using And.intro (bound dx hd) (bound dy he)




theorem quantitative_chart_phase_margin {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  have hdet0 : coordDet (fderiv ℝ φ p) ≠ 0 := abs_pos.mp (hd.trans_le hdet)
  have hsq : d^2 ≤ (coordDet (fderiv ℝ φ p))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hd.le hdet 2
  have hbc : ‖realSecondTensor (F ∘ φ) p‖ ≤ 4*‖realSecondTensor F (φ p)‖*C ^ 2 := by
    apply (norm_realSecondTensor_comp_smooth hF hφ p hD hdet0).trans
    gcongr
  have hlength := norm_phase_length_comp_smooth hF hφ ξ p hD hdet0
  have hbound : d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    calc
      _ ≤ d^2*ε/(4*C ^ 2)*(4*‖realSecondTensor F (φ p)‖*C ^ 2) := by gcongr
      _ = d^2*(ε*‖realSecondTensor F (φ p)‖) := by field_simp
      _ ≤ d^2*‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
  have hpos : 0 < ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    exact mul_pos (sq_pos_of_ne_zero hdet0) ((mul_pos hε (norm_pos_iff.mpr hB)).trans_le hmargin)
  refine ⟨(norm_pullCovector_le _ _).trans ?_,hbound,good_of_direction_length_pos _ _ hpos,?_⟩
  · gcongr
  · intro hz
    simp only [hz,secondQuadratic,Pi.zero_apply,smul_zero,add_zero,norm_zero] at hpos
    exact lt_irrefl 0 hpos

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter




theorem quantitative_chart_phase_margin_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V) (ξ : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  obtain ⟨G,hG,_,_,heG⟩ := smooth_extension_near hV hF.contMDiffOn hφp
  obtain ⟨Φ,hΦ,_,_,heΦ⟩ := smooth_extension_near hU hφ.contMDiffOn hp
  have ep := heΦ.eq_of_nhds
  have eD := heΦ.fderiv_eq (𝕜 := ℝ)
  have hc : ContinuousAt φ p := (hφ p hp).contDiffAt (hU.mem_nhds hp) |>.continuousAt
  have hecomp : G ∘ Φ =ᶠ[𝓝 p] F ∘ φ := by
    filter_upwards [heΦ,heG.comp_tendsto hc] with q hqΦ hqG
    simpa only [Function.comp_apply,hqΦ] using hqG
  have hDG : NormalFrame.gramDet (coordDeriv dx G (Φ p)) (coordDeriv dy G (Φ p)) ≠ 0 := by
    rw [ep,(coordDeriv_eventuallyEq heG dx).eq_of_nhds,
      (coordDeriv_eventuallyEq heG dy).eq_of_nhds]
    exact hD
  have hTG := (realSecondTensor_eventuallyEq heG).eq_of_nhds
  have hTF := (realSecondTensor_eventuallyEq hecomp).eq_of_nhds
  have h := quantitative_chart_phase_margin hG.contDiff hΦ.contDiff ξ p hd hC hε hDG
    (by simpa only [eD] using hdet) (by simpa only [eD] using hA)
    (by simpa only [ep,hTG] using hB) (by simpa only [ep,hTG] using hmargin)
  simpa only [eD,hTF] using h

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasMargins
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q (coordinateTransition q p x) = coordinateMap F p x := by
  change spaceCoordinates (F (coordinateInverse q (coordinateTransition q p x))) =
    spaceCoordinates (F (coordinateInverse p x))
  rw [← coordinateChart_symm_apply, ← coordinateChart_symm_apply]
  change spaceCoordinates (F ((coordinateChart q).symm
    (coordinateChart q ((coordinateChart p).symm x)))) = _
  have hqx : (coordinateChart p).symm x ∈ (coordinateChart q).source := hx.2
  rw [(coordinateChart q).left_inv hqx]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition_eventuallyEq (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q ∘ coordinateTransition q p =ᶠ[𝓝 x] coordinateMap F p := by
  filter_upwards [(coordinateTransition q p).open_source.mem_nhds hx] with y hy
  exact coordinateMap_transition F q p hy




theorem actual_chart_phase_margin {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) (ξ : SmallModes.Base)
    {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateTransition q p x))
      (coordDeriv dy (coordinateMap F q) (coordinateTransition q p x)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)|)
    (hA : ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ L)
    (hB : realSecondTensor (coordinateMap F q) (coordinateTransition q p x) ≠ 0)
    (hmargin : ε*‖realSecondTensor (coordinateMap F q) (coordinateTransition q p x)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateTransition q p x)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ‖ ≤ 2*L*‖ξ‖ ∧
    d^2*ε/(4*L^2)*‖realSecondTensor (coordinateMap F p) x‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F p) x)
        (-(pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).2,
          (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).1)‖ ∧
    Good (realSecondTensor (coordinateMap F p) x)
      (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ) ∧
    realSecondTensor (coordinateMap F p) x ≠ 0 := by
  have hy : coordinateTransition q p x ∈ coordinateDomain q := by
    rw [← coordinateChart_target]
    exact (coordinateChart q).map_source hx.2
  have ht := quantitative_chart_phase_margin_on
    (coordinateTransition q p).open_source (coordinateDomain_open q)
    (coordinateMap_smoothOn hF q) (coordinateTransition_smoothOn q p)
    hx hy ξ hd hL hε hD hdet hA hB hmargin
  have he := (realSecondTensor_eventuallyEq
    (coordinateMap_transition_eventuallyEq F q p hx)).eq_of_nhds
  simpa only [he] using ht

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma coordinateChart_compact_image {K : Set M} (hK : IsCompact K) (p : M)
    (hKs : K ⊆ (coordinateChart p).source) :
    IsCompact (coordinateChart p '' K) := hK.image_of_continuousOn ((coordinateChart p).continuousOn.mono hKs)

omit [IsManifold planeModel ∞ M] in
lemma coordinateChart_image_overlap {K : Set M} (q p : M)
    (hKp : K ⊆ (coordinateChart p).source) (hKq : K ⊆ (coordinateChart q).source) :
    coordinateChart p '' K ⊆ (coordinateTransition q p).source := by
  rintro x ⟨a,ha,rfl⟩
  constructor
  · exact (coordinateChart p).map_source (hKp ha)
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rw [(coordinateChart p).left_inv (hKp ha)]
    exact hKq ha




end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridBumps
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

lemma cutoff_support {h : ℝ} (hh : 0 < h) (a : Index) :
    Function.support (cutoff h a) = cell h 2 a := by
  ext x
  change gridBump (h⁻¹ • x - center a) ≠ 0 ↔ _
  rw [← Function.mem_support, gridBump.support_eq]
  simp only [Metric.mem_ball, dist_zero_right, gridBump, Prod.norm_def]
  change (max |h⁻¹*x.1-a.1| |h⁻¹*x.2-a.2| < 2) ↔ _
  rw [max_lt_iff]
  exact and_congr (scaled_coordinate_lt hh) (scaled_coordinate_lt hh)

lemma cutoff_tsupport_subset {h : ℝ} (hh : 0 < h) (a : Index) :
    tsupport (cutoff h a) ⊆ cell h 3 a := by
  have hclosed : IsClosed {x : Base | |x.1-h*a.1| ≤ 2*h ∧ |x.2-h*a.2| ≤ 2*h} :=
    (isClosed_le ((continuous_fst.sub continuous_const).abs) continuous_const).inter
      (isClosed_le ((continuous_snd.sub continuous_const).abs) continuous_const)
  have hs : Function.support (cutoff h a) ⊆
      {x : Base | |x.1-h*a.1| ≤ 2*h ∧ |x.2-h*a.2| ≤ 2*h} := by
    rw [cutoff_support hh]
    exact fun _ hx => ⟨hx.1.le,hx.2.le⟩
  have ht := closure_minimal hs hclosed
  intro x hx
  have hp := ht hx
  exact ⟨lt_of_le_of_lt hp.1 (by linarith),lt_of_le_of_lt hp.2 (by linarith)⟩



theorem cutoff_same_color_disjoint {h : ℝ} (hh : 0 < h) {a b : Index} (hne : a ≠ b)
    (he : color 6 a = color 6 b) :
    Disjoint (tsupport (cutoff h a)) (tsupport (cutoff h b)) :=
  (same_color_disjoint (by norm_num : 0 < 6) hh (by norm_num : (2:ℝ)*3 ≤ 6) hne he).mono
    (cutoff_tsupport_subset hh a) (cutoff_tsupport_subset hh b)

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridCover
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

lemma norm_sub_center_lt {h R : ℝ} {a : Index} {x : Base}
    (hx : x ∈ cell h R a) : ‖x-h • center a‖ < R*h := by
  change max |x.1-h*a.1| |x.2-h*a.2| < R*h
  exact max_lt hx.1 hx.2




theorem compact_subpatch_grid {K U : Set Base} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < C ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∃ s : Finset Index,
        (s.card : ℝ) ≤ C/h^2 ∧
        (∀ x ∈ K, ∃ a ∈ s, x ∈ cell h 1 a) ∧
        (∀ a ∈ s, h • center a ∈ U ∧ tsupport (cutoff h a) ⊆ U) := by
  classical
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨A,hA,hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨min 1 (δ/5),(2*A+5)^2,lt_min zero_lt_one (by positivity),
    min_le_left _ _,by positivity,?_⟩
  intro h hh hsmall
  have hh1 : h ≤ 1 := hsmall.trans (min_le_left _ _)
  have hδh : 4*h ≤ δ := by
    have ht : h ≤ δ/5 := hsmall.trans (min_le_right _ _)
    linarith
  let N : ℕ := ⌈A/h+1⌉₊
  have hNlo : A/h+1 ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) ≤ A/h+2 := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ A/h+1 by positivity)
    dsimp [N]
    linarith
  let s := (box N).filter (fun a => ∃ x ∈ K, x ∈ cell h 1 a)
  refine ⟨s,?_,?_,?_⟩
  · calc
      (s.card : ℝ) ≤ ((box N).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ ((2*A+5)/h)^2 := box_card_bound hA.le hh hh1 hNhi
      _ = (2*A+5)^2/h^2 := div_pow _ _ _
  · intro x hx
    have hnorm := hbound x hx
    have hcoords : |x.1| ≤ A ∧ |x.2| ≤ A :=
      ⟨(le_max_left _ _).trans hnorm,(le_max_right _ _).trans hnorm⟩
    obtain ⟨a,ha,hxa⟩ := finite_box_covers hh hNlo hcoords
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,x,hx,hxa⟩,hxa⟩
  · intro a ha
    obtain ⟨_,x,hx,hxa⟩ := Finset.mem_filter.mp ha
    have hxc : ‖x-h • center a‖ < h := by
      simpa using norm_sub_center_lt hxa
    constructor
    · apply hthick
      apply Metric.mem_cthickening_of_dist_le _ x δ K hx
      rw [dist_eq_norm,norm_sub_rev]
      linarith
    · intro y hy
      have hyc : ‖y-h • center a‖ < 3*h := norm_sub_center_lt (cutoff_tsupport_subset hh a hy)
      have hxy : ‖y-x‖ ≤ ‖y-h • center a‖+‖x-h • center a‖ := by
        simpa [dist_eq_norm,norm_sub_rev] using dist_triangle y (h • center a) x
      apply hthick
      apply Metric.mem_cthickening_of_dist_le _ x δ K hx
      rw [dist_eq_norm]
      linarith



theorem compact_subpatch_polynomial_grid {K U : Set Base}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ z₀ C : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < C ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ → ∃ s : Finset Index,
        (s.card : ℝ) ≤ C/z^12 ∧
        (∀ x ∈ K, ∃ a ∈ s, x ∈ cell (z^6) 1 a) ∧
        (∀ a ∈ s, z^6 • center a ∈ U ∧ tsupport (cutoff (z^6) a) ⊆ U) := by
  obtain ⟨h₀,C,hh₀,hh₀1,hC,hgrid⟩ := compact_subpatch_grid hK hU hKU
  refine ⟨h₀,C,hh₀,hh₀1,hC,fun z hz hzsmall => ?_⟩
  have hz1 : z ≤ 1 := hzsmall.trans hh₀1
  have hp : z^5 ≤ 1 := by simpa using pow_le_pow_left₀ hz.le hz1 5
  have hzpow : z^6 ≤ h₀ := by
    have hm := mul_le_mul_of_nonneg_left hp hz.le
    nlinarith [hm]
  obtain ⟨s,hcard,hcover,hsub⟩ := hgrid (z^6) (pow_pos hz _) hzpow
  refine ⟨s,?_,hcover,hsub⟩
  simpa only [← pow_mul] using hcard
end ClosedSurfaceR4.PhaseGrid

namespace ClosedSurfaceR4.PhaseGrid
open Set
attribute [local instance] Classical.propDecidable



theorem distinct_labels_on_intersection {h : ℝ} (hh : 0 < h)
    {a b : Index × Fin 3} (hab : a ≠ b) {x : Base}
    (ha : x ∈ tsupport (cutoff h a.1)) (hb : x ∈ tsupport (cutoff h b.1)) :
    phaseLabel a ≠ phaseLabel b := by
  intro he
  have hp := (Fintype.equivFin Label).injective he
  have hc : color 6 a.1 = color 6 b.1 := congrArg Prod.fst hp
  have hi : a.2 = b.2 := congrArg (fun p : Label => p.2) hp
  by_cases hcelleq : a.1 = b.1
  · exact hab (Prod.ext hcelleq hi)
  · exact (Set.disjoint_left.mp (cutoff_same_color_disjoint hh hcelleq hc)) ha hb


end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GlobalPartition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set Function Filter PhaseGeometry SmallModes RealModes PhaseGrid

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]



omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma refinedCutoff_tsupport_inner (p : M) {ψ : M → ℝ}
    (hsource : tsupport ψ ⊆ (chartAt Plane p).source)
    (s : Finset Index) (h : ℝ) (a : Index) :
    tsupport (refinedCutoff p ψ s h a) ⊆
      (chartCoordinates p) ⁻¹' tsupport (normalizedCutoff s h a) := by
  intro q hq
  have hqψ := refinedCutoff_tsupport_outer p ψ s h a hq
  have hc := (chartCoordinates_continuousOn p q (hsource hqψ)).continuousAt
    ((chartAt Plane p).open_source.mem_nhds (hsource hqψ))
  by_contra hn
  have heq := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hc
  have hz : refinedCutoff p ψ s h a =ᶠ[𝓝 q] 0 := by
    filter_upwards [heq] with x hx
    simp only [refinedCutoff,Pi.zero_apply,Function.comp_apply] at hx ⊢
    rw [hx,mul_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hq

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPartition
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

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

lemma finite_positive_threshold {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ i, z ≤ v i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image v)
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,Finset.min'_le s 1 (Finset.mem_insert_self _ _),?_⟩
  · have hm := s.min'_mem hs
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hm
    rcases hm with he | ⟨i,hi⟩
    · rw [he]; norm_num
    · rw [← hi]; exact hv i
  · intro i
    exact Finset.min'_le s (v i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasLabels
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]



omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
theorem atlas_distinct_labels_on_intersection (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (s : ι → Finset Index) {h : ℝ} (hh : 0 < h)
    {a b : ι × (Index × Fin 3)} (hab : a ≠ b) {q : M}
    (ha : q ∈ tsupport (refinedCutoff (p a.1) (ψ a.1) (s a.1) h a.2.1))
    (hb : q ∈ tsupport (refinedCutoff (p b.1) (ψ b.1) (s b.1) h b.2.1)) :
    atlasPhaseLabel a ≠ atlasPhaseLabel b := by
  intro he
  have hl := (Fintype.equivFin (AtlasPhaseLabel (ι := ι))).injective he
  have hi : a.1 = b.1 := congrArg (fun x : AtlasPhaseLabel (ι := ι) => x.1) hl
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  simp only at hi
  subst j
  have hab' : a ≠ b := fun he => hab (congrArg (fun x => (i,x)) he)
  have hca := normalizedCutoff_tsupport (s i) h a.1
    (refinedCutoff_tsupport_inner (p i) (hsource i) (s i) h a.1 ha)
  have hcb := normalizedCutoff_tsupport (s i) h b.1
    (refinedCutoff_tsupport_inner (p i) (hsource i) (s i) h b.1 hb)
  exact distinct_labels_on_intersection hh hab' hca hcb (congrArg (fun x : AtlasPhaseLabel (ι := ι) => x.2) hl)

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] {ι : Type*} [Fintype ι]



theorem finite_atlas_transition_bounds (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i)) :
    ∃ d L : ℝ, 0 < d ∧ 0 < L ∧ ∀ i j : ι,
      ∀ x ∈ coordinateChart (p i) '' (tsupport (ψ i) ∩ tsupport (ψ j)),
        d ≤ |coordDet (fderiv ℝ (coordinateTransition (p j) (p i)) x)| ∧
        ‖fderiv ℝ (coordinateTransition (p j) (p i)) x‖ ≤ L := by
  classical
  have hs (i : ι) : tsupport (ψ i) ⊆ (coordinateChart (p i)).source := by
    rw [coordinateChart_source]
    exact hsource i
  have hb (a : ι × ι) : ∃ d L : ℝ, 0 < d ∧ 0 < L ∧
      ∀ x ∈ coordinateChart (p a.1) '' (tsupport (ψ a.1) ∩ tsupport (ψ a.2)),
        d ≤ |coordDet (fderiv ℝ (coordinateTransition (p a.2) (p a.1)) x)| ∧
        ‖fderiv ℝ (coordinateTransition (p a.2) (p a.1)) x‖ ≤ L := by
    have hK := (hcompact a.1).inter_right (isClosed_tsupport (ψ a.2))
    exact coordinateTransition_compact_bounds (p a.2) (p a.1)
      (coordinateChart_compact_image hK (p a.1) (fun x hx => hs a.1 hx.1))
      (coordinateChart_image_overlap (p a.2) (p a.1)
        (fun x hx => hs a.1 hx.1) (fun x hx => hs a.2 hx.2))
  choose d L hd hL hbound using hb
  obtain ⟨d₀,hd₀,_,hle⟩ := finite_positive_threshold d hd
  refine ⟨d₀,1+∑ a, L a,hd₀,?_,?_⟩
  · have hn : 0 ≤ ∑ a, L a := Finset.sum_nonneg (fun a _ => le_of_lt (hL a))
    linarith
  · intro i j x hx
    refine ⟨(hle (i,j)).trans ((hbound (i,j) x hx).1),?_⟩
    have hsL : L (i,j) ≤ ∑ a, L a :=
      Finset.single_le_sum (fun a _ => le_of_lt (hL a)) (Finset.mem_univ (i,j))
    exact ((hbound (i,j) x hx).2).trans (by linarith)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


lemma phaseDerivative_linear_comp {φ : SmallModes.Base → SmallModes.Base}
    {x : SmallModes.Base} (hφ : DifferentiableAt ℝ φ x) (ξ : SmallModes.Base) :
    phaseDerivative (phaseLinear ξ ∘ φ) x = pullCovector (fderiv ℝ φ x) ξ := by
  have hd := ((phaseLinear ξ).hasFDerivAt.comp x hφ.hasFDerivAt).fderiv
  unfold phaseDerivative
  rw [hd]
  rfl



theorem actual_phase_differential (q p : M) (ξ : SmallModes.Base)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    phaseDerivative (atlasPhase q ξ ∘ (coordinateChart p).symm) x =
      pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ := by
  change phaseDerivative (phaseLinear ξ ∘ coordinateTransition q p) x = _
  have hc := ((coordinateTransition_smoothOn q p) x hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)
  exact phaseDerivative_linear_comp (hc.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ξ

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_apply_chart (q p : M) {a : M}
    (ha : a ∈ (coordinateChart p).source) :
    coordinateTransition q p (coordinateChart p a) = coordinateChart q a := by
  change coordinateChart q ((coordinateChart p).symm (coordinateChart p a)) = _
  rw [(coordinateChart p).left_inv ha]

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_mem_chart (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    coordinateChart p a ∈ (coordinateTransition q p).source := by
  constructor
  · exact (coordinateChart p).map_source hap
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rwa [(coordinateChart p).left_inv hap]



theorem actual_phase_margin_at {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source)
    (ξ : SmallModes.Base) {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateChart q a))
      (coordDeriv dy (coordinateMap F q) (coordinateChart q a)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) (coordinateChart p a))|)
    (hA : ‖fderiv ℝ (coordinateTransition q p) (coordinateChart p a)‖ ≤ L)
    (hB : realSecondTensor (coordinateMap F q) (coordinateChart q a) ≠ 0)
    (hmargin : ε*‖realSecondTensor (coordinateMap F q) (coordinateChart q a)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateChart q a)) (-ξ.2,ξ.1)‖) :
    ‖atlasPhaseCovector q p ξ a‖ ≤ 2*L*‖ξ‖ ∧
    d^2*ε/(4*L^2)*‖realSecondTensor (coordinateMap F p) (coordinateChart p a)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F p) (coordinateChart p a))
        (-(atlasPhaseCovector q p ξ a).2,(atlasPhaseCovector q p ξ a).1)‖ ∧
    Good (realSecondTensor (coordinateMap F p) (coordinateChart p a))
      (atlasPhaseCovector q p ξ a) ∧
    realSecondTensor (coordinateMap F p) (coordinateChart p a) ≠ 0 := by
  have hx := coordinateTransition_mem_chart q p hap haq
  have he := coordinateTransition_apply_chart q p hap
  have h := actual_chart_phase_margin hF q p hx ξ hd hL hε
    (by simpa only [he] using hD) hdet hA
    (by simpa only [he] using hB) (by simpa only [he] using hmargin)
  unfold atlasPhaseCovector
  rw [actual_phase_differential q p ξ hx]
  exact h

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasWeights
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]





omit [T2Space M] [CompactSpace M] in
theorem atlas_phase_weight_constants_with_catalog (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i))
    {ε C : ℝ} (hε : 0 < ε) (σ : Type*) :
    ∃ stock : Finset ℝ, ∃ W κ : ℝ, 0 < W ∧ 0 < κ ∧
      ∀ h : ℝ, 0 < h → ∀ s : ι → Finset Index,
      ∀ ξ : AtlasCellPhase (ι := ι) → SmallModes.Base,
      (∀ a, ‖ξ a‖ ≤ C) →
      ∀ (G : σ → M → Space),
      (∀ t, ContMDiff planeModel spaceModel ∞ (G t)) →
      (∀ t a q, atlasActive p ψ s h a q →
        atlasGram (G t) (p a.1) q ≠ 0 ∧ atlasSecondTensor (G t) (p a.1) q ≠ 0 ∧
        ε*‖atlasSecondTensor (G t) (p a.1) q‖ ≤
          ‖secondQuadratic (atlasSecondTensor (G t) (p a.1) q) (-(ξ a).2,(ξ a).1)‖) →
      ∃ w : AtlasCellPhase (ι := ι) → ℝ, (∀ a, w a ∈ stock) ∧
        (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        ∀ (t : σ) (a b : AtlasCellPhase (ι := ι)) (j : ι) (q : M),
          a ≠ b → atlasActive p ψ s h a q → atlasActive p ψ s h b q → q ∈ tsupport (ψ j) →
          κ*‖atlasSecondTensor (G t) (p j) q‖ ≤
            ‖secondQuadratic (atlasSecondTensor (G t) (p j) q)
              (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
               (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
          κ*‖atlasSecondTensor (G t) (p j) q‖ ≤
            ‖secondQuadratic (atlasSecondTensor (G t) (p j) q)
              (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
               (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
          Good (atlasSecondTensor (G t) (p j) q)
            (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
             w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q) ∧
          Good (atlasSecondTensor (G t) (p j) q)
            (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
             w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q) := by
  obtain ⟨d,L,hd,hL,hbound⟩ := finite_atlas_transition_bounds p ψ hsource hcompact
  let e := d^2*ε/(4*L^2)
  have he : 0 < e := div_pos (mul_pos (sq_pos_of_pos hd) hε)
    (mul_pos (by norm_num) (sq_pos_of_pos hL))
  obtain ⟨stock,W,κ,hW,hκ,hweights⟩ := quantitative_labeled_phase_lengths_with_catalog
    (ι := AtlasCellPhase (ι := ι)) (X := σ × (ι × M)) (n := 4)
    (C := 2*L*C) (atlasPhaseLabel (ι := ι)) he
  refine ⟨stock,W,κ,hW,hκ,?_⟩
  intro h hh s ξ hξ G hG hlocal
  let B : σ × (ι × M) → Fin 3 → RVec 4 := fun x =>
    atlasSecondTensor (G x.1) (p x.2.1) x.2.2
  let Ξ : AtlasCellPhase (ι := ι) → σ × (ι × M) → SmallModes.Base := fun a x =>
    atlasPhaseCovector (p a.1) (p x.2.1) (ξ a) x.2.2
  let active : AtlasCellPhase (ι := ι) → σ × (ι × M) → Prop := fun a x =>
    atlasActive p ψ s h a x.2.2 ∧ x.2.2 ∈ tsupport (ψ x.2.1)
  have hlabels : ∀ a b x, a ≠ b → active a x → active b x →
      atlasPhaseLabel a ≠ atlasPhaseLabel b := by
    intro a b x hab ha hb
    exact atlas_distinct_labels_on_intersection p ψ hsource s hh hab ha.1.2 hb.1.2
  have hdata : ∀ a x, active a x → B x ≠ 0 ∧ ‖Ξ a x‖ ≤ 2*L*C ∧
      e*‖B x‖ ≤ ‖secondQuadratic (B x) (-(Ξ a x).2,(Ξ a x).1)‖ := by
    intro a x hx
    have hqa : x.2.2 ∈ tsupport (ψ a.1) :=
      refinedCutoff_tsupport_outer (p a.1) (ψ a.1) (s a.1) h a.2.1 hx.1.2
    have hap : x.2.2 ∈ (coordinateChart (p a.1)).source := by
      rw [coordinateChart_source]; exact hsource a.1 hqa
    have hjp : x.2.2 ∈ (coordinateChart (p x.2.1)).source := by
      rw [coordinateChart_source]; exact hsource x.2.1 hx.2
    have hc := hbound x.2.1 a.1 (coordinateChart (p x.2.1) x.2.2)
      ⟨x.2.2,⟨hx.2,hqa⟩,rfl⟩
    have hl := hlocal x.1 a x.2.2 hx.1
    have hm := actual_phase_margin_at (hG x.1) (p a.1) (p x.2.1)
      hjp hap (ξ a) hd hL hε hl.1 hc.1 hc.2 hl.2.1 hl.2.2
    refine ⟨hm.2.2.2,?_,hm.2.1⟩
    exact hm.1.trans (mul_le_mul_of_nonneg_left (hξ a) (by positivity))
  obtain ⟨w,hstock,hw,hcross⟩ := hweights B Ξ active hlabels hdata
  refine ⟨w,hstock,hw,?_⟩
  intro t a b j q hab ha hb hqj
  exact hcross a b (t,j,q) hab ⟨ha,hqj⟩ ⟨hb,hqj⟩

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateInverse_mfderiv_injective (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    Function.Injective (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) := by
  have hxt : x ∈ (coordinateChart p).target := by rwa [coordinateChart_target]
  have hs : coordinateInverse p x ∈ (coordinateChart p).source := by
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).map_target hxt
  have hi := ((coordinateInverse_smoothOn p) x hx).contMDiffAt
    ((coordinateDomain_open p).mem_nhds hx)
  have hc := ((coordinateChart_smoothOn p) (coordinateInverse p x) hs).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hs)
  have he : coordinateChart p ∘ coordinateInverse p =ᶠ[𝓝 x] id := by
    filter_upwards [(coordinateDomain_open p).mem_nhds hx] with y hy
    change coordinateChart p (coordinateInverse p y) = y
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).right_inv (by rwa [coordinateChart_target])
  have hd : (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) (coordinateInverse p x)).comp
      (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) =
      ContinuousLinearMap.id ℝ SmallModes.Base := by
    rw [← mfderiv_comp x (hc.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp)),
      he.mfderiv_eq,mfderiv_id]
    rfl
  intro v w hv
  have hvw := congrArg (mfderiv planeModel 𝓘(ℝ,SmallModes.Base)
    (coordinateChart p) (coordinateInverse p x)) hv
  have hdv := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L v) hd
  have hdw := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L w) hd
  exact hdv.symm.trans (hvw.trans hdw)

lemma coordinateMetric_positive (g : SmoothMetric M) (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    0 < coordinateMetric g p x 0 ∧
      0 < coordinateMetric g p x 0 * coordinateMetric g p x 2 - (coordinateMetric g p x 1)^2 := by
  apply (tensor_positive_iff _).mp
  intro v hv
  rw [coordinateMetric_evaluate]
  exact metricPullback_pos g (coordinateInverse_mfderiv_injective p hx) hv



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter Bundle Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
lemma coordinateInverse_mfderiv_right (p : M) {q : M}
    (hq : q ∈ (coordinateChart p).source) :
    (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) (coordinateChart p q)).comp
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q) =
    ContinuousLinearMap.id ℝ (TangentSpace planeModel q) := by
  have hx : coordinateChart p q ∈ coordinateDomain p := by
    rw [← coordinateChart_target]
    exact (coordinateChart p).map_source hq
  have hi := ((coordinateInverse_smoothOn p) _ hx).contMDiffAt
    ((coordinateDomain_open p).mem_nhds hx)
  have hc := ((coordinateChart_smoothOn p) q hq).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hq)
  have he : coordinateInverse p ∘ coordinateChart p =ᶠ[𝓝 q] id := by
    filter_upwards [(coordinateChart p).open_source.mem_nhds hq] with a ha
    change coordinateInverse p (coordinateChart p a) = a
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).left_inv ha
  rw [← mfderiv_comp q (hi.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp)),
    he.mfderiv_eq,mfderiv_id]
  try rfl

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
lemma coordinateMetric_pullback_chart (g : SmoothMetric M) (p : M) {q : M}
    (hq : q ∈ (coordinateChart p).source) (v w : TangentSpace planeModel q) :
    PhaseMean.evaluate (coordinateMetric g p (coordinateChart p q))
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q v)
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q w) = g.inner q v w := by
  let D : TangentSpace planeModel q →L[ℝ] SmallModes.Base :=
    mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q
  change PhaseMean.evaluate (coordinateMetric g p (coordinateChart p q)) (D v) (D w) =
    g.inner q v w
  rw [coordinateMetric_evaluate]
  have hinv : coordinateInverse p (coordinateChart p q) = q := by
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).left_inv hq
  let I : SmallModes.Base →L[ℝ] TangentSpace planeModel q :=
    mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) (coordinateChart p q)
  have hcomp : I.comp D = ContinuousLinearMap.id ℝ (TangentSpace planeModel q) :=
    coordinateInverse_mfderiv_right p hq
  have hv : I (D v) = v := congrArg (fun L => L v) hcomp
  have hw : I (D w) = w := congrArg (fun L => L w) hcomp
  change g.inner (coordinateInverse p (coordinateChart p q)) (I (D v)) (I (D w)) =
    g.inner q v w
  calc
    _ = g.inner (coordinateInverse p (coordinateChart p q)) v w :=
      congrArg₂ (fun a b : TangentSpace planeModel q =>
        g.inner (coordinateInverse p (coordinateChart p q)) a b) hv hw
    _ = g.inner q v w := congrArg (fun r => g.inner r v w) hinv

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AnchoredGridCover
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial grids with every selected cell anchored on the compact set. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGrid

 theorem compact_anchored_polynomial_grid {K : Set Base} (hK : IsCompact K) :
    ∃ z₀ C : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < C ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ → ∃ s : Finset Index,
        (s.card : ℝ) ≤ C/z^12 ∧ K ⊆ coverRegion s (z^6) ∧
        (∀ a ∈ s, ∃ x ∈ K, ‖x-z^6 • center a‖ ≤ 3*z^6) := by
  classical
  obtain ⟨z₀,C,hz₀,hz₀1,hC,hgrid⟩ :=
    compact_subpatch_polynomial_grid hK isOpen_univ (subset_univ _)
  refine ⟨z₀,C,hz₀,hz₀1,hC,?_⟩
  intro z hz hzsmall
  obtain ⟨s,hcard,hcover,_⟩ := hgrid z hz hzsmall
  let t := s.filter (fun a => ∃ x ∈ K, x ∈ cell (z^6) 1 a)
  refine ⟨t,?_,?_,?_⟩
  · exact (show (t.card : ℝ) ≤ (s.card : ℝ) by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  · intro x hx
    obtain ⟨a,ha,hxa⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨ha,x,hx,hxa⟩,hxa⟩⟩
  · intro a ha
    obtain ⟨_,x,hx,hxa⟩ := Finset.mem_filter.mp ha
    refine ⟨x,hx,?_⟩
    have hd := norm_sub_center_lt hxa
    have hp := pow_pos hz 6
    nlinarith

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three independent coordinates of a symmetric surface tensor, with
an explicit continuous linear reconstruction into the full tensor fiber. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberNormed
local instance coordinateFiberSpace_r2e3548_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberToThree_apply (B : TensorFiber) (k : Fin 3) :
    fiberToThree B k = B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k)) := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberSpace
local instance chartReadSectionNormed_r2e3548_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r2e3548_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorChartRead_on_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorChartRead i u (chart (i : M) p) = fiberToThree (A.bundleComponent A.tensorTriv i u p) := by
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp]
  simp only [one_pow, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r2e3548_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GoodSmoothingAtlas
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smoothing atlas subordinate to actual good-phase neighborhoods. -/
noncomputable section
open Set Manifold Filter TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_chart_symm (F : M → Space) (p : M) (x : SmallModes.Base) :
    coordinateMap F p x = spaceCoordinates (F ((chart p).symm (planeCoordinateIsometry.symm x))) := rfl

variable [T2Space M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [T2Space M] [CompactSpace M] in
/-- Locally constant outer cutoffs identify the entire coordinate germ on
the original weight support, and hence every derivative used by the phases. -/
lemma vectorPlaneRead_eventually_coordinateMap
    (F : M → Space) (i : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))] coordinateMap F (i : M) := by
  let x := planeCoordinateIsometry (chart (i : M) p)
  let inv : SmallModes.Base → M := fun z => (chart (i : M)).symm (planeCoordinateIsometry.symm z)
  have hpS := A.weight_support i hp
  have hinv : inv x = p := by
    dsimp [inv,x]
    rw [LinearIsometryEquiv.symm_apply_apply,(chart (i : M)).left_inv hpS]
  have hc : ContinuousAt inv x := by
    apply ContinuousAt.comp
    · apply (chart (i : M)).continuousAt_symm
      simpa only [x,LinearIsometryEquiv.symm_apply_apply] using (chart (i : M)).map_source hpS
    · exact planeCoordinateIsometry.symm.continuous.continuousAt
  have ht : Tendsto inv (𝓝 x) (𝓝 p) := by simpa only [ContinuousAt,hinv] using hc
  have ho : ∀ᶠ z in 𝓝 x, A.outer i (inv z) = 1 := (houter p hp).comp_tendsto ht
  have htarget : ∀ᶠ z in 𝓝 x,
      planeCoordinateIsometry.symm z ∈ (chart (i : M)).target :=
    ((chart (i : M)).open_target.preimage planeCoordinateIsometry.symm.continuous).mem_nhds
      (by simpa only [Set.mem_preimage,x,LinearIsometryEquiv.symm_apply_apply] using
        (chart (i : M)).map_source hpS)
  filter_upwards [ho,htarget] with z hz htgt
  change spaceCoordinates (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm z)) = _
  rw [localize,indicator_of_mem htgt]
  change spaceCoordinates (A.outer i (inv z)^2 • F (inv z)) = _
  rw [hz,one_pow,one_smul]
  exact (coordinateMap_chart_symm F (i : M) z).symm

end SmoothingAtlas

end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricAtlasReference
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth metric section gives the reference tensor used by
the compact good-phase construction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean
open JetPolynomial (planeCoordinateIsometry)
open JetPolynomial.Perturbation (modeSupport)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualSmul
local instance metricReferenceSectionNormed_r2e3548_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_r2e3548_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metric_inner_smooth (g : SmoothMetric M) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (g.inner p)) := g.contMDiff

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberSpace
local instance metricReferenceSectionNormed_r2e3548_2 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_r2e3548_2 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorComponent_metric (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : Plane) :
    A.bundleComponent A.tensorTriv i g.inner p v w =
      evaluate (coordinateMetric g (i : M) (coordinateChart (i : M) p))
        (planeCoordinates v) (planeCoordinates w) := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  have hp' : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source, chart_source] using hp
  have hc := A.tensorComponent_tangentCoordinates i g.inner hp
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w)
  simp only [Trivialization.continuousLinearMapAt_symmL _ ht] at hc
  have hm := coordinateMetric_pullback_chart g (i : M) hp'
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w)
  rw [A.coordinateChart_tangentCoordinates i hp] at hm
  change evaluate (coordinateMetric g (i : M) (coordinateChart (i : M) p))
      (planeCoordinates
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)))
      (planeCoordinates
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w))) =
      g.inner p
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w) at hm
  simp only [Trivialization.continuousLinearMapAt_symmL _ ht] at hm
  exact hc.trans hm.symm

lemma tensorPlaneRead_metric_on_weight (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorPlaneRead i g.inner (planeCoordinateIsometry (chart (i : M) p)) =
      coordinateMetric g (i : M) (coordinateChart (i : M) p) := by
  change A.tensorChartRead i g.inner
    (planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (i : M) p))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, A.tensorChartRead_on_weight i g.inner hp]
  ext k
  rw [fiberToThree_apply, A.tensorComponent_metric g i (A.weight_support i hp)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

variable [CompactSpace M]

lemma tensorPlaneRead_metric (g : SmoothMetric M) (i : A.centers)
    {x : SmallModes.Base} (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.tensorPlaneRead i g.inner x = coordinateMetric g (i : M) x := by
  change x ∈ planeCoordinateIsometry '' ((chart (i : M)) '' tsupport (A.weight i)) at hx
  rcases hx with ⟨y, ⟨p, hp, rfl⟩, rfl⟩
  exact A.tensorPlaneRead_metric_on_weight g i hp

lemma tensorPlaneRead_metric_smooth (g : SmoothMetric M) (i : A.centers) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i g.inner) :=
  A.tensorPlaneRead_smooth i (metric_inner_smooth g)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact positive metric range and global first-order bounds for atlas readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadBoundsFiberNormed
local instance metricReadBoundsFiberSpace_r2e3548_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricReadBoundsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadBoundsFiberNormed
local instance metricReadBoundsFiberSpace_r2e3548_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricReadBoundsDualSmul_r2e3548_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricReadBoundsSectionNormed_r2e3548_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadBoundsSectionSpace_r2e3548_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metricReadSupport_domain (i : A.centers) :
    (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coordinateDomain (i : M) := by
  rintro x ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hs : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
  rw [← coordinateChart_target]
  exact (coordinateChart (i : M)).map_source hs

theorem metric_plane_read_bounds (g : SmoothMetric M) :
    ∃ T : Set PhaseMean.Tensor, ∃ B : ℝ, IsCompact T ∧
      (∀ H ∈ T, 0 < H 0) ∧ (∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) ∧ 1 ≤ B ∧
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        A.tensorPlaneRead i g.inner x ∈ T) ∧
      (∀ i x, ‖A.tensorPlaneRead i g.inner x‖ ≤ B) ∧
      (∀ i x y, ‖A.tensorPlaneRead i g.inner y-A.tensorPlaneRead i g.inner x‖ ≤ B*‖y-x‖) := by
  classical
  let T : Set PhaseMean.Tensor := ⋃ i : A.centers,
    A.tensorPlaneRead i g.inner '' (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)
  have hT : IsCompact T := isCompact_iUnion (fun i =>
    (modeSupport (A.chartWeightCompact i)).isCompact.image (A.tensorPlaneRead_metric_smooth g i).continuous)
  have hpos (H : PhaseMean.Tensor) (hH : H ∈ T) :
      0 < H 0 ∧ 0 < H 0*H 2-(H 1)^2 := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hH
    rw [A.tensorPlaneRead_metric g i hx]
    exact coordinateMetric_positive g (i : M) (A.metricReadSupport_domain i hx)
  obtain ⟨C,hC,hbound⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain 1 g.contMDiff
  choose D hD hd using fun i : A.centers => A.tensorPlaneRead_bound i 1
  let B : ℝ := 1+∑ i : A.centers, D i*C
  have hB : 1 ≤ B := by
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg (hD i) hC)
    change 1 ≤ 1+∑ i : A.centers, D i*C
    linarith
  have hb (i : A.centers) : WeightedEstimates.WeightedBound univ 1 1 B (A.tensorPlaneRead i g.inner) := by
    apply (hd i g.inner 1 C zero_lt_one le_rfl hC g.contMDiff hbound).mono_const
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun i _ => mul_nonneg (hD i) hC) (Finset.mem_univ i)
    change D i*C ≤ 1+∑ i : A.centers, D i*C
    linarith
  refine ⟨T,B,hT,fun H hH => (hpos H hH).1,fun H hH => (hpos H hH).2,hB,
    fun i x hx => mem_iUnion.mpr ⟨i,mem_image_of_mem _ hx⟩,
    fun i x => (hb i).norm_le (mem_univ x),?_⟩
  intro i x y
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) _ _
    (convex_univ : Convex ℝ (univ : Set SmallModes.Base)) (mem_univ x) (mem_univ y)
  · intro a _
    exact (A.tensorPlaneRead_metric_smooth g i).differentiable (by simp) a
  · intro a _
    have hh := (hb i).deriv_le zero_lt_one (le_refl 1) (mem_univ a)
    simpa only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AnchoredAtlasPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase catalogs for a fixed smoothing atlas, using geometry only on its weight supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates PhaseGeometry PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma readJetBall_self (z : ℝ) {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F) :
    A.ReadJetBall z F F := by
  refine ⟨hF,fun i x hx => ?_⟩
  simp only [sub_self,norm_zero]
  exact ⟨by positivity,by positivity⟩

omit [CompactSpace M] in
lemma read_gram_eq_atlas (F : M → Space) (i : A.centers)
    (houter : ∀ p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    NormalFrame.gramDet
      (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) (coordinateChart (i : M) p)).1
      (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) (coordinateChart (i : M) p)).2 =
      atlasGram F (i : M) p := by
  have he := (A.vectorPlaneRead_eventually_coordinateMap F i houter hp).fderiv_eq (𝕜 := ℝ)
  change NormalFrame.gramDet
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p)) SmallModes.dx)
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p)) SmallModes.dy) = _
  exact
    congrArg (fun L : SmallModes.Base →L[ℝ] RVec 4 => NormalFrame.gramDet (L SmallModes.dx) (L SmallModes.dy)) he

omit [CompactSpace M] in
lemma read_second_eq_atlas (F : M → Space) (i : A.centers)
    (houter : ∀ p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (coordinateChart (i : M) p) =
      atlasSecondTensor F (i : M) p :=
  (realSecondTensor_eventuallyEq (A.vectorPlaneRead_eventually_coordinateMap F i houter hp)).eq_of_nhds

theorem anchored_atlas_phases_oai (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ phaseStock : Finset PhaseBasis, ∃ weightStock : Finset ℝ,
    ∃ z₀ K C ε W κ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < K ∧ 1 ≤ C ∧
      0 < ε ∧ 0 < W ∧ 0 < κ ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∃ (s : A.centers → Finset Index) (P : ∀ i, (s i) → PhaseBasis)
      (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
      (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ i a, P i a ∈ phaseStock) ∧ (∀ a, w a ∈ weightStock) ∧
      (∑ i, ((s i).card : ℝ)) ≤ K/z^12 ∧
      (∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (s i) (z^6)) ∧
      (∀ i a j, ξ (i,a.val,j) = (P i a).ξ j ∧
        ‖(P i a).ξ j‖ ≤ C ∧ ‖(P i a).Q j‖ ≤ C) ∧
      (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
      (∀ G, A.ReadJetBall z F G → ∀ i (a : s i) x,
        x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        x ∈ tsupport (cutoff (z^6) a.val) →
        c/4 ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).2 ∧
        b/2 ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ∧ ∀ j,
          ε/2 ≤ (P i a).Q j (A.tensorPlaneRead i g.inner x) ∧
          (ε/4)*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤
            ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x)
              (-((P i a).ξ j).2,((P i a).ξ j).1)‖ ∧
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x) ((P i a).ξ j)) ∧
      (∀ G, A.ReadJetBall z F G →
        AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s (z^6) κ ξ w G) := by
  classical
  obtain ⟨T,L,hT,hT0,hTd,hL,hTrange,_,hLip⟩ := A.metric_plane_read_bounds g
  obtain ⟨stock,ε,C,δ,z₁,W₁,κ₁,hε,hC,hδ,hz₁,hz₁1,_hW₁,_hκ₁,hselect⟩ :=
    anchored_polynomial_grid_phases hT hT0 hTd R c B b L hc hB hb (zero_le_one.trans hL)
  obtain ⟨weightStock,W,κ,hW,hκ,hweight⟩ :=
    atlas_phase_weight_constants_with_catalog (fun i : A.centers => (i : M)) A.weight
      (fun i => by simpa only [chart_source] using A.weight_support i)
      (fun i => (isClosed_tsupport _).isCompact) (C := C)
      (by positivity : 0 < ε/4) (M → Space)
  choose zi Ki hzi hzi1 hKi hgrid using fun i : A.centers =>
    compact_anchored_polynomial_grid (modeSupport (A.chartWeightCompact i)).isCompact
  obtain ⟨z₂,hz₂,hz₂1,hz₂i⟩ := finite_positive_threshold zi hzi
  let K : ℝ := 1+∑ i, Ki i
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => (hKi i).le)
    change 0 < 1+∑ i : A.centers, Ki i
    linarith
  refine ⟨stock,weightStock,min z₁ z₂,K,C,ε,W,κ,lt_min hz₁ hz₂,
    (min_le_left _ _).trans hz₁1,hK,hC,hε,hW,hκ,?_⟩
  intro z hz hzsmall F hF hFb hFm
  choose s hcard hcover hanchors using fun i : A.centers =>
    hgrid i z hz ((hzsmall.trans (min_le_right _ _)).trans (hz₂i i))
  have hchoose (i : A.centers) := hselect z hz (hzsmall.trans (min_le_left _ _))
    (spaceCoordinates ∘ A.vectorPlaneRead i F)
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) (hFb i)
    (A.tensorPlaneRead i g.inner) (hLip i) (s i) (by
      intro a ha
      obtain ⟨x,hx,hd⟩ := hanchors i a ha
      exact ⟨x,hd,(hFm i x hx).1,(hFm i x hx).2.1,(hFm i x hx).2.2,hTrange i x hx⟩)
  choose P wlocal hPstock hPB hwlocal hpoint hlocalPair using hchoose
  let ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base := fun a =>
    if ha : a.2.1 ∈ s a.1 then (P a.1 ⟨a.2.1,ha⟩).ξ a.2.2 else SmallModes.dx
  have hξ (a : AtlasCellPhase (ι := A.centers)) : ‖ξ a‖ ≤ C := by
    dsimp [ξ]
    split_ifs with ha
    · exact (hPB a.1 ⟨a.2.1,ha⟩ a.2.2).1
    · simpa [SmallModes.dx,Prod.norm_def] using hC
  have hpt (G : M → Space) (hG : A.ReadJetBall z F G) (i : A.centers) (a : s i)
      (x : SmallModes.Base) (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
      (ha : x ∈ tsupport (cutoff (z^6) a.val)) :=
    hpoint i a x (spaceCoordinates ∘ A.vectorPlaneRead i G) (A.tensorPlaneRead i g.inner x)
      ha (hG.2 i x hx).1 (hG.2 i x hx).2 (by simpa using hδ.le)
  let family : (M → Space) → M → Space := fun G => if A.ReadJetBall z F G then G else F
  have hfamily (G : M → Space) : A.ReadJetBall z F (family G) := by
    dsimp [family]
    split_ifs with h
    · exact h
    · exact A.readJetBall_self z hF
  have hmarg (G : M → Space) (a : AtlasCellPhase (ι := A.centers)) (p : M)
      (ha : atlasActive (fun i : A.centers => (i : M)) A.weight s (z^6) a p) :
      atlasGram (family G) (a.1 : M) p ≠ 0 ∧ atlasSecondTensor (family G) (a.1 : M) p ≠ 0 ∧
      (ε/4)*‖atlasSecondTensor (family G) (a.1 : M) p‖ ≤
        ‖secondQuadratic (atlasSecondTensor (family G) (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖ := by
    have hp := refinedCutoff_tsupport_outer (a.1 : M) (A.weight a.1) (s a.1) (z^6) a.2.1 ha.2
    have hx : coordinateChart (a.1 : M) p ∈
        (modeSupport (A.chartWeightCompact a.1) : Set SmallModes.Base) :=
      ⟨chart (a.1 : M) p,⟨p,hp,rfl⟩,rfl⟩
    have hcutt := normalizedCutoff_tsupport (s a.1) (z^6) a.2.1
      (refinedCutoff_tsupport_inner (a.1 : M)
        (by simpa only [chart_source] using A.weight_support a.1) (s a.1) (z^6) a.2.1 ha.2)
    have hh := hpt (family G) (hfamily G) a.1 ⟨a.2.1,ha.1⟩ _ hx hcutt
    rw [A.read_gram_eq_atlas (family G) a.1 (houter a.1) hp,
      A.read_second_eq_atlas (family G) a.1 (houter a.1) hp] at hh
    refine ⟨ne_of_gt ((by positivity : 0 < c/4).trans_le hh.1),
      norm_pos_iff.mp ((half_pos hb).trans_le hh.2.1),?_⟩
    simpa only [ξ,dite_eq_left ha.1] using (hh.2.2 a.2.2).2.1
  obtain ⟨w,hwStock,hw,hpairs⟩ := hweight (z^6) (pow_pos hz _) s ξ hξ family
    (fun G => (hfamily G).1) hmarg
  refine ⟨s,P,ξ,w,hPstock,hwStock,?_,hcover,?_,hw,hpt,?_⟩
  · calc
      (∑ i, ((s i).card : ℝ)) ≤ ∑ i, Ki i/z^12 := Finset.sum_le_sum (fun i _ => hcard i)
      _ = (∑ i, Ki i)/z^12 := (Finset.sum_div _ _ _).symm
      _ ≤ K/z^12 := div_le_div_of_nonneg_right (by
        change (∑ i : A.centers, Ki i) ≤ 1+∑ i : A.centers, Ki i
        linarith) (pow_pos hz _).le
  · intro i a j
    exact ⟨by simp only [ξ,dite_eq_left a.property],hPB i a j⟩
  · intro G hG a d j p had ha hd hp
    have he : family G = G := ite_eq_left hG
    simpa only [he] using hpairs G a d j p had ha hd hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases_oai.{u_1}
