-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:19.346196+00:00
-- url     : https://prove2.me/submissions/4b8f4f0d-649b-4371-b1b5-cdacaf4f157d

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_linear_unperturbed_solver
import Theorems.Thm_OAI_ClosedSurfaceR4_PhaseMean_polynomial_linear_mean_budgets

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseGrid
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

end ClosedSurfaceR4.PhaseGrid

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

end ClosedSurfaceR4.WeightedEstimates

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
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

namespace ClosedSurfaceR4.WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma WeightedBound.real_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
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

end ClosedSurfaceR4.WeightedEstimates

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

lemma coordDeriv_comp_linear {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v p : Base) :
    coordDeriv v (F ∘ e) p = coordDeriv (e v) F (e p) := by
  simp only [coordDeriv, fderiv_comp p (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) e.differentiableAt,
    e.fderiv, ContinuousLinearMap.comp_apply]

lemma second_coordDeriv_comp_linear {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v w p : Base) :
    coordDeriv v (coordDeriv w (F ∘ e)) p =
      coordDeriv (e v) (coordDeriv (e w) F) (e p) := by
  have he : coordDeriv w (F ∘ e) = (coordDeriv (e w) F) ∘ e := by
    funext q; exact coordDeriv_comp_linear hF e w q
  rw [he, coordDeriv_comp_linear (contDiff_real_coordDeriv hF (e w))]


lemma realSecondForm_quadratic {F : RField 4} (hF : ContDiff ℝ ∞ F) (v p : Base) :
    realSecondForm F v v p = secondQuadratic (realSecondTensor F p) v := by
  unfold realSecondForm
  rw [second_coordDeriv_quadratic hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [secondQuadratic, realSecondTensor, realSecondForm]

lemma realSecondForm_comp_linear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v w p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (e p)) (coordDeriv dy F (e p)) ≠ 0)
    (hdet : (e dx).1 * (e dy).2 - (e dx).2 * (e dy).1 ≠ 0) :
    realSecondForm (F ∘ e) v w p = realSecondForm F (e v) (e w) (e p) := by
  unfold realSecondForm
  rw [coordDeriv_comp_linear hF, coordDeriv_comp_linear hF, second_coordDeriv_comp_linear hF,
    coordDeriv_eq_basis F (e dx), coordDeriv_eq_basis F (e dy), realNormalPart_change_basis]
  · exact hD
  · exact hdet

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
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



lemma gramDet_ne_zero_of_injective (A : Base →L[ℝ] RVec 4) (hA : Function.Injective A) :
    NormalFrame.gramDet (A dx) (A dy) ≠ 0 := by
  let X := A dx
  let Y := A dy
  have hX : X ≠ 0 := by
    intro hx
    have he : dx = 0 := hA (by simpa [X] using hx)
    exact one_ne_zero (congrArg Prod.fst he)
  have hXX : X ⬝ᵥ X ≠ 0 := (dotProduct_self_eq_zero).not.mpr hX
  intro hD
  let v : Base := -(X ⬝ᵥ Y) • dx + (X ⬝ᵥ X) • dy
  have hv : A v = -(X ⬝ᵥ Y) • X + (X ⬝ᵥ X) • Y := by simp [v,X,Y]
  have hsq : A v ⬝ᵥ A v = (X ⬝ᵥ X) * NormalFrame.gramDet X Y := by
    rw [hv]
    simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hz : A v = 0 := dotProduct_self_eq_zero.mp (by rw [hsq]; change _ * NormalFrame.gramDet (A dx) (A dy) = 0; rw [hD,mul_zero])
  have hv0 : v = 0 := hA (by simpa using hz)
  have hy0 := congrArg Prod.snd hv0
  exact hXX (by simpa [v,dx,dy] using hy0)

lemma injective_of_gramDet_ne_zero (A : Base →L[ℝ] RVec 4)
    (hD : NormalFrame.gramDet (A dx) (A dy) ≠ 0) : Function.Injective A := by
  have hz : ∀ v : Base, A v = 0 → v = 0 := by
    intro v hv
    have hb : A v = v.1 • A dx + v.2 • A dy := by
      calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
           _ = _ := by simp
    have hx := congrArg (fun W => A dx ⬝ᵥ W) hv
    have hy := congrArg (fun W => A dy ⬝ᵥ W) hv
    rw [hb] at hx hy
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      dotProduct_comm (A dy) (A dx)] at hx hy
    have hvx : v.1 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.1 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dy ⬝ᵥ A dy) * hx - (A dx ⬝ᵥ A dy) * hy)).resolve_left hD
    have hvy : v.2 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.2 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dx ⬝ᵥ A dx) * hy - (A dx ⬝ᵥ A dy) * hx)).resolve_left hD
    exact Prod.ext hvx hvy
  intro p q hpq
  exact sub_eq_zero.mp (hz (p-q) (by simpa using sub_eq_zero.mpr hpq))

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma contDiffAt_realSecondTensor {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    ContDiffAt ℝ ∞ (realSecondTensor F) p := by
  have hx := (contDiff_real_coordDeriv hF dx).contDiffAt (x := p)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffAt (x := p)
  have hb (v w : Base) : ContDiffAt ℝ ∞ (fun q => realSecondForm F v w q) p :=
    contDiffAt_realNormalPart hx hy
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hb dx dx
  · exact hb dx dy
  · exact hb dy dy

lemma continuous_gramDet_field {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p => NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p)) := by
  have hx := (contDiff_real_coordDeriv hF dx).continuous
  have hy := (contDiff_real_coordDeriv hF dy).continuous
  unfold NormalFrame.gramDet dotProduct
  fun_prop

lemma good_eventually {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} {p : X}
    (hB : ContinuousAt B p) (hξ : ContinuousAt ξ p) (hg : Good (B p) (ξ p)) :
    ∀ᶠ q in 𝓝 p, Good (B q) (ξ q) := by
  have ho : IsOpen {z : (Fin 3 → RVec n) × Base | Good z.1 z.2} :=
    isOpen_good continuous_fst continuous_snd
  exact (hB.prodMk hξ).preimage_mem_nhds (ho.mem_nhds hg)




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.instVAddIntReal_solutions
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


lemma phaseLinear_apply (ξ x : SmallModes.Base) : phaseLinear ξ x = ξ.1*x.1+ξ.2*x.2 := rfl

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridBumps
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



theorem cutoff_derivative_bounds : ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ (h : ℝ), 0 < h → ∀ (a : Index) (j : ℕ) (x : Base),
      ‖iteratedFDeriv ℝ j (cutoff h a) x‖ ≤ C j / h^j := by
  have hbound (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Base, ‖iteratedFDeriv ℝ j (gridBump : Base → ℝ) x‖ ≤ C := by
    have hc := (gridBump.contDiff (n := ⊤)).continuous_iteratedFDeriv (m := j) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    obtain ⟨x₀,hx₀⟩ := hc.norm.exists_forall_ge_of_hasCompactSupport
      ((gridBump.hasCompactSupport.iteratedFDeriv j).norm)
    exact ⟨_, norm_nonneg _, hx₀⟩
  choose C hC hbound using hbound
  refine ⟨C,hC,fun h hh a j x => ?_⟩
  let L : Base →L[ℝ] Base := h⁻¹ • ContinuousLinearMap.id ℝ Base
  let f : Base → ℝ := fun x => gridBump (x-center a)
  have hf : ContDiff ℝ ∞ f := gridBump.contDiff.comp (contDiff_id.sub contDiff_const)
  have he : cutoff h a = f ∘ L := rfl
  rw [he,L.iteratedFDeriv_comp_right hf x (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
  have hd : ‖iteratedFDeriv ℝ j f (L x)‖ ≤ C j := by
    simpa [f, iteratedFDeriv_comp_sub] using hbound j (L x-center a)
  have hL : ‖L‖ = h⁻¹ := by simp [L, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ∏ _ : Fin j, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C j * h⁻¹ ^ j := by simp only [hL, Finset.prod_const, Finset.card_univ, Fintype.card_fin]; gcongr
    _ = C j / h^j := by rw [inv_pow, div_eq_mul_inv]


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
attribute [local instance] Classical.propDecidable


theorem active_cutoff_count {h : ℝ} (hh : 0 < h) (s : Finset Index) (x : Base) :
    (s.filter (fun a => x ∈ tsupport (cutoff h a))).card ≤ 36 := by
  classical
  let t := s.filter (fun a => x ∈ tsupport (cutoff h a))
  have hinj : Set.InjOn (color 6) (t : Set Index) := by
    intro a ha b hb he
    by_contra hne
    exact (Set.disjoint_left.mp (cutoff_same_color_disjoint hh hne he))
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have heq := Finset.card_image_of_injOn hinj
  have hb := Finset.card_le_univ (t.image (color 6))
  rw [heq] at hb
  simpa using hb

end ClosedSurfaceR4.PhaseGrid

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridPartition
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
open Set Function WeightedEstimates
attribute [local instance] Classical.propDecidable


lemma cutoff_weighted_bounds : ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    ∀ (h : ℝ), 0 < h → ∀ (a : Index) (m : ℕ),
      WeightedBound univ h m (C m) (cutoff h a) := by
  obtain ⟨c,hc,hbound⟩ := cutoff_derivative_bounds
  let C (m : ℕ) := 1 + ∑ j ∈ Finset.range (m+1), c j
  have hC (m : ℕ) : 1 ≤ C m := by
    have hs : 0 ≤ ∑ j ∈ Finset.range (m+1), c j := Finset.sum_nonneg (fun j _ => hc j)
    dsimp [C] <;> linarith
  refine ⟨C,hC,fun h hh a m j hj x _ => ?_⟩
  rw [iteratedFDerivWithin_univ]
  have hmul := mul_le_mul_of_nonneg_left (hbound h hh a j x) (pow_nonneg hh.le j)
  have hle : c j ≤ C m := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m+1)) => hc i)
      (show j ∈ Finset.range (m+1) by simp; omega)
    dsimp [C] <;> linarith
  apply le_trans _ hle
  convert hmul using 1
  all_goals try with_reducible_and_instances rfl
  field_simp



lemma weighted_sum_bounded_overlap {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C)
    {m : ℕ} (s : Finset Index) (f : Index → Base → ℝ)
    (hf : ∀ a ∈ s, ContDiff ℝ ∞ (f a))
    (hsupp : ∀ a ∈ s, tsupport (f a) ⊆ tsupport (cutoff h a))
    (hb : ∀ a ∈ s, WeightedBound univ h m C (f a)) :
    WeightedBound univ h m (36*C) (fun x => ∑ a ∈ s, f a x) := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ, iteratedFDeriv_sum (fun a ha =>
    (hf a ha).of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))]
  let t := s.filter (fun a => x ∈ tsupport (cutoff h a))
  have ht : t ⊆ s := Finset.filter_subset _ _
  have hz (a : Index) (ha : a ∈ s) (hat : a ∉ t) :
      iteratedFDeriv ℝ j (f a) x = 0 := by
    apply notMem_support.mp
    intro hmem
    have hx := hsupp a ha (support_iteratedFDeriv_subset j hmem)
    exact hat (Finset.mem_filter.mpr ⟨ha,hx⟩)
  have he : (∑ a ∈ t, iteratedFDeriv ℝ j (f a) x) =
      ∑ a ∈ s, iteratedFDeriv ℝ j (f a) x :=
    Finset.sum_subset ht (fun a ha hat => hz a ha hat)
  simp only [Finset.sum_apply]
  rw [← he]
  calc
    _ ≤ h^j * ∑ a ∈ t, ‖iteratedFDeriv ℝ j (f a) x‖ := by
      gcongr; exact norm_sum_le _ _
    _ = ∑ a ∈ t, h^j * ‖iteratedFDeriv ℝ j (f a) x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _a ∈ t, C := Finset.sum_le_sum (fun a ha => by
      simpa only [iteratedFDerivWithin_univ] using hb a (ht ha) j hj x (mem_univ x))
    _ = (t.card : ℝ)*C := by simp
    _ ≤ 36*C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast active_cutoff_count hh s x

lemma squareSum_weighted_bounds : ∃ D : ℕ → ℝ, (∀ m, 1 ≤ D m) ∧
    ∀ (h : ℝ), 0 < h → ∀ (s : Finset Index) (m : ℕ),
      WeightedBound univ h m (D m) (squareSum s h) := by
  obtain ⟨C,hC,hbound⟩ := cutoff_weighted_bounds
  let D (m : ℕ) := 1 + 36 * (2^m * C m * C m)
  have hD (m : ℕ) : 1 ≤ D m := by
    have hc0 : 0 ≤ C m := zero_le_one.trans (hC m)
    have hp : 0 ≤ 36 * (2^m * C m * C m) := by positivity
    dsimp [D] <;> linarith
  refine ⟨D,hD,fun h hh s m => ?_⟩
  have hc0 : 0 ≤ C m := zero_le_one.trans (hC m)
  have hb : WeightedBound univ h m (36 * (2^m * C m * C m))
      (fun x => ∑ a ∈ s, cutoff h a x * cutoff h a x) :=
    weighted_sum_bounded_overlap hh (by positivity) s _
      (fun a _ => (cutoff_smooth h a).mul (cutoff_smooth h a))
      (fun a _ => tsupport_mul_subset_left)
      (fun a _ => (hbound h hh a m).real_mul uniqueDiffOn_univ hh.le hc0 hc0
        (cutoff_smooth h a).contDiffOn (cutoff_smooth h a).contDiffOn (hbound h hh a m))
  exact (hb.mono_const (by dsimp [D] <;> linarith)).congr (fun x _ => by simp [squareSum,pow_two])

end ClosedSurfaceR4.PhaseGrid

namespace ClosedSurfaceR4.PhaseGrid
open Set Function WeightedEstimates




theorem normalizedCutoff_weighted_bounds : ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    ∀ (h : ℝ), 0 < h → ∀ (s : Finset Index) (U : Set Base), IsOpen U →
      (∀ x ∈ U, ∃ a ∈ s, x ∈ cell h 1 a) → ∀ (a : Index) (m : ℕ),
      WeightedBound U h m (C m) (normalizedCutoff s h a) := by
  obtain ⟨c,hc,hcb⟩ := cutoff_weighted_bounds
  obtain ⟨d,hd,hdb⟩ := squareSum_weighted_bounds
  have hcoeff (m : ℕ) : ∃ e : ℝ, 1 ≤ e ∧ ∀ j ≤ m, ∀ r ∈ Icc (1:ℝ) (d m),
      ‖iteratedFDerivWithin ℝ j (fun r : ℝ => (Real.sqrt r)⁻¹) (Ioi 0) r‖ ≤ e :=
    compact_coefficient_bound isOpen_Ioi.uniqueDiffOn isCompact_Icc
      (fun r hr => zero_lt_one.trans_le hr.1) inverse_sqrt_smooth m
  choose e he heb using hcoeff
  let C (m : ℕ) := 1 + 2^m * c m * ((m.factorial : ℝ) * e m * (d m)^m)
  have hc0 (m : ℕ) : 0 ≤ c m := zero_le_one.trans (hc m)
  have hd0 (m : ℕ) : 0 ≤ d m := zero_le_one.trans (hd m)
  have he0 (m : ℕ) : 0 ≤ e m := zero_le_one.trans (he m)
  have hC (m : ℕ) : 1 ≤ C m := by
    have hcm := hc0 m
    have hdm := hd0 m
    have hem := he0 m
    have hnonneg : 0 ≤ 2^m * c m * ((m.factorial : ℝ) * e m * (d m)^m) := by positivity
    dsimp [C] <;> linarith
  refine ⟨C,hC,fun h hh s U hU hcover a m => ?_⟩
  have hb := (hdb h hh s m).restrict_open hU
  have hmap : MapsTo (squareSum s h) U (Icc 1 (d m)) := by
    intro x hx
    refine ⟨squareSum_ge_one hh (hcover x hx),?_⟩
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb.norm_le hx)
  have hpos : MapsTo (squareSum s h) U (Ioi 0) := fun x hx =>
    zero_lt_one.trans_le (hmap hx).1
  have hs : ContDiffOn ℝ ∞ (squareSum s h) U := (squareSum_smooth s h).contDiffOn
  have hi : ContDiffOn ℝ ∞ (fun x => (Real.sqrt (squareSum s h x))⁻¹) U :=
    inverse_sqrt_smooth.comp hs hpos
  have hbi := hb.comp hU.uniqueDiffOn isOpen_Ioi.uniqueDiffOn hh (hd m) (he0 m)
    hs inverse_sqrt_smooth hpos (fun j hj x hx => heb m j hj _ (hmap hx))
  have hcm := hc0 m
  have hdm := hd0 m
  have hem := he0 m
  have hp := ((hcb h hh a m).restrict_open hU).real_mul hU.uniqueDiffOn hh.le
    (hc0 m) (by positivity) (cutoff_smooth h a).contDiffOn hi hbi
  have hp' := hp.mono_const (show 2^m*c m*((m.factorial:ℝ)*e m*(d m)^m) ≤ C m by
    dsimp [C] <;> linarith)
  exact hp'.congr (fun x _ => by simp only [normalizedCutoff,div_eq_mul_inv])



end ClosedSurfaceR4.PhaseGrid

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
local instance planeReadSectionSpace_rcbc94a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedChartTransport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport smooth compactly supported fields through an actual local
coordinate homeomorphism. Extension by zero preserves the original support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma chartPush_bound (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) {s : ℝ≥0} {J : ℝ} {m : ℕ}
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hJ : 1 ≤ J)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ J)
    (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm (chartSupport e K hK) s m (chartPush e he K hK f) ≤
      (m.factorial : ℝ) * supportedWeightedSeminorm K s m f * J ^ m := by
  have hf := (weightedBound_of_supportedSeminorm s m f).restrict_open e.open_source
  have hb := hf.comp_coordinates e.open_target.uniqueDiffOn e.open_source.uniqueDiffOn hs hs1 hJ
    (apply_nonneg _ _) he f.contDiff.contDiffOn (fun _ hy => e.map_target hy) hderiv
  apply supportedSeminorm_le_of_weightedBound hs (by positivity)
  exact hb.indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
    (chartSupport_subset e K hK) (by positivity) (chartPush_zero e K hK f)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_rcbc94a_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_rcbc94a_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_rcbc94a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_rcbc94a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_rcbc94a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_rcbc94a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_plane (i : A.centers) (F : M → Space) :
    A.jetChartMap i F ∘ planeCoordinateIsometry.symm = spaceCoordinates ∘ A.vectorPlaneRead i F := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasOuterDomains
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded open coordinate domains containing every outer cutoff support. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_outer_domains :
    ∃ (U : A.centers → Set JetPolynomial.Base) (K : A.centers → Compacts JetPolynomial.Base),
      (∀ i, IsOpen (U i)) ∧ (∀ i, U i ⊆ K i) ∧
      (∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i) ∧
      (∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i) := by
  classical
  have hc (i : A.centers) : IsCompact ((chart (i : M)) '' tsupport (A.outer i)) :=
    (isClosed_tsupport (A.outer i)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (A.outer_support i))
  choose U hU hKU hUc _ using fun i => CollarVelocity.compact_open_thickening
    (hc i) isOpen_univ (subset_univ _)
  refine ⟨U,fun i => ⟨closure (U i),hUc i⟩,hU,fun _ => subset_closure,?_,hKU⟩
  intro i x hx
  obtain ⟨p,hp,rfl⟩ := hx
  apply hKU i
  refine ⟨p,subset_tsupport (A.outer i) ?_,rfl⟩
  change A.outer i p ≠ 0
  rw [A.outer_one i p hp]
  exact one_ne_zero

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridSupportedCutoffs
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized grid cutoffs multiplied by a supported chart
weight. The derivative constant is independent of the number of cells. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.WeightedEstimates

lemma WeightedBound.to_unit_scale {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {s C : ℝ} {m : ℕ}
    {f : E → F} (hb : WeightedBound U s m C f) (hs : 0 < s) (hs1 : s ≤ 1)
    (hC : 0 ≤ C) : WeightedBound U 1 m (C/s^m) f := by
  intro j hj x hx
  simp only [one_pow,one_mul]
  exact (hb.deriv_le hs hj hx).trans (div_le_div_of_nonneg_left hC
    (pow_pos hs _) (pow_le_pow_of_le_one hs.le hs1 hj))

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.PhaseGrid
open WeightedEstimates JetPolynomial

theorem supported_normalized_cutoff_bounds :
    ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    ∀ {K : Compacts Base} (f : SupportedField (F := ℝ) K)
      {a : Finset Index} {h : ℝ} (hh : 0 < h) (_hh1 : h ≤ 1)
      (hK : (K : Set Base) ⊆ coverRegion a h) (P : ℕ → ℝ),
      (∀ m, 0 ≤ P m) → (∀ m, WeightedBound univ 1 m (P m) f) →
      ∀ k m, WeightedBound univ 1 m (C m*P m/h^m)
        (supportedNormalizedCutoff f hh hK k) := by
  obtain ⟨C,hC,hb⟩ := normalizedCutoff_weighted_bounds
  refine ⟨fun m => 2^m*C m,fun m => one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) (hC m),?_⟩
  intro K f a h hh hh1 hK P hP hf k m
  let U := coverRegion a h
  have hU : IsOpen U := coverRegion_open a h
  have hnorm := hb h hh a U hU (fun x hx => coverRegion_covers a h hx) k m
  have hsm := normalizedCutoff_smooth hh (fun x hx => coverRegion_covers a h hx) k
  have hprod := ((hf m).shrink_scale hh.le hh1).restrict_open hU
  have hmul := hprod.real_mul hU.uniqueDiffOn hh.le (hP m)
    (zero_le_one.trans (hC m)) f.contDiff.contDiffOn hsm hnorm
  have hd : WeightedBound U h m (2^m*P m*C m) (supportedNormalizedCutoff f hh hK k) :=
    hmul
  have hprod : 0 ≤ 2^m*P m*C m :=
    mul_nonneg (mul_nonneg (by positivity) (hP m)) (zero_le_one.trans (hC m))
  have hall := hd.extend_support hU
    ((supportedNormalizedCutoff f hh hK k).tsupport_subset.trans hK) hprod
  convert hall.to_unit_scale hh hh1 hprod using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseReparametrization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A good covector supplies the actual free coordinate system for a mode. -/

noncomputable section

namespace ClosedSurfaceR4.RealModes

open SmallModes PhaseGeometry Set
open scoped ContDiff

lemma phaseInverse_det {ξ : Base} (hξ : ξ ≠ 0) :
    (((phaseEquiv ξ hξ).symm dx).1 * ((phaseEquiv ξ hξ).symm dy).2 -
      ((phaseEquiv ξ hξ).symm dx).2 * ((phaseEquiv ξ hξ).symm dy).1) ≠ 0 := by
  have hd : ξ.1 ^ 2 + ξ.2 ^ 2 ≠ 0 := (covector_length_sq_pos hξ).ne'
  have he :
      (((phaseEquiv ξ hξ).symm dx).1 * ((phaseEquiv ξ hξ).symm dy).2 -
        ((phaseEquiv ξ hξ).symm dx).2 * ((phaseEquiv ξ hξ).symm dy).1) =
        (ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹ := by
    simp only [phaseEquiv_symm_apply, dx, dy]
    field_simp
    ring
  rw [he]
  exact inv_ne_zero hd

lemma phaseInverse_dy {ξ : Base} (hξ : ξ ≠ 0) :
    (phaseEquiv ξ hξ).symm dy = (ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹ • (-ξ.2, ξ.1) := by
  ext <;> simp [dy, div_eq_mul_inv, mul_comm]

/-- The normal acceleration in the new y direction is a positive scalar
multiple of the old second fundamental form in the covector's kernel. -/
theorem realSecond_phase {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {ξ : Base} (hξ : ξ ≠ 0) (p : Base)
    (hImm : Function.Injective (fderiv ℝ F ((phaseEquiv ξ hξ).symm p))) :
    realSecond (F ∘ (phaseEquiv ξ hξ).symm) p =
      ((ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹) ^ 2 •
        secondQuadratic (realSecondTensor F ((phaseEquiv ξ hξ).symm p)) (-ξ.2, ξ.1) := by
  change realSecondForm (F ∘ (phaseEquiv ξ hξ).symm) dy dy p = _
  have he := realSecondForm_comp_linear hF (phaseEquiv ξ hξ).symm.toContinuousLinearMap
    dy dy p (gramDet_ne_zero_of_injective _ hImm) (phaseInverse_det hξ)
  simp only [ContinuousLinearEquiv.coe_coe] at he
  rw [he]
  rw [phaseInverse_dy, realSecondForm_quadratic hF, secondQuadratic_smul]

/-- Immersion and the good-direction condition on an open set produce the
free-mode domain required by the finite oscillatory construction. -/
theorem realModeDomain_phase {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {O : Set Base} (hO : IsOpen O) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ p ∈ O, Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ O, Good (realSecondTensor F p) ξ) :
    RealModeDomain (F ∘ (phaseEquiv ξ hξ).symm) ((phaseEquiv ξ hξ) '' O) := by
  refine ⟨(phaseEquiv ξ hξ).isOpenMap O hO, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    apply gramDet_ne_zero_of_injective
    rw [fderiv_comp _ (hF.differentiable (by simp) _)
      (phaseEquiv ξ hξ).symm.differentiableAt]
    simpa only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using
      (hImm p hp).comp (phaseEquiv ξ hξ).symm.injective
  · rintro _ ⟨p, hp, rfl⟩
    have hi : Function.Injective (fderiv ℝ F
        ((phaseEquiv ξ hξ).symm ((phaseEquiv ξ hξ) p))) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hImm p hp
    rw [realSecond_phase hF hξ _ hi, ContinuousLinearEquiv.symm_apply_apply]
    exact smul_ne_zero (pow_ne_zero 2 (inv_ne_zero (covector_length_sq_pos hξ).ne'))
      (hgood p hp).2

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseChart
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit restricted linear chart used for a nonzero phase covector. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma linearPhaseChart_modeDomain {F : RealModes.RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (hU : IsOpen U) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ U, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ U, Good (RealModes.realSecondTensor F x) ξ) :
    RealModes.RealModeDomain (F ∘ (linearPhaseChart ξ hξ U hU).symm)
      (linearPhaseChart ξ hξ U hU).target :=
  RealModes.realModeDomain_phase hF hU hξ hImm hgood

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetPrefixBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual positional two-jet on a fixed bounded domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem directional_of_prefix {U : Set E} (hU : IsOpen U)
    {f : E → V} (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+1, WeightedBound U 1 j (C/s^(j-1)) f)
    (v : E) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m C (fun x => fderiv ℝ f x v) := by
  intro j hj x hx
  have hh := ((hb (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn v)
    j le_rfl x hx
  simp only [one_pow,one_mul,div_one,Nat.add_sub_cancel] at hh
  calc
    _ ≤ s^j*(‖v‖*(C/s^j)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = ‖v‖*C := by field_simp
    _ ≤ C := mul_le_of_le_one_left hC hv

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem jet_lowWord_bound {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G)
    (w : Fin 7) (a : Fin 4) :
    WeightedBound U s m C (fun p => jet G (lowWord w) a p) := by
  let f : Base → ℝ := fun p => G p a
  have hf : ContDiff ℝ ∞ f := contDiff_pi.mp hG a
  have hp (j : ℕ) (hj : j ≤ m+2) : WeightedBound U 1 j (C/s^(j-2)) f :=
    (hb j hj).component hU.uniqueDiffOn zero_le_one
      (div_nonneg hC (pow_nonneg hs.le _)) hG.contDiffOn a
  have hzero : WeightedBound U s m C f := by
    intro j hj x hx
    have hh := hp j (by omega) j le_rfl x hx
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ s^j*(C/s^(j-2)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ ≤ s^j*(C/s^j) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le _ _))) (pow_nonneg hs.le _)
      _ = C := by field_simp
  have hunit (v : Fin 2) : ‖coordinateVector v‖ = 1 := by
    simp only [coordinateVector,Pi.norm_single,norm_one]
  have hfirst (v : Fin 2) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound U 1 j (C/s^(j-1)) (fun x => fderiv ℝ f x (coordinateVector v)) := by
    have hh := (hp (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn (coordinateVector v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hunit,one_mul,div_one,he] using hh
  have hone (v : Fin 2) :
      WeightedBound U s m C (fun x => fderiv ℝ f x (coordinateVector v)) := by
    apply directional_of_prefix hU hf hs hC _ (coordinateVector v) (hunit v).le
    intro j hj
    apply (hp j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have htwo (v v' : Fin 2) : WeightedBound U s m C
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector v')) x (coordinateVector v)) :=
    directional_of_prefix hU
      ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)
      hs hC (hfirst v') (coordinateVector v) (hunit v).le
  fin_cases w
  · exact hzero
  · exact hone 0
  · exact hone 1
  · exact htwo 0 0
  · exact htwo 0 1
  · exact htwo 1 0
  · exact htwo 1 1

theorem bounded_lowJet_prefix {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G) →
      WeightedBound U s m (D+C) (lowJet G) := by
  obtain ⟨D,hD,hd⟩ := compact_local_weighted_bound hU isOpen_univ K.isCompact hUK
    (subset_univ _) (contDiff_id : ContDiff ℝ ∞ (id : Base → Base)).contDiffOn m
  refine ⟨D,hD,?_⟩
  intro G hG s C hs hs1 hC hb
  apply WeightedBound.pi hU.uniqueDiffOn hs (by linarith)
  · intro i
    exact (contDiff_pi.mp (lowJet_smooth hG) i).contDiffOn
  · intro i
    cases i with
    | inl i =>
      exact ((hd s hs.le hs1).component hU.uniqueDiffOn hs.le
        (zero_le_one.trans hD) contDiff_id.contDiffOn i).mono_const (by linarith)
    | inr i =>
      exact (jet_lowWord_bound hU hG hs hs1 hC hb i.1 i.2).mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseCutoffBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative transport of the actual supported cutoff to a linear
phase chart, including the inverse frequency factor. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseGeometry RealModes

theorem linear_phase_cutoff_bound {U : Set SmallModes.Base} (hU : IsOpen U)
    {ξ : SmallModes.Base} (hξ : ξ ≠ 0) (K : Compacts SmallModes.Base)
    (hK : (K : Set SmallModes.Base) ⊆ U) {s : ℝ≥0} {C J W w : ℝ} {m : ℕ}
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hJ : 1 ≤ J)
    (hi : ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ J) (hw : |w⁻¹| ≤ W)
    (f : SupportedField (F := ℝ) K) (hf : WeightedBound univ s m C f) :
    WeightedBound univ s m (phaseCutoffBudget m C J W)
      (w⁻¹ • chartPush (linearPhaseChart ξ hξ U hU)
        (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn K hK f) := by
  let e := linearPhaseChart ξ hξ U hU
  let g := chartPush e (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn K hK f
  have hj (j : ℕ) (hj : 1 ≤ j) (_hjm : j ≤ m) (y : SmallModes.Base) (hy : y ∈ e.target) :
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ J :=
    (positive_order_linear_derivative_le (phaseEquiv ξ hξ).symm.toContinuousLinearMap
      e.open_target hj hy).trans hi
  have hseminorm := chartPush_bound e
    (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn K hK hs hs1 hJ hj f
  have hpush : WeightedBound univ s m ((m.factorial : ℝ)*C*J^m) g := by
    apply (weightedBound_of_supportedSeminorm s m g).mono_const
    exact hseminorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (supportedSeminorm_le_of_weightedBound hs hC f hf)
        (Nat.cast_nonneg _)) (pow_nonneg (zero_le_one.trans hJ) _))
  have hscale := hpush.const_smul uniqueDiffOn_univ g.contDiff.contDiffOn (w⁻¹)
  apply hscale.mono_const
  exact mul_le_mul_of_nonneg_right hw
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (pow_nonneg (zero_le_one.trans hJ) _))

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridCutoffSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local cell cutoff has the exact global refined support used in
phase selection. This keeps the solver's geometry on that original support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma cellChartCompact_subset (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index) :
    (A.cellChartCompact i a h k : Set JetPolynomial.Base) ⊆ A.chartWeightCompact i :=
  Set.image_mono (refinedCutoff_tsupport_outer (i : M) (A.weight i) a h k)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridCutoffBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact supported cell cutoffs have a fixed atlas polynomial bound. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology NNReal BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem grid_exact_cutoff_bounds :
    ∃ P : ℕ → ℝ, (∀ m, 1 ≤ P m) ∧ ∀ (i : A.centers)
      {a : Finset Index} {z : ℝ} (hz : 0 < z), z ≤ 1 →
      ∀ hcover : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
        coverRegion a (z^6),
      ∀ (k : Index) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ w : ℝ, 1 ≤ w → ∀ m,
      WeightedEstimates.WeightedBound univ s m (P m/z^(6*m))
        (w⁻¹ • A.exactCellCutoff i (pow_pos hz 6) hcover k) := by
  classical
  obtain ⟨C,hC,hcut⟩ := supported_normalized_cutoff_bounds
  let B := fun m => 1+∑ i : A.centers,
    supportedWeightedSeminorm (modeSupport (A.chartWeightCompact i)) 1 m (A.supportedPlaneWeight i)
  have hB (m : ℕ) : 1 ≤ B m := le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => apply_nonneg _ _)
  have hb (i : A.centers) (m : ℕ) :
      WeightedEstimates.WeightedBound univ 1 m (B m) (A.supportedPlaneWeight i) := by
    apply (weightedBound_of_supportedSeminorm 1 m (A.supportedPlaneWeight i)).mono_const
    have hh : supportedWeightedSeminorm (modeSupport (A.chartWeightCompact i)) 1 m
        (A.supportedPlaneWeight i) ≤ ∑ j : A.centers,
          supportedWeightedSeminorm (modeSupport (A.chartWeightCompact j)) 1 m
            (A.supportedPlaneWeight j) :=
      Finset.single_le_sum (fun j _ => show 0 ≤
        supportedWeightedSeminorm (modeSupport (A.chartWeightCompact j)) 1 m
          (A.supportedPlaneWeight j) from apply_nonneg _ _) (Finset.mem_univ i)
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨fun m => C m*B m,fun m => one_le_mul_of_one_le_of_one_le (hC m) (hB m),?_⟩
  intro i a z hz hz1 hcover k s hs hs1 w hw m
  have hraw := (hcut (A.supportedPlaneWeight i) (pow_pos hz 6)
    (pow_le_one₀ hz.le hz1) hcover B (fun m => zero_le_one.trans (hB m)) (hb i) k m).shrink_scale
      s.coe_nonneg hs1
  have he : (A.exactCellCutoff i (pow_pos hz 6) hcover k : SmallModes.Base → ℝ) =
      supportedNormalizedCutoff (A.supportedPlaneWeight i) (pow_pos hz 6) hcover k := rfl
  have hraw' : WeightedEstimates.WeightedBound univ s m (C m*B m/z^(6*m))
      (A.exactCellCutoff i (pow_pos hz 6) hcover k) := by
    simpa only [he,pow_mul] using hraw
  have hbound : |w⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hw))]
    exact inv_le_one_of_one_le₀ hw
  have hh := hraw'.const_smul uniqueDiffOn_univ
    (A.exactCellCutoff i (pow_pos hz 6) hcover k).contDiff.contDiffOn w⁻¹
  apply hh.mono_const
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hbound
    (div_nonneg (mul_nonneg (zero_le_one.trans (hC m)) (zero_le_one.trans (hB m)))
      (pow_nonneg hz.le _))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricAtlasReference
attribute [-instance] _root_.instVAddIntReal_solutions
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
local instance metricReferenceSectionNormed_rcbc94a_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_rcbc94a_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metric_inner_smooth (g : SmoothMetric M) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (g.inner p)) := g.contMDiff

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberNormed
local instance metricReferenceSectionNormed_rcbc94a_2 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_rcbc94a_2 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_metric_smooth (g : SmoothMetric M) (i : A.centers) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i g.inner) :=
  A.tensorPlaneRead_smooth i (metric_inner_smooth g)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseDenominatorNeighborhood
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact-support denominator bound extends to an open phase domain
with a specified factor of two. The domain may depend on the immersion;
the numerical bounds do not. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma continuousAt_phaseNormal {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0) :
    ContinuousAt (fun y => secondQuadratic (realSecondTensor F y)
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)) x := by
  have hb := (contDiffAt_realSecondTensor hF x hD).continuousAt
  have hp := (continuous_phaseDerivative hφ).continuousAt (x := x)
  have hh : ContinuousAt (fun y : Base => (realSecondTensor F y,
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1))) x :=
    hb.prodMk (hp.snd.neg.prodMk hp.fst)
  have hc : ContinuousAt (fun z : (Fin 3 → RVec 4) × Base => secondQuadratic z.1 z.2)
      (realSecondTensor F x, (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)) :=
    (continuous_secondQuadratic (n := 4)).continuousAt
  exact hc.comp (f := fun y : Base => (realSecondTensor F y,
    (-(phaseDerivative φ y).2,(phaseDerivative φ y).1))) hh

lemma eventually_gram_reciprocal_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (x : Base) {B : ℝ} (hB : 0 < B)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (h : ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) :
    ∀ᶠ y in 𝓝 x,
      ‖(NormalFrame.gramDet (coordDeriv dx F y) (coordDeriv dy F y))⁻¹‖ < 2*B := by
  have hc := ((continuous_gramDet_field hF).continuousAt (x := x)).inv₀ hD
  exact hc.norm.eventually (Iio_mem_nhds (lt_of_le_of_lt h (by linarith)))

lemma eventually_normal_reciprocal_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Base) {B : ℝ} (hB : 0 < B)
    (hD : NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (hn : secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1) ≠ 0)
    (h : ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ B) :
    ∀ᶠ y in 𝓝 x, ‖secondQuadratic (realSecondTensor F y)
      (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)‖⁻¹ < 2*B := by
  have hc := (continuousAt_phaseNormal hF hφ x hD).norm.inv₀ (norm_ne_zero_iff.mpr hn)
  exact hc.eventually (Iio_mem_nhds (lt_of_le_of_lt h (by linarith)))

theorem phase_denominator_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Set Base) {B : ℝ} (hB : 0 < B)
    (hImm : ∀ x ∈ K, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ K, Good (realSecondTensor F x) (phaseDerivative φ x))
    (hgram : ∀ x ∈ K, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B)
    (hnormal : ∀ x ∈ K, ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ B) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U,
      Function.Injective (fderiv ℝ F x) ∧ Good (realSecondTensor F x) (phaseDerivative φ x) ∧
      ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ 2*B ∧
      ‖secondQuadratic (realSecondTensor F x)
        (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ 2*B := by
  let S : Set Base := {x | Function.Injective (fderiv ℝ F x) ∧
    Good (realSecondTensor F x) (phaseDerivative φ x) ∧
    ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ 2*B ∧
    ‖secondQuadratic (realSecondTensor F x)
      (-(phaseDerivative φ x).2,(phaseDerivative φ x).1)‖⁻¹ ≤ 2*B}
  refine ⟨interior S,isOpen_interior,?_,fun x hx => (show x ∈ S from interior_subset hx)⟩
  intro x hx
  have hD := gramDet_ne_zero_of_injective (fderiv ℝ F x) (hImm x hx)
  have hge := eventually_gram_reciprocal_bound hF x hB hD (hgram x hx)
  have hne := eventually_normal_reciprocal_bound hF hφ x hB hD (hgood x hx).2
    (hnormal x hx)
  have hb := (contDiffAt_realSecondTensor hF x hD).continuousAt
  have hp := (continuous_phaseDerivative hφ).continuousAt (x := x)
  have hgood' := good_eventually hb hp (hgood x hx)
  have hD' := (continuous_gramDet_field hF).continuousAt.eventually_ne hD
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hD',hgood',hge,hne] with y hyD hyg hyG hyN
  exact ⟨injective_of_gramDet_ne_zero _ hyD,hyg,hyG.le,hyN.le⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LinearPhaseMeanGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mean geometry for an actual linear good phase: the coefficient
margin is transported exactly, and the pullback operator is constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean

theorem linear_phase_local_bounds {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (hU : IsOpen U) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ U, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ U, Good (realSecondTensor F x) ξ)
    {ψ : Base → ℝ} (hψ : ContDiff ℝ ∞ ψ) (Q : PhaseMean.Tensor →L[ℝ] ℝ)
    {s r ρ R : ℝ} {reference : Base → PhaseMean.Tensor}
    (hmargin : ∀ x ∈ U, ρ + ‖Q‖*r ≤ Q (reference x) ∧ Q (reference x) ≤ R - ‖Q‖*r) :
    LocalBounds U (linearPhaseChart ξ hξ U hU).target s r ρ R reference
      (F ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
      (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm := by
  have hsm := linearPhaseChart_smooth ξ hξ U hU
  refine {
    openU := hU
    smoothF := hF.comp hsm.2
    domain := linearPhaseChart_modeDomain hF hU hξ hImm hgood
    smoothPsi := hψ.contDiffOn
    smoothQ := contDiffOn_const
    smoothChi := hsm.1.contDiffOn
    smoothInv := hsm.2.contDiffOn
    chiInto := fun x hx => (linearPhaseChart ξ hξ U hU).map_source hx
    invInto := fun x hx => (linearPhaseChart ξ hξ U hU).map_target hx
    smoothPullback := ?_
    margin := ?_
  }
  · have he : pullbackField (linearPhaseChart ξ hξ U hU) =
        fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [he]
    exact contDiffOn_const
  · intro x hx
    exact hmargin _ ((linearPhaseChart ξ hξ U hU).map_target hx)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UnperturbedMeanDataFromBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete actual mean data from the local geometry and its specified
budgets. Compact positional jets are obtained on a bounded source domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

theorem unperturbed_mean_data_from_bounds
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
    (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    {U : Set Base} (hU : IsOpen U) (K₀ : Compacts Base)
    (hUK : U ⊆ K₀) (hKU : (K : Set Base) ⊆ U)
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (loc : LocalBounds c.e.source c.e.target s r ρ R reference
      c.realMap ψ Q c.e c.e.symm)
    (b : Budgets c.e.source c.e.target s c.realMap ψ Q c.e c.e.symm)
    (Pjet : ℕ → ℝ) (hPjet : ∀ m, 0 ≤ Pjet m)
    (hpref : ∀ m j, j ≤ m+2 → WeightedBound U 1 j
      (Pjet m/(s : ℝ)^(j-2)) G) :
    ∃ d : ChartedMeanData (c.onSourceDomain U hU hKU) r ρ R reference,
      d.cutoff = ψ ∧ d.form = Q ∧
      d.budgets.inv = b.inv ∧ d.budgets.chi = b.chi ∧
      d.budgets.forms = b.forms ∧ d.budgets.pull = b.pull ∧
      d.budgets.psi = b.psi ∧ d.budgets.normal = b.normal ∧ d.budgets.mode = b.mode := by
  classical
  choose D hD hd using fun m => bounded_lowJet_prefix hU K₀ hUK m
  have hφ (v : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x (coordinateVector v)) :=
    (c.smoothPhase.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  choose A hA ha using fun (m : ℕ) (v : Fin 2) => compact_local_weighted_bound
    hU isOpen_univ K₀.isCompact hUK (subset_univ _) (hφ v).contDiffOn m
  let B := fun m => D m+Pjet m
  let F := fun m => ∑ v : Fin 2, A m v
  refine ⟨{
    cutoff := ψ
    form := Q
    localBounds := loc
    budgets := b
    compactJets := lowJet G '' (K₀ : Set Base)
    compact := K₀.isCompact.image (lowJet_smooth hG).continuous
    subsetDomain := subset_univ _
    mapsJets := fun x hx => ⟨x,hUK hx,rfl⟩
    B := B
    F := F
    oneLEB := fun m => (hD m).trans (le_add_of_nonneg_right (hPjet m))
    nonnegF := fun m => Finset.sum_nonneg (fun v _ => zero_le_one.trans (hA m v))
    jetsBound := ?_
    phaseBound := ?_
  },rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro m
    change WeightedBound U s (m+tensorOrder emptyMetricPolynomial) (B m) (lowJet G)
    simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero] using
      hd m G hG s (Pjet m) hs hs1 (hPjet m) (hpref m)
  · intro m v
    change WeightedBound U s (m+tensorOrder emptyMetricPolynomial) (F m)
      (fun x => fderiv ℝ φ x (coordinateVector v))
    have hv : A m v ≤ F m := Finset.single_le_sum
      (fun w _ => zero_le_one.trans (hA m w)) (Finset.mem_univ v)
    simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero] using
      (ha m v s s.coe_nonneg hs1).mono_const hv

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearMeanData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual supported mean data with polynomial geometric budgets, for
the linear phases used in the exact metric correction. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

theorem polynomial_linear_charted_mean_data :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
      (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
      {U : Set SmallModes.Base} (hU : IsOpen U) {ξ : SmallModes.Base} (hξ : ξ ≠ 0),
      c.e = linearPhaseChart ξ hξ U hU →
      ∀ {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base),
      U₀ ⊆ K₀ → ∀ hKU₀ : (K : Set Base) ⊆ U₀, 0 < (s : ℝ) → s ≤ 1 →
      ∀ (ψ : SupportedField (F := ℝ) c.chartCompact) (Q : Tensor →L[ℝ] ℝ)
        {r ρ R : ℝ} {reference : SmallModes.Base → Tensor},
      (∀ x ∈ U, ρ+‖Q‖*r ≤ Q (reference x) ∧ Q (reference x) ≤ R-‖Q‖*r) →
      (∀ x ∈ U, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ U, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ) →
      ∀ B P Pjet : ℕ → ℝ, (∀ m, 1 ≤ B m) → (∀ m, 1 ≤ P m) →
      (∀ m, 0 ≤ Pjet m) →
      (∀ m, ‖ξ‖ ≤ B m ∧ ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧
        ‖Q‖ ≤ B m ∧
        (∀ j ≤ m+2, WeightedBound U 1 j (B m/(s : ℝ)^(j-2))
          (G ∘ planeCoordinateIsometry.symm)) ∧
        (∀ x ∈ U, ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ U, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-ξ.2,ξ.1)‖⁻¹ ≤ B m)) →
      (∀ m, WeightedBound c.e.target s m (P m) ψ) →
      (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j (Pjet m/(s : ℝ)^(j-2)) G) →
      ∃ d : ChartedMeanData (c.onSourceDomain U₀ hU₀ hKU₀)
          r ρ R reference,
        d.cutoff = ψ ∧ d.form = (fun _ => Q) ∧
        ∀ m, d.budgets.inv m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.chi m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.forms m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.pull m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.psi m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.normal m ≤ linearMeanGeometryBudget p A B P m ∧
          d.budgets.mode m ≤ linearMeanGeometryBudget p A B P m := by
  obtain ⟨p,A,hA,hbudgets⟩ := polynomial_linear_mean_budgets
  refine ⟨p,A,hA,?_⟩
  intro G hG φ K τ s c U hU ξ hξ hce U₀ hU₀ K₀ hU₀K hKU₀ hs hs1
    ψ Q r ρ R reference hmargin hImm hgood B P Pjet hB hP hPjet hb hψ hpref
  have hGc : ContDiff ℝ ∞ (G ∘ planeCoordinateIsometry.symm) :=
    hG.comp planeCoordinateIsometry.symm.contDiff
  have hψ' : ∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (P m) ψ := by
    simpa only [hce] using hψ
  obtain ⟨b,hb⟩ := hbudgets hGc hU hξ hs hs1 ψ Q B P hB hP hb hImm hgood hψ'
  have loc : LocalBounds c.e.source c.e.target s r ρ R reference
      c.realMap ψ (fun _ => Q) c.e c.e.symm := by
    simpa only [hce,linearPhaseChart_source,PolynomialSolveData.realMap] using
      linear_phase_local_bounds hGc hU hξ hImm hgood ψ.contDiff Q hmargin
  let b' : Budgets c.e.source c.e.target s c.realMap ψ (fun _ => Q) c.e c.e.symm := {
    inv := b.inv
    chi := b.chi
    psi := b.psi
    forms := b.forms
    pull := b.pull
    normal := b.normal
    mode := b.mode
    inv_pos := b.inv_pos
    chi_pos := b.chi_pos
    psi_pos := b.psi_pos
    forms_pos := b.forms_pos
    pull_pos := b.pull_pos
    normal_pos := b.normal_pos
    mode_pos := b.mode_pos
    inv_bound := by simpa only [hce] using b.inv_bound
    chi_bound := by simpa only [hce,linearPhaseChart_source] using b.chi_bound
    psi_bound := by simpa only [hce] using b.psi_bound
    normal_bound := by simpa only [hce,PolynomialSolveData.realMap] using b.normal_bound
    mode_bound := by simpa only [hce,PolynomialSolveData.realMap] using b.mode_bound
    forms_bound := by simpa only [hce] using b.forms_bound
    pull_bound := by simpa only [hce,linearPhaseChart_source] using b.pull_bound
  }
  obtain ⟨d,hcut,hform,hi,hχ,hQ,hpull,hpsi,hn,hm⟩ :=
    unperturbed_mean_data_from_bounds c hU₀ K₀ hU₀K hKU₀ hs hs1 ψ (fun _ => Q)
      loc b' Pjet hPjet hpref
  refine ⟨d,hcut,hform,?_⟩
  intro m
  rw [hi,hχ,hQ,hpull,hpsi,hn,hm]
  exact hb m

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSupportedMeanData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported linear-phase mean data with numerical budgets chosen before
its phase domain. The domain is constructed from the actual denominator
bounds on the support. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

private lemma linear_phase_derivative (ξ x : SmallModes.Base) :
    phaseDerivative (phaseLinear ξ) x = ξ := by
  unfold phaseDerivative
  rw [(phaseLinear ξ).hasFDerivAt.fderiv]
  ext <;> simp [phaseLinear_apply,SmallModes.dx,SmallModes.dy]

theorem polynomial_supported_linear_mean_data :
    ∃ (p p' : ℕ → ℕ) (C C' : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ C' m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
      {W : Set SmallModes.Base} (_hW : IsOpen W)
      (_hKW : (modeSupport K : Set SmallModes.Base) ⊆ W)
      {U₀ : Set Base} (_hU₀ : IsOpen U₀) (K₀ : Compacts Base)
      (_hU₀K : U₀ ⊆ K₀) (_hKU₀ : (K : Set Base) ⊆ U₀)
      {D : ℝ} (_hD : 0 < D),
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-ξ.2,ξ.1)‖⁻¹ ≤ D) →
      ∀ (Q : Tensor →L[ℝ] ℝ) {r ρ R : ℝ} {reference : SmallModes.Base → Tensor},
      (∀ x ∈ W, ρ+‖Q‖*r ≤ Q (reference x) ∧ Q (reference x) ≤ R-‖Q‖*r) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B P : ℕ → ℝ, (∀ m, 1 ≤ B m) → (∀ m, 1 ≤ P m) →
      (∀ m, 2*D ≤ B m ∧ ‖ξ‖ ≤ B m ∧
        ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧ ‖Q‖ ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j (B m/(s : ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∀ f : SupportedField (F := ℝ) (modeSupport K),
      (∀ m, WeightedBound univ s m (P m) f) →
      ∃ (U : Set SmallModes.Base) (hU : IsOpen U),
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG
          (phaseLinear ξ ∘ planeCoordinateIsometry) K τ s,
      ∃ d : ChartedMeanData c r ρ R reference,
        c.e = linearPhaseChart ξ hξ U hU ∧
        (∀ m, c.C m = C m*(B m)^(p m)) ∧ (∀ m, c.J m = 1+2*B m) ∧
        (∀ m, c.D m = 0) ∧
        (∀ x ∈ c.e.source, d.cutoff (c.e x) = f x) ∧ d.form = (fun _ => Q) ∧
        ∀ m, let b := linearMeanGeometryBudget p' C' B (fun j => 1+phaseCutoffBudget j (P j) (B j) 1) m;
          d.budgets.inv m ≤ b ∧ d.budgets.chi m ≤ b ∧ d.budgets.forms m ≤ b ∧
          d.budgets.pull m ≤ b ∧ d.budgets.psi m ≤ b ∧ d.budgets.normal m ≤ b ∧
          d.budgets.mode m ≤ b := by
  obtain ⟨p,C,hC,hsolver⟩ := polynomial_linear_unperturbed_solver
  obtain ⟨p',C',hC',hmean⟩ := polynomial_linear_charted_mean_data
  refine ⟨p,p',C,C',hC,hC',?_⟩
  intro G hG K ξ hξ W hW hKW U₀ hU₀ K₀ hU₀K hKU₀ D hD hImm hgood hgram hnormal
    Q r ρ R reference hmargin τ s hs hs1 B P hB hP hb hjets f hf
  have hGc := hG.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨V,hV,hKV,hVdata⟩ := phase_denominator_neighborhood hGc
    (phaseLinear ξ).contDiff (modeSupport K) hD hImm
    (by simpa only [linear_phase_derivative] using hgood) hgram
    (by simpa only [linear_phase_derivative] using hnormal)
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hKU : (modeSupport K : Set SmallModes.Base) ⊆ U := fun x hx => ⟨hKV hx,hKW hx⟩
  have hdata (x : SmallModes.Base) (hx : x ∈ U) :
      Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x) ∧
      Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ ∧
      ‖(NormalFrame.gramDet
        (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
        (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ 2*D ∧
      ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (-ξ.2,ξ.1)‖⁻¹ ≤ 2*D := by
    simpa only [linear_phase_derivative] using hVdata x hx.1
  have hphase : coordinatePhase (phaseLinear ξ ∘ planeCoordinateIsometry) = phaseLinear ξ := by
    funext x
    simp only [coordinatePhase,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  have hsb (m : ℕ) := (hb m).1
  obtain ⟨c,hce,hcC,hcD,hcJ⟩ := hsolver hG K hU hξ
    ((phaseLinear ξ).contDiff.comp planeCoordinateIsometry.contDiff) hphase hKU
    (fun x hx => (hdata x hx).1) (fun x hx => (hdata x hx).2.1) τ s hs hs1 B hB
    (fun m => ⟨(hb m).2.1,(hb m).2.2.1,
      fun j hj => (hjets m j hj).restrict_open hU,
      fun x hx => (hdata x hx).2.2.1.trans (hsb m),
      fun x hx => (hdata x hx).2.2.2.trans (hsb m)⟩)
  let e := linearPhaseChart ξ hξ U hU
  let ψ : SupportedField (F := ℝ) c.chartCompact :=
    chartPush c.e c.smoothInverse (modeSupport K) c.supportChart f
  have hψeq : (ψ : SmallModes.Base → ℝ) =
      chartPush e (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn (modeSupport K) hKU f := by
    funext x
    simp only [ψ,chartPush_apply]
    rw [hce]
    rfl
  let P' := fun m => 1+phaseCutoffBudget m (P m) (B m) 1
  have hP' (m : ℕ) : 1 ≤ P' m := by
    apply le_add_of_nonneg_right
    have hPm := zero_le_one.trans (hP m)
    have hBm := zero_le_one.trans (hB m)
    dsimp [phaseCutoffBudget]
    positivity
  have hψ (m : ℕ) : WeightedBound c.e.target s m (P' m) ψ := by
    have hh := linear_phase_cutoff_bound hU hξ (modeSupport K) hKU hs hs1
      (zero_le_one.trans (hP m)) (hB m) (hb m).2.2.1
      (show |(1 : ℝ)⁻¹| ≤ 1 by norm_num) f (hf m)
    simp only [inv_one,one_smul] at hh
    have hh' : WeightedBound univ s m (phaseCutoffBudget m (P m) (B m) 1) ψ := by
      exact hh.congr (fun x _ => congrFun hψeq x)
    exact (hh'.mono_const (le_add_of_nonneg_left zero_le_one)).restrict_open c.e.open_target
  have hpref (m j : ℕ) (hj : j ≤ m+2) :
      WeightedBound U₀ 1 j (B m/(s : ℝ)^(j-2)) G := by
    have hh := weightedBound_comp_isometry planeCoordinateIsometry hGc (hjets m j (by omega))
    have he : (G ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = G := by
      funext x
      simp only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply]
    rw [he] at hh
    exact hh.restrict_open hU₀
  obtain ⟨d,hdψ,hdQ,hbd⟩ := hmean c hU hξ hce hU₀ K₀ hU₀K hKU₀ hs hs1 ψ Q
    (fun x hx => hmargin x hx.2) (fun x hx => (hdata x hx).1)
    (fun x hx => (hdata x hx).2.1) B P' B hB hP'
    (fun m => zero_le_one.trans (hB m))
    (fun m => ⟨(hb m).2.1,(hb m).2.2.1,(hb m).2.2.2,
      fun j hj => (hjets m j (by omega)).restrict_open hU,
      fun x hx => (hdata x hx).2.2.1.trans (hsb m),
      fun x hx => (hdata x hx).2.2.2.trans (hsb m)⟩) hψ hpref
  refine ⟨U,hU,c.onSourceDomain U₀ hU₀ hKU₀,d,hce,hcC,hcJ,fun _ => rfl,?_,hdQ,hbd⟩
  intro x hx
  rw [hdψ]
  have hx' : x ∈ e.source := by simpa only [PolynomialSolveData.onSourceDomain,hce,e] using hx
  change ψ (c.e x) = f x
  rw [hce,congrFun hψeq (e x)]
  exact chartPush_eval_source e (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn
    (modeSupport K) hKU f hx'

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global nonlinear mean is the finite restoration of the actual
local means evaluated on unweighted chart readings. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberSpace
local instance atlasMeanDualAdd_rcbc94a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberNormed
local instance atlasMeanSectionNormed_rcbc94a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMeanSectionSpace_rcbc94a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma one_le_tensorReadBallConstant : 1 ≤ A.tensorReadBallConstant :=
  (Classical.choose_spec A.tensorPlaneRead_decode_ball).1

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformCoefficientMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common quantitative trial radius for varying grid coefficient forms. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseMean
open SmallModes (Base)

theorem uniform_coefficient_margins {a C H : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
      ∀ (Q : Tensor →L[ℝ] ℝ), ‖Q‖ ≤ C →
      ∀ reference : Base → Tensor, Continuous reference →
      (∀ x, Q (reference x) ≤ H) → ∀ K : Set Base,
      (∀ x ∈ K, a ≤ Q (reference x)) →
      ∃ W : Set Base, IsOpen W ∧ K ⊆ W ∧
        ∀ x ∈ W, ρ+‖Q‖*r ≤ Q (reference x) ∧
          Q (reference x) ≤ R-‖Q‖*r := by
  let r : ℝ := (a/8)/(C+1)
  have hr : 0 < r := div_pos (by linarith) (by linarith)
  have hCr : (C+1)*r = a/8 := by
    dsimp [r]
    field_simp
  refine ⟨r,a/8,H+a/8+1,hr,by linarith,by linarith,?_⟩
  intro Q hQ reference href hu K hl
  let W : Set Base := {x | a/2 < Q (reference x)}
  have hW : IsOpen W := isOpen_lt continuous_const (Q.continuous.comp href)
  have hKW : K ⊆ W := fun x hx => lt_of_lt_of_le (by linarith) (hl x hx)
  have hnr : ‖Q‖*r ≤ a/8 :=
    (mul_le_mul_of_nonneg_right hQ hr.le).trans (by nlinarith)
  refine ⟨W,hW,hKW,?_⟩
  intro x hx
  have hlx : a/2 < Q (reference x) := hx
  have hux := hu x
  constructor <;> linarith

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridMeanData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mean solvers for the variable grid, with common polynomial budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGrid PhaseGeometry RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance gridMeanDataFiberNormed_rcbc94a_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance gridMeanDataFiberSpace_rcbc94a_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance gridMeanDataDualAdd_rcbc94a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridMeanDataDualSmul_rcbc94a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)


local instance gridMeanDataSectionNormed_rcbc94a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridMeanDataSectionSpace_rcbc94a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_grid_mean_data_oai (g : SmoothMetric M) {a₀ C₀ H : ℝ}
    (ha₀ : 0 < a₀) (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) :
    ∃ (p p' : ℕ → ℕ) (C C' L : ℕ → ℝ),
      (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ C' m) ∧ (∀ m, 1 ≤ L m) ∧
    ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
    ∀ (z : ℝ) (hz : 0 < z), z ≤ 1 → ∀ a : A.centers → Finset Index,
      (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (a i) (z^6)) →
    ∀ (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ),
      (∀ i k j, 1 ≤ w i k j) → (∀ i k j, ‖(Q i k).Q j‖ ≤ C₀) →
      (∀ i k j x, (Q i k).Q j (A.tensorPlaneRead i g.inner x) ≤ H) →
      (∀ i k j x, x ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        a₀ ≤ (Q i k).Q j (A.tensorPlaneRead i g.inner x)) →
    ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 → ∀ D : ℝ, 0 < D →
    ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) → (∀ m, 2*D ≤ B m ∧ C₀ ≤ B m) →
      (∀ i k j m, ‖w i k j • (Q i k).ξ j‖ ≤ B m ∧
        ∀ hξ : w i k j • (Q i k).ξ j ≠ 0,
          ‖(phaseEquiv (w i k j • (Q i k).ξ j) hξ).symm.toContinuousLinearMap‖ ≤ B m) →
      (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
        (B m/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i k j x, x ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ∧
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (w i k j • (Q i k).ξ j) ∧
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x))⁻¹‖ ≤ D ∧
        ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (-(w i k j • (Q i k).ξ j).2,(w i k j • (Q i k).ξ j).1)‖⁻¹ ≤ D) →
      ∃ c : ∀ i (j : (a i) × Fin 3), PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF)
        (phaseLinear (w i j.1 j.2 • (Q i j.1).ξ j.2) ∘ planeCoordinateIsometry)
        (A.cellChartCompact i (a i) (z^6) j.1.val) τ s,
      ∃ d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i g.inner),
        (∀ i j m, (c i j).C m = C m*(B m)^(p m) ∧
          (c i j).J m = 1+2*B m ∧ (c i j).D m = 0) ∧
        (∀ i j x, x ∈ (c i j).e.source → (d i j).cutoff ((c i j).e x) =
          supportedCellCutoff (A.supportedPlaneWeight i) (pow_pos hz 6)
            (hcover i) j.1.val x / w i j.1 j.2) ∧
        (∀ i j, (d i j).form = fun _ => (Q i j.1).Q j.2) ∧
        (∀ i j, tsupport (fun x => A.planeWeight i x * normalizedCutoff (a i) (z^6) j.1.val x) ⊆
          (c i j).e.source) ∧
        ∀ i j m, let b := linearMeanGeometryBudget p' C' B (fun l =>
          1+phaseCutoffBudget l (L l/z^(6*l)) (B l) 1) m;
          (d i j).budgets.inv m ≤ b ∧ (d i j).budgets.chi m ≤ b ∧
          (d i j).budgets.forms m ≤ b ∧ (d i j).budgets.pull m ≤ b ∧
          (d i j).budgets.psi m ≤ b ∧ (d i j).budgets.normal m ≤ b ∧ (d i j).budgets.mode m ≤ b := by
  classical
  obtain ⟨p,p',C,C',hC,hC',hmean⟩ := polynomial_supported_linear_mean_data
  obtain ⟨L,hL,hcut⟩ := A.grid_exact_cutoff_bounds
  obtain ⟨r,ρ,R,hr,hρ,hR,hmargin⟩ := uniform_coefficient_margins ha₀ hC₀ hH
  obtain ⟨U₀,K₀,hU₀,hUK,hKU,_⟩ := A.exists_outer_domains
  have hball := zero_lt_one.trans_le A.one_le_tensorReadBallConstant
  have hballr : A.tensorReadBallConstant*(r/A.tensorReadBallConstant) = r :=
    mul_div_cancel₀ r hball.ne'
  refine ⟨p,p',C,C',L,hC,hC',hL,r/A.tensorReadBallConstant,ρ,R,div_pos hr hball,hρ,hR,?_⟩
  intro z hz hz1 a hcover Q w hw hQ hup hlow F hF τ s hs hs1 D hD B hB hBD hphase hjets hgeom
  rw [hballr]
  let K := fun i (j : (a i) × Fin 3) => A.cellChartCompact i (a i) (z^6) j.1.val
  let φ := fun i (j : (a i) × Fin 3) =>
    phaseLinear (w i j.1 j.2 • (Q i j.1).ξ j.2) ∘ planeCoordinateIsometry
  have local_data (i : A.centers) (j : (a i) × Fin 3) :
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 (A.jetChartMap i F)
          (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s,
      ∃ d : ChartedMeanData c r ρ R (A.tensorPlaneRead i g.inner),
        (∀ m, c.C m = C m*(B m)^(p m)) ∧ (∀ m, c.J m = 1+2*B m) ∧
        (∀ m, c.D m = 0) ∧
        (∀ x ∈ c.e.source, d.cutoff (c.e x) =
          (w i j.1 j.2)⁻¹ * A.exactCellCutoff i (pow_pos hz 6) (hcover i) j.1.val x) ∧
        d.form = (fun _ => (Q i j.1).Q j.2) ∧
        ∀ m, let b := linearMeanGeometryBudget p' C' B (fun l =>
          1+phaseCutoffBudget l (L l/z^(6*l)) (B l) 1) m;
          d.budgets.inv m ≤ b ∧ d.budgets.chi m ≤ b ∧ d.budgets.forms m ≤ b ∧
          d.budgets.pull m ≤ b ∧ d.budgets.psi m ≤ b ∧ d.budgets.normal m ≤ b ∧ d.budgets.mode m ≤ b := by
    let ξ := w i j.1 j.2 • (Q i j.1).ξ j.2
    have hξ : ξ ≠ 0 := smul_ne_zero (ne_of_gt (zero_lt_one.trans_le (hw i j.1 j.2)))
      ((Q i j.1).nonzero j.2)
    obtain ⟨W,hW,hKW,hWmargin⟩ := hmargin ((Q i j.1).Q j.2) (hQ i j.1 j.2)
      (A.tensorPlaneRead i g.inner) (A.tensorPlaneRead_metric_smooth g i).continuous
      (hup i j.1 j.2) (modeSupport (K i j)) (hlow i j.1 j.2)
    let f : SupportedField (F := ℝ) (modeSupport (K i j)) :=
      (w i j.1 j.2)⁻¹ • A.exactCellCutoff i (pow_pos hz 6) (hcover i) j.1.val
    have hP (m : ℕ) : 1 ≤ L m/z^(6*m) :=
      (one_le_div (pow_pos hz _)).mpr ((pow_le_one₀ hz.le hz1).trans (hL m))
    obtain ⟨V,hV,c,d,_,hcC,hcJ,hcD,hψ,hform,hbudget⟩ := hmean
      (A.jetChartMap_smooth i hF) (K i j) hξ hW hKW (hU₀ i) (K₀ i) (hUK i)
      ((A.cellChartCompact_subset i (a i) (z^6) j.1.val).trans (hKU i)) hD
      (by simpa only [A.jetChartMap_plane] using fun x hx => (hgeom i j.1 j.2 x hx).1)
      (by simpa only [A.jetChartMap_plane] using fun x hx => (hgeom i j.1 j.2 x hx).2.1)
      (by simpa only [A.jetChartMap_plane] using fun x hx => (hgeom i j.1 j.2 x hx).2.2.1)
      (by simpa only [A.jetChartMap_plane] using fun x hx => (hgeom i j.1 j.2 x hx).2.2.2)
      ((Q i j.1).Q j.2) hWmargin τ s hs hs1 B (fun m => L m/z^(6*m)) hB hP
      (fun m => ⟨(hBD m).1,(hphase i j.1 j.2 m).1,(hphase i j.1 j.2 m).2 hξ,
        (hQ i j.1 j.2).trans (hBD m).2⟩)
      (by simpa only [A.jetChartMap_plane] using hjets i) f
      (hcut i hz hz1 (hcover i) j.1.val s hs hs1 (w i j.1 j.2) (hw i j.1 j.2))
    exact ⟨c,d,hcC,hcJ,hcD,hψ,hform,hbudget⟩
  choose c d hcC hcJ hcD hψ hform hbudget using local_data
  refine ⟨c,d,fun i j m => ⟨hcC i j m,hcJ i j m,hcD i j m⟩,?_,hform,?_,hbudget⟩
  · intro i j x hx
    rw [hψ i j x hx]
    change (w i j.1 j.2)⁻¹ *
      (A.planeWeight i x * normalizedCutoff (a i) (z^6) j.1.val x) = _
    simp only [supportedCellCutoff_apply,supportedPlaneWeight_apply,div_eq_mul_inv]
    ring
  · intro i j
    exact (A.cellCutoff_tsupport i (pow_pos hz 6) (hcover i) j.1.val).trans (c i j).supportChart

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data_oai.{u_1}
