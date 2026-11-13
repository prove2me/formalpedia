-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:05.589491+00:00
-- url     : https://prove2.me/submissions/7925e8d1-ac69-4722-8703-093856465b57

import Mathlib
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_PhaseGeometry_choose_three_avoiding

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
attribute [-instance] _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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
open SmallModes Set Metric

lemma contDiff_gram_pair : ContDiff ℝ ∞ (fun p : TangentPair => NormalFrame.gramDet p.1 p.2) := by
  unfold NormalFrame.gramDet dotProduct
  fun_prop

lemma contDiffAt_normalColumns {p : TangentPair} (hp : NormalFrame.gramDet p.1 p.2 ≠ 0) :
    ContDiffAt ℝ ∞ normalColumns p := by
  apply contDiffAt_pi.mpr
  intro i
  unfold normalColumns realNormalPart
  have hd : ContDiffAt ℝ ∞ (fun p : TangentPair => NormalFrame.gramDet p.1 p.2) p :=
    contDiff_gram_pair.contDiffAt
  have hX : ContDiffAt ℝ ∞ (fun p : TangentPair => p.1) p := contDiff_fst.contDiffAt
  have hY : ContDiffAt ℝ ∞ (fun p : TangentPair => p.2) p := contDiff_snd.contDiffAt
  apply (contDiffAt_const.sub ?_).sub ?_
  · apply ContDiffAt.fun_smul _ hX
    apply ContDiffAt.fun_div _ hd hp
    unfold dotProduct
    fun_prop
  · apply ContDiffAt.fun_smul _ hY
    apply ContDiffAt.fun_div _ hd hp
    unfold dotProduct
    fun_prop

lemma realNormalPart_columns (p : TangentPair) (W : RVec 4) :
    realNormalPart p.1 p.2 W = ∑ i : Fin 4, W i • normalColumns p i := by
  have hlin := realNormalPart_linear p.1 p.2
  have he : W = ∑ i : Fin 4, W i • (Pi.single i 1 : RVec 4) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => arg 3; rw [he]
  change (hlin.mk' _) (∑ i : Fin 4, W i • Pi.single i 1) = _
  simp only [map_sum,map_smul,IsLinearMap.mk'_apply,normalColumns]

lemma norm_realNormalPart_columns (p : TangentPair) (W : RVec 4) :
    ‖realNormalPart p.1 p.2 W‖ ≤ 4 * ‖normalColumns p‖ * ‖W‖ := by
  rw [realNormalPart_columns]
  calc
    _ ≤ ∑ i : Fin 4, ‖W i • normalColumns p i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖normalColumns p‖ * ‖W‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm W i) (norm_le_pi_norm (normalColumns p) i)
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by simp <;> ring

lemma norm_realNormalPart_change (p q : TangentPair) (W : RVec 4) :
    ‖realNormalPart p.1 p.2 W - realNormalPart q.1 q.2 W‖ ≤
      4 * ‖normalColumns p - normalColumns q‖ * ‖W‖ := by
  rw [realNormalPart_columns,realNormalPart_columns,← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i : Fin 4, W i • (normalColumns p i-normalColumns q i)‖ := by simp [smul_sub]
    _ ≤ ∑ i : Fin 4, ‖W i • (normalColumns p i-normalColumns q i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖normalColumns p-normalColumns q‖ * ‖W‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm W i)
        (norm_le_pi_norm (normalColumns p-normalColumns q) i)
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by simp <;> ring



theorem compact_normal_projection_bounds (R c : ℝ) (hc : 0 < c) :
    ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧ ∀ (p q : TangentPair),
      ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 →
      ‖q‖ ≤ R → c ≤ NormalFrame.gramDet q.1 q.2 → ∀ W Z : RVec 4,
      ‖realNormalPart p.1 p.2 W - realNormalPart q.1 q.2 Z‖ ≤
        L * ‖p-q‖ * ‖W‖ + D * ‖W-Z‖ := by
  let K : Set TangentPair := closedBall 0 R ∩ {p | c ≤ NormalFrame.gramDet p.1 p.2}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const contDiff_gram_pair.continuous)
  have hne (p : TangentPair) (hp : p ∈ K) : NormalFrame.gramDet p.1 p.2 ≠ 0 :=
    (hc.trans_le hp.2).ne'
  have hloc : LocallyLipschitzOn K normalColumns := by
    intro p hp
    obtain ⟨L,U,hU,hL⟩ := ((contDiffAt_normalColumns (hne p hp)).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).exists_lipschitzOnWith
    exact ⟨L,U,Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hU) (fun _ h => h),hL⟩
  obtain ⟨L,hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  have hcont : ContinuousOn normalColumns K := fun p hp =>
    (contDiffAt_normalColumns (hne p hp)).continuousAt.continuousWithinAt
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨4*(L:ℝ),4*max D 0,by positivity,by positivity,?_⟩
  intro p q hp hpD hq hqD W Z
  have hpK : p ∈ K := ⟨by simpa only [mem_closedBall,dist_zero_right] using hp,hpD⟩
  have hqK : q ∈ K := ⟨by simpa only [mem_closedBall,dist_zero_right] using hq,hqD⟩
  have hcols : ‖normalColumns p-normalColumns q‖ ≤ (L:ℝ)*‖p-q‖ := by
    simpa only [dist_eq_norm] using hL.dist_le_mul p hpK q hqK
  have hdecomp : realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z =
      (realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 W) +
        realNormalPart q.1 q.2 (W-Z) := by
    rw [(realNormalPart_linear q.1 q.2).map_sub]
    abel
  rw [hdecomp]
  calc
    _ ≤ ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 W‖ +
        ‖realNormalPart q.1 q.2 (W-Z)‖ := norm_add_le _ _
    _ ≤ 4*‖normalColumns p-normalColumns q‖*‖W‖ + 4*‖normalColumns q‖*‖W-Z‖ :=
      add_le_add (norm_realNormalPart_change p q W) (norm_realNormalPart_columns q (W-Z))
    _ ≤ (4*(L:ℝ))*‖p-q‖*‖W‖ + (4*max D 0)*‖W-Z‖ := by
      have hcq := (hD q hqK).trans (le_max_left D 0)
      nlinarith [mul_le_mul_of_nonneg_right hcols (show 0 ≤ 4*‖W‖ by positivity),
        mul_le_mul_of_nonneg_right hcq (show 0 ≤ 4*‖W-Z‖ by positivity)]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
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

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



lemma secondQuadratic_smul {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (w : ℝ) :
    secondQuadratic B (w • v) = w ^ 2 • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



lemma finite_bad_slopes {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0) :
    Set.Finite {t : ℝ | secondQuadratic B (-t, 1) = 0} := by
  classical
  have hex : ∃ j i, B j i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hB (funext fun j => funext fun i => hn j i)
  obtain ⟨j, i, hji⟩ := hex
  let p : ℝ[X] := C (B 0 i) * X ^ 2 - C (2 * B 1 i) * X + C (B 2 i)
  have hp : p ≠ 0 := by
    intro hz
    have h0 := congrArg (fun P : ℝ[X] => P.coeff 0) hz
    have h1 := congrArg (fun P : ℝ[X] => P.coeff 1) hz
    have h2 := congrArg (fun P : ℝ[X] => P.coeff 2) hz
    simp [p, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow] at h0 h1 h2
    fin_cases j <;> simp_all
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro t ht
  have hi := congrFun ht i
  simp only [secondQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    neg_sq, one_pow, mul_one, one_mul] at hi
  change p.eval t = 0
  simp only [p, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  nlinarith [hi]

lemma finite_affine_preimage {T : Set ℝ} (hT : T.Finite) {a b : ℝ} (ha : a ≠ 0) :
    ( (fun t : ℝ => a * t + b) ⁻¹' T).Finite := by
  apply hT.preimage
  intro x hx y hy he
  exact mul_left_cancel₀ ha (by linarith)



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PositiveBasis
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean
open Set


lemma basisCoefficient_apply (t u v : ℝ) (H : PhaseMean.Tensor) :
    basisCoefficient t u v H = (H 2 - (u + v) * H 1 + u * v * H 0) / ((t - u) * (t - v)) := by
  simp only [basisCoefficient, smul_apply, add_apply,
    sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, div_eq_mul_inv]
  ring

lemma covectorSquare_smul (w : ℝ) (ξ : Base) :
    covectorSquare (w • ξ) = w ^ 2 • covectorSquare ξ := by
  ext i
  fin_cases i <;> simp [covectorSquare, smul_eq_mul] <;> ring



lemma three_slope_decomposition {t₀ t₁ t₂ : ℝ} (h₀₁ : t₀ ≠ t₁)
    (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) (H : PhaseMean.Tensor) :
    basisCoefficient t₀ t₁ t₂ H • covectorSquare (1, t₀) +
      basisCoefficient t₁ t₀ t₂ H • covectorSquare (1, t₁) +
      basisCoefficient t₂ t₀ t₁ H • covectorSquare (1, t₂) = H := by
  have h10 : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr h₀₁.symm
  have h20 : t₂ - t₀ ≠ 0 := sub_ne_zero.mpr h₀₂.symm
  have h21 : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have h01 : t₀ - t₁ ≠ 0 := sub_ne_zero.mpr h₀₁
  have h02 : t₀ - t₂ ≠ 0 := sub_ne_zero.mpr h₀₂
  have h12 : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h₁₂
  ext i
  fin_cases i <;>
    simp [Pi.add_apply, basisCoefficient_apply, covectorSquare] <;>
    field_simp [h10, h20, h21, h01, h02, h12] <;> ring



lemma normalized_numerators_positive {x₀ x₁ x₂ : ℝ}
    (h₀ : x₀ ∈ Ioo (-3 : ℝ) (-2)) (h₁ : x₁ ∈ Ioo (-(1/4) : ℝ) (1/4))
    (h₂ : x₂ ∈ Ioo (2 : ℝ) 3) :
    0 < 1 + x₁*x₂ ∧ 1 + x₀*x₂ < 0 ∧ 0 < 1 + x₀*x₁ := by
  have hx₂ : 0 < x₂ := by linarith [h₂.1]
  have hx₀ : 0 < -x₀ := by linarith [h₀.2]
  have hp₁ := mul_pos (show 0 < x₁ + 1/4 by linarith [h₁.1]) hx₂
  have hp₂ := mul_pos (show 0 < -x₀ - 2 by linarith [h₀.2]) hx₂
  have hp₃ := mul_pos (show 0 < 1/4 - x₁ by linarith [h₁.2]) hx₀
  constructor
  · nlinarith [h₂.2]
  constructor
  · nlinarith [h₂.1]
  · nlinarith [h₀.1]

lemma positive_center_parameters {H : PhaseMean.Tensor} (h₀ : 0 < H 0)
    (hdet : 0 < H 0 * H 2 - (H 1) ^ 2) :
    ∃ β r : ℝ, 0 < r ∧ H 1 = H 0 * β ∧ H 2 = H 0 * (β ^ 2 + r ^ 2) := by
  let β := H 1 / H 0
  let D := H 2 / H 0 - β ^ 2
  have hD : 0 < D := by
    have he : D = (H 0 * H 2 - (H 1) ^ 2) / (H 0) ^ 2 := by
      dsimp [D, β]
      field_simp
    rw [he]
    exact div_pos hdet (sq_pos_of_pos h₀)
  refine ⟨β, Real.sqrt D, Real.sqrt_pos.2 hD, ?_, ?_⟩
  · dsimp [β]
    field_simp
  · rw [Real.sq_sqrt hD.le]
    dsimp [D]
    field_simp
    ring

lemma shifted_numerator (H : PhaseMean.Tensor) {β r : ℝ}
    (h₁ : H 1 = H 0 * β) (h₂ : H 2 = H 0 * (β ^ 2 + r ^ 2)) (u v : ℝ) :
    H 2 - ((β + r*u) + (β + r*v)) * H 1 + (β + r*u)*(β + r*v)*H 0 =
      H 0 * r ^ 2 * (1 + u*v) := by
  rw [h₁, h₂]
  ring

lemma shifted_basis_positive {H : PhaseMean.Tensor} (h₀ : 0 < H 0)
    {β r x₀ x₁ x₂ : ℝ} (hr : 0 < r)
    (h₁ : H 1 = H 0 * β) (h₂ : H 2 = H 0 * (β ^ 2 + r ^ 2))
    (hx₀ : x₀ ∈ Ioo (-3 : ℝ) (-2)) (hx₁ : x₁ ∈ Ioo (-(1/4) : ℝ) (1/4))
    (hx₂ : x₂ ∈ Ioo (2 : ℝ) 3) :
    0 < basisCoefficient (β+r*x₀) (β+r*x₁) (β+r*x₂) H ∧
    0 < basisCoefficient (β+r*x₁) (β+r*x₀) (β+r*x₂) H ∧
    0 < basisCoefficient (β+r*x₂) (β+r*x₀) (β+r*x₁) H := by
  have hnum := normalized_numerators_positive hx₀ hx₁ hx₂
  have h01 : β+r*x₀ < β+r*x₁ := by nlinarith [hx₀.2, hx₁.1]
  have h12 : β+r*x₁ < β+r*x₂ := by nlinarith [hx₁.2, hx₂.1]
  have hp : 0 < H 0 * r ^ 2 := mul_pos h₀ (sq_pos_of_pos hr)
  simp only [basisCoefficient_apply, shifted_numerator H h₁ h₂]
  refine ⟨div_pos (mul_pos hp hnum.1) (mul_pos_of_neg_of_neg (sub_neg.mpr h01)
    (sub_neg.mpr (h01.trans h12))), ?_, ?_⟩
  · exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp hnum.2.1)
      (mul_neg_of_pos_of_neg (sub_pos.mpr h01) (sub_neg.mpr h12))
  · exact div_pos (mul_pos hp hnum.2.2)
      (mul_pos (sub_pos.mpr (h01.trans h12)) (sub_pos.mpr h12))

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma good_weighted {n : ℕ} {B : Fin 3 → RVec n} {t w : ℝ}
    (hw : w ≠ 0) (ht : secondQuadratic B (-t, 1) ≠ 0) : Good B (w, w*t) := by
  constructor
  · intro hz
    exact hw (congrArg Prod.fst hz)
  · have he : (-(w*t), w) = w • (-t, (1 : ℝ)) := by
      ext <;> simp
    rw [he, secondQuadratic_smul]
    exact smul_ne_zero (pow_ne_zero 2 hw) ht



theorem positive_good_slopes {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0)
    {H : PhaseMean.Tensor} (h₀ : 0 < H 0) (hdet : 0 < H 0 * H 2 - (H 1)^2) :
    ∃ t₀ t₁ t₂ : ℝ, t₀ < t₁ ∧ t₁ < t₂ ∧
      0 < basisCoefficient t₀ t₁ t₂ H ∧ 0 < basisCoefficient t₁ t₀ t₂ H ∧
      0 < basisCoefficient t₂ t₀ t₁ H ∧
      secondQuadratic B (-t₀, 1) ≠ 0 ∧ secondQuadratic B (-t₁, 1) ≠ 0 ∧
      secondQuadratic B (-t₂, 1) ≠ 0 ∧
      secondQuadratic B (-((t₀ + 2*t₁)/3), 1) ≠ 0 ∧
      secondQuadratic B (-(2*t₁-t₀), 1) ≠ 0 ∧
      secondQuadratic B (-((t₀ + 4*t₂)/5), 1) ≠ 0 ∧
      secondQuadratic B (-((4*t₂-t₀)/3), 1) ≠ 0 ∧
      secondQuadratic B (-((t₁ + 2*t₂)/3), 1) ≠ 0 ∧
      secondQuadratic B (-(2*t₂-t₁), 1) ≠ 0 := by
  obtain ⟨β, r, hr, h₁, h₂⟩ := positive_center_parameters h₀ hdet
  let T : Set ℝ := (fun x : ℝ => r*x + β) ⁻¹' {t : ℝ | secondQuadratic B (-t, 1) = 0}
  have hT : T.Finite := finite_affine_preimage (finite_bad_slopes hB) hr.ne'
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hn₀, hn₁, hn₂, hn₃, hn₄, hn₅, hn₆, hn₇, hn₈⟩ :=
    choose_three_avoiding hT (show (-3 : ℝ) < -2 by norm_num)
      (show (-(1/4) : ℝ) < 1/4 by norm_num) (show (2 : ℝ) < 3 by norm_num)
  have hn : ∀ {x : ℝ}, x ∉ T → secondQuadratic B (-(β+r*x), 1) ≠ 0 := by
    intro x hx
    simpa only [T, mem_preimage, mem_ofPred_eq, add_comm] using hx
  have hpos := shifted_basis_positive h₀ hr h₁ h₂ hx₀ hx₁ hx₂
  refine ⟨β+r*x₀, β+r*x₁, β+r*x₂, ?_, ?_, hpos.1, hpos.2.1, hpos.2.2,
    hn hn₀, hn hn₁, hn hn₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [hx₀.2, hx₁.1]
  · nlinarith [hx₁.2, hx₂.1]
  · convert hn hn₃ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₄ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₅ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₆ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₇ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · convert hn hn₈ using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_neg {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base} (h : Good B ξ) : Good B (-ξ) := by
  constructor
  · exact neg_ne_zero.mpr h.1
  · have he : (-(-ξ).2, (-ξ).1) = (-1 : ℝ) • (-ξ.2, ξ.1) := by ext <;> simp
    rw [he, secondQuadratic_smul]
    simpa using h.2



theorem positive_good_phase_data {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0)
    {H₀ : PhaseMean.Tensor} (h₀ : 0 < H₀ 0) (hdet : 0 < H₀ 0 * H₀ 2 - (H₀ 1)^2) :
    ∃ (ξ : Fin 3 → Base) (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ),
      (∀ H, ∑ i : Fin 3, Q i H • covectorSquare (ξ i) = H) ∧
      (∀ i, 0 < Q i H₀) ∧ (∀ i, Good B (ξ i)) ∧
      (∀ i j, i ≠ j → Good B (ξ i + ξ j) ∧ Good B (ξ i - ξ j)) := by
  obtain ⟨t₀, t₁, t₂, h01, h12, hp₀, hp₁, hp₂, hg₀, hg₁, hg₂, hg₃, hg₄, hg₅, hg₆, hg₇, hg₈⟩ :=
    positive_good_slopes hB h₀ hdet
  let ξ : Fin 3 → Base := ![(1, t₀), (2, 2*t₁), (4, 4*t₂)]
  let Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ :=
    ![basisCoefficient t₀ t₁ t₂, (1/4 : ℝ) • basisCoefficient t₁ t₀ t₂,
      (1/16 : ℝ) • basisCoefficient t₂ t₀ t₁]
  have hξ₁ : ξ 1 = (2 : ℝ) • (1, t₁) := by ext <;> simp [ξ]
  have hξ₂ : ξ 2 = (4 : ℝ) • (1, t₂) := by ext <;> simp [ξ]
  have h03 : Good B (ξ 0 + ξ 1) := by
    convert good_weighted (B := B) (w := 3) (by norm_num) hg₃ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  have h04 : Good B (ξ 1 - ξ 0) := by
    convert good_weighted (B := B) (w := 1) (by norm_num) hg₄ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ]
    ring
  have h05 : Good B (ξ 0 + ξ 2) := by
    convert good_weighted (B := B) (w := 5) (by norm_num) hg₅ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  have h06 : Good B (ξ 2 - ξ 0) := by
    convert good_weighted (B := B) (w := 3) (by norm_num) hg₆ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  have h07 : Good B (ξ 1 + ξ 2) := by
    convert good_weighted (B := B) (w := 6) (by norm_num) hg₇ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  have h08 : Good B (ξ 2 - ξ 1) := by
    convert good_weighted (B := B) (w := 2) (by norm_num) hg₈ using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [ξ] <;> ring
  refine ⟨ξ, Q, ?_, ?_, ?_, ?_⟩
  · intro H
    rw [Fin.sum_univ_three, hξ₁, hξ₂, covectorSquare_smul, covectorSquare_smul]
    convert three_slope_decomposition h01.ne (h01.trans h12).ne h12.ne H using 1
    all_goals try with_reducible_and_instances rfl
    ext i
    simp [Q, ξ, Pi.smul_apply, smul_smul, smul_eq_mul]
    ring
  · intro i
    fin_cases i <;> simp [Q]
    · exact hp₀
    · positivity
    · positivity
  · intro i
    fin_cases i
    · simpa [ξ] using good_weighted (w := 1) (by norm_num) hg₀
    · simpa [ξ] using good_weighted (w := 2) (by norm_num) hg₁
    · simpa [ξ] using good_weighted (w := 4) (by norm_num) hg₂
  · intro i j hij
    have h40 := good_neg h04
    have h60 := good_neg h06
    have h80 := good_neg h08
    simp only [neg_sub] at h40 h60 h80
    fin_cases i <;> fin_cases j <;> simp_all [add_comm]

end ClosedSurfaceR4.PhaseGeometry

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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
open SmallModes Set Metric



theorem uniform_gram_neighborhood (R c : ℝ) (hc : 0 < c) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ p q : TangentPair,
      ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 → ‖p-q‖ ≤ η →
      ‖q‖ ≤ R+1 ∧ c/2 ≤ NormalFrame.gramDet q.1 q.2 := by
  obtain ⟨L,hL⟩ := contDiff_gram_pair.contDiffOn.exists_lipschitzOnWith
    (show (∞ : ℕ∞ω) ≠ 0 by simp) (convex_closedBall (0 : TangentPair) (R+1))
    (isCompact_closedBall _ _)
  let η : ℝ := min 1 (c/(2*((L:ℝ)+1)))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hc (by positivity))
  refine ⟨η,hη,min_le_left _ _,fun p q hp hpD hpq => ?_⟩
  have hq : ‖q‖ ≤ R+1 := by
    calc ‖q‖ ≤ ‖p‖+‖q-p‖ := norm_le_insert' q p
         _ = ‖p‖+‖p-q‖ := by rw [norm_sub_rev q p]
         _ ≤ R+1 := add_le_add hp (hpq.trans (min_le_left _ _))
  have hpK : p ∈ closedBall 0 (R+1) := by
    rw [mem_closedBall,dist_zero_right]
    linarith
  have hqK : q ∈ closedBall 0 (R+1) := by simpa only [mem_closedBall,dist_zero_right] using hq
  have hl : |NormalFrame.gramDet p.1 p.2-NormalFrame.gramDet q.1 q.2| ≤ (L:ℝ)*‖p-q‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs] using hL.dist_le_mul p hpK q hqK
  have hηc : (L:ℝ)*η ≤ c/2 := by
    have hmin : η ≤ c/(2*((L:ℝ)+1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (show 0 < 2*((L:ℝ)+1) by positivity)).mp hmin
    nlinarith [hη.le]
  refine ⟨hq,?_⟩
  have hdiff := (le_abs_self _).trans (hl.trans (mul_le_mul_of_nonneg_left hpq L.coe_nonneg))
  linarith



theorem uniform_normal_projection_stability (R c : ℝ) (hc : 0 < c) :
    ∃ η L D : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ D ∧
      ∀ p q : TangentPair, ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 →
        ‖p-q‖ ≤ η → ∀ W Z : RVec 4,
        ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z‖ ≤
          L*‖p-q‖*‖W‖+D*‖W-Z‖ := by
  obtain ⟨η,hη,hη1,hηb⟩ := uniform_gram_neighborhood R c hc
  obtain ⟨L,D,hL,hD,hb⟩ := compact_normal_projection_bounds (R+1) (c/2) (half_pos hc)
  refine ⟨η,L,D,hη,hη1,hL,hD,fun p q hp hpD hpq W Z => ?_⟩
  obtain ⟨hq,hqD⟩ := hηb p q hp hpD hpq
  exact hb p q (by linarith) (by linarith) hq hqD W Z




theorem normal_projection_z4_stability (R c : ℝ) (hc : 0 < c) (A : ℝ) (hA : 0 ≤ A) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (z : ℝ), 0 < z → z ≤ 1 → z^4 ≤ η →
      ∀ (p q : TangentPair) (W Z : RVec 4), ‖p‖ ≤ R →
        c ≤ NormalFrame.gramDet p.1 p.2 → ‖p-q‖ ≤ z^4 →
        ‖W‖ ≤ A/z^2 → ‖W-Z‖ ≤ z^4 →
        ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z‖ ≤ C*z^2 := by
  obtain ⟨η,L,D,hη,_,hL,hD,hb⟩ := uniform_normal_projection_stability R c hc
  refine ⟨η,L*A+D,hη,by positivity,fun z hz hz1 hzη p q W Z hp hpD hpq hW hWZ => ?_⟩
  have hh := hb p q hp hpD (hpq.trans hzη) W Z
  have hz42 : z^4 ≤ z^2 := pow_le_pow_of_le_one hz.le hz1 (by norm_num : 2 ≤ 4)
  calc
    _ ≤ L*‖p-q‖*‖W‖+D*‖W-Z‖ := hh
    _ ≤ L*z^4*(A/z^2)+D*z^4 := by gcongr
    _ ≤ L*z^4*(A/z^2)+D*z^2 := by gcongr
    _ = (L*A+D)*z^2 := by field_simp [hz.ne']

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set

lemma realSecondTensor_eq_projection (F : RField 4) (p : Base) (i : Fin 3) :
    realSecondTensor F p i =
      realNormalPart (firstJetPair F p).1 (firstJetPair F p).2 (secondJetTriple F p i) := by
  fin_cases i <;> rfl





theorem secondTensor_z4_stability (R c A : ℝ) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (z : ℝ), 0 < z → z ≤ 1 → z^4 ≤ η →
      ∀ (F G : RField 4) (p : Base), ‖firstJetPair F p‖ ≤ R →
      c ≤ NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2 →
      ‖firstJetPair F p-firstJetPair G p‖ ≤ z^4 →
      ‖secondJetTriple F p‖ ≤ A/z^2 →
      ‖secondJetTriple F p-secondJetTriple G p‖ ≤ z^4 →
      ‖realSecondTensor F p-realSecondTensor G p‖ ≤ C*z^2 := by
  obtain ⟨η,C,hη,hC,hb⟩ := normal_projection_z4_stability R c hc A hA
  refine ⟨η,C,hη,hC,fun z hz hz1 hzη F G p hp hpD hpq hH hHG => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simp only [Pi.sub_apply,realSecondTensor_eq_projection]
  exact hb z hz hz1 hzη _ _ _ _ hp hpD hpq
    ((norm_le_pi_norm _ i).trans hH) ((norm_le_pi_norm _ i).trans hHG)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
attribute [-instance] _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DirectionStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma secondQuadratic_sub_form {n : ℕ} (B C : Fin 3 → RVec n) (v : Base) :
    secondQuadratic (B-C) v = secondQuadratic B v-secondQuadratic C v := by
  simp only [secondQuadratic,Pi.sub_apply,smul_sub]
  abel

lemma norm_secondQuadratic_le {n : ℕ} (B : Fin 3 → RVec n) (v : Base) :
    ‖secondQuadratic B v‖ ≤ 4*‖B‖*‖v‖^2 := by
  have h1 : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  have hq1 : |v.1^2| ≤ ‖v‖^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hq2 : |v.2^2| ≤ ‖v‖^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hm : |2*v.1*v.2| ≤ 2*‖v‖^2 := by
    simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg v)]
  unfold secondQuadratic
  calc
    _ ≤ (‖v.1^2 • B 0‖+‖(2*v.1*v.2) • B 1‖)+‖v.2^2 • B 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖^2*‖B‖+(2*‖v‖^2)*‖B‖)+‖v‖^2*‖B‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      gcongr
      · exact norm_le_pi_norm B 0
      · exact norm_le_pi_norm B 1
      · exact norm_le_pi_norm B 2
    _ = _ := by ring

lemma norm_rotated_covector (ξ : Base) : ‖(-ξ.2,ξ.1)‖ = ‖ξ‖ := by
  simp only [Prod.norm_def,norm_neg]
  exact max_comm _ _




theorem second_form_direction_persists {n : ℕ} (B C : Fin 3 → RVec n) (ξ : Base)
    {κ : ℝ} (hκ : 0 < κ) (hB : κ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖)
    (hBC : 4*‖B-C‖*‖ξ‖^2 ≤ κ/2) :
    κ/2 ≤ ‖secondQuadratic C (-ξ.2,ξ.1)‖ ∧ Good C ξ := by
  have he : ‖secondQuadratic B (-ξ.2,ξ.1)-secondQuadratic C (-ξ.2,ξ.1)‖ ≤ κ/2 := by
    rw [← secondQuadratic_sub_form]
    exact (norm_secondQuadratic_le _ _).trans (by simpa only [norm_rotated_covector] using hBC)
  have hb' : κ/2 ≤ ‖secondQuadratic C (-ξ.2,ξ.1)‖ := by
    have hh := norm_sub_norm_le (secondQuadratic B (-ξ.2,ξ.1)) (secondQuadratic C (-ξ.2,ξ.1))
    linarith
  have hn := norm_pos_iff.mp ((half_pos hκ).trans_le hb')
  refine ⟨hb',?_,hn⟩
  intro hz
  apply hn
  simp [hz,secondQuadratic]

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.WeightedEstimates
open Set

lemma WeightedBound.convex_variation {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {s A : ℝ} {f : E → G} (hs : 0 < s)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s 1 A f)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f x-f y‖ ≤ (A/s)*‖x-y‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderivWithin_le
    (hf.differentiableOn (by simp)) _ hconv hy hx
  intro p hp
  have hh := hb.deriv_le hs (show 1 ≤ 1 by rfl) hp
  simpa only [norm_iteratedFDerivWithin_one (𝕜 := ℝ) f (hU.uniqueDiffOn p hp),pow_one] using hh

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates Set

lemma weighted_coordinate_second_jet {F : RField 4} {U : Set Base} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) {z A : ℝ} (hz : 0 < z)
    (hb : WeightedBound U z 3 A F) {v w : Base} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    WeightedBound U z 1 (A/z^2) (coordDeriv v (coordDeriv w F)) := by
  have h1 : WeightedBound U z 2 (A/z) (coordDeriv w F) := by
    have hh := hb.directional hU hz hF w
    simp only [hw,one_mul] at hh
    exact hh.congr (fun p hp => rfl)
  have h2 := h1.directional hU hz (contDiffOn_coordDeriv_vector hU hF w) v
  simp only [hv,one_mul,div_div,← pow_two] at h2
  exact h2.congr (fun p hp => rfl)

lemma coordinate_jets_variation {F : RField 4} {U : Set Base} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hF : ContDiffOn ℝ ∞ F U) {z A : ℝ} (hz : 0 < z)
    (hA : 0 ≤ A) (hb : WeightedBound U z 3 A F) {x y : Base} (hx : x ∈ U) (hy : y ∈ U) :
    ‖firstJetPair F x-firstJetPair F y‖ ≤ (A/z^2)*‖x-y‖ ∧
    ‖secondJetTriple F x‖ ≤ A/z^2 ∧
    ‖secondJetTriple F x-secondJetTriple F y‖ ≤ (A/z^3)*‖x-y‖ := by
  have hdx : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have hdy : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have h1 (v : Base) (hv : ‖v‖ = 1) :
      ‖coordDeriv v F x-coordDeriv v F y‖ ≤ (A/z^2)*‖x-y‖ := by
    have hh : WeightedBound U z 1 (A/z) (coordDeriv v F) := by
      have hh := (hb.mono_order (by omega : 2 ≤ 3)).directional hU hz hF v
      simp only [hv,one_mul] at hh
      exact hh.congr (fun p hp => rfl)
    simpa only [div_div,pow_two] using hh.convex_variation hU hconv hz
      (contDiffOn_coordDeriv_vector hU hF v) hx hy
  have h2 (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖coordDeriv v (coordDeriv w F) x‖ ≤ A/z^2 ∧
      ‖coordDeriv v (coordDeriv w F) x-coordDeriv v (coordDeriv w F) y‖ ≤ (A/z^3)*‖x-y‖ := by
    have hh := weighted_coordinate_second_jet hU hF hz hb hv hw
    refine ⟨hh.norm_le hx,?_⟩
    have hvw := hh.convex_variation hU hconv hz
      (contDiffOn_coordDeriv_vector hU (contDiffOn_coordDeriv_vector hU hF w) v) hx hy
    simpa only [div_div,← pow_succ] using hvw
  refine ⟨?_,?_,?_⟩
  · change max ‖coordDeriv dx F x-coordDeriv dx F y‖ ‖coordDeriv dy F x-coordDeriv dy F y‖ ≤ _
    exact max_le (h1 dx hdx) (h1 dy hdy)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · exact (h2 dx dx hdx hdx).1
    · exact (h2 dx dy hdx hdy).1
    · exact (h2 dy dy hdy hdy).1
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · exact (h2 dx dx hdx hdx).2
    · exact (h2 dx dy hdx hdy).2
    · exact (h2 dy dy hdy hdy).2




theorem second_form_cell_variation (R c A : ℝ) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℝ), 0 < z → z ≤ 1 →
      ∀ (F : RField 4) (U : Set Base), IsOpen U → Convex ℝ U → ContDiffOn ℝ ∞ F U →
      WeightedBound U z 3 A F →
      (∀ p ∈ U, ‖firstJetPair F p‖ ≤ R ∧ c ≤ NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2) →
      ∀ x ∈ U, ∀ y ∈ U, ‖realSecondTensor F x-realSecondTensor F y‖ ≤ (C/z^4)*‖x-y‖ := by
  obtain ⟨L,D,hL,hD,hb⟩ := compact_normal_projection_bounds R c hc
  refine ⟨L*A^2+D*A,by positivity,fun z hz hz1 F U hU hconv hF hFbound hmetric x hx y hy => ?_⟩
  obtain ⟨h1,h2,h3⟩ := coordinate_jets_variation hU hconv hF hz hA hFbound hx hy
  have hp4 : z^4 ≤ z^3 := pow_le_pow_of_le_one hz.le hz1 (by omega : 3 ≤ 4)
  have h43 : A/z^3 ≤ A/z^4 := div_le_div_of_nonneg_left hA (pow_pos hz 4) hp4
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simp only [Pi.sub_apply,realSecondTensor_eq_projection]
  have hh := hb (firstJetPair F x) (firstJetPair F y)
    (hmetric x hx).1 (hmetric x hx).2 (hmetric y hy).1 (hmetric y hy).2
    (secondJetTriple F x i) (secondJetTriple F y i)
  calc
    _ ≤ L*‖firstJetPair F x-firstJetPair F y‖*‖secondJetTriple F x i‖+
        D*‖secondJetTriple F x i-secondJetTriple F y i‖ := hh
    _ ≤ L*((A/z^2)*‖x-y‖)*(A/z^2)+D*((A/z^3)*‖x-y‖) := by
      gcongr
      · exact (norm_le_pi_norm _ i).trans h2
      · exact (norm_le_pi_norm _ i).trans h3
    _ ≤ L*((A/z^2)*‖x-y‖)*(A/z^2)+D*((A/z^4)*‖x-y‖) := by gcongr
    _ = _ := by field_simp [hz.ne']

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridBumps
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.Path.extend_div_self
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
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseWeights
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
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



lemma compact_finite_uniform_margin {X ι : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) (hpos : ∀ x ∈ K, ∃ i, 0 < f i x) :
    ∃ (s : Finset ι) (ε : ℝ), 0 < ε ∧ ∀ x ∈ K, ∃ i ∈ s, ε < f i x := by
  classical
  choose i hi using fun x : K => hpos x x.property
  let d (p : K) : ℝ := f (i p) p / 2
  have hd (p : K) : 0 < d p := half_pos (hi p)
  let U (p : K) : Set X := {x | d p < f (i p) x}
  have hU (p : K) : IsOpen (U p) := isOpen_lt continuous_const (hf (i p))
  have hcover : K ⊆ ⋃ p : K, U p := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x,hx⟩, ?_⟩
    change f (i ⟨x,hx⟩) x / 2 < f (i ⟨x,hx⟩) x
    linarith [hi ⟨x,hx⟩]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcover
  by_cases htn : t.Nonempty
  · let ε : ℝ := t.inf' htn d
    have hε : 0 < ε := (Finset.lt_inf'_iff htn).mpr (fun p _ => hd p)
    refine ⟨t.image i, ε, hε, ?_⟩
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (ht hx)
    refine ⟨i p, Finset.mem_image.mpr ⟨p,hp,rfl⟩, ?_⟩
    exact lt_of_le_of_lt (Finset.inf'_le d hp) hxp
  · refine ⟨∅, 1, zero_lt_one, ?_⟩
    intro x hx
    obtain ⟨p,hp,_⟩ := mem_iUnion₂.mp (ht hx)
    exact (htn ⟨p,hp⟩).elim



lemma PhaseBasis.margin_lt_iff {n : ℕ} (P : PhaseBasis) (z : PhaseInput n) (ε : ℝ) :
    ε < P.margin z ↔ ∀ i, ε < P.Q i z.2 ∧
      ε < ‖secondQuadratic z.1 (-(P.ξ i).2, (P.ξ i).1)‖ := by
  simp [PhaseBasis.margin, Finset.lt_inf'_iff, lt_min_iff]

lemma PhaseBasis.margin_continuous {n : ℕ} (P : PhaseBasis) :
    Continuous (P.margin (n := n)) := by
  apply Continuous.finset_inf'_apply
  intro i _
  exact ((P.Q i).continuous.comp continuous_snd).min
    (continuous_secondQuadratic.comp (continuous_fst.prodMk continuous_const)).norm

lemma positive_input_has_basis {n : ℕ} {z : PhaseInput n}
    (hB : z.1 ≠ 0) (hH0 : 0 < z.2 0) (hdet : 0 < z.2 0 * z.2 2 - (z.2 1)^2) :
    ∃ P : PhaseBasis, 0 < P.margin z := by
  obtain ⟨ξ,Q,hdec,hpos,hgood,_⟩ := positive_good_phase_data hB hH0 hdet
  let P : PhaseBasis := ⟨ξ,Q,hdec,fun i => (hgood i).1⟩
  refine ⟨P,(P.margin_lt_iff z 0).mpr (fun i => ?_)⟩
  exact ⟨hpos i, norm_pos_iff.mpr (hgood i).2⟩




theorem compact_positive_phase_bases {n : ℕ} {K : Set (PhaseInput n)}
    (hK : IsCompact K)
    (hB : ∀ z ∈ K, z.1 ≠ 0)
    (hH0 : ∀ z ∈ K, 0 < z.2 0)
    (hdet : ∀ z ∈ K, 0 < z.2 0 * z.2 2 - (z.2 1)^2) :
    ∃ (s : Finset PhaseBasis) (ε : ℝ), 0 < ε ∧ ∀ z ∈ K,
      ∃ P ∈ s, ∀ i, ε < P.Q i z.2 ∧
        ε < ‖secondQuadratic z.1 (-(P.ξ i).2, (P.ξ i).1)‖ := by
  obtain ⟨s,ε,hε,hs⟩ := compact_finite_uniform_margin hK
    (fun P : PhaseBasis => P.margin) (fun P => P.margin_continuous)
    (fun z hz => positive_input_has_basis (hB z hz) (hH0 z hz) (hdet z hz))
  refine ⟨s,ε,hε,fun z hz => ?_⟩
  obtain ⟨P,hP,hpm⟩ := hs z hz
  exact ⟨P,hP,(P.margin_lt_iff z ε).mp hpm⟩

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean Set

lemma secondQuadratic_smul_form {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (a : ℝ) :
    secondQuadratic (a • B) v = a • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



theorem normalized_positive_phase_bases {n : ℕ} {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0 * H 2 - (H 1)^2) :
    ∃ (s : Finset PhaseBasis) (ε : ℝ), 0 < ε ∧
      ∀ (B : Fin 3 → RVec n) (H : PhaseMean.Tensor), B ≠ 0 → H ∈ T →
      ∃ P ∈ s, ∀ i, ε < P.Q i H ∧
        ε * ‖B‖ < ‖secondQuadratic B (-(P.ξ i).2, (P.ξ i).1)‖ := by
  let K : Set (PhaseInput n) := Metric.sphere 0 1 ×ˢ T
  have hK : IsCompact K := (isCompact_sphere (0 : Fin 3 → RVec n) 1).prod hT
  have hnorm (z : PhaseInput n) (hz : z ∈ K) : ‖z.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz.1
  obtain ⟨s,ε,hε,hs⟩ := compact_positive_phase_bases hK
    (fun z hz => norm_ne_zero_iff.mp (by rw [hnorm z hz]; norm_num))
    (fun z hz => hT0 z.2 hz.2) (fun z hz => hTd z.2 hz.2)
  refine ⟨s,ε,hε,fun B H hB hH => ?_⟩
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hunit : ‖(‖B‖⁻¹ : ℝ) • B‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hz : ((‖B‖⁻¹ : ℝ) • B,H) ∈ K :=
    ⟨by simpa [Metric.mem_sphere, dist_zero_right] using hunit, hH⟩
  obtain ⟨P,hPs,hP⟩ := hs _ hz
  refine ⟨P,hPs,fun i => ⟨(hP i).1,?_⟩⟩
  have hi := (hP i).2
  simp only [secondQuadratic_smul_form, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hn] at hi
  have ht := mul_lt_mul_of_pos_right hi hn
  simpa only [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel₀ hn.ne', mul_one, one_mul] using ht



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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





end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PolynomialPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma finite_phase_basis_bounds (s : Finset PhaseBasis) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P ∈ s, ∀ i, ‖P.ξ i‖ ≤ C ∧ ‖P.Q i‖ ≤ C := by
  classical
  let d (P : PhaseBasis) := ∑ i : Fin 3, (‖P.ξ i‖+‖P.Q i‖)
  have hd (P : PhaseBasis) : 0 ≤ d P := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨1+∑ P ∈ s, d P,by linarith [Finset.sum_nonneg (fun P (_ : P ∈ s) => hd P)],?_⟩
  intro P hP i
  have hi : ‖P.ξ i‖+‖P.Q i‖ ≤ d P :=
    Finset.single_le_sum (f := fun j => ‖P.ξ j‖+‖P.Q j‖) (fun j (_ : j ∈ Finset.univ) => by positivity) (Finset.mem_univ i)
  have hp : d P ≤ ∑ P ∈ s, d P := Finset.single_le_sum (fun P (_ : P ∈ s) => hd P) hP
  constructor <;> linarith [norm_nonneg (P.ξ i),norm_nonneg (P.Q i)]




theorem finite_phase_stock_neighborhoods {n : ℕ} {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) :
    ∃ (s : Finset PhaseBasis) (ε C δ : ℝ), 0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      (∀ P ∈ s, ∀ i, ‖P.ξ i‖ ≤ C ∧ ‖P.Q i‖ ≤ C) ∧
      ∀ (B : Fin 3 → RVec n) (H : PhaseMean.Tensor), B ≠ 0 → H ∈ T →
      ∃ P ∈ s, ∀ (B' : Fin 3 → RVec n) (H' : PhaseMean.Tensor),
        ‖B'-B‖ ≤ δ*‖B‖ → ‖H'-H‖ ≤ δ →
        ∀ i, ε/2 ≤ P.Q i H' ∧
          (ε/4)*‖B'‖ ≤ ‖secondQuadratic B' (-(P.ξ i).2,(P.ξ i).1)‖ ∧ Good B' (P.ξ i) := by
  obtain ⟨s,ε,hε,hs⟩ := normalized_positive_phase_bases (n := n) hT hT0 hTd
  obtain ⟨C,hC,hbounds⟩ := finite_phase_basis_bounds s
  let δ := min 1 (min (ε/(8*C ^ 2+2)) (ε/(2*(C+1))))
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ*(8*C ^ 2+2) ≤ ε := by
    exact (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hδQ : δ*(2*(C+1)) ≤ ε := by
    exact (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨s,ε,C,δ,hε,hC,hδ,hδ1,hbounds,fun B H hB hH => ?_⟩
  obtain ⟨P,hP,hpm⟩ := hs B H hB hH
  refine ⟨P,hP,fun B' H' hb hh i => ?_⟩
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hQ : |P.Q i H'-P.Q i H| ≤ C*δ := by
    rw [← map_sub]
    exact ((P.Q i).le_opNorm _).trans (mul_le_mul (hbounds P hP i).2 hh (norm_nonneg _) (by linarith))
  have hq : ε/2 ≤ P.Q i H' := by
    have hlow := neg_abs_le (P.Q i H'-P.Q i H)
    have hbase := (hpm i).1
    have hcd : C*δ ≤ ε/2 := by nlinarith [hδ.le]
    linarith
  have hbc : 4*‖B-B'‖*‖P.ξ i‖^2 ≤ (ε*‖B‖)/2 := by
    rw [norm_sub_rev B B']
    calc
      _ ≤ 4*(δ*‖B‖)*C ^ 2 := by gcongr; exact (hbounds P hP i).1
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hδε hn.le]
  obtain ⟨hl,hgood⟩ := second_form_direction_persists B B' (P.ξ i)
    (mul_pos hε hn) (hpm i).2.le hbc
  have hBn : ‖B'‖ ≤ 2*‖B‖ := by
    have hh := norm_le_insert' B' B
    have hsmall : ‖B'-B‖ ≤ ‖B‖ := hb.trans (mul_le_of_le_one_left hn.le hδ1)
    linarith
  refine ⟨hq,?_,hgood⟩
  have hh := mul_le_mul_of_nonneg_left hBn (by positivity : 0 ≤ ε/4)
  linarith

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates Set






theorem actual_polynomial_cell_phases {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
    (R c A b K Q : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) :
    ∃ (stock : Finset PhaseBasis) (ε C δ z₀ : ℝ),
      0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ 0 < z₀ ∧ z₀ ≤ 1 ∧
      (∀ P ∈ stock, ∀ i, ‖P.ξ i‖ ≤ C ∧ ‖P.Q i‖ ≤ C) ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ →
      ∀ (F : RField 4) (U : Set Base), IsOpen U → Convex ℝ U → ContDiffOn ℝ ∞ F U →
        WeightedBound U z 3 A F →
        (∀ p ∈ U, ‖firstJetPair F p‖ ≤ R ∧
          c ≤ NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2) →
      ∀ (H : Base → PhaseMean.Tensor) (x : Base), x ∈ U → H x ∈ T → b ≤ ‖realSecondTensor F x‖ →
        (∀ y ∈ U, ‖H y-H x‖ ≤ K*‖y-x‖) →
      ∃ P ∈ stock, ∀ (y : Base) (G : RField 4) (H' : PhaseMean.Tensor),
        y ∈ U → ‖y-x‖ ≤ Q*z^6 →
        ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
        ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
        c/2 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
        b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ P.Q i H' ∧
          (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-(P.ξ i).2,(P.ξ i).1)‖ ∧
          ε*b/8 ≤ ‖secondQuadratic (realSecondTensor G y) (-(P.ξ i).2,(P.ξ i).1)‖ ∧
          Good (realSecondTensor G y) (P.ξ i) := by
  obtain ⟨stock,ε,C,d,hε,hC,hd,hd1,hbounds,hstock⟩ :=
    finite_phase_stock_neighborhoods (n := 4) hT hT0 hTd
  obtain ⟨L,hL,hvariation⟩ := second_form_cell_variation R c A hc hA
  obtain ⟨η,D,hη,hD,hperturb⟩ := secondTensor_z4_stability R c A hc hA
  obtain ⟨ηg,hηg,_,hgram⟩ := uniform_gram_neighborhood R c hc
  let E := D+L*Q
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  let z₀ := min 1 (min η (min ηg (min (d*b/(2*(E+1))) (d/(2*(K*Q+1))))))
  have hz₀ : 0 < z₀ := by dsimp [z₀] <;> positivity
  have hz₀1 : z₀ ≤ 1 := min_le_left _ _
  refine ⟨stock,ε,C,d/2,z₀,hε,hC,half_pos hd,hz₀,hz₀1,hbounds,?_⟩
  intro z hz hz0 F U hU hconv hF hFbound hmetric H x hx hHx hBx hH
  have hz1 := hz0.trans hz₀1
  have hzη : z ≤ η := hz0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hzηg : z ≤ ηg := hz0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hze : z ≤ d*b/(2*(E+1)) := hz0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hzh : z ≤ d/(2*(K*Q+1)) := hz0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hz41 : z^4 ≤ z := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hz.le hz1 (by omega : 1 ≤ 4))
  have hz61 : z^6 ≤ z := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hz.le hz1 (by omega : 1 ≤ 6))
  have hz21 : z^2 ≤ z := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hz.le hz1 (by omega : 1 ≤ 2))
  have hEz : E*z^2 ≤ d*b/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(E+1))).mp hze
    nlinarith [mul_le_mul_of_nonneg_left hz21 hE]
  have hHz : K*Q*z^6 ≤ d/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(K*Q+1))).mp hzh
    nlinarith [mul_le_mul_of_nonneg_left hz61 (mul_nonneg hK hQ)]
  have hBn : realSecondTensor F x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hb.trans_le hBx))
  obtain ⟨P,hP,hPb⟩ := hstock (realSecondTensor F x) (H x) hBn hHx
  refine ⟨P,hP,?_⟩
  intro y G H' hy hxy hFG1 hFG2 hH'
  have hnormjet := (coordinate_jets_variation hU hconv hF hz hA hFbound hy hy).2.1
  have hdiff : ‖realSecondTensor G y-realSecondTensor F x‖ ≤ E*z^2 := by
    have hp := hperturb z hz hz1 (hz41.trans hzη) F G y
      (hmetric y hy).1 (hmetric y hy).2 hFG1 hnormjet hFG2
    have hv := hvariation z hz hz1 F U hU hconv hF hFbound hmetric y hy x hx
    calc
      _ ≤ ‖realSecondTensor G y-realSecondTensor F y‖+
          ‖realSecondTensor F y-realSecondTensor F x‖ := by
            simpa only [dist_eq_norm] using dist_triangle (realSecondTensor G y) (realSecondTensor F y) (realSecondTensor F x)
      _ = ‖realSecondTensor F y-realSecondTensor G y‖+
          ‖realSecondTensor F y-realSecondTensor F x‖ := by rw [norm_sub_rev (realSecondTensor G y)]
      _ ≤ D*z^2+(L/z^4)*‖y-x‖ := add_le_add hp hv
      _ ≤ D*z^2+(L/z^4)*(Q*z^6) := by gcongr
      _ = E*z^2 := by dsimp [E]; field_simp [hz.ne']
  have hsmall : ‖realSecondTensor G y-realSecondTensor F x‖ ≤ d*‖realSecondTensor F x‖ := by
    apply hdiff.trans (hEz.trans _)
    nlinarith [mul_le_mul_of_nonneg_left hBx hd.le]
  have hnearH : ‖H'-H x‖ ≤ d := by
    calc
      _ ≤ ‖H'-H y‖+‖H y-H x‖ := by
        simpa only [dist_eq_norm] using dist_triangle H' (H y) (H x)
      _ ≤ d/2+K*‖y-x‖ := add_le_add hH' (hH y hy)
      _ ≤ d/2+K*(Q*z^6) := by gcongr
      _ ≤ d := by nlinarith [hHz]
  have hhalf : b/2 ≤ ‖realSecondTensor G y‖ := by
    have hn := norm_le_insert' (realSecondTensor F x) (realSecondTensor G y)
    rw [norm_sub_rev (realSecondTensor F x)] at hn
    have he : d*b/2 ≤ b/2 := by nlinarith
    linarith [hdiff.trans (hEz.trans he)]
  refine ⟨(hgram _ _ (hmetric y hy).1 (hmetric y hy).2
    (hFG1.trans (hz41.trans hzηg))).2,hhalf,?_⟩
  intro i
  obtain ⟨hq,hl,hgood⟩ := hPb _ H' hsmall hnearH i
  refine ⟨hq,hl,?_,hgood⟩
  have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ ε/4)
  linarith

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates Set



lemma cutoff_distance_to_center {h : ℝ} (hh : 0 < h) (a : PhaseGrid.Index) {p : Base}
    (hp : p ∈ tsupport (PhaseGrid.cutoff h a)) : ‖p-h • PhaseGrid.center a‖ ≤ 3*h := by
  obtain ⟨hp1,hp2⟩ := PhaseGrid.cutoff_tsupport_subset hh a hp
  change max |p.1-h*a.1| |p.2-h*a.2| ≤ 3*h
  exact max_le hp1.le hp2.le






end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AnchoredCellGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase cells anchored at the compact weight support need no enclosing
convex chart on which the immersion remains nondegenerate. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma firstJet_anchor_neighborhood (R c A Q : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hQ : 0 ≤ Q) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
    ∀ z : ℝ, 0 < z → z ≤ η → ∀ F : RField 4, ContDiff ℝ ∞ F →
      WeightedBound univ z 3 A F → ∀ x : Base,
      ‖firstJetPair F x‖ ≤ R → c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 →
      ∀ y : Base, ‖y-x‖ ≤ Q*z^6 →
      ‖firstJetPair F y‖ ≤ R+1 ∧
        c/2 ≤ NormalFrame.gramDet (firstJetPair F y).1 (firstJetPair F y).2 := by
  obtain ⟨ε,hε,hε1,hgram⟩ := uniform_gram_neighborhood R c hc
  let η := min 1 (ε/(A*Q+1))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε (by positivity))
  refine ⟨η,hη,min_le_left _ _,?_⟩
  intro z hz hzη F hF hb x hx hxg y hy
  have hz1 : z ≤ 1 := hzη.trans (min_le_left _ _)
  have hze : z ≤ ε/(A*Q+1) := hzη.trans (min_le_right _ _)
  have hz4 : z^4 ≤ z := by
    calc
      z^4 ≤ z^1 := pow_le_pow_of_le_one hz.le hz1 (by omega)
      _ = z := pow_one z
  have hsmall : A*Q*z^4 ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < A*Q+1)).mp hze
    nlinarith [mul_le_mul_of_nonneg_left hz4 (mul_nonneg hA hQ)]
  have hv := (coordinate_jets_variation isOpen_univ (convex_univ : Convex ℝ (univ : Set Base))
    hF.contDiffOn hz hA hb (mem_univ x) (mem_univ y)).1
  have hclose : ‖firstJetPair F x-firstJetPair F y‖ ≤ ε := by
    calc
      _ ≤ (A/z^2)*‖x-y‖ := hv
      _ = (A/z^2)*‖y-x‖ := by rw [norm_sub_rev x y]
      _ ≤ (A/z^2)*(Q*z^6) := mul_le_mul_of_nonneg_left hy (div_nonneg hA (sq_nonneg z))
      _ = A*Q*z^4 := by field_simp [hz.ne']
      _ ≤ ε := hsmall
  exact hgram _ _ hx hxg hclose

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates

theorem anchored_polynomial_cell_phases {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
    (R c A b K : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ stock : Finset PhaseBasis, ∃ ε C δ z₀ : ℝ,
      0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ 0 < z₀ ∧ z₀ ≤ 1 ∧
      (∀ P ∈ stock, ∀ i, ‖P.ξ i‖ ≤ C ∧ ‖P.Q i‖ ≤ C) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : RField 4, ContDiff ℝ ∞ F →
      WeightedBound univ z 3 A F → ∀ (H : Base → PhaseMean.Tensor) (x : Base),
      ‖firstJetPair F x‖ ≤ R → c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 →
      b ≤ ‖realSecondTensor F x‖ → H x ∈ T →
      (∀ y, ‖H y-H x‖ ≤ K*‖y-x‖) →
      ∃ P ∈ stock, ∀ (y : Base) (G : RField 4) (H' : PhaseMean.Tensor),
        ‖y-x‖ ≤ 6*z^6 →
        ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
        ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
        c/4 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
        b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ P.Q i H' ∧
          (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-(P.ξ i).2,(P.ξ i).1)‖ ∧
          ε*b/8 ≤ ‖secondQuadratic (realSecondTensor G y) (-(P.ξ i).2,(P.ξ i).1)‖ ∧
          Good (realSecondTensor G y) (P.ξ i) := by
  obtain ⟨η,hη,hη1,hanchor⟩ := firstJet_anchor_neighborhood R c A 7 hc hA (by norm_num)
  obtain ⟨stock,ε,C,δ,z₁,hε,hC,hδ,hz₁,hz₁1,hstock,hcell⟩ :=
    actual_polynomial_cell_phases hT hT0 hTd (R+1) (c/2) A b K 6
      (half_pos hc) hA hb hK (by norm_num)
  refine ⟨stock,ε,C,δ,min η z₁,hε,hC,hδ,lt_min hη hz₁,
    (min_le_left _ _).trans hη1,hstock,?_⟩
  intro z hz hz0 F hF hbF H x hx hxg hxB hxH hLip
  let U : Set Base := Metric.ball x (7*z^6)
  have hxU : x ∈ U := Metric.mem_ball_self (by positivity)
  have hmetric (y : Base) (hy : y ∈ U) : ‖firstJetPair F y‖ ≤ R+1 ∧
      c/2 ≤ NormalFrame.gramDet (firstJetPair F y).1 (firstJetPair F y).2 := by
    apply hanchor z hz (hz0.trans (min_le_left _ _)) F hF hbF x hx hxg y
    exact (show ‖y-x‖ < 7*z^6 from by simpa only [U,Metric.mem_ball,dist_eq_norm] using hy).le
  obtain ⟨P,hPs,hp⟩ := hcell z hz (hz0.trans (min_le_right _ _)) F U Metric.isOpen_ball
    (convex_ball _ _) hF.contDiffOn
    (hbF.restrict_open Metric.isOpen_ball) hmetric H x hxU hxH hxB (fun y _ => hLip y)
  refine ⟨P,hPs,?_⟩
  intro y G H' hy h1 h2 hHH
  have hyU : y ∈ U := by
    change dist y x < 7*z^6
    rw [dist_eq_norm]
    exact hy.trans_lt (by nlinarith [pow_pos hz 6])
  have hh := hp y G H' hyU hy h1 h2 hHH
  simpa only [div_div, show (2:ℝ)*2=4 by norm_num] using hh

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AnchoredGridPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Grid phases selected at support anchors, with a fixed finite phase catalog. -/
noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates Set

theorem anchored_polynomial_grid_phases_oai {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
    (R c A b K : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ stock : Finset PhaseBasis, ∃ ε C δ z₀ W κ : ℝ,
      0 < ε ∧ 1 ≤ C ∧ 0 < δ ∧ 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < W ∧ 0 < κ ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ →
      ∀ F : RField 4, ContDiff ℝ ∞ F → WeightedBound univ z 3 A F →
      ∀ H : Base → PhaseMean.Tensor,
        (∀ x y, ‖H y-H x‖ ≤ K*‖y-x‖) →
      ∀ s : Finset PhaseGrid.Index,
        (∀ a ∈ s, ∃ x : Base, ‖x-z^6 • PhaseGrid.center a‖ ≤ 3*z^6 ∧
          ‖firstJetPair F x‖ ≤ R ∧
          c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 ∧
          b ≤ ‖realSecondTensor F x‖ ∧ H x ∈ T) →
      ∃ (P : {a // a ∈ s} → PhaseBasis) (w : {a // a ∈ s} × Fin 3 → ℝ),
        (∀ a, P a ∈ stock) ∧
        (∀ a i, ‖(P a).ξ i‖ ≤ C ∧ ‖(P a).Q i‖ ≤ C) ∧
        (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        (∀ a y G H', y ∈ tsupport (PhaseGrid.cutoff (z^6) a.val) →
          ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
          ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
          c/4 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
          b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ (P a).Q i H' ∧
            (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-((P a).ξ i).2,((P a).ξ i).1)‖ ∧
            Good (realSecondTensor G y) ((P a).ξ i)) ∧
        (∀ a d y G, a ≠ d → y ∈ tsupport (PhaseGrid.cutoff (z^6) a.1.val) →
          y ∈ tsupport (PhaseGrid.cutoff (z^6) d.1.val) →
          ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
          ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 →
          κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
            (-(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).1)‖ ∧
          κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
            (-(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).1)‖ ∧
          Good (realSecondTensor G y) (w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2) ∧
          Good (realSecondTensor G y) (w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2)) := by
  classical
  obtain ⟨stock,ε,C,δ,z₀,hε,hC,hδ,hz₀,hz₀1,hstock,hcell⟩ :=
    anchored_polynomial_cell_phases hT hT0 hTd R c A b K hc hA hb hK
  obtain ⟨d,k,hd,hk,hm⟩ := universal_relative_length_margin (n := 4) (C := C) (by positivity : 0 < ε/4)


  let aa : ℝ := 1+1/d
  let WW : ℝ := aa^(Fintype.card PhaseGrid.Label)
  have haa : 1 ≤ aa := by dsimp [aa] <;> linarith [one_div_pos.mpr hd]
  have haa0 : 0 < aa := zero_lt_one.trans_le haa
  have had : 1 < d*aa := by dsimp [aa]; rw [mul_add,mul_one,mul_one_div_cancel hd.ne']; linarith
  refine ⟨stock,ε,C,δ,z₀,WW,k,hε,hC,hδ,hz₀,hz₀1,pow_pos haa0 _,hk,?_⟩
  intro z hz hzsmall F hF hFbound H hHLip s hanchors
  let I := {a // a ∈ s}
  choose anchor hdist hjet hgram hnormal htarget using
    fun a : I => hanchors a.val a.property
  have hselection (a : I) := hcell z hz hzsmall F hF hFbound H (anchor a)
    (hjet a) (hgram a) (hnormal a) (htarget a) (hHLip (anchor a))
  choose P hPs hP using hselection
  let w (a : I × Fin 3) : ℝ := aa^(PhaseGrid.phaseLabel (a.1.val,a.2)).val
  have hw (a : I × Fin 3) : 1 ≤ w a ∧ w a ≤ WW :=
    ⟨one_le_pow₀ haa,pow_le_pow_right₀ haa (PhaseGrid.phaseLabel (a.1.val,a.2)).isLt.le⟩
  have hpoint (a : I) (y : Base) (G : RField 4) (H' : PhaseMean.Tensor)
      (hy : y ∈ tsupport (PhaseGrid.cutoff (z^6) a.val))
      (h1 : ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4)
      (h2 : ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4) (hh : ‖H'-H y‖ ≤ δ) :=
    hP a y G H' (by
      have hy := cutoff_distance_to_center (pow_pos hz 6) a.val hy
      calc
        ‖y-anchor a‖ ≤ ‖y-z^6 • PhaseGrid.center a.val‖+
            ‖z^6 • PhaseGrid.center a.val-anchor a‖ := by
              simpa only [dist_eq_norm] using dist_triangle y (z^6 • PhaseGrid.center a.val) (anchor a)
        _ = ‖y-z^6 • PhaseGrid.center a.val‖+
            ‖anchor a-z^6 • PhaseGrid.center a.val‖ := by rw [norm_sub_rev (z^6 • PhaseGrid.center a.val)]
        _ ≤ 6*z^6 := by linarith [hdist a]) h1 h2 hh
  refine ⟨P,w,hPs,fun a i => hstock (P a) (hPs a) i,hw,?_,?_⟩
  · intro a y G H' hy h1 h2 hh
    obtain ⟨hg,hB,hi⟩ := hpoint a y G H' hy h1 h2 hh
    exact ⟨hg,hB,fun i => ⟨(hi i).1,(hi i).2.1,(hi i).2.2.2⟩⟩
  · intro a e y G hae hay hey h1 h2
    have haB := hpoint a.1 y G (H y) hay h1 h2 (by simpa using hδ.le)
    have heB := hpoint e.1 y G (H y) hey h1 h2 (by simpa using hδ.le)
    have hBn : realSecondTensor G y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((half_pos hb).trans_le haB.2.1))
    have ordered (a e : I × Fin 3)
        (ha : y ∈ tsupport (PhaseGrid.cutoff (z^6) a.1.val))
        (he : y ∈ tsupport (PhaseGrid.cutoff (z^6) e.1.val))
        (hlt : (PhaseGrid.phaseLabel (a.1.val,a.2)).val < (PhaseGrid.phaseLabel (e.1.val,e.2)).val) :
        k*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
          (-(w a • (P a.1).ξ a.2+w e • (P e.1).ξ e.2).2,(w a • (P a.1).ξ a.2+w e • (P e.1).ξ e.2).1)‖ ∧
        k*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
          (-(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2).2,(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2).1)‖ := by
      have hmargin := ((hpoint e.1 y G (H y) he h1 h2 (by simpa using hδ.le)).2.2 e.2).2.1
      exact power_weight_length_pairs _ _ _ haa had
        (fun t ht => hm _ _ _ hBn (hstock (P e.1) (hPs e.1) e.2).1
          (hstock (P a.1) (hPs a.1) a.2).1 hmargin t ht.le) hlt
    have hne : (a.1.val,a.2) ≠ (e.1.val,e.2) := by
      intro heq
      have hfirst : a.1.val = e.1.val := congrArg (fun p : PhaseGrid.Index × Fin 3 => p.1) heq
      have hsecond : a.2 = e.2 := congrArg (fun p : PhaseGrid.Index × Fin 3 => p.2) heq
      exact hae (Prod.ext (Subtype.ext hfirst) hsecond)
    have hlab := PhaseGrid.distinct_labels_on_intersection (pow_pos hz _) hne hay hey
    have hnv : (PhaseGrid.phaseLabel (a.1.val,a.2)).val ≠ (PhaseGrid.phaseLabel (e.1.val,e.2)).val :=
      fun heq => hlab (Fin.ext heq)
    have hlen :
        k*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
          (-(w a • (P a.1).ξ a.2+w e • (P e.1).ξ e.2).2,(w a • (P a.1).ξ a.2+w e • (P e.1).ξ e.2).1)‖ ∧
        k*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
          (-(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2).2,(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2).1)‖ := by
      rcases lt_or_gt_of_ne hnv with hlt | hgt
      · exact ordered a e hay hey hlt
      · obtain ⟨hp,hm⟩ := ordered e a hey hay hgt
        refine ⟨by simpa only [add_comm] using hp,?_⟩
        have heq : w e • (P e.1).ξ e.2-w a • (P a.1).ξ a.2 = -(w a • (P a.1).ξ a.2-w e • (P e.1).ξ e.2) := by abel
        simpa only [heq,norm_secondQuadratic_rotated_neg] using hm
    have hpos : 0 < k*‖realSecondTensor G y‖ := mul_pos hk (norm_pos_iff.mpr hBn)
    exact ⟨hlen.1,hlen.2,good_of_direction_length_pos _ _ (hpos.trans_le hlen.1),
      good_of_direction_length_pos _ _ (hpos.trans_le hlen.2)⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases_oai := @OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases_oai
