-- Prove2me | solution 1 for OAI.ScalarConductivity.main_nonuniqueness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:15:28.787757+00:00
-- url     : https://prove2.me/submissions/7df4c678-94a7-418f-8be9-f78f0b4f81ff

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C008
import Theorems.Thm_OAI_ScalarConductivity_boundedRootSources_nonempty

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_NestedGeometry
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceSimilarity_dist (σ : ℝ) (x y : R3) :
    dist (sourceSimilarity σ x) (sourceSimilarity σ y)=sourceScale*dist x y := by
  change dist (sourceScale • sourceSwap x+sourceShift σ)
    (sourceScale • sourceSwap y+sourceShift σ)=_
  rw [dist_add_right,dist_smul₀,sourceSwap.dist_map]
  norm_num [sourceScale]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VariationalDN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem exists_variational_DN
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : Submodule ℝ V) [hK : IsClosed (K : Set V)]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hcoer : IsCoercive (((B.comp K.subtypeL).flip.comp K.subtypeL).flip)) :
    ∃ Λ : (V ⧸ K) →L[ℝ] (V ⧸ K) →L[ℝ] ℝ,
    ∀ f : V ⧸ K, ∃ u : V,
      K.mkQ u = f ∧ (∀ h ∈ K, B u h = 0) ∧
      (∀ u', K.mkQ u' = f → (∀ h ∈ K, B u' h = 0) → u' = u) ∧
      ∀ v : V, Λ f (K.mkQ v) = B u v := by
  let R : (V ⧸ K) →L[ℝ] V :=
    K.orthogonal.subtypeL.comp K.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hR (f : V ⧸ K) : K.mkQ (R f) = f := by
    change Submodule.Quotient.mk (K.quotientEquivOrthogonal f).val = f
    rw [← K.quotientEquivOrthogonal_symm_eq_mk]
    exact K.quotientEquivOrthogonal.symm_apply_apply f
  let A : K →L[ℝ] K →L[ℝ] ℝ := ((B.comp K.subtypeL).flip.comp K.subtypeL).flip
  let S : V →L[ℝ] K →L[ℝ] ℝ := (B.flip.comp K.subtypeL).flip
  let W : V →L[ℝ] K :=
    hcoer.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
      ((InnerProductSpace.toDual ℝ K).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp S)
  have hW (v : V) (h : K) : B (W v).val h.val = B v h.val := by
    change A (W v) h = S v h
    rw [← hcoer.continuousLinearEquivOfBilin_apply]
    change inner ℝ (hcoer.continuousLinearEquivOfBilin
      (hcoer.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ K).symm (S v)))) h = _
    rw [hcoer.continuousLinearEquivOfBilin.apply_symm_apply]
    exact congrArg (fun g : K →L[ℝ] ℝ => g h)
      ((InnerProductSpace.toDual ℝ K).apply_symm_apply (S v))
  let E : (V ⧸ K) →L[ℝ] V := R - K.subtypeL.comp (W.comp R)
  have hEtrace (f : V ⧸ K) : K.mkQ (E f) = f := by
    change K.mkQ (R f - (W (R f)).val) = f
    rw [map_sub, hR]
    simp
  have hEharm (f : V ⧸ K) (h : V) (hh : h ∈ K) : B (E f) h = 0 := by
    change B (R f - (W (R f)).val) h = 0
    rw [map_sub, sub_apply, hW (R f) ⟨h, hh⟩, sub_self]
  have huniq (f : V ⧸ K) (u : V) (hu : K.mkQ u = f)
      (huh : ∀ h ∈ K, B u h = 0) : u = E f := by
    have hdmem : u - E f ∈ K := (Submodule.Quotient.eq K).mp (hu.trans (hEtrace f).symm)
    let d : K := ⟨u - E f, hdmem⟩
    have hd : A d d = 0 := by
      change B (u - E f) (u - E f) = 0
      rw [map_sub B u (E f)]
      change B u (u - E f) - B (E f) (u - E f) = 0
      rw [huh _ hdmem, hEharm _ _ hdmem, sub_self]
    obtain ⟨c, hc, hbound⟩ := hcoer
    have hz : ‖d‖ = 0 := by
      have hb := hbound d
      rw [hd] at hb
      by_contra hn
      have hp : 0 < ‖d‖ := (norm_nonneg d).lt_of_ne (Ne.symm hn)
      exact (not_lt_of_ge hb) (mul_pos (mul_pos hc hp) hp)
    have heq : d = 0 := norm_eq_zero.mp hz
    exact sub_eq_zero.mp (congrArg (fun x : K => x.val) heq)
  let Λ : (V ⧸ K) →L[ℝ] (V ⧸ K) →L[ℝ] ℝ := ((B.comp E).flip.comp R).flip
  refine ⟨Λ, fun f => ⟨E f, hEtrace f, hEharm f, fun u hu huh => huniq f u hu huh, ?_⟩⟩
  intro v
  change B (E f) (R (K.mkQ v)) = B (E f) v
  have hmem : v - R (K.mkQ v) ∈ K := (Submodule.Quotient.eq K).mp (hR (K.mkQ v)).symm
  have hh := hEharm f _ hmem
  rw [map_sub] at hh
  exact (sub_eq_zero.mp hh).symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourcePhysicalCoordinates_right {y : Fin 3 → ℝ}
    (ht : sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100)) :
    sourceAngularCollar (sourceCollarTime y) (sourcePhysicalAngles y)=y := by
  obtain ⟨i,j,a,b,ha,hb,he⟩ := sourceCollarPiece_cover_extended
    (sourceRadial_pos_of_time ht.1) (by linarith [ht.2])
  have he' : sourceAngularCollar (sourceCollarTime y)
      (torusAngles (sourceFaceAngles i j ![sourceCollarTime y,a,b]))=y :=
    (sourceFaceAngles_physical i j ha hb).trans he
  have hinv := sourcePhysicalAngles_angular ht
    (torusAngles (sourceFaceAngles i j ![sourceCollarTime y,a,b]))
  rw [he'] at hinv
  rw [hinv]
  exact he'

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_BoundedMultiplier
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem boundedMultiplier_apply_ae {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) (f : Lp E 2 μ) :
    (boundedMultiplier μ a ha C hC haC f : α → E) =ᵐ[μ] fun x => a x • f x := by
  change (((boundedMultiplier_memLp μ a ha C haC f).toLp _) : α → E) =ᵐ[μ] _
  exact MemLp.coeFn_toLp _

theorem energyForm_apply (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂ballMeasure, |a x| ≤ C) (u v : H1) :
    energyForm a ha C hC haC u v = energy a u v := by
  change inner ℝ (boundedMultiplier ballMeasure a ha C hC haC (weakGradientL u))
    (weakGradientL v) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_apply_ae ballMeasure a ha C hC haC (weakGradientL u),
    weakGradientL_apply_ae u, weakGradientL_apply_ae v] with x hx hu hv
  rw [hx, hu, hv, real_inner_smul_left]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixFiniteLaminate
attribute [-instance] _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
namespace ScalarConductivity

open Set Filter Topology

lemma jetValue_smoothJet (f : R3 → ℝ) (x : R3) : jetValue (smoothJet f x) = f x := rfl
lemma jetGradient_smoothJet (f : R3 → ℝ) (x : R3) :
    jetGradient (smoothJet f x) = gradient f x := rfl

lemma jetFiber_decomposition (z : JetFiber) :
    z = jetLiftValue (jetValue z) + jetLiftGradient (jetGradient z) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · change z 0 = z 0 + 0; simp
  · change z i.succ = 0 + z i.succ; simp

lemma compactSmoothJets_add {z w : JetSpace} (hz : z ∈ compactSmoothJets)
    (hw : w ∈ compactSmoothJets) : z + w ∈ compactSmoothJets := by
  obtain ⟨f, hf, hfc, hfs, hfm, rfl⟩ := hz
  obtain ⟨g, hg, hgc, hgs, hgm, rfl⟩ := hw
  have hj := smoothJet_add (hf.differentiable (by simp)) (hg.differentiable (by simp))
  have hm : MemLp (smoothJet (f + g)) 2 ballMeasure := by rw [hj]; exact hfm.add hgm
  refine ⟨f + g, hf.add hg, hfc.add hgc,
    (tsupport_add f g).trans (union_subset hfs hgs), hm, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (hfm.toLp _) (hgm.toLp _), hfm.coeFn_toLp,
    hgm.coeFn_toLp, hm.coeFn_toLp] with x hsum hfx hgx hfgx
  rw [hsum, hfgx, hj]
  simp only [Pi.add_apply, hfx, hgx]

lemma compactSmoothJets_smul (c : ℝ) {z : JetSpace} (hz : z ∈ compactSmoothJets) :
    c • z ∈ compactSmoothJets := by
  obtain ⟨f, hf, hfc, hfs, hfm, rfl⟩ := hz
  have hj := smoothJet_smul c (hf.differentiable (by simp))
  have hm : MemLp (smoothJet (c • f)) 2 ballMeasure := by rw [hj]; exact hfm.const_smul c
  refine ⟨c • f, hf.const_smul c, hfc.smul_left,
    (tsupport_smul_subset_right (fun _ : R3 => c) f).trans hfs, hm, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (hfm.toLp _), hfm.coeFn_toLp,
    hm.coeFn_toLp] with x hc hfx hcx
  rw [hc, hcx, hj]
  simp only [Pi.smul_apply, hfx]

lemma span_compactSmoothJets : (Submodule.span ℝ compactSmoothJets : Set JetSpace) =
    compactSmoothJets := by
  let K : Submodule ℝ JetSpace := {
    carrier := compactSmoothJets
    zero_mem' := compactSmoothJets_zero
    add_mem' := compactSmoothJets_add
    smul_mem' := compactSmoothJets_smul }
  exact congrArg SetLike.coe (Submodule.span_eq K)

lemma ballPoincareConstant_nonneg : 0 ≤ ballPoincareConstant := by
  exact_mod_cast (eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure R3) ball 2 2).coe_nonneg

lemma norm_gradient_eq_norm_fderiv (f : R3 → ℝ) (x : R3) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ R3).symm.norm_map _

lemma compact_smooth_poincare {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ ball) :
    (eLpNorm f 2 ballMeasure).toReal ≤
      ballPoincareConstant * (eLpNorm (gradient f) 2 ballMeasure).toReal := by
  have hfm : MemLp (fderiv ℝ f) 2 (volume : Measure R3) :=
    (hf.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hfc.fderiv ℝ)
  have he := eLpNorm_le_eLpNorm_fderiv (volume : Measure R3)
    (hf.of_le (by simp) : ContDiff ℝ 1 f) ((subset_tsupport f).trans hfs)
    (p := 2) (by norm_num)
    (by norm_num [R3, finrank_euclideanSpace]) (Metric.isBounded_ball (x := (0 : R3)) (r := 3))
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfm.eLpNorm_ne_top) he
  have hgc : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ R3).symm.continuous.comp (hf.continuous_fderiv (by simp))
  have hg : eLpNorm (gradient f) 2 ballMeasure = eLpNorm (fderiv ℝ f) 2 ballMeasure :=
    eLpNorm_congr_norm_ae
      (Filter.Eventually.of_forall (norm_gradient_eq_norm_fderiv f))
  rw [hg]
  change (eLpNorm f 2 (volume.restrict ball)).toReal ≤
    ballPoincareConstant * (eLpNorm (fderiv ℝ f) 2 (volume.restrict ball)).toReal
  rw [eLpNorm_restrict_eq_of_support_subset
      ((subset_tsupport f).trans hfs),
    eLpNorm_restrict_eq_of_support_subset (f := fderiv ℝ f) (p := 2) (μ := volume)
      ((support_fderiv_subset ℝ).trans hfs)]
  simpa [ENNReal.toReal_mul, ballPoincareConstant] using ht

lemma jetValue_compLp_smooth {f : R3 → ℝ} (hf : MemLp (smoothJet f) 2 ballMeasure) :
    (jetValue.compLp (hf.toLp _) : R3 → ℝ) =ᵐ[ballMeasure] f := by
  filter_upwards [jetValue.coeFn_compLp (hf.toLp _), hf.coeFn_toLp] with x hx hfx
  rw [hx, hfx, jetValue_smoothJet]

lemma jetGradient_compLp_smooth {f : R3 → ℝ} (hf : MemLp (smoothJet f) 2 ballMeasure) :
    (jetGradient.compLp (hf.toLp _) : R3 → R3) =ᵐ[ballMeasure] gradient f := by
  filter_upwards [jetGradient.coeFn_compLp (hf.toLp _), hf.coeFn_toLp] with x hx hfx
  rw [hx, hfx, jetGradient_smoothJet]

lemma compactSmoothJets_poincare {z : JetSpace} (hz : z ∈ compactSmoothJets) :
    ‖jetValue.compLp z‖ ≤ ballPoincareConstant * ‖jetGradient.compLp z‖ := by
  obtain ⟨f, hf, hfc, hfs, hfm, rfl⟩ := hz
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (jetValue_compLp_smooth hfm),
    eLpNorm_congr_ae (jetGradient_compLp_smooth hfm)]
  exact compact_smooth_poincare hf hfc hfs

lemma zeroTraceAmbient_poincare {z : JetSpace} (hz : z ∈ zeroTraceAmbient) :
    ‖jetValue.compLp z‖ ≤ ballPoincareConstant * ‖jetGradient.compLp z‖ := by
  have hc : IsClosed {z : JetSpace | ‖jetValue.compLp z‖ ≤
      ballPoincareConstant * ‖jetGradient.compLp z‖} :=
    isClosed_le ((jetValue.compLpL 2 ballMeasure).continuous.norm)
      (continuous_const.mul ((jetGradient.compLpL 2 ballMeasure).continuous.norm))
  apply closure_minimal (s := compactSmoothJets) (fun _ hz => compactSmoothJets_poincare hz) hc
  change z ∈ closure (Submodule.span ℝ compactSmoothJets : Set JetSpace) at hz
  rwa [span_compactSmoothJets] at hz

lemma jetSpace_decomposition (z : JetSpace) :
    z = jetLiftValue.compLp (jetValue.compLp z) +
      jetLiftGradient.compLp (jetGradient.compLp z) := by
  apply Lp.ext
  filter_upwards [jetLiftValue.coeFn_compLp (jetValue.compLp z),
    jetLiftGradient.coeFn_compLp (jetGradient.compLp z),
    jetValue.coeFn_compLp z, jetGradient.coeFn_compLp z,
    Lp.coeFn_add (jetLiftValue.compLp (jetValue.compLp z))
      (jetLiftGradient.compLp (jetGradient.compLp z))] with x hv hg hvx hgx ha
  rw [ha, Pi.add_apply, hv, hg, hvx, hgx]
  exact jetFiber_decomposition (z x)

lemma h10PoincareConstant_pos : 0 < h10PoincareConstant := by
  have hp := ballPoincareConstant_nonneg
  unfold h10PoincareConstant
  positivity

lemma zeroTraceAmbient_norm_le {z : JetSpace} (hz : z ∈ zeroTraceAmbient) :
    ‖z‖ ≤ h10PoincareConstant * ‖jetGradient.compLp z‖ := by
  calc
    ‖z‖ ≤ ‖jetLiftValue.compLp (jetValue.compLp z)‖ +
        ‖jetLiftGradient.compLp (jetGradient.compLp z)‖ := by
      conv_lhs => rw [jetSpace_decomposition z]
      exact norm_add_le _ _
    _ ≤ ‖jetLiftValue.compLpL 2 ballMeasure‖ * ‖jetValue.compLp z‖ +
        ‖jetLiftGradient.compLpL 2 ballMeasure‖ * ‖jetGradient.compLp z‖ :=
      add_le_add ((jetLiftValue.compLpL 2 ballMeasure).le_opNorm _)
        ((jetLiftGradient.compLpL 2 ballMeasure).le_opNorm _)
    _ ≤ ‖jetLiftValue.compLpL 2 ballMeasure‖ *
        (ballPoincareConstant * ‖jetGradient.compLp z‖) +
        ‖jetLiftGradient.compLpL 2 ballMeasure‖ * ‖jetGradient.compLp z‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (zeroTraceAmbient_poincare hz)
        (norm_nonneg _)) le_rfl
    _ ≤ h10PoincareConstant * ‖jetGradient.compLp z‖ := by
      dsimp [h10PoincareConstant]
      nlinarith [norm_nonneg (jetGradient.compLp z)]

lemma H10_norm_le_weakGradientL (u : H10) :
    ‖u‖ ≤ h10PoincareConstant * ‖weakGradientL u.val‖ :=
  zeroTraceAmbient_norm_le u.property

lemma boundedMultiplier_inner_lower {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure α) (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C)
    (c : ℝ) (hac : ∀ᵐ x ∂μ, c ≤ a x) (u : Lp E 2 μ) :
    c * ‖u‖ ^ 2 ≤ inner ℝ (boundedMultiplier μ a ha C hC haC u) u := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner u u).const_mul c)
    (L2.integrable_inner _ _)
  filter_upwards [boundedMultiplier_apply_ae μ a ha C hC haC u, hac] with x hx hcx
  rw [hx, real_inner_smul_left]
  exact mul_le_mul_of_nonneg_right hcx (real_inner_self_nonneg)

lemma energyForm_coercive_lower (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂ballMeasure, |a x| ≤ C)
    (c : ℝ) (hc : 0 < c) (hac : ∀ᵐ x ∂ballMeasure, c ≤ a x)
    (u : H10) :
    c / h10PoincareConstant ^ 2 * ‖u‖ * ‖u‖ ≤ energyForm a ha C hC haC u.val u.val := by
  have hnorm := H10_norm_le_weakGradientL u
  have hsq := mul_self_le_mul_self (norm_nonneg u) hnorm
  have hlo := boundedMultiplier_inner_lower ballMeasure a ha C hC haC c hac
    (weakGradientL u.val)
  change c / h10PoincareConstant ^ 2 * ‖u‖ * ‖u‖ ≤
    inner ℝ (boundedMultiplier ballMeasure a ha C hC haC (weakGradientL u.val))
      (weakGradientL u.val)
  calc
    _ = c * (‖u‖ ^ 2 / h10PoincareConstant ^ 2) := by ring
    _ ≤ c * ‖weakGradientL u.val‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      apply (div_le_iff₀ (sq_pos_of_pos h10PoincareConstant_pos)).2
      nlinarith [hsq]
    _ ≤ _ := hlo

theorem exists_DirichletToNeumann (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂ballMeasure, |a x| ≤ C)
    (c : ℝ) (hc : 0 < c) (hac : ∀ᵐ x ∂ballMeasure, c ≤ a x) :
    ∃ Λ : DNOperator, IsDirichletToNeumann a Λ := by
  obtain ⟨Λ, hΛ⟩ := exists_variational_DN H10 (energyForm a ha C hC haC)
    ⟨c / h10PoincareConstant ^ 2, div_pos hc (sq_pos_of_pos h10PoincareConstant_pos),
      energyForm_coercive_lower a ha C hC haC c hc hac⟩
  refine ⟨Λ, ?_⟩
  intro f
  obtain ⟨u, hu, hh, huniq, hident⟩ := hΛ f
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · intro h hhmem
    rw [← energyForm_apply a ha C hC haC]
    exact hh h hhmem
  · intro u' hu' hhu'
    apply huniq u' hu'
    intro h hhmem
    rw [energyForm_apply a ha C hC haC]
    exact hhu' h hhmem
  · intro v
    rw [← energyForm_apply a ha C hC haC]
    exact hident v

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_NonlinearLp
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma zeroTraceAmbient_eq_closure : (zeroTraceAmbient : Set JetSpace)=closure compactSmoothJets := by
  change closure (Submodule.span ℝ compactSmoothJets : Set JetSpace)=closure compactSmoothJets
  rw [span_compactSmoothJets]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevChain
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {g dg : ℝ → ℝ} (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hdg : Continuous dg)
  (hderiv : ∀ r, HasDerivAt g (dg r) r) {C : ℝ} (hC : 0≤C)
  (hgb : ∀ r, ‖g r‖≤C*‖r‖) (hdgb : ∀ r, ‖dg r‖≤C)

include hderiv

lemma sobolevChainLp_preserves_H10 (hg0 : g 0=0) {z : JetSpace} (hz : z∈zeroTraceAmbient) :
    sobolevChainLp hg hdg hC hgb hdgb z ∈ zeroTraceAmbient := by
  change z ∈ (zeroTraceAmbient : Set JetSpace) at hz
  change _ ∈ (zeroTraceAmbient : Set JetSpace)
  rw [zeroTraceAmbient_eq_closure] at hz ⊢
  apply nonlinear_closure_preservation (sobolevChainLp_continuous hg hdg hC hgb hdgb) _ hz
  rintro w ⟨f,hf,hfc,hfs,hm,rfl⟩
  obtain ⟨hgm,he⟩ := sobolevChainLp_smooth hg hdg hderiv hC hgb hdgb hf hm
  refine ⟨g ∘ f,hg.comp hf,hfc.comp_left hg0,?_,hgm,he⟩
  exact (closure_mono (Function.support_comp_subset hg0 f)).trans hfs

lemma sobolevChain_value (u : H1) :
    (fun x => jetValue ((sobolevChain hg hdg hderiv hC hgb hdgb u).val x)) =ᵐ[ballMeasure]
      fun x => g (jetValue (u.val x)) := by
  filter_upwards [sobolevChainLp_coe_ae hg hdg hC hgb hdgb u.val] with x hx
  change jetValue (sobolevChainLp hg hdg hC hgb hdgb u.val x) = _
  rw [hx]
  change g (jetValue (u.val x))+0=g (jetValue (u.val x))
  simp

lemma sobolevChain_gradient (u : H1) :
    weakGradient (sobolevChain hg hdg hderiv hC hgb hdgb u) =ᵐ[ballMeasure]
      fun x => dg (jetValue (u.val x)) • weakGradient u x := by
  filter_upwards [sobolevChainLp_coe_ae hg hdg hC hgb hdgb u.val] with x hx
  change jetGradient (sobolevChainLp hg hdg hC hgb hdgb u.val x)=_
  rw [hx]
  ext i
  change 0+(dg (jetValue (u.val x)) • weakGradient u x) i=_
  simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothOperations
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

namespace SmoothLipZero

lemma onLp_continuous (F : SmoothLipZero) : Continuous F.onLp :=
  sobolevChainLp_continuous _ _ _ _ _

lemma onLp_ae (F : SmoothLipZero) (z : JetSpace) :
    F.onLp z =ᵐ[ballMeasure] fun x => jetSuperposition F (deriv F) (z x) :=
  sobolevChainLp_coe_ae _ _ _ _ _ _

lemma preserves_H10 (F : SmoothLipZero) {z : JetSpace} (hz : z∈zeroTraceAmbient) :
    F.onLp z∈zeroTraceAmbient :=
  sobolevChainLp_preserves_H10 _ _ F.derivative _ _ _ F.at_zero hz

lemma onH1_continuous (F : SmoothLipZero) : Continuous F.onH1 :=
  (F.onLp_continuous.comp continuous_subtype_val).subtype_mk _

lemma onH1_value (F : SmoothLipZero) (u : H1) :
    (fun x => jetValue ((F.onH1 u).val x)) =ᵐ[ballMeasure] fun x => F (jetValue (u.val x)) :=
  sobolevChain_value _ _ F.derivative _ _ _ _

lemma onH1_gradient (F : SmoothLipZero) (u : H1) :
    weakGradient (F.onH1 u) =ᵐ[ballMeasure] fun x => deriv F (jetValue (u.val x)) • weakGradient u x :=
  sobolevChain_gradient _ _ F.derivative _ _ _ _

end SmoothLipZero

lemma clippedValue_eventually {M r : ℝ} (hr : |r|≤M) : clippedValue M =ᶠ[𝓝 r] id := by
  have hb : r ∈ Metric.ball 0 (valueBump M).rIn := by
    change dist r 0 < |M|+1
    rw [dist_zero_right,Real.norm_eq_abs]
    linarith [le_abs_self M]
  filter_upwards [(valueBump M).eventuallyEq_one_of_mem_ball hb] with s hs
  simp only [clippedValue,hs,Pi.one_apply,one_mul,id_eq]

lemma clippedValue_eq {M r : ℝ} (hr : |r|≤M) : clippedValue M r=r :=
  (clippedValue_eventually hr).eq_of_nhds

lemma clippedValue_deriv {M r : ℝ} (hr : |r|≤M) : deriv (clippedValue M) r=1 := by
  rw [(clippedValue_eventually hr).deriv_eq]
  exact deriv_id r

lemma exists_clippedValue_bound (M : ℝ) : ∃ C : ℝ, 0<C ∧ ∀ r, |clippedValue M r|≤C := by
  obtain ⟨C,hC⟩ := (clippedValue_compact M).exists_bound_of_continuous (clippedValue_smooth M).continuous
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),fun r => ?_⟩
  exact (show |clippedValue M r|≤C from hC r).trans (le_max_right _ _)

lemma squaredValue_eventually {M r : ℝ} (hr : |r|≤M) :
    squaredValue M =ᶠ[𝓝 r] fun s => s^2 := by
  have hb : r ∈ Metric.ball 0 (valueBump M).rIn := by
    change dist r 0 < |M|+1
    rw [dist_zero_right,Real.norm_eq_abs]
    linarith [le_abs_self M]
  filter_upwards [(valueBump M).eventuallyEq_one_of_mem_ball hb] with s hs
  simp only [squaredValue,hs,Pi.one_apply,one_mul]

lemma squaredValue_eq {M r : ℝ} (hr : |r|≤M) : squaredValue M r=r^2 :=
  (squaredValue_eventually hr).eq_of_nhds

lemma squaredValue_deriv {M r : ℝ} (hr : |r|≤M) : deriv (squaredValue M) r=2*r := by
  rw [(squaredValue_eventually hr).deriv_eq]
  simp

lemma jet_squareOperation {M : ℝ} {z : JetFiber} (hz : |jetValue z|≤M) :
    jetSuperposition (squareOperation M) (deriv (squareOperation M)) z =
      jetLiftValue (jetValue z ^ 2) + jetLiftGradient ((2*jetValue z) • jetGradient z) := by
  change jetLiftValue (squaredValue M (jetValue z)) +
    jetLiftGradient (deriv (squaredValue M) (jetValue z) • jetGradient z)=_
  rw [squaredValue_eq hz,squaredValue_deriv hz]

lemma gradient_product {f g : R3 → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : R3) :
    gradient (f*g) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_mul (hf x) (hg x)]
  simp

lemma smoothJet_product {f g : R3 → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : R3) :
    smoothJet (f*g) x=jetProduct (smoothJet f x) (smoothJet g x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change f x*g x=f x*g x+0; simp
  · change gradient (f*g) x j=0+(f x • gradient g x+g x • gradient f x) j
    rw [gradient_product hf hg]; simp

lemma square_polarization {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    {z w : JetFiber} (hz : |jetValue z|≤A) (hw : |jetValue w|≤B) :
    (1/2:ℝ) • (jetSuperposition (squareOperation (A+B)) (deriv (squareOperation (A+B))) (z+w) -
      jetSuperposition (squareOperation (A+B)) (deriv (squareOperation (A+B))) z -
      jetSuperposition (squareOperation (A+B)) (deriv (squareOperation (A+B))) w) =
    jetProduct z w := by
  have hzw : |jetValue (z+w)|≤A+B := by
    rw [map_add]; exact (abs_add_le _ _).trans (add_le_add hz hw)
  rw [jet_squareOperation hzw,jet_squareOperation (hz.trans (le_add_of_nonneg_right hB)),
    jet_squareOperation (hw.trans (le_add_of_nonneg_left hA))]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (1/2:ℝ)*(((jetValue z+jetValue w)^2+0)-(jetValue z^2+0)-(jetValue w^2+0))=
      jetValue z*jetValue w+0
    ring
  · change (1/2:ℝ)*((0+(2*(jetValue z+jetValue w))*((jetGradient z) j+(jetGradient w) j))-
      (0+(2*jetValue z)*(jetGradient z) j)-(0+(2*jetValue w)*(jetGradient w) j))=
      0+((jetValue z)*(jetGradient w) j+(jetValue w)*(jetGradient z) j)
    ring

variable (F G : SmoothLipZero) (A B : ℝ)

lemma clippedProductLp_continuous : Continuous (fun p : JetSpace × JetSpace =>
    clippedProductLp F G A B p.1 p.2) := by
  exact (((squareOperation (A+B)).onLp_continuous.comp
    ((F.onLp_continuous.comp continuous_fst).add (G.onLp_continuous.comp continuous_snd))).sub
    ((squareOperation (A+B)).onLp_continuous.comp (F.onLp_continuous.comp continuous_fst)) |>.sub
    ((squareOperation (A+B)).onLp_continuous.comp (G.onLp_continuous.comp continuous_snd))).const_smul (1/2:ℝ)

lemma clippedProductLp_preserves_H1 {z w : JetSpace} (hz : z∈H1Space) (hw : w∈H1Space) :
    clippedProductLp F G A B z w∈H1Space := by
  apply H1Space.smul_mem
  apply H1Space.sub_mem
  · apply H1Space.sub_mem
    · exact (squareOperation (A+B)).preserves_H1
        (H1Space.add_mem (F.preserves_H1 hz) (G.preserves_H1 hw))
    · exact (squareOperation (A+B)).preserves_H1 (F.preserves_H1 hz)
  · exact (squareOperation (A+B)).preserves_H1 (G.preserves_H1 hw)

variable (hA : 0≤A) (hB : 0≤B) (hF : ∀ r, |F r|≤A) (hG : ∀ r, |G r|≤B)
include hA hB hF hG

lemma clippedProductLp_ae (z w : JetSpace) :
    clippedProductLp F G A B z w =ᵐ[ballMeasure] fun x =>
      jetProduct (jetSuperposition F (deriv F) (z x)) (jetSuperposition G (deriv G) (w x)) := by
  let S := squareOperation (A+B)
  filter_upwards [Lp.coeFn_smul (1/2:ℝ) (S.onLp (F.onLp z+G.onLp w)-S.onLp (F.onLp z)-S.onLp (G.onLp w)),
    Lp.coeFn_sub (S.onLp (F.onLp z+G.onLp w)-S.onLp (F.onLp z)) (S.onLp (G.onLp w)),
    Lp.coeFn_sub (S.onLp (F.onLp z+G.onLp w)) (S.onLp (F.onLp z)),
    S.onLp_ae (F.onLp z+G.onLp w),S.onLp_ae (F.onLp z),S.onLp_ae (G.onLp w),
    Lp.coeFn_add (F.onLp z) (G.onLp w),F.onLp_ae z,G.onLp_ae w] with x hs hsub hsub' hsum h1 h2 ha hf hg
  change ((1/2:ℝ) • (S.onLp (F.onLp z+G.onLp w)-S.onLp (F.onLp z)-S.onLp (G.onLp w))) x=_
  rw [hs,Pi.smul_apply,hsub,Pi.sub_apply,hsub',Pi.sub_apply,hsum,h1,h2,ha,Pi.add_apply,hf,hg]
  apply square_polarization hA hB
  · change |F (jetValue (z x))+0|≤A; simpa using hF (jetValue (z x))
  · change |G (jetValue (w x))+0|≤B; simpa using hG (jetValue (w x))

lemma clippedProductLp_smooth {f g : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hfm : MemLp (smoothJet f) 2 ballMeasure) (hgm : MemLp (smoothJet g) 2 ballMeasure) :
    ∃ hm : MemLp (smoothJet ((F ∘ f)*(G ∘ g))) 2 ballMeasure,
      clippedProductLp F G A B (hfm.toLp _) (hgm.toLp _) = hm.toLp _ := by
  have he : clippedProductLp F G A B (hfm.toLp _) (hgm.toLp _) =ᵐ[ballMeasure]
      smoothJet ((F ∘ f)*(G ∘ g)) := by
    filter_upwards [clippedProductLp_ae F G A B hA hB hF hG (hfm.toLp _) (hgm.toLp _),
      hfm.coeFn_toLp,hgm.coeFn_toLp] with x hx hy hz
    rw [hx,hy,hz,←smoothJet_comp F.derivative (hf.differentiable (by simp)),
      ←smoothJet_comp G.derivative (hg.differentiable (by simp)),
      ←smoothJet_product ((F.smooth.comp hf).differentiable (by simp))
        ((G.smooth.comp hg).differentiable (by simp))]
  have hm := MemLp.ae_eq he (Lp.memLp (clippedProductLp F G A B (hfm.toLp _) (hgm.toLp _)))
  exact ⟨hm,Lp.ext (he.trans hm.coeFn_toLp.symm)⟩

lemma clippedProductLp_smooth_compact {z w : JetSpace} (hz : z∈smoothJets) (hw : w∈compactSmoothJets) :
    clippedProductLp F G A B z w∈compactSmoothJets := by
  obtain ⟨f,hf,hfm,rfl⟩ := hz
  obtain ⟨g,hg,hgc,hgs,hgm,rfl⟩ := hw
  obtain ⟨hm,he⟩ := clippedProductLp_smooth F G A B hA hB hF hG hf hg hfm hgm
  refine ⟨(F ∘ f)*(G ∘ g),(F.smooth.comp hf).mul (G.smooth.comp hg),
    (hgc.comp_left G.at_zero).mul_left,?_,hm,he⟩
  exact (closure_mono (Function.support_mul_subset_right _ _)).trans
    ((closure_mono (Function.support_comp_subset G.at_zero g)).trans hgs)

lemma clippedProductLp_preserves_H10 {z w : JetSpace} (hz : z∈H1Space) (hw : w∈zeroTraceAmbient) :
    clippedProductLp F G A B z w∈zeroTraceAmbient := by
  have hc := clippedProductLp_continuous F G A B
  have hb {z : JetSpace} (hz : z∈smoothJets) {w : JetSpace} (hw : w∈closure compactSmoothJets) :
      clippedProductLp F G A B z w∈closure compactSmoothJets := by
    apply (image_closure_subset_closure_image (hc.comp (continuous_const.prodMk continuous_id))).trans
      (closure_mono (show (fun w => clippedProductLp F G A B z w) '' compactSmoothJets ⊆ compactSmoothJets from ?_))
      ⟨w,hw,rfl⟩
    rintro _ ⟨w,hw,rfl⟩
    exact clippedProductLp_smooth_compact F G A B hA hB hF hG hz hw
  change z∈(H1Space : Set JetSpace) at hz
  change w∈(zeroTraceAmbient : Set JetSpace) at hw
  change _∈(zeroTraceAmbient : Set JetSpace)
  rw [H1Space_eq_closure] at hz
  rw [zeroTraceAmbient_eq_closure] at hw ⊢
  have ht : (fun z => clippedProductLp F G A B z w) '' smoothJets ⊆ closure compactSmoothJets := by
    rintro _ ⟨z,hz,rfl⟩; exact hb hz hw
  have hh := (image_closure_subset_closure_image (hc.comp (continuous_id.prodMk continuous_const))).trans
    (closure_mono ht)
  simpa only [closure_closure,Function.comp_apply,id_eq] using hh ⟨z,hz,rfl⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevTraceChain
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma continuous_binary_closure {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {T : X → Y → Z} (hT : Continuous (fun p : X × Y => T p.1 p.2))
    {S : Set X} {U : Set Y} {V : Set Z} (h : ∀ x∈S, ∀ y∈U, T x y∈V)
    {x : X} (hx : x∈closure S) {y : Y} (hy : y∈closure U) : T x y∈closure V := by
  have hb {x : X} (hx : x∈S) : T x y∈closure V := by
    have ht : (fun y => T x y) '' U ⊆ V := by
      rintro _ ⟨y,hy,rfl⟩; exact h x hx y hy
    exact (image_closure_subset_closure_image (hT.comp (continuous_const.prodMk continuous_id))).trans
      (closure_mono ht) ⟨y,hy,rfl⟩
  have ht : (fun x => T x y) '' S ⊆ closure V := by
    rintro _ ⟨x,hx,rfl⟩; exact hb hx
  have hh := (image_closure_subset_closure_image (hT.comp (continuous_id.prodMk continuous_const))).trans
    (closure_mono ht)
  simpa only [closure_closure,Function.comp_apply,id_eq] using hh ⟨x,hx,rfl⟩

lemma smoothJet_sub {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    smoothJet (f-g)=smoothJet f-smoothJet g := by
  ext x i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [smoothJet,gradient,fderiv_sub (hf x) (hg x)]

lemma chainDifference_smooth_compact (F : SmoothLipZero) {z w : JetSpace}
    (hz : z∈smoothJets) (hw : w∈compactSmoothJets) :
    F.onLp (z+w)-F.onLp z ∈ compactSmoothJets := by
  obtain ⟨f,hf,hfm,rfl⟩ := hz
  obtain ⟨g,hg,hgc,hgs,hgm,rfl⟩ := hw
  let d : R3 → ℝ := F ∘ (f+g)-F ∘ f
  have hd : ContDiff ℝ (↑(⊤ : ℕ∞)) d := (F.smooth.comp (hf.add hg)).sub (F.smooth.comp hf)
  have hs : Function.support d ⊆ Function.support g := by
    intro x hx
    contrapose! hx
    simp only [Function.mem_support,not_not] at hx ⊢
    simp [d,hx]
  have hdc : HasCompactSupport d := hgc.of_isClosed_subset isClosed_closure (closure_mono hs)
  have hdm : tsupport d ⊆ ball := (closure_mono hs).trans hgs
  have he : F.onLp (hfm.toLp _+hgm.toLp _)-F.onLp (hfm.toLp _) =ᵐ[ballMeasure] smoothJet d := by
    filter_upwards [Lp.coeFn_sub (F.onLp (hfm.toLp _+hgm.toLp _)) (F.onLp (hfm.toLp _)),
      F.onLp_ae (hfm.toLp _+hgm.toLp _),F.onLp_ae (hfm.toLp _),
      Lp.coeFn_add (hfm.toLp _) (hgm.toLp _),hfm.coeFn_toLp,hgm.coeFn_toLp] with x hs h1 h2 ha hf' hg'
    rw [hs,Pi.sub_apply,h1,h2,ha,Pi.add_apply,hf',hg']
    have haJet := congrFun (smoothJet_add (hf.differentiable (by simp))
      (hg.differentiable (by simp))) x
    simp only [Pi.add_apply] at haJet
    rw [←haJet]
    rw [←smoothJet_comp (f := f+g) F.derivative ((hf.add hg).differentiable (by simp)) x,
      ←smoothJet_comp (f := f) F.derivative (hf.differentiable (by simp)) x]
    exact (congrFun (smoothJet_sub ((F.smooth.comp (hf.add hg)).differentiable (by simp))
      ((F.smooth.comp hf).differentiable (by simp))) x).symm
  have hm := MemLp.ae_eq he (Lp.memLp (F.onLp (hfm.toLp _+hgm.toLp _)-F.onLp (hfm.toLp _)))
  exact ⟨d,hd,hdc,hdm,hm,Lp.ext (he.trans hm.coeFn_toLp.symm)⟩

lemma chainDifference_H10 (F : SmoothLipZero) {z w : JetSpace}
    (hz : z∈H1Space) (hw : w∈zeroTraceAmbient) :
    F.onLp (z+w)-F.onLp z ∈ zeroTraceAmbient := by
  change z∈(H1Space : Set JetSpace) at hz
  change w∈(zeroTraceAmbient : Set JetSpace) at hw
  change _∈(zeroTraceAmbient : Set JetSpace)
  rw [H1Space_eq_closure] at hz
  rw [zeroTraceAmbient_eq_closure] at hw ⊢
  exact continuous_binary_closure
    ((F.onLp_continuous.comp (continuous_fst.add continuous_snd)).sub
      (F.onLp_continuous.comp continuous_fst))
    (fun _ hz _ hw => chainDifference_smooth_compact F hz hw) hz hw

lemma chain_trace_eq (F : SmoothLipZero) {u v : H1} (h : trace u=trace v) :
    trace (F.onH1 u)=trace (F.onH1 v) := by
  have hw : u-v∈H10 := (Submodule.Quotient.eq H10).mp h
  apply (Submodule.Quotient.eq H10).mpr
  change F.onLp u.val-F.onLp v.val∈zeroTraceAmbient
  have hh := chainDifference_H10 F v.property (show u.val-v.val∈zeroTraceAmbient from hw)
  simpa only [add_sub_cancel] using hh

lemma jet_clipped_of_bound {M : ℝ} {z : JetFiber} (hz : |jetValue z|≤M) :
    jetSuperposition (clipOperation M) (deriv (clipOperation M)) z=z := by
  change jetLiftValue (clippedValue M (jetValue z)) +
    jetLiftGradient (deriv (clippedValue M) (jetValue z) • jetGradient z)=z
  rw [clippedValue_eq hz,clippedValue_deriv hz,one_smul,←jetFiber_decomposition]

lemma jetValue_product (z w : JetFiber) : jetValue (jetProduct z w)=jetValue z*jetValue w := by
  change jetValue z*jetValue w+0=_; simp

lemma jetGradient_product (z w : JetFiber) :
    jetGradient (jetProduct z w)=jetValue z • jetGradient w+jetValue w • jetGradient z := by
  ext i
  change 0+(jetValue z • jetGradient w+jetValue w • jetGradient z) i=
    (jetValue z • jetGradient w+jetValue w • jetGradient z) i
  simp

theorem exists_H1_product {u v : H1} {M N : ℝ}
    (hu : ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M)
    (hv : ∀ᵐ x ∂ballMeasure, |weakValue v x|≤N) :
    ∃ p : H1,
      (∀ᵐ x ∂ballMeasure, weakValue p x=weakValue u x*weakValue v x) ∧
      (∀ᵐ x ∂ballMeasure, weakGradient p x=
        weakValue u x • weakGradient v x+weakValue v x • weakGradient u x) ∧
      (v∈H10 → p∈H10) := by
  obtain ⟨A,hA,hca⟩ := exists_clippedValue_bound M
  obtain ⟨B,hB,hcb⟩ := exists_clippedValue_bound N
  let F := clipOperation M
  let G := clipOperation N
  let p : H1 := ⟨clippedProductLp F G A B u.val v.val,
    clippedProductLp_preserves_H1 F G A B u.property v.property⟩
  have he : p.val =ᵐ[ballMeasure] fun x => jetProduct (u.val x) (v.val x) := by
    filter_upwards [clippedProductLp_ae F G A B hA.le hB.le hca hcb u.val v.val,hu,hv]
      with x hx hy hz
    exact hx.trans (by rw [jet_clipped_of_bound hy,jet_clipped_of_bound hz])
  refine ⟨p,?_,?_,?_⟩
  · filter_upwards [he] with x hx
    exact congrArg jetValue hx |>.trans (jetValue_product _ _)
  · filter_upwards [he] with x hx
    exact congrArg jetGradient hx |>.trans (jetGradient_product _ _)
  · intro hv0
    exact clippedProductLp_preserves_H10 F G A B hA.le hB.le hca hcb u.property hv0

lemma constantH1_value (r : ℝ) : weakValue (constantH1 r) =ᵐ[ballMeasure] fun _ => r := by
  filter_upwards [(constantJet_memLp r).coeFn_toLp] with x hx
  change jetValue ((constantJet_memLp r).toLp _ x)=r
  rw [hx]; rfl

lemma constantH1_gradient (r : ℝ) : weakGradient (constantH1 r) =ᵐ[ballMeasure] 0 := by
  filter_upwards [(constantJet_memLp r).coeFn_toLp] with x hx
  change jetGradient ((constantJet_memLp r).toLp _ x)=0
  rw [hx,smoothJet_constant]
  ext i; rfl

lemma weakValue_sub (u v : H1) : weakValue (u-v) =ᵐ[ballMeasure] weakValue u-weakValue v := by
  filter_upwards [Lp.coeFn_sub u.val v.val] with x hx
  change jetValue ((u.val-v.val) x)=jetValue (u.val x)-jetValue (v.val x)
  rw [hx,Pi.sub_apply,map_sub]

lemma weakValue_smul (r : ℝ) (u : H1) : weakValue (r • u) =ᵐ[ballMeasure] r • weakValue u := by
  filter_upwards [Lp.coeFn_smul r u.val] with x hx
  change jetValue ((r • u.val) x)=r*jetValue (u.val x)
  rw [hx,Pi.smul_apply,map_smul]; rfl

lemma weakGradient_sub (u v : H1) : weakGradient (u-v) =ᵐ[ballMeasure] weakGradient u-weakGradient v := by
  filter_upwards [Lp.coeFn_sub u.val v.val] with x hx
  change jetGradient ((u.val-v.val) x)=jetGradient (u.val x)-jetGradient (v.val x)
  rw [hx,Pi.sub_apply,map_sub]

lemma weakGradient_smul (r : ℝ) (u : H1) : weakGradient (r • u) =ᵐ[ballMeasure] r • weakGradient u := by
  filter_upwards [Lp.coeFn_smul r u.val] with x hx
  change jetGradient ((r • u.val) x)=r • jetGradient (u.val x)
  rw [hx,Pi.smul_apply,map_smul]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothTests
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma smoothH1_bounded (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ∃ M : ℝ, 0≤M ∧ ∀ᵐ x ∂ballMeasure, |weakValue (smoothH1 f hf) x|≤M := by
  obtain ⟨M,hM,hb⟩ := continuous_bound_ball hf.continuous
  refine ⟨M,hM,?_⟩
  filter_upwards [hb,smoothH1_value f hf] with x hx hy
  simpa only [hy,Real.norm_eq_abs] using hx

lemma compactH1_dense_H10 {u : H1} (hu : u∈H10) :
    u∈closure {v : H1 | v.val∈compactSmoothJets} := by
  rw [closure_subtype]
  have he : Subtype.val '' {v : H1 | v.val∈compactSmoothJets}=compactSmoothJets := by
    apply Set.ext; intro z; constructor
    · rintro ⟨v,hv,rfl⟩; exact hv
    · intro hz
      rcases hz with ⟨f,hf,hc,hs,hm,rfl⟩
      exact ⟨⟨hm.toLp _, (Submodule.le_topologicalClosure _)
        (Submodule.subset_span ⟨f,hf,hm,rfl⟩)⟩,⟨f,hf,hc,hs,hm,rfl⟩,rfl⟩
  rw [he,←zeroTraceAmbient_eq_closure]
  exact hu

lemma harmonic_of_compact_tests (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C) (u : H1)
    (h : ∀ (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f),
      HasCompactSupport f → tsupport f⊆ball → energy a u (smoothH1 f hf)=0) :
    Harmonic a u := by
  intro v hv
  have hs : {v : H1 | v.val∈compactSmoothJets} ⊆ {v | energyForm a ha C hC hb u v=0} := by
    rintro v ⟨f,hf,hc,hs,hm,he⟩
    have hev : v=smoothH1 f hf := Subtype.ext he
    change energyForm a ha C hC hb u v=0
    rw [hev,energyForm_apply]
    exact h f hf hc hs
  have hc : IsClosed {v | energyForm a ha C hC hb u v=0} :=
    isClosed_eq (energyForm a ha C hC hb u).continuous continuous_const
  rw [←energyForm_apply a ha C hC hb]
  exact (closure_minimal hs hc) (compactH1_dense_H10 hv)

open Set MeasureTheory Filter Topology Real

lemma inverseCorrection_eventually {r : ℝ} (hr : |r|≤1/2) :
    inverseCorrection =ᶠ[𝓝 r] fun s => (1+s)⁻¹-1 := by
  have hb : r ∈ Metric.ball 0 inverseBump.rIn := by
    change dist r 0 < (3/5:ℝ)
    rw [dist_zero_right,Real.norm_eq_abs]
    linarith
  filter_upwards [inverseBump.eventuallyEq_one_of_mem_ball hb] with s hs
  simp only [inverseCorrection,inverseClip,hs,Pi.one_apply,one_mul]

lemma inverseCorrection_eq {r : ℝ} (hr : |r|≤1/2) : inverseCorrection r=(1+r)⁻¹-1 :=
  (inverseCorrection_eventually hr).eq_of_nhds

lemma inverseCorrection_deriv {r : ℝ} (hr : |r|≤1/2) :
    deriv inverseCorrection r= -((1+r)^2)⁻¹ := by
  rw [(inverseCorrection_eventually hr).deriv_eq]
  have hn : (1:ℝ)+r≠0 := by have := (abs_le.mp hr).1; linarith
  simpa only [one_div,neg_div,pow_two,id_eq,Pi.inv_apply] using
    ((((hasDerivAt_id r).const_add 1).inv hn).sub_const 1).deriv

lemma inverseCorrection_bound {r : ℝ} (hr : |r|≤1/2) : |inverseCorrection r|≤1 := by
  rw [inverseCorrection_eq hr]
  have hlo := (abs_le.mp hr).1
  have hpos : 0<1+r := by linarith
  rw [abs_le]
  constructor
  · have h := inv_pos.mpr hpos; linarith
  · have hle : (1+r)⁻¹≤2 := (inv_le_comm₀ hpos (by norm_num)).mpr (by norm_num; linarith)
    linarith

theorem inverseOperation_spec {w : H1} (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2) :
    (∀ᵐ x ∂ballMeasure, weakValue (inverseOperation.onH1 w) x=(1+weakValue w x)⁻¹-1) ∧
    (∀ᵐ x ∂ballMeasure, weakGradient (inverseOperation.onH1 w) x=
      (-((1+weakValue w x)^2)⁻¹) • weakGradient w x) ∧
    (∀ᵐ x ∂ballMeasure, |weakValue (inverseOperation.onH1 w) x|≤1) ∧
    (w∈H10 → inverseOperation.onH1 w∈H10) := by
  refine ⟨?_,?_,?_,fun h => inverseOperation.preserves_H10 h⟩
  · filter_upwards [inverseOperation.onH1_value w,hw] with x hx h
    exact hx.trans (inverseCorrection_eq h)
  · filter_upwards [inverseOperation.onH1_gradient w,hw] with x hx h
    exact hx.trans (by rw [show deriv inverseOperation (weakValue w x)= -((1+weakValue w x)^2)⁻¹ from
      inverseCorrection_deriv h])
  · filter_upwards [inverseOperation.onH1_value w,hw] with x hx h
    change |jetValue ((inverseOperation.onH1 w).val x)|≤1
    rw [hx]; exact inverseCorrection_bound h

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildTransportFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childTransportComponentCLM_ae_of_ae (k : Fin 2) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber) (he : ballWholePiJetCLM z=ᵐ[volume] f) (i : Fin 4) :
    childTransportComponentCLM k i z=ᵐ[volume] (fun y => Fin.cases
      (f ((sourceChildHomeomorph (actualChildSign k)).symm y) 0)
      (fun j => sourceScale⁻¹*f ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis j).succ) i) := by
  have hc (j : Fin 4) : ballWholePiComponentCLM j z=ᵐ[volume] (fun y => f y j) := by
    filter_upwards [ballWholePiComponentCLM_ae j z,he] with y hi hy
    rw [hi,hy]
  have hp (j : Fin 4) := (sourceChildPushforwardCLM_ae (actualChildSign k) (ballWholePiComponentCLM j z)).trans
    ((sourceChildInverse_quasi _).ae_eq_comp (hc j))
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hp 0
  · apply (Lp.coeFn_smul _ _).trans
    filter_upwards [hp (childAxis j).succ] with y hy
    exact congrArg (fun t : ℝ => sourceScale⁻¹*t) hy

lemma childTransportJetCLM_ae_of_ae (k : Fin 2) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber) (he : ballWholePiJetCLM z=ᵐ[volume] f) :
    childTransportJetCLM k z=ᵐ[ballMeasure] (fun x => WithLp.toLp 2 (Fin.cases
      (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) 0)
      (fun j => sourceScale⁻¹*f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis j).succ))) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childTransportComponentCLM_ae_of_ae k z f he i))
  filter_upwards [physicalFourJetCLM_ae (fun i => childTransportComponentCLM k i z),ae_all_iff.mpr hi] with x hx hi
  change physicalFourJetCLM (fun i => childTransportComponentCLM k i z) x=_
  rw [hx]
  ext i
  exact hi i

lemma childAxis_involutive (i : Fin 3) : childAxis (childAxis i)=i := by
  fin_cases i <;> rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildH1Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma childH1Pullback_smooth (k : Fin 2) (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    childH1Pullback k (smoothH1 f hf)=
      smoothH1 (f ∘ sourceChildEuclidean (actualChildSign k)) (hf.comp (sourceChildEuclidean_contDiff _)) :=
  Subtype.ext (childPullbackJetCLM_smooth k f hf)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildJetScaling
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma sourceChildEuclidean_map_volume (σ : ℝ) :
    Measure.map (sourceChildEuclidean σ) volume=ENNReal.ofReal ((sourceScale^3)⁻¹) • volume := by
  change Measure.map (((WithLp.toLp 2 : Coord3 → R3) ∘ sourceChildCoordinates σ) ∘
    (WithLp.ofLp : R3 → Coord3)) volume=_
  rw [←Measure.map_map ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
    (sourceChildCoordinates_contDiff σ).continuous.measurable)
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable,
    (PiLp.volume_preserving_ofLp (Fin 3)).map_eq,
    ←Measure.map_map (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable
      (sourceChildCoordinates_contDiff σ).continuous.measurable,
    sourceChildCoordinates_map_volume,
    Measure.map_smul,
    (PiLp.volume_preserving_toLp (Fin 3)).map_eq]

lemma sourceChildEuclidean_inverse_map_volume (σ : ℝ) :
    Measure.map (sourceChildEuclidean σ).symm volume=ENNReal.ofReal (sourceScale^3) • volume := by
  apply (sourceChildEuclidean σ).toMeasurableEquiv.measurableEmbedding.map_injective
  change Measure.map (sourceChildEuclidean σ) (Measure.map (sourceChildEuclidean σ).symm volume)=
    Measure.map (sourceChildEuclidean σ) (ENNReal.ofReal (sourceScale^3) • volume)
  rw [Measure.map_map (sourceChildEuclidean σ).measurable (sourceChildEuclidean σ).symm.measurable]
  have he : (sourceChildEuclidean σ) ∘ (sourceChildEuclidean σ).symm=id :=
    funext (sourceChildEuclidean σ).apply_symm_apply
  rw [he,Measure.map_id,Measure.map_smul,
    sourceChildEuclidean_map_volume,smul_smul,
    ←ENNReal.ofReal_mul (by norm_num [sourceScale])]
  norm_num [sourceScale]

lemma integral_sourceChild_inverse (σ : ℝ) (f : R3 → ℝ) :
    (∫ x,f ((sourceChildEuclidean σ).symm x))=sourceScale^3*(∫ x,f x) := by
  have hh := integral_map_equiv (μ:=(volume : Measure R3)) (sourceChildEuclidean σ).symm.toMeasurableEquiv f
  change (∫ x,f x ∂Measure.map (sourceChildEuclidean σ).symm volume)=_ at hh
  rw [sourceChildEuclidean_inverse_map_volume,integral_smul_measure,ENNReal.toReal_ofReal (by norm_num [sourceScale]),smul_eq_mul] at hh
  exact hh.symm

lemma childAxisSwap_inner (v w : R3) : inner ℝ (childAxisSwap v) w=inner ℝ v (childAxisSwap w) := by
  simp only [PiLp.inner_apply,Fin.sum_univ_succ]
  simp [childAxisSwap,childAxis,RCLike.inner_apply]
  ring

lemma childAxisSwap_involutive (v : R3) : childAxisSwap (childAxisSwap v)=v := by
  ext i
  exact congrArg v (childAxis_involutive i)

lemma childAxisSwap_inner_self (v : R3) : inner ℝ (childAxisSwap v) (childAxisSwap v)=inner ℝ v v := by
  rw [childAxisSwap_inner,childAxisSwap_involutive]

lemma childH1Pullback_value (k : Fin 2) (u : H1) :
    weakValue (childH1Pullback k u)=ᵐ[ballMeasure]
      (fun x => weakValue u (sourceChildEuclidean (actualChildSign k) x)) := by
  filter_upwards [childPullbackJetCLM_ae k u.val] with x hx
  change jetValue (childPullbackJetCLM k u.val x)=_
  rw [hx]
  rfl

lemma childH1Pullback_gradient (k : Fin 2) (u : H1) :
    weakGradient (childH1Pullback k u)=ᵐ[ballMeasure]
      (fun x => sourceScale • childAxisSwap (weakGradient u (sourceChildEuclidean (actualChildSign k) x))) := by
  filter_upwards [childPullbackJetCLM_ae k u.val] with x hx
  change jetGradient (childPullbackJetCLM k u.val x)=_
  rw [hx]
  rfl

lemma childH10Transport_jet (k : Fin 2) (u : H10) :
    (childH10Transport k u).val=ᵐ[ballMeasure] fun x =>
      if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then
        WithLp.toLp 2 (Fin.cases (weakValue u.val ((sourceChildEuclidean (actualChildSign k)).symm x))
          (fun j => sourceScale⁻¹*weakGradient u.val ((sourceChildEuclidean (actualChildSign k)).symm x) (childAxis j)))
      else 0 := by
  have he := ballWholePiJetCLM_ae_of_ae u.val.val (fun y => u.val.val (WithLp.toLp 2 y))
    (by filter_upwards [] with x; rfl)
  apply (childTransportJetCLM_ae_of_ae k u.val.val _ he).trans
  exact Eventually.of_forall (fun x => by
    change (WithLp.toLp 2 (Fin.cases
      ((if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then u.val.val ((sourceChildEuclidean (actualChildSign k)).symm x) else 0) 0)
      (fun j => sourceScale⁻¹*(if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then
        u.val.val ((sourceChildEuclidean (actualChildSign k)).symm x) else 0) (childAxis j).succ)) : JetFiber)=_
    dsimp only
    split_ifs with h
    · rfl
    · ext i
      cases i using Fin.cases <;> simp)

lemma childH10Transport_value (k : Fin 2) (u : H10) :
    weakValue (childH10Transport k u)=ᵐ[ballMeasure] fun x =>
      if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then
        weakValue u.val ((sourceChildEuclidean (actualChildSign k)).symm x) else 0 := by
  filter_upwards [childH10Transport_jet k u] with x hx
  change jetValue ((childH10Transport k u).val x)=_
  rw [hx]
  split_ifs <;> rfl

lemma childH10Transport_gradient (k : Fin 2) (u : H10) :
    weakGradient (childH10Transport k u)=ᵐ[ballMeasure] fun x =>
      if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then
        sourceScale⁻¹ • childAxisSwap (weakGradient u.val ((sourceChildEuclidean (actualChildSign k)).symm x)) else 0 := by
  filter_upwards [childH10Transport_jet k u] with x hx
  change jetGradient ((childH10Transport k u).val x)=_
  rw [hx]
  split_ifs <;> rfl

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma integral_child_ball (k : Fin 2) (f : R3 → ℝ)
    (hf : ∀ᵐ x∂ballMeasure,(sourceChildEuclidean (actualChildSign k)).symm x∉ball → f x=0) :
    (∫ x,f x ∂ballMeasure)=sourceScale^3*(∫ x,f (sourceChildEuclidean (actualChildSign k) x) ∂ballMeasure) := by
  let S := sourceChildEuclidean (actualChildSign k)
  have hid : (fun x => if S.symm x∈ball then f x else 0)=
      (fun x => (ball.indicator (fun y => f (S y))) (S.symm x)) := by
    funext x
    simp only [indicator,Homeomorph.apply_symm_apply]
  calc
    _ = ∫ x,(if S.symm x∈ball then f x else 0) ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      split_ifs with hb
      · rfl
      · exact hx hb
    _ = ∫ x,(if S.symm x∈ball then f x else 0) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      apply ite_eq_right
      intro hh
      apply hx
      exact sourceChildEuclidean_ball k ⟨S.symm x,hh,S.apply_symm_apply x⟩
    _ = sourceScale^3*(∫ x,ball.indicator (fun y => f (S y)) x) := by
      rw [hid]
      exact integral_sourceChild_inverse _ _
    _ = _ := by rw [integral_indicator (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)]; rfl

lemma childH10Transport_gradient_at_child (k : Fin 2) (v : H10) :
    (fun x => weakGradient (childH10Transport k v) (sourceChildEuclidean (actualChildSign k) x))=ᵐ[ballMeasure]
      (fun x => sourceScale⁻¹ • childAxisSwap (weakGradient v.val x)) := by
  filter_upwards [(sourceChildEuclidean_ball_quasi k).ae_eq_comp (childH10Transport_gradient k v),
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxb
  simpa only [Function.comp_apply,Homeomorph.symm_apply_apply,ite_eq_left hxb] using hx

lemma child_energy_scaling (k : Fin 2) (v : H10) (h : H1) (a : R3 → ℝ) :
    (∫ x,a x*inner ℝ (weakGradient (childH10Transport k v) x) (weakGradient h x) ∂ballMeasure)=
      sourceScale*(∫ x,a (sourceChildEuclidean (actualChildSign k) x)*
        inner ℝ (weakGradient v.val x) (weakGradient (childH1Pullback k h) x) ∂ballMeasure) := by
  rw [integral_child_ball k _ (by
    filter_upwards [childH10Transport_gradient k v] with x hx hn
    rw [hx,ite_eq_right hn,inner_zero_left,mul_zero])]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [childH10Transport_gradient_at_child k v,childH1Pullback_gradient k h] with x hv hh
  rw [hv,hh,real_inner_smul_left,real_inner_smul_right,childAxisSwap_inner]
  norm_num [sourceScale]
  ring

lemma weakGradient_norm_sq_integral (u : H1) :
    ‖weakGradientL u‖^2=(∫ x,inner ℝ (weakGradient u x) (weakGradient u x) ∂ballMeasure) := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weakGradientL_apply_ae u] with x hx
  rw [hx]

lemma child_gradient_norm_sq (k : Fin 2) (v : H10) :
    ‖weakGradientL (childH10Transport k v)‖^2=sourceScale*‖weakGradientL v.val‖^2 := by
  rw [weakGradient_norm_sq_integral,weakGradient_norm_sq_integral]
  rw [integral_child_ball k _ (by
    filter_upwards [childH10Transport_gradient k v] with x hx hn
    rw [hx,ite_eq_right hn,inner_zero_left])]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [childH10Transport_gradient_at_child k v] with x hv
  rw [hv,real_inner_smul_left,real_inner_smul_right,childAxisSwap_inner_self]
  norm_num [sourceScale]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevMaximum
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Real

lemma energy_integrable (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C) (u v : H1) :
    Integrable (fun x => a x*inner ℝ (weakGradient u x) (weakGradient v x)) ballMeasure := by
  apply (L2.integrable_inner (boundedMultiplier ballMeasure a ha C hC hb (weakGradientL u))
    (weakGradientL v)).congr
  filter_upwards [boundedMultiplier_apply_ae ballMeasure a ha C hC hb (weakGradientL u),
    weakGradientL_apply_ae u,weakGradientL_apply_ae v] with x hx hy hz
  rw [hx,hy,hz,real_inner_smul_left]

lemma zero_of_weakGradient_zero {u : H1} (hu : u∈H10)
    (hg : weakGradient u =ᵐ[ballMeasure] 0) : u=0 := by
  have he : weakGradientL u=0 := by
    apply Lp.ext
    filter_upwards [weakGradientL_apply_ae u,hg,Lp.coeFn_zero R3 2 ballMeasure] with x hx hy hz
    rw [hx,hy,hz]
  have hn := H10_norm_le_weakGradientL (⟨u,hu⟩ : H10)
  rw [he,norm_zero,mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg u))

lemma chain_zero (F : SmoothLipZero) {v : H1}
    (hv : ∀ᵐ x ∂ballMeasure, F (weakValue v x)=0)
    (hd : ∀ᵐ x ∂ballMeasure, deriv F (weakValue v x)=0) : F.onH1 v=0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [F.onLp_ae v.val,hv,hd,Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx hy hd hz
  change F.onLp v.val x=(0:JetSpace) x
  rw [hx,hz]
  unfold jetSuperposition
  rw [hy,hd,zero_smul,map_zero,map_zero,add_zero]
  rfl

lemma upperTransition_nonneg (M : ℝ) (hM : 0≤M) (r : ℝ) : 0≤upperTransition M hM r :=
  smoothTransition.nonneg _

lemma upperTransition_zero_iff (M : ℝ) (hM : 0≤M) (r : ℝ) :
    upperTransition M hM r=0 ↔ r≤M := by
  change smoothTransition (r-M)=0 ↔ r≤M
  rw [smoothTransition.zero_iff_nonpos,sub_nonpos]

lemma upperTransition_deriv_nonneg (M : ℝ) (hM : 0≤M) (r : ℝ) :
    0≤deriv (upperTransition M hM) r := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact smoothTransition.monotone (sub_le_sub_right hxy M)

lemma upperTransition_deriv_zero {M r : ℝ} (hM : 0≤M) (hr : r≤M) :
    deriv (upperTransition M hM) r=0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro s
  rw [(upperTransition_zero_iff M hM r).mpr hr]
  exact upperTransition_nonneg M hM s

theorem harmonic_le_of_trace_le (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    (hp : ∀ᵐ x ∂ballMeasure, 0<a x) {u v : H1}
    (hu : Harmonic a u) (ht : trace u=trace v) {M : ℝ} (hM : 0≤M)
    (hv : ∀ᵐ x ∂ballMeasure, weakValue v x≤M) :
    ∀ᵐ x ∂ballMeasure, weakValue u x≤M := by
  let F := upperTransition M hM
  have hv0 : F.onH1 v=0 := by
    apply chain_zero F
    · filter_upwards [hv] with x hx
      exact (upperTransition_zero_iff M hM _).mpr hx
    · filter_upwards [hv] with x hx
      exact upperTransition_deriv_zero hM hx
  have ht0 : trace (F.onH1 u)=trace (0:H1) := by
    rw [←hv0]; exact chain_trace_eq F ht
  have hh0 : F.onH1 u∈H10 := by
    have hh := (Submodule.Quotient.eq H10).mp ht0
    simpa only [sub_zero] using hh
  have he := hu (F.onH1 u) hh0
  have hg := F.onH1_gradient u
  have hnonneg : 0 ≤ᵐ[ballMeasure] fun x => a x*inner ℝ (weakGradient u x) (weakGradient (F.onH1 u) x) := by
    filter_upwards [hp,hg] with x ha hx
    rw [hx,real_inner_smul_right]
    exact mul_nonneg ha.le (mul_nonneg (upperTransition_deriv_nonneg M hM _) real_inner_self_nonneg)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    (energy_integrable a ha C hC hb u (F.onH1 u))).mp he
  have hhg : weakGradient (F.onH1 u) =ᵐ[ballMeasure] 0 := by
    filter_upwards [hp,hg,hzero] with x ha hx hz
    rw [hx,real_inner_smul_right] at hz
    have hh : deriv F (weakValue u x)*inner ℝ (weakGradient u x) (weakGradient u x)=0 :=
      (mul_eq_zero.mp hz).resolve_left ha.ne'
    rcases mul_eq_zero.mp hh with hd | hd
    · rw [hx,hd,zero_smul]; rfl
    · rw [hx,inner_self_eq_zero.mp hd,smul_zero]; rfl
  have hF0 := zero_of_weakGradient_zero hh0 hhg
  have hval := F.onH1_value u
  filter_upwards [hval,Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx hz
  apply (upperTransition_zero_iff M hM _).mp
  rw [←hx,hF0]
  change jetValue ((0:JetSpace) x)=0
  rw [hz]; rfl

lemma harmonic_neg (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    {u : H1} (hu : Harmonic a u) : Harmonic a (-u) := by
  intro h hh
  rw [←energyForm_apply a ha C hC hb,map_neg,neg_apply,
    energyForm_apply a ha C hC hb,hu h hh,neg_zero]

lemma weakValue_neg (u : H1) : weakValue (-u) =ᵐ[ballMeasure] -weakValue u := by
  filter_upwards [Lp.coeFn_neg u.val] with point hneg
  change jetValue ((-u.val) point) = -jetValue (u.val point)
  rw [hneg,Pi.neg_apply,map_neg]

theorem harmonic_bounded_of_trace_bounded (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    (hp : ∀ᵐ x ∂ballMeasure, 0<a x) {u v : H1}
    (hu : Harmonic a u) (ht : trace u=trace v) {M : ℝ} (hM : 0≤M)
    (hv : ∀ᵐ x ∂ballMeasure, |weakValue v x|≤M) :
    ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M := by
  have hup := harmonic_le_of_trace_le a ha C hC hb hp hu ht hM
    (hv.mono (fun x hx => (abs_le.mp hx).2))
  have hvneg : ∀ᵐ x ∂ballMeasure, weakValue (-v) x≤M := by
    filter_upwards [hv,weakValue_neg v] with x hx hy
    rw [hy]; exact (neg_le_iff_add_nonneg).mpr (by linarith [(abs_le.mp hx).1])
  have htneg : trace (-u)=trace (-v) := by
    change H10.mkQ (-u)=H10.mkQ (-v)
    simpa only [map_neg,trace] using congrArg Neg.neg ht
  have hlo := harmonic_le_of_trace_le a ha C hC hb hp
    (harmonic_neg a ha C hC hb hu) htneg hM hvneg
  filter_upwards [hup,hlo,weakValue_neg u] with x hx hy hz
  apply abs_le.mpr
  rw [hz,Pi.neg_apply] at hy
  exact ⟨by linarith,hx⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalBlockDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceCollarTime_pos_iff_domain (y : Fin 3 → ℝ) :
    0 < sourceCollarTime y ↔ WithLp.toLp 2 y∈sourceDomain := by
  change 0 < sourceCollarTime y ↔ sourceHole < sourceRadial y ∧ sourceRadial y<1 ∧ |y 2|<1
  rw [←not_le,sourceCollarTime_le_iff]
  simp only [sub_zero,mul_zero,add_zero,not_or,not_le]
  tauto

lemma sourceDomain_closure_time (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈closure sourceDomain ↔ 0≤ sourceCollarTime y := by
  have hcoord : Continuous (fun x : R3 => (fun i : Fin 3 => x i)) :=
    continuous_pi (fun i => (EuclideanSpace.proj i).continuous)
  have hclosed : IsClosed {x : R3 | 0≤ sourceCollarTime (fun i => x i)} :=
    isClosed_le continuous_const (locallyLipschitz_sourceCollarTime.continuous.comp hcoord)
  constructor
  · intro hy
    exact closure_minimal (fun x hx => ((sourceCollarTime_pos_iff_domain _).mpr hx).le) hclosed hy
  · intro hy
    by_cases hp : 0 < sourceCollarTime y
    · exact subset_closure ((sourceCollarTime_pos_iff_domain y).mp hp)
    · have he : sourceCollarTime y=0 := le_antisymm (le_of_not_gt hp) hy
      let g : ℝ → R3 := fun t => WithLp.toLp 2 (sourceAngularCollar t (sourcePhysicalAngles y))
      have hg : Continuous g := (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
        (continuous_uncurry_sourceAngularCollar.comp (continuous_id.prodMk continuous_const))
      have hz : (0:ℝ)∈closure (Ioo 0 centralThickness) := by
        rw [closure_Ioo (show (0:ℝ)≠centralThickness by norm_num [centralThickness])]
        exact ⟨le_rfl,by norm_num [centralThickness]⟩
      have hin : g '' Ioo 0 centralThickness ⊆ sourceDomain := by
        rintro _ ⟨t,ht,rfl⟩
        apply (sourceCollarTime_pos_iff_domain _).mp
        rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
          ⟨by linarith [ht.1],ht.2.le.trans (by norm_num [centralThickness])⟩)]
        exact ht.1
      have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
      have hright := sourcePhysicalCoordinates_right
        (show sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100) by rw [he]; norm_num)
      rw [he] at hright
      simpa only [g,hright] using hmem

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevDistribution
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma smooth_ball_integration_by_parts {f ψ : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball) (v : R3) :
    (∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure)=
      -(∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := ψ) (g := f) (v := v)
    ((hdψ.mul hf.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right)
    ((hψ.continuous.mul hdf).integrable_of_hasCompactSupport hc.mul_right)
    ((hψ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  have hl : (∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure)=∫ x, ψ x*fderiv ℝ f x v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)),zero_mul]
  have hr : (∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure)=∫ x, fderiv ℝ ψ x v*f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (hs hh))]
    simp
  rw [hl,hr]; exact he

lemma weak_integration_by_parts (u : H1) {ψ : R3 → ℝ}
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆ball) (v : R3) :
    inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v u)=
      -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL u) := by
  have hd {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
      (weakDirectionL v (smoothH1 f hf) : R3 → ℝ) =ᵐ[ballMeasure]
        fun x => fderiv ℝ f x v := by
    filter_upwards [weakDirectionL_apply_ae (smoothH1 f hf) v,smoothH1_gradient f hf]
      with x hx hy
    simp only [hx,hy,inner_gradient_right,RCLike.conj_to_real]
  have hv {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
      (weakValueL (smoothH1 f hf) : R3 → ℝ) =ᵐ[ballMeasure] f :=
    (weakValueL_apply_ae _).trans (smoothH1_value f hf)
  have hsmooth : {z : H1 | z.val∈smoothJets} ⊆
      {z | inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v z)=
        -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL z)} := by
    rintro z ⟨f,hf,hm,he⟩
    have hz : z=smoothH1 f hf := Subtype.ext he
    change inner ℝ (weakValueL (smoothH1 ψ hψ)) (weakDirectionL v z)=
      -inner ℝ (weakDirectionL v (smoothH1 ψ hψ)) (weakValueL z)
    rw [hz,L2.inner_def,L2.inner_def]
    have hl : (∫ x, inner ℝ (weakValueL (smoothH1 ψ hψ) x)
        (weakDirectionL v (smoothH1 f hf) x) ∂ballMeasure)=
        ∫ x, ψ x*fderiv ℝ f x v ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hv hψ,hd hf] with x hx hy
      simp only [hx,hy,Real.inner_apply]
    have hr : (∫ x, inner ℝ (weakDirectionL v (smoothH1 ψ hψ) x)
        (weakValueL (smoothH1 f hf) x) ∂ballMeasure)=
        ∫ x, fderiv ℝ ψ x v*f x ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hd hψ,hv hf] with x hx hy
      simp only [hx,hy,Real.inner_apply]
    rw [hl,hr]
    exact smooth_ball_integration_by_parts hf hψ hc hs v

  exact (closure_minimal hsmooth (isClosed_eq
    (continuous_const.inner (weakDirectionL v).continuous)
    ((continuous_const.inner weakValueL.continuous).neg))) (smoothH1_dense u)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma weakDirection_zero_of_value_zero (u : H1)
    (hu : weakValue u =ᵐ[ballMeasure] 0) (v : R3) : weakDirectionL v u=0 := by
  have huv : weakValueL u=0 := Lp.ext (((weakValueL_apply_ae u).trans hu).trans (Lp.coeFn_zero ℝ 2 ballMeasure).symm)
  have hi : Integrable (weakDirectionL v u : R3 → ℝ) ballMeasure :=
    (Lp.memLp _).integrable (by norm_num)
  have hz := (Metric.isOpen_ball : IsOpen ball).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hi.locallyIntegrable.locallyIntegrableOn ball) (fun ψ hψ hc hs => ?_)
  · apply Lp.ext
    filter_upwards [hz,ae_restrict_mem (Metric.isOpen_ball.measurableSet : MeasurableSet ball),
      Lp.coeFn_zero ℝ 2 ballMeasure] with x hx hb hzero
    exact (hx hb).trans hzero.symm
  · have h := weak_integration_by_parts u hψ hc hs v
    rw [huv,inner_zero_right,neg_zero,L2.inner_def] at h
    rw [←h]
    apply integral_congr_ae
    filter_upwards [(weakValueL_apply_ae _).trans (smoothH1_value ψ hψ)] with x hx
    simp only [hx,Real.inner_apply,smul_eq_mul]

lemma h1_eq_zero_of_value_zero (u : H1) (hu : weakValue u =ᵐ[ballMeasure] 0) : u=0 := by
  have hg (i : Fin 3) : ∀ᵐ x ∂ballMeasure, weakGradient u x i=0 := by
    have he := weakDirection_zero_of_value_zero u hu (EuclideanSpace.single i 1)
    filter_upwards [weakDirectionL_apply_ae u (EuclideanSpace.single i 1),
      ((Lp.ext_iff.mp he).trans (Lp.coeFn_zero ℝ 2 ballMeasure))] with x hx hy
    have hh : inner ℝ (EuclideanSpace.single i 1) (weakGradient u x)=0 := hx.symm.trans hy
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using hh
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hu,ae_all_iff.mpr hg,Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx hy hzero
  change weakValue u x=0 at hx
  change (0 : JetSpace) x=0 at hzero
  have hwg : weakGradient u x=0 := by ext i; exact hy i
  calc
    u.val x = jetLiftValue (jetValue (u.val x)) + jetLiftGradient (jetGradient (u.val x)) :=
      jetFiber_decomposition _
    _ = 0 := by change jetLiftValue (weakValue u x)+jetLiftGradient (weakGradient u x)=0
                rw [hx,hwg,map_zero,map_zero,add_zero]
    _ = (0 : JetSpace) x := hzero.symm

lemma weakValueL_injective : Function.Injective weakValueL := by
  intro u v huv
  have he : weakValueL (u-v)=0 := by rw [map_sub,huv,sub_self]
  have hz : weakValue (u-v) =ᵐ[ballMeasure] 0 :=
    (weakValueL_apply_ae _).symm.trans ((Lp.ext_iff.mp he).trans (Lp.coeFn_zero ℝ 2 ballMeasure))
  exact sub_eq_zero.mp (h1_eq_zero_of_value_zero _ hz)

lemma nonzero_h1_positive_value_measure {u : H1} (hu : u≠0) :
    0<ballMeasure {x | weakValue u x≠0} := by
  by_contra h
  have hz : ballMeasure {x | weakValue u x≠0}=0 := le_zero_iff.mp (not_lt.mp h)
  have he : weakValue u =ᵐ[ballMeasure] 0 := by
    rw [Filter.EventuallyEq,ae_iff]
    exact hz
  exact hu (h1_eq_zero_of_value_zero u he)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_NestedLimits
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma h1_limit_ae_closed {u : ℕ → H1} {w : H1}
    (hu : Tendsto u atTop (𝓝 w)) (K : R3 → Set JetFiber)
    (hK : ∀ x, IsClosed (K x)) (hm : ∀ n, ∀ᵐ x ∂ballMeasure, (u n).val x∈K x) :
    ∀ᵐ x ∂ballMeasure, w.val x∈K x := by
  have ht : Tendsto (fun n => (u n).val) atTop (𝓝 w.val) :=
    continuous_subtype_val.continuousAt.tendsto.comp hu
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  filter_upwards [hφae,ae_all_iff.mpr hm] with x hx hy
  exact (hK x).mem_of_tendsto hx (Eventually.of_forall (fun n => hy (φ n)))

lemma h1_limit_bounded {u : ℕ → H1} {w : H1} {M : ℝ}
    (hu : Tendsto u atTop (𝓝 w))
    (hm : ∀ n, ∀ᵐ x ∂ballMeasure, |weakValue (u n) x|≤M) :
    ∀ᵐ x ∂ballMeasure, |weakValue w x|≤M := by
  exact h1_limit_ae_closed hu (fun _ => {z | |jetValue z|≤M})
    (fun _ => isClosed_le (jetValue.continuous.abs) continuous_const) hm

lemma h1_limit_supported {u : ℕ → H1} {w : H1} {r : ℝ}
    (hu : Tendsto u atTop (𝓝 w))
    (hm : ∀ n, ∀ᵐ x ∂ballMeasure, r<‖x‖ →
      weakValue (u n) x=0 ∧ weakGradient (u n) x=0) :
    ∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0 := by
  exact h1_limit_ae_closed hu
    (fun x => {z | r<‖x‖ → jetValue z=0 ∧ jetGradient z=0})
    (fun x => by
      by_cases hx : r<‖x‖
      · simpa only [hx,true_implies,Set.inter_def,Set.mem_ofPred_eq] using
          (isClosed_eq jetValue.continuous continuous_const).inter
            (isClosed_eq jetGradient.continuous continuous_const)
      · simp only [hx,IsEmpty.forall_iff,Set.ofPred_true]
        exact isClosed_univ) hm

lemma weakValue_sum (s : Finset ℕ) (u : ℕ → H1) :
    weakValue (∑ n∈s, u n) =ᵐ[ballMeasure] fun x => ∑ n∈s, weakValue (u n) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx
    change jetValue ((0:JetSpace) x)=0
    rw [hx,Pi.zero_apply,map_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [weakValue_add (u a) (∑ i∈s,u i),ih] with x hx hy
    simpa only [Pi.add_apply,hy] using hx

lemma weakGradient_sum (s : Finset ℕ) (u : ℕ → H1) :
    weakGradient (∑ n∈s, u n) =ᵐ[ballMeasure] fun x => ∑ n∈s, weakGradient (u n) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx
    change jetGradient ((0:JetSpace) x)=0
    rw [hx,Pi.zero_apply,map_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [weakGradient_add (u a) (∑ i∈s,u i),ih] with x hx hy
    simpa only [Pi.add_apply,hy] using hx

theorem source_series_limit (Z : ℕ → H1) (b : ℕ → ℝ)
    (hnorm : Summable (fun n => ‖Z n‖)) (hb : Summable b)
    (hb0 : ∀ n, 0≤b n) (hZ : ∀ n, Z n∈H10)
    (hbound : ∀ n, ∀ᵐ x ∂ballMeasure, |weakValue (Z n) x|≤b n)
    (r : ℝ) (hsupp : ∀ n, ∀ᵐ x ∂ballMeasure, r<‖x‖ →
      weakValue (Z n) x=0 ∧ weakGradient (Z n) x=0) :
    ∃ w : H1, w∈H10 ∧
      Tendsto (fun N => ∑ n∈Finset.range N, Z n) atTop (𝓝 w) ∧
      (∀ᵐ x ∂ballMeasure, |weakValue w x|≤∑' n,b n) ∧
      (∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0) := by
  classical
  have hsum : Summable Z := hnorm.of_norm
  refine ⟨∑' n,Z n,?_,hsum.hasSum.tendsto_sum_nat,?_,?_⟩
  · exact H10_isClosed.mem_of_tendsto hsum.hasSum.tendsto_sum_nat
      (Eventually.of_forall (fun N => H10.sum_mem (fun n _ => hZ n)))
  · apply h1_limit_bounded hsum.hasSum.tendsto_sum_nat
    intro N
    filter_upwards [weakValue_sum (Finset.range N) Z,ae_all_iff.mpr hbound] with x hx hy
    rw [hx]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun n _ => hy n)).trans (Summable.sum_le_tsum _ (fun n _ => hb0 n) hb))
  · apply h1_limit_supported hsum.hasSum.tendsto_sum_nat
    intro N
    filter_upwards [weakValue_sum (Finset.range N) Z,weakGradient_sum (Finset.range N) Z,
      ae_all_iff.mpr hsupp] with x hv hg hx
    intro hr
    simp only [hv,hg]
    exact ⟨Finset.sum_eq_zero (fun n _ => (hx n hr).1),Finset.sum_eq_zero (fun n _ => (hx n hr).2)⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CriticalWallGap
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma h1_layer_norm_bound {Z : H1} (hZ : Z∈H10) {K q : ℝ}
    (hK : 0≤K) (hq : 0≤q) (n : ℕ)
    (he : ‖weakGradientL Z‖^2≤K*q^n) :
    ‖Z‖≤h10PoincareConstant*Real.sqrt K*(Real.sqrt q)^n := by
  have hsK := Real.sq_sqrt hK
  have hsQ := Real.sq_sqrt hq
  have hp : (Real.sqrt K*(Real.sqrt q)^n)^2=K*q^n := by
    rw [mul_pow,←pow_mul,show n*2=2*n by omega,pow_mul,hsK,hsQ]
  have hn : ‖weakGradientL Z‖≤Real.sqrt K*(Real.sqrt q)^n := by
    nlinarith [norm_nonneg (weakGradientL Z),Real.sqrt_nonneg K,
      mul_nonneg (Real.sqrt_nonneg K) (pow_nonneg (Real.sqrt_nonneg q) n)]
  exact (H10_norm_le_weakGradientL (⟨Z,hZ⟩:H10)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn h10PoincareConstant_pos.le)

theorem geometric_source_series (Z : ℕ → H1) {K q : ℝ}
    (hK : 0≤K) (hq : 0≤q) (hq1 : q<1) (hZ : ∀ n, Z n∈H10)
    (hbound : ∀ n, ∀ᵐ x ∂ballMeasure, |weakValue (Z n) x|≤K*q^n)
    (henergy : ∀ n, ‖weakGradientL (Z n)‖^2≤K*q^n)
    (r : ℝ) (hsupp : ∀ n, ∀ᵐ x ∂ballMeasure, r<‖x‖ →
      weakValue (Z n) x=0 ∧ weakGradient (Z n) x=0) :
    ∃ w : H1, w∈H10 ∧
      Tendsto (fun N => ∑ n∈Finset.range N,Z n) atTop (𝓝 w) ∧
      (∀ᵐ x ∂ballMeasure, |weakValue w x|≤K/(1-q)) ∧
      (∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0) := by
  have hsq : Real.sqrt q<1 := by
    have hh := Real.sq_sqrt hq
    have hn := Real.sqrt_nonneg q
    nlinarith
  have hs : Summable (fun n => ‖Z n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => h1_layer_norm_bound (hZ n) hK hq n (henergy n))
      ((summable_geometric_of_lt_one (Real.sqrt_nonneg q) hsq).mul_left _)
  have hv : Summable (fun n => K*q^n) := (summable_geometric_of_lt_one hq hq1).mul_left K
  obtain ⟨w,hw,ht,hb,hsp⟩ := source_series_limit Z (fun n => K*q^n) hs hv
    (fun n => mul_nonneg hK (pow_nonneg hq n)) hZ hbound r hsupp
  refine ⟨w,hw,ht,?_,hsp⟩
  have hts : (∑' n : ℕ,K*q^n)=K/(1-q) := by
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq hq1,div_eq_mul_inv]
  simpa only [hts] using hb

lemma source_energy_limit (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    {w : ℕ → H1} {u : H1} (hw : Tendsto w atTop (𝓝 u)) (ψ : H1) :
    Tendsto (fun n => energy a (w n) ψ) atTop (𝓝 (energy a u ψ)) := by
  simpa only [Function.comp_def,ContinuousLinearMap.flip_apply,energyForm_apply] using
    ((energyForm a ha C hC hb).flip ψ).continuous.continuousAt.tendsto.comp hw

lemma source_energy_nonzero (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    {w : ℕ → H1} {u : H1} (hw : Tendsto w atTop (𝓝 u)) (ψ : H1)
    (hne : ∀ᶠ n in atTop, energy a (w n) ψ=1) :
    u≠0 ∧ 0<ballMeasure {x | weakValue u x≠0} := by
  have he : energy a u ψ=1 := tendsto_nhds_unique
    (source_energy_limit a ha hC hb hw ψ) (tendsto_const_nhds.congr' (hne.mono (fun n hn => hn.symm)))
  have hu : u≠0 := by
    intro hz
    rw [hz,←energyForm_apply a ha C hC hb,map_zero,_root_.zero_apply] at he
    norm_num at he
  exact ⟨hu,nonzero_h1_positive_value_measure hu⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_VoltageBoundaryTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped Convolution ENNReal NNReal

lemma smoothOuterFourier_original (i : Fin 3) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    physicalOuterTraceCLM i (smoothH1 f hf)=continuousOuterFourier i hf.continuous := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hp : ContDiff ℝ (↑(⊤:ℕ∞)) (f ∘ e) := hf.comp e.contDiff
  have he : piSmoothH1 hp=smoothH1 f hf := by
    unfold piSmoothH1
    congr 1
  rw [←he]
  have hh := (dense_linear_observable_extension smoothPiH1L (smoothOuterFourierL i)
    smoothPiH1L_dense (smoothOuterFourierL_bound i)).choose_spec ⟨f ∘ e,hp⟩
  exact hh

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalRealTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
attribute [local instance] OAI.ScalarConductivity.physicalRealTraceMeasureSpaceUnitAddCircle
local instance physicalRealTraceIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma H1_eq_of_value_ae {u v : H1} (h : weakValue u=ᵐ[ballMeasure] weakValue v) : u=v := by
  apply weakValueL_injective
  apply Lp.ext
  exact (weakValueL_apply_ae u).trans (h.trans (weakValueL_apply_ae v).symm)

lemma SmoothLipZero.onH1_smooth (F : SmoothLipZero) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) : F.onH1 (smoothH1 f hf)=smoothH1 (F ∘ f) (F.smooth.comp hf) := by
  apply H1_eq_of_value_ae
  filter_upwards [F.onH1_value (smoothH1 f hf),smoothH1_value f hf,
    smoothH1_value (F ∘ f) (F.smooth.comp hf)] with x hF hf hh
  change weakValue (F.onH1 (smoothH1 f _)) x=F (weakValue (smoothH1 f _) x) at hF
  rw [hF,hf,hh]
  rfl

lemma physicalRealTrace_smooth_ae (i : Fin 3) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    physicalRealTraceCLM i (smoothH1 f hf)=ᵐ[volume]
      fun θ => f (WithLp.toLp 2 (physicalOuterBoundary i θ)) := by
  have he : physicalComplexTraceCLM i (smoothH1 f hf)=
      ContinuousMap.toLp 2 volume ℂ (continuousOuterMap i hf.continuous) := by
    change (mFourierBasis (d:=Fin 2)).repr.symm (physicalOuterTraceCLM i (smoothH1 f hf))=_
    rw [smoothOuterFourier_original]
    exact (mFourierBasis (d:=Fin 2)).repr.symm_apply_apply _
  have hh := Complex.reCLM.coeFn_compLpL (p:=2) (μ:=volume) (physicalComplexTraceCLM i (smoothH1 f hf))
  change physicalRealTraceCLM i (smoothH1 f hf)=ᵐ[volume] _ at hh
  rw [he] at hh
  filter_upwards [hh,ContinuousMap.coeFn_toLp (continuousOuterMap i hf.continuous) (p:=2) (μ:=volume) (𝕜:=ℂ)]
    with θ hθ hv
  rw [hθ,hv]
  rfl

theorem physicalRealTrace_chain (F : SmoothLipZero) (i : Fin 3) (u : H1) :
    physicalRealTraceCLM i (F.onH1 u)=F.lipschitz.compLp F.at_zero (physicalRealTraceCLM i u) := by
  have hc : IsClosed {u : H1 | physicalRealTraceCLM i (F.onH1 u)=
      F.lipschitz.compLp F.at_zero (physicalRealTraceCLM i u)} :=
    isClosed_eq ((physicalRealTraceCLM i).continuous.comp F.onH1_continuous)
      ((F.lipschitz.continuous_compLp F.at_zero).comp (physicalRealTraceCLM i).continuous)
  apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hc) (smoothH1_dense u)
  rintro v ⟨f,hf,hm,he⟩
  have hv : v=smoothH1 f hf := Subtype.ext he
  change physicalRealTraceCLM i (F.onH1 v)=_
  rw [hv,F.onH1_smooth]
  apply Lp.ext
  filter_upwards [physicalRealTrace_smooth_ae i (F.smooth.comp hf),
    F.lipschitz.coeFn_compLp F.at_zero (physicalRealTraceCLM i (smoothH1 f hf)),
    physicalRealTrace_smooth_ae i hf] with θ hF hc hhf
  rw [hF,hc]
  change F (f (WithLp.toLp 2 (physicalOuterBoundary i θ)))=F (physicalRealTraceCLM i (smoothH1 f hf) θ)
  rw [hhf]

theorem physicalRealTrace_upper_bound (i : Fin 3) (u : H1) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,weakValue u x≤M) :
    ∀ᵐ θ : UnitAddTorus (Fin 2),physicalRealTraceCLM i u θ≤M := by
  let F := upperTransition M hM
  have hz : F.onH1 u=0 := by
    apply h1_eq_zero_of_value_zero
    filter_upwards [F.onH1_value u,hb] with x hx hb
    change weakValue (F.onH1 u) x=F (weakValue u x) at hx
    rw [hx]
    exact (upperTransition_zero_iff M hM _).mpr hb
  have ht := physicalRealTrace_chain F i u
  rw [hz,map_zero] at ht
  have he := (Lp.ext_iff.mp ht).symm.trans (Lp.coeFn_zero ℝ 2 (volume : Measure (UnitAddTorus (Fin 2))))
  filter_upwards [he,F.lipschitz.coeFn_compLp F.at_zero (physicalRealTraceCLM i u)] with θ hz hc
  exact (upperTransition_zero_iff M hM _).mp (hc.symm.trans hz)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTraceMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.physicalTraceMeanMeasureSpace
local instance physicalTraceMeanIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma physicalRealTrace_mean (i : Fin 3) (u : H1) :
    (∫ θ,physicalRealTraceCLM i u θ)=(physicalOuterTraceCLM i u 0).re := by
  have he : (mFourierBasis (d:=Fin 2)).repr (physicalComplexTraceCLM i u)=physicalOuterTraceCLM i u :=
    (mFourierBasis (d:=Fin 2)).repr.apply_symm_apply _
  rw [←he,mFourierBasis_repr]
  simp only [mFourierCoeff,neg_zero,mFourier_zero,ContinuousMap.one_apply,one_smul]
  have hi : Integrable (physicalComplexTraceCLM i u) :=
    (Lp.memLp (physicalComplexTraceCLM i u)).integrable (by norm_num)
  calc
    _ = ∫ θ,Complex.reCLM (physicalComplexTraceCLM i u θ) := integral_congr_ae
      (Complex.reCLM.coeFn_compLpL (p:=2) (μ:=volume) (physicalComplexTraceCLM i u))
    _ = _ := Complex.reCLM.integral_comp_comm hi

lemma constantTerminalFlux_realTrace (κ : Fin 3 → ℝ) (u : H1) :
    constantTerminalFluxCLM κ u=angularArea*∑ i : Fin 3,κ i*(∫ θ,physicalRealTraceCLM i u θ) := by
  simp only [constantTerminalFluxCLM,smul_apply,sum_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul,physicalRealTrace_mean]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalTraceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
attribute [local instance] OAI.ScalarConductivity.physicalTraceTransportMeasureSpace
local instance physicalTraceTransportProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma physicalRealTrace_child (k : Fin 2) (u : H1) :
    physicalRealTraceCLM k.succ u=physicalRealTraceCLM 0 (childH1Pullback k u) := by
  have hc : IsClosed {u : H1 | physicalRealTraceCLM k.succ u=
      physicalRealTraceCLM 0 (childH1Pullback k u)} :=
    isClosed_eq (physicalRealTraceCLM k.succ).continuous
      ((physicalRealTraceCLM 0).continuous.comp (childH1Pullback k).continuous)
  apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hc) (smoothH1_dense u)
  rintro v ⟨f,hf,_,he⟩
  have hv : v=smoothH1 f hf := Subtype.ext he
  change physicalRealTraceCLM k.succ v=physicalRealTraceCLM 0 (childH1Pullback k v)
  rw [hv,childH1Pullback_smooth]
  apply Lp.ext
  filter_upwards [physicalRealTrace_smooth_ae k.succ hf,
    physicalRealTrace_smooth_ae 0 (hf.comp (sourceChildEuclidean_contDiff (actualChildSign k)))] with θ h1 h0
  exact h1.trans h0.symm

lemma sourceMean_eq_integral (i : Fin 3) (u : H1) :
    sourceMeanCLM i u=∫ θ,physicalRealTraceCLM i u θ := (physicalRealTrace_mean i u).symm

lemma sourceMean_child (k : Fin 2) (u : H1) :
    sourceMeanCLM k.succ u=sourceMeanCLM 0 (childH1Pullback k u) := by
  rw [sourceMean_eq_integral,sourceMean_eq_integral,physicalRealTrace_child]

lemma basisFlux_mean (j : Fin 2) (u : H1) :
    constantTerminalFluxCLM (centralBasisSlopes j) u=
      angularArea*(sourceMeanCLM j.succ u-sourceMeanCLM 0 u) := by
  rw [constantTerminalFlux_realTrace]
  simp only [←sourceMean_eq_integral]
  rw [Fin.sum_univ_three]
  fin_cases j
  · change angularArea*((-1)*sourceMeanCLM 0 u+1*sourceMeanCLM 1 u+0*sourceMeanCLM 2 u)=angularArea*(sourceMeanCLM 1 u-sourceMeanCLM 0 u)
    ring
  · change angularArea*((-1)*sourceMeanCLM 0 u+0*sourceMeanCLM 1 u+1*sourceMeanCLM 2 u)=angularArea*(sourceMeanCLM 2 u-sourceMeanCLM 0 u)
    ring

lemma physicalRealTrace_bound (i : Fin 3) (u : H1) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x)≤M) :
    ∀ᵐ θ : UnitAddTorus (Fin 2),abs (physicalRealTraceCLM i u θ)≤M := by
  have hh := physicalRealTrace_upper_bound i u hM (hb.mono (fun _ h => (abs_le.mp h).2))
  have hn : ∀ᵐ x∂ballMeasure,weakValue (-u) x≤M := by
    filter_upwards [hb,weakValue_neg u] with x hx hn
    rw [hn,Pi.neg_apply]
    linarith [(abs_le.mp hx).1]
  have hh' := physicalRealTrace_upper_bound i (-u) hM hn
  rw [map_neg] at hh'
  filter_upwards [hh,hh',Lp.coeFn_neg (physicalRealTraceCLM i u)] with θ h0 h1 hn
  rw [hn,Pi.neg_apply] at h1
  exact abs_le.mpr ⟨by linarith,h0⟩

lemma sourceMean_bound (i : Fin 3) (u : H1) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x)≤M) : abs (sourceMeanCLM i u)≤M := by
  rw [sourceMean_eq_integral]
  have hh : ∀ᵐ θ,‖physicalRealTraceCLM i u θ‖≤M := by
    simpa only [Real.norm_eq_abs] using physicalRealTrace_bound i u hM hb
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using norm_integral_le_of_norm_le_const hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WordGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceWordMap_dist (ν : SourceWord) (x y : R3) :
    dist (sourceWordMap ν x) (sourceWordMap ν y)=sourceScale^ν.length*dist x y := by
  induction ν with
  | nil => simp
  | cons k ν ih =>
    simp only [sourceWordMap_cons,sourceChildEuclidean_eq_similarity,sourceSimilarity_dist,ih,List.length_cons,pow_succ]
    ring

lemma sourceWordCell_subset (ν : SourceWord) : sourceWordCell ν⊆closure sourceDomain := sourceWordMap_closed_subset ν

lemma sourceWordBlock_root : sourceWordBlock []=sourceOpenBlock := by
  ext x
  simp [sourceWordBlock,sourceWordMap]

lemma sourceWordBlock_child_iff (k : Fin 2) {x : R3} (hx : x∈closure sourceDomain) (ν : SourceWord) :
    sourceChildEuclidean (actualChildSign k) x∈sourceWordBlock ν ↔
      ∃ ω : SourceWord,ν=k::ω ∧ x∈sourceWordBlock ω := by
  constructor
  · intro hν
    cases ν with
    | nil =>
      rw [sourceWordBlock_root] at hν
      exact (hν.2 (mem_iUnion.mpr ⟨k,by rw [←sourceChildEuclidean_eq_similarity]; exact ⟨x,hx,rfl⟩⟩)).elim
    | cons l ν =>
      have hl : k=l := by
        by_contra hn
        exact Set.disjoint_left.mp (source_child_closed_disjoint hn) ⟨x,hx,rfl⟩
          (sourceWordCell_cons_subset l ν (sourceWordBlock_subset_cell _ hν))
      subst l
      rw [sourceWordBlock_cons] at hν
      exact ⟨ν,rfl,(sourceChildEuclidean (actualChildSign k)).injective.mem_set_image.mp hν⟩
  · rintro ⟨ω,rfl,hω⟩
    rw [sourceWordBlock_cons]
    exact ⟨x,hω,rfl⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CopiedScalarCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma copiedScalarCoefficient_one (b : Coord3 → ℝ) {x : R3}
    (hx : x∉closure sourceDomain) : copiedScalarCoefficient b x=1 := by
  apply copiedScalarCoefficient_outside
  intro ν hν
  exact hx (sourceWordCell_subset ν (sourceWordBlock_subset_cell ν hν))

lemma copiedScalarCoefficient_collar (b : Coord3 → ℝ) :
    EqualOneNearBoundary (copiedScalarCoefficient b) := by
  refine ⟨5/2,by norm_num,by norm_num,Eventually.of_forall ?_⟩
  intro x hx
  apply copiedScalarCoefficient_one
  intro hh
  have hn := sourceClosure_subset_ball hh
  simp only [Metric.mem_ball,dist_zero_right] at hn
  linarith

lemma copiedScalarCoefficient_root (b : Coord3 → ℝ) :
    ∀ᵐ y∂volume.restrict physicalOpenBlock,copiedScalarCoefficient b (WithLp.toLp 2 y)=b y := by
  filter_upwards [ae_restrict_mem (sourceOpenBlock_isOpen.preimage (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))).measurableSet] with y hy
  have hroot : WithLp.toLp 2 y∈sourceWordBlock [] := by
    rw [sourceWordBlock_root]
    exact hy
  exact copiedScalarCoefficient_on b hroot

lemma copiedScalarCoefficient_child (b : Coord3 → ℝ) (k : Fin 2) {x : R3}
    (hx : x∈closure sourceDomain) :
    copiedScalarCoefficient b (sourceChildEuclidean (actualChildSign k) x)=copiedScalarCoefficient b x := by
  by_cases h : ∃ ν : SourceWord,x∈sourceWordBlock ν
  · obtain ⟨ν,hν⟩ := h
    have hc := (sourceWordBlock_child_iff k hx (k::ν)).mpr ⟨ν,rfl,hν⟩
    rw [copiedScalarCoefficient_on b hc,copiedScalarCoefficient_on b hν]
    change b (WithLp.ofLp ((sourceWordMap ν).symm ((sourceChildEuclidean (actualChildSign k)).symm
      (sourceChildEuclidean (actualChildSign k) x))))=_
    rw [Homeomorph.symm_apply_apply]
  · rw [copiedScalarCoefficient_outside b (not_exists.mp h),copiedScalarCoefficient_outside b]
    intro ν hn
    obtain ⟨ω,hω,hxω⟩ := (sourceWordBlock_child_iff k hx ν).mp hn
    exact h ⟨ω,hxω⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma sourceChildEuclidean_inverse_quasi (σ : ℝ) :
    Measure.QuasiMeasurePreserving (sourceChildEuclidean σ).symm volume volume := by
  refine ⟨(sourceChildEuclidean σ).symm.measurable,?_⟩
  rw [sourceChildEuclidean_inverse_map_volume]
  exact Measure.smul_absolutelyContinuous

lemma sourceChild_inverse_ballae (k : Fin 2) {p : R3 → Prop} (hp : ∀ᵐ x∂ballMeasure,p x) :
    ∀ᵐ x∂ballMeasure,(sourceChildEuclidean (actualChildSign k)).symm x∈ball →
      p ((sourceChildEuclidean (actualChildSign k)).symm x) := by
  exact ae_restrict_of_ae ((sourceChildEuclidean_inverse_quasi _).ae
    ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hp))

lemma sourceSupported_iff (u : H1) : SourceSupported u ↔
    ∀ᵐ x∂ballMeasure,x∉closure sourceDomain → weakValue u x=0 ∧ weakGradient u x=0 := by
  constructor
  · intro hu
    filter_upwards [hu] with x hx hn
    change jetValue (u.val x)=0 ∧ jetGradient (u.val x)=0
    rw [hx hn]; exact ⟨map_zero _,map_zero _⟩
  · intro hu
    filter_upwards [hu] with x hx hn
    obtain ⟨hv,hg⟩ := hx hn
    rw [jetFiber_decomposition (u.val x)]
    change jetLiftValue (weakValue u x)+jetLiftGradient (weakGradient u x)=0
    rw [hv,hg,map_zero,map_zero,add_zero]

lemma SourceSupported.add {u v : H1} (hu : SourceSupported u) (hv : SourceSupported v) :
    SourceSupported (u+v) := by
  filter_upwards [hu,hv,Lp.coeFn_add u.val v.val] with x hx hy he hn
  change (u.val+v.val) x=0
  rw [he,Pi.add_apply,hx hn,hy hn,add_zero]

lemma SourceSupported.smul {u : H1} (hu : SourceSupported u) (r : ℝ) :
    SourceSupported (r • u) := by
  filter_upwards [hu,Lp.coeFn_smul r u.val] with x hx he hn
  change (r • u.val) x=0
  rw [he,Pi.smul_apply,hx hn,smul_zero]

lemma childH10Transport_support (k : Fin 2) (u : H10) (hu : SourceSupported u.val) :
    ∀ᵐ x∂ballMeasure,x∉sourceChildEuclidean (actualChildSign k) '' closure sourceDomain →
      (childH10Transport k u).val x=0 := by
  filter_upwards [childH10Transport_jet k u,sourceChild_inverse_ballae k hu] with x hx hs hn
  rw [hx]
  split_ifs with hb
  · have hi : (sourceChildEuclidean (actualChildSign k)).symm x∉closure sourceDomain := by
      intro h
      exact hn ⟨_,h,Homeomorph.apply_symm_apply _ x⟩
    have he := hs hb hi
    have hv := congrArg jetValue he
    have hg := congrArg jetGradient he
    change weakValue u.val ((sourceChildEuclidean (actualChildSign k)).symm x)=0 at hv
    change weakGradient u.val ((sourceChildEuclidean (actualChildSign k)).symm x)=0 at hg
    rw [hv,hg]
    ext i
    cases i using Fin.cases <;> simp
  · rfl

lemma SourceSupported.child (k : Fin 2) {u : H10} (hu : SourceSupported u.val) :
    SourceSupported (childZeroTransport k u).val := by
  filter_upwards [childH10Transport_support k u hu] with x hx hn
  exact hx (fun h => hn (subset_closure (source_child_closed_subset k h)))

lemma childH10Transport_bounded (k : Fin 2) (u : H10) {M : ℝ} (hM : 0≤M)
    (hu : ∀ᵐ x∂ballMeasure,|weakValue u.val x|≤M) :
    ∀ᵐ x∂ballMeasure,|weakValue (childH10Transport k u) x|≤M := by
  filter_upwards [childH10Transport_value k u,sourceChild_inverse_ballae k hu] with x hx hs
  rw [hx]
  split_ifs with hb
  · exact hs hb
  · simpa only [abs_zero] using hM

lemma copied_child_energy (b : Coord3 → ℝ) (k : Fin 2) (v : H10)
    (hv : SourceSupported v.val) (h : H1) :
    (∫ x,copiedScalarCoefficient b x*inner ℝ (weakGradient (childH10Transport k v) x) (weakGradient h x) ∂ballMeasure)=
      sourceScale*(∫ x,copiedScalarCoefficient b x*
        inner ℝ (weakGradient v.val x) (weakGradient (childH1Pullback k h) x) ∂ballMeasure) := by
  rw [child_energy_scaling]
  congr 1
  apply integral_congr_ae
  filter_upwards [(sourceSupported_iff v.val).mp hv] with x hx
  by_cases hd : x∈closure sourceDomain
  · rw [copiedScalarCoefficient_child b k hd]
  · rw [(hx hd).2,inner_zero_left,mul_zero,mul_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_BranchCombine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma source_child_push_inner_zero (v w : H10)
    (hv : SourceSupported v.val) (hw : SourceSupported w.val) :
    inner ℝ (weakGradientL (childZeroTransport 0 v).val)
      (weakGradientL (childZeroTransport 1 w).val)=0 := by
  rw [L2.inner_def]
  apply (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [weakGradientL_apply_ae (childZeroTransport 0 v).val,
    weakGradientL_apply_ae (childZeroTransport 1 w).val,
    childH10Transport_support 0 v hv,childH10Transport_support 1 w hw] with x h0 h1 hs0 hs1
  rw [h0,h1]
  have hd := source_child_closed_disjoint (show (0:Fin 2)≠1 by decide)
  by_cases hx : x∈sourceChildEuclidean (actualChildSign 0) '' closure sourceDomain
  · have hn := Set.disjoint_left.mp hd hx
    have he := congrArg jetGradient (hs1 hn)
    change weakGradient (childZeroTransport 1 w).val x=0 at he
    rw [he,inner_zero_right]
  · have he := congrArg jetGradient (hs0 hx)
    change weakGradient (childZeroTransport 0 v).val x=0 at he
    rw [he,inner_zero_left]

lemma sourceBranchCombine_support {v w : H10} (hv : SourceSupported v.val)
    (hw : SourceSupported w.val) (α β : ℝ) :
    SourceSupported (sourceBranchCombine α β v w).val :=
  ((hv.child 0).smul α).add ((hw.child 1).smul β)

private lemma norm_smul_sq_real {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (x : E) : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma sourceBranchCombine_energy (α β : ℝ) (v w : H10)
    (hv : SourceSupported v.val) (hw : SourceSupported w.val) :
    ‖weakGradientL (sourceBranchCombine α β v w).val‖^2=
      sourceScale*(α^2*‖weakGradientL v.val‖^2+β^2*‖weakGradientL w.val‖^2) := by
  have horth : inner ℝ (α • weakGradientL (childZeroTransport 0 v).val)
      (β • weakGradientL (childZeroTransport 1 w).val) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right,
      source_child_push_inner_zero v w hv hw, mul_zero, mul_zero]
  have hnorm := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  simp only [← pow_two] at hnorm
  change ‖weakGradientL (α • (childZeroTransport 0 v).val+β • (childZeroTransport 1 w).val)‖^2=_
  rw [map_add,map_smul,map_smul,hnorm]
  rw [norm_smul_sq_real, norm_smul_sq_real]
  change α^2*‖weakGradientL (childH10Transport 0 v)‖^2+β^2*‖weakGradientL (childH10Transport 1 w)‖^2=_
  calc
    _ = α^2*(sourceScale*‖weakGradientL v.val‖^2)+β^2*(sourceScale*‖weakGradientL w.val‖^2) :=
      congrArg₂ (fun r t : ℝ => α^2*r+β^2*t) (child_gradient_norm_sq 0 v) (child_gradient_norm_sq 1 w)
    _ = _ := by ring

lemma sourceBranchCombine_bound (α β : ℝ) (v w : H10)
    (hv : SourceSupported v.val) (hw : SourceSupported w.val) {M N : ℝ}
    (hM : 0≤M) (hN : 0≤N)
    (hvM : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x) ≤ M)
    (hwN : ∀ᵐ x∂ballMeasure,abs (weakValue w.val x) ≤ N) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceBranchCombine α β v w).val x) ≤ max (abs α * M) (abs β * N) := by
  filter_upwards [weakValue_add (α • (childZeroTransport 0 v).val) (β • (childZeroTransport 1 w).val),
    weakValue_smul α (childZeroTransport 0 v).val,weakValue_smul β (childZeroTransport 1 w).val,
    childH10Transport_support 0 v hv,childH10Transport_support 1 w hw,
    childH10Transport_bounded 0 v hM hvM,childH10Transport_bounded 1 w hN hwN] with x ha hα hβ hs0 hs1 hb0 hb1
  change abs (weakValue (α • (childZeroTransport 0 v).val+β • (childZeroTransport 1 w).val) x) ≤ _
  rw [ha,Pi.add_apply,hα,hβ,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul]
  by_cases hx : x∈sourceChildEuclidean (actualChildSign 0) '' closure sourceDomain
  · have hn := Set.disjoint_left.mp (source_child_closed_disjoint (show (0:Fin 2)≠1 by decide)) hx
    have he := congrArg jetValue (hs1 hn)
    change weakValue (childZeroTransport 1 w).val x=0 at he
    rw [he,mul_zero,add_zero,abs_mul]
    exact (mul_le_mul_of_nonneg_left hb0 (abs_nonneg α)).trans (le_max_left _ _)
  · have he := congrArg jetValue (hs0 hx)
    change weakValue (childZeroTransport 0 v).val x=0 at he
    rw [he,mul_zero,zero_add,abs_mul]
    exact (mul_le_mul_of_nonneg_left hb1 (abs_nonneg β)).trans (le_max_right _ _)

lemma sourceAveragePush_eq (v : H10) : sourceAveragePush v=sourceBranchCombine sourceRatio sourceRatio v v := by
  change sourceRatio • (childZeroTransport 0 v+childZeroTransport 1 v)=_
  exact smul_add _ _ _

lemma sourceDifferencePush_eq (v : H10) : sourceDifferencePush v=sourceBranchCombine sourceScale⁻¹ (-(sourceScale⁻¹)) v v := by
  change sourceScale⁻¹ • (childZeroTransport 0 v-childZeroTransport 1 v)=_
  change sourceScale⁻¹ • (childZeroTransport 0 v-childZeroTransport 1 v)=sourceScale⁻¹ • childZeroTransport 0 v+(-(sourceScale⁻¹)) • childZeroTransport 1 v
  norm_num [sourceScale]
  module

lemma sourceRatio_pos : 0 < sourceRatio := by norm_num [sourceRatio,sourceScale]
lemma sourceRatio_lt_one : sourceRatio<1 := by norm_num [sourceRatio,sourceScale]

lemma sourceAveragePush_support {v : H10} (hv : SourceSupported v.val) :
    SourceSupported (sourceAveragePush v).val := by
  rw [sourceAveragePush_eq]
  exact sourceBranchCombine_support hv hv _ _

lemma sourceDifferencePush_support {v : H10} (hv : SourceSupported v.val) :
    SourceSupported (sourceDifferencePush v).val := by
  rw [sourceDifferencePush_eq]
  exact sourceBranchCombine_support hv hv _ _

lemma sourceAveragePush_energy {v : H10} (hv : SourceSupported v.val) :
    ‖weakGradientL (sourceAveragePush v).val‖^2=sourceRatio*‖weakGradientL v.val‖^2 := by
  rw [sourceAveragePush_eq,sourceBranchCombine_energy _ _ v v hv hv]
  norm_num [sourceRatio,sourceScale]
  ring

lemma sourceAveragePush_bound {v : H10} (hv : SourceSupported v.val) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x) ≤ M) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceAveragePush v).val x) ≤ sourceRatio*M := by
  rw [sourceAveragePush_eq]
  simpa only [abs_of_pos sourceRatio_pos,max_self] using sourceBranchCombine_bound sourceRatio sourceRatio v v hv hv hM hM hb hb

lemma sourceDifferencePush_bound {v : H10} (hv : SourceSupported v.val) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x) ≤ M) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceDifferencePush v).val x) ≤ sourceScale⁻¹*M := by
  rw [sourceDifferencePush_eq]
  simpa only [abs_neg,abs_of_pos (show 0 < sourceScale⁻¹ by norm_num [sourceScale]),max_self]
    using sourceBranchCombine_bound sourceScale⁻¹ (-(sourceScale⁻¹)) v v hv hv hM hM hb hb

end

open Set MeasureTheory Filter Topology

lemma sourceSupported_zero : SourceSupported (0:H1) := by
  filter_upwards [Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx _
  exact hx

lemma SourceSupported.sum {ι : Type*} (s : Finset ι) (f : ι → H1)
    (hf : ∀ i∈s,SourceSupported (f i)) : SourceSupported (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using sourceSupported_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma sourceSupported_limit {u : ℕ → H1} {w : H1} (hu : Tendsto u atTop (𝓝 w))
    (hs : ∀ n,SourceSupported (u n)) : SourceSupported w := by
  apply h1_limit_ae_closed hu (fun x => {z : JetFiber | x∉closure sourceDomain → z=0}) _ hs
  intro x
  by_cases hx : x∈closure sourceDomain
  · simpa only [hx,not_true_eq_false,false_implies,Set.ofPred_true] using isClosed_univ (X:=JetFiber)
  · simpa only [hx,not_false_eq_true,true_implies] using (isClosed_eq continuous_id continuous_const : IsClosed {z : JetFiber | z = 0})

lemma sourceSupported_collar {u : H1} (hu : SourceSupported u) :
    ∀ᵐ x∂ballMeasure, (5/2:ℝ)<‖x‖ → weakValue u x=0 ∧ weakGradient u x=0 := by
  filter_upwards [(sourceSupported_iff u).mp hu] with x hx hn
  apply hx
  intro hd
  have hd' := sourceClosure_subset_ball hd
  simp only [Metric.mem_ball,dist_zero_right] at hd'
  linarith

lemma sourceAverageIter_support {v : H10} (hv : SourceSupported v.val) (n : ℕ) :
    SourceSupported (sourceAverageIter v n).val := by
  induction n with
  | zero => exact hv
  | succ n ih => exact sourceAveragePush_support ih

lemma sourceAverageIter_energy {v : H10} (hv : SourceSupported v.val) (n : ℕ) :
    ‖weakGradientL (sourceAverageIter v n).val‖^2=sourceRatio^n*‖weakGradientL v.val‖^2 := by
  induction n with
  | zero => simp [sourceAverageIter]
  | succ n ih =>
    change ‖weakGradientL (sourceAveragePush (sourceAverageIter v n)).val‖^2=_
    rw [sourceAveragePush_energy (sourceAverageIter_support hv n),ih,pow_succ]
    ring

lemma sourceAverageIter_bound {v : H10} (hv : SourceSupported v.val) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x)≤M) (n : ℕ) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceAverageIter v n).val x)≤M*sourceRatio^n := by
  induction n with
  | zero => simpa [sourceAverageIter] using hb
  | succ n ih =>
    have hh := sourceAveragePush_bound (sourceAverageIter_support hv n)
      (mul_nonneg hM (pow_nonneg sourceRatio_pos.le n)) ih
    have he : sourceRatio*(M*sourceRatio^n)=M*sourceRatio^(n+1) := by rw [pow_succ]; ring
    simpa only [he,sourceAverageIter] using hh

theorem sourceAverage_series_exists (v : H10) (hv : SourceSupported v.val) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x)≤M) :
    ∃ w : H10,SourceSupported w.val ∧
      Tendsto (fun N => ∑ n∈Finset.range N,sourceAverageIter v n) atTop (𝓝 w) ∧
      (∀ᵐ x∂ballMeasure,abs (weakValue w.val x)≤(M+‖weakGradientL v.val‖^2)/(1-sourceRatio)) := by
  let K := M+‖weakGradientL v.val‖^2
  have hK : 0≤K := add_nonneg hM (sq_nonneg _)
  obtain ⟨w,hw,ht,hb',hs⟩ := geometric_source_series (fun n => (sourceAverageIter v n).val)
    hK sourceRatio_pos.le sourceRatio_lt_one (fun n => (sourceAverageIter v n).property)
    (fun n => (sourceAverageIter_bound hv hM hb n).mono (fun x hx => hx.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (pow_nonneg sourceRatio_pos.le n))))
    (fun n => by rw [sourceAverageIter_energy hv n]; dsimp [K]; nlinarith [pow_nonneg sourceRatio_pos.le n])
    (5/2) (fun n => sourceSupported_collar (sourceAverageIter_support hv n))
  refine ⟨⟨w,hw⟩,sourceSupported_limit ht (fun n => SourceSupported.sum _ _ (fun i _ => sourceAverageIter_support hv i)),?_,hb'⟩
  apply tendsto_subtype_rng.mpr
  simpa only [Submodule.coe_sum] using ht

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevGaugeTransform
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma H1_sub_constant_spec (u : H1) (c : ℝ) :
    (∀ᵐ x ∂ballMeasure, weakValue (u-constantH1 c) x=weakValue u x-c) ∧
    (weakGradient (u-constantH1 c) =ᵐ[ballMeasure] weakGradient u) := by
  constructor
  · filter_upwards [weakValue_sub u (constantH1 c),constantH1_value c] with x hx hy
    simpa only [Pi.sub_apply,hy] using hx
  · filter_upwards [weakGradient_sub u (constantH1 c),constantH1_gradient c] with x hx hy
    simpa only [Pi.sub_apply,hy,Pi.zero_apply,sub_zero] using hx

theorem exists_gauge_transform {u w : H1} {M : ℝ}
    (hu : ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M)
    (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2) (hw0 : w∈H10) (c : ℝ) :
    ∃ v : H1, trace v=trace u ∧
      (∀ᵐ x ∂ballMeasure, weakValue v x=c+(weakValue u x-c)/(1+weakValue w x)) ∧
      (∀ᵐ x ∂ballMeasure, ∀ a : ℝ,
        (a*(1+weakValue w x)^2) • weakGradient v x=
          ((1+weakValue w x)*a) • weakGradient u x-
          ((weakValue u x-c)*a) • weakGradient w x) := by
  let q := inverseOperation.onH1 w
  have hi := inverseOperation_spec hw
  have hs := H1_sub_constant_spec u c
  have huc : ∀ᵐ x ∂ballMeasure, |weakValue (u-constantH1 c) x|≤M+|c| := by
    filter_upwards [hs.1,hu] with x hx hy
    rw [hx]
    exact (abs_sub _ _).trans (add_le_add hy (le_refl _))
  obtain ⟨p,hpv,hpg,hp0⟩ := exists_H1_product huc hi.2.2.1
  have hp : p∈H10 := hp0 (hi.2.2.2 hw0)
  refine ⟨u+p,?_,?_,?_⟩
  · apply (Submodule.Quotient.eq H10).mpr
    simpa only [add_sub_cancel_left] using hp
  · filter_upwards [weakValue_add u p,hpv,hs.1,hi.1,hw] with x hx hp hs hq hw
    rw [hx,Pi.add_apply,hp,hs,hq]
    ring
  · filter_upwards [weakGradient_add u p,hpg,hs.1,hs.2,hi.1,hi.2.1,hw]
      with x hx hp hs hg hq hd hw
    intro a
    rw [hx,Pi.add_apply,hp,hs,hg,hq,hd]
    have hn : (1:ℝ)+weakValue w x≠0 := by have := (abs_le.mp hw).1; linarith
    ext i
    change (a*(1+weakValue w x)^2)*((weakGradient u x) i+
      ((weakValue u x-c)*(-((1+weakValue w x)^2)⁻¹*(weakGradient w x) i)+
      ((1+weakValue w x)⁻¹-1)*(weakGradient u x) i))=_
    change _ = ((1+weakValue w x)*a)*(weakGradient u x) i-
      ((weakValue u x-c)*a)*(weakGradient w x) i
    field_simp [hn]
    ring

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma gaugeCoefficient_aeStronglyMeasurable (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (w : H1) :
    AEStronglyMeasurable (gaugeCoefficient a w) ballMeasure :=
  ha.mul ((aestronglyMeasurable_const.add
    (jetValue.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.val))).pow 2)

lemma gaugeCoefficient_bounds {a : R3 → ℝ} {w : H1} {c C : ℝ}
    (hc : 0 < c) (ha : ∀ᵐ x ∂ballMeasure, c≤a x ∧ a x≤C)
    (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2) :
    ∀ᵐ x ∂ballMeasure, c/4≤gaugeCoefficient a w x ∧ gaugeCoefficient a w x≤9*C/4 := by
  filter_upwards [ha,hw] with x hx hy
  have hlo := (abs_le.mp hy).1
  have hup := (abs_le.mp hy).2
  have hp : 0≤a x := le_trans hc.le hx.1
  have hrlo : (1/4:ℝ)≤(1+weakValue w x)^2 := by nlinarith
  have hrup : (1+weakValue w x)^2≤(9/4:ℝ) := by nlinarith
  constructor
  · change c/4≤a x*(1+weakValue w x)^2
    calc
      _ = c*(1/4:ℝ) := by ring
      _ ≤ a x*(1/4:ℝ) := mul_le_mul_of_nonneg_right hx.1 (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hrlo hp
  · change a x*(1+weakValue w x)^2≤9*C/4
    calc
      _ ≤ a x*(9/4:ℝ) := mul_le_mul_of_nonneg_left hrup hp
      _ ≤ C*(9/4:ℝ) := mul_le_mul_of_nonneg_right hx.2 (by norm_num)
      _ = _ := by ring

lemma gauge_test_integrand (a r U c F : ℝ) (du dw dF : R3) :
    inner ℝ ((r*a) • du-((U-c)*a) • dw) dF =
      a*inner ℝ du (dF+(r-1) • dF+F • dw)-
      a*inner ℝ dw ((U-c) • dF+F • du) := by
  simp only [inner_sub_left,real_inner_smul_left,inner_add_right,real_inner_smul_right]
  rw [real_inner_comm dw du]
  ring

theorem gauge_harmonic_of_weighted (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    {u w v : H1} {M : ℝ} (hu : ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M)
    (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2)
    (huh : Harmonic a u) (c : ℝ) (hweighted : WeightedAnnihilation a w u c)
    (hflux : ∀ᵐ x ∂ballMeasure,
      gaugeCoefficient a w x • weakGradient v x=
      ((1+weakValue w x)*a x) • weakGradient u x-
        ((weakValue u x-c)*a x) • weakGradient w x) :
    Harmonic (gaugeCoefficient a w) v := by
  have hgb : ∀ᵐ x ∂ballMeasure, |gaugeCoefficient a w x|≤C*(9/4:ℝ) := by
    filter_upwards [hb,hw] with x hx hy
    have hsq : (1+weakValue w x)^2≤(9/4:ℝ) := by
      have hl := (abs_le.mp hy).1; have hu := (abs_le.mp hy).2; nlinarith
    rw [gaugeCoefficient,abs_mul,abs_of_nonneg (sq_nonneg (1+weakValue w x))]
    exact mul_le_mul hx hsq (sq_nonneg _) hC
  apply harmonic_of_compact_tests _ (gaugeCoefficient_aeStronglyMeasurable a ha w)
    (C*(9/4:ℝ)) (mul_nonneg hC (by norm_num)) hgb v
  intro f hf hfc hfs
  let φ := smoothH1 f hf
  obtain ⟨N,hN,hφ⟩ := smoothH1_bounded f hf
  have hφ0 : φ∈H10 := smoothH1_mem_H10 f hf hfc hfs
  have hs := H1_sub_constant_spec u c
  have huc : ∀ᵐ x ∂ballMeasure, |weakValue (u-constantH1 c) x|≤M+|c| := by
    filter_upwards [hu,hs.1] with x hx hy
    rw [hy]; exact (abs_sub _ _).trans (add_le_add hx (le_refl _))
  obtain ⟨p₁,_,hp₁,hp₁0⟩ := exists_H1_product hw hφ
  obtain ⟨p₂,_,hp₂,_⟩ := exists_H1_product huc hφ
  have hρφ : φ+p₁∈H10 := H10.add_mem hφ0 (hp₁0 hφ0)
  have he₁ : energy a u (φ+p₁)=0 := huh _ hρφ
  have he₂ : energy a w p₂=0 := by
    calc
      _ = ∫ x, a x*inner ℝ (weakGradient w x)
        ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure := by
          apply integral_congr_ae
          filter_upwards [hp₂,hs.1,hs.2,smoothH1_value f hf,smoothH1_gradient f hf]
            with x hx hy hz hv hg
          rw [hx,hy,hz,hv,hg]
      _ = 0 := hweighted f hf hfc hfs
  have he : energy (gaugeCoefficient a w) v φ=energy a u (φ+p₁)-energy a w p₂ := by
    unfold energy
    rw [←integral_sub (energy_integrable a ha C hC hb u (φ+p₁))
      (energy_integrable a ha C hC hb w p₂)]
    apply integral_congr_ae
    filter_upwards [hflux,hp₁,hp₂,hs.1,hs.2,weakGradient_add φ p₁]
      with x hx h₁ h₂ hv hg ha
    rw [←real_inner_smul_left,hx,ha,Pi.add_apply,h₁,h₂,hv,hg]
    convert gauge_test_integrand (a x) (1+weakValue w x) (weakValue u x) c
      (weakValue φ x) (weakGradient u x) (weakGradient w x) (weakGradient φ x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [add_sub_cancel_left,add_assoc,φ]
  rw [he,he₁,he₂,sub_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CopiedEnergyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

namespace BoundedRootSources
variable (r : BoundedRootSources)
lemma form_apply (v h : H1) : r.form v h=energy r.coefficient v h := energyForm_apply _ _ _ _ _ _ _
lemma form_symm (v h : H1) : r.form v h=r.form h v := by
  simp only [form_apply,energy,real_inner_comm]
lemma root_support (j : Fin 2) : SourceSupported (r.W j) :=
  (sourceSupported_iff _).mpr (r.W_support j)
lemma form_root (j : Fin 2) (h : H1) :
    r.form (r.root j).val h=angularArea*(sourceMeanCLM j.succ h-sourceMeanCLM 0 h) := by
  rw [form_apply]
  exact (r.green r.coefficient (copiedScalarCoefficient_root r.b) j h).trans (basisFlux_mean j h)
lemma form_child (k : Fin 2) (v : H10) (hv : SourceSupported v.val) (h : H1) :
    r.form (childZeroTransport k v).val h=sourceScale*r.form v.val (childH1Pullback k h) := by
  rw [form_apply,form_apply]
  exact copied_child_energy r.b k v hv h
lemma form_average (v : H10) (hv : SourceSupported v.val) (h : H1) :
    r.form (sourceAveragePush v).val h=r.form v.val (sourceAveragePull h) := by
  rw [sourceAveragePush_eq]
  change r.form (sourceRatio • (childZeroTransport 0 v).val+sourceRatio • (childZeroTransport 1 v).val) h=_
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [r.form_child 0 v hv h,r.form_child 1 v hv h]
  change _=r.form v.val ((1/2:ℝ) • (childH1Pullback 0 h+childH1Pullback 1 h))
  rw [map_smul,map_add]
  simp only [smul_eq_mul]
  norm_num [sourceRatio,sourceScale]
  ring
lemma form_difference (v : H10) (hv : SourceSupported v.val) (h : H1) :
    r.form (sourceDifferencePush v).val h=r.form v.val (sourceDifferencePull h) := by
  rw [sourceDifferencePush_eq]
  change r.form (sourceScale⁻¹ • (childZeroTransport 0 v).val+(-(sourceScale⁻¹)) • (childZeroTransport 1 v).val) h=_
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [r.form_child 0 v hv h,r.form_child 1 v hv h]
  change _=r.form v.val (childH1Pullback 0 h-childH1Pullback 1 h)
  rw [map_sub]
  norm_num [sourceScale]
  ring

lemma harmonic_sourceHarmonic {u : H1} (hu : Harmonic r.coefficient u) : r.sourceHarmonic u := by
  intro v _
  rw [r.form_symm,r.form_apply]
  exact hu v.val v.property
lemma sourceHarmonic_child {u : H1} (hu : r.sourceHarmonic u) (k : Fin 2) :
    r.sourceHarmonic (childH1Pullback k u) := by
  intro v hv
  have he := hu (childZeroTransport k v) (hv.child k)
  rw [r.form_child k v hv] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num [sourceScale])
lemma sourceHarmonic_mean {u : H1} (hu : r.sourceHarmonic u) (k : Fin 2) :
    sourceMeanCLM 0 (childH1Pullback k u)=sourceMeanCLM 0 u := by
  have he := hu (r.root k) (r.root_support k)
  rw [r.form_root,sourceMean_child] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (by dsimp [angularArea]; positivity : angularArea≠0))

end BoundedRootSources
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma weakValue_bound_add {u v : H1} {M N : ℝ}
    (hu : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M)
    (hv : ∀ᵐ x∂ballMeasure,abs (weakValue v x) ≤ N) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (u+v) x) ≤ M+N := by
  filter_upwards [weakValue_add u v,hu,hv] with x he hu hv
  rw [he,Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add hu hv)

lemma weakValue_bound_smul {u : H1} {M : ℝ}
    (hu : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) (a : ℝ) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (a • u) x) ≤ abs a*M := by
  filter_upwards [weakValue_smul a u,hu] with x he hu
  rw [he,Pi.smul_apply,smul_eq_mul,abs_mul]
  exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)

lemma sourceAveragePullIter_succ (n : ℕ) (h : H1) :
    sourceAveragePullIter (n+1) h=sourceAveragePull (sourceAveragePullIter n h) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change sourceAveragePullIter (n+1) (sourceAveragePull h)=sourceAveragePull (sourceAveragePullIter (n+1) h)
    rw [ih]
    rfl

namespace BoundedRootSources
variable (r : BoundedRootSources)

lemma seed_support : SourceSupported r.seed.val :=
  ((r.root_support 0).add (r.root_support 1)).smul _
lemma initial_support : SourceSupported r.initial.val := by
  change SourceSupported (angularArea⁻¹ • ((r.root 0).val-(r.root 1).val))
  rw [sub_eq_add_neg,←neg_one_smul ℝ (r.root 1).val]
  exact ((r.root_support 0).add ((r.root_support 1).smul (-1))).smul _

lemma seed_bounded : ∃ M : ℝ,0 ≤ M ∧ ∀ᵐ x∂ballMeasure,abs (weakValue r.seed.val x) ≤ M := by
  have hK : 0 < r.K := r.K_pos
  refine ⟨abs (1/(2*angularArea))*(r.K+r.K),by positivity,?_⟩
  exact weakValue_bound_smul (weakValue_bound_add (r.W_bound 0) (r.W_bound 1)) _
lemma initial_bounded : ∃ M : ℝ,0 ≤ M ∧ ∀ᵐ x∂ballMeasure,abs (weakValue r.initial.val x) ≤ M := by
  have hK : 0 < r.K := r.K_pos
  refine ⟨abs (angularArea⁻¹)*(r.K+abs (-1:ℝ)*r.K),by positivity,?_⟩
  change ∀ᵐ x∂ballMeasure,abs (weakValue (angularArea⁻¹ • (r.W 0-r.W 1)) x) ≤ _
  rw [sub_eq_add_neg,←neg_one_smul ℝ (r.W 1)]
  exact weakValue_bound_smul (weakValue_bound_add (r.W_bound 0) (weakValue_bound_smul (r.W_bound 1) (-1))) _

lemma form_seed (h : H1) :
    r.form r.seed.val h=sourceMeanCLM 0 (sourceAveragePull h)-sourceMeanCLM 0 h := by
  change r.form ((1/(2*angularArea)) • ((r.root 0).val+(r.root 1).val)) h=_
  simp only [map_smul,map_add,smul_apply,add_apply,smul_eq_mul]
  rw [r.form_root,r.form_root,sourceMean_child,sourceMean_child]
  change _=sourceMeanCLM 0 ((1/2:ℝ) • (childH1Pullback 0 h+childH1Pullback 1 h))-sourceMeanCLM 0 h
  rw [map_smul,map_add]
  simp only [smul_eq_mul]
  have hA : angularArea≠0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le angularArea_ge_one)
  field_simp
  ring

lemma form_initial (h : H1) :
    r.form r.initial.val h=sourceMeanCLM 0 (sourceDifferencePull h) := by
  change r.form (angularArea⁻¹ • ((r.root 0).val-(r.root 1).val)) h=_
  simp only [map_smul,map_sub,smul_apply,sub_apply,smul_eq_mul]
  rw [r.form_root,r.form_root,sourceMean_child,sourceMean_child]
  change _=sourceMeanCLM 0 (childH1Pullback 0 h-childH1Pullback 1 h)
  rw [map_sub]
  have hA : angularArea≠0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le angularArea_ge_one)
  field_simp
  ring

lemma form_averageIter (v : H10) (hv : SourceSupported v.val) (n : ℕ) (h : H1) :
    r.form (sourceAverageIter v n).val h=r.form v.val (sourceAveragePullIter n h) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change r.form (sourceAveragePush (sourceAverageIter v n)).val h=_
    rw [r.form_average _ (sourceAverageIter_support hv n),ih]
    rfl

lemma form_finiteSource (N : ℕ) (h : H1) :
    r.form (r.finiteSource N).val h=sourceMeanCLM 0 (sourceAveragePullIter N (sourceDifferencePull h)) := by
  induction N with
  | zero =>
    change r.form (r.initial+sourceDifferencePush (∑ n∈Finset.range 0,sourceAverageIter r.seed n)).val h=_
    simpa only [Finset.range_zero,Finset.sum_empty,map_zero,add_zero,sourceAveragePullIter,ContinuousLinearMap.id_apply] using r.form_initial h
  | succ N ih =>
    have he : r.finiteSource (N+1)=r.finiteSource N+sourceDifferencePush (sourceAverageIter r.seed N) := by
      simp only [finiteSource,Finset.sum_range_succ,map_add,add_assoc]
    rw [he]
    change r.form ((r.finiteSource N).val+(sourceDifferencePush (sourceAverageIter r.seed N)).val) h=_
    rw [map_add,add_apply,ih,r.form_difference _ (sourceAverageIter_support r.seed_support N),
      r.form_averageIter r.seed r.seed_support N,r.form_seed,sourceAveragePullIter_succ]
    ring

theorem nested_source_limit_exists : ∃ w : H10,SourceSupported w.val ∧
    (∃ M : ℝ,0<M ∧ ∀ᵐ x∂ballMeasure,abs (weakValue w.val x) ≤ M) ∧
    Tendsto (fun N => (r.finiteSource N).val) atTop (𝓝 w.val) := by
  obtain ⟨M,hM,hb⟩ := r.seed_bounded
  obtain ⟨v,hv,ht,hvb⟩ := sourceAverage_series_exists r.seed r.seed_support hM hb
  let w : H10 := r.initial+sourceDifferencePush v
  have hw : SourceSupported w.val := r.initial_support.add (sourceDifferencePush_support hv)
  obtain ⟨P,hP,hPb⟩ := r.initial_bounded
  let Q := (M+‖weakGradientL r.seed.val‖^2)/(1-sourceRatio)
  have hQ : 0 ≤ Q := div_nonneg (add_nonneg hM (sq_nonneg _)) (sub_nonneg.mpr sourceRatio_lt_one.le)
  have hDb := sourceDifferencePush_bound hv hQ hvb
  have hs : 0 < sourceScale := by norm_num [sourceScale]
  refine ⟨w,hw,⟨P+sourceScale⁻¹*Q+1,by positivity,?_⟩,?_⟩
  · exact (weakValue_bound_add hPb hDb).mono (fun x hx => hx.trans (by linarith))
  · have : ContinuousAdd H10 := inferInstance
    have htw : Tendsto (fun N => r.finiteSource N) atTop (𝓝 w) :=
      (tendsto_const_nhds (x := r.initial)).add ((sourceDifferencePush.continuous.continuousAt.tendsto).comp ht)
    exact continuous_subtype_val.continuousAt.tendsto.comp htw

end BoundedRootSources
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_OriginalMultiplierOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {χ : R3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

lemma originalMulH1_smooth {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    originalMulH1CLM hχ hc (smoothH1 f hf)=smoothH1 (χ*f) (hχ.mul hf) :=
  Subtype.ext (originalMulJetCLM_smooth hχ hc hf)

lemma originalMulH1_gradient (u : H1) :
    weakGradient (originalMulH1CLM hχ hc u)=ᵐ[ballMeasure]
      (fun x => weakValue u x • gradient χ x+χ x • weakGradient u x) := by
  filter_upwards [originalMulJetCLM_ae hχ hc u] with x hx
  change jetGradient (originalMulJetCLM hχ hc u x)=_
  rw [hx]
  ext j
  change fderiv ℝ χ x (EuclideanSpace.single j 1)*weakValue u x+χ x*weakGradient u x j=
    weakValue u x*gradient χ x j+χ x*weakGradient u x j
  rw [gradient_apply_single]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_NestedWeightedLimit
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma surface_cancellation_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (t f : α → ℝ) (d M ε : ℝ)
    (hM : 0≤M) (hε : 0≤ε) (ht : Integrable t μ)
    (htf : Integrable (fun x => t x*f x) μ) (hz : (∫ x,t x ∂μ)=0)
    (hb : ∀ᵐ x ∂μ,|t x|≤M) (ho : ∀ᵐ x ∂μ,|f x-d|≤ε) :
    |∫ x,t x*f x ∂μ|≤M*ε := by
  have he : (∫ x,t x*f x ∂μ)=(∫ x,t x*(f x-d) ∂μ) := by
    simp_rw [mul_sub]
    rw [integral_sub htf (ht.mul_const d),integral_mul_const,hz,zero_mul,sub_zero]
  rw [he]
  have hb' : ∀ᵐ x ∂μ,‖t x*(f x-d)‖≤|M| * |ε| := by
    filter_upwards [hb,ho] with x hx hy
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hx.trans (le_abs_self M)) (hy.trans (le_abs_self ε))
      (abs_nonneg _) (abs_nonneg _)
  simpa [abs_of_nonneg hM,abs_of_nonneg hε] using norm_integral_le_of_norm_le_const hb'

lemma weighted_integral_tendsto (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ x ∂ballMeasure,|a x|≤C) {W : ℕ → H1} {w u : H1}
    (hW : Tendsto W atTop (𝓝 w)) {M : ℝ}
    (hu : ∀ᵐ x ∂ballMeasure,|weakValue u x|≤M) (c : ℝ)
    (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    Tendsto (fun n => ∫ x,a x*inner ℝ (weakGradient (W n) x)
      ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure)
      atTop (𝓝 (∫ x,a x*inner ℝ (weakGradient w x)
      ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure)) := by
  let φ := smoothH1 f hf
  obtain ⟨N,hN,hφ⟩ := smoothH1_bounded f hf
  have hs := H1_sub_constant_spec u c
  have huc : ∀ᵐ x ∂ballMeasure,|weakValue (u-constantH1 c) x|≤M+|c| := by
    filter_upwards [hu,hs.1] with x hx hy
    rw [hy]
    exact (abs_sub _ _).trans (add_le_add hx (le_refl _))
  obtain ⟨p,_,hp,_⟩ := exists_H1_product huc hφ
  have he (z : H1) : energy a z p=∫ x,a x*inner ℝ (weakGradient z x)
      ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure := by
    apply integral_congr_ae
    filter_upwards [hp,hs.1,hs.2,smoothH1_value f hf,smoothH1_gradient f hf]
      with x hx hy hz hv hg
    rw [hx,hy,hz,hv,hg]
  simpa only [he] using source_energy_limit a ha hC hb hW p

theorem weighted_annihilation_of_geometric_error (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ x ∂ballMeasure,|a x|≤C) {W : ℕ → H1} {w u : H1}
    (hW : Tendsto W atTop (𝓝 w)) {M : ℝ}
    (hu : ∀ᵐ x ∂ballMeasure,|weakValue u x|≤M) (c s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hfinite : ∀ (f : R3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f →
      HasCompactSupport f → tsupport f⊆ball → ∃ K : ℝ,∀ N,
        |∫ x,a x*inner ℝ (weakGradient (W N) x)
          ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure|≤K*s^N) :
    WeightedAnnihilation a w u c := by
  intro f hf hfc hfs
  obtain ⟨K,hK⟩ := hfinite f hf hfc hfs
  have ht₀ : Tendsto (fun N : ℕ => K*s^N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).const_mul K
  have ht := squeeze_zero (fun N => abs_nonneg _ ) hK ht₀
  have hlim := (weighted_integral_tendsto a ha C hC hb hW hu c f hf).abs
  exact abs_eq_zero.mp (tendsto_nhds_unique hlim ht)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma compact_smooth_lipschitz_bound (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f) :
    ∃ L : ℝ,0≤L ∧ ∀ x y,|f x-f y|≤L*dist x y := by
  obtain ⟨L,hL⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m:=0) (by simp)).continuous
  have hL₀ : 0≤L := (norm_nonneg _).trans (hL 0)
  have hlip : LipschitzWith ⟨L,hL₀⟩ f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by simp)) (fun x => hL x)
  refine ⟨L,hL₀,?_⟩
  intro x y
  have hh := hlip.dist_le_mul x y
  change dist (f x) (f y) ≤ L*dist x y at hh
  simpa only [Real.dist_eq] using hh

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WordTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourceWordPull_smooth (ν : SourceWord) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    sourceWordPull ν (smoothH1 f hf)=smoothH1 (f ∘ sourceWordMap ν) (hf.comp (sourceWordMap_contDiff ν)) := by
  induction ν generalizing f with
  | nil => rfl
  | cons k ν ih =>
    change sourceWordPull ν (childH1Pullback k (smoothH1 f hf))=_
    rw [childH1Pullback_smooth,ih]
    rfl

lemma childH1Pullback_bound (k : Fin 2) (u : H1) {M : ℝ}
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (childH1Pullback k u) x) ≤ M := by
  filter_upwards [childH1Pullback_value k u,(sourceChildEuclidean_ball_quasi k).ae hb] with x hx hy
  rw [hx]; exact hy

lemma sourceWordPull_bound (ν : SourceWord) (u : H1) {M : ℝ}
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceWordPull ν u) x) ≤ M := by
  induction ν generalizing u with
  | nil => exact hb
  | cons k ν ih => exact ih _ (childH1Pullback_bound k u hb)

lemma sourceWordBoundary_continuous (ν : SourceWord) : Continuous (sourceWordBoundary ν) :=
  (sourceWordMap ν).continuous.comp ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (physicalOuterBoundary_continuous 0))

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_13
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_13_rcea606_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma sourceWordTrace_smooth (ν : SourceWord) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    sourceWordTraceCLM ν (smoothH1 f hf)=ᵐ[volume] (fun θ => f (sourceWordBoundary ν θ)) := by
  change physicalRealTraceCLM 0 (sourceWordPull ν (smoothH1 f hf))=ᵐ[volume] _
  rw [sourceWordPull_smooth]
  exact physicalRealTrace_smooth_ae 0 (hf.comp (sourceWordMap_contDiff ν))

lemma sourceWordTrace_mul (ν : SourceWord) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f) (u : H1) :
    sourceWordTraceCLM ν (originalMulH1CLM hf hc u)=ᵐ[volume]
      (fun θ => f (sourceWordBoundary ν θ)*sourceWordTraceCLM ν u θ) := by
  let χ : UnitAddTorus (Fin 2) → ℝ := f ∘ sourceWordBoundary ν
  have hχ : Continuous χ := hf.continuous.comp (sourceWordBoundary_continuous ν)
  have hχc : HasCompactSupport χ := HasCompactSupport.of_compactSpace _
  have he : sourceWordTraceCLM ν (originalMulH1CLM hf hc u)=
      compactMultiplierCLM hχ hχc (sourceWordTraceCLM ν u) := by
    have hclosed : IsClosed {u : H1 | sourceWordTraceCLM ν (originalMulH1CLM hf hc u)=
        compactMultiplierCLM hχ hχc (sourceWordTraceCLM ν u)} :=
      isClosed_eq ((sourceWordTraceCLM ν).continuous.comp (originalMulH1CLM hf hc).continuous)
        ((compactMultiplierCLM hχ hχc).continuous.comp (sourceWordTraceCLM ν).continuous)
    apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hclosed) (smoothH1_dense u)
    rintro v ⟨g,hg,_,hv⟩
    have he : v=smoothH1 g hg := Subtype.ext hv
    change sourceWordTraceCLM ν (originalMulH1CLM hf hc v)=_
    rw [he,originalMulH1_smooth]
    apply Lp.ext
    filter_upwards [sourceWordTrace_smooth ν (hf.mul hg),sourceWordTrace_smooth ν hg,
      compactMultiplierCLM_ae hχ hχc (sourceWordTraceCLM ν (smoothH1 g hg))] with θ h0 h1 h2
    exact h0.trans (by rw [h2,h1]; rfl)
  rw [he]
  exact compactMultiplierCLM_ae hχ hχc (sourceWordTraceCLM ν u)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_14
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_14 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma constantH1_eq_smooth (c : ℝ) : constantH1 c=smoothH1 (fun _ => c) contDiff_const := by
  apply H1_eq_of_value_ae
  exact (constantH1_value c).trans (smoothH1_value _ contDiff_const).symm

lemma sourceWordTrace_constant (ν : SourceWord) (c : ℝ) :
    sourceWordTraceCLM ν (constantH1 c)=ᵐ[volume] (fun _ => c) := by
  rw [constantH1_eq_smooth]
  exact sourceWordTrace_smooth ν contDiff_const

lemma sourceWordMean_constant (ν : SourceWord) (c : ℝ) :
    sourceMeanCLM 0 (sourceWordPull ν (constantH1 c))=c := by
  rw [sourceMean_eq_integral]
  change (∫ θ,sourceWordTraceCLM ν (constantH1 c) θ)=c
  rw [integral_congr_ae (sourceWordTrace_constant ν c)]
  simp

namespace BoundedRootSources
variable (r : BoundedRootSources)

lemma sourceHarmonic_word_mean {u : H1} (hu : r.sourceHarmonic u) (ν : SourceWord) :
    sourceMeanCLM 0 (sourceWordPull ν u)=sourceMeanCLM 0 u := by
  induction ν generalizing u with
  | nil => rfl
  | cons k ν ih =>
    change sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback k u))=_
    rw [ih (r.sourceHarmonic_child hu k),r.sourceHarmonic_mean hu k]

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_14
lemma sourceHarmonic_trace_centered_mean {u : H1} (hu : r.sourceHarmonic u) (ν : SourceWord) :
    (∫ θ,sourceWordTraceCLM ν (u-constantH1 (sourceMeanCLM 0 u)) θ)=0 := by
  change (∫ θ,physicalRealTraceCLM 0 (sourceWordPull ν (u-constantH1 (sourceMeanCLM 0 u))) θ)=0
  rw [←sourceMean_eq_integral,map_sub,map_sub,r.sourceHarmonic_word_mean hu ν,sourceWordMean_constant,sub_self]
end BoundedRootSources

lemma sourceWordBoundary_radius : ∃ D : ℝ,0 ≤ D ∧ ∀ ν θ,
    dist (sourceWordBoundary ν θ) (sourceWordMap ν 0) ≤ D*sourceScale^ν.length := by
  let f : UnitAddTorus (Fin 2) → ℝ := fun θ => dist (sourceWordBoundary [] θ) 0
  have hf : Continuous f := (sourceWordBoundary_continuous []).dist continuous_const
  obtain ⟨D,hD⟩ := (HasCompactSupport.of_compactSpace f).exists_bound_of_continuous hf
  have hD0 : 0 ≤ D := (norm_nonneg (f 0)).trans (hD 0)
  refine ⟨D,hD0,?_⟩
  intro ν θ
  change dist (sourceWordMap ν (WithLp.toLp 2 (physicalOuterBoundary 0 θ))) (sourceWordMap ν 0) ≤ _
  rw [sourceWordMap_dist]
  have hh : dist (WithLp.toLp 2 (physicalOuterBoundary 0 θ)) 0 ≤ D := by
    simpa only [f,sourceWordBoundary,sourceWordMap_nil,Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using hD θ
  nlinarith [pow_nonneg (show 0 ≤ sourceScale by norm_num [sourceScale]) ν.length]

lemma sourceWord_weighted_mean_bound (r : BoundedRootSources) {u : H1}
    (hu : r.sourceHarmonic u) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M)
    {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f)
    {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hlip : ∀ x y,abs (f x-f y) ≤ L*dist x y)
    (hdiam : ∀ ν θ,dist (sourceWordBoundary ν θ) (sourceWordMap ν 0) ≤ D*sourceScale^ν.length)
    (ν : SourceWord) :
    abs (sourceMeanCLM 0 (sourceWordPull ν
      (originalMulH1CLM hf hc (u-constantH1 (sourceMeanCLM 0 u))))) ≤
        (2*M*L*D)*sourceScale^ν.length := by
  let v := u-constantH1 (sourceMeanCLM 0 u)
  have hv : ∀ᵐ x∂ballMeasure,abs (weakValue v x) ≤ 2*M := by
    filter_upwards [hb,(H1_sub_constant_spec u (sourceMeanCLM 0 u)).1] with x hx he
    change abs (weakValue (u-constantH1 (sourceMeanCLM 0 u)) x) ≤ _
    rw [he]
    have hm := sourceMean_bound 0 u hM hb
    exact (abs_sub _ _).trans (by linarith)
  let t := sourceWordTraceCLM ν v
  have ht : Integrable t := (Lp.memLp t).integrable (by norm_num)
  have htb : ∀ᵐ θ,abs (t θ) ≤ 2*M := physicalRealTrace_bound 0 (sourceWordPull ν v)
    (by positivity) (sourceWordPull_bound ν v hv)
  have hz : (∫ θ,t θ)=0 := r.sourceHarmonic_trace_centered_mean hu ν
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hf.continuous
  have htf : Integrable (fun θ => t θ*f (sourceWordBoundary ν θ)) :=
    ht.mul_bdd (hf.continuous.comp (sourceWordBoundary_continuous ν)).aestronglyMeasurable
      (Eventually.of_forall (fun θ => hA (sourceWordBoundary ν θ)))
  have ho : ∀ᵐ θ,abs (f (sourceWordBoundary ν θ)-f (sourceWordMap ν 0)) ≤ L*(D*sourceScale^ν.length) :=
    Eventually.of_forall (fun θ => (hlip _ _).trans (mul_le_mul_of_nonneg_left (hdiam ν θ) hL))
  have hh := surface_cancellation_bound volume t (f ∘ sourceWordBoundary ν)
    (f (sourceWordMap ν 0)) (2*M) (L*(D*sourceScale^ν.length)) (by positivity)
    (mul_nonneg hL (mul_nonneg hD (pow_nonneg (by norm_num [sourceScale]) _))) ht htf hz htb ho
  rw [sourceMean_eq_integral]
  change abs (∫ θ,sourceWordTraceCLM ν (originalMulH1CLM hf hc v) θ) ≤ _
  rw [integral_congr_ae (sourceWordTrace_mul ν hf hc v)]
  have he : (∫ θ,f (sourceWordBoundary ν θ)*t θ)=(∫ θ,t θ*f (sourceWordBoundary ν θ)) := by
    congr 1; funext θ; ring
  rw [he]
  exact hh.trans_eq (by ring)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_IteratedAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceAveragePullIter_mean_bound (N : ℕ) (h : H1) (c K : ℝ)
    (hm : ∀ ν : SourceWord,ν.length=N →
      abs (sourceMeanCLM 0 (sourceWordPull ν h)-c) ≤ K) :
    abs (sourceMeanCLM 0 (sourceAveragePullIter N h)-c) ≤ K := by
  induction N generalizing h with
  | zero => exact hm [] rfl
  | succ N ih =>
    change abs (sourceMeanCLM 0 (sourceAveragePullIter N (sourceAveragePull h))-c) ≤ K
    apply ih
    intro ν hν
    have h0 := abs_le.mp (hm (0::ν) (by simp only [List.length_cons,hν]))
    have h1 := abs_le.mp (hm (1::ν) (by simp only [List.length_cons,hν]))
    change abs (sourceMeanCLM 0 (sourceWordPull ν ((1/2:ℝ) • (childH1Pullback 0 h+childH1Pullback 1 h)))-c) ≤ K
    simp only [map_smul,map_add,smul_eq_mul]
    simp only [sourceWordPull,ContinuousLinearMap.comp_apply] at h0 h1
    apply abs_le.mpr
    constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

lemma sourceAveragePullIter_mean_eq (N : ℕ) (h : H1) (c : ℝ)
    (hm : ∀ ν : SourceWord,ν.length=N → sourceMeanCLM 0 (sourceWordPull ν h)=c) :
    sourceMeanCLM 0 (sourceAveragePullIter N h)=c := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply sourceAveragePullIter_mean_bound N h c 0
  intro ν hν
  rw [hm ν hν,sub_self,abs_zero]

lemma sourceAverageDifference_mean_bound (N : ℕ) (h : H1) (K : ℝ)
    (hm : ∀ ν : SourceWord,ν.length=N+1 → abs (sourceMeanCLM 0 (sourceWordPull ν h)) ≤ K) :
    abs (sourceMeanCLM 0 (sourceAveragePullIter N (sourceDifferencePull h))) ≤ 2*K := by
  have hh := sourceAveragePullIter_mean_bound N (sourceDifferencePull h) 0 (2*K) (by
    intro ν hν
    change abs (sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback 0 h-childH1Pullback 1 h))-0) ≤ _
    rw [map_sub,map_sub,sub_zero]
    have h0 := hm (0::ν) (by simp only [List.length_cons,hν])
    have h1 := hm (1::ν) (by simp only [List.length_cons,hν])
    simp only [sourceWordPull,ContinuousLinearMap.comp_apply] at h0 h1
    exact (abs_sub _ _).trans (by linarith))
  simpa only [sub_zero] using hh

namespace BoundedRootSources
variable (r : BoundedRootSources)

lemma finiteSource_weighted_bound {u : H1} (hu : r.sourceHarmonic u) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M)
    {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f)
    {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hlip : ∀ x y,abs (f x-f y) ≤ L*dist x y)
    (hdiam : ∀ ν θ,dist (sourceWordBoundary ν θ) (sourceWordMap ν 0) ≤ D*sourceScale^ν.length)
    (N : ℕ) :
    abs (r.form (r.finiteSource N).val
      (originalMulH1CLM hf hc (u-constantH1 (sourceMeanCLM 0 u)))) ≤
        (4*M*L*D)*sourceScale^N := by
  rw [r.form_finiteSource]
  have hh := sourceAverageDifference_mean_bound N
    (originalMulH1CLM hf hc (u-constantH1 (sourceMeanCLM 0 u)))
    ((2*M*L*D)*sourceScale^(N+1)) (by
      intro ν hν
      simpa only [hν] using sourceWord_weighted_mean_bound r hu hM hb hf hc hL hD hlip hdiam ν)
  apply hh.trans
  rw [pow_succ]
  have hs : sourceScale ≤ 1 := by norm_num [sourceScale]
  have hs0 : 0 ≤ sourceScale := by norm_num [sourceScale]
  have hn : 0 ≤ (4*M*L*D)*sourceScale^N := by positivity
  nlinarith

lemma form_weighted_test (W u : H1) (c : ℝ) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f) :
    r.form W (originalMulH1CLM hf hc (u-constantH1 c))=
      ∫ x,r.coefficient x*inner ℝ (weakGradient W x)
        ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure := by
  rw [r.form_apply]
  apply integral_congr_ae
  filter_upwards [originalMulH1_gradient hf hc (u-constantH1 c),
    (H1_sub_constant_spec u c).1,(H1_sub_constant_spec u c).2] with x hx hv hg
  rw [hx,hv,hg]

theorem nested_source_weighted {w : H1}
    (hw : Tendsto (fun N => (r.finiteSource N).val) atTop (𝓝 w))
    {u : H1} (hu : Harmonic r.coefficient u)
    (hb : ∃ M : ℝ,∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) :
    WeightedAnnihilation r.coefficient w u (sourceMeanCLM 0 u) := by
  obtain ⟨M,hb⟩ := hb
  let P := max M 0
  have hP : 0 ≤ P := le_max_right _ _
  have hb' : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ P := hb.mono (fun x hx => hx.trans (le_max_left _ _))
  apply weighted_annihilation_of_geometric_error r.coefficient r.coefficient_measurable.aestronglyMeasurable
    (max r.C 1) ((by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)) r.coefficient_bound hw hb'
    (sourceMeanCLM 0 u) sourceScale (by norm_num [sourceScale]) (by norm_num [sourceScale])
  intro f hf hc hsupp
  obtain ⟨L,hL,hlip⟩ := compact_smooth_lipschitz_bound f hf hc
  obtain ⟨D,hD,hdiam⟩ := sourceWordBoundary_radius
  refine ⟨4*P*L*D,?_⟩
  intro N
  rw [←r.form_weighted_test (r.finiteSource N).val u (sourceMeanCLM 0 u) hf hc]
  exact r.finiteSource_weighted_bound (r.harmonic_sourceHarmonic hu) hP hb' hf hc hL hD hlip hdiam N

end BoundedRootSources
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
attribute [local instance] OAI.ScalarConductivity.iteratedAveragesMeasureSpace
local instance iteratedAveragesIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma sourceRootBoundary_mem_closure (θ : UnitAddTorus (Fin 2)) :
    WithLp.toLp 2 (physicalOuterBoundary 0 θ)∈closure sourceDomain := by
  rw [sourceDomain_closure_time]
  change 0 ≤ sourceCollarTime (sourceAngularCollar 0 θ)
  rw [sourceAngular_time (by norm_num)]

lemma sourceWordBoundary_mem_cell (ν : SourceWord) (θ : UnitAddTorus (Fin 2)) :
    sourceWordBoundary ν θ∈sourceWordCell ν :=
  ⟨WithLp.toLp 2 (physicalOuterBoundary 0 θ),sourceRootBoundary_mem_closure θ,rfl⟩

lemma sourceWordMean_smooth_constant (ν : SourceWord) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) {c : ℝ}
    (hfc : ∀ θ,f (sourceWordBoundary ν θ)=c) :
    sourceMeanCLM 0 (sourceWordPull ν (smoothH1 f hf))=c := by
  rw [sourceMean_eq_integral]
  change (∫ θ,sourceWordTraceCLM ν (smoothH1 f hf) θ)=c
  rw [integral_congr_ae (sourceWordTrace_smooth ν hf)]
  simp [hfc]

lemma source_first_children_separator : ∃ f : R3 → ℝ,
    ContDiff ℝ (↑(⊤:ℕ∞)) f ∧
    (∀ ν θ,f (sourceWordBoundary (0::ν) θ)=1) ∧
    (∀ ν θ,f (sourceWordBoundary (1::ν) θ)=0) := by
  let A := sourceChildEuclidean (actualChildSign 0) '' closure sourceDomain
  let B := sourceChildEuclidean (actualChildSign 1) '' closure sourceDomain
  have hA : IsClosed A := (sourceClosure_isCompact.image (sourceChildEuclidean (actualChildSign 0)).continuous).isClosed
  have hB : IsClosed B := (sourceClosure_isCompact.image (sourceChildEuclidean (actualChildSign 1)).continuous).isClosed
  obtain ⟨f,hf0,hf1,hfb⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ R3) hB hA (source_child_closed_disjoint (by decide : (1:Fin 2)≠0))
    (n:=↑(⊤:ℕ∞))
  refine ⟨f,f.contMDiff.contDiff,?_,?_⟩
  · intro ν θ
    exact hf1 (sourceWordCell_cons_subset 0 ν (sourceWordBoundary_mem_cell (0::ν) θ))
  · intro ν θ
    exact hf0 (sourceWordCell_cons_subset 1 ν (sourceWordBoundary_mem_cell (1::ν) θ))

namespace BoundedRootSources
variable (r : BoundedRootSources)

lemma finiteSource_separator : ∃ ψ : H1,∀ N,r.form (r.finiteSource N).val ψ=1 := by
  obtain ⟨f,hf,hf0,hf1⟩ := source_first_children_separator
  let ψ := smoothH1 f hf
  refine ⟨ψ,?_⟩
  intro N
  rw [r.form_finiteSource]
  apply sourceAveragePullIter_mean_eq N (sourceDifferencePull ψ) 1
  intro ν hν
  change sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback 0 ψ-childH1Pullback 1 ψ))=1
  rw [map_sub,map_sub]
  have h0 := sourceWordMean_smooth_constant (0::ν) hf (hf0 ν)
  have h1 := sourceWordMean_smooth_constant (1::ν) hf (hf1 ν)
  change sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback 0 ψ))=1 at h0
  change sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback 1 ψ))=0 at h1
  rw [h0,h1,sub_zero]

lemma nested_source_nonzero {w : H1}
    (hw : Tendsto (fun N => (r.finiteSource N).val) atTop (𝓝 w)) :
    w≠0 ∧ 0<ballMeasure {x | weakValue w x≠0} := by
  obtain ⟨ψ,hψ⟩ := r.finiteSource_separator
  apply source_energy_nonzero r.coefficient r.coefficient_measurable.aestronglyMeasurable
    ((by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)) r.coefficient_bound hw ψ
  apply Eventually.of_forall
  intro N
  rw [←r.form_apply]
  exact hψ N

end BoundedRootSources
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevOuterTests
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem exists_outer_test {g : H1} {M : ℝ}
    (hg : ∀ᵐ x ∂ballMeasure, |weakValue g x|≤M)
    {r : ℝ} (hr : 0 < r) (hr3 : r<3) :
    ∃ v : H1, trace v=trace g ∧
      ∀ᵐ x ∂ballMeasure, ‖x‖ ≤ r → weakGradient v x=0 := by
  let R : ℝ := (r+3)/2
  let κ : ContDiffBump (0:R3) := ⟨R,(R+3)/2,by dsimp [R]; linarith,
    by dsimp [R]; linarith⟩
  let k := smoothH1 κ κ.contDiff
  have hk0 : k∈H10 := smoothH1_mem_H10 κ κ.contDiff κ.hasCompactSupport (by
    rw [κ.tsupport_eq]
    intro x hx
    change dist x 0<3
    have ht : dist x 0≤(R+3)/2 := hx
    dsimp [R] at ht; linarith)
  obtain ⟨N,_,hk⟩ := smoothH1_bounded κ κ.contDiff
  obtain ⟨p,_,hp,hp0⟩ := exists_H1_product hg hk
  refine ⟨g-p,?_,?_⟩
  · apply (Submodule.Quotient.eq H10).mpr
    have hs : g-p-g = -p := by abel
    rw [hs]; exact H10.neg_mem (hp0 hk0)
  · filter_upwards [weakGradient_sub g p,hp,smoothH1_value κ κ.contDiff,
      smoothH1_gradient κ κ.contDiff] with x hx hp hv hd
    intro hxnorm
    have hxin : x∈Metric.ball (0:R3) κ.rIn := by
      change dist x 0<R
      rw [dist_zero_right]; dsimp [R]; linarith
    have he := κ.eventuallyEq_one_of_mem_ball hxin
    have hgκ : gradient (κ : R3 → ℝ) x=0 := by
      rw [he.gradient_eq]
      exact gradient_fun_const x (1:ℝ)
    rw [hx,Pi.sub_apply,hp,hv,hd,he.eq_of_nhds,Pi.one_apply,hgκ,smul_zero,
      one_smul,zero_add,sub_self]

lemma IsDirichletToNeumann.pairing {a : R3 → ℝ} {Λ : DNOperator}
    (hΛ : IsDirichletToNeumann a Λ) {u : H1} (hu : Harmonic a u) (v : H1) :
    Λ (trace u) (trace v)=energy a u v := by
  obtain ⟨u₀,_,_,huniq,hpair⟩ := hΛ (trace u)
  have he : u=u₀ := huniq u rfl hu
  simpa only [he] using hpair v

theorem DN_eq_of_smooth_pairings {Λ₀ Λ₁ : DNOperator}
    (h : ∀ (f g : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g),
      Λ₀ (trace (smoothH1 f hf)) (trace (smoothH1 g hg))=
      Λ₁ (trace (smoothH1 f hf)) (trace (smoothH1 g hg))) : Λ₀=Λ₁ := by
  have hsm {u v : H1} (hu : u.val∈smoothJets) (hv : v.val∈smoothJets) :
      Λ₀ (trace u) (trace v)=Λ₁ (trace u) (trace v) := by
    obtain ⟨f,hf,hm,he⟩ := hu
    obtain ⟨g,hg,hn,hf'⟩ := hv
    have he₁ : u=smoothH1 f hf := Subtype.ext he
    have he₂ : v=smoothH1 g hg := Subtype.ext hf'
    rw [he₁,he₂]; exact h f g hf hg
  have hfirst (u : H1) (hu : u.val∈smoothJets) (v : H1) :
      Λ₀ (trace u) (trace v)=Λ₁ (trace u) (trace v) := by
    apply (closure_minimal (fun z hz => hsm hu hz) (isClosed_eq
      ((Λ₀ (trace u)).continuous.comp H10.continuous_mkQ)
      ((Λ₁ (trace u)).continuous.comp H10.continuous_mkQ))) (smoothH1_dense v)
  have hall (u v : H1) : Λ₀ (trace u) (trace v)=Λ₁ (trace u) (trace v) := by
    apply (closure_minimal (fun z hz => hfirst z hz v) (isClosed_eq
      ((ContinuousLinearMap.apply ℝ ℝ (trace v)).continuous.comp (Λ₀.continuous.comp H10.continuous_mkQ))
      ((ContinuousLinearMap.apply ℝ ℝ (trace v)).continuous.comp (Λ₁.continuous.comp H10.continuous_mkQ)))) (smoothH1_dense u)
  ext f g
  obtain ⟨u,rfl⟩ := H10.mkQ_surjective f
  obtain ⟨v,rfl⟩ := H10.mkQ_surjective g
  exact hall u v

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WeightedGaugeDN
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem weighted_gauge_DN (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (c C : ℝ) (hc : 0 < c) (hC : 0≤C)
    (hab : ∀ᵐ x ∂ballMeasure, c≤a x ∧ a x≤C)
    (w : H1) (hw0 : w∈H10) (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2)
    (r : ℝ) (hr : 0 < r) (hr3 : r<3)
    (hsupp : ∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0)
    (hweighted : ∀ u : H1, Harmonic a u →
      (∃ M : ℝ, ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M) →
      ∃ d : ℝ, WeightedAnnihilation a w u d) :
    ∃ Λ : DNOperator, IsDirichletToNeumann a Λ ∧
      IsDirichletToNeumann (gaugeCoefficient a w) Λ := by
  have habs : ∀ᵐ x ∂ballMeasure, |a x|≤C := hab.mono
    (fun x hx => by rw [abs_of_nonneg (hc.le.trans hx.1)]; exact hx.2)
  obtain ⟨Λ₀,hΛ₀⟩ := exists_DirichletToNeumann a ha C hC habs c hc
    (hab.mono (fun _ hx => hx.1))
  have hbb := gaugeCoefficient_bounds hc hab hw
  have hbabs : ∀ᵐ x ∂ballMeasure, |gaugeCoefficient a w x|≤9*C/4 := hbb.mono
    (fun x hx => by rw [abs_of_nonneg ((div_pos hc (by norm_num)).le.trans hx.1)]; exact hx.2)
  obtain ⟨Λ₁,hΛ₁⟩ := exists_DirichletToNeumann _ (gaugeCoefficient_aeStronglyMeasurable a ha w)
    (9*C/4) (by positivity) hbabs (c/4) (by positivity) (hbb.mono (fun _ hx => hx.1))
  have heq : Λ₀=Λ₁ := by
    apply DN_eq_of_smooth_pairings
    intro f g hf hg
    obtain ⟨u,ht,hu,_,_⟩ := hΛ₀ (trace (smoothH1 f hf))
    obtain ⟨M,hM,hfM⟩ := smoothH1_bounded f hf
    have huM := harmonic_bounded_of_trace_bounded a ha C hC habs
      (hab.mono (fun _ hx => hc.trans_le hx.1)) hu ht hM hfM
    obtain ⟨d,hd⟩ := hweighted u hu ⟨M,huM⟩
    obtain ⟨u₁,ht₁,_,hflux⟩ := exists_gauge_transform huM hw hw0 d
    have hflux' : ∀ᵐ x ∂ballMeasure,
        gaugeCoefficient a w x • weakGradient u₁ x=
        ((1+weakValue w x)*a x) • weakGradient u x-
          ((weakValue u x-d)*a x) • weakGradient w x := hflux.mono (fun x hx => hx (a x))
    have hu₁ := gauge_harmonic_of_weighted a ha C hC habs huM hw hu d hd hflux'
    obtain ⟨N,_,hgN⟩ := smoothH1_bounded g hg
    obtain ⟨V,hV,hVg⟩ := exists_outer_test hgN hr hr3
    have he : energy a u V=energy (gaugeCoefficient a w) u₁ V := by
      apply integral_congr_ae
      filter_upwards [hflux',hsupp,hVg] with x hx hy hz
      by_cases hh : ‖x‖ ≤ r
      · simp only [hz hh, inner_zero_right, mul_zero]
      · obtain ⟨hv,hg⟩ := hy (lt_of_not_ge hh)
        simp only [←real_inner_smul_left]
        rw [hx,hv,hg,smul_zero,sub_zero,add_zero,one_mul]
    calc
      Λ₀ (trace (smoothH1 f hf)) (trace (smoothH1 g hg)) = Λ₀ (trace u) (trace V) := by rw [ht,hV]
      _ = energy a u V := hΛ₀.pairing hu V
      _ = energy (gaugeCoefficient a w) u₁ V := he
      _ = Λ₁ (trace u₁) (trace V) := (hΛ₁.pairing hu₁ V).symm
      _ = Λ₁ (trace (smoothH1 f hf)) (trace (smoothH1 g hg)) := by rw [ht₁,ht,hV]
  exact ⟨Λ₀,hΛ₀,heq.symm ▸ hΛ₁⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma weakValue_measurable (w : H1) : Measurable (weakValue w) :=
  jetValue.continuous.measurable.comp (Lp.stronglyMeasurable w.val).measurable

lemma gaugeCoefficient_measurable {a : R3 → ℝ} (ha : Measurable a) (w : H1) :
    Measurable (gaugeCoefficient a w) :=
  ha.mul ((measurable_const.add (weakValue_measurable w)).pow_const 2)

lemma gaugeCoefficient_ne_ae_iff {a : R3 → ℝ} {w : H1}
    (ha : ∀ᵐ x ∂ballMeasure, 0<a x)
    (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2) :
    ∀ᵐ x ∂ballMeasure, a x≠gaugeCoefficient a w x ↔ weakValue w x≠0 := by
  filter_upwards [ha,hw] with x ha hw
  apply not_congr
  change a x=a x*(1+weakValue w x)^2 ↔ weakValue w x=0
  constructor
  · intro h
    have hs : (1+weakValue w x)^2=1 := by
      apply mul_left_cancel₀ ha.ne'
      simpa only [mul_one] using h.symm
    have hm : weakValue w x*(2+weakValue w x)=0 := by nlinarith
    have hp : 0<2+weakValue w x := by have := (abs_le.mp hw).1; linarith
    exact (mul_eq_zero.mp hm).resolve_right hp.ne'
  · intro h; simp [h]

lemma gaugeCoefficient_equalOneNearBoundary {a : R3 → ℝ} {w : H1}
    (ha : EqualOneNearBoundary a) {r : ℝ} (hr : 0 < r) (hr3 : r<3)
    (hsupp : ∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0) :
    EqualOneNearBoundary (gaugeCoefficient a w) := by
  obtain ⟨q,_,hq3,hqa⟩ := ha
  refine ⟨max q r,lt_of_lt_of_le hr (le_max_right _ _),max_lt hq3 hr3,?_⟩
  filter_upwards [hsupp,hqa] with x hx hy
  intro hn
  have hwr := hx (lt_of_le_of_lt (le_max_right _ _) hn)
  have har := hy (lt_of_le_of_lt (le_max_left _ _) hn)
  simp only [gaugeCoefficient,hwr,har,add_zero,one_pow,mul_one]

theorem MainStatement_of_weighted_source
    (a : R3 → ℝ) (ha : Measurable a) (c C : ℝ) (hc : 0 < c) (hcC : c<C)
    (hab : ∀ᵐ x ∂ballMeasure, c≤a x ∧ a x≤C) (hnear : EqualOneNearBoundary a)
    (w : H1) (hw0 : w∈H10) (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2)
    (hwne : 0<ballMeasure {x | weakValue w x≠0})
    (r : ℝ) (hr : 0 < r) (hr3 : r<3)
    (hsupp : ∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0)
    (hweighted : ∀ u : H1, Harmonic a u →
      (∃ M : ℝ, ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M) →
      ∃ d : ℝ, WeightedAnnihilation a w u d) : MainStatement := by
  have hC : 0<C := hc.trans hcC
  have habs : ∀ᵐ x ∂ballMeasure, |a x|≤C := hab.mono
    (fun x hx => by rw [abs_of_nonneg (hc.le.trans hx.1)]; exact hx.2)
  have hbb := gaugeCoefficient_bounds hc hab hw
  have hbabs : ∀ᵐ x ∂ballMeasure, |gaugeCoefficient a w x|≤9*C/4 := hbb.mono
    (fun x hx => by rw [abs_of_nonneg ((div_pos hc (by norm_num)).le.trans hx.1)]; exact hx.2)
  have ham : MemLp a ∞ ballMeasure := MemLp.of_bound ha.aestronglyMeasurable C
    (by simpa only [Real.norm_eq_abs] using habs)
  have hbm : MemLp (gaugeCoefficient a w) ∞ ballMeasure :=
    MemLp.of_bound (gaugeCoefficient_aeStronglyMeasurable a ha.aestronglyMeasurable w) (9*C/4)
      (by simpa only [Real.norm_eq_abs] using hbabs)
  obtain ⟨Λ,hΛ₀,hΛ₁⟩ := weighted_gauge_DN a ha.aestronglyMeasurable c C hc hC.le hab
    w hw0 hw r hr hr3 hsupp hweighted
  refine ⟨a,gaugeCoefficient a w,c/4,9*C/4+1,Λ,by positivity,by linarith,
    ha,gaugeCoefficient_measurable ha w,ham,hbm,?_,?_,hnear,?_,?_,hΛ₀,hΛ₁⟩
  · filter_upwards [hab] with x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · filter_upwards [hbb] with x hx
    exact ⟨hx.1,by linarith [hx.2]⟩
  · exact gaugeCoefficient_equalOneNearBoundary hnear hr hr3
      (hsupp.mono (fun _ hx h => (hx h).1))
  · have he := gaugeCoefficient_ne_ae_iff (hab.mono (fun _ hx => hc.trans_le hx.1)) hw
    have hm : ballMeasure {x | a x≠gaugeCoefficient a w x}=ballMeasure {x | weakValue w x≠0} :=
      measure_congr (he.mono (fun _ hx => propext hx))
    rw [hm]; exact hwne

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma WeightedAnnihilation.smul {a : R3 → ℝ} {w u : H1} {c : ℝ}
    (hw : WeightedAnnihilation a w u c) (δ : ℝ) :
    WeightedAnnihilation a (δ • w) u c := by
  intro f hf hc hs
  calc
    (∫ x,a x*inner ℝ (weakGradient (δ • w) x)
      ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure)=
        ∫ x,δ*(a x*inner ℝ (weakGradient w x)
          ((weakValue u x-c) • gradient f x+f x • weakGradient u x)) ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [weakGradient_smul δ w] with x hx
      rw [hx,Pi.smul_apply,real_inner_smul_left]
      ring
    _=0 := by rw [integral_const_mul,hw f hf hc hs,mul_zero]

theorem actual_nested_weighted_source_exists :
    ∃ (a : R3 → ℝ) (c C : ℝ) (w : H1),
      Measurable a ∧ 0 < c ∧ c<C ∧
      (∀ᵐ x∂ballMeasure,c ≤ a x ∧ a x ≤ C) ∧ EqualOneNearBoundary a ∧
      w∈H10 ∧ (∀ᵐ x∂ballMeasure,abs (weakValue w x) ≤ 1/2) ∧
      0<ballMeasure {x | weakValue w x≠0} ∧
      (∀ᵐ x∂ballMeasure,(5/2:ℝ)<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0) ∧
      ∀ u : H1,Harmonic a u → (∃ M : ℝ,∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) →
        ∃ d : ℝ,WeightedAnnihilation a w u d := by
  let r : BoundedRootSources := Classical.choice boundedRootSources_nonempty
  obtain ⟨w,hw,⟨M,hM,hMb⟩,ht⟩ := r.nested_source_limit_exists
  let δ : ℝ := 1/(2*M)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδM : δ*M=1/2 := by dsimp [δ]; field_simp
  have hwne := r.nested_source_nonzero ht
  have hvne : δ • w.val≠(0:H1) := smul_ne_zero hδ.ne' hwne.1
  refine ⟨r.coefficient,min r.c 1,max r.C 1+1,δ • w.val,
    r.coefficient_measurable,lt_min r.c_pos (by norm_num),?_,?_,
    copiedScalarCoefficient_collar r.b,H10.smul_mem δ w.property,?_,
    nonzero_h1_positive_value_measure hvne,sourceSupported_collar (hw.smul δ),?_⟩
  · have hmin := min_le_left r.c 1
    have hmax := le_max_left r.C 1
    have hcc := r.c_lt_C
    linarith
  · exact Eventually.of_forall (fun x => ⟨(copiedScalarCoefficient_bounds r.bounds x).1,
      (copiedScalarCoefficient_bounds r.bounds x).2.trans (by linarith)⟩)
  · have hh := weakValue_bound_smul hMb δ
    simpa only [abs_of_pos hδ,hδM] using hh
  · intro u hu hb
    exact ⟨sourceMeanCLM 0 u,(r.nested_source_weighted ht hu hb).smul δ⟩

theorem main_nonuniqueness_oai : MainStatement := by
  obtain ⟨a,c,C,w,ha,hc,hcC,hab,hnear,hw0,hw,hwne,hsupp,hweighted⟩ :=
    actual_nested_weighted_source_exists
  exact MainStatement_of_weighted_source a ha c C hc hcC hab hnear w hw0 hw hwne
    (5/2) (by norm_num) (by norm_num) hsupp hweighted

end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.main_nonuniqueness_oai := @OAI.ScalarConductivity.main_nonuniqueness_oai
