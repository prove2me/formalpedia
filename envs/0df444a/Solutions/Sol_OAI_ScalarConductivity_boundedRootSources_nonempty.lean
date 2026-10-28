-- Prove2me | solution 1 for OAI.ScalarConductivity.boundedRootSources_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:24:58.782374+00:00
-- url     : https://prove2.me/submissions/171f5ae1-987c-46af-8975-01200901e745

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C008
import Theorems.Thm_OAI_ScalarConductivity_PhysicalFiniteEndingData_scalar_pair_green_exists
import Theorems.Thm_OAI_ScalarConductivity_physicalFiniteEndingData_nonempty

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusNonresonance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory

lemma real_outer_pair_injective {a b c d : ℝ}
    (h0 : a^2=c^2) (h1 : b^2=d^2) (h2 : a*b=c*d) :
    (a=c ∧ b=d) ∨ (a= -c ∧ b= -d) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h0 with h0|h0 <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h1|h1
  · exact Or.inl ⟨h0,h1⟩
  · by_cases hc : c=0
    · right; constructor <;> linarith
    · left; refine ⟨h0,?_⟩
      have hz : c*(b-d)=0 := by rw [h0] at h2; nlinarith
      have := (mul_eq_zero.mp hz).resolve_left hc
      linarith
  · by_cases hd : d=0
    · right; constructor <;> linarith
    · left; refine ⟨?_,h1⟩
      have hz : (a-c)*d=0 := by rw [h1] at h2; nlinarith
      have := (mul_eq_zero.mp hz).resolve_right hd
      linarith
  · exact Or.inr ⟨h0,h1⟩

lemma torusResonance_proper {h l : Fin 2 → ℤ} (he : l ≠ h) (hn : l ≠ -h) :
    (torusResonanceForm h l).ker ≠ ⊤ := by
  intro hk
  have hh (s : Fin 3 → ℝ) : torusQuadratic s h=torusQuadratic s l := by
    have : s∈(torusResonanceForm h l).ker := hk ▸ Submodule.mem_top
    exact sub_eq_zero.mp this
  have h0 := hh ![1,0,0]
  have h1 := hh ![0,0,1]
  have h2 := hh ![0,1,0]
  norm_num [torusQuadratic,Matrix.cons_val_two] at h0 h1 h2
  have h2' : (h 0 : ℝ)*(h 1 : ℝ)=(l 0 : ℝ)*(l 1 : ℝ) := by linarith
  rcases real_outer_pair_injective h0 h1 h2' with hh|hh
  · apply he; ext i; fin_cases i
    · exact_mod_cast hh.1.symm
    · exact_mod_cast hh.2.symm
  · apply hn; ext i; fin_cases i
    · change l 0= -(h 0)
      exact_mod_cast (show (l 0 : ℝ)= -(h 0 : ℝ) by linarith [hh.1])
    · change l 1= -(h 1)
      exact_mod_cast (show (l 1 : ℝ)= -(h 1 : ℝ) by linarith [hh.2])

theorem exists_nonresonant_angular_tensor : ∃ s : Fin 3 → ℝ,
    (∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) ∧
    (∀ h l : Fin 2 → ℤ, torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h) := by
  let I := {p : (Fin 2 → ℤ) × (Fin 2 → ℤ) // p.2 ≠ p.1 ∧ p.2 ≠ -p.1}
  let bad : Set (Fin 3 → ℝ) := ⋃ p : I, ((torusResonanceForm p.val.1 p.val.2).ker : Set (Fin 3 → ℝ))
  have hbad : volume bad=0 := by
    apply measure_iUnion_null
    intro p
    exact Measure.addHaar_submodule volume _ (torusResonance_proper p.property.1 p.property.2)
  let o : Fin 3 → ℝ := ![1,0,1]
  obtain ⟨s,hs,hsg⟩ : ∃ s∈Metric.ball o (1/4), s∉bad := by
    by_contra! hn
    have hsub : Metric.ball o (1/4)⊆bad := hn
    have hle := measure_mono (μ := volume) hsub
    rw [hbad] at hle
    exact (Metric.measure_ball_pos volume o (by norm_num : (0:ℝ)<1/4)).not_ge hle
  refine ⟨s,?_,?_⟩
  · have hnorm : ‖s-o‖<1/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using hs
    have hi (i : Fin 3) : |s i-o i|<1/4 := by
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using (norm_le_pi_norm (s-o) i).trans_lt hnorm
    have h0 := (abs_lt.mp (hi 0)).1
    have h1 := abs_lt.mp (hi 1)
    have h2 := (abs_lt.mp (hi 2)).1
    norm_num [o,Matrix.cons_val_two] at h0 h1 h2
    intro x y
    nlinarith [mul_nonneg (show 0 ≤ s 0-3/4 by linarith) (sq_nonneg x),
      mul_nonneg (show 0 ≤ s 2-3/4 by linarith) (sq_nonneg y),
      mul_nonneg (show 0 ≤ 1/4+s 1 by linarith) (sq_nonneg (x+y)),
      mul_nonneg (show 0 ≤ 1/4-s 1 by linarith) (sq_nonneg (x-y))]
  · intro h l hh
    by_contra! hn
    apply hsg
    apply mem_iUnion.mpr
    refine ⟨⟨(h,l),hn⟩,?_⟩
    exact sub_eq_zero.mpr hh

end

open Set

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

lemma weakGradient_sub (u v : H1) : weakGradient (u-v) =ᵐ[ballMeasure] weakGradient u-weakGradient v := by
  filter_upwards [Lp.coeFn_sub u.val v.val] with x hx
  change jetGradient ((u.val-v.val) x)=jetGradient (u.val x)-jetGradient (v.val x)
  rw [hx,Pi.sub_apply,map_sub]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CompactLipschitzH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

theorem compact_lipschitz_H1 {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hR : R<3)
    (hs : ∀ x, R<‖x‖ → f x=0) :
    ∃ u : H1, u∈H10 ∧ (∀ᵐ x ∂ballMeasure,
      weakValue u x=f x ∧ ∀ i : Fin 3,
        weakGradient u x i=lineDeriv ℝ f x (EuclideanSpace.single i 1)) := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport (bounded_support_compact hs)
  have hd (i : Fin 3) := lipschitz_lineDeriv_memLp hf hs (EuclideanSpace.single i 1)
  let F : Fin 4 → WholeL2 := Fin.cases (hm.toLp f)
    (fun i => (hd i).toLp (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)))
  have hv : (F 0 : R3 → ℝ)=ᵐ[volume] f := hm.coeFn_toLp
  have hg (i : Fin 3) : (F i.succ : R3 → ℝ)=ᵐ[volume]
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) := (hd i).coeFn_toLp
  have hw (i : Fin 3) : WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1) :=
    (lipschitz_weakDirection hf _).congr hv (hg i)
  obtain ⟨u,hu,he⟩ := compact_weak_H1 F hw hR (by
    filter_upwards [hv] with x hx
    intro hn
    exact hx.trans (hs x hn))
  refine ⟨u,hu,?_⟩
  have hv' := hv.filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  have hg' := (ae_all_iff.mpr hg).filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  filter_upwards [he,hv',hg'] with x hx hy hz
  exact ⟨hx.1.trans hy,fun i => (hx.2 i).trans (hz i)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma squareFace_interior_unique (i k : Fin 4) {a b : ℝ} (ha : |a|<1)
    (he : squareFace i a=squareFace k b) : i=k := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have ha₁ := (abs_lt.mp ha).1
  have ha₂ := (abs_lt.mp ha).2
  fin_cases i <;> fin_cases k <;>
    simp [squareFace,squareFaceBase,squareFaceDirection] at h0 h1 ⊢ <;> linarith

lemma sourceCollarPiece_open_unique (i j k l : Fin 4) {x z : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox)
    (hz : z∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (he : sourceCollarPiece i j x=sourceCollarPiece k l z) : i=k ∧ j=l := by
  obtain ⟨hzt,hza,hzb⟩ := mem_sourceExtendedBox.mp hz
  have hx' := sourceCollarOpenBox_subset hx
  obtain ⟨hxt,hxa,hxb⟩ := mem_sourceExtendedBox.mp hx'
  have hxR : 0 < sourceCollarRadius j (x 0) (x 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended j hxt hxb).1
  have hzR : 0 < sourceCollarRadius l (z 0) (z 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended l hzt hzb).1
  have hR : sourceCollarRadius j (x 0) (x 2)=sourceCollarRadius l (z 0) (z 2) := by
    have hh := congrArg sourceRadial he
    rwa [sourceCollarPiece_radial_pos i j hxR.le hxa,
      sourceCollarPiece_radial_pos k l hzR.le hza] at hh
  have ht : x 0=z 0 := by
    have hh := congrArg sourceCollarTime he
    rwa [sourceCollarPiece_time_pos i j hxR.le (by linarith [hxt.2]) hxa hxb,
      sourceCollarPiece_time_pos k l hzR.le (by linarith [hzt.2]) hza hzb] at hh
  constructor
  · apply squareFace_interior_unique i k hx.2.1
    have hh := congrArg (fun y : Fin 3 → ℝ => ![y 0/sourceLength,y 1]) he
    rw [sourceCollarPiece_angular,sourceCollarPiece_angular,←hR] at hh
    exact smul_right_injective (Fin 2 → ℝ) hxR.ne' hh
  · apply squareFace_interior_unique j l hx.2.2
    have hh := congrArg sourceCrossCoordinates he
    rw [sourceCollarPiece_cross_pos i j hxR.le hxa,
      sourceCollarPiece_cross_pos k l hzR.le hza,←ht] at hh
    exact smul_right_injective (Fin 2 → ℝ) (by linarith [hxt.2] : 1-x 0≠0) hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTestEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceExtendedBox_open_ae {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x∈sourceCollarOpenBox := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier B := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc),
    ae_restrict_of_ae hn] with x hx hn
  have hxB : x∈B := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra h
  exact hn ⟨subset_closure hxB,h⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullWeakEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceCollarClosedPiece_measurable (l r : ℝ) (i j : Fin 4) :
    MeasurableSet (sourceCollarPiece i j '' sourceExtendedBox l r) :=
  (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measurableSet

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullEndClosedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceExtendedBox_interior_axial {l r : ℝ} {x : Fin 3 → ℝ}
    (hx : x∈interior (sourceExtendedBox l r)) : x 0∈Ioo l r := by
  have hbox : sourceExtendedBox l r=
      (univ : Set (Fin 3)).pi (fun k => Icc (![l,-1,-1] k) (![r,1,1] k)) := by
    ext x
    simp only [sourceExtendedBox,mem_Icc,Set.mem_pi,mem_univ,true_implies,Pi.le_def]
    simp only [forall_and]
  rw [hbox,interior_pi_set (finite_univ)] at hx
  have ht := hx 0 (mem_univ 0)
  simpa only [interior_Icc,Matrix.cons_val_zero] using ht

lemma sourceExtendedBox_axial_strict_ae (l r : ℝ) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x 0∈Ioo l r := by
  have hB : volume (frontier (sourceExtendedBox l r))=0 :=
    (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier (sourceExtendedBox l r) := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  apply sourceExtendedBox_interior_axial
  by_contra hi
  exact hx ⟨subset_closure hm,hi⟩

end ScalarConductivity

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

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSmoothModeJet
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

lemma torusAngles_shift (n : Fin 2 → ℤ) (x : Coord3) :
    torusAngles (x+angularShift (2*Real.pi) n)=torusAngles x := by
  have hπ : 2*Real.pi≠0 := by positivity
  ext i
  fin_cases i <;> simp [torusAngles,angularShift,add_div,hπ,mul_div_cancel_left₀]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusAffineField
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusAffineField_periodic (s : Fin 3 → ℝ) (κ : ℝ) (f : TorusL2) :
    AngularPeriodic (2*Real.pi) (torusAffineField s κ f) := by
  intro n x
  simp only [torusAffineField,torusRealContinuation,torusAngles_shift]
  simp [angularShift]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AxialExtension
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_eventually_self {d e : ℝ} {f : Coord3 → E} {x : Coord3}
    (hx : d+e/2<x 0) : axialZeroExtension d e f=ᶠ[𝓝 x] f := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx] with y hy
  exact ite_eq_left hy

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_periodic {T d e : ℝ} {f : Coord3 → E}
    (hf : AngularPeriodic T f) : AngularPeriodic T (axialZeroExtension d e f) := by
  intro n x
  change (if d+e/2<x 0+0 then f (x+angularShift T n) else 0)=_
  rw [add_zero,hf n x]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma torusEndingCorrection_periodic {T d e : ℝ} {v f : Coord3 → ℝ}
    (hv : AngularPeriodic T v) (hf : AngularPeriodic T f) :
    AngularPeriodic T (torusEndingCorrection d e v f) := by
  apply axialZeroExtension_periodic
  intro n x
  change v (x+angularShift T n)-f (x+angularShift T n)=v x-f x
  rw [hv n x,hf n x]

lemma torusEndingCorrection_terminal {d e : ℝ} {v f : Coord3 → ℝ}
    {x : Coord3} (hx : d+e/2<x 0) :
    torusEndingCorrection d e v f=ᶠ[𝓝 x] (v-f) :=
  axialZeroExtension_eventually_self (by linarith)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiniteEndPhysicalDescent
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma sourceRealFlat_angles (y : Coord3) :
    torusAngles (sourceRealFlat y)=sourcePhysicalAngles y := by
  ext i
  fin_cases i <;> rfl

lemma physicalPeriodicField_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    physicalPeriodicField f (sourceCollarPiece i j x)=f (sourceFaceAngles i j x) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [←sourceFaceAngles_physical i j ha hb]
  apply hp.eq_of_angles
  · exact sourceAngular_time ht _
  · rw [sourceRealFlat_angles]
    exact congrArg Prod.snd (sourcePhysicalCoordinates_angular ht _)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSpectralContinuation
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusSpectralSynthesis_coeff (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (h : Fin 2 → ℤ) :
    mFourierCoeff (torusSpectralSynthesis s f) h=f.val 0 h := by
  rw [←mFourierBasis_repr]
  change (mFourierBasis (d:=Fin 2)).repr ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)) h=_
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma torusRealContinuation_spectral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (torusSpectralSynthesis s f) x=
      (endPoissonField s f 0 (x 0,torusAngles x)).re := by
  unfold torusRealContinuation
  congr 1
  rw [torusPoissonContinuous_apply hs hx]
  unfold endPoissonField
  apply tsum_congr
  intro h
  simp [endPoissonModeField,endModeCoefficient,torusSpectralSynthesis_coeff]

lemma mFourierCoeff_Lp_add (f g : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (f+g) h=mFourierCoeff f h+mFourierCoeff g h := by
  simp only [←mFourierBasis_repr,map_add,lp.coeFn_add,Pi.add_apply]

lemma mFourierCoeff_Lp_neg (f : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (-f) h= -mFourierCoeff f h := by
  simp only [←mFourierBasis_repr,map_neg,lp.coeFn_neg,Pi.neg_apply]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchOutputNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

variable {E : Type*} [AddCommGroup E]

variable [Module ℝ E]

lemma branchNormalize_means (i : Fin 3) (f : Fin 2 → TorusL2) :
    branchNormalize i (fun j => (mFourierCoeff (f j) 0).re)=
      fun j => (mFourierCoeff (branchNormalize i f j : TorusL2) 0).re := by
  fin_cases i
  · ext j
    fin_cases j
    · change -(mFourierCoeff (f 0) 0).re=(mFourierCoeff (-f 0 : TorusL2) 0).re
      rw [mFourierCoeff_Lp_neg,Complex.neg_re]
    · change (mFourierCoeff (f 1) 0).re-(mFourierCoeff (f 0) 0).re=
        (mFourierCoeff (f 1-f 0 : TorusL2) 0).re
      simp only [sub_eq_add_neg]
      rw [mFourierCoeff_Lp_add,mFourierCoeff_Lp_neg,Complex.add_re,Complex.neg_re]
  · rfl
  · ext j
    fin_cases j <;> rfl

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

namespace TorusEndingData
variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (z : TorusEndingData s f)

lemma terminal_component (j : Fin 2) (x : Coord3) (hx : z.R≤x 0) :
    z.w.v x j=normalizedSlope j*x 0+(mFourierCoeff (f j) 0).re := by
  rw [z.terminal_v x hx]
  fin_cases j <;> simp [normalizedSlope]

end TorusEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchFiniteEnding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma branchFinitePair_v {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) :
    (branchFinitePair i z).v x=branchNormalize i (z.w.v x) := by
  simp [branchFinitePair]

lemma branchFinitePair_terminal {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) (hx : z.R≤x 0) :
    (branchFinitePair i z).v x=fun j => centralBasisSlopes j i*x 0+(mFourierCoeff (f j) 0).re := by
  rw [branchFinitePair_v]
  have he : z.w.v x=(fun j => normalizedSlope j*x 0)+
      (fun j => (mFourierCoeff (branchNormalize i f j : TorusL2) 0).re) := by
    ext j
    exact z.terminal_component j x hx
  rw [he,branchNormalize_add]
  have hm := (branchNormalize_means i (branchNormalize i f)).trans
    (by rw [branchNormalize_involutive])
  rw [hm]
  have hs : branchNormalize i (fun j => normalizedSlope j*x 0)=
      fun j => centralBasisSlopes j i*x 0 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [branchNormalize,normalizedSlope,centralBasisSlopes]
  rw [hs]
  rfl

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

lemma branchFinitePair_periodic_v : AngularPeriodic (2*Real.pi) (branchFinitePair i z).v := by
  intro n x
  simp only [branchFinitePair_v,z.periodic_v n x]

lemma branchCorrection_periodic (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (branchCorrection i z j) := by
  exact torusEndingCorrection_periodic
    (fun n x => congrFun (branchFinitePair_periodic_v i z n x) j)
    (torusAffineField_periodic _ _ _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_FlatEndingSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

lemma branchSplicedField_final (j : Fin 2) {x : Coord3} (hx : z.d+z.e/2<x 0) :
    branchSplicedField i z j=ᶠ[𝓝 x] (fun y => (branchFinitePair i z).v y j) := by
  filter_upwards [torusEndingCorrection_terminal
    (v:=fun y => (branchFinitePair i z).v y j)
    (f:=torusAffineField s (centralBasisSlopes j i) (f j)) hx] with y hy
  change _+torusEndingCorrection _ _ _ _ y=_
  rw [hy]
  change torusAffineField s (centralBasisSlopes j i) (f j) y+
    ((branchFinitePair i z).v y j-torusAffineField s (centralBasisSlopes j i) (f j) y)=_
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physicalBlockRegion_compact : IsCompact physicalBlockRegion :=
  centralPhysical_compact.union (isCompact_iUnion physicalEndRegion_compact)

lemma physicalBlockRegion_subset_ball {y : Fin 3 → ℝ} (hy : y∈physicalBlockRegion) :
    WithLp.toLp 2 y∈ball := by
  rcases hy with hc|he
  · exact centralPhysical_subset_ball hc
  · obtain ⟨i,hi⟩ := mem_iUnion.mp he
    exact physicalEndRegion_subset_ball i hi

lemma physicalEndRegion_mem_block (i : Fin 3) : physicalEndRegion i⊆physicalBlockRegion :=
  fun _ hy => Or.inr (mem_iUnion.mpr ⟨i,hy⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExpandedInner_bounds {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) :
    |y 0|≤1602/1000 ∧ |y 1|≤1001/1000 ∧ |y 2|≤1002/1000 := by
  have hh := (sourceCollarTime_ge_iff y (-centralThickness)).mp hy
  have hx := (le_max_left (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  have hy' := (le_max_right (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  norm_num [centralThickness,sourceRadialWidth,sourceHole,sourceLength] at hx hy' hh ⊢
  exact ⟨by linarith,by linarith,by linarith [hh.1]⟩

lemma sourceExpandedChild_far_parent (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) :
    2*centralThickness ≤ sourceCollarTime (sourceChildCoordinates (actualChildSign k) y) := by
  obtain ⟨h₀,h₁,h₂⟩ := sourceExpandedInner_bounds hy
  have hsign : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  have ha : |actualChildSign k*sourceOffset|=sourceOffset := by
    rw [abs_mul,hsign,one_mul]; norm_num [sourceOffset]
  have hu := abs_add_le (sourceScale*y 1) (actualChildSign k*sourceOffset)
  rw [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale]),ha] at hu
  have hl := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+actualChildSign k*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+actualChildSign k*sourceOffset)=
    actualChildSign k*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at hl
  apply (sourceCollarTime_ge_iff _ _).mpr
  change |sourceScale*y 2|≤_ ∧ _≤ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
    (|sourceScale*y 0|) ∧ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
      (|sourceScale*y 0|)≤_
  simp only [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])]
  constructor
  · norm_num [sourceScale,centralThickness]; linarith
  · constructor
    · apply le_trans _ (le_max_left _ _)
      norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
      linarith
    · apply max_le
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith

lemma sourceExpandedChildren_exclusive (y : Fin 3 → ℝ)
    (h₀ : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y))
    (h₁ : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)) : False := by
  have ha := (sourceExpandedInner_bounds h₀).2.1
  have hb := (sourceExpandedInner_bounds h₁).2.1
  change |(y 0 - actualChildSign 0 * sourceOffset)/sourceScale| ≤ _ at ha
  change |(y 0 - actualChildSign 1 * sourceOffset)/sourceScale| ≤ _ at hb
  norm_num [actualChildSign] at ha hb
  rw [abs_div,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at ha hb
  have ha' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp ha)
  have hb' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp hb)
  norm_num [sourceScale,sourceOffset] at ha' hb'
  linarith [ha'.1,hb'.2]

lemma sourceExpandedChild_other (k j : Fin 2) (hkj : k≠j) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) :
    sourceCollarTime ((sourceChildHomeomorph (actualChildSign j)).symm y)< -centralThickness := by
  by_contra h
  have hj := le_of_not_gt h
  fin_cases k <;> fin_cases j
  · exact hkj rfl
  · exact sourceExpandedChildren_exclusive y hy hj
  · exact sourceExpandedChildren_exclusive y hj hy
  · exact hkj rfl

theorem physicalBlockRegion_time_iff (y : Fin 3 → ℝ) :
    y∈physicalBlockRegion ↔ 0≤ sourceCollarTime y ∧
      ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≤0 := by
  have hδ : 0 < centralThickness := by norm_num [centralThickness]
  have hfar (k : Fin 2)
      (h : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) :
      2*centralThickness≤ sourceCollarTime y := by
    have hh := sourceExpandedChild_far_parent k h
    have he : sourceChildCoordinates (actualChildSign k)
        ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
    rwa [he] at hh
  constructor
  · rintro (hc|he)
    · obtain ⟨hp,hc⟩ := (centralPhysical_time_iff y).mp hc
      exact ⟨hδ.le.trans hp,fun k => (hc k).trans (by linarith)⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp he
      revert hi
      refine Fin.cases ?_ (fun k => ?_) i
      · intro hi
        change sourceCollarTime y∈Icc 0 centralThickness at hi
        refine ⟨hi.1,fun k => ?_⟩
        by_contra hn
        have hh := hfar k (show -centralThickness≤ sourceCollarTime
            ((sourceChildHomeomorph (actualChildSign k)).symm y) by linarith [lt_of_not_ge hn])
        linarith [hi.2]
      · intro hi
        change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)
          ∈Icc (-centralThickness) 0 at hi
        refine ⟨(by linarith [hfar k hi.1]),fun j => ?_⟩
        by_cases hkj : k=j
        · simpa only [←hkj] using hi.2
        · exact (sourceExpandedChild_other k j hkj hi.1).le.trans (by linarith)
  · rintro ⟨hp,hc⟩
    by_cases ht : sourceCollarTime y ≤ centralThickness
    · exact physicalEndRegion_mem_block 0 ⟨hp,ht⟩
    · by_cases hh : ∀ k : Fin 2,sourceCollarTime
          ((sourceChildHomeomorph (actualChildSign k)).symm y)≤ -centralThickness
      · exact Or.inl ((centralPhysical_time_iff y).mpr ⟨(lt_of_not_ge ht).le,hh⟩)
      · push Not at hh
        obtain ⟨k,hk⟩ := hh
        exact physicalEndRegion_mem_block k.succ ⟨hk.le,hc k⟩

end ScalarConductivity

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
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalOpenBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceSimilarity_childInverse (σ : ℝ) (y : Fin 3 → ℝ) :
    sourceSimilarity σ (WithLp.toLp 2 ((sourceChildHomeomorph σ).symm y))=WithLp.toLp 2 y := by
  rw [←sourceChild_toLp]
  exact congrArg (WithLp.toLp 2) ((sourceChildHomeomorph σ).apply_symm_apply y)

lemma sourceChild_closure_image_iff (σ : ℝ) (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈sourceSimilarity σ '' closure sourceDomain ↔
      0≤ sourceCollarTime ((sourceChildHomeomorph σ).symm y) := by
  rw [←sourceDomain_closure_time]
  constructor
  · rintro ⟨x,hx,he⟩
    have hh := (sourceSimilarity σ).injective (he.trans (sourceSimilarity_childInverse σ y).symm)
    rwa [←hh]
  · intro hy
    exact ⟨_,hy,sourceSimilarity_childInverse σ y⟩

lemma sourceOpenBlock_time_iff (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈sourceOpenBlock ↔ 0 < sourceCollarTime y ∧
      ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)<0 := by
  simp only [sourceOpenBlock,Set.mem_sdiff,mem_iUnion,not_exists,
    ←sourceCollarTime_pos_iff_domain,sourceChild_closure_image_iff,not_le]

end ScalarConductivity



end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceOpenBlock_parent_band {y : Fin 3 → ℝ}
    (hp : 0 < sourceCollarTime y) (ht : sourceCollarTime y < centralThickness) :
    WithLp.toLp 2 y∈sourceOpenBlock := by
  apply (sourceOpenBlock_time_iff y).mpr
  refine ⟨hp,fun k => ?_⟩
  by_contra hn
  have hc : -centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y) :=
    (show -centralThickness≤(0:ℝ) by norm_num [centralThickness]).trans (le_of_not_gt hn)
  have hfar := sourceExpandedChild_far_parent k hc
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  rw [he] at hfar
  norm_num [centralThickness] at ht hfar
  linarith

lemma sourceOpenBlock_child_band (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -centralThickness ≤ sourceCollarTime y) (ht : sourceCollarTime y<0) :
    WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)∈sourceOpenBlock := by
  apply (sourceOpenBlock_time_iff _).mpr
  refine ⟨lt_of_lt_of_le (show (0:ℝ)<2*centralThickness by norm_num [centralThickness])
    (sourceExpandedChild_far_parent k hy),fun j => ?_⟩
  have he : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  by_cases hkj : k=j
  · rw [←hkj,he]
    exact ht
  · exact (sourceExpandedChild_other k j hkj (show -centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm
        (sourceChildCoordinates (actualChildSign k) y)) by rw [he]; exact hy)).trans
      (by norm_num [centralThickness])

lemma physicalBlockRegion_mem_closure_openBlock {y : Fin 3 → ℝ}
    (hy : y∈physicalBlockRegion) :
    y∈closure ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) := by
  obtain ⟨hp,hc⟩ := (physicalBlockRegion_time_iff y).mp hy
  by_cases h0 : sourceCollarTime y=0
  · let g : ℝ → (Fin 3 → ℝ) := fun t => sourceAngularCollar t (sourcePhysicalAngles y)
    have hg : Continuous g := continuous_uncurry_sourceAngularCollar.comp
      (continuous_id.prodMk continuous_const)
    have hz : (0:ℝ)∈closure (Ioo 0 centralThickness) := by
      rw [closure_Ioo (show (0:ℝ)≠centralThickness by norm_num [centralThickness])]
      exact ⟨le_rfl,by norm_num [centralThickness]⟩
    have hin : g '' Ioo 0 centralThickness ⊆ (WithLp.toLp 2) ⁻¹' sourceOpenBlock := by
      rintro _ ⟨t,ht,rfl⟩
      have he := sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
        ⟨by linarith [ht.1],ht.2.le.trans (by norm_num [centralThickness])⟩) (sourcePhysicalAngles y)
      exact sourceOpenBlock_parent_band (by dsimp [g]; rw [he]; exact ht.1) (by dsimp [g]; rw [he]; exact ht.2)
    have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
    have he := sourcePhysicalCoordinates_right
      (show sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100) by rw [h0]; norm_num)
    rw [h0] at he
    simpa only [g,he] using hmem
  · by_cases hchild : ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≠0
    · exact subset_closure ((sourceOpenBlock_time_iff y).mpr
        ⟨lt_of_le_of_ne hp (Ne.symm h0),fun k => lt_of_le_of_ne (hc k) (hchild k)⟩)
    · push Not at hchild
      obtain ⟨k,hk⟩ := hchild
      let z := (sourceChildHomeomorph (actualChildSign k)).symm y
      let g : ℝ → (Fin 3 → ℝ) := fun t => sourceChildCoordinates (actualChildSign k)
        (sourceAngularCollar t (sourcePhysicalAngles z))
      have hg : Continuous g := (sourceChildCoordinates_contDiff _).continuous.comp
        (continuous_uncurry_sourceAngularCollar.comp (continuous_id.prodMk continuous_const))
      have hz : (0:ℝ)∈closure (Ioo (-centralThickness) 0) := by
        rw [closure_Ioo (show -centralThickness≠(0:ℝ) by norm_num [centralThickness])]
        exact ⟨by norm_num [centralThickness],le_rfl⟩
      have hin : g '' Ioo (-centralThickness) 0 ⊆ (WithLp.toLp 2) ⁻¹' sourceOpenBlock := by
        rintro _ ⟨t,ht,rfl⟩
        apply sourceOpenBlock_child_band k
        · rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
            ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans ht.1.le,
              ht.2.le.trans (by norm_num)⟩)]
          exact ht.1.le
        · rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
            ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans ht.1.le,
              ht.2.le.trans (by norm_num)⟩)]
          exact ht.2
      have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
      have he := sourcePhysicalCoordinates_right
        (show sourceCollarTime z∈Icc (-(1:ℝ)/100) (1/100) by
          change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈_
          rw [hk]
          norm_num)
      change sourceAngularCollar (sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y))
        (sourcePhysicalAngles z)=z at he
      rw [hk] at he
      have he' : sourceChildCoordinates (actualChildSign k) z=y :=
        (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
      simpa only [g,he,he'] using hmem

theorem physicalBlockRegion_eq_closure_openBlock : physicalBlockRegion=
    closure ((WithLp.toLp 2) ⁻¹' sourceOpenBlock) := by
  apply Subset.antisymm (fun y hy => physicalBlockRegion_mem_closure_openBlock hy)
  apply closure_minimal _ physicalBlockRegion_compact.isClosed
  intro y hy
  obtain ⟨hp,hc⟩ := (sourceOpenBlock_time_iff y).mp hy
  exact (physicalBlockRegion_time_iff y).mpr ⟨hp.le,fun k => (hc k).le⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExtendedBox_mono {l r l' r' : ℝ} (hl : l'≤l) (hr : r ≤ r') :
    sourceExtendedBox l r ⊆ sourceExtendedBox l' r' := by
  intro x hx
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,ha,hb⟩

lemma sourceCollarPieces_aedisjoint {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Pairwise (fun k m : Fin 4 × Fin 4 => AEDisjoint volume
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r)
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r)) := by
  intro k m hkm
  have hn : ∀ᵐ y : Fin 3 → ℝ, y∉
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r) ∩
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r) := by
    filter_upwards [sourceCollar_open_charts_ae] with y hy hm
    obtain ⟨⟨z,hz,hzy⟩,w,hw,hwy⟩ := hm
    have hyb := sourceCollarClosedPiece_subset (l:=-(1:ℝ)/100) (r:=1/100)
      le_rfl le_rfl k.1 k.2 ⟨z,sourceExtendedBox_mono hl hr hz,hzy⟩
    obtain ⟨i,j,x,hx,hxy⟩ := hy hyb
    obtain ⟨hik,hjk⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx
      (sourceExtendedBox_mono hl hr hz) (hxy.trans hzy.symm)
    obtain ⟨him,hjm⟩ := sourceCollarPiece_open_unique i j m.1 m.2 hx
      (sourceExtendedBox_mono hl hr hw) (hxy.trans hwy.symm)
    exact hkm (Prod.ext (hik.symm.trans him) (hjk.symm.trans hjm))
  simpa only [AEDisjoint,ae_iff,not_not,Set.ofPred_mem_eq] using hn

theorem sourceClosedCollarBand_measure_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    volume.restrict (sourceClosedCollarBand l r)=
      ∑ i : Fin 4,∑ j : Fin 4,
        volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r) := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  have he : (⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r)=
      ⋃ k : Fin 4 × Fin 4,sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r := by
    ext x
    simp
  rw [he,Measure.restrict_iUnion_ae (sourceCollarPieces_aedisjoint hl hr)
    (fun k => (sourceCollarClosedPiece_measurable l r k.1 k.2).nullMeasurableSet),
    Measure.sum_fintype,Fintype.sum_prod_type]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalAttachedWeakPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix UnitAddTorus

lemma smoothCollarTrace_eq_zero (s : Fin 3 → ℝ) (t : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hz : ∀ θ : UnitAddTorus (Fin 2),φ (sourceAngularCollar t θ)=0) :
    smoothCollarTrace s t hφ=0 := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  ext h
  rw [smoothCollarTrace_fst]
  simp [hz,Complex.ofReal_zero,mFourierCoeff]

lemma physicalSmoothOuterTrace_compact_zero (s : Fin 3 → ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hφs : tsupport φ⊆(WithLp.toLp 2) ⁻¹' sourceOpenBlock) (i : Fin 3) :
    physicalSmoothOuterTrace s hφ i=0 := by
  revert i
  refine Fin.cases ?_ (fun k => ?_)
  · apply smoothCollarTrace_eq_zero
    intro θ
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := (sourceOpenBlock_time_iff _).mp (hφs h)
    rw [sourceAngular_time (by norm_num)] at hb
    exact (lt_irrefl 0) hb.1
  · apply smoothCollarTrace_eq_zero
    intro θ
    change φ (sourceChildCoordinates (actualChildSign k) (sourceAngularCollar 0 θ))=0
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := ((sourceOpenBlock_time_iff _).mp (hφs h)).2 k
    have he : (sourceChildHomeomorph (actualChildSign k)).symm
        (sourceChildCoordinates (actualChildSign k) (sourceAngularCollar 0 θ))=
        sourceAngularCollar 0 θ :=
      (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply _
    rw [he,sourceAngular_time (by norm_num)] at hb
    exact (lt_irrefl 0) hb

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FacePasting
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix

variable {E : Type*}

lemma sourceFacePasteList_local (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (y : Coord3)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧ sourceFacePasteList B v ks y=B k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · exact ⟨k,List.mem_cons_self,hk,by rw [sourceFacePasteList_cons,ite_eq_left hk]⟩
    · obtain ⟨l,hl,hly⟩ := hy
      have hl' : l∈ks := (List.mem_cons.mp hl).resolve_left (by rintro rfl; exact hk hly)
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,hl',hly⟩
      exact ⟨l,List.mem_cons_of_mem _ hl,hly,by rw [sourceFacePasteList_cons,ite_eq_right hk,he]⟩

lemma sourceFacePasteList_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (hk : (i,j)∈ks) :
    sourceFacePasteList B v ks (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) := by
  obtain ⟨k,_,hy,he⟩ := sourceFacePasteList_local B v ks _
    ⟨(i,j),hk,⟨x,sourceCollarOpenBox_subset hx,rfl⟩⟩
  obtain ⟨z,hz,hze⟩ := hy
  obtain ⟨hi,hj⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx hz hze.symm
  simpa only [←hi,←hj] using he

lemma sourceFacePaste_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    sourceFacePaste B v (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) :=
  sourceFacePasteList_open B v _ i j hx (by simp)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalNullTransport
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma ae_image_of_differentiable {f : Coord3 → Coord3} {S : Set Coord3}
    (hS : MeasurableSet S) (hI : MeasurableSet (f '' S)) (hf : DifferentiableOn ℝ f S) {P : Coord3 → Prop}
    (hP : ∀ᵐ x ∂volume.restrict S,P (f x)) :
    ∀ᵐ y ∂volume.restrict (f '' S),P y := by
  have hn : volume {x | x∈S ∧ ¬ P (f x)}=0 := by
    rw [ae_restrict_iff' hS,ae_iff] at hP
    simpa using hP
  have hn' := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (hf.mono (show {x | x∈S ∧ ¬ P (f x)}⊆S from fun x hx => hx.1)) hn
  rw [ae_iff,Measure.restrict_apply' hI]
  apply le_antisymm _ bot_le
  have he : {y | ¬P y} ∩ f '' S ⊆ f '' {x | x∈S ∧ ¬P (f x)} := by
    rintro y ⟨hy,x,hx,rfl⟩
    exact ⟨x,⟨hx,hy⟩,rfl⟩
  exact (measure_mono he).trans hn'.le

lemma sourceClosedCollarBand_ae_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {P : Coord3 → Prop}
    (hP : ∀ i j : Fin 4,∀ᵐ x ∂volume.restrict (sourceExtendedBox l r),
      P (sourceCollarPiece i j x)) :
    ∀ᵐ y ∂volume.restrict (sourceClosedCollarBand l r),P y := by
  rw [sourceClosedCollarBand_measure_faces hl hr]
  simp only [ae_finsetSum_measure_iff,Finset.mem_univ,true_implies]
  intro i j
  exact ae_image_of_differentiable measurableSet_Icc (sourceCollarClosedPiece_measurable l r i j)
    (fun x _ => (sourceCollarPiece_hasFDeriv i j x).differentiableAt.differentiableWithinAt)
    (hP i j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralAffineCovector
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusRealContinuation_spectral_eventually {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (torusSpectralSynthesis s f)=ᶠ[𝓝 x]
      (fun y => (endFlatPoisson s f y).re) := by
  filter_upwards [(axial_halfspace_open 0).mem_nhds hx] with y hy
  rw [torusRealContinuation_spectral hs f hy,endFlatPoisson_eq]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma variableCollarField_open (u : Coord3 → Fin 2 → ℝ) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarField u a b (sourceCollarPiece i j x)=
      u (flatEndCoordinates a b (sourceFaceAngles i j x)) := by
  rw [variableCollarField,sourceFacePaste_open _ _ i j hx]
  simp only [variableFaceField,sourceCollarInverse_point i j hx]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_FiniteEndPhysicalH1
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

theorem compact_localLip_H1_pi {u : Coord3 → ℝ}
    (hu : ∀ x,LocalLipAt u x) {R : ℝ} (hR : R<3)
    (hs : ∀ x,R<‖WithLp.toLp 2 x‖ → u x=0) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=u (WithLp.ofLp x) ∧ ∀ i,
        weakGradient w x i=lineDeriv ℝ u (WithLp.ofLp x) (Pi.single i 1)) := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hh (x : R3) : LocalLipAt (u ∘ E) x :=
    (hu (E x)).comp (E.toContinuousLinearMap.lipschitz.locallyLipschitz x)
  have hz (x : R3) (hx : R<‖x‖) : (u ∘ E) x=0 := hs (E x) hx
  obtain ⟨K,hK⟩ := compact_locallyLipschitz hh (bounded_support_compact hz)
  obtain ⟨w,hw,he⟩ := compact_lipschitz_H1 hK hR hz
  refine ⟨w,hw,?_⟩
  filter_upwards [he] with x hx
  refine ⟨hx.1,fun i => (hx.2 i).trans ?_⟩
  unfold lineDeriv
  congr 1

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatEndCoordinates_shift (a b T : ℝ) (n : Fin 2 → ℤ) (x : Coord3) :
    flatEndCoordinates a b (x+angularShift T n)=flatEndCoordinates a b x+angularShift T n := by
  ext i
  fin_cases i <;> simp [flatEndCoordinates,angularShift]

lemma AngularPeriodic.flatEnd {E : Type*} {f : Coord3 → E} {T : ℝ}
    (hp : AngularPeriodic T f) (a b : ℝ) :
    AngularPeriodic T (fun x => f (flatEndCoordinates a b x)) := by
  intro n x
  change f (flatEndCoordinates a b (x+angularShift T n))=f (flatEndCoordinates a b x)
  rw [flatEndCoordinates_shift,hp n (flatEndCoordinates a b x)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageOriginalH10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

lemma voltageComponentJetCLM_ae (μ : Measure Coord3) (U : Set Coord3) (j : Fin 2)
    (z : VoltageJetSpace μ U) :
    voltageComponentJetCLM μ U j z=ᵐ[μ.restrict U]
      fun x => WithLp.toLp 2 (Fin.cases (z.1 x j) (fun i => z.2 x (i,j))) := by
  have h1 := (voltageValueComponentJet j).coeFn_compLpL (p:=2) (μ:=μ.restrict U) z.1
  have h2 := (voltageGradientComponentJet j).coeFn_compLpL (p:=2) (μ:=μ.restrict U) z.2
  have ha := Lp.coeFn_add ((voltageValueComponentJet j).compLpL 2 (μ.restrict U) z.1)
    ((voltageGradientComponentJet j).compLpL 2 (μ.restrict U) z.2)
  filter_upwards [h1,h2,ha] with x h1 h2 ha
  change (((voltageValueComponentJet j).compLpL 2 (μ.restrict U) z.1)+
    ((voltageGradientComponentJet j).compLpL 2 (μ.restrict U) z.2)) x=_
  rw [ha,Pi.add_apply,h1,h2]
  ext i
  refine Fin.cases ?_ (fun k => ?_) i <;>
    simp [voltageValueComponentJet,voltageGradientComponentJet]

lemma voltageOriginalJetCLM_ae {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2)
    (z : VoltageJetSpace volume U) :
    voltageOriginalJetCLM hU j z=ᵐ[ballMeasure] fun x =>
      if WithLp.ofLp x∈U then WithLp.toLp 2
        (Fin.cases (z.1 (WithLp.ofLp x) j) (fun i => z.2 (WithLp.ofLp x) (i,j))) else 0 := by
  have he := lpZeroExtensionCLM_ae_of_ae hU
    (voltageComponentJetCLM volume U j z) (voltageComponentJetCLM_ae volume U j z)
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp he
  have hc := Lp.coeFn_compMeasurePreserving
    (lpZeroExtensionCLM hU (voltageComponentJetCLM volume U j z))
    (PiLp.volume_preserving_ofLp (Fin 3))
  have hr := lpRestrictionCLM_ae ball
    ((Lp.compMeasurePreservingₗᵢ ℝ
      (WithLp.ofLp : R3 → Coord3)
      (PiLp.volume_preserving_ofLp (Fin 3)))
      (lpZeroExtensionCLM hU (voltageComponentJetCLM volume U j z)))
  apply hr.trans
  apply ae_restrict_of_ae
  filter_upwards [hc,hp] with x hc hp
  apply hc.trans
  rw [hp]
  by_cases hx : WithLp.ofLp x∈U <;> simp [hx]

lemma voltage_component_smoothJet {v : Coord3 → Fin 2 → ℝ}
    (hv : Differentiable ℝ v) (j : Fin 2) (x : R3) :
    smoothJet (fun x : R3 => v (WithLp.ofLp x) j) x=
      WithLp.toLp 2 (Fin.cases (v (WithLp.ofLp x) j)
        (fun i => voltageGradient v (WithLp.ofLp x) (i,j))) := by
  ext k
  refine Fin.cases rfl (fun i => ?_) k
  change gradient (fun x : R3 => v (WithLp.ofLp x) j) x i=_
  have herr : gradient (fun x : R3 => v (WithLp.ofLp x) j) x i=
      fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x (EuclideanSpace.single i 1) := by
    have h : inner ℝ (EuclideanSpace.single i 1)
        (gradient (fun x : R3 => v (WithLp.ofLp x) j) x)=
        fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x (EuclideanSpace.single i 1) := by
      simp only [inner_gradient_right,RCLike.conj_to_real]
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using h
  rw [herr]
  let P : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hd := ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (P x)
    (hv (P x)).hasFDerivAt).comp x P.hasFDerivAt
  have hP : (P : R3 → Coord3)=WithLp.ofLp := rfl
  rw [show fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x=
    (ContinuousLinearMap.proj j).comp ((fderiv ℝ v (P x)).comp P.toContinuousLinearMap) from by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_assoc,ContinuousLinearMap.proj_apply,hP] using hd.fderiv]
  rfl

lemma voltageOriginalJetCLM_compact {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2)
    {z : VoltageJetSpace volume U} (hz : z∈compactVoltageJets volume U) :
    voltageOriginalJetCLM hU j z∈zeroTraceAmbient := by
  obtain ⟨v,hv,hvc,hvs,hm,hg,rfl⟩ := hz
  let P : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hP : (P : R3 → Coord3)=WithLp.ofLp := rfl
  let f : R3 → ℝ := fun x => v (WithLp.ofLp x) j
  have hf : ContDiff ℝ (↑(⊤:ℕ∞)) f := by
    simpa only [Function.comp_def,hP] using
      (((contDiff_apply ℝ ℝ j).comp hv).comp P.contDiff)
  have hfc : HasCompactSupport f := by
    simpa only [Function.comp_def,show (P.toHomeomorph : R3 → Coord3)=WithLp.ofLp from rfl] using
      (hvc.comp_left (g:=fun w : Fin 2 → ℝ => w j) rfl).comp_homeomorph P.toHomeomorph
  have hfsU : tsupport f⊆(WithLp.ofLp : R3 → Coord3)⁻¹' U := by
    intro x hx
    have hs := tsupport_comp_subset_preimage (fun y : Coord3 => v y j) P.continuous
    have hm : P x∈tsupport (fun y : Coord3 => v y j) := hs hx
    exact hvs ((tsupport_comp_subset (g:=fun w : Fin 2 → ℝ => w j) rfl v) hm)
  have hfs : tsupport f⊆ball := by
    intro x hx
    simpa only [WithLp.toLp_ofLp] using hUb (WithLp.ofLp x) (hfsU hx)
  have hm' := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hm.coeFn_toLp)
  have hg' := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hg.coeFn_toLp)
  have he : voltageOriginalJetCLM hU j (hm.toLp _,hg.toLp _)=(smoothH1 f hf).val := by
    apply Lp.ext
    filter_upwards [voltageOriginalJetCLM_ae hU j (hm.toLp _,hg.toLp _),
      ae_restrict_of_ae hm',ae_restrict_of_ae hg',(smoothJet_memLp hf).coeFn_toLp]
      with x hx hm hg hfx
    change _=(smoothJet_memLp hf).toLp _ x
    rw [hfx,hx]
    by_cases hu : WithLp.ofLp x∈U
    · rw [ite_eq_left hu,hm hu,hg hu]
      exact (voltage_component_smoothJet (hv.differentiable (by simp)) j x).symm
    · rw [ite_eq_right hu]
      exact (smoothJet_zero_of_notMem_support (fun hh => hu (hfsU hh))).symm
  rw [he]
  exact smoothH1_mem_H10 f hf hfc hfs

theorem voltageOriginalJetCLM_zeroTrace {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2)
    {z : VoltageJetSpace volume U} (hz : z∈zeroVoltageJets volume U) :
    voltageOriginalJetCLM hU j z∈zeroTraceAmbient := by
  exact closure_minimal
    (fun z hz => voltageOriginalJetCLM_compact hU hUb j hz)
    ((Submodule.isClosed_topologicalClosure _).preimage
      (voltageOriginalJetCLM hU j).continuous) hz

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_OriginalPairVoltage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma voltageGradient_component {v : Coord3 → Fin 2 → ℝ} {y : Coord3}
    (hv : DifferentiableAt ℝ v y) (i : Fin 3) (j : Fin 2) :
    (voltageGradient v y) (i,j)=fderiv ℝ (fun x => v x j) y (Pi.single i 1) := by
  have he : fderiv ℝ (fun x => v x j) y=(ContinuousLinearMap.proj j).comp (fderiv ℝ v y) :=
    ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp y hv.hasFDerivAt).fderiv
  rw [he]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOuterTrace
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

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_9
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_9
lemma smoothOuterFourierL_apply (i : Fin 3) (φ : SmoothScalar (Fin 3 → ℝ)) (h : TorusModes) :
    smoothOuterFourierL i φ h=mFourierCoeff (fun θ => (φ.val (physicalOuterBoundary i θ):ℂ)) h := by
  change (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (smoothOuterContinuousL i φ)) h=_
  rw [mFourierBasis_repr,mFourierCoeff_toLp]
  rfl

lemma physicalOuterTrace_smooth (i : Fin 3) {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (s : Fin 3 → ℝ) :
    physicalOuterTraceCLM i (piSmoothH1 hφ)=(physicalSmoothOuterTrace s hφ i).val 0 := by
  have he := (dense_linear_observable_extension smoothPiH1L (smoothOuterFourierL i)
    smoothPiH1L_dense (smoothOuterFourierL_bound i)).choose_spec ⟨φ,hφ⟩
  change physicalOuterTraceCLM i (piSmoothH1 hφ)=smoothOuterFourierL i ⟨φ,hφ⟩ at he
  rw [he]
  ext h
  rw [smoothOuterFourierL_apply]
  refine Fin.cases ?_ (fun k => ?_) i
  · exact (smoothCollarTrace_fst s 0 hφ h).symm
  · exact (smoothCollarTrace_fst s 0 (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) h).symm

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothRepresentativeGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open TopologicalSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [IsOpenPosMeasure μ]

omit [NormedSpace ℝ E] [BorelSpace E] [IsOpenPosMeasure μ] in
lemma ae_on_open_cover {ι : Type*} (O : ι → Set E) (hO : ∀ i,IsOpen (O i))
    (P : E → Prop) (hP : ∀ i,∀ᵐ x∂μ.restrict (O i),P x) :
    ∀ᵐ x∂μ.restrict (⋃ i,O i),P x := by
  obtain ⟨T,hT,he⟩ := isOpen_iUnion_countable O hO
  rw [←he]
  exact (ae_restrict_biUnion_iff O hT P).mpr (fun i _ => hP i)

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralCorrectedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma H1JetOn.value_cartesian {w : H1} {D : Set Coord3} {f : R3 → JetFiber}
    (hw : H1JetOn w D f) (hDb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    ∀ᵐ y : Coord3,y∈D → weakValue w (WithLp.toLp 2 y)=f (WithLp.toLp 2 y) 0 := by
  have hh := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp hw)
  filter_upwards [hh] with y hy hyD
  exact congrArg (fun z : JetFiber => z 0) (hy (hDb y hyD) hyD)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma correctedEndValue_face {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) (a b : ℝ) (m n : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    fullAttachedEndValue s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
      attachedPeriodicField (branchCorrection i z j) a b (sourceCollarPiece m n x)=
      variableCollarField (fun y j => branchSplicedField i z j y) a b (sourceCollarPiece m n x) j := by
  rw [variableCollarField_open _ a b m n hx]
  change (attachedEndPoissonField s (f j) a b 0 (sourceCollarPiece m n x)).re+
    (centralBasisSlopes j i)*(a*(sourceCollarTime (sourceCollarPiece m n x)-b))+
    physicalPeriodicField (fun y => branchCorrection i z j (flatEndCoordinates a b y)) (sourceCollarPiece m n x)=_
  rw [attachedEndPoissonField_piece _ _ _ _ _ _ (sourceCollarOpenBox_subset hx),
    physicalPeriodicField_piece ((branchCorrection_periodic i z j).flatEnd a b) m n
      (sourceCollarOpenBox_subset hx),sourceCollarPiece_time_open hx]
  unfold branchSplicedField torusAffineField
  rw [(torusRealContinuation_spectral_eventually hs (f j)
    (show 0<(flatEndCoordinates a b (sourceFaceAngles m n x)) 0 from ht)).eq_of_nhds]
  change _+_+_= (centralBasisSlopes j i)*(a*(x 0-b))+
    (endFlatPoisson s (f j) (endAxialAffine a b (sourceFaceAngles m n x))).re+_
  ring

lemma correctedEndValue_band {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) (a b : ℝ) {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Ioo l r,0<a*(t-b)) :
    ∀ᵐ y∂volume.restrict (sourceClosedCollarBand l r),
      fullAttachedEndValue s (f j) a b (centralBasisSlopes j i) y+
        attachedPeriodicField (branchCorrection i z j) a b y=
        variableCollarField (fun y j => branchSplicedField i z j y) a b y j := by
  apply sourceClosedCollarBand_ae_faces hl hr
  intro m n
  filter_upwards [sourceExtendedBox_open_ae hl hr,sourceExtendedBox_axial_strict_ae l r]
    with x hxo hxt
  exact correctedEndValue_face hs f i z j a b m n hxo (hT _ hxt)

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma parent_open_time {t : ℝ} (ht : t∈Ioo 0 centralThickness) :
    0<z.compression 0*(t-centralThickness) := mul_pos_of_neg_of_neg z.compression_parent (sub_neg.mpr ht.2)
lemma child_open_time (k : Fin 2) {t : ℝ} (ht : t∈Ioo (-centralThickness) 0) :
    0<z.compression k.succ*(t-(-centralThickness)) := mul_pos (z.compression_child k) (sub_pos.mpr ht.1)

lemma endRepresentative_value
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (i : Fin 3) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i → z.correctedEndJet j i (WithLp.toLp 2 y) 0=z.endRepresentative i y j := by
  refine Fin.cases ?_ (fun k => ?_) i
  · have hh := correctedEndValue_band hs (fun j => centralT s 0 (z.p j)) 0 (z.ending 0) j
      (z.compression 0) centralThickness (by norm_num : -(1:ℝ)/100≤0)
      (by norm_num [centralThickness] : centralThickness≤(1:ℝ)/100) (fun t => z.parent_open_time)
    exact (ae_restrict_iff' (physicalEndRegion_compact 0).measurableSet).mp hh
  · have hh := correctedEndValue_band hs (fun j => centralT s k.succ (z.p j)) k.succ (z.ending k.succ) j
      (z.compression k.succ) (-centralThickness) (by norm_num [centralThickness] : -(1:ℝ)/100≤-centralThickness)
      (by norm_num : (0:ℝ)≤1/100) (fun t => z.child_open_time k)
    exact (sourceChildInverse_quasi (actualChildSign k)).ae
      ((ae_restrict_iff' childEndBand_measurable).mp hh)

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTerminalBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma branchSplicedField_terminal {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f)) (j : Fin 2)
    {x : Coord3} (hx : z.R≤x 0) :
    branchSplicedField i z j x=centralBasisSlopes j i*x 0+(mFourierCoeff (f j) 0).re := by
  rw [(branchSplicedField_final i z j (by linarith [z.overlap_lt,z.e_pos])).eq_of_nhds]
  exact congrFun (branchFinitePair_terminal i z x hx) j

lemma variableCollarField_terminal_ae {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f)) (a b : ℝ) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      z.R≤a*(sourceCollarTime y-b) →
      variableCollarField (fun x j => branchSplicedField i z j x) a b y j=
        centralBasisSlopes j i*(a*(sourceCollarTime y-b))+(mFourierCoeff (f j) 0).re := by
  filter_upwards [sourceCollar_open_charts_ae] with y hy hband ht
  obtain ⟨m,n,x,hx,rfl⟩ := hy hband
  rw [variableCollarField_open _ a b m n hx]
  rw [sourceCollarPiece_time_open hx] at ht ⊢
  exact branchSplicedField_terminal i z j ht

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma compression_base (i : Fin 3) :
    z.compression i*(-terminalBase i)=(z.ending i).R+1 := by
  unfold compression terminalBase
  split_ifs <;> field_simp [show centralThickness≠0 by norm_num [centralThickness]]

lemma terminal_affine (i : Fin 3) (j : Fin 2) (t : ℝ) :
    centralBasisSlopes j i*(z.compression i*(t-terminalBase i))+
      (mFourierCoeff (z.traces i j) 0).re=
    z.terminalValue i j+centralBasisSlopes j i*z.compression i*t := by
  have hh := z.compression_base i
  dsimp [terminalValue]
  nlinarith [congrArg (fun r => centralBasisSlopes j i*r) hh]

lemma terminal_band_exists : ∃ η : ℝ,0<η ∧ η < centralThickness ∧
    ∀ i : Fin 3,∀ t : ℝ,|t|≤η → (z.ending i).R<z.compression i*(t-terminalBase i) := by
  have hc (i : Fin 3) : ContinuousAt (fun t : ℝ => z.compression i*(t-terminalBase i)) 0 := by fun_prop
  have hn (i : Fin 3) : ∀ᶠ t : ℝ in 𝓝 0,(z.ending i).R<z.compression i*(t-terminalBase i) := by
    apply (hc i).eventually (lt_mem_nhds ?_)
    simpa only [zero_sub,z.compression_base] using (lt_add_one (z.ending i).R)
  have hall : ∀ᶠ t : ℝ in 𝓝 0,∀ i : Fin 3,(z.ending i).R<z.compression i*(t-terminalBase i) :=
    eventually_all.mpr hn
  obtain ⟨ε,hε,hb⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨min (ε/2) (centralThickness/2),lt_min (by positivity) (by norm_num [centralThickness]),
    (min_le_right _ _).trans_lt (by norm_num [centralThickness]),?_⟩
  intro i t ht
  apply hb ?_ i
  change dist t 0<ε
  rw [Real.dist_eq,sub_zero]
  exact (ht.trans (min_le_left _ _)).trans_lt (by linarith)

lemma endRepresentative_terminal_ae (i : Fin 3) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i →
      (z.ending i).R≤z.compression i*(terminalTime i y-terminalBase i) →
      z.endRepresentative i y j=z.terminalValue i j+
        centralBasisSlopes j i*z.compression i*terminalTime i y := by
  have hh (i : Fin 3) := variableCollarField_terminal_ae i (z.ending i)
    (z.compression i) (terminalBase i) j
  refine Fin.cases ?_ (fun k => ?_) i
  · filter_upwards [hh 0] with y hy he ht
    exact (hy ⟨(show -(1:ℝ)/100≤0 by norm_num).trans he.1,
      he.2.trans (by norm_num [centralThickness])⟩ ht).trans (z.terminal_affine 0 j _)
  · filter_upwards [(sourceChildInverse_quasi (actualChildSign k)).ae (hh k.succ)] with y hy he ht
    exact (hy ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans he.1,
      he.2.trans (by norm_num)⟩ ht).trans (z.terminal_affine k.succ j _)

lemma correctedEndValue_terminal_ae
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i →
      (z.ending i).R≤z.compression i*(terminalTime i y-terminalBase i) →
      z.correctedEndJet j i (WithLp.toLp 2 y) 0=z.terminalValue i j+
        centralBasisSlopes j i*z.compression i*terminalTime i y := by
  filter_upwards [z.endRepresentative_value hs i j,z.endRepresentative_terminal_ae i j]
    with y hv ht hy hT
  exact (hv hy).trans (ht hy hT)

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_OriginalSmoothMultiplier
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

lemma originalMulJetCLM_mem_zero (hs : tsupport χ⊆ball) (u : H1) :
    originalMulJetCLM hχ hc u∈zeroTraceAmbient := by
  have hclosed : IsClosed {u : H1 | originalMulJetCLM hχ hc u∈zeroTraceAmbient} :=
    (Submodule.isClosed_topologicalClosure _).preimage (originalMulJetCLM hχ hc).continuous
  apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hclosed) (smoothH1_dense u)
  rintro v ⟨f,hf,hm,he⟩
  have hv : v=smoothH1 f hf := Subtype.ext he
  rw [hv]
  change originalMulJetCLM hχ hc (smoothH1 f hf)∈zeroTraceAmbient
  rw [originalMulJetCLM_smooth]
  exact smoothH1_mem_H10 (χ*f) (hχ.mul hf) (hc.mul_right) ((tsupport_mul_subset_left).trans hs)

include hχ hc in

theorem original_smooth_mul_exists (hs : tsupport χ⊆ball) (u : H1) :
    ∃ v : H1,v∈H10 ∧ weakValue v=ᵐ[ballMeasure] fun x => χ x*weakValue u x := by
  have hz := originalMulJetCLM_mem_zero hχ hc hs u
  refine ⟨⟨originalMulJetCLM hχ hc u,zeroTraceAmbient_le_H1Space hz⟩,hz,?_⟩
  filter_upwards [originalMulJetCLM_ae hχ hc u] with x hx
  exact congrArg (fun z : JetFiber => z 0) hx

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
lemma LocalLipAt.add {E : Type*} [PseudoMetricSpace E] {f g : E → ℝ} {x : E}
    (hf : LocalLipAt f x) (hg : LocalLipAt g x) : LocalLipAt (fun y => f y+g y) x := by
  exact (localLipAt_of_contDiffAt
    (show ContDiffAt ℝ 1 (fun p : ℝ×ℝ => p.1+p.2) (f x,g x) by fun_prop)).comp
    (f:=fun y => (f y,g y)) (x:=x) (hf.prodMk hg)

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma terminalTime_locallyLipschitz (i : Fin 3) : LocallyLipschitz (terminalTime i) := by
  refine Fin.cases locallyLipschitz_sourceCollarTime (fun k => ?_) i
  exact locallyLipschitz_sourceCollarTime.comp
    ((sourceChildInverse_contDiff (actualChildSign k)).of_le (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by simp)).locallyLipschitz

lemma terminalProfileParent_localLip (η : ℝ) (j : Fin 2) (y : Coord3) :
    LocalLipAt (z.terminalProfileParent η j) y := by
  have hmax : LocallyLipschitz (fun x => max (terminalTime 0 x) 0) :=
    (terminalTime_locallyLipschitz 0).max (LipschitzWith.const (0:ℝ)).locallyLipschitz
  have hcut : ContDiff ℝ 1 (fun t : ℝ => 1-Real.smoothTransition (t/η-1)) :=
    contDiff_const.sub ((Real.smoothTransition.contDiff (n:=1)).comp (by fun_prop))
  exact ((localLipAt_of_contDiffAt (contDiffAt_const (c:=centralBasisSlopes j 0*z.compression 0))).mul
    (hmax y)).mul (hcut.locallyLipschitz.comp (terminalTime_locallyLipschitz 0) y)

lemma terminalProfileChild_localLip (η : ℝ) (j : Fin 2) (k : Fin 2) (y : Coord3) :
    LocalLipAt (z.terminalProfileChild η j k) y := by
  have hmin : LocallyLipschitz (fun x => min (terminalTime k.succ x) 0) :=
    (terminalTime_locallyLipschitz k.succ).min (LipschitzWith.const (0:ℝ)).locallyLipschitz
  have ha : ContDiff ℝ 1 (fun t : ℝ => z.terminalValue k.succ j-z.terminalValue 0 j+
      centralBasisSlopes j k.succ*z.compression k.succ*t) := by fun_prop
  have hb : ContDiff ℝ 1 (fun t : ℝ => Real.smoothTransition (t/η+2)) :=
    (Real.smoothTransition.contDiff (n:=1)).comp (by fun_prop)
  exact LocalLipAt.mul (ha.locallyLipschitz.comp hmin y)
    (hb.locallyLipschitz.comp (terminalTime_locallyLipschitz k.succ) y)

lemma terminalProfile_localLip (η : ℝ) (j : Fin 2) (y : Coord3) :
    LocalLipAt (z.terminalProfile η j) y := by
  change LocalLipAt (fun x => z.terminalProfileParent η j x+∑ k : Fin 2,z.terminalProfileChild η j k x) y
  simp only [Fin.sum_univ_two]
  exact (z.terminalProfileParent_localLip η j y).add
    ((z.terminalProfileChild_localLip η j 0 y).add (z.terminalProfileChild_localLip η j 1 y))

lemma terminalProfileParent_zero_left (η : ℝ) (j : Fin 2) {y : Coord3}
    (hy : terminalTime 0 y≤0) : z.terminalProfileParent η j y=0 := by
  simp [terminalProfileParent,max_eq_right hy]

lemma terminalProfileParent_zero_right {η : ℝ} (hη : 0<η) (j : Fin 2) {y : Coord3}
    (hy : 2*η≤terminalTime 0 y) : z.terminalProfileParent η j y=0 := by
  have hh : 1≤terminalTime 0 y/η-1 := by rw [le_sub_iff_add_le,le_div_iff₀ hη]; linarith
  simp [terminalProfileParent,Real.smoothTransition.one_of_one_le hh]

lemma terminalProfileChild_zero {η : ℝ} (hη : 0<η) (j : Fin 2) (k : Fin 2) {y : Coord3}
    (hy : terminalTime k.succ y≤-2*η) : z.terminalProfileChild η j k y=0 := by
  have hh : terminalTime k.succ y/η+2≤0 := by have hh : terminalTime k.succ y/η≤ -2 := (div_le_iff₀ hη).mpr (by linarith); linarith
  simp [terminalProfileChild,Real.smoothTransition.zero_of_nonpos hh]

lemma terminalTime_far_parent (k : Fin 2) {y : Coord3}
    (hy : -centralThickness≤terminalTime k.succ y) : 2*centralThickness≤terminalTime 0 y := by
  have hh := sourceExpandedChild_far_parent k hy
  change 2*centralThickness≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k))
    ((sourceChildHomeomorph (actualChildSign k)).symm y)) at hh
  simpa only [Homeomorph.apply_symm_apply,terminalTime,Fin.cases_zero] using hh

lemma terminalProfile_zero_outside {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (j : Fin 2) {y : Coord3} (hy : terminalTime 0 y≤0) : z.terminalProfile η j y=0 := by
  rw [terminalProfile,z.terminalProfileParent_zero_left η j hy,zero_add]
  apply Finset.sum_eq_zero
  intro k _
  apply z.terminalProfileChild_zero hη j k
  by_contra hn
  have hc : -centralThickness≤terminalTime k.succ y := by linarith [lt_of_not_ge hn]
  have hh := terminalTime_far_parent k hc
  have : 0 < centralThickness := by norm_num [centralThickness]
  linarith

lemma terminalProfile_H10 {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness) (j : Fin 2) :
    ∃ w : H1,w∈H10 ∧ weakValue w=ᵐ[ballMeasure] fun x => z.terminalProfile η j (WithLp.ofLp x) := by
  have hz (y : Coord3) (hy : 5/2<‖WithLp.toLp 2 y‖) : z.terminalProfile η j y=0 := by
    apply z.terminalProfile_zero_outside hη hηc j
    by_contra hn
    have hd := (sourceCollarTime_pos_iff_domain y).mp (lt_of_not_ge hn)
    have hb := sourceClosure_subset_ball (subset_closure hd)
    simp only [Metric.mem_ball,dist_zero_right] at hb
    linarith
  obtain ⟨w,hw,he⟩ := compact_localLip_H1_pi (z.terminalProfile_localLip η j)
    (R:=5/2) (by norm_num) hz
  exact ⟨w,hw,he.mono (fun _ h => h.1)⟩

lemma terminalProfile_parent_band {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (j : Fin 2) {y : Coord3} (h0 : 0≤terminalTime 0 y) (hy : terminalTime 0 y≤η) :
    z.terminalProfile η j y=centralBasisSlopes j 0*z.compression 0*terminalTime 0 y := by
  have hh : terminalTime 0 y/η-1≤0 := by rw [sub_nonpos,div_le_iff₀ hη]; simpa using hy
  have hz : ∑ k : Fin 2,z.terminalProfileChild η j k y=0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply z.terminalProfileChild_zero hη j k
    by_contra hn
    have hh := terminalTime_far_parent k (show -centralThickness≤terminalTime k.succ y by linarith)
    linarith
  simp [terminalProfile,terminalProfileParent,max_eq_left h0,hz,Real.smoothTransition.zero_of_nonpos hh]

lemma terminalProfile_child_band {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (j : Fin 2) (k : Fin 2) {y : Coord3} (hy : -η≤terminalTime k.succ y) :
    z.terminalProfile η j y=z.terminalValue k.succ j-z.terminalValue 0 j+
      centralBasisSlopes j k.succ*z.compression k.succ*min (terminalTime k.succ y) 0 := by
  have hc : -centralThickness≤terminalTime k.succ y := by linarith
  have hh := terminalTime_far_parent k hc
  have hp := z.terminalProfileParent_zero_right hη j (show 2*η≤terminalTime 0 y by linarith)
  have hb : 1≤terminalTime k.succ y/η+2 := by have hh : -1≤terminalTime k.succ y/η := (le_div_iff₀ hη).mpr (by linarith); linarith
  have ho (l : Fin 2) (hl : l≠k) : z.terminalProfileChild η j l y=0 := by
    apply z.terminalProfileChild_zero hη j l
    have hh := sourceExpandedChild_other k l (Ne.symm hl) hc
    change terminalTime l.succ y< -centralThickness at hh
    linarith
  rw [terminalProfile,hp,zero_add,Finset.sum_eq_single k]
  · simp only [terminalProfileChild,Real.smoothTransition.one_of_one_le hb,mul_one]
  · exact fun l _ hl => ho l hl
  · simp

end PhysicalFiniteEndingData
end ScalarConductivity

end
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

lemma upperTransition_zero_iff (M : ℝ) (hM : 0≤M) (r : ℝ) :
    upperTransition M hM r=0 ↔ r≤M := by
  change smoothTransition (r-M)=0 ↔ r≤M
  rw [smoothTransition.zero_iff_nonpos,sub_nonpos]

lemma upperTransition_deriv_nonneg (M : ℝ) (hM : 0≤M) (r : ℝ) :
    0≤deriv (upperTransition M hM) r := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact smoothTransition.monotone (sub_le_sub_right hxy M)

lemma weakValue_neg (u : H1) : weakValue (-u) =ᵐ[ballMeasure] -weakValue u := by
  filter_upwards [Lp.coeFn_neg u.val] with point hneg
  change jetValue ((-u.val) point) = -jetValue (u.val point)
  rw [hneg,Pi.neg_apply,map_neg]

end ScalarConductivity

end
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

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEuclideanJets
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma weak_partial_of_smooth_representative (f F : WholeL2) {U : Set R3}
    (hU : IsOpen U) (v : R3) (g : R3 → ℝ)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (heq : (f : R3 → ℝ)=ᵐ[volume.restrict U] g)
    (hweak : ∀ ψ : R3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ⊆U → (∫ x,F x*ψ x)=-(∫ x,f x*fderiv ℝ ψ x v)) :
    ∀ᵐ x∂volume,x∈U → F x=fderiv ℝ g x v := by
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hloc := ((Lp.memLp F).locallyIntegrable (by norm_num : (1:ℝ≥0∞)≤2)).sub hdg.locallyIntegrable
  have heq' := (ae_restrict_iff' hU.measurableSet).mp heq
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn U) (by
    intro ψ hψ hc hsp
    have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψF : Integrable (fun x => ψ x*F x) :=
      (hψ.continuous.memLp_of_hasCompactSupport (p := 2) hc).integrable_mul (Lp.memLp F)
    have hψg : Integrable (fun x => ψ x*fderiv ℝ g x v) :=
      (hψ.continuous.mul hdg).integrable_of_hasCompactSupport hc.mul_right
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := ψ) (g := g) (v := v)
      ((hdψ.mul hg.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right)
      hψg ((hψ.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ => hψ.differentiable (by simp) x)
      (fun x _ => hg.differentiable (by simp) x)
    have hreplace : (∫ x,f x*fderiv ℝ ψ x v)=(∫ x,g x*fderiv ℝ ψ x v) := by
      apply integral_congr_ae
      filter_upwards [heq'] with x hx
      by_cases hxu : x∈U
      · rw [hx hxu]
      · have hzero := fderiv_of_notMem_tsupport ℝ (fun hh => hxu (hsp hh))
        rw [hzero]
        simp
    have hw := hweak ψ hψ hc hsp
    simp only [smul_eq_mul,Pi.sub_apply,mul_sub]
    rw [integral_sub hψF hψg]
    have hswap : (∫ x,ψ x*F x)=∫ x,F x*ψ x := by simp only [mul_comm]
    rw [hswap,hw,hreplace,he]
    simp only [mul_comm,sub_self])
  filter_upwards [hz] with x hx hxu
  exact sub_eq_zero.mp (hx hxu)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalSmoothWeakDerivative
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

lemma contDiffOn_local_global {g : R3 → ℝ} {U : Set R3}
    (hU : IsOpen U) (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U) {x : R3} (hx : x∈U) :
    ∃ (V : Set R3) (G : R3 → ℝ),IsOpen V ∧ x∈V ∧ V⊆U ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) G ∧ EqOn G g V := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton
    Metric.isOpen_ball (Metric.isBounded_ball (x := x) (r := r))
    (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have he : (fun y => χ y*g y)=ᶠ[𝓝 x] g := by
    filter_upwards [hχone x (mem_singleton x)] with y hy
    simp only [hy,one_mul]
  obtain ⟨V,hVs,hV,hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) he)
  exact ⟨V,fun y => χ y*g y,hV,hxV,fun _ hy => (hVs hy).1,
    smooth_mul_of_support_in_open hU hg hχ (hχs.trans hball),fun _ hy => (hVs hy).2⟩

theorem weak_partial_of_contDiffOn_representative (f F : WholeL2) {U : Set R3}
    (hU : IsOpen U) (v : R3) (g : R3 → ℝ)
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U)
    (heq : (f : R3 → ℝ)=ᵐ[volume.restrict U] g)
    (hweak : ∀ ψ : R3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ⊆U → (∫ x,F x*ψ x)=-(∫ x,f x*fderiv ℝ ψ x v)) :
    ∀ᵐ x∂volume,x∈U → F x=fderiv ℝ g x v := by
  classical
  have hlocal (x : U) := contDiffOn_local_global hU hg x.property
  choose V G hV hxV hVU hG he using hlocal
  have hcover : (⋃ x : U,V x)=U := by
    apply Subset.antisymm (iUnion_subset (fun x => hVU x))
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hp (x : U) : ∀ᵐ y∂volume.restrict (V x),F y=fderiv ℝ g y v := by
    have heq' : (f : R3 → ℝ)=ᵐ[volume.restrict (V x)] G x := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hVU x) heq,
        ae_restrict_mem (hV x).measurableSet] with y hy hyV
      exact hy.trans (he x hyV).symm
    have hw := weak_partial_of_smooth_representative f F (hV x) v (G x) (hG x) heq'
      (fun ψ hψ hc hsp => hweak ψ hψ hc (hsp.trans (hVU x)))
    filter_upwards [ae_restrict_of_ae hw,ae_restrict_mem (hV x).measurableSet] with y hy hyV
    rw [hy hyV]
    exact congrArg (fun D : R3 →L[ℝ] ℝ => D v)
      ((show G x=ᶠ[𝓝 y] g from Filter.Eventually.mono ((hV x).mem_nhds hyV) (fun t ht => he x ht)).fderiv_eq)
  have hh := ae_on_open_cover volume V hV (fun y => F y=fderiv ℝ g y v) hp
  rw [hcover] at hh
  exact (ae_restrict_iff' hU.measurableSet).mp hh

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma original_zero_pairing (f : Lp ℝ 2 ballMeasure) (ψ : R3 → ℝ) :
    (∫ x,lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) f x*ψ x)=
      ∫ x,f x*ψ x∂ballMeasure := by
  change _ = ∫ x in ball,f x*ψ x
  rw [←integral_indicator (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)]
  apply integral_congr_ae
  filter_upwards [lpZeroExtensionCLM_ae (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) f] with x hx
  rw [hx]
  by_cases h : x∈ball
  · simp only [indicator_of_mem h]
    rfl
  · simp only [indicator_of_notMem h,zero_mul]

lemma originalWholeValue_ae (u : H1) : originalWholeValue u=ᵐ[volume] ball.indicator (weakValue u) :=
  lpZeroExtensionCLM_ae_of_ae _ _ (weakValueL_apply_ae u)

lemma originalWholeDirection_ae (u : H1) (v : R3) :
    originalWholeDirection u v=ᵐ[volume] ball.indicator (fun x => inner ℝ v (weakGradient u x)) :=
  lpZeroExtensionCLM_ae_of_ae _ _ (weakDirectionL_apply_ae u v)

lemma originalWhole_weak_partial (u : H1) (v : R3) (ψ : R3 → ℝ)
    (hψ : ContDiff ℝ (↑(⊤:ℕ∞)) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball) :
    (∫ x,originalWholeDirection u v x*ψ x)=
      -(∫ x,originalWholeValue u x*fderiv ℝ ψ x v) := by
  have he := weak_integration_by_parts u hψ hc hs v
  rw [L2.inner_def,L2.inner_def] at he
  change (∫ x,lpZeroExtensionCLM _ (weakDirectionL v u) x*ψ x)=
    -(∫ x,lpZeroExtensionCLM _ (weakValueL u) x*fderiv ℝ ψ x v)
  rw [original_zero_pairing,original_zero_pairing]
  have hv := (weakValueL_apply_ae (smoothH1 ψ hψ)).trans (smoothH1_value ψ hψ)
  have hd : (weakDirectionL v (smoothH1 ψ hψ) : R3 → ℝ)=ᵐ[ballMeasure]
      (fun x => fderiv ℝ ψ x v) := by
    filter_upwards [weakDirectionL_apply_ae (smoothH1 ψ hψ) v,smoothH1_gradient ψ hψ] with x hx hy
    simp only [hx,hy,inner_gradient_right,RCLike.conj_to_real]
  calc
    _ = ∫ x,inner ℝ (weakValueL (smoothH1 ψ hψ) x) (weakDirectionL v u x)∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp only [hx,Real.inner_apply,mul_comm]
    _ = _ := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hd] with x hx
      simp only [hx,Real.inner_apply,mul_comm]

theorem original_contDiffOn_representative_gradient (u : H1) {U : Set R3}
    (hU : IsOpen U) (hUb : U⊆ball) (g : R3 → ℝ)
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U)
    (heq : weakValue u=ᵐ[volume.restrict U] g) :
    ∀ᵐ x∂volume,x∈U → weakGradient u x=gradient g x := by
  have hf : (originalWholeValue u : R3 → ℝ)=ᵐ[volume.restrict U] g := by
    filter_upwards [ae_restrict_of_ae (originalWholeValue_ae u),heq,ae_restrict_mem hU.measurableSet] with x hx he hxU
    rw [hx,indicator_of_mem (hUb hxU),he]
  have hi (i : Fin 3) := weak_partial_of_contDiffOn_representative
    (originalWholeValue u) (originalWholeDirection u (EuclideanSpace.single i 1)) hU
    (EuclideanSpace.single i 1) g hg hf
    (fun ψ hψ hc hsp => originalWhole_weak_partial u _ ψ hψ hc (hsp.trans hUb))
  have hd (i : Fin 3) := originalWholeDirection_ae u (EuclideanSpace.single i 1)
  filter_upwards [ae_all_iff.mpr hi,ae_all_iff.mpr hd] with x hx hd hxU
  ext i
  have he := hx i hxU
  rw [hd i,indicator_of_mem (hUb hxU)] at he
  have hgr : inner ℝ (EuclideanSpace.single i 1) (gradient g x)=fderiv ℝ g x (EuclideanSpace.single i 1) := by
    simp only [inner_gradient_right,RCLike.conj_to_real]
  rw [←hgr] at he
  simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using he

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_OriginalGradientLocality
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

lemma original_local_constant_gradient (u : H1) {U : Set R3}
    (hU : IsOpen U) (hUb : U⊆ball) (c : ℝ)
    (hv : ∀ᵐ x∂ballMeasure,x∈U → weakValue u x=c) :
    ∀ᵐ x∂ballMeasure,x∈U → weakGradient u x=0 := by
  have he : weakValue u=ᵐ[volume.restrict U] fun _ => c := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUb hv,ae_restrict_mem hU.measurableSet] with x hx hm
    exact hx hm
  have hg := original_contDiffOn_representative_gradient u hU hUb (fun _ => c) contDiffOn_const he
  filter_upwards [ae_restrict_of_ae hg] with x hx hm
  rw [hx hm]
  exact gradient_fun_const x c

lemma original_local_value_difference_gradient (u v : H1) {U : Set R3}
    (hU : IsOpen U) (hUb : U⊆ball) (c : ℝ)
    (hv : ∀ᵐ x∂ballMeasure,x∈U → weakValue u x-weakValue v x=c) :
    ∀ᵐ x∂ballMeasure,x∈U → weakGradient u x=weakGradient v x := by
  have he : ∀ᵐ x∂ballMeasure,x∈U → weakValue (u-v) x=c := by
    filter_upwards [hv,weakValue_sub u v] with x hx hs hm
    rw [hs]
    exact hx hm
  filter_upwards [original_local_constant_gradient (u-v) hU hUb c he,weakGradient_sub u v]
    with x hx hs hm
  have hh := hx hm
  rw [hs] at hh
  exact sub_eq_zero.mp hh

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOpenVoltage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma physicalOpenBlock_subset : physicalOpenBlock⊆physicalBlockRegion := by
  rw [physicalBlockRegion_eq_closure_openBlock]
  exact subset_closure

lemma physicalOpenBlock_subset_ball {y : Coord3} (hy : y∈physicalOpenBlock) :
    WithLp.toLp 2 y∈ball := physicalBlockRegion_subset_ball (physicalOpenBlock_subset hy)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
attribute [local instance] Classical.propDecidable
namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma source_patch_gradient {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (q W : H1) (j : Fin 2)
    (hv : ∀ᵐ x∂ballMeasure,weakValue W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakValue q x-z.terminalValue 0 j
      else z.terminalProfile η j (WithLp.ofLp x)) :
    ∀ᵐ x∂ballMeasure,weakGradient W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakGradient q x else 0 := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let U : Set R3 := E ⁻¹' physicalOpenBlock
  have hU : IsOpen U := physicalOpenBlock_open.preimage E.continuous
  have hUb : U⊆ball := fun x hx => physicalOpenBlock_subset_ball hx
  have hinside : ∀ᵐ x∂ballMeasure,x∈U → weakGradient W x=weakGradient q x := by
    apply original_local_value_difference_gradient W q hU hUb (-z.terminalValue 0 j)
    filter_upwards [hv] with x hx hm
    change WithLp.ofLp x∈physicalOpenBlock at hm
    rw [hx,ite_eq_left hm]
    ring
  let O : Set R3 := ball∩{x | terminalTime 0 (E x)<0}
  have hO : IsOpen O := Metric.isOpen_ball.inter
    (isOpen_lt ((terminalTime_locallyLipschitz 0).continuous.comp E.continuous) continuous_const)
  have hout : ∀ᵐ x∂ballMeasure,x∈O → weakGradient W x=0 := by
    apply original_local_constant_gradient W hO inter_subset_left 0
    filter_upwards [hv] with x hx hm
    have hn : E x∉physicalOpenBlock := by
      intro hh
      have hh := (sourceOpenBlock_time_iff (E x)).mp hh
      exact (not_lt.mpr hm.2.le) hh.1
    change WithLp.ofLp x∉physicalOpenBlock at hn
    rw [hx,ite_eq_right hn]
    exact z.terminalProfile_zero_outside hη hηc j hm.2.le
  let C : Fin 2 → Set R3 := fun k => ball∩{x | 0<terminalTime k.succ (E x)}
  have hC (k : Fin 2) : IsOpen (C k) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const ((terminalTime_locallyLipschitz k.succ).continuous.comp E.continuous))
  have hchild (k : Fin 2) : ∀ᵐ x∂ballMeasure,x∈C k → weakGradient W x=0 := by
    apply original_local_constant_gradient W (hC k) inter_subset_left (z.terminalValue k.succ j-z.terminalValue 0 j)
    filter_upwards [hv] with x hx hm
    have hn : E x∉physicalOpenBlock := by
      intro hh
      have hh := (sourceOpenBlock_time_iff (E x)).mp hh
      exact (not_lt.mpr hm.2.le) (hh.2 k)
    change WithLp.ofLp x∉physicalOpenBlock at hn
    have hm' : 0<terminalTime k.succ (WithLp.ofLp x) := hm.2
    rw [hx,ite_eq_right hn,z.terminalProfile_child_band hη hηc j k (by linarith)]
    rw [min_eq_right hm'.le]
    ring
  have h0 := sourceColevel_ae_ne (show (0:ℝ)∈Icc (-(1:ℝ)/100) (1/100) by norm_num)
  have hh (i : Fin 3) : ∀ᵐ y : Coord3,terminalTime i y≠0 := by
    refine Fin.cases h0 (fun k => ?_) i
    exact (sourceChildInverse_quasi (actualChildSign k)).ae h0
  have hne := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (ae_all_iff.mpr hh))
  filter_upwards [hinside,hout,ae_all_iff.mpr hchild,hne,ae_restrict_mem Metric.isOpen_ball.measurableSet]
    with x hi ho hc hn hx
  by_cases hb : WithLp.ofLp x∈physicalOpenBlock
  · rw [ite_eq_left hb]
    exact hi hb
  · rw [ite_eq_right hb]
    by_cases hp : terminalTime 0 (E x)<0
    · exact ho ⟨hx,hp⟩
    · have hp' : 0<terminalTime 0 (E x) := lt_of_le_of_ne (le_of_not_gt hp) (hn 0).symm
      have hnchild : ¬∀ k : Fin 2,terminalTime k.succ (E x)<0 := by
        intro hh
        exact hb ((sourceOpenBlock_time_iff (E x)).mpr ⟨hp',hh⟩)
      push Not at hnchild
      obtain ⟨k,hk⟩ := hnchild
      exact hc k ⟨hx,lt_of_le_of_ne hk (hn k.succ).symm⟩

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_PhysicalTerminalCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory
namespace PhysicalFiniteEndingData

lemma terminalCore_closed (η : ℝ) : IsClosed (terminalCore η) := by
  simp only [terminalCore,ofPred_and,ofPred_forall]
  exact (isClosed_le continuous_const (terminalTime_locallyLipschitz 0).continuous).inter
    (isClosed_iInter (fun k => isClosed_le (terminalTime_locallyLipschitz k.succ).continuous continuous_const))

lemma terminalCore_subset {η : ℝ} (hη : 0≤η) : terminalCore η⊆physicalBlockRegion := by
  intro y hy
  rw [physicalBlockRegion_time_iff]
  exact ⟨hη.trans hy.1,fun k => (hy.2 k).trans (by linarith)⟩

lemma terminalCore_compact {η : ℝ} (hη : 0≤η) : IsCompact (terminalCore η) :=
  physicalBlockRegion_compact.of_isClosed_subset (terminalCore_closed η) (terminalCore_subset hη)

lemma terminalCore_subset_open {η : ℝ} (hη : 0<η) : terminalCore η⊆physicalOpenBlock := by
  intro y hy
  change WithLp.toLp 2 y∈sourceOpenBlock
  rw [sourceOpenBlock_time_iff]
  exact ⟨hη.trans_le hy.1,fun k => (hy.2 k).trans_lt (by linarith)⟩

lemma terminalCore_subset_interior {α β : ℝ} (hab : α<β) :
    terminalCore β⊆interior (terminalCore α) := by
  intro y hy
  apply mem_interior_iff_mem_nhds.mpr
  have hp : ∀ᶠ x in 𝓝 y,α<terminalTime 0 x :=
    (terminalTime_locallyLipschitz 0).continuous.continuousAt.eventually
      (lt_mem_nhds (hab.trans_le hy.1))
  have hc (k : Fin 2) : ∀ᶠ x in 𝓝 y,terminalTime k.succ x< -α :=
    (terminalTime_locallyLipschitz k.succ).continuous.continuousAt.eventually
      (gt_mem_nhds ((hy.2 k).trans_lt (by linarith)))
  filter_upwards [hp,eventually_all.mpr hc] with x hp hc
  exact ⟨hp.le,fun k => (hc k).le⟩

lemma terminal_cutoff_exists {η : ℝ} (hη : 0<η) :
    ∃ χ : Coord3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆physicalOpenBlock ∧ (∀ y∈terminalCore η,χ y=1) := by
  have hs := terminalCore_compact (show 0≤η/2 by positivity)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ Coord3) (terminalCore_closed η)
    (terminalCore_subset_interior (show η/2<η by linarith)) (n:=↑(⊤:ℕ∞))
  have hts : tsupport (χ : Coord3 → ℝ)⊆terminalCore (η/2) := by
    apply closure_minimal _ hs.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  refine ⟨χ,χ.contMDiff.contDiff,HasCompactSupport.intro hs hχ0,
    hts.trans (terminalCore_subset_open (by positivity)),?_⟩
  intro y hy
  have hh : (χ : Coord3 → ℝ)=ᶠ[𝓝 y] (fun _ => 1) := hχ1.filter_mono (nhds_le_nhdsSet hy)
  exact hh.eq_of_nhds

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
attribute [local instance] Classical.propDecidable
namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma terminal_band_value
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (hT : ∀ i : Fin 3,∀ t : ℝ,|t|≤η → (z.ending i).R<z.compression i*(t-terminalBase i))
    (w : Fin 2 → H1) (he : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i))
    (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈physicalOpenBlock → y∉terminalCore η →
      weakValue (w j) (WithLp.toLp 2 y)-z.terminalValue 0 j=z.terminalProfile η j y := by
  have hev (i : Fin 3) := (he j i).value_cartesian (fun _ => physicalEndRegion_subset_ball i)
  filter_upwards [ae_all_iff.mpr hev,ae_all_iff.mpr (fun i => z.correctedEndValue_terminal_ae hs i j)]
    with y hv ht hy hn
  have hy' := (sourceOpenBlock_time_iff y).mp hy
  change 0<terminalTime 0 y ∧ ∀ k : Fin 2,terminalTime k.succ y<0 at hy'
  by_cases hp : terminalTime 0 y≤η
  · have he0 : y∈physicalEndRegion 0 := by
      change 0≤terminalTime 0 y ∧ terminalTime 0 y ≤ centralThickness
      exact ⟨hy'.1.le,by linarith⟩
    have hTa : |terminalTime 0 y|≤η := by rw [abs_of_pos hy'.1]; exact hp
    have hh := (hv 0 he0).trans (ht 0 he0 (hT 0 _ hTa).le)
    rw [z.terminalProfile_parent_band hη hηc j hy'.1.le hp]
    linarith
  · have hn' : ¬∀ k : Fin 2,terminalTime k.succ y≤-η := fun h => hn ⟨(lt_of_not_ge hp).le,h⟩
    push Not at hn'
    obtain ⟨k,hk⟩ := hn'
    have hc : terminalTime k.succ y≤0 := (hy'.2 k).le
    have hek : y∈physicalEndRegion k.succ := by
      change -centralThickness≤terminalTime k.succ y ∧ terminalTime k.succ y≤0
      exact ⟨by linarith,hc⟩
    have hTa : |terminalTime k.succ y|≤η := by rw [abs_of_nonpos hc]; linarith
    have hh := (hv k.succ hek).trans (ht k.succ hek (hT k.succ _ hTa).le)
    rw [z.terminalProfile_child_band hη hηc j k hk.le,min_eq_left hc]
    linarith

end PhysicalFiniteEndingData
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
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma voltageOriginalProjectedH1_eq {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2)
    (Z : VoltageJetSpace volume U) (u : H1) (hu : u.val=voltageOriginalJetCLM hU j Z) :
    voltageOriginalProjectedH1 hU j Z=u := by
  change H1Space.orthogonalProjectionOnto (voltageOriginalJetCLM hU j Z)=u
  rw [←hu]
  exact H1Space.orthogonalProjectionOnto_mem_subspace_eq_self u

lemma voltageOriginalJetCLM_smooth_compact {U : Set Coord3} (hU : MeasurableSet U)
    {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hvs : tsupport v⊆U) (hm : MemLp v 2 (volume.restrict U))
    (hg : MemLp (voltageGradient v) 2 (volume.restrict U)) (j : Fin 2) :
    voltageOriginalJetCLM hU j (hm.toLp _,hg.toLp _)=
      (piSmoothH1 ((contDiff_apply ℝ ℝ j).comp hv)).val := by
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hm.coeFn_toLp)
  have hgp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hg.coeFn_toLp)
  apply Lp.ext
  filter_upwards [voltageOriginalJetCLM_ae hU j (hm.toLp _,hg.toLp _),
    ae_restrict_of_ae hp,ae_restrict_of_ae hgp,
    piSmoothH1_jet ((contDiff_apply ℝ ℝ j).comp hv)] with x hx hp hgp hf
  rw [hx,hf]
  by_cases hu : WithLp.ofLp x∈U
  · rw [ite_eq_left hu,hp hu,hgp hu]
    ext k
    refine Fin.cases rfl (fun i => ?_) k
    exact voltageGradient_component (hv.differentiable (by simp) _) i j
  · rw [ite_eq_right hu]
    have hn : WithLp.ofLp x∉tsupport (fun y => v y j) := by
      intro h
      exact hu (hvs ((tsupport_comp_subset (g:=fun w : Fin 2 → ℝ => w j) rfl v) h))
    ext k
    refine Fin.cases ?_ (fun i => ?_) k
    · exact (image_eq_zero_of_notMem_tsupport hn).symm
    · change 0=fderiv ℝ (fun y => v y j) (WithLp.ofLp x) (Pi.single i 1)
      rw [fderiv_of_notMem_tsupport ℝ hn]
      rfl

theorem voltageOriginal_outer_trace_zero (j : Fin 2)
    {Z : VoltageJetSpace volume physicalOpenBlock}
    (hZ : Z∈zeroVoltageJets volume physicalOpenBlock) (u : H1)
    (hu : u.val=voltageOriginalJetCLM physicalOpenBlock_open.measurableSet j Z) (i : Fin 3) :
    physicalOuterTraceCLM i u=0 := by
  let T : VoltageJetSpace volume physicalOpenBlock →L[ℝ] SpectralL2 TorusModes :=
    (physicalOuterTraceCLM i).comp (voltageOriginalProjectedH1 physicalOpenBlock_open.measurableSet j)
  have hz : T Z=0 := by
    apply closure_minimal (t:={Z | T Z=0}) ?_ (isClosed_eq T.continuous continuous_const) hZ
    intro a ha
    obtain ⟨v,hv,hvc,hvs,hm,hg,rfl⟩ := ha
    have he := voltageOriginalJetCLM_smooth_compact physicalOpenBlock_open.measurableSet hv hvs hm hg j
    change physicalOuterTraceCLM i (voltageOriginalProjectedH1 physicalOpenBlock_open.measurableSet j
      (hm.toLp _,hg.toLp _))=0
    rw [voltageOriginalProjectedH1_eq _ _ _ _ he.symm,physicalOuterTrace_smooth i _ (fun _ => 1),
      physicalSmoothOuterTrace_compact_zero (fun _ => 1) _ ?_]
    rfl
    exact (tsupport_comp_subset (g:=fun w : Fin 2 → ℝ => w j) rfl v).trans hvs
  change physicalOuterTraceCLM i (voltageOriginalProjectedH1 physicalOpenBlock_open.measurableSet j Z)=0 at hz
  rw [voltageOriginalProjectedH1_eq _ _ _ _ hu] at hz
  exact hz

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped Convolution ENNReal NNReal

lemma mollifyReal_congr_ae (φ : SpatialBump) {f g : R3 → ℝ}
    (h : f=ᵐ[volume] g) : mollifyReal φ f=mollifyReal φ g := by
  funext x
  unfold mollifyReal
  rw [convolution_eq_swap,convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

lemma mollifyReal_lipschitz_bound {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) (φ : SpatialBump) (x : R3) :
    ‖mollifyReal φ f x-f x‖≤C*φ.rOut := by
  have hi : Integrable (fun y => f (x-y)) (bumpProbability φ) := by
    apply Integrable.mono' (integrable_const (‖f x‖+C*φ.rOut))
      (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    filter_upwards [bumpProbability_ball φ] with y hy
    have hh := hf.norm_sub_le (x-y) x
    have hn : ‖x-y-x‖=‖y‖ := by rw [sub_sub_cancel_left,norm_neg]
    rw [hn] at hh
    exact (norm_le_insert' (f (x-y)) (f x)).trans (by nlinarith [C.coe_nonneg])
  have hc : (∫ _ : R3,f x ∂bumpProbability φ)=f x := by simp
  rw [mollifyReal_eq_average,←hc,←integral_sub hi (integrable_const _)]
  have hh := norm_integral_le_of_norm_le_const (μ:=bumpProbability φ)
    (f:=fun y => f (x-y)-f x) (C:=(C:ℝ)*φ.rOut) (by
      filter_upwards [bumpProbability_ball φ] with y hy
      have hb := hf.norm_sub_le (x-y) x
      have hn : ‖x-y-x‖=‖y‖ := by rw [sub_sub_cancel_left,norm_neg]
      rw [hn] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left hy.le C.coe_nonneg))
  simpa using hh

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

lemma continuousOuterMap_mollify_tendsto {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) (i : Fin 3) :
    Tendsto (fun n => continuousOuterMap i (mollifyReal_smooth (dyadicBump n)
      hf.continuous.locallyIntegrable).continuous) atTop (𝓝 (continuousOuterMap i hf.continuous)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (g:=fun n => (C:ℝ)*(dyadicBump n).rOut) (fun _ => norm_nonneg _) ?_ ?_
  · intro n
    apply (ContinuousMap.norm_le _ (mul_nonneg C.coe_nonneg (by change 0≤(1/2:ℝ)^n; positivity))).mpr
    intro θ
    change ‖(mollifyReal (dyadicBump n) f (WithLp.toLp 2 (physicalOuterBoundary i θ)):ℂ)-
      (f (WithLp.toLp 2 (physicalOuterBoundary i θ)):ℂ)‖≤_
    rw [←Complex.ofReal_sub,Complex.norm_real]
    exact mollifyReal_lipschitz_bound hf _ _
  · simpa using (tendsto_const_nhds.mul dyadicBump_radius :
      Tendsto (fun n => (C:ℝ)*(dyadicBump n).rOut) atTop (𝓝 ((C:ℝ)*0)))

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_10
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_10
theorem physicalOuterTrace_lipschitz {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) (F : Fin 4 → WholeL2)
    (hv : (F 0 : R3 → ℝ)=ᵐ[volume] f)
    (hw : ∀ i : Fin 3,WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1))
    (u : H1) (hu : u.val=ballJet F) (i : Fin 3) :
    physicalOuterTraceCLM i u=continuousOuterFourier i hf.continuous := by
  let P := H1Space.orthogonalProjectionOnto
  have hp : P (ballJet F)=u := by
    rw [←hu]
    exact H1Space.orthogonalProjectionOnto_mem_subspace_eq_self u
  have hlim := ((physicalOuterTraceCLM i).continuous.comp P.continuous).continuousAt.tendsto.comp
    (ballJet_mollify_tendsto F)
  change Tendsto (fun n => physicalOuterTraceCLM i
    (H1Space.orthogonalProjectionOnto (ballJet (fun j => mollifyL2 (dyadicBump n) (F j)))))
    atTop (𝓝 (physicalOuterTraceCLM i (P (ballJet F)))) at hlim
  simp only [mollifiedJet_eq F hw,
    H1Space.orthogonalProjectionOnto_mem_subspace_eq_self,smoothOuterFourier_original] at hlim
  change Tendsto _ atTop (𝓝 (physicalOuterTraceCLM i (P (ballJet F)))) at hlim
  rw [hp] at hlim
  have hlim' := (mFourierBasis (d:=Fin 2)).repr.continuous.continuousAt.tendsto.comp
    ((ContinuousMap.toLp 2 volume ℂ).continuous.continuousAt.tendsto.comp
      (continuousOuterMap_mollify_tendsto hf i))
  apply tendsto_nhds_unique hlim
  convert hlim' using 1
  · funext n
    unfold continuousOuterFourier continuousOuterMap
    congr 3
    ext θ
    rw [mollifyReal_congr_ae _ hv]
  · rfl

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

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalTrace
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
attribute [local instance] OAI.ScalarConductivity.sourcePhysicalTraceMeasureSpace
local instance sourcePhysicalTraceIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma physicalOuterTrace_compact_mul {χ : R3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ⊆(WithLp.ofLp) ⁻¹' physicalOpenBlock) (u v : H1)
    (hv : weakValue v=ᵐ[ballMeasure] fun x => χ x*weakValue u x) (i : Fin 3) :
    physicalOuterTraceCLM i v=0 := by
  let P := H1Space.orthogonalProjectionOnto
  let T : H1 →L[ℝ] SpectralL2 TorusModes :=
    (physicalOuterTraceCLM i).comp (P.comp (originalMulJetCLM hχ hc))
  have hz : T u=0 := by
    apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_
      (isClosed_eq T.continuous continuous_const)) (smoothH1_dense u)
    rintro w ⟨f,hf,hm,he⟩
    have hw : w=smoothH1 f hf := Subtype.ext he
    change T w=0
    rw [hw]
    change physicalOuterTraceCLM i (P (originalMulJetCLM hχ hc (smoothH1 f hf)))=0
    rw [originalMulJetCLM_smooth]
    simp only [P,H1Space.orthogonalProjectionOnto_mem_subspace_eq_self]
    let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
    have hd : ContDiff ℝ (↑(⊤:ℕ∞)) ((χ*f) ∘ E) := (hχ.mul hf).comp E.contDiff
    have hev : piSmoothH1 hd=smoothH1 (χ*f) (hχ.mul hf) := by
      unfold piSmoothH1
      congr 1
    rw [←hev,physicalOuterTrace_smooth i hd (fun _ => 1),
      physicalSmoothOuterTrace_compact_zero (fun _ => 1) hd ?_]
    rfl
    have hss : tsupport ((χ*f) ∘ E)⊆E ⁻¹' tsupport χ :=
      closure_minimal (fun x hx => tsupport_mul_subset_left (subset_tsupport (χ*f) hx))
        ((isClosed_tsupport χ).preimage E.continuous)
    intro y hy
    exact hs (hss hy)
  have hm := originalMulJetCLM_mem_zero hχ hc (fun x hx => physicalOpenBlock_subset_ball (hs hx)) u
  let a : H1 := ⟨originalMulJetCLM hχ hc u,zeroTraceAmbient_le_H1Space hm⟩
  have ha : a=v := by
    apply H1_eq_of_value_ae
    filter_upwards [originalMulJetCLM_ae hχ hc u,hv] with x hx hv
    exact (congrArg (fun z : JetFiber => z 0) hx).trans hv.symm
  change physicalOuterTraceCLM i (P a.val)=0 at hz
  rw [H1Space.orthogonalProjectionOnto_mem_subspace_eq_self,ha] at hz
  exact hz

lemma physicalOuterTrace_compact_lipschitz {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖x‖ → f x=0)
    (u : H1) (hu : weakValue u=ᵐ[ballMeasure] f) (i : Fin 3) :
    physicalOuterTraceCLM i u=continuousOuterFourier i hf.continuous := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport (bounded_support_compact hs)
  have hd (j : Fin 3) := lipschitz_lineDeriv_memLp hf hs (EuclideanSpace.single j 1)
  let F : Fin 4 → WholeL2 := Fin.cases (hm.toLp f)
    (fun j => (hd j).toLp (fun x => lineDeriv ℝ f x (EuclideanSpace.single j 1)))
  have hv : (F 0 : R3 → ℝ)=ᵐ[volume] f := hm.coeFn_toLp
  have hw (j : Fin 3) : WeakL2Direction (F 0) (F j.succ) (EuclideanSpace.single j 1) :=
    (lipschitz_weakDirection hf _).congr hv ((hd j).coeFn_toLp)
  have hz := compact_weakJet_mem_zeroTrace F hw hR (by
    filter_upwards [hv] with x hx hn; exact hx.trans (hs x hn))
  let v : H1 := ⟨ballJet F,zeroTraceAmbient_le_H1Space hz⟩
  have he : u=v := by
    apply H1_eq_of_value_ae
    filter_upwards [hu,ae_restrict_of_ae (s:=ball) hv,ballJet_ae F] with x hu hx hb
    exact hu.trans (hx.symm.trans (hb 0).symm)
  rw [he]
  exact physicalOuterTrace_lipschitz hf F hv hw v rfl i

lemma physicalRealTrace_compact_lipschitz {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖x‖ → f x=0)
    (u : H1) (hu : weakValue u=ᵐ[ballMeasure] f) (i : Fin 3) :
    physicalRealTraceCLM i u=ᵐ[volume] fun θ => f (WithLp.toLp 2 (physicalOuterBoundary i θ)) := by
  have he : physicalComplexTraceCLM i u=ContinuousMap.toLp 2 volume ℂ (continuousOuterMap i hf.continuous) := by
    change (mFourierBasis (d:=Fin 2)).repr.symm (physicalOuterTraceCLM i u)=_
    rw [physicalOuterTrace_compact_lipschitz hf hR hs u hu]
    exact (mFourierBasis (d:=Fin 2)).repr.symm_apply_apply _
  have hh := Complex.reCLM.coeFn_compLpL (p:=2) (μ:=volume) (physicalComplexTraceCLM i u)
  change physicalRealTraceCLM i u=ᵐ[volume] _ at hh
  rw [he] at hh
  filter_upwards [hh,ContinuousMap.coeFn_toLp (continuousOuterMap i hf.continuous) (p:=2) (μ:=volume) (𝕜:=ℂ)]
    with θ hθ hfv
  rw [hθ,hfv]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma terminalTime_outer (i : Fin 3) (θ : UnitAddTorus (Fin 2)) :
    terminalTime i (physicalOuterBoundary i θ)=0 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · change sourceCollarTime (sourceAngularCollar 0 θ)=0
    exact sourceAngular_time (by norm_num) θ
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm
      ((sourceChildHomeomorph (actualChildSign k)) (sourceAngularCollar 0 θ)))=0
    rw [Homeomorph.symm_apply_apply,sourceAngular_time (by norm_num)]

lemma terminalProfile_boundary {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (j : Fin 2) (i : Fin 3) (θ : UnitAddTorus (Fin 2)) :
    z.terminalProfile η j (physicalOuterBoundary i θ)=z.terminalValue i j-z.terminalValue 0 j := by
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [z.terminalProfile_zero_outside hη hηc j (terminalTime_outer 0 θ).le,sub_self]
  · rw [z.terminalProfile_child_band hη hηc j k (by rw [terminalTime_outer]; linarith),terminalTime_outer]
    simp

attribute [local instance] OAI.ScalarConductivity.sourcePhysicalTraceMeasureSpace
lemma terminalProfile_trace {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (j : Fin 2) (f : H1)
    (hf : weakValue f=ᵐ[ballMeasure] fun x => z.terminalProfile η j (WithLp.ofLp x)) (i : Fin 3) :
    physicalRealTraceCLM i f=ᵐ[volume] fun _ => z.terminalValue i j-z.terminalValue 0 j := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hh (x : R3) : LocalLipAt (z.terminalProfile η j ∘ E) x :=
    (z.terminalProfile_localLip η j (E x)).comp
      (E.toContinuousLinearMap.lipschitz.locallyLipschitz x)
  have hz (x : R3) (hx : 5/2<‖x‖) : (z.terminalProfile η j ∘ E) x=0 := by
    apply z.terminalProfile_zero_outside hη hηc j
    by_contra hn
    have hd := (sourceCollarTime_pos_iff_domain (E x)).mp (lt_of_not_ge hn)
    have hb := sourceClosure_subset_ball (subset_closure hd)
    change x∈Metric.ball 0 (5/2) at hb
    simp only [Metric.mem_ball,dist_zero_right] at hb
    linarith
  obtain ⟨K,hK⟩ := compact_locallyLipschitz hh (bounded_support_compact hz)
  have ht := physicalRealTrace_compact_lipschitz hK (by norm_num : (5/2:ℝ)<3) hz f hf i
  exact ht.mono (fun θ h => h.trans (z.terminalProfile_boundary hη hηc j i θ))

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
attribute [local instance] Classical.propDecidable

lemma patch_energy_eq (a : R3 → ℝ) (σ : Coord3 → ℝ) (q W h : H1)
    (ha : ∀ᵐ y∂volume.restrict physicalOpenBlock,a (WithLp.toLp 2 y)=σ y)
    (hW : ∀ᵐ x∂ballMeasure,weakGradient W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakGradient q x else 0) :
    (∫ x,a x*inner ℝ (weakGradient W x) (weakGradient h x) ∂ballMeasure)=
      ∫ y in physicalOpenBlock,σ y*(originalPiGradient q y ⬝ᵥ originalPiGradient h y) := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let U := E ⁻¹' physicalOpenBlock
  let f : R3 → ℝ := fun x => a x*inner ℝ (weakGradient q x) (weakGradient h x)
  have hU : MeasurableSet U := physicalOpenBlock_open.measurableSet.preimage E.continuous.measurable
  have hUb : U⊆ball := fun _ hx => physicalOpenBlock_subset_ball hx
  have hi : (∫ x,a x*inner ℝ (weakGradient W x) (weakGradient h x) ∂ballMeasure)=
      ∫ x,f x ∂volume.restrict U := by
    calc
      _ = ∫ x,U.indicator f x ∂ballMeasure := integral_congr_ae (by
        filter_upwards [hW] with x hx
        rw [hx]
        by_cases hb : WithLp.ofLp x∈physicalOpenBlock
        · rw [ite_eq_left hb,Set.indicator_of_mem (show x∈U from hb)]
        · rw [ite_eq_right hb,Set.indicator_of_notMem (show x∉U from hb),inner_zero_left,mul_zero])
      _ = ∫ x in U,f x ∂ballMeasure := integral_indicator hU
      _ = _ := by rw [ballMeasure,Measure.restrict_restrict hU,inter_eq_left.mpr hUb]
  rw [hi]
  have ht := (PiLp.volume_preserving_ofLp (Fin 3)).setIntegral_preimage_emb
    E.toHomeomorph.measurableEmbedding (fun y => f (WithLp.toLp 2 y)) physicalOpenBlock
  change (∫ x in U,f x)=_ at ht
  rw [ht]
  apply integral_congr_ae
  filter_upwards [ha] with y hy
  change a (WithLp.toLp 2 y)*inner ℝ (weakGradient q (WithLp.toLp 2 y))
    (weakGradient h (WithLp.toLp 2 y))=_
  rw [hy]
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  exact dotProduct_comm _ _

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

theorem source_patch_green {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (a : R3 → ℝ) (σ : Coord3 → ℝ) (q W : H1) (j : Fin 2)
    (ha : ∀ᵐ y∂volume.restrict physicalOpenBlock,a (WithLp.toLp 2 y)=σ y)
    (hv : ∀ᵐ x∂ballMeasure,weakValue W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakValue q x-z.terminalValue 0 j
      else z.terminalProfile η j (WithLp.ofLp x))
    (hg : ∀ h : H1,(∫ y in physicalOpenBlock,σ y*(originalPiGradient q y ⬝ᵥ
      originalPiGradient h y))=constantTerminalFluxCLM (centralBasisSlopes j) h) :
    ∀ h : H1,(∫ x,a x*inner ℝ (weakGradient W x) (weakGradient h x) ∂ballMeasure)=
      constantTerminalFluxCLM (centralBasisSlopes j) h := by
  intro h
  exact (patch_energy_eq a σ q W h ha (z.source_patch_gradient hη hηc q W j hv)).trans (hg h)

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
attribute [local instance] Classical.propDecidable
namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

attribute [local instance] OAI.ScalarConductivity.physicalRootMeasureSpaceUnitAddCircle
local instance physicalRootIsProbabilityMeasure_rdfd3f1_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem source_patch_trace_exists
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {η : ℝ} (hη : 0<η) (hηc : 2*η < centralThickness)
    (hT : ∀ i : Fin 3,∀ t : ℝ,|t|≤η → (z.ending i).R<z.compression i*(t-terminalBase i))
    (w q : Fin 2 → H1) (he : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i))
    (Z : VoltageJetSpace volume physicalOpenBlock)
    (hZ : Z∈zeroVoltageJets volume physicalOpenBlock)
    (hq : ∀ j,(q j-w j).val=voltageOriginalJetCLM physicalOpenBlock_open.measurableSet j Z)
    (j : Fin 2) :
    ∃ W : H1,W∈H10 ∧ (∀ᵐ x∂ballMeasure,weakValue W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakValue (q j) x-z.terminalValue 0 j
      else z.terminalProfile η j (WithLp.ofLp x)) ∧
      ∀ i : Fin 3,physicalRealTraceCLM i W=ᵐ[volume] fun _ => z.terminalValue i j-z.terminalValue 0 j := by
  obtain ⟨f,hf,hfv⟩ := z.terminalProfile_H10 hη hηc j
  obtain ⟨χ,hχ,hχc,hχs,hχ1⟩ := terminal_cutoff_exists hη
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hχd : ContDiff ℝ (↑(⊤:ℕ∞)) (χ ∘ E) := hχ.comp E.contDiff
  have hχcc : HasCompactSupport (χ ∘ E) := hχc.comp_homeomorph E.toHomeomorph
  have hχblock : tsupport (χ ∘ E)⊆E ⁻¹' physicalOpenBlock := by
    have hh : tsupport (χ ∘ E)⊆E ⁻¹' tsupport χ :=
      closure_minimal (fun y hy => subset_tsupport χ hy) ((isClosed_tsupport χ).preimage E.continuous)
    intro x hx
    exact hχs (hh hx)
  have hχss : tsupport (χ ∘ E)⊆ball := fun _ hx => physicalOpenBlock_subset_ball (hχblock hx)
  let u := w j-constantH1 (z.terminalValue 0 j)-f
  obtain ⟨v,hv,hvv⟩ := original_smooth_mul_exists hχd hχcc hχss u
  have hd : q j-w j∈H10 := by
    change (q j-w j).val∈zeroTraceAmbient
    rw [hq]
    exact voltageOriginalJetCLM_zeroTrace physicalOpenBlock_open.measurableSet
      (fun _ => physicalOpenBlock_subset_ball) j hZ
  have hband := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (z.terminal_band_value hs hη hηc hT w he j))
  have hdv : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉physicalOpenBlock → weakValue (q j-w j) x=0 := by
    have hz := voltageOriginalJetCLM_ae physicalOpenBlock_open.measurableSet j Z
    rw [←hq j] at hz
    filter_upwards [hz] with x hx hxn
    have hh := congrArg (fun f : JetFiber => f 0) hx
    change (q j-w j).val x 0=0
    rw [hx,ite_eq_right hxn]
    rfl
  refine ⟨v+f+(q j-w j),H10.add_mem (H10.add_mem hv hf) hd,?_,?_⟩
  · filter_upwards [hvv,hfv,hband,hdv,weakValue_add (v+f) (q j-w j),weakValue_add v f,
      weakValue_sub (w j-constantH1 (z.terminalValue 0 j)) f,
      (H1_sub_constant_spec (w j) (z.terminalValue 0 j)).1,weakValue_sub (q j) (w j)]
      with x hmv hfv hband hdv hsum hadd hu1 hu2 hd1
    rw [hsum]
    simp only [Pi.add_apply]
    rw [hadd]
    simp only [Pi.add_apply]
    have hu : weakValue u x=weakValue (w j) x-z.terminalValue 0 j-z.terminalProfile η j (WithLp.ofLp x) := by
      change weakValue (w j-constantH1 (z.terminalValue 0 j)-f) x=_
      rw [hu1,Pi.sub_apply,hu2,hfv]
    rw [hmv,hu,hfv]
    change χ (WithLp.ofLp x)*(weakValue (w j) x-z.terminalValue 0 j-z.terminalProfile η j (WithLp.ofLp x))+
      z.terminalProfile η j (WithLp.ofLp x)+weakValue (q j-w j) x=_
    by_cases hx : WithLp.ofLp x∈physicalOpenBlock
    · rw [ite_eq_left hx,hd1]
      simp only [Pi.sub_apply]
      by_cases hc : WithLp.ofLp x∈terminalCore η
      · rw [hχ1 _ hc]; ring
      · have hh := hband hx hc
        simp only [WithLp.toLp_ofLp] at hh
        rw [show weakValue (w j) x-z.terminalValue 0 j-z.terminalProfile η j (WithLp.ofLp x)=0 by linarith]
        linarith
    · rw [ite_eq_right hx,hdv hx]
      have hz : χ (WithLp.ofLp x)=0 := image_eq_zero_of_notMem_tsupport (fun hn => hx (hχs hn))
      rw [hz]
      ring
  · intro i
    have htv := physicalOuterTrace_compact_mul hχd hχcc hχblock u v hvv i
    have htd := voltageOriginal_outer_trace_zero j hZ (q j-w j) (hq j) i
    have hrzero (u : H1) (hu : physicalOuterTraceCLM i u=0) : physicalRealTraceCLM i u=0 := by
      change Complex.reCLM.compLpL 2 volume ((mFourierBasis (d:=Fin 2)).repr.symm (physicalOuterTraceCLM i u))=0
      rw [hu,map_zero,map_zero]
    rw [map_add,map_add,hrzero v htv,hrzero (q j-w j) htd,zero_add,add_zero]
    exact z.terminalProfile_trace hη hηc j f hfv i

end PhysicalFiniteEndingData
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

lemma constantTerminalFlux_zero_of_realTrace (κ : Fin 3 → ℝ) (u : H1)
    (hu : ∀ i : Fin 3,physicalRealTraceCLM i u=0) : constantTerminalFluxCLM κ u=0 := by
  rw [constantTerminalFlux_realTrace]
  have hz (i : Fin 3) : (∫ θ,physicalRealTraceCLM i u θ)=0 := by
    rw [hu i]
    exact (integral_congr_ae (Lp.coeFn_zero ℝ 2 (volume : Measure (UnitAddTorus (Fin 2))))).trans (integral_zero _ _)
  simp [hz]

lemma physicalRealTrace_transition_zero (u : H1) {M : ℝ} (hM : 0≤M)
    (ht : ∀ i : Fin 3,∀ᵐ θ,physicalRealTraceCLM i u θ≤M) :
    ∀ i : Fin 3,physicalRealTraceCLM i ((upperTransition M hM).onH1 u)=0 := by
  intro i
  rw [physicalRealTrace_chain]
  apply Lp.ext
  filter_upwards [(upperTransition M hM).lipschitz.coeFn_compLp (upperTransition M hM).at_zero
    (physicalRealTraceCLM i u),ht i,Lp.coeFn_zero ℝ 2 (volume : Measure (UnitAddTorus (Fin 2)))]
    with θ hx ht hz
  rw [hx,hz]
  exact (upperTransition_zero_iff M hM _).mpr ht

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma le_of_transition_energy_zero (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x∂ballMeasure,|a x|≤C)
    (hp : ∀ᵐ x∂ballMeasure,0<a x) {u : H1} (hu : u∈H10) {M : ℝ} (hM : 0≤M)
    (he : (∫ x,a x*inner ℝ (weakGradient u x)
      (weakGradient ((upperTransition M hM).onH1 u) x) ∂ballMeasure)=0) :
    ∀ᵐ x∂ballMeasure,weakValue u x≤M := by
  let F := upperTransition M hM
  have hh0 : F.onH1 u∈H10 := F.preserves_H10 hu
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

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_11
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_11_rdfd3f1_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem physical_source_le (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x∂ballMeasure,|a x|≤C)
    (hp : ∀ᵐ x∂ballMeasure,0<a x) {u : H1} (hu : u∈H10) (κ : Fin 3 → ℝ)
    (hg : ∀ h : H1,(∫ x,a x*inner ℝ (weakGradient u x) (weakGradient h x) ∂ballMeasure)=
      constantTerminalFluxCLM κ h) {M : ℝ} (hM : 0≤M)
    (ht : ∀ i : Fin 3,∀ᵐ θ,physicalRealTraceCLM i u θ≤M) :
    ∀ᵐ x∂ballMeasure,weakValue u x≤M := by
  apply le_of_transition_energy_zero a ha C hC hb hp hu hM
  rw [hg,constantTerminalFlux_zero_of_realTrace κ _ (physicalRealTrace_transition_zero u hM ht)]

 theorem physical_source_bounded (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x∂ballMeasure,|a x|≤C)
    (hp : ∀ᵐ x∂ballMeasure,0<a x) {u : H1} (hu : u∈H10) (κ : Fin 3 → ℝ)
    (hg : ∀ h : H1,(∫ x,a x*inner ℝ (weakGradient u x) (weakGradient h x) ∂ballMeasure)=
      constantTerminalFluxCLM κ h) {M : ℝ} (hM : 0≤M)
    (ht : ∀ i : Fin 3,∀ᵐ θ,|physicalRealTraceCLM i u θ|≤M) :
    ∀ᵐ x∂ballMeasure,|weakValue u x|≤M := by
  have hup := physical_source_le a ha C hC hb hp hu κ hg hM
    (fun i => (ht i).mono (fun _ h => (abs_le.mp h).2))
  have hneg : (∫ x,a x*inner ℝ (weakGradient (-u) x)
      (weakGradient ((upperTransition M hM).onH1 (-u)) x) ∂ballMeasure)=0 := by
    change energy a (-u) ((upperTransition M hM).onH1 (-u))=0
    rw [←energyForm_apply a ha C hC hb,map_neg,neg_apply,energyForm_apply a ha C hC hb]
    change -(∫ x,a x*inner ℝ (weakGradient u x) (weakGradient ((upperTransition M hM).onH1 (-u)) x) ∂ballMeasure)=0
    rw [hg]
    have htneg : ∀ i : Fin 3,∀ᵐ θ,physicalRealTraceCLM i (-u) θ≤M := by
      intro i
      rw [map_neg]
      filter_upwards [ht i,Lp.coeFn_neg (physicalRealTraceCLM i u)] with θ ht hn
      rw [hn]
      exact (neg_le_iff_add_nonneg).mpr (by linarith [(abs_le.mp ht).1])
    rw [constantTerminalFlux_zero_of_realTrace κ _ (physicalRealTrace_transition_zero (-u) hM htneg),neg_zero]
  have hlo := le_of_transition_energy_zero a ha C hC hb hp (H10.neg_mem hu) hM hneg
  filter_upwards [hup,hlo,weakValue_neg u] with x hx hy hz
  rw [hz,Pi.neg_apply] at hy
  exact abs_le.mpr ⟨by linarith,hx⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix UnitAddTorus
attribute [local instance] Classical.propDecidable

local instance instMeasureSpaceUnitAddCircle_solutions_12_rdfd3f1_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
theorem boundedRootSources_nonempty_oai : Nonempty BoundedRootSources := by
  obtain ⟨s,hs,hres⟩ := exists_nonresonant_angular_tensor
  let z : PhysicalFiniteEndingData s := Classical.choice (physicalFiniteEndingData_nonempty hs hres)
  obtain ⟨σ,c,C,w,q,hσ,hσLp,hc,hcC,hσb,hq0,hwc,hwe,⟨Z,hZ,hq⟩,hgreen⟩ := z.scalar_pair_green_exists hs
  obtain ⟨η,hη,hηc,hT⟩ := z.terminal_band_exists
  let t := η/4
  have ht : 0<t := by dsimp [t]; positivity
  have htc : 2*t < centralThickness := by dsimp [t]; linarith
  have hT' : ∀ i : Fin 3,∀ r : ℝ,|r|≤t → (z.ending i).R<z.compression i*(r-PhysicalFiniteEndingData.terminalBase i) := by
    intro i r hr
    apply hT i r
    dsimp [t] at hr
    linarith
  choose W hW hWv hWt using z.source_patch_trace_exists hs ht htc hT' w q hwe
    (Z-originalPairVoltageJet physicalOpenBlock w) hZ hq
  let b : Coord3 → ℝ := fun y => max c (min C (σ y))
  have hbm : Measurable b := measurable_const.max (measurable_const.min hσ)
  have hbb (y : Coord3) : b y∈Icc c C := ⟨le_max_left _ _,max_le hcC.le (min_le_left _ _)⟩
  have hbe : b=ᵐ[volume.restrict physicalOpenBlock] σ := by
    filter_upwards [hσb] with y hy
    exact max_eq_right (by simpa only [min_eq_right hy.2] using hy.1) |>.trans (min_eq_right hy.2)
  let a : R3 → ℝ := fun x => b (WithLp.ofLp x)
  have ham : AEStronglyMeasurable a ballMeasure :=
    (hbm.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable).aestronglyMeasurable
  have hC : 0≤C := (hc.trans hcC).le
  have hab : ∀ᵐ x∂ballMeasure,|a x|≤C := Eventually.of_forall (fun x => by
    rw [abs_of_pos (hc.trans_le (hbb _).1)]; exact (hbb _).2)
  have hap : ∀ᵐ x∂ballMeasure,0<a x := Eventually.of_forall (fun x => hc.trans_le (hbb _).1)
  have hae : ∀ᵐ y∂volume.restrict physicalOpenBlock,a (WithLp.toLp 2 y)=σ y := hbe
  let M : ℝ := ∑ j : Fin 2,∑ i : Fin 3,|z.terminalValue i j-z.terminalValue 0 j|
  have hM : 0≤M := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  have hMi (i : Fin 3) (j : Fin 2) : |z.terminalValue i j-z.terminalValue 0 j|≤M := by
    have h1 : |z.terminalValue i j-z.terminalValue 0 j|≤∑ i : Fin 3,|z.terminalValue i j-z.terminalValue 0 j| :=
      Finset.single_le_sum (f:=fun i : Fin 3 => |z.terminalValue i j-z.terminalValue 0 j|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : (∑ i : Fin 3,|z.terminalValue i j-z.terminalValue 0 j|)≤M :=
      Finset.single_le_sum (f:=fun j : Fin 2 => ∑ i : Fin 3,|z.terminalValue i j-z.terminalValue 0 j|) (fun k _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)) (Finset.mem_univ j)
    exact h1.trans h2
  have hWb (j : Fin 2) : ∀ᵐ x∂ballMeasure,|weakValue (W j) x|≤M :=
    physical_source_bounded a ham C hC hab hap (hW j) (centralBasisSlopes j)
      (z.source_patch_green ht htc a σ (q j) (W j) j hae (hWv j) (hgreen j)) hM
      (fun i => (hWt j i).mono (fun θ hθ => by rw [hθ]; exact hMi i j))
  let K := M+(∑ j : Fin 2,‖weakGradientL (W j)‖^2)+1
  have he0 : 0≤∑ j : Fin 2,‖weakGradientL (W j)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hMK : M≤K := by dsimp [K]; linarith
  have hWK (j : Fin 2) : ‖weakGradientL (W j)‖^2≤K := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (fun k _ => sq_nonneg ‖weakGradientL (W k)‖) (Finset.mem_univ j)
    dsimp [K]; linarith
  have hWg (j : Fin 2) := z.source_patch_gradient ht htc (q j) (W j) j (hWv j)
  refine ⟨⟨b,hbm,c,C,K,hc,hcC,(by dsimp [K]; linarith),hbb,W,hW,
    fun j => (hWb j).mono (fun _ h => h.trans hMK),hWK,?_,?_,?_⟩⟩
  · intro j
    filter_upwards [hWv j,hWg j] with x hv hg hx
    have ht0 : sourceCollarTime (WithLp.ofLp x)<0 := by
      apply lt_of_not_ge
      intro hn
      apply hx
      exact (sourceDomain_closure_time (WithLp.ofLp x)).mpr hn
    have hn : WithLp.ofLp x∉physicalOpenBlock := by
      intro hn
      have hh := (sourceOpenBlock_time_iff _).mp hn
      exact (not_lt.mpr ht0.le) hh.1
    rw [ite_eq_right hn] at hv hg
    refine ⟨?_,hg⟩
    rw [hv]
    exact z.terminalProfile_zero_outside ht htc j ht0.le
  · intro j
    filter_upwards [hWg j] with x hx hn
    simpa only [ite_eq_right hn] using hx
  · intro a ha j h
    exact z.source_patch_green ht htc a σ (q j) (W j) j (Filter.EventuallyEq.trans ha hbe) (hWv j) (hgreen j) h

end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.boundedRootSources_nonempty_oai := @OAI.ScalarConductivity.boundedRootSources_nonempty_oai
