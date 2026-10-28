-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:36:38.958198+00:00
-- url     : https://prove2.me/submissions/68325b06-343f-439e-98e1-da4fb1b71b92

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_weak

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section
section H1SmoothMultiplierActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots



namespace H1
variable {Ω : Set Plane} {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))

lemma smoothMul_value_ae (u : H1 Ω) : H1.value (smoothMul hb hb0 hb1 u) =ᵐ[volume.restrict Ω]
    fun x => b x*H1.value u x :=
  ((H1.hasH1Gradient u).mul_smooth hb hb0 hb1).1.coeFn_toLp

end H1
end StrictHotSpots
end H1SmoothMultiplierActualCompatibleLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
end
end ActualVectorSupport

section ActualScalarEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 ≤ firstPositiveNeumannValue Ω)

lemma physicalSolution_class {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    ∃ v : H10 (show IsOpen Ω from c.diskMap.open_target), c.physicalSolution hb hs hμ hw hl-
      (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1=v.val := by
  refine ⟨transportH10 c.diskMap c.diskMap_inverse_smooth (c.datumCorrection hb hs hμ hw hl),?_⟩
  exact add_sub_cancel_left _ _

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualScalarEnergy

section ActualVectorEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Laplacian
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)


lemma scalarSolution_class {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ v : H10 (show IsOpen Ω from c.diskMap.open_target), c.scalarSolution hb hs hμ hw-
      (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1=v.val :=
  c.physicalSolution_class hb hs hμ.le hw (c.datumTrace_lipschitz hb hs hw).choose_spec

end StrictHotSpots.Conformal.ClosedDiskChart
namespace StrictHotSpots

lemma smoothMul_smooth_closure {Ω : Set Plane} (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hs : SmoothBoundary Ω) {b w : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    H1.smoothMul hb hb0 hb1 (smooth_closure_H1 ho hbound hs hw).toH1 =
      (smooth_closure_H1 ho hbound hs (hb.contDiffOn.mul hw)).toH1 := by
  apply H1.value_injective ho
  apply Lp.ext
  filter_upwards [H1.smoothMul_value_ae hb hb0 hb1 (smooth_closure_H1 ho hbound hs hw).toH1,
    (smooth_closure_H1 ho hbound hs hw).1.coeFn_toLp,
    (smooth_closure_H1 ho hbound hs (hb.contDiffOn.mul hw)).1.coeFn_toLp] with x h1 h2 h3
  exact h1.trans ((congrArg (fun t : ℝ => b x*t) h2).trans h3.symm)

end StrictHotSpots
end
end ActualVectorEnergy


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PhysicalHelmholtz

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PhysicalHelmholtz
variable {Ω : Set Plane} (ho : IsOpen Ω)

attribute [local instance] OAI.StrictHotSpots.PhysicalHelmholtz.instNormedAddCommGroupSubtypeH1AmbientMemSubmoduleRealH1H10
lemma pair_apply (μ : ℝ) (u v : H1 Ω) : pair μ u v =
    inner ℝ (H1.grad v) (H1.grad u)-μ*inner ℝ (H1.value v) (H1.value u) := rfl

lemma pair_comm (μ : ℝ) (u v : H1 Ω) : pair μ u v=pair μ v u := by
  rw [pair_apply,pair_apply]
  exact congrArg₂ (fun a b : ℝ => a-μ*b)
    (real_inner_comm (H1.grad u) (H1.grad v))
    (real_inner_comm (H1.value u) (H1.value v))

lemma zeroPair_pair (μ : ℝ) (u v : H10 ho) : zeroPair ho μ u v=pair μ v.val u.val := rfl

attribute [local instance] OAI.StrictHotSpots.PhysicalHelmholtz.instInnerProductSpaceRealSubtypeH1AmbientMemSubmoduleH1H10
attribute [local instance] OAI.StrictHotSpots.PhysicalHelmholtz.instCompleteSpaceSubtypeH1AmbientMemSubmoduleRealH1H10
lemma correction_spec (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (a : H1 Ω) (v : H10 ho) :
    zeroPair ho μ (correction ho hb hμ hl hD a) v = -pair μ a v.val := by
  rw [← (zeroPair_coercive ho hb hμ hl hD).continuousLinearEquivOfBilin_apply]
  simp only [correction,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

lemma extension_class (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) (a : H1 Ω) :
    ∃ w : H10 ho, extension ho hb hμ hl hD a-a=w.val := by
  exact ⟨correction ho hb hμ hl hD a,add_sub_cancel_left _ _⟩

lemma extension_weak (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) (a : H1 Ω)
    (v : H10 ho) : pair μ (extension ho hb hμ hl hD a) v.val=0 := by
  change pair μ (a+(correction ho hb hμ hl hD a).val) v.val=0
  rw [map_add,add_apply]
  have he := correction_spec ho hb hμ hl hD a v
  have hh : pair μ (correction ho hb hμ hl hD a).val v.val=
      zeroPair ho μ (correction ho hb hμ hl hD a) v := by
    exact (pair_comm μ _ _).trans (zeroPair_pair ho μ _ _).symm
  rw [hh,he,add_neg_cancel]

lemma norm_zero_numeric {C x : ℝ} (hC : 0 < C) (hx : 0 ≤ x) (h : C*x*x ≤ 0) : x=0 := by
  by_contra hn
  have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm hn)
  exact (not_le_of_gt (mul_pos (mul_pos hC hp) hp)) h

lemma self_zero (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (w : H10 ho) (hz : zeroPair ho μ w w=0) : w=0 := by
  obtain ⟨C,hC,hB⟩ := zeroPair_coercive ho hb hμ hl hD
  have hn := hB w
  rw [hz] at hn
  exact norm_eq_zero.mp (norm_zero_numeric hC (norm_nonneg w) hn)

lemma pair_sub (μ : ℝ) (a b v : H1 Ω) :
    pair μ (a-b) v = pair μ a v-pair μ b v := by
  exact congrArg (fun t : H1 Ω →L[ℝ] ℝ => t v) ((pair μ).map_sub a b)

lemma unique (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    {a b : H1 Ω} (ha : ∀ v : H10 ho, pair μ a v.val=0)
    (hb' : ∀ v : H10 ho, pair μ b v.val=0)
    (hab : ∃ w : H10 ho, a-b=w.val) : a=b := by
  obtain ⟨w,hw⟩ := hab
  have h0 : pair μ w.val w.val=0 := by
    calc
      _ = pair μ (a-b) w.val := congrArg (fun z : H1 Ω => pair μ z w.val) hw.symm
      _ = pair μ a w.val-pair μ b w.val := pair_sub μ a b w.val
      _ = 0 := by rw [ha,hb',sub_self]
  have hz : zeroPair ho μ w w=0 := h0
  have hw0 : w=0 := self_zero ho hb hμ hl hD w hz
  apply sub_eq_zero.mp
  exact hw.trans (congrArg (fun z : H10 ho => z.val) hw0)

end StrictHotSpots.PhysicalHelmholtz
end
end PhysicalHelmholtz

section LipschitzH1Convergence

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots

lemma H1.tendsto_of_components {Ω : Set Plane} {v : ℕ → H1 Ω} {u : H1 Ω}
    (hv : Tendsto (fun n => H1.value (v n)) atTop (𝓝 (H1.value u)))
    (hg : Tendsto (fun n => H1.grad (v n)) atTop (𝓝 (H1.grad u))) :
    Tendsto v atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  exact (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp (hv.prodMk_nhds hg)

lemma smoothMul_tendsto_lipschitzMul {Ω : Set Plane} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b)
    (u : H1 Ω) :
    Tendsto (fun n => H1.smoothMul (ambientSmooth_smooth (planeApproxBump n) hb)
      (continuous_closure_memLp_top ho hΩ (ambientSmooth_lipschitz (planeApproxBump n) hb).continuous.continuousOn)
      (lipschitz_gradient_memLp_top (ambientSmooth_lipschitz (planeApproxBump n) hb)) u)
      atTop (𝓝 (H1.lipschitzMul ho hΩ hb u)) := by
  let bn := fun n => ambientSmooth (planeApproxBump n) b
  have hbn (n : ℕ) : ContDiff ℝ ∞ (bn n) := ambientSmooth_smooth _ hb
  have hbl (n : ℕ) : LipschitzWith L (bn n) := ambientSmooth_lipschitz _ hb
  have hn0 (n : ℕ) := continuous_closure_memLp_top ho hΩ (hbl n).continuous.continuousOn
  have hn1 (n : ℕ) := lipschitz_gradient_memLp_top (Ω:=Ω) (hbl n)
  have hu := H1.hasH1Gradient u
  have hf (n : ℕ) := hu.mul_smooth (hbn n) (hn0 n) (hn1 n)
  have hl := hu.mul_lipschitz ho hΩ hb
  obtain ⟨C,hC,hbd⟩ := ambientSmooth_uniform_bound hΩ hb
  have ht (x : Plane) : Tendsto (fun n => bn n x) atTop (𝓝 (b x)) :=
    ambientSmooth_tendsto planeApproxBump_rOut_tendsto hb x
  have hgt : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => gradient (bn n) x)
      atTop (𝓝 (gradient b x)) :=
    ae_restrict_of_ae (ambientSmooth_gradient_tendsto planeApproxBump_rOut_tendsto
      (Eventually.of_forall planeApproxBump_ratio) hb)
  apply H1.tendsto_of_components
  · apply L2VectorLimits.tendsto_toLp_of_dominated (fun n => (hf n).1) hl.1
      (hu.1.norm.const_mul C)
    · filter_upwards [] with n
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbd n x hx) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (ht x).mul_const (H1.value u x)
  · apply L2VectorLimits.tendsto_toLp_of_dominated (fun n => (hf n).2.1) hl.2.1
      ((hu.2.1.norm.const_mul C).add (hu.1.norm.const_mul (L:ℝ)))
    · filter_upwards [] with n
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      calc
        _ ≤ ‖bn n x • H1.grad u x‖+‖H1.value u x • gradient (bn n) x‖ := norm_add_le _ _
        _ = ‖bn n x‖*‖H1.grad u x‖+‖H1.value u x‖*‖gradient (bn n) x‖ := by rw [norm_smul,norm_smul]
        _ ≤ C*‖H1.grad u x‖+‖H1.value u x‖*(L:ℝ) := add_le_add
          (mul_le_mul_of_nonneg_right (hbd n x hx) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (lipschitz_gradient_bound (hbl n) x) (norm_nonneg _))
        _ = _ := by simp only [Pi.add_apply]; ring
    · filter_upwards [hgt] with x hx
      exact ((ht x).smul_const (H1.grad u x)).add (tendsto_const_nhds.smul hx)

end StrictHotSpots
end
end LipschitzH1Convergence

section PhysicalMultiplierLimit

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

lemma class_difference {S : Set Plane} (ho : IsOpen S) {a b f : H1 S}
    (ha : ∃ v : H10 ho, a-f=v.val) (hb : ∃ v : H10 ho, b-f=v.val) :
    ∃ v : H10 ho, a-b=v.val := by
  obtain ⟨v,hv⟩ := ha
  obtain ⟨w,hw⟩ := hb
  refine ⟨v-w,?_⟩
  change a-b=v.val-w.val
  exact (show a-b=(a-f)-(b-f) from by abel).trans
    (congrArg₂ (fun x y : H1 S => x-y) hv hw)

lemma scalarSolution_eq_extension {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw =
      PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
        (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1 := by
  apply PhysicalHelmholtz.unique hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
    (c.scalarSolution_weak hΩ hμ hw)
    (PhysicalHelmholtz.extension_weak hΩ.2.1 hΩ.2.2.1 hμ.le hl hD _)
  exact class_difference hΩ.2.1 (c.scalarSolution_class hΩ.2.2.1 hΩ.2.2.2.2 hμ hw)
    (PhysicalHelmholtz.extension_class hΩ.2.1 hΩ.2.2.1 hμ.le hl hD _)

lemma multipliedGradient_eq_extension {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))
    (i : Fin 2) : c.multipliedGradient hΩ hu hμ hb i =
      PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
        (H1.smoothMul hb hb0 hb1 (eigenGradientField hΩ hu i)) := by
  have hh := c.scalarSolution_eq_extension hΩ hμ hl hD
    (hb.contDiffOn.mul (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)))
  have he := smoothMul_smooth_closure hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hb hb0 hb1
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i))
  exact hh.trans (congrArg (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD) he.symm)


lemma multipliedGradient_tendsto_oai {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) (i : Fin 2) :
    Tendsto (fun n => c.multipliedGradient hΩ hu hμ (ambientSmooth_smooth (planeApproxBump n) hb) i)
      atTop (𝓝 (lipschitzMultipliedGradient hΩ hμ hl hD hu hb i)) := by
  have ht := (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD).continuous.continuousAt.tendsto.comp
    (smoothMul_tendsto_lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (eigenGradientField hΩ hu i))
  apply ht.congr'
  exact Eventually.of_forall fun n => (c.multipliedGradient_eq_extension hΩ hμ hl hD hu
    (ambientSmooth_smooth (planeApproxBump n) hb)
    (continuous_closure_memLp_top hΩ.2.1 hΩ.2.2.1
      (ambientSmooth_lipschitz (planeApproxBump n) hb).continuous.continuousOn)
    (lipschitz_gradient_memLp_top (ambientSmooth_lipschitz (planeApproxBump n) hb)) i).symm

end StrictHotSpots.Conformal.ClosedDiskChart

end
end PhysicalMultiplierLimit


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_tendsto_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_tendsto_oai
