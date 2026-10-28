-- Prove2me | solution 1 for OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:57:10.552092+00:00
-- url     : https://prove2.me/submissions/69466b42-56ef-4752-addc-98b7938517d0

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_actual_priced_particle_bound_three
import Theorems.Thm_OAI_CoulombAtom_exists_actual_fullAnnulus_inverse_constant
import Theorems.Thm_OAI_CoulombBarrier_original_finite_barrier_iteration
import Theorems.Thm_OAI_CoulombBarrier_tail_initial_good_event

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoulombCoercivity

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

end CoulombCoercivity

lemma graphFormVector_admissible {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖ ^ 2 = 1) : FormAdmissible (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    exact ((mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property
      (i, a)) φ hφ hcφ
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s
  · have hmass := graphValue_norm_sq F
    rw [hn] at hmass
    simpa only [lp_norm_sq, graphComponent_apply, graphFormVector] using hmass.symm
  · intro s i
    exact nuclear_integrable i (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  · intro s i j hij
    exact pair_integrable i j hij (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SommerfeldCoefficient
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma laplacian_comp_isometry {f : E → ℝ} (e : E ≃ₗᵢ[ℝ] E) (x : E)
    (hf : ContDiffAt ℝ 2 f (e x)) : Δ (fun y => f (e y)) x = Δ f (e x) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (e y)) x := hf.comp x e.contDiff.contDiffAt
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map e)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, OrthonormalBasis.map_apply]
  rw [← second_deriv_line hc, ← second_deriv_line hf]
  congr 2
  funext t
  simp only [map_add, map_smul]

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_GlobalDensityConstant
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
open MeasureTheory Set Metric
open scoped ENNReal
namespace CoulombAtom

namespace Pauli
open CoulombDensity

lemma globalDensityConstant_pos : 0 < globalDensityConstant := by
  unfold globalDensityConstant
  positivity

end Pauli
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierConditionalBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CoulombBarrier

lemma reaction_monotone {k : ℝ} (hk : 0 ≤ k) : Monotone (reaction k) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_max_right _ _) (max_le_max hst le_rfl) (by norm_num))
    (by positivity)

lemma reaction_continuous (k : ℝ) : Continuous (reaction k) := by
  apply continuous_const.mul
  exact (continuous_id.max continuous_const).rpow_const (fun _ => Or.inr (by norm_num))

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSmoothMaxBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter Laplacian InnerProductSpace MeasureTheory
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE

lemma second_fderiv_scalar_comp {u : TFSpace → ℝ} {g : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 g) (x v : TFSpace) :
    fderiv ℝ (fderiv ℝ (g ∘ u)) x v v =
      deriv (deriv g) (u x)*(fderiv ℝ u x v)^2+
        deriv g (u x)*fderiv ℝ (fderiv ℝ u) x v v := by
  have hud (z : TFSpace) := (hu.differentiable (by norm_num) z)
  have hgd (z : ℝ) := (hg.differentiable (by norm_num) z)
  have hud' (z : TFSpace) := ((hu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) z)
  have hgd' (z : ℝ) := differentiableAt_deriv_of_contDiffAt (hg.contDiffAt (x := z))
  have hcu := hg.comp hu
  have hcu' := (hcu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) x
  have he : (fun z => fderiv ℝ (g ∘ u) z v) =
      fun z => deriv g (u z)*fderiv ℝ u z v := by
    funext z
    rw [((hgd (u z)).hasDerivAt.comp_hasFDerivAt z (hud z).hasFDerivAt).fderiv]
    rfl
  rw [← fderiv_apply_const_scalar hcu' v v,he]
  have h1 := (hgd' (u x)).hasDerivAt.comp_hasFDerivAt x (hud x).hasFDerivAt
  have h2 : DifferentiableAt ℝ (fun z => fderiv ℝ u z v) x :=
    (hud' x).clm_apply (differentiableAt_const v)
  rw [show (fun z => deriv g (u z)*fderiv ℝ u z v) =
      (deriv g ∘ u)*(fun z => fderiv ℝ u z v) from rfl,
    fderiv_mul h1.differentiableAt h2]
  simp only [add_apply,smul_apply,smul_eq_mul,
    Function.comp_apply]
  rw [h1.fderiv,fderiv_apply_const_scalar (hud' x)]
  simp only [smul_apply,smul_eq_mul]
  ring

lemma laplacian_scalar_comp_lower {u : TFSpace → ℝ} {g : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 g) (x : TFSpace)
    (hpos : 0 ≤ deriv (deriv g) (u x)) :
    deriv g (u x)*Δ u x ≤ Δ (g ∘ u) x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [second_fderiv_scalar_comp hu hg]
  exact le_add_of_nonneg_left (mul_nonneg hpos (sq_nonneg _))

lemma smoothPositive_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (smoothPositive ε) := by
  exact (contDiff_id.add (((contDiff_id.pow 2).add contDiff_const).sqrt
    (fun t => ne_of_gt (by positivity)))).div_const 2

lemma smoothRoot_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sqrt (z^2+ε^2))
      (t/Real.sqrt (t^2+ε^2)) t := by
  have hq : t^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hd : HasDerivAt (fun z : ℝ => Real.sqrt (z^2+ε^2))
      (2*t/(2*Real.sqrt (t^2+ε^2))) t := by
    simpa only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] using
      ((((hasDerivAt_id t).pow 2).add_const (ε^2)).sqrt hq)
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma smoothPositive_deriv {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (smoothPositive ε) t = (1+t/Real.sqrt (t^2+ε^2))/2 := by
  have hh := ((hasDerivAt_id t).add (smoothRoot_hasDerivAt hε t)).div_const 2
  exact hh.deriv

lemma smoothPositive_deriv_bounds {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (smoothPositive ε) t ∧ deriv (smoothPositive ε) t ≤ 1 := by
  have hq : 0 < Real.sqrt (t^2+ε^2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2)
  have ha : |t| ≤ Real.sqrt (t^2+ε^2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ε]
  have hlo : -1 ≤ t/Real.sqrt (t^2+ε^2) := (le_div_iff₀ hq).mpr (by linarith [(abs_le.mp ha).1])
  have hhi : t/Real.sqrt (t^2+ε^2) ≤ 1 := (div_le_iff₀ hq).mpr (by linarith [(abs_le.mp ha).2])
  rw [smoothPositive_deriv hε]
  constructor <;> linarith

lemma smoothPositive_second_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (deriv (smoothPositive ε)) t := by
  have hq : t^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hqs : 0 < Real.sqrt (t^2+ε^2) := Real.sqrt_pos.mpr (by positivity)
  have hd' := smoothRoot_hasDerivAt hε t
  have he : deriv (smoothPositive ε) = fun z => (1+z/Real.sqrt (z^2+ε^2))/2 :=
    funext (smoothPositive_deriv hε)
  rw [he]
  have hquot := (hasDerivAt_id t).div hd' hqs.ne'
  have hh : HasDerivAt (fun z => (1+z/Real.sqrt (z^2+ε^2))/2)
      (((Real.sqrt (t^2+ε^2)-t*(t/Real.sqrt (t^2+ε^2)))/Real.sqrt (t^2+ε^2)^2)/2) t := by
    simpa only [Pi.add_apply,Pi.div_apply,id_eq,one_mul,zero_add] using
      ((hasDerivAt_const t 1).add hquot |>.div_const 2)
  rw [hh.deriv]
  have hnum : 0 ≤ Real.sqrt (t^2+ε^2)-t*(t/Real.sqrt (t^2+ε^2)) := by
    rw [← mul_div_assoc,sub_nonneg,div_le_iff₀ hqs]
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2),sq_nonneg ε]
  exact div_nonneg (div_nonneg (by simpa only [one_mul] using hnum) (sq_nonneg _)) (by norm_num)

lemma smoothMaximum_contDiff {ε : ℝ} (hε : 0 < ε) {u v : TFSpace → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 (smoothMaximum ε u v) :=
  hv.add ((smoothPositive_contDiff hε).comp (hu.sub hv))

theorem smoothMaximum_laplacian_lower {ε : ℝ} (hε : 0 < ε) {u v : TFSpace → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : TFSpace) {h : ℝ}
    (huL : h ≤ Δ u x) (hvL : h ≤ Δ v x) :
    h ≤ Δ (smoothMaximum ε u v) x := by
  have hd := laplacian_scalar_comp_lower (hu.sub hv) (smoothPositive_contDiff hε) x
    (smoothPositive_second_nonneg hε (u x-v x))
  obtain ⟨hp0,hp1⟩ := smoothPositive_deriv_bounds hε (u x-v x)
  change deriv (smoothPositive ε) (u x-v x)*Δ (u-v) x ≤ Δ (smoothPositive ε ∘ (u-v)) x at hd
  rw [(hu.contDiffAt (x := x)).laplacian_sub hv.contDiffAt] at hd
  change deriv (smoothPositive ε) (u x-v x)*(Δ u x-Δ v x) ≤ _ at hd
  change h ≤ Δ (v+smoothPositive ε ∘ (u-v)) x
  have hc : ContDiff ℝ 2 (smoothPositive ε ∘ (u-v)) :=
    (smoothPositive_contDiff hε).comp (hu.sub hv)
  rw [hv.contDiffAt.laplacian_add hc.contDiffAt]
  nlinarith [mul_nonneg hp0 (sub_nonneg.mpr huL),
    mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hvL)]

lemma smoothPositive_bounds {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    max t 0 ≤ smoothPositive ε t ∧ smoothPositive ε t ≤ max t 0+ε/2 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2)
  have hp := Real.sqrt_nonneg (t^2+ε^2)
  have hlo : |t| ≤ Real.sqrt (t^2+ε^2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ε]
  have hhi : Real.sqrt (t^2+ε^2) ≤ |t|+ε := by
    nlinarith [abs_nonneg t,sq_abs t,mul_nonneg (abs_nonneg t) hε]
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht,abs_of_nonneg ht] at *
    dsimp [smoothPositive]
    constructor <;> linarith
  · have ht' := le_of_not_ge ht
    rw [max_eq_right ht',abs_of_nonpos ht'] at *
    dsimp [smoothPositive]
    constructor <;> linarith

lemma smoothMaximum_bounds {ε : ℝ} (hε : 0 ≤ ε) (u v : TFSpace → ℝ) (x : TFSpace) :
    max (u x) (v x) ≤ smoothMaximum ε u v x ∧
    smoothMaximum ε u v x ≤ max (u x) (v x)+ε/2 := by
  obtain ⟨hl,hh⟩ := smoothPositive_bounds hε (u x-v x)
  dsimp [smoothMaximum]
  by_cases hvu : v x ≤ u x
  · rw [max_eq_left hvu,max_eq_left (sub_nonneg.mpr hvu)] at *
    constructor <;> linarith
  · have huv := le_of_not_ge hvu
    rw [max_eq_right huv,max_eq_right (sub_nonpos.mpr huv)] at *
    constructor <;> linarith

lemma smoothMaximum_norm_bound {ε C : ℝ} (hε : 0 ≤ ε) {u v : TFSpace → ℝ}
    (x : TFSpace) (hu : ‖u x‖ ≤ C) (hv : ‖v x‖ ≤ C) :
    ‖smoothMaximum ε u v x‖ ≤ C+ε/2 := by
  have hb := smoothMaximum_bounds hε u v x
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · linarith [le_max_left (u x) (v x)]
  · linarith [max_le hu'.2 hv'.2]

lemma smoothMaximum_tendsto {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    {u v : ι → TFSpace → ℝ} {a b : ℝ} (x : TFSpace)
    (hε0 : ∀ᶠ i in l, 0 ≤ ε i) (hε : Tendsto ε l (𝓝 0))
    (hu : Tendsto (fun i => u i x) l (𝓝 a))
    (hv : Tendsto (fun i => v i x) l (𝓝 b)) :
    Tendsto (fun i => smoothMaximum (ε i) (u i) (v i) x) l (𝓝 (max a b)) := by
  have hm := hu.max hv
  have he := hm.add (hε.div_const 2)
  simp only [zero_div,add_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm he
  · filter_upwards [hε0] with i hi
    exact (smoothMaximum_bounds hi (u i) (v i) x).1
  · filter_upwards [hε0] with i hi
    exact (smoothMaximum_bounds hi (u i) (v i) x).2

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierWeakMaxBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma newtonMul_flip_eq : newtonMul.flip = newtonMul := by
  exact ContinuousLinearMap.flip_mul

lemma laplacian_sub_left {k : TFSpace → ℝ} (hk : ContDiff ℝ 2 k)
    (x y : TFSpace) : Δ (fun z => k (x-z)) y = Δ k (x-y) := by
  have hd : ContDiff ℝ 2 (fun z : TFSpace => k (x+z)) :=
    hk.comp (contDiff_const.add contDiff_id)
  have hh := laplacian_comp_isometry (LinearIsometryEquiv.neg ℝ) y hd.contDiffAt
  simpa only [LinearIsometryEquiv.coe_neg,sub_eq_add_neg,tfLaplacian_translate] using hh

lemma tsupport_sub_left {k : TFSpace → ℝ} {r : ℝ}
    (hk : ∀ z, k z ≠ 0 → ‖z‖ ≤ r) (x : TFSpace) :
    tsupport (fun y => k (x-y)) ⊆ closedBall x r := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  rw [mem_closedBall,dist_eq_norm_sub']
  exact hk (x-y) hy

lemma weak_lower_convolution {U : Set TFSpace} {u h k : TFSpace → ℝ}
    (hu : Continuous u) (hw : WeakLaplacianLowerOn U u h)
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hk0 : ∀ y, 0 ≤ k y)
    {x : TFSpace} (hs : tsupport (fun y => k (x-y)) ⊆ U) :
    (k ⋆[newtonMul] h) x ≤ Δ (k ⋆[newtonMul] u) x := by
  have hd : ContDiff ℝ 2 (fun y => k (x-y)) := hk.comp (contDiff_const.sub contDiff_id)
  have hc : HasCompactSupport (fun y => k (x-y)) := hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hi := hw _ hd hc hs (fun y => hk0 (x-y))
  have he : k ⋆[newtonMul] u = u ⋆[newtonMul] k := by
    simpa only [newtonMul_flip_eq] using (convolution_flip newtonMul (f := u) (g := k))
  rw [he,laplacian_convolution hu.locallyIntegrable hkc hk]
  simp_rw [laplacian_sub_left hk] at hi
  rw [convolution_eq_swap]
  simpa only [newtonMul,ContinuousLinearMap.mul_apply',mul_comm] using hi

lemma maxKernel_radius (n : ℕ) : (shrinkingBump (E := TFSpace) n).rOut ≤ 2 := by
  dsimp [shrinkingBump]
  have hn : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have ht := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn
  norm_num only [one_div_one] at ht
  linarith

lemma maxKernel_support (n : ℕ) {z : TFSpace} (hz : maxKernel n z ≠ 0) :
    ‖z‖ ≤ (shrinkingBump (E := TFSpace) n).rOut := by
  have ht : z ∈ Function.support ((shrinkingBump (E := TFSpace) n).normed volume) := hz
  rw [ContDiffBump.support_normed_eq] at ht
  exact (by simpa only [mem_ball,dist_zero_right] using ht : ‖z‖ < _).le

lemma maxMollify_contDiff {u : TFSpace → ℝ} (hu : LocallyIntegrable u) (n : ℕ) :
    ContDiff ℝ 2 (maxMollify n u) :=
  (shrinkingBump n).hasCompactSupport_normed.contDiff_convolution_left newtonMul
    (shrinkingBump n).contDiff_normed hu

lemma maxMollify_tendsto {u : TFSpace → ℝ} (hu : Continuous u) (x : TFSpace) :
    Tendsto (fun n => maxMollify n u x) atTop (𝓝 (u x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto hu x

lemma maxMollify_bound {u : TFSpace → ℝ} {R C : ℝ}
    (hC : ∀ y, ‖y‖ ≤ R+2 → ‖u y‖ ≤ C) (n : ℕ) {x : TFSpace} (hx : ‖x‖ ≤ R) :
    ‖maxMollify n u x‖ ≤ C := by
  have hi : Integrable (maxKernel n) :=
    (shrinkingBump n).continuous_normed.integrable_of_hasCompactSupport
      (shrinkingBump n).hasCompactSupport_normed
  change ‖∫ z, maxKernel n z*u (x-z)‖ ≤ C
  calc
    _ ≤ ∫ z, C*maxKernel n z := norm_integral_le_of_norm_le (hi.const_mul C)
      (Eventually.of_forall fun z => by
        by_cases hz : maxKernel n z = 0
        · simp only [hz,zero_mul,mul_zero,norm_zero,le_refl]
        · rw [norm_mul,Real.norm_of_nonneg (show 0 ≤ maxKernel n z from (shrinkingBump n).nonneg_normed z)]
          have hb : ‖u (x-z)‖ ≤ C := hC (x-z)
            ((norm_sub_le x z).trans (add_le_add hx ((maxKernel_support n hz).trans (maxKernel_radius n))))
          nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ maxKernel n z from (shrinkingBump n).nonneg_normed z)])
    _ = C := by rw [integral_const_mul]; change C*(∫ z, (shrinkingBump n).normed volume z) = C; rw [ContDiffBump.integral_normed,mul_one]

lemma continuous_ball_bound {u : TFSpace → ℝ} (hu : Continuous u) (R : ℝ) :
    ∃ C > 0, ∀ x, ‖x‖ ≤ R → ‖u x‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := ((isCompact_closedBall (0 : TFSpace) R).image hu).isBounded.exists_pos_norm_lt
  exact ⟨C,hC,fun x hx => (hb _ ⟨x,by simpa using hx,rfl⟩).le⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierWeakMaxGeneralBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierWeakMaxGeneral_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution

open CoulombAnalysis CoulombPDE CoulombAtom

lemma maxMollify_test_pairing {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (n : ℕ) :
    (∫ x, maxMollify n h x * φ x) =
      maxMollify n (h ⋆[newtonMul] (fun x => φ (-x))) 0 := by
  let φ' : TFSpace → ℝ := fun x => φ (-x)
  have hd : Continuous φ' := hφ.comp continuous_neg
  have hc : HasCompactSupport φ' := hcφ.comp_homeomorph (Homeomorph.neg TFSpace)
  have hk : Continuous (maxKernel n) := (shrinkingBump n).continuous_normed
  have hkc : HasCompactSupport (maxKernel n) := (shrinkingBump n).hasCompactSupport_normed
  have hhn : LocallyIntegrable (fun x => ‖h x‖) := fun x => (hh x).norm
  have hfg := hkc.convolutionExists_left newtonMul hk hh
  have hgk := hc.norm.convolutionExists_right newtonMul hhn hd.norm
  have hgkc := hc.norm.continuous_convolution_right newtonMul hhn hd.norm
  have hfgk := hkc.norm.convolutionExists_left_of_continuous_right (μ := volume) newtonMul
    hk.norm.locallyIntegrable hgkc 0
  have ha := convolution_assoc newtonMul newtonMul newtonMul newtonMul
    (fun x y z : ℝ => mul_assoc x y z) hk.aestronglyMeasurable
    hh.aestronglyMeasurable hd.aestronglyMeasurable
    (Eventually.of_forall hfg) (Eventually.of_forall hgk) hfgk
  simpa only [maxMollify,convolution_def, newtonMul, ContinuousLinearMap.mul_apply',zero_sub,φ',neg_neg] using ha

lemma maxMollify_test_tendsto {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, maxMollify n h x * φ x) atTop (𝓝 (∫ x, h x*φ x)) := by
  let φ' : TFSpace → ℝ := fun x => φ (-x)
  have hd : Continuous φ' := hφ.comp continuous_neg
  have hc : HasCompactSupport φ' := hcφ.comp_homeomorph (Homeomorph.neg TFSpace)
  have ht := maxMollify_tendsto (hc.continuous_convolution_right newtonMul hh hd) 0
  simp_rw [maxMollify_test_pairing hh hφ hcφ]
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  simp only [convolution_def,newtonMul,ContinuousLinearMap.mul_apply',zero_sub,φ',neg_neg]

theorem weak_maximum_common_locallyIntegrable_source {U : Set TFSpace} (hU : IsOpen U)
    {u v h : TFSpace → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hh : LocallyIntegrable h)
    (hwu : WeakLaplacianLowerOn U u h) (hwv : WeakLaplacianLowerOn U v h) :
    WeakLaplacianLowerOn U (fun x => max (u x) (v x)) h := by
  intro φ hφ hcφ hsφ hnφ
  obtain ⟨δ,hδ,hsδ⟩ := hcφ.isCompact.exists_cthickening_subset_open hU hsφ
  obtain ⟨R,hR,hbR⟩ := hcφ.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨Cu,hCu,hbu⟩ := continuous_ball_bound hu (R+2)
  obtain ⟨Cv,hCv,hbv⟩ := continuous_ball_bound hv (R+2)
  let D := max Cu Cv
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → TFSpace → ℝ := fun n => smoothMaximum (ε n) (maxMollify n u) (maxMollify n v)
  have hwd (n : ℕ) : ContDiff ℝ 2 (w n) := smoothMaximum_contDiff (hε n)
    (maxMollify_contDiff hu.locallyIntegrable n) (maxMollify_contDiff hv.locallyIntegrable n)
  have hwb (n : ℕ) {x : TFSpace} (hx : x ∈ tsupport φ) : ‖w n x‖ ≤ D+1 := by
    have hux : ‖maxMollify n u x‖ ≤ D :=
      (maxMollify_bound hbu n (hbR x hx).le).trans (le_max_left _ _)
    have hvx : ‖maxMollify n v x‖ ≤ D :=
      (maxMollify_bound hbv n (hbR x hx).le).trans (le_max_right _ _)
    have hw := smoothMaximum_norm_bound (hε n).le x hux hvx
    change ‖w n x‖ ≤ D+ε n/2 at hw
    linarith [hεle n]
  have hwlim (x : TFSpace) : Tendsto (fun n => w n x) atTop (𝓝 (max (u x) (v x))) :=
    smoothMaximum_tendsto x (Eventually.of_forall fun n => (hε n).le) hε0
      (maxMollify_tendsto hu x) (maxMollify_tendsto hv x)
  have hΔφ := tfLaplacian_continuous hφ
  have hcΔφ := tfLaplacian_compact hφ hcφ
  have htR : Tendsto (fun n => ∫ x, w n x*Δ φ x) atTop
      (𝓝 (∫ x, max (u x) (v x)*Δ φ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (D+1)*‖Δ φ x‖)
    · intro n
      exact ((hwd n).continuous.mul hΔφ).aestronglyMeasurable
    · exact (hΔφ.norm.integrable_of_hasCompactSupport hcΔφ.norm).const_mul _
    · intro n
      exact Eventually.of_forall fun x => by
        by_cases hx : Δ φ x = 0
        · simp only [hx,mul_zero,norm_zero,le_refl]
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hwb n (tfLaplacian_support hφ hx)) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (hwlim x).mul_const (Δ φ x)
  have htL := maxMollify_test_tendsto hh hφ.continuous hcφ
  apply le_of_tendsto_of_tendsto htL htR
  filter_upwards [(shrinkingBump_tendsto (E := TFSpace)).eventually (gt_mem_nhds hδ)] with n hn
  have hks (x : TFSpace) (hx : x ∈ tsupport φ) :
      tsupport (fun y => maxKernel n (x-y)) ⊆ U := by
    intro y hy
    have hxy := tsupport_sub_left (fun z hz => maxKernel_support n hz) x hy
    apply hsδ
    exact mem_cthickening_of_dist_le y x δ (tsupport φ) hx ((mem_closedBall.mp hxy).trans hn.le)
  have hlow (x : TFSpace) (hx : x ∈ tsupport φ) : maxMollify n h x ≤ Δ (w n) x := by
    apply smoothMaximum_laplacian_lower (hε n) (maxMollify_contDiff hu.locallyIntegrable n)
      (maxMollify_contDiff hv.locallyIntegrable n)
    · exact weak_lower_convolution hu hwu (shrinkingBump n).contDiff_normed
        (shrinkingBump n).hasCompactSupport_normed (shrinkingBump n).nonneg_normed (hks x hx)
    · exact weak_lower_convolution hv hwv (shrinkingBump n).contDiff_normed
        (shrinkingBump n).hasCompactSupport_normed (shrinkingBump n).nonneg_normed (hks x hx)
  rw [compact_laplacian_green (hwd n) hφ hcφ]
  apply integral_mono
    (((maxMollify_contDiff hh n).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left)
    (((tfLaplacian_continuous (hwd n)).mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left)
  intro x
  change maxMollify n h x * φ x ≤ Δ (w n) x * φ x
  by_cases hx : φ x = 0
  · simp only [hx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hlow x (subset_tsupport φ hx)) (hnφ x)

end Work_BarrierWeakMaxGeneral_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology Convolution BigOperators Manifold

open CoulombAnalysis CoulombPDE CoulombAtom

lemma locallyIntegrable_mul_test {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x => h x*φ x) :=
  hh.integrable_smul_right_of_hasCompactSupport hφ hcφ

lemma laplacian_finset_sum {ι : Type*} (s : Finset ι) (f : ι → TFSpace → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : TFSpace) :
    Δ (∑ i ∈ s, f i) x = ∑ i ∈ s, Δ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Pi.zero_def,laplacian_const]
  | @insert i s hi ih =>
    have hi' := hf i (Finset.mem_insert_self _ _)
    have hs' : ∀ j ∈ s, ContDiff ℝ 2 (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsD : ContDiff ℝ 2 (∑ j ∈ s, f j) := by
      simpa only [←Finset.sum_apply] using ContDiff.sum hs'
    rw [Finset.sum_insert hi,hi'.contDiffAt.laplacian_add hsD.contDiffAt,
      ih hs',Finset.sum_insert hi]

theorem weak_lower_open_cover {ι : Type*} {V : ι → Set TFSpace}
    (hV : ∀ i, IsOpen (V i)) {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : ∀ i, WeakLaplacianLowerOn (V i) u h) :
    WeakLaplacianLowerOn (⋃ i, V i) u h := by
  classical
  intro φ hφ hcφ hsφ hnφ
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ,TFSpace))
    (isClosed_tsupport φ) V hV hsφ
  let s := (ρ.locallyFinite.finite_nonempty_inter_compact hcφ.isCompact).toFinset
  let ψ : ι → TFSpace → ℝ := fun i x => ρ i x*φ x
  have hψd (i : ι) : ContDiff ℝ 2 (ψ i) :=
    ((ρ i).contMDiff.contDiff.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).mul hφ
  have hψc (i : ι) : HasCompactSupport (ψ i) := hcφ.mul_left
  have hψs (i : ι) : tsupport (ψ i) ⊆ V i := tsupport_mul_subset_left.trans (hρ i)
  have hψn (i : ι) (x : TFSpace) : 0 ≤ ψ i x := mul_nonneg (ρ.nonneg i x) (hnφ x)
  have hψzero {i : ι} (hi : i ∉ s) (x : TFSpace) : ψ i x = 0 := by
    dsimp [ψ]
    by_cases h1 : ρ i x = 0
    · rw [h1,zero_mul]
    · have h2 : φ x = 0 := by
        by_contra h2
        apply hi
        exact (Set.Finite.mem_toFinset _).mpr ⟨x,h1,subset_tsupport φ h2⟩
      rw [h2,mul_zero]
  have hsum : ∑ i ∈ s, ψ i = φ := by
    funext x
    rw [Finset.sum_apply]
    calc
      ∑ i ∈ s, ψ i x = ∑ᶠ i, ψ i x :=
        (finsum_eq_sum_of_support_subset (fun i => ψ i x) (s := s) fun i hi => by
          by_contra hn
          exact hi (hψzero hn x)).symm
      _ = φ x := by
        dsimp only [ψ]
        rw [←finsum_mul]
        by_cases hx : φ x = 0
        · rw [hx,mul_zero]
        · rw [ρ.sum_eq_one (subset_tsupport φ hx),one_mul]
  have hLp : (∫ x, h x*φ x) = ∑ i ∈ s, ∫ x, h x*ψ i x := by
    conv_lhs => rw [←hsum]
    simp only [Finset.sum_apply,Finset.mul_sum]
    exact integral_finsetSum s (fun i _ => locallyIntegrable_mul_test hh (hψd i).continuous (hψc i))
  have hRp : (∫ x, u x*Δ φ x) = ∑ i ∈ s, ∫ x, u x*Δ (ψ i) x := by
    conv_lhs => rw [←hsum]
    simp_rw [laplacian_finset_sum s ψ (fun i _ => hψd i),Finset.mul_sum]
    exact integral_finsetSum s (fun i _ => locallyIntegrable_mul_test hu
      (tfLaplacian_continuous (hψd i)) (tfLaplacian_compact (hψd i) (hψc i)))
  rw [hLp,hRp]
  exact Finset.sum_le_sum fun i _ => hw i _ (hψd i) (hψc i) (hψs i) (hψn i)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNonlinearBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma WeakLaplacianLowerOn.mono_set {U V : Set TFSpace} {u h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hVU : V ⊆ U) : WeakLaplacianLowerOn V u h :=
  fun φ hφ hc hs hn => hw φ hφ hc (hs.trans hVU) hn

lemma WeakLaplacianLowerOn.congr_field {U : Set TFSpace} {u v h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (he : ∀ x ∈ U, u x = v x) :
    WeakLaplacianLowerOn U v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · rw [hx,mul_zero,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakLaplacianLowerOn.source_mono_ae {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ᵐ x, x ∈ U → h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := by
  intro φ hφ hc hs hn
  apply le_trans _ (hw φ hφ hc hs hn)
  apply integral_mono_ae (locallyIntegrable_mul_test hh' hφ.continuous hc)
    (locallyIntegrable_mul_test hh hφ.continuous hc)
  filter_upwards [hle] with x hx
  by_cases hφx : φ x = 0
  · simp only [hφx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hx (hs (subset_tsupport φ hφx))) (hn x)

lemma WeakLaplacianLowerOn.source_mono {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ x ∈ U, h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := hw.source_mono_ae hh hh' (Eventually.of_forall hle)

lemma weak_lower_local {U : Set TFSpace} {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : ∀ x ∈ U, ∃ V : Set TFSpace, IsOpen V ∧ x ∈ V ∧ WeakLaplacianLowerOn V u h) :
    WeakLaplacianLowerOn U u h := by
  choose V hV hxV hW using fun x : U => hw x x.property
  apply (weak_lower_open_cover hV hu hh hW).mono_set
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩

lemma weak_lower_of_constant_errors {U : Set TFSpace} {u h : TFSpace → ℝ}
    (hh : LocallyIntegrable h)
    (hw : ∀ ε > 0, WeakLaplacianLowerOn U u (fun x => h x-ε)) :
    WeakLaplacianLowerOn U u h := by
  intro φ hφ hc hs hn
  have hi := locallyIntegrable_mul_test hh hφ.continuous hc
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
  have he (ε : ℝ) (hε : 0 < ε) :
      (∫ x, h x*φ x)-ε*(∫ x, φ x) ≤ ∫ x, u x*Δ φ x := by
    have ht := hw ε hε φ hφ hc hs hn
    simp_rw [sub_mul] at ht
    rwa [integral_sub hi (hφi.const_mul ε),integral_const_mul] at ht
  have ht := (tendsto_const_nhds (x := ∫ x, h x*φ x)).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (∫ x, φ x))
  have hb := le_of_tendsto ht (Eventually.of_forall fun n : ℕ =>
    he (1/((n:ℝ)+1)) (by positivity))
  simpa only [zero_mul,sub_zero] using hb

lemma semilinear_source_locallyIntegrable {g χ u : TFSpace → ℝ} {F : ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous F) (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*F (u x)) := by
  have hχl : LocallyIntegrable χ :=
    (memLp_top_of_bound hχ.aestronglyMeasurable 1 (Eventually.of_forall hbχ)).locallyIntegrable le_top
  exact hg.add (LocallyIntegrable.mul_continuous (hF.comp hu) hχl)

lemma weighted_max_reaction_le {F : ℝ → ℝ} {a b χ ε : ℝ}
    (hχ : ‖χ‖ ≤ 1) (hε : 0 ≤ ε) (hF : ‖F a-F b‖ ≤ ε) :
    χ*F (max a b)-ε ≤ χ*F a := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    have hb : χ*(F b-F a) ≤ ε := by
      calc
        _ ≤ ‖χ*(F b-F a)‖ := le_abs_self _
        _ = ‖χ‖*‖F a-F b‖ := by rw [norm_mul,norm_sub_rev]
        _ ≤ 1*ε := mul_le_mul hχ hF (norm_nonneg _) (by norm_num)
        _ = ε := one_mul _
    nlinarith
  · rw [max_eq_left hba]
    linarith

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSpatialBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma spatial_source_locallyIntegrable {g χ u : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2)) (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*F x (u x)) := by
  have hχl : LocallyIntegrable χ :=
    (memLp_top_of_bound hχ.aestronglyMeasurable 1 (Eventually.of_forall hbχ)).locallyIntegrable le_top
  exact hg.add (LocallyIntegrable.mul_continuous (hF.comp (continuous_id.prodMk hu)) hχl)

theorem weak_maximum_spatial {U : Set TFSpace} (hU : IsOpen U)
    {u v g χ : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    (hwu : WeakLaplacianLowerOn U u (fun x => g x+χ x*F x (u x)))
    (hwv : WeakLaplacianLowerOn U v (fun x => g x+χ x*F x (v x))) :
    WeakLaplacianLowerOn U (fun x => max (u x) (v x))
      (fun x => g x+χ x*F x (max (u x) (v x))) := by
  let w : TFSpace → ℝ := fun x => max (u x) (v x)
  have hwc : Continuous w := hu.max hv
  have hgu := spatial_source_locallyIntegrable hg hχ hbχ hF hu
  have hgv := spatial_source_locallyIntegrable hg hχ hbχ hF hv
  have hgw := spatial_source_locallyIntegrable hg hχ hbχ hF hwc
  apply weak_lower_of_constant_errors hgw
  intro ε hε
  have hge : LocallyIntegrable (fun x => (g x+χ x*F x (w x))-ε) :=
    hgw.sub (locallyIntegrable_const ε)
  apply weak_lower_local hwc.locallyIntegrable hge
  intro x hx
  by_cases heq : u x = v x
  · let V := U ∩ {y | ‖F y (u y)-F y (v y)‖ < ε}
    have hVo : IsOpen V := hU.inter (isOpen_lt ((hF.comp (continuous_id.prodMk hu)).sub (hF.comp (continuous_id.prodMk hv))).norm continuous_const)
    have hxV : x ∈ V := ⟨hx,by simp only [mem_ofPred_eq,heq,sub_self,norm_zero]; exact hε⟩
    have hcu : WeakLaplacianLowerOn V u (fun x => (g x+χ x*F x (w x))-ε) := by
      apply (hwu.mono_set inter_subset_left).source_mono hgu hge
      intro y hy
      have he := weighted_max_reaction_le (hbχ y) hε.le hy.2.le
      change χ y*F y (w y)-ε ≤ χ y*F y (u y) at he
      linarith
    have hcv : WeakLaplacianLowerOn V v (fun x => (g x+χ x*F x (w x))-ε) := by
      apply (hwv.mono_set inter_subset_left).source_mono hgv hge
      intro y hy
      have he := weighted_max_reaction_le (F := F y) (a := v y) (b := u y)
        (hbχ y) hε.le (by rw [norm_sub_rev]; exact hy.2.le)
      rw [max_comm] at he
      change χ y*F y (w y)-ε ≤ χ y*F y (v y) at he
      linarith
    exact ⟨V,hVo,hxV,weak_maximum_common_locallyIntegrable_source hVo hu hv hge hcu hcv⟩
  · rcases lt_or_gt_of_ne heq with huv | hvu
    · let V := U ∩ {y | u y < v y}
      have hVo : IsOpen V := hU.inter (isOpen_lt hu hv)
      have hvw : ∀ y ∈ V, v y = w y := fun y hy => (max_eq_right hy.2.le).symm
      have he : WeakLaplacianLowerOn V v (fun x => (g x+χ x*F x (w x))-ε) := by
        apply (hwv.mono_set inter_subset_left).source_mono hgv hge
        intro y hy
        rw [←hvw y hy]
        linarith
      exact ⟨V,hVo,⟨hx,huv⟩,he.congr_field hvw⟩
    · let V := U ∩ {y | v y < u y}
      have hVo : IsOpen V := hU.inter (isOpen_lt hv hu)
      have huw : ∀ y ∈ V, u y = w y := fun y hy => (max_eq_left hy.2.le).symm
      have he : WeakLaplacianLowerOn V u (fun x => (g x+χ x*F x (w x))-ε) := by
        apply (hwu.mono_set inter_subset_left).source_mono hgu hge
        intro y hy
        rw [←huw y hy]
        linarith
      exact ⟨V,hVo,⟨hx,hvu⟩,he.congr_field huw⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNuclearBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma nuclearField_locallyIntegrable (Z : ℝ) : LocallyIntegrable (nuclearField Z) := by
  change LocallyIntegrable (fun x : TFSpace => Z*‖x‖⁻¹)
  exact newtonInverse_locallyIntegrable.smul Z

lemma clippedNuclearField_continuous (Z : ℝ) {R : ℝ} (hR : 0 < R) :
    Continuous (clippedNuclearField Z R) := by
  exact continuous_const.div (continuous_const.max continuous_norm)
    (fun x => ne_of_gt (hR.trans_le (le_max_left R ‖x‖)))

lemma weighted_clipped_reaction (Z R : ℝ) {χ : TFSpace → ℝ}
    (hχ : ∀ x, ‖x‖ < R → χ x = 0) (F : ℝ → ℝ) (t : ℝ) (x : TFSpace) :
    χ x*F (nuclearField Z x+t) = χ x*F (clippedNuclearField Z R x+t) := by
  by_cases hx : ‖x‖ < R
  · rw [hχ x hx,zero_mul,zero_mul]
  · simp only [clippedNuclearField,max_eq_right (le_of_not_gt hx),nuclearField]

lemma nuclearField_weak_laplacian (Z : ℝ) {φ : TFSpace → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, nuclearField Z x*Δ φ x) = -(4*Real.pi*Z)*φ 0 := by
  have h := tfPotential_laplacian hφ hc (0 : TFSpace)
  have he : (fun x => nuclearField Z x*Δ φ x) = fun x => Z*(Δ φ x/‖x‖) := by
    funext x
    dsimp only [nuclearField]
    ring
  rw [he,integral_const_mul]
  simp only [tfPotential,zero_sub,norm_neg] at h
  rw [h]
  ring

theorem weakNuclearLower_add_iff {U : Set TFSpace} (Z : ℝ) {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x) h ↔
      WeakLaplacianLowerOn U u h := by
  have he (φ : TFSpace → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
      (∫ x, (nuclearField Z x+u x)*Δ φ x) =
        -(4*Real.pi*Z)*φ 0+(∫ x, u x*Δ φ x) := by
    simp_rw [add_mul]
    rw [integral_add
      (locallyIntegrable_mul_test (nuclearField_locallyIntegrable Z)
        (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc))
      (locallyIntegrable_mul_test hu (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)),
      nuclearField_weak_laplacian Z hφ hc]
  constructor
  · intro hw φ hφ hc hs hn
    have ht := hw φ hφ hc hs hn
    rw [he φ hφ hc] at ht
    exact (add_le_add_iff_left _).mp ht
  · intro hw φ hφ hc hs hn
    rw [he φ hφ hc]
    exact add_le_add_right (hw φ hφ hc hs hn) _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierInitialPoissonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma bounded_density_weak_poisson {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, tfPotential ρ x*Δ φ x) = -(4*Real.pi)*(∫ x, ρ x*φ x) := by
  obtain ⟨S,_,hS⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  apply tfPotential_weak_laplacian_ball (bounded_support_memLp hm hn hb hs (5/3))
    (S := max R S)
  · exact hs.trans (ball_subset_ball (le_max_left _ _))
  · exact hφ
  · exact hc
  · intro x hx
    exact mem_ball_zero_iff.mpr ((hS x hx).trans_le (le_max_right _ _))

lemma initialOffset_continuous {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R) (Z r a : ℝ) :
    Continuous (initialOffset Z r a ρ) := by
  exact ((tfPotential_continuous (bounded_support_integrable hm hn hb hs)
    (bounded_support_memLp hm hn hb hs (5/3))).neg.sub continuous_const).add
      (continuous_const.mul (continuous_norm.pow 2))

lemma initial_polynomial_laplacian (Z r a : ℝ) (x : TFSpace) :
    Δ (fun y : TFSpace => (-(7/10)*Z/r+a*‖y‖^2 : ℝ)) x = 6*a := by
  have hd := (contDiff_norm_sq ℝ : ContDiff ℝ 2 (fun y : TFSpace => ‖y‖^2))
  have ha := ContDiffAt.laplacian_add (x := x)
    (contDiffAt_const (c := (-(7/10)*Z/r : ℝ)))
    ((contDiffAt_const (c := a)).mul hd.contDiffAt)
  change Δ ((fun _ : TFSpace => (-(7/10)*Z/r : ℝ)) + (fun y : TFSpace => a*‖y‖^2)) x = 6*a
  rw [ha,laplacian_const,Pi.zero_apply,zero_add]
  have he := laplacian_smul (x := x) a hd.contDiffAt
  simp only [smul_eq_mul] at he
  change Δ (a • (fun y : TFSpace => ‖y‖^2)) x = 6*a
  rw [he, CoulombPDE.laplacian_norm_sq]
  norm_num [TFSpace,finrank_euclideanSpace_fin]
  ring

lemma initialOffset_weak_poisson {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R) (Z r a : ℝ)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, initialOffset Z r a ρ x*Δ φ x) = ∫ x, (4*Real.pi*ρ x+6*a)*φ x := by
  have hp := tfPotential_continuous (bounded_support_integrable hm hn hb hs)
    (bounded_support_memLp hm hn hb hs (5/3))
  let q : TFSpace → ℝ := fun y => -(7/10)*Z/r+a*‖y‖^2
  have hq : ContDiff ℝ 2 q := contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  have he : initialOffset Z r a ρ = fun x => -tfPotential ρ x+q x := by funext x; dsimp [initialOffset,q]; ring
  have hρ : LocallyIntegrable ρ := (bounded_support_integrable hm hn hb hs).locallyIntegrable
  rw [he]
  simp_rw [add_mul,neg_mul]
  rw [integral_add (f := fun x => -(tfPotential ρ x * Δ φ x)) (g := fun x => q x * Δ φ x) (locallyIntegrable_mul_test hp.locallyIntegrable (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)).neg
    (locallyIntegrable_mul_test hq.continuous.locallyIntegrable (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)),
    integral_neg,bounded_density_weak_poisson hm hn hb hs hφ hc,neg_mul,neg_neg,
    compact_laplacian_green hq hφ hc]
  have hl : Δ q = fun _ => 6*a := funext (initial_polynomial_laplacian Z r a)
  rw [hl]
  have hi : Integrable (fun x => 4*Real.pi*ρ x*φ x) := by
    simpa only [mul_assoc] using (locallyIntegrable_mul_test hρ hφ.continuous hc).const_mul (4*Real.pi)
  rw [integral_add hi ((hφ.continuous.integrable_of_hasCompactSupport hc).const_mul (6*a))]
  congr 1
  calc
    _ = ∫ x, (4*Real.pi)*(ρ x*φ x) := (integral_const_mul (4*Real.pi) _).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun x => by dsimp only; ring)

theorem initialBranch_weak_nuclear {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R) (Z r a : ℝ) :
    WeakNuclearLowerOn univ Z (initialBranch Z r a ρ) (fun x => 4*Real.pi*ρ x+6*a) := by
  apply (weakNuclearLower_add_iff Z (initialOffset_continuous hm hn hb hs Z r a).locallyIntegrable).mpr
  intro φ hφ hc _ _
  exact (initialOffset_weak_poisson hm hn hb hs Z r a hφ hc).ge

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumRawLaw_scope

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CoulombAtom

attribute [local irreducible] graphComponent fermionGraphValue

lemma graphRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ, hn, ENNReal.ofReal_one]

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationIntegral
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationIntegral_scope

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

lemma eventLog_eq {p : ℝ} (hp : 0 < p) : Real.log (Real.exp 1/p) = 1-Real.log p := by
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hp), Real.log_exp]

end Work_ObservationIntegral_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

lemma observationFisherConstant_pos : 0 < observationFisherConstant := by
  unfold observationFisherConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) observationMomentConstant_pos

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

lemma physicalObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (physicalObservedConfiguration (N := N) ell k) := by
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact (((EuclideanSpace.proj a : Space →L[ℝ] ℝ).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    (((measurable_pi_apply (k,i,a)).comp measurable_snd).const_mul _))

lemma unorderedObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (unorderedObservedConfiguration (N := N) ell k) :=
  unorderedConfiguration_measurable.comp (physicalObservedConfiguration_measurable ell k)

lemma observationInformation_le {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j ≤
      (inferInstance : MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (unorderedObservedConfiguration_measurable ell k).comap_le
  · exact bot_le

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma originalDatum_measurable {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    Measurable (originalDatum (N := N) ell j) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap id (observationInformation ell j) ≤ _
  simpa only [MeasurableSpace.comap_id] using (observationInformation_le (N := N) ell j)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

lemma masterWidth_upper {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hs : 0 < s)
    (x : Space) : masterWidth c₁ r₀ s x ≤ c₁*masterBaseDistance r₀ x*s^masterExponent := by
  have hD : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_min hD.le hs.le) (min_le_right _ _) masterExponent_nonneg)
    (mul_nonneg hc hD.le)

lemma masterWidth_lower {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hrs : r₀ ≤ s)
    (x : Space) : c₁*r₀^(1+masterExponent) ≤ masterWidth c₁ r₀ s x := by
  have hD : r₀ ≤ masterBaseDistance r₀ x := le_max_right _ _
  rw [Real.rpow_one_add' hr.le (by linarith [masterExponent_pos])]
  simpa only [masterWidth,mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hD (Real.rpow_le_rpow hr.le (le_min hD hrs) masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hD)) hc

open Set Metric
open scoped NNReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

lemma masterKernel_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ masterKernel c₁ r₀ s g x y := sq_nonneg _

lemma masterKernel_mass {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    ∫ y, masterKernel c₁ r₀ s g x y = 1 := by
  unfold masterKernel
  rw [integral_sub_right_eq_self (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) x,
    scaledRealPacket_mass (masterWidth_pos hc hr hs x) g,hgn]

lemma masterKernel_joint_continuous {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Continuous (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2) := by
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := (masterWidth_lipschitz hc.le hr hs).continuous.comp (continuous_fst : Continuous (Prod.fst : Space × Space → Space))
  have hi := ht.inv₀ (fun p => (masterWidth_pos hc hr hs p.1).ne')
  exact (hi.pow 3).mul ((hg.pow 2).comp (hi.smul (continuous_snd.sub continuous_fst)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterKernelFubini
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAnalysis

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombObservation ProbabilityTheory

lemma originalRawKernel_comp {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) :
    originalRawKernel μ ell j ∘ₘ ((physicalObservationLaw μ K).map (originalDatum ell j)) = μ := by
  rw [originalRawKernel,condDistrib_comp_map (originalDatum_measurable ell j).aemeasurable
    measurable_fst.aemeasurable]
  simp [physicalObservationLaw,Measure.map_fst_prod]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTruncationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierTruncation_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma innerPotential_eq_tfPotential (r : ℝ) (ρ : Space → ℝ) (y : Space) :
    innerPotential r ρ y = tfPotential ((ball (0 : Space) r).indicator ρ) y := by
  unfold innerPotential tfPotential
  rw [←integral_indicator measurableSet_ball]
  congr 1
  funext z
  by_cases hz : z ∈ ball (0 : Space) r <;> simp [hz]

end CoulombAtom

end Work_BarrierTruncation_barrier_scope

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators
open CoulombAnalysis CoulombPDE CoulombAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma average_continuous {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hc : ∀ᵐ sample ∂P, Continuous (u sample)) : Continuous (fun x => ∫ sample, u sample x ∂P) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨C,hC⟩ := hb (closedBall x 1) (isCompact_closedBall x 1)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => C)
  · exact Eventually.of_forall fun y =>
      (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with y hy
    exact Eventually.of_forall fun sample => hC sample y (ball_subset_closedBall hy)
  · exact integrable_const C
  · exact hc.mono fun _ h => h.continuousAt

end Average

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

open CoulombAnalysis CoulombPDE CoulombAtom

lemma DeterministicLocalBound.add {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v) :
    DeterministicLocalBound (fun sample x => u sample x+v sample x) := by
  intro K hK
  obtain ⟨A,hA⟩ := hu K hK
  obtain ⟨B,hB⟩ := hv K hK
  exact ⟨A+B,fun sample x hx => (norm_add_le _ _).trans (add_le_add (hA sample x hx) (hB sample x hx))⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterJointPosterior
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma jointMasterPosterior_nonneg {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : OriginalDatum N K ell j) (y : Space) :
    0 ≤ jointMasterPosterior μ ell j c₁ r₀ s g z y :=
  integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) y))

lemma jointMasterPosterior_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  have h : StronglyMeasurable (fun p : (OriginalDatum N K ell j × Space) × Configuration N =>
      ∑ i, masterKernel c₁ r₀ s g (p.2 i) p.1.2) :=
    (Finset.measurable_sum _ (fun i _ => hm.comp
      (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst.snd))).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := (originalRawKernel μ ell j).comap Prod.fst measurable_fst)).measurable

lemma masterKernel_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    Integrable (masterKernel c₁ r₀ s g x) := by
  by_contra h
  have hm := masterKernel_mass hc hr hs hgn x
  rw [integral_undef h] at hm
  norm_num at hm

lemma masterConfigurationKernel_integrable {N : ℕ} (ν : Measure (Configuration N)) [IsFiniteMeasure ν]
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1) :
    Integrable (fun p : Configuration N × Space => ∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)
      (ν.prod volume) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  apply (integrable_prod_iff ((Finset.measurable_sum _ (fun i _ => hm.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))).aestronglyMeasurable)).mpr
  refine ⟨ae_of_all _ (fun x => integrable_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))),?_⟩
  have he (x : Configuration N) :
      (∫ y, ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖) = (N:ℝ) := by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) _))]
    rw [integral_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))]
    simp only [masterKernel_mass hc hr hs hgn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  change Integrable (fun x : Configuration N => ∫ y, ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖) ν
  simpa only [he] using (integrable_const (N:ℝ) : Integrable (fun _ : Configuration N => (N:ℝ)) ν)

lemma jointMasterPosterior_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    Integrable (jointMasterPosterior μ ell j c₁ r₀ s g z) :=
  (masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn).integral_prod_right

lemma jointMasterPosterior_mass {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    ∫ y, jointMasterPosterior μ ell j c₁ r₀ s g z y = (N:ℝ) := by
  change (∫ y, ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) y ∂originalRawKernel μ ell j z) = _
  rw [←integral_integral_swap (masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn)]
  have he (x : Configuration N) : (∫ y, ∑ i, masterKernel c₁ r₀ s g (x i) y) = (N:ℝ) := by
    rw [integral_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))]
    simp [masterKernel_mass hc hr hs hgn]
  simp_rw [he]
  simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierMasterRegularityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation

lemma masterKernel_global_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖masterKernel c₁ r₀ s g x y‖ ≤ C := by
  have hc2 : HasCompactSupport (fun x => (g x)^2) := hcg.mul_left
  obtain ⟨z,hz⟩ := (hg.pow 2).norm.exists_forall_ge_of_hasCompactSupport hc2.norm
  let δ := c₁*r₀^(1+masterExponent)
  have hδ : 0 < δ := mul_pos hc (Real.rpow_pos_of_pos hr _)
  refine ⟨δ⁻¹^3*‖(g z)^2‖,by positivity,fun x y => ?_⟩
  have hi : (masterWidth c₁ r₀ s x)⁻¹ ≤ δ⁻¹ := by
    apply inv_anti₀ hδ
    exact masterWidth_lower hc.le hr hrs x
  rw [masterKernel,scaledRealPacket_sq (masterWidth_pos hc hr hs x),norm_mul,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) 3)]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) hi 3)
    (hz _) (norm_nonneg _) (by positivity)

attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma masterConfigurationDensity_measurable {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (masterConfigurationDensity (N := N) c₁ r₀ s g)) := by
  have hm (i : Fin N) : Measurable (fun p : Configuration N × Space =>
      masterKernel c₁ r₀ s g (p.1 i) p.2) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun p : Configuration N × Space => (p.1 i,p.2))
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  exact Finset.measurable_sum Finset.univ (fun i _ => hm i)

lemma masterConfigurationDensity_continuous {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g)
    (z : Configuration N) : Continuous (masterConfigurationDensity c₁ r₀ s g z) := by
  have ht (i : Fin N) : Continuous (fun y : Space => masterKernel c₁ r₀ s g (z i) y) :=
    (masterKernel_joint_continuous hc hr hs hg).comp
      (f := fun y : Space => (z i,y)) (continuous_const.prodMk continuous_id)
  exact continuous_finsetSum Finset.univ (fun i _ => ht i)

lemma masterConfigurationDensity_bound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z y, ‖masterConfigurationDensity (N := N) c₁ r₀ s g z y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterKernel_global_bound hc hr hs hrs hg hcg
  refine ⟨N*C,by positivity,fun z y => ?_⟩
  calc
    _ ≤ ∑ i : Fin N, ‖masterKernel c₁ r₀ s g (z i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hC (z i) y)
    _ = N*C := by simp

lemma masterConfigurationDensity_deterministicBound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    DeterministicLocalBound (masterConfigurationDensity (N := N) c₁ r₀ s g) := by
  obtain ⟨C,_,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  exact fun _ _ => ⟨C,fun z y _ => hC z y⟩

lemma jointMasterPosterior_continuous {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (d : OriginalDatum N K ell j) :
    Continuous (jointMasterPosterior μ ell j c₁ r₀ s g d) := by
  exact average_continuous (masterConfigurationDensity_measurable hc hr hs hg)
    (masterConfigurationDensity_deterministicBound hc hr hs hrs hg hcg)
    (Eventually.of_forall (masterConfigurationDensity_continuous hc hr hs hg))

lemma jointMasterPosterior_global_bound {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d y, ‖jointMasterPosterior μ ell j c₁ r₀ s g d y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  refine ⟨C,hCn,fun d y => ?_⟩
  calc
    _ ≤ ∫ _ : Configuration N, C ∂originalRawKernel μ ell j d :=
      norm_integral_le_of_norm_le (integrable_const C) (Eventually.of_forall fun z => hC z y)
    _ = C := by simp

end CoulombBarrier

end Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierObservationTowerBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma originalMasterField_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (originalMasterField μ ell j c₁ r₀ s g)) :=
  (jointMasterPosterior_measurable μ ell j hc hr hs hg).comp
    (((originalDatum_measurable ell j).comp measurable_fst).prodMk measurable_snd)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BoundedL1PotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_coulomb_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z/‖x-z‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [hn z]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hd' : 1 ≤ ‖x-z‖ := le_of_not_gt hd
    exact (div_le_self (hn z) hd')

lemma bounded_invSquare_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z*‖x-z‖⁻¹^2 ≤ M*truncatedInvSquare 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedInvSquare,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (sq_nonneg ‖x-z‖⁻¹)
    linarith [hn z]
  · rw [truncatedInvSquare,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hi : ‖x-z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_gt hd)
    have hi0 := inv_nonneg.mpr (norm_nonneg (x-z))
    have hs : ‖x-z‖⁻¹^2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs (hn z)).trans_eq (mul_one _)

lemma bounded_L1_potential_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  apply ((hk.const_mul M).add hi).mono' (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/‖x-z‖‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact bounded_coulomb_majorant hM hn hb x z

lemma bounded_L1_potential_difference {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x y : TFSpace) :
    |tfPotential ρ x-tfPotential ρ y| ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖ := by
  have hpi (w : TFSpace) := bounded_L1_potential_integrable hm hi hM hn hb w
  let A (w z : TFSpace) := M*truncatedInvSquare 1 (w-z)+ρ z
  have hk (w : TFSpace) : Integrable (fun z => truncatedInvSquare 1 (w-z)) :=
    (tfSubMap_preserving w).integrable_comp (truncatedInvSquare_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedInvSquare_integrable 1)
  have hAi (w : TFSpace) : Integrable (A w) := ((hk w).const_mul M).add hi
  have hAm (w : TFSpace) : (∫ z, A w z) = 4*Real.pi*M+∫ z, ρ z := by
    dsimp only [A]
    rw [integral_add ((hk w).const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
      truncatedInvSquare_integral (by norm_num : (0:ℝ) < 1)]
    ring
  have he : (∫ z, ρ z/‖x-z‖-ρ z/‖y-z‖) = tfPotential ρ x-tfPotential ρ y :=
    integral_sub (hpi x) (hpi y)
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, (‖x-y‖/2)*(A x z+A y z) := by
      apply integral_mono_ae ((hpi x).sub (hpi y)).abs (((hAi x).add (hAi y)).const_mul _)
      filter_upwards [volume.ae_ne x,volume.ae_ne y] with z hzx hzy
      change |ρ z/‖x-z‖-ρ z/‖y-z‖| ≤ _
      rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul,abs_of_nonneg (hn z)]
      calc
        _ ≤ ρ z*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
          mul_le_mul_of_nonneg_left (coulomb_inv_difference hzx hzy) (hn z)
        _ = (‖x-y‖/2)*(ρ z*‖x-z‖⁻¹^2+ρ z*‖y-z‖⁻¹^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
          (bounded_invSquare_majorant hM hn hb x z) (bounded_invSquare_majorant hM hn hb y z)) (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_add (hAi x) (hAi y),hAm,hAm]
      ring

lemma bounded_L1_potential_lipschitz {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) :
    LipschitzWith ⟨4*Real.pi*M+∫ z, ρ z,add_nonneg (by positivity) (integral_nonneg hn)⟩ (tfPotential ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖tfPotential ρ x-tfPotential ρ y‖ ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖
  simpa only [Real.norm_eq_abs] using bounded_L1_potential_difference hm hi hM hn hb x y

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ActualMasterCenterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma graphFormVector_sobolev {N : ℕ} (F : fermionGraph N) :
    SobolevFermion (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_⟩
  · intro s i a
    exact (mem_weakGraph _ _).mp (F.val s).property (i,a)
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s

lemma formRawLaw_graph {N : ℕ} (F : fermionGraph N) :
    formRawLaw (graphFormVector F) = graphRawLaw F := rfl

lemma formMass_graph {N : ℕ} (F : fermionGraph N) :
    formMass (graphFormVector F) = ‖fermionGraphValue N F‖^2 := by
  rw [←formRawDensity_integral (graphFormVector_sobolev F).sobolevVector]
  exact graphRawDensity_integral F

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedSelectedMaster
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma priced_graph_tilt_excess {Z lam e : ℝ} {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) (G : fermionGraph N)
    (hn : ‖fermionGraphValue N G‖^2 = 1)
    (hE : formEnergy Z (graphFormVector G) ≤ energy Z N+e) :
    corePriceExcess Z lam (graphFormVector G) ≤ e := by
  rw [corePriceExcess,formMass_graph,hn,mul_one,mul_one,priceEnergy_eq_of_minimizes hN]
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_UnshiftedCellCountBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma masterWidth_radius_lower {c₁ r₀ s r : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r)
    (hrs : r ≤ s) {y : Space} (hy : r ≤ ‖y‖) :
    c₁*r^(1+masterExponent) ≤ masterWidth c₁ r₀ s y := by
  have hd : r ≤ masterBaseDistance r₀ y := hy.trans (le_max_left _ _)
  have hm : r ≤ min (masterBaseDistance r₀ y) s := le_min hd hrs
  rw [masterWidth,Real.rpow_add hr]
  simp only [Real.rpow_one]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hd (Real.rpow_le_rpow hr.le hm masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hd)) hc

lemma masterWidth_radius_upper {c₁ r₀ s r : ℝ} (hc : 0 ≤ c₁)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrr : r₀ ≤ r)
    {y : Space} (hy : r ≤ ‖y‖) (hy2 : ‖y‖ ≤ 2*r) :
    masterWidth c₁ r₀ s y ≤ 2*c₁*r := by
  have hm : masterBaseDistance r₀ y = ‖y‖ := max_eq_left (hrr.trans hy)
  have hb := masterWidth_upper hc hr₀ hs y
  rw [hm] at hb
  have hpow := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  calc
    _ ≤ c₁*‖y‖*s^masterExponent := hb
    _ ≤ c₁*‖y‖*1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hc (norm_nonneg _))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hy2 hc]

lemma rawBallCount_le_annular {N : ℕ} {y : Space} {r R : ℝ}
    (_hr : 0 ≤ r) (hy : r ≤ ‖y‖) (hy2 : ‖y‖ ≤ 2*r) (hR : R ≤ r/2)
    (x : Configuration N) : rawBallCount y R x ≤ rawAnnularCount (r/2) (3*r) x := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h hA hA
  · norm_num
  · exfalso
    apply hA
    have hxy : ‖x i-y‖ ≤ r/2 := h.le.trans hR
    have hlo := norm_sub_norm_le y (x i)
    rw [norm_sub_rev y (x i)] at hlo
    have hup := norm_sub_norm_le (x i) y
    constructor <;> linarith
  · norm_num
  · norm_num

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPosteriorCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_potential_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma dyadicUniformEventBudget_mono {r p₀ p δ : ℝ}
    (hr : 0 < r) (h₀ : 0 < p₀) (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/p))^5+δ ≤
      dyadicUniformEventBudget r p₀ δ := by
  have hp' : 0 < p := h₀.trans_le hp
  have hlog : 0 ≤ Real.log (Real.exp 1/p) := by
    rw [eventLog_eq hp']
    linarith [Real.log_nonpos hp'.le hp1]
  have hh : Real.log (Real.exp 1/p) ≤ Real.log (Real.exp 1/p₀) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left (Real.exp_pos 1).le h₀ hp
  unfold dyadicUniformEventBudget
  exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hh 5)
    (mul_nonneg observationFisherConstant_pos.le (Real.rpow_nonneg hr.le _))) le_rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_InverseThresholdLimitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma localTFResponse_rescale {a : ℝ} (ha : 0 < a) (h : ℝ) :
    a^6*localTFResponse h = localTFResponse (a^4*h) := by
  have he : max (a^4*h) 0 = a^4*max h 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le _),mul_zero]
  have hT := tfKinetic_pos
  unfold localTFResponse
  rw [he,mul_div_assoc,Real.mul_rpow (pow_nonneg ha.le _) (by positivity),
    ←Real.rpow_natCast a 4,←Real.rpow_mul ha.le]
  norm_num

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PosteriorSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

open CoulombAnalysis CoulombObservation CoulombBarrier

open MeasureTheory Set Metric

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma originalQueryDensity_bounded_L1 {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ),
      Measurable (originalQueryDensity F r j c₁ r₀ s z) ∧
      Integrable (originalQueryDensity F r j c₁ r₀ s z) ∧
      (∀ y, 0 ≤ originalQueryDensity F r j c₁ r₀ s z y) ∧
      (∀ y, originalQueryDensity F r j c₁ r₀ s z y ≤ M) := by
  let ell := fun k : Fin K => dyadicObservationWidth r k
  have hm := originalMasterField_measurable (graphRawLaw F) ell j hc hr₀ hs
    canonicalRealPacket_smooth.continuous
  obtain ⟨M,hM,hb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr₀ hs hrs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
  refine ⟨M,hM,fun z => ⟨?_,?_,?_,?_⟩⟩
  · exact hm.comp ((measurable_const (a := z)).prodMk measurable_id)
  · exact jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr₀ hs
      canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized (originalDatum ell j z)
  · exact jointMasterPosterior_nonneg (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)
  · intro y
    apply (le_abs_self _).trans
    change |jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y| ≤ M
    simpa only [Real.norm_eq_abs] using hb (originalDatum ell j z) y

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_OriginalFieldOscillationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OriginalFieldOscillation_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma originalQueryField_continuousOn_punctured {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    ContinuousOn (originalQueryField F Z lam r j c₁ r₀ s z) {0}ᶜ := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  have hp := (bounded_L1_potential_lipschitz (hρ z).1 (hρ z).2.1 hM
    (hρ z).2.2.1 (hρ z).2.2.2).continuous
  apply ((continuousOn_const.div continuous_norm.continuousOn ?_).sub continuousOn_const).sub hp.continuousOn
  intro x hx
  exact norm_ne_zero_iff.mpr hx

end CoulombAtom

end Work_OriginalFieldOscillation_barrier_scope

open MeasureTheory Filter Set Metric

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierRetainedComparisonBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis CoulombPDE CoulombAtom

lemma classical_weak_lower {U : Set TFSpace} (hU : IsOpen U)
    {u h : TFSpace → ℝ} (hu : Continuous u) (hh : LocallyIntegrable h)
    (hd : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hle : ∀ x ∈ U, h x ≤ Δ u x) :
    WeakLaplacianLowerOn U u h := by
  apply weak_lower_local hu.locallyIntegrable hh
  intro x hx
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x := ⟨r/2,3*r/4,by positivity,by linarith⟩
  let v : TFSpace → ℝ := fun y => b y*u y
  have hv : ContDiff ℝ 2 v := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact b.contDiffAt.mul (hd y hy)
    · have hyb : y ∉ tsupport b := by
        intro hyb
        have hb : dist y x ≤ 3*r/4 := by
          simpa only [ContDiffBump.tsupport_eq,mem_closedBall] using hyb
        exact hy (hsub (mem_ball.mpr (by linarith)))
      apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hyb] with z hz
      simp only [v,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  have he {y : TFSpace} (hy : y ∈ ball x (r/2)) : v =ᶠ[𝓝 y] u := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp only [v,b.one_of_mem_closedBall (ball_subset_closedBall hz),one_mul]
  refine ⟨ball x (r/2),isOpen_ball,mem_ball_self (by positivity),?_⟩
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ y, Δ v y*φ y := by
      apply integral_mono (locallyIntegrable_mul_test hh hφ.continuous hc)
        (locallyIntegrable_mul_test (tfLaplacian_continuous hv).locallyIntegrable hφ.continuous hc)
      intro y
      dsimp only
      by_cases hy : φ y = 0
      · simp only [hy,mul_zero,le_refl]
      · have hym := hs (subset_tsupport φ hy)
        rw [(laplacian_congr_nhds (he hym)).eq_of_nhds]
        exact mul_le_mul_of_nonneg_right (hle y (hsub (ball_subset_ball (by linarith) hym))) (hn y)
    _ = ∫ y, v y*Δ φ y := (compact_laplacian_green hv hφ hc).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun y => by
      dsimp only
      by_cases hy : Δ φ y = 0
      · simp only [hy,mul_zero]
      · rw [(he (hs (tfLaplacian_support hφ hy))).eq_of_nhds])

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTowerBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSourceTower_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma outerCoefficient_measurable (R : ℝ) : Measurable (outerCoefficient R) :=
  Measurable.ite (measurableSet_le measurable_const continuous_norm.measurable)
    measurable_const measurable_const

lemma outerCoefficient_bound (R : ℝ) (x : TFSpace) : ‖outerCoefficient R x‖ ≤ 1 := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_zero (R : ℝ) (x : TFSpace) (hx : ‖x‖ < R) :
    outerCoefficient R x = 0 := ite_eq_right (not_le_of_gt hx)

end Work_BarrierSourceTower_barrier_scope

open Set Filter Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

lemma radialPower_neg_two (x : Space) : radialPower (-2) x = (‖x‖^4)⁻¹ := by
  unfold radialPower
  rw [Real.rpow_neg (sq_nonneg _),Real.rpow_two]
  congr 1
  ring

lemma radialPower_neg_three (x : Space) : radialPower (-3) x = (‖x‖^6)⁻¹ := by
  unfold radialPower
  rw [Real.rpow_neg (sq_nonneg _),show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_natCast]
  congr 1
  ring

lemma outerBarrier_eq_combination (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    outerBarrier B r x = radialCombination B (-B*r/8) (1/2) 0 x := by
  rw [radialCombination_factor _ _ _ _ hx,radialPower_half_inv,radialPower_neg_two]
  unfold outerBarrier
  ring

lemma outerBarrier_contDiffAt (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (outerBarrier B r) x := by
  apply (radialCombination_contDiffAt B (-B*r/8) (1/2) 0 hx).congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  exact outerBarrier_eq_combination B r hy

lemma outerBarrier_laplacian (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    Δ (outerBarrier B r) x = B/‖x‖^6*(12-20*r/(8*‖x‖)) := by
  have he : outerBarrier B r =ᶠ[𝓝 x] radialCombination B (-B*r/8) (1/2) 0 := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact outerBarrier_eq_combination B r hy
  rw [(laplacian_congr_nhds he).eq_of_nhds,radialCombination_laplacian _ _ _ _ hx,
    radialPower_half_inv,radialPower_neg_three]
  ring

lemma outerBarrier_bounds {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    {x : Space} (hx : r ≤ ‖x‖) :
    (7*B/8)/‖x‖^4 ≤ outerBarrier B r x ∧ outerBarrier B r x ≤ B/‖x‖^4 := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hq0 : 0 ≤ r/(8*‖x‖) := by positivity
  have hq1 : r/(8*‖x‖) ≤ 1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hb : 0 ≤ B/‖x‖^4 := by positivity
  unfold outerBarrier
  constructor
  · calc
      _ = (B/‖x‖^4)*(7/8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hb
  · calc
      _ ≤ (B/‖x‖^4)*1 := mul_le_mul_of_nonneg_left (by linarith) hb
      _ = _ := mul_one _

theorem outerBarrier_subsolution {B r k : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hk : 0 ≤ k) (hsmall : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {x : Space} (hx : r ≤ ‖x‖) :
    4*Real.pi*k*(max (outerBarrier B r x) 0)^(3/2:ℝ) ≤ Δ (outerBarrier B r) x := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp hd.ne'
  obtain ⟨hl,hu⟩ := outerBarrier_bounds hB.le hr hx
  have hn : 0 ≤ outerBarrier B r x := (by positivity : 0 ≤ (7*B/8)/‖x‖^4).trans hl
  have hc : 0 ≤ 4*Real.pi*k := by positivity
  have hreact : (B/‖x‖^4)^(3/2:ℝ) = radialPower (-3) x*B^(3/2:ℝ) := by
    rw [← radial_scaled_reaction hB.le x,radialPower_neg_two]
    congr 1
    ring
  have hq : r/(8*‖x‖) ≤ 1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  calc
    _ ≤ 4*Real.pi*k*(B/‖x‖^4)^(3/2:ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (max_le hu (by positivity)) (by norm_num)) hc
    _ = (4*Real.pi*k*Real.sqrt B)*B/‖x‖^6 := by
      rw [hreact,rpow_three_halves B hB.le,← Real.sqrt_eq_rpow,radialPower_neg_three]
      ring
    _ ≤ (19/2)*B/‖x‖^6 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall hB.le) (by positivity)
    _ ≤ B/‖x‖^6*(12-20*r/(8*‖x‖)) := by
      have hp : 0 ≤ B/‖x‖^6 := by positivity
      have hq' : 20*r/(8*‖x‖) ≤ 5/2 := by
        calc
          _ = 20*(r/(8*‖x‖)) := by ring
          _ ≤ _ := by linarith
      calc
        _ = (B/‖x‖^6)*(19/2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hp
    _ = _ := (outerBarrier_laplacian B r hx0).symm

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOuterWeakBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis

lemma clippedOuterBarrier_continuous (B : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (clippedOuterBarrier B r) := by
  have hm : Continuous (fun x : TFSpace => max r ‖x‖) := continuous_const.max continuous_norm
  have hn (x : TFSpace) : max r ‖x‖ ≠ 0 := (hr.trans_le (le_max_left _ _)).ne'
  exact (continuous_const.div (hm.pow 4) (fun x => pow_ne_zero _ (hn x))).mul
    (continuous_const.sub (continuous_const.div (continuous_const.mul hm)
      (fun x => mul_ne_zero (by norm_num) (hn x))))

lemma outerOffset_continuous (Z B : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (outerOffset Z B r) :=
  (clippedOuterBarrier_continuous B hr).sub (clippedNuclearField_continuous Z hr)

lemma clippedOuterBarrier_eq {B r : ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) :
    clippedOuterBarrier B r x = outerBarrier B r x := by
  simp only [clippedOuterBarrier,outerBarrier,max_eq_right hx]

lemma nuclear_outerOffset_eq {Z B r : ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) :
    nuclearField Z x+outerOffset Z B r x = outerBarrier B r x := by
  simp only [outerOffset,clippedNuclearField,max_eq_right hx,
    clippedOuterBarrier_eq hx,nuclearField]
  ring

lemma WeakNuclearLowerOn.mono_set {U V : Set TFSpace} {Z : ℝ} {u h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (hVU : V ⊆ U) :
    WeakNuclearLowerOn V Z u h := fun φ hφ hc hs hn => hw φ hφ hc (hs.trans hVU) hn

lemma weakNuclearLower_iff_off_origin {U : Set TFSpace} (hU : (0 : TFSpace) ∉ U)
    (Z : ℝ) (u h : TFSpace → ℝ) :
    WeakNuclearLowerOn U Z u h ↔ WeakLaplacianLowerOn U u h := by
  have hzero {φ : TFSpace → ℝ} (hs : tsupport φ ⊆ U) : φ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx => hU (hs hx))
  constructor
  · intro hw φ hφ hc hs hn
    have hh := hw φ hφ hc hs hn
    simpa only [hzero hs,mul_zero,zero_add] using hh
  · intro hw φ hφ hc hs hn
    simpa only [hzero hs,mul_zero,zero_add] using hw φ hφ hc hs hn

lemma WeakNuclearLowerOn.congr_field {U : Set TFSpace} {Z : ℝ} {u v h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, u x = v x) :
    WeakNuclearLowerOn U Z v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (ae_of_all _ fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · simp only [hx,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakNuclearLowerOn.congr_source {U : Set TFSpace} {Z : ℝ} {u h h' : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, h x = h' x) :
    WeakNuclearLowerOn U Z u h' := by
  intro φ hφ hc hs hn
  have hh : (∫ x, h' x*φ x) = ∫ x, h x*φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : φ x = 0
    · simp only [hx,mul_zero]
    · rw [he x (hs (subset_tsupport φ hx))]
  rw [hh]
  exact hw φ hφ hc hs hn

theorem outerOffset_weak_nuclear {B r k : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hk : 0 ≤ k) (hsmall : 4*Real.pi*k*Real.sqrt B ≤ 19/2) (Z : ℝ) :
    WeakNuclearLowerOn {x : TFSpace | r < ‖x‖} Z
      (fun x => nuclearField Z x+outerOffset Z B r x)
      (fun x => reaction k (nuclearField Z x+outerOffset Z B r x)) := by
  have he {x : TFSpace} (hx : r < ‖x‖) :
      clippedOuterBarrier B r =ᶠ[𝓝 x] outerBarrier B r := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact clippedOuterBarrier_eq hy.le
  have hc := clippedOuterBarrier_continuous B hr
  have hw := classical_weak_lower (isOpen_lt continuous_const continuous_norm) hc
    ((reaction_continuous k).comp hc).locallyIntegrable
    (fun x hx => (outerBarrier_contDiffAt B r (norm_ne_zero_iff.mp (hr.trans hx).ne')).congr_of_eventuallyEq (he hx))
    (fun x hx => by
      dsimp only [Function.comp_def]
      rw [clippedOuterBarrier_eq hx.le,(laplacian_congr_nhds (he hx)).eq_of_nhds]
      exact outerBarrier_subsolution hB hr hk hsmall hx.le)
  have hn := (weakNuclearLower_iff_off_origin (Z := Z)
    (u := clippedOuterBarrier B r) (h := fun x => reaction k (clippedOuterBarrier B r x))
    (by change ¬ r < ‖(0:TFSpace)‖; simpa only [norm_zero,not_lt] using hr.le)).mpr hw
  apply (hn.congr_field (fun x hx => (clippedOuterBarrier_eq hx.le).trans (nuclear_outerOffset_eq hx.le).symm)).congr_source
  intro x hx
  rw [clippedOuterBarrier_eq hx.le,nuclear_outerOffset_eq hx.le]

end Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma nuclear_source_locallyIntegrable (Z k : ℝ) {r : ℝ} (hr : 0 < r)
    {g χ u : TFSpace → ℝ} (hg : LocallyIntegrable g) (hχ : Measurable χ)
    (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*reaction k (nuclearField Z x+u x)) := by
  simp_rw [weighted_clipped_reaction Z r hzero]
  exact semilinear_source_locallyIntegrable hg hχ hbχ (reaction_continuous k)
    ((clippedNuclearField_continuous Z hr).add hu)

lemma nuclear_weak_maximum {U : Set TFSpace} (hU : IsOpen U) (Z k : ℝ)
    {r : ℝ} (hr : 0 < r) {u v g χ : TFSpace → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hwu : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u x)))
    (hwv : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+v x))) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+max (u x) (v x))
      (fun x => g x+χ x*reaction k (nuclearField Z x+max (u x) (v x))) := by
  rw [weakNuclearLower_add_iff Z (hu.max hv).locallyIntegrable]
  simp_rw [weighted_clipped_reaction Z r hzero]
  apply weak_maximum_spatial hU hu hv hg hχ hbχ
    (F := fun x t => reaction k (clippedNuclearField Z r x+t))
    ((reaction_continuous k).comp (((clippedNuclearField_continuous Z hr).comp continuous_fst).add continuous_snd))
  · simpa only [weighted_clipped_reaction Z r hzero] using
      (weakNuclearLower_add_iff Z hu.locallyIntegrable).mp hwu
  · simpa only [weighted_clipped_reaction Z r hzero] using
      (weakNuclearLower_add_iff Z hv.locallyIntegrable).mp hwv

lemma WeakNuclearLowerOn.source_mono {U : Set TFSpace} {Z : ℝ} {u h h' : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (hh : LocallyIntegrable h) (hh' : LocallyIntegrable h')
    (hle : ∀ x ∈ U, h' x ≤ h x) : WeakNuclearLowerOn U Z u h' := by
  intro φ hφ hc hs hn
  apply le_trans _ (hw φ hφ hc hs hn)
  apply add_le_add_right
  apply integral_mono (locallyIntegrable_mul_test hh' hφ.continuous hc)
    (locallyIntegrable_mul_test hh hφ.continuous hc)
  intro x
  dsimp only
  by_cases hx : φ x = 0
  · simp only [hx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hle x (hs (subset_tsupport φ hx))) (hn x)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Cut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierGluing_barrier_scope
open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff
open CoulombAnalysis
variable {r t L R : ℝ} {u v : TFSpace → ℝ}
variable (hrt : r < t) (htL : t < L) (hLR : L < R)
variable (hlo : ∀ x, r ≤ ‖x‖ → ‖x‖ < t → v x ≤ u x)
variable (hhi : ∀ x, L < ‖x‖ → ‖x‖ < R → u x ≤ v x)

include htL hLR hlo in
lemma cutMaximum_inner {x : TFSpace} (hx : ‖x‖ < t) : cutMaximum r R u v x = u x := by
  unfold cutMaximum
  split_ifs with h1 h2
  · rfl
  · exact max_eq_left (hlo x (le_of_not_gt h1) hx)
  · exact False.elim (h2 (hx.trans (htL.trans hLR)))

lemma cutMaximum_middle {x : TFSpace} (hx : r < ‖x‖) (hR : ‖x‖ < R) :
    cutMaximum r R u v x = max (u x) (v x) := by
  simp only [cutMaximum,ite_eq_right (not_lt.mpr hx.le),ite_eq_left hR]

include hrt htL hhi in
lemma cutMaximum_outer {x : TFSpace} (hx : L < ‖x‖) : cutMaximum r R u v x = v x := by
  unfold cutMaximum
  rw [ite_eq_right (not_lt.mpr ((hrt.trans htL).trans hx).le)]
  split_ifs with hR
  · exact max_eq_right (hhi x hx hR)
  · rfl

include hrt htL hLR hlo hhi in
lemma cutMaximum_continuous (hu : Continuous u) (hv : Continuous v) :
    Continuous (cutMaximum r R u v) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ‖x‖ < t
  · apply hu.continuousAt.congr
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact (cutMaximum_inner htL hLR hlo hy).symm
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      apply (hu.max hv).continuousAt.congr
      filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hx',hR⟩] with y hy
      exact (cutMaximum_middle hy.1 hy.2).symm
    · have hL : L < ‖x‖ := hLR.trans_le (le_of_not_gt hR)
      apply hv.continuousAt.congr
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hL] with y hy
      exact (cutMaximum_outer hrt htL hhi hy).symm

include hrt htL hLR hlo hhi in

theorem cutMaximum_weak_nuclear (Z k : ℝ) (hr : 0 < r)
    (hu : Continuous u) (hv : Continuous v) {g χ : TFSpace → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hui : WeakNuclearLowerOn {x : TFSpace | ‖x‖ < t} Z (fun x => nuclearField Z x+u x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u x)))
    (hum : WeakNuclearLowerOn {x : TFSpace | r < ‖x‖ ∧ ‖x‖ < R} Z (fun x => nuclearField Z x+u x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u x)))
    (hvm : WeakNuclearLowerOn {x : TFSpace | r < ‖x‖ ∧ ‖x‖ < R} Z (fun x => nuclearField Z x+v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+v x)))
    (hvo : WeakNuclearLowerOn {x : TFSpace | L < ‖x‖} Z (fun x => nuclearField Z x+v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+v x))) :
    WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+cutMaximum r R u v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+cutMaximum r R u v x)) := by
  have hc := cutMaximum_continuous hrt htL hLR hlo hhi hu hv
  have hg' := nuclear_source_locallyIntegrable Z k hr hg hχ hbχ hzero hc
  rw [weakNuclearLower_add_iff Z hc.locallyIntegrable]
  apply weak_lower_local hc.locallyIntegrable hg'
  intro x _
  have transfer {V : Set TFSpace} {w : TFSpace → ℝ}
      (hw : WeakNuclearLowerOn V Z (fun y => nuclearField Z y+w y)
        (fun y => g y+χ y*reaction k (nuclearField Z y+w y)))
      (he : ∀ y ∈ V, w y = cutMaximum r R u v y) :
      WeakLaplacianLowerOn V (cutMaximum r R u v)
        (fun y => g y+χ y*reaction k (nuclearField Z y+cutMaximum r R u v y)) := by
    have hn := hw.congr_field (fun y hy => congrArg (nuclearField Z y+·) (he y hy))
    have hn' := hn.congr_source (fun y hy => by rw [he y hy])
    exact (weakNuclearLower_add_iff Z hc.locallyIntegrable).mp hn'
  by_cases hx : ‖x‖ < t
  · exact ⟨{y | ‖y‖ < t},isOpen_lt continuous_norm continuous_const,hx,
      transfer hui (fun y hy => (cutMaximum_inner htL hLR hlo hy).symm)⟩
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      have hopen : IsOpen {y : TFSpace | r < ‖y‖ ∧ ‖y‖ < R} := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
      exact ⟨{y | r < ‖y‖ ∧ ‖y‖ < R},hopen,⟨hx',hR⟩,
        transfer (nuclear_weak_maximum hopen Z k hr hu hv hg hχ hbχ hzero hum hvm)
          (fun y hy => (cutMaximum_middle hy.1 hy.2).symm)⟩
    · exact ⟨{y | L < ‖y‖},isOpen_lt continuous_const continuous_norm,hLR.trans_le (le_of_not_gt hR),
        transfer hvo (fun y hy => (cutMaximum_outer hrt htL hhi hy).symm)⟩

end Work_BarrierGluing_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology

open CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialBoundsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialBounds_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma initial_quadratic_bound {Z r a d : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (hs : 4*a*r^2 ≤ Z/(20*r)) (hd : 0 ≤ d) (hd2 : d ≤ 2*r) :
    a*d^2 ≤ Z/(20*r) := by
  have hh : d^2 ≤ (2*r)^2 := by nlinarith
  calc
    _ ≤ a*(2*r)^2 := mul_le_mul_of_nonneg_left hh ha
    _ = 4*a*r^2 := by ring
    _ ≤ _ := hs

lemma initial_branch_lower {Z r a : ℝ} (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a)
    {ρ : TFSpace → ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) (hx1 : ‖x‖ ≤ (53/50)*r)
    (hp : tfPotential ρ x ≤ Z/(10*r)) :
    (7/50)*(Z/r) < initialBranch Z r a ρ x := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hv : (50/53)*(Z/r) ≤ Z/‖x‖ := by
    apply (le_div_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hx1 (show 0 ≤ (50/53)*(Z/r) by positivity)
    have he : (50/53)*(Z/r)*((53/50)*r) = Z := by field_simp
    exact hh.trans_eq he
  have hp' : Z/(10*r) = (1/10)*(Z/r) := by ring
  have hv' : 0 ≤ a*‖x‖^2 := by positivity
  simp only [initialBranch,initialOffset,nuclearField,mul_div_assoc]
  rw [hp'] at hp
  have hzr : 0 < Z/r := div_pos hZ hr
  nlinarith

lemma initial_branch_upper {Z r a : ℝ} (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a)
    (hs : 4*a*r^2 ≤ Z/(20*r)) {ρ : TFSpace → ℝ} {x : TFSpace}
    (hx : r ≤ ‖x‖) (hx2 : ‖x‖ ≤ 2*r) (hp : 0 ≤ tfPotential ρ x) :
    initialBranch Z r a ρ x ≤ 2*(Z/r) := by
  have hv := div_le_div_of_nonneg_left hZ.le hr hx
  have hq := initial_quadratic_bound hr ha hs (norm_nonneg x) hx2
  have he : Z/(20*r) = (1/20)*(Z/r) := by ring
  rw [he] at hq
  have hn : 0 ≤ Z/r := by positivity
  simp only [initialBranch,initialOffset,nuclearField,mul_div_assoc]
  nlinarith

lemma initial_branch_negative {Z r a : ℝ} (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a)
    (hs : 4*a*r^2 ≤ Z/(20*r)) {ρ : TFSpace → ℝ} {x : TFSpace}
    (hx : (19/10)*r < ‖x‖) (hx2 : ‖x‖ ≤ 2*r) (hp : 0 ≤ tfPotential ρ x) :
    initialBranch Z r a ρ x < 0 := by
  have hd : 0 < ‖x‖ := lt_trans (by positivity) hx
  have hv : Z/‖x‖ ≤ (10/19)*(Z/r) := by
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hx.le (show 0 ≤ (10/19)*(Z/r) by positivity)
    have he : (10/19)*(Z/r)*((19/10)*r) = Z := by field_simp
    nlinarith
  have hq := initial_quadratic_bound hr ha hs (norm_nonneg x) hx2
  have he : Z/(20*r) = (1/20)*(Z/r) := by ring
  rw [he] at hq
  have hn : 0 < Z/r := by positivity
  simp only [initialBranch,initialOffset,nuclearField,mul_div_assoc]
  nlinarith

lemma initial_outer_upper {Z B r : ℝ} (hZ : 0 < Z) (hr : 0 < r) (hB : 0 ≤ B)
    (hsmall : B ≤ Z*r^3/10) {x : TFSpace} (hx : r ≤ ‖x‖) :
    outerBarrier B r x ≤ (1/10)*(Z/r) := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  apply (outerBarrier_bounds hB hr hx).2.trans
  calc
    _ ≤ B/r^4 := div_le_div_of_nonneg_left hB (pow_pos hr 4) (by gcongr)
    _ ≤ (Z*r^3/10)/r^4 := div_le_div_of_nonneg_right hsmall (by positivity)
    _ = _ := by field_simp

lemma initial_lower_overlap {Z B r a : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hsmall : B ≤ Z*r^3/10)
    {ρ : TFSpace → ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) (hx1 : ‖x‖ ≤ (53/50)*r)
    (hp : tfPotential ρ x ≤ Z/(10*r)) :
    outerBarrier B r x < initialBranch Z r a ρ x := by
  have hu := initial_outer_upper hZ hr hB hsmall hx
  have hl := initial_branch_lower hZ hr ha hx hx1 hp
  have hn : 0 < Z/r := by positivity
  linarith

lemma initial_branch_cap {Z C r a : ℝ} (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a)
    (hs : 4*a*r^2 ≤ Z/(20*r)) (hC : 32*Z*r^3 ≤ C)
    {ρ : TFSpace → ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) (hx2 : ‖x‖ ≤ 2*r)
    (hp : 0 ≤ tfPotential ρ x) :
    initialBranch Z r a ρ x ≤ C/‖x‖^4 := by
  apply (initial_branch_upper hZ hr ha hs hx hx2 hp).trans
  have hd : 0 < ‖x‖ := hr.trans_le hx
  apply (le_div_iff₀ (pow_pos hd 4)).mpr
  calc
    _ ≤ (2*(Z/r))*(2*r)^4 := by gcongr
    _ = 32*Z*r^3 := by field_simp; ring
    _ ≤ C := hC

end Work_BarrierInitialBounds_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped ContDiff Topology

open CoulombAnalysis

lemma truncated_density_exterior {ρ : TFSpace → ℝ} {r : ℝ}
    (hs : Function.support ρ ⊆ ball 0 r) {x : TFSpace} (hx : r ≤ ‖x‖) : ρ x = 0 := by
  by_contra hn
  have hh := hs hn
  have hh' : ‖x‖ < r := mem_ball_zero_iff.mp hh
  linarith

lemma initialBranch_weak_reaction {Z r a k : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (ha : 0 ≤ a) (hk : 0 ≤ k) (hsmall : 4*a*r^2 ≤ Z/(20*r))
    (hreact : reaction k (2*(Z/r)) ≤ 6*a)
    {ρ : TFSpace → ℝ} {M : ℝ} (hm : Measurable ρ) (hn : ∀ x, 0 ≤ ρ x)
    (hb : ∀ x, ρ x ≤ M) (hs : Function.support ρ ⊆ ball 0 r) :
    WeakNuclearLowerOn {x : TFSpace | ‖x‖ < 2*r} Z (initialBranch Z r a ρ)
      (fun x => 4*Real.pi*ρ x+outerCoefficient r x*reaction k (initialBranch Z r a ρ x)) := by
  have hl : LocallyIntegrable (fun x => 4*Real.pi*ρ x) :=
    ((bounded_support_integrable hm hn hb hs).const_mul (4*Real.pi)).locallyIntegrable
  have hli := nuclear_source_locallyIntegrable Z k hr hl (outerCoefficient_measurable r)
    (outerCoefficient_bound r) (outerCoefficient_zero r) (initialOffset_continuous hm hn hb hs Z r a)
  apply ((initialBranch_weak_nuclear hm hn hb hs Z r a).mono_set (subset_univ _)).source_mono
    (hl.add (locallyIntegrable_const (6*a))) hli
  intro x hx
  by_cases hx' : r ≤ ‖x‖
  · simp only [outerCoefficient,ite_eq_left hx',one_mul]
    have hh := initial_branch_upper hZ hr ha hsmall hx' hx.le
      (tfPotential_nonneg (ae_of_all _ hn) x)
    have hf := (reaction_monotone hk hh).trans hreact
    change reaction k (nuclearField Z x+initialOffset Z r a ρ x) ≤ 6*a at hf
    linarith
  · simp only [outerCoefficient,ite_eq_right hx',zero_mul,add_zero]
    linarith

lemma outerOffset_weak_initial_source {Z B r k : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hk : 0 ≤ k) (hsmall : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {ρ : TFSpace → ℝ} (hs : Function.support ρ ⊆ ball 0 r) :
    WeakNuclearLowerOn {x : TFSpace | r < ‖x‖} Z
      (fun x => nuclearField Z x+outerOffset Z B r x)
      (fun x => 4*Real.pi*ρ x+outerCoefficient r x*reaction k (nuclearField Z x+outerOffset Z B r x)) := by
  apply (outerOffset_weak_nuclear hB hr hk hsmall Z).congr_source
  intro x hx
  change r < ‖x‖ at hx
  simp only [truncated_density_exterior hs hx.le,outerCoefficient,ite_eq_left hx.le,
    mul_zero,zero_add,one_mul]

theorem initialized_barrier_weak {Z B r a k : ℝ} (hZ : 0 < Z) (hB : 0 < B)
    (hr : 0 < r) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hquad : 4*a*r^2 ≤ Z/(20*r)) (hreact : reaction k (2*(Z/r)) ≤ 6*a)
    (hBsmall : B ≤ Z*r^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {ρ : TFSpace → ℝ} {M : ℝ} (hm : Measurable ρ) (hn : ∀ x, 0 ≤ ρ x)
    (hb : ∀ x, ρ x ≤ M) (hs : Function.support ρ ⊆ ball 0 r)
    (hgood : ∀ x, r ≤ ‖x‖ → ‖x‖ ≤ (53/50)*r → tfPotential ρ x ≤ Z/(10*r)) :
    Continuous (initializedOffset Z B r a ρ) ∧
    WeakNuclearLowerOn univ Z (initializedBarrier Z B r a ρ)
      (fun x => 4*Real.pi*ρ x+outerCoefficient r x*reaction k (initializedBarrier Z B r a ρ x)) := by
  have ht : r < (53/50)*r := by linarith
  have htL : (53/50)*r < (19/10)*r := by linarith
  have hLR : (19/10)*r < 2*r := by linarith
  have hlo : ∀ x : TFSpace, r ≤ ‖x‖ → ‖x‖ < (53/50)*r →
      outerOffset Z B r x ≤ initialOffset Z r a ρ x := by
    intro x hx hx'
    have hh := initial_lower_overlap hZ hr ha hB.le hBsmall hx hx'.le (hgood x hx hx'.le)
    rw [← nuclear_outerOffset_eq (Z := Z) hx] at hh
    change nuclearField Z x+outerOffset Z B r x < nuclearField Z x+initialOffset Z r a ρ x at hh
    linarith
  have hhi : ∀ x : TFSpace, (19/10)*r < ‖x‖ → ‖x‖ < 2*r →
      initialOffset Z r a ρ x ≤ outerOffset Z B r x := by
    intro x hx hx'
    have hx0 : r ≤ ‖x‖ := by linarith
    have hh := initial_branch_negative hZ hr ha hquad hx hx'.le (tfPotential_nonneg (ae_of_all _ hn) x)
    have ho := (outerBarrier_bounds hB.le hr hx0).1
    have hp : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
    rw [← nuclear_outerOffset_eq (Z := Z) hx0] at ho
    change nuclearField Z x+initialOffset Z r a ρ x < 0 at hh
    linarith
  have hu := initialOffset_continuous hm hn hb hs Z r a
  have hv := outerOffset_continuous Z B hr
  refine ⟨cutMaximum_continuous ht htL hLR hlo hhi hu hv,?_⟩
  have hwi := initialBranch_weak_reaction hZ hr ha hk hquad hreact hm hn hb hs
  have hwo := outerOffset_weak_initial_source (Z := Z) hB hr hk hsub hs
  apply cutMaximum_weak_nuclear ht htL hLR hlo hhi Z k hr hu hv
    (((bounded_support_integrable hm hn hb hs).const_mul (4*Real.pi)).locallyIntegrable)
    (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r)
  · exact hwi.mono_set (fun x hx => (show ‖x‖ < (53/50)*r from hx).trans (htL.trans hLR))
  · exact hwi.mono_set (fun _ hx => hx.2)
  · exact hwo.mono_set (fun _ hx => hx.1)
  · exact hwo.mono_set (fun x hx => (ht.trans htL).trans hx)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_BarrierInitialDeterministicBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma potential_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ)) :
    Measurable (fun p : Ω × TFSpace => tfPotential (ρ p.1) p.2) := by
  have h : Measurable (fun p : (Ω × TFSpace) × TFSpace => ρ p.1.1 p.2/‖p.1.2-p.2‖) :=
    (hm.comp (measurable_fst.fst.prodMk measurable_snd)).div
      (measurable_fst.snd.sub measurable_snd).norm
  exact h.stronglyMeasurable.integral_prod_right.measurable

lemma cutMaximum_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {u v : Ω → TFSpace → ℝ} (hu : Measurable (Function.uncurry u))
    (hv : Measurable (Function.uncurry v)) (r R : ℝ) :
    Measurable (fun p : Ω × TFSpace => cutMaximum r R (u p.1) (v p.1) p.2) :=
  Measurable.ite (measurableSet_lt measurable_snd.norm measurable_const) hu
    (Measurable.ite (measurableSet_lt measurable_snd.norm measurable_const) (hu.max hv) hv)

lemma initializedOffset_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ))
    (Z B a : ℝ) {r : ℝ} (hr : 0 < r) :
    Measurable (fun p : Ω × TFSpace => initializedOffset Z B r a (ρ p.1) p.2) := by
  exact cutMaximum_joint_measurable (u := fun sample => initialOffset Z r a (ρ sample))
    (v := fun _ => outerOffset Z B r)
    (((potential_joint_measurable hm).neg.sub measurable_const).add
      (measurable_const.mul (measurable_snd.norm.pow_const 2)))
    ((outerOffset_continuous Z B hr).measurable.comp measurable_snd) r (2*r)

lemma bounded_potential_deterministicBound {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) {M r : ℝ} (hM : 0 ≤ M)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 r) :
    DeterministicLocalBound (fun sample => tfPotential (ρ sample)) := by
  intro K hK
  obtain ⟨S,hS,hKS⟩ := hK.isBounded.exists_pos_norm_lt
  let T := max r S
  have hT : 0 < T := hS.trans_le (le_max_right _ _)
  refine ⟨8*Real.pi*M*T^2,fun sample x hx => ?_⟩
  rw [Real.norm_of_nonneg (tfPotential_nonneg (ae_of_all _ (hn sample)) x)]
  exact bounded_density_potential_le (hm sample) hM hT (hn sample) (hb sample)
    ((hs sample).trans (ball_subset_ball (le_max_left _ _))) x
    ((hKS x hx).le.trans (le_max_right _ _))

lemma DeterministicLocalBound.neg {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) : DeterministicLocalBound (fun sample x => -u sample x) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  exact ⟨C,fun sample x hx => by simpa only [norm_neg] using hC sample x hx⟩

lemma continuous_deterministicBound {Ω : Type*} {u : TFSpace → ℝ}
    (hu : Continuous u) : DeterministicLocalBound (fun _ : Ω => u) := by
  intro K hK
  obtain ⟨C,_,hC⟩ := (hK.image hu).isBounded.exists_pos_norm_lt
  exact ⟨C,fun _ x hx => (hC (u x) (mem_image_of_mem u hx)).le⟩

lemma cutMaximum_deterministicBound {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v) (r R : ℝ) :
    DeterministicLocalBound (fun sample => cutMaximum r R (u sample) (v sample)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,hD⟩ := hv K hK
  refine ⟨max C D,fun sample x hx => ?_⟩
  have hu' := (hC sample x hx).trans (le_max_left C D)
  have hv' := (hD sample x hx).trans (le_max_right C D)
  change ‖if ‖x‖ < r then u sample x else if ‖x‖ < R then max (u sample x) (v sample x) else v sample x‖ ≤ _
  split_ifs
  · exact hu'
  · rcases le_total (u sample x) (v sample x) with hh|hh
    · simpa only [max_eq_right hh] using hv'
    · simpa only [max_eq_left hh] using hu'
  · exact hv'

lemma initializedOffset_deterministicBound {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 r) (Z B a : ℝ) :
    DeterministicLocalBound (fun sample => initializedOffset Z B r a (ρ sample)) := by
  have hp := (bounded_potential_deterministicBound hm hM hn hb hs).neg
  have hc : Continuous (fun x : TFSpace => -(7/10)*Z/r+a*‖x‖^2) :=
    continuous_const.add (continuous_const.mul (continuous_norm.pow 2))
  have hi := hp.add (continuous_deterministicBound (Ω := Ω) hc)
  have he : (fun sample x => -tfPotential (ρ sample) x+(-(7/10)*Z/r+a*‖x‖^2)) =
      (fun sample => initialOffset Z r a (ρ sample)) := by
    funext sample x
    dsimp [initialOffset]
    ring
  rw [he] at hi
  exact cutMaximum_deterministicBound hi (continuous_deterministicBound (outerOffset_continuous Z B hr)) r (2*r)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorMomentBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma bounded_integrable_square {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable (fun x => (f x)^2) P := by
  apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C^2)
  exact ae_of_all _ fun x => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2

lemma square_integral_le_of_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : (∫ x, f x ∂P)^2 ≤ ∫ x, (f x)^2 ∂P := by
  have hi : Integrable f P := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  exact (Even.convexOn_pow (by decide : Even (2:ℕ))).map_integral_le (continuous_pow 2).continuousOn isClosed_univ
    (ae_of_all _ fun _ => mem_univ _) hi (bounded_integrable_square hf hC)

lemma bounded_original_posterior_mean {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ)
    {f : Configuration N → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ z, (∫ x, f x ∂originalRawKernel μ ell j (originalDatum ell j z))
      ∂physicalObservationLaw μ K) = ∫ x, f x ∂μ := by
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hm : StronglyMeasurable (fun d => ∫ x, f x ∂originalRawKernel μ ell j d) :=
    hf.stronglyMeasurable.integral_kernel
  rw [←integral_map (originalDatum_measurable ell j).aemeasurable hm.aestronglyMeasurable]
  have hh : Integrable f (originalRawKernel μ ell j ∘ₘ
      (physicalObservationLaw μ K).map (originalDatum ell j)) := by
    rwa [originalRawKernel_comp]
  conv_rhs => rw [←originalRawKernel_comp μ ell j]
  rw [Measure.comp_eq_comp_const_apply] at hh ⊢
  simpa only [Kernel.const_apply] using (Kernel.integral_comp hh).symm

theorem original_posterior_square_le {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ)
    {f : Configuration N → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ z, (∫ x, f x ∂originalRawKernel μ ell j (originalDatum ell j z))^2
      ∂physicalObservationLaw μ K) ≤ ∫ x, (f x)^2 ∂μ := by
  have hm : Measurable (fun z => ∫ x, f x ∂originalRawKernel μ ell j (originalDatum ell j z)) :=
    hf.stronglyMeasurable.integral_kernel.measurable.comp (originalDatum_measurable ell j)
  have hb (z) : ‖∫ x, f x ∂originalRawKernel μ ell j (originalDatum ell j z)‖ ≤ C := by
    calc
      _ ≤ ∫ _ : Configuration N, C ∂originalRawKernel μ ell j (originalDatum ell j z) :=
        norm_integral_le_of_norm_le (integrable_const C) (ae_of_all _ hC)
      _ = C := by simp
  have hsq (x) : ‖(f x)^2‖ ≤ C^2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hC x) _
  have hm2 : Measurable (fun z => ∫ x, (f x)^2 ∂originalRawKernel μ ell j (originalDatum ell j z)) :=
    (hf.pow_const 2).stronglyMeasurable.integral_kernel.measurable.comp (originalDatum_measurable ell j)
  have hb2 (z) : ‖∫ x, (f x)^2 ∂originalRawKernel μ ell j (originalDatum ell j z)‖ ≤ C^2 := by
    calc
      _ ≤ ∫ _ : Configuration N, C^2 ∂originalRawKernel μ ell j (originalDatum ell j z) :=
        norm_integral_le_of_norm_le (integrable_const _) (ae_of_all _ hsq)
      _ = C^2 := by simp
  calc
    _ ≤ ∫ z, (∫ x, (f x)^2 ∂originalRawKernel μ ell j (originalDatum ell j z))
        ∂physicalObservationLaw μ K :=
      integral_mono (bounded_integrable_square hm hb)
        (Integrable.of_bound hm2.aestronglyMeasurable _ (ae_of_all _ hb2))
        (fun _ => square_integral_le_of_bound hf hC)
    _ = _ := bounded_original_posterior_mean μ ell j (hf.pow_const 2) hsq

theorem original_master_second_moment_from_count {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ}
    (hg : Continuous g) (y : Space) {R A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ x, masterKernel c₁ r₀ s g x y ≤ A)
    (hsupport : Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆ ball y R) :
    (∫ z, (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y)^2
      ∂physicalObservationLaw μ K) ≤ A^2*(∫ x, (rawBallCount y R x)^2 ∂μ) := by
  let f : Configuration N → ℝ := fun x => ∑ i, masterKernel c₁ r₀ s g (x i) y
  have hm : Measurable f := Finset.measurable_sum _ (fun i _ =>
    ((masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun x : Configuration N => (x i,y))
      ((measurable_pi_apply i).prodMk measurable_const)))
  have hn (x) : 0 ≤ f x := Finset.sum_nonneg fun i _ => masterKernel_nonneg _ _ _ _ _ _
  have hb (x) : f x ≤ A*rawBallCount y R x := by
    rw [rawBallCount,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · simpa only [mul_one] using hbound (x i)
    · have hz : masterKernel c₁ r₀ s g (x i) y = 0 := by
        by_contra hh
        have hmem := hsupport hh
        simp only [mem_ball,dist_eq_norm] at hmem
        exact h hmem
      simp only [hz,mul_zero,le_refl]
  have hfb (x) : ‖f x‖ ≤ A*N := by
    rw [Real.norm_of_nonneg (hn x)]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (rawBallCount_le y R x) hA)
  have hci : Integrable (fun x => (rawBallCount y R x)^2) μ :=
    bounded_integrable_square (rawBallCount_measurable y R) (fun x => by
      rw [Real.norm_of_nonneg (rawBallCount_nonneg y R x)]; exact rawBallCount_le y R x)
  calc
    _ ≤ ∫ x, (f x)^2 ∂μ := by
      unfold jointMasterPosterior
      exact original_posterior_square_le μ ell j hm hfb
    _ ≤ ∫ x, A^2*(rawBallCount y R x)^2 ∂μ := by
      apply integral_mono (bounded_integrable_square hm hfb) (hci.const_mul _)
      intro x
      simpa only [mul_pow] using pow_le_pow_left₀ (hn x) (hb x) 2
    _ = _ := integral_const_mul _ _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialLipschitzBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialLipschitz_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis

lemma locallyLipschitz_comp_contDiffAt {E : Type*} [PseudoMetricSpace E]
    {g : E → ℝ} (hg : LocallyLipschitz g) {f : ℝ → ℝ}
    (hf : ∀ x, ContDiffAt ℝ 1 f (g x)) : LocallyLipschitz (f ∘ g) := by
  intro x
  obtain ⟨Kg,t,ht,hgL⟩ := hg x
  obtain ⟨Kf,u,hu,hfL⟩ := (hf x).exists_lipschitzOnWith
  exact ⟨Kf*Kg,t ∩ g ⁻¹' u,inter_mem ht (hg.continuous.continuousAt hu),
    hfL.comp (hgL.mono inter_subset_left) ((mapsTo_preimage g u).mono_left inter_subset_right)⟩

lemma outerOffset_locallyLipschitz (Z B : ℝ) {r : ℝ} (hr : 0 < r) :
    LocallyLipschitz (outerOffset Z B r) := by
  let f : ℝ → ℝ := fun t => B/t^4*(1-r/(8*t))-Z/t
  have hm : LocallyLipschitz (fun x : TFSpace => max r ‖x‖) :=
    lipschitzWith_one_norm.locallyLipschitz.const_max r
  apply locallyLipschitz_comp_contDiffAt hm (f := f)
  intro x
  have hp : 0 < max r ‖x‖ := hr.trans_le (le_max_left _ _)
  dsimp [f]
  fun_prop (disch := positivity)

end Work_BarrierInitialLipschitz_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma deterministicLip_spatial {Ω : Type*} {u : TFSpace → ℝ} (h : LocallyLipschitz u) :
    DeterministicLocalLipschitz (fun _ : Ω => u) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,fun _ => hL⟩

lemma DeterministicLocalLipschitz.neg {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (h : DeterministicLocalLipschitz u) : DeterministicLocalLipschitz (fun sample x => -u sample x) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,fun sample => (hL sample).neg⟩

lemma DeterministicLocalLipschitz.add {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => u sample x+v sample x) := by
  intro x
  obtain ⟨Ku,t,ht,hLu⟩ := hu x
  obtain ⟨Kv,s,hs,hLv⟩ := hv x
  refine ⟨Ku+Kv,t ∩ s,inter_mem ht hs,fun sample => ?_⟩
  exact ((hLu sample).mono inter_subset_left).add ((hLv sample).mono inter_subset_right)

lemma DeterministicLocalLipschitz.sub {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => u sample x-v sample x) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

lemma DeterministicLocalLipschitz.max {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => max (u sample x) (v sample x)) := by
  intro x
  obtain ⟨Ku,t,ht,hLu⟩ := hu x
  obtain ⟨Kv,s,hs,hLv⟩ := hv x
  refine ⟨Max.max Ku Kv,t ∩ s,inter_mem ht hs,fun sample => ?_⟩
  exact lipschitzOnWith_iff_restrict.mpr
    (((hLu sample).mono inter_subset_left).to_restrict.max ((hLv sample).mono inter_subset_right).to_restrict)

lemma deterministicLip_local_congr {Ω : Type*} {u v : Ω → TFSpace → ℝ} {x : TFSpace}
    (hu : ∃ K : NNReal, ∃ t ∈ 𝓝 x, ∀ sample, LipschitzOnWith K (u sample) t)
    (he : ∀ᶠ y in 𝓝 x, ∀ sample, u sample y = v sample y) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 x, ∀ sample, LipschitzOnWith K (v sample) t := by
  obtain ⟨K,t,ht,hL⟩ := hu
  refine ⟨K,t ∩ {y | ∀ sample, u sample y = v sample y},inter_mem ht he,fun sample y hy z hz => ?_⟩
  change edist (v sample y) (v sample z) ≤ _
  rw [←hy.2 sample,←hz.2 sample]
  exact hL sample hy.1 hz.1

lemma cutMaximum_deterministicLip {Ω : Type*} {u v : Ω → TFSpace → ℝ} {r t L R : ℝ}
    (hrt : r < t) (htL : t < L) (hLR : L < R)
    (hlo : ∀ sample x, r ≤ ‖x‖ → ‖x‖ < t → v sample x ≤ u sample x)
    (hhi : ∀ sample x, L < ‖x‖ → ‖x‖ < R → u sample x ≤ v sample x)
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample => cutMaximum r R (u sample) (v sample)) := by
  intro x
  by_cases hx : ‖x‖ < t
  · apply deterministicLip_local_congr (hu x)
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact fun sample => (cutMaximum_inner htL hLR (hlo sample) hy).symm
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      apply deterministicLip_local_congr (hu.max hv x)
      filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hx',hR⟩] with y hy
      exact fun sample => (cutMaximum_middle hy.1 hy.2).symm
    · have hL : L < ‖x‖ := hLR.trans_le (le_of_not_gt hR)
      apply deterministicLip_local_congr (hv x)
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hL] with y hy
      exact fun sample => (cutMaximum_outer hrt htL (hhi sample) hy).symm

lemma bounded_density_potential_deterministicLip {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) {M r : ℝ} (hM : 0 ≤ M)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 r) :
    DeterministicLocalLipschitz (fun sample => tfPotential (ρ sample)) := by
  intro x
  let S := max r (‖x‖+1)
  have hS : 0 < S := (by positivity : (0:ℝ) < ‖x‖+1).trans_le (le_max_right _ _)
  have hxS : ‖x‖ < S := (by linarith : ‖x‖ < ‖x‖+1).trans_le (le_max_right _ _)
  let K : NNReal := ⟨8*Real.pi*M*S,by positivity⟩
  refine ⟨K,ball 0 S,isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxS),fun sample => ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  rw [Real.dist_eq,dist_eq_norm]
  change |tfPotential (ρ sample) y-tfPotential (ρ sample) z| ≤ (8*Real.pi*M*S)*‖y-z‖
  exact bounded_density_potential_difference (hm sample) hM hS (hn sample) (hb sample)
    ((hs sample).trans (ball_subset_ball (le_max_left _ _))) y z
    (mem_ball_zero_iff.mp hy).le (mem_ball_zero_iff.mp hz).le

lemma initialOffset_deterministicLip {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) {M R : ℝ} (hM : 0 ≤ M)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 R) (Z r a : ℝ) :
    DeterministicLocalLipschitz (fun sample => initialOffset Z r a (ρ sample)) := by
  have hq : ContDiff ℝ 1 (fun x : TFSpace => a*‖x‖^2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  exact ((bounded_density_potential_deterministicLip hm hM hn hb hs).neg.sub
    (deterministicLip_spatial (LocallyLipschitz.const ((7/10)*Z/r)))).add
    (deterministicLip_spatial hq.locallyLipschitz)

lemma initializedOffset_deterministicLip {Ω : Type*} {Z B r a M : ℝ}
    (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hquad : 4*a*r^2 ≤ Z/(20*r)) (hBsmall : B ≤ Z*r^3/10)
    {ρ : Ω → TFSpace → ℝ} (hm : ∀ sample, Measurable (ρ sample))
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 r)
    (hgood : ∀ sample x, r ≤ ‖x‖ → ‖x‖ ≤ (53/50)*r → tfPotential (ρ sample) x ≤ Z/(10*r)) :
    DeterministicLocalLipschitz (fun sample => initializedOffset Z B r a (ρ sample)) := by
  apply cutMaximum_deterministicLip (t := (53/50)*r) (L := (19/10)*r)
    (by linarith) (by linarith) (by linarith) _ _
    (initialOffset_deterministicLip hm hM hn hb hs Z r a)
    (deterministicLip_spatial (outerOffset_locallyLipschitz Z B hr))
  · intro sample x hx hx'
    have hh := initial_lower_overlap hZ hr ha hB hBsmall hx hx'.le (hgood sample x hx hx'.le)
    rw [←nuclear_outerOffset_eq (Z := Z) hx] at hh
    change nuclearField Z x+outerOffset Z B r x < nuclearField Z x+initialOffset Z r a (ρ sample) x at hh
    linarith
  · intro sample x hx hx'
    have hx0 : r ≤ ‖x‖ := by linarith
    have hh := initial_branch_negative hZ hr ha hquad hx hx'.le
      (tfPotential_nonneg (ae_of_all _ (hn sample)) x)
    have ho := (outerBarrier_bounds hB hr hx0).1
    have hp : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
    rw [←nuclear_outerOffset_eq (Z := Z) hx0] at ho
    change nuclearField Z x+initialOffset Z r a (ρ sample) x < 0 at hh
    linarith

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma compactBound_integrable_prod {p : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry p)) (hb : DeterministicLocalBound p)
    {R : ℝ} (hs : ∀ sample x, R < ‖x‖ → p sample x = 0) :
    Integrable (Function.uncurry p) (P.prod volume) := by
  obtain ⟨C,hC⟩ := hb (closedBall 0 R) (isCompact_closedBall 0 R)
  have hi : Integrable ((closedBall (0 : TFSpace) R).indicator (fun _ => C)) volume :=
    (integrableOn_const (C := C) (isCompact_closedBall (0 : TFSpace) R).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  apply (hi.comp_snd P).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z.2 ∈ closedBall (0 : TFSpace) R
    · rw [indicator_of_mem hz]
      exact hC z.1 z.2 hz
    · rw [indicator_of_notMem hz,Function.uncurry_apply_pair,
        hs z.1 z.2 (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hz)),norm_zero]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialCapsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set MeasureTheory

namespace CoulombBarrier
open CoulombAnalysis

lemma initializedBarrier_exterior {Z B r a : ℝ} {ρ : TFSpace → ℝ} {x : TFSpace}
    (hx : r ≤ ‖x‖) :
    initializedBarrier Z B r a ρ x =
      if ‖x‖ < 2*r then max (initialBranch Z r a ρ x) (outerBarrier B r x)
      else outerBarrier B r x := by
  unfold initializedBarrier initializedOffset cutMaximum
  rw [ite_eq_right (not_lt.mpr hx)]
  split_ifs
  · rw [add_max,nuclear_outerOffset_eq hx]
    rfl
  · exact nuclear_outerOffset_eq hx

lemma initializedBarrier_lower {Z B r a : ℝ} {ρ : TFSpace → ℝ} {x : TFSpace}
    (hx : r ≤ ‖x‖) : outerBarrier B r x ≤ initializedBarrier Z B r a ρ x := by
  rw [initializedBarrier_exterior hx]
  split_ifs
  · exact le_max_right _ _
  · exact le_refl _

lemma initializedBarrier_cap {Z B C r a : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hquad : 4*a*r^2 ≤ Z/(20*r))
    (hCB : B ≤ C) (hCZ : 32*Z*r^3 ≤ C) {ρ : TFSpace → ℝ}
    (hn : ∀ x, 0 ≤ ρ x) {x : TFSpace} (hx : r ≤ ‖x‖) :
    initializedBarrier Z B r a ρ x ≤ C/‖x‖^4 := by
  rw [initializedBarrier_exterior hx]
  have hb : outerBarrier B r x ≤ C/‖x‖^4 :=
    (outerBarrier_bounds hB hr hx).2.trans (div_le_div_of_nonneg_right hCB (by positivity))
  split_ifs with h2
  · exact max_le (initial_branch_cap hZ hr ha hquad hCZ hx h2.le
      (tfPotential_nonneg (ae_of_all _ hn) x)) hb
  · exact hb

lemma initializedBarrier_tail {Z B r a : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hquad : 4*a*r^2 ≤ Z/(20*r))
    {ρ : TFSpace → ℝ} (hn : ∀ x, 0 ≤ ρ x) {x : TFSpace}
    (hx : (19/10)*r < ‖x‖) : initializedBarrier Z B r a ρ x = outerBarrier B r x := by
  have hx0 : r ≤ ‖x‖ := by linarith
  rw [initializedBarrier_exterior hx0]
  split_ifs with h2
  · have hv := initial_branch_negative hZ hr ha hquad hx h2.le (tfPotential_nonneg (ae_of_all _ hn) x)
    have hb := (outerBarrier_bounds hB hr hx0).1
    have hp : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
    exact max_eq_right (by linarith)
  · rfl

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitializationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis
attribute [local instance] Classical.propDecidable

variable {Ω : Type*}

lemma initialCharge_measurable [MeasurableSpace Ω] {A : Set Ω} (hA : MeasurableSet A) (r : ℝ)
    {μ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry μ)) :
    Measurable (Function.uncurry (initialCharge A r μ)) := by
  exact Measurable.ite (hA.preimage measurable_fst)
    (hm.indicator (measurableSet_ball.preimage measurable_snd)) measurable_const

lemma initialCharge_nonneg {A : Set Ω} {r : ℝ} {μ : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ μ sample x) (sample : Ω) (x : TFSpace) : 0 ≤ initialCharge A r μ sample x := by
  unfold initialCharge
  split_ifs
  · exact indicator_nonneg (fun x _ => hn sample x) x
  · exact le_refl _

lemma initialCharge_le {A : Set Ω} {r : ℝ} {μ : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ μ sample x) (sample : Ω) (x : TFSpace) : initialCharge A r μ sample x ≤ μ sample x := by
  unfold initialCharge
  split_ifs
  · by_cases hx : x ∈ ball (0 : TFSpace) r
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]; exact hn sample x
  · exact hn sample x

lemma initialCharge_support (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) (sample : Ω) :
    Function.support (initialCharge A r μ sample) ⊆ ball 0 r := by
  intro x hx
  by_contra h
  simp only [Function.mem_support,initialCharge,indicator_of_notMem h] at hx
  split_ifs at hx <;> exact hx rfl

lemma initialCharge_bound {A : Set Ω} {r M : ℝ} {μ : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ μ sample x) (hb : ∀ sample x, μ sample x ≤ M) (sample : Ω) (x : TFSpace) :
    initialCharge A r μ sample x ≤ M := (initialCharge_le hn sample x).trans (hb sample x)

lemma initialCharge_deterministicBound {A : Set Ω} {r M : ℝ} {μ : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ μ sample x) (hb : ∀ sample x, μ sample x ≤ M) :
    DeterministicLocalBound (initialCharge A r μ) := by
  intro K _
  refine ⟨M,fun sample x _ => ?_⟩
  rw [Real.norm_of_nonneg (initialCharge_nonneg hn sample x)]
  exact initialCharge_bound hn hb sample x

lemma initialCharge_source (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) (sample : Ω) (x : TFSpace) :
    4*Real.pi*initialCharge A r μ sample x = innerSource r (μ sample) (initialError A r μ sample) x := by
  simp only [innerSource,initialError,initialCharge,mem_compl_iff,mem_ball_zero_iff,
    indicator_apply]
  split_ifs <;> ring

lemma initialCharge_of_mem {A : Set Ω} {sample : Ω} (h : sample ∈ A) (r : ℝ) (μ : Ω → TFSpace → ℝ) :
    initialCharge A r μ sample = (ball (0 : TFSpace) r).indicator (μ sample) := by
  funext x
  exact ite_eq_left h

lemma initialCharge_of_notMem {A : Set Ω} {sample : Ω} (h : sample ∉ A) (r : ℝ) (μ : Ω → TFSpace → ℝ) :
    initialCharge A r μ sample = fun _ => 0 := by
  funext x
  exact ite_eq_right h

lemma initialCharge_potential (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) (sample : Ω) (x : TFSpace) :
    tfPotential (initialCharge A r μ sample) x = if sample ∈ A then innerPotential r (μ sample) x else 0 := by
  by_cases h : sample ∈ A
  · rw [initialCharge_of_mem h,ite_eq_left h,innerPotential_eq_tfPotential]
  · rw [initialCharge_of_notMem h,ite_eq_right h]; simp only [tfPotential,zero_div,integral_zero]

lemma initialCharge_good {A : Set Ω} {Z r : ℝ} {μ : Ω → TFSpace → ℝ}
    (hZ : 0 ≤ Z) (hr : 0 ≤ r)
    (hgood : ∀ sample ∈ A, ∀ x : TFSpace, ‖x‖ ≤ (11/10)*r → innerPotential r (μ sample) x ≤ Z/(10*r))
    (sample : Ω) (x : TFSpace) (_hx : r ≤ ‖x‖) (hx' : ‖x‖ ≤ (53/50)*r) :
    tfPotential (initialCharge A r μ sample) x ≤ Z/(10*r) := by
  rw [initialCharge_potential]
  split_ifs with hh
  · exact hgood sample hh x (by linarith)
  · positivity

theorem initialError_expected_mass [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) {r M n : ℝ} {μ : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry μ)) (hn : ∀ sample x, 0 ≤ μ sample x)
    (hb : ∀ sample x, μ sample x ≤ M) (hi : ∀ sample, Integrable (μ sample))
    (hcount : ∀ sample, ∫ x, μ sample x ≤ n) :
    (∫ sample, (∫ x, initialError A r μ sample x) ∂P) ≤ n*P.real Aᶜ := by
  have hp := initialCharge_measurable hA.compl r hm
  have hb' := initialCharge_deterministicBound (A := Aᶜ) (r := r) hn hb
  have hs : ∀ sample x, r < ‖x‖ → initialCharge Aᶜ r μ sample x = 0 := by
    intro sample x hx
    exact truncated_density_exterior (initialCharge_support Aᶜ r μ sample) hx.le
  have hie := compactBound_integrable_prod (P := P) hp hb' hs
  have hconst : Integrable (Aᶜ.indicator (fun _ : Ω => n)) P :=
    (integrable_const n).indicator hA.compl
  have hle : ∀ sample, (∫ x, initialError A r μ sample x) ≤ Aᶜ.indicator (fun _ => n) sample := by
    intro sample
    by_cases hω : sample ∈ Aᶜ
    · rw [indicator_of_mem hω]
      apply le_trans _ (hcount sample)
      have hii : Integrable (initialError A r μ sample) :=
        bounded_support_integrable (hp.comp (measurable_const.prodMk measurable_id))
          (initialCharge_nonneg hn sample) (initialCharge_bound hn hb sample) (initialCharge_support Aᶜ r μ sample)
      exact integral_mono hii (hi sample) (initialCharge_le hn sample)
    · simp only [initialError,initialCharge,ite_eq_right hω,integral_zero,indicator_of_notMem hω,le_refl]
  calc
    _ ≤ ∫ sample, Aᶜ.indicator (fun _ : Ω => n) sample ∂P :=
      integral_mono hie.integral_prod_left hconst hle
    _ = n*P.real Aᶜ := by rw [integral_indicator hA.compl]; simp [mul_comm]

theorem initial_barrier_with_error {A : Set Ω} {Z B r a k M : ℝ}
    (hZ : 0 < Z) (hB : 0 < B) (hr : 0 < r) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hquad : 4*a*r^2 ≤ Z/(20*r)) (hreact : reaction k (2*(Z/r)) ≤ 6*a)
    (hBsmall : B ≤ Z*r^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {μ : Ω → TFSpace → ℝ} (hm : ∀ sample, Measurable (μ sample))
    (hn : ∀ sample x, 0 ≤ μ sample x) (hb : ∀ sample x, μ sample x ≤ M)
    (hgood : ∀ sample ∈ A, ∀ x : TFSpace, ‖x‖ ≤ (11/10)*r → innerPotential r (μ sample) x ≤ Z/(10*r))
    (sample : Ω) :
    Continuous (initializedOffset Z B r a (initialCharge A r μ sample)) ∧
    WeakNuclearLowerOn univ Z (initializedBarrier Z B r a (initialCharge A r μ sample))
      (fun x => innerSource r (μ sample) (initialError A r μ sample) x+
        outerCoefficient r x*reaction k (initializedBarrier Z B r a (initialCharge A r μ sample) x)) := by
  have hm' : Measurable (initialCharge A r μ sample) := by
    by_cases hω : sample ∈ A
    · rw [initialCharge_of_mem hω]; exact (hm sample).indicator measurableSet_ball
    · rw [initialCharge_of_notMem hω]; exact measurable_const
  have hh := initialized_barrier_weak hZ hB hr ha hk hquad hreact hBsmall hsub hm'
    (initialCharge_nonneg hn sample) (initialCharge_bound hn hb sample)
    (initialCharge_support A r μ sample) (initialCharge_good hZ.le hr.le hgood sample)
  exact ⟨hh.1,hh.2.congr_source (fun x _ => by rw [initialCharge_source])⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepGeometryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma barrierGap_pos {B : ℝ} (hB : 0 < B) : 0 < barrierGap B := by
  unfold barrierGap
  positivity

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepWeakBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma initial_density_scale {Z r : ℝ} (hZ : 0 < Z) (hr : 0 < r) :
    ((Pauli.globalDensityConstant*(Z^(7/3:ℝ)+Z^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r)^(1/5:ℝ))*(r/Z) =
      initialDensityConstant*(Z*r^3)^(2/5:ℝ) := by
  have hp (a : ℝ) := Real.rpow_pos_of_pos hZ a
  rw [show Pauli.globalDensityConstant*(Z^(7/3:ℝ)+Z^(7/3:ℝ)) =
      (2*Pauli.globalDensityConstant)*Z^(7/3:ℝ) by ring,
    Real.mul_rpow (mul_nonneg (by norm_num) Pauli.globalDensityConstant_pos.le) (hp _).le, ←Real.rpow_mul hZ.le,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr.le,
    Real.mul_rpow hZ.le (pow_nonneg hr.le 3), ←Real.rpow_natCast, ←Real.rpow_mul hr.le]
  norm_num
  unfold initialDensityConstant
  have hZpow : Z^(7/5:ℝ)/Z = Z^(2/5:ℝ) := by
    calc
      _ = Z^(7/5:ℝ)/Z^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hZ]; norm_num
  have hrpow : r^(1/5:ℝ)*r = r^(6/5:ℝ) := by
    calc
      _ = r^(1/5:ℝ)*r^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hr]; norm_num
  calc
    _ = ((2*Pauli.globalDensityConstant)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*4^(1/5:ℝ))*
        (Z^(7/5:ℝ)/Z)*(r^(1/5:ℝ)*r) := by ring
    _ = _ := by rw [hZpow,hrpow]; ring

lemma initial_density_small_of_nuclear_relation {Z r ε : ℝ}
    (hZ : 0 < Z) (hr : 0 < r) (hε : 0 < ε) (hrel : Z*r^3 = ε^3)
    (hs : initialDensityConstant*ε^(6/5:ℝ) < 1/20) :
    (Pauli.globalDensityConstant*(Z^(7/3:ℝ)+Z^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r)^(1/5:ℝ) < Z/(20*r) := by
  have hh := initial_density_scale hZ hr
  rw [hrel,←Real.rpow_natCast,←Real.rpow_mul hε.le] at hh
  norm_num at hh
  apply (mul_lt_mul_iff_right₀ (div_pos hr hZ)).mp
  rw [mul_comm (r/Z), hh]
  have he : r/Z*(Z/(20*r)) = (1:ℝ)/20 := by field_simp
  rw [he]
  exact hs

lemma initial_event_cost_small :
    Tendsto (fun r : ℝ => r^(7-2.02:ℝ)*(Real.log (Real.exp 1/r^40))^5)
      (𝓝[>] 0) (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r^(249/250:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuousAt_rpow_const 0 (249/250:ℝ) (Or.inr (by norm_num))).tendsto.mono_left (show (𝓝[>] (0:ℝ)) ≤ 𝓝 (0:ℝ) from inf_le_left)
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ) < 249/250)
  have hh := (hpow.sub (hlog.const_mul 40)).pow 5
  simp only [mul_zero,sub_zero,zero_pow (by norm_num : (5:ℕ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.log_div (Real.exp_pos 1).ne' (pow_pos hr 40).ne',Real.log_exp,Real.log_pow]
  have he : r^(249/250:ℝ)-40*(Real.log r*r^(249/250:ℝ)) =
      r^(249/250:ℝ)*(1-40*Real.log r) := by ring
  rw [he,mul_pow,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  norm_num

lemma coarse_offset_nuclear_ratio {Z s : ℝ} (hZ : 0 < Z) (hs : 0 < s) :
    (3*Z*s^(-4:ℝ))/Z^(7/3:ℝ) = 3*(Z*s^3)^(-4/3:ℝ) := by
  rw [Real.mul_rpow hZ.le (pow_nonneg hs.le 3),←Real.rpow_natCast,←Real.rpow_mul hs.le]
  norm_num only [show (3:ℝ)*(-4/3) = -4 by norm_num]
  have he : Z/Z^(7/3:ℝ) = Z^(-4/3:ℝ) := by
    calc
      _ = Z^(1:ℝ)/Z^(7/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hZ]; norm_num
  calc
    _ = 3*(Z/Z^(7/3:ℝ))*s^(-4:ℝ) := by ring
    _ = _ := by rw [he]; ring_nf

theorem coarse_offset_nuclear_vanishes {ι : Type*} {l : Filter ι}
    {Z s : ι → ℝ} (hZ : ∀ᶠ i in l, 0 < Z i) (hs : ∀ᶠ i in l, 0 < s i)
    (hscale : Tendsto (fun i => Z i*(s i)^3) l atTop) :
    Tendsto (fun i => (3*Z i*(s i)^(-4:ℝ))/(Z i)^(7/3:ℝ)) l (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 4/3)).comp hscale
  have ht := hh.const_mul 3
  simp only [mul_zero] at ht
  exact ht.congr' (by filter_upwards [hZ,hs] with i hZi hsi; simpa only [Function.comp_apply,neg_div] using (coarse_offset_nuclear_ratio hZi hsi).symm)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierNuclearScaleBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierNuclearScale_barrier_scope

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombObservation

lemma nuclear_radius_relation {Z ε : ℝ} (hZ : 0 < Z) :
    Z*(ε*Z^(-1/3:ℝ))^3 = ε^3 := by
  rw [mul_pow,←Real.rpow_natCast (Z^(-1/3:ℝ)) 3,←Real.rpow_mul hZ.le]
  norm_num [Real.rpow_neg_one]
  field_simp

lemma nuclear_energy_relation {Z r ε : ℝ} (hZ : 0 < Z) (hr : 0 < r) (hε : 0 < ε)
    (hrel : Z*r^3 = ε^3) : Z^(7/3:ℝ)*r^7 = ε^7 := by
  have hh := congrArg (fun t : ℝ => t^(7/3:ℝ)) hrel
  rw [Real.mul_rpow hZ.le (pow_nonneg hr.le 3),←Real.rpow_natCast,
    ←Real.rpow_mul hr.le,←Real.rpow_natCast,←Real.rpow_mul hε.le] at hh
  norm_num at hh
  exact hh

lemma initial_event_ratio {Z r ε : ℝ} (hZ : 0 < Z) (hr : 0 < r) (hε : 0 < ε)
    (hrel : Z*r^3 = ε^3) :
    (r^(-2.02:ℝ)*(Real.log (Real.exp 1/r^40))^5)/Z^(7/3:ℝ) =
      (r^(7-2.02:ℝ)*(Real.log (Real.exp 1/r^40))^5)/ε^7 := by
  have hE := nuclear_energy_relation hZ hr hε hrel
  have he : r^(7-2.02:ℝ) = r^(-2.02:ℝ)*r^7 := by
    rw [←Real.rpow_natCast,←Real.rpow_add hr]; congr 1; norm_num
  rw [he,←hE]
  field_simp

lemma initial_event_ratio_vanishes {ι : Type*} {l : Filter ι} {Z r : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hZ : ∀ᶠ i in l, 0 < Z i) (hr : ∀ᶠ i in l, 0 < r i)
    (hrel : ∀ᶠ i in l, Z i*(r i)^3 = ε^3) (hr0 : Tendsto r l (𝓝 0)) :
    Tendsto (fun i => ((r i)^(-2.02:ℝ)*(Real.log (Real.exp 1/(r i)^40))^5)/(Z i)^(7/3:ℝ)) l (𝓝 0) := by
  have ht : Tendsto r l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hr0,hr⟩
  have hh := (initial_event_cost_small.comp ht).div_const (ε^7)
  simp only [zero_div] at hh
  exact hh.congr' (by filter_upwards [hZ,hr,hrel] with i hZi hri hli; exact (initial_event_ratio hZi hri hε hli).symm)

lemma nuclear_inverse_energy_vanishes {ι : Type*} {l : Filter ι} {Z r : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hZ : ∀ᶠ i in l, 0 < Z i) (hr : ∀ᶠ i in l, 0 < r i)
    (hrel : ∀ᶠ i in l, Z i*(r i)^3 = ε^3) (hr0 : Tendsto r l (𝓝 0)) :
    Tendsto (fun i => (Z i)^(-(7/3):ℝ)) l (𝓝 0) := by
  have hh := (hr0.pow 7).div_const (ε^7)
  simp only [zero_pow (by norm_num : (7:ℕ) ≠ 0),zero_div] at hh
  apply hh.congr'
  filter_upwards [hZ,hr,hrel] with i hZi hri hli
  rw [Real.rpow_neg hZi.le,←nuclear_energy_relation hZi hri hε hli]
  field_simp

theorem initial_budget_eventually {ι : Type*} {l : Filter ι} {Z s r : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hZ : ∀ᶠ i in l, 0 < Z i) (hs : ∀ᶠ i in l, 0 < s i)
    (hr : ∀ᶠ i in l, 0 < r i) (hrel : ∀ᶠ i in l, Z i*(r i)^3 = ε^3)
    (hr0 : Tendsto r l (𝓝 0)) (hscale : Tendsto (fun i => Z i*(s i)^3) l atTop)
    (δ : ℝ) :
    ∀ᶠ i in l, 3*Z i*(s i)^(-4:ℝ)+observationFisherConstant*(r i)^(-2.02:ℝ)*
      (Real.log (Real.exp 1/(r i)^40))^5+δ ≤ (Z i)^(7/3:ℝ) := by
  have h1 := coarse_offset_nuclear_vanishes hZ hs hscale
  have h2 := (initial_event_ratio_vanishes hε hZ hr hrel hr0).const_mul observationFisherConstant
  have h3 := (nuclear_inverse_energy_vanishes hε hZ hr hrel hr0).const_mul δ
  have ht := (h1.add h2).add h3
  simp only [mul_zero,add_zero] at ht
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [he,hZ] with i hi hZi
  have hden : 0 < (Z i)^(7/3:ℝ) := Real.rpow_pos_of_pos hZi _
  apply le_of_lt
  apply (div_lt_one hden).mp
  change (3*Z i*(s i)^(-4:ℝ))/(Z i)^(7/3:ℝ)+
    observationFisherConstant*((r i)^(-2.02:ℝ)*(Real.log (Real.exp 1/(r i)^40))^5/(Z i)^(7/3:ℝ))+
    δ*(Z i)^(-(7/3):ℝ) < 1 at hi
  rw [Real.rpow_neg hZi.le] at hi
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

lemma nuclear_radius_tendsto {ι : Type*} {l : Filter ι} {Z s : ι → ℝ}
    (hs0 : Tendsto s l (𝓝 0)) (hs : ∀ᶠ i in l, 0 < s i)
    (hscale : Tendsto (fun i => Z i*(s i)^3) l atTop) (ε : ℝ) :
    Tendsto (fun i => ε*(Z i)^(-1/3:ℝ)) l (𝓝 0) := by
  have hb : ∀ᶠ i in l, s i < 1 := hs0.eventually (Iio_mem_nhds (by norm_num))
  have hz : ∀ᶠ i in l, 0 < Z i := by
    filter_upwards [hscale.eventually (eventually_gt_atTop 0),hs] with i hi hsi
    exact (mul_pos_iff_of_pos_right (pow_pos hsi 3)).mp hi
  have hZtop : Tendsto Z l atTop := tendsto_atTop_mono' l (by
    filter_upwards [hb,hz,hs] with i hbi hzi hsi
    have hp : (s i)^3 ≤ 1 := pow_le_one₀ hsi.le hbi.le
    nlinarith) hscale
  simpa only [mul_zero,neg_div,Function.comp_def] using
    ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).comp hZtop).const_mul ε

end CoulombAtom

end Work_BarrierNuclearScale_barrier_scope

open Filter Set
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma initialQuadraticConstant_pos {k : ℝ} (hk : 0 ≤ k) : 0 < initialQuadraticConstant k := by
  unfold initialQuadraticConstant
  positivity

lemma initialQuadratic_reaction {k Z r : ℝ} (hZ : 0 < Z) (hr : 0 < r) :
    reaction k (2*(Z/r)) ≤ 6*initialQuadratic (initialQuadraticConstant k) Z r := by
  have hp : 0 ≤ Z/r := (div_pos hZ hr).le
  rw [reaction, max_eq_left (by positivity : 0 ≤ 2*(Z/r)),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hp]
  unfold initialQuadratic initialQuadraticConstant
  have hq := Real.rpow_nonneg hp (3/2:ℝ)
  nlinarith

lemma initialQuadratic_scale {Z r ε : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (hε : 0 < ε) (hrel : Z*r^3 = ε^3) :
    (Z/r)^(3/2:ℝ)*r^3 = Z*ε^(3/2:ℝ) := by
  have he : ε^(3/2:ℝ) = Z^(1/2:ℝ)*r^(3/2:ℝ) := by
    calc
      _ = (ε^3)^(1/2:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul hε.le]; norm_num
      _ = (Z*r^3)^(1/2:ℝ) := by rw [hrel]
      _ = _ := by rw [Real.mul_rpow hZ.le (pow_nonneg hr.le 3),←Real.rpow_natCast,
        ←Real.rpow_mul hr.le]; norm_num
  rw [he,Real.div_rpow hZ.le hr.le]
  have hZp : Z^(3/2:ℝ) = Z*Z^(1/2:ℝ) := by
    calc
      _ = Z^((1:ℝ)+(1/2:ℝ)) := by norm_num
      _ = Z^(1:ℝ)*Z^(1/2:ℝ) := Real.rpow_add hZ 1 (1/2)
      _ = _ := by rw [Real.rpow_one]
  have hrp : r^3 = r^(3/2:ℝ)*r^(3/2:ℝ) := by
    rw [←Real.rpow_add hr]; norm_num
  rw [hZp,hrp]
  field_simp

lemma initialQuadratic_small {C Z r ε : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (hε : 0 < ε) (hrel : Z*r^3 = ε^3) (hsmall : 4*C*ε^(3/2:ℝ) ≤ 1/20) :
    4*initialQuadratic C Z r*r^2 ≤ Z/(20*r) := by
  apply (le_div_iff₀ (by positivity : 0 < 20*r)).mpr
  have hi := initialQuadratic_scale hZ hr hε hrel
  unfold initialQuadratic
  calc
    _ = (4*C*((Z/r)^(3/2:ℝ)*r^3))*20 := by ring
    _ = Z*(4*C*ε^(3/2:ℝ))*20 := by rw [hi]; ring
    _ ≤ Z*(1/20)*20 := by gcongr
    _ = Z := by ring

lemma exists_barrier_epsilon (k : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    initialDensityConstant*ε^(6/5:ℝ) < 1/20 ∧
    4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20 := by
  have ht (a : ℝ) (ha : 0 < a) (C : ℝ) :
      Tendsto (fun ε : ℝ => C*ε^a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow ha.ne',mul_zero] using ((Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.const_mul C).mono_left
      (show (𝓝[>] (0:ℝ)) ≤ 𝓝 (0:ℝ) from inf_le_left)
  have h1 := (ht (6/5) (by norm_num) initialDensityConstant).eventually
    (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/20))
  have h2 := (ht (3/2) (by norm_num) (4*initialQuadraticConstant k)).eventually
    (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/20))
  have h3 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (show ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 from Iio_mem_nhds (by norm_num)).filter_mono inf_le_left
  have h4 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hε1,hi,hq⟩ := (h4.and (h3.and (h1.and h2))).exists
  exact ⟨ε,hε,hε1,hi,hq.le⟩

lemma exists_barrier_B {ε k : ℝ} (hε : 0 < ε) : ∃ B : ℝ,
    0 < B ∧ B ≤ ε^3/10 ∧ 4*Real.pi*k*Real.sqrt B ≤ 19/2 := by
  have ht : Tendsto (fun B : ℝ => 4*Real.pi*k*Real.sqrt B) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).const_mul (4*Real.pi*k)).mono_left
      (show (𝓝[>] (0:ℝ)) ≤ 𝓝 (0:ℝ) from inf_le_left)
  have h1 := ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 19/2))
  have h2 : ∀ᶠ B : ℝ in 𝓝[>] 0, B < ε^3/10 :=
    (show ∀ᶠ B : ℝ in 𝓝 0, B < ε^3/10 from Iio_mem_nhds (by positivity)).filter_mono inf_le_left
  have h3 : ∀ᶠ B : ℝ in 𝓝[>] 0, 0 < B := self_mem_nhdsWithin
  obtain ⟨B,hB,hBs,hBk⟩ := (h3.and (h2.and h1)).exists
  exact ⟨B,hB,hBs.le,hBk.le⟩

lemma initial_interpolation_eventually {ι : Type*} {l : Filter ι} {r : ι → ℝ}
    (hr : Tendsto r l (𝓝 0)) (C : ℝ) : ∀ᶠ i in l,
    C*(r i)^(1-3*masterExponent) ≤ 1/20 := by
  have hp : 0 < 1-3*masterExponent := by
    norm_num [masterExponent]
  have ht := ((Real.continuousAt_rpow_const 0 _ (Or.inr hp.le)).tendsto.comp hr).const_mul C
  simp only [Real.zero_rpow hp.ne',mul_zero] at ht
  exact (ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/20))).mono fun _ h => h.le

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialInvariantBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialInvariant_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma initial_error_mass_power {n Z r ε : ℝ} (hn : 0 ≤ n) (hcount : n ≤ 3*Z)
    (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hrel : Z*r^3 = ε^3) {p : ℝ} (hp : p ≤ 1728*r^37) :
    n*p ≤ 5184*r^32 := by
  have he : Z*r^37 = ε^3*r^34 := by
    calc
      _ = (Z*r^3)*r^34 := by ring
      _ = _ := by rw [hrel]
  have hε3 : ε^3 ≤ 1 := pow_le_one₀ hε.le hε1
  have hrp : r^34 ≤ r^32 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
  calc
    n*p ≤ n*(1728*r^37) := mul_le_mul_of_nonneg_left hp hn
    _ ≤ (3*Z)*(1728*r^37) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 5184*(ε^3*r^34) := by rw [show (3*Z)*(1728*r^37) = 5184*(Z*r^37) by ring,he]
    _ ≤ 5184*((1:ℝ)*r^32) := by gcongr
    _ = _ := by ring

theorem initial_barrier_invariant {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {μ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry μ))
    {M n Z B r ε k : ℝ} (hM : 0 ≤ M) (hn : 0 ≤ n)
    (hZ : 0 < Z) (hB : 0 < B) (hr : 0 < r) (hr1 : r ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k)
    (hrel : Z*r^3 = ε^3) (hquad : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBsmall : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    (hμn : ∀ sample x, 0 ≤ μ sample x) (hμb : ∀ sample x, μ sample x ≤ M)
    (hμi : ∀ sample, Integrable (μ sample)) (hμc : ∀ sample, ∫ x, μ sample x ≤ n)
    (hcount : n ≤ 3*Z)
    (hgood : ∀ sample ∈ A, ∀ x : TFSpace, ‖x‖ ≤ (11/10)*r → innerPotential r (μ sample) x ≤ Z/(10*r))
    (hbad : P.real Aᶜ ≤ 1728*r^37) :
    IsNuclearBarrier P μ Z k B (max B (32*ε^3)) r 2 (5184*r^32)
      (fun sample => initializedOffset Z B r (initialQuadratic (initialQuadraticConstant k) Z r)
        (initialCharge A r μ sample)) (initialError A r μ) := by
  let a := initialQuadratic (initialQuadraticConstant k) Z r
  have ha : 0 ≤ a := mul_nonneg (initialQuadraticConstant_pos hk).le (Real.rpow_nonneg (by positivity) _)
  have hq : 4*a*r^2 ≤ Z/(20*r) := initialQuadratic_small hZ hr hε hrel hquad
  have hreact : reaction k (2*(Z/r)) ≤ 6*a := initialQuadratic_reaction hZ hr
  have hBs : B ≤ Z*r^3/10 := by rwa [hrel]
  have hρm := initialCharge_measurable hA r hm
  have hρn := initialCharge_nonneg (A := A) (r := r) hμn
  have hρb := initialCharge_bound (A := A) (r := r) hμn hμb
  have hρs := initialCharge_support A r μ
  have hρg := initialCharge_good hZ.le hr.le hgood
  have hmω (sample : Ω) : Measurable (μ sample) := hm.comp (measurable_const.prodMk measurable_id)
  have hρmω (sample : Ω) : Measurable (initialCharge A r μ sample) :=
    hρm.comp (measurable_const.prodMk measurable_id)
  refine ⟨initializedOffset_joint_measurable hρm Z B a hr,?_,
    initializedOffset_deterministicBound hρmω hM hr hρn hρb hρs Z B a,
    initialCharge_measurable hA.compl r hm,initialCharge_nonneg hμn,
    ⟨M,initialCharge_bound hμn hμb⟩,?_,?_,?_,?_,?_,?_⟩
  · exact initializedOffset_deterministicLip hZ hr ha hM hB.le hq hBs hρmω hρn hρb hρs hρg
  · intro sample x hx
    exact truncated_density_exterior (initialCharge_support Aᶜ r μ sample) hx.le
  · exact ae_of_all _ (fun sample => (initial_barrier_with_error hZ hB hr ha hk hq hreact hBs hsub
      hmω hμn hμb hgood sample).2)
  · intro sample x hx
    exact initializedBarrier_lower hx
  · intro sample x hx
    exact initializedBarrier_cap hZ hr hB.le ha hq (le_max_left _ _)
      (by rw [mul_assoc,hrel]; exact le_max_right _ _) (hρn sample) hx
  · intro sample x hx
    exact initializedBarrier_tail hZ hr hB.le ha hq (hρn sample) (by linarith)
  · exact (initialError_expected_mass hA hm hμn hμb hμi hμc).trans
      (initial_error_mass_power hn hcount hr hr1 hε hε1 hrel hbad)

end Work_BarrierInitialInvariant_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOriginalForgettingBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis

lemma barrierErrorExponent_one_le : 1 ≤ barrierErrorExponent := by
  norm_num [barrierErrorExponent,masterExponent]

lemma barrierErrorExponent_pos : 0 < barrierErrorExponent := lt_of_lt_of_le (by norm_num) barrierErrorExponent_one_le

lemma sum_dyadic_powers_le {r a : ℝ} (hr : 0 < r) (ha : 1 ≤ a) (K : ℕ) :
    (∑ j ∈ Finset.range K, ((2:ℝ)^j*r)^a) ≤ ((2:ℝ)^K*r)^a-r^a := by
  have htwo : 2 ≤ (2:ℝ)^a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ha
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have he : ((2:ℝ)^(K+1)*r)^a = (2:ℝ)^a*((2:ℝ)^K*r)^a := by
      rw [pow_succ,show (2:ℝ)^K*2*r = 2*((2:ℝ)^K*r) by ring,Real.mul_rpow (by norm_num) (by positivity)]
    rw [he]
    have hh := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by positivity : 0 ≤ (2:ℝ)^K*r) a)
    linarith

lemma sum_dyadic_errors_le {r s C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (K : ℕ)
    (hend : (2:ℝ)^K*r ≤ s) :
    (∑ j ∈ Finset.range K, C*((2:ℝ)^j*r)^barrierErrorExponent) ≤ C*s^barrierErrorExponent := by
  rw [←Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC
  apply (sum_dyadic_powers_le hr barrierErrorExponent_one_le K).trans
  have hmon := Real.rpow_le_rpow (by positivity : 0 ≤ (2:ℝ)^K*r) hend barrierErrorExponent_pos.le
  linarith [Real.rpow_nonneg hr.le barrierErrorExponent]

lemma initial_budget_le_final_radius {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    5184*r^32 ≤ 5184*s^32 :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs 32) (by norm_num)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierQuantitativeStepBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierQuantitativeStep_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

lemma IsNuclearBarrier.mono_budget {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C r T η η' : ℝ}
    (old : IsNuclearBarrier P μ Z k B C r T η a p) (hη : η ≤ η') :
    IsNuclearBarrier P μ Z k B C r T η' a p :=
  { old with mass := old.mass.trans hη }

lemma IsNuclearBarrier.mono_cap {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C C' r T η : ℝ}
    (old : IsNuclearBarrier P μ Z k B C r T η a p) (hC : C ≤ C') :
    IsNuclearBarrier P μ Z k B C' r T η a p := by
  refine { old with upper := fun sample x hx => (old.upper sample x hx).trans ?_ }
  exact div_le_div_of_nonneg_right hC (pow_nonneg (norm_nonneg _) _)

end Work_BarrierQuantitativeStep_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierActualInitializationBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

section Work_BarrierPullback_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation

lemma IsNuclearBarrier.pullback {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {f : Ω → Ω'} (hf : Measurable f)
    {μ a p : Ω' → TFSpace → ℝ} {Z k B C r T η : ℝ}
    (old : IsNuclearBarrier (P.map f) μ Z k B C r T η a p) :
    IsNuclearBarrier P (fun sample => μ (f sample)) Z k B C r T η
      (fun sample => a (f sample)) (fun sample => p (f sample)) := by
  refine ⟨old.measurable_offset.comp (hf.prodMap measurable_id),?_,?_,
    old.measurable_error.comp (hf.prodMap measurable_id),
    fun sample x => old.nonneg_error (f sample) x,?_,
    fun sample x hx => old.support_error (f sample) x hx,?_,
    fun sample x hx => old.lower (f sample) x hx,
    fun sample x hx => old.upper (f sample) x hx,
    fun sample x hx => old.tail (f sample) x hx,?_⟩
  · intro x
    obtain ⟨L,t,ht,hL⟩ := old.uniform_lipschitz_offset x
    exact ⟨L,t,ht,fun sample => hL (f sample)⟩
  · intro K hK
    obtain ⟨L,hL⟩ := old.bound_offset K hK
    exact ⟨L,fun sample x hx => hL (f sample) x hx⟩
  · obtain ⟨L,hL⟩ := old.bounded_error
    exact ⟨L,fun sample x => hL (f sample) x⟩
  · exact ae_of_ae_map hf.aemeasurable old.weak
  · have hm : AEStronglyMeasurable (fun sample => ∫ x, p sample x) (P.map f) :=
      old.measurable_error.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    rw [←integral_map hf.aemeasurable hm]
    exact old.mass

end Work_BarrierPullback_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierDataSelectionBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

lemma nuclear_radius_le_of_relation {Z r s ε : ℝ} (hZ : 0 < Z) (hs : 0 ≤ s)
    (hrel : Z*r^3 = ε^3) (hscale : ε^3 ≤ Z*s^3) : r ≤ s := by
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hs
  apply (mul_le_mul_iff_right₀ hZ).mp
  simpa only [mul_comm r, mul_comm (s^3)] using hrel.le.trans hscale

lemma initial_numerics_eventually {ι : Type*} {l : Filter ι}
    (Z : ι → ℕ) (s : ι → ℝ) (hZ : ∀ᶠ i in l, 1 ≤ Z i)
    (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hscale : Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop)
    {ε : ℝ} (hε : 0 < ε) (G c δ : ℝ) :
    ∀ᶠ i in l, InitialNumerics (Z i) (s i) ε G c δ := by
  let r : ι → ℝ := fun i => ε*(Z i:ℝ)^(-1/3:ℝ)
  have hZr : ∀ᶠ i in l, 0 < (Z i:ℝ) := hZ.mono fun i hi => by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hi)
  have hr : ∀ᶠ i in l, 0 < r i := hZr.mono fun i hi => mul_pos hε (Real.rpow_pos_of_pos hi _)
  have hrel : ∀ᶠ i in l, (Z i:ℝ)*(r i)^3 = ε^3 :=
    hZr.mono fun _ hi => nuclear_radius_relation hi
  have hr0 : Tendsto r l (𝓝 0) := nuclear_radius_tendsto hs0 hs hscale ε
  have hr1 : ∀ᶠ i in l, r i ≤ 1 :=
    (hr0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))).mono fun _ hi => hi.le
  have hs1 : ∀ᶠ i in l, s i ≤ 1 :=
    (hs0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))).mono fun _ hi => hi.le
  have hrs : ∀ᶠ i in l, r i ≤ s i := by
    filter_upwards [hZr,hs,hrel,hscale.eventually (eventually_ge_atTop (ε^3))] with i hz hs hr hh
    exact nuclear_radius_le_of_relation hz hs.le hr hh
  have hbudget := initial_budget_eventually hε hZr hs hr hrel hr0 hscale δ
  have hinterp := initial_interpolation_eventually hr0 (48*Real.pi*G*c⁻¹^3)
  filter_upwards [hZ,hs,hr,hr1,hs1,hrs,hrel,hbudget,hinterp] with i hz hs hr hr1 hs1 hrs hrel hb hi
  exact ⟨hz,hs,hs1,hr,hr1,hrs,hrel,hb,hi⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailInitialPointwiseBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem tail_initial_barrier {Z : ℕ} (hZ : 1 ≤ Z)
    {lam r₀ s c₁ ε k B : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hr1 : r₀ ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r₀ ≤ s) (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k) (hB : 0 < B)
    (hrel : (Z:ℝ)*r₀^3 = ε^3)
    (heps : initialDensityConstant*ε^(6/5:ℝ) < 1/20)
    (hquad : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBsmall : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {N K : ℕ} (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ G : ℝ}
    {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
    (j : Fin (K+1)) (h₀ : 0 < p₀ j) (hp40 : p₀ j ≤ r₀^40)
    (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hinterp : (48*Real.pi*G*c₁⁻¹^3)*r₀^(1-3*masterExponent) ≤ 1/20)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ a p : OriginalDatum N K (fun k => dyadicObservationWidth r₀ k) j → TFSpace → ℝ,
      IsNuclearBarrier
        ((physicalObservationLaw (graphRawLaw F) K).map
          (originalDatum (fun k => dyadicObservationWidth r₀ k) j))
        (jointMasterPosterior (graphRawLaw F) (fun k => dyadicObservationWidth r₀ k) j c₁ r₀ s g)
        (Z:ℝ) k B (max B (32*ε^3)) r₀ 2 (5184*r₀^32) a p := by
  have hZr : 0 < (Z:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hZ)
  have hsmall := initial_density_small_of_nuclear_relation hZr hr hε hrel heps
  have hcount := actual_priced_particle_bound_three Z hZ hlam hN
  obtain ⟨A,hA,hgood,hbad⟩ := tail_initial_good_event hZ hlam hr hr1 hs hs1 hrs hc hc1
    hN hF j h₀ hp40 hbudget hsmall hinterp hg hcg hG hgn hrad hgs
  let := graphRawLaw_probability F hF.1
  let ell : Fin K → ℝ := fun l => dyadicObservationWidth r₀ l
  let μ := jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g
  let P := (physicalObservationLaw (graphRawLaw F) K).map (originalDatum ell j)
  have hP : IsProbabilityMeasure P := by first | exact Measure.isProbabilityMeasure_map (originalDatum_measurable ell j).aemeasurable | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let := hP
  let A' : Set (OriginalDatum N K ell j) := A
  have hAm : MeasurableSet A' := hA
  have hbad' : P.real A'ᶜ ≤ 1728*r₀^37 := by
    change ((physicalObservationLaw (graphRawLaw F) K).map (originalDatum ell j)).real A'ᶜ ≤ _
    rw [map_measureReal_apply (originalDatum_measurable ell j) hAm.compl]
    exact hbad
  obtain ⟨M,hM,hMb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr hs hrs hg.continuous hcg
  have hμm : Measurable (Function.uncurry μ) := jointMasterPosterior_measurable (graphRawLaw F) ell j hc hr hs hg.continuous
  have hμn : ∀ z y, 0 ≤ μ z y := jointMasterPosterior_nonneg (graphRawLaw F) ell j c₁ r₀ s g
  have hμb : ∀ z y, μ z y ≤ M := fun z y => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hMb z y)
  have hμi : ∀ z, Integrable (μ z) := jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr hs hg.continuous hgn
  have hμc : ∀ z, ∫ y, μ z y ≤ (N:ℝ) := fun z =>
    (jointMasterPosterior_mass (graphRawLaw F) ell j hc hr hs hg.continuous hgn z).le
  have hi := initial_barrier_invariant hAm hμm hM (Nat.cast_nonneg N) hZr hB hr hr1 hε hε1 hk
    hrel hquad hBsmall hsub hμn hμb hμi hμc (by exact_mod_cast hcount) hgood hbad'
  exact ⟨_,_,hi⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailInitialEventuallyBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_TailInitialEventually_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

lemma tailPolynomialThreshold_pos {r : ℝ} (hr : 0 < r) {K : ℕ} (j : Fin (K+1)) :
    0 < tailPolynomialThreshold r j := by
  unfold tailPolynomialThreshold
  positivity

lemma tailPolynomialThreshold_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (K : ℕ) :
    tailPolynomialThreshold r (0 : Fin (K+1)) = r^40 := by
  simp only [tailPolynomialThreshold,Fin.val_zero,pow_zero,one_mul]
  exact min_eq_right (pow_le_one₀ hr hr1)

end Work_TailInitialEventually_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma masterWidth_inverse_cube_radius {c₁ r₀ s r : ℝ} (hc : 0 < c₁) (hr : 0 < r)
    (hrs : r ≤ s) {y : Space} (hy : r ≤ ‖y‖) :
    (masterWidth c₁ r₀ s y)⁻¹^3 ≤ c₁⁻¹^3*r^(-3-3*masterExponent) := by
  have hl := masterWidth_radius_lower (r₀ := r₀) hc.le hr hrs hy
  have hp : 0 < c₁*r^(1+masterExponent) := mul_pos hc (Real.rpow_pos_of_pos hr _)
  have hinv := inv_anti₀ hp hl
  have he : (c₁*r^(1+masterExponent))⁻¹^3 = c₁⁻¹^3*r^(-3-3*masterExponent) := by
    rw [mul_inv_rev,mul_pow,←Real.rpow_neg hr.le,←Real.rpow_mul_natCast hr.le]
    have hex : -(1+masterExponent)*(3:ℝ) = -3-3*masterExponent := by ring
    norm_num only [Nat.cast_ofNat]
    rw [hex]
    ring
  exact (pow_le_pow_left₀ (inv_nonneg.mpr (hp.le.trans hl)) hinv 3).trans_eq he

theorem original_master_annular_second_moment {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {r₀ s r Q : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ r → r ≤ s → 0 ≤ Q →
      (∫ x, (rawAnnularCount (r/2) (3*r) x)^2 ∂μ) ≤ Q*r^(-6:ℝ) →
      ∀ y : Space, r ≤ ‖y‖ → ‖y‖ ≤ 2*r →
      (∫ z, (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y)^2
        ∂physicalObservationLaw μ K) ≤ D*Q*r^(-12-6*masterExponent) := by
  obtain ⟨A,hAn,hA⟩ := masterKernel_amplitude hg hgs
  refine ⟨(A*c₁⁻¹^3)^2,sq_nonneg _,?_⟩
  intro N K μ hμ ell j r₀ s r Q hr₀ hs hs1 hrr hrs hQ hcount y hy hy2
  have hr : 0 < r := hr₀.trans_le hrr
  let B := A*c₁⁻¹^3*r^(-3-3*masterExponent)
  have hBn : 0 ≤ B := by dsimp only [B]; positivity
  have hb (x) : masterKernel c₁ r₀ s g x y ≤ B :=
    (hA hc hcL hr₀ hs hs1 x y).trans (by
      simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_left
        (masterWidth_inverse_cube_radius (r₀ := r₀) hc hr hrs hy) hAn)
  have ht := masterWidth_radius_upper hc.le hr₀ hs hs1 hrr hy hy2
  have hsmall : 2*masterWidth c₁ r₀ s y < r/2 := by
    have hc2 : c₁ < 1/8 := by norm_num at hcL ⊢; linarith
    nlinarith
  have hsupport : Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆ ball y (r/2) := by
    rw [masterKernel_eq_widthKernel hc hr₀ hs g]
    exact (widthKernel_support_local (masterWidth_small_lipschitz hc hcL hr₀ hs hs1)
      (masterWidth_pos hc hr₀ hs) (by norm_num) (masterProfile_support hgs) y).trans
      (closedBall_subset_ball hsmall)
  have hm := original_master_second_moment_from_count μ ell j hc hr₀ hs hg y hBn hb hsupport
  have hraw : (∫ x, (rawBallCount y (r/2) x)^2 ∂μ) ≤
      ∫ x, (rawAnnularCount (r/2) (3*r) x)^2 ∂μ := by
    apply integral_mono
      (bounded_integrable_square (rawBallCount_measurable y (r/2)) (fun x => by
        rw [Real.norm_of_nonneg (rawBallCount_nonneg _ _ _)]; exact rawBallCount_le _ _ _))
      (bounded_integrable_square (rawAnnularCount_measurable (r/2) (3*r)) (fun x => by
        rw [Real.norm_of_nonneg (rawAnnularCount_nonneg _ _ _)]; exact rawAnnularCount_le _ _ _))
    intro x
    exact pow_le_pow_left₀ (rawBallCount_nonneg _ _ _)
      (rawBallCount_le_annular hr.le hy hy2 le_rfl x) 2
  apply (hm.trans (mul_le_mul_of_nonneg_left (hraw.trans hcount) (sq_nonneg B))).trans_eq
  dsimp only [B]
  rw [mul_pow,←Real.rpow_mul_natCast hr.le]
  calc
    (A*c₁⁻¹^3)^2*r^((-3-3*masterExponent)*2)*(Q*r^(-6:ℝ)) =
        (A*c₁⁻¹^3)^2*Q*(r^((-3-3*masterExponent)*2)*r^(-6:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hr]; congr 2; ring

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityTailTiltBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma OwnProbabilityTailTiltState.to_tailTiltState {N K : ℕ} {F : fermionGraph N}
    {Z lam r δ : ℝ} {p₀ p₁ : Fin (K+1) → ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ δ F)
    (hr : 0 < r) (h₁ : ∀ j, 0 < p₁ j) (h01 : ∀ j, p₀ j ≤ p₁ j) :
    TailTiltState Z lam r K p₁ δ F := by
  refine ⟨hF.1,hF.2.1,?_⟩
  intro j A hA hp
  obtain ⟨G,hGn,hGlaw,hGE⟩ := hF.2.2 j A hA ((h01 j).trans hp)
  refine ⟨G,hGn,hGlaw,hGE.trans ?_⟩
  let := graphRawLaw_probability F hF.1
  let := physicalObservationLaw_probability (K := K) (graphRawLaw F)
  exact dyadicUniformEventBudget_mono (by positivity) (h₁ j) hp (measureReal_le_one (s := A))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TinyProbabilityFloorBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombBarrier

lemma tinyProbabilityFloor_le_polynomial {Z u : ℝ} (hZ : 0 ≤ Z) (hu : 0 ≤ u) :
    tinyProbabilityFloor Z u ≤ min 1 (u^40) := by
  have hn : 0 ≤ min (1:ℝ) (u^80) := le_min (by norm_num) (pow_nonneg hu _)
  have hd : 1 ≤ 1+Z := by linarith
  apply (div_le_self hn hd).trans
  by_cases h : u ≤ 1
  · apply min_le_min_left 1
    have h40 := pow_le_one₀ hu h (n := 40)
    have hpow : u^80 = (u^40)^2 := by ring
    rw [hpow]
    nlinarith [pow_nonneg hu 40]
  · have h40 : 1 ≤ u^40 := one_le_pow₀ (by linarith)
    rw [min_eq_left h40]
    exact min_le_left _ _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityRareCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma originalQueryField_info_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (y : Space) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => originalQueryField F Z lam r j c₁ r₀ s z y) :=
  measurable_const.sub (jointMasterPosterior_potential_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j y hc hr₀ hs canonicalRealPacket_smooth.continuous)

end Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_InverseNetEventsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

lemma originalQueryDensity_info_measurable {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (y : Space) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => originalQueryDensity F r j c₁ r₀ s z y) := by
  exact (jointMasterPosterior_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j hc hr₀ hs
    canonicalRealPacket_smooth.continuous).comp (measurable_id.prodMk measurable_const)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservedAnnularCountBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombBarrier CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma annularOffsetMass_one_small {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (annularOffsetMass 1 r)^2 ≤ 4*r^(-6:ℝ) := by
  have hpow : r^3 ≤ 1 := pow_le_one₀ hr.le hr1
  have hi : 1 ≤ 1/r^3 := (one_le_div (pow_pos hr 3)).mpr hpow
  have hs : Real.sqrt r ≤ 1 := (Real.sqrt_le_one).mpr hr1
  have hm : annularOffsetMass 1 r ≤ 2*(1/r^3) := by
    simp only [annularOffsetMass,one_mul,max_eq_left hi]
    linarith only [hi,hs]
  have hmn : 0 ≤ annularOffsetMass 1 r := (zero_le_one.trans (annularOffsetMass_one_le 1 r))
  have he : (2*(1/r^3))^2 = 4*r^(-6:ℝ) := by
    rw [Real.rpow_neg hr.le,Real.rpow_ofNat]
    field_simp
    ring
  exact (pow_le_pow_left₀ hmn hm 2).trans_eq he

theorem exists_actual_priced_moment_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Z lam : ℝ} {N : ℕ}, 0 ≤ Z → 0 < lam →
      PriceMinimizes (energy Z) lam N → ∀ F : fermionGraph N,
      ‖fermionGraphValue N F‖^2 = 1 →
      formEnergy Z (graphFormVector F) ≤ energy Z N+1 →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∫ x, (rawAnnularCount (r/2) (3*r) x)^2 ∂graphRawLaw F) ≤ C*r^(-6:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_priced_annular_count_constant (alpha := (1/2:ℝ)) (beta := 3) (by norm_num)
  have hCn : 0 ≤ C := zero_le_one.trans hC
  refine ⟨4*C,by positivity,?_⟩
  intro Z lam N hZ hlam hN F hn hF r hr hr1
  have hψ := graphFormVector_admissible F hn
  have hm : formMass (graphFormVector F) = 1 := hψ.2.2.2.2.1
  have he : max (corePriceExcess Z lam (graphFormVector F)) 0 ≤ 1 :=
    max_le (priced_graph_tilt_excess hN F hn hF) zero_le_one
  have hb := hbound Z lam N (graphFormVector F) hψ.sobolevFermion hm hZ hlam 1 r zero_le_one hr he
  rw [rawAnnularMoment_eq_integral hψ.sobolevFermion.sobolevVector,formRawLaw_graph] at hb
  have hh := hb.trans (mul_le_mul_of_nonneg_left (annularOffsetMass_one_small hr hr1) hCn)
  simpa only [show (1/2:ℝ)*r = r/2 by ring, show C*(4*r^(-6:ℝ)) = (4*C)*r^(-6:ℝ) by ring] using hh

theorem actual_original_posterior_moment {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ {Z lam : ℝ} {N K : ℕ}, 0 ≤ Z → 0 < lam →
      PriceMinimizes (energy Z) lam N → ∀ F : fermionGraph N,
      ‖fermionGraphValue N F‖^2 = 1 →
      formEnergy Z (graphFormVector F) ≤ energy Z N+1 →
      ∀ (ell : Fin K → ℝ) (j : ℕ) {r₀ s r : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ r → r ≤ s →
      ∀ y : Space, r ≤ ‖y‖ → ‖y‖ ≤ 2*r →
      (∫ z, (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z) y)^2
        ∂physicalObservationLaw (graphRawLaw F) K) ≤ Q*r^(-12-6*masterExponent) := by
  obtain ⟨C,hC,hcount⟩ := exists_actual_priced_moment_constant
  obtain ⟨D,hD,hpost⟩ := original_master_annular_second_moment hg hgs hc hcL
  refine ⟨D*C,mul_nonneg hD hC,?_⟩
  intro Z lam N K hZ hlam hN F hn hF ell j r₀ s r hr₀ hs hs1 hrr hrs y hy hy2
  let := graphRawLaw_probability F hn
  exact hpost (graphRawLaw F) ell j hr₀ hs hs1 hrr hrs hC
    (hcount hZ hlam hN F hn hF r (hr₀.trans_le hrr) (hrs.trans hs1)) y hy hy2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SelectedScreenedProfileBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfDensityCoefficient_pos : 0 < tfDensityCoefficient := by
  unfold tfDensityCoefficient
  have hh := tfKinetic_pos
  positivity
end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FiniteBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

lemma originalQueryField_eq_nuclear_mean {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) (c r₀ s : ℝ) (q) (y : Space) :
    originalQueryField F Z lam r j c r₀ s q y =
      nuclearField Z y+meanFieldOffset lam
        (originalMasterField (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c r₀ s canonicalRealPacket q) y := by
  unfold originalQueryField nuclearField meanFieldOffset
  have he : originalQueryDensity F r j c r₀ s q =
      originalMasterField (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
        j c r₀ s canonicalRealPacket q := rfl
  rw [he]
  ring

lemma actual_finite_barrier_from_good {N K : ℕ} {Z lam r s c A Q B C M lam1 lam2 e ξ hl hh : ℝ}
    (_hZ : 0 ≤ Z) (_hlam : 0 < lam) (hr : 0 < r) (hs : 0 < s) (_hs1 : s ≤ 1)
    (hrs : r ≤ s) (hc : 0 < c) (_hcL : c < (10*(100000:ℝ))⁻¹)
    (_hN : PriceMinimizes (energy Z) lam N) {F : fermionGraph N}
    (hFn : ‖fermionGraphValue N F‖^2 = 1)
    (_hFE : formEnergy Z (graphFormVector F) ≤ energy Z N+1)
    (cal : OutwardCalibration tfDensityCoefficient B C M lam1 lam2 e ξ hl hh)
    (hCC : actualInverseCap ≤ C) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hm : ∀ (j : ℕ) {v : ℝ}, r ≤ v → v ≤ s → ∀ y : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v →
      (∫ q, (originalQueryDensity F r j c r s q y)^2 ∂physicalObservationLaw (graphRawLaw F) K)
        ≤ Q*v^(-12-6*masterExponent))
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ} {η : ℝ}
    (initial : IsNuclearBarrier (physicalObservationLaw (graphRawLaw F) K)
      (originalQueryDensity F r 0 c r s) Z tfDensityCoefficient B C r 2 η a p)
    (hgood : ∀ j : Fin K, (2:ℝ)^j.val*r ≤ s →
      ∃ G : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)),
        MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] G ∧
        (physicalObservationLaw (graphRawLaw F) K).real Gᶜ ≤ A*((2:ℝ)^j.val*r)^25 ∧
        ∀ q ∈ G, ∀ y : Space, (2:ℝ)^j.val*r ≤ ‖y‖ → ‖y‖ ≤ 4*M*((2:ℝ)^j.val*r) →
          InverseComparisonAt ‖y‖ (originalQueryField F Z lam r j c r s q y)
            (originalQueryDensity F r j c r s q y) tfDensityCoefficient hl hh ξ actualInverseCap)
    (J : ℕ) (hJK : J ≤ K) (hJs : (2:ℝ)^J*r ≤ s) :
    ∃ a' p', IsNuclearBarrier (physicalObservationLaw (graphRawLaw F) K)
      (originalQueryDensity F r J c r s) Z tfDensityCoefficient B C ((2:ℝ)^J*r) (max 2 M)
      (η+(32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*s^barrierErrorExponent) a' p' := by
  classical
  let := graphRawLaw_probability F hFn
  have hjr (j : ℕ) : r ≤ (2:ℝ)^j*r := le_mul_of_one_le_left hr.le (one_le_pow₀ (by norm_num))
  have hjs (j : ℕ) (hj : j < J) : (2:ℝ)^j*r ≤ s :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj.le) hr.le).trans hJs
  choose G hG hp hcomp using fun j : Fin J =>
    hgood ⟨j,Nat.lt_of_lt_of_le j.isLt hJK⟩ (hjs j j.isLt)
  let good : ℕ → (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → Prop :=
    fun j q => if hj : j < J then q ∈ G ⟨j,hj⟩ else True
  have hg (j) (hj : j < J) : MeasurableSet {q | good j q} := by
    simp only [good,dite_eq_left hj]
    exact (observationInformation_le _ _) _ (hG ⟨j,hj⟩)
  have hcomp' (j) (hj : j < J) (q) (hq : good j q) (y : Space)
      (hy : (2:ℝ)^j*r ≤ ‖y‖) (hy' : ‖y‖ < 4*M*((2:ℝ)^j*r)) :
      InverseComparisonAt ‖y‖
        (nuclearField Z y+meanFieldOffset lam
          (originalMasterField (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
            j c r s canonicalRealPacket q) y)
        (originalMasterField (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c r s canonicalRealPacket q y)
        tfDensityCoefficient hl hh ξ actualInverseCap := by
    simp only [good,dite_eq_left hj] at hq
    have h := hcomp ⟨j,hj⟩ q hq y hy hy'.le
    rw [originalQueryField_eq_nuclear_mean] at h
    exact h
  obtain ⟨a',p',hnew⟩ := original_finite_barrier_iteration (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) hc hr hs hrs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_compact canonicalRealPacket_normalized
    cal hA hQ good hg initial
    (fun j hj q hq y hy hy' => by
      have h := (hcomp' j hj q hq y hy hy').1.trans hCC
      exact (le_div_iff₀ (pow_pos (hr.trans_le ((hjr j).trans hy)) 4)).mpr (by simpa [mul_comm] using h))
    hcomp'
    (fun j hj => by simpa only [good,dite_eq_left hj,Set.compl_def] using hp ⟨j,hj⟩)
    (fun j hj y hy hy' => hm j (hjr j) (hjs j hj) y hy hy'.le)
  refine ⟨a',p',hnew.mono_budget ?_⟩
  exact add_le_add le_rfl (sum_dyadic_errors_le (C := 32*Real.pi/3*Real.sqrt A*Real.sqrt Q)
    hr (by positivity) J hJs)

end
open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_FullAnnulusNormalization
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma localTFResponse_eq_coefficient {h : ℝ} (hh : 0 ≤ h) :
    localTFResponse h = (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹*h^(3/2:ℝ) := by
  rw [localTFResponse,max_eq_left hh,Real.div_rpow hh (mul_pos (by norm_num) tfKinetic_pos).le]
  ring

lemma localTFResponse_div_radius_four {b : ℝ} (hb : 0 < b) (h : ℝ) :
    localTFResponse (h/b^4) = localTFResponse h/b^6 := by
  have ht := localTFResponse_rescale hb (h/b^4)
  have he : b^4*(h/b^4) = h := by field_simp
  rw [he] at ht
  exact (eq_div_iff (pow_ne_zero 6 hb.ne')).mpr (by linarith)

lemma inverseComparisonAt_of_cell {y : Space} {H μ lo hi xi C : ℝ}
    (hlo : 0 ≤ lo)
    (hcap : (localCellRadius y)^4*H ≤ C)
    (hinv : ∀ h ∈ Icc (lo/100000^4) (hi/100000^4),
      (localTFResponse h < (localCellRadius y)^6*μ → h-xi/100000^4 ≤ (localCellRadius y)^4*H) ∧
      ((localCellRadius y)^6*μ < localTFResponse h → (localCellRadius y)^4*H ≤ h+xi/100000^4)) :
    InverseComparisonAt ‖y‖ H μ (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi (100000^4*C) := by
  have hcap' : ‖y‖^4*H ≤ 100000^4*C := by
    dsimp [localCellRadius] at hcap
    rw [div_pow,div_mul_eq_mul_div] at hcap
    simpa [mul_comm] using (div_le_iff₀ (by norm_num : (0:ℝ) < 100000^4)).mp hcap
  refine ⟨hcap',?_,?_⟩
  · intro h hh ht
    have hh' : h/100000^4 ∈ Icc (lo/100000^4) (hi/100000^4) :=
      ⟨div_le_div_of_nonneg_right hh.1 (by positivity),div_le_div_of_nonneg_right hh.2 (by positivity)⟩
    have hr := localTFResponse_div_radius_four (by norm_num : (0:ℝ) < 100000) h
    rw [localTFResponse_eq_coefficient (hlo.trans hh.1)] at hr
    have hf := (hinv _ hh').1
    simp only [localCellRadius,div_pow,div_mul_eq_mul_div] at hf
    rw [hr] at hf
    have hz := hf ((div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^6)).mpr ht)
    rw [←sub_div] at hz
    exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^4)).mp hz
  · intro h hh ht
    have hh' : h/100000^4 ∈ Icc (lo/100000^4) (hi/100000^4) :=
      ⟨div_le_div_of_nonneg_right hh.1 (by positivity),div_le_div_of_nonneg_right hh.2 (by positivity)⟩
    have hr := localTFResponse_div_radius_four (by norm_num : (0:ℝ) < 100000) h
    rw [localTFResponse_eq_coefficient (hlo.trans hh.1)] at hr
    have hf := (hinv _ hh').2
    simp only [localCellRadius,div_pow,div_mul_eq_mul_div] at hf
    rw [hr] at hf
    have hz := hf ((div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^6)).mpr ht)
    rw [←add_div] at hz
    exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^4)).mp hz

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ContinuousUniversalEvent
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open Set MeasureTheory

theorem measurableSet_forall_closed_parameter
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    {P : Ω → X → Prop} (hm : ∀ x, MeasurableSet {ω | P ω x})
    (hc : ∀ ω, IsClosed {x | P ω x}) : MeasurableSet {ω | ∀ x, P ω x} := by
  obtain ⟨D,hD,hd⟩ := TopologicalSpace.exists_countable_dense X
  have he : {ω | ∀ x, P ω x} = ⋂ x ∈ D, {ω | P ω x} := by
    ext ω
    simp only [mem_ofPred_eq,mem_iInter]
    constructor
    · intro h x _
      exact h x
    · intro h x
      exact closure_minimal h (hc ω) (hd x)
  rw [he]
  exact MeasurableSet.biInter hD (fun x _ => hm x)

open Set MeasureTheory
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma inverseComparisonAt_closed {X : Type*} [TopologicalSpace X]
    {d H μ : X → ℝ} (hd : Continuous d) (hH : Continuous H) (hμ : Continuous μ)
    (κ lo hi xi C : ℝ) : IsClosed {x | InverseComparisonAt (d x) (H x) (μ x) κ lo hi xi C} := by
  have hf := (hd.pow 4).mul hH
  have hr := (hd.pow 6).mul hμ
  have h₀ := isClosed_le hf continuous_const (g := fun _ => C)
  have h₁ := isClosed_iInter (fun h : Icc lo hi =>
    (isClosed_le hr continuous_const (g := fun _ => κ*(h:ℝ)^(3/2:ℝ))).union
      (isClosed_le continuous_const hf (f := fun _ => (h:ℝ)-xi)))
  have h₂ := isClosed_iInter (fun h : Icc lo hi =>
    (isClosed_le continuous_const hr (f := fun _ => κ*(h:ℝ)^(3/2:ℝ))).union
      (isClosed_le hf continuous_const (g := fun _ => (h:ℝ)+xi)))
  convert h₀.inter (h₁.inter h₂) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_iInter,mem_union,mem_ofPred_eq,InverseComparisonAt,
    imp_iff_not_or,not_lt,Subtype.forall,Pi.mul_apply,Pi.pow_apply]

lemma inverseComparisonAt_measurable {Ω : Type*} [MeasurableSpace Ω]
    {H μ : Ω → ℝ} (hH : Measurable H) (hμ : Measurable μ)
    (d κ lo hi xi C : ℝ) : MeasurableSet {q | InverseComparisonAt d (H q) (μ q) κ lo hi xi C} := by
  have hf := hH.const_mul (d^4)
  have hr := hμ.const_mul (d^6)
  have h₀ := measurableSet_le hf measurable_const (g := fun _ => C)
  have ht : Continuous (fun h : Icc lo hi => κ*(h:ℝ)^(3/2:ℝ)) :=
    ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp continuous_subtype_val).const_mul κ
  have h₁ : MeasurableSet {q | ∀ h : Icc lo hi,
      d^6*μ q ≤ κ*(h:ℝ)^(3/2:ℝ) ∨ (h:ℝ)-xi ≤ d^4*H q} := by
    apply measurableSet_forall_closed_parameter
    · intro h
      exact (measurableSet_le hr measurable_const).union (measurableSet_le measurable_const hf)
    · intro q
      exact (isClosed_le continuous_const ht).union
        (isClosed_le (continuous_subtype_val.sub continuous_const) continuous_const)
  have h₂ : MeasurableSet {q | ∀ h : Icc lo hi,
      κ*(h:ℝ)^(3/2:ℝ) ≤ d^6*μ q ∨ d^4*H q ≤ (h:ℝ)+xi} := by
    apply measurableSet_forall_closed_parameter
    · intro h
      exact (measurableSet_le measurable_const hr).union (measurableSet_le hf measurable_const)
    · intro q
      exact (isClosed_le ht continuous_const).union
        (isClosed_le continuous_const (continuous_subtype_val.add_const xi))
  convert h₀.inter (h₁.inter h₂) using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  simp only [mem_inter_iff,mem_ofPred_eq,InverseComparisonAt,imp_iff_not_or,not_lt,Subtype.forall]

lemma original_inverse_fullAnnulus_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s u B κ lo hi xi C : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s) (hu : 0 < u) :
    MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      {q | ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
        InverseComparisonAt ‖y‖
          (originalQueryField F Z lam r j c₁ r₀ s q y)
          (originalQueryDensity F r j c₁ r₀ s q y) κ lo hi xi C} := by
  let Y := {y : Space // u ≤ ‖y‖ ∧ ‖y‖ ≤ B*u}
  have he : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      {q | ∀ y : Y, InverseComparisonAt ‖(y:Space)‖
        (originalQueryField F Z lam r j c₁ r₀ s q y)
        (originalQueryDensity F r j c₁ r₀ s q y) κ lo hi xi C} := by
    apply @measurableSet_forall_closed_parameter _ Y
      (observationInformation (fun k : Fin K => dyadicObservationWidth r k) j) _ _
    · intro y
      exact @inverseComparisonAt_measurable _
        (observationInformation (fun k : Fin K => dyadicObservationWidth r k) j) _ _
        (originalQueryField_info_measurable F Z lam r j hc hr hs y)
        (originalQueryDensity_info_measurable F r j hc hr hs y) _ _ _ _ _ _
    · intro q
      have hfield : Continuous (fun y : Y => originalQueryField F Z lam r j c₁ r₀ s q y) := by
        apply (originalQueryField_continuousOn_punctured F Z lam r j hc hr hs hrs q).comp_continuous
          continuous_subtype_val
        intro y
        change (y:Space) ≠ 0
        exact norm_pos_iff.mp (hu.trans_le y.property.1)
      have hden : Continuous (fun y : Y => originalQueryDensity F r j c₁ r₀ s q y) :=
        (jointMasterPosterior_continuous (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j hc hr hs hrs
          canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j q)).comp continuous_subtype_val
      exact inverseComparisonAt_closed continuous_subtype_val.norm hfield hden _ _ _ _ _
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  simp only [mem_ofPred_eq,Subtype.forall,Y]
  simp only [and_imp]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FullAnnulusGoodEvent
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom
open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local instance] physicalObservationLaw_probability

theorem exists_actual_fullAnnulus_good_constant {B c₁ lo hi xi : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real Gᶜ ≤ C*u^25 ∧
          ∀ q ∈ G, ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
            InverseComparisonAt ‖y‖
              (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y)
              (originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y)
              (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi
              (100000^4*(16*(tfPatchCapConstant+3))) := by
  have hp : (0:ℝ) < 100000^4 := by norm_num
  obtain ⟨C,hC,hresult⟩ := exists_actual_fullAnnulus_inverse_constant hB hc hcL
    (div_le_div_of_nonneg_right hlh hp.le) (div_pos hxi hp)
    (lo := lo/100000^4) (hi := hi/100000^4)
    (by rw [←mul_div_assoc]; exact (div_lt_div_iff_of_pos_right hp).mpr hlo)
  refine ⟨C,hC,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs hr hF
  have he := hresult hδ hs hr hF
  filter_upwards [he,hr,hF,hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hie hri hFi hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := hjs.trans hsi.le
  have hrs : r₀ i ≤ s i := (le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))).trans hjs
  have hsp : 0 < s i := hu.trans_le hjs
  obtain ⟨E,hE,hpE,hqE⟩ := hie j hjs
  let G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) :=
    {q | ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
      InverseComparisonAt ‖y‖
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y)
        (originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y)
        (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi
        (100000^4*(16*(tfPatchCapConstant+3)))}
  have hG : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G :=
    original_inverse_fullAnnulus_measurable (F i) (Z i) (lam i) (r₀ i) j hc hri hsp hrs hu
  have hae : Gᶜ ≤ᵐ[physicalObservationLaw (graphRawLaw (F i)) (K i)] E := by
    filter_upwards [hqE] with q hq
    intro hqG
    by_contra hqnot
    apply hqG
    intro y hyl hyh
    have hh := hq hqnot
    exact inverseComparisonAt_of_cell (by linarith) (hh.2 y hyl hyh) (hh.1 y hyl hyh)
  let := graphRawLaw_probability (F i) hFi.2.2.1
  refine ⟨G,hG,?_,fun q hq => hq⟩
  calc
    _ ≤ (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
    _ ≤ C*u^37 := hpE
    _ ≤ C*u^25 := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu.le hu1 (by norm_num)) hC.le

end CoulombAtom

namespace CoulombBarrier
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

lemma own_state_initial_barrier {Z N K : ℕ} {s ε k B c δ G : ℝ}
    (hn : InitialNumerics Z s ε G c δ) (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k) (hB : 0 < B)
    (hed : initialDensityConstant*ε^(6/5:ℝ) < 1/20)
    (hq : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBs : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    (hG : ∀ z, (canonicalRealPacket z)^2 ≤ G)
    (hN : PriceMinimizes (energy Z) (s^(-4:ℝ)) N) {F : fermionGraph N}
    (hF : OwnProbabilityTailTiltState Z (s^(-4:ℝ)) (ε*(Z:ℝ)^(-1/3:ℝ)) K
      (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*(ε*(Z:ℝ)^(-1/3:ℝ)))) δ F) :
    ∃ a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ,
      IsNuclearBarrier (physicalObservationLaw (graphRawLaw F) K)
        (originalQueryDensity F (ε*(Z:ℝ)^(-1/3:ℝ)) 0 c (ε*(Z:ℝ)^(-1/3:ℝ)) s)
        (Z:ℝ) k B (max B (32*ε^3)) (ε*(Z:ℝ)^(-1/3:ℝ)) 2
        (5184*(ε*(Z:ℝ)^(-1/3:ℝ))^32) a p := by
  let r₀ := ε*(Z:ℝ)^(-1/3:ℝ)
  have htail : TailTiltState Z (s^(-4:ℝ)) r₀ K (tailPolynomialThreshold r₀) δ F :=
    hF.to_tailTiltState hn.radius_pos (tailPolynomialThreshold_pos hn.radius_pos)
      (fun _ => tinyProbabilityFloor_le_polynomial (Nat.cast_nonneg Z) (by positivity))
  have hp := tailPolynomialThreshold_zero hn.radius_pos.le hn.radius_le K
  have hb : 3*(Z:ℝ)*s^(-4:ℝ)+
      dyadicUniformEventBudget ((2:ℝ)^(0:Fin (K+1)).val*r₀)
        (tailPolynomialThreshold r₀ (0 : Fin (K+1))) δ ≤ (Z:ℝ)^(7/3:ℝ) := by
    simp only [Fin.val_zero,pow_zero,one_mul,dyadicUniformEventBudget]
    rw [hp]
    dsimp only [r₀]
    linarith only [hn.budget]
  obtain ⟨a,p,hi⟩ := tail_initial_barrier hn.charge (Real.rpow_pos_of_pos hn.scale_pos _)
    hn.radius_pos hn.radius_le hn.scale_pos hn.scale_le hn.radius_scale hc hc1
    hε hε1 hk hB hn.radius_relation hed hq hBs hsub hN htail (0 : Fin (K+1))
    (tailPolynomialThreshold_pos hn.radius_pos 0) hp.le hb hn.interpolation
    canonicalRealPacket_smooth canonicalRealPacket_compact hG canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  exact ⟨_,_,hi.pullback (originalDatum_measurable _ _)⟩

end CoulombBarrier

open Set Filter MeasureTheory Metric
open scoped Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma exists_fullAnnulus_outward_calibration {κ B C : ℝ} (hκ : 0 ≤ κ) (hB : 0 < B)
    (hBC : B ≤ C) (hsub : 4*Real.pi*κ*Real.sqrt B ≤ 19/2) :
    ∃ M lam1 lam2 e ξ hl hh : ℝ, OutwardCalibration κ B C M lam1 lam2 e ξ hl hh ∧
      0 < ξ ∧ 16*ξ < hl ∧ hl ≤ hh := by
  let δ := barrierGap B
  have hδ : 0 < δ := barrierGap_pos hB
  let lam1 := δ/2
  let lam2 := δ/4
  have hl2 : 0 < lam2 := by dsimp only [lam2]; positivity
  let M := C/lam2+3
  have hC : 0 ≤ C := hB.le.trans hBC
  have hM : 2 < M := by dsimp only [M]; linarith [div_nonneg hC hl2.le]
  have hM0 : 0 < M := by linarith
  have hM4 : 0 < (2*M)^4 := by positivity
  have hpow : M ≤ M^4 := by
    have h2 : 1 ≤ M^2 := by nlinarith
    have h4 : M^2 ≤ M^4 := by nlinarith [sq_nonneg (M^2-1)]
    nlinarith
  have hcap : C/M^4 < lam2 := by
    apply (div_lt_iff₀ (pow_pos hM0 4)).mpr
    have hCM : C+3*lam2 = M*lam2 := by dsimp only [M]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hpow hl2.le]
  let e := min (δ/32) (B/(16*(2*M)^4))
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have he1 : e ≤ δ/32 := min_le_left _ _
  have he2 : e*(2*M)^4 ≤ B/16 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16*(2*M)^4)).mp (min_le_right (δ/32) (B/(16*(2*M)^4)))
    dsimp only [e]
    nlinarith
  refine ⟨M,lam1,lam2,e,δ/512,B/8,2*C,?_,by positivity,?_,by linarith⟩
  swap
  · dsimp [δ,barrierGap]
    norm_num [div_eq_mul_inv]
    linarith
  refine ⟨hκ,hB,hC,hBC,hM,by positivity,?_,?_,?_,?_,he,?_,hcap,?_,?_,hsub⟩
  · dsimp only [lam2]; linarith
  · dsimp only [lam2,lam1]; linarith
  · dsimp only [lam1,δ]; linarith [barrierGap_pos hB]
  · dsimp only [lam1,lam2]; linarith
  · linarith
  · linarith
  · linarith

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

theorem actual_outward_barrier_given_state_eventually_oai {c : ℝ} (hc : 0 < c)
    (hcL : c < (10*(100000:ℝ))⁻¹) :
    ∃ ε B C M D : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < B ∧ 2 < M ∧ 0 ≤ D ∧
      ∀ {ι : Type*} {l : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N K : ι → ℕ),
        (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s l (𝓝 0) →
        Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop →
        (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
        ∀ F : ∀ i, fermionGraph (N i),
          (∀ i, OwnProbabilityTailTiltState (Z i) ((s i)^(-4:ℝ)) (ε*(Z i:ℝ)^(-1/3:ℝ)) (K i)
            (fun j => tinyProbabilityFloor (Z i) ((2:ℝ)^j.val*(ε*(Z i:ℝ)^(-1/3:ℝ)))) 1 (F i)) →
          ∀ᶠ i in l, ∀ J : ℕ, J ≤ K i → (2:ℝ)^J*(ε*(Z i:ℝ)^(-1/3:ℝ)) ≤ s i →
            ∃ a p : (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) → TFSpace → ℝ,
              IsNuclearBarrier (physicalObservationLaw (graphRawLaw (F i)) (K i))
                (originalQueryDensity (F i) (ε*(Z i:ℝ)^(-1/3:ℝ)) J c (ε*(Z i:ℝ)^(-1/3:ℝ)) (s i))
                (Z i:ℝ) tfDensityCoefficient B C ((2:ℝ)^J*(ε*(Z i:ℝ)^(-1/3:ℝ))) M
                (5184*(s i)^32+D*(s i)^barrierErrorExponent) a p := by
  classical
  obtain ⟨ε,hε,hε1,hed,hq⟩ := exists_barrier_epsilon tfDensityCoefficient
  obtain ⟨B,hB,hBs,hsub⟩ := exists_barrier_B (k := tfDensityCoefficient) hε
  let C := max (max B (32*ε^3)) actualInverseCap
  have hBC : B ≤ C := (le_max_left B _).trans (le_max_left _ _)
  have hCinit : max B (32*ε^3) ≤ C := le_max_left _ _
  have hCcap : actualInverseCap ≤ C := le_max_right _ _
  obtain ⟨M,lam1,lam2,e,ξ,hl,hh,cal,hξ,hhl,hlh⟩ :=
    exists_fullAnnulus_outward_calibration tfDensityCoefficient_pos.le hB hBC hsub
  obtain ⟨A,hA,hgood⟩ := exists_actual_fullAnnulus_good_constant
    (B := 4*M) (by linarith [cal.M_large]) hc hcL hlh hξ hhl
  obtain ⟨Q,hQ,hmoment⟩ := actual_original_posterior_moment
    canonicalRealPacket_smooth.continuous canonicalRealPacket_support hc hcL
  let D := 32*Real.pi/3*Real.sqrt A*Real.sqrt Q
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨ε,B,C,M,D,hε,hε1,hB,cal.M_large,hD,?_⟩
  intro ι l Z s N K hZ hs hs0 hscale hN F hF
  let r : ι → ℝ := fun i => ε*(Z i:ℝ)^(-1/3:ℝ)
  have hZp (i) : 0 < (Z i:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hZ i))
  have hr (i) : 0 < r i := mul_pos hε (Real.rpow_pos_of_pos (hZp i) _)
  obtain ⟨z,hz⟩ := (canonicalRealPacket_smooth.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport
    canonicalRealPacket_compact.mul_left.norm
  let G : ℝ := ‖(canonicalRealPacket z)^2‖
  have hG (y : Space) : (canonicalRealPacket y)^2 ≤ G := by
    rw [←Real.norm_of_nonneg (sq_nonneg (canonicalRealPacket y))]
    exact hz y
  have hnum := initial_numerics_eventually Z s (Filter.Eventually.of_forall hZ) (Filter.Eventually.of_forall hs)
    hs0 hscale hε G c 1
  have hgood' := hgood (r₀ := r) (s := s) (Z := fun i => (Z i:ℝ))
    (lam := fun i => (s i)^(-4:ℝ)) (N := N) (K := K) (F := F)
    (by norm_num : (0:ℝ) ≤ 1) hs0 (Filter.Eventually.of_forall hr)
    (Filter.Eventually.of_forall (fun i => ⟨(Nat.cast_nonneg (Z i)),Real.rpow_pos_of_pos (hs i) _,hF i⟩))
  have hc1 : c ≤ 1/2 := by linarith
  filter_upwards [hnum,hgood'] with i hi hgi
  intro J hJK hJs
  obtain ⟨a,p,hinit⟩ := own_state_initial_barrier hi hc hc1 hε hε1.le
    tfDensityCoefficient_pos.le hB hed hq hBs hsub hG (hN i) (hF i)
  have hm (j : ℕ) {v : ℝ} (hv : r i ≤ v) (hvs : v ≤ s i) (y : Space)
      (hy : v ≤ ‖y‖) (hy' : ‖y‖ ≤ 2*v) :
      (∫ q, (originalQueryDensity (F i) (r i) j c (r i) (s i) q y)^2
        ∂physicalObservationLaw (graphRawLaw (F i)) (K i)) ≤ Q*v^(-12-6*masterExponent) :=
    hmoment (Nat.cast_nonneg (Z i)) (Real.rpow_pos_of_pos (hs i) _) (hN i) (F i)
      (hF i).1 (hF i).2.1 (fun k => dyadicObservationWidth (r i) k) j
      (hr i) (hs i) hi.scale_le hv hvs y hy hy'
  obtain ⟨a',p',hnew⟩ := actual_finite_barrier_from_good (Nat.cast_nonneg (Z i))
    (Real.rpow_pos_of_pos (hs i) _) (hr i) (hs i) hi.scale_le hi.radius_scale hc hcL
    (hN i) (hF i).1 (hF i).2.1 cal hCcap hA.le hQ hm (hinit.mono_cap hCinit) hgi J hJK hJs
  refine ⟨a',p',?_⟩
  rw [max_eq_right cal.M_large.le] at hnew
  exact hnew.mono_budget (add_le_add (initial_budget_le_final_radius (hr i).le hi.radius_scale) le_rfl)

end CoulombBarrier

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually_oai.{u_1} := @OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually_oai.{u_1}
