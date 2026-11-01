-- Prove2me | solution 1 for OAI.CircleDomainRigidity.planarSobolevCoarea
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:43:03.012973+00:00
-- url     : https://prove2.me/submissions/285712f5-af84-4014-827f-b17db92e7479

import Mathlib
import Definitions.Def_Q146C004
import Definitions.Def_Q146C005

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_AverageOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary mean-oscillation bounds used for Sobolev square averages. -/
open Set Function MeasureTheory

theorem _root_.MeasureTheory.average_add {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ⨍ a, (f + g) a ∂μ = ⨍ a, f a ∂μ + ⨍ a, g a ∂μ := by
  simp only [average_eq, Pi.add_apply, integral_add hf hg, smul_add]
theorem _root_.MeasureTheory.average_sub {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ⨍ a, (f - g) a ∂μ = ⨍ a, f a ∂μ - ⨍ a, g a ∂μ := by
  simp only [average_eq, Pi.sub_apply, integral_sub hf hg, smul_sub]
theorem _root_.MeasureTheory.average_const_mul {α 𝕜 : Type*} [MeasurableSpace α] (μ : Measure α)
    [RCLike 𝕜] (r : 𝕜) (f : α → 𝕜) : ⨍ a, r * f a ∂μ = r * ⨍ a, f a ∂μ :=
  integral_const_mul ..
theorem _root_.MeasureTheory.average_nonneg {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] [ClosedIciTopology E] {f : α → E} (hf : 0 ≤ f) : 0 ≤ ⨍ a, f a ∂μ :=
  integral_nonneg hf
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma average_mono_real {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    (⨍ x, f x ∂μ) ≤ ⨍ x, g x ∂μ := by
  rw [average_eq, average_eq]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg) (by positivity)

lemma abs_average_le_average_abs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : |⨍ x, f x ∂μ| ≤ ⨍ x, |f x| ∂μ := by
  simpa only [average, Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (f := f) (μ := (μ univ)⁻¹ • μ))

lemma abs_sub_average_le_average_abs_sub {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ}
    (hf : Integrable f μ) (a : ℝ) :
    |a-(⨍ x, f x ∂μ)| ≤ ⨍ x, |a-f x| ∂μ := by
  have he : (⨍ x, a-f x ∂μ) = a-(⨍ x, f x ∂μ) := by
    have hh := average_sub (integrable_const a : Integrable (fun _ : X => a) μ) hf
    simpa only [Pi.sub_apply, average_const] using hh
  rw [← he]
  exact abs_average_le_average_abs μ _

lemma abs_sub_average_le_of_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ}
    (hf : Integrable f μ) (a C : ℝ) (h : ∀ᵐ x ∂μ, |a-f x| ≤ C) :
    |a-(⨍ x, f x ∂μ)| ≤ C := by
  apply (abs_sub_average_le_average_abs_sub hf a).trans
  simpa only [Pi.sub_apply, average_const] using
    average_mono_real ((integrable_const a).sub hf).abs (integrable_const C) h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevJacobianLocality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Sobolev replacements agreeing outside a closed region have
the same Jacobian integral over that region. This is the interior
replacement step in the conductivity area computation. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakGradient_eq_on_open {u v : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hv : DeGiorgi.MemW1pWitness 2 v univ)
    {U : Set EuclideanPlane} (hU : IsOpen U) (heq : EqOn u v U) (i : Fin 2) :
    (fun x => hu.weakGrad x i) =ᵐ[volume.restrict U] fun x => hv.weakGrad x i := by
  let huU := hu.restrict hU (subset_univ U)
  let hvU := hv.restrict hU (subset_univ U)
  have hh := weakPartial_congrOn hU (huU.isWeakGrad i) heq
  exact hh.ae_eq hU (hvU.isWeakGrad i)
    ((huU.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hvU.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactWeakDerivativeIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Sobolev perturbations contribute zero total first derivative.
The support and integrability of the actual weak derivative are proved,
so the boundary-flux replacement does not assume an unproved trace fact. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_weakGradient_zero_off {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ x ∂volume, x ∉ tsupport u → hu.weakGrad x i = 0 := by
  have heq : EqOn u (fun x => (0 : ℝ) * u x) (tsupport u)ᶜ := by
    intro x hx
    simp only [zero_mul]
    exact image_eq_zero_of_notMem_tsupport hx
  have hh := weakGradient_eq_on_open hu (hu.smul 0) isClosed_closure.isOpen_compl heq i
  have hh' := (ae_restrict_iff' isClosed_closure.measurableSet.compl).mp hh
  filter_upwards [hh'] with x hx hxU
  simpa only [DeGiorgi.MemW1pWitness.smul, zero_smul, PiLp.zero_apply] using hx hxU

 theorem compact_weakGradient_integrable {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hs : HasCompactSupport u) (i : Fin 2) :
    Integrable (fun x => hu.weakGrad x i) := by
  let : IsFiniteMeasure (volume.restrict (tsupport u)) :=
    isFiniteMeasure_restrict.mpr hs.isCompact.measure_lt_top.ne
  have hG : MemLp (fun x => hu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp i
  have hi : IntegrableOn (fun x => hu.weakGrad x i) (tsupport u) :=
    (hG.restrict _).integrable (by norm_num)
  exact hi.integrable_of_ae_notMem_eq_zero (compact_weakGradient_zero_off hu i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar coarea and its finite-energy consequences

The planar scalar coarea identities specialize
Federer, *Geometric Measure Theory*, Springer (1969), §3.2.11 (coarea)
and §3.2.12 (weighted coarea),
DOI: 10.1007/978-3-642-62010-2. For a `C¹` real function on an open
subset of the Euclidean plane, the integral of the one-dimensional
Hausdorff measures of its fibers equals the integral of the norm of its
differential. The locally Lipschitz version follows from the stated
Lipschitz coarea theorem by a countable relatively compact covering.

`PlanarScalarCoarea` and `WeightedPlanarScalarCoarea` express these
specializations as propositions. They require neither finite energy nor
topological conclusions. The length function need only be Lebesgue
measurable; Borel measurability is unnecessary.

Finite area and finite squared differential imply finite integrated
length, and integer periodization
gives finite physical length for almost every circle-valued level.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace CircleDomainRigidity

/-- The scalar fibers are measurable even though the function is only
assumed continuous on its open domain. -/
theorem measurableSet_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (t : ℝ) :
    MeasurableSet (D ∩ {z | f z = t}) := by
  classical
  have hm : Measurable (D.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ {z | f z = t} =
      D ∩ (D.piecewise f (fun _ => 0)) ⁻¹' {t} := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  rw [heq]
  exact hD.measurableSet.inter (hm (measurableSet_singleton t))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoordinateLines
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate lines in the actual Euclidean Sobolev plane. Their
one-dimensional derivatives and total energies are the physical partials. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physicalCoordinateLine_contDiff (i : Fin 2) (y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCoordinateLine i y) := by
  unfold physicalCoordinateLine
  split <;> fun_prop

 theorem physicalCoordinateLine_deriv {f : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) (y x : ℝ) :
    deriv (fun t => f (physicalCoordinateLine i y t)) x =
      fderiv ℝ f (physicalCoordinateLine i y x) (EuclideanSpace.single i 1) := by
  have h0 := (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h1 := (hasDerivAt_const x y).prodMk (hasDerivAt_id x)
  have he0 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt x h0
  have he1 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt x h1
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,
      show euclideanPlaneCoordinates.symm (1,0) = EuclideanSpace.single (0 : Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 0] using
      ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt x he0).deriv
  · simpa [physicalCoordinateLine,Function.comp_def,
      show euclideanPlaneCoordinates.symm (0,1) = EuclideanSpace.single (1 : Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 1] using
      ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt x he1).deriv

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalLineFubini
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini on the two physical coordinate line families. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physicalCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (fun p : ℝ × ℝ => physicalCoordinateLine i p.1 p.2)
      (volume.prod volume) volume := by
  have he : MeasurePreserving euclideanPlaneCoordinates.symm (volume.prod volume) volume := by
    simpa only [← Measure.volume_eq_prod] using euclideanPlaneCoordinates_symm_measurePreserving
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,Prod.swap] using
      he.comp (Measure.measurePreserving_swap (μ := volume) (ν := volume))
  · simpa [physicalCoordinateLine] using he

 theorem ae_ae_physicalCoordinateLine {p : EuclideanPlane → Prop}
    (hp : ∀ᵐ z ∂volume, p z) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ x ∂volume, p (physicalCoordinateLine i y x) := by
  exact Measure.ae_ae_of_ae_prod ((physicalCoordinatePlane_measurePreserving i).quasiMeasurePreserving.ae hp)

 theorem memLp_physicalCoordinateLine_ae {P : EuclideanPlane → ℝ}
    (hP : Measurable P) (hL : MemLp P 2 volume) (i : Fin 2) :
    ∀ᵐ y ∂volume, MemLp (fun x => P (physicalCoordinateLine i y x)) 2 volume := by
  have hs := (physicalCoordinatePlane_measurePreserving i).integrable_comp_of_integrable hL.integrable_sq
  filter_upwards [hs.prod_right_ae] with y hy
  exact (memLp_two_iff_integrable_sq (hP.comp (physicalCoordinateLine_contDiff i y).continuous.measurable).aestronglyMeasurable).mpr hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2Series
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise sum of the cutoff differential norms is itself in L2,
with the sum of their L2 norms as a bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_series_of_summable_norms {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (g : ℕ → X → ℝ)
    (hg : ∀ n, MemLp (g n) 2 μ)
    (hs : Summable (fun n => (eLpNorm (g n) 2 μ).toReal)) :
    MemLp (fun z => ∑' n, g n z) 2 μ ∧
      (eLpNorm (fun z => ∑' n, g n z) 2 μ).toReal ≤
        ∑' n, (eLpNorm (g n) 2 μ).toReal := by
  let F : ℕ → Lp ℝ 2 μ := fun n => (hg n).toLp (g n)
  have hnorm : Summable (fun n => ‖F n‖) := by
    simpa only [F, Lp.norm_toLp] using hs
  have hfinite : (∑' n, ‖F n‖ₑ) ≠ (⊤ : ℝ≥0∞) := by
    have hh := hs.tsum_ofReal_lt_top
    have he (n : ℕ) : ENNReal.ofReal (eLpNorm (g n) 2 μ).toReal = eLpNorm (g n) 2 μ :=
      ENNReal.ofReal_toReal (hg n).eLpNorm_ne_top
    simp_rw [he] at hh
    simpa only [F, Lp.enorm_toLp] using hh.ne
  have hvalues : ∀ᵐ z ∂μ, ∀ n, F n z = g n z :=
    ae_all_iff.mpr (fun n => (hg n).coeFn_toLp)
  have hae : (⇑(∑' n, F n) : X → ℝ) =ᵐ[μ] (fun z => ∑' n, g n z) := by
    filter_upwards [Lp.coeFn_tsum hfinite, hvalues] with z hz hv
    rw [hz]
    exact tsum_congr hv
  refine ⟨(Lp.memLp (∑' n, F n)).ae_eq hae, ?_⟩
  rw [← eLpNorm_congr_ae hae, ← Lp.norm_def]
  simpa only [F, Lp.norm_toLp] using norm_tsum_le_tsum_norm hnorm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2DominatingSubsequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L² convergence admits a cofinal subsequence with one L²
pointwise majorant. This will pass smooth line payments to a continuous
Sobolev limit without assuming an ACL representative theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_L2_dominating_subsequence {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 2 μ) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (P : X → ℝ), Tendsto σ atTop atTop ∧ Measurable P ∧
      (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧ (∀ᵐ x ∂μ, ∀ n, |f (σ n) x| ≤ P x) := by
  let δ := fun n : ℕ => (1/2:ℝ)^n
  have hδ (n : ℕ) : 0 < δ n := pow_pos (by norm_num) n
  have hδs : Summable δ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun n => (eLpNorm (fun x => f n x-g x) 2 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp hlim
  have hchoose (n : ℕ) : ∃ k, n ≤ k ∧ (eLpNorm (fun x => f k x-g x) 2 μ).toReal ≤ δ n := by
    obtain ⟨k,hk,hke⟩ := ((eventually_ge_atTop n).and (ht.eventually (gt_mem_nhds (hδ n)))).exists
    exact ⟨k,hk,hke.le⟩
  choose σ hσ hb using hchoose
  have hσt : Tendsto σ atTop atTop := tendsto_atTop_mono hσ tendsto_id
  let e := fun n x => f (σ n) x-g x
  have he (n : ℕ) : MemLp (e n) 2 μ := (hf _).sub hg
  have hes : Summable (fun n => (eLpNorm (e n) 2 μ).toReal) :=
    hδs.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hb
  have hef : (∑' n, eLpNorm (e n) 2 μ) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) hδs.tsum_ofReal_lt_top
    rw [← ENNReal.ofReal_toReal (he n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hser := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2) (fun n => (he n).1) hef
  have hn : Summable (fun n => (eLpNorm (fun x => ‖e n x‖) 2 μ).toReal) := by
    simpa only [eLpNorm_norm _] using hes
  have hsum := (l2_series_of_summable_norms (fun n x => ‖e n x‖) (fun n => (he n).norm) hn).1
  let Q := fun x => ‖g x‖+∑' n, ‖e n x‖
  have hQ : MemLp Q 2 μ := hg.norm.add hsum
  have hQ0 (x : X) : 0 ≤ Q x := add_nonneg (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _))
  let P := fun x => max (hQ.aestronglyMeasurable.mk Q x) 0
  have hPQ : P =ᵐ[μ] Q := by
    filter_upwards [hQ.aestronglyMeasurable.ae_eq_mk] with x hx
    change max (hQ.aestronglyMeasurable.mk Q x) 0 = Q x
    rw [← hx,max_eq_left (hQ0 x)]
  refine ⟨σ,P,hσt,hQ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const,
    (fun _ => le_max_right _ _),hQ.ae_eq hPQ.symm,?_⟩
  filter_upwards [hPQ,hser] with x hx hxs
  intro n
  rw [hx]
  have heq : f (σ n) x = g x+e n x := by dsimp only [e] <;> ring
  calc
    _ = ‖f (σ n) x‖ := Real.norm_eq_abs _ |>.symm
    _ ≤ ‖g x‖+‖e n x‖ := by rw [heq]; exact norm_add_le _ _
    _ ≤ Q x := by
      dsimp only [Q]
      exact add_le_add_right (hxs.le_tsum n (fun _ _ => norm_nonneg _)) _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevTypicalLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous compact Sobolev function admits an actual L² payment
for all intervals on almost every coordinate line. Strong mollification
and a summably convergent subsequence supply the payment. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_line_increment_payment_ae {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {x y : ℝ}
    (hg : IntervalIntegrable g volume x y)
    (hb : ∀ᵐ t ∂volume, |deriv f t| ≤ g t) :
    |f x-f y| ≤ ∫ t in uIoc x y, g t := by
  have hi : IntervalIntegrable (deriv f) volume x y :=
    hf.continuous_deriv_one.intervalIntegrable x y
  have he := intervalIntegral.integral_deriv_eq_sub
    (fun z (_ : z ∈ uIcc y x) => hf.differentiable_one z) hi.symm
  rw [← he,← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  rw [uIoc_comm y x]
  apply integral_mono_ae hi.norm.def' hg.def'
  exact ae_restrict_of_ae hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DominatedLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing one-dimensional derivative payment to a pointwise limit,
with the actual almost-everywhere derivative limit as payment density. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma line_payment_of_dominated_derivatives
    {f : ℕ → ℝ → ℝ} {u g P : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ 1 (f n))
    (hu : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (u x)))
    (hP : LocallyIntegrable P volume)
    (hdom : ∀ᵐ x ∂volume, ∀ n, |deriv (f n) x| ≤ P x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => deriv (f n) x) atTop (𝓝 (g x))) :
    ∀ x z : ℝ, IntervalIntegrable g volume x z ∧
      |u x-u z| ≤ ∫ t in uIoc x z, |g t| := by
  have hgm : AEStronglyMeasurable g volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hf n).continuous_deriv_one.aestronglyMeasurable) hlim
  have hgb : ∀ᵐ t ∂volume, ‖g t‖ ≤ P t := by
    filter_upwards [hdom, hlim] with t ht hl
    exact le_of_tendsto hl.norm (Eventually.of_forall fun n => by simpa only [Real.norm_eq_abs] using ht n)
  intro x z
  have hPi : IntegrableOn P (uIoc x z) volume :=
    (hP.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hgi : IntegrableOn g (uIoc x z) volume :=
    hPi.mono' hgm.restrict (ae_restrict_of_ae hgb)
  refine ⟨intervalIntegrable_iff.mpr hgi, ?_⟩
  have hi : Tendsto (fun n => ∫ t in uIoc x z, |deriv (f n) t|) atTop
      (𝓝 (∫ t in uIoc x z, |g t|)) := by
    apply tendsto_integral_of_dominated_convergence P
      (fun n => (hf n).continuous_deriv_one.abs.aestronglyMeasurable.restrict) hPi
    · intro n
      filter_upwards [ae_restrict_of_ae hdom] with t ht
      simpa only [Real.norm_eq_abs, abs_abs] using ht n
    · filter_upwards [ae_restrict_of_ae hlim] with t ht
      exact ht.abs
  have hpay (n : ℕ) : |f n x-f n z| ≤ ∫ t in uIoc x z, |deriv (f n) t| :=
    smooth_line_increment_payment_ae (hf n)
      ((hf n).continuous_deriv_one.abs.intervalIntegrable x z)
      (Eventually.of_forall fun _ => le_rfl)
  exact le_of_tendsto_of_tendsto ((hu x).sub (hu z)).abs hi (Eventually.of_forall hpay)


lemma line_integral_eq_sub_of_dominated_derivatives
    {f : ℕ → ℝ → ℝ} {u g P : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ 1 (f n))
    (hu : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (u x)))
    (hP : LocallyIntegrable P volume)
    (hdom : ∀ᵐ x ∂volume, ∀ n, |deriv (f n) x| ≤ P x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => deriv (f n) x) atTop (𝓝 (g x))) :
    ∀ x z : ℝ, (∫ t in x..z, g t) = u z-u x := by
  intro x z
  wlog horder : x ≤ z generalizing x z
  · have he := this z x (le_of_not_ge horder)
    rw [intervalIntegral.integral_symm z x, he]
    ring
  have hPi : IntegrableOn P (Ioc x z) volume :=
    (hP.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hi : Tendsto (fun n => ∫ t in Ioc x z, deriv (f n) t) atTop
      (𝓝 (∫ t in Ioc x z, g t)) := by
    apply tendsto_integral_of_dominated_convergence P
      (fun n => (hf n).continuous_deriv_one.aestronglyMeasurable.restrict) hPi
    · intro n
      filter_upwards [ae_restrict_of_ae hdom] with t ht
      simpa only [Real.norm_eq_abs] using ht n
    · exact ae_restrict_of_ae hlim
  have heq (n : ℕ) : (∫ t in Ioc x z, deriv (f n) t) = f n z-f n x := by
    rw [← intervalIntegral.integral_of_le horder]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ => (hf n).differentiable_one _) ((hf n).continuous_deriv_one.intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le horder]
  exact tendsto_nhds_unique hi (by simpa only [heq] using (hu z).sub (hu x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FixedCapacityCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoffs for the scalar graph-capacity argument. Their
bounds are independent of the function, graph point, and chosen scale. -/
open Set Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma euclideanPlane_norm_le_two_of_coordinate_unit {x : EuclideanPlane}
    (hx : euclideanPlaneCoordinates x ∈ closedBall 0 1) : ‖x‖ ≤ 2 := by
  have hp : |x 0| ≤ 1 ∧ |x 1| ≤ 1 := by
    simpa only [mem_closedBall, euclideanPlaneCoordinates_apply, Prod.dist_eq,
      Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero, max_le_iff] using hx
  have he : ‖x‖^2 = (x 0)^2+(x 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  have h0 : (x 0)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (x 0)) zero_le_one).mpr hp.1
  have h1 : (x 1)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (x 1)) zero_le_one).mpr hp.2
  nlinarith [norm_nonneg x]

lemma scalarCapacityBump_one {t : ℝ} (ht : |t| ≤ 1) : scalarCapacityBump t = 1 := by
  apply scalarCapacityBump.one_of_mem_closedBall
  simpa only [scalarCapacityBump, mem_closedBall, Real.dist_eq, sub_zero] using ht

lemma spatialCapacityBump_one {x : EuclideanPlane}
    (hx : euclideanPlaneCoordinates x ∈ closedBall 0 1) : spatialCapacityBump x = 1 := by
  apply spatialCapacityBump.one_of_mem_closedBall
  simpa only [spatialCapacityBump, mem_closedBall, dist_zero_right] using
    euclideanPlane_norm_le_two_of_coordinate_unit hx

lemma scalarCapacityBump_zero {t : ℝ} (ht : 2 < |t|) :
    scalarCapacityBump t = 0 ∧ deriv scalarCapacityBump t = 0 := by
  have hn : t ∉ tsupport (scalarCapacityBump : ℝ → ℝ) := by
    rw [scalarCapacityBump.tsupport_eq]
    simpa only [scalarCapacityBump, mem_closedBall, Real.dist_eq, sub_zero, not_le] using ht
  exact ⟨image_eq_zero_of_notMem_tsupport hn,
    image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))⟩

lemma spatialCapacityBump_zero {x : EuclideanPlane} (hx : 4 < ‖x‖) :
    spatialCapacityBump x = 0 ∧ fderiv ℝ spatialCapacityBump x = 0 := by
  have hn : x ∉ tsupport (spatialCapacityBump : EuclideanPlane → ℝ) := by
    rw [spatialCapacityBump.tsupport_eq]
    simpa only [spatialCapacityBump, mem_closedBall, dist_zero_right, not_le] using hx
  exact ⟨image_eq_zero_of_notMem_tsupport hn,
    image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_fderiv_subset ℝ h))⟩

lemma exists_capacity_cutoff_derivative_bound : ∃ C : ℝ, 0 ≤ C ∧
    (∀ t, ‖deriv scalarCapacityBump t‖ ≤ C) ∧
    (∀ x, ‖fderiv ℝ spatialCapacityBump x‖ ≤ C) := by
  obtain ⟨A,hA⟩ := ((scalarCapacityBump.contDiff : ContDiff ℝ 1 (scalarCapacityBump : ℝ → ℝ)).continuous_deriv le_rfl).bounded_above_of_compact_support
    scalarCapacityBump.hasCompactSupport.deriv
  obtain ⟨B,hB⟩ := ((spatialCapacityBump.contDiff : ContDiff ℝ 1 (spatialCapacityBump : EuclideanPlane → ℝ)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (spatialCapacityBump.hasCompactSupport.fderiv ℝ)
  exact ⟨max 0 (max A B),le_max_left _ _,
    fun t => (hA t).trans ((le_max_left _ _).trans (le_max_right _ _)),
    fun x => (hB x).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_EnergyBallCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable small-cost ball cover obtained from a local energy payment.
Only the plane's sup metric and the usual fourfold Vitali enlargement are used. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma energy_ball_cover {A : Set (ℝ × ℝ)} {r : (ℝ × ℝ) → ℝ}
    (hr : ∀ x ∈ A, 0 < r x) (hsmall : ∀ x ∈ A, r x ≤ 1)
    (μ : Measure (ℝ × ℝ)) (C : ℝ≥0∞)
    (hpay : ∀ x ∈ A, ENNReal.ofReal (r x) ≤ C * μ (closedBall x (r x))) :
    ∃ U : Set (ℝ × ℝ), U ⊆ A ∧ U.Countable ∧
      A ⊆ ⋃ x : U, closedBall (x : ℝ × ℝ) (4*r x) ∧
      (∑' x : U, ENNReal.ofReal (r x)) ≤ C * μ univ := by
  obtain ⟨U,hUA,hdj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    A id r 1 hsmall 4 (by norm_num)
  have hc : U.Countable :=
    (hdj.mono (fun _ => ball_subset_closedBall)).countable_of_isOpen
      (fun _ _ => isOpen_ball) (fun x hx => nonempty_ball.mpr (hr x (hUA hx)))
  have : Countable U := hc.to_subtype
  refine ⟨U,hUA,hc,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨⟨y,hy⟩, hxy (mem_closedBall_self (hr x hx).le)⟩
  · calc
      _ ≤ ∑' x : U, C * μ (closedBall (x : ℝ × ℝ) (r x)) :=
        ENNReal.tsum_le_tsum (fun x => hpay x (hUA x.property))
      _ = C * μ (⋃ x : U, closedBall (x : ℝ × ℝ) (r x)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion]
        · exact hdj.subtype _ _
        · exact fun _ => isClosed_closedBall.measurableSet
      _ ≤ C * μ univ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VerticalCylinderCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A narrow vertical cylinder has a finite small-diameter cover whose
quadratic cost is controlled by its height times its base radius. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma vertical_cylinder_cover (c : ℝ × ℝ) (t : ℝ) {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hdR : d ≤ 4*R) :
    ∃ (N : ℕ) (T : Fin N → Set ((ℝ × ℝ) × ℝ)),
      closedBall c d ×ˢ Icc (t-R) (t+R) ⊆ ⋃ i, T i ∧
      (∀ i, ediam (T i) ≤ ENNReal.ofReal (2*d)) ∧
      (N : ℝ)*(2*d)^2 ≤ 32*R*d := by
  let N := Nat.floor (2*R/d)+1
  let T : Fin N → Set ((ℝ × ℝ) × ℝ) := fun i =>
    closedBall c d ×ˢ closedBall (t-R+(i:ℕ)*d) d
  refine ⟨N,T,?_,?_,?_⟩
  · rintro ⟨x,y⟩ ⟨hx,hy⟩
    let w := (y-(t-R))/d
    have hw0 : 0 ≤ w := div_nonneg (by linarith [hy.1]) hd.le
    have hwR : w ≤ 2*R/d := (div_le_div_iff_of_pos_right hd).mpr (by linarith [hy.2])
    let k := Nat.floor w
    have hk : k < N := Nat.lt_succ_of_le (Nat.floor_mono hwR)
    apply mem_iUnion.mpr
    refine ⟨⟨k,hk⟩,hx,?_⟩
    change dist y (t-R+(k:ℝ)*d) ≤ d
    rw [Real.dist_eq]
    apply abs_le.mpr
    have hlo := (le_div_iff₀ hd).mp (Nat.floor_le hw0)
    have hhi := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one w)
    dsimp only [w, k] at hlo hhi ⊢
    constructor <;> nlinarith
  · intro i
    change ediam (closedBall c d ×ˢ closedBall (t-R+(i:ℕ)*d) d) ≤ _
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    rw [Prod.dist_eq]
    apply max_le
    · have htri := dist_triangle x.1 c y.1
      rw [dist_comm c y.1] at htri
      linarith [mem_closedBall.mp hx.1, mem_closedBall.mp hy.1]
    · have htri := dist_triangle x.2 (t-R+(i:ℕ)*d) y.2
      rw [dist_comm (t-R+(i:ℕ)*d) y.2] at htri
      linarith [mem_closedBall.mp hx.2, mem_closedBall.mp hy.2]
  · have hN : (N : ℝ) ≤ 2*R/d+1 := by
      dsimp only [N]
      rw [Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.floor_le (div_nonneg (show 0 ≤ 2*R by positivity) hd.le)) le_rfl
    have hNd : (N : ℝ)*d ≤ 2*R+d := by
      have h := mul_le_mul_of_nonneg_right hN hd.le
      field_simp [hd.ne'] at h
      nlinarith
    nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GraphCylinderCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn a countable base-ball cover of a scalar level slab into an
explicit small-diameter graph cover, retaining the quadratic cost. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma graph_cover_of_base_balls {U : Set (ℝ × ℝ)} (hU : U.Countable)
    (r : (ℝ × ℝ) → ℝ) {R : ℝ} (hR : 0 < R)
    (hr : ∀ x ∈ U, 0 < r x ∧ r x ≤ 4*R)
    {A : Set (ℝ × ℝ)} (hcover : A ⊆ ⋃ x : U, closedBall (x : ℝ × ℝ) (r x))
    (f : (ℝ × ℝ) → ℝ) (t : ℝ) (hband : ∀ x ∈ A, f x ∈ Icc (t-R) (t+R)) :
    ∃ (N : U → ℕ) (T : (x : U) → Fin (N x) → Set ((ℝ × ℝ) × ℝ)),
      (fun x => (x,f x)) '' A ⊆ ⋃ x : U, ⋃ j : Fin (N x), T x j ∧
      (∀ x j, ediam (T x j) ≤ ENNReal.ofReal (8*R)) ∧
      (∑' x : U, ∑' j : Fin (N x), ediam (T x j)^2) ≤
        32*ENNReal.ofReal R * ∑' x : U, ENNReal.ofReal (r x) := by
  have : Countable U := hU.to_subtype
  choose N T hT hdiam hcost using fun x : U =>
    vertical_cylinder_cover (x : ℝ × ℝ) t (hr x x.property).1 hR (hr x x.property).2
  refine ⟨N,T,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := mem_iUnion.mp (hcover hx)
    have htmem : (x,f x) ∈ ⋃ j, T y j := hT y ⟨hy,hband x hx⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp htmem
    exact mem_iUnion.mpr ⟨y,mem_iUnion.mpr ⟨j,hj⟩⟩
  · intro x j
    exact (hdiam x j).trans (ENNReal.ofReal_le_ofReal (by linarith [(hr x x.property).2]))
  · have hbound (x : U) : (∑' j : Fin (N x), ediam (T x j)^2) ≤
        32*ENNReal.ofReal R*ENNReal.ofReal (r x) := by
      calc
        _ ≤ ∑' _j : Fin (N x), (ENNReal.ofReal (2*r x))^2 :=
          ENNReal.tsum_le_tsum (fun j => pow_le_pow_left' (hdiam x j) 2)
        _ = ENNReal.ofReal ((N x : ℝ)*(2*r x)^2) := by
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg (N x)),
            ENNReal.ofReal_pow (mul_nonneg (by norm_num) (hr x x.property).1.le)]
          simp
        _ ≤ ENNReal.ofReal (32*R*r x) := ENNReal.ofReal_le_ofReal (hcost x)
        _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
          norm_num
    exact (ENNReal.tsum_le_tsum hbound).trans_eq ENNReal.tsum_mul_left

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AverageSubsets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compare a smaller-set average to a larger-set average by mean oscillation. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma abs_average_sub_average_le_integral {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s t : Set X} (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ∞)
    {f : X → ℝ} (hf : IntegrableOn f t μ) :
    |(⨍ x in s, f x ∂μ)-(⨍ x in t, f x ∂μ)| ≤
    (μ.real s)⁻¹ * (∫ x in t, |f x-(⨍ y in t, f y ∂μ)| ∂μ) := by
  have hsf : μ s ≠ ∞ := ne_top_of_le_ne_top ht (measure_mono hst)
  let : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hsf
  let : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.mpr ht
  let : NeZero (μ.restrict s) := ⟨by simpa using hs⟩
  have he : (⨍ x in s, f x-(⨍ y in t, f y ∂μ) ∂μ) =
      (⨍ x in s, f x ∂μ)-(⨍ y in t, f y ∂μ) := by
    simpa only [Pi.sub_apply, average_const] using
      average_sub (hf.mono_set hst) (integrable_const (⨍ y in t, f y ∂μ))
  rw [← he]
  apply (abs_average_le_average_abs (μ.restrict s) _).trans
  rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_mono_set (hf.sub (integrable_const _)).abs
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall fun _ hx => hst hx))
    (inv_nonneg.mpr measureReal_nonneg)

lemma abs_average_sub_average_le_oscillation {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s t : Set X} (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ∞)
    {f : X → ℝ} (hf : IntegrableOn f t μ) {C : ℝ}
    (hC : μ.real t ≤ C * μ.real s) :
    |(⨍ x in s, f x ∂μ)-(⨍ x in t, f x ∂μ)| ≤
      C*(⨍ x in t, |f x-(⨍ y in t, f y ∂μ)| ∂μ) := by
  have hsf : μ s ≠ ∞ := ne_top_of_le_ne_top ht (measure_mono hst)
  have hspos : 0 < μ.real s := lt_of_le_of_ne measureReal_nonneg
    ((measureReal_ne_zero_iff hsf).mpr hs).symm
  let : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.mpr ht
  have he : (∫ x in t, |f x-(⨍ y in t, f y ∂μ)| ∂μ) =
      μ.real t * (⨍ x in t, |f x-(⨍ y in t, f y ∂μ)| ∂μ) := by
    simpa only [measureReal_restrict_apply_univ, smul_eq_mul] using
      (measure_smul_average (μ.restrict t) (fun x => |f x-(⨍ y in t, f y ∂μ)|)).symm
  apply (abs_average_sub_average_le_integral hst hs ht hf).trans
  rw [he, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (average_nonneg fun _ => abs_nonneg _)
  exact (inv_mul_le_iff₀ hspos).mpr (by simpa only [mul_comm] using hC)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2DominatedAeSubsequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L² convergence has a cofinal subsequence with both a common
L² majorant and pointwise almost-everywhere convergence. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_L2_dominated_ae_subsequence {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 2 μ) atTop (𝓝 0)) :
    ∃ (ρ : ℕ → ℕ) (P : X → ℝ), Tendsto ρ atTop atTop ∧ Measurable P ∧
      (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧
      (∀ᵐ x ∂μ, (∀ n, |f (ρ n) x| ≤ P x) ∧
        Tendsto (fun n => f (ρ n) x) atTop (𝓝 (g x))) := by
  obtain ⟨σ, P, hσ, hP, hP0, hPL, hdom⟩ := exists_L2_dominating_subsequence hf hg hlim
  have hmeasure : TendstoInMeasure μ (fun n => f (σ n)) atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (hf := fun n => (hf (σ n)).aestronglyMeasurable) (hg := hg.aestronglyMeasurable) (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hlim.comp hσ)
  obtain ⟨τ, hτ, hconv⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨σ ∘ τ, P, hσ.comp hτ.tendsto_atTop, hP, hP0, hPL, ?_⟩
  filter_upwards [hdom, hconv] with x hxd hxc
  exact ⟨fun n => hxd (τ n), hxc⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExactSobolevLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous compact W1,2 function satisfies the coordinate-line
fundamental inequality with its actual distributional gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exact_sobolev_line_payment {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ x z : ℝ,
      IntervalIntegrable (fun t => W.weakGrad (physicalCoordinateLine i y t) i) volume x z ∧
      |u (physicalCoordinateLine i y x)-u (physicalCoordinateLine i y z)| ≤
        ∫ t in uIoc x z, |W.weakGrad (physicalCoordinateLine i y t) i| := by
  have hg : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  obtain ⟨ρ, P, hρ, hP, hP0, hPL, hdom⟩ := exists_L2_dominated_ae_subsequence
    (fun n => planarMollification_partial_memLp W hs n i) hg
    (planarMollification_tendsto_gradient_L2 W i)
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using W.memLp
  have hfn (n : ℕ) : ContDiff ℝ 1 (planarMollification u (ρ n)) :=
    (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) (ρ n)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  filter_upwards [memLp_physicalCoordinateLine_ae hP hPL i,
    ae_ae_physicalCoordinateLine hdom i] with y hy hd
  apply line_payment_of_dominated_derivatives
    (fun n => (hfn n).comp ((physicalCoordinateLine_contDiff i y).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
    (fun t => (planarMollification_tendsto_of_continuous hu _).comp hρ)
    (hy.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  · filter_upwards [hd] with t ht
    intro n
    simpa only [Function.comp_def, physicalCoordinateLine_deriv (hfn n)] using ht.1 n
  · filter_upwards [hd] with t ht
    simpa only [Function.comp_def, physicalCoordinateLine_deriv (hfn _)] using ht.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_IntegralPaymentAbsoluteContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral payment for all subintervals implies absolute continuity.
The proof compares increments with an absolutely continuous primitive. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma absolutelyContinuous_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hg ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  apply lt_of_le_of_lt _ (hbound E hE hlen)
  exact Finset.sum_le_sum fun i hi => h _ (hE.1 i hi).1 _ (hE.1 i hi).2

lemma integral_payment_implies_absoluteContinuity {u G : ℝ → ℝ}
    (hG : ∀ a b, IntervalIntegrable G volume a b)
    (hpay : ∀ x y, |u x-u y| ≤ ∫ t in uIoc x y, |G t|) (a b : ℝ) :
    AbsolutelyContinuousOnInterval u a b := by
  let F : ℝ → ℝ := fun x => ∫ t in a..x, |G t|
  have hF : AbsolutelyContinuousOnInterval F a b :=
    (hG a b).abs.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  apply absolutelyContinuous_of_dist_le hF
  intro x _ y _
  have he : dist (F x) (F y) = ∫ t in uIoc x y, |G t| := by
    rw [Real.dist_eq, abs_sub_comm]
    change |(∫ t in a..y, |G t|)-(∫ t in a..x, |G t|)| = _
    rw [intervalIntegral.integral_interval_sub_left (hG a y).abs (hG a x).abs,
      intervalIntegral.abs_integral_eq_abs_integral_uIoc,
      abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
  rw [he, Real.dist_eq]
  exact hpay x y

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevCoordinateFTC
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual weak partials integrate to coordinate increments on almost
every line; the continuous representative is absolutely continuous there. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolev_coordinate_fundamentalTheorem {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ x z : ℝ,
      (∫ t in x..z, W.weakGrad (physicalCoordinateLine i y t) i) =
        u (physicalCoordinateLine i y z)-u (physicalCoordinateLine i y x) := by
  have hg : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  obtain ⟨ρ, P, hρ, hP, _, hPL, hdom⟩ := exists_L2_dominated_ae_subsequence
    (fun n => planarMollification_partial_memLp W hs n i) hg
    (planarMollification_tendsto_gradient_L2 W i)
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using W.memLp
  have hfn (n : ℕ) : ContDiff ℝ 1 (planarMollification u (ρ n)) :=
    (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) (ρ n)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  filter_upwards [memLp_physicalCoordinateLine_ae hP hPL i,
    ae_ae_physicalCoordinateLine hdom i] with y hy hd
  apply line_integral_eq_sub_of_dominated_derivatives
    (fun n => (hfn n).comp ((physicalCoordinateLine_contDiff i y).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
    (fun t => (planarMollification_tendsto_of_continuous hu _).comp hρ)
    (hy.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  · filter_upwards [hd] with t ht
    intro n
    simpa only [Function.comp_def, physicalCoordinateLine_deriv (hfn n)] using ht.1 n
  · filter_upwards [hd] with t ht
    simpa only [Function.comp_def, physicalCoordinateLine_deriv (hfn _)] using ht.2

lemma sobolev_coordinate_absolutelyContinuous {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun t => u (physicalCoordinateLine i y t)) a b := by
  filter_upwards [exact_sobolev_line_payment hu hs W i] with y hy
  exact integral_payment_implies_absoluteContinuity
    (fun a b => (hy a b).1) (fun a b => (hy a b).2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevClassicalPartials
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On almost every coordinate line, the classical derivative of the
continuous Sobolev representative equals its actual weak partial. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma locallyIntegrable_of_intervalIntegrable {G : ℝ → ℝ}
    (hG : ∀ a b, IntervalIntegrable G volume a b) : LocallyIntegrable G volume := by
  intro x
  refine ⟨Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (hG (x-1) (x+1)).1.mono_set Ioo_subset_Ioc_self

lemma ae_hasDerivAt_of_integral_increments {u G : ℝ → ℝ}
    (hG : ∀ a b, IntervalIntegrable G volume a b)
    (hinc : ∀ a b, (∫ t in a..b, G t) = u b-u a) :
    ∀ᵐ t ∂volume, HasDerivAt u (G t) t := by
  have hu : u = fun t => u 0 + ∫ s in (0 : ℝ)..t, G s := by
    funext t
    rw [hinc]
    ring
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_of_intervalIntegrable hG)] with t ht
  rw [hu]
  exact (ht 0).const_add _

lemma sobolev_coordinate_ae_hasDerivAt {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ t ∂volume,
      HasDerivAt (fun s => u (physicalCoordinateLine i y s))
        (W.weakGrad (physicalCoordinateLine i y t) i) t := by
  filter_upwards [exact_sobolev_line_payment hu hs W i,
    sobolev_coordinate_fundamentalTheorem hu hs W i] with y hy hftc
  exact ae_hasDerivAt_of_integral_increments (fun a b => (hy a b).1) hftc

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevClassicalPartials
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localizing the actual coordinate derivative theorem by a smooth
compact cutoff equal to one near the chosen compact core. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_core_sobolev_coordinate_derivative
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u Ω) (i : Fin 2) :
    ∃ V : Set EuclideanPlane, IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∀ᵐ y ∂volume, ∀ᵐ t ∂volume, physicalCoordinateLine i y t ∈ V →
        HasDerivAt (fun s => u (physicalCoordinateLine i y s))
          (W.weakGrad (physicalCoordinateLine i y t) i) t := by
  obtain ⟨η, V, hη, hsη, _, hηΩ, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hηΩ
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨Ww⟩ := exists_global_compact_cutoff_witness hΩ W.memW1p hη hsη hηΩ
  have heq : EqOn w u V := fun p hp => by dsimp only [w]; rw [hone p hp, one_mul]
  have hg : ∀ᵐ p ∂volume, p ∈ V → Ww.weakGrad p i = W.weakGrad p i :=
    (ae_restrict_iff' hV.measurableSet).mp (weakGrad_eq_on_cutoff_plateau hV hVΩ W Ww hone i)
  refine ⟨V, hV, hKV, hVΩ, ?_⟩
  filter_upwards [sobolev_coordinate_ae_hasDerivAt (hη.continuous.mul hu) hsη.mul_right Ww i,
    ae_ae_physicalCoordinateLine hg i] with y hy hgy
  filter_upwards [hy, hgy] with t ht hgt
  intro htV
  rw [hgt htV] at ht
  apply ht.congr_of_eventuallyEq
  have hn : ∀ᶠ s in 𝓝 t, physicalCoordinateLine i y s ∈ V :=
    (physicalCoordinateLine_contDiff i y).continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds htV)
  filter_upwards [hn] with s hs
  exact (heq hs).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocallySobolevPartials
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Classical coordinate partials for the precise continuous representative
of a genuinely local W1,2 function. No global integrability is assumed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_coordinate_ae_hasDerivAt {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ t ∂volume,
      HasDerivAt (fun s => u (physicalCoordinateLine i y s))
        (V (physicalCoordinateLine i y t) i) t := by
  have hsub (n : ℕ) : closedBall (0 : EuclideanPlane) n ⊆ ball 0 (n+1) := by
    intro p hp
    exact (mem_closedBall.mp hp).trans_lt (by linarith)
  choose O hO hKO hOsub hder using fun n : ℕ =>
    compact_core_sobolev_coordinate_derivative isOpen_ball (isCompact_closedBall (0 : EuclideanPlane) n)
      (hsub n) hu (scalarBallWeakWitness hu hw hLp (n+1)) i
  have hall : ∀ᵐ y ∂volume, ∀ n : ℕ, ∀ᵐ t ∂volume,
      physicalCoordinateLine i y t ∈ O n →
        HasDerivAt (fun s => u (physicalCoordinateLine i y s))
          (V (physicalCoordinateLine i y t) i) t := by
    apply ae_all_iff.mpr
    intro n
    exact hder n
  filter_upwards [hall] with y hy
  filter_upwards [ae_all_iff.mpr hy] with t ht
  obtain ⟨n, hn⟩ := exists_nat_gt ‖physicalCoordinateLine i y t‖
  apply ht n (hKO n ?_)
  simpa only [mem_closedBall, dist_zero_right] using hn.le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocallySobolevACL
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate absolute continuity for continuous local W1,2 functions,
obtained from compact cutoffs without assumptions at infinity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal

/-- d13f23b's `AbsolutelyContinuousOnInterval.congr` (missing in our Mathlib 0df444a), with its proof. -/
theorem _root_.AbsolutelyContinuousOnInterval.congr {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X}
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : Set.EqOn f g (Set.uIcc a b)) : AbsolutelyContinuousOnInterval g a b := by
  apply Filter.Tendsto.congr' _ hf
  rw [Filter.eventuallyEq_inf_principal_iff]
  filter_upwards with ⟨n, I⟩ hnI
  exact Finset.sum_congr rfl fun i hi ↦ by rw [hfg (hnI.1 i hi).1, hfg (hnI.1 i hi).2]
noncomputable section
namespace CircleDomainRigidity

lemma compact_core_sobolev_coordinate_ACL
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u Ω) (i : Fin 2) :
    ∃ V : Set EuclideanPlane, IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∀ᵐ y ∂volume, ∀ a b : ℝ, MapsTo (physicalCoordinateLine i y) (uIcc a b) V →
        AbsolutelyContinuousOnInterval (fun s => u (physicalCoordinateLine i y s)) a b := by
  obtain ⟨η, V, hη, hsη, _, hηΩ, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hηΩ
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨Ww⟩ := exists_global_compact_cutoff_witness hΩ W.memW1p hη hsη hηΩ
  have heq : EqOn w u V := fun p hp => by dsimp only [w]; rw [hone p hp, one_mul]
  refine ⟨V, hV, hKV, hVΩ, ?_⟩
  filter_upwards [sobolev_coordinate_absolutelyContinuous (hη.continuous.mul hu) hsη.mul_right Ww i]
    with y hy
  intro a b hab
  exact (hy a b).congr (fun t ht => heq (hab ht))

lemma locally_sobolev_coordinate_absolutelyContinuous {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun s => u (physicalCoordinateLine i y s)) a b := by
  have hsub (n : ℕ) : closedBall (0 : EuclideanPlane) n ⊆ ball 0 (n+1) := by
    intro p hp
    exact (mem_closedBall.mp hp).trans_lt (by linarith)
  choose O hO hKO hOsub hac using fun n : ℕ =>
    compact_core_sobolev_coordinate_ACL isOpen_ball (isCompact_closedBall (0 : EuclideanPlane) n)
      (hsub n) hu (scalarBallWeakWitness hu hw hLp (n+1)) i
  have hall : ∀ᵐ y ∂volume, ∀ n : ℕ, ∀ a b : ℝ,
      MapsTo (physicalCoordinateLine i y) (uIcc a b) (O n) →
        AbsolutelyContinuousOnInterval (fun s => u (physicalCoordinateLine i y s)) a b :=
    ae_all_iff.mpr hac
  filter_upwards [hall] with y hy
  intro a b
  obtain ⟨B, hB⟩ := isCompact_uIcc.bddAbove_image
    ((physicalCoordinateLine_contDiff i y).continuous.norm.continuousOn)
  obtain ⟨n, hn⟩ := exists_nat_gt B
  apply hy n a b
  intro t ht
  apply hKO n
  rw [mem_closedBall, dist_zero_right]
  exact (hB (mem_image_of_mem _ ht)).trans hn.le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocallySobolevCoordinateFTC
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local Sobolev coordinate integration with the actual weak
partial, now without any global support or global L2 hypothesis. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_coordinate_fundamentalTheorem {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ a b : ℝ,
      IntervalIntegrable (fun t => V (physicalCoordinateLine i y t) i) volume a b ∧
      (∫ t in a..b, V (physicalCoordinateLine i y t) i) =
        u (physicalCoordinateLine i y b)-u (physicalCoordinateLine i y a) := by
  filter_upwards [locally_sobolev_coordinate_absolutelyContinuous hu hw hLp i,
    locally_sobolev_coordinate_ae_hasDerivAt hu hw hLp i] with y hac hd
  have heq : (fun t => deriv (fun s => u (physicalCoordinateLine i y s)) t) =ᵐ[volume]
      fun t => V (physicalCoordinateLine i y t) i := hd.mono fun t ht => ht.deriv
  intro a b
  refine ⟨(hac a b).intervalIntegrable_deriv.congr_ae (ae_restrict_of_ae heq), ?_⟩
  rw [← intervalIntegral.integral_congr_ae_restrict (ae_restrict_of_ae heq)]
  exact (hac a b).integral_deriv_eq_sub

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalGradientIntegrability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the actual local weak partials on compact coordinate sets. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_partial_integrableOn_compact {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {K : Set EuclideanPlane} (hK : IsCompact K) (i : Fin 2) :
    IntegrableOn (fun p => V p i) K volume := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hi : IntegrableOn (fun p => V p i) (ball 0 R) volume :=
    (hLp R i).integrable (by norm_num)
  exact hi.mono_set hR

lemma local_partial_coordinate_integrableOn {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (i : Fin 2) :
    IntegrableOn (fun p => V (euclideanPlaneCoordinates.symm p) i) K volume := by
  have hKC := hK.image euclideanPlaneCoordinates.symm.continuous
  have hI := local_partial_integrableOn_compact hLp hKC i
  have hP := euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
    hKC.measurableSet
  have hpre : euclideanPlaneCoordinates.symm ⁻¹' (euclideanPlaneCoordinates.symm '' K) = K :=
    Set.preimage_image_eq K euclideanPlaneCoordinates.symm.injective
  rw [hpre] at hP
  exact hP.integrable_comp_of_integrable hI

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TensorAverageBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging an axis-by-axis pointwise bound over a product set. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma abs_sub_iterated_average_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NeZero μ] [NeZero ν] {f : X → Y → ℝ} {V : X → ℝ} {z H : ℝ}
    (hf : ∀ᵐ x ∂μ, Integrable (f x) ν)
    (hmean : Integrable (fun x => ⨍ y, f x y ∂ν) μ)
    (hV : Integrable V μ)
    (hb : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, |z-f x y| ≤ H+V x) :
    |z-(⨍ x, ⨍ y, f x y ∂ν ∂μ)| ≤ H+(⨍ x, V x ∂μ) := by
  have hpoint : ∀ᵐ x ∂μ, |z-(⨍ y, f x y ∂ν)| ≤ H+V x := by
    filter_upwards [hf, hb] with x hx hbx
    exact abs_sub_average_le_of_ae hx z (H+V x) hbx
  apply (abs_sub_average_le_average_abs_sub hmean z).trans
  have hh := average_mono_real ((integrable_const z).sub hmean).abs
    ((integrable_const H).add hV) hpoint
  have he : (⨍ x, H+V x ∂μ) = H+(⨍ x, V x ∂μ) := by
    simpa only [Pi.add_apply, average_const] using
      (average_add (integrable_const H : Integrable (fun _ : X => H) μ) hV)
  have hh' : (⨍ x, |z-(⨍ y, f x y ∂ν)| ∂μ) ≤ (⨍ x, H+V x ∂μ) := by
    simpa only [Pi.sub_apply, Pi.add_apply] using hh
  exact hh'.trans_eq he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ProductAverage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini for finite-measure averages and an integrated row estimate. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma product_average {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (⨍ p, f p ∂μ.prod ν) = ⨍ x, ⨍ y, f (x,y) ∂ν ∂μ := by
  have hm : (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using (measureReal_prod_prod (μ := μ) (ν := ν) univ univ)
  simp only [average_eq, smul_eq_mul, hm, integral_const_mul, integral_prod _ hf, mul_inv_rev]
  ring

lemma iterated_average_swap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (⨍ x, ⨍ y, f (x,y) ∂ν ∂μ) = ⨍ y, ⨍ x, f (x,y) ∂μ ∂ν := by
  simp only [average_eq, smul_eq_mul, integral_const_mul]
  rw [integral_integral_swap (f := fun x y => f (x,y)) hf]
  ring

lemma average_integral_first {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (⨍ y, ∫ x, f (x,y) ∂μ ∂ν) = μ.real univ * (⨍ p, f p ∂μ.prod ν) := by
  simp_rw [← measure_smul_average μ (fun x => f (x,_)), smul_eq_mul]
  rw [average_const_mul, ← iterated_average_swap hf, ← product_average hf]

lemma average_integral_second {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (⨍ x, ∫ y, f (x,y) ∂ν ∂μ) = ν.real univ * (⨍ p, f p ∂μ.prod ν) := by
  simp_rw [← measure_smul_average ν (fun y => f (_,y)), smul_eq_mul]
  rw [average_const_mul, ← product_average hf]

lemma iterated_average_row_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NeZero μ] [NeZero ν] {f : X × Y → ℝ} {H : Y → ℝ} {C : ℝ}
    (hf : Integrable f (μ.prod ν)) (hH : Integrable H ν)
    (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x,y) ≤ H y+C) :
    (⨍ y, ⨍ x, f (x,y) ∂μ ∂ν) ≤ (⨍ y, H y ∂ν)+C := by
  have hi : Integrable (fun y => ⨍ x, f (x,y) ∂μ) ν := by
    simp only [average_eq, smul_eq_mul]
    exact hf.integral_prod_right.const_mul _
  have hh : (fun y => ⨍ x, f (x,y) ∂μ) ≤ᵐ[ν] fun y => H y+C := by
    filter_upwards [hf.prod_left_ae, h] with y hy hle
    simpa only [average_const] using average_mono_real hy (integrable_const (H y+C)) hle
  have he : (⨍ y, H y+C ∂ν) = (⨍ y, H y ∂ν)+C := by
    simpa only [Pi.add_apply, average_const] using average_add hH (integrable_const C)
  exact (average_mono_real hi (hH.add (integrable_const C)) hh).trans_eq he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_IntervalPoincare
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A one-dimensional mean-oscillation bound, keeping the actual
integrable derivative in the right-hand side. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma interval_increment_le_integral {u G : ℝ → ℝ} {a b x y : ℝ}
    (hG : IntegrableOn G (Icc a b) volume) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hftc : (∫ t in x..y, G t) = u y-u x) :
    |u x-u y| ≤ ∫ t in Icc a b, |G t| := by
  calc
    |u x-u y| = |∫ t in x..y, G t| := by rw [hftc, abs_sub_comm]
    _ ≤ ∫ t in uIoc x y, |G t| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := G) (a := x) (b := y))
    _ ≤ ∫ t in Icc a b, |G t| :=
      setIntegral_mono_set hG.abs (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall fun _ ht => uIcc_subset_Icc hx hy (uIoc_subset_uIcc ht))

lemma volume_restrict_Icc_ne_zero {a b : ℝ} (hab : a < b) :
    (volume : Measure ℝ).restrict (Icc a b) ≠ 0 := by
  intro h
  have hh := congrArg (fun μ : Measure ℝ => μ univ) h
  have hv : volume (Icc a b) = 0 := by simpa using hh
  rw [Real.volume_Icc] at hv
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))) hv

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectanglePoincare
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Axis-by-axis mean oscillation on actual Euclidean rectangles. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma rectangle_point_mean_bound {f Gx Gy : ℝ × ℝ → ℝ} {a b c d x y : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGy : Integrable Gy ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hrow : IntegrableOn (fun s => Gx (s,y)) (Icc a b) volume)
    (hfx : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (∫ r in s..t, Gx (r,y)) = f (t,y)-f (s,y))
    (hfy : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ t ∈ Icc c d, ∀ w ∈ Icc c d,
      (∫ r in t..w, Gy (s,r)) = f (s,w)-f (s,t))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    |f (x,y) - (⨍ s in Icc a b, ⨍ t in Icc c d, f (s,t))| ≤
      (∫ s in Icc a b, |Gx (s,y)|) +
        (⨍ s in Icc a b, ∫ t in Icc c d, |Gy (s,t)|) := by
  let : NeZero ((volume : Measure ℝ).restrict (Icc a b)) :=
    ⟨volume_restrict_Icc_ne_zero hab⟩
  let : NeZero ((volume : Measure ℝ).restrict (Icc c d)) :=
    ⟨volume_restrict_Icc_ne_zero hcd⟩
  have hm : Integrable (fun s => ⨍ t in Icc c d, f (s,t))
      (volume.restrict (Icc a b)) := by
    simp only [average_eq, smul_eq_mul]
    exact hf.integral_prod_left.const_mul _
  apply abs_sub_iterated_average_le hf.prod_right_ae hm hGy.abs.integral_prod_left
  filter_upwards [hGy.prod_right_ae, hfy, ae_restrict_mem measurableSet_Icc]
    with s hs hfs hsmem
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  calc
    |f (x,y)-f (s,t)| ≤ |f (x,y)-f (s,y)| + |f (s,y)-f (s,t)| := abs_sub_le _ _ _
    _ ≤ (∫ r in Icc a b, |Gx (r,y)|) + (∫ r in Icc c d, |Gy (s,r)|) :=
      add_le_add (interval_increment_le_integral (u := fun r => f (r,y)) hrow hx hsmem (hfx x hx s hsmem))
        (interval_increment_le_integral (u := fun r => f (s,r)) hs hy ht (hfs y hy t ht))

lemma rectangle_ae_mean_bound {f Gx Gy : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGx : Integrable Gx ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGy : Integrable Gy ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hfx : ∀ᵐ t ∂volume.restrict (Icc c d), ∀ s ∈ Icc a b, ∀ w ∈ Icc a b,
      (∫ r in s..w, Gx (r,t)) = f (w,t)-f (s,t))
    (hfy : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ t ∈ Icc c d, ∀ w ∈ Icc c d,
      (∫ r in t..w, Gy (s,r)) = f (s,w)-f (s,t)) :
    ∀ᵐ y ∂volume.restrict (Icc c d), ∀ x ∈ Icc a b,
    |f (x,y) - (⨍ s in Icc a b, ⨍ t in Icc c d, f (s,t))| ≤
      (∫ s in Icc a b, |Gx (s,y)|) +
        (⨍ s in Icc a b, ∫ t in Icc c d, |Gy (s,t)|) := by
  filter_upwards [hGx.prod_left_ae, hfx, ae_restrict_mem measurableSet_Icc]
    with y hy hfy' hymem
  intro x hx
  exact rectangle_point_mean_bound hab hcd hf hGy hy hfy' hfy hx hymem

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RectangleMeanOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The L1 rectangular Poincare estimate, in normalized-average form. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma rectangle_mean_oscillation {f Gx Gy : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGx : Integrable Gx ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGy : Integrable Gy ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hfx : ∀ᵐ t ∂volume.restrict (Icc c d), ∀ s ∈ Icc a b, ∀ w ∈ Icc a b,
      (∫ r in s..w, Gx (r,t)) = f (w,t)-f (s,t))
    (hfy : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ t ∈ Icc c d, ∀ w ∈ Icc c d,
      (∫ r in t..w, Gy (s,r)) = f (s,w)-f (s,t)) :
    (⨍ y in Icc c d, ⨍ x in Icc a b,
      |f (x,y)-(⨍ s in Icc a b, ⨍ t in Icc c d, f (s,t))|) ≤
      (⨍ y in Icc c d, ∫ x in Icc a b, |Gx (x,y)|) +
      (⨍ x in Icc a b, ∫ y in Icc c d, |Gy (x,y)|) := by
  let : NeZero ((volume : Measure ℝ).restrict (Icc a b)) :=
    ⟨volume_restrict_Icc_ne_zero hab⟩
  let : NeZero ((volume : Measure ℝ).restrict (Icc c d)) :=
    ⟨volume_restrict_Icc_ne_zero hcd⟩
  apply iterated_average_row_bound (hf.sub (integrable_const _)).abs
    hGx.abs.integral_prod_right
  filter_upwards [rectangle_ae_mean_bound hab hcd hf hGx hGy hfx hfy] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hy x hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectangularPoincare
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Poincare with explicit side lengths and area averages. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma rectangular_poincare {f Gx Gy : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGx : Integrable Gx ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGy : Integrable Gy ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hfx : ∀ᵐ t ∂volume.restrict (Icc c d), ∀ s ∈ Icc a b, ∀ w ∈ Icc a b,
      (∫ r in s..w, Gx (r,t)) = f (w,t)-f (s,t))
    (hfy : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ t ∈ Icc c d, ∀ w ∈ Icc c d,
      (∫ r in t..w, Gy (s,r)) = f (s,w)-f (s,t)) :
    (⨍ p, |f p-(⨍ q, f q ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))|
      ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) ≤
    (b-a)*(⨍ p, |Gx p| ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) +
    (d-c)*(⨍ p, |Gy p| ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  let m := ⨍ s in Icc a b, ⨍ t in Icc c d, f (s,t)
  have ho : Integrable (fun p => |f p-m|)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) :=
    (hf.sub (integrable_const m)).abs
  calc
    _ = ⨍ y in Icc c d, ⨍ x in Icc a b, |f (x,y)-m| := by
      rw [product_average hf]
      exact (product_average ho).trans (iterated_average_swap ho)
    _ ≤ (⨍ y in Icc c d, ∫ x in Icc a b, |Gx (x,y)|) +
        (⨍ x in Icc a b, ∫ y in Icc c d, |Gy (x,y)|) :=
      rectangle_mean_oscillation hab hcd hf hGx hGy hfx hfy
    _ = _ := by
      rw [average_integral_first hGx.abs, average_integral_second hGy.abs]
      simp only [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le hab.le,
        Real.volume_real_Icc_of_le hcd.le]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevPoincare
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poincare for the precise continuous local W1,2 representative, with
its actual distributional partials and no additional line assumptions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_rectangular_poincare {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    let μ := (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))
    (⨍ p, |u (euclideanPlaneCoordinates.symm p)-
      (⨍ q, u (euclideanPlaneCoordinates.symm q) ∂μ)| ∂μ) ≤
    (b-a)*(⨍ p, |V (euclideanPlaneCoordinates.symm p) 0| ∂μ) +
    (d-c)*(⨍ p, |V (euclideanPlaneCoordinates.symm p) 1| ∂μ) := by
  dsimp only
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hμ : (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) =
      (volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hcont : Continuous (fun p => u (euclideanPlaneCoordinates.symm p)) :=
    hu.comp euclideanPlaneCoordinates.symm.continuous
  have hf : Integrable (fun p => u (euclideanPlaneCoordinates.symm p))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [hμ]
    exact hcont.continuousOn.integrableOn_compact hK
  have hI (i : Fin 2) : Integrable (fun p => V (euclideanPlaneCoordinates.symm p) i)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [hμ]
    exact local_partial_coordinate_integrableOn hLp hK i
  apply rectangular_poincare hab hcd hf (hI 0) (hI 1)
  · filter_upwards [ae_restrict_of_ae (locally_sobolev_coordinate_fundamentalTheorem hu hw hLp 0)]
      with t ht
    intro s _ w _
    simpa only [physicalCoordinateLine, ite_true, if_true] using (ht s w).2
  · filter_upwards [ae_restrict_of_ae (locally_sobolev_coordinate_fundamentalTheorem hu hw hLp 1)]
      with s hs
    intro t _ w _
    simpa [physicalCoordinateLine] using (hs t w).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoordinateSquares
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate squares, their exact areas, and the actual Sobolev Poincare estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma coordinateSquare_eq_rectangle (c : ℝ × ℝ) (r : ℝ) :
    coordinateSquare c r = Icc (c.1-r) (c.1+r) ×ˢ Icc (c.2-r) (c.2+r) := by
  change closedBall (c.1,c.2) r = _
  rw [← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc]

lemma coordinateSquare_compact (c : ℝ × ℝ) (r : ℝ) : IsCompact (coordinateSquare c r) :=
  isCompact_closedBall c r

lemma coordinateSquare_real_volume (c : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coordinateSquare c r) = 4*r^2 := by
  rw [coordinateSquare_eq_rectangle]
  have h0 : c.1-r ≤ c.1+r := by linarith
  have h1 : c.2-r ≤ c.2+r := by linarith
  rw [Measure.volume_eq_prod, measureReal_prod_prod,
    Real.volume_real_Icc_of_le h0, Real.volume_real_Icc_of_le h1]
  ring

lemma coordinateSquare_volume_ne_zero (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    volume (coordinateSquare c r) ≠ 0 := by
  intro hz
  have he := coordinateSquare_real_volume c hr.le
  rw [measureReal_def, hz, ENNReal.toReal_zero] at he
  nlinarith [sq_pos_of_pos hr]

lemma locally_sobolev_square_poincare {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    (⨍ p in coordinateSquare c r, |u (euclideanPlaneCoordinates.symm p)-
      (⨍ q in coordinateSquare c r, u (euclideanPlaneCoordinates.symm q))|) ≤
    2*r*(⨍ p in coordinateSquare c r,
      |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) := by
  have h0 : c.1-r < c.1+r := by linarith
  have h1 : c.2-r < c.2+r := by linarith
  have h := locally_sobolev_rectangular_poincare hu hw hLp h0 h1
  dsimp only at h
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod,
    ← coordinateSquare_eq_rectangle] at h
  have hI (i : Fin 2) : IntegrableOn
      (fun p => |V (euclideanPlaneCoordinates.symm p) i|) (coordinateSquare c r) volume :=
    (local_partial_coordinate_integrableOn hLp (coordinateSquare_compact c r) i).abs
  have he : (⨍ p in coordinateSquare c r,
      |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) =
      (⨍ p in coordinateSquare c r, |V (euclideanPlaneCoordinates.symm p) 0|)+
      (⨍ p in coordinateSquare c r, |V (euclideanPlaneCoordinates.symm p) 1|) := by
    simpa only [Pi.add_apply] using average_add (hI 0) (hI 1)
  rw [he]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_SquareAverageLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking square averages recover the specified continuous representative. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma squareAverage_tendsto {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => squareAverage f c (r n)) atTop (𝓝 (f c)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfd⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := c))
    (ε/2) (half_pos hε)
  have hev : ∀ᶠ n in atTop, r n < δ := (tendsto_order.mp hlim).2 δ hδ
  filter_upwards [hev] with n hn
  let : IsFiniteMeasure (volume.restrict (coordinateSquare c (r n))) :=
    isFiniteMeasure_restrict.mpr (coordinateSquare_compact c (r n)).measure_lt_top.ne
  let : NeZero (volume.restrict (coordinateSquare c (r n))) :=
    ⟨by simpa using coordinateSquare_volume_ne_zero c (hr n)⟩
  have hi : IntegrableOn f (coordinateSquare c (r n)) volume :=
    hf.continuousOn.integrableOn_compact (coordinateSquare_compact c (r n))
  have hb : ∀ᵐ p ∂volume.restrict (coordinateSquare c (r n)), |f c-f p| ≤ ε/2 := by
    filter_upwards [ae_restrict_mem (coordinateSquare_compact c (r n)).measurableSet] with p hp
    have hd : dist p c < δ := (mem_closedBall.mp hp).trans_lt hn
    simpa only [Real.dist_eq, abs_sub_comm] using (hfd hd).le
  have hbound := abs_sub_average_le_of_ae hi (f c) (ε/2) hb
  have hh : dist (squareAverage f c (r n)) (f c) ≤ ε/2 := by
    simpa only [squareAverage, Real.dist_eq, abs_sub_comm] using hbound
  exact hh.trans_lt (half_lt_self hε)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SquareAverageComparison
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative comparison of averages on nested comparable coordinate squares. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma squareAverage_comparison {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {c d : ℝ × ℝ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hsub : coordinateSquare c r ⊆ coordinateSquare d R) (hscale : R ≤ 2*r) :
    |squareAverage f c r-squareAverage f d R| ≤
    4*(⨍ p in coordinateSquare d R, |f p-squareAverage f d R|) := by
  apply abs_average_sub_average_le_oscillation hsub
    (coordinateSquare_volume_ne_zero c hr) (coordinateSquare_compact d R).measure_lt_top.ne
    (hf.continuousOn.integrableOn_compact (coordinateSquare_compact d R))
  rw [coordinateSquare_real_volume d hR.le, coordinateSquare_real_volume c hr.le]
  nlinarith [mul_self_le_mul_self hR.le hscale]

lemma squareAverage_halving {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    |squareAverage f c r-squareAverage f c (r/2)| ≤
    4*(⨍ p in coordinateSquare c r, |f p-squareAverage f c r|) := by
  rw [abs_sub_comm]
  exact squareAverage_comparison hf (half_pos hr) hr
    (closedBall_subset_closedBall (by linarith)) (by linarith)

lemma square_point_average_bound {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r K : ℝ} (hr : 0 < r)
    (hosc : ∀ n : ℕ, (⨍ p in coordinateSquare c (r*(1/2:ℝ)^n),
      |f p-squareAverage f c (r*(1/2:ℝ)^n)|) ≤ K*(r*(1/2:ℝ)^n)) :
    |f c-squareAverage f c r| ≤ 8*K*r := by
  have hpos (n : ℕ) : 0 < r*(1/2:ℝ)^n := mul_pos hr (pow_pos (by norm_num) n)
  have hlim : Tendsto (fun n : ℕ => r*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).const_mul r
  have hstep (n : ℕ) : dist (squareAverage f c (r*(1/2:ℝ)^n))
      (squareAverage f c (r*(1/2:ℝ)^(n+1))) ≤ (4*K*r)*(1/2:ℝ)^n := by
    have he : r*(1/2:ℝ)^(n+1) = (r*(1/2:ℝ)^n)/2 := by rw [pow_succ]; ring
    rw [he, Real.dist_eq]
    calc
      _ ≤ 4*(⨍ p in coordinateSquare c (r*(1/2:ℝ)^n),
          |f p-squareAverage f c (r*(1/2:ℝ)^n)|) := squareAverage_halving hf c (hpos n)
      _ ≤ 4*(K*(r*(1/2:ℝ)^n)) := mul_le_mul_of_nonneg_left (hosc n) (by norm_num)
      _ = _ := by ring
  have hb := dist_le_of_le_geometric_of_tendsto₀ (1/2:ℝ) (4*K*r) (by norm_num)
    hstep (squareAverage_tendsto hf c hpos hlim)
  simpa only [pow_zero, mul_one, Real.dist_eq, abs_sub_comm] using
    (show dist (squareAverage f c (r*(1/2:ℝ)^0)) (f c) ≤ 8*K*r by
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      ring)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SquareQuarterOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise control by the mean oscillations on quarter-scale squares.
The geometric decay is matched to square-integrable energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma squareAverage_quartering {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    |squareAverage f c r-squareAverage f c (r/4)| ≤
      16*(⨍ p in coordinateSquare c r, |f p-squareAverage f c r|) := by
  rw [abs_sub_comm]
  apply abs_average_sub_average_le_oscillation
    (closedBall_subset_closedBall (by linarith))
    (coordinateSquare_volume_ne_zero c (by positivity))
    (coordinateSquare_compact c r).measure_lt_top.ne
    (hf.continuousOn.integrableOn_compact (coordinateSquare_compact c r))
  change volume.real (coordinateSquare c r) ≤ 16*volume.real (coordinateSquare c (r/4))
  rw [coordinateSquare_real_volume c hr.le,
    coordinateSquare_real_volume c (show 0 ≤ r/4 by positivity)]
  nlinarith

lemma square_point_average_bound_quarters {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r K : ℝ} (hr : 0 < r)
    (hosc : ∀ n : ℕ, (⨍ p in coordinateSquare c (r*(1/4:ℝ)^n),
      |f p-squareAverage f c (r*(1/4:ℝ)^n)|) ≤ K*(1/2:ℝ)^n) :
    |f c-squareAverage f c r| ≤ 32*K := by
  have hpos (n : ℕ) : 0 < r*(1/4:ℝ)^n := mul_pos hr (pow_pos (by norm_num) n)
  have hlim : Tendsto (fun n : ℕ => r*(1/4:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
        (by norm_num : (1/4:ℝ) < 1)).const_mul r
  have hstep (n : ℕ) : dist (squareAverage f c (r*(1/4:ℝ)^n))
      (squareAverage f c (r*(1/4:ℝ)^(n+1))) ≤ (16*K)*(1/2:ℝ)^n := by
    have he : r*(1/4:ℝ)^(n+1) = (r*(1/4:ℝ)^n)/4 := by rw [pow_succ]; ring
    rw [he, Real.dist_eq]
    calc
      _ ≤ 16*(⨍ p in coordinateSquare c (r*(1/4:ℝ)^n),
          |f p-squareAverage f c (r*(1/4:ℝ)^n)|) := squareAverage_quartering hf c (hpos n)
      _ ≤ 16*(K*(1/2:ℝ)^n) := mul_le_mul_of_nonneg_left (hosc n) (by norm_num)
      _ = _ := by ring
  have hb := dist_le_of_le_geometric_of_tendsto₀ (1/2:ℝ) (16*K) (by norm_num)
    hstep (squareAverage_tendsto hf c hpos hlim)
  simpa only [pow_zero, mul_one, Real.dist_eq, abs_sub_comm] using
    (show dist (squareAverage f c (r*(1/4:ℝ)^0)) (f c) ≤ 32*K by
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      ring)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AverageSquareBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square of a real average is bounded by the average of the square. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma sq_average_le_average_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [NeZero μ] {g : X → ℝ} (hg : Integrable g μ)
    (hg2 : Integrable (fun x => g x^2) μ) :
    (⨍ x, g x ∂μ)^2 ≤ ⨍ x, g x^2 ∂μ := by
  let a := ⨍ x, g x ∂μ
  have hp : (fun x => (g x-a)^2) = (fun x => g x^2-(2*a)*g x+a^2) := by
    funext x
    ring
  have hn : 0 ≤ (⨍ x, (g x-a)^2 ∂μ) := average_nonneg (fun x => sq_nonneg (g x-a))
  have he1 := average_add (hg2.sub (hg.const_mul (2*a)))
    (integrable_const (a^2) : Integrable (fun _ : X => a^2) μ)
  have he2 := average_sub hg2 (hg.const_mul (2*a))
  simp only [Pi.add_apply, Pi.sub_apply] at he1 he2
  rw [hp, he1, he2, average_const_mul, average_const] at hn
  dsimp only [a] at hn
  nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SquarePoincareEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A square's mean oscillation squared is bounded by its actual local
Sobolev energy. The radius cancels against the square's area. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_partial_coordinate_memLp {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (i : Fin 2) :
    MemLp (fun p => V (euclideanPlaneCoordinates.symm p) i) 2 (volume.restrict K) := by
  have hKC := hK.image euclideanPlaneCoordinates.symm.continuous
  obtain ⟨R,hR⟩ := hKC.isBounded.subset_ball 0
  have hi := (hLp R i).mono_measure (Measure.restrict_mono hR le_rfl)
  have hP := euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage hKC.measurableSet
  have hpre : euclideanPlaneCoordinates.symm ⁻¹' (euclideanPlaneCoordinates.symm '' K) = K :=
    Set.preimage_image_eq K euclideanPlaneCoordinates.symm.injective
  rw [hpre] at hP
  exact hi.comp_measurePreserving hP

lemma locally_sobolev_square_oscillation_sq {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    (⨍ p in coordinateSquare c r, |u (euclideanPlaneCoordinates.symm p)-
      squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c r|)^2 ≤
    ∫ p in coordinateSquare c r,
      (|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2 := by
  let G := fun p => |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|
  let μ := volume.restrict (coordinateSquare c r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (coordinateSquare_compact c r).measure_lt_top.ne
  let : NeZero μ := ⟨by simpa [μ] using coordinateSquare_volume_ne_zero c hr⟩
  have hG : MemLp G 2 μ :=
    (local_partial_coordinate_memLp hLp (coordinateSquare_compact c r) 0).norm.add
      (local_partial_coordinate_memLp hLp (coordinateSquare_compact c r) 1).norm
  have hsq := sq_average_le_average_sq (hG.integrable (by norm_num))
    ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG)
  have hP := locally_sobolev_square_poincare hu hw hLp c hr
  have hA : 0 ≤ ⨍ p in coordinateSquare c r, |u (euclideanPlaneCoordinates.symm p)-
      squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c r| :=
    average_nonneg (fun _ => abs_nonneg _)
  have hle := pow_le_pow_left₀ hA hP 2
  calc
    _ ≤ (2*r)^2 * (⨍ p, G p ∂μ)^2 := by simpa only [mul_pow] using hle
    _ ≤ (2*r)^2 * (⨍ p, G p^2 ∂μ) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by
      rw [average_eq, show μ.real univ = 4*r^2 by
        change (volume.restrict (coordinateSquare c r)).real univ = 4*r^2
        rw [measureReal_restrict_apply_univ, coordinateSquare_real_volume c hr.le], smul_eq_mul]
      dsimp only [μ, G]
      field_simp [hr.ne']
      ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevCapacityScale
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A point with value at least one and small coarse average forces
quantitative Sobolev energy on one of its shrinking coordinate squares. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_capacity_scale {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (c : ℝ × ℝ) (hc : 1 ≤ u (euclideanPlaneCoordinates.symm c))
    (hmean : |squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1| ≤ 1/2) :
    ∃ n : ℕ, (1/128:ℝ)^2 * (1/4:ℝ)^n ≤
      ∫ p in coordinateSquare c ((1/4:ℝ)^n),
        (|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2 := by
  by_contra! hn
  have hosc (n : ℕ) :
      (⨍ p in coordinateSquare c (1*(1/4:ℝ)^n),
        |u (euclideanPlaneCoordinates.symm p)-
          squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c (1*(1/4:ℝ)^n)|) ≤
        (1/128:ℝ)*(1/2:ℝ)^n := by
    have he := locally_sobolev_square_oscillation_sq hu hw hLp c
      (pow_pos (by norm_num : (0:ℝ)<1/4) n)
    have hp : ((1/2:ℝ)^n)^2 = (1/4:ℝ)^n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    have hb : 0 ≤ (1/128:ℝ)*(1/2:ℝ)^n := by positivity
    simp only [one_mul]
    nlinarith [hn n]
  have hpoint := square_point_average_bound_quarters
    (hu.comp euclideanPlaneCoordinates.symm.continuous) c (by norm_num : (0:ℝ)<1) hosc
  have hmean' := (le_abs_self (squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1)).trans hmean
  have hl := le_abs_self (u (euclideanPlaneCoordinates.symm c)-
    squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1)
  change |u (euclideanPlaneCoordinates.symm c)-
    squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1| ≤ 32*(1/128:ℝ) at hpoint
  norm_num at hpoint
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevEnergyMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local two-coordinate Sobolev energy as a measure. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma coordinateSobolevEnergy_square (V : EuclideanPlane → EuclideanPlane)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (c : ℝ × ℝ) (r : ℝ) :
    coordinateSobolevEnergy V (coordinateSquare c r) = ENNReal.ofReal
      (∫ p in coordinateSquare c r,
        (|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2) := by
  have hG := (local_partial_coordinate_memLp hLp (coordinateSquare_compact c r) 0).norm.add
    (local_partial_coordinate_memLp hLp (coordinateSquare_compact c r) 1).norm
  rw [coordinateSobolevEnergy, withDensity_apply _ (coordinateSquare_compact c r).measurableSet]
  exact (ofReal_integral_eq_lintegral_ofReal hG.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SquareAverageL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse square averages are small when the global L2 mass is small. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma abs_unitSquareAverage_le_half {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 volume)
    (hsmall : (∫ p, f p^2) ≤ 1) (c : ℝ × ℝ) :
    |squareAverage f c 1| ≤ 1/2 := by
  let μ := volume.restrict (coordinateSquare c 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (coordinateSquare_compact c 1).measure_lt_top.ne
  let : NeZero μ := ⟨by
    simpa [μ] using coordinateSquare_volume_ne_zero c (by norm_num)⟩
  have hfm : MemLp f 2 μ := hf.mono_measure Measure.restrict_le_self
  have hJ := sq_average_le_average_sq (hfm.integrable (by norm_num)) hfm.integrable_sq
  have hglobal : (∫ p, f p^2 ∂μ) ≤ 1 :=
    (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun p => sq_nonneg (f p))
      hf.integrable_sq).trans hsmall
  have hm : μ.real univ = 4 := by
    change (volume.restrict (coordinateSquare c 1)).real univ = 4
    rw [measureReal_restrict_apply_univ, coordinateSquare_real_volume c (by norm_num)]
    norm_num
  have havg2 : (⨍ p, f p^2 ∂μ) = (4:ℝ)⁻¹*(∫ p, f p^2 ∂μ) := by
    rw [average_eq, hm, smul_eq_mul]
  rw [havg2] at hJ
  change (squareAverage f c 1)^2 ≤ _ at hJ
  nlinarith [sq_abs (squareAverage f c 1), abs_nonneg (squareAverage f c 1)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevCapacityBallCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capacity estimate retains its countable positive-radius ball cover,
so its cost can be transported to a small-diameter cover of the graph. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_unit_ball_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (huL2 : MemLp (fun p => u (euclideanPlaneCoordinates.symm p)) 2 volume)
    {A : Set (ℝ × ℝ)} (hA : A ⊆ closedBall 0 1)
    (hone : ∀ c ∈ A, 1 ≤ u (euclideanPlaneCoordinates.symm c)) :
    ∃ (U : Set (ℝ × ℝ)) (r : (ℝ × ℝ) → ℝ), U.Countable ∧
      (∀ x ∈ U, 0 < r x ∧ r x ≤ 4) ∧
      A ⊆ ⋃ x : U, closedBall (x : ℝ × ℝ) (r x) ∧
      (∑' x : U, ENNReal.ofReal (r x)) ≤ 131072 *
        (ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ) := by
  classical
  by_cases hs : (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) ≤ 1
  · have hmean (c : ℝ × ℝ) :
        |squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1| ≤ 1/2 :=
      abs_unitSquareAverage_le_half huL2 hs c
    choose n hn using fun c : A => locally_sobolev_capacity_scale hu hw hLp c (hone c c.property) (hmean c)
    let r : (ℝ × ℝ) → ℝ := fun c => if hc : c ∈ A then (1/4:ℝ)^(n ⟨c,hc⟩) else 1
    have hr : ∀ c ∈ A, 0 < r c := by
      intro c hc
      simp only [r, dite_eq_left hc]
      positivity
    have hb : ∀ c ∈ A, r c ≤ 1 := by
      intro c hc
      simp only [r, dite_eq_left hc]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hpay : ∀ c ∈ A, ENNReal.ofReal (r c) ≤
        16384 * coordinateSobolevEnergy V (closedBall c (r c)) := by
      intro c hc
      let E := ∫ p in coordinateSquare c (r c),
        (|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2
      have he : (1/128:ℝ)^2*r c ≤ E := by
        simpa only [r, dite_eq_left hc, E] using hn ⟨c,hc⟩
      have hh : r c ≤ 16384*E := by nlinarith
      have hm := coordinateSobolevEnergy_square V hLp c (r c)
      change coordinateSobolevEnergy V (closedBall c (r c)) = ENNReal.ofReal E at hm
      calc
        ENNReal.ofReal (r c) ≤ ENNReal.ofReal (16384*E) := ENNReal.ofReal_le_ofReal hh
        _ = 16384*ENNReal.ofReal E := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ = _ := by rw [hm]
    obtain ⟨U,hUA,hUc,hcover,hcost⟩ := energy_ball_cover hr hb (coordinateSobolevEnergy V) 16384 hpay
    refine ⟨U,fun x => 4*r x,hUc,(fun x hx => ⟨mul_pos (by norm_num) (hr x (hUA hx)), by linarith [hb x (hUA hx)]⟩),hcover,?_⟩
    have hsum : (∑' x : U, ENNReal.ofReal (4*r x)) = 4*∑' x : U, ENNReal.ofReal (r x) := by
      simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4), ENNReal.ofReal_ofNat]
      exact ENNReal.tsum_mul_left
    rw [hsum]
    calc
      _ ≤ 4*(16384*coordinateSobolevEnergy V univ) := mul_le_mul' le_rfl hcost
      _ ≤ 131072*(ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ) := by
        rw [← mul_assoc]
        apply mul_le_mul'
        · norm_num
        · exact le_add_of_nonneg_left (by positivity)
  · refine ⟨{0},fun _ => 1,countable_singleton _,(by simp),?_,?_⟩
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨0,mem_singleton 0⟩,hA hx⟩
    · have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) := by
        exact_mod_cast (ENNReal.ofReal_le_ofReal (le_of_not_ge hs))
      have hcard : (∑' _x : ({0} : Set (ℝ × ℝ)), (1 : ℝ≥0∞)) = 1 := by simp
      simp only [ENNReal.ofReal_one]
      change (∑' _x : ({0} : Set (ℝ × ℝ)), (1 : ℝ≥0∞)) ≤ _
      rw [hcard]
      calc
        1 ≤ 131072*(1:ℝ≥0∞) := by norm_num
        _ ≤ _ := mul_le_mul' le_rfl (h1.trans (le_add_of_nonneg_right (by positivity)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_UnitGraphCapacity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit Sobolev capacity estimate supplies a countable graph cover
with a quantitative quadratic cost and uniformly bounded diameters. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma unit_graph_capacity_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (huL2 : MemLp (fun p => u (euclideanPlaneCoordinates.symm p)) 2 volume)
    {A : Set (ℝ × ℝ)} (hA : A ⊆ closedBall 0 1)
    (hone : ∀ c ∈ A, 1 ≤ u (euclideanPlaneCoordinates.symm c))
    (f : (ℝ × ℝ) → ℝ) (t : ℝ)
    (hband : ∀ x ∈ A, f x ∈ Icc (t-1) (t+1)) :
    ∃ (U : Set (ℝ × ℝ)) (N : U → ℕ)
      (T : (x : U) → Fin (N x) → Set ((ℝ × ℝ) × ℝ)),
      U.Countable ∧ (fun x => (x,f x)) '' A ⊆ ⋃ x : U, ⋃ j, T x j ∧
      (∀ x j, ediam (T x j) ≤ 8) ∧
      (∑' x : U, ∑' j : Fin (N x), ediam (T x j)^2) ≤
        4194304 * (ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ) := by
  obtain ⟨U,r,hU,hr,hcover,hcost⟩ :=
    locally_sobolev_unit_ball_cover hu hw hLp huL2 hA hone
  obtain ⟨N,T,hcover',hdiam,hcost'⟩ := graph_cover_of_base_balls hU r zero_lt_one
    (by simpa using hr) hcover f t hband
  refine ⟨U,N,T,hU,hcover',?_,?_⟩
  · simpa using hdiam
  · calc
      _ ≤ 32*∑' x : U, ENNReal.ofReal (r x) := by simpa using hcost'
      _ ≤ 32*(131072*(ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ)) := mul_le_mul' le_rfl hcost
      _ = _ := by rw [← mul_assoc]; norm_num

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScaledGraphCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine dilation of a graph cover retains its diameter and cost
factors. The metric is the sup metric on the base and the vertical axis. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma graphAffine_lipschitz (c : ℝ × ℝ) (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    LipschitzWith ⟨s,hs⟩ (graphAffine c t s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist ((c,t)+s • x) ((c,t)+s • y) ≤ s*dist x y
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hs]

lemma scaled_graph_cover {ι : Type*} [Countable ι]
    (T : ι → Set ((ℝ × ℝ) × ℝ)) (c : ℝ × ℝ) (t : ℝ) {s D : ℝ}
    (hs : 0 < s) (hdiam : ∀ i, ediam (T i) ≤ ENNReal.ofReal D)
    {A : Set ((ℝ × ℝ) × ℝ)} (hcover : A ⊆ ⋃ i, T i) :
    graphAffine c t s '' A ⊆ ⋃ i, graphAffine c t s '' T i ∧
    (∀ i, ediam (graphAffine c t s '' T i) ≤ ENNReal.ofReal (s*D)) ∧
    (∑' i, ediam (graphAffine c t s '' T i)^2) ≤
      ENNReal.ofReal (s^2) * ∑' i, ediam (T i)^2 := by
  have hL := graphAffine_lipschitz c t hs.le
  refine ⟨?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i,mem_image_of_mem _ hi⟩
  · intro i
    calc
      _ ≤ ENNReal.ofReal s * ediam (T i) := by
        simpa only [ENNReal.ofReal_eq_coe_nnreal hs.le, NNReal.mk] using hL.ediam_image_le (T i)
      _ ≤ ENNReal.ofReal s * ENNReal.ofReal D := mul_le_mul' le_rfl (hdiam i)
      _ = _ := (ENNReal.ofReal_mul hs.le).symm
  · calc
      _ ≤ ∑' i, (ENNReal.ofReal s * ediam (T i))^2 := by
        apply ENNReal.tsum_le_tsum
        intro i
        apply pow_le_pow_left'
        simpa only [ENNReal.ofReal_eq_coe_nnreal hs.le, NNReal.mk] using hL.ediam_image_le (T i)
      _ = ENNReal.ofReal (s^2) * ∑' i, ediam (T i)^2 := by
        simp only [mul_pow, ← ENNReal.ofReal_pow hs.le]
        exact ENNReal.tsum_mul_left

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RescaledScalarBump
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed scalar cutoff translated to a level and rescaled to its
band width, with its exact derivative and support. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma rescaledScalarBump_one (t : ℝ) {s y : ℝ} (hs : 0 < s) (hy : |y-t| ≤ s) :
    rescaledScalarBump t s y = 1 := by
  apply scalarCapacityBump_one
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  exact hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarCutoffEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise energy control for the actual product-and-chain-rule
field. Constants depend only on the fixed smooth cutoffs. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

lemma scalar_cutoff_energy_algebra {u₀ u₁ d₀ d₁ a b c C : ℝ}
    (hC : 0 ≤ C) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hc : |c| ≤ C) (hd₀ : |d₀| ≤ C) (hd₁ : |d₁| ≤ C) :
    (a*b)^2 + (|a*(c*u₀)+d₀*b|+|a*(c*u₁)+d₁*b|)^2 ≤
      (1+8*C^2)*(1+(|u₀|+|u₁|)^2) := by
  have hab : |a*b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have hd (u d : ℝ) (hd : |d| ≤ C) : |a*(c*u)+d*b| ≤ C*|u|+C := by
    calc
      _ ≤ |a| * (|c| * |u|)+|d| * |b| := by simpa only [abs_mul] using abs_add_le (a*(c*u)) (d*b)
      _ ≤ 1*(C*|u|)+C*1 := add_le_add
        (mul_le_mul ha (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one)
        (mul_le_mul hd hb (abs_nonneg _) hC)
      _ = _ := by ring
  have hs : |a*(c*u₀)+d₀*b|+|a*(c*u₁)+d₁*b| ≤ C*((|u₀|+|u₁|)+2) := by
    nlinarith [hd u₀ d₀ hd₀, hd u₁ d₁ hd₁]
  have hs2 := sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg hC (by positivity)) |>.mpr hs
  have hab2 : (a*b)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (a*b)) zero_le_one).mpr hab
  have hquad : ((|u₀|+|u₁|)+2)^2 ≤ 8*(1+(|u₀|+|u₁|)^2) := by
    nlinarith [sq_nonneg ((|u₀|+|u₁|)-2)]
  have hmul := mul_le_mul_of_nonneg_left hquad (sq_nonneg C)
  nlinarith [sq_nonneg (|u₀|+|u₁|)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RescaledBandWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At graph scale s the domain and value rescalings cancel in the
chain-rule term. The remaining gradient is the original physical one. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma rescaledBandWitness_gradient {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (x : EuclideanPlane) (i : Fin 2) :
    (rescaledBandWitness hu W hsu a t hs hC).weakGrad x i =
      spatialCapacityBump x *
        (deriv scalarCapacityBump ((u (a+s • x)-t)/s) * W.weakGrad (a+s • x) i) +
      fderiv ℝ spatialCapacityBump x (EuclideanSpace.single i 1) *
        scalarCapacityBump ((u (a+s • x)-t)/s) := by
  change spatialCapacityBump x *
      (deriv (rescaledScalarBump t s) (u (a+s • x)) * (s • W.weakGrad (a+s • x)) i) +
      fderiv ℝ spatialCapacityBump x (EuclideanSpace.single i 1) *
        rescaledScalarBump t s (u (a+s • x)) = _
  rw [rescaledScalarBump_deriv, PiLp.smul_apply, smul_eq_mul]
  dsimp only [rescaledScalarBump]
  field_simp [hs.ne']

lemma rescaledBandWitness_one {u : EuclideanPlane → ℝ}
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s) {x : EuclideanPlane}
    (hx : euclideanPlaneCoordinates x ∈ Metric.closedBall 0 1)
    (hu : |u (a+s • x)-t| ≤ s) :
    spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s) = 1 := by
  rw [spatialCapacityBump_one hx]
  exact one_mul _ |>.trans (rescaledScalarBump_one t hs hu)

lemma rescaledBandWitness_zero {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C) {x : EuclideanPlane}
    (hx : 4 < ‖x‖ ∨ 2*s < |u (a+s • x)-t|) :
    spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s) = 0 ∧
      (rescaledBandWitness hu W hsu a t hs hC).weakGrad x = 0 := by
  rcases hx with hx | hx
  · obtain ⟨hz,hd⟩ := spatialCapacityBump_zero hx
    refine ⟨by rw [hz,zero_mul],?_⟩
    ext i
    simp only [rescaledBandWitness_gradient, hz, hd, zero_apply,
      zero_mul, add_zero, PiLp.zero_apply]
  · have hlarge : 2 < |(u (a+s • x)-t)/s| := by
      rw [abs_div, abs_of_pos hs]
      exact (lt_div_iff₀ hs).mpr hx
    obtain ⟨hz,hd⟩ := scalarCapacityBump_zero hlarge
    refine ⟨by rw [hz,mul_zero],?_⟩
    ext i
    simp only [rescaledBandWitness_gradient, hz, hd, mul_zero, zero_mul,
      add_zero, PiLp.zero_apply]

lemma rescaledBandWitness_energy {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (hηd : ∀ y, ‖fderiv ℝ spatialCapacityBump y‖ ≤ C) (x : EuclideanPlane) :
    let Q := rescaledBandWitness hu W hsu a t hs hC
    (spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s))^2 +
      (|Q.weakGrad x 0|+|Q.weakGrad x 1|)^2 ≤
      ({y : EuclideanPlane | ‖y‖ ≤ 4 ∧ |u (a+s • y)-t| ≤ 2*s}).indicator
        (fun y => (1+8*C^2)*(1+(|W.weakGrad (a+s • y) 0|+|W.weakGrad (a+s • y) 1|)^2)) x := by
  dsimp only
  by_cases hx : x ∈ {y : EuclideanPlane | ‖y‖ ≤ 4 ∧ |u (a+s • y)-t| ≤ 2*s}
  · rw [indicator_of_mem hx]
    rw [rescaledBandWitness_gradient, rescaledBandWitness_gradient]
    have hd (i : Fin 2) : |fderiv ℝ spatialCapacityBump x (EuclideanSpace.single i 1)| ≤ C := by
      have he := (fderiv ℝ spatialCapacityBump x).le_opNorm (EuclideanSpace.single i 1)
      simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
        using he.trans (mul_le_mul_of_nonneg_right (hηd x) (norm_nonneg _))
    apply scalar_cutoff_energy_algebra hC0
    · exact abs_le.mpr ⟨by linarith [spatialCapacityBump.nonneg (x := x)],
        spatialCapacityBump.le_one⟩
    · exact abs_le.mpr ⟨by linarith [scalarCapacityBump.nonneg (x := (u (a+s • x)-t)/s)],
        scalarCapacityBump.le_one⟩
    · exact hC _
    · exact hd 0
    · exact hd 1
  · rw [indicator_of_notMem hx]
    have hh : 4 < ‖x‖ ∨ 2*s < |u (a+s • x)-t| := by
      simpa only [mem_ofPred_eq, not_and_or, not_le] using hx
    obtain ⟨hz,hg⟩ := rescaledBandWitness_zero hu W hsu a t hs hC hh
    simp only [hz, hg, PiLp.zero_apply, abs_zero, zero_add, zero_pow (by decide : 2 ≠ 0), le_rfl]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AffineLIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative integrals under the physical affine change of variables,
including measurable indicators and possibly infinite energies. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma lintegral_planarAffine (a : EuclideanPlane) {s : ℝ} (hs : 0 < s)
    (f : EuclideanPlane → ℝ≥0∞) :
    (∫⁻ x, f (a+s • x)) = ENNReal.ofReal ((s^2)⁻¹) * ∫⁻ y, f y := by
  have he := (planarAffineHomeomorph a s hs.ne').toMeasurableEquiv.measurableEmbedding.lintegral_map (μ := volume) f
  change (∫⁻ y, f y ∂Measure.map (fun x : EuclideanPlane => a+s • x) volume) =
    ∫⁻ x, f (a+s • x) at he
  rw [← he, map_volume_planarAffine a hs, lintegral_smul_measure, smul_eq_mul]

lemma scaled_lintegral_planarAffine (a : EuclideanPlane) {s : ℝ} (hs : 0 < s)
    (f : EuclideanPlane → ℝ≥0∞) :
    ENNReal.ofReal (s^2) * (∫⁻ x, f (a+s • x)) = ∫⁻ y, f y := by
  rw [lintegral_planarAffine a hs, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg s), mul_inv_cancel₀ (pow_ne_zero 2 hs.ne'),
    ENNReal.ofReal_one, one_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevCapacityMass
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mass in the capacity estimate equals the integral of the actual
scalar and two-coordinate gradient densities on the physical plane. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolev_capacity_mass {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (huL2 : MemLp (fun p => u (euclideanPlaneCoordinates.symm p)) 2 volume)
    (V : EuclideanPlane → EuclideanPlane) :
    ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
        coordinateSobolevEnergy V univ =
      ∫⁻ x, ENNReal.ofReal ((u x)^2+(|V x 0|+|V x 1|)^2) := by
  have hi := ofReal_integral_eq_lintegral_ofReal huL2.integrable_sq
    (Eventually.of_forall fun p => sq_nonneg (u (euclideanPlaneCoordinates.symm p)))
  rw [hi, coordinateSobolevEnergy, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← euclideanPlaneCoordinates_symm_measurePreserving.lintegral_comp_emb
    euclideanPlaneCoordinates.symm.toHomeomorph.measurableEmbedding
    (fun x => ENNReal.ofReal ((u x)^2+(|V x 0|+|V x 1|)^2))]
  simp only [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  exact (lintegral_add_left
    (ENNReal.measurable_ofReal.comp ((hu.comp euclideanPlaneCoordinates.symm.continuous).pow 2).measurable)
    _).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RescaledBandEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the actual band-test energy and returning to physical
coordinates gives the local energy payment required by graph covers. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma rescaled_band_set (u : EuclideanPlane → ℝ) (a : EuclideanPlane) (t : ℝ)
    {s : ℝ} (hs : 0 < s) (x : EuclideanPlane) :
    (‖a+s • x-a‖ ≤ 4*s ∧ |u (a+s • x)-t| ≤ 2*s) ↔
      (‖x‖ ≤ 4 ∧ |u (a+s • x)-t| ≤ 2*s) := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  constructor <;> intro h
  · exact ⟨by nlinarith [h.1],h.2⟩
  · exact ⟨by nlinarith [h.1],h.2⟩

lemma rescaled_band_energy_payment {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (hηd : ∀ y, ‖fderiv ℝ spatialCapacityBump y‖ ≤ C) :
    let w := fun x => spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s)
    let Q := rescaledBandWitness hu W hsu a t hs hC
    ENNReal.ofReal (s^2) *
      (ENNReal.ofReal (∫ p, (w (euclideanPlaneCoordinates.symm p))^2) +
        coordinateSobolevEnergy Q.weakGrad univ) ≤
      ENNReal.ofReal (1+8*C^2) *
        ∫⁻ y in {y : EuclideanPlane | ‖y-a‖ ≤ 4*s ∧ |u y-t| ≤ 2*s},
          ENNReal.ofReal (1+(|W.weakGrad y 0|+|W.weakGrad y 1|)^2) := by
  dsimp only
  let w := fun x => spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s)
  let Q := rescaledBandWitness hu W hsu a t hs hC
  have hw : Continuous w := spatialCapacityBump.continuous.mul
    (scalarCapacityBump.continuous.comp
      ((hu.comp (planarAffineHomeomorph a s hs.ne').continuous).sub continuous_const |>.div_const s))
  have hLp : MemLp (fun p => w (euclideanPlaneCoordinates.symm p)) 2 volume :=
    (show MemLp w 2 volume by simpa only [Measure.restrict_univ] using Q.memLp).comp_measurePreserving
      euclideanPlaneCoordinates_symm_measurePreserving
  rw [sobolev_capacity_mass hw hLp Q.weakGrad]
  let S := {y : EuclideanPlane | ‖y-a‖ ≤ 4*s ∧ |u y-t| ≤ 2*s}
  have hS : MeasurableSet S :=
    (isClosed_le (continuous_id.sub continuous_const |>.norm) continuous_const).measurableSet.inter
      (isClosed_le ((hu.sub continuous_const).abs) continuous_const).measurableSet
  let g := fun y => ENNReal.ofReal (1+8*C^2) *
    ENNReal.ofReal (1+(|W.weakGrad y 0|+|W.weakGrad y 1|)^2)
  have hbound (x : EuclideanPlane) :
      ENNReal.ofReal ((w x)^2+(|Q.weakGrad x 0|+|Q.weakGrad x 1|)^2) ≤
        S.indicator g (a+s • x) := by
    have he := ENNReal.ofReal_le_ofReal (rescaledBandWitness_energy hu W hsu a t hs hC0 hC hηd x)
    by_cases hx : x ∈ {y : EuclideanPlane | ‖y‖ ≤ 4 ∧ |u (a+s • y)-t| ≤ 2*s}
    · have hy : a+s • x ∈ S := (rescaled_band_set u a t hs x).mpr hx
      rw [indicator_of_mem hy]
      simp only [indicator_of_mem hx] at he
      rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 1+8*C^2 by positivity)] at he
      exact he
    · have hy : a+s • x ∉ S := fun h => hx ((rescaled_band_set u a t hs x).mp h)
      rw [indicator_of_notMem hy]
      simpa only [indicator_of_notMem hx, ENNReal.ofReal_zero, w, Q] using he
  calc
    _ ≤ ENNReal.ofReal (s^2) * ∫⁻ x, S.indicator g (a+s • x) :=
      mul_le_mul' le_rfl (lintegral_mono hbound)
    _ = ∫⁻ y, S.indicator g y := scaled_lintegral_planarAffine a hs _
    _ = _ := by
      rw [lintegral_indicator hS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LocalGraphCapacity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual compact Sobolev graph has a small-diameter local cover.
Its cost is paid by the original energy in the enlarged graph cylinder. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_graph_capacity_cover {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (hηd : ∀ y, ‖fderiv ℝ spatialCapacityBump y‖ ≤ C)
    {A : Set (ℝ × ℝ)} (hA : A ⊆ closedBall 0 1)
    (hband : ∀ p ∈ A, |u (a+s • euclideanPlaneCoordinates.symm p)-t| ≤ s) :
    ∃ (U : Set (ℝ × ℝ)) (N : U → ℕ)
      (T : (x : U) → Fin (N x) → Set ((ℝ × ℝ) × ℝ)),
      U.Countable ∧
      (fun p => (euclideanPlaneCoordinates (a+s • euclideanPlaneCoordinates.symm p),
        u (a+s • euclideanPlaneCoordinates.symm p))) '' A ⊆ ⋃ x : U, ⋃ j, T x j ∧
      (∀ x j, ediam (T x j) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' x : U, ∑' j : Fin (N x), ediam (T x j)^2) ≤
        4194304 * ENNReal.ofReal (1+8*C^2) *
          ∫⁻ y in {y : EuclideanPlane | ‖y-a‖ ≤ 4*s ∧ |u y-t| ≤ 2*s},
            ENNReal.ofReal (1+(|W.weakGrad y 0|+|W.weakGrad y 1|)^2) := by
  let w := fun x => spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s)
  let Q := rescaledBandWitness hu W hsu a t hs hC
  have hw : Continuous w := spatialCapacityBump.continuous.mul
    (scalarCapacityBump.continuous.comp
      ((hu.comp (planarAffineHomeomorph a s hs.ne').continuous).sub continuous_const |>.div_const s))
  have hwLp : MemLp (fun p => w (euclideanPlaneCoordinates.symm p)) 2 volume :=
    (show MemLp w 2 volume by simpa only [Measure.restrict_univ] using Q.memLp).comp_measurePreserving
      euclideanPlaneCoordinates_symm_measurePreserving
  let f := fun p => (u (a+s • euclideanPlaneCoordinates.symm p)-t)/s
  have hone (p) (hp : p ∈ A) : 1 ≤ w (euclideanPlaneCoordinates.symm p) := by
    have h := rescaledBandWitness_one a t hs (by simpa using hA hp) (hband p hp)
    exact le_of_eq h.symm
  have hfb (p) (hp : p ∈ A) : f p ∈ Icc (0-1) (0+1) := by
    have habs : |f p| ≤ 1 := by
      rw [abs_div,abs_of_pos hs,div_le_one hs]
      exact hband p hp
    simpa only [mem_Icc, zero_sub, zero_add] using abs_le.mp habs
  have hQLp (R : ℝ) (i : Fin 2) : MemLp (fun x => Q.weakGrad x i) 2 (volume.restrict (ball 0 R)) :=
    (show MemLp (fun x => Q.weakGrad x i) 2 volume by
      simpa only [Measure.restrict_univ] using Q.weakGrad_component_memLp i).restrict _
  obtain ⟨U,N,T,hU,hcover,hdiam,hcost⟩ := unit_graph_capacity_cover hw Q.isWeakGrad hQLp
    hwLp hA hone f 0 hfb
  have : Countable U := hU.to_subtype
  let S : (Σ x : U, Fin (N x)) → Set ((ℝ × ℝ) × ℝ) := fun p => T p.1 p.2
  have hcoverS : (fun p => (p,f p)) '' A ⊆ ⋃ j, S j := by
    simpa only [S, iUnion_sigma] using hcover
  obtain ⟨hc,hd,hcst⟩ := scaled_graph_cover (D := 8) S (euclideanPlaneCoordinates a) t hs
    (by simpa using fun p : Σ x : U, Fin (N x) => hdiam p.1 p.2) hcoverS
  refine ⟨U,N,fun x j => graphAffine (euclideanPlaneCoordinates a) t s '' T x j,hU,?_,?_,?_⟩
  · have himage : (fun p => (euclideanPlaneCoordinates (a+s • euclideanPlaneCoordinates.symm p),
        u (a+s • euclideanPlaneCoordinates.symm p))) '' A =
      graphAffine (euclideanPlaneCoordinates a) t s '' ((fun p => (p,f p)) '' A) := by
      rw [image_image]
      congr 1
      funext p
      apply Prod.ext
      · simp only [graphAffine, map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
      · dsimp only [graphAffine,comp_apply,f]
        field_simp [hs.ne']
        ring
    rw [himage]
    simpa only [S,iUnion_sigma] using hc
  · intro x j
    have h := hd ⟨x,j⟩
    simpa only [S,mul_comm s 8] using h
  · have hcst' := hcst
    rw [ENNReal.tsum_sigma', ENNReal.tsum_sigma'] at hcst'
    calc
      _ ≤ ENNReal.ofReal (s^2) * ∑' x : U, ∑' j : Fin (N x), ediam (T x j)^2 := hcst'
      _ ≤ ENNReal.ofReal (s^2) * (4194304 *
          (ENNReal.ofReal (∫ p, (w (euclideanPlaneCoordinates.symm p))^2) +
            coordinateSobolevEnergy Q.weakGrad univ)) := mul_le_mul' le_rfl hcost
      _ = 4194304 * (ENNReal.ofReal (s^2) *
          (ENNReal.ofReal (∫ p, (w (euclideanPlaneCoordinates.symm p))^2) +
            coordinateSobolevEnergy Q.weakGrad univ)) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul' (show (4194304:ℝ≥0∞) ≤ 4194304 from le_rfl)
          (rescaled_band_energy_payment hu W hsu a t hs hC0 hC hηd)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ShrinkingLengthFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diameter covers for codimension-one fibers. The estimate is also
useful on the critical set, where a positive chart Jacobian is unavailable. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma hausdorff_one_fiber_le_liminf_cover
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y) (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (T : ℕ → ℕ → Set X) (hT : ∀ n k, ediam (T n k) ≤ r n)
    (hcover : ∀ n, A ⊆ ⋃ k, T n k) (y : Y) :
    (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤
      liminf (fun n => ∑' k, if y ∈ closure (f '' T n k) then ediam (T n k) else 0) atTop := by
  let S (n k : ℕ) := A ∩ f ⁻¹' {y} ∩ T n k
  have hS : ∀ n k, ediam (S n k) ≤ r n := fun n k =>
    (ediam_mono inter_subset_right).trans (hT n k)
  have hcov : ∀ n, A ∩ f ⁻¹' {y} ⊆ ⋃ k, S n k := by
    intro n x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover n hx.1)
    exact mem_iUnion.mpr ⟨k, hx, hk⟩
  have h := Measure.hausdorffMeasure_le_liminf_tsum 1 (A ∩ f ⁻¹' {y}) r hr S
    (.of_forall hS) (.of_forall hcov)
  simp only [ENNReal.rpow_one] at h
  apply h.trans
  apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  apply Eventually.of_forall
  intro n
  apply ENNReal.tsum_le_tsum
  intro k
  split_ifs with hy
  · exact ediam_mono inter_subset_right
  · have hempty : S n k = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxT⟩
      exact hy (subset_closure ⟨x, hxT, hx.2⟩)
    simp only [hempty, ediam_empty]
    exact le_rfl

lemma iSup_nonempty_ediam_sq {X : Type*} [EMetricSpace X] (S : Set X) :
    (⨆ _ : S.Nonempty, ediam S ^ (2 : ℝ)) = ediam S ^ (2 : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · simp only [iSup_pos hS]

lemma exists_small_quadratic_hausdorff_cover
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (r ε : ℝ≥0∞) (hr : 0 < r) (hε : 0 < ε) :
    ∃ T : ℕ → Set X, A ⊆ ⋃ k, T k ∧ (∀ k, ediam (T k) ≤ r) ∧
      (∑' k, ediam (T k) ^ (2 : ℕ)) < (μH[2] : Measure X) A + ε := by
  have hle : (⨅ (T : ℕ → Set X) (_ : A ⊆ ⋃ k, T k) (_ : ∀ k, ediam (T k) ≤ r),
      ∑' k, ⨆ _ : (T k).Nonempty, ediam (T k) ^ (2 : ℝ)) ≤ (μH[2] : Measure X) A := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hlt := hle.trans_lt (ENNReal.lt_add_right hA.ne hε.ne')
  simp only [iInf_lt_iff] at hlt
  obtain ⟨T, hc, hd, hcost⟩ := hlt
  refine ⟨T, hc, hd, ?_⟩
  simp_rw [iSup_nonempty_ediam_sq] at hcost
  simpa only [ENNReal.rpow_two] using hcost

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CurveLowerDistance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A strict derivative gives lower distance bounds on a small interval.
These bounds will supply the reverse arclength inequality. -/
open Set Function Filter Topology
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma real_clm_eq_toSpanSingleton (d : ℝ →L[ℝ] ℂ) :
    d = ContinuousLinearMap.toSpanSingleton ℝ (d 1) := by
  apply ContinuousLinearMap.ext
  intro t
  change d t = t • d 1
  simpa using d.map_smul t (1 : ℝ)

lemma norm_real_clm_apply (d : ℝ →L[ℝ] ℂ) (t : ℝ) :
    ‖d t‖ = ‖d‖ * |t| := by
  have hn := congrArg norm (real_clm_eq_toSpanSingleton d)
  rw [ContinuousLinearMap.norm_toSpanSingleton] at hn
  have ht : d t = t • d 1 := by simpa using d.map_smul t (1 : ℝ)
  rw [ht, norm_smul, Real.norm_eq_abs, ← hn, mul_comm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CurveHausdorffLower
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower distance estimates on countably many pieces give the reverse
arclength bound for an injective C1 curve. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma lower_distance_hausdorff
    {γ : ℝ → ℂ} {U S : Set ℝ} (hSU : S ⊆ U) (k : ℝ≥0)
    (h : ∀ a ∈ U, ∀ b ∈ U, (k : ℝ) * dist a b ≤ dist (γ a) (γ b)) :
    (k : ℝ≥0∞) * volume S ≤ (μH[1] : Measure ℂ) (γ '' S) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkR : (0 : ℝ) < k := by exact_mod_cast pos_iff_ne_zero.mpr hk
  let T : Set U := {x | (x : ℝ) ∈ S}
  let g : U → ℂ := fun x => γ x
  have hg : AntilipschitzWith k⁻¹ g := by
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    change dist (a : ℝ) (b : ℝ) ≤ (k⁻¹ : ℝ≥0) * dist (γ a) (γ b)
    rw [NNReal.coe_inv, inv_mul_eq_div, le_div_iff₀ hkR]
    simpa only [mul_comm] using h a a.property b b.property
  have hT : Subtype.val '' T = S := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, hSU hx⟩, hx, rfl⟩
  have hmeasure : (μH[1] : Measure U) T = volume S := by
    rw [← isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)), hT,
      hausdorffMeasure_real]
  have himage : g '' T = γ '' S := by
    change (γ ∘ Subtype.val) '' T = γ '' S
    rw [image_comp, hT]
  have hb := hg.le_hausdorffMeasure_image (by norm_num : (0 : ℝ) ≤ 1) T
  rw [hmeasure, himage, ENNReal.rpow_one, ENNReal.coe_inv hk] at hb
  have hk0 : (k : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hk
  calc
    (k : ℝ≥0∞) * volume S ≤ (k : ℝ≥0∞) * ((k : ℝ≥0∞)⁻¹ * (μH[1] : Measure ℂ) (γ '' S)) :=
      mul_le_mul' le_rfl hb
    _ = (μH[1] : Measure ℂ) (γ '' S) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hk0 ENNReal.coe_ne_top, one_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LineDerivativeLocality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Classical one-dimensional derivatives are local on arbitrary level sets,
outside the countable set of one-sided isolated points. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma ae_deriv_zero_of_eqOn_const {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ}
    (h : EqOn f (fun _ => c) S) :
    ∀ᵐ x ∂volume, x ∈ S → deriv f x = 0 := by
  have hnull : volume {x ∈ S | 𝓝[S ∩ Ioi x] x = ⊥} = 0 :=
    countable_setOfPred_isolated_right_within.measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxs
  let : NeBot (𝓝[S ∩ Ioi x] x) := ⟨fun hbot => hx ⟨hxs, hbot⟩⟩
  have hfreq : ∃ᶠ y in 𝓝[S ∩ Ioi x] x, f y = c := by
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h hy.1
  apply deriv_zero_of_frequently_const
  exact hfreq.filter_mono (nhdsWithin_mono _ (fun y hy => ne_of_gt hy.2))

lemma ae_derivative_eq_of_eqOn {f g : ℝ → ℝ} {S : Set ℝ} (h : EqOn f g S) :
    ∀ᵐ x ∂volume, x ∈ S → ∀ a b : ℝ, HasDerivAt f a x → HasDerivAt g b x → a = b := by
  have he : EqOn (fun x => f x-g x) (fun _ => (0:ℝ)) S := fun x hx => sub_eq_zero.mpr (h hx)
  filter_upwards [ae_deriv_zero_of_eqOn_const he] with x hx hxs a b ha hb
  have hd := (ha.sub hb).deriv
  have hz := hx hxs
  change deriv (f-g) x = 0 at hz
  rw [hd] at hz
  exact sub_eq_zero.mp hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ApproximateCurveDerivative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A planar curve approximated by a linear map on an arbitrary real set
has the same derivative bound almost everywhere on that set. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma ae_curve_derivative_sub_le {γ : ℝ → ℂ} {A : ℝ →L[ℝ] ℂ}
    {S : Set ℝ} {δ : ℝ≥0} (ha : ApproximatesLinearOn γ A S δ)
    {d : ℝ → ℝ →L[ℝ] ℂ} :
    ∀ᵐ x ∂volume, x ∈ S → HasFDerivWithinAt γ (d x) S x → ‖d x-A‖ ≤ δ := by
  have hnull : volume {x ∈ S | 𝓝[S ∩ Ioi x] x = ⊥} = 0 :=
    countable_setOfPred_isolated_right_within.measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxS hd
  let : NeBot (𝓝[S ∩ Ioi x] x) := ⟨fun hbot => hx ⟨hxS, hbot⟩⟩
  have hh : HasDerivWithinAt (γ-(A : ℝ → ℂ)) ((d x-A) 1) S x :=
    (hd.sub A.hasFDerivAt.hasFDerivWithinAt).hasDerivWithinAt
  have hl : Tendsto (fun y => ‖slope (γ-(A : ℝ → ℂ)) x y‖)
      (𝓝[S ∩ Ioi x] x) (𝓝 ‖(d x-A) 1‖) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hh).norm.mono_left
      (nhdsWithin_mono _ (fun y hy => ⟨hy.1, ne_of_gt hy.2⟩))
  have hbound : ∀ᶠ y in 𝓝[S ∩ Ioi x] x, ‖slope (γ-(A : ℝ → ℂ)) x y‖ ≤ (δ:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hdist := ha.lipschitzOnWith.dist_le_mul y hy.1 x hxS
    rw [dist_eq_norm, Real.dist_eq] at hdist
    rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs]
    apply (inv_mul_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hy.2)))).mpr
    simpa only [vsub_eq_sub, mul_comm] using hdist
  have hb := le_of_tendsto hl hbound
  simpa only [norm_real_clm_apply, abs_one, mul_one] using hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ApproximateCurveDistances
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Upper and lower distance control for plane curves on differentiability pieces. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma approximate_curve_lower_distance {γ : ℝ → ℂ} {A : ℝ →L[ℝ] ℂ}
    {S : Set ℝ} {δ : ℝ≥0} (ha : ApproximatesLinearOn γ A S δ) :
    ∀ x ∈ S, ∀ y ∈ S,
      (Real.toNNReal (‖A‖-(δ:ℝ)) : ℝ) * dist x y ≤ dist (γ x) (γ y) := by
  intro x hx y hy
  have hr := ha x hx y hy
  have ht : ‖A (x-y)‖ ≤ ‖γ x-γ y‖ + ‖γ x-γ y-A (x-y)‖ := by
    have he : A (x-y) = (γ x-γ y)-(γ x-γ y-A (x-y)) := by abel
    nth_rw 1 [he]
    exact norm_sub_le _ _
  rw [norm_real_clm_apply] at ht
  rw [Real.dist_eq, dist_eq_norm]
  by_cases hp : 0 ≤ ‖A‖-(δ:ℝ)
  · rw [Real.coe_toNNReal _ hp]
    rw [Real.norm_eq_abs] at hr
    nlinarith
  · rw [Real.toNNReal_of_nonpos (le_of_not_ge hp), NNReal.coe_zero, zero_mul]
    exact norm_nonneg _

lemma differentiable_curve_distance_partition {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hd : ∀ x ∈ S, HasFDerivWithinAt γ (d x) S x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : ℕ → Set ℝ) (K k : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (B n)) ∧ Pairwise (Disjoint on B) ∧ (⋃ n, B n) = S ∧
      (∀ n, LipschitzOnWith (K n) γ (B n)) ∧
      (∀ n x, x ∈ B n → ∀ y ∈ B n, (k n : ℝ)*dist x y ≤ dist (γ x) (γ y)) ∧
      ∀ n, ∀ᵐ x ∂volume.restrict (B n),
        (K n : ℝ) ≤ ‖d x‖+ε ∧ ‖d x‖ ≤ (k n : ℝ)+ε := by
  let δ : ℝ≥0 := ⟨ε/2, (half_pos hε).le⟩
  obtain ⟨t, A, htDisj, htMeas, htCover, htApprox, _⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt γ S d
      hd (fun _ => δ)
      (fun _ => ne_of_gt (show 0 < δ by exact half_pos hε))
  let B : ℕ → Set ℝ := fun n => S ∩ t n
  let K : ℕ → ℝ≥0 := fun n => ‖A n‖₊+δ
  let k : ℕ → ℝ≥0 := fun n => Real.toNNReal (‖A n‖-(δ:ℝ))
  have hB (n : ℕ) : MeasurableSet (B n) := hS.inter (htMeas n)
  refine ⟨B, K, k, hB, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hij => (htDisj hij).mono inter_subset_right inter_subset_right
  · simp only [B, ← inter_iUnion, inter_eq_left.mpr htCover]
  · intro n
    exact lipschitzOnWith_iff_restrict.mpr (htApprox n).lipschitz
  · intro n
    exact approximate_curve_lower_distance (htApprox n)
  · intro n
    filter_upwards [ae_restrict_of_ae (ae_curve_derivative_sub_le (htApprox n)),
      ae_restrict_mem (hB n)] with x hx hxB
    have hnorm := hx hxB ((hd x hxB.1).mono inter_subset_left)
    have h1 := norm_sub_norm_le (A n) (d x)
    have h2 := norm_sub_norm_le (d x) (A n)
    rw [norm_sub_rev] at h1
    have hk : ‖A n‖-(δ:ℝ) ≤ (k n : ℝ) := Real.le_coe_toNNReal _
    change ‖A n‖+(ε/2) ≤ ‖d x‖+ε ∧ ‖d x‖ ≤ (k n : ℝ)+ε
    change ‖d x-A n‖ ≤ ε/2 at hnorm
    change ‖A n‖-ε/2 ≤ (k n : ℝ) at hk
    constructor <;> linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DifferentiableCurveLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arclength on a bounded Borel set where a plane curve is differentiable.
No continuity of the derivative or open-domain assumption is used. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma differentiable_curve_upper_error {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hd : ∀ x ∈ S, HasFDerivWithinAt γ (d x) S x)
    {ε : ℝ} (hε : 0 < ε) :
    (μH[1] : Measure ℂ) (γ '' S) ≤
      (∫⁻ t in S, ENNReal.ofReal ‖d t‖) + ENNReal.ofReal ε * volume S := by
  obtain ⟨B, K, k, hB, hdj, hcov, hLip, _, hnorm⟩ :=
    differentiable_curve_distance_partition hS hd hε
  calc
    (μH[1] : Measure ℂ) (γ '' S) = (μH[1] : Measure ℂ) (⋃ n, γ '' B n) := by
      rw [← image_iUnion, hcov]
    _ ≤ ∑' n, (μH[1] : Measure ℂ) (γ '' B n) := measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ t in B n, ENNReal.ofReal (‖d t‖+ε) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hb : (μH[1] : Measure ℂ) (γ '' B n) ≤ (K n : ℝ≥0∞)*volume (B n) := by
        simpa only [ENNReal.rpow_one, hausdorffMeasure_real] using
          (hLip n).hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1)
      apply hb.trans
      rw [← Measure.restrict_apply_univ, ← lintegral_const]
      apply lintegral_mono_ae
      filter_upwards [hnorm n] with t ht
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal ht.1
    _ = ∫⁻ t in S, ENNReal.ofReal (‖d t‖+ε) := by
      rw [← lintegral_iUnion hB hdj, hcov]
    _ = (∫⁻ t in S, ENNReal.ofReal ‖d t‖)+ENNReal.ofReal ε*volume S := by
      simp_rw [ENNReal.ofReal_add (norm_nonneg _) hε.le]
      rw [lintegral_add_right (f := fun t => ENNReal.ofReal ‖d t‖)
        (g := fun _ => ENNReal.ofReal ε) measurable_const]
      simp only [lintegral_const, Measure.restrict_apply_univ]

lemma differentiable_curve_lower_error {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hd : ∀ x ∈ S, HasFDerivWithinAt γ (d x) S x)
    (hi : InjOn γ S) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) ≤
      (μH[1] : Measure ℂ) (γ '' S) + ENNReal.ofReal ε * volume S := by
  obtain ⟨B, K, k, hB, hdj, hcov, _, hdist, hnorm⟩ :=
    differentiable_curve_distance_partition hS hd hε
  have hBS (n : ℕ) : B n ⊆ S := hcov ▸ subset_iUnion B n
  have hcont : ContinuousOn γ S := fun x hx => (hd x hx).continuousWithinAt
  have him (n : ℕ) : MeasurableSet (γ '' B n) :=
    (hB n).image_of_continuousOn_injOn (hcont.mono (hBS n)) (hi.mono (hBS n))
  have hidj : Pairwise (Disjoint on fun n => γ '' B n) := fun i j hij =>
    (hdj hij).image hi (hBS i) (hBS j)
  calc
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) = ∑' n, ∫⁻ t in B n, ENNReal.ofReal ‖d t‖ := by
      rw [← lintegral_iUnion hB hdj, hcov]
    _ ≤ ∑' n, ((μH[1] : Measure ℂ) (γ '' B n)+ENNReal.ofReal ε*volume (B n)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hb : (∫⁻ t in B n, ENNReal.ofReal ‖d t‖) ≤
          ((k n : ℝ≥0∞)+ENNReal.ofReal ε)*volume (B n) := by
        rw [← Measure.restrict_apply_univ, ← lintegral_const]
        apply lintegral_mono_ae
        filter_upwards [hnorm n] with t ht
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (NNReal.coe_nonneg _) hε.le]
        exact ENNReal.ofReal_le_ofReal ht.2
      rw [add_mul] at hb
      exact hb.trans (add_le_add (lower_distance_hausdorff (Subset.rfl) (k n) (hdist n)) le_rfl)
    _ = (∑' n, (μH[1] : Measure ℂ) (γ '' B n))+ENNReal.ofReal ε*(∑' n, volume (B n)) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ = (μH[1] : Measure ℂ) (γ '' S)+ENNReal.ofReal ε*volume S := by
      rw [← measure_iUnion hidj him, ← measure_iUnion hdj hB, ← image_iUnion, hcov]

lemma differentiable_curve_hausdorff_eq {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S)
    (hd : ∀ x ∈ S, HasFDerivWithinAt γ (d x) S x) (hi : InjOn γ S) :
    (μH[1] : Measure ℂ) (γ '' S) = ∫⁻ t in S, ENNReal.ofReal ‖d t‖ := by
  have hεlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1:ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hvan : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1:ℝ))*volume S) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hεlim
      (Or.inr (hb.measure_lt_top (μ := volume)).ne)
  apply le_antisymm
  · have ht := (tendsto_const_nhds (x := ∫⁻ t in S, ENNReal.ofReal ‖d t‖)).add hvan
    simp only [add_zero] at ht
    exact ge_of_tendsto' ht (fun n => differentiable_curve_upper_error hS hd
      (ε := 1/(n+1:ℝ)) (one_div_pos.mpr (by positivity)))
  · have ht := (tendsto_const_nhds (x := (μH[1] : Measure ℂ) (γ '' S))).add hvan
    simp only [add_zero] at ht
    exact ge_of_tendsto' ht (fun n => differentiable_curve_lower_error hS hd hi
      (ε := 1/(n+1:ℝ)) (one_div_pos.mpr (by positivity)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_InverseOnDifferentiation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverses on bi-Lipschitz measurable pieces retain the exact within-set derivative. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverseOn_lipschitz {F : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) :
    LipschitzOnWith K (invFunOn F S) (F '' S) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have h := hF.le_mul_dist ⟨invFunOn F S y, invFunOn_mem hy⟩
    ⟨invFunOn F S z, invFunOn_mem hz⟩
  simpa only [Subtype.dist_eq, domRestrict_apply, invFunOn_eq hy, invFunOn_eq hz] using h

lemma inverseOn_injOn {F : ℂ → ℂ} {S : Set ℂ} : InjOn (invFunOn F S) (F '' S) := by
  intro y hy z hz he
  have h := congrArg F he
  rwa [invFunOn_eq hy, invFunOn_eq hz] at h

lemma inverseOn_hasFDerivWithinAt {F : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) {y : ℂ} (hy : y ∈ F '' S)
    (A : ℂ ≃L[ℝ] ℂ)
    (hd : HasFDerivWithinAt F (A : ℂ →L[ℝ] ℂ) S (invFunOn F S y)) :
    HasFDerivWithinAt (invFunOn F S) (A.symm : ℂ →L[ℝ] ℂ) (F '' S) y := by
  have hc := (inverseOn_lipschitz hF).continuousOn y hy
  have hm : MapsTo (invFunOn F S) (F '' S) S := fun _ hv => invFunOn_mem hv
  apply HasFDerivWithinAt.of_local_left_inverse (hc.tendsto_nhdsWithin hm) hd hy
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact invFunOn_eq hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RegularMapPieces
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A planar map with invertible derivatives splits into countably many
measurable pieces with quantitative forward and inverse Lipschitz bounds. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma linearInverseApproxRadius_ne_zero (A : ℂ →L[ℝ] ℂ) :
    linearInverseApproxRadius A ≠ 0 := by
  unfold linearInverseApproxRadius
  apply inv_ne_zero
  positivity

lemma linearInverseApproxRadius_lt (e : ℂ ≃L[ℝ] ℂ) :
    linearInverseApproxRadius (e : ℂ →L[ℝ] ℂ) < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
  unfold linearInverseApproxRadius
  rw [ContinuousLinearMap.inverse_equiv]
  have hN : 0 < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊ := by exact_mod_cast e.symm.norm_pos
  apply (inv_lt_inv₀ (by positivity) hN).mpr
  calc
    _ < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊+1 := lt_add_one _
    _ ≤ (‖(e.symm : ℂ →L[ℝ] ℂ)‖₊+1)+(‖(e.symm : ℂ →L[ℝ] ℂ)‖₊+1) :=
      le_add_of_nonneg_right (by positivity)
    _ = _ := (two_mul _).symm

lemma regular_map_measurable_pieces {F : ℂ → ℂ} {DF : ℂ → ℂ →L[ℝ] ℂ}
    {S : Set ℂ} (hS : MeasurableSet S) (hne : S.Nonempty)
    (hd : ∀ p ∈ S, HasFDerivAt F (DF p) p)
    (hi : ∀ p ∈ S, (DF p).IsInvertible) :
    ∃ (B : ℕ → Set ℂ) (L K : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (B n)) ∧ Pairwise (Disjoint on B) ∧ (⋃ n, B n) = S ∧
      ∀ n, LipschitzOnWith (L n) F (B n) ∧ AntilipschitzWith (K n) ((B n).domRestrict F) := by
  obtain ⟨t, A, htDisj, htMeas, htCover, htApprox, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F S DF
      (fun p hp => (hd p hp).hasFDerivWithinAt) linearInverseApproxRadius
      linearInverseApproxRadius_ne_zero
  have hAi (n : ℕ) : (A n).IsInvertible := by
    obtain ⟨p, hp, hAp⟩ := hA hne n
    rw [hAp]
    exact hi p hp
  choose e he using hAi
  let B : ℕ → Set ℂ := fun n => S ∩ t n
  let L : ℕ → ℝ≥0 := fun n => ‖A n‖₊+linearInverseApproxRadius (A n)
  let K : ℕ → ℝ≥0 := fun n =>
    (‖((e n).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹-linearInverseApproxRadius (A n))⁻¹
  refine ⟨B, L, K, (fun n => hS.inter (htMeas n)), ?_, ?_, ?_⟩
  · exact fun i j hij => (htDisj hij).mono inter_subset_right inter_subset_right
  · simp only [B, ← inter_iUnion, inter_eq_left.mpr htCover]
  · intro n
    refine ⟨lipschitzOnWith_iff_restrict.mpr (htApprox n).lipschitz, ?_⟩
    have hh := htApprox n
    rw [← he n] at hh
    dsimp only [K, B]
    rw [← he n]
    exact hh.antilipschitz (Or.inr (linearInverseApproxRadius_lt (e n)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableLinearInverse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse of a planar linear map, with zero at singular maps, is Borel measurable. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma measurable_planar_linear_inverse :
    Measurable (ContinuousLinearMap.inverse : (ℂ →L[ℝ] ℂ) → (ℂ →L[ℝ] ℂ)) := by
  classical
  let U : Set (ℂ →L[ℝ] ℂ) := {A | A.IsInvertible}
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen
  have hc : ContinuousOn ContinuousLinearMap.inverse U := by
    intro A hA
    exact (hA.contDiffAt_map_inverse (n := 0)).continuousAt.continuousWithinAt
  have hm := hc.measurable_piecewise (g := fun _ => (0 : ℂ →L[ℝ] ℂ)) continuousOn_const hU.measurableSet
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext A
  by_cases hA : A ∈ U
  · simp only [piecewise_eq_of_mem U _ _ hA]
  · rw [piecewise_eq_of_notMem U _ _ hA, ContinuousLinearMap.inverse_of_not_isInvertible hA]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurablePieceInverse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable zero extensions of the inverse on a Borel image piece. -/
open Set Function MeasureTheory
open scoped Topology NNReal Classical
noncomputable section
namespace CircleDomainRigidity

lemma measurable_inverseOnPiece {F : ℂ → ℂ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (hT : MeasurableSet T) (hTS : T ⊆ F '' S) :
    Measurable (inverseOnPiece F S T) :=
  ((inverseOn_lipschitz hF).continuousOn.mono hTS).measurable_piecewise continuousOn_const hT

lemma inverseOnPiece_eq {F : ℂ → ℂ} {S T : Set ℂ} {y : ℂ} (hy : y ∈ T) :
    inverseOnPiece F S T y = invFunOn F S y :=
  piecewise_eq_of_mem T _ _ hy

lemma measurable_inversePieceDifferential {F : ℂ → ℂ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (hT : MeasurableSet T) (hTS : T ⊆ F '' S) :
    Measurable (fun y => (fderiv ℝ F (inverseOnPiece F S T y)).inverse) :=
  measurable_planar_linear_inverse.comp ((measurable_fderiv ℝ F).comp (measurable_inverseOnPiece hF hT hTS))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_InverseOnDerivativeField
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual derivative field of an inverse on a regular measurable piece. -/
open Set Function MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverseOn_derivative_field {F : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F))
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    {y : ℂ} (hy : y ∈ F '' S) :
    HasFDerivWithinAt (invFunOn F S) (fderiv ℝ F (invFunOn F S y)).inverse (F '' S) y := by
  have hx : invFunOn F S y ∈ S := invFunOn_mem hy
  obtain ⟨A, hA⟩ := hi _ hx
  rw [← hA, ContinuousLinearMap.inverse_equiv]
  apply inverseOn_hasFDerivWithinAt hF hy A
  rw [hA]
  exact (hd _ hx).hasFDerivAt.hasFDerivWithinAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedDifferentiableCurve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted arclength on a bounded Borel parameter set with actual within-set derivatives. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma differentiable_curve_length_map_measure {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hi : InjOn γ S)
    (hd : ∀ t ∈ S, HasFDerivWithinAt γ (d t) S t) :
    Measure.map (curveOnSet S γ)
      ((volume.restrict S).withDensity (fun t => ENNReal.ofReal ‖d t‖)) =
      (μH[1] : Measure ℂ).restrict (γ '' S) := by
  classical
  let g := curveOnSet S γ
  have hc : ContinuousOn γ S := fun t ht => (hd t ht).continuousWithinAt
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const hS
  apply Measure.ext
  intro B hB
  have hT : MeasurableSet (S ∩ g ⁻¹' B) := hS.inter (hg hB)
  have him : γ '' (S ∩ g ⁻¹' B) = B ∩ γ '' S := by
    ext z
    constructor
    · rintro ⟨t, ⟨ht, htB⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht] using htB,
        ⟨t, ht, rfl⟩⟩
    · rintro ⟨hz, t, ht, rfl⟩
      refine ⟨t, ⟨ht, ?_⟩, rfl⟩
      simpa only [mem_preimage, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht] using hz
  change Measure.map g _ B = _
  rw [Measure.map_apply hg hB, withDensity_apply _ (hg hB),
    Measure.restrict_restrict (hg hB), Measure.restrict_apply hB]
  rw [inter_comm (g ⁻¹' B) S,
    ← differentiable_curve_hausdorff_eq hT (hb.subset inter_subset_left)
      (fun t ht => (hd t ht.1).mono inter_subset_left) (hi.mono inter_subset_left), him]

lemma weighted_differentiable_curve_length {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hi : InjOn γ S)
    (hd : ∀ t ∈ S, HasFDerivWithinAt γ (d t) S t)
    (hm : AEMeasurable (fun t => ENNReal.ofReal ‖d t‖) (volume.restrict S))
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in γ '' S, q z ∂μH[1]) =
      ∫⁻ t in S, q (γ t)*ENNReal.ofReal ‖d t‖ := by
  classical
  let g := curveOnSet S γ
  have hc : ContinuousOn γ S := fun t ht => (hd t ht).continuousWithinAt
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const hS
  rw [← differentiable_curve_length_map_measure hS hb hi hd, lintegral_map hq hg,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun t => q (g t)) hm (hq.comp hg).aemeasurable]
  apply setLIntegral_congr_fun hS
  intro t ht
  simp only [Pi.mul_apply, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht, mul_comm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_VerticalLevelCurve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical parameter curves of a C1 inverse level chart. -/
open Set Function MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma coareaVerticalLine_contDiff (t : ℝ) : ContDiff ℝ 1 (coareaVerticalLine t) :=
  contDiff_const.add (ContinuousLinearMap.toSpanSingleton ℝ Complex.I).contDiff

lemma coareaVerticalLine_hasFDerivAt (t s : ℝ) :
    HasFDerivAt (coareaVerticalLine t) (ContinuousLinearMap.toSpanSingleton ℝ Complex.I) s := by
  simpa only [coareaVerticalLine] using!
    (ContinuousLinearMap.toSpanSingleton ℝ Complex.I).hasFDerivAt.const_add (t : ℂ)

lemma coareaVerticalLine_injective (t : ℝ) : Injective (coareaVerticalLine t) := by
  intro a b h
  simpa only [coareaVerticalLine_im] using congrArg Complex.im h

lemma vertical_slice_bounded {T : Set ℂ} (hT : IsBounded T) (t : ℝ) :
    IsBounded ((coareaVerticalLine t) ⁻¹' T) := by
  apply (hT.isCompact_closure.image Complex.continuous_im).isBounded.subset
  intro s hs
  exact ⟨coareaVerticalLine t s, subset_closure hs, coareaVerticalLine_im t s⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedInversePieceCurve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted arclength on vertical fibers of the inverse of a regular measurable piece. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverse_piece_vertical_derivative_norm (B : ℂ →L[ℝ] ℂ) :
    ‖B.comp (ContinuousLinearMap.toSpanSingleton ℝ Complex.I)‖ = ‖B Complex.I‖ := by
  have h := norm_real_clm_apply (B.comp (ContinuousLinearMap.toSpanSingleton ℝ Complex.I)) 1
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, abs_one, mul_one] using h.symm

lemma weighted_inverse_piece_vertical_curve {F : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F))
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    {T : Set ℂ} (hT : MeasurableSet T) (hb : IsBounded T) (hTS : T ⊆ F '' S)
    (t : ℝ) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in ((invFunOn F S) ∘ coareaVerticalLine t) '' ((coareaVerticalLine t) ⁻¹' T), q z ∂μH[1]) =
    ∫⁻ s in (coareaVerticalLine t) ⁻¹' T,
      q (invFunOn F S (coareaVerticalLine t s)) *
      ENNReal.ofReal ‖(fderiv ℝ F (invFunOn F S (coareaVerticalLine t s))).inverse Complex.I‖ := by
  let J := (coareaVerticalLine t) ⁻¹' T
  let D : ℝ → ℝ →L[ℝ] ℂ := fun s =>
    (fderiv ℝ F (invFunOn F S (coareaVerticalLine t s))).inverse.comp
      (ContinuousLinearMap.toSpanSingleton ℝ Complex.I)
  have hJ : MeasurableSet J := hT.preimage (coareaVerticalLine_contDiff t).continuous.measurable
  have hder : ∀ s ∈ J, HasFDerivWithinAt ((invFunOn F S) ∘ coareaVerticalLine t) (D s) J s := by
    intro s hs
    exact ((inverseOn_derivative_field hF hd hi (hTS hs)).mono hTS).comp s
      (coareaVerticalLine_hasFDerivAt t s).hasFDerivWithinAt (fun _ hx => hx)
  have hinj : InjOn ((invFunOn F S) ∘ coareaVerticalLine t) J := by
    intro a ha b hb he
    exact coareaVerticalLine_injective t (inverseOn_injOn (hTS ha) (hTS hb) he)
  have hnorm (s : ℝ) : ‖D s‖ =
      ‖(fderiv ℝ F (invFunOn F S (coareaVerticalLine t s))).inverse Complex.I‖ :=
    inverse_piece_vertical_derivative_norm _
  have hBm := (ContinuousLinearMap.measurable_apply Complex.I).comp
    (measurable_inversePieceDifferential hF hT hTS)
  have hm : AEMeasurable (fun s => ENNReal.ofReal ‖D s‖) (volume.restrict J) := by
    apply (((hBm.comp (coareaVerticalLine_contDiff t).continuous.measurable).norm.ennreal_ofReal).aemeasurable).congr
    filter_upwards [ae_restrict_mem hJ] with s hs
    dsimp only [Function.comp_def]
    rw [hnorm, inverseOnPiece_eq hs]
  rw [weighted_differentiable_curve_length hJ (vertical_slice_bounded hb t) hinj hder hm hq]
  apply setLIntegral_congr_fun hJ
  intro s _
  dsimp only [Function.comp_def]
  rw [hnorm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LocalPartialMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local L2 hypotheses supply global completed measurability of each weak partial. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma local_partial_aestronglyMeasurable {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (i : Fin 2) :
    AEStronglyMeasurable (fun p => V p i) volume := by
  have h : AEStronglyMeasurable (fun p => V p i)
      (volume.restrict (⋃ n : ℕ, ball (0 : EuclideanPlane) n)) :=
    AEStronglyMeasurable.iUnion (fun n : ℕ => (hLp n i).aestronglyMeasurable)
  simpa only [Metric.iUnion_ball_nat, Measure.restrict_univ] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_EqualScaleCellSeparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite coloring separates the enlarged equal-scale cells.
This supplies bounded overlap without assuming measure doubling. -/
open Set
noncomputable section
namespace CircleDomainRigidity

lemma equal_scale_cell_separation {s : ℝ} (hs : 0 < s) {k l : ℤ} (hkl : k ≠ l)
    (r : ℝ) {x y : ℝ}
    (hx : x ∈ Icc ((16*(k:ℝ)+r)*s) ((16*(k:ℝ)+r+1)*s))
    (hy : y ∈ Icc ((16*(l:ℝ)+r)*s) ((16*(l:ℝ)+r+1)*s)) :
    8*s < |x-y| := by
  rcases lt_or_gt_of_ne hkl with h | h
  · have hi : (k:ℝ)+1 ≤ (l:ℝ) := by exact_mod_cast (show k+1 ≤ l by omega)
    have hm := mul_le_mul_of_nonneg_right hi hs.le
    have hgap : 15*s ≤ y-x := by nlinarith [hx.2,hy.1]
    have he : y-x ≤ |x-y| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · have hi : (l:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast (show l+1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_right hi hs.le
    have hgap : 15*s ≤ x-y := by nlinarith [hy.2,hx.1]
    linarith [le_abs_self (x-y)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_GraphGridCells
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equal-scale three-dimensional cells, colored by sixteen residues
in each coordinate. Enlarged balls in one color are disjoint. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma graphGridCell_dist_gt {s : ℝ} (hs : 0 < s) (r : GraphGridColor)
    {k l : GraphGridIndex} (hkl : k ≠ l) {x y : GraphSpace}
    (hx : x ∈ graphGridCell r k s) (hy : y ∈ graphGridCell r l s) :
    8*s < dist x y := by
  by_cases h₀ : k.1.1 = l.1.1
  · by_cases h₁ : k.1.2 = l.1.2
    · have h₂ : k.2 ≠ l.2 := by
        intro h
        exact hkl (Prod.ext (Prod.ext h₀ h₁) h)
      have hh := equal_scale_cell_separation hs h₂ (r.2:ℕ) hx.2 hy.2
      exact hh.trans_le (by
        rw [Prod.dist_eq,Real.dist_eq]
        exact le_max_right _ _)
    · have hh := equal_scale_cell_separation hs h₁ (r.1.2:ℕ) hx.1.2 hy.1.2
      exact hh.trans_le (by
        rw [Prod.dist_eq,Prod.dist_eq,Real.dist_eq]
        exact (le_max_right _ _).trans (le_max_left _ _))
  · have hh := equal_scale_cell_separation hs h₀ (r.1.1:ℕ) hx.1.1 hy.1.1
    exact hh.trans_le (by
      rw [Prod.dist_eq,Prod.dist_eq,Real.dist_eq]
      exact (le_max_left _ _).trans (le_max_left _ _))

lemma graphGridCell_enlarged_disjoint {s : ℝ} (hs : 0 < s) (r : GraphGridColor)
    {k l : GraphGridIndex} (hkl : k ≠ l) {x y : GraphSpace}
    (hx : x ∈ graphGridCell r k s) (hy : y ∈ graphGridCell r l s) :
    Disjoint (closedBall x (4*s)) (closedBall y (4*s)) := by
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  have ht := dist_triangle x z y
  rw [dist_comm x z] at ht
  have hle : dist x y ≤ 8*s := by
    linarith [mem_closedBall.mp hzx, mem_closedBall.mp hzy]
  exact (not_lt_of_ge hle) (graphGridCell_dist_gt hs r hkl hx hy)

lemma exists_graphGridInterval {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ∃ (r : Fin 16) (k : ℤ), x ∈ graphGridInterval r k s := by
  let n : ℤ := Int.floor (x/s)
  have hn0 : 0 ≤ n % 16 := Int.emod_nonneg _ (by norm_num)
  have hn16 : n % 16 < 16 := Int.emod_lt_of_pos _ (by norm_num)
  let r : Fin 16 := ⟨(n%16).toNat,by omega⟩
  refine ⟨r,n/16,?_⟩
  have he : (16:ℝ)*(n/16:ℤ)+(r:ℕ) = (n:ℝ) := by
    have hr : ((r:ℕ):ℝ) = ((n%16:ℤ):ℝ) := by
      dsimp only [r]
      exact_mod_cast (Int.natCast_toNat_eq_self.mpr hn0)
    rw [hr]
    have hh : (16:ℤ)*(n/16)+n%16 = n := by simpa only [add_comm] using Int.emod_add_mul_ediv n 16
    exact_mod_cast hh
  change (16*(n/16:ℤ)+(r:ℕ))*s ≤ x ∧ x ≤ (16*(n/16:ℤ)+(r:ℕ)+1)*s
  rw [he]
  have hlo := (le_div_iff₀ hs).mp (Int.floor_le (x/s))
  have hhi := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (x/s))
  exact ⟨hlo,hhi.le⟩

lemma exists_graphGridCell {s : ℝ} (hs : 0 < s) (x : GraphSpace) :
    ∃ (r : GraphGridColor) (k : GraphGridIndex), x ∈ graphGridCell r k s := by
  obtain ⟨r₀,k₀,h₀⟩ := exists_graphGridInterval hs x.1.1
  obtain ⟨r₁,k₁,h₁⟩ := exists_graphGridInterval hs x.1.2
  obtain ⟨r₂,k₂,h₂⟩ := exists_graphGridInterval hs x.2
  exact ⟨((r₀,r₁),r₂),((k₀,k₁),k₂),⟨⟨h₀,h₁⟩,h₂⟩⟩

lemma graphGridCell_dist_le {s : ℝ} (r : GraphGridColor) (k : GraphGridIndex)
    {x y : GraphSpace} (hx : x ∈ graphGridCell r k s) (hy : y ∈ graphGridCell r k s) :
    dist x y ≤ s := by
  have hcoord {a x y : ℝ} (hx : x ∈ Icc a (a+s)) (hy : y ∈ Icc a (a+s)) :
      |x-y| ≤ s := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩
  have h₀ := hcoord (a := (16*(k.1.1:ℝ)+(r.1.1:ℕ))*s)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hx.1.1)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hy.1.1)
  have h₁ := hcoord (a := (16*(k.1.2:ℝ)+(r.1.2:ℕ))*s)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hx.1.2)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hy.1.2)
  have h₂ := hcoord (a := (16*(k.2:ℝ)+(r.2:ℕ))*s)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hx.2)
    (by simpa only [graphGridInterval,add_mul,one_mul] using hy.2)
  simpa only [Prod.dist_eq,Real.dist_eq,max_le_iff] using And.intro (And.intro h₀ h₁) h₂

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableGraphCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindex a countable graph cover by the natural numbers without
changing its quadratic cost or increasing its diameter bound. -/
open Set Function MeasureTheory Metric Encodable
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma nat_graph_cover_of_countable {ι : Type*} [Countable ι]
    (T : ι → Set GraphSpace) {D : ℝ≥0∞} (hD : ∀ i, ediam (T i) ≤ D) :
    ∃ S : ℕ → Set GraphSpace,
      (⋃ i, T i) = (⋃ n, S n) ∧ (∀ n, ediam (S n) ≤ D) ∧
      (∑' n, ediam (S n)^2) = ∑' i, ediam (T i)^2 := by
  let : Encodable ι := Encodable.ofCountable ι
  let S : ℕ → Set GraphSpace := fun n => ⋃ i ∈ Encodable.decode₂ ι n, T i
  refine ⟨S,?_,?_,?_⟩
  · exact (iUnion_decode₂ T).symm
  · intro n
    rw [show S n = ⋃ i ∈ Encodable.decode₂ ι n, T i from rfl, ediam_iUnion_mem_option]
    exact iSup_le fun i => iSup_le fun _ => hD i
  · exact tsum_iUnion_decode₂ (fun A : Set GraphSpace => ediam A^2) (by simp) T

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ColoredGridEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCountableElemFirstUncountableIio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The enlarged graph-grid balls have a uniform energy sum, with no
doubling hypothesis on the measure. -/
open Set Function MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma colored_grid_energy_sum (μ : Measure GraphSpace) {s : ℝ} (hs : 0 < s)
    (r : GraphGridColor) (I : Set GraphGridIndex) (c : I → GraphSpace)
    (hc : ∀ i : I, c i ∈ graphGridCell r (i : GraphGridIndex) s) {O : Set GraphSpace}
    (hO : ∀ i : I, closedBall (c i) (4*s) ⊆ O) :
    (∑' i : I, μ (closedBall (c i) (4*s))) ≤ μ O := by
  have hd : Pairwise (Disjoint on (fun i : I => closedBall (c i) (4*s))) := by
    intro i j hij
    exact graphGridCell_enlarged_disjoint hs r (Subtype.coe_ne_coe.mpr hij) (hc i) (hc j)
  rw [← measure_iUnion hd (fun _ => isClosed_closedBall.measurableSet)]
  exact measure_mono (iUnion_subset hO)

lemma all_colored_grid_energy_sum (μ : Measure GraphSpace) {s : ℝ} (hs : 0 < s)
    (I : GraphGridColor → Set GraphGridIndex) (c : (r : GraphGridColor) → I r → GraphSpace)
    (hc : ∀ (r : GraphGridColor) (i : I r), c r i ∈ graphGridCell r (i : GraphGridIndex) s) {O : Set GraphSpace}
    (hO : ∀ (r : GraphGridColor) (i : I r), closedBall (c r i) (4*s) ⊆ O) :
    (∑' r, ∑' i : I r, μ (closedBall (c r i) (4*s))) ≤ 4096 * μ O := by
  calc
    _ ≤ ∑' _r : GraphGridColor, μ O :=
      ENNReal.tsum_le_tsum (fun r => colored_grid_energy_sum μ hs r (I r) (c r) (hc r) (hO r))
    _ = _ := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      norm_num

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_UniformGraphCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble local graph covers at one scale. The finite residue coloring
controls the cost by the energy of an open neighborhood. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma uniform_graph_cover {A O : Set GraphSpace} (μ : Measure GraphSpace)
    (K : ℝ≥0∞) {s : ℝ} (hs : 0 < s)
    (hsmall : ∀ x ∈ A, closedBall x (4*s) ⊆ O)
    (hlocal : ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s))) :
    ∃ (I : GraphGridColor → Set GraphGridIndex)
      (T : (r : GraphGridColor) → I r → ℕ → Set GraphSpace),
      A ⊆ ⋃ r, ⋃ i, ⋃ n, T r i n ∧
      (∀ r i n, ediam (T r i n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' r, ∑' i : I r, ∑' n, ediam (T r i n)^2) ≤ 4096*K*μ O := by
  classical
  let I : GraphGridColor → Set GraphGridIndex := fun r => {k | (A ∩ graphGridCell r k s).Nonempty}
  choose c hc using fun r (i : I r) => i.property
  choose T hT using fun r (i : I r) => hlocal (c r i) (hc r i).1
  refine ⟨I,T,?_,(fun r i n => (hT r i).2.1 n),?_⟩
  · intro x hx
    obtain ⟨r,k,hk⟩ := exists_graphGridCell hs x
    have hi : k ∈ I r := ⟨x,hx,hk⟩
    let i : I r := ⟨k,hi⟩
    have hd : dist x (c r i) ≤ s := graphGridCell_dist_le r k hk (hc r i).2
    obtain ⟨n,hn⟩ := mem_iUnion.mp ((hT r i).1 ⟨hx,hd⟩)
    exact mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨n,hn⟩⟩⟩
  · calc
      _ ≤ ∑' r, ∑' i : I r, K*μ (closedBall (c r i) (4*s)) :=
        ENNReal.tsum_le_tsum (fun r => ENNReal.tsum_le_tsum (fun i => (hT r i).2.2))
      _ = K*(∑' r, ∑' i : I r, μ (closedBall (c r i) (4*s))) := by
        simp only [ENNReal.tsum_mul_left]
      _ ≤ K*(4096*μ O) := mul_le_mul' le_rfl
        (all_colored_grid_energy_sum μ hs I c (fun r i => (hc r i).2)
          (fun r i => hsmall (c r i) (hc r i).1))
      _ = _ := by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_UniformGraphHausdorff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCountableElemFirstUncountableIio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform small graph covers give an actual Hausdorff-measure bound.
Only a fixed interior margin of the chosen energy neighborhood is used. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma uniform_graph_hausdorff_le {A O : Set GraphSpace} (μ : Measure GraphSpace)
    (K : ℝ≥0∞) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : ∀ x ∈ A, closedBall x (4*δ) ⊆ O)
    (hlocal : ∀ s, 0 < s → s ≤ δ → ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s))) :
    (μH[2] : Measure GraphSpace) A ≤ 4096*K*μ O := by
  let s : ℕ → ℝ := fun n => δ*(1/2:ℝ)^n
  have hs (n : ℕ) : 0 < s n := mul_pos hδ (pow_pos (by norm_num) _)
  have hsδ (n : ℕ) : s n ≤ δ := by
    dsimp only [s]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hδ.le).trans_eq (mul_one δ)
  have hst : Tendsto s atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)))
  choose I T hcover hdiam hcost using fun n => uniform_graph_cover μ K (hs n)
    (fun x hx => (closedBall_subset_closedBall (by nlinarith [hsδ n])).trans (hsmall x hx))
    (hlocal (s n) (hs n) (hsδ n))
  let ι := fun n => Σ r : GraphGridColor, Σ i : I n r, ℕ
  have : ∀ n, Countable (ι n) := fun _ => inferInstance
  let S : (n : ℕ) → ι n → Set GraphSpace := fun n p => T n p.1 p.2.1 p.2.2
  have hD (n : ℕ) (i : ι n) : ediam (S n i) ≤ ENNReal.ofReal (8*s n) := hdiam n i.1 i.2.1 i.2.2
  have hcov (n : ℕ) : A ⊆ ⋃ i, S n i := by
    simpa only [S,ι,iUnion_sigma] using hcover n
  have hsum (n : ℕ) : (∑' i : ι n, ediam (S n i)^(2:ℝ)) ≤ 4096*K*μ O := by
    simpa only [S,ι,ENNReal.rpow_two,ENNReal.tsum_sigma'] using hcost n
  have ht : Tendsto (fun n => ENNReal.ofReal (8*s n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul hst)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum 2 A _ ht S
    (Eventually.of_forall hD) (Eventually.of_forall hcov)
  apply hh.trans
  simpa only [liminf_const] using liminf_le_liminf (f := atTop) (Eventually.of_forall hsum)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OpenGraphHausdorff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the fixed interior margin by a compact exhaustion of the open
energy neighborhood. The resulting estimate applies to the entire set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_graph_hausdorff_le_open {A O : Set GraphSpace} (hO : IsOpen O) (hAO : A ⊆ O)
    (μ : Measure GraphSpace) (K : ℝ≥0∞)
    (hlocal : ∀ s, 0 < s → ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s))) :
    (μH[2] : Measure GraphSpace) A ≤ 4096*K*μ O := by
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let B : ℕ → Set GraphSpace := fun n => Subtype.val '' compactCovering O n
  have hB (n : ℕ) : IsCompact (B n) :=
    (isCompact_compactCovering O n).image continuous_subtype_val
  have hBO (n : ℕ) : B n ⊆ O := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hmB : Monotone B := fun _ _ h => image_mono (compactCovering_subset O h)
  have hcap (n : ℕ) : (μH[2] : Measure GraphSpace) (A ∩ B n) ≤ 4096*K*μ O := by
    obtain ⟨ε,hε,hεO⟩ := (hB n).exists_cthickening_subset_open hO (hBO n)
    apply uniform_graph_hausdorff_le μ K (show 0 < ε/4 by positivity)
    · intro x hx
      have hh : closedBall x (4*(ε/4)) ⊆ cthickening ε (B n) := by
        simpa only [mul_div_cancel₀ _ (by norm_num : (4:ℝ) ≠ 0)] using
          (closedBall_subset_cthickening hx.2 ε)
      exact hh.trans hεO
    · intro s hs _ x hx
      obtain ⟨T,hT,hD,hC⟩ := hlocal s hs x hx.1
      exact ⟨T,(inter_subset_inter_left _ inter_subset_left).trans hT,hD,hC⟩
  have hcover : (⋃ n, A ∩ B n) = A := by
    apply Subset.antisymm (iUnion_subset fun _ => inter_subset_left)
    intro x hx
    obtain ⟨n,hn⟩ := exists_mem_compactCovering (⟨x,hAO hx⟩ : O)
    exact mem_iUnion.mpr ⟨n,hx,⟨⟨x,hAO hx⟩,hn,rfl⟩⟩
  have hm : Monotone (fun n => A ∩ B n) := fun _ _ h _ hx => ⟨hx.1,hmB h hx.2⟩
  rw [← hcover,hm.measure_iUnion]
  exact iSup_le hcap

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GraphHausdorffDomination
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Outer regularity turns the local graph-cover energy payment into
Hausdorff-measure domination and, in particular, preservation of null sets. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma graph_hausdorff_le_of_local_covers {A : Set GraphSpace}
    (μ : Measure GraphSpace) [μ.OuterRegular] (K : ℝ≥0∞) (hK : K ≠ ∞)
    (hlocal : ∀ s, 0 < s → ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s))) :
    (μH[2] : Measure GraphSpace) A ≤ 4096*K*μ A := by
  by_cases hK0 : K = 0
  · simpa only [hK0,mul_zero,zero_mul] using
      local_graph_hausdorff_le_open isOpen_univ (subset_univ A) μ K hlocal
  · have hc0 : (4096:ℝ≥0∞)*K ≠ 0 := mul_ne_zero (by norm_num) hK0
    have hct : (4096:ℝ≥0∞)*K ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hK
    rw [A.measure_eq_iInf_isOpen μ]
    simp_rw [ENNReal.mul_iInf_of_ne hc0 hct]
    exact le_iInf fun O => le_iInf fun hAO => le_iInf fun hO =>
      local_graph_hausdorff_le_open hO hAO μ K hlocal

lemma graph_hausdorff_zero_of_local_covers {A : Set GraphSpace}
    (μ : Measure GraphSpace) [μ.OuterRegular] (K : ℝ≥0∞) (hK : K ≠ ∞)
    (hlocal : ∀ s, 0 < s → ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s)))
    (hA : μ A = 0) : (μH[2] : Measure GraphSpace) A = 0 := by
  apply le_antisymm _ bot_le
  simpa only [bot_eq_zero,hA,mul_zero] using graph_hausdorff_le_of_local_covers μ K hK hlocal

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexCoareaJacobian
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Jacobian identity in regular complex coordinates. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma complex_real_det_columns (B : ℂ →L[ℝ] ℂ) :
    B.det = (B 1).re * (B Complex.I).im - (B Complex.I).re * (B 1).im := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    ContinuousLinearMap.coe_coe, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma coarea_covector_jacobian (A : ℂ →L[ℝ] ℝ) (B : ℂ →L[ℝ] ℂ)
    (h1 : A (B 1) = 1) (hI : A (B Complex.I) = 0) :
    ‖A‖ * |B.det| = ‖B Complex.I‖ := by
  rw [complexCovector_apply] at h1 hI
  let Δ := (B 1).re * (B Complex.I).im - (B Complex.I).re * (B 1).im
  have ha : A 1 * Δ = (B Complex.I).im := by
    dsimp only [Δ]
    linear_combination (B Complex.I).im * h1 - (B 1).im * hI
  have hb : A Complex.I * Δ = -(B Complex.I).re := by
    dsimp only [Δ]
    linear_combination -(B Complex.I).re * h1 + (B 1).re * hI
  have hs : (‖A‖ * |B.det|) ^ 2 = ‖B Complex.I‖ ^ 2 := by
    rw [mul_pow, sq_abs, complexCovector_norm_sq, complex_real_det_columns,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [← pow_two]
    change ((A 1)^2 + (A Complex.I)^2) * Δ^2 = (B Complex.I).re^2 + (B Complex.I).im^2
    calc
      _ = (A 1 * Δ)^2 + (A Complex.I * Δ)^2 := by ring
      _ = (B Complex.I).re^2 + (B Complex.I).im^2 := by rw [ha, hb]; ring
  exact (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (norm_nonneg _)).mp hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DifferentiableCriticalPieces
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At critical differentiability points the linear-approximation partition
has arbitrarily small Lipschitz constant on each measurable piece. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma differentiable_critical_pieces {f : ℂ → ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) (hne : S.Nonempty)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hz : ∀ x ∈ S, fderiv ℝ f x = 0) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ B : ℕ → Set ℂ, (∀ n, MeasurableSet (B n)) ∧
      Pairwise (Disjoint on B) ∧ (⋃ n, B n) = S ∧
      ∀ n, LipschitzOnWith ε f (B n) := by
  obtain ⟨t,A,hdj,ht,hcover,happrox,hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f S (fderiv ℝ f)
      (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) (fun _ => ε)
      (fun _ => hε.ne')
  have hAz (n : ℕ) : A n = 0 := by
    obtain ⟨x,hx,he⟩ := hA hne n
    rw [he, hz x hx]
  refine ⟨fun n => S ∩ t n, (fun n => hS.inter (ht n)), ?_, ?_, ?_⟩
  · exact fun i j hij => (hdj hij).mono inter_subset_right inter_subset_right
  · rw [← inter_iUnion, inter_eq_left.mpr hcover]
  · intro n
    have hh := (happrox n).lipschitz
    rw [hAz n] at hh
    simpa only [norm_zero, nnnorm_zero, zero_add] using lipschitzOnWith_iff_restrict.mpr hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzLengthFiberMajorant
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable majorant for the lengths of Lipschitz scalar fibers.
Only a finite two-dimensional Hausdorff measure is needed. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma exists_lipschitz_length_fiber_majorant
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (L : ℝ≥0) (f : X → ℝ) (hf : LipschitzWith L f)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hε : ∀ n, 0 < ε n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose T hcover hdiam hcost using fun n =>
    exists_small_quadratic_hausdorff_cover A hA (ε n) δ (hε n) hδ
  let g : ℕ → ℝ → ℝ≥0∞ := fun n y =>
    ∑' k, if y ∈ closure (f '' T n k) then ediam (T n k) else 0
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    apply Measurable.tsum
    intro k
    exact Measurable.ite isClosed_closure.measurableSet measurable_const measurable_const
  have hgint : ∀ n, (∫⁻ y, g n y) ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
    intro n
    calc
      (∫⁻ y, g n y) = ∑' k, ediam (T n k) * volume (closure (f '' T n k)) := by
        rw [show g n = fun y => ∑' k, (closure (f '' T n k)).indicator
          (fun _ => ediam (T n k)) y by rfl]
        rw [lintegral_tsum (fun k => measurable_const.indicator
          isClosed_closure.measurableSet |>.aemeasurable)]
        simp only [lintegral_indicator isClosed_closure.measurableSet, lintegral_const,
          Measure.restrict_apply_univ]
      _ ≤ ∑' k, ediam (T n k) * ((L : ℝ≥0∞) * ediam (T n k)) := by
        apply ENNReal.tsum_le_tsum
        intro k
        apply mul_le_mul' le_rfl
        exact (Real.volume_le_diam _).trans ((ediam_closure _).le.trans (hf.ediam_image_le _))
      _ = (L : ℝ≥0∞) * ∑' k, ediam (T n k) ^ (2 : ℕ) := by
        simp_rw [mul_left_comm (ediam _) (L : ℝ≥0∞), ← pow_two]
        exact ENNReal.tsum_mul_left
      _ ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
        exact mul_le_mul' le_rfl (hcost n).le
  refine ⟨fun y => liminf (fun n => g n y) atTop, Measurable.liminf hgm,
    hausdorff_one_fiber_le_liminf_cover A f ε hεlim T hdiam hcover, ?_⟩
  apply (lintegral_liminf_le hgm).trans
  have hm : liminf (fun n => ∫⁻ y, g n y) atTop ≤
      liminf (fun _ : ℕ => (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ)) atTop :=
    liminf_le_liminf (Eventually.of_forall hgint)
  simpa only [liminf_const] using hm

lemma exists_exact_lipschitz_length_fiber_majorant
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (L : ℝ≥0) (f : X → ℝ) (hf : LipschitzWith L f) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (L : ℝ≥0∞) * (μH[2] : Measure X) A := by
  let δ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hδ : ∀ n, 0 < δ n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose G hG hbound hint using fun n => exists_lipschitz_length_fiber_majorant A hA L f hf (δ n) (hδ n)
  refine ⟨fun y => ⨅ n, G n y, Measurable.iInf hG,
    (fun y => le_iInf (fun n => hbound n y)), ?_⟩
  have ht : Tendsto (fun n => (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ n)) atTop
      (𝓝 ((L : ℝ≥0∞) * (μH[2] : Measure X) A)) := by
    simpa only [add_zero] using
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hδlim) (Or.inr ENNReal.coe_ne_top)
  apply ge_of_tendsto' ht
  intro n
  exact (lintegral_mono (fun y => iInf_le (fun k => G k y) n)).trans (hint n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DifferentiableCriticalFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical differentiability points contribute zero length on almost every
scalar fiber. No continuity of the differential is used. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma differentiable_critical_fiber_majorant
    {f : ℂ → ℝ} {A : Set ℂ} (hA : MeasurableSet A)
    (hAfin : (μH[2] : Measure ℂ) A < ∞)
    (hd : ∀ x ∈ A, DifferentiableAt ℝ f x)
    (hcrit : ∀ x ∈ A, fderiv ℝ f x = 0) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) A := by
  rcases A.eq_empty_or_nonempty with h0 | hn
  · subst A
    exact ⟨0, measurable_const, by simp, by simp⟩
  obtain ⟨P,hP,hdj,heqA,hLP⟩ := differentiable_critical_pieces hA hn hd hcrit ε hε
  have hPA (n : ℕ) : P n ⊆ A := by rw [← heqA]; exact subset_iUnion P n
  choose g hg heq using fun n => (hLP n).extend_real
  have hfin : ∀ n, (μH[2] : Measure ℂ) (P n) < ∞ := fun n =>
    (measure_mono (hPA n)).trans_lt hAfin
  choose G hG hbound hint using fun n =>
    exists_exact_lipschitz_length_fiber_majorant (P n) (hfin n) ε (g n) (hg n)
  have heqfiber : ∀ n y, P n ∩ (g n) ⁻¹' {y} = P n ∩ f ⁻¹' {y} := by
    intro n y
    ext x
    by_cases hx : x ∈ P n
    · simp only [mem_inter_iff, hx, true_and, mem_preimage, mem_singleton_iff, ← heq n hx]
    · simp only [mem_inter_iff, hx, false_and]
  refine ⟨fun y => ∑' n, G n y, Measurable.tsum hG, ?_, ?_⟩
  · intro y
    calc
      (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) =
          (μH[1] : Measure ℂ) (⋃ n, P n ∩ f ⁻¹' {y}) := by rw [← iUnion_inter, heqA]
      _ ≤ ∑' n, (μH[1] : Measure ℂ) (P n ∩ f ⁻¹' {y}) := measure_iUnion_le _
      _ ≤ ∑' n, G n y := ENNReal.tsum_le_tsum (fun n => by rw [← heqfiber]; exact hbound n y)
  · rw [lintegral_tsum (fun n => (hG n).aemeasurable)]
    calc
      (∑' n, ∫⁻ y, G n y) ≤ ∑' n, (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) (P n) :=
        ENNReal.tsum_le_tsum hint
      _ = (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) A := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hdj hP, heqA]

lemma ae_zero_differentiable_critical_fiber_length
    {f : ℂ → ℝ} {A : Set ℂ} (hA : MeasurableSet A)
    (hAfin : (μH[2] : Measure ℂ) A < ∞)
    (hd : ∀ x ∈ A, DifferentiableAt ℝ f x)
    (hcrit : ∀ x ∈ A, fderiv ℝ f x = 0) :
    ∀ᵐ y, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) = 0 := by
  let ε : ℕ → ℝ≥0 := fun n => ⟨1 / (n + 1 : ℝ), by positivity⟩
  have hε : ∀ n, 0 < ε n := fun n => by change (0 : ℝ) < 1 / (n + 1 : ℝ); positivity
  choose G hG hbound hint using fun n => differentiable_critical_fiber_majorant hA hAfin hd hcrit (ε n) (hε n)
  let H : ℝ → ℝ≥0∞ := fun y => ⨅ n, G n y
  have hH : Measurable H := Measurable.iInf hG
  have hεlim : Tendsto (fun n => (ε n : ℝ≥0∞)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have heq : (fun n => (ε n : ℝ≥0∞)) = fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      funext n
      exact (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm
    rw [heq]
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using h
  have hintH : (∫⁻ y, H y) = 0 := by
    apply le_antisymm _ bot_le
    have ht := ENNReal.Tendsto.mul_const hεlim (Or.inr hAfin.ne)
    simp only [zero_mul] at ht
    apply ge_of_tendsto' ht
    intro n
    exact (lintegral_mono (fun y => iInf_le (fun k => G k y) n)).trans (hint n)
  filter_upwards [(lintegral_eq_zero_iff hH).mp hintH] with y hy
  apply le_antisymm _ bot_le
  change H y = 0 at hy
  exact (le_iInf (fun n => hbound n y)).trans_eq hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_InversePieceJacobian
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact inverse Jacobian on a measurable scalar level-coordinate piece. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverse_piece_jacobian {F : ℂ → ℂ} {f : ℂ → ℝ} {S : Set ℂ}
    (he : ∀ z, (F z).re = f z) (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    {y : ℂ} (hy : y ∈ F '' S) :
    ‖fderiv ℝ f (invFunOn F S y)‖ * |((fderiv ℝ F (invFunOn F S y)).inverse).det| =
      ‖(fderiv ℝ F (invFunOn F S y)).inverse Complex.I‖ := by
  let x := invFunOn F S y
  have hx : x ∈ S := invFunOn_mem hy
  have hf : HasFDerivAt f (Complex.reCLM.comp (fderiv ℝ F x)) x :=
    (Complex.reCLM.hasFDerivAt.comp x (hd x hx).hasFDerivAt).congr_of_eventuallyEq
      (Eventually.of_forall fun z => (he z).symm)
  have hdf : fderiv ℝ f x = Complex.reCLM.comp (fderiv ℝ F x) := hf.fderiv
  apply coarea_covector_jacobian
  · rw [hdf, ContinuousLinearMap.comp_apply, (hi x hx).self_apply_inverse]
    simp
  · rw [hdf, ContinuousLinearMap.comp_apply, (hi x hx).self_apply_inverse]
    simp

lemma measurable_inversePieceWeight {F : ℂ → ℂ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (hT : MeasurableSet T) (hTS : T ⊆ F '' S)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : Measurable (inversePieceWeight F S T q) := by
  have hm := ((hq.comp (measurable_inverseOnPiece hF hT hTS)).mul
    (((ContinuousLinearMap.measurable_apply Complex.I).comp
      (measurable_inversePieceDifferential hF hT hTS)).norm.ennreal_ofReal)).indicator hT
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  by_cases hy : y ∈ T
  · simp only [inversePieceWeight, indicator_of_mem hy, Pi.mul_apply, Function.comp_def, inverseOnPiece_eq hy]
  · simp only [inversePieceWeight, indicator_of_notMem hy]

lemma inverse_piece_energy_eq {F : ℂ → ℂ} {f : ℂ → ℝ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (he : ∀ z, (F z).re = f z)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    (hT : MeasurableSet T) (hTS : T ⊆ F '' S) (q : ℂ → ℝ≥0∞) :
    (∫⁻ z in (invFunOn F S) '' T, q z*ENNReal.ofReal ‖fderiv ℝ f z‖) =
      ∫⁻ y, inversePieceWeight F S T q y := by
  have hder : ∀ y ∈ T, HasFDerivWithinAt (invFunOn F S)
      (fderiv ℝ F (invFunOn F S y)).inverse T y :=
    fun y hy => (inverseOn_derivative_field hF hd hi (hTS hy)).mono hTS
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT hder (inverseOn_injOn.mono hTS),
    inversePieceWeight, lintegral_indicator hT]
  apply setLIntegral_congr_fun hT
  intro y hy
  dsimp only
  calc
    ENNReal.ofReal |((fderiv ℝ F (invFunOn F S y)).inverse).det| *
        (q (invFunOn F S y)*ENNReal.ofReal ‖fderiv ℝ f (invFunOn F S y)‖) =
      q (invFunOn F S y)*ENNReal.ofReal
        (‖fderiv ℝ f (invFunOn F S y)‖*|((fderiv ℝ F (invFunOn F S y)).inverse).det|) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
          ac_rfl
    _ = _ := by rw [inverse_piece_jacobian he hd hi (hTS hy)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_InversePieceCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted scalar coarea on a regular measurable inverse piece. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverse_piece_fiber_eq {F : ℂ → ℂ} {f : ℂ → ℝ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (he : ∀ z, (F z).re = f z)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    (hT : MeasurableSet T) (hb : IsBounded T) (hTS : T ⊆ F '' S)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) (t : ℝ) :
    weightedScalarLevelLength ((invFunOn F S) '' T) f q t =
      ∫⁻ s, inversePieceWeight F S T q (coareaVerticalLine t s) := by
  have hset : ((invFunOn F S) '' T) ∩ {z | f z = t} =
      ((invFunOn F S) ∘ coareaVerticalLine t) '' ((coareaVerticalLine t) ⁻¹' T) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hfy⟩
      have hyr : y.re = t := by
        calc
          y.re = (F (invFunOn F S y)).re := congrArg Complex.re (invFunOn_eq (hTS hy)).symm
          _ = f (invFunOn F S y) := he _
          _ = t := hfy
      have hyline : coareaVerticalLine t y.im = y := by
        apply Complex.ext <;> simp [hyr]
      exact ⟨y.im, by rwa [mem_preimage, hyline], by simp only [comp_apply, hyline]⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨coareaVerticalLine t s, hs, rfl⟩, ?_⟩
      change f (invFunOn F S (coareaVerticalLine t s)) = t
      rw [← he, invFunOn_eq (hTS hs), coareaVerticalLine_re]
  rw [weightedScalarLevelLength, hset,
    weighted_inverse_piece_vertical_curve hF hd hi hT hb hTS t hq]
  rw [← lintegral_indicator (hT.preimage (coareaVerticalLine_contDiff t).continuous.measurable)]
  apply lintegral_congr
  intro s
  by_cases hs : coareaVerticalLine t s ∈ T <;> simp [inversePieceWeight, hs]

lemma inverse_piece_weighted_coarea {F : ℂ → ℂ} {f : ℂ → ℝ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (he : ∀ z, (F z).re = f z)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    (hT : MeasurableSet T) (hb : IsBounded T) (hTS : T ⊆ F '' S)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    WeightedScalarCoareaIdentity ((invFunOn F S) '' T) f q := by
  let W := inversePieceWeight F S T q
  have hW : Measurable W := measurable_inversePieceWeight hF hT hTS hq
  let H : ℝ × ℝ → ℝ≥0∞ := fun p => W (Complex.measurableEquivRealProd.symm p)
  have hH : Measurable H := hW.comp Complex.measurableEquivRealProd.symm.measurable
  have hline (t s : ℝ) : coareaVerticalLine t s = Complex.measurableEquivRealProd.symm (t,s) := by
    apply Complex.ext <;> simp
  have hfun : weightedScalarLevelLength ((invFunOn F S) '' T) f q = fun t => ∫⁻ s, H (t,s) := by
    funext t
    rw [inverse_piece_fiber_eq hF he hd hi hT hb hTS hq]
    simp only [H, W, hline]
  refine ⟨by rw [hfun]; exact hH.lintegral_prod_right'.aemeasurable, ?_⟩
  rw [hfun, ← lintegral_prod H hH.aemeasurable, ← Measure.volume_eq_prod]
  have hm := (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).lintegral_comp hW
  exact hm.trans (inverse_piece_energy_eq hF he hd hi hT hTS q).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneCriticalFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded plane sets have finite two-dimensional Hausdorff measure;
exhaustion therefore removes the finite-measure restriction in the
critical-fiber argument. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma bounded_plane_hausdorff_two_lt_top {A : Set ℂ} (hA : IsBounded A) :
    (μH[2] : Measure ℂ) A < ∞ := by
  have h := Complex.antilipschitz_equivRealProd.le_hausdorffMeasure_image
    (by norm_num : (0 : ℝ) ≤ 2) A
  rw [MeasureTheory.hausdorffMeasure_prod_real] at h
  apply h.trans_lt
  apply ENNReal.mul_lt_top
  · finiteness
  · exact (Complex.lipschitz_equivRealProd.isBounded_image hA).measure_lt_top

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzNullFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null planar sets meet almost every fiber of a Lipschitz scalar map
in a set of zero one-dimensional Hausdorff measure. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma planar_hausdorff_two_zero_of_volume_zero {A : Set ℂ} (hA : volume A = 0) :
    (μH[2] : Measure ℂ) A = 0 := by
  have h := Complex.antilipschitz_equivRealProd.le_hausdorffMeasure_image
    (by norm_num : (0 : ℝ) ≤ 2) A
  rw [hausdorffMeasure_prod_real] at h
  have he : volume (Complex.measurableEquivRealProd '' A) = volume A := by
    rw [← Complex.volume_preserving_equiv_real_prod.map_eq,
      Complex.measurableEquivRealProd.map_apply,
      Complex.measurableEquivRealProd.injective.preimage_image]
  change volume (Complex.equivRealProd '' A) = volume A at he
  exact le_antisymm (by simpa only [he, hA, mul_zero] using h) bot_le

lemma lipschitz_null_fibers {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {A : Set ℂ} (hA : volume A = 0) :
    ∀ᵐ t, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {t}) = 0 := by
  have hz := planar_hausdorff_two_zero_of_volume_zero hA
  obtain ⟨G,hG,hbound,hint⟩ := exists_exact_lipschitz_length_fiber_majorant A
    (by rw [hz]; exact ENNReal.zero_lt_top) L f hf
  rw [hz, mul_zero] at hint
  have he : (∫⁻ t, G t) = 0 := le_antisymm hint bot_le
  filter_upwards [(lintegral_eq_zero_iff hG).mp he] with t ht
  exact le_antisymm ((hbound t).trans_eq ht) bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalLineDifferentiation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating along either coordinate family and the measurable reverse Fubini bridge. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma hasDerivAt_physicalCoordinate_comp {g : EuclideanPlane → ℝ}
    {i : Fin 2} {y t : ℝ} (hg : DifferentiableAt ℝ g (physicalCoordinateLine i y t)) :
    HasDerivAt (fun s => g (physicalCoordinateLine i y s))
      (fderiv ℝ g (physicalCoordinateLine i y t) (EuclideanSpace.single i 1)) t := by
  have h0 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have h1 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))
  fin_cases i
  · simpa [physicalCoordinateLine, Function.comp_def,
      show euclideanPlaneCoordinates.symm (1,0) = EuclideanSpace.single (0:Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 0] using hg.hasFDerivAt.comp_hasDerivAt t h0
  · simpa [physicalCoordinateLine, Function.comp_def,
      show euclideanPlaneCoordinates.symm (0,1) = EuclideanSpace.single (1:Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 1] using hg.hasFDerivAt.comp_hasDerivAt t h1

lemma ae_of_ae_ae_physicalCoordinateLine {P : EuclideanPlane → Prop}
    (hP : MeasurableSet {p | P p}) (i : Fin 2)
    (h : ∀ᵐ y ∂volume, ∀ᵐ t ∂volume, P (physicalCoordinateLine i y t)) :
    ∀ᵐ p ∂volume, P p := by
  have hm := physicalCoordinatePlane_measurePreserving i
  rw [← hm.map_eq, ae_map_iff hm.measurable.aemeasurable hP]
  exact (Measure.ae_prod_iff_ae_ae (hP.preimage hm.measurable)).mpr h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzPieceGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Lipschitz extension agreeing on a measurable piece has the original
Sobolev weak gradient there, almost everywhere. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma lipschitz_piece_partial_eq {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {S : Set EuclideanPlane} (hS : MeasurableSet S)
    {g : EuclideanPlane → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (heq : EqOn u g S) (i : Fin 2) :
    (fun p => fderiv ℝ g p (EuclideanSpace.single i 1)) =ᵐ[volume.restrict S]
      fun p => V p i := by
  have hVm := local_partial_aestronglyMeasurable hLp i
  let G : EuclideanPlane → ℝ := hVm.mk (fun p => V p i)
  have hG : Measurable G := hVm.stronglyMeasurable_mk.measurable
  have hVG : (fun p => V p i) =ᵐ[volume] G := hVm.ae_eq_mk
  have hP : MeasurableSet {p | p ∈ Sᶜ ∨ fderiv ℝ g p (EuclideanSpace.single i 1) = G p} :=
    hS.compl.union (measurableSet_eq_fun (measurable_fderiv_apply_const ℝ g (EuclideanSpace.single i 1)) hG)
  have hglobal : ∀ᵐ p ∂volume,
      p ∈ Sᶜ ∨ fderiv ℝ g p (EuclideanSpace.single i 1) = G p := by
    apply ae_of_ae_ae_physicalCoordinateLine hP i
    filter_upwards [locally_sobolev_coordinate_ae_hasDerivAt hu hw hLp i,
      ae_ae_physicalCoordinateLine (hg.ae_differentiableAt (μ := volume)) i,
      ae_ae_physicalCoordinateLine hVG i] with y hy hgy hVy
    have hline : EqOn (fun t => u (physicalCoordinateLine i y t))
        (fun t => g (physicalCoordinateLine i y t))
        {t | physicalCoordinateLine i y t ∈ S} := fun t ht => heq ht
    filter_upwards [hy, hgy, hVy, ae_derivative_eq_of_eqOn hline] with t ht hgt hVt hloc
    by_cases hmem : physicalCoordinateLine i y t ∈ S
    · right
      exact (hloc hmem _ _ ht (hasDerivAt_physicalCoordinate_comp hgt)).symm.trans hVt
    · exact Or.inl hmem
  change ∀ᵐ p ∂volume.restrict S, fderiv ℝ g p (EuclideanSpace.single i 1) = V p i
  rw [ae_restrict_iff' hS]
  filter_upwards [hglobal, hVG] with p hp hVp hpS
  exact (hp.resolve_left (not_not_intro hpS)).trans hVp.symm

lemma lipschitz_piece_gradient_eq {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {S : Set EuclideanPlane} (hS : MeasurableSet S)
    {g : EuclideanPlane → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) (heq : EqOn u g S) :
    ∀ᵐ p ∂volume.restrict S, ∀ i : Fin 2,
      fderiv ℝ g p (EuclideanSpace.single i 1) = V p i :=
  ae_all_iff.mpr (fun i => lipschitz_piece_partial_eq hu hw hLp hS hg heq i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedCoareaUnion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable measurable disjoint assembly of the weighted coarea identity. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma measurableSet_restricted_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) {A : Set ℂ} (hA : MeasurableSet A)
    (hAD : A ⊆ D) (t : ℝ) : MeasurableSet (A ∩ {z | f z = t}) := by
  have he : A ∩ {z | f z = t} = A ∩ (D ∩ {z | f z = t}) := by
    ext z
    constructor
    · exact fun hz => ⟨hz.1, hAD hz.1, hz.2⟩
    · exact fun hz => ⟨hz.1, hz.2.2⟩
  rw [he]
  exact hA.inter (measurableSet_scalar_level hD hf t)

lemma weightedScalarLevelLength_iUnion {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (A : ℕ → Set ℂ)
    (hA : ∀ n, MeasurableSet (A n)) (hdj : Pairwise (Disjoint on A))
    (hAD : ∀ n, A n ⊆ D) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    weightedScalarLevelLength (⋃ n, A n) f q t = ∑' n, weightedScalarLevelLength (A n) f q t := by
  simp only [weightedScalarLevelLength, iUnion_inter]
  apply lintegral_iUnion (fun n => measurableSet_restricted_scalar_level hD hf (hA n) (hAD n) t)
  exact fun i j hij => (hdj hij).mono inter_subset_left inter_subset_left

lemma weighted_coarea_iUnion {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (A : ℕ → Set ℂ)
    (hA : ∀ n, MeasurableSet (A n)) (hdj : Pairwise (Disjoint on A))
    (hAD : ∀ n, A n ⊆ D) (q : ℂ → ℝ≥0∞)
    (hlocal : ∀ n, WeightedScalarCoareaIdentity (A n) f q) :
    WeightedScalarCoareaIdentity (⋃ n, A n) f q := by
  have heq : weightedScalarLevelLength (⋃ n, A n) f q =
      fun t => ∑' n, weightedScalarLevelLength (A n) f q t :=
    funext (weightedScalarLevelLength_iUnion hD hf A hA hdj hAD q)
  refine ⟨by rw [heq]; exact AEMeasurable.tsum (fun n => (hlocal n).1), ?_⟩
  rw [heq, lintegral_tsum (fun n => (hlocal n).1)]
  calc
    (∑' n, ∫⁻ t, weightedScalarLevelLength (A n) f q t) =
        ∑' n, ∫⁻ z in A n, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ :=
      tsum_congr (fun n => (hlocal n).2)
    _ = _ := (lintegral_iUnion hA hdj (fun z => q z * ENNReal.ofReal ‖fderiv ℝ f z‖)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RegularPieceCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarea on a bounded regular measurable set, using its actual scalar
coordinate map and the countable bi-Lipschitz decomposition. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma weighted_coarea_empty (f : ℂ → ℝ) (q : ℂ → ℝ≥0∞) :
    WeightedScalarCoareaIdentity ∅ f q := by
  constructor
  · have he : weightedScalarLevelLength ∅ f q = fun _ : ℝ => 0 := by
      funext t
      simp [weightedScalarLevelLength]
    rw [he]
    exact measurable_const.aemeasurable
  · simp [weightedScalarLevelLength]

lemma regular_piece_weighted_coarea {F : ℂ → ℂ} {f : ℂ → ℝ}
    {S : Set ℂ} {L K : ℝ≥0} (hS : MeasurableSet S) (hb : IsBounded S)
    (hL : LipschitzOnWith L F S) (hK : AntilipschitzWith K (S.domRestrict F))
    (he : ∀ z, (F z).re = f z) (hd : ∀ z ∈ S, DifferentiableAt ℝ F z)
    (hi : ∀ z ∈ S, (fderiv ℝ F z).IsInvertible)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q := by
  have hinj : InjOn F S := by
    intro x hx y hy hxy
    have hh : (⟨x,hx⟩ : S) = ⟨y,hy⟩ := hK.injective hxy
    exact congrArg Subtype.val hh
  have hT : MeasurableSet (F '' S) := hS.image_of_continuousOn_injOn hL.continuousOn hinj
  have hTb : IsBounded (F '' S) := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hb
    apply Metric.isBounded_iff.mpr
    refine ⟨L*C, ?_⟩
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (hL.dist_le_mul x hx y hy).trans (mul_le_mul_of_nonneg_left (hC hx hy) L.coe_nonneg)
  have h := inverse_piece_weighted_coarea hK he hd hi hT hTb (Subset.refl _) hq
  have hinverse : (invFunOn F S) '' (F '' S) = S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact invFunOn_mem hy
    · intro hx
      exact ⟨F x, mem_image_of_mem F hx, hinj (invFunOn_mem (mem_image_of_mem F hx)) hx (invFunOn_eq (mem_image_of_mem F hx))⟩
  rwa [hinverse] at h

lemma regular_map_weighted_coarea {F : ℂ → ℂ} {f : ℂ → ℝ}
    (hf : Continuous f) {S : Set ℂ} (hS : MeasurableSet S) (hb : IsBounded S)
    (he : ∀ z, (F z).re = f z) (hd : ∀ z ∈ S, DifferentiableAt ℝ F z)
    (hi : ∀ z ∈ S, (fderiv ℝ F z).IsInvertible)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q := by
  rcases S.eq_empty_or_nonempty with h0 | hn
  · rw [h0]
    exact weighted_coarea_empty f q
  obtain ⟨B,L,K,hB,hdj,hcover,hLK⟩ := regular_map_measurable_pieces hS hn
    (fun z hz => (hd z hz).hasFDerivAt) hi
  have hBS (n : ℕ) : B n ⊆ S := by rw [← hcover]; exact subset_iUnion B n
  have hlocal (n : ℕ) : WeightedScalarCoareaIdentity (B n) f q :=
    regular_piece_weighted_coarea (hB n) (hb.subset (hBS n)) (hLK n).1 (hLK n).2 he
      (fun z hz => hd z (hBS n hz)) (fun z hz => hi z (hBS n hz)) hq
  have hh := weighted_coarea_iUnion isOpen_univ hf.continuousOn B hB hdj
    (fun _ => subset_univ _) q hlocal
  rwa [hcover] at hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarRegularCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scalar coordinate maps with transverse real or imaginary coordinate.
Their Jacobians are the corresponding nonzero scalar partials. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma planar_linear_isInvertible_of_det_ne_zero (A : ℂ →L[ℝ] ℂ) (hA : A.det ≠ 0) :
    A.IsInvertible := by
  have hunit : IsUnit A := ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
    ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA))
  obtain ⟨a, rfl⟩ := hunit
  exact ⟨ContinuousLinearEquiv.ofUnit a, rfl⟩

lemma scalarLevelCoordinate_re (f : ℂ → ℝ) (H : ℂ →L[ℝ] ℝ) (z : ℂ) :
    (scalarLevelCoordinate f H z).re = f z := by
  simp [scalarLevelCoordinate]

lemma hasFDerivAt_scalarLevelCoordinate {f : ℂ → ℝ} {L : ℂ →L[ℝ] ℝ} {z : ℂ}
    (hf : HasFDerivAt f L z) (H : ℂ →L[ℝ] ℝ) :
    HasFDerivAt (scalarLevelCoordinate f H) (scalarLevelDifferential L H) z := by
  exact (Complex.ofRealCLM.hasFDerivAt.comp z hf).add
    ((ContinuousLinearMap.toSpanSingleton ℝ Complex.I).hasFDerivAt.comp z H.hasFDerivAt)

lemma scalarLevelDifferential_det (L H : ℂ →L[ℝ] ℝ) :
    (scalarLevelDifferential L H).det = L 1 * H Complex.I - L Complex.I * H 1 := by
  rw [complex_real_det_columns]
  simp [scalarLevelDifferential, ContinuousLinearMap.toSpanSingleton_apply]

lemma scalarLevelCoordinate_im_isInvertible {f : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : fderiv ℝ f z 1 ≠ 0) :
    (fderiv ℝ (scalarLevelCoordinate f Complex.imCLM) z).IsInvertible := by
  rw [(hasFDerivAt_scalarLevelCoordinate hf.hasFDerivAt _).fderiv]
  apply planar_linear_isInvertible_of_det_ne_zero
  simpa only [scalarLevelDifferential_det, Complex.imCLM_apply, Complex.I_im,
    Complex.one_im, mul_one, mul_zero, sub_zero] using hz

lemma scalarLevelCoordinate_re_isInvertible {f : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : fderiv ℝ f z Complex.I ≠ 0) :
    (fderiv ℝ (scalarLevelCoordinate f Complex.reCLM) z).IsInvertible := by
  rw [(hasFDerivAt_scalarLevelCoordinate hf.hasFDerivAt _).fderiv]
  apply planar_linear_isInvertible_of_det_ne_zero
  simpa only [scalarLevelDifferential_det, Complex.reCLM_apply, Complex.I_re,
    Complex.one_re, mul_zero, mul_one, zero_sub, neg_ne_zero] using hz

lemma scalar_regular_im_weighted_coarea {f : ℂ → ℝ} (hf : Continuous f)
    {S : Set ℂ} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    (hd : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hn : ∀ z ∈ S, fderiv ℝ f z 1 ≠ 0)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q :=
  regular_map_weighted_coarea hf hS hb (scalarLevelCoordinate_re f Complex.imCLM)
    (fun z hz => (hasFDerivAt_scalarLevelCoordinate (hd z hz).hasFDerivAt _).differentiableAt)
    (fun z hz => scalarLevelCoordinate_im_isInvertible (hd z hz) (hn z hz)) hq

lemma scalar_regular_re_weighted_coarea {f : ℂ → ℝ} (hf : Continuous f)
    {S : Set ℂ} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    (hd : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hn : ∀ z ∈ S, fderiv ℝ f z Complex.I ≠ 0)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q :=
  regular_map_weighted_coarea hf hS hb (scalarLevelCoordinate_re f Complex.reCLM)
    (fun z hz => (hasFDerivAt_scalarLevelCoordinate (hd z hz).hasFDerivAt _).differentiableAt)
    (fun z hz => scalarLevelCoordinate_re_isInvertible (hd z hz) (hn z hz)) hq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedCoareaFiniteUnion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint finite assembly of exact weighted scalar coarea. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma weighted_coarea_union {f : ℂ → ℝ} (hf : Continuous f)
    {A B : Set ℂ} (hB : MeasurableSet B) (hd : Disjoint A B) (q : ℂ → ℝ≥0∞)
    (hAco : WeightedScalarCoareaIdentity A f q)
    (hBco : WeightedScalarCoareaIdentity B f q) :
    WeightedScalarCoareaIdentity (A ∪ B) f q := by
  have hsplit : weightedScalarLevelLength (A ∪ B) f q =
      fun t => weightedScalarLevelLength A f q t + weightedScalarLevelLength B f q t := by
    funext t
    unfold weightedScalarLevelLength
    rw [union_inter_distrib_right]
    apply lintegral_union
    · exact hB.inter (measurableSet_eq_fun hf.measurable measurable_const)
    · exact hd.mono inter_subset_left inter_subset_left
  refine ⟨by rw [hsplit]; exact hAco.1.add hBco.1, ?_⟩
  rw [hsplit, lintegral_add_left' hAco.1, hAco.2, hBco.2, lintegral_union hB hd]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarRegularCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coarea on every bounded Borel set of noncritical differentiability
points of a continuous planar scalar function. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma scalar_regular_weighted_coarea {f : ℂ → ℝ} (hf : Continuous f)
    {S : Set ℂ} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    (hd : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hn : ∀ z ∈ S, fderiv ℝ f z ≠ 0)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q := by
  let A := S ∩ {z | fderiv ℝ f z 1 ≠ 0}
  let B := S ∩ {z | fderiv ℝ f z 1 = 0}
  have hz : MeasurableSet {z | fderiv ℝ f z 1 = 0} :=
    measurableSet_eq_fun (measurable_fderiv_apply_const ℝ f 1) measurable_const
  have hA : MeasurableSet A := hS.inter hz.compl
  have hB : MeasurableSet B := hS.inter hz
  have hneI : ∀ z ∈ B, fderiv ℝ f z Complex.I ≠ 0 := by
    intro z hz hI
    apply hn z hz.1
    ext w
    rw [complexCovector_apply, hz.2, hI]
    simp
  have hAc := scalar_regular_im_weighted_coarea hf hA (hb.subset inter_subset_left)
    (fun z hz => hd z hz.1) (fun _ hz => hz.2) hq
  have hBc := scalar_regular_re_weighted_coarea hf hB (hb.subset inter_subset_left)
    (fun z hz => hd z hz.1) hneI hq
  have hdAB : Disjoint A B := by
    apply disjoint_left.mpr
    exact fun z ha hb => ha.2 hb.2
  have he : A ∪ B = S := by ext z; simp [A, B]; tauto
  have hh := weighted_coarea_union hf hB hdAB q hAc hBc
  rwa [he] at hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzScalarCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted scalar coarea for a planar Lipschitz function. Regular
pieces, zero-derivative pieces, and the Rademacher null set are all included. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma weighted_coarea_of_zero_fibers {f : ℂ → ℝ} {A : Set ℂ} {q : ℂ → ℝ≥0∞}
    (hzero : ∀ᵐ t, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {t}) = 0)
    (henergy : (∫⁻ z in A, q z*ENNReal.ofReal ‖fderiv ℝ f z‖) = 0) :
    WeightedScalarCoareaIdentity A f q := by
  have he : weightedScalarLevelLength A f q =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hzero] with t ht
    change (∫⁻ z in A ∩ {z | f z = t}, q z ∂μH[1]) = 0
    rw [show A ∩ {z | f z = t} = A ∩ f ⁻¹' {t} from rfl,
      Measure.restrict_eq_zero.mpr ht]
    exact lintegral_zero_measure q
  exact ⟨aemeasurable_const.congr he.symm, by rw [lintegral_congr_ae he, lintegral_zero, henergy]⟩

lemma lipschitz_scalar_weighted_coarea {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {E : Set ℂ} (hE : MeasurableSet E) (hb : IsBounded E)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity E f q := by
  let D := {z | DifferentiableAt ℝ f z}
  let R := (E ∩ D) ∩ {z | fderiv ℝ f z ≠ 0}
  let C := (E ∩ D) ∩ {z | fderiv ℝ f z = 0}
  let N := E \ D
  have hD : MeasurableSet D := measurableSet_of_differentiableAt ℝ f
  have hz : MeasurableSet {z | fderiv ℝ f z = 0} :=
    measurableSet_eq_fun (measurable_fderiv ℝ f) measurable_const
  have hR : MeasurableSet R := (hE.inter hD).inter hz.compl
  have hC : MeasurableSet C := (hE.inter hD).inter hz
  have hN : MeasurableSet N := hE.diff hD
  have hRco := scalar_regular_weighted_coarea hf.continuous hR
    (hb.subset (inter_subset_left.trans inter_subset_left)) (fun z hz => hz.1.2)
    (fun _ hz => hz.2) hq
  have hCzero := ae_zero_differentiable_critical_fiber_length hC
    (bounded_plane_hausdorff_two_lt_top (hb.subset (inter_subset_left.trans inter_subset_left)))
    (fun z hz => hz.1.2) (fun _ hz => hz.2)
  have hCenergy : (∫⁻ z in C, q z*ENNReal.ofReal ‖fderiv ℝ f z‖) = 0 := by
    apply setLIntegral_eq_zero hC
    intro z hz
    change q z*ENNReal.ofReal ‖fderiv ℝ f z‖ = 0
    rw [hz.2, norm_zero, ENNReal.ofReal_zero, mul_zero]
  have hCco := weighted_coarea_of_zero_fibers hCzero hCenergy
  have hNzero : volume N = 0 := by
    apply measure_mono_null (show N ⊆ Dᶜ from fun _ hz => hz.2)
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hf.ae_differentiableAt] with z hz
    exact fun hn => hn hz
  have hNenergy : (∫⁻ z in N, q z*ENNReal.ofReal ‖fderiv ℝ f z‖) = 0 := by
    rw [Measure.restrict_eq_zero.mpr hNzero]
    exact lintegral_zero_measure _
  have hNco := weighted_coarea_of_zero_fibers (lipschitz_null_fibers hf hNzero) hNenergy
  have hRC : Disjoint R C := by
    apply disjoint_left.mpr
    exact fun _ hr hc => hr.2 hc.2
  have heRC : R ∪ C = E ∩ D := by ext z; simp [R,C]; tauto
  have hED := weighted_coarea_union hf.continuous hC hRC q hRco hCco
  rw [heRC] at hED
  have hdEN : Disjoint (E ∩ D) N := by
    apply disjoint_left.mpr
    exact fun _ hd hn => hn.2 hd.2
  have heE : (E ∩ D) ∪ N = E := inter_union_sdiff E D
  have hh := weighted_coarea_union hf.continuous hN hdEN q hED hNco
  rwa [heE] at hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SquareAverageBounded
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable fields have finite centered-square maximal averages
almost everywhere. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma abs_squareAverage_le_global_integral {g : ℝ × ℝ → ℝ}
    (hg : Integrable g volume) (x : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    |squareAverage g x r| ≤ (4*r^2)⁻¹ * (∫ p, |g p|) := by
  apply (abs_average_le_average_abs (volume.restrict (coordinateSquare x r)) g).trans
  rw [average_eq, measureReal_restrict_apply_univ, coordinateSquare_real_volume x hr.le,
    smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ => abs_nonneg _) hg.abs)
    (by positivity)

lemma ae_squareAverage_bounded {g : ℝ × ℝ → ℝ} (hg : Integrable g volume) :
    ∀ᵐ x ∂volume, ∃ B : ℝ, 0 ≤ B ∧ ∀ r > 0, squareAverage g x r ≤ B := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hg.locallyIntegrable 1] with x hx
  have hl : Tendsto (fun r : ℝ => squareAverage g x r) (𝓝[>] 0) (𝓝 (g x)) := by
    apply hx (fun _ => x) id tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mem_closedBall_self (by simpa only [one_mul] using hr.le)
  have he : ∀ᶠ r in 𝓝[>] (0:ℝ), squareAverage g x r < g x+1 :=
    hl (Iio_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp he
  let B := max (|g x|+1) ((4*δ^2)⁻¹ * (∫ p, |g p|))
  refine ⟨B, (by dsimp only [B] <;> positivity), ?_⟩
  intro r hr
  by_cases hrd : r < δ
  · have hs : squareAverage g x r < g x+1 := hsmall ⟨?_, hr⟩
    · calc
        _ ≤ g x+1 := hs.le
        _ ≤ |g x|+1 := by linarith [le_abs_self (g x)]
        _ ≤ B := le_max_left _ _
    · simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using hrd
  · have hdr : δ ≤ r := le_of_not_gt hrd
    apply le_trans (le_abs_self _) ((abs_squareAverage_le_global_integral hg x hr).trans ?_)
    apply le_trans ?_ (le_max_right _ _)
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => abs_nonneg _)
    apply inv_anti₀ (by positivity)
    nlinarith [mul_self_le_mul_self hδ.le hdr]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SquareOscillationLipschitz
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform square mean-oscillation bounds give a quantitative Lipschitz restriction. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma square_oscillation_lipschitzOn {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {S : Set (ℝ × ℝ)} (M : ℝ≥0)
    (hosc : ∀ c ∈ S, ∀ r > 0,
      (⨍ p in coordinateSquare c r, |f p-squareAverage f c r|) ≤ (M:ℝ)*r) :
    LipschitzOnWith (32*M) f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases heq : x = y
  · simp [heq]
  let r := dist x y
  have hr : 0 < r := dist_pos.mpr heq
  have hxr : |f x-squareAverage f x (2*r)| ≤ 8*(M:ℝ)*(2*r) :=
    square_point_average_bound hf x (by positivity) (fun n =>
      hosc x hx _ (mul_pos (by positivity) (pow_pos (by norm_num) n)))
  have hyr : |f y-squareAverage f y r| ≤ 8*(M:ℝ)*r :=
    square_point_average_bound hf y hr (fun n =>
      hosc y hy _ (mul_pos hr (pow_pos (by norm_num) n)))
  have hsub : coordinateSquare y r ⊆ coordinateSquare x (2*r) :=
    closedBall_subset_closedBall' (by dsimp only [r]; rw [dist_comm y x]; linarith)
  have hcomp := squareAverage_comparison hf hr (by positivity : 0 < 2*r) hsub (le_refl _)
  have havg : |squareAverage f x (2*r)-squareAverage f y r| ≤ 8*(M:ℝ)*r := by
    rw [abs_sub_comm]
    calc
      _ ≤ 4*(⨍ p in coordinateSquare x (2*r), |f p-squareAverage f x (2*r)|) := hcomp
      _ ≤ 4*((M:ℝ)*(2*r)) := mul_le_mul_of_nonneg_left (hosc x hx _ (by positivity)) (by norm_num)
      _ = _ := by ring
  have htriangle : |f x-f y| ≤ |f x-squareAverage f x (2*r)| +
      |squareAverage f x (2*r)-squareAverage f y r| + |squareAverage f y r-f y| := by
    calc
      _ ≤ |f x-squareAverage f x (2*r)|+|squareAverage f x (2*r)-f y| := abs_sub_le _ _ _
      _ ≤ _ := by linarith [abs_sub_le (squareAverage f x (2*r)) (squareAverage f y r) (f y)]
  rw [abs_sub_comm (squareAverage f y r) (f y)] at htriangle
  change |f x-f y| ≤ _
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  change |f x-f y| ≤ 32*(M:ℝ)*r
  linarith

lemma locally_sobolev_lipschitzOn_of_square_averages {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {S : Set (ℝ × ℝ)} (B : ℝ≥0)
    (havg : ∀ c ∈ S, ∀ r > 0, (⨍ p in coordinateSquare c r,
      |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) ≤ B) :
    LipschitzOnWith (64*B) (fun p => u (euclideanPlaneCoordinates.symm p)) S := by
  have ho : ∀ c ∈ S, ∀ r > 0,
      (⨍ p in coordinateSquare c r, |u (euclideanPlaneCoordinates.symm p)-
        squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c r|) ≤ (2*B:ℝ≥0)*r := by
    intro c hc r hr
    calc
      _ ≤ 2*r*(⨍ p in coordinateSquare c r,
          |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) :=
        locally_sobolev_square_poincare hu hw hLp c hr
      _ ≤ 2*r*(B:ℝ) := mul_le_mul_of_nonneg_left (havg c hc r hr) (by positivity)
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat] <;> ring
  convert square_oscillation_lipschitzOn (hu.comp euclideanPlaneCoordinates.symm.continuous)
    (2*B) ho using 1
  · ring
  · rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevClosedLipschitzCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many closed Lipschitz pieces cover almost every point of a
continuous Sobolev representative with integrable partials. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_closed_lipschitz_cover_of_integrable_partials {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (hI : Integrable (fun p : ℝ × ℝ =>
      |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) volume) :
    ∃ K : ℕ → Set (ℝ × ℝ),
      (∀ n, IsClosed (K n) ∧
        LipschitzOnWith (64*(n:ℝ≥0)) (fun p => u (euclideanPlaneCoordinates.symm p)) (K n)) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  let g : ℝ × ℝ → ℝ := fun p =>
    |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|
  let S : ℕ → Set (ℝ × ℝ) := fun n => {c | ∀ r > 0, squareAverage g c r ≤ n}
  refine ⟨fun n => closure (S n), ?_, ?_⟩
  · intro n
    refine ⟨isClosed_closure, ?_⟩
    apply LipschitzOnWith.closure (hu.comp euclideanPlaneCoordinates.symm.continuous).continuousOn
    exact locally_sobolev_lipschitzOn_of_square_averages hu hw hLp (n:ℝ≥0) (fun c hc => hc)
  · filter_upwards [ae_squareAverage_bounded hI] with p hp
    obtain ⟨B, _, hB⟩ := hp
    obtain ⟨n, hn⟩ := exists_nat_ge B
    apply mem_iUnion.mpr
    refine ⟨n, subset_closure ?_⟩
    intro r hr
    exact (hB r hr).trans hn

lemma compact_sobolev_closed_lipschitz_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u) (W : DeGiorgi.MemW1pWitness 2 u univ) :
    ∃ K : ℕ → Set (ℝ × ℝ),
      (∀ n, IsClosed (K n) ∧
        LipschitzOnWith (64*(n:ℝ≥0)) (fun p => u (euclideanPlaneCoordinates.symm p)) (K n)) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  have hLp (R : ℝ) (i : Fin 2) :
      MemLp (fun p => W.weakGrad p i) 2 (volume.restrict (ball 0 R)) := by
    have h : MemLp (fun p => W.weakGrad p i) 2 volume := by
      simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
    exact h.restrict _
  have hI (i : Fin 2) : Integrable (fun p : ℝ × ℝ => W.weakGrad (euclideanPlaneCoordinates.symm p) i)
      volume := euclideanPlaneCoordinates_symm_measurePreserving.integrable_comp_of_integrable
        (compact_weakGradient_integrable W hs i)
  exact exists_closed_lipschitz_cover_of_integrable_partials hu W.isWeakGrad hLp ((hI 0).abs.add (hI 1).abs)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalSobolevLipschitzCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer closed Lipschitz pieces from real coordinates to the actual Euclidean plane. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma euclideanPlaneCoordinates_lipschitz : LipschitzWith 1 euclideanPlaneCoordinates := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, euclideanPlaneCoordinates_apply, Prod.dist_eq]
  rw [Real.dist_eq, Real.dist_eq, dist_eq_norm, max_le_iff]
  constructor
  · simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (x-y) (0:Fin 2)
  · simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (x-y) (1:Fin 2)

lemma compact_sobolev_physical_lipschitz_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u) (W : DeGiorgi.MemW1pWitness 2 u univ) :
    ∃ K : ℕ → Set EuclideanPlane,
      (∀ n, IsClosed (K n) ∧ LipschitzOnWith (64*(n:ℝ≥0)) u (K n)) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  obtain ⟨K, hK, hcover⟩ := compact_sobolev_closed_lipschitz_cover hu hs W
  refine ⟨fun n => euclideanPlaneCoordinates ⁻¹' K n, ?_, ?_⟩
  · intro n
    refine ⟨(hK n).1.preimage euclideanPlaneCoordinates.continuous, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := (hK n).2.dist_le_mul _ hx _ hy
    simp only [euclideanPlaneCoordinates.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one, one_mul] using euclideanPlaneCoordinates_lipschitz.dist_le_mul x y)
      (by positivity))
  · filter_upwards [euclideanPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae hcover]
      with p hp
    simpa only [mem_iUnion, mem_preimage] using hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevLipschitzCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable closed Lipschitz pieces for genuinely local continuous W1,2 functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_sobolev_core_lipschitz_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {K : Set EuclideanPlane} (hK : IsCompact K) :
    ∃ F : ℕ → Set EuclideanPlane,
      (∀ n, IsClosed (F n) ∧ F n ⊆ K ∧ LipschitzOnWith (64*(n:ℝ≥0)) u (F n)) ∧
      ∀ᵐ p ∂volume, p ∈ K → p ∈ ⋃ n, F n := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  obtain ⟨η, O, hη, hsη, _, hηR, _, hKO, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK isOpen_ball hR
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨W⟩ := exists_global_compact_cutoff_witness isOpen_ball
    (scalarBallWeakWitness hu hw hLp R).memW1p hη hsη hηR
  have hwc : Continuous w := hη.continuous.mul hu
  have hws : HasCompactSupport w := hsη.mul_right
  have heq (p : EuclideanPlane) (hp : p ∈ K) : w p = u p := by
    dsimp only [w]
    rw [hone p (hKO hp), one_mul]
  obtain ⟨L, hL, hcover⟩ := compact_sobolev_physical_lipschitz_cover hwc hws W
  refine ⟨fun n => L n ∩ K, ?_, ?_⟩
  · intro n
    refine ⟨(hL n).1.inter hK.isClosed, inter_subset_right, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    rw [← heq p hp.2, ← heq q hq.2]
    exact (hL n).2.dist_le_mul _ hp.1 _ hq.1
  · filter_upwards [hcover] with p hp hpK
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨n, hn, hpK⟩

lemma locally_sobolev_closed_lipschitz_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) :
    ∃ K : ℕ × ℕ → Set EuclideanPlane,
      (∀ n, IsClosed (K n) ∧ LipschitzOnWith (64*(n.2:ℝ≥0)) u (K n)) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  choose K hK hcover using fun n : ℕ => local_sobolev_core_lipschitz_cover hu hw hLp
    (isCompact_closedBall (0 : EuclideanPlane) n)
  refine ⟨fun n => K n.1 n.2, ?_, ?_⟩
  · intro n
    exact ⟨(hK n.1 n.2).1, (hK n.1 n.2).2.2⟩
  · have hall : ∀ᵐ p ∂volume, ∀ n : ℕ,
        p ∈ closedBall (0 : EuclideanPlane) n → p ∈ ⋃ j, K n j := ae_all_iff.mpr hcover
    filter_upwards [hall] with p hp
    obtain ⟨n, hn⟩ := exists_nat_gt ‖p‖
    have hpK : p ∈ closedBall (0 : EuclideanPlane) n := by
      simpa only [mem_closedBall, dist_zero_right] using hn.le
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hp n hpK)
    exact mem_iUnion.mpr ⟨(n,j), hj⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevGraphEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original Sobolev energy pushed to the scalar graph. The local
capacity cost is bounded by its mass on an actual ambient graph ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolevGraph_continuous {u : EuclideanPlane → ℝ} (hu : Continuous u) :
    Continuous (sobolevGraph u) := euclideanPlaneCoordinates.continuous.prodMk hu

lemma sobolev_graph_band_energy_le_ball {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (V : EuclideanPlane → EuclideanPlane) (a : EuclideanPlane) (t : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ y in {y : EuclideanPlane | ‖y-a‖ ≤ 4*s ∧ |u y-t| ≤ 2*s},
      ENNReal.ofReal (1+(|V y 0|+|V y 1|)^2)) ≤
      sobolevGraphEnergy u V (closedBall (euclideanPlaneCoordinates a,t) (4*s)) := by
  rw [sobolevGraphEnergy, Measure.map_apply (sobolevGraph_continuous hu).measurable
    isClosed_closedBall.measurableSet,
    withDensity_apply _ (isClosed_closedBall.preimage (sobolevGraph_continuous hu)).measurableSet]
  apply lintegral_mono_set
  intro y hy
  change dist (euclideanPlaneCoordinates y,u y) (euclideanPlaneCoordinates a,t) ≤ 4*s
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · have h := euclideanPlaneCoordinates_lipschitz.dist_le_mul y a
    simpa only [NNReal.coe_one,one_mul,dist_eq_norm] using h.trans (by simpa only [NNReal.coe_one,one_mul,dist_eq_norm] using hy.1)
  · rw [Real.dist_eq]
    exact hy.2.trans (by linarith)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevGraphEnergyRegular
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Sobolev graph energy is locally finite and outer regular.
A volume-null base set has zero graph energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolevGraph_injective (u : EuclideanPlane → ℝ) : Injective (sobolevGraph u) := by
  intro x y h
  exact euclideanPlaneCoordinates.injective (congrArg Prod.fst h)

lemma sobolevGraphEnergy_finiteOnCompacts {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) :
    IsFiniteMeasureOnCompacts (sobolevGraphEnergy u W.weakGrad) := by
  constructor
  intro K hK
  have hS : IsCompact (euclideanPlaneCoordinates.symm '' (Prod.fst '' K)) :=
    (hK.image continuous_fst).image euclideanPlaneCoordinates.symm.continuous
  have hpre : IsCompact (sobolevGraph u ⁻¹' K) := by
    apply hS.of_isClosed_subset (hK.isClosed.preimage (sobolevGraph_continuous hu))
    intro x hx
    exact ⟨euclideanPlaneCoordinates x,⟨sobolevGraph u x,hx,rfl⟩,
      euclideanPlaneCoordinates.symm_apply_apply x⟩
  have hG : MemLp (fun x => |W.weakGrad x 0|+|W.weakGrad x 1|) 2 volume := by
    exact (show MemLp (fun x => W.weakGrad x 0) 2 volume by
      simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp 0).norm.add
      (show MemLp (fun x => W.weakGrad x 1) 2 volume by
        simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp 1).norm
  let : IsFiniteMeasure (volume.restrict (sobolevGraph u ⁻¹' K)) :=
    isFiniteMeasure_restrict.mpr hpre.measure_lt_top.ne
  have hi : IntegrableOn (fun x => 1+(|W.weakGrad x 0|+|W.weakGrad x 1|)^2)
      (sobolevGraph u ⁻¹' K) :=
    (integrable_const 1).add hG.integrable_sq.integrableOn
  rw [sobolevGraphEnergy,Measure.map_apply (sobolevGraph_continuous hu).measurable hK.measurableSet,
    withDensity_apply _ hpre.measurableSet,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
  exact ENNReal.ofReal_lt_top

lemma sobolevGraphEnergy_outerRegular {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) :
    (sobolevGraphEnergy u W.weakGrad).OuterRegular := by
  let : IsFiniteMeasureOnCompacts (sobolevGraphEnergy u W.weakGrad) :=
    sobolevGraphEnergy_finiteOnCompacts hu W
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma sobolevGraphEnergy_null {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (V : EuclideanPlane → EuclideanPlane) {E : Set EuclideanPlane}
    (hE : MeasurableSet E) (hnull : volume E = 0) :
    sobolevGraphEnergy u V (sobolevGraph u '' E) = 0 := by
  have hm := (sobolevGraph_continuous hu).measurableEmbedding (sobolevGraph_injective u)
  rw [sobolevGraphEnergy,Measure.map_apply hm.measurable (hm.measurableSet_image' hE),
    Set.preimage_image_eq _ (sobolevGraph_injective u)]
  exact withDensity_absolutelyContinuous volume _ hnull

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevGraphLocalCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local capacity estimate as a natural-number cover of the actual
Sobolev graph inside an ambient ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolev_graph_local_cover {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (E : Set EuclideanPlane) (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (hηd : ∀ y, ‖fderiv ℝ spatialCapacityBump y‖ ≤ C) :
    ∃ T : ℕ → Set GraphSpace,
      sobolevGraph u '' E ∩ closedBall (euclideanPlaneCoordinates a,t) s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤
        (4194304 * ENNReal.ofReal (1+8*C^2)) *
          sobolevGraphEnergy u W.weakGrad (closedBall (euclideanPlaneCoordinates a,t) (4*s)) := by
  let A : Set (ℝ × ℝ) := {p | a+s • euclideanPlaneCoordinates.symm p ∈ E ∧
    p ∈ closedBall 0 1 ∧ |u (a+s • euclideanPlaneCoordinates.symm p)-t| ≤ s}
  obtain ⟨U,N,T,hU,hcover,hdiam,hcost⟩ := local_graph_capacity_cover hu W hsu a t hs hC0 hC hηd
    (A := A) (fun _ hp => hp.2.1) (fun _ hp => hp.2.2)
  have : Countable U := hU.to_subtype
  let S : (Σ x : U, Fin (N x)) → Set GraphSpace := fun i => T i.1 i.2
  obtain ⟨B,hB,hBd,hBc⟩ := nat_graph_cover_of_countable S
    (fun i => hdiam i.1 i.2)
  refine ⟨B,?_,hBd,?_⟩
  · rintro z ⟨⟨y,hy,rfl⟩,hz⟩
    let p := euclideanPlaneCoordinates ((planarAffineHomeomorph a s hs.ne').symm y)
    have hp : a+s • euclideanPlaneCoordinates.symm p = y := by
      dsimp only [p]
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact (planarAffineHomeomorph a s hs.ne').apply_symm_apply y
    have hb : dist (euclideanPlaneCoordinates y) (euclideanPlaneCoordinates a) ≤ s ∧
        |u y-t| ≤ s := by
      simpa only [mem_closedBall,sobolevGraph,Prod.dist_eq,max_le_iff,Real.dist_eq] using hz
    have hunit : p ∈ closedBall 0 1 := by
      have he : euclideanPlaneCoordinates y - euclideanPlaneCoordinates a = s • p := by
        rw [← hp,map_add,map_smul,ContinuousLinearEquiv.apply_symm_apply,add_sub_cancel_left]
      have hn : s*‖p‖ ≤ s := by
        simpa only [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos hs] using hb.1
      have hpn : ‖p‖ ≤ 1 := by nlinarith
      simpa only [mem_closedBall,dist_zero_right] using hpn
    have hpA : p ∈ A := by
      change a+s • euclideanPlaneCoordinates.symm p ∈ E ∧ _
      exact ⟨by rwa [hp],hunit,by simpa only [hp] using hb.2⟩
    have hin := hcover (mem_image_of_mem _ hpA)
    rw [hp] at hin
    rw [← hB]
    simpa only [S,iUnion_sigma,sobolevGraph] using hin
  · rw [hBc,ENNReal.tsum_sigma']
    exact hcost.trans (mul_le_mul' le_rfl (sobolev_graph_band_energy_le_ball hu W.weakGrad a t hs.le))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevGraphNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous compact Sobolev scalar function sends volume-null base
sets to graphs of zero two-dimensional Hausdorff measure. The proof uses
only the constructed local energy covers and measure regularity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_sobolev_graph_null {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hnull : volume E = 0) :
    (μH[2] : Measure GraphSpace) (sobolevGraph u '' E) = 0 := by
  obtain ⟨C,hC0,hC,hηd⟩ := exists_capacity_cutoff_derivative_bound
  let μ := sobolevGraphEnergy u W.weakGrad
  let : μ.OuterRegular := sobolevGraphEnergy_outerRegular hu W
  let K : ℝ≥0∞ := 4194304 * ENNReal.ofReal (1+8*C^2)
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  apply graph_hausdorff_zero_of_local_covers μ K hK
  · intro s hs x hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact sobolev_graph_local_cover hu W hsu E a (u a) hs hC0 hC hηd
  · exact sobolevGraphEnergy_null hu W.weakGrad hE hnull

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevGraphNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The graph-null result localizes to continuous W1,2_loc functions on
bounded null base sets by a genuine compact smooth cutoff. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_graph_null {u : EuclideanPlane → ℝ} (hu : Continuous u)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hEb : IsBounded E)
    (hnull : volume E = 0) :
    (μH[2] : Measure GraphSpace) (sobolevGraph u '' E) = 0 := by
  have hK : IsCompact (closure E) := hEb.isCompact_closure
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball 0
  obtain ⟨η,O,hη,hsη,_,hηR,_,hKO,hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK isOpen_ball hR
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨W⟩ := exists_global_compact_cutoff_witness isOpen_ball
    (scalarBallWeakWitness hu hw hLp R).memW1p hη hsη hηR
  have heq : EqOn (sobolevGraph w) (sobolevGraph u) E := by
    intro x hx
    change (euclideanPlaneCoordinates x,w x) = (euclideanPlaneCoordinates x,u x)
    apply Prod.ext
    · rfl
    · change η x*u x = u x
      rw [hone x (hKO (subset_closure hx)),one_mul]
  rw [← Set.image_congr heq]
  exact compact_sobolev_graph_null (hη.continuous.mul hu) W hsη.mul_right hE hnull

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoareaCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical Euclidean plane and complex plane carry the same area
and length measures, and precomposition preserves differential norms. -/
open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma physical_complex_hausdorff_preserving (d : ℝ) :
    MeasurePreserving complexPlaneCoordinates (μH[d] : Measure EuclideanPlane)
      (μH[d] : Measure ℂ) :=
  complexPlaneLinearIsometry.toIsometryEquiv.measurePreserving_hausdorffMeasure d

lemma complex_precomposition_fderiv_norm (u : EuclideanPlane → ℝ) (z : ℂ) :
    ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖ =
      ‖fderiv ℝ u (complexPlaneCoordinates.symm z)‖ := by
  rw [complexPlaneCoordinates.symm.comp_right_fderiv]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ complexPlaneLinearIsometry.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoareaTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of weighted scalar levels and differential energy
between the complex chart and the physical Euclidean plane. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma complex_weighted_level_eq_physical (E : Set EuclideanPlane) (u : EuclideanPlane → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) (t : ℝ) :
    weightedScalarLevelLength (complexPlaneCoordinates '' E)
      (u ∘ complexPlaneCoordinates.symm) (q ∘ complexPlaneCoordinates.symm) t =
      sobolevLevelIntegral E u q t := by
  have hp : complexPlaneCoordinates ⁻¹'
      ((complexPlaneCoordinates '' E) ∩ {z | (u ∘ complexPlaneCoordinates.symm) z = t}) =
        E ∩ {x | u x = t} := by
    ext x
    simp only [mem_preimage,mem_inter_iff,mem_image,mem_ofPred_eq,comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    constructor
    · rintro ⟨⟨y,hy,hxy⟩,hx⟩
      have he : y = x := complexPlaneCoordinates.injective hxy
      exact ⟨he ▸ hy,hx⟩
    · rintro ⟨hx,hu⟩
      exact ⟨⟨x,hx,rfl⟩,hu⟩
  have h := (physical_complex_hausdorff_preserving 1).setLIntegral_comp_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding (q ∘ complexPlaneCoordinates.symm)
    ((complexPlaneCoordinates '' E) ∩ {z | (u ∘ complexPlaneCoordinates.symm) z = t})
  rw [hp] at h
  simpa only [weightedScalarLevelLength,sobolevLevelIntegral,comp_apply,
    ContinuousLinearEquiv.symm_apply_apply] using h.symm

lemma complex_weighted_energy_eq_physical (E : Set EuclideanPlane) (u : EuclideanPlane → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) :
    (∫⁻ z in complexPlaneCoordinates '' E, (q ∘ complexPlaneCoordinates.symm) z *
      ENNReal.ofReal ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖) =
      ∫⁻ x in E, q x * ENNReal.ofReal ‖fderiv ℝ u x‖ := by
  have h := complexPlaneCoordinates_measurePreserving.setLIntegral_comp_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding
    (fun z => (q ∘ complexPlaneCoordinates.symm) z * ENNReal.ofReal
      ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖) (complexPlaneCoordinates '' E)
  rw [Set.preimage_image_eq _ complexPlaneCoordinates.injective] at h
  simpa only [comp_apply,complex_precomposition_fderiv_norm,
    ContinuousLinearEquiv.symm_apply_apply] using h.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalLipschitzCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted coarea for a Lipschitz function on the physical
Euclidean plane, with the norm of its actual differential. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma physical_lipschitz_weighted_coarea {u : EuclideanPlane → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {E : Set EuclideanPlane} (hE : MeasurableSet E)
    (hb : IsBounded E) {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q) :
    PhysicalWeightedCoareaIdentity E u q := by
  have hF : LipschitzWith L (u ∘ complexPlaneCoordinates.symm) := by
    have he : (complexPlaneLinearIsometry.symm : ℂ → EuclideanPlane) = complexPlaneCoordinates.symm := rfl
    simpa only [he,mul_one] using hu.comp complexPlaneLinearIsometry.symm.lipschitz
  have hEc : MeasurableSet (complexPlaneCoordinates '' E) :=
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding.measurableSet_image' hE
  have hEb : IsBounded (complexPlaneCoordinates '' E) :=
    complexPlaneLinearIsometry.lipschitz.isBounded_image hb
  obtain ⟨hm,he⟩ := lipschitz_scalar_weighted_coarea hF hEc hEb
    (hq.comp complexPlaneCoordinates.symm.continuous.measurable)
  have hlevels : weightedScalarLevelLength (complexPlaneCoordinates '' E)
      (u ∘ complexPlaneCoordinates.symm) (q ∘ complexPlaneCoordinates.symm) =
      sobolevLevelIntegral E u q :=
    funext (complex_weighted_level_eq_physical E u q)
  rw [hlevels] at hm he
  exact ⟨hm,he.trans (complex_weighted_energy_eq_physical E u q)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalFieldCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted coarea identities retaining a specified actual weak-gradient
field, and their disjoint countable assembly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma physical_field_coarea_piece {u g : EuclideanPlane → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {A : Set EuclideanPlane} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) (heq : EqOn u g A)
    {V : EuclideanPlane → EuclideanPlane}
    (hV : ∀ᵐ x ∂volume.restrict A, ∀ i : Fin 2,
      fderiv ℝ g x (EuclideanSpace.single i 1) = V x i)
    {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q) :
    PhysicalFieldCoareaIdentity A u V q := by
  obtain ⟨hm,hi⟩ := physical_lipschitz_weighted_coarea hg hA hb hq
  have hlev : sobolevLevelIntegral A g q = sobolevLevelIntegral A u q := by
    funext t
    have hs : A ∩ {x | g x = t} = A ∩ {x | u x = t} := by
      ext x
      constructor
      · rintro ⟨hx,ht⟩
        exact ⟨hx,(heq hx).trans ht⟩
      · rintro ⟨hx,ht⟩
        exact ⟨hx,(heq hx).symm.trans ht⟩
    simp only [sobolevLevelIntegral,hs]
  rw [hlev] at hm hi
  refine ⟨hm,hi.trans ?_⟩
  apply lintegral_congr_ae
  filter_upwards [hV] with x hx
  have he : planeCovectorGradient (fderiv ℝ g x) = V x := by
    unfold planeCovectorGradient
    rw [hx 0,hx 1,planePair_coordinates]

  rw [← planeCovectorGradient_norm,he]

lemma physical_field_coarea_iUnion {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (V : EuclideanPlane → EuclideanPlane) (q : EuclideanPlane → ℝ≥0∞)
    (A : ℕ → Set EuclideanPlane) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A))
    (hco : ∀ n, PhysicalFieldCoareaIdentity (A n) u V q) :
    PhysicalFieldCoareaIdentity (⋃ n, A n) u V q := by
  have hlev : sobolevLevelIntegral (⋃ n, A n) u q =
      fun t => ∑' n, sobolevLevelIntegral (A n) u q t := by
    funext t
    unfold sobolevLevelIntegral
    rw [iUnion_inter]
    apply lintegral_iUnion
    · exact fun n => (hA n).inter (measurableSet_eq_fun hu.measurable measurable_const)
    · exact fun i j hij => (hd hij).mono inter_subset_left inter_subset_left
  refine ⟨by rw [hlev]; exact AEMeasurable.tsum (fun n => (hco n).1),?_⟩
  rw [hlev,lintegral_tsum (fun n => (hco n).1)]
  calc
    _ = ∑' n, ∫⁻ x in A n, q x*ENNReal.ofReal ‖V x‖ := tsum_congr (fun n => (hco n).2)
    _ = _ := (lintegral_iUnion hA hd _).symm

lemma physical_field_coarea_union {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (V : EuclideanPlane → EuclideanPlane) (q : EuclideanPlane → ℝ≥0∞)
    {A B : Set EuclideanPlane} (hB : MeasurableSet B) (hd : Disjoint A B)
    (hAco : PhysicalFieldCoareaIdentity A u V q) (hBco : PhysicalFieldCoareaIdentity B u V q) :
    PhysicalFieldCoareaIdentity (A ∪ B) u V q := by
  have hs : sobolevLevelIntegral (A ∪ B) u q =
      fun t => sobolevLevelIntegral A u q t + sobolevLevelIntegral B u q t := by
    funext t
    unfold sobolevLevelIntegral
    rw [union_inter_distrib_right]
    exact lintegral_union (hB.inter (measurableSet_eq_fun hu.measurable measurable_const))
      (hd.mono inter_subset_left inter_subset_left)
  refine ⟨by rw [hs]; exact hAco.1.add hBco.1,?_⟩
  rw [hs,lintegral_add_left' hAco.1,hAco.2,hBco.2,lintegral_union hB hd]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevLipschitzRepresentatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local Sobolev function and its weak gradient are represented,
on countably many closed pieces of full measure, by global Lipschitz functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_lipschitz_representatives {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) :
    ∃ (K : ℕ × ℕ → Set EuclideanPlane) (g : ℕ × ℕ → EuclideanPlane → ℝ),
      (∀ n, IsClosed (K n) ∧ LipschitzWith (64*(n.2:ℝ≥0)) (g n) ∧ EqOn u (g n) (K n) ∧
        ∀ᵐ p ∂volume.restrict (K n), ∀ i : Fin 2,
          fderiv ℝ (g n) p (EuclideanSpace.single i 1) = V p i) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  obtain ⟨K, hK, hcover⟩ := locally_sobolev_closed_lipschitz_cover hu hw hLp
  choose g hg heq using fun n => (hK n).2.extend_real
  refine ⟨K, g, ?_, hcover⟩
  intro n
  exact ⟨(hK n).1, hg n, heq n,
    lipschitz_piece_gradient_eq hu hw hLp (hK n).1.measurableSet (hg n) (heq n)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevNullFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The graph-null theorem removes exceptional scalar fibers for the
actual continuous local Sobolev representative. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma physical_graph_null_fibers (u : EuclideanPlane → ℝ) (E : Set EuclideanPlane)
    (hG : (μH[2] : Measure GraphSpace) (sobolevGraph u '' E) = 0) :
    ∀ᵐ t, (μH[1] : Measure EuclideanPlane) (E ∩ u ⁻¹' {t}) = 0 := by
  let G := sobolevGraph u '' E
  obtain ⟨H,hH,hbound,hint⟩ := exists_exact_lipschitz_length_fiber_majorant G
    (by rw [hG]; exact ENNReal.zero_lt_top) 1 Prod.snd LipschitzWith.prod_snd
  have hzero : (∫⁻ t, H t) = 0 := by
    apply le_antisymm _ bot_le
    simpa only [bot_eq_zero,G,hG,mul_zero] using hint
  let P : GraphSpace → EuclideanPlane := euclideanPlaneCoordinates.symm ∘ Prod.fst
  have hp := euclideanPlaneCoordinates.symm.lipschitz.comp
    (LipschitzWith.prod_fst (α := ℝ × ℝ) (β := ℝ))
  filter_upwards [(lintegral_eq_zero_iff hH).mp hzero] with t ht
  have hset : P '' (G ∩ Prod.snd ⁻¹' {t}) = E ∩ u ⁻¹' {t} := by
    ext x
    constructor
    · rintro ⟨z,⟨⟨y,hy,rfl⟩,hty⟩,rfl⟩
      simpa only [P,comp_apply,sobolevGraph,Prod.fst,Prod.snd,
        ContinuousLinearEquiv.symm_apply_apply,mem_inter_iff,mem_preimage,mem_singleton_iff]
        using And.intro hy hty
    · intro hx
      refine ⟨sobolevGraph u x,⟨⟨x,hx.1,rfl⟩,hx.2⟩,?_⟩
      exact euclideanPlaneCoordinates.symm_apply_apply x
  apply le_antisymm _ bot_le
  rw [← hset]
  have hm : (μH[1] : Measure GraphSpace) (G ∩ Prod.snd ⁻¹' {t}) = 0 := by
    apply le_antisymm _ bot_le
    simpa only [bot_eq_zero,ht,Pi.zero_apply] using hbound t
  have hh := hp.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1) (G ∩ Prod.snd ⁻¹' {t})
  simpa only [bot_eq_zero,hm,mul_zero] using hh

lemma locally_sobolev_null_fibers {u : EuclideanPlane → ℝ} (hu : Continuous u)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (hnull : volume E = 0) :
    ∀ᵐ t, (μH[1] : Measure EuclideanPlane) (E ∩ u ⁻¹' {t}) = 0 :=
  physical_graph_null_fibers u E (locally_sobolev_graph_null hu hw hLp hE hEb hnull)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevCoareaProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact weighted Sobolev coarea input is proved from the closed
Lipschitz representatives, their actual gradients, and the null-fiber
result for the remaining volume-null set. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma physical_field_coarea_null {u : EuclideanPlane → ℝ}
    (V : EuclideanPlane → EuclideanPlane) (q : EuclideanPlane → ℝ≥0∞)
    {N : Set EuclideanPlane} (hnull : volume N = 0)
    (hfiber : ∀ᵐ t, (μH[1] : Measure EuclideanPlane) (N ∩ u ⁻¹' {t}) = 0) :
    PhysicalFieldCoareaIdentity N u V q := by
  have he : sobolevLevelIntegral N u q =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hfiber] with t ht
    change (∫⁻ x in N ∩ u ⁻¹' {t}, q x ∂μH[1]) = 0
    rw [Measure.restrict_eq_zero.mpr ht]
    exact lintegral_zero_measure q
  refine ⟨aemeasurable_const.congr he.symm,?_⟩
  rw [lintegral_congr_ae he,lintegral_zero,Measure.restrict_eq_zero.mpr hnull]
  exact (lintegral_zero_measure _).symm

lemma planarSobolevCoarea_oai : PlanarSobolevCoarea := by
  intro u hu V hw hLp E hE hEb q hq
  obtain ⟨K,g,hK,hcover⟩ := locally_sobolev_lipschitz_representatives hu hw hLp
  let C : ℕ → Set EuclideanPlane := fun n => E ∩ K (Nat.unpair n)
  let A : ℕ → Set EuclideanPlane := disjointed C
  have hC (n : ℕ) : MeasurableSet (C n) := hE.inter (hK _).1.measurableSet
  have hA (n : ℕ) : MeasurableSet (A n) := MeasurableSet.disjointed hC n
  have hAC (n : ℕ) : A n ⊆ C n := disjointed_subset C n
  have hAE (n : ℕ) : A n ⊆ E := (hAC n).trans inter_subset_left
  have hAK (n : ℕ) : A n ⊆ K (Nat.unpair n) := (hAC n).trans inter_subset_right
  have hco (n : ℕ) : PhysicalFieldCoareaIdentity (A n) u V q := by
    exact physical_field_coarea_piece (hK _).2.1 (hA n) (hEb.subset (hAE n))
      (fun _ hx => (hK _).2.2.1 (hAK n hx))
      (ae_restrict_of_ae_restrict_of_subset (hAK n) (hK _).2.2.2) hq
  let U := ⋃ n, A n
  have hUE : U ⊆ E := iUnion_subset hAE
  have hU : U = E ∩ ⋃ i, K i := by
    change (⋃ n, disjointed C n) = _
    rw [iUnion_disjointed]
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      exact ⟨hn.1,mem_iUnion.mpr ⟨Nat.unpair n,hn.2⟩⟩
    · rintro ⟨hx,hxK⟩
      obtain ⟨⟨j,k⟩,hjk⟩ := mem_iUnion.mp hxK
      apply mem_iUnion.mpr
      refine ⟨Nat.pair j k,?_⟩
      simpa only [C,Nat.unpair_pair,mem_inter_iff] using And.intro hx hjk
  have hUc : MeasurableSet U := MeasurableSet.iUnion hA
  let N := E \ U
  have hN : MeasurableSet N := hE.diff hUc
  have hN0 : volume N = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcover] with x hx hxn
    apply hxn.2
    rw [hU]
    exact ⟨hxn.1,hx⟩
  have hNco : PhysicalFieldCoareaIdentity N u V q := physical_field_coarea_null V q hN0
    (locally_sobolev_null_fibers hu hw hLp hN (hEb.subset sdiff_subset) hN0)
  have hUco : PhysicalFieldCoareaIdentity U u V q :=
    physical_field_coarea_iUnion hu V q A hA (disjoint_disjointed C) hco
  have hd : Disjoint U N := disjoint_sdiff_right
  have hall := physical_field_coarea_union hu V q hN hd hUco hNco
  have he : U ∪ N = E := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hUE hx
      · exact hx.1
    · intro hx
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · exact Or.inr ⟨hx,hxU⟩
  rw [he] at hall
  exact hall

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.planarSobolevCoarea_oai := @OAI.CircleDomainRigidity.planarSobolevCoarea_oai
