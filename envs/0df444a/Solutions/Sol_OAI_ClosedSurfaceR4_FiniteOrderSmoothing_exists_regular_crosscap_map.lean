-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_regular_crosscap_map
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:11:23.515035+00:00
-- url     : https://prove2.me/submissions/dd7da8f8-540f-461c-a22b-538961a8dae5

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI003
import Definitions.Def_OAIQ249SI004
import Definitions.Def_OAIQ249SI005

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SquarePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]




theorem exists_smooth_square_partition (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set M) ⊆ ⋃ i, U i) :
    ∃ ψ : ι → M → ℝ,
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  classical
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E) isClosed_univ U hU hcover
  let σ : M → ℝ := fun p => ∑ i, (ρ i p)^2
  have hsum (p : M) : ∑ i, ρ i p = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ p)
  have hσ (p : M) : 0 < σ p := by
    have hnon : 0 ≤ σ p := Finset.sum_nonneg (fun i _ => sq_nonneg (ρ i p))
    by_contra hn
    have hz : σ p = 0 := le_antisymm (not_lt.mp hn) hnon
    have hi : ∀ i, ρ i p = 0 := by
      intro i
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => sq_nonneg (ρ j p))).mp hz i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hs
    have hf := hsum p
    simp only [hi, Finset.sum_const_zero] at hf
    norm_num at hf
  have hsmoothσ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ σ := by
    exact contMDiff_finsetSum (fun i _ => (ρ i).contMDiff.pow 2)
  have hsmoothsqrt : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun p => Real.sqrt (σ p)) := by
    intro p
    exact (Real.contDiffAt_sqrt (hσ p).ne').contMDiffAt.comp p (hsmoothσ p)
  let ψ : ι → M → ℝ := fun i p => ρ i p / Real.sqrt (σ p)
  have hψsupp (i : ι) : tsupport (ψ i) ⊆ tsupport (ρ i) := by
    apply closure_mono
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    exact fun hn => hp (by simp [ψ, hn])
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).contMDiff.div₀ hsmoothsqrt (fun p => (Real.sqrt_pos.mpr (hσ p)).ne')
  · intro i
    exact (hψsupp i).trans (hρ i)
  · intro i
    exact (isClosed_tsupport (ψ i)).isCompact
  · intro i p
    exact div_nonneg (ρ.nonneg i p) (Real.sqrt_nonneg _)
  · intro p
    calc
      ∑ i, (ψ i p)^2 = (∑ i, (ρ i p)^2) / (Real.sqrt (σ p))^2 := by
        simp only [ψ, div_pow, Finset.sum_div]
      _ = σ p / σ p := by rw [Real.sq_sqrt (hσ p).le]
      _ = 1 := div_self (hσ p).ne'

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]



theorem exists_finite_smooth_square_partition (U : M → Set M)
    (hU : ∀ p, IsOpen (U p)) (hp : ∀ p, p ∈ U p) :
    ∃ (t : Finset M) (ψ : t → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  classical
  have hc : (univ : Set M) ⊆ ⋃ p, U p := fun p _ => mem_iUnion.mpr ⟨p, hp p⟩
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover U hU hc
  have hct : (univ : Set M) ⊆ ⋃ i : t, U i := by
    intro p _
    obtain ⟨i,hi,hpi⟩ := mem_iUnion₂.mp (ht (mem_univ p))
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hpi⟩
  obtain ⟨ψ,hψ⟩ := exists_smooth_square_partition (E := E) (fun i : t => U i)
    (fun i => hU i) hct
  exact ⟨t,ψ,hψ⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite chart data with inner and outer cutoffs for smoothing on a closed
surface. All chart and cutoff data are chosen independently of the input. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M]

variable [T2Space M] [CompactSpace M]

/-- A compact smooth surface admits fixed finite smoothing chart data. -/
theorem exists_smoothingAtlas : Nonempty (SmoothingAtlas M) := by
  classical
  obtain ⟨t, ψ, hψ, hsupp, _, _, hsum⟩ :=
    PhaseGeometry.exists_finite_smooth_square_partition (E := Plane)
      (fun p : M => (chart p).source) (fun p => (chart p).open_source)
      (fun p => by rw [chart_source]; exact mem_chart_source Plane p)
  have hout : ∀ i : t, ∃ χ : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      tsupport χ ⊆ (chart (i : M)).source ∧
      ∀ x ∈ tsupport (ψ i), χ x = 1 := by
    intro i
    have hc : IsCompact (tsupport (ψ i)) := (isClosed_tsupport _).isCompact
    obtain ⟨O, hO, hKO, hOc⟩ := hc.exists_isOpen_closure_subset
      ((chart (i : M)).open_source.mem_nhdsSet.mpr (hsupp i))
    obtain ⟨χ, hχ, _, hχs, hχone⟩ :=
      exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
        hO (isClosed_tsupport (ψ i)) hKO
    refine ⟨χ, hχ, ?_, fun x hx => (hχone x).mp hx⟩
    change closure (Function.support χ) ⊆ _
    rw [hχs]
    exact hOc
  choose χ hχ hχs hχone using hout
  exact ⟨⟨t, ψ, χ, hψ, hsupp, hχ, hχs, hχone, hsum⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasLinearMapBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed linear coordinate changes preserve the actual atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V W : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma localize_clm (p : M) (χ : M → ℝ) (L : V →L[ℝ] W) (F : M → V) :
    localize p χ (L ∘ F) = L ∘ localize p χ F := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize,hx,map_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateSardThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact three-dimensional coordinate Sard and regular-fiber facts
needed for generic projections of a surface from four-space to three-space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PublishedInputs

theorem smooth_coordinate_critical_values_null
    (f : SurfaceDirectionParameters → ThreeSpace)
    (U : Set SurfaceDirectionParameters) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  have : ContinuousSMul ℝ SurfaceDirectionParameters := Prod.continuousSMul
  let L : ThreeSpace ≃L[ℝ] SurfaceDirectionParameters :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let C : Set SurfaceDirectionParameters :=
    {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}
  let g : ThreeSpace → ThreeSpace := f ∘ L
  have hg (x : ThreeSpace) (hx : L x ∈ U) :
      HasFDerivAt g ((fderiv ℝ f (L x)).comp L.toContinuousLinearMap) x :=
    ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp x
      L.hasFDerivAt
  have hnull : volume (g '' (L ⁻¹' C)) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => (fderiv ℝ f (L x)).comp L.toContinuousLinearMap)
    · intro x hx
      exact (hg x hx.1).hasFDerivWithinAt
    · intro x hx
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot,ne_eq,LinearMap.ker_eq_bot]
      intro hinj
      have hsurj := LinearMap.injective_iff_surjective.mp hinj
      apply hx.2
      intro y
      obtain ⟨z,hz⟩ := hsurj y
      exact ⟨L z,hz⟩
  have he : g '' (L ⁻¹' C) = f '' C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨L x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨L.symm x,by simpa using hx,by simp [g]⟩
  rwa [he] at hnull

lemma regular_coordinate_point_locally_injective
    {f : SurfaceDirectionParameters → ThreeSpace}
    {U : Set SurfaceDirectionParameters} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x : SurfaceDirectionParameters} (hx : x ∈ U)
    (hreg : Function.Surjective (fderiv ℝ f x)) :
    ∃ V : Set SurfaceDirectionParameters, IsOpen V ∧ x ∈ V ∧ V.InjOn f := by
  have : ContinuousSMul ℝ SurfaceDirectionParameters := Prod.continuousSMul
  have hdim : Module.finrank ℝ SurfaceDirectionParameters = Module.finrank ℝ ThreeSpace := by simp
  have hinj : Function.Injective (fderiv ℝ f x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hreg
  let L : SurfaceDirectionParameters ≃L[ℝ] ThreeSpace :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ f x)
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hreg)
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hd : HasFDerivAt f L.toContinuousLinearMap x :=
    (hfx.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  let e := hfx.toOpenPartialHomeomorph f hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ⟨e.source,e.open_source,hfx.mem_toOpenPartialHomeomorph_source hd (by simp),e.injOn⟩

theorem finite_compact_coordinate_regular_fiber
    {f : SurfaceDirectionParameters → ThreeSpace}
    {U : Set SurfaceDirectionParameters} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {K : Set SurfaceDirectionParameters} (hK : IsCompact K) (hKU : K ⊆ U) (y : ThreeSpace)
    (hreg : ∀ x ∈ K, f x = y → Function.Surjective (fderiv ℝ f x)) :
    (K ∩ {x | f x = y}).Finite := by
  have hcompact : IsCompact (K ∩ {x | f x = y}) :=
    hK.of_isClosed_subset
      ((hf.continuousOn.mono hKU).preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  apply hcompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨V,hV,hxV,hVinj⟩ := regular_coordinate_point_locally_injective hU hf
    (hKU hx.1) (hreg x hx.1 hx.2)
  refine ⟨V,hV,?_⟩
  ext z
  constructor
  · rintro ⟨hzV,hzK,hzy⟩
    exact mem_singleton_iff.mpr (hVinj hzV hxV (hzy.trans hx.2.symm))
  · rintro rfl
    exact ⟨hxV,hx⟩

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowerDimensionalRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth three-parameter family has zero volume in dimension at least four. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

/-- Extend the map constantly in a complementary coordinate and apply the
same-dimensional zero-Jacobian image theorem. -/
theorem smooth_lower_dimensional_image_null {n : ℕ} (hn : 4 ≤ n)
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) : volume (f '' U) = 0 := by
  let : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin 3)) := inferInstance
  let : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (n - 3))) := inferInstance
  let : ContinuousSMul ℝ
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin (n - 3))) :=
    Prod.continuousSMul
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin (n - 3)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp; omega)
  let P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (ContinuousLinearMap.fst ℝ _ _).comp L.toContinuousLinearMap
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := f ∘ P
  have hfd (x : EuclideanSpace ℝ (Fin n)) (hx : P x ∈ U) :
      DifferentiableAt ℝ f (P x) :=
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg (x : EuclideanSpace ℝ (Fin n)) (hx : P x ∈ U) :
      DifferentiableAt ℝ g x := (hfd x hx).comp x P.differentiableAt
  let k : Fin (n - 3) := ⟨0, by omega⟩
  let v : EuclideanSpace ℝ (Fin (n - 3)) := PiLp.single 2 k 1
  have hv : v ≠ 0 := by
    intro he
    have he' := congrArg (fun z : EuclideanSpace ℝ (Fin (n - 3)) => z k) he
    exact one_ne_zero (by simpa only [v, PiLp.single_apply, ite_true, if_true, PiLp.zero_apply] using he')
  have hP : P (L.symm (0,v)) = 0 := by
    change (L (L.symm (0,v))).1 = 0
    rw [L.apply_symm_apply]
  have hdet (x : EuclideanSpace ℝ (Fin n)) (hx : P x ∈ U) :
      LinearMap.det (fderiv ℝ g x).toLinearMap = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hi
    have hd : fderiv ℝ g x = (fderiv ℝ f (P x)).comp P := by
      change fderiv ℝ (f ∘ P) x = _
      rw [fderiv_comp x (hfd x hx) P.differentiableAt,
        P.fderiv]
    have he : fderiv ℝ g x (L.symm (0,v)) = fderiv ℝ g x 0 := by
      rw [hd]
      simp only [ContinuousLinearMap.comp_apply, hP, map_zero]
    have hz : L.symm (0,v) = 0 := hi he
    have he' := congrArg (fun z => (L z).2) hz
    exact hv (by simpa using he')
  have hnull : volume (g '' (P ⁻¹' U)) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ g x)
    · intro x hx
      exact (hg x hx).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hdet x hx
  have he : g '' (P ⁻¹' U) = f '' U := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨P x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨L.symm (x,0),?_,?_⟩
      · simpa [P] using hx
      · change f (P (L.symm (x,0))) = f x
        congr 1
        simp [P]
  rwa [he] at hnull

/-- The same null-image fact in the plane-coordinate parameter space used
for a tangent vector and one scalar coefficient. -/
theorem smooth_coordinate_parameter_image_null {n : ℕ} (hn : 4 ≤ n)
    (f : ((Fin 2 → ℝ) × ℝ) → EuclideanSpace ℝ (Fin n))
    (U : Set ((Fin 2 → ℝ) × ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) : volume (f '' U) = 0 := by
  let : ContinuousSMul ℝ ((Fin 2 → ℝ) × ℝ) := Prod.continuousSMul
  let L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ((Fin 2 → ℝ) × ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc : ContDiffOn ℝ ∞ (f ∘ L) (L ⁻¹' U) :=
    hf.comp L.contDiff.contDiffOn (fun _ hx => hx)
  have hnull := smooth_lower_dimensional_image_null hn (f ∘ L) (L ⁻¹' U)
    (hU.preimage L.continuous) hc
  have he : (f ∘ L) '' (L ⁻¹' U) = f '' U := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨L x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨L.symm x,by simpa using hx,by simp⟩
  rwa [he] at hnull

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionJets
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted first jets detect immersion on the region where a partition
weight is nonzero. They depend continuously on the localized C1 data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma weightedJet_eq_smul {w : Base → ℝ} {l h : Base → V} {x : Base}
    (hw : DifferentiableAt ℝ w x) (hh : DifferentiableAt ℝ h x)
    (he : l =ᶠ[𝓝 x] fun y => w y • h y) :
    weightedJet w l x = (w x)^2 • fderiv ℝ h x := by
  unfold weightedJet
  rw [he.fderiv_eq, fderiv_fun_smul hw hh, he.self_of_nhds]
  ext v
  simp only [sub_apply,smul_apply,add_apply,ContinuousLinearMap.smulRight_apply]
  simp only [smul_add,smul_smul,pow_two,mul_comm (w x) ((fderiv ℝ w x) v)]
  abel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

lemma localizedWeight_smooth (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source) :
    ContDiff ℝ ∞ (localizedWeight p ψ) := localize_smooth p hψ hs contMDiff_const

omit [CompactSpace M] in
lemma fderiv_comp_chart_symm {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {x : Base}
    (hx : x ∈ (chart p).target) :
    fderiv ℝ (f ∘ (chart p).symm) x =
      (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp x (hf.mdifferentiable one_ne_zero).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt_symm hx)

lemma localized_weightedJet {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source)
    {x : Base} (hx : x ∈ (chart p).target) :
    weightedJet (localizedWeight p ψ) (localize p ψ f) x =
      (ψ ((chart p).symm x))^4 •
        ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
          (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) := by
  have hh : DifferentiableAt ℝ (f ∘ (chart p).symm) x :=
    ((hf.mdifferentiable one_ne_zero).mdifferentiableAt.comp x
      ((chart_mdifferentiable p).mdifferentiableAt_symm hx)).differentiableAt
  have he : localize p ψ f =ᶠ[𝓝 x]
      fun y => localizedWeight p ψ y • (f ∘ (chart p).symm) y := by
    filter_upwards [(chart p).open_target.mem_nhds hx] with y hy
    simp only [localizedWeight,localize,indicator_of_mem hy,smul_eq_mul,mul_one,
      Function.comp_apply]
  rw [weightedJet_eq_smul ((localizedWeight_smooth p hψ hs).differentiable (by simp) x) hh he,
    fderiv_comp_chart_symm hf p hx]
  have hw : localizedWeight p ψ x = (ψ ((chart p).symm x))^2 := by
    simp only [localizedWeight,localize,indicator_of_mem hx,smul_eq_mul,mul_one]
  rw [hw,← pow_mul]
  norm_num
  rfl

/-- The weighted jet loses no immersion information wherever its weight is
nonzero; the chart differential is an isomorphism there. -/
lemma localized_weightedJet_injective_iff {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source)
    {x : Base} (hx : x ∈ (chart p).target) (hw : ψ ((chart p).symm x) ≠ 0) :
    Function.Injective (weightedJet (localizedWeight p ψ) (localize p ψ f) x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)) := by
  rw [localized_weightedJet hf p hψ hs hx]
  constructor
  · intro hi
    have hcomp : Function.Injective
        ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
          (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) := by
      intro v u h
      apply hi
      change (ψ ((chart p).symm x))^4 •
          ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
            (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) v = _
      exact congrArg ((ψ ((chart p).symm x))^4 • ·) h
    change Function.Injective
      ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)) ∘
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) at hcomp
    exact hcomp.of_comp_right ((chart_mdifferentiable p).symm.mfderiv_surjective hx)
  · intro hi
    exact (smul_right_injective V (pow_ne_zero 4 hw)).comp
      (hi.comp ((chart_mdifferentiable p).symm.mfderiv_injective hx))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionDirections
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two affine charts for the tangent directions of a surface, and the
kernel criterion for a linear projection along a graph direction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma tangentRay_ne_zero (b : Bool) (t : ℝ) : tangentRay b t ≠ 0 := by
  cases b <;> intro h
  · have hh := congrFun h 0
    norm_num [tangentRay] at hh
  · have hh := congrFun h 1
    norm_num [tangentRay] at hh

lemma tangentRay_smooth (b : Bool) : ContDiff ℝ ∞ (tangentRay b) := by
  cases b <;> apply contDiff_pi.mpr <;> intro i <;> fin_cases i <;>
    first | exact contDiff_id | exact contDiff_const

lemma exists_tangentRay {v : Base} (hv : v ≠ 0) :
    ∃ (b : Bool) (t c : ℝ), c ≠ 0 ∧ v = c • tangentRay b t := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0,h1]
    refine ⟨true,v 0 / v 1,v 1,h1,?_⟩
    ext i
    fin_cases i
    · change v 0 = v 1 * (v 0 / v 1)
      field_simp
    · change v 1 = v 1 * 1
      rw [mul_one]
  · refine ⟨false,v 1 / v 0,v 0,h0,?_⟩
    ext i
    fin_cases i
    · change v 0 = v 0 * 1
      rw [mul_one]
    · change v 1 = v 0 * (v 1 / v 0)
      field_simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma graphProjection_comp_injective (a : V) (H : Base →L[ℝ] V × ℝ)
    (hH : Function.Injective H)
    (ha : ∀ b t, (H (tangentRay b t)).2 ≠ 0 →
      a ≠ ((H (tangentRay b t)).2)⁻¹ • (H (tangentRay b t)).1) :
    Function.Injective ((graphProjection a).comp H) := by
  have hker (v : Base) (hv : graphProjection a (H v) = 0) : v = 0 := by
    by_contra hn
    obtain ⟨b,t,c,hc,he⟩ := exists_tangentRay hn
    have hz : graphProjection a (H (tangentRay b t)) = 0 := by
      rw [he,map_smul,map_smul] at hv
      exact (smul_eq_zero.mp hv).resolve_left hc
    have hfst : (H (tangentRay b t)).1 = (H (tangentRay b t)).2 • a :=
      sub_eq_zero.mp hz
    have hlast : (H (tangentRay b t)).2 ≠ 0 := by
      intro hlast
      have hh : H (tangentRay b t) = H 0 := by
        rw [map_zero]
        apply Prod.ext
        · change (H (tangentRay b t)).1 = 0
          simpa only [hlast,zero_smul] using hfst
        · exact hlast
      exact tangentRay_ne_zero b t (hH hh)
    apply ha b t hlast
    rw [hfst,smul_smul,inv_mul_cancel₀ hlast,one_smul]
  intro v w h
  apply sub_eq_zero.mp
  apply hker
  change graphProjection a (H v) = graphProjection a (H w) at h
  rw [map_sub,map_sub,h,sub_self]

lemma weightedJet_smooth {w : Base → ℝ} {l : Base → V}
    (hw : ContDiff ℝ ∞ w) (hl : ContDiff ℝ ∞ l) :
    ContDiff ℝ ∞ (weightedJet w l) := by
  exact (hw.smul (hl.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).sub
    ((hw.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).smulRight hl)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GenericProjectionParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common graph direction avoids every tangent plane in a finite family
of smooth surface-coordinate derivatives when the projection target has
dimension at least four. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {n : ℕ}

lemma tangentSlopeDomain_open {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (b : Bool) : IsOpen (tangentSlopeDomain H b) := by
  exact isOpen_compl_singleton.preimage ((hH.comp contDiff_fst).clm_apply
    ((tangentRay_smooth b).comp contDiff_snd)).continuous.snd

lemma tangentSlope_smoothOn {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (b : Bool) :
    ContDiffOn ℝ ∞ (tangentSlope H b) (tangentSlopeDomain H b) := by
  have h := (hH.comp contDiff_fst).clm_apply
    ((tangentRay_smooth b).comp contDiff_snd)
  exact (h.snd.contDiffOn.inv (fun _ hx => hx)).smul h.fst.contDiffOn

theorem tangentSlope_image_null (hn : 4 ≤ n)
    {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (b : Bool) :
    volume (tangentSlope H b '' tangentSlopeDomain H b) = 0 :=
  PublishedInputs.smooth_coordinate_parameter_image_null hn _ _
    (tangentSlopeDomain_open hH b) (tangentSlope_smoothOn hH b)

/-- The excluded parameters form a null set; therefore the projection can
be chosen in any prescribed nonempty open set of graph parameters. -/
theorem exists_common_projection_parameter (hn : 4 ≤ n)
    {ι : Type*} [Countable ι]
    (H : ι → Base → Base →L[ℝ] ProjectionTarget n × ℝ)
    (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (U : Set (ProjectionTarget n)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ a ∈ U, ∀ i x, Function.Injective (H i x) →
      Function.Injective ((graphProjection a).comp (H i x)) := by
  let bad : Set (ProjectionTarget n) :=
    ⋃ i, ⋃ b : Bool, tangentSlope (H i) b '' tangentSlopeDomain (H i) b
  have hbad : volume bad = 0 :=
    measure_iUnion_null (fun i => measure_iUnion_null (fun b =>
      tangentSlope_image_null hn (hH i) b))
  have hae : ∀ᵐ a ∂volume, a ∉ bad := by
    simp only [ae_iff, not_not]
    change volume bad = 0
    exact hbad
  obtain ⟨a,hUa,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty U hU hne
  refine ⟨a,hUa,fun i x hi => graphProjection_comp_injective a (H i x) hi ?_⟩
  intro b t ht he
  apply ha
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨b,⟨(x,t),ht,he.symm⟩⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionSlopeDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative of a graph-direction coordinate. At a projection kernel
its derivative is exactly the projected derivative divided by the height. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma tangentRay_hasDerivAt (b : Bool) (t : ℝ) :
    HasDerivAt (tangentRay b) (tangentRayVelocity b) t := by
  apply hasDerivAt_pi.mpr
  intro i
  cases b <;> fin_cases i <;>
    first | exact hasDerivAt_id t | exact hasDerivAt_const t _

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma hasFDerivAt_graph_slope {f : E → V × ℝ} {D : E →L[ℝ] V × ℝ} {x : E}
    (hf : HasFDerivAt f D x) (a : V) (hn : (f x).2 ≠ 0)
    (he : (f x).1 = (f x).2 • a) :
    HasFDerivAt (fun y => (f y).2⁻¹ • (f y).1)
      ((f x).2⁻¹ • (graphProjection a).comp D) x := by
  have h := ((hasFDerivAt_inv hn).comp x hf.snd).smul hf.fst
  convert h using 1
  · rfl
  ext v
  change (f x).2⁻¹ • ((D v).1-(D v).2 • a) =
    (f x).2⁻¹ • (D v).1 + ((D v).2 * (-((f x).2 ^ 2)⁻¹)) • (f x).1
  have hc : (D v).2 * (-((f x).2 ^ 2)⁻¹) * (f x).2 =
      -((f x).2⁻¹ * (D v).2) := by
    field_simp
  rw [he,smul_smul,hc,neg_smul,smul_sub,smul_smul,sub_eq_add_neg]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TangentSlopeLinearization
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact linearization of the projective tangent-direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {n : ℕ}

lemma hasFDerivAt_tangent_direction
    {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (b : Bool) (z : Base × ℝ) :
    HasFDerivAt (fun w : Base × ℝ => H w.1 (tangentRay b w.2))
      (directionJetLinearization H b z) z := by
  have h := ((hH.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z.1).hasFDerivAt.comp z
    hasFDerivAt_fst).clm_apply
      ((tangentRay_hasDerivAt b z.2).hasFDerivAt.comp z hasFDerivAt_snd)
  exact h

theorem tangentSlope_fderiv
    {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (a : ProjectionTarget n) (b : Bool) (z : Base × ℝ)
    (hz : z ∈ tangentSlopeDomain H b) (ha : tangentSlope H b z = a) :
    fderiv ℝ (tangentSlope H b) z =
      (H z.1 (tangentRay b z.2)).2⁻¹ •
        (graphProjection a).comp (directionJetLinearization H b z) := by
  have he : (H z.1 (tangentRay b z.2)).1 =
      (H z.1 (tangentRay b z.2)).2 • a := by
    rw [← ha]
    change (H z.1 (tangentRay b z.2)).1 =
      (H z.1 (tangentRay b z.2)).2 •
        ((H z.1 (tangentRay b z.2)).2⁻¹ • (H z.1 (tangentRay b z.2)).1)
    rw [smul_smul,mul_inv_cancel₀ hz,one_smul]
  exact (hasFDerivAt_graph_slope (hasFDerivAt_tangent_direction hH b z) a hz he).fderiv

theorem regular_tangentSlope_linearization_bijective
    {H : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ}
    (hH : ContDiff ℝ ∞ H) (a : ProjectionTarget 3) (b : Bool) (z : Base × ℝ)
    (hz : z ∈ tangentSlopeDomain H b) (ha : tangentSlope H b z = a)
    (hreg : Function.Surjective (fderiv ℝ (tangentSlope H b) z)) :
    Function.Bijective ((graphProjection a).comp (directionJetLinearization H b z)) := by
  have hs : Function.Surjective ((graphProjection a).comp (directionJetLinearization H b z)) := by
    intro y
    obtain ⟨w,hw⟩ := hreg ((H z.1 (tangentRay b z.2)).2⁻¹ • y)
    rw [tangentSlope_fderiv hH a b z hz ha] at hw
    refine ⟨w,?_⟩
    exact (smul_right_injective _ (inv_ne_zero hz)) hw
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mpr hs,hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedProjectionLinearization
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive scalar weights do not alter the crosscap linearization at a
projection kernel, except by the same nonzero scalar factor. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {n : ℕ}

lemma weightedJet_product_germ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {w : Base → ℝ} {F l : Base → V} {x : Base}
    (hw : ContDiff ℝ ∞ w) (hF : ContDiff ℝ ∞ F)
    (he : l =ᶠ[𝓝 x] fun y => w y • F y) :
    weightedJet w l =ᶠ[𝓝 x] fun y => (w y)^2 • fderiv ℝ F y := by
  filter_upwards [he.eventuallyEq_nhds] with y hy
  exact weightedJet_eq_smul (hw.differentiable (by simp) y)
    (hF.differentiable (by simp) y) hy

lemma directionJetLinearization_congr_germ
    {H K : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    {x : Base} (he : H =ᶠ[𝓝 x] K) (b : Bool) (t : ℝ) :
    directionJetLinearization H b (x,t) = directionJetLinearization K b (x,t) := by
  unfold directionJetLinearization
  rw [he.self_of_nhds,he.fderiv_eq]

lemma projected_directionJet_scaled
    {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ} {w : Base → ℝ}
    (hH : ContDiff ℝ ∞ H) (hw : ContDiff ℝ ∞ w)
    (a : ProjectionTarget n) (b : Bool) (x : Base) (t : ℝ)
    (hker : graphProjection a (H x (tangentRay b t)) = 0) :
    (graphProjection a).comp (directionJetLinearization (fun y => w y • H y) b (x,t)) =
      w x • (graphProjection a).comp (directionJetLinearization H b (x,t)) := by
  apply ContinuousLinearMap.ext
  intro z
  have hd : fderiv ℝ (fun y => w y • H y) x =
      w x • fderiv ℝ H x + (fderiv ℝ w x).smulRight (H x) :=
    ((hw.differentiable (by simp) x).hasFDerivAt.smul
      (hH.differentiable (by simp) x).hasFDerivAt).fderiv
  simp only [ContinuousLinearMap.comp_apply,directionJetLinearization_apply,hd,
    smul_apply,add_apply,ContinuousLinearMap.smulRight_apply,
    map_add,map_smul,smul_add,smul_smul,hker,smul_zero,add_zero]
  rw [mul_comm z.2 (w x)]

theorem regular_weighted_directionJet
    {H : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ} {w : Base → ℝ}
    {K : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ}
    (hH : ContDiff ℝ ∞ H) (hw : ContDiff ℝ ∞ w)
    (a : ProjectionTarget 3) (b : Bool) (x : Base) (t : ℝ)
    (hw0 : w x ≠ 0) (he : K =ᶠ[𝓝 x] fun y => w y • H y)
    (hker : graphProjection a (H x (tangentRay b t)) = 0)
    (hbij : Function.Bijective ((graphProjection a).comp (directionJetLinearization K b (x,t)))) :
    Function.Bijective ((graphProjection a).comp (directionJetLinearization H b (x,t))) := by
  rw [directionJetLinearization_congr_germ he b t,
    projected_directionJet_scaled hH hw a b x t hker] at hbij
  constructor
  · intro v u h
    apply hbij.1
    exact congrArg (w x • ·) h
  · intro y
    obtain ⟨v,hv⟩ := hbij.2 (w x • y)
    exact ⟨v,(smul_right_injective _ hw0) hv⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundedProjectionDirections
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact direction parameters for kernels of maps on a surface tangent plane. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma exists_bounded_tangentRay {v : Base} (hv : v ≠ 0) :
    ∃ (b : Bool) (t c : ℝ), t ∈ Icc (-1 : ℝ) 1 ∧ c ≠ 0 ∧
      v = c • tangentRay b t := by
  by_cases h : |v 1| ≤ |v 0|
  · have h0 : v 0 ≠ 0 := by
      intro h0
      have h1 : v 1 = 0 := abs_nonpos_iff.mp (by simpa only [h0,abs_zero] using h)
      apply hv
      ext i
      fin_cases i <;> simp [h0,h1]
    have ht : |v 1 / v 0| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr h0)).mpr h
    refine ⟨false,v 1 / v 0,v 0,abs_le.mp ht,h0,?_⟩
    ext i
    fin_cases i
    · change v 0 = v 0 * 1
      rw [mul_one]
    · change v 1 = v 0 * (v 1 / v 0)
      field_simp
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply h
      simpa only [h1,abs_zero] using abs_nonneg (v 0)
    have ht : |v 0 / v 1| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr h1)).mpr (le_of_lt (lt_of_not_ge h))
    refine ⟨true,v 0 / v 1,v 1,abs_le.mp ht,h1,?_⟩
    ext i
    fin_cases i
    · change v 0 = v 1 * (v 0 / v 1)
      field_simp
    · change v 1 = v 1 * 1
      rw [mul_one]

lemma exists_bounded_tangentRay_in_kernel {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Base →L[ℝ] V) (hL : ¬ Function.Injective L) :
    ∃ (b : Bool) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 ∧ L (tangentRay b t) = 0 := by
  change ¬ (∀ u v : Base, L u = L v → u = v) at hL
  push Not at hL
  obtain ⟨u,v,he,hne⟩ := hL
  have hv : u-v ≠ 0 := sub_ne_zero.mpr hne
  have hz : L (u-v) = 0 := by rw [map_sub,he,sub_self]
  obtain ⟨b,t,c,ht,hc,hec⟩ := exists_bounded_tangentRay hv
  refine ⟨b,t,ht,?_⟩
  rw [hec,map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left hc

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionApproximation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing a compact C1 immersion while keeping its differential injective. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma coreThreshold_pos : 0 < A.coreThreshold := by unfold coreThreshold; positivity

omit [CompactSpace M] in
lemma weightCore_nonzero (i : A.centers) {p : M} (hp : p ∈ A.weightCore i) :
    A.weight i p ≠ 0 := by
  intro hz
  have h := A.coreThreshold_pos
  change A.coreThreshold ≤ (A.weight i p)^2 at hp
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at hp
  exact (not_lt_of_ge hp) h

omit [CompactSpace M] in
lemma weightCore_source (i : A.centers) : A.weightCore i ⊆ (chart (i : M)).source :=
  fun _ hp => A.weight_support i (subset_tsupport _ (A.weightCore_nonzero i hp))

lemma weightCore_compact (i : A.centers) : IsCompact (A.weightCore i) :=
  (isClosed_le continuous_const ((A.weight_smooth i).continuous.pow 2)).isCompact

lemma coordinateCore_compact (i : A.centers) : IsCompact (A.coordinateCore i) :=
  (A.weightCore_compact i).image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.weightCore_source i))

omit [CompactSpace M] in
lemma mem_some_weightCore (p : M) : ∃ i : A.centers, p ∈ A.weightCore i := by
  classical
  by_contra hn
  have hi (i : A.centers) : (A.weight i p)^2 ≤ A.coreThreshold :=
    le_of_lt (lt_of_not_ge (fun h => hn ⟨i,h⟩))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset A.centers)) (fun i _ => hi i)
  rw [A.partition p] at hs
  have hcount : (∑ _i : A.centers, A.coreThreshold) =
      (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) := by
    simp [coreThreshold,div_eq_mul_inv]
  rw [hcount] at hs
  have hlt : (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact (not_lt_of_ge hs) hlt

omit [CompactSpace M] in
lemma coordinateCore_target (i : A.centers) : A.coordinateCore i ⊆ (chart (i : M)).target := by
  rintro _ ⟨p,hp,rfl⟩
  exact (chart (i : M)).map_source (A.weightCore_source i hp)

omit [CompactSpace M] in
lemma coordinateCore_weight_nonzero (i : A.centers) {x : Base}
    (hx : x ∈ A.coordinateCore i) : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
  obtain ⟨p,hp,rfl⟩ := hx
  rw [(chart (i : M)).left_inv (A.weightCore_source i hp)]
  exact A.weightCore_nonzero i hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LinearProjectionImmersion
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth compact surface immersion in E × R projects to an immersion
in E when E is a Euclidean space of dimension at least four. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma weightedJet_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (w : Base → ℝ) {l : Base → V} {x : Base}
    (hl : DifferentiableAt ℝ l x) :
    weightedJet w (L ∘ l) x = L.comp (weightedJet w l x) := by
  unfold weightedJet
  rw [fderiv_comp x L.differentiableAt hl,L.fderiv]
  ext v
  simp only [ContinuousLinearMap.comp_apply,sub_apply,
    smul_apply,ContinuousLinearMap.smulRight_apply,
    Function.comp_apply,map_sub,map_smul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

theorem SmoothingAtlas.exists_projected_immersion (A : SmoothingAtlas M)
    {n : ℕ} (hn : 4 ≤ n)
    {F : M → ProjectionTarget n × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget n × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget n × ℝ) F p)) :
    ∃ a : ProjectionTarget n,
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget n) ∞ (graphProjection a ∘ F) ∧
      ∀ p, Function.Injective
        (mfderiv planeModel 𝓘(ℝ,ProjectionTarget n) (graphProjection a ∘ F) p) := by
  classical
  let H (i : A.centers) : Base → Base →L[ℝ] ProjectionTarget n × ℝ :=
    weightedJet (localizedWeight (i : M) (A.weight i))
      (localize (i : M) (A.weight i) F)
  have hH (i : A.centers) : ContDiff ℝ ∞ (H i) :=
    weightedJet_smooth
      (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i))
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF)
  obtain ⟨a,_ha,ha⟩ := exists_common_projection_parameter hn H hH univ isOpen_univ
    (Set.univ_nonempty : (univ : Set (ProjectionTarget n)).Nonempty)
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget n) ∞ (graphProjection a ∘ F) :=
    (graphProjection a).contDiff.contMDiff.comp hF
  refine ⟨a,hg,?_⟩
  intro p
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  let x := chart (i : M) p
  have hx : x ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hxT := A.coordinateCore_target i hx
  have hw := A.coordinateCore_weight_nonzero i hx
  have hf' := hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hHinj : Function.Injective (H i x) :=
    (localized_weightedJet_injective_iff hf' (i : M) (A.weight_smooth i)
      (A.weight_support i) hxT hw).mpr (hI _)
  have hproj := ha i x hHinj
  have hnew : Function.Injective (weightedJet (localizedWeight (i : M) (A.weight i))
      (localize (i : M) (A.weight i) (graphProjection a ∘ F)) x) := by
    rw [localize_clm,weightedJet_comp _ _
      ((localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).differentiable
        (by simp) x)]
    exact hproj
  have hgI := (localized_weightedJet_injective_iff (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (i : M)
    (A.weight_smooth i) (A.weight_support i) hxT hw).mp hnew
  change Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget n)
    (graphProjection a ∘ F) ((chart (i : M)).symm (chart (i : M) p))) at hgI
  rwa [(chart (i : M)).left_inv (A.weightCore_source i hi)] at hgI

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularProjectionParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular graph-projection parameters in dimension three. Unlike the
higher-dimensional avoidance result, this gives finite exceptional
directions on compact coordinate sets. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_regular_projection_parameter {ι : Type*} [Countable ι]
    (H : ι → Base → Base →L[ℝ] ProjectionTarget 3 × ℝ)
    (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (U : Set (ProjectionTarget 3)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ a ∈ U, ∀ i b z, z ∈ tangentSlopeDomain (H i) b →
      tangentSlope (H i) b z = a →
      Function.Surjective (fderiv ℝ (tangentSlope (H i) b) z) := by
  let bad : Set (ProjectionTarget 3) := ⋃ i, ⋃ b : Bool,
    tangentSlope (H i) b '' {z | z ∈ tangentSlopeDomain (H i) b ∧
      ¬ Function.Surjective (fderiv ℝ (tangentSlope (H i) b) z)}
  have hbad : volume bad = 0 := measure_iUnion_null (fun i =>
    measure_iUnion_null (fun b => PublishedInputs.smooth_coordinate_critical_values_null
      _ _ (tangentSlopeDomain_open (hH i) b) (tangentSlope_smoothOn (hH i) b)))
  have hae : ∀ᵐ a ∂volume, a ∉ bad := by
    simp only [ae_iff,not_not]
    change volume bad = 0
    exact hbad
  obtain ⟨a,haU,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty U hU hne
  refine ⟨a,haU,?_⟩
  intro i b z hz he
  by_contra hn
  apply ha
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨b,⟨z,⟨hz,hn⟩,he⟩⟩⟩

theorem finite_compact_projection_directions
    {H : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ}
    (hH : ContDiff ℝ ∞ H) {K : Set Base} (hK : IsCompact K)
    (hI : ∀ x ∈ K, Function.Injective (H x)) (a : ProjectionTarget 3) (b : Bool)
    (hreg : ∀ z, z ∈ tangentSlopeDomain H b → tangentSlope H b z = a →
      Function.Surjective (fderiv ℝ (tangentSlope H b) z)) :
    (compactProjectionDirections a H K b).Finite := by
  let C := compactProjectionDirections a H K b
  have hcomp : IsCompact C := (hK.prod isCompact_Icc).inter_right
    (isClosed_eq ((graphProjection a).continuous.comp
      ((hH.comp contDiff_fst).clm_apply
        ((tangentRay_smooth b).comp contDiff_snd)).continuous) continuous_const)
  have hU : C ⊆ tangentSlopeDomain H b := by
    intro z hz
    have he : (H z.1 (tangentRay b z.2)).1 =
        (H z.1 (tangentRay b z.2)).2 • a := sub_eq_zero.mp hz.2
    intro hs
    have he0 : H z.1 (tangentRay b z.2) = H z.1 0 := by
      rw [map_zero]
      apply Prod.ext
      · change (H z.1 (tangentRay b z.2)).1 = 0
        simpa only [hs,zero_smul] using he
      · exact hs
    exact tangentRay_ne_zero b z.2 (hI z.1 hz.1.1 he0)
  have heq (z) (hz : z ∈ C) : tangentSlope H b z = a := by
    have he : (H z.1 (tangentRay b z.2)).1 =
        (H z.1 (tangentRay b z.2)).2 • a := sub_eq_zero.mp hz.2
    change (H z.1 (tangentRay b z.2)).2⁻¹ • (H z.1 (tangentRay b z.2)).1 = a
    rw [he,smul_smul,inv_mul_cancel₀ (hU hz),one_smul]
  have hfin := PublishedInputs.finite_compact_coordinate_regular_fiber
    (tangentSlopeDomain_open hH b) (tangentSlope_smoothOn hH b) hcomp hU a
    (fun z _ he => hreg z (hU ‹z ∈ C›) he)
  exact hfin.subset (fun z hz => ⟨hz,heq z hz⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_EuclideanImmersionReduction
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension reduction of the ordinary Whitney embedding to a smooth
immersion of a compact surface in four-dimensional Euclidean space. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma euclideanPad_injective {n m : ℕ} (hn : n ≤ m) :
    Function.Injective (euclideanPad n m) := by
  intro v w he
  ext i
  have h := congrArg (fun z : ProjectionTarget m => z ⟨i.val,lt_of_lt_of_le i.isLt hn⟩) he
  simpa [euclideanPad,i.isLt] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma smooth_immersion_postcompose (L : V →L[ℝ] W) (hL : Function.Injective L)
    {F : M → V} (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) F p)) :
    ContMDiff planeModel 𝓘(ℝ,W) ∞ (L ∘ F) ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,W) (L ∘ F) p) := by
  have hLc : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,W) ∞ L := L.contDiff.contMDiff
  refine ⟨hLc.comp hF,?_⟩
  intro p
  rw [mfderiv_comp p (hLc.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt
    (hF.mdifferentiable (by simp)).mdifferentiableAt,mfderiv_eq_fderiv,L.fderiv]
  exact hL.comp (hI p)

variable [IsManifold planeModel ∞ M] [CompactSpace M]

theorem SmoothingAtlas.reduce_immersion_dimension (A : SmoothingAtlas M) (n : ℕ) :
    (∃ F : M → ProjectionTarget n, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget n) ∞ F ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget n) F p)) →
    ∃ G : M → ProjectionTarget 4, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 4) ∞ G ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 4) G p) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rintro ⟨F,hF,hI⟩
    by_cases hn : n ≤ 4
    · exact ⟨euclideanPad n 4 ∘ F,
        smooth_immersion_postcompose (euclideanPad n 4) (euclideanPad_injective hn) hF hI⟩
    · have hn0 : n ≠ 0 := by omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      let e : ProjectionTarget (k+1) ≃L[ℝ] ProjectionTarget k × ℝ :=
        ContinuousLinearEquiv.ofFinrankEq (by simp)
      obtain ⟨he,heI⟩ := smooth_immersion_postcompose e.toContinuousLinearMap e.injective hF hI
      obtain ⟨a,hg,hgI⟩ := A.exists_projected_immersion (show 4 ≤ k by omega) he heI
      exact ih k (Nat.lt_succ_self k) ⟨graphProjection a ∘ (e ∘ F),hg,hgI⟩

variable [T2Space M]

/-- The ordinary four-dimensional immersion is proved without the
three-dimensional Whitney input used in the conditional isometric theorem. -/
theorem exists_smooth_euclidean_four_immersion :
    ∃ F : M → ProjectionTarget 4, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 4) ∞ F ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 4) F p) := by
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  obtain ⟨n,F,hF,_hclosed,hI⟩ := exists_embedding_euclidean_of_compact (I := planeModel) (M := M)
  exact A.reduce_immersion_dimension n ⟨F,hF,hI⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteSingularProjection
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual smooth map of every compact surface into three-space with
only finitely many singular points. The regularity of its direction
parameter maps is retained for the subsequent local analysis. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma projectionJet_smooth {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F) (i : A.centers) :
    ContDiff ℝ ∞ (A.projectionJet F i) :=
  weightedJet_smooth
    (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i))
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF)

theorem finite_singular_projection {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) F p))
    (a : ProjectionTarget 3)
    (hreg : ∀ i b z, z ∈ tangentSlopeDomain (A.projectionJet F i) b →
      tangentSlope (A.projectionJet F i) b z = a →
      Function.Surjective (fderiv ℝ (tangentSlope (A.projectionJet F i) b) z)) :
    {p | ¬ Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (graphProjection a ∘ F) p)}.Finite := by
  classical
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (graphProjection a ∘ F) :=
    (graphProjection a).contDiff.contMDiff.comp hF
  have hji (i : A.centers) (x : Base) (hx : x ∈ A.coordinateCore i) :
      Function.Injective (A.projectionJet F i x) :=
    (localized_weightedJet_injective_iff (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (i : M)
      (A.weight_smooth i) (A.weight_support i) (A.coordinateCore_target i hx)
      (A.coordinateCore_weight_nonzero i hx)).mpr (hI _)
  let D (i : A.centers) (b : Bool) :=
    compactProjectionDirections a (A.projectionJet F i) (A.coordinateCore i) b
  have hD (i : A.centers) (b : Bool) : (D i b).Finite :=
    finite_compact_projection_directions (A.projectionJet_smooth hF i)
      (A.coordinateCore_compact i) (hji i) a b (hreg i b)
  have hfinite : (⋃ i : A.centers, ⋃ b : Bool,
      (fun z : Base × ℝ => (chart (i : M)).symm z.1) '' D i b).Finite :=
    Set.finite_iUnion (fun i => Set.finite_iUnion (fun b => (hD i b).image _))
  apply hfinite.subset
  intro p hp
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  let x := chart (i : M) p
  have hx : x ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hbad : ¬ Function.Injective ((graphProjection a).comp (A.projectionJet F i x)) := by
    intro hinj
    have hnew : Function.Injective (weightedJet (localizedWeight (i : M) (A.weight i))
        (localize (i : M) (A.weight i) (graphProjection a ∘ F)) x) := by
      rw [localize_clm,weightedJet_comp _ _
        ((localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).differentiable
          (by simp) x)]
      exact hinj
    have hImm := (localized_weightedJet_injective_iff (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (i : M)
      (A.weight_smooth i) (A.weight_support i) (A.coordinateCore_target i hx)
      (A.coordinateCore_weight_nonzero i hx)).mp hnew
    apply hp
    change Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3)
      (graphProjection a ∘ F) ((chart (i : M)).symm (chart (i : M) p))) at hImm
    rwa [(chart (i : M)).left_inv (A.weightCore_source i hi)] at hImm
  obtain ⟨b,t,ht,hker⟩ := exists_bounded_tangentRay_in_kernel _ hbad
  apply mem_iUnion.mpr
  refine ⟨i,mem_iUnion.mpr ⟨b,?_⟩⟩
  refine ⟨(x,t),⟨⟨hx,ht⟩,hker⟩,?_⟩
  exact (chart (i : M)).left_inv (A.weightCore_source i hi)

theorem exists_finite_singular_projection {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) F p)) :
    ∃ a : ProjectionTarget 3,
      (∀ i b z, z ∈ tangentSlopeDomain (A.projectionJet F i) b →
        tangentSlope (A.projectionJet F i) b z = a →
        Function.Surjective (fderiv ℝ (tangentSlope (A.projectionJet F i) b) z)) ∧
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (graphProjection a ∘ F) ∧
      {p | ¬ Function.Injective
        (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (graphProjection a ∘ F) p)}.Finite := by
  obtain ⟨a,_ha,hreg⟩ := exists_regular_projection_parameter
    (A.projectionJet F) (A.projectionJet_smooth hF) univ isOpen_univ Set.univ_nonempty
  exact ⟨a,hreg,(graphProjection a).contDiff.contMDiff.comp hF,
    A.finite_singular_projection hF hI a hreg⟩

end SmoothingAtlas

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionLocalRepresentatives
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globally smooth representatives for the original immersion in each
active coordinate core, with the exact weighted-jet germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_projection_representatives {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F) :
    ∃ Φ : A.centers → Base → ProjectionTarget 3 × ℝ,
      (∀ i, ContDiff ℝ ∞ (Φ i)) ∧
      ∀ i x, x ∈ A.coordinateCore i →
        Φ i =ᶠ[𝓝 x] F ∘ (chart (i : M)).symm := by
  have hc (i : A.centers) : ContDiffOn ℝ ∞
      (F ∘ (chart (i : M)).symm) (chart (i : M)).target :=
    (hF.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  choose U hU hKU _ Φ hΦ hEq using fun i =>
    CollarVelocity.compact_smooth_extension (A.coordinateCore_compact i)
      (chart (i : M)).open_target (A.coordinateCore_target i) (hc i)
  refine ⟨Φ,hΦ,?_⟩
  intro i x hx
  filter_upwards [(hU i).mem_nhds (hKU i hx)] with y hy
  exact hEq i hy

omit [CompactSpace M] in
lemma localizedWeight_ne_zero_on_core (i : A.centers) {x : Base}
    (hx : x ∈ A.coordinateCore i) : localizedWeight (i : M) (A.weight i) x ≠ 0 := by
  have hxT := A.coordinateCore_target i hx
  have hw := A.coordinateCore_weight_nonzero i hx
  simpa only [localizedWeight,localize,indicator_of_mem hxT,smul_eq_mul,mul_one]
    using pow_ne_zero 2 hw

theorem projectionJet_representative_germ {F : M → ProjectionTarget 3 × ℝ}
    (i : A.centers) {Φ : Base → ProjectionTarget 3 × ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {x : Base} (hx : x ∈ A.coordinateCore i)
    (he : Φ =ᶠ[𝓝 x] F ∘ (chart (i : M)).symm) :
    A.projectionJet F i =ᶠ[𝓝 x] fun y =>
      (localizedWeight (i : M) (A.weight i) y)^2 • fderiv ℝ Φ y := by
  have hp : localize (i : M) (A.weight i) F =ᶠ[𝓝 x]
      fun y => localizedWeight (i : M) (A.weight i) y • Φ y := by
    filter_upwards [he,(chart (i : M)).open_target.mem_nhds (A.coordinateCore_target i hx)]
      with y hy hyT
    simp only [localizedWeight,localize,indicator_of_mem hyT,smul_eq_mul,mul_one,hy]
    rfl
  exact weightedJet_product_germ
    (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i)) hΦ hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ProjectionCrosscapJet
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nondegenerate second-jet condition at a singularity of a regular
three-dimensional projection. This concerns the original unweighted
coordinate representative, not merely the weighted atlas derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem regular_projection_crosscap_jet {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (i : A.centers) {Φ : Base → ProjectionTarget 3 × ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {x : Base} (hx : x ∈ A.coordinateCore i)
    (he : Φ =ᶠ[𝓝 x] F ∘ (chart (i : M)).symm)
    (a : ProjectionTarget 3) (b : Bool) (t : ℝ)
    (hz : (x,t) ∈ tangentSlopeDomain (A.projectionJet F i) b)
    (ha : tangentSlope (A.projectionJet F i) b (x,t) = a)
    (hreg : Function.Surjective (fderiv ℝ (tangentSlope (A.projectionJet F i) b) (x,t))) :
    graphProjection a (fderiv ℝ Φ x (tangentRay b t)) = 0 ∧
      Function.Bijective (projectedCrosscapJet Φ a b x t) := by
  let w := localizedWeight (i : M) (A.weight i)
  have hw : ContDiff ℝ ∞ w :=
    localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
  have hw0 : (w x)^2 ≠ 0 := pow_ne_zero 2 (A.localizedWeight_ne_zero_on_core i hx)
  have hK := A.projectionJet_representative_germ i hΦ hx he
  have hzeroK : graphProjection a (A.projectionJet F i x (tangentRay b t)) = 0 := by
    rw [← ha]
    change (A.projectionJet F i x (tangentRay b t)).1 -
      (A.projectionJet F i x (tangentRay b t)).2 •
        ((A.projectionJet F i x (tangentRay b t)).2⁻¹ •
          (A.projectionJet F i x (tangentRay b t)).1) = 0
    rw [smul_smul,mul_inv_cancel₀ hz,one_smul,sub_self]
  have hzero : graphProjection a (fderiv ℝ Φ x (tangentRay b t)) = 0 := by
    rw [hK.self_of_nhds] at hzeroK
    change graphProjection a ((w x)^2 • fderiv ℝ Φ x (tangentRay b t)) = 0 at hzeroK
    rw [map_smul] at hzeroK
    exact (smul_eq_zero.mp hzeroK).resolve_left hw0
  refine ⟨hzero,?_⟩
  exact regular_weighted_directionJet (hΦ.fderiv_right (m := ∞) (by simp))
    (hw.pow 2) a b x t hw0 hK hzero
    (regular_tangentSlope_linearization_bijective (A.projectionJet_smooth hF i)
      a b (x,t) hz ha hreg)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionSingularDirection
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every singular point of a regular projection has a compact direction
parameter and the nondegenerate unweighted crosscap jet. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem singular_projection_direction {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) F p))
    (a : ProjectionTarget 3) (p : M)
    (hp : ¬ Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (graphProjection a ∘ F) p)) :
    ∃ (i : A.centers) (b : Bool) (t : ℝ), p ∈ A.weightCore i ∧ t ∈ Icc (-1 : ℝ) 1 ∧
      (chart (i : M) p,t) ∈ tangentSlopeDomain (A.projectionJet F i) b ∧
      tangentSlope (A.projectionJet F i) b (chart (i : M) p,t) = a := by
  classical
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (graphProjection a ∘ F) :=
    (graphProjection a).contDiff.contMDiff.comp hF
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  let x := chart (i : M) p
  have hx : x ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hbad : ¬ Function.Injective ((graphProjection a).comp (A.projectionJet F i x)) := by
    intro hinj
    have hnew : Function.Injective (weightedJet (localizedWeight (i : M) (A.weight i))
        (localize (i : M) (A.weight i) (graphProjection a ∘ F)) x) := by
      rw [localize_clm,weightedJet_comp _ _
        ((localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).differentiable
          (by simp) x)]
      exact hinj
    have hImm := (localized_weightedJet_injective_iff (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (i : M)
      (A.weight_smooth i) (A.weight_support i) (A.coordinateCore_target i hx)
      (A.coordinateCore_weight_nonzero i hx)).mp hnew
    apply hp
    change Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3)
      (graphProjection a ∘ F) ((chart (i : M)).symm (chart (i : M) p))) at hImm
    rwa [(chart (i : M)).left_inv (A.weightCore_source i hi)] at hImm
  have hjet : Function.Injective (A.projectionJet F i x) :=
    (localized_weightedJet_injective_iff (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (i : M)
      (A.weight_smooth i) (A.weight_support i) (A.coordinateCore_target i hx)
      (A.coordinateCore_weight_nonzero i hx)).mpr (hI _)
  obtain ⟨b,t,ht,hker⟩ := exists_bounded_tangentRay_in_kernel _ hbad
  have hfst : (A.projectionJet F i x (tangentRay b t)).1 =
      (A.projectionJet F i x (tangentRay b t)).2 • a := sub_eq_zero.mp hker
  have hlast : (A.projectionJet F i x (tangentRay b t)).2 ≠ 0 := by
    intro hz
    have he0 : A.projectionJet F i x (tangentRay b t) = A.projectionJet F i x 0 := by
      rw [map_zero]
      apply Prod.ext
      · change (A.projectionJet F i x (tangentRay b t)).1 = 0
        simpa only [hz,zero_smul] using hfst
      · exact hz
    exact tangentRay_ne_zero b t (hjet he0)
  refine ⟨i,b,t,hi,ht,hlast,?_⟩
  change (A.projectionJet F i x (tangentRay b t)).2⁻¹ •
    (A.projectionJet F i x (tangentRay b t)).1 = a
  rw [hfst,smul_smul,inv_mul_cancel₀ hlast,one_smul]

theorem singular_projection_crosscap_jet {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) F p))
    (a : ProjectionTarget 3)
    (hreg : ∀ i b z, z ∈ tangentSlopeDomain (A.projectionJet F i) b →
      tangentSlope (A.projectionJet F i) b z = a →
      Function.Surjective (fderiv ℝ (tangentSlope (A.projectionJet F i) b) z))
    (p : M) (hp : ¬ Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (graphProjection a ∘ F) p)) :
    ∃ (i : A.centers) (b : Bool) (t : ℝ) (Φ : Base → ProjectionTarget 3 × ℝ),
      p ∈ A.weightCore i ∧ t ∈ Icc (-1 : ℝ) 1 ∧ ContDiff ℝ ∞ Φ ∧
      Φ =ᶠ[𝓝 (chart (i : M) p)] F ∘ (chart (i : M)).symm ∧
      graphProjection a (fderiv ℝ Φ (chart (i : M) p) (tangentRay b t)) = 0 ∧
      Function.Bijective (projectedCrosscapJet Φ a b (chart (i : M) p) t) := by
  obtain ⟨i,b,t,hi,ht,hdom,hval⟩ := A.singular_projection_direction hF hI a p hp
  obtain ⟨Φ,hΦ,hgerm⟩ := A.exists_projection_representatives hF
  have hx : chart (i : M) p ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hres := A.regular_projection_crosscap_jet hF i (hΦ i) hx (hgerm i _ hx)
    a b t hdom hval (hreg i b _ hdom hval)
  exact ⟨i,b,t,Φ i,hi,ht,hΦ i,hgerm i _ hx,hres⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceDirectionJet
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-direction map of an actual three-dimensional surface,
and its relation to the unweighted projection jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceDirection_projected {Φ : Base → ProjectionTarget 3 × ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (a : ProjectionTarget 3) (b : Bool) (z : Base × ℝ) :
    surfaceDirection (graphProjection a ∘ Φ) b z =
      graphProjection a (fderiv ℝ Φ z.1 (tangentRay b z.2)) := by
  rw [surfaceDirection,fderiv_comp z.1 (graphProjection a).differentiableAt
    (hΦ.differentiable (by simp) z.1),(graphProjection a).fderiv]
  rfl

lemma surfaceDirection_projected_fderiv {Φ : Base → ProjectionTarget 3 × ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (a : ProjectionTarget 3) (b : Bool) (z : Base × ℝ) :
    fderiv ℝ (surfaceDirection (graphProjection a ∘ Φ) b) z =
      projectedCrosscapJet Φ a b z.1 z.2 := by
  have hd := (graphProjection a).hasFDerivAt.comp z
    (hasFDerivAt_tangent_direction (hΦ.fderiv_right (m := ∞) (by simp)) b z)
  have he : surfaceDirection (graphProjection a ∘ Φ) b =
      graphProjection a ∘ (fun w : Base × ℝ => fderiv ℝ Φ w.1 (tangentRay b w.2)) := by
    funext w
    exact surfaceDirection_projected hΦ a b w
  rw [he,hd.fderiv]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularCrosscapRepresentatives
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An unconditional generic map to three-space with finitely many
singularities, expressed using the actual derivative-direction map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_regular_crosscap_map_oai :
    ∃ f : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite ∧
      ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
        ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
          p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
          φ =ᶠ[𝓝 (chart q p)] f ∘ (chart q).symm ∧
          surfaceDirection φ b (chart q p,t) = 0 ∧
          Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)) := by
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  obtain ⟨F,hF,hI⟩ := exists_smooth_euclidean_four_immersion (M := M)
  let e : ProjectionTarget 4 ≃L[ℝ] ProjectionTarget 3 × ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨he,heI⟩ := smooth_immersion_postcompose e.toContinuousLinearMap e.injective hF hI
  obtain ⟨a,hreg,hg,hfin⟩ := A.exists_finite_singular_projection he heI
  refine ⟨graphProjection a ∘ (e ∘ F),hg,hfin,?_⟩
  intro p hp
  obtain ⟨i,b,t,Φ,hi,_ht,hΦ,heq,hzero,hbij⟩ :=
    A.singular_projection_crosscap_jet he heI a hreg p hp
  refine ⟨(i : M),graphProjection a ∘ Φ,b,t,A.weightCore_source i hi,
    (graphProjection a).contDiff.comp hΦ,?_,?_,?_⟩
  · filter_upwards [heq] with x hx
    exact congrArg (graphProjection a) hx
  · rw [surfaceDirection_projected hΦ]
    exact hzero
  · rw [surfaceDirection_projected_fderiv hΦ]
    exact hbij

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_regular_crosscap_map_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_regular_crosscap_map_oai.{u_1}
