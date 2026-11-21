-- Prove2me | solution 1 for MasulloRH.rational_adele_theta_image
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:11:46.970159+00:00
-- url     : https://prove2.me/submissions/1970e403-e8a0-4fb8-aec4-c67bfe2430f9

import Mathlib
import Definitions.Def_MasulloRH_RationalFiniteRadial
import Definitions.Def_NumberField_AdelicFourier
import Theorems.Thm_MasulloRH_finite_adele_radial_synthesis
import Theorems.Thm_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff
import Theorems.Thm_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod

section
open NumberField MeasureTheory
open scoped SchwartzMap Topology Classical
namespace MasulloRH.RationalArch
noncomputable section

abbrev M := mixedEmbedding.mixedSpace ℚ
private abbrev RPlace := {w : InfinitePlace ℚ // w.IsReal}
private abbrev CPlace := {w : InfinitePlace ℚ // w.IsComplex}
def realPlace : {w : InfinitePlace ℚ // w.IsReal} := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

private local instance uniqueReal : Unique RPlace :=
  ⟨⟨realPlace⟩,fun _ => Subsingleton.elim _ _⟩

private local instance emptyComplex : IsEmpty CPlace :=
  ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.val)) w.prop⟩

/-- The canonical real coordinate on the mixed archimedean space of ℚ. -/
def mixedCoord : M ≃L[ℝ] ℝ :=
  (ContinuousLinearEquiv.prodUnique ℝ (RPlace → ℝ) (CPlace → ℂ)).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : RPlace => ℝ))

@[simp] theorem mixedCoord_apply (x : M) : mixedCoord x = x.1 realPlace := rfl

@[simp] theorem mixedCoord_symm_apply (x : ℝ) :
    mixedCoord.symm x = algebraMap ℝ M x := by
  apply mixedCoord.injective
  rw [mixedCoord.apply_symm_apply]
  rfl

def mixedRingEquiv : M ≃+* ℝ where
  toEquiv := mixedCoord.toEquiv
  map_mul' _ _ := rfl
  map_add' := mixedCoord.map_add

@[simp] theorem mixedCoord_mixedEmbedding (q : ℚ) :
    mixedCoord (mixedEmbedding ℚ q) = (q:ℝ) := by
  simp only [mixedCoord_apply,mixedEmbedding.mixedEmbedding_apply_isReal]
  exact map_ratCast _ q

def archSection : ℝ →+* InfiniteAdeleRing ℚ :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm.toRingHom.comp mixedRingEquiv.symm.toRingHom

@[simp] theorem mixed_eq_archSection (x : ℝ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (archSection x) = mixedCoord.symm x :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).apply_symm_apply _

@[simp] theorem archSection_ratCast (q : ℚ) :
    archSection (q : ℝ) = algebraMap ℚ (InfiniteAdeleRing ℚ) q := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).injective
  rw [mixed_eq_archSection, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact mixedCoord.symm_apply_eq.mpr (mixedCoord_mixedEmbedding q).symm

@[simp] theorem mixedCoord_archSection_mul_rat (x : ℝ) (q : ℚ) :
    mixedCoord (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ
      (archSection x * algebraMap ℚ (InfiniteAdeleRing ℚ) q)) = x*(q:ℝ) := by
  rw [← archSection_ratCast,←map_mul,mixed_eq_archSection,mixedCoord.apply_symm_apply]

theorem mixedCoord_measurePreserving :
    MeasurePreserving mixedCoord (volume : Measure M) (volume : Measure ℝ) := by
  let : IsProbabilityMeasure (volume : Measure (CPlace → ℂ)) :=
    ⟨Measure.pi_empty_univ (fun _ : CPlace => (volume : Measure ℂ))⟩
  have hfst : MeasurePreserving (Prod.fst : M → (RPlace → ℝ))
      ((volume : Measure (RPlace → ℝ)).prod (volume : Measure (CPlace → ℂ))) volume :=
    measurePreserving_fst
  have hcoord := volume_preserving_funUnique RPlace ℝ
  have hidx : @Unique.fintype RPlace _ = Subtype.fintype InfinitePlace.IsReal := Subsingleton.elim _ _
  rw [hidx] at hcoord
  exact hcoord.comp hfst

theorem mixedCoord_symm_measurePreserving :
    MeasurePreserving mixedCoord.symm (volume : Measure ℝ) (volume : Measure M) := by
  let e := mixedCoord.toHomeomorph.toMeasurableEquiv
  have h : MeasurePreserving e (volume : Measure M) volume := mixedCoord_measurePreserving
  exact h.symm

theorem integral_mixed_to_real (g : M → ℂ) :
    (∫ x : M, g x) = ∫ t : ℝ, g (mixedCoord.symm t) := by
  exact (mixedCoord_symm_measurePreserving.integral_comp
    mixedCoord.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding _).symm

/-- Write an archimedean Schwartz function in the real coordinate. -/
def toRealTest : 𝓢(M,ℂ) →L[ℂ] 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ mixedCoord.symm

/-- Lift a real Schwartz function to the mixed archimedean coordinate. -/
def ofRealTest : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(M,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ mixedCoord

@[simp] theorem toRealTest_apply (g : 𝓢(M,ℂ)) (x : ℝ) :
    toRealTest g x = g (mixedCoord.symm x) := rfl

@[simp] theorem ofRealTest_apply (g : 𝓢(ℝ,ℂ)) (x : M) :
    ofRealTest g x = g (mixedCoord x) := rfl

@[simp] theorem toRealTest_ofRealTest (g : 𝓢(ℝ,ℂ)) : toRealTest (ofRealTest g) = g := by
  ext x
  simp

@[simp] theorem ofRealTest_toRealTest (g : 𝓢(M,ℂ)) : ofRealTest (toRealTest g) = g := by
  ext x
  simp only [ofRealTest_apply,toRealTest_apply,ContinuousLinearEquiv.symm_apply_apply]

theorem realTest_at_rational_scale (g : 𝓢(M,ℂ)) (t : ℝ) (q : ℚ) :
    g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ
      (archSection t * algebraMap ℚ (InfiniteAdeleRing ℚ) q)) = toRealTest g (t*(q:ℝ)) := by
  rw [←archSection_ratCast,←map_mul,mixed_eq_archSection]
  rfl

end
end MasulloRH.RationalArch
end

section
open NumberField NumberField.AdelicBox MeasureTheory IsDedekindDomain Set
open scoped Classical SchwartzMap
namespace MasulloRH.RationalArch
noncomputable section

abbrev FinA := FiniteAdeleRing (𝓞 ℚ) ℚ
abbrev FullA := AdeleRing (𝓞 ℚ) ℚ

theorem sigmaCompact_finiteAdeles : SigmaCompactSpace FinA := by
  let B (d : ℚ) := (fun z : FinA => algebraMap ℚ FinA d * z) '' integralFiniteAdeles (𝓞 ℚ) ℚ
  apply SigmaCompactSpace.of_countable (Set.range B) (Set.countable_range _)
  · rintro _ ⟨d,rfl⟩
    exact (isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id)
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨s,hs,hx⟩ := exists_mul_mem_integralFiniteAdeles (𝓞 ℚ) ℚ x
    have hs' : (s:ℚ) ≠ 0 := by exact_mod_cast hs
    apply Set.mem_sUnion_of_mem _ (Set.mem_range_self (s:ℚ)⁻¹)
    refine ⟨algebraMap ℚ FinA (s:ℚ) * x,hx,?_⟩
    dsimp only
    rw [←mul_assoc,←map_mul,inv_mul_cancel₀ hs',map_one,one_mul]

private local instance : SigmaCompactSpace FinA := sigmaCompact_finiteAdeles

theorem rational_integerLattice_covolume :
    ZLattice.covolume (mixedEmbedding.integerLattice ℚ) (volume : Measure M) = 1 := by
  rw [mixedEmbedding.covolume_integerLattice, IsTotallyReal.nrComplexPlaces_eq_zero,
    Rat.numberField_discr]
  norm_num

variable [MeasurableSpace FullA] [BorelSpace FullA]
  (μ : Measure FullA) [μ.IsAddHaarMeasure]
  [MeasurableSpace FinA] [BorelSpace FinA] (ν : Measure FinA) [ν.IsAddHaarMeasure]

def haarFactor : ℝ := (μ (adelicBox ℚ)).toReal / (ν (integralFiniteAdeles (𝓞 ℚ) ℚ)).toReal

private theorem mixed_map_haar :
    0 < haarFactor μ ν ∧
    Measure.map (fun x : FullA => (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1,x.2)) μ =
      (haarFactor μ ν).toNNReal • (volume : Measure M).prod ν := by
  simpa only [haarFactor,rational_integerLattice_covolume,one_mul] using
    map_ringEquiv_mixedSpace_eq_smul_volume_prod ℚ μ ν

theorem haarFactor_pos : 0 < haarFactor μ ν := (mixed_map_haar μ ν).1

omit [BorelSpace FullA] [μ.IsAddHaarMeasure] [BorelSpace FinA] [ν.IsAddHaarMeasure] in
theorem haarFactor_eq_one_of_normalized (hμ : μ (adelicBox ℚ) = 1)
    (hν : ν (integralFiniteAdeles (𝓞 ℚ) ℚ) = 1) : haarFactor μ ν = 1 := by
  simp [haarFactor,hμ,hν]

private theorem measurable_mixed_finite :
    Measurable (fun x : FullA => (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1,x.2)) := by
  apply Measurable.prodMk
  · apply Continuous.measurable
    exact (continuous_ringEquiv_mixedSpace ℚ).comp (show Continuous (fun x : FullA => x.1) from continuous_fst)
  · apply Continuous.measurable
    exact (show Continuous (fun x : FullA => x.2) from continuous_snd)

include ν in
theorem integrable_pureTensor (g : 𝓢(M,ℂ)) (h : FinA → ℂ)
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    Integrable (fun x : FullA => g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * h x.2) μ := by
  let E (x : FullA) := (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1,x.2)
  let W (x : M × FinA) := g x.1 * h x.2
  have hW : Integrable W ((volume : Measure M).prod ν) :=
    g.integrable.mul_prod (hlc.continuous.integrable_of_hasCompactSupport hcs)
  have hWE : Integrable W (Measure.map E μ) := by
    rw [(mixed_map_haar μ ν).2]
    exact hW.smul_measure_nnreal
  exact hWE.comp_measurable measurable_mixed_finite

theorem integral_pureTensor (g : 𝓢(M,ℂ)) (h : FinA → ℂ) (hlc : IsLocallyConstant h) :
    (∫ x : FullA, g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * h x.2 ∂μ) =
      (haarFactor μ ν : ℂ) * ((∫ t : ℝ, toRealTest g t) * ∫ a : FinA, h a ∂ν) := by
  let E (x : FullA) := (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1,x.2)
  let W (x : M × FinA) := g x.1 * h x.2
  have hW : StronglyMeasurable W := (g.continuous.comp continuous_fst).mul
    (hlc.continuous.comp continuous_snd) |>.stronglyMeasurable
  change (∫ x, W (E x) ∂μ) = _
  rw [←integral_map_of_stronglyMeasurable measurable_mixed_finite hW,
    (mixed_map_haar μ ν).2, integral_smul_nnreal_measure]
  change (haarFactor μ ν).toNNReal •
    (∫ x : M × FinA, g x.1 * h x.2 ∂(volume.prod ν)) = _
  rw [integral_prod_mul,integral_mixed_to_real,NNReal.smul_def,
    Real.coe_toNNReal _ (haarFactor_pos μ ν).le,Complex.real_smul]
  rfl

include ν in
theorem integrable_schwartzBruhat {F : FullA → ℂ} (hF : F ∈ AdelicFourier.schwartzBruhat ℚ) :
    Integrable F μ := by
  induction hF using AdelicFourier.schwartzBruhat_induction with
  | tensor F hF =>
    obtain ⟨g,h,hlc,hcs,rfl⟩ := hF
    exact integrable_pureTensor μ ν g h hlc hcs
  | zero => exact integrable_zero _ _ _
  | add f g hf hg hf' hg' => exact hf'.add hg'
  | smul c f hf hf' => exact hf'.smul c

end
end MasulloRH.RationalArch
end

section
open NumberField NumberField.AdelicBox MeasureTheory Set Filter
open scoped SchwartzMap Topology
namespace MasulloRH.RationalFinite
noncomputable section

private def integerSubring : Subring A where
  carrier := O
  one_mem' := fun v => one_mem (v.adicCompletionIntegers ℚ)
  add_mem' := fun hx hy v => add_mem (hx v) (hy v)
  mul_mem' := fun hx hy v => mul_mem (hx v) (hy v)
  neg_mem' := fun hx v => neg_mem (hx v)
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers ℚ)

private theorem diagonal_integral_iff (q : ℚ) : diag q ∈ O ↔ ∃ m : ℤ, q = m := by
  have hh := NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff ℚ
    (1 : 𝓞 ℚ) one_ne_zero 0 q
  simp only [map_zero,map_one,zero_add,one_mul,Set.image_id'] at hh
  constructor
  · intro h
    obtain ⟨a,ha⟩ := hh.mp h
    exact ⟨Rat.ringOfIntegersEquiv a, ha.trans (Rat.ringOfIntegersEquiv_apply_coe a).symm⟩
  · rintro ⟨m,rfl⟩
    exact hh.mpr ⟨Rat.ringOfIntegersEquiv.symm m, (Rat.ringOfIntegersEquiv_symm_apply_coe m).symm⟩

private theorem invert_diag_mul (r : ℚ) (hr : r ≠ 0) (x : A) : diag r⁻¹ * (diag r*x) = x := by
  rw [← mul_assoc,← map_mul,inv_mul_cancel₀ hr,map_one,one_mul]

private theorem mem_centered_iff (s : ℚ) (hs : s ≠ 0) (x : A) :
    x ∈ centeredBall s ↔ diag s⁻¹ * x ∈ O := by
  constructor
  · rintro ⟨z,hz,rfl⟩
    change diag s⁻¹ * (diag s * z) ∈ O
    rwa [invert_diag_mul s hs]
  · intro hx
    refine ⟨_,hx,?_⟩
    change diag s * (diag s⁻¹ * x) = x
    rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hs,map_one,one_mul]

private theorem rational_mem_centered_iff (q s : ℚ) (hs : s ≠ 0) :
    diag q ∈ centeredBall s ↔ ∃ m : ℤ, q = s * m := by
  rw [mem_centered_iff _ hs,← map_mul,diagonal_integral_iff]
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,by rw [←hm]; field_simp⟩
  · rintro ⟨m,rfl⟩
    exact ⟨m,by field_simp⟩

private theorem unit_mul_mem_centeredBall_iff (u : K) (d : ℚ) (x : A) :
    (u.val:A)*x ∈ centeredBall d ↔ x ∈ centeredBall d := by
  have h (v : K) {y : A} (hy : y ∈ centeredBall d) : (v.val:A)*y ∈ centeredBall d := by
    obtain ⟨z,hz,rfl⟩ := hy
    refine ⟨(v.val:A)*z,fun w => mul_mem (v.property.1 w) (hz w),?_⟩
    change _ = (v.val:A)*(diag d*z)
    ring
  constructor
  · intro hx
    have ht := h u⁻¹ hx
    change (↑u.val⁻¹:A)*((u.val:A)*x) ∈ _ at ht
    simpa only [← mul_assoc, Units.inv_mul,one_mul] using ht
  · exact h u

/-- Compact sets in the finite rational adeles have a common denominator. -/
theorem compact_subset_denominator_ball {C : Set A} (hC : IsCompact C) :
    ∃ d : ℚ, d ≠ 0 ∧ C ⊆ centeredBall d := by
  let I := {n : ℤ // n ≠ 0}
  let : Nonempty I := ⟨⟨1,one_ne_zero⟩⟩
  let U (n : I) := (fun x : A => (n.1:A)*x) ⁻¹' O
  have hcov : C ⊆ ⋃ n : I, U n := by
    intro x _
    obtain ⟨s,hs,hx⟩ := exists_mul_mem_integralFiniteAdeles (𝓞 ℚ) ℚ x
    let n := Rat.ringOfIntegersEquiv s
    have hn : n ≠ 0 := fun h => hs (Rat.ringOfIntegersEquiv.injective (h.trans (map_zero _).symm))
    apply Set.mem_iUnion.mpr
    refine ⟨⟨n,hn⟩,?_⟩
    change (n:A)*x ∈ O
    have he : (n:A) = algebraMap (𝓞 ℚ) A s := by
      have hq : (n:ℚ) = (s:ℚ) := Rat.ringOfIntegersEquiv_apply_coe s
      calc
        _ = diag (n:ℚ) := (map_intCast _ _).symm
        _ = _ := by rw [hq]; rfl
    rw [he]
    exact hx
  have hd : Directed (· ⊆ ·) U := by
    intro a b
    refine ⟨⟨a.1*b.1,mul_ne_zero a.2 b.2⟩, ?_, ?_⟩
    · intro x hx
      change ((a.1*b.1:ℤ):A)*x ∈ integerSubring
      rw [Int.cast_mul,mul_comm (a.1:A),mul_assoc]
      exact integerSubring.mul_mem (intCast_mem _ _) hx
    · intro x hx
      change ((a.1*b.1:ℤ):A)*x ∈ integerSubring
      rw [Int.cast_mul,mul_assoc]
      exact integerSubring.mul_mem (intCast_mem _ _) hx
  obtain ⟨n,hn⟩ := hC.elim_directed_cover U (fun n => (isOpen_integralFiniteAdeles ℚ).preimage
    (continuous_const.mul continuous_id)) hcov hd
  have hnq : (n.1:ℚ) ≠ 0 := by exact_mod_cast n.2
  refine ⟨(n.1:ℚ)⁻¹,inv_ne_zero hnq,?_⟩
  intro x hx
  rw [mem_centered_iff _ (inv_ne_zero hnq), inv_inv, map_intCast]
  exact hn hx

/-- A single lattice contains every rational at which one of the unit rotations is nonzero. -/
theorem common_unit_lattice {h : A → ℂ} (hcs : HasCompactSupport h) :
    ∃ d : ℚ, d ≠ 0 ∧ ∀ u : K, ∀ q : ℚ,
      q ∉ Set.range (fun n : ℤ => d*n) → h ((u.val:A)*diag q) = 0 := by
  obtain ⟨d,hd,hm⟩ := compact_subset_denominator_ball hcs
  refine ⟨d,hd,fun u q hq => ?_⟩
  by_contra hn
  exact hq (by
    obtain ⟨n,hn⟩ := (rational_mem_centered_iff q d hd).mp ((unit_mul_mem_centeredBall_iff u d _).mp
      (hm (subset_tsupport h hn)))
    exact ⟨n,hn.symm⟩)

private theorem lattice_injective {d : ℚ} (hd : d ≠ 0) :
    Function.Injective (fun n : ℤ => d*n) := by
  intro m n h
  exact_mod_cast mul_left_cancel₀ hd h

/-- Absolute convergence of the Archimedean Schwartz theta series on any nonzero lattice. -/
theorem schwartz_lattice_summable (g : 𝓢(ℝ,ℂ)) {a : ℝ} (ha : a ≠ 0) :
    Summable (fun n : ℤ => ‖g (a*n)‖) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e g
  have hs : Summable (fun n : ℤ => f (n:ℝ)) := summable_of_isBigO
    (Real.summable_abs_int_rpow one_lt_two) ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  exact hs.norm

/-- The restriction of a centered finite ball to the rational diagonal is its integer dilation. -/
theorem theta_centeredBall_diagonal (g : ℝ → ℂ) (t : ℝ) {d : ℚ} (hd : d ≠ 0) :
    (∑' q : ℚ, g ((q:ℝ)*t) * (centeredBall d).indicator (1 : A → ℂ) (diag q)) =
      ∑' n : ℤ, g (((d:ℝ)*n)*t) := by
  classical
  let F (q : ℚ) := g ((q:ℝ)*t) * (centeredBall d).indicator (1 : A → ℂ) (diag q)
  have hzero : Function.support F ⊆ Set.range (fun n : ℤ => d*n) := by
    intro q hq
    by_contra h
    have hnu : diag q ∉ centeredBall d := fun hx => by
      obtain ⟨n,hn⟩ := (rational_mem_centered_iff q d hd).mp hx
      exact h ⟨n,hn.symm⟩
    exact hq (by simp [F,hnu])
  have he (n : ℤ) : F (d*n) = g (((d:ℝ)*n)*t) := by
    have hin : diag (d*n) ∈ centeredBall d := (rational_mem_centered_iff _ d hd).mpr ⟨n,rfl⟩
    simp only [F,Set.indicator_of_mem hin,Pi.one_apply,mul_one,Rat.cast_mul,Rat.cast_intCast]
  exact ((lattice_injective hd).tsum_eq hzero).symm.trans (tsum_congr he)

/-- Absolute convergence on all unit orbits and commutation of finite-unit averaging with
the rational theta sum. A finite measure suffices.  The finite test may be continuous. -/
private theorem theta_unit_average_aux [MeasurableSpace K] [OpensMeasurableSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (g : 𝓢(ℝ,ℂ)) (h : A → ℂ)
    (hc : Continuous h) (hcs : HasCompactSupport h) {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun u : K => ∑' q : ℚ, g ((q:ℝ)*t) * h ((u.val:A)*diag q)) μ ∧
    (∀ u : K, Summable (fun q : ℚ => ‖g ((q:ℝ)*t) * h ((u.val:A)*diag q)‖)) ∧
    Summable (fun q : ℚ => ∫ u : K, ‖g ((q:ℝ)*t) * h ((u.val:A)*diag q)‖ ∂μ) ∧
    (∫ u : K, (∑' q : ℚ, g ((q:ℝ)*t) * h ((u.val:A)*diag q)) ∂μ) =
      ∑' q : ℚ, g ((q:ℝ)*t) * (∫ u : K, h ((u.val:A)*diag q) ∂μ) := by
  obtain ⟨d, hd, hzero⟩ := common_unit_lattice hcs
  obtain ⟨C,hC⟩ := hcs.exists_bound_of_continuous hc
  let ι (n : ℤ) : ℚ := d*n
  have hinj : Function.Injective ι := by
    intro n m he
    exact_mod_cast mul_left_cancel₀ hd he
  let F (q : ℚ) (u : K) := g ((q:ℝ)*t) * h ((u.val:A)*diag q)
  have hz {q : ℚ} (hq : q ∉ Set.range ι) (u : K) : F q u = 0 := by
    simp [F,hzero u q hq]
  have hscalar : (d:ℝ)*t ≠ 0 := mul_ne_zero (by exact_mod_cast hd) ht
  have hS : Summable (fun n : ℤ => ‖g (((ι n:ℚ):ℝ)*t)‖ * C) := by
    convert! (schwartz_lattice_summable g hscalar).mul_right C using 2 with n
    dsimp [ι]
    push_cast
    ring_nf
  have hpoint (q : ℚ) (u : K) : ‖F q u‖ ≤ ‖g ((q:ℝ)*t)‖ * C := by
    simp only [F,norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hcont (q : ℚ) : Continuous (F q) := by
    have hu : Continuous (fun u : K => (u.val:A)) := Units.continuous_val.comp continuous_subtype_val
    exact continuous_const.mul (hc.comp (hu.mul continuous_const))
  have hint (q : ℚ) : Integrable (F q) μ :=
    (integrable_const (‖g ((q:ℝ)*t)‖ * C)).mono' (hcont q).aestronglyMeasurable (Eventually.of_forall (hpoint q))
  have habs : ∀ u : K, Summable (fun q : ℚ => ‖F q u‖) := by
    intro u
    apply (hinj.summable_iff (fun q hq => by simp [hz hq u])).mp
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hpoint (ι n) u) hS
  have hiabs : Summable (fun q : ℚ => ∫ u : K, ‖F q u‖ ∂μ) := by
    apply (hinj.summable_iff (fun q hq => by simp [hz hq])).mp
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) _ (hS.mul_right (μ.real univ))
    intro n
    calc
      (∫ u : K, ‖F (ι n) u‖ ∂μ) ≤ ∫ _ : K, ‖g (((ι n:ℚ):ℝ)*t)‖ * C ∂μ :=
        integral_mono (hint _).norm (integrable_const _) (hpoint _)
      _ = _ := by simp [mul_comm]
  have htotal : Integrable (fun u : K => ∑' q : ℚ, F q u) μ := by
    apply (integrable_const (∑' n : ℤ, ‖g (((ι n:ℚ):ℝ)*t)‖ * C)).mono'
    · exact (Measurable.tsum (fun q => (hcont q).measurable)).aestronglyMeasurable
    · apply Eventually.of_forall
      intro u
      apply (norm_tsum_le_tsum_norm (habs u)).trans
      have hsupp : Function.support (fun q => ‖F q u‖) ⊆ Set.range ι := fun q hq => by
        by_contra hn
        exact hq (by simp [hz hn u])
      rw [← hinj.tsum_eq hsupp]
      exact Summable.tsum_le_tsum (fun n => hpoint (ι n) u) ((habs u).comp_injective hinj) hS
  refine ⟨htotal,habs,hiabs,?_⟩
  exact (integral_tsum_of_summable_integral_norm hint hiabs).symm.trans
    (tsum_congr (fun q => integral_const_mul ..))

theorem theta_unit_average_interchange [MeasurableSpace K] [OpensMeasurableSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (g : 𝓢(ℝ,ℂ)) (h : A → ℂ)
    (hc : Continuous h) (hcs : HasCompactSupport h) {t : ℝ} (ht : t ≠ 0) :
    (∀ u : K, Summable (fun q : ℚ => ‖g ((q:ℝ)*t) * h ((u.val:A)*diag q)‖)) ∧
    Summable (fun q : ℚ => ∫ u : K, ‖g ((q:ℝ)*t) * h ((u.val:A)*diag q)‖ ∂μ) ∧
    (∫ u : K, (∑' q : ℚ, g ((q:ℝ)*t) * h ((u.val:A)*diag q)) ∂μ) =
      ∑' q : ℚ, g ((q:ℝ)*t) * (∫ u : K, h ((u.val:A)*diag q) ∂μ) := (theta_unit_average_aux μ g h hc hcs ht).2

theorem integrable_theta_unit_orbit [MeasurableSpace K] [OpensMeasurableSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (g : 𝓢(ℝ,ℂ)) (h : A → ℂ)
    (hc : Continuous h) (hcs : HasCompactSupport h) {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun u : K => ∑' q : ℚ, g ((q:ℝ)*t) * h ((u.val:A)*diag q)) μ :=
  (theta_unit_average_aux μ g h hc hcs ht).1

end
end MasulloRH.RationalFinite
end

section
open NumberField MeasureTheory IsDedekindDomain Set Filter
open MasulloRH.RationalFinite
open scoped Classical SchwartzMap Topology
namespace MasulloRH.RationalArch
noncomputable section

/-- A rational diagonal point, dilated at the archimedean place and rotated by a finite unit. -/
def orbitPoint (t : ℝ) (u : K) (q : ℚ) : FullA :=
  (archSection t * algebraMap ℚ (InfiniteAdeleRing ℚ) q, (u.val : A) * diag q)

def bilateral (g : 𝓢(ℝ,ℂ)) (t : ℝ) : ℂ := ∑' n : ℤ, g ((n:ℝ)*t)

def spherical [MeasurableSpace K] (κ : Measure K) (F : FullA → ℂ) (t : ℝ) : ℂ :=
  ∫ u : K, ∑' q : ℚ, F (orbitPoint t u q) ∂κ

private theorem tensor_orbit (G : 𝓢(M,ℂ)) (h : A → ℂ) (t : ℝ) (u : K) (q : ℚ) :
    (fun x : FullA => G (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * h x.2)
      (orbitPoint t u q) = toRealTest G ((q:ℝ)*t) * h ((u.val:A)*diag q) := by
  dsimp only [orbitPoint]
  rw [realTest_at_rational_scale,mul_comm t]

def OrbitRegular [MeasurableSpace K] (κ : Measure K) (F : FullA → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t →
    (∀ u : K, Summable (fun q : ℚ => ‖F (orbitPoint t u q)‖)) ∧
    Integrable (fun u : K => ∑' q : ℚ, F (orbitPoint t u q)) κ

private theorem orbital_add {F H : FullA → ℂ} {t : ℝ} {u : K}
    (hF : Summable (fun q : ℚ => ‖F (orbitPoint t u q)‖))
    (hH : Summable (fun q : ℚ => ‖H (orbitPoint t u q)‖)) :
    (∑' q : ℚ, (F+H) (orbitPoint t u q)) =
      (∑' q : ℚ, F (orbitPoint t u q)) + ∑' q : ℚ, H (orbitPoint t u q) :=
  hF.of_norm.tsum_add hH.of_norm

private theorem OrbitRegular.add [MeasurableSpace K] {κ : Measure K} {F H : FullA → ℂ}
    (hf : OrbitRegular κ F) (hh : OrbitRegular κ H) : OrbitRegular κ (F+H) := by
  intro t ht
  have h1 := hf t ht
  have h2 := hh t ht
  constructor
  · intro u
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le ..)
      ((h1.1 u).add (h2.1 u))
  · have he : (fun u : K => ∑' q : ℚ, (F+H) (orbitPoint t u q)) =
        fun u : K => (∑' q : ℚ, F (orbitPoint t u q)) + ∑' q : ℚ, H (orbitPoint t u q) :=
      funext fun u => orbital_add (h1.1 u) (h2.1 u)
    rw [he]
    exact h1.2.add h2.2

private theorem OrbitRegular.smul [MeasurableSpace K] {κ : Measure K} {F : FullA → ℂ}
    (c : ℂ) (hf : OrbitRegular κ F) : OrbitRegular κ (c • F) := by
  intro t ht
  have h1 := hf t ht
  constructor
  · intro u
    simpa only [Pi.smul_apply,smul_eq_mul,norm_mul] using (h1.1 u).mul_left ‖c‖
  · simpa only [Pi.smul_apply,smul_eq_mul,tsum_mul_left] using h1.2.const_mul c

private theorem spherical_add [MeasurableSpace K] {κ : Measure K} {F H : FullA → ℂ}
    (hf : OrbitRegular κ F) (hh : OrbitRegular κ H) {t : ℝ} (ht : 0 < t) :
    spherical κ (F+H) t = spherical κ F t + spherical κ H t := by
  obtain ⟨h1,h2⟩ := hf t ht
  obtain ⟨h3,h4⟩ := hh t ht
  simp only [spherical]
  calc
    _ = ∫ u : K, ((∑' q : ℚ, F (orbitPoint t u q)) + ∑' q : ℚ, H (orbitPoint t u q)) ∂κ :=
      integral_congr_ae (Eventually.of_forall fun u => orbital_add (h1 u) (h3 u))
    _ = _ := integral_add h2 h4

private theorem spherical_smul [MeasurableSpace K] (κ : Measure K) (c : ℂ) (F : FullA → ℂ) (t : ℝ) :
    spherical κ (c • F) t = c * spherical κ F t := by
  simp only [spherical,Pi.smul_apply,smul_eq_mul,tsum_mul_left,integral_const_mul]

private theorem bilateral_add (f g : 𝓢(ℝ,ℂ)) {t : ℝ} (ht : 0 < t) :
    bilateral (f+g) t = bilateral f t + bilateral g t := by
  have hs (G : 𝓢(ℝ,ℂ)) : Summable (fun n : ℤ => G ((n:ℝ)*t)) := by
    simpa only [mul_comm t] using (schwartz_lattice_summable G ht.ne').of_norm
  exact (hs f).tsum_add (hs g)

private theorem bilateral_smul (c : ℂ) (g : 𝓢(ℝ,ℂ)) (t : ℝ) :
    bilateral (c • g) t = c * bilateral g t := by
  simp only [bilateral,smul_apply,smul_eq_mul,tsum_mul_left]

variable [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [IsProbabilityMeasure κ]
  [MeasurableSpace FullA] [BorelSpace FullA] (μ : Measure FullA) [μ.IsAddHaarMeasure]
  [MeasurableSpace A] [BorelSpace A] (ν : Measure A) [ν.IsAddHaarMeasure]

def Matches (F : FullA → ℂ) (g : 𝓢(ℝ,ℂ)) : Prop :=
  g 0 = F 0 ∧
  (∫ x : FullA, F x ∂μ) = (haarFactor μ ν : ℂ) * (ν.real O : ℂ) * (∫ t : ℝ, g t) ∧
  ∀ t : ℝ, 0<t → spherical κ F t = bilateral g t

theorem exists_matching_schwartz
    (hcollapse : ∀ (G : 𝓢(ℝ,ℂ)) (h : A → ℂ), IsLocallyConstant h → HasCompactSupport h →
      ∃ g : 𝓢(ℝ,ℂ), g 0 = G 0*h 0 ∧
      (∫x:ℝ,G x)*(∫x:A,h x ∂ν) = (ν.real O:ℂ)*(∫x:ℝ,g x) ∧
      ∀ t : ℝ, 0<t → (∑' q:ℚ,G ((q:ℝ)*t)*(∫u:K,h ((u.val:A)*diag q) ∂κ)) = ∑' n:ℤ,g ((n:ℝ)*t))
    {F : FullA → ℂ} (hF : F ∈ AdelicFourier.schwartzBruhat ℚ) :
    OrbitRegular κ F ∧ ∃ g : 𝓢(ℝ,ℂ), Matches κ μ ν F g := by
  induction hF using AdelicFourier.schwartzBruhat_induction with
  | tensor F hF =>
    obtain ⟨G,h,hlc,hcs,rfl⟩ := hF
    obtain ⟨g,hg0,hgI,hg⟩ := hcollapse (toRealTest G) h hlc hcs
    constructor
    · intro t ht
      simp only [tensor_orbit]
      exact ⟨(theta_unit_average_interchange κ (toRealTest G) h hlc.continuous hcs ht.ne').1,
        integrable_theta_unit_orbit κ (toRealTest G) h hlc.continuous hcs ht.ne'⟩
    · refine ⟨g,?_,?_,?_⟩
      · change g 0 = G (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ 0) * h 0
        simpa only [toRealTest_apply,map_zero] using hg0
      · rw [integral_pureTensor μ ν G h hlc,hgI,mul_assoc]
      · intro t ht
        simp only [spherical,tensor_orbit,bilateral]
        exact (theta_unit_average_interchange κ (toRealTest G) h hlc.continuous hcs ht.ne').2.2.trans (hg t ht)
  | zero =>
    constructor
    · intro t ht
      simp
    · refine ⟨0,?_⟩
      simp [Matches,spherical,bilateral]
  | add f h hf hh hf' hh' =>
    obtain ⟨rf,g,eg⟩ := hf'
    obtain ⟨rh,k,ek⟩ := hh'
    refine ⟨rf.add rh,g+k,?_,?_,?_⟩
    · simp only [Pi.add_apply,add_apply,eg.1,ek.1]
    · change (∫ x : FullA, f x + h x ∂μ) = _ * _ * ∫ t : ℝ, g t + k t
      rw [integral_add (integrable_schwartzBruhat μ ν hf) (integrable_schwartzBruhat μ ν hh),
        integral_add g.integrable k.integrable,eg.2.1,ek.2.1,mul_add]
    · intro t ht
      rw [spherical_add rf rh ht,bilateral_add _ _ ht,eg.2.2 t ht,ek.2.2 t ht]
  | smul c f hf hf' =>
    obtain ⟨rf,g,eg⟩ := hf'
    refine ⟨rf.smul c,c • g,?_,?_,?_⟩
    · simp only [smul_apply,Pi.smul_apply,eg.1]
    · change (∫ x : FullA, c*f x ∂μ) = _ * _ * ∫ t : ℝ, c*g t
      rw [integral_const_mul,integral_const_mul,eg.2.1]
      ring
    · intro t ht
      rw [spherical_smul,bilateral_smul,eg.2.2 t ht]

end
end MasulloRH.RationalArch
end

section
open NumberField MeasureTheory IsDedekindDomain Set Filter
open NumberField.AdelicBox MasulloRH.RationalFinite
open scoped Classical SchwartzMap Topology
namespace MasulloRH.RationalArch
noncomputable section

def integralIndicator : A → ℂ := O.indicator 1

private theorem indicator_lc : IsLocallyConstant integralIndicator := by
  have hopen : IsClopen O := ⟨(isCompact_integralFiniteAdeles ℚ).isClosed,
    isOpen_integralFiniteAdeles ℚ⟩
  exact (LocallyConstant.charFn ℂ hopen).isLocallyConstant

private theorem indicator_cs : HasCompactSupport integralIndicator := by
  apply (isCompact_integralFiniteAdeles ℚ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isCompact_integralFiniteAdeles ℚ).isClosed
  exact Set.support_indicator_subset ..

private theorem indicator_zero : integralIndicator 0 = 1 := by
  have hz : (0:A) ∈ O := fun v => zero_mem (v.adicCompletionIntegers ℚ)
  simp [integralIndicator,Set.indicator_of_mem hz]

private theorem indicator_unit (u : K) (a : A) :
    integralIndicator ((u.val:A)*a) = integralIndicator a := by
  have hm (v : K) {b : A} (hb : b ∈ O) : (v.val:A) * b ∈ O :=
    fun w => mul_mem (v.property.1 w) (hb w)
  by_cases ha : a ∈ O
  · simp only [integralIndicator,Set.indicator_of_mem ha,Set.indicator_of_mem (hm u ha),Pi.one_apply]
  · have hn : (u.val:A)*a ∉ O := by
      intro h
      have hh := hm u⁻¹ h
      change (↑u.val⁻¹:A) * ((u.val:A)*a) ∈ O at hh
      exact ha (by simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh)
    simp only [integralIndicator,Set.indicator_of_notMem ha,Set.indicator_of_notMem hn]

/-- Lift a one-dimensional Schwartz function by the unramified finite test. -/
def liftIntegral (g : 𝓢(ℝ,ℂ)) (x : FullA) : ℂ :=
  ofRealTest g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * integralIndicator x.2

theorem liftIntegral_schwartzBruhat (g : 𝓢(ℝ,ℂ)) : liftIntegral g ∈ AdelicFourier.schwartzBruhat ℚ :=
  AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet
    (AdelicFourier.tensor_mem_pureTensorSet _ _ indicator_lc indicator_cs)

private theorem orbit_sum_lift (g : 𝓢(ℝ,ℂ)) (t : ℝ) (u : K) :
    (∑' q : ℚ, liftIntegral g (orbitPoint t u q)) = bilateral g t := by
  have he (q : ℚ) : liftIntegral g (orbitPoint t u q) =
       g ((q:ℝ)*t) * integralIndicator (diag q) := by
    simp only [liftIntegral,orbitPoint,realTest_at_rational_scale,toRealTest_ofRealTest,
      indicator_unit,mul_comm t]
  simp_rw [he]
  have hball : centeredBall 1 = O := by simp [centeredBall]
  simpa only [hball,Rat.cast_one,one_mul,integralIndicator,bilateral] using
    theta_centeredBall_diagonal g t (one_ne_zero : (1:ℚ) ≠ 0)

theorem liftIntegral_regular [MeasurableSpace K] [BorelSpace K] (κ : Measure K)
    [IsFiniteMeasure κ] (g : 𝓢(ℝ,ℂ)) : OrbitRegular κ (liftIntegral g) := by
  intro t ht
  constructor
  · have hh := (theta_unit_average_interchange κ g integralIndicator indicator_lc.continuous indicator_cs ht.ne').1
    intro u
    simpa only [liftIntegral,orbitPoint,realTest_at_rational_scale,toRealTest_ofRealTest,mul_comm t] using hh u
  · simp_rw [orbit_sum_lift]
    exact integrable_const _

variable [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [IsProbabilityMeasure κ]
  [MeasurableSpace FullA] [BorelSpace FullA] (μ : Measure FullA) [μ.IsAddHaarMeasure]
  [MeasurableSpace A] [BorelSpace A] (ν : Measure A) [ν.IsAddHaarMeasure]

omit [BorelSpace K] in
theorem liftIntegral_matches (g : 𝓢(ℝ,ℂ)) : Matches κ μ ν (liftIntegral g) g := by
  refine ⟨?_,?_,?_⟩
  · change g 0 = ofRealTest g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ 0) * integralIndicator 0
    simp only [map_zero,ofRealTest_apply,indicator_zero,mul_one]
  · have hi : (∫ a : A, integralIndicator a ∂ν) = (ν.real O : ℂ) := by
      change (∫ a : A, O.indicator (fun _ => (1:ℂ)) a ∂ν) = _
      rw [integral_indicator_const _ (isOpen_integralFiniteAdeles ℚ).measurableSet,Complex.real_smul,mul_one]
    change (∫ x : FullA, ofRealTest g _ * integralIndicator x.2 ∂μ) = _
    rw [integral_pureTensor μ ν (ofRealTest g) integralIndicator indicator_lc,toRealTest_ofRealTest,hi]
    ring
  · intro t ht
    simp [spherical,orbit_sum_lift]

omit [MeasurableSpace K] [BorelSpace K] [MeasurableSpace FullA] [BorelSpace FullA] [BorelSpace A] in
private theorem measureReal_O_pos : 0 < ν.real O := by
  have hO : O.Nonempty := ⟨0,fun v => zero_mem (v.adicCompletionIntegers ℚ)⟩
  exact ENNReal.toReal_pos ((isOpen_integralFiniteAdeles ℚ).measure_pos ν hO).ne'
    (isCompact_integralFiniteAdeles ℚ).measure_lt_top.ne

omit [IsProbabilityMeasure κ] [BorelSpace K] in
theorem Matches.admissible_iff {F : FullA → ℂ} {g : 𝓢(ℝ,ℂ)} (h : Matches κ μ ν F g) :
    (F 0 = 0 ∧ (∫ x : FullA, F x ∂μ) = 0) ↔
      (g 0 = 0 ∧ (∫ t : ℝ, g t) = 0) := by
  have hc : (haarFactor μ ν : ℂ) ≠ 0 := by exact_mod_cast (haarFactor_pos μ ν).ne'
  have ho : (ν.real O : ℂ) ≠ 0 := by exact_mod_cast (measureReal_O_pos ν).ne'
  rw [←h.1,h.2.1]
  simp [hc,ho]

omit [BorelSpace K] in
theorem admissible_image_eq_of_forward
    (hforward : ∀ F ∈ AdelicFourier.schwartzBruhat ℚ, ∃ g : 𝓢(ℝ,ℂ), Matches κ μ ν F g) :
    {Φ : {t : ℝ // 0 < t} → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ,
      F 0 = 0 ∧ (∫ x : FullA, F x ∂μ) = 0 ∧ ∀ t, Φ t = spherical κ F t.1} =
    {Φ : {t : ℝ // 0 < t} → ℂ | ∃ g : 𝓢(ℝ,ℂ),
      g 0 = 0 ∧ (∫ t : ℝ, g t) = 0 ∧ ∀ t, Φ t = bilateral g t.1} := by
  ext Φ
  constructor
  · rintro ⟨F,hF,h0,hI,hΦ⟩
    obtain ⟨g,h⟩ := hforward F hF
    obtain ⟨h0',hI'⟩ := (h.admissible_iff κ μ ν).mp ⟨h0,hI⟩
    exact ⟨g,h0',hI',fun t => (hΦ t).trans (h.2.2 t t.2)⟩
  · rintro ⟨g,h0,hI,hΦ⟩
    have h := liftIntegral_matches κ μ ν g
    obtain ⟨h0',hI'⟩ := (h.admissible_iff κ μ ν).mpr ⟨h0,hI⟩
    exact ⟨liftIntegral g,liftIntegral_schwartzBruhat g,h0',hI',fun t => (hΦ t).trans (h.2.2 t t.2).symm⟩

end
end MasulloRH.RationalArch
end

section
open MeasureTheory NumberField NumberField.AdelicBox Set Filter
open scoped Topology ENNReal
namespace MasulloRH.RationalFinite
noncomputable section

def scaleUnit (e : Aˣ) : A ≃ₜ+ A where
  toFun x := (e:A)*x
  invFun x := (e⁻¹:Aˣ)*x
  left_inv x := by simp [←mul_assoc]
  right_inv x := by simp [←mul_assoc]
  map_add' := mul_add _
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def ratUnit (q : ℚ) (hq : q ≠ 0) : Aˣ := Units.map diag.toMonoidHom (Units.mk0 q hq)

theorem ball_open (q : ℚ) (hq : q ≠ 0) : IsOpen (centeredBall q) :=
  (scaleUnit (ratUnit q hq)).toHomeomorph.isOpenMap O (isOpen_integralFiniteAdeles ℚ)

theorem ball_compact (q : ℚ) : IsCompact (centeredBall q) :=
  (isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id)

theorem ball_one : centeredBall 1 = O := by simp [centeredBall]

theorem ball_mul (r q : ℚ) : (fun x:A => diag r*x) '' centeredBall q = centeredBall (r*q) := by
  rw [centeredBall,centeredBall,Set.image_image,map_mul]
  simp only [mul_assoc]

variable [MeasurableSpace A] [BorelSpace A] (ν : Measure A) [ν.IsAddHaarMeasure]

theorem nat_ball_mass (a : ℕ) (ha : a ≠ 0) :
    (a:ℝ≥0∞) * ν (centeredBall a) = ν O := by
  have hd : (a : 𝓞 ℚ) ≠ 0 := by exact_mod_cast ha
  have h := NumberField.AdelicBox.absNorm_mul_measure_image_integralFiniteAdeles ℚ ν
    (a : 𝓞 ℚ) hd 0
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank,Module.finrank_self,pow_one] at h
  simpa [centeredBall,diag] using h

theorem positive_ball_mass (q : ℚ) (hq : 0 < q) :
    (q:ℝ)* (ν.real (centeredBall q)) = ν.real O := by
  let a := q.num.natAbs
  let b := q.den
  have hna : 0 < q.num := Rat.num_pos.mpr hq
  have ha : a ≠ 0 := Int.natAbs_ne_zero.mpr hna.ne'
  have hb : b ≠ 0 := q.den_nz
  have hqb : q*(b:ℚ) = a := by
    change q*(q.den:ℚ) = (q.num.natAbs:ℚ)
    have ht : (q.num.natAbs:ℤ) = q.num := Int.natAbs_of_nonneg hna.le
    have htq := congrArg (fun z : ℤ => (z:ℚ)) ht
    simp only [Int.cast_natCast] at htq
    rw [htq]
    exact ((div_eq_iff (by exact_mod_cast q.den_nz : (q.den:ℚ) ≠ 0)).mp (Rat.num_div_den q)).symm
  let e := scaleUnit (ratUnit q hq.ne')
  let μ := ν.map e.symm
  let : μ.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map ν
  have hm {S : Set A} (hs : MeasurableSet S) : μ S = ν (e '' S) := by
    have hm : Measurable (fun x => e.symm x) := e.symm.continuous.measurable
    calc
      μ S = ν (e.symm ⁻¹' S) := Measure.map_apply hm hs
      _ = ν (e '' S) := by
        congr 1
        ext x
        constructor
        · intro hx; exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
        · rintro ⟨z,hz,rfl⟩; simpa using hz
  have h := nat_ball_mass μ b hb
  have he : e '' centeredBall b = centeredBall a := (ball_mul q b).trans (congrArg centeredBall hqb)
  rw [hm (ball_open b (by exact_mod_cast hb)).measurableSet,he,hm (isOpen_integralFiniteAdeles ℚ).measurableSet] at h
  change (b:ℝ≥0∞)*ν (centeredBall a) = ν (centeredBall q) at h
  have h' := congrArg ENNReal.toReal h
  have hA := congrArg ENNReal.toReal (nat_ball_mass ν a ha)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast] at h' hA
  change (q:ℝ)*(ν (centeredBall q)).toReal = (ν O).toReal
  have hh : (q:ℝ) * (b:ℝ) = (a:ℝ) := by exact_mod_cast hqb
  rw [←h',←mul_assoc,hh,hA]

end
end MasulloRH.RationalFinite
end

section
open NumberField NumberField.AdelicBox MeasureTheory Set Filter
open scoped Topology
namespace MasulloRH.RationalFinite
noncomputable section

private theorem finiteAdele_compact_cover : (⋃ q : ℚ, centeredBall q) = univ := by
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨s,hs,hx⟩ := exists_mul_mem_integralFiniteAdeles (𝓞 ℚ) ℚ x
  have hn : (s:ℚ) ≠ 0 := by exact_mod_cast hs
  refine ⟨(s:ℚ)⁻¹,diag (s:ℚ)*x,hx,?_⟩
  change diag (s:ℚ)⁻¹*(diag (s:ℚ)*x) = x
  rw [← mul_assoc,← map_mul,inv_mul_cancel₀ hn,map_one,one_mul]

/-- Additive Haar measures on the rational finite adeles agree if they agree on integral
finite adeles. This uses the countable compact cover by rational dilates. -/
theorem addHaar_eq_of_integralFiniteAdeles [MeasurableSpace A] [BorelSpace A]
    (η ν : Measure A) [η.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (hO : η O = ν O) : η = ν := by
  have hc : IsCompact O := isCompact_integralFiniteAdeles ℚ
  have hopen : IsOpen O := isOpen_integralFiniteAdeles ℚ
  have hpos : ν O ≠ 0 := (hopen.measure_pos ν ⟨0,fun v => zero_mem _⟩).ne'
  have hscale := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure_of_measurableSet η ν
    hopen.measurableSet hc.closure
  have h1 : η.addHaarScalarFactor ν = 1 := by
    have hh : (η.addHaarScalarFactor ν : ENNReal) * ν O = (1:ENNReal) * ν O := by
      rw [one_mul, ← hO]
      simpa only [ENNReal.smul_def,smul_eq_mul,hO] using hscale.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hc.measure_lt_top.ne).mp hh
  apply Measure.ext_of_iUnion_eq_univ finiteAdele_compact_cover
  intro q
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs,Measure.restrict_apply hs]
  have hq : IsCompact (centeredBall q) := hc.image ((continuous_const (y:=diag q)).mul continuous_id)
  have hcl : IsCompact (closure (s ∩ centeredBall q)) := hq.of_isClosed_subset isClosed_closure
    (closure_minimal inter_subset_right hq.isClosed)
  simpa only [h1,one_smul] using Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure_of_measurableSet
    η ν (hs.inter hq.measurableSet) hcl

/-- Multiplication by a finite unit preserves every additive Haar measure. -/
theorem measurePreserving_finiteUnit [MeasurableSpace A] [BorelSpace A]
    (ν : Measure A) [ν.IsAddHaarMeasure] (u : K) :
    MeasurePreserving (fun x : A => (u.val:A)*x) ν ν := by
  let e : A ≃ₜ+ A := (ContinuousLinearEquiv.smulLeft (R₁ := A) (M₁ := A) u.val).toContinuousAddEquiv
  have hpre : e ⁻¹' O = O := by
    ext x
    change (u.val:A)*x ∈ O ↔ x ∈ O
    constructor
    · intro hx v
      have hm : ((↑u.val⁻¹:A) * ((u.val:A)*x)) v ∈ v.adicCompletionIntegers ℚ :=
        mul_mem (u.prop.2 v) (hx v)
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using hm
    · intro hx v
      exact mul_mem (u.prop.1 v) (hx v)
  change MeasurePreserving e ν ν
  refine ⟨e.continuous.measurable,addHaar_eq_of_integralFiniteAdeles _ _ ?_⟩
  calc
    _ = ν (e ⁻¹' O) := Measure.map_apply (f := (e : A → A)) e.continuous.measurable (isOpen_integralFiniteAdeles ℚ).measurableSet
    _ = _ := congrArg ν hpre

private theorem unitMoment_compactUnitIdeles : CompactSpace K := by
  let S : Set (A×A) := (O ×ˢ O) ∩ {z | z.1*z.2=1}
  have hc : IsCompact S := (isCompact_integralFiniteAdeles ℚ).prod (isCompact_integralFiniteAdeles ℚ) |>.inter_right
    (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hc
  let f (z : S) : Aˣ := ⟨z.val.1,z.val.2,z.prop.2, (mul_comm _ _).trans z.prop.2⟩
  let F (z : S) : K := ⟨f z,z.prop.1⟩
  have h : Continuous f := Units.continuous_iff.mpr
    ⟨continuous_fst.comp continuous_subtype_val,continuous_snd.comp continuous_subtype_val⟩
  have hF : Continuous F := h.subtype_mk _
  have hsurj : Function.Surjective F := by
    intro u
    exact ⟨⟨((u.val:A),↑u.val⁻¹),u.prop,Units.mul_inv u.val⟩,Subtype.ext (Units.ext rfl)⟩
  exact hsurj.compactSpace hF

/-- Averaging the finite component over unit ideles preserves its total additive integral. -/
theorem integral_average_finiteUnit [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace K] [OpensMeasurableSpace K] (ν : Measure A) [ν.IsAddHaarMeasure]
    (μ : Measure K) [IsProbabilityMeasure μ] {h : A → ℂ}
    (hc : Continuous h) (hcs : HasCompactSupport h) :
    (∫ x : A, ∫ u : K, h ((u.val:A)*x) ∂μ ∂ν) = ∫ x : A, h x ∂ν := by
  let : CompactSpace K := unitMoment_compactUnitIdeles
  let F (x : A) (u : K) := h ((u.val:A)*x)
  have hv : Continuous (fun u : K => (u.val:A)) := Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous (Function.uncurry F) := hc.comp ((hv.comp continuous_snd).mul continuous_fst)
  let back (z : A × K) := ((↑z.2.val⁻¹:A)*z.1,z.2)
  have hb : Continuous back := ((hv.comp (continuous_inv.comp continuous_snd)).mul continuous_fst).prodMk continuous_snd
  have hcf : HasCompactSupport (Function.uncurry F) := by
    apply HasCompactSupport.of_support_subset_isCompact ((hcs.prod (isCompact_univ (X:=K))).image hb)
    intro z hz
    refine ⟨((z.2.val:A)*z.1,z.2),⟨subset_tsupport h hz,mem_univ _⟩,?_⟩
    change ((↑z.2.val⁻¹:A)*((z.2.val:A)*z.1),z.2) = z
    rw [← mul_assoc,Units.inv_mul,one_mul]
  have hfix (u : K) : (∫ x : A, F x u ∂ν) = ∫ x : A, h x ∂ν := by
    let e : A ≃ₜ+ A := (ContinuousLinearEquiv.smulLeft (R₁ := A) (M₁ := A) u.val).toContinuousAddEquiv
    have hp : MeasurePreserving e ν ν := measurePreserving_finiteUnit ν u
    exact hp.integral_comp e.toHomeomorph.measurableEmbedding h
  rw [integral_integral_swap_of_hasCompactSupport hf hcf]
  simp only [hfix,integral_const,probReal_univ,one_smul]

end
end MasulloRH.RationalFinite
end

section
open MeasureTheory NumberField Set
open scoped SchwartzMap Topology
namespace MasulloRH.RationalFinite
noncomputable section

private theorem arch_summable (G : 𝓢(ℝ,ℂ)) (t : ℝ) (ht : 0<t) :
    Summable (fun n : ℤ => G ((n:ℝ)*t)) := by
  simpa only [mul_comm t] using (schwartz_lattice_summable G ht.ne').of_norm

variable [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ]

include κ
private theorem radial_regular {f : A → ℂ} (hf : f ∈ radialSpan) :
    IsLocallyConstant f ∧ HasCompactSupport f :=
  let h := ((MasulloRH.finite_adele_radial_synthesis κ).1 f).2.mp hf
  ⟨h.1,h.2.1⟩

variable [MeasurableSpace A] [BorelSpace A] (ν : Measure A) [ν.IsAddHaarMeasure]

private theorem radial_integrable {f : A → ℂ} (hf : f ∈ radialSpan) : Integrable f ν :=
  (radial_regular κ hf).1.continuous.integrable_of_hasCompactSupport (radial_regular κ hf).2

omit [MeasurableSpace A] [BorelSpace A] in
private theorem radial_summable (G : 𝓢(ℝ,ℂ)) {f : A→ℂ} (hf : f ∈ radialSpan) (t : ℝ) (ht : 0<t) :
    Summable (fun q : ℚ => G ((q:ℝ)*t)*f (diag q)) := by
  obtain ⟨hlc,hcs⟩ := radial_regular κ hf
  have h := (theta_unit_average_interchange κ G f hlc.continuous hcs ht.ne').1 (1:K)
  simpa using h.of_norm

theorem collapse_radial (G : 𝓢(ℝ,ℂ)) {f : A → ℂ} (hf : f ∈ radialSpan) :
    ∃ g : 𝓢(ℝ,ℂ), g 0 = G 0*f 0 ∧
      ((∫ x : ℝ, G x) * ∫ x : A, f x ∂ν) = (ν.real O:ℂ) * ∫ x : ℝ, g x ∧
      ∀ t : ℝ, 0<t →
        (∑' q : ℚ, G ((q:ℝ)*t)*f (diag q)) = ∑' n : ℤ, g ((n:ℝ)*t) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d,hd,rfl⟩ := hf
    have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
    let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (d:ℝ) hdR.ne')
    let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e G
    have hg (x : ℝ) : g x = G ((d:ℝ)*x) := rfl
    have h0 : (0:A) ∈ centeredBall d :=
      ⟨0,fun v => zero_mem _,by simp⟩
    refine ⟨g,by simp [hg,h0],?_,?_⟩
    · rw [integral_indicator (ball_open d hd.ne').measurableSet]
      simp only [Pi.one_apply,setIntegral_const,Complex.real_smul,
        mul_one, hg,Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hdR)]
      have hm : ((d:ℝ):ℂ) * (ν.real (centeredBall d):ℂ) = (ν.real O:ℂ) := by
        exact_mod_cast positive_ball_mass ν d hd
      change _ = (ν.real O:ℂ)*_
      rw [←hm]
      push_cast
      field_simp [hdR.ne']
    · intro t _
      rw [theta_centeredBall_diagonal _ _ hd.ne']
      apply tsum_congr
      intro n
      rw [hg,mul_assoc]
  | zero =>
    exact ⟨0, by simp, by simp, by simp⟩
  | add f h hf hh ih jh =>
    obtain ⟨g,hg0,hgI,hgt⟩ := ih
    obtain ⟨k,hk0,hkI,hkt⟩ := jh
    refine ⟨g+k,by simp [hg0,hk0,mul_add],?_,?_⟩
    · rw [show (fun x => (f+h) x) = fun x => f x+h x from rfl,
          integral_add (radial_integrable κ ν hf) (radial_integrable κ ν hh)]
      simp only [add_apply,integral_add g.integrable k.integrable,mul_add,hgI,hkI]
    · intro t ht
      simp only [Pi.add_apply,mul_add,add_apply,
        (radial_summable κ G hf t ht).tsum_add (radial_summable κ G hh t ht),
        (arch_summable g t ht).tsum_add (arch_summable k t ht),hgt t ht,hkt t ht]
  | smul c f hf ih =>
    obtain ⟨g,hg0,hgI,hgt⟩ := ih
    refine ⟨c • g,by simp [hg0,mul_left_comm],?_,?_⟩
    · simp only [Pi.smul_apply,smul_apply,smul_eq_mul,integral_const_mul]
      linear_combination c*hgI
    · intro t ht
      simp only [Pi.smul_apply,smul_apply,smul_eq_mul,mul_left_comm (G _),
        tsum_mul_left, hgt t ht]

theorem collapse_averaged (G : 𝓢(ℝ,ℂ)) (h : A → ℂ)
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ g : 𝓢(ℝ,ℂ), g 0 = G 0*h 0 ∧
      (∫ x : ℝ, G x) * (∫ x : A, h x ∂ν) = (ν.real O:ℂ) * ∫ x : ℝ, g x ∧
      ∀ t : ℝ, 0<t →
        (∑' q : ℚ, G ((q:ℝ)*t)*(∫ u : K, h ((u.val:A)*diag q) ∂κ)) =
          ∑' n : ℤ, g ((n:ℝ)*t) := by
  let f (x : A) := ∫ u : K, h ((u.val:A)*x) ∂κ
  have hf : f ∈ radialSpan := ((MasulloRH.finite_adele_radial_synthesis κ).1 f).1.mpr
    ⟨h,hlc,hcs,fun _ => rfl⟩
  obtain ⟨g,hg0,hgI,hgt⟩ := collapse_radial κ ν G hf
  have hf0 : f 0 = h 0 := by simp [f]
  have hfI : (∫ x, f x ∂ν) = ∫ x, h x ∂ν := integral_average_finiteUnit ν κ hlc.continuous hcs
  exact ⟨g,hg0.trans (congrArg (G 0 * ·) hf0),hfI ▸ hgI,hgt⟩

end
end MasulloRH.RationalFinite
end

open NumberField IsDedekindDomain MeasureTheory MasulloRH.RationalFinite
open scoped Classical SchwartzMap

/-- The spherical rational adelic theta image and its real Schwartz realization,
including the matching of the zero value, the integral, and both admissibility conditions. -/
theorem solution [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)]
    (μ : Measure (AdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure]
    [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ] :
    let orbit (t : ℝ) (u : K) (q : ℚ) : AdeleRing (𝓞 ℚ) ℚ :=
      let dilation : AdeleRing (𝓞 ℚ) ℚ := ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
        (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) t), (u.val : A))
      dilation * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q
    let adelicTheta (F : AdeleRing (𝓞 ℚ) ℚ → ℂ) (t : ℝ) := ∫ u : K, ∑' q : ℚ, F (orbit t u q) ∂κ
    let realTheta (g : 𝓢(ℝ,ℂ)) (t : ℝ) := ∑' n : ℤ, g ((n:ℝ)*t)
    (∀ F ∈ AdelicFourier.schwartzBruhat ℚ,
      (∀ t : ℝ, 0<t → (∀ u : K, Summable (fun q : ℚ => ‖F (orbit t u q)‖)) ∧
        Integrable (fun u : K => ∑' q : ℚ, F (orbit t u q)) κ) ∧
      ∃ g : 𝓢(ℝ,ℂ), g 0 = F 0 ∧
        (∫ x, F x ∂μ) = (μ.real (AdelicBox.adelicBox ℚ) : ℂ) * (∫ x : ℝ, g x) ∧
        ∀ t : ℝ, 0<t → adelicTheta F t = realTheta g t) ∧
    (∀ g : 𝓢(ℝ,ℂ),
      let F (x : AdeleRing (𝓞 ℚ) ℚ) :=
        g ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1).1
          ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩) * O.indicator (1 : A → ℂ) x.2
      F ∈ AdelicFourier.schwartzBruhat ℚ ∧ g 0 = F 0 ∧
        (∫ x, F x ∂μ) = (μ.real (AdelicBox.adelicBox ℚ) : ℂ) * (∫ x : ℝ, g x) ∧
        ∀ t : ℝ, 0<t → adelicTheta F t = realTheta g t) ∧
    {Φ : {t : ℝ // 0<t} → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ,
      F 0 = 0 ∧ (∫ x, F x ∂μ) = 0 ∧ ∀ t, Φ t = adelicTheta F t.1} =
    {Φ : {t : ℝ // 0<t} → ℂ | ∃ g : 𝓢(ℝ,ℂ),
      g 0 = 0 ∧ (∫ x : ℝ, g x) = 0 ∧ ∀ t, Φ t = realTheta g t.1} := by
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let ν : Measure A := Measure.addHaar
  let : ν.IsAddHaarMeasure := Measure.isAddHaarMeasure_addHaarMeasure _
  have hO : 0 < ν.real O := ENNReal.toReal_pos
    ((AdelicBox.isOpen_integralFiniteAdeles ℚ).measure_pos ν
      ⟨0,fun v => zero_mem (v.adicCompletionIntegers ℚ)⟩).ne'
    (AdelicBox.isCompact_integralFiniteAdeles ℚ).measure_lt_top.ne
  have hfactor : (MasulloRH.RationalArch.haarFactor μ ν : ℂ) * (ν.real O : ℂ) =
      (μ.real (AdelicBox.adelicBox ℚ) : ℂ) := by
    exact_mod_cast div_mul_cancel₀ (μ.real (AdelicBox.adelicBox ℚ)) hO.ne'
  have harch (t : ℝ) : (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
      (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) t) = MasulloRH.RationalArch.archSection t := by
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).injective
    rw [RingEquiv.apply_symm_apply,MasulloRH.RationalArch.mixed_eq_archSection,
      MasulloRH.RationalArch.mixedCoord_symm_apply]
  dsimp only
  simp_rw [harch]
  have hfwd (F : MasulloRH.RationalArch.FullA → ℂ) (hF : F ∈ AdelicFourier.schwartzBruhat ℚ) :=
    MasulloRH.RationalArch.exists_matching_schwartz κ μ ν (collapse_averaged κ ν) hF
  refine ⟨?_,?_,?_⟩
  · intro F hF
    obtain ⟨hR,g,hg⟩ := hfwd F hF
    exact ⟨hR,g,hg.1,hfactor ▸ hg.2.1,hg.2.2⟩
  · intro g
    have hg := MasulloRH.RationalArch.liftIntegral_matches κ μ ν g
    exact ⟨MasulloRH.RationalArch.liftIntegral_schwartzBruhat g,hg.1,hfactor ▸ hg.2.1,hg.2.2⟩
  · exact MasulloRH.RationalArch.admissible_image_eq_of_forward κ μ ν (fun F hF => (hfwd F hF).2)
