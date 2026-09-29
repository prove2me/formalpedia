-- Prove2me | solution 1 for LanglandsTunnell.Converse.isHaarMeasure_and_isMulRightInvariant_archMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ddad59c7-bc93-5df8-a336-cd4c27e60a47

import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure

set_option autoImplicit false

open MeasureTheory Matrix Topology NumberField RSCarrier

noncomputable section

namespace ArchMeasureHaar

private scoped instance : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)

private scoped instance : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩

private abbrev entries (g : GL (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j

private theorem continuousOn_inv_isUnit :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_
    (Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin 2) (Fin 2) ℝ))).continuousOn
  exact (Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

private theorem isEmbedding_val : IsEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  Units.isEmbedding_val_mk' continuousOn_inv_isUnit fun u => (Matrix.coe_units_inv u).symm

private theorem isEmbedding_entries : IsEmbedding entries :=
  isEmbedding_val

private theorem isOpen_range_entries : IsOpen (Set.range entries) := by
  have h : Set.range entries =
      (fun A : Fin 2 → Fin 2 → ℝ => (Matrix.of A).det) ⁻¹' {x | x ≠ 0} := by
    ext A
    constructor
    · rintro ⟨u, rfl⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
    · intro hA
      exact (Matrix.isUnit_iff_isUnit_det (Matrix.of A)).mpr (isUnit_iff_ne_zero.mpr hA)
  rw [h]
  exact isOpen_ne.preimage (Continuous.matrix_det continuous_id)

private theorem isOpenEmbedding_entries : IsOpenEmbedding entries :=
  ⟨isEmbedding_entries, isOpen_range_entries⟩

private theorem measurableEmbedding_entries : MeasurableEmbedding entries :=
  isOpenEmbedding_entries.measurableEmbedding

private theorem locallyCompactSpace_gl : LocallyCompactSpace (GL (Fin 2) ℝ) :=
  isOpenEmbedding_entries.locallyCompactSpace

private theorem secondCountableTopology_gl : SecondCountableTopology (GL (Fin 2) ℝ) :=
  isEmbedding_entries.secondCountableTopology

private theorem measurable_density : Measurable fun g : GL (Fin 2) ℝ =>
    ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹ := by
  have hdet : Continuous fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ) := by
    show Continuous fun g : GL (Fin 2) ℝ => Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ)
    exact (Continuous.matrix_det continuous_id).comp Units.continuous_val
  exact ENNReal.measurable_ofReal.comp ((hdet.abs.pow 2).measurable.inv)

private theorem archMeasure_univ_pos : 0 < archMeasure Set.univ := by
  show 0 < (Measure.comap entries volume).withDensity _ Set.univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_pos_iff_support measurable_density]
  have hsupp : Function.support (fun g : GL (Fin 2) ℝ =>
      ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have h0 : (Matrix.GeneralLinearGroup.det g : ℝ) ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
    positivity
  rw [hsupp, measurableEmbedding_entries.comap_apply, Set.image_univ]
  exact isOpen_range_entries.measure_pos volume ⟨entries 1, Set.mem_range_self 1⟩

private theorem continuous_realDensity :
    Continuous fun g : GL (Fin 2) ℝ => (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹ := by
  have hdet : Continuous fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ) := by
    show Continuous fun g : GL (Fin 2) ℝ => Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ)
    exact (Continuous.matrix_det continuous_id).comp Units.continuous_val
  refine (hdet.abs.pow 2).inv₀ fun g => ?_
  have h0 : (Matrix.GeneralLinearGroup.det g : ℝ) ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  exact pow_ne_zero _ (abs_ne_zero.mpr h0)

private theorem isLocallyFiniteMeasure_archMeasure : IsLocallyFiniteMeasure archMeasure := by
  haveI := locallyCompactSpace_gl
  refine ⟨fun g => ?_⟩
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds g
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn continuous_realDensity.continuousOn
  refine ⟨K, hKn, ?_⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  show (Measure.comap entries volume).withDensity _ K < ⊤
  rw [withDensity_apply _ hKm]
  calc ∫⁻ x in K, ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det x : ℝ)| ^ 2)⁻¹
          ∂(Measure.comap entries volume)
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(Measure.comap entries volume) := by
        refine setLIntegral_mono' hKm fun x hx => ENNReal.ofReal_le_ofReal ?_
        exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM x hx))
    _ = ENNReal.ofReal M * Measure.comap entries volume K := by rw [setLIntegral_const, mul_comm]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [measurableEmbedding_entries.comap_apply]
        exact (hKc.image isEmbedding_entries.continuous).measure_lt_top

private theorem regular_archMeasure : archMeasure.Regular := by
  haveI := locallyCompactSpace_gl
  haveI := secondCountableTopology_gl
  haveI : TopologicalSpace.PseudoMetrizableSpace (GL (Fin 2) ℝ) :=
    isEmbedding_entries.pseudoMetrizableSpace
  haveI := isLocallyFiniteMeasure_archMeasure
  infer_instance

private def rowMul (h : GL (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.pi fun i => (Matrix.toLin' ((h : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)).comp (LinearMap.proj i)

private theorem rowMul_entries (h g : GL (Fin 2) ℝ) : rowMul h (entries g) = entries (g * h) := by
  funext i j
  simp [rowMul, entries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]

private theorem det_rowMul (h : GL (Fin 2) ℝ) :
    LinearMap.det (rowMul h) = (Matrix.GeneralLinearGroup.det h : ℝ) ^ 2 := by
  unfold rowMul
  rw [LinearMap.det_pi]
  simp [Matrix.det_transpose, Finset.prod_const]

private theorem det_rowMul_ne_zero (h : GL (Fin 2) ℝ) : LinearMap.det (rowMul h) ≠ 0 := by
  rw [det_rowMul]
  exact pow_ne_zero 2 (Matrix.GeneralLinearGroup.det h).ne_zero

private theorem rowMul_inv_rowMul (h : GL (Fin 2) ℝ) (A : Fin 2 → Fin 2 → ℝ) : rowMul h⁻¹ (rowMul h A) = A := by
  funext i
  simp only [rowMul, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply]
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
  have hmul : (h : Matrix (Fin 2) (Fin 2) ℝ) * ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
    Units.mul_inv h
  rw [hmul, Matrix.transpose_one, Matrix.one_mulVec]

private theorem image_entries_preimage_mul_right (h : GL (Fin 2) ℝ) (S : Set (GL (Fin 2) ℝ)) :
    entries '' ((fun g => g * h) ⁻¹' S) = rowMul h ⁻¹' (entries '' S) := by
  ext A
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * h, hg, (rowMul_entries h g).symm⟩
  · rintro ⟨g', hg', hA⟩
    refine ⟨g' * h⁻¹, ?_, ?_⟩
    · show g' * h⁻¹ * h ∈ S
      simpa using hg'
    · rw [← rowMul_inv_rowMul h A, ← hA, rowMul_entries]

private theorem map_mul_right_comap (h : GL (Fin 2) ℝ) :
    Measure.map (fun g => g * h) (Measure.comap entries volume) =
      ENNReal.ofReal |(LinearMap.det (rowMul h))⁻¹| • Measure.comap entries volume := by
  ext S hS
  have hm : Measurable fun g : GL (Fin 2) ℝ => g * h :=
    (continuous_id.mul continuous_const : Continuous fun g : GL (Fin 2) ℝ => g * h).measurable
  rw [Measure.map_apply hm hS, measurableEmbedding_entries.comap_apply,
    image_entries_preimage_mul_right, Measure.addHaar_preimage_linearMap volume (det_rowMul_ne_zero h),
    Measure.smul_apply, measurableEmbedding_entries.comap_apply, smul_eq_mul]

private theorem map_mul_right_withDensity (h : GL (Fin 2) ℝ) (ν : Measure (GL (Fin 2) ℝ)) {ρ : GL (Fin 2) ℝ → ENNReal}
    (hρ : Measurable ρ) :
    Measure.map (fun g => g * h) (ν.withDensity ρ) =
      (Measure.map (fun g => g * h) ν).withDensity fun g => ρ (g * h⁻¹) := by
  have hm : Measurable fun g : GL (Fin 2) ℝ => g * h :=
    (continuous_id.mul continuous_const : Continuous fun g : GL (Fin 2) ℝ => g * h).measurable
  have hm' : Measurable fun g : GL (Fin 2) ℝ => g * h⁻¹ :=
    (continuous_id.mul continuous_const : Continuous fun g : GL (Fin 2) ℝ => g * h⁻¹).measurable
  have hf : Measurable fun g : GL (Fin 2) ℝ => ρ (g * h⁻¹) := hρ.comp hm'
  ext S hS
  rw [Measure.map_apply hm hS, withDensity_apply _ (hm hS), withDensity_apply _ hS,
    setLIntegral_map hS hf hm]
  simp only [mul_inv_cancel_right]

private theorem density_mul_inv (h g : GL (Fin 2) ℝ) :
    ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det (g * h⁻¹) : ℝ)| ^ 2)⁻¹ =
      ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det h : ℝ)| ^ 2) *
        ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹ := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, abs_mul, abs_inv]
  have h0 : |(Matrix.GeneralLinearGroup.det h : ℝ)| ≠ 0 := abs_ne_zero.mpr (Matrix.GeneralLinearGroup.det h).ne_zero
  field_simp

private theorem isMulRightInvariant_archMeasure : archMeasure.IsMulRightInvariant := by
  refine ⟨fun h => ?_⟩
  show Measure.map (fun g => g * h) ((Measure.comap entries volume).withDensity _) =
    (Measure.comap entries volume).withDensity _
  rw [map_mul_right_withDensity h _ measurable_density, map_mul_right_comap, withDensity_smul_measure]
  have hρ : (fun g : GL (Fin 2) ℝ => ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det (g * h⁻¹) : ℝ)| ^ 2)⁻¹) =
      ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det h : ℝ)| ^ 2) •
        fun g : GL (Fin 2) ℝ => ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹ :=
    funext fun g => density_mul_inv h g
  rw [hρ, withDensity_smul _ measurable_density, smul_smul, det_rowMul]
  have hd : |(Matrix.GeneralLinearGroup.det h : ℝ)| ^ 2 ≠ 0 :=
    pow_ne_zero 2 (abs_ne_zero.mpr (Matrix.GeneralLinearGroup.det h).ne_zero)
  have hscal : ENNReal.ofReal |((Matrix.GeneralLinearGroup.det h : ℝ) ^ 2)⁻¹| *
      ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det h : ℝ)| ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, abs_pow, inv_mul_cancel₀ hd, ENNReal.ofReal_one]
  rw [hscal, one_smul]

private def transposeLin : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ) where
  toFun A := fun i j => A j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem transposeLin_transposeLin (A : Fin 2 → Fin 2 → ℝ) : transposeLin (transposeLin A) = A := rfl

private theorem transposeLin_comp_transposeLin : transposeLin.comp transposeLin = LinearMap.id :=
  LinearMap.ext fun A => transposeLin_transposeLin A

private def glTranspose (h : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  ⟨(h : Matrix (Fin 2) (Fin 2) ℝ)ᵀ, ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ,
    by rw [← Matrix.transpose_mul]; simp, by rw [← Matrix.transpose_mul]; simp⟩

private def colMul (h : GL (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  transposeLin.comp ((rowMul (glTranspose h)).comp transposeLin)

private theorem colMul_entries (h g : GL (Fin 2) ℝ) : colMul h (entries g) = entries (h * g) := by
  funext i j
  simp [colMul, transposeLin, rowMul, glTranspose, entries, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.mul_apply]

private theorem det_colMul (h : GL (Fin 2) ℝ) :
    LinearMap.det (colMul h) = (Matrix.GeneralLinearGroup.det h : ℝ) ^ 2 := by
  have hτ : LinearMap.det transposeLin * LinearMap.det transposeLin = 1 := by
    rw [← LinearMap.det_comp, transposeLin_comp_transposeLin, LinearMap.det_id]
  unfold colMul
  rw [LinearMap.det_comp, LinearMap.det_comp, det_rowMul]
  have hdet : (Matrix.GeneralLinearGroup.det (glTranspose h) : ℝ) = Matrix.GeneralLinearGroup.det h := by
    show Matrix.det ((h : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) = Matrix.det (h : Matrix (Fin 2) (Fin 2) ℝ)
    exact Matrix.det_transpose _
  rw [hdet]
  calc LinearMap.det transposeLin * ((Matrix.GeneralLinearGroup.det h : ℝ) ^ 2 * LinearMap.det transposeLin)
      = (LinearMap.det transposeLin * LinearMap.det transposeLin) * (Matrix.GeneralLinearGroup.det h : ℝ) ^ 2 := by
        ring
    _ = (Matrix.GeneralLinearGroup.det h : ℝ) ^ 2 := by rw [hτ, one_mul]

private theorem colMul_inv_colMul (h : GL (Fin 2) ℝ) (A : Fin 2 → Fin 2 → ℝ) : colMul h⁻¹ (colMul h A) = A := by
  funext i j
  simp only [colMul, transposeLin, rowMul, glTranspose, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.pi_apply, LinearMap.proj_apply, Matrix.toLin'_apply, Matrix.transpose_transpose]
  rw [Matrix.mulVec_mulVec]
  have hmul : ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (h : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
    Units.inv_mul h
  rw [hmul, Matrix.one_mulVec]

private theorem det_colMul_ne_zero (h : GL (Fin 2) ℝ) : LinearMap.det (colMul h) ≠ 0 := by
  rw [det_colMul]
  exact pow_ne_zero 2 (Matrix.GeneralLinearGroup.det h).ne_zero

private theorem image_entries_preimage_mul_left (h : GL (Fin 2) ℝ) (S : Set (GL (Fin 2) ℝ)) :
    entries '' ((fun g => h * g) ⁻¹' S) = colMul h ⁻¹' (entries '' S) := by
  ext A
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨h * g, hg, (colMul_entries h g).symm⟩
  · rintro ⟨g', hg', hA⟩
    refine ⟨h⁻¹ * g', ?_, ?_⟩
    · show h * (h⁻¹ * g') ∈ S
      simpa using hg'
    · rw [← colMul_inv_colMul h A, ← hA, colMul_entries]

private theorem map_mul_left_comap (h : GL (Fin 2) ℝ) :
    Measure.map (fun g => h * g) (Measure.comap entries volume) =
      ENNReal.ofReal |(LinearMap.det (colMul h))⁻¹| • Measure.comap entries volume := by
  have hm : Measurable fun g : GL (Fin 2) ℝ => h * g :=
    (continuous_const.mul continuous_id : Continuous fun g : GL (Fin 2) ℝ => h * g).measurable
  ext S hS
  rw [Measure.map_apply hm hS, measurableEmbedding_entries.comap_apply, image_entries_preimage_mul_left,
    Measure.addHaar_preimage_linearMap volume (det_colMul_ne_zero h), Measure.smul_apply,
    measurableEmbedding_entries.comap_apply, smul_eq_mul]

private theorem map_mul_left_withDensity (h : GL (Fin 2) ℝ) (ν : Measure (GL (Fin 2) ℝ)) {ρ : GL (Fin 2) ℝ → ENNReal}
    (hρ : Measurable ρ) :
    Measure.map (fun g => h * g) (ν.withDensity ρ) =
      (Measure.map (fun g => h * g) ν).withDensity fun g => ρ (h⁻¹ * g) := by
  have hm : Measurable fun g : GL (Fin 2) ℝ => h * g :=
    (continuous_const.mul continuous_id : Continuous fun g : GL (Fin 2) ℝ => h * g).measurable
  have hm' : Measurable fun g : GL (Fin 2) ℝ => h⁻¹ * g :=
    (continuous_const.mul continuous_id : Continuous fun g : GL (Fin 2) ℝ => h⁻¹ * g).measurable
  have hf : Measurable fun g : GL (Fin 2) ℝ => ρ (h⁻¹ * g) := hρ.comp hm'
  ext S hS
  rw [Measure.map_apply hm hS, withDensity_apply _ (hm hS), withDensity_apply _ hS, setLIntegral_map hS hf hm]
  simp only [inv_mul_cancel_left]

private theorem density_inv_mul (h g : GL (Fin 2) ℝ) :
    ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det (h⁻¹ * g) : ℝ)| ^ 2)⁻¹ =
      ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det h : ℝ)| ^ 2) *
        ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹ := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, abs_mul, abs_inv]
  have h0 : |(Matrix.GeneralLinearGroup.det h : ℝ)| ≠ 0 := abs_ne_zero.mpr (Matrix.GeneralLinearGroup.det h).ne_zero
  field_simp

private theorem isMulLeftInvariant_archMeasure : archMeasure.IsMulLeftInvariant := by
  refine ⟨fun h => ?_⟩
  show Measure.map (fun g => h * g) ((Measure.comap entries volume).withDensity _) =
    (Measure.comap entries volume).withDensity _
  rw [map_mul_left_withDensity h _ measurable_density, map_mul_left_comap, withDensity_smul_measure]
  have hρ : (fun g : GL (Fin 2) ℝ => ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det (h⁻¹ * g) : ℝ)| ^ 2)⁻¹) =
      ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det h : ℝ)| ^ 2) •
        fun g : GL (Fin 2) ℝ => ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹ :=
    funext fun g => density_inv_mul h g
  rw [hρ, withDensity_smul _ measurable_density, smul_smul, det_colMul]
  have hd : |(Matrix.GeneralLinearGroup.det h : ℝ)| ^ 2 ≠ 0 :=
    pow_ne_zero 2 (abs_ne_zero.mpr (Matrix.GeneralLinearGroup.det h).ne_zero)
  have hscal : ENNReal.ofReal |((Matrix.GeneralLinearGroup.det h : ℝ) ^ 2)⁻¹| *
      ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det h : ℝ)| ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, abs_pow, inv_mul_cancel₀ hd, ENNReal.ofReal_one]
  rw [hscal, one_smul]

private theorem density_ne_zero (g : GL (Fin 2) ℝ) :
    ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹ ≠ 0 := by
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have h0 : (Matrix.GeneralLinearGroup.det g : ℝ) ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  positivity

private theorem isOpenPosMeasure_archMeasure : archMeasure.IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  show (Measure.comap entries volume).withDensity _ U ≠ 0
  rw [ne_eq, withDensity_apply_eq_zero measurable_density]
  have hset : {x : GL (Fin 2) ℝ | ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det x : ℝ)| ^ 2)⁻¹ ≠ 0} ∩ U = U := by
    rw [Set.inter_eq_right]
    exact fun x _ => density_ne_zero x
  rw [hset, measurableEmbedding_entries.comap_apply]
  exact (isOpenEmbedding_entries.isOpenMap U hU).measure_ne_zero volume (hne.image entries)

private theorem isHaarMeasure_archMeasure : archMeasure.IsHaarMeasure :=
  haveI := isLocallyFiniteMeasure_archMeasure
  { toIsFiniteMeasureOnCompacts := inferInstance
    toIsMulLeftInvariant := isMulLeftInvariant_archMeasure
    toIsOpenPosMeasure := isOpenPosMeasure_archMeasure }

private theorem main : RSCarrier.archMeasure.IsHaarMeasure ∧ RSCarrier.archMeasure.IsMulRightInvariant :=
  ⟨isHaarMeasure_archMeasure, isMulRightInvariant_archMeasure⟩

end ArchMeasureHaar
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure.ArchMeasureHaar"

theorem solution :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
    RSCarrier.archMeasure.IsHaarMeasure ∧ RSCarrier.archMeasure.IsMulRightInvariant :=
  ArchMeasureHaar.main

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure.ArchMeasureHaar"

end S_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure
end P2MW
export P2MW.S_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure (solution)
