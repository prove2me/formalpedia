-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e692b422-f683-57e3-8ed7-18772f037d6b

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Compactness.SigmaCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier
open Topology
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace LanglandsTunnell
namespace Converse
p2m_open "LanglandsTunnell"

private scoped instance : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)

private scoped instance : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩

private abbrev diagReflection : GL (Fin 2) ℝ := upperUnit (1 : ℝ) 0 (-1) one_ne_zero (by norm_num)

private def detOneSet : Set (rowIsometrySubgroup ℝ) :=
  {k | ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1}

private def unitCell : Set realUnipotent :=
  {n : realUnipotent | ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}

private def weighted (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ) (g : GL (Fin 2) ℝ) : ℂ :=
  (W g * F g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))

private def iwasawaChart (q : (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ) : GL (Fin 2) ℝ :=
  (if h : 0 < q.1.2.1 ∧ 0 < q.1.2.2 then
      upperUnit (q.1.2.2 * q.1.2.1) (q.1.2.2 * q.1.1) q.1.2.2 (mul_pos h.2 h.1).ne' h.2.ne'
    else 1) * (q.2 : GL (Fin 2) ℝ)

private def iwasawaBase : Measure (ℝ × ℝ × ℝ) :=
  (volume.restrict (Set.univ ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).withDensity
    (fun q => ENNReal.ofReal ((q.2.1 ^ 2) ⁻¹ * q.2.2⁻¹))

private def torusIntegrand (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ) (a₂ a₁ : ℝ) : ℂ :=
  if h : a₁ ≠ 0 ∧ 0 < a₂ then
    weighted s W F (upperUnit a₁ 0 a₂ h.1 h.2.ne') * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
  else 0

private theorem measurable_weighted (s : ℂ) {W F : GL (Fin 2) ℝ → ℂ} (hW : Measurable W) (hF : Measurable F) :
    Measurable (weighted s W F) := by
  unfold weighted
  have h1 : (fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ)) =
      fun g : GL (Fin 2) ℝ => ((g : Matrix (Fin 2) (Fin 2) ℝ)).det :=
    funext fun g => Matrix.GeneralLinearGroup.val_det_apply g
  have hdet : Continuous fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ) := by
    rw [h1]
    exact Units.continuous_val.matrix_det
  exact (hW.mul hF).mul ((Complex.continuous_ofReal.comp (continuous_abs.comp hdet)).measurable.pow_const _)

private theorem aemeasurable_iwasawaChart [archMeasure.IsHaarMeasure] (ν : Measure (rowIsometrySubgroup ℝ))
    (c : NNReal) (hμ : archMeasure = c • Measure.map iwasawaChart (iwasawaBase.prod ν)) :
    AEMeasurable iwasawaChart (iwasawaBase.prod ν) := by
  by_contra h
  rw [Measure.map_of_not_aemeasurable h, smul_zero] at hμ
  have h0 : (0 : ENNReal) < archMeasure Set.univ := isOpen_univ.measure_pos archMeasure Set.univ_nonempty
  rw [hμ] at h0
  simp at h0

private abbrev glEntries (g : GL (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j

private theorem continuousOn_matrixInv_isUnit :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_
    (Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin 2) (Fin 2) ℝ))).continuousOn
  exact (Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

private theorem isEmbedding_glVal : IsEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv_isUnit fun u => (Matrix.coe_units_inv u).symm

private theorem isEmbedding_glEntries : IsEmbedding glEntries :=
  isEmbedding_glVal

private theorem isOpen_range_glEntries : IsOpen (Set.range glEntries) := by
  have h : Set.range glEntries =
      (fun A : Fin 2 → Fin 2 → ℝ => (Matrix.of A).det) ⁻¹' {x | x ≠ 0} := by
    ext A
    constructor
    · rintro ⟨u, rfl⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
    · intro hA
      exact (Matrix.isUnit_iff_isUnit_det (Matrix.of A)).mpr (isUnit_iff_ne_zero.mpr hA)
  rw [h]
  exact isOpen_ne.preimage (Continuous.matrix_det continuous_id)

private theorem isOpenEmbedding_glEntries : IsOpenEmbedding glEntries :=
  ⟨isEmbedding_glEntries, isOpen_range_glEntries⟩

private theorem locallyCompactSpace_gl_two_real : LocallyCompactSpace (GL (Fin 2) ℝ) :=
  isOpenEmbedding_glEntries.locallyCompactSpace

private theorem secondCountableTopology_gl_two_real : SecondCountableTopology (GL (Fin 2) ℝ) :=
  isEmbedding_glEntries.secondCountableTopology

private def rowIsometryEntries : Set (Fin 2 → Fin 2 → ℝ) :=
  {A | ‖(Matrix.of A).det‖ = 1 ∧
    ∀ x y : ℝ, ‖x * A 0 0 + y * A 1 0‖ ^ 2 + ‖x * A 0 1 + y * A 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2}

private theorem isClosed_rowIsometryEntries : IsClosed rowIsometryEntries := by
  unfold rowIsometryEntries
  rw [Set.setOf_and]
  refine IsClosed.inter (isClosed_eq ((Continuous.matrix_det continuous_id).norm) continuous_const) ?_
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
  fun_prop

private theorem abs_le_one_of_mem_rowIsometryEntries {A : Fin 2 → Fin 2 → ℝ} (hA : A ∈ rowIsometryEntries)
    (i j : Fin 2) : A i j ∈ Set.Icc (-1 : ℝ) 1 := by
  have h10 := hA.2 1 0
  have h01 := hA.2 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add, Real.norm_eq_abs, sq_abs, norm_one, norm_zero,
    one_pow] at h10 h01
  rw [Set.mem_Icc]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    constructor <;> nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 0 1), sq_nonneg (A 1 0), sq_nonneg (A 1 1),
      sq_nonneg (A 0 0 + 1), sq_nonneg (A 0 0 - 1), sq_nonneg (A 0 1 + 1), sq_nonneg (A 0 1 - 1),
      sq_nonneg (A 1 0 + 1), sq_nonneg (A 1 0 - 1), sq_nonneg (A 1 1 + 1), sq_nonneg (A 1 1 - 1)]

private theorem isCompact_rowIsometryEntries : IsCompact rowIsometryEntries := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine Metric.isCompact_of_isClosed_isBounded isClosed_rowIsometryEntries (hbox.isBounded.subset ?_)
  intro A hA
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  exact fun i j => abs_le_one_of_mem_rowIsometryEntries hA i j

private theorem image_glEntries_rowIsometrySubgroup :
    glEntries '' (rowIsometrySubgroup ℝ : Set (GL (Fin 2) ℝ)) = rowIsometryEntries := by
  ext A
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hA
    have hdet : (Matrix.of A).det ≠ 0 := by
      intro h0
      have := hA.1
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) hdet, hA, rfl⟩

private theorem isCompact_rowIsometrySubgroup : IsCompact (rowIsometrySubgroup ℝ : Set (GL (Fin 2) ℝ)) := by
  rw [isEmbedding_glEntries.toIsInducing.isCompact_iff, image_glEntries_rowIsometrySubgroup]
  exact isCompact_rowIsometryEntries

private theorem compactSpace_rowIsometrySubgroup : CompactSpace (rowIsometrySubgroup ℝ) :=
  isCompact_iff_compactSpace.1 isCompact_rowIsometrySubgroup

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

private theorem measurable_haarQuotient_weight [BorelSpace G] (H : Subgroup G) (μH : Measure H) :
    Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · exact Measurable.tsum fun n =>
      (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  · exact measurable_const

private theorem measurable_haarQuotient_density [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable (HaarQuotient.density H μH) := by
  unfold HaarQuotient.density
  refine (measurable_haarQuotient_weight H μH).div ?_
  have hm : Measurable fun p : H × G => HaarQuotient.weight H μH ((p.1 : G) * p.2) :=
    (measurable_haarQuotient_weight H μH).comp
      ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
  exact hm.lintegral_prod_left' (μ := μH)

private theorem haarQuotient_weight_ne_top (H : Subgroup G) (μH : Measure H) (g : G) :
    HaarQuotient.weight H μH g ≠ ⊤ := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine ne_top_of_le_ne_top (ENNReal.tsum_geometric_two ▸ ENNReal.ofNat_ne_top) (ENNReal.tsum_le_tsum fun n => ?_)
    calc (2⁻¹ : ℝ≥0∞) ^ n * (1 + μH _)⁻¹ * (interior _).indicator (fun _ => (1 : ℝ≥0∞)) g
        ≤ (2⁻¹ : ℝ≥0∞) ^ n * 1 * 1 := by
          gcongr
          · exact ENNReal.inv_le_one.2 le_self_add
          · exact Set.indicator_le' (fun _ _ => le_rfl) (fun _ _ => zero_le_one) g
      _ = (2⁻¹ : ℝ≥0∞) ^ n := by ring
  · exact ENNReal.zero_ne_top

private theorem haarQuotient_weight_pos [IsTopologicalGroup G] [BorelSpace G] [SigmaCompactSpace G]
    [WeaklyLocallyCompactSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] (g : G) : 0 < HaarQuotient.weight H μH g := by
  unfold HaarQuotient.weight
  rw [dif_pos ⟨inferInstance, inferInstance⟩]
  set K := CompactExhaustion.choice G with hK
  obtain ⟨n, hn⟩ : ∃ n, g ∈ interior (K (n + 1) : Set G) := ⟨K.find g, K.subset_interior_succ _ (K.mem_find g)⟩
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum n)
  rw [Set.indicator_of_mem hn, mul_one]
  refine ENNReal.mul_pos (pow_ne_zero _ (by simp)) (ENNReal.inv_ne_zero.2 ?_)
  refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ?_⟩
  have hc : IsCompact (((↑) : H → G) ⁻¹' ((K (n + 1) : Set G) * (K (n + 1) : Set G)⁻¹)) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage ((K.isCompact _).mul (K.isCompact _).inv)
  exact hc.measure_lt_top.ne

private theorem haarQuotient_density_ne_top [IsTopologicalGroup G] [BorelSpace G] [SigmaCompactSpace G]
    [WeaklyLocallyCompactSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] (g : G) : HaarQuotient.density H μH g ≠ ⊤ := by
  unfold HaarQuotient.density
  refine (ENNReal.div_lt_top (haarQuotient_weight_ne_top H μH g) ?_).ne
  have hm : Measurable fun x : H => HaarQuotient.weight H μH ((x : G) * g) :=
    (measurable_haarQuotient_weight H μH).comp (measurable_subtype_coe.mul_const g)
  refine ((lintegral_pos_iff_support hm).2 ?_).ne'
  have hs : (Function.support fun x : H => HaarQuotient.weight H μH ((x : G) * g)) = Set.univ :=
    Set.eq_univ_of_forall fun x => (haarQuotient_weight_pos H hH μH _).ne'
  rw [hs]
  exact isOpen_univ.measure_pos μH Set.univ_nonempty

end Generic

private def unipCoord (g : GL (Fin 2) ℝ) : ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1

private theorem unipCoord_unipotentGL2 (x : ℝ) : unipCoord (unipotentGL2 x) = x := by
  simp [unipCoord, unipotentGL2]

private theorem continuous_unipCoord : Continuous unipCoord := by
  unfold unipCoord
  exact Units.continuous_val.matrix_elem 0 1

private theorem continuous_unipotentGL2 : Continuous (unipotentGL2 : ℝ → GL (Fin 2) ℝ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : ℝ => (!![(1 : ℝ), x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : ℝ => (!![(1 : ℝ), -x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem mem_realUnipotent_iff (g : GL (Fin 2) ℝ) :
    g ∈ realUnipotent ↔ g = unipotentGL2 (unipCoord g) := by
  constructor
  · rintro ⟨y, rfl⟩
    change unipotentGL2 (Multiplicative.toAdd y) =
      unipotentGL2 (unipCoord (unipotentGL2 (Multiplicative.toAdd y)))
    rw [unipCoord_unipotentGL2]
  · intro h
    exact ⟨Multiplicative.ofAdd (unipCoord g), by simpa [unipotentGL2Hom] using h.symm⟩

private theorem isClosed_realUnipotent :
    IsClosed ((realUnipotent : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  have h : ((realUnipotent : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) =
      {g | g = unipotentGL2 (unipCoord g)} := by
    ext g
    exact mem_realUnipotent_iff g
  rw [h]
  exact isClosed_eq continuous_id (continuous_unipotentGL2.comp continuous_unipCoord)

private def unipHomeo : ℝ ≃ₜ realUnipotent where
  toFun x := ⟨unipotentGL2 x, (mem_realUnipotent_iff _).2 (by rw [unipCoord_unipotentGL2])⟩
  invFun n := unipCoord n
  left_inv x := unipCoord_unipotentGL2 x
  right_inv n := Subtype.ext ((mem_realUnipotent_iff _).1 n.2).symm
  continuous_toFun := continuous_unipotentGL2.subtype_mk _
  continuous_invFun := continuous_unipCoord.comp continuous_subtype_val

@[scoped simp] private theorem coe_unipHomeo_apply (x : ℝ) :
    ((unipHomeo x : realUnipotent) : GL (Fin 2) ℝ) = unipotentGL2 x := rfl

private theorem unipHomeo_add (c x : ℝ) : unipHomeo (c + x) = unipHomeo c * unipHomeo x :=
  Subtype.ext (unipotentGL2_add c x)

private theorem unipHomeo_unipCoord (n : realUnipotent) : unipHomeo (unipCoord n) = n :=
  unipHomeo.apply_symm_apply n

private theorem preimage_unitCell : unipHomeo ⁻¹' unitCell = Set.Icc (0 : ℝ) 1 := by
  ext x
  simp [unitCell, unipotentGL2]

private theorem isCompact_unitCell : IsCompact unitCell := by
  have h : unitCell = unipHomeo '' Set.Icc (0 : ℝ) 1 := by
    rw [← preimage_unitCell, Homeomorph.image_preimage]
  rw [h]
  exact isCompact_Icc.image unipHomeo.continuous

private theorem image_Ioo_subset_unitCell : unipHomeo '' Set.Ioo (0 : ℝ) 1 ⊆ unitCell := by
  rw [Set.image_subset_iff, preimage_unitCell]
  exact Set.Ioo_subset_Icc_self

private scoped instance : LocallyCompactSpace realUnipotent := unipHomeo.locallyCompactSpace_iff.1 inferInstance

private scoped instance : SecondCountableTopology realUnipotent := unipHomeo.symm.secondCountableTopology

section Borel

private theorem isMulRightInvariant_of_realUnipotent (μN : Measure realUnipotent) [μN.IsMulLeftInvariant] :
    μN.IsMulRightInvariant :=
  ⟨fun n => by
    have h : (fun m : realUnipotent => m * n) = fun m => n * m :=
      funext fun m => IsMulCommutative.is_comm.comm m n
    rw [h]
    exact map_mul_left_eq_self μN n⟩

private def unipLebesgue : Measure realUnipotent := Measure.map unipHomeo (volume : Measure ℝ)

private theorem unipLebesgue_apply (S : Set realUnipotent) (hS : MeasurableSet S) :
    unipLebesgue S = volume (unipHomeo ⁻¹' S) :=
  Measure.map_apply unipHomeo.continuous.measurable hS

private theorem unipLebesgue_unitCell : unipLebesgue unitCell = 1 := by
  rw [unipLebesgue_apply _ isCompact_unitCell.isClosed.measurableSet, preimage_unitCell, Real.volume_Icc]
  simp

private scoped instance unipLebesgue_isHaarMeasure : unipLebesgue.IsHaarMeasure where
  map_mul_left_eq_self n := by
    unfold unipLebesgue
    rw [Measure.map_map (measurable_const_mul n) unipHomeo.continuous.measurable]
    have h : ((fun m : realUnipotent => n * m) ∘ unipHomeo) = unipHomeo ∘ (fun x : ℝ => unipCoord n + x) := by
      funext x
      simp only [Function.comp, unipHomeo_add, unipHomeo_unipCoord]
    rw [h, ← Measure.map_map unipHomeo.continuous.measurable (measurable_const_add _), map_add_left_eq_self]
  lt_top_of_isCompact K hK := by
    rw [unipLebesgue_apply _ hK.isClosed.measurableSet]
    exact (unipHomeo.isCompact_preimage.2 hK).measure_lt_top
  open_pos U hU hne := by
    rw [unipLebesgue_apply _ hU.measurableSet]
    refine (unipHomeo.isOpen_preimage.2 hU).measure_ne_zero volume ?_
    obtain ⟨n, hn⟩ := hne
    exact ⟨unipHomeo.symm n, by simpa using hn⟩

private theorem haar_eq_smul_unipLebesgue (μN : Measure realUnipotent) [μN.IsHaarMeasure] :
    μN = μN unitCell • unipLebesgue := by
  have h := Measure.isMulLeftInvariant_eq_smul μN unipLebesgue
  have hc : μN unitCell = ((μN.haarScalarFactor unipLebesgue : ℝ≥0) : ℝ≥0∞) := by
    conv_lhs => rw [h]
    rw [Measure.smul_apply, unipLebesgue_unitCell, ENNReal.smul_def, smul_eq_mul, mul_one]
  ext s hs
  rw [Measure.smul_apply, hc, smul_eq_mul]
  conv_lhs => rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

private theorem lintegral_haar_eq_mul_lintegral_unipHomeo (μN : Measure realUnipotent) [μN.IsHaarMeasure]
    (Φ : realUnipotent → ℝ≥0∞) : ∫⁻ n, Φ n ∂μN = μN unitCell * ∫⁻ x : ℝ, Φ (unipHomeo x) := by
  have key : ∀ ν : Measure realUnipotent, ν = μN unitCell • unipLebesgue →
      ∫⁻ n, Φ n ∂ν = μN unitCell * ∫⁻ x : ℝ, Φ (unipHomeo x) := by
    rintro ν rfl
    rw [lintegral_smul_measure]
    congr 1
    unfold unipLebesgue
    rw [← unipHomeo.toMeasurableEquiv_coe, lintegral_map_equiv]
  exact key μN (haar_eq_smul_unipLebesgue μN)

private theorem unitCell_measure_ne_zero (μN : Measure realUnipotent) [μN.IsHaarMeasure] : μN unitCell ≠ 0 := by
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono image_Ioo_subset_unitCell))
  exact (unipHomeo.isOpenMap _ isOpen_Ioo).measure_pos μN
    (Set.Nonempty.image _ ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩)

private theorem unitCell_measure_ne_top (μN : Measure realUnipotent) [μN.IsHaarMeasure] : μN unitCell ≠ ⊤ :=
  isCompact_unitCell.measure_lt_top.ne

private theorem mul_lintegral_density_unipHomeo_mul
    [LocallyCompactSpace (GL (Fin 2) ℝ)] [SecondCountableTopology (GL (Fin 2) ℝ)]
    (μN : Measure realUnipotent) [μN.IsHaarMeasure] (g : GL (Fin 2) ℝ) :
    μN unitCell * ∫⁻ x : ℝ, HaarQuotient.density realUnipotent μN ((unipHomeo x : GL (Fin 2) ℝ) * g) = 1 := by
  haveI := isMulRightInvariant_of_realUnipotent μN
  have h := HaarQuotient.lintegral_density_mul_eq_one realUnipotent isClosed_realUnipotent μN g
  rw [lintegral_haar_eq_mul_lintegral_unipHomeo μN] at h
  exact h

private theorem lintegral_density_unipHomeo_mul
    [LocallyCompactSpace (GL (Fin 2) ℝ)] [SecondCountableTopology (GL (Fin 2) ℝ)]
    (μN : Measure realUnipotent) [μN.IsHaarMeasure] (g : GL (Fin 2) ℝ) :
    ∫⁻ x : ℝ, HaarQuotient.density realUnipotent μN ((unipHomeo x : GL (Fin 2) ℝ) * g) = (μN unitCell)⁻¹ := by
  have h := mul_lintegral_density_unipHomeo_mul μN g
  rw [mul_comm] at h
  exact ENNReal.eq_inv_of_mul_eq_one_left h

private theorem measurable_density (μN : Measure realUnipotent) [μN.IsHaarMeasure] :
    Measurable (HaarQuotient.density realUnipotent μN) := by
  haveI := secondCountableTopology_gl_two_real
  exact measurable_haarQuotient_density realUnipotent μN

private theorem density_ne_top (μN : Measure realUnipotent) [μN.IsHaarMeasure] (g : GL (Fin 2) ℝ) :
    HaarQuotient.density realUnipotent μN g ≠ ⊤ := by
  haveI := locallyCompactSpace_gl_two_real
  haveI := secondCountableTopology_gl_two_real
  exact haarQuotient_density_ne_top realUnipotent isClosed_realUnipotent μN g

private theorem unitCell_pos (μN : Measure realUnipotent) [μN.IsHaarMeasure] : 0 < (μN unitCell).toReal :=
  ENNReal.toReal_pos (unitCell_measure_ne_zero μN) (unitCell_measure_ne_top μN)

private theorem integral_density_toReal_unipotent_mul (μN : Measure realUnipotent) [μN.IsHaarMeasure]
    (g₀ : GL (Fin 2) ℝ) :
    ∫ x : ℝ, (HaarQuotient.density realUnipotent μN (unipotentGL2 x * g₀)).toReal = ((μN unitCell).toReal)⁻¹ := by
  haveI := locallyCompactSpace_gl_two_real
  haveI := secondCountableTopology_gl_two_real
  have hm : Measurable fun x : ℝ => HaarQuotient.density realUnipotent μN (unipotentGL2 x * g₀) :=
    (measurable_density μN).comp (continuous_unipotentGL2.measurable.mul_const g₀)
  have hlt : ∀ᵐ x : ℝ, HaarQuotient.density realUnipotent μN (unipotentGL2 x * g₀) < ⊤ :=
    Filter.Eventually.of_forall fun x => (density_ne_top μN _).lt_top
  rw [integral_toReal hm.aemeasurable hlt]
  have h := lintegral_density_unipHomeo_mul μN g₀
  simp only [coe_unipHomeo_apply] at h
  rw [h, ENNReal.toReal_inv]

end Borel

private theorem integral_withDensity_density (μN : Measure realUnipotent) [μN.IsHaarMeasure]
    (G : GL (Fin 2) ℝ → ℂ) :
    ∫ g, G g ∂(archMeasure.withDensity (HaarQuotient.density realUnipotent μN)) =
      ∫ g, (HaarQuotient.density realUnipotent μN g).toReal • G g ∂archMeasure :=
  integral_withDensity_eq_integral_toReal_smul (measurable_density μN)
    (Filter.Eventually.of_forall fun g => (density_ne_top μN g).lt_top) G

private theorem integral_archMeasure_eq_smul_integral_chart [archMeasure.IsHaarMeasure]
    (ν : Measure (rowIsometrySubgroup ℝ)) (c : NNReal)
    (hμ : archMeasure = c • Measure.map iwasawaChart (iwasawaBase.prod ν)) (G : GL (Fin 2) ℝ → ℂ)
    (hG : Measurable G) :
    ∫ g, G g ∂archMeasure = (c : ℝ) • ∫ q, G (iwasawaChart q) ∂(iwasawaBase.prod ν) := by
  have hφ := aemeasurable_iwasawaChart ν c hμ
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, integral_map hφ hG.aestronglyMeasurable]

private def baseSet : Set (ℝ × ℝ × ℝ) := Set.univ ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)

private def baseWeight (p : ℝ × ℝ × ℝ) : ℝ := (p.2.1 ^ 2)⁻¹ * p.2.2⁻¹

private theorem measurableSet_baseSet : MeasurableSet baseSet :=
  MeasurableSet.univ.prod (measurableSet_Ioi.prod measurableSet_Ioi)

private theorem measurable_baseWeight : Measurable baseWeight := by
  unfold baseWeight
  fun_prop

private theorem measurable_baseDensity :
    Measurable fun q : ℝ × ℝ × ℝ => ENNReal.ofReal ((q.2.1 ^ 2)⁻¹ * q.2.2⁻¹) :=
  measurable_baseWeight.ennreal_ofReal

private theorem baseWeight_nonneg {p : ℝ × ℝ × ℝ} (hp : p ∈ baseSet) : 0 ≤ baseWeight p := by
  obtain ⟨-, hy, ht⟩ : p.1 ∈ Set.univ ∧ p.2.1 ∈ Set.Ioi (0 : ℝ) ∧ p.2.2 ∈ Set.Ioi (0 : ℝ) := by
    simpa only [baseSet, Set.mem_prod] using hp
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (inv_nonneg.mpr (le_of_lt ht))

private theorem iwasawaBase_eq : iwasawaBase = (volume.restrict baseSet).withDensity
    (fun q => ENNReal.ofReal ((q.2.1 ^ 2)⁻¹ * q.2.2⁻¹)) := rfl

private scoped instance sFinite_iwasawaBase : SFinite iwasawaBase := by
  rw [iwasawaBase_eq]; infer_instance

private theorem volume_restrict_baseSet :
    (volume : Measure (ℝ × ℝ × ℝ)).restrict baseSet =
      (volume : Measure ℝ).prod ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) := by
  rw [baseSet, Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict, Measure.restrict_univ]

private theorem volume_restrict_quadrant_set :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) =
      ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]

private theorem integrable_baseWeight_mul {G : ℝ × ℝ × ℝ → ℂ} (hG : Integrable G iwasawaBase) :
    Integrable (fun p => (baseWeight p : ℂ) * G p)
      ((volume : Measure ℝ).prod
        ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)))) := by
  rw [← volume_restrict_baseSet]
  have hfin : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ × ℝ)).restrict baseSet,
      (fun q : ℝ × ℝ × ℝ => ENNReal.ofReal ((q.2.1 ^ 2)⁻¹ * q.2.2⁻¹)) p < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have h := (integrable_withDensity_iff_integrable_smul' measurable_baseDensity hfin).mp
    (iwasawaBase_eq ▸ hG)
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_baseSet] with p hp
  show (ENNReal.ofReal (baseWeight p)).toReal • G p = (baseWeight p : ℂ) * G p
  rw [ENNReal.toReal_ofReal (baseWeight_nonneg hp), Complex.real_smul]

private theorem integral_iwasawaBase_eq (G : ℝ × ℝ × ℝ → ℂ) (hG : Integrable G iwasawaBase) :
    ∫ p, G p ∂iwasawaBase =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (∫ x : ℝ, G (x, y, t)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ) := by
  have hfin : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ × ℝ)).restrict baseSet,
      (fun q : ℝ × ℝ × ℝ => ENNReal.ofReal ((q.2.1 ^ 2)⁻¹ * q.2.2⁻¹)) p < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

  have h1 : ∫ p, G p ∂iwasawaBase = ∫ p in baseSet, (baseWeight p : ℂ) * G p := by
    rw [iwasawaBase_eq, integral_withDensity_eq_integral_toReal_smul measurable_baseDensity hfin]
    refine setIntegral_congr_fun measurableSet_baseSet fun p hp => ?_
    show (ENNReal.ofReal (baseWeight p)).toReal • G p = (baseWeight p : ℂ) * G p
    rw [ENNReal.toReal_ofReal (baseWeight_nonneg hp), Complex.real_smul]

  have hint := integrable_baseWeight_mul hG
  have h2 : ∫ p in baseSet, (baseWeight p : ℂ) * G p =
      ∫ p' in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), ∫ x : ℝ, (baseWeight (x, p') : ℂ) * G (x, p') := by
    show ∫ p, (baseWeight p : ℂ) * G p ∂((volume : Measure (ℝ × ℝ × ℝ)).restrict baseSet) = _
    rw [volume_restrict_baseSet, integral_prod_symm _ hint]

  have h3 : ∀ p' : ℝ × ℝ, ∫ x : ℝ, (baseWeight (x, p') : ℂ) * G (x, p') =
      (∫ x : ℝ, G (x, p'.1, p'.2)) * ((((p'.1 ^ 2)⁻¹ * p'.2⁻¹ : ℝ)) : ℂ) := by
    intro p'
    rw [mul_comm, ← integral_const_mul]
    rfl

  have hF : Integrable (fun p' : ℝ × ℝ => ∫ x : ℝ, (baseWeight (x, p') : ℂ) * G (x, p'))
      ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) :=
    hint.integral_prod_right
  have h4 : ∫ p' in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), ∫ x : ℝ, (baseWeight (x, p') : ℂ) * G (x, p') =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (∫ x : ℝ, G (x, y, t)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ) := by
    show ∫ p', _ ∂((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) = _
    rw [volume_restrict_quadrant_set] at hF ⊢
    rw [integral_prod_symm _ hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact h3 (y, t)
  rw [h1, h2, h4]

private theorem integrableOn_integral_iwasawaBase (G : ℝ × ℝ × ℝ → ℂ) (hG : Integrable G iwasawaBase) :
    IntegrableOn (fun p : ℝ × ℝ => (∫ x : ℝ, G (x, p.1, p.2)) * ((((p.1 ^ 2)⁻¹ * p.2⁻¹ : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  have hF : Integrable (fun p' : ℝ × ℝ => ∫ x : ℝ, (baseWeight (x, p') : ℂ) * G (x, p'))
      ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) :=
    (integrable_baseWeight_mul hG).integral_prod_right
  refine hF.congr (Filter.Eventually.of_forall fun p' => ?_)
  show (∫ x : ℝ, (baseWeight (x, p') : ℂ) * G (x, p')) =
    (∫ x : ℝ, G (x, p'.1, p'.2)) * ((((p'.1 ^ 2)⁻¹ * p'.2⁻¹ : ℝ)) : ℂ)
  rw [mul_comm, ← integral_const_mul]
  rfl

private theorem integral_prod_iwasawaBase (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure]
    (H : (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ → ℂ) (hH : Integrable H (iwasawaBase.prod ν)) :
    ∫ q, H q ∂(iwasawaBase.prod ν) =
      ∫ k, (∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (∫ x : ℝ, H ((x, y, t), k)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) ∂ν := by
  haveI : CompactSpace (rowIsometrySubgroup ℝ) := compactSpace_rowIsometrySubgroup
  rw [integral_prod_symm H hH]
  refine integral_congr_ae ?_
  filter_upwards [hH.prod_left_ae] with k hk
  exact integral_iwasawaBase_eq (fun p => H (p, k)) hk

private theorem ae_integrableOn_prod_iwasawaBase (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure]
    (H : (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ → ℂ) (hH : Integrable H (iwasawaBase.prod ν)) :
    ∀ᵐ k ∂ν, IntegrableOn
      (fun p : ℝ × ℝ => (∫ x : ℝ, H ((x, p.1, p.2), k)) * ((((p.1 ^ 2)⁻¹ * p.2⁻¹ : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  haveI : CompactSpace (rowIsometrySubgroup ℝ) := compactSpace_rowIsometrySubgroup
  filter_upwards [hH.prod_left_ae] with k hk
  exact integrableOn_integral_iwasawaBase (fun p => H (p, k)) hk

private theorem integrable_chart [archMeasure.IsHaarMeasure] (μN : Measure realUnipotent) [μN.IsHaarMeasure]
    (ν : Measure (rowIsometrySubgroup ℝ))
    [ν.IsHaarMeasure] (c : NNReal) (hc : 0 < c) (hμ : archMeasure = c • Measure.map iwasawaChart (iwasawaBase.prod ν))
    (s : ℂ) {W F : GL (Fin 2) ℝ → ℂ} (hW : Measurable W) (hF : Measurable F)
    (hint : Integrable (weighted s W F) (archMeasure.withDensity (HaarQuotient.density realUnipotent μN))) :
    Integrable (fun q => (HaarQuotient.density realUnipotent μN (iwasawaChart q)).toReal •
      weighted s W F (iwasawaChart q))
      (iwasawaBase.prod ν) := by
  have h1 : Integrable (fun g => (HaarQuotient.density realUnipotent μN g).toReal • weighted s W F g) archMeasure :=
    (integrable_withDensity_iff_integrable_smul' (measurable_density μN)
      (Filter.Eventually.of_forall fun g => (density_ne_top μN g).lt_top)).1 hint
  rw [hμ, ENNReal.smul_def, integrable_smul_measure (ENNReal.coe_ne_zero.2 hc.ne') ENNReal.coe_ne_top] at h1
  have hGm : Measurable fun g => (HaarQuotient.density realUnipotent μN g).toReal • weighted s W F g :=
    (measurable_density μN).ennreal_toReal.smul (measurable_weighted s hW hF)
  exact (integrable_map_measure hGm.aestronglyMeasurable (aemeasurable_iwasawaChart ν c hμ)).1 h1

private theorem unipotentGL2_mem_realUnipotent (x : ℝ) : unipotentGL2 x ∈ realUnipotent :=
  ⟨Multiplicative.ofAdd x, rfl⟩

private theorem det_unipotentGL2 (x : ℝ) : ((unipotentGL2 x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  simp [Matrix.det_fin_two]

private theorem abs_det_unipotentGL2_mul (x : ℝ) (g : GL (Fin 2) ℝ) :
    |(Matrix.GeneralLinearGroup.det (unipotentGL2 x * g) : ℝ)| = |(Matrix.GeneralLinearGroup.det g : ℝ)| := by
  rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    det_unipotentGL2, one_mul]

private theorem abs_det_mul_rowIsometry (g : GL (Fin 2) ℝ) {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) :
    |(Matrix.GeneralLinearGroup.det (g * k) : ℝ)| = |(Matrix.GeneralLinearGroup.det g : ℝ)| := by
  have h := (mem_rowIsometrySubgroup_iff.1 hk).1
  rw [Real.norm_eq_abs] at h
  rw [map_mul, Units.val_mul, abs_mul, Matrix.GeneralLinearGroup.val_det_apply k, h, mul_one]

private theorem weighted_unipotent_mul (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g) (x : ℝ) (g : GL (Fin 2) ℝ) :
    weighted s W F (unipotentGL2 x * g) = weighted s W F g := by
  unfold weighted
  rw [hN _ (unipotentGL2_mem_realUnipotent x) g, abs_det_unipotentGL2_mul]

private theorem weighted_mul_detOne (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup ℝ) (hdet : Matrix.GeneralLinearGroup.det k = 1)
    (g : GL (Fin 2) ℝ) :
    weighted s W F (g * k) = weighted s W F g := by
  unfold weighted
  rw [hK k hk hdet g, abs_det_mul_rowIsometry g hk]

private theorem upperUnit_eq_unipotentGL2_mul_diag (x y t : ℝ) (hty : t * y ≠ 0) (ht : t ≠ 0) :
    upperUnit (t * y) (t * x) t hty ht = unipotentGL2 x * upperUnit (t * y) 0 t hty ht := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem upperUnit_mul_diagReflection (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    upperUnit a 0 t ha ht * diagReflection = upperUnit a 0 (-t) ha (neg_ne_zero.2 ht) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperUnit_neg_mul_neg_one (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    upperUnit a 0 (-t) ha (neg_ne_zero.2 ht) * (-1 : GL (Fin 2) ℝ) =
      upperUnit (-a) 0 t (neg_ne_zero.2 ha) ht := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_neg]

private theorem neg_one_mem_rowIsometrySubgroup : (-1 : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup ℝ := by
  rw [mem_rowIsometrySubgroup_iff]
  refine ⟨?_, fun x y => ?_⟩
  · simp [Units.val_neg, Units.val_one, Matrix.det_neg, Fintype.card_fin]
  · simp [Units.val_neg, Units.val_one, norm_neg]

private theorem diagReflection_mem_rowIsometrySubgroup : diagReflection ∈ rowIsometrySubgroup ℝ := by
  rw [mem_rowIsometrySubgroup_iff]
  refine ⟨?_, fun x y => ?_⟩
  · simp [diagReflection, upperUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two_of]
  · simp [norm_neg]

private theorem det_neg_one_eq_one : Matrix.GeneralLinearGroup.det (-1 : GL (Fin 2) ℝ) = 1 := by
  apply Units.ext
  simp [Units.val_neg, Units.val_one, Matrix.det_neg, Fintype.card_fin]

private theorem det_neg_one_mul (k : GL (Fin 2) ℝ) :
    Matrix.GeneralLinearGroup.det (-1 * k) = Matrix.GeneralLinearGroup.det k := by
  rw [map_mul, det_neg_one_eq_one, one_mul]

private theorem integral_Ioi_mul_left_inv_sq (φ : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    ∫ y in Set.Ioi (0 : ℝ), φ (t * y) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ) =
      ∫ a in Set.Ioi (0 : ℝ), φ a * (((a ^ 2)⁻¹ : ℝ) : ℂ) := by
  have h := integral_comp_mul_left_Ioi (fun a : ℝ => φ a * (((a ^ 2)⁻¹ : ℝ) : ℂ)) 0 ht
  rw [mul_zero] at h
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  calc ∫ y in Set.Ioi (0 : ℝ), φ (t * y) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)
      = ∫ y in Set.Ioi (0 : ℝ), (t : ℂ) • (φ (t * y) * ((((t * y) ^ 2)⁻¹ : ℝ) : ℂ)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
        rw [smul_eq_mul]
        push_cast
        field_simp
    _ = (t : ℂ) • ∫ y in Set.Ioi (0 : ℝ), φ (t * y) * ((((t * y) ^ 2)⁻¹ : ℝ) : ℂ) := integral_smul _ _
    _ = (t : ℂ) • ((t⁻¹ : ℝ) • ∫ a in Set.Ioi (0 : ℝ), φ a * (((a ^ 2)⁻¹ : ℝ) : ℂ)) := by rw [h]
    _ = ∫ a in Set.Ioi (0 : ℝ), φ a * (((a ^ 2)⁻¹ : ℝ) : ℂ) := by
        rw [Complex.real_smul, smul_eq_mul, ← mul_assoc]
        push_cast
        rw [mul_inv_cancel₀ ht', one_mul]

private theorem integral_eq_integral_Ioi_add_neg (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (hψn : Integrable fun a : ℝ => ψ (-a)) :
    ∫ a, ψ a = ∫ a in Set.Ioi (0 : ℝ), (ψ a + ψ (-a)) := by
  rw [integral_add hψ.integrableOn hψn.integrableOn, integral_comp_neg_Ioi, neg_zero, add_comm,
    intervalIntegral.integral_Iic_add_Ioi hψ.integrableOn hψ.integrableOn]

private theorem det_eq_one_iff_det_val (k : GL (Fin 2) ℝ) :
    Matrix.GeneralLinearGroup.det k = 1 ↔ (k : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

private theorem det_val_eq_one_or_neg_one_of_mem {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) :
    (k : Matrix (Fin 2) (Fin 2) ℝ).det = 1 ∨ (k : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
  have h := (mem_rowIsometrySubgroup_iff.1 hk).1
  rw [Real.norm_eq_abs] at h
  exact abs_eq (zero_le_one) |>.1 h

private theorem det_val_diagReflection : (diagReflection : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
  simp [diagReflection, Matrix.det_fin_two]

private abbrev reflectionO2 : rowIsometrySubgroup ℝ := ⟨diagReflection, diagReflection_mem_rowIsometrySubgroup⟩

private theorem preimage_reflection_mul_detOneSet :
    (fun k : rowIsometrySubgroup ℝ => reflectionO2 * k) ⁻¹' detOneSet = detOneSetᶜ := by
  ext k
  simp only [Set.mem_preimage, detOneSet, Set.mem_setOf_eq, Set.mem_compl_iff, Subgroup.coe_mul, Units.val_mul,
    Matrix.det_mul, det_val_diagReflection]
  rcases det_val_eq_one_or_neg_one_of_mem k.2 with h | h <;> rw [h] <;> norm_num

private theorem isClosed_detOneSet : IsClosed detOneSet :=
  isClosed_eq ((Continuous.matrix_det continuous_id).comp (Units.continuous_val.comp continuous_subtype_val))
    continuous_const

private theorem integral_rowIsometrySubgroup_eq_of_right_invariant
    [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
    [MeasurableSpace (rowIsometrySubgroup ℝ)] [BorelSpace (rowIsometrySubgroup ℝ)]
    (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure] (f : GL (Fin 2) ℝ → ℂ)
    (hf : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, f (g * k) = f g)
    (g : GL (Fin 2) ℝ) :
    ∫ k, f (g * (k : GL (Fin 2) ℝ)) ∂ν = (ν detOneSet).toReal • (f g + f (g * diagReflection)) := by
  haveI : CompactSpace (rowIsometrySubgroup ℝ) := compactSpace_rowIsometrySubgroup
  have hS : MeasurableSet detOneSet := isClosed_detOneSet.measurableSet
  have hpt : ∀ k : rowIsometrySubgroup ℝ, f (g * (k : GL (Fin 2) ℝ)) =
      detOneSet.indicator (fun _ => f g) k + detOneSetᶜ.indicator (fun _ => f (g * diagReflection)) k := by
    intro k
    by_cases hk : k ∈ detOneSet
    · rw [Set.indicator_of_mem hk, Set.indicator_of_notMem (by simpa using hk), add_zero]
      exact hf k k.2 ((det_eq_one_iff_det_val _).2 hk) g
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_mem (Set.mem_compl hk), zero_add]

      have hmem : reflectionO2 * k ∈ detOneSet := by
        rw [← Set.mem_preimage, preimage_reflection_mul_detOneSet]
        exact hk
      have hrr : (reflectionO2 : GL (Fin 2) ℝ) * (reflectionO2 : GL (Fin 2) ℝ) = 1 := by
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      calc f (g * (k : GL (Fin 2) ℝ))
          = f (g * diagReflection * ((reflectionO2 * k : rowIsometrySubgroup ℝ) : GL (Fin 2) ℝ)) := by
            rw [Subgroup.coe_mul, ← mul_assoc, mul_assoc g,
              show (reflectionO2 : GL (Fin 2) ℝ) = diagReflection from rfl]
            rw [hrr, mul_one]
        _ = f (g * diagReflection) :=
            hf _ (reflectionO2 * k).2 ((det_eq_one_iff_det_val _).2 hmem) _
  simp_rw [hpt]
  rw [integral_add ((integrable_const _).indicator hS) ((integrable_const _).indicator hS.compl),
    integral_indicator_const _ hS, integral_indicator_const _ hS.compl, ← preimage_reflection_mul_detOneSet,
    measureReal_def, measureReal_def, measure_preimage_mul, smul_add]

private theorem continuous_detVal :
    Continuous fun k : rowIsometrySubgroup ℝ => ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_det

private theorem detVal_eq_one_or_neg_one (k : rowIsometrySubgroup ℝ) :
    ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 ∨
      ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
  have h := (mem_rowIsometrySubgroup_iff.1 k.2).1
  rw [Real.norm_eq_abs] at h
  exact (abs_eq zero_le_one).1 h

private theorem isOpen_detOneSet : IsOpen detOneSet := by
  have hc : IsClosed {k : rowIsometrySubgroup ℝ | ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1} :=
    isClosed_eq continuous_detVal continuous_const
  convert hc.isOpen_compl using 1
  ext k
  simp only [detOneSet, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · intro h1 h2
    rw [h1] at h2
    norm_num at h2
  · intro h2
    rcases detVal_eq_one_or_neg_one k with h | h
    · exact h
    · exact absurd h h2

private theorem measurableSet_detOneSet : MeasurableSet detOneSet :=
  isOpen_detOneSet.measurableSet

private theorem iwasawaChart_zero_one (y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    iwasawaChart ((0, y, t), 1) = upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' := by
  simp only [iwasawaChart, hy, ht, and_self, dite_true, OneMemClass.coe_one, mul_one]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private def torusValue (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ) (t : ℝ) (ht : 0 < t) (a : ℝ) : ℂ :=
  if h : a ≠ 0 then weighted s W F (upperUnit a 0 t h ht.ne') else 0

private theorem torusIntegrand_eq_torusValue_mul (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ) (t : ℝ) (ht : 0 < t) (a : ℝ) :
    torusIntegrand s W F t a = torusValue s W F t ht a * (((a ^ 2)⁻¹ : ℝ) : ℂ) := by
  unfold torusIntegrand torusValue
  by_cases ha : a ≠ 0
  · rw [dif_pos ⟨ha, ht⟩, dif_pos ha]
  · rw [dif_neg (fun h => ha h.1), dif_neg ha, zero_mul]

private theorem weighted_mul_diagReflection (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    weighted s W F (upperUnit a 0 t ha ht * diagReflection) =
      weighted s W F (upperUnit (-a) 0 t (neg_ne_zero.2 ha) ht) := by
  rw [upperUnit_mul_diagReflection a t ha ht, ← upperUnit_neg_mul_neg_one a t ha ht,
    weighted_mul_detOne s W F hK (-1) neg_one_mem_rowIsometrySubgroup det_neg_one_eq_one]

private theorem torus_fold_slice (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (t : ℝ) (ht : 0 < t) (hψ : Integrable (torusIntegrand s W F t)) :
    (∫ y in Set.Ioi (0 : ℝ), weighted s W F (iwasawaChart ((0, y, t), 1)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) +
      (∫ y in Set.Ioi (0 : ℝ),
        weighted s W F (iwasawaChart ((0, y, t), 1) * diagReflection) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) =
    ∫ a₁ : ℝ, torusIntegrand s W F t a₁ := by
  set φ : ℝ → ℂ := torusValue s W F t ht with hφ
  have hA : (∫ y in Set.Ioi (0 : ℝ), weighted s W F (iwasawaChart ((0, y, t), 1)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ))
      = ∫ y in Set.Ioi (0 : ℝ), φ (t * y) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy : (0 : ℝ) < y := hy
    simp only [hφ, torusValue, iwasawaChart_zero_one y t hy ht, dif_pos (mul_pos ht hy).ne']
  have hB : (∫ y in Set.Ioi (0 : ℝ),
        weighted s W F (iwasawaChart ((0, y, t), 1) * diagReflection) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ))
      = ∫ y in Set.Ioi (0 : ℝ), φ (-(t * y)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy : (0 : ℝ) < y := hy
    have hty : t * y ≠ 0 := (mul_pos ht hy).ne'
    simp only [hφ, torusValue, iwasawaChart_zero_one y t hy ht, dif_pos (neg_ne_zero.2 hty)]
    rw [weighted_mul_diagReflection s W F hK (t * y) t hty ht.ne']
  have hψ' : ∀ a : ℝ, torusIntegrand s W F t a = φ a * (((a ^ 2)⁻¹ : ℝ) : ℂ) :=
    fun a => torusIntegrand_eq_torusValue_mul s W F t ht a
  have hψn : ∀ a : ℝ, torusIntegrand s W F t (-a) = φ (-a) * (((a ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro a
    rw [hψ' (-a), neg_sq]
  rw [hA, hB, integral_Ioi_mul_left_inv_sq φ ht, integral_Ioi_mul_left_inv_sq (fun a => φ (-a)) ht,
    integral_eq_integral_Ioi_add_neg _ hψ hψ.comp_neg,
    integral_add hψ.integrableOn (hψ.comp_neg.integrableOn)]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi fun a _ => (hψ' a).symm
  · exact setIntegral_congr_fun measurableSet_Ioi fun a _ => (hψn a).symm

private theorem torus_fold (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (hA : IntegrableOn (fun t : ℝ => ∫ y in Set.Ioi (0 : ℝ),
      weighted s W F (iwasawaChart ((0, y, t), 1)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) (Set.Ioi (0 : ℝ)))
    (hB : IntegrableOn (fun t : ℝ => ∫ y in Set.Ioi (0 : ℝ),
      weighted s W F (iwasawaChart ((0, y, t), 1) * diagReflection) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)))
    (hψ : ∀ᵐ a₂ ∂(volume.restrict (Set.Ioi (0 : ℝ))), Integrable (torusIntegrand s W F a₂)) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        weighted s W F (iwasawaChart ((0, y, t), 1)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) +
      (∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        weighted s W F (iwasawaChart ((0, y, t), 1) * diagReflection) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) =
    ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ, torusIntegrand s W F a₂ a₁ := by
  rw [← integral_add hA hB]
  refine integral_congr_ae ?_
  filter_upwards [hψ, ae_restrict_mem measurableSet_Ioi] with t hψt ht
  exact torus_fold_slice s W F hK t ht hψt

private theorem iwasawaChart_eq (x y t : ℝ) (k : rowIsometrySubgroup ℝ) (hy : 0 < y) (ht : 0 < t) :
    iwasawaChart ((x, y, t), k) = unipotentGL2 x * (iwasawaChart ((0, y, t), 1) * (k : GL (Fin 2) ℝ)) := by
  simp only [iwasawaChart, hy, ht, and_self, dite_true, OneMemClass.coe_one, mul_one]
  rw [← mul_assoc]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem integral_x (μN : Measure realUnipotent) [μN.IsHaarMeasure] (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g) (g₀ : GL (Fin 2) ℝ) :
    ∫ x : ℝ, (HaarQuotient.density realUnipotent μN (unipotentGL2 x * g₀)).toReal •
      weighted s W F (unipotentGL2 x * g₀) =
      ((μN unitCell).toReal)⁻¹ • weighted s W F g₀ := by
  simp_rw [weighted_unipotent_mul s W F hN]
  rw [integral_smul_const, integral_density_toReal_unipotent_mul μN g₀]

private def cosetFn (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ) (g : GL (Fin 2) ℝ) (p : ℝ × ℝ) : ℂ :=
  weighted s W F (iwasawaChart ((0, p.1, p.2), 1) * g) * ((((p.1 ^ 2)⁻¹ * p.2⁻¹ : ℝ)) : ℂ)

private abbrev quadrant : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)

private theorem ae_integrableOn_cosetFn [archMeasure.IsHaarMeasure] (μN : Measure realUnipotent) [μN.IsHaarMeasure]
    (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure] (c : NNReal) (hc : 0 < c)
    (hμ : archMeasure = c • Measure.map iwasawaChart (iwasawaBase.prod ν)) (s : ℂ) {W F : GL (Fin 2) ℝ → ℂ}
    (hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
    (hW : Measurable W) (hF : Measurable F)
    (hint : Integrable (weighted s W F) (archMeasure.withDensity (HaarQuotient.density realUnipotent μN))) :
    ∀ᵐ (k : rowIsometrySubgroup ℝ) ∂ν, IntegrableOn (cosetFn s W F (k : GL (Fin 2) ℝ)) quadrant := by
  have hκ : (μN unitCell).toReal ≠ 0 := (unitCell_pos μN).ne'
  filter_upwards [ae_integrableOn_prod_iwasawaBase ν _ (integrable_chart μN ν c hc hμ s hW hF hint)] with k hk
  refine IntegrableOn.congr_fun (hk.smul (μN unitCell).toReal) (fun p hp => ?_)
    (measurableSet_Ioi.prod measurableSet_Ioi)
  obtain ⟨hy, ht⟩ := hp
  have hy : (0 : ℝ) < p.1 := hy
  have ht : (0 : ℝ) < p.2 := ht
  have hx : ∀ x : ℝ, iwasawaChart ((x, p.1, p.2), k) =
      unipotentGL2 x * (iwasawaChart ((0, p.1, p.2), 1) * (k : GL (Fin 2) ℝ)) :=
    fun x => iwasawaChart_eq x p.1 p.2 k hy ht
  simp only [Pi.smul_apply, cosetFn]
  simp_rw [hx]
  rw [integral_x μN s W F hN, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hκ, one_smul]

private theorem diagReflection_mul_self : diagReflection * diagReflection = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem integrableOn_cosetFn_one (s : ℂ) {W F : GL (Fin 2) ℝ → ℂ}
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure]
    (hae : ∀ᵐ (k : rowIsometrySubgroup ℝ) ∂ν, IntegrableOn (cosetFn s W F (k : GL (Fin 2) ℝ)) quadrant) :
    IntegrableOn (cosetFn s W F 1) quadrant := by
  have hpos : ν detOneSet ≠ 0 := isOpen_detOneSet.measure_ne_zero ν ⟨1, by simp [detOneSet]⟩
  obtain ⟨k₀, hk₀, hint₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hae)
  have hdet : Matrix.GeneralLinearGroup.det (k₀ : GL (Fin 2) ℝ) = 1 := (det_eq_one_iff_det_val _).2 hk₀
  have heq : cosetFn s W F (k₀ : GL (Fin 2) ℝ) = cosetFn s W F 1 := by
    funext p
    simp only [cosetFn, mul_one]
    rw [weighted_mul_detOne s W F hK _ k₀.2 hdet]
  have hint₀' : IntegrableOn (cosetFn s W F (k₀ : GL (Fin 2) ℝ)) quadrant := hint₀
  rwa [heq] at hint₀'

private theorem integrableOn_cosetFn_reflection (s : ℂ) {W F : GL (Fin 2) ℝ → ℂ}
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure]
    (hae : ∀ᵐ (k : rowIsometrySubgroup ℝ) ∂ν, IntegrableOn (cosetFn s W F (k : GL (Fin 2) ℝ)) quadrant) :
    IntegrableOn (cosetFn s W F diagReflection) quadrant := by
  have hpos : ν detOneSetᶜ ≠ 0 := by
    rw [← preimage_reflection_mul_detOneSet, measure_preimage_mul]
    exact isOpen_detOneSet.measure_ne_zero ν ⟨1, by simp [detOneSet]⟩
  obtain ⟨k₁, hk₁, hint₁⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hae)
  have hk₁' : ((k₁ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1 :=
    (detVal_eq_one_or_neg_one k₁).resolve_left hk₁

  have hmem : diagReflection * (k₁ : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup ℝ :=
    (rowIsometrySubgroup ℝ).mul_mem diagReflection_mem_rowIsometrySubgroup k₁.2
  have hdet : Matrix.GeneralLinearGroup.det (diagReflection * (k₁ : GL (Fin 2) ℝ)) = 1 := by
    rw [det_eq_one_iff_det_val, Units.val_mul, Matrix.det_mul, det_val_diagReflection, hk₁']
    norm_num
  have hsplit : (k₁ : GL (Fin 2) ℝ) = diagReflection * (diagReflection * (k₁ : GL (Fin 2) ℝ)) := by
    rw [← mul_assoc, diagReflection_mul_self, one_mul]
  have heq : cosetFn s W F (k₁ : GL (Fin 2) ℝ) = cosetFn s W F diagReflection := by
    funext p
    simp only [cosetFn]
    rw [hsplit, ← mul_assoc, weighted_mul_detOne s W F hK _ hmem hdet]
  have hint₁' : IntegrableOn (cosetFn s W F (k₁ : GL (Fin 2) ℝ)) quadrant := hint₁
  rwa [heq] at hint₁'

private theorem volume_restrict_quadrant :
    (volume : Measure (ℝ × ℝ)).restrict quadrant =
      ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

private theorem integrableOn_torus_coset_one [archMeasure.IsHaarMeasure] (μN : Measure realUnipotent)
    [μN.IsHaarMeasure] (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure] (c : NNReal) (hc : 0 < c)
    (hμ : archMeasure = c • Measure.map iwasawaChart (iwasawaBase.prod ν)) (s : ℂ) {W F : GL (Fin 2) ℝ → ℂ}
    (hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (hW : Measurable W) (hF : Measurable F)
    (hint : Integrable (weighted s W F) (archMeasure.withDensity (HaarQuotient.density realUnipotent μN))) :
    IntegrableOn (fun t : ℝ => ∫ y in Set.Ioi (0 : ℝ),
      weighted s W F (iwasawaChart ((0, y, t), 1)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_cosetFn_one s hK ν (ae_integrableOn_cosetFn μN ν c hc hμ s hN hW hF hint)
  unfold IntegrableOn at h
  rw [volume_restrict_quadrant] at h
  have h2 := h.integral_prod_right
  simpa only [cosetFn, mul_one, IntegrableOn] using h2

private theorem integrableOn_torus_coset_reflection [archMeasure.IsHaarMeasure] (μN : Measure realUnipotent)
    [μN.IsHaarMeasure] (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure] (c : NNReal) (hc : 0 < c)
    (hμ : archMeasure = c • Measure.map iwasawaChart (iwasawaBase.prod ν)) (s : ℂ) {W F : GL (Fin 2) ℝ → ℂ}
    (hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (hW : Measurable W) (hF : Measurable F)
    (hint : Integrable (weighted s W F) (archMeasure.withDensity (HaarQuotient.density realUnipotent μN))) :
    IntegrableOn (fun t : ℝ => ∫ y in Set.Ioi (0 : ℝ),
      weighted s W F (iwasawaChart ((0, y, t), 1) * diagReflection) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_cosetFn_reflection s hK ν (ae_integrableOn_cosetFn μN ν c hc hμ s hN hW hF hint)
  unfold IntegrableOn at h
  rw [volume_restrict_quadrant] at h
  exact h.integral_prod_right

private theorem integrable_torusIntegrand_of_slices (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (t : ℝ) (ht : 0 < t)
    (h₁ : IntegrableOn (fun y : ℝ => cosetFn s W F 1 (y, t)) (Set.Ioi 0))
    (h₂ : IntegrableOn (fun y : ℝ => cosetFn s W F diagReflection (y, t)) (Set.Ioi 0)) :
    Integrable (torusIntegrand s W F t) := by
  set ψ : ℝ → ℂ := torusIntegrand s W F t with hψ_def
  set φ : ℝ → ℂ := torusValue s W F t ht with hφ_def
  have hψ : ∀ a : ℝ, ψ a = φ a * (((a ^ 2)⁻¹ : ℝ) : ℂ) := fun a => torusIntegrand_eq_torusValue_mul s W F t ht a
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'

  have hpos : IntegrableOn ψ (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun y : ℝ => ψ (t * y)) (Set.Ioi 0) := by
      refine IntegrableOn.congr_fun (h₁.mul_const ((t : ℂ)⁻¹)) (fun y hy => ?_) measurableSet_Ioi
      have hy : (0 : ℝ) < y := hy
      simp only [cosetFn, mul_one, iwasawaChart_zero_one y t hy ht, hψ, hφ_def, torusValue,
        dif_pos (mul_pos ht hy).ne']
      push_cast
      field_simp
    simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff ψ 0 ht).1 h1

  have hneg : IntegrableOn (fun a : ℝ => ψ (-a)) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun y : ℝ => ψ (-(t * y))) (Set.Ioi 0) := by
      refine IntegrableOn.congr_fun (h₂.mul_const ((t : ℂ)⁻¹)) (fun y hy => ?_) measurableSet_Ioi
      have hy : (0 : ℝ) < y := hy
      have hty : t * y ≠ 0 := (mul_pos ht hy).ne'
      simp only [cosetFn, iwasawaChart_zero_one y t hy ht, hψ, hφ_def, torusValue, dif_pos (neg_ne_zero.2 hty),
        weighted_mul_diagReflection s W F hK (t * y) t hty ht.ne', neg_sq]
      push_cast
      field_simp
    simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff (fun a : ℝ => ψ (-a)) 0 ht).1 h1
  have hIio : IntegrableOn ψ (Set.Iio 0) := by
    have h1 : Integrable ((Set.Ioi (0 : ℝ)).indicator fun a : ℝ => ψ (-a)) :=
      (integrable_indicator_iff measurableSet_Ioi).2 hneg
    have h2 := h1.comp_neg
    have h3 : (fun a : ℝ => ((Set.Ioi (0 : ℝ)).indicator fun a : ℝ => ψ (-a)) (-a)) =
        (Set.Iio (0 : ℝ)).indicator ψ := by
      funext a
      by_cases ha : a < 0
      · rw [Set.indicator_of_mem (show -a ∈ Set.Ioi (0 : ℝ) from neg_pos.2 ha), neg_neg,
          Set.indicator_of_mem (show a ∈ Set.Iio (0 : ℝ) from ha)]
      · rw [Set.indicator_of_notMem (show -a ∉ Set.Ioi (0 : ℝ) from fun h => ha (neg_pos.1 h)),
          Set.indicator_of_notMem (show a ∉ Set.Iio (0 : ℝ) from ha)]
    rw [h3] at h2
    exact (integrable_indicator_iff measurableSet_Iio).1 h2
  have hIic : IntegrableOn ψ (Set.Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio).2 hIio
  have huniv : IntegrableOn ψ (Set.Iic 0 ∪ Set.Ioi 0) := hIic.union hpos
  rw [Set.Iic_union_Ioi] at huniv
  exact integrableOn_univ.1 huniv

private theorem ae_integrable_torusIntegrand [archMeasure.IsHaarMeasure] (μN : Measure realUnipotent)
    [μN.IsHaarMeasure] (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure] (c : NNReal) (hc : 0 < c)
    (hμ : archMeasure = c • Measure.map iwasawaChart (iwasawaBase.prod ν)) (s : ℂ) {W F : GL (Fin 2) ℝ → ℂ}
    (hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
    (hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
      ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
    (hW : Measurable W) (hF : Measurable F)
    (hint : Integrable (weighted s W F) (archMeasure.withDensity (HaarQuotient.density realUnipotent μN))) :
    ∀ᵐ a₂ ∂(volume.restrict (Set.Ioi (0 : ℝ))), Integrable (torusIntegrand s W F a₂) := by
  have hae := ae_integrableOn_cosetFn μN ν c hc hμ s hN hW hF hint
  have h₁ := integrableOn_cosetFn_one s hK ν hae
  have h₂ := integrableOn_cosetFn_reflection s hK ν hae
  unfold IntegrableOn at h₁ h₂
  rw [volume_restrict_quadrant] at h₁ h₂
  filter_upwards [h₁.prod_left_ae, h₂.prod_left_ae, ae_restrict_mem measurableSet_Ioi] with t h₁t h₂t ht
  exact integrable_torusIntegrand_of_slices s W F hK t ht h₁t h₂t

private theorem rsArchIntegral_eq_of_iwasawa [archMeasure.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure] (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
        (_hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
        (_hW : Measurable W) (_hF : Measurable F)
        (_hint : Integrable (weighted s W F) (archMeasure.withDensity (HaarQuotient.density realUnipotent μN))),
        rsArchIntegral archMeasure μN s W F =
          ((c / (μN unitCell).toReal : ℝ) : ℂ) * ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ, torusIntegrand s W F a₂ a₁ := by
  haveI := compactSpace_rowIsometrySubgroup
  let ν : Measure (rowIsometrySubgroup ℝ) := Measure.haar
  obtain ⟨c, hc, hμ⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa archMeasure ν
  have hν_pos : 0 < (ν detOneSet).toReal :=
    ENNReal.toReal_pos (isOpen_detOneSet.measure_ne_zero ν ⟨1, by simp [detOneSet]⟩) (measure_ne_top ν _)
  refine ⟨(c : ℝ) * (ν detOneSet).toReal, mul_pos hc hν_pos, ?_⟩
  intro μN _ s W F hN hK hW hF hint
  have hmeas : Measurable fun g => (HaarQuotient.density realUnipotent μN g).toReal • weighted s W F g :=
    (measurable_density μN).ennreal_toReal.smul (measurable_weighted s hW hF)
  calc rsArchIntegral archMeasure μN s W F
      = ∫ g, weighted s W F g ∂(archMeasure.withDensity (HaarQuotient.density realUnipotent μN)) := rfl
    _ = ∫ g, (HaarQuotient.density realUnipotent μN g).toReal • weighted s W F g ∂archMeasure :=
        integral_withDensity_density μN _
    _ = (c : ℝ) • ∫ q, (HaarQuotient.density realUnipotent μN (iwasawaChart q)).toReal •
          weighted s W F (iwasawaChart q) ∂(iwasawaBase.prod ν) :=
        integral_archMeasure_eq_smul_integral_chart ν c hμ _ hmeas
    _ = (c : ℝ) • ∫ k, (∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
          (∫ x : ℝ, (HaarQuotient.density realUnipotent μN (iwasawaChart ((x, y, t), k))).toReal •
            weighted s W F (iwasawaChart ((x, y, t), k))) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) ∂ν := by
        rw [integral_prod_iwasawaBase ν _ (integrable_chart μN ν c hc hμ s hW hF hint)]
    _ = (c : ℝ) • ∫ k, (((μN unitCell).toReal)⁻¹ • ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
          weighted s W F (iwasawaChart ((0, y, t), 1) * (k : GL (Fin 2) ℝ)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) ∂ν := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        beta_reduce
        rw [← integral_smul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [← integral_smul]
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        have hx : ∀ x : ℝ, iwasawaChart ((x, y, t), k) = unipotentGL2 x * (iwasawaChart ((0, y, t), 1) * k) :=
          fun x => iwasawaChart_eq x y t k hy ht
        simp_rw [hx]
        rw [integral_x μN s W F hN, smul_mul_assoc]
    _ = (c : ℝ) • ((ν detOneSet).toReal • (((μN unitCell).toReal)⁻¹ •
          ((∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
              weighted s W F (iwasawaChart ((0, y, t), 1)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) +
            (∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
              weighted s W F (iwasawaChart ((0, y, t), 1) * diagReflection) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ))))) := by
        congr 1

        set f : GL (Fin 2) ℝ → ℂ := fun g => ((μN unitCell).toReal)⁻¹ • ∫ t in Set.Ioi (0 : ℝ),
          ∫ y in Set.Ioi (0 : ℝ), weighted s W F (iwasawaChart ((0, y, t), 1) * g) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)
          with hf_def
        have hf : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ g, f (g * k) = f g := by
          intro k hk hdet g
          simp only [hf_def]
          congr 1
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
          rw [← mul_assoc, weighted_mul_detOne s W F hK k hk hdet]
        have h1 := integral_rowIsometrySubgroup_eq_of_right_invariant ν f hf 1
        simp only [one_mul] at h1
        rw [show (∫ k, (((μN unitCell).toReal)⁻¹ • ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
            weighted s W F (iwasawaChart ((0, y, t), 1) * (k : GL (Fin 2) ℝ)) * ((((y ^ 2)⁻¹ * t⁻¹ : ℝ)) : ℂ)) ∂ν)
            = ∫ k, f (k : GL (Fin 2) ℝ) ∂ν from rfl, h1, hf_def]
        simp only [mul_one, smul_add]
    _ = ((((c : ℝ) * (ν detOneSet).toReal) / (μN unitCell).toReal : ℝ) : ℂ) *
          ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ, torusIntegrand s W F a₂ a₁ := by
        rw [torus_fold s W F hK (integrableOn_torus_coset_one μN ν c hc hμ s hN hK hW hF hint)
            (integrableOn_torus_coset_reflection μN ν c hc hμ s hN hK hW hF hint)
            (ae_integrable_torusIntegrand μN ν c hc hμ s hN hK hW hF hint), smul_smul, smul_smul,
          Complex.real_smul, div_eq_mul_inv]

private theorem exists_const_of_iwasawa :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure),
    ∃ c : ℝ, 0 < c ∧
      ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure] (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
        (_hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
        (_hW : Measurable W) (_hF : Measurable F)
        (_hint : Integrable
          (fun g : GL (Fin 2) ℝ =>
            (W g * F g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN))),
        rsArchIntegral RSCarrier.archMeasure μN s W F =
          ((c / (μN {n : realUnipotent |
              ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal : ℝ) : ℂ) *
            ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((W p * F p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0 := by
  intros
  exact rsArchIntegral_eq_of_iwasawa

end LanglandsTunnell.Converse
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal.LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal.LanglandsTunnell.Converse"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal.LanglandsTunnell"

open LanglandsTunnell.Converse in
theorem solution :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure),
    ∃ c : ℝ, 0 < c ∧
      ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure] (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
        (_hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
        (_hW : Measurable W) (_hF : Measurable F)
        (_hint : Integrable
          (fun g : GL (Fin 2) ℝ =>
            (W g * F g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN))),
        rsArchIntegral RSCarrier.archMeasure μN s W F =
          ((c / (μN {n : realUnipotent |
              ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal : ℝ) : ℂ) *
            ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((W p * F p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0 :=
  exists_const_of_iwasawa

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal.LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal.LanglandsTunnell.Converse"

end S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal (solution)
