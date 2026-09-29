-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/27f89077-12a9-5769-886f-6022f1ab39f1

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker
open Topology
open scoped ENNReal NNReal

noncomputable section

namespace Ws46
namespace CONVC

scoped instance : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
scoped instance : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩

private abbrev glEntries (g : GL (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j

private theorem continuousOn_matrixInv_isUnit :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_ (Continuous.matrix_adjugate continuous_id).continuousOn
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

scoped instance : LocallyCompactSpace realUnipotent := unipHomeo.locallyCompactSpace_iff.1 inferInstance
scoped instance : SecondCountableTopology realUnipotent := unipHomeo.symm.secondCountableTopology

private theorem measurable_density (μN : Measure realUnipotent) [μN.IsHaarMeasure] :
    Measurable (HaarQuotient.density realUnipotent μN) := by
  haveI := secondCountableTopology_gl_two_real
  exact measurable_haarQuotient_density realUnipotent μN

theorem bottom_row_unipotent_mul {n : GL (Fin 2) ℝ} (hn : n ∈ realUnipotent) (g : GL (Fin 2) ℝ) (j : Fin 2) :
    ((n * g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 j = (g : Matrix (Fin 2) (Fin 2) ℝ) 1 j := by
  obtain ⟨x, rfl⟩ := hn
  change (((unipotentGL2 (Multiplicative.toAdd x)) * g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 j = _
  rw [Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem bottom_row_sq_mul_rowIsometry (g : GL (Fin 2) ℝ) {κ : GL (Fin 2) ℝ} (hκ : κ ∈ rowIsometrySubgroup ℝ) :
    ((g * κ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + ((g * κ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 =
      (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 := by
  have h := hκ.2 ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1)
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  exact h

theorem upperUnit_val (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    ((upperUnit a b t ha ht : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, t] := rfl

theorem det_upperUnit (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (upperUnit a b t ha ht) : ℝˣ) : ℝ) = a * t := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnit_val, Matrix.det_fin_two_of]
  ring

theorem det_realUnipotent_mul {n : GL (Fin 2) ℝ} (hn : n ∈ realUnipotent) (g : GL (Fin 2) ℝ) :
    Matrix.GeneralLinearGroup.det (n * g) = Matrix.GeneralLinearGroup.det g := by
  obtain ⟨x, rfl⟩ := hn
  rw [map_mul]
  have : Matrix.GeneralLinearGroup.det (unipotentGL2Hom x : GL (Fin 2) ℝ) = 1 := by
    apply Units.ext
    change (((unipotentGL2 (Multiplicative.toAdd x)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    rw [unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  rw [this, one_mul]

abbrev reflGL : GL (Fin 2) ℝ := upperUnit (-1 : ℝ) 0 1 (by norm_num) one_ne_zero

theorem reflGL_mem : reflGL ∈ rowIsometrySubgroup ℝ := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [upperUnit_val, Matrix.det_fin_two_of]; simp
  · simp [upperUnit_val]

theorem det_reflGL : ((Matrix.GeneralLinearGroup.det reflGL : ℝˣ) : ℝ) = -1 := by
  rw [det_upperUnit]; ring

theorem upperUnit_mul_reflGL (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) :
    upperUnit a₁ 0 a₂ h₁ h₂ * reflGL = upperUnit (-a₁) 0 a₂ (neg_ne_zero.mpr h₁) h₂ := by
  apply Units.ext
  rw [Units.val_mul, upperUnit_val, upperUnit_val, upperUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem abs_det_of_mem {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) :
    |((Matrix.GeneralLinearGroup.det k : ℝˣ) : ℝ)| = 1 := by
  have := hk.1
  rw [Real.norm_eq_abs] at this
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact this

end Ws46.CONVC
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat.Ws46 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat.Ws46.CONVC"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat.Ws46"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat.Ws46 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat.Ws46.CONVC"

open Ws46.CONVC in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (WA WA' FA : GL (Fin 2) ℝ → ℂ) (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (P : ℝ → ℝ) (x₀ : ℝ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (e₁ e₂ cS uS : ℝ) (tS : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hφc : Continuous φ) (_hφ'c : Continuous φ')
    (_hφd : IsRapidlyDecreasingOnSiegelSets ℚ φ) (_hφ'd : IsRapidlyDecreasingOnSiegelSets ℚ φ')
    (_hφG : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (_hφ'G : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (globalPoints (𝓞 ℚ) ℚ γ * g) = φ' g)
    (_hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (_he₁ : 0 < e₁) (_he : e₁ < e₂) (_hcS : 0 < cS) (_hDm : MeasurableSet D)
    (_hDμ : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤)
    (_hDs : D ⊆ {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (_hDS : D ⊆ ⋃ t ∈ tS, (· * t) '' integralWindowedSiegelSet ℚ cS uS)
    (_hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g))
    (_hW' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g = WA' (ratArchGL2 g) * Wf' (finFactor g))
    (_hΦsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g))
    (_hFA : ∀ g : GL (Fin 2) ℝ, FA g = Complex.exp (-(Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))
    (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
      WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * WA' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ))
    (_hP0 : ∀ y : ℝ, 0 ≤ P y)
    (_hPint : ∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2)))
    (_hWfm : Measurable Wf) (_hWf'm : Measurable Wf') (_hFfm : Measurable Ff)
    (_harch : @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA ∧ @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA' ∧ Measurable P ∧
      (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, WA (n * g) * WA' (n * g) = WA g * WA' g) ∧
      (∀ κ' ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ' = 1 →
        ∀ g : GL (Fin 2) ℝ, WA (g * κ') * WA' (g * κ') = WA g * WA' g))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (_hfin :
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * (Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g) * Ff ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
          Wf g * (Wf' g * Ff g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
          Wf' (finFactor (g * placeEmbed ℚ v x)) * Ff (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g) * Ff (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
        Wf (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
          (Wf' (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
            Ff (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)))) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g)))))
    (_hsupp :
      (∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
        (∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g * (Wf' g * Ff g)‖ ≤ B₀) ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g * (Wf' g * Ff g) ≠ 0 →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)))
    :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
      ∀ (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν₀.IsHaarMeasure]
        (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
      Integrable
        (fun g : GL (Fin 2) ℝ =>
          (WA g * (WA' g * Complex.exp (-(Real.pi *
              (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
            (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  obtain ⟨hWAm, hWA'm, hPm, hN, hK⟩ := _harch
  refine ⟨max x₀ 0, fun s hs ν₀ _ μf _ μNArch _ μNFin _ => ?_⟩
  have hx₀ : x₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs0 : 0 < s.re := lt_of_le_of_lt (le_max_right _ _) hs

  set Gs : GL (Fin 2) ℝ → ℂ := fun g => Complex.exp (-(Real.pi *
      (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)) with hGs
  set f : GL (Fin 2) ℝ → ℂ := fun g => (WA g * (WA' g * Gs g)) *
      (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) with hf
  have hGc : Continuous Gs := by
    have h1 : Continuous fun g : GL (Fin 2) ℝ => (Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2)) :=
      (continuous_const.mul (((Units.continuous_val.matrix_elem 1 0).pow 2).add
        ((Units.continuous_val.matrix_elem 1 1).pow 2)))
    exact ((Complex.continuous_ofReal.comp h1).neg).cexp
  have hdetc : Continuous fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ) := by
    have h1 : (fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ)) =
        fun g : GL (Fin 2) ℝ => ((g : Matrix (Fin 2) (Fin 2) ℝ)).det :=
      funext fun g => Matrix.GeneralLinearGroup.val_det_apply g
    rw [h1]; exact Units.continuous_val.matrix_det
  have hfm : Measurable f :=
    (hWAm.mul (hWA'm.mul hGc.measurable)).mul
      ((Complex.continuous_ofReal.comp (continuous_abs.comp hdetc)).measurable.pow_const _)
  show Integrable f _
  refine ⟨hfm.aestronglyMeasurable, ?_⟩

  haveI := compactSpace_rowIsometrySubgroup
  let ν : Measure (rowIsometrySubgroup ℝ) := Measure.haar
  obtain ⟨C₀, hC₀, hmaj⟩ :=
    LanglandsTunnell.Converse.exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa μNArch ν
  have hHN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, (fun g => ‖f g‖ₑ) (n * g) = (fun g => ‖f g‖ₑ) g := by
    intro n hn g
    simp only [hf, hGs]
    rw [bottom_row_unipotent_mul hn g 0, bottom_row_unipotent_mul hn g 1, det_realUnipotent_mul hn g,
      ← mul_assoc (WA (n * g)), hN n hn g]
    congr 1
    ring
  have key := hmaj (fun g => ‖f g‖ₑ) hfm.enorm hHN

  have hdm : Measurable (HaarQuotient.density realUnipotent μNArch) := measurable_density μNArch
  unfold HasFiniteIntegral
  rw [lintegral_withDensity_eq_lintegral_mul _ hdm hfm.enorm]
  have hcomm : (fun g => (HaarQuotient.density realUnipotent μNArch * fun g => ‖f g‖ₑ) g) =
      fun g => ‖f g‖ₑ * HaarQuotient.density realUnipotent μNArch g := by
    funext g; simp only [Pi.mul_apply]; rw [mul_comm]
  rw [hcomm]
  refine lt_of_le_of_lt key ?_

  set σ : ℝ := s.re with hσ
  set G : ℝ × ℝ → ℝ≥0∞ := fun q =>
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
      (fun q => ENNReal.ofReal ((P q.1 + P (-q.1)) * q.1 ^ (σ - 2)) *
        ENNReal.ofReal (Real.exp (-(Real.pi * q.2 ^ 2)) * q.2 ^ (2 * σ - 1))) q with hG
  have hpt : ∀ (k : rowIsometrySubgroup ℝ) (q : ℝ × ℝ),
      (if h : 0 < q.1 ∧ 0 < q.2 then
          (fun g => ‖f g‖ₑ) (upperUnit (q.2 * q.1) 0 q.2 (mul_pos h.2 h.1).ne' h.2.ne' * (k : GL (Fin 2) ℝ)) *
            ENNReal.ofReal ((q.1 ^ 2)⁻¹ * q.2⁻¹)
        else 0) ≤ G q := by
    intro k q
    by_cases h : 0 < q.1 ∧ 0 < q.2
    · rw [dif_pos h]
      obtain ⟨hy, ha⟩ := h
      have hmem : q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := ⟨hy, ha⟩
      simp only [hG, Set.indicator_of_mem hmem]
      set p : GL (Fin 2) ℝ := upperUnit (q.2 * q.1) 0 q.2 (mul_pos ha hy).ne' ha.ne' with hp
      have hk := k.2

      have hWW : ‖WA (p * k) * WA' (p * k)‖ ≤ P q.1 + P (-q.1) := by
        by_cases hd : Matrix.GeneralLinearGroup.det (k : GL (Fin 2) ℝ) = 1
        · rw [hK k hk hd p, hp, _hT (q.2 * q.1) q.2 (mul_pos ha hy).ne' ha,
            show q.2 * q.1 / q.2 = q.1 by field_simp, Complex.norm_real, Real.norm_of_nonneg (_hP0 _)]
          linarith [_hP0 (-q.1)]
        · have hk1 := abs_det_of_mem hk
          have hdk : ((Matrix.GeneralLinearGroup.det (k : GL (Fin 2) ℝ) : ℝˣ) : ℝ) = -1 := by
            rcases abs_eq (zero_le_one) |>.mp hk1 with h1 | h1
            · exact absurd (Units.ext h1) hd
            · exact h1
          have hk' : reflGL⁻¹ * (k : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup ℝ :=
            Subgroup.mul_mem _ (Subgroup.inv_mem _ reflGL_mem) hk
          have hdk' : Matrix.GeneralLinearGroup.det (reflGL⁻¹ * (k : GL (Fin 2) ℝ)) = 1 := by
            apply Units.ext
            rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, det_reflGL, hdk, Units.val_one]
            norm_num
          have hsplit : p * (k : GL (Fin 2) ℝ) = (p * reflGL) * (reflGL⁻¹ * (k : GL (Fin 2) ℝ)) := by group
          rw [hsplit, hK _ hk' hdk' (p * reflGL), hp, upperUnit_mul_reflGL,
            _hT (-(q.2 * q.1)) q.2 (neg_ne_zero.mpr (mul_pos ha hy).ne') ha,
            show -(q.2 * q.1) / q.2 = -q.1 by field_simp, Complex.norm_real, Real.norm_of_nonneg (_hP0 _)]
          linarith [_hP0 q.1]
      have hGauss : ‖Gs (p * k)‖ = Real.exp (-(Real.pi * q.2 ^ 2)) := by
        simp only [hGs]
        rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, bottom_row_sq_mul_rowIsometry p hk, hp, upperUnit_val]
        congr 1
        simp
      have hdetpk : |((Matrix.GeneralLinearGroup.det (p * (k : GL (Fin 2) ℝ)) : ℝˣ) : ℝ)| = q.2 ^ 2 * q.1 := by
        rw [map_mul, Units.val_mul, abs_mul, abs_det_of_mem hk, mul_one, hp, det_upperUnit,
          abs_of_pos (mul_pos (mul_pos ha hy) ha)]
        ring
      have hpos : 0 < q.2 ^ 2 * q.1 := by positivity
      have hD : norm (((|((Matrix.GeneralLinearGroup.det (p * (k : GL (Fin 2) ℝ)) : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) =
          (q.2 ^ 2 * q.1) ^ σ := by
        rw [hdetpk, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        congr 1
        rw [hσ]; simp
      have hnf : ‖f (p * k)‖ ≤ (P q.1 + P (-q.1)) * (Real.exp (-(Real.pi * q.2 ^ 2)) * (q.2 ^ 2 * q.1) ^ σ) := by
        simp only [hf]
        rw [norm_mul, norm_mul, norm_mul, hD, hGauss]
        calc ‖WA (p * ↑k)‖ * (‖WA' (p * ↑k)‖ * Real.exp (-(Real.pi * q.2 ^ 2))) * (q.2 ^ 2 * q.1) ^ σ
            = ‖WA (p * ↑k) * WA' (p * ↑k)‖ * (Real.exp (-(Real.pi * q.2 ^ 2)) * (q.2 ^ 2 * q.1) ^ σ) := by
              rw [norm_mul]; ring
          _ ≤ (P q.1 + P (-q.1)) * (Real.exp (-(Real.pi * q.2 ^ 2)) * (q.2 ^ 2 * q.1) ^ σ) :=
              mul_le_mul_of_nonneg_right hWW (by positivity)

      have halg : (Real.exp (-(Real.pi * q.2 ^ 2)) * (q.2 ^ 2 * q.1) ^ σ) * ((q.1 ^ 2)⁻¹ * q.2⁻¹) =
          q.1 ^ (σ - 2) * (Real.exp (-(Real.pi * q.2 ^ 2)) * q.2 ^ (2 * σ - 1)) := by
        have e1 : (q.2 ^ 2 * q.1) ^ σ = q.2 ^ (2 * σ) * q.1 ^ σ := by
          rw [Real.mul_rpow (sq_nonneg _) hy.le]
          congr 1
          rw [show (q.2 ^ 2 : ℝ) = q.2 ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_mul ha.le]
          norm_num
        have e2 : q.1 ^ (σ - 2) = q.1 ^ σ * (q.1 ^ 2)⁻¹ := by
          rw [Real.rpow_sub hy, Real.rpow_two, div_eq_mul_inv]
        have e3 : q.2 ^ (2 * σ - 1) = q.2 ^ (2 * σ) * q.2⁻¹ := by
          rw [Real.rpow_sub_one ha.ne', div_eq_mul_inv]
        rw [e1, e2, e3]; ring
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
        ← ENNReal.ofReal_mul (mul_nonneg (add_nonneg (_hP0 _) (_hP0 _)) (Real.rpow_nonneg hy.le _))]
      apply ENNReal.ofReal_le_ofReal
      calc ‖f (p * ↑k)‖ * ((q.1 ^ 2)⁻¹ * q.2⁻¹)
          ≤ (P q.1 + P (-q.1)) * (Real.exp (-(Real.pi * q.2 ^ 2)) * (q.2 ^ 2 * q.1) ^ σ) * ((q.1 ^ 2)⁻¹ * q.2⁻¹) :=
            mul_le_mul_of_nonneg_right hnf (by positivity)
        _ = (P q.1 + P (-q.1)) * q.1 ^ (σ - 2) * (Real.exp (-(Real.pi * q.2 ^ 2)) * q.2 ^ (2 * σ - 1)) := by
            rw [mul_assoc, halg]; ring
    · rw [dif_neg h]
      exact bot_le
  have hG_lt : ∫⁻ q, G q ∂(volume : Measure (ℝ × ℝ)) < ⊤ := by
    have hσx : x₀ < σ := hx₀

    set g₁ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((P y + P (-y)) * y ^ (σ - 2)) with hg₁
    set g₂ : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal (Real.exp (-(Real.pi * a ^ 2)) * a ^ (2 * σ - 1)) with hg₂
    have hGeq : G = fun q : ℝ × ℝ => (Set.Ioi (0 : ℝ)).indicator g₁ q.1 * (Set.Ioi (0 : ℝ)).indicator g₂ q.2 := by
      funext q
      simp only [hG]
      by_cases h1 : q.1 ∈ Set.Ioi (0 : ℝ)
      · by_cases h2 : q.2 ∈ Set.Ioi (0 : ℝ)
        · have hm : q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := Set.mem_prod.mpr ⟨h1, h2⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
        · have hn : q ∉ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := fun h => h2 h.2
          rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem h2, mul_zero]
      · have hn : q ∉ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := fun h => h1 h.1
        rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem h1, zero_mul]
    have hPm' : Measurable g₁ := by
      simp only [hg₁]
      exact ENNReal.measurable_ofReal.comp (((hPm.add (hPm.comp measurable_neg)).mul
        (measurable_id.pow_const _)))
    have hg₂m : Measurable g₂ := by
      simp only [hg₂]
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    rw [hGeq, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
      lintegral_prod_mul (hPm'.indicator measurableSet_Ioi).aemeasurable (hg₂m.indicator measurableSet_Ioi).aemeasurable]
    refine ENNReal.mul_lt_top ?_ ?_
    ·
      have hI1 := _hPint σ hσx
      have hI2 := hI1.comp_neg
      have hb : ∀ y : ℝ, (Set.Ioi (0 : ℝ)).indicator g₁ y ≤
          ‖P y * |y| ^ (σ - 2)‖ₑ + ‖P (-y) * |-y| ^ (σ - 2)‖ₑ := by
        intro y
        by_cases hy : y ∈ Set.Ioi (0 : ℝ)
        · have hy' : (0 : ℝ) < y := hy
          rw [Set.indicator_of_mem hy]
          simp only [hg₁]
          rw [Real.enorm_eq_ofReal (mul_nonneg (_hP0 _) (Real.rpow_nonneg (abs_nonneg _) _)),
            Real.enorm_eq_ofReal (mul_nonneg (_hP0 _) (Real.rpow_nonneg (abs_nonneg _) _)),
            ← ENNReal.ofReal_add (mul_nonneg (_hP0 _) (Real.rpow_nonneg (abs_nonneg _) _))
              (mul_nonneg (_hP0 _) (Real.rpow_nonneg (abs_nonneg _) _)),
            abs_neg, abs_of_pos hy']
          apply ENNReal.ofReal_le_ofReal
          nlinarith [_hP0 y, _hP0 (-y), Real.rpow_nonneg hy'.le (σ - 2)]
        · rw [Set.indicator_of_notMem hy]; exact bot_le
      calc ∫⁻ y, (Set.Ioi (0 : ℝ)).indicator g₁ y
          ≤ ∫⁻ y, (‖P y * |y| ^ (σ - 2)‖ₑ + ‖P (-y) * |-y| ^ (σ - 2)‖ₑ) := lintegral_mono hb
        _ = (∫⁻ y, ‖P y * |y| ^ (σ - 2)‖ₑ) + ∫⁻ y, ‖P (-y) * |-y| ^ (σ - 2)‖ₑ :=
            lintegral_add_left' hI1.aestronglyMeasurable.enorm _
        _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hI1.hasFiniteIntegral, hI2.hasFiniteIntegral⟩
    ·
      have hI := integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := 2 * σ - 1) (by linarith)
      rw [lintegral_indicator measurableSet_Ioi]
      have heq : ∀ a ∈ Set.Ioi (0 : ℝ), g₂ a = ‖a ^ (2 * σ - 1) * Real.exp (-Real.pi * a ^ 2)‖ₑ := by
        intro a ha
        simp only [hg₂]
        rw [Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg (le_of_lt ha) _) (Real.exp_nonneg _))]
        congr 1
        rw [neg_mul]; ring
      rw [setLIntegral_congr_fun measurableSet_Ioi heq]
      exact hI.2
  have hνfin : ν Set.univ < ⊤ := (isCompact_univ (X := rowIsometrySubgroup ℝ)).measure_lt_top
  calc C₀ * ∫⁻ k, ∫⁻ q, (if h : 0 < q.1 ∧ 0 < q.2 then
            (fun g => ‖f g‖ₑ) (upperUnit (q.2 * q.1) 0 q.2 (mul_pos h.2 h.1).ne' h.2.ne' * (k : GL (Fin 2) ℝ)) *
              ENNReal.ofReal ((q.1 ^ 2)⁻¹ * q.2⁻¹)
          else 0) ∂(volume : Measure (ℝ × ℝ)) ∂ν
      ≤ C₀ * ∫⁻ k, ∫⁻ q, G q ∂(volume : Measure (ℝ × ℝ)) ∂ν := by
        exact mul_le_mul_right (lintegral_mono fun k => lintegral_mono fun q => hpt k q) _
    _ = C₀ * ((∫⁻ q, G q ∂(volume : Measure (ℝ × ℝ))) * ν Set.univ) := by rw [lintegral_const]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top hC₀.lt_top (ENNReal.mul_lt_top hG_lt hνfin)

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat (solution)
