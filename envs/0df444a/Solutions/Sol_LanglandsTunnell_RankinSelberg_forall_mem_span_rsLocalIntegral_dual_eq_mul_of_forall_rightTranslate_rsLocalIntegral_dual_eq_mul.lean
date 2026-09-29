-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_rightTranslate_rsLocalIntegral_dual_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/974e7933-45b8-5857-a239-460d08dc42a5

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_map_mk_withDensity_eq_smul_measure
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_rightTranslate_rsLocalIntegral_dual_eq_mul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped NNReal ENNReal Matrix

noncomputable section

namespace LTRSSpanK3

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem dualWhittakerFn3_translate {R : Type*} (W : GL (Fin 3) A → R) (h : GL (Fin 3) A) :
    dualWhittakerFn3 (fun x => W (x * h)) = fun X => dualWhittakerFn3 W (X * transposeInv3 h) := by
  funext X
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

theorem embedMat2_transpose (M : Matrix (Fin 2) (Fin 2) A) : embedMat2 Mᵀ = (embedMat2 M)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem transposeInv3_iotaGL (h : GL (Fin 2) A) :
    transposeInv3 (iotaGL h) = iotaGL (transposeInvN (Fin 2) h) := by
  refine Units.ext ?_
  rw [transposeInv3_coe, ← map_inv, coe_iotaGL, coe_iotaGL, coe_transposeInvN, embedMat2_transpose]

theorem det_transposeInvN (h : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) h) = (Matrix.GeneralLinearGroup.det h)⁻¹ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose,
    ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem transposeInv3_upperUnipotent3 (x : A) :
    transposeInv3 (upperUnipotent3 x 0 0 : GL (Fin 3) A) = lowerUnipotent21 (-x) := by
  have h := transposeInv3_lowerUnipotent21 (A := A) (-x)
  rw [neg_neg] at h
  rw [← h, transposeInv3_transposeInv3]

theorem longWeyl3_mul_lowerUnipotent21 (x : A) :
    (longWeyl3 : GL (Fin 3) A) * lowerUnipotent21 x = upperUnipotent3 0 x 0 * longWeyl3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, longWeyl3_coe, lowerUnipotent21_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

variable {K : Type*} [Field K]

theorem unipotent_eq_unipotentGL2 (x : K) : UnramifiedWhittaker.unipotent x = (unipotentGL2 x : GL (Fin 2) K) := by
  refine Units.ext ?_
  rw [unipotentGL2_coe]
  simp [UnramifiedWhittaker.unipotent]

theorem det_unipotentGL2 (x : K) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : GL (Fin 2) K) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem coe_inv_unipotentGL2 (x : K) :
    (((unipotentGL2 x : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, -x; 0, 1] := rfl

theorem weyl_mul_transposeInvN_unipotentGL2 {w₀p : GL (Fin 2) K}
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0]) (x : K) :
    w₀p * transposeInvN (Fin 2) (unipotentGL2 x) = unipotentGL2 (-x) * w₀p := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, coe_inv_unipotentGL2, hw₀p, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end Algebra

section LocalField

variable (v : HeightOneSpectrum (𝓞 ℚ))

def qR : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_qR : 1 < qR v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [qR]; exact_mod_cast this

theorem qR_pos : 0 < qR v := zero_lt_one.trans (one_lt_qR v)

theorem qC_eq : ((qR v : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) := by
  rw [qR, Complex.ofReal_natCast]

theorem qC_ne_zero : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  rw [← qC_eq, Complex.ofReal_ne_zero]
  exact (qR_pos v).ne'

theorem norm_eq_zpow_of_v_eq_exp (x : v.adicCompletion ℚ) (m : ℤ) (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = qR v ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    NNReal.coe_zpow, qR]
  congr 1

theorem coe_modulus_eq_norm (x : v.adicCompletion ℚ) :
    ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

theorem exists_modulus_eq_zpow {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    ∃ d : ℤ, ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = qR v ^ d := by
  have hv : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩
  rw [coe_modulus_eq_norm]
  refine norm_eq_zpow_of_v_eq_exp v x _ ?_
  rw [WithZero.exp, ofAdd_toAdd, WithZero.coe_unzero]

theorem cpow_of_eq_zpow {c : ℝ} {d : ℤ} (hc : c = qR v ^ d) (w : ℂ) :
    ((c : ℝ) : ℂ) ^ w = (Ideal.absNorm v.asIdeal : ℂ) ^ ((d : ℂ) * w) := by
  have hq0 : (0 : ℝ) ≤ qR v := (qR_pos v).le
  have hlog : Complex.log ((qR v : ℝ) : ℂ) * (d : ℂ) = ((Real.log (qR v) * d : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hq0]; push_cast; ring
  have him : (Complex.log ((qR v : ℝ) : ℂ) * (d : ℂ)).im = 0 := by
    rw [hlog, Complex.ofReal_im]
  rw [← qC_eq, Complex.cpow_mul w (by rw [him]; exact neg_lt_zero.mpr Real.pi_pos) (by rw [him]; exact Real.pi_pos.le),
    Complex.cpow_intCast, ← Complex.ofReal_zpow, ← hc]

end LocalField

section Topology

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range

theorem coe_unip_eq :
    ((unip v : Subgroup G) : Set G) = {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Mat) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Mat) 0 1) : G) : Mat) = (g : Mat)
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip : IsClosed ((unip v : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem unip_comm (x y : ↥(unip v)) : x * y = y * x := by
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  refine Subtype.ext ?_
  show (x : G) * y = y * x
  rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem sFinite_unipHaar :
    letI := localGLBorel ℚ v
    ∀ (μN : Measure ↥(unip v)) [μN.IsHaarMeasure], SFinite μN := by
  intro μN _
  haveI := locallyCompactSpace_localGL ℚ v
  haveI := secondCountableTopology_localGL v
  haveI : SigmaCompactSpace ↥(unip v) := (isClosed_unip v).sigmaCompactSpace
  infer_instance

theorem sFinite_localHaar :
    letI := localGLBorel ℚ v
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure], SFinite μ₂ := by
  intro μ₂ _
  haveI := locallyCompactSpace_localGL ℚ v
  haveI := secondCountableTopology_localGL v
  infer_instance

theorem isMulRightInvariant_unipHaar :
    letI := localGLBorel ℚ v
    ∀ (μN : Measure ↥(unip v)) [μN.IsHaarMeasure], μN.IsMulRightInvariant := by
  intro μN _
  letI : MeasurableSpace G := localGLBorel ℚ v
  refine ⟨fun x => ?_⟩
  have h : (fun y : ↥(unip v) => y * x) = fun y => x * y := funext fun y => unip_comm v y x
  rw [h]
  exact map_mul_left_eq_self μN x

theorem map_mul_right_localHaar :
    letI := localGLBorel ℚ v
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure] (h : G), Measure.map (fun g : G => g * h) μ₂ = μ₂ := by
  intro μ₂ _ h
  letI : MeasurableSpace G := localGLBorel ℚ v
  haveI : BorelSpace G := borelSpace_localGLBorel ℚ v
  haveI := locallyCompactSpace_localGL ℚ v
  haveI := secondCountableTopology_localGL v
  haveI : μ₂.IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂).1
  exact map_mul_right_eq_self μ₂ h

theorem continuous_iotaGL : Continuous fun g : G => (iotaGL g : G₃) := by
  rw [Units.continuous_iff]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  have hci : ∀ i j : Fin 2, Continuous fun g : G => ((g⁻¹ : G) : Mat) i j := fun i j =>
    (Units.continuous_coe_inv).matrix_elem i j
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Function.comp_apply, coe_iotaGL, embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hc _ _
  · have h : ∀ g : G, ((((iotaGL g : G₃)⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F) = embedMat2 ((g⁻¹ : G) : Mat) :=
      fun g => by rw [← map_inv, coe_iotaGL]
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hci _ _

theorem continuous_transposeInvN : Continuous fun g : G => transposeInvN (Fin 2) g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ fun g : G => transposeInvN (Fin 2) g) = fun g : G => (((g⁻¹ : G) : Mat))ᵀ :=
      funext fun g => coe_transposeInvN (Fin 2) g
    rw [this]
    exact Units.continuous_coe_inv.matrix_transpose
  · have : (fun g : G => (((transposeInvN (Fin 2) g)⁻¹ : G) : Mat)) = fun g : G => ((g : G) : Mat)ᵀ :=
      funext fun g => coe_inv_transposeInvN (Fin 2) g
    rw [this]
    exact Units.continuous_val.matrix_transpose

theorem continuous_of_rightInvariant {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    {α : Type*} [TopologicalSpace α]
    {f : H → α} {U : Subgroup H} (hU : IsOpen (U : Set H)) (hf : ∀ k ∈ U, ∀ g : H, f (g * k) = f g) :
    Continuous f := by
  refine (IsLocallyConstant.iff_exists_open f).mpr (fun x => ?_) |>.continuous
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' (U : Set H), hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro y hy
    have := hf (x⁻¹ * y) hy x
    rwa [mul_inv_cancel_left] at this

theorem continuous_modulus_det : Continuous fun g : G =>
    ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) := by
  have : (fun g : G => ((LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

end Topology

section QuotientInvariance

variable {G : Type*} [Group G]

theorem apply_out_mk {H : Subgroup G} {α : Type*} {Φ : G → α}
    (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) (g : G) :
    Φ (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = Φ g := by
  have h : (MulAction.orbitRel H G) (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out g :=
    Quotient.exact (Quotient.out_eq _)
  obtain ⟨x, hx⟩ := MulAction.orbitRel_apply.1 h
  rw [← hx]
  exact hinv x g

theorem measurable_comp_out [MeasurableSpace G] {H : Subgroup G} {α : Type*}
    [MeasurableSpace α] {Φ : G → α} (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => Φ q.out := by
  refine measurable_from_quotient.2 ?_
  have : (fun q : MulAction.orbitRel.Quotient H G => Φ q.out) ∘ Quotient.mk'' = Φ :=
    funext fun g => apply_out_mk hinv g
  rw [this]
  exact hΦ

theorem measurable_weight [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · simp_rw [ENNReal.tsum_eq_iSup_sum]
    refine Measurable.iSup fun s => s.measurable_fun_sum fun n _ => ?_
    exact measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet))
  · exact measurable_const

theorem measurable_density [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem map_mk_withDensity_eq_of_admissible
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1) :
    Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ) =
      Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
        (μ.withDensity (HaarQuotient.density H μH)) := by
  rw [HaarQuotient.map_mk_withDensity_eq_smul_measure μ H hH μH ρ hρ 1 hρc, one_smul]
  rfl

theorem integral_withDensity_eq_of_admissible
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1)
    (Φ : G → ℂ) (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) :
    ∫ g, Φ g ∂(μ.withDensity ρ) = ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) := by
  have hmk := map_mk_withDensity_eq_of_admissible μ H hH μH ρ hρ hρc
  set Ψ : MulAction.orbitRel.Quotient H G → ℂ := fun q => Φ q.out with hΨ
  have hΨm : Measurable Ψ := measurable_comp_out hΦ hinv
  have hΦΨ : Φ = fun g => Ψ (Quotient.mk'' g) := funext fun g => (apply_out_mk hinv g).symm
  rw [hΦΨ]
  change ∫ g, Ψ (Quotient.mk'' g) ∂_ = ∫ g, Ψ (Quotient.mk'' g) ∂_
  rw [← integral_map measurable_quotient_mk''.aemeasurable hΨm.aestronglyMeasurable,
    ← integral_map measurable_quotient_mk''.aemeasurable hΨm.aestronglyMeasurable, hmk]

theorem integrable_withDensity_iff_of_admissible
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1)
    (Φ : G → ℂ) (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) :
    Integrable Φ (μ.withDensity ρ) ↔ Integrable Φ (μ.withDensity (HaarQuotient.density H μH)) := by
  have hmk := map_mk_withDensity_eq_of_admissible μ H hH μH ρ hρ hρc
  set Ψ : MulAction.orbitRel.Quotient H G → ℂ := fun q => Φ q.out with hΨ
  have hΨm : Measurable Ψ := measurable_comp_out hΦ hinv
  have hΦΨ : Φ = Ψ ∘ (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) :=
    funext fun g => (apply_out_mk hinv g).symm
  rw [hΦΨ, ← integrable_map_measure hΨm.aestronglyMeasurable measurable_quotient_mk''.aemeasurable,
    ← integrable_map_measure hΨm.aestronglyMeasurable measurable_quotient_mk''.aemeasurable, hmk]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in

theorem map_mulRight_withDensity (μ : Measure G) (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (h : G)
    (hμh : Measure.map (fun g : G => g * h) μ = μ) :
    Measure.map (fun g : G => g * h) (μ.withDensity ρ) = μ.withDensity (fun g => ρ (g * h⁻¹)) := by
  set e : G ≃ᵐ G := MeasurableEquiv.mulRight h with he
  have hecoe : (e : G → G) = fun g : G => g * h := rfl
  have hρ' : Measurable fun g => ρ (g * h⁻¹) := hρ.comp (measurable_mul_const _)
  ext s hs
  rw [← hecoe, e.map_apply, withDensity_apply _ hs, withDensity_apply _ (e.measurable hs)]
  have h1 : (Measure.map e μ).restrict s = μ.restrict s := by rw [hecoe, hμh]
  rw [← h1, e.restrict_map, lintegral_map_equiv]
  refine lintegral_congr fun g => ?_
  show ρ g = ρ (g * h * h⁻¹)
  rw [mul_inv_cancel_right]

theorem integral_comp_mul_right_and_integrable_iff
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (Φ : G → ℂ) (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) (h : G)
    (hμh : Measure.map (fun g : G => g * h) μ = μ) :
    (∫ g, Φ (g * h) ∂(μ.withDensity (HaarQuotient.density H μH)) =
        ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH))) ∧
      (Integrable (fun g => Φ (g * h)) (μ.withDensity (HaarQuotient.density H μH)) ↔
        Integrable Φ (μ.withDensity (HaarQuotient.density H μH))) := by
  set D := HaarQuotient.density H μH with hDdef
  have hD : Measurable D := measurable_density H μH

  set ρ : G → ℝ≥0∞ := fun g => D (g * h⁻¹) with hρdef
  have hρ : Measurable ρ := hD.comp (measurable_mul_const _)
  have hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1 := by
    intro g
    show ∫⁻ x : H, D ((x : G) * g * h⁻¹) ∂μH = 1
    simp_rw [mul_assoc]
    exact HaarQuotient.lintegral_density_mul_eq_one H hH μH (g * h⁻¹)
  have hmap : Measure.map (fun g : G => g * h) (μ.withDensity D) = μ.withDensity ρ :=
    map_mulRight_withDensity μ D hD h hμh
  set e : G ≃ᵐ G := MeasurableEquiv.mulRight h with he
  have hecoe : (e : G → G) = fun g : G => g * h := rfl
  constructor
  · have h1 : ∫ g, Φ (g * h) ∂(μ.withDensity D) = ∫ g, Φ g ∂(Measure.map (fun g : G => g * h) (μ.withDensity D)) := by
      rw [← hecoe, integral_map_equiv]
      rfl
    rw [h1, hmap]
    exact integral_withDensity_eq_of_admissible μ H hH μH ρ hρ hρc Φ hΦ hinv
  · have h1 : Integrable (fun g => Φ (g * h)) (μ.withDensity D) ↔
        Integrable Φ (Measure.map (fun g : G => g * h) (μ.withDensity D)) := by
      rw [← hecoe, integrable_map_equiv]
      rfl
    rw [h1, hmap]
    exact integrable_withDensity_iff_of_admissible μ H hH μH ρ hρ hρc Φ hΦ hinv

end QuotientInvariance

section Package

def Pkg6 (q : ℂ) (γ : ℂ → ℂ) (I Id : ℂ → Prop) (val vald : ℂ → ℂ) : Prop :=
  ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
    (∀ s : ℂ, σ₂ < s.re → I s) ∧
    (∀ s : ℂ, σ₃ < s.re → Id s) ∧
    (∀ s : ℂ, σ₂ < s.re → val s = q ^ ((m : ℂ) * s) * P.eval (q ^ (-s))) ∧
    (∀ s : ℂ, σ₃ < s.re → vald s = q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s))) ∧
    (∀ s : ℂ, q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s)) = γ s * (q ^ ((m : ℂ) * (-s)) * P.eval (q ^ s)))

variable {q : ℂ}

theorem qpow_shift (hq : q ≠ 0) {n N : ℤ} (h : n ≤ N) (s : ℂ) :
    q ^ ((n : ℂ) * s) = q ^ ((N : ℂ) * s) * (q ^ (-s)) ^ (N - n).toNat := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  have h1 : (((N - n).toNat : ℕ) : ℂ) = (N : ℂ) - (n : ℂ) := by
    have : (((N - n).toNat : ℕ) : ℤ) = N - n := Int.toNat_of_nonneg (sub_nonneg.mpr h)
    exact_mod_cast this
  rw [h1]
  ring

theorem qpow_shift_neg (hq : q ≠ 0) {n N : ℤ} (h : n ≤ N) (s : ℂ) :
    q ^ ((n : ℂ) * (-s)) = q ^ ((N : ℂ) * (-s)) * (q ^ s) ^ (N - n).toNat := by
  have := qpow_shift hq h (-s)
  rwa [neg_neg] at this

theorem pkg6_zero (γ : ℂ → ℂ) {I Id : ℂ → Prop} {val vald : ℂ → ℂ}
    (hI : ∀ s, I s) (hId : ∀ s, Id s) (hv : ∀ s, val s = 0) (hvd : ∀ s, vald s = 0) :
    Pkg6 q γ I Id val vald := by
  refine ⟨0, 0, 0, 0, 0, 0, fun s _ => hI s, fun s _ => hId s, fun s _ => ?_, fun s _ => ?_, fun s => ?_⟩
  · rw [hv]; simp
  · rw [hvd]; simp
  · simp

theorem pkg6_smul (γ : ℂ → ℂ) (c : ℂ) {I₁ Id₁ I Id : ℂ → Prop} {val₁ vald₁ val vald : ℂ → ℂ}
    (h₁ : Pkg6 q γ I₁ Id₁ val₁ vald₁)
    (hI : ∀ s, I₁ s → I s) (hId : ∀ s, Id₁ s → Id s)
    (hv : ∀ s, I₁ s → val s = c * val₁ s) (hvd : ∀ s, Id₁ s → vald s = c * vald₁ s) :
    Pkg6 q γ I Id val vald := by
  obtain ⟨P, Pd, m, md, σ₂, σ₃, hi, hid, he, hed, hfe⟩ := h₁
  refine ⟨Polynomial.C c * P, Polynomial.C c * Pd, m, md, σ₂, σ₃, fun s hs => hI s (hi s hs),
    fun s hs => hId s (hid s hs), fun s hs => ?_, fun s hs => ?_, fun s => ?_⟩
  · rw [hv s (hi s hs), he s hs, Polynomial.eval_mul, Polynomial.eval_C]; ring
  · rw [hvd s (hid s hs), hed s hs, Polynomial.eval_mul, Polynomial.eval_C]; ring
  · simp only [Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination c * hfe s

theorem pkg6_add (hq : q ≠ 0) (γ : ℂ → ℂ) {I₁ Id₁ I₂ Id₂ I Id : ℂ → Prop} {val₁ vald₁ val₂ vald₂ val vald : ℂ → ℂ}
    (h₁ : Pkg6 q γ I₁ Id₁ val₁ vald₁) (h₂ : Pkg6 q γ I₂ Id₂ val₂ vald₂)
    (hI : ∀ s, I₁ s → I₂ s → I s) (hId : ∀ s, Id₁ s → Id₂ s → Id s)
    (hv : ∀ s, I₁ s → I₂ s → val s = val₁ s + val₂ s) (hvd : ∀ s, Id₁ s → Id₂ s → vald s = vald₁ s + vald₂ s) :
    Pkg6 q γ I Id val vald := by
  obtain ⟨P, Pd, m, md, σ₂, σ₃, hi, hid, he, hed, hfe⟩ := h₁
  obtain ⟨P', Pd', m', md', σ₂', σ₃', hi', hid', he', hed', hfe'⟩ := h₂
  set M : ℤ := max m m' with hM
  set Md : ℤ := max md md' with hMd
  set a : ℕ := (M - m).toNat with ha
  set a' : ℕ := (M - m').toNat with ha'
  set b : ℕ := (Md - md).toNat with hb
  set b' : ℕ := (Md - md').toNat with hb'
  refine ⟨P * Polynomial.X ^ a + P' * Polynomial.X ^ a', Pd * Polynomial.X ^ b + Pd' * Polynomial.X ^ b', M, Md,
    max σ₂ σ₂', max σ₃ σ₃', fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s => ?_⟩
  · exact hI s (hi s (lt_of_le_of_lt (le_max_left _ _) hs)) (hi' s (lt_of_le_of_lt (le_max_right _ _) hs))
  · exact hId s (hid s (lt_of_le_of_lt (le_max_left _ _) hs)) (hid' s (lt_of_le_of_lt (le_max_right _ _) hs))
  · have hs₁ : σ₂ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₂' < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have E₁ := he s hs₁
    have E₂ := he' s hs₂
    rw [qpow_shift hq (le_max_left m m' : m ≤ M) s] at E₁
    rw [qpow_shift hq (le_max_right m m' : m' ≤ M) s] at E₂
    rw [hv s (hi s hs₁) (hi' s hs₂), E₁, E₂]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  · have hs₁ : σ₃ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₃' < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have E₁ := hed s hs₁
    have E₂ := hed' s hs₂
    rw [qpow_shift hq (le_max_left md md' : md ≤ Md) s] at E₁
    rw [qpow_shift hq (le_max_right md md' : md' ≤ Md) s] at E₂
    rw [hvd s (hid s hs₁) (hid' s hs₂), E₁, E₂]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  · have E₁ := hfe s
    have E₂ := hfe' s
    rw [qpow_shift hq (le_max_left md md' : md ≤ Md) s, qpow_shift_neg hq (le_max_left m m' : m ≤ M) s] at E₁
    rw [qpow_shift hq (le_max_right md md' : md' ≤ Md) s, qpow_shift_neg hq (le_max_right m m' : m' ≤ M) s] at E₂
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination E₁ + E₂

theorem pkg6_rescale (hq : q ≠ 0) (γ : ℂ → ℂ) (d : ℤ) {I₁ Id₁ I Id : ℂ → Prop} {val₁ vald₁ val vald : ℂ → ℂ}
    (h₁ : Pkg6 q γ I₁ Id₁ val₁ vald₁)
    (hI : ∀ s, I₁ s → I s) (hId : ∀ s, Id₁ s → Id s)
    (hv : ∀ s, I₁ s → val s = q ^ ((d : ℂ) * (1 / 2 - s)) * val₁ s)
    (hvd : ∀ s, Id₁ s → vald s = q ^ ((d : ℂ) * (1 / 2 + s)) * vald₁ s) :
    Pkg6 q γ I Id val vald := by
  obtain ⟨P, Pd, m, md, σ₂, σ₃, hi, hid, he, hed, hfe⟩ := h₁
  have hsplit₁ : ∀ s : ℂ, q ^ ((d : ℂ) * (1 / 2 - s)) = q ^ ((d : ℂ) / 2) * q ^ (-((d : ℂ) * s)) := by
    intro s
    rw [← Complex.cpow_add _ _ hq]
    congr 1; ring
  have hsplit₂ : ∀ s : ℂ, q ^ ((d : ℂ) * (1 / 2 + s)) = q ^ ((d : ℂ) / 2) * q ^ ((d : ℂ) * s) := by
    intro s
    rw [← Complex.cpow_add _ _ hq]
    congr 1; ring
  have hm : ∀ s : ℂ, q ^ ((m : ℂ) * s) = q ^ ((((m - d : ℤ)) : ℂ) * s) * q ^ ((d : ℂ) * s) := by
    intro s
    rw [← Complex.cpow_add _ _ hq]
    congr 1; push_cast; ring
  have hmneg : ∀ s : ℂ, q ^ ((m : ℂ) * (-s)) = q ^ ((((m - d : ℤ)) : ℂ) * (-s)) * q ^ (-((d : ℂ) * s)) := by
    intro s
    rw [← Complex.cpow_add _ _ hq]
    congr 1; push_cast; ring
  have hmd : ∀ s : ℂ, q ^ ((((md + d : ℤ)) : ℂ) * s) = q ^ ((md : ℂ) * s) * q ^ ((d : ℂ) * s) := by
    intro s
    rw [← Complex.cpow_add _ _ hq]
    congr 1; push_cast; ring
  have hcancel : ∀ s : ℂ, q ^ ((d : ℂ) * s) * q ^ (-((d : ℂ) * s)) = 1 := by
    intro s
    rw [← Complex.cpow_add _ _ hq, add_neg_cancel, Complex.cpow_zero]
  refine ⟨Polynomial.C (q ^ ((d : ℂ) / 2)) * P, Polynomial.C (q ^ ((d : ℂ) / 2)) * Pd, m - d, md + d, σ₂, σ₃,
    fun s hs => hI s (hi s hs), fun s hs => hId s (hid s hs), fun s hs => ?_, fun s hs => ?_, fun s => ?_⟩
  · rw [hv s (hi s hs), he s hs, hsplit₁, hm, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination (q ^ ((d : ℂ) / 2) * q ^ ((((m - d : ℤ)) : ℂ) * s) * Polynomial.eval (q ^ (-s)) P) * hcancel s
  · rw [hvd s (hid s hs), hed s hs, hsplit₂, hmd, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  · have E := hfe s
    rw [hmneg] at E
    rw [hmd, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination (q ^ ((d : ℂ) / 2) * q ^ ((d : ℂ) * s)) * E +
      (γ s * q ^ ((((m - d : ℤ)) : ℂ) * (-s)) * q ^ ((d : ℂ) / 2) * Polynomial.eval (q ^ s) P) * hcancel s

end Package

section Integrand

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def δC (g : G) : ℂ :=
  ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ)

def δR (g : G) : ℝ :=
  ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ v) : ℝ≥0) : ℝ)

theorem δC_eq (g : G) : δC g = ((δR g : ℝ) : ℂ) := rfl

theorem δR_nonneg (g : G) : 0 ≤ δR g := NNReal.coe_nonneg _

theorem δR_mul (g h : G) : δR (g * h) = δR g * δR h := by
  simp only [δR, map_mul, Units.val_mul, LanglandsTunnell.TateLocal.modulus_mul, NNReal.coe_mul]

theorem δC_mul (g h : G) : δC (g * h) = δC g * δC h := by
  rw [δC_eq, δR_mul, Complex.ofReal_mul, ← δC_eq, ← δC_eq]

theorem δC_ne_zero (g : G) : δC g ≠ 0 := by
  rw [δC_eq, Complex.ofReal_ne_zero, δR, NNReal.coe_ne_zero]
  exact LanglandsTunnell.TateLocal.modulus_ne_zero (Units.ne_zero _)

theorem δC_one : δC (1 : G) = 1 := by
  simp [δC]

theorem δC_unipotentGL2 (x : F) : δC (unipotentGL2 x : G) = 1 := by
  simp [δC, det_unipotentGL2]

theorem δC_transposeInvN_mul (h : G) : δC (transposeInvN (Fin 2) h) * δC h = 1 := by
  rw [← δC_mul, ← δC_one (v := v)]
  simp only [δC, map_mul, det_transposeInvN, inv_mul_cancel, map_one]

theorem δC_mul_cpow (g h : G) (r : ℂ) : (δC (g * h)) ^ r = δC g ^ r * δC h ^ r := by
  rw [δC_mul, δC_eq, δC_eq, Complex.mul_cpow_ofReal_nonneg (δR_nonneg g) (δR_nonneg h)]

def rsPrim (W : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) (g : G) : ℂ :=
  (W (iotaGL g) * w g) * δC g ^ (s - 1 / 2)

def rsDual (w₀p : G) (W : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) (g : G) : ℂ :=
  (dualWhittakerFn3 W (iotaGL g) * (δC g * w (w₀p * transposeInvN (Fin 2) g))) * δC g ^ (s - 1 / 2)

theorem rsPrim_add_left (W₁ W₂ : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) :
    rsPrim (W₁ + W₂) w s = rsPrim W₁ w s + rsPrim W₂ w s := by
  funext g; simp only [rsPrim, Pi.add_apply]; ring

theorem rsPrim_add_right (W : LocalGL3 v → ℂ) (w₁ w₂ : G → ℂ) (s : ℂ) :
    rsPrim W (w₁ + w₂) s = rsPrim W w₁ s + rsPrim W w₂ s := by
  funext g; simp only [rsPrim, Pi.add_apply]; ring

theorem rsPrim_smul_left (c : ℂ) (W : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) :
    rsPrim (c • W) w s = fun g => c * rsPrim W w s g := by
  funext g; simp only [rsPrim, Pi.smul_apply, smul_eq_mul]; ring

theorem rsPrim_smul_right (c : ℂ) (W : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) :
    rsPrim W (c • w) s = fun g => c * rsPrim W w s g := by
  funext g; simp only [rsPrim, Pi.smul_apply, smul_eq_mul]; ring

theorem rsPrim_zero_left (w : G → ℂ) (s : ℂ) : rsPrim (0 : LocalGL3 v → ℂ) w s = fun _ => 0 := by
  funext g; simp [rsPrim]

theorem rsPrim_zero_right (W : LocalGL3 v → ℂ) (s : ℂ) : rsPrim W (0 : G → ℂ) s = fun _ => 0 := by
  funext g; simp [rsPrim]

theorem rsDual_add_left (w₀p : G) (W₁ W₂ : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) :
    rsDual w₀p (W₁ + W₂) w s = rsDual w₀p W₁ w s + rsDual w₀p W₂ w s := by
  funext g; simp only [rsDual, dualWhittakerFn3_apply, Pi.add_apply]; ring

theorem rsDual_add_right (w₀p : G) (W : LocalGL3 v → ℂ) (w₁ w₂ : G → ℂ) (s : ℂ) :
    rsDual w₀p W (w₁ + w₂) s = rsDual w₀p W w₁ s + rsDual w₀p W w₂ s := by
  funext g; simp only [rsDual, Pi.add_apply]; ring

theorem rsDual_smul_left (w₀p : G) (c : ℂ) (W : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) :
    rsDual w₀p (c • W) w s = fun g => c * rsDual w₀p W w s g := by
  funext g; simp only [rsDual, dualWhittakerFn3_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem rsDual_smul_right (w₀p : G) (c : ℂ) (W : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) :
    rsDual w₀p W (c • w) s = fun g => c * rsDual w₀p W w s g := by
  funext g; simp only [rsDual, Pi.smul_apply, smul_eq_mul]; ring

theorem rsDual_zero_left (w₀p : G) (w : G → ℂ) (s : ℂ) : rsDual w₀p (0 : LocalGL3 v → ℂ) w s = fun _ => 0 := by
  funext g; simp [rsDual, dualWhittakerFn3_apply]

theorem rsDual_zero_right (w₀p : G) (W : LocalGL3 v → ℂ) (s : ℂ) : rsDual w₀p W (0 : G → ℂ) s = fun _ => 0 := by
  funext g; simp [rsDual]

theorem rsPrim_unip_mul {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W) {w : G → ℂ}
    (hw : ∀ (x : F) (g : G), w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w g)
    (s : ℂ) (n : ↥(unip v)) (g : G) :
    rsPrim W w s ((n : G) * g) = rsPrim W w s g := by
  obtain ⟨z, hz⟩ := n.2
  have hn : (n : G) = unipotentGL2 z.toAdd := by rw [← hz]; rfl
  unfold rsPrim
  rw [hn, map_mul, iotaGL_unipotentGL2, hW, δC_mul, δC_unipotentGL2, one_mul, ← unipotent_eq_unipotentGL2, hw,
    AddChar.inv_apply, add_zero]
  calc (NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * W (iotaGL g) *
        ((NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd * w g) * δC g ^ (s - 1 / 2)
      = ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd) *
          ((W (iotaGL g) * w g) * δC g ^ (s - 1 / 2)) := by ring
    _ = (W (iotaGL g) * w g) * δC g ^ (s - 1 / 2) := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem rsDual_unip_mul {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W) {w : G → ℂ}
    (hw : ∀ (x : F) (g : G), w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w g)
    (s : ℂ) (n : ↥(unip v)) (g : G) :
    rsDual w₀p W w s ((n : G) * g) = rsDual w₀p W w s g := by
  obtain ⟨z, hz⟩ := n.2
  have hn : (n : G) = unipotentGL2 z.toAdd := by rw [← hz]; rfl
  set x : F := z.toAdd with hx
  have h1 : dualWhittakerFn3 W (iotaGL ((unipotentGL2 x : G) * g)) =
      (NumberField.StandardAddChar.psiLocal ℚ v) x * dualWhittakerFn3 W (iotaGL g) := by
    rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, map_mul, transposeInv3_mul, iotaGL_unipotentGL2,
      transposeInv3_upperUnipotent3, ← mul_assoc, longWeyl3_mul_lowerUnipotent21, mul_assoc, hW, AddChar.inv_apply,
      zero_add, neg_neg]
  have h2 : w (w₀p * transposeInvN (Fin 2) ((unipotentGL2 x : G) * g)) =
      (NumberField.StandardAddChar.psiLocal ℚ v) (-x) * w (w₀p * transposeInvN (Fin 2) g) := by
    rw [transposeInvN_mul, ← mul_assoc, weyl_mul_transposeInvN_unipotentGL2 hw₀p, mul_assoc,
      ← unipotent_eq_unipotentGL2, hw]
  unfold rsDual
  rw [hn, h1, h2, δC_mul, δC_unipotentGL2, one_mul]
  calc (NumberField.StandardAddChar.psiLocal ℚ v) x * dualWhittakerFn3 W (iotaGL g) *
        (δC g * ((NumberField.StandardAddChar.psiLocal ℚ v) (-x) * w (w₀p * transposeInvN (Fin 2) g))) *
          δC g ^ (s - 1 / 2)
      = ((NumberField.StandardAddChar.psiLocal ℚ v) x * (NumberField.StandardAddChar.psiLocal ℚ v) (-x)) *
          ((dualWhittakerFn3 W (iotaGL g) * (δC g * w (w₀p * transposeInvN (Fin 2) g))) * δC g ^ (s - 1 / 2)) := by
        ring
    _ = (dualWhittakerFn3 W (iotaGL g) * (δC g * w (w₀p * transposeInvN (Fin 2) g))) * δC g ^ (s - 1 / 2) := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

theorem measurable_rsPrim {W : LocalGL3 v → ℂ} (hWc : Continuous W) {w : G → ℂ} (hwc : Continuous w) (s : ℂ) :
    Measurable[localGLBorel ℚ v] (rsPrim W w s) := by
  letI : MeasurableSpace G := localGLBorel ℚ v
  haveI : BorelSpace G := borelSpace_localGLBorel ℚ v
  have h1 : Continuous fun g : G => W (iotaGL g) := hWc.comp (continuous_iotaGL v)
  exact ((h1.mul hwc).measurable).mul ((continuous_modulus_det v).measurable.pow_const _)

theorem measurable_rsDual (w₀p : G) {W : LocalGL3 v → ℂ} (hWc : Continuous W) {w : G → ℂ} (hwc : Continuous w)
    (s : ℂ) : Measurable[localGLBorel ℚ v] (rsDual w₀p W w s) := by
  letI : MeasurableSpace G := localGLBorel ℚ v
  haveI : BorelSpace G := borelSpace_localGLBorel ℚ v
  have h1 : Continuous fun g : G => dualWhittakerFn3 W (iotaGL g) := by
    have : (fun g : G => dualWhittakerFn3 W (iotaGL g)) =
        fun g : G => W ((longWeyl3 : G₃) * iotaGL (transposeInvN (Fin 2) g)) := by
      funext g
      rw [dualWhittakerFn3_apply, transposeInv3_iotaGL]
    rw [this]
    exact hWc.comp (continuous_const.mul ((continuous_iotaGL v).comp (continuous_transposeInvN v)))
  have h2 : Continuous fun g : G => w (w₀p * transposeInvN (Fin 2) g) :=
    hwc.comp (continuous_const.mul (continuous_transposeInvN v))
  exact ((h1.mul ((continuous_modulus_det v).mul h2)).measurable).mul
    ((continuous_modulus_det v).measurable.pow_const _)

theorem rsPrim_translate (W : LocalGL3 v → ℂ) (w : G → ℂ) (h : G) (s : ℂ) :
    rsPrim (fun x => W (x * iotaGL h)) (fun g => w (g * h)) s =
      fun g => δC h ^ (1 / 2 - s) * rsPrim W w s (g * h) := by
  funext g
  have hc : δC h ^ (1 / 2 - s) * δC h ^ (s - 1 / 2) = 1 := by
    rw [← Complex.cpow_add _ _ (δC_ne_zero h), sub_add_sub_cancel, sub_self, Complex.cpow_zero]
  simp only [rsPrim]
  rw [map_mul, δC_mul_cpow]
  linear_combination -(W (iotaGL g * iotaGL h) * w (g * h) * δC g ^ (s - 1 / 2)) * hc

theorem rsDual_translate (w₀p : G) (W : LocalGL3 v → ℂ) (w : G → ℂ) (h : G) (s : ℂ) :
    rsDual w₀p (fun x => W (x * iotaGL h)) (fun g => w (g * h)) s =
      fun g => δC h ^ (1 / 2 + s) * rsDual w₀p W w s (g * transposeInvN (Fin 2) h) := by
  funext g
  set h' : G := transposeInvN (Fin 2) h with hh'
  have hcc : δC h' * δC h = 1 := δC_transposeInvN_mul h
  have hpow : δC h' ^ (s - 1 / 2) * δC h ^ (s - 1 / 2) = 1 := by
    rw [δC_eq, δC_eq, ← Complex.mul_cpow_ofReal_nonneg (δR_nonneg _) (δR_nonneg _), ← δC_eq, ← δC_eq, hcc,
      Complex.one_cpow]
  have hsplit : δC h ^ (1 / 2 + s) = δC h ^ (s - 1 / 2) * δC h := by
    rw [show (1 : ℂ) / 2 + s = (s - 1 / 2) + 1 by ring, Complex.cpow_add _ _ (δC_ne_zero h), Complex.cpow_one]
  have h1 : dualWhittakerFn3 (fun x => W (x * iotaGL h)) (iotaGL g) = dualWhittakerFn3 W (iotaGL (g * h')) := by
    rw [dualWhittakerFn3_translate, transposeInv3_iotaGL, map_mul]
  have h2 : w₀p * transposeInvN (Fin 2) g * h = w₀p * transposeInvN (Fin 2) (g * h') := by
    rw [transposeInvN_mul, hh', transposeInvN_transposeInvN, mul_assoc]
  simp only [rsDual]
  rw [h1, h2, δC_mul_cpow, δC_mul, hsplit]
  linear_combination (-(dualWhittakerFn3 W (iotaGL (g * h')) * δC g * w (w₀p * transposeInvN (Fin 2) (g * h')) *
      δC g ^ (s - 1 / 2))) * ((δC h' ^ (s - 1 / 2) * δC h ^ (s - 1 / 2)) * hcc + hpow)

end Integrand

section Assembly

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def RSPkg [MeasurableSpace G] (ν : Measure G) (w₀p : G) (γ : ℂ → ℂ) (W : LocalGL3 v → ℂ) (w : G → ℂ) : Prop :=
  Pkg6 (Ideal.absNorm v.asIdeal : ℂ) γ (fun s => Integrable (rsPrim W w s) ν) (fun s => Integrable (rsDual w₀p W w s) ν)
    (fun s => ∫ g, rsPrim W w s g ∂ν) (fun s => ∫ g, rsDual w₀p W w s g ∂ν)

variable {v}

theorem continuous_and_law_of_mem_gl3CyclicSubspace {ψ : AddChar F ℂ} {W₀ : LocalGL3 v → ℂ}
    (hlaw : IsGL3PsiWhittakerFn ψ W₀)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₀) : Continuous W ∧ IsGL3PsiWhittakerFn ψ W := by
  obtain ⟨Uv, hUv, hWU⟩ := hsm
  have hW₀c : Continuous W₀ := continuous_of_rightInvariant hUv hWU
  refine Submodule.span_induction (p := fun f _ => Continuous f ∧ IsGL3PsiWhittakerFn ψ f) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩
    refine ⟨hW₀c.comp (continuous_id.mul continuous_const), ?_⟩
    exact (mem_gl3PsiWhittakerFnSpace_iff ψ _).mp
      (rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h ((mem_gl3PsiWhittakerFnSpace_iff ψ W₀).mpr hlaw))
  · exact ⟨continuous_const, fun x y z g => by simp⟩
  · rintro f₁ f₂ - - ⟨h₁c, h₁l⟩ ⟨h₂c, h₂l⟩
    refine ⟨h₁c.add h₂c, fun x y z g => ?_⟩
    simp only [Pi.add_apply, h₁l x y z g, h₂l x y z g]
    ring
  · rintro c f - ⟨hc, hl⟩
    refine ⟨continuous_const.mul hc, fun x y z g => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, hl x y z g]
    ring

section Closure

variable [MeasurableSpace (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))]
  (ν : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))
  (w₀p : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (γ : ℂ → ℂ)

theorem rspkg_zero_left (w : G → ℂ) : RSPkg v ν w₀p γ 0 w := by
  unfold RSPkg
  refine pkg6_zero γ (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s => ?_)
  · show Integrable (rsPrim 0 w s) ν
    rw [rsPrim_zero_left]; exact integrable_zero _ _ _
  · show Integrable (rsDual w₀p 0 w s) ν
    rw [rsDual_zero_left]; exact integrable_zero _ _ _
  · show ∫ g, rsPrim 0 w s g ∂ν = 0
    rw [rsPrim_zero_left]; exact integral_zero _ _
  · show ∫ g, rsDual w₀p 0 w s g ∂ν = 0
    rw [rsDual_zero_left]; exact integral_zero _ _

theorem rspkg_zero_right (W : LocalGL3 v → ℂ) : RSPkg v ν w₀p γ W 0 := by
  unfold RSPkg
  refine pkg6_zero γ (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s => ?_)
  · show Integrable (rsPrim W 0 s) ν
    rw [rsPrim_zero_right]; exact integrable_zero _ _ _
  · show Integrable (rsDual w₀p W 0 s) ν
    rw [rsDual_zero_right]; exact integrable_zero _ _ _
  · show ∫ g, rsPrim W 0 s g ∂ν = 0
    rw [rsPrim_zero_right]; exact integral_zero _ _
  · show ∫ g, rsDual w₀p W 0 s g ∂ν = 0
    rw [rsDual_zero_right]; exact integral_zero _ _

theorem rspkg_add_left {W₁ W₂ : LocalGL3 v → ℂ} {w : G → ℂ} (h₁ : RSPkg v ν w₀p γ W₁ w) (h₂ : RSPkg v ν w₀p γ W₂ w) :
    RSPkg v ν w₀p γ (W₁ + W₂) w := by
  unfold RSPkg at h₁ h₂ ⊢
  refine pkg6_add (qC_ne_zero v) γ h₁ h₂ (fun s i₁ i₂ => ?_) (fun s i₁ i₂ => ?_) (fun s i₁ i₂ => ?_) (fun s i₁ i₂ => ?_)
  · show Integrable (rsPrim (W₁ + W₂) w s) ν
    rw [rsPrim_add_left]; exact i₁.add i₂
  · show Integrable (rsDual w₀p (W₁ + W₂) w s) ν
    rw [rsDual_add_left]; exact i₁.add i₂
  · show ∫ g, rsPrim (W₁ + W₂) w s g ∂ν = ∫ g, rsPrim W₁ w s g ∂ν + ∫ g, rsPrim W₂ w s g ∂ν
    rw [rsPrim_add_left]; exact integral_add i₁ i₂
  · show ∫ g, rsDual w₀p (W₁ + W₂) w s g ∂ν = ∫ g, rsDual w₀p W₁ w s g ∂ν + ∫ g, rsDual w₀p W₂ w s g ∂ν
    rw [rsDual_add_left]; exact integral_add i₁ i₂

theorem rspkg_add_right {W : LocalGL3 v → ℂ} {w₁ w₂ : G → ℂ} (h₁ : RSPkg v ν w₀p γ W w₁) (h₂ : RSPkg v ν w₀p γ W w₂) :
    RSPkg v ν w₀p γ W (w₁ + w₂) := by
  unfold RSPkg at h₁ h₂ ⊢
  refine pkg6_add (qC_ne_zero v) γ h₁ h₂ (fun s i₁ i₂ => ?_) (fun s i₁ i₂ => ?_) (fun s i₁ i₂ => ?_) (fun s i₁ i₂ => ?_)
  · show Integrable (rsPrim W (w₁ + w₂) s) ν
    rw [rsPrim_add_right]; exact i₁.add i₂
  · show Integrable (rsDual w₀p W (w₁ + w₂) s) ν
    rw [rsDual_add_right]; exact i₁.add i₂
  · show ∫ g, rsPrim W (w₁ + w₂) s g ∂ν = ∫ g, rsPrim W w₁ s g ∂ν + ∫ g, rsPrim W w₂ s g ∂ν
    rw [rsPrim_add_right]; exact integral_add i₁ i₂
  · show ∫ g, rsDual w₀p W (w₁ + w₂) s g ∂ν = ∫ g, rsDual w₀p W w₁ s g ∂ν + ∫ g, rsDual w₀p W w₂ s g ∂ν
    rw [rsDual_add_right]; exact integral_add i₁ i₂

theorem rspkg_smul_left (c : ℂ) {W : LocalGL3 v → ℂ} {w : G → ℂ} (h₁ : RSPkg v ν w₀p γ W w) :
    RSPkg v ν w₀p γ (c • W) w := by
  unfold RSPkg at h₁ ⊢
  refine pkg6_smul γ c h₁ (fun s i₁ => ?_) (fun s i₁ => ?_) (fun s _ => ?_) (fun s _ => ?_)
  · show Integrable (rsPrim (c • W) w s) ν
    rw [rsPrim_smul_left]; exact i₁.const_mul c
  · show Integrable (rsDual w₀p (c • W) w s) ν
    rw [rsDual_smul_left]; exact i₁.const_mul c
  · show ∫ g, rsPrim (c • W) w s g ∂ν = c * ∫ g, rsPrim W w s g ∂ν
    rw [rsPrim_smul_left]; exact integral_const_mul c _
  · show ∫ g, rsDual w₀p (c • W) w s g ∂ν = c * ∫ g, rsDual w₀p W w s g ∂ν
    rw [rsDual_smul_left]; exact integral_const_mul c _

theorem rspkg_smul_right (c : ℂ) {W : LocalGL3 v → ℂ} {w : G → ℂ} (h₁ : RSPkg v ν w₀p γ W w) :
    RSPkg v ν w₀p γ W (c • w) := by
  unfold RSPkg at h₁ ⊢
  refine pkg6_smul γ c h₁ (fun s i₁ => ?_) (fun s i₁ => ?_) (fun s _ => ?_) (fun s _ => ?_)
  · show Integrable (rsPrim W (c • w) s) ν
    rw [rsPrim_smul_right]; exact i₁.const_mul c
  · show Integrable (rsDual w₀p W (c • w) s) ν
    rw [rsDual_smul_right]; exact i₁.const_mul c
  · show ∫ g, rsPrim W (c • w) s g ∂ν = c * ∫ g, rsPrim W w s g ∂ν
    rw [rsPrim_smul_right]; exact integral_const_mul c _
  · show ∫ g, rsDual w₀p W (c • w) s g ∂ν = c * ∫ g, rsDual w₀p W w s g ∂ν
    rw [rsDual_smul_right]; exact integral_const_mul c _

end Closure

variable (v) in

theorem rspkg_translate {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (γ : ℂ → ℂ)
    {W : LocalGL3 v → ℂ} (hWc : Continuous W)
    (hWlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    {w : G → ℂ} (hwc : Continuous w)
    (hwlaw : ∀ (x : F) (g : G), w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w g)
    (h : G) :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure] (μN₂ : Measure ↥(unip v)) [μN₂.IsHaarMeasure],
      RSPkg v (μ₂.withDensity (HaarQuotient.density (unip v) μN₂)) w₀p γ W w →
      RSPkg v (μ₂.withDensity (HaarQuotient.density (unip v) μN₂)) w₀p γ
        (fun x => W (x * iotaGL h)) (fun g => w (g * h)) := by
  intro μ₂ _ μN₂ _ hP
  letI : MeasurableSpace G := localGLBorel ℚ v
  haveI : BorelSpace G := borelSpace_localGLBorel ℚ v
  haveI := locallyCompactSpace_localGL ℚ v
  haveI := secondCountableTopology_localGL v
  haveI : SFinite μN₂ := sFinite_unipHaar v μN₂
  haveI : SFinite μ₂ := sFinite_localHaar v μ₂
  haveI : μN₂.IsMulRightInvariant := isMulRightInvariant_unipHaar v μN₂
  set ν : Measure G := μ₂.withDensity (HaarQuotient.density (unip v) μN₂) with hν
  set h' : G := transposeInvN (Fin 2) h with hh'

  obtain ⟨d, hd⟩ := exists_modulus_eq_zpow v
    (Units.ne_zero (Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ v)ˣ))
  have hδ : ∀ z : ℂ, δC h ^ z = (Ideal.absNorm v.asIdeal : ℂ) ^ ((d : ℂ) * z) := fun z => cpow_of_eq_zpow v hd z

  have hRP : ∀ s : ℂ, (∫ g, rsPrim W w s (g * h) ∂ν = ∫ g, rsPrim W w s g ∂ν) ∧
      (Integrable (fun g => rsPrim W w s (g * h)) ν ↔ Integrable (rsPrim W w s) ν) := fun s =>
    integral_comp_mul_right_and_integrable_iff μ₂ (unip v) (isClosed_unip v) μN₂ (rsPrim W w s)
      (measurable_rsPrim hWc hwc s) (fun x g => rsPrim_unip_mul hWlaw hwlaw s x g) h (map_mul_right_localHaar v μ₂ h)
  have hRD : ∀ s : ℂ, (∫ g, rsDual w₀p W w s (g * h') ∂ν = ∫ g, rsDual w₀p W w s g ∂ν) ∧
      (Integrable (fun g => rsDual w₀p W w s (g * h')) ν ↔ Integrable (rsDual w₀p W w s) ν) := fun s =>
    integral_comp_mul_right_and_integrable_iff μ₂ (unip v) (isClosed_unip v) μN₂ (rsDual w₀p W w s)
      (measurable_rsDual w₀p hWc hwc s) (fun x g => rsDual_unip_mul hw₀p hWlaw hwlaw s x g) h'
      (map_mul_right_localHaar v μ₂ h')
  unfold RSPkg at hP ⊢
  refine pkg6_rescale (qC_ne_zero v) γ d hP (fun s i₁ => ?_) (fun s i₁ => ?_) (fun s _ => ?_) (fun s _ => ?_)
  · show Integrable (rsPrim (fun x => W (x * iotaGL h)) (fun g => w (g * h)) s) ν
    rw [rsPrim_translate]
    exact ((hRP s).2.mpr i₁).const_mul _
  · show Integrable (rsDual w₀p (fun x => W (x * iotaGL h)) (fun g => w (g * h)) s) ν
    rw [rsDual_translate]
    exact ((hRD s).2.mpr i₁).const_mul _
  · show ∫ g, rsPrim (fun x => W (x * iotaGL h)) (fun g => w (g * h)) s g ∂ν =
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((d : ℂ) * (1 / 2 - s)) * ∫ g, rsPrim W w s g ∂ν
    rw [rsPrim_translate, integral_const_mul, (hRP s).1, hδ]
  · show ∫ g, rsDual w₀p (fun x => W (x * iotaGL h)) (fun g => w (g * h)) s g ∂ν =
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((d : ℂ) * (1 / 2 + s)) * ∫ g, rsDual w₀p W w s g ∂ν
    rw [rsDual_translate, integral_const_mul, (hRD s).1, hδ]

variable (v) in

theorem main
    (W₃base : LocalGL3 v → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W₃base (g * k) = W₃base g)
    (w₂base : G → ℂ)
    (hw₂law : ∀ (x : F) (g : G),
      w₂base (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w₂base g)
    (hw₂sm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w₂base (g * k) = w₂base g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (γ : ℂ → ℂ) :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure] (μN₂ : Measure ↥(unip v)) [μN₂.IsHaarMeasure],
      (∀ g₃ : LocalGL3 v, RSPkg v (μ₂.withDensity (HaarQuotient.density (unip v) μN₂)) w₀p γ
        (fun x => W₃base (x * g₃)) w₂base) →
      ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        RSPkg v (μ₂.withDensity (HaarQuotient.density (unip v) μN₂)) w₀p γ W₃ w₂ := by
  intro μ₂ _ μN₂ _ hbase w₂ hw₂ W₃ hW₃
  letI : MeasurableSpace G := localGLBorel ℚ v
  haveI : BorelSpace G := borelSpace_localGLBorel ℚ v
  set ν : Measure G := μ₂.withDensity (HaarQuotient.density (unip v) μN₂) with hν

  obtain ⟨U₂, hU₂, hwU⟩ := hw₂sm
  have hw₂c : Continuous w₂base := continuous_of_rightInvariant hU₂ hwU
  have hreg : ∀ W ∈ gl3CyclicSubspace W₃base,
      Continuous W ∧ IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W := fun W hW =>
    continuous_and_law_of_mem_gl3CyclicSubspace hW₃law hW₃sm hW

  have step1 : ∀ W ∈ gl3CyclicSubspace W₃base, RSPkg v ν w₀p γ W w₂base := by
    intro W hW
    refine Submodule.span_induction (p := fun f _ => RSPkg v ν w₀p γ f w₂base) ?_ ?_ ?_ ?_ hW
    · rintro _ ⟨g₃, rfl⟩
      exact hbase g₃
    · exact rspkg_zero_left ν w₀p γ w₂base
    · rintro f₁ f₂ - - h₁ h₂
      exact rspkg_add_left ν w₀p γ h₁ h₂
    · rintro c f - hf
      exact rspkg_smul_left ν w₀p γ c hf

  have step2 : ∀ (h : G), ∀ W ∈ gl3CyclicSubspace W₃base, RSPkg v ν w₀p γ W (fun g => w₂base (g * h)) := by
    intro h W hW
    set W' : LocalGL3 v → ℂ := fun x => W (x * (iotaGL h)⁻¹) with hW'def
    have hW' : W' ∈ gl3CyclicSubspace W₃base := gl3AmbientRightTranslate_mem_gl3CyclicSubspace W₃base (iotaGL h)⁻¹ hW
    have hWeq : (fun x => W' (x * iotaGL h)) = W := by
      funext x
      simp only [hW'def, mul_inv_cancel_right]
    rw [← hWeq]
    exact rspkg_translate v hw₀p γ (hreg W' hW').1 (hreg W' hW').2 hw₂c hw₂law h μ₂ μN₂ (step1 W' hW')

  revert W₃ hW₃
  refine Submodule.span_induction (p := fun f _ => ∀ W₃ ∈ gl3CyclicSubspace W₃base, RSPkg v ν w₀p γ W₃ f)
    ?_ ?_ ?_ ?_ hw₂
  · rintro _ ⟨h, rfl⟩ W₃ hW₃
    exact step2 h W₃ hW₃
  · intro W₃ _
    exact rspkg_zero_right ν w₀p γ W₃
  · rintro f₁ f₂ - - h₁ h₂ W₃ hW₃
    exact rspkg_add_right ν w₀p γ (h₁ W₃ hW₃) (h₂ W₃ hW₃)
  · rintro c f - hf W₃ hW₃
    exact rspkg_smul_right ν w₀p γ c (hf W₃ hW₃)

end Assembly

end LTRSSpanK3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_rightTranslate_rsLocalIntegral_dual_eq_mul.LTRSSpanK3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_rightTranslate_rsLocalIntegral_dual_eq_mul.LTRSSpanK3"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)

    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂sm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)

    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (γ : ℂ → ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],

      (∀ g₃ : LocalGL3 p,
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃base (iotaGL g * g₃) * w₂base g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂base (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃base (iotaGL g * g₃)) w₂base =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂base (w₀p * transposeInvN (Fin 2) g)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              γ s * ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)))) →

      ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂ =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              γ s * ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by
  intro μ₂ _ μN₂ _ hbase w₂ hw₂ W₃ hW₃
  exact LTRSSpanK3.main p W₃base hW₃law hW₃sm w₂base hw₂law hw₂sm w₀p hw₀p γ μ₂ μN₂ hbase w₂ hw₂ W₃ hW₃

end S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_rightTranslate_rsLocalIntegral_dual_eq_mul
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_rightTranslate_rsLocalIntegral_dual_eq_mul (solution)
