-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f68b3127-241b-5ad5-85fe-f9d22c7d8025

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero
import Theorems.Thm_HaarQuotient_exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 1600000

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped NNReal ENNReal Matrix

noncomputable section

namespace ExistGlobRS

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

end Assembly

end ExistGlobRS
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation.ExistGlobRS"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation.ExistGlobRS"

namespace ExistGlob

theorem analyticOnNhd_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) : AnalyticOnNhd ℂ f Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr hf

theorem eq_of_eqOn_halfPlane {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → f s = g s) : f = g := by
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz : ((σ + 1 : ℝ) : ℂ) ∈ {s : ℂ | σ < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith
  have hev : f =ᶠ[nhds ((σ + 1 : ℝ) : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun s hs => h s hs)
  have := (analyticOnNhd_of_differentiable hf).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_of_differentiable hg) isPreconnected_univ (Set.mem_univ _) hev
  exact funext fun s => this (Set.mem_univ s)

theorem eq_zero_of_mul_eq_zero_of_ne {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ s, f s * g s = 0) (hg0 : ∃ s, g s ≠ 0) : ∀ s, f s = 0 := by
  rcases (analyticOnNhd_of_differentiable hf).eq_zero_or_eq_zero_of_mul_eq_zero
      (analyticOnNhd_of_differentiable hg) (fun z _ => hfg z) isPreconnected_univ with h | h
  · exact fun s => h s (Set.mem_univ s)
  · obtain ⟨s, hs⟩ := hg0; exact absurd (h s (Set.mem_univ s)) hs

theorem differentiable_cpow_mul (q : ℂ) (hq : q ≠ 0) (c : ℂ) : Differentiable ℂ fun s : ℂ => q ^ (c * s) :=
  (differentiable_id.const_mul c).const_cpow (Or.inl hq)

theorem differentiable_cpow_neg (q : ℂ) (hq : q ≠ 0) : Differentiable ℂ fun s : ℂ => q ^ (-s) :=
  differentiable_id.neg.const_cpow (Or.inl hq)

theorem differentiable_cpow_id (q : ℂ) (hq : q ≠ 0) : Differentiable ℂ fun s : ℂ => q ^ s :=
  differentiable_id.const_cpow (Or.inl hq)

theorem differentiable_eval_cpow_neg (q : ℂ) (hq : q ≠ 0) (P : Polynomial ℂ) :
    Differentiable ℂ fun s : ℂ => P.eval (q ^ (-s)) :=
  P.differentiable.comp (differentiable_cpow_neg q hq)

theorem differentiable_eval_cpow (q : ℂ) (hq : q ≠ 0) (P : Polynomial ℂ) :
    Differentiable ℂ fun s : ℂ => P.eval (q ^ s) :=
  P.differentiable.comp (differentiable_cpow_id q hq)

theorem differentiable_comp_neg {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ fun s : ℂ => f (-s) :=
  hf.comp differentiable_neg

theorem exists_eval_cpow_neg_ne_zero (N : ℕ) (hN : 1 < N) (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ s : ℂ, Q.eval (((N : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  by_contra h
  push Not at h
  apply hQ
  apply Polynomial.eq_zero_of_infinite_isRoot

  have hsub : Set.range (fun n : ℕ => (((N : ℕ) : ℂ) ^ (-((n : ℕ) : ℂ)))) ⊆ {x | Q.IsRoot x} := by
    rintro x ⟨n, rfl⟩
    exact h n
  refine Set.Infinite.mono hsub (Set.infinite_range_of_injective ?_)
  intro a b hab
  simp only at hab
  rw [Complex.cpow_neg, Complex.cpow_neg, inv_inj, Complex.cpow_natCast, Complex.cpow_natCast] at hab
  have hN' : 1 < ((N : ℕ) : ℝ) := by exact_mod_cast hN
  have habs : ((N : ℝ)) ^ a = ((N : ℝ)) ^ b := by
    have := congrArg (‖·‖) hab
    simpa [Complex.norm_natCast] using this
  exact (pow_right_injective₀ (by positivity) hN'.ne') habs

theorem exists_eval_cpow_ne_zero (N : ℕ) (hN : 1 < N) (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ s : ℂ, Q.eval (((N : ℕ) : ℂ) ^ s) ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_eval_cpow_neg_ne_zero N hN Q hQ
  exact ⟨-s, hs⟩

theorem exists_lt_re_and_eval_cpow_neg_ne_zero (N : ℕ) (hN : 1 < N) (Q : Polynomial ℂ) (hQ : Q ≠ 0) (σ : ℝ) :
    ∃ s : ℂ, σ < s.re ∧ Q.eval (((N : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  by_contra h
  push Not at h
  apply hQ
  apply Polynomial.eq_zero_of_infinite_isRoot
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt σ
  have hsub : Set.range (fun n : ℕ => (((N : ℕ) : ℂ) ^ (-(((n + n₀ : ℕ) : ℂ))))) ⊆ {x | Q.IsRoot x} := by
    rintro x ⟨n, rfl⟩
    refine h _ ?_
    simp only [Complex.natCast_re]
    push_cast
    linarith
  refine Set.Infinite.mono hsub (Set.infinite_range_of_injective ?_)
  intro a b hab
  simp only at hab
  rw [Complex.cpow_neg, Complex.cpow_neg, inv_inj, Complex.cpow_natCast, Complex.cpow_natCast] at hab
  have hN' : 1 < ((N : ℕ) : ℝ) := by exact_mod_cast hN
  have habs : ((N : ℝ)) ^ (a + n₀) = ((N : ℝ)) ^ (b + n₀) := by
    have := congrArg (‖·‖) hab
    simpa [Complex.norm_natCast] using this
  have := pow_right_injective₀ (by positivity) hN'.ne' habs
  omega

theorem exists_lt_re_and_eval_cpow_ne_zero (N : ℕ) (hN : 1 < N) (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ s : ℂ, Q.eval (((N : ℕ) : ℂ) ^ s) ≠ 0 := exists_eval_cpow_ne_zero N hN Q hQ

theorem core_fixed (N : ℕ) (hN : 1 < N)
    (M Md Λ₀ Ψ₀ Ψd₀ Λ Ψ Ψd : ℂ → ℂ)

    (hΛ₀ : Differentiable ℂ Λ₀) (σ₀ : ℝ) (hu₀ : ∀ s : ℂ, σ₀ < s.re → Λ₀ s = M s * Ψ₀ s)
    (σ₀' : ℝ) (hd₀ : ∀ s : ℂ, σ₀' < s.re → Λ₀ (-s) = Md s * Ψd₀ s)
    (hnz : ∀ σ' : ℝ, ∃ s : ℂ, σ' < s.re ∧ Λ₀ s ≠ 0)
    (P₀ Pd₀ Q₀ Qd₀ : Polynomial ℂ) (m₀ md₀ : ℤ) (τ₂ τ₃ : ℝ) (hP₀ : P₀ ≠ 0) (hQd₀ : Qd₀ ≠ 0)
    (hc3₀ : ∀ s : ℂ, τ₂ < s.re →
      Ψ₀ s * Q₀.eval (((N : ℕ) : ℂ) ^ (-s)) = ((N : ℕ) : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval (((N : ℕ) : ℂ) ^ (-s)))
    (hc4₀ : ∀ s : ℂ, τ₃ < s.re →
      Ψd₀ s * Qd₀.eval (((N : ℕ) : ℂ) ^ (-s)) = ((N : ℕ) : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval (((N : ℕ) : ℂ) ^ (-s)))

    (hΛ : Differentiable ℂ Λ) (σ : ℝ) (hu : ∀ s : ℂ, σ < s.re → Λ s = M s * Ψ s)
    (σ' : ℝ) (hd : ∀ s : ℂ, σ' < s.re → Λ (-s) = Md s * Ψd s)
    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ) (hQ : Q ≠ 0) (hQd : Qd ≠ 0)
    (hc3 : ∀ s : ℂ, σ₂ < s.re →
      Ψ s * Q.eval (((N : ℕ) : ℂ) ^ (-s)) = ((N : ℕ) : ℂ) ^ ((m : ℂ) * s) * P.eval (((N : ℕ) : ℂ) ^ (-s)))
    (hc4 : ∀ s : ℂ, σ₃ < s.re →
      Ψd s * Qd.eval (((N : ℕ) : ℂ) ^ (-s)) = ((N : ℕ) : ℂ) ^ ((md : ℂ) * s) * Pd.eval (((N : ℕ) : ℂ) ^ (-s)))

    (R₁ R₂ : Polynomial ℂ) (r : ℤ)
    (hE3 : ∀ s : ℂ,
      R₂.eval (((N : ℕ) : ℂ) ^ s) * (((N : ℕ) : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval (((N : ℕ) : ℂ) ^ (-s))) *
          Q₀.eval (((N : ℕ) : ℂ) ^ s) =
        (R₁.eval (((N : ℕ) : ℂ) ^ s) * ((N : ℕ) : ℂ) ^ ((r : ℂ) * s)) *
          (((N : ℕ) : ℂ) ^ ((m₀ : ℂ) * (-s)) * P₀.eval (((N : ℕ) : ℂ) ^ s)) * Qd₀.eval (((N : ℕ) : ℂ) ^ (-s))) :
    ∀ s : ℂ,
      R₂.eval (((N : ℕ) : ℂ) ^ s) * (((N : ℕ) : ℂ) ^ ((md : ℂ) * s) * Pd.eval (((N : ℕ) : ℂ) ^ (-s))) *
          Q.eval (((N : ℕ) : ℂ) ^ s) =
        (R₁.eval (((N : ℕ) : ℂ) ^ s) * ((N : ℕ) : ℂ) ^ ((r : ℂ) * s)) *
          (((N : ℕ) : ℂ) ^ ((m : ℂ) * (-s)) * P.eval (((N : ℕ) : ℂ) ^ s)) * Qd.eval (((N : ℕ) : ℂ) ^ (-s)) := by
  set q : ℂ := ((N : ℕ) : ℂ) with hqdef
  have hq : q ≠ 0 := by rw [hqdef]; exact_mod_cast (show N ≠ 0 by omega)

  have dM : ∀ (c : ℂ), Differentiable ℂ fun s : ℂ => q ^ (c * s) := fun c => differentiable_cpow_mul q hq c
  have dX : ∀ (P : Polynomial ℂ), Differentiable ℂ fun s : ℂ => P.eval (q ^ (-s)) :=
    fun P => differentiable_eval_cpow_neg q hq P
  have dY : ∀ (P : Polynomial ℂ), Differentiable ℂ fun s : ℂ => P.eval (q ^ s) :=
    fun P => differentiable_eval_cpow q hq P
  have dΛn : Differentiable ℂ fun s : ℂ => Λ (-s) := differentiable_comp_neg hΛ
  have dΛ₀n : Differentiable ℂ fun s : ℂ => Λ₀ (-s) := differentiable_comp_neg hΛ₀
  have hqpow : ∀ t : ℂ, q ^ t ≠ 0 := fun t h => hq ((Complex.cpow_eq_zero_iff q t).mp h).1
  have dMn : ∀ (c : ℂ), Differentiable ℂ fun s : ℂ => q ^ (c * -s) :=
    fun c => (differentiable_id.neg.const_mul c).const_cpow (Or.inl hq)

  have hQ₀ : Q₀ ≠ 0 := by
    intro hQ0
    obtain ⟨s, hs, hne⟩ := exists_lt_re_and_eval_cpow_neg_ne_zero N hN P₀ hP₀ τ₂
    have h := hc3₀ s hs
    rw [hQ0, Polynomial.eval_zero, mul_zero] at h
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact hqpow _ h1
    · exact hne h1

  have E1 : (fun s : ℂ => Λ s * (q ^ ((m₀ : ℂ) * s) * P₀.eval (q ^ (-s))) * Q.eval (q ^ (-s)))
      = (fun s : ℂ => Λ₀ s * (q ^ ((m : ℂ) * s) * P.eval (q ^ (-s))) * Q₀.eval (q ^ (-s))) := by
    refine eq_of_eqOn_halfPlane ((hΛ.mul ((dM _).mul (dX _))).mul (dX _))
      ((hΛ₀.mul ((dM _).mul (dX _))).mul (dX _)) (max (max σ σ₀) (max τ₂ σ₂)) ?_
    intro s hs
    rw [max_lt_iff, max_lt_iff, max_lt_iff] at hs
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hs
    rw [hu s h1, hu₀ s h2, ← hc3 s h4, ← hc3₀ s h3]; ring

  have E2 : (fun s : ℂ => Λ (-s) * (q ^ ((md₀ : ℂ) * s) * Pd₀.eval (q ^ (-s))) * Qd.eval (q ^ (-s)))
      = (fun s : ℂ => Λ₀ (-s) * (q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s))) * Qd₀.eval (q ^ (-s))) := by
    refine eq_of_eqOn_halfPlane ((dΛn.mul ((dM _).mul (dX _))).mul (dX _))
      ((dΛ₀n.mul ((dM _).mul (dX _))).mul (dX _)) (max (max σ' σ₀') (max τ₃ σ₃)) ?_
    intro s hs
    rw [max_lt_iff, max_lt_iff, max_lt_iff] at hs
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hs
    rw [hd s h1, hd₀ s h2, ← hc4 s h4, ← hc4₀ s h3]; ring

  set G : ℂ → ℂ := fun s =>
    R₂.eval (q ^ s) * (q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s))) * Q.eval (q ^ s) -
      (R₁.eval (q ^ s) * q ^ ((r : ℂ) * s)) * (q ^ ((m : ℂ) * (-s)) * P.eval (q ^ s)) * Qd.eval (q ^ (-s)) with hG
  have dG : Differentiable ℂ G := by
    rw [hG]
    exact (((dY R₂).mul ((dM _).mul (dX Pd))).mul (dY Q)).sub
      ((((dY R₁).mul (dM _)).mul ((dMn _).mul (dY P))).mul (dX Qd))

  have key : ∀ s : ℂ, (G s * Q₀.eval (q ^ s) * Qd₀.eval (q ^ (-s))) * Λ₀ (-s) = 0 := by
    intro s
    have e1 := congrFun E1 (-s)
    have e2 := congrFun E2 s
    have e3 := hE3 s
    simp only [neg_neg] at e1
    simp only [hG]
    linear_combination (-(R₂.eval (q ^ s) * Q.eval (q ^ s) * Q₀.eval (q ^ s))) * e2
      + (Q.eval (q ^ s) * Λ (-s) * Qd.eval (q ^ (-s))) * e3
      + (R₁.eval (q ^ s) * q ^ ((r : ℂ) * s) * Qd₀.eval (q ^ (-s)) * Qd.eval (q ^ (-s))) * e1

  have hΛ₀n0 : ∃ s : ℂ, Λ₀ (-s) ≠ 0 := by
    obtain ⟨s, -, hs⟩ := hnz 0
    exact ⟨-s, by rwa [neg_neg]⟩
  have step1 := eq_zero_of_mul_eq_zero_of_ne (((dG.mul (dY Q₀)).mul (dX Qd₀))) dΛ₀n key hΛ₀n0
  have step2 := eq_zero_of_mul_eq_zero_of_ne (dG.mul (dY Q₀)) (dX Qd₀) step1
    (exists_eval_cpow_neg_ne_zero N hN Qd₀ hQd₀)
  have step3 := eq_zero_of_mul_eq_zero_of_ne dG (dY Q₀) step2 (exists_eval_cpow_ne_zero N hN Q₀ hQ₀)
  intro s
  have := step3 s
  simp only [hG] at this
  exact sub_eq_zero.mp this

theorem exists_lt_re_and_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : ∃ z, f z ≠ 0) (b : ℝ) :
    ∃ s : ℂ, b < s.re ∧ f s ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨z, hz⟩ := h
  have := eq_of_eqOn_halfPlane hf (differentiable_const (0 : ℂ)) b (fun s hs => hc s hs)
  exact hz (congrFun this z)

end ExistGlob
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation.ExistGlobRS"

namespace SS1VForm

section Generic

variable {G : Type*} [Group G]

theorem translate_mem_span (f : G → ℂ) (h : G) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    (fun g : G => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : G => (W₁ + W₂) (g * h)) = (fun g : G => W₁ (g * h)) + fun g : G => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : G => (a • W) (g * h)) = a • fun g : G => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem span_le_span_of_mem (f W₀ : G → ℂ)
    (h₀ : f ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h'))) :
    Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) ≤
      Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h')) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span W₀ h h₀

theorem law_of_mem_span (f : G → ℂ) (a : G) (χ : ℂ) (hf : ∀ g : G, f (a * g) = χ * f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∀ g : G, W (a * g) = χ * W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      intro g
      show f (a * g * h') = χ * f (g * h')
      rw [mul_assoc, hf]
  | zero => intro g; simp
  | add W₁ W₂ _ _ h₁ h₂ => intro g; simp only [Pi.add_apply, h₁ g, h₂ g]; ring
  | smul c W _ h₁ => intro g; simp only [Pi.smul_apply, smul_eq_mul, h₁ g]; ring

variable [TopologicalSpace G] [ContinuousMul G]

theorem exists_open_stabilizer_of_mem_span (f : G → ℂ) (K : Subgroup G) (hK : IsOpen (K : Set G))
    (hf : ∀ k ∈ K, ∀ g : G, f (g * k) = f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set G) := by
          ext k
          simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            SetLike.mem_coe]
        rw [hset]
        exact hK.preimage hc
      · intro k hk g
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk
        show f (g * k * h) = f (g * h)
        rw [show g * k * h = g * h * (h⁻¹ * k * h) by simp only [mul_assoc, mul_inv_cancel_left]]
        exact hf _ hk (g * h)
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, hW₁⟩ := h₁
      obtain ⟨U₂, hU₂, hW₂⟩ := h₂
      refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
      · intro k hk g
        rw [Subgroup.mem_inf] at hk
        simp only [Pi.add_apply, hW₁ k hk.1 g, hW₂ k hk.2 g]
  | smul c W _ h₁ =>
      obtain ⟨U, hU, hWU⟩ := h₁
      exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hWU k hk g]⟩

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation.ExistGlobRS"

end SS1VForm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation.ExistGlobRS"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

section AssemblyLemmas

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem rsLocalIntegral_eq_integral_rsPrim [MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range)
    (W₃ : LocalGL3 p → ℂ) (w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (s : ℂ) :
    RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
      s (fun g => W₃ (iotaGL g)) w₂ =
    ∫ g, ExistGlobRS.rsPrim W₃ w₂ s g ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := rfl

theorem rsLocalIntegral_eq_integral_rsDual [MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (W₃ : LocalGL3 p → ℂ) (w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (s : ℂ) :
    RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
      s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
          w₂ (w₀p * transposeInvN (Fin 2) g)) =
    ∫ g, ExistGlobRS.rsDual w₀p W₃ w₂ s g ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := rfl

end AssemblyLemmas
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation.ExistGlobRS"

open scoped Classical in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃base,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))

    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (ωV : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ωV z : ℂˣ) : ℂ) * w₂base g)

    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

    (hGlob :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∃ (M Md : ℂ → ℂ) (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)),
          IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
              (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ∧

          (∃ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
            ∃ W₃ ∈ gl3CyclicSubspace W₃base,
              ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (σ : ℝ),
                (∀ s : ℂ, σ < s.re → rsGlobalIntegral D s φ Θ = M s *
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                    (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                    s (fun g => W₃ (iotaGL g)) w₂) ∧
                (∀ σ' : ℝ, ∃ s : ℂ, σ' < s.re ∧ rsGlobalIntegral D s φ Θ ≠ 0) ∧

                ∃ (P₀ Pd₀ Q₀ Qd₀ : Polynomial ℂ) (m₀ md₀ : ℤ) (σ₂ σ₃ : ℝ), P₀ ≠ 0 ∧ Qd₀ ≠ 0 ∧
                (∀ s : ℂ, σ₂ < s.re →
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                      s (fun g => W₃ (iotaGL g)) w₂ * Q₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
                (∀ s : ℂ, σ₃ < s.re →
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                      s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
                      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) *
                      Qd₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    (Ideal.absNorm p.asIdeal : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) ∧

          ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
            ∀ W₃ ∈ gl3CyclicSubspace W₃base,
              ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
                Differentiable ℂ (fun s : ℂ => rsGlobalIntegral D s φ Θ) ∧
                (∀ s : ℂ, rsGlobalIntegral (transposeInvN (Fin 2) ⁻¹' D) (1 + s)
                    (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ) = rsGlobalIntegral D (-s) φ Θ) ∧
                (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → rsGlobalIntegral D s φ Θ = M s *
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                    (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                    s (fun g => W₃ (iotaGL g)) w₂) ∧
                (∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
                  rsGlobalIntegral (transposeInvN (Fin 2) ⁻¹' D) (1 + s)
                      (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ) = Md s *
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                    (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                    s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
                    (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
                        w₂ (w₀p * transposeInvN (Fin 2) g)))) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

          (∀ s : ℂ,
            R₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
              (R₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((r : ℂ) * s)) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  letI hms : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI hbs : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI := locallyCompactSpace_localGL ℚ p
  haveI := ExistGlobRS.secondCountableTopology_localGL p

  have hNq : 1 < Ideal.absNorm p.asIdeal := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
    exact_mod_cast this

  have hVlaw : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g :=
    fun w hw x => SS1VForm.law_of_mem_span w₂base (unipotent x) _ (hw₂law x) hw
  have hq : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := ExistGlobRS.qC_ne_zero p
  have hqpow : ∀ t : ℂ, (Ideal.absNorm p.asIdeal : ℂ) ^ t ≠ 0 :=
    fun t h => hq ((Complex.cpow_eq_zero_iff _ t).mp h).1

  have hPi3 : ∀ W ∈ gl3CyclicSubspace W₃base,
      Continuous W ∧ IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W :=
    fun W hW => ExistGlobRS.continuous_and_law_of_mem_gl3CyclicSubspace hW₃law hW₃sm hW

  have hinvP : ∀ W ∈ gl3CyclicSubspace W₃base, ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (s : ℂ) (n : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ExistGlobRS.rsPrim W w s ((n : GL (Fin 2) (p.adicCompletion ℚ)) * g) = ExistGlobRS.rsPrim W w s g :=
    fun W hW w hw s n g => ExistGlobRS.rsPrim_unip_mul (hPi3 W hW).2 (hVlaw w hw) s n g
  have hinvD : ∀ W ∈ gl3CyclicSubspace W₃base, ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (s : ℂ) (n : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ExistGlobRS.rsDual w₀p W w s ((n : GL (Fin 2) (p.adicCompletion ℚ)) * g) = ExistGlobRS.rsDual w₀p W w s g :=
    fun W hW w hw s n g => ExistGlobRS.rsDual_unip_mul hw₀p (hPi3 W hW).2 (hVlaw w hw) s n g

  by_cases hex : ∃ (μ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) (μN : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range),
      μ.IsHaarMeasure ∧ μN.IsHaarMeasure
  swap
  · exact ⟨0, 1, 0, one_ne_zero, fun μ₂ _ μN₂ _ => (hex ⟨μ₂, μN₂, ‹_›, ‹_›⟩).elim⟩
  obtain ⟨μs, μNs, hμs, hμNs⟩ := hex
  haveI := hμs
  haveI := hμNs
  haveI : μNs.IsMulRightInvariant := ExistGlobRS.isMulRightInvariant_unipHaar p μNs

  obtain ⟨Ms, Mds, Ds, -, ⟨w₀, hw₀, W₀, hW₀, φs, Θs, σs, hus, hnzs, P₀, Pd₀, Q₀, Qd₀, m₀, md₀, τ₂, τ₃, hP₀, hQd₀,
    hc3s, hc4s⟩, -⟩ := hGlob μs μNs
  obtain ⟨R₁, R₂, r, hR₂, hE3⟩ := Polynomial.exists_eval_mul_cpow_mul_eval_eq_of_ne_zero (Ideal.absNorm p.asIdeal : ℂ)
    hq P₀ Pd₀ Q₀ Qd₀ m₀ md₀ hP₀ hQd₀
  refine ⟨R₁, R₂, r, hR₂, ?_⟩
  intro μ₂ _ μN₂ _ w₂ hw₂ W₃ hW₃ P Pd Q Qd m md σ₂ σ₃ hQ hQd _hc1 _hc2 hc3 hc4
  haveI : μN₂.IsMulRightInvariant := ExistGlobRS.isMulRightInvariant_unipHaar p μN₂

  obtain ⟨M, Md, D, -, ⟨w₁, hw₁, W₁, hW₁, φ₁, Θ₁, σ₁, hu₁, hnz₁, -⟩, hreal⟩ := hGlob μ₂ μN₂
  obtain ⟨φ, Θ, hΛ, hrefl, ⟨σ, hu⟩, ⟨σ', hd⟩⟩ := hreal w₂ hw₂ W₃ hW₃
  obtain ⟨φ₀, Θ₀, hΛ₀, hrefl₀, ⟨ρ, hu₀⟩, ⟨ρ', hd₀⟩⟩ := hreal w₀ hw₀ W₀ hW₀
  obtain ⟨φ₁', Θ₁', hΛ₁', -, ⟨σ₁', hu₁'⟩, -⟩ := hreal w₁ hw₁ W₁ hW₁

  obtain ⟨c, hc0, hscale⟩ :=
    HaarQuotient.exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure (E := ℂ)
      (unipotentGL2Hom (R := p.adicCompletion ℚ)).range (ExistGlobRS.isClosed_unip p) μs μ₂ μNs μN₂
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hc0)
  have hΨ₀ : ∀ s : ℂ, (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => W₀ (iotaGL g)) w₀) s = ((c : ℝ) : ℂ) * (fun s : ℂ => RSCarrier.rsLocalIntegral μs (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μNs
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => W₀ (iotaGL g)) w₀) s := by
    intro s
    simp only []
    rw [rsLocalIntegral_eq_integral_rsPrim, rsLocalIntegral_eq_integral_rsPrim, hscale _ (hinvP W₀ hW₀ w₀ hw₀ s),
      Complex.real_smul]
  have hΨd₀ : ∀ s : ℂ, (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => dualWhittakerFn3 W₀ (iotaGL g))
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w₀ (w₀p * transposeInvN (Fin 2) g))) s = ((c : ℝ) : ℂ) * (fun s : ℂ => RSCarrier.rsLocalIntegral μs (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μNs
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => dualWhittakerFn3 W₀ (iotaGL g))
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w₀ (w₀p * transposeInvN (Fin 2) g))) s := by
    intro s
    simp only []
    rw [rsLocalIntegral_eq_integral_rsDual, rsLocalIntegral_eq_integral_rsDual, hscale _ (hinvD W₀ hW₀ w₀ hw₀ s),
      Complex.real_smul]

  have hc3₀ : ∀ s : ℂ, τ₂ < s.re →
      (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => W₀ (iotaGL g)) w₀) s * Q₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₀ : ℂ) * s) *
          (Polynomial.C ((c : ℝ) : ℂ) * P₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro s hs
    rw [hΨ₀ s, Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, hc3s s hs]; ring
  have hc4₀ : ∀ s : ℂ, τ₃ < s.re →
      (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => dualWhittakerFn3 W₀ (iotaGL g))
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w₀ (w₀p * transposeInvN (Fin 2) g))) s * Qd₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((md₀ : ℂ) * s) *
          (Polynomial.C ((c : ℝ) : ℂ) * Pd₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro s hs
    rw [hΨd₀ s, Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, hc4s s hs]; ring
  have hP₀' : Polynomial.C ((c : ℝ) : ℂ) * P₀ ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hcC) hP₀
  have hE3' : ∀ s : ℂ,
      R₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
          ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md₀ : ℂ) * s) *
            (Polynomial.C ((c : ℝ) : ℂ) * Pd₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
          Q₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
        (R₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((r : ℂ) * s)) *
          ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m₀ : ℂ) * (-s)) *
            (Polynomial.C ((c : ℝ) : ℂ) * P₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
          Qd₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro s
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination ((c : ℝ) : ℂ) * hE3 s

  have hd' : ∀ s : ℂ, σ' < s.re → (fun s : ℂ => rsGlobalIntegral D s φ Θ) (-s) = Md s * (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w₂ (w₀p * transposeInvN (Fin 2) g))) s := by
    intro s hs
    simp only []
    rw [← hrefl s]; exact hd s hs
  have hd₀' : ∀ s : ℂ, ρ' < s.re → (fun s : ℂ => rsGlobalIntegral D s φ₀ Θ₀) (-s) = Md s * (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => dualWhittakerFn3 W₀ (iotaGL g))
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w₀ (w₀p * transposeInvN (Fin 2) g))) s := by
    intro s hs
    simp only []
    rw [← hrefl₀ s]; exact hd₀ s hs

  have hnz₀ : ∀ σ'' : ℝ, ∃ s : ℂ, σ'' < s.re ∧ (fun s : ℂ => rsGlobalIntegral D s φ₀ Θ₀) s ≠ 0 := by
    intro σ''
    have h1 : ∃ z : ℂ, rsGlobalIntegral D z φ₁' Θ₁' ≠ 0 := by
      obtain ⟨z, hz, hne⟩ := hnz₁ (max σ₁ σ₁')
      rw [max_lt_iff] at hz
      refine ⟨z, ?_⟩
      rw [hu₁' z hz.2, ← hu₁ z hz.1]; exact hne
    have hprod : ∃ z : ℂ, rsGlobalIntegral D z φ₁' Θ₁' *
        (Polynomial.C ((c : ℝ) : ℂ) * P₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-z)) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hall := ExistGlob.eq_zero_of_mul_eq_zero_of_ne hΛ₁'
        (ExistGlob.differentiable_eval_cpow_neg _ hq _) hcon
        (ExistGlob.exists_eval_cpow_neg_ne_zero (Ideal.absNorm p.asIdeal) hNq _ hP₀')
      obtain ⟨z, hz⟩ := h1
      exact hz (hall z)
    obtain ⟨s, hs, hne⟩ := ExistGlob.exists_lt_re_and_ne_zero
      (hΛ₁'.mul (ExistGlob.differentiable_eval_cpow_neg _ hq _)) hprod (max (max σ₁' ρ) (max τ₂ σ''))
    rw [max_lt_iff, max_lt_iff, max_lt_iff] at hs
    obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := hs
    simp only [Pi.mul_apply] at hne
    refine ⟨s, h4', ?_⟩
    have hM : M s ≠ 0 := by
      intro hM0
      apply hne
      rw [hu₁' s h1', hM0, zero_mul, zero_mul]
    have hPX : (Polynomial.C ((c : ℝ) : ℂ) * P₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ≠ 0 :=
      fun h0 => hne (by rw [h0, mul_zero])
    have hΨne : (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => W₀ (iotaGL g)) w₀) s ≠ 0 := by
      intro h0
      have h3 := hc3₀ s h3'
      rw [h0, zero_mul] at h3
      rcases mul_eq_zero.mp h3.symm with h5 | h5
      · exact hqpow _ h5
      · exact hPX h5
    simp only []
    rw [hu₀ s h2']
    exact mul_ne_zero hM hΨne

  exact ExistGlob.core_fixed (Ideal.absNorm p.asIdeal) hNq M Md
    (fun s : ℂ => rsGlobalIntegral D s φ₀ Θ₀) (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => W₀ (iotaGL g)) w₀) (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => dualWhittakerFn3 W₀ (iotaGL g))
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w₀ (w₀p * transposeInvN (Fin 2) g)))
    (fun s : ℂ => rsGlobalIntegral D s φ Θ) (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => W₃ (iotaGL g)) w₂) (fun s : ℂ => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
        s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w₂ (w₀p * transposeInvN (Fin 2) g)))
    hΛ₀ ρ hu₀ ρ' hd₀' hnz₀ (Polynomial.C ((c : ℝ) : ℂ) * P₀) (Polynomial.C ((c : ℝ) : ℂ) * Pd₀) Q₀ Qd₀ m₀ md₀ τ₂ τ₃
    hP₀' hQd₀ hc3₀ hc4₀ hΛ σ hu σ' hd' P Pd Q Qd m md σ₂ σ₃ hQ hQd hc3 hc4 R₁ R₂ r hE3'

end S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation (solution)
