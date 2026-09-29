-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0741ca0b-ff2e-59d6-b24c-6686fe5039c4

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open NumberField.AdelicLevel (diagOne)
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace RS22UnrefoldW

section LocalField

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem norm_units_pos (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : 0 < ‖(u : F)‖ :=
  norm_pos_iff.mpr u.ne_zero

scoped instance secondCountable_units : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : ℝ≥0) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem scalar_identity (r t : ℝ) (hr : 0 < r) (ht : 0 < t) (s : ℂ) :
    ((Real.sqrt (1 / r) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ s =
      ((r : ℝ) : ℂ) ^ (s - 1 / 2) * ((t : ℝ) : ℂ) ^ s := by
  have hr0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ht0 : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have htr0 : ((r * t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hr ht).ne'
  have e1 : ((Real.sqrt (1 / r) : ℝ) : ℂ) = Complex.exp ((((-Real.log r) / 2 : ℝ)) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity), one_div, Real.log_inv, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have e2 : ((r * t : ℝ) : ℂ) ^ s = Complex.exp (((Real.log r + Real.log t : ℝ) : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero htr0, ← Complex.ofReal_log (mul_pos hr ht).le, Real.log_mul hr.ne' ht.ne']
  have e4 : ((r : ℝ) : ℂ) ^ (s - 1 / 2) = Complex.exp (((Real.log r : ℝ) : ℂ) * (s - 1 / 2)) := by
    rw [Complex.cpow_def_of_ne_zero hr0, ← Complex.ofReal_log hr.le]
  have e5 : ((t : ℝ) : ℂ) ^ s = Complex.exp (((Real.log t : ℝ) : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
  rw [e1, e2, e4, e5, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end LocalField

section GL2

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL ℚ p

theorem continuous_entry (i j : Fin 2) : Continuous fun g : G => (g : Mat) i j :=
  (Units.continuous_val).matrix_elem i j

theorem continuous_row (i : Fin 2) : Continuous fun g : G => (g : Mat) i :=
  continuous_pi fun j => continuous_entry p i j

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range

theorem coe_unip_eq :
    ((unip p : Subgroup G) : Set G) = {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
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

theorem isClosed_unip : IsClosed ((unip p : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  exact ((isClosed_singleton.preimage (continuous_entry p 0 0)).inter
    ((isClosed_singleton.preimage (continuous_entry p 1 0)).inter
      (isClosed_singleton.preimage (continuous_entry p 1 1))))

theorem unip_eq_unipotentGL2 (n : unip p) : (n : G) = unipotentGL2 (((n : G) : Mat) 0 1) := by
  obtain ⟨z, hz⟩ := n.2
  rw [← hz]
  change (unipotentGL2 z.toAdd : G) = unipotentGL2 (((unipotentGL2 z.toAdd : G) : Mat) 0 1)
  have h01 : (((unipotentGL2 z.toAdd : G) : Mat) 0 1) = z.toAdd := by simp [unipotentGL2_coe]
  rw [h01]

theorem unip_comm (m n : unip p) : m * n = n * m := by
  refine Subtype.ext ?_
  change (m : G) * (n : G) = (n : G) * (m : G)
  rw [unip_eq_unipotentGL2 p m, unip_eq_unipotentGL2 p n, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem det_unipotentGL2 (x : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem row_unipotentGL2_mul (x : F) (g : G) : (((unipotentGL2 x * g : G)) : Mat) 1 = (g : Mat) 1 := by
  funext j
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]

theorem continuous_unipotentGL2 : Continuous fun y : F => (unipotentGL2 y : G) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun y : F => (unipotentGL2 y : G)) = fun y => !![1, y; 0, 1] := funext fun y => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · have h : (fun y : F => (((unipotentGL2 y : G)⁻¹ : G) : Mat)) = fun y => !![1, -y; 0, 1] :=
      funext fun y => rfl
    show Continuous fun y : F => (((unipotentGL2 y : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

def unipHomeo : F ≃ₜ (unip p) where
  toFun y := ⟨unipotentGL2 y, ⟨Multiplicative.ofAdd y, rfl⟩⟩
  invFun n := ((n : G) : Mat) 0 1
  left_inv y := by simp [unipotentGL2_coe]
  right_inv n := Subtype.ext (unip_eq_unipotentGL2 p n).symm
  continuous_toFun := (continuous_unipotentGL2 p).subtype_mk _
  continuous_invFun := (continuous_entry p 0 1).comp continuous_subtype_val

theorem unipHomeo_apply_coe (y : F) : ((unipHomeo p y : unip p) : G) = unipotentGL2 y := rfl

theorem unipHomeo_add (y y' : F) : unipHomeo p (y + y') = unipHomeo p y * unipHomeo p y' :=
  Subtype.ext (by simp [unipHomeo_apply_coe, unipotentGL2_add])

abbrev torA : Subgroup G := (diagOne (A := HeightOneSpectrum.adicCompletion ℚ p)).range

theorem coe_diagOne (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ((diagOne y : G) : Mat) = Matrix.diagonal ![(y : F), 1] := rfl

theorem det_diagOne (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne y : G) = y := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagOne, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem coe_torA_eq :
    ((torA p : Subgroup G) : Set G) = {g : G | (g : Mat) 0 1 = 0 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, rfl⟩
    simp [coe_diagOne]
  · rintro ⟨h01, h10, h11⟩
    refine ⟨Matrix.GeneralLinearGroup.det g, Units.ext ?_⟩
    have hdet : ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) = (g : Mat) 0 0 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01, h11]
      ring
    change ((diagOne (Matrix.GeneralLinearGroup.det g) : G) : Mat) = (g : Mat)
    rw [coe_diagOne, hdet]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

theorem isClosed_torA : IsClosed ((torA p : Subgroup G) : Set G) := by
  rw [coe_torA_eq]
  exact ((isClosed_singleton.preimage (continuous_entry p 0 1)).inter
    ((isClosed_singleton.preimage (continuous_entry p 1 0)).inter
      (isClosed_singleton.preimage (continuous_entry p 1 1))))

theorem torA_eq_diagOne (a : torA p) : (a : G) = diagOne (Matrix.GeneralLinearGroup.det (a : G)) := by
  obtain ⟨y, hy⟩ := a.2
  rw [← hy, det_diagOne]

theorem torA_comm (a b : torA p) : a * b = b * a := by
  refine Subtype.ext ?_
  change (a : G) * (b : G) = (b : G) * (a : G)
  obtain ⟨y, hy⟩ := a.2
  obtain ⟨y', hy'⟩ := b.2
  rw [← hy, ← hy', ← map_mul, ← map_mul, mul_comm]

theorem row_diagOne_mul (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (h : G) :
    (((diagOne y * h : G)) : Mat) 1 = (h : Mat) 1 := by
  funext j
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_diagOne]

theorem continuous_diagOne : Continuous fun y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (diagOne y : G) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ((diagOne y : G) : Mat)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_diagOne, Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · have h : (fun y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (((diagOne y : G)⁻¹ : G) : Mat)) =
        fun y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
          Matrix.diagonal ![((y⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F), 1] :=
      funext fun y => rfl
    show Continuous fun y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (((diagOne y : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first
        | exact continuous_const
        | exact Units.continuous_coe_inv
        | exact Units.continuous_val.inv₀ fun u => u.ne_zero

def torHomeo : (HeightOneSpectrum.adicCompletion ℚ p)ˣ ≃ₜ (torA p) where
  toFun y := ⟨diagOne y, ⟨y, rfl⟩⟩
  invFun a := Matrix.GeneralLinearGroup.det (a : G)
  left_inv y := det_diagOne p y
  right_inv a := Subtype.ext (torA_eq_diagOne p a).symm
  continuous_toFun := (continuous_diagOne p).subtype_mk _
  continuous_invFun := Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val

theorem torHomeo_apply_coe (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ((torHomeo p y : torA p) : G) = diagOne y :=
  rfl

theorem torHomeo_mul (y y' : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    torHomeo p (y * y') = torHomeo p y * torHomeo p y' :=
  Subtype.ext (by simp [torHomeo_apply_coe])

theorem continuous_modulus_det :
    Continuous fun g : G =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) := by
  have : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) :
      ℝ) : ℂ)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

theorem antidiag_mul_diagOne (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    w₀ * diagOne y = diagonal2 p ![1, y] * w₀ := by
  refine Units.ext ?_
  change (w₀ : Mat) * ((diagOne y : G) : Mat) = ((diagonal2 p ![1, y] : G) : Mat) * (w₀ : Mat)
  rw [hw₀, coe_diagOne, diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

theorem torusChar2_one_left (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
    (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    torusChar2 p χ ![1, y] = ((χ 1 y : ℂˣ) : ℂ) := by
  simp [torusChar2, Fin.prod_univ_two]

theorem halfModulus2_one_left (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    halfModulus2 p ![1, y] = ((Real.sqrt (1 / ‖(y : F)‖) : ℝ) : ℂ) := by
  simp [halfModulus2]

end GL2

section SubgroupHaar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance borelSpace_units_local : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ := borelSpace_units

scoped instance locallyCompactSpace_unip : LocallyCompactSpace (unip p) := (isClosed_unip p).locallyCompactSpace

scoped instance secondCountable_unip : SecondCountableTopology (unip p) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unip p : Subgroup G) : Set G)

scoped instance locallyCompactSpace_torA : LocallyCompactSpace (torA p) := (isClosed_torA p).locallyCompactSpace

scoped instance secondCountable_torA : SecondCountableTopology (torA p) :=
  TopologicalSpace.Subtype.secondCountableTopology ((torA p : Subgroup G) : Set G)

theorem isMulRightInvariant_unip (μN : Measure (unip p)) [μN.IsMulLeftInvariant] : μN.IsMulRightInvariant := by
  refine ⟨fun n₀ => ?_⟩
  have h : (fun n : unip p => n * n₀) = fun n => n₀ * n := funext fun n => unip_comm p n n₀
  rw [h]
  exact map_mul_left_eq_self μN n₀

theorem isMulRightInvariant_torA (μA : Measure (torA p)) [μA.IsMulLeftInvariant] : μA.IsMulRightInvariant := by
  refine ⟨fun a₀ => ?_⟩
  have h : (fun a : torA p => a * a₀) = fun a => a₀ * a := funext fun a => torA_comm p a a₀
  rw [h]
  exact map_mul_left_eq_self μA a₀

def unipMeasure (ν : Measure F) : Measure (unip p) := Measure.map (unipHomeo p) ν

theorem measurable_unipHomeo : Measurable (unipHomeo p) := (unipHomeo p).continuous.measurable

scoped instance isHaarMeasure_unipMeasure (ν : Measure F) [ν.IsAddHaarMeasure] : (unipMeasure p ν).IsHaarMeasure where
  map_mul_left_eq_self n₀ := by
    obtain ⟨y₀, rfl⟩ : ∃ y₀, unipHomeo p y₀ = n₀ := ⟨(unipHomeo p).symm n₀, (unipHomeo p).apply_symm_apply n₀⟩
    unfold unipMeasure
    rw [Measure.map_map (measurable_const_mul _) (measurable_unipHomeo p)]
    have hcomp : ((fun n : unip p => unipHomeo p y₀ * n) ∘ (unipHomeo p)) = (unipHomeo p) ∘ fun y : F => y₀ + y := by
      funext y
      simp [Function.comp_apply, unipHomeo_add]
    rw [hcomp, ← Measure.map_map (measurable_unipHomeo p) (measurable_const_add _), map_add_left_eq_self]
  lt_top_of_isCompact K hK := by
    unfold unipMeasure
    rw [Measure.map_apply (measurable_unipHomeo p) hK.measurableSet]
    have : (unipHomeo p) ⁻¹' K = (unipHomeo p).symm '' K := by
      rw [← Homeomorph.image_symm]
    rw [this]
    exact (hK.image (unipHomeo p).symm.continuous).measure_lt_top
  open_pos U hU hne := by
    unfold unipMeasure
    rw [Measure.map_apply (measurable_unipHomeo p) hU.measurableSet]
    exact (hU.preimage (unipHomeo p).continuous).measure_ne_zero ν (hne.preimage (unipHomeo p).surjective)

theorem exists_eq_smul_unipMeasure (ν : Measure F) [ν.IsAddHaarMeasure] (μN : Measure (unip p)) [μN.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μN = c • unipMeasure p ν :=
  ⟨μN.haarScalarFactor (unipMeasure p ν), Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul _ _⟩

theorem integral_unip_eq (ν : Measure F) [ν.IsAddHaarMeasure] (μN : Measure (unip p)) [μN.IsHaarMeasure]
    {c : ℝ≥0} (hc : μN = c • unipMeasure p ν) (h : unip p → ℂ) :
    ∫ n, h n ∂μN = (c : ℂ) * ∫ y, h (unipHomeo p y) ∂ν := by
  rw [hc, integral_smul_nnreal_measure]
  unfold unipMeasure
  rw [← Homeomorph.toMeasurableEquiv_coe, integral_map_equiv]
  rw [NNReal.smul_def, Complex.real_smul]

def torMeasure (τ : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : Measure (torA p) := Measure.map (torHomeo p) τ

theorem measurable_torHomeo : Measurable (torHomeo p) := (torHomeo p).continuous.measurable

scoped instance isHaarMeasure_torMeasure (τ : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ) [τ.IsHaarMeasure] :
    (torMeasure p τ).IsHaarMeasure where
  map_mul_left_eq_self a₀ := by
    obtain ⟨y₀, rfl⟩ : ∃ y₀, torHomeo p y₀ = a₀ := ⟨(torHomeo p).symm a₀, (torHomeo p).apply_symm_apply a₀⟩
    unfold torMeasure
    rw [Measure.map_map (measurable_const_mul _) (measurable_torHomeo p)]
    have hcomp : ((fun a : torA p => torHomeo p y₀ * a) ∘ (torHomeo p)) =
        (torHomeo p) ∘ fun y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => y₀ * y := by
      funext y
      simp [Function.comp_apply, torHomeo_mul]
    rw [hcomp, ← Measure.map_map (measurable_torHomeo p) (measurable_const_mul _), map_mul_left_eq_self]
  lt_top_of_isCompact K hK := by
    unfold torMeasure
    rw [Measure.map_apply (measurable_torHomeo p) hK.measurableSet]
    have : (torHomeo p) ⁻¹' K = (torHomeo p).symm '' K := by
      rw [← Homeomorph.image_symm]
    rw [this]
    exact (hK.image (torHomeo p).symm.continuous).measure_lt_top
  open_pos U hU hne := by
    unfold torMeasure
    rw [Measure.map_apply (measurable_torHomeo p) hU.measurableSet]
    exact (hU.preimage (torHomeo p).continuous).measure_ne_zero τ (hne.preimage (torHomeo p).surjective)

theorem exists_eq_smul_torMeasure (τ : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ) [τ.IsHaarMeasure]
    (μA : Measure (torA p)) [μA.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μA = c • torMeasure p τ :=
  ⟨μA.haarScalarFactor (torMeasure p τ), Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul _ _⟩

theorem integral_torA_eq (τ : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ) [τ.IsHaarMeasure]
    (μA : Measure (torA p)) [μA.IsHaarMeasure]
    {c : ℝ≥0} (hc : μA = c • torMeasure p τ) (h : torA p → ℂ) :
    ∫ a, h a ∂μA = (c : ℂ) * ∫ y, h (torHomeo p y) ∂τ := by
  rw [hc, integral_smul_nnreal_measure]
  unfold torMeasure
  rw [← Homeomorph.toMeasurableEquiv_coe, integral_map_equiv]
  rw [NNReal.smul_def, Complex.real_smul]

end SubgroupHaar

section Unfold

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem integrable_and_integral_eq_unfold
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Φ : G → ℂ) (hΦm : Measurable Φ) (hΦi : Integrable Φ μ) :
    (∀ᵐ g ∂(μ.withDensity (HaarQuotient.density H μH)), Integrable (fun x : H => Φ ((x : G) * g)) μH) ∧
    Integrable (fun g : G => ∫ x : H, Φ ((x : G) * g) ∂μH) (μ.withDensity (HaarQuotient.density H μH)) ∧
    ∫ g, Φ g ∂μ = ∫ g, (∫ x : H, Φ ((x : G) * g) ∂μH) ∂(μ.withDensity (HaarQuotient.density H μH)) := by
  classical

  have hS : IsFundamentalDomain (↥(⊥ : Subgroup G)) (Set.univ : Set G) μ :=
    ⟨MeasurableSet.univ.nullMeasurableSet, Filter.Eventually.of_forall fun x => ⟨1, Set.mem_univ _⟩,
      Subsingleton.pairwise⟩
  haveI : Subsingleton (↥((⊥ : Subgroup G).subgroupOf H)) := ⟨fun a b => by
    refine Subtype.ext (Subtype.ext ?_)
    have ha := a.2
    have hb := b.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  have hT : IsFundamentalDomain (↥((⊥ : Subgroup G).subgroupOf H)) (Set.univ : Set H) μH :=
    ⟨MeasurableSet.univ.nullMeasurableSet, Filter.Eventually.of_forall fun x => ⟨1, Set.mem_univ _⟩,
      Subsingleton.pairwise⟩
  have hfin : ∫⁻ g in Set.univ, ‖Φ g‖ₑ ∂μ < ⊤ := by
    rw [Measure.restrict_univ]
    exact hΦi.2
  obtain ⟨h1, h2, h3⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ H hH μH ⊥ bot_le Φ
      hΦm (fun γ hγ g => by rw [Subgroup.mem_bot.mp hγ, one_mul]) Set.univ hS Set.univ hT hfin
  simp only [Measure.restrict_univ] at h2 h3
  simp only [integrableOn_univ] at h1

  set μD := μ.withDensity (HaarQuotient.density H μH) with hμD
  set Ξ : MulAction.orbitRel.Quotient H G → ℂ := fun q => ∫ x : H, Φ ((x : G) * q.out) ∂μH with hΞ
  have hmk : Measurable (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) := measurable_quotient_mk''
  have hmeas : HaarQuotient.measure μ H μH = Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD :=
    rfl
  rw [hmeas] at h1 h2 h3
  have hΞi : Integrable Ξ (Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD) := h2
  have hcomp : Integrable (Ξ ∘ (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)) μD :=
    (integrable_map_measure hΞi.aestronglyMeasurable hmk.aemeasurable).mp hΞi
  have hint : ∫ q, Ξ q ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD) =
      ∫ g, Ξ (Quotient.mk'' g) ∂μD :=
    integral_map hmk.aemeasurable hΞi.aestronglyMeasurable

  have hfib : ∀ g : G, Ξ (Quotient.mk'' g) = ∫ x : H, Φ ((x : G) * g) ∂μH := by
    intro g
    have hrel : @Setoid.r _ (MulAction.orbitRel H G) ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
      Quotient.mk_out' g
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    simp only [hΞ]
    rw [← hn, Subgroup.smul_def, smul_eq_mul]
    have := integral_mul_right_eq_self (μ := μH) (fun x : H => Φ ((x : G) * g)) n
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  have hfun : (Ξ ∘ (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)) = fun g => ∫ x : H, Φ ((x : G) * g) ∂μH :=
    funext fun g => hfib g

  have hae : ∀ᵐ g ∂μD, Integrable (fun x : H => Φ ((x : G) * g)) μH := by
    have h1' := ae_of_ae_map hmk.aemeasurable h1
    filter_upwards [h1'] with g hg
    have hrel : @Setoid.r _ (MulAction.orbitRel H G) ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
      Quotient.mk_out' g
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    rw [← hn, Subgroup.smul_def, smul_eq_mul] at hg
    have := hg.comp_mul_right n⁻¹
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
  refine ⟨hae, hfun ▸ hcomp, ?_⟩
  rw [h3, hint]
  exact integral_congr_ae (Filter.Eventually.of_forall hfib)

end Unfold

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

def mulHaar : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))

scoped instance isHaarMeasure_mulHaar : (mulHaar p).IsHaarMeasure := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  exact LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

def adet (g : G) : ℝ :=
  ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ))

theorem adet_pos (g : G) : 0 < adet p g := by
  simp only [adet, coe_modulus_eq_norm]
  exact norm_units_pos p _

theorem adet_unipotentGL2_mul (x : F) (g : G) : adet p (unipotentGL2 x * g) = adet p g := by
  simp only [adet, map_mul, det_unipotentGL2, one_mul]

theorem adet_diagOne_mul (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (h : G) :
    adet p (diagOne y * h) = ‖(y : F)‖ * adet p h := by
  simp only [adet, map_mul, det_diagOne, Units.val_mul, coe_modulus_eq_norm, norm_mul]

theorem row_one_antidiag_mul (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (h : G) :
    (((w₀ * h : G)) : Mat) 1 = (h : Mat) 0 := by
  funext j
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hw₀]

theorem det_antidiag (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) :
    Matrix.GeneralLinearGroup.det w₀ = -1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, hw₀, Matrix.det_fin_two_of]
  simp

theorem adet_antidiag_mul (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (h : G) :
    adet p (w₀ * h) = adet p h := by
  simp only [adet, map_mul, det_antidiag p w₀ hw₀, Units.val_mul, Units.val_neg, Units.val_one,
    coe_modulus_eq_norm, norm_mul, norm_neg, norm_one, one_mul]

theorem row_zero_diagOne_mul (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (h : G) (j : Fin 2) :
    (((diagOne y * h : G)) : Mat) 0 j = (y : F) * (h : Mat) 0 j := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_diagOne]

scoped instance isMulRightInvariant_mulHaar : (mulHaar p).IsMulRightInvariant := by
  refine ⟨fun y₀ => ?_⟩
  have h : (fun y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => y * y₀) = fun y => y₀ * y := funext fun y => mul_comm y y₀
  rw [h]
  exact map_mul_left_eq_self (mulHaar p) y₀

theorem coe_modulus_units_ne_zero (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ((modulus (y : F) : ℝ) : ℂ) ≠ 0 := by
  rw [coe_modulus_eq_norm]
  exact_mod_cast (norm_units_pos p y).ne'

theorem modulus_mul_cpow (t y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (e : ℂ) :
    ((modulus (((t * y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) : ℝ) : ℂ) ^ e =
      ((modulus (t : F) : ℝ) : ℂ) ^ e * ((modulus (y : F) : ℝ) : ℂ) ^ e := by
  rw [Units.val_mul, coe_modulus_eq_norm, coe_modulus_eq_norm, coe_modulus_eq_norm, norm_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _) e

theorem scalar_identity2 (r t : ℝ) (hr : 0 < r) (ht : 0 < t) (s : ℂ) :
    ((r * t : ℝ) : ℂ) ^ (s + 1 / 2) * ((r : ℝ) : ℂ) ^ (1 / 2 - s) = ((r : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (s + 1 / 2) := by
  have hr0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le ht.le]
  have e : ((r : ℝ) : ℂ) ^ (s + 1 / 2) * ((r : ℝ) : ℂ) ^ (1 / 2 - s) = ((r : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hr0]
    have : s + 1 / 2 + (1 / 2 - s) = (1 : ℂ) := by ring
    rw [this, Complex.cpow_one]
  linear_combination (((t : ℝ) : ℂ) ^ (s + 1 / 2)) * e

theorem norm_psiLocal (x : F) : ‖NumberField.StandardAddChar.psiLocal ℚ p x‖ = 1 := by
  rw [NumberField.StandardAddChar.psiLocal_apply]
  exact NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ
    (NumberField.StandardAddChar.adelicTraceData ℚ).isGlobalAddChar_psiK _

theorem map_mul_left_eq_smul (ν : Measure F) [ν.IsAddHaarMeasure] (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    Measure.map (fun x : F => (t : F) * x) ν = ((modulus (t : F))⁻¹ : ℝ≥0) • ν := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.coe_nnreal_smul_apply]
  have hpre : (fun x : F => (t : F) * x) ⁻¹' s = (t⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) • s := by
    rw [← Set.preimage_smul t s]
    rfl
  rw [hpre, ← distribHaarChar_mul ν (t⁻¹) s, map_inv, modulus_coe_units]

theorem integral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure F) [ν.IsAddHaarMeasure] (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (f : F → E) :
    ∫ x, f ((t : F) * x) ∂ν = ((modulus (t : F))⁻¹ : ℝ≥0) • ∫ y, f y ∂ν := by
  have e := integral_map_equiv (MeasurableEquiv.mulLeft₀ (t : F) t.ne_zero) (μ := ν) f
  simp only [MeasurableEquiv.coe_mulLeft₀] at e
  rw [← e, map_mul_left_eq_smul p ν t, integral_smul_nnreal_measure]

theorem isOpen_setOf_valued_units_eq (γ : WithZero (Multiplicative ℤ)) :
    IsOpen {y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ | Valued.v (y : F) = γ} := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · convert isOpen_empty
    ext y
    simp [Units.ne_zero]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, γ = WithZero.exp m := ⟨_, (WithZero.exp_log hγ).symm⟩
  obtain ⟨π, hπ0, hπ⟩ := NumberField.AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p 1
  have hvzpow : ∀ k : ℤ, Valued.v (π ^ k) = WithZero.exp (-k) := by
    intro k
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    congr 1
    simp
  set t : F := π ^ (-m) with ht
  have hvt : Valued.v t = WithZero.exp m := by rw [ht, hvzpow, neg_neg]
  have ht0 : t ≠ 0 := zpow_ne_zero _ hπ0
  have htπ0 : t * π ≠ 0 := mul_ne_zero ht0 hπ0
  have hvtπ : Valued.v (t * π) = WithZero.exp (m - 1) := by
    rw [map_mul, hvt, hπ, ← WithZero.exp_add]
    congr 1
  have hset : {y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ | Valued.v (y : F) = γ}
      = Units.val ⁻¹' ({x : F | Valued.v x ≤ Valued.v t} ∩ {x : F | Valued.v x ≤ Valued.v (t * π)}ᶜ) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff, hvt, hvtπ, hm]
    have hy0 : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (y : F) = WithZero.exp k := ⟨_, (WithZero.exp_log hy0).symm⟩
    rw [hk, WithZero.exp_le_exp, WithZero.exp_le_exp, WithZero.exp_injective.eq_iff]
    omega
  rw [hset]
  exact ((NumberField.AdelicLevel.isOpen_setOf_valued_le p t ht0).inter
    (NumberField.AdelicLevel.isClosed_setOf_valued_le p (t * π) htπ0).isOpen_compl).preimage
    Units.continuous_val

theorem continuous_comp_valued {X : Type*} [TopologicalSpace X] {ι : Type*}
    (φ : X → ι) (hφ : ∀ i, IsOpen (φ ⁻¹' {i})) (ω : ι → ℂ) : Continuous (ω ∘ φ) := by
  refine continuous_def.mpr fun s _ => ?_
  have : (ω ∘ φ) ⁻¹' s = ⋃ i ∈ ω ⁻¹' s, φ ⁻¹' {i} := by
    ext x; simp
  rw [this]
  exact isOpen_biUnion fun i _ => hφ i

theorem continuous_weightGJ (ω : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) :
    Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ω (Valued.v (q.2 : F)) (Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) := by
  have h := continuous_comp_valued
    (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      (Valued.v (q.2 : F), Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)))
    (fun i => ?_) (fun i => ω i.1 i.2)
  · exact h
  · have : (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        (Valued.v (q.2 : F), Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F))) ⁻¹' {i}
        = (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => q.2) ⁻¹' {y | Valued.v (y : F) = i.1} ∩
          (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => Matrix.GeneralLinearGroup.det q.1) ⁻¹'
            {y | Valued.v (y : F) = i.2} := by
      ext q; simp [Prod.ext_iff]
    rw [this]
    exact ((isOpen_setOf_valued_units_eq p i.1).preimage continuous_snd).inter
      ((isOpen_setOf_valued_units_eq p i.2).preimage (Matrix.GeneralLinearGroup.continuous_det.comp continuous_fst))

theorem continuous_weightN (ω : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) :
    Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ω (Valued.v (q.2 : F))⁻¹ (Valued.v (q.2 : F) *
        Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) := by
  have h := continuous_comp_valued
    (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      (Valued.v (q.2 : F), Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)))
    (fun i => ?_) (fun i => ω i.1⁻¹ (i.1 * i.2))
  · exact h
  · have : (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        (Valued.v (q.2 : F), Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F))) ⁻¹' {i}
        = (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => q.2) ⁻¹' {y | Valued.v (y : F) = i.1} ∩
          (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => Matrix.GeneralLinearGroup.det q.1) ⁻¹'
            {y | Valued.v (y : F) = i.2} := by
      ext q; simp [Prod.ext_iff]
    rw [this]
    exact ((isOpen_setOf_valued_units_eq p i.1).preimage continuous_snd).inter
      ((isOpen_setOf_valued_units_eq p i.2).preimage (Matrix.GeneralLinearGroup.continuous_det.comp continuous_fst))

def shear : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G ≃ᵐ (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G where
  toFun q := (q.1, (diagOne q.1)⁻¹ * q.2)
  invFun q := (q.1, diagOne q.1 * q.2)
  left_inv q := by simp
  right_inv q := by simp
  measurable_toFun := (continuous_fst.prodMk
    (((continuous_diagOne p).comp continuous_fst).inv.mul continuous_snd)).measurable
  measurable_invFun := (continuous_fst.prodMk
    (((continuous_diagOne p).comp continuous_fst).mul continuous_snd)).measurable

theorem shear_apply (q : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G) : shear p q = (q.1, (diagOne q.1)⁻¹ * q.2) := rfl

theorem measurePreserving_shear (μ₂ : Measure G) [μ₂.IsHaarMeasure] :
    MeasurePreserving (shear p) ((mulHaar p).prod μ₂) ((mulHaar p).prod μ₂) := by
  have h := MeasurePreserving.skew_product (μa := mulHaar p) (μc := μ₂) (μd := μ₂)
    (g := fun (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (g : G) => (diagOne y)⁻¹ * g)
    (MeasurePreserving.id (mulHaar p))
    ((((continuous_diagOne p).comp continuous_fst).inv.mul continuous_snd).measurable)
    (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μ₂ _)
  exact h

def outerW (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ Φ₂ : (Fin 2 → F) → ℂ) (s : ℂ) (g : G) : ℂ :=
  Φ₁ ((g : Mat) 0) * Φ₂ ((g : Mat) 1) * ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((adet p g : ℝ) : ℂ) ^ (s + 1 / 2)

def innerW (w : G → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ) (g : G) (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ℂ :=
  wt (Valued.v (y : F)) (Valued.v ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
    w (diagOne y * g) * ((χ 1 y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)

def kerW (w : G → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ Φ₂ : (Fin 2 → F) → ℂ) (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ)
    (q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ℂ :=
  outerW p χ Φ₁ Φ₂ s q.1 * innerW p w χ wt s q.1 q.2

def kXi (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ : (Fin 2 → F) → ℂ) (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (h : G) (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ℂ :=
  wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
    Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j) * ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ *
    ((modulus (t : F) : ℝ) : ℂ)

def cXi (w : G → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₂ : (Fin 2 → F) → ℂ) (s : ℂ) (h : G) : ℂ :=
  w h * Φ₂ ((h : Mat) 1) * ((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((adet p h : ℝ) : ℂ) ^ (s + 1 / 2)

theorem scalar_identity6 (u a : ℝ) (hu : 0 < u) (ha : 0 < a) (s : ℂ) :
    ((u * a : ℝ) : ℂ) ^ (s + 1 / 2) * ((u⁻¹ : ℝ) : ℂ) ^ (s - 1 / 2) = ((u : ℝ) : ℂ) * ((a : ℝ) : ℂ) ^ (s + 1 / 2) := by
  have hu0 : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have ha0 : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hua0 : ((u * a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hu ha).ne'
  have hui0 : ((u⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.mpr hu).ne'
  have e1 : ((u * a : ℝ) : ℂ) ^ (s + 1 / 2) = Complex.exp (((Real.log u + Real.log a : ℝ) : ℂ) * (s + 1 / 2)) := by
    rw [Complex.cpow_def_of_ne_zero hua0, ← Complex.ofReal_log (mul_pos hu ha).le, Real.log_mul hu.ne' ha.ne']
  have e2 : ((u⁻¹ : ℝ) : ℂ) ^ (s - 1 / 2) = Complex.exp (((-Real.log u : ℝ) : ℂ) * (s - 1 / 2)) := by
    rw [Complex.cpow_def_of_ne_zero hui0, ← Complex.ofReal_log (inv_pos.mpr hu).le, Real.log_inv]
  have e3 : ((u : ℝ) : ℂ) = Complex.exp (((Real.log u : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log hu]
  have e4 : ((a : ℝ) : ℂ) ^ (s + 1 / 2) = Complex.exp (((Real.log a : ℝ) : ℂ) * (s + 1 / 2)) := by
    rw [Complex.cpow_def_of_ne_zero ha0, ← Complex.ofReal_log ha.le]
  rw [e1, e2, e4, e3, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem kerW_shear (w : G → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ Φ₂ : (Fin 2 → F) → ℂ) (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ)
    (y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (h : G) :
    kerW p w χ Φ₁ Φ₂ wt s ((diagOne y)⁻¹ * h, y) = cXi p w χ Φ₂ s h * kXi p χ Φ₁ wt h y⁻¹ := by
  have hrow0 : ((((diagOne y)⁻¹ * h : G)) : Mat) 0 = fun j => (((y⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) * (h : Mat) 0 j := by
    rw [← map_inv]; exact funext (row_zero_diagOne_mul p y⁻¹ h)
  have hrow1 : ((((diagOne y)⁻¹ * h : G)) : Mat) 1 = (h : Mat) 1 := by
    rw [← map_inv]; exact row_diagOne_mul p y⁻¹ h
  have hdet : Matrix.GeneralLinearGroup.det ((diagOne y)⁻¹ * h) = y⁻¹ * Matrix.GeneralLinearGroup.det h := by
    rw [← map_inv, map_mul, det_diagOne]
  have hadet : adet p ((diagOne y)⁻¹ * h) = ‖(((y⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F)‖ * adet p h := by
    rw [← map_inv]; exact adet_diagOne_mul p y⁻¹ h
  have hw : w (diagOne y * ((diagOne y)⁻¹ * h)) = w h := by rw [mul_inv_cancel_left]
  have hv : Valued.v (((y⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) = (Valued.v (y : F))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  simp only [kerW, outerW, innerW, cXi, kXi]
  rw [hrow0, hrow1, hdet, hadet, hw, map_mul (χ 0), Units.val_mul, Units.val_mul, map_mul Valued.v, hv, inv_inv,
    map_inv (χ 1), Units.val_inv_eq_inv_val (χ 1 y), inv_inv, coe_modulus_eq_norm, coe_modulus_eq_norm,
    Units.val_inv_eq_inv_val y, norm_inv]
  have key := scalar_identity6 ‖(y : F)‖⁻¹ (adet p h) (inv_pos.mpr (norm_units_pos p y)) (adet_pos p h) s
  rw [inv_inv] at key
  linear_combination (Φ₁ (fun j => ((y : F))⁻¹ * (h : Mat) 0 j) * Φ₂ ((h : Mat) 1) *
    ((χ 0 y⁻¹ : ℂˣ) : ℂ) * ((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
    wt (Valued.v (y : F)) ((Valued.v (y : F))⁻¹ * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
    w h * ((χ 1 y : ℂˣ) : ℂ)) * key

theorem cXi_unipotent_mul (w : G → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₂ : (Fin 2 → F) → ℂ) (s : ℂ)
    (hwlaw : ∀ (x : F) (g : G), w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (x : F) (h : G) :
    cXi p w χ Φ₂ s (unipotentGL2 x * h) = NumberField.StandardAddChar.psiLocal ℚ p x * cXi p w χ Φ₂ s h := by
  simp only [cXi, hwlaw, row_unipotentGL2_mul, map_mul, det_unipotentGL2, one_mul, adet_unipotentGL2_mul]
  ring

theorem row_zero_unipotentGL2_mul (x : F) (h : G) (j : Fin 2) :
    (((unipotentGL2 x * h : G)) : Mat) 0 j = (h : Mat) 0 j + x * (h : Mat) 1 j := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]

theorem kXi_unipotent_mul (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ : (Fin 2 → F) → ℂ) (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (x : F) (h : G) (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    kXi p χ Φ₁ wt (unipotentGL2 x * h) t =
      wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
        Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + ((t : F) * x) * (h : Mat) 1 j) *
        ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : F) : ℝ) : ℂ) := by
  simp only [kXi, map_mul, det_unipotentGL2, one_mul, row_zero_unipotentGL2_mul]
  have e : (fun j : Fin 2 => (t : F) * ((h : Mat) 0 j + x * (h : Mat) 1 j))
      = fun j : Fin 2 => (t : F) * (h : Mat) 0 j + (t : F) * x * (h : Mat) 1 j := funext fun j => by ring
  rw [e]

theorem continuous_coe_modulus_snd :
    Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ((modulus ((q.2 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) := by
  have e : (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ((modulus ((q.2 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ)) =
      fun q => (((‖((q.2 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ : ℝ)) : ℂ) := by
    funext q; rw [coe_modulus_eq_norm]
  rw [e]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.comp continuous_snd))

theorem measurable_kerW {w : G → ℂ} (hw : IsLocallyConstant w)
    {χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)} (hχ : ∀ i, IsLocallyConstant (χ i))
    {Φ₁ Φ₂ : (Fin 2 → F) → ℂ} (hΦ₁ : IsLocallyConstant Φ₁) (hΦ₂ : IsLocallyConstant Φ₂)
    (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ) :
    Measurable (kerW p w χ Φ₁ Φ₂ wt s) := by
  have h1 : Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => Φ₁ ((q.1 : Mat) 0) :=
    hΦ₁.continuous.comp ((continuous_row p 0).comp continuous_fst)
  have h2 : Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => Φ₂ ((q.1 : Mat) 1) :=
    hΦ₂.continuous.comp ((continuous_row p 1).comp continuous_fst)
  have h3 : Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ((χ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp ((hχ 0).continuous.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_fst))
  have h4 : Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ((adet p q.1 : ℝ) : ℂ) ^ (s + 1 / 2) :=
    ((continuous_modulus_det p).comp continuous_fst).measurable.pow_const _
  have h5 := continuous_weightGJ p wt
  have h6 : Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => w (diagOne q.2 * q.1) :=
    hw.continuous.comp (((continuous_diagOne p).comp continuous_snd).mul continuous_fst)
  have h7 : Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ((χ 1 q.2 : ℂˣ) : ℂ) :=
    Units.continuous_val.comp ((hχ 1).continuous.comp continuous_snd)
  have h8 : Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ((modulus ((q.2 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2) :=
    (continuous_coe_modulus_snd p).measurable.pow_const _
  unfold kerW outerW innerW
  exact ((((h1.mul h2).mul h3).measurable).mul h4).mul (((((h5.mul h6).mul h7).measurable).mul h8))

theorem measurable_kXi {χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)} (hχ : ∀ i, IsLocallyConstant (χ i))
    {Φ₁ : (Fin 2 → F) → ℂ} (hΦ₁ : IsLocallyConstant Φ₁)
    (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) :
    Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => kXi p χ Φ₁ wt q.1 q.2 := by
  have h1 := continuous_weightN p wt
  have h2 : Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      Φ₁ (fun j : Fin 2 => ((q.2 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) * (q.1 : Mat) 0 j) := by
    refine hΦ₁.continuous.comp (continuous_pi fun j => ?_)
    exact (Units.continuous_val.comp continuous_snd).mul ((continuous_entry p 0 j).comp continuous_fst)
  have h3 : Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ((χ 0 q.2 : ℂˣ) : ℂ) :=
    Units.continuous_val.comp ((hχ 0).continuous.comp continuous_snd)
  have h4 : Continuous fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (((χ 1 q.2 : ℂˣ) : ℂ))⁻¹ :=
    (Units.continuous_val.comp ((hχ 1).continuous.comp continuous_snd)).inv₀ (fun q => Units.ne_zero _)
  have h5 := continuous_coe_modulus_snd p
  unfold kXi
  exact ((((h1.mul h2).mul h3).mul h4).mul h5).measurable

theorem measurable_cXi {w : G → ℂ} (hw : IsLocallyConstant w)
    {χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)} (hχ : ∀ i, IsLocallyConstant (χ i))
    {Φ₂ : (Fin 2 → F) → ℂ} (hΦ₂ : IsLocallyConstant Φ₂) (s : ℂ) :
    Measurable (cXi p w χ Φ₂ s) := by
  have h1 : Continuous w := hw.continuous
  have h2 : Continuous fun g : G => Φ₂ ((g : Mat) 1) := hΦ₂.continuous.comp (continuous_row p 1)
  have h3 : Continuous fun g : G => ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp ((hχ 0).continuous.comp Matrix.GeneralLinearGroup.continuous_det)
  have h4 : Measurable fun g : G => ((adet p g : ℝ) : ℂ) ^ (s + 1 / 2) :=
    (continuous_modulus_det p).measurable.pow_const _
  unfold cXi
  exact (((h1.mul h2).mul h3).measurable).mul h4

def Xi (w : G → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ Φ₂ : (Fin 2 → F) → ℂ)
    (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ) (h : G) : ℂ :=
  ∫ y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ, cXi p w χ Φ₂ s h * kXi p χ Φ₁ wt h y⁻¹ ∂(mulHaar p)

theorem measurable_Xi {w : G → ℂ} (hw : IsLocallyConstant w)
    {χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)} (hχ : ∀ i, IsLocallyConstant (χ i))
    {Φ₁ Φ₂ : (Fin 2 → F) → ℂ} (hΦ₁ : IsLocallyConstant Φ₁) (hΦ₂ : IsLocallyConstant Φ₂)
    (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ) :
    Measurable (Xi p w χ Φ₁ Φ₂ wt s) := by
  have h1 : Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => cXi p w χ Φ₂ s q.1 := by
    have := (measurable_cXi p hw hχ hΦ₂ s).comp
      (measurable_fst : Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => q.1)
    simpa only [Function.comp_def] using this
  have h2 : Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => kXi p χ Φ₁ wt q.1 q.2⁻¹ := by
    have := (measurable_kXi p hχ hΦ₁ wt).comp
      ((measurable_fst.prodMk measurable_snd.inv : Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (q.1, q.2⁻¹)))
    simpa only [Function.comp_def] using this
  have hK : Measurable (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      cXi p w χ Φ₂ s q.1 * kXi p χ Φ₁ wt q.1 q.2⁻¹) := h1.mul h2
  have e : Xi p w χ Φ₁ Φ₂ wt s = fun h => ∫ y, (fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      cXi p w χ Φ₂ s q.1 * kXi p χ Φ₁ wt q.1 q.2⁻¹) (h, y) ∂(mulHaar p) := by
    funext h; rfl
  rw [e]
  exact (hK.stronglyMeasurable.integral_prod_right' (ν := mulHaar p)).measurable

theorem lintegral_unip_eq (ν : Measure F) [ν.IsAddHaarMeasure] (μN : Measure (unip p)) [μN.IsHaarMeasure]
    {c : ℝ≥0} (hc : μN = c • unipMeasure p ν) (h : unip p → ℝ≥0∞) :
    ∫⁻ n, h n ∂μN = c * ∫⁻ y, h (unipHomeo p y) ∂ν := by
  rw [hc, lintegral_smul_measure]
  unfold unipMeasure
  rw [← Homeomorph.toMeasurableEquiv_coe, lintegral_map_equiv]
  rfl

theorem inner_dilation (ν : Measure F) [ν.IsAddHaarMeasure] (Φ₁ : (Fin 2 → F) → ℂ) (h : G)
    (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
        Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + ((t : F) * x) * (h : Mat) 1 j) ∂ν
      = ((modulus (t : F))⁻¹ : ℝ≥0) •
        ∫ y : F, Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + y * (h : Mat) 1 j) *
          NumberField.StandardAddChar.psiLocal ℚ p ((t : F)⁻¹ * y) ∂ν := by
  rw [← integral_comp_mul_left p ν t]
  congr 1
  funext x
  rw [← mul_assoc, inv_mul_cancel₀ t.ne_zero, one_mul, mul_comm]

def Rfun (w : G → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ Φ₂ : (Fin 2 → F) → ℂ)
    (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ) (ν : Measure F) (h : G) : ℂ :=
  (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((adet p h : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      ∫ t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ,
        wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
          (∫ y : F, Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + y * (h : Mat) 1 j) *
              NumberField.StandardAddChar.psiLocal ℚ p ((t : F)⁻¹ * y) ∂ν) *
          ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(mulHaar p)) *
    (w h * Φ₂ ((h : Mat) 1)) * ((adet p h : ℝ) : ℂ) ^ s

theorem inner_x_integral (ν : Measure F) [ν.IsAddHaarMeasure]
    (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ : (Fin 2 → F) → ℂ)
    (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (h : G)
    (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x * kXi p χ Φ₁ wt (unipotentGL2 x * h) t ∂ν
      = wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
          (∫ y : F, Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + y * (h : Mat) 1 j) *
              NumberField.StandardAddChar.psiLocal ℚ p ((t : F)⁻¹ * y) ∂ν) *
          ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ := by
  simp_rw [kXi_unipotent_mul]
  set A : ℂ := wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) *
    Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) with hA
  set B : ℂ := ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ with hB
  set M : ℂ := ((modulus (t : F) : ℝ) : ℂ) with hM
  have hM0 : M ≠ 0 := coe_modulus_units_ne_zero p t
  have e : (fun x : F => NumberField.StandardAddChar.psiLocal ℚ p x *
        (A * Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + ((t : F) * x) * (h : Mat) 1 j) *
          ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ * M))
      = fun x => (A * B * M) * (NumberField.StandardAddChar.psiLocal ℚ p x *
          Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + ((t : F) * x) * (h : Mat) 1 j)) := by
    funext x; simp only [hB]; ring
  rw [e, integral_const_mul, inner_dilation p ν Φ₁ h t, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
    Complex.ofReal_inv]
  have hM' : (((modulus (t : F) : ℝ≥0) : ℝ) : ℂ) = M := rfl
  rw [hM']
  generalize (∫ y : F, Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + y * (h : Mat) 1 j) *
      NumberField.StandardAddChar.psiLocal ℚ p ((t : F)⁻¹ * y) ∂ν) = I
  rw [hB]
  have hMM : M * M⁻¹ = 1 := mul_inv_cancel₀ hM0
  linear_combination (A * I * ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹) * hMM

theorem fibre_eq (ν : Measure F) [ν.IsAddHaarMeasure] (μN : Measure (unip p)) [μN.IsHaarMeasure]
    {cN : ℝ≥0} (hμN : μN = cN • unipMeasure p ν)
    (w : G → ℂ)
    (hwlaw : ∀ (x : F) (g : G), w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (Φ₁ Φ₂ : (Fin 2 → F) → ℂ)
    (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ) (h : G)
    (hgood : cXi p w χ Φ₂ s h = 0 ∨
      Integrable (fun z : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        NumberField.StandardAddChar.psiLocal ℚ p z.1 * kXi p χ Φ₁ wt (unipotentGL2 z.1 * h) z.2⁻¹) (ν.prod (mulHaar p))) :
    ∫ n : unip p, Xi p w χ Φ₁ Φ₂ wt s ((n : G) * h) ∂μN = (cN : ℂ) * Rfun p w χ Φ₁ Φ₂ wt s ν h := by
  rw [integral_unip_eq p ν μN hμN]
  congr 1
  simp_rw [unipHomeo_apply_coe]
  have hXi : ∀ x : F, Xi p w χ Φ₁ Φ₂ wt s (unipotentGL2 x * h)
      = cXi p w χ Φ₂ s h * ∫ y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ,
          NumberField.StandardAddChar.psiLocal ℚ p x * kXi p χ Φ₁ wt (unipotentGL2 x * h) y⁻¹ ∂(mulHaar p) := by
    intro x
    simp only [Xi, cXi_unipotent_mul p w χ Φ₂ s hwlaw]
    rw [← integral_const_mul]
    congr 1; funext y; ring
  simp_rw [hXi]
  rw [integral_const_mul]
  have hane : ((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((adet p h : ℝ) : ℂ) ^ (s + 1 / 2) ≠ 0 := by
    refine mul_ne_zero (Units.ne_zero _) ?_
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast (adet_pos p h).ne')
  rcases hgood with h0 | hg
  ·
    have hwΦ : w h * Φ₂ ((h : Mat) 1) = 0 := by
      have : (w h * Φ₂ ((h : Mat) 1)) *
          (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((adet p h : ℝ) : ℂ) ^ (s + 1 / 2)) = 0 := by
        rw [← h0, cXi]; ring
      exact (mul_eq_zero.mp this).resolve_right hane
    rw [h0, zero_mul, Rfun, hwΦ, mul_zero, zero_mul]
  · rw [integral_integral_swap hg]
    simp_rw [inner_x_integral p ν χ Φ₁ wt h]
    rw [integral_inv_eq_self
      (fun t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
          (∫ y : F, Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + y * (h : Mat) 1 j) *
              NumberField.StandardAddChar.psiLocal ℚ p ((t : F)⁻¹ * y) ∂ν) *
          ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹) (mulHaar p)]
    simp only [Rfun, cXi]
    have key : ((adet p h : ℝ) : ℂ) ^ (s + 1 / 2) = ((adet p h : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((adet p h : ℝ) : ℂ) ^ s := by
      rw [← Complex.cpow_add _ _ (by exact_mod_cast (adet_pos p h).ne'), add_comm]
    rw [key]
    ring

theorem enorm_psiLocal (x : F) : ‖NumberField.StandardAddChar.psiLocal ℚ p x‖ₑ = 1 := by
  rw [← ofReal_norm, norm_psiLocal, ENNReal.ofReal_one]

theorem ae_good (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (μN : Measure (unip p)) [μN.IsHaarMeasure] [μN.IsMulRightInvariant]
    (ν : Measure F) [ν.IsAddHaarMeasure] {cN : ℝ≥0} (hcN : 0 < cN) (hμN : μN = cN • unipMeasure p ν)
    {w : G → ℂ} (hwlc : IsLocallyConstant w)
    (hwlaw : ∀ (x : F) (g : G), w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    {χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)} (hχ : ∀ i, IsLocallyConstant (χ i))
    {Φ₁ Φ₂ : (Fin 2 → F) → ℂ} (hΦ₁ : IsLocallyConstant Φ₁) (hΦ₂ : IsLocallyConstant Φ₂)
    (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ) (s : ℂ)
    (hFk : Integrable (fun q : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G =>
      cXi p w χ Φ₂ s q.2 * kXi p χ Φ₁ wt q.2 q.1⁻¹) ((mulHaar p).prod μ₂)) :
    ∀ᵐ h ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN)),
      cXi p w χ Φ₂ s h = 0 ∨
        Integrable (fun z : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
          NumberField.StandardAddChar.psiLocal ℚ p z.1 * kXi p χ Φ₁ wt (unipotentGL2 z.1 * h) z.2⁻¹)
          (ν.prod (mulHaar p)) := by
  classical
  set τ := mulHaar p with hτ

  have hkm : Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => kXi p χ Φ₁ wt q.1 q.2⁻¹ := by
    have := (measurable_kXi p hχ hΦ₁ wt).comp
      ((measurable_fst.prodMk measurable_snd.inv :
        Measurable fun q : G × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (q.1, q.2⁻¹)))
    simpa only [Function.comp_def] using this
  have hCm : Measurable (cXi p w χ Φ₂ s) := measurable_cXi p hwlc hχ hΦ₂ s
  set Γ : G → ℝ≥0∞ := fun h => ∫⁻ y, ‖cXi p w χ Φ₂ s h * kXi p χ Φ₁ wt h y⁻¹‖ₑ ∂τ with hΓ
  have hΓm : Measurable Γ :=
    ((hCm.comp measurable_fst).mul hkm).enorm.lintegral_prod_right'

  have hΓfin : ∫⁻ h, Γ h ∂μ₂ ≠ ∞ := by
    have h1 : ∫⁻ q, ‖cXi p w χ Φ₂ s q.2 * kXi p χ Φ₁ wt q.2 q.1⁻¹‖ₑ ∂(τ.prod μ₂) < ∞ := hFk.2
    rw [lintegral_prod_symm _ hFk.1.enorm] at h1
    exact h1.ne

  set Λ : G → ℝ≥0∞ := fun h => ∫⁻ n : unip p, Γ ((n : G) * h) ∂μN with hΛ
  have hΓ2m : Measurable fun q : G × unip p => Γ ((q.2 : G) * q.1) :=
    hΓm.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  have hΛm : Measurable Λ := hΓ2m.lintegral_prod_right'
  have hΛinv : ∀ (n₀ : unip p) (h : G), Λ ((n₀ : G) * h) = Λ h := by
    intro n₀ h
    simp only [hΛ]
    have := lintegral_mul_right_eq_self (μ := μN) (fun n : unip p => Γ ((n : G) * h)) n₀
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  set Λq : MulAction.orbitRel.Quotient (unip p) G → ℝ≥0∞ := fun q => Λ q.out with hΛq
  have hΛq_mk : ∀ h : G, Λq (Quotient.mk'' h) = Λ h := by
    intro h
    have hrel : @Setoid.r _ (MulAction.orbitRel (unip p) G)
        ((Quotient.mk'' h : MulAction.orbitRel.Quotient (unip p) G).out) h := Quotient.mk_out' h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    simp only [hΛq]
    rw [← hn, Subgroup.smul_def, smul_eq_mul, hΛinv]
  have hΛqm : Measurable Λq := by
    refine measurable_from_quotient.mpr ?_
    have : Λq ∘ Quotient.mk'' = Λ := funext hΛq_mk
    rw [this]; exact hΛm

  have hunf := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ₂ (unip p) (isClosed_unip p) μN Γ hΓm
  have hΛq_fin : ∫⁻ q, Λq q ∂(HaarQuotient.measure μ₂ (unip p) μN) ≠ ∞ := by
    simp only [hΛq, hΛ]
    rw [← hunf]; exact hΓfin
  have hae_q : ∀ᵐ q ∂(HaarQuotient.measure μ₂ (unip p) μN), Λq q < ∞ := ae_lt_top hΛqm hΛq_fin
  have hmeas : HaarQuotient.measure μ₂ (unip p) μN
      = Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient (unip p) G)
          (μ₂.withDensity (HaarQuotient.density (unip p) μN)) := rfl
  rw [hmeas] at hae_q
  have hae_G : ∀ᵐ h ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN)), Λ h < ∞ := by
    have := ae_of_ae_map (measurable_quotient_mk''.aemeasurable) hae_q
    filter_upwards [this] with h hh
    rwa [hΛq_mk] at hh

  filter_upwards [hae_G] with h hh
  by_cases h0 : cXi p w χ Φ₂ s h = 0
  · exact Or.inl h0
  · right
    have hC0 : ‖cXi p w χ Φ₂ s h‖ₑ ≠ 0 := by simpa using h0
    have hCtop : ‖cXi p w χ Φ₂ s h‖ₑ ≠ ∞ := enorm_ne_top

    have hΛx : Λ h = cN * ∫⁻ x : F, Γ (unipotentGL2 x * h) ∂ν := by
      simp only [hΛ]
      rw [lintegral_unip_eq p ν μN hμN]
      rfl

    have hΓx : ∀ x : F, Γ (unipotentGL2 x * h) = ‖cXi p w χ Φ₂ s h‖ₑ *
        ∫⁻ y, ‖kXi p χ Φ₁ wt (unipotentGL2 x * h) y⁻¹‖ₑ ∂τ := by
      intro x
      simp only [hΓ]
      rw [← lintegral_const_mul' _ _ hCtop]
      congr 1; funext y
      rw [enorm_mul, cXi_unipotent_mul p w χ Φ₂ s hwlaw, enorm_mul, enorm_psiLocal, one_mul]
    have hkm2 : Measurable fun z : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        kXi p χ Φ₁ wt (unipotentGL2 z.1 * h) z.2⁻¹ := by
      have hm : Measurable fun z : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (unipotentGL2 z.1 * h, z.2⁻¹) :=
        (((continuous_unipotentGL2 p).comp continuous_fst).mul continuous_const).measurable.prodMk measurable_snd.inv
      have := (measurable_kXi p hχ hΦ₁ wt).comp hm
      simpa only [Function.comp_def] using this
    have hfin : ∫⁻ x : F, ∫⁻ y, ‖kXi p χ Φ₁ wt (unipotentGL2 x * h) y⁻¹‖ₑ ∂τ ∂ν < ∞ := by
      have h1 : (cN : ℝ≥0∞) * (‖cXi p w χ Φ₂ s h‖ₑ *
          ∫⁻ x : F, ∫⁻ y, ‖kXi p χ Φ₁ wt (unipotentGL2 x * h) y⁻¹‖ₑ ∂τ ∂ν) < ∞ := by
        rw [← lintegral_const_mul' _ _ hCtop]
        simp_rw [← hΓx]
        rwa [← hΛx]
      have h2 : ‖cXi p w χ Φ₂ s h‖ₑ * ∫⁻ x : F, ∫⁻ y, ‖kXi p χ Φ₁ wt (unipotentGL2 x * h) y⁻¹‖ₑ ∂τ ∂ν < ∞ :=
        ENNReal.lt_top_of_mul_ne_top_right h1.ne (ENNReal.coe_ne_zero.mpr hcN.ne')
      exact ENNReal.lt_top_of_mul_ne_top_right h2.ne hC0
    refine ⟨?_, ?_⟩
    · exact (((NumberField.StandardAddChar.continuous_psiLocal ℚ p).measurable.comp measurable_fst).mul hkm2).aestronglyMeasurable
    · show ∫⁻ z, ‖NumberField.StandardAddChar.psiLocal ℚ p z.1 * kXi p χ Φ₁ wt (unipotentGL2 z.1 * h) z.2⁻¹‖ₑ ∂(ν.prod τ) < ∞
      have e : (fun z : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
          ‖NumberField.StandardAddChar.psiLocal ℚ p z.1 * kXi p χ Φ₁ wt (unipotentGL2 z.1 * h) z.2⁻¹‖ₑ)
          = fun z => ‖kXi p χ Φ₁ wt (unipotentGL2 z.1 * h) z.2⁻¹‖ₑ := by
        funext z; rw [enorm_mul, enorm_psiLocal, one_mul]
      rw [e, lintegral_prod _ hkm2.enorm.aemeasurable]
      exact hfin

theorem mainW :
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure]
      (μN₂ : Measure (unip p)) [μN₂.IsHaarMeasure]
      (ν : Measure F) [ν.IsAddHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
      ∀ (w : G → ℂ) (_hwlc : IsLocallyConstant w)
        (_hwlaw : ∀ (x : F) (g : G), w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
        (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (_hχ : ∀ i, IsLocallyConstant (χ i))
        (Φ₁ : (Fin 2 → F) → ℂ) (_hΦ₁ : IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁)
        (Φ₂ : (Fin 2 → F) → ℂ) (_hΦ₂ : IsLocallyConstant Φ₂)
        (wt : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ)
        (s : ℂ),
        Integrable (kerW p w χ Φ₁ Φ₂ wt s) (μ₂.prod (mulHaar p)) →
        Integrable (fun h : G =>
            (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((adet p h : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∫ t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ,
                wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
                  (∫ y : F, Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + y * (h : Mat) 1 j) *
                      NumberField.StandardAddChar.psiLocal ℚ p ((t : F)⁻¹ * y) ∂ν) *
                  ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(mulHaar p)) *
              (w h * Φ₂ ((h : Mat) 1)) * ((adet p h : ℝ) : ℂ) ^ s)
          (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) ∧
        ∫ h, (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((adet p h : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∫ t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ,
                wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
                  (∫ y : F, Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + y * (h : Mat) 1 j) *
                      NumberField.StandardAddChar.psiLocal ℚ p ((t : F)⁻¹ * y) ∂ν) *
                  ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(mulHaar p)) *
              (w h * Φ₂ ((h : Mat) 1)) * ((adet p h : ℝ) : ℂ) ^ s
          ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) =
        c * ∫ g, outerW p χ Φ₁ Φ₂ s g * (∫ y, innerW p w χ wt s g y ∂(mulHaar p)) ∂μ₂ := by
  intro μ₂ _ μN₂ _ ν _
  haveI : μN₂.IsMulRightInvariant := isMulRightInvariant_unip p μN₂
  obtain ⟨cN, hcN, hμN⟩ := exists_eq_smul_unipMeasure p ν μN₂
  refine ⟨(cN : ℝ)⁻¹, inv_pos.mpr hcN, ?_⟩
  intro w hwlc hwlaw χ hχ Φ₁ hΦ₁ Φ₂ hΦ₂ wt s hK
  have hcN0 : (cN : ℂ) ≠ 0 := by exact_mod_cast hcN.ne'

  set τ := mulHaar p with hτ
  set C : G → ℂ := cXi p w χ Φ₂ s with hC
  set k : G → (HeightOneSpectrum.adicCompletion ℚ p)ˣ → ℂ := kXi p χ Φ₁ wt with hk
  set Fk : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G → ℂ := fun q => C q.2 * k q.2 q.1⁻¹ with hFk

  have hK1 : Integrable (fun q : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G => kerW p w χ Φ₁ Φ₂ wt s q.swap)
      (τ.prod μ₂) := hK.swap
  have hFk_eq : (fun q : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G => kerW p w χ Φ₁ Φ₂ wt s (shear p q).swap) = Fk := by
    funext q
    simp only [shear_apply, Prod.swap_prod_mk, hFk, hC, hk]
    exact kerW_shear p w χ Φ₁ Φ₂ wt s q.1 q.2
  have hFk_int : Integrable Fk (τ.prod μ₂) := by
    rw [← hFk_eq]
    exact ((measurePreserving_shear p μ₂).integrable_comp_emb (shear p).measurableEmbedding
      (g := fun r : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G => kerW p w χ Φ₁ Φ₂ wt s r.swap)).mpr hK1
  have hI1 : ∫ q, kerW p w χ Φ₁ Φ₂ wt s q ∂(μ₂.prod τ) = ∫ q, Fk q ∂(τ.prod μ₂) := by
    calc ∫ q, kerW p w χ Φ₁ Φ₂ wt s q ∂(μ₂.prod τ)
        = ∫ z, kerW p w χ Φ₁ Φ₂ wt s z.swap ∂(τ.prod μ₂) := (integral_prod_swap _).symm
      _ = ∫ z, (fun r : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × G => kerW p w χ Φ₁ Φ₂ wt s r.swap) (shear p z) ∂(τ.prod μ₂) :=
          ((measurePreserving_shear p μ₂).integral_comp' _).symm
      _ = ∫ q, Fk q ∂(τ.prod μ₂) := by rw [← hFk_eq]

  have hΞ_eq : (fun h : G => ∫ y, Fk (y, h) ∂τ) = Xi p w χ Φ₁ Φ₂ wt s := by
    funext h; rfl
  have hΞi : Integrable (Xi p w χ Φ₁ Φ₂ wt s) μ₂ := by
    rw [← hΞ_eq]; exact hFk_int.integral_prod_right
  have hΞm : Measurable (Xi p w χ Φ₁ Φ₂ wt s) := measurable_Xi p hwlc hχ hΦ₁.1 hΦ₂ wt s
  have hI2 : ∫ q, Fk q ∂(τ.prod μ₂) = ∫ h, Xi p w χ Φ₁ Φ₂ wt s h ∂μ₂ := by
    rw [integral_prod_symm Fk hFk_int, hΞ_eq]

  have hGJ : ∫ g, outerW p χ Φ₁ Φ₂ s g * (∫ y, innerW p w χ wt s g y ∂τ) ∂μ₂ = ∫ q, kerW p w χ Φ₁ Φ₂ wt s q ∂(μ₂.prod τ) := by
    rw [integral_prod _ hK]
    congr 1; funext g
    rw [← integral_const_mul]
    rfl

  obtain ⟨-, hU1, hU2⟩ := integrable_and_integral_eq_unfold μ₂ (unip p) (isClosed_unip p) μN₂ _ hΞm hΞi

  set R : G → ℂ := fun h =>
    (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((adet p h : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      ∫ t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ,
        wt (Valued.v (t : F))⁻¹ (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det h : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)) *
          (∫ y : F, Φ₁ (fun j : Fin 2 => (t : F) * (h : Mat) 0 j + y * (h : Mat) 1 j) *
              NumberField.StandardAddChar.psiLocal ℚ p ((t : F)⁻¹ * y) ∂ν) *
          ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂τ) *
      (w h * Φ₂ ((h : Mat) 1)) * ((adet p h : ℝ) : ℂ) ^ s with hR
  have hfib : ∀ᵐ h ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂)),
      ∫ n : unip p, Xi p w χ Φ₁ Φ₂ wt s ((n : G) * h) ∂μN₂ = (cN : ℂ) * R h := by
    have hgood := ae_good p μ₂ μN₂ ν hcN hμN hwlc hwlaw hχ hΦ₁.1 hΦ₂ wt s hFk_int
    filter_upwards [hgood] with h hh
    exact fibre_eq p ν μN₂ hμN w hwlaw χ Φ₁ Φ₂ wt s h hh
  have hRint : Integrable R (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) := by
    have h1 : Integrable (fun h => (cN : ℂ)⁻¹ * ∫ n : unip p, Xi p w χ Φ₁ Φ₂ wt s ((n : G) * h) ∂μN₂)
        (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) := hU1.const_mul _
    refine h1.congr ?_
    filter_upwards [hfib] with h hh
    rw [hh, ← mul_assoc, inv_mul_cancel₀ hcN0, one_mul]
  have hstep : ∫ h, R h ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂))
      = ((cN : ℂ))⁻¹ * ∫ h, Xi p w χ Φ₁ Φ₂ wt s h ∂μ₂ := by
    rw [hU2, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hfib] with h hh
    rw [hh, ← mul_assoc, inv_mul_cancel₀ hcN0, one_mul]
  refine ⟨hRint, ?_⟩
  show ∫ h, R h ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) =
    ((cN : ℝ)⁻¹ : ℝ) * ∫ g, outerW p χ Φ₁ Φ₂ s g * (∫ y, innerW p w χ wt s g y ∂τ) ∂μ₂
  rw [hstep, hGJ, hI1, hI2]
  push_cast
  ring

end Main

end RS22UnrefoldW
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta.RS22UnrefoldW"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
      ∀ (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (_hwlc : IsLocallyConstant w)
        (_hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
        (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
        (_hχ : ∀ i, IsLocallyConstant (χ i))
        (Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (_hΦ₁ : IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁)
        (Φ₂ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (_hΦ₂ : IsLocallyConstant Φ₂)
        (ω : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ)
        (s : ℂ),

        Integrable (fun q : GL (Fin 2) (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ =>
            Φ₁ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) *
                ((χ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (ω (Valued.v (q.2 : p.adicCompletion ℚ)) (Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                w (diagOne q.2 * q.1) * ((χ 1 q.2 : ℂˣ) : ℂ) * ((modulus (q.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)))
          (μ₂.prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) →
        Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∫ t : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (t : p.adicCompletion ℚ))⁻¹ (Valued.v (t : p.adicCompletion ℚ) * Valued.v ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  (∫ y : p.adicCompletion ℚ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                      NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂ν) *
                  ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (w h * Φ₂ ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        ∫ h, (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∫ t : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (t : p.adicCompletion ℚ))⁻¹ (Valued.v (t : p.adicCompletion ℚ) * Valued.v ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  (∫ y : p.adicCompletion ℚ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                      NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂ν) *
                  ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (w h * Φ₂ ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) h
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) =
        c *
          ∫ g, Φ₁ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) * ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (∫ y : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (y : p.adicCompletion ℚ)) (Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  w (diagOne y * g) * ((χ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂μ₂ := by
  intro μ₂ _ μN₂ _ ν _
  exact RS22UnrefoldW.mainW p μ₂ μN₂ ν

end
end S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta (solution)
