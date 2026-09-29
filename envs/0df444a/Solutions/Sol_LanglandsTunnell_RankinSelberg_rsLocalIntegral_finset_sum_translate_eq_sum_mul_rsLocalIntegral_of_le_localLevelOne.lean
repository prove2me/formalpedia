-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/962f9d79-7237-54cc-8538-eca617f1d194

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal

open scoped Topology ENNReal NNReal Matrix

namespace KcH1

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G₂ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G₂ := locallyCompactSpace_localGL K v

abbrev kzero : Subgroup G₂ := AdelicDock.localLevelOne (𝓞 K) K v ⊤

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G₂) :
    k ∈ kzero K v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G₂) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral K v h1, isLocalLevelOne_top_of_integral K v h2⟩

theorem valuation_det_of_mem_kzero {k : G₂} (hk : k ∈ kzero K v) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = 1 := by
  rw [mem_kzero_iff] at hk
  have hint : ∀ (m : Mat), (∀ i j, m i j ∈ (O)) → Valued.v m.det ≤ 1 := by
    intro m hm
    rw [Matrix.det_fin_two]
    have h := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm i j)
    calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
        ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
      _ ≤ 1 := by
          refine max_le ?_ ?_
          · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
          · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)
  have h1 := hint _ hk.1
  have h2 := hint _ hk.2
  have hprod : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

theorem modulus_det_of_mem_kzero {k : G₂} (hk : k ∈ kzero K v) :
    (modulus ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) = 1 := by
  rw [coe_modulus_eq_norm, NumberField.FinitePlace.norm_def, valuation_det_of_mem_kzero K v hk, map_one, NNReal.coe_one]

end

end KcH1
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne.KcH1"

namespace KcH1Q

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open KcH1

variable (p : HeightOneSpectrum (𝓞 ℚ))

scoped instance isMulRightInvariant_localHaar (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] :
    μ₂.IsMulRightInvariant :=
  (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂).1

abbrev unip : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)) := (unipotentGL2Hom (R := p.adicCompletion ℚ)).range

theorem continuous_entry (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j :=
  (Units.continuous_val).matrix_elem i j

theorem coe_unip_eq :
    ((unip p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      {g : GL (Fin 2) (p.adicCompletion ℚ) | (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) :
      GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = _
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip : IsClosed ((unip p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
    Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [coe_unip_eq]
  exact ((isClosed_singleton.preimage (continuous_entry p 0 0)).inter
    ((isClosed_singleton.preimage (continuous_entry p 1 0)).inter
      (isClosed_singleton.preimage (continuous_entry p 1 1))))

theorem unip_eq_unipotentGL2 (n : unip p) :
    (n : GL (Fin 2) (p.adicCompletion ℚ)) =
      unipotentGL2 (((n : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) := by
  obtain ⟨z, hz⟩ := n.2
  rw [← hz]
  change (unipotentGL2 z.toAdd : GL (Fin 2) (p.adicCompletion ℚ)) =
    unipotentGL2 (((unipotentGL2 z.toAdd : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1)
  have h01 : (((unipotentGL2 z.toAdd : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) = z.toAdd := by simp [unipotentGL2_coe]
  rw [h01]

theorem unip_comm (m n : unip p) : m * n = n * m := by
  refine Subtype.ext ?_
  change (m : GL (Fin 2) (p.adicCompletion ℚ)) * (n : GL (Fin 2) (p.adicCompletion ℚ)) = (n : _) * (m : _)
  rw [unip_eq_unipotentGL2 p m, unip_eq_unipotentGL2 p n, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem isMulRightInvariant_unip (μN : Measure (unip p)) [μN.IsMulLeftInvariant] : μN.IsMulRightInvariant := by
  refine ⟨fun x => ?_⟩
  have h : (fun y : unip p => y * x) = fun y => x * y := funext fun y => unip_comm p y x
  rw [h]
  exact map_mul_left_eq_self μN x

theorem det_unipotentGL2 (x : p.adicCompletion ℚ) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem continuous_modulus_det :
    Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) := by
  have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) =
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => (((‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ : ℝ)) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

theorem continuous_modulus_det_real :
    Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) := by
  have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))) =
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => (‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ : ℝ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact continuous_norm.comp (Units.continuous_val.matrix_det)

section RightTranslation

variable {p}

theorem rs_translate
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (A B : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hA : Continuous A) (hB : Continuous B)
    (hAlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), A (unipotentGL2 x * g) = θ⁻¹ x * A g)
    (hBlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), B (unipotentGL2 x * g) = θ x * B g)
    (k : GL (Fin 2) (p.adicCompletion ℚ)) (hk : k ∈ kzero ℚ p)
    (hBk : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), B (g * k⁻¹) = B g)
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (μN₂ : Measure (unip p)) [μN₂.IsHaarMeasure] (s : ℂ) :
    (Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (A g * B g) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) ↔
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (A (g * k) * B g) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unip p) μN₂))) ∧
    RSCarrier.rsLocalIntegral μ₂ (unip p) μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s A B =
      RSCarrier.rsLocalIntegral μ₂ (unip p) μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s
        (fun g => A (g * k)) B := by
  haveI : μN₂.IsMulRightInvariant := isMulRightInvariant_unip p μN₂
  haveI : SigmaCompactSpace (unip p) := (isClosed_unip p).sigmaCompactSpace
  have hμh : Measure.map (· * k⁻¹) μ₂ = μ₂ := map_mul_right_eq_self μ₂ k⁻¹
  have hδm : Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) :=
    (continuous_modulus_det_real p).measurable
  have hδpos : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      0 < ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) :=
    fun g => by exact_mod_cast modulus_pos (Units.ne_zero _)
  have hδmul : ∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
      ((modulus ((Matrix.GeneralLinearGroup.det (g * h) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) =
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) *
        ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) := by
    intro g h; rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul]
  have hδH : ∀ x ∈ unip p, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      ((modulus ((Matrix.GeneralLinearGroup.det (x * g) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) =
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) := by
    intro x hx g
    have hx' := unip_eq_unipotentGL2 p ⟨x, hx⟩
    simp only at hx'
    rw [hx', map_mul, det_unipotentGL2, one_mul]
  have hWF : ∀ x ∈ unip p, ∀ g k' : GL (Fin 2) (p.adicCompletion ℚ), A (x * g) * B (x * k') = A g * B k' := by
    intro x hx g k'
    have hx' := unip_eq_unipotentGL2 p ⟨x, hx⟩
    simp only at hx'
    rw [hx', hAlaw, hBlaw, AddChar.inv_apply]
    have h1 : θ (-((x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1)) *
        θ ((x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    calc θ (-((x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1)) * A g *
          (θ ((x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) * B k')
        = (θ (-((x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1)) *
            θ ((x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1)) * (A g * B k') := by ring
      _ = A g * B k' := by rw [h1, one_mul]
  have hcard := RSCarrier.rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
    μ₂ (unip p) (isClosed_unip p) μN₂ k⁻¹ hμh _ hδm hδpos hδmul hδH s A B hA.measurable hB.measurable hWF
  simp only [hBk, inv_inv] at hcard
  have hδk : ((modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) = 1 :=
    modulus_det_of_mem_kzero ℚ p hk
  rw [hδk, Complex.ofReal_one, Complex.one_cpow, one_mul] at hcard
  exact hcard

theorem rs_sum_translate
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (A B : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hA : Continuous A) (hB : Continuous B)
    (hAlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), A (unipotentGL2 x * g) = θ⁻¹ x * A g)
    (hBlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), B (unipotentGL2 x * g) = θ x * B g)
    (Kc : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hKc : Kc ≤ kzero ℚ p)
    (hBK : ∀ k ∈ Kc, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), B (g * k) = B g)
    {ι : Type*} (T : Finset ι) (c : ι → ℝ) (kf : ι → GL (Fin 2) (p.adicCompletion ℚ)) (hkf : ∀ i ∈ T, kf i ∈ Kc)
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (μN₂ : Measure (unip p)) [μN₂.IsHaarMeasure] (s : ℂ)
    (hint : Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (A g * B g) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unip p) μN₂))) :
    Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((∑ i ∈ T, (c i : ℂ) * A (g * kf i)) * B g) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) ∧
    RSCarrier.rsLocalIntegral μ₂ (unip p) μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s
        (fun g => ∑ i ∈ T, (c i : ℂ) * A (g * kf i)) B =
      ((∑ i ∈ T, c i : ℝ) : ℂ) * RSCarrier.rsLocalIntegral μ₂ (unip p) μN₂
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s A B := by
  set D := μ₂.withDensity (HaarQuotient.density (unip p) μN₂) with hD
  set δ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
    ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) with hδ
  have hterm : ∀ i ∈ T,
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (A (g * kf i) * B g) * δ g) D ∧
      (∫ g, (A (g * kf i) * B g) * δ g ∂D) = ∫ g, (A g * B g) * δ g ∂D := by
    intro i hi
    have hk : kf i ∈ kzero ℚ p := hKc (hkf i hi)
    have hBk : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), B (g * (kf i)⁻¹) = B g :=
      fun g => hBK _ (Kc.inv_mem (hkf i hi)) g
    have h := rs_translate θ A B hA hB hAlaw hBlaw (kf i) hk hBk μ₂ μN₂ s
    refine ⟨h.1.mp hint, ?_⟩
    have h2 := h.2
    unfold RSCarrier.rsLocalIntegral at h2
    exact h2.symm
  have hfun : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((∑ i ∈ T, (c i : ℂ) * A (g * kf i)) * B g) * δ g) =
      fun g => ∑ i ∈ T, (c i : ℂ) * ((A (g * kf i) * B g) * δ g) := by
    funext g
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact integrable_finsetSum _ fun i hi => (hterm i hi).1.const_mul _
  · unfold RSCarrier.rsLocalIntegral
    rw [hfun, integral_finsetSum _ (fun i hi => (hterm i hi).1.const_mul _)]
    simp_rw [integral_const_mul]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [(hterm i hi).2]

end RightTranslation
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne.KcH1"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne.KcH1"

end KcH1Q
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne.KcH1 P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne.KcH1Q"

attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open KcH1 KcH1Q in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (A B : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hA : Continuous A) (hB : Continuous B)
    (hAlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), A (unipotentGL2 x * g) = θ⁻¹ x * A g)
    (hBlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), B (unipotentGL2 x * g) = θ x * B g)
    (Kc : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hKc : Kc ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (hBK : ∀ k ∈ Kc, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), B (g * k) = B g)
    {ι : Type} (T : Finset ι) (c : ι → ℝ) (kf : ι → GL (Fin 2) (p.adicCompletion ℚ)) (hkf : ∀ i ∈ T, kf i ∈ Kc) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure] (s : ℂ),
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (A g * B g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((∑ i ∈ T, (c i : ℂ) * A (g * kf i)) * B g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s
          (fun g => ∑ i ∈ T, (c i : ℂ) * A (g * kf i)) B =
        ((∑ i ∈ T, c i : ℝ) : ℂ) *
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s A B := by
  intro μ₂ _ μN₂ _ s hint
  haveI := locallyCompactSpace_localGL ℚ p
  exact rs_sum_translate θ A B hA hB hAlaw hBlaw Kc hKc hBK T c kf hkf μ₂ μN₂ s hint

end S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne (solution)
