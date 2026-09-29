-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d4fae86a-21a8-53cc-aea4-8793f2d547e8

import Theorems.Thm_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
import Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Ws23HLInt

section Basic

open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def qR : ℝ := ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ)

theorem one_lt_qR : 1 < qR v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [qR]; exact_mod_cast this

theorem qR_pos : 0 < qR v := zero_lt_one.trans (one_lt_qR v)

theorem qR_eq_natCast : qR v = (Ideal.absNorm v.asIdeal : ℝ) := NNReal.coe_natCast _

theorem norm_eq_zpow_of_v_eq_exp (x : F) (m : ℤ) (hx : Valued.v x = WithZero.exp m) : ‖x‖ = qR v ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    NNReal.coe_zpow, qR]
  congr 1

theorem coe_modulus_eq_norm (x : F) : ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

theorem exists_modulus_det_eq_zpow (h : G) : ∃ m : ℤ,
    ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F) : ℝ≥0) : ℝ) = qR v ^ m := by
  have hne : Valued.v ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  refine ⟨WithZero.log (Valued.v ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F)), ?_⟩
  rw [coe_modulus_eq_norm]
  exact norm_eq_zpow_of_v_eq_exp v _ _ (WithZero.exp_log hne).symm

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

theorem unip_comm (a b : (unip v : Subgroup G)) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  refine Subtype.ext ?_
  change (a : G) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem unipotent_eq_unipotentGL2 (x : F) : UnramifiedWhittaker.unipotent x = (unipotentGL2 x : G) := by
  refine Units.ext ?_
  rw [unipotentGL2_coe]
  simp [UnramifiedWhittaker.unipotent]

theorem det_unipotentGL2 (x : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

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
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun g : G => (((g⁻¹ : G)) : Mat)ᵀ
    exact (Units.continuous_coe_inv (M := Mat)).matrix_transpose
  · change Continuous fun g : G => ((g : G) : Mat)ᵀ
    exact (Units.continuous_val (M := Mat)).matrix_transpose

theorem continuous_transposeInv3 : Continuous fun g : G₃ => transposeInv3 g := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun g : G₃ => (((g⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F)ᵀ
    exact (Units.continuous_coe_inv (M := Matrix (Fin 3) (Fin 3) F)).matrix_transpose
  · change Continuous fun g : G₃ => ((g : G₃) : Matrix (Fin 3) (Fin 3) F)ᵀ
    exact (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) F)).matrix_transpose

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

end Basic

section Cyclic

open LanglandsTunnell.CubicInduction

variable {A : Type*} [CommRing A]

theorem law_of_mem_gl3CyclicSubspace {ψ : AddChar A ℂ} {W₀ W : GL (Fin 3) A → ℂ} (h₀ : IsGL3PsiWhittakerFn ψ W₀)
    (hW : W ∈ gl3CyclicSubspace W₀) : IsGL3PsiWhittakerFn ψ W := by
  have hmem : W₀ ∈ gl3PsiWhittakerFnSpace A ℂ ψ := (mem_gl3PsiWhittakerFnSpace_iff ψ W₀).mpr h₀
  have hle : gl3CyclicSubspace W₀ ≤ gl3PsiWhittakerFnSpace A ℂ ψ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h hmem
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ W).mp (hle hW)

theorem smooth_of_mem_span_translates {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {w₀ w : H → ℂ}
    (hsm : ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g, w₀ (g * k) = w₀ g)
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : H => fun g : H => w₀ (g * h))) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g, w (g * k) = w g := by
  obtain ⟨U₀, hU₀, hfix⟩ := hsm
  refine Submodule.span_induction (p := fun (w : H → ℂ) _ =>
      ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g, w (g * k) = w g) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨h, rfl⟩
    refine ⟨U₀.map (MulAut.conj h).toMonoidHom, ?_, ?_⟩
    · have : ((U₀.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) =
          (Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹) '' (U₀ : Set H) := by
        ext x
        simp only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Set.mem_image, SetLike.mem_coe,
          Homeomorph.trans_apply, Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]
      rw [this]
      exact (Homeomorph.isOpenMap _) _ hU₀
    · rintro k ⟨u, hu, rfl⟩ g
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have : g * (h * u * h⁻¹) * h = g * h * u := by group
      rw [this, hfix u hu]
  · exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  · rintro w₁ w₂ _ _ ⟨U₁, hU₁, h₁⟩ ⟨U₂, hU₂, h₂⟩
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
    simp only [Pi.add_apply, h₁ k hk.1 g, h₂ k hk.2 g]
  · rintro c w _ ⟨U, hU, h⟩
    exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, h k hk g]⟩

theorem smooth_of_mem_gl3CyclicSubspace [TopologicalSpace A] [IsTopologicalRing A] {W₀ W : GL (Fin 3) A → ℂ}
    (hsm : ∃ U : Subgroup (GL (Fin 3) A), IsOpen (U : Set (GL (Fin 3) A)) ∧ ∀ k ∈ U, ∀ g, W₀ (g * k) = W₀ g)
    (hW : W ∈ gl3CyclicSubspace W₀) :
    ∃ U : Subgroup (GL (Fin 3) A), IsOpen (U : Set (GL (Fin 3) A)) ∧ ∀ k ∈ U, ∀ g, W (g * k) = W g :=
  smooth_of_mem_span_translates hsm hW

variable {F₀ : Type*} [Field F₀]

theorem law_of_mem_span_range (ψ : AddChar F₀ ℂ) (w₀ : GL (Fin 2) F₀ → ℂ)
    (hlaw : ∀ (x : F₀) (g : GL (Fin 2) F₀), w₀ (unipotent x * g) = ψ x * w₀ g)
    {W : GL (Fin 2) F₀ → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) F₀ => fun g : GL (Fin 2) F₀ => w₀ (g * h))) :
    ∀ (x : F₀) (g : GL (Fin 2) F₀), W (unipotent x * g) = ψ x * W g := by
  refine Submodule.span_induction (p := fun W _ => ∀ (x : F₀) (g : GL (Fin 2) F₀),
      W (unipotent x * g) = ψ x * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ x g
    simp only [mul_assoc, hlaw]
  · intro x g
    simp
  · intro W₁ W₂ _ _ h₁ h₂ x g
    simp only [Pi.add_apply, h₁ x g, h₂ x g, mul_add]
  · intro c W _ hW' x g
    simp only [Pi.smul_apply, hW' x g, smul_eq_mul]
    ring

end Cyclic

section Integrands

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def modC (g : G) : ℂ :=
  ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ)

def modR (g : G) : ℝ :=
  ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ v) : ℝ))

theorem modC_eq (g : G) : modC g = ((modR g : ℝ) : ℂ) := rfl

theorem modR_nonneg (g : G) : 0 ≤ modR g := NNReal.coe_nonneg _

theorem modR_mul (g h : G) : modR (g * h) = modR g * modR h := by
  unfold modR
  rw [map_mul, Units.val_mul, LanglandsTunnell.TateLocal.modulus_mul, NNReal.coe_mul]

theorem modC_mul (g h : G) : modC (g * h) = modC g * modC h := by
  rw [modC_eq, modC_eq, modC_eq, modR_mul, Complex.ofReal_mul]

theorem modR_pos (g : G) : 0 < modR g := by
  unfold modR
  exact_mod_cast LanglandsTunnell.TateLocal.modulus_pos (K := F) (Units.ne_zero _)

theorem modC_ne_zero (g : G) : modC g ≠ 0 := by
  rw [modC_eq]
  exact_mod_cast (modR_pos g).ne'

theorem modC_cpow_mul (g h : G) (r : ℂ) : modC (g * h) ^ r = modC g ^ r * modC h ^ r := by
  rw [modC_mul, modC_eq, modC_eq, Complex.mul_cpow_ofReal_nonneg (modR_nonneg g) (modR_nonneg h)]

def phiP (W : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) (g : G) : ℂ := (W (iotaGL g) * w g) * modC g ^ (s - 1 / 2)

def phiD (W : LocalGL3 v → ℂ) (w : G → ℂ) (w₀p : G) (s : ℂ) (g : G) : ℂ :=
  (dualWhittakerFn3 W (iotaGL g) * (modC g * w (w₀p * transposeInvN (Fin 2) g))) * modC g ^ (s - 1 / 2)

theorem continuous_modC : Continuous (modC (v := v)) := by
  have : (modC (v := v)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [modC, coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

theorem eq_gl2Weyl_of_coe {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) : w₀p = gl2Weyl :=
  Units.ext (hw₀p.trans (gl2Weyl_val).symm)

theorem phiP_unipotent_mul {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    {w : G → ℂ} (hw : ∀ (x : F) (g : G), w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w g)
    (s : ℂ) : ∀ (x : ↥(unip v)) (g : G), phiP W w s ((x : G) * g) = phiP W w s g := by
  rintro ⟨_, ⟨z, rfl⟩⟩ g
  have hx : (unipotentGL2Hom z : G) = unipotentGL2 z.toAdd := rfl
  show phiP W w s (unipotentGL2Hom z * g) = phiP W w s g
  unfold phiP modC
  rw [hx, map_mul, iotaGL_unipotentGL2, hW, map_mul, det_unipotentGL2, one_mul, ← unipotent_eq_unipotentGL2, hw,
    AddChar.inv_apply, add_zero]
  congr 1
  calc (NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * W (iotaGL g) *
        ((NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd * w g)
      = ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd) *
          (W (iotaGL g) * w g) := by ring
    _ = W (iotaGL g) * w g := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem coe_transposeInv3_upperUnipotent3 (x y z : F) :
    ((transposeInv3 (upperUnipotent3 x y z) : G₃) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
  have hinv : (((upperUnipotent3 x y z)⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F) = !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  change (((upperUnipotent3 x y z)⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F)ᵀ = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem transposeInv3_mul (g h : G₃) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change (((g * h)⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F)ᵀ =
    (((g⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F))ᵀ * (((h⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F))ᵀ
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : G₃) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : G₃) : Matrix (Fin 3) (Fin 3) F))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem longWeyl3_mul_self : (longWeyl3 : G₃) * longWeyl3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem isGL3PsiWhittakerFn_dualWhittakerFn3 {ψ : AddChar F ℂ} {W : G₃ → ℂ} (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) :
    IsGL3PsiWhittakerFn ψ (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul]
  have hconj : (longWeyl3 : G₃) * transposeInv3 (upperUnipotent3 x y z) * longWeyl3 = upperUnipotent3 (-y) (-x) (x * y - z) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_transposeInv3_upperUnipotent3, longWeyl3_coe, upperUnipotent3_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h : (longWeyl3 : G₃) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
      upperUnipotent3 (-y) (-x) (x * y - z) * (longWeyl3 * transposeInv3 g) := by
    rw [← hconj]
    have : (longWeyl3 : G₃) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
        longWeyl3 * transposeInv3 (upperUnipotent3 x y z) * longWeyl3⁻¹ * (longWeyl3 * transposeInv3 g) := by group
    rw [this, inv_eq_of_mul_eq_one_right (longWeyl3_mul_self (v := v))]
  rw [h, hW, AddChar.inv_apply]
  congr 2
  ring

theorem dualWhittakerFn3_iotaGL_unipotent_mul {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W) (x : F) (X : G₃) :
    dualWhittakerFn3 W (iotaGL (unipotentGL2 x : G) * X) =
      NumberField.StandardAddChar.psiLocal ℚ v x * dualWhittakerFn3 W X := by
  have hWd : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) (dualWhittakerFn3 W) :=
    isGL3PsiWhittakerFn_dualWhittakerFn3 hW
  rw [iotaGL_unipotentGL2, hWd, add_zero]

theorem phiD_unipotent_mul {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    {w : G → ℂ} (hw : ∀ (x : F) (g : G), w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w g)
    {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (s : ℂ) :
    ∀ (x : ↥(unip v)) (g : G), phiD W w w₀p s ((x : G) * g) = phiD W w w₀p s g := by
  rintro ⟨_, ⟨z, rfl⟩⟩ g
  have hx : (unipotentGL2Hom z : G) = unipotentGL2 z.toAdd := rfl
  show phiD W w w₀p s (unipotentGL2Hom z * g) = phiD W w w₀p s g

  have hconj : w₀p * transposeInvN (Fin 2) (unipotentGL2 z.toAdd * g) =
      UnramifiedWhittaker.unipotent (-z.toAdd) * (w₀p * transposeInvN (Fin 2) g) := by
    rw [transposeInvN_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    refine Units.ext ?_
    have hinv : (((unipotentGL2 z.toAdd : G)⁻¹ : G) : Mat) = !![1, -z.toAdd; 0, 1] := by
      rw [← hx, ← map_inv]; rfl
    rw [Units.val_mul, Units.val_mul, coe_transposeInvN, hinv, hw₀p]
    simp only [UnramifiedWhittaker.unipotent, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  unfold phiD modC
  rw [hx, map_mul, dualWhittakerFn3_iotaGL_unipotent_mul hW, map_mul, det_unipotentGL2, one_mul, hconj, hw]
  congr 1
  calc (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd * dualWhittakerFn3 W (iotaGL g) *
        (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) *
          ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * w (w₀p * transposeInvN (Fin 2) g)))
      = ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd) *
          (dualWhittakerFn3 W (iotaGL g) *
            (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
              HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g))) := by ring
    _ = dualWhittakerFn3 W (iotaGL g) *
        (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem measurable_phiP [MeasurableSpace G] [BorelSpace G] {W : LocalGL3 v → ℂ} (hWc : Continuous W) {w : G → ℂ}
    (hwc : Continuous w) (s : ℂ) : Measurable (phiP W w s) :=
  ((hWc.comp (continuous_iotaGL v)).mul hwc).measurable.mul (continuous_modC.measurable.pow_const _)

theorem measurable_phiD [MeasurableSpace G] [BorelSpace G] {W : LocalGL3 v → ℂ} (hWc : Continuous W) {w : G → ℂ}
    (hwc : Continuous w) (w₀p : G) (s : ℂ) : Measurable (phiD W w w₀p s) := by
  have h1 : Continuous fun g : G => dualWhittakerFn3 W (iotaGL g) := by
    change Continuous fun g : G => W (longWeyl3 * transposeInv3 (iotaGL g))
    exact hWc.comp (continuous_const.mul ((continuous_transposeInv3 v).comp (continuous_iotaGL v)))
  have h2 : Continuous fun g : G => modC g * w (w₀p * transposeInvN (Fin 2) g) :=
    continuous_modC.mul (hwc.comp (continuous_const.mul (continuous_transposeInvN v)))
  exact (h1.mul h2).measurable.mul (continuous_modC.measurable.pow_const _)

theorem iotaGL_transposeInvN (g : G) : iotaGL (transposeInvN (Fin 2) g) = transposeInv3 (iotaGL g) := by
  refine Units.ext ?_
  change embedMat2 (((g⁻¹ : G) : Mat)ᵀ) = ((((iotaGL g)⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F)ᵀ
  rw [← map_inv, coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

theorem phiP_translate (W : LocalGL3 v → ℂ) (w : G → ℂ) (h : G) (s : ℂ) (g : G) :
    phiP (fun x => W (x * (iotaGL h)⁻¹)) w s (g * h) = phiP W (fun x => w (x * h)) s g * modC h ^ (s - 1 / 2) := by
  simp only [phiP, map_mul, mul_inv_cancel_right, modC_cpow_mul]
  ring

theorem phiD_translate (W : LocalGL3 v → ℂ) (w : G → ℂ) (w₀p h : G) (s : ℂ) (g : G) :
    phiD (fun x => W (x * (iotaGL h)⁻¹)) w w₀p s (g * transposeInvN (Fin 2) h) =
      phiD W (fun x => w (x * h)) w₀p s g * (modC (transposeInvN (Fin 2) h) * modC (transposeInvN (Fin 2) h) ^ (s - 1 / 2)) := by
  have hdual : dualWhittakerFn3 (fun x => W (x * (iotaGL h)⁻¹)) (iotaGL (g * transposeInvN (Fin 2) h)) =
      dualWhittakerFn3 W (iotaGL g) := by
    rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, map_mul, transposeInv3_mul, iotaGL_transposeInvN,
      transposeInv3_transposeInv3, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  simp only [phiD]
  rw [hdual, transposeInvN_mul, transposeInvN_transposeInvN, ← mul_assoc w₀p, modC_cpow_mul, modC_mul]
  ring

end Integrands

section Core

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal

theorem local_core
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (b : ℕ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)
    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ w₂ ∈ Submodule.span ℂ
          (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W₃ (iotaGL g) * w₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := by
  intro μ₂ _ μN₂ _ w₂ hw₂
  classical
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI := locallyCompactSpace_localGL ℚ p
  haveI := secondCountableTopology_localGL p
  haveI : μN₂.IsMulRightInvariant :=
    ⟨fun g => by
      have : (fun h : ↥(unip p) => h * g) = fun h => g * h := funext fun h => unip_comm p h g
      rw [this]
      exact map_mul_left_eq_self μN₂ g⟩
  set ν : Measure (GL (Fin 2) (p.adicCompletion ℚ)) :=
    μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂) with hν

  have hK₁o : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (p.asIdeal ^ b) (pow_ne_zero b p.ne_bot)).2
  have hcont3 : ∀ W ∈ gl3CyclicSubspace W₃base, Continuous W := fun W hW => by
    obtain ⟨U, hU, hfix⟩ := smooth_of_mem_gl3CyclicSubspace hW₃sm hW
    exact continuous_of_rightInvariant hU hfix
  have hw₂c : Continuous w₂base := continuous_of_rightInvariant hK₁o hw₂K

  have hcentralR : ∀ (t : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω t : ℂˣ) : ℂ) * w₂base g := by
    intro t g
    have hcomm : g * Matrix.GeneralLinearGroup.scalar (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) t * g := by
      refine Units.ext ?_
      change (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Matrix.scalar (Fin 2) (t : p.adicCompletion ℚ) =
        Matrix.scalar (Fin 2) (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
      exact ((Matrix.scalar_commute (t : p.adicCompletion ℚ) (fun r => mul_comm _ _)
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).eq).symm
    rw [hcomm, hcentral]

  have hbase : ∀ W₃ ∈ gl3CyclicSubspace W₃base, ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re → Integrable (phiP W₃ w₂base s) ν := by
    intro W₃ hW₃
    refine Submodule.span_induction (p := fun (W : LocalGL3 p → ℂ) _ =>
        ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re → Integrable (phiP W w₂base s) ν) ?_ ?_ ?_ ?_ hW₃
    ·
      rintro _ ⟨g₃, rfl⟩
      obtain ⟨σ₂, hσ₂⟩ := LanglandsTunnell.CubicInduction.exists_forall_integrable_rsLocalIntegrand_of_gauge p _ rfl W₃base hW₃law
        hW₃sm hWgauge hπ hϖ b w₂base hw₂law (fun k g hk => hw₂K k hk g) ω hcentralR hw₂gr g₃ μ₂ μN₂
      exact ⟨σ₂, fun s hs => hσ₂ s hs⟩
    ·
      refine ⟨0, fun s _ => ?_⟩
      have : phiP (0 : LocalGL3 p → ℂ) w₂base s = 0 := by funext g; simp [phiP]
      rw [this]; exact integrable_zero _ _ _
    ·
      intro W W' _ _ hW hW'
      obtain ⟨σ₂, h1⟩ := hW
      obtain ⟨σ₂', h1'⟩ := hW'
      have hadd : ∀ s, phiP (W + W') w₂base s = fun g => phiP W w₂base s g + phiP W' w₂base s g := by
        intro s; funext g; simp only [phiP, Pi.add_apply]; ring
      refine ⟨max σ₂ σ₂', fun s hs => ?_⟩
      rw [hadd s]
      exact (h1 s ((le_max_left _ _).trans_lt hs)).add (h1' s ((le_max_right _ _).trans_lt hs))
    ·
      intro c W _ hW
      obtain ⟨σ₂, h1⟩ := hW
      have hsm : ∀ s, phiP (c • W) w₂base s = fun g => c * phiP W w₂base s g := by
        intro s; funext g; simp only [phiP, Pi.smul_apply, smul_eq_mul]; ring
      refine ⟨σ₂, fun s hs => ?_⟩
      rw [hsm s]; exact (h1 s hs).const_mul c

  let Pack : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) → Prop := fun w =>
    ∀ W₃ ∈ gl3CyclicSubspace W₃base, ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re → Integrable (phiP W₃ w s) ν
  suffices hPack : Pack w₂ by
    intro W₃ hW₃
    exact hPack W₃ hW₃
  refine Submodule.span_induction (p := fun w _ => Pack w) ?_ ?_ ?_ ?_ hw₂
  ·
    rintro _ ⟨h, rfl⟩ W₃ hW₃
    set W₃' : LocalGL3 p → ℂ := fun x => W₃ (x * (iotaGL h)⁻¹) with hW₃'
    have hW₃'mem : W₃' ∈ gl3CyclicSubspace W₃base := gl3AmbientRightTranslate_mem_gl3CyclicSubspace W₃base _ hW₃
    obtain ⟨σ₂, hint⟩ := hbase W₃' hW₃'mem
    have hlaw' : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃' := law_of_mem_gl3CyclicSubspace hW₃law hW₃'mem
    have hW₃'c : Continuous W₃' := hcont3 _ hW₃'mem
    have hmP : ∀ s, Measurable (phiP W₃' w₂base s) := fun s => measurable_phiP hW₃'c hw₂c s
    have hNP : ∀ s, ∀ (x : ↥(unip p)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        phiP W₃' w₂base s ((x : GL (Fin 2) (p.adicCompletion ℚ)) * g) = phiP W₃' w₂base s g :=
      fun s => phiP_unipotent_mul hlaw' hw₂law s
    obtain ⟨c₁, hc₁0, hc₁⟩ := HaarQuotient.exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul (E := ℂ) μ₂
      (unipotentGL2Hom (R := p.adicCompletion ℚ)).range (isClosed_unip p) μN₂ h
    have hΦP : ∀ s, phiP W₃ (fun x => w₂base (x * h)) s =
        fun g => phiP W₃' w₂base s (g * h) * (modC h ^ (s - 1 / 2))⁻¹ := by
      intro s; funext g
      rw [phiP_translate, mul_assoc, mul_inv_cancel₀, mul_one]
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl (modC_ne_zero h))
    refine ⟨σ₂, fun s hs => ?_⟩
    rw [hΦP s]
    exact (((hc₁ _ (hmP s) (hNP s)).1.mpr (hint s hs)).mul_const _)
  ·
    intro W₃ hW₃
    refine ⟨0, fun s _ => ?_⟩
    have : phiP W₃ (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) s = 0 := by funext g; simp [phiP]
    rw [this]; exact integrable_zero _ _ _
  ·
    intro w w' _ _ hPw hPw' W₃ hW₃
    obtain ⟨σ₂, h1⟩ := hPw W₃ hW₃
    obtain ⟨σ₂', h1'⟩ := hPw' W₃ hW₃
    have haddP : ∀ s, phiP W₃ (w + w') s = fun g => phiP W₃ w s g + phiP W₃ w' s g := by
      intro s; funext g; simp only [phiP, Pi.add_apply]; ring
    refine ⟨max σ₂ σ₂', fun s hs => ?_⟩
    rw [haddP s]; exact (h1 s ((le_max_left _ _).trans_lt hs)).add (h1' s ((le_max_right _ _).trans_lt hs))
  ·
    intro c w _ hPw W₃ hW₃
    obtain ⟨σ₂, h1⟩ := hPw W₃ hW₃
    have hsmP : ∀ s, phiP W₃ (c • w) s = fun g => c * phiP W₃ w s g := by
      intro s; funext g; simp only [phiP, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨σ₂, fun s hs => ?_⟩
    rw [hsmP s]; exact (h1 s hs).const_mul c

end Core

end Ws23HLInt
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch.Ws23HLInt"

namespace Ws23HLInt

section GL3
open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal

theorem det_upperUnipotent3 {A : Type*} [CommRing A] (x y z : A) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Units.val_one, Matrix.det_fin_three]
  simp

private def _root_.Ws23HLInt.twist (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  fun x => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x

p2m_export "Ws23HLInt" "twist"

theorem isGL3PsiWhittakerFn_twist (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    {ψv : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψv W) :
    IsGL3PsiWhittakerFn ψv (twist χA v W) := by
  intro x y z g
  simp only [twist]
  rw [map_mul, det_upperUnipotent3, one_mul, hW x y z g]
  ring

theorem norm_localChar_eq_one (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) :
    ‖((NumberField.TateGlobal.localChar χA v u : ℂˣ) : ℂ)‖ = 1 := by
  rw [NumberField.TateGlobal.localChar_apply]
  exact hχA.2.2 _

theorem twist_gauge (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (p : HeightOneSpectrum (𝓞 ℚ)) {W : LocalGL3 p → ℂ}
    (hW : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → twist χA p W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖twist χA p W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
  obtain ⟨B, t, C, hB⟩ := hW
  refine ⟨B, t, C, fun h => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · simp only [twist, (hB h).1 hb, mul_zero]
  · simp only [twist, norm_mul, norm_localChar_eq_one χA hχA, one_mul]
    exact (hB h).2 hb

theorem isOpen_ker_localChar_det (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v n, NumberField.TateGlobal.localChar χA v u = 1)
    (z : v.adicCompletion ℚ) (hz0 : Valued.v z ≠ 0) (hz : Valued.v z ≤ WithZero.exp (-(n : ℤ))) :
    IsOpen (((NumberField.TateGlobal.localChar χA v).comp
      (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (v.adicCompletion ℚ)ˣ)).ker : Set (LocalGL3 v)) := by
  set H := ((NumberField.TateGlobal.localChar χA v).comp
      (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (v.adicCompletion ℚ)ˣ)).ker
  apply Subgroup.isOpen_of_mem_nhds H (g := 1)
  have hz0' : z ≠ 0 := fun h => hz0 (by rw [h, map_zero])
  have hball : {y : v.adicCompletion ℚ | Valued.v (y - 1) < Valued.v z} ∈ nhds (1 : v.adicCompletion ℚ) := by
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 (Valued.v.restrict z) ((Valuation.ne_zero_iff _).2 hz0'), fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq, Units.val_mk0] at hy
    exact (Valuation.restrict_lt_iff _).1 hy
  have hcont : Continuous fun k : LocalGL3 v => ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) :=
    Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det
  have h1det : ((Matrix.GeneralLinearGroup.det (1 : LocalGL3 v) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [map_one, Units.val_one]
  have hpre := hcont.continuousAt.preimage_mem_nhds (by rw [h1det]; exact hball)
  refine Filter.mem_of_superset hpre ?_
  intro k hk
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hk
  show k ∈ H
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  apply hn
  rw [LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff]
  have hle1 : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by omega)
  have h1 : Valued.v ((1 : v.adicCompletion ℚ)) = 1 := Valuation.map_one _
  have hlt : Valued.v (((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) <
      Valued.v ((1 : v.adicCompletion ℚ)) := by
    rw [h1]; exact lt_of_lt_of_le hk (hz.trans hle1)
  refine ⟨?_, Or.inr (hk.le.trans hz)⟩
  have := Valuation.map_add_eq_of_lt_left Valued.v hlt
  rwa [add_sub_cancel, h1] at this

theorem twist_open_stabiliser (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v n, NumberField.TateGlobal.localChar χA v u = 1)
    (z : v.adicCompletion ℚ) (hz0 : Valued.v z ≠ 0) (hz : Valued.v z ≤ WithZero.exp (-(n : ℤ)))
    {W : LocalGL3 v → ℂ}
    (hW : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, twist χA v W (g * k) = twist χA v W g := by
  obtain ⟨Uv, hUo, hUW⟩ := hW
  refine ⟨Uv ⊓ ((NumberField.TateGlobal.localChar χA v).comp
      (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (v.adicCompletion ℚ)ˣ)).ker,
    hUo.inter (isOpen_ker_localChar_det χA v n hn z hz0 hz), fun k hk g => ?_⟩
  obtain ⟨hkU, hkK⟩ := Subgroup.mem_inf.1 hk
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hkK
  simp only [twist]
  rw [map_mul, map_mul, hkK, mul_one, hUW k hkU g]

theorem psiLoc_eq_psiLocal_inv_of_inv_eq_psiQ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc ψ p = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ := by
  have hinv : ∀ (χ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ),
      LanglandsTunnell.CubicInduction.psiLoc χ⁻¹ p = (LanglandsTunnell.CubicInduction.psiLoc χ p)⁻¹ := by
    intro χ
    refine DFunLike.ext _ _ fun x => ?_
    rw [AddChar.inv_apply]
    show χ⁻¹ (NumberField.StandardAddChar.adeleSingleAt ℚ p x) = χ (NumberField.StandardAddChar.adeleSingleAt ℚ p (-x))
    rw [map_neg (NumberField.StandardAddChar.adeleSingleAt ℚ p) x, AddChar.inv_apply]
  have hQ : LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ p =
      NumberField.StandardAddChar.psiLocal ℚ p :=
    DFunLike.ext _ _ fun x => (NumberField.StandardAddChar.psiLocal_rat_eq_psiQ_adeleSingleAt p x).symm
  rw [← inv_inv ψ, hinv, hψQ, hQ]

theorem exists_local_uniformizer (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ ϖ : p.adicCompletionIntegers ℚ, algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 ∧
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := by
  refine ⟨⟨(NumberField.AdelicLevel.uniformizerUnit ℚ p : p.adicCompletion ℚ), ?_⟩, ?_, ?_⟩
  · show Valued.v (NumberField.AdelicLevel.uniformizerUnit ℚ p : p.adicCompletion ℚ) ≤ 1
    rw [NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by norm_num)
  · exact Units.ne_zero _
  · exact NumberField.AdelicLevel.valued_uniformizerUnit ℚ p

end GL3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch.Ws23HLInt"

end Ws23HLInt
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch.Ws23HLInt"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23HLInt

section GL2
open LanglandsTunnell.TateLocal

section TranslateSpan
variable {G : Type*} [Group G]

theorem translateSpan_stable (w : G → ℂ) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)), ∀ h : G,
      (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) := by
  intro W hW h
  refine Submodule.span_induction (p := fun W _ => (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)))
    ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h', rfl⟩
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g
    simp only [mul_assoc]
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    exact Submodule.smul_mem _ a hx

theorem translateSpan_law {N : Type*} (act : N → G → G) (χ : N → ℂ) (hact : ∀ n g h, act n (g * h) = act n g * h)
    (w : G → ℂ) (hw : ∀ n g, w (act n g) = χ n * w g) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)), ∀ n g, W (act n g) = χ n * W g := by
  intro W hW
  refine Submodule.span_induction (p := fun W _ => ∀ n g, W (act n g) = χ n * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ n g
    show w (act n g * h) = χ n * w (g * h)
    rw [← hact, hw]
  · intro n g; simp
  · intro x y _ _ hx hy n g
    simp only [Pi.add_apply, hx, hy]; ring
  · intro a x _ hx n g
    simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

end TranslateSpan
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch.Ws23HLInt"

theorem diagZ_eq_diagOne {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) (m : ℤ) :
    diagZ π hπ m = diagOne (Units.mk0 π hπ ^ m) := by
  refine Units.ext ?_
  show (!![π ^ m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![((Units.mk0 π hπ ^ m : Kˣ) : K), 1]
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem norm_uniformizer (p : HeightOneSpectrum (𝓞 ℚ)) {ϖ : p.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ‖algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def (K := ℚ) (v := p), hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have h1 : (WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0)).toAdd = -1 := by
    rw [show WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0) = Multiplicative.ofAdd (-1 : ℤ) from
      WithZero.unzero_coe _, toAdd_ofAdd]
  rw [h1, _root_.zpow_neg, _root_.zpow_one, NNReal.coe_inv]
  norm_cast

theorem shell_growth (p : HeightOneSpectrum (𝓞 ℚ)) (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (C : ℝ) (M : ℕ)
    (hb : ∀ (y : (p.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (p.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      ‖W (diagOne y * k)‖ ≤ C * max 1 ((modulus (y : p.adicCompletion ℚ)) ^ M)⁻¹)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∃ (C' A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C' * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m) := by
  set π : p.adicCompletion ℚ := algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ with hπdef
  set q : ℝ := (Ideal.absNorm p.asIdeal : ℝ) with hqdef
  have hq1 : 1 < q := by rw [hqdef]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hq0 : 0 < q := lt_trans one_pos hq1
  have hnorm : ∀ x : p.adicCompletion ℚ, ((modulus x : NNReal) : ℝ) = ‖x‖ := fun x => by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]
  have hπn : ‖π‖ = q⁻¹ := by rw [hπdef, norm_uniformizer p hϖ, hqdef]
  refine ⟨max C 0, (M : ℝ), fun m hm k hk => ?_⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [diagZ_eq_diagOne, zpow_natCast]
  set y : (p.adicCompletion ℚ)ˣ := Units.mk0 π hπ ^ n with hydef
  have hy : ‖(y : p.adicCompletion ℚ)‖ = q ^ (-(n : ℝ)) := by
    rw [hydef, Units.val_pow_eq_pow_val, Units.val_mk0, norm_pow, hπn, ← Real.rpow_neg_one, ← Real.rpow_natCast,
      ← Real.rpow_mul hq0.le]
    ring_nf
  have hW : ‖W (diagOne y * k)‖ ≤ max C 0 * q ^ ((n : ℝ) * M) := by
    refine (hb y k hk).trans ?_
    have hmax : max 1 (((modulus (y : p.adicCompletion ℚ) : ℝ)) ^ M)⁻¹ = q ^ ((n : ℝ) * M) := by
      rw [hnorm, hy, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_neg hq0.le]
      rw [max_eq_right]
      · congr 1; ring
      · refine Real.one_le_rpow hq1.le ?_
        have : (0 : ℝ) ≤ n * M := by positivity
        linarith [show -( -(n:ℝ) * M) = n * M from by ring]
    have hcast : (((max 1 ((modulus (y : p.adicCompletion ℚ)) ^ M)⁻¹ : NNReal)) : ℝ) =
        max 1 (((modulus (y : p.adicCompletion ℚ) : ℝ)) ^ M)⁻¹ := by
      rw [NNReal.coe_max, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_one]
    rw [hcast, hmax]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hq0.le _)
  refine hW.trans (le_of_eq ?_)
  congr 1
  rw [show (((n : ℕ) : ℤ) : ℝ) = (n : ℝ) from by norm_cast]
  ring_nf

open AutomorphicForm in
theorem whittakerCoefficient_mul_right {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (X Y : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (X * Y) = whittakerCoefficient F pins ψ (fun x => φ (x * Y)) α X := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

open AutomorphicForm AutomorphicForm.WhittakerModel in
theorem localFnAt_translate {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : GL (Fin 2) (v.adicCompletion F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    localFnAt F pins ψ v φ (g * h) =
      localFnAt F pins ψ v (fun x => φ (x * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v h))) g := by
  unfold localFnAt
  rw [map_mul, map_mul, whittakerCoefficient_mul_right]

open AutomorphicForm AutomorphicForm.WhittakerModel in

theorem localSpaceAt_translate_mem {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    ∀ W ∈ localSpaceAt F pins ψ v φ, ∀ h : GL (Fin 2) (v.adicCompletion F),
      (fun g => W (g * h)) ∈ localSpaceAt F pins ψ v φ := by
  intro W hW h
  refine Submodule.span_induction (p := fun W _ => (fun g => W (g * h)) ∈ localSpaceAt F pins ψ v φ)
    ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h', rfl⟩
    refine Submodule.subset_span ⟨AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v h) * h', ?_⟩
    funext g
    rw [localFnAt_translate]
    simp only [mul_assoc]
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    exact Submodule.smul_mem _ a hx

theorem phicen
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ φ) :
    ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * x) =
        (((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) z : ℂˣ) : ℂ) * φ x := by
  intro z x
  letI := (productionPinsGeneral ℚ).mS
  have ht := (((lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).μ (productionPinsGeneral ℚ).Z R.centralChar
    (productionPinsGeneral ℚ).D φ).mp hiso.smoothCusp.1.1).1).central_transform (Subgroup.topEquiv.symm z) x
  exact ht

theorem coe_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 g))⁻¹ * g := rfl

theorem ratArchGL2_of_mem {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : LanglandsTunnell.ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

theorem finFactor_coe (gf : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (gf : AdelicGL2 (𝓞 ℚ) ℚ) = gf := by
  refine Subtype.ext ?_
  rw [coe_finFactor, ratArchGL2_of_mem gf.2, map_one, inv_one, one_mul]

theorem finFactor_one : RSCarrier.finFactor (1 : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
  finFactor_coe (1 : finiteAdelicGL2Subgroup ℚ)

end GL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch.Ws23HLInt"

end Ws23HLInt
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch.Ws23HLInt"

theorem Ws23FamGL2.partner
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWf1 : ∀ par, Wf par 1 ≠ 0)
    (hV : ∀ par, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ →
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))
    (bQ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hbQ : ∀ p ∈ SQ, p.asIdeal ^ bQ p ∣ Φ.level ∧ ¬ p.asIdeal ^ (bQ p + 1) ∣ Φ.level)
    (par : InfinitePlace ℚ → ZMod 2) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∃ (b : ℕ) (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ),
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w₂base (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        w₂base (g * k) = w₂base g) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g) ∧
      (∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
          C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m)) ∧
      Submodule.span ℂ {f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ |
          ∃ w₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            ∃ h : GL (Fin 2) (p.adicCompletion ℚ), f = fun g => w₀ (g * h)} ≤
        Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := by
  classical

  obtain ⟨m, wS, WS, hmem, -, hlaw, -, -, -, hsm, -, hlev, hsplit⟩ :=
    AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt Φ S R
      φv hiso hφne WA Wf hWAf par SQ (hV par)

  have hex : ∃ α : Fin m, wS ⟨p, hp⟩ α 1 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hWf1 par
    have h1 := hsplit 1
    rw [Ws23HLInt.finFactor_one] at h1
    rw [h1]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ (⟨p, hp⟩ : ↥SQ)) (by rw [map_one]; exact hall α), zero_mul]
  obtain ⟨α, hα⟩ := hex
  set w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := wS ⟨p, hp⟩ α with hw₂def
  have hw₂mem : w₂base ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par) :=
    hmem ⟨p, hp⟩ α
  have hw₂ne : w₂base ≠ 0 := fun h => hα (by rw [h, Pi.zero_apply])
  have hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g :=
    hlaw ⟨p, hp⟩ α

  set Vp := AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par) with hVp
  have hVstab : ∀ W ∈ Vp, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ Vp :=
    Ws23HLInt.localSpaceAt_translate_mem (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par)
  obtain ⟨hVirr, hVadm, hVsm⟩ := hV par p hp
  set ξ0 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom with hξ0
  have hVcen := AutomorphicForm.WhittakerModel.forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
    (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (φv par) ξ0 (Ws23HLInt.phicen Φ S R (φv par) (hiso par)) p

  set V' : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) with hV'
  have hle : V' ≤ Vp := Submodule.span_le.2 (by rintro _ ⟨h, rfl⟩; exact hVstab w₂base hw₂mem h)
  have hlaw' : ∀ W ∈ V', ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g :=
    Ws23HLInt.translateSpan_law (fun (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)) => UnramifiedWhittaker.unipotent x * g)
      (fun x => NumberField.StandardAddChar.psiLocal ℚ p x) (fun x g h => (mul_assoc _ _ _).symm) w₂base hw₂law
  obtain ⟨C, M, c, -, -, hb⟩ := AutomorphicForm.WhittakerModel.exists_norm_diagOne_mul_le_of_irreducible_admissible p V'
    (Ws23HLInt.translateSpan_stable w₂base) hlaw' (fun W hW => hVsm W (hle hW))
    (fun U hU => by obtain ⟨B, hB⟩ := hVadm U hU; exact ⟨B, fun W hW hinv => hB W (hle hW) hinv⟩)
    (fun W₀ hW₀ h0 W hW => hVirr W₀ (hle hW₀) h0 W (hle hW)) (NumberField.TateGlobal.localChar ξ0 p)
    (fun W hW => hVcen W (hle hW))
    w₂base (Submodule.subset_span ⟨1, funext fun g => by beta_reduce; rw [mul_one]⟩)
  refine ⟨bQ p, w₂base, NumberField.TateGlobal.localChar ξ0 p, hw₂law, ?_, hVcen w₂base hw₂mem,
    Ws23HLInt.shell_growth p w₂base C M (fun y k hk => (hb y k hk).1) hπ hϖ, ?_⟩
  ·
    intro k hk g
    exact LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq p Φ.level
      w₂base (hlev ⟨p, hp⟩ α) (bQ p) (hbQ p hp) k g hk
  ·
    refine Submodule.span_le.2 ?_
    rintro f ⟨w₀, hw₀, h, rfl⟩
    exact hVirr w₂base hw₂mem hw₂ne _ (hVstab w₀ hw₀ h)

set_option linter.unusedVariables false in
open Ws23HLInt in
open MeasureTheory LanglandsTunnell.TateLocal in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (P : RealArchParam)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (hP1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (hP2 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (hRcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wr : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℂ → ℂ)
    (kw : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℤ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (hφarch : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (kw par w)) (φv par))
    (hkw1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w))
    (hkw2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hφW : ∀ par, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (φv par) 1 (diagOne a * g)
          = (∏ w : InfinitePlace ℚ, Wr par w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
              * Cfin (a : AdeleRing (𝓞 ℚ) ℚ).2 g)
    (hWr1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par w ∨ b = par w + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓)
    (hE : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ SK)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent
        ((archOfParamR K P w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hkχ : ∀ p ∈ SQ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) (kχ p))
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (c₀ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hν : ∀ p ∈ SQ, ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ p ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w
        (NumberField.TateGlobal.localChar
          (μ * (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)⁻¹) w) c)
    (bQ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hbQ : ∀ p ∈ SQ, p.asIdeal ^ bQ p ∣ Φ.level ∧ ¬ p.asIdeal ^ (bQ p + 1) ∣ Φ.level)
    (hkfloor : ∀ p ∈ SQ,
      6 * ((bQ p : ℤ) + 3 * (2 * ((∑ᶠ w ∈ primeFibre ℚ K p,
              ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                    (2 * ((52 : ℤ) + 3 * (c₀ p : ℤ)) +
                      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                  (c₀ p : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
            ((52 : ℤ) + 3 * (c₀ p : ℤ)))) + 3) + 7 ≤ (kχ p : ℤ))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hμν : μ = ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K ν v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K ν v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (mP : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)
    (hmPmem : ∀ p : ↥SQ, mP p ∈ gl3CyclicSubspace
      (fun g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) g))
    (hmP1 : ∀ p : ↥SQ, mP p 1 = 1)
    (hW₃admM : ∀ p : ↥SQ, ∀ Uv : Subgroup (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))), IsOpen (Uv : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))) →
      ∃ B : Finset (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ), ∀ W ∈ gl3CyclicSubspace (mP p),
        (∀ k ∈ Uv, ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)))
    (hW₃irrM : ∀ p : ↥SQ, ∀ W ∈ gl3CyclicSubspace (mP p), W ≠ 0 → mP p ∈ gl3CyclicSubspace W)
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWfC : ∀ par (g : finiteAdelicGL2Subgroup ℚ), Wf par g = Cfin 1 (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hWf1 : ∀ par, Wf par 1 ≠ 0)
    (hV : ∀ par, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ →
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (par : InfinitePlace ℚ → ZMod 2) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)

    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw : w ∈ Submodule.span ℂ {f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ |
      ∃ w₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
        ∃ h : GL (Fin 2) (p.adicCompletion ℚ), f = fun g => w₀ (g * h)})

    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ ∈ gl3CyclicSubspace
      (fun g : LocalGL3 p => ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (W₃ (iotaGL g) * w g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := by
  intro μ₂ _ μN₂ _
  classical

  obtain ⟨ϖp, hπp, hϖp⟩ := Ws23HLInt.exists_local_uniformizer p

  obtain ⟨b, w₂base, ω, hw₂law, hw₂K, hcen, hw₂gr, hspan⟩ :=
    Ws23FamGL2.partner Φ SQ S R φv hiso hφne WA Wf hWAf hWf1 hV bQ hbQ par p hp hπp hϖp

  have hψp := Ws23HLInt.psiLoc_eq_psiLocal_inv_of_inv_eq_psiQ ψ hψQ p
  have hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹
      (Ws23HLInt.twist χA p (F.whittakerLoc p)) := by
    rw [← hψp]
    exact Ws23HLInt.isGL3PsiWhittakerFn_twist χA p (F.whittakerLoc_law p)

  have hW₀sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, F.whittakerLoc p (g * k) = F.whittakerLoc p g := by
    by_cases hb : IsBadPlace K ν p
    · exact (hBad {p}).1 p (Finset.mem_singleton_self _) hb
    · exact ⟨localMaximalCompact3 (𝓞 ℚ) ℚ p, LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3 (𝓞 ℚ) ℚ p,
        fun k hk g => (F.spherical p hb).1 g k hk⟩
  have hvz : Valued.v ((algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖp) ^ kχ p) =
      WithZero.exp (-(kχ p : ℤ)) := by
    rw [map_pow, hϖp, ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul, mul_one]
  have hW₃sm := Ws23HLInt.twist_open_stabiliser χA p (kχ p) (hkχ p hp).1 _
    (by rw [hvz]; exact WithZero.exp_ne_zero) hvz.le hW₀sm

  have hgoodν : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S' → ¬ IsBadPlace K ν q := by
    intro q hq hbad
    have hqQ : q ∉ SQ := fun h => hq (hSS' h)
    have h := (LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K _hdeg ν χA hχA q
      (hχoff q hqQ)).1.2 hbad
    rw [← hμν] at h
    exact hgood q hq h
  have hWgauge := Ws23HLInt.twist_gauge χA hχA p
    (LanglandsTunnell.CubicInduction.exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero K _ ψ ν F hF0.1 hFg S'
      hgoodν p)

  exact Ws23HLInt.local_core p (Ws23HLInt.twist χA p (F.whittakerLoc p)) hW₃law hW₃sm hWgauge b hπp hϖp w₂base hw₂law
    hw₂K ω hcen hw₂gr μ₂ μN₂ w (hspan hw) W₃ hW₃

#print axioms solution

end
end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch (solution)
