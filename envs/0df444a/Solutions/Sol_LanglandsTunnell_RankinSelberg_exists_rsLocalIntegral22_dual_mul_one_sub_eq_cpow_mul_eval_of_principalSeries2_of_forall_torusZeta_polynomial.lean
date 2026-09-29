-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b55fd889-2f1c-59ee-b9d8-fbfd2d0f652c

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

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_AutomorphicForm_hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsIntegrand22_withDensity_of_admissible_of_chamber
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_le_setIntegral_localLevelOne_dualJacquet_mul_partner_mul_eq_zero_of_dualTorusZeta_polynomial
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace RS22SpanKit

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

end RS22SpanKit

namespace RS22DualShell

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "scal" => (Matrix.GeneralLinearGroup.scalar (Fin 2) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem coe_scal (z : Fˣ) : ((scal z : G) : Mat) = Matrix.diagonal fun _ => (z : F) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.scalar]

theorem coe_diagOne (y : Fˣ) : ((diagOne y : G) : Mat) = Matrix.diagonal ![(y : F), 1] := rfl

theorem scal_mul_comm (z : Fˣ) (g : G) : scal z * g = g * scal z := by
  refine Units.ext ?_
  change ((scal z : G) : Mat) * (g : Mat) = (g : Mat) * ((scal z : G) : Mat)
  rw [coe_scal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> ring

theorem transposeInvN_scal (z : Fˣ) : transposeInvN (Fin 2) (scal z) = scal z⁻¹ := by
  refine Units.ext ?_
  rw [coe_transposeInvN, ← map_inv, coe_scal, Matrix.diagonal_transpose]

theorem transposeInvN_diagOne (y : Fˣ) : transposeInvN (Fin 2) (diagOne y : G) = diagOne y⁻¹ := by
  refine Units.ext ?_
  rw [coe_transposeInvN, ← map_inv, coe_diagOne, Matrix.diagonal_transpose]

theorem antidiag_mul_diagOne_inv (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (y : Fˣ) :
    w₀ * diagOne y⁻¹ = scal y⁻¹ * diagOne y * w₀ := by
  refine Units.ext ?_
  change (w₀ : Mat) * ((diagOne y⁻¹ : G) : Mat) = ((scal y⁻¹ : G) : Mat) * ((diagOne y : G) : Mat) * (w₀ : Mat)
  rw [hw₀, coe_diagOne, coe_diagOne, coe_scal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem antidiag_mul_transposeInvN_shell (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (t y : Fˣ) (k : G) :
    w₀ * transposeInvN (Fin 2) (scal t * diagOne y * k) =
      scal (t⁻¹ * y⁻¹) * (diagOne y * (w₀ * transposeInvN (Fin 2) k)) := by
  rw [transposeInvN_mul, transposeInvN_mul, transposeInvN_scal, transposeInvN_diagOne, map_mul]

  rw [← mul_assoc w₀, ← mul_assoc w₀, ← scal_mul_comm p t⁻¹ w₀, mul_assoc (scal t⁻¹) w₀,
    antidiag_mul_diagOne_inv p w₀ hw₀ y]
  simp only [mul_assoc]

theorem row_one_shell (t y : Fˣ) (k : G) (j : Fin 2) :
    ((scal t * diagOne y * k : G) : Mat) 1 j = (t : F) * (k : Mat) 1 j := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_scal, coe_diagOne, Matrix.diagonal]

theorem det_shell (t y : Fˣ) (k : G) :
    Matrix.GeneralLinearGroup.det (scal t * diagOne y * k) = t * t * y * Matrix.GeneralLinearGroup.det k := by
  rw [map_mul, map_mul]
  have h1 : Matrix.GeneralLinearGroup.det (scal t : G) = t * t := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_scal, Matrix.det_diagonal]
    simp [Fin.prod_univ_two, pow_two]
  have h2 : Matrix.GeneralLinearGroup.det (diagOne y : G) = y := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagOne, Matrix.det_diagonal]
    simp [Fin.prod_univ_two]
  rw [h1, h2]

theorem scal_eq_diagonal2 (c : Fˣ) : (scal c : G) = diagonal2 p ![c, c] := by
  refine Units.ext ?_
  rw [coe_scal, diagonal2_coe]
  congr 1
  funext i
  fin_cases i <;> simp

theorem torusChar2_pair_same (μ : Fin 2 → (Fˣ →* ℂˣ)) (c : Fˣ) :
    torusChar2 p μ ![c, c] = ((μ 0 c : ℂˣ) : ℂ) * ((μ 1 c : ℂˣ) : ℂ) := by
  simp [torusChar2, Fin.prod_univ_two]

theorem halfModulus2_pair_same (c : Fˣ) : halfModulus2 p ![c, c] = 1 := by
  have hc : ‖(c : F)‖ ≠ 0 := norm_ne_zero_iff.mpr c.ne_zero
  simp [halfModulus2, div_self hc]

theorem principalSeries2_scal_mul {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    (c : Fˣ) (g : G) :
    φ (scal c * g) = ((μ 0 c : ℂˣ) : ℂ) * ((μ 1 c : ℂˣ) : ℂ) * φ g := by
  obtain ⟨-, -, hT⟩ := mem_principalSeries2_iff.mp hφ
  rw [scal_eq_diagonal2, hT, torusChar2_pair_same, halfModulus2_pair_same, mul_one]

theorem jacquetIntegral_scal_mul {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    [MeasurableSpace F] (ν : Measure F) (c : Fˣ) (h : G) :
    ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (scal c * h)) ∂ν =
      ((μ 0 c : ℂˣ) : ℂ) * ((μ 1 c : ℂˣ) : ℂ) *
        ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * h) ∂ν := by
  rw [← integral_const_mul]
  congr 1
  funext x
  have : antidiagonal2 p * upperUnipotent2 p x * (scal c * h) = scal c * (antidiagonal2 p * upperUnipotent2 p x * h) := by
    rw [← mul_assoc, ← scal_mul_comm p c (antidiagonal2 p * upperUnipotent2 p x), mul_assoc]
  rw [this, principalSeries2_scal_mul p hφ]
  ring

theorem dualWhittakerSlot_shell {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    [MeasurableSpace F] (ν : Measure F)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (t y : Fˣ) (k : G) :
    ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (scal t * diagOne y * k))) ∂ν =
      ((μ 0 (t⁻¹ * y⁻¹) : ℂˣ) : ℂ) * ((μ 1 (t⁻¹ * y⁻¹) : ℂˣ) : ℂ) *
        ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
          φ (antidiagonal2 p * upperUnipotent2 p x * (diagOne y * (w₀p * transposeInvN (Fin 2) k))) ∂ν := by
  rw [antidiag_mul_transposeInvN_shell p w₀p hw₀p t y k, jacquetIntegral_scal_mul p hφ ν]

theorem dualPartnerSlot_shell (θ₀ : Fˣ →* ℂˣ) (w₂ : G → ℂ)
    (hw₂cen : ∀ (z : Fˣ) (g : G), w₂ (scal z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (t y : Fˣ) (k : G) :
    w₂ (w₀p * transposeInvN (Fin 2) (scal t * diagOne y * k)) =
      ((θ₀ (t⁻¹ * y⁻¹) : ℂˣ) : ℂ) * w₂ (diagOne y * (w₀p * transposeInvN (Fin 2) k)) := by
  rw [antidiag_mul_transposeInvN_shell p w₀p hw₀p t y k, hw₂cen]

theorem modulus_det_shell (t y : Fˣ) (k : G) :
    ((modulus ((Matrix.GeneralLinearGroup.det (scal t * diagOne y * k) : Fˣ) : F) : ℝ) : ℂ) =
      ((‖(t : F)‖ : ℝ) : ℂ) ^ 2 * ((‖(y : F)‖ : ℝ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) : ℝ) : ℂ) := by
  rw [det_shell]
  simp only [Units.val_mul, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm, norm_mul]
  push_cast
  ring

end RS22DualShell

namespace RS22Dual

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

def qN : ℂ := (Ideal.absNorm p.asIdeal : ℂ)

def phiHat (Φ₂ : F × F → ℂ) (v : F × F) : ℂ :=
  ∫ u : F × F, Φ₂ u * NumberField.StandardAddChar.psiLocal ℚ p (u.1 * v.1 + u.2 * v.2)
    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))

def dualW (φ : G → ℂ) (w₀p : G) (g : G) : ℂ :=
  ∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)

def dualF (w₂ : G → ℂ) (w₀p : G) (Φ₂ : F × F → ℂ) (g : G) : ℂ :=
  ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) *
    phiHat p Φ₂ ((g : Mat) 1 0, (g : Mat) 1 1)

def dualD (φ : G → ℂ) (w₂ : G → ℂ) (w₀p : G) (Φ₂ : F × F → ℂ) (s : ℂ) (g : G) : ℂ :=
  (dualW p φ w₀p g * dualF p w₂ w₀p Φ₂ g) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)

theorem SER (τ : ℤ × ℤ → ℂ) (ρ : ℂ) (nlo nhi a b : ℤ) (α : ℤ → ℂ)
    (hsupp₂ : ∀ n : ℤ × ℤ, n.2 < nlo → τ n = 0)
    (hsupp₁ : ∀ n : ℤ × ℤ, (n.1 < a ∨ b < n.1) → τ n = 0)
    (hdeep : ∀ n : ℤ × ℤ, nhi ≤ n.2 → τ n = ρ ^ (n.2 - nhi).toNat * α n.1) :
    ∃ (m : ℤ) (P : Polynomial ℂ), ∀ (s S : ℂ),
      HasSum (fun n : ℤ × ℤ => qN p ^ (-(((2 * n.2 + n.1 : ℤ)) : ℂ) * s) * τ n) S →
        S * (1 - ρ * qN p ^ (-(2 : ℂ) * s)) = qN p ^ ((m : ℂ) * s) * P.eval (qN p ^ (-s)) := by
  classical
  set I₁ : Finset ℤ := Finset.Icc a b with hI₁
  set I₂ : Finset ℤ := Finset.Ico nlo nhi with hI₂
  set A : Finset (ℤ × ℤ) := I₁ ×ˢ I₂ with hA
  set e₀ : ℤ := 2 * min nlo nhi + a with he₀
  set mono : ℤ → ℂ → Polynomial ℂ := fun e c => Polynomial.monomial (e - e₀).toNat c with hmono
  refine ⟨-e₀, (∑ n ∈ A, mono (2 * n.2 + n.1) (τ n)) - (∑ n ∈ A, mono (2 * n.2 + n.1 + 2) (ρ * τ n)) +
    (∑ i ∈ I₁, mono (2 * nhi + i) (α i)), ?_⟩
  intro s S hS
  have hq0 : qN p ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    simp only [qN, ne_eq, Nat.cast_eq_zero]; omega
  set X : ℂ := qN p ^ (-s) with hX
  have hX0 : X ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq0)
  have hpow : ∀ e : ℤ, qN p ^ (-((e : ℤ) : ℂ) * s) = X ^ e := by
    intro e
    rw [show (-((e : ℤ) : ℂ) * s) = ((e : ℤ) : ℂ) * (-s) by ring, Complex.cpow_int_mul]
  have hpow2 : qN p ^ (-(2 : ℂ) * s) = X ^ (2 : ℤ) := by
    rw [← hpow 2]; norm_num
  have hpowm : qN p ^ (((-e₀ : ℤ) : ℂ) * s) = X ^ e₀ := by
    rw [show (((-e₀ : ℤ) : ℂ) * s) = ((e₀ : ℤ) : ℂ) * (-s) by push_cast; ring, Complex.cpow_int_mul]

  set T : ℤ × ℤ → ℂ := fun n => X ^ (2 * n.2 + n.1) * τ n with hT
  have hfun : (fun n : ℤ × ℤ => qN p ^ (-(((2 * n.2 + n.1 : ℤ)) : ℂ) * s) * τ n) = T := by
    funext n; simp only [hT]; rw [hpow]
  rw [hfun] at hS

  have hT0 : ∀ n : ℤ × ℤ, ¬ (n.1 ∈ I₁ ∧ nlo ≤ n.2) → T n = 0 := by
    intro n hn
    simp only [hT]
    have : τ n = 0 := by
      by_cases h1 : n.1 ∈ I₁
      · have h2 : n.2 < nlo := by
          by_contra h2; exact hn ⟨h1, not_lt.mp h2⟩
        exact hsupp₂ n h2
      · rw [hI₁, Finset.mem_Icc, not_and_or, not_le, not_le] at h1
        exact hsupp₁ n h1
    rw [this, mul_zero]

  set TA : ℤ × ℤ → ℂ := fun n => if n ∈ A then T n else 0 with hTA
  set TD : ℤ × ℤ → ℂ := fun n => if n.1 ∈ I₁ ∧ nhi ≤ n.2 then T n else 0 with hTD
  have hsplit : T = fun n => TA n + TD n := by
    funext n
    simp only [hTA, hTD]
    by_cases hAn : n ∈ A
    · have : ¬ (n.1 ∈ I₁ ∧ nhi ≤ n.2) := by
        rw [hA, Finset.mem_product, hI₂, Finset.mem_Ico] at hAn
        exact fun h => absurd hAn.2.2 (not_lt.mpr h.2)
      simp [hAn, this]
    · by_cases hDn : n.1 ∈ I₁ ∧ nhi ≤ n.2
      · simp [hAn, hDn]
      · simp only [hAn, hDn, if_false, add_zero]
        apply hT0
        intro h
        apply hAn
        rw [hA, Finset.mem_product, hI₂, Finset.mem_Ico]
        exact ⟨h.1, h.2, not_le.mp fun h' => hDn ⟨h.1, h'⟩⟩
  have hTA_sum : HasSum TA (∑ n ∈ A, T n) := by
    have h1 : ∀ n ∉ A, TA n = 0 := fun n hn => by simp only [hTA, hn, if_false]
    have h2 : ∑ n ∈ A, TA n = ∑ n ∈ A, T n := Finset.sum_congr rfl fun n hn => by simp only [hTA, hn, if_true]
    rw [← h2]; exact hasSum_sum_of_ne_finset_zero h1
  have hTD_sum : HasSum TD (S - ∑ n ∈ A, T n) := by
    have := hS
    rw [hsplit] at this
    have h3 := this.sub hTA_sum
    simpa using h3

  set ι : (↥I₁ × ℕ) → ℤ × ℤ := fun ik => ((ik.1 : ℤ), nhi + (ik.2 : ℤ)) with hι
  have hι_inj : Function.Injective ι := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ h
    simp only [hι, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : k = k' := by exact_mod_cast (add_left_cancel h2)
    exact Prod.ext (Subtype.ext h1) this
  have hTD_off : ∀ n ∉ Set.range ι, TD n = 0 := by
    intro n hn
    simp only [hTD]
    split_ifs with h
    · exfalso; apply hn
      refine ⟨(⟨n.1, h.1⟩, (n.2 - nhi).toNat), ?_⟩
      simp only [hι]
      ext
      · rfl
      · simp only []; rw [Int.toNat_of_nonneg (sub_nonneg.mpr h.2)]; ring
    · rfl
  set r : ℂ := ρ * X ^ (2 : ℤ) with hr
  set c : ↥I₁ → ℂ := fun i => X ^ (2 * nhi + (i : ℤ)) * α i with hc
  have hTDι : TD ∘ ι = fun ik : ↥I₁ × ℕ => c ik.1 * r ^ ik.2 := by
    funext ik
    obtain ⟨i, k⟩ := ik
    have hmem : (i : ℤ) ∈ I₁ := i.2
    have hle : nhi ≤ nhi + (k : ℤ) := le_add_of_nonneg_right (Int.natCast_nonneg k)
    simp only [Function.comp_apply, hι, hTD, hmem, hle, and_self, if_true, hT, hc, hr]
    rw [hdeep _ hle]
    simp only [show nhi + (k : ℤ) - nhi = (k : ℤ) by ring, Int.toNat_natCast]
    rw [mul_pow, show (2 * (nhi + (k : ℤ)) + (i : ℤ)) = (2 * nhi + (i : ℤ)) + 2 * (k : ℤ) by ring, zpow_add₀ hX0,
      show X ^ (2 * (k : ℤ)) = (X ^ (2 : ℤ)) ^ k by rw [← zpow_natCast, ← zpow_mul]]
    ring
  have hg : HasSum (fun ik : ↥I₁ × ℕ => c ik.1 * r ^ ik.2) (S - ∑ n ∈ A, T n) := by
    rw [← hTDι]; exact (hι_inj.hasSum_iff hTD_off).mpr hTD_sum

  have hdeep_val : (S - ∑ n ∈ A, T n) * (1 - r) = ∑ i : ↥I₁, c i := by
    by_cases hc0 : ∀ i : ↥I₁, c i = 0
    · have hz : (fun ik : ↥I₁ × ℕ => c ik.1 * r ^ ik.2) = fun _ => 0 := by
        funext ik; rw [hc0 ik.1, zero_mul]
      rw [hz] at hg
      have : S - ∑ n ∈ A, T n = 0 := (hasSum_zero.unique hg).symm
      rw [this, zero_mul, Finset.sum_eq_zero fun i _ => hc0 i]
    · push_neg at hc0
      obtain ⟨i₀, hi₀⟩ := hc0
      have hsum := hg.summable
      have hray : Summable fun k : ℕ => c i₀ * r ^ k := hsum.prod_factor i₀
      have hr1 : ‖r‖ < 1 := summable_geometric_iff_norm_lt_one.mp ((summable_mul_left_iff hi₀).mp hray)
      have hval : S - ∑ n ∈ A, T n = ∑ i : ↥I₁, c i * (1 - r)⁻¹ := by
        rw [← hg.tsum_eq, hsum.tsum_prod' (fun i => hsum.prod_factor i), tsum_fintype]
        refine Finset.sum_congr rfl fun i _ => ?_
        change ∑' k : ℕ, c i * r ^ k = c i * (1 - r)⁻¹
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr1]
      have h1r : (1 - r) ≠ 0 := by
        intro h
        have : ‖r‖ = 1 := by rw [show r = 1 from (sub_eq_zero.mp h).symm, norm_one]
        exact absurd hr1 (by rw [this]; exact lt_irrefl 1)
      rw [hval, ← Finset.sum_mul, mul_assoc, inv_mul_cancel₀ h1r, mul_one]

  have hS_eq : S * (1 - r) = (∑ n ∈ A, T n) * (1 - r) + ∑ i : ↥I₁, c i := by
    rw [← hdeep_val]; ring

  have hminlo : min nlo nhi ≤ nlo := min_le_left _ _
  have hminhi : min nlo nhi ≤ nhi := min_le_right _ _
  have heA : ∀ n ∈ A, e₀ ≤ 2 * n.2 + n.1 := by
    intro n hn
    rw [hA, Finset.mem_product, hI₁, Finset.mem_Icc, hI₂, Finset.mem_Ico] at hn
    simp only [he₀]; omega
  have heI : ∀ i ∈ I₁, e₀ ≤ 2 * nhi + i := by
    intro i hi
    rw [hI₁, Finset.mem_Icc] at hi
    simp only [he₀]; omega
  have hXe : ∀ e : ℤ, e₀ ≤ e → X ^ e = X ^ e₀ * X ^ (e - e₀).toNat := by
    intro e he
    rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr he), ← zpow_add₀ hX0]; ring_nf
  have hmono_eval : ∀ (e : ℤ) (cc : ℂ), e₀ ≤ e → (mono e cc).eval X = cc * X ^ (e - e₀).toNat := by
    intro e cc he; simp only [hmono, Polynomial.eval_monomial]

  rw [hpow2, hpowm, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_finset_sum,
    Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  rw [show S * (1 - ρ * X ^ (2 : ℤ)) = S * (1 - r) by rfl, hS_eq]
  have hsumA : (∑ n ∈ A, T n) * (1 - r) =
      X ^ e₀ * (∑ n ∈ A, (mono (2 * n.2 + n.1) (τ n)).eval X) -
        X ^ e₀ * (∑ n ∈ A, (mono (2 * n.2 + n.1 + 2) (ρ * τ n)).eval X) := by
    rw [Finset.mul_sum, Finset.mul_sum, mul_sub, mul_one, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [hmono_eval _ _ (heA n hn), hT]; simp only []
      rw [hXe _ (heA n hn)]; ring
    · refine Finset.sum_congr rfl fun n hn => ?_
      have he2 : e₀ ≤ 2 * n.2 + n.1 + 2 := by linarith [heA n hn]
      rw [hmono_eval _ _ he2, hT]; simp only [hr]
      rw [show X ^ (2 * n.2 + n.1) * τ n * (ρ * X ^ (2 : ℤ)) = ρ * τ n * (X ^ (2 * n.2 + n.1) * X ^ (2 : ℤ)) by ring,
        ← zpow_add₀ hX0, hXe _ he2]; ring
  have hsumI : ∑ i : ↥I₁, c i = X ^ e₀ * ∑ i ∈ I₁, (mono (2 * nhi + i) (α i)).eval X := by
    rw [Finset.mul_sum, ← Finset.sum_coe_sort I₁]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hc]
    rw [hmono_eval _ _ (heI i i.2), hXe _ (heI i i.2)]; ring
  rw [hsumA, hsumI]; ring

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : NNReal) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : NNReal) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

attribute [local instance] isAddHaarMeasure_selfDualHaarAt

theorem unipotent_eq_unipotentGL2 (x : F) : (UnramifiedWhittaker.unipotent x : G) = unipotentGL2 x := by
  refine Units.ext ?_
  rw [unipotentGL2_coe]
  simp [UnramifiedWhittaker.unipotent]

theorem upperUnipotent2_eq_unipotentGL2 (x : F) : upperUnipotent2 p x = (unipotentGL2 x : G) := by
  refine Units.ext ?_
  rw [upperUnipotent2_coe, unipotentGL2_coe]

theorem antidiag_mul_transposeInvN_unipotentGL2 (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (a : F) :
    w₀ * transposeInvN (Fin 2) (unipotentGL2 a : G) = unipotentGL2 (-a) * w₀ := by
  refine Units.ext ?_
  change (w₀ : Mat) * ((transposeInvN (Fin 2) (unipotentGL2 a : G) : G) : Mat) =
    ((unipotentGL2 (-a) : G) : Mat) * (w₀ : Mat)
  have hone : (unipotentGL2 (0 : F) : G) = 1 := by
    refine Units.ext ?_
    rw [unipotentGL2_coe, Units.val_one, Matrix.one_fin_two]
  have hinv' : ((unipotentGL2 a : G)⁻¹ : G) = unipotentGL2 (-a) :=
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, hone])
  have hinv : (((unipotentGL2 a : G)⁻¹ : G) : Mat) = !![1, -a; 0, 1] := by
    rw [hinv', unipotentGL2_coe]
  rw [coe_transposeInvN, hinv, hw₀, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem row_one_unipotentGL2_mul (a : F) (g : G) (j : Fin 2) :
    ((unipotentGL2 a * g : G) : Mat) 1 j = (g : Mat) 1 j := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]

theorem det_unipotentGL2' (a : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 a : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem dualW_unipotentGL2_mul {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (a : F) (g : G) :
    dualW p φ w₀p (unipotentGL2 a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * dualW p φ w₀p g := by
  unfold dualW
  set h : G := w₀p * transposeInvN (Fin 2) g with hh
  set f : F → ℂ := fun y => NumberField.StandardAddChar.psiLocal ℚ p (a + y) *
    φ (antidiagonal2 p * upperUnipotent2 p y * h) with hf
  have hpt : (fun x : F => NumberField.StandardAddChar.psiLocal ℚ p x *
      φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (unipotentGL2 a * g)))) =
      fun x => f (-a + x) := by
    funext x
    simp only [hf]
    rw [transposeInvN_mul, ← mul_assoc w₀p, antidiag_mul_transposeInvN_unipotentGL2 p w₀p hw₀p a,
      add_neg_cancel_left, ← upperUnipotent2_eq_unipotentGL2]
    have e : antidiagonal2 p * upperUnipotent2 p x * (upperUnipotent2 p (-a) * w₀p * transposeInvN (Fin 2) g) =
        antidiagonal2 p * upperUnipotent2 p (-a + x) * h := by
      rw [hh, show -a + x = x + -a from add_comm _ _, upperUnipotent2_eq_unipotentGL2,
        upperUnipotent2_eq_unipotentGL2, upperUnipotent2_eq_unipotentGL2, unipotentGL2_add]
      simp only [mul_assoc]
    rw [e]
  rw [hpt, integral_add_left_eq_self f (-a)]
  simp only [hf, AddChar.map_add_eq_mul, mul_assoc]
  rw [integral_const_mul]

theorem dualF_unipotentGL2_mul (w₂ : G → ℂ)
    (hw₂law : ∀ (x : F) (g : G), w₂ (UnramifiedWhittaker.unipotent x * g) =
      NumberField.StandardAddChar.psiLocal ℚ p x * w₂ g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (Φ₂ : F × F → ℂ) (a : F) (g : G) :
    dualF p w₂ w₀p Φ₂ (unipotentGL2 a * g) = NumberField.StandardAddChar.psiLocal ℚ p (-a) * dualF p w₂ w₀p Φ₂ g := by
  unfold dualF
  rw [map_mul, det_unipotentGL2', one_mul, transposeInvN_mul, ← mul_assoc w₀p,
    antidiag_mul_transposeInvN_unipotentGL2 p w₀p hw₀p a, mul_assoc (unipotentGL2 (-a) : G),
    ← unipotent_eq_unipotentGL2, hw₂law, row_one_unipotentGL2_mul, row_one_unipotentGL2_mul]
  ring

theorem D0_invariant {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    (w₂ : G → ℂ)
    (hw₂law : ∀ (x : F) (g : G), w₂ (UnramifiedWhittaker.unipotent x * g) =
      NumberField.StandardAddChar.psiLocal ℚ p x * w₂ g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (Φ₂ : F × F → ℂ) (s : ℂ) :
    ∀ x ∈ (unipotentGL2Hom (R := F)).range, ∀ g : G,
      dualD p φ w₂ w₀p Φ₂ s (x * g) = dualD p φ w₂ w₀p Φ₂ s g := by
  rintro x ⟨z, rfl⟩ g
  change dualD p φ w₂ w₀p Φ₂ s (unipotentGL2 z.toAdd * g) = dualD p φ w₂ w₀p Φ₂ s g
  unfold dualD
  rw [dualW_unipotentGL2_mul p hφ w₀p hw₀p, dualF_unipotentGL2_mul p w₂ hw₂law w₀p hw₀p, map_mul,
    det_unipotentGL2', one_mul]
  have hψ : NumberField.StandardAddChar.psiLocal ℚ p z.toAdd * NumberField.StandardAddChar.psiLocal ℚ p (-z.toAdd) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  linear_combination (dualW p φ w₀p g * dualF p w₂ w₀p Φ₂ g *
    ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) * hψ

theorem D3_centreWindow (Φ₂ : F × F → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) = WithZero.exp (-1 : ℤ)) :
    ∃ (nlo nhi : ℤ), nlo ≤ nhi ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ,
        (n < nlo →
          phiHat p Φ₂ ((algebraMap (p.adicCompletionIntegers ℚ) F ϖ) ^ n * ((k : Mat) 1 0),
              (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) ^ n * ((k : Mat) 1 1)) = 0) ∧
        (nhi ≤ n →
          phiHat p Φ₂ ((algebraMap (p.adicCompletionIntegers ℚ) F ϖ) ^ n * ((k : Mat) 1 0),
              (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) ^ n * ((k : Mat) 1 1)) = phiHat p Φ₂ (0, 0)) := by
  have hSB := (LanglandsTunnell.TateLocal.isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
    p Φ₂ hΦ₂).1
  exact LanglandsTunnell.RankinSelberg.exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport
    p (phiHat p Φ₂) hSB hπ hϖ

open RS22DualShell in

theorem scalarPi_eq_scalar {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖ ≠ 0) :
    (UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ : G) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ) := by
  refine Units.ext ?_
  rw [RS22DualShell.coe_scal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.scalarPi, Matrix.diagonal]

theorem diagZ_eq_diagOne {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖ ≠ 0) (n : ℤ) :
    (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ n : G) =
      diagOne ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ) ^ n) := by
  refine Units.ext ?_
  rw [RS22DualShell.coe_diagOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UnramifiedWhittaker.diagZ, Matrix.diagonal, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem shellElt_eq {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖ ≠ 0) (dn : ℤ × ℤ) (k : G) :
    (UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ ^ dn.2 *
        UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ dn.1 * k : G) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ) ^ dn.2) *
        diagOne ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ) ^ dn.1) * k := by
  simp only [scalarPi_eq_scalar, diagZ_eq_diagOne, map_zpow]

open RS22DualShell in

theorem dualD_shell {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    (θ₀ : Fˣ →* ℂˣ) (w₂ : G → ℂ)
    (hw₂cen : ∀ (z : Fˣ) (g : G), w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (Φ₂ : F × F → ℂ) (s : ℂ) (t y : Fˣ) (k : G) :
    dualD p φ w₂ w₀p Φ₂ s (Matrix.GeneralLinearGroup.scalar (Fin 2) t * diagOne y * k) =
      (((μ 0 (t⁻¹ * y⁻¹) : ℂˣ) : ℂ) * ((μ 1 (t⁻¹ * y⁻¹) : ℂˣ) : ℂ) * ((θ₀ (t⁻¹ * y⁻¹) : ℂˣ) : ℂ)) *
        ((((‖(t : F)‖ : ℝ) : ℂ) ^ 2 * ((‖(y : F)‖ : ℝ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) : ℝ) : ℂ)) *
          (((‖(t : F)‖ : ℝ) : ℂ) ^ 2 * ((‖(y : F)‖ : ℝ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) : ℝ) : ℂ)) ^ s) *
        ((∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
            φ (antidiagonal2 p * upperUnipotent2 p x * (diagOne y * (w₀p * transposeInvN (Fin 2) k))) ∂(selfDualHaarAt ℚ p)) *
          w₂ (diagOne y * (w₀p * transposeInvN (Fin 2) k)) *
          phiHat p Φ₂ ((t : F) * (k : Mat) 1 0, (t : F) * (k : Mat) 1 1)) := by
  unfold dualD dualW dualF
  rw [dualWhittakerSlot_shell p hφ _ w₀p hw₀p t y k, dualPartnerSlot_shell p θ₀ w₂ hw₂cen w₀p hw₀p t y k,
    modulus_det_shell p t y k, row_one_shell p t y k 0, row_one_shell p t y k 1, add_sub_cancel_right]
  ring

theorem conjSet_shell_eq {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖ ≠ 0) (dn : ℤ × ℤ) :
    {x : ↥(unipotentGL2Hom (R := F)).range |
        (UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ ^ dn.2 *
            UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ dn.1)⁻¹ *
          (x : G) *
          (UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ ^ dn.2 *
            UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ dn.1) ∈
        AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤} =
    {x : ↥(unipotentGL2Hom (R := F)).range |
        (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ dn.1)⁻¹ * (x : G) *
          UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ dn.1 ∈
        AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤} := by
  ext x
  simp only [Set.mem_setOf_eq]
  have hc : ∀ g : G, UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ ^ dn.2 * g =
      g * UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ ^ dn.2 := by
    intro g
    rw [scalarPi_eq_scalar, ← map_zpow]
    exact RS22DualShell.scal_mul_comm p _ g
  set S := UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ ^ dn.2 with hS
  set D := UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ dn.1 with hD
  have hc' : ∀ g : G, S⁻¹ * g = g * S⁻¹ := by
    intro g
    have h1 := hc g
    calc S⁻¹ * g = S⁻¹ * (g * S) * S⁻¹ := by group
      _ = S⁻¹ * (S * g) * S⁻¹ := by rw [h1]
      _ = g * S⁻¹ := by group
  have : (S * D)⁻¹ * (x : G) * (S * D) = D⁻¹ * (x : G) * D := by
    rw [mul_inv_rev, mul_assoc D⁻¹, hc' (x : G)]
    group
  rw [this]

theorem lowerCutoff (θ₀ : Fˣ →* ℂˣ) (w₂ : G → ℂ)
    (hw₂law : ∀ (x : F) (g : G), w₂ (UnramifiedWhittaker.unipotent x * g) =
      NumberField.StandardAddChar.psiLocal ℚ p x * w₂ g)
    (hw₂sm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w₂ (g * k) = w₂ g)
    (hw₂adm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂ (g * h)),
        (∀ k ∈ U, ∀ g : G, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (hw₂cen : ∀ (z : Fˣ) (g : G), w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g) :
    ∃ m₁ : ℤ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ y : Fˣ,
      WithZero.exp m₁ < Valued.v (y : F) → w₂ (diagOne y * k) = 0 := by
  obtain ⟨C, A, τ, m₁, -, h⟩ :=
    AutomorphicForm.WhittakerModel.exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
      p θ₀ w₂ hw₂law hw₂sm hw₂adm hw₂cen
  refine ⟨m₁, fun k hk y hy => ?_⟩
  have hd : (diagOne y : G) = diagUnits2 y 1 := by
    refine Units.ext ?_
    change Matrix.diagonal ![(y : F), 1] = !![(y : F), 0; 0, ((1 : Fˣ) : F)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have h2 := (h k hk y 1).2
  rw [inv_one, mul_one] at h2
  rw [hd]
  exact h2 hy

theorem continuous_transposeInvN' : Continuous (transposeInvN (Fin 2) : G → G) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun g : G => ((transposeInvN (Fin 2) g : G) : Mat)
    simp only [coe_transposeInvN]
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : G => (((transposeInvN (Fin 2) g)⁻¹ : G) : Mat)
    simp only [coe_inv_transposeInvN]
    exact Units.continuous_val.matrix_transpose

theorem continuous_unipotentGL2' : Continuous fun y : F => (unipotentGL2 y : G) := by
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

theorem continuous_upperUnipotent2' : Continuous fun x : F => (upperUnipotent2 p x : G) := by
  have : (fun x : F => (upperUnipotent2 p x : G)) = fun x => (unipotentGL2 x : G) :=
    funext fun x => upperUnipotent2_eq_unipotentGL2 p x
  rw [this]; exact continuous_unipotentGL2' p

theorem continuous_of_rightInvariant {w : G → ℂ}
    (hwsm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w (g * k) = w g) : Continuous w := by
  obtain ⟨U, hU, hw⟩ := hwsm
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hS : IsOpen ((fun k : G => g * k) '' (U : Set G)) := (Homeomorph.mulLeft g).isOpenMap _ hU
  have hg : g ∈ (fun k : G => g * k) '' (U : Set G) := ⟨1, U.one_mem, mul_one g⟩
  refine (continuousAt_const : ContinuousAt (fun _ : G => w g) g).congr ?_
  filter_upwards [hS.mem_nhds hg] with x hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact (hw k hk g).symm

theorem continuous_modDet : Continuous fun g : G =>
    ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) := by
  have e : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ)) =
      fun g => ((‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ : ℝ) : ℂ) := by
    funext g
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]
  rw [e]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp
    (Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det))

theorem measurable_dualD {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    {w₂ : G → ℂ} (hw₂sm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w₂ (g * k) = w₂ g)
    (w₀p : G) (Φ₂ : F × F → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂) (s : ℂ) :
    Measurable (dualD p φ w₂ w₀p Φ₂ s) := by
  have hφc : Continuous φ := (mem_principalSeries2_iff.mp hφ).1.continuous

  have hK : Continuous fun q : G × F => NumberField.StandardAddChar.psiLocal ℚ p q.2 *
      φ (antidiagonal2 p * upperUnipotent2 p q.2 * (w₀p * transposeInvN (Fin 2) q.1)) := by
    refine ((NumberField.StandardAddChar.continuous_psiLocal ℚ p).comp continuous_snd).mul (hφc.comp ?_)
    exact (continuous_const.mul ((continuous_upperUnipotent2' p).comp continuous_snd)).mul
      (continuous_const.mul ((continuous_transposeInvN' p).comp continuous_fst))
  have h1 : Measurable (dualW p φ w₀p) := by
    unfold dualW
    exact (hK.measurable.stronglyMeasurable.integral_prod_right' (ν := (selfDualHaarAt ℚ p : Measure F))).measurable

  have hΦc : Continuous (phiHat p Φ₂) :=
    (LanglandsTunnell.TateLocal.isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
      p Φ₂ hΦ₂).1.1.continuous
  have h2 : Continuous (dualF p w₂ w₀p Φ₂) := by
    unfold dualF
    refine ((continuous_modDet p).mul ((continuous_of_rightInvariant p hw₂sm).comp
      (continuous_const.mul (continuous_transposeInvN' p)))).mul (hΦc.comp ?_)
    exact ((Units.continuous_val.matrix_elem 1 0)).prodMk (Units.continuous_val.matrix_elem 1 1)
  have h3 : Measurable fun g : G =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2) :=
    (continuous_modDet p).measurable.pow_const _
  unfold dualD
  exact (h1.mul h2.measurable).mul h3

local notation "OO" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (OO)) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ↔
      (∀ i j, (k : Mat) i j ∈ (OO)) ∧ ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ (OO) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral p h1, isLocalLevelOne_top_of_integral p h2⟩

theorem transposeInvN_mem_kzero {k : G} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    transposeInvN (Fin 2) k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  rw [mem_kzero_iff] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_transposeInvN, Matrix.transpose_apply]; exact hk.2 j i
  · rw [coe_inv_transposeInvN, Matrix.transpose_apply]; exact hk.1 j i

theorem antidiag_mem_kzero (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) :
    w₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have hinv : (w₀⁻¹ : G) = w₀ := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, hw₀, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [mem_kzero_iff, hinv, hw₀]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]

theorem diagOne_mem_kzero (u : Fˣ) (hu : Valued.v (u : F) = 1) :
    (diagOne u : G) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have hu' : (u : F) ∈ (OO) := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le
  have hui : ((u : F))⁻¹ ∈ (OO) := by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_
    rw [map_inv₀, hu, inv_one]
  have hui' : ((u⁻¹ : Fˣ) : F) ∈ (OO) := by rw [Units.val_inv_eq_inv_val]; exact hui
  rw [mem_kzero_iff, ← map_inv, RS22DualShell.coe_diagOne, RS22DualShell.coe_diagOne]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, zero_mem, one_mem, hu', hui, hui']

theorem valuation_det_of_mem_kzero {k : G} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1 := by
  rw [mem_kzero_iff] at hk
  have hint : ∀ (m : Mat), (∀ i j, m i j ∈ (OO)) → Valued.v m.det ≤ 1 := by
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
  have hprod : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G) : Mat).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G) : Mat).det) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

theorem modulus_det_of_mem_kzero {k : G} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    (modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) : ℝ) = 1 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm, NumberField.FinitePlace.norm_def,
    valuation_det_of_mem_kzero p hk, map_one, NNReal.coe_one]

theorem valued_varpiU_zpow {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    Valued.v ((((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ n : Fˣ)) : F) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_eq_mul, mul_one,
    Int.cast_id]

theorem modulus_varpiU_zpow {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    (modulus ((((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ n : Fˣ)) : F) : ℝ) = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n) :=
  (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.2.2.1
    n ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ n) (valued_varpiU_zpow p hπ hϖ n)

theorem norm_varpiU_zpow {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    ‖((((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ n : Fˣ)) : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n) := by
  rw [← modulus_varpiU_zpow p hπ hϖ n, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]

theorem ofReal_absNorm_zpow_cpow (m : ℤ) (s : ℂ) :
    ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ m : ℝ) : ℂ) ^ s = qN p ^ ((m : ℂ) * s) := by
  have hN : (0 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show 0 < Ideal.absNorm p.asIdeal by omega)
  have hlog : Complex.log (qN p) = ((Real.log ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [qN, show ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) = ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.ofReal_log hN.le]
  rw [Complex.ofReal_zpow, show ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ)) : ℂ) = qN p by simp [qN],
    ← Complex.cpow_intCast, ← Complex.cpow_mul]
  · rw [hlog, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact neg_lt_zero.mpr Real.pi_pos
  · rw [hlog, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact Real.pi_pos.le

theorem measurableSet_kzero :
    MeasurableSet ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) :=
  (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).2.measurableSet

open RS22DualShell in

theorem setIntegral_dualD_shell {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    (θ₀ : Fˣ →* ℂˣ) (w₂ : G → ℂ)
    (hw₂cen : ∀ (z : Fˣ) (g : G), w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (Φ₂ : F × F → ℂ)
    {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) = WithZero.exp (-1 : ℤ)) (μ₂ : Measure G) (s : ℂ) (dn : ℤ × ℤ) :
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G),
        dualD p φ w₂ w₀p Φ₂ s
          (UnramifiedWhittaker.scalarPi (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ ^ dn.2 *
            UnramifiedWhittaker.diagZ (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ dn.1 * k) ∂μ₂ =
      qN p ^ (-(((2 * dn.2 + dn.1 : ℤ)) : ℂ) * s) *
        ((((μ 0 (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2)⁻¹ * ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1)⁻¹) : ℂˣ) : ℂ) *
            ((μ 1 (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2)⁻¹ * ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1)⁻¹) : ℂˣ) : ℂ) *
            ((θ₀ (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2)⁻¹ * ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1)⁻¹) : ℂˣ) : ℂ)) *
          ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-(2 * dn.2 + dn.1)) : ℝ) : ℂ) *
          ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G),
            (∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x *
                  (diagOne ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1) * (w₀p * transposeInvN (Fin 2) k))) ∂(selfDualHaarAt ℚ p)) *
              w₂ (diagOne ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1) * (w₀p * transposeInvN (Fin 2) k)) *
              phiHat p Φ₂ ((((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2 : Fˣ) : F) * (k : Mat) 1 0, (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2 : Fˣ) : F) * (k : Mat) 1 1) ∂μ₂) := by
  set t : Fˣ := (Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2 with ht
  set y : Fˣ := (Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1 with hy
  set r : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-(2 * dn.2 + dn.1)) with hr
  have hnt : ‖(t : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-dn.2) := norm_varpiU_zpow p hπ hϖ dn.2
  have hny : ‖(y : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-dn.1) := norm_varpiU_zpow p hπ hϖ dn.1
  have hN0 : ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hr' : ((‖(t : F)‖ : ℝ) : ℂ) ^ 2 * ((‖(y : F)‖ : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
    rw [hnt, hny, hr]
    push_cast
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (by exact_mod_cast hN0)]
    congr 1; ring

  have hcongr : ∀ k ∈ ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G),
      dualD p φ w₂ w₀p Φ₂ s
          (UnramifiedWhittaker.scalarPi (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ ^ dn.2 *
            UnramifiedWhittaker.diagZ (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ dn.1 * k) =
        ((((μ 0 (t⁻¹ * y⁻¹) : ℂˣ) : ℂ) * ((μ 1 (t⁻¹ * y⁻¹) : ℂˣ) : ℂ) * ((θ₀ (t⁻¹ * y⁻¹) : ℂˣ) : ℂ)) *
          (((r : ℝ) : ℂ) * ((r : ℝ) : ℂ) ^ s)) *
        ((∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
              φ (antidiagonal2 p * upperUnipotent2 p x * (diagOne y * (w₀p * transposeInvN (Fin 2) k))) ∂(selfDualHaarAt ℚ p)) *
            w₂ (diagOne y * (w₀p * transposeInvN (Fin 2) k)) *
            phiHat p Φ₂ ((t : F) * (k : Mat) 1 0, (t : F) * (k : Mat) 1 1)) := by
    intro k hk
    rw [shellElt_eq, dualD_shell p hφ θ₀ w₂ hw₂cen w₀p hw₀p Φ₂ s t y k, modulus_det_of_mem_kzero p hk]
    push_cast
    rw [mul_one, hr']
  rw [setIntegral_congr_fun (measurableSet_kzero p) hcongr, integral_const_mul]
  have hrs : ((r : ℝ) : ℂ) ^ s = qN p ^ (-(((2 * dn.2 + dn.1 : ℤ)) : ℂ) * s) := by
    rw [hr, ofReal_absNorm_zpow_cpow]; push_cast; ring_nf
  rw [hrs]
  ring

def chiFac (μ : Fin 2 → (Fˣ →* ℂˣ)) (θ₀ : Fˣ →* ℂˣ) {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0) (dn : ℤ × ℤ) : ℂ :=
  ((μ 0 (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2)⁻¹ * ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1)⁻¹) : ℂˣ) : ℂ) *
    ((μ 1 (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2)⁻¹ * ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1)⁻¹) : ℂˣ) : ℂ) *
    ((θ₀ (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2)⁻¹ * ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1)⁻¹) : ℂˣ) : ℂ)

def shellK (φ : G → ℂ) (w₂ : G → ℂ) (w₀p : G) (Φ₂ : F × F → ℂ) {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0) (μ₂ : Measure G) (dn : ℤ × ℤ) : ℂ :=
  ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G),
    (∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (antidiagonal2 p * upperUnipotent2 p x *
          (diagOne ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1) * (w₀p * transposeInvN (Fin 2) k))) ∂(selfDualHaarAt ℚ p)) *
      w₂ (diagOne ((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.1) * (w₀p * transposeInvN (Fin 2) k)) *
      phiHat p Φ₂ ((((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2 : Fˣ) : F) * (k : Mat) 1 0, (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ dn.2 : Fˣ) : F) * (k : Mat) 1 1) ∂μ₂

def volFac {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0) (μN₂ : Measure ↥(unipotentGL2Hom (R := F)).range) (n₁ : ℤ) : ℂ :=
  (((μN₂ {x : ↥(unipotentGL2Hom (R := F)).range |
      (UnramifiedWhittaker.diagZ (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ n₁)⁻¹ * (x : G) *
        UnramifiedWhittaker.diagZ (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ n₁ ∈
      AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤})⁻¹).toReal : ℂ)

def tauFun (μ : Fin 2 → (Fˣ →* ℂˣ)) (φ : G → ℂ) (θ₀ : Fˣ →* ℂˣ) (w₂ : G → ℂ) (w₀p : G) (Φ₂ : F × F → ℂ)
    {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0) (μ₂ : Measure G) (μN₂ : Measure ↥(unipotentGL2Hom (R := F)).range) (dn : ℤ × ℤ) : ℂ :=
  volFac p hπ μN₂ dn.1 *
    (chiFac p μ θ₀ hπ dn * ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-(2 * dn.2 + dn.1)) : ℝ) : ℂ) *
      shellK p φ w₂ w₀p Φ₂ hπ μ₂ dn)

theorem hasSum_tau {μ : Fin 2 → (Fˣ →* ℂˣ)} {φ : G → ℂ} (hφ : φ ∈ principalSeries2 p μ)
    (θ₀ : Fˣ →* ℂˣ) (w₂ : G → ℂ)
    (hw₂law : ∀ (x : F) (g : G), w₂ (UnramifiedWhittaker.unipotent x * g) =
      NumberField.StandardAddChar.psiLocal ℚ p x * w₂ g)
    (hw₂sm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w₂ (g * k) = w₂ g)
    (hw₂cen : ∀ (z : Fˣ) (g : G), w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (Φ₂ : F × F → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)
    {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) = WithZero.exp (-1 : ℤ))
    (μ₂ : Measure G) [μ₂.IsHaarMeasure] (μN₂ : Measure ↥(unipotentGL2Hom (R := F)).range) [μN₂.IsHaarMeasure]
    (s : ℂ) (hint : Integrable (dualD p φ w₂ w₀p Φ₂ s)
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := F)).range μN₂))) :
    HasSum (fun dn : ℤ × ℤ => qN p ^ (-(((2 * dn.2 + dn.1 : ℤ)) : ℂ) * s) *
        tauFun p μ φ θ₀ w₂ w₀p Φ₂ hπ μ₂ μN₂ dn)
      (∫ g, dualD p φ w₂ w₀p Φ₂ s g ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := F)).range μN₂))) := by
  obtain ⟨-, -, hHS⟩ := AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 ℚ p ϖ hπ hϖ
    μ₂ μN₂ (dualD p φ w₂ w₀p Φ₂ s) (measurable_dualD p hφ hw₂sm w₀p Φ₂ hΦ₂ s)
    (D0_invariant p hφ w₂ hw₂law w₀p hw₀p Φ₂ s) hint
  refine (hHS.congr_fun fun dn => ?_)

  rw [setIntegral_dualD_shell p hφ θ₀ w₂ hw₂cen w₀p hw₀p Φ₂ hπ hϖ μ₂ s dn, conjSet_shell_eq p hπ dn]
  simp only [tauFun, volFac, chiFac, shellK]
  ring

theorem row_one_diagOne_mul (u : Fˣ) (k : G) (j : Fin 2) :
    ((diagOne u * k : G) : Mat) 1 j = (k : Mat) 1 j := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, RS22DualShell.coe_diagOne, Matrix.diagonal]

theorem varpiU_zpow_coe {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ ≠ 0) (n : ℤ) :
    (((Units.mk0 (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) hπ) ^ n : Fˣ) : F) =
      (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p) F ϖ) ^ n := by
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem D1_dualConv
    (μ : Fin 2 → (Fˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ) (hσ : ∀ (i : Fin 2) (a : Fˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : G → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (θ₀ : Fˣ →* ℂˣ) (w₂ : G → ℂ)
    (hw₂law : ∀ (x : F) (g : G), w₂ (UnramifiedWhittaker.unipotent x * g) =
      NumberField.StandardAddChar.psiLocal ℚ p x * w₂ g)
    (hw₂sm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w₂ (g * k) = w₂ g)
    (hw₂adm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂ (g * h)),
        (∀ k ∈ U, ∀ g : G, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (hw₂cen : ∀ (z : Fˣ) (g : G), w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0])
    (Φ₂ : F × F → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂) :
    ∃ σ₃ : ℝ, ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := F)).range) [μN₂.IsHaarMeasure] (s : ℂ), σ₃ < s.re →
        Integrable (dualD p φ w₂ w₀p Φ₂ s)
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := F)).range μN₂)) := by
  obtain ⟨σ₃, h⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_dual_rsIntegrand22_withDensity_of_admissible_of_chamber
      p θ₀ w₂ hw₂law hw₂sm hw₂adm hw₂cen μ hμ σ hσ h01 φ hφ Φ₂ hΦ₂ w₀p hw₀p
  exact ⟨σ₃, fun μ₂ _ μN₂ _ s hs => h μ₂ μN₂ s hs⟩

theorem D4_upperCutoff
    (μ : Fin 2 → (Fˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ) (hσ : ∀ (i : Fin 2) (a : Fˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : G → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (θ₀ : Fˣ →* ℂˣ) (w₂ : G → ℂ)
    (hw₂law : ∀ (x : F) (g : G), w₂ (UnramifiedWhittaker.unipotent x * g) =
      NumberField.StandardAddChar.psiLocal ℚ p x * w₂ g)
    (hw₂sm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w₂ (g * k) = w₂ g)
    (hw₂cen : ∀ (z : Fˣ) (g : G), w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g)
    (wJ : G) (hwJ : (wJ : Mat) = !![0, 1; -1, 0])

    (hdualZeta : ∀ (i : Fin 2) (h : G), ∃ (Pd : Polynomial ℂ) (md : ℤ) (σ₁ : ℝ), ∀ s : ℂ, s.re < σ₁ →
      Integrable (fun y : Fˣ => w₂ (diagOne y * wJ * h) * (((μ i y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
      ∫ y : Fˣ, w₂ (diagOne y * wJ * h) * (((μ i y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0])
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) = WithZero.exp (-1 : ℤ))
    (μ₂ : Measure G) [μ₂.IsHaarMeasure] :
    ∃ nup : ℤ, ∀ n₁ : ℤ, nup ≤ n₁ →
      ∀ (Gw : G → ℂ), Measurable Gw → (∃ B : ℝ, ∀ k, ‖Gw k‖ ≤ B) →
        (∀ (u : Fˣ), Valued.v (u : F) = 1 → ∀ k : G, Gw (diagOne u * k) = Gw k) →
        ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G),
            dualW p φ w₀p (diagOne ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ) ^ n₁) * k) *
              w₂ (w₀p * transposeInvN (Fin 2)
                (diagOne ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ) ^ n₁) * k)) * Gw k ∂μ₂ = 0 :=
  LanglandsTunnell.RankinSelberg.exists_forall_le_setIntegral_localLevelOne_dualJacquet_mul_partner_mul_eq_zero_of_dualTorusZeta_polynomial
    p μ hμ σ hσ h01 φ hφ θ₀ w₂ hw₂law hw₂sm hw₂cen wJ hwJ hdualZeta w₀p hw₀p hπ hϖ μ₂

end RS22Dual

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
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
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (E : Fin 2 → ℂ) (e : Fin 2 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe1 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (m : ℤ) (P : Polynomial ℂ) (σ₃ : ℝ), ∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) *
                (1 - ((((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) *
                      ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)))⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) *
                    (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
  intro μ₂ _ μN₂ _ w₂ hw₂V
  classical
  letI : MeasurableSpace (p.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ p
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := AutomorphicForm.localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := AutomorphicForm.borelSpace_localGLBorel ℚ p

  have hKopen : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have hw₂law' : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂ g :=
    fun x => RS22SpanKit.law_of_mem_span w₂base (unipotent x) _ (hw₂law x) hw₂V
  have hw₂cen' : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g :=
    fun z => RS22SpanKit.law_of_mem_span w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z) _ (hcentral z) hw₂V
  have hw₂sm' : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g, w₂ (g * k) = w₂ g :=
    RS22SpanKit.exists_open_stabilizer_of_mem_span w₂base _ hKopen hw₂K hw₂V
  have hw₂adm' : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) := by
    intro U hU
    obtain ⟨B, hB⟩ := hw₂adm U hU
    exact ⟨B, fun w' hw' hinv => hB w' (RS22SpanKit.span_le_span_of_mem w₂ w₂base hw₂V hw') hinv⟩

  have hdualZeta : ∀ (i : Fin 2) (h : GL (Fin 2) (p.adicCompletion ℚ)),
      ∃ (Pd : Polynomial ℂ) (md : ℤ) (σ₁ : ℝ), ∀ s : ℂ, s.re < σ₁ →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ => w₂ (diagOne y * wJ * h) * (((μ i y : ℂˣ) : ℂ))⁻¹ *
            (((θ₀ y : ℂˣ) : ℂ))⁻¹ * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        ∫ y : (p.adicCompletion ℚ)ˣ, w₂ (diagOne y * wJ * h) * (((μ i y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
            ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro i h
    have hmem := RS22SpanKit.translate_mem_span w₂base h hw₂V
    fin_cases i
    · obtain ⟨P, Pd, m, md, σ₀, σ₁, -, -, h3, h4, -⟩ := hfe0 _ hmem
      exact ⟨Pd, md, σ₁, fun s hs => ⟨h3 s hs, h4 s hs⟩⟩
    · obtain ⟨P, Pd, m, md, σ₀, σ₁, -, -, h3, h4, -⟩ := hfe1 _ hmem
      exact ⟨Pd, md, σ₁, fun s hs => ⟨h3 s hs, h4 s hs⟩⟩

  obtain ⟨σ₃, hD1⟩ := RS22Dual.D1_dualConv p μ hμ σ hσ h01 φ hφ θ₀ w₂ hw₂law' hw₂sm' hw₂adm' hw₂cen' w₀p hw₀p Φ₂ hΦ₂
  obtain ⟨nlo, nhi, hlohi, hD3⟩ := RS22Dual.D3_centreWindow p Φ₂ hΦ₂ hπ hϖ
  obtain ⟨m₁, hlow⟩ := RS22Dual.lowerCutoff p θ₀ w₂ hw₂law' hw₂sm' hw₂adm' hw₂cen'
  obtain ⟨nup, hD4⟩ := RS22Dual.D4_upperCutoff p μ hμ σ hσ h01 φ hφ θ₀ w₂ hw₂law' hw₂sm' hw₂cen' wJ hwJ hdualZeta
    w₀p hw₀p hπ hϖ μ₂

  set τ : ℤ × ℤ → ℂ := RS22Dual.tauFun p μ φ θ₀ w₂ w₀p Φ₂ hπ μ₂ μN₂ with hτ
  set c₀ : ℂ := ((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) with hc₀
  set ρ : ℂ := c₀⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) with hρ
  set A : ℤ → ℂ := fun n₁ => ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))),
    (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (antidiagonal2 p * upperUnipotent2 p x *
          (diagOne ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n₁) * (w₀p * transposeInvN (Fin 2) k))) ∂(selfDualHaarAt ℚ p)) *
      w₂ (diagOne ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n₁) * (w₀p * transposeInvN (Fin 2) k)) ∂μ₂ with hA
  set α : ℤ → ℂ := fun n₁ => ρ ^ nhi * (RS22Dual.volFac p hπ μN₂ n₁ *
      (c₀ ^ (-n₁) * ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n₁) : ℝ) : ℂ) *
        (RS22Dual.phiHat p Φ₂ (0, 0) * A n₁))) with hα
  have hsupp₂ : ∀ n : ℤ × ℤ, n.2 < nlo → τ n = 0 := by
    intro n hn
    have h0 : RS22Dual.shellK p φ w₂ w₀p Φ₂ hπ μ₂ n = 0 := by
      unfold RS22Dual.shellK
      refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
      rw [RS22Dual.varpiU_zpow_coe p hπ n.2, ((hD3 k hk n.2).1 hn), mul_zero]
    simp only [hτ, RS22Dual.tauFun, h0, mul_zero]
  have hΦc : Continuous (RS22Dual.phiHat p Φ₂) :=
    (LanglandsTunnell.TateLocal.isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
      p Φ₂ hΦ₂).1.1.continuous
  have hΦb : ∃ B : ℝ, ∀ v, ‖RS22Dual.phiHat p Φ₂ v‖ ≤ B :=
    (LanglandsTunnell.TateLocal.isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
      p Φ₂ hΦ₂).1.2.exists_bound_of_continuous hΦc
  have hsupp₁ : ∀ n : ℤ × ℤ, (n.1 < -m₁ ∨ nup - 1 < n.1) → τ n = 0 := by
    intro n hn
    have h0 : RS22Dual.shellK p φ w₂ w₀p Φ₂ hπ μ₂ n = 0 := by
      rcases hn with hn | hn
      ·
        unfold RS22Dual.shellK
        refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
        have hkt : w₀p * transposeInvN (Fin 2) k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ :=
          Subgroup.mul_mem _ (RS22Dual.antidiag_mem_kzero p w₀p hw₀p) (RS22Dual.transposeInvN_mem_kzero p hk)
        have hv : WithZero.exp m₁ < Valued.v ((((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n.1 : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) := by
          rw [RS22Dual.valued_varpiU_zpow p hπ hϖ n.1]
          exact WithZero.exp_lt_exp.mpr (by omega)
        rw [hlow _ hkt _ hv, mul_zero, zero_mul]
      ·
        have hle : nup ≤ n.1 := by omega
        set y : (p.adicCompletion ℚ)ˣ := (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n.1 with hy
        set t : (p.adicCompletion ℚ)ˣ := (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n.2 with ht
        set Gw : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun k =>
          RS22Dual.phiHat p Φ₂ ((t : p.adicCompletion ℚ) * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
            (t : p.adicCompletion ℚ) * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) with hGw
        have hGm : Measurable Gw :=
          (hΦc.comp (((continuous_const.mul (Units.continuous_val.matrix_elem 1 0))).prodMk
            (continuous_const.mul (Units.continuous_val.matrix_elem 1 1)))).measurable
        have hGb : ∃ B : ℝ, ∀ k, ‖Gw k‖ ≤ B := by
          obtain ⟨B, hB⟩ := hΦb; exact ⟨B, fun k => hB _⟩
        have hGinv : ∀ (u : (p.adicCompletion ℚ)ˣ), Valued.v (u : p.adicCompletion ℚ) = 1 →
            ∀ k : GL (Fin 2) (p.adicCompletion ℚ), Gw (diagOne u * k) = Gw k := by
          intro u _ k
          simp only [hGw, RS22Dual.row_one_diagOne_mul]
        have hD4' := hD4 n.1 hle Gw hGm hGb hGinv

        set C : ℂ := ((μ 0 (1⁻¹ * y⁻¹) : ℂˣ) : ℂ) * ((μ 1 (1⁻¹ * y⁻¹) : ℂˣ) : ℂ) * ((θ₀ (1⁻¹ * y⁻¹) : ℂˣ) : ℂ) with hC
        have hC0 : C ≠ 0 := by simp only [hC]; exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Units.ne_zero _)
        have hrel : ∀ k : GL (Fin 2) (p.adicCompletion ℚ),
            RS22Dual.dualW p φ w₀p (diagOne y * k) * w₂ (w₀p * transposeInvN (Fin 2) (diagOne y * k)) * Gw k =
              C * ((∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ (antidiagonal2 p * upperUnipotent2 p x *
                    (diagOne y * (w₀p * transposeInvN (Fin 2) k))) ∂(selfDualHaarAt ℚ p)) *
                w₂ (diagOne y * (w₀p * transposeInvN (Fin 2) k)) * Gw k) := by
          intro k
          have e1 : (diagOne y * k : GL (Fin 2) (p.adicCompletion ℚ)) =
              Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * diagOne y * k := by rw [map_one, one_mul]
          unfold RS22Dual.dualW
          rw [e1, RS22DualShell.dualWhittakerSlot_shell p hφ _ w₀p hw₀p 1 y k,
            RS22DualShell.dualPartnerSlot_shell p θ₀ w₂ hw₂cen' w₀p hw₀p 1 y k]
          simp only [hC]; ring
        have hint0 : ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
            Set (GL (Fin 2) (p.adicCompletion ℚ))),
            C * ((∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ (antidiagonal2 p * upperUnipotent2 p x *
                    (diagOne y * (w₀p * transposeInvN (Fin 2) k))) ∂(selfDualHaarAt ℚ p)) *
                w₂ (diagOne y * (w₀p * transposeInvN (Fin 2) k)) * Gw k) ∂μ₂ = 0 := by
          rw [← hD4']
          exact (setIntegral_congr_fun (RS22Dual.measurableSet_kzero p) fun k _ => (hrel k).symm)
        rw [integral_const_mul, mul_eq_zero] at hint0
        rcases hint0 with h | h
        · exact absurd h hC0
        · unfold RS22Dual.shellK; simpa [hGw, hy, ht] using h
    simp only [hτ, RS22Dual.tauFun, h0, mul_zero]
  have hN0 : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc₀0 : c₀ ≠ 0 := by
    simp only [hc₀]; exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Units.ne_zero _)
  have hNc : ((Ideal.absNorm p.asIdeal : ℂ)) = ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) := rfl
  have hρ' : ρ = c₀⁻¹ * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-2 : ℤ) := by
    rw [hρ, hNc, show (-(2 : ℂ)) = ((-2 : ℤ) : ℂ) by norm_num, Complex.cpow_intCast]
  have hρ0 : ρ ≠ 0 := by
    rw [hρ']; exact mul_ne_zero (inv_ne_zero hc₀0) (zpow_ne_zero _ hN0)
  have hdeep : ∀ n : ℤ × ℤ, nhi ≤ n.2 → τ n = ρ ^ (n.2 - nhi).toNat * α n.1 := by
    intro n hn

    have hK : RS22Dual.shellK p φ w₂ w₀p Φ₂ hπ μ₂ n = A n.1 * RS22Dual.phiHat p Φ₂ (0, 0) := by
      unfold RS22Dual.shellK
      rw [← integral_mul_const]
      refine setIntegral_congr_fun (RS22Dual.measurableSet_kzero p) fun k hk => ?_
      rw [RS22Dual.varpiU_zpow_coe p hπ n.2, (hD3 k hk n.2).2 hn]

    have hchi : RS22Dual.chiFac p μ θ₀ hπ n = c₀ ^ (-n.2 + -n.1) := by
      have e : (((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n.2)⁻¹ * ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n.1)⁻¹ : (p.adicCompletion ℚ)ˣ) = (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (-n.2 + -n.1) := by
        rw [← zpow_neg, ← zpow_neg, ← zpow_add]
      simp only [RS22Dual.chiFac, e, map_zpow, Units.val_zpow_eq_zpow_val, hc₀, mul_zpow]
      ring

    have hNz : ∀ m : ℤ, ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ m : ℝ) : ℂ) = ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ m := by
      intro m; push_cast; rfl

    have hρpow : ρ ^ (n.2 - nhi).toNat * ρ ^ nhi =
        c₀ ^ (-n.2) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-2 * n.2) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hn), ← zpow_add₀ hρ0, sub_add_cancel, hρ',
        mul_zpow, inv_zpow', zpow_mul]

    simp only [hτ, RS22Dual.tauFun, hα, hK, hchi, hNz]
    rw [show c₀ ^ (-n.2 + -n.1) = c₀ ^ (-n.2) * c₀ ^ (-n.1) from zpow_add₀ hc₀0 _ _,
      show ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-(2 * n.2 + n.1)) =
        ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-2 * n.2) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-n.1) by
          rw [← zpow_add₀ hN0]; congr 1; ring]
    rw [show ρ ^ (n.2 - nhi).toNat * (ρ ^ nhi * (RS22Dual.volFac p hπ μN₂ n.1 *
        (c₀ ^ (-n.1) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-n.1) * (RS22Dual.phiHat p Φ₂ (0, 0) * A n.1)))) =
        (ρ ^ (n.2 - nhi).toNat * ρ ^ nhi) * (RS22Dual.volFac p hπ μN₂ n.1 *
        (c₀ ^ (-n.1) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-n.1) * (RS22Dual.phiHat p Φ₂ (0, 0) * A n.1))) by ring,
      hρpow]
    ring
  obtain ⟨m, P, hSER⟩ := RS22Dual.SER p τ ρ nlo nhi (-m₁) (nup - 1) α hsupp₂ hsupp₁ hdeep
  refine ⟨m, P, σ₃, fun s hs => ⟨hD1 μ₂ μN₂ s hs, ?_⟩⟩
  have hHS := RS22Dual.hasSum_tau p hφ θ₀ w₂ hw₂law' hw₂sm' hw₂cen' w₀p hw₀p Φ₂ hΦ₂ hπ hϖ μ₂ μN₂ s
    (hD1 μ₂ μN₂ s hs)
  have hmain := hSER s _ hHS
  have hI : RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
      (s + 1 / 2)
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p))
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
          w₂ (w₀p * transposeInvN (Fin 2) g) *
          (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
            NumberField.StandardAddChar.psiLocal ℚ p
              (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 +
                u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
            ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) =
      ∫ g, RS22Dual.dualD p φ w₂ w₀p Φ₂ s g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := rfl
  rw [hI]
  have hq : RS22Dual.qN p = (Ideal.absNorm p.asIdeal : ℂ) := rfl
  rw [hq] at hmain
  rw [show (1 - (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ))⁻¹ *
      (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
      (1 - ρ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) by rw [hρ, hc₀, mul_assoc]]
  exact hmain

end

end S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial (solution)
