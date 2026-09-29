-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d11a0c66-ebba-591c-8025-691437bad5f5

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

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

set_option maxHeartbeats 1600000

namespace L1Box46

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "νa" => (selfDualHaarAt ℚ p)
local notation "νx" => (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ)

theorem one_lt_qN : (1 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) :=
  NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p

theorem norm_le_norm_iff_v_le_v (x y : F) : ‖x‖ ≤ ‖y‖ ↔ Valued.v x ≤ Valued.v y := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, NNReal.coe_le_coe,
    (WithZeroMulInt.toNNReal_strictMono (one_lt_qN p)).le_iff_le]

theorem norm_eq_norm_iff_v_eq_v (x y : F) : ‖x‖ = ‖y‖ ↔ Valued.v x = Valued.v y := by
  constructor
  · intro h; exact le_antisymm ((norm_le_norm_iff_v_le_v p x y).1 h.le) ((norm_le_norm_iff_v_le_v p y x).1 h.ge)
  · intro h; exact le_antisymm ((norm_le_norm_iff_v_le_v p x y).2 h.le) ((norm_le_norm_iff_v_le_v p y x).2 h.ge)

theorem norm_eq_one_of_v_eq_one {x : F} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [← norm_one (α := F)]; exact (norm_eq_norm_iff_v_eq_v p x 1).2 (by rw [h, Valuation.map_one])

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl

theorem v_eq_one_of_v_sub_one_le {a : F} {M : ℤ} (hM : 1 ≤ M) (h : Valued.v (a - 1) ≤ WithZero.exp (-M)) : Valued.v a = 1 := by
  have hlt : Valued.v (a - 1) < 1 := by
    refine lt_of_le_of_lt h ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have := Valuation.map_one_add_of_lt (Valued.v : Valuation F _) hlt
  rwa [add_sub_cancel] at this

theorem exp_neg_le_one {M : ℤ} (hM : 0 ≤ M) : WithZero.exp (-M) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem mem_integers_of_v_le {x : F} {M : ℤ} (hM : 0 ≤ M) (h : Valued.v x ≤ WithZero.exp (-M)) : x ∈ (O) :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_trans h (exp_neg_le_one hM))

theorem unipotentGL2_eq_unipotent (x : F) : (unipotentGL2 x : G) = unipotent x := Units.ext rfl

theorem coe_chart (x : F) (a₁ a₂ : Fˣ) (y : F) :
    ((unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) : M2) =
      !![(a₁ : F) + x * (a₂ : F) * y, x * (a₂ : F); (a₂ : F) * y, (a₂ : F)] := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_diagUnits2]
  show !![(1 : F), x; 0, 1] * !![(a₁ : F), 0; 0, (a₂ : F)] * !![(1 : F), 0; y, 1] = _
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_chart (x : F) (a₁ a₂ : Fˣ) (y : F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) = a₁ * a₂ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_chart, Matrix.det_fin_two_of, Units.val_mul]
  ring

theorem diagOne_coe (a : Fˣ) : ((diagOne a : G) : M2) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem chart_eq (x : F) (a₁ a₂ : Fˣ) (y : F) :
    (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) = unipotent x * (diagOne a₁ * (diagUnits2 1 a₂ * lowerUnipotentGL2 y)) := by
  have hd : (diagUnits2 a₁ a₂ : G) = diagOne a₁ * diagUnits2 1 a₂ := by
    apply Units.ext
    rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, diagOne_coe, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [unipotentGL2_eq_unipotent, hd]; simp only [mul_assoc]

section Pointwise

def boxSet (L Mb Mc Md : ℤ) : Set M2 :=
  {X : M2 | Valued.v (X 0 0) ≤ WithZero.exp L ∧ Valued.v (X 0 1) ≤ WithZero.exp (-Mb) ∧
      Valued.v (X 1 0) ≤ WithZero.exp (-Mc) ∧ Valued.v (X 1 1 - 1) ≤ WithZero.exp (-Md)}

def Φb (L Mb Mc Md : ℤ) : M2 → ℂ := fun X => Set.indicator (boxSet p L Mb Mc Md) (fun _ => (1 : ℂ)) X

def Hfun (w : G → ℂ) (χ : Fˣ →* ℂˣ) (L Mb Mc Md : ℤ) (s : ℂ) (g : G) : ℂ :=
  w g * Φb p L Mb Mc Md (g : M2) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + 1 / 2)

def f1 (Mb : ℤ) (x : F) : ℂ := Set.indicator {x : F | Valued.v x ≤ WithZero.exp (-Mb)} (fun _ => (1 : ℂ)) x
def f2 (Md : ℤ) (a : Fˣ) : ℂ := Set.indicator {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} (fun _ => (1 : ℂ)) a
def f3 (w : G → ℂ) (χ : Fˣ →* ℂˣ) (L : ℤ) (s : ℂ) (a : Fˣ) : ℂ := Set.indicator {a : Fˣ | Valued.v (a : F) ≤ WithZero.exp L}
  (fun a => w (diagOne a) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (s - 1 / 2)) a
def f4 (Mc : ℤ) (y : F) : ℂ := Set.indicator {y : F | Valued.v y ≤ WithZero.exp (-Mc)} (fun _ => (1 : ℂ)) y

theorem mem_box_chart_iff {L Mb Mc Md : ℤ} (hL : 0 ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md) (x : F) (a₁ a₂ : Fˣ) (y : F) :
    ((unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) : M2) ∈ boxSet p L Mb Mc Md ↔
      Valued.v x ≤ WithZero.exp (-Mb) ∧ Valued.v ((a₂ : F) - 1) ≤ WithZero.exp (-Md) ∧
        Valued.v (a₁ : F) ≤ WithZero.exp L ∧ Valued.v y ≤ WithZero.exp (-Mc) := by
  rw [coe_chart]
  simp only [boxSet, Set.mem_setOf_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  have hxy_small : ∀ {x y : F}, Valued.v x ≤ WithZero.exp (-Mb) → Valued.v y ≤ WithZero.exp (-Mc) →
      Valued.v ((a₂ : F)) = 1 → Valued.v (x * (a₂ : F) * y) ≤ WithZero.exp L := by
    intro x y hx hy ha
    rw [map_mul, map_mul, ha, mul_one]
    calc Valued.v x * Valued.v y ≤ WithZero.exp (-Mb) * WithZero.exp (-Mc) := mul_le_mul' hx hy
      _ = WithZero.exp (-Mb + -Mc) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp L := by rw [WithZero.exp_le_exp]; omega
  constructor
  · rintro ⟨h00, h01, h10, h11⟩
    have ha : Valued.v (a₂ : F) = 1 := v_eq_one_of_v_sub_one_le p hMd h11
    have hx : Valued.v x ≤ WithZero.exp (-Mb) := by rw [map_mul, ha, mul_one] at h01; exact h01
    have hy : Valued.v y ≤ WithZero.exp (-Mc) := by rw [map_mul, ha, one_mul] at h10; exact h10
    refine ⟨hx, h11, ?_, hy⟩
    have : (a₁ : F) = ((a₁ : F) + x * (a₂ : F) * y) - x * (a₂ : F) * y := by ring
    rw [this]
    exact le_trans (Valuation.map_sub _ _ _) (max_le h00 (hxy_small hx hy ha))
  · rintro ⟨hx, h11, ha₁, hy⟩
    have ha : Valued.v (a₂ : F) = 1 := v_eq_one_of_v_sub_one_le p hMd h11
    refine ⟨?_, ?_, ?_, h11⟩
    · exact le_trans (Valuation.map_add _ _ _) (max_le ha₁ (hxy_small hx hy ha))
    · rw [map_mul, ha, mul_one]; exact hx
    · rw [map_mul, ha, one_mul]; exact hy

theorem pointwise (w : G → ℂ) (χ : Fˣ →* ℂˣ) {L Mb Mc Md : ℤ} (s : ℂ) (hwlaw : ∀ (x : F) (g : G), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (U : Subgroup G) (hU : ∀ k ∈ U, ∀ g : G, w (g * k) = w g)
    (hL : 0 ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (hstab : ∀ (a : Fˣ) (y : F), Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → Valued.v y ≤ WithZero.exp (-Mc) →
      diagUnits2 1 a * lowerUnipotentGL2 y ∈ U)
    (hχ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → χ a = 1)
    (x : F) (a₂ a₁ : Fˣ) (y : F) :
    (modulus (((a₂ * a₁⁻¹ : Fˣ)) : F)) • Hfun p w χ L Mb Mc Md s (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y) =
      f1 p Mb x * (f2 p Md a₂ * (f3 p w χ L s a₁ * f4 p Mc y)) := by
  by_cases hbox : Valued.v x ≤ WithZero.exp (-Mb) ∧ Valued.v ((a₂ : F) - 1) ≤ WithZero.exp (-Md) ∧
        Valued.v (a₁ : F) ≤ WithZero.exp L ∧ Valued.v y ≤ WithZero.exp (-Mc)
  · obtain ⟨hx, h11, ha₁, hy⟩ := hbox
    have ha : Valued.v (a₂ : F) = 1 := v_eq_one_of_v_sub_one_le p hMd h11
    have hmem := (mem_box_chart_iff p hL hMb hMc hMd x a₁ a₂ y).2 ⟨hx, h11, ha₁, hy⟩

    have hΦ : Φb p L Mb Mc Md ((unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) : M2) = 1 := by
      simp only [Φb]; rw [Set.indicator_of_mem hmem]
    have hψ : NumberField.StandardAddChar.psiLocal ℚ p x = 1 :=
      LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x (mem_integers_of_v_le p hMb hx)
    have hw : w (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y) = w (diagOne a₁) := by
      rw [chart_eq, hwlaw, hψ, one_mul, hU _ (hstab a₂ y h11 hy)]
    have hdet := det_chart p x a₁ a₂ y
    have hχ' : ((χ (Matrix.GeneralLinearGroup.det (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G)) : ℂˣ) : ℂ) = ((χ a₁ : ℂˣ) : ℂ) := by
      rw [hdet, map_mul, hχ a₂ h11, mul_one]
    have hma₂ : modulus ((a₂ : F)) = 1 := by
      apply NNReal.coe_injective
      rw [coe_modulus_eq_norm, NNReal.coe_one]; exact norm_eq_one_of_v_eq_one p ha
    have hmod : ((modulus ((Matrix.GeneralLinearGroup.det (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) : Fˣ) : F) : ℝ) : ℂ) =
        ((modulus (a₁ : F) : ℝ) : ℂ) := by
      rw [hdet, Units.val_mul, modulus_mul, hma₂, mul_one]
    have hdens : modulus (((a₂ * a₁⁻¹ : Fˣ)) : F) = (modulus (a₁ : F))⁻¹ := by
      rw [Units.val_mul, modulus_mul, hma₂, one_mul]
      have h1 : modulus (((a₁⁻¹ : Fˣ)) : F) * modulus (a₁ : F) = 1 := by
        rw [← modulus_mul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ a₁.ne_zero]
        apply NNReal.coe_injective; rw [coe_modulus_eq_norm, norm_one, NNReal.coe_one]
      exact eq_inv_of_mul_eq_one_left h1

    have e1 : f1 p Mb x = 1 := by
      have hx' : x ∈ {x : F | Valued.v x ≤ WithZero.exp (-Mb)} := hx
      simp only [f1]; rw [Set.indicator_of_mem hx']
    have e2 : f2 p Md a₂ = 1 := by
      have h' : a₂ ∈ {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} := h11
      simp only [f2]; rw [Set.indicator_of_mem h']
    have e4 : f4 p Mc y = 1 := by
      have h' : y ∈ {y : F | Valued.v y ≤ WithZero.exp (-Mc)} := hy
      simp only [f4]; rw [Set.indicator_of_mem h']
    have e3 : f3 p w χ L s a₁ = w (diagOne a₁) * ((χ a₁ : ℂˣ) : ℂ) * ((modulus (a₁ : F) : ℝ) : ℂ) ^ (s - 1 / 2) := by
      have h' : a₁ ∈ {a : Fˣ | Valued.v (a : F) ≤ WithZero.exp L} := ha₁
      simp only [f3]; rw [Set.indicator_of_mem h']
    rw [e1, e2, e4, e3, one_mul, one_mul, mul_one]
    simp only [Hfun]
    rw [hΦ, hw, hχ', hmod, hdens, mul_one]

    have hr : (0 : ℝ) < (modulus (a₁ : F) : ℝ) := by
      rw [coe_modulus_eq_norm]; exact norm_pos_iff.2 a₁.ne_zero
    have hrC : ((modulus (a₁ : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [NNReal.smul_def, NNReal.coe_inv, Complex.real_smul, Complex.ofReal_inv]
    have hsplit : ((modulus (a₁ : F) : ℝ) : ℂ) ^ (s + 1 / 2) = ((modulus (a₁ : F) : ℝ) : ℂ) ^ (s - 1 / 2) * ((modulus (a₁ : F) : ℝ) : ℂ) := by
      rw [show s + 1 / 2 = (s - 1 / 2) + 1 by ring, Complex.cpow_add _ _ hrC, Complex.cpow_one]
    rw [hsplit]
    field_simp
  ·
    have hnot : ((unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) : M2) ∉ boxSet p L Mb Mc Md :=
      fun h => hbox ((mem_box_chart_iff p hL hMb hMc hMd x a₁ a₂ y).1 h)
    have hΦ : Φb p L Mb Mc Md ((unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) : M2) = 0 := by
      simp only [Φb]; rw [Set.indicator_of_notMem hnot]
    have lhs0 : Hfun p w χ L Mb Mc Md s (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y) = 0 := by
      simp only [Hfun]; rw [hΦ]; ring
    rw [lhs0, smul_zero]

    simp only [not_and_or] at hbox
    rcases hbox with hx | h11 | ha₁ | hy
    · have hx' : x ∉ {x : F | Valued.v x ≤ WithZero.exp (-Mb)} := hx
      have : f1 p Mb x = 0 := by simp only [f1]; exact Set.indicator_of_notMem hx' _
      rw [this, zero_mul]
    · have h' : a₂ ∉ {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} := h11
      have : f2 p Md a₂ = 0 := by simp only [f2]; exact Set.indicator_of_notMem h' _
      rw [this, zero_mul, mul_zero]
    · have h' : a₁ ∉ {a : Fˣ | Valued.v (a : F) ≤ WithZero.exp L} := ha₁
      have : f3 p w χ L s a₁ = 0 := by simp only [f3]; exact Set.indicator_of_notMem h' _
      rw [this, zero_mul, mul_zero, mul_zero]
    · have h' : y ∉ {y : F | Valued.v y ≤ WithZero.exp (-Mc)} := hy
      have : f4 p Mc y = 0 := by simp only [f4]; exact Set.indicator_of_notMem h' _
      rw [this, mul_zero, mul_zero, mul_zero]

end Pointwise

section Setup

scoped instance : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_units : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_GL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem measurable_unitsVal : Measurable (Units.val : Fˣ → F) := comap_measurable Units.val

scoped instance borelSpace_units : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := HeightOneSpectrum.adicCompletion ℚ p)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := HeightOneSpectrum.adicCompletion ℚ p)]
    rfl⟩

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p

scoped instance isHaarMeasure_units : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p _

theorem exists_uniformizer : ∃ ϖ : F, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation ℚ p)).symm π : F),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

theorem v_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem isOpen_vball (m : ℤ) : IsOpen {x : F | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hset : {x : F | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow p hϖ, WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m := mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem isClosed_vball (γ : WithZero (Multiplicative ℤ)) : IsClosed {x : F | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
  have hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hx)
  filter_upwards [Valued.locally_const hx0] with y hy
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hy]; exact hx

theorem measurableSet_vball (γ : WithZero (Multiplicative ℤ)) : MeasurableSet {x : F | Valued.v x ≤ γ} :=
  (isClosed_vball p γ).measurableSet

theorem isCompact_integers : IsCompact ((HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F)) := by
  rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
  exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact

theorem vball_lt_top {M : ℤ} (hM : 0 ≤ M) : (selfDualHaarAt ℚ p) {x : F | Valued.v x ≤ WithZero.exp (-M)} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (isCompact_integers p).measure_lt_top
  intro x hx; exact mem_integers_of_v_le p hM hx

theorem vball_pos (M : ℤ) : 0 < (selfDualHaarAt ℚ p) {x : F | Valued.v x ≤ WithZero.exp (-M)} :=
  (isOpen_vball p _).measure_pos _ ⟨0, by simp⟩

theorem isOpen_prinUnits (M : ℤ) : IsOpen {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} :=
  (isOpen_vball p _).preimage (Units.continuous_val.sub continuous_const)

theorem measurableSet_prinUnits (M : ℤ) : MeasurableSet {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} :=
  (isOpen_prinUnits p M).measurableSet

theorem isCompact_units_sphere : IsCompact {u : Fˣ | Valued.v (u : F) = 1} := by
  have hS : IsCompact {x : F | Valued.v x = 1} := by
    refine (isCompact_integers p).of_isClosed_subset ?_ (fun x hx => by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx)
    have : {x : F | Valued.v x = 1} = {x : F | Valued.v x ≤ 1} ∩ {x : F | Valued.v x ≤ WithZero.exp (-1 : ℤ)}ᶜ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
      constructor
      · intro h; rw [h]; refine ⟨le_rfl, ?_⟩
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
      · rintro ⟨h1, h2⟩
        by_cases hx : (Valued.v x : WithZero (Multiplicative ℤ)) = 0
        · rw [hx] at h2; exact absurd h2 (not_lt.2 zero_le')
        · rw [← WithZero.exp_log hx] at h1 h2 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
          rw [WithZero.exp_lt_exp] at h2
          rw [← WithZero.exp_zero]; congr 1; omega
    rw [this]
    exact (isClosed_vball p 1).inter (isOpen_vball p _).isClosed_compl
  have himage : Units.val '' {u : Fˣ | Valued.v (u : F) = 1} = {x : F | Valued.v x = 1} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx' : Valued.v x = 1 := hx
      have hx0 : x ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hx'; exact zero_ne_one hx'
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [(Units.isEmbedding_val₀ (G₀ := HeightOneSpectrum.adicCompletion ℚ p)).isCompact_iff, himage]
  exact hS

theorem prinUnits_lt_top {M : ℤ} (hM : 1 ≤ M) :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ) {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (isCompact_units_sphere p).measure_lt_top
  intro a ha; exact v_eq_one_of_v_sub_one_le p hM ha

theorem prinUnits_pos (M : ℤ) :
    0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ) {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} :=
  (isOpen_prinUnits p M).measure_pos _ ⟨1, by simp⟩

end Setup

section Factors

theorem continuous_of_open_stabilizer (f : G → ℂ) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hU : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) : Continuous f := by
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show f (g * k) ∈ s
    rw [hU k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hUo

theorem isClosed_boxG (L Mb Mc Md : ℤ) : IsClosed {g : G | ((g : G) : M2) ∈ boxSet p L Mb Mc Md} := by
  have hc : ∀ i j : Fin 2, Continuous fun g : G => ((g : G) : M2) i j := fun i j => Units.continuous_val.matrix_elem i j
  simp only [boxSet, Set.mem_setOf_eq]
  refine ((isClosed_vball p _).preimage (hc 0 0)).inter (((isClosed_vball p _).preimage (hc 0 1)).inter
    (((isClosed_vball p _).preimage (hc 1 0)).inter ((isClosed_vball p _).preimage ((hc 1 1).sub continuous_const))))

theorem measurable_Φb_comp (L Mb Mc Md : ℤ) : Measurable fun g : G => Φb p L Mb Mc Md ((g : G) : M2) := by
  have : (fun g : G => Φb p L Mb Mc Md ((g : G) : M2)) =
      Set.indicator {g : G | ((g : G) : M2) ∈ boxSet p L Mb Mc Md} (fun _ => (1 : ℂ)) := by
    funext g
    simp only [Φb, Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]
  exact measurable_const.indicator (isClosed_boxG p L Mb Mc Md).measurableSet

theorem continuous_modulusR_det : Continuous fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ)) := by
  have : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ))) = fun g : G => ‖((g : G) : M2).det‖ := by
    funext g; rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact continuous_norm.comp Units.continuous_val.matrix_det

theorem measurable_Hfun (w : G → ℂ) (χ : Fˣ →* ℂˣ) (hχc : IsLocallyConstant χ) (L Mb Mc Md : ℤ) (s : ℂ)
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) (hU : ∀ k ∈ U, ∀ g : G, w (g * k) = w g) :
    Measurable (Hfun p w χ L Mb Mc Md s) := by
  have hw : Measurable w := (continuous_of_open_stabilizer p w U hUo hU).measurable
  have hΦ := measurable_Φb_comp p L Mb Mc Md
  have hχm : Measurable fun g : G => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp (hχc.continuous.comp Matrix.GeneralLinearGroup.continuous_det)).measurable
  have hmod : Measurable fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + 1 / 2) :=
    (Complex.measurable_ofReal.comp (continuous_modulusR_det p).measurable).pow_const _
  unfold Hfun
  exact ((hw.mul hΦ).mul hχm).mul hmod

theorem measurable_dens : Measurable fun q : F × Fˣ × Fˣ × F => modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F) := by
  have : (fun q : F × Fˣ × Fˣ × F => modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F)) =
      fun q : F × Fˣ × Fˣ × F => ‖(((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F)‖₊ := by
    funext q; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
  rw [this]
  refine (continuous_nnnorm.comp (Units.continuous_val.comp ?_)).measurable
  exact (continuous_fst.comp continuous_snd).mul ((continuous_fst.comp (continuous_snd.comp continuous_snd)).inv)

theorem integrable_f1 {Mb : ℤ} (hMb : 0 ≤ Mb) : Integrable (f1 p Mb) νa := by
  unfold f1
  exact (integrable_indicator_iff (measurableSet_vball p _)).2
    (integrableOn_const (vball_lt_top p hMb).ne)

theorem integrable_f2 {Md : ℤ} (hMd : 1 ≤ Md) : Integrable (f2 p Md) νx := by
  unfold f2
  exact (integrable_indicator_iff (measurableSet_prinUnits p _)).2
    (integrableOn_const (prinUnits_lt_top p hMd).ne)

theorem integrable_f4 {Mc : ℤ} (hMc : 0 ≤ Mc) : Integrable (f4 p Mc) νa := by
  unfold f4
  exact (integrable_indicator_iff (measurableSet_vball p _)).2
    (integrableOn_const (vball_lt_top p hMc).ne)

theorem integral_f1 (Mb : ℤ) : ∫ x, f1 p Mb x ∂νa = (((selfDualHaarAt ℚ p) {x : F | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) := by
  unfold f1
  rw [integral_indicator_const _ (measurableSet_vball p _), Complex.real_smul, mul_one]; rfl

theorem integral_f2 (Md : ℤ) : ∫ a, f2 p Md a ∂νx = ((νx {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) := by
  unfold f2
  rw [integral_indicator_const _ (measurableSet_prinUnits p _), Complex.real_smul, mul_one]; rfl

theorem integral_f4 (Mc : ℤ) : ∫ y, f4 p Mc y ∂νa = (((selfDualHaarAt ℚ p) {x : F | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ) := by
  unfold f4
  rw [integral_indicator_const _ (measurableSet_vball p _), Complex.real_smul, mul_one]; rfl

theorem f3_eq (w : G → ℂ) (χ : Fˣ →* ℂˣ) (L : ℤ) (s : ℂ)
    (hsupp : ∀ y : Fˣ, WithZero.exp L < Valued.v (y : F) → w (diagOne y) = 0) :
    f3 p w χ L s = fun a => w (diagOne a) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (s - 1 / 2) := by
  funext a
  unfold f3
  by_cases ha : Valued.v (a : F) ≤ WithZero.exp L
  · have ha' : a ∈ {a : Fˣ | Valued.v (a : F) ≤ WithZero.exp L} := ha
    rw [Set.indicator_of_mem ha']
  · have ha' : a ∉ {a : Fˣ | Valued.v (a : F) ≤ WithZero.exp L} := ha
    rw [Set.indicator_of_notMem ha', hsupp a (lt_of_not_ge ha), zero_mul, zero_mul]

end Factors

section Chart

theorem continuous_unipotentGL2' : Continuous (fun x : F => (unipotentGL2 x : G)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : F => (!![(1 : F), x; 0, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : F => (!![(1 : F), -x; 0, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_lowerUnipotentGL2' : Continuous (fun y : F => (lowerUnipotentGL2 y : G)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun y : F => (!![(1 : F), 0; y, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun y : F => (!![(1 : F), 0; -y, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_diagUnits2' : Continuous (fun ab : Fˣ × Fˣ => (diagUnits2 ab.1 ab.2 : G)) := by
  have h1 : Continuous fun ab : Fˣ × Fˣ => ((ab.1 : Fˣ) : F) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun ab : Fˣ × Fˣ => ((ab.2 : Fˣ) : F) := Units.continuous_val.comp continuous_snd
  have h1' : Continuous fun ab : Fˣ × Fˣ => (((ab.1 : Fˣ) : F))⁻¹ := h1.inv₀ (fun ab => ab.1.ne_zero)
  have h2' : Continuous fun ab : Fˣ × Fˣ => (((ab.2 : Fˣ) : F))⁻¹ := h2.inv₀ (fun ab => ab.2.ne_zero)
  have h0 : Continuous fun _ : Fˣ × Fˣ => (0 : F) := continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun ab : Fˣ × Fˣ => (!![((ab.1 : Fˣ) : F), 0; 0, ((ab.2 : Fˣ) : F)] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j
    · simpa using h1
    · simpa using h0
    · simpa using h0
    · simpa using h2
  · show Continuous fun ab : Fˣ × Fˣ => (!![(((ab.1)⁻¹ : Fˣ) : F), 0; 0, (((ab.2)⁻¹ : Fˣ) : F)] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j
    · simpa using h1'
    · simpa using h0
    · simpa using h0
    · simpa using h2'

theorem continuous_chart :
    Continuous (fun q : F × Fˣ × Fˣ × F => (unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2 : G)) := by
  refine ((continuous_unipotentGL2' p |>.comp continuous_fst).mul ?_).mul
    ((continuous_lowerUnipotentGL2' p).comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  exact (continuous_diagUnits2' p).comp
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd))

end Chart

end

end L1Box46
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart.L1Box46"

open L1Box46 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχc : IsLocallyConstant χ)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hU : ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (L Mb Mc Md : ℤ) (hL : 0 ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (hsupp : ∀ y : (p.adicCompletion ℚ)ˣ, WithZero.exp L < Valued.v (y : p.adicCompletion ℚ) → w (diagOne y) = 0)
    (hstab : ∀ (a : (p.adicCompletion ℚ)ˣ) (y : p.adicCompletion ℚ),
      Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → Valued.v y ≤ WithZero.exp (-Mc) →
        diagUnits2 1 a * lowerUnipotentGL2 y ∈ U)
    (hχ : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → χ a = 1)
    (Φ₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hΦ₀ : Φ₀ = fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        Set.indicator {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) |
            Valued.v (X 0 0) ≤ WithZero.exp L ∧ Valued.v (X 0 1) ≤ WithZero.exp (-Mb) ∧
            Valued.v (X 1 0) ≤ WithZero.exp (-Mc) ∧ Valued.v (X 1 1 - 1) ≤ WithZero.exp (-Md)} (fun _ => (1 : ℂ)) X) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ →
      μ₂ = c • Measure.map
          (fun q : (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) =>
            unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2)
          ((((selfDualHaarAt ℚ p).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p))))).withDensity fun q =>
            (modulus (((q.2.1 * (q.2.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ENNReal)) →
      (((c.toReal : ℝ) : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) *
            (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ)) ≠ 0 ∧
      ∀ s : ℂ,
        Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
          w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w g * Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
        godementZeta2 p μ₂ w Φ₀ χ (s + 1 / 2) =
          (((c.toReal : ℝ) : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) *
            (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ)) *
            ∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  intro μ₂ _ c hc0 hcT hchart
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  haveI := borelSpace_localBorel ℚ p

  have hc' : ((c.toReal : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hc0 hcT).ne'
  have hVb : ((((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos (vball_pos p Mb).ne' (vball_lt_top p hMb).ne).ne'
  have hVc : ((((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos (vball_pos p Mc).ne' (vball_lt_top p hMc).ne).ne'
  have hVd : ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos (prinUnits_pos p Md).ne' (prinUnits_lt_top p hMd).ne).ne'
  refine ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero hc' hVb) hVd) hVc, fun s hint => ?_⟩

  have hH : (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      w g * Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) =
      Hfun p w χ L Mb Mc Md s := by
    funext g; simp only [Hfun, Φb, boxSet, hΦ₀]
  have hHm := measurable_Hfun p w χ hχc L Mb Mc Md s U hUo hU
  have hΨ := (continuous_chart p).measurable
  have hf3 := f3_eq p w χ L s hsupp
  have hint3 : Integrable (f3 p w χ L s) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    rw [hf3]; exact hint
  have key : (fun q : (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) =>
      (modulus (((q.2.1 * (q.2.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ)) •
        Hfun p w χ L Mb Mc Md s (unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2)) =
      fun q => f1 p Mb q.1 * (f2 p Md q.2.1 * (f3 p w χ L s q.2.2.1 * f4 p Mc q.2.2.2)) := by
    funext q
    exact pointwise p w χ s hwlaw U hU hL hMb hMc hMd hstab hχ q.1 q.2.1 q.2.2.1 q.2.2.2
  have hprod : Integrable (fun q : (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) =>
      f1 p Mb q.1 * (f2 p Md q.2.1 * (f3 p w χ L s q.2.2.1 * f4 p Mc q.2.2.2)))
      ((selfDualHaarAt ℚ p).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p)))) :=
    (integrable_f1 p hMb).mul_prod ((integrable_f2 p hMd).mul_prod (hint3.mul_prod (integrable_f4 p hMc)))
  constructor
  ·
    rw [hH, hchart]
    refine (integrable_smul_measure hc0 hcT).2 ?_
    refine (integrable_map_measure hHm.aestronglyMeasurable hΨ.aemeasurable).2 ?_
    refine (integrable_withDensity_iff_integrable_smul (measurable_dens p)).2 ?_
    refine (integrable_congr (Filter.Eventually.of_forall fun q => ?_)).2 hprod
    exact (congrFun key q)
  ·
    simp only [godementZeta2]
    rw [hH, hchart, integral_smul_measure, integral_map hΨ.aemeasurable hHm.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul (measurable_dens p)]
    rw [show (fun q : (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) =>
        (modulus (((q.2.1 * (q.2.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ)) •
          Hfun p w χ L Mb Mc Md s (unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2)) =
        fun q => f1 p Mb q.1 * (f2 p Md q.2.1 * (f3 p w χ L s q.2.2.1 * f4 p Mc q.2.2.2)) from key]
    rw [integral_prod_mul (f1 p Mb) (fun r : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) =>
          f2 p Md r.1 * (f3 p w χ L s r.2.1 * f4 p Mc r.2.2)),
      integral_prod_mul (f2 p Md) (fun r : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) => f3 p w χ L s r.1 * f4 p Mc r.2),
      integral_prod_mul (f3 p w χ L s) (f4 p Mc)]
    rw [integral_f1, integral_f2, integral_f4, hf3, Complex.real_smul]
    ring

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart (solution)
