-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d780d18c-01b7-5ccc-9bbd-3fe37ac6eff8

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Matrix
open scoped NNReal

noncomputable section

namespace LTFlatSection

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

abbrev kzero : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

variable {p}

theorem norm_le_one_iff (x : F) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p)

theorem norm_eq_one_iff (x : F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero p)
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p).ne'

theorem v_entry_le_one {k : G} (hk : k ∈ kzero p) (i j : Fin 2) : Valued.v ((k : Mat) i j) ≤ 1 := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk.1.integral i j)

theorem norm_entry_le_one {k : G} (hk : k ∈ kzero p) (i j : Fin 2) : ‖(k : Mat) i j‖ ≤ 1 :=
  (norm_le_one_iff _).mpr (v_entry_le_one hk i j)

theorem v_det_le_one_of_integral {m : Mat} (h : ∀ i j, Valued.v (m i j) ≤ 1) : Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
      ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
    _ ≤ 1 := by
        refine max_le ?_ ?_
        · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
        · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem v_det_eq_one {k : G} (hk : k ∈ kzero p) : Valued.v (k : Mat).det = 1 := by
  have h1 : Valued.v (k : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one hk)
  have h2 : Valued.v ((k⁻¹ : G) : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one (inv_mem hk))
  have hprod : Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det := hprod.symm
    _ ≤ Valued.v (k : Mat).det * 1 := by gcongr
    _ = Valued.v (k : Mat).det := mul_one _

theorem norm_det_eq_one {k : G} (hk : k ∈ kzero p) : ‖(k : Mat).det‖ = 1 :=
  (norm_eq_one_iff _).mpr (v_det_eq_one hk)

variable (p) in

def rowSup (g : G) : ℝ := max ‖(g : Mat) 1 0‖ ‖(g : Mat) 1 1‖

variable (p) in

def height (g : G) : ℝ := ‖(g : Mat).det‖ / rowSup p g ^ 2

theorem rowSup_pos (g : G) : 0 < rowSup p g := by
  unfold rowSup
  by_contra h
  rw [not_lt] at h
  have h0 : ‖(g : Mat) 1 0‖ ≤ 0 := (le_max_left _ _).trans h
  have h1 : ‖(g : Mat) 1 1‖ ≤ 0 := (le_max_right _ _).trans h
  have e0 : (g : Mat) 1 0 = 0 := norm_le_zero_iff.mp h0
  have e1 : (g : Mat) 1 1 = 0 := norm_le_zero_iff.mp h1
  have hdet : (g : Mat).det = 0 := by rw [Matrix.det_fin_two, e0, e1]; ring
  exact (Matrix.GeneralLinearGroup.det g).ne_zero (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet)

theorem det_ne_zero (g : G) : (g : Mat).det ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det g).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h

theorem height_pos (g : G) : 0 < height p g :=
  div_pos (norm_pos_iff.mpr (det_ne_zero g)) (pow_pos (rowSup_pos g) 2)

theorem rowSup_mul_le {k : G} (hk : k ∈ kzero p) (g : G) : rowSup p (g * k) ≤ rowSup p g := by
  have hent : ∀ j : Fin 2, ‖((g * k : G) : Mat) 1 j‖ ≤ rowSup p g := by
    intro j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    calc ‖(g : Mat) 1 0 * (k : Mat) 0 j + (g : Mat) 1 1 * (k : Mat) 1 j‖
        ≤ max ‖(g : Mat) 1 0 * (k : Mat) 0 j‖ ‖(g : Mat) 1 1 * (k : Mat) 1 j‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max ‖(g : Mat) 1 0‖ ‖(g : Mat) 1 1‖ := by
          rw [norm_mul, norm_mul]
          exact max_le_max (mul_le_of_le_one_right (norm_nonneg _) (norm_entry_le_one hk 0 j))
            (mul_le_of_le_one_right (norm_nonneg _) (norm_entry_le_one hk 1 j))
  exact max_le (hent 0) (hent 1)

theorem rowSup_mul {k : G} (hk : k ∈ kzero p) (g : G) : rowSup p (g * k) = rowSup p g := by
  refine le_antisymm (rowSup_mul_le hk g) ?_
  have := rowSup_mul_le (inv_mem hk) (g * k)
  rwa [mul_inv_cancel_right] at this

theorem height_mul {k : G} (hk : k ∈ kzero p) (g : G) : height p (g * k) = height p g := by
  rw [height, height, rowSup_mul hk, Units.val_mul, Matrix.det_mul, norm_mul, norm_det_eq_one hk, mul_one]

theorem rowSup_one : rowSup p (1 : G) = 1 := by
  simp [rowSup]

theorem height_one : height p (1 : G) = 1 := by
  rw [height, rowSup_one, Units.val_one, Matrix.det_one, norm_one]; norm_num

theorem height_of_mem {k : G} (hk : k ∈ kzero p) : height p k = 1 := by
  rw [← one_mul k, height_mul hk, height_one]

theorem height_upperUnipotent2_mul (x : F) (g : G) : height p (upperUnipotent2 p x * g) = height p g := by
  have h10 := gl2Entry_upperUnipotent2_mul_one p x g 0
  have h11 := gl2Entry_upperUnipotent2_mul_one p x g 1
  have hdet := gl2Det_upperUnipotent2_mul p x g
  simp only [gl2Entry, gl2Det] at h10 h11 hdet
  rw [height, height, rowSup, rowSup, h10, h11, hdet]

theorem height_diagonal2_mul (a : Fin 2 → Fˣ) (g : G) :
    height p (diagonal2 p a * g) = ‖(a 0 : F)‖ / ‖(a 1 : F)‖ * height p g := by
  have h10 := gl2Entry_diagonal2_mul p a g 1 0
  have h11 := gl2Entry_diagonal2_mul p a g 1 1
  have hdet := gl2Det_diagonal2_mul p a g
  simp only [gl2Entry, gl2Det] at h10 h11 hdet
  have hr : rowSup p (diagonal2 p a * g) = ‖(a 1 : F)‖ * rowSup p g := by
    rw [rowSup, rowSup, h10, h11, norm_mul, norm_mul, mul_max_of_nonneg _ _ (norm_nonneg _)]
  rw [height, height, hr, hdet, norm_mul, norm_mul]
  have h1 : ‖(a 1 : F)‖ ≠ 0 := norm_ne_zero_iff.mpr (a 1).ne_zero
  have hm : rowSup p g ≠ 0 := (rowSup_pos g).ne'
  field_simp

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ HeightOneSpectrum.adicCompletionIntegers ℚ p) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem coe_kzero_eq_localIntegralSet : ((kzero p : Subgroup G) : Set G) = AutomorphicForm.localIntegralSet ℚ p := by
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff, AutomorphicForm.mem_localIntegralSet]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩; exact ⟨isLocalLevelOne_top_of_integral h1, isLocalLevelOne_top_of_integral h2⟩

theorem isOpen_kzero : IsOpen ((kzero p : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact AutomorphicForm.isOpen_localIntegralSet ℚ p

theorem isLocallyConstant_height : IsLocallyConstant (height p) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun x => ?_
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' ((kzero p : Subgroup G) : Set G),
    (isOpen_kzero).preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
  have := height_mul hy x
  rwa [mul_inv_cancel_left] at this

theorem cpow_mul_ofReal_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℂ) :
    (((a * b : ℝ) : ℂ)) ^ u = ((a : ℂ)) ^ u * ((b : ℂ)) ^ u := by
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg ha.le hb.le u

theorem cpow_div_ofReal_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℂ) :
    (((a / b : ℝ) : ℂ)) ^ u = ((a : ℂ)) ^ u * ((b : ℂ)) ^ (-u) := by
  rw [div_eq_mul_inv, cpow_mul_ofReal_pos ha (inv_pos.mpr hb), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hb.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg]

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem flat_mem (χ χ' : Fin 2 → (Fˣ →* ℂˣ)) (u : ℂ)
    (hχ'₀ : ∀ a : Fˣ, ((χ' 0 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ) * (((modulus (a : F) : ℝ) : ℂ) ^ u))
    (hχ'₁ : ∀ a : Fˣ, ((χ' 1 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ) * (((modulus (a : F) : ℝ) : ℂ) ^ (-u)))
    {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) :
    (fun g : G => f g * ((height p g : ℝ) : ℂ) ^ u) ∈ principalSeries2 p χ' := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  refine mem_principalSeries2_iff.mpr ⟨?_, fun x g => ?_, fun a g => ?_⟩
  · exact hlc.mul (isLocallyConstant_height.comp fun r : ℝ => ((r : ℝ) : ℂ) ^ u)
  · simp only [hn, height_upperUnipotent2_mul]
  · simp only [ht, height_diagonal2_mul]
    have h0 : 0 < ‖(a 0 : F)‖ := norm_pos_iff.mpr (a 0).ne_zero
    have h1 : 0 < ‖(a 1 : F)‖ := norm_pos_iff.mpr (a 1).ne_zero
    rw [cpow_mul_ofReal_pos (div_pos h0 h1) (height_pos g), cpow_div_ofReal_pos h0 h1]
    have hχ : torusChar2 p χ' a = torusChar2 p χ a * (((‖(a 0 : F)‖ : ℝ) : ℂ) ^ u * ((‖(a 1 : F)‖ : ℝ) : ℂ) ^ (-u)) := by
      simp only [torusChar2, Fin.prod_univ_two, hχ'₀, hχ'₁, coe_modulus_eq_norm]
      ring
    rw [hχ]
    ring

end LTFlatSection

end

open LTFlatSection in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ χ' : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (u : ℂ)
    (hχ'₀ : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χ' 0 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ u))
    (hχ'₁ : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χ' 1 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-u)))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ) :

    (fun g : GL (Fin 2) (p.adicCompletion ℚ) => f g *
        (((‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ) ^ u)) ∈
        principalSeries2 p χ' ∧

    (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ‖((upperUnipotent2 p x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖((upperUnipotent2 p x * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖((upperUnipotent2 p x * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 =
          ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2) ∧

    (∀ (a : Fin 2 → (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ‖((diagonal2 p a * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖((diagonal2 p a * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖((diagonal2 p a * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 =
          ‖(a 0 : p.adicCompletion ℚ)‖ / ‖(a 1 : p.adicCompletion ℚ)‖ *
            (‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
              max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
                ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2)) ∧

    (∀ (g k : GL (Fin 2) (p.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
        ‖((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 =
          ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2) ∧

    (∀ k : GL (Fin 2) (p.adicCompletion ℚ), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
        ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 = 1) ∧

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        0 < ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2) := by
  exact ⟨flat_mem χ χ' u hχ'₀ hχ'₁ hf, fun x g => height_upperUnipotent2_mul x g, fun a g => height_diagonal2_mul a g,
    fun g k hk => height_mul hk g, fun k hk => height_of_mem hk, fun g => height_pos g⟩

end S_LanglandsTunnell_CubicInduction_flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq (solution)
