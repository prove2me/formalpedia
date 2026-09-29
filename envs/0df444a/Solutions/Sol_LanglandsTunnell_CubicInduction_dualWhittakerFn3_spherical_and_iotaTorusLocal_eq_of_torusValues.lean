-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/48f8994e-3132-5e03-ac13-c5b4d11354ae

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus

import Theorems.Thm_LanglandsTunnell_CubicInduction_twoRowTable_contragredient_eq_inv_pow_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal NumberField.InfinitePlace LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction

noncomputable section

namespace DualTorusA

variable {A : Type*} [CommRing A]

private theorem longWeyl3_mul_longWeyl3 : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  simp [transposeInv3, _root_.mul_inv_rev, Matrix.transpose_mul]

private theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  simp [transposeInv3]

private theorem transposeInv3_upperUnipotent3 (x y z : A) :
    transposeInv3 (upperUnipotent3 x y z)
      = longWeyl3 * upperUnipotent3 (-y) (-x) (x * y - z) * longWeyl3 := by
  have htr : ((transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
      = !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
    change Matrix.transpose (((upperUnipotent3 x y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) :
      Matrix (Fin 3) (Fin 3) A) = _
    rw [show (((upperUnipotent3 x y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
        = !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] from rfl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  refine Units.ext ?_
  rw [htr, Units.val_mul, Units.val_mul, longWeyl3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private def diag3 (a b c : Aˣ) : GL (Fin 3) A where
  val := !![(a : A), 0, 0; 0, (b : A), 0; 0, 0, (c : A)]
  inv := !![((a⁻¹ : Aˣ) : A), 0, 0; 0, ((b⁻¹ : Aˣ) : A), 0; 0, 0, ((c⁻¹ : Aˣ) : A)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem diag3_coe (a b c : Aˣ) :
    ((diag3 a b c : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![(a : A), 0, 0; 0, (b : A), 0; 0, 0, (c : A)] :=
  rfl

private theorem diag3_mul (a b c a' b' c' : Aˣ) : diag3 a b c * diag3 a' b' c' = diag3 (a * a') (b * b') (c * c') := by
  refine Units.ext ?_
  rw [Units.val_mul, diag3_coe, diag3_coe, diag3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem diag3_one : diag3 (1 : Aˣ) 1 1 = 1 := by
  refine Units.ext ?_
  rw [diag3_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem diag3_pow (a b c : Aˣ) (n : ℕ) : diag3 a b c ^ n = diag3 (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero => simp only [pow_zero, diag3_one]
  | succ n ih => rw [pow_succ, ih, diag3_mul, ← pow_succ, ← pow_succ, ← pow_succ]

private theorem diag3_inv (a b c : Aˣ) : (diag3 a b c)⁻¹ = diag3 a⁻¹ b⁻¹ c⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [diag3_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, diag3_one])

private theorem transposeInv3_diag3 (a b c : Aˣ) : transposeInv3 (diag3 a b c) = diag3 a⁻¹ b⁻¹ c⁻¹ := by
  refine Units.ext ?_
  change Matrix.transpose (((diag3 a b c : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = _
  rw [show (((diag3 a b c : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
      = !![((a⁻¹ : Aˣ) : A), 0, 0; 0, ((b⁻¹ : Aˣ) : A), 0; 0, 0, ((c⁻¹ : Aˣ) : A)] from rfl, diag3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

private theorem longWeyl3_mul_diag3 (a b c : Aˣ) : longWeyl3 * diag3 a b c = diag3 c b a * longWeyl3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, longWeyl3_coe, diag3_coe, diag3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem diag3_scalar_mul_comm (a : Aˣ) (g : GL (Fin 3) A) : diag3 a a a * g = g * diag3 a a a := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, diag3_coe]
  have : (!![(a : A), 0, 0; 0, (a : A), 0; 0, 0, (a : A)] : Matrix (Fin 3) (Fin 3) A) = (a : A) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [this, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

private theorem iotaGL_diagUnitGL2_eq (x : Aˣ) : iotaGL (diagUnitGL2 x) = diag3 x 1 1 := by
  refine Units.ext ?_
  rw [coe_iotaGL, diag3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagUnitGL2]

private theorem iotaGL_diagUnits2_eq (x y : Aˣ) : iotaGL (diagUnits2 x y) = diag3 x y 1 := by
  refine Units.ext ?_
  rw [coe_iotaGL, diag3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

end DualTorusA

namespace DualTorusB
open DualTorusA

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_natCast' (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation (n : 𝓞 ℚ) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact AdelicLevel.valued_algebraMap v (n : 𝓞 ℚ)

private theorem absNorm_span_intCast' (z : ℤ) : Ideal.absNorm (Ideal.span {(z : 𝓞 ℚ)}) = z.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)) z, Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one]

private theorem absNorm_span_natCast' (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  simpa using absNorm_span_intCast' (n : ℤ)

private theorem intValuation_absNorm' :
    v.intValuation (Ideal.absNorm v.asIdeal : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have h1 : v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, pow_one]
    exact hmem
  have h2 : ¬ v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
    intro hmem2
    have hle : Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hmem2
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_natCast'] at hdvd
    have hle' := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  have hr : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-(c : ℤ)) :=
    ⟨_, v.intValuation_if_neg hr⟩
  rw [hc, WithZero.exp_le_exp] at h1 h2
  rw [hc]
  congr 1
  omega

private theorem valued_ratPrimeAt' : Valued.v (ratPrimeAt v) = Valued.v (varpi v) := by
  show Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = _
  rw [valued_natCast', intValuation_absNorm']
  exact (AdelicLevel.valued_uniformizerUnit ℚ v).symm

private def piOverP : (v.adicCompletion ℚ)ˣ := AdelicLevel.uniformizerUnit ℚ v * (ratPrimeUnit v)⁻¹

private theorem valued_piOverP : Valued.v ((piOverP v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  simp only [piOverP, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [show ((ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v from rfl, valued_ratPrimeAt']
  exact mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr (varpi_ne_zero v))

private theorem valued_piOverP_pow (n : ℕ) :
    Valued.v (((piOverP v ^ n : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
  rw [Units.val_pow_eq_pow_val, map_pow, valued_piOverP, one_pow]

private theorem valued_piOverP_pow_inv (n : ℕ) :
    Valued.v ((((piOverP v ^ n)⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, valued_piOverP_pow, inv_one]

private theorem centralGen_eq_diag3 :
    centralGen v = diag3 (AdelicLevel.uniformizerUnit ℚ v) (AdelicLevel.uniformizerUnit ℚ v)
      (AdelicLevel.uniformizerUnit ℚ v) := by
  refine Units.ext ?_
  rw [diag3_coe]
  show Matrix.diagonal ![varpi v, varpi v, varpi v] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [varpi]

private def corr (n : ℕ) : LocalGL3 v :=
  diag3 (piOverP v ^ n) (piOverP v ^ n) (piOverP v ^ n) * longWeyl3

private theorem corr_mem (n : ℕ) : corr v n ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hle : ∀ i j, Valued.v ((((diag3 (piOverP v ^ n) (piOverP v ^ n) (piOverP v ^ n) * longWeyl3 :
      LocalGL3 v)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 := by
    intro i j
    rw [Units.val_mul, diag3_coe, longWeyl3_coe]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, valued_piOverP_pow, valued_piOverP]
  have hle' : ∀ i j, Valued.v (((((diag3 (piOverP v ^ n) (piOverP v ^ n) (piOverP v ^ n) * longWeyl3 :
      LocalGL3 v))⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 := by
    intro i j
    rw [_root_.mul_inv_rev, show (longWeyl3 : LocalGL3 v)⁻¹ = longWeyl3 from
      inv_eq_of_mul_eq_one_right longWeyl3_mul_longWeyl3, Units.val_mul, longWeyl3_coe,
      show ((((diag3 (piOverP v ^ n) (piOverP v ^ n) (piOverP v ^ n) : LocalGL3 v))⁻¹ : LocalGL3 v) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
          (!![(((piOverP v ^ n)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0, 0;
            0, (((piOverP v ^ n)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0;
            0, 0, (((piOverP v ^ n)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] :
            Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
        from rfl]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, valued_piOverP_pow_inv, valued_piOverP]
  exact ⟨hle, hle'⟩

private theorem longWeyl3_mul_transposeInv3_iotaTorusLocal (n : ℕ) :
    longWeyl3 * transposeInv3 (iotaTorusLocal v n) = (centralGen v ^ n)⁻¹ * (twoRowPointLocal v n n * corr v n) := by
  rw [iotaTorusLocal, diagHom_apply, iotaGL_diagUnitGL2_eq, transposeInv3_diag3, inv_one, longWeyl3_mul_diag3]
  simp only [twoRowPointLocal, corr]
  rw [iotaGL_diagUnits2_eq, centralGen_eq_diag3, diag3_pow, diag3_inv, ← mul_assoc, ← mul_assoc, diag3_mul, diag3_mul]
  congr 1
  simp only [piOverP, mul_pow, inv_pow]
  congr 1
  · rw [eq_comm, mul_assoc, mul_left_comm (ratPrimeUnit v ^ n), mul_inv_cancel, mul_one, inv_mul_cancel]
  · rw [eq_comm, mul_assoc, mul_left_comm (ratPrimeUnit v ^ n), mul_inv_cancel, mul_one, inv_mul_cancel]
  · rw [eq_comm, mul_one, ← mul_assoc, inv_mul_cancel, one_mul]

variable {v}

private theorem apply_centralGen_pow_inv_mul (W : LocalGL3 v → ℂ) (e₃ : ℂ) (he₃ : e₃ ≠ 0)
    (hcen : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (n : ℕ) (g : LocalGL3 v) :
    W ((centralGen v ^ n)⁻¹ * g) = e₃⁻¹ ^ n * W g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ h : LocalGL3 v, W ((centralGen v)⁻¹ * h) = e₃⁻¹ * W h := fun h => by
      have := hcen ((centralGen v)⁻¹ * h)
      rw [mul_inv_cancel_left] at this
      rw [this, ← mul_assoc, inv_mul_cancel₀ he₃, one_mul]
    rw [pow_succ, _root_.mul_inv_rev, mul_assoc, h1, ih, pow_succ]
    ring

end DualTorusB

open DualTorusA DualTorusB

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (e₁ e₂ e₃ : ℂ) (he₃ : e₃ ≠ 0)
    (hcen : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (h1 : W 1 = 1)
    (htv₁ : ∀ n : ℕ, W (iotaTorusLocal v n) = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)
    (htv₂ : ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      (cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂)) :
    IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (dualWhittakerFn3 W) ∧
    IsGL3PsiWhittakerFn ψv⁻¹ (dualWhittakerFn3 W) ∧
    dualWhittakerFn3 W 1 = 1 ∧
    (∀ g : LocalGL3 v, dualWhittakerFn3 W (centralGen v * g) = e₃⁻¹ * dualWhittakerFn3 W g) ∧
    (∀ n : ℕ, dualWhittakerFn3 W (iotaTorusLocal v n) =
      (cNormQ v)⁻¹ ^ n * sphericalTorusValue (e₂ * e₃⁻¹) (e₁ * e₃⁻¹) e₃⁻¹ n) := by
  have hw3 : (longWeyl3 : LocalGL3 v) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [longWeyl3_coe]; fin_cases i <;> fin_cases j <;> simp
    · rw [show (longWeyl3 : LocalGL3 v)⁻¹ = longWeyl3 from inv_eq_of_mul_eq_one_right longWeyl3_mul_longWeyl3,
        longWeyl3_coe]
      fin_cases i <;> fin_cases j <;> simp
  have hT : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, transposeInv3 k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    intro k hk
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact hk.2 j i
    · exact hk.1 j i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g u hu
    simp only [dualWhittakerFn3_apply, transposeInv3_mul, ← mul_assoc]
    exact hK _ _ (hT u hu)
  ·
    intro x y z g
    simp only [dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_upperUnipotent3]
    rw [show (longWeyl3 : LocalGL3 v) * (longWeyl3 * upperUnipotent3 (-y) (-x) (x * y - z) * longWeyl3 * transposeInv3 g) =
      upperUnipotent3 (-y) (-x) (x * y - z) * (longWeyl3 * transposeInv3 g) by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, longWeyl3_mul_longWeyl3, one_mul, mul_assoc],
      hψ, AddChar.inv_apply', ← AddChar.map_neg_eq_inv, neg_add, add_comm]
  ·
    rw [dualWhittakerFn3_apply, transposeInv3_one, mul_one, ← one_mul (longWeyl3 : LocalGL3 v), hK 1 _ hw3, h1]
  ·
    intro g
    have hTc : transposeInv3 (centralGen v) = (centralGen v)⁻¹ := by
      rw [centralGen_eq_diag3, transposeInv3_diag3, diag3_inv]
    have hcomm : (longWeyl3 : LocalGL3 v) * (centralGen v)⁻¹ = (centralGen v)⁻¹ * longWeyl3 := by
      rw [centralGen_eq_diag3, diag3_inv, diag3_scalar_mul_comm]
    rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, ← mul_assoc, hTc, hcomm, mul_assoc]
    have := apply_centralGen_pow_inv_mul W e₃ he₃ hcen 1 (longWeyl3 * transposeInv3 g)
    rwa [pow_one, pow_one] at this
  ·
    intro n
    rw [dualWhittakerFn3_apply, longWeyl3_mul_transposeInv3_iotaTorusLocal, apply_centralGen_pow_inv_mul W e₃ he₃ hcen,
      hK _ _ (corr_mem v n)]
    classical
    let h : ℕ → ℂ := sphericalTorusValue e₁ e₂ e₃
    let hd : ℕ → ℂ := sphericalTorusValue (e₂ * e₃⁻¹) (e₁ * e₃⁻¹) e₃⁻¹
    let u : ℕ → ℕ → ℂ := fun a b => if b = 0 then h a else h a * h b - h (a + 1) * h (b - 1)
    let ud : ℕ → ℕ → ℂ := fun a b => if b = 0 then hd a else hd a * hd b - hd (a + 1) * hd (b - 1)
    have key := LanglandsTunnell.CubicInduction.twoRowTable_contragredient_eq_inv_pow_mul e₁ e₂ e₃ he₃
      h rfl rfl rfl (fun _ => rfl) hd rfl rfl rfl (fun _ => rfl)
      u (fun a => by simp [u]) (fun a b => by simp [u])
      ud (fun a => by simp [ud]) (fun a b => by simp [ud]) n 0 (Nat.zero_le n)
    have hud : ud n 0 = sphericalTorusValue (e₂ * e₃⁻¹) (e₁ * e₃⁻¹) e₃⁻¹ n := by simp [ud, hd]
    rw [hud, Nat.sub_zero] at key
    rw [key]
    cases n with
    | zero =>
      rw [show twoRowPointLocal v 0 0 = 1 by rw [twoRowPointLocal_zero_right, iotaTorusLocal_zero], h1]
      simp [u, h, sphericalTorusValue]
    | succ m =>
      rw [htv₂ (m + 1) m le_rfl]
      have hu : u (m + 1) (m + 1) = sphericalTorusValue e₁ e₂ e₃ (m + 1) * sphericalTorusValue e₁ e₂ e₃ (m + 1) -
          sphericalTorusValue e₁ e₂ e₃ (m + 1 + 1) * sphericalTorusValue e₁ e₂ e₃ m := by
        simp [u, h]
      rw [hu]
      ring

end

end S_LanglandsTunnell_CubicInduction_dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues (solution)
