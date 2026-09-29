-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2e49d324-00c3-5311-8b52-ec65495e76ef

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_SphericalValues
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SphericalValues

section Valuations

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_natCast_eq_intValuation (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation (n : 𝓞 ℚ) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact AdelicLevel.valued_algebraMap (K := ℚ) v (n : 𝓞 ℚ)

private theorem absNorm_span_natCast_ratIntegers (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  have h : Ideal.absNorm (Ideal.span {((n : ℤ) : 𝓞 ℚ)}) = (n : ℤ).natAbs := by
    rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)) (n : ℤ), Algebra.norm_algebraMap,
      RingOfIntegers.rank, Module.finrank_self, pow_one]
  simpa using h

private theorem intValuation_absNorm_eq :
    v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have h1 : v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, pow_one]
    exact hmem
  have h2 : ¬ v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    intro hmem2
    have hle : Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hmem2
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_natCast_ratIntegers] at hdvd
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

private theorem valued_ratPrime : Valued.v ((ratPrimeUnit v : v.adicCompletion ℚ)) = WithZero.exp (-1 : ℤ) := by
  show Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = _
  rw [valued_natCast_eq_intValuation, intValuation_absNorm_eq]

private theorem valued_ratPrime_pow (k : ℕ) :
    Valued.v ((ratPrimeUnit v : v.adicCompletion ℚ) ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, valued_ratPrime, ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem valued_varpi_eq : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) :=
  AdelicLevel.valued_uniformizerUnit ℚ v

private theorem valued_varpi_lt_one' : Valued.v (varpi v) < 1 := by
  rw [valued_varpi_eq, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem valued_ratPrime_pow_lt {k₁ k₂ : ℕ} (h : k₁ < k₂) :
    Valued.v ((ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂) <
      Valued.v ((ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁) := by
  rw [valued_ratPrime_pow, valued_ratPrime_pow, WithZero.exp_lt_exp]
  omega

private theorem valued_ratio : Valued.v ((ratPrimeUnit v : v.adicCompletion ℚ) * (varpi v)⁻¹) = 1 := by
  rw [map_mul, map_inv₀, valued_ratPrime, valued_varpi_eq, mul_inv_cancel₀ WithZero.exp_ne_zero]

private theorem valued_ratio_inv : Valued.v (((ratPrimeUnit v : v.adicCompletion ℚ) * (varpi v)⁻¹)⁻¹) = 1 := by
  rw [map_inv₀, valued_ratio, inv_one]

private theorem cNormQ_ne_zero' : cNormQ v ≠ 0 := by
  have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  show (Ideal.absNorm v.asIdeal : ℂ) ≠ 0
  exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)

end Valuations

section Points

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_twoRowPoint (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal
        ![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoRowPointLocal, embedMat2, Units.val_pow_eq_pow_val]

private theorem coe_heckeGen2' :
    ((heckeGen2 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, 1] := rfl

private theorem coe_centralGen' :
    ((centralGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, varpi v] := rfl

private noncomputable def diagUnit (a b c : v.adicCompletion ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    LocalGL3 v where
  val := Matrix.diagonal ![a, b, c]
  inv := Matrix.diagonal ![a⁻¹, b⁻¹, c⁻¹]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [ha, hb, hc]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [ha, hb, hc]

private theorem coe_diagUnit (a b c : v.adicCompletion ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((diagUnit v a b c ha hb hc : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![a, b, c] := rfl

private theorem coe_diagUnit_inv (a b c : v.adicCompletion ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (((diagUnit v a b c ha hb hc)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![a⁻¹, b⁻¹, c⁻¹] := rfl

private theorem corner_eq :
    centralGen v * (heckeGen2 v)⁻¹ = diagUnit v 1 1 (varpi v) one_ne_zero one_ne_zero (varpi_ne_zero v) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, coe_centralGen', coe_diagUnit, coe_heckeGen2', Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem coe_point_mul_corner (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ * (centralGen v * (heckeGen2 v)⁻¹) : LocalGL3 v) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal
        ![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, varpi v] := by
  rw [corner_eq, Units.val_mul, coe_twoRowPoint, coe_diagUnit, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem ratio_ne_zero : (ratPrimeUnit v : v.adicCompletion ℚ) * (varpi v)⁻¹ ≠ 0 :=
  mul_ne_zero (ratPrimeUnit v).ne_zero (inv_ne_zero (varpi_ne_zero v))

private noncomputable def ratioUnit : LocalGL3 v :=
  diagUnit v ((ratPrimeUnit v : v.adicCompletion ℚ) * (varpi v)⁻¹)
    ((ratPrimeUnit v : v.adicCompletion ℚ) * (varpi v)⁻¹)
    1 (ratio_ne_zero v) (ratio_ne_zero v) one_ne_zero

private theorem ratioUnit_mem : ratioUnit v ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  have h₁ := valued_ratio v
  have h₂ := valued_ratio_inv v
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [ratioUnit, coe_diagUnit]
    fin_cases i <;> fin_cases j <;> simp [h₁]
  · simp only [ratioUnit, coe_diagUnit_inv]
    have h₃ : Valued.v (varpi v) * (Valued.v (ratPrimeUnit v : v.adicCompletion ℚ))⁻¹ ≤ 1 := by
      have h := h₂
      simp only [map_inv₀, map_mul, mul_inv, inv_inv] at h
      rw [mul_comm] at h
      exact h.le
    fin_cases i <;> fin_cases j <;> simp <;> exact h₃

private theorem point_succ_mul_corner (k₁ k₂ : ℕ) :
    twoRowPointLocal v (k₁ + 1) (k₂ + 1) * (centralGen v * (heckeGen2 v)⁻¹) =
      centralGen v * (twoRowPointLocal v k₁ k₂ * ratioUnit v) := by
  apply Units.ext
  rw [coe_point_mul_corner, Units.val_mul, Units.val_mul, coe_centralGen', coe_twoRowPoint, ratioUnit, coe_diagUnit,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hϖ := varpi_ne_zero v
  congr 1
  funext i
  fin_cases i <;> simp <;> field_simp <;> ring

end Points

section Values

variable (e₁ e₂ e₃ : ℂ) (q : ℂ)

private theorem value_of_lt {k₁ k₂ : ℕ} (h : k₁ < k₂) : sphericalValue e₁ e₂ e₃ q k₁ k₂ 0 = 0 :=
  sphericalValue_of_not_isDominant e₁ e₂ e₃ q _ _ _ (fun hd => by have := hd.1; omega)

private theorem value_zero_one (k₁ : ℕ) : sphericalValue e₁ e₂ e₃ q k₁ 0 1 = 0 :=
  sphericalValue_of_not_isDominant e₁ e₂ e₃ q _ _ _ (fun hd => by have := hd.2; omega)

private theorem value_zero_succ_one (j : ℕ) : sphericalValue e₁ e₂ e₃ q 0 ((j + 1 : ℕ) : ℤ) 1 = 0 :=
  sphericalValue_of_not_isDominant e₁ e₂ e₃ q _ _ _ (fun hd => by have := hd.1; omega)

private theorem value_zero_zero_zero : sphericalValue e₁ e₂ e₃ q 0 0 0 = 1 := by
  have h := sphericalValue_natCast_zero_zero e₁ e₂ e₃ q 0
  simp only [Nat.cast_zero, pow_zero, one_mul] at h
  rw [h, ← completeHom_eq, completeHom_zero]

private theorem value_succ_succ_one (i j : ℕ) :
    sphericalValue e₁ e₂ e₃ q ((i + 1 : ℕ) : ℤ) ((j + 1 : ℕ) : ℤ) 1 = e₃ * sphericalValue e₁ e₂ e₃ q i j 0 := by
  by_cases hij : j ≤ i
  · rw [sphericalValue_of_isDominant e₁ e₂ e₃ q _ _ _ ⟨by omega, by omega⟩,
      sphericalValue_of_isDominant e₁ e₂ e₃ q _ _ _ ⟨by exact_mod_cast hij, by positivity⟩]
    have h1 : (((i + 1 : ℕ) : ℤ) - 1).toNat = i := by omega
    have h2 : (((j + 1 : ℕ) : ℤ) - 1).toNat = j := by omega
    have h3 : ((i : ℤ) - 0).toNat = i := by omega
    have h4 : ((j : ℤ) - 0).toNat = j := by omega
    rw [h1, h2, h3, h4, zpow_one, zpow_zero, one_mul]
    ring
  · rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q _ _ _ (fun hd => by have := hd.1; omega),
      sphericalValue_of_not_isDominant e₁ e₂ e₃ q _ _ _ (fun hd => by have := hd.1; omega), mul_zero]

end Values

section Induction

variable {v : HeightOneSpectrum (𝓞 ℚ)} {ψv : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} {e₁ e₂ e₃ : ℂ}

private theorem point_eq_zero_of_lt (hinv : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    {k₁ k₂ : ℕ} (h : k₁ < k₂) : W (twoRowPointLocal v k₁ k₂) = 0 :=
  eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hinv hψ hψ1 _ _ (coe_twoRowPoint v k₁ k₂)
    (Or.inl (by simpa using valued_ratPrime_pow_lt v h))

private theorem corner_eq_zero_right (hinv : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (k₁ : ℕ) : W (twoRowPointLocal v k₁ 0 * (centralGen v * (heckeGen2 v)⁻¹)) = 0 :=
  eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hinv hψ hψ1 _ _ (coe_point_mul_corner v k₁ 0)
    (Or.inr (by simpa using valued_varpi_lt_one' v))

private theorem corner_eq_zero_left (hinv : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (j : ℕ) : W (twoRowPointLocal v 0 (j + 1) * (centralGen v * (heckeGen2 v)⁻¹)) = 0 :=
  eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hinv hψ hψ1 _ _
    (coe_point_mul_corner v 0 (j + 1))
    (Or.inl (by simpa using valued_ratPrime_pow_lt v (show 0 < j + 1 by omega)))

private theorem corner_value (hinv : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hcen : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (k₁ k₂ : ℕ)
    (hlow : ∀ i j : ℕ, k₁ = i + 1 → k₂ = j + 1 →
      W (twoRowPointLocal v i j) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) i j 0) :
    W (twoRowPointLocal v k₁ k₂ * (centralGen v * (heckeGen2 v)⁻¹)) =
      W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 1 := by
  cases k₂ with
  | zero => rw [corner_eq_zero_right hinv hψ hψ1, Nat.cast_zero, value_zero_one, mul_zero]
  | succ j =>
    cases k₁ with
    | zero => rw [corner_eq_zero_left hinv hψ hψ1, Nat.cast_zero, value_zero_succ_one, mul_zero]
    | succ i =>
      rw [point_succ_mul_corner, hcen, hinv _ _ (ratioUnit_mem v), hlow i j rfl rfl, value_succ_succ_one]
      ring

private theorem step_first (hq : cNormQ v ≠ 0) (he₃ : e₃ ≠ 0)
    (heig : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    {k₁ k₂ : ℕ} (hk : k₂ ≤ k₁)
    (hA : W (twoRowPointLocal v k₁ k₂) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 0)
    (hB : W (twoRowPointLocal v k₁ (k₂ + 1)) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ ((k₂ + 1 : ℕ) : ℤ) 0)
    (hC : W (twoRowPointLocal v k₁ k₂ * (centralGen v * (heckeGen2 v)⁻¹)) =
      W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 1) :
    W (twoRowPointLocal v (k₁ + 1) k₂) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((k₁ + 1 : ℕ) : ℤ) k₂ 0 := by
  obtain ⟨reps, hsys, hlaw⟩ := exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal v
  have hrel := hlaw ψv hψ0 W hψ k₁ k₂ hk
  rw [heig _ reps hsys] at hrel
  have hp : cNormQ v ^ 2 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((k₁ : ℤ) + 1) k₂ 0 +
        cNormQ v * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ ((k₂ : ℤ) + 1) 0 +
        sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 1 =
      cNormQ v * e₁ * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 0 :=
    pieri_first e₁ e₂ e₃ hq he₃ (by exact_mod_cast hk) (by positivity)
  have hq2 : cNormQ v ^ 2 ≠ 0 := pow_ne_zero 2 hq
  apply mul_left_cancel₀ hq2
  push_cast at hB ⊢
  rw [hA, hB, hC] at hrel
  linear_combination hrel.symm - W 1 * hp

private theorem step_second (hq : cNormQ v ≠ 0) (he₃ : e₃ ≠ 0)
    (heig : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    {k₁ k₂ : ℕ} (hk : k₂ ≤ k₁)
    (hA : W (twoRowPointLocal v k₁ k₂) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 0)
    (hC₁ : W (twoRowPointLocal v (k₁ + 1) k₂ * (centralGen v * (heckeGen2 v)⁻¹)) =
      W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((k₁ + 1 : ℕ) : ℤ) k₂ 1)
    (hC₂ : W (twoRowPointLocal v k₁ (k₂ + 1) * (centralGen v * (heckeGen2 v)⁻¹)) =
      W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ ((k₂ + 1 : ℕ) : ℤ) 1) :
    W (twoRowPointLocal v (k₁ + 1) (k₂ + 1)) =
      W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((k₁ + 1 : ℕ) : ℤ) ((k₂ + 1 : ℕ) : ℤ) 0 := by
  obtain ⟨reps, hsys, hlaw⟩ := exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal v
  have hrel := hlaw ψv hψ0 W hψ k₁ k₂ hk
  rw [heig _ reps hsys] at hrel
  have hp : cNormQ v ^ 2 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((k₁ : ℤ) + 1) ((k₂ : ℤ) + 1) 0 +
        cNormQ v * sphericalValue e₁ e₂ e₃ (cNormQ v) ((k₁ : ℤ) + 1) k₂ 1 +
        sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ ((k₂ : ℤ) + 1) 1 =
      cNormQ v * e₂ * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 0 :=
    pieri_second e₁ e₂ e₃ hq he₃ (by exact_mod_cast hk) (by positivity)
  have hq2 : cNormQ v ^ 2 ≠ 0 := pow_ne_zero 2 hq
  apply mul_left_cancel₀ hq2
  push_cast at hC₁ hC₂ ⊢
  rw [hA, hC₁, hC₂] at hrel
  linear_combination hrel.symm - W 1 * hp

private theorem point_eq (hq : cNormQ v ≠ 0) (he₃ : e₃ ≠ 0)
    (hinv : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (heig₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (heig₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hcen : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (k₁ k₂ : ℕ) :
    W (twoRowPointLocal v k₁ k₂) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 0 := by

  suffices h : ∀ K : ℕ, (∀ j : ℕ, W (twoRowPointLocal v K j) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) K j 0) ∧
      (∀ j : ℕ, W (twoRowPointLocal v (K + 1) j) =
        W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((K + 1 : ℕ) : ℤ) j 0) from (h k₁).1 k₂
  have hzero : ∀ j : ℕ, W (twoRowPointLocal v 0 j) =
      W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((0 : ℕ) : ℤ) j 0 := by
    intro j
    cases j with
    | zero =>
      rw [twoRowPointLocal_zero_right, iotaTorusLocal_zero, Nat.cast_zero, value_zero_zero_zero, mul_one]
    | succ j =>
      rw [point_eq_zero_of_lt hinv hψ hψ1 (show 0 < j + 1 by omega), value_of_lt _ _ _ _ (show 0 < j + 1 by omega),
        mul_zero]

  have hcorner : ∀ k₁ k₂ : ℕ,
      (∀ i j : ℕ, k₁ = i + 1 → k₂ = j + 1 →
        W (twoRowPointLocal v i j) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) i j 0) →
      W (twoRowPointLocal v k₁ k₂ * (centralGen v * (heckeGen2 v)⁻¹)) =
        W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) k₁ k₂ 1 :=
    fun k₁ k₂ hlow => corner_value hinv hcen hψ hψ1 k₁ k₂ hlow

  have hstep : ∀ K : ℕ,
      (∀ j : ℕ, W (twoRowPointLocal v K j) = W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) K j 0) →
      (∀ j : ℕ, W (twoRowPointLocal v (K + 1) j) =
        W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((K + 1 : ℕ) : ℤ) j 0) →
      ∀ j : ℕ, W (twoRowPointLocal v (K + 1 + 1) j) =
        W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((K + 1 + 1 : ℕ) : ℤ) j 0 := by
    intro K hK hK1 j
    rcases Nat.lt_or_ge (K + 1 + 1) j with hj | hj
    · rw [point_eq_zero_of_lt hinv hψ hψ1 hj, value_of_lt _ _ _ _ hj, mul_zero]
    rcases Nat.lt_or_ge j (K + 1 + 1) with hj' | hj'
    ·
      have hj1 : j ≤ K + 1 := by omega
      have hC := hcorner (K + 1) j (fun i j' hi _ => by
        have h1 : i = K := by omega
        rw [h1]
        exact hK j')
      exact step_first hq he₃ heig₁ hψ hψ0 hj1 (hK1 j) (hK1 (j + 1)) hC
    ·
      obtain rfl : j = K + 1 + 1 := by omega
      have hC₁ := hcorner (K + 1 + 1) (K + 1) (fun i j' hi hj'' => by
        have h1 : i = K + 1 := by omega
        have h2 : j' = K := by omega
        rw [h1, h2]
        exact hK1 K)
      have hC₂ := hcorner (K + 1) (K + 1 + 1) (fun i j' hi hj'' => by
        have h1 : i = K := by omega
        have h2 : j' = K + 1 := by omega
        rw [h1, h2]
        exact hK (K + 1))
      exact step_second hq he₃ heig₂ hψ hψ0 (le_refl (K + 1)) (hK1 (K + 1)) hC₁ hC₂

  have hone : ∀ j : ℕ, W (twoRowPointLocal v (0 + 1) j) =
      W 1 * sphericalValue e₁ e₂ e₃ (cNormQ v) ((0 + 1 : ℕ) : ℤ) j 0 := by
    intro j
    rcases Nat.lt_or_ge (0 + 1) j with hj | hj
    · rw [point_eq_zero_of_lt hinv hψ hψ1 hj, value_of_lt _ _ _ _ hj, mul_zero]
    rcases Nat.lt_or_ge j 1 with hj' | hj'
    · obtain rfl : j = 0 := by omega
      have hC := hcorner 0 0 (fun i j' hi _ => absurd hi (by omega))
      exact step_first hq he₃ heig₁ hψ hψ0 (le_refl 0) (hzero 0) (hzero (0 + 1)) hC
    · obtain rfl : j = 0 + 1 := by omega
      have hC₁ := hcorner (0 + 1) 0 (fun i j' _ hj'' => absurd hj'' (by omega))
      have hC₂ := hcorner 0 (0 + 1) (fun i j' hi _ => absurd hi (by omega))
      exact step_second hq he₃ heig₂ hψ hψ0 (le_refl 0) (hzero 0) hC₁ hC₂
  intro K
  induction K with
  | zero => exact ⟨hzero, hone⟩
  | succ K ih => exact ⟨ih.2, hstep K ih.1 ih.2⟩

end Induction

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) :
    (∀ n : ℕ, W (iotaTorusLocal v n) = W 1 * ((cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)) ∧
    (∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      W 1 * ((cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂))) := by
  obtain ⟨hinv, heig₁, heig₂, hcen⟩ := hW
  by_cases he₃ : e₃ = 0
  ·
    have hzero : ∀ g : LocalGL3 v, W g = 0 := fun g => by
      have h := hcen ((centralGen v)⁻¹ * g)
      rw [mul_inv_cancel_left, he₃, zero_mul] at h
      exact h
    refine ⟨fun n => ?_, fun k₁ k₂ _ => ?_⟩ <;> simp only [hzero, zero_mul]
  have hq := cNormQ_ne_zero' v
  have hpt := point_eq hq he₃ hinv heig₁ heig₂ hcen hψ hψ0 hψ1
  refine ⟨fun n => ?_, fun k₁ k₂ hk => ?_⟩
  · rw [← twoRowPointLocal_zero_right, hpt n 0, Nat.cast_zero, sphericalValue_natCast_zero_zero]
  · rw [hpt k₁ (k₂ + 1), Nat.cast_add_one, sphericalValue_natCast_succ_zero e₁ e₂ e₃ (cNormQ v) k₁ k₂ hk]

end S_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn (solution)
