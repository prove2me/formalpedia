-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ef94054d-6c65-50b7-86c0-ba802cc5c62d

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel

open LanglandsTunnell.CubicInduction

namespace TorusNormalizationProof

section Furniture

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem absNorm_asIdeal_eq_natGenerator : Ideal.absNorm v.asIdeal = Rat.HeightOneSpectrum.natGenerator v := by
  rw [RatIdele.asIdeal_eq_span_natGenerator v, Ideal.absNorm_span_singleton,
    ← map_natCast (algebraMap ℤ (𝓞 ℚ)) (Rat.HeightOneSpectrum.natGenerator v), Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]

private theorem ratPrimeAt_eq_algebraMap :
    ratPrimeAt v = algebraMap ℚ (v.adicCompletion ℚ) ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) := by
  simp only [ratPrimeAt, map_natCast]

private theorem valued_ratPrimeAt : Valued.v (ratPrimeAt v) = WithZero.exp (-1 : ℤ) := by
  rw [ratPrimeAt_eq_algebraMap, RatIdele.valued_algebraMap_rat, absNorm_asIdeal_eq_natGenerator]
  exact RatIdele.valuation_natGenerator v

private theorem valued_ratPrimeAt_pow_mul_zpow (k : ℕ) (c : ℤ) :
    Valued.v (ratPrimeAt v ^ k * ratPrimeAt v ^ c) = WithZero.exp (-((k : ℤ) + c)) := by
  rw [map_mul, map_pow, map_zpow₀, valued_ratPrimeAt, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul,
    ← WithZero.exp_add, WithZero.exp_inj]
  simp only [Int.nsmul_eq_mul, Int.zsmul_eq_mul]
  ring

private theorem valued_ratPrimeAt_zpow (c : ℤ) : Valued.v (ratPrimeAt v ^ c) = WithZero.exp (-c) := by
  rw [map_zpow₀, valued_ratPrimeAt, ← WithZero.exp_zsmul, WithZero.exp_inj]
  simp only [Int.zsmul_eq_mul]
  ring

private theorem valued_div_eq_one {x y : v.adicCompletion ℚ} (hy : y ≠ 0) (h : Valued.v x = Valued.v y) :
    Valued.v (x / y) = 1 := by
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  rw [map_div₀, h, div_self hy']

private def diagGL3 (d : Fin 3 → v.adicCompletion ℚ) (hd : ∀ i, d i ≠ 0) : LocalGL3 v where
  val := Matrix.diagonal d
  inv := Matrix.diagonal fun i => (d i)⁻¹
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd i)
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd i)

@[scoped simp] private theorem coe_diagGL3 (d : Fin 3 → v.adicCompletion ℚ) (hd : ∀ i, d i ≠ 0) :
    ((diagGL3 v d hd : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d :=
  rfl

private theorem diagGL3_mem (d : Fin 3 → v.adicCompletion ℚ) (hd : ∀ i, d i ≠ 0) (hu : ∀ i, Valued.v (d i) = 1) :
    diagGL3 v d hd ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · show Valued.v (Matrix.diagonal d i j) ≤ 1
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact (hu i).le
    · rw [map_zero]
      exact zero_le
  · show Valued.v (Matrix.diagonal (fun i => (d i)⁻¹) i j) ≤ 1
    rw [Matrix.diagonal_apply]
    split_ifs
    · rw [map_inv₀, hu i, inv_one]
    · rw [map_zero]
      exact zero_le

private def scalarGL3 : (v.adicCompletion ℚ)ˣ →* LocalGL3 v :=
  Matrix.GeneralLinearGroup.scalar (Fin 3)

private theorem coe_scalarGL3 (u : (v.adicCompletion ℚ)ˣ) :
    ((scalarGL3 v u : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal fun _ => (u : v.adicCompletion ℚ) := by
  show Matrix.scalar (Fin 3) (u : v.adicCompletion ℚ) = _
  rw [Matrix.scalar_apply]

private theorem scalarGL3_eq_diagGL3 (u : (v.adicCompletion ℚ)ˣ) :
    scalarGL3 v u = diagGL3 v (fun _ => (u : v.adicCompletion ℚ)) (fun _ => u.ne_zero) :=
  Units.ext (coe_scalarGL3 v u)

private theorem scalarGL3_mul_comm (u : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    scalarGL3 v u * g = g * scalarGL3 v u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_scalarGL3]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact mul_comm _ _

private theorem scalarGL3_mem {u : (v.adicCompletion ℚ)ˣ} (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    scalarGL3 v u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [scalarGL3_eq_diagGL3]
  exact diagGL3_mem v _ _ fun _ => hu

private theorem coe_centralGen :
    ((centralGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, varpi v] :=
  rfl

private theorem centralGen_eq_scalarGL3 : centralGen v = scalarGL3 v (uniformizerUnit ℚ v) := by
  apply Units.ext
  rw [coe_centralGen, coe_scalarGL3]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem valued_uniformizerUnit_inv_mul_ratPrimeUnit :
    Valued.v (((uniformizerUnit ℚ v)⁻¹ * ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, valued_uniformizerUnit, ratPrimeUnit,
    Units.val_mk0, valued_ratPrimeAt]
  exact inv_mul_cancel₀ WithZero.exp_ne_zero

private theorem coe_twoRowPointLocal (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![ratPrimeAt v ^ k₁, 0, 0; 0, ratPrimeAt v ^ k₂, 0; 0, 0, 1] := by
  rw [twoRowPointLocal, coe_iotaGL, coe_diagUnits2, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    ratPrimeUnit, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Furniture

section Laws

variable {v : HeightOneSpectrum (𝓞 ℚ)} {W : LocalGL3 v → ℂ} {e₃ : ℂ}

private theorem apply_eq_zero_of_central_of_eq_zero (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (he : e₃ = 0) (g : LocalGL3 v) : W g = 0 := by
  rw [← mul_inv_cancel_left (centralGen v) g, hZ, he, zero_mul]

private theorem apply_scalarGL3_mul_of_valued_eq_one (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    {u : (v.adicCompletion ℚ)ˣ} (hu : Valued.v (u : v.adicCompletion ℚ) = 1) (g : LocalGL3 v) :
    W (scalarGL3 v u * g) = W g := by
  have hW' : ∀ g : LocalGL3 v, ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, W (g * k) = W g := hW
  rw [scalarGL3_mul_comm]
  exact hW' g _ (scalarGL3_mem v hu)

private theorem apply_scalarGL3_ratPrimeUnit_mul (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (g : LocalGL3 v) :
    W (scalarGL3 v (ratPrimeUnit v) * g) = e₃ * W g := by
  calc W (scalarGL3 v (ratPrimeUnit v) * g)
      = W (centralGen v * (scalarGL3 v ((uniformizerUnit ℚ v)⁻¹ * ratPrimeUnit v) * g)) := by
        rw [centralGen_eq_scalarGL3, ← mul_assoc, ← map_mul, mul_inv_cancel_left]
    _ = e₃ * W (scalarGL3 v ((uniformizerUnit ℚ v)⁻¹ * ratPrimeUnit v) * g) := hZ _
    _ = e₃ * W g := by
        rw [apply_scalarGL3_mul_of_valued_eq_one hW (valued_uniformizerUnit_inv_mul_ratPrimeUnit v)]

private theorem apply_scalarGL3_ratPrimeUnit_pow_mul (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (n : ℕ) (g : LocalGL3 v) :
    W (scalarGL3 v (ratPrimeUnit v ^ n) * g) = e₃ ^ n * W g := by
  induction n with
  | zero => simp only [pow_zero, map_one, one_mul]
  | succ n ih =>
    rw [pow_succ' (ratPrimeUnit v) n, map_mul, mul_assoc, apply_scalarGL3_ratPrimeUnit_mul hW hZ, ih,
      pow_succ' e₃ n, mul_assoc]

private theorem apply_scalarGL3_ratPrimeUnit_zpow_mul (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (he : e₃ ≠ 0) (c : ℤ) (g : LocalGL3 v) :
    W (scalarGL3 v (ratPrimeUnit v ^ c) * g) = e₃ ^ c * W g := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · rw [zpow_natCast, zpow_natCast]
    exact apply_scalarGL3_ratPrimeUnit_pow_mul hW hZ n g
  · have key : e₃ ^ n * W (scalarGL3 v (ratPrimeUnit v ^ (-(n : ℤ))) * g) = W g := by
      rw [← apply_scalarGL3_ratPrimeUnit_pow_mul hW hZ n (scalarGL3 v (ratPrimeUnit v ^ (-(n : ℤ))) * g),
        ← mul_assoc, ← map_mul, zpow_neg (ratPrimeUnit v), ← zpow_natCast (ratPrimeUnit v), mul_inv_cancel,
        map_one, one_mul]
    rw [zpow_neg e₃, zpow_natCast e₃, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero n he)]
    exact key

end Laws

end TorusNormalizationProof
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant.TorusNormalizationProof"

private theorem TorusNormalizationProof.eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (k₁ k₂ : ℕ) (c : ℤ)
    (h0 : Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)))
    (h1 : Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)))
    (h2 : Valued.v (d 2) = WithZero.exp (-c)) :
    W t = e₃ ^ c * W (twoRowPointLocal v k₁ k₂) := by
  by_cases he : e₃ = 0
  · rw [apply_eq_zero_of_central_of_eq_zero hZ he, apply_eq_zero_of_central_of_eq_zero hZ he, mul_zero]
  have hW' : ∀ g : LocalGL3 v, ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, W (g * k) = W g := hW
  have hp : ratPrimeAt v ≠ 0 := ratPrimeAt_ne_zero v
  have hpk₁ : ratPrimeAt v ^ k₁ ≠ 0 := pow_ne_zero _ hp
  have hpk₂ : ratPrimeAt v ^ k₂ ≠ 0 := pow_ne_zero _ hp
  have hpc : ratPrimeAt v ^ c ≠ 0 := zpow_ne_zero c hp
  have hu0 : Valued.v (d 0 / (ratPrimeAt v ^ k₁ * ratPrimeAt v ^ c)) = 1 :=
    valued_div_eq_one v (mul_ne_zero hpk₁ hpc) (h0.trans (valued_ratPrimeAt_pow_mul_zpow v k₁ c).symm)
  have hu1 : Valued.v (d 1 / (ratPrimeAt v ^ k₂ * ratPrimeAt v ^ c)) = 1 :=
    valued_div_eq_one v (mul_ne_zero hpk₂ hpc) (h1.trans (valued_ratPrimeAt_pow_mul_zpow v k₂ c).symm)
  have hu2 : Valued.v (d 2 / ratPrimeAt v ^ c) = 1 :=
    valued_div_eq_one v hpc (h2.trans (valued_ratPrimeAt_zpow v c).symm)
  obtain ⟨u, hu_def⟩ : ∃ u : Fin 3 → v.adicCompletion ℚ,
      u = ![d 0 / (ratPrimeAt v ^ k₁ * ratPrimeAt v ^ c), d 1 / (ratPrimeAt v ^ k₂ * ratPrimeAt v ^ c),
        d 2 / ratPrimeAt v ^ c] :=
    ⟨_, rfl⟩
  have hu : ∀ i, Valued.v (u i) = 1 := by
    intro i
    rw [hu_def]
    fin_cases i
    · exact hu0
    · exact hu1
    · exact hu2
  have hd : ∀ i, u i ≠ 0 := by
    intro i hi
    have h := hu i
    rw [hi, map_zero] at h
    exact zero_ne_one h
  have hfac : t = scalarGL3 v (ratPrimeUnit v ^ c) * twoRowPointLocal v k₁ k₂ * diagGL3 v u hd := by
    apply Units.ext
    rw [ht, Units.val_mul, Units.val_mul, coe_scalarGL3, coe_twoRowPointLocal, coe_diagGL3, hu_def,
      Units.val_zpow_eq_zpow_val, ratPrimeUnit, Units.val_mk0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal] <;> field_simp
  rw [hfac, hW' _ _ (diagGL3_mem v u hd hu), apply_scalarGL3_ratPrimeUnit_zpow_mul hW hZ he c]

open LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (k₁ k₂ : ℕ) (c : ℤ)
    (h0 : Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)))
    (h1 : Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)))
    (h2 : Valued.v (d 2) = WithZero.exp (-c)) :
    W t = e₃ ^ c * W (twoRowPointLocal v k₁ k₂) :=
  TorusNormalizationProof.eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
    v W e₃ hW hZ t d ht k₁ k₂ c h0 h1 h2

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant.TorusNormalizationProof"

end S_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant (solution)
