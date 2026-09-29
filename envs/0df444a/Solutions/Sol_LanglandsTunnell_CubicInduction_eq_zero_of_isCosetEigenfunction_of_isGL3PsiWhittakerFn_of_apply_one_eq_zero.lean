-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f299aa0e-f3fc-5a09-861e-d2080911c334

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Theorems.Thm_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel TateLocal.addCharLevel_def"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ IsCosetEigenfunction IsRightInvariant twoRowPointLocal twoRowPointLocal_zero_right sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem level_dichotomy (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1) :
    ((∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) ∧
        ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) ∨
      ∀ n : ℤ, ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n ∧ ψv x ≠ 1 := by
  set T : Set ℤ := {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψv x = 1} with hT
  by_cases hTe : T.Nonempty
  · have hbdd : BddAbove T := by
      by_contra hnb
      apply hne
      ext x
      rw [AddChar.one_apply]
      obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x ≤ WithZero.exp n := by
        by_cases hx : Valued.v x = 0
        · exact ⟨0, by rw [hx]; exact zero_le'⟩
        · exact ⟨WithZero.log (Valued.v x), (WithZero.exp_log hx).ge⟩
      obtain ⟨m, hmT, hnm⟩ := (not_bddAbove_iff.mp hnb) n
      exact hmT x (hn.trans (WithZero.exp_le_exp.mpr hnm.le))
    have hsup : sSup T ∈ T := Int.csSup_mem hTe hbdd
    have h0 : sSup T = 0 := by
      rw [← hlev, LanglandsTunnell.TateLocal.addCharLevel_def]
    have h1 : (1 : ℤ) ∉ T := by
      intro h1
      have := le_csSup hbdd h1
      rw [h0] at this
      omega
    rw [h0] at hsup
    left
    refine ⟨fun x hx => hsup x (by simpa using hx), ?_⟩
    have hy : ∃ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (1 : ℤ) ∧ ψv y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact h1 hcon
    obtain ⟨y, hy, hy1⟩ := hy
    refine ⟨varpi v * y, ?_, ?_⟩
    · have h := mul_le_mul_right hy (Valued.v (varpi v))
      rw [Valuation.map_mul]
      refine h.trans (le_of_eq ?_)
      rw [show Valued.v (varpi v) = WithZero.exp (-1 : ℤ) from NumberField.AdelicLevel.valued_uniformizerUnit ℚ v,
        ← WithZero.exp_add]
      norm_num
    · rwa [← mul_assoc, inv_mul_cancel₀ (varpi_ne_zero v), one_mul]
  · right
    intro n
    by_contra hcon
    push Not at hcon
    exact hTe ⟨n, hcon⟩

private theorem upperUnipotent3_mem_localMaximalCompact3 (v : HeightOneSpectrum (𝓞 ℚ)) {u : v.adicCompletion ℚ}
    (hu : Valued.v u ≤ 1) :
    upperUnipotent3 u 0 0 ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hu]

private theorem diagonal_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) (t : LocalGL3 v)
    (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (hd1 : d 1 ≠ 0)
    (u : v.adicCompletion ℚ) : t * upperUnipotent3 u 0 0 = upperUnipotent3 (d 0 / d 1 * u) 0 0 * t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ht, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  field_simp

private theorem eq_zero_of_coe_eq_diagonal_of_forall_exists_ne_one (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hF2 : ∀ n : ℤ, ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n ∧ ψv x ≠ 1)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) : W t = 0 := by
  have hdet : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det t).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  rw [ht, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have hd0 : d 0 ≠ 0 := fun h => hdet (by simp [h])
  have hd1 : d 1 ≠ 0 := fun h => hdet (by simp [h])
  have hr0 : d 0 / d 1 ≠ 0 := div_ne_zero hd0 hd1
  have hvr : Valued.v (d 0 / d 1) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  obtain ⟨x, hx, hx1⟩ := hF2 (WithZero.log (Valued.v (d 0 / d 1)))
  rw [WithZero.exp_log hvr] at hx
  have hu : Valued.v (x / (d 0 / d 1)) ≤ 1 := by
    rw [Valuation.map_div, div_le_one₀ (lt_of_le_of_ne zero_le' hvr.symm)]
    exact hx
  have h1 : W t = W (t * upperUnipotent3 (x / (d 0 / d 1)) 0 0) :=
    (hU t _ (upperUnipotent3_mem_localMaximalCompact3 v hu)).symm
  have hx' : d 0 / d 1 * (x / (d 0 / d 1)) = x := by
    field_simp
  rw [diagonal_mul_upperUnipotent3 v t d ht hd1, hψ, hx', add_zero] at h1
  have h2 : (ψv x - 1) * W t = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hx1
  · exact h

private theorem ne_zero_of_coe_eq_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (t : LocalGL3 v)
    (d : Fin 3 → v.adicCompletion ℚ) (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (i : Fin 3) : d i ≠ 0 := by
  have hdet : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp t.isUnit).ne_zero
  rw [ht, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

private theorem twoRowPointLocal_eq_zero_of_apply_one_eq_zero (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (e₁ e₂ e₃ : ℂ) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (hW1 : W 1 = 0)
    (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) : W (twoRowPointLocal v k₁ k₂) = 0 := by
  have h := sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn v ψv W e₁ e₂ e₃
    ⟨hU, hT₁, hT₂, hZ⟩ hψ hψ0 hψ1
  cases k₂ with
  | zero => rw [twoRowPointLocal_zero_right, h.1 k₁, hW1, zero_mul]
  | succ j => rw [h.2 k₁ j hk, hW1, zero_mul]

private theorem eq_zero_of_coe_eq_diagonal_of_level_pair (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (e₁ e₂ e₃ : ℂ) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (hW1 : W 1 = 0)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) : W t = 0 := by
  have hd : ∀ i : Fin 3, ∃ a : ℤ, Valued.v (d i) = WithZero.exp a := fun i =>
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff Valued.v).mpr (ne_zero_of_coe_eq_diagonal v t d ht i))).symm⟩
  obtain ⟨a₀, h₀⟩ := hd 0
  obtain ⟨a₁, h₁⟩ := hd 1
  obtain ⟨a₂, h₂⟩ := hd 2
  by_cases hdrop : a₁ < a₀ ∨ a₂ < a₁
  · refine eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hU hψ hψ1 t d ht ?_
    rcases hdrop with h | h
    · exact Or.inl (by rw [h₀, h₁]; exact WithZero.exp_lt_exp.mpr h)
    · exact Or.inr (by rw [h₁, h₂]; exact WithZero.exp_lt_exp.mpr h)
  · obtain ⟨h01, h12⟩ := not_or.mp hdrop
    have h01' : a₀ ≤ a₁ := not_lt.mp h01
    have h12' : a₁ ≤ a₂ := not_lt.mp h12
    have e0 : Valued.v (d 0) = WithZero.exp (-(((a₂ - a₀).toNat : ℤ) + -a₂)) := by
      rw [h₀, WithZero.exp_inj, Int.toNat_of_nonneg (by omega)]
      omega
    have e1 : Valued.v (d 1) = WithZero.exp (-(((a₂ - a₁).toNat : ℤ) + -a₂)) := by
      rw [h₁, WithZero.exp_inj, Int.toNat_of_nonneg (by omega)]
      omega
    have e2 : Valued.v (d 2) = WithZero.exp (-(-a₂)) := by
      rw [h₂, WithZero.exp_inj]
      omega
    rw [eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant v W e₃ hU hZ t d ht _ _ _ e0 e1 e2,
      twoRowPointLocal_eq_zero_of_apply_one_eq_zero v ψv e₁ e₂ e₃ W hU hT₁ hT₂ hZ hψ hψ0 hψ1 hW1 _ _
        (Int.toNat_le_toNat (by omega)), mul_zero]

end LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero.LanglandsTunnell.CubicInduction"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (e₁ e₂ e₃ : ℂ) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1)
    (hW1 : W 1 = 0) :
    W = 0 := by
  have hdiag : ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
      (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d → W t = 0 := by
    intro t d ht
    rcases level_dichotomy v ψv hlev hne with ⟨hψ0, hψ1⟩ | hempty
    · exact eq_zero_of_coe_eq_diagonal_of_level_pair v ψv e₁ e₂ e₃ W hU hT₁ hT₂ hZ hψ hψ0 hψ1 hW1 t d ht
    · exact eq_zero_of_coe_eq_diagonal_of_forall_exists_ne_one v ψv W hU hψ hempty t d ht
  funext g
  obtain ⟨x, y, z, t, d, k, hk, ht, hg⟩ := exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 v g
  rw [Pi.zero_apply, hg, mul_assoc, hψ x y z (t * k), hU t k hk, hdiag t d ht, mul_zero]

end S_LanglandsTunnell_CubicInduction_eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero (solution)
