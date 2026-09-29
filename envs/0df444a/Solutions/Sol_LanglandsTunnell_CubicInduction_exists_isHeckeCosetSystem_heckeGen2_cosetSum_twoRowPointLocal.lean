-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5d6414a9-be7f-579f-9ff3-d86560943baa

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeRepresentatives
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn upperUnipotent3 upperUnipotent3_coe embedMat2 localMaximalCompact3 LocalGL3 heckeGen2 centralGen cNormQ cosetSum ratPrimeUnit twoRowPointLocal"
namespace HeckeRepresentatives
p2m_export "LanglandsTunnell.CubicInduction.HeckeRepresentatives" "digit heckeGen2Reps heckeGen2RepsAt isHeckeCosetSystem_heckeGen2RepsAt"
namespace CosetSumCollapse
p2m_open "LanglandsTunnell.CubicInduction.HeckeRepresentatives LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_twoRowPointLocal (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
         0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
         0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoRowPointLocal, embedMat2, Units.val_pow_eq_pow_val]

private theorem twoRowPointLocal_mul_one_zero (a b : ℕ) :
    twoRowPointLocal v a b * twoRowPointLocal v 1 0 = twoRowPointLocal v (a + 1) b := by
  apply Units.ext
  simp only [Units.val_mul, coe_twoRowPointLocal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ]

private theorem twoRowPointLocal_mul_zero_one (a b : ℕ) :
    twoRowPointLocal v a b * twoRowPointLocal v 0 1 = twoRowPointLocal v a (b + 1) := by
  apply Units.ext
  simp only [Units.val_mul, coe_twoRowPointLocal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ]

private theorem twoRowPointLocal_mul_one_one (a b : ℕ) :
    twoRowPointLocal v a b * twoRowPointLocal v 1 1 = twoRowPointLocal v (a + 1) (b + 1) := by
  apply Units.ext
  simp only [Units.val_mul, coe_twoRowPointLocal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ]

private theorem twoRowPointLocal_mul_upperUnipotent3 (k₂ m : ℕ) (x y z : v.adicCompletion ℚ) :
    twoRowPointLocal v (k₂ + m) k₂ * upperUnipotent3 x y z =
      upperUnipotent3 (x * (ratPrimeUnit v : v.adicCompletion ℚ) ^ m)
          (y * (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂)
          (z * (ratPrimeUnit v : v.adicCompletion ℚ) ^ (k₂ + m)) * twoRowPointLocal v (k₂ + m) k₂ := by
  apply Units.ext
  simp only [Units.val_mul, coe_twoRowPointLocal, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

variable {v}

private theorem apply_upperUnipotent3_mul_eq {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1) {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) {x y : v.adicCompletion ℚ} (z : v.adicCompletion ℚ)
    (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) (g : LocalGL3 v) :
    W (upperUnipotent3 x y z * g) = W g := by
  rw [hW x y z g, hψ0 (x + y) ((Valuation.map_add _ x y).trans (max_le hx hy)), one_mul]

private theorem valued_mul_pow_le_one {x p : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (hp : Valued.v p ≤ 1)
    (n : ℕ) : Valued.v (x * p ^ n) ≤ 1 := by
  rw [Valuation.map_mul, Valuation.map_pow]
  exact mul_le_one' hx (pow_le_one' hp n)

variable (v)
variable {α : Type}

private theorem cosetSum_heckeGen2Reps [Fintype α] (dig : α → v.adicCompletion ℚ) (hdig : ∀ a, Valued.v (dig a) ≤ 1)
    (hP : Valued.v (ratPrimeUnit v : v.adicCompletion ℚ) ≤ 1)
    {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1)
    {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) {k₁ k₂ : ℕ} (hk : k₂ ≤ k₁) :
    cosetSum (heckeGen2Reps v dig) W (twoRowPointLocal v k₁ k₂) =
      (Fintype.card α : ℂ) ^ 2 * W (twoRowPointLocal v (k₁ + 1) (k₂ + 1)) +
        (Fintype.card α : ℂ) * W (twoRowPointLocal v (k₁ + 1) k₂ * (centralGen v * (heckeGen2 v)⁻¹)) +
        W (twoRowPointLocal v k₁ (k₂ + 1) * (centralGen v * (heckeGen2 v)⁻¹)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hA : ∀ bc : α × α,
      W (twoRowPointLocal v (k₂ + m) k₂ * (upperUnipotent3 0 (dig bc.2) (dig bc.1) * twoRowPointLocal v 1 1)) =
        W (twoRowPointLocal v (k₂ + m + 1) (k₂ + 1)) := by
    intro bc
    rw [← mul_assoc, twoRowPointLocal_mul_upperUnipotent3, mul_assoc, twoRowPointLocal_mul_one_one,
      apply_upperUnipotent3_mul_eq hψ0 hW _ (by rw [zero_mul, Valuation.map_zero]; exact zero_le')
        (valued_mul_pow_le_one (hdig bc.2) hP k₂)]
  have hB : ∀ a : α,
      W (twoRowPointLocal v (k₂ + m) k₂ *
          (upperUnipotent3 (dig a) 0 0 * (twoRowPointLocal v 1 0 * (centralGen v * (heckeGen2 v)⁻¹)))) =
        W (twoRowPointLocal v (k₂ + m + 1) k₂ * (centralGen v * (heckeGen2 v)⁻¹)) := by
    intro a
    rw [← mul_assoc, twoRowPointLocal_mul_upperUnipotent3, mul_assoc, ← mul_assoc (twoRowPointLocal v _ _),
      twoRowPointLocal_mul_one_zero,
      apply_upperUnipotent3_mul_eq hψ0 hW _ (valued_mul_pow_le_one (hdig a) hP m)
        (by rw [zero_mul, Valuation.map_zero]; exact zero_le')]
  have hC : twoRowPointLocal v (k₂ + m) k₂ * (twoRowPointLocal v 0 1 * (centralGen v * (heckeGen2 v)⁻¹)) =
      twoRowPointLocal v (k₂ + m) (k₂ + 1) * (centralGen v * (heckeGen2 v)⁻¹) := by
    rw [← mul_assoc, twoRowPointLocal_mul_zero_one]
  simp only [cosetSum, heckeGen2Reps, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.card_unit,
    Nat.cast_one, one_mul,
    hA, hB, hC, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
  ring

private theorem valued_natCast_le_one (n : ℕ) : Valued.v ((n : ℕ) : v.adicCompletion ℚ) ≤ 1 := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n,
    AdelicLevel.valued_algebraMap v (n : 𝓞 ℚ)]
  exact v.intValuation_le_one _

private theorem cosetSum_comp_equiv {G : Type*} [Group G] {ι κ : Type} [Fintype ι] [Fintype κ] (reps : ι → G)
    (e : κ ≃ ι) (W : G → ℂ) (g : G) : cosetSum (reps ∘ e) W g = cosetSum reps W g :=
  Fintype.sum_equiv e _ _ fun _ => rfl

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.CosetSumCollapse

end

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal.LanglandsTunnell.CubicInduction _root_.LanglandsTunnell.CubicInduction.HeckeRepresentatives _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal.LanglandsTunnell.CubicInduction.HeckeRepresentatives in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal ^ 2 + Ideal.absNorm v.asIdeal + 1) → LocalGL3 v,
      HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) reps ∧
      ∀ (ψv : AddChar (v.adicCompletion ℚ) ℂ), (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) →
        ∀ W : LocalGL3 v → ℂ, IsGL3PsiWhittakerFn ψv W →
            ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ →
              cosetSum reps W (twoRowPointLocal v k₁ k₂) =
                cNormQ v ^ 2 * W (twoRowPointLocal v (k₁ + 1) (k₂ + 1)) +
                cNormQ v * W (twoRowPointLocal v (k₁ + 1) k₂ * (centralGen v * (heckeGen2 v)⁻¹)) +
                W (twoRowPointLocal v k₁ (k₂ + 1) * (centralGen v * (heckeGen2 v)⁻¹)) := by
  refine ⟨heckeGen2RepsAt v, isHeckeCosetSystem_heckeGen2RepsAt v, fun ψv hψ0 W hW k₁ k₂ hk => ?_⟩
  have h := CosetSumCollapse.cosetSum_heckeGen2Reps v (digit v)
    (fun d => CosetSumCollapse.valued_natCast_le_one v d)
    (CosetSumCollapse.valued_natCast_le_one v (Ideal.absNorm v.asIdeal)) hψ0 hW hk
  rw [Fintype.card_fin] at h
  unfold cNormQ heckeGen2RepsAt
  rw [CosetSumCollapse.cosetSum_comp_equiv]
  exact h

#print axioms solution

end S_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal (solution)
