-- Prove2me | solution 1 for N25.unitAnalytic25_A13
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:26.936628+00:00
-- url     : https://prove2.me/submissions/a357e072-45ba-43ac-b8eb-db92b8a37f29

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_etaAnalytic25_pair_A13

set_option autoImplicit false

namespace N25

/-- The literal forward-label-thirteen matrix sends each original unpowered
unit to its cyclic predecessor, with its exact sign. -/
theorem _root_.solution (i : Fin 5) (τ : UpperHalfPlane) :
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
    let ε : Fin 5 → ℂ := ![-1,-1,1,-1,-1]
    unitAnalytic25 i (A • τ) = ε i * unitAnalytic25 (i-1) τ := by
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
  let σ : Fin 5 → ℂ := ![-1,1,-1,-1,1]
  let ε : Fin 5 → ℂ := ![-1,-1,1,-1,-1]
  let P (j : Fin 5) (z : UpperHalfPlane) : ℂ :=
    etaAnalytic25 (unitResidues25 j).1 z * etaAnalytic25 (unitResidues25 j).2 z
  obtain ⟨μ, hμ, hcov⟩ := etaAnalytic25_pair_A13
  have H (j : Fin 5) (z : UpperHalfPlane) :
      P j (A • z) = (μ^2 * σ j) * P (j-1) z := hcov j z
  have hμne : μ ≠ 0 := by
    intro hz
    rw [hz] at hμ
    norm_num at hμ
  have hn (k : Fin 5) : k+1 =
      ⟨(k.val+1)%5, Nat.mod_lt _ (by decide)⟩ := by
    fin_cases k <;> decide
  have hsign (j : Fin 5) : σ j / σ (j+1) = ε j := by
    rw [hn]
    fin_cases j <;> norm_num [σ, ε]
  have hidx (j : Fin 5) : (j+1)-1 = j := by fin_cases j <;> decide
  have hidx' (j : Fin 5) : (j-1)+1 = j := by fin_cases j <;> decide
  change P i (A • τ) / P (i+1) (A • τ) =
    ε i * (P (i-1) τ / P ((i-1)+1) τ)
  rw [H i τ, H (i+1) τ, hidx, hidx']
  calc
    ((μ^2 * σ i) * P (i-1) τ) / ((μ^2 * σ (i+1)) * P i τ) =
      (μ^2 * (σ i * P (i-1) τ)) / (μ^2 * (σ (i+1) * P i τ)) := by
        congr 1 <;> ring
    _ = (σ i * P (i-1) τ) / (σ (i+1) * P i τ) :=
      mul_div_mul_left _ _ (pow_ne_zero 2 hμne)
    _ = (σ i / σ (i+1)) * (P (i-1) τ / P i τ) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = ε i * (P (i-1) τ / P i τ) := by rw [hsign]

end N25
