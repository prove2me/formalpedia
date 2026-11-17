-- Prove2me | solution 1 for N25.unitAnalytic25_gamma1
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:28.512029+00:00
-- url     : https://prove2.me/submissions/f44022c9-d07b-4d85-889c-da00a7d1d148

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_siegelFun_reflect_first_index
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_N25_etaAnalytic25_even_pair_gamma1

set_option autoImplicit false

namespace N25

/-- The original five unpowered Siegel ratios are Gamma1 invariant: reflection
presents their factors by even residues, whose common multipliers cancel. -/
theorem _root_.solution
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CongruenceSubgroup.Gamma1 25) (τ : UpperHalfPlane) :
    unitAnalytic25 i (A • τ) = unitAnalytic25 i τ := by
  let evenPairs : Fin 5 → ℕ × ℕ := ![(24,18),(2,14),(22,4),(6,8),(16,12)]
  let P (j : Fin 5) (z : UpperHalfPlane) : ℂ :=
    etaAnalytic25 (unitResidues25 j).1 z * etaAnalytic25 (unitResidues25 j).2 z
  have hreflect (g : ℕ) (hg : g ≤ 25) (z : UpperHalfPlane) :
      etaAnalytic25 (25-g) z = etaAnalytic25 g z := by
    let z25 : UpperHalfPlane := ⟨25*(z : ℂ), by
      simpa using (mul_pos (by norm_num : (0 : ℝ) < 25) z.im_pos)⟩
    simpa only [etaAnalytic25, Nat.cast_sub hg, Nat.cast_ofNat] using
      congrArg Neg.neg (siegelFun_reflect_first_index 25 (g : ℤ) z25)
  have hpair (j : Fin 5) (z : UpperHalfPlane) :
      P j z = etaAnalytic25 (evenPairs j).1 z * etaAnalytic25 (evenPairs j).2 z := by
    fin_cases j <;>
      simp [P, unitResidues25, evenPairs, hreflect 1 (by decide) z,
        hreflect 7 (by decide) z, hreflect 11 (by decide) z,
        hreflect 3 (by decide) z, hreflect 9 (by decide) z]
  obtain ⟨μ, hμ, hcov⟩ := etaAnalytic25_even_pair_gamma1 A hA
  have H (j : Fin 5) (z : UpperHalfPlane) : P j (A • z) = μ^2 * P j z := by
    rw [hpair j (A • z), hpair j z]
    apply hcov (evenPairs j).1 (evenPairs j).2
    · fin_cases j <;> norm_num [evenPairs]
    · fin_cases j <;> norm_num [evenPairs]
    · fin_cases j <;> norm_num [evenPairs]
  have hμne : μ ≠ 0 := by
    intro hz
    rw [hz] at hμ
    norm_num at hμ
  change P i (A • τ) / P (i+1) (A • τ) = P i τ / P (i+1) τ
  rw [H i τ, H (i+1) τ]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hμne)

end N25
