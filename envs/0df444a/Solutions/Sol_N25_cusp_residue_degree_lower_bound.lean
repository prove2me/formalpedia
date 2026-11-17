-- Prove2me | solution 1 for N25.cusp_residue_degree_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:54.119816+00:00
-- url     : https://prove2.me/submissions/26dbdc59-ba12-4e06-9a83-371c0b6557b0

import Mathlib
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_GammaH25_finiteIndex
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField

set_option autoImplicit false

noncomputable section

namespace N25

open Endgame AlgebraicCurve

/-- A primitive fifth root in a closed cusp residue field forces degree at least four. -/
theorem _root_.solution (P : QPlace) (ζ : P.ResidueField)
    (hζ : IsPrimitiveRoot ζ 5) : 4 ≤ P.deg := by
  let : Γ25.FiniteIndex := N25.GammaH25_finiteIndex
  obtain ⟨x,hx,hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
    Γ25 (ModularCurve.translation_mem_GammaH 25 H25)
  have : IsCurveOver ℚ FQ := isCurveOver_of_transcendental_of_perfectField hx hfd
  have : Module.Finite ℚ P.ResidueField := IsCurveOver.finiteResidue P
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic 5 ℚ :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat (by decide))).symm
  have hb := minpoly.natDegree_le (A := ℚ) ζ
  rw [hmin, Polynomial.natDegree_cyclotomic] at hb
  norm_num [Place.deg] at hb ⊢
  exact hb

end N25
