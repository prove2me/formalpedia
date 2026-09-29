-- Prove2me | solution 1 for IntermediateField.exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0175d04e-8069-58d3-af65-f27e697824d4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : ℕ) [NeZero q]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq : 0 < q := Nat.pos_of_ne_zero hq0
  obtain ⟨ζ, hζdef⟩ : ∃ z : ℂ, z = Complex.exp (2 * Real.pi * Complex.I / q) := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot ζ q := by rw [hζdef]; exact Complex.isPrimitiveRoot_exp q hq0

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ := Algebra.IsAlgebraic.of_injective k₀.val (RingHom.injective _)
  have hint : IsIntegral ℚ ξ := Algebra.IsIntegral.isIntegral ξ
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic q ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hξ hq).symm
  have hζroot : ζ ∈ (minpoly ℚ ξ).aroots ℂ := by
    rw [Polynomial.mem_aroots, hmin]
    refine ⟨Polynomial.cyclotomic_ne_zero q ℚ, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def,
      Polynomial.isRoot_cyclotomic_iff]
    exact hζ

  let φ₀ : ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) →ₐ[ℚ] ℂ :=
    (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ, hζroot⟩
  have hφ₀ : φ₀ (IntermediateField.AdjoinSimple.gen ℚ ξ) = ζ :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint ⟨ζ, hζroot⟩
  letI algF : Algebra ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) ℂ := φ₀.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) ↥k₀ :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀))
  let ι : ↥k₀ →ₐ[↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀))] ℂ := IsAlgClosed.lift
  refine ⟨ι.toRingHom, ?_⟩
  rw [← hζdef]
  have h2 : ι ξ = algebraMap ↥(IntermediateField.adjoin ℚ ({ξ} : Set ↥k₀)) ℂ (IntermediateField.AdjoinSimple.gen ℚ ξ) :=
    ι.commutes (IntermediateField.AdjoinSimple.gen ℚ ξ)
  exact h2.trans hφ₀

end S_IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot
end P2MW
export P2MW.S_IntermediateField_exists_ringHom_complex_apply_eq_exp_of_isPrimitiveRoot (solution)
