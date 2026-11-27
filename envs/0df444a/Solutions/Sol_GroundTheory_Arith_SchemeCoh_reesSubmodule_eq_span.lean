-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.reesSubmodule_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:06.430246+00:00
-- url     : https://prove2.me/submissions/f209a037-f15e-49c0-9fe6-4c8e0d66b07b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_single_zero_mem_reesSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open Polynomial
universe u v w
variable {A : Type u} [CommRing A] (I : Ideal A)
variable (M : Type v) [AddCommGroup M] [Module A M]
variable {I M}
variable (I M)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution :
    reesSubmodule I M =
      Submodule.span (reesAlgebra I) (Set.range (PolynomialModule.single A 0 : M → _)) := by
  apply le_antisymm
  · intro p hp
    have key : ∀ n, ∀ x ∈ I ^ n • (⊤ : Submodule A M), PolynomialModule.single A n x ∈
        Submodule.span (reesAlgebra I) (Set.range (PolynomialModule.single A 0 : M → _)) := by
      intro n x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha m _
        have hmem : monomial n a ∈ reesAlgebra I := reesAlgebra.monomial_mem.2 ha
        have : PolynomialModule.single A n (a • m) =
            (⟨monomial n a, hmem⟩ : reesAlgebra I) • PolynomialModule.single A 0 m := by
          change _ = monomial n a • PolynomialModule.single A 0 m
          rw [PolynomialModule.monomial_smul_single, add_zero]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      · intro x y hx hy
        rw [PolynomialModule.single_add]
        exact add_mem hx hy
    have hp' : p = ∑ n ∈ p.coeff.support, PolynomialModule.single A n (p.coeff n) := by
      apply PolynomialModule.coeff_injective
      ext k
      rw [PolynomialModule.coeff_sum, Finsupp.finsetSum_apply]
      simp only [PolynomialModule.coeff_single, Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
      split_ifs with h
      · rfl
      · exact Finsupp.notMem_support_iff.1 h
    rw [hp']
    exact Submodule.sum_mem _ fun n _ => key n _ (hp n)
  · rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact single_zero_mem_reesSubmodule I M m
end GroundTheory.Arith.SchemeCoh
