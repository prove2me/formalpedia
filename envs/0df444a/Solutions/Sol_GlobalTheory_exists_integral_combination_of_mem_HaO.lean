-- Prove2me | solution 1 for GlobalTheory.exists_integral_combination_of_mem_HaO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:21.867059+00:00
-- url     : https://prove2.me/submissions/beb0274d-d2b9-4b6f-a8d9-8808417eaa34

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralBasisLinearCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemHHaOfCoeffFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Theorems.Thm_GlobalTheory_CoeffFunctional_mem_HHa_of_coeff_functional
import Theorems.Thm_GlobalTheory_exists_integral_basis_linear_coordinates


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] (e : K →+* C) (R : Subring C), (∀ x : V, e (algebraMap V K x) ∈ R) → ∀ (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C), P ∈ HaO r n C R cc isX a → ∃ (s : ℕ) (c : Fin s → C) (Q : Fin s → MvPolynomial (Letter T r n) K), (∀ j, c j ∈ R) ∧ (∀ j, Q j ∈ HaO r n K (algebraMap V K).range cc isX a) ∧ P = ∑ j, MvPolynomial.C (c j) * MvPolynomial.map e (Q j) := by
  intro T r n V K C _ _ _ _ _ _ _ e R hR cc isX a P hP
  classical
  let _ : Algebra K C := e.toAlgebra
  obtain ⟨hH, hO⟩ := hP
  obtain ⟨s, c, φ, hc, hφ⟩ := GlobalTheory.exists_integral_basis_linear_coordinates V K C R hR (P.support.image fun μ => P.coeff μ) (by
    intro x hx
    obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
    exact hO μ)
  let Q : Fin s → MvPolynomial (Letter T r n) K := fun j =>
    ∑ μ ∈ P.support, MvPolynomial.monomial μ (φ j (P.coeff μ))
  have hQ : ∀ j μ, (Q j).coeff μ = φ j (P.coeff μ) := by
    intro j μ
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
  refine ⟨s, c, Q, hc, fun j => ⟨GlobalTheory.CoeffFunctional.mem_HHa_of_coeff_functional T r n K C (φ j) cc isX a P (Q j) (hQ j) hH, ?_⟩, ?_⟩
  · intro μ
    rw [hQ]
    by_cases h : μ ∈ P.support
    · exact (hφ _ (Finset.mem_image_of_mem _ h)).1 j
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
      exact zero_mem _
  · ext μ
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hQ]
    by_cases h : μ ∈ P.support
    · refine (hφ _ (Finset.mem_image_of_mem _ h)).2.trans ?_
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · rw [MvPolynomial.notMem_support_iff.mp h]
      simp
end GlobalTheory
