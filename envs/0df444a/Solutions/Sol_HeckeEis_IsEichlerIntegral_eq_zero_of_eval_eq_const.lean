-- Prove2me | solution 1 for HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f8bcd7b6-882a-529b-a52d-d65cdcdbc0ac

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Theorems.Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv
import Theorems.Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const

set_option autoImplicit false

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm IsEichlerIntegral IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv"
namespace LadderAux
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial Filter Function
open scoped MatrixGroups Manifold Topology

variable {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)}

def rung (G : ℍ → ↥(BinaryForm ℂ n)) (j : ℕ) (τ : ℍ) : ℂ :=
  MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((MvPolynomial.pderiv 1)^[j] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))

theorem rung_zero (G : ℍ → ↥(BinaryForm ℂ n)) (τ : ℍ) :
    rung G 0 τ = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) := rfl

theorem rung_succ_n (G : ℍ → ↥(BinaryForm ℂ n)) (τ : ℍ) : rung G (n + 1) τ = 0 := by
  rw [rung, MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt ((mem_homogeneousSubmodule n _).mp (G τ).2) 1
    (Nat.lt_succ_self n), map_zero]

theorem hasDerivAt_rung (hG : IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n) (τ : ℍ) :
    HasDerivAt (rung G j ∘ ofComplex)
      ((if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - rung G (j + 1) τ) (τ : ℂ) := by
  have h := hG.hasDerivAt_eval_iterate_pderiv hj τ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
  simp only [Function.comp_apply, rung]
  rw [ofComplex_apply_of_im_pos hz]

theorem mdifferentiable_rung (hG : IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (rung G j) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (hasDerivAt_rung hG hj ⟨z, hz⟩).differentiableAt.differentiableWithinAt

theorem eq_zero_of_rung_zero_const (hG : IsEichlerIntegral n g G) {c : ℂ} (hc : ∀ τ : ℍ, rung G 0 τ = c) :
    ∀ τ : ℍ, g τ = 0 := by

  have hstep : ∀ j : ℕ, j ≤ n → (∃ c : ℂ, ∀ τ : ℍ, rung G j τ = c) →
      ∀ τ : ℍ, (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - rung G (j + 1) τ = 0 := by
    rintro j hj ⟨c', hc'⟩ τ
    have h1 := hasDerivAt_rung hG hj τ
    have h2 : HasDerivAt (rung G j ∘ ofComplex) 0 (τ : ℂ) := by
      refine (hasDerivAt_const (τ : ℂ) c').congr_of_eventuallyEq ?_
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
      simp only [Function.comp_apply]
      exact hc' _
    exact h1.unique h2

  have hconst : ∀ j : ℕ, j ≤ n → ∃ c : ℂ, ∀ τ : ℍ, rung G j τ = c := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨c, hc⟩
    | succ j ih =>
      intro hj
      refine ⟨0, fun τ => ?_⟩
      have := hstep j (by omega) (ih (by omega)) τ
      rw [if_neg (by omega), zero_sub, neg_eq_zero] at this
      exact this
  intro τ
  have := hstep n le_rfl (hconst n le_rfl) τ
  rw [if_pos rfl, rung_succ_n, sub_zero] at this
  have hn : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  exact (mul_eq_zero.mp this).resolve_left hn

end HeckeEis.LadderAux

end

open scoped MatrixGroups in

theorem solution {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {c : ℂ}
    (hc : ∀ τ : UpperHalfPlane,
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = c) :
    g = 0 :=
  funext fun τ => HeckeEis.LadderAux.eq_zero_of_rung_zero_const hG hc τ

#print axioms solution

end S_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const
end P2MW
export P2MW.S_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const (solution)
