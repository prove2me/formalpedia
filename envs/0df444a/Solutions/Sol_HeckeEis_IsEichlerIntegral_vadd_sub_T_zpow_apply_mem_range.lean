-- Prove2me | solution 1 for HeckeEis.IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4e512fb3-ad49-5597-a7ce-07d88c6caa5d

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

import Theorems.Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm
import Theorems.Thm_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty
import Theorems.Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range

set_option autoImplicit false

open scoped Manifold MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binaryFormRepSL binaryFormRepSL_apply_coe linePow coe_linePow IsEichlerIntegral coeff_single_one_eq_eval_of_mem_binaryForm mem_range_binaryFormRepSL_T_zpow_sub_one"
namespace CuspInftySol
p2m_open "HeckeEis"

p2m_open "UpperHalfPlane MvPolynomial HeckeEis P2MW.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.HeckeEis"
open scoped Manifold MatrixGroups

theorem eval_binarySubst_T_zpow (h : ℤ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![0, 1] (binarySubst ℂ ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P)
      = MvPolynomial.eval ![0, 1] P := by
  have key : (fun j : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℂ) (![0, 1] : Fin 2 → ℂ)
      (∑ i : Fin 2, C ((((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) * X i))
      = (![0, 1] : Fin 2 → ℂ) := by
    funext j
    fin_cases j <;> simp [ModularGroup.coe_T_zpow, Fin.sum_univ_two]
  rw [binarySubst, MvPolynomial.aeval_eq_bind₁, MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁, key]

theorem coeff_single_one_binaryFormRepSL_T_zpow (n : ℕ) (h : ℤ) (P : ↥(BinaryForm ℂ n)) :
    MvPolynomial.coeff (Finsupp.single 1 n)
        ((binaryFormRepSL ℂ n (ModularGroup.T ^ h) P : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) ℂ) := by
  rw [coeff_single_one_eq_eval_of_mem_binaryForm (binaryFormRepSL ℂ n _ P).2,
    coeff_single_one_eq_eval_of_mem_binaryForm P.2, binaryFormRepSL_apply_coe, eval_binarySubst_T_zpow]

theorem coeff_single_one_linePow (n : ℕ) (z : ℂ) :
    MvPolynomial.coeff (Finsupp.single 1 n) ((linePow n z : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = 1 := by
  rw [coeff_single_one_eq_eval_of_mem_binaryForm (linePow n z).2, coe_linePow]
  simp

end HeckeEis.CuspInftySol

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.HeckeEis HeckeEis.CuspInftySol UpperHalfPlane MvPolynomial in
theorem solution {n : ℕ} {h : ℤ} (hh : h ≠ 0)
    {g : UpperHalfPlane → ℂ} {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : UpperHalfPlane.IsZeroAtImInfty g) (τ : UpperHalfPlane) :
    G ((h : ℝ) +ᵥ τ) - HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)
      ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) - 1) := by
  apply mem_range_binaryFormRepSL_T_zpow_sub_one n hh
  rw [Submodule.coe_sub, coeff_sub, coeff_single_one_binaryFormRepSL_T_zpow, sub_eq_zero]
  set φ : ℂ → ℂ := fun z =>
    MvPolynomial.coeff (Finsupp.single 1 n) ((G (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) with hφdef
  have hφ : ∀ σ : ℍ, HasDerivAt φ (g σ) ↑σ := fun σ => by
    have := hG (Finsupp.single 1 n) σ
    rw [coeff_single_one_linePow, mul_one] at this
    exact this
  suffices hs : φ ((((h : ℝ) +ᵥ τ : ℍ) : ℂ)) = φ (τ : ℂ) by
    simpa only [hφdef, ofComplex_apply] using hs
  rw [coe_vadd, add_comm]
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · have hper' : Function.Periodic (g ∘ ofComplex) (((-h : ℤ) : ℝ) : ℂ) := by
      push_cast
      exact hper.neg
    have key := UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty (h := ((-h : ℤ) : ℝ))
      (by exact_mod_cast (neg_pos.mpr hneg)) hper' hhol hzero hφ ((h : ℝ) +ᵥ τ)
    rw [coe_vadd] at key
    push_cast at key ⊢
    have e : (h : ℂ) + (τ : ℂ) + -(h : ℂ) = (τ : ℂ) := by ring
    rw [e] at key
    rw [add_comm]
    exact key.symm
  · have key := UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty (h := ((h : ℤ) : ℝ))
      (by exact_mod_cast hpos) hper hhol hzero hφ τ
    push_cast at key ⊢
    exact key

end

end S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range
end P2MW
export P2MW.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range (solution)
