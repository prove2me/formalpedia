-- Prove2me | solution 1 for GlobalTheory.PeriodChart.exists_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:31.038569+00:00
-- url     : https://prove2.me/submissions/b5710cfc-cffd-4aeb-8897-51bd8049d41b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_anti_apply
import Theorems.Thm_P2M_GlobalTheory_PeriodChart_star_mulVec__98f0c4b56c3f
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_mulVec_left
import Theorems.Thm_GlobalTheory_PeriodChart_isHermitian_iff
import Theorems.Thm_GlobalTheory_PeriodChart_isUnit_det_of_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (G Z : Matrix (Fin g) (Fin g) ℂ) (hG : G.IsHermitian)
    (hs : ∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z)
    (hc : ∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) :
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z, z ≠ 0 → 0 < (sesq Hm z z).re) ∧
      ∀ z w, (sesq Hm (z + anti Z z) (w + anti Z w)).im = (sesq G z w).im := by
  have hH := (isHermitian_iff G).1 hG
  set N := anti Z with hN
  set M : Matrix (Fin g) (Fin g) ℂ := 1 - Z * Z.map (starRingEnd ℂ) with hM

  have hMv : ∀ u, M *ᵥ u = u - N (N u) := by
    intro u
    simp only [hM, hN, Matrix.sub_mulVec, Matrix.one_mulVec, anti_apply, star_mulVec', star_star,
      Matrix.mulVec_mulVec]

  have hsq : ∀ a b, sesq G a (N (N b)) = sesq G (N (N a)) b := by
    intro a b
    rw [hH a, hs (N b) a, hs (N a) b, hH (N b) (N a)]

  have hinj : ∀ u, M *ᵥ u = 0 → u = 0 := by
    intro u hu
    rw [hMv, sub_eq_zero] at hu
    by_contra h0
    have hNu : N u ≠ 0 := by
      intro h1
      apply h0
      rw [hu, h1, map_zero]
    have h1 := hc u h0
    have h2 := hc (N u) hNu
    rw [← hu] at h2
    linarith
  have hdet : IsUnit M.det := isUnit_det_of_ker M (fun z hz h => hz (hinj z h))
  have hMMi : ∀ x, M *ᵥ (M⁻¹ *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMiM : ∀ x, M⁻¹ *ᵥ (M *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

  have hcomm : ∀ z, M⁻¹ *ᵥ (z + N z) = M⁻¹ *ᵥ z + N (M⁻¹ *ᵥ z) := by
    intro z
    have e : z + N z = M *ᵥ (M⁻¹ *ᵥ z + N (M⁻¹ *ᵥ z)) := by
      conv_lhs => rw [← hMMi z]
      simp only [hMv, map_add, map_sub]
      abel
    rw [e, hMiM]
  have hF : ∀ x y, sesq ((M⁻¹)ᵀ * G) x y = sesq G (M⁻¹ *ᵥ x) y :=
    fun x y => (sesq_mulVec_left G M⁻¹ x y).symm
  refine ⟨(M⁻¹)ᵀ * G, ?_, ?_, ?_⟩
  · rw [isHermitian_iff]
    intro x y
    rw [hF, hF, ← hH]
    conv_lhs => rw [← hMMi y]
    conv_rhs => rw [← hMMi x]
    rw [hMv, hMv, map_sub, map_sub, LinearMap.sub_apply, hsq]
  · intro x hx
    have hu : M⁻¹ *ᵥ x ≠ 0 := by
      intro h
      apply hx
      rw [← hMMi x, h, Matrix.mulVec_zero]
    have e : sesq G (M⁻¹ *ᵥ x) x = sesq G (M⁻¹ *ᵥ x) (M *ᵥ (M⁻¹ *ᵥ x)) := by rw [hMMi]
    rw [hF, e, hMv, map_sub, hsq, hs (N (M⁻¹ *ᵥ x)) (M⁻¹ *ᵥ x), Complex.sub_re]
    have := hc _ hu
    linarith
  · intro z w
    obtain ⟨u, rfl⟩ : ∃ u, z = M *ᵥ u := ⟨M⁻¹ *ᵥ z, (hMMi z).symm⟩
    rw [hF, hcomm, hMiM, hMv]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, Complex.add_im, Complex.sub_im]
    rw [hs u w, hs (N u) w, hH (N w) u, hH (N w) (N u), Complex.conj_im, Complex.conj_im]
    ring
end GlobalTheory.PeriodChart
