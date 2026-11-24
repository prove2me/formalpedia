-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:53.634799+00:00
-- url     : https://prove2.me/submissions/f54eed17-22f5-4a06-9499-56e3affc294d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_eq_coord
import Theorems.Thm_GlobalTheory_QuadraticZeta_discr_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (h2 : finrank ℚ K = 2) :
    ∃ (b : Basis (Fin 2) ℤ (𝓞 K)) (t n : ℤ), b 0 = 1 ∧ b 1 ^ 2 = t * b 1 - n ∧
      discr K = t ^ 2 - 4 * n := by
  let e : Basis (Fin 2) ℤ (𝓞 K) := finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans h2)
  have h1 : (1 : 𝓞 K) = e.repr 1 0 • e 0 + e.repr 1 1 • e 1 := by
    conv_lhs => rw [← e.sum_repr 1]
    simp
  generalize e.repr 1 0 = x, e.repr 1 1 = y at h1
  have hc : IsCoprime x y := by
    refine isCoprime_of_dvd x y (fun h => by simp [h.1, h.2] at h1) ?_
    rintro z hz - ⟨x', rfl⟩ ⟨y', rfl⟩
    apply hz
    have hu : IsUnit (algebraMap ℤ (𝓞 K) z) :=
      IsUnit.of_mul_eq_one (x' • e 0 + y' • e 1) (by rw [h1]; simp; ring)
    have := hu.map (Algebra.norm ℤ)
    rw [Algebra.norm_algebraMap_of_basis e] at this
    exact (isUnit_pow_iff (by simp)).1 this
  obtain ⟨u, v, huv⟩ := hc
  have hd : IsUnit (e.det ![x • e 0 + y • e 1, -v • e 0 + u • e 1]) := by
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp only [Basis.toMatrix_apply]
    simp [-zsmul_eq_mul]
    convert isUnit_one using 1
    linarith
  obtain ⟨hi, hs⟩ := (e.is_basis_iff_det).2 hd
  let b : Basis (Fin 2) ℤ (𝓞 K) := Basis.mk hi hs.ge
  have h0 : b 0 = 1 := by simp [b, h1.symm, -zsmul_eq_mul]
  have hw : b 1 ^ 2 = (b.repr (b 1 ^ 2) 1 : ℤ) * b 1 - (-b.repr (b 1 ^ 2) 0 : ℤ) := by
    conv_lhs => rw [eq_coord b h0 (b 1 ^ 2)]
    push_cast
    ring
  exact ⟨b, _, _, h0, hw, by rw [← discr_eq_discr K b, discr_eq b h0 hw]⟩
end GlobalTheory.QuadraticZeta
