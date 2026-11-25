-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.shift_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:10.919563+00:00
-- url     : https://prove2.me/submissions/4d3d02aa-b54d-4812-95f2-a88926fb3be7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HermitianTensorPowers_herm_add_left
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HermitianTensorPowers_herm_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (k : ℕ) (c : ℂ)
    (v l : Fin g → ℂ) (a : ℤ) (ha : k * (herm Hm v l).im = a) (θ : (Fin g → ℂ) → ℂ)
    (hθ : ∀ z, θ (z + l) = factor Hm c l z ^ k * θ z) (z : Fin g → ℂ) :
    shift Hm k v θ (z + l) = factor Hm c l z ^ k * shift Hm k v θ z := by
  have h1 : herm Hm v l - herm Hm l v = 2 * ((herm Hm v l).im : ℂ) * Complex.I := by
    rw [herm_swap h v l, Complex.sub_conj]; push_cast; ring
  have ha' : (k : ℂ) * ((herm Hm v l).im : ℂ) = a := by exact_mod_cast ha
  have h2 : Complex.exp (a * (2 * Real.pi * Complex.I)) = 1 := Complex.exp_int_mul_two_pi_mul_I a
  simp only [shift, factor, add_right_comm z l v, hθ, herm_add_left, mul_pow, ← Complex.exp_nat_mul]
  have h3 : Complex.exp (-(k * Real.pi * (herm Hm z v + herm Hm l v))) *
      Complex.exp (k * (Real.pi * (herm Hm z l + herm Hm v l) + Real.pi / 2 * herm Hm l l)) =
      Complex.exp (k * (Real.pi * herm Hm z l + Real.pi / 2 * herm Hm l l)) *
      Complex.exp (-(k * Real.pi * herm Hm z v)) := by
    rw [← mul_one (Complex.exp _ * Complex.exp (-(k * Real.pi * herm Hm z v))), ← h2]
    simp only [← Complex.exp_add]
    congr 1
    linear_combination ((k : ℂ) * Real.pi) * h1 + (2 * Real.pi * Complex.I) * ha'
  linear_combination (c ^ k * θ (z + v)) * h3
end GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
