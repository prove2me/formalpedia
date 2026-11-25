-- Prove2me | solution 1 for GlobalTheory.AppellHumbert.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:25:48.086819+00:00
-- url     : https://prove2.me/submissions/05205e9e-a4eb-4ef8-b387-aa9cf3e36aa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertNormalFormOfLinearExponent
import Theorems.Thm_GlobalTheory_AppellHumbert_eq_sum_re_im
import Theorems.Thm_GlobalTheory_AppellHumbert_apply_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AppellHumbert
namespace GlobalTheory.AppellHumbert
theorem _root_.solution {g : ℕ} (F : (Fin g → ℂ) →ₗ[ℝ] ((Fin g → ℂ) →ₗ[ℂ] ℂ)) :
    ∃ S H : Matrix (Fin g) (Fin g) ℂ, ∀ u z,
      F u z = z ⬝ᵥ S.mulVec u + z ⬝ᵥ H.mulVec (star u) := by
  refine ⟨Matrix.of fun a b => (F (Pi.single b 1) (Pi.single a 1)
      - I * F (Pi.single b I) (Pi.single a 1)) / 2,
    Matrix.of fun a b => (F (Pi.single b 1) (Pi.single a 1)
      + I * F (Pi.single b I) (Pi.single a 1)) / 2, fun u z => ?_⟩
  rw [apply_eq_sum, ← dotProduct_add, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  conv_lhs => rw [eq_sum_re_im u]
  simp only [map_sum, map_add, map_smul, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Pi.add_apply, mulVec, dotProduct, of_apply, ← Finset.sum_add_distrib,
    Pi.star_apply, real_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : u b = (u b).re + (u b).im * I := (re_add_im _).symm
  have h2 : star (u b) = (u b).re - (u b).im * I := by
    apply Complex.ext <;> simp
  rw [h2]
  generalize (u b).re = x at *
  generalize (u b).im = y at *
  rw [h1]
  linear_combination (y * F (Pi.single b I) (Pi.single a 1)) * I_mul_I
end GlobalTheory.AppellHumbert
