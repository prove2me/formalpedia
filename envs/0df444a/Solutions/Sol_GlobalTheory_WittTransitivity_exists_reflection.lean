-- Prove2me | solution 1 for GlobalTheory.WittTransitivity.exists_reflection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:12.971032+00:00
-- url     : https://prove2.me/submissions/0c55db26-39fb-4e9a-bf06-7cab23cbb29f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Theorems.Thm_GlobalTheory_WittTransitivity_hform_sub_left
import Theorems.Thm_GlobalTheory_WittTransitivity_hform_sub_right
import Theorems.Thm_GlobalTheory_WittTransitivity_hform_smul_left
import Theorems.Thm_GlobalTheory_WittTransitivity_hform_smul_right
import Theorems.Thm_GlobalTheory_WittTransitivity_conj_hform
import Theorems.Thm_GlobalTheory_WittTransitivity_hform_eq_sum
import Theorems.Thm_GlobalTheory_WittTransitivity_exists_mem_UJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Formalism.UG
open GlobalTheory GlobalTheory.WittTransitivity
variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
namespace GlobalTheory.WittTransitivity
theorem _root_.solution (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (hdet : IsUnit J.det) (x x' : Fin M → A) (hx : hform c J x x = hform c J x' x')
    (hs : IsUnit (hform c J x x - hform c J x' x)) :
    ∃ g ∈ UJ c J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  set s := hform c J x x - hform c J x' x with hs_def
  obtain ⟨su, hsu⟩ := hs
  set b : A := ↑su⁻¹ with hb_def
  have hbs : b * s = 1 := by rw [hb_def, ← hsu, Units.inv_mul]
  have hcb : c b * c s = 1 := by rw [← map_mul, hbs, map_one]
  set v := x - x' with hv
  have hvv : hform c J v v = s + c s := by
    have hxx : c (hform c J x x) = hform c J x x := conj_hform c J hc hJ x x
    have e1 : c s = hform c J x x - hform c J x x' := by
      rw [hs_def, map_sub, hxx, conj_hform c J hc hJ]
    rw [hv, hform_sub_left, hform_sub_right, hform_sub_right, e1, hs_def, ← hx]
    ring
  set g : Matrix (Fin M) (Fin M) A :=
    1 - Matrix.of (fun k j => b * v k * hform c J v (Pi.single j 1)) with hg_def
  have hgy : ∀ y, g *ᵥ y = y - (b * hform c J v y) • v := by
    intro y
    rw [hform_eq_sum c J v y]
    ext k
    rw [hg_def, Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.of_apply]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpres : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z := by
    intro y z
    rw [hgy, hgy, hform_sub_left, hform_sub_right, hform_sub_right, hform_smul_left,
      hform_smul_left, hform_smul_right, hform_smul_right, map_mul,
      conj_hform c J hc hJ v y, hvv]
    linear_combination (hform c J y v * hform c J v z * c b) * hbs +
      (hform c J y v * hform c J v z * b) * hcb
  obtain ⟨G, hG, hGg⟩ := exists_mem_UJ c J hdet g hpres
  refine ⟨G, hG, ?_⟩
  have hvx : hform c J v x = s := by rw [hv, hform_sub_left, hs_def]
  rw [hGg, hgy, hvx, hbs, one_smul, hv, sub_sub_cancel]
end GlobalTheory.WittTransitivity
