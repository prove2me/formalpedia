-- Prove2me | solution 1 for GlobalTheory.WittTransitivity.witt_transitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:07.027813+00:00
-- url     : https://prove2.me/submissions/6419f89b-5991-4792-9e8e-921e506b6a3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Theorems.Thm_GlobalTheory_WittTransitivity_hform_smul_left
import Theorems.Thm_GlobalTheory_WittTransitivity_hform_smul_right
import Theorems.Thm_GlobalTheory_WittTransitivity_conj_hform
import Theorems.Thm_GlobalTheory_WittTransitivity_exists_mem_UJ
import Theorems.Thm_GlobalTheory_WittTransitivity_exists_reflection
import Theorems.Thm_GlobalTheory_WittTransitivity_exists_norm_one

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
theorem _root_.solution (A : Type) [CommRing A] (c : A →+* A) (hc : ∀ a, c (c a) = a)
    (hf : ∀ a, c a = a → a ≠ 0 → IsUnit a) (h2 : IsUnit (2 : A)) (h3 : (3 : A) ≠ 0)
    (hθ : ∃ θ, IsUnit (θ - c θ)) (M : ℕ) (J : Matrix (Fin M) (Fin M) A)
    (hJ : ∀ i j, c (J j i) = J i j) (hdet : IsUnit J.det) (x x' : Fin M → A)
    (hx : hform c J x x = hform c J x' x') (hb : IsUnit (hform c J x x)) :
    ∃ g ∈ UJ c J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  have hxx : c (hform c J x x) = hform c J x x := conj_hform c J hc hJ x x
  obtain ⟨u, hu, hut⟩ :=
    exists_norm_one c hc hf h2 h3 hθ (hform c J x x) (hform c J x' x) hxx hb
  have hux : hform c J x x = hform c J (u • x') (u • x') := by
    rw [hform_smul_left, hform_smul_right, ← hx]
    linear_combination (-(hform c J x x)) * hu
  obtain ⟨g1, hg1, hg1x⟩ := exists_reflection c J hc hJ hdet x (u • x') hux
    (by rw [hform_smul_left]; exact hut)
  obtain ⟨g2, hg2, hg2e⟩ := exists_mem_UJ c J hdet (c u • (1 : Matrix (Fin M) (Fin M) A))
    (by
      intro y z
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hform_smul_left, hform_smul_right, hc]
      linear_combination (hform c J y z) * hu)
  refine ⟨g2 * g1, mul_mem hg2 hg1, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg1x, hg2e]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  rw [mul_comm, hu, one_smul]
end GlobalTheory.WittTransitivity
