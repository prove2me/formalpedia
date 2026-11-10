-- Prove2me | solution 1 for OAI.SharpPlanar.piece_damping_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:22:00.746858+00:00
-- url     : https://prove2.me/submissions/6fbba029-358a-4678-9f24-a3642d021485

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_endpoint_kernel_bounds_g
import Theorems.Thm_OAI_SharpPlanar_piece_secant_bound_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

theorem z_im (t : ℝ) : (z t).im = h * (B / (t ^ 2 + h ^ 2) - 1) := by
  simp [z, Complex.div_im, Complex.normSq, pow_two]
  ring

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma piece_damping_bound_g_oai (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    dampingCap ⟨j.val+1,by omega⟩+slopeCap j*(((j.val:ℝ)+1)/6-t) ≤ (z t).im := by
  let u : ℝ := ((j.val:ℝ)+1)/6
  have hd : 0 < t^2+h^2 := by unfold h; positivity
  have hu : 0 < u^2+h^2 := by unfold h; positivity
  have hid : ((z t).im-(z u).im)*(t^2+h^2)*(u^2+h^2) = h*B*(u-t)*(u+t) := by
    rw [z_im,z_im]
    field_simp
    ring
  have hs := mul_le_mul_of_nonneg_right (piece_secant_bound_g j ht) (sub_nonneg.mpr ht.2)
  have hm : slopeCap j*(u-t) ≤ (z t).im-(z u).im := by
    apply (mul_le_mul_iff_right₀ (mul_pos hd hu)).mp
    dsimp [u] at hid ⊢
    nlinarith only [hs,hid]
  have he := (endpoint_kernel_bounds_g ⟨j.val+1,by omega⟩).2.2
  simp only [Nat.cast_add,Nat.cast_one] at he
  change dampingCap ⟨j.val+1,by omega⟩ ≤ (z u).im at he
  dsimp [u] at hm he
  linarith only [hm,he]


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.piece_damping_bound_g_oai := @OAI.SharpPlanar.piece_damping_bound_g_oai
