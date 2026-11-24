-- Prove2me | solution 1 for GlobalTheory.WeightedLS.det_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:44.051861+00:00
-- url     : https://prove2.me/submissions/a2666ded-e4a5-43da-88da-35cae020d82b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory GlobalTheory.WeightedLS
open Matrix
variable {M g : ℕ}
namespace GlobalTheory.WeightedLS
theorem _root_.solution (L : Matrix (Fin M) (Fin g) ℝ) (hL : L.rank = g) (D : Fin M → ℝ)
    (hD : ∀ k, 0 < D k) : 0 < (L.transpose * Matrix.diagonal D * L).det := by
  have hinj : Function.Injective L.mulVec := by
    have h := LinearMap.finrank_range_add_finrank_ker L.mulVecLin
    have h2 : Module.finrank ℝ (LinearMap.range L.mulVecLin) = g := hL
    rw [h2, Module.finrank_fin_fun] at h
    have h3 : Module.finrank ℝ (LinearMap.ker L.mulVecLin) = 0 := by omega
    have h4 : LinearMap.ker L.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h3
    exact LinearMap.ker_eq_bot.mp h4
  have hP : (Matrix.diagonal D).PosDef := Matrix.posDef_diagonal_iff.mpr hD
  have h := hP.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_pos
end GlobalTheory.WeightedLS
