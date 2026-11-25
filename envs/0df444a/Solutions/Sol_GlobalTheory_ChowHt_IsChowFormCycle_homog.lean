-- Prove2me | solution 1 for GlobalTheory.ChowHt.IsChowFormCycle.homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:25.656473+00:00
-- url     : https://prove2.me/submissions/c9da16a1-6a58-45c6-a2ae-86d1ca7b1535

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
open GlobalTheory.ChowHt.IsChowFormCycle
variable {Z Z' : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}
namespace GlobalTheory.ChowHt.IsChowFormCycle
theorem _root_.solution (h : IsChowFormCycle Z e dl f) :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => dl) f := by
  obtain ⟨c, hc, d, g, hg, rfl, rfl⟩ := h
  rw [isMultiHomogeneous_iff_block]
  refine IsWeightedHomogeneous.C_mul ?_ c
  have := IsWeightedHomogeneous.prod (w := GlobalTheory.Chow.blockWeight) Z.support
    (fun P => g P ^ Z P) (fun P => Z P • fun _ : Fin (e + 1) => d P)
    (fun P hP => IsWeightedHomogeneous.pow
      (isMultiHomogeneous_iff_block.1 (hg P hP).2.2.homog) (Z P))
  have hd : (fun _ : Fin (e + 1) => Z.sum fun P m => m * d P) =
      ∑ P ∈ Z.support, Z P • fun _ : Fin (e + 1) => d P := by
    funext b
    simp [Finsupp.sum, Finset.sum_apply]
  rw [hd]
  exact this
end GlobalTheory.ChowHt.IsChowFormCycle
