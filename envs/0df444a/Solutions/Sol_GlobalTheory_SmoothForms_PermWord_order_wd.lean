-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.order_wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:38.317734+00:00
-- url     : https://prove2.me/submissions/ac698e8d-52a8-4410-a6b5-63cef71dc16c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution (E : Fin n → Fin n → A) (l : List (Fin n × Fin n)) :
    order E (wd (gen n) l) = wd E (l : Multiset (Fin n × Fin n)).toList := by
  rw [wd_gen, ← congrFun (MvPolynomial.coe_basisMonomials (Fin n × Fin n) ℂ), order, Module.Basis.constr_basis]
  simp
end GlobalTheory.SmoothForms.PermWord
