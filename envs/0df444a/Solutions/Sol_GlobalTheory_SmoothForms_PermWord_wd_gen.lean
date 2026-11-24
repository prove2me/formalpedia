-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.wd_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:51:59.666923+00:00
-- url     : https://prove2.me/submissions/40b30f20-c6e9-4638-add7-d441f0b6eb08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_cons

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
theorem _root_.solution (l : List (Fin n × Fin n)) :
    wd (gen n) l = MvPolynomial.monomial (Multiset.toFinsupp (l : Multiset (Fin n × Fin n))) 1 := by
  induction l with
  | nil => simp [wd]
  | cons z l ih =>
    rw [wd_cons, ih, gen, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, ← Multiset.cons_coe,
      ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton]
end GlobalTheory.SmoothForms.PermWord
