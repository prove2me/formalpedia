-- Prove2me | solution 1 for GlobalTheory.CMVal.TermUnit.norm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:38:13.5768+00:00
-- url     : https://prove2.me/submissions/3f0bd124-51cd-4287-8572-42e1fd8ac6da

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_prod_norm_sq
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.CMVal.TermUnit
theorem _root_.solution [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) {x : E} (hx : x ≠ 0) :
    ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re)) := by
  have hpos : ∀ i, 0 < ‖φ i x‖ := fun i => norm_pos_iff.mpr ((map_ne_zero (φ i)).mpr hx)
  rw [← prod_norm_sq h x, ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  simp only [term, norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha := hpos i
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos ha, inv_pow, ← Real.rpow_natCast _ (2 * s + κ i),
    ← Real.rpow_natCast _ (κ i), ← Real.rpow_neg ha.le, ← Real.rpow_add ha, ← Real.rpow_add ha,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le]
  congr 1
  simp
  ring
end GlobalTheory.CMVal.TermUnit
