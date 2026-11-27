-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_rational_weierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:46:27.655694+00:00
-- url     : https://prove2.me/submissions/4f3ebaaf-cecf-42dd-91b2-4024bbc8a46c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Theorems.Thm_GroundTheory_Global_Elliptic_isPeriodic_derivWeierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_codiscrete_derivWeierstrassP_ne_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_polynomial_div_of_even
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∃ P Q R S : ℂ[X], Q ≠ 0 ∧ S ≠ 0 ∧ f =ᶠ[codiscrete ℂ] fun z ↦
      P.eval (℘[L] z) / Q.eval (℘[L] z) + ℘'[L] z * (R.eval (℘[L] z) / S.eval (℘[L] z)) := by
  have hneg : Meromorphic fun z ↦ f (-z) := fun z ↦ by
    have : MeromorphicAt f (-z) := hf.1 (-z)
    exact this.comp_analyticAt (g := fun z ↦ -z) (by fun_prop)
  have hpneg : IsPeriodic L fun z ↦ f (-z) := fun z l hl ↦ by
    simp only [neg_add, ← sub_eq_add_neg]
    exact hf.2.sub (-z) hl
  obtain ⟨P, Q, hQ, h1⟩ := exists_polynomial_div_of_even (L := L)
    (f := fun z ↦ (f z + f (-z)) / 2)
    ⟨fun z ↦ ((hf.1 z).add (hneg z)).div analyticAt_const.meromorphicAt,
      fun z l hl ↦ by simp only [hf.2 z l hl, hpneg z l hl]⟩
    (fun z ↦ by simp only [neg_neg]; ring)
  obtain ⟨R, S, hS, h2⟩ := exists_polynomial_div_of_even (L := L)
    (f := fun z ↦ (f z - f (-z)) / 2 / ℘'[L] z)
    ⟨fun z ↦ (((hf.1 z).sub (hneg z)).div analyticAt_const.meromorphicAt).div
      (L.meromorphic_derivWeierstrassP z),
      fun z l hl ↦ by simp only [hf.2 z l hl, hpneg z l hl, isPeriodic_derivWeierstrassP z l hl]⟩
    (fun z ↦ by simp only [neg_neg, L.derivWeierstrassP_neg]; ring)
  refine ⟨P, Q, R, S, hQ, hS, ?_⟩
  filter_upwards [h1, h2, eventually_codiscrete_derivWeierstrassP_ne_zero (L := L)]
    with z e1 e2 e3
  rw [← e1, ← e2]
  field_simp
  ring
end GroundTheory.Global.Elliptic
