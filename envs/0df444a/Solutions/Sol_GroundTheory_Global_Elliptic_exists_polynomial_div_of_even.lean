-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_polynomial_div_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:41.106279+00:00
-- url     : https://prove2.me/submissions/be0cee18-8ac4-48c0-a552-f964b0397293

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Theorems.Thm_GroundTheory_Global_Elliptic_meromorphicAt_eval
import Theorems.Thm_GroundTheory_Global_Elliptic_isPeriodic_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_polynomial_of_even_of_analyticAt_off_lattice
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_polynomial_mul_analyticAt_off_lattice
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_codiscrete_eval_weierstrassP_ne_zero

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
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f)
    (he : ∀ z, f (-z) = f z) :
    ∃ P Q : ℂ[X], Q ≠ 0 ∧ f =ᶠ[codiscrete ℂ] fun z ↦ P.eval (℘[L] z) / Q.eval (℘[L] z) := by
  obtain ⟨Q, hQ, hQa⟩ := exists_polynomial_mul_analyticAt_off_lattice hf.1 hf.2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun w ↦ Q.eval (℘[L] w) * f w) 0 := by
    cases h : meromorphicOrderAt (fun w ↦ Q.eval (℘[L] w) * f w) 0 with
    | top => exact ⟨0, le_top⟩
    | coe o => exact ⟨o.natAbs, by exact_mod_cast (by omega : -(o.natAbs : ℤ) ≤ o)⟩
  obtain ⟨P, hP⟩ := exists_polynomial_of_even_of_analyticAt_off_lattice n
    (g := fun w ↦ Q.eval (℘[L] w) * f w)
    (fun z ↦ by
      have := hf.1 z
      have := meromorphicAt_eval (L.meromorphic_weierstrassP z) Q
      fun_prop)
    (fun z l hl ↦ by simp only [hf.2 z l hl, isPeriodic_weierstrassP z l hl])
    (fun z ↦ by simp only [he, L.weierstrassP_neg]) hQa hn
  refine ⟨P, Q, hQ, ?_⟩
  filter_upwards [hP, eventually_codiscrete_eval_weierstrassP_ne_zero hQ] with z hz hQz
  rw [← hz, mul_div_cancel_left₀ _ hQz]
end GroundTheory.Global.Elliptic
