-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:08.611492+00:00
-- url     : https://prove2.me/submissions/18722acf-a5e8-4182-b710-742eb1aba3b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
variable [DecidableEq n]
namespace GlobalTheory.LocalQuad.FiveVar
theorem _root_.solution (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0)
    (h : decide (Even (WithZero.log (v y))) = decide (Even (WithZero.log (v x)))) :
    ∃ u : K, v u ^ 2 * v y = v x := by
  have he : Even (WithZero.log (v x) - WithZero.log (v y)) := by
    rw [Int.even_sub]
    simpa [eq_comm] using h
  obtain ⟨m, hm⟩ := he
  obtain ⟨u, hu⟩ := hv (WithZero.exp m)
  refine ⟨u, ?_⟩
  rw [hu, ← WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hx),
    ← WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hy), sq, ← WithZero.exp_add,
    ← WithZero.exp_add]
  congr 1
  omega
end GlobalTheory.LocalQuad.FiveVar
