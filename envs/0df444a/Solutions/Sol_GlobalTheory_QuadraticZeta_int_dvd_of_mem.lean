-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.int_dvd_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:04.707313+00:00
-- url     : https://prove2.me/submissions/9ef32212-fb90-4278-8c56-4b2c419253b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution {p : ℕ} {P : Ideal (𝓞 K)} (hP : P.under ℤ = .span {(p : ℤ)}) (x : ℤ) :
    (x : 𝓞 K) ∈ P ↔ (p : ℤ) ∣ x := by
  rw [← Ideal.mem_span_singleton, ← hP, Ideal.under, Ideal.mem_comap]
  simp
end GlobalTheory.QuadraticZeta
