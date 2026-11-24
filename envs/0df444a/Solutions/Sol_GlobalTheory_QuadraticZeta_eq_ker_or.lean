-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.eq_ker_or
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:05:59.225742+00:00
-- url     : https://prove2.me/submissions/dc3c0ba3-8592-4432-8957-8171b58a8b0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_int_dvd_of_mem
import Theorems.Thm_GlobalTheory_QuadraticZeta_eq_ker_of_mem

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
variable (b : Basis (Fin 2) ℤ (𝓞 K)) (h0 : b 0 = 1) {t n : ℤ} (hw : b 1 ^ 2 = t * b 1 - n)
  {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hPm : P.IsMaximal)
  (hP : P.under ℤ = .span {(p : ℤ)})
include h0 hw hp hPm hP
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (φ φ' : 𝓞 K →+* ZMod p) (h1 : φ (b 1) + φ' (b 1) = t)
    (h2 : φ (b 1) * φ' (b 1) = n) : P = RingHom.ker φ ∨ P = RingHom.ker φ' := by
  obtain ⟨c, hc⟩ := ZMod.intCast_surjective (φ (b 1))
  obtain ⟨c', hc'⟩ := ZMod.intCast_surjective (φ' (b 1))
  have e1 : ((c + c' - t : ℤ) : 𝓞 K) ∈ P := by
    rw [int_dvd_of_mem hP, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hc, hc', h1, sub_self]
  have e2 : ((c * c' - n : ℤ) : 𝓞 K) ∈ P := by
    rw [int_dvd_of_mem hP, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hc, hc', h2, sub_self]
  have : (b 1 - c) * (b 1 - c') ∈ P := by
    convert P.sub_mem e2 (P.mul_mem_left (b 1) e1) using 1
    push_cast
    linear_combination hw
  rcases hPm.isPrime.mem_or_mem this with h | h
  · exact Or.inl (eq_ker_of_mem b h0 hp hPm hP φ hc.symm h)
  · exact Or.inr (eq_ker_of_mem b h0 hp hPm hP φ' hc'.symm h)
end GlobalTheory.QuadraticZeta
