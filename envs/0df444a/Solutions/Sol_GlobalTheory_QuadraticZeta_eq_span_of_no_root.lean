-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.eq_span_of_no_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:46:32.984834+00:00
-- url     : https://prove2.me/submissions/dad311c5-aa43-492b-83ac-6f48ea4e32cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_eq_coord
import Theorems.Thm_GlobalTheory_QuadraticZeta_int_dvd_of_mem

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
theorem _root_.solution (h : ∀ β : ZMod p, β ^ 2 ≠ t * β - n) :
    P = Ideal.span {(p : 𝓞 K)} := by
  refine le_antisymm (fun z hz => ?_) ?_
  · rw [eq_coord b h0 z] at hz ⊢
    generalize b.repr z 0 = x, b.repr z 1 = y at hz ⊢
    have h1 : ((x ^ 2 + t * x * y + n * y ^ 2 : ℤ) : 𝓞 K) ∈ P := by
      convert P.mul_mem_left (x + y * (t - b 1)) hz using 1
      push_cast
      linear_combination (y : 𝓞 K) ^ 2 * hw
    rw [int_dvd_of_mem hP, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    push_cast at h1
    haveI := Fact.mk hp
    have hy : (y : ZMod p) = 0 := by
      by_contra hy
      refine h (-x / y) ?_
      field_simp
      linear_combination h1
    have hx : (x : ZMod p) = 0 := by simpa [hy] using h1
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact Ideal.mem_span_singleton.2 ⟨x + y * b 1, by push_cast; ring⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact_mod_cast (int_dvd_of_mem hP p).2 dvd_rfl
end GlobalTheory.QuadraticZeta
