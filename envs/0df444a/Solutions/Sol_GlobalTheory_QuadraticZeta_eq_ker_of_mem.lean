-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.eq_ker_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:46:32.079245+00:00
-- url     : https://prove2.me/submissions/e6ef1771-fa7a-4222-aaa1-0d7b23884e92

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
omit hw
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (φ : 𝓞 K →+* ZMod p) {c : ℤ} (hc : φ (b 1) = c) (hm : b 1 - c ∈ P) :
    P = RingHom.ker φ := by
  haveI := Fact.mk hp
  refine ((RingHom.ker_isMaximal_of_surjective φ (ZMod.ringHom_surjective φ)).eq_of_le
    hPm.ne_top fun z hz => ?_).symm
  rw [eq_coord b h0 z] at hz ⊢
  generalize b.repr z 0 = x, b.repr z 1 = y at hz ⊢
  have h1 : ((x + y * c : ℤ) : 𝓞 K) ∈ P := by
    rw [int_dvd_of_mem hP, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [hc] using hz
  convert P.add_mem h1 (P.mul_mem_left y hm) using 1
  push_cast
  ring
end GlobalTheory.QuadraticZeta
