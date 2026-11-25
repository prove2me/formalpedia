-- Prove2me | solution 1 for GlobalTheory.PolyNorm.mul_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:28.827893+00:00
-- url     : https://prove2.me/submissions/33ab2634-0287-4408-a5e5-c7939c9aa299

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
import Theorems.Thm_GlobalTheory_PolyNorm_shift_poly
import Theorems.Thm_P2M_GlobalTheory_PolyNorm_shift_poly__31f4ccca3525

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN
namespace GlobalTheory.PolyNorm
theorem _root_.solution (Good : ℤ[X] → Prop) (hG : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t))
    (hm : ∀ F G, Good F → Good G → N (F * G) = N F * N G) (F G : ℤ[X]) :
    N (F * G) = N F * N G := by
  obtain ⟨p, hp⟩ := shift_poly N Φ hN F
  obtain ⟨q, hq⟩ := shift_poly N Φ hN G
  obtain ⟨s, hs⟩ := shift_poly₂ N Φ hN F G
  have : s = p * q := by
    apply eq_of_infinite_eval_eq
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp ((hG F).and (hG G))
    refine Set.Infinite.mono (s := (fun t : ℕ => (t : ℚ)) '' Set.Ici a) ?_
      ((Set.Ici_infinite a).image Nat.cast_injective.injOn)
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_setOf_eq, eval_mul]
    rw [← hp, ← hq, ← hs, hm _ _ (ha t ht).1 (ha t ht).2]
  have h0 := hs 0
  rw [this, eval_mul, ← hp, ← hq] at h0
  simpa using h0
end GlobalTheory.PolyNorm
