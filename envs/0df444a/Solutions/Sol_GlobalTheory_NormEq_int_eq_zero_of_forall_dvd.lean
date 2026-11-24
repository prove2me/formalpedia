-- Prove2me | solution 1 for GlobalTheory.NormEq.int_eq_zero_of_forall_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:28.397256+00:00
-- url     : https://prove2.me/submissions/a7fb85a1-1df6-46c0-9805-8c1bb8381dee

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfMemAllPowers
import Theorems.Thm_GlobalTheory_NormEq_eq_zero_of_forall_v_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c : intL L}
    (hc : ∀ m : ℕ, piO h ^ m ∣ c) : c = 0 := by
  refine Subtype.ext (eq_zero_of_forall_v_le fun m => ?_)
  obtain ⟨d, hd⟩ := hc m
  have hd' : (c : L) = ϖ ^ m * (d : L) := by
    rw [hd]; simp
  have hdv : Valued.v (d : L) ≤ 1 := d.2
  rw [hd', map_mul, map_pow, h.2.2.2.1]
  calc ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * Valued.v (d : L)
      ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * 1 := by gcongr
    _ = _ := by
      rw [mul_one, ← WithZero.coe_pow, ← ofAdd_nsmul]
      congr 2
      simp
end GlobalTheory.NormEq
