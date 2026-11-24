-- Prove2me | solution 1 for GlobalTheory.NormEq.finite_quot_span_piO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:45.444576+00:00
-- url     : https://prove2.me/submissions/0b3d9a20-3901-42ec-91b9-1bba1550264e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
import Theorems.Thm_GlobalTheory_NormEq_mem_span_piO_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    Finite (intL L ⧸ Ideal.span {piO h}) := by
  let V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc := h.2.2.2.2.2.2
  have hq := h.2.2.2.2.2.1
  have hfin0 := Nat.finite_of_card_ne_zero (hc.trans_ne (by positivity))
  haveI : Finite (V ⧸ IsLocalRing.maximalIdeal V) := hfin0
  let f : V →+* intL L :=
    { toFun := fun y => ⟨(y : L), (Valuation.mem_valuationSubring_iff _ _).1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hker : ∀ y ∈ IsLocalRing.maximalIdeal V, (Ideal.Quotient.mk (Ideal.span {piO h})).comp f y = 0 := by
    intro y hy
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    by_contra hn
    have hv : Valued.v (y : L) = 1 := by
      rcases lt_or_eq_of_le (show Valued.v (y : L) ≤ 1 from (f y).2) with hl | he
      · exact absurd (mem_span_piO_of_lt h (f y) hl) hn
      · exact he
    apply (IsLocalRing.mem_maximalIdeal _).1 hy
    have hy0 : (y : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have hinv : (y : L)⁻¹ ∈ V := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, hv, inv_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (show (y : L) * (y : L)⁻¹ = 1 from mul_inv_cancel₀ hy0)⟩
  let g := Ideal.Quotient.lift (IsLocalRing.maximalIdeal V) ((Ideal.Quotient.mk (Ideal.span {piO h})).comp f) hker
  refine Finite.of_surjective g fun a => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨Ideal.Quotient.mk _ ⟨(y : L), (Valuation.mem_valuationSubring_iff _ _).2 y.2⟩, ?_⟩
  rfl
end GlobalTheory.NormEq
