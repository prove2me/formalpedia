-- Prove2me | solution 1 for GlobalTheory.NormEq.span_piO_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:46.299203+00:00
-- url     : https://prove2.me/submissions/5a43d3cf-50a0-4836-adf2-163f2dadb90a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
import Theorems.Thm_GlobalTheory_NormEq_mem_span_piO_of_lt
import Theorems.Thm_GlobalTheory_NormEq_isUnit_of_v_eq_one

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
    (Ideal.span {piO h}).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => ?_, fun J y _ hy hyJ => ?_⟩
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    have hv := congrArg (fun t : intL L => Valued.v (t : L)) hc
    simp only [Subring.coe_mul, coe_piO, map_mul, h.2.2.2.1, OneMemClass.coe_one, map_one] at hv
    have hc1 : Valued.v (c : L) ≤ 1 := c.2
    have hlt : Valued.v (c : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 :=
      calc Valued.v (c : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
          ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by gcongr
        _ < 1 := by
          rw [one_mul]
          exact_mod_cast (WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))
    exact absurd hv hlt.ne
  · have hv : Valued.v (y : L) = 1 := by
      rcases lt_or_eq_of_le (show Valued.v (y : L) ≤ 1 from y.2) with hl | he
      · exact absurd (mem_span_piO_of_lt h y hl) hy
      · exact he
    rw [Ideal.eq_top_of_isUnit_mem J hyJ (isUnit_of_v_eq_one y hv)]
    trivial
end GlobalTheory.NormEq
