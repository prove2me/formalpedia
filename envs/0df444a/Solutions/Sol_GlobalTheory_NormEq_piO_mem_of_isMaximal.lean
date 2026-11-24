-- Prove2me | solution 1 for GlobalTheory.NormEq.piO_mem_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:45.599968+00:00
-- url     : https://prove2.me/submissions/35caa4be-66a6-4f0e-9742-f8639c35b8d2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {M : Ideal (intL L)}
    (hM : M.IsMaximal) : piO h ∈ M := by
  by_contra hϖ
  obtain ⟨y, i, hi, e⟩ := hM.exists_inv hϖ
  have hlt : Valued.v ((y : L) * ϖ) < 1 := by
    rw [map_mul, h.2.2.2.1]
    have hy : Valued.v (y : L) ≤ 1 := y.2
    calc Valued.v (y : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul]
          exact_mod_cast (WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))
  have hi1 : (i : L) = 1 - (y : L) * ϖ := by
    have := congrArg Subtype.val e
    simp only [Subring.coe_add, Subring.coe_mul, coe_piO, OneMemClass.coe_one] at this
    linear_combination this
  have hv : Valued.v (i : L) = 1 := by rw [hi1]; exact Valuation.map_one_sub_of_lt _ hlt
  have hi0 : (i : L) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hinv : (i : L)⁻¹ ∈ intL L := by
    change Valued.v ((i : L)⁻¹) ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hu : IsUnit i := isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hi0])⟩
  exact hM.ne_top (M.eq_top_of_isUnit_mem hi hu)
end GlobalTheory.NormEq
