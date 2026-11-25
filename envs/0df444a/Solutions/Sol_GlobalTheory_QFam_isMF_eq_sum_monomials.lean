-- Prove2me | solution 1 for GlobalTheory.QFam.isMF_eq_sum_monomials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:03.912961+00:00
-- url     : https://prove2.me/submissions/aee136cf-f717-4d7f-9355-23e4d85d964f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularFormPolynomialE4E6
import Theorems.Thm_ReciprocityTheory_PGsh_coe_mem_monoSpanF
import Theorems.Thm_ReciprocityTheory_PGsh_coe_monoW
import Theorems.Thm_ReciprocityTheory_PGsh_monoIdx_wt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (IsMF)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
open ReciprocityTheory.PGsh
namespace GlobalTheory.QFam
theorem _root_.solution :
    ∀ (w : ℕ) (F : ℍ → ℂ), IsMF w F → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ),
      (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
        ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro w F hF
  obtain ⟨g, hg⟩ := hF
  have hm := coe_mem_monoSpanF w g
  rw [monoSpanF, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨(monoIdx w).image fun a => (a, monoB w a),
    fun p => if h : p.1 ∈ monoIdx w then c ⟨p.1, h⟩ else 0, ?_, fun τ => ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact monoIdx_wt ha
  · rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h), ← hg τ, ← hc,
      Finset.sum_apply, ← Finset.sum_coe_sort (monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coe_monoW a.2]
    simp [a.2]
end GlobalTheory.QFam
