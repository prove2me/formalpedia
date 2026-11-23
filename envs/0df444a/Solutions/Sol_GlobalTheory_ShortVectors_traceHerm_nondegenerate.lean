-- Prove2me | solution 1 for GlobalTheory.ShortVectors.traceHerm_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:56.565988+00:00
-- url     : https://prove2.me/submissions/8b0d7ec4-9ec2-49cc-a1d2-83e97b0e6b77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_self
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_isSymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
open GlobalTheory.ShortVectors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ShortVectors
theorem _root_.solution (n : ℕ) : (traceHerm (E := E) n).Nondegenerate := by
  have hl : ∀ x : Fin n → E, (∀ y, traceHerm n x y = 0) → x = 0 := by
    intro x hx
    have h0 := traceHerm_self x
    rw [hx x, Rat.cast_zero] at h0
    obtain ⟨σ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    funext k
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun σ _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg ‖σ (x k)‖)).mp h0.symm σ (Finset.mem_univ _)
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖σ (x k)‖)).mp hs k
      (Finset.mem_univ _)
    have h1 : σ (x k) = 0 := by simpa using hk
    simpa using h1
  exact ⟨hl, fun y hy => hl y fun x => by rw [(traceHerm_isSymm n).eq]; exact hy x⟩
end GlobalTheory.ShortVectors
