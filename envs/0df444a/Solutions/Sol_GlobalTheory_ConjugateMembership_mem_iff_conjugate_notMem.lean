-- Prove2me | solution 1 for GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:42:49.099057+00:00
-- url     : https://prove2.me/submissions/2d2eff71-042c-47bc-b9eb-cdc02dccf640

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Theorems.Thm_GlobalTheory_ConjugateMembership_eq_iff_conj_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateMembership
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ConjugateMembership
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hx : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [← map_pow, hE]; simp
  have hr : H.rt0 ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [H.sqrt_neg_disc_sq]; simp
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  exact eq_iff_conj_ne hd hx hr
end GlobalTheory.ConjugateMembership
