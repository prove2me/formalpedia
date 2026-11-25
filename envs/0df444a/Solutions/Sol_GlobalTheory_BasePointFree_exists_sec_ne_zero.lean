-- Prove2me | solution 1 for GlobalTheory.BasePointFree.exists_sec_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:03.606536+00:00
-- url     : https://prove2.me/submissions/9d8ffc61-26b3-4c47-8e42-932ee1b2330a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
import Theorems.Thm_GlobalTheory_BasePointFree_exists_ne_zero_pair
import Theorems.Thm_GlobalTheory_BasePointFree_prod_translate_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.BasePointFree
namespace GlobalTheory.BasePointFree
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ), s ∈ X.Sec 1 1 → s ≠ 0 → ∀ q : ℕ, 2 ≤ q → ∀ v : Fin 1 → Vsp X.dim, ∃ F ∈ X.Sec q 1, F v ≠ 0 := by
  intro E _ _ _ X s hs hs0 q hq v
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hs0
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  obtain ⟨t, h1, h2⟩ := exists_ne_zero_pair (fun t : ℂ => s (v + t • (p - v)))
    (hs.1.comp (by fun_prop)) (by simpa using hp) m hm
  refine ⟨_, prod_translate_mem X s hs m (t • (p - v)), ?_⟩
  refine mul_ne_zero (pow_ne_zero _ (by simpa using h1)) ?_
  rwa [smul_smul, neg_mul]
end GlobalTheory.BasePointFree
