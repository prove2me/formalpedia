-- Prove2me | solution 1 for GlobalTheory.Published.finitenessOfHermitianClasses_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:05:52.444287+00:00
-- url     : https://prove2.me/submissions/af2f5db1-1c54-4682-8653-4a0a6cd79276

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteUnitaryClassesOfDualEqSmul_87ddafdad67ddc06
import Theorems.Thm_GlobalTheory_exists_finite_unitary_classes
import Theorems.Thm_GlobalTheory_exists_int_bound_of_dual_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
namespace Published
theorem _root_.solution : Published.FinitenessOfHermitianClasses := by
  intro E _ _ _ r G hG hdet c hc 𝔪 h𝔪 ι _ 𝓛 h𝓛
  obtain ⟨N, hN, H⟩ := exists_int_bound_of_dual_eq_smul G hc
  obtain ⟨S, hS, HS⟩ := exists_finite_unitary_classes G hG hdet hN h𝔪 (fun p : 𝓛 => p.1.1)
    (fun p => p.1.2) (fun p => (h𝓛 p p.2).1) (fun p => (H _ (h𝓛 p p.2).2.1).1)
    (fun p => (H _ (h𝓛 p p.2).2.1).2) (fun p => (h𝓛 p p.2).2.2)
  refine ⟨Subtype.val '' S, by rintro _ ⟨p, -, rfl⟩; exact p.2, hS.image _, fun p hp => ?_⟩
  obtain ⟨s, hs, h⟩ := HS ⟨p, hp⟩
  exact ⟨s, ⟨s, hs, rfl⟩, h⟩
end Published
end GlobalTheory
