-- Prove2me | solution 1 for GroundTheory.ProfCoh.cdp_le_of_forall_primary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:37.373826+00:00
-- url     : https://prove2.me/submissions/5c9c92ce-839e-447b-91ad-c9e86b02dd62

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_subQuotShortComplex_shortExact
import Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_eq_bot_iff
import Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_cohomology_eq_bot_of_bijective
import Theorems.Thm_GroundTheory_ProfCoh_primarySubmodule_le_comap
import Theorems.Thm_GroundTheory_ProfCoh_bijective_nsmul_quotient_primarySubmodule
import Theorems.Thm_GroundTheory_ProfCoh_cdp_le_iff
import Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology_exact__bae5173fa4e3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} (hp : p.Prime) {n : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      ∀ q : ℕ, n < q → Subsingleton (cohomology A q)) :
    cdp p G ≤ n := by
  rw [cdp_le_iff]
  intro A _ hA q hq
  have hq' : n < q := by exact_mod_cast hq
  have hW := primarySubmodule_le_comap A p
  have hTp : ∀ a : A.subrepresentation (primarySubmodule A p) hW, ∃ k : ℕ, p ^ k • a = 0 := by
    rintro ⟨a, k, hk⟩
    exact ⟨k, Subtype.ext hk⟩
  have hT := h (A.subrepresentation (primarySubmodule A p) hW) hTp q hq'
  have hQ := primaryComponent_cohomology_eq_bot_of_bijective
    (A.quotient (primarySubmodule A p) hW) (p := p)
    (bijective_nsmul_quotient_primarySubmodule A hA hp) q
  rw [primaryComponent_eq_bot_iff] at hQ ⊢
  rintro x ⟨k, hk⟩
  have hx : (cohomologyMap (Rep.mkQ A (primarySubmodule A p) hW) q).hom x = 0 :=
    hQ _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (cohomology_exact₂ (subQuotShortComplex_shortExact A (primarySubmodule A p) hW) q) x hx
  rw [← hz, @Subsingleton.elim _ hT z 0]
  exact map_zero _
end GroundTheory.ProfCoh
