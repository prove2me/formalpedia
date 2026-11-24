-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.fixed_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:13.105934+00:00
-- url     : https://prove2.me/submissions/c2a4dbcb-912e-4616-b987-ac9beac38813

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_eq_one_or

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.UnitRoot
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat.UnitRoot
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E)
    (hx : IsIntegral ℤ x) (hfix : c x = x) :
    ∃ y ∈ (algebraMap (𝓞 F) F).range, algebraMap F E y = x := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := inferInstance
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) x).2 (fun f => by
    rcases eq_one_or c h2 hc f with rfl | rfl
    · rfl
    · exact hfix)
  exact ⟨y, ⟨⟨y, (isIntegral_algebraMap_iff (algebraMap F E).injective).1 hx⟩, rfl⟩, rfl⟩
end GlobalTheory.AdLat.UnitRoot
