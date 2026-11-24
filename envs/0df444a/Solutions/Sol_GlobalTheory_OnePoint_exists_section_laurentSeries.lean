-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_section_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:18.009032+00:00
-- url     : https://prove2.me/submissions/fe0d9ba0-c7fa-4896-b294-0f7cd8a9bd65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_laurentSeries
import Theorems.Thm_GlobalTheory_OnePoint_exists_section_of_locallyQuasiFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (x : Spec (.of K⸨X⸩) ⟶ F) (hx : x ≫ f = specAlg(K, K⸨X⸩)) :
    ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₁ = x → x₁ = x₀ :=
  have := isIntegrallyClosedIn_laurentSeries (K := K)
  exists_section_of_locallyQuasiFinite f _ x hx
end GlobalTheory.OnePoint
