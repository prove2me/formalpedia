-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_point_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:12.381496+00:00
-- url     : https://prove2.me/submissions/831d2d35-3ba2-46d9-b4a0-ecb51c53eeb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_laurentSeries
import Theorems.Thm_GlobalTheory_OnePoint_exists_point_of_locallyQuasiFinite

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
theorem _root_.solution {X Y : Scheme.{u}} (κ : X ⟶ Y) [LocallyQuasiFinite κ]
    (x : Spec (.of K⸨X⸩) ⟶ X) (y : Spec (.of K) ⟶ Y) (hx : x ≫ κ = specAlg(K, K⸨X⸩) ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, K⸨X⸩) ≫ x₁ = x → x₁ = x₀ :=
  have := isIntegrallyClosedIn_laurentSeries (K := K)
  exists_point_of_locallyQuasiFinite κ _ x y hx
end GlobalTheory.OnePoint
