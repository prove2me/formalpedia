-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_point_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:58.57561+00:00
-- url     : https://prove2.me/submissions/3ee9c068-4eb7-4392-ad26-75d063f0a28b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_exists_point_of_subsingleton_fiber

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
theorem _root_.solution [PerfectField K] {X Y : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyOfFiniteType κ]
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
      Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ κ)
    (K' : Type u) [Field K'] [Algebra K K'] (x : Spec (.of K') ⟶ X) (y : Spec (.of K) ⟶ Y)
    (hx : x ≫ κ = specAlg(K, K') ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₁ = x → x₁ = x₀ :=
  exists_point_of_subsingleton_fiber κ y (AlgebraicClosure K)
    (fun _ _ ha hb ↦ h _ (ha.trans hb.symm)) _ x hx
end GlobalTheory.OnePoint
