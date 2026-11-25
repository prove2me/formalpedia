-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_point_of_injective_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:14.766304+00:00
-- url     : https://prove2.me/submissions/0cea9327-a205-4a2c-9a31-406b07f06347

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
theorem _root_.solution {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (κ : X ⟶ Y) (π : Y ⟶ Spec (.of k)) [LocallyOfFiniteType κ]
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (a b : Spec (.of Ω) ⟶ X),
      a ≫ κ ≫ π = specAlg(k, Ω) → a ≫ κ = b ≫ κ → a = b)
    (K' : Type u) [Field K'] [Algebra K K'] (x : Spec (.of K') ⟶ X) (y : Spec (.of K) ⟶ Y)
    (hx : x ≫ κ = specAlg(K, K') ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₁ = x → x₁ = x₀ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ π)
  let : Algebra k K := φ.hom.toAlgebra
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  refine exists_point_of_subsingleton_fiber κ y (AlgebraicClosure K)
    (fun a b ha hb ↦ h _ a b ?_ (ha.trans hb.symm)) _ x hx
  rw [reassoc_of% ha, ← hφ, ← Spec.map_comp]
  rfl
end GlobalTheory.OnePoint
