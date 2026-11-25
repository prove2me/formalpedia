-- Prove2me | solution 1 for GlobalTheory.FixedPoint.defined_over_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:25.650734+00:00
-- url     : https://prove2.me/submissions/727ab57b-f851-4141-863b-ec547feb6adb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
import Theorems.Thm_GlobalTheory_FixedPoint_existsUnique_factor
import Theorems.Thm_GlobalTheory_FixedPoint_value_mem_range
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_range_algebraMap_of_forall_algEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K₀ K₁ L : Type u} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]
namespace GlobalTheory.FixedPoint
theorem _root_.solution [CharZero K₀] [IsAlgClosed L] :
    (∀ a : L, (∀ s : L ≃ₐ[K₀] L, s a = a) → a ∈ Set.range (algebraMap K₀ L)) ∧
    ∀ (Z : Scheme.{u}) (x : Spec (.of K₁) ⟶ Z),
      (∀ s : L ≃ₐ[K₀] L,
        Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x) →
      (∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x) ∧
      ∀ (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Z, U)),
        ((Scheme.ΓSpecIso (.of K₁)).hom (x.appLE U ⊤ h f) : K₁) ∈
          Set.range (algebraMap K₀ K₁) :=
  ⟨GaloisDescent.mem_range_algebraMap_of_forall_algEquiv,
    fun _ x hx => ⟨existsUnique_factor x hx, value_mem_range x hx⟩⟩
end GlobalTheory.FixedPoint
