-- Prove2me | solution 1 for GlobalTheory.FixedPoint.value_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:10.64053+00:00
-- url     : https://prove2.me/submissions/080d7846-021d-4f88-9762-e14602f129f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
import Theorems.Thm_GlobalTheory_FixedPoint_existsUnique_factor
import Theorems.Thm_GlobalTheory_FixedPoint_top_le_preimage_comp_iff
import Theorems.Thm_GlobalTheory_FixedPoint_value_comp

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
theorem _root_.solution [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of K₁) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x)
    (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Z, U)) :
    ((Scheme.ΓSpecIso (.of K₁)).hom (x.appLE U ⊤ h f) : K₁) ∈ Set.range (algebraMap K₀ K₁) := by
  obtain ⟨y, rfl⟩ := (existsUnique_factor x hx).exists
  exact ⟨_, (value_comp _ y U ((top_le_preimage_comp_iff y U).1 h) h f).symm⟩
end GlobalTheory.FixedPoint
