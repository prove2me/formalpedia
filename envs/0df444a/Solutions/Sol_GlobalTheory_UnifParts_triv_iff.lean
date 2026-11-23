-- Prove2me | solution 1 for GlobalTheory.UnifParts.triv_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:14:38.370536+00:00
-- url     : https://prove2.me/submissions/a9ab2f8a-cbe3-430c-b980-14d2b236f87d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FamilyUnifOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifParts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.UnifParts
theorem _root_.solution {D D' : Datum H} (l : Level H) (t : D.La →ₗ[𝓞 E] D'.La)
    (ht : ∀ b, ∃ a e, b = t a + l.M' • e) (gam : D'.La ≃ₗ[𝓞 E] D'.La) (I : Ideal (𝓞 E)) (n : ℕ) (hn : n ∣ l.M') :
    (∀ a ∈ I • (⊤ : Submodule (𝓞 E) D.La), ∃ x, gam (t a) = t a + n • x) ↔
      ∀ a ∈ I • (⊤ : Submodule (𝓞 E) D'.La), ∃ x, gam a = a + n • x := by
  obtain ⟨k, hk⟩ := hn
  constructor
  · intro h b hb
    refine Submodule.smul_induction_on hb (fun c hc b' _ => ?_) ?_
    · obtain ⟨a, e, rfl⟩ := ht b'
      obtain ⟨x, hx⟩ := h (c • a) (Submodule.smul_mem_smul hc trivial)
      refine ⟨x + k • (gam (c • e) - c • e), ?_⟩
      rw [smul_add, ← t.map_smul, map_add, hx, smul_comm c, map_nsmul, smul_add, ← mul_smul, hk, smul_sub]
      abel
    · rintro x y ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨u + v, by rw [map_add, hu, hv, smul_add]; abel⟩
  · intro h a ha
    refine h _ (Submodule.smul_induction_on ha (fun c hc a' _ => ?_) fun x y hx hy => ?_)
    · rw [t.map_smul]; exact Submodule.smul_mem_smul hc trivial
    · rw [map_add]; exact add_mem hx hy
end GlobalTheory.UnifParts
