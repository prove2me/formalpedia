-- Prove2me | solution 1 for GlobalTheory.RepUniq.same_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:03:56.167781+00:00
-- url     : https://prove2.me/submissions/f42f54c9-017f-46ac-900c-f09154f612bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation
import Theorems.Thm_GlobalTheory_RepUniq_Same_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}
variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}
namespace GlobalTheory.RepUniq
theorem _root_.solution (H : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ Same M th (W.ι ≫ x) M' th' (W.ι ≫ x')) :
    Same M th x M' th' x' := fun t => by
  obtain ⟨W, ht, h⟩ := H t
  obtain ⟨V, hV, f, ⟨j, hj, u, hu, e⟩, ⟨k, hk, u', hu', e'⟩⟩ := h ⟨t, ht⟩
  have hle : V ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ V) := (W.ι.preimage_image_eq V).ge
  have : IsIso (W.ι.appLE (W.ι ''ᵁ V) V hle) := by
    rw [← Scheme.Hom.appIso_hom']
    infer_instance
  have hb := ConcreteCategory.bijective_of_isIso (W.ι.appLE (W.ι ''ᵁ V) V hle)
  let φ := RingEquiv.ofBijective (W.ι.appLE (W.ι ''ᵁ V) V hle).hom hb
  have h₁ : W.ι ''ᵁ V ≤ x ⁻¹ᵁ M.U j := by
    rintro _ ⟨y, hy, rfl⟩
    exact hj hy
  have h₂ : W.ι ''ᵁ V ≤ x' ⁻¹ᵁ M'.U k := by
    rintro _ ⟨y, hy, rfl⟩
    exact hk hy
  refine ⟨W.ι ''ᵁ V, ⟨⟨t, ht⟩, hV, rfl⟩, fun i => φ.symm (f i),
    ⟨j, h₁, φ.symm u, hu.map _, fun i => φ.injective ?_⟩, ⟨k, h₂, φ.symm u', hu'.map _, fun i => φ.injective ?_⟩⟩
  · rw [← map_mul, φ.apply_symm_apply, ← e]
    exact appLE_appLE _ _ _ _ _
  · rw [← map_mul, φ.apply_symm_apply, ← e']
    exact appLE_appLE _ _ _ _ _
end GlobalTheory.RepUniq
