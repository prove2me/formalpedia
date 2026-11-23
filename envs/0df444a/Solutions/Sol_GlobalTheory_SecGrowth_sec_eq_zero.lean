-- Prove2me | solution 1 for GlobalTheory.SecGrowth.sec_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:43.295832+00:00
-- url     : https://prove2.me/submissions/9afa8e74-bb1a-4997-9b43-3143b1def29d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
variable {X : Scheme.{0}}
namespace GlobalTheory.SecGrowth
theorem _root_.solution [IsIntegral X] {M : LB X} (σ : LB.Sec M) {k₀ : M.ι} {W : X.Opens} (hW : W ≤ M.U k₀)
    [Nonempty W] (h : rs X hW (σ.f k₀) = 0) (k : M.ι) : σ.f k = 0 := by
  have h₀ : σ.f k₀ = 0 := map_injective_of_isIntegral X (homOfLE hW) (h.trans (map_zero _).symm)
  by_cases hk : M.U k = ⊥
  · have : Subsingleton Γ(X, M.U k) := by
      rw [hk]; infer_instance
    exact Subsingleton.elim _ _
  · have hne : Nonempty (M.U k ⊓ M.U k₀ : X.Opens) := by
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hk
      obtain ⟨y⟩ := ‹Nonempty W›
      obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (M.U k).isOpen (M.U k₀).isOpen ⟨x, hx⟩ ⟨y.1, hW y.2⟩
      exact ⟨⟨z, hz⟩⟩
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : M.U k ⊓ M.U k₀ ≤ M.U k))
    refine (σ.compat k k₀).trans ?_
    rw [h₀, map_zero, map_zero, mul_zero]
end GlobalTheory.SecGrowth
