-- Prove2me | solution 1 for GlobalTheory.Moduli.LevelAction.mem_of_modN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:49.765507+00:00
-- url     : https://prove2.me/submissions/4862454c-01f1-46fb-9cf2-dc8fcca0844c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open GlobalTheory GlobalTheory.Moduli GlobalTheory.Moduli.LevelAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.Moduli.LevelAction
theorem _root_.solution (l : Level H) {x : D.La} (h : D.ModN l.M x) : x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, rfl⟩ := h
  have h₁ : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  have h₂ : (l.M : 𝓞 E) ∈ l.Mb := by
    refine Submodule.mul_induction_on h₁ (fun x hx y _ => l.Mb.mul_mem_right y hx) fun x y hx hy => l.Mb.add_mem hx hy
  have h₃ : l.M • b = (l.M : 𝓞 E) • b := (Nat.cast_smul_eq_nsmul (𝓞 E) l.M b).symm
  rw [h₃]
  exact Submodule.smul_mem_smul h₂ Submodule.mem_top
end GlobalTheory.Moduli.LevelAction
