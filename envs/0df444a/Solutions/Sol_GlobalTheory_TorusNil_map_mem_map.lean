-- Prove2me | solution 1 for GlobalTheory.TorusNil.map_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:47.216569+00:00
-- url     : https://prove2.me/submissions/18deb524-94b0-4cec-b339-696bcd2db1fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
namespace GlobalTheory.TorusNil
theorem _root_.solution {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (I : Ideal A) (r : C →ₗ[A] D) {x : C} (hx : x ∈ I.map (algebraMap A C)) :
    r x ∈ I.map (algebraMap A D) := by
  have h1 : x ∈ I • (⊤ : Submodule A C) := by rw [Ideal.smul_top_eq_map]; exact hx
  have h2 : r x ∈ I • (⊤ : Submodule A D) := by
    have := Submodule.mem_map_of_mem (f := r) h1
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  rw [Ideal.smul_top_eq_map] at h2
  exact h2
end GlobalTheory.TorusNil
