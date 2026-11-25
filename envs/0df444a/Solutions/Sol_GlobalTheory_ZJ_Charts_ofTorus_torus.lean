-- Prove2me | solution 1 for GlobalTheory.ZJ.Charts.ofTorus_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:17.237858+00:00
-- url     : https://prove2.me/submissions/5412de86-aa7f-453b-a2ee-44b0a262c4b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Theorems.Thm_GlobalTheory_ZJ_stable_top
import Theorems.Thm_GlobalTheory_ZJ_hasWt_one
import Theorems.Thm_GlobalTheory_ZJ_hasWt_charUnit
import Theorems.Thm_GlobalTheory_ZJ_HasWt_mem_range_of_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZJ
attribute [instance] Charts.fin Charts.finC
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
namespace GlobalTheory.ZJ
namespace Charts
theorem _root_.solution (S : Scheme.{0}) [IsAffine S] (d : ℕ) :
    (Charts.ofTorus S d).Torus (d := d) some (𝟙 _) where
  hom := inferInstance
  stable := fun _ => stable_top _
  inv := by
    rintro a j hj
    obtain rfl : j = none := hj
    exact hasWt_one _ _
  wt := by
    rintro a j k hj
    obtain rfl : j = some k := hj
    exact hasWt_charUnit _
  bpf := by
    intro k x
    refine ⟨⟨none, rfl⟩, some k, rfl, ?_⟩
    change x ∈ (splitTorus S (Fin d → ℤ)).left.basicOpen (charUnit S (Fin d → ℤ) (Pi.single k 1)).val
    rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]
    trivial
  gen := by
    intro a u hu
    exact Subring.subset_closure (Or.inl (HasWt.mem_range_of_id hu))
end Charts
end GlobalTheory.ZJ
