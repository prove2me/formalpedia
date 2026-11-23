-- Prove2me | solution 1 for GlobalTheory.SecAff.chart_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:11.903344+00:00
-- url     : https://prove2.me/submissions/4ce36eae-0713-41d1-a578-87338a47561f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
namespace GlobalTheory.SecAff
theorem _root_.solution (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j ≤ (LPow A L a T').U j := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : ((h ▷ A).left ≫ (snd T A).left) y ∈ (L.U (j i) : Set A.left) := Set.mem_iInter.1 hy i
  rw [whisker_snd_left] at h1
  exact h1
end GlobalTheory.SecAff
