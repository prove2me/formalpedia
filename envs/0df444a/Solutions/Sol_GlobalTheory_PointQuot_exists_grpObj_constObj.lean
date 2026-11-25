-- Prove2me | solution 1 for GlobalTheory.PointQuot.exists_grpObj_constObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:13.189376+00:00
-- url     : https://prove2.me/submissions/3023a381-f416-421a-a607-daba3f618df2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
import Theorems.Thm_GlobalTheory_PointQuot_exists_grpObj_of_mono
import Theorems.Thm_GlobalTheory_PointQuot_const_of_le
import Theorems.Thm_GlobalTheory_PointQuot_constPt_desc
import Theorems.Thm_GlobalTheory_PointQuot_locally_const_desc
import Theorems.Thm_GlobalTheory_PointQuot_exists_lift

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
open GlobalTheory
open GlobalTheory.PointQuot
variable {S : Scheme.{0}}
namespace GlobalTheory.PointQuot
theorem _root_.solution {I : Type} {A : Over S} [GrpObj A] (x : I → (𝟙_ (Over S) ⟶ A))
    [Mono (constDesc x)] (C : Subgroup (𝟙_ (Over S) ⟶ A)) (hC : Set.range x = C) :
    ∃ _ : GrpObj (constObj S I), IsMonHom (constDesc x) := by
  have mem : ∀ c, x c ∈ C := fun c => hC.le ⟨c, rfl⟩
  obtain ⟨c₀, h₀⟩ := hC.ge C.one_mem
  obtain ⟨m, hm⟩ := exists_lift x
    ((fst _ _ ≫ constDesc x) * (snd _ _ ≫ constDesc x)) fun z => by
      obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (fst _ _) z
      obtain ⟨W, hW, d, hd⟩ := locally_const_desc x (snd _ _) z
      obtain ⟨a, ha⟩ := hC.ge (C.mul_mem (mem c) (mem d))
      refine ⟨V ⊓ W, ⟨hV, hW⟩, a, ?_⟩
      rw [MonObj.comp_mul, const_of_le inf_le_left hc, const_of_le inf_le_right hd, ha,
        MonObj.comp_mul]
  obtain ⟨n, hn⟩ := exists_lift x (constDesc x)⁻¹ fun z => by
      obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (𝟙 _) z
      obtain ⟨a, ha⟩ := hC.ge (C.inv_mem (mem c))
      refine ⟨V, hV, a, ?_⟩
      rw [Category.id_comp] at hc
      rw [GrpObj.comp_inv, hc, ha, GrpObj.comp_inv]
  exact exists_grpObj_of_mono _ (constPt S c₀) m n ((constPt_desc x c₀).trans h₀) hm hn
end GlobalTheory.PointQuot
