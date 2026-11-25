-- Prove2me | solution 1 for GlobalTheory.PointQuot.mono_constDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:15.029735+00:00
-- url     : https://prove2.me/submissions/d641a094-fa89-428a-9cbc-09d599a61472

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
import Theorems.Thm_GlobalTheory_PointQuot_const_of_le
import Theorems.Thm_GlobalTheory_PointQuot_hom_ext_local
import Theorems.Thm_GlobalTheory_PointQuot_constPt_desc
import Theorems.Thm_GlobalTheory_PointQuot_locally_const
import Theorems.Thm_GlobalTheory_PointQuot_epi_toUnit

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
theorem _root_.solution {k : Type} [Field k] {I : Type} {A : Over (Sp k)}
    (x : I → (𝟙_ (Over (Sp k)) ⟶ A)) (hx : Function.Injective x) : Mono (constDesc x) := by
  refine ⟨fun {Z} f g h => hom_ext_local f g fun z => ?_⟩
  obtain ⟨V, hV, c, hc⟩ := locally_const f z
  obtain ⟨W, hW, d, hd⟩ := locally_const g z
  have hc' := const_of_le (inf_le_left : V ⊓ W ≤ V) hc
  have hd' := const_of_le (inf_le_right : V ⊓ W ≤ W) hd
  have : Nonempty (openObj Z (V ⊓ W)).left := ⟨(⟨z, hV, hW⟩ : (V ⊓ W : Z.left.Opens))⟩
  have := epi_toUnit (openObj Z (V ⊓ W))
  obtain rfl : c = d := by
    apply hx
    rw [← cancel_epi (toUnit (openObj Z (V ⊓ W))), ← constPt_desc x c, ← constPt_desc x d,
      ← reassoc_of% hc', ← reassoc_of% hd', h]
  exact ⟨V ⊓ W, ⟨hV, hW⟩, hc'.trans hd'.symm⟩
end GlobalTheory.PointQuot
