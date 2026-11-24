-- Prove2me | solution 1 for GlobalTheory.exists_splitExt_isGt_of_torusExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:23.329965+00:00
-- url     : https://prove2.me/submissions/fc826887-f416-4cce-9551-0628801a7cf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
import Theorems.Thm_GlobalTheory_T_exists_splitExtDatum_of_splitTorus_extension


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G],
      Nonempty (TorusExtension G) → ∃ E : SplitExt (Spec (CommRingCat.of K)), E.IsGt G := by
  intro K _ G _ _ ⟨T⟩
  let _ := T.addCommGroup
  let _ := T.free
  let _ := T.finite
  let _ := T.grpB
  obtain ⟨O, h₁, h₂, h₃, h⟩ := GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension (Spec (CommRingCat.of K)) T.X G T.B T.isAbelian T.q T.i
    T.q_hom T.i_hom T.q_flat T.q_surjective T.q_quasiCompact T.isKernel
  obtain ⟨d, -, -⟩ := h T.isAbelian
  exact ⟨_, ⟨d⟩⟩
end GlobalTheory
