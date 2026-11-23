-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.localField_secondCountable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:08.861388+00:00
-- url     : https://prove2.me/submissions/48174174-4a8e-493d-883e-ce3729f4dd96

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution : SecondCountableTopology F := by
  have hZ : Countable (WithZero (Multiplicative ℤ)) := by
    have : Countable (Multiplicative ℤ) := inferInstanceAs (Countable ℤ)
    exact inferInstanceAs (Countable (Option (Multiplicative ℤ)))
  have hcount : Countable (ValueGroupWithZero F) :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective.countable
  have : Countable (ValueGroupWithZero F)ˣ := Units.val_injective.countable
  have hsig : SigmaCompactSpace F := by
    refine SigmaCompactSpace.of_countable (Set.range fun γ : ValueGroupWithZero F => {x : F | valuation F x ≤ γ})
      (Set.countable_range _) ?_ ?_
    · rintro _ ⟨γ, rfl⟩
      exact IsNonarchimedeanLocalField.isCompact_closedBall F γ
    · refine Set.eq_univ_of_forall fun x => ?_
      exact Set.mem_sUnion.mpr ⟨_, ⟨valuation F x, rfl⟩, show valuation F x ≤ valuation F x from le_rfl⟩
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : (nhds (0 : F)).IsCountablyGenerated :=
    (IsValuativeTopology.hasBasis_nhds_zero F).isCountablyGenerated
  have := IsUniformAddGroup.uniformity_countably_generated (α := F)
  infer_instance
end GlobalTheory.SgLoc.Top
