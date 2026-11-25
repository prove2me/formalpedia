-- Prove2me | solution 1 for GlobalTheory.DiscEval.residueFieldInfiniteOn_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:59:29.214476+00:00
-- url     : https://prove2.me/submissions/4ecf971b-6d6d-4140-915e-e733bdd29fc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
namespace GlobalTheory.DiscEval
theorem _root_.solution {C K : Type*} [NormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [NormedField K] [IsUltrametricDist K] (e : C →+* K) (he : ∀ x, ‖e x‖ = ‖x‖) :
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (e.fieldRange : Set K) := by
  intro s
  by_contra! h
  have := infinite_residueField_of_isAlgClosed (C := C)
  choose l hl using fun a => residue_surjective
    (R := (NormedField.valuation (K := C)).valuationSubring) a
  choose y hy hy1 using fun a => h (e (l a)) ⟨l a, rfl⟩
    (by rw [he]; exact (mem_normValuationSubring_iff _).1 (l a).2)
  obtain ⟨a, b, hab, h1⟩ := Finite.exists_ne_map_eq_of_infinite fun a => (⟨y a, hy a⟩ : s)
  have h2 : y a = y b := congrArg Subtype.val h1
  refine hab ?_
  rw [← hl a, ← hl b, ← sub_eq_zero, ← map_sub, residue_normValuationSubring_eq_zero_iff, ← he]
  have : e ((l a - l b : (NormedField.valuation (K := C)).valuationSubring) : C) =
      (e (l a) - y a) + -(e (l b) - y b) := by
    rw [h2]
    simp
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    (max_lt (hy1 a) (by rw [norm_neg]; exact hy1 b))
end GlobalTheory.DiscEval
