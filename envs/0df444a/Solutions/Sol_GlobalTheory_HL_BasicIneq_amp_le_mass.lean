-- Prove2me | solution 1 for GlobalTheory.HL.BasicIneq.amp_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:26.178816+00:00
-- url     : https://prove2.me/submissions/397219c3-4878-4f48-8148-a8cfd485955c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasicInequality
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_WitIndep_witness_independence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BasicIneq
namespace GlobalTheory.HL.BasicIneq
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (d : S.Datum) (P : Submodule L.O S.V → Prop) :
    ENNReal.ofReal (‖S.amp d P‖) ≤ S.mass d P := by
  rw [ofReal_norm_eq_enorm]
  unfold Frames.amp Frames.mass
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun o => ?_)
  split_ifs with h
  · obtain ⟨p, hp⟩ := h.1
    have h1 : ‖S.om d o.out‖ = 1 := (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have h2 : 0 ≤ S.mu o.out := by
      unfold Frames.mu invVol
      positivity
    rw [← ofReal_norm_eq_enorm, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_of_nonneg h2]
  · simp
end GlobalTheory.HL.BasicIneq
