-- Prove2me | solution 1 for GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:06.024368+00:00
-- url     : https://prove2.me/submissions/34df909c-1436-4b16-81ea-eff1ef23e9e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSubquotSmIndCongr
import Theorems.Thm_GlobalTheory_LGrp_SatakeCompare_isSubquot_ps_iff
import Theorems.Thm_GlobalTheory_LGrp_isSpherical_iff
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_isSmooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel
open scoped NNReal
open GlobalTheory GlobalTheory.LGrp GlobalTheory.LGrp.SatakeCompare
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
open MeasureTheory ValuativeRel
open scoped NNReal
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
namespace GlobalTheory.LGrp.SatakeCompare
namespace _root_.GlobalTheory.LGrp.SatakeCompare
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n V : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (S : Multiset ℂˣ), _root_.GlobalTheory.LGrp.HasSatakeGL π S ↔
      ∃ α : n → ℂˣ, Finset.univ.val.map α = S ∧ _root_.GlobalTheory.SmGL.HasSatake π α := by
  intro k _ _ _ _ n V _ _ _ _ _ π S
  unfold _root_.GlobalTheory.LGrp.HasSatakeGL _root_.GlobalTheory.LGrp.InUPSGL _root_.GlobalTheory.SmGL.HasSatake
    _root_.GlobalTheory.SmGL.IsSpherical _root_.GlobalTheory.LGrp.IsIrrSmooth
  rw [_root_.GlobalTheory.LGrp.isSpherical_iff]
  constructor
  · rintro ⟨⟨α, hα, ⟨-, hirr⟩, hsub⟩, hsph⟩
    exact ⟨α, hα, hirr, hsph, (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).1 hsub⟩
  · rintro ⟨α, hα, hirr, hsph, hsub⟩
    have hsub' := (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).2 hsub
    refine ⟨⟨α, hα, ⟨?_, hirr⟩, hsub'⟩, hsph⟩
    refine _root_.GlobalTheory.SmGL.IsSubquotient.isSmooth hsub' ?_
    unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd
    exact _root_.GlobalTheory.LGrp.LeviDatum.nInd_isSmooth _ _
end _root_.GlobalTheory.LGrp.SatakeCompare
end GlobalTheory.LGrp.SatakeCompare
