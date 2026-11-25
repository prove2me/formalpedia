-- Prove2me | solution 1 for GlobalTheory.MoveFine.relIndex_scl_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:59.701811+00:00
-- url     : https://prove2.me/submissions/a6b49c20-0a71-4e4b-9607-afe9cdebf041

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_mem_scl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
namespace GlobalTheory.MoveFine
theorem _root_.solution {E W : Type} [CommRing E] [AddCommGroup W] [Module E W] (O : Subring E)
    (P : Submodule O W) (hP : P.FG) (I : Ideal O) [Finite (O ⧸ I)] (c : E)
    (hI : ∀ x ∈ I, ∃ y ∈ O, (x : E) = c * y) :
    (scl P.toAddSubgroup c).relIndex P.toAddSubgroup ≠ 0 := by
  haveI : Module.Finite O P := Module.Finite.iff_fg.2 hP
  haveI : Finite (P ⧸ (⊤ : Submodule O P)) := inferInstance
  haveI hf : Finite (P ⧸ I • (⊤ : Submodule O P)) :=
    Submodule.finite_quotient_smul I Module.Finite.fg_top
  have h1 : (I • (⊤ : Submodule O P)).toAddSubgroup.index ≠ 0 :=
    AddSubgroup.index_ne_zero_iff_finite.2 hf
  intro h0
  apply h1
  refine Nat.eq_zero_of_zero_dvd (h0 ▸ AddSubgroup.index_dvd_of_le ?_)
  intro v hv
  refine Submodule.smul_induction_on (p := fun v : P => v ∈ (scl P.toAddSubgroup c).addSubgroupOf P.toAddSubgroup) hv ?_ ?_
  · intro x hx n _
    obtain ⟨y, hy, e⟩ := hI x hx
    refine mem_scl.2 ⟨(⟨y, hy⟩ : O) • (n : W), P.smul_mem _ n.2, ?_⟩
    show (x : E) • (n : W) = c • y • (n : W)
    rw [e, mul_smul]
  · intro x y hx hy
    exact AddSubgroup.add_mem _ hx hy
end GlobalTheory.MoveFine
