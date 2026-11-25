-- Prove2me | solution 1 for GlobalTheory.HL.FibU.relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:06:34.896259+00:00
-- url     : https://prove2.me/submissions/2ab8e551-78e3-4f25-9e59-21094e265277

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMemOfIsLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBound

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FibU
namespace GlobalTheory.HL.FibU
theorem _root_.solution {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (Λ : Submodule R W)
    (hΛ : Λ.FG) (c : R) [Finite (R ⧸ Ideal.span {c})] (P : AddSubgroup W) (hP : ∀ y ∈ Λ, c • y ∈ P) :
    P.relIndex Λ.toAddSubgroup ≠ 0 := by
  have h1 : Finite (Λ ⧸ (Ideal.span {c} • (⊤ : Submodule R Λ))) :=
    Submodule.finite_quotient_smul _ ((Submodule.fg_top Λ).2 hΛ)
  have h2 : (Ideal.span {c} • (⊤ : Submodule R Λ)).toAddSubgroup.index ≠ 0 :=
    Nat.card_pos (α := Λ ⧸ (Ideal.span {c} • (⊤ : Submodule R Λ))) |>.ne'
  have h3 : (Ideal.span {c} • (⊤ : Submodule R Λ)).toAddSubgroup ≤ P.addSubgroupOf Λ.toAddSubgroup := by
    intro x hx
    rw [Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact hP y y.2
  intro h0
  exact h2 (Nat.eq_zero_of_zero_dvd (h0 ▸ AddSubgroup.index_dvd_of_le h3))
end GlobalTheory.HL.FibU
