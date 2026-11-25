-- Prove2me | solution 1 for GlobalTheory.T.term_invariants_independent_of_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:24.103967+00:00
-- url     : https://prove2.me/submissions/795a6cd9-0263-41a4-8751-5d26da6f15da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Theorems.Thm_GlobalTheory_HL_WitIndep_witness_independence


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ d Λ n n', S.IsTermW d Λ n n' → S.om d Λ = S.psi n * (S.psi' n')⁻¹ ∧ S.M d Λ = S.Mof (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ S.Fr d Λ = S.frameCls (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ (∀ y, S.lev (S.fr d Λ) (S.fr' d Λ) y = S.lev (fun b => n (S.f b)) (fun b => n' (S.f' b)) y) ∧ ‖S.om d Λ‖ = 1 := by
  first | exact @GlobalTheory.HL.WitIndep.witness_independence | exact GlobalTheory.HL.WitIndep.witness_independence | (intros; apply GlobalTheory.HL.WitIndep.witness_independence <;> assumption)
end _root_.GlobalTheory.T
