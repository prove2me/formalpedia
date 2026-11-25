-- Prove2me | solution 1 for GlobalTheory.HL.Glue.exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:09.546716+00:00
-- url     : https://prove2.me/submissions/ed7a9397-b53d-4a4c-90d5-d48082c5439d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLattices
import Theorems.Thm_GlobalTheory_NatSmulMem_exists_nat_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
variable {R : Type} [CommRing R] {O : Subring R} {n : ℕ}
namespace GlobalTheory.HL.Glue
theorem _root_.solution (Λ : Submodule O (Fin n → R))
    (hd : ∀ y : R, ∃ m : ℕ, m ≠ 0 ∧ (m : R) * y ∈ O) {x : Fin n → R}
    (hx : x ∈ Submodule.span R (Λ : Set (Fin n → R))) : ∃ m : ℕ, m ≠ 0 ∧ (m : R) • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem ..)
end GlobalTheory.HL.Glue
