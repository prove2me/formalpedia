-- Prove2me | solution 1 for GlobalTheory.DenClear.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:57.988668+00:00
-- url     : https://prove2.me/submissions/d1f1c460-887d-4601-b978-02ae6ccc8d24

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulMemLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCommonDenominatorForHermitianLatticeData
import Theorems.Thm_GlobalTheory_IntMulIntegerSmulMemLattice_exists_int_smul_mem_lattice


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
open GlobalTheory GlobalTheory.DenClear
namespace GlobalTheory.DenClear
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : 𝓞 E) • w ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice
  | exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice
  | (apply _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice ..)
end GlobalTheory.DenClear
