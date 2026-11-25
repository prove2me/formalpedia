-- Prove2me | solution 1 for GlobalTheory.HermOrthBasis.le_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:11:07.979997+00:00
-- url     : https://prove2.me/submissions/d4fb11bf-b8b0-47ff-bb47-668753c1578a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_GlobalTheory_HermOrthBasis_coeff_eq_zero
import Theorems.Thm_GlobalTheory_HermOrthBasis_nontrivial_alg
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HermOrthBasis
theorem _root_.solution {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det) : m ≤ n := by
  haveI := nontrivial_alg L
  have hli : LinearIndependent E x := Fintype.linearIndependent_iff.2 fun c hc a =>
    congrFun (coeff_eq_zero L Hm x hx c fun a => by rw [hc]; simp [hf]) a
  simpa using hli.fintype_card_le_finrank
end GlobalTheory.HermOrthBasis
