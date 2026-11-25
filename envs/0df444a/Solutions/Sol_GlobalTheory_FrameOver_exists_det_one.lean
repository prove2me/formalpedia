-- Prove2me | solution 1 for GlobalTheory.FrameOver.exists_det_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:15:07.279438+00:00
-- url     : https://prove2.me/submissions/1ee1ed95-631a-439f-a940-b877b3df801d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameOver
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {r k : ℕ}
    (S : Frames L r k) {C : Set S.FrP} (hC : S.IsCls C) {p : S.FrP} (hp : p ∈ C) :
    ∃ U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, U.det = 1 ∧ U'.det = 1 ∧
      (∀ j, p.1 j = ∑ i, U i j • S.f i) ∧ ∀ j, p.2 j = ∑ i, U' i j • S.f' i := by
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  obtain ⟨A, A', -, -, h0, h1, -, hA, hA'⟩ := hp
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := (GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).1 n hn
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := (GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).2.1 n' hn'
  have hd : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, j < i → B i j = 0) →
      (∀ i, B i i = 1) → B.det = 1 := fun B b0 b1 => by
    rw [Matrix.det_of_upperTriangular (fun i j h => b0 i j h)]
    simp [b1]
  refine ⟨s * A, s' * A', ?_, ?_, fun j => ?_, fun j => ?_⟩
  · rw [Matrix.det_mul, hd s hs0 hs1, hd A (fun i j h => (h0 i j h).1) (fun i => (h1 i).1), one_mul]
  · rw [Matrix.det_mul, hd s' hs0' hs1', hd A' (fun i j h => (h0 i j h).2) (fun i => (h1 i).2),
      one_mul]
  · simp only [hA, hs, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · simp only [hA', hs', Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
end GlobalTheory.FrameOver
