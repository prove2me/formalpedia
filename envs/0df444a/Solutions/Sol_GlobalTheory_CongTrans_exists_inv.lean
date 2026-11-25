-- Prove2me | solution 1 for GlobalTheory.CongTrans.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:15.316807+00:00
-- url     : https://prove2.me/submissions/588f44a8-7eb3-48d2-8939-bbfc7b901ebe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Theorems.Thm_GlobalTheory_CongTrans_int_sub
import Theorems.Thm_GlobalTheory_CongTrans_int_neg
import Theorems.Thm_GlobalTheory_CongTrans_int_smul
import Theorems.Thm_GlobalTheory_CongTrans_int_mul
import Theorems.Thm_GlobalTheory_CongTrans_int_one
import Theorems.Thm_GlobalTheory_CongTrans_mem_congK_iff
import Theorems.Thm_GlobalTheory_CongTrans_exists_fixed
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
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
open GlobalTheory GlobalTheory.CongTrans
open GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
variable [CharZero F] (L : LocE F E)
namespace GlobalTheory.CongTrans
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m i : ℕ} (hi : 1 ≤ i)
    {A : Matrix (Fin m) (Fin m) E} (hA : A ∈ congK L ϖ m i) :
    ∃ B, IsIntM L B ∧ A * B = 1 := by
  have hp : algebraMap F E ϖ ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  obtain ⟨N, hN, rfl⟩ := (mem_congK_iff L ϖ i A).1 hA
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨B, hB, h⟩ := exists_fixed L hϖ (fun B => 1 - algebraMap F E ϖ ^ (1 + i) • (N * B))
    (fun Y hY => int_sub L (int_one L) (int_smul L (L.O.pow_mem hp _) (int_mul L hN hY)))
    (fun n Y W hY hW => ⟨-(algebraMap F E ϖ ^ i • (N * W)),
      int_neg L (int_smul L (L.O.pow_mem hp _) (int_mul L hN hW)), by
        simp only [Matrix.mul_add, Matrix.mul_smul]
        module⟩)
  refine ⟨B, hB, ?_⟩
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  exact eq_sub_iff_add_eq.1 h.symm
end GlobalTheory.CongTrans
