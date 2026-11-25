-- Prove2me | solution 1 for GlobalTheory.CongTrans.exists_solution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:19.599159+00:00
-- url     : https://prove2.me/submissions/a689363f-e9c2-4c04-86e7-2a21ff4c9ec1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Theorems.Thm_GlobalTheory_CongTrans_int_add
import Theorems.Thm_GlobalTheory_CongTrans_int_sub
import Theorems.Thm_GlobalTheory_CongTrans_int_neg
import Theorems.Thm_GlobalTheory_CongTrans_int_smul
import Theorems.Thm_GlobalTheory_CongTrans_int_mul
import Theorems.Thm_GlobalTheory_CongTrans_int_cT
import Theorems.Thm_GlobalTheory_CongTrans_cT_add
import Theorems.Thm_GlobalTheory_CongTrans_cT_sub
import Theorems.Thm_GlobalTheory_CongTrans_cT_smul
import Theorems.Thm_GlobalTheory_CongTrans_cT_mul
import Theorems.Thm_GlobalTheory_CongTrans_cT_cT
import Theorems.Thm_GlobalTheory_CongTrans_exists_fixed
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
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
    {G D : Matrix (Fin m) (Fin m) E} (hG : IsHerm L G) (hGi : IsIntM L G) (hD : IsHerm L D)
    (hDi : IsIntM L D) :
    ∃ Z, IsIntM L Z ∧ Z + cT L Z + algebraMap F E ϖ ^ i • (cT L Z * G * Z) = D := by
  have hp : algebraMap F E ϖ ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  obtain ⟨τ, hτ, hτ1⟩ := (order_facts L ϖ hϖ).1 1
  have hτ2 : L.cj τ = 1 - τ := by
    have : algebraMap F E ((1 : 𝒪[F]) : F) = 1 := by simp
    rw [this] at hτ1
    linear_combination hτ1
  have hcp : ∀ n : ℕ, L.cj (algebraMap F E ϖ ^ n) = algebraMap F E ϖ ^ n := fun n => by
    rw [map_pow, AlgEquiv.commutes]
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨Z, hZ, h⟩ := exists_fixed L hϖ
    (fun Z => τ • (D - algebraMap F E ϖ ^ (1 + i) • (cT L Z * G * Z)))
    (fun Y hY => int_smul L hτ (int_sub L hDi (int_smul L (L.O.pow_mem hp _)
      (int_mul L (int_mul L (int_cT L hY) hGi) hY))))
    (fun n Y W hY hW => ⟨-(τ • algebraMap F E ϖ ^ i • (cT L W * G * Y + cT L Y * G * W
        + algebraMap F E ϖ ^ n • (cT L W * G * W))),
      int_neg L (int_smul L hτ (int_smul L (L.O.pow_mem hp _) (int_add L (int_add L
        (int_mul L (int_mul L (int_cT L hW) hGi) hY) (int_mul L (int_mul L (int_cT L hY) hGi) hW))
        (int_smul L (L.O.pow_mem hp _) (int_mul L (int_mul L (int_cT L hW) hGi) hW))))), by
        simp only [cT_add, cT_smul, hcp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul]
        module⟩)
  refine ⟨Z, hZ, ?_⟩
  have h' := congrArg (cT L) h
  simp only [cT_smul, cT_sub, cT_mul, cT_cT, hcp, hτ2] at h'
  rw [show cT L D = D from hD, show cT L G = G from hG, ← Matrix.mul_assoc] at h'
  set Q := cT L Z * G * Z
  rw [← h', ← h]
  module
end GlobalTheory.CongTrans
