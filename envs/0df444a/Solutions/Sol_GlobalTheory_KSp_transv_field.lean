-- Prove2me | solution 1 for GlobalTheory.KSp.transv_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:59.202083+00:00
-- url     : https://prove2.me/submissions/fc27ad34-8d5c-4265-9f75-16a17710fd65

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertible
import Theorems.Thm_GlobalTheory_KSp_transvRankOne_adm
import Theorems.Thm_GlobalTheory_KSp_transv_step
import Theorems.Thm_GlobalTheory_KSp_transv_iso_update
import Theorems.Thm_GlobalTheory_KSp_skewAdmissibleMatrix_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
variable {k : Type} [Field k] {ν : Type} [Fintype ν] [DecidableEq ν]
namespace GlobalTheory.KSp
theorem _root_.solution (c : k →+* k) (S : Matrix ν ν k) (hSu : IsUnit S.det) (hS : Sᵀ = -S.map c)
    (A C : Matrix ν ν k) (hinj : ∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  suffices H : ∀ m : ℕ, ∀ A : Matrix ν ν k,
      Module.finrank k (LinearMap.ker A.mulVecLin) < m →
      (∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from
    H _ A (Nat.lt_succ_self _) hinj hiso
  intro m
  induction m with
  | zero => intro A h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro A hm hinj hiso
    by_cases hdet : IsUnit A.det
    · exact ⟨0, by simp, by simpa using hdet⟩
    · have hd : A.det = 0 := by simpa [isUnit_iff_ne_zero] using hdet
      obtain ⟨u, hu0, hu⟩ := exists_mulVec_eq_zero_iff.mpr hd
      obtain ⟨j, hker, hne⟩ := transv_step c S hSu A C hinj hiso u hu0 hu
      have hX1 := transvRankOne_adm c S hS j
      have hlt : LinearMap.ker (A + transvRankOne S j * C).mulVecLin <
          LinearMap.ker A.mulVecLin := by
        refine lt_of_le_of_ne ?_ ?_
        · intro w hw
          simp only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢
          exact hker w hw
        · intro heq
          apply hne
          have hmem : u ∈ LinearMap.ker A.mulVecLin := by
            simpa [LinearMap.mem_ker, mulVecLin_apply] using hu
          rw [← heq] at hmem
          rw [LinearMap.mem_ker, mulVecLin_apply] at hmem
          exact hmem
      have hfin := Submodule.finrank_lt_finrank_of_lt hlt
      have hinj' : ∀ w : ν → k, (A + transvRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0 := by
        intro w h1 h2
        apply hinj w _ h2
        rw [add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero] at h1
        exact h1
      obtain ⟨X2, hX2, hdet2⟩ := ih (A + transvRankOne S j * C) (by omega) hinj'
        (transv_iso_update c S A C _ hX1 hiso)
      refine ⟨transvRankOne S j + X2, skewAdmissibleMatrix_add c S _ _ hX1 hX2, ?_⟩
      rwa [Matrix.add_mul, ← add_assoc]
end GlobalTheory.KSp
