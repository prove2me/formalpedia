-- Prove2me | solution 1 for GlobalTheory.CongTrans.exists_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:14.115099+00:00
-- url     : https://prove2.me/submissions/e33d0d50-6bbd-42dd-8283-dc54ac38ee65

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Theorems.Thm_GlobalTheory_CongTrans_int_add
import Theorems.Thm_GlobalTheory_CongTrans_int_sub
import Theorems.Thm_GlobalTheory_CongTrans_int_smul
import Theorems.Thm_GlobalTheory_CongTrans_series_ord
import Theorems.Thm_GlobalTheory_CongTrans_eq_zero_ord
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
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m : ℕ}
    (T : Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E)
    (h0 : ∀ Y, IsIntM L Y → IsIntM L (T Y))
    (hT : ∀ (n : ℕ) Y W, IsIntM L Y → IsIntM L W → ∃ W', IsIntM L W' ∧
      T (Y + algebraMap F E ϖ ^ n • W) = T Y + algebraMap F E ϖ ^ (n + 1) • W') :
    ∃ Z, IsIntM L Z ∧ T Z = Z := by
  have hp : algebraMap F E ϖ ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  set p := algebraMap F E ϖ with hpdef
  let f : ℕ → Matrix (Fin m) (Fin m) E := fun n => T^[n] 0
  have hf : ∀ n, f (n + 1) = T (f n) := fun n => Function.iterate_succ_apply' T n 0
  have hfi : ∀ n, IsIntM L (f n) := by
    intro n
    induction n with
    | zero => exact fun _ _ => L.O.zero_mem
    | succ n ih => rw [hf]; exact h0 _ ih
  have hW : ∀ n, ∃ W, IsIntM L W ∧ f (n + 1) = f n + p ^ n • W := by
    intro n
    induction n with
    | zero => exact ⟨f 1 - f 0, int_sub L (hfi _) (hfi _), by simp⟩
    | succ n ih =>
      obtain ⟨W, hW, h⟩ := ih
      obtain ⟨W', hW', h'⟩ := hT n (f n) W (hfi n) hW
      exact ⟨W', hW', by rw [hf (n + 1), h, h', ← hf, h]⟩
  choose W hWi hW using hW
  have hsum : ∀ n a b, f n a b = ∑ k ∈ Finset.range n, p ^ k * W k a b := by
    intro n a b
    induction n with
    | zero => simp [f]
    | succ n ih => rw [hW, Finset.sum_range_succ, ← ih]; simp
  choose Z hZ using fun a b => series_ord L hϖ (fun k => W k a b) (fun k => hWi k a b)
  have hZ' : ∀ n, ∃ V, IsIntM L V ∧ Matrix.of Z = f n + p ^ n • V := by
    intro n
    choose V hV hV' using fun a b => hZ a b n
    refine ⟨Matrix.of V, hV, ?_⟩
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [hsum]; exact hV' a b
  refine ⟨Matrix.of Z, ?_, ?_⟩
  · obtain ⟨V, hV, h⟩ := hZ' 0
    rw [h]
    exact int_add L (hfi _) (int_smul L (L.O.pow_mem hp _) hV)
  · rw [← sub_eq_zero]
    ext a b
    refine eq_zero_ord L hϖ _ fun n => ?_
    obtain ⟨V, hV, h⟩ := hZ' n
    obtain ⟨V', hV', h'⟩ := hZ' (n + 1)
    obtain ⟨U, hU, hU'⟩ := hT n (f n) V (hfi n) hV
    refine ⟨p * (U a b - V' a b), L.O.mul_mem hp (L.O.sub_mem (hU a b) (hV' a b)), ?_⟩
    rw [← h, ← hf] at hU'
    rw [hU', h']
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
end GlobalTheory.CongTrans
