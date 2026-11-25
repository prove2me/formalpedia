-- Prove2me | solution 1 for GlobalTheory.LocFlat.DoubleStepProof.rowE_mem_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:59.28153+00:00
-- url     : https://prove2.me/submissions/64143aa3-2d41-44ee-a4dd-2b31251bcb7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
import Theorems.Thm_P2M_GlobalTheory_LocFlat_DoubleStepProof_rowE_inv__be53a7a31087
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_conj_rowE
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_intM_one
import Theorems.Thm_GlobalTheory_StepData_intM_zero
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block
import Theorems.Thm_GlobalTheory_StepData_stdOrd_d
import Theorems.Thm_GlobalTheory_StepData_stdOrd_eps
import Theorems.Thm_GlobalTheory_StepData_stdOrd_f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.DoubleStepProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LocFlat.DoubleStepProof
theorem _root_.solution (hP : S.Pattern t) (j c : ℕ) (H : j + 1 + (c + 1) = s) (r : ℕ) (hc : c = 2 * r)
    (u : XIx (Fin κ) t (j + 1) → k) (hu : u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1))) :
    rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev (j + 1) (c + 1 + 1) (by omega)).J := by
  have hr : r < S.ρ := by have := S.odd; omega
  set ord := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega) with hord
  have hint : ∀ v ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1)),
      IntM (fromBlocks 1 0 (Matrix.of fun (l : Fin (c + 1 + 1)) x => if l.val = r then (((S.ϖ : k) ^ (r + 1))⁻¹ * v x) else 0) 1 :
        Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) := by
    intro v hv
    refine intM_fromBlocks.2 ⟨intM_one, intM_zero, fun l x => ?_, intM_one⟩
    simp only [Matrix.of_apply]
    split_ifs
    · rw [Valuation.mem_integer_iff, map_mul, map_inv₀]
      have h0 : valuation k ((S.ϖ : k) ^ (r + 1)) ≠ 0 := (Valuation.ne_zero_iff _).2 (pow_ne_zero _ (Units.ne_zero _))
      have h1 := hv x
      rw [Units.val_pow_eq_pow_val] at h1
      calc (valuation k ((S.ϖ : k) ^ (r + 1)))⁻¹ * valuation k (v x) ≤
            (valuation k ((S.ϖ : k) ^ (r + 1)))⁻¹ * valuation k ((S.ϖ : k) ^ (r + 1)) := mul_le_mul' le_rfl h1
        _ = 1 := inv_mul_cancel₀ h0
    · exact zero_mem _
  change (typeFrame S.ϖ ord).conj.symm (rowE (c + 1 + 1) (r + 1) u) ∈ (S.P.iter t S.μ S.tame (j + 1)).J
  rw [hP (j + 1)]
  refine ⟨mem_KO.2 ⟨?_, ?_⟩, ?_⟩
  · rw [conj_rowE S t j c H r u]
    exact fun a b => hint u hu _ _
  · rw [← map_inv, rowE_inv', conj_rowE S t j c H r (-u)]
    exact fun a b => hint (-u) (neg_mem hu) _ _
  · intro a b hab
    rw [conj_rowE S t j c H r u]
    suffices h : (fromBlocks 1 0 (Matrix.of fun (l : Fin (c + 1 + 1)) x => if l.val = r then (((S.ϖ : k) ^ (r + 1))⁻¹ * u x) else 0) 1 :
        Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) (ord a) (ord b) =
        (1 : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) (ord a) (ord b) by
      have h1 : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) t (j + 1)) k) a b =
          (1 : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) (ord a) (ord b) := by
        simp only [Matrix.one_apply, ord.injective.eq_iff]
      rw [Matrix.submatrix_apply, h, ← h1, sub_self, map_zero]
      exact zero_lt_one
    rcases hA : ord a with A | A <;> rcases hB : ord b with B | B
    · simp [Matrix.one_apply]
    · simp
    · simp only [fromBlocks_apply₂₁, Matrix.of_apply]
      split_ifs with hAr
      · exfalso
        apply hab
        have ha : a = .inl (.inr ⟨A.val, by omega⟩) :=
          ord.injective (hA.trans (standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) (c + 1 + 1) _ A).symm)
        subst ha
        rcases B with (B | B) | B
        · have hb : b = .inl (.inl B) := ord.injective (hB.trans (stdOrd_eps (Fin κ) t (j + 1) (c + 1 + 1) _ B).symm)
          subst hb
          simp only [FreeIx, FreeTop]
          omega
        · have hb : b = .inl (.inr ⟨c + 1 + 1 + B.val, by omega⟩) :=
            ord.injective (hB.trans (stdOrd_f (Fin κ) t (j + 1) (c + 1 + 1) _ B).symm)
          subst hb
          simp only [FreeIx, FreeTop, Fin.lt_def]
          omega
        · have hb : b = .inr B := ord.injective (hB.trans (stdOrd_d (Fin κ) t (j + 1) (c + 1 + 1) _ B).symm)
          subst hb
          simp only [FreeIx]
      · simp
    · simp [Matrix.one_apply]
end GlobalTheory.LocFlat.DoubleStepProof
