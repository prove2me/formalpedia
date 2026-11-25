-- Prove2me | solution 1 for GlobalTheory.SymChain.rowE_mem_symLev_of_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:21:28.42259+00:00
-- url     : https://prove2.me/submissions/282130a2-a01e-4883-a4c2-7c5b879156e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevel
import Theorems.Thm_GlobalTheory_SymChain_conj_embA_lowU
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply
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
open GlobalTheory GlobalTheory.SymChain
namespace GlobalTheory.SymChain
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k, u ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J := by
  intro k _ _ _ _ s κ S t _ _ hP j c H r hc u hu
  have hr : r < S.ρ := by have := S.odd; omega
  let o := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  let d : Fin (c + 1 + 1) → kˣ := fun i => S.ϖ ^ (i.val + 1)
  let C : Matrix (Fin (c + 1 + 1)) (XIx (Fin κ) t j) k := Matrix.of fun l x => if l.val + 1 = r + 1 then u x else 0
  let C' := diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) * C
  have hC' : ∀ l x, C' l x = if l.val = r then (((S.ϖ ^ (r + 1))⁻¹ : kˣ) : k) * u x else 0 := by
    intro l x
    simp only [C', C, d, diagonal_mul, of_apply, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rfl
    · simp
  have hint : ∀ l x, C' l x ∈ 𝒪[k] := by
    intro l x
    rw [hC']
    split_ifs
    · rw [Valuation.mem_integer_iff, map_mul]
      have h0 : 0 < valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by simp [zero_lt_iff]
      rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_one₀ h0]
      exact hu x
    · exact zero_mem _
  have e1 : (typeFrame S.ϖ o).conj ((reGL o).symm (lowU C')) = rowE (c + 1 + 1) (r + 1) u := by
    rw [LatFrame.conj_apply]
    change embA _ (GlobalTheory.SplitFlip.diagGL d) * reGL o ((reGL o).symm (lowU C')) * (embA _ (GlobalTheory.SplitFlip.diagGL d))⁻¹ = _
    rw [MulEquiv.apply_symm_apply]
    exact conj_embA_lowU d C
  show (typeFrame S.ϖ o).conj.symm (rowE (c + 1 + 1) (r + 1) u) ∈ (S.P.iter t S.μ S.tame j).J
  rw [← e1, MulEquiv.symm_apply_apply, hP]
  have hfb : ∀ (M : Matrix (Fin (c + 1 + 1)) (XIx (Fin κ) t j) k), (∀ l x, M l x ∈ 𝒪[k]) →
      ∀ y z, (fromBlocks 1 0 M 1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) y z ∈ 𝒪[k] := by
    intro M hM y z
    rcases y with y | y <;> rcases z with z | z
    · simp only [fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp [zero_mem, one_mem]
    · simp [zero_mem]
    · simpa using hM y z
    · simp only [fromBlocks_apply₂₂, one_apply]; split_ifs <;> simp [zero_mem, one_mem]
  refine ⟨?_, ?_⟩
  · rw [mem_KO, ← map_inv]
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [reGL_symm_val, submatrix_apply]; exact hfb C' hint _ _
    · rw [reGL_symm_val, submatrix_apply]
      exact hfb (-C') (fun l x => by simpa using neg_mem (hint l x)) _ _
  · intro a b hnf
    suffices h : (lowU C').val (o a) (o b) = (1 : Matrix _ _ k) a b by
      rw [reGL_symm_val, submatrix_apply, h, sub_self, map_zero]; exact zero_lt_one
    have h1 : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t j) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k) a b =
        (1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) (o a) (o b) := by
      simp only [one_apply, EmbeddingLike.apply_eq_iff_eq]
    rw [h1]
    change (fromBlocks 1 0 C' 1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) (o a) (o b) = _
    rcases hoa : o a with y | l <;> rcases hob : o b with z | z
    · simp [one_apply]
    · simp [one_apply]
    · rw [fromBlocks_apply₂₁, one_apply, if_neg (by simp), hC']
      split_ifs with hl
      · exfalso
        have ha : a = Sum.inl (Sum.inr ⟨l.val, by omega⟩) :=
          o.injective (by rw [hoa]; exact (standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (by omega) l).symm)
        subst ha
        rcases z with (z | z) | z
        · have hb : b = Sum.inl (Sum.inl z) :=
            o.injective (by rw [hob]; exact (stdOrd_eps (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf (by simp only [FreeIx, FreeTop]; omega)
        · have hb : b = Sum.inl (Sum.inr ⟨c + 1 + 1 + z.val, by omega⟩) :=
            o.injective (by rw [hob]; exact (stdOrd_f (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf (by simp only [FreeIx, FreeTop, Fin.mk_lt_mk]; omega)
        · have hb : b = Sum.inr z :=
            o.injective (by rw [hob]; exact (stdOrd_d (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf trivial
      · rfl
    · simp [one_apply]
end GlobalTheory.SymChain
