-- Prove2me | solution 1 for GlobalTheory.SymChain.ExchangeCol.phi_add_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:06.750863+00:00
-- url     : https://prove2.me/submissions/8f088266-0366-467d-a346-c1ca4dc49691

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixBlockColumnVanishingStep
import Theorems.Thm_GlobalTheory_SymChain_ExchangeCol_coords_typeFrame_apply
import Theorems.Thm_GlobalTheory_SymChain_ExchangeCol_coords_add
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_add
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.ExchangeCol
namespace GlobalTheory.SymChain.ExchangeCol
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t)
    (j c : ℕ) (H : j + c = s) (q : Fin c) (hρ : q.val + 1 ≤ S.ρ) (hc : q.val + 2 ≤ c)
    (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k)
    (hx : ∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) (w : XIx (Fin κ) t (j + 1) → k) :
    (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) =
      if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by
  have H1 : j + 1 + c = s + 1 := by omega
  have H2 : j + (c + 1) = s + 1 := by omega
  have hPhi : ∀ z, (S.T t).Phi j c H z = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ (stdOrd (Fin κ) t (j + 1) c H1)).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) t j (c + 1) H2)) z).submatrix (ixSucc _ t j) id) := fun _ => rfl
  split_ifs with hw
  · rw [hPhi, hPhi, coords_add, Matrix.submatrix_add, Pi.add_apply, Pi.add_apply]
    refine (S.P.iter t S.μ S.tame j).Phi_add (S.tame _) _ fun a b => ?_
    rw [submatrix_apply, coords_typeFrame_apply, of_apply]
    split_ifs with hb
    · rw [hb]
      rcases stdOrd (Fin κ) t (j + 1) c H1 (ixSucc _ t j a) with r | r
      · simpa [mul_comm] using hw r
      · simp
    · simp
  · by_contra h
    rw [← Ne, hPhi, TypeDatum.Phi_ne_zero_iff] at h
    obtain ⟨⟨g, hg, e⟩, hb⟩ := h
    refine hw fun r => ?_
    obtain ⟨a, ha⟩ := ((ixSucc _ t j).trans (stdOrd (Fin κ) t (j + 1) c H1)).surjective (.inl r)
    simp only [Equiv.trans_apply] at ha
    have hq : q.succ.val < s + 1 := by have := q.succ.2; omega
    have hcol : stdOrd (Fin κ) t j (c + 1) H2 (.inl (.inr ⟨q.succ.val, hq⟩)) = .inr q.succ :=
      standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1) H2 q.succ
    have key : (((typeFrame S.ϖ (stdOrd (Fin κ) t (j + 1) c H1)).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) t j (c + 1) H2))
        (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0)).submatrix (ixSucc _ t j) id)
        a (.inl (.inr ⟨q.succ.val, hq⟩)) = ((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r := by
      rw [submatrix_apply, coords_typeFrame_apply, id, ha, hcol]
      simp [hx, mul_comm]
    rw [← key]
    rcases a with a | a
    · have hne : ¬ FreeIx S.ρ a (.inl (.inr ⟨q.succ.val, hq⟩)) ∧ a ≠ .inl (.inr ⟨q.succ.val, hq⟩) := by
        rcases a with (a | a) | a
        · simp only [FreeIx, FreeTop, Fin.val_succ]
          exact ⟨by omega, by simp⟩
        · have hac : c ≤ a.val := by
            by_contra hlt
            have := standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) c H1 ⟨a.val, by omega⟩
            exact Sum.inr_ne_inl (this.symm.trans ha)
          simp only [FreeIx, FreeTop, Fin.lt_def, Fin.val_succ, ne_eq, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff]
          omega
        · simp [FreeIx]
      have := ((hP j g).1 hg).2 a _ hne.1
      rw [e, Matrix.one_apply_ne hne.2, sub_zero] at this
      exact this
    · exact hb a _
end GlobalTheory.SymChain.ExchangeCol
