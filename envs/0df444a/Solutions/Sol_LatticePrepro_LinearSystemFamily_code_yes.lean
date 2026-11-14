-- Prove2me | solution 1 for LatticePrepro.LinearSystemFamily.code_yes
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:27:59.212447+00:00
-- url     : https://prove2.me/submissions/7fafdfd5-0341-4eb6-8658-3b991dc3996f

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

variable {ι β F : Type*}

variable [Fintype ι] [DecidableEq β]

section

variable [Zero F] [DecidableEq F] (blk : ι → β)

/-- The Hamming weight is the sum of the block supports. -/
lemma hammingNorm_eq_sum_blockSupport [Fintype β] (y : ι → F) :
    hammingNorm y = ∑ s, (blockSupport blk y s).card := by
  classical
  unfold hammingNorm blockSupport
  rw [Finset.card_eq_sum_card_fiberwise (f := blk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  ext i
  simp [and_comm]

lemma hammingNorm_le_card_of_atMostOnePerBlock [Fintype β] {y : ι → F}
    (h : AtMostOnePerBlock blk y) : hammingNorm y ≤ Fintype.card β := by
  rw [hammingNorm_eq_sum_blockSupport blk y]
  calc ∑ s, (blockSupport blk y s).card ≤ ∑ _s : β, 1 := Finset.sum_le_sum fun s _ => h s
    _ = Fintype.card β := by simp

end

end LatticePrepro

namespace LatticePrepro

/-- The Hamming weight of a vector on a sum type is the sum of the weights of its halves. -/
lemma hammingNorm_sum_elim {α β γ : Type*} [Fintype α] [Fintype β] [Zero γ] [DecidableEq γ]
    (a : α → γ) (b : β → γ) : hammingNorm (Sum.elim a b) = hammingNorm a + hammingNorm b := by
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

end LatticePrepro

namespace LatticePrepro

section OfSystem

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- Membership in the code `ker A × {0}`. -/
lemma LinearSystemFamily.mem_code_iff (w : L.ι ⊕ L.ι → ZMod p) :
    w ∈ L.code ↔ L.A (w ∘ Sum.inl) = 0 ∧ ∀ i, w (Sum.inr i) = 0 := by
  simp [LinearSystemFamily.code, LinearMap.mem_ker, funext_iff]
  exact fun _ => Iff.rfl

lemma LinearSystemFamily.codeTarget_of_exists {x : X} (h : ∃ v, L.IsSolution x v) :
    L.codeTarget x = Sum.elim h.choose 0 := by
  simp [LinearSystemFamily.codeTarget, h]

lemma LinearSystemFamily.card_blockSupport_codeBlk_inl (v w : L.ι → ZMod p) (t : L.β) :
    (blockSupport L.codeBlk (Sum.elim v w) (Sum.inl t)).card = (blockSupport L.blk v t).card := by
  unfold blockSupport
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, reduceCtorEq, false_and, ite_false, Finset.sum_const_zero, add_zero]

lemma LinearSystemFamily.card_blockSupport_codeBlk_inr (v w : L.ι → ZMod p) (t : L.β) :
    (blockSupport L.codeBlk (Sum.elim v w) (Sum.inr t)).card = (blockSupport L.blk w t).card := by
  unfold blockSupport
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Sum.inr.injEq, reduceCtorEq, false_and, ite_false, Finset.sum_const_zero, zero_add]

/-- YES instances (equation (38)): a binary block-sparse error vector of weight `≤ D`. -/
private theorem LinearSystemFamily.code_yes {x : X} (hx : L.IsYes x) :
    ∃ e : L.ι ⊕ L.ι → ZMod p, IsBinary e ∧ AtMostOnePerBlock L.codeBlk e ∧
      hammingNorm e ≤ L.numBlocks ∧ L.codeTarget x - e ∈ L.code := by
  obtain ⟨v, hv, hb, ho⟩ := hx
  have hex : ∃ v, L.IsSolution x v := ⟨v, hv⟩
  refine ⟨Sum.elim v 0, ?_, ?_, ?_, ?_⟩
  · rintro (i | i)
    · exact hb i
    · exact Or.inl rfl
  · rintro (t | t)
    · rw [L.card_blockSupport_codeBlk_inl]; exact ho t
    · rw [L.card_blockSupport_codeBlk_inr]
      simp [blockSupport]
  · rw [hammingNorm_sum_elim, hammingNorm_zero, add_zero]
    exact hammingNorm_le_card_of_atMostOnePerBlock L.blk ho
  · rw [L.codeTarget_of_exists hex, L.mem_code_iff]
    have h0 : L.A hex.choose = L.rhs x := hex.choose_spec
    refine ⟨?_, fun i => by simp⟩
    have : (Sum.elim hex.choose 0 - Sum.elim v 0 : L.ι ⊕ L.ι → ZMod p) ∘ Sum.inl =
        hex.choose - v := by
      funext i; simp
    rw [this, map_sub, h0, hv, sub_self]

end OfSystem

end LatticePrepro

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)
theorem solution {x : X} (hx : L.IsYes x) :
    ∃ e : L.ι ⊕ L.ι → ZMod p, IsBinary e ∧ AtMostOnePerBlock L.codeBlk e ∧
      hammingNorm e ≤ L.numBlocks ∧ L.codeTarget x - e ∈ L.code :=
  @LatticePrepro.LinearSystemFamily.code_yes p _ X L x hx
