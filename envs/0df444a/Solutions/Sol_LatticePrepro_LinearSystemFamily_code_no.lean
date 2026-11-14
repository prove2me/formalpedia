-- Prove2me | solution 1 for LatticePrepro.LinearSystemFamily.code_no
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:00.62075+00:00
-- url     : https://prove2.me/submissions/052c0650-cecb-49b1-9c26-4c2a2cdcaec5

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

/-- The Hamming distance of vectors on a sum type is the sum of the distances of their halves. -/
lemma hammingDist_sum_elim {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (a c : α → γ) (b d : β → γ) :
    hammingDist (Sum.elim a b) (Sum.elim c d) = hammingDist a c + hammingDist b d := by
  simp only [hammingDist, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

end LatticePrepro

namespace LatticePrepro

namespace LinearSystemFamily

variable {F : Type} [Field F] {X : Type}

variable (L : LinearSystemFamily F X)

/-- Number of columns `n = D · b`. -/
lemma card_ι : Fintype.card L.ι = L.numBlocks * L.blockSize := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := L.blk) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp [L.card_fiber, Finset.sum_const, numBlocks]

end LinearSystemFamily

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

lemma LinearSystemFamily.codeTarget_of_not_exists {x : X} (h : ¬ ∃ v, L.IsSolution x v) :
    L.codeTarget x = Sum.elim (0 : L.ι → ZMod p) (1 : L.ι → ZMod p) := by
  simp [LinearSystemFamily.codeTarget, h]

/-- NO instances (equation (38)): every codeword is far from the target. -/
private theorem LinearSystemFamily.code_no {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hx : L.IsNo g x) :
    ∀ c ∈ L.code, g * L.numBlocks < hammingDist (L.codeTarget x) c := by
  intro c hc
  rw [L.mem_code_iff] at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hc_eq : c = Sum.elim (c ∘ Sum.inl) 0 := by
    funext i; rcases i with i | i
    · rfl
    · exact hc2 i
  by_cases hex : ∃ v, L.IsSolution x v
  · rw [L.codeTarget_of_exists hex, hc_eq, hammingDist_sum_elim, hammingDist_self, add_zero,
      hammingDist_comm, hammingDist_eq_hammingNorm]
    apply hx
    have h0 : L.A hex.choose = L.rhs x := hex.choose_spec
    show L.A (-(c ∘ Sum.inl) + hex.choose) = L.rhs x
    rw [map_add, map_neg, h0, hc1, neg_zero, zero_add]
  · rw [L.codeTarget_of_not_exists hex, hc_eq, hammingDist_sum_elim]
    have h1 : hammingDist (1 : L.ι → ZMod p) 0 = Fintype.card L.ι := by
      simp [hammingDist, Finset.card_univ]
    rw [h1, L.card_ι]
    have : g * L.numBlocks < L.numBlocks * L.blockSize := by
      rw [Nat.mul_comm L.numBlocks]; exact Nat.mul_lt_mul_of_pos_right hg hD
    omega

end OfSystem

end LatticePrepro

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)
theorem solution {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hx : L.IsNo g x) :
    ∀ c ∈ L.code, g * L.numBlocks < hammingDist (L.codeTarget x) c :=
  @LatticePrepro.LinearSystemFamily.code_no p _ X L g hg hD x hx
