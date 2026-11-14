-- Prove2me | solution 1 for LatticePrepro.blockHad_lift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:02.339497+00:00
-- url     : https://prove2.me/submissions/549e02af-26c1-4666-802f-3bce55495ab9

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

open Finset

variable {p : ℕ} [Fact p.Prime] {M : Type*}

lemma liftZMod_eq_zero_iff (y : M → ZMod p) (i : M) : liftZMod y i = 0 ↔ y i = 0 := by
  unfold liftZMod
  rw [Int.natCast_eq_zero, ZMod.val_eq_zero]

/-- The lift of a binary word is a `{0, 1}`-vector. -/
lemma liftZMod_binary {e : M → ZMod p} (he : IsBinary e) (i : M) :
    liftZMod e i = 0 ∨ liftZMod e i = 1 := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  rcases he i with h | h
  · left; unfold liftZMod; rw [h, ZMod.val_zero]; simp
  · right; unfold liftZMod; rw [h, ZMod.val_one]; simp

end LatticePrepro

namespace LatticePrepro

namespace Hadamard

lemma abs_sgn (a : ZMod 2) : |sgn a| = 1 := by
  unfold sgn; split_ifs <;> simp

variable (k : ℕ)

lemma card_Idx : Fintype.card (Idx k) = 2 ^ k := by
  simp [ZMod.card]

lemma abs_wh (u w : Idx k) : |wh k u w| = 1 := abs_sgn _

section Block

variable {β : Type*}

lemma blockHad_apply (v : β × Idx k → ℤ) (su : β × Idx k) :
    blockHad k v su = ∑ w, wh k su.2 w * v (su.1, w) := by
  simp [blockHad, Matrix.mulVec, dotProduct, whMat]

/-- Entries of the block Hadamard map are bounded by the `ℓ_1` norm of the block. -/
lemma abs_blockHad_le (v : β × Idx k → ℤ) (su : β × Idx k) :
    |blockHad k v su| ≤ ∑ w, |v (su.1, w)| := by
  rw [blockHad_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp [abs_mul, abs_wh]

lemma blockHad_eq_zero_of_block (v : β × Idx k → ℤ) (su : β × Idx k)
    (h : ∀ w, v (su.1, w) = 0) : blockHad k v su = 0 := by
  simp [blockHad_apply, h]

end Block

end Hadamard

end LatticePrepro

namespace LatticePrepro

section HadamardSparse

open Finset

variable {p : ℕ} [Fact p.Prime] {β : Type*} [Fintype β] [DecidableEq β] {k : ℕ}

/-- For a `{0,1}`-vector `ẽ` with at most one nonzero entry per block, `H ẽ` has entries of
absolute value at most `1`, supported on at most `2^k · wt(ẽ)` coordinates. -/
private lemma blockHad_lift_bound {e : β × Hadamard.Idx k → ZMod p} (hb : IsBinary e)
    (h1 : AtMostOnePerBlock Prod.fst e) :
    (∀ su, |Hadamard.blockHad k (liftZMod e) su| ≤ 1) ∧
    (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0).card ≤
      hammingNorm e * 2 ^ k := by
  -- the number of nonzero entries of `e` in block `s`
  have hblk : ∀ s : β, (univ.filter fun w => e (s, w) ≠ 0).card ≤ 1 := by
    intro s
    refine le_trans ?_ (h1 s)
    refine Finset.card_le_card_of_injOn (fun w => (s, w)) ?_ ?_
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_filter] at hw
      rw [Finset.mem_coe]
      simp [blockSupport, hw.2]
    · intro w _ w' _ h
      exact (Prod.mk.inj h).2
  have habs : ∀ i, |liftZMod e i| = if e i ≠ 0 then 1 else 0 := by
    intro i
    rcases liftZMod_binary hb i with h | h
    · rw [h, abs_zero]
      rw [(liftZMod_eq_zero_iff e i).mp h]
      simp
    · rw [h, abs_one]
      have : e i ≠ 0 := fun h0 => by
        rw [(liftZMod_eq_zero_iff e i).mpr h0] at h
        exact zero_ne_one h
      simp [this]
  refine ⟨fun su => ?_, ?_⟩
  · calc |Hadamard.blockHad k (liftZMod e) su| ≤ ∑ w, |liftZMod e (su.1, w)| :=
          Hadamard.abs_blockHad_le k _ su
      _ = ((univ.filter fun w => e (su.1, w) ≠ 0).card : ℤ) := by
          simp_rw [habs]
          rw [Finset.sum_boole]
      _ ≤ 1 := by exact_mod_cast hblk su.1
  · -- the support of `H ẽ` is contained in `{blocks of e that are nonzero} × univ`
    have hsub : (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0) ⊆
        (univ.filter fun s : β => ∃ w, e (s, w) ≠ 0) ×ˢ univ := by
      intro su hsu
      simp only [mem_filter, mem_univ, true_and, mem_product, and_true] at hsu ⊢
      by_contra h
      simp only [not_exists, not_not] at h
      apply hsu
      apply Hadamard.blockHad_eq_zero_of_block
      intro w
      rw [liftZMod_eq_zero_iff]
      exact h w
    have hcard : (univ.filter fun s : β => ∃ w, e (s, w) ≠ 0).card ≤ hammingNorm e := by
      unfold hammingNorm
      calc (univ.filter fun s : β => ∃ w, e (s, w) ≠ 0).card
          ≤ ((univ.filter fun su : β × Hadamard.Idx k => e su ≠ 0).image Prod.fst).card := by
            apply Finset.card_le_card
            intro s hs
            simp only [mem_filter, mem_univ, true_and, mem_image] at hs ⊢
            obtain ⟨w, hw⟩ := hs
            exact ⟨(s, w), hw, rfl⟩
        _ ≤ (univ.filter fun su : β × Hadamard.Idx k => e su ≠ 0).card := Finset.card_image_le
    calc (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0).card
        ≤ ((univ.filter fun s : β => ∃ w, e (s, w) ≠ 0) ×ˢ univ).card := Finset.card_le_card hsub
      _ = (univ.filter fun s : β => ∃ w, e (s, w) ≠ 0).card * 2 ^ k := by
          rw [Finset.card_product, Finset.card_univ, Hadamard.card_Idx]
      _ ≤ hammingNorm e * 2 ^ k := Nat.mul_le_mul_right _ hcard

end HadamardSparse

end LatticePrepro

open LatticePrepro
open Finset
variable {p : ℕ} [Fact p.Prime] {β : Type*} [Fintype β] [DecidableEq β] {k : ℕ}
theorem solution {e : β × Hadamard.Idx k → ZMod p} (hb : IsBinary e)
    (h1 : AtMostOnePerBlock Prod.fst e) :
    (∀ su, |Hadamard.blockHad k (liftZMod e) su| ≤ 1) ∧
    (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0).card ≤
      hammingNorm e * 2 ^ k :=
  @LatticePrepro.blockHad_lift_bound p _ β _ _ k e hb h1
