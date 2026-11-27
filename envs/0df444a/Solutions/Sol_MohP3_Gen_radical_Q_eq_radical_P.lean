-- Prove2me | solution 1 for MohP3.Gen.radical_Q_eq_radical_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:31.647436+00:00
-- url     : https://prove2.me/submissions/ce0906ff-d9f2-4921-a9e7-248eab4c1b20

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
public import Theorems.Thm_MohP3_Gen_Q_le_P
public import Theorems.Thm_MohP3_Gen_P_sq_le_Q

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
variable [Algebra ℚ A]
namespace MohP3.Gen
theorem _root_.solution : (Q x y z).radical = (P x y z).radical := by
  refine le_antisymm (Ideal.radical_mono (Q_le_P x y z)) ?_
  intro a ha
  rw [Ideal.mem_radical_iff] at ha ⊢
  obtain ⟨n, hn⟩ := ha
  exact ⟨n*2, by
    rw [pow_mul]
    exact P_sq_le_Q x y z (Ideal.pow_mem_pow hn 2)⟩
end MohP3.Gen
