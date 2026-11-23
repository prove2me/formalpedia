-- Prove2me | solution 1 for GlobalTheory.CardQuotientPow.card_quot_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:31.40521+00:00
-- url     : https://prove2.me/submissions/a842f648-7f0d-4940-b6cb-a88abae1a529

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardQuotientPow
open Module Submodule
namespace GlobalTheory.CardQuotientPow
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by
  have key : ∀ I : Ideal R, Nat.card (R ⧸ I) = I.toAddSubgroup.index := fun I => rfl
  induction k with
  | zero => rw [key]; simp
  | succ k ih =>
    rw [pow_succ (Nat.card (R ⧸ Ideal.span {p})) k, ← ih, key, key, key]
    have hle : (Ideal.span {p ^ (k+1)}).toAddSubgroup ≤ (Ideal.span {p ^ k}).toAddSubgroup := by
      intro x hx
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p (Nat.le_succ k)) hx
    rw [← AddSubgroup.relIndex_mul_index hle, mul_comm]
    congr 1
    let f : R →+ R := AddMonoidHom.mulLeft (p ^ k)
    have hr : f.range = (Ideal.span {p ^ k}).toAddSubgroup := by
      ext x
      simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton', f,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
    have hc : (Ideal.span {p ^ (k+1)}).toAddSubgroup.comap f = (Ideal.span {p}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, f,
        AddMonoidHom.coe_mulLeft]
      rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
    rw [← hr, ← AddSubgroup.index_comap, hc]
end GlobalTheory.CardQuotientPow
