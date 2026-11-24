-- Prove2me | solution 1 for GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:45.6202+00:00
-- url     : https://prove2.me/submissions/2f8e00b4-f51a-4b20-9562-5f8bee82a1b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosSemidefQuadraticAdjointPairBound
import Theorems.Thm_GlobalTheory_PosFormAdjoint_int_cauchy_schwarz
import Theorems.Thm_GlobalTheory_PosFormAdjoint_seq_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PosFormAdjoint
namespace GlobalTheory.PosFormAdjoint
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y := by
  intro X _ _ _ h h'
  let T : Module.End ℤ X := h'.toIntLinearMap * h.toIntLinearMap
  have hT : ∀ u, T u = h' (h u) := fun u => rfl
  let p := T.charpoly
  refine ⟨(∑ i ∈ Finset.range p.natDegree, (-(p.coeff i)).natAbs) + 1, ?_⟩
  intro q hq hq0 hqneg hcube hadj y
  let B : X →+ X →+ ℤ := AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v => q (u + v) - q u - q v)
      (fun a b => by
        have := hcube u a b
        rw [← add_assoc]
        linarith))
    (fun a b => by
      ext v
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      have := hcube a b v
      linarith)
  have hB : ∀ u v, B u v = q (u + v) - q u - q v := fun u v => rfl
  have Bsym : ∀ u v, B u v = B v u := by
    intro u v; rw [hB, hB, add_comm]; ring
  have Bdiag : ∀ u, B u u = 2 * q u := by
    intro u
    have := hcube u u (-u)
    simp only [add_neg_cancel_right, add_neg_cancel, hq0, hqneg] at this
    rw [hB]; linarith
  have Badj : ∀ u v, B (h u) v = B u (h' v) := by
    intro u v; rw [hB, hB]; have := hadj u v; linarith
  have BT : ∀ u v, B (T u) v = B u (T v) := by
    intro u v
    rw [hT, hT, Bsym, ← Badj, Bsym, Badj]
  have BTpow : ∀ k u v, B ((T ^ k) u) v = B u ((T ^ k) v) := by
    intro k
    induction k with
    | zero => intro u v; rfl
    | succ k ih =>
      intro u v
      rw [pow_succ', Module.End.mul_apply, BT, ih]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ, ← pow_succ']
  let G : X →+ X →+ ℤ := B.comp (T : X →+ X)
  have hG : ∀ u v, G u v = B (T u) v := fun u v => rfl
  have Gsym : ∀ u v, G u v = G v u := by
    intro u v; rw [hG, hG, BT, Bsym]
  have Gdiag : ∀ u, G u u = 2 * q (h u) := by
    intro u; rw [hG, hT, Bsym, ← Badj, Bdiag]
  have Bpos : ∀ u, 0 ≤ B u u := fun u => by rw [Bdiag]; linarith [hq u]
  have Gpos : ∀ u, 0 ≤ G u u := fun u => by rw [Gdiag]; linarith [hq (h u)]
  let a : ℕ → ℤ := fun k => B ((T ^ k) y) y
  have aB : ∀ i j, a (i + j) = B ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    show B ((T ^ (i + j)) y) y = _
    rw [pow_add, Module.End.mul_apply, BTpow]
    exact Bsym _ _
  have aG : ∀ i j, a (i + j + 1) = G ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    rw [hG, ← Module.End.mul_apply, ← pow_succ', add_right_comm, aB]
  have apos : ∀ k, 0 ≤ a k := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [two_mul, aB]; exact Bpos _
    · rw [two_mul, aG]; exact Gpos _
  have alc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have e1 : a (2 * m + 1) = B ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      have e2 : a (2 * m + 2) = B ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      rw [e1, e2, two_mul, aB]
      exact int_cauchy_schwarz B Bsym Bpos _ _
    · have e1 : a (2 * m + 1 + 1) = G ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      have e2 : a (2 * m + 1 + 2) = G ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      rw [e1, e2, two_mul, aG]
      exact int_cauchy_schwarz G Gsym Gpos _ _
  have hmonic : p.Monic := LinearMap.charpoly_monic T
  have hrec : a p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * a i = 0 := by
    have hCH : (Polynomial.aeval T p) y = 0 := by
      rw [LinearMap.aeval_self_charpoly]; rfl
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at hCH
    have h2 := congrArg (fun x => B x y) hCH
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add,
      map_sum, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.finset_sum_apply,
      AddMonoidHom.smul_apply, smul_eq_mul, map_zero, AddMonoidHom.zero_apply] at h2
    rw [add_comm]; exact h2
  have hb := seq_bound a (fun i => p.coeff i) p.natDegree apos alc hrec
  have a0 : a 0 = 2 * q y := by show B ((T ^ 0) y) y = _; rw [pow_zero]; exact Bdiag y
  have a1 : a 1 = 2 * q (h y) := by
    have := aG 0 0
    simp only [zero_add, pow_zero] at this
    rw [this]; exact Gdiag y
  rw [a0, a1] at hb
  have habs : ∀ i, (-(p.coeff i)).natAbs = (p.coeff i).natAbs := fun i => Int.natAbs_neg _
  simp only [habs]
  linarith
end GlobalTheory.PosFormAdjoint
