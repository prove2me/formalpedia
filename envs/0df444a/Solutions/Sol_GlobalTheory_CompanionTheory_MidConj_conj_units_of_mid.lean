-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:10:48.580006+00:00
-- url     : https://prove2.me/submissions/d93a7036-c734-4799-be9a-b2d7f2d30e1f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_AdaptedFrameOrthogonalSubspace
import Theorems.Thm_GlobalTheory_CompanionTheory_MidConj_mul_single_one_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MidConj
namespace GlobalTheory.CompanionTheory.MidConj
theorem _root_.solution (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P.det)
    (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ)
    (hJJ : Jp * J = 1) (hBB : B * Bi = 1)
    (hJ : ∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j)
    (hout : ∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0)
    (p q : Fin n') :
    J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  let Pm : Matrix (Fin n) (Fin n') ℂ := fun i s => P i ⟨a + s.val, by omega⟩
  have hJm : J = Pm * B := by
    ext i j
    rw [hJ i j]
    rfl
  have hmid : Jp * Pm = Bi := by
    calc Jp * Pm = Jp * Pm * (B * Bi) := by rw [hBB, Matrix.mul_one]
      _ = (Jp * J) * Bi := by rw [hJm]; simp only [Matrix.mul_assoc]
      _ = Bi := by rw [hJJ, Matrix.one_mul]
  have hN_mid : ∀ (q : Fin n') (s : Fin n'), (Jp * P) q ⟨a + s.val, by omega⟩ = Bi q s := by
    intro q s
    calc (Jp * P) q ⟨a + s.val, by omega⟩ = (Jp * Pm) q s := rfl
      _ = Bi q s := by rw [hmid]
  have hN_out : ∀ (q : Fin n') (b : Fin n), (b.val < a ∨ n ≤ b.val + a) → (Jp * P) q b = 0 := by
    intro q b hb
    have h := congrFun (hout b hb) q
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  have hJp : ∀ (q : Fin n') (k : Fin n),
      Jp q k = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k := by
    intro q k
    calc Jp q k = ((Jp * P) * P⁻¹) q k := by rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = ∑ b : Fin n, (Jp * P) q b * P⁻¹ b k := by rw [Matrix.mul_apply]
      _ = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k := by
        symm
        refine Fintype.sum_of_injective (fun u : Fin n' => (⟨a + u.val, by omega⟩ : Fin n)) ?_ _ _ ?_ ?_
        · intro u v huv
          simp only [Fin.mk.injEq] at huv
          exact Fin.ext (by omega)
        · intro b hb
          have hb' : b.val < a ∨ n ≤ b.val + a := by
            by_contra hc
            simp only [not_or, not_lt] at hc
            exact hb (Set.mem_range.mpr ⟨⟨b.val - a, by omega⟩, Fin.ext (show a + (b.val - a) = b.val by omega)⟩)
          rw [hN_out q b hb', zero_mul]
        · intro u
          rw [hN_mid q u]
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_single_one_mul_apply]
  rw [hJ i p, hJp q k, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun u _ => ?_))
  ring
end GlobalTheory.CompanionTheory.MidConj
