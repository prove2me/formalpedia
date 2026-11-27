-- Prove2me | solution 1 for GlobalTheory.eq_mul_prod_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:58.495488+00:00
-- url     : https://prove2.me/submissions/f091721f-6661-4424-b837-ff49de1ae902

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_leadMinor_diagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_BiInvariant_eq_mul_prod
import Theorems.Thm_GlobalTheory_UnipotentInvariant_setBlock_apply
import Theorems.Thm_GlobalTheory_UnipotentInvariant_setBlock_of_not
import Theorems.Thm_P2M_GlobalTheory_UnipotentInvariant_eval_bind___d799cbbaf6da
import Theorems.Thm_GlobalTheory_UnipotentInvariant_biInvariant_eval
import Theorems.Thm_GlobalTheory_UnipotentInvariant_eval_setBlock_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open UnipotentInvariant
namespace GlobalTheory
theorem _root_.solution {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p : ℕ} (z : Fin p × Fin p → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) (c : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = ∑ i ∈ Finset.Ici a, c i)
    (hr : ∀ a b : Fin p, a < b → ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (hc : ∀ k l : Fin p, k < l → ∀ t : K, bind₁ (fun s => X s + ∑ a, if s = z (a, l) then C t * X (z (a, k)) else 0) P = P) :
    ∃ Q : MvPolynomial σ K, (∀ w, z w ∉ Q.vars) ∧
      P = Q * ∏ i : Fin p, (Matrix.of fun a b : Fin (i.val + 1) => (X (z (Fin.castLE i.isLt a, Fin.castLE i.isLt b)) : MvPolynomial σ K)).det ^ c i := by
  let g : σ → MvPolynomial σ K :=
    Function.extend z (fun w => C ((1 : Matrix (Fin p) (Fin p) K) w.1 w.2)) X
  let Δ : Fin p → MvPolynomial σ K := fun i => (Matrix.of fun a b : Fin (i.val + 1) =>
    (X (z (Fin.castLE i.isLt a, Fin.castLE i.isLt b)) : MvPolynomial σ K)).det
  have hΔ : ∀ (x : σ → K) i, eval x (Δ i) = leadMinor i (Matrix.of fun a b => x (z (a, b))) := by
    intro x i
    simp only [Δ, leadMinor]
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp
  have hg : ∀ x : σ → K, eval x (bind₁ g P) = eval (setBlock z x 1) P := by
    intro x
    rw [eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨w, rfl⟩ := hs
      simp [g, setBlock_apply hz, hz.extend_apply]
    · simp [g, setBlock_of_not _ _ hs, Function.extend_apply' _ _ _ hs]
  refine ⟨bind₁ g P, ?_, ?_⟩
  · intro w hw
    obtain ⟨s, -, hs'⟩ := mem_vars_bind₁ g P hw
    by_cases hs : ∃ w, z w = s
    · obtain ⟨w', rfl⟩ := hs
      simp [g, hz.extend_apply] at hs'
    · simp only [g, Function.extend_apply' _ _ _ hs, vars_X, Finset.mem_singleton] at hs'
      exact hs ⟨w, hs'⟩
  · have hne : ∏ i, Δ i ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ h => ?_
      have := hΔ (setBlock z 0 1) i
      rw [h, map_zero] at this
      have h1 : (Matrix.of fun a b => setBlock z (0 : σ → K) 1 (z (a, b))) = diagonal fun _ => 1 := by
        ext a b
        simp [setBlock_apply hz]
      rw [h1, leadMinor_diagonal] at this
      simp at this
    apply mul_left_cancel₀ hne
    apply MvPolynomial.funext
    intro x
    change eval x (_ * P) = eval x (_ * (_ * ∏ i, Δ i ^ c i))
    simp only [map_mul, map_prod, map_pow, hΔ, hg]
    by_cases h : ∀ i, leadMinor i (Matrix.of fun a b => x (z (a, b))) ≠ 0
    · congr 1
      have hx : setBlock z x (Matrix.of fun a b => x (z (a, b))) = x := by
        funext s
        by_cases hs : ∃ w, z w = s
        · obtain ⟨w, rfl⟩ := hs
          simp [setBlock_apply hz]
        · exact setBlock_of_not _ _ hs
      have := (biInvariant_eval hz P hr hc x).eq_mul_prod c
        (eval_setBlock_diagonal hz P _ hrow x) _ h
      simpa only [hx] using this
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul, zero_mul]
end GlobalTheory
