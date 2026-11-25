-- Prove2me | solution 1 for GlobalTheory.scalar_of_triangular_moves_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:23:51.866663+00:00
-- url     : https://prove2.me/submissions/c057747d-58e4-4e6c-98da-d7392a76a4b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalarOfBorelMovesOpenFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  intro E _ _ _ r X m W hW hne _ hact
  classical
  cases r with
  | zero => exact ⟨0, by ext i; exact i.elim0⟩
  | succ n =>
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : σ ∈ X.Ψ
    · exact ⟨σ, h⟩
    · refine ⟨ComplexEmbedding.conjugate σ, ?_⟩
      by_contra h'
      exact h ((X.cmType σ).2 h')
  obtain ⟨τ0, hτ0⟩ := hτ
  let τ : X.Ψ := ⟨τ0, hτ0⟩
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := (m : Matrix (Fin (n+1)) (Fin (n+1)) E).map τ0
  have key : ∀ y ∈ W, ∀ i j : Fin (n+1),
      (M *ᵥ (fun k => y τ k 0)) i * y τ j 0 = (M *ᵥ (fun k => y τ k 0)) j * y τ i 0 := by
    intro y hy i j
    obtain ⟨b, hb, he⟩ := hact y hy
    have hcol : ∀ a : Fin (n+1), (M *ᵥ (fun k => y τ k 0)) a = y τ a 0 * b τ 0 0 := by
      intro a
      have := congrFun (congrFun (congrFun he τ) a) 0
      simp only [lact, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at this
      have hs : ∑ k, y τ a k * b τ k 0 = y τ a 0 * b τ 0 0 := by
        rw [Finset.sum_eq_single (0 : Fin (n+1))]
        · intro k _ hk
          rw [(hb τ).2 k 0 (Fin.pos_of_ne_zero hk), mul_zero]
        · simp
      rw [hs] at this
      simp only [Matrix.mulVec, dotProduct]
      exact this
    rw [hcol i, hcol j]; ring
  obtain ⟨x0, hx0⟩ := hne
  have hq : ∀ w : Fin (n+1) → ℂ, ∀ i j : Fin (n+1), (M *ᵥ w) i * w j = (M *ᵥ w) j * w i := by
    intro w i j
    let pert : ℂ → Frame X.Ψ (n+1) := fun t σ a c => x0 σ a c + if σ = τ ∧ c = 0 then t * w a else 0
    have hc : Continuous pert := by
      apply continuous_pi; intro σ; apply continuous_pi; intro a; apply continuous_pi; intro c
      by_cases h : σ = τ ∧ c = 0
      · simp only [pert, h, and_self, if_true]; fun_prop
      · simp only [pert, h, if_false]; fun_prop
    have h0 : pert 0 = x0 := by funext σ a c; simp [pert]
    have hO : IsOpen (pert ⁻¹' W) := hW.preimage hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 (by simp [h0, hx0])
    set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht_def
    have htn : t ≠ 0 := by
      rw [ht_def]; exact_mod_cast (by positivity : ε / 2 ≠ 0)
    have hnorm : ‖t‖ < ε := by
      rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have h1 : pert t ∈ W := hball (by simpa using hnorm)
    have h2 : pert (-t) ∈ W := hball (by simpa using hnorm)
    have hcolp : ∀ s : ℂ, (fun k => pert s τ k 0) = (fun k => x0 τ k 0) + s • w := by
      intro s; funext k; simp [pert]
    have e1 := key _ h1 i j
    have e2 := key _ h2 i j
    have e0 := key _ hx0 i j
    have hpt : ∀ s : ℂ, ∀ k, pert s τ k 0 = x0 τ k 0 + s * w k := by
      intro s k; simp [pert]
    rw [hcolp] at e1 e2
    simp only [hpt, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have : t ^ 2 * ((M *ᵥ w) i * w j - (M *ᵥ w) j * w i) = 0 := by
      linear_combination (1/2 : ℂ) * e1 + (1/2 : ℂ) * e2 - e0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) htn
    · exact sub_eq_zero.mp h
  have hoff : ∀ i j : Fin (n+1), i ≠ j → M i j = 0 := by
    intro i j hij
    have := hq (Pi.single j 1) i j
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hij] using this
  have hsv : ∀ j k : Fin (n+1), (M *ᵥ Pi.single j (1:ℂ)) k = M k j := by
    intro j k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdiag : ∀ i j : Fin (n+1), M i i = M j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have := hq (Pi.single i 1 + Pi.single j 1) i j
    have hji : j ≠ i := Ne.symm hij
    rw [Matrix.mulVec_add] at this
    simp only [Pi.add_apply, hsv, Pi.single_apply, hij, hji, if_true, if_false, mul_one, add_zero, zero_add, hoff i j hij, hoff j i hji] at this
    exact this
  refine ⟨(m : Matrix (Fin (n+1)) (Fin (n+1)) E) 0 0, ?_⟩
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    apply τ0.injective
    have := hdiag i 0
    simpa [M] using this
  · apply τ0.injective
    have := hoff i j hij
    simpa [M] using this
end GlobalTheory
