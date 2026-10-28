-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_support_sum_eq_mulVec
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:21:03.737749+00:00
-- url     : https://prove2.me/submissions/52077d0b-ff52-4895-9aae-137f07498221

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

namespace A3S47MD

/-- The correct identity: the matrix-vector product uses `entry r`, not `entry (j • r)`. -/
lemma mulVec_eq {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hcols : ∀ e ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = e)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
      ((InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.coeff (InterpolationMatrix.exponentVector c.1))) rho =
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry r
          (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) := by
  classical
  set f : (Fin (m + 1) →₀ ℕ) → ℂ := fun e => P.coeff e * InterpolationMatrix.entry r
          (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) with hf
  set g : InterpolationMatrix.Column w0 w H → (Fin (m + 1) →₀ ℕ) :=
    fun c => InterpolationMatrix.exponentVector c.1 with hg
  have hgv : ∀ c i, g c i = c.1 i := by
    intro c i; simp [g, InterpolationMatrix.exponentVector]
  have hginj : Function.Injective g := by
    intro c d h
    apply Subtype.ext; funext i
    rw [← hgv, ← hgv, h]
  rw [Matrix.mulVecLin_apply]
  show ∑ c, _ * _ = _
  have hR : ∀ c : InterpolationMatrix.Column w0 w H,
      InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T rho c *
        P.coeff (InterpolationMatrix.exponentVector c.1) = f (g c) := by
    intro c
    have e1 : InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T rho c =
        InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ) (c.1 0) (fun i => c.1 i.succ) := rfl
    have e2 : f (g c) = P.coeff (g c) * InterpolationMatrix.entry r
          (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (c.1 0) (fun i => c.1 i.succ) := by
      simp only [f, hgv]
    rw [e1, e2, mul_comm]
  rw [Finset.sum_congr rfl (fun c _ => hR c)]
  rw [← Finset.sum_image (f := f) (fun c _ d _ h => hginj h)]
  symm
  apply Finset.sum_subset
  · intro e he
    obtain ⟨c, hc⟩ := hcols e he
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩
  · intro e _ he
    simp only [f, MvPolynomial.notMem_support_iff.mp he, zero_mul]

lemma entry_eval (r : Fin 1 → ℂ) (j : ℕ) :
    InterpolationMatrix.entry r (fun _ => InterpolationMatrix.truncatedLog 0) j 0 (fun _ => 0)
      0 (fun _ => 1) = (j : ℂ) * r 0 := by
  unfold InterpolationMatrix.entry InterpolationMatrix.monomialImage
  have h0 : InterpolationMatrix.exponentVector (fun _ : Fin 1 => (0 : ℕ)) = 0 := by
    ext i; simp [InterpolationMatrix.exponentVector]
  simp [h0, InterpolationMatrix.truncatedLog, MvPolynomial.coeff_X']
  rw [show ((j : MvPolynomial (Fin 1) (Polynomial ℂ))) * MvPolynomial.C (Polynomial.C (r 0)) =
    MvPolynomial.C (Polynomial.C ((j : ℂ) * r 0)) by simp, MvPolynomial.coeff_C]
  simp

end A3S47MD

open A3S47MD in
theorem solution : ¬ (∀
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hcols : ∀ e ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = e)
    (rho : InterpolationMatrix.Row K v0 theta w H),
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          (fun i => (rho.1.val : Complex) * r i)
          (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) =
      ((InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.coeff (InterpolationMatrix.exponentVector c.1))) rho) := by
  intro h
  classical
  set e : Fin 2 →₀ ℕ := Finsupp.single 1 1 with he
  set P : MvPolynomial (Fin 2) ℂ := MvPolynomial.monomial e 1 with hP
  have hsupp : P.support = {e} := MvPolynomial.support_monomial.trans (by simp)
  have hcw : ∀ i, InterpolationMatrix.columnWeights 1 (fun _ : Fin 1 => (1 : ℝ)) i = 1 := by
    intro i; exact Fin.cases rfl (fun _ => rfl) i
  have hrw : ∀ i, InterpolationMatrix.rowWeights 1 1 (fun _ : Fin 1 => (1 : ℝ)) i = 1 := by
    intro i; refine Fin.cases rfl (fun _ => ?_) i; simp [InterpolationMatrix.rowWeights]
  have hcol : (fun i : Fin 2 => e i) ∈ realWeightedSimplex
      (InterpolationMatrix.columnWeights 1 (fun _ : Fin 1 => (1 : ℝ))) 1 := by
    simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [e, hcw]
    · simp [Fin.sum_univ_two, e, hcw]
  have hrow : (fun _ : Fin 2 => (0 : ℕ)) ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights 1 1 (fun _ : Fin 1 => (1 : ℝ))) 1 := by
    simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨⟨fun i => by simp [hrw], by simp⟩, by simp⟩
  let rho : InterpolationMatrix.Row 3 1 1 (fun _ : Fin 1 => (1 : ℝ)) 1 :=
    (⟨2, by norm_num⟩, ⟨_, hrow⟩)
  have hcols : ∀ e' ∈ P.support, ∃ c : InterpolationMatrix.Column 1 (fun _ : Fin 1 => (1 : ℝ)) 1,
      InterpolationMatrix.exponentVector c.1 = e' := by
    intro e' he'
    rw [hsupp, Finset.mem_singleton] at he'
    subst he'
    exact ⟨⟨_, hcol⟩, by ext i; simp [InterpolationMatrix.exponentVector]⟩
  have H1 := h (m := 1) 3 1 1 1 (fun _ => 1) 1 (fun _ => 1) (fun _ => 0) P hcols rho
  rw [mulVec_eq 3 1 1 1 (fun _ => 1) 1 (fun _ => 1) (fun _ => 0) P hcols rho, hsupp,
    Finset.sum_singleton, Finset.sum_singleton] at H1
  have he0 : e 0 = 0 := by simp [e]
  have he1 : (fun i : Fin 1 => e i.succ) = fun _ => 1 := by funext i; fin_cases i; simp [e]
  have hcoef : P.coeff e = 1 := by simp [P]
  simp only [rho, he0, he1, hcoef, one_mul] at H1
  rw [entry_eval, entry_eval] at H1
  norm_num at H1
