-- Prove2me | solution 1 for NeutrinoDecoherence.vonNeumannEntropy_monotone_of_unital
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T09:17:05.539787+00:00
-- url     : https://prove2.me/submissions/5357947b-6023-4493-9cf3-d3d5322aa397

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs

set_option autoImplicit false

open scoped ComplexOrder

open Complex in
theorem nd_ode (f : ℝ → ℂ) (c : ℂ)
    (hf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (c * f t) (Set.Ici 0) t) (L : ℝ) (hL : 0 ≤ L) :
    f L = exp (c * (L : ℂ)) * f 0 := by
  set g : ℝ → ℂ := fun t => exp (-(c * (t : ℂ))) * f t with hgdef
  have hg : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt g 0 (Set.Ici 0) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => exp (-(c * (s : ℂ)))) (exp (-(c * (t : ℂ))) * (-(c * 1))) t :=
      (((hasDerivAt_id t).ofReal_comp).const_mul c).neg.cexp
    have h2 : HasDerivWithinAt g (exp (-(c * (t : ℂ))) * (-(c * 1)) * f t +
        exp (-(c * (t : ℂ))) * (c * f t)) (Set.Ici 0) t := h1.hasDerivWithinAt.mul (hf t ht)
    exact h2.congr_deriv (by ring)
  have hcont : ContinuousOn g (Set.Icc 0 L) := fun x hx =>
    (hg x hx.1).continuousWithinAt.mono Set.Icc_subset_Ici_self
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun x hx => (hg x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1)) L ⟨hL, le_refl L⟩
  simp only [hgdef, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hconst
  rw [← hconst, ← mul_assoc, ← Complex.exp_add]
  simp

open Matrix in
theorem nd_trace_cfc {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  simp

open NeutrinoDecoherence Matrix in
theorem nd_linEnt {n : Type*} [Fintype n] (ρ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) :
    0 ≤ linearEntropy ρ ∧ linearEntropy ρ ≤ 1 ∧ (linearEntropy ρ = 0 ↔ ρ * ρ = ρ) := by
  classical
  obtain ⟨hpsd, htr⟩ := hρ
  have hH : ρ.IsHermitian := hpsd.1
  have hsa : IsSelfAdjoint ρ := hH.isSelfAdjoint
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := hpsd.eigenvalues_nonneg
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have h := hH.trace_eq_sum_eigenvalues
    rw [htr] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at h2
    exact h2.symm
  have hsq : cfc (fun x : ℝ => x * x) ρ = ρ * ρ := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) ρ, cfc_id' (R := ℝ) (a := ρ)]
  have hid : cfc (fun x : ℝ => x) ρ = ρ := cfc_id' (R := ℝ) (a := ρ)
  have htr2 : (ρ * ρ).trace.re = ∑ i, hH.eigenvalues i * hH.eigenvalues i := by
    rw [← hsq, nd_trace_cfc ρ hH]
    simp only [Complex.re_sum, Complex.ofReal_re]
  have hle1 : ∀ i, hH.eigenvalues i ≤ 1 := fun i =>
    hsum ▸ Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have hterm : ∀ i, 0 ≤ hH.eigenvalues i - hH.eigenvalues i * hH.eigenvalues i :=
    fun i => by nlinarith [hnn i, hle1 i]
  have hS : linearEntropy ρ = ∑ i, (hH.eigenvalues i - hH.eigenvalues i * hH.eigenvalues i) := by
    unfold linearEntropy
    rw [htr2, Finset.sum_sub_distrib, hsum]
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]
    exact Finset.sum_nonneg (fun i _ => hterm i)
  · unfold linearEntropy
    rw [htr2]
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (hH.eigenvalues i))
    linarith
  · rw [hS, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)]
    constructor
    · intro h
      rw [← hsq]
      conv_rhs => rw [← hid]
      apply cfc_congr
      rw [hH.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      have := h i (Finset.mem_univ _)
      simp only
      linarith
    · intro h i _
      rw [← hsq] at h
      conv_rhs at h => rw [← hid]
      have h2 := eqOn_of_cfc_eq_cfc h
      rw [hH.spectrum_real_eq_range_eigenvalues] at h2
      have h3 := h2 ⟨i, rfl⟩
      simp only at h3
      linarith
open NeutrinoDecoherence Matrix Complex in
theorem nd_diss_add (a : Matrix (Fin 3) (Fin 3) ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    dissipator a (X + Y) = dissipator a X + dissipator a Y := by
  unfold dissipator
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_add]
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul]
  module

open NeutrinoDecoherence Matrix Complex in
theorem nd_lind_add (H : Matrix (Fin 2) (Fin 2) ℂ) (a : Matrix (Fin 3) (Fin 3) ℂ)
    (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladian H a (X + Y) = lindbladian H a X + lindbladian H a Y := by
  unfold lindbladian
  rw [nd_diss_add, Matrix.mul_add, Matrix.add_mul]
  module

open NeutrinoDecoherence Matrix Complex in
theorem nd_diss_smul (a : Matrix (Fin 3) (Fin 3) ℂ) (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    dissipator a (c • X) = c • dissipator a X := by
  unfold dissipator
  rw [smul_comm c (1 / 2 : ℂ)]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_comm c (a i j)]
  congr 1
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  module

open NeutrinoDecoherence Matrix Complex in
theorem nd_lind_smul (H : Matrix (Fin 2) (Fin 2) ℂ) (a : Matrix (Fin 3) (Fin 3) ℂ)
    (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladian H a (c • X) = c • lindbladian H a X := by
  unfold lindbladian
  rw [nd_diss_smul, Matrix.mul_smul, Matrix.smul_mul]
  module

open NeutrinoDecoherence Matrix Complex in
theorem nd_pauli_herm (i : Fin 3) : (pauli i)ᴴ = pauli i := by
  fin_cases i <;> ext k l <;> fin_cases k <;> fin_cases l <;> simp [pauli]

open NeutrinoDecoherence Matrix Complex in
theorem nd_diss_star (a : Matrix (Fin 3) (Fin 3) ℂ) (ha : a.IsHermitian)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (dissipator a X)ᴴ = dissipator a Xᴴ := by
  unfold dissipator
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul, nd_pauli_herm]
  congr 1
  · simp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha.apply i j]
  congr 1
  simp only [Matrix.mul_assoc, star_ofNat]
  abel

open NeutrinoDecoherence Matrix Complex in
theorem nd_lind_star (H : Matrix (Fin 2) (Fin 2) ℂ) (a : Matrix (Fin 3) (Fin 3) ℂ)
    (hH : H.IsHermitian) (ha : a.IsHermitian) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladian H a Xᴴ = (lindbladian H a X)ᴴ := by
  unfold lindbladian
  rw [Matrix.conjTranspose_add, nd_diss_star a ha, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq]
  simp only [star_neg, Complex.star_def, Complex.conj_I]
  module
open NeutrinoDecoherence Matrix Complex in
theorem nd_lind_trace (H : Matrix (Fin 2) (Fin 2) ℂ) (a : Matrix (Fin 3) (Fin 3) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (lindbladian H a X).trace = 0 := by
  simp [Matrix.trace_fin_two, lindbladian, dissipator, pauli, Fin.sum_univ_three,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring_nf
  simp only [Complex.I_sq]
  ring

open NeutrinoDecoherence Matrix Complex in
theorem nd_unital (a : Matrix (Fin 3) (Fin 3) ℂ) (h : dissipator a 1 = 0) :
    a 0 1 = a 1 0 ∧ a 0 2 = a 2 0 ∧ a 1 2 = a 2 1 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp [dissipator, pauli, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.vecMul, dotProduct] at h00 h01 h10
  ring_nf at h00 h01 h10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(I / 4)) * h00 + (a 0 1 - a 1 0) * Complex.I_sq
  · linear_combination (h10 - h01) / 8
  · linear_combination (-(I / 8)) * h01 + (-(I / 8)) * h10 + (a 1 2 - a 2 1) * Complex.I_sq

open NeutrinoDecoherence Matrix Complex in
theorem nd_rate (H : Matrix (Fin 2) (Fin 2) ℂ) (α : Fin 3 → Fin 3 → ℝ)
    (h10 : α 1 0 = α 0 1) (h20 : α 2 0 = α 0 2) (h21 : α 2 1 = α 1 2) (u w x y : ℝ) :
    (!![(u : ℂ), (x : ℂ) - (y : ℂ) * I; (x : ℂ) + (y : ℂ) * I, (w : ℂ)] *
      lindbladian H (Matrix.of fun i j => ((α i j : ℝ) : ℂ))
        !![(u : ℂ), (x : ℂ) - (y : ℂ) * I; (x : ℂ) + (y : ℂ) * I, (w : ℂ)]).trace.re =
      -4 * ((∑ k, ∑ l, α k l * (![y, -x, 0] : Fin 3 → ℝ) k * (![y, -x, 0] : Fin 3 → ℝ) l) +
        (∑ k, ∑ l, α k l * (![(u - w) / 2, 0, -x] : Fin 3 → ℝ) k *
          (![(u - w) / 2, 0, -x] : Fin 3 → ℝ) l) +
        (∑ k, ∑ l, α k l * (![0, (u - w) / 2, -y] : Fin 3 → ℝ) k *
          (![0, (u - w) / 2, -y] : Fin 3 → ℝ) l)) := by
  set X : Matrix (Fin 2) (Fin 2) ℂ :=
    !![(u : ℂ), (x : ℂ) - (y : ℂ) * I; (x : ℂ) + (y : ℂ) * I, (w : ℂ)] with hX
  have hcomm : (X * (H * X - X * H)).trace = 0 := by
    rw [Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc, Matrix.trace_mul_comm (X * H) X,
      sub_self]
  unfold lindbladian
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, hcomm, smul_zero,
    zero_add, hX]
  simp [dissipator, pauli, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.trace_fin_two, Matrix.vecMul, dotProduct, h10, h20, h21]
  ring
open NeutrinoDecoherence Matrix Complex in
theorem nd_herm (H : Matrix (Fin 2) (Fin 2) ℂ) (a : Matrix (Fin 3) (Fin 3) ℂ)
    (hH : H.IsHermitian) (ha : a.IsHermitian) (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution H a ρ) (h0 : (ρ 0).IsHermitian) (t : ℝ) (ht : 0 ≤ t) :
    (ρ t).IsHermitian := by
  let T : (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → Fin 2 → ℂ) :=
    { toFun := fun X => lindbladian H a X
      map_add' := fun X Y => nd_lind_add H a X Y
      map_smul' := fun c X => nd_lind_smul H a c X }
  let Tc := LinearMap.toContinuousLinearMap T
  let Δ : ℝ → (Fin 2 → Fin 2 → ℂ) := fun s i j => ρ s i j - star (ρ s j i)
  have hΔm : ∀ s, (Δ s : Matrix (Fin 2) (Fin 2) ℂ) = ρ s - (ρ s)ᴴ := by
    intro s; ext k l; simp [Δ, Matrix.conjTranspose_apply]
  have hsub : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      lindbladian H a (X - Xᴴ) = lindbladian H a X - (lindbladian H a X)ᴴ := by
    intro X
    rw [← nd_lind_star H a hH ha]
    exact T.map_sub X Xᴴ
  have hD : ∀ s, 0 ≤ s → HasDerivWithinAt Δ (T (Δ s)) (Set.Ici 0) s := by
    intro s hs
    rw [hasDerivWithinAt_pi]
    intro i
    rw [hasDerivWithinAt_pi]
    intro j
    have h1 : HasDerivWithinAt (fun x => Δ x i j)
        (lindbladian H a (ρ s) i j - star (lindbladian H a (ρ s) j i)) (Set.Ici 0) s :=
      (hsol s hs i j).sub (hsol s hs j i).star
    refine h1.congr_deriv ?_
    show _ = lindbladian H a (Δ s) i j
    rw [hΔm, hsub]
    simp [Matrix.conjTranspose_apply]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := Δ)
    (f' := fun s => T (Δ s)) (K := ‖Tc‖) (a := 0) (b := t + 1)
    (fun x hx => (hD x hx.1).continuousWithinAt.mono Set.Icc_subset_Ici_self)
    (fun x hx => (hD x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1))
    (by
      funext i j
      show ρ 0 i j - star (ρ 0 j i) = 0
      rw [h0.apply i j, sub_self])
    (fun x _ => Tc.le_opNorm (Δ x)) t ⟨ht, by linarith⟩
  ext i j
  have := congrFun (congrFun hzero j) i
  simp only [Δ, Pi.zero_apply, sub_eq_zero] at this
  rw [Matrix.conjTranspose_apply, this, star_star]

open Matrix in
theorem nd_quad (α : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) :
    RCLike.re (star (fun i => (v i : ℂ)) ⬝ᵥ
      ((Matrix.of fun i j => ((α i j : ℝ) : ℂ)) *ᵥ (fun i => (v i : ℂ)))) =
      ∑ k, ∑ l, α k l * v k * v l := by
  simp [dotProduct, mulVec, Fin.sum_univ_three]
  ring

theorem nd_G_anti {e1 e2 : ℝ} (h0 : 0 ≤ e1) (h12 : e1 ≤ e2) (h1 : e2 ≤ 1) :
    Real.negMulLog ((1 + e2) / 2) + Real.negMulLog ((1 - e2) / 2) ≤
      Real.negMulLog ((1 + e1) / 2) + Real.negMulLog ((1 - e1) / 2) := by
  rcases eq_or_lt_of_le (le_trans h0 h12) with he | he
  · have he1 : e1 = 0 := by linarith
    rw [← he, he1]
  · have ht0 : 0 ≤ (e1 + e2) / (2 * e2) := by positivity
    have ht1 : 0 ≤ 1 - (e1 + e2) / (2 * e2) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      linarith
    have ha : (1 - e2) / 2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
    have hd : (1 + e2) / 2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
    have c1 := Real.concaveOn_negMulLog.2 ha hd ht0 ht1 (by ring)
    have c2 := Real.concaveOn_negMulLog.2 ha hd ht1 ht0 (by ring)
    have eb : ((e1 + e2) / (2 * e2)) • ((1 - e2) / 2) + (1 - (e1 + e2) / (2 * e2)) • ((1 + e2) / 2)
        = (1 - e1) / 2 := by
      simp only [smul_eq_mul]
      field_simp
      ring
    have ec : (1 - (e1 + e2) / (2 * e2)) • ((1 - e2) / 2) + ((e1 + e2) / (2 * e2)) • ((1 + e2) / 2)
        = (1 + e1) / 2 := by
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [eb] at c1
    rw [ec] at c2
    simp only [smul_eq_mul] at c1 c2
    linarith

theorem nd_pair {l0 l1 : ℝ} (h : l0 + l1 = 1) :
    Real.negMulLog l0 + Real.negMulLog l1 =
      Real.negMulLog ((1 + |l0 - l1|) / 2) + Real.negMulLog ((1 - |l0 - l1|) / 2) := by
  rcases le_total l1 l0 with hl | hl
  · rw [abs_of_nonneg (by linarith)]
    rw [show (1 + (l0 - l1)) / 2 = l0 by linarith, show (1 - (l0 - l1)) / 2 = l1 by linarith]
  · rw [abs_of_nonpos (by linarith)]
    rw [show (1 + -(l0 - l1)) / 2 = l1 by linarith, show (1 - -(l0 - l1)) / 2 = l0 by linarith]
    ring

open NeutrinoDecoherence Matrix in
theorem nd_state (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.IsHermitian) (htr : X.trace = 1) :
    ∃ e : ℝ, 0 ≤ e ∧ e ^ 2 = 2 * (X * X).trace.re - 1 ∧
      vonNeumannEntropy X = Real.negMulLog ((1 + e) / 2) + Real.negMulLog ((1 - e) / 2) := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have hsum : hX.eigenvalues 0 + hX.eigenvalues 1 = 1 := by
    have h := hX.trace_eq_sum_eigenvalues
    rw [htr, Fin.sum_univ_two] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.add_re, Complex.ofReal_re] at h2
    exact h2.symm
  have hsq : cfc (fun x : ℝ => x * x) X = X * X := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) X, cfc_id' (R := ℝ) (a := X)]
  have hP : (X * X).trace.re = hX.eigenvalues 0 * hX.eigenvalues 0 +
      hX.eigenvalues 1 * hX.eigenvalues 1 := by
    rw [← hsq, nd_trace_cfc X hX, Fin.sum_univ_two]
    simp only [Complex.add_re, Complex.ofReal_re]
  refine ⟨|hX.eigenvalues 0 - hX.eigenvalues 1|, abs_nonneg _, ?_, ?_⟩
  · rw [sq_abs, hP]
    have : hX.eigenvalues 1 = 1 - hX.eigenvalues 0 := by linarith
    rw [this]
    ring
  · unfold vonNeumannEntropy
    rw [nd_trace_cfc X hX, Fin.sum_univ_two]
    simp only [Complex.add_re, Complex.ofReal_re]
    exact nd_pair hsum

open NeutrinoDecoherence Matrix Complex in
theorem nd_trace_pres (H : Matrix (Fin 2) (Fin 2) ℂ) (a : Matrix (Fin 3) (Fin 3) ℂ)
    (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hsol : IsLindbladSolution H a ρ) (t : ℝ) (ht : 0 ≤ t) :
    (ρ t).trace = (ρ 0).trace := by
  have h := nd_ode (fun s => ρ s 0 0 + ρ s 1 1) 0 (fun s hs => by
    have h1 := (hsol s hs 0 0).add (hsol s hs 1 1)
    refine h1.congr_deriv ?_
    have := nd_lind_trace H a (ρ s)
    rw [Matrix.trace_fin_two] at this
    rw [this, zero_mul]) t ht
  simp only [zero_mul, Complex.exp_zero, one_mul] at h
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  exact h

open NeutrinoDecoherence Matrix Complex ComplexOrder in
theorem solution (H : Matrix (Fin 2) (Fin 2) ℂ)
    (a : Matrix (Fin 3) (Fin 3) ℂ) (hH : H.IsHermitian) (ha : a.PosSemidef)
    (hunital : dissipator a 1 = 0) (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution H a ρ) (h0 : IsDensityMatrix (ρ 0)) :
    MonotoneOn (fun t => vonNeumannEntropy (ρ t)) (Set.Ici 0) := by
  have hherm : ∀ t, 0 ≤ t → (ρ t).IsHermitian :=
    fun t ht => nd_herm H a hH ha.1 ρ hsol h0.1.1 t ht
  have htr : ∀ t, 0 ≤ t → (ρ t).trace = 1 :=
    fun t ht => (nd_trace_pres H a ρ hsol t ht).trans h0.2
  obtain ⟨h01, h02, h12⟩ := nd_unital a hunital
  have hsym : ∀ i j, a j i = a i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h12]
  have hreal : ∀ i j, a i j = (((a i j).re : ℝ) : ℂ) := by
    intro i j
    have h := ha.1.apply i j
    rw [hsym i j, Complex.star_def] at h
    exact (Complex.conj_eq_iff_re.mp h).symm
  set α : Fin 3 → Fin 3 → ℝ := fun i j => (a i j).re with hαdef
  have haα : a = Matrix.of fun i j => ((α i j : ℝ) : ℂ) := by
    ext i j
    exact hreal i j
  have hα10 : α 1 0 = α 0 1 := by simp only [hαdef, hsym 0 1]
  have hα20 : α 2 0 = α 0 2 := by simp only [hαdef, hsym 0 2]
  have hα21 : α 2 1 = α 1 2 := by simp only [hαdef, hsym 1 2]
  have hQ : ∀ v : Fin 3 → ℝ, 0 ≤ ∑ k, ∑ l, α k l * v k * v l := by
    intro v
    have h := ha.re_dotProduct_nonneg (fun i => (v i : ℂ))
    rw [haα, nd_quad] at h
    exact h
  have hrate : ∀ t, 0 ≤ t → (ρ t * lindbladian H a (ρ t)).trace.re ≤ 0 := by
    intro t ht
    have hX := hherm t ht
    have e00 : ρ t 0 0 = (((ρ t 0 0).re : ℝ) : ℂ) := by
      have h := hX.apply 0 0
      rw [Complex.star_def] at h
      exact (Complex.conj_eq_iff_re.mp h).symm
    have e11 : ρ t 1 1 = (((ρ t 1 1).re : ℝ) : ℂ) := by
      have h := hX.apply 1 1
      rw [Complex.star_def] at h
      exact (Complex.conj_eq_iff_re.mp h).symm
    have e10 : ρ t 1 0 = (((ρ t 1 0).re : ℝ) : ℂ) + (((ρ t 1 0).im : ℝ) : ℂ) * I :=
      (Complex.re_add_im _).symm
    have e01 : ρ t 0 1 = (((ρ t 1 0).re : ℝ) : ℂ) - (((ρ t 1 0).im : ℝ) : ℂ) * I := by
      have h := hX.apply 0 1
      rw [← h, Complex.star_def]
      apply Complex.ext <;> simp
    have hform : ρ t = !![(((ρ t 0 0).re : ℝ) : ℂ),
        (((ρ t 1 0).re : ℝ) : ℂ) - (((ρ t 1 0).im : ℝ) : ℂ) * I;
        (((ρ t 1 0).re : ℝ) : ℂ) + (((ρ t 1 0).im : ℝ) : ℂ) * I,
        (((ρ t 1 1).re : ℝ) : ℂ)] := by
      conv_lhs => rw [Matrix.eta_fin_two (ρ t)]
      rw [← e00, ← e11, ← e10, ← e01]
    rw [hform, haα, nd_rate H α hα10 hα20 hα21]
    have q1 := hQ ![(ρ t 1 0).im, -(ρ t 1 0).re, 0]
    have q2 := hQ ![((ρ t 0 0).re - (ρ t 1 1).re) / 2, 0, -(ρ t 1 0).re]
    have q3 := hQ ![0, ((ρ t 0 0).re - (ρ t 1 1).re) / 2, -(ρ t 1 0).im]
    linarith
  have hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt (fun s => ((ρ s * ρ s).trace).re)
      ((2 * (ρ t * lindbladian H a (ρ t)).trace).re) (Set.Ici 0) t := by
    intro t ht
    have e : (fun s => (ρ s * ρ s).trace) = fun s => ρ s 0 0 * ρ s 0 0 + ρ s 0 1 * ρ s 1 0 +
        (ρ s 1 0 * ρ s 0 1 + ρ s 1 1 * ρ s 1 1) := by
      funext s
      simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    have d00 := hsol t ht 0 0
    have d01 := hsol t ht 0 1
    have d10 := hsol t ht 1 0
    have d11 := hsol t ht 1 1
    have hg : HasDerivWithinAt (fun s => (ρ s * ρ s).trace)
        (2 * (ρ t * lindbladian H a (ρ t)).trace) (Set.Ici 0) t := by
      rw [e]
      refine (((d00.mul d00).add (d01.mul d10)).add
        ((d10.mul d01).add (d11.mul d11))).congr_deriv ?_
      simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hg
  have hanti : AntitoneOn (fun s => ((ρ s * ρ s).trace).re) (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · intro x hx
      exact (hderiv x hx).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx ⊢
      exact (hderiv x (le_of_lt hx)).mono Set.Ioi_subset_Ici_self
    · intro x hx
      rw [interior_Ici] at hx
      have := hrate x (le_of_lt hx)
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith
  have hP0 : ((ρ 0 * ρ 0).trace).re ≤ 1 := by
    have := (nd_linEnt (ρ 0) h0).1
    unfold linearEntropy at this
    linarith
  intro s hs t ht hst
  have hs' : (0 : ℝ) ≤ s := hs
  have ht' : (0 : ℝ) ≤ t := ht
  obtain ⟨es, hes0, hes2, hSs⟩ := nd_state (ρ s) (hherm s hs') (htr s hs')
  obtain ⟨et, het0, het2, hSt⟩ := nd_state (ρ t) (hherm t ht') (htr t ht')
  have hPts := hanti hs ht hst
  have hPs0 := hanti (Set.mem_Ici.mpr le_rfl) hs hs'
  simp only at hPts hPs0 hSs hSt ⊢
  have hle : et ≤ es := by nlinarith
  have hes1 : es ≤ 1 := by nlinarith
  rw [hSs, hSt]
  exact nd_G_anti het0 hle hes1
