-- Prove2me | solution 1 for ModernConvex.MatrixCube.trace_max_eig_l1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:42:51.497623+00:00
-- url     : https://prove2.me/submissions/ae08d4c0-8232-4403-8a24-ac45b17e23a3

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix
open scoped MatrixOrder
open ModernConvex.MatrixCube

lemma g72mn_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      M = U * diagonal hM.eigenvalues * Uᵀ := by
  refine ⟨(hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · conv_lhs => rw [hM.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]

lemma g72mn_diag_entry {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    (Uᵀ * Y * U) k k = (fun i => U i k) ⬝ᵥ (Y *ᵥ fun i => U i k) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma g72mn_quad_spec {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1)
    (d : Fin n → ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ ((U * diagonal d * Uᵀ) *ᵥ v) = ∑ k, d k * (Uᵀ *ᵥ v) k ^ 2 ∧
      v ⬝ᵥ v = ∑ k, (Uᵀ *ᵥ v) k ^ 2 := by
  constructor
  · rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
    simp only [dotProduct, mulVec_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have : (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) = v ⬝ᵥ v := by
      rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, mulVec_mulVec, hU,
        one_mulVec]
    rw [← this]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

def g72mn_Q {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ v : Fin n → ℝ, |v ⬝ᵥ (Y *ᵥ v)| ≤ v ⬝ᵥ v

lemma g72mn_Q_of_spec {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1)
    (d : Fin n → ℝ) (hd : ∀ k, |d k| ≤ 1) : g72mn_Q (U * diagonal d * Uᵀ) := by
  intro v
  obtain ⟨h1, h2⟩ := g72mn_quad_spec U hU d v
  rw [h1, h2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_nonneg (sq_nonneg ((Uᵀ *ᵥ v) k))]
  exact mul_le_of_le_one_left (sq_nonneg _) (hd k)

lemma g72mn_eig_le_of_Q {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian)
    (hQ : g72mn_Q M) (i : Fin n) : |hM.eigenvalues i| ≤ 1 := by
  obtain ⟨U, hU1, hU2, hMU⟩ := g72mn_spec M hM
  generalize hM.eigenvalues = l at hMU ⊢
  have hD : Uᵀ * M * U = diagonal l := by
    rw [hMU]
    calc Uᵀ * (U * diagonal l * Uᵀ) * U
        = (Uᵀ * U) * diagonal l * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have e1 : l i = (fun j => U j i) ⬝ᵥ (M *ᵥ fun j => U j i) := by
    rw [← g72mn_diag_entry, hD, diagonal_apply_eq]
  have e2 : (fun j => U j i) ⬝ᵥ (fun j => U j i) = 1 := by
    have := g72mn_diag_entry U 1 i
    rw [Matrix.mul_one, hU1, one_mulVec, one_apply_eq] at this
    exact this.symm
  rw [e1]
  have := hQ (fun j => U j i)
  rwa [e2] at this

lemma g72mn_trace_le {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (d : Fin n → ℝ) (hY : g72mn_Q Y) :
    (Y * (U * diagonal d * Uᵀ)).trace ≤ ∑ k, |d k| := by
  have : (Y * (U * diagonal d * Uᵀ)).trace = ((Uᵀ * Y * U) * diagonal d).trace := by
    rw [show Y * (U * diagonal d * Uᵀ) = (Y * U * diagonal d) * Uᵀ by
      simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [this]
  simp only [trace, diag, mul_diagonal]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [g72mn_diag_entry]
  have hc : (fun i => U i k) ⬝ᵥ (fun i => U i k) = 1 := by
    have := g72mn_diag_entry U 1 k
    rw [Matrix.mul_one, hU, one_mulVec, one_apply_eq] at this
    exact this.symm
  have h1 := hY (fun i => U i k)
  rw [hc] at h1
  calc _ ≤ |(fun i => U i k) ⬝ᵥ (Y *ᵥ fun i => U i k) * d k| := le_abs_self _
    _ = _ := abs_mul _ _
    _ ≤ 1 * |d k| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |d k| := one_mul _

lemma g72mn_psd_q {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) (v : Fin n → ℝ) :
    0 ≤ v ⬝ᵥ (M *ᵥ v) := by
  simpa using hM.dotProduct_mulVec_nonneg v

lemma g72mn_herm_T {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) : Mᵀ = M := by
  have := hM.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma g72mn_herm_of_T {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = M) : M.IsHermitian := by
  unfold IsHermitian
  rwa [conjTranspose_eq_transpose_of_trivial]

lemma g72mn_spec_T {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    (U * diagonal d * Uᵀ)ᵀ = U * diagonal d * Uᵀ := by
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma g72mn_spec_mul {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) (d e : Fin n → ℝ) :
    (U * diagonal d * Uᵀ) * (U * diagonal e * Uᵀ) = U * diagonal (d * e) * Uᵀ := by
  calc (U * diagonal d * Uᵀ) * (U * diagonal e * Uᵀ)
      = U * diagonal d * (Uᵀ * U) * diagonal e * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; rfl

lemma g72mn_spec_psd {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hd : 0 ≤ d) :
    (U * diagonal d * Uᵀ).PosSemidef := by
  have := (PosSemidef.diagonal hd).mul_mul_conjTranspose_same U
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma g72mn_trace_spec {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) (d : Fin n → ℝ) :
    (U * diagonal d * Uᵀ).trace = ∑ k, d k := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, trace_diagonal]

theorem g72mn_main {n : ℕ} (W A : Matrix (Fin n) (Fin n) ℝ) (hW : W.PosSemidef)
    (hA : A.IsHermitian) :
    IsGreatest {t : ℝ | ∃ U V : Matrix (Fin n) (Fin n) ℝ, U.PosSemidef ∧ V.PosSemidef ∧
        U + V = W ∧ t = ((U - V) * A).trace}
      (eigL1 (CFC.sqrt W * A * CFC.sqrt W)) ∧
    IsGreatest {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian ∧
        (∀ i, |eigVec X i| ≤ 1) ∧ t = (X * (CFC.sqrt W * A * CFC.sqrt W)).trace}
      (eigL1 (CFC.sqrt W * A * CFC.sqrt W)) := by
  set S := CFC.sqrt W with hSdef
  have hW0 : 0 ≤ W := hW.nonneg
  have hSS : S * S = W := CFC.sqrt_mul_sqrt_self W hW0
  have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg W).posSemidef
  have hST : Sᵀ = S := g72mn_herm_T hSpsd.1
  have hAT : Aᵀ = A := g72mn_herm_T hA
  set C := S * A * S with hCdef
  have hCT : Cᵀ = C := by
    rw [hCdef, Matrix.transpose_mul, Matrix.transpose_mul, hST, hAT, Matrix.mul_assoc]
  have hC : C.IsHermitian := g72mn_herm_of_T hCT
  have hL1 : eigL1 C = ∑ k, |hC.eigenvalues k| := by
    unfold eigL1 eigVec; rw [dif_pos hC]
  obtain ⟨UC, hUC1, hUC2, hCU⟩ := g72mn_spec C hC
  generalize hC.eigenvalues = lam at hCU hL1
  set s : Fin n → ℝ := fun k => if 0 ≤ lam k then 1 else -1 with hs
  have hs1 : ∀ k, |s k| ≤ 1 := fun k => by
    simp only [hs]; split_ifs <;> simp
  have hslam : ∀ k, s k * lam k = |lam k| := fun k => by
    simp only [hs]; split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set G := UC * diagonal s * UCᵀ with hG
  have hGC : (G * C).trace = eigL1 C := by
    rw [hL1, hCU, hG, g72mn_spec_mul UC hUC1, g72mn_trace_spec UC hUC1]
    exact Finset.sum_congr rfl fun k _ => hslam k
  -- the pseudo-inverse of S
  obtain ⟨US, hUS1, hUS2, hSU⟩ := g72mn_spec S hSpsd.1
  generalize hSpsd.1.eigenvalues = mu at hSU
  set T := US * diagonal mu⁻¹ * USᵀ with hTdef
  have hTT : Tᵀ = T := g72mn_spec_T _ _
  have hSTc : S * T = T * S := by
    rw [hSU, hTdef, g72mn_spec_mul US hUS1, g72mn_spec_mul US hUS1, mul_comm]
  have hSTS : S * T * S = S := by
    have hmu : mu * mu⁻¹ * mu = mu := by
      funext k
      simp only [Pi.mul_apply, Pi.inv_apply]
      by_cases h : mu k = 0
      · simp [h]
      · field_simp
    rw [hSU, hTdef, g72mn_spec_mul US hUS1, g72mn_spec_mul US hUS1, hmu]
  have hSP0 : S * (S * T) = S := by rw [hSTc, ← Matrix.mul_assoc, hSTS]
  obtain ⟨P, hPdef⟩ : ∃ P, P = S * T := ⟨_, rfl⟩
  have hPT : Pᵀ = P := by rw [hPdef, Matrix.transpose_mul, hST, hTT, ← hSTc]
  have hPP : P * P = P := by
    rw [hPdef, show S * T * (S * T) = (S * T * S) * T by simp only [Matrix.mul_assoc], hSTS]
  have hSP : S * P = S := by rw [hPdef, hSP0]
  have hTS : T * S = P := by rw [hPdef, hSTc]
  have hWP : W * P = W := by rw [← hSS, Matrix.mul_assoc, hSP]
  have hTWT : T * W * T = P := by
    rw [← hSS, show T * (S * S) * T = (T * S) * (S * T) by simp only [Matrix.mul_assoc], hTS,
      ← hPdef, hPP]
  have hSPS : S * P * S = W := by rw [hSP, hSS]
  have hPpsd : P.PosSemidef := by
    have := posSemidef_conjTranspose_mul_self P
    rwa [conjTranspose_eq_transpose_of_trivial, hPT, hPP] at this
  have hIPpsd : (1 - P).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self (1 - P)
    rwa [conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub, transpose_one, hPT,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hPP, sub_self, sub_zero] at this
  have hGh : G.IsHermitian := g72mn_herm_of_T (g72mn_spec_T _ _)
  refine ⟨⟨⟨S * (UC * diagonal (fun k => (1 + s k) / 2) * UCᵀ) * S,
      S * (UC * diagonal (fun k => (1 - s k) / 2) * UCᵀ) * S, ?_, ?_, ?_, ?_⟩, ?_⟩,
    ⟨⟨G, hGh, ?_, hGC.symm⟩, ?_⟩⟩
  · have := (g72mn_spec_psd UC (fun k => (1 + s k) / 2) fun k => by
      have := hs1 k; simp only [Pi.zero_apply]
      have := neg_abs_le (s k); linarith).mul_mul_conjTranspose_same S
    rwa [conjTranspose_eq_transpose_of_trivial, hST] at this
  · have := (g72mn_spec_psd UC (fun k => (1 - s k) / 2) fun k => by
      have := hs1 k; simp only [Pi.zero_apply]
      have := le_abs_self (s k); linarith).mul_mul_conjTranspose_same S
    rwa [conjTranspose_eq_transpose_of_trivial, hST] at this
  · rw [← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    have : (fun i => (1 + s i) / 2 + (1 - s i) / 2) = (fun _ => (1 : ℝ)) := by
      funext k; ring
    rw [this, diagonal_one, Matrix.mul_one, hUC2, Matrix.mul_one, hSS]
  · rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    have : (fun i => (1 + s i) / 2 - (1 - s i) / 2) = s := by
      funext k; ring
    rw [this, ← hG, ← hGC, show S * G * S * A = S * (G * S * A) by simp only [Matrix.mul_assoc],
      trace_mul_comm]
    simp only [hCdef, Matrix.mul_assoc]
    rw [show S * (A * (S * G)) = (S * A * S) * G by simp only [Matrix.mul_assoc],
      trace_mul_comm S (G * (S * A)), trace_mul_comm (S * A * S) G]
    simp only [Matrix.mul_assoc]
  · rintro t ⟨U, V, hU, hV, hUV, rfl⟩
    have hVW : V = W - U := by rw [← hUV]; abel
    have hker : U * (1 - P) = 0 := by
      rw [ext_iff_mulVec]
      intro v
      set w := (1 - P) *ᵥ v
      have hWw : W *ᵥ w = 0 := by
        simp only [w, mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hWP, sub_self, zero_mulVec]
      have h0 : w ⬝ᵥ (U *ᵥ w) + w ⬝ᵥ (V *ᵥ w) = 0 := by
        rw [← dotProduct_add, ← add_mulVec, hUV, hWw, dotProduct_zero]
      have h1 := g72mn_psd_q hU w
      have h2 := g72mn_psd_q hV w
      have h3 : w ⬝ᵥ (U *ᵥ w) = 0 := by linarith
      rw [← mulVec_mulVec, zero_mulVec]
      have := (hU.dotProduct_mulVec_zero_iff w).mp (by simpa using h3)
      exact this
    have hUP : U * P = U := by
      have := hker; rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this; exact this.symm
    have hUT : Uᵀ = U := g72mn_herm_T hU.1
    have hPU : P * U = U := by
      have := congrArg Matrix.transpose hUP
      rwa [Matrix.transpose_mul, hPT, hUT] at this
    have hY : U - V = S * ((2 : ℝ) • (T * U * T) - P) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hSPS, Matrix.mul_smul, Matrix.smul_mul,
        show S * (T * U * T) * S = (S * T) * U * (T * S) by simp only [Matrix.mul_assoc],
        ← hPdef, hTS, hPU, hUP, hVW]
      rw [two_smul]; abel
    rw [hY, show S * ((2 : ℝ) • (T * U * T) - P) * S * A =
        S * (((2 : ℝ) • (T * U * T) - P) * S * A) by simp only [Matrix.mul_assoc],
      trace_mul_comm, show ((2 : ℝ) • (T * U * T) - P) * S * A * S =
        ((2 : ℝ) • (T * U * T) - P) * C by simp only [hCdef, Matrix.mul_assoc], hL1, hCU]
    refine g72mn_trace_le UC _ hUC1 lam fun v => ?_
    have hTv : ∀ (M : Matrix (Fin n) (Fin n) ℝ),
        v ⬝ᵥ ((T * M * T) *ᵥ v) = (T *ᵥ v) ⬝ᵥ (M *ᵥ (T *ᵥ v)) := by
      intro M
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hTT]
    have ha := g72mn_psd_q hU (T *ᵥ v)
    have hb := g72mn_psd_q hV (T *ᵥ v)
    have hab : (T *ᵥ v) ⬝ᵥ (U *ᵥ (T *ᵥ v)) + (T *ᵥ v) ⬝ᵥ (V *ᵥ (T *ᵥ v)) = v ⬝ᵥ (P *ᵥ v) := by
      rw [← dotProduct_add, ← add_mulVec, hUV, ← hTv, hTWT]
    have hp1 := g72mn_psd_q hPpsd v
    have hp2 := g72mn_psd_q hIPpsd v
    rw [sub_mulVec, one_mulVec, dotProduct_sub] at hp2
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, hTv, smul_eq_mul, abs_le]
    constructor <;> linarith
  · intro i
    unfold eigVec; rw [dif_pos hGh]
    exact g72mn_eig_le_of_Q G hGh (g72mn_Q_of_spec UC hUC2 s hs1) i
  · rintro t ⟨X, hX, heig, rfl⟩
    have heig' : ∀ i, |hX.eigenvalues i| ≤ 1 := by
      intro i; have := heig i; unfold eigVec at this; rwa [dif_pos hX] at this
    obtain ⟨UX, hUX1, hUX2, hXU⟩ := g72mn_spec X hX
    generalize hX.eigenvalues = lx at hXU heig'
    have hQX : g72mn_Q X := by rw [hXU]; exact g72mn_Q_of_spec UX hUX2 lx heig'
    rw [hL1, hCU]
    exact g72mn_trace_le UC X hUC1 lam hQX



/-- Ben-Tal–Nemirovski, Lemma 4.4.3, p. 191, (4.4.41): let `W, A ∈ Sⁿ` with `W ⪰ 0`, and let
`W^{1/2}` be the positive semidefinite square root of `W`. Then
`max_{U,V ⪰ 0, U+V=W} Tr([U − V]A) = max_{X=Xᵀ : ‖λ(X)‖_∞ ≤ 1} Tr(XW^{1/2}AW^{1/2})
  = ‖λ(W^{1/2}AW^{1/2})‖₁`.
Both maxima are stated as attained greatest values of the respective sets of traces. -/
theorem solution {n : ℕ} (W A : Matrix (Fin n) (Fin n) ℝ) (hW : W.PosSemidef)
    (hA : A.IsHermitian) :
    IsGreatest {t : ℝ | ∃ U V : Matrix (Fin n) (Fin n) ℝ, U.PosSemidef ∧ V.PosSemidef ∧
        U + V = W ∧ t = ((U - V) * A).trace}
      (eigL1 (CFC.sqrt W * A * CFC.sqrt W)) ∧
    IsGreatest {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian ∧
        (∀ i, |eigVec X i| ≤ 1) ∧ t = (X * (CFC.sqrt W * A * CFC.sqrt W)).trace}
      (eigL1 (CFC.sqrt W * A * CFC.sqrt W)) := by
  exact g72mn_main W A hW hA


