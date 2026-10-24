-- Prove2me | solution 1 for ModernConvex.Relaxations.nemirovski_roos_terlaky
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T23:35:03.780059+00:00
-- url     : https://prove2.me/submissions/fac3da17-4327-41fe-af86-05c4440a94f5

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_QuadraticSystem
import Theorems.Thm_VBSDP_Duality_theorem_3_1

open Matrix

namespace NRT100

/-- Rademacher sign vector. -/
def sg {n : ℕ} (ξ : Fin n → Bool) : Fin n → ℝ := fun j => if ξ j then 1 else -1

lemma H_mgf {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    ∑ ξ : Fin n → Bool, Real.exp (t * (a ⬝ᵥ sg ξ)) ≤
      2 ^ n * Real.exp (t ^ 2 * (a ⬝ᵥ a) / 2) := by
  have h1 : ∀ ξ : Fin n → Bool, Real.exp (t * (a ⬝ᵥ sg ξ)) =
      ∏ j, (fun j (b : Bool) => Real.exp (t * a j * (if b then 1 else -1))) j (ξ j) := by
    intro ξ
    simp only [dotProduct, Finset.mul_sum, ← Real.exp_sum, sg]
    congr 1; apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_congr rfl (fun ξ _ => h1 ξ),
    ← Fintype.prod_sum (fun j (b : Bool) => Real.exp (t * a j * (if b then 1 else -1)))]
  have h2 : ∀ j, ∑ b : Bool, Real.exp (t * a j * (if b then 1 else -1)) ≤
      2 * Real.exp ((t * a j) ^ 2 / 2) := by
    intro j
    have := Real.cosh_le_exp_half_sq (t * a j)
    rw [Real.cosh_eq] at this
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, mul_one, mul_neg]
    linarith
  calc _ ≤ ∏ j, 2 * Real.exp ((t * a j) ^ 2 / 2) :=
        Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => h2 j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      congr 2
      simp only [dotProduct, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _; ring

/-- (H) Hoeffding + union bound over finitely many vectors. -/
theorem rad_union {n : ℕ} {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (R : ℝ)
    (hR : (Fintype.card ι : ℝ) ≤ R) (hR1 : 1 ≤ R) :
    ∃ ξ : Fin n → Bool, ∀ k, (a k ⬝ᵥ sg ξ) ^ 2 ≤ 2 * Real.log (2 * R) * (a k ⬝ᵥ a k) := by
  by_contra hcon
  push Not at hcon
  set ρ := 2 * Real.log (2 * R) with hρdef
  have hρ : 0 < ρ := by
    have : 0 < Real.log (2 * R) := Real.log_pos (by linarith)
    linarith
  have hq : ∀ k, a k ≠ 0 → 0 < a k ⬝ᵥ a k := by
    intro k hk
    have h0 : 0 ≤ a k ⬝ᵥ a k := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hk
  set lam : ι → ℝ := fun k => Real.sqrt (ρ / (a k ⬝ᵥ a k)) with hlam
  have hlam2 : ∀ k, a k ≠ 0 → lam k ^ 2 * (a k ⬝ᵥ a k) = ρ := by
    intro k hk
    simp only [hlam]
    rw [Real.sq_sqrt (div_nonneg hρ.le (hq k hk).le), div_mul_cancel₀ _ (hq k hk).ne']
  set g : ι → (Fin n → Bool) → ℝ := fun k ξ => if a k = 0 then 0 else
    Real.exp (lam k * (a k ⬝ᵥ sg ξ) - ρ) + Real.exp (-lam k * (a k ⬝ᵥ sg ξ) - ρ) with hg
  have hg0 : ∀ k ξ, 0 ≤ g k ξ := by
    intro k ξ; simp only [hg]; split_ifs <;> positivity
  have hbad : ∀ ξ, 1 < ∑ k, g k ξ := by
    intro ξ
    obtain ⟨k, hk⟩ := hcon ξ
    have hak : a k ≠ 0 := by
      rintro h; simp [h] at hk
    have hqk := hq k hak
    have hsq : ρ ^ 2 < (lam k * (a k ⬝ᵥ sg ξ)) ^ 2 := by
      have e : (lam k * (a k ⬝ᵥ sg ξ)) ^ 2 = lam k ^ 2 * (a k ⬝ᵥ sg ξ) ^ 2 := by ring
      rw [e]
      have : lam k ^ 2 = ρ / (a k ⬝ᵥ a k) := by
        rw [← hlam2 k hak, mul_div_assoc, div_self hqk.ne', mul_one]
      rw [this, div_mul_eq_mul_div, lt_div_iff₀ hqk]
      nlinarith
    rw [sq_lt_sq, abs_of_pos hρ] at hsq
    calc 1 < g k ξ := by
          simp only [hg, hak, if_false]
          rcases lt_abs.mp hsq with h | h
          · have := Real.one_lt_exp_iff.mpr (show 0 < lam k * (a k ⬝ᵥ sg ξ) - ρ by linarith)
            have := Real.exp_pos (-lam k * (a k ⬝ᵥ sg ξ) - ρ)
            linarith
          · have := Real.one_lt_exp_iff.mpr (show 0 < -lam k * (a k ⬝ᵥ sg ξ) - ρ by linarith)
            have := Real.exp_pos (lam k * (a k ⬝ᵥ sg ξ) - ρ)
            linarith
      _ ≤ ∑ k, g k ξ := Finset.single_le_sum (fun k _ => hg0 k ξ) (Finset.mem_univ k)
  have hsum : ∀ k, ∑ ξ, g k ξ ≤ 2 ^ n / R := by
    intro k
    by_cases hak : a k = 0
    · simp only [hg, hak, if_true, Finset.sum_const_zero]; positivity
    simp only [hg, hak, if_false]
    rw [Finset.sum_add_distrib]
    simp only [Real.exp_sub, ← Finset.sum_div]
    have m1 := H_mgf (a k) (lam k)
    have m2 := H_mgf (a k) (-lam k)
    rw [neg_sq, hlam2 k hak] at m2
    rw [hlam2 k hak] at m1
    have hE : Real.exp (ρ / 2) / Real.exp ρ = 1 / (2 * R) := by
      rw [← Real.exp_sub, show ρ / 2 - ρ = -Real.log (2 * R) by rw [hρdef]; ring,
        Real.exp_neg, Real.exp_log (by linarith)]
      ring
    have hp : 0 < Real.exp ρ := Real.exp_pos _
    calc _ ≤ 2 ^ n * Real.exp (ρ / 2) / Real.exp ρ + 2 ^ n * Real.exp (ρ / 2) / Real.exp ρ := by
          gcongr
      _ = 2 * 2 ^ n * (Real.exp (ρ / 2) / Real.exp ρ) := by ring
      _ = 2 ^ n / R := by rw [hE]; field_simp
  have hlt : (2 : ℝ) ^ n < ∑ k, ∑ ξ, g k ξ := by
    rw [Finset.sum_comm]
    calc (2 : ℝ) ^ n = ∑ _ξ : Fin n → Bool, (1 : ℝ) := by simp
      _ < _ := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ξ _ => hbad ξ)
  have hle : ∑ k, ∑ ξ, g k ξ ≤ 2 ^ n := by
    calc _ ≤ ∑ _k : ι, (2 : ℝ) ^ n / R := Finset.sum_le_sum (fun k _ => hsum k)
      _ = Fintype.card ι * (2 ^ n / R) := by simp
      _ ≤ R * (2 ^ n / R) := by gcongr
      _ = 2 ^ n := by field_simp
  linarith

end NRT100


open Matrix

namespace NRT100

theorem CD_spec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      A = U * diagonal hA.eigenvalues * Uᵀ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  · have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have e : (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℝ) = hA.eigenvalues := by
      funext i; simp
    rw [e] at h
    conv_lhs => rw [h]
    simp [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

theorem psd_factor {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    ∃ (F : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)),
      Fᵀ * F = B ∧ (∀ k, k ∉ s → F k = 0) ∧ s.card = B.rank := by
  classical
  obtain ⟨U, h1, h2, hBU⟩ := CD_spec hB.isHermitian
  set μ := hB.isHermitian.eigenvalues with hμ
  have hnn : ∀ i, 0 ≤ μ i := hB.eigenvalues_nonneg
  refine ⟨diagonal (fun k => Real.sqrt (μ k)) * Uᵀ, Finset.univ.filter (fun k => μ k ≠ 0),
    ?_, ?_, ?_⟩
  · rw [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal, ← Matrix.mul_assoc, hBU]
    congr 2
    congr 1
    funext k
    exact Real.mul_self_sqrt (hnn k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hk
    funext j
    simp [diagonal_mul, hk]
  · rw [hB.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]

theorem diag_factor {n : ℕ} {X A : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hA : A.IsHermitian) :
    ∃ G : Matrix (Fin n) (Fin n) ℝ, G * Gᵀ = X ∧ ∃ c : Fin n → ℝ, Gᵀ * A * G = diagonal c := by
  obtain ⟨F, -, hF, -, -⟩ := psd_factor hX
  have hM : (F * A * Fᵀ).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_mul,
      transpose_transpose, ← conjTranspose_eq_transpose_of_trivial A, hA.eq, Matrix.mul_assoc]
  obtain ⟨U, h1, h2, hMU⟩ := CD_spec hM
  refine ⟨Fᵀ * U, ?_, hM.eigenvalues, ?_⟩
  · rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U, h2,
      Matrix.one_mul, hF]
  · rw [transpose_mul, transpose_transpose]
    calc Uᵀ * F * A * (Fᵀ * U) = Uᵀ * (F * A * Fᵀ) * U := by simp only [Matrix.mul_assoc]
      _ = Uᵀ * U * diagonal hM.eigenvalues * (Uᵀ * U) := by
          conv_lhs => rw [hMU]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]

end NRT100


open Matrix
open ModernConvex.Relaxations

namespace NY99

/-- block diagonal matrix with blocks of sizes `n` and `m` -/
def sddD_bd {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (n+m)) (Fin (n+m)) ℝ :=
  fun a b => Fin.addCases (fun i => Fin.addCases (fun j => M i j) (fun _ => (0:ℝ)) b)
    (fun i => Fin.addCases (fun _ => (0:ℝ)) (fun j => W i j) b) a

section
variable {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
lemma sddD_bd_ll (i j : Fin n) : sddD_bd M W (Fin.castAdd m i) (Fin.castAdd m j) = M i j := by
  simp [sddD_bd]
lemma sddD_bd_lr (i : Fin n) (j : Fin m) : sddD_bd M W (Fin.castAdd m i) (Fin.natAdd n j) = 0 := by
  simp [sddD_bd, -Fin.natAdd_eq_addNat]
lemma sddD_bd_rl (i : Fin m) (j : Fin n) : sddD_bd M W (Fin.natAdd n i) (Fin.castAdd m j) = 0 := by
  simp [sddD_bd, -Fin.natAdd_eq_addNat]
lemma sddD_bd_rr (i j : Fin m) : sddD_bd M W (Fin.natAdd n i) (Fin.natAdd n j) = W i j := by
  simp [sddD_bd, -Fin.natAdd_eq_addNat]
end

lemma sddD_bd_quad {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin (n+m) → ℝ) :
    x ⬝ᵥ (sddD_bd M W *ᵥ x) = (fun i => x (Fin.castAdd m i)) ⬝ᵥ (M *ᵥ fun i => x (Fin.castAdd m i))
      + (fun i => x (Fin.natAdd n i)) ⬝ᵥ (W *ᵥ fun i => x (Fin.natAdd n i)) := by
  simp [dotProduct, mulVec, Fin.sum_univ_add, sddD_bd_ll, sddD_bd_lr, sddD_bd_rl, sddD_bd_rr,
    -Fin.natAdd_eq_addNat]

lemma sddD_bd_herm {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.IsHermitian) (hW : W.IsHermitian) : (sddD_bd M W).IsHermitian := by
  have hM' : ∀ a b, M a b = M b a := fun a b => by simpa using (hM.apply b a)
  have hW' : ∀ a b, W a b = W b a := fun a b => by simpa using (hW.apply b a)
  ext a b
  induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    simp [hM', hW', -Fin.natAdd_eq_addNat, sddD_bd_ll, sddD_bd_lr, sddD_bd_rl, sddD_bd_rr]

lemma sddD_bd_psd {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.PosSemidef) (hW : W.PosSemidef) : (sddD_bd M W).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨sddD_bd_herm hM.isHermitian hW.isHermitian, fun x => ?_⟩
  simp only [star_trivial, sddD_bd_quad]
  have h1 := hM.dotProduct_mulVec_nonneg (fun i => x (Fin.castAdd m i))
  have h2 := hW.dotProduct_mulVec_nonneg (fun i => x (Fin.natAdd n i))
  simp only [star_trivial] at h1 h2
  linarith

lemma sddD_bd_posDef {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.PosDef) (hW : W.PosDef) : (sddD_bd M W).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨sddD_bd_herm hM.isHermitian hW.isHermitian, fun x hx => ?_⟩
  simp only [star_trivial, sddD_bd_quad]
  have h1 := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => x (Fin.castAdd m i))
  have h2 := hW.posSemidef.dotProduct_mulVec_nonneg (fun i => x (Fin.natAdd n i))
  simp only [star_trivial] at h1 h2
  by_cases hu : (fun i => x (Fin.castAdd m i)) = 0
  · have hv : (fun i => x (Fin.natAdd n i)) ≠ 0 := by
      intro hv
      apply hx
      ext a
      induction a using Fin.addCases with
      | left i => exact congrFun hu i
      | right i => exact congrFun hv i
    have := hW.dotProduct_mulVec_pos hv
    simp only [star_trivial] at this
    linarith
  · have := hM.dotProduct_mulVec_pos hu
    simp only [star_trivial] at this
    linarith

lemma sddD_bd_psd_left {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (h : (sddD_bd M W).PosSemidef) : M.PosSemidef := by
  have := h.submatrix (Fin.castAdd m)
  convert this using 1
  ext i j; simp [sddD_bd_ll]

lemma sddD_bd_psd_right {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {W : Matrix (Fin m) (Fin m) ℝ}
    (h : (sddD_bd M W).PosSemidef) : W.PosSemidef := by
  have := h.submatrix (Fin.natAdd n)
  convert this using 1
  ext i j; simp [sddD_bd_rr, -Fin.natAdd_eq_addNat]

lemma sddD_bd_trace {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℝ) :
    (sddD_bd M W * Z).trace = (M * Z.submatrix (Fin.castAdd m) (Fin.castAdd m)).trace
      + (W * Z.submatrix (Fin.natAdd n) (Fin.natAdd n)).trace := by
  simp [trace, mul_apply, Fin.sum_univ_add, sddD_bd_ll, sddD_bd_lr, sddD_bd_rl, sddD_bd_rr,
    -Fin.natAdd_eq_addNat]

/-- trace of a product of PSD matrices is nonnegative -/
lemma sddD_trace_psd {n : ℕ} {P X : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef)
    (hX : X.PosSemidef) : 0 ≤ (P * X).trace := by
  obtain ⟨k, v, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.1 hX
  rw [Matrix.mul_sum, trace_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [mul_vecMulVec, trace_vecMulVec]
  have := hP.dotProduct_mulVec_nonneg (v i)
  simp only [star_trivial] at this ⊢
  rw [dotProduct_comm]; exact this

lemma sddD_pd_lower {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) :
    ∃ c > 0, ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x) := by
  set K := Metric.sphere (0 : Fin n → ℝ) 1 with hK
  have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (P *ᵥ x) := by fun_prop
  have hdot_le : ∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ n * ‖x‖ ^ 2 := by
    intro x
    have : ∀ i, x i * x i ≤ ‖x‖ ^ 2 := fun i => by
      have h := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at h
      nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
    calc x ⬝ᵥ x = ∑ i, x i * x i := rfl
      _ ≤ ∑ _i : Fin n, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = n * ‖x‖ ^ 2 := by simp
  have hscale : ∀ x : Fin n → ℝ, x ≠ 0 → ‖x‖⁻¹ • x ∈ K := by
    intro x hx
    rw [hK, mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0K, hmin⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hne
      hcont.continuousOn
    have hx0 : x0 ≠ 0 := by
      rintro rfl; simp at hx0K
    have hc0 : 0 < x0 ⬝ᵥ (P *ᵥ x0) := by
      have := hP.dotProduct_mulVec_pos hx0
      simpa using this
    refine ⟨x0 ⬝ᵥ (P *ᵥ x0) / (n + 1), by positivity, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    have hu := hmin (hscale x hx)
    have hu' : x0 ⬝ᵥ (P *ᵥ x0) ≤ (‖x‖⁻¹ • x) ⬝ᵥ (P *ᵥ (‖x‖⁻¹ • x)) := hu
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hu'
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hq : ‖x‖ ^ 2 * (x0 ⬝ᵥ (P *ᵥ x0)) ≤ x ⬝ᵥ (P *ᵥ x) := by
      have : ‖x‖ ^ 2 * (‖x‖⁻¹ * (‖x‖⁻¹ * (x ⬝ᵥ (P *ᵥ x)))) = x ⬝ᵥ (P *ᵥ x) := by
        field_simp
      calc _ ≤ ‖x‖ ^ 2 * (‖x‖⁻¹ * (‖x‖⁻¹ * (x ⬝ᵥ (P *ᵥ x)))) :=
            mul_le_mul_of_nonneg_left hu' (by positivity)
        _ = _ := this
    have h1 := hdot_le x
    have hd0 : 0 ≤ x ⬝ᵥ x := by
      simpa using (PosSemidef.one (n := Fin n) (R := ℝ)).dotProduct_mulVec_nonneg x
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ‖x‖]
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    exact absurd ⟨_, hscale x hx⟩ hne

lemma sddD_herm_lower {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    -((∑ i, ∑ j, |Q i j|) * (x ⬝ᵥ x)) ≤ x ⬝ᵥ (Q *ᵥ x) := by
  set u := x
  have hsq : ∀ i, u i ^ 2 ≤ u ⬝ᵥ u := fun i => by
    simpa [dotProduct, sq] using Finset.single_le_sum (f := fun k => u k * u k)
      (fun k _ => mul_self_nonneg (u k)) (Finset.mem_univ i)
  have hterm : ∀ i j, -(|Q i j| * (u ⬝ᵥ u)) ≤ u i * (Q i j * u j) := by
    intro i j
    have h1 : |u i * u j| ≤ u ⬝ᵥ u := by
      rw [abs_mul]
      nlinarith [abs_nonneg (u i), abs_nonneg (u j), sq_abs (u i), sq_abs (u j), hsq i, hsq j,
        sq_nonneg (|u i| - |u j|)]
    have h2 : |u i * (Q i j * u j)| = |Q i j| * |u i * u j| := by
      simp only [abs_mul]; ring
    have h3 := neg_abs_le (u i * (Q i j * u j))
    nlinarith [abs_nonneg (Q i j)]
  have : u ⬝ᵥ (Q *ᵥ u) = ∑ i, ∑ j, u i * (Q i j * u j) := by
    simp [dotProduct, mulVec, Finset.mul_sum]
  rw [this, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun j _ => hterm i j

lemma sddD_shift {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) (hQ : Q.IsHermitian) :
    ∃ t : ℝ, 0 ≤ t ∧ (t • P + Q).PosDef := by
  obtain ⟨c, hc, hcP⟩ := sddD_pd_lower hP
  set s := ∑ i, ∑ j, |Q i j|
  have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(s + 1) / c, by positivity, ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · exact (hP.posSemidef.smul (a := (s + 1) / c) (by positivity)).isHermitian.add hQ
  simp only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h1 := hcP x
  have h2 := sddD_herm_lower Q x
  have hpos : 0 < x ⬝ᵥ x := by
    simpa using (PosDef.one (n := Fin n) (R := ℝ)).dotProduct_mulVec_pos hx
  have : (s + 1) / c * (x ⬝ᵥ (P *ᵥ x)) ≥ (s + 1) * (x ⬝ᵥ x) := by
    rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hc]
    nlinarith
  nlinarith

/-- constraint matrices of the VB encoding -/
noncomputable def sddD_Fs {n m : ℕ} (S : QuadraticSystem n m) :
    Fin m → Matrix (Fin (n+m)) (Fin (n+m)) ℝ :=
  fun i => sddD_bd (S.B i) (diagonal (Pi.single i 1))

lemma sddD_lmi_eq {n m : ℕ} (S : QuadraticSystem n m) (x : Fin m → ℝ) :
    VBSDP.Duality.lmi (sddD_bd (-S.A) 0) (sddD_Fs S) x =
      sddD_bd (∑ i, x i • S.B i - S.A) (diagonal x) := by
  ext a c
  induction a using Fin.addCases <;> induction c using Fin.addCases <;>
    simp [VBSDP.Duality.lmi, sddD_Fs, Matrix.sum_apply, diagonal_apply, Pi.single_apply,
      -Fin.natAdd_eq_addNat, sddD_bd_ll, sddD_bd_lr, sddD_bd_rl, sddD_bd_rr]
  ring

lemma sddD_Fs_trace {n m : ℕ} (S : QuadraticSystem n m) (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℝ)
    (i : Fin m) :
    (sddD_Fs S i * Z).trace = (S.B i * Z.submatrix (Fin.castAdd m) (Fin.castAdd m)).trace
      + Z (Fin.natAdd n i) (Fin.natAdd n i) := by
  rw [sddD_Fs, sddD_bd_trace]
  congr 1
  simp [trace, diagonal_mul, Pi.single_apply]

lemma sddD_F0_trace {n m : ℕ} (S : QuadraticSystem n m) (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℝ) :
    -(sddD_bd (-S.A) 0 * Z).trace = (S.A * Z.submatrix (Fin.castAdd m) (Fin.castAdd m)).trace := by
  rw [sddD_bd_trace]
  simp [neg_mul, trace_neg]

lemma sddD_weak {n m : ℕ} (S : QuadraticSystem n m) {lam : Fin m → ℝ} (hlam : S.SDDFeasible lam)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : S.SDPFeasible X) :
    (S.A * X).trace ≤ ∑ i, lam i * S.d i := by
  have h0 := sddD_trace_psd hlam.1 hX.2
  have hexp : ((∑ i, lam i • S.B i - S.A) * X).trace = ∑ i, lam i * (S.B i * X).trace
      - (S.A * X).trace := by
    simp [sub_mul, Finset.sum_mul, trace_sub, trace_sum, trace_smul]
  have h1 : ∑ i, lam i * (S.B i * X).trace ≤ ∑ i, lam i * S.d i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hX.1 i) (hlam.2 i)
  linarith

theorem ny_sdd {n m : ℕ} (S : QuadraticSystem n m)
    (hB : ∀ i, (S.B i).IsHermitian) (hd : ∀ i, 0 ≤ S.d i)
    (hstrict : S.StrictlyFeasible)
    (hpd : ∃ μ : Fin m → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • S.B i).PosDef)
    (hAh : S.A.IsHermitian)
    (Fstar : ℝ) (hF : S.IsSDPValue Fstar) :
    S.SDDSolvableWithValue Fstar := by
  classical
  obtain ⟨μ, hμ0, hμpd⟩ := hpd
  have hF0 : (sddD_bd (-S.A) (0 : Matrix (Fin m) (Fin m) ℝ)).IsHermitian := sddD_bd_herm hAh.neg isHermitian_zero
  have hFs : ∀ i, (sddD_Fs S i).IsHermitian := fun i =>
    sddD_bd_herm (hB i) (isHermitian_diagonal _)
  -- primal strict feasibility
  have hQ : (∑ i, S.B i - S.A).IsHermitian := by
    refine IsHermitian.sub ?_ hAh
    rw [IsHermitian, conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => hB i
  obtain ⟨t, ht, htpd⟩ := sddD_shift hμpd hQ
  have hprim : ∃ x, (VBSDP.Duality.lmi (sddD_bd (-S.A) (0 : Matrix (Fin m) (Fin m) ℝ)) (sddD_Fs S) x).PosDef := by
    refine ⟨fun i => t * μ i + 1, ?_⟩
    rw [sddD_lmi_eq]
    refine sddD_bd_posDef ?_ ?_
    · convert htpd using 1
      simp only [add_smul, mul_smul, Finset.sum_add_distrib, one_smul, Finset.smul_sum]
      abel
    · rw [posDef_diagonal_iff]
      intro i
      have := hμ0 i
      positivity
  -- dual strict feasibility
  obtain ⟨x0, hx0⟩ := hstrict
  have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      ∀ i, ε * (S.B i).trace < S.d i - x0 ⬝ᵥ (S.B i *ᵥ x0) := by
    rw [Filter.eventually_all]
    intro i
    have hlim : Filter.Tendsto (fun ε : ℝ => ε * (S.B i).trace) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (0 * (S.B i).trace)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds (Filter.tendsto_id.mul_const _))
    rw [zero_mul] at hlim
    exact hlim.eventually (gt_mem_nhds (by linarith [hx0 i]))
  obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hεpos' : 0 < ε := hεpos
  set Z11 : Matrix (Fin n) (Fin n) ℝ := vecMulVec x0 x0 + ε • 1 with hZ11
  have hZ11pd : Z11.PosDef := by
    have h1 := posSemidef_vecMulVec_self_star x0
    have h1' : (vecMulVec x0 x0).PosSemidef := by simpa using h1
    exact PosDef.posSemidef_add h1' (PosDef.one.smul hεpos')
  have hBZ : ∀ i, (S.B i * Z11).trace = x0 ⬝ᵥ (S.B i *ᵥ x0) + ε * (S.B i).trace := by
    intro i
    rw [hZ11, mul_add, trace_add, mul_vecMulVec, trace_vecMulVec, dotProduct_comm, mul_smul_comm,
      mul_one, trace_smul, smul_eq_mul]
  have hdual : ∃ Z : Matrix (Fin (n+m)) (Fin (n+m)) ℝ, Z.PosDef ∧
      ∀ i, (sddD_Fs S i * Z).trace = S.d i := by
    refine ⟨sddD_bd Z11 (diagonal fun i => S.d i - (S.B i * Z11).trace), sddD_bd_posDef hZ11pd ?_,
      fun i => ?_⟩
    · rw [posDef_diagonal_iff]
      intro i
      have := hε i
      rw [hBZ]
      linarith
    · rw [sddD_Fs_trace]
      have e1 : (sddD_bd Z11 (diagonal fun i => S.d i - (S.B i * Z11).trace)).submatrix
          (Fin.castAdd m) (Fin.castAdd m) = Z11 := by
        ext a b; simp [sddD_bd_ll]
      rw [e1, sddD_bd_rr]
      simp
  have key := VBSDP.Duality.theorem_3_1 S.d (sddD_bd (-S.A) (0 : Matrix (Fin m) (Fin m) ℝ)) (sddD_Fs S) hF0 hFs
  have hpd_eq := key.1 (Or.inl hprim)
  obtain ⟨lam, hlamf, hlamv⟩ := (key.2 ⟨hprim, hdual⟩).1
  have hlamf' : (sddD_bd (∑ i, lam i • S.B i - S.A) (diagonal lam)).PosSemidef := by
    have := hlamf
    unfold VBSDP.Duality.IsPrimalFeasible at this
    rwa [sddD_lmi_eq] at this
  have hfeas : S.SDDFeasible lam := by
    refine ⟨sddD_bd_psd_left hlamf', fun i => ?_⟩
    have := (sddD_bd_psd_right hlamf').diag_nonneg (i := i)
    simpa using this
  have hval : S.d ⬝ᵥ lam = ∑ i, lam i * S.d i := by
    simp [dotProduct, mul_comm]
  have hlow : ∀ lam', S.SDDFeasible lam' → Fstar ≤ ∑ i, lam' i * S.d i := by
    intro lam' hl
    apply hF.2
    rintro _ ⟨X, hX, rfl⟩
    exact sddD_weak S hl hX
  have hup : VBSDP.Duality.dStar S.d (sddD_bd (-S.A) (0 : Matrix (Fin m) (Fin m) ℝ)) (sddD_Fs S) ≤ (Fstar : EReal) := by
    apply sSup_le
    rintro _ ⟨Z, ⟨hZp, hZc⟩, rfl⟩
    rw [EReal.coe_le_coe_iff, sddD_F0_trace]
    apply hF.1
    refine ⟨_, ⟨fun i => ?_, hZp.submatrix _⟩, rfl⟩
    have h1 := hZc i
    rw [sddD_Fs_trace] at h1
    have h2 := hZp.diag_nonneg (i := Fin.natAdd n i)
    have h3 : 0 ≤ Z (Fin.natAdd n i) (Fin.natAdd n i) := h2
    linarith
  have hr : ∑ i, lam i * S.d i ≤ Fstar := by
    have h := hlamv.trans_le (hpd_eq.trans_le hup)
    rw [EReal.coe_le_coe_iff, hval] at h
    exact h
  refine ⟨⟨lam, hfeas, le_antisymm hr (hlow lam hfeas)⟩, ?_⟩
  rintro _ ⟨lam', hl, rfl⟩
  exact hlow lam' hl

end NY99


open Matrix
open ModernConvex.Relaxations

namespace NRT100

theorem rank_ge_one {n m : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (B i).PosSemidef) (hsum : (∑ i, B i).PosDef) (hn : 0 < n) :
    (1 : ℝ) ≤ ∑ i, ((B i).rank : ℝ) := by
  classical
  have hex : ∃ i, B i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : (∑ i, B i) = 0 := Finset.sum_eq_zero (fun i _ => h i)
    have := hsum.dotProduct_mulVec_pos (x := Pi.single (⟨0, hn⟩ : Fin n) (1:ℝ)) (by simp)
    simp [h0] at this
  obtain ⟨i, hi⟩ := hex
  have hr : (B i).rank ≠ 0 := by
    intro hr
    rw [(hB i).1.rank_eq_card_non_zero_eigs, Fintype.card_eq_zero_iff] at hr
    apply hi
    rw [← (hB i).1.eigenvalues_eq_zero_iff]
    funext k
    by_contra hk
    exact hr.false ⟨k, hk⟩
  have h1 : (1 : ℝ) ≤ ((B i).rank : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
  calc (1 : ℝ) ≤ ((B i).rank : ℝ) := h1
    _ ≤ ∑ i, ((B i).rank : ℝ) :=
      Finset.single_le_sum (f := fun i => ((B i).rank : ℝ)) (fun _ _ => by positivity)
        (Finset.mem_univ i)

theorem quad_conj {n : ℕ} (P N : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((Pᵀ * N * P) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (N *ᵥ (P *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem sg_sq {n : ℕ} (ξ : Fin n → Bool) (j : Fin n) : sg ξ j * sg ξ j = 1 := by
  unfold sg; split_ifs <;> norm_num

theorem diag_quad {n : ℕ} (c : Fin n → ℝ) (ξ : Fin n → Bool) :
    sg ξ ⬝ᵥ (diagonal c *ᵥ sg ξ) = ∑ j, c j := by
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have := sg_sq ξ j
  calc sg ξ j * (c j * sg ξ j) = c j * (sg ξ j * sg ξ j) := by ring
    _ = c j := by rw [this, mul_one]

theorem sum_rows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ∑ k, M k ⬝ᵥ M k = (M * Mᵀ).trace := by
  simp [trace, mul_apply, dotProduct]

theorem quad_rows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = ∑ k, (M k ⬝ᵥ x) ^ 2 := by
  simp [dotProduct, mulVec, sq]

theorem round {n m : ℕ} (S : QuadraticSystem n m) (hA : S.A.IsHermitian)
    (hB : ∀ i, (S.B i).PosSemidef) (hsum : (∑ i, S.B i).PosDef) (hn : 0 < n)
    (fstar : ℝ) (hf : S.IsPValue fstar) (X : Matrix (Fin n) (Fin n) ℝ) (hX : S.SDPFeasible X) :
    (S.A * X).trace ≤ 2 * Real.log (2 * ∑ i, ((S.B i).rank : ℝ)) * fstar := by
  classical
  set R : ℝ := ∑ i, ((S.B i).rank : ℝ) with hRdef
  have hR1 : 1 ≤ R := rank_ge_one S.B hB hsum hn
  set ρ : ℝ := 2 * Real.log (2 * R) with hρdef
  have hρ : 0 < ρ := by
    have : 1 < 2 * R := by linarith
    have := Real.log_pos this
    positivity
  obtain ⟨G, hG, c, hc⟩ := diag_factor hX.2 hA
  choose F s hF hFs hcard using fun i => psd_factor (hB i)
  let ι := Σ i : Fin m, (s i)
  have hcardι : (Fintype.card ι : ℝ) = R := by
    rw [hRdef, Fintype.card_sigma]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.card_coe, hcard i]
  let a : ι → Fin n → ℝ := fun p => (F p.1 * G) p.2
  obtain ⟨ξ, hξ⟩ := rad_union a R hcardι.le hR1
  set ζ : Fin n → ℝ := G *ᵥ sg ξ with hζdef
  -- objective value
  have hobj : ζ ⬝ᵥ (S.A *ᵥ ζ) = (S.A * X).trace := by
    rw [hζdef, ← quad_conj, hc, diag_quad, ← hG]
    have : (Gᵀ * S.A * G).trace = (S.A * (G * Gᵀ)).trace := by
      rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
    rw [← this, hc, trace_diagonal]
  -- constraint values
  have hcon : ∀ i, ζ ⬝ᵥ (S.B i *ᵥ ζ) ≤ ρ * S.d i := by
    intro i
    have h1 : ζ ⬝ᵥ (S.B i *ᵥ ζ) = ∑ k, ((F i * G) k ⬝ᵥ sg ξ) ^ 2 := by
      rw [← hF i, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hζdef, mulVec_mulVec,
        quad_rows]
    have h2 : ∀ k, ((F i * G) k ⬝ᵥ sg ξ) ^ 2 ≤ ρ * ((F i * G) k ⬝ᵥ (F i * G) k) := by
      intro k
      by_cases hk : k ∈ s i
      · exact hξ ⟨i, ⟨k, hk⟩⟩
      · have h0 : (F i * G) k = 0 := by
          funext j
          simp [mul_apply, hFs i k hk]
        rw [h0]; simp
    have h3 : ∑ k, (F i * G) k ⬝ᵥ (F i * G) k = (S.B i * X).trace := by
      rw [sum_rows, ← hF i, ← hG, transpose_mul]
      have : F i * G * (Gᵀ * (F i)ᵀ) = F i * (G * Gᵀ * (F i)ᵀ) := by
        simp only [Matrix.mul_assoc]
      rw [this, trace_mul_comm, Matrix.mul_assoc]
      exact trace_mul_comm _ _
    rw [h1]
    calc ∑ k, ((F i * G) k ⬝ᵥ sg ξ) ^ 2 ≤ ∑ k, ρ * ((F i * G) k ⬝ᵥ (F i * G) k) :=
          Finset.sum_le_sum (fun k _ => h2 k)
      _ = ρ * (S.B i * X).trace := by rw [← Finset.mul_sum, h3]
      _ ≤ ρ * S.d i := mul_le_mul_of_nonneg_left (hX.1 i) hρ.le
  -- scaled point
  set t : ℝ := (Real.sqrt ρ)⁻¹ with htdef
  have ht2 : t * t = ρ⁻¹ := by
    rw [htdef, ← mul_inv, Real.mul_self_sqrt hρ.le]
  have hquad : ∀ M : Matrix (Fin n) (Fin n) ℝ, (t • ζ) ⬝ᵥ (M *ᵥ (t • ζ)) = ρ⁻¹ * (ζ ⬝ᵥ (M *ᵥ ζ)) := by
    intro M
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ht2]
  have hsol : S.Solves (t • ζ) := by
    intro i
    rw [hquad]
    have := hcon i
    calc ρ⁻¹ * (ζ ⬝ᵥ (S.B i *ᵥ ζ)) ≤ ρ⁻¹ * (ρ * S.d i) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hρ.le)
      _ = S.d i := by field_simp
  have hle := hf.1 ⟨t • ζ, hsol, rfl⟩
  simp only at hle
  rw [hquad, hobj] at hle
  have := mul_le_mul_of_nonneg_left hle hρ.le
  rwa [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at this

theorem main {n m : ℕ} (S : QuadraticSystem n m) (hA : S.A.IsHermitian)
    (hB : ∀ i, (S.B i).PosSemidef) (hd : ∀ i, 0 < S.d i) (hsum : (∑ i, S.B i).PosDef)
    (fstar Fstar : ℝ) (hf : S.IsPValue fstar) (hF : S.IsSDPValue Fstar) :
    0 ≤ fstar ∧ S.SDDSolvableWithValue Fstar ∧
      Fstar ≤ 2 * Real.log (2 * ∑ i, ((S.B i).rank : ℝ)) * fstar := by
  have h0 : S.Solves 0 := fun i => by simpa using (hd i).le
  have hf0 : 0 ≤ fstar := by
    have := hf.1 ⟨0, h0, rfl⟩
    simpa using this
  refine ⟨hf0, ?_, ?_⟩
  · refine NY99.ny_sdd S (fun i => (hB i).1) (fun i => (hd i).le) ⟨0, fun i => by simpa using hd i⟩
      ⟨fun _ => 1, fun _ => zero_le_one, by simpa using hsum⟩ hA Fstar hF
  · refine hF.2 ?_
    rintro _ ⟨X, hX, rfl⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : (S.A * X).trace = 0 := by simp [trace]
      show (S.A * X).trace ≤ _
      rw [this]
      have : (S.B = fun _ => 0) := by funext i; ext a; exact a.elim0
      simp [this]
    · exact round S hA hB hsum hn fstar hf X hX

end NRT100

open Matrix
open ModernConvex.Relaxations

theorem solution {n m : ℕ} (S : QuadraticSystem n m) (hA : S.A.IsHermitian)
    (hB : ∀ i, (S.B i).PosSemidef) (hd : ∀ i, 0 < S.d i) (hsum : (∑ i, S.B i).PosDef)
    (fstar Fstar : ℝ) (hf : S.IsPValue fstar) (hF : S.IsSDPValue Fstar) :
    0 ≤ fstar ∧ S.SDDSolvableWithValue Fstar ∧
      Fstar ≤ 2 * Real.log (2 * ∑ i, ((S.B i).rank : ℝ)) * fstar :=
  NRT100.main S hA hB hd hsum fstar Fstar hf hF
