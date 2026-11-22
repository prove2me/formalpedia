-- Prove2me | solution 1 for MixedCloning.Optimal.werner_pure_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:09:11.69967+00:00
-- url     : https://prove2.me/submissions/6182dd22-ea77-4ef7-8755-fd9fc6868a4c

import Theorems.Thm_MixedCloning_Optimal_werner_trace_bose

noncomputable section
open Matrix
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

section PureFidelity
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma wpf_pure_eq (w : ι → ℂ) : MixedCloning.Optimal.pure w = vecMulVec w (star w) := by
  ext i j
  simp [MixedCloning.Optimal.pure, vecMulVec]

lemma wpf_pure_nonneg (w : ι → ℂ) : 0 ≤ MixedCloning.Optimal.pure w := by
  rw [wpf_pure_eq]
  exact (posSemidef_vecMulVec_self_star w).nonneg

/-- On positive matrices the two square roots agree. -/
lemma wpf_cfc_sqrt_eq (A : Matrix ι ι ℂ) (hA : 0 ≤ A) : cfc Real.sqrt A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA,
    cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero)]

/-- `star w ⬝ᵥ w` is the real number `Σ |w_i|²`. -/
lemma wpf_dot_self (w : ι → ℂ) : star w ⬝ᵥ w = (((star w ⬝ᵥ w).re : ℝ) : ℂ) := by
  have h := dotProduct_star_self_nonneg w
  apply Complex.ext
  · simp
  · simpa using (Complex.nonneg_iff.mp h).2.symm

lemma wpf_dot_self_re_nonneg (w : ι → ℂ) : 0 ≤ (star w ⬝ᵥ w).re :=
  (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg w)).1

/-- Square root of a rank-one positive matrix: `√(|w⟩⟨w|) = s^{-1/2} |w⟩⟨w|`, `s = ⟨w,w⟩`. -/
lemma wpf_sqrt_pure (w : ι → ℂ) :
    cfc Real.sqrt (MixedCloning.Optimal.pure w) =
      (((Real.sqrt (star w ⬝ᵥ w).re)⁻¹ : ℝ) : ℂ) • MixedCloning.Optimal.pure w := by
  rw [wpf_cfc_sqrt_eq _ (wpf_pure_nonneg w)]
  by_cases hw : w = 0
  · subst hw
    have h0 : MixedCloning.Optimal.pure (0 : ι → ℂ) = 0 := by
      ext i j; simp [MixedCloning.Optimal.pure]
    rw [h0, CFC.sqrt_zero, smul_zero]
  · set s := (star w ⬝ᵥ w).re with hs
    have hspos : 0 < s := by
      rcases lt_or_eq_of_le (wpf_dot_self_re_nonneg w) with h | h
      · exact h
      · exfalso
        apply hw
        apply dotProduct_star_self_eq_zero.mp
        rw [wpf_dot_self w, ← h]
        simp
    have hc : (0 : ℂ) ≤ (((Real.sqrt s)⁻¹ : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (inv_nonneg.mpr (Real.sqrt_nonneg s))
    apply CFC.sqrt_unique
    · have hPP : MixedCloning.Optimal.pure w * MixedCloning.Optimal.pure w =
          (star w ⬝ᵥ w) • MixedCloning.Optimal.pure w := by
        rw [wpf_pure_eq, vecMulVec_mul_vecMulVec, vecMulVec_smul]
      have hscal : ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * (((Real.sqrt s)⁻¹ : ℝ) : ℂ)) * (star w ⬝ᵥ w) = 1 := by
        rw [wpf_dot_self w, ← hs]
        have : (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ * s = 1 := by
          rw [← mul_inv, Real.mul_self_sqrt hspos.le, inv_mul_cancel₀ hspos.ne']
        exact_mod_cast this
      rw [smul_mul_smul_comm, hPP, smul_smul, hscal, one_smul]
    · rw [wpf_pure_eq]
      exact ((posSemidef_vecMulVec_self_star w).smul hc).nonneg

/-- Fidelity with a pure state: `F(σ, |φ⟩⟨φ|) = ⟨φ|σ|φ⟩` for positive semidefinite `σ`. -/
lemma wpf_fidelity_pure (σ : Matrix ι ι ℂ) (hσ : σ.PosSemidef) (φ : ι → ℂ) :
    fidelity σ (MixedCloning.Optimal.pure φ) = (star φ ⬝ᵥ (σ *ᵥ φ)).re := by
  set S := cfc Real.sqrt σ with hSdef
  have hS : S = CFC.sqrt σ := wpf_cfc_sqrt_eq σ hσ.nonneg
  have hSsa : IsSelfAdjoint S := cfc_predicate Real.sqrt σ
  have hSh : Sᴴ = S := hSsa.star_eq
  have hSS : S * S = σ := by rw [hS]; exact CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  have hmid : S * MixedCloning.Optimal.pure φ * S = MixedCloning.Optimal.pure (S *ᵥ φ) := by
    rw [wpf_pure_eq, wpf_pure_eq, mul_vecMulVec, vecMulVec_mul]
    congr 1
    rw [star_mulVec, hSh]
  have hw : star (S *ᵥ φ) ⬝ᵥ (S *ᵥ φ) = star φ ⬝ᵥ (σ *ᵥ φ) := by
    rw [star_mulVec, hSh, ← dotProduct_mulVec, mulVec_mulVec, hSS]
  have hs0 : 0 ≤ (star φ ⬝ᵥ (σ *ᵥ φ)).re := by rw [← hw]; exact wpf_dot_self_re_nonneg _
  unfold fidelity QAlgorithms.rootFidelity
  rw [← hSdef, hmid, wpf_sqrt_pure, Matrix.trace_smul, wpf_pure_eq, trace_vecMulVec,
    dotProduct_comm (S *ᵥ φ) (star (S *ᵥ φ)), wpf_dot_self (S *ᵥ φ), hw]
  simp only [Complex.ofReal_re, smul_eq_mul, ← Complex.ofReal_mul]
  rcases lt_or_eq_of_le hs0 with h | h
  · rw [inv_mul_eq_div, Real.div_sqrt, Real.sq_sqrt hs0]
  · rw [← h]; simp

/-- A Hermitian matrix fixing `ψ` absorbs `|ψ⟩⟨ψ|` from both sides. -/
lemma wpf_proj_mul_pure (P : Matrix ι ι ℂ) (hP : Pᴴ = P) (ψ : ι → ℂ) (hψ : P *ᵥ ψ = ψ) :
    P * MixedCloning.Optimal.pure ψ = MixedCloning.Optimal.pure ψ ∧
      MixedCloning.Optimal.pure ψ * P = MixedCloning.Optimal.pure ψ := by
  rw [wpf_pure_eq]
  refine ⟨by rw [mul_vecMulVec, hψ], ?_⟩
  rw [vecMulVec_mul]
  congr 1
  have h := star_mulVec P ψ
  rw [hψ, hP] at h
  exact h.symm

end PureFidelity

section Werner
variable {a : Type} [Fintype a]

/-- `(|u⟩⟨u|)^{⊗m} = |u^{⊗m}⟩⟨u^{⊗m}|`. -/
lemma wb_tensorPower_pure (m : ℕ) (u : a → ℂ) :
    tensorPower m (MixedCloning.Optimal.pure u) =
      MixedCloning.Optimal.pure (fun i : Word a m => ∏ t, u (i t)) := by
  ext i j
  simp only [tensorPower, MixedCloning.Optimal.pure, Finset.prod_mul_distrib, map_prod]

/-- Permuting the tensor factors fixes the product vector `u^{⊗m}`. -/
lemma wb_perm_mulVec (m : ℕ) (u : a → ℂ) (p : Equiv.Perm (Fin m)) :
    permMatrix (a := a) m p *ᵥ (fun i : Word a m => ∏ t, u (i t)) = fun i => ∏ t, u (i t) := by
  ext i
  simp only [mulVec, dotProduct, permMatrix, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (i ∘ p)]
  · rw [if_pos (by ext t; simp)]
    exact Equiv.prod_comp p (fun t => u (i t))
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    rw [h]
    ext t
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The symmetric projector fixes `u^{⊗m}`. -/
lemma wb_symProjector_mulVec (m : ℕ) (u : a → ℂ) :
    symProjector a m *ᵥ (fun i : Word a m => ∏ t, u (i t)) = fun i => ∏ t, u (i t) := by
  unfold symProjector
  rw [smul_mulVec, sum_mulVec]
  simp only [wb_perm_mulVec, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero m)), one_smul]

lemma wb_permMatrix_conjTranspose (m : ℕ) (p : Equiv.Perm (Fin m)) :
    (permMatrix (a := a) m p)ᴴ = permMatrix m p⁻¹ := by
  ext i j
  simp only [conjTranspose_apply, permMatrix, Equiv.Perm.inv_def, Equiv.symm_symm]
  by_cases h : j = i ∘ p.symm
  · rw [if_pos h, if_pos]
    · simp
    · rw [h]; ext t; simp
  · rw [if_neg h, if_neg]
    · simp
    · intro h'
      apply h
      rw [h']
      ext t
      simp

/-- The symmetric projector is Hermitian. -/
lemma wb_symProjector_conjTranspose (m : ℕ) : (symProjector a m)ᴴ = symProjector a m := by
  unfold symProjector
  rw [conjTranspose_smul, conjTranspose_sum]
  simp only [wb_permMatrix_conjTranspose]
  have hsum : ∑ x : Equiv.Perm (Fin m), permMatrix (a := a) m x⁻¹ = ∑ p, permMatrix m p :=
    Equiv.sum_comp (Equiv.inv _) (fun p => permMatrix (a := a) m p)
  rw [hsum]
  congr 1
  simp

/-- On a symmetric pure input the completion term vanishes and `Π_n X Π_n = X`. -/
lemma wb_werner_eq (n k : ℕ) (tau : Op (Word a (n+k))) (ψ : Word a n → ℂ)
    (hψ : symProjector a n *ᵥ ψ = ψ) :
    werner a n k tau (MixedCloning.Optimal.pure ψ) =
      ((symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k)) •
        (symProjector a (n+k) * appendIdentity n k (MixedCloning.Optimal.pure ψ) *
          symProjector a (n+k)) := by
  obtain ⟨hl, hr⟩ := wpf_proj_mul_pure (symProjector a n) (wb_symProjector_conjTranspose n) ψ hψ
  simp only [werner]
  rw [hl, hr, sub_mul, one_mul, hl, sub_self, Matrix.trace_zero, zero_smul, add_zero]

/-- `|ψ⟩⟨ψ| ⊗ I = Bᴴ B` for an explicit `B`, hence positive semidefinite. -/
lemma wb_appendIdentity_pure (n k : ℕ) (ψ : Word a n → ℂ) :
    ∃ B : Matrix (Word a k) (Word a (n+k)) ℂ,
      appendIdentity n k (MixedCloning.Optimal.pure ψ) = Bᴴ * B := by
  refine ⟨Matrix.of fun z j => star (ψ (fun t => j (Fin.castAdd k t))) *
    (if (fun t => j (Fin.natAdd n t)) = z then 1 else 0), ?_⟩
  ext i j
  simp only [appendIdentity, MixedCloning.Optimal.pure, mul_apply, conjTranspose_apply,
    Matrix.of_apply, star_mul', star_star, apply_ite star, star_one, star_zero]
  rw [Finset.sum_eq_single (fun t => i (Fin.natAdd n t))]
  · by_cases h : (fun t : Fin k => i (Fin.natAdd n t)) = (fun t => j (Fin.natAdd n t))
    · simp [h, RCLike.star_def, mul_comm]
    · rw [if_neg h, if_neg (Ne.symm h)]
      simp
  · intro z _ hz
    rw [if_neg (Ne.symm hz)]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `Σ_i |u^{⊗m}(i)|² = (Σ_x |u x|²)^m = 1`. -/
lemma wb_dot_prod (m : ℕ) (u : a → ℂ) (hu : ∑ x, u x * star (u x) = 1) :
    star (fun i : Word a m => ∏ t, u (i t)) ⬝ᵥ (fun i : Word a m => ∏ t, u (i t)) = 1 := by
  simp only [dotProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (x : a) => star (u x) * u x)]
  have h1 : ∑ x, (starRingEnd ℂ) (u x) * u x = 1 := by
    rw [← hu]
    exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm]; rfl)
  simp only [RCLike.star_def, h1, Finset.prod_const_one]

/-- `(|ψ⟩⟨ψ| ⊗ I) φ = φ` for `ψ = u^{⊗n}`, `φ = u^{⊗(n+k)}` with `‖u‖ = 1`. -/
lemma wb_appendIdentity_mulVec (n k : ℕ) (u : a → ℂ) (hu : ∑ x, u x * star (u x) = 1) :
    appendIdentity n k (MixedCloning.Optimal.pure (fun i : Word a n => ∏ t, u (i t))) *ᵥ
        (fun i : Word a (n+k) => ∏ t, u (i t)) = fun i => ∏ t, u (i t) := by
  ext i
  have hdot := wb_dot_prod n u hu
  simp only [dotProduct, Pi.star_apply] at hdot
  simp only [mulVec, dotProduct, appendIdentity, MixedCloning.Optimal.pure]
  rw [← (Fin.appendEquiv n k).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.appendEquiv_apply, Fin.append_left, Fin.append_right, Fin.prod_univ_add]
  have hfun : ∀ (y : Fin n → a) (z : Fin k → a),
      (fun t : Fin k => Fin.append y z (Fin.natAdd n t)) = z := fun y z => by
    ext t; simp
  have hfun' : ∀ (y : Fin n → a) (z : Fin k → a),
      (fun t : Fin n => Fin.append y z (Fin.castAdd k t)) = y := fun y z => by
    ext t; simp
  simp only [hfun, hfun', mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc ∑ y : Fin n → a, (∏ t, u (i (Fin.castAdd k t))) * (starRingEnd ℂ) (∏ t, u (y t)) *
          ((∏ t, u (y t)) * ∏ t, u (i (Fin.natAdd n t)))
        = (∏ t, u (i (Fin.castAdd k t))) * (∏ t, u (i (Fin.natAdd n t))) *
            ∑ y : Fin n → a, star (∏ t, u (y t)) * ∏ t, u (y t) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          simp only [RCLike.star_def]
          ring
    _ = _ := by
          simp only [star_prod] at hdot ⊢
          rw [hdot, mul_one]

end Werner

theorem solution {a : Type} [Fintype a] [DecidableEq a] (n k : ℕ) (tau : Op (Word a (n+k)))
    (v : EuclideanSpace ℂ a) (hv : ‖v‖ = 1) :
    IsState (werner a n k tau (tensorPower n (pure v))) ∧
    fidelity (werner a n k tau (tensorPower n (pure v))) (tensorPower (n+k) (pure v)) =
      (symDimension (Fintype.card a) n : ℝ) / symDimension (Fintype.card a) (n+k) := by
  -- normalisation of `v`
  have hu : ∑ x, v.ofLp x * star (v.ofLp x) = 1 := by
    have h1 : ∑ x, ‖v x‖ ^ 2 = 1 := by
      have h := EuclideanSpace.norm_eq v
      rw [hv] at h
      have h2 := congrArg (· ^ 2) h
      simp only [one_pow] at h2
      rw [h2, Real.sq_sqrt (Finset.sum_nonneg (fun x _ => sq_nonneg _))]
    have h3 : ∀ x, v.ofLp x * star (v.ofLp x) = ((‖v x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [h3]
    exact_mod_cast h1
  set D := Fintype.card a with hD
  have hDpos : 0 < D := by
    rw [hD, Fintype.card_pos_iff]
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hu
  have hdpos : ∀ m, 0 < symDimension D m := fun m => by
    unfold symDimension; exact Nat.choose_pos (by omega)
  have hdn : (symDimension D n : ℂ) ≠ 0 := by exact_mod_cast (hdpos n).ne'
  have hdnk : (symDimension D (n+k) : ℂ) ≠ 0 := by exact_mod_cast (hdpos (n+k)).ne'
  set ψ : Word a n → ℂ := fun i => ∏ t, v.ofLp (i t) with hψdef
  set φ : Word a (n+k) → ℂ := fun i => ∏ t, v.ofLp (i t) with hφdef
  have hψ : symProjector a n *ᵥ ψ = ψ := wb_symProjector_mulVec n v.ofLp
  have hφ : symProjector a (n+k) *ᵥ φ = φ := wb_symProjector_mulVec (n+k) v.ofLp
  rw [wb_tensorPower_pure n v.ofLp, wb_tensorPower_pure (n+k) v.ofLp, ← hψdef, ← hφdef,
    wb_werner_eq n k tau ψ hψ]
  set c : ℂ := (symDimension D n : ℂ) / symDimension D (n+k) with hc
  set Q := symProjector a (n+k)
  set A := appendIdentity n k (MixedCloning.Optimal.pure ψ)
  have hcreal : c = ((((symDimension D n : ℝ) / symDimension D (n+k)) : ℝ) : ℂ) := by
    rw [hc]; push_cast; rfl
  have hc0 : (0 : ℂ) ≤ c := by
    rw [hcreal]; exact Complex.zero_le_real.mpr (by positivity)
  -- positivity of the output
  have hpsd : (c • (Q * A * Q)).PosSemidef := by
    obtain ⟨B, hB⟩ := wb_appendIdentity_pure n k ψ
    have hB' : A = Bᴴ * B := hB
    have hQ : Qᴴ = Q := wb_symProjector_conjTranspose (n+k)
    have : Q * A * Q = (B * Q)ᴴ * (B * Q) := by
      rw [hB', conjTranspose_mul, hQ]
      simp only [Matrix.mul_assoc]
    rw [this]
    exact (posSemidef_conjTranspose_mul_self (B * Q)).smul hc0
  -- trace one, from the trace-preservation child
  have htrX : (MixedCloning.Optimal.pure ψ).trace = 1 := by
    rw [wpf_pure_eq, trace_vecMulVec, dotProduct_comm]
    exact wb_dot_prod n v.ofLp hu
  have hchild := werner_trace_bose (a := a) n k (MixedCloning.Optimal.pure ψ)
  obtain ⟨hl, hr⟩ := wpf_proj_mul_pure (symProjector a n) (wb_symProjector_conjTranspose n) ψ hψ
  rw [hl, hr, htrX, mul_one] at hchild
  have htr : (c • (Q * A * Q)).trace = 1 := by
    rw [Matrix.trace_smul, smul_eq_mul, hc]
    field_simp
    exact hchild
  refine ⟨⟨hpsd, htr⟩, ?_⟩
  -- the fidelity value
  rw [wpf_fidelity_pure _ hpsd φ, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hφ,
    wb_appendIdentity_mulVec n k v.ofLp hu, hφ, dotProduct_smul, wb_dot_prod (n+k) v.ofLp hu,
    smul_eq_mul, mul_one, hcreal, Complex.ofReal_re]
