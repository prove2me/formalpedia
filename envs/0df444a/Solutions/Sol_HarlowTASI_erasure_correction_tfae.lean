-- Prove2me | solution 1 for HarlowTASI.erasure_correction_tfae
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T14:59:35.985716+00:00
-- url     : https://prove2.me/submissions/a68e8037-8f22-4389-90b3-bfac26814e37

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Matrix
open scoped Kronecker ComplexOrder

set_option maxHeartbeats 100000

namespace HarlowTASI

section ECT

variable {R Rb C : Type} [Fintype R] [DecidableEq R] [Fintype Rb] [DecidableEq Rb]
  [Fintype C] [DecidableEq C]

/-! ### (1) → (2) -/

lemma ect_12 (V : Matrix (R × Rb) C ℂ)
    (h1 : ∀ O : Matrix C C ℂ, ∃ OR : Matrix R R ℂ,
      (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧ (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ)
    (X : Matrix Rb Rb ℂ) :
    ∃ c : ℂ, (V * Vᴴ) * ((1 : Matrix R R ℂ) ⊗ₖ X) * (V * Vᴴ) = c • (V * Vᴴ) := by
  have hcomm : ∀ O : Matrix C C ℂ,
      O * (Vᴴ * ((1 : Matrix R R ℂ) ⊗ₖ X) * V) = (Vᴴ * ((1 : Matrix R R ℂ) ⊗ₖ X) * V) * O := by
    intro O
    obtain ⟨OR, h1, h2⟩ := h1 O
    have hk : ((1 : Matrix R R ℂ) ⊗ₖ X) * (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) =
        (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * ((1 : Matrix R R ℂ) ⊗ₖ X) := by
      rw [← mul_kronecker_mul, ← mul_kronecker_mul]; simp
    have h2' : Vᴴ * (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) = O * Vᴴ := by
      have := congrArg conjTranspose h2
      simpa [conjTranspose_mul, conjTranspose_kronecker] using this
    calc O * (Vᴴ * ((1 : Matrix R R ℂ) ⊗ₖ X) * V)
        = (O * Vᴴ) * ((1 : Matrix R R ℂ) ⊗ₖ X) * V := by simp only [Matrix.mul_assoc]
      _ = Vᴴ * (((OR ⊗ₖ (1 : Matrix Rb Rb ℂ))) * ((1 : Matrix R R ℂ) ⊗ₖ X)) * V := by
          rw [← h2']; simp only [Matrix.mul_assoc]
      _ = Vᴴ * (((1 : Matrix R R ℂ) ⊗ₖ X) * (OR ⊗ₖ (1 : Matrix Rb Rb ℂ))) * V := by rw [hk]
      _ = (Vᴴ * ((1 : Matrix R R ℂ) ⊗ₖ X) * V) * O := by simp only [Matrix.mul_assoc, h1]
  obtain ⟨c, hc⟩ : (Vᴴ * ((1 : Matrix R R ℂ) ⊗ₖ X) * V) ∈ Set.range (Matrix.scalar C) :=
    mem_range_scalar_iff_commute_single'.mpr fun i j => hcomm _
  refine ⟨c, ?_⟩
  calc (V * Vᴴ) * ((1 : Matrix R R ℂ) ⊗ₖ X) * (V * Vᴴ)
      = V * (Vᴴ * ((1 : Matrix R R ℂ) ⊗ₖ X) * V) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = c • (V * Vᴴ) := by
      rw [← hc, scalar_apply, ← smul_one_eq_diagonal]
      simp [Matrix.mul_smul, Matrix.smul_mul]

/-! ### The Gram-matrix condition `(G)` and its equivalence with (2), (3) -/

lemma ect_entry (V : Matrix (R × Rb) C ℂ) (b' b : Rb) (s' s : C) :
    (Vᴴ * ((1 : Matrix R R ℂ) ⊗ₖ Matrix.single b' b (1 : ℂ)) * V) s' s =
      ∑ r, star (V (r, b') s') * V (r, b) s := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Matrix.single_apply,
    Finset.sum_mul, ite_and]

lemma ect_2G (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (h2 : ∀ X : Matrix Rb Rb ℂ, ∃ c : ℂ,
      (V * Vᴴ) * ((1 : Matrix R R ℂ) ⊗ₖ X) * (V * Vᴴ) = c • (V * Vᴴ)) :
    ∃ g : Matrix Rb Rb ℂ, ∀ s s' b b',
      ∑ r, star (V (r, b') s') * V (r, b) s = if s' = s then g b' b else 0 := by
  have hV' : Vᴴ * V = 1 := hV
  have e1 : ∀ {n : Type} [Fintype n] (Y : Matrix C n ℂ), Vᴴ * (V * Y) = Y := by
    intro n _ Y; rw [← Matrix.mul_assoc, hV', Matrix.one_mul]
  choose c hc using fun p : Rb × Rb => h2 (Matrix.single p.1 p.2 1)
  refine ⟨fun b' b => c (b', b), fun s s' b b' => ?_⟩
  have := congrArg (fun M => (Vᴴ * M * V) s' s) (hc (b', b))
  simp only [Matrix.mul_assoc, e1, hV', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
  rw [← ect_entry, Matrix.mul_assoc, this]

/-- `|C|^{-1/2} · conj (|C|^{-1/2}) = |C|^{-1}`. -/
lemma ect_kappa (N : ℕ) :
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * star (((Real.sqrt N : ℝ) : ℂ)⁻¹) = (N : ℂ)⁻¹ := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

lemma ect_phi (V : Matrix (R × Rb) C ℂ) (x y : C × R × Rb) :
    codeReferenceState V x * star (codeReferenceState V y) =
      (Fintype.card C : ℂ)⁻¹ * (star (V (y.2.1, y.2.2) y.1) * V (x.2.1, x.2.2) x.1) := by
  simp only [codeReferenceState, star_mul']
  rw [← ect_kappa]; ring

lemma ect_SB (V : Matrix (R × Rb) C ℂ) (s s' : C) (b b' : Rb) :
    reducedSB (codeReferenceState V) (s, b) (s', b') =
      (Fintype.card C : ℂ)⁻¹ * ∑ r, star (V (r, b') s') * V (r, b) s := by
  simp only [reducedSB, ect_phi, Finset.mul_sum]

lemma ect_S (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V) (s s' : C) :
    reducedS (codeReferenceState V) s s' =
      (Fintype.card C : ℂ)⁻¹ * if s' = s then 1 else 0 := by
  have h := congrFun (congrFun (show Vᴴ * V = 1 from hV) s') s
  simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply] at h
  simp only [reducedS, ect_phi, ← Finset.mul_sum, h]

lemma ect_B (V : Matrix (R × Rb) C ℂ) (b b' : Rb) :
    reducedB (codeReferenceState V) b b' =
      (Fintype.card C : ℂ)⁻¹ * ∑ s, ∑ r, star (V (r, b') s) * V (r, b) s := by
  simp only [reducedB, ect_phi, ← Finset.mul_sum]

lemma ect_G3 [Nonempty C] (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V) (g : Matrix Rb Rb ℂ)
    (hG : ∀ s s' b b', ∑ r, star (V (r, b') s') * V (r, b) s = if s' = s then g b' b else 0) :
    reducedSB (codeReferenceState V) =
      reducedS (codeReferenceState V) ⊗ₖ reducedB (codeReferenceState V) := by
  have hN : (Fintype.card C : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext ⟨s, b⟩ ⟨s', b'⟩
  rw [kroneckerMap_apply, ect_SB, ect_S V hV, ect_B, hG]
  simp only [hG, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  split_ifs
  · field_simp
  · simp

lemma ect_3G [Nonempty C] (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (h3 : reducedSB (codeReferenceState V) =
      reducedS (codeReferenceState V) ⊗ₖ reducedB (codeReferenceState V)) :
    ∃ g : Matrix Rb Rb ℂ, ∀ s s' b b',
      ∑ r, star (V (r, b') s') * V (r, b) s = if s' = s then g b' b else 0 := by
  have hN : (Fintype.card C : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun b' b => reducedB (codeReferenceState V) b b', fun s s' b b' => ?_⟩
  have h := congrFun (congrFun h3 (s, b)) (s', b')
  rw [kroneckerMap_apply, ect_SB, ect_S V hV] at h
  have h' := congrArg (fun z => (Fintype.card C : ℂ) * z) h
  simp only at h'
  rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ hN, one_mul] at h'
  rw [h']
  split_ifs <;> simp

/-! ### (4) → (1) -/

/-- The block operator `O ⊗ 1` on `C × Fin q`, extended by zero on `Fin m`. -/
def ectBlock {q m : ℕ} (O : Matrix C C ℂ) :
    Matrix ((C × Fin q) ⊕ Fin m) ((C × Fin q) ⊕ Fin m) ℂ :=
  Matrix.fromBlocks (O ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) 0 0 0

lemma ectBlock_conjTranspose {q m : ℕ} (O : Matrix C C ℂ) :
    (ectBlock (q := q) (m := m) O)ᴴ = ectBlock Oᴴ := by
  simp [ectBlock, fromBlocks_conjTranspose, conjTranspose_kronecker]

/-- The column `F_i(r', b)` of the statement, as a function on the split index set. -/
def ectF {q m : ℕ} (χ : Fin q × Rb → ℂ) (y : (C × Fin q) ⊕ Fin m) (b : Rb) (i : C) : ℂ :=
  match y with
  | Sum.inl (c, k) => if c = i then χ (k, b) else 0
  | Sum.inr _ => 0

lemma ectBlock_F {q m : ℕ} (χ : Fin q × Rb → ℂ) (O : Matrix C C ℂ)
    (y : (C × Fin q) ⊕ Fin m) (b : Rb) (i : C) :
    ∑ z, ectBlock O y z * ectF χ z b i = ∑ c, ectF χ y b c * O c i := by
  rcases y with ⟨c, k⟩ | j
  · simp [ectBlock, ectF, Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.one_apply,
      ite_and]
    ring
  · simp [ectBlock, ectF, Fintype.sum_sum_type]

lemma ect_41 {q m : ℕ} (V : Matrix (R × Rb) C ℂ) (e : R ≃ (C × Fin q) ⊕ Fin m)
    (UR : Matrix R R ℂ) (hU : IsUnitaryMatrix UR) (χ : Fin q × Rb → ℂ)
    (hrep : ∀ (i : C) (r : R) (b : Rb), V (r, b) i = ∑ r', UR r r' * ectF χ (e r') b i)
    (O : Matrix C C ℂ) :
    ((UR * (ectBlock O).submatrix e e * URᴴ) ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O := by
  let W0 : Matrix (R × Rb) C ℂ := Matrix.of fun x i => ectF χ (e x.1) x.2 i
  have hVW : V = (UR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W0 := by
    ext ⟨r, b⟩ i
    rw [hrep, Matrix.mul_apply, Fintype.sum_prod_type]
    simp [Matrix.one_apply, W0]
  have hOW : ((ectBlock O).submatrix e e ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W0 = W0 * O := by
    ext ⟨r, b⟩ i
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [kroneckerMap_apply, submatrix_apply, Matrix.one_apply, mul_ite, mul_one,
      mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, W0, of_apply]
    rw [← ectBlock_F χ O (e r) b i]
    exact e.sum_comp (fun z => ectBlock O (e r) z * ectF χ z b i)
  have hU1 : URᴴ * UR = 1 := hU.1
  rw [hVW, ← Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.mul_assoc, hU1, Matrix.mul_one,
    Matrix.mul_one, ← Matrix.mul_one (1 : Matrix Rb Rb ℂ), mul_kronecker_mul, Matrix.mul_assoc,
    hOW, Matrix.mul_assoc, Matrix.mul_one]

lemma ect_41' {q m : ℕ} (V : Matrix (R × Rb) C ℂ) (e : R ≃ (C × Fin q) ⊕ Fin m)
    (UR : Matrix R R ℂ) (hU : IsUnitaryMatrix UR) (χ : Fin q × Rb → ℂ)
    (hrep : ∀ (i : C) (r : R) (b : Rb), V (r, b) i = ∑ r', UR r r' * ectF χ (e r') b i) :
    ∀ O : Matrix C C ℂ, ∃ OR : Matrix R R ℂ,
      (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧ (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ := by
  intro O
  refine ⟨UR * (ectBlock O).submatrix e e * URᴴ, ect_41 V e UR hU χ hrep O, ?_⟩
  have : (UR * (ectBlock O).submatrix e e * URᴴ)ᴴ = UR * (ectBlock Oᴴ).submatrix e e * URᴴ := by
    simp [conjTranspose_mul, conjTranspose_submatrix, ectBlock_conjTranspose, Matrix.mul_assoc]
  rw [this]
  exact ect_41 V e UR hU χ hrep Oᴴ

end ECT

section ECT2

variable {R Rb C : Type} [Fintype R] [DecidableEq R] [Fintype Rb] [DecidableEq Rb]
  [Fintype C] [DecidableEq C]

lemma ect_sum_sq {J K : Type} [Fintype J] [Fintype K] [DecidableEq K] (ι : J ↪ K)
    (a : J → ℂ) :
    ∑ k, ‖∑ j, if ι j = k then a j else 0‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 := by
  have h : ∀ k, ‖∑ j, if ι j = k then a j else 0‖ ^ 2 =
      ∑ j, if ι j = k then ‖a j‖ ^ 2 else 0 := by
    intro k
    by_cases hk : ∃ j0, ι j0 = k
    · obtain ⟨j0, rfl⟩ := hk
      rw [Finset.sum_eq_single j0, Finset.sum_eq_single j0]
      · simp
      · intro j _ hj; simp [ι.injective.eq_iff, hj]
      · simp
      · intro j _ hj; simp [ι.injective.eq_iff, hj]
      · simp
    · push_neg at hk
      simp [hk]
  simp only [h]
  rw [Finset.sum_comm]
  simp

/-- Columns of `V` for a fixed logical index, as an `R × Rb` matrix. -/
def ectA (V : Matrix (R × Rb) C ℂ) (s : C) : Matrix R Rb ℂ := fun r b => V (r, b) s

lemma ect_G4 [Nonempty C] (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V) (g : Matrix Rb Rb ℂ)
    (hG : ∀ s s' b b', ∑ r, star (V (r, b') s') * V (r, b) s = if s' = s then g b' b else 0) :
    Fintype.card C ≤ Fintype.card R ∧
      ∀ e : R ≃ (C × Fin (Fintype.card R / Fintype.card C)) ⊕
          Fin (Fintype.card R % Fintype.card C),
        ∃ UR : Matrix R R ℂ, IsUnitaryMatrix UR ∧
          ∃ χ : Fin (Fintype.card R / Fintype.card C) × Rb → ℂ,
            ∑ x, ‖χ x‖ ^ 2 = 1 ∧
            ∀ (i : C) (r : R) (b : Rb),
              V (r, b) i = ∑ r', UR r r' *
                (match e r' with
                  | Sum.inl (c, k) => if c = i then χ (k, b) else 0
                  | Sum.inr _ => 0) := by
  set A := ectA V with hAdef
  have hAA : ∀ s s', (A s')ᴴ * A s = if s' = s then g else 0 := by
    intro s s'; ext b' b
    simp only [hAdef, ectA, Matrix.mul_apply, conjTranspose_apply, hG]
    split_ifs <;> simp
  obtain ⟨s0⟩ := ‹Nonempty C›
  have hgP : g.PosSemidef := by
    have := posSemidef_conjTranspose_mul_self (A s0); rwa [hAA s0 s0, if_pos rfl] at this
  set hg := hgP.1 with hhg
  set ev := hg.eigenvalues with hev
  set u := hg.eigenvectorBasis with hu
  have hev0 : ∀ j, 0 ≤ ev j := hgP.eigenvalues_nonneg
  -- Gram matrix of the vectors `A s u j`
  have hAu : ∀ s s' j j', star (A s' *ᵥ u j') ⬝ᵥ (A s *ᵥ u j) =
      if s' = s ∧ j' = j then (ev j : ℂ) else 0 := by
    intro s s' j j'
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hAA]
    by_cases hs : s' = s
    · rw [if_pos hs, hg.mulVec_eigenvectorBasis]
      have ho := orthonormal_iff_ite.mp u.orthonormal j' j
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at ho
      simp only [hs, true_and]
      rw [dotProduct_smul, ho]
      split_ifs <;> simp [RCLike.real_smul_eq_coe_mul] <;> rfl
    · simp [hs]
  have hAu0 : ∀ s j, ev j = 0 → A s *ᵥ u j = 0 := by
    intro s j h0
    have := hAu s s j j
    simp only [and_self, if_true, h0, Complex.ofReal_zero] at this
    exact dotProduct_star_self_eq_zero.mp this
  -- trace of `g` is one
  have htr : ∑ j, ev j = 1 := by
    have h1 : g.trace = 1 := by
      have h := congrFun (congrFun (show Vᴴ * V = 1 from hV) s0) s0
      simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.one_apply, if_true] at h
      rw [Finset.sum_comm] at h
      simp only [hG, if_true] at h
      exact h
    rw [hg.trace_eq_sum_eigenvalues] at h1
    rw [hev]
    have h2 := congrArg Complex.re h1
    simpa [Complex.re_sum] using h2
  -- orthonormal family `w (s, j) = ev_j^{-1/2} A s u j`
  let J := {j : Rb // ev j ≠ 0}
  let w : C × J → EuclideanSpace ℂ R := fun p =>
    WithLp.toLp 2 ((((Real.sqrt (ev p.2.1))⁻¹ : ℝ) : ℂ) • (A p.1 *ᵥ u p.2.1))
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    rintro ⟨s', j', hj'⟩ ⟨s, j, hj⟩
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp only [w, WithLp.ofLp_toLp, star_smul, smul_dotProduct, dotProduct_smul, hAu,
      Prod.mk.injEq, Subtype.mk.injEq]
    by_cases h : s' = s ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true, smul_eq_mul, RCLike.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_assoc, ← mul_inv,
        Real.mul_self_sqrt (hev0 _), inv_mul_cancel₀ hj', Complex.ofReal_one]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, congrArg Subtype.val h'.2⟩)]; simp
  have hcard : Fintype.card C * Fintype.card J ≤ Fintype.card R := by
    have := hw.linearIndependent.fintype_card_le_finrank
    simpa [Fintype.card_prod, finrank_euclideanSpace] using this
  have hJpos : 0 < Fintype.card J := by
    by_contra hcon
    have hJ0 : ∀ j, ev j = 0 := by
      intro j; by_contra hj
      exact hcon (Fintype.card_pos_iff.mpr ⟨⟨j, hj⟩⟩)
    simp [hJ0] at htr
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hCR : Fintype.card C ≤ Fintype.card R :=
    le_trans (Nat.le_mul_of_pos_right _ hJpos) hcard
  have hJq : Fintype.card J ≤ Fintype.card R / Fintype.card C :=
    (Nat.le_div_iff_mul_le hCpos).mpr (by rw [mul_comm]; exact hcard)
  let ι : J ↪ Fin (Fintype.card R / Fintype.card C) :=
    (Fintype.equivFin J).toEmbedding.trans (Fin.castLEEmb hJq)
  refine ⟨hCR, fun e => ?_⟩
  -- the split index set and the orthonormal-basis extension
  let I' := (C × Fin (Fintype.card R / Fintype.card C)) ⊕ Fin (Fintype.card R % Fintype.card C)
  let f : C × J → I' := fun p => Sum.inl (p.1, ι p.2)
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Sum.inl_injective h)
    exact Prod.ext h1 (ι.injective h2)
  let v : I' → EuclideanSpace ℂ R := Function.extend f w 0
  have hcardI : Module.finrank ℂ (EuclideanSpace ℂ R) = Fintype.card I' := by
    simp only [finrank_euclideanSpace, I', Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact (Nat.div_add_mod _ _).symm
  have hvS : Orthonormal ℂ ((Set.range f).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, p, rfl⟩ ⟨_, p', rfl⟩
    simp only [Set.domRestrict_apply, v, hf.extend_apply, Subtype.mk.injEq, hf.eq_iff]
    rw [orthonormal_iff_ite.mp hw p p']
    by_cases hp : p = p'
    · subst hp; simp
    · rw [if_neg hp, if_neg]; intro h; exact hp (hf (congrArg Subtype.val h))
  obtain ⟨ob, hob⟩ := hvS.exists_orthonormalBasis_extension_of_card_eq hcardI
  have hobw : ∀ s (j : J), ob (Sum.inl (s, ι j)) = w (s, j) := by
    intro s j
    rw [hob _ ⟨(s, j), rfl⟩]
    exact hf.extend_apply w 0 (s, j)
  let UR : Matrix R R ℂ := Matrix.of fun r r' => ob (e r') r
  have hUR1 : URᴴ * UR = 1 := by
    ext r1 r2
    have ho := orthonormal_iff_ite.mp ob.orthonormal (e r1) (e r2)
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at ho
    simp only [e.injective.eq_iff] at ho
    rw [Matrix.one_apply, ← ho, Matrix.mul_apply]
    simp [UR, dotProduct, conjTranspose_apply]
  refine ⟨UR, ⟨hUR1, mul_eq_one_comm.mp hUR1⟩, ?_⟩
  let χ : Fin (Fintype.card R / Fintype.card C) × Rb → ℂ := fun x =>
    ∑ j : J, if ι j = x.1 then ((Real.sqrt (ev j.1) : ℝ) : ℂ) * star (u j.1 x.2) else 0
  refine ⟨χ, ?_, ?_⟩
  · -- normalization
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [χ]
    simp only [ect_sum_sq ι]
    rw [Finset.sum_comm]
    have hu1 : ∀ j : Rb, ∑ b, ‖u j b‖ ^ 2 = 1 := by
      intro j
      have h := u.orthonormal.1 j
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
      exact h
    have : ∀ j : J, ∑ b, ‖((Real.sqrt (ev j.1) : ℝ) : ℂ) * star (u j.1 b)‖ ^ 2 = ev j.1 := by
      intro j
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
        Real.sq_sqrt (hev0 _), ← Finset.mul_sum, hu1, mul_one]
    simp only [this]
    have hz : ∑ j : {j // ¬ ev j ≠ 0}, ev j.1 = 0 :=
      Finset.sum_eq_zero fun j _ => not_not.mp j.2
    rw [← htr, ← Fintype.sum_subtype_add_sum_subtype (fun j => ev j ≠ 0) ev, hz, add_zero]
  · intro i r b
    -- expand the right-hand side over the split index set
    have hR : ∑ r', UR r r' *
        (match e r' with
          | Sum.inl (c, k) => if c = i then χ (k, b) else 0
          | Sum.inr _ => 0) =
        ∑ j : J, (A i *ᵥ u j.1) r * star (u j.1 b) := by
      simp only [UR, Matrix.of_apply]
      rw [e.sum_comp (fun y => ob y r *
        (match y with
          | Sum.inl (c, k) => if c = i then χ (k, b) else 0
          | Sum.inr _ => 0))]
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, mul_ite, mul_zero,
        Finset.sum_const_zero, add_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [χ, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (by simp)]
      simp only [eq_self_iff_true, if_true]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hobw]
      simp only [w, WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]
      have hs : ((Real.sqrt (ev j.1) : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero (hev0 _)]; exact j.2
      rw [Complex.ofReal_inv]
      field_simp
    rw [hR]
    -- expand the left-hand side in the eigenbasis
    have hcomp : ∀ b', ∑ j, u j b' * star (u j b) = if b' = b then 1 else 0 := by
      intro b'
      have h := congrArg (fun M : Matrix Rb Rb ℂ => M b' b)
        (Unitary.mul_star_self_of_mem hg.eigenvectorUnitary.2)
      simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply,
        Matrix.IsHermitian.eigenvectorUnitary_apply, u] using h
    have hL : V (r, b) i = ∑ j, (A i *ᵥ u j) r * star (u j b) := by
      simp only [mulVec, dotProduct, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hcomp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rfl
    have hz : ∑ j : {j // ¬ ev j ≠ 0}, (A i *ᵥ u j.1) r * star (u j.1 b) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hAu0 i j.1 (not_not.mp j.2)]; simp
    rw [hL, ← Fintype.sum_subtype_add_sum_subtype (fun j => ev j ≠ 0), hz, add_zero]

end ECT2

end HarlowTASI

open HarlowTASI in
theorem solution {R Rb C : Type} [Fintype R] [DecidableEq R] [Fintype Rb]
    [DecidableEq Rb] [Fintype C] [DecidableEq C] [Nonempty C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V) :
    List.TFAE
      [ ∀ O : Matrix C C ℂ, ∃ OR : Matrix R R ℂ,
          (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
          (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ,
        ∀ X : Matrix Rb Rb ℂ, ∃ c : ℂ,
          (V * Vᴴ) * ((1 : Matrix R R ℂ) ⊗ₖ X) * (V * Vᴴ) = c • (V * Vᴴ),
        reducedSB (codeReferenceState V) =
          reducedS (codeReferenceState V) ⊗ₖ reducedB (codeReferenceState V),
        Fintype.card C ≤ Fintype.card R ∧
          ∀ e : R ≃ (C × Fin (Fintype.card R / Fintype.card C)) ⊕
              Fin (Fintype.card R % Fintype.card C),
            ∃ UR : Matrix R R ℂ, IsUnitaryMatrix UR ∧
              ∃ χ : Fin (Fintype.card R / Fintype.card C) × Rb → ℂ,
                ∑ x, ‖χ x‖ ^ 2 = 1 ∧
                ∀ (i : C) (r : R) (b : Rb),
                  V (r, b) i = ∑ r', UR r r' *
                    (match e r' with
                      | Sum.inl (c, k) => if c = i then χ (k, b) else 0
                      | Sum.inr _ => 0) ] := by
  tfae_have 1 → 2 := fun h1 X => ect_12 V h1 X
  tfae_have 2 → 3 := fun h2 => by
    obtain ⟨g, hg⟩ := ect_2G V hV h2
    exact ect_G3 V hV g hg
  tfae_have 3 → 4 := fun h3 => by
    obtain ⟨g, hg⟩ := ect_3G V hV h3
    exact ect_G4 V hV g hg
  tfae_have 4 → 1 := fun h4 => by
    have hc : Fintype.card R = Fintype.card ((C × Fin (Fintype.card R / Fintype.card C)) ⊕
        Fin (Fintype.card R % Fintype.card C)) := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      exact (Nat.div_add_mod _ _).symm
    obtain ⟨UR, hU, χ, -, hrep⟩ := h4.2 (Fintype.equivOfCardEq hc)
    refine ect_41' V (Fintype.equivOfCardEq hc) UR hU χ fun i r b => ?_
    rw [hrep i r b]
    refine Finset.sum_congr rfl fun r' _ => ?_
    congr 1
    generalize (Fintype.equivOfCardEq hc) r' = y
    rcases y with ⟨c, k⟩ | j <;> rfl
  tfae_finish
