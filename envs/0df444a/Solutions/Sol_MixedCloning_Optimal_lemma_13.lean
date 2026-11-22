-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:10:17.302856+00:00
-- url     : https://prove2.me/submissions/748ce46b-1e8f-438a-8b3e-dc2ec35f814c

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace L13

/-! ### Permutation matrices -/

/-- `P_p P_q = P_{pq}`. -/
lemma permMatrix_mul (d m : ℕ) (p q : Equiv.Perm (Fin m)) :
    permMatrix (a := Fin d) m p * permMatrix m q = permMatrix m (p * q) := by
  ext i j
  simp only [mul_apply, permMatrix]
  rw [Finset.sum_eq_single (j ∘ q.symm)]
  · rw [if_pos rfl, mul_one]
    rfl
  · intro x _ hx
    rw [if_neg hx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `P_pᴴ = P_{p⁻¹}`. -/
lemma permMatrix_conjTranspose (d m : ℕ) (p : Equiv.Perm (Fin m)) :
    (permMatrix (a := Fin d) m p)ᴴ = permMatrix m p⁻¹ := by
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

/-- `P_1 = 1`. -/
lemma permMatrix_one (d m : ℕ) : permMatrix (a := Fin d) m 1 = 1 := by
  ext i j
  have hc : j ∘ (1 : Equiv.Perm (Fin m)).symm = j := by funext t; rfl
  by_cases h : i = j
  · rw [h, one_apply_eq]
    simp [permMatrix, hc]
  · rw [one_apply_ne h]
    simp [permMatrix, hc, h]

lemma permMatrix_mul_conjTranspose (d m : ℕ) (p : Equiv.Perm (Fin m)) :
    permMatrix (a := Fin d) m p * (permMatrix m p)ᴴ = 1 := by
  rw [permMatrix_conjTranspose, permMatrix_mul, mul_inv_cancel, permMatrix_one]

lemma permMatrix_conjTranspose_mul (d m : ℕ) (p : Equiv.Perm (Fin m)) :
    (permMatrix (a := Fin d) m p)ᴴ * permMatrix m p = 1 := by
  rw [permMatrix_conjTranspose, permMatrix_mul, inv_mul_cancel, permMatrix_one]

/-- `(P_p M)_{i,k} = M_{i∘p, k}`. -/
lemma permMatrix_mul_apply (d m : ℕ) (p : Equiv.Perm (Fin m)) (M : Op (Word (Fin d) m))
    (i k : Word (Fin d) m) : (permMatrix (a := Fin d) m p * M : Op (Word (Fin d) m)) i k = M (i ∘ p) k := by
  simp only [mul_apply, permMatrix, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (i ∘ p)]
  · rw [if_pos (by ext t; simp)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    rw [h]
    ext t
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `(M P_p)_{i,k} = M_{i, k∘p⁻¹}`. -/
lemma mul_permMatrix_apply (d m : ℕ) (p : Equiv.Perm (Fin m)) (M : Op (Word (Fin d) m))
    (i k : Word (Fin d) m) : (M * permMatrix (a := Fin d) m p : Op (Word (Fin d) m)) i k = M i (k ∘ p.symm) := by
  simp only [mul_apply, permMatrix, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (k ∘ p.symm)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Permutation matrices commute with tensor powers. -/
lemma permMatrix_tensorPower_comm (d m : ℕ) (p : Equiv.Perm (Fin m)) (X : Op (Fin d)) :
    permMatrix m p * tensorPower m X = tensorPower m X * permMatrix m p := by
  ext i k
  rw [permMatrix_mul_apply, mul_permMatrix_apply]
  have h := Equiv.prod_comp p (fun t => X (i t) (k (p.symm t)))
  simp only [Equiv.symm_apply_apply] at h
  simpa [tensorPower] using h

/-- `P_p X^{⊗m} P_pᴴ = X^{⊗m}`. -/
lemma permMatrix_conj_tensorPower (d m : ℕ) (p : Equiv.Perm (Fin m)) (X : Op (Fin d)) :
    permMatrix m p * tensorPower m X * (permMatrix m p)ᴴ = tensorPower m X := by
  rw [permMatrix_tensorPower_comm, Matrix.mul_assoc, permMatrix_mul_conjTranspose,
    Matrix.mul_one]

lemma permMatrix_conj_tensorPower' (d m : ℕ) (p : Equiv.Perm (Fin m)) (X : Op (Fin d)) :
    permMatrix m p * (tensorPower m X * (permMatrix m p)ᴴ) = tensorPower m X := by
  rw [← Matrix.mul_assoc, permMatrix_conj_tensorPower]

/-! ### A normalized Kraus family over any finite index type gives a channel -/

lemma isChannel_of_kraus {ι κ K : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype K]
    (Φ : QAlgorithms.Superop ι κ) (G : K → Matrix κ ι ℂ)
    (hG : ∑ x, (G x)ᴴ * G x = 1) (hΦ : ∀ ρ, Φ ρ = ∑ x, G x * ρ * (G x)ᴴ) :
    QAlgorithms.IsChannel Φ := by
  refine ⟨Fintype.card K, fun k => G ((Fintype.equivFin K).symm k), ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [← hG]
    exact Equiv.sum_comp (Fintype.equivFin K).symm (fun x => (G x)ᴴ * G x)
  · intro ρ
    rw [hΦ ρ]
    unfold QAlgorithms.krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K).symm (fun x => G x * ρ * (G x)ᴴ)).symm

/-! ### The symmetrized channel -/

section Main
variable (d n m : ℕ)

/-- The normalization `(n! m!)⁻¹`. -/
def cst : ℂ := ((n.factorial : ℂ) * (m.factorial : ℂ))⁻¹

/-- Its square root `(n! m!)^{-1/2}` (real). -/
def sc : ℂ := (((Real.sqrt ((n.factorial : ℝ) * (m.factorial : ℝ)))⁻¹ : ℝ) : ℂ)

lemma star_sc : star (sc n m) = sc n m := Complex.conj_ofReal _

lemma sc_mul_sc : sc n m * sc n m = cst n m := by
  unfold sc cst
  rw [← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by positivity), Complex.ofReal_inv]
  push_cast
  rfl

lemma cst_mul_card (t : ℂ) :
    cst n m * ((m.factorial : ℂ) * ((n.factorial : ℂ) * t)) = t := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  unfold cst
  field_simp

/-- `Cbar X = (n! m!)⁻¹ Σ_{π,σ} P_πᴴ C(P_σ X P_σᴴ) P_π`. -/
def cbar (C : Cloner d n m) (X : Op (Word (Fin d) n)) : Op (Word (Fin d) m) :=
  cst n m • ∑ π : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin n),
      (permMatrix (a := Fin d) m π)ᴴ *
        C (permMatrix (a := Fin d) n σ * X * (permMatrix (a := Fin d) n σ)ᴴ) *
          permMatrix (a := Fin d) m π

/-- The Kraus family `(n! m!)^{-1/2} P_πᴴ E_j P_σ`. -/
def krausFam {K : ℕ} (E : Fin K → Matrix (Word (Fin d) m) (Word (Fin d) n) ℂ)
    (x : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) × Fin K) :
    Matrix (Word (Fin d) m) (Word (Fin d) n) ℂ :=
  sc n m • ((permMatrix (a := Fin d) m x.1)ᴴ * E x.2.2 * permMatrix (a := Fin d) n x.2.1)

lemma krausFam_conjTranspose {K : ℕ} (E : Fin K → Matrix (Word (Fin d) m) (Word (Fin d) n) ℂ)
    (x : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) × Fin K) :
    (krausFam d n m E x)ᴴ =
      sc n m • ((permMatrix (a := Fin d) n x.2.1)ᴴ * (E x.2.2)ᴴ * permMatrix (a := Fin d) m x.1) := by
  unfold krausFam
  rw [conjTranspose_smul, star_sc, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma krausFam_term {K : ℕ} (E : Fin K → Matrix (Word (Fin d) m) (Word (Fin d) n) ℂ)
    (π : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin n)) (j : Fin K) :
    (krausFam d n m E (π, σ, j))ᴴ * krausFam d n m E (π, σ, j) =
      cst n m • ((permMatrix (a := Fin d) n σ)ᴴ * ((E j)ᴴ * E j) * permMatrix n σ) := by
  rw [krausFam_conjTranspose]
  unfold krausFam
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sc_mul_sc]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (permMatrix m π) (permMatrix m π)ᴴ, permMatrix_mul_conjTranspose,
    Matrix.one_mul]

lemma krausFam_apply {K : ℕ} (E : Fin K → Matrix (Word (Fin d) m) (Word (Fin d) n) ℂ)
    (ρ : Op (Word (Fin d) n))
    (π : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin n)) (j : Fin K) :
    krausFam d n m E (π, σ, j) * ρ * (krausFam d n m E (π, σ, j))ᴴ =
      cst n m • ((permMatrix (a := Fin d) m π)ᴴ *
        (E j * (permMatrix n σ * ρ * (permMatrix n σ)ᴴ) * (E j)ᴴ) * permMatrix m π) := by
  rw [krausFam_conjTranspose]
  unfold krausFam
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sc_mul_sc]
  congr 1
  simp only [Matrix.mul_assoc]

lemma cbar_isChannel (C : Cloner d n m) (hC : QAlgorithms.IsChannel C) :
    QAlgorithms.IsChannel (cbar d n m C) := by
  obtain ⟨K, E, hE, hCE⟩ := hC
  have hE' : ∑ j, (E j)ᴴ * E j = 1 := hE
  apply isChannel_of_kraus (cbar d n m C) (krausFam d n m E)
  · have hinner : ∀ σ : Equiv.Perm (Fin n),
        ∑ j, (permMatrix (a := Fin d) n σ)ᴴ * ((E j)ᴴ * E j) * permMatrix n σ = 1 := by
      intro σ
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE', Matrix.mul_one,
        permMatrix_conjTranspose_mul]
    calc ∑ x, (krausFam d n m E x)ᴴ * krausFam d n m E x
        = ∑ π : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin n), ∑ j,
            cst n m • ((permMatrix (a := Fin d) n σ)ᴴ * ((E j)ᴴ * E j) * permMatrix n σ) := by
          simp only [Fintype.sum_prod_type, krausFam_term]
      _ = ∑ _π : Equiv.Perm (Fin m), ∑ _σ : Equiv.Perm (Fin n),
            cst n m • (1 : Op (Word (Fin d) n)) := by
          refine Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun σ _ => ?_))
          rw [← Finset.smul_sum, hinner]
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
          rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
          have h1 : ((m.factorial : ℂ) * (n.factorial : ℂ)) * cst n m = 1 := by
            have h2 := cst_mul_card n m 1
            rw [mul_one] at h2
            rw [mul_comm]
            exact h2
          rw [h1, one_smul]
  · intro ρ
    simp only [Fintype.sum_prod_type, krausFam_apply]
    unfold cbar
    simp only [hCE, QAlgorithms.krausApply, Finset.smul_sum, Finset.mul_sum, Finset.sum_mul]

/-- `P_p (P_πᴴ Y P_π) P_pᴴ = P_{πp⁻¹}ᴴ Y P_{πp⁻¹}`. -/
lemma summand_out (π p : Equiv.Perm (Fin m)) (Y : Op (Word (Fin d) m)) :
    permMatrix (a := Fin d) m p * ((permMatrix m π)ᴴ * Y * permMatrix m π) * (permMatrix m p)ᴴ
      = (permMatrix m (π * p⁻¹))ᴴ * Y * permMatrix m (π * p⁻¹) := by
  rw [← permMatrix_mul d m π p⁻¹, ← permMatrix_conjTranspose d m p, conjTranspose_mul,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- `P_σ (P_s X P_sᴴ) P_σᴴ = P_{σs} X P_{σs}ᴴ`. -/
lemma summand_in (σ s : Equiv.Perm (Fin n)) (X : Op (Word (Fin d) n)) :
    permMatrix (a := Fin d) n σ * (permMatrix n s * X * (permMatrix n s)ᴴ) * (permMatrix n σ)ᴴ
      = permMatrix n (σ * s) * X * (permMatrix n (σ * s))ᴴ := by
  rw [← permMatrix_mul d n σ s, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma cbar_permInvariant (C : Cloner d n m) : PermInvariant d n m (cbar d n m C) := by
  intro pi si X
  dsimp only
  unfold cbar
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, summand_in, summand_out]
  refine Fintype.sum_equiv (Equiv.mulRight pi⁻¹) _ _ (fun π => ?_)
  refine Fintype.sum_equiv (Equiv.mulRight si) _ _ (fun σ => ?_)
  rfl

lemma cbar_overlap (r : ℕ) (C : Cloner d n m) (P : Op (Fin d)) :
    overlap d r n m (cbar d n m C) P = overlap d r n m C P := by
  unfold overlap
  congr 1
  unfold cbar
  simp only [permMatrix_conj_tensorPower]
  have key : ∀ π : Equiv.Perm (Fin m),
      ((permMatrix (a := Fin d) m π)ᴴ * C (tensorPower n (projectorState r P)) *
        permMatrix m π * tensorPower m P).trace =
      (C (tensorPower n (projectorState r P)) * tensorPower m P).trace := by
    intro π
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [permMatrix_conj_tensorPower']
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp only [Finset.sum_mul, Matrix.trace_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, smul_eq_mul]
  exact cst_mul_card n m _

end Main

end L13

theorem solution (d r n m : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (C : Cloner d n m) (hC : QAlgorithms.IsChannel C) :
    ∃ Cbar : Cloner d n m, QAlgorithms.IsChannel Cbar ∧ PermInvariant d n m Cbar ∧
      (∀ P : Op (Fin d), IsProjector r P → overlap d r n m Cbar P = overlap d r n m C P) ∧
      minimumOverlap d r n m Cbar = minimumOverlap d r n m C ∧
      averageOverlap d r n m Cbar = averageOverlap d r n m C := by
  have hov : ∀ P, overlap d r n m (L13.cbar d n m C) P = overlap d r n m C P :=
    fun P => L13.cbar_overlap d n m r C P
  refine ⟨L13.cbar d n m C, L13.cbar_isChannel d n m C hC, L13.cbar_permInvariant d n m C,
    fun P _ => hov P, ?_, ?_⟩
  · simp only [minimumOverlap, hov]
  · simp only [averageOverlap, hov]
