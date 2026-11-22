-- Prove2me | solution 1 for MixedCloning.Optimal.Supplement.proposition_25
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T06:35:00.785589+00:00
-- url     : https://prove2.me/submissions/2021ace4-367e-46db-a6a3-443de325e862

import Definitions.Def_MixedCloning_Optimal_Supplement_Transposition
import Theorems.Thm_MixedCloning_Optimal_werner_trace_bose
import Theorems.Thm_MayersBC_fuchs_caves
import Theorems.Thm_MixedCloning_Optimal_fidelity_le_partialTrace
import Theorems.Thm_MixedCloning_Optimal_lemma_6

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal MixedCloning.Optimal.Supplement

attribute [local instance] Classical.propDecidable Classical.decEq

-- ===== from PttA.lean =====

/-! ### Kraus channels -/

section Kraus
open QAlgorithms

lemma ptt_isChannel_transport {ι κ : Type*} [Fintype ι] [Fintype κ] (i₁ i₂ : DecidableEq ι)
    (Φ : Superop ι κ) (h : @IsChannel ι κ _ _ i₁ Φ) : @IsChannel ι κ _ _ i₂ Φ := by
  cases Subsingleton.elim i₁ i₂
  exact h

lemma ptt_isChannel_of_kraus {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    {_ : DecidableEq ι} (Φ : Superop ι κ) (E : K → Matrix κ ι ℂ)
    (hE : ∑ j, (E j)ᴴ * E j = 1) (hΦ : ∀ ρ, Φ ρ = ∑ j, E j * ρ * (E j)ᴴ) : IsChannel Φ := by
  refine ⟨Fintype.card K, fun i => E ((Fintype.equivFin K).symm i), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← hE]
    exact Equiv.sum_comp (Fintype.equivFin K).symm (fun j => (E j)ᴴ * E j)
  · intro ρ
    rw [hΦ ρ]
    unfold krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K).symm (fun j => E j * ρ * (E j)ᴴ)).symm

lemma ptt_isChannel_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    {_ : DecidableEq ι} {_ : DecidableEq κ} (Φ : Superop ι κ) (Ψ : Superop κ μ)
    (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) : IsChannel (fun X => Ψ (Φ X)) := by
  obtain ⟨m₁, E, hE, hΦE⟩ := hΦ
  obtain ⟨m₂, F, hF, hΨF⟩ := hΨ
  refine ptt_isChannel_of_kraus _ (fun p : Fin m₁ × Fin m₂ => F p.2 * E p.1) ?_ ?_
  · rw [Fintype.sum_prod_type]
    have h : ∀ x : Fin m₁, ∑ y : Fin m₂, (F y * E x)ᴴ * (F y * E x) = (E x)ᴴ * E x := by
      intro x
      calc ∑ y : Fin m₂, (F y * E x)ᴴ * (F y * E x)
          = (E x)ᴴ * (∑ y, (F y)ᴴ * F y) * E x := by
            rw [Matrix.mul_sum, Matrix.sum_mul]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = (E x)ᴴ * E x := by
            have hF' : ∑ y, (F y)ᴴ * F y = 1 := hF
            rw [hF', Matrix.mul_one]
    simp only [h]
    exact hE
  · intro ρ
    show Ψ (Φ ρ) = _
    rw [hΦE, hΨF]
    unfold krausApply
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]

/-- A channel maps states to states. -/
lemma ptt_channel_state {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι}
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (Φ ρ) := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  rw [hΦE]
  unfold krausApply
  refine ⟨Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (E j), ?_⟩
  rw [Matrix.trace_sum]
  have h : ∀ j, (E j * ρ * (E j)ᴴ).trace = ((E j)ᴴ * E j * ρ).trace := by
    intro j
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [h]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul]
  have hE' : ∑ j, (E j)ᴴ * E j = 1 := hE
  rw [hE', Matrix.one_mul]
  exact hρ.2

/-- A channel agrees with a `ℂ`-linear map. -/
lemma ptt_channel_linear {ι κ : Type*} [Fintype ι] [Fintype κ] {_ : DecidableEq ι}
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) :
    ∃ L : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ, ∀ X, L X = Φ X := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  refine ⟨{ toFun := Φ, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · intro X Y
    simp only [hΦE, krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · intro c X
    simp only [hΦE, krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum,
      RingHom.id_apply]

end Kraus

/-! ### The partial trace is a channel -/

lemma ptt_partialTrace_isChannel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (m : ℕ) :
    QAlgorithms.IsChannel (fun X : Op (Word (a × b) m) => partialTrace (a := a) m X) := by
  let E : Word b m → Matrix (Word a m) (Word (a × b) m) ℂ :=
    fun z => Matrix.of fun i w => if w = (fun t => (i t, z t)) then 1 else 0
  refine ptt_isChannel_of_kraus _ E ?_ ?_
  · have key : ∀ (w : Word (a × b) m) (i : Word a m) (z : Word b m),
        (w = fun t => (i t, z t)) ↔ (i = fun t => (w t).1) ∧ (z = fun t => (w t).2) := by
      intro w i z
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    ext w w'
    simp only [E, Matrix.sum_apply, mul_apply, conjTranspose_apply, of_apply, apply_ite star,
      star_one, star_zero, ite_mul, one_mul, zero_mul]
    simp only [key, ite_and]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [one_apply]
    by_cases h : w = w'
    · subst h
      simp
    · rw [if_neg h]
      split_ifs with h1 h2
      · exact absurd (funext fun t => Prod.ext (congrFun h1 t) (congrFun h2 t)) h
      · rfl
      · rfl
  · intro X
    ext i j
    simp only [E, partialTrace, Matrix.sum_apply, mul_apply, conjTranspose_apply, of_apply,
      apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ### Factorization and matrix units -/

section Factor
open scoped MatrixOrder

lemma ptt_psd_factor {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.PosSemidef) : ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, by rw [hB, star_eq_conjTranspose]⟩

end Factor

lemma ptt_sum_single {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (Y : Matrix β β ℂ) :
    ∑ i : α, ∑ j : β, single i j (1 : ℂ) * Y * single j i (1 : ℂ) =
      Y.trace • (1 : Matrix α α ℂ) := by
  simp only [single_mul_mul_single, one_mul, mul_one]
  ext p q
  simp only [Matrix.sum_apply, single_apply, Matrix.smul_apply, one_apply, trace, diag,
    smul_eq_mul, mul_ite, mul_one, mul_zero, ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

/-! ### Symmetric projectors and word splitting (no `DecidableEq a` binder) -/

section Transposer
variable {a : Type} [Fintype a]

lemma ptt_permMatrix_mul (m : ℕ) (p q : Equiv.Perm (Fin m)) :
    permMatrix (a := a) m p * permMatrix m q = permMatrix m (p * q) := by
  ext i j
  simp only [permMatrix, mul_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (j ∘ q.symm)]
  · rw [if_pos rfl]
    rfl
  · intro l _ hl
    rw [if_neg hl]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma ptt_permMatrix_mul_symProjector (m : ℕ) (p : Equiv.Perm (Fin m)) :
    permMatrix (a := a) m p * symProjector a m = symProjector a m := by
  unfold symProjector
  rw [Matrix.mul_smul, Matrix.mul_sum]
  simp only [ptt_permMatrix_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft p) (fun q => permMatrix (a := a) m q)

lemma ptt_symProjector_mul_self (m : ℕ) :
    symProjector a m * symProjector a m = symProjector a m := by
  calc symProjector a m * symProjector a m
      = ((Nat.factorial m : ℂ)⁻¹ • ∑ p : Equiv.Perm (Fin m), permMatrix (a := a) m p) *
          symProjector a m := rfl
    _ = symProjector a m := by
      rw [Matrix.smul_mul, Matrix.sum_mul]
      simp only [ptt_permMatrix_mul_symProjector, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero m)), one_smul]

omit [Fintype a] in
lemma ptt_permMatrix_conjTranspose (m : ℕ) (p : Equiv.Perm (Fin m)) :
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

lemma ptt_symProjector_conjTranspose (m : ℕ) : (symProjector a m)ᴴ = symProjector a m := by
  unfold symProjector
  rw [conjTranspose_smul, conjTranspose_sum]
  simp only [ptt_permMatrix_conjTranspose]
  have hsum : ∑ x : Equiv.Perm (Fin m), permMatrix (a := a) m x⁻¹ = ∑ p, permMatrix m p :=
    Equiv.sum_comp (Equiv.inv _) (fun p => permMatrix (a := a) m p)
  rw [hsum]
  congr 1
  simp

lemma ptt_Q_star (m : ℕ) (x y : Word a m) :
    star (symProjector a m x y) = symProjector a m y x := by
  have h := congrFun (congrFun (ptt_symProjector_conjTranspose (a := a) m) y) x
  rw [conjTranspose_apply] at h
  exact h

lemma ptt_Q_sum (m : ℕ) (x y : Word a m) :
    ∑ u, symProjector a m x u * symProjector a m u y = symProjector a m x y := by
  have h := congrFun (congrFun (ptt_symProjector_mul_self (a := a) m) x) y
  rw [mul_apply] at h
  exact h

/-- Splitting a sum over words of length `n+k` into prefix and suffix. -/
lemma ptt_sum_split {M : Type*} [AddCommMonoid M] (n k : ℕ) (f : Word a (n+k) → M) :
    ∑ w, f w = ∑ z : Word a n, ∑ b : Word a k, f (Fin.append z b) := by
  rw [← (Fin.appendEquiv n k).sum_comp, Fintype.sum_prod_type]
  rfl

lemma ptt_appendIdentity_append (n k : ℕ) (Y : Op (Word a n)) (z z' : Word a n)
    (b b' : Word a k) :
    appendIdentity n k Y (Fin.append z b) (Fin.append z' b') =
      if b = b' then Y z z' else 0 := by
  simp only [appendIdentity, Fin.append_left, Fin.append_right]
  by_cases h : b = b'
  · subst h
    simp
  · have h' : ¬ ((fun t => b t) = fun t => b' t) := h
    rw [if_neg h', if_neg h, mul_zero]

/-- `S_u : (S_u)_{z,b} = Π_{n+k}(z ++ b, u)`. -/
def pttS (n k : ℕ) (u : Word a (n+k)) : Matrix (Word a n) (Word a k) ℂ :=
  Matrix.of fun z b => symProjector a (n+k) (Fin.append z b) u

/-- Kraus form of the transposed partial trace:
`(tr_{1..n}[Π_{n+k} (Y ⊗ I)])ᵀ = Σ_u S_uᴴ Y S_u`. -/
lemma ptt_lemmaA (n k : ℕ) (Y : Op (Word a n)) :
    (traceFirst n k (symProjector a (n+k) * appendIdentity n k Y))ᵀ =
      ∑ u : Word a (n+k), (pttS n k u)ᴴ * Y * pttS n k u := by
  ext b b'
  have hL : ∀ y : Word a n,
      ∑ w, symProjector a (n+k) (Fin.append y b') w * appendIdentity n k Y w (Fin.append y b) =
        ∑ z, symProjector a (n+k) (Fin.append y b') (Fin.append z b) * Y z y := by
    intro y
    rw [ptt_sum_split n k]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [ptt_appendIdentity_append, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hR : ∀ y z : Word a n, ∑ u : Word a (n+k),
      star (symProjector a (n+k) (Fin.append z b) u) * Y z y *
        symProjector a (n+k) (Fin.append y b') u =
      symProjector a (n+k) (Fin.append y b') (Fin.append z b) * Y z y := by
    intro y z
    rw [← ptt_Q_sum (n+k) (Fin.append y b') (Fin.append z b), Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [ptt_Q_star]
    ring
  simp only [transpose_apply, traceFirst, mul_apply, Matrix.sum_apply, conjTranspose_apply,
    pttS, of_apply]
  simp only [hL, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (hR y z).symm

lemma ptt_traceFirst_trace (n k : ℕ) (M : Op (Word a (n+k))) :
    (traceFirst n k M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, traceFirst]
  rw [ptt_sum_split n k (fun w => M w w), Finset.sum_comm]

/-- `T = Σ_u S_u S_uᴴ` (the partial trace of `Π_{n+k}` over the last `k` registers). -/
def pttT (n k : ℕ) : Op (Word a n) := ∑ u : Word a (n+k), pttS n k u * (pttS n k u)ᴴ

lemma ptt_trace_Q_append (n k : ℕ) (Y : Op (Word a n)) :
    (symProjector a (n+k) * appendIdentity n k Y * symProjector a (n+k)).trace =
      (pttT (a := a) n k * Y).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ptt_symProjector_mul_self,
    ← ptt_traceFirst_trace n k, ← Matrix.trace_transpose, ptt_lemmaA, Matrix.trace_sum, pttT,
    Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]

/-- From `werner_trace_bose` by trace duality: `d[n] Π_n T Π_n = d[n+k] Π_n`. -/
lemma ptt_PTP (n k : ℕ) :
    (symDimension (Fintype.card a) n : ℂ) • (symProjector a n * pttT n k * symProjector a n) =
      (symDimension (Fintype.card a) (n+k) : ℂ) • symProjector a n := by
  rw [Matrix.ext_iff_trace_mul_right]
  intro X
  have h := werner_trace_bose (a := a) n k X
  rw [ptt_trace_Q_append] at h
  set P := symProjector a n with hP
  set T := pttT (a := a) n k with hT
  have hPP : P * P = P := ptt_symProjector_mul_self n
  have e1 : (P * T * P * X).trace = (T * (P * X * P)).trace := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm P]
    simp only [Matrix.mul_assoc]
  have e2 : (P * X * P).trace = (P * X).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPP]
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul, e1, ← e2]
  exact h

lemma ptt_K_norm (n k : ℕ) (hD : 0 < Fintype.card a) (s : ℂ)
    (hs : star s * s =
      (symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k)) :
    ∑ u : Word a (n+k), (s • ((pttS n k u)ᴴ * symProjector a n))ᴴ *
        (s • ((pttS n k u)ᴴ * symProjector a n)) = symProjector a n := by
  have hdpos : ∀ m, 0 < symDimension (Fintype.card a) m := fun m => by
    unfold symDimension; exact Nat.choose_pos (by omega)
  have hdnk : (symDimension (Fintype.card a) (n+k) : ℂ) ≠ 0 := by
    exact_mod_cast (hdpos (n+k)).ne'
  have hPh : (symProjector a n)ᴴ = symProjector a n := ptt_symProjector_conjTranspose n
  have e : ∀ u : Word a (n+k), (s • ((pttS n k u)ᴴ * symProjector a n))ᴴ *
        (s • ((pttS n k u)ᴴ * symProjector a n)) =
      (star s * s) • (symProjector a n * (pttS n k u * (pttS n k u)ᴴ) * symProjector a n) := by
    intro u
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul,
      hPh, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [mul_comm s (star s)]
  simp only [e]
  rw [← Finset.smul_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hs, div_eq_inv_mul, ← smul_smul]
  have hT : ∑ u : Word a (n+k), pttS n k u * (pttS n k u)ᴴ = pttT n k := rfl
  rw [hT, ptt_PTP, smul_smul, inv_mul_cancel₀ hdnk, one_smul]

lemma ptt_L_norm (n k : ℕ) (B : Op (Word a k)) (hB : (Bᴴ * B).trace = 1) :
    ∑ ij : Word a k × Word a n, (Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n))ᴴ *
        (Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n)) = 1 - symProjector a n := by
  set M : Op (Word a n) := 1 - symProjector a n with hM
  have hMh : Mᴴ = M := by
    rw [hM, conjTranspose_sub, conjTranspose_one, ptt_symProjector_conjTranspose]
  have hMM : M * M = M := by
    rw [hM]
    simp only [sub_mul, mul_sub, one_mul, mul_one, ptt_symProjector_mul_self, sub_self, sub_zero]
  have e : ∀ ij : Word a k × Word a n,
      (Bᴴ * single ij.1 ij.2 (1 : ℂ) * M)ᴴ * (Bᴴ * single ij.1 ij.2 (1 : ℂ) * M) =
        M * (single ij.2 ij.1 (1 : ℂ) * (B * Bᴴ) * single ij.1 ij.2 (1 : ℂ)) * M := by
    intro ij
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_single, star_one,
      conjTranspose_conjTranspose, hMh]
    simp only [Matrix.mul_assoc]
  simp only [e]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Fintype.sum_prod_type, Finset.sum_comm, ptt_sum_single,
    Matrix.trace_mul_comm, hB, one_smul, Matrix.mul_one, hMM]

lemma ptt_K_action (n k : ℕ) (s : ℂ) (X : Op (Word a n)) :
    ∑ u : Word a (n+k), (s • ((pttS n k u)ᴴ * symProjector a n)) * X *
        (s • ((pttS n k u)ᴴ * symProjector a n))ᴴ =
      (s * star s) • (traceFirst n k (symProjector a (n+k) *
        appendIdentity n k (symProjector a n * X * symProjector a n)))ᵀ := by
  rw [ptt_lemmaA, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul,
    ptt_symProjector_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [mul_comm (star s) s]

lemma ptt_L_action (n k : ℕ) (B : Op (Word a k)) (X : Op (Word a n)) :
    ∑ ij : Word a k × Word a n, (Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n)) * X *
        (Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n))ᴴ =
      ((1 - symProjector a n) * X).trace • (Bᴴ * B) := by
  set M : Op (Word a n) := 1 - symProjector a n with hM
  have hMh : Mᴴ = M := by
    rw [hM, conjTranspose_sub, conjTranspose_one, ptt_symProjector_conjTranspose]
  have hMM : M * M = M := by
    rw [hM]
    simp only [sub_mul, mul_sub, one_mul, mul_one, ptt_symProjector_mul_self, sub_self, sub_zero]
  have e : ∀ ij : Word a k × Word a n,
      (Bᴴ * single ij.1 ij.2 (1 : ℂ) * M) * X * (Bᴴ * single ij.1 ij.2 (1 : ℂ) * M)ᴴ =
        Bᴴ * (single ij.1 ij.2 (1 : ℂ) * (M * X * M) * single ij.2 ij.1 (1 : ℂ)) * B := by
    intro ij
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_single, star_one,
      conjTranspose_conjTranspose, hMh]
    simp only [Matrix.mul_assoc]
  simp only [e]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Fintype.sum_prod_type, ptt_sum_single, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul]
  congr 1
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hMM]

/-- The completed pure-state transposer is a channel whenever `tau` is a state. -/
lemma ptt_transposer_isChannel (n k : ℕ) (hD : 0 < Fintype.card a) (tau : Op (Word a k))
    (htau : IsState tau) : QAlgorithms.IsChannel (wernerTransposer a n k tau) := by
  obtain ⟨B, hB⟩ := ptt_psd_factor tau htau.1
  have htr : (Bᴴ * B).trace = 1 := by rw [← hB]; exact htau.2
  obtain ⟨s, hss⟩ : ∃ s : ℂ, star s * s =
      (symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k) := by
    refine ⟨((Real.sqrt ((symDimension (Fintype.card a) n : ℝ) /
      symDimension (Fintype.card a) (n+k)) : ℝ) : ℂ), ?_⟩
    rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
    push_cast
    rfl
  have hss' : s * star s =
      (symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k) := by
    rw [mul_comm]; exact hss
  let K : Word a (n+k) ⊕ (Word a k × Word a n) → Matrix (Word a k) (Word a n) ℂ :=
    Sum.elim (fun u => s • ((pttS n k u)ᴴ * symProjector a n))
      (fun ij => Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n))
  refine ptt_isChannel_of_kraus _ K ?_ ?_
  · rw [Fintype.sum_sum_type]
    simp only [K, Sum.elim_inl, Sum.elim_inr]
    rw [ptt_K_norm n k hD s hss, ptt_L_norm n k B htr]
    abel
  · intro X
    rw [Fintype.sum_sum_type]
    simp only [K, Sum.elim_inl, Sum.elim_inr]
    rw [ptt_K_action, ptt_L_action, hss', ← hB]
    rfl

end Transposer

-- ===== from PttB.lean =====

/-! ## Pure-state fidelity (`MatrixOrder` only locally) -/

section PureFidelity
open scoped MatrixOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma wpf_pure_eq (w : ι → ℂ) : MixedCloning.Optimal.pure w = vecMulVec w (star w) := by
  ext i j
  simp [MixedCloning.Optimal.pure, vecMulVec]

lemma wpf_pure_nonneg (w : ι → ℂ) : 0 ≤ MixedCloning.Optimal.pure w := by
  rw [wpf_pure_eq]
  exact (posSemidef_vecMulVec_self_star w).nonneg

lemma wpf_cfc_sqrt_eq (A : Matrix ι ι ℂ) (hA : 0 ≤ A) : cfc Real.sqrt A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA,
    cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero)]

lemma wpf_dot_self (w : ι → ℂ) : star w ⬝ᵥ w = (((star w ⬝ᵥ w).re : ℝ) : ℂ) := by
  have h := dotProduct_star_self_nonneg w
  apply Complex.ext
  · simp
  · simpa using (Complex.nonneg_iff.mp h).2.symm

lemma wpf_dot_self_re_nonneg (w : ι → ℂ) : 0 ≤ (star w ⬝ᵥ w).re :=
  (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg w)).1

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
      have hscal : ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * (((Real.sqrt s)⁻¹ : ℝ) : ℂ)) *
          (star w ⬝ᵥ w) = 1 := by
        rw [wpf_dot_self w, ← hs]
        have : (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ * s = 1 := by
          rw [← mul_inv, Real.mul_self_sqrt hspos.le, inv_mul_cancel₀ hspos.ne']
        exact_mod_cast this
      rw [smul_mul_smul_comm, hPP, smul_smul, hscal, one_smul]
    · rw [wpf_pure_eq]
      exact ((posSemidef_vecMulVec_self_star w).smul hc).nonneg

/-- `F(σ, |φ⟩⟨φ|) = ⟨φ|σ|φ⟩` for positive semidefinite `σ`. -/
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

/-- The root fidelity is nonnegative. -/
lemma pfp_rootFidelity_nonneg (X Y : Matrix ι ι ℂ) : 0 ≤ QAlgorithms.rootFidelity X Y := by
  unfold QAlgorithms.rootFidelity
  have h : (0 : Matrix ι ι ℂ) ≤ cfc Real.sqrt (cfc Real.sqrt X * Y * cfc Real.sqrt X) :=
    cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
  have ht := (Matrix.nonneg_iff_posSemidef.mp h).trace_nonneg
  exact (Complex.nonneg_iff.mp ht).1

/-- `Re tr(M X) ≥ 0` for positive semidefinite `M`, `X`. -/
lemma pfp_trace_mul_nonneg (M X : Matrix ι ι ℂ) (hM : M.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (M * X).trace.re := by
  have hSsa : IsSelfAdjoint (CFC.sqrt M) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)
  have hSh : (CFC.sqrt M)ᴴ = CFC.sqrt M := hSsa.star_eq
  have hSS : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
  have htr : (M * X).trace = (CFC.sqrt M * X * (CFC.sqrt M)ᴴ).trace := by
    rw [hSh]
    conv_lhs => rw [← hSS]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hpsd : (CFC.sqrt M * X * (CFC.sqrt M)ᴴ).PosSemidef := hX.mul_mul_conjTranspose_same _
  rw [htr]
  exact (Complex.nonneg_iff.mp hpsd.trace_nonneg).1

end PureFidelity

/-! ## Tensor powers of pure states -/

section TP
variable {a : Type} [Fintype a]

lemma wb_tensorPower_pure (m : ℕ) (u : a → ℂ) :
    tensorPower m (MixedCloning.Optimal.pure u) =
      MixedCloning.Optimal.pure (fun i : Word a m => ∏ t, u (i t)) := by
  ext i j
  simp only [tensorPower, MixedCloning.Optimal.pure, Finset.prod_mul_distrib, map_prod]

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

lemma wb_symProjector_mulVec (m : ℕ) (u : a → ℂ) :
    symProjector a m *ᵥ (fun i : Word a m => ∏ t, u (i t)) = fun i => ∏ t, u (i t) := by
  unfold symProjector
  rw [smul_mulVec, sum_mulVec]
  simp only [wb_perm_mulVec, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero m)), one_smul]

lemma wb_dot_prod (m : ℕ) (u : a → ℂ) (hu : ∑ x, u x * star (u x) = 1) :
    star (fun i : Word a m => ∏ t, u (i t)) ⬝ᵥ (fun i : Word a m => ∏ t, u (i t)) = 1 := by
  simp only [dotProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (x : a) => star (u x) * u x)]
  have h1 : ∑ x, (starRingEnd ℂ) (u x) * u x = 1 := by
    rw [← hu]
    exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm]; rfl)
  simp only [RCLike.star_def, h1, Finset.prod_const_one]

lemma pfp_tensorPower_mul (n : ℕ) (A B : Op a) :
    tensorPower n A * tensorPower n B = tensorPower n (A * B) := by
  ext i j
  simp only [tensorPower, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib]

lemma pfp_tensorPower_conjTranspose (n : ℕ) (A : Op a) :
    (tensorPower n A)ᴴ = tensorPower n Aᴴ := by
  ext i j
  simp [tensorPower, conjTranspose_apply, map_prod]

lemma pfp_mul_pure_mul (B : Op a) (v : a → ℂ) :
    B * MixedCloning.Optimal.pure v * Bᴴ = MixedCloning.Optimal.pure (B *ᵥ v) := by
  rw [wpf_pure_eq, wpf_pure_eq, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

lemma pfp_conj_tensorPower_pure (n : ℕ) (B : Op a) (v : a → ℂ) :
    tensorPower n B * tensorPower n (MixedCloning.Optimal.pure v) * (tensorPower n B)ᴴ =
      tensorPower n (MixedCloning.Optimal.pure (B *ᵥ v)) := by
  rw [pfp_tensorPower_conjTranspose, pfp_tensorPower_mul, pfp_tensorPower_mul, pfp_mul_pure_mul]

lemma pfp_tensorPower_trace (m : ℕ) (X : Op a) : (tensorPower m X).trace = X.trace ^ m := by
  rw [← Fin.prod_const]
  simp only [Matrix.trace, Matrix.diag, tensorPower]
  rw [Fintype.prod_sum]

lemma pfp_partialTrace_tensorPower {b : Type} [Fintype b] (m : ℕ) (X : Op (a × b)) :
    partialTrace m (tensorPower m X) = tensorPower m (fun i j => ∑ z : b, X (i, z) (j, z)) := by
  ext i j
  simp only [partialTrace, tensorPower]
  rw [Fintype.prod_sum]

lemma pfp_tensorPower_pure_posSemidef (m : ℕ) (u : a → ℂ) :
    (tensorPower m (MixedCloning.Optimal.pure u)).PosSemidef := by
  have h : tensorPower m (MixedCloning.Optimal.pure u) =
      vecMulVec (fun i : Word a m => ∏ t, u (i t)) (star fun i : Word a m => ∏ t, u (i t)) := by
    ext i j
    simp only [tensorPower, MixedCloning.Optimal.pure, vecMulVec, Matrix.of_apply, Pi.star_apply,
      RCLike.star_def, Finset.prod_mul_distrib, map_prod]
  rw [h]
  exact posSemidef_vecMulVec_self_star _

/-- `|u⟩⟨u|^{⊗m}` is a state for a unit vector `u`. -/
lemma ptt_tensorPower_pure_isState (m : ℕ) (u : a → ℂ) (hu : ∑ x, u x * star (u x) = 1) :
    IsState (tensorPower m (MixedCloning.Optimal.pure u)) := by
  refine ⟨pfp_tensorPower_pure_posSemidef m u, ?_⟩
  rw [pfp_tensorPower_trace]
  have h : (MixedCloning.Optimal.pure u).trace = 1 := by
    rw [← hu]
    simp only [Matrix.trace, Matrix.diag, MixedCloning.Optimal.pure, RCLike.star_def]
  rw [h, one_pow]

end TP

/-- Normalization of a unit vector of `EuclideanSpace`. -/
lemma ptt_norm_sum {a : Type} [Fintype a] (v : EuclideanSpace ℂ a) (hv : ‖v‖ = 1) :
    ∑ x, v.ofLp x * star (v.ofLp x) = 1 := by
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

/-! ## The transposer on symmetric pure inputs (no `DecidableEq a` binder) -/

section TransposerPure
variable {a : Type} [Fintype a]

lemma ptt_transposer_pure (n k : ℕ) (tau : Op (Word a k)) (ψ : Word a n → ℂ)
    (hψ : symProjector a n *ᵥ ψ = ψ) :
    wernerTransposer a n k tau (MixedCloning.Optimal.pure ψ) =
      ((symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k)) •
        ∑ u : Word a (n+k), MixedCloning.Optimal.pure ((pttS n k u)ᴴ *ᵥ ψ) := by
  obtain ⟨hl, hr⟩ := wpf_proj_mul_pure (symProjector a n) (ptt_symProjector_conjTranspose n) ψ hψ
  simp only [wernerTransposer]
  rw [hl, hr, sub_mul, one_mul, hl, sub_self, Matrix.trace_zero, zero_smul, add_zero, ptt_lemmaA]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [wpf_pure_eq, wpf_pure_eq, mul_vecMulVec, vecMulVec_mul, star_mulVec,
    conjTranspose_conjTranspose]

/-- `⟨φ|S_uᴴ|ψ⟩ = (v^{⊗(n+k)})_u` for `ψ = v^{⊗n}`, `φ = v̄^{⊗k}`. -/
lemma ptt_overlap (n k : ℕ) (v : a → ℂ) (u : Word a (n+k)) :
    star (fun b : Word a k => ∏ t, star (v (b t))) ⬝ᵥ
        ((pttS n k u)ᴴ *ᵥ (fun z : Word a n => ∏ t, v (z t))) = ∏ t, v (u t) := by
  have h1 := congrFun (wb_symProjector_mulVec (n+k) v) u
  rw [← h1]
  simp only [mulVec, dotProduct, conjTranspose_apply, pttS, of_apply, Pi.star_apply, star_prod,
    star_star, ptt_Q_star]
  conv_rhs => rw [ptt_sum_split n k]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

end TransposerPure

lemma ptt_dot_pure {ι : Type} [Fintype ι] (φ w : ι → ℂ) :
    star φ ⬝ᵥ (MixedCloning.Optimal.pure w *ᵥ φ) = (star φ ⬝ᵥ w) * star (star φ ⬝ᵥ w) := by
  simp only [dotProduct, mulVec, MixedCloning.Optimal.pure, Pi.star_apply, RCLike.star_def,
    map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## Pure-state fidelity of the transposer -/

section PureFid
variable {a : Type} [Fintype a] [DecidableEq a]

/-- [BGSQ26] via the Kraus form: on `|v⟩⟨v|^{⊗n}` the transposer outputs a state whose fidelity
with `|v̄⟩⟨v̄|^{⊗k}` is `D[n]/D[n+k]`. -/
lemma ptt_pure_fidelity (n k : ℕ) (hD : 0 < Fintype.card a) (tau : Op (Word a k))
    (htau : IsState tau) (v : a → ℂ) (hv : ∑ x, v x * star (v x) = 1) :
    IsState (wernerTransposer a n k tau (tensorPower n (MixedCloning.Optimal.pure v))) ∧
    fidelity (wernerTransposer a n k tau (tensorPower n (MixedCloning.Optimal.pure v)))
        (MixedCloning.Optimal.pure (fun b : Word a k => ∏ t, star (v (b t)))) =
      (symDimension (Fintype.card a) n : ℝ) / symDimension (Fintype.card a) (n+k) := by
  have hψ : symProjector a n *ᵥ (fun i : Word a n => ∏ t, v (i t)) = fun i => ∏ t, v (i t) :=
    wb_symProjector_mulVec n v
  have hst := ptt_channel_state _ (ptt_transposer_isChannel n k hD tau htau) _
    (ptt_tensorPower_pure_isState n v hv)
  refine ⟨hst, ?_⟩
  rw [wpf_fidelity_pure _ hst.1, wb_tensorPower_pure n v, ptt_transposer_pure n k tau _ hψ,
    smul_mulVec, sum_mulVec, dotProduct_smul, dotProduct_sum]
  simp only [ptt_dot_pure, ptt_overlap]
  have h1 : ∑ u : Word a (n+k), (∏ t, v (u t)) * star (∏ t, v (u t)) = 1 := by
    have h := wb_dot_prod (n+k) v hv
    rw [dotProduct] at h
    rw [← h]
    exact Finset.sum_congr rfl fun u _ => mul_comm _ _
  rw [h1, smul_eq_mul, mul_one]
  have hc : ((symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k)) =
      ((((symDimension (Fintype.card a) n : ℝ) / symDimension (Fintype.card a) (n+k)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, Complex.ofReal_re]

end PureFid

/-! ## The target `(ρᵀ)^{⊗k}` -/

lemma ptt_marg_star {a b : Type} [Fintype b] (w : a × b → ℂ) (rho : Op a)
    (hw : (fun i j => ∑ z : b, MixedCloning.Optimal.pure w (i,z) (j,z)) = rho) :
    (fun i j => ∑ z : b, MixedCloning.Optimal.pure (fun x => star (w x)) (i,z) (j,z)) = rhoᵀ := by
  rw [← hw]
  ext i j
  simp only [transpose_apply, MixedCloning.Optimal.pure, RCLike.star_def, Complex.conj_conj]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

lemma ptt_target {a b : Type} [Fintype a] [Fintype b] (k : ℕ) (u : a × b → ℂ) (rho : Op a)
    (hmarg : (fun i j => ∑ z : b, MixedCloning.Optimal.pure u (i,z) (j,z)) = rho) :
    partialTrace k (MixedCloning.Optimal.pure (fun c : Word (a × b) k => ∏ t, star (u (c t)))) =
      tensorPower k rhoᵀ := by
  rw [show MixedCloning.Optimal.pure (fun c : Word (a × b) k => ∏ t, star (u (c t))) =
      tensorPower k (MixedCloning.Optimal.pure (fun x => star (u x))) from
    (wb_tensorPower_pure k (fun x => star (u x))).symm, pfp_partialTrace_tensorPower, ptt_marg_star u rho hmarg]

-- ===== from PttC.lean =====

/-! ## The partial trace preserves states -/

section PT
variable {a b : Type} [Fintype a] [Fintype b]

lemma pfp_partialTrace_eq_sum (m : ℕ) (X : Op (Word (a × b) m)) :
    partialTrace m X =
      ∑ z : Word b m, X.submatrix (fun i t => (i t, z t)) (fun i t => (i t, z t)) := by
  ext i j
  simp [partialTrace, Matrix.sum_apply, submatrix_apply]

lemma pfp_partialTrace_posSemidef (m : ℕ) (X : Op (Word (a × b) m)) (hX : X.PosSemidef) :
    (partialTrace m X).PosSemidef := by
  rw [pfp_partialTrace_eq_sum]
  exact Matrix.posSemidef_sum _ fun z _ => hX.submatrix _

end PT

/-! ## Marginals and purifications -/

lemma pfp_auxAction_mulVec {d r : ℕ} (U : Matrix.unitaryGroup (Fin r) ℂ)
    (w : Fin d × Fin r → ℂ) (i : Fin d) (z : Fin r) :
    (auxAction (d := d) U *ᵥ w) (i, z) = ((U : Op (Fin r)) *ᵥ (fun z' => w (i, z'))) z := by
  simp only [Matrix.mulVec, dotProduct, auxAction]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

lemma pfp_marg_auxAction {d r : ℕ} (U : Matrix.unitaryGroup (Fin r) ℂ) (w : Fin d × Fin r → ℂ) :
    (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure (auxAction (d := d) U *ᵥ w) (i,z) (j,z)) =
      (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) := by
  funext i j
  have hU : (U : Op (Fin r))ᴴ * (U : Op (Fin r)) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp U.2
    simpa [Matrix.star_eq_conjTranspose] using h
  simp only [MixedCloning.Optimal.pure, pfp_auxAction_mulVec]
  have h1 : ∀ x y : Fin r → ℂ, ∑ z, ((U : Op (Fin r)) *ᵥ x) z * conj (((U : Op (Fin r)) *ᵥ y) z) =
      star y ⬝ᵥ x := by
    intro x y
    have h2 : ∑ z, ((U : Op (Fin r)) *ᵥ x) z * conj (((U : Op (Fin r)) *ᵥ y) z) =
        star ((U : Op (Fin r)) *ᵥ y) ⬝ᵥ ((U : Op (Fin r)) *ᵥ x) := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def]
      exact Finset.sum_congr rfl fun z _ => mul_comm _ _
    rw [h2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec]
  rw [h1]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

lemma pfp_norm_sq_of_marg {a b : Type} [Fintype a] [Fintype b] (w : EuclideanSpace ℂ (a × b))
    (ρ : Op a) (hm : (fun i j => ∑ z : b, MixedCloning.Optimal.pure w (i,z) (j,z)) = ρ) :
    ‖w‖ ^ 2 = ρ.trace.re := by
  rw [← hm, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, MixedCloning.Optimal.pure, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma pfp_sum_embed {S T : Type} [Fintype S] [Fintype T] [DecidableEq T] (φ : S ↪ T)
    (α β : S → ℂ) :
    ∑ z : T, (∑ k, if φ k = z then α k else 0) * conj (∑ k, if φ k = z then β k else 0) =
      ∑ k, α k * conj (β k) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  congr 2
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    simp [φ.injective.ne hk']
  · simp

lemma pfp_exists_embed_marg {a S T : Type} [Fintype a] [Fintype S] [Fintype T] (φ : S ↪ T)
    (B : a → S → ℂ) :
    ∃ w : a × T → ℂ, (fun i j => ∑ z : T, MixedCloning.Optimal.pure w (i,z) (j,z)) =
      fun i j => ∑ k, B i k * conj (B j k) := by
  classical
  refine ⟨fun p => ∑ k, if φ k = p.2 then B p.1 k else 0, ?_⟩
  funext i j
  simp only [MixedCloning.Optimal.pure]
  exact pfp_sum_embed φ (fun k => B i k) (fun k => B j k)

lemma pfp_exists_purification {d r : ℕ} (ρ : Op (Fin d)) (hρ : ρ.PosSemidef)
    (hrank : ρ.rank ≤ r) :
    ∃ w : Fin d × Fin r → ℂ,
      (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) = ρ := by
  have hH : ρ.IsHermitian := hρ.1
  have hcard : Fintype.card {k // hH.eigenvalues k ≠ 0} ≤ Fintype.card (Fin r) := by
    rw [Fintype.card_fin]
    have h := hH.rank_eq_card_non_zero_eigs
    convert hrank using 1
    convert h.symm
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨w, hw⟩ := pfp_exists_embed_marg φ (fun i (k : {k // hH.eigenvalues k ≠ 0}) =>
    ((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) * (hH.eigenvectorUnitary : Op (Fin d)) i k)
  refine ⟨w, hw.trans ?_⟩
  funext i j
  have hspec : ρ i j = ∑ k, (hH.eigenvectorUnitary : Op (Fin d)) i k *
      (hH.eigenvalues k : ℂ) * conj ((hH.eigenvectorUnitary : Op (Fin d)) j k) := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    simp [Matrix.mul_diagonal, Matrix.star_apply]
  rw [hspec]
  have hterm : ∀ k : {k // hH.eigenvalues k ≠ 0},
      ((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) * (hH.eigenvectorUnitary : Op (Fin d)) i k *
        conj (((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) *
          (hH.eigenvectorUnitary : Op (Fin d)) j k) =
      (hH.eigenvectorUnitary : Op (Fin d)) i k * (hH.eigenvalues k : ℂ) *
        conj ((hH.eigenvectorUnitary : Op (Fin d)) j k) := by
    intro k
    have hl : 0 ≤ hH.eigenvalues k := hρ.eigenvalues_nonneg k
    have hs : ((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) =
        (hH.eigenvalues k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
    rw [map_mul, Complex.conj_ofReal]
    linear_combination ((hH.eigenvectorUnitary : Op (Fin d)) i k *
      conj ((hH.eigenvectorUnitary : Op (Fin d)) j k)) * hs
  simp only [hterm]
  rw [← Finset.sum_subtype (Finset.univ.filter fun k => hH.eigenvalues k ≠ 0) (by simp)
    (fun k => (hH.eigenvectorUnitary : Op (Fin d)) i k * (hH.eigenvalues k : ℂ) *
      conj ((hH.eigenvectorUnitary : Op (Fin d)) j k))]
  rw [Finset.sum_filter_of_ne]
  intro k _ hk
  intro h0
  apply hk
  rw [h0]
  simp

/-! ## Integrals -/

lemma pfp_map_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →ₗ[ℝ] F) {f : α → E} (hf : Integrable f μ) :
    T (∫ x, f x ∂μ) = ∫ x, T (f x) ∂μ := by
  have h := (LinearMap.toContinuousLinearMap T).integral_comp_comm hf
  simpa only [LinearMap.coe_toContinuousLinearMap'] using h.symm

lemma pfp_integral_sqrt_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hsf : Integrable (fun x => Real.sqrt (f x)) μ) :
    ∫ x, Real.sqrt (f x) ∂μ ≤ Real.sqrt (∫ x, f x ∂μ) :=
  (Real.strictConcaveOn_sqrt.concaveOn).le_map_integral Real.continuous_sqrt.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hf0) hf hsf

lemma pfp_isClosed_state {ι : Type} [Fintype ι] : IsClosed {X : Op ι | IsState X} := by
  have hset : {X : Op ι | IsState X} =
      ({X | Xᴴ = X} ∩ ⋂ x : ι → ℂ, {X | 0 ≤ star x ⬝ᵥ (X *ᵥ x)}) ∩ {X | X.trace = 1} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, QAlgorithms.IsDensityMatrix,
      Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [hset]
  refine IsClosed.inter (IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))))
    (isClosed_eq continuous_id.matrix_trace continuous_const)

lemma pfp_convex_state {ι : Type} [Fintype ι] : Convex ℝ {X : Op ι | IsState X} := by
  intro X hX Y hY s t hs ht hst
  obtain ⟨hX1, hX2⟩ : IsState X := hX
  obtain ⟨hY1, hY2⟩ : IsState Y := hY
  show IsState (s • X + t • Y)
  refine ⟨(hX1.smul hs).add (hY1.smul ht), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX2, hY2, ← add_smul, hst, one_smul]

lemma pfp_continuous_auxAction (d r : ℕ) :
    Continuous (fun U : Matrix.unitaryGroup (Fin r) ℂ => auxAction (d := d) U) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i.1 = j.1
  · simp only [auxAction, h, if_true]
    exact continuous_subtype_val.matrix_elem i.2 j.2
  · simp only [auxAction, h, if_false]
    exact continuous_const

lemma pfp_continuous_tp {X : Type*} [TopologicalSpace X] {a : Type} [Fintype a] (n : ℕ)
    (v : X → a → ℂ) (hv : Continuous v) :
    Continuous fun x => tensorPower n (MixedCloning.Optimal.pure (v x)) := by
  refine continuous_matrix fun i j => ?_
  simp only [tensorPower, MixedCloning.Optimal.pure]
  refine continuous_finsetProd _ fun t _ => ?_
  exact ((continuous_apply _).comp hv).mul
    (Complex.continuous_conj.comp ((continuous_apply _).comp hv))

lemma pfp_integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {r : ℕ}
    (f : Matrix.unitaryGroup (Fin r) ℂ → E) (hf : Continuous f) : Integrable f (haar r) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- `X ↦ Re tr(M X)` as an `ℝ`-linear functional. -/
lemma pfp_exists_effect_linear {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) :
    ∃ T : Matrix ι ι ℂ →ₗ[ℝ] ℝ, ∀ X, T X = (M * X).trace.re :=
  ⟨{ toFun := fun X => (M * X).trace.re
     map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.trace_add]
     map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.trace_smul] },
   fun _ => rfl⟩

/-! ## Concavity -/

/-- Concavity of the root fidelity in its first argument for a continuous family of states
averaged against the Haar probability measure (Fuchs–Caves + Jensen for `√`). -/
lemma pfp_concavity {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (g : Matrix.unitaryGroup (Fin r) ℂ → Matrix ι ι ℂ) (hg : Continuous g)
    (hgs : ∀ U, IsState (g U)) (Y : Matrix ι ι ℂ) (hY : IsState Y) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ U, c ≤ fidelity (g U) Y) : c ≤ fidelity (∫ U, g U ∂haar r) Y := by
  have hg_int := pfp_integrable_of_continuous g hg
  have hG : IsState (∫ U, g U ∂haar r) :=
    pfp_convex_state.integral_mem pfp_isClosed_state (Filter.Eventually.of_forall hgs) hg_int
  obtain ⟨m, M, hM, hMeq⟩ := (MayersBC.fuchs_caves _ _ hG hY).2
  have hbound : ∀ U, Real.sqrt c ≤ ∑ j, Real.sqrt ((M j * g U).trace.re * (M j * Y).trace.re) := by
    intro U
    have h3 : Real.sqrt c ≤ QAlgorithms.rootFidelity (g U) Y :=
      (Real.sqrt_le_sqrt (hc U)).trans_eq (Real.sqrt_sq (pfp_rootFidelity_nonneg _ _))
    have h4 := (MayersBC.fuchs_caves _ _ (hgs U) hY).1 M hM
    exact h3.trans h4
  have hp_cont : ∀ j, Continuous fun U => (M j * g U).trace.re := fun j =>
    Complex.continuous_re.comp ((continuous_const.matrix_mul hg).matrix_trace)
  have hint_p : ∀ j, Integrable (fun U => (M j * g U).trace.re * (M j * Y).trace.re) (haar r) :=
    fun j => pfp_integrable_of_continuous _ ((hp_cont j).mul continuous_const)
  have hint_h : ∀ j, Integrable (fun U => Real.sqrt ((M j * g U).trace.re * (M j * Y).trace.re))
      (haar r) := fun j =>
    pfp_integrable_of_continuous _ (Real.continuous_sqrt.comp ((hp_cont j).mul continuous_const))
  have hp_nonneg : ∀ U j, 0 ≤ (M j * g U).trace.re := fun U j =>
    pfp_trace_mul_nonneg _ _ (hM.1 j) (hgs U).1
  have hq_nonneg : ∀ j, 0 ≤ (M j * Y).trace.re := fun j =>
    pfp_trace_mul_nonneg _ _ (hM.1 j) hY.1
  have hstep : Real.sqrt c ≤
      ∑ j, ∫ U, Real.sqrt ((M j * g U).trace.re * (M j * Y).trace.re) ∂haar r := by
    rw [← integral_finsetSum _ (fun j _ => hint_h j)]
    have h := integral_mono (integrable_const (Real.sqrt c))
      (integrable_finsetSum _ (fun j _ => hint_h j)) hbound
    have hconst : ∫ _U, Real.sqrt c ∂(haar r) = Real.sqrt c := by simp
    rw [hconst] at h
    exact h
  have hjensen : ∀ j, ∫ U, Real.sqrt ((M j * g U).trace.re * (M j * Y).trace.re) ∂haar r ≤
      Real.sqrt ((M j * ∫ U, g U ∂haar r).trace.re * (M j * Y).trace.re) := by
    intro j
    have h := pfp_integral_sqrt_le (haar r) _ (hint_p j)
      (fun U => mul_nonneg (hp_nonneg U j) (hq_nonneg j)) (hint_h j)
    rw [integral_mul_const] at h
    obtain ⟨T, hT⟩ := pfp_exists_effect_linear (M j)
    have hTi := pfp_map_integral T hg_int
    simp only [hT] at hTi
    rw [hTi]
    exact h
  have hfinal : Real.sqrt c ≤ QAlgorithms.rootFidelity (∫ U, g U ∂haar r) Y := by
    rw [← hMeq]
    exact hstep.trans (Finset.sum_le_sum fun j _ => hjensen j)
  show c ≤ QAlgorithms.rootFidelity (∫ U, g U ∂haar r) Y ^ 2
  calc c = Real.sqrt c ^ 2 := (Real.sq_sqrt hc0).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg c) hfinal 2

lemma pfp_rotated_purification {d r : ℕ} (rho : Op (Fin d)) (hrho : IsState rho)
    (w : Fin d × Fin r → ℂ)
    (hw : (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) = rho)
    (U : Matrix.unitaryGroup (Fin r) ℂ) :
    ‖(WithLp.toLp 2 (auxAction (d := d) U *ᵥ w) : EuclideanSpace ℂ (Fin d × Fin r))‖ = 1 ∧
      (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure
        (WithLp.toLp 2 (auxAction (d := d) U *ᵥ w) : EuclideanSpace ℂ (Fin d × Fin r))
          (i,z) (j,z)) = rho := by
  have hm : (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure
      (WithLp.toLp 2 (auxAction (d := d) U *ᵥ w) : EuclideanSpace ℂ (Fin d × Fin r)) (i,z) (j,z))
      = rho := (pfp_marg_auxAction U w).trans hw
  refine ⟨?_, hm⟩
  have h2 := pfp_norm_sq_of_marg _ rho hm
  rw [hrho.2, Complex.one_re] at h2
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]

lemma pfp_unit_purification {d r : ℕ} (rho : Op (Fin d)) (hrho : IsState rho)
    (w : Fin d × Fin r → ℂ)
    (hw : (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) = rho) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin d × Fin r))‖ = 1 := by
  have h2 := pfp_norm_sq_of_marg (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin d × Fin r)) rho hw
  rw [hrho.2, Complex.one_re] at h2
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]

/-- `(ρᵀ)^{⊗k}` is a state. -/
lemma ptt_target_isState {d r : ℕ} (k : ℕ) (rho : Op (Fin d)) (hrho : IsState rho)
    (w : Fin d × Fin r → ℂ)
    (hw : (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) = rho) :
    IsState (tensorPower k rhoᵀ) := by
  refine ⟨?_, ?_⟩
  · rw [← ptt_target k w rho hw]
    exact pfp_partialTrace_posSemidef _ _ (by
      rw [wpf_pure_eq]
      exact posSemidef_vecMulVec_self_star _)
  · rw [pfp_tensorPower_trace, Matrix.trace_transpose, hrho.2, one_pow]

/-- The PTT output is the Haar average of traced transposer outputs on random purifications, so
by concavity a bound valid for every unit purification transfers to the PTT output. -/
lemma ptt_fidelity_ge_of_purifications (d r n k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n)) (hR : IsRPC d r n R)
    (tau : Op (Word (Fin d × Fin r) k)) (htau : IsState tau)
    (rho : Op (Fin d)) (hrho : IsState rho) (hrank : rho.rank ≤ r) (c : ℝ)
    (hc : ∀ u : EuclideanSpace ℂ (Fin d × Fin r), ‖u‖ = 1 →
      (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure u (i,z) (j,z)) = rho →
      c ≤ fidelity (partialTrace k (wernerTransposer (Fin d × Fin r) n k tau
        (tensorPower n (MixedCloning.Optimal.pure u)))) (tensorPower k rhoᵀ)) :
    c ≤ fidelity (ptt d r n k R tau (tensorPower n rho)) (tensorPower k rhoᵀ) := by
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact hc0.le.trans (sq_nonneg _)
  have hD : 0 < Fintype.card (Fin d × Fin r) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hd hr
  have hWT := ptt_isChannel_comp _ _ (ptt_transposer_isChannel (a := Fin d × Fin r) n k hD tau htau)
    (ptt_partialTrace_isChannel (a := Fin d) (b := Fin r) k)
  obtain ⟨L, hL0⟩ := ptt_channel_linear _ hWT
  have hL : ∀ X, L X = partialTrace k (wernerTransposer (Fin d × Fin r) n k tau X) :=
    fun X => hL0 X
  obtain ⟨w, hw⟩ := pfp_exists_purification rho hrho.1 hrank
  have hRint := hR.2 rho hrho hrank _ (pfp_unit_purification rho hrho w hw) hw
  obtain ⟨f, hf⟩ : ∃ f : Matrix.unitaryGroup (Fin r) ℂ → Op (Word (Fin d × Fin r) n),
      ∀ U, f U = tensorPower n (MixedCloning.Optimal.pure (auxAction (d := d) U *ᵥ w)) :=
    ⟨_, fun _ => rfl⟩
  have hfun : (fun U : Matrix.unitaryGroup (Fin r) ℂ =>
      tensorPower n (auxAction (d := d) U) * tensorPower n (MixedCloning.Optimal.pure w) *
        (tensorPower n (auxAction (d := d) U))ᴴ) = f := by
    funext U
    rw [hf]
    exact pfp_conj_tensorPower_pure n _ w
  have hRf : R (tensorPower n rho) = ∫ U, f U ∂haar r := by
    rw [← hfun]
    exact hRint
  have hf_cont : Continuous f := by
    rw [show f = fun U => tensorPower n (MixedCloning.Optimal.pure (auxAction (d := d) U *ᵥ w))
      from funext hf]
    exact pfp_continuous_tp n _ ((pfp_continuous_auxAction d r).matrix_mulVec continuous_const)
  have hf_int := pfp_integrable_of_continuous f hf_cont
  have hptt : ptt d r n k R tau (tensorPower n rho) = ∫ U, L (f U) ∂haar r := by
    show partialTrace k (wernerTransposer (Fin d × Fin r) n k tau (R (tensorPower n rho))) = _
    rw [← hL, hRf]
    exact pfp_map_integral (L.restrictScalars ℝ) hf_int
  rw [hptt]
  refine pfp_concavity (fun U => L (f U)) (L.continuous_of_finiteDimensional.comp hf_cont)
    ?_ _ (ptt_target_isState k rho hrho w hw) c hc0 ?_
  · intro U
    show IsState (L (f U))
    rw [hL0, hf]
    exact ptt_channel_state _ hWT _ (ptt_tensorPower_pure_isState n _
      (ptt_norm_sum _ (pfp_rotated_purification rho hrho w hw U).1))
  · intro U
    have h1 := hc _ (pfp_rotated_purification rho hrho w hw U).1
      (pfp_rotated_purification rho hrho w hw U).2
    show c ≤ fidelity (L (f U)) (tensorPower k rhoᵀ)
    rw [hL, hf]
    exact h1

theorem solution (d r n k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : 1 ≤ n)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n))
    (hR : IsRPC d r n R) (tau : Op (Word (Fin d × Fin r) k)) (htau : IsState tau) :
    Transposes d r n k ((k : ℝ)*r*d/n) (ptt d r n k R tau) ∧
    ∀ eps : ℝ, 0 < eps → Nat.ceil ((k : ℝ)*r*d/eps) ≤ n →
      Transposes d r n k eps (ptt d r n k R tau) := by
  have hD : 0 < Fintype.card (Fin d × Fin r) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hd hr
  have hch : QAlgorithms.IsChannel (ptt d r n k R tau) := by
    have hW := ptt_transposer_isChannel (a := Fin d × Fin r) n k hD tau htau
    have hT := ptt_partialTrace_isChannel (a := Fin d) (b := Fin r) k
    have h1 := ptt_isChannel_comp _ _ hW hT
    exact ptt_isChannel_comp R _ hR.1 h1
  have hmain : ∀ rho : Op (Fin d), IsState rho → rho.rank ≤ r →
      1 - (k : ℝ)*r*d/n ≤
        fidelity (ptt d r n k R tau (tensorPower n rho)) (tensorPower k rhoᵀ) := by
    intro rho hrho hrank
    apply ptt_fidelity_ge_of_purifications d r n k hd hr R hR tau htau rho hrho hrank
    intro u hu hmarg
    obtain ⟨hstate, hfid⟩ := ptt_pure_fidelity (a := Fin d × Fin r) n k hD tau htau u.ofLp
      (ptt_norm_sum u hu)
    have hcard : Fintype.card (Fin d × Fin r) = d * r := by simp
    have h6 := lemma_6 n (d*r) k hn (Nat.mul_pos hd hr)
    have hratio : 1 - (k : ℝ)*r*d/n ≤ (symDimension (Fintype.card (Fin d × Fin r)) n : ℝ) /
        symDimension (Fintype.card (Fin d × Fin r)) (n+k) := by
      rw [hcard]
      calc 1 - (k : ℝ)*r*d/n = 1 - (k : ℝ)*((d*r : ℕ) : ℝ)/n := by push_cast; ring
        _ ≤ _ := h6
    have h7 := hratio.trans_eq hfid.symm
    have hdp := fidelity_le_partialTrace (a := Fin d) (b := Fin r) k
      (wernerTransposer (Fin d × Fin r) n k tau (tensorPower n (MixedCloning.Optimal.pure u)))
      (MixedCloning.Optimal.pure (fun c : Word (Fin d × Fin r) k => ∏ t, star (u.ofLp (c t))))
      hstate.1 (by rw [wpf_pure_eq]; exact posSemidef_vecMulVec_self_star _)
    rw [← ptt_target k u.ofLp rho hmarg]
    exact h7.trans hdp
  refine ⟨⟨hch, hmain⟩, ?_⟩
  intro eps heps hceil
  refine ⟨hch, fun rho hrho hrank => le_trans ?_ (hmain rho hrho hrank)⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (k : ℝ)*r*d/eps ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have h2 : (k : ℝ)*r*d/n ≤ eps := by
    rw [div_le_iff₀ hn']
    rw [div_le_iff₀ heps] at h1
    linarith
  linarith
