-- Prove2me | solution 1 for MixedCloning.Optimal.pct_isChannel
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:10:01.493854+00:00
-- url     : https://prove2.me/submissions/e50c5384-45d9-408f-84f1-42b0039d3fc4

import Theorems.Thm_MixedCloning_Optimal_werner_trace_bose

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ### General facts about Kraus channels -/

section Kraus
open QAlgorithms

/-- The `DecidableEq` instance inside `IsChannel` is irrelevant. -/
lemma pci_isChannel_transport {ι κ : Type*} [Fintype ι] [Fintype κ] (i₁ i₂ : DecidableEq ι)
    (Φ : Superop ι κ) (h : @IsChannel ι κ _ _ i₁ Φ) : @IsChannel ι κ _ _ i₂ Φ := by
  cases Subsingleton.elim i₁ i₂
  exact h

/-- A normalized Kraus family over any finite index type gives a channel. -/
lemma pci_isChannel_of_kraus {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
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

/-- The composition of two channels is a channel. -/
lemma pci_isChannel_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    {_ : DecidableEq ι} {_ : DecidableEq κ} (Φ : Superop ι κ) (Ψ : Superop κ μ)
    (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) : IsChannel (fun X => Ψ (Φ X)) := by
  obtain ⟨m₁, E, hE, hΦE⟩ := hΦ
  obtain ⟨m₂, F, hF, hΨF⟩ := hΨ
  refine pci_isChannel_of_kraus _ (fun p : Fin m₁ × Fin m₂ => F p.2 * E p.1) ?_ ?_
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

end Kraus

/-! ### The partial trace is a channel -/

section PartialTrace

lemma pci_partialTrace_isChannel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (m : ℕ) :
    QAlgorithms.IsChannel (fun X : Op (Word (a × b) m) => partialTrace (a := a) m X) := by
  let E : Word b m → Matrix (Word a m) (Word (a × b) m) ℂ :=
    fun z => Matrix.of fun i w => if w = (fun t => (i t, z t)) then 1 else 0
  refine pci_isChannel_of_kraus _ E ?_ ?_
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

end PartialTrace

/-! ### The completed Werner map is a channel -/

section Factor
open scoped MatrixOrder

/-- A positive semidefinite matrix factors as `Bᴴ B`. -/
lemma pci_psd_factor {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.PosSemidef) : ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, by rw [hB, star_eq_conjTranspose]⟩

end Factor

/-- `∑_{i,j} E_{ij} Y E_{ji} = tr(Y) · 1` for matrix units `E_{ij}`. -/
lemma pci_sum_single {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
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

section Werner
variable {a : Type} [Fintype a]

lemma pci_permMatrix_mul (m : ℕ) (p q : Equiv.Perm (Fin m)) :
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

lemma pci_permMatrix_mul_symProjector (m : ℕ) (p : Equiv.Perm (Fin m)) :
    permMatrix (a := a) m p * symProjector a m = symProjector a m := by
  unfold symProjector
  rw [Matrix.mul_smul, Matrix.mul_sum]
  simp only [pci_permMatrix_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft p) (fun q => permMatrix (a := a) m q)

/-- `Π_m² = Π_m`. -/
lemma pci_symProjector_mul_self (m : ℕ) :
    symProjector a m * symProjector a m = symProjector a m := by
  calc symProjector a m * symProjector a m
      = ((Nat.factorial m : ℂ)⁻¹ • ∑ p : Equiv.Perm (Fin m), permMatrix (a := a) m p) *
          symProjector a m := rfl
    _ = symProjector a m := by
      rw [Matrix.smul_mul, Matrix.sum_mul]
      simp only [pci_permMatrix_mul_symProjector, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero m)), one_smul]

omit [Fintype a] in
lemma pci_permMatrix_conjTranspose (m : ℕ) (p : Equiv.Perm (Fin m)) :
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

/-- `Π_mᴴ = Π_m`. -/
lemma pci_symProjector_conjTranspose (m : ℕ) : (symProjector a m)ᴴ = symProjector a m := by
  unfold symProjector
  rw [conjTranspose_smul, conjTranspose_sum]
  simp only [pci_permMatrix_conjTranspose]
  have hsum : ∑ x : Equiv.Perm (Fin m), permMatrix (a := a) m x⁻¹ = ∑ p, permMatrix m p :=
    Equiv.sum_comp (Equiv.inv _) (fun p => permMatrix (a := a) m p)
  rw [hsum]
  congr 1
  simp

/-- `V_z : |y⟩ ↦ |y z⟩` appends the word `z`. -/
def pciV (n k : ℕ) (z : Word a k) : Matrix (Word a (n+k)) (Word a n) ℂ :=
  Matrix.of fun w y =>
    if (fun t => w (Fin.castAdd k t)) = y ∧ (fun t => w (Fin.natAdd n t)) = z then 1 else 0

/-- `Σ_z V_z Y V_zᴴ = Y ⊗ I`. -/
lemma pci_sum_V (n k : ℕ) (Y : Op (Word a n)) :
    ∑ z : Word a k, pciV n k z * Y * (pciV n k z)ᴴ = appendIdentity n k Y := by
  ext w w'
  simp only [pciV, appendIdentity, Matrix.sum_apply, mul_apply, conjTranspose_apply, of_apply,
    apply_ite star, star_one, star_zero, ite_and, ite_mul, mul_ite, one_mul, mul_one, zero_mul,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- `tr(Q (Y ⊗ I) Q) = tr(T Y)` with `T = Σ_z V_zᴴ Q V_z`. -/
lemma pci_trace_Q_append (n k : ℕ) (Y : Op (Word a n)) :
    (symProjector a (n+k) * appendIdentity n k Y * symProjector a (n+k)).trace =
      ((∑ z : Word a k, (pciV n k z)ᴴ * symProjector a (n+k) * pciV n k z) * Y).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, pci_symProjector_mul_self, ← pci_sum_V n k Y,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (symProjector a (n+k))]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (pciV n k z)]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Y]
  simp only [Matrix.mul_assoc]

/-- From the child `werner_trace_bose`, by trace duality:
`d[n] · Π_n T Π_n = d[n+k] · Π_n`, where `T = tr_k Π_{n+k} = Σ_z V_zᴴ Π_{n+k} V_z`. -/
lemma pci_PTP (n k : ℕ) :
    (symDimension (Fintype.card a) n : ℂ) • (symProjector a n *
        (∑ z : Word a k, (pciV n k z)ᴴ * symProjector a (n+k) * pciV n k z) * symProjector a n) =
      (symDimension (Fintype.card a) (n+k) : ℂ) • symProjector a n := by
  rw [Matrix.ext_iff_trace_mul_right]
  intro X
  have h := werner_trace_bose (a := a) n k X
  rw [pci_trace_Q_append] at h
  set P := symProjector a n with hP
  set T := ∑ z : Word a k, (pciV n k z)ᴴ * symProjector a (n+k) * pciV n k z with hT
  have hPP : P * P = P := pci_symProjector_mul_self n
  have e1 : (P * T * P * X).trace = (T * (P * X * P)).trace := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm P]
    simp only [Matrix.mul_assoc]
  have e2 : (P * X * P).trace = (P * X).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPP]
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul, e1, ← e2]
  exact h

/-- Normalization of the Kraus operators `K_z = s Π_{n+k} V_z Π_n`, `|s|² = d[n]/d[n+k]`. -/
lemma pci_K_norm (n k : ℕ) (hD : 0 < Fintype.card a) (s : ℂ)
    (hs : star s * s =
      (symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k)) :
    ∑ z : Word a k, (s • (symProjector a (n+k) * pciV n k z * symProjector a n))ᴴ *
        (s • (symProjector a (n+k) * pciV n k z * symProjector a n)) = symProjector a n := by
  have hdpos : ∀ m, 0 < symDimension (Fintype.card a) m := fun m => by
    unfold symDimension; exact Nat.choose_pos (by omega)
  have hdnk : (symDimension (Fintype.card a) (n+k) : ℂ) ≠ 0 := by
    exact_mod_cast (hdpos (n+k)).ne'
  have hPh : (symProjector a n)ᴴ = symProjector a n := pci_symProjector_conjTranspose n
  have hQh : (symProjector a (n+k))ᴴ = symProjector a (n+k) :=
    pci_symProjector_conjTranspose (n+k)
  have hQQ : symProjector a (n+k) * symProjector a (n+k) = symProjector a (n+k) :=
    pci_symProjector_mul_self (n+k)
  have e : ∀ z : Word a k, (s • (symProjector a (n+k) * pciV n k z * symProjector a n))ᴴ *
        (s • (symProjector a (n+k) * pciV n k z * symProjector a n)) =
      (star s * s) • (symProjector a n *
        ((pciV n k z)ᴴ * symProjector a (n+k) * pciV n k z) * symProjector a n) := by
    intro z
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul,
      hPh, hQh, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (symProjector a (n+k)) (symProjector a (n+k)), hQQ, mul_comm s (star s)]
  simp only [e]
  rw [← Finset.smul_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hs, div_eq_inv_mul, ← smul_smul,
    pci_PTP, smul_smul, inv_mul_cancel₀ hdnk, one_smul]

/-- Normalization of the Kraus operators `L_{ij} = Bᴴ E_{ij} (1 - Π_n)`, `tr(Bᴴ B) = 1`. -/
lemma pci_L_norm (n k : ℕ) (B : Op (Word a (n+k))) (hB : (Bᴴ * B).trace = 1) :
    ∑ ij : Word a (n+k) × Word a n, (Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n))ᴴ *
        (Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n)) = 1 - symProjector a n := by
  set M : Op (Word a n) := 1 - symProjector a n with hM
  have hMh : Mᴴ = M := by
    rw [hM, conjTranspose_sub, conjTranspose_one, pci_symProjector_conjTranspose]
  have hMM : M * M = M := by
    rw [hM]
    simp only [sub_mul, mul_sub, one_mul, mul_one, pci_symProjector_mul_self, sub_self, sub_zero]
  have e : ∀ ij : Word a (n+k) × Word a n,
      (Bᴴ * single ij.1 ij.2 (1 : ℂ) * M)ᴴ * (Bᴴ * single ij.1 ij.2 (1 : ℂ) * M) =
        M * (single ij.2 ij.1 (1 : ℂ) * (B * Bᴴ) * single ij.1 ij.2 (1 : ℂ)) * M := by
    intro ij
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_single, star_one,
      conjTranspose_conjTranspose, hMh]
    simp only [Matrix.mul_assoc]
  simp only [e]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Fintype.sum_prod_type, Finset.sum_comm, pci_sum_single,
    Matrix.trace_mul_comm, hB, one_smul, Matrix.mul_one, hMM]

/-- Action of the `K` part: `Σ_z K_z X K_zᴴ = |s|² Π_{n+k} (Π_n X Π_n ⊗ I) Π_{n+k}`. -/
lemma pci_K_action (n k : ℕ) (s : ℂ) (X : Op (Word a n)) :
    ∑ z : Word a k, (s • (symProjector a (n+k) * pciV n k z * symProjector a n)) * X *
        (s • (symProjector a (n+k) * pciV n k z * symProjector a n))ᴴ =
      (s * star s) • (symProjector a (n+k) *
        appendIdentity n k (symProjector a n * X * symProjector a n) * symProjector a (n+k)) := by
  rw [← pci_sum_V n k, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul,
    pci_symProjector_conjTranspose, Matrix.mul_assoc]
  rw [mul_comm (star s) s]

/-- Action of the `L` part: `Σ_{ij} L_{ij} X L_{ij}ᴴ = tr((1 - Π_n) X) Bᴴ B`. -/
lemma pci_L_action (n k : ℕ) (B : Op (Word a (n+k))) (X : Op (Word a n)) :
    ∑ ij : Word a (n+k) × Word a n, (Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n)) * X *
        (Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n))ᴴ =
      ((1 - symProjector a n) * X).trace • (Bᴴ * B) := by
  set M : Op (Word a n) := 1 - symProjector a n with hM
  have hMh : Mᴴ = M := by
    rw [hM, conjTranspose_sub, conjTranspose_one, pci_symProjector_conjTranspose]
  have hMM : M * M = M := by
    rw [hM]
    simp only [sub_mul, mul_sub, one_mul, mul_one, pci_symProjector_mul_self, sub_self, sub_zero]
  have e : ∀ ij : Word a (n+k) × Word a n,
      (Bᴴ * single ij.1 ij.2 (1 : ℂ) * M) * X * (Bᴴ * single ij.1 ij.2 (1 : ℂ) * M)ᴴ =
        Bᴴ * (single ij.1 ij.2 (1 : ℂ) * (M * X * M) * single ij.2 ij.1 (1 : ℂ)) * B := by
    intro ij
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_single, star_one,
      conjTranspose_conjTranspose, hMh]
    simp only [Matrix.mul_assoc]
  simp only [e]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Fintype.sum_prod_type, pci_sum_single, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul]
  congr 1
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hMM]

/-- The completed Werner map is a channel whenever `tau` is a state. -/
lemma pci_werner_isChannel (n k : ℕ) (hD : 0 < Fintype.card a) (tau : Op (Word a (n+k)))
    (htau : IsState tau) : QAlgorithms.IsChannel (werner a n k tau) := by
  obtain ⟨B, hB⟩ := pci_psd_factor tau htau.1
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
  let K : Word a k ⊕ (Word a (n+k) × Word a n) → Matrix (Word a (n+k)) (Word a n) ℂ :=
    Sum.elim (fun z => s • (symProjector a (n+k) * pciV n k z * symProjector a n))
      (fun ij => Bᴴ * single ij.1 ij.2 (1 : ℂ) * (1 - symProjector a n))
  refine pci_isChannel_of_kraus _ K ?_ ?_
  · rw [Fintype.sum_sum_type]
    simp only [K, Sum.elim_inl, Sum.elim_inr]
    rw [pci_K_norm n k hD s hss, pci_L_norm n k B htr]
    abel
  · intro X
    rw [Fintype.sum_sum_type]
    simp only [K, Sum.elim_inl, Sum.elim_inr]
    rw [pci_K_action, pci_L_action, hss', ← hB]
    rfl

end Werner

theorem solution (d r n k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n))
    (hR : QAlgorithms.IsChannel R)
    (tau : Op (Word (Fin d × Fin r) (n+k))) (htau : IsState tau) :
    QAlgorithms.IsChannel (pct d r n k R tau) := by
  have hD : 0 < Fintype.card (Fin d × Fin r) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hd hr
  have hW := pci_werner_isChannel (a := Fin d × Fin r) n k hD tau htau
  have hT := pci_partialTrace_isChannel (a := Fin d) (b := Fin r) (n+k)
  have h1 := pci_isChannel_comp _ _ hW hT
  have h2 := pci_isChannel_comp R _ hR h1
  exact h2
