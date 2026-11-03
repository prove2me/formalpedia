-- Prove2me | solution 1 for HorodeckiBoundKey.filter_key_rate
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T16:03:48.994196+00:00
-- url     : https://prove2.me/submissions/42866e03-592c-466e-932f-00e01842d525

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_HorodeckiBoundKey_finCut
import Definitions.Def_HorodeckiBoundKey_keyPower
import Definitions.Def_HorodeckiBoundKey_localPair

/-!
# `HorodeckiBoundKey.filter_key_rate`

Key distilled from the output of a local filter on blocks of `n` copies counts for the input:
`K(ρ) ≥ (q/n) K(σ)`.

Structure of the proof (all in namespace `FKR`):
* `LOCC`/`Abs`: closure properties of `FiniteLOCC` (linearity, positivity and trace
  preservation, composition, local relabellings) and LOCC maps between arbitrary finite
  bipartite systems (`IsLOCCAbs`), with local instruments with arbitrary outcome sets.
* `TraceNorm`: triangle inequality and homogeneity of the trace norm (via the polar
  decomposition), trace norm of density matrices.
* `Tensor`: tensor products of operator families, heterogeneous product states, the
  selection channel (keep some registers, discard the rest) and the discard-and-prepare channel.
* `Cheb`: Chebyshev bound for the number of successes in independent trials.
* `Proto`/`Error`: the block-filtering protocol and the exact computation and error bound of
  its output.
* `FilterRate`: rate `r` of `ω'` and a filter `ω ↦ q ω'` give rate `q r` of `ω`.
* `Block`: rate `R` of the `n`-copy block state gives rate `R / n`.
* `Main`: translation of `keyPower`/`localPair`/`finCut` and the final statement.
-/

section FKR_LOCC

/-!
# Basic closure properties of `FiniteLOCC`

`FiniteLOCC` (Information100.P21) is the inductive class of finite adaptive LOCC trees on
`Fin a × Fin b`.  We prove that every such map is additive, homogeneous, positivity and trace
preserving, that the class is closed under composition and under local relabellings, and we
transport it to maps between arbitrary finite types (`IsLOCCAbs`), where local instruments with
arbitrary outcome sets can be used.
-/

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

open Matrix

lemma kron_eq {R l m n p : Type*} [Mul R] (A : Matrix l m R) (B : Matrix n p R) :
    Matrix.kronecker A B = A ⊗ₖ B := rfl

section Basic

variable {a b c d : ℕ}

lemma kraus_sum_one {k h a b : ℕ} (E : Fin k → Matrix (Fin h) (Fin a) ℂ)
    (hE : IsKrausFamily E) :
    ∑ i, (Matrix.kronecker (E i) (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ *
      Matrix.kronecker (E i) (1 : Matrix (Fin b) (Fin b) ℂ) = 1 := by
  simp only [kron_eq, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.mul_one]
  have : ∑ i, ((E i)ᴴ * E i) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) =
      (∑ i, (E i)ᴴ * E i) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) := by
    ext x y
    simp [Matrix.sum_apply, Finset.sum_mul]
  rw [this]
  unfold IsKrausFamily at hE
  rw [hE, one_kronecker_one]

lemma kraus_sum_one' {k h a b : ℕ} (E : Fin k → Matrix (Fin h) (Fin b) ℂ)
    (hE : IsKrausFamily E) :
    ∑ i, (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (E i))ᴴ *
      Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (E i) = 1 := by
  simp only [kron_eq, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.mul_one]
  have : ∑ i, (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ ((E i)ᴴ * E i) =
      (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (∑ i, (E i)ᴴ * E i) := by
    ext x y
    simp [Matrix.sum_apply, Finset.mul_sum]
  rw [this]
  unfold IsKrausFamily at hE
  rw [hE, one_kronecker_one]

theorem locc_map_add {L : Superop (Fin a × Fin b) (Fin c × Fin d)} (h : FiniteLOCC L) :
    ∀ X Y, L (X + Y) = L X + L Y := by
  induction h with
  | identity a b => intro X Y; rfl
  | alice E complete next valid ih =>
    intro X Y
    simp only [Matrix.mul_add, Matrix.add_mul, ih, Finset.sum_add_distrib]
  | bob E complete next valid ih =>
    intro X Y
    simp only [Matrix.mul_add, Matrix.add_mul, ih, Finset.sum_add_distrib]

theorem locc_map_smul {L : Superop (Fin a × Fin b) (Fin c × Fin d)} (h : FiniteLOCC L) :
    ∀ (r : ℂ) X, L (r • X) = r • L X := by
  induction h with
  | identity a b => intro r X; rfl
  | alice E complete next valid ih =>
    intro r X
    simp only [Matrix.mul_smul, Matrix.smul_mul, ih, Finset.smul_sum]
  | bob E complete next valid ih =>
    intro r X
    simp only [Matrix.mul_smul, Matrix.smul_mul, ih, Finset.smul_sum]

theorem locc_map_zero {L : Superop (Fin a × Fin b) (Fin c × Fin d)} (h : FiniteLOCC L) :
    L 0 = 0 := by
  have := locc_map_smul h 0 0
  simpa using this

theorem locc_map_sum {L : Superop (Fin a × Fin b) (Fin c × Fin d)} (h : FiniteLOCC L)
    {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    L (∑ i ∈ s, X i) = ∑ i ∈ s, L (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [locc_map_zero h]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, locc_map_add h, ih]

theorem locc_posSemidef {L : Superop (Fin a × Fin b) (Fin c × Fin d)} (h : FiniteLOCC L) :
    ∀ X, X.PosSemidef → (L X).PosSemidef := by
  induction h with
  | identity a b => intro X hX; exact hX
  | alice E complete next valid ih =>
    intro X hX
    exact Matrix.posSemidef_sum _ fun i _ => ih i _ (hX.mul_mul_conjTranspose_same _)
  | bob E complete next valid ih =>
    intro X hX
    exact Matrix.posSemidef_sum _ fun i _ => ih i _ (hX.mul_mul_conjTranspose_same _)

lemma trace_conj_sum {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n] [DecidableEq n]
    (K : ι → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix n n ℂ) :
    ∑ i, (K i * X * (K i)ᴴ).trace = X.trace := by
  have e : ∀ i, (K i * X * (K i)ᴴ).trace = ((K i)ᴴ * K i * X).trace := by
    intro i
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [e, ← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

theorem locc_trace {L : Superop (Fin a × Fin b) (Fin c × Fin d)} (h : FiniteLOCC L) :
    ∀ X, (L X).trace = X.trace := by
  induction h with
  | identity a b => intro X; rfl
  | alice E complete next valid ih =>
    intro X
    simp only [Matrix.trace_sum, ih]
    exact trace_conj_sum _ (kraus_sum_one E complete) X
  | bob E complete next valid ih =>
    intro X
    simp only [Matrix.trace_sum, ih]
    exact trace_conj_sum _ (kraus_sum_one' E complete) X

theorem locc_comp {e f : ℕ} {L1 : Superop (Fin a × Fin b) (Fin c × Fin d)}
    (h1 : FiniteLOCC L1) :
    ∀ {L2 : Superop (Fin c × Fin d) (Fin e × Fin f)}, FiniteLOCC L2 →
      FiniteLOCC (fun X => L2 (L1 X)) := by
  induction h1 with
  | identity a b => intro L2 h2; exact h2
  | @alice a b c d h k E complete next valid ih =>
    intro L2 h2
    convert FiniteLOCC.alice E complete (fun i => fun Y => L2 (next i Y)) (fun i => ih i h2)
      using 1
    funext X
    exact locc_map_sum h2 _ _
  | @bob a b c d h k E complete next valid ih =>
    intro L2 h2
    convert FiniteLOCC.bob E complete (fun i => fun Y => L2 (next i Y)) (fun i => ih i h2)
      using 1
    funext X
    exact locc_map_sum h2 _ _

end Basic

/-! ### Permutation matrices and local relabellings -/

section Perm

variable {α α' : Type*} [DecidableEq α]

/-- The permutation matrix of an equivalence: `P x' x = 1` iff `x = e x'`. -/
def pmat (e : α' ≃ α) : Matrix α' α ℂ := fun x' x => if x = e x' then 1 else 0

lemma pmat_conj_mul [Fintype α'] [DecidableEq α'] (e : α' ≃ α) : (pmat e)ᴴ * pmat e = 1 := by
  ext x y
  simp only [Matrix.mul_apply, conjTranspose_apply, pmat, Matrix.one_apply]
  rw [Finset.sum_eq_single (e.symm x)]
  · simp only [Equiv.apply_symm_apply, if_true, star_one, one_mul]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg (fun h' => h (by rw [h'])), if_neg h]
  · intro z _ hz
    rw [if_neg (fun h' => hz (by rw [h', Equiv.symm_apply_apply])), star_zero, zero_mul]
  · simp

lemma pmat_mul_mul [Fintype α] [Fintype α'] (e : α' ≃ α) (X : Matrix α α ℂ) :
    pmat e * X * (pmat e)ᴴ = X.submatrix e e := by
  ext x y
  simp only [Matrix.mul_apply, conjTranspose_apply, pmat, submatrix_apply]
  rw [Finset.sum_eq_single (e y)]
  · rw [if_pos rfl, star_one, mul_one, Finset.sum_eq_single (e x)]
    · simp
    · intro z _ hz; rw [if_neg hz, zero_mul]
    · simp
  · intro z _ hz
    rw [if_neg (fun h' => hz h'), star_zero, mul_zero]
  · simp

lemma pmat_kron_one {β : Type*} [DecidableEq β] (e : α' ≃ α) :
    Matrix.kronecker (pmat e) (1 : Matrix β β ℂ) = pmat (e.prodCongr (Equiv.refl β)) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [kron_eq, kronecker_apply, pmat, Matrix.one_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id_eq, Prod.mk.injEq]
  by_cases h1 : y1 = e x1 <;> by_cases h2 : x2 = y2 <;> simp [h1, h2, eq_comm]

lemma one_kron_pmat {β : Type*} [DecidableEq β] (e : α' ≃ α) :
    Matrix.kronecker (1 : Matrix β β ℂ) (pmat e) = pmat ((Equiv.refl β).prodCongr e) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [kron_eq, kronecker_apply, pmat, Matrix.one_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id_eq, Prod.mk.injEq]
  by_cases h1 : y2 = e x2 <;> by_cases h2 : x1 = y1 <;> simp [h1, h2, eq_comm]

end Perm

section Reidx

variable {a b a' b' c d : ℕ}

/-- Local relabellings are finite LOCC maps. -/
theorem locc_reidx (eA : Fin a' ≃ Fin a) (eB : Fin b' ≃ Fin b) :
    FiniteLOCC (fun X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ =>
      X.submatrix (Prod.map eA eB) (Prod.map eA eB)) := by
  have hA : IsKrausFamily (fun _ : Fin 1 => pmat eA) := by
    simp [IsKrausFamily, pmat_conj_mul]
  have hB : IsKrausFamily (fun _ : Fin 1 => pmat eB) := by
    simp [IsKrausFamily, pmat_conj_mul]
  have h := FiniteLOCC.alice (fun _ : Fin 1 => pmat eA) hA
    (fun _ => fun Y => ∑ j : Fin 1, (fun _ : Fin 1 => fun Z : Matrix (Fin a' × Fin b')
      (Fin a' × Fin b') ℂ => Z) j ((Matrix.kronecker (1 : Matrix (Fin a') (Fin a') ℂ) (pmat eB)) * Y *
        (Matrix.kronecker (1 : Matrix (Fin a') (Fin a') ℂ) (pmat eB))ᴴ))
    (fun _ => FiniteLOCC.bob (fun _ : Fin 1 => pmat eB) hB _ fun _ => FiniteLOCC.identity _ _)
  convert h using 1
  funext X
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [pmat_kron_one, pmat_mul_mul, one_kron_pmat, pmat_mul_mul, submatrix_submatrix]
  rfl

theorem locc_pre {L : Superop (Fin a × Fin b) (Fin c × Fin d)} (h : FiniteLOCC L)
    (eA : Fin a' ≃ Fin a) (eB : Fin b' ≃ Fin b) :
    FiniteLOCC (fun X : Matrix (Fin a' × Fin b') (Fin a' × Fin b') ℂ =>
      L (X.submatrix (Prod.map eA.symm eB.symm) (Prod.map eA.symm eB.symm))) :=
  locc_comp (locc_reidx eA.symm eB.symm) h

theorem locc_post {c' d' : ℕ} {L : Superop (Fin a × Fin b) (Fin c × Fin d)} (h : FiniteLOCC L)
    (eC : Fin c' ≃ Fin c) (eD : Fin d' ≃ Fin d) :
    FiniteLOCC (fun X => (L X).submatrix (Prod.map eC eD) (Prod.map eC eD)) :=
  locc_comp h (locc_reidx eC eD)

end Reidx

end FKR

end FKR_LOCC

section FKR_Abs

/-!
# LOCC maps between arbitrary finite bipartite systems
-/

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

open Matrix

lemma submatrix_sum {ι m n m' n' : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ)
    (f : m' → m) (g : n' → n) : (∑ i ∈ s, A i).submatrix f g = ∑ i ∈ s, (A i).submatrix f g := by
  ext x y
  simp [Matrix.sum_apply]

lemma trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (Y : Matrix κ κ ℂ)
    (e : ι ≃ κ) : (Y.submatrix e e).trace = Y.trace := by
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact Equiv.sum_comp e (fun j => Y j j)

lemma prodMap_eq {α β γ δ : Type*} (e : α ≃ γ) (f : β ≃ δ) :
    Prod.map ⇑e ⇑f = ⇑(e.prodCongr f) := rfl

lemma prodMap_symm_comp {α β γ δ : Type*} (e : α ≃ γ) (f : β ≃ δ) :
    Prod.map ⇑e.symm ⇑f.symm ∘ Prod.map ⇑e ⇑f = id := by
  funext ⟨x1, x2⟩; simp

lemma submatrix_add' {m n m' n' : Type*} (A B : Matrix m n ℂ) (f : m' → m) (g : n' → n) :
    (A + B).submatrix f g = A.submatrix f g + B.submatrix f g := rfl

lemma submatrix_smul' {m n m' n' : Type*} (r : ℂ) (A : Matrix m n ℂ) (f : m' → m) (g : n' → n) :
    (r • A).submatrix f g = r • A.submatrix f g := rfl

section Abs

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- A map between operators on arbitrary finite bipartite systems is LOCC if, after some
local identifications of the four registers with `Fin` types, it is a `FiniteLOCC` map. -/
def IsLOCCAbs (Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ) : Prop :=
  ∃ (a b c d : ℕ) (eα : α ≃ Fin a) (eβ : β ≃ Fin b) (eγ : γ ≃ Fin c) (eδ : δ ≃ Fin d)
    (L : Superop (Fin a × Fin b) (Fin c × Fin d)), FiniteLOCC L ∧
    ∀ X, Φ X = (L (X.submatrix (Prod.map eα.symm eβ.symm) (Prod.map eα.symm eβ.symm))).submatrix
      (Prod.map eγ eδ) (Prod.map eγ eδ)

theorem IsLOCCAbs.encode {Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (h : IsLOCCAbs Φ) {a' b' c' d' : ℕ} (eα' : α ≃ Fin a') (eβ' : β ≃ Fin b')
    (eγ' : γ ≃ Fin c') (eδ' : δ ≃ Fin d') :
    FiniteLOCC (fun X : Matrix (Fin a' × Fin b') (Fin a' × Fin b') ℂ =>
      (Φ (X.submatrix (Prod.map eα' eβ') (Prod.map eα' eβ'))).submatrix
        (Prod.map eγ'.symm eδ'.symm) (Prod.map eγ'.symm eδ'.symm)) := by
  obtain ⟨a, b, c, d, eα, eβ, eγ, eδ, L, hL, hΦ⟩ := h
  convert locc_post (locc_pre hL (eα'.symm.trans eα) (eβ'.symm.trans eβ))
    (eγ'.symm.trans eγ) (eδ'.symm.trans eδ) using 1
  funext X
  rw [hΦ, submatrix_submatrix, submatrix_submatrix]
  rfl

theorem IsLOCCAbs.ofFinite {a b c d : ℕ} {L : Superop (Fin a × Fin b) (Fin c × Fin d)}
    (h : FiniteLOCC L) : IsLOCCAbs L :=
  ⟨a, b, c, d, Equiv.refl _, Equiv.refl _, Equiv.refl _, Equiv.refl _, L, h, fun X => by
    simp only [Equiv.refl_symm, Equiv.coe_refl, Prod.map_id, submatrix_id_id]⟩

theorem IsLOCCAbs.toFinite {a b c d : ℕ} {L : Superop (Fin a × Fin b) (Fin c × Fin d)}
    (h : IsLOCCAbs L) : FiniteLOCC L := by
  have := h.encode (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Prod.map_id, submatrix_id_id] using this

theorem IsLOCCAbs.id : IsLOCCAbs (fun X : Matrix (α × β) (α × β) ℂ => X) := by
  refine ⟨_, _, _, _, Fintype.equivFin α, Fintype.equivFin β, Fintype.equivFin α,
    Fintype.equivFin β, fun X => X, FiniteLOCC.identity _ _, fun X => ?_⟩
  rw [submatrix_submatrix]
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp

theorem IsLOCCAbs.comp {ε ζ : Type} [Fintype ε] [Fintype ζ]
    {Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    {Ψ : Matrix (γ × δ) (γ × δ) ℂ → Matrix (ε × ζ) (ε × ζ) ℂ}
    (hΦ : IsLOCCAbs Φ) (hΨ : IsLOCCAbs Ψ) : IsLOCCAbs (fun X => Ψ (Φ X)) := by
  obtain ⟨a, b, c, d, eα, eβ, eγ, eδ, L, hL, hΦ'⟩ := hΦ
  have h2 := hΨ.encode eγ eδ (Fintype.equivFin ε) (Fintype.equivFin ζ)
  refine ⟨a, b, _, _, eα, eβ, Fintype.equivFin ε, Fintype.equivFin ζ, _, locc_comp hL h2,
    fun X => ?_⟩
  simp only [hΦ', submatrix_submatrix]
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp

/-- Linearity and positivity of abstract LOCC maps. -/
theorem IsLOCCAbs.map_add {Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (h : IsLOCCAbs Φ) (X Y : Matrix (α × β) (α × β) ℂ) : Φ (X + Y) = Φ X + Φ Y := by
  obtain ⟨a, b, c, d, eα, eβ, eγ, eδ, L, hL, hΦ⟩ := h
  rw [hΦ, hΦ, hΦ, submatrix_add', locc_map_add hL, submatrix_add']

theorem IsLOCCAbs.map_smul {Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (h : IsLOCCAbs Φ) (r : ℂ) (X : Matrix (α × β) (α × β) ℂ) : Φ (r • X) = r • Φ X := by
  obtain ⟨a, b, c, d, eα, eβ, eγ, eδ, L, hL, hΦ⟩ := h
  rw [hΦ, hΦ, submatrix_smul', locc_map_smul hL, submatrix_smul']

theorem IsLOCCAbs.map_zero {Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (h : IsLOCCAbs Φ) : Φ 0 = 0 := by
  have := h.map_smul 0 0
  simpa using this

theorem IsLOCCAbs.map_sum {Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (h : IsLOCCAbs Φ) {ι : Type*} (s : Finset ι) (X : ι → Matrix (α × β) (α × β) ℂ) :
    Φ (∑ i ∈ s, X i) = ∑ i ∈ s, Φ (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.map_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, h.map_add, ih]

theorem IsLOCCAbs.posSemidef {Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (h : IsLOCCAbs Φ) (X : Matrix (α × β) (α × β) ℂ) (hX : X.PosSemidef) : (Φ X).PosSemidef := by
  obtain ⟨a, b, c, d, eα, eβ, eγ, eδ, L, hL, hΦ⟩ := h
  rw [hΦ]
  exact (locc_posSemidef hL _ (hX.submatrix _)).submatrix _

theorem IsLOCCAbs.trace {Φ : Matrix (α × β) (α × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (h : IsLOCCAbs Φ) (X : Matrix (α × β) (α × β) ℂ) : (Φ X).trace = X.trace := by
  obtain ⟨a, b, c, d, eα, eβ, eγ, eδ, L, hL, hΦ⟩ := h
  rw [hΦ, show Prod.map ⇑eγ ⇑eδ = ⇑(eγ.prodCongr eδ) from rfl, trace_submatrix_equiv,
    locc_trace hL, show Prod.map ⇑eα.symm ⇑eβ.symm = ⇑(eα.prodCongr eβ).symm from rfl,
    trace_submatrix_equiv]

/-- Re-indexing identity for a local Kraus operator acting on Alice's side. -/
lemma kron_conj_reidx {α' : Type} [Fintype α'] [DecidableEq β] {a b a' : ℕ}
    (K0 : Matrix α' α ℂ) (X : Matrix (α × β) (α × β) ℂ)
    (eα : α ≃ Fin a) (eβ : β ≃ Fin b) (eα' : α' ≃ Fin a') :
    Matrix.kronecker (K0.submatrix eα'.symm eα.symm) (1 : Matrix (Fin b) (Fin b) ℂ) *
        X.submatrix (Prod.map eα.symm eβ.symm) (Prod.map eα.symm eβ.symm) *
        (Matrix.kronecker (K0.submatrix eα'.symm eα.symm) (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ =
      (Matrix.kronecker K0 (1 : Matrix β β ℂ) * X * (Matrix.kronecker K0 (1 : Matrix β β ℂ))ᴴ).submatrix
        (Prod.map eα'.symm eβ.symm) (Prod.map eα'.symm eβ.symm) := by
  have hK : Matrix.kronecker (K0.submatrix eα'.symm eα.symm) (1 : Matrix (Fin b) (Fin b) ℂ) =
      (Matrix.kronecker K0 (1 : Matrix β β ℂ)).submatrix (Prod.map eα'.symm eβ.symm)
        ((eα.prodCongr eβ).symm) := by
    ext ⟨x1, x2⟩ ⟨y1, y2⟩
    simp [Matrix.one_apply, Equiv.prodCongr_symm]
  rw [hK, conjTranspose_submatrix, show Prod.map ⇑eα.symm ⇑eβ.symm = ⇑(eα.prodCongr eβ).symm from rfl,
    submatrix_mul_equiv, submatrix_mul_equiv]

lemma kron_conj_reidx' {β' : Type} [Fintype β'] [DecidableEq α] {a b b' : ℕ}
    (K0 : Matrix β' β ℂ) (X : Matrix (α × β) (α × β) ℂ)
    (eα : α ≃ Fin a) (eβ : β ≃ Fin b) (eβ' : β' ≃ Fin b') :
    Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (K0.submatrix eβ'.symm eβ.symm) *
        X.submatrix (Prod.map eα.symm eβ.symm) (Prod.map eα.symm eβ.symm) *
        (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (K0.submatrix eβ'.symm eβ.symm))ᴴ =
      (Matrix.kronecker (1 : Matrix α α ℂ) K0 * X * (Matrix.kronecker (1 : Matrix α α ℂ) K0)ᴴ).submatrix
        (Prod.map eα.symm eβ'.symm) (Prod.map eα.symm eβ'.symm) := by
  have hK : Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (K0.submatrix eβ'.symm eβ.symm) =
      (Matrix.kronecker (1 : Matrix α α ℂ) K0).submatrix (Prod.map eα.symm eβ'.symm)
        ((eα.prodCongr eβ).symm) := by
    ext ⟨x1, x2⟩ ⟨y1, y2⟩
    simp [Matrix.one_apply, Equiv.prodCongr_symm]
  rw [hK, conjTranspose_submatrix, show Prod.map ⇑eα.symm ⇑eβ.symm = ⇑(eα.prodCongr eβ).symm from rfl,
    submatrix_mul_equiv, submatrix_mul_equiv]

/-- A local instrument of Alice with arbitrary finite outcome set, followed by an
outcome-dependent abstract LOCC continuation, is an abstract LOCC map. -/
theorem IsLOCCAbs.alice {K α' : Type} [Fintype K] [Fintype α'] [DecidableEq α] [DecidableEq α']
    [DecidableEq β] (E : K → Matrix α' α ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1)
    (next : K → Matrix (α' × β) (α' × β) ℂ → Matrix (γ × δ) (γ × δ) ℂ)
    (hnext : ∀ k, IsLOCCAbs (next k)) :
    IsLOCCAbs (fun X : Matrix (α × β) (α × β) ℂ =>
      ∑ k, next k (Matrix.kronecker (E k) (1 : Matrix β β ℂ) * X *
      (Matrix.kronecker (E k) (1 : Matrix β β ℂ))ᴴ)) := by
  classical
  set eα := Fintype.equivFin α
  set eβ := Fintype.equivFin β
  set eα' := Fintype.equivFin α'
  set eγ := Fintype.equivFin γ
  set eδ := Fintype.equivFin δ
  set eK := Fintype.equivFin K
  let E' : Fin (Fintype.card K) → Matrix (Fin (Fintype.card α')) (Fin (Fintype.card α)) ℂ :=
    fun i => (E (eK.symm i)).submatrix eα'.symm eα.symm
  have hE' : IsKrausFamily E' := by
    unfold IsKrausFamily
    have : ∑ i, (E' i)ᴴ * E' i = (∑ k, (E k)ᴴ * E k).submatrix eα.symm eα.symm := by
      rw [submatrix_sum]
      refine (Fintype.sum_equiv eK.symm _ _ fun i => ?_)
      simp only [E', conjTranspose_submatrix]
      rw [submatrix_mul_equiv]
    rw [this, hE, submatrix_one_equiv]
  let N : Fin (Fintype.card K) → Superop (Fin (Fintype.card α') × Fin (Fintype.card β))
      (Fin (Fintype.card γ) × Fin (Fintype.card δ)) :=
    fun i Y => (next (eK.symm i) (Y.submatrix (Prod.map eα' eβ) (Prod.map eα' eβ))).submatrix
      (Prod.map eγ.symm eδ.symm) (Prod.map eγ.symm eδ.symm)
  have hN : ∀ i, FiniteLOCC (N i) := fun i => (hnext (eK.symm i)).encode eα' eβ eγ eδ
  refine ⟨_, _, _, _, eα, eβ, eγ, eδ, _, FiniteLOCC.alice E' hE' N hN, fun X => ?_⟩
  simp only [N, E']
  rw [submatrix_sum]
  refine (Fintype.sum_equiv eK.symm _ _ fun i => ?_).symm
  rw [kron_conj_reidx, submatrix_submatrix, prodMap_symm_comp, submatrix_id_id,
    submatrix_submatrix, prodMap_symm_comp, submatrix_id_id]

theorem IsLOCCAbs.bob {K β' : Type} [Fintype K] [Fintype β'] [DecidableEq α] [DecidableEq β]
    [DecidableEq β'] (E : K → Matrix β' β ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1)
    (next : K → Matrix (α × β') (α × β') ℂ → Matrix (γ × δ) (γ × δ) ℂ)
    (hnext : ∀ k, IsLOCCAbs (next k)) :
    IsLOCCAbs (fun X : Matrix (α × β) (α × β) ℂ =>
      ∑ k, next k (Matrix.kronecker (1 : Matrix α α ℂ) (E k) * X *
      (Matrix.kronecker (1 : Matrix α α ℂ) (E k))ᴴ)) := by
  classical
  set eα := Fintype.equivFin α
  set eβ := Fintype.equivFin β
  set eβ' := Fintype.equivFin β'
  set eγ := Fintype.equivFin γ
  set eδ := Fintype.equivFin δ
  set eK := Fintype.equivFin K
  let E' : Fin (Fintype.card K) → Matrix (Fin (Fintype.card β')) (Fin (Fintype.card β)) ℂ :=
    fun i => (E (eK.symm i)).submatrix eβ'.symm eβ.symm
  have hE' : IsKrausFamily E' := by
    unfold IsKrausFamily
    have : ∑ i, (E' i)ᴴ * E' i = (∑ k, (E k)ᴴ * E k).submatrix eβ.symm eβ.symm := by
      rw [submatrix_sum]
      refine (Fintype.sum_equiv eK.symm _ _ fun i => ?_)
      simp only [E', conjTranspose_submatrix]
      rw [submatrix_mul_equiv]
    rw [this, hE, submatrix_one_equiv]
  let N : Fin (Fintype.card K) → Superop (Fin (Fintype.card α) × Fin (Fintype.card β'))
      (Fin (Fintype.card γ) × Fin (Fintype.card δ)) :=
    fun i Y => (next (eK.symm i) (Y.submatrix (Prod.map eα eβ') (Prod.map eα eβ'))).submatrix
      (Prod.map eγ.symm eδ.symm) (Prod.map eγ.symm eδ.symm)
  have hN : ∀ i, FiniteLOCC (N i) := fun i => (hnext (eK.symm i)).encode eα eβ' eγ eδ
  refine ⟨_, _, _, _, eα, eβ, eγ, eδ, _, FiniteLOCC.bob E' hE' N hN, fun X => ?_⟩
  simp only [N, E']
  rw [submatrix_sum]
  refine (Fintype.sum_equiv eK.symm _ _ fun i => ?_).symm
  rw [kron_conj_reidx', submatrix_submatrix, prodMap_symm_comp, submatrix_id_id,
    submatrix_submatrix, prodMap_symm_comp, submatrix_id_id]

end Abs

end FKR

end FKR_Abs

section FKR_TraceNorm

/-!
# Trace-norm inequalities

`polar`, `re_tr_le`, `tr_cfc_swap` and their helpers are copied from the accepted public
solution of `QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_3` (namespaces `X5B2`, `X5UH`),
as already reused in the accepted solutions of `HorodeckiBoundKey.polar_twist` and
`HorodeckiBoundKey.ppt_undistillable`.
-/

open QAlgorithms
open scoped Matrix ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace FKR

open Matrix
open scoped MatrixOrder

section Polar

variable {R : Type*} [Fintype R] [DecidableEq R]

lemma fin (X : Matrix R R ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma sqrt_herm (X : Matrix R R ℂ) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X :=
  (cfc_predicate Real.sqrt X : IsSelfAdjoint _)

lemma sqrt_sq {X : Matrix R R ℂ} (hX : X.PosSemidef) :
    cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hs : IsSelfAdjoint X := hX.1.isSelfAdjoint
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hs]
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)

lemma dot_self (Y : Matrix R R ℂ) (v : R → ℂ) :
    star (Y *ᵥ v) ⬝ᵥ (Y *ᵥ v) = star v ⬝ᵥ ((Yᴴ * Y) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma norm_sq_eq (x : EuclideanSpace ℂ R) : ((‖x‖ ^ 2 : ℝ) : ℂ) = star (x.ofLp) ⬝ᵥ x.ofLp := by
  rw [Complex.ofReal_pow, show ((‖x‖ : ℂ)) ^ 2 = inner ℂ x x from
    (inner_self_eq_norm_sq_to_K x).symm, PiLp.inner_apply]
  simp [dotProduct, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

/-- Polar decomposition: `Y = W |Y|` with `W` unitary.  (Adapted from the accepted public
solution of `QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_3`, lemma `X5UH.polar`.) -/
theorem polar (Y : Matrix R R ℂ) :
    ∃ W : Matrix.unitaryGroup R ℂ, (W : Matrix R R ℂ) * cfc Real.sqrt (Yᴴ * Y) = Y := by
  set G := Yᴴ * Y
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Y
  set A := cfc Real.sqrt G
  set Ap := cfc (fun x => (Real.sqrt x)⁻¹) G
  set P := cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) G
  have hAh : Aᴴ = A := sqrt_herm G
  have hAA : A * A = G := sqrt_sq hG
  have hApA : Ap * A = P := by
    rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
    exact cfc_congr fun x _ => mul_comm _ _
  have hA1P : A * (1 - P) = 0 := by
    rw [← cfc_one ℝ G, ← cfc_sub _ _ _ (fin _ _) (fin _ _),
      ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
    rw [show (0 : Matrix R R ℂ) = cfc (fun _ : ℝ => (0 : ℝ)) G by simp]
    refine cfc_congr fun x _ => ?_
    by_cases h : Real.sqrt x = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]
  have hY1P : Y * (1 - P) = 0 := by
    have : (Y * (1 - P))ᴴ * (Y * (1 - P)) = 0 := by
      have e : (Y * (1 - P))ᴴ * (Y * (1 - P)) = (A * (1 - P))ᴴ * (A * (1 - P)) := by
        simp only [conjTranspose_mul, hAh]
        rw [show (1 - P)ᴴ * Yᴴ * (Y * (1 - P)) = (1 - P)ᴴ * G * (1 - P) by
            simp only [G, Matrix.mul_assoc],
          ← hAA]
        simp only [Matrix.mul_assoc]
      rw [e, hA1P, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
  set M := Y * Ap
  have hMA : M * A = Y := by
    rw [Matrix.mul_assoc, hApA]
    have := hY1P
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have hnorm : ∀ v : R → ℂ, ‖(WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)‖ =
      ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)‖ := by
    intro v
    have h1 := norm_sq_eq (WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)
    have h2 := norm_sq_eq (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)
    simp only [WithLp.ofLp_toLp] at h1 h2
    rw [dot_self] at h1
    rw [dot_self, hAh, hAA] at h2
    rw [← h2] at h1
    have := Complex.ofReal_injective h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  set TA := Matrix.toEuclideanLin A
  set S := LinearMap.range TA
  let L : S →ₗᵢ[ℂ] EuclideanSpace ℂ R :=
    { toLinearMap := (Matrix.toEuclideanLin M).domRestrict S
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        simp only [LinearMap.domRestrict_apply, TA, Matrix.toEuclideanLin_apply,
          WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hMA, Submodule.coe_norm]
        exact hnorm _ }
  set W := L.extend
  set Wm := Matrix.toEuclideanLin.symm W.toLinearMap
  have hW : ∀ x, Matrix.toEuclideanLin Wm x = W x := by
    intro x; simp [Wm]
  have hWv : ∀ u : R → ℂ, Wm *ᵥ u = (W (WithLp.toLp 2 u)).ofLp := by
    intro u; rw [← hW]; simp
  have hWA : Wm * A = Y := by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    rw [← Matrix.mulVec_mulVec, hWv]
    have hx : (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R) ∈ S :=
      ⟨WithLp.toLp 2 v, by simp [TA]⟩
    have := L.extend_apply ⟨_, hx⟩
    simp only at this
    rw [this]
    simp [L, Matrix.mulVec_mulVec, hMA]
  have hU : Wm ∈ Matrix.unitaryGroup R ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := W.inner_map_map (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j 1)
    have hc : ∀ j : R, (W (EuclideanSpace.single j (1 : ℂ))).ofLp = Wm.col j := by
      intro j; rw [← Matrix.mulVec_single_one, hWv]; rfl
    rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at this
    simp only [hc] at this
    simp only [star_eq_conjTranspose, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply]
    convert this using 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.col_apply, RCLike.inner_apply]
      exact mul_comm _ _
    · simp [EuclideanSpace.single_apply, eq_comm]
  exact ⟨⟨Wm, hU⟩, hWA⟩

end Polar

section TraceIneq
open Matrix Finset Polynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma fin' (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma psd_re {X : Matrix I I ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma cs (X Y : Matrix I I ℂ) :
    (Xᴴ * Y).trace.re + (Yᴴ * X).trace.re ≤ (Xᴴ * X).trace.re + (Yᴴ * Y).trace.re := by
  have h0 := psd_re (Matrix.posSemidef_conjTranspose_mul_self (X - Y))
  simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re] at h0
  linarith

/-- `Re Tr Z ≤ Tr √(Z Z†)` -/
theorem re_tr_le (Z : Matrix I I ℂ) : Z.trace.re ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set M := Z * Zᴴ
  have hM : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Z
  have hMs : IsSelfAdjoint M := hM.1.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ M, 0 ≤ x := fun x hx => spectrum_nonneg_of_nonneg hM.nonneg hx
  have key : ∀ ε : ℝ, 0 < ε → Z.trace.re ≤ (cfc Real.sqrt M).trace.re + ε * Fintype.card I / 2 := by
    intro ε hε
    set L := cfc (fun x => Real.sqrt (Real.sqrt x + ε)) M
    set K := cfc (fun x => (Real.sqrt (Real.sqrt x + ε))⁻¹) M
    have hpos : ∀ x : ℝ, 0 < Real.sqrt (Real.sqrt x + ε) :=
      fun x => Real.sqrt_pos.2 (by positivity)
    have hLK : L * K = 1 := by
      rw [← cfc_mul _ _ _ (fin' _ _) (fin' _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => mul_inv_cancel₀ (hpos x).ne'
    have hKL : K * L = 1 := by
      rw [← cfc_mul _ _ _ (fin' _ _) (fin' _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => inv_mul_cancel₀ (hpos x).ne'
    have hLh : Lᴴ = L := (cfc_predicate _ M : IsSelfAdjoint L)
    have hKh : Kᴴ = K := (cfc_predicate _ M : IsSelfAdjoint K)
    have h := cs L (K * Z)
    have e1 : Lᴴ * (K * Z) = Z := by rw [hLh, ← Matrix.mul_assoc, hLK, Matrix.one_mul]
    have e2 : (K * Z)ᴴ * L = Zᴴ := by
      rw [conjTranspose_mul, hKh, Matrix.mul_assoc, hKL, Matrix.mul_one]
    have e3 : (Lᴴ * L).trace.re = (cfc Real.sqrt M).trace.re + ε * Fintype.card I := by
      have : Lᴴ * L = cfc Real.sqrt M + (ε : ℂ) • 1 := by
        rw [hLh, ← cfc_mul _ _ _ (fin' _ _) (fin' _ _)]
        rw [show (ε : ℂ) • (1 : Matrix I I ℂ) = cfc (fun _ : ℝ => ε) M by
          rw [cfc_const ε M hMs]; simp [Algebra.algebraMap_eq_smul_one]]
        rw [← cfc_add _ _ _ (fin' _ _) (fin' _ _)]
        refine cfc_congr fun x hx => ?_
        exact Real.mul_self_sqrt (by have := Real.sqrt_nonneg x; linarith)
      rw [this, Matrix.trace_add, Complex.add_re, Matrix.trace_smul, Matrix.trace_one]
      simp
    have e4 : ((K * Z)ᴴ * (K * Z)).trace.re ≤ (cfc Real.sqrt M).trace.re := by
      have t1 : ((K * Z)ᴴ * (K * Z)).trace = (K * K * M).trace := by
        rw [conjTranspose_mul, hKh]
        rw [show Zᴴ * K * (K * Z) = Zᴴ * (K * K * Z) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [M, Matrix.mul_assoc]
      have t2 : K * K * M = cfc (fun x => x / (Real.sqrt x + ε)) M := by
        rw [show K * K * M = K * K * cfc (fun x : ℝ => x) M by rw [cfc_id' ℝ M hMs],
          ← cfc_mul _ _ _ (fin' _ _) (fin' _ _), ← cfc_mul _ _ _ (fin' _ _) (fin' _ _)]
        refine cfc_congr fun x hx => ?_
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [← mul_inv, Real.mul_self_sqrt h1.le, div_eq_inv_mul]
      have t3 : (cfc Real.sqrt M - K * K * M).PosSemidef := by
        rw [t2, ← cfc_sub _ _ _ (fin' _ _) (fin' _ _)]
        refine (cfc_nonneg (fun x hx => ?_) :
          0 ≤ cfc (fun x => Real.sqrt x - x / (Real.sqrt x + ε)) M).posSemidef
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [sub_nonneg, div_le_iff₀ h1]
        have := Real.mul_self_sqrt h0
        nlinarith [Real.sqrt_nonneg x]
      have := psd_re t3
      rw [Matrix.trace_sub, Complex.sub_re] at this
      rw [t1]; linarith
    rw [e1, e2, e3, Matrix.trace_conjTranspose] at h
    simp only [RCLike.star_def, Complex.conj_re] at h
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have := key (2 * δ / (Fintype.card I + 1)) (by positivity)
  refine this.trans ?_
  have : 2 * δ / (Fintype.card I + 1) * Fintype.card I / 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma tr_pow_swap (X : Matrix m n ℂ) (k : ℕ) :
    ((Xᴴ * X) ^ (k + 1)).trace = ((X * Xᴴ) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (Xᴴ * X) ^ (k + 1) = Xᴴ * (X * Xᴴ) ^ k * X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

lemma tr_aeval_swap (X : Matrix m n ℂ) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    (aeval (Xᴴ * X) p).trace = (aeval (X * Xᴴ) p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [hp]
  · rw [tr_pow_swap]

theorem tr_cfc_swap (X : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by
  set A := Xᴴ * X
  set B := X * Xᴴ
  have hA : IsSelfAdjoint A := (Matrix.posSemidef_conjTranspose_mul_self X).1.isSelfAdjoint
  have hB : IsSelfAdjoint B := (Matrix.posSemidef_self_mul_conjTranspose X).1.isSelfAdjoint
  have fA : (spectrum ℝ A).Finite := A.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := B.finite_real_spectrum
  set s : Finset ℝ := {0} ∪ fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f B = cfc (fun x => p.eval x) B :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p A hA, cfc_polynomial p B hB]
  refine tr_aeval_swap X p ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [s]), hf]


end TraceIneq

section TraceNorm

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- `Re Tr(V Y) ≤ ‖Y‖₁` for a unitary `V`. -/
lemma re_tr_unitary_mul_le (V Y : Matrix I I ℂ) (hV : Vᴴ * V = 1) :
    (V * Y).trace.re ≤ traceNorm Y := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have := re_tr_le (Y * V)
  rw [Matrix.conjTranspose_mul, show Y * V * (Vᴴ * Yᴴ) = Y * (V * Vᴴ) * Yᴴ by
    simp only [Matrix.mul_assoc], hV', Matrix.mul_one,
    ← tr_cfc_swap Y Real.sqrt Real.sqrt_zero] at this
  rw [Matrix.trace_mul_comm]
  exact this

/-- The trace norm is attained by the polar unitary. -/
lemma traceNorm_eq_polar (Z : Matrix I I ℂ) :
    ∃ V : Matrix I I ℂ, Vᴴ * V = 1 ∧ traceNorm Z = (V * Z).trace.re := by
  obtain ⟨W, hW⟩ := polar Z
  have hu : (W : Matrix I I ℂ)ᴴ * (W : Matrix I I ℂ) = 1 := by
    have := W.2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have hu' : (W : Matrix I I ℂ) * (W : Matrix I I ℂ)ᴴ = 1 := mul_eq_one_comm.mp hu
  have hsq : cfc Real.sqrt (Zᴴ * Z) = (W : Matrix I I ℂ)ᴴ * Z := by
    calc cfc Real.sqrt (Zᴴ * Z) = (W : Matrix I I ℂ)ᴴ * ((W : Matrix I I ℂ) *
          cfc Real.sqrt (Zᴴ * Z)) := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
      _ = (W : Matrix I I ℂ)ᴴ * Z := by rw [hW]
  refine ⟨(W : Matrix I I ℂ)ᴴ, by rw [conjTranspose_conjTranspose]; exact hu', ?_⟩
  unfold traceNorm
  rw [hsq]

theorem traceNorm_add_le (X Y : Matrix I I ℂ) : traceNorm (X + Y) ≤ traceNorm X + traceNorm Y := by
  obtain ⟨V, hV, he⟩ := traceNorm_eq_polar (X + Y)
  rw [he, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (re_tr_unitary_mul_le V X hV) (re_tr_unitary_mul_le V Y hV)

theorem traceNorm_smul_le (c : ℝ) (hc : 0 ≤ c) (X : Matrix I I ℂ) :
    traceNorm ((c : ℂ) • X) ≤ c * traceNorm X := by
  obtain ⟨V, hV, he⟩ := traceNorm_eq_polar ((c : ℂ) • X)
  rw [he, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left (re_tr_unitary_mul_le V X hV) hc

theorem traceNorm_neg (X : Matrix I I ℂ) : traceNorm (-X) = traceNorm X := by
  unfold traceNorm
  rw [conjTranspose_neg, neg_mul_neg]

theorem traceNorm_sub_le (X Y : Matrix I I ℂ) : traceNorm (X - Y) ≤ traceNorm X + traceNorm Y := by
  rw [sub_eq_add_neg]
  exact (traceNorm_add_le X (-Y)).trans (by rw [traceNorm_neg])

lemma cfc_sqrt_mul_self {A : Matrix I I ℂ} (hA : A.PosSemidef) : cfc Real.sqrt (A * A) = A := by
  have hs : IsSelfAdjoint A := hA.1.isSelfAdjoint
  have e : A * A = cfc (fun x : ℝ => x * x) A := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A (fin' _ _) (fin' _ _), cfc_id' ℝ A hs]
  rw [e, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) A]
  conv_rhs => rw [← cfc_id' ℝ A hs]
  exact cfc_congr fun x hx => Real.sqrt_mul_self (spectrum_nonneg_of_nonneg hA.nonneg hx)

theorem traceNorm_density {ρ : Matrix I I ℂ} (hρ : IsDensityMatrix ρ) : traceNorm ρ = 1 := by
  unfold traceNorm
  rw [hρ.1.1, cfc_sqrt_mul_self hρ.1, hρ.2, Complex.one_re]

end TraceNorm

end FKR

end FKR_TraceNorm

section FKR_Tensor

/-!
# Tensor powers, selection of subsystems, and state preparation
-/

open QAlgorithms
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

open Matrix

lemma sum_sum_delta {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) (u0 v0 : n) :
    ∑ u, ∑ v, (if u = u0 then (1 : ℂ) else 0) * Y u v * star (if v = v0 then (1 : ℂ) else 0) =
      Y u0 v0 := by
  rw [Finset.sum_eq_single u0 (fun u _ hu => by simp [hu]) (by simp)]
  rw [Finset.sum_eq_single v0 (fun v _ hv => by simp [hv]) (by simp)]
  simp

lemma conj_apply {m n : Type*} [Fintype n] (K : Matrix m n ℂ) (Y : Matrix n n ℂ) (p q : m) :
    (K * Y * Kᴴ) p q = ∑ u, ∑ v, K p u * Y u v * star (K q v) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Two successive local operations combine into a product operation. -/
lemma kron_two_step {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β']
    (A : Matrix α' α ℂ) (B : Matrix β' β ℂ) (X : Matrix (α × β) (α × β) ℂ) :
    Matrix.kronecker (1 : Matrix α' α' ℂ) B * (Matrix.kronecker A (1 : Matrix β β ℂ) * X *
      (Matrix.kronecker A (1 : Matrix β β ℂ))ᴴ) * (Matrix.kronecker (1 : Matrix α' α' ℂ) B)ᴴ =
    Matrix.kronecker A B * X * (Matrix.kronecker A B)ᴴ := by
  have h : Matrix.kronecker (1 : Matrix α' α' ℂ) B * Matrix.kronecker A (1 : Matrix β β ℂ) =
      Matrix.kronecker A B := by
    simp only [kron_eq, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [← h, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

section TPow

variable {τ : Type} [Fintype τ] [DecidableEq τ]

/-- Tensor product of a family of operators: `(⊗ₜ Kₜ)(x', x) = ∏ₜ Kₜ(x'ₜ, xₜ)`. -/
def tpow {α α' : Type} (K : τ → Matrix α' α ℂ) : Matrix (τ → α') (τ → α) ℂ :=
  fun x' x => ∏ t, K t (x' t) (x t)

lemma tpow_mul {α α' α'' : Type} [Fintype α'] (K : τ → Matrix α'' α' ℂ)
    (M : τ → Matrix α' α ℂ) : tpow K * tpow M = tpow (fun t => K t * M t) := by
  ext x z
  simp only [tpow, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun t b => K t (x t) b * M t b (z t))).symm

lemma tpow_conjTranspose {α α' : Type} (K : τ → Matrix α' α ℂ) :
    (tpow K)ᴴ = tpow (fun t => (K t)ᴴ) := by
  ext x y
  simp [tpow, conjTranspose_apply, star_prod]

lemma tpow_one {α : Type} [DecidableEq α] : tpow (fun _ : τ => (1 : Matrix α α ℂ)) = 1 := by
  ext x y
  simp only [tpow, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨t, ht⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)

lemma tpow_sum {α α' κ : Type} [Fintype κ] (G : κ → Matrix α' α ℂ) :
    ∑ w : τ → κ, tpow (fun t => G (w t)) = tpow (fun _ => ∑ k, G k) := by
  ext x y
  simp only [Matrix.sum_apply, tpow]
  exact (Fintype.prod_sum (fun t k => G k (x t) (y t))).symm

/-- The tensor power of a complete Kraus family is a complete Kraus family. -/
lemma tpow_kraus {α α' κ : Type} [Fintype κ] [Fintype α'] [DecidableEq α]
    (E : κ → Matrix α' α ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    ∑ w : τ → κ, (tpow (fun t => E (w t)))ᴴ * tpow (fun t => E (w t)) = 1 := by
  simp only [tpow_conjTranspose, tpow_mul]
  rw [tpow_sum (fun k => (E k)ᴴ * E k), hE, tpow_one]

lemma tpow_trace {α : Type} [Fintype α] (M : τ → Matrix α α ℂ) :
    (tpow M).trace = ∏ t, (M t).trace := by
  simp only [Matrix.trace, Matrix.diag, tpow]
  exact (Fintype.prod_sum (fun t a => M t a a)).symm

open scoped MatrixOrder in
lemma tpow_posSemidef {α : Type} [Fintype α] [DecidableEq α] (M : τ → Matrix α α ℂ)
    (hM : ∀ t, (M t).PosSemidef) : (tpow M).PosSemidef := by
  choose B hB using fun t => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM t).nonneg
  have : tpow M = (tpow B)ᴴ * tpow B := by
    rw [tpow_conjTranspose, tpow_mul]
    congr 1
    funext t
    rw [hB t, Matrix.star_eq_conjTranspose]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

variable {α β α' β' : Type}

/-- Pairing of two families of local indices. -/
def pairE (α β : Type) : (τ → α) × (τ → β) ≃ (τ → α × β) :=
  (Equiv.arrowProdEquivProdArrow τ (fun _ => α) (fun _ => β)).symm

@[simp] lemma pairE_apply (x : (τ → α) × (τ → β)) (t : τ) : pairE α β x t = (x.1 t, x.2 t) := rfl

/-- Heterogeneous product state `⊗ₜ Mₜ` of bipartite operators, in the grouped layout
(Alice's registers, Bob's registers). -/
def hpow (M : τ → Matrix (α × β) (α × β) ℂ) :
    Matrix ((τ → α) × (τ → β)) ((τ → α) × (τ → β)) ℂ :=
  fun x y => ∏ t, M t (x.1 t, x.2 t) (y.1 t, y.2 t)

lemma hpow_eq (M : τ → Matrix (α × β) (α × β) ℂ) :
    hpow M = (tpow M).submatrix (pairE α β) (pairE α β) := rfl

lemma kron_tpow (KA : τ → Matrix α' α ℂ) (KB : τ → Matrix β' β ℂ) :
    Matrix.kronecker (tpow KA) (tpow KB) =
      (tpow (fun t => Matrix.kronecker (KA t) (KB t))).submatrix (pairE α' β') (pairE α β) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [kron_eq, kronecker_apply, tpow, submatrix_apply, pairE_apply,
    Finset.prod_mul_distrib]

/-- Product local operations act factorwise on a heterogeneous product state. -/
lemma kron_tpow_conj_hpow [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (KA : τ → Matrix α' α ℂ) (KB : τ → Matrix β' β ℂ) (M : τ → Matrix (α × β) (α × β) ℂ) :
    Matrix.kronecker (tpow KA) (tpow KB) * hpow M * (Matrix.kronecker (tpow KA) (tpow KB))ᴴ =
      hpow (fun t => Matrix.kronecker (KA t) (KB t) * M t *
        (Matrix.kronecker (KA t) (KB t))ᴴ) := by
  rw [kron_tpow, hpow_eq, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv,
    tpow_conjTranspose, tpow_mul, tpow_mul, hpow_eq]

lemma hpow_trace [Fintype α] [Fintype β] (M : τ → Matrix (α × β) (α × β) ℂ) :
    (hpow M).trace = ∏ t, (M t).trace := by
  rw [hpow_eq, trace_submatrix_equiv, tpow_trace]

lemma hpow_posSemidef [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : τ → Matrix (α × β) (α × β) ℂ) (hM : ∀ t, (M t).PosSemidef) : (hpow M).PosSemidef := by
  rw [hpow_eq]
  exact (tpow_posSemidef M hM).submatrix _

lemma hpow_smul_const (c : ℂ) (P : Matrix (α × β) (α × β) ℂ) :
    hpow (fun _ : τ => c • P) = (c ^ Fintype.card τ) • hpow (fun _ : τ => P) := by
  ext x y
  simp only [hpow, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

end TPow

section Sel

variable {τ κ : Type} [Fintype τ] [DecidableEq τ] [Fintype κ] [DecidableEq κ]
variable (ι : κ → τ)

/-- The indices outside the range of `ι`. -/
def Cmp : Type := {t : τ // ¬ ∃ k, ι k = t}

instance : Fintype (Cmp ι) := inferInstanceAs (Fintype {t : τ // ¬ ∃ k, ι k = t})

instance : DecidableEq (Cmp ι) := inferInstanceAs (DecidableEq {t : τ // ¬ ∃ k, ι k = t})

/-- Splitting a configuration into its `ι`-part and the rest. -/
def selFun {γ : Type} (x : τ → γ) : (κ → γ) × (Cmp ι → γ) := (fun k => x (ι k), fun c => x c.1)

variable {ι}

lemma selFun_bij {γ : Type} [Inhabited γ] (hι : Function.Injective ι) :
    Function.Bijective (selFun ι (γ := γ)) := by
  classical
  constructor
  · intro x x' h
    simp only [selFun, Prod.mk.injEq] at h
    funext t
    by_cases ht : ∃ k, ι k = t
    · obtain ⟨k, rfl⟩ := ht
      exact congrFun h.1 k
    · exact congrFun h.2 ⟨t, ht⟩
  · rintro ⟨y, z⟩
    refine ⟨fun t => if ht : ∃ k, ι k = t then y ht.choose else z ⟨t, ht⟩, ?_⟩
    simp only [selFun, Prod.mk.injEq]
    constructor
    · funext k
      have hk : ∃ k', ι k' = ι k := ⟨k, rfl⟩
      rw [dif_pos hk]
      congr 1
      exact hι hk.choose_spec
    · funext c
      rw [dif_neg c.2]
      rfl

/-- The splitting as an equivalence. -/
noncomputable def selEquiv {γ : Type} [Inhabited γ] (hι : Function.Injective ι) :
    (τ → γ) ≃ (κ → γ) × (Cmp ι → γ) :=
  Equiv.ofBijective _ (selFun_bij hι)

lemma selEquiv_apply {γ : Type} [Inhabited γ] (hι : Function.Injective ι) (x : τ → γ) :
    selEquiv hι x = selFun ι x := rfl

lemma selEquiv_symm_ι {γ : Type} [Inhabited γ] (hι : Function.Injective ι)
    (y : κ → γ) (z : Cmp ι → γ) (k : κ) : (selEquiv hι).symm (y, z) (ι k) = y k := by
  have := (selEquiv hι).apply_symm_apply (y, z)
  rw [selEquiv_apply] at this
  exact congrFun (congrArg Prod.fst this) k

lemma selEquiv_symm_c {γ : Type} [Inhabited γ] (hι : Function.Injective ι)
    (y : κ → γ) (z : Cmp ι → γ) (c : Cmp ι) : (selEquiv hι).symm (y, z) c.1 = z c := by
  have := (selEquiv hι).apply_symm_apply (y, z)
  rw [selEquiv_apply] at this
  exact congrFun (congrArg Prod.snd this) c

variable (ι)

/-- Kraus operators of the channel that keeps the `ι`-registers and discards the rest. -/
def selK {γ : Type} [DecidableEq γ] (z : Cmp ι → γ) : Matrix (κ → γ) (τ → γ) ℂ :=
  fun y x => if selFun ι x = (y, z) then 1 else 0

variable {ι}

lemma selK_apply {γ : Type} [DecidableEq γ] [Inhabited γ] (hι : Function.Injective ι)
    (z : Cmp ι → γ) (y : κ → γ) (x : τ → γ) :
    selK ι z y x = if x = (selEquiv hι).symm (y, z) then 1 else 0 := by
  unfold selK
  congr 1
  rw [← selEquiv_apply hι, ← Equiv.eq_symm_apply]

lemma selK_kraus {γ : Type} [Fintype γ] [DecidableEq γ] [Inhabited γ]
    (hι : Function.Injective ι) : ∑ z : Cmp ι → γ, (selK ι z)ᴴ * selK ι z = 1 := by
  ext x1 x2
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, selK, Matrix.one_apply]
  rw [Finset.sum_comm]
  have e : ∀ (y : κ → γ) (z : Cmp ι → γ), star (if selFun ι x1 = (y, z) then (1 : ℂ) else 0) *
      (if selFun ι x2 = (y, z) then (1 : ℂ) else 0) =
      if selFun ι x1 = (y, z) then (if selFun ι x2 = selFun ι x1 then 1 else 0) else 0 := by
    intro y z
    by_cases h1 : selFun ι x1 = (y, z)
    · rw [if_pos h1, if_pos h1, star_one, one_mul, h1]
    · rw [if_neg h1, if_neg h1, star_zero, zero_mul]
  simp only [e]
  rw [← Fintype.sum_prod_type' (fun y z => if selFun ι x1 = (y, z) then
    (if selFun ι x2 = selFun ι x1 then (1 : ℂ) else 0) else 0)]
  simp only [Prod.mk.eta]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases h : x1 = x2
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h ((selFun_bij hι).1 h'.symm))]

/-- Splitting a product over `τ` into the `ι`-part and the rest. -/
lemma prod_split (hι : Function.Injective ι) (f : τ → ℂ) :
    ∏ t, f t = (∏ k, f (ι k)) * ∏ c : Cmp ι, f c.1 := by
  classical
  let e2 : κ ⊕ Cmp ι ≃ τ := Equiv.ofBijective (Sum.elim ι (fun c => c.1)) (by
    constructor
    · rintro (k | c) (k' | c') h
      · exact congrArg Sum.inl (hι h)
      · exact absurd ⟨k, h⟩ c'.2
      · exact absurd ⟨k', h.symm⟩ c.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro t
      by_cases ht : ∃ k, ι k = t
      · obtain ⟨k, hk⟩ := ht
        exact ⟨Sum.inl k, hk⟩
      · exact ⟨Sum.inr ⟨t, ht⟩, rfl⟩)
  rw [← Fintype.prod_equiv e2 (fun s => f (e2 s)) f (fun s => rfl), Fintype.prod_sum_type]
  rfl

/-- The selection channel applied to a heterogeneous product state keeps the selected factors and
multiplies by the traces of the discarded ones. -/
theorem sel_output {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Inhabited α] [Inhabited β] (hι : Function.Injective ι)
    (M : τ → Matrix (α × β) (α × β) ℂ) :
    ∑ zA : Cmp ι → α, ∑ zB : Cmp ι → β, Matrix.kronecker (selK ι zA) (selK ι zB) * hpow M *
        (Matrix.kronecker (selK ι zA) (selK ι zB))ᴴ =
      (∏ c : Cmp ι, (M c.1).trace) • hpow (fun k => M (ι k)) := by
  ext ⟨yA, yB⟩ ⟨yA', yB'⟩
  simp only [Matrix.sum_apply, conj_apply, Matrix.smul_apply, smul_eq_mul]
  have hK : ∀ (zA : Cmp ι → α) (zB : Cmp ι → β) (y : (κ → α) × (κ → β))
      (u : (τ → α) × (τ → β)), Matrix.kronecker (selK ι zA) (selK ι zB) y u =
      if u = ((selEquiv hι).symm (y.1, zA), (selEquiv hι).symm (y.2, zB)) then 1 else 0 := by
    intro zA zB y u
    obtain ⟨y1, y2⟩ := y
    obtain ⟨u1, u2⟩ := u
    simp only [kron_eq, kronecker_apply, selK_apply hι, Prod.mk.injEq]
    by_cases h1 : u1 = (selEquiv hι).symm (y1, zA) <;>
      by_cases h2 : u2 = (selEquiv hι).symm (y2, zB) <;> simp [h1, h2]
  have step : ∀ (zA : Cmp ι → α) (zB : Cmp ι → β),
      ∑ u, ∑ v, Matrix.kronecker (selK ι zA) (selK ι zB) (yA, yB) u * hpow M u v *
        star (Matrix.kronecker (selK ι zA) (selK ι zB) (yA', yB') v) =
      hpow M ((selEquiv hι).symm (yA, zA), (selEquiv hι).symm (yB, zB))
        ((selEquiv hι).symm (yA', zA), (selEquiv hι).symm (yB', zB)) := by
    intro zA zB
    simp only [hK]
    exact sum_sum_delta _ _ _
  simp only [step]
  have split : ∀ (zA : Cmp ι → α) (zB : Cmp ι → β),
      hpow M ((selEquiv hι).symm (yA, zA), (selEquiv hι).symm (yB, zB))
        ((selEquiv hι).symm (yA', zA), (selEquiv hι).symm (yB', zB)) =
      (∏ k, M (ι k) (yA k, yB k) (yA' k, yB' k)) *
        ∏ c : Cmp ι, M c.1 (zA c, zB c) (zA c, zB c) := by
    intro zA zB
    unfold hpow
    rw [prod_split hι]
    simp only [selEquiv_symm_ι, selEquiv_symm_c]
  simp only [split, ← Finset.mul_sum]
  have htr : ∑ zA : Cmp ι → α, ∑ zB : Cmp ι → β, ∏ c : Cmp ι, M c.1 (zA c, zB c) (zA c, zB c) =
      ∏ c : Cmp ι, (M c.1).trace := by
    have e1 : ∀ zA : Cmp ι → α, ∑ zB : Cmp ι → β, ∏ c : Cmp ι, M c.1 (zA c, zB c) (zA c, zB c) =
        ∏ c : Cmp ι, ∑ b : β, M c.1 (zA c, b) (zA c, b) := fun zA =>
      (Fintype.prod_sum (fun (c : Cmp ι) (b : β) => M c.1 (zA c, b) (zA c, b))).symm
    simp only [e1]
    rw [← Fintype.prod_sum (fun (c : Cmp ι) (a : α) => ∑ b : β, M c.1 (a, b) (a, b))]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [Matrix.trace, Matrix.diag]
    exact (Fintype.sum_prod_type' (fun a b => M c.1 (a, b) (a, b))).symm
  rw [htr, mul_comm]
  rfl

end Sel

section Prep

variable {α γ : Type} [DecidableEq α] [DecidableEq γ]

/-- Kraus operators of the channel that discards a register and prepares `g₀`. -/
def prepK (g0 : γ) (x : α) : Matrix γ α ℂ := fun g x' => if g = g0 ∧ x' = x then 1 else 0

lemma prepK_kraus [Fintype α] [Fintype γ] (g0 : γ) : ∑ x : α, (prepK g0 x)ᴴ * prepK g0 x = 1 := by
  ext x1 x2
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, prepK, Matrix.one_apply]
  have e : ∀ (x : α) (g : γ), star (if g = g0 ∧ x1 = x then (1 : ℂ) else 0) *
      (if g = g0 ∧ x2 = x then (1 : ℂ) else 0) =
      if g = g0 then (if x1 = x then (if x2 = x then 1 else 0) else 0) else 0 := by
    intro x g
    by_cases hg : g = g0 <;> by_cases h1 : x1 = x <;> by_cases h2 : x2 = x <;> simp [hg, h1, h2]
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases h : x1 = x2
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

/-- The prepared product basis state `|g₀ h₀⟩⟨g₀ h₀|`. -/
def prepState {δ : Type} [DecidableEq δ] (g0 : γ) (h0 : δ) : Matrix (γ × δ) (γ × δ) ℂ :=
  fun p q => if p = (g0, h0) ∧ q = (g0, h0) then 1 else 0

lemma prepState_density {δ : Type} [Fintype γ] [Fintype δ] [DecidableEq δ] (g0 : γ) (h0 : δ) :
    IsDensityMatrix (prepState g0 h0) := by
  let v : Matrix Unit (γ × δ) ℂ := Matrix.of fun _ q => if q = (g0, h0) then (1 : ℂ) else 0
  have e : prepState g0 h0 = vᴴ * v := by
    ext p q
    simp only [prepState, v, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
      Finset.univ_unique, Finset.sum_singleton]
    by_cases hp : p = (g0, h0) <;> by_cases hq : q = (g0, h0) <;> simp [hp, hq]
  refine ⟨?_, ?_⟩
  · rw [e]; exact Matrix.posSemidef_conjTranspose_mul_self _
  · simp only [Matrix.trace, Matrix.diag, prepState, and_self]
    rw [Finset.sum_ite_eq']
    simp

theorem prep_output {β δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq β] [DecidableEq δ] (g0 : γ) (h0 : δ) (Y : Matrix (α × β) (α × β) ℂ) :
    ∑ x : α, ∑ y : β, Matrix.kronecker (prepK g0 x) (prepK h0 y) * Y *
        (Matrix.kronecker (prepK g0 x) (prepK h0 y))ᴴ = Y.trace • prepState g0 h0 := by
  ext ⟨g, h⟩ ⟨g', h'⟩
  simp only [Matrix.sum_apply, conj_apply, Matrix.smul_apply, smul_eq_mul]
  have hK : ∀ (x : α) (y : β) (p : γ × δ) (u : α × β),
      Matrix.kronecker (prepK g0 x) (prepK h0 y) p u =
      if p = (g0, h0) then (if u = (x, y) then 1 else 0) else 0 := by
    intro x y p u
    obtain ⟨p1, p2⟩ := p
    obtain ⟨u1, u2⟩ := u
    simp only [kron_eq, kronecker_apply, prepK, Prod.mk.injEq]
    by_cases a1 : p1 = g0 <;> by_cases a2 : p2 = h0 <;> by_cases a3 : u1 = x <;>
      by_cases a4 : u2 = y <;> simp [a1, a2, a3, a4]
  simp only [hK]
  by_cases hp : (g, h) = (g0, h0)
  · by_cases hq : (g', h') = (g0, h0)
    · simp only [hp, hq, if_true]
      simp only [sum_sum_delta]
      simp only [prepState, hp, hq, and_self, if_true, mul_one]
      simp only [Matrix.trace, Matrix.diag]
      exact (Fintype.sum_prod_type' (fun x y => Y (x, y) (x, y))).symm
    · simp [hq, prepState]
  · simp [hp, prepState]

end Prep

end FKR

end FKR_Tensor

section FKR_Cheb

/-!
# Chebyshev bound for the number of successes in independent trials
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

section Cheb

variable {γ : Type} [Fintype γ] {m : ℕ}

lemma sum_prod_mul_prod (μ : γ → ℝ) (h : Fin m → γ → ℝ) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * ∏ t, h t (w t) = ∏ t, ∑ x, μ x * h t x := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib]

lemma sum_prod_one (μ : γ → ℝ) (hμ1 : ∑ g, μ g = 1) :
    ∑ w : Fin m → γ, ∏ t, μ (w t) = 1 := by
  have := sum_prod_mul_prod (m := m) μ (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [this, hμ1, Finset.prod_const_one]

variable (μ : γ → ℝ) (ind : γ → ℝ)

lemma sum_prod_ind (hμ1 : ∑ g, μ g = 1) (t0 : Fin m) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * ind (w t0) = ∑ x, μ x * ind x := by
  have := sum_prod_mul_prod μ (fun t x => if t = t0 then ind x else 1)
  have e : ∀ w : Fin m → γ, ∏ t, (if t = t0 then ind (w t) else 1) = ind (w t0) := by
    intro w
    rw [Finset.prod_ite_eq']
    simp
  simp only [e] at this
  rw [this]
  have e2 : ∀ t : Fin m, ∑ x, μ x * (if t = t0 then ind x else 1) =
      if t = t0 then ∑ x, μ x * ind x else 1 := by
    intro t
    by_cases ht : t = t0
    · simp [ht]
    · simp [ht, hμ1]
  simp only [e2]
  rw [Finset.prod_ite_eq']
  simp

lemma sum_prod_ind2 (hμ1 : ∑ g, μ g = 1) (hind : ∀ x, ind x * ind x = ind x) (t1 t2 : Fin m) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * (ind (w t1) * ind (w t2)) =
      if t1 = t2 then ∑ x, μ x * ind x else (∑ x, μ x * ind x) ^ 2 := by
  have := sum_prod_mul_prod μ (fun t x => (if t = t1 then ind x else 1) * (if t = t2 then ind x else 1))
  have e : ∀ w : Fin m → γ,
      ∏ t, ((if t = t1 then ind (w t) else 1) * (if t = t2 then ind (w t) else 1)) =
        ind (w t1) * ind (w t2) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
  simp only [e] at this
  rw [this]
  set q := ∑ x, μ x * ind x
  by_cases h12 : t1 = t2
  · subst h12
    rw [if_pos rfl]
    have e2 : ∀ t : Fin m, ∑ x, μ x * ((if t = t1 then ind x else 1) * (if t = t1 then ind x else 1))
        = if t = t1 then q else 1 := by
      intro t
      by_cases ht : t = t1
      · simp only [ht, if_true, hind]; rfl
      · simp [ht, hμ1]
    simp only [e2]
    rw [Finset.prod_ite_eq']
    simp
  · rw [if_neg h12]
    have e2 : ∀ t : Fin m, ∑ x, μ x * ((if t = t1 then ind x else 1) * (if t = t2 then ind x else 1))
        = (if t = t1 then q else 1) * (if t = t2 then q else 1) := by
      intro t
      by_cases ht1 : t = t1 <;> by_cases ht2 : t = t2
      · exact absurd (ht1.symm.trans ht2) h12
      · subst ht1; simp [h12, q]
      · subst ht2; simp [Ne.symm h12, q]
      · simp [ht1, ht2, hμ1]
    simp only [e2]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp [sq]

/-- Variance of the number of successes. -/
lemma variance_count (hμ1 : ∑ g, μ g = 1) (hind : ∀ x, ind x * ind x = ind x) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t) - m * ∑ x, μ x * ind x) ^ 2 =
      m * (∑ x, μ x * ind x) * (1 - ∑ x, μ x * ind x) := by
  obtain ⟨q, hq⟩ : ∃ q, q = ∑ x, μ x * ind x := ⟨_, rfl⟩
  rw [← hq]
  have hS0 : ∑ w : Fin m → γ, ∏ t, μ (w t) = 1 := sum_prod_one μ hμ1
  have hS2 : ∑ w : Fin m → γ, (∏ t, μ (w t)) * ∑ t, ind (w t) = m * q := by
    have e : ∀ w : Fin m → γ, (∏ t, μ (w t)) * ∑ t, ind (w t) =
        ∑ t, (∏ t, μ (w t)) * ind (w t) := fun w => Finset.mul_sum _ _ _
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ t0 : Fin m, ∑ w : Fin m → γ, (∏ t, μ (w t)) * ind (w t0) = q := by
      intro t0; rw [sum_prod_ind μ ind hμ1 t0, hq]
    simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hS1 : ∑ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t)) ^ 2 =
      m * q + (m * m - m) * q ^ 2 := by
    have e : ∀ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t)) ^ 2 =
        ∑ t1, ∑ t2, (∏ t, μ (w t)) * (ind (w t1) * ind (w t2)) := by
      intro w
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t1 _ => Finset.mul_sum _ _ _
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ t1 : Fin m, ∑ w : Fin m → γ, ∑ t2, (∏ t, μ (w t)) * (ind (w t1) * ind (w t2)) =
        ∑ t2 : Fin m, (if t1 = t2 then q else q ^ 2) := by
      intro t1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t2 _ => ?_
      rw [sum_prod_ind2 μ ind hμ1 hind t1 t2, hq]
    simp only [e2]
    have e3 : ∀ t1 : Fin m, ∑ t2 : Fin m, (if t1 = t2 then q else q ^ 2) = q + (m - 1) * q ^ 2 := by
      intro t1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ t1), if_pos rfl]
      rw [Finset.sum_congr rfl fun t2 ht2 => if_neg (Ne.symm (Finset.ne_of_mem_erase ht2))]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · exact absurd t1.isLt (by omega)
      · rw [Nat.cast_sub hm]; push_cast; ring
    simp only [e3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  calc ∑ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t) - m * q) ^ 2
      = ∑ w : Fin m → γ, ((∏ t, μ (w t)) * (∑ t, ind (w t)) ^ 2 -
          2 * (m * q) * ((∏ t, μ (w t)) * ∑ t, ind (w t)) + (m * q) ^ 2 * ∏ t, μ (w t)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        ring
    _ = (∑ w : Fin m → γ, (∏ t, μ (w t)) * (∑ t, ind (w t)) ^ 2) -
          2 * (m * q) * (∑ w : Fin m → γ, (∏ t, μ (w t)) * ∑ t, ind (w t)) +
          (m * q) ^ 2 * ∑ w : Fin m → γ, ∏ t, μ (w t) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = m * q * (1 - q) := by
        rw [hS1, hS2, hS0]
        ring

/-- **Chebyshev bound** for the lower tail of the number of successes. -/
theorem count_lower_tail (hμ0 : ∀ g, 0 ≤ μ g) (hμ1 : ∑ g, μ g = 1)
    (hind : ∀ x, ind x * ind x = ind x) (k : ℝ) (hk : k < m * ∑ x, μ x * ind x) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * (if ∑ t, ind (w t) < k then 1 else 0) ≤
      m * (∑ x, μ x * ind x) * (1 - ∑ x, μ x * ind x) / (m * (∑ x, μ x * ind x) - k) ^ 2 := by
  set q := ∑ x, μ x * ind x with hq
  have hpos : 0 < m * q - k := by linarith
  rw [← variance_count μ ind hμ1 hind, Finset.sum_div]
  refine Finset.sum_le_sum fun w _ => ?_
  have hP : 0 ≤ ∏ t, μ (w t) := Finset.prod_nonneg fun t _ => hμ0 _
  split_ifs with h
  · rw [mul_one, mul_div_assoc]
    refine le_mul_of_one_le_right hP ?_
    rw [one_le_div (by positivity)]
    nlinarith
  · rw [mul_zero]
    positivity

end Cheb

end FKR

end FKR_Cheb

section FKR_Proto

/-!
# The block-filtering protocol and its output
-/

open QAlgorithms
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

open Matrix

section Kfam

/-- The local filter instrument: outcome `none` applies the filter `F`; outcome `some j`
(failure) applies `|e₀⟩⟨j| G`, where `G†G = 𝟙 − F†F`. -/
def kfam {α α' : Type} [DecidableEq α'] (F : Matrix α' α ℂ) (G : Matrix α α ℂ) (e0 : α') :
    Option α → Matrix α' α ℂ
  | none => F
  | some j => fun x'' x => if x'' = e0 then G j x else 0

@[simp] lemma kfam_none {α α' : Type} [DecidableEq α'] (F : Matrix α' α ℂ) (G : Matrix α α ℂ)
    (e0 : α') : kfam F G e0 none = F := rfl

lemma kfam_some {α α' : Type} [DecidableEq α'] (F : Matrix α' α ℂ) (G : Matrix α α ℂ)
    (e0 : α') (j : α) (x'' : α') (x : α) :
    kfam F G e0 (some j) x'' x = if x'' = e0 then G j x else 0 := rfl

lemma kfam_kraus {α α' : Type} [Fintype α] [Fintype α'] [DecidableEq α] [DecidableEq α']
    (F : Matrix α' α ℂ) (G : Matrix α α ℂ) (e0 : α') (hG : Gᴴ * G = 1 - Fᴴ * F) :
    ∑ o, (kfam F G e0 o)ᴴ * kfam F G e0 o = 1 := by
  rw [Fintype.sum_option]
  have : ∑ j : α, (kfam F G e0 (some j))ᴴ * kfam F G e0 (some j) = Gᴴ * G := by
    ext x y
    simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, kfam_some]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single e0 (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [this, hG, kfam_none]
  simp

end Kfam

section Sel'

/-- Every set of at least `k` indices contains the range of an injection of `Fin k`. -/
lemma exists_sel {m k : ℕ} (S : Finset (Fin m)) (h : k ≤ S.card) :
    ∃ ι : Fin k → Fin m, Function.Injective ι ∧ ∀ i, ι i ∈ S := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq h
  exact ⟨fun i => T.orderEmbOfFin hT i, (T.orderEmbOfFin hT).injective,
    fun i => hTS (T.orderEmbOfFin_mem hT i)⟩

end Sel'

section Proto

variable {A B A' B' : ℕ} {γ δ : Type} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]
variable (FA : Matrix (Fin A') (Fin A) ℂ) (GA : Matrix (Fin A) (Fin A) ℂ) (eA : Fin A')
  (FB : Matrix (Fin B') (Fin B) ℂ) (GB : Matrix (Fin B) (Fin B) ℂ) (eB : Fin B')

/-- The set of rounds in which both filters succeeded. -/
def succ {m : ℕ} (wA : Fin m → Option (Fin A)) (wB : Fin m → Option (Fin B)) : Finset (Fin m) :=
  Finset.univ.filter (fun t => wA t = none ∧ wB t = none)

/-- Good branch: keep the registers `ι`, discard the rest, then run `Lk`. -/
noncomputable def goodMap {m k : ℕ} (ι : Fin k → Fin m)
    (Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ) :
    Matrix ((Fin m → Fin A') × (Fin m → Fin B')) ((Fin m → Fin A') × (Fin m → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ :=
  fun X => ∑ zA : Cmp ι → Fin A',
    (fun Y => ∑ zB : Cmp ι → Fin B',
      Lk (Matrix.kronecker (1 : Matrix (Fin k → Fin A') (Fin k → Fin A') ℂ) (selK ι zB) * Y *
        (Matrix.kronecker (1 : Matrix (Fin k → Fin A') (Fin k → Fin A') ℂ) (selK ι zB))ᴴ))
    (Matrix.kronecker (selK ι zA) (1 : Matrix (Fin m → Fin B') (Fin m → Fin B') ℂ) * X *
      (Matrix.kronecker (selK ι zA) (1 : Matrix (Fin m → Fin B') (Fin m → Fin B') ℂ))ᴴ)

/-- Bad branch: discard everything and prepare `g₀ h₀`. -/
noncomputable def badMap {m : ℕ} (g0 : γ) (h0 : δ) :
    Matrix ((Fin m → Fin A') × (Fin m → Fin B')) ((Fin m → Fin A') × (Fin m → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ :=
  fun X => ∑ x : Fin m → Fin A',
    (fun Y => ∑ y : Fin m → Fin B', (fun Z : Matrix (γ × δ) (γ × δ) ℂ => Z)
      (Matrix.kronecker (1 : Matrix γ γ ℂ) (prepK h0 y) * Y *
        (Matrix.kronecker (1 : Matrix γ γ ℂ) (prepK h0 y))ᴴ))
    (Matrix.kronecker (prepK g0 x) (1 : Matrix (Fin m → Fin B') (Fin m → Fin B') ℂ) * X *
      (Matrix.kronecker (prepK g0 x) (1 : Matrix (Fin m → Fin B') (Fin m → Fin B') ℂ))ᴴ)

/-- The continuation after the filtering round. -/
noncomputable def contMap {m k : ℕ}
    (Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ) (g0 : γ) (h0 : δ)
    (wA : Fin m → Option (Fin A)) (wB : Fin m → Option (Fin B)) :
    Matrix ((Fin m → Fin A') × (Fin m → Fin B')) ((Fin m → Fin A') × (Fin m → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ :=
  if h : k ≤ (succ wA wB).card then goodMap (A' := A') (B' := B') (Classical.choose (exists_sel _ h)) Lk
  else badMap (A' := A') (B' := B') g0 h0

/-- The whole protocol on `m` copies. -/
noncomputable def proto {m k : ℕ}
    (Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ) (g0 : γ) (h0 : δ) :
    Matrix ((Fin m → Fin A) × (Fin m → Fin B)) ((Fin m → Fin A) × (Fin m → Fin B)) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ :=
  fun X => ∑ wA : Fin m → Option (Fin A),
    (fun Y => ∑ wB : Fin m → Option (Fin B), contMap (A := A) (B := B) Lk g0 h0 wA wB
      (Matrix.kronecker (1 : Matrix (Fin m → Fin A') (Fin m → Fin A') ℂ)
          (tpow (fun t => kfam FB GB eB (wB t))) * Y *
        (Matrix.kronecker (1 : Matrix (Fin m → Fin A') (Fin m → Fin A') ℂ)
          (tpow (fun t => kfam FB GB eB (wB t))))ᴴ))
    (Matrix.kronecker (tpow (fun t => kfam FA GA eA (wA t)))
        (1 : Matrix (Fin m → Fin B) (Fin m → Fin B) ℂ) * X *
      (Matrix.kronecker (tpow (fun t => kfam FA GA eA (wA t)))
        (1 : Matrix (Fin m → Fin B) (Fin m → Fin B) ℂ))ᴴ)

theorem goodMap_locc {m k : ℕ} (ι : Fin k → Fin m) (hι : Function.Injective ι)
    {Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ} (hLk : IsLOCCAbs Lk) [Inhabited (Fin A')] [Inhabited (Fin B')] :
    IsLOCCAbs (goodMap (A' := A') (B' := B') ι Lk) :=
  IsLOCCAbs.alice (fun zA => selK ι zA) (selK_kraus hι) _ fun zA =>
    IsLOCCAbs.bob (fun zB => selK ι zB) (selK_kraus hι) (fun _ => Lk) fun zB => hLk

theorem badMap_locc {m : ℕ} (g0 : γ) (h0 : δ) :
    IsLOCCAbs (badMap (m := m) (A' := A') (B' := B') g0 h0) :=
  IsLOCCAbs.alice (fun x => prepK g0 x) (prepK_kraus g0) _ fun x =>
    IsLOCCAbs.bob (fun y => prepK h0 y) (prepK_kraus h0) (fun _ Z => Z) fun y => IsLOCCAbs.id

theorem contMap_locc {m k : ℕ}
    {Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ} (hLk : IsLOCCAbs Lk) (g0 : γ) (h0 : δ)
    (wA : Fin m → Option (Fin A)) (wB : Fin m → Option (Fin B)) [Inhabited (Fin A')]
    [Inhabited (Fin B')] : IsLOCCAbs (contMap (A := A) (B := B) Lk g0 h0 wA wB) := by
  unfold contMap
  split_ifs with h
  · exact goodMap_locc _ (Classical.choose_spec (exists_sel _ h)).1 hLk
  · exact badMap_locc g0 h0

theorem proto_locc {m k : ℕ}
    {Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ} (hLk : IsLOCCAbs Lk) (g0 : γ) (h0 : δ)
    (hGA : GAᴴ * GA = 1 - FAᴴ * FA) (hGB : GBᴴ * GB = 1 - FBᴴ * FB)
    [Inhabited (Fin A')] [Inhabited (Fin B')] :
    IsLOCCAbs (proto (m := m) FA GA eA FB GB eB Lk g0 h0) :=
  IsLOCCAbs.alice _ (tpow_kraus _ (kfam_kraus FA GA eA hGA)) _ fun wA =>
    IsLOCCAbs.bob _ (tpow_kraus _ (kfam_kraus FB GB eB hGB)) _ fun wB =>
      contMap_locc hLk g0 h0 wA wB

/-- The post-measurement factor of round `t`. -/
def Mw {m : ℕ} (ω : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (wA : Fin m → Option (Fin A))
    (wB : Fin m → Option (Fin B)) (t : Fin m) : Matrix (Fin A' × Fin B') (Fin A' × Fin B') ℂ :=
  Matrix.kronecker (kfam FA GA eA (wA t)) (kfam FB GB eB (wB t)) * ω *
    (Matrix.kronecker (kfam FA GA eA (wA t)) (kfam FB GB eB (wB t)))ᴴ

theorem proto_apply {m k : ℕ}
    (Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ) (g0 : γ) (h0 : δ) (ω : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) :
    proto (m := m) FA GA eA FB GB eB Lk g0 h0 (hpow (fun _ => ω)) =
      ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
        contMap (A := A) (B := B) Lk g0 h0 wA wB (hpow (Mw FA GA eA FB GB eB ω wA wB)) := by
  unfold proto
  refine Finset.sum_congr rfl fun wA _ => Finset.sum_congr rfl fun wB _ => ?_
  rw [kron_two_step, kron_tpow_conj_hpow]
  rfl

theorem goodMap_apply {m k : ℕ} (ι : Fin k → Fin m) (hι : Function.Injective ι)
    {Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ} (hLk : IsLOCCAbs Lk) [Inhabited (Fin A')] [Inhabited (Fin B')]
    (M : Fin m → Matrix (Fin A' × Fin B') (Fin A' × Fin B') ℂ) :
    goodMap (A' := A') (B' := B') ι Lk (hpow M) =
      (∏ c : Cmp ι, (M c.1).trace) • Lk (hpow (fun i => M (ι i))) := by
  unfold goodMap
  have e : ∀ (zA : Cmp ι → Fin A') (zB : Cmp ι → Fin B'),
      Matrix.kronecker (1 : Matrix (Fin k → Fin A') (Fin k → Fin A') ℂ) (selK ι zB) *
        (Matrix.kronecker (selK ι zA) (1 : Matrix (Fin m → Fin B') (Fin m → Fin B') ℂ) * hpow M *
          (Matrix.kronecker (selK ι zA) (1 : Matrix (Fin m → Fin B') (Fin m → Fin B') ℂ))ᴴ) *
        (Matrix.kronecker (1 : Matrix (Fin k → Fin A') (Fin k → Fin A') ℂ) (selK ι zB))ᴴ =
      Matrix.kronecker (selK ι zA) (selK ι zB) * hpow M *
        (Matrix.kronecker (selK ι zA) (selK ι zB))ᴴ := fun zA zB => kron_two_step _ _ _
  simp only [e]
  simp only [← hLk.map_sum]
  rw [sel_output hι M, hLk.map_smul]

theorem badMap_apply {m : ℕ} (g0 : γ) (h0 : δ)
    (Y : Matrix ((Fin m → Fin A') × (Fin m → Fin B')) ((Fin m → Fin A') × (Fin m → Fin B')) ℂ) :
    badMap (A' := A') (B' := B') g0 h0 Y = Y.trace • prepState g0 h0 := by
  unfold badMap
  have e : ∀ (x : Fin m → Fin A') (y : Fin m → Fin B'),
      Matrix.kronecker (1 : Matrix γ γ ℂ) (prepK h0 y) *
        (Matrix.kronecker (prepK g0 x) (1 : Matrix (Fin m → Fin B') (Fin m → Fin B') ℂ) * Y *
          (Matrix.kronecker (prepK g0 x) (1 : Matrix (Fin m → Fin B') (Fin m → Fin B') ℂ))ᴴ) *
        (Matrix.kronecker (1 : Matrix γ γ ℂ) (prepK h0 y))ᴴ =
      Matrix.kronecker (prepK g0 x) (prepK h0 y) * Y *
        (Matrix.kronecker (prepK g0 x) (prepK h0 y))ᴴ := fun x y => kron_two_step _ _ _
  simp only [e]
  exact prep_output g0 h0 Y

end Proto

end FKR

end FKR_Proto

section FKR_Error

/-!
# Error analysis of the block-filtering protocol
-/

open QAlgorithms
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

open Matrix

lemma psd_trace_real {I : Type*} [Fintype I] {X : Matrix I I ℂ} (h : X.PosSemidef) :
    X.trace = ((X.trace.re : ℝ) : ℂ) := by
  have := h.trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact Complex.ext (by simp) (by simp [← this.2])

lemma psd_trace_re_nonneg {I : Type*} [Fintype I] {X : Matrix I I ℂ} (h : X.PosSemidef) :
    0 ≤ X.trace.re := (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma traceNorm_zero' {I : Type*} [Fintype I] [DecidableEq I] :
    traceNorm (0 : Matrix I I ℂ) = 0 := by
  simp [traceNorm]

lemma traceNorm_sum_smul_le {I ι : Type*} [Fintype I] [DecidableEq I] (s : Finset ι)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (X : ι → Matrix I I ℂ) :
    traceNorm (∑ i ∈ s, (c i : ℂ) • X i) ≤ ∑ i ∈ s, c i * traceNorm (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceNorm_zero']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (traceNorm_add_le _ _).trans (add_le_add (traceNorm_smul_le _ (hc j) _) ih)

lemma traceNorm_sum_le {I ι : Type*} [Fintype I] [DecidableEq I] (s : Finset ι)
    (X : ι → Matrix I I ℂ) : traceNorm (∑ i ∈ s, X i) ≤ ∑ i ∈ s, traceNorm (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceNorm_zero']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

lemma kron_sum_sum {ι κ m n p r : Type*} [Fintype ι] [Fintype κ] (A : ι → Matrix m n ℂ)
    (B : κ → Matrix p r ℂ) :
    Matrix.kronecker (∑ i, A i) (∑ j, B j) = ∑ i, ∑ j, Matrix.kronecker (A i) (B j) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [kron_eq, kronecker_apply, Matrix.sum_apply, Finset.sum_mul_sum]

section Analysis

variable {A B A' B' : ℕ}
variable (FA : Matrix (Fin A') (Fin A) ℂ) (GA : Matrix (Fin A) (Fin A) ℂ) (eA : Fin A')
  (FB : Matrix (Fin B') (Fin B) ℂ) (GB : Matrix (Fin B) (Fin B) ℂ) (eB : Fin B')
variable (ω : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)

/-- The per-round outcome distribution. -/
noncomputable def mu (o : Option (Fin A) × Option (Fin B)) : ℝ :=
  (Matrix.kronecker (kfam FA GA eA o.1) (kfam FB GB eB o.2) * ω *
    (Matrix.kronecker (kfam FA GA eA o.1) (kfam FB GB eB o.2))ᴴ).trace.re

lemma mu_nonneg (hω : ω.PosSemidef) (o : Option (Fin A) × Option (Fin B)) :
    0 ≤ mu FA GA eA FB GB eB ω o :=
  psd_trace_re_nonneg (hω.mul_mul_conjTranspose_same _)

lemma Mw_trace (hω : ω.PosSemidef) {m : ℕ} (wA : Fin m → Option (Fin A))
    (wB : Fin m → Option (Fin B)) (t : Fin m) :
    (Mw FA GA eA FB GB eB ω wA wB t).trace = (mu FA GA eA FB GB eB ω (wA t, wB t) : ℂ) :=
  psd_trace_real (hω.mul_mul_conjTranspose_same _)

lemma mu_sum (hGA : GAᴴ * GA = 1 - FAᴴ * FA) (hGB : GBᴴ * GB = 1 - FBᴴ * FB)
    (hω : IsDensityMatrix ω) : ∑ o, mu FA GA eA FB GB eB ω o = 1 := by
  have hK : ∑ o : Option (Fin A) × Option (Fin B),
      (Matrix.kronecker (kfam FA GA eA o.1) (kfam FB GB eB o.2))ᴴ *
        Matrix.kronecker (kfam FA GA eA o.1) (kfam FB GB eB o.2) = 1 := by
    have e : ∀ o : Option (Fin A) × Option (Fin B),
        (Matrix.kronecker (kfam FA GA eA o.1) (kfam FB GB eB o.2))ᴴ *
          Matrix.kronecker (kfam FA GA eA o.1) (kfam FB GB eB o.2) =
        Matrix.kronecker ((kfam FA GA eA o.1)ᴴ * kfam FA GA eA o.1)
          ((kfam FB GB eB o.2)ᴴ * kfam FB GB eB o.2) := by
      intro o
      simp only [kron_eq, conjTranspose_kronecker, ← mul_kronecker_mul]
    simp only [e]
    rw [Fintype.sum_prod_type' (fun u v => Matrix.kronecker ((kfam FA GA eA u)ᴴ * kfam FA GA eA u)
      ((kfam FB GB eB v)ᴴ * kfam FB GB eB v)), ← kron_sum_sum, kfam_kraus FA GA eA hGA,
      kfam_kraus FB GB eB hGB]
    simp only [kron_eq, one_kronecker_one]
  have := trace_conj_sum (fun o : Option (Fin A) × Option (Fin B) =>
    Matrix.kronecker (kfam FA GA eA o.1) (kfam FB GB eB o.2)) hK ω
  unfold mu
  rw [← Complex.re_sum, this, hω.2, Complex.one_re]

lemma mu_none (ω' : Matrix (Fin A' × Fin B') (Fin A' × Fin B') ℂ) (hω' : IsDensityMatrix ω') (q : ℝ)
    (hfilt : Matrix.kronecker FA FB * ω * (Matrix.kronecker FA FB)ᴴ = (q : ℂ) • ω') :
    mu FA GA eA FB GB eB ω (none, none) = q := by
  unfold mu
  simp only [kfam_none]
  rw [hfilt, Matrix.trace_smul, hω'.2, smul_eq_mul, mul_one, Complex.ofReal_re]

/-- The total probability of the outcome patterns. -/
lemma sum_patterns (μ : Option (Fin A) × Option (Fin B) → ℝ) {m : ℕ} :
    ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B), ∏ t, μ (wA t, wB t) =
      ∏ _t : Fin m, ∑ o, μ o := by
  have e1 : ∀ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B), ∏ t, μ (wA t, wB t) =
      ∏ t, ∑ v : Option (Fin B), μ (wA t, v) := fun wA =>
    (Fintype.prod_sum (fun (t : Fin m) (v : Option (Fin B)) => μ (wA t, v))).symm
  simp only [e1]
  rw [← Fintype.prod_sum (fun (t : Fin m) (u : Option (Fin A)) => ∑ v : Option (Fin B), μ (u, v))]
  refine Finset.prod_congr rfl fun t _ => ?_
  exact (Fintype.sum_prod_type' (fun u v => μ (u, v))).symm

/-- The output of the protocol: a convex combination of `Lk(ω'^{⊗k})` and the prepared state. -/
theorem proto_output (hω : IsDensityMatrix ω) (ω' : Matrix (Fin A' × Fin B') (Fin A' × Fin B') ℂ)
    (hω' : IsDensityMatrix ω') (q : ℝ)
    (hfilt : Matrix.kronecker FA FB * ω * (Matrix.kronecker FA FB)ᴴ = (q : ℂ) • ω')
    {γ δ : Type} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]
    [Inhabited (Fin A')] [Inhabited (Fin B')] {m k : ℕ}
    {Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ} (hLk : IsLOCCAbs Lk) (g0 : γ) (h0 : δ) :
    proto (m := m) FA GA eA FB GB eB Lk g0 h0 (hpow (fun _ : Fin m => ω)) =
      ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
        ((∏ t, mu FA GA eA FB GB eB ω (wA t, wB t) : ℝ) : ℂ) •
          (if k ≤ (succ wA wB).card then Lk (hpow (fun _ : Fin k => ω')) else prepState g0 h0) := by
  rw [proto_apply]
  refine Finset.sum_congr rfl fun wA _ => Finset.sum_congr rfl fun wB _ => ?_
  have hPc : ((∏ t, mu FA GA eA FB GB eB ω (wA t, wB t) : ℝ) : ℂ) =
      ∏ t, (Mw FA GA eA FB GB eB ω wA wB t).trace := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun t _ => (Mw_trace FA GA eA FB GB eB ω hω.1 wA wB t).symm
  by_cases h : k ≤ (succ wA wB).card
  · rw [if_pos h]
    unfold contMap
    rw [dif_pos h]
    set ι := Classical.choose (exists_sel _ h) with hιdef
    have hι : Function.Injective ι := (Classical.choose_spec (exists_sel _ h)).1
    have hS : ∀ i, ι i ∈ succ wA wB := (Classical.choose_spec (exists_sel _ h)).2
    rw [goodMap_apply _ hι hLk]
    have hM : ∀ i, Mw FA GA eA FB GB eB ω wA wB (ι i) = (q : ℂ) • ω' := by
      intro i
      have h2 : wA (ι i) = none ∧ wB (ι i) = none := (Finset.mem_filter.mp (hS i)).2
      unfold Mw
      rw [h2.1, h2.2, kfam_none, kfam_none]
      exact hfilt
    have hM' : (fun i => Mw FA GA eA FB GB eB ω wA wB (ι i)) = fun _ => (q : ℂ) • ω' :=
      funext hM
    rw [hM', hpow_smul_const, hLk.map_smul, smul_smul, hPc,
      prod_split hι (fun t => (Mw FA GA eA FB GB eB ω wA wB t).trace)]
    congr 1
    rw [mul_comm]
    congr 1
    have hq1 : ∀ i, (Mw FA GA eA FB GB eB ω wA wB (ι i)).trace = (q : ℂ) := by
      intro i
      rw [hM i, Matrix.trace_smul, hω'.2, smul_eq_mul, mul_one]
    simp only [hq1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    unfold contMap
    rw [dif_neg h, badMap_apply, hpow_trace, hPc]

/-- The probability of the bad branch, by Chebyshev's inequality. -/
theorem bad_prob (hGA : GAᴴ * GA = 1 - FAᴴ * FA) (hGB : GBᴴ * GB = 1 - FBᴴ * FB)
    (hω : IsDensityMatrix ω) (ω' : Matrix (Fin A' × Fin B') (Fin A' × Fin B') ℂ)
    (hω' : IsDensityMatrix ω') (q : ℝ)
    (hfilt : Matrix.kronecker FA FB * ω * (Matrix.kronecker FA FB)ᴴ = (q : ℂ) • ω')
    {m k : ℕ} (hk : (k : ℝ) < m * q) :
    ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
      (∏ t, mu FA GA eA FB GB eB ω (wA t, wB t)) * (if k ≤ (succ wA wB).card then 0 else 1) ≤
      m * q * (1 - q) / (m * q - k) ^ 2 := by
  classical
  set μ := mu FA GA eA FB GB eB ω with hμdef
  have hμ0 : ∀ o, 0 ≤ μ o := mu_nonneg FA GA eA FB GB eB ω hω.1
  have hμ1 : ∑ o, μ o = 1 := mu_sum FA GA eA FB GB eB ω hGA hGB hω
  have hμq : μ (none, none) = q := mu_none FA GA eA FB GB eB ω ω' hω' q hfilt
  let ind : Option (Fin A) × Option (Fin B) → ℝ := fun o => if o = (none, none) then 1 else 0
  have hind : ∀ x, ind x * ind x = ind x := fun x => by
    simp only [ind]; split_ifs <;> norm_num
  have hq' : ∑ x, μ x * ind x = q := by
    rw [Finset.sum_eq_single (none, none)]
    · simp [ind, hμq]
    · intro b _ hb; simp [ind, hb]
    · simp
  have hcheb := count_lower_tail μ ind hμ0 hμ1 hind (k : ℝ) (by rw [hq']; exact hk)
  rw [hq'] at hcheb
  refine le_trans (le_of_eq ?_) hcheb
  rw [← Fintype.sum_prod_type' (fun wA wB => (∏ t, μ (wA t, wB t)) *
    (if k ≤ (succ wA wB).card then (0 : ℝ) else 1))]
  refine Fintype.sum_equiv (pairE (Option (Fin A)) (Option (Fin B))) _ _ fun p => ?_
  congr 1
  have hcard : ∑ t, ind (pairE (Option (Fin A)) (Option (Fin B)) p t) =
      ((succ p.1 p.2).card : ℝ) := by
    simp only [succ, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ind, pairE_apply, Prod.mk.injEq]
  split_ifs with h1 h2 h2
  · rw [hcard] at h2
    exact absurd h2 (not_lt.mpr (by exact_mod_cast h1))
  · rfl
  · rfl
  · rw [hcard] at h2
    exact absurd (by exact_mod_cast not_le.mp h1) h2

/-- **Error bound for the protocol.** -/
theorem proto_error (hGA : GAᴴ * GA = 1 - FAᴴ * FA) (hGB : GBᴴ * GB = 1 - FBᴴ * FB)
    (hω : IsDensityMatrix ω) (ω' : Matrix (Fin A' × Fin B') (Fin A' × Fin B') ℂ)
    (hω' : IsDensityMatrix ω') (q : ℝ)
    (hfilt : Matrix.kronecker FA FB * ω * (Matrix.kronecker FA FB)ᴴ = (q : ℂ) • ω')
    {γ δ : Type} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]
    [Inhabited (Fin A')] [Inhabited (Fin B')] {m k : ℕ} (hk : (k : ℝ) < m * q)
    {Lk : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (γ × δ) (γ × δ) ℂ} (hLk : IsLOCCAbs Lk) (g0 : γ) (h0 : δ)
    (Γ : Matrix (γ × δ) (γ × δ) ℂ) (ε' : ℝ)
    (hY : traceNorm (Lk (hpow (fun _ : Fin k => ω')) - Γ) ≤ ε') :
    traceNorm (proto (m := m) FA GA eA FB GB eB Lk g0 h0 (hpow (fun _ : Fin m => ω)) - Γ) ≤
      ε' + 2 * (m * q * (1 - q) / (m * q - k) ^ 2) := by
  classical
  have hμ0 : ∀ o, 0 ≤ mu FA GA eA FB GB eB ω o := mu_nonneg FA GA eA FB GB eB ω hω.1
  have hμ1 : ∑ o, mu FA GA eA FB GB eB ω o = 1 := mu_sum FA GA eA FB GB eB ω hGA hGB hω
  have hP0 : ∀ (wA : Fin m → Option (Fin A)) (wB : Fin m → Option (Fin B)),
      0 ≤ ∏ t, mu FA GA eA FB GB eB ω (wA t, wB t) :=
    fun _ _ => Finset.prod_nonneg fun t _ => hμ0 _
  have hP1 : ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
      ∏ t, mu FA GA eA FB GB eB ω (wA t, wB t) = 1 := by
    rw [sum_patterns, hμ1, Finset.prod_const_one]
  rw [proto_output FA GA eA FB GB eB ω hω ω' hω' q hfilt hLk g0 h0]
  -- write the difference as a convex combination
  have hΓ : Γ = ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
      ((∏ t, mu FA GA eA FB GB eB ω (wA t, wB t) : ℝ) : ℂ) • Γ := by
    simp only [← Finset.sum_smul, ← Complex.ofReal_sum, hP1, Complex.ofReal_one, one_smul]
  conv_lhs => rw [hΓ]
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← smul_sub]
  have hY1 : traceNorm (Lk (hpow (fun _ : Fin k => ω'))) = 1 := by
    apply traceNorm_density
    refine ⟨hLk.posSemidef _ (hpow_posSemidef _ fun _ => hω'.1), ?_⟩
    rw [hLk.trace, hpow_trace, hω'.2, Finset.prod_const_one]
  have hω01 : traceNorm (prepState g0 h0) = 1 := traceNorm_density (prepState_density g0 h0)
  have hterm : ∀ (wA : Fin m → Option (Fin A)) (wB : Fin m → Option (Fin B)),
      (∏ t, mu FA GA eA FB GB eB ω (wA t, wB t)) *
        traceNorm ((if k ≤ (succ wA wB).card then Lk (hpow (fun _ : Fin k => ω'))
          else prepState g0 h0) - Γ) ≤
      (∏ t, mu FA GA eA FB GB eB ω (wA t, wB t)) * ε' +
        2 * ((∏ t, mu FA GA eA FB GB eB ω (wA t, wB t)) *
          (if k ≤ (succ wA wB).card then 0 else 1)) := by
    intro wA wB
    by_cases h : k ≤ (succ wA wB).card
    · rw [if_pos h, if_pos h, mul_zero, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left hY (hP0 wA wB)
    · rw [if_neg h, if_neg h, mul_one]
      have e : prepState g0 h0 - Γ = (prepState g0 h0 - Lk (hpow (fun _ : Fin k => ω'))) +
          (Lk (hpow (fun _ : Fin k => ω')) - Γ) := by abel
      rw [e]
      have h1 := traceNorm_add_le (prepState g0 h0 - Lk (hpow (fun _ : Fin k => ω')))
        (Lk (hpow (fun _ : Fin k => ω')) - Γ)
      have h2 := traceNorm_sub_le (prepState g0 h0) (Lk (hpow (fun _ : Fin k => ω')))
      rw [hω01, hY1] at h2
      have h3 : traceNorm (prepState g0 h0 - Lk (hpow (fun _ : Fin k => ω')) +
          (Lk (hpow (fun _ : Fin k => ω')) - Γ)) ≤ 2 + ε' := by linarith
      have := mul_le_mul_of_nonneg_left h3 (hP0 wA wB)
      linarith
  calc traceNorm (∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
        ((∏ t, mu FA GA eA FB GB eB ω (wA t, wB t) : ℝ) : ℂ) •
          ((if k ≤ (succ wA wB).card then Lk (hpow (fun _ : Fin k => ω'))
            else prepState g0 h0) - Γ))
      ≤ ∑ wA : Fin m → Option (Fin A), traceNorm (∑ wB : Fin m → Option (Fin B),
        ((∏ t, mu FA GA eA FB GB eB ω (wA t, wB t) : ℝ) : ℂ) •
          ((if k ≤ (succ wA wB).card then Lk (hpow (fun _ : Fin k => ω'))
            else prepState g0 h0) - Γ)) := traceNorm_sum_le _ _
    _ ≤ ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
        (∏ t, mu FA GA eA FB GB eB ω (wA t, wB t)) *
          traceNorm ((if k ≤ (succ wA wB).card then Lk (hpow (fun _ : Fin k => ω'))
            else prepState g0 h0) - Γ) :=
        Finset.sum_le_sum fun wA _ => traceNorm_sum_smul_le _ _ (fun wB => hP0 wA wB) _
    _ ≤ ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
        ((∏ t, mu FA GA eA FB GB eB ω (wA t, wB t)) * ε' +
          2 * ((∏ t, mu FA GA eA FB GB eB ω (wA t, wB t)) *
            (if k ≤ (succ wA wB).card then 0 else 1))) :=
        Finset.sum_le_sum fun wA _ => Finset.sum_le_sum fun wB _ => hterm wA wB
    _ = ε' + 2 * ∑ wA : Fin m → Option (Fin A), ∑ wB : Fin m → Option (Fin B),
          (∏ t, mu FA GA eA FB GB eB ω (wA t, wB t)) *
            (if k ≤ (succ wA wB).card then 0 else 1) := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hP1, one_mul]
    _ ≤ ε' + 2 * (m * q * (1 - q) / (m * q - k) ^ 2) := by
        have hb := bad_prob FA GA eA FB GB eB ω hGA hGB hω ω' hω' q hfilt hk
        linarith

end Analysis

end FKR

end FKR_Error

section FKR_FilterRate

/-!
# Key rates through a local filter (single-system version)

If a local filter `F_A ⊗ F_B` (with `F†F ≤ 𝟙`) maps `ω` to `q·ω'`, every key rate `r` of `ω'`
gives the key rate `q·r` of `ω`.
-/

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)
open QAlgorithms.Papers.Independent.Gap48.P42 (KeyAchievable bipartitePrivate)
open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower copyIndex)
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

open Matrix

lemma rate_arith (q r δ θ L : ℝ) (m k : ℕ) (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hθ : 0 < θ) (hθδ : θ ≤ δ / (4 * (r + 1))) (hm : 4 * (r + 1) / δ < m) (hk0 : 0 < k)
    (hk2 : (q - θ) * m - 1 < k) (hL0 : 0 ≤ L) (hrate : r - δ / 2 ≤ L / k) :
    q * r - δ ≤ L / m := by
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  by_cases hrd : r ≤ δ / 2
  · have : q * r ≤ r := by nlinarith
    have : 0 ≤ L / m := div_nonneg hL0 hm0.le
    linarith
  rw [not_le] at hrd
  have hLk : (r - δ / 2) * k ≤ L := by rwa [le_div_iff₀ hk0'] at hrate
  have hθr : r * θ ≤ δ / 4 := by
    have h1 : r * θ ≤ r * (δ / (4 * (r + 1))) := mul_le_mul_of_nonneg_left hθδ hr
    have h2 : r * (δ / (4 * (r + 1))) ≤ δ / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hmr : r / m ≤ δ / 4 := by
    rw [div_le_iff₀ hm0]
    have : 4 * (r + 1) < δ * m := by rw [div_lt_iff₀ hδ] at hm; linarith
    nlinarith
  have key : (r - δ / 2) * ((q - θ) * m - 1) ≤ L := by
    have := mul_le_mul_of_nonneg_left hk2.le (by linarith : (0 : ℝ) ≤ r - δ / 2)
    linarith
  rw [le_div_iff₀ hm0]
  have e : (r - δ / 2) * ((q - θ) * m - 1) = m * (r * q - r * θ - r / m - δ / 2 * q + δ / 2 * θ) +
      δ / 2 := by
    field_simp
    ring
  rw [e] at key
  have h5 : m * (q * r - δ) ≤ m * (r * q - r * θ - r / m - δ / 2 * q + δ / 2 * θ) := by
    apply mul_le_mul_of_nonneg_left _ hm0.le
    nlinarith
  nlinarith

lemma err_arith (q θ ε : ℝ) (m k : ℕ) (hθ : 0 < θ) (hε : 0 < ε) (hm : 1 / (θ ^ 2 * ε) < m)
    (hk1 : (k : ℝ) ≤ (q - θ) * m) :
    2 * (m * q * (1 - q) / (m * q - k) ^ 2) ≤ ε / 2 := by
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  have hgap : θ * m ≤ m * q - k := by nlinarith
  have hgap0 : 0 < θ * m := by positivity
  have hsq : (θ * m) ^ 2 ≤ (m * q - k) ^ 2 := pow_le_pow_left₀ hgap0.le hgap 2
  have hnum : m * q * (1 - q) ≤ m / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have h1 : m * q * (1 - q) / (m * q - k) ^ 2 ≤ (m / 4) / (θ * m) ^ 2 := by
    calc m * q * (1 - q) / (m * q - k) ^ 2 ≤ (m / 4) / (m * q - k) ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (m / 4) / (θ * m) ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
  have h2 : (m / 4) / (θ * m) ^ 2 = 1 / (4 * θ ^ 2 * m) := by
    field_simp
  have h3 : 1 / (4 * θ ^ 2 * m) ≤ ε / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 1 < θ ^ 2 * ε * m := by
      rw [div_lt_iff₀ (by positivity)] at hm; linarith
    nlinarith
  linarith

lemma dimensionedPower_reindex {a b n : ℕ} (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (dimensionedPower ρ n).submatrix (Prod.map (copyIndex a n) (copyIndex b n))
      (Prod.map (copyIndex a n) (copyIndex b n)) = hpow (fun _ : Fin n => ρ) := by
  ext x y
  simp [dimensionedPower, QAlgorithms.Papers.Independent.Information100.P80.groupedPower, hpow]

lemma dimensionedPower_eq {a b n : ℕ} (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    dimensionedPower ρ n = (hpow (fun _ : Fin n => ρ)).submatrix
      (Prod.map (copyIndex a n).symm (copyIndex b n).symm)
      (Prod.map (copyIndex a n).symm (copyIndex b n).symm) := rfl

open scoped MatrixOrder in
theorem filter_rate {A B A' B' : ℕ} (ω : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (hω : IsDensityMatrix ω) (ω' : Matrix (Fin A' × Fin B') (Fin A' × Fin B') ℂ)
    (hω' : IsDensityMatrix ω') (FA : Matrix (Fin A') (Fin A) ℂ) (FB : Matrix (Fin B') (Fin B) ℂ)
    (hFA : (1 - FAᴴ * FA).PosSemidef) (hFB : (1 - FBᴴ * FB).PosSemidef) (q : ℝ) (hq : 0 < q)
    (hfilt : Matrix.kronecker FA FB * ω * (Matrix.kronecker FA FB)ᴴ = (q : ℂ) • ω')
    (r : ℝ) (hr : KeyAchievable ω' r) : KeyAchievable ω (q * r) := by
  classical
  obtain ⟨hr0, hrach⟩ := hr
  obtain ⟨GA, hGA0⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hFA.nonneg
  obtain ⟨GB, hGB0⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hFB.nonneg
  have hGA : GAᴴ * GA = 1 - FAᴴ * FA := by rw [hGA0, Matrix.star_eq_conjTranspose]
  have hGB : GBᴴ * GB = 1 - FBᴴ * FB := by rw [hGB0, Matrix.star_eq_conjTranspose]
  have hA' : 0 < A' := by
    rcases Nat.eq_zero_or_pos A' with h | h
    · subst h
      have := hω'.2
      simp [Matrix.trace] at this
    · exact h
  have hB' : 0 < B' := by
    rcases Nat.eq_zero_or_pos B' with h | h
    · subst h
      have := hω'.2
      simp [Matrix.trace] at this
    · exact h
  have : Inhabited (Fin A') := ⟨⟨0, hA'⟩⟩
  have : Inhabited (Fin B') := ⟨⟨0, hB'⟩⟩
  have hq1 : q ≤ 1 := by
    have hs := mu_sum FA GA default FB GB default ω hGA hGB hω
    have hn := mu_none FA GA default FB GB default ω ω' hω' q hfilt
    have := Finset.single_le_sum (f := mu FA GA default FB GB default ω)
      (fun o _ => mu_nonneg FA GA default FB GB default ω hω.1 o) (Finset.mem_univ (none, none))
    linarith
  refine ⟨mul_nonneg hq.le hr0, fun ε hε δ hδ => ?_⟩
  set θ := min (q / 2) (δ / (4 * (r + 1))) with hθdef
  have hθpos : 0 < θ := lt_min (by linarith) (by positivity)
  have hθq : θ ≤ q / 2 := min_le_left _ _
  have hθδ : θ ≤ δ / (4 * (r + 1)) := min_le_right _ _
  obtain ⟨n0, hn0⟩ := hrach (ε / 2) (by positivity) (δ / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (max (((n0 : ℝ) + 1) / (q - θ)) (4 * (r + 1) / δ)) (1 / (θ ^ 2 * ε)))
  refine ⟨N + 1, fun m hm hm0 => ?_⟩
  have hmN : (N : ℝ) < m := by exact_mod_cast Nat.lt_of_succ_le hm
  have hm1 : ((n0 : ℝ) + 1) / (q - θ) < m :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) (hN.trans hmN)
  have hm2 : 4 * (r + 1) / δ < m :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) (hN.trans hmN)
  have hm3 : 1 / (θ ^ 2 * ε) < m := lt_of_le_of_lt (le_max_right _ _) (hN.trans hmN)
  have hqθ : 0 < q - θ := by linarith
  set k := ⌊(q - θ) * m⌋₊ with hkdef
  have hk1 : (k : ℝ) ≤ (q - θ) * m := Nat.floor_le (by positivity)
  have hk2 : (q - θ) * m - 1 < k := by
    have := Nat.lt_floor_add_one ((q - θ) * m)
    linarith
  have hkn : n0 + 1 ≤ k := by
    apply Nat.le_floor
    have := (div_lt_iff₀ hqθ).mp hm1
    push_cast
    linarith
  obtain ⟨d, s, t, hd, hs, ht, tau, htau, U, Lk, hLk, herr, hrate⟩ :=
    hn0 k (by omega) (by omega)
  -- the abstract version of the protocol for `ω'`
  let Lk' : Matrix ((Fin k → Fin A') × (Fin k → Fin B')) ((Fin k → Fin A') × (Fin k → Fin B')) ℂ →
      Matrix (Fin (d * s) × Fin (d * t)) (Fin (d * s) × Fin (d * t)) ℂ :=
    fun Y => Lk (Y.submatrix (Prod.map (copyIndex A' k).symm (copyIndex B' k).symm)
      (Prod.map (copyIndex A' k).symm (copyIndex B' k).symm))
  have hLk' : IsLOCCAbs Lk' := ⟨_, _, _, _, copyIndex A' k, copyIndex B' k, Equiv.refl _,
    Equiv.refl _, Lk, hLk, fun Y => by simp only [Equiv.coe_refl, Prod.map_id, submatrix_id_id, Lk']⟩
  have hY : traceNorm (Lk' (hpow (fun _ : Fin k => ω')) - bipartitePrivate tau U) ≤ ε / 2 := by
    simp only [Lk']
    rw [← dimensionedPower_eq]
    exact herr
  let g0 : Fin (d * s) := ⟨0, Nat.mul_pos hd hs⟩
  let h0 : Fin (d * t) := ⟨0, Nat.mul_pos hd ht⟩
  have hP := proto_locc (m := m) FA GA default FB GB default hLk' g0 h0 hGA hGB
  have hFin := hP.encode (copyIndex A m) (copyIndex B m) (Equiv.refl _) (Equiv.refl _)
  refine ⟨d, s, t, hd, hs, ht, tau, htau, U, _, hFin, ?_, ?_⟩
  · simp only [Equiv.refl_symm, Equiv.coe_refl, Prod.map_id, submatrix_id_id]
    rw [dimensionedPower_reindex]
    have hkq : (k : ℝ) < m * q := by nlinarith
    have he := proto_error FA GA default FB GB default ω hGA hGB hω ω' hω' q hfilt hkq hLk' g0 h0
      (bipartitePrivate tau U) (ε / 2) hY
    have he2 := err_arith q θ ε m k hθpos hε hm3 hk1
    linarith
  · have hL0 : 0 ≤ Real.logb 2 d := Real.logb_nonneg one_lt_two (by exact_mod_cast hd)
    exact rate_arith q r δ θ (Real.logb 2 d) m k hq hq1 hr0 hδ hθpos hθδ hm2 (by omega) hk2 hL0
      hrate

end FKR

end FKR_FilterRate

section FKR_Block

/-!
# Key rates of block states

A key rate `R` of the `n`-copy state `ρ^{⊗n}` (viewed as one bipartite state) gives the key rate
`R / n` of `ρ`: on `m` copies, discard the last `m mod n` copies, regroup the rest into
`⌊m/n⌋` blocks of `n` copies and run the protocol of the block state.
-/

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)
open QAlgorithms.Papers.Independent.Gap48.P42 (KeyAchievable bipartitePrivate)
open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower copyIndex)
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

open Matrix

section SelMap

variable {τ κ α β : Type} [Fintype τ] [DecidableEq τ] [Fintype κ] [DecidableEq κ]
  [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {γ δ : Type} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]

/-- Keep the registers `ι`, discard the rest, then run `L`. -/
noncomputable def selMap (ι : κ → τ)
    (L : Matrix ((κ → α) × (κ → β)) ((κ → α) × (κ → β)) ℂ → Matrix (γ × δ) (γ × δ) ℂ) :
    Matrix ((τ → α) × (τ → β)) ((τ → α) × (τ → β)) ℂ → Matrix (γ × δ) (γ × δ) ℂ :=
  fun X => ∑ zA : Cmp ι → α,
    (fun Y => ∑ zB : Cmp ι → β,
      L (Matrix.kronecker (1 : Matrix (κ → α) (κ → α) ℂ) (selK ι zB) * Y *
        (Matrix.kronecker (1 : Matrix (κ → α) (κ → α) ℂ) (selK ι zB))ᴴ))
    (Matrix.kronecker (selK ι zA) (1 : Matrix (τ → β) (τ → β) ℂ) * X *
      (Matrix.kronecker (selK ι zA) (1 : Matrix (τ → β) (τ → β) ℂ))ᴴ)

theorem selMap_locc (ι : κ → τ) (hι : Function.Injective ι)
    {L : Matrix ((κ → α) × (κ → β)) ((κ → α) × (κ → β)) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (hL : IsLOCCAbs L) [Inhabited α] [Inhabited β] : IsLOCCAbs (selMap ι L) :=
  IsLOCCAbs.alice (fun zA => selK ι zA) (selK_kraus hι) _ fun zA =>
    IsLOCCAbs.bob (fun zB => selK ι zB) (selK_kraus hι) (fun _ => L) fun zB => hL

theorem selMap_apply (ι : κ → τ) (hι : Function.Injective ι)
    {L : Matrix ((κ → α) × (κ → β)) ((κ → α) × (κ → β)) ℂ → Matrix (γ × δ) (γ × δ) ℂ}
    (hL : IsLOCCAbs L) [Inhabited α] [Inhabited β] (M : τ → Matrix (α × β) (α × β) ℂ) :
    selMap ι L (hpow M) = (∏ c : Cmp ι, (M c.1).trace) • L (hpow (fun i => M (ι i))) := by
  unfold selMap
  have e : ∀ (zA : Cmp ι → α) (zB : Cmp ι → β),
      Matrix.kronecker (1 : Matrix (κ → α) (κ → α) ℂ) (selK ι zB) *
        (Matrix.kronecker (selK ι zA) (1 : Matrix (τ → β) (τ → β) ℂ) * hpow M *
          (Matrix.kronecker (selK ι zA) (1 : Matrix (τ → β) (τ → β) ℂ))ᴴ) *
        (Matrix.kronecker (1 : Matrix (κ → α) (κ → α) ℂ) (selK ι zB))ᴴ =
      Matrix.kronecker (selK ι zA) (selK ι zB) * hpow M *
        (Matrix.kronecker (selK ι zA) (selK ι zB))ᴴ := fun zA zB => kron_two_step _ _ _
  simp only [e]
  simp only [← hL.map_sum]
  rw [sel_output hι M, hL.map_smul]

end SelMap

/-- Regrouping `B` blocks of `n` copies. -/
noncomputable def blockEquiv (a n B : ℕ) : Fin ((a ^ n) ^ B) ≃ (Fin B × Fin n → Fin a) :=
  (copyIndex (a ^ n) B).symm.trans
    ((Equiv.arrowCongr (Equiv.refl (Fin B)) (copyIndex a n).symm).trans
      (Equiv.curry (Fin B) (Fin n) (Fin a)).symm)

lemma blockEquiv_apply (a n B : ℕ) (P : Fin ((a ^ n) ^ B)) (p : Fin B × Fin n) :
    blockEquiv a n B P p = (copyIndex a n).symm ((copyIndex (a ^ n) B).symm P p.1) p.2 := rfl

lemma blockPower_eq {a b n B : ℕ} (ρ0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (hpow (fun _ : Fin B × Fin n => ρ0)).submatrix (Prod.map (blockEquiv a n B) (blockEquiv b n B))
      (Prod.map (blockEquiv a n B) (blockEquiv b n B)) = dimensionedPower (dimensionedPower ρ0 n) B := by
  ext ⟨P1, P2⟩ ⟨Q1, Q2⟩
  simp only [submatrix_apply, Prod.map_apply, hpow, blockEquiv_apply, Fintype.prod_prod_type,
    dimensionedPower, QAlgorithms.Papers.Independent.Information100.P80.groupedPower]

lemma block_rate_arith (R δ L : ℝ) (n m B : ℕ) (hn : 0 < n) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hm : 2 * R / δ < m) (hB : (m : ℝ) / n - 1 < B) (hB0 : 0 < B) (hL0 : 0 ≤ L)
    (hrate : R - n * δ / 2 ≤ L / B) : R / n - δ ≤ L / m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  have hB0' : (0 : ℝ) < B := by exact_mod_cast hB0
  by_cases hRd : R - n * δ / 2 ≤ 0
  · have h1 : R / n ≤ δ / 2 := by
      rw [div_le_iff₀ hn0]; linarith
    have : 0 ≤ L / m := div_nonneg hL0 hm0.le
    linarith
  rw [not_le] at hRd
  have hLB : (R - n * δ / 2) * B ≤ L := by rwa [le_div_iff₀ hB0'] at hrate
  have hRm : R / m ≤ δ / 2 := by
    rw [div_le_iff₀ hm0]
    have : 2 * R < δ * m := by rw [div_lt_iff₀ hδ] at hm; linarith
    linarith
  have key : (R - n * δ / 2) * ((m : ℝ) / n - 1) ≤ L := by
    have := mul_le_mul_of_nonneg_left hB.le hRd.le
    linarith
  rw [le_div_iff₀ hm0]
  have e : (R - n * δ / 2) * ((m : ℝ) / n - 1) = m * (R / n - δ / 2 - R / m) + n * δ / 2 := by
    field_simp
    ring
  rw [e] at key
  have h5 : m * (R / n - δ) ≤ m * (R / n - δ / 2 - R / m) := by
    apply mul_le_mul_of_nonneg_left _ hm0.le
    linarith
  nlinarith

theorem block_rate {a b n : ℕ} (hn : 1 ≤ n) (ρ0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hρ0 : IsDensityMatrix ρ0) (R : ℝ) (hR : KeyAchievable (dimensionedPower ρ0 n) R) :
    KeyAchievable ρ0 (R / n) := by
  classical
  obtain ⟨hR0, hRach⟩ := hR
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      have := hρ0.2
      simp [Matrix.trace] at this
    · exact h
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h
      have := hρ0.2
      simp [Matrix.trace] at this
    · exact h
  have : Inhabited (Fin a) := ⟨⟨0, ha⟩⟩
  have : Inhabited (Fin b) := ⟨⟨0, hb⟩⟩
  have hn0 : 0 < n := hn
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨div_nonneg hR0 hn0'.le, fun ε hε δ hδ => ?_⟩
  obtain ⟨B0, hB0⟩ := hRach ε hε (n * δ / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R / δ)
  refine ⟨n * (B0 + 1) + N, fun m hm hm0 => ?_⟩
  set B := m / n with hBdef
  have hBge : B0 + 1 ≤ B := by
    rw [hBdef, Nat.le_div_iff_mul_le hn0]
    nlinarith
  have hBm : B * n ≤ m := Nat.div_mul_le_self m n
  have hBreal : (m : ℝ) / n - 1 < B := by
    have h1 : m < B * n + n := Nat.lt_div_mul_add hn0
    have h2 : (m : ℝ) < B * n + n := by exact_mod_cast h1
    rw [div_sub_one hn0'.ne', div_lt_iff₀ hn0']
    linarith
  have hmN : 2 * R / δ < m := by
    have : (N : ℝ) ≤ m := by exact_mod_cast (le_trans (Nat.le_add_left N _) hm)
    linarith
  obtain ⟨d, s, t, hd, hs, ht, tau, htau, U, LB, hLB, herr, hrate⟩ :=
    hB0 B (by omega) (by omega)
  -- regrouping map and the protocol of the block state
  let LB' : Matrix ((Fin B × Fin n → Fin a) × (Fin B × Fin n → Fin b))
      ((Fin B × Fin n → Fin a) × (Fin B × Fin n → Fin b)) ℂ →
      Matrix (Fin (d * s) × Fin (d * t)) (Fin (d * s) × Fin (d * t)) ℂ :=
    fun Y => LB (Y.submatrix (Prod.map (blockEquiv a n B) (blockEquiv b n B))
      (Prod.map (blockEquiv a n B) (blockEquiv b n B)))
  have hLB' : IsLOCCAbs LB' := ⟨_, _, _, _, (blockEquiv a n B).symm, (blockEquiv b n B).symm,
    Equiv.refl _, Equiv.refl _, LB, hLB, fun Y => by
      simp only [Equiv.symm_symm, Equiv.coe_refl, Prod.map_id, submatrix_id_id, LB']⟩
  let ι : Fin B × Fin n → Fin m := fun p => Fin.castLE hBm (finProdFinEquiv p)
  have hι : Function.Injective ι :=
    (Fin.castLE_injective hBm).comp finProdFinEquiv.injective
  have hP := selMap_locc ι hι hLB'
  have hFin := hP.encode (copyIndex a m) (copyIndex b m) (Equiv.refl _) (Equiv.refl _)
  refine ⟨d, s, t, hd, hs, ht, tau, htau, U, _, hFin, ?_, ?_⟩
  · simp only [Equiv.refl_symm, Equiv.coe_refl, Prod.map_id, submatrix_id_id]
    rw [dimensionedPower_reindex, selMap_apply ι hι hLB']
    have htr : ∏ c : Cmp ι, ((fun _ : Fin m => ρ0) c.1).trace = 1 := by
      simp only [hρ0.2, Finset.prod_const_one]
    rw [htr, one_smul]
    simp only [LB']
    rw [blockPower_eq]
    exact herr
  · have hL0 : 0 ≤ Real.logb 2 d := Real.logb_nonneg one_lt_two (by exact_mod_cast hd)
    exact block_rate_arith R δ (Real.logb 2 d) n m B hn0 hR0 hδ hmN hBreal (by omega) hL0 hrate

end FKR

end FKR_Block

section FKR_Main

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)
open QAlgorithms.Papers.Independent.Gap48.P42 (distillableKey KeyAchievable)
open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower copyIndex)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKR

open Matrix HorodeckiBoundKey

/-- The fixed relabelling of a party's register `Fin 2 × S` used by `finCut`. -/
noncomputable def eK (S : Type) [Fintype S] [DecidableEq S] :
    Fin (Fintype.card (Fin 2 × S)) ≃ Fin 2 × S :=
  (Fintype.equivFin (Fin 2 × S)).symm

/-- Regrouping `((a, s), (b, t)) ↦ ((a, b), (s, t))`. -/
def regroup (S T : Type) : (Fin 2 × S) × (Fin 2 × T) ≃ Key 2 × (S × T) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv p := rfl
  right_inv p := rfl

/-- The relabelling performed by `finCut`, as an equivalence. -/
noncomputable def pcE (S T : Type) [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] :
    Fin (Fintype.card (Fin 2 × S)) × Fin (Fintype.card (Fin 2 × T)) ≃ Key 2 × (S × T) :=
  ((eK S).prodCongr (eK T)).trans (regroup S T)

/-- A party's `n` copies, relabelled as in `dimensionedPower ∘ finCut`. -/
noncomputable def decE (S : Type) [Fintype S] [DecidableEq S] (n : ℕ) :
    Fin (Fintype.card (Fin 2 × S) ^ n) ≃ (Fin n → Fin 2) × (Fin n → S) :=
  (copyIndex (Fintype.card (Fin 2 × S)) n).symm.trans
    ((Equiv.arrowCongr (Equiv.refl (Fin n)) (eK S)).trans
      (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 2) (fun _ => S)))

/-- Regrouping of `n` copies into the layout of `keyPower`. -/
def regroupN (n : ℕ) (S T : Type) :
    ((Fin n → Fin 2) × (Fin n → S)) × ((Fin n → Fin 2) × (Fin n → T)) ≃
      (Fin n → Key 2) × ((Fin n → S) × (Fin n → T)) where
  toFun p := (fun i => (p.1.1 i, p.2.1 i), (p.1.2, p.2.2))
  invFun p := ((fun i => (p.1 i).1, p.2.1), (fun i => (p.1 i).2, p.2.2))
  left_inv p := rfl
  right_inv p := rfl

noncomputable def eIn (n : ℕ) (S T : Type) [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] : Fin (Fintype.card (Fin 2 × S) ^ n) × Fin (Fintype.card (Fin 2 × T) ^ n) ≃
      (Fin n → Key 2) × ((Fin n → S) × (Fin n → T)) :=
  ((decE S n).prodCongr (decE T n)).trans (regroupN n S T)

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

lemma finCut_eq (ρ : Op (Key 2 × (S × T))) : finCut ρ = ρ.submatrix (pcE S T) (pcE S T) := rfl

lemma finCut_density {ρ : Op (Key 2 × (S × T))} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (finCut ρ) := by
  rw [finCut_eq]
  exact ⟨hρ.1.submatrix _, by rw [trace_submatrix_equiv, hρ.2]⟩

lemma dimensionedPower_density {a b : ℕ} {ρ0 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}
    (hρ0 : IsDensityMatrix ρ0) (n : ℕ) : IsDensityMatrix (dimensionedPower ρ0 n) := by
  rw [dimensionedPower_eq]
  refine ⟨(hpow_posSemidef _ fun _ => hρ0.1).submatrix _, ?_⟩
  rw [show Prod.map ⇑(copyIndex a n).symm ⇑(copyIndex b n).symm =
      ⇑((copyIndex a n).prodCongr (copyIndex b n)).symm from rfl, trace_submatrix_equiv,
    hpow_trace, hρ0.2, Finset.prod_const_one]

lemma dimensionedPower_finCut (ρ : Op (Key 2 × (S × T))) (n : ℕ) :
    dimensionedPower (finCut ρ) n = (keyPower ρ n).submatrix (eIn n S T) (eIn n S T) := rfl

lemma kron_tilde {S' T' : Type} [Fintype S'] [DecidableEq S'] [Fintype T'] [DecidableEq T'] {n : ℕ}
    (FA : Matrix (Fin 2 × S') ((Fin n → Fin 2) × (Fin n → S)) ℂ)
    (FB : Matrix (Fin 2 × T') ((Fin n → Fin 2) × (Fin n → T)) ℂ) :
    Matrix.kronecker (FA.submatrix (eK S') (decE S n)) (FB.submatrix (eK T') (decE T n)) =
      (localPair FA FB).submatrix (pcE S' T') (eIn n S T) := rfl

lemma one_sub_tilde {S' : Type} [Fintype S'] [DecidableEq S'] {n : ℕ}
    (FA : Matrix (Fin 2 × S') ((Fin n → Fin 2) × (Fin n → S)) ℂ)
    (hFA : (1 - FAᴴ * FA).PosSemidef) :
    (1 - (FA.submatrix (eK S') (decE S n))ᴴ * FA.submatrix (eK S') (decE S n)).PosSemidef := by
  have e : (FA.submatrix (eK S') (decE S n))ᴴ * FA.submatrix (eK S') (decE S n) =
      (FAᴴ * FA).submatrix (decE S n) (decE S n) := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv]
  rw [e, ← submatrix_one_equiv (decE S n)]
  exact hFA.submatrix _

end FKR

open FKR in
theorem solution {S T S' T' : Type} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] [Fintype S'] [DecidableEq S'] [Fintype T'] [DecidableEq T']
    (ρ : Op (Key 2 × (S × T))) (hρ : IsDensityMatrix ρ) (n : ℕ) (hn : 1 ≤ n)
    (FA : Matrix (Fin 2 × S') ((Fin n → Fin 2) × (Fin n → S)) ℂ)
    (FB : Matrix (Fin 2 × T') ((Fin n → Fin 2) × (Fin n → T)) ℂ)
    (hFA : (1 - FAᴴ * FA).PosSemidef) (hFB : (1 - FBᴴ * FB).PosSemidef)
    (q : ℝ) (hq : 0 < q) (σ : Op (Key 2 × (S' × T'))) (hσ : IsDensityMatrix σ)
    (hfilter : HorodeckiBoundKey.localPair FA FB * HorodeckiBoundKey.keyPower ρ n *
      (HorodeckiBoundKey.localPair FA FB)ᴴ = (q : ℂ) • σ) :
    ENNReal.ofReal (q / n) * distillableKey (HorodeckiBoundKey.finCut σ) ≤
      distillableKey (HorodeckiBoundKey.finCut ρ) := by
  classical
  have hρ' := finCut_density hρ
  have hσ' := finCut_density hσ
  have hω := dimensionedPower_density hρ' n
  have hfilt : Matrix.kronecker (FA.submatrix (eK S') (decE S n)) (FB.submatrix (eK T') (decE T n)) *
      dimensionedPower (HorodeckiBoundKey.finCut ρ) n *
      (Matrix.kronecker (FA.submatrix (eK S') (decE S n)) (FB.submatrix (eK T') (decE T n)))ᴴ =
      (q : ℂ) • HorodeckiBoundKey.finCut σ := by
    rw [kron_tilde, dimensionedPower_finCut, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hfilter, finCut_eq]
    rfl
  unfold distillableKey
  rw [ENNReal.mul_iSup]
  refine iSup_le fun r => ?_
  have h1 := filter_rate (dimensionedPower (HorodeckiBoundKey.finCut ρ) n) hω
    (HorodeckiBoundKey.finCut σ) hσ' _ _ (one_sub_tilde FA hFA) (one_sub_tilde FB hFB) q hq hfilt
    r.1 r.2
  have h2 := block_rate hn (HorodeckiBoundKey.finCut ρ) hρ' (q * r.1) h1
  rw [← ENNReal.ofReal_mul (div_nonneg hq.le (Nat.cast_nonneg n))]
  refine le_iSup_of_le ⟨q * r.1 / n, h2⟩ (le_of_eq ?_)
  congr 1
  ring

end FKR_Main
