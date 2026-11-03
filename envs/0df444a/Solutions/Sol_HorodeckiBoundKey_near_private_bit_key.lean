-- Prove2me | solution 1 for HorodeckiBoundKey.near_private_bit_key
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T18:18:11.231006+00:00
-- url     : https://prove2.me/submissions/46138ae2-0c78-4ad6-a467-5ae3544f470d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_HorodeckiBoundKey_finCut
import Definitions.Def_HorodeckiBoundKey_keyPower
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

/-!
# `HorodeckiBoundKey.near_private_bit_key`

There is `ε₀ > 0` (we take `ε₀ = 2⁻¹⁴`) such that every state `σ` on `A B A' B'` (one key qubit
per party, arbitrary finite shields) whose corner `X = ⟨00|σ|11⟩` has `‖X‖₁ > 1/2 - ε₀` has
strictly positive distillable key across `AA' : BB'`. We show the explicit rate `1/8`.

Proof outline (modules below; namespaces `FKR`, reused from the accepted `filter_key_rate`
solution, and `NPK`):
* Privacy squeezing (`Squeeze`): with the twist `V₀ = 𝟙`, `V₁ = W` (polar part of `X`), the
  distribution `p(x,z)` of `σ` in the twisted Bell basis satisfies `p(0,0) ≥ 2‖X‖₁`, so bit and
  phase errors have probability `< 2ε₀ = 2⁻¹³`.
* Codes (`Codes`): by a union bound there are `F₂`-linear maps `H₁` (bit checks), `H₂` (phase
  checks), `K` (key) with unique decoding of errors of weight `≤ w`, rows of `H₂` orthogonal
  to `H₁, K`, and coset representatives `t_k`.
* Protocol (`Proto`): Alice announces `H₁ a` and outputs `K a`; Bob corrects his raw key with the
  syndrome difference and outputs `K b'`. It is an `IsLOCCAbs` map (one-way LOCC).
* Twist (`Twist`, `GoodVec`): every good `n`-copy twisted Bell vector is mapped by every Kraus
  operator into the range of the private-state isometry `J g = 2^{-m/2} Σ_k |kk⟩ ⊗ U_k g`, where
  `U_k = C† (𝟙 ⊗ Q_{t_k} Ξ_k) C` (shield untwisting, coset translation, coherent phase correction
  via the spectral projectors of the `H₂`-translations).
* One shot (`OneShot`): virtual-decoding bound + gentle measurement: the output is within
  `2√(1-p) + 2(1-p)` of a private state, `p` = weight of the good patterns (Chebyshev, `Prob`).
* `Achieve`/`Final`: relabelling to the operational definition `KeyAchievable`, parameters
  `w = ⌊n/2048⌋`, `r₁ = r₂ = m = 512 w`, rate `m/n ≥ 1/8`.
-/

section Mod_FKR_LOCC
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

end Mod_FKR_LOCC

section Mod_FKR_Abs
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

end Mod_FKR_Abs

section Mod_FKR_TraceNorm
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

end Mod_FKR_TraceNorm

section Mod_FKR_Tensor
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

end Mod_FKR_Tensor

section Mod_FKR_Cheb
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

end Mod_FKR_Cheb

section Mod_NPK_MainLite
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

lemma dimensionedPower_finCut (ρ : Op (Key 2 × (S × T))) (n : ℕ) :
    dimensionedPower (finCut ρ) n = (keyPower ρ n).submatrix (eIn n S T) (eIn n S T) := rfl

end FKR

end Mod_NPK_MainLite

section Mod_NPK_F2
/-!
# Arithmetic over `F₂ = ZMod 2`: characters, weights, counting

Toolkit for the one-way hashing protocol of `near_private_bit_key`.
-/

open scoped Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

abbrev F2 := ZMod 2

/-- The nontrivial character of `F₂`: `χ(0) = 1`, `χ(1) = -1`. -/
def chi (x : F2) : ℂ := if x = 0 then 1 else -1

lemma F2_cases (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma F2_ne_zero_iff (x : F2) : x ≠ 0 ↔ x = 1 := by
  rcases F2_cases x with h | h <;> simp [h]

lemma F2_add_self (x : F2) : x + x = 0 := by
  rcases F2_cases x with rfl | rfl <;> decide

lemma vec_add_self {ι : Type*} (v : ι → F2) : v + v = 0 := by
  funext i; exact F2_add_self _

@[simp] lemma chi_zero : chi 0 = 1 := by simp [chi]

@[simp] lemma chi_one : chi 1 = -1 := by simp [chi]

lemma chi_add (x y : F2) : chi (x + y) = chi x * chi y := by
  rcases F2_cases x with rfl | rfl <;> rcases F2_cases y with rfl | rfl <;> simp [chi] <;> decide

lemma chi_mul_self (x : F2) : chi x * chi x = 1 := by
  rcases F2_cases x with rfl | rfl <;> simp

lemma star_chi (x : F2) : star (chi x) = chi x := by
  rcases F2_cases x with rfl | rfl <;> simp

lemma chi_ne_zero (x : F2) : chi x ≠ 0 := by
  rcases F2_cases x with rfl | rfl <;> simp

lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → F2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, chi_add, ih]

lemma univ_F2 : (Finset.univ : Finset F2) = {0, 1} := by decide

lemma sum_F2 {M : Type*} [AddCommMonoid M] (f : F2 → M) : ∑ x, f x = f 0 + f 1 := by
  rw [univ_F2, Finset.sum_pair (by decide)]

lemma sum_chi_mul (c : F2) : ∑ x : F2, chi (x * c) = if c = 0 then 2 else 0 := by
  rw [sum_F2]
  rcases F2_cases c with rfl | rfl
  · simp; norm_num
  · simp

/-- Orthogonality of characters on `F₂ⁿ`. -/
lemma sum_chi_dot {n : ℕ} (v : Fin n → F2) :
    ∑ a : Fin n → F2, chi (a ⬝ᵥ v) = if v = 0 then (2 : ℂ) ^ n else 0 := by
  have h1 : ∀ a : Fin n → F2, chi (a ⬝ᵥ v) = ∏ i, chi (a i * v i) := by
    intro a
    simp only [dotProduct]
    exact chi_sum _ _
  simp only [h1]
  rw [← Fintype.prod_sum (fun (i : Fin n) (x : F2) => chi (x * v i))]
  simp only [sum_chi_mul]
  by_cases hv : v = 0
  · subst hv; simp
  · rw [if_neg hv]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hi' : v i ≠ 0 := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])

/-- Hamming weight. -/
def wt {n : ℕ} (v : Fin n → F2) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

lemma wt_zero {n : ℕ} : wt (0 : Fin n → F2) = 0 := by simp [wt]

lemma wt_eq_zero_iff {n : ℕ} (v : Fin n → F2) : wt v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    by_contra hi
    have hi' : v i ≠ 0 := hi
    have : i ∈ Finset.univ.filter fun i => v i ≠ 0 := by simp [hi']
    rw [wt, Finset.card_eq_zero] at h
    rw [h] at this
    simp at this
  · rintro rfl; exact wt_zero

lemma wt_add_le {n : ℕ} (u v : Fin n → F2) : wt (u + v) ≤ wt u + wt v := by
  classical
  unfold wt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.add_apply] at hi ⊢
  by_contra h
  rw [not_or, not_not, not_not] at h
  rw [h.1, h.2, add_zero] at hi
  exact hi rfl

lemma wt_le {n : ℕ} (v : Fin n → F2) : wt v ≤ n := by
  unfold wt
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- Product formula for the Bernoulli weight of a vector. -/
lemma prod_bernoulli {n : ℕ} (β : ℝ) (v : Fin n → F2) :
    ∏ i, (if v i ≠ 0 then β else 1 - β) = β ^ wt v * (1 - β) ^ (n - wt v) := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => v i ≠ 0)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold wt
  omega

/-- **Ball-size bound.** For `0 < β ≤ 1/2` and `j ≤ n`, the number of vectors of weight at most
`j` is at most `β^{-j} (1 - β)^{-(n - j)}`. -/
lemma card_ball_le {n : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 2) (j : ℕ) (hj : j ≤ n) :
    ((Finset.univ.filter fun v : Fin n → F2 => wt v ≤ j).card : ℝ) * (β ^ j * (1 - β) ^ (n - j))
      ≤ 1 := by
  classical
  have h1β : β ≤ 1 - β := by linarith
  have h1β0 : 0 < 1 - β := by linarith
  have hpt : ∀ v : Fin n → F2, wt v ≤ j →
      β ^ j * (1 - β) ^ (n - j) ≤ β ^ wt v * (1 - β) ^ (n - wt v) := by
    intro v hv
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hv
    have e1 : n - wt v = d + (n - j) := by omega
    have hj' : β ^ j = β ^ wt v * β ^ d := by rw [hd, pow_add]
    have hn' : (1 - β) ^ (n - wt v) = (1 - β) ^ d * (1 - β) ^ (n - j) := by rw [e1, pow_add]
    rw [hj', hn']
    have : β ^ d ≤ (1 - β) ^ d := pow_le_pow_left₀ hβ0.le h1β d
    calc β ^ wt v * β ^ d * (1 - β) ^ (n - j)
        ≤ β ^ wt v * (1 - β) ^ d * (1 - β) ^ (n - j) := by gcongr
      _ = β ^ wt v * ((1 - β) ^ d * (1 - β) ^ (n - j)) := by ring
  have htot : ∑ v : Fin n → F2, β ^ wt v * (1 - β) ^ (n - wt v) = 1 := by
    simp only [← prod_bernoulli]
    rw [← Fintype.prod_sum (fun (i : Fin n) (x : F2) => if x ≠ 0 then β else 1 - β)]
    have : ∀ i : Fin n, ∑ x : F2, (if x ≠ 0 then β else 1 - β) = 1 := by
      intro i
      rw [sum_F2]
      simp only [ne_eq, not_true_eq_false, if_false]
      rw [if_pos (by decide)]; ring
    exact Finset.prod_eq_one fun i _ => this i
  calc ((Finset.univ.filter fun v : Fin n → F2 => wt v ≤ j).card : ℝ) * (β ^ j * (1 - β) ^ (n - j))
      = ∑ v ∈ Finset.univ.filter (fun v : Fin n → F2 => wt v ≤ j), β ^ j * (1 - β) ^ (n - j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n → F2 => wt v ≤ j),
          β ^ wt v * (1 - β) ^ (n - wt v) :=
        Finset.sum_le_sum fun v hv => hpt v (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v : Fin n → F2, β ^ wt v * (1 - β) ^ (n - wt v) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun v _ _ => by positivity)
    _ = 1 := htot

/-! ### Counting solutions of linear equations -/

lemma card_dot_eq {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → F2) (hy : y ≠ 0) (c : F2) :
    (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = c).card = 2 ^ Fintype.card ι / 2 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  have hyi : y i = 1 := (F2_ne_zero_iff _).mp hi
  let τ : (ι → F2) → (ι → F2) := fun h => h + Pi.single i 1
  have hτ : ∀ h, τ h ⬝ᵥ y = h ⬝ᵥ y + 1 := by
    intro h
    simp only [τ, add_dotProduct, single_dotProduct, one_mul, hyi]
  have hττ : ∀ h, τ (τ h) = h := by
    intro h
    simp only [τ, add_assoc]
    have : (Pi.single i (1 : F2) : ι → F2) + Pi.single i 1 = 0 := by
      rw [← Pi.single_add]; simp; decide
    rw [this, add_zero]
  have hcard : ∀ c' : F2, (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = c').card =
      (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = c' + 1).card := by
    intro c'
    refine Finset.card_bij (fun h _ => τ h) ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      rw [hτ, hh]
    · intro h1 _ h2 _ h12
      have := congrArg τ h12
      rwa [hττ, hττ] at this
    · intro h hh
      refine ⟨τ h, ?_, hττ h⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      rw [hτ, hh, add_assoc]
      have : (1 : F2) + 1 = 0 := by decide
      rw [this, add_zero]
  have htot : (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = 0).card +
      (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = 1).card = 2 ^ Fintype.card ι := by
    rw [← Finset.card_union_of_disjoint]
    · have : (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = 0) ∪
          (Finset.univ.filter fun h : ι → F2 => h ⬝ᵥ y = 1) = Finset.univ := by
        ext h
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact F2_cases _
      rw [this, Finset.card_univ, Fintype.card_fun, ZMod.card]
    · rw [Finset.disjoint_filter]
      intro h _ h0 h1
      rw [h0] at h1
      exact absurd h1 (by decide)
  have h01 := hcard 0
  simp only [zero_add] at h01
  rcases F2_cases c with rfl | rfl
  · omega
  · omega

lemma card_mulVec_eq {ρ ι : Type} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (y : ι → F2) (hy : y ≠ 0) (z : ρ → F2) :
    (Finset.univ.filter fun M : Matrix ρ ι F2 => M *ᵥ y = z).card =
      (2 ^ Fintype.card ι / 2) ^ Fintype.card ρ := by
  classical
  rw [← Fintype.card_subtype]
  have e : {M : Matrix ρ ι F2 // M *ᵥ y = z} ≃
      ((i : ρ) → {h : ι → F2 // h ⬝ᵥ y = z i}) :=
    (Equiv.subtypeEquivRight (fun M => by
      constructor
      · intro hM i; exact congrFun hM i
      · intro hM; funext i; exact hM i)).trans
      (Equiv.subtypePiEquivPi (p := fun (i : ρ) (h : ι → F2) => h ⬝ᵥ y = z i))
  rw [Fintype.card_congr e, Fintype.card_pi]
  simp only [Fintype.card_subtype, card_dot_eq y hy, Finset.prod_const, Finset.card_univ]

lemma half_pow_bound (N k : ℕ) :
    (((2 ^ N / 2) ^ k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N * k) * (1 / 2) ^ k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp [zero_pow hk.ne']
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h2 : 2 ^ (M + 1) / 2 = 2 ^ M := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [h2]
    push_cast
    rw [← pow_mul, show (M + 1) * k = M * k + k by ring, pow_add, mul_assoc, ← mul_pow]
    norm_num

end NPK

end Mod_NPK_F2

section Mod_NPK_Codes
/-!
# Existence of the codes used by the hashing protocol

For block length `n = r₂ + n'` we use the structured random construction
* `H₂ v = v₁ + C v₂` (phase checks),
* `φ v = Cᵀ v₁ + v₂`, `H₁ = Y₁ φ` (bit checks), `K = Y_K φ` (key map),
with `C, Y₁, Y_K` uniform. Every row of `H₂` lies in `ker H₁ ∩ ker K`. A counting (union) bound
shows that some choice makes `H₁` and `H₂` injective on vectors of weight `≤ 2w` and makes
`K` surjective on `ker H₁`.
-/

open scoped Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

/-- The interface used by the protocol. -/
structure GoodCode (n r1 r2 m w : ℕ) where
  H1 : Matrix (Fin r1) (Fin n) F2
  K : Matrix (Fin m) (Fin n) F2
  H2 : Matrix (Fin r2) (Fin n) F2
  dec : (Fin r1 → F2) → (Fin n → F2)
  zdec : (Fin r2 → F2) → (Fin n → F2)
  tk : (Fin m → F2) → (Fin n → F2)
  dec_spec : ∀ X, wt X ≤ w → dec (H1 *ᵥ X) = X
  zdec_spec : ∀ Z, wt Z ≤ w → zdec (H2 *ᵥ Z) = Z
  tk_H1 : ∀ k, H1 *ᵥ tk k = 0
  tk_K : ∀ k, K *ᵥ tk k = k
  orth_H1 : ∀ u : Fin r2 → F2, H1 *ᵥ (u ᵥ* H2) = 0
  orth_K : ∀ u : Fin r2 → F2, K *ᵥ (u ᵥ* H2) = 0

/-- Unique decoding from injectivity on low weights. -/
lemma decode_spec {n r w : ℕ} (H : Matrix (Fin r) (Fin n) F2)
    (hinj : ∀ v : Fin n → F2, v ≠ 0 → wt v ≤ 2 * w → H *ᵥ v ≠ 0) (X : Fin n → F2)
    (hX : wt X ≤ w) :
    (if h : ∃ X' : Fin n → F2, wt X' ≤ w ∧ H *ᵥ X' = H *ᵥ X then Classical.choose h else 0) = X := by
  have hex : ∃ X' : Fin n → F2, wt X' ≤ w ∧ H *ᵥ X' = H *ᵥ X := ⟨X, hX, rfl⟩
  rw [dif_pos hex]
  obtain ⟨hw, hH⟩ := Classical.choose_spec hex
  set X' := Classical.choose hex
  by_contra hne
  have hv : X' + X ≠ 0 := by
    intro h0
    apply hne
    have : X' = X' + X + X := by rw [add_assoc, vec_add_self, add_zero]
    rw [this, h0, zero_add]
  apply hinj (X' + X) hv (le_trans (wt_add_le _ _) (by omega))
  rw [Matrix.mulVec_add, hH, vec_add_self]

/-- Over `F₂`, a matrix with trivial left kernel is surjective. -/
lemma mulVec_surjective {ρ ι : Type} [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]
    (M : Matrix ρ ι F2) (hM : ∀ u : ρ → F2, u ᵥ* M = 0 → u = 0) :
    Function.Surjective (M *ᵥ ·) := by
  classical
  by_contra hns
  have hlt : LinearMap.range (Matrix.mulVecLin M) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hns fun z => ?_
    have : z ∈ LinearMap.range (Matrix.mulVecLin M) := by rw [htop]; trivial
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  let u : ρ → F2 := fun i => f (Pi.single i 1)
  have hfu : ∀ x : ρ → F2, f x = u ⬝ᵥ x := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp only [map_sum, dotProduct, u]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Pi.single i (x i) : ρ → F2) = x i • Pi.single i 1 by
      rw [← Pi.single_smul]; simp, map_smul, smul_eq_mul, mul_comm]
  have hu : u ᵥ* M = 0 := by
    funext j
    have h1 : M *ᵥ Pi.single j 1 ∈ LinearMap.range (Matrix.mulVecLin M) := ⟨_, rfl⟩
    have h2 := hfle h1
    rw [LinearMap.mem_ker, hfu, Matrix.dotProduct_mulVec] at h2
    simpa [dotProduct_single] using h2
  have hu0 := hM u hu
  apply hf0
  apply LinearMap.ext
  intro x
  rw [hfu, hu0, zero_dotProduct, LinearMap.zero_apply]

section Construction

variable {n r1 r2 m w n' : ℕ}

/-- Block structure of `Fin n = Fin r₂ ⊕ Fin n'`. -/
def splitE (h : r2 + n' = n) : Fin n ≃ Fin r2 ⊕ Fin n' :=
  (finCongr h.symm).trans finSumFinEquiv.symm

def glue (h : r2 + n' = n) (a : Fin r2 → F2) (b : Fin n' → F2) : Fin n → F2 :=
  fun x => Sum.elim a b (splitE h x)

def part1 (h : r2 + n' = n) (v : Fin n → F2) : Fin r2 → F2 := fun i => v ((splitE h).symm (Sum.inl i))

def part2 (h : r2 + n' = n) (v : Fin n → F2) : Fin n' → F2 := fun j => v ((splitE h).symm (Sum.inr j))

lemma sum_split (h : r2 + n' = n) {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ∑ x, f x = ∑ i, f ((splitE h).symm (Sum.inl i)) + ∑ j, f ((splitE h).symm (Sum.inr j)) := by
  have := Fintype.sum_sum_type (fun s : Fin r2 ⊕ Fin n' => f ((splitE h).symm s))
  rw [← this]
  exact Fintype.sum_equiv (splitE h) f _ (fun x => by simp)

lemma glue_eq_iff (h : r2 + n' = n) (v : Fin n → F2) : v = glue h (part1 h v) (part2 h v) := by
  funext x
  unfold glue part1 part2
  rcases hx : splitE h x with i | j
  · show v x = v ((splitE h).symm (Sum.inl i)); rw [← hx, Equiv.symm_apply_apply]
  · show v x = v ((splitE h).symm (Sum.inr j)); rw [← hx, Equiv.symm_apply_apply]

lemma part1_glue (h : r2 + n' = n) (a : Fin r2 → F2) (b : Fin n' → F2) :
    part1 h (glue h a b) = a := by
  funext i; simp [part1, glue]

lemma part2_glue (h : r2 + n' = n) (a : Fin r2 → F2) (b : Fin n' → F2) :
    part2 h (glue h a b) = b := by
  funext j; simp [part2, glue]

lemma ne_zero_parts (h : r2 + n' = n) {v : Fin n → F2} (hv : v ≠ 0) :
    part1 h v ≠ 0 ∨ part2 h v ≠ 0 := by
  by_contra hc
  rw [not_or, not_not, not_not] at hc
  apply hv
  rw [glue_eq_iff h v, hc.1, hc.2]
  funext x; simp only [glue, Pi.zero_apply]
  rcases splitE h x with i | j <;> rfl

/-- Phase checks `H₂ v = v₁ + C v₂`. -/
def H2C (h : r2 + n' = n) (C : Matrix (Fin r2) (Fin n') F2) : Matrix (Fin r2) (Fin n) F2 :=
  fun i x => Sum.elim (fun i' => if i = i' then 1 else 0) (fun j => C i j) (splitE h x)

/-- `φ v = Cᵀ v₁ + v₂`. -/
def phiC (h : r2 + n' = n) (C : Matrix (Fin r2) (Fin n') F2) : Matrix (Fin n') (Fin n) F2 :=
  fun j x => Sum.elim (fun i => C i j) (fun j' => if j = j' then 1 else 0) (splitE h x)

lemma H2C_mulVec (h : r2 + n' = n) (C : Matrix (Fin r2) (Fin n') F2) (v : Fin n → F2) :
    H2C h C *ᵥ v = part1 h v + C *ᵥ part2 h v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, H2C, Pi.add_apply]
  rw [sum_split h]
  simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, part1, part2]

lemma phiC_mulVec (h : r2 + n' = n) (C : Matrix (Fin r2) (Fin n') F2) (v : Fin n → F2) :
    phiC h C *ᵥ v = Cᵀ *ᵥ part1 h v + part2 h v := by
  funext j
  simp only [Matrix.mulVec, dotProduct, phiC, Pi.add_apply, Matrix.transpose_apply]
  rw [sum_split h]
  simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, part1, part2]

lemma vecMul_H2C (h : r2 + n' = n) (C : Matrix (Fin r2) (Fin n') F2) (u : Fin r2 → F2) :
    u ᵥ* H2C h C = glue h u (u ᵥ* C) := by
  funext x
  simp only [Matrix.vecMul, dotProduct, H2C, glue]
  rcases splitE h x with i | j
  · simp only [Sum.elim_inl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  · simp only [Sum.elim_inr]; rfl

lemma phiC_glue_orth (h : r2 + n' = n) (C : Matrix (Fin r2) (Fin n') F2) (u : Fin r2 → F2) :
    phiC h C *ᵥ glue h u (u ᵥ* C) = 0 := by
  rw [phiC_mulVec, part1_glue, part2_glue, Matrix.mulVec_transpose, vec_add_self]

lemma phiC_glue_zero (h : r2 + n' = n) (C : Matrix (Fin r2) (Fin n') F2) (y : Fin n' → F2) :
    phiC h C *ᵥ glue h 0 y = y := by
  rw [phiC_mulVec, part1_glue, part2_glue, Matrix.mulVec_zero, zero_add]

end Construction

section Existence

lemma card_mat (a b : ℕ) : Fintype.card (Matrix (Fin a) (Fin b) F2) = 2 ^ (a * b) := by
  show Fintype.card (Fin a → Fin b → ZMod 2) = _
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin, ← pow_mul,
    mul_comm]

lemma card_subtype_fst {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop) [DecidablePred P] :
    Fintype.card {ω : α × β // P ω.1} = Fintype.card {a // P a} * Fintype.card β := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr ⟨fun ω => (⟨ω.1.1, ω.2⟩, ω.1.2), fun p => ⟨(p.1.1, p.2), p.1.2⟩,
    fun _ => rfl, fun _ => rfl⟩

lemma card_subtype_snd {α β : Type*} [Fintype α] [Fintype β] (P : β → Prop) [DecidablePred P] :
    Fintype.card {ω : α × β // P ω.2} = Fintype.card α * Fintype.card {b // P b} := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr ⟨fun ω => (ω.1.1, ⟨ω.1.2, ω.2⟩), fun p => ⟨(p.1, p.2.1), p.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

lemma card_subtype_prod_le {α β : Type*} [Fintype α] [Fintype β] (P : α × β → Prop)
    [DecidablePred P] (c : ℕ) (hc : ∀ a, Fintype.card {b // P (a, b)} ≤ c) :
    Fintype.card {ω // P ω} ≤ Fintype.card α * c := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b => P (a, b)),
    Fintype.card_sigma]
  calc ∑ a, Fintype.card {b // P (a, b)} ≤ ∑ _a : α, c := Finset.sum_le_sum fun a _ => hc a
    _ = Fintype.card α * c := by simp

variable {n r1 r2 m w n' : ℕ}

/-- The sample space of the random construction. -/
abbrev MatY (r1 m n' : ℕ) := Matrix (Fin r1) (Fin n') F2 × Matrix (Fin m) (Fin n') F2

abbrev Omega (r1 r2 m n' : ℕ) := Matrix (Fin r2) (Fin n') F2 × MatY r1 m n'

lemma card_MatY : (Fintype.card (MatY r1 m n') : ℝ) = (2 : ℝ) ^ (r1 * n') * (2 : ℝ) ^ (m * n') := by
  simp only [Fintype.card_prod, card_mat]; push_cast; ring

lemma card_Omega : (Fintype.card (Omega r1 r2 m n') : ℝ) =
    (2 : ℝ) ^ (r2 * n') * ((2 : ℝ) ^ (r1 * n') * (2 : ℝ) ^ (m * n')) := by
  rw [Fintype.card_prod, Nat.cast_mul, card_MatY, card_mat]; push_cast; ring

def lowSet (n w : ℕ) : Finset (Fin n → F2) := Finset.univ.filter fun v => v ≠ 0 ∧ wt v ≤ 2 * w

lemma add_eq_zero_iff_F2 {ι : Type*} (a b : ι → F2) : a + b = 0 ↔ b = a := by
  constructor
  · intro hab
    calc b = a + b + a := by rw [add_comm a b, add_assoc, vec_add_self, add_zero]
      _ = a := by rw [hab, zero_add]
  · rintro rfl; exact vec_add_self _

lemma card_mulVec_eq_le {ρ ι : Type} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (y : ι → F2) (z : ρ → F2) (hyz : y = 0 → z ≠ 0) :
    (Fintype.card {M : Matrix ρ ι F2 // M *ᵥ y = z} : ℝ) ≤
      (2 : ℝ) ^ (Fintype.card ι * Fintype.card ρ) * (1 / 2) ^ Fintype.card ρ := by
  classical
  by_cases hy : y = 0
  · subst hy
    have : IsEmpty {M : Matrix ρ ι F2 // M *ᵥ 0 = z} :=
      ⟨fun M => hyz rfl (M.2.symm.trans (Matrix.mulVec_zero _))⟩
    rw [Fintype.card_eq_zero]; push_cast; positivity
  · rw [Fintype.card_subtype, card_mulVec_eq y hy z]
    exact half_pow_bound _ _

/-- Event 1: a low-weight error with trivial phase syndrome. -/
lemma card_E1_le (h : r2 + n' = n) {v : Fin n → F2} (hv : v ≠ 0) :
    (Fintype.card {ω : Omega r1 r2 m n' // H2C h ω.1 *ᵥ v = 0} : ℝ) ≤
      (Fintype.card (Omega r1 r2 m n') : ℝ) * (1 / 2) ^ r2 := by
  classical
  have e : Fintype.card {ω : Omega r1 r2 m n' // H2C h ω.1 *ᵥ v = 0} =
      Fintype.card {C : Matrix (Fin r2) (Fin n') F2 // C *ᵥ part2 h v = part1 h v} *
        Fintype.card (MatY r1 m n') := by
    rw [← card_subtype_fst]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun ω => by
      rw [H2C_mulVec, add_eq_zero_iff_F2])
  rw [e, Nat.cast_mul]
  have hb := card_mulVec_eq_le (ρ := Fin r2) (ι := Fin n') (part2 h v) (part1 h v) (fun h2 => by
    rcases ne_zero_parts h hv with h' | h'
    · exact h'
    · exact absurd h2 h')
  simp only [Fintype.card_fin] at hb
  rw [card_MatY, card_Omega]
  calc (Fintype.card {C : Matrix (Fin r2) (Fin n') F2 // C *ᵥ part2 h v = part1 h v} : ℝ) *
        ((2 : ℝ) ^ (r1 * n') * (2 : ℝ) ^ (m * n'))
      ≤ (2 ^ (n' * r2) * (1 / 2) ^ r2) * ((2 : ℝ) ^ (r1 * n') * (2 : ℝ) ^ (m * n')) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ (r2 * n') * ((2 : ℝ) ^ (r1 * n') * (2 : ℝ) ^ (m * n')) * (1 / 2) ^ r2 := by
        rw [mul_comm n' r2]; ring

/-- Event 2: a low-weight error in the kernel of `φ`. -/
lemma card_E2_le (h : r2 + n' = n) {v : Fin n → F2} (hv : v ≠ 0) :
    (Fintype.card {ω : Omega r1 r2 m n' // phiC h ω.1 *ᵥ v = 0} : ℝ) ≤
      (Fintype.card (Omega r1 r2 m n') : ℝ) * (1 / 2) ^ n' := by
  classical
  have e : Fintype.card {ω : Omega r1 r2 m n' // phiC h ω.1 *ᵥ v = 0} =
      Fintype.card {D : Matrix (Fin n') (Fin r2) F2 // D *ᵥ part1 h v = part2 h v} *
        Fintype.card (MatY r1 m n') := by
    rw [← card_subtype_fst]
    refine Fintype.card_congr ⟨fun ω => ⟨(ω.1.1ᵀ, ω.1.2), by
        have := ω.2; rw [phiC_mulVec, add_eq_zero_iff_F2] at this; exact this.symm⟩,
      fun p => ⟨(p.1.1ᵀ, p.1.2), by
        show phiC h p.1.1ᵀ *ᵥ v = 0
        rw [phiC_mulVec, add_eq_zero_iff_F2, Matrix.transpose_transpose]; exact p.2.symm⟩,
      fun ω => by simp, fun p => by simp⟩
  rw [e, Nat.cast_mul]
  have hb := card_mulVec_eq_le (ρ := Fin n') (ι := Fin r2) (part1 h v) (part2 h v) (fun h1 => by
    rcases ne_zero_parts h hv with h' | h'
    · exact absurd h1 h'
    · exact h')
  simp only [Fintype.card_fin] at hb
  rw [card_MatY, card_Omega]
  calc (Fintype.card {D : Matrix (Fin n') (Fin r2) F2 // D *ᵥ part1 h v = part2 h v} : ℝ) *
        ((2 : ℝ) ^ (r1 * n') * (2 : ℝ) ^ (m * n'))
      ≤ (2 ^ (r2 * n') * (1 / 2) ^ n') * ((2 : ℝ) ^ (r1 * n') * (2 : ℝ) ^ (m * n')) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ (r2 * n') * ((2 : ℝ) ^ (r1 * n') * (2 : ℝ) ^ (m * n')) * (1 / 2) ^ n' := by
        ring

/-- Event 3: a low-weight error outside `ker φ` with trivial bit syndrome. -/
lemma card_E3_le (h : r2 + n' = n) (v : Fin n → F2) :
    (Fintype.card {ω : Omega r1 r2 m n' //
        phiC h ω.1 *ᵥ v ≠ 0 ∧ ω.2.1 *ᵥ (phiC h ω.1 *ᵥ v) = 0} : ℝ) ≤
      (Fintype.card (Omega r1 r2 m n') : ℝ) * (1 / 2) ^ r1 := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun (C : Matrix (Fin r2) (Fin n') F2)
    (Y : MatY r1 m n') => phiC h C *ᵥ v ≠ 0 ∧ Y.1 *ᵥ (phiC h C *ᵥ v) = 0), Fintype.card_sigma]
  have hC : ∀ C : Matrix (Fin r2) (Fin n') F2,
      (Fintype.card {Y : MatY r1 m n' // phiC h C *ᵥ v ≠ 0 ∧ Y.1 *ᵥ (phiC h C *ᵥ v) = 0} : ℝ) ≤
        ((2 : ℝ) ^ (r1 * n') * (1 / 2) ^ r1) * (2 : ℝ) ^ (m * n') := by
    intro C
    by_cases hy : phiC h C *ᵥ v = 0
    · have : IsEmpty {Y : MatY r1 m n' // phiC h C *ᵥ v ≠ 0 ∧ Y.1 *ᵥ (phiC h C *ᵥ v) = 0} :=
        ⟨fun Y => Y.2.1 hy⟩
      rw [Fintype.card_eq_zero]; push_cast; positivity
    · have e : Fintype.card {Y : MatY r1 m n' // phiC h C *ᵥ v ≠ 0 ∧
          Y.1 *ᵥ (phiC h C *ᵥ v) = 0} =
          Fintype.card {Y1 : Matrix (Fin r1) (Fin n') F2 // Y1 *ᵥ (phiC h C *ᵥ v) = 0} *
            Fintype.card (Matrix (Fin m) (Fin n') F2) := by
        rw [← card_subtype_fst]
        exact Fintype.card_congr (Equiv.subtypeEquivRight fun Y => by simp [hy])
      rw [e, Nat.cast_mul, card_mat]
      have hb := card_mulVec_eq_le (ρ := Fin r1) (ι := Fin n') (phiC h C *ᵥ v) 0
        (fun h' => absurd h' hy)
      simp only [Fintype.card_fin] at hb
      push_cast
      calc (Fintype.card {Y1 : Matrix (Fin r1) (Fin n') F2 // Y1 *ᵥ (phiC h C *ᵥ v) = 0} : ℝ) *
            (2 : ℝ) ^ (m * n') ≤ (2 ^ (n' * r1) * (1 / 2) ^ r1) * (2 : ℝ) ^ (m * n') :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = _ := by rw [mul_comm n' r1]
  rw [Nat.cast_sum]
  calc ∑ C : Matrix (Fin r2) (Fin n') F2, (Fintype.card {Y : MatY r1 m n' //
        phiC h C *ᵥ v ≠ 0 ∧ Y.1 *ᵥ (phiC h C *ᵥ v) = 0} : ℝ)
      ≤ ∑ _C : Matrix (Fin r2) (Fin n') F2, ((2 : ℝ) ^ (r1 * n') * (1 / 2) ^ r1) *
          (2 : ℝ) ^ (m * n') := Finset.sum_le_sum fun C _ => hC C
    _ = (Fintype.card (Omega r1 r2 m n') : ℝ) * (1 / 2) ^ r1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Omega, card_mat]
        push_cast; ring

/-- Event 4: `[Y₁; Y_K]` has a nontrivial left kernel. -/
lemma card_E4_le :
    (Fintype.card {ω : Omega r1 r2 m n' // ∃ u : Fin r1 ⊕ Fin m → F2, u ≠ 0 ∧
        u ᵥ* Matrix.fromRows ω.2.1 ω.2.2 = 0} : ℝ) ≤
      (Fintype.card (Omega r1 r2 m n') : ℝ) * ((2 : ℝ) ^ (r1 + m) * (1 / 2) ^ n') := by
  classical
  rw [card_subtype_snd (α := Matrix (Fin r2) (Fin n') F2) (fun Y : MatY r1 m n' =>
    ∃ u : Fin r1 ⊕ Fin m → F2, u ≠ 0 ∧ u ᵥ* Matrix.fromRows Y.1 Y.2 = 0), Nat.cast_mul]
  have hu : ∀ u : Fin r1 ⊕ Fin m → F2, u ≠ 0 →
      (Fintype.card {Y : MatY r1 m n' // u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} : ℝ) ≤
        (Fintype.card (MatY r1 m n') : ℝ) * (1 / 2) ^ n' := by
    intro u hu0
    have e : Fintype.card {Y : MatY r1 m n' // u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} =
        Fintype.card {D : Matrix (Fin n') (Fin r1 ⊕ Fin m) F2 // D *ᵥ u = 0} := by
      refine Fintype.card_congr ⟨fun Y => ⟨(Matrix.fromRows Y.1.1 Y.1.2)ᵀ, by
          rw [Matrix.mulVec_transpose]; exact Y.2⟩,
        fun D => ⟨(fun i j => D.1 j (Sum.inl i), fun i j => D.1 j (Sum.inr i)), by
          have e : Matrix.fromRows (fun i j => D.1 j (Sum.inl i) : Matrix (Fin r1) (Fin n') F2)
              (fun i j => D.1 j (Sum.inr i) : Matrix (Fin m) (Fin n') F2) = D.1ᵀ := by
            ext k j; rcases k with k | k <;> rfl
          show u ᵥ* Matrix.fromRows _ _ = 0
          rw [e, Matrix.vecMul_transpose]; exact D.2⟩,
        fun Y => by ext <;> simp, fun D => by
          ext j k
          rcases k with k | k <;> rfl⟩
    rw [e]
    have hb := card_mulVec_eq_le (ρ := Fin n') (ι := Fin r1 ⊕ Fin m) u 0 (fun h' => absurd h' hu0)
    simp only [Fintype.card_fin, Fintype.card_sum] at hb
    refine hb.trans (le_of_eq ?_)
    rw [card_MatY]
    rw [show (r1 + m) * n' = r1 * n' + m * n' by ring, pow_add]
  have hunion : (Fintype.card {Y : MatY r1 m n' // ∃ u : Fin r1 ⊕ Fin m → F2, u ≠ 0 ∧
      u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} : ℝ) ≤
      ∑ u : Fin r1 ⊕ Fin m → F2, (Fintype.card {Y : MatY r1 m n' // u ≠ 0 ∧
        u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} : ℝ) := by
    simp only [Fintype.card_subtype]
    rw [← Nat.cast_sum]
    exact_mod_cast (Finset.card_le_card (fun Y hY => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
      obtain ⟨u, hu1, hu2⟩ := hY
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu1, hu2⟩⟩)).trans
      Finset.card_biUnion_le
  have hterm : ∀ u : Fin r1 ⊕ Fin m → F2, (Fintype.card {Y : MatY r1 m n' // u ≠ 0 ∧
      u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} : ℝ) ≤ (Fintype.card (MatY r1 m n') : ℝ) * (1 / 2) ^ n' := by
    intro u
    by_cases hu0 : u = 0
    · have : IsEmpty {Y : MatY r1 m n' // u ≠ 0 ∧ u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} :=
        ⟨fun Y => Y.2.1 hu0⟩
      rw [Fintype.card_eq_zero]; push_cast; positivity
    · have e : Fintype.card {Y : MatY r1 m n' // u ≠ 0 ∧ u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} =
          Fintype.card {Y : MatY r1 m n' // u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun Y => by simp [hu0])
      rw [e]; exact hu u hu0
  calc (Fintype.card (Matrix (Fin r2) (Fin n') F2) : ℝ) *
        (Fintype.card {Y : MatY r1 m n' // ∃ u : Fin r1 ⊕ Fin m → F2, u ≠ 0 ∧
          u ᵥ* Matrix.fromRows Y.1 Y.2 = 0} : ℝ)
      ≤ (Fintype.card (Matrix (Fin r2) (Fin n') F2) : ℝ) *
          ∑ _u : Fin r1 ⊕ Fin m → F2, (Fintype.card (MatY r1 m n') : ℝ) * (1 / 2) ^ n' := by
        gcongr
        exact hunion.trans (Finset.sum_le_sum fun u _ => hterm u)
    _ = (Fintype.card (Omega r1 r2 m n') : ℝ) * ((2 : ℝ) ^ (r1 + m) * (1 / 2) ^ n') := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin, ZMod.card, Fintype.card_prod (Matrix (Fin r2) (Fin n') F2)]
        push_cast; ring

/-- **Existence of good codes** by the union bound. -/
theorem exists_goodCode (h : r2 + n' = n)
    (hcond : ((lowSet n w).card : ℝ) * ((1 / 2 : ℝ) ^ r2 + (1 / 2) ^ n' + (1 / 2) ^ r1) +
      (2 : ℝ) ^ (r1 + m) * (1 / 2) ^ n' < 1) :
    Nonempty (GoodCode n r1 r2 m w) := by
  classical
  let P1 : (Fin n → F2) → Omega r1 r2 m n' → Prop := fun v ω => H2C h ω.1 *ᵥ v = 0
  let P2 : (Fin n → F2) → Omega r1 r2 m n' → Prop := fun v ω => phiC h ω.1 *ᵥ v = 0
  let P3 : (Fin n → F2) → Omega r1 r2 m n' → Prop := fun v ω =>
    phiC h ω.1 *ᵥ v ≠ 0 ∧ ω.2.1 *ᵥ (phiC h ω.1 *ᵥ v) = 0
  let P4 : Omega r1 r2 m n' → Prop := fun ω => ∃ u : Fin r1 ⊕ Fin m → F2, u ≠ 0 ∧
    u ᵥ* Matrix.fromRows ω.2.1 ω.2.2 = 0
  let Bad : Omega r1 r2 m n' → Prop := fun ω =>
    (∃ v ∈ lowSet n w, P1 v ω ∨ P2 v ω ∨ P3 v ω) ∨ P4 ω
  have hsub : (Finset.univ.filter Bad) ⊆
      ((lowSet n w).biUnion fun v => Finset.univ.filter (P1 v) ∪ Finset.univ.filter (P2 v) ∪
        Finset.univ.filter (P3 v)) ∪ Finset.univ.filter P4 := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bad] at hω
    rcases hω with ⟨v, hv, hP⟩ | hP
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩)
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩)
  have hOmega : (0 : ℝ) < Fintype.card (Omega r1 r2 m n') := by exact_mod_cast Fintype.card_pos
  have hbad : ((Finset.univ.filter Bad).card : ℝ) < Fintype.card (Omega r1 r2 m n') := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((lowSet n w).biUnion fun v => Finset.univ.filter (P1 v) ∪
      Finset.univ.filter (P2 v) ∪ Finset.univ.filter (P3 v)) (Finset.univ.filter P4)
    have h3 := Finset.card_biUnion_le (s := lowSet n w) (t := fun v => Finset.univ.filter (P1 v) ∪
      Finset.univ.filter (P2 v) ∪ Finset.univ.filter (P3 v))
    have h4 : ∀ v ∈ lowSet n w, ((Finset.univ.filter (P1 v) ∪ Finset.univ.filter (P2 v) ∪
        Finset.univ.filter (P3 v)).card : ℝ) ≤ (Fintype.card (Omega r1 r2 m n') : ℝ) *
          ((1 / 2 : ℝ) ^ r2 + (1 / 2) ^ n' + (1 / 2) ^ r1) := by
      intro v hv
      have hv0 : v ≠ 0 := (Finset.mem_filter.mp hv).2.1
      have a1 := card_E1_le (r1 := r1) (m := m) h hv0
      have a2 := card_E2_le (r1 := r1) (m := m) h hv0
      have a3 := card_E3_le (r1 := r1) (m := m) h v
      rw [Fintype.card_subtype] at a1 a2 a3
      have u1 := Finset.card_union_le (Finset.univ.filter (P1 v) ∪ Finset.univ.filter (P2 v))
        (Finset.univ.filter (P3 v))
      have u2 := Finset.card_union_le (Finset.univ.filter (P1 v)) (Finset.univ.filter (P2 v))
      have : ((Finset.univ.filter (P1 v) ∪ Finset.univ.filter (P2 v) ∪
          Finset.univ.filter (P3 v)).card : ℝ) ≤ (Finset.univ.filter (P1 v)).card +
            (Finset.univ.filter (P2 v)).card + (Finset.univ.filter (P3 v)).card := by
        exact_mod_cast u1.trans (by omega)
      refine this.trans ?_
      have e1 : (Finset.univ.filter (P1 v)).card =
          (Finset.univ.filter fun ω : Omega r1 r2 m n' => H2C h ω.1 *ᵥ v = 0).card := rfl
      have e2 : (Finset.univ.filter (P2 v)).card =
          (Finset.univ.filter fun ω : Omega r1 r2 m n' => phiC h ω.1 *ᵥ v = 0).card := rfl
      have e3 : (Finset.univ.filter (P3 v)).card =
          (Finset.univ.filter fun ω : Omega r1 r2 m n' =>
            phiC h ω.1 *ᵥ v ≠ 0 ∧ ω.2.1 *ᵥ (phiC h ω.1 *ᵥ v) = 0).card := rfl
      rw [e1, e2, e3]
      linarith
    have h5 := card_E4_le (r1 := r1) (r2 := r2) (m := m) (n' := n')
    rw [Fintype.card_subtype] at h5
    have e4 : (Finset.univ.filter P4).card = (Finset.univ.filter fun ω : Omega r1 r2 m n' =>
        ∃ u : Fin r1 ⊕ Fin m → F2, u ≠ 0 ∧ u ᵥ* Matrix.fromRows ω.2.1 ω.2.2 = 0).card := rfl
    have hsum : (∑ v ∈ lowSet n w, ((Finset.univ.filter (P1 v) ∪ Finset.univ.filter (P2 v) ∪
        Finset.univ.filter (P3 v)).card : ℝ)) ≤ ((lowSet n w).card : ℝ) *
          ((Fintype.card (Omega r1 r2 m n') : ℝ) *
            ((1 / 2 : ℝ) ^ r2 + (1 / 2) ^ n' + (1 / 2) ^ r1)) := by
      calc (∑ v ∈ lowSet n w, ((Finset.univ.filter (P1 v) ∪ Finset.univ.filter (P2 v) ∪
          Finset.univ.filter (P3 v)).card : ℝ))
          ≤ ∑ _v ∈ lowSet n w, ((Fintype.card (Omega r1 r2 m n') : ℝ) *
              ((1 / 2 : ℝ) ^ r2 + (1 / 2) ^ n' + (1 / 2) ^ r1)) := Finset.sum_le_sum h4
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.univ.filter Bad).card : ℝ) ≤
        (∑ v ∈ lowSet n w, ((Finset.univ.filter (P1 v) ∪ Finset.univ.filter (P2 v) ∪
          Finset.univ.filter (P3 v)).card : ℝ)) + (Finset.univ.filter P4).card := by
      rw [← Nat.cast_sum]
      exact_mod_cast h1.trans (h2.trans (by omega))
    rw [e4] at this
    calc ((Finset.univ.filter Bad).card : ℝ)
        ≤ ((lowSet n w).card : ℝ) * ((Fintype.card (Omega r1 r2 m n') : ℝ) *
            ((1 / 2 : ℝ) ^ r2 + (1 / 2) ^ n' + (1 / 2) ^ r1)) +
          (Fintype.card (Omega r1 r2 m n') : ℝ) * ((2 : ℝ) ^ (r1 + m) * (1 / 2) ^ n') := by
          linarith
      _ = (Fintype.card (Omega r1 r2 m n') : ℝ) * (((lowSet n w).card : ℝ) *
            ((1 / 2 : ℝ) ^ r2 + (1 / 2) ^ n' + (1 / 2) ^ r1) + (2 : ℝ) ^ (r1 + m) * (1 / 2) ^ n') := by
          ring
      _ < (Fintype.card (Omega r1 r2 m n') : ℝ) * 1 := mul_lt_mul_of_pos_left hcond hOmega
      _ = _ := mul_one _
  obtain ⟨ω, hω⟩ : ∃ ω, ¬ Bad ω := by
    by_contra hall
    rw [not_exists] at hall
    have hall' : ∀ ω, Bad ω := fun ω => not_not.mp (hall ω)
    have : (Finset.univ.filter Bad) = Finset.univ := by
      ext ω; simp [hall' ω]
    rw [this, Finset.card_univ] at hbad
    exact lt_irrefl _ hbad
  obtain ⟨C, Y1, YK⟩ := ω
  simp only [Bad, not_or, not_exists, not_and] at hω
  obtain ⟨hω1, hω4⟩ := hω
  have hlow : ∀ v : Fin n → F2, v ≠ 0 → wt v ≤ 2 * w → v ∈ lowSet n w := fun v h1 h2 =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
  have hinj2 : ∀ v : Fin n → F2, v ≠ 0 → wt v ≤ 2 * w → H2C h C *ᵥ v ≠ 0 := fun v h1 h2 h0 =>
    (hω1 v (hlow v h1 h2)).1 h0
  have hinj1 : ∀ v : Fin n → F2, v ≠ 0 → wt v ≤ 2 * w → (Y1 * phiC h C) *ᵥ v ≠ 0 := by
    intro v h1 h2 h0
    rw [← Matrix.mulVec_mulVec] at h0
    by_cases hphi : phiC h C *ᵥ v = 0
    · exact (hω1 v (hlow v h1 h2)).2.1 hphi
    · exact (hω1 v (hlow v h1 h2)).2.2 ⟨hphi, h0⟩
  have hsurj := mulVec_surjective (Matrix.fromRows Y1 YK) (fun u hu => by
    by_contra hu0; exact hω4 ⟨u, hu0, hu⟩)
  have hy : ∀ k : Fin m → F2, ∃ y : Fin n' → F2, Y1 *ᵥ y = 0 ∧ YK *ᵥ y = k := by
    intro k
    obtain ⟨y, hy⟩ := hsurj (Sum.elim 0 k)
    refine ⟨y, ?_, ?_⟩
    · funext i; have := congrFun hy (Sum.inl i); simpa [Matrix.fromRows_mulVec] using this
    · funext i; have := congrFun hy (Sum.inr i); simpa [Matrix.fromRows_mulVec] using this
  refine ⟨{
    H1 := Y1 * phiC h C
    K := YK * phiC h C
    H2 := H2C h C
    dec := fun σ => if hh : ∃ X' : Fin n → F2, wt X' ≤ w ∧ (Y1 * phiC h C) *ᵥ X' = σ then
      Classical.choose hh else 0
    zdec := fun σ => if hh : ∃ X' : Fin n → F2, wt X' ≤ w ∧ H2C h C *ᵥ X' = σ then
      Classical.choose hh else 0
    tk := fun k => glue h 0 (Classical.choose (hy k))
    dec_spec := fun X hX => decode_spec _ hinj1 X hX
    zdec_spec := fun Z hZ => decode_spec _ hinj2 Z hZ
    tk_H1 := fun k => by
      rw [← Matrix.mulVec_mulVec, phiC_glue_zero]; exact (Classical.choose_spec (hy k)).1
    tk_K := fun k => by
      rw [← Matrix.mulVec_mulVec, phiC_glue_zero]; exact (Classical.choose_spec (hy k)).2
    orth_H1 := fun u => by
      rw [← Matrix.mulVec_mulVec, vecMul_H2C, phiC_glue_orth, Matrix.mulVec_zero]
    orth_K := fun u => by
      rw [← Matrix.mulVec_mulVec, vecMul_H2C, phiC_glue_orth, Matrix.mulVec_zero] }⟩

end Existence

end NPK

end Mod_NPK_Codes

section Mod_NPK_Quantum
/-!
# Generic quantum lemmas for the key-distillation analysis
-/

open QAlgorithms
open scoped Matrix ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

section Psd

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_re_nonneg_of_psd {X : Matrix ι ι ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

open scoped MatrixOrder in
lemma trace_mul_psd_nonneg {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  exact trace_re_nonneg_of_psd (by
    have := hB.mul_mul_conjTranspose_same C
    simpa [Matrix.mul_assoc] using this)

lemma traceNorm_psd {X : Matrix ι ι ℂ} (h : X.PosSemidef) : traceNorm X = X.trace.re := by
  unfold traceNorm
  rw [h.isHermitian.eq, cfc_sqrt_mul_self h]

end Psd

section Core

variable {In Out G J : Type*} [Fintype In] [Fintype Out] [Fintype G] [Fintype J]
  [DecidableEq In] [DecidableEq Out] [DecidableEq G]

/-- **Virtual decoding bound.** If the projector `P` contains the images of all "good" input
vectors (the columns of the isometry `B`) under every Kraus operator, then the weight of the
channel output on `P` is at least the weight of the input on the good subspace. -/
theorem fidelity_ge (B : Matrix In G ℂ) (hB : Bᴴ * B = 1) (K : J → Matrix Out In ℂ)
    (hK : ∑ j, (K j)ᴴ * K j = 1) (P : Matrix Out Out ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hgood : ∀ j, P * K j * B = K j * B) (ρ : Matrix In In ℂ) (hρ : ρ.PosSemidef) :
    (B * Bᴴ * ρ).trace.re ≤ (P * ∑ j, K j * ρ * (K j)ᴴ).trace.re := by
  classical
  set Q := ∑ j, (K j)ᴴ * P * K j with hQ
  have htr : (P * ∑ j, K j * ρ * (K j)ᴴ).trace = (Q * ρ).trace := by
    rw [Matrix.mul_sum, Matrix.trace_sum, hQ, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show P * (K j * ρ * (K j)ᴴ) = (P * K j * ρ) * (K j)ᴴ by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hQB : Q * B = B := by
    rw [hQ, Matrix.sum_mul]
    have : ∀ j, (K j)ᴴ * P * K j * B = (K j)ᴴ * K j * B := by
      intro j
      rw [Matrix.mul_assoc ((K j)ᴴ * P), show (K j)ᴴ * P * (K j * B) = (K j)ᴴ * (P * K j * B) by
        simp only [Matrix.mul_assoc], hgood j, ← Matrix.mul_assoc]
    simp only [this, ← Matrix.sum_mul, hK, Matrix.one_mul]
  have hQh : Qᴴ = Q := by
    rw [hQ, conjTranspose_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]
  have hBQ : Bᴴ * Q = Bᴴ := by
    have := congrArg Matrix.conjTranspose hQB
    rwa [conjTranspose_mul, hQh] at this
  have hQpsd : Q.PosSemidef := by
    rw [hQ]
    refine Matrix.posSemidef_sum _ fun j _ => ?_
    have : (K j)ᴴ * P * K j = (P * K j)ᴴ * (P * K j) := by
      rw [conjTranspose_mul, hP]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P (K j), hPP]
    rw [this]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hdecomp : Q - B * Bᴴ = (1 - B * Bᴴ) * Q * (1 - B * Bᴴ) := by
    have e1 : B * Bᴴ * Q = B * Bᴴ := by rw [Matrix.mul_assoc, hBQ]
    have e2 : Q * (B * Bᴴ) = B * Bᴴ := by rw [← Matrix.mul_assoc, hQB]
    have e4 : B * Bᴴ * (B * Bᴴ) = B * Bᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, hB, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.one_mul, e1, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, e2, e4]
    abel
  have hpsd : (Q - B * Bᴴ).PosSemidef := by
    rw [hdecomp]
    have := hQpsd.mul_mul_conjTranspose_same (1 - B * Bᴴ)
    convert this using 2
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  have h0 := trace_mul_psd_nonneg hpsd hρ
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at h0
  rw [htr]
  linarith

end Core

section Gentle

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Cauchy–Schwarz for the Hilbert–Schmidt pairing, real part. -/
lemma re_trace_cs (Y Z : Matrix ι ι ℂ) :
    (Yᴴ * Z).trace.re ^ 2 ≤ (Yᴴ * Y).trace.re * (Zᴴ * Z).trace.re := by
  have hq : ∀ x : ℝ, 0 ≤ (Yᴴ * Y).trace.re * (x * x) + (-2 * (Yᴴ * Z).trace.re) * x +
      (Zᴴ * Z).trace.re := by
    intro x
    have h := trace_re_nonneg_of_psd (Matrix.posSemidef_conjTranspose_mul_self ((x : ℂ) • Y - Z))
    have hsym : (Zᴴ * Y).trace.re = (Yᴴ * Z).trace.re := by
      rw [show Zᴴ * Y = (Yᴴ * Z)ᴴ by rw [conjTranspose_mul, conjTranspose_conjTranspose],
        trace_conjTranspose]
      simp
    simp only [conjTranspose_sub, conjTranspose_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hsym] at h
    nlinarith
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

lemma traceNorm_sandwich_le (P Q ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (hP : Pᴴ = P)
    (hQ : Qᴴ = Q) :
    traceNorm (P * ρ * Q) ≤ Real.sqrt ((P * ρ * P).trace.re * (Q * ρ * Q).trace.re) := by
  obtain ⟨V, hV, he⟩ := traceNorm_eq_polar (P * ρ * Q)
  set R := cfc Real.sqrt ρ with hR
  have hRh : Rᴴ = R := sqrt_herm ρ
  have hRR : R * R = ρ := sqrt_sq hρ
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  set Y := R * P * Vᴴ
  set Z := R * Q
  have h1 : (V * (P * ρ * Q)).trace = (Yᴴ * Z).trace := by
    simp only [Y, Z, conjTranspose_mul, conjTranspose_conjTranspose, hRh, hP]
    rw [← hRR]
    simp only [Matrix.mul_assoc]
  have h2 : (Yᴴ * Y).trace.re = (P * ρ * P).trace.re := by
    simp only [Y, conjTranspose_mul, conjTranspose_conjTranspose, hRh, hP]
    rw [show V * (P * R) * (R * P * Vᴴ) = V * (P * (R * R) * P) * Vᴴ by
      simp only [Matrix.mul_assoc], hRR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV,
      Matrix.one_mul]
  have h3 : (Zᴴ * Z).trace.re = (Q * ρ * Q).trace.re := by
    simp only [Z, conjTranspose_mul, hRh, hQ]
    rw [show Q * R * (R * Q) = Q * (R * R) * Q by simp only [Matrix.mul_assoc], hRR]
  rw [he, h1]
  have hcs := re_trace_cs Y Z
  rw [h2, h3] at hcs
  exact Real.le_sqrt_of_sq_le hcs

/-- **Gentle measurement.** -/
theorem gentle (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) (P : Matrix ι ι ℂ) (hP : Pᴴ = P)
    (hPP : P * P = P) (ht : 0 < (P * ρ).trace.re) :
    traceNorm (ρ - ((1 / (P * ρ).trace.re : ℝ) : ℂ) • (P * ρ * P)) ≤
      2 * Real.sqrt (1 - (P * ρ).trace.re) + 2 * (1 - (P * ρ).trace.re) := by
  set t := (P * ρ).trace.re with htdef
  set Q := 1 - P with hQdef
  have hQ : Qᴴ = Q := by rw [hQdef, conjTranspose_sub, conjTranspose_one, hP]
  have hQQ : Q * Q = Q := by
    rw [hQdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hPP]; abel
  have hPρP : (P * ρ * P).trace.re = t := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPP]
  have hQρQ : (Q * ρ * Q).trace.re = 1 - t := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQQ, hQdef, Matrix.sub_mul, Matrix.one_mul,
      Matrix.trace_sub, Complex.sub_re, hρ.2, Complex.one_re]
  have ht1 : t ≤ 1 := by
    have := trace_re_nonneg_of_psd (hρ.1.mul_mul_conjTranspose_same Q)
    rw [hQ] at this
    linarith
  have hρdec : ρ = P * ρ * P + P * ρ * Q + Q * ρ * P + Q * ρ * Q := by
    have hPQ : P + Q = 1 := by rw [hQdef]; abel
    calc ρ = (P + Q) * ρ * (P + Q) := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.add_mul, Matrix.mul_add]; abel
  have hsplit : ρ - ((1 / t : ℝ) : ℂ) • (P * ρ * P) =
      P * ρ * Q + Q * ρ * P + Q * ρ * Q - ((1 / t - 1 : ℝ) : ℂ) • (P * ρ * P) := by
    nth_rewrite 1 [hρdec]
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  rw [hsplit]
  have hb1 := traceNorm_sandwich_le P Q ρ hρ.1 hP hQ
  have hb2 := traceNorm_sandwich_le Q P ρ hρ.1 hQ hP
  rw [hPρP, hQρQ] at hb1 hb2
  have hb3 : traceNorm (Q * ρ * Q) = 1 - t := by
    rw [traceNorm_psd (by simpa [hQ] using hρ.1.mul_mul_conjTranspose_same Q), hQρQ]
  have hb4 : traceNorm (((1 / t - 1 : ℝ) : ℂ) • (P * ρ * P)) ≤ 1 - t := by
    refine (traceNorm_smul_le _ (by rw [sub_nonneg, le_div_iff₀ ht]; linarith) _).trans ?_
    rw [traceNorm_psd (by simpa [hP] using hρ.1.mul_mul_conjTranspose_same P), hPρP]
    field_simp
    linarith
  have hsq : Real.sqrt (t * (1 - t)) ≤ Real.sqrt (1 - t) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsq' : Real.sqrt ((1 - t) * t) ≤ Real.sqrt (1 - t) :=
    Real.sqrt_le_sqrt (by nlinarith)
  calc traceNorm (P * ρ * Q + Q * ρ * P + Q * ρ * Q - ((1 / t - 1 : ℝ) : ℂ) • (P * ρ * P))
      ≤ traceNorm (P * ρ * Q + Q * ρ * P + Q * ρ * Q) +
          traceNorm (((1 / t - 1 : ℝ) : ℂ) • (P * ρ * P)) := traceNorm_sub_le _ _
    _ ≤ (traceNorm (P * ρ * Q) + traceNorm (Q * ρ * P) + traceNorm (Q * ρ * Q)) +
          traceNorm (((1 / t - 1 : ℝ) : ℂ) • (P * ρ * P)) := by
        gcongr
        exact (traceNorm_add_le _ _).trans (add_le_add (traceNorm_add_le _ _) le_rfl)
    _ ≤ 2 * Real.sqrt (1 - t) + 2 * (1 - t) := by linarith

end Gentle

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma traceNorm_submatrix_le (M : Matrix κ κ ℂ) (e : ι ≃ κ) :
    traceNorm (M.submatrix e e) ≤ traceNorm M := by
  obtain ⟨V, hV, he⟩ := traceNorm_eq_polar (M.submatrix e e)
  rw [he]
  have hV' : (V.submatrix e.symm e.symm)ᴴ * V.submatrix e.symm e.symm = 1 := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv, hV, submatrix_one_equiv]
  refine le_trans (le_of_eq ?_) (re_tr_unitary_mul_le _ M hV')
  congr 1
  have : V * M.submatrix e e = (V.submatrix e.symm e.symm * M).submatrix e e := by
    rw [← submatrix_mul_equiv (V.submatrix e.symm e.symm) M e e e]
    simp
  rw [this, FKR.trace_submatrix_equiv]

lemma traceNorm_submatrix_equiv (M : Matrix κ κ ℂ) (e : ι ≃ κ) :
    traceNorm (M.submatrix e e) = traceNorm M := by
  refine le_antisymm (traceNorm_submatrix_le M e) ?_
  have := traceNorm_submatrix_le (M.submatrix e e) e.symm
  simpa using this

end Reindex

end NPK

end Mod_NPK_Quantum

section Mod_NPK_Bell
/-!
# Twisted Bell vectors

For a family of shield unitaries `U_{(a,b)}` (a *twisting*), the twisted Bell vectors of one copy
are `β_{x,z,f} = 2^{-1/2} Σ_a χ(a z) |a, a+x⟩ ⊗ U_{(a,a+x)} |f⟩`. They form an orthonormal basis,
and on `n` copies they are tensor products.
-/

open QAlgorithms
open scoped Matrix ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

/-! ### Tensor vectors -/

section TVec

variable {τ κ : Type} [Fintype τ] [DecidableEq τ] [Fintype κ]

/-- Tensor product of a family of vectors. -/
def tvec (v : τ → κ → ℂ) : (τ → κ) → ℂ := fun x => ∏ t, v t (x t)

lemma tvec_form (v w : τ → κ → ℂ) (M : τ → Matrix κ κ ℂ) :
    star (tvec v) ⬝ᵥ (tpow M *ᵥ tvec w) = ∏ t, star (v t) ⬝ᵥ (M t *ᵥ w t) := by
  simp only [dotProduct, Matrix.mulVec, tvec, tpow, Pi.star_apply, star_prod, Finset.mul_sum]
  have e : ∀ x y : τ → κ, (∏ t, star (v t (x t))) * ((∏ t, M t (x t) (y t)) * ∏ t, w t (y t)) =
      ∏ t, (star (v t (x t)) * (M t (x t) (y t) * w t (y t))) := by
    intro x y
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp only [e]
  have e1 : ∀ x : τ → κ, ∑ y : τ → κ, ∏ t, (star (v t (x t)) * (M t (x t) (y t) * w t (y t))) =
      ∏ t, ∑ b : κ, star (v t (x t)) * (M t (x t) b * w t b) := fun x =>
    (Fintype.prod_sum (fun (t : τ) (b : κ) => star (v t (x t)) * (M t (x t) b * w t b))).symm
  simp only [e1]
  rw [← Fintype.prod_sum (fun (t : τ) (a : κ) => ∑ b : κ, star (v t a) * (M t a b * w t b))]

lemma tvec_inner (v w : τ → κ → ℂ) :
    star (tvec v) ⬝ᵥ tvec w = ∏ t, star (v t) ⬝ᵥ w t := by
  simp only [dotProduct, tvec, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (t : τ) (a : κ) => star (v t a) * w t a)).symm

end TVec

/-- Trace from a complete family of vectors. -/
lemma sum_quad_complete {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Bm : Matrix ι κ ℂ) (hB : Bm * Bmᴴ = 1) (σ : Matrix ι ι ℂ) :
    ∑ k, star (fun i => Bm i k) ⬝ᵥ (σ *ᵥ fun i => Bm i k) = σ.trace := by
  have : ∀ k, star (fun i => Bm i k) ⬝ᵥ (σ *ᵥ fun i => Bm i k) = (Bmᴴ * σ * Bm) k k := by
    intro k
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.mul_apply, conjTranspose_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [this]
  rw [show ∑ k, (Bmᴴ * σ * Bm) k k = (Bmᴴ * σ * Bm).trace from rfl, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hB, Matrix.one_mul]

/-! ### One copy -/

section One

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
variable (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ)

abbrev Cell (S T : Type) := (F2 × F2) × (S × T)

noncomputable def c2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma c2_sq : c2 * c2 = 1 / 2 := by
  unfold c2
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

lemma star_c2 : star c2 = c2 := by
  unfold c2; simp [Complex.conj_ofReal]

/-- The per-copy twisted Bell vector `β_{x,z,f}`. -/
noncomputable def bell1 (x z : F2) (f : S × T) : Cell S T → ℂ :=
  fun p => if p.1.2 = p.1.1 + x then c2 * chi (p.1.1 * z) * Uc p.1 p.2 f else 0

variable {Uc}

lemma sum_cell {M : Type*} [AddCommMonoid M] (g : Cell S T → M) :
    ∑ p, g p = ∑ a : F2, ∑ b : F2, ∑ s : S × T, g ((a, b), s) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]

lemma bell1_orthonormal (hU : ∀ c, (Uc c)ᴴ * Uc c = 1) (x z x' z' : F2) (f f' : S × T) :
    star (bell1 Uc x z f) ⬝ᵥ bell1 Uc x' z' f' =
      if x = x' ∧ z = z' ∧ f = f' then 1 else 0 := by
  classical
  simp only [dotProduct, Pi.star_apply, bell1]
  rw [sum_cell]
  have hb : ∀ a : F2, ∑ b : F2, ∑ s : S × T,
      star (if b = a + x then c2 * chi (a * z) * Uc (a, b) s f else 0) *
        (if b = a + x' then c2 * chi (a * z') * Uc (a, b) s f' else 0) =
      if x = x' then (1 / 2 : ℂ) * chi (a * (z + z')) * (if f = f' then 1 else 0) else 0 := by
    intro a
    rw [Finset.sum_eq_single (a + x)]
    · by_cases hxx : x = x'
      · subst hxx
        simp only [if_true, star_mul', star_chi, star_c2]
        have : ∑ s : S × T, c2 * chi (a * z) * star (Uc (a, a + x) s f) *
            (c2 * chi (a * z') * Uc (a, a + x) s f') =
            c2 * c2 * (chi (a * z) * chi (a * z')) * ((Uc (a, a + x))ᴴ * Uc (a, a + x)) f f' := by
          simp only [Matrix.mul_apply, conjTranspose_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => by ring
        rw [this, hU, c2_sq, Matrix.one_apply, mul_add, chi_add]
      · have : a + x ≠ a + x' := fun h => hxx (add_left_cancel h)
        simp [this, hxx]
    · intro b _ hb
      simp [hb]
    · simp
  simp only [hb]
  by_cases hxx : x = x'
  · simp only [hxx, true_and, if_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_chi_mul]
    have hzz : z + z' = 0 ↔ z = z' := by
      constructor
      · intro h
        calc z = z + z' + z' := by rw [add_assoc, F2_add_self, add_zero]
          _ = z' := by rw [h, zero_add]
      · rintro rfl; exact F2_add_self z
    by_cases hz : z = z'
    · rw [if_pos (hzz.mpr hz)]
      by_cases hf : f = f' <;> simp [hz, hf]
    · rw [if_neg (fun h => hz (hzz.mp h))]
      simp [hz]
  · simp [hxx]

/-- Completeness: `Σ_{x,z,f} β β† = 𝟙`. -/
lemma bell1_complete (hU' : ∀ c, Uc c * (Uc c)ᴴ = 1) (p q : Cell S T) :
    ∑ x : F2, ∑ z : F2, ∑ f : S × T, bell1 Uc x z f p * star (bell1 Uc x z f q) =
      if p = q then 1 else 0 := by
  classical
  obtain ⟨⟨a, b⟩, s⟩ := p
  obtain ⟨⟨a', b'⟩, s'⟩ := q
  simp only [bell1]
  have hz : ∀ x : F2, ∑ z : F2, ∑ f : S × T,
      (if b = a + x then c2 * chi (a * z) * Uc (a, b) s f else 0) *
        star (if b' = a' + x then c2 * chi (a' * z) * Uc (a', b') s' f else 0) =
      if b = a + x ∧ b' = a' + x ∧ a = a' then (Uc (a, b) * (Uc (a', b'))ᴴ) s s' else 0 := by
    intro x
    by_cases h1 : b = a + x
    · by_cases h2 : b' = a' + x
      · simp only [h1, h2, if_true, true_and, star_mul', star_chi, star_c2]
        have e : ∀ z : F2, ∑ f : S × T, c2 * chi (a * z) * Uc (a, a + x) s f *
            (c2 * chi (a' * z) * star (Uc (a', a' + x) s' f)) =
            (c2 * c2) * chi (z * (a + a')) * (Uc (a, a + x) * (Uc (a', a' + x))ᴴ) s s' := by
          intro z
          simp only [Matrix.mul_apply, conjTranspose_apply, Finset.mul_sum, mul_add, chi_add]
          refine Finset.sum_congr rfl fun f _ => by
            rw [mul_comm z a, mul_comm z a']; ring
        simp only [e]
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_chi_mul, c2_sq]
        have haa : a + a' = 0 ↔ a = a' := by
          constructor
          · intro h
            calc a = a + a' + a' := by rw [add_assoc, F2_add_self, add_zero]
              _ = a' := by rw [h, zero_add]
          · rintro rfl; exact F2_add_self a
        by_cases ha : a = a'
        · rw [if_pos (haa.mpr ha), if_pos ha]; ring
        · rw [if_neg (fun h => ha (haa.mp h)), if_neg ha]; ring
      · simp [h2]
    · simp [h1]
  simp only [hz]
  by_cases hp : ((a, b), s) = ((a', b'), s')
  · simp only [Prod.mk.injEq] at hp
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
    rw [if_pos rfl]
    rw [Finset.sum_eq_single (a + b)]
    · have : b = a + (a + b) := by
        rw [← add_assoc, F2_add_self, zero_add]
      simp only [← this, and_self, if_true, hU', Matrix.one_apply_eq]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨h1, -, -⟩
      apply hx
      rw [h1, ← add_assoc, F2_add_self, zero_add]
    · simp
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs with hc
    · obtain ⟨h1, h2, rfl⟩ := hc
      have hbb : b = b' := by rw [h1, h2]
      subst hbb
      have hss : s ≠ s' := fun h => hp (by rw [h])
      rw [hU', Matrix.one_apply_ne hss]
    · rfl

variable (Uc)

/-- The outcome distribution `p(x,z)` of a state `σ` in the twisted Bell basis. -/
noncomputable def pBell (σ : Matrix (Cell S T) (Cell S T) ℂ) (x z : F2) : ℝ :=
  ∑ f : S × T, (star (bell1 Uc x z f) ⬝ᵥ (σ *ᵥ bell1 Uc x z f)).re

lemma pBell_nonneg {σ : Matrix (Cell S T) (Cell S T) ℂ} (hσ : σ.PosSemidef) (x z : F2) :
    0 ≤ pBell Uc σ x z :=
  Finset.sum_nonneg fun f _ => by
    have := hσ.dotProduct_mulVec_nonneg (bell1 Uc x z f)
    rw [Complex.nonneg_iff] at this
    exact this.1

lemma pBell_sum (hU' : ∀ c, Uc c * (Uc c)ᴴ = 1) {σ : Matrix (Cell S T) (Cell S T) ℂ}
    (hσ : σ.trace = 1) : ∑ x : F2, ∑ z : F2, pBell Uc σ x z = 1 := by
  classical
  let Bm : Matrix (Cell S T) (F2 × F2 × (S × T)) ℂ := Matrix.of fun p k => bell1 Uc k.1 k.2.1 k.2.2 p
  have hB : Bm * Bmᴴ = 1 := by
    ext p q
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [conjTranspose_apply, Bm, Matrix.of_apply]
    rw [Fintype.sum_prod_type, ← bell1_complete hU' p q]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
  have h := sum_quad_complete Bm hB σ
  unfold pBell
  simp only [← Complex.re_sum]
  rw [hσ] at h
  rw [show (∑ x : F2, ∑ z : F2, ∑ f : S × T, star (bell1 Uc x z f) ⬝ᵥ (σ *ᵥ bell1 Uc x z f)) =
      ∑ k : F2 × F2 × (S × T), star (fun i => Bm i k) ⬝ᵥ (σ *ᵥ fun i => Bm i k) by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]; rfl, h, Complex.one_re]

end One

end NPK

end Mod_NPK_Bell

section Mod_NPK_BellN
/-!
# Twisted Bell vectors on `n` copies

The `n`-copy registers are grouped by party: Alice holds `(a, sA) : (Fin n → F₂) × (Fin n → S)`,
Bob holds `(b, sB)`. A label of one copy is `(x, z, f)`; an `n`-copy label is `ℓ : Fin n → Lab`.
-/

open QAlgorithms
open scoped Matrix ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

/-- A party's `n`-copy register: key bits and shields. -/
abbrev AReg (n : ℕ) (S : Type) := (Fin n → F2) × (Fin n → S)

/-- The bipartite `n`-copy register. -/
abbrev InReg (n : ℕ) (S T : Type) := AReg n S × AReg n T

/-- One-copy labels `(x, z, f)`. -/
abbrev Lab (S T : Type) := F2 × F2 × (S × T)

/-- Copy-wise regrouping of the bipartite register. -/
def cw (n : ℕ) (S T : Type) : InReg n S T ≃ (Fin n → Cell S T) where
  toFun p := fun i => ((p.1.1 i, p.2.1 i), (p.1.2 i, p.2.2 i))
  invFun x := ((fun i => (x i).1.1, fun i => (x i).2.1), (fun i => (x i).1.2, fun i => (x i).2.2))
  left_inv p := rfl
  right_inv x := rfl

section N

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
variable {n : ℕ}

/-- One-copy Bell vector of a label. -/
noncomputable def bellL (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) (l : Lab S T) : Cell S T → ℂ :=
  bell1 Uc l.1 l.2.1 l.2.2

/-- `n`-copy twisted Bell vector. -/
noncomputable def bellN (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) (ℓ : Fin n → Lab S T) :
    InReg n S T → ℂ :=
  fun p => tvec (fun i => bellL Uc (ℓ i)) (cw n S T p)

lemma bellN_eq (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) (ℓ : Fin n → Lab S T) :
    bellN Uc ℓ = tvec (fun i => bellL Uc (ℓ i)) ∘ cw n S T := rfl

lemma bellL_orthonormal {Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ} (hU : ∀ c, (Uc c)ᴴ * Uc c = 1)
    (l l' : Lab S T) : star (bellL Uc l) ⬝ᵥ bellL Uc l' = if l = l' then 1 else 0 := by
  obtain ⟨x, z, f⟩ := l
  obtain ⟨x', z', f'⟩ := l'
  unfold bellL
  rw [bell1_orthonormal hU]
  simp only [Prod.mk.injEq]

lemma bellN_orthonormal {Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ} (hU : ∀ c, (Uc c)ᴴ * Uc c = 1)
    (ℓ ℓ' : Fin n → Lab S T) :
    star (bellN Uc ℓ) ⬝ᵥ bellN Uc ℓ' = if ℓ = ℓ' then 1 else 0 := by
  classical
  rw [bellN_eq, bellN_eq, show star (tvec (fun i => bellL Uc (ℓ i)) ∘ cw n S T) =
    star (tvec (fun i => bellL Uc (ℓ i))) ∘ cw n S T from rfl, comp_equiv_dotProduct_comp_equiv,
    tvec_inner]
  simp only [bellL_orthonormal hU]
  by_cases h : ℓ = ℓ'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The `n`-fold power of a one-copy state in the bipartite layout. -/
def powN (σ : Matrix (Cell S T) (Cell S T) ℂ) : Matrix (InReg n S T) (InReg n S T) ℂ :=
  (tpow (fun _ : Fin n => σ)).submatrix (cw n S T) (cw n S T)

lemma bellN_form (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) (σ : Matrix (Cell S T) (Cell S T) ℂ)
    (ℓ : Fin n → Lab S T) :
    star (bellN Uc ℓ) ⬝ᵥ (powN σ *ᵥ bellN Uc ℓ) =
      ∏ i, star (bellL Uc (ℓ i)) ⬝ᵥ (σ *ᵥ bellL Uc (ℓ i)) := by
  unfold powN
  rw [bellN_eq, submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
    Function.comp_id, show star (tvec (fun i => bellL Uc (ℓ i)) ∘ cw n S T) =
    star (tvec (fun i => bellL Uc (ℓ i))) ∘ cw n S T from rfl, comp_equiv_dotProduct_comp_equiv,
    tvec_form]

/-- The weight of a one-copy label: `μ(x,z,f) = ⟨β_{xzf}, σ β_{xzf}⟩`. -/
noncomputable def mu (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) (σ : Matrix (Cell S T) (Cell S T) ℂ)
    (l : Lab S T) : ℝ :=
  (star (bellL Uc l) ⬝ᵥ (σ *ᵥ bellL Uc l)).re

lemma quad_real {ι : Type} [Fintype ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (v : ι → ℂ) :
    star v ⬝ᵥ (σ *ᵥ v) = ((star v ⬝ᵥ (σ *ᵥ v)).re : ℂ) := by
  have h := hσ.dotProduct_mulVec_nonneg v
  rw [Complex.nonneg_iff] at h
  apply Complex.ext
  · simp
  · simp [← h.2]

lemma mu_nonneg (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) {σ : Matrix (Cell S T) (Cell S T) ℂ}
    (hσ : σ.PosSemidef) (l : Lab S T) : 0 ≤ mu Uc σ l := by
  have h := hσ.dotProduct_mulVec_nonneg (bellL Uc l)
  rw [Complex.nonneg_iff] at h
  exact h.1

lemma mu_sum {Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ} (hU' : ∀ c, Uc c * (Uc c)ᴴ = 1)
    {σ : Matrix (Cell S T) (Cell S T) ℂ} (hσ : σ.trace = 1) : ∑ l, mu Uc σ l = 1 := by
  rw [← pBell_sum Uc hU' hσ]
  unfold mu pBell bellL
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]

lemma bellN_quad_re (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) {σ : Matrix (Cell S T) (Cell S T) ℂ}
    (hσ : σ.PosSemidef) (ℓ : Fin n → Lab S T) :
    (star (bellN Uc ℓ) ⬝ᵥ (powN σ *ᵥ bellN Uc ℓ)).re = ∏ i, mu Uc σ (ℓ i) := by
  rw [bellN_form]
  have e : ∀ i, star (bellL Uc (ℓ i)) ⬝ᵥ (σ *ᵥ bellL Uc (ℓ i)) = ((mu Uc σ (ℓ i) : ℝ) : ℂ) :=
    fun i => quad_real hσ _
  simp only [e]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

/-! ### Twistings depending on Alice's key bit only -/

/-- The twisting `U_{(a,b)} = V_a`. -/
def Ua (V : F2 → Matrix (S × T) (S × T) ℂ) : F2 × F2 → Matrix (S × T) (S × T) ℂ := fun c => V c.1

/-- Shield pair of `n` copies. -/
abbrev Sh (n : ℕ) (S T : Type) := (Fin n → S) × (Fin n → T)

/-- The `n`-copy shield twisting `⊗ᵢ V_{aᵢ}` in the grouped shield layout. -/
def Vn (V : F2 → Matrix (S × T) (S × T) ℂ) (a : Fin n → F2) : Matrix (Sh n S T) (Sh n S T) ℂ :=
  fun x y => ∏ i, V (a i) (x.1 i, x.2 i) (y.1 i, y.2 i)

lemma Vn_eq (V : F2 → Matrix (S × T) (S × T) ℂ) (a : Fin n → F2) :
    Vn V a = (tpow (fun i => V (a i))).submatrix (pairE S T) (pairE S T) := rfl

lemma Vn_conj_mul {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (a : Fin n → F2) : (Vn V a)ᴴ * Vn V a = 1 := by
  rw [Vn_eq, conjTranspose_submatrix, submatrix_mul_equiv, tpow_conjTranspose, tpow_mul]
  simp only [hV]
  rw [tpow_one, submatrix_one_equiv]

lemma Vn_mul_conj {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (a : Fin n → F2) : Vn V a * (Vn V a)ᴴ = 1 :=
  mul_eq_one_comm.mp (Vn_conj_mul hV a)

/-- Shield labels of an `n`-copy label. -/
def shL (ℓ : Fin n → Lab S T) : Sh n S T := (fun i => (ℓ i).2.2.1, fun i => (ℓ i).2.2.2)

/-- Bit-error pattern of a label. -/
def xL (ℓ : Fin n → Lab S T) : Fin n → F2 := fun i => (ℓ i).1

/-- Phase-error pattern of a label. -/
def zL (ℓ : Fin n → Lab S T) : Fin n → F2 := fun i => (ℓ i).2.1

lemma bellN_closed (V : F2 → Matrix (S × T) (S × T) ℂ) (ℓ : Fin n → Lab S T) (p : InReg n S T) :
    bellN (Ua V) ℓ p = if p.2.1 = p.1.1 + xL ℓ then
      c2 ^ n * chi (p.1.1 ⬝ᵥ zL ℓ) * Vn V p.1.1 (p.1.2, p.2.2) (shL ℓ) else 0 := by
  classical
  unfold bellN tvec bellL bell1 Ua
  simp only [cw, Equiv.coe_fn_mk]
  split_ifs with h
  · have hi : ∀ i, p.2.1 i = p.1.1 i + (ℓ i).1 := fun i => congrFun h i
    simp only [hi, if_true]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    · congr 1
      unfold dotProduct zL
      rw [chi_sum]
  · obtain ⟨i, hi⟩ : ∃ i, p.2.1 i ≠ p.1.1 i + (ℓ i).1 := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma Ua_conj_mul {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1) (c : F2 × F2) :
    (Ua V c)ᴴ * Ua V c = 1 := hV c.1

lemma Ua_mul_conj {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1) (c : F2 × F2) :
    Ua V c * (Ua V c)ᴴ = 1 := mul_eq_one_comm.mp (hV c.1)

end N

end NPK

end Mod_NPK_BellN

section Mod_NPK_Squeeze
/-!
# Privacy squeezing

With the twisting `V₀ = 𝟙`, `V₁ = W`, the twisted-Bell distribution of a state `σ` satisfies
`p(0,0) - p(0,1) = 2 Re Tr(W X)` where `X = ⟨00|σ|11⟩`. Choosing `W` from the polar
decomposition of `X` gives `p(0,0) ≥ 2‖X‖₁`.
-/

open QAlgorithms
open scoped Matrix ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

section Sq

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

/-- The squeezing twist `V₀ = 𝟙`, `V₁ = W`. -/
def Vsq (W : Matrix (S × T) (S × T) ℂ) : F2 → Matrix (S × T) (S × T) ℂ :=
  fun a => if a = 0 then 1 else W

lemma Vsq_zero (W : Matrix (S × T) (S × T) ℂ) : Vsq W 0 = 1 := by simp [Vsq]

lemma Vsq_one (W : Matrix (S × T) (S × T) ℂ) : Vsq W 1 = W := by simp [Vsq]

lemma Vsq_unitary {W : Matrix (S × T) (S × T) ℂ} (hW : Wᴴ * W = 1) (c : F2) :
    (Vsq W c)ᴴ * Vsq W c = 1 := by
  rcases F2_cases c with rfl | rfl
  · simp [Vsq_zero]
  · rw [Vsq_one]; exact hW

/-- The corner block `X = ⟨00|σ|11⟩`. -/
def corner (σ : Matrix (Cell S T) (Cell S T) ℂ) : Matrix (S × T) (S × T) ℂ :=
  fun s t => σ ((0, 0), s) ((1, 1), t)

lemma sum_cell_diag (g : Cell S T → ℂ) (hg : ∀ p : Cell S T, p.1.2 ≠ p.1.1 → g p = 0) :
    ∑ p, g p = ∑ a : F2, ∑ s : S × T, g ((a, a), s) := by
  rw [sum_cell (M := ℂ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · intro b _ hb
    exact Finset.sum_eq_zero fun s _ => hg _ hb
  · simp

lemma bell1_zero_diag (V : F2 → Matrix (S × T) (S × T) ℂ) (z : F2) (f : S × T) (a : F2)
    (s : S × T) : bell1 (Ua V) 0 z f ((a, a), s) = c2 * chi (a * z) * V a s f := by
  simp [bell1, Ua]

lemma bell1_zero_off (V : F2 → Matrix (S × T) (S × T) ℂ) (z : F2) (f : S × T) (p : Cell S T)
    (hp : p.1.2 ≠ p.1.1) : bell1 (Ua V) 0 z f p = 0 := by
  simp only [bell1, add_zero]
  exact if_neg hp

lemma quad0 (V : F2 → Matrix (S × T) (S × T) ℂ) (σ : Matrix (Cell S T) (Cell S T) ℂ) (z : F2)
    (f : S × T) :
    star (bell1 (Ua V) 0 z f) ⬝ᵥ (σ *ᵥ bell1 (Ua V) 0 z f) =
      c2 * c2 * ∑ a : F2, ∑ a' : F2, chi (a * z) * chi (a' * z) *
        ∑ s : S × T, ∑ s' : S × T, star (V a s f) * σ ((a, a), s) ((a', a'), s') * V a' s' f := by
  classical
  have hmv : ∀ p : Cell S T, (σ *ᵥ bell1 (Ua V) 0 z f) p =
      ∑ a' : F2, ∑ s' : S × T, σ p ((a', a'), s') * (c2 * chi (a' * z) * V a' s' f) := by
    intro p
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_cell_diag]
    · simp only [bell1_zero_diag]
    · intro q hq
      rw [bell1_zero_off V z f q hq, mul_zero]
  simp only [dotProduct, Pi.star_apply]
  rw [sum_cell_diag]
  · simp only [bell1_zero_diag, hmv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun s' _ => ?_
    simp only [star_mul', star_chi, star_c2]
    ring
  · intro p hp
    rw [bell1_zero_off V z f p hp, star_zero, zero_mul]

lemma sum_G (V : F2 → Matrix (S × T) (S × T) ℂ) (σ : Matrix (Cell S T) (Cell S T) ℂ) (a a' : F2) :
    ∑ f : S × T, ∑ s : S × T, ∑ s' : S × T, star (V a s f) * σ ((a, a), s) ((a', a'), s') * V a' s' f =
      ∑ s : S × T, ∑ s' : S × T, σ ((a, a), s) ((a', a'), s') * (V a' * (V a)ᴴ) s' s := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  simp only [Matrix.mul_apply, conjTranspose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => by ring

theorem squeeze (σ : Matrix (Cell S T) (Cell S T) ℂ) (hσ : σ.IsHermitian)
    (W : Matrix (S × T) (S × T) ℂ) :
    pBell (Ua (Vsq W)) σ 0 0 - pBell (Ua (Vsq W)) σ 0 1 = 2 * (W * corner σ).trace.re := by
  classical
  unfold pBell
  rw [← Finset.sum_sub_distrib]
  simp only [← Complex.sub_re, quad0]
  rw [← Complex.re_sum]
  have e : ∀ f : S × T,
      c2 * c2 * ∑ a : F2, ∑ a' : F2, chi (a * 0) * chi (a' * 0) *
        ∑ s : S × T, ∑ s' : S × T, star (Vsq W a s f) * σ ((a, a), s) ((a', a'), s') * Vsq W a' s' f -
      c2 * c2 * ∑ a : F2, ∑ a' : F2, chi (a * 1) * chi (a' * 1) *
        ∑ s : S × T, ∑ s' : S × T, star (Vsq W a s f) * σ ((a, a), s) ((a', a'), s') * Vsq W a' s' f =
      (∑ s : S × T, ∑ s' : S × T, star (Vsq W 0 s f) * σ ((0, 0), s) ((1, 1), s') * Vsq W 1 s' f) +
      (∑ s : S × T, ∑ s' : S × T, star (Vsq W 1 s f) * σ ((1, 1), s) ((0, 0), s') * Vsq W 0 s' f) := by
    intro f
    simp only [sum_F2, mul_zero, mul_one, chi_zero, chi_one, zero_mul, one_mul]
    have h2 := c2_sq
    linear_combination (2 * (∑ s : S × T, ∑ s' : S × T,
      star (Vsq W 0 s f) * σ ((0, 0), s) ((1, 1), s') * Vsq W 1 s' f) +
      2 * (∑ s : S × T, ∑ s' : S × T,
      star (Vsq W 1 s f) * σ ((1, 1), s) ((0, 0), s') * Vsq W 0 s' f)) * h2
  simp only [e]
  rw [Finset.sum_add_distrib, sum_G, sum_G, Vsq_zero, Vsq_one, Matrix.conjTranspose_one,
    Matrix.mul_one, Matrix.one_mul]
  have h1 : ∑ s : S × T, ∑ s' : S × T, σ ((0, 0), s) ((1, 1), s') * W s' s = (W * corner σ).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, corner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  have h2 : ∑ s : S × T, ∑ s' : S × T, σ ((1, 1), s) ((0, 0), s') * Wᴴ s' s =
      star (W * corner σ).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, star_sum, star_mul']
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [conjTranspose_apply, ← hσ.apply ((1, 1), s) ((0, 0), s')]
    unfold corner
    ring
  rw [h1, h2, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- Privacy squeezing: with the polar twist, `p(0,0) ≥ 2‖X‖₁`. -/
theorem squeeze_polar (σ : Matrix (Cell S T) (Cell S T) ℂ) (hσ : σ.PosSemidef) :
    ∃ W : Matrix (S × T) (S × T) ℂ, Wᴴ * W = 1 ∧
      2 * traceNorm (corner σ) ≤ pBell (Ua (Vsq W)) σ 0 0 := by
  obtain ⟨W, hW, he⟩ := traceNorm_eq_polar (corner σ)
  refine ⟨W, hW, ?_⟩
  have h := squeeze σ hσ.1 W
  have h0 := pBell_nonneg (Ua (Vsq W)) hσ 0 1
  rw [he]
  linarith

end Sq

end NPK

end Mod_NPK_Squeeze

section Mod_NPK_Prob
/-!
# Probability of the good error patterns
-/

open scoped Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

section Tail

variable {γ : Type} [Fintype γ] {m : ℕ}

/-- **Chebyshev bound** for the upper tail of the number of successes. -/
theorem count_upper_tail (μ ind : γ → ℝ) (hμ0 : ∀ g, 0 ≤ μ g) (hμ1 : ∑ g, μ g = 1)
    (hind : ∀ x, ind x * ind x = ind x) (k : ℝ) (hk : m * ∑ x, μ x * ind x < k) :
    ∑ w : Fin m → γ, (∏ t, μ (w t)) * (if k < ∑ t, ind (w t) then 1 else 0) ≤
      m * (∑ x, μ x * ind x) * (1 - ∑ x, μ x * ind x) / (k - m * ∑ x, μ x * ind x) ^ 2 := by
  set ind' : γ → ℝ := fun x => 1 - ind x with hind'
  have hind'2 : ∀ x, ind' x * ind' x = ind' x := by
    intro x
    simp only [hind']
    have := hind x
    linear_combination this
  have hq' : ∑ x, μ x * ind' x = 1 - ∑ x, μ x * ind x := by
    simp only [hind', mul_sub, mul_one, Finset.sum_sub_distrib, hμ1]
  have hk' : (m : ℝ) - k < m * ∑ x, μ x * ind' x := by
    rw [hq']; linarith
  have h := FKR.count_lower_tail μ ind' hμ0 hμ1 hind'2 (m - k) hk'
  have e : ∀ w : Fin m → γ, (if k < ∑ t, ind (w t) then (1 : ℝ) else 0) =
      if ∑ t, ind' (w t) < m - k then 1 else 0 := by
    intro w
    have : ∑ t, ind' (w t) = m - ∑ t, ind (w t) := by
      simp only [hind', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [this]
    congr 1
    apply propext
    constructor <;> intro h <;> linarith
  simp only [e]
  refine le_trans h (le_of_eq ?_)
  rw [hq']
  congr 1
  · ring
  · ring

end Tail

section Good

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] {n : ℕ}

/-- Indicator of a bit error. -/
def indX (l : Lab S T) : ℝ := if l.1 ≠ 0 then 1 else 0

/-- Indicator of a phase error. -/
def indZ (l : Lab S T) : ℝ := if l.2.1 ≠ 0 then 1 else 0

lemma indX_sq (l : Lab S T) : indX l * indX l = indX l := by
  unfold indX; split_ifs <;> norm_num

lemma indZ_sq (l : Lab S T) : indZ l * indZ l = indZ l := by
  unfold indZ; split_ifs <;> norm_num

lemma wt_xL (ℓ : Fin n → Lab S T) : (wt (xL ℓ) : ℝ) = ∑ t, indX (ℓ t) := by
  unfold wt xL indX
  rw [Finset.natCast_card_filter]

lemma wt_zL (ℓ : Fin n → Lab S T) : (wt (zL ℓ) : ℝ) = ∑ t, indZ (ℓ t) := by
  unfold wt zL indZ
  rw [Finset.natCast_card_filter]

/-- The good labels: few bit errors and few phase errors. -/
def Good (w : ℕ) (ℓ : Fin n → Lab S T) : Prop := wt (xL ℓ) ≤ w ∧ wt (zL ℓ) ≤ w

instance (w : ℕ) : DecidablePred (Good (S := S) (T := T) (n := n) w) := fun ℓ => by
  unfold Good; infer_instance

lemma tail_bound (μ ind : Lab S T → ℝ) (hμ0 : ∀ g, 0 ≤ μ g) (hμ1 : ∑ g, μ g = 1)
    (hind : ∀ x, ind x * ind x = ind x) (w : ℕ) (q0 : ℝ) (hq : ∑ x, μ x * ind x ≤ q0)
    (hqw : n * q0 < w) :
    ∑ ℓ : Fin n → Lab S T, (∏ t, μ (ℓ t)) * (if (w : ℝ) < ∑ t, ind (ℓ t) then 1 else 0) ≤
      n * q0 / (w - n * q0) ^ 2 := by
  set q := ∑ x, μ x * ind x with hqdef
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun x _ => mul_nonneg (hμ0 x) (by
    have := hind x
    nlinarith [sq_nonneg (ind x)])
  have hq1 : q ≤ 1 := by
    have : ∀ x, μ x * ind x ≤ μ x := by
      intro x
      have h1 := hind x
      have : ind x ≤ 1 := by nlinarith [sq_nonneg (ind x - 1)]
      exact mul_le_of_le_one_right (hμ0 x) this
    calc q ≤ ∑ x, μ x := Finset.sum_le_sum fun x _ => this x
      _ = 1 := hμ1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hqw' : n * q < w := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hq hn0) hqw
  refine le_trans (count_upper_tail μ ind hμ0 hμ1 hind w hqw') ?_
  have hgap : 0 < (w : ℝ) - n * q0 := by linarith
  have hgap' : (w : ℝ) - n * q0 ≤ w - n * q := by nlinarith
  have hnum : (n : ℝ) * q * (1 - q) ≤ n * q0 := by
    have h1 := mul_nonneg (mul_nonneg hn0 hq0) hq0
    have h2 := mul_le_mul_of_nonneg_left hq hn0
    nlinarith
  have hgq : 0 < (w : ℝ) - n * q := by linarith
  calc (n : ℝ) * q * (1 - q) / (w - n * q) ^ 2 ≤ n * q0 / (w - n * q) ^ 2 :=
        div_le_div_of_nonneg_right hnum (pow_pos hgq 2).le
    _ ≤ n * q0 / (w - n * q0) ^ 2 := by
        apply div_le_div_of_nonneg_left (mul_nonneg hn0 (le_trans hq0 hq)) (pow_pos hgap 2)
        exact pow_le_pow_left₀ hgap.le hgap' 2

theorem good_prob (μ : Lab S T → ℝ) (hμ0 : ∀ g, 0 ≤ μ g) (hμ1 : ∑ g, μ g = 1) (w : ℕ) (q0 : ℝ)
    (hqx : ∑ x, μ x * indX x ≤ q0) (hqz : ∑ x, μ x * indZ x ≤ q0) (hqw : n * q0 < w) :
    1 - 2 * (n * q0 / (w - n * q0) ^ 2) ≤
      ∑ ℓ : Fin n → Lab S T, (∏ t, μ (ℓ t)) * (if Good w ℓ then 1 else 0) := by
  have hX := tail_bound (n := n) μ indX hμ0 hμ1 indX_sq w q0 hqx hqw
  have hZ := tail_bound (n := n) μ indZ hμ0 hμ1 indZ_sq w q0 hqz hqw
  have h1 : ∑ ℓ : Fin n → Lab S T, ∏ t, μ (ℓ t) = 1 := FKR.sum_prod_one μ hμ1
  have hle : ∀ ℓ : Fin n → Lab S T,
      (∏ t, μ (ℓ t)) - (∏ t, μ (ℓ t)) * (if (w : ℝ) < ∑ t, indX (ℓ t) then 1 else 0) -
        (∏ t, μ (ℓ t)) * (if (w : ℝ) < ∑ t, indZ (ℓ t) then 1 else 0) ≤
      (∏ t, μ (ℓ t)) * (if Good w ℓ then 1 else 0) := by
    intro ℓ
    have hP : 0 ≤ ∏ t, μ (ℓ t) := Finset.prod_nonneg fun t _ => hμ0 _
    rw [← wt_xL, ← wt_zL]
    unfold Good
    by_cases hx : wt (xL ℓ) ≤ w <;> by_cases hz : wt (zL ℓ) ≤ w
    · have hx' : ¬ ((w : ℝ) < wt (xL ℓ)) := by rw [not_lt]; exact_mod_cast hx
      have hz' : ¬ ((w : ℝ) < wt (zL ℓ)) := by rw [not_lt]; exact_mod_cast hz
      simp [hx, hz, hx', hz']
    · have hz' : (w : ℝ) < wt (zL ℓ) := by exact_mod_cast not_le.mp hz
      simp only [hz', if_true, hx, hz, and_false, if_false, mul_zero, mul_one]
      split_ifs <;> linarith
    · have hx' : (w : ℝ) < wt (xL ℓ) := by exact_mod_cast not_le.mp hx
      simp only [hx', if_true, hx, false_and, if_false, mul_zero, mul_one]
      split_ifs <;> linarith
    · have hx' : (w : ℝ) < wt (xL ℓ) := by exact_mod_cast not_le.mp hx
      have hz' : (w : ℝ) < wt (zL ℓ) := by exact_mod_cast not_le.mp hz
      simp only [hx', hz', if_true, hx, false_and, if_false, mul_zero, mul_one]
      linarith
  have := Finset.sum_le_sum fun ℓ (_ : ℓ ∈ Finset.univ) => hle ℓ
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1] at this
  linarith

end Good

end NPK

end Mod_NPK_Prob

section Mod_NPK_Proto
/-!
# The one-way hashing protocol

Alice measures the syndrome `s = H₁ a` of her raw key, announces it, and outputs the key `K a`
(keeping `a` and her shields). Bob measures `s' = H₁ b`, corrects `b ↦ b + dec(s + s')`, and
outputs `K (b + dec(s+s'))` (keeping the corrected string and his shields).
-/

open QAlgorithms
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

/-! ### Classical partial maps as matrices -/

section CMap

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma star_ite_one (c : Prop) [Decidable c] : star (if c then (1 : ℂ) else 0) = if c then 1 else 0 := by
  split_ifs <;> simp

/-- The matrix of a classical partial map: `|f x⟩⟨x|` for `x` satisfying `P`. -/
noncomputable def cmap (P : ι → Prop) [DecidablePred P] (f : ι → κ) : Matrix κ ι ℂ :=
  fun o x => if P x ∧ o = f x then 1 else 0

lemma cmap_conj_mul (P : ι → Prop) [DecidablePred P] (f : ι → κ) (hf : Function.Injective f) :
    (cmap P f)ᴴ * cmap P f = Matrix.diagonal (fun x => if P x then 1 else 0) := by
  ext x y
  simp only [Matrix.mul_apply, conjTranspose_apply, cmap, Matrix.diagonal_apply, star_ite_one]
  rw [Finset.sum_eq_single (f x)]
  · by_cases hxy : x = y
    · subst hxy
      by_cases hP : P x <;> simp [hP]
    · have : f x ≠ f y := fun h => hxy (hf h)
      simp [hxy, this]
  · intro o _ ho
    simp [ho]
  · simp

lemma cmap_kraus {σ : Type} [Fintype σ] [DecidableEq σ] (π : ι → σ) (f : σ → ι → κ)
    (hf : ∀ s, Function.Injective (f s)) :
    ∑ s, (cmap (fun x => π x = s) (f s))ᴴ * cmap (fun x => π x = s) (f s) = 1 := by
  simp only [cmap_conj_mul _ _ (hf _)]
  ext x y
  simp only [Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · simp [h]

lemma cmap_mulVec (P : ι → Prop) [DecidablePred P] (f : ι → κ) (g : κ → ι)
    (hg : ∀ x, g (f x) = x) (v : ι → ℂ) (o : κ) :
    (cmap P f *ᵥ v) o = if P (g o) ∧ o = f (g o) then v (g o) else 0 := by
  simp only [Matrix.mulVec, dotProduct, cmap]
  rw [Finset.sum_eq_single (g o)]
  · split_ifs <;> simp
  · intro x _ hx
    rw [if_neg, zero_mul]
    rintro ⟨-, ho⟩
    apply hx
    rw [ho, hg]
  · simp

lemma kron_cmap {ι' κ' : Type} [DecidableEq κ'] (P : ι → Prop) [DecidablePred P] (f : ι → κ)
    (Q : ι' → Prop) [DecidablePred Q] (g : ι' → κ') :
    Matrix.kronecker (cmap P f) (cmap Q g) =
      cmap (fun x : ι × ι' => P x.1 ∧ Q x.2) (Prod.map f g) := by
  ext ⟨o1, o2⟩ ⟨x1, x2⟩
  rw [kron_eq, kronecker_apply]
  unfold cmap
  simp only [Prod.map_apply, Prod.mk.injEq]
  by_cases h1 : P x1 <;> by_cases h2 : Q x2 <;> by_cases h3 : o1 = f x1 <;>
    by_cases h4 : o2 = g x2 <;> simp [h1, h2, h3, h4]

end CMap

lemma kron_sum_right {l m' n' p : Type*} {ι : Type*} (s : Finset ι) (A : Matrix l m' ℂ)
    (B : ι → Matrix n' p ℂ) :
    Matrix.kronecker A (∑ i ∈ s, B i) = ∑ i ∈ s, Matrix.kronecker A (B i) := by
  ext x y
  simp [kron_eq, Matrix.sum_apply, kronecker_apply, Finset.mul_sum]

lemma kron_sum_left {l m' n' p : Type*} {ι : Type*} (s : Finset ι) (A : ι → Matrix l m' ℂ)
    (B : Matrix n' p ℂ) :
    Matrix.kronecker (∑ i ∈ s, A i) B = ∑ i ∈ s, Matrix.kronecker (A i) B := by
  ext x y
  simp [kron_eq, Matrix.sum_apply, kronecker_apply, Finset.sum_mul]

lemma kron_sum_right' {l m' n' p : Type*} {ι : Type*} (s : Finset ι) (A : Matrix l m' ℂ)
    (B : ι → Matrix n' p ℂ) : A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, A ⊗ₖ (B i) :=
  kron_sum_right s A B

lemma kron_sum_left' {l m' n' p : Type*} {ι : Type*} (s : Finset ι) (A : ι → Matrix l m' ℂ)
    (B : Matrix n' p ℂ) : (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, (A i) ⊗ₖ B :=
  kron_sum_left s A B

/-! ### The protocol -/

/-- Output key register. -/
abbrev KeyO (m : ℕ) := Fin m → F2

/-- A party's output register: key and shield. -/
abbrev OutA (m n : ℕ) (S : Type) := KeyO m × AReg n S

/-- The bipartite output register. -/
abbrev Out (m n : ℕ) (S T : Type) := OutA m n S × OutA m n T

set_option synthInstance.maxSize 1000 in
instance instDecEqOut (m n : ℕ) (S T : Type) [DecidableEq S] [DecidableEq T] :
    DecidableEq (Out m n S T) :=
  instDecidableEqProd

section Proto

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
variable {n r1 r2 m w : ℕ} (C : GoodCode n r1 r2 m w)

/-- Alice's Kraus operator for the announced syndrome `s`. -/
noncomputable def kA (s : Fin r1 → F2) : Matrix (OutA m n S) (AReg n S) ℂ :=
  cmap (fun x : AReg n S => C.H1 *ᵥ x.1 = s) (fun x => (C.K *ᵥ x.1, x))

/-- Bob's correction. -/
def bobFix (s s' : Fin r1 → F2) (y : AReg n T) : AReg n T := (y.1 + C.dec (s + s'), y.2)

/-- Bob's Kraus operator for his syndrome `s'`, given Alice's announcement `s`. -/
noncomputable def kB (s s' : Fin r1 → F2) : Matrix (OutA m n T) (AReg n T) ℂ :=
  cmap (fun y : AReg n T => C.H1 *ᵥ y.1 = s')
    (fun y => (C.K *ᵥ (bobFix C s s' y).1, bobFix C s s' y))

lemma kA_kraus : ∑ s, (kA (S := S) C s)ᴴ * kA C s = 1 :=
  cmap_kraus (fun x : AReg n S => C.H1 *ᵥ x.1) (fun _ x => (C.K *ᵥ x.1, x))
    fun _ x y h => (Prod.mk.inj h).2

lemma bobFix_inj (s s' : Fin r1 → F2) : Function.Injective (bobFix (T := T) C s s') := by
  intro y y' h
  simp only [bobFix, Prod.mk.injEq] at h
  exact Prod.ext (add_right_cancel h.1) h.2

lemma kB_kraus (s : Fin r1 → F2) : ∑ s', (kB (T := T) C s s')ᴴ * kB C s s' = 1 :=
  cmap_kraus (fun y : AReg n T => C.H1 *ᵥ y.1)
    (fun s' y => (C.K *ᵥ (bobFix C s s' y).1, bobFix C s s' y))
    fun s' y y' h => bobFix_inj C s s' (Prod.mk.inj h).2

/-- The protocol, as an LOCC map. -/
noncomputable def proto (X : Matrix (InReg n S T) (InReg n S T) ℂ) :
    Matrix (Out m n S T) (Out m n S T) ℂ :=
  ∑ s : Fin r1 → F2, (fun Y : Matrix (OutA m n S × AReg n T) (OutA m n S × AReg n T) ℂ =>
    ∑ s' : Fin r1 → F2, (fun Z : Matrix (Out m n S T) (Out m n S T) ℂ => Z)
      (Matrix.kronecker (1 : Matrix (OutA m n S) (OutA m n S) ℂ) (kB (T := T) C s s') * Y *
        (Matrix.kronecker (1 : Matrix (OutA m n S) (OutA m n S) ℂ) (kB (T := T) C s s'))ᴴ))
    (Matrix.kronecker (kA (S := S) C s) (1 : Matrix (AReg n T) (AReg n T) ℂ) * X *
      (Matrix.kronecker (kA (S := S) C s) (1 : Matrix (AReg n T) (AReg n T) ℂ))ᴴ)

theorem proto_locc : IsLOCCAbs (proto (S := S) (T := T) C) :=
  IsLOCCAbs.alice (kA (S := S) C) (kA_kraus C) _ fun s =>
    IsLOCCAbs.bob (kB (T := T) C s) (kB_kraus C s) (fun _ Z => Z) fun _ => IsLOCCAbs.id

/-- The joint Kraus operators. -/
noncomputable def Kj (j : (Fin r1 → F2) × (Fin r1 → F2)) :
    Matrix (Out m n S T) (InReg n S T) ℂ :=
  Matrix.kronecker (kA (S := S) C j.1) (kB (T := T) C j.1 j.2)

theorem proto_eq (X : Matrix (InReg n S T) (InReg n S T) ℂ) :
    proto C X = ∑ j, Kj (S := S) (T := T) C j * X * (Kj (S := S) (T := T) C j)ᴴ := by
  unfold proto Kj
  simp only [kron_two_step]
  rw [Fintype.sum_prod_type]

theorem Kj_kraus : ∑ j, (Kj (S := S) (T := T) C j)ᴴ * Kj (S := S) (T := T) C j = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Kj, kron_eq, conjTranspose_kronecker, ← mul_kronecker_mul]
  have e : ∀ s : Fin r1 → F2, ∑ s', ((kA (S := S) C s)ᴴ * kA (S := S) C s) ⊗ₖ
      ((kB (T := T) C s s')ᴴ * kB (T := T) C s s') =
      ((kA (S := S) C s)ᴴ * kA (S := S) C s) ⊗ₖ (1 : Matrix (AReg n T) (AReg n T) ℂ) := by
    intro s
    rw [← kron_sum_right']
    congr 1
    exact kB_kraus C s
  simp only [e]
  rw [← kron_sum_left']
  rw [show ∑ s, (kA (S := S) C s)ᴴ * kA (S := S) C s = 1 from kA_kraus C, one_kronecker_one]

end Proto

end NPK

end Mod_NPK_Proto

section Mod_NPK_Twist
/-!
# The output twisting

The output of the protocol on a good twisted Bell vector is a vector of the form
`2^{-m/2} Σ_k |k k⟩ ⊗ U_k g`, where the twist `U_k` is built from
* the inverse shield twisting `C` (controlled by Alice's raw key),
* a translation of both raw keys by `t_k` (mapping the key-`0` coset to the key-`k` coset),
* a coherent phase correction `Ξ_k = Σ_ς χ(t_k · zdec ς) Π_ς`, where the `Π_ς` are the spectral
  projectors of the translations by the phase checks.
-/

open QAlgorithms
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

lemma two_pow_ne (r : ℕ) : ((2 : ℂ) ^ r) ≠ 0 := pow_ne_zero _ two_ne_zero

lemma sum_chi_dot' {r : ℕ} (u : Fin r → F2) :
    ∑ ς : Fin r → F2, chi (u ⬝ᵥ ς) = if u = 0 then (2 : ℂ) ^ r else 0 := by
  simp_rw [dotProduct_comm u]
  exact sum_chi_dot u

lemma F2_vec_add_eq_zero {r : ℕ} (a b : Fin r → F2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + b + b := by rw [add_assoc, vec_add_self, add_zero]
      _ = b := by rw [h, zero_add]
  · rintro rfl; exact vec_add_self a

/-! ### Spectral projectors of a representation of `F₂^r` -/

section Fourier

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- `Π_ς = 2^{-r} Σ_u χ(u·ς) G(u)`. -/
noncomputable def projF (G : (Fin r → F2) → Matrix ι ι ℂ) (ς : Fin r → F2) : Matrix ι ι ℂ :=
  ((2 : ℂ) ^ r)⁻¹ • ∑ u, chi (u ⬝ᵥ ς) • G u

lemma projF_sum (G : (Fin r → F2) → Matrix ι ι ℂ) (hG0 : G 0 = 1) : ∑ ς, projF G ς = 1 := by
  unfold projF
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_chi_dot', ite_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (0 : Fin r → F2), if_pos (Finset.mem_univ _), hG0, smul_smul,
    inv_mul_cancel₀ (two_pow_ne r), one_smul]

lemma projF_mul (G : (Fin r → F2) → Matrix ι ι ℂ) (hGm : ∀ u u', G u * G u' = G (u + u'))
    (ς ς' : Fin r → F2) : projF G ς * projF G ς' = if ς = ς' then projF G ς else 0 := by
  have step1 : projF G ς * projF G ς' = ((2 : ℂ) ^ r)⁻¹ • ((2 : ℂ) ^ r)⁻¹ •
      ∑ u, ∑ u', (chi (u ⬝ᵥ ς) * chi (u' ⬝ᵥ ς')) • G (u + u') := by
    unfold projF
    rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hGm]
  have step2 : ∀ u : Fin r → F2, ∑ u', (chi (u ⬝ᵥ ς) * chi (u' ⬝ᵥ ς')) • G (u + u') =
      ∑ v, (chi (u ⬝ᵥ (ς + ς')) * chi (v ⬝ᵥ ς')) • G v := by
    intro u
    refine Fintype.sum_equiv (Equiv.addLeft u) _ _ fun u' => ?_
    simp only [Equiv.coe_addLeft]
    congr 1
    rw [dotProduct_add, add_dotProduct, chi_add, chi_add]
    have := chi_mul_self (u ⬝ᵥ ς')
    linear_combination (-(chi (u ⬝ᵥ ς) * chi (u' ⬝ᵥ ς'))) * this
  have step3 : ∑ u : Fin r → F2, ∑ v, (chi (u ⬝ᵥ (ς + ς')) * chi (v ⬝ᵥ ς')) • G v =
      (∑ u : Fin r → F2, chi (u ⬝ᵥ (ς + ς'))) • ∑ v, chi (v ⬝ᵥ ς') • G v := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_smul]
  rw [step1]
  simp_rw [step2]
  rw [step3, sum_chi_dot]
  by_cases h : ς = ς'
  · subst h
    rw [if_pos (vec_add_self ς), if_pos rfl, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (two_pow_ne r), mul_one]
    rfl
  · rw [if_neg (fun h' => h ((F2_vec_add_eq_zero _ _).mp h')), if_neg h, zero_smul, smul_zero,
      smul_zero]

lemma projF_herm (G : (Fin r → F2) → Matrix ι ι ℂ) (hGh : ∀ u, (G u)ᴴ = G u)
    (ς : Fin r → F2) : (projF G ς)ᴴ = projF G ς := by
  unfold projF
  rw [conjTranspose_smul, conjTranspose_sum]
  congr 1
  · simp [star_inv₀, star_pow]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [conjTranspose_smul, hGh, star_chi]

lemma projF_mulVec (G : (Fin r → F2) → Matrix ι ι ℂ) (v : ι → ℂ) (Zs : Fin r → F2)
    (hv : ∀ u, G u *ᵥ v = chi (u ⬝ᵥ Zs) • v) (ς : Fin r → F2) :
    projF G ς *ᵥ v = if ς = Zs then v else 0 := by
  unfold projF
  rw [smul_mulVec, sum_mulVec]
  simp_rw [smul_mulVec, hv, smul_smul]
  rw [← Finset.sum_smul]
  have e : ∀ u : Fin r → F2, chi (u ⬝ᵥ ς) * chi (u ⬝ᵥ Zs) = chi (u ⬝ᵥ (ς + Zs)) := by
    intro u; rw [dotProduct_add, chi_add]
  simp_rw [e]
  rw [sum_chi_dot, smul_smul]
  by_cases h : ς = Zs
  · subst h
    rw [if_pos (vec_add_self ς), if_pos rfl, inv_mul_cancel₀ (two_pow_ne r), one_smul]
  · rw [if_neg (fun h' => h ((F2_vec_add_eq_zero _ _).mp h')), if_neg h, mul_zero, zero_smul]

/-- `Σ_ς c(ς) Π_ς`. -/
noncomputable def phaseF (G : (Fin r → F2) → Matrix ι ι ℂ) (c : (Fin r → F2) → ℂ) : Matrix ι ι ℂ :=
  ∑ ς, c ς • projF G ς

lemma phaseF_unitary (G : (Fin r → F2) → Matrix ι ι ℂ) (hG0 : G 0 = 1)
    (hGm : ∀ u u', G u * G u' = G (u + u')) (hGh : ∀ u, (G u)ᴴ = G u)
    (c : (Fin r → F2) → ℂ) (hc : ∀ ς, star (c ς) * c ς = 1) :
    (phaseF G c)ᴴ * phaseF G c = 1 := by
  unfold phaseF
  rw [conjTranspose_sum, Finset.sum_mul]
  have e : ∀ ς : Fin r → F2, (c ς • projF G ς)ᴴ * ∑ ς', c ς' • projF G ς' = projF G ς := by
    intro ς
    rw [conjTranspose_smul, projF_herm G hGh, Finset.mul_sum]
    simp_rw [Matrix.smul_mul, Matrix.mul_smul, projF_mul G hGm, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq Finset.univ ς, if_pos (Finset.mem_univ _), smul_smul, hc, one_smul]
  simp_rw [e]
  exact projF_sum G hG0

lemma phaseF_mulVec (G : (Fin r → F2) → Matrix ι ι ℂ) (c : (Fin r → F2) → ℂ) (v : ι → ℂ)
    (Zs : Fin r → F2) (hv : ∀ u, G u *ᵥ v = chi (u ⬝ᵥ Zs) • v) :
    phaseF G c *ᵥ v = c Zs • v := by
  unfold phaseF
  rw [sum_mulVec]
  simp_rw [smul_mulVec, projF_mulVec G v Zs hv, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' Finset.univ Zs, if_pos (Finset.mem_univ _)]

end Fourier

/-! ### Translations of the raw-key pair -/

/-- The raw-key pair register. -/
abbrev AB (n : ℕ) := (Fin n → F2) × (Fin n → F2)

section Trans

variable {n : ℕ}

/-- Translation of both raw keys by `v`. -/
noncomputable def Qm (v : Fin n → F2) : Matrix (AB n) (AB n) ℂ :=
  fun x y => if y = (x.1 + v, x.2 + v) then 1 else 0

lemma Qm_mulVec (v : Fin n → F2) (g : AB n → ℂ) : Qm v *ᵥ g = fun x => g (x.1 + v, x.2 + v) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Qm, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]

lemma Qm_mul (v v' : Fin n → F2) : Qm v * Qm v' = Qm (v + v') := by
  ext x z
  simp only [Matrix.mul_apply, Qm, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]
  simp only [add_assoc]

lemma Qm_zero : Qm (0 : Fin n → F2) = 1 := by
  ext x y
  simp only [Qm, add_zero, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

lemma Qm_herm (v : Fin n → F2) : (Qm v)ᴴ = Qm v := by
  ext x y
  simp only [conjTranspose_apply, Qm, star_ite_one]
  congr 1
  apply propext
  constructor
  · intro h
    rw [h, add_assoc, add_assoc, vec_add_self, add_zero, add_zero]
  · intro h
    rw [h, add_assoc, add_assoc, vec_add_self, add_zero, add_zero]

lemma Qm_unitary (v : Fin n → F2) : (Qm v)ᴴ * Qm v = 1 := by
  rw [Qm_herm, Qm_mul, vec_add_self, Qm_zero]

end Trans

/-! ### The key-register part of the twist -/

section KeyTwist

variable {n r1 r2 m w : ℕ} (C : GoodCode n r1 r2 m w)

/-- Translations by the phase checks. -/
noncomputable def Gph (u : Fin r2 → F2) : Matrix (AB n) (AB n) ℂ := Qm (u ᵥ* C.H2)

lemma Gph_zero : Gph C 0 = 1 := by
  unfold Gph; rw [zero_vecMul, Qm_zero]

lemma Gph_mul (u u' : Fin r2 → F2) : Gph C u * Gph C u' = Gph C (u + u') := by
  unfold Gph; rw [Qm_mul, add_vecMul]

lemma Gph_herm (u : Fin r2 → F2) : (Gph C u)ᴴ = Gph C u := Qm_herm _

/-- The coherent phase correction for the key value `k`. -/
noncomputable def Xi (k : KeyO m) : Matrix (AB n) (AB n) ℂ :=
  phaseF (Gph C) (fun ς => chi (C.tk k ⬝ᵥ C.zdec ς))

lemma Xi_unitary (k : KeyO m) : (Xi C k)ᴴ * Xi C k = 1 :=
  phaseF_unitary _ (Gph_zero C) (Gph_mul C) (Gph_herm C) _ fun ς => by
    rw [star_chi, chi_mul_self]

/-- The key-register twist `M_k = Q_{t_k} Ξ_k`. -/
noncomputable def Mk (k : KeyO m) : Matrix (AB n) (AB n) ℂ := Qm (C.tk k) * Xi C k

lemma Mk_unitary (k : KeyO m) : (Mk C k)ᴴ * Mk C k = 1 := by
  unfold Mk
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Qm (C.tk k))ᴴ, Qm_unitary,
    Matrix.one_mul, Xi_unitary]

/-- The raw-key amplitude of a good vector in the key-`k` sector. -/
noncomputable def amp (s : Fin r1 → F2) (Z : Fin n → F2) (k : KeyO m) (x : AB n) : ℂ :=
  if x.2 = x.1 ∧ C.H1 *ᵥ x.1 = s ∧ C.K *ᵥ x.1 = k then c2 ^ n * chi (x.1 ⬝ᵥ Z) else 0

lemma amp_shift (s : Fin r1 → F2) (Z : Fin n → F2) (k k' : KeyO m) (v : Fin n → F2)
    (hH : C.H1 *ᵥ v = 0) (hK : C.K *ᵥ v = k' ) (x : AB n) :
    amp C s Z k (x.1 + v, x.2 + v) = chi (v ⬝ᵥ Z) * amp C s Z (k + k') x := by
  unfold amp
  simp only [Matrix.mulVec_add, hH, hK, add_zero]
  have e1 : (x.2 + v = x.1 + v) ↔ x.2 = x.1 := ⟨fun h => add_right_cancel h, fun h => by rw [h]⟩
  have e2 : (C.K *ᵥ x.1 + k' = k) ↔ C.K *ᵥ x.1 = k + k' := by
    constructor
    · intro h; rw [← h, add_assoc, vec_add_self, add_zero]
    · intro h; rw [h, add_assoc, vec_add_self, add_zero]
  simp only [e1, e2]
  split_ifs
  · rw [add_dotProduct, chi_add]; ring
  · rw [mul_zero]

lemma Gph_amp (s : Fin r1 → F2) (Z : Fin n → F2) (u : Fin r2 → F2) :
    Gph C u *ᵥ amp C s Z 0 = chi (u ⬝ᵥ (C.H2 *ᵥ Z)) • amp C s Z 0 := by
  unfold Gph
  rw [Qm_mulVec]
  funext x
  rw [amp_shift C s Z 0 0 (u ᵥ* C.H2) (C.orth_H1 u) (C.orth_K u), add_zero, Pi.smul_apply,
    smul_eq_mul, Matrix.dotProduct_mulVec]

lemma Xi_amp (s : Fin r1 → F2) (Z : Fin n → F2) (hZ : wt Z ≤ w) (k : KeyO m) :
    Xi C k *ᵥ amp C s Z 0 = chi (C.tk k ⬝ᵥ Z) • amp C s Z 0 := by
  unfold Xi
  rw [phaseF_mulVec (Gph C) _ _ (C.H2 *ᵥ Z) (Gph_amp C s Z), C.zdec_spec Z hZ]

lemma Mk_amp (s : Fin r1 → F2) (Z : Fin n → F2) (hZ : wt Z ≤ w) (k : KeyO m) :
    Mk C k *ᵥ amp C s Z 0 = amp C s Z k := by
  unfold Mk
  rw [← Matrix.mulVec_mulVec, Xi_amp C s Z hZ, Matrix.mulVec_smul, Qm_mulVec]
  funext x
  rw [Pi.smul_apply, amp_shift C s Z 0 k (C.tk k) (C.tk_H1 k) (C.tk_K k), zero_add, smul_eq_mul,
    ← mul_assoc, chi_mul_self, one_mul]

end KeyTwist

/-! ### The full twist -/

section FullTwist

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
variable {n r1 r2 m w : ℕ} (C : GoodCode n r1 r2 m w)

/-- Layout `(shields) × (raw keys)`. -/
abbrev L2 (n : ℕ) (S T : Type) := Sh n S T × AB n

/-- The relabelling of the shield-pair register into the layout `L2`. -/
def eL (n : ℕ) (S T : Type) : InReg n S T ≃ L2 n S T where
  toFun x := ((x.1.2, x.2.2), (x.1.1, x.2.1))
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv x := rfl
  right_inv p := rfl

/-- The inverse shield twisting, controlled by Alice's raw key. -/
noncomputable def Cop (V : F2 → Matrix (S × T) (S × T) ℂ) : Matrix (L2 n S T) (L2 n S T) ℂ :=
  Matrix.blockDiagonal (fun ab : AB n => (Vn V ab.1)ᴴ)

lemma Cop_unitary {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1) :
    (Cop (n := n) V)ᴴ * Cop V = 1 := by
  unfold Cop
  rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  simp only [conjTranspose_conjTranspose, Vn_mul_conj hV]
  exact blockDiagonal_one

lemma Cop_unitary' {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1) :
    Cop (n := n) V * (Cop V)ᴴ = 1 :=
  mul_eq_one_comm.mp (Cop_unitary hV)

/-- The twist in the layout `L2`. -/
noncomputable def UL (V : F2 → Matrix (S × T) (S × T) ℂ) (k : KeyO m) :
    Matrix (L2 n S T) (L2 n S T) ℂ :=
  (Cop V)ᴴ * Matrix.kronecker (1 : Matrix (Sh n S T) (Sh n S T) ℂ) (Mk C k) * Cop V

lemma kron_one_unitary {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℂ) (hM : Mᴴ * M = 1) :
    (Matrix.kronecker (1 : Matrix ι ι ℂ) M)ᴴ * Matrix.kronecker (1 : Matrix ι ι ℂ) M = 1 := by
  rw [kron_eq, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hM,
    one_kronecker_one]

lemma UL_unitary {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1) (k : KeyO m) :
    (UL (S := S) (T := T) C V k)ᴴ * UL C V k = 1 := by
  unfold UL
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  have h1 := Cop_unitary (n := n) hV
  have h2 := Cop_unitary' (n := n) hV
  have h3 := kron_one_unitary (ι := Sh n S T) (Mk C k) (Mk_unitary C k)
  calc (Cop V)ᴴ * ((Matrix.kronecker (1 : Matrix (Sh n S T) (Sh n S T) ℂ) (Mk C k))ᴴ *
        Cop V) * ((Cop V)ᴴ * Matrix.kronecker (1 : Matrix (Sh n S T) (Sh n S T) ℂ) (Mk C k) *
        Cop V)
      = (Cop V)ᴴ * ((Matrix.kronecker (1 : Matrix (Sh n S T) (Sh n S T) ℂ) (Mk C k))ᴴ *
        (Cop V * (Cop V)ᴴ) * Matrix.kronecker (1 : Matrix (Sh n S T) (Sh n S T) ℂ) (Mk C k)) *
        Cop V := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h2, Matrix.mul_one, h3, Matrix.mul_one, h1]

/-- The good vector in the key-`k` sector, layout `L2`. -/
noncomputable def phiL (V : F2 → Matrix (S × T) (S × T) ℂ) (s : Fin r1 → F2) (Z : Fin n → F2)
    (F : Sh n S T) (k : KeyO m) : L2 n S T → ℂ :=
  fun p => amp C s Z k p.2 * Vn V p.2.1 p.1 F

/-- The same vector after removing the shield twisting. -/
noncomputable def hL (s : Fin r1 → F2) (Z : Fin n → F2) (F : Sh n S T) (k : KeyO m) :
    L2 n S T → ℂ :=
  fun p => (if p.1 = F then 1 else 0) * amp C s Z k p.2

lemma blockDiagonal_mulVec {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : κ → Matrix ι ι ℂ) (u : ι × κ → ℂ) (p : ι × κ) :
    (Matrix.blockDiagonal M *ᵥ u) p = ∑ i, M p.2 p.1 i * u (i, p.2) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single p.2]
  · rw [if_pos rfl]
  · intro k _ hk; rw [if_neg (Ne.symm hk), zero_mul]
  · simp

lemma Cop_phiL {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (s : Fin r1 → F2) (Z : Fin n → F2) (F : Sh n S T) (k : KeyO m) :
    Cop V *ᵥ phiL C V s Z F k = hL C s Z F k := by
  funext p
  unfold Cop
  rw [blockDiagonal_mulVec]
  unfold phiL hL
  have : ∑ i, (Vn V p.2.1)ᴴ p.1 i * (amp C s Z k p.2 * Vn V p.2.1 i F) =
      amp C s Z k p.2 * ((Vn V p.2.1)ᴴ * Vn V p.2.1) p.1 F := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, Vn_conj_mul hV, Matrix.one_apply]
  ring

lemma Copinv_hL {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (s : Fin r1 → F2) (Z : Fin n → F2) (F : Sh n S T) (k : KeyO m) :
    (Cop V)ᴴ *ᵥ hL C s Z F k = phiL C V s Z F k := by
  rw [← Cop_phiL C hV, Matrix.mulVec_mulVec, Cop_unitary hV, Matrix.one_mulVec]

lemma kron_hL (M : Matrix (AB n) (AB n) ℂ) (s : Fin r1 → F2) (Z : Fin n → F2) (F : Sh n S T)
    (k : KeyO m) :
    Matrix.kronecker (1 : Matrix (Sh n S T) (Sh n S T) ℂ) M *ᵥ hL C s Z F k =
      fun p => (if p.1 = F then 1 else 0) * (M *ᵥ amp C s Z k) p.2 := by
  funext p
  obtain ⟨p1, p2⟩ := p
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [kron_eq, kronecker_apply, hL, Matrix.one_apply]
  rw [Finset.sum_eq_single p1]
  · simp only [if_true, one_mul]
    by_cases h : p1 = F
    · simp only [h, if_true, one_mul]
    · simp only [h, if_false, zero_mul, mul_zero, Finset.sum_const_zero]
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

lemma UL_phiL {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (s : Fin r1 → F2) (Z : Fin n → F2) (hZ : wt Z ≤ w) (F : Sh n S T) (k : KeyO m) :
    UL C V k *ᵥ phiL C V s Z F 0 = phiL C V s Z F k := by
  unfold UL
  rw [← Matrix.mulVec_mulVec, Cop_phiL C hV, ← Matrix.mulVec_mulVec, kron_hL, Mk_amp C s Z hZ]
  exact Copinv_hL C hV s Z F k

/-- The output twist on the shield-pair register. -/
noncomputable def Uout (V : F2 → Matrix (S × T) (S × T) ℂ) (k : KeyO m) :
    Matrix (InReg n S T) (InReg n S T) ℂ :=
  (UL C V k).submatrix (eL n S T) (eL n S T)

lemma Uout_unitary {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (k : KeyO m) : (Uout (S := S) (T := T) C V k)ᴴ * Uout C V k = 1 := by
  unfold Uout
  rw [conjTranspose_submatrix, submatrix_mul_equiv, UL_unitary C hV, submatrix_one_equiv]

lemma Uout_phi {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (s : Fin r1 → F2) (Z : Fin n → F2) (hZ : wt Z ≤ w) (F : Sh n S T) (k : KeyO m) :
    Uout C V k *ᵥ (phiL C V s Z F 0 ∘ eL n S T) = phiL C V s Z F k ∘ eL n S T := by
  unfold Uout
  rw [submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
    UL_phiL C hV s Z hZ F k]

/-- The normalisation `2^{-m/2}`. -/
noncomputable def cd (m : ℕ) : ℂ := ((Real.sqrt ((2 : ℝ) ^ m) : ℝ) : ℂ)⁻¹

lemma cd_mul_star (m : ℕ) : cd m * star (cd m) = ((2 : ℂ) ^ m)⁻¹ := by
  unfold cd
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity)]
  push_cast; rfl

/-- The private-state isometry `J g = 2^{-m/2} Σ_k |k k⟩ ⊗ U_k g`. -/
noncomputable def Jm (V : F2 → Matrix (S × T) (S × T) ℂ) :
    Matrix (Out m n S T) (InReg n S T) ℂ :=
  fun o y => if o.1.1 = o.2.1 then cd m * Uout C V o.1.1 (o.1.2, o.2.2) y else 0

lemma card_KeyO (m : ℕ) : Fintype.card (KeyO m) = 2 ^ m := by
  simp [KeyO, Fintype.card_fun, ZMod.card]

lemma Jm_iso {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1) :
    (Jm (S := S) (T := T) C V)ᴴ * Jm C V = 1 := by
  ext y y'
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [conjTranspose_apply, Jm]
  rw [Fintype.sum_prod_type]
  have e : ∀ (kA : KeyO m) (shA : AReg n S),
      ∑ oB : OutA m n T,
        star (if kA = oB.1 then cd m * Uout C V kA (shA, oB.2) y else 0) *
          (if kA = oB.1 then cd m * Uout C V kA (shA, oB.2) y' else 0) =
      ((2 : ℂ) ^ m)⁻¹ * ∑ shB : AReg n T,
        star (Uout C V kA (shA, shB) y) * Uout C V kA (shA, shB) y' := by
    intro kA shA
    rw [Fintype.sum_prod_type, Finset.sum_eq_single kA]
    · simp only [if_true, star_mul', Finset.mul_sum]
      refine Finset.sum_congr rfl fun shB _ => ?_
      rw [← cd_mul_star m]
      ring
    · intro kB _ hk
      simp [Ne.symm hk]
    · simp
  simp only [e]
  have e2 : ∀ kA : KeyO m, ∑ shA : AReg n S, ((2 : ℂ) ^ m)⁻¹ * ∑ shB : AReg n T,
      star (Uout C V kA (shA, shB) y) * Uout C V kA (shA, shB) y' =
      ((2 : ℂ) ^ m)⁻¹ * ((Uout C V kA)ᴴ * Uout C V kA) y y' := by
    intro kA
    rw [← Finset.mul_sum, Matrix.mul_apply, Fintype.sum_prod_type (f := fun x =>
      (Uout C V kA)ᴴ y x * Uout C V kA x y')]
    simp only [conjTranspose_apply]
  simp only [e2, Uout_unitary C hV, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    card_KeyO, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (two_pow_ne m), one_mul]

lemma Jm_mulVec (V : F2 → Matrix (S × T) (S × T) ℂ) (g : InReg n S T → ℂ) (o : Out m n S T) :
    (Jm C V *ᵥ g) o = if o.1.1 = o.2.1 then cd m * (Uout C V o.1.1 *ᵥ g) (o.1.2, o.2.2) else 0 := by
  simp only [Matrix.mulVec, dotProduct, Jm]
  split_ifs
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  · simp

end FullTwist

end NPK

end Mod_NPK_Twist

section Mod_NPK_GoodVec
/-!
# Good twisted Bell vectors are mapped into the range of the private-state isometry
-/

open QAlgorithms
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

section GoodVec

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
variable {n r1 r2 m w : ℕ} (C : GoodCode n r1 r2 m w)

lemma bobFix_invol (s s' : Fin r1 → F2) (y : AReg n T) :
    bobFix C s s' (bobFix C s s' y) = y := by
  unfold bobFix
  simp only [add_assoc, vec_add_self, add_zero]

lemma Kj_mulVec (j : (Fin r1 → F2) × (Fin r1 → F2)) (v : InReg n S T → ℂ) (o : Out m n S T) :
    (Kj C j *ᵥ v) o = if (C.H1 *ᵥ o.1.2.1 = j.1 ∧ C.H1 *ᵥ (bobFix C j.1 j.2 o.2.2).1 = j.2) ∧
        (o.1.1 = C.K *ᵥ o.1.2.1 ∧ o.2.1 = C.K *ᵥ o.2.2.1) then
      v (o.1.2, bobFix C j.1 j.2 o.2.2) else 0 := by
  unfold Kj kA kB
  rw [kron_cmap, cmap_mulVec _ _ (fun o => (o.1.2, bobFix C j.1 j.2 o.2.2))
    (fun x => Prod.ext rfl (bobFix_invol C j.1 j.2 x.2))]
  congr 1
  apply propext
  simp only [Prod.map_apply, bobFix_invol]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_, ?_⟩
    · exact congrArg (fun p => p.1) (congrArg Prod.fst h2)
    · exact congrArg (fun p => p.1) (congrArg Prod.snd h2)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    obtain ⟨⟨kA, xA⟩, ⟨kB, xB⟩⟩ := o
    simp only at h2 h3
    rw [h2, h3]

lemma Kj_mulVec' (s s' : Fin r1 → F2) (v : InReg n S T → ℂ) (kA : KeyO m) (a : Fin n → F2)
    (sA : Fin n → S) (kB : KeyO m) (b : Fin n → F2) (sB : Fin n → T) :
    (Kj C (s, s') *ᵥ v) ((kA, (a, sA)), (kB, (b, sB))) =
      if (C.H1 *ᵥ a = s ∧ C.H1 *ᵥ (b + C.dec (s + s')) = s') ∧ (kA = C.K *ᵥ a ∧ kB = C.K *ᵥ b)
      then v ((a, sA), (b + C.dec (s + s'), sB)) else 0 :=
  Kj_mulVec C (s, s') v _

lemma bellN_closed' (V : F2 → Matrix (S × T) (S × T) ℂ) (ℓ : Fin n → Lab S T) (a : Fin n → F2)
    (sA : Fin n → S) (b : Fin n → F2) (sB : Fin n → T) :
    bellN (Ua V) ℓ ((a, sA), (b, sB)) = if b = a + xL ℓ then
      c2 ^ n * chi (a ⬝ᵥ zL ℓ) * Vn V a (sA, sB) (shL ℓ) else 0 :=
  bellN_closed V ℓ _

lemma amp_apply (s : Fin r1 → F2) (Z : Fin n → F2) (k : KeyO m) (a b : Fin n → F2) :
    amp C s Z k (a, b) = if b = a ∧ C.H1 *ᵥ a = s ∧ C.K *ᵥ a = k then c2 ^ n * chi (a ⬝ᵥ Z)
      else 0 := rfl

lemma phiL_eL (V : F2 → Matrix (S × T) (S × T) ℂ) (s : Fin r1 → F2) (Z : Fin n → F2)
    (F : Sh n S T) (k : KeyO m) (a : Fin n → F2) (sA : Fin n → S) (b : Fin n → F2)
    (sB : Fin n → T) :
    (phiL C V s Z F k ∘ eL n S T) ((a, sA), (b, sB)) = amp C s Z k (a, b) * Vn V a (sA, sB) F :=
  rfl

lemma Kj_bell (V : F2 → Matrix (S × T) (S × T) ℂ) (ℓ : Fin n → Lab S T) (hX : wt (xL ℓ) ≤ w)
    (s s' : Fin r1 → F2) (kA : KeyO m) (a : Fin n → F2) (sA : Fin n → S) (kB : KeyO m)
    (b : Fin n → F2) (sB : Fin n → T) :
    (Kj C (s, s') *ᵥ bellN (Ua V) ℓ) ((kA, (a, sA)), (kB, (b, sB))) =
      if s' = s + C.H1 *ᵥ xL ℓ then
      (if kA = kB then amp C s (zL ℓ) kA (a, b) * Vn V a (sA, sB) (shL ℓ) else 0) else 0 := by
  rw [Kj_mulVec', bellN_closed', amp_apply]
  by_cases hs : s' = s + C.H1 *ᵥ xL ℓ
  · have hdec : C.dec (s + s') = xL ℓ := by
      rw [hs, ← add_assoc, vec_add_self, zero_add, C.dec_spec _ hX]
    rw [if_pos hs]
    simp only [hdec]
    by_cases hb : b = a
    · subst hb
      simp only [if_true, true_and]
      have hH : ∀ h : C.H1 *ᵥ b = s, C.H1 *ᵥ (b + xL ℓ) = s' := by
        intro h; rw [Matrix.mulVec_add, h, hs]
      by_cases h1 : C.H1 *ᵥ b = s
      · simp only [h1, hH h1, true_and, and_self]
        by_cases hk : kA = kB
        · subst hk
          by_cases hk' : kA = C.K *ᵥ b
          · simp [hk', Eq.comm]
          · simp [hk', Ne.symm hk']
        · simp only [hk, if_false]
          split_ifs with h2
          · exact absurd (h2.1.trans h2.2.symm) hk
          · rfl
      · simp [h1]
    · have hne : ¬ (b + xL ℓ = a + xL ℓ) := fun h => hb (add_right_cancel h)
      simp only [hne, if_false, hb, false_and, zero_mul, ite_self]
  · rw [if_neg hs]
    simp only [ite_eq_right_iff]
    intro h1 h2
    exfalso
    apply hs
    rw [← h1.1.2, h2, Matrix.mulVec_add, h1.1.1]

lemma Jm_mulVec' (V : F2 → Matrix (S × T) (S × T) ℂ) (g : InReg n S T → ℂ) (kA : KeyO m)
    (xA : AReg n S) (kB : KeyO m) (xB : AReg n T) :
    (Jm C V *ᵥ g) ((kA, xA), (kB, xB)) =
      if kA = kB then cd m * (Uout C V kA *ᵥ g) (xA, xB) else 0 :=
  Jm_mulVec C V g _

/-- The preimage vector of a good twisted Bell vector. -/
noncomputable def gv (V : F2 → Matrix (S × T) (S × T) ℂ) (ℓ : Fin n → Lab S T)
    (j : (Fin r1 → F2) × (Fin r1 → F2)) : InReg n S T → ℂ :=
  if j.2 = j.1 + C.H1 *ᵥ xL ℓ then
    ((Real.sqrt ((2 : ℝ) ^ m) : ℝ) : ℂ) • (phiL C V j.1 (zL ℓ) (shL ℓ) 0 ∘ eL n S T) else 0

lemma cd_mul_sqrt (m : ℕ) : cd m * ((Real.sqrt ((2 : ℝ) ^ m) : ℝ) : ℂ) = 1 := by
  unfold cd
  apply inv_mul_cancel₀
  have : (0 : ℝ) < Real.sqrt ((2 : ℝ) ^ m) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast this.ne'

lemma good_col {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (ℓ : Fin n → Lab S T) (hX : wt (xL ℓ) ≤ w) (hZ : wt (zL ℓ) ≤ w)
    (j : (Fin r1 → F2) × (Fin r1 → F2)) :
    Kj C j *ᵥ bellN (Ua V) ℓ = Jm C V *ᵥ gv C V ℓ j := by
  funext o
  obtain ⟨⟨kA, a, sA⟩, ⟨kB, b, sB⟩⟩ := o
  obtain ⟨s, s'⟩ := j
  rw [Kj_bell C V ℓ hX, Jm_mulVec']
  unfold gv
  by_cases hs : s' = s + C.H1 *ᵥ xL ℓ
  · rw [if_pos hs, if_pos hs, Matrix.mulVec_smul, Uout_phi C hV _ _ hZ]
    split_ifs with hk
    · rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, cd_mul_sqrt, one_mul]
      rfl
    · rfl
  · rw [if_neg hs, if_neg hs, Matrix.mulVec_zero]
    split_ifs <;> simp

/-- The isometry whose columns are the good twisted Bell vectors. -/
noncomputable def Bm (V : F2 → Matrix (S × T) (S × T) ℂ) (w : ℕ) :
    Matrix (InReg n S T) {ℓ : Fin n → Lab S T // Good w ℓ} ℂ :=
  fun p ℓ => bellN (Ua V) ℓ.1 p

lemma Bm_iso {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1) (w : ℕ) :
    (Bm (n := n) V w)ᴴ * Bm (n := n) V w = 1 := by
  ext ℓ ℓ'
  have h := bellN_orthonormal (Ua_conj_mul hV) ℓ.1 ℓ'.1
  simp only [dotProduct, Pi.star_apply] at h
  simp only [Matrix.mul_apply, conjTranspose_apply, Bm, h, Matrix.one_apply, Subtype.ext_iff]

/-- The matrix of preimage vectors. -/
noncomputable def Gm (V : F2 → Matrix (S × T) (S × T) ℂ) (j : (Fin r1 → F2) × (Fin r1 → F2)) :
    Matrix (InReg n S T) {ℓ : Fin n → Lab S T // Good w ℓ} ℂ :=
  fun y ℓ => gv C V ℓ.1 j y

lemma Kj_Bm {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (j : (Fin r1 → F2) × (Fin r1 → F2)) :
    Kj (S := S) (T := T) C j * Bm (n := n) V w = Jm C V * Gm (w := w) C V j := by
  ext o ℓ
  have h := congrFun (good_col C hV ℓ.1 ℓ.2.1 ℓ.2.2 j) o
  simp only [Matrix.mulVec, dotProduct] at h
  simp only [Matrix.mul_apply, Bm, Gm]
  exact h

lemma Bm_good {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    (j : (Fin r1 → F2) × (Fin r1 → F2)) :
    Jm C V * (Jm C V)ᴴ * Kj (S := S) (T := T) C j * Bm (n := n) V w =
      Kj (S := S) (T := T) C j * Bm (n := n) V w := by
  rw [Matrix.mul_assoc, Kj_Bm C hV, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm C V)ᴴ, Jm_iso C hV,
    Matrix.one_mul]

/-- Weight of the good vectors. -/
lemma trace_Bm (V : F2 → Matrix (S × T) (S × T) ℂ) {σ : Matrix (Cell S T) (Cell S T) ℂ}
    (hσ : σ.PosSemidef) (w : ℕ) :
    (Bm (n := n) V w * (Bm (n := n) V w)ᴴ * powN (n := n) σ).trace.re =
      ∑ ℓ : Fin n → Lab S T, (∏ t, mu (Ua V) σ (ℓ t)) * (if Good w ℓ then 1 else 0) := by
  classical
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e : ∀ ℓ : {ℓ : Fin n → Lab S T // Good w ℓ},
      ((Bm (n := n) V w)ᴴ * powN (n := n) σ * Bm (n := n) V w) ℓ ℓ =
        star (bellN (Ua V) ℓ.1) ⬝ᵥ (powN (n := n) σ *ᵥ bellN (Ua V) ℓ.1) := by
    intro ℓ
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, conjTranspose_apply, Bm, Finset.sum_mul]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [show ((Bm (n := n) V w)ᴴ * powN (n := n) σ * Bm (n := n) V w).trace =
    ∑ ℓ, ((Bm (n := n) V w)ᴴ * powN (n := n) σ * Bm (n := n) V w) ℓ ℓ from rfl]
  simp only [e, Complex.re_sum, bellN_quad_re (Ua V) hσ]
  rw [← Finset.sum_subtype (Finset.univ.filter (Good w)) (by simp) (fun ℓ => ∏ t, mu (Ua V) σ (ℓ t)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs <;> simp

end GoodVec

end NPK

end Mod_NPK_GoodVec

section Mod_NPK_OneShot
/-!
# One run of the protocol

If the good twisted Bell vectors carry weight `≥ p > 0`, the output of the protocol is within
`2√(1-p) + 2(1-p)` (trace norm) of `J τ J†` for a state `τ`, i.e. of a private state.
-/

open QAlgorithms
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

section OneShot

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

lemma powN_density {n : ℕ} {σ : Matrix (Cell S T) (Cell S T) ℂ} (hσ : IsDensityMatrix σ) :
    IsDensityMatrix (powN (n := n) σ) := by
  unfold powN
  refine ⟨(tpow_posSemidef _ fun _ => hσ.1).submatrix _, ?_⟩
  rw [trace_submatrix_equiv, tpow_trace, hσ.2, Finset.prod_const_one]

lemma trace_eq_re_of_psd {ι : Type} [Fintype ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef) :
    X.trace = (X.trace.re : ℂ) := by
  have h := hX.trace_nonneg
  rw [Complex.nonneg_iff] at h
  apply Complex.ext
  · simp
  · simp [← h.2]

variable {n r1 r2 m w : ℕ} (C : GoodCode n r1 r2 m w)

theorem one_shot {V : F2 → Matrix (S × T) (S × T) ℂ} (hV : ∀ c, (V c)ᴴ * V c = 1)
    {σ : Matrix (Cell S T) (Cell S T) ℂ} (hσ : IsDensityMatrix σ) (p : ℝ) (hp : 0 < p)
    (hpG : p ≤ ∑ ℓ : Fin n → Lab S T, (∏ t, mu (Ua V) σ (ℓ t)) * (if Good w ℓ then 1 else 0)) :
    ∃ τ : Matrix (InReg n S T) (InReg n S T) ℂ, IsDensityMatrix τ ∧
      traceNorm (proto C (powN σ) - Jm C V * τ * (Jm C V)ᴴ) ≤
        2 * Real.sqrt (1 - p) + 2 * (1 - p) := by
  classical
  have hρ := powN_density (n := n) hσ
  set ω := proto (S := S) (T := T) C (powN σ) with hωdef
  have hω : IsDensityMatrix ω :=
    ⟨(proto_locc C).posSemidef _ hρ.1, by rw [hωdef, (proto_locc C).trace, hρ.2]⟩
  set J := Jm C V with hJ
  have hJJ : Jᴴ * J = 1 := Jm_iso C hV
  set P := J * Jᴴ with hPdef
  have hP : Pᴴ = P := by rw [hPdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hPP : P * P = P := by
    rw [hPdef, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJJ, Matrix.one_mul]
  have hfid := fidelity_ge (Bm (n := n) V w) (Bm_iso hV w) (Kj (S := S) (T := T) C) (Kj_kraus C) P
    hP hPP (fun j => Bm_good C hV j) (powN σ) hρ.1
  rw [trace_Bm V hσ.1 w, ← proto_eq] at hfid
  set t := (P * ω).trace.re with htdef
  have ht : p ≤ t := le_trans hpG hfid
  have ht0 : 0 < t := lt_of_lt_of_le hp ht
  have hg := gentle ω hω P hP hPP ht0
  -- the state τ
  set τ := ((1 / t : ℝ) : ℂ) • (Jᴴ * ω * J) with hτdef
  have hJτ : ((1 / t : ℝ) : ℂ) • (P * ω * P) = J * τ * Jᴴ := by
    rw [hτdef, hPdef, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have hpsd : (Jᴴ * ω * J).PosSemidef := by
    have := hω.1.conjTranspose_mul_mul_same J
    simpa [Matrix.mul_assoc] using this
  have htr : (Jᴴ * ω * J).trace = (t : ℂ) := by
    have e : (Jᴴ * ω * J).trace = (P * ω).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPdef]
    rw [trace_eq_re_of_psd hpsd, e]
  have hτ : IsDensityMatrix τ := by
    refine ⟨hpsd.smul (by positivity), ?_⟩
    rw [hτdef, Matrix.trace_smul, htr, smul_eq_mul, ← Complex.ofReal_mul, one_div,
      inv_mul_cancel₀ ht0.ne', Complex.ofReal_one]
  refine ⟨τ, hτ, ?_⟩
  rw [← hJτ]
  refine le_trans hg ?_
  have h1 : 1 - t ≤ 1 - p := by linarith
  have h2 : Real.sqrt (1 - t) ≤ Real.sqrt (1 - p) := Real.sqrt_le_sqrt h1
  linarith

end OneShot

end NPK

end Mod_NPK_OneShot

section Mod_NPK_Achieve
/-!
# From a protocol on the grouped registers to the operational definition of key rates
-/

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open QAlgorithms.Papers.Independent.Gap48.P42 (KeyAchievable bipartitePrivate
  bipartitePrivateRaw localIndex distillableKey)
open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower copyIndex)
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key keyBlock)
open scoped Matrix ComplexOrder Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

section Achieve

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

/-- The private-state isometry of a twisting family. -/
noncomputable def Jgen {n m : ℕ} (U : KeyO m → Matrix (InReg n S T) (InReg n S T) ℂ) :
    Matrix (Out m n S T) (InReg n S T) ℂ :=
  fun o y => if o.1.1 = o.2.1 then cd m * U o.1.1 (o.1.2, o.2.2) y else 0

lemma Jm_eq {n r1 r2 m w : ℕ} (C : GoodCode n r1 r2 m w) (V : F2 → Matrix (S × T) (S × T) ℂ) :
    Jm C V = Jgen (Uout C V) := rfl

lemma conj_apply' {ι κ : Type} [Fintype κ] (A B : Matrix ι κ ℂ) (Y : Matrix κ κ ℂ) (p q : ι) :
    (A * Y * Bᴴ) p q = ∑ u, ∑ v, A p u * Y u v * star (B q v) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma Jgen_conj {n m : ℕ} (U : KeyO m → Matrix (InReg n S T) (InReg n S T) ℂ)
    (τ : Matrix (InReg n S T) (InReg n S T) ℂ) (o o' : Out m n S T) :
    (Jgen U * τ * (Jgen U)ᴴ) o o' = if o.1.1 = o.2.1 ∧ o'.1.1 = o'.2.1 then
      ((2 : ℂ) ^ m)⁻¹ * (U o.1.1 * τ * (U o'.1.1)ᴴ) (o.1.2, o.2.2) (o'.1.2, o'.2.2) else 0 := by
  rw [conj_apply', conj_apply']
  simp only [Jgen]
  by_cases h1 : o.1.1 = o.2.1
  · by_cases h2 : o'.1.1 = o'.2.1
    · simp only [h1, h2, if_true, and_self, Finset.mul_sum, ← cd_mul_star m, star_mul']
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    · simp [h2]
  · simp [h1]

lemma submatrix_sub' {ι κ ι' κ' : Type*} (A B : Matrix ι κ ℂ) (f : ι' → ι) (g : κ' → κ) :
    (A - B).submatrix f g = A.submatrix f g - B.submatrix f g := rfl

lemma not_isEmpty_of_density {ι : Type} [Fintype ι] {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hρ.2
  simp [Matrix.trace] at this

theorem achieve (σ : Op (Key 2 × (S × T))) (hσ : IsDensityMatrix σ) (n m : ℕ)
    (Φ : Matrix (InReg n S T) (InReg n S T) ℂ → Matrix (Out m n S T) (Out m n S T) ℂ)
    (hΦ : IsLOCCAbs Φ) (U : KeyO m → Matrix (InReg n S T) (InReg n S T) ℂ)
    (hU : ∀ k, (U k)ᴴ * U k = 1) (τ : Matrix (InReg n S T) (InReg n S T) ℂ)
    (hτ : IsDensityMatrix τ) (ε : ℝ)
    (herr : traceNorm (Φ (powN (σ : Matrix (Cell S T) (Cell S T) ℂ)) - Jgen U * τ * (Jgen U)ᴴ) ≤ ε) :
    ∃ d s t : ℕ, 0 < d ∧ 0 < s ∧ 0 < t ∧
    ∃ tau : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ, IsDensityMatrix tau ∧
    ∃ U' : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ,
    ∃ L : Superop (Fin (Fintype.card (Fin 2 × S) ^ n) × Fin (Fintype.card (Fin 2 × T) ^ n))
      (Fin (d * s) × Fin (d * t)),
      FiniteLOCC L ∧
      traceNorm (L (dimensionedPower (HorodeckiBoundKey.finCut σ) n) - bipartitePrivate tau U') ≤ ε ∧
      d = 2 ^ m := by
  classical
  have hne : Nonempty (Key 2 × (S × T)) := not_isEmpty_of_density hσ
  obtain ⟨⟨_, s0, t0⟩⟩ := hne
  have : Nonempty S := ⟨s0⟩
  have : Nonempty T := ⟨t0⟩
  set d := 2 ^ m with hd
  set s := Fintype.card (AReg n S) with hs
  set t := Fintype.card (AReg n T) with ht
  have hd0 : 0 < d := by positivity
  have hs0 : 0 < s := Fintype.card_pos
  have ht0 : 0 < t := Fintype.card_pos
  let eK : KeyO m ≃ Fin d := Fintype.equivFinOfCardEq (card_KeyO m)
  let eA : AReg n S ≃ Fin s := Fintype.equivFin _
  let eB : AReg n T ≃ Fin t := Fintype.equivFin _
  let eSh : InReg n S T ≃ Fin s × Fin t := eA.prodCongr eB
  let eγ : OutA m n S ≃ Fin (d * s) := (eK.prodCongr eA).trans (localIndex d s)
  let eδ : OutA m n T ≃ Fin (d * t) := (eK.prodCongr eB).trans (localIndex d t)
  let eα : AReg n S ≃ Fin (Fintype.card (Fin 2 × S) ^ n) := (decE S n).symm
  let eβ : AReg n T ≃ Fin (Fintype.card (Fin 2 × T) ^ n) := (decE T n).symm
  have hL := hΦ.encode eα eβ eγ eδ
  -- the input state
  have hin : (dimensionedPower (HorodeckiBoundKey.finCut σ) n).submatrix (Prod.map eα eβ)
      (Prod.map eα eβ) = powN (σ : Matrix (Cell S T) (Cell S T) ℂ) := by
    rw [dimensionedPower_finCut, submatrix_submatrix]
    have e : (eIn n S T) ∘ Prod.map eα eβ = regroupN n S T := by
      funext x
      obtain ⟨x1, x2⟩ := x
      simp only [Function.comp_apply, eIn, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
        eα, eβ]
      exact congrArg _ (Prod.ext ((decE S n).apply_symm_apply x1) ((decE T n).apply_symm_apply x2))
    rw [e]
    rfl
  -- the target private state
  let tau : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ := τ.submatrix eSh.symm eSh.symm
  have htau : IsDensityMatrix tau :=
    ⟨hτ.1.submatrix _, by simp only [tau]; rw [trace_submatrix_equiv, hτ.2]⟩
  have hU' : ∀ i : Fin d, ((U (eK.symm i)).submatrix eSh.symm eSh.symm) ∈
      Matrix.unitaryGroup (Fin s × Fin t) ℂ := by
    intro i
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, conjTranspose_submatrix,
      submatrix_mul_equiv, hU, submatrix_one_equiv]
  let U' : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ := fun i => ⟨_, hU' i⟩
  have hbp : bipartitePrivate tau U' = (Jgen U * τ * (Jgen U)ᴴ).submatrix
      (Prod.map eγ.symm eδ.symm) (Prod.map eγ.symm eδ.symm) := by
    ext x y
    simp only [bipartitePrivate, bipartitePrivateRaw,
      QAlgorithms.Papers.Independent.Information100.P67.privateState, submatrix_apply,
      Prod.map_fst, Prod.map_snd, Jgen_conj]
    have hx1 : eγ.symm x.1 = (eK.symm ((localIndex d s).symm x.1).1,
        eA.symm ((localIndex d s).symm x.1).2) := rfl
    have hx2 : eδ.symm x.2 = (eK.symm ((localIndex d t).symm x.2).1,
        eB.symm ((localIndex d t).symm x.2).2) := rfl
    have hy1 : eγ.symm y.1 = (eK.symm ((localIndex d s).symm y.1).1,
        eA.symm ((localIndex d s).symm y.1).2) := rfl
    have hy2 : eδ.symm y.2 = (eK.symm ((localIndex d t).symm y.2).1,
        eB.symm ((localIndex d t).symm y.2).2) := rfl
    rw [hx1, hx2, hy1, hy2]
    simp only [eK.symm.injective.eq_iff]
    split_ifs with hc
    · congr 1
      · simp [hd]
      · simp only [U', tau]
        rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_apply]
        rfl
    · rfl
  refine ⟨d, s, t, hd0, hs0, ht0, tau, htau, U', _, hL, ?_, rfl⟩
  rw [hin, hbp, ← submatrix_sub', show Prod.map ⇑eγ.symm ⇑eδ.symm = ⇑(eγ.prodCongr eδ).symm from rfl,
    traceNorm_submatrix_equiv]
  exact herr

end Achieve

end NPK

end Mod_NPK_Achieve

section Mod_NPK_Final
/-!
# Positive key from a state with corner norm close to `1/2`
-/

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open QAlgorithms.Papers.Independent.Gap48.P42 (KeyAchievable bipartitePrivate localIndex
  distillableKey)
open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower copyIndex)
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key keyBlock)
open scoped Matrix ComplexOrder Kronecker ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NPK

open Matrix FKR

/-! ### Arithmetic -/

lemma half_pow_mul (a b : ℕ) : ((1 / 2 : ℝ) ^ a) ^ b = (1 / 2 : ℝ) ^ (a * b) := (pow_mul _ _ _).symm

lemma ball_weight (n q : ℕ) (hq : 1 ≤ q) (hn' : n < 2048 * (q + 1)) :
    (1 / 2 : ℝ) ^ (32 * q + 16) ≤ (1 / 256 : ℝ) ^ (2 * q) * (1 - 1 / 256) ^ (n - 2 * q) := by
  have h1 : (1 / 256 : ℝ) ^ (2 * q) = (1 / 2 : ℝ) ^ (16 * q) := by
    rw [show (1 / 256 : ℝ) = (1 / 2) ^ 8 by norm_num, ← pow_mul]
    congr 1
    ring
  have hb : (1 / 2 : ℝ) ≤ (1 - 1 / 256 : ℝ) ^ 128 := by
    have := one_add_mul_le_pow (a := (-(1 / 256) : ℝ)) (by norm_num) 128
    norm_num at this ⊢ <;> linarith
  have h2 : (1 - 1 / 256 : ℝ) ^ (2048 * (q + 1)) ≤ (1 - 1 / 256 : ℝ) ^ (n - 2 * q) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h3 : (1 / 2 : ℝ) ^ (16 * q + 16) ≤ (1 - 1 / 256 : ℝ) ^ (2048 * (q + 1)) := by
    rw [show 2048 * (q + 1) = 128 * (16 * q + 16) by ring, pow_mul,
      show (1 / 2 : ℝ) ^ (16 * q + 16) = ((1 / 2 : ℝ)) ^ (16 * q + 16) from rfl]
    exact pow_le_pow_left₀ (by norm_num) hb _
  rw [h1, show 32 * q + 16 = 16 * q + (16 * q + 16) by ring, pow_add]
  exact mul_le_mul_of_nonneg_left (h3.trans h2) (by positivity)

lemma card_low_le (n q : ℕ) (hq : 1 ≤ q) (hn : 2048 * q ≤ n) (hn' : n < 2048 * (q + 1)) :
    ((lowSet n q).card : ℝ) ≤ (2 : ℝ) ^ (32 * q + 16) := by
  classical
  have hsub : lowSet n q ⊆ Finset.univ.filter fun v : Fin n → F2 => wt v ≤ 2 * q := by
    intro v hv
    simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have hc : ((lowSet n q).card : ℝ) ≤
      ((Finset.univ.filter fun v : Fin n → F2 => wt v ≤ 2 * q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hb := card_ball_le (n := n) (1 / 256) (by norm_num) (by norm_num) (2 * q) (by omega)
  have hw := ball_weight n q hq hn'
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (32 * q + 16) := by positivity
  have h2 : ((Finset.univ.filter fun v : Fin n → F2 => wt v ≤ 2 * q).card : ℝ) *
      (1 / 2 : ℝ) ^ (32 * q + 16) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hw (by positivity)) hb
  have h3 : ((Finset.univ.filter fun v : Fin n → F2 => wt v ≤ 2 * q).card : ℝ) ≤
      (2 : ℝ) ^ (32 * q + 16) := by
    have e : (2 : ℝ) ^ (32 * q + 16) * (1 / 2 : ℝ) ^ (32 * q + 16) = 1 := by
      rw [← mul_pow]; norm_num
    nlinarith
  exact hc.trans h3

lemma code_cond (n q : ℕ) (hq : 1 ≤ q) (hn : 2048 * q ≤ n) (hn' : n < 2048 * (q + 1)) :
    ((lowSet n q).card : ℝ) * ((1 / 2 : ℝ) ^ (512 * q) + (1 / 2) ^ (n - 512 * q) +
      (1 / 2) ^ (512 * q)) + (2 : ℝ) ^ (512 * q + 512 * q) * (1 / 2) ^ (n - 512 * q) < 1 := by
  have hc := card_low_le n q hq hn hn'
  have hA : (1 / 2 : ℝ) ^ (n - 512 * q) ≤ (1 / 2) ^ (512 * q) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hB : (2 : ℝ) ^ (512 * q + 512 * q) * (1 / 2) ^ (n - 512 * q) ≤ (1 / 2) ^ (512 * q) := by
    have h1 : (1 / 2 : ℝ) ^ (n - 512 * q) ≤ (1 / 2) ^ (1536 * q) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (512 * q + 512 * q) * (1 / 2) ^ (1536 * q) = (1 / 2) ^ (512 * q) := by
      rw [show 1536 * q = (512 * q + 512 * q) + 512 * q by ring,
        pow_add (1 / 2 : ℝ) (512 * q + 512 * q) (512 * q), ← mul_assoc, ← mul_pow]
      norm_num
    calc (2 : ℝ) ^ (512 * q + 512 * q) * (1 / 2) ^ (n - 512 * q)
        ≤ (2 : ℝ) ^ (512 * q + 512 * q) * (1 / 2) ^ (1536 * q) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := h2
  have hC : (2 : ℝ) ^ (32 * q + 16) * (1 / 2) ^ (512 * q) ≤ 2 ^ 16 * (1 / 2) ^ 480 := by
    have e : (2 : ℝ) ^ (32 * q + 16) * (1 / 2) ^ (512 * q) = 2 ^ 16 * (1 / 2) ^ (480 * q) := by
      rw [show 512 * q = 32 * q + 480 * q by ring, pow_add, pow_add]
      have : (2 : ℝ) ^ (32 * q) * (1 / 2) ^ (32 * q) = 1 := by rw [← mul_pow]; norm_num
      linear_combination (2 ^ 16 * (1 / 2 : ℝ) ^ (480 * q)) * this
    rw [e]
    have : (1 / 2 : ℝ) ^ (480 * q) ≤ (1 / 2) ^ 480 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hD : (1 / 2 : ℝ) ^ (512 * q) ≤ (1 / 2) ^ 512 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpos : (0 : ℝ) ≤ (1 / 2) ^ (512 * q) := by positivity
  have hsum : (1 / 2 : ℝ) ^ (512 * q) + (1 / 2) ^ (n - 512 * q) + (1 / 2) ^ (512 * q) ≤
      3 * (1 / 2) ^ (512 * q) := by linarith
  calc ((lowSet n q).card : ℝ) * ((1 / 2 : ℝ) ^ (512 * q) + (1 / 2) ^ (n - 512 * q) +
        (1 / 2) ^ (512 * q)) + (2 : ℝ) ^ (512 * q + 512 * q) * (1 / 2) ^ (n - 512 * q)
      ≤ (2 : ℝ) ^ (32 * q + 16) * (3 * (1 / 2) ^ (512 * q)) + (1 / 2) ^ (512 * q) := by
        gcongr
    _ = 3 * ((2 : ℝ) ^ (32 * q + 16) * (1 / 2) ^ (512 * q)) + (1 / 2) ^ (512 * q) := by ring
    _ ≤ 3 * (2 ^ 16 * (1 / 2) ^ 480) + (1 / 2) ^ 512 := by linarith
    _ < 1 := by
        have h1 : (1 / 2 : ℝ) ^ 480 ≤ (1 / 2) ^ 20 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
        have h2 : (1 / 2 : ℝ) ^ 512 ≤ (1 / 2) ^ 20 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
        have h3 : 3 * ((2 : ℝ) ^ 16 * (1 / 2) ^ 20) + (1 / 2) ^ 20 < 1 := by norm_num
        exact lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by norm_num)) h2) h3

lemma prob_arith (n q : ℕ) (hq : 1 ≤ q) (hn' : n < 2048 * (q + 1)) :
    (n : ℝ) * (1 / 8192) < q ∧
      1 - 4 / (q : ℝ) ≤ 1 - 2 * ((n : ℝ) * (1 / 8192) / ((q : ℝ) - n * (1 / 8192)) ^ 2) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hn'' : (n : ℝ) < 2048 * (q + 1) := by exact_mod_cast hn'
  have h1 : (n : ℝ) * (1 / 8192) ≤ q / 2 := by nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨by linarith, ?_⟩
  have h2 : (q : ℝ) / 2 ≤ q - n * (1 / 8192) := by linarith
  have h3 : ((q : ℝ) / 2) ^ 2 ≤ ((q : ℝ) - n * (1 / 8192)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have h4 : (n : ℝ) * (1 / 8192) / ((q : ℝ) - n * (1 / 8192)) ^ 2 ≤ (q / 2) / (q / 2) ^ 2 := by
    calc (n : ℝ) * (1 / 8192) / ((q : ℝ) - n * (1 / 8192)) ^ 2
        ≤ (q / 2) / ((q : ℝ) - n * (1 / 8192)) ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ (q / 2) / (q / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h3
  have h5 : ((q : ℝ) / 2) / (q / 2) ^ 2 = 2 / q := by
    field_simp
  rw [h5] at h4
  have : 2 * (2 / (q : ℝ)) = 4 / q := by ring
  linarith

lemma err_arith' (ε : ℝ) (hε : 0 < ε) (q : ℕ) (hq : 64 / ε ^ 2 + 16 / ε ≤ q) :
    2 * Real.sqrt (1 - (1 - 4 / (q : ℝ))) + 2 * (1 - (1 - 4 / (q : ℝ))) ≤ ε := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hq1 : 64 / ε ^ 2 ≤ q := by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 16) hε.le; linarith
  have hq2 : 16 / ε ≤ q := by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 64) hε2.le; linarith
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq1
  simp only [sub_sub_cancel]
  have ha : 4 / (q : ℝ) ≤ (ε / 4) ^ 2 := by
    rw [div_le_iff₀ hq0]
    rw [div_le_iff₀ hε2] at hq1
    nlinarith
  have hb : Real.sqrt (4 / (q : ℝ)) ≤ ε / 4 := by
    rw [show ε / 4 = Real.sqrt ((ε / 4) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt ha
  have hc : 4 / (q : ℝ) ≤ ε / 4 := by
    rw [div_le_iff₀ hq0]
    rw [div_le_iff₀ hε] at hq2
    nlinarith
  linarith

lemma rate_arith' (n q : ℕ) (hq : 1 ≤ q) (hn' : n < 2048 * (q + 1)) (hn0 : 0 < n) (δ : ℝ)
    (hδ : 0 < δ) : (1 / 8 : ℝ) - δ ≤ Real.logb 2 ((2 ^ (512 * q) : ℕ) : ℝ) / n := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hn'' : (n : ℝ) < 2048 * (q + 1) := by exact_mod_cast hn'
  have : (1 / 8 : ℝ) ≤ ((512 * q : ℕ) : ℝ) / n := by
    rw [le_div_iff₀ hn0']
    push_cast
    nlinarith
  linarith

/-! ### Error probabilities from the corner norm -/

section Marg

variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

lemma sum_mu_indX (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) (σ : Matrix (Cell S T) (Cell S T) ℂ) :
    ∑ l, mu Uc σ l * indX l = pBell Uc σ 1 0 + pBell Uc σ 1 1 := by
  rw [Fintype.sum_prod_type, sum_F2]
  simp only [indX, ne_eq, not_true_eq_false, if_false, mul_zero, Finset.sum_const_zero, zero_add,
    one_ne_zero, not_false_eq_true, if_true, mul_one]
  rw [Fintype.sum_prod_type, sum_F2]
  rfl

lemma sum_mu_indZ (Uc : F2 × F2 → Matrix (S × T) (S × T) ℂ) (σ : Matrix (Cell S T) (Cell S T) ℂ) :
    ∑ l, mu Uc σ l * indZ l = pBell Uc σ 0 1 + pBell Uc σ 1 1 := by
  rw [Fintype.sum_prod_type, sum_F2]
  simp only [Fintype.sum_prod_type (f := fun p : F2 × (S × T) => mu Uc σ (_, p) * indZ (_, p))]
  simp only [sum_F2 (fun z : F2 => ∑ y : S × T, mu Uc σ (_, z, y) * indZ (_, z, y))]
  simp only [indZ, ne_eq, not_true_eq_false, if_false, mul_zero, Finset.sum_const_zero, zero_add,
    one_ne_zero, not_false_eq_true, if_true, mul_one]
  rfl

end Marg

end NPK

open NPK in
theorem npk_main :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (S T : Type) [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
        (σ : Op (Key 2 × (S × T))), IsDensityMatrix σ →
        1 / 2 - ε₀ < traceNorm (keyBlock σ (0,0) (1,1)) →
        0 < distillableKey (HorodeckiBoundKey.finCut σ) := by
  refine ⟨1 / 16384, by norm_num, ?_⟩
  intro S T _ _ _ _ σ hσ hX
  classical
  set σc : Matrix (Cell S T) (Cell S T) ℂ := σ with hσc
  have hσc' : IsDensityMatrix σc := hσ
  obtain ⟨W, hW, hp00⟩ := squeeze_polar σc hσc'.1
  have hcorner : traceNorm (corner σc) = traceNorm (keyBlock σ (0,0) (1,1)) := rfl
  set V := Vsq W with hVdef
  have hV : ∀ c, (V c)ᴴ * V c = 1 := Vsq_unitary hW
  have hsum := pBell_sum (Ua V) (Ua_mul_conj hV) hσc'.2
  simp only [sum_F2] at hsum
  have hp01 := pBell_nonneg (Ua V) hσc'.1 0 1
  have hp10 := pBell_nonneg (Ua V) hσc'.1 1 0
  have hqx : ∑ l, mu (Ua V) σc l * indX l ≤ 1 / 8192 := by
    rw [sum_mu_indX]; linarith
  have hqz : ∑ l, mu (Ua V) σc l * indZ l ≤ 1 / 8192 := by
    rw [sum_mu_indZ]; linarith
  have hach : KeyAchievable (HorodeckiBoundKey.finCut σ) (1 / 8) := by
    refine ⟨by norm_num, fun ε hε δ hδ => ?_⟩
    obtain ⟨Q, hQ⟩ := exists_nat_gt (64 / ε ^ 2 + 16 / ε)
    refine ⟨2048 * (Q + 5), fun n hn hn0 => ?_⟩
    set q := n / 2048 with hqdef
    have hq5 : Q + 5 ≤ q := by
      rw [hqdef, Nat.le_div_iff_mul_le (by norm_num)]
      linarith
    have hq1 : 1 ≤ q := by omega
    have hqn : 2048 * q ≤ n := by rw [hqdef]; exact Nat.mul_div_le n 2048
    have hnq : n < 2048 * (q + 1) := by
      rw [hqdef]
      have := Nat.lt_div_mul_add (a := n) (b := 2048) (by norm_num)
      linarith
    obtain ⟨C⟩ := exists_goodCode (n := n) (r1 := 512 * q) (r2 := 512 * q) (m := 512 * q) (w := q)
      (n' := n - 512 * q) (by omega) (code_cond n q hq1 hqn hnq)
    obtain ⟨hqw, hpa⟩ := prob_arith n q hq1 hnq
    have hpG := good_prob (n := n) (mu (Ua V) σc) (mu_nonneg (Ua V) hσc'.1)
      (mu_sum (Ua_mul_conj hV) hσc'.2) q (1 / 8192) hqx hqz hqw
    have hq5' : (5 : ℝ) ≤ q := by exact_mod_cast (show 5 ≤ q by omega)
    have hp : (0 : ℝ) < 1 - 4 / (q : ℝ) := by
      have : 4 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    obtain ⟨τ, hτ, herr⟩ := one_shot C hV hσc' (1 - 4 / (q : ℝ)) hp (hpa.trans hpG)
    have hQq : 64 / ε ^ 2 + 16 / ε ≤ (q : ℝ) := by
      have : (Q : ℝ) ≤ q := by exact_mod_cast (show Q ≤ q by omega)
      linarith
    have herr2 := le_trans herr (err_arith' ε hε q hQq)
    rw [Jm_eq] at herr2
    obtain ⟨d, s, t, hd, hs, ht, tau, htau, U', L, hL, herr', hd'⟩ :=
      achieve σ hσ n (512 * q) (proto C) (proto_locc C) (Uout C V) (Uout_unitary C hV) τ hτ ε herr2
    refine ⟨d, s, t, hd, hs, ht, tau, htau, U', L, hL, herr', ?_⟩
    rw [hd']
    exact rate_arith' n q hq1 hnq hn0 δ hδ
  unfold distillableKey
  refine lt_of_lt_of_le ?_ (le_iSup_of_le (⟨1 / 8, hach⟩ : {r : ℝ // KeyAchievable _ r}) le_rfl)
  simp

end Mod_NPK_Final

section Final_Statement

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key keyBlock)
open QAlgorithms.Papers.Independent.Gap48.P42 (distillableKey)

theorem solution :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (S T : Type) [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
        (σ : Op (Key 2 × (S × T))), IsDensityMatrix σ →
        1 / 2 - ε₀ < traceNorm (keyBlock σ (0,0) (1,1)) →
        0 < distillableKey (HorodeckiBoundKey.finCut σ) :=
  npk_main

end Final_Statement
