-- Prove2me | solution 1 for OAI.Paper256.pencil_compression_positive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:54:12.216077+00:00
-- url     : https://prove2.me/submissions/fbaafd43-bf4f-4036-8bed-46d5aa8b6883

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilCompression.lean:L54-L72
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.pencil_compression_positive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Theorems.Thm_OAI_Paper256_matrix_compression_posSemidef_iff

-- ---- from OAI.Analysis.HyperbolicCones.PencilConjugation ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

theorem conjugatePencil_posSemidef_iff {n : ℕ} (L : V →ₗ[ℝ] Sym n)
    (U : Mat n ℝ) (hU : IsUnit U) (x : V) :
    (conjugatePencil L U x : Mat n ℝ).PosSemidef ↔ (L x : Mat n ℝ).PosSemidef := by
  change (Uᴴ * (L x : Mat n ℝ) * U).PosSemidef ↔ _
  simpa only [Matrix.star_eq_conjTranspose] using hU.posSemidef_star_left_conjugate_iff

theorem spectral_conjugate_diagonal {n : ℕ} (A : Sym n) :
    ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)ᴴ * (A : Mat n ℝ) *
      ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ) = Matrix.diagonal (sym_isHermitian A).eigenvalues := by
  simpa [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def] using (sym_isHermitian A).conjStarAlgAut_star_eigenvectorUnitary

theorem spectral_conjugate_zero_column {n : ℕ} (A B : Sym n)
    (hA : (A : Mat n ℝ).PosSemidef)
    (hker : ∀ v : Fin n → ℝ, (A : Mat n ℝ) *ᵥ v = 0 → (B : Mat n ℝ) *ᵥ v = 0)
    (i : Fin n) (hi : ¬ 0 < (sym_isHermitian A).eigenvalues i) (j : Fin n) :
    (((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)ᴴ * (B : Mat n ℝ) *
      ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)) j i = 0 := by
  let U : Mat n ℝ := (sym_isHermitian A).eigenvectorUnitary
  have heig : (sym_isHermitian A).eigenvalues i = 0 :=
    le_antisymm (le_of_not_gt hi) (hA.eigenvalues_nonneg i)
  have ha : (A : Mat n ℝ) *ᵥ (U *ᵥ Pi.single i 1) = 0 := by
    rw [show U *ᵥ Pi.single i 1 = ⇑((sym_isHermitian A).eigenvectorBasis i) from
      (sym_isHermitian A).eigenvectorUnitary_mulVec i]
    rw [(sym_isHermitian A).mulVec_eigenvectorBasis, heig, zero_smul]
  have hb := hker (U *ᵥ Pi.single i 1) ha
  have hz : (Uᴴ * (B : Mat n ℝ) * U) *ᵥ Pi.single i 1 = 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hb, mulVec_zero]
  have hv := congrFun hz j
  simpa using hv

theorem spectral_conjugate_zero_row {n : ℕ} (A B : Sym n)
    (hA : (A : Mat n ℝ).PosSemidef)
    (hker : ∀ v : Fin n → ℝ, (A : Mat n ℝ) *ᵥ v = 0 → (B : Mat n ℝ) *ᵥ v = 0)
    (i : Fin n) (hi : ¬ 0 < (sym_isHermitian A).eigenvalues i) (j : Fin n) :
    (((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)ᴴ * (B : Mat n ℝ) *
      ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)) i j = 0 := by
  have hh := Matrix.isHermitian_conjTranspose_mul_mul
    ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ) B.property
  have hs := hh.apply j i
  have hz := spectral_conjugate_zero_column A B hA hker i hi j
  simpa using hs.trans hz

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PencilCompression ----
namespace OAI

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

theorem pencil_compression {n : ℕ} (L : V →ₗ[ℝ] Sym n) (e : V)
    (he : (L e : Mat n ℝ).PosSemidef)
    (hker : ∀ x : V, ∀ v : Fin n → ℝ,
      (L e : Mat n ℝ) *ᵥ v = 0 → (L x : Mat n ℝ) *ᵥ v = 0) :
    ∃ m : ℕ, ∃ C : V →ₗ[ℝ] Sym m,
      (C e : Mat m ℝ).PosDef ∧
      ∀ x : V, (L x : Mat n ℝ).PosSemidef ↔ (C x : Mat m ℝ).PosSemidef := by
  classical
  let p : Fin n → Prop := fun i => 0 < (sym_isHermitian (L e)).eigenvalues i
  let J := {i : Fin n // p i}
  let m := Fintype.card J
  let q : Fin m ≃ J := (Fintype.equivFin J).symm
  let f : Fin m → Fin n := fun i => (q i).val
  let U : Mat n ℝ := (sym_isHermitian (L e)).eigenvectorUnitary
  let T := conjugatePencil L U
  let C := restrictPencil T f
  have hf : Function.Injective f := Subtype.val_injective.comp q.injective
  refine ⟨m, C, ?_, ?_⟩
  · change ((Uᴴ * (L e : Mat n ℝ) * U).submatrix f f).PosDef
    rw [spectral_conjugate_diagonal (L e), Matrix.submatrix_diagonal _ f hf]
    exact Matrix.PosDef.diagonal fun i => (q i).property
  · intro x
    have hT : (T x : Mat n ℝ).IsHermitian := (T x).property
    have hzero : ∀ i, ¬p i → ∀ j, (T x : Mat n ℝ) i j = 0 := by
      intro i hi j
      exact spectral_conjugate_zero_row (L e) (L x) he (hker x) i hi j
    have hp := matrix_compression_posSemidef_iff p (T x : Mat n ℝ) hT hzero
    have hq := Matrix.posSemidef_submatrix_equiv
      (M := (T x : Mat n ℝ).submatrix (Subtype.val : J → Fin n) Subtype.val) q
    calc
      (L x : Mat n ℝ).PosSemidef ↔ (T x : Mat n ℝ).PosSemidef :=
        (conjugatePencil_posSemidef_iff L U
          (Unitary.isUnit_coe (U := (sym_isHermitian (L e)).eigenvectorUnitary)) x).symm
      _ ↔ ((T x : Mat n ℝ).submatrix (Subtype.val : J → Fin n) Subtype.val).PosSemidef := hp
      _ ↔ (C x : Mat m ℝ).PosSemidef := by
        simpa [C, restrictPencil, f, Matrix.submatrix_submatrix, Function.comp_def] using hq.symm

theorem pencil_compression_positive {n : ℕ} (L : V →ₗ[ℝ] Sym n) (e : V)
    (he : (L e : Mat n ℝ).PosSemidef)
    (hker : ∀ x : V, ∀ v : Fin n → ℝ,
      (L e : Mat n ℝ) *ᵥ v = 0 → (L x : Mat n ℝ) *ᵥ v = 0)
    (hproper : ∃ x : V, ¬(L x : Mat n ℝ).PosSemidef) :
    ∃ m : ℕ, 0 < m ∧ ∃ C : V →ₗ[ℝ] Sym m,
      (C e : Mat m ℝ).PosDef ∧
      ∀ x : V, (L x : Mat n ℝ).PosSemidef ↔ (C x : Mat m ℝ).PosSemidef := by
  obtain ⟨m, C, hC, hrep⟩ := pencil_compression L e he hker
  refine ⟨m, ?_, C, hC, hrep⟩
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  obtain ⟨x, hx⟩ := hproper
  apply hx
  apply (hrep x).mpr
  have hz : (C x : Mat 0 ℝ) = 0 := Subsingleton.elim _ _
  rw [hz]
  exact Matrix.PosSemidef.zero

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Matrix Set
open scoped Matrix.Norms.L2Operator


theorem solution.{u} : type_of% @_root_.OAI.Paper256.pencil_compression_positive.{u} := @_root_.OAI.Paper256.pencil_compression_positive.{u}
