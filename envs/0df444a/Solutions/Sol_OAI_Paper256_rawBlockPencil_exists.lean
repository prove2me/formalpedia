-- Prove2me | solution 1 for OAI.Paper256.rawBlockPencil_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:13:31.510671+00:00
-- url     : https://prove2.me/submissions/15756d67-c137-46da-bec2-36c05d1cfd6c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilSplit.lean:L13-L65
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.rawBlockPencil_exists. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Theorems.Thm_OAI_Paper256_pencilSpectralSplit_exists
import Theorems.Thm_OAI_Paper256_pencil_first_identity_ne_zero
import Theorems.Thm_OAI_Paper256_pencil_first_identity_not_posDef
import Theorems.Thm_OAI_Paper256_positiveLinearMap_common_kernel
import Theorems.Thm_OAI_Paper256_rawBlockPencil_of_partition

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

-- ---- from OAI.Analysis.HyperbolicCones.SplitBasic ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem pencil_decomposition {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    L ((X, Z), y) = pencilFirst L X + pencilSecond L Z + pencilParameter L y := by
  change L ((X, Z), y) = L ((X, 0), 0) + L ((0, Z), 0) + L ((0, 0), y)
  rw [← map_add, ← map_add]
  simp

theorem pencil_components_positive {m : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    (∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (pencilFirst L X : Mat m ℝ).PosSemidef) ∧
    (∀ Z : Sym 4, (Z : Mat 4 ℝ).PosSemidef → (pencilSecond L Z : Mat m ℝ).PosSemidef) := by
  constructor
  · intro X hX
    have h := (hzero X 0).mpr ⟨hX, Matrix.PosSemidef.zero⟩
    simpa only [hrep, mem_ofPred_eq] using! h
  · intro Z hZ
    have h := (hzero 0 Z).mpr ⟨Matrix.PosSemidef.zero, hZ⟩
    simpa only [hrep, mem_ofPred_eq] using! h

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.SplitFrame ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem conjugatePencil_posDef {V : Type u} [AddCommGroup V] [Module ℝ V]
    {m : ℕ} (L : V →ₗ[ℝ] Sym m) (U : Mat m ℝ) (hU : IsUnit U) (x : V)
    (hx : (L x : Mat m ℝ).PosDef) : (conjugatePencil L U x : Mat m ℝ).PosDef := by
  change (Uᴴ * (L x : Mat m ℝ) * U).PosDef
  exact hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hU)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PencilSplit ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem rawBlockPencil_exists {m : ℕ} (K : Set Ambient)
    (C : Ambient →ₗ[ℝ] Sym m) (hC : (C basePoint : Mat m ℝ).PosDef)
    (hrep : K = {x | (C x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    Nonempty (RawBlockPencil K) := by
  classical
  let A := pencilFirst C 1
  have hfirst := (pencil_components_positive K C hrep hzero).1
  have hA : (A : Mat m ℝ).PosSemidef := hfirst 1 Matrix.PosSemidef.one
  obtain ⟨S⟩ := pencilSpectralSplit_exists A hA
    (pencil_first_identity_ne_zero K C hrep hzero)
    (pencil_first_identity_not_posDef K C hrep hzero)
  let U : Mat m ℝ := (sym_isHermitian A).eigenvectorUnitary
  have hU : IsUnit U := Unitary.isUnit_coe (U := (sym_isHermitian A).eigenvectorUnitary)
  let L := conjugatePencil C U
  have hrepL : K = {x | (L x : Mat m ℝ).PosSemidef} := by
    ext x
    rw [hrep]
    exact (conjugatePencil_posSemidef_iff C U hU x).symm
  have hpos := pencil_components_positive K L hrepL hzero
  have hrow (X : Sym 4) (i : Fin S.c) (j : Fin m) :
      (pencilFirst L X : Mat m ℝ) (S.index (Sum.inr i)) j = 0 := by
    exact spectral_conjugate_zero_row A (pencilFirst C X) hA
      (positiveLinearMap_common_kernel (pencilFirst C) hfirst X)
      _ (S.nonpositive i) j
  let f := S.index ∘ Sum.inl
  let g := S.index ∘ Sum.inr
  have hf : Function.Injective f := S.index.injective.comp Sum.inl_injective
  have hg : Function.Injective g := S.index.injective.comp Sum.inr_injective
  have hD : ((pencilFirst L 1 : Mat m ℝ).submatrix f f).PosDef := by
    change ((Uᴴ * (A : Mat m ℝ) * U).submatrix f f).PosDef
    rw [spectral_conjugate_diagonal A, Matrix.submatrix_diagonal _ f hf]
    exact Matrix.PosDef.diagonal S.positive
  have hbase : (L basePoint : Mat m ℝ).PosDef := conjugatePencil_posDef C U hU basePoint hC
  have hE : ((pencilSecond L 1 : Mat m ℝ).submatrix g g).PosDef := by
    have heq : (L basePoint : Mat m ℝ).submatrix g g =
        (pencilSecond L 1 : Mat m ℝ).submatrix g g := by
      ext i j
      change (L (((1, 1), 0) : Ambient) : Mat m ℝ) (g i) (g j) = _
      rw [pencil_decomposition]
      change (pencilFirst L 1 : Mat m ℝ) (g i) (g j) +
        (pencilSecond L 1 : Mat m ℝ) (g i) (g j) +
        (pencilParameter L 0 : Mat m ℝ) (g i) (g j) = _
      rw [map_zero]
      change (pencilFirst L 1 : Mat m ℝ) (S.index (Sum.inr i)) (g j) +
        (pencilSecond L 1 : Mat m ℝ) (g i) (g j) + 0 =
        (pencilSecond L 1 : Mat m ℝ) (g i) (g j)
      rw [hrow, zero_add, add_zero]
    rw [← heq]
    exact hbase.submatrix hg
  exact rawBlockPencil_of_partition K L S.a_pos S.c_pos S.index hrepL
    hpos.1 hpos.2 hrow hD hE

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.rawBlockPencil_exists := @_root_.OAI.Paper256.rawBlockPencil_exists
