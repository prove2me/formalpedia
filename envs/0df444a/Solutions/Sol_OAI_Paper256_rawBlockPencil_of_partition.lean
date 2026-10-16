-- Prove2me | solution 1 for OAI.Paper256.rawBlockPencil_of_partition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:12:13.024584+00:00
-- url     : https://prove2.me/submissions/3f768069-f9ff-463e-ab3c-934c34fdf1d8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SplitAssembly.lean:L51-L88
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.rawBlockPencil_of_partition. The node keeps its source
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

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.SplitAssembly ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem pencil_reindex_blocks {m a c : ℕ} (L : Ambient →ₗ[ℝ] Sym m)
    (e : (Fin a ⊕ Fin c) ≃ Fin m)
    (hrow : ∀ (X : Sym 4) (i : Fin c) (j : Fin m),
      (pencilFirst L X : Mat m ℝ) (e (Sum.inr i)) j = 0)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    (L ((X, Z), y) : Mat m ℝ).submatrix e e =
      Matrix.fromBlocks
        ((pencilFirst L X : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl) +
         (pencilSecond L Z : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl) +
         (pencilParameter L y : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
        ((pencilSecond L Z : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr) +
         (pencilParameter L y : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))
        (((pencilSecond L Z : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr) +
          (pencilParameter L y : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))ᵀ)
        ((pencilSecond L Z : Mat m ℝ).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr) +
         (pencilParameter L y : Mat m ℝ).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
  have hdec (i j : Fin m) : (L ((X, Z), y) : Mat m ℝ) i j =
      (pencilFirst L X : Mat m ℝ) i j + (pencilSecond L Z : Mat m ℝ) i j +
      (pencilParameter L y : Mat m ℝ) i j := by
    rw [pencil_decomposition]
    rfl
  have hcol (i : Fin m) (j : Fin c) :
      (pencilFirst L X : Mat m ℝ) i (e (Sum.inr j)) = 0 := by
    have hh := (sym_isHermitian (pencilFirst L X)).apply (e (Sum.inr j)) i
    simpa using hh.trans (hrow X j i)
  have hs (H : Sym m) (i j : Fin m) : (H : Mat m ℝ) i j = (H : Mat m ℝ) j i := by
    simpa using (sym_isHermitian H).apply j i
  ext (i | i) (j | j)
  · exact hdec _ _
  · change (L ((X, Z), y) : Mat m ℝ) _ _ = _ + _
    rw [hdec, hcol, zero_add]
    rfl
  · change (L ((X, Z), y) : Mat m ℝ) _ _ = _ + _
    rw [hdec, hrow, zero_add, hs (pencilSecond L Z), hs (pencilParameter L y)]
    rfl
  · change (L ((X, Z), y) : Mat m ℝ) _ _ = _ + _
    rw [hdec, hrow, zero_add]
    rfl

theorem rawBlockPencil_of_partition {m a c : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (ha : 0 < a) (hc : 0 < c)
    (e : (Fin a ⊕ Fin c) ≃ Fin m)
    (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hfirst : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef →
      (pencilFirst L X : Mat m ℝ).PosSemidef)
    (hsecond : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef →
      (pencilSecond L X : Mat m ℝ).PosSemidef)
    (hrow : ∀ (X : Sym 4) (i : Fin c) (j : Fin m),
      (pencilFirst L X : Mat m ℝ) (e (Sum.inr i)) j = 0)
    (hD : ((pencilFirst L 1 : Mat m ℝ).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).PosDef)
    (hE : ((pencilSecond L 1 : Mat m ℝ).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)).PosDef) :
    Nonempty (RawBlockPencil K) := by
  let f := e ∘ Sum.inl
  let g := e ∘ Sum.inr
  refine ⟨{
    a := a
    c := c
    a_pos := ha
    c_pos := hc
    D := restrictPencil (pencilFirst L) f
    E := restrictPencil (pencilSecond L) g
    F := restrictPencil (pencilSecond L) f
    C := rectangularPencil (pencilSecond L) f g
    A := restrictPencil (pencilParameter L) f
    B := rectangularPencil (pencilParameter L) f g
    G := restrictPencil (pencilParameter L) g
    D_positive := fun X hX => (hfirst X hX).submatrix f
    E_positive := fun X hX => (hsecond X hX).submatrix g
    D_identity_posDef := hD
    E_identity_posDef := hE
    represents := ?_ }⟩
  intro X Z y
  rw [hrep]
  change (L ((X, Z), y) : Mat m ℝ).PosSemidef ↔ _
  rw [← Matrix.posSemidef_submatrix_equiv e,
    pencil_reindex_blocks L e hrow X Z y]
  rfl

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.rawBlockPencil_of_partition := @_root_.OAI.Paper256.rawBlockPencil_of_partition
