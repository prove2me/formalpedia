-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.lower_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:23.790358+00:00
-- url     : https://prove2.me/submissions/552cf8b4-73df-4314-9c76-fdf67fd51842

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational
import Theorems.Thm_GlobalTheory_Reg_CellChange_minors_iff
import Theorems.Thm_GlobalTheory_cell_coordinates_exists_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.CellChange
open Matrix
namespace GlobalTheory.Reg.CellChange
theorem _root_.solution {F K : Type} [Field F] [Field K] (φ : F →+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (l b : Matrix (Fin n) (Fin n) K) (h0 : ∀ i j : Fin n, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) (h : M.map φ = l * b) (i j : Fin n) :
    ∃ x, φ x = l i j := by
  have hm := (minors_iff (M.map φ)).2 ⟨l, b, h0, h1, hb, hu, h⟩
  obtain ⟨u, c, hu0, hu1, hc, hcu, hM⟩ := (minors_iff M).1 (fun k hk => by
    have h2 := hm k hk
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    rw [isUnit_iff_ne_zero] at h2 ⊢
    intro h3
    exact h2 (by rw [h3, map_zero]))
  have := (GlobalTheory.cell_coordinates_exists_unique K n n (Function.Embedding.refl _) l).2 l (u.map φ) b (c.map φ)
    ⟨h0, h1⟩ ⟨fun i j hij => by simpa using hu0 i j hij, fun i => by simp [hu1 i]⟩ hb
    (hc.map φ) hu (by rw [← h, hM, Matrix.map_mul])
  exact ⟨u i j, by rw [this.1]; rfl⟩
end GlobalTheory.Reg.CellChange
