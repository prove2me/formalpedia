-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.minors_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:25.53296+00:00
-- url     : https://prove2.me/submissions/d4f0e984-855c-4a11-b774-c75264e35d74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational
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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    (∀ k (hk : k ≤ n), IsUnit (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) ↔
      ∃ u b : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b :=
  (GlobalTheory.cell_coordinates_exists_unique R n n (Function.Embedding.refl _) g).1
end GlobalTheory.Reg.CellChange
