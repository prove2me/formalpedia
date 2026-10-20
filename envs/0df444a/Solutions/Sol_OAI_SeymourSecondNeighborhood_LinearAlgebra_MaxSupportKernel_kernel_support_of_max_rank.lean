-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel.kernel_support_of_max_rank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:11:49.423036+00:00
-- url     : https://prove2.me/submissions/e976e447-2ed0-48a4-ba82-65cb384a25d4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MaxSupportKernel.lean:L57-L84
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel.kernel_support_of_max_rank. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel

-- ---- from OAI.Combinatorics.SecondNeighborhood.MaxSupportKernel ----
namespace OAI

namespace SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel

open Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

theorem range_lt_range_add_single [DecidableEq I] [DecidableEq J]
    (D : Matrix I J ℝ) {x : J → ℝ} {y : I → ℝ}
    (hx : D *ᵥ x = 0) (hy : Dᵀ *ᵥ y = 0)
    (s : I) (j : J) (hxj : x j ≠ 0) (hys : y s ≠ 0) :
    LinearMap.range D.mulVecLin <
      LinearMap.range (D + Matrix.single s j (1 : ℝ)).mulVecLin := by
  let E : Matrix I J ℝ := D + Matrix.single s j 1
  let e : I → ℝ := Pi.single s 1
  change LinearMap.range D.mulVecLin < LinearMap.range E.mulVecLin
  have hsingle (w : J → ℝ) :
      Matrix.single s j (1 : ℝ) *ᵥ w = w j • e := by
    ext i
    simp [Matrix.single_mulVec, Function.update_apply, Pi.single_apply, e]
  have hEw (w : J → ℝ) :
      E.mulVecLin w = D.mulVecLin w + w j • e := by
    change (D + Matrix.single s j (1 : ℝ)) *ᵥ w = D *ᵥ w + w j • e
    rw [Matrix.add_mulVec, hsingle]
  have hEx : E.mulVecLin x = x j • e := by
    rw [hEw]
    change D *ᵥ x + x j • e = x j • e
    rw [hx, zero_add]
  have he : e ∈ LinearMap.range E.mulVecLin := by
    have hm : x j • e ∈ LinearMap.range E.mulVecLin := ⟨x, hEx⟩
    have hs := (LinearMap.range E.mulVecLin).smul_mem (x j)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hxj, one_smul] using hs
  have hle : LinearMap.range D.mulVecLin ≤ LinearMap.range E.mulVecLin := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    have hm : E.mulVecLin w ∈ LinearMap.range E.mulVecLin := ⟨w, rfl⟩
    have hs := (LinearMap.range E.mulVecLin).sub_mem hm
      ((LinearMap.range E.mulVecLin).smul_mem (w j) he)
    rw [hEw] at hs
    simpa only [add_sub_cancel_right] using hs
  have hnot : e ∉ LinearMap.range D.mulVecLin := by
    rintro ⟨w, hw⟩
    have ha : dotProduct y (D.mulVecLin w) = 0 := by
      change dotProduct y (D *ᵥ w) = 0
      rw [← Matrix.dotProduct_transpose_mulVec D w y, hy, dotProduct_zero]
    rw [hw] at ha
    exact hys (by simpa [e] using ha)
  exact lt_iff_le_not_ge.mpr ⟨hle, fun hge => hnot (hge he)⟩

theorem kernel_support_of_max_rank {T : Set (I × J)} {D : Matrix I J ℝ}
    (hD : SupportedOn T D)
    (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)
    {x : J → ℝ} {y : I → ℝ}
    (hx : D *ᵥ x = 0) (hy : Dᵀ *ᵥ y = 0)
    {s : I} {j : J} (hsj : (s, j) ∈ T) :
    x j * y s = 0 := by
  classical
  by_contra hxy
  have hxj : x j ≠ 0 := by
    intro h
    exact hxy (by rw [h, zero_mul])
  have hys : y s ≠ 0 := by
    intro h
    exact hxy (by rw [h, mul_zero])
  have hsupport : SupportedOn T (D + Matrix.single s j (1 : ℝ)) := by
    intro i k hik
    have hne : ¬(s = i ∧ j = k) := by
      rintro ⟨rfl, rfl⟩
      exact hik hsj
    change D i k + Matrix.single s j (1 : ℝ) i k = 0
    rw [hD i k hik, Matrix.single_apply_of_ne s j (1 : ℝ) i k hne, zero_add]
  have hlt : D.rank < (D + Matrix.single s j (1 : ℝ)).rank := by
    change Module.finrank ℝ (LinearMap.range D.mulVecLin) <
      Module.finrank ℝ (LinearMap.range (D + Matrix.single s j (1 : ℝ)).mulVecLin)
    exact Submodule.finrank_lt_finrank_of_lt
      (range_lt_range_add_single D hx hy s j hxj hys)
  exact (not_lt_of_ge (hmax _ hsupport)) hlt

end SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.LinearAlgebra OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel
open Matrix


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel.kernel_support_of_max_rank := @_root_.OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel.kernel_support_of_max_rank
