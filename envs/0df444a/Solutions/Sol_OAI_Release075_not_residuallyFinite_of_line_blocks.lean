-- Prove2me | solution 1 for OAI.Release075.not_residuallyFinite_of_line_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:01:28.809643+00:00
-- url     : https://prove2.me/submissions/a5d9e3c7-1ff7-44c4-85bc-baedeb887ebd

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L921-L945
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.not_residuallyFinite_of_line_blocks. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Theorems.Thm_OAI_Release075_exists_finite_preserving_rectangles
import Theorems.Thm_OAI_Release075_finite_quotient_rank_obstruction
import Theorems.Thm_OAI_Release075_grid_line_certificate
import Theorems.Thm_OAI_Release075_quotientMatrix_sum_rank_le

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- Subadditivity of matrix rank over a field. -/
theorem rank_add_le {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (A B : Matrix ι κ K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- An arbitrary relabeling of a Cartesian block does not affect its summed
regular-representation matrix. Opposite-index shifts are permitted independently. -/
theorem quotientMatrix_sum_reindex {ι B s t F K : Type*} [Fintype B]
    [Fintype s] [Fintype t] [Group F] [Fintype F] [DecidableEq F] [Semiring K]
    (g : B → ι → ι → F) (L : ι → s → F) (R : ι → t → F)
    (e : ι → ι → B ≃ s × t)
    (h : ∀ i u v, g i u v = (L u (e u v i).1)⁻¹ * R v (e u v i).2) :
    (∑ i, quotientMatrix (R := K) (g i)) =
      ∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k) := by
  ext ⟨u,a⟩ ⟨v,b⟩
  simp only [Matrix.sum_apply, quotientMatrix, flattenMatrix_apply, Matrix.of_apply, h]
  exact (Equiv.sum_comp (e u v) (fun p : s × t =>
    (regularMatrix (R := K) ((L u p.1)⁻¹ * R v p.2)) a b)).trans
      (Fintype.sum_prod_type _)

theorem CartesianBlock.quotient_rank_le {I F K : Type*} {r : ℕ}
    [Group F] [Fintype F] [DecidableEq F] [Field K]
    (b : CartesianBlock I r) (g : I → Fin r → Fin r → F)
    (L : Fin r → ZMod b.s → F) (R : Fin r → ZMod b.t → F)
    (hrel : ∀ (i : b.labels) u v,
      g i u v = (L u ((b.coordinates i).1 + (v.val : ZMod b.s)))⁻¹ *
        R v ((b.coordinates i).2 + (u.val : ZMod b.t))) :
    (∑ i ∈ b.labels, quotientMatrix (R := K) (g i)).rank ≤ Fintype.card F := by
  classical
  rw [Finset.sum_subtype b.labels (fun _ => Iff.rfl)]
  rw [quotientMatrix_sum_reindex (fun i : b.labels => g i) L R b.shifted hrel]
  exact quotientMatrix_sum_rank_le L R

theorem CartesianBlock.Relations.map {I G F : Type*} [Group G] [Group F] {r : ℕ}
    {b : CartesianBlock I r} {g : I → Fin r → Fin r → G}
    (h : b.Relations g) (φ : G →* F) : b.Relations (fun i u v => φ (g i u v)) := by
  obtain ⟨L,R,hrel⟩ := h
  refine ⟨fun u j => φ (L u j), fun v k => φ (R v k), ?_⟩
  intros
  simp [hrel]

theorem two_block_quotient_rank_le {I F K : Type*} [DecidableEq I]
    [Group F] [Fintype F] [DecidableEq F] [Field K] {r : ℕ}
    (A : Finset I) (g : I → Fin r → Fin r → F)
    (b₀ b₁ : CartesianBlock I r)
    (hdis : Disjoint b₀.labels b₁.labels) (hunion : b₀.labels ∪ b₁.labels = A)
    (h₀ : b₀.Relations g) (h₁ : b₁.Relations g) :
    (∑ i ∈ A, quotientMatrix (R := K) (g i)).rank ≤ 2 * Fintype.card F := by
  obtain ⟨L₀,R₀,h₀⟩ := h₀
  obtain ⟨L₁,R₁,h₁⟩ := h₁
  rw [← hunion, Finset.sum_union hdis]
  have h := (rank_add_le _ _).trans (Nat.add_le_add
    (b₀.quotient_rank_le (K := K) g L₀ R₀ h₀)
    (b₁.quotient_rank_le (K := K) g L₁ R₁ h₁))
  simpa [two_mul] using h

theorem not_residuallyFinite_of_line_blocks {T I G : Type*}
    [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] [Group G]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (S : Finset (ZMod q)) (a v : I → T → ZMod q)
    (ha : ∀ i t, a i t ∈ S) (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < q - 1)
    (E : Finset (T → ZMod q)) (g : I → Fin r → Fin r → G)
    (hg : ∀ i, RectanglesSurvive (g i))
    (hblocks : ∀ z, z ∉ E → ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = lineIncidence a v z ∧
      b₀.Relations g ∧ b₁.Relations g)
    (hbudget : 4 * (2 * Fintype.card (T → ZMod q) + r * E.card) < Fintype.card I * r) :
    ¬ Group.ResiduallyFinite G := by
  classical
  intro hRF
  let := hRF
  obtain ⟨Q,hQ,hfin,φ,hφ⟩ := exists_finite_preserving_rectangles g hg
  let := hQ
  let := hfin
  apply finite_quotient_rank_obstruction r q hq (lineIncidence a v)
    (fun z i => gridLagrange S (a i) z) E (fun i u v => φ (g i u v)) hφ
    (grid_line_certificate S a v ha hinj hv (by simpa using hdeg)) _ hbudget
  intro z hz
  obtain ⟨b₀,b₁,hd,hu,h₀,h₁⟩ := hblocks z hz
  exact two_block_quotient_rank_le _ _ b₀ b₁ hd hu (h₀.map φ) (h₁.map φ)

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.not_residuallyFinite_of_line_blocks := @_root_.OAI.Release075.not_residuallyFinite_of_line_blocks
