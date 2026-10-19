-- Prove2me | solution 1 for OAI.MainGap.Stable.block_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:38:23.778409+00:00
-- url     : https://prove2.me/submissions/6692cb10-2477-4b57-bbf6-e31497b77e9d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/MatrixEntries.lean:L145-L163
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.Stable.block_conjugate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Diagonalization
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_MatrixEntries

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.MatrixEntries ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap.Stable
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.Stable.matrixEntryOrder
attribute [local instance] OAI.MainGap.Stable.matrixEntryStarOrder
attribute [local instance] OAI.MainGap.Stable.algebraicTopology'
lemma continuous_entry (i j : ℕ) : Continuous (entry (A := A) i j) :=
  UniformSpace.Completion.continuous_extension

lemma continuous_block (m n : ℕ) : Continuous (block (A := A) m n) := by
  exact continuous_pi fun i => continuous_pi fun j => (continuous_entry i.val j.val)

end MainGap.Stable

namespace MainGap.Stable
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.Stable.blockConjugateOrder
attribute [local instance] OAI.MainGap.Stable.blockConjugateStarOrder
attribute [local instance] OAI.MainGap.Stable.algebraicTopology''
lemma paddedEntry_star (i j n : ℕ) (x : Mat A n) :
    paddedEntry i j n (star x) = star (paddedEntry j i n x) := by
  by_cases hi : i < n <;> by_cases hj : j < n <;>
    simp [paddedEntry, hi, hj, CStarMatrix.star_apply]

lemma paddedEntry_mul (i j n : ℕ) (x y : Mat A n) :
    paddedEntry i j n (x*y) =
      ∑ k : Fin n, paddedEntry i k.val n x * paddedEntry k.val j n y := by
  by_cases hi : i < n <;> by_cases hj : j < n <;>
    simp [paddedEntry, hi, hj, CStarMatrix.mul_apply]

lemma paddedEntry_conjugate (i j : ℕ) {m N : ℕ} (h : m ≤ N)
    (z : Mat A N) (v : Mat A m) :
    paddedEntry i j N (star z * pad h v * z) =
      ∑ q : Fin m, ∑ p : Fin m,
        star (paddedEntry p.val i N z) * v p q * paddedEntry q.val j N z := by
  classical
  simp only [paddedEntry_mul, paddedEntry_star, paddedEntry_pad]
  rw [← sum_pad h (fun q : Fin m => ∑ p : Fin m,
      star (paddedEntry p.val i N z) * v p q * paddedEntry q.val j N z)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.val < m
  · rw [dite_eq_left hq, Finset.sum_mul]
    rw [← sum_pad h (fun p : Fin m =>
      star (paddedEntry p.val i N z) * v p ⟨q,hq⟩ * paddedEntry q.val j N z)]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.val < m <;> simp [paddedEntry, hp, hq]
  · simp [paddedEntry, hq]

lemma block_conjugate_corner {m N : ℕ} (h : m ≤ N) (n : ℕ)
    (v : Mat A m) (z : Mat A N) :
    block n n (star (corner N z) * corner m v * corner N z) =
      (block m n (corner N z)).conjTranspose * v * block m n (corner N z) := by
  rw [← corner_pad h v]
  have he : star (corner N z) * corner N (pad h v) * corner N z =
      corner N (star z * pad h v * z) := by rw [map_mul, map_mul, map_star]
  rw [he]
  ext i j
  simp only [block_apply, entry_corner, CStarMatrix.mul_apply,
    CStarMatrix.conjTranspose_apply, Finset.sum_mul]
  exact paddedEntry_conjugate i.val j.val h z v

lemma block_conjugate (m n : ℕ) (v : Mat A m) (x : Stabilization A) :
    block n n (star x * corner m v * x) =
      (block m n x).conjTranspose * v * block m n x := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · apply isClosed_eq
    · exact (continuous_block n n).comp ((continuous_star.mul continuous_const).mul continuous_id)
    · have hc : Continuous (fun x : Stabilization A => (block m n x).conjTranspose) := by
        change Continuous (fun x : Stabilization A =>
          fun i j => star (block m n x j i))
        exact continuous_pi fun i => continuous_pi fun j =>
          continuous_star.comp (continuous_entry j.val i.val)
      exact (hc.matrix_mul continuous_const).matrix_mul (continuous_block m n)
  · intro z
    induction z using DirectLimit.induction with
    | ih k z =>
      change block n n (star (corner k z) * corner m v * corner k z) =
        (block m n (corner k z)).conjTranspose * v * block m n (corner k z)
      rw [← corner_pad (le_max_right m k) z]
      exact block_conjugate_corner (le_max_left m k) n v _

end MainGap.Stable

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap OAI.MainGap.Stable
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.Stable.blockConjugateOrder
attribute [local instance] OAI.MainGap.Stable.blockConjugateStarOrder
attribute [local instance] OAI.MainGap.Stable.algebraicTopology''


theorem solution : type_of% @_root_.OAI.MainGap.Stable.block_conjugate := @_root_.OAI.MainGap.Stable.block_conjugate
