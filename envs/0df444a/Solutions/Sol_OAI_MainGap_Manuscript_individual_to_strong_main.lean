-- Prove2me | solution 1 for OAI.MainGap.Manuscript.individual_to_strong_main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:40:48.754885+00:00
-- url     : https://prove2.me/submissions/bd95e073-3223-47cb-a6ad-c281394abdc3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Main.lean:L43-L50
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.MainGap.Manuscript.individual_to_strong_main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_MainGap_Manuscript_individual_to_strong_main) verbatim and is proved by it.
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
import Theorems.Thm_OAI_MainGap_Stable_block_conjugate
import Theorems.Thm_OAI_MainGap_individual_to_strong

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Diagonalization ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.boundedDiagonalizationPartialOrder
attribute [local instance] OAI.MainGap.boundedDiagonalizationStarOrderedRing
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.diagonalizationPartialOrder
attribute [local instance] OAI.MainGap.diagonalizationStarOrderedRing
theorem individual_to_strong_spi (hP : PropertyP A) : StronglyPurelyInfinite A := by
  intro x y hx hy ε hε
  exact individual_to_strong hP (x*x) (y*y)
    (by simpa only [hx.isSelfAdjoint.star_eq] using star_mul_self_nonneg x)
    (by simpa only [hy.isSelfAdjoint.star_eq] using star_mul_self_nonneg y) (x*y) ε hε

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.MatrixEntries ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
end MainGap.Stable

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Main ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap.Manuscript
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.Manuscript.positivityOrder
attribute [local instance] OAI.MainGap.Manuscript.positivityStarOrder
lemma finiteCuntzLE_of_stable {m n : ℕ} (d : Stable.Mat A n) (v : Stable.Mat A m)
    (h : CuntzLE (Stable.corner n d) (Stable.corner m v)) : MainGap.FiniteCuntzLE d v := by
  obtain ⟨r,hr⟩ := h
  refine ⟨fun j => Stable.block m n (r j), ?_⟩
  have ht := (Stable.continuous_block (A := A) n n).continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, Stable.block_conjugate, Stable.block_corner_self] using ht

lemma PropertyP.finite (hP : PropertyP A) : MainGap.PropertyP A := by
  intro h hh
  exact finiteCuntzLE_of_stable _ _ (hP h hh)

theorem individual_to_strong (hP : PropertyP A) : MainGap.UnrestrictedDiagonalization A :=
  MainGap.individual_to_strong hP.finite

theorem individual_to_strong_spi (hP : PropertyP A) : MainGap.StronglyPurelyInfinite A :=
  MainGap.individual_to_strong_spi hP.finite

theorem individual_to_strong_main (hP : PropertyP A) :
    (∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ c : A, ∀ ε : ℝ, 0 < ε →
      ∃ s t : A,
        ‖star s * a * s - a‖ < ε ∧
        ‖star t * b * t - b‖ < ε ∧
        ‖star s * c * t‖ < ε) ∧
    MainGap.StronglyPurelyInfinite A := by
  exact ⟨individual_to_strong hP, individual_to_strong_spi hP⟩

end MainGap.Manuscript

end

end OAI

-- ---- mission target ----
open OAI OAI.MainGap OAI.MainGap.Manuscript
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open Filter
open scoped Topology
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.OAI.MainGap.Manuscript.positivityOrder
attribute [local instance] _root_.OAI.MainGap.Manuscript.positivityStarOrder
attribute [local instance] OAI.MainGap.Manuscript.positivityOrder
attribute [local instance] OAI.MainGap.Manuscript.positivityStarOrder

namespace OAI
namespace MainGap.Manuscript
theorem _root_.solution (hP : PropertyP A) :
    (∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ c : A, ∀ ε : ℝ, 0 < ε →
      ∃ s t : A,
        ‖star s * a * s - a‖ < ε ∧
        ‖star t * b * t - b‖ < ε ∧
        ‖star s * c * t‖ < ε) ∧
    MainGap.StronglyPurelyInfinite A := by
  first
    | exact OAI.MainGap.Manuscript.individual_to_strong_main hP
    | exact OAI.MainGap.Manuscript.individual_to_strong_main
    | (apply OAI.MainGap.Manuscript.individual_to_strong_main <;> assumption)
    | (intros; apply OAI.MainGap.Manuscript.individual_to_strong_main <;> assumption)
end MainGap.Manuscript
end OAI
