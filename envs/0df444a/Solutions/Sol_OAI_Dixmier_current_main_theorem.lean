-- Prove2me | solution 1 for OAI.Dixmier.current_main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:23:22.419336+00:00
-- url     : https://prove2.me/submissions/f065a9ee-72e9-4ced-9075-13227848fe63

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/AllDiscrete.lean:L12-L24
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Dixmier.current_main_theorem.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Dixmier_current_main_theorem) verbatim and is proved by it.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Frames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Masked__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MeanBounds
import Definitions.Def_OAI_Analysis_Unitarizability_AveragedForm
import Theorems.Thm_OAI_Dixmier_DayDixmier_representation_similar
import Theorems.Thm_OAI_Dixmier_nonamenable_near_one

-- ---- from OAI.Analysis.Unitarizability.UniverseTransport ----
namespace OAI

/-! Countability lets a group be represented in any universe.
Transport by group equivalences preserves the positive normalized invariant mean
and the bounded nonunitarizable witness. -/
noncomputable section
namespace Dixmier
universe u v w
open scoped BoundedContinuousFunction
variable {G : Type u} {Q : Type v} [Group G] [Group Q]
variable [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace Q] [DiscreteTopology Q]

/-- Amenability transport uses the same positive normalized invariant mean. -/
theorem amenable_of_mulEquiv (e : G ≃* Q) (hQ : Amenable Q) : Amenable G := by
  rcases hQ with ⟨m, h1, hp, hi⟩
  refine ⟨m.comp (meanPullback e), ?_, ?_, ?_⟩
  · have hc : meanPullback e (BoundedContinuousFunction.const G 1) =
        BoundedContinuousFunction.const Q 1 := by ext q; rfl
    simpa only [LinearMap.comp_apply, hc] using h1
  · intro f hf
    exact hp _ (fun q => hf (e.symm q))
  · intro g f
    have hc : meanPullback e (leftTranslate g f) = leftTranslate (e g) (meanPullback e f) := by
      ext q
      simp [meanPullback_apply, leftTranslate, map_mul, map_inv]
    simpa only [LinearMap.comp_apply, hc] using hi (e g) (meanPullback e f)

end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.NearOne ----
namespace OAI

noncomputable section
namespace Dixmier
universe u
open Filter
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

universe v

theorem nonamenable_near_one_large (hG : ¬ Amenable G) (ε : ℝ) (hε : 0 < ε) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
      (Countable G → TopologicalSpace.SeparableSpace H) ∧
      (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π := by
  let Q := ULift.{v} G
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  let e : G ≃* Q := MulEquiv.ulift.symm
  have hQ : ¬ Amenable Q := fun h => hG (amenable_of_mulEquiv e h)
  obtain ⟨H, hnorm, hinner, hcomplete, π, hsep, hb, hn⟩ := nonamenable_near_one hQ ε hε
  refine ⟨H, hnorm, hinner, hcomplete, π.comp e.toMonoidHom, ?_, fun g => hb (e g), ?_⟩
  · intro hcount
    let := hcount
    exact hsep (e.surjective.countable)
  · rintro ⟨S, hS⟩
    apply hn
    refine ⟨S, ?_⟩
    intro q x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply]
      using hS (e.symm q) x

end Dixmier
end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Amenable ----
namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

end DayDixmier

universe v
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  
theorem amenable_unitarizable (hG : Amenable G) : Unitarizable.{_, v} G := by
  intro H _ _ _ π hπ
  exact DayDixmier.representation_similar hG π hπ

end Dixmier
end

end OAI

-- ---- from OAI.Analysis.Unitarizability.AllDiscrete ----
namespace OAI

noncomputable section
namespace Dixmier
universe u v

theorem current_main_theorem : CurrentMainTheorem.{u,v} := by
  intro G _ _ _
  constructor
  · constructor
    · intro hG
      exact amenable_unitarizable hG
    · intro hunit
      by_contra hnot
      obtain ⟨H, hnorm, hinner, hcomplete, π, _, hb, hn⟩ :=
        nonamenable_near_one_large.{u,v} hnot 1 zero_lt_one
      exact hn (@hunit H hnorm hinner hcomplete π ⟨1 + 1, hb⟩)
  · intro ε hε hG
    exact nonamenable_near_one_large.{u,v} hG ε hε

end Dixmier
end

end OAI

-- ---- mission target ----
open OAI OAI.Dixmier
universe u v
open scoped BoundedContinuousFunction

theorem solution : CurrentMainTheorem.{u,v} := by
  first
    | exact OAI.Dixmier.current_main_theorem
    | (apply OAI.Dixmier.current_main_theorem <;> assumption)
    | (intros; apply OAI.Dixmier.current_main_theorem <;> assumption)
