-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_piTensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:39.713736+00:00
-- url     : https://prove2.me/submissions/f9f9a4dd-1231-41ad-ad10-467ee4f37fff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GlobalTheory.SmGL
theorem _root_.solution {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module F (X a)] {ρ : ∀ a, Representation F (Γ a) (X a)} (hρ : ∀ a, IsSmooth (ρ a)) :
    IsSmooth (piTensor ρ) := by
  intro x
  show x ∈ smoothPart (piTensor ρ)
  induction x using PiTensorProduct.induction_on with
  | add x y hx hy => exact add_mem hx hy
  | smul_tprod c x =>
    refine Submodule.smul_mem _ c (mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((isOpen_set_pi Set.finite_univ fun a _ => hρ a (x a)).mem_nhds (by simp)) fun g hg => ?_))
    have h : ∀ a, ρ a (g a) (x a) = x a := fun a => hg a trivial
    simp [h]
end GlobalTheory.SmGL
