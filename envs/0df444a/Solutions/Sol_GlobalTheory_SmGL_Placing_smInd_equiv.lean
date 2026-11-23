-- Prove2me | solution 1 for GlobalTheory.SmGL.Placing.smInd_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:55.371076+00:00
-- url     : https://prove2.me/submissions/3fe89a79-1b6b-434f-9c9a-dd8bcc93e170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
open ValuativeRel MeasureTheory
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
namespace GlobalTheory.SmGL.Placing
namespace _root_.GlobalTheory.SmGL.Placing
theorem _root_.solution [TopologicalSpace G] [IsTopologicalGroup G]
    {P Q : Subgroup G}
    {σ : Representation F P V} {τ : Representation F Q V} (w : G)
    (h : ∀ q : Q, ∃ p : P, (p : G) = w * q * w⁻¹ ∧ σ p = τ q)
    (h' : ∀ p : P, ∃ q : Q, (q : G) = w⁻¹ * p * w⁻¹⁻¹ ∧ τ q = σ p) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd P σ).Equiv (_root_.GlobalTheory.PRep.smInd Q τ)) := by
  refine ⟨Representation.Equiv.mk
    { _root_.GlobalTheory.SmGL.Placing.indLeft w h with
      invFun := _root_.GlobalTheory.SmGL.Placing.indLeft w⁻¹ h'
      left_inv := fun f => ?_
      right_inv := fun f => ?_ } fun g => ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (mul_inv_cancel_left w x)
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (inv_mul_cancel_left w x)
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (mul_assoc w x g)
end _root_.GlobalTheory.SmGL.Placing
end GlobalTheory.SmGL.Placing
