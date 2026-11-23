-- Prove2me | solution 1 for GlobalTheory.RestrMeas.exists_extend_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:11.265456+00:00
-- url     : https://prove2.me/submissions/4ed3f5fa-0ad6-488e-9958-f910736d33d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
omit [∀ v, TopologicalSpace (Yf v)]
namespace GlobalTheory.RestrMeas
theorem _root_.solution {V' : Type} {j : V' → V} (hj : Function.Injective j) (y : ∀ v', Yf (j v')) :
    ∃ z : ∀ v, Yf v, (∀ v', z (j v') = y v') ∧ ∀ v ∉ range j, z v = 1 := by
  have : ∀ v, ∃ z : Yf v, (∀ v' (e : j v' = v), z = e ▸ y v') ∧ (v ∉ range j → z = 1) := fun v => by
    by_cases hv : v ∈ range j
    · obtain ⟨u, rfl⟩ := hv
      exact ⟨y u, fun v' e => by obtain rfl := hj e; rfl, fun h => absurd ⟨u, rfl⟩ h⟩
    · exact ⟨1, fun v' e => absurd ⟨v', e⟩ hv, fun _ => rfl⟩
  choose z h1 h2 using this
  exact ⟨z, fun v' => h1 _ v' rfl, h2⟩
end GlobalTheory.RestrMeas
