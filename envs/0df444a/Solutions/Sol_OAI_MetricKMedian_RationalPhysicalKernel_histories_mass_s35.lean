-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_mass_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:26:31.634189+00:00
-- url     : https://prove2.me/submissions/6a04781c-b865-41ef-8943-c1ffed487446

import Mathlib
import Definitions.Def_OAIQ035K043
import Definitions.Def_OAIQ035K047

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem mass_mono {g : ℝ} {S T : Finset I} (hg : 0 ≤ g) (hST : S ⊆ T) :
    mass g S ≤ mass g T := by
  apply mul_le_mul_of_nonneg_left _ hg
  exact_mod_cast Finset.card_le_card hST

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_HeavyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem ordinary_heavyActions (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    e ∈ (heavyActions Full H).ordinary ↔ e.isLeft := by simp [heavyActions]

omit [Fintype I] in
 theorem heavyParent_membership (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    heavyParent Full H e ∈ H ↔ ¬ e.isLeft := by
  cases e with
  | inl h => simp [heavyParent, h.property]
  | inr p => simp [heavyParent, p.property.1]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActualActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

 theorem nonordinary_parent_heavy (G : I → Finset I) (H : Finset I)
    (e : HeavyAction (graphActions G) H) (he : e ∉ (heavyActions (graphActions G) H).ordinary) :
    (heavyActions (graphActions G) H).source e ∈ H := by
  apply (heavyParent_membership _ _ e).mpr
  simpa only [ordinary_heavyActions] using he

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F]
variable (Δ : ℕ)

 theorem slots_disjoint {f h : F} (hfh : f ≠ h) : Disjoint (slots Δ f) (slots Δ h) := by
  apply disjoint_left.mpr
  intro i hi hj
  exact hfh (((mem_slots Δ f i).mp hi).symm.trans ((mem_slots Δ h i).mp hj))

 theorem card_resets (O : Finset F) : (resets Δ O).card=O.card*Δ := by
  rw [resets, card_biUnion (fun _ _ _ _ hne => slots_disjoint Δ hne)]
  simp

variable [Fintype F]

omit [Fintype F] in
 theorem reset_mass (O : Finset F) {g : ℝ} (hunit : g*(Δ:ℝ)=1) :
    mass g (resets Δ O)=(O.card:ℝ) := by
  rw [mass, card_resets, Nat.cast_mul]
  nlinarith only [hunit]

omit [Fintype F] in
 theorem next_mass_at_least_one (A erased : Finset (Copy (F := F) Δ)) (O : Finset F)
    {g : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hA : 1 ≤ mass g A)
    (ha : erased.Nonempty → O.Nonempty) : 1 ≤ mass g (next Δ A erased O) := by
  by_cases ho : O.Nonempty
  · have hc : (1:ℝ) ≤ O.card := by exact_mod_cast ho.card_pos
    have hs : resets Δ O ⊆ next Δ A erased O := subset_union_right
    exact (hc.trans_eq (reset_mass Δ O hunit).symm).trans (mass_mono hg hs)
  · have he : erased=∅ := not_nonempty_iff_eq_empty.mp (fun h => ho (ha h))
    exact hA.trans (mass_mono hg (by simp [next,he]))

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

variable {Δ}

 theorem parent_selected {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → Finset I) (H : Finset I) (Z : Finset (HeavyAction (graphActions G) H))
    {e : HeavyAction (graphActions G) H} (he : e ∈ Z) :
    heavyParent (graphActions G) H e ∈ selectedSources G H Z := by
  by_cases ho : e ∈ (heavyActions (graphActions G) H).ordinary
  · exact mem_union_right _ (mem_image.mpr ⟨e,mem_inter.mpr ⟨he,ho⟩,rfl⟩)
  · exact mem_union_left _ (nonordinary_parent_heavy G H e ho)

omit [Fintype F] in
 theorem roundErased_nonempty (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (he : (roundErased A G H Z).Nonempty) : (roundOpened A G H Z).Nonempty := by
  obtain ⟨i,hi⟩ := he
  obtain ⟨j,hj,_⟩ := mem_image.mp hi
  obtain ⟨e,he,_⟩ := mem_biUnion.mp hj
  exact ⟨_,mem_image.mpr ⟨_,parent_selected G H Z he,rfl⟩⟩

omit [Fintype F] in
 theorem round_mass_at_least_one (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hA : 1 ≤ PhysicalPotential.mass g A) :
    1 ≤ PhysicalPotential.mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z)) :=
  next_mass_at_least_one Δ A _ _ hg hunit hA (roundErased_nonempty A G H Z)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem tree_property (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (P : ℕ → History α → Prop) (h0 : P 0 (a,[]))
    (hstep : ∀ t h, P t h → ∀ i : Fin (κ t h.1).length, P (t+1) (extend h (κ t h.1).states[i.val]))
    (t : ℕ) : ∀ i : Fin (tree κ a t).length, P t (tree κ a t).states[i.val] := by
  induction t with
  | zero => intro i; simpa only [tree,SparseIntegerLaw.dirac,Vector.getElem_replicate] using h0
  | succ t ih =>
    apply SparseIntegerLaw.bindIndexed_property _ _ (P (t+1))
    intro i j
    have hh := SparseIntegerLaw.map_states (κ t (tree κ a t).states[i.val].1)
      (extend (tree κ a t).states[i.val]) j
    change (branch (κ t) (tree κ a t).states[i.val]).states[j.val]=_ at hh
    rw [hh]
    exact hstep t _ (ih i) j

theorem physical_invariant (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (P : α → Prop) (h0 : P a)
    (hstep : ∀ t s, P s → ∀ i : Fin (κ t s).length, P (κ t s).states[i.val])
    (t : ℕ) (i : Fin (tree κ a t).length) : P (tree κ a t).states[i.val].1 :=
  tree_property κ a (fun _ h => P h.1) h0 (fun t h hh j => hstep t h.1 hh j) t i

end MetricKMedian.SparseHistories
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy
omit [Fintype F] in

theorem step_records (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (i : Fin (step d g β p φ P hp hφ hupper s).length) :
    ∃ e : RationalBatchData.Event s.1 g β,
      (step d g β p φ P hp hφ hupper s).states[i.val]=updateEvent g β s.1 e := by
  exact ⟨_, SparseIntegerLaw.map_states _ _ i⟩

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

omit [Fintype F] in

theorem update_mass (g β : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (e : RationalBatchData.Event A g β) (hg : 0 ≤ (g:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1) (hA : 1 ≤ mass (g:ℝ) A) :
    1 ≤ mass (g:ℝ) (updateEvent g β A e).1 := by
  obtain ⟨G,Z⟩ := e
  exact CopyState.round_mass_at_least_one A G
    (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z hg hunit hA

omit [Fintype F] in
theorem step_mass (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hs : 1 ≤ mass (g:ℝ) s.1) (i : Fin (step d g β p φ P hp hφ hupper s).length) :
    1 ≤ mass (g:ℝ) (step d g β p φ P hp hφ hupper s).states[i.val].1 := by
  obtain ⟨e,he⟩ := step_records d g β p φ P hp hφ hupper s i
  rw [he]
  exact update_mass g β s.1 e hg hunit hs

omit [Fintype F] in

theorem histories_mass_s35_oai (d : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hA : 1 ≤ mass (g:ℝ) A)
    (i : Fin (histories d g β p φ P hp hφ hupper A T).length) :
    1 ≤ mass (g:ℝ) (histories d g β p φ P hp hφ hupper A T).states[i.val].1.1 := by
  exact SparseHistories.physical_invariant
    (fun t => step d g β p φ (P t) hp hφ hupper) (A,none)
    (fun s => 1 ≤ mass (g:ℝ) s.1) hA
    (fun t s hs j => step_mass d g β p φ (P t) hp hφ hupper s hg hunit hs j) T i

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.histories_mass_s35_oai := @OAI.MetricKMedian.RationalPhysicalKernel.histories_mass_s35_oai
