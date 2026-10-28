-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:27:16.119988+00:00
-- url     : https://prove2.me/submissions/ff067aa8-d786-4626-ae10-a15407266175

import Mathlib
import Definitions.Def_OAIQ035K043
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_CopyState_round_backup_s35
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data_all_s35

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

theorem retained_subset (a dh : ℝ) (d : I → ℝ) (T : Finset I) : retained a dh d T ⊆ T :=
  Finset.filter_subset _ _

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_FixedBatchTransition
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

omit [Fintype E] in
 theorem physical_subset (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A ⊆ S := sdiff_subset

end MetricKMedian.FixedBatch
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
-- module Solutions.OAIQ035_KM.KMedian_Process_ForceBatchBound
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem nextAliveAt_subset (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : nextAliveAt D a d S A ⊆ S := by
  unfold nextAliveAt
  split_ifs
  · exact (retained_subset _ _ _ _).trans (physical_subset D S A)
  · exact physical_subset D S A

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] {Δ : ℕ}

 theorem nextAliveAt_subset_physical {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
    (D : Actions I E) (a : ℝ) (d : I → ℝ) (S : Finset I) (Z : Finset E) :
    nextAliveAt D a d S Z ⊆ physical D S Z := by
  unfold nextAliveAt
  split_ifs
  · exact retained_subset _ _ _ _
  · exact Subset.rfl

omit [Fintype F] in
 theorem roundAlive_subset (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ) (d : F → ℝ) :
    roundAlive A S G H Z x g d ⊆ S := by
  rintro i hi
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
  exact (mem_localSet _ _ _).mp
    (sdiff_subset (nextAliveAt_subset _ _ _ _ _ hj))

omit [Fintype F] in
 theorem roundAlive_active (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ) (d : F → ℝ) :
    roundAlive A S G H Z x g d ⊆ next Δ A (roundErased A G H Z) (roundOpened A G H Z) := by
  rintro i hi
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
  have hp := (mem_sdiff.mp (nextAliveAt_subset_physical _ _ _ _ _ hj)).2
  apply mem_union_left
  apply mem_sdiff.mpr
  refine ⟨j.property,?_⟩
  intro he
  obtain ⟨k,hk,hkj⟩ := mem_image.mp he
  exact hp ((Subtype.ext hkj) ▸ hk)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_StateInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype J] [DecidableEq J] in
 theorem valid_initial (A : Finset (Copy (F := F) Δ)) (S₀ : J → Finset (Copy (F := F) Δ))
    (g : ℝ) (location : F → X) (client : J → X) (R : J → ℝ)
    (hA : 1 ≤ mass g A) (hS : ∀ j, S₀ j ⊆ A) : Valid g location client R S₀ (A,S₀) :=
  ⟨hA,hS,fun _ => Subset.rfl,fun j _ => hS j⟩

omit [Fintype J] [DecidableEq J] in
 theorem valid_advance (s : State F J Δ) (S₀ : J → Finset (Copy (F := F) Δ))
    (location : F → X) (client : J → X) (R : J → ℝ) {g P : ℝ}
    (D : Taper.GraphData Δ g P (fun i : s.1 => location i.val.1) (own Δ s.1))
    (G : s.1 → Finset s.1) (H : Finset s.1) (Z : Finset (HeavyAction (graphActions G) H))
    (x : ℝ) (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hP : 0 < P) (hP1 : P ≤ 1/2)
    (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass g (S₀ j)=1)
    (hd : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hgood : D.Good G) (hv : Valid g location client R S₀ s) :
    Valid g location client R S₀ (advance s G H Z x g (fun j f => dist (client j) (location f))) := by
  dsimp only [Valid, advance]
  refine ⟨round_mass_at_least_one s.1 G H Z hg hunit hv.1,?_,?_,?_⟩
  · intro j
    exact roundAlive_active s.1 (s.2 j) G H Z x g _
  · intro j
    exact (roundAlive_subset s.1 (s.2 j) G H Z x g _).trans (hv.2.2.1 j)
  · intro j
    exact round_backup_s35 s.1 (S₀ j) location (client j) D G H Z hg hP hP1 (hR j) (hm j)
      (hd j) hgood (hv.2.2.2 j)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalRoundEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

theorem events_property (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (Q : Event I g β → Prop)
    (hQ : ∀ i : Fin μ.length, ∀ Z : Finset (HeavyAction (graph μ.states[i.val])
      (heavySet (graphMass μ.states[i.val] g) β)), Q ⟨μ.states[i.val],Z⟩) :
    ∀ i : Fin (events μ Δ g β p φ hp hφ hupper).length,
      Q (events μ Δ g β p φ hp hφ hupper).states[i.val] := by
  apply SparseIntegerLaw.bindIndexed_property _ _ Q
  intro i j
  have he := SparseIntegerLaw.map_states
    (proposal μ.states[i.val] Δ g β p φ hp hφ hupper
      (enumeration (graph μ.states[i.val]) (heavySet (graphMass μ.states[i.val] g) β)))
    (fun Z => (⟨μ.states[i.val],Z⟩ : Event I g β)) j
  rw [he]
  exact hQ i _

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F J : Type} [LinearOrder F] {Δ : ℕ}

theorem replay_extend (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (h : SparseHistories.History (State F Δ g β)) (s : State F Δ g β) :
    replay g β x d S₀ (SparseHistories.extend h s)=
      labels g β (x h.2.length) d s (replay g β x d S₀ h) := by
  simp only [replay,SparseHistories.extend,replayList,List.length_cons,Nat.add_sub_cancel]

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistoryValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.rationalHistoryValidCopyOrder
omit [Fintype J] [DecidableEq J] in
theorem histories_valid_s35_oai (d₀ : F → F → ℚ) (location : F → X) (client : J → X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (R : J → ℝ) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hSA : ∀ j, S₀ j⊆A)
    (hR : ∀ j, 0≤R j) (hm : ∀ j, mass (g:ℝ) (S₀ j)=1)
    (hdR : ∀ j i, i∈S₀ j → dist (client j) (location i.1)≤R j)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    CopyState.Valid (g:ℝ) location client R S₀
      (z.1.1, replay g β x (fun j f => dist (client j) (location f)) S₀ z) := by
  let d := fun j f => dist (client j) (location f)
  let κ := fun t => step (Δ:=Δ) d₀ g β p φ (P t) hp hφ hupper
  have hh : ∀ t≤T, ∀ a : Fin (SparseHistories.tree κ (A,none) t).length,
      let z := (SparseHistories.tree κ (A,none) t).states[a.val];
      CopyState.Valid (g:ℝ) location client R S₀ (z.1.1,replay g β x d S₀ z) := by
    intro t
    induction t with
    | zero =>
      intro _ a
      simpa only [SparseHistories.tree,SparseIntegerLaw.dirac,Vector.getElem_replicate,
        replay,replayList,labels] using CopyState.valid_initial A S₀ (g:ℝ) location client R hA hSA
    | succ t ih =>
      intro ht
      simp only [SparseHistories.tree]
      apply SparseIntegerLaw.bindIndexed_property _ _ (fun z =>
        CopyState.Valid (g:ℝ) location client R S₀ (z.1.1,replay g β x d S₀ z))
      intro b c
      let z := (SparseHistories.tree κ (A,none) t).states[b.val]
      have hv := ih (by omega) b
      have he := SparseIntegerLaw.map_states (κ t z.1) (SparseHistories.extend z) c
      change (SparseHistories.branch (κ t) z).states[c.val]=_ at he
      rw [he]
      rw [replay_extend]
      obtain ⟨D,hD⟩ := graph_data_all_s35 d₀ location hd₀ g (P t) z.1.1 hg hunit
        (hP t (by omega)) (hP1 t (by omega)) hv.1
      have hprop := RationalBatchData.events_property (graphLaw d₀ g (P t) z.1.1) Δ g β p φ
        hp hφ hupper (fun e => CopyState.Valid (g:ℝ) location client R S₀
          ((updateEvent g β z.1.1 e).1,
            labels g β (x z.2.length) d (updateEvent g β z.1.1 e) (replay g β x d S₀ z)))
        (fun i Z => by
          exact CopyState.valid_advance (z.1.1,replay g β x d S₀ z) S₀ location client R D
            (graphLaw d₀ g (P t) z.1.1).states[i.val]
            (RationalBatchData.heavySet
              (RationalBatchData.graphMass (graphLaw d₀ g (P t) z.1.1).states[i.val] g) β)
            Z (x z.2.length) hg.le hunit (hP t (by omega)) (hP1 t (by omega)) hR hm hdR (hD i) hv)
      have hevent := SparseIntegerLaw.map_states
        (RationalBatchData.events (graphLaw d₀ g (P t) z.1.1) Δ g β p φ hp hφ hupper)
        (updateEvent g β z.1.1) c
      change (κ t z.1).states[c.val]=_ at hevent
      simpa only [SparseHistories.extend,hevent] using hprop c
  exact hh T le_rfl a

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s35_oai := @OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s35_oai
