-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:26:53.750932+00:00
-- url     : https://prove2.me/submissions/f4caccf4-213f-4f5b-b0fc-6357a79ce481

import Mathlib
import Definitions.Def_OAIQ035K043
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_mass_s35
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_step_survival_s35
import Theorems.Thm_OAI_MetricKMedian_SparseHistories_history_contraction_s35

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

theorem retained_subset (a dh : ℝ) (d : I → ℝ) (T : Finset I) : retained a dh d T ⊆ T :=
  Finset.filter_subset _ _

end MetricKMedian.PhysicalPotential
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

theorem past_length (κ : ℕ → α → SparseIntegerLaw α) (a : α) (t : ℕ)
    (i : Fin (tree κ a t).length) : ((tree κ a t).states[i.val].2).length=t := by
  exact tree_property κ a (fun t h => h.2.length=t) rfl
    (fun t h hh j => by simp only [extend,List.length_cons,hh]) t i

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

theorem labels_active (g β : ℚ) (x : ℝ) (d : J → F → ℝ)
    (A : Finset (CopyState.Copy (F := F) Δ)) (e : RationalBatchData.Event A g β)
    (S : J → Finset (CopyState.Copy (F := F) Δ)) (j : J) :
    labels g β x d (updateEvent g β A e) S j ⊆ (updateEvent g β A e).1 := by
  obtain ⟨G,Z⟩ := e
  exact CopyState.roundAlive_active A (S j) G _ Z x (g:ℝ) (d j)

theorem replay_extend (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (h : SparseHistories.History (State F Δ g β)) (s : State F Δ g β) :
    replay g β x d S₀ (SparseHistories.extend h s)=
      labels g β (x h.2.length) d s (replay g β x d S₀ h) := by
  simp only [replay,SparseHistories.extend,replayList,List.length_cons,Nat.add_sub_cancel]

theorem histories_alive (d₀ : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (x : ℕ → ℝ) (d : J → F → ℝ) (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (hactive : ∀ j, S₀ j ⊆ A)
    (i : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) (j : J) :
    replay g β x d S₀ (histories d₀ g β p φ P hp hφ hupper A T).states[i.val] j ⊆
      (histories d₀ g β p φ P hp hφ hupper A T).states[i.val].1.1 := by
  have hh := SparseHistories.tree_property
    (fun t => step d₀ g β p φ (P t) hp hφ hupper) (A,none)
    (fun _ h => ∀ j, replay g β x d S₀ h j ⊆ h.1.1) hactive
    (fun t h _ k => by
      obtain ⟨e,he⟩ := step_records d₀ g β p φ (P t) hp hφ hupper h.1 k
      intro j
      rw [replay_extend,he]
      exact labels_active g β (x h.2.length) d h.1.1 e _ j) T i
  exact hh j

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalHistorySurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {Δ : ℕ}

theorem histories_survival_s35_oai (d₀ : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A S₀ : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (x : ℕ → ℝ) (d : F → ℝ) {h : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hA : 1 ≤ mass (g:ℝ) A)
    (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S₀ ⊆ A) :
    (histories d₀ g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => mass (g:ℝ) (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())) ≤
      (1-h/2)^T*mass (g:ℝ) S₀ := by
  let κ := fun t => step (Δ := Δ) d₀ g β p φ (P t) hp0 hφ0 hupper
  let V := fun (_ : ℕ) (z : SparseHistories.History (State F Δ g β)) =>
    mass (g:ℝ) (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())
  have hstep : ∀ t < T, ∀ i : Fin (SparseHistories.tree κ (A,none) t).length,
      (κ t (SparseHistories.tree κ (A,none) t).states[i.val].1).expectation
        (fun s => V (t+1) (SparseHistories.extend (SparseHistories.tree κ (A,none) t).states[i.val] s)) ≤
      (1-h/2)*V t (SparseHistories.tree κ (A,none) t).states[i.val] := by
    intro t ht i
    let z := (SparseHistories.tree κ (A,none) t).states[i.val]
    have hz : z.2.length=t := SparseHistories.past_length κ (A,none) t i
    have ha := histories_alive d₀ g β p φ P hp0 hφ0 hupper A t x
      (fun (_ : Unit) => d) (fun _ => S₀) (fun _ => hSA) i ()
    have hm := histories_mass_s35 d₀ g β p φ P hp0 hφ0 hupper A t hg.le hunit hA i
    have hs := step_survival_s35 d₀ location hd g β p φ (P t) hp0 hφ0 hupper z.1
      (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ()) d hprob hg hunit
      (hP t ht) (hP1 t ht) hh0 hφ1 hm hsmall ha (x := x t)
    change (κ t z.1).expectation (fun s => V (t+1) (SparseHistories.extend z s)) ≤ (1-h/2)*V t z
    dsimp only [V]
    simp_rw [replay_extend,hz]
    exact hs
  have ht := SparseHistories.history_contraction_s35 κ (A,none) V (1-h/2)
    (by linarith only [hh1]) T hstep
  simpa only [V,κ,histories,replay,replayList,labels] using ht

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s35_oai := @OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s35_oai
