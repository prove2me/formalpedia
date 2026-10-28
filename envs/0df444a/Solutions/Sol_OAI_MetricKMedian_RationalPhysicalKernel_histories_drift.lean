-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_drift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:48:53.330994+00:00
-- url     : https://prove2.me/submissions/9af993da-615a-408e-99d2-469aa5d8574a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ035K043
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_mass
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_step_drift
import Theorems.Thm_OAI_MetricKMedian_SparseHistories_accumulated_drift_up_to

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem exp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

private theorem exp_derivative_integral (x : ℝ) :
    -x * (∫ t : ℝ in 0..1, Real.exp (-t * x)) = Real.exp (-x) - 1 := by
  rw [← intervalIntegral.integral_const_mul]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-t * x))
      (-x * Real.exp (-t * x)) t := by
    intro t
    simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul, mul_one, mul_neg, mul_comm]
      using (((hasDerivAt_id t).neg.mul_const x).exp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · simp
  · exact (exp_integrable x).const_mul _

theorem A_eq (x : ℝ) :
    A x = 1 + 2 * (1 - ∫ t : ℝ in 0..1, Real.exp (-t * x)) := by
  rw [A, intervalIntegral.integral_sub (intervalIntegrable_const) (exp_integrable x)]
  simp

theorem A_one : A 1 = 1 + 2 / Real.exp 1 := by
  rw [A_eq]
  have h := exp_derivative_integral 1
  simp only [mul_one, neg_mul, one_mul] at h
  simp only [mul_one]
  rw [Real.exp_neg] at h
  rw [div_eq_mul_inv]
  linarith

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

theorem coefficient_eq (x y : ℝ) : coefficient x y = 1+m x+B x*y := by
  unfold coefficient m B
  ring

end MetricKMedian.Analytic
end
end

end OAI
end

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

theorem cost_mono {g : ℝ} {d : I → ℝ} {S T : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ T, 0 ≤ d i) (hST : S ⊆ T) : cost g d S ≤ cost g d T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i hi _ => mul_nonneg hg (hd i hi))

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

theorem labels_subset (g β : ℚ) (x : ℝ) (d : J → F → ℝ)
    (s : State F Δ g β) (S : J → Finset (CopyState.Copy (F := F) Δ)) (j : J) :
    labels g β x d s S j ⊆ S j := by
  obtain ⟨A,e⟩ := s
  cases e with
  | none => exact Subset.rfl
  | some e =>
    obtain ⟨B,⟨G,Z⟩⟩ := e
    exact CopyState.roundAlive_subset B (S j) G _ Z x (g:ℝ) (d j)

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

theorem replay_subset (g β : ℚ) (x : ℕ → ℝ) (d : J → F → ℝ)
    (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (h : SparseHistories.History (State F Δ g β)) (j : J) :
    replay g β x d S₀ h j ⊆ S₀ j := by
  have hh : ∀ L, replayList g β x d S₀ L j ⊆ S₀ j := by
    intro L
    induction L with
    | nil => exact Subset.rfl
    | cons s L ih => exact (labels_subset g β (x (L.length-1)) d s _ j).trans ih
  exact hh _

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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalHistoryDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential FixedBatch Analytic CopyState
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

theorem histories_drift_oai (d₀ : F → F → ℚ) (location : F → X) (client : X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A S₀ : Finset (Copy (F := F) Δ)) (T : ℕ)
    {h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4)
    (he : ∀ t < T, |(P t:ℝ)-Analytic.P (Real.exp (-(t:ℝ)*h))| ≤ ζ)
    (hactive : S₀ ⊆ A) (hm₀ : mass (g:ℝ) S₀=1)
    (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
    (histories d₀ g β p φ P hp hφ hupper A T).expectation (fun z =>
      potential (Real.exp (-(T:ℝ)*h)) (g:ℝ) (fun i => dist client (location i.1))
        (replay g β (fun t => Real.exp (-(t:ℝ)*h))
          (fun (_ : Unit) f => dist client (location f)) (fun _ => S₀) z ())
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ z.1.1))) ≤
      (1+2/Real.exp 1)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S₀+
      (T:ℝ)*(h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S₀+
        batchConstant Δ*h*((φ:ℝ)+h)*R) := by
  let x := fun t : ℕ => Real.exp (-(t:ℝ)*h)
  let d := fun f => dist client (location f)
  let κ := fun t => step (Δ := Δ) d₀ g β p φ (P t) hp hφ hupper
  let V := fun t (z : SparseHistories.History (State F Δ g β)) =>
    potential (x t) (g:ℝ) (fun i => d i.1)
      (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())
      (GroupCap.cap R d (integral Δ z.1.1))
  let V₀ := PhysicalPotential.cost (g:ℝ) (fun i => d i.1) S₀
  let E := h*((g:ℝ)+12*ζ)*V₀+batchConstant Δ*h*((φ:ℝ)+h)*R
  have hx0 : ∀ t, 0 ≤ x t := fun _ => (Real.exp_pos _).le
  have hx1 : ∀ t, x t ≤ 1 := fun t => Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg t)) hh0)
  have hxs : ∀ t, x (t+1)=x t*Real.exp (-h) := by
    intro t
    dsimp only [x]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hstep : ∀ t < T, ∀ i : Fin (SparseHistories.tree κ (A,none) t).length,
      (κ t (SparseHistories.tree κ (A,none) t).states[i.val].1).expectation
        (fun s => V (t+1) (SparseHistories.extend (SparseHistories.tree κ (A,none) t).states[i.val] s)) ≤
      V t (SparseHistories.tree κ (A,none) t).states[i.val]+E := by
    intro t ht i
    let z := (SparseHistories.tree κ (A,none) t).states[i.val]
    let S := replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ()
    have hz : z.2.length=t := SparseHistories.past_length κ (A,none) t i
    have ha : S ⊆ z.1.1 := histories_alive d₀ g β p φ P hp hφ hupper A t
      x (fun (_ : Unit) => d) (fun _ => S₀) (fun _ => hactive) i ()
    have hs : S ⊆ S₀ := replay_subset g β x (fun (_ : Unit) => d) (fun _ => S₀) z ()
    have hm := histories_mass d₀ g β p φ P hp hφ hupper A t hg.le hunit hA i
    have htstep := step_drift d₀ location client hd₀ g β p φ (P t) hp hφ hupper z.1 S S₀
      hprob hg hg1 hunit (hP t ht) (hP1 t ht) hm (hx0 t) (hx1 t) hh0 hh1 hφ1
      hsmall hζ0 hζ1 (he t ht) ha hs hm₀ hR0 hdR hR
    have hv : ∀ s, V (t+1) (SparseHistories.extend z s)=
        potential (x t*Real.exp (-h)) (g:ℝ) (fun i => d i.1)
          (labels g β (x t) (fun (_ : Unit) => d) s (fun _ => S) ())
          (GroupCap.cap R d (integral Δ s.1)) := by
      intro s
      dsimp only [V]
      rw [replay_extend,hz,hxs]
      rfl
    change (κ t z.1).expectation (fun s => V (t+1) (SparseHistories.extend z s)) ≤ V t z+E
    simp_rw [hv]
    apply htstep.trans
    have hc := cost_mono hg.le (d := fun i : Copy (F := F) Δ => d i.1)
      (fun _ _ => dist_nonneg) hs
    have hc' := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ h*((g:ℝ)+12*ζ) from mul_nonneg hh0 (by positivity))
    change V t z+h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => d i.1) S+
      batchConstant Δ*h*((φ:ℝ)+h)*R ≤ V t z+E
    dsimp only [E,V₀]
    linarith only [hc']
  have ht := SparseHistories.accumulated_drift_up_to κ (A,none) V (fun _ => E) T hstep
  have hinit : V 0 ((A,none),[])=(1+2/Real.exp 1)*V₀ := by
    change potential (x 0) (g:ℝ) (fun i => d i.1) S₀ (GroupCap.cap R d (integral Δ A))=_
    simp only [x,Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero]
    rw [potential,hm₀,sub_self,zero_mul,add_zero,← coefficient_eq]
    rw [coefficient,sub_self,mul_zero,add_zero,A_one]
  rw [hinit] at ht
  simpa only [sum_const,card_range,nsmul_eq_mul,V,V₀,E,x,d,κ,histories] using ht

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_oai := @OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_oai
