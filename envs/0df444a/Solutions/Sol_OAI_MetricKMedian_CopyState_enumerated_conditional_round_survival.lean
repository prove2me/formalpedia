-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:42:19.474163+00:00
-- url     : https://prove2.me/submissions/17a5c5b3-5afb-42c7-837f-a06f2f0bb238

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_erasure_at_least_quarter

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
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace BatchRemainder

theorem expect_selected_sum {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ) :
    μ.expect (fun ω => ∑ e ∈ A ω, b e) =
      ∑ e, μ.prob (fun ω => e ∈ A ω) * b e := by
  have hsum : ∀ ω, (∑ e ∈ A ω, b e) = ∑ e, (if e ∈ A ω then (1:ℝ) else 0) * b e := by
    intro ω
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
    simp only [Finset.filter_univ_mem]
  simp_rw [hsum, FiniteLaw.expect_sum, FiniteLaw.expect_mul_right]
  rfl

end BatchRemainder
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_FiniteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteGraph

variable {I H : Type*} [Fintype H] [DecidableEq I] [DecidableEq H]

theorem touching_card (E : H → Finset I) (S : Finset I) {Δ : ℕ}
    (hin : ∀ i ∈ S, (incoming E i).card ≤ Δ) :
    (touching E S).card ≤ S.card*Δ := by
  apply le_trans (Finset.card_biUnion_le) ?_
  calc
    (∑ i ∈ S, (incoming E i).card) ≤ ∑ _i ∈ S, Δ := Finset.sum_le_sum hin
    _ = S.card*Δ := by simp

theorem self_not_conflict (E : H → Finset I) (balanced : Finset H) (h : H) :
    h ∉ conflicts E balanced h := by simp [conflicts]

theorem conflicts_card (E : H → Finset I) (balanced : Finset H) (h : H) {Δ : ℕ}
    (hout : (E h).card ≤ Δ) (hin : ∀ i ∈ E h, (incoming E i).card ≤ Δ) :
    (conflicts E balanced h).card ≤ Δ^2 := by
  have hsub : conflicts E balanced h ⊆ touching E (E h) :=
    Finset.Subset.trans (Finset.erase_subset _ _) Finset.inter_subset_left
  calc
    (conflicts E balanced h).card ≤ (touching E (E h)).card := Finset.card_le_card hsub
    _ ≤ (E h).card*Δ := touching_card E (E h) hin
    _ ≤ Δ*Δ := Nat.mul_le_mul_right Δ hout
    _ = Δ^2 := (pow_two Δ).symm

end MetricKMedian.FiniteGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceGenerator
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic GeneratorAverage GraphMoments
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem mem_graph_erase (G : I → Finset I) (h i : I) :
    i ∈ (graphActions G).erase h ↔ h ∈ G i := by simp [graphActions]

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

 theorem same_parent_eraser (Full : Actions I I) (H : Finset I)
    (e f : HeavyAction Full H) {i : I}
    (hpar : heavyParent Full H e=heavyParent Full H f)
    (he : i ∈ (heavyActions Full H).erase e) (hf : i ∈ (heavyActions Full H).erase f) : e=f := by
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (Subtype.ext hpar)
    | inr f =>
      change e.val=f.val.1 at hpar
      exact (e.property (hpar.symm ▸ f.property.1)).elim
  | inr e =>
    cases f with
    | inl f =>
      change e.val.1=f.val at hpar
      exact (f.property (hpar ▸ e.property.1)).elim
    | inr f =>
      have he' : i=e.val.2 := mem_singleton.mp he
      have hf' : i=f.val.2 := mem_singleton.mp hf
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hpar (he'.symm.trans hf')))

 theorem heavy_partition_union (Full : Actions I I) (H : Finset I) (h : I) :
    (univ.filter (fun e => heavyParent Full H e=h)).biUnion (heavyActions Full H).erase=Full.erase h := by
  ext i
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hi⟩
    cases e with
    | inl e => exact he ▸ hi
    | inr e =>
      change e.val.1=h at he
      have hi' : i=e.val.2 := mem_singleton.mp hi
      exact he ▸ (hi'.symm ▸ e.property.2)
  · intro hi
    by_cases hh : h ∈ H
    · exact ⟨.inr ⟨(h,i), hh, hi⟩, rfl, mem_singleton_self _⟩
    · exact ⟨.inl ⟨h,hh⟩, rfl, hi⟩

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

omit [Fintype I] in
 theorem balancedConflicts_bound (D : Actions I E) (Δ : ℕ)
    (hin : ∀ i, (incoming D.erase i).card ≤ Δ) (e : E) :
    (balancedConflicts D Δ e).card ≤ Δ^2 := by
  unfold balancedConflicts
  split_ifs with he
  · apply conflicts_card _ _ _ (le_of_eq (mem_filter.mp he).2)
    intro i _
    exact hin i
  · simp

omit [Fintype I] in
 theorem balancedConflicts_self (D : Actions I E) (Δ : ℕ) (e : E) :
    e ∉ balancedConflicts D Δ e := by
  unfold balancedConflicts
  split_ifs
  · exact self_not_conflict _ _ _
  · simp

theorem heavy_incoming_card (G : I → Finset I) (H : Finset I) (i : I) :
    (incoming (heavyActions (graphActions G) H).erase i).card=(G i).card := by
  apply card_bij (fun e _ => heavyParent (graphActions G) H e)
  · intro e he
    have hi := (mem_filter.mp he).2
    have hu := heavy_partition_union (graphActions G) H (heavyParent (graphActions G) H e)
    have hic : i ∈ (graphActions G).erase (heavyParent (graphActions G) H e) := by
      rw [← hu]
      exact mem_biUnion.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,rfl⟩,hi⟩
    exact (mem_graph_erase _ _ _).mp hic
  · intro e he f hf heq
    exact same_parent_eraser (graphActions G) H e f heq (mem_filter.mp he).2 (mem_filter.mp hf).2
  · intro h hh
    have hh' := (mem_graph_erase G h i).mpr hh
    rw [← heavy_partition_union (graphActions G) H h] at hh'
    obtain ⟨e,he,hi⟩ := mem_biUnion.mp hh'
    exact ⟨e,mem_filter.mpr ⟨mem_univ _,hi⟩,(mem_filter.mp he).2⟩

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

 theorem localSet_image (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) :
    (localSet A S).image Subtype.val=S := by
  ext i
  constructor
  · rintro hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact (mem_localSet _ _ _).mp hj
  · intro hi
    exact mem_image.mpr ⟨⟨i,hS hi⟩,(mem_localSet _ _ _).mpr hi,rfl⟩

 theorem image_mass (A : Finset (Copy (F := F) Δ)) (S : Finset A) (g : ℝ) :
    mass g (S.image Subtype.val)=mass g S := by
  simp only [mass,card_image_of_injective _ Subtype.val_injective]

 theorem localSet_mass (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (g : ℝ) :
    mass g (localSet A S)=mass g S := by
  rw [← image_mass,localSet_image A S hS]

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

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ErasureDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset PhysicalPotential
variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem expected_mass_subset (μ : FiniteLaw Ω) (T : Ω → Finset I) (S : Finset I)
    {g ρ : ℝ} (hg : 0 ≤ g) (hsub : ∀ ω, T ω ⊆ S)
    (hp : ∀ i ∈ S, μ.prob (fun ω => i ∈ T ω) ≤ ρ) :
    μ.expect (fun ω => mass g (T ω)) ≤ ρ*mass g S := by
  have he : μ.expect (fun ω => mass g (T ω))=
      ∑ i, μ.prob (fun ω => i ∈ T ω)*g := by
    have hh := BatchRemainder.expect_selected_sum μ T (fun _ => g)
    simpa only [sum_const,nsmul_eq_mul,mass,mul_comm g] using hh
  rw [he]
  have hzero : ∀ i, i ∉ S → μ.prob (fun ω => i ∈ T ω)=0 := by
    intro i hi
    unfold prob
    have hp : (fun ω => if i ∈ T ω then (1:ℝ) else 0)=fun _ => 0 := by
      funext ω
      rw [ite_eq_right (fun hm => hi (hsub ω hm))]
    rw [hp,expect_const]
  have hsum := sum_le_sum (s := univ) (f := fun i => μ.prob (fun ω => i ∈ T ω)*g)
    (g := fun i => if i ∈ S then ρ*g else 0) (fun i _ => ?_)
  · have he' : (∑ i, if i ∈ S then ρ*g else 0)=ρ*mass g S := by
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,mass]
      ring
    exact hsum.trans_eq he'
  · by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      exact mul_le_mul_of_nonneg_right (hp i hi) hg
    · rw [ite_eq_right hi,hzero i hi,zero_mul]

end MetricKMedian.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePhysicalSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem enumerated_conditional_round_survival_oai (A S : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (H : Finset A)
    (enum : Fin n ≃ HeavyAction (graphActions G) H)
    (p : ℚ) (q : HeavyAction (graphActions G) H → ℚ)
    {x g h : ℝ} (d : F → ℝ) (hG : ∀ i, (G i).card=Δ)
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (_hh0 : 0 ≤ h)
    (hprob : (p:ℝ)=2*h*g) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ))
    (hsmall : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ A) :
    let D := heavyActions (graphActions G) H
    let μ := (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ)
      p q hp hq0).real
    μ.expect (fun Z => mass g (roundAlive A S G H Z x g d)) ≤ (1-h/2)*mass g S := by
  intro D μ
  let T := fun Z => nextAliveAt D (Analytic.coefficient x (mass g S))
    (fun i => d i.val.1) (localSet A S \ forcedAlive A S H) Z
  have hin : ∀ i, (FiniteGraph.incoming D.erase i).card=Δ := fun i =>
    (heavy_incoming_card G H i).trans (hG i)
  have hp : ∀ i ∈ localSet A S, μ.prob (fun Z => i ∈ T Z) ≤ 1-h/2 := by
    intro i _
    let R := FiniteGraph.incoming D.erase i
    have herase := SparseEnumeratedBatch.erasure_at_least_quarter enum (balancedActions D Δ) R
      (balancedConflicts D Δ) p q hp hq0 hq
      (balancedConflicts_bound D Δ (fun i => le_of_eq (hin i)))
      (balancedConflicts_self D Δ) (by simpa only [R,hin i,hprob] using hsmall)
    rw [hprob] at herase
    have he : μ.prob (fun Z => i ∈ T Z) ≤ μ.prob (fun Z => ¬∃ e ∈ R, e ∈ Z) := by
      apply μ.prob_mono
      intro Z hi ⟨e,he,heZ⟩
      have hh := (mem_sdiff.mp (nextAliveAt_subset_physical _ _ _ _ _ hi)).2
      exact hh (mem_biUnion.mpr ⟨e,heZ,(mem_filter.mp he).2⟩)
    rw [μ.prob_compl] at he
    have hc : (R.card:ℝ)*(2*h*g)/4=h/2 := by
      rw [show R.card=Δ from hin i]
      calc
        _ = (g*(Δ:ℝ))*h/2 := by ring
        _ = h/2 := by rw [hunit,one_mul]
    rw [hc] at herase
    linarith only [herase,he]
  have hh := μ.expected_mass_subset T (localSet A S) hg
    (fun Z => (nextAliveAt_subset _ _ _ _ _).trans sdiff_subset) hp
  simpa only [roundAlive,image_mass,localSet_mass A S hSA,T] using hh

end MetricKMedian.CopyState
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival_oai := @OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival_oai
