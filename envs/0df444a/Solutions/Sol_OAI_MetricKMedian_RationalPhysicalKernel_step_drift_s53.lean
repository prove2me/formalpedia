-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:31:29.475535+00:00
-- url     : https://prove2.me/submissions/80231900-1e95-47ec-9d48-6ad74f641bdf

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K043
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s53
import Theorems.Thm_OAI_MetricKMedian_CopyState_rational_conditional_round_drift_s53
import Theorems.Thm_OAI_MetricKMedian_GeneratorAverage_averaged_ideal_drift_s53
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_MomentAnalysis
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
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalPotential
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

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_FixedBatchTransition
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

 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_ChunkCharges
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
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem charge_eq_zero (D : Actions I E) (x g b : ℝ) (d : I → ℝ)
    (S : Finset I) {e : E} (he : e ∉ relevant D S) : charge D x g b d S e=0 := by
  have hn : ¬(e ∈ D.ordinary ∧ D.source e ∈ S) := fun h => he ((mem_relevant D S e).mpr (.inl h))
  have hi : S ∩ D.erase e=∅ := by
    apply not_nonempty_iff_eq_empty.mp
    exact fun h => he ((mem_relevant D S e).mpr (.inr h))
  simp only [charge, ite_eq_right hn, hi, mass, PhysicalPotential.cost, card_empty, Nat.cast_zero, mul_zero,
    sum_empty, zero_mul, sub_zero]

 theorem sum_charge_relevant (D : Actions I E) (x g b : ℝ) (d : I → ℝ) (S : Finset I) :
    (∑ e ∈ relevant D S, charge D x g b d S e)=∑ e, charge D x g b d S e := by
  apply sum_subset (subset_univ _)
  intro e _ he
  exact charge_eq_zero D x g b d S he

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_PotentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic Finset

variable {I : Type*}

theorem B_le_one {x : ℝ} (hx : 0 ≤ x) : B x ≤ 1 := by
  have h := P_le_half_s53 hx
  unfold B
  linarith only [h]

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyTransport
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

 theorem image_cost (A : Finset (Copy (F := F) Δ)) (S : Finset A) (g : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    PhysicalPotential.cost g d (S.image Subtype.val)=
      PhysicalPotential.cost g (fun i => d i.val) S := by
  unfold PhysicalPotential.cost
  rw [sum_image (fun _ _ _ _ he => Subtype.ext he)]

 theorem localSet_mass (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (g : ℝ) :
    mass g (localSet A S)=mass g S := by
  rw [← image_mass,localSet_image A S hS]

 theorem localSet_cost (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (g : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    PhysicalPotential.cost g (fun i => d i.val) (localSet A S)=PhysicalPotential.cost g d S := by
  rw [← image_cost,localSet_image A S hS]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_SourceGenerator
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseGraph.cast_edge
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

 theorem indicator_sum (G : I → Finset I) (S : Finset I) (h : I) (f : I → ℝ) :
    (∑ i : S, f i*GraphLaw.edge G h i)=∑ i ∈ S ∩ (graphActions G).erase h, f i := by
  rw [sum_coe_sort S (fun i => f i*GraphLaw.edge G h i)]
  simp only [GraphLaw.edge, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_inter, mem_graph_erase]

 theorem nonindicator_sum (G : I → Finset I) (S : Finset I) (h : I) (f : I → ℝ) :
    (∑ i : S, f i*(1-GraphLaw.edge G h i))=∑ i ∈ S \ (graphActions G).erase h, f i := by
  rw [sum_coe_sort S (fun i => f i*(1-GraphLaw.edge G h i))]
  have he : ∀ i, f i*(1-GraphLaw.edge G h i)=if h ∉ G i then f i else 0 := by
    intro i
    by_cases hi : h ∈ G i <;> simp [GraphLaw.edge, hi]
  simp only [he]
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_sdiff, mem_graph_erase]

 theorem graph_removed_mass (G : I → Finset I) (S : Finset I) (h : I) (g : ℝ) :
    (∑ i : S, g*GraphLaw.edge G h i)=mass g (S ∩ (graphActions G).erase h) := by
  rw [indicator_sum G S h (fun _ => g)]
  simp only [mass, sum_const, nsmul_eq_mul, mul_comm]

 theorem graph_removed_cost (G : I → Finset I) (S : Finset I) (h : I) (g : ℝ) (d : I → ℝ) :
    (∑ i : S, g*d i*GraphLaw.edge G h i)=PhysicalPotential.cost g d (S ∩ (graphActions G).erase h) :=
  indicator_sum G S h (fun i => g*d i)

theorem source_generator_identity (G : I → Finset I) (S : Finset I)
    (x g b : ℝ) (d : I → ℝ) :
    g*(∑ h ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S h)=
      inside g (coefficient x (mass g S)) (potential x g d S b) (fun i : S => d i)
        (fun (_ : Unit) h i => GraphLaw.edge G h i) ()+
      external g (coefficient x (mass g S)) (B x) (PhysicalPotential.cost g d S)
        (fun h : (Sᶜ : Finset I) => min b (d h)) (fun i : S => d i)
        (fun (_ : Unit) h i => GraphLaw.edge G h i) () := by
  rw [sum_charge_relevant, mul_sum, ← sum_add_sum_compl S]
  congr 1
  · unfold inside
    simp only
    rw [sum_coe_sort S (fun h => g*(d h -
      (∑ i : S, g*(1-GraphLaw.edge G h i)*max (d h-coefficient x (mass g S)*d i) 0) -
      potential x g d S b))]
    apply sum_congr rfl
    intro h hh
    have hin : h ∈ (graphActions G).ordinary ∧ (graphActions G).source h ∈ S :=
      ⟨mem_univ h, hh⟩
    rw [charge, ite_eq_left hin]
    have hs : (∑ i : S, g*(1-GraphLaw.edge G h i)*max (d h-coefficient x (mass g S)*d i) 0)=
        ∑ i ∈ S \ (graphActions G).erase h, g*max (d h-coefficient x (mass g S)*d i) 0 := by
      calc
        _ = ∑ i : S, (g*max (d h-coefficient x (mass g S)*d i) 0)*(1-GraphLaw.edge G h i) := by
          apply sum_congr rfl
          intro i _
          ring
        _ = _ := nonindicator_sum G S h (fun i => g*max (d h-coefficient x (mass g S)*d i) 0)
    rw [hs]
    rfl
  · unfold external
    simp only [removedMass, removedCost, graph_removed_mass, graph_removed_cost]
    rw [sum_coe_sort (Sᶜ : Finset I) (fun h => g*(
      mass g (S ∩ (graphActions G).erase h)*min b (d h) -
      coefficient x (mass g S)*PhysicalPotential.cost g d (S ∩ (graphActions G).erase h) -
      B x*mass g (S ∩ (graphActions G).erase h)*
        (PhysicalPotential.cost g d S-PhysicalPotential.cost g d (S ∩ (graphActions G).erase h))))]
    apply sum_congr rfl
    intro h hh
    have hout : ¬(h ∈ (graphActions G).ordinary ∧ (graphActions G).source h ∈ S) := by
      rintro ⟨_, hs⟩
      exact mem_compl.mp hh hs
    rw [charge, ite_eq_right hout]
    rfl

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_SourceDriftLaw
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseGraph.cast_edge _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
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

theorem source_drift_of_law (μ : FiniteLaw (I → Finset I)) (Δ : ℕ) (S : Finset I) {g x pHat ζ b : ℝ}
    (d N : I → ℝ) (q : I → I → ℝ)
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : mass g S ≤ 1)
    (hd : ∀ i, 0 ≤ d i) (hN : ∀ i, 0 ≤ N i)
    (hq0 : ∀ h i, 0 ≤ q h i) (hq1 : ∀ h i, q h i ≤ 1)
    (hsum : ∀ i, ∑ h, q h i=Δ)
    (hp0 : 0 ≤ pHat) (hp1 : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i ∈ S, ∀ t ∈ S, q t i < 1 → N i*(1-pHat*q t i) ≤ d i+d t)
    (htaper : ∀ h i, 0 < q h i → min b (d h) ≤ d i+(1-pHat*q h i)*N i)
    (hfirst : ∀ h i, μ.expect (fun G => GraphLaw.edge G h i)=q h i)
    (hpair : ∀ h k i j, i ≠ j → μ.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G k j)=q h i*q k j) :
    timeRate x (mass g S)*PhysicalPotential.cost g d S+
      μ.expect (fun G => g*∑ h ∈ relevant (graphActions G) S,
        charge (graphActions G) x g b d S h) ≤
      B x*g*PhysicalPotential.cost g d S+12*ζ*PhysicalPotential.cost g d S := by
  have hysum : (∑ _i : S, g)=mass g S := by
    simp [mass, mul_comm]
  have hV : (∑ i : S, g*d i)=PhysicalPotential.cost g d S := sum_coe_sort S (fun i => g*d i)
  have hmass : ∀ i : S, (∑ h : (Sᶜ : Finset I), g*q h i)=1-∑ t : S, g*q t i := by
    intro i
    have hh := congrArg (fun z : ℝ => g*z) (hsum i)
    rw [mul_sum, hunit, ← sum_add_sum_compl S] at hh
    rw [sum_coe_sort S (fun t => g*q t i), sum_coe_sort (Sᶜ : Finset I) (fun t => g*q t i)]
    linarith only [hh]
  have ha := averaged_ideal_drift_s53 μ (fun i : S => d i) (fun i : S => N i)
    (fun h : (Sᶜ : Finset I) => min b (d h))
    (fun G (h i : S) => GraphLaw.edge G h i)
    (fun G (h : (Sᶜ : Finset I)) (i : S) => GraphLaw.edge G h i)
    (fun (h i : S) => q h i) (fun (h : (Sᶜ : Finset I)) (i : S) => q h i)
    hg hx0 hx1 hysum hy (fun i => hd i) (fun i => hN i)
    (fun h i => hq0 h i) (fun h i => hq1 h i) (fun h i => hq0 h i) (fun h i => hq1 h i)
    hmass hp0 hp1 hζ0 hζ1 he (fun i t => hcomp i i.property t t.property)
    (fun _ => min_le_left _ _) (fun h i => htaper h i)
    (fun h i => hfirst h i) (fun h i => hfirst h i)
    (fun G h i => by unfold GraphLaw.edge; split_ifs <;> norm_num)
    (fun h i t hit => hpair h h i t (fun hh => hit (Subtype.ext hh)))
  dsimp only at ha
  rw [hV] at ha
  have hid : ∀ G, g*(∑ h ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S h)=
      inside g (coefficient x (mass g S))
        (coefficient x (mass g S)*PhysicalPotential.cost g d S+(1-mass g S)*b)
        (fun i : S => d i) (fun (G : I → Finset I) (h i : S) => GraphLaw.edge G h i) G+
      external g (coefficient x (mass g S)) (B x) (PhysicalPotential.cost g d S)
        (fun h : (Sᶜ : Finset I) => min b (d h)) (fun i : S => d i)
        (fun (G : I → Finset I) (h : (Sᶜ : Finset I)) (i : S) => GraphLaw.edge G h i) G := by
    intro G
    rw [source_generator_identity, potential, ← coefficient_eq]
    rfl
  simp_rw [hid]
  exact ha

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraph
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I X : Type*} [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

theorem GraphData.drift {Δ : ℕ} {g P x ζ b : ℝ} {location : I → X} {own : I → Finset I}
    (D : GraphData Δ g P location own) (μ : FiniteLaw (I → Finset I))
    (client : X) (S : Finset I)
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (hP : 0 ≤ P) (hP1 : P ≤ 1/2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : PhysicalPotential.mass g S ≤ 1)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |P-Analytic.P x| ≤ ζ)
    (hfirst : ∀ h i, μ.expect (fun G => GraphLaw.edge G h i)=D.marginal h i)
    (hpair : ∀ h k i j, i ≠ j → μ.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G k j)=
      D.marginal h i*D.marginal k j) :
    Analytic.timeRate x (PhysicalPotential.mass g S)*
        PhysicalPotential.cost g (fun i => dist client (location i)) S+
      μ.expect (fun G => g*∑ h ∈ FixedBatch.relevant (FixedBatch.graphActions G) S,
        FixedBatch.charge (FixedBatch.graphActions G) x g b
          (fun i => dist client (location i)) S h) ≤
      Analytic.B x*g*PhysicalPotential.cost g (fun i => dist client (location i)) S+
        12*ζ*PhysicalPotential.cost g (fun i => dist client (location i)) S := by
  apply FixedBatch.source_drift_of_law μ Δ S (fun i => dist client (location i))
    D.radius D.marginal hg hunit hx0 hx1 hy (fun _ => dist_nonneg) D.radius_nonneg
    D.marginal_nonneg D.marginal_le_one D.incoming_count hP hP1 hζ0 hζ1 he
    _ _ hfirst hpair
  · intro i _ t _ hq
    apply (D.lower t i hq).trans
    simpa only [dist_comm (location i) client] using
      (dist_triangle (location i) client (location t))
  · intro h i hq
    have ht := dist_triangle client (location i) (location h)
    have hu := D.upper h i hq
    have hm := min_le_right b (dist client (location h))
    nlinarith only [ht,hu,hm]

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRealExpectation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_def (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.expectation f=∑ i : Fin μ.length, (μ.law.rational.weight i:ℝ)*f μ.states[i.val] := rfl

theorem expectation_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℝ) :
    (μ.bindIndexed κ).expectation f=
      ∑ a, (μ.law.rational.weight a:ℝ)*(κ a).expectation f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  calc
    _ = ∑ z, (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val] := by
      unfold expectation realIndex
      change (∑ i, (((ρ.integer.reindex finSigmaFinEquiv).rational.weight i):ℝ)*
        f ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
          (κ z.1).states[z.2.val]))[i.val])) = _
      simp only [Vector.getElem_ofFn]
      change (∑ i, (ρ.integer.rational.weight (finSigmaFinEquiv.symm i):ℝ)*
        f (κ (finSigmaFinEquiv.symm i).1).states[(finSigmaFinEquiv.symm i).2.val]) = _
      simp only [RationalLaw.integer_weight]
      exact (finSigmaFinEquiv (n := fun a => (κ a).length)).symm.sum_comp
        (fun z : Sigma (fun a : Fin μ.length => Fin (κ a).length) =>
          (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val])
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [ρ,RationalLaw.sigma,Rat.cast_mul,mul_assoc,← mul_sum,expectation_def]

theorem expectation_map (μ : SparseIntegerLaw α) (g : α → β) (f : β → ℝ) :
    (μ.map g).expectation f=μ.expectation (fun a => f (g a)) := by
  simp only [expectation_def,map,Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMixture
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem real_expect_all [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.real.expect f=μ.expectation f := by
  rw [real,FiniteLaw.expect_map]
  rfl

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalRoundEvents
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem events_expectation (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) (V : Event I g β → ℝ) :
    (events μ Δ g β p φ hp hφ hupper).expectation V=
      μ.expectation (fun G =>
        (proposal G Δ g β p φ hp hφ hupper
          (enumeration (graph G) (heavySet (graphMass G g) β))).expectation (fun Z => V ⟨G,Z⟩)) := by
  rw [events,SparseIntegerLaw.expectation_bindIndexed]
  simp only [SparseIntegerLaw.expectation_def,SparseIntegerLaw.map,Vector.getElem_map]

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalKernel
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem step_expectation (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (V : State F Δ g β → ℝ) :
    (step d g β p φ P hp hφ hupper s).expectation V=
      (graphLaw d g P s.1).expectation (fun G =>
        (RationalBatchData.proposal G Δ g β p φ hp hφ hupper
          (RationalBatchData.enumeration (RationalBatchData.graph G)
            (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))).expectation
          (fun Z => V (updateEvent g β s.1 ⟨G,Z⟩))) := by
  exact (SparseIntegerLaw.expectation_map
    (RationalBatchData.events (graphLaw d g P s.1) Δ g β p φ hp hφ hupper)
    (updateEvent g β s.1) V).trans
      (RationalBatchData.events_expectation (graphLaw d g P s.1) Δ g β p φ hp hφ hupper
        (fun e => V (updateEvent g β s.1 e)))

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalDrift
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.rationalPhysicalDriftCopyOrder
theorem step_drift_s53_oai (d₀ : F → F → ℚ) (location : F → X) (client : X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ P : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (S S₀ : Finset (Copy (F := F) Δ))
    {x h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) s.1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |(P:ℝ)-Analytic.P x| ≤ ζ)
    (hactive : S ⊆ s.1) (hS : S ⊆ S₀) (hm₀ : mass (g:ℝ) S₀=1)
    (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
    (step d₀ g β p φ P hp hφ hupper s).expectation (fun t =>
      potential (x*Real.exp (-h)) (g:ℝ) (fun i => dist client (location i.1))
        (labels g β x (fun (_ : Unit) f => dist client (location f)) t (fun _ => S) ())
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ t.1))) ≤
      potential x (g:ℝ) (fun i => dist client (location i.1)) S
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ s.1))+
      h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  let d := fun f => dist client (location f)
  let V := PhysicalPotential.cost (g:ℝ) (fun i => d i.1) S
  let b := GroupCap.cap R d (integral Δ s.1)
  let f := potential x (g:ℝ) (fun i => d i.1) S b
  let a := timeRate x (mass (g:ℝ) S)*V
  let μ := graphLaw d₀ g P s.1
  let chargeSum := fun G => (g:ℝ)*∑ e ∈ relevant (graphActions G) (localSet s.1 S),
    charge (graphActions G) x (g:ℝ) b (fun i => d i.val.1) (localSet s.1 S) e
  let ν : (G : s.1 → Finset s.1) → SparseIntegerLaw
      (Finset (HeavyAction (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))) :=
    fun G => RationalBatchData.proposal G Δ g β p φ hp hφ hupper
    (RationalBatchData.enumeration (RationalBatchData.graph G)
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
  let v := fun (G : s.1 → Finset s.1) Z =>
    potential (x*Real.exp (-h)) (g:ℝ) (fun i => d i.1)
      (roundAlive s.1 S G (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z x (g:ℝ) d)
      (GroupCap.cap R d (integral Δ (next Δ s.1
        (roundErased s.1 G (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z)
        (roundOpened s.1 G (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z))))
  obtain ⟨D,hgood,hfirst,hpair⟩ := graph_data_s53 d₀ location hd₀ g P s.1 hg hunit hP hP1 hA
  have hcond : ∀ G, 0 < μ.real.weight G →
      (ν G).real.expect (v G) ≤ f+h*(a+chargeSum G)+batchConstant Δ*h*((φ:ℝ)+h)*R := by
    intro G hG
    have hh := rational_conditional_round_drift_s53 s.1 S S₀ G g β p φ hp hφ hupper
      (RationalBatchData.enumeration (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β)) d hprob
      (hgood G hG).1 (hgood G hG).2.1 hg hg1 hunit hx0 hx1 hh0 hh1 hφ1 hsmall
      hactive hS hm₀ (fun _ => dist_nonneg) hR0 hdR hR
    dsimp only at hh
    rw [FiniteLaw.expect_sub,FiniteLaw.expect_const] at hh
    change (ν G).real.expect (v G)-f ≤ h*(a+chargeSum G)+_ at hh
    linarith only [hh]
  have hav := μ.real.expect_mono_support hcond
  simp_rw [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_mul] at hav
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const] at hav
  have hy : mass (g:ℝ) (localSet s.1 S) ≤ 1 := by
    rw [localSet_mass _ _ hactive]
    exact (mass_mono hg.le hS).trans_eq hm₀
  have hgen := D.drift (b := b) μ.real client (localSet s.1 S) hg hunit hP.le hP1
    hx0 hx1 hy hζ0 hζ1 he hfirst hpair
  rw [localSet_mass _ _ hactive,localSet_cost _ _ hactive (g:ℝ)
    (fun i => dist client (location i.1))] at hgen
  change a+μ.real.expect chargeSum ≤ B x*(g:ℝ)*V+12*ζ*V at hgen
  have hVB := mul_le_mul_of_nonneg_right (B_le_one hx0)
    (mul_nonneg hg.le (cost_nonneg hg.le (fun _ _ => dist_nonneg) : 0 ≤ V))
  have hgen' : a+μ.real.expect chargeSum ≤ ((g:ℝ)+12*ζ)*V := by
    nlinarith only [hgen,hVB]
  have hmul := mul_le_mul_of_nonneg_left hgen' hh0
  have hfinish : μ.real.expect (fun G => (ν G).real.expect (v G)) ≤
      f+h*((g:ℝ)+12*ζ)*V+batchConstant Δ*h*((φ:ℝ)+h)*R := by
    linarith only [hav,hmul]
  rw [step_expectation]
  change μ.expectation (fun G => (ν G).expectation (v G)) ≤
    f+h*((g:ℝ)+12*ζ)*V+batchConstant Δ*h*((φ:ℝ)+h)*R
  rw [← SparseIntegerLaw.real_expect_all]
  have hpoint : ∀ G, (ν G).expectation (v G)=(ν G).real.expect (v G) :=
    fun G => (SparseIntegerLaw.real_expect_all (ν G) (v G)).symm
  simp_rw [hpoint]
  exact hfinish

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53_oai := @OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53_oai
