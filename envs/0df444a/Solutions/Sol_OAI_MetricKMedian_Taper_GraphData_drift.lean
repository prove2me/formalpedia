-- Prove2me | solution 1 for OAI.MetricKMedian.Taper.GraphData.drift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:40:28.475638+00:00
-- url     : https://prove2.me/submissions/0e59f731-9746-4754-850c-35df9a0868a0

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K021
import Theorems.Thm_OAI_MetricKMedian_GeneratorAverage_averaged_ideal_drift

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

 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_ChunkCharges
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
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceDriftLaw
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
  have ha := averaged_ideal_drift μ (fun i : S => d i) (fun i : S => N i)
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
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperGraph
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

theorem GraphData.drift_oai {Δ : ℕ} {g P x ζ b : ℝ} {location : I → X} {own : I → Finset I}
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

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedian.Taper.GraphData.drift_oai.{u_1, u_2} := @OAI.MetricKMedian.Taper.GraphData.drift_oai.{u_1, u_2}
