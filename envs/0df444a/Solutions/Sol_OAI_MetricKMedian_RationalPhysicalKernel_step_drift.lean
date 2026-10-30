-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.step_drift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:49:37.539978+00:00
-- url     : https://prove2.me/submissions/a6abaa61-3f14-4719-86bc-8db3f19d0d4b

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half
import Theorems.Thm_OAI_MetricKMedian_CopyState_rational_conditional_round_drift
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data
import Theorems.Thm_OAI_MetricKMedian_Taper_GraphData_drift

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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_PotentialBounds
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
  have h := P_le_half hx
  unfold B
  linarith only [h]

end MetricKMedian.PhysicalPotential
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRealExpectation
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMixture
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalDrift
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
theorem step_drift_oai (d₀ : F → F → ℚ) (location : F → X) (client : X)
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
  obtain ⟨D,hgood,hfirst,hpair⟩ := graph_data d₀ location hd₀ g P s.1 hg hunit hP hP1 hA
  have hcond : ∀ G, 0 < μ.real.weight G →
      (ν G).real.expect (v G) ≤ f+h*(a+chargeSum G)+batchConstant Δ*h*((φ:ℝ)+h)*R := by
    intro G hG
    have hh := rational_conditional_round_drift s.1 S S₀ G g β p φ hp hφ hupper
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

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.step_drift_oai := @OAI.MetricKMedian.RationalPhysicalKernel.step_drift_oai
