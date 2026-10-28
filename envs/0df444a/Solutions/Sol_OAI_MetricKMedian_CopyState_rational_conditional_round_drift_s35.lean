-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:16:10.409205+00:00
-- url     : https://prove2.me/submissions/ed506a53-50e8-4f6b-a0eb-937acad8f070

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_CopyState_round_cap_s35
import Theorems.Thm_OAI_MetricKMedian_RationalBatchData_proposal_local_bound_s35

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

theorem point_cost_le {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) {i : I} (hi : i ∈ S) : g * d i ≤ cost g d S := by
  exact Finset.single_le_sum (fun j hj => mul_nonneg hg (hd j hj)) hi

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

 theorem image_potential (A : Finset (Copy (F := F) Δ)) (S : Finset A) (x g b : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    potential x g d (S.image Subtype.val) b=potential x g (fun i => d i.val) S b := by
  unfold potential
  rw [image_mass,image_cost]

 theorem localSet_potential (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (x g b : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    potential x g (fun i => d i.val) (localSet A S) b=potential x g d S b := by
  rw [← image_potential,localSet_image A S hS]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_GroupCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.GroupCap
open Finset
variable {F E : Type*}

 theorem le_cap (R : ℝ) (d : F → ℝ) (O : Finset F) (c : ℝ) :
    c ≤ cap R d O ↔ c ≤ 5*R ∧ ∀ f ∈ O, c ≤ d f := le_fold_min _

 theorem cap_le_radius (R : ℝ) (d : F → ℝ) (O : Finset F) : cap R d O ≤ 5*R :=
  (fold_min_le _).mpr (Or.inl le_rfl)

 theorem cap_le_member (R : ℝ) (d : F → ℝ) (O : Finset F) {f : F} (hf : f ∈ O) :
    cap R d O ≤ d f := (fold_min_le _).mpr (Or.inr ⟨f,hf,le_rfl⟩)

 theorem cap_nonneg {R : ℝ} (d : F → ℝ) (O : Finset F)
    (hR : 0 ≤ R) (hd : ∀ f, 0 ≤ d f) : 0 ≤ cap R d O :=
  (le_cap R d O 0).mpr ⟨by positivity,fun f _ => hd f⟩

 theorem cap_antitone (R : ℝ) (d : F → ℝ) {O O' : Finset F} (hO : O ⊆ O') :
    cap R d O' ≤ cap R d O :=
  (le_cap R d O _).mpr ⟨cap_le_radius R d O',fun _ hf => cap_le_member R d O' (hO hf)⟩

end MetricKMedian.GroupCap
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_LocalForceScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Finset Analytic
variable {I : Type*} [DecidableEq I]

theorem local_cap_scale {g b R : ℝ} {d : I → ℝ} {S S₀ : Finset I}
    (hg : 0 < g) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd : ∀ i ∈ S₀, 0 ≤ d i) (hb : 0 ≤ b) (hbR : b ≤ 5*R)
    (hR : ∃ i ∈ S₀, R=d i) :
    b ≤ 5*(cost g d S+(1-mass g S)*b)/g := by
  let Q := cost g d S+(1-mass g S)*b
  have hy : mass g S ≤ 1 := (mass_mono hg.le hS).trans_eq hm₀
  have hV0 := cost_nonneg hg.le (fun i hi => hd i (hS hi))
  have hVQ : cost g d S ≤ Q := le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hy) hb)
  have hQ : 0 ≤ Q := hV0.trans hVQ
  change b ≤ 5*Q/g
  apply (le_div_iff₀ hg).mpr
  by_cases heq : S=S₀
  · obtain ⟨i, hi, hRi⟩ := hR
    have hp := point_cost_le hg.le (fun i hi => hd i (hS hi)) (heq.symm ▸ hi)
    rw [← hRi] at hp
    have hm := mul_le_mul_of_nonneg_right hbR hg.le
    nlinarith only [hp, hm, hVQ]
  · have hc : S.card < S₀.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS, heq⟩)
    have hc' : (S.card:ℝ)+1 ≤ (S₀.card:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hc)
    have hmul := mul_le_mul_of_nonneg_left hc' hg.le
    have hgap : g ≤ 1-mass g S := by
      unfold mass at hm₀ ⊢
      nlinarith only [hmul, hm₀]
    have hb' := mul_le_mul_of_nonneg_right hgap hb
    dsimp only [Q] at hQ ⊢
    nlinarith only [hb', hV0, hQ]

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

omit [Fintype F] in
 theorem forcedAlive_subset (A S : Finset (Copy (F := F) Δ)) (H : Finset A) :
    forcedAlive A S H ⊆ localSet A S := filter_subset _ _

omit [Fintype F] in
 theorem heavy_alive_forced (A S : Finset (Copy (F := F) Δ)) (H : Finset A) :
    H ∩ localSet A S ⊆ forcedAlive A S H := by
  intro i hi
  exact mem_filter.mpr ⟨(mem_inter.mp hi).2,
    mem_image.mpr ⟨i,(mem_inter.mp hi).1,rfl⟩⟩

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalBatchData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

theorem graph_eq (G : I → Finset I) : graph G=graphActions G := rfl

theorem heavy_eq (Full : Actions I I) (H : Finset I) : heavy Full H=heavyActions Full H := rfl

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseConditionalRoundDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F : Type} [DecidableEq F] [Fintype F] {Δ n : ℕ}

theorem rational_conditional_round_drift_s35_oai (A S S₀ : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (RationalBatchData.graph G)
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
    {x h R : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hSA : S ⊆ A) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd0 : ∀ f, 0 ≤ d f) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, d i.1 ≤ R)
    (hR : ∃ i ∈ S₀, R=d i.1) :
    let H := RationalBatchData.heavySet (RationalBatchData.graphMass G g) β
    let μ := RationalBatchData.proposal G Δ g β p φ hp hφ hupper enum
    μ.real.expect (fun Z => potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))-
      potential x g (fun i => d i.1) S (GroupCap.cap R d (integral Δ A))) ≤
    h*(timeRate x (mass g S)*PhysicalPotential.cost g (fun i => d i.1) S+
      (g:ℝ)*(∑ e ∈ relevant (graphActions G) (localSet A S),
        charge (graphActions G) x g (GroupCap.cap R d (integral Δ A))
          (fun i => d i.val.1) (localSet A S) e))+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  intro H μ
  let D := heavyActions (graphActions G) H
  let b := GroupCap.cap R d (integral Δ A)
  let b' := GroupCap.cap R d (integral Δ A ∪ forcedGroups A H)
  have hb0 : 0 ≤ b := GroupCap.cap_nonneg d _ hR0 hd0
  have hbR : b ≤ 5*R := GroupCap.cap_le_radius R d _
  have hb'0 : 0 ≤ b' := GroupCap.cap_nonneg d _ hR0 hd0
  have hb' : b' ≤ b := GroupCap.cap_antitone R d subset_union_left
  have hy : mass g (localSet A S) ≤ 1 := by
    rw [localSet_mass A S hSA]
    exact (mass_mono hg.le hS).trans_eq hm₀
  have hbQ : b ≤ 5*((PhysicalPotential.cost g (fun i : A => d i.val.1) (localSet A S)+
      (1-mass g (localSet A S))*b)/g) := by
    rw [localSet_mass A S hSA,localSet_cost A S hSA g (fun i => d i.1)]
    simpa only [mul_div_assoc] using local_cap_scale hg hS hm₀ (fun i _ => hd0 i.1) hb0 hbR hR
  have hbF : ∀ i ∈ forcedAlive A S H, b' ≤ d i.val.1 := by
    intro i hi
    exact GroupCap.cap_le_member R d _ (mem_union_right _ (mem_filter.mp hi).2)
  have hbH : ∀ i ∈ H, b' ≤ d i.val.1 := by
    intro i hi
    exact GroupCap.cap_le_member R d _ (mem_union_right _ (mem_image.mpr ⟨i,hi,rfl⟩))
  have hh := RationalBatchData.proposal_local_bound_s35 G (localSet A S) (forcedAlive A S H) Δ
    g β p φ hp hφ hupper enum (fun i => d i.val.1) hprob
    hG hg hg1 hunit hx0 hx1 hh0 hh1 hφ1 hsmall
    hy (forcedAlive_subset A S H) (heavy_alive_forced A S H) (fun i => hd0 i.val.1) hR0
    (fun i hi => hdR i.val (hS ((mem_localSet _ _ _).mp hi)))
    hbQ hb0 hbR hb'0 hb' hbF hbH
  dsimp only at hh
  change μ.real.expect _ ≤ _ at hh
  have hpoint : ∀ Z, potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))=
    potential (x*Real.exp (-h)) g (fun i : A => d i.val.1)
      (nextAliveAt D (coefficient x (mass g (localSet A S))) (fun i => d i.val.1)
        (localSet A S \ forcedAlive A S H) Z)
      (nextCap D (fun i => d i.val.1) b' Z) := by
    intro Z
    rw [round_cap_s35 A G H Z R d hG hown]
    unfold roundAlive
    rw [image_potential,localSet_mass A S hSA]
  have hequal := congrArg
    (fun v : Finset (HeavyAction (graphActions G) H) → ℝ =>
      μ.real.expect (fun Z => v Z-potential x g (fun i => d i.1) S b)) (funext hpoint)
  apply hequal.le.trans
  convert hh using 1 <;>
    (try simp only [localSet_mass A S hSA,localSet_cost A S hSA g (fun i => d i.1),
    localSet_potential A S hSA x g b (fun i => d i.1),b,D,H,
    RationalBatchData.heavy_eq,RationalBatchData.graph_eq])
  all_goals rfl

end MetricKMedian.CopyState
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s35_oai := @OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s35_oai
