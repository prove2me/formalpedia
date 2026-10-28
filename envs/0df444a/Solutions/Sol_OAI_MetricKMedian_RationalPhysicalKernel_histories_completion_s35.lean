-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:25:02.950021+00:00
-- url     : https://prove2.me/submissions/d83d7c50-0545-4b86-ae58-1bd1d45a4549

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_Completion_Rational_output_potential_s35
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_valid_s35

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

theorem mass_sdiff [DecidableEq I] (g : ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    mass g (S \ T) = mass g S - mass g T := by
  unfold mass
  rw [Finset.card_sdiff_of_subset hTS, Nat.cast_sub (Finset.card_le_card hTS)]
  ring

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GreedyPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Completion
open Finset PhysicalPotential
variable {J I : Type*} [DecidableEq J] [DecidableEq I]

omit [DecidableEq J] in
                                                                           
theorem packing_mass {g : ℝ} (hg : 0 ≤ g) (A : Finset J) (B : J → Finset I)
    (active : Finset I) (hB : ∀ j ∈ A, B j ⊆ active)
    (hdis : (↑A : Set J).PairwiseDisjoint B)
    (hunit : ∀ j ∈ A, 1 ≤ mass g (B j)) :
    (A.card:ℝ) ≤ mass g active := by
  have hu : A.biUnion B ⊆ active := by
    intro i hi
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hi
    exact hB j hj hij
  have he : (∑ j ∈ A, mass g (B j))=mass g (A.biUnion B) := by
    simp only [mass, card_biUnion hdis, Nat.cast_sum, mul_sum]
  have hh := sum_le_sum hunit
  simp only [sum_const, nsmul_eq_mul, mul_one] at hh
  exact (hh.trans_eq he).trans (mass_mono hg hu)

omit [DecidableEq J] [DecidableEq I] in

theorem packed_connection {X : Type*} [PseudoMetricSpace X]
    (client : J → X) (location : I → X) (R : J → ℝ) (B : J → Finset I)
    (hR : ∀ j i, i ∈ B j → dist (client j) (location i) ≤ R j)
    {j a : J} (hr : R a ≤ R j) (hinter : ¬Disjoint (B j) (B a))
    {opened : I} (ho : opened ∈ B a) :
    dist (client j) (location opened) ≤ 3*R j := by
  obtain ⟨i,hij,hia⟩ := not_disjoint_iff.mp hinter
  have h1 := dist_triangle (client j) (location i) (client a)
  have h2 := dist_triangle (client j) (client a) (location opened)
  have hi := hR j i hij
  have ha := hR a i hia
  have ho' := hR a opened ho
  rw [dist_comm (location i) (client a)] at h1
  linarith only [h1,h2,hi,ha,ho',hr]

end MetricKMedian.Completion
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

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalGreedyCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Completion.Rational
open Finset PhysicalPotential CopyState Preparation
variable {j : ℕ} {I : Type*} [DecidableEq I]

theorem packing_spec (t : ℕ) (U : Finset (Fin j)) (R : Fin j → ℚ) (B : Fin j → Finset I)
    (hU : U.card ≤ t) (hB : ∀ c ∈ U, (B c).Nonempty) :
    packing t U R B ⊆ U ∧ (↑(packing t U R B) : Set (Fin j)).PairwiseDisjoint B ∧
      ∀ c ∈ U, ∃ a ∈ packing t U R B, R a ≤ R c ∧ ¬ Disjoint (B c) (B a) := by
  induction t generalizing U with
  | zero =>
    have hu : U=∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hU)
    subst U
    simp [packing]
  | succ t ih =>
    by_cases hu : U.Nonempty
    · let c := firstNearest U R hu
      have hc : c∈U := (firstNearest_spec U R hu).1
      have hmin : ∀ i∈U, R c ≤ R i := (firstNearest_spec U R hu).2
      let V := U.filter (fun i => Disjoint (B c) (B i))
      have hVU : V ⊆ U := filter_subset _ _
      have hcV : c∉V := by
        intro h
        have hd := (mem_filter.mp h).2
        obtain ⟨a,ha⟩ := hB c hc
        exact disjoint_left.mp hd ha ha
      have hlt : V.card<U.card := card_lt_card <|
        Finset.ssubset_iff_subset_ne.mpr ⟨hVU,fun he => hcV (he ▸ hc)⟩
      obtain ⟨hsub,hdis,hcover⟩ := ih V (by omega) (fun i hi => hB i (hVU hi))
      rw [packing, dite_eq_left hu]
      change insert c (packing t V R B) ⊆ U ∧ _
      refine ⟨insert_subset hc (hsub.trans hVU),?_,?_⟩
      · rw [coe_insert]
        apply hdis.insert
        intro a ha _
        exact (mem_filter.mp (hsub ha)).2
      · intro i hi
        by_cases hiv : i∈V
        · obtain ⟨a,ha,hr,hd⟩ := hcover i hiv
          exact ⟨a,mem_insert_of_mem ha,hr,hd⟩
        · exact ⟨c,mem_insert_self _ _,hmin i hi,
            fun hd => hiv (mem_filter.mpr ⟨hi,hd.symm⟩)⟩
    · have hue : U=∅ := not_nonempty_iff_eq_empty.mp hu
      subst U
      simp [packing]

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.Completion.Rational.instLinearOrderCopy
theorem output_spec (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (location : F → X) (client : Fin j → X)
    (hdist : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (hR : ∀ c, 0 ≤ R c) {g : ℝ} (hg : 0≤g) (hunit : g*(Δ:ℝ)=1)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) (hm : ∀ c, mass g (B c)=1)
    (hd : ∀ c i, i∈B c → d c i.1 ≤ R c)
    (hbackup : ∀ c, (¬∃ f∈integral Δ A, d c f ≤ 5*R c) → B c ⊆ A) :
    integral Δ A ⊆ output d R A B hB ∧
    ((output d R A B hB).card:ℝ) ≤ mass g A ∧
    ∀ c, ∃ f∈output d R A B hB, d c f ≤ 5*R c := by
  let Q := integral Δ A
  let U := uncovered d R A
  let C := packing j U R B
  have hpick : ∀ c, pick B hB c∈B c := fun c => min'_mem _ _
  have hcard : U.card ≤ j := (card_le_univ U).trans_eq (Fintype.card_fin j)
  obtain ⟨hCU,hdis,hcover⟩ := packing_spec j U R B hcard (fun c _ => hB c)
  have hres : resets Δ Q ⊆ A := by
    intro i hi
    exact (mem_integral Δ A i.1).mp ((mem_resets Δ Q i).mp hi)
      ((mem_slots Δ i.1 i).mpr rfl)
  have hbucket : ∀ c∈U, B c ⊆ A \ resets Δ Q := by
    intro c hc i hi
    have hn := (mem_filter.mp hc).2
    refine mem_sdiff.mpr ⟨hbackup c hn hi,?_⟩
    intro hir
    have hif := (mem_resets Δ Q i).mp hir
    exact hn ⟨i.1,hif,(hd c i hi).trans (by linarith only [hR c])⟩
  have hcount : (C.card:ℝ) ≤ mass g A-(Q.card:ℝ) := by
    have hh := packing_mass hg C B (A \ resets Δ Q)
      (fun c hc => hbucket c (hCU hc)) hdis (fun c _ => (hm c).ge)
    rw [mass_sdiff g hres,reset_mass Δ Q hunit] at hh
    exact hh
  refine ⟨subset_union_left,?_,?_⟩
  · have hh : ((output d R A B hB).card:ℝ) ≤ (Q.card:ℝ)+(C.card:ℝ) := by
      exact_mod_cast (card_union_le Q (C.image (fun c => (pick B hB c).1))).trans
        (Nat.add_le_add_left card_image_le Q.card)
    linarith only [hh,hcount]
  · intro c
    by_cases hc : c∈U
    · obtain ⟨a,ha,hRa,hinter⟩ := hcover c hc
      refine ⟨(pick B hB a).1,mem_union_right Q (mem_image.mpr ⟨a,ha,rfl⟩),?_⟩
      have hh := packed_connection client (fun i : Copy (F := F) Δ => location i.1)
        (fun c => (R c:ℝ)) B (fun c i hi => by rw [hdist]; exact_mod_cast hd c i hi)
        (by exact_mod_cast hRa) hinter (hpick a)
      rw [hdist] at hh
      have hr : (0:ℝ)≤R c := by exact_mod_cast hR c
      have hhh : (d c (pick B hB a).1:ℝ) ≤ 5*(R c:ℝ) := by linarith only [hh,hr]
      exact_mod_cast hhh
    · have hex : ∃ f∈Q, d c f ≤ 5*R c := by
        simpa only [U,uncovered,mem_filter,mem_univ,true_and,not_not] using hc
      obtain ⟨f,hf,hfd⟩ := hex
      exact ⟨f,mem_union_left _ hf,hfd⟩

end MetricKMedian.Completion.Rational
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistoryCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential CopyState Completion.Rational
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

theorem histories_completion_s35_oai (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hBA : ∀ c, B c⊆A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1≤R c)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    let O := completed d R B hB g β z;
    ((O.card:ℝ)≤ mass (g:ℝ) z.1.1) ∧
    (0<j → O.Nonempty) ∧
    (score d O:ℝ) ≤ ∑ c, (
      potential (x T) (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1))
        (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())
        (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ z.1.1))+
      5*(R c:ℝ)*mass (g:ℝ)
        (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())) := by
  let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val]
  have hbackup : ∀ c, (¬∃ f∈integral Δ z.1.1, d c f≤5*R c) → B c⊆z.1.1 := by
    intro c hn
    have hv := histories_valid_s35 d₀ location (fun (_ : Unit) => client c) hd₀ g β p φ P hp hφ hupper A
      (fun _ => B c) (fun _ => (R c:ℝ)) T x hg hunit hP hP1 hA (fun _ => hBA c)
      (fun _ => by exact_mod_cast hR c) (fun _ => hm c)
      (fun _ i hi => by rw [hd]; exact_mod_cast hdR c i hi) a
    apply hv.2.2.2 ()
    intro h
    obtain ⟨f,hf,hfd⟩ := h
    rw [hd] at hfd
    dsimp only at hfd
    exact hn ⟨f,hf,by exact_mod_cast hfd⟩
  obtain ⟨_,hc,hn⟩ := output_spec d R location client hd hR hg.le hunit z.1.1 B hB hm hdR hbackup
  refine ⟨hc,?_,?_⟩
  · intro hj
    obtain ⟨f,hf,_⟩ := hn ⟨0,hj⟩
    exact ⟨f,hf⟩
  · exact output_potential_s35 d R location client hd hR hg.le hunit z.1.1 B
      (fun c => replay g β x (fun (_ : Unit) f => dist (client c) (location f))
        (fun _ => B c) z ()) hB hm hdR hbackup

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s35_oai := @OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s35_oai
