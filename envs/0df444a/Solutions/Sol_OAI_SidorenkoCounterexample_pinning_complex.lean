-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.pinning_complex
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-08T17:32:35.96328+00:00
-- url     : https://prove2.me/submissions/f0478c4b-7a1b-4b56-97ca-2a437f1cf207

import Mathlib
import Definitions.Def_SidorenkoRefinementColors
import Theorems.Thm_OAI_SidorenkoCounterexample_refinement_round_0
import Theorems.Thm_OAI_SidorenkoCounterexample_refinement_round_1
import Theorems.Thm_OAI_SidorenkoCounterexample_refinement_round_2
import Theorems.Thm_OAI_SidorenkoCounterexample_refinement_round_3

namespace OAI.SidorenkoCounterexample
open Classical
open scoped BigOperators
section
variable {I J E C : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
lemma histogram_weighted (t : E → I) (c : E → C) (f : I → C → ℝ) :
    (∑ i,∑ d,(neighborHistogram t c i d:ℝ)*f i d)=∑ e,f (t e) (c e) := by
  simp only [neighborHistogram,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
  calc
    _ = ∑ i,∑ e,∑ d,(if t e=i ∧ c e=d then (1:ℝ) else 0)*f i d := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = ∑ e,∑ i,∑ d,(if t e=i ∧ c e=d then (1:ℝ) else 0)*f i d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro e _
      simp [ite_and,ite_mul]

noncomputable def roundScores (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C) : VertexPairScores I J where
  left a := -(∑ c,(neighborHistogram t (cJ ∘ h) a c:ℝ)^2)
  right b := -(∑ c,(neighborHistogram h (cI ∘ t) b c:ℝ)^2)
  pair a b := 2*(neighborHistogram t (cJ ∘ h) a (cJ b):ℝ)+2*(neighborHistogram h (cI ∘ t) b (cI a):ℝ)

lemma roundScore_formula (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    (roundScores t h cI cJ).score t h a b=
    (∑ i,∑ c,(2*(neighborHistogram t (cJ ∘ h) i c:ℝ)*(neighborHistogram t (cJ ∘ h) (a i) c:ℝ)-
      (neighborHistogram t (cJ ∘ h) (a i) c:ℝ)^2))+
    (∑ j,∑ c,(2*(neighborHistogram h (cI ∘ t) j c:ℝ)*(neighborHistogram h (cI ∘ t) (b j) c:ℝ)-
      (neighborHistogram h (cI ∘ t) (b j) c:ℝ)^2)) := by
  have hL := histogram_weighted t (cJ ∘ h) (fun i c => 2*(neighborHistogram t (cJ ∘ h) (a i) c:ℝ))
  have hR := histogram_weighted h (cI ∘ t) (fun j c => 2*(neighborHistogram h (cI ∘ t) (b j) c:ℝ))
  simp only [Function.comp_apply] at hL hR
  simp only [VertexPairScores.score,roundScores,ha,hb,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  rw [←hL,←hR]
  simp only [Finset.sum_sub_distrib]
  have hmul (x y : ℝ) : x*(2*y)=2*x*y := by ring
  simp only [hmul]
  ring

lemma roundScore_loss (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    (roundScores t h cI cJ).score t h id id-(roundScores t h cI cJ).score t h a b=
    (∑ i,∑ c,((neighborHistogram t (cJ ∘ h) (a i) c:ℝ)-(neighborHistogram t (cJ ∘ h) i c:ℝ))^2)+
    (∑ j,∑ c,((neighborHistogram h (cI ∘ t) (b j) c:ℝ)-(neighborHistogram h (cI ∘ t) j c:ℝ))^2) := by
  rw [roundScore_formula t h cI cJ id id (fun _ => rfl) (fun _ => rfl),roundScore_formula t h cI cJ a b ha hb]
  simp only [id_eq]
  have halg (x y : ℝ) : (2*x*x-x^2)-(2*x*y-y^2)=(y-x)^2 := by ring
  rw [show ∀ x y z w : ℝ,x+y-(z+w)=(x-z)+(y-w) by intros; ring]
  simp only [←Finset.sum_sub_distrib,halg]
end
end OAI.SidorenkoCounterexample

namespace OAI


section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Mix
variable {A : Type*} [Fintype A]
lemma exists_positive_perturbation (f g : A → ℝ) (hf : ∀ a,0≤f a)
    (hg : ∀ a,f a=0 → 0≤g a) :
    ∃ ε : ℝ,0<ε ∧ ∀ a,0≤f a+ε*g a ∧ (f a+ε*g a=0 ↔ f a=0 ∧ g a=0) := by
  have hv : ∀ᶠ ε : ℝ in nhds 0,∀ a,f a≠0 → 0<f a+ε*g a := by
    apply eventually_all.mpr; intro a
    by_cases h : f a=0
    · exact Filter.Eventually.of_forall (fun _ hn => (hn h).elim)
    · have hpos : 0<f a := lt_of_le_of_ne (hf a) (Ne.symm h)
      have ht : Tendsto (fun ε : ℝ => f a+ε*g a) (nhds 0) (nhds (f a)) := by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => f a) (nhds 0) (nhds (f a))).add ((tendsto_id : Tendsto (fun ε : ℝ => ε) (nhds 0) (nhds 0)).mul_const (g a))
      exact (ht.eventually (lt_mem_nhds hpos)).mono (fun _ h _ => h)
  have hw : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),0<ε ∧ ∀ a,f a≠0 → 0<f a+ε*g a :=
    eventually_mem_nhdsWithin.and (hv.filter_mono nhdsWithin_le_nhds)
  obtain ⟨ε,hε,he⟩ := hw.exists
  refine ⟨ε,hε,fun a => ?_⟩
  by_cases ha : f a=0
  · have hga := hg a ha
    rw [ha,zero_add]
    refine ⟨mul_nonneg hε.le hga,?_⟩
    simp only [true_and]
    exact mul_eq_zero.trans (or_iff_right (ne_of_gt hε))
  · have hp := he a ha
    exact ⟨hp.le,iff_of_false (ne_of_gt hp) (fun h => ha h.1)⟩
end Mix
section Pin
variable {I J E C : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
omit [DecidableEq I] [DecidableEq C] in
lemma sum_hist_sq_nonneg (f g : I → C → ℕ) :
    0≤∑ i,∑ c,((f i c:ℝ)-(g i c:ℝ))^2 :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
omit [DecidableEq I] [DecidableEq C] in
lemma sum_hist_sq_eq_zero (f g : I → C → ℕ) :
    (∑ i,∑ c,((f i c:ℝ)-(g i c:ℝ))^2)=0 ↔ f=g := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Finset.mem_univ,forall_true_left]
  simp only [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),Finset.mem_univ,forall_true_left,
    sq_eq_zero_iff,sub_eq_zero,Nat.cast_inj]
  exact ⟨fun h => funext (fun i => funext (h i)),fun h => by rw [h]; simp⟩
lemma roundScore_loss_properties (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    let loss := (roundScores t h cI cJ).score t h id id-(roundScores t h cI cJ).score t h a b
    0≤loss ∧ (loss=0 ↔
      (∀ i,neighborHistogram t (cJ ∘ h) (a i)=neighborHistogram t (cJ ∘ h) i) ∧
      (∀ j,neighborHistogram h (cI ∘ t) (b j)=neighborHistogram h (cI ∘ t) j)) := by
  dsimp only
  rw [roundScore_loss t h cI cJ a b ha hb]
  have hL := sum_hist_sq_nonneg (fun i => neighborHistogram t (cJ ∘ h) (a i)) (neighborHistogram t (cJ ∘ h))
  have hR := sum_hist_sq_nonneg (fun j => neighborHistogram h (cI ∘ t) (b j)) (neighborHistogram h (cI ∘ t))
  refine ⟨add_nonneg hL hR,?_⟩
  rw [add_eq_zero_iff_of_nonneg hL hR,sum_hist_sq_eq_zero,sum_hist_sq_eq_zero]
  simp only [funext_iff]

noncomputable def VertexPairScores.mix (s r : VertexPairScores I J) (ε : ℝ) : VertexPairScores I J where
  left i := s.left i+ε*r.left i
  right j := s.right j+ε*r.right j
  pair i j := s.pair i j+ε*r.pair i j
omit [DecidableEq I] [DecidableEq J] in
lemma VertexPairScores.score_mix (s r : VertexPairScores I J) (ε : ℝ)
    (t : E → I) (h : E → J) (a : I → I) (b : J → J) :
    (s.mix r ε).score t h a b=s.score t h a b+ε*r.score t h a b := by
  simp only [score,mix,Finset.sum_add_distrib,←Finset.mul_sum]; ring

def PreservesColors (cI : I → C) (cJ : J → C) (m : (I → I) × (J → J)) : Prop :=
  (∀ i,cI (m.1 i)=cI i) ∧ ∀ j,cJ (m.2 j)=cJ j
lemma pinning_step (t : E → I) (h : E → J) (cI dI : I → C) (cJ dJ : J → C)
    (hI : ∀ v w,dI v=dI w ↔ cI v=cI w ∧ neighborHistogram t (cJ ∘ h) v=neighborHistogram t (cJ ∘ h) w)
    (hJ : ∀ v w,dJ v=dJ w ↔ cJ v=cJ w ∧ neighborHistogram h (cI ∘ t) v=neighborHistogram h (cI ∘ t) w)
    (s : VertexPairScores I J)
    (hs : ∀ m : (I → I) × (J → J),0≤ s.score t h id id-s.score t h m.1 m.2 ∧
      (s.score t h id id-s.score t h m.1 m.2=0 ↔ PreservesColors cI cJ m)) :
    ∃ snew : VertexPairScores I J,∀ m : (I → I) × (J → J),0≤ snew.score t h id id-snew.score t h m.1 m.2 ∧
      (snew.score t h id id-snew.score t h m.1 m.2=0 ↔ PreservesColors dI dJ m) := by
  let r := roundScores t h cI cJ
  let f (m : (I → I) × (J → J)) := s.score t h id id-s.score t h m.1 m.2
  let g (m : (I → I) × (J → J)) := r.score t h id id-r.score t h m.1 m.2
  have hg (m) (hm : f m=0) := (hs m).2.mp hm
  have hp (m) (hm : f m=0) := roundScore_loss_properties t h cI cJ m.1 m.2 (hg m hm).1 (hg m hm).2
  obtain ⟨ε,hε,he⟩ := exists_positive_perturbation f g (fun m => (hs m).1) (fun m hm => (hp m hm).1)
  refine ⟨s.mix r ε,fun m => ?_⟩
  have halg : (s.mix r ε).score t h id id-(s.mix r ε).score t h m.1 m.2=f m+ε*g m := by
    simp only [VertexPairScores.score_mix,f,g]; ring
  rw [halg]
  refine ⟨(he m).1,(he m).2.trans ?_⟩
  constructor
  · rintro ⟨hf,hg0⟩
    obtain ⟨hL,hR⟩ := (hp m hf).2.mp hg0
    exact ⟨fun i => (hI _ _).mpr ⟨(hg m hf).1 i,hL i⟩,fun j => (hJ _ _).mpr ⟨(hg m hf).2 j,hR j⟩⟩
  · intro hm
    have hc : PreservesColors cI cJ m := ⟨fun i => ((hI _ _).mp (hm.1 i)).1,fun j => ((hJ _ _).mp (hm.2 j)).1⟩
    have hf := (hs m).2.mpr hc
    exact ⟨hf,(hp m hf).2.mpr ⟨fun i => ((hI _ _).mp (hm.1 i)).2,fun j => ((hJ _ _).mp (hm.2 j)).2⟩⟩
end Pin
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
lemma pinning_scores_proved : ∃ s : VertexPairScores (Fin 13) (Fin 22),
    ∀ a b,(a,b)≠(id,id) → s.score cornerPoint (fun k : ActCorner => k.1) a b < s.score cornerPoint (fun k : ActCorner => k.1) id id := by
  let t := cornerPoint
  let h := fun k : ActCorner => k.1
  let s0 : VertexPairScores (Fin 13) (Fin 22) := ⟨fun _ => 0,fun _ => 0,fun _ _ => 0⟩
  have hcI : ∀ i,refineLeft0 i=0 := by decide
  have hcJ : ∀ j,refineRight0 j=1 := by decide
  have hs0 (m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22)) :
      0 ≤ s0.score t h id id-s0.score t h m.1 m.2 ∧
      (s0.score t h id id-s0.score t h m.1 m.2=0 ↔ PreservesColors refineLeft0 refineRight0 m) := by
    simp only [VertexPairScores.score,s0,Finset.sum_const_zero,add_zero,sub_self,le_refl,true_and]
    exact iff_of_true trivial ⟨fun i => (hcI _).trans (hcI i).symm,fun j => (hcJ _).trans (hcJ j).symm⟩
  have hI0 := refinement_round_0.1
  have hJ0 := refinement_round_0.2
  obtain ⟨s1,hs1⟩ := pinning_step t h refineLeft0 refineLeft1 refineRight0 refineRight1 hI0 hJ0 s0 hs0
  have hI1 := refinement_round_1.1
  have hJ1 := refinement_round_1.2
  obtain ⟨s2,hs2⟩ := pinning_step t h refineLeft1 refineLeft2 refineRight1 refineRight2 hI1 hJ1 s1 hs1
  have hI2 := refinement_round_2.1
  have hJ2 := refinement_round_2.2
  obtain ⟨s3,hs3⟩ := pinning_step t h refineLeft2 refineLeft3 refineRight2 refineRight3 hI2 hJ2 s2 hs2
  have hI3 := refinement_round_3.1
  have hJ3 := refinement_round_3.2.1
  obtain ⟨s4,hs4⟩ := pinning_step t h refineLeft3 refineLeft4 refineRight3 refineRight4 hI3 hJ3 s3 hs3
  refine ⟨s4,fun a b hne => ?_⟩
  have hp := hs4 (a,b)
  have hn : s4.score t h id id-s4.score t h a b≠0 := by
    intro hz
    have hc := hp.2.mp hz
    apply hne
    exact Prod.ext (funext (fun i => refinement_round_3.2.2.1 (hc.1 i))) (funext (fun j => refinement_round_3.2.2.2 (hc.2 j)))
  exact sub_pos.mp (lt_of_le_of_ne hp.1 (Ne.symm hn))
end SidorenkoCounterexample

end



end OAI

open OAI.SidorenkoCounterexample
theorem solution : ∃ s : VertexPairScores (Fin 13) (Fin 22),
    ∀ a b,(a,b)≠(id,id) → s.score cornerPoint (fun k : ActCorner => k.1) a b < s.score cornerPoint (fun k : ActCorner => k.1) id id := by
  exact OAI.SidorenkoCounterexample.pinning_scores_proved

