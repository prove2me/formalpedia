-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.distant_assignments_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:27:30.80543+00:00
-- url     : https://prove2.me/submissions/17a49dea-c1ec-4bd3-a130-0ae351da52f5

import Mathlib
import Definitions.Def_OAIQ053K043
import Theorems.Thm_OAI_MetricKMedian_Preparation_supplier_assignments_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationCostGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I X : Type*} [DecidableEq I]

theorem far_exchange (Fj Fs : Finset I) (y d : I → ℝ) {R D α : ℝ}
    (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i)
    (hmj : ∑ i ∈ Fj, y i=1) (hms : ∑ i ∈ Fs, y i=1)
    (hα : 0 ≤ α) (hα1 : α < 1) (hD : D ≤ α*R)
    (hupper : ∀ i ∈ Fs \ Fj, d i ≤ R+D)
    (hlower : ∀ i ∈ Fj \ Fs, R-D ≤ d i) :
    (∑ i ∈ Fs, y i*d i) ≤ (1+α)/(1-α)*(∑ i ∈ Fj, y i*d i) := by
  let κ := (1+α)/(1-α)
  have hden : 0 < 1-α := sub_pos.mpr hα1
  have hκ : 1 ≤ κ := (le_div_iff₀ hden).mpr (by linarith only [hα])
  have hκ0 : 0 ≤ κ := le_trans (by norm_num) hκ
  have hκid : κ*(1-α)=1+α := div_mul_cancel₀ _ hden.ne'
  have hr : R+D ≤ κ*(R-D) := by
    apply (mul_le_mul_iff_of_pos_left hden).mp
    calc
      (1-α)*(R+D) ≤ (1+α)*(R-D) := by nlinarith only [hD]
      _ = (1-α)*(κ*(R-D)) := by rw [← mul_assoc,mul_comm (1-α),hκid]
  let c := ∑ i ∈ Fs ∩ Fj, y i*d i
  let m := ∑ i ∈ Fs \ Fj, y i
  have hm0 : 0 ≤ m := sum_nonneg (fun i _ => hy i)
  have hc0 : 0 ≤ c := sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
  have hm : (∑ i ∈ Fj \ Fs, y i)=m := by
    have h1 := sum_inter_add_sum_sdiff Fs Fj y
    have h2 := sum_inter_add_sum_sdiff Fj Fs y
    rw [hms] at h1
    rw [hmj,inter_comm Fj Fs] at h2
    dsimp only [m]
    linarith only [h1,h2]
  have hup : (∑ i ∈ Fs, y i*d i) ≤ c+(R+D)*m := by
    rw [← sum_inter_add_sum_sdiff Fs Fj (fun i => y i*d i)]
    apply add_le_add le_rfl
    dsimp only [m]
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact (mul_le_mul_of_nonneg_left (hupper i hi) (hy i)).trans_eq (mul_comm _ _)
  have hlo : c+(R-D)*m ≤ ∑ i ∈ Fj, y i*d i := by
    rw [← sum_inter_add_sum_sdiff Fj Fs (fun i => y i*d i),inter_comm Fj Fs,← hm]
    apply add_le_add le_rfl
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact (mul_comm (R-D) (y i)).le.trans (mul_le_mul_of_nonneg_left (hlower i hi) (hy i))
  calc
    _ ≤ c+(R+D)*m := hup
    _ ≤ κ*c+κ*((R-D)*m) := add_le_add (le_mul_of_one_le_left hc0 hκ)
      ((mul_le_mul_of_nonneg_right hr hm0).trans_eq (by ring))
    _ = κ*(c+(R-D)*m) := by ring
    _ ≤ κ*(∑ i ∈ Fj, y i*d i) := mul_le_mul_of_nonneg_left hlo hκ0

omit [DecidableEq I] in
 theorem bundle_relocation [PseudoMetricSpace X] (j s t i u : X) {β δ Ls Lt : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hsep : β+δ < 1)
    (hD : dist j s ≤ β*Ls) (hLs : Ls ≤ dist s t) (hLt : Lt ≤ dist s t)
    (hi : dist t i ≤ δ*Lt) (hu : dist t u ≤ δ*Lt) :
    dist j u ≤ (1+2*δ/(1-β-δ))*dist j i := by
  have hden : 0 < 1-β-δ := by linarith only [hsep]
  have hDj : dist j s ≤ β*dist s t := hD.trans (mul_le_mul_of_nonneg_left hLs hβ)
  have hdi : dist t i ≤ δ*dist s t := hi.trans (mul_le_mul_of_nonneg_left hLt hδ)
  have hdu : dist t u ≤ δ*dist s t := hu.trans (mul_le_mul_of_nonneg_left hLt hδ)
  have htri := dist_triangle s j t
  have htri' := dist_triangle j i t
  rw [dist_comm s j] at htri
  rw [dist_comm i t] at htri'
  have hbase : (1-β-δ)*dist s t ≤ dist j i := by linarith only [htri,htri',hDj,hdi]
  have hdst : dist s t ≤ dist j i/(1-β-δ) := (le_div_iff₀ hden).mpr (by nlinarith only [hbase])
  have hnew := dist_triangle j i u
  have hnew' := dist_triangle i t u
  rw [dist_comm i t] at hnew'
  have hh := mul_le_mul_of_nonneg_left hdst (show 0 ≤ 2*δ by positivity)
  calc
    dist j u ≤ dist j i+2*δ*dist s t := by linarith only [hnew,hnew',hdi,hdu]
    _ ≤ dist j i+2*δ*(dist j i/(1-β-δ)) := add_le_add le_rfl hh
    _ = _ := by ring

omit [DecidableEq I] in
 theorem extra_star_charge {β δ γ L c V : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ)
    (hγ : 0 ≤ γ) (hcharge : δ*L*c ≤ V) :
    (β+1+δ)*γ*c*L ≤ ((β+1+δ)*γ/δ)*V := by
  have hc := mul_le_mul_of_nonneg_left hcharge
    (show 0 ≤ (β+1+δ)*γ/δ by positivity)
  have he : (β+1+δ)*γ/δ*(δ*L*c)=(β+1+δ)*γ*c*L := by field_simp
  rw [he] at hc
  exact hc

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_NearestAssignmentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

omit [Fintype I] in

theorem metric_exchange (Fj Fs : Finset I) (y : I → ℝ) (i : I → X) (j s : X)
    {R α : ℝ} (hy : ∀ a, 0 ≤ y a) (hmj : ∑ a ∈ Fj, y a=1)
    (hms : ∑ a ∈ Fs, y a=1) (hα : 0 ≤ α) (hα1 : α < 1)
    (hD : dist j s ≤ α*R) (hmax : ∀ a ∈ Fs, dist s (i a) ≤ R)
    (hmin : ∀ a ∉ Fs, R ≤ dist s (i a)) :
    (∑ a ∈ Fs, y a*dist j (i a)) ≤ (1+α)/(1-α)*(∑ a ∈ Fj, y a*dist j (i a)) := by
  apply far_exchange Fj Fs y (fun a => dist j (i a)) hy (fun _ => dist_nonneg)
    hmj hms hα hα1 hD
  · intro a ha
    have hh := hmax a (mem_sdiff.mp ha).1
    have ht := dist_triangle j s (i a)
    linarith only [hh,ht]
  · intro a ha
    have hh := hmin a (mem_sdiff.mp ha).2
    have ht := dist_triangle s j (i a)
    rw [dist_comm s j] at ht
    linarith only [hh,ht]

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem ordinary_positive (P A : T → Finset I) (y : I → ℝ) (c : T → ℝ)
    (γ : ℝ) (q : Star I T → ℝ) (s u t : T)
    (hy : ∀ i, 0 ≤ y i)
    (htarget : ∀ e, s ∉ targets A e → q e=0)
    (hzero : ∀ e, weight y P A c γ e=0 → q e=0)
    (hq : 0 < q (.inr (.inl (u,t)))) :
    u=s ∧ 0 < ∑ i ∈ A s ∩ P t, y i := by
  have hus : u=s := by
    by_contra h
    have ht := htarget (.inr (.inl (u,t))) (by simpa only [targets,mem_singleton] using Ne.symm h)
    rw [ht] at hq
    exact lt_irrefl _ hq
  subst u
  refine ⟨rfl,lt_of_le_of_ne (sum_nonneg (fun i _ => hy i)) ?_⟩
  intro he
  have hz := hzero (.inr (.inl (s,t))) he.symm
  rw [hz] at hq
  exact lt_irrefl _ hq

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierCharges
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

omit [Fintype I] [DecidableEq I] [DecidableEq T] in
 theorem weighted_mean_charge (F : Finset I) (y d : I → ℝ) (κ : ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    (∑ i ∈ F, y i)*(κ*((∑ i ∈ F, y i*d i)/(∑ i ∈ F, y i)))=κ*(∑ i ∈ F, y i*d i) := by
  by_cases hz : (∑ i ∈ F, y i)=0
  · have hc : (∑ i ∈ F, y i*d i)=0 := by
      apply sum_eq_zero
      intro i hi
      have hle := single_le_sum (fun j _ => hy j) hi
      have h0 : y i=0 := le_antisymm (hle.trans_eq hz) (hy i)
      rw [h0,zero_mul]
    simp only [hz,hc,mul_zero,zero_div]
  · field_simp

omit [Fintype I] [Fintype T] [DecidableEq T] in
 theorem connectionCharge_nonneg (P A : T → Finset I) (y d : I → ℝ)
    (L : T → ℝ) {κ β δ : ℝ} (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i)
    (hL : ∀ t, 0 ≤ L t) (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) :
    ∀ e, 0 ≤ connectionCharge P A y d L κ β δ e := by
  rintro (i | (st | t))
  · exact hd i
  · exact mul_nonneg hκ (div_nonneg (sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i)))
      (sum_nonneg (fun i _ => hy i)))
  · exact mul_nonneg (by linarith only [hβ,hδ]) (hL t)

theorem targeted_connection_charge (P A : T → Finset I) (y d : I → ℝ)
    (c L : T → ℝ) (γ κ β δ : ℝ) (hy : ∀ i, 0 ≤ y i) (s : T) :
    (∑ e, (if s ∈ targets A e then weight y P A c γ e else 0)*connectionCharge P A y d L κ β δ e)=
      (∑ i ∈ A s ∩ outside P, y i*d i)+
      κ*(∑ t, ∑ i ∈ A s ∩ P t, y i*d i)+(β+1+δ)*γ*c s*L s := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [targets,weight,connectionCharge,mem_filter,mem_univ,true_and,mem_singleton]
  have ho : (∑ i, (if i ∈ A s then (if i ∈ outside P then y i else 0) else 0)*d i)=
      ∑ i ∈ A s ∩ outside P, y i*d i := by
    simp only [ite_mul,zero_mul,sum_ite_mem,univ_inter]
  have hb : (∑ u, ∑ t, (if s=u then ∑ i ∈ A u ∩ P t, y i else 0)*
      (κ*((∑ i ∈ A u ∩ P t, y i*d i)/(∑ i ∈ A u ∩ P t, y i))))=
      κ*(∑ t, ∑ i ∈ A s ∩ P t, y i*d i) := by
    simp only [ite_mul,zero_mul,weighted_mean_charge _ y d κ hy,
      sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true, mul_sum]
  have hx : (∑ t, (if s=t then γ*c t else 0)*((β+1+δ)*L t))=(β+1+δ)*γ*c s*L s := by
    simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]
    ring
  rw [ho,hb,hx]
  ring

theorem old_charge_bound (F : Finset I) (P A : T → Finset I) (y d : I → ℝ)
    (p c L : T → ℝ) {γ κ β δ p₀ : ℝ} (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t))) (s : T)
    (hsub : P s ⊆ F) (hA : A s=F \ P s) (hp₀ : 0 < p₀) (hp : p₀ ≤ p s) (hκ : 1 ≤ κ) :
    (∑ i ∈ P s, y i*d i)/p s+
      (∑ e, (if s ∈ targets A e then weight y P A c γ e else 0)*connectionCharge P A y d L κ β δ e) ≤
      max (1/p₀) κ*(∑ i ∈ F, y i*d i)+(β+1+δ)*γ*c s*L s := by
  rw [targeted_connection_charge P A y d c L γ κ β δ hy s]
  let z := fun i => y i*d i
  have hz : ∀ i, 0 ≤ z i := fun i => mul_nonneg (hy i) (hd i)
  have hpart := mass_partition z P hP (A s)
  have hfull : (∑ i ∈ P s, z i)+(∑ i ∈ A s, z i)=∑ i ∈ F, z i := by
    rw [hA,add_comm,sum_sdiff hsub]
  have hmul : (∑ i ∈ P s, z i)/p s ≤ max (1/p₀) κ*(∑ i ∈ P s, z i) := by
    calc
      _ ≤ (∑ i ∈ P s, z i)/p₀ := div_le_div_of_nonneg_left (sum_nonneg (fun i _ => hz i)) hp₀ hp
      _ = (1/p₀)*(∑ i ∈ P s, z i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (sum_nonneg (fun i _ => hz i))
  have hout : (∑ i ∈ A s ∩ outside P, z i) ≤ max (1/p₀) κ*(∑ i ∈ A s ∩ outside P, z i) :=
    le_mul_of_one_le_left (sum_nonneg (fun i _ => hz i)) (hκ.trans (le_max_right _ _))
  have hb : κ*(∑ t, ∑ i ∈ A s ∩ P t, z i) ≤ max (1/p₀) κ*(∑ t, ∑ i ∈ A s ∩ P t, z i) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (sum_nonneg (fun t _ => sum_nonneg (fun i _ => hz i)))
  change (∑ i ∈ P s, z i)/p s+((∑ i ∈ A s ∩ outside P, z i)+κ*(∑ t, ∑ i ∈ A s ∩ P t, z i)+_)
    ≤ max (1/p₀) κ*(∑ i ∈ F, z i)+_
  calc
    _ ≤ max (1/p₀) κ*(∑ i ∈ P s, z i)+
        (max (1/p₀) κ*(∑ i ∈ A s ∩ outside P, z i)+
          max (1/p₀) κ*(∑ t, ∑ i ∈ A s ∩ P t, z i)+(β+1+δ)*γ*c s*L s) :=
      add_le_add hmul (add_le_add (add_le_add hout hb) le_rfl)
    _ = max (1/p₀) κ*((∑ i ∈ P s, z i)+((∑ i ∈ A s ∩ outside P, z i)+
          (∑ t, ∑ i ∈ A s ∩ P t, z i)))+(β+1+δ)*γ*c s*L s := by ring
    _ = _ := by rw [hpart,hfull]

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem request_connection_radius (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ γ β : ℝ} (G : BundleGeometry F y s i V M δ)
    (hy : ∀ a, 0 ≤ y a) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
    (j : X) (t : T) (hD : 0 < G.c t → dist j (s t) ≤ β*G.L t)
    (q : Star I T → ℝ) (htarget : ∀ e, t ∉ targets G.A e → q e=0)
    (hzero : ∀ e, weight y G.P G.A G.c γ e=0 → q e=0) :
    ∀ e, 0 < q e → match supplier G.next e with
      | .inl a => dist j (i a) ≤ connectionCharge G.P G.A y (fun a => dist j (i a)) G.L
          (1+2*δ/(1-β-δ)) β δ e
      | .inr u => ∀ a ∈ G.P u, dist j (i a) ≤
          connectionCharge G.P G.A y (fun a => dist j (i a)) G.L (1+2*δ/(1-β-δ)) β δ e := by
  have hAP : ∀ t, Disjoint (G.A t) (G.P t) := fun t => by
    rw [G.missing t]
    exact sdiff_disjoint
  rintro (a | (ut | u)) he
  · exact le_rfl
  · obtain ⟨hut,hw⟩ := ordinary_positive G.P G.A y G.c γ q t ut.1 ut.2 hy htarget hzero he
    rcases ut with ⟨u,v⟩
    dsimp only at hut
    subst u
    dsimp only [supplier,connectionCharge]
    intro a ha
    have hvt : v ≠ t := by
      intro hv
      subst v
      rw [disjoint_iff_inter_eq_empty.mp (hAP t),sum_empty] at hw
      exact lt_irrefl _ hw
    have hct : 0 < G.c t := by
      rw [← G.deficit_mass t]
      exact hw.trans_le (sum_le_sum_of_subset_of_nonneg inter_subset_left (fun a _ _ => hy a))
    have hnv : G.next v ≠ v := fun hv => hvt ((G.self_singleton v hv t).symm)
    have hr : ∀ b ∈ G.A t ∩ G.P v, dist j (i a) ≤
        (1+2*δ/(1-β-δ))*dist j (i b) := by
      intro b hb
      apply bundle_relocation j (s t) (s v) (i b) (i a) hβ hδ hsep (hD hct)
      · exact G.closest t v hvt.symm
      · exact (G.closest v t hvt).trans_eq (dist_comm _ _)
      · exact G.radius v hnv b (mem_inter.mp hb).2
      · exact G.radius v hnv a ha
    have hs : (∑ b ∈ G.A t ∩ G.P v, y b)*dist j (i a) ≤
        (1+2*δ/(1-β-δ))*(∑ b ∈ G.A t ∩ G.P v, y b*dist j (i b)) := by
      rw [sum_mul,mul_sum]
      exact sum_le_sum (fun b hb => (mul_le_mul_of_nonneg_left (hr b hb) (hy b)).trans_eq (by ring))
    calc
      dist j (i a) ≤ ((1+2*δ/(1-β-δ))*(∑ b ∈ G.A t ∩ G.P v, y b*dist j (i b)))/
          (∑ b ∈ G.A t ∩ G.P v, y b) := (le_div_iff₀ hw).mpr (by nlinarith only [hs])
      _ = _ := by ring
  · have hut : u=t := by
      by_contra hn
      have hz := htarget (.inr (.inr u)) (by simpa only [targets,mem_singleton] using Ne.symm hn)
      rw [hz] at he
      exact lt_irrefl _ he
    subst u
    have hct : 0 < G.c t := by
      apply lt_of_le_of_ne (G.nonneg t)
      intro hz
      have heq := hzero (.inr (.inr t)) (by simp only [weight,← hz,mul_zero])
      rw [heq] at he
      exact lt_irrefl _ he
    have hn : G.next t ≠ t := fun ht => (ne_of_gt hct) (G.self_zero t ht)
    have hnn : G.next (G.next t) ≠ G.next t := fun ht => hn (G.self_singleton (G.next t) ht t).symm
    dsimp only [supplier,connectionCharge]
    intro a ha
    have hLn : G.L (G.next t) ≤ G.L t :=
      (G.closest (G.next t) t hn).trans_eq ((dist_comm _ _).trans (G.next_distance t).symm)
    have hr := (G.radius (G.next t) hnn a ha).trans (mul_le_mul_of_nonneg_left hLn hδ)
    have ht := dist_triangle j (s t) (i a)
    have ht' := dist_triangle (s t) (s (G.next t)) (i a)
    rw [← G.next_distance t] at ht'
    nlinarith only [ht,ht',hr,hD hct]

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_DistantAssignments
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem distant_assignments_s53_oai (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ g γ B v p₀ α β : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hδ : 0 < δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
    (hg : 0 < g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (hp₀ : 0 < p₀) (hp : ∀ t, p₀ ≤ G.p t) (hα : 0 ≤ α) (hα1 : α < 1)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hms : ∑ a ∈ F t, y a=1) (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hV : V t ≤ v) (R : ℝ) (hDα : dist j (s t) ≤ α*R)
    (hmax : ∀ a ∈ F t, dist (s t) (i a) ≤ R)
    (hmin : ∀ a ∉ F t, R ≤ dist (s t) (i a))
    (hDβ : 0 < G.c t → dist j (s t) ≤ β*G.L t) :
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        farFactor δ p₀ α β γ*v := by
  classical
  let d := fun a => dist j (i a)
  let κ := 1+2*δ/(1-β-δ)
  let charge := connectionCharge G.P G.A y d G.L κ β δ
  have hκ : 1 ≤ κ := le_add_of_nonneg_right (div_nonneg (by positivity) (by linarith only [hsep]))
  have hκ0 : 0 ≤ κ := le_trans (by norm_num) hκ
  have hAP : ∀ u, Disjoint (G.A u) (G.P u) := fun u => by
    rw [G.missing u]
    exact sdiff_disjoint
  have hrad : ∀ ω, 0 < L.ν.weight ω → ∀ ξ, 0 < (L.κ ω).weight ξ →
      ∀ e, 0 < L.R ω t e → match supplier G.next e with
        | .inl a => d a ≤ charge e
        | .inr u => ∀ a, 0 < L.C ω ξ (u,a) → d a ≤ charge e := by
    intro ω hω ξ hξ e he
    let q : Star I T → ℝ := fun e => (L.R ω t e:ℝ)
    have ht : ∀ e, t ∉ targets G.A e → q e=0 := by
      intro e ht
      simp only [q,L.request_target ω t e ht,Nat.cast_zero]
    have hz : ∀ e, weight y G.P G.A G.c γ e=0 → q e=0 := by
      intro e hz
      have hh := L.request_cap ω hω t e
      rw [L.open_zero ω hω e hz] at hh
      simp only [q,Nat.eq_zero_of_le_zero hh,Nat.cast_zero]
    have hr := request_connection_radius F y s i V G hy hδ.le hβ hsep j t hDβ q ht hz e (show 0 < (L.R ω t e:ℝ) by exact_mod_cast he)
    cases hs : supplier G.next e with
    | inl a => simpa only [hs] using hr
    | inr u =>
      simp only [hs] at hr
      intro a ha
      apply hr a
      by_contra hn
      rw [(L.pieces ω ξ hξ u).2.2 a hn] at ha
      exact Nat.lt_irrefl _ ha
  obtain ⟨r,hr,hc⟩ := supplier_assignments_s53 G.P G.A y G.p G.c hg hunit L G.next G.self_zero
    hAP t d charge hy (fun _ => dist_nonneg) (hp₀.trans_le (hp t))
    (connectionCharge_nonneg G.P G.A y d G.L hy (fun _ => dist_nonneg)
      (fun t => by rw [G.next_distance t]; exact dist_nonneg) hκ0 hβ hδ.le) hrad
  refine ⟨r,?_,hc.trans ?_⟩
  · intro z hz
    refine ⟨?_, (hr z hz).2⟩
    intro a
    cases a <;> exact (hr z hz).1 _
  apply (old_charge_bound (F t) G.P G.A y d G.p G.c G.L hy (fun _ => dist_nonneg)
    G.disjoint t (G.sub t) (G.missing t) hp₀ (hp t) hκ).trans
  have hex := metric_exchange Fj (F t) y i j (s t) hy hmj hms hα hα1 hDα hmax hmin
  rw [hvj] at hex
  have hbase := mul_le_mul_of_nonneg_left hex
    (show 0 ≤ max (1/p₀) κ from le_trans hκ0 (le_max_right _ _))
  have hext := (extra_star_charge hβ hδ hγ (G.charge t)).trans
    (mul_le_mul_of_nonneg_left hV (show 0 ≤ (β+1+δ)*γ/δ by positivity))
  exact (add_le_add hbase hext).trans_eq (by dsimp only [farFactor,κ]; ring)

end MetricKMedian.Preparation
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.distant_assignments_s53_oai := @OAI.MetricKMedian.Preparation.distant_assignments_s53_oai
