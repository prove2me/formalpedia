-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.pooled_tail_test
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:55:11.227967+00:00
-- url     : https://prove2.me/submissions/14b99429-7690-484a-8344-116d47f146a1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L952-L1074
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.pooled_tail_test. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_opposite_crossing_le
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_primal_filter_tail_le
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_replaced_tail_eq
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_segment_filter_tail
import Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_jensen_sq
import Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_joint_budget
import Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_pooled_mass
import Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_sqrt_pooled
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_norm_combine_le
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_norm_cone_mean_le
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_test_energy_le_allow_empty

-- ---- from OAI.Analysis.DiamondDistortion.FiniteAverage ----
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace FiniteAverage
variable {Ω : Type*} [Fintype Ω]

lemma sum_mul_sq_le (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hs : ∑ ω,w ω = 1) (f : Ω → ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hf : (∑ ω, w ω * f ω ^ 2) ≤ V) :
    |∑ ω, w ω * f ω| ≤ Real.sqrt V := by
  have h := (jensen_sq w f hw hs).trans hf
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by
    rw [sq_abs, Real.sq_sqrt hV]
    exact h)

lemma norm_mean_le_sqrt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω,w ω = 1)
    (z : Ω → E) {V : ℝ} (hV : 0 ≤ V)
    (hz : (∑ ω, w ω * ‖z ω‖ ^ 2) ≤ V) :
    ‖∑ ω, w ω • z ω‖ ≤ Real.sqrt V := by
  calc
    _ ≤ ∑ ω, ‖w ω • z ω‖ := norm_sum_le _ _
    _ = ∑ ω, w ω * ‖z ω‖ := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw ω)]
    _ ≤ |∑ ω, w ω * ‖z ω‖| := le_abs_self _
    _ ≤ _ := sum_mul_sq_le w hw hs (fun ω => ‖z ω‖) hV hz

end FiniteAverage

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma sub_filterPrimal (p : ι → Prop) (u : T.Primal) :
    u - T.filterPrimal p u = T.filterPrimal (fun x => ¬ p x) u := by
  apply Finsupp.ext
  intro v
  change T.ofPrimal (u - T.filterPrimal p u) v =
    T.ofPrimal (T.filterPrimal (fun x => ¬ p x) u) v
  simp only [ofPrimal_sub, ofPrimal_filter, Finsupp.sub_apply, Finsupp.filter_apply]
  split_ifs <;> simp_all

lemma sum_units_eq_filter (H : Finset ι) (u : T.Primal) :
    (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) = T.filterPrimal (· ∈ H) u := by
  classical
  apply Finsupp.ext
  intro w
  change T.ofPrimal (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) w =
    T.ofPrimal (T.filterPrimal (· ∈ H) u) w
  simp only [ofPrimal_sum, ofPrimal_smul, ofPrimal_filter, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp [ofPrimal, unitFinite, Finsupp.single_apply,
    mul_ite, Finset.sum_ite_eq']
  convert (Finsupp.filter_apply (· ∈ H) (T.ofPrimal u) w).symm using 1
  all_goals congr

lemma headPrimal_coe (H : Finset ι) (u : T.Primal) :
    T.headPrimal H (u : T.JamesSpace) =
      (T.filterPrimal (· ∈ H) u : T.JamesSpace) := by
  classical
  rw [headPrimal_apply, ← T.sum_units_eq_filter]
  simp only [coordinate_coe, unitVector]
  change (∑ v ∈ H, T.ofPrimal u v •
    (UniformSpace.Completion.toComplL (𝕜 := ℝ)) (T.unitFinite v)) =
    (UniformSpace.Completion.toComplL (𝕜 := ℝ)) (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v)
  simp only [map_sum, map_smul]

lemma tailDual_apply_apply (H : Finset ι) (x : T.Dual) (u : T.JamesSpace) :
    T.tailDual H x u = x (u - T.headPrimal H u) := by
  simp [tailDual_apply, mul_comm]

lemma combine_sub {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a b : κ → ℝ) :
    T.combine S (a-b) = T.combine S a - T.combine S b := by
  unfold combine
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact sub_smul (a i) (b i) (T.segmentFunctional (S i))

lemma combine_unit_of_mem (F : T.Family) (a : Fin F.n → ℝ)
    (i : Fin F.n) {v : ι} (hv : v ∈ F.seg i) :
    T.combine F.seg a (T.unitVector v) = a i := by
  classical
  rw [combine_unit, Finset.sum_eq_single i]
  · simp only [ite_eq_left hv]
  · intro j _ hji
    rw [ite_eq_right (fun h => Finset.disjoint_left.mp (F.disjoint hji) h hv)]
  · simp

lemma combine_smul {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ) (c : ℝ) :
    T.combine S (fun i => c * a i) = c • T.combine S a := by
  simp only [combine, mul_smul, Finset.smul_sum]

variable {T}

variable (T)

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
lemma interval_chain {S : Finset ι} (hS : A.segments.IsSegment S) :
    ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a := by
  obtain ⟨l, r, _, hmem⟩ := hS
  intro a ha b hb
  exact A.predecessors_total ((hmem a).mp ha).2 ((hmem b).mp hb).2

lemma gates_eq_of_le {H : Set ι} {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgh : g ≤ h) : g = h := by
  by_contra hne
  exact hg.1 (hh.2 g (lt_of_le_of_ne hgh hne))

lemma gates_eq_of_common_upper {H : Set ι} {g h v : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgv : g ≤ v) (hhv : h ≤ v) : g = h := by
  rcases A.predecessors_total hgv hhv with h | h
  · exact A.gates_eq_of_le hg hh h
  · exact (A.gates_eq_of_le hh hg h).symm

lemma gate_unique_in_segment {H : Set ι} {S : Finset ι}
    (hS : A.segments.IsSegment S) {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgS : g ∈ S) (hhS : h ∈ S) : g = h := by
  rcases A.interval_chain hS g hgS h hhS with h | h
  · exact A.gates_eq_of_le hg hh h
  · exact (A.gates_eq_of_le hh hg h).symm

lemma gate_coefficient_energy {κ : Type*} [Fintype κ] {H : Set ι}
    (F : A.segments.Family) (a : Fin F.n → ℝ)
    (gate : κ ↪ ι) (hg : ∀ g, A.Gate H (gate g)) :
    (∑ g, (A.segments.combine F.seg a (A.segments.unitVector (gate g))) ^ 2) ≤
      ∑ i, a i ^ 2 := by
  classical
  let P : κ → Prop := fun g => ∃ i, gate g ∈ F.seg i
  let M := {g : κ // P g}
  choose idx hidx using fun g : M => g.property
  have hinj : Function.Injective idx := by
    intro g h he
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (F.allowed (idx g)) (hg g.val) (hg h.val)
      (hidx g) (by rw [he]; exact hidx h)
  have hz : (∑ g : {g : κ // ¬ P g},
      (A.segments.combine F.seg a (A.segments.unitVector (gate g.val))) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    rw [SegmentSystem.combine_unit]
    have hgn : ∀ i, gate g.val ∉ F.seg i := by simpa only [P, not_exists] using g.property
    simp only [hgn, ↓reduceIte, Finset.sum_const_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have he := Fintype.sum_subtype_add_sum_subtype P
    (fun g => (A.segments.combine F.seg a (A.segments.unitVector (gate g))) ^ 2)
  rw [hz, add_zero] at he
  rw [← he]
  calc
    _ = ∑ g : M, a (idx g) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [A.segments.combine_unit_of_mem F a (idx g) (hidx g)]
    _ = ∑ i ∈ Finset.univ.image idx, a i ^ 2 :=
      (Finset.sum_image (s := Finset.univ) (f := fun i : Fin F.n => a i ^ 2)
        (fun _ _ _ _ h => hinj h)).symm
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg _)

lemma tailAt_eq (F : A.segments.Family) (H : Finset ι)
    (i : Fin F.n) {g : ι} (hg : g ∈ F.seg i) :
    A.tailAt F H g = (F.seg i).filter (· ∉ H) := by
  classical
  have h : ∃ i, g ∈ F.seg i := ⟨i,hg⟩
  have he : h.choose = i := by
    by_contra hn
    exact Finset.disjoint_left.mp (F.disjoint hn) h.choose_spec hg
  simp only [tailAt, dite_eq_left h]
  rw [he]

lemma tailAt_mem {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hv : v ∈ A.tailAt F H g) : ∃ i, g ∈ F.seg i ∧ v ∈ F.seg i ∧ v ∉ H := by
  classical
  unfold tailAt at hv
  split_ifs at hv with h
  · exact ⟨h.choose, h.choose_spec, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  · simp at hv

lemma tailAt_allowed (F : A.segments.Family) {H : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (g : ι) (hne : (A.tailAt F H g).Nonempty) :
    A.segments.IsSegment (A.tailAt F H g) := by
  classical
  obtain ⟨v,hv⟩ := hne
  obtain ⟨i, hgi, _, _⟩ := A.tailAt_mem hv
  rw [A.tailAt_eq F H i hgi] at hv ⊢
  convert A.segment_filter_tail (F.allowed i) hH ?_ using 1
  · ext w
    simp only [Finset.mem_filter, Finset.mem_coe]
  · simpa only [Finset.filter_nonempty_iff, Finset.mem_coe] using
      (show ((F.seg i).filter (· ∉ H)).Nonempty from ⟨v,hv⟩)

lemma tailAt_cone {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hg : A.Gate (H : Set ι) g) (hv : v ∈ A.tailAt F H g) : g ≤ v := by
  obtain ⟨i,hgi,hvi,hvH⟩ := A.tailAt_mem hv
  rcases A.interval_chain (F.allowed i) g hgi v hvi with h | h
  · exact h
  · by_contra hn
    have hvne : v ≠ g := fun he => hn (he ▸ le_rfl)
    exact hvH (hg.2 v (lt_of_le_of_ne h hvne))

lemma mem_gateSet {H K : Finset ι} {g : ι} :
    g ∈ A.gateSet H K ↔ g ∈ K ∧ A.Gate (H : Set ι) g := Finset.mem_filter

lemma tailPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖u - A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, ← UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    rw [SegmentSystem.sub_filterPrimal, SegmentSystem.norm_eq_primal,
      SegmentSystem.norm_eq_primal, SegmentSystem.ofPrimal_filter]
    convert A.primal_filter_tail_le hH (A.segments.ofPrimal u) using 1
    congr 2

lemma tailDual_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (x : A.segments.Dual) : ‖A.segments.tailDual H x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [SegmentSystem.tailDual_apply_apply]
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (A.tailPrimal_norm_le hH u)
    (norm_nonneg _))

lemma replacement_error_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (F : A.segments.Family) (a b : Fin F.n → ℝ) :
    ‖A.segments.tailDual H (A.segments.combine F.seg a - A.segments.combine F.seg b)‖ ^ 2 ≤
      ∑ i, (a i - b i) ^ 2 := by
  have hV : 0 ≤ ∑ i,(a i-b i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := A.tailDual_norm_le hH (A.segments.combine F.seg a - A.segments.combine F.seg b)
  rw [← SegmentSystem.combine_sub] at hc
  have ha := A.segments.norm_combine_le F.seg (a-b) (fun i _ => F.allowed i) F.disjoint
  have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 (hc.trans ha)
  simpa only [Pi.sub_apply, Real.sq_sqrt hV, SegmentSystem.combine_sub] using h

lemma replacement_error_gate {H : Finset ι} (F : A.segments.Family)
    (a : Fin F.n → ℝ) (q : ι →₀ ℝ) {g : ι} (hg : g ∉ H) :
    A.segments.tailDual H (A.segments.combine F.seg a -
      A.segments.combine F.seg (fun i => ∑ v ∈ F.seg i,q v)) (A.segments.unitVector g) =
      A.segments.combine F.seg a (A.segments.unitVector g) - A.boundaryCoeff F q g := by
  rw [SegmentSystem.tailDual_apply, sub_apply, SegmentSystem.headDual_unit, ite_eq_right hg,
    sub_zero, sub_apply]
  simp only [SegmentSystem.combine_unit, boundaryCoeff]

lemma replacement_cross (F : A.segments.Family) (a : Fin F.n → ℝ) (p : ι →₀ ℝ) (r : ℝ) :
    (∑ i, a i * (∑ v ∈ F.seg i,(r • p) v)) =
      r * A.segments.combine F.seg a (A.segments.finiteEmbedding p) := by
  rw [SegmentSystem.finiteEmbedding_apply, SegmentSystem.combine_coe]
  change (∑ i,a i*(∑ v ∈ F.seg i,(r • p) v)) = r*(∑ i,a i*(∑ v ∈ F.seg i,p v))
  simp_rw [Finsupp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma replacement_mass_norm {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {H K : Finset ι} (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι))
    (F : Ω → A.segments.Family) (hFK : ∀ ω i, (F ω).seg i ⊆ K)
    (q : ι →₀ ℝ) (hq : ∀ v,v ∉ H → q v=0)
    (w σ : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hσ : ∀ ω,|σ ω|=1) :
    ‖∑ ω,w ω • (σ ω • A.segments.tailDual H
      (A.segments.combine (F ω).seg (fun i => ∑ v ∈ (F ω).seg i,q v)))‖ ≤
      Real.sqrt (∑ g : A.gateSet H K, (∑ ω,w ω * |A.boundaryCoeff (F ω) q g.val|)^2) := by
  classical
  let gate : A.gateSet H K ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have hg (g : A.gateSet H K) : A.Gate (H : Set ι) (gate g) :=
    (A.mem_gateSet.mp g.property).2
  have h := A.segments.norm_cone_mean_le
    (fun ω (g : A.gateSet H K) => A.tailAt (F ω) H g.val)
    (fun ω g => σ ω * A.boundaryCoeff (F ω) q g.val) w hw
    (fun ω g => A.tailAt_allowed (F ω) hH g.val) (by
      intro g h hgh ω ν
      apply Finset.disjoint_left.mpr
      intro v hvg hvh
      exact hgh (gate.injective (A.gates_eq_of_common_upper (hg g) (hg h)
        (A.tailAt_cone (hg g) hvg) (A.tailAt_cone (hg h) hvh))))
  simp only [abs_mul, hσ, one_mul] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [A.replaced_tail_eq hH hK (F ω) (hFK ω) q hq, SegmentSystem.combine_smul]

/-- The finite pooled coefficient/slack bound, before taking the supremum over
    head tests. No lens or convexity modulus is postulated for the space. -/
lemma pooled_tail_test {Ω : Type*} [Fintype Ω] {H K : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι))
    {R : ℝ} {x y : A.segments.Dual} (law : A.segments.BipolarLaw Ω R x y)
    (hFK : ∀ ω i,(law.atom ω).family.seg i ⊆ K)
    (hx : ∀ v,v ∉ H → x (A.segments.unitVector v)=0)
    (p : ι →₀ ℝ) (hp : ∀ v,v ∉ H → p v=0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H y‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  classical
  have : Nonempty Ω := by
    by_contra hn
    have : IsEmpty Ω := not_nonempty_iff.mp hn
    have h := law.sum_one
    simp at h
  let r : ℝ := x (A.segments.finiteEmbedding p)
  let q : ι →₀ ℝ := r • p
  let F : Ω → A.segments.Family := fun ω => (law.atom ω).family
  let a : (ω : Ω) → Fin (F ω).n → ℝ := fun ω => (law.atom ω).coeff
  let β : (ω : Ω) → Fin (F ω).n → ℝ := fun ω i => ∑ v ∈ (F ω).seg i,q v
  let Ac : Ω → A.segments.Dual := fun ω => A.segments.combine (F ω).seg (β ω)
  let W : Ω → A.segments.Dual := fun ω =>
    A.segments.tailDual H ((law.atom ω).value - Ac ω)
  let V : Ω → ℝ := fun ω => ∑ i,(a ω i-β ω i)^2
  let L : Ω → ℝ := fun ω => r^2-∑ i,β ω i^2
  let η : ℝ := ∑ ω,law.weight ω*V ω
  let θ : ℝ := ∑ ω,law.weight ω*L ω
  have hq (v : ι) (hv : v ∉ H) : q v = 0 := by simp only [q,Finsupp.smul_apply,hp v hv,smul_zero]
  have hqn : A.segments.primalSeminorm q ≤ |r| := by
    dsimp [q]
    rw [map_smul_eq_mul, Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpn (abs_nonneg r)
  have hqn2 : (A.segments.primalSeminorm q)^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (apply_nonneg _ _) (abs_nonneg r)).2 hqn
  have hV (ω : Ω) : 0 ≤ V ω := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hL (ω : Ω) : 0 ≤ L ω := by
    apply sub_nonneg.mpr
    exact (A.segments.test_energy_le_allow_empty (F ω).seg
      (fun i _ => (F ω).allowed i) (F ω).disjoint q).trans hqn2
  have hη : 0 ≤ η := Finset.sum_nonneg (fun ω _ => mul_nonneg (law.nonneg ω) (hV ω))
  have hθ : 0 ≤ θ := Finset.sum_nonneg (fun ω _ => mul_nonneg (law.nonneg ω) (hL ω))
  have hcross : (∑ ω,law.weight ω*(∑ i,a ω i*β ω i)) = r^2 := by
    have hm := congrArg (fun z : A.segments.Dual => z (A.segments.finiteEmbedding p)) law.mean
    simp only [sum_apply, smul_apply, smul_eq_mul] at hm
    calc
      _ = r*(∑ ω,law.weight ω*(law.atom ω).value (A.segments.finiteEmbedding p)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        have hr := A.replacement_cross (F ω) (a ω) p r
        change (∑ i,a ω i*β ω i) = r*(law.atom ω).value (A.segments.finiteEmbedding p) at hr
        rw [hr]
        ring
      _ = r^2 := by rw [hm]; dsimp [r]; ring
  have hbudget : η+θ ≤ R^2-r^2 :=
    FiniteAverage.joint_budget law.weight law.nonneg law.sum_one (fun ω => Fin (F ω).n)
      a β (fun ω => (law.atom ω).energy_le) hcross
  have hWnorm (ω : Ω) : ‖W ω‖^2 ≤ V ω :=
    A.replacement_error_le hH (F ω) (a ω) (β ω)
  let gate : A.gateSet H K ↪ ι := ⟨Subtype.val,Subtype.val_injective⟩
  have hg (g : A.gateSet H K) : A.Gate (H : Set ι) (gate g) :=
    (A.mem_gateSet.mp g.property).2
  let b : Ω → A.gateSet H K → ℝ := fun ω g => A.boundaryCoeff (F ω) q g.val
  let e : Ω → A.gateSet H K → ℝ := fun ω g => W ω (A.segments.unitVector g.val)
  have he (ω : Ω) (g : A.gateSet H K) :
      e ω g = (law.atom ω).value (A.segments.unitVector g.val) - b ω g :=
    A.replacement_error_gate (F ω) (a ω) q (hg g).1
  have hgateEnergy (ω : Ω) : (∑ g,e ω g^2) ≤ V ω := by
    have heq (g : A.gateSet H K) : e ω g =
        A.segments.combine (F ω).seg (a ω-β ω) (A.segments.unitVector g.val) := by
      rw [SegmentSystem.combine_sub]
      rw [sub_apply]
      simpa only [SegmentSystem.Atom.value, SegmentSystem.combine_unit, b, β,
        boundaryCoeff, F, a] using he ω g
    simp_rw [heq]
    exact A.gate_coefficient_energy (F ω) (a ω-β ω) gate hg
  have hmean (g : A.gateSet H K) :
      (∑ ω,law.weight ω*b ω g) = -(∑ ω,law.weight ω*e ω g) := by
    have hm := congrArg (fun z : A.segments.Dual => z (A.segments.unitVector g.val)) law.mean
    simp only [sum_apply,smul_apply,smul_eq_mul,hx g.val (hg g).1] at hm
    have heq : (∑ ω,law.weight ω*b ω g)+(∑ ω,law.weight ω*e ω g) =
        ∑ ω,law.weight ω*(law.atom ω).value (A.segments.unitVector g.val) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      rw [he]
      ring
    rw [hm] at heq
    linarith
  have hopp (ω ν : Ω) : (∑ g,(|b ω g| * |b ν g|-b ω g*b ν g)) ≤ L ω+L ν := by
    have h := A.opposite_crossing_le hH q hq (F ω) (F ν) gate hg
    change (∑ g,(|b ω g| * |b ν g|-b ω g*b ν g)) ≤
      ((A.segments.primalSeminorm q)^2 - ∑ i,β ω i^2) +
      ((A.segments.primalSeminorm q)^2 - ∑ i,β ν i^2) at h
    exact h.trans (add_le_add (sub_le_sub_right hqn2 _) (sub_le_sub_right hqn2 _))
  have hmass : (∑ g,(∑ ω,law.weight ω* |b ω g|)^2) ≤ η+2*θ :=
    FiniteAverage.pooled_mass law.weight law.nonneg law.sum_one b e V L hmean hgateEnergy hopp
  have herr : ‖∑ ω,law.weight ω • (law.sign ω • W ω)‖ ≤ Real.sqrt η := by
    apply FiniteAverage.norm_mean_le_sqrt law.weight law.nonneg law.sum_one _ hη
    apply Finset.sum_le_sum
    intro ω _
    rw [norm_smul,Real.norm_eq_abs,law.abs_sign,one_mul]
    exact mul_le_mul_of_nonneg_left (hWnorm ω) (law.nonneg ω)
  have hrec : ‖∑ ω,law.weight ω • (law.sign ω • A.segments.tailDual H (Ac ω))‖ ≤
      Real.sqrt (η+2*θ) := by
    exact (A.replacement_mass_norm hH hK F hFK q hq law.weight law.sign law.nonneg law.abs_sign).trans
      (Real.sqrt_le_sqrt hmass)
  have hdec : A.segments.tailDual H y =
      (∑ ω,law.weight ω • (law.sign ω • W ω)) +
      (∑ ω,law.weight ω • (law.sign ω • A.segments.tailDual H (Ac ω))) := by
    conv_lhs => rw [← law.signed_mean]
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [map_smul, W, map_sub, smul_sub]
    module
  calc
    ‖A.segments.tailDual H y‖ ≤ Real.sqrt η+Real.sqrt (η+2*θ) := by
      rw [hdec]
      exact (norm_add_le _ _).trans (add_le_add herr hrec)
    _ ≤ 2*Real.sqrt (η+θ) := FiniteAverage.sqrt_pooled hη hθ
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbudget) (by norm_num)

end Ancestry

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.pooled_tail_test := @_root_.OAI.DiamondDistortion.Ancestry.pooled_tail_test
