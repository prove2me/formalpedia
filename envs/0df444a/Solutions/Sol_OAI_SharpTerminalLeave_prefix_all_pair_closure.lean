-- Prove2me | solution 1 for OAI.SharpTerminalLeave.prefix_all_pair_closure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:58:07.737908+00:00
-- url     : https://prove2.me/submissions/1f7b5cf5-a475-42d5-8ca4-036f5b629ebb

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000
import Theorems.Thm_OAI_SharpTerminalLeave_prefix_present_edge_closure

section
-- module Solutions.OAIQ4_Tr.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_LogStepSandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave

lemma log_step_sandwich {p q h : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : p = q+h) :
    h/p ≤ Real.log p-Real.log q ∧ Real.log p-Real.log q ≤ h/q := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have hu := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at hl
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)] at hu
  have he₁ : q/p-1 = -(h/p) := by field_simp; linarith only [hs]
  have he₂ : p/q-1 = h/q := by field_simp; linarith only [hs]
  rw [he₁] at hl
  rw [he₂] at hu
  exact ⟨by linarith only [hl],hu⟩

theorem density_log_sum_bounds (p : ℕ → ℝ) (h : ℝ) (T : ℕ)
    (hp : ∀ i ≤ T, 0 < p i) (hs : ∀ i < T, p i = p (i+1)+h) :
    (∑ i ∈ Finset.range T, h/p i) ≤ Real.log (p 0)-Real.log (p T) ∧
    Real.log (p 0)-Real.log (p T) ≤
      (∑ i ∈ Finset.range T, h/p i)+(h/p T-h/p 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
    obtain ⟨hl,hu⟩ := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    obtain ⟨sl,su⟩ := log_step_sandwich (hp T (by omega)) (hp (T+1) le_rfl) (hs T (by omega))
    rw [Finset.sum_range_succ]
    constructor <;> linarith only [hl,hu,sl,su]

lemma inverse_square_grid_step {a p q h : ℝ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hh : 0 ≤ h) (hs : p = q+h) :
    2*h/(a*p^3) ≤ 1/(a*q^2)-1/(a*p^2) := by
  have hpq : q ≤ p := by linarith only [hs,hh]
  have hc : 2*q^2 ≤ p*(p+q) := by nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (by linarith : 0 ≤ p+2*q)]
  have hm := mul_le_mul_of_nonneg_left hc hh
  have he : p^2-q^2 = h*(p+q) := by rw [hs]; ring
  apply (div_le_iff₀ (mul_pos ha (pow_pos hp 3))).mpr
  have hd : (1/(a*q^2)-1/(a*p^2))*(a*p^3) = (p^2-q^2)*p/q^2 := by
    field_simp
  rw [hd,he]
  apply (le_div_iff₀ (pow_pos hq 2)).mpr
  nlinarith only [hm]

theorem inverse_square_grid_sum (p : ℕ → ℝ) (a h : ℝ) (T : ℕ)
    (ha : 0 < a) (hh : 0 ≤ h) (hp : ∀ i ≤ T, 0 < p i)
    (hs : ∀ i < T, p i = p (i+1)+h) :
    (∑ i ∈ Finset.range T, 2*h/(a*p i^3)) ≤ 1/(a*p T^2)-1/(a*p 0^2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hi := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    have hstep := inverse_square_grid_step ha (hp T (by omega)) (hp (T+1) le_rfl) hh (hs T (by omega))
    rw [Finset.sum_range_succ]
    linarith only [hi,hstep]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_FiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmf_weight_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

@[simp] theorem pmfMean_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  simp only [pmfMean, ← Finset.sum_mul, pmf_weight_sum, one_mul]

theorem pmfMean_congr {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => f a * c) = pmfMean p f * c := by
  simp only [pmfMean, ← mul_assoc, ← Finset.sum_mul]

theorem pmfMean_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  simp only [pmfMean, PMF.bind_apply, tsum_fintype]
  have hfin (b : β) (a : α) : p a * q a b ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hfin _ a), Finset.sum_mul,
    ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem pmfMean_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfMean (p.map g) f = pmfMean p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfMean_bind]
  simp

theorem pmfMean_uniformOfFinset {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfMean (PMF.uniformOfFinset s hs) f = (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [pmfMean, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  simp only [div_eq_mul_inv, mul_comm, Finset.sum_mul]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TerminalLaw
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem triangle_edge_card {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) : (t.powersetCard 2).card = 3 := by
  rw [Finset.card_powersetCard, (mem_triangles.mp ht).1]
  decide

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_TriangleDrift
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : β → α → ℝ) :
    pmfMean p (fun a => ∑ b, f b a) = ∑ b, pmfMean p (f b) := by
  simp only [pmfMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem step_mean {n : ℕ} (G : Graph n) (f : Graph n → ℝ)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) f =
      (∑ t ∈ triangles G, f (G \ t.powersetCard 2)) / ((triangles G).card : ℝ) := by
  rw [step, dite_eq_left hG, pmfMean_map, pmfMean_uniformOfFinset]

theorem intact_delete {n : ℕ} {G F : Graph n} (hF : F ⊆ G)
    (t : Finset (Fin n)) :
    intact F (G \ t.powersetCard 2) =
      1 - if ¬ Disjoint F (t.powersetCard 2) then 1 else 0 := by
  classical
  simp only [intact, Finset.subset_sdiff, hF, true_and]
  split_ifs <;> simp_all

theorem step_mean_intact {n : ℕ} {G F : Graph n} (hF : F ⊆ G)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) (intact F) =
      1 - ((hittingTriangles G F).card : ℝ) / ((triangles G).card : ℝ) := by
  classical
  rw [step_mean G (intact F) hG]
  simp_rw [intact_delete hF]
  rw [Finset.sum_sub_distrib]
  have hb : (∑ t ∈ triangles G, if ¬ Disjoint F (t.powersetCard 2) then (1 : ℝ) else 0) =
      ((hittingTriangles G F).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [hittingTriangles]
  rw [hb]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [sub_div, div_self (by exact_mod_cast hG.card_pos.ne')]

theorem step_mean_intact_of_not_subset {n : ℕ} {G F : Graph n}
    (hF : ¬ F ⊆ G) : pmfMean (step G) (intact F) = 0 := by
  rw [← pmfMean_const (step G) 0]
  apply pmfMean_congr
  intro H hH
  have hFH : ¬ F ⊆ H := fun h => hF (h.trans (step_support_subset hH))
  simp [intact, hFH]

theorem step_mean_copyCount {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (hG : (triangles G).Nonempty) :
    pmfMean (step G) (copyCount required) = copyCount required G -
      (∑ a, if required a ⊆ G then ((hittingTriangles G (required a)).card : ℝ) else 0) /
        ((triangles G).card : ℝ) := by
  classical
  unfold copyCount
  rw [pmfMean_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : required a ⊆ G
  · rw [step_mean_intact ha hG, ite_eq_left ha, intact, ite_eq_left ha]
  · rw [step_mean_intact_of_not_subset ha, ite_eq_right ha, intact, ite_eq_right ha]
    simp

theorem three_le_card_union {α : Type*} [DecidableEq α]
    {e f : Finset α} (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f) :
    3 ≤ (e ∪ f).card := by
  have hi : (e ∩ f).card < 2 := by
    by_contra h
    have hge : 2 ≤ (e ∩ f).card := by omega
    have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hfq : e ∩ f = f := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    exact hef (heq.symm.trans hfq)
  have h := Finset.card_union_add_card_inter e f
  omega

theorem triangle_eq_of_two_edges {α : Type*} [DecidableEq α]
    {t u e f : Finset α} (ht : t.card = 3) (hu : u.card = 3)
    (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f)
    (het : e ⊆ t) (hft : f ⊆ t) (heu : e ⊆ u) (hfu : f ⊆ u) : t = u := by
  have hm := three_le_card_union he hf hef
  have ht' : e ∪ f = t := Finset.eq_of_subset_of_card_le
    (Finset.union_subset het hft) (by omega)
  have hu' : e ∪ f = u := Finset.eq_of_subset_of_card_le
    (Finset.union_subset heu hfu) (by omega)
  exact ht'.symm.trans hu'

theorem hittingTriangles_eq_biUnion {n : ℕ} (G F : Graph n) :
    hittingTriangles G F = F.biUnion (incidentTriangles G) := by
  classical
  ext t
  simp only [hittingTriangles, Finset.mem_filter, Finset.mem_biUnion,
    incidentTriangles, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨ht, e, heF, het⟩
    exact ⟨e, heF, ht, het⟩
  · rintro ⟨e, heF, ht, het⟩
    exact ⟨ht, e, heF, het⟩

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleDegreeMean
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma triangles_delete_eq_sdiff_hitting {n : ℕ} (G : Graph n) (t : Finset (Fin n)) :
    triangles (G \ t.powersetCard 2) = triangles G \ hittingTriangles G (t.powersetCard 2) := by
  ext u
  simp only [mem_triangles, hittingTriangles, Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hu,hs⟩
    refine ⟨⟨hu, fun e he => (Finset.mem_sdiff.mp (hs he)).1⟩, ?_⟩
    rintro ⟨_,hd⟩
    apply hd
    apply Finset.disjoint_left.mpr
    intro e het heu
    exact (Finset.mem_sdiff.mp (hs heu)).2 het
  · rintro ⟨⟨hu,hs⟩,hn⟩
    refine ⟨hu, ?_⟩
    intro e he
    refine Finset.mem_sdiff.mpr ⟨hs he, ?_⟩
    intro het
    apply hn
    refine ⟨⟨hu,hs⟩, ?_⟩
    exact fun hd => Finset.disjoint_left.mp hd het he

lemma triangle_edge_inter_card_le_one {n : ℕ} {G : Graph n}
    {t u : Finset (Fin n)} (ht : t ∈ triangles G) (hu : u ∈ triangles G)
    (hne : t ≠ u) : (t.powersetCard 2 ∩ u.powersetCard 2).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hef
  apply hne
  have he' := Finset.mem_inter.mp he
  have hf' := Finset.mem_inter.mp hf
  exact triangle_eq_of_two_edges (mem_triangles.mp ht).1 (mem_triangles.mp hu).1
    (Finset.mem_powersetCard.mp he'.1).2 (Finset.mem_powersetCard.mp hf'.1).2 hef
    (Finset.mem_powersetCard.mp he'.1).1 (Finset.mem_powersetCard.mp hf'.1).1
    (Finset.mem_powersetCard.mp he'.2).1 (Finset.mem_powersetCard.mp hf'.2).1

lemma triangle_incidence_swap {n : ℕ} (G : Graph n) (f : Finset (Fin n) → ℝ) :
    (∑ t ∈ triangles G, ∑ e ∈ t.powersetCard 2, f e) =
      ∑ e ∈ G, (triangleDegree G e : ℝ) * f e := by
  classical
  calc
    _ = ∑ t ∈ triangles G, ∑ e ∈ G, if e ∈ t.powersetCard 2 then f e else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun he => ⟨(mem_triangles.mp ht).2 he,he⟩, fun he => he.2⟩
    _ = ∑ e ∈ G, ∑ t ∈ triangles G, if e ∈ t.powersetCard 2 then f e else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      simp [triangleDegree, incidentTriangles, mul_comm]

lemma triangle_degree_sum {n : ℕ} (G : Graph n) :
    (∑ e ∈ G, (triangleDegree G e : ℝ)) = 3 * (triangles G).card := by
  have h := triangle_incidence_swap G (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  calc
    _ = ∑ t ∈ triangles G, ((t.powersetCard 2).card : ℝ) := h.symm
    _ = ∑ _t ∈ triangles G, (3 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [triangle_edge_card ht]
      norm_num
    _ = _ := by simp; ring

lemma triangle_incidence_sum_on {n : ℕ} (G F : Graph n) :
    (∑ e ∈ F, (triangleDegree G e : ℝ)) =
      ∑ t ∈ triangles G, ((F ∩ t.powersetCard 2).card : ℝ) := by
  classical
  have he (e : Finset (Fin n)) : (triangleDegree G e : ℝ) =
      ∑ t ∈ triangles G, if e ∈ t.powersetCard 2 then (1 : ℝ) else 0 := by
    simp [triangleDegree, incidentTriangles, Finset.sum_boole]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.sum_boole]
  congr 1

lemma triangle_hit_multiplicity {n : ℕ} {G : Graph n} {t u : Finset (Fin n)}
    (ht : t ∈ triangles G) (hu : u ∈ triangles G) :
    ((t.powersetCard 2 ∩ u.powersetCard 2).card : ℝ) =
      (if u ∈ hittingTriangles G (t.powersetCard 2) then 1 else 0) +
      (if u = t then 2 else 0) := by
  classical
  by_cases hut : u = t
  · subst u
    have hhit : t ∈ hittingTriangles G (t.powersetCard 2) := by
      apply Finset.mem_filter.mpr
      refine ⟨ht, ?_⟩
      intro hd
      have hzero : t.powersetCard 2 = ∅ := disjoint_self.mp hd
      have hc := triangle_edge_card ht
      rw [hzero,Finset.card_empty] at hc
      omega
    norm_num [hhit, triangle_edge_card ht]
  · by_cases hhit : u ∈ hittingTriangles G (t.powersetCard 2)
    · have hnon : (t.powersetCard 2 ∩ u.powersetCard 2).Nonempty := by
        exact Finset.not_disjoint_iff_nonempty_inter.mp (Finset.mem_filter.mp hhit).2
      have hcard : (t.powersetCard 2 ∩ u.powersetCard 2).card = 1 := by
        exact Nat.le_antisymm (triangle_edge_inter_card_le_one ht hu (Ne.symm hut))
          (Finset.one_le_card.mpr hnon)
      simp [hhit,hut,hcard]
    · have hd : Disjoint (t.powersetCard 2) (u.powersetCard 2) := by
        by_contra hn
        exact hhit (Finset.mem_filter.mpr ⟨hu,hn⟩)
      simp [hhit,hut,Finset.disjoint_iff_inter_eq_empty.mp hd]

theorem triangle_hitting_card_exact {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) :
    ((hittingTriangles G (t.powersetCard 2)).card : ℝ) =
      (∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) - 2 := by
  classical
  rw [triangle_incidence_sum_on]
  have hm : (∑ u ∈ triangles G, ((t.powersetCard 2 ∩ u.powersetCard 2).card : ℝ)) =
      ((hittingTriangles G (t.powersetCard 2)).card : ℝ) + 2 := by
    calc
      _ = ∑ u ∈ triangles G,
          ((if u ∈ hittingTriangles G (t.powersetCard 2) then (1 : ℝ) else 0) +
          (if u = t then 2 else 0)) := by
        apply Finset.sum_congr rfl
        exact fun u hu => triangle_hit_multiplicity ht hu
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_boole,Finset.sum_ite_eq',ht,ite_true]
        have hf : (triangles G).filter (fun u => u ∈ hittingTriangles G (t.powersetCard 2)) =
            hittingTriangles G (t.powersetCard 2) := by
          ext u
          simp only [hittingTriangles,Finset.mem_filter]
          tauto
        rw [hf]
  linarith

theorem triangle_count_delete {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) :
    ((triangles (G \ t.powersetCard 2)).card : ℝ) =
      (triangles G).card - (∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) + 2 := by
  have hsub : hittingTriangles G (t.powersetCard 2) ⊆ triangles G := Finset.filter_subset _ _
  rw [triangles_delete_eq_sdiff_hitting,Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub), triangle_hitting_card_exact ht]
  ring

theorem step_mean_triangle_count {n : ℕ} {G : Graph n}
    (hQ : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => ((triangles H).card : ℝ)) =
      (triangles G).card - (∑ e ∈ G, (triangleDegree G e : ℝ)^2) /
        (triangles G).card + 2 := by
  classical
  rw [step_mean G _ hQ]
  have he : (∑ t ∈ triangles G, ((triangles (G \ t.powersetCard 2)).card : ℝ)) =
      (triangles G).card * ((triangles G).card + 2 : ℝ) -
      ∑ e ∈ G, (triangleDegree G e : ℝ)^2 := by
    calc
      _ = ∑ t ∈ triangles G, (((triangles G).card : ℝ) + 2 -
          ∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [triangle_count_delete ht]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib,triangle_incidence_swap]
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, pow_two]
        ring
  rw [he]
  have hq : ((triangles G).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ.card_pos
  field_simp
  ring

lemma triangleDegreeVariance_nonneg {n : ℕ} (G : Graph n) :
    0 ≤ triangleDegreeVariance G := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma triangleDegreeMean_mass {n : ℕ} {G : Graph n} (hG : G.Nonempty) :
    (G.card : ℝ) * triangleDegreeMean G = 3 * (triangles G).card := by
  have hm : (G.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hG.card_pos
  unfold triangleDegreeMean
  field_simp

theorem triangle_degree_second_moment {n : ℕ} {G : Graph n} (hG : G.Nonempty) :
    (∑ e ∈ G, (triangleDegree G e : ℝ)^2) =
      triangleDegreeVariance G + (G.card : ℝ)*(triangleDegreeMean G)^2 := by
  have hlin := triangle_degree_sum G
  have hm := triangleDegreeMean_mass hG
  have hv : triangleDegreeVariance G =
      (∑ e ∈ G, (triangleDegree G e : ℝ)^2) -
      2*triangleDegreeMean G*(∑ e ∈ G, (triangleDegree G e : ℝ)) +
      (G.card : ℝ)*(triangleDegreeMean G)^2 := by
    unfold triangleDegreeVariance
    calc
      _ = ∑ e ∈ G, ((triangleDegree G e : ℝ)^2 -
          2*triangleDegreeMean G*(triangleDegree G e : ℝ) + (triangleDegreeMean G)^2) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
        Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
  rw [hlin, ← hm] at hv
  nlinarith only [hv]

lemma graph_nonempty_of_triangles {n : ℕ} {G : Graph n} (hQ : (triangles G).Nonempty) :
    G.Nonempty := by
  obtain ⟨t,ht⟩ := hQ
  have hc := triangle_edge_card ht
  have he : (t.powersetCard 2).Nonempty := Finset.card_pos.mp (by omega)
  exact he.mono (mem_triangles.mp ht).2

theorem step_mean_triangle_count_centered {n : ℕ} {G : Graph n}
    (hQ : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => ((triangles H).card : ℝ)) =
      (triangles G).card - 9*(triangles G).card / G.card -
      triangleDegreeVariance G / (triangles G).card + 2 := by
  rw [step_mean_triangle_count hQ, triangle_degree_second_moment (graph_nonempty_of_triangles hQ)]
  have hq : ((triangles G).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ.card_pos
  have hm : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (graph_nonempty_of_triangles hQ).card_pos
  unfold triangleDegreeMean
  field_simp
  ring

lemma triangle_degree_variance_shift {n : ℕ} {G : Graph n} (hG : G.Nonempty) (d : ℝ) :
    (∑ e ∈ G, ((triangleDegree G e : ℝ)-d)^2) =
      triangleDegreeVariance G + (G.card : ℝ)*(triangleDegreeMean G-d)^2 := by
  have hlin := triangle_degree_sum G
  have hm := triangleDegreeMean_mass hG
  have hsec := triangle_degree_second_moment hG
  calc
    _ = (∑ e ∈ G, (triangleDegree G e : ℝ)^2) -
        2*d*(∑ e ∈ G, (triangleDegree G e : ℝ))+(G.card : ℝ)*d^2 := by
      calc
        _ = ∑ e ∈ G, ((triangleDegree G e : ℝ)^2 - 2*d*(triangleDegree G e : ℝ) + d^2) := by
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
          Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
    _ = _ := by rw [hsec,hlin,← hm]; ring

lemma triangle_degree_variance_le {n : ℕ} {G : Graph n} (hG : G.Nonempty)
    (d δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ e ∈ G, |(triangleDegree G e : ℝ)-d| ≤ δ) :
    triangleDegreeVariance G ≤ (G.card : ℝ)*δ^2 := by
  have hv : triangleDegreeVariance G ≤ ∑ e ∈ G, ((triangleDegree G e : ℝ)-d)^2 := by
    rw [triangle_degree_variance_shift hG d]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  apply hv.trans
  calc
    _ ≤ ∑ _e ∈ G, δ^2 := by
      apply Finset.sum_le_sum
      intro e he
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ).mpr (h e he)
    _ = _ := by simp

end SharpTerminalLeave
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_DensityEdgeSafe
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

lemma triangle_count_from_edge_degrees {n : ℕ} (G : Graph n) (D δ : ℝ)
    (hd : ∀ e ∈ G, |(triangleDegree G e : ℝ)-D| ≤ δ) :
    |3*(triangles G).card-(G.card : ℝ)*D| ≤ (G.card : ℝ)*δ := by
  have he : 3*(triangles G).card-(G.card : ℝ)*D =
      ∑ e ∈ G, ((triangleDegree G e : ℝ)-D) := by
    rw [Finset.sum_sub_distrib,triangle_degree_sum]
    simp
  rw [he]
  calc
    _ ≤ ∑ e ∈ G, |(triangleDegree G e : ℝ)-D| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ G, δ := Finset.sum_le_sum (fun e he => hd e he)
    _ = _ := by simp

lemma densityEdgeSafe_triangle_bounds {n : ℕ} {p η : ℝ} {G : Graph n}
    (h : densityEdgeSafe n p η G) :
    (n : ℝ)^3*p^3/6*(1-η) ≤ (triangles G).card ∧
      (triangles G).card ≤ (n : ℝ)^3*p^3/6*(1+η) := by
  have hc := triangle_count_from_edge_degrees G (n*p^2) (η*(n*p^2)) h.2.2
  rw [h.2.1] at hc
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  constructor <;> nlinarith only [hl,hu]

lemma densityEdgeSafe_triangle_positive {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : η ≤ 1/2) (h : densityEdgeSafe n p η G) :
    (triangles G).Nonempty := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := (densityEdgeSafe_triangle_bounds h).1
  have hfac : 0 < 1-η := by linarith
  have hpos : (0 : ℝ) < (triangles G).card :=
    lt_of_lt_of_le (by positivity) hq
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighbors
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem commonNeighbors_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (hw : w ∈ commonNeighbors G u v) : u ≠ w ∧ v ≠ w := by
  obtain ⟨hu,hv⟩ := (mem_commonNeighbors G u v w).mp hw
  constructor
  · intro h
    have hc := mem_completeGraph.mp (hG hu)
    simp [h] at hc
  · intro h
    have hc := mem_completeGraph.mp (hG hv)
    simp [h] at hc

theorem currentCodegree_copyCount {n : ℕ} (G : Graph n) (u v : Fin n) :
    (currentCodegree G u v : ℝ) = copyCount (wedgeEdges u v) G := by
  simp only [copyCount, intact, wedgeEdges_subset]
  rw [← Finset.sum_filter]
  simp [currentCodegree, commonNeighbors]

theorem step_mean_codegree_hazard {n : ℕ} (G : Graph n) (u v : Fin n)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)) =
      (currentCodegree G u v : ℝ) -
      (∑ w ∈ commonNeighbors G u v,
        ((hittingTriangles G (wedgeEdges u v w)).card : ℝ)) / (triangles G).card := by
  simp_rw [currentCodegree_copyCount]
  rw [step_mean_copyCount _ G hG]
  congr 2
  simp only [wedgeEdges_subset]
  rw [← Finset.sum_filter]
  simp [commonNeighbors]

theorem hittingTriangles_wedge {n : ℕ} (G : Graph n) (u v w : Fin n) :
    hittingTriangles G (wedgeEdges u v w) =
      incidentTriangles G {u,w} ∪ incidentTriangles G {v,w} := by
  rw [hittingTriangles_eq_biUnion]
  simp [wedgeEdges]

theorem wedge_incident_inter {n : ℕ} (G : Graph n) {u v w : Fin n}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    incidentTriangles G {u,w} ∩ incidentTriangles G {v,w} =
      if {u,v,w} ∈ triangles G then {{u,v,w}} else ∅ := by
  ext t
  simp only [Finset.mem_inter, incidentTriangles, Finset.mem_filter]
  have hpairu : ({u,w} : Finset (Fin n)).card = 2 := Finset.card_pair huw
  have hpairv : ({v,w} : Finset (Fin n)).card = 2 := Finset.card_pair hvw
  have htriple : ({u,v,w} : Finset (Fin n)).card = 3 := by simp [huv,huw,hvw]
  have hpt : ({u,w} : Finset (Fin n)) ⊆ {u,v,w} := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  have hqt : ({v,w} : Finset (Fin n)) ⊆ {u,v,w} := by
    simp
  have hpq : ({u,w} : Finset (Fin n)) ≠ {v,w} := by
    intro he
    have hh : u ∈ ({v,w} : Finset (Fin n)) := he ▸ (by simp)
    simp [huv,huw] at hh
  constructor
  · rintro ⟨⟨ht,he⟩,_,hf⟩
    have heq := triangle_eq_of_two_edges (mem_triangles.mp ht).1 htriple
      hpairu hpairv hpq (Finset.mem_powersetCard.mp he).1
      (Finset.mem_powersetCard.mp hf).1 hpt hqt
    subst t
    simp [ht]
  · intro hh
    split_ifs at hh with ht
    · have heq : t = {u,v,w} := Finset.mem_singleton.mp hh
      subst t
      exact ⟨⟨ht,Finset.mem_powersetCard.mpr ⟨hpt,hpairu⟩⟩,
        ht,Finset.mem_powersetCard.mpr ⟨hqt,hpairv⟩⟩
    · exact False.elim (Finset.notMem_empty t hh)

theorem wedge_hazard_exact {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    ((hittingTriangles G (wedgeEdges u v w)).card : ℝ) =
      (triangleDegree G {u,w} : ℝ) + (triangleDegree G {v,w} : ℝ) -
        if {u,v,w} ∈ triangles G then 1 else 0 := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  have hh := Finset.card_union_add_card_inter
    (incidentTriangles G {u,w}) (incidentTriangles G {v,w})
  rw [wedge_incident_inter G huv huw hvw] at hh
  rw [hittingTriangles_wedge]
  unfold triangleDegree
  split_ifs at hh ⊢ with ht <;> simp only [Finset.card_singleton, Finset.card_empty] at hh
  all_goals
    have hh' : ((incidentTriangles G {u,w} ∪ incidentTriangles G {v,w}).card : ℝ) +
        (if {u,v,w} ∈ triangles G then 1 else 0) =
        (incidentTriangles G {u,w}).card + (incidentTriangles G {v,w}).card := by
      simp only [ht, ↓reduceIte]
      exact_mod_cast hh
    simp only [ht, ↓reduceIte] at hh'
    linarith

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem prefixDensity_bounds (n : ℕ) (hn : 0 < n)
    (ht : 0 ≤ prefixTargetTime n) :
    prefixTargetDensity n ≤ prefixDensity n ∧
      prefixDensity n < prefixTargetDensity n + 6 / (n : ℝ)^2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  have hf : (prefixTime n : ℝ) ≤ prefixTargetTime n := Nat.floor_le ht
  have hg : prefixTargetTime n < (prefixTime n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx : prefixTargetTime n * 6 =
      (n : ℝ)^2 * (1 - 1 / (n : ℝ) - prefixTargetDensity n) := by
    unfold prefixTargetTime
    ring
  have hp : prefixDensity n * (n : ℝ)^2 =
      (1 - 1 / (n : ℝ)) * (n : ℝ)^2 - 6 * prefixTime n := by
    unfold prefixDensity
    field_simp
  constructor
  · apply (le_of_mul_le_mul_right (a := (n : ℝ)^2) _ hn2)
    nlinarith
  · apply (lt_of_mul_lt_mul_right (a := (n : ℝ)^2) _ (le_of_lt hn2))
    have he : (6 / (n : ℝ)^2) * (n : ℝ)^2 = 6 := div_mul_cancel₀ _ (ne_of_gt hn2)
    nlinarith

end SharpTerminalLeave

open InnerProductSpace
open scoped InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_OneAddLogRpow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Asymptotics

lemma one_add_log_rpow_isLittleO (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (fun x : ℝ => (1 + Real.log x) ^ C) =o[atTop] fun x => x ^ δ := by
  let C' := max C 1
  have hC' : 0 < C' := lt_max_iff.mpr (Or.inr zero_lt_one)
  have hq : 0 < δ / C' := div_pos hδ hC'
  have hc : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ (δ / C') := by
    apply (isLittleO_const_left_of_ne one_ne_zero).mpr
    apply (tendsto_rpow_atTop hq).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (Real.norm_of_nonneg (Real.rpow_nonneg hx _)).symm
  have hs := hc.add (isLittleO_log_rpow_atTop hq)
  calc
    (fun x : ℝ => (1 + Real.log x) ^ C) =O[atTop]
        fun x => (1 + Real.log x) ^ C' := by
      apply IsBigO.of_norm_eventuallyLE
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx
      simp only [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Real.log x) C)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    _ =o[atTop] fun x => (x ^ (δ / C')) ^ C' :=
      hs.rpow hC' ((eventually_ge_atTop (0 : ℝ)).mono fun x hx => Real.rpow_nonneg hx _)
    _ =ᶠ[atTop] fun x => x ^ δ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_mul hx,div_mul_cancel₀ _ hC'.ne']

 theorem prefixTemplateFactor_subpower (C : ℝ) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C ≤ b * (n : ℝ) ^ δ := by
  have h := ((one_add_log_rpow_isLittleO C hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound hb
  filter_upwards [h,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hb0 : 0 ≤ 1 + Real.log (n : ℝ) := by linarith
  simpa only [Function.comp_apply,Real.norm_of_nonneg (Real.rpow_nonneg hb0 C),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) δ),prefixTemplateFactor] using hn

lemma prefixTargetDensity_eq (n : ℕ) :
    prefixTargetDensity n = (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  unfold prefixTargetDensity prefixEpsilon
  congr 1
  norm_num

lemma prefixTargetDensity_tendsto : Tendsto prefixTargetDensity atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => prefixTargetDensity n) atTop (𝓝 0)
  simp_rw [prefixTargetDensity_eq]
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999 / 2000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixTargetTime_eventually_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ prefixTargetTime n := by
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [prefixTargetDensity_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    hi.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hp hi
  unfold prefixTargetTime
  exact mul_nonneg (by positivity) (by linarith)

theorem prefixDensity_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (-(999 / 2000 : ℝ)) ≤ prefixDensity n ∧
      prefixDensity n ≤ 2 * (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  filter_upwards [prefixTargetTime_eventually_nonneg,eventually_ge_atTop (6 : ℕ)] with n ht hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl,hu⟩ := prefixDensity_bounds n (by omega) ht
  rw [prefixTargetDensity_eq] at hl hu
  refine ⟨hl,?_⟩
  have h1 : 6 / (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2) hn0).mpr
    nlinarith
  have h2 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  linarith

lemma prefix_target_D_identity (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ) ^ (-(999 / 2000 : ℝ))) ^ 2 =
      (n : ℝ) ^ (1 / 1000 : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Real.rpow_natCast,← Real.rpow_mul hnR.le]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnR]
  congr 1
  norm_num

theorem prefixD_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (1 / 1000 : ℝ) ≤ prefixD n ∧
      prefixD n ≤ 4 * (n : ℝ) ^ (1 / 1000 : ℝ) := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hp hn
  have hn0 : 0 < n := by omega
  have hq : 0 ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpl : 0 ≤ prefixDensity n := hq.trans hp.1
  rw [← prefix_target_D_identity n hn0]
  unfold prefixD
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hp.1 2) (Nat.cast_nonneg n)
  · have hsq := pow_le_pow_left₀ hpl hp.2 2
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hsq)]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PowersetCardTriple
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma powersetCard_triple {α : Type*} [DecidableEq α] {u v w : α}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u,v,w} : Finset α).powersetCard 2 = {{u,v},{u,w},{v,w}} := by
  have h2 : ({v,w}:Finset α).powersetCard 2 = {{v,w}} := by
    rw [← Finset.card_pair hvw]
    exact Finset.powersetCard_self _
  rw [Finset.powersetCard_succ_insert (by simp [huv,huw]) 1, h2]
  simp only [Finset.powersetCard_one, Finset.map_insert, Finset.map_singleton, Finset.image_insert,
    Finset.image_singleton, Function.Embedding.coeFn_mk]
  ext s
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma triangle_closure_iff {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    {u,v,w} ∈ triangles G ↔ {u,v} ∈ G := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  obtain ⟨huwG,hvwG⟩ := (mem_commonNeighbors G u v w).mp hw
  rw [mem_triangles, powersetCard_triple huv huw hvw]
  simp [huv,huw,hvw,Finset.insert_subset_iff,Finset.singleton_subset_iff,huwG,hvwG]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_RelativeScaleBudgetLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem relativeScaleBudget_le_log (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ k ≤ T, 0 < s k)
    (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hratio : ∀ k < T, s k ≤ 2*s (k+1)) :
    relativeScaleBudget s T ≤ 2*Real.log (s 0/s T) := by
  have hsingle {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) : r-1 ≤ 2*Real.log r := by
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one h1
    have hi : 0 ≤ 1-r⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hr).mpr h1)
    calc
      r-1 = r*(1-r⁻¹) := by field_simp
      _ ≤ 2*(1-r⁻¹) := mul_le_mul_of_nonneg_right h2 hi
      _ ≤ 2*Real.log r := mul_le_mul_of_nonneg_left
        (Real.one_sub_inv_le_log_of_pos hr) (by norm_num)
  have htel : (∑ k ∈ Finset.range T, Real.log (s k/s (k+1))) =
      Real.log (s 0/s T) := by
    calc
      _ = ∑ k ∈ Finset.range T, (Real.log (s k)-Real.log (s (k+1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkT := Finset.mem_range.mp hk
        exact Real.log_div (ne_of_gt (hs k (by omega)))
          (ne_of_gt (hs (k+1) (by omega)))
      _ = Real.log (s 0)-Real.log (s T) := by rw [Finset.sum_range_sub']
      _ = Real.log (s 0/s T) := (Real.log_div
        (ne_of_gt (hs 0 (Nat.zero_le T))) (ne_of_gt (hs T le_rfl))).symm
  rw [← htel,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkT := Finset.mem_range.mp hk
  exact hsingle ((one_le_div (hs (k+1) (by omega))).mpr (hdec k hkT))
    ((div_le_iff₀ (hs (k+1) (by omega))).mpr (hratio k hkT))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_EarlyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyDensity_antitone (n : ℕ) : Antitone (earlyDensity n) := by
  intro i j hij
  unfold earlyDensity
  have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact sub_le_sub_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (by norm_num)) (sq_nonneg (n : ℝ))) _

lemma earlyDensity_succ (n i : ℕ) :
    earlyDensity n i = earlyDensity n (i+1)+6/(n : ℝ)^2 := by
  unfold earlyDensity
  push_cast
  ring

lemma prefixDensity_eventually_inverse_lower : ∀ᶠ n : ℕ in atTop,
    1/(n : ℝ) ≤ prefixDensity n := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  apply le_trans _ hn.1
  rw [one_div,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)

theorem earlyTemplateScale_regular (a b : ℕ) : ∀ᶠ n : ℕ in atTop,
    (∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i) ∧
    (∀ i < prefixTime n, earlyTemplateScale a b n (i+1) ≤ earlyTemplateScale a b n i) ∧
    (∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1)) := by
  have hi : Tendsto (fun n : ℕ => 6/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (1+6/(n : ℝ))^b) atTop (𝓝 1) := by
    simpa only [add_zero,one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).add hi).pow b
  filter_upwards [prefixDensity_eventually_inverse_lower,
    hlim.eventually_le_const (by norm_num : (1 : ℝ) < 2),
    eventually_ge_atTop (1 : ℕ)] with n hp hratio hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow : ∀ i ≤ prefixTime n, 1/(n : ℝ) ≤ earlyDensity n i := by
    intro i hi
    exact hp.trans (earlyDensity_antitone n hi)
  have hpos : ∀ i ≤ prefixTime n, 0 < earlyDensity n i := by
    intro i hi
    exact lt_of_lt_of_le (by positivity) (hlow i hi)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    exact mul_pos (pow_pos hn0 _) (pow_pos (hpos i hi) _)
  · intro i hi
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos (i+1) (by omega)).le
      (earlyDensity_antitone n (Nat.le_succ i)) b) (by positivity)
  · intro i hi
    have hp1 : 0 < earlyDensity n (i+1) := hpos (i+1) (by omega)
    have hstep : earlyDensity n i ≤ earlyDensity n (i+1)*(1+6/(n : ℝ)) := by
      rw [earlyDensity_succ n i]
      have hh := hlow (i+1) (by omega)
      have hhmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ 6/(n : ℝ) by positivity)
      have he : (6/(n : ℝ))*(1/(n : ℝ)) = 6/(n : ℝ)^2 := by ring
      rw [he] at hhmul
      nlinarith only [hhmul]
    have hpw := pow_le_pow_left₀ (hpos i (by omega)).le hstep b
    rw [mul_pow] at hpw
    unfold earlyTemplateScale
    calc
      _ ≤ (n : ℝ)^a * (earlyDensity n (i+1)^b*(1+6/(n : ℝ))^b) :=
        mul_le_mul_of_nonneg_left hpw (by positivity)
      _ ≤ (n : ℝ)^a * (earlyDensity n (i+1)^b*2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio (by positivity))
          (by positivity)
      _ = _ := by ring

theorem earlyTemplateScale_log_budget (a b : ℕ) : ∀ᶠ n : ℕ in atTop,
    relativeScaleBudget (earlyTemplateScale a b n) (prefixTime n) ≤
      2*(b : ℝ)*Real.log n := by
  filter_upwards [earlyTemplateScale_regular a b,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n hreg hlow hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hlow
  have hscale : earlyTemplateScale a b n 0/earlyTemplateScale a b n (prefixTime n) ≤
      (n : ℝ)^b := by
    unfold earlyTemplateScale
    rw [earlyDensity_prefix,mul_div_mul_left _ _ (ne_of_gt (pow_pos hn0 a)),← div_pow]
    apply pow_le_pow_left₀ (div_nonneg (by
      have hh := (earlyDensity_antitone n (Nat.zero_le (prefixTime n)))
      change prefixDensity n ≤ earlyDensity n 0 at hh
      linarith) hp.le)
    apply (div_le_iff₀ hp).mpr
    have hp' := (div_le_iff₀ hn0).mp hlow
    have hzero : earlyDensity n 0 ≤ 1 := by unfold earlyDensity; simp
    nlinarith only [hp',hzero]
  have hlog := Real.log_le_log
    (div_pos (hreg.1 0 (Nat.zero_le _)) (hreg.1 (prefixTime n) le_rfl)) hscale
  rw [Real.log_pow] at hlog
  exact (relativeScaleBudget_le_log (earlyTemplateScale a b n) (prefixTime n)
    hreg.1 hreg.2.1 hreg.2.2).trans (by nlinarith only [hlog])

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CodegreeVertexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyCodegreeScale_ge_prefixD (n i : ℕ) (hi : i ≤ prefixTime n)
    (hp : 0 ≤ prefixDensity n) : prefixD n ≤ earlyTemplateScale 1 2 n i := by
  unfold earlyTemplateScale prefixD
  rw [pow_one]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp (earlyDensity_antitone n hi) 2) (Nat.cast_nonneg n)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_EarlyDensityOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyDensity_le_one (n i : ℕ) : earlyDensity n i ≤ 1 := by
  unfold earlyDensity
  have h₁ : 0 ≤ 1/(n : ℝ) := by positivity
  have h₂ : 0 ≤ 6*(i : ℝ)/(n : ℝ)^2 := by positivity
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEdgeRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter
open Classical

namespace SharpTerminalLeave

lemma early_density_positive {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) {i : ℕ} (hi : i ≤ prefixTime n) :
    0 < earlyDensity n i := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (hp.trans (earlyDensity_antitone n hi))

lemma early_density_log_bound {n i : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i ≤ prefixTime n) :
    -Real.log (earlyDensity n i) ≤ Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : Real.log (1/(n : ℝ)) ≤ Real.log (earlyDensity n i) :=
    Real.log_le_log (by positivity) (hp.trans (earlyDensity_antitone n hi))
  rw [one_div,Real.log_inv] at hh
  linarith

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PowerEulerError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma power_euler_error (b : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |(1-r)^b-1+(b : ℝ)*r| ≤ (b : ℝ)^2*r^2 := by
  have hber : ∀ b : ℕ, 0 ≤ (1-r)^b-1+(b : ℝ)*r := by
    intro b
    have hh := one_add_mul_le_pow (show -2 ≤ -r by linarith) b
    simp only [← sub_eq_add_neg,mul_neg] at hh
    linarith only [hh]
  have hupper : ∀ b : ℕ, (1-r)^b-1+(b : ℝ)*r ≤ (b : ℝ)^2*r^2 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1-r by linarith)
      have hn : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
      have hcube : 0 ≤ (b : ℝ)^2*r^3 := by positivity
      rw [pow_succ,Nat.cast_add,Nat.cast_one]
      nlinarith only [hm,hcube,mul_nonneg hn (sq_nonneg r),sq_nonneg r]
  rw [abs_of_nonneg (hber b)]
  exact hupper b

lemma history_relative_drift_sum {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : α → ℝ) (s : ℕ → ℝ)
    (T j : ℕ) (hj : j ≤ T) (ω : History α T) :
    f (ω (historyIndex T j))/s j-f (ω (historyIndex T 0))/s 0-
      historyNoise K (fun k a => f a/s k) T j ω =
    ∑ k ∈ Finset.range j,
      (pmfMean (K k (ω (historyIndex T k))) f/s (k+1)-f (ω (historyIndex T k))/s k) := by
  unfold historyNoise historyIncrement
  simp only [Nat.min_eq_left hj,div_eq_mul_inv,pmfMean_mul_const]
  have he := Finset.sum_range_sub' (fun k => f (ω (historyIndex T k))*(s k)⁻¹) j
  have hh : (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T k))*(s k)⁻¹-f (ω (historyIndex T (k+1)))*(s (k+1))⁻¹))+
      (∑ k ∈ Finset.range j,
        (f (ω (historyIndex T (k+1)))*(s (k+1))⁻¹-
          pmfMean (K k (ω (historyIndex T k))) f*(s (k+1))⁻¹)) =
      -(∑ k ∈ Finset.range j,
        (pmfMean (K k (ω (historyIndex T k))) f*(s (k+1))⁻¹-
          f (ω (historyIndex T k))*(s k)⁻¹)) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hh
  linarith only [hh]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighborsComplete
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma commonNeighbors_complete {n : ℕ} (u v : Fin n) :
    commonNeighbors (completeGraph n) u v = Finset.univ \ {u,v} := by
  ext w
  simp only [mem_commonNeighbors,mem_completeGraph,Finset.mem_sdiff,
    Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_and]
  by_cases hu : u = w <;> by_cases hv : v = w <;>
    simp [hu,hv,eq_comm]

lemma currentCodegree_complete {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    currentCodegree (completeGraph n) u v = n-2 := by
  rw [currentCodegree,commonNeighbors_complete]
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ]
  simp only [Finset.card_univ,Fintype.card_fin,Finset.card_pair huv]

theorem initial_normalized_codegree_error {n : ℕ} (hn : 2 ≤ n)
    (u v : Fin n) (huv : u ≠ v) :
    (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0-1 =
      -1/((n : ℝ)-1)^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  rw [currentCodegree_complete u v huv,Nat.cast_sub hn,Nat.cast_ofNat]
  unfold earlyTemplateScale earlyDensity
  simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero,pow_one]
  field_simp
  ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IncidentTriangleThird
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma incidentTriangle_third {n : ℕ} {G : Graph n} {u v : Fin n}
    (huv : u ≠ v) {t : Finset (Fin n)} (ht : t ∈ incidentTriangles G {u,v}) :
    ∃ w ∈ commonNeighbors G u v, t = {u,v,w} ∧ u ≠ w ∧ v ≠ w := by
  obtain ⟨ht,hpair⟩ := Finset.mem_filter.mp ht
  obtain ⟨htcard,htG⟩ := mem_triangles.mp ht
  have hsub : ({u,v} : Finset (Fin n)) ⊆ t := (Finset.mem_powersetCard.mp hpair).1
  have hc : (t \ {u,v}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, htcard, Finset.card_pair huv]
  obtain ⟨w,heq⟩ := Finset.card_eq_one.mp hc
  have hw : w ∈ t \ {u,v} := by rw [heq]; simp
  obtain ⟨hwt,hwuv⟩ := Finset.mem_sdiff.mp hw
  have huw : u ≠ w := by intro h; apply hwuv; simp [h]
  have hvw : v ≠ w := by intro h; apply hwuv; simp [h]
  have htriple : t = {u,v,w} := by
    have hu := Finset.sdiff_union_of_subset hsub
    rw [heq] at hu
    rw [← hu]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hcw : w ∈ commonNeighbors G u v := by
    apply (mem_commonNeighbors G u v w).mpr
    constructor
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair huw⟩
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair hvw⟩
  exact ⟨w,hcw,htriple,huw,hvw⟩

lemma incidentTriangles_eq_image {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    incidentTriangles G {u,v} = (commonNeighbors G u v).image (fun w => {u,v,w}) := by
  have huv : u ≠ v := by
    intro h
    have hh := mem_completeGraph.mp (hG he)
    simp [h] at hh
  ext t
  constructor
  · intro ht
    obtain ⟨w,hw,rfl,_,_⟩ := incidentTriangle_third huv ht
    exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
  · intro ht
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨(triangle_closure_iff hG huv hw).mpr he,?_⟩
    exact Finset.mem_powersetCard.mpr ⟨by simp,Finset.card_pair huv⟩

theorem triangleDegree_eq_codegree {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    triangleDegree G {u,v} = currentCodegree G u v := by
  unfold triangleDegree currentCodegree
  rw [incidentTriangles_eq_image hG he]
  apply Finset.card_image_of_injOn
  intro a ha b _ hab
  change ({u,v,a} : Finset (Fin n)) = {u,v,b} at hab
  have ha' : a ∈ ({u,v,b} : Finset (Fin n)) := by rw [← hab]; simp
  have hnea := commonNeighbors_ne hG ha
  simpa [hnea.1.symm,hnea.2.symm] using ha'

theorem step_mean_codegree {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (hQ : (triangles G).Nonempty)
    (u v : Fin n) (huv : u ≠ v) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)) =
      (currentCodegree G u v : ℝ) -
      (∑ w ∈ commonNeighbors G u v,
        ((currentCodegree G u w : ℝ) + currentCodegree G v w -
          if {u,v} ∈ G then 1 else 0)) / (triangles G).card := by
  rw [step_mean_codegree_hazard G u v hQ]
  congr 2
  apply Finset.sum_congr rfl
  intro w hw
  rw [wedge_hazard_exact hG huv hw]
  have hw' := (mem_commonNeighbors G u v w).mp hw
  rw [triangleDegree_eq_codegree hG hw'.1, triangleDegree_eq_codegree hG hw'.2]
  simp only [triangle_closure_iff hG huv hw]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ProspectiveFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedGood_bind {α : Type*} [Fintype α] (π : PMF α)
    (p : α → PMF (Bool × Bool)) :
    markedGood (π.bind p) = pmfMean π (fun a => markedGood (p a)) :=
  pmfMean_bind π p _

@[simp] theorem markedGood_no_marks (p : PMF Bool) :
    markedGood (p.map (fun b => (b,true))) = 1 := by
  rw [markedGood,pmfMean_map]
  simp only [↓reduceIte,pmfMean_const]

@[simp] theorem markedSuccess_no_marks (p : PMF Bool) :
    markedSuccess (p.map (fun b => (b,true))) = (p true).toReal := by
  rw [markedSuccess,pmfMean_map]
  simp [pmfMean]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma earlyTriangleScale_regular : ∀ᶠ n : ℕ in atTop,
    (∀ i ≤ prefixTime n, 0 < earlyTriangleScale n i) ∧
    (∀ i < prefixTime n, earlyTriangleScale n (i+1) ≤ earlyTriangleScale n i) ∧
    (∀ i < prefixTime n, earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1)) ∧
    relativeScaleBudget (earlyTriangleScale n) (prefixTime n) ≤ 6*Real.log n := by
  filter_upwards [earlyTemplateScale_regular 3 3,earlyTemplateScale_log_budget 3 3] with n hr hb
  refine ⟨fun i hi => div_pos (hr.1 i hi) (by norm_num),?_,?_,?_⟩
  · intro i hi
    exact div_le_div_of_nonneg_right (hr.2.1 i hi) (by norm_num)
  · intro i hi
    have hh := div_le_div_of_nonneg_right (hr.2.2 i hi) (by norm_num : (0 : ℝ) ≤ 6)
    simpa only [earlyTriangleScale,mul_div_assoc] using hh
  · convert hb using 1
    · unfold relativeScaleBudget earlyTriangleScale
      congr 1
      ext i
      ring
    · norm_num

lemma triangleDegree_complete {n : ℕ} (e : Finset (Fin n)) (he : e ∈ completeGraph n) :
    triangleDegree (completeGraph n) e = n-2 := by
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp he)
  rw [triangleDegree_eq_codegree (Finset.Subset.refl _) he,currentCodegree_complete u v huv]

lemma triangleCount_complete_formula {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (completeGraph n)).card : ℝ) = (n : ℝ)*(n-1)*(n-2)/6 := by
  have hh := triangle_degree_sum (completeGraph n)
  have he : (∑ e ∈ completeGraph n, (triangleDegree (completeGraph n) e : ℝ)) =
      ((completeGraph n).card : ℝ)*(n-2) := by
    calc
      _ = ∑ _e ∈ completeGraph n, ((n-2 : ℕ) : ℝ) := Finset.sum_congr rfl (fun e he => by rw [triangleDegree_complete e he])
      _ = _ := by simp [Nat.cast_sub hn]; ring
  rw [he,card_completeGraph,Nat.cast_choose_two] at hh
  nlinarith only [hh]

lemma initial_triangle_relative_error {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (completeGraph n)).card : ℝ)/earlyTriangleScale n 0-1 = -1/((n : ℝ)-1)^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  have hs : earlyTriangleScale n 0 = ((n : ℝ)-1)^3/6 := by
    unfold earlyTriangleScale earlyTemplateScale earlyDensity
    simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero]
    field_simp
  rw [triangleCount_complete_formula hn,hs]
  field_simp
  ring

lemma densityEdgeSafe_triangle_load {n : ℕ} {p η : ℝ} {G : Graph n}
    (hp : 0 ≤ p) (hη : η ≤ 1) (h : densityEdgeSafe n p η G) :
    copyLoadSafe (triangleRequired (n := n)) (2*((n : ℝ)*p^2)) G := by
  intro e he
  rw [triangle_copyEdgeLoad]
  have hb := (abs_le.mp (h.2.2 e he)).2
  have hd : 0 ≤ (n : ℝ)*p^2 := mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hp 2)
  have hh := mul_le_mul_of_nonneg_right hη hd
  linarith

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_DensityEdgeSafeTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

theorem densityEdgeSafe_triangle_euler_error {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (h : densityEdgeSafe n p η G) :
    |pmfMean (step G) (fun H => ((triangles H).card : ℝ))-(triangles G).card+
      3*(6/(n : ℝ)^2/p)*(triangles G).card| ≤ 6*η^2*((n : ℝ)*p^2)+2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast ht.card_pos
  have hm : (0 : ℝ) < G.card := by exact_mod_cast (graph_nonempty_of_triangles ht).card_pos
  have he : 9/(G.card : ℝ) = 3*(6/(n : ℝ)^2/p) := by
    rw [h.2.1]
    field_simp
    ring
  have hv := triangle_degree_variance_le (graph_nonempty_of_triangles ht) ((n : ℝ)*p^2)
    (η*((n : ℝ)*p^2)) (by positivity) h.2.2
  have hlo := (densityEdgeSafe_triangle_bounds h).1
  have hhalf : (n : ℝ)^3*p^3/12 ≤ (triangles G).card := by
    have hh := mul_le_mul_of_nonneg_left hη1 (show 0 ≤ (n : ℝ)^3*p^3/6 by positivity)
    nlinarith only [hlo,hh]
  have hVbound : triangleDegreeVariance G/(triangles G).card ≤ 6*η^2*((n : ℝ)*p^2) := by
    apply (div_le_iff₀ hq).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 6*η^2*((n : ℝ)*p^2) by positivity)
    rw [h.2.1] at hv
    nlinarith only [hv,hh]
  have hVnonneg : 0 ≤ triangleDegreeVariance G/(triangles G).card :=
    div_nonneg (triangleDegreeVariance_nonneg G) hq.le
  rw [step_mean_triangle_count_centered ht]
  have he' : 9*(triangles G).card/(G.card : ℝ) = 3*(6/(n : ℝ)^2/p)*(triangles G).card := by
    rw [mul_div_right_comm,he]
  rw [he']
  apply abs_le.mpr
  constructor <;> linarith only [hVbound,hVnonneg]

lemma relative_power_absolute_drift_bound {X Y s t r a B : ℝ} {b : ℕ}
    (hX : 0 ≤ X) (hs : 0 < s) (ht : 0 < t) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hscale : t = s*(1-r)^b) (hratio : s ≤ 2*t) (hcap : X ≤ B*s)
    (ha : 0 ≤ a) (h : |Y-X+(b : ℝ)*r*X| ≤ a*s) :
    |Y/t-X/s| ≤ 2*(a+B*(b : ℝ)^2*r^2) := by
  have hpow := power_euler_error b hr hr1
  have he : Y/t-X/s = ((Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r))/t := by
    apply (eq_div_iff ht.ne').mpr
    field_simp [hs.ne']
    rw [hscale]
    ring
  have hB : 0 ≤ B := (mul_nonneg_iff_of_pos_right hs).mp (hX.trans hcap)
  have hnum : |(Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r)| ≤
      (a+B*(b : ℝ)^2*r^2)*s := by
    calc
      _ ≤ |Y-X+(b : ℝ)*r*X|+|X*((1-r)^b-1+(b : ℝ)*r)| := abs_sub _ _
      _ ≤ a*s+X*((b : ℝ)^2*r^2) := by
        apply add_le_add h
        rw [abs_mul,abs_of_nonneg hX]
        exact mul_le_mul_of_nonneg_left hpow hX
      _ ≤ a*s+(B*s)*((b : ℝ)^2*r^2) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hcap (by positivity))
      _ = _ := by ring
  rw [he,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ a+B*(b : ℝ)^2*r^2 by positivity)
  exact hnum.trans (by nlinarith only [hm])

lemma early_triangle_drift_single {n : ℕ} {i : ℕ} {G : Graph n} {η : ℝ}
    (hn : 0 < n) (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i < prefixTime n)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hreg : earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1))
    (h : densityEdgeSafe n (earlyDensity n i) η G) :
    |pmfMean (step G) (fun H => ((triangles H).card : ℝ))/earlyTriangleScale n (i+1)-
      (triangles G).card/earlyTriangleScale n i| ≤
      12*η^2*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        36*(6/(n : ℝ)^2/earlyDensity n i)^2 := by
  let p := earlyDensity n i
  let lam := 6/(n : ℝ)^2/p
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := early_density_positive hn hp hi.le
  have hp1 := early_density_positive hn hp (show i+1 ≤ prefixTime n by omega)
  have hstep := earlyDensity_succ n i
  have hl : 0 ≤ lam := by dsimp [lam]; positivity
  have hl1 : lam ≤ 1 := by
    apply (div_le_iff₀ hp0).mpr
    dsimp only [p] at hp0 ⊢
    linarith only [hstep,hp1]
  have hs : 0 < earlyTriangleScale n i := by unfold earlyTriangleScale earlyTemplateScale; change 0 < (n : ℝ)^3*p^3/6; positivity
  have ht : 0 < earlyTriangleScale n (i+1) := by unfold earlyTriangleScale earlyTemplateScale; positivity
  have hscale : earlyTriangleScale n (i+1) = earlyTriangleScale n i*(1-lam)^3 := by
    have he : earlyDensity n (i+1) = p*(1-lam) := by
      have he : earlyDensity n (i+1) = p-6/(n : ℝ)^2 := by dsimp [p]; linarith only [hstep]
      rw [he]
      dsimp [lam]
      field_simp
    unfold earlyTriangleScale earlyTemplateScale
    rw [he,mul_pow]
    dsimp [p]
    ring
  have hcap : ((triangles G).card : ℝ) ≤ 2*earlyTriangleScale n i := by
    have hu := (densityEdgeSafe_triangle_bounds h).2
    have hh := mul_le_mul_of_nonneg_left (show 1+η ≤ 2 by linarith) hs.le
    exact hu.trans (by dsimp only [earlyTriangleScale,earlyTemplateScale] at hh ⊢; nlinarith only [hh])
  have hd := densityEdgeSafe_triangle_euler_error hn hp0 hη hη1 h
  have he : (6*η^2*lam+2*lam/((n : ℝ)*p^2))*earlyTriangleScale n i = 6*η^2*((n : ℝ)*p^2)+2 := by
    dsimp [lam,earlyTriangleScale,earlyTemplateScale]
    change (6*η^2*(6/(n : ℝ)^2/p)+2*(6/(n : ℝ)^2/p)/((n : ℝ)*p^2))*((n : ℝ)^3*p^3/6) = _
    field_simp
  rw [← he] at hd
  have hh := relative_power_absolute_drift_bound (Nat.cast_nonneg (triangles G).card) hs ht hl hl1
    hscale hreg hcap (by positivity : 0 ≤ 6*η^2*lam+2*lam/((n : ℝ)*p^2)) hd
  norm_num only [Nat.cast_ofNat] at hh
  dsimp only [lam,p] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma early_grid_sum_bounds {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (j : ℕ) (hj : j ≤ prefixTime n) :
    (∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i) ≤ Real.log n ∧
    (∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)) ≤ 1/(2*prefixD n) ∧
    (∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)^2) ≤ 6/(n : ℝ)*Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let p := earlyDensity n
  let h : ℝ := 6/(n : ℝ)^2
  let lam : ℕ → ℝ := fun i => h/p i
  have hpos : ∀ i ≤ prefixTime n, 0 < p i := fun i hi => early_density_positive hn hp hi
  have hstep : ∀ i, p i = p (i+1)+h := fun i => earlyDensity_succ n i
  have hlog : (∑ i ∈ Finset.range j, lam i) ≤ Real.log n := by
    have hh := (density_log_sum_bounds p h j (fun i hi => hpos i (hi.trans hj))
      (fun i _ => hstep i)).1
    have hp0 := Real.log_nonpos (hpos 0 (Nat.zero_le _)).le (earlyDensity_le_one n 0)
    have hln := early_density_log_bound hn hp hj
    dsimp only [lam] at hh ⊢
    linarith only [hh,hp0,hln]
  have hlD : (∑ i ∈ Finset.range j, lam i/((n : ℝ)*p i^2)) ≤ 1/(2*prefixD n) := by
    have hh := inverse_square_grid_sum p (n : ℝ) h j hnR (by dsimp [h]; positivity)
      (fun i hi => hpos i (hi.trans hj)) (fun i _ => hstep i)
    have he : (∑ i ∈ Finset.range j, 2*h/((n : ℝ)*p i^3)) =
        2*(∑ i ∈ Finset.range j, lam i/((n : ℝ)*p i^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have := hpos i ((Finset.mem_range.mp hi).le.trans hj)
      dsimp only [lam]
      field_simp
    rw [he] at hh
    have hDj := earlyCodegreeScale_ge_prefixD n j hj (le_trans (by positivity) hp)
    have hD : 0 < prefixD n := by unfold prefixD; have := early_density_positive hn hp (show prefixTime n ≤ prefixTime n by rfl); rw [earlyDensity_prefix] at this; positivity
    have hDj' : prefixD n ≤ (n : ℝ)*p j^2 := by simpa only [earlyTemplateScale,pow_one] using hDj
    have hr := one_div_le_one_div_of_le hD hDj'
    have ht : 0 ≤ 1/((n : ℝ)*p 0^2) := by positivity
    have he' : 1/prefixD n = 2*(1/(2*prefixD n)) := by ring
    rw [he'] at hr
    linarith only [hh,hr,ht]
  have hsq : (∑ i ∈ Finset.range j, (lam i)^2) ≤ 6/(n : ℝ)*Real.log n := by
    have hlmax (i : ℕ) (hi : i < j) : lam i ≤ 6/(n : ℝ) := by
      have hp' := hp.trans (earlyDensity_antitone n (hi.le.trans hj))
      change 1/(n : ℝ) ≤ p i at hp'
      apply (div_le_iff₀ (hpos i (hi.le.trans hj))).mpr
      dsimp only [h]
      have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 6/(n : ℝ) by positivity)
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    calc
      _ ≤ ∑ i ∈ Finset.range j, (6/(n : ℝ))*lam i := by
        apply Finset.sum_le_sum
        intro i hi
        have hli : 0 ≤ lam i := by dsimp [lam,h]; exact div_nonneg (by positivity) (hpos i ((Finset.mem_range.mp hi).le.trans hj)).le
        nlinarith only [mul_le_mul_of_nonneg_right (hlmax i (Finset.mem_range.mp hi)) hli]
      _ = 6/(n : ℝ)*(∑ i ∈ Finset.range j, lam i) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  exact ⟨hlog,hlD,hsq⟩

theorem early_triangle_drift_bound {n : ℕ} (η : ℝ) (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hreg : ∀ i < prefixTime n, earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1))
    (j : ℕ) (hj : j ≤ prefixTime n) (ω : History (Graph n) (prefixTime n))
    (hsafe : ∀ i < j, densityEdgeSafe n (earlyDensity n i) η (ω (historyIndex (prefixTime n) i))) :
    |(triangles (ω (historyIndex (prefixTime n) j))).card/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-
      historyNoise (fun _ => step) (fun i G => (triangles G).card/earlyTriangleScale n i)
        (prefixTime n) j ω| ≤ 12*η^2*Real.log n+2/prefixD n+216*Real.log n/(n : ℝ) := by
  have hb := early_grid_sum_bounds hn hp j hj
  rw [history_relative_drift_sum (fun _ => step) (fun G : Graph n => ((triangles G).card : ℝ))
    (earlyTriangleScale n) (prefixTime n) j hj ω]
  calc
    _ ≤ ∑ i ∈ Finset.range j,
        |pmfMean (step (ω (historyIndex (prefixTime n) i))) (fun G => ((triangles G).card : ℝ))/earlyTriangleScale n (i+1)-
          (triangles (ω (historyIndex (prefixTime n) i))).card/earlyTriangleScale n i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j,
        (12*η^2*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        36*(6/(n : ℝ)^2/earlyDensity n i)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij := Finset.mem_range.mp hi
      exact early_triangle_drift_single hn hp (by omega) hη hη1 (hreg i (by omega)) (hsafe i hij)
    _ = 12*η^2*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i)+
        4*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2))+
        36*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ 12*η^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hb.2.1 (by norm_num : (0 : ℝ) ≤ 4)
      have h₃ := mul_le_mul_of_nonneg_left hb.2.2 (by norm_num : (0 : ℝ) ≤ 36)
      simp only [div_eq_mul_inv,mul_inv_rev] at h₁ h₂ h₃ ⊢
      norm_num only [invOf_eq_inv,inv_div,inv_one] at h₂
      nlinarith only [h₁,h₂,h₃]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem history_noise_compensator {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T j : ℕ) (hj : j ≤ T)
    (ω : History α T) :
    f j (ω (historyIndex T j)) = f 0 (ω (historyIndex T 0))+
      historyNoise K f T j ω+historyCompensator K f T j ω := by
  unfold historyCompensator historyCounter historyNoise historyIncrement
  simp only [Nat.min_eq_left hj]
  rw [add_assoc,← Finset.sum_add_distrib]
  have he : (∑ k ∈ Finset.range j,
      (f (k+1) (ω (historyIndex T (k+1)))-pmfMean (K k (ω (historyIndex T k))) (f (k+1))+
        (pmfMean (K k (ω (historyIndex T k))) (f (k+1))-f k (ω (historyIndex T k))))) =
      f j (ω (historyIndex T j))-f 0 (ω (historyIndex T 0)) := by
    calc
      _ = ∑ k ∈ Finset.range j,
          (f (k+1) (ω (historyIndex T (k+1)))-f k (ω (historyIndex T k))) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := Finset.sum_range_sub (fun k => f k (ω (historyIndex T k))) j
  rw [he]
  ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CenteredCodegreeNeighborSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma codegree_hazard_centering {n : ℕ} (G : Graph n) (u v : Fin n) (s : ℝ) :
    (∑ w ∈ commonNeighbors G u v,
      ((currentCodegree G u w : ℝ)+currentCodegree G v w-if {u,v} ∈ G then 1 else 0)) =
    (2*s-if {u,v} ∈ G then 1 else 0)*(currentCodegree G u v : ℝ)+
      centeredCodegreeNeighborSum G u v s := by
  classical
  have he : (∑ w ∈ commonNeighbors G u v,
      ((currentCodegree G u w : ℝ)+currentCodegree G v w-if {u,v} ∈ G then 1 else 0)) =
      (∑ _w ∈ commonNeighbors G u v, (2*s-if {u,v} ∈ G then 1 else 0))+
        centeredCodegreeNeighborSum G u v s := by
    rw [centeredCodegreeNeighborSum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,currentCodegree]
  ring

theorem normalized_codegree_centered_drift {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (u v : Fin n) (huv : u ≠ v) (s t : ℝ) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)/t)-
      (currentCodegree G u v : ℝ)/s =
    (currentCodegree G u v : ℝ)*(1/t-1/s)-
      ((2*s-if {u,v} ∈ G then 1 else 0)*(currentCodegree G u v : ℝ)+
        centeredCodegreeNeighborSum G u v s)/((triangles G).card*t) := by
  by_cases hQ : (triangles G).Nonempty
  · have hd := step_mean_codegree hG hQ u v huv
    rw [codegree_hazard_centering G u v s] at hd
    simp only [div_eq_mul_inv,pmfMean_mul_const] at hd ⊢
    rw [hd,mul_inv_rev]
    ring
  · have hzero : triangles G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    rw [step,dite_eq_right hQ,pmfMean_pure,hzero,Finset.card_empty,Nat.cast_zero,zero_mul,div_zero]
    ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_EdgeStabilityRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma triangle_relative_inverse_bound {Q S r : ℝ} (hS : 0 < S) (hr : r ≤ 1/2)
    (h : |Q/S-1| ≤ r) : 0 < Q ∧ |1-S/Q| ≤ 2*r ∧ S/Q ≤ 2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  have hlow : S/2 ≤ Q := by
    have hh : 1/2 ≤ Q/S := by linarith
    have hh' := (le_div_iff₀ hS).mp hh
    linarith only [hh']
  have hQ : 0 < Q := lt_of_lt_of_le (by positivity) hlow
  have hab : |Q-S| ≤ r*S := by
    have he : Q/S-1 = (Q-S)/S := by field_simp
    rw [he,abs_div,abs_of_pos hS] at h
    exact (div_le_iff₀ hS).mp h
  have hratio : S/Q ≤ 2 := (div_le_iff₀ hQ).mpr (by linarith)
  have hr0 : 0 ≤ r := (abs_nonneg _).trans h
  refine ⟨hQ,?_,hratio⟩
  have he : 1-S/Q = (Q-S)/Q := by field_simp
  rw [he,abs_div,abs_of_pos hQ]
  calc
    _ ≤ r*S/Q := div_le_div_of_nonneg_right hab hQ.le
    _ = r*(S/Q) := by ring
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hratio hr0]

lemma edge_stability_coefficients {s t Q S lam r κ : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hS : 0 < S) (hl : 0 ≤ lam)
    (hscale : t = s*(1-lam)^2) (hratio : s ≤ 2*t)
    (hident : s = lam*S) (hr : r ≤ 1/2) (hQerr : |Q/S-1| ≤ r)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (0 ≤ edgeStabilityRate s t Q ∧ edgeStabilityRate s t Q ≤ 4*lam) ∧
      |edgeStabilityScalar s t Q κ| ≤ 8*r*lam+2*lam^2+4*lam/s := by
  obtain ⟨hQ,habs,hSQ⟩ := triangle_relative_inverse_bound hS hr hQerr
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hQerr
  have hsQ : s/Q ≤ 2*lam := by
    rw [hident,mul_div_assoc]
    simpa only [mul_comm lam 2] using mul_le_mul_of_nonneg_left hSQ hl
  have hsQdiff : |lam-s/Q| ≤ 2*r*lam := by
    have he : lam-s/Q = lam*(1-S/Q) := by rw [hident]; ring
    rw [he,abs_mul,abs_of_nonneg hl]
    nlinarith only [mul_le_mul_of_nonneg_left habs hl]
  have hsT : s/t ≤ 2 := (div_le_iff₀ ht).mpr hratio
  have haeq : edgeStabilityRate s t Q = (s/t)*(s/Q) := by unfold edgeStabilityRate; ring
  have hbeq : edgeStabilityScalar s t Q κ =
      (s/t)*(2*(lam-s/Q)-lam^2+κ/Q) := by
    unfold edgeStabilityScalar edgeStabilityRate
    apply (mul_right_cancel₀ ht.ne')
    field_simp [hs.ne',ht.ne',hQ.ne']
    rw [hscale]
    ring
  constructor
  · rw [haeq]
    exact ⟨by positivity,(mul_le_mul hsT hsQ (by positivity) (by norm_num)).trans_eq (by ring)⟩
  · have hκQ : |κ/Q| ≤ 2*lam/s := by
      rw [abs_of_nonneg (div_nonneg hκ hQ.le)]
      apply (le_div_iff₀ hs).mpr
      have hh := div_le_div_of_nonneg_right hκ1 hQ.le
      have hm := mul_le_mul_of_nonneg_right hh hs.le
      calc
        _ ≤ (1/Q)*s := hm
        _ = s/Q := by ring
        _ ≤ _ := hsQ
    have hb : |2*(lam-s/Q)-lam^2+κ/Q| ≤ 4*r*lam+lam^2+2*lam/s := by
      calc
        _ ≤ |2*(lam-s/Q)-lam^2|+|κ/Q| := abs_add_le _ _
        _ ≤ |2*(lam-s/Q)|+|lam^2|+|κ/Q| := by linarith only [abs_sub (2*(lam-s/Q)) (lam^2)]
        _ ≤ 4*r*lam+lam^2+2*lam/s := by
          rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_of_nonneg (sq_nonneg lam)]
          linarith only [hsQdiff,hκQ]
    rw [hbeq,abs_mul,abs_of_pos (div_pos hs ht)]
    calc
      _ ≤ 2*(4*r*lam+lam^2+2*lam/s) := mul_le_mul hsT hb (abs_nonneg _) (by norm_num)
      _ = _ := by ring

lemma early_codegree_grid {n i : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i < prefixTime n) :
    earlyTemplateScale 1 2 n (i+1) = earlyTemplateScale 1 2 n i*
      (1-6/(n : ℝ)^2/earlyDensity n i)^2 ∧
    earlyTemplateScale 1 2 n i = (6/(n : ℝ)^2/earlyDensity n i)*earlyTriangleScale n i ∧
    0 ≤ 6/(n : ℝ)^2/earlyDensity n i ∧
    6/(n : ℝ)^2/earlyDensity n i ≤ 6/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := early_density_positive hn hp hi.le
  have hs := earlyDensity_succ n i
  have he : earlyDensity n (i+1) = earlyDensity n i*(1-6/(n : ℝ)^2/earlyDensity n i) := by
    have he : earlyDensity n (i+1) = earlyDensity n i-6/(n : ℝ)^2 := by linarith only [hs]
    rw [he]
    field_simp
  refine ⟨?_,?_,by positivity,?_⟩
  · simp only [earlyTemplateScale,pow_one,he,mul_pow]; ring
  · unfold earlyTriangleScale
    simp only [earlyTemplateScale,pow_one]
    field_simp
  · have hp' := hp.trans (earlyDensity_antitone n hi.le)
    apply (div_le_iff₀ hpi).mpr
    have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 6/(n : ℝ) by positivity)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    field_simp

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixTriangleRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma triangle_closure_budget : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeRadius n ∧ prefixEdgeRadius n ≤ 1/2 ∧
    4/(n : ℝ)+codegreeNoiseRadius n+12*(prefixEdgeRadius n)^2*Real.log n+
      2/prefixD n+216*Real.log n/(n : ℝ) ≤ prefixTriangleRadius n := by
  have hrad : Tendsto prefixEdgeRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-1/40000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 1/40000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/80000)
      (by norm_num : (0 : ℝ) < 1/235),prefixD_eventual_envelope,
    hrad.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1 : ℕ)] with n hlog hD hrad hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have he : (prefixEdgeRadius n)^2 = (n : ℝ)^(-1/20000 : ℝ) := by
    unfold prefixEdgeRadius
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hinv : 1/(n : ℝ) ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    simpa only [Real.rpow_neg_one,one_div] using
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -1/20000))
  have hnoise : codegreeNoiseRadius n ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hdisc : 1/prefixD n ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    apply (div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hn0 _) hD.1).trans
    rw [one_div,← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hs := mul_le_mul_of_nonneg_right (show 1+Real.log (n : ℝ) ≤
      1/235*(n : ℝ)^(1/80000 : ℝ) by
        simpa only [prefixTemplateFactor,Real.rpow_one] using hlog)
      (show 0 ≤ 235*(prefixEdgeRadius n)^2 by positivity)
  have hprod : (n : ℝ)^(1/80000 : ℝ)*(prefixEdgeRadius n)^2 = prefixTriangleRadius n := by
    rw [he,← Real.rpow_add hn0]
    norm_num [prefixTriangleRadius]
  have hscaled : 235*(1+Real.log (n : ℝ))*(prefixEdgeRadius n)^2 ≤ prefixTriangleRadius n := by
    nlinarith only [hs,hprod]
  refine ⟨Real.rpow_nonneg hn0.le _,hrad,?_⟩
  have hgrid := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 216*Real.log (n : ℝ) by positivity)
  simp only [div_eq_mul_inv,one_mul] at hinv hdisc hgrid ⊢
  nlinarith only [hinv,hnoise,hdisc,hgrid,hscaled,sq_nonneg (prefixEdgeRadius n),
    mul_nonneg (sq_nonneg (prefixEdgeRadius n)) hl]

theorem prefix_triangle_tracking : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    |(triangles (ω (historyIndex (prefixTime n) j))).card/earlyTriangleScale n j-1| ≤
      prefixTriangleRadius n := by
  filter_upwards [triangle_closure_budget,earlyTriangleScale_regular,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (2 : ℕ)] with n hb hr hp hn
  intro ω hω hnse j hj hsafe
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by
    simpa only [PMF.mem_support_pure_iff] using hi
  have hloads : pastRelativeCopyLoadsSafe (triangleRequired (n := n)) (triangleNoiseLoad n)
      (prefixTime n) j ω := by
    intro i hit
    have hij : i < j := lt_of_lt_of_le hit (Nat.min_le_left _ _)
    have hh := densityEdgeSafe_triangle_load (early_density_positive hn0 hp (by omega)).le
      (show prefixEdgeRadius n ≤ 1 by linarith only [hb.2.1]) (hsafe i hij)
    simpa only [triangleNoiseLoad,earlyTemplateScale,pow_one] using hh
  have hcap : ∀ i < j, copyCount (triangleRequired (n := n)) (ω (historyIndex (prefixTime n) i)) ≤
      2*earlyTriangleScale n i := by
    intro i hij
    rw [triangle_copyCount]
    have hh := (densityEdgeSafe_triangle_bounds (hsafe i hij)).2
    have hS : 0 ≤ earlyTriangleScale n i := (hr.1 i (by omega)).le
    change _ ≤ earlyTriangleScale n i*(1+prefixEdgeRadius n) at hh
    have ht := mul_le_mul_of_nonneg_right hb.2.1 hS
    linarith only [hh,ht,hS]
  have hnoise : |historyNoise (fun _ => step)
      (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω| < codegreeNoiseRadius n := by
    apply lt_of_not_ge
    intro hcross
    apply hnse
    refine ⟨j,hj,hloads,hcap,?_⟩
    simpa only [triangle_copyCount] using hcross
  have hd := early_triangle_drift_bound (prefixEdgeRadius n) hn0 hp hb.1 hb.2.1
    hr.2.2.1 j hj ω hsafe
  have hinit : |(triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-1| ≤ 4/(n : ℝ) := by
    rw [hi',initial_triangle_relative_error hn,neg_div,abs_neg,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((n : ℝ)-1)^2)]
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero (by linarith)) (by linarith : (0 : ℝ) < n)).mpr
    nlinarith
  have ht := (abs_add_le
    (((triangles (ω (historyIndex (prefixTime n) j))).card : ℝ)/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-
      historyNoise (fun _ => step) (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω)
    (historyNoise (fun _ => step) (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω))
  have ht' := abs_add_le
    (((triangles (ω (historyIndex (prefixTime n) j))).card : ℝ)/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0)
    (((triangles (ω (historyIndex (prefixTime n) 0))).card : ℝ)/earlyTriangleScale n 0-1)
  simp only [sub_add_cancel] at ht
  simp only [sub_add_sub_cancel] at ht'
  linarith only [ht,ht',hd,hnoise,hinit,hb.2.2]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEdgeForcingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma prefix_edge_forcing_power : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeForcingBound n ∧
    prefixEdgeForcingBound n ≤ 49*(1+Real.log (n : ℝ))*prefixTriangleRadius n := by
  filter_upwards [prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hD hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have ht : 0 ≤ prefixTriangleRadius n := Real.rpow_nonneg hn0.le _
  have hl := Real.log_nonneg hn1
  have hD0 := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hD.1
  have hi : 1/(n : ℝ) ≤ prefixTriangleRadius n := by
    simpa only [Real.rpow_neg_one,one_div,prefixTriangleRadius] using
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -3/80000))
  have hno0 : 0 ≤ codegreeNoiseRadius n := Real.rpow_nonneg hn0.le _
  have hno : codegreeNoiseRadius n ≤ prefixTriangleRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hdi : 1/prefixD n ≤ prefixTriangleRadius n := by
    apply (div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hn0 _) hD.1).trans
    rw [one_div,← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hg := mul_le_mul_of_nonneg_left hi (show 0 ≤ 24*Real.log (n : ℝ) by positivity)
  constructor
  · unfold prefixEdgeForcingBound
    positivity
  · unfold prefixEdgeForcingBound
    simp only [div_eq_mul_inv,one_mul] at hi hdi hg ⊢
    nlinarith only [hi,hno,hdi,hg,ht,mul_nonneg ht hl]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryGraphNested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma prefix_triangle_radius_small : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixTriangleRadius n ∧ prefixTriangleRadius n ≤ 1/2 := by
  have hl : Tendsto prefixTriangleRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-3/80000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 3/80000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hl.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hn
  exact ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,hn⟩

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CenteredNeighborSumBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma centered_neighbor_sum_bound {n : ℕ} {G : Graph n} (_hG : G ⊆ completeGraph n)
    (u v : Fin n) {s η : ℝ} (_hη : 0 ≤ η) (_hs : 0 ≤ s)
    (hrow : ∀ a b, {a,b} ∈ G → |(currentCodegree G a b : ℝ)-s| ≤ η*s) :
    |centeredCodegreeNeighborSum G u v s| ≤ 2*η*s*(currentCodegree G u v : ℝ) := by
  unfold centeredCodegreeNeighborSum
  calc
    _ ≤ ∑ w ∈ commonNeighbors G u v,
      |(currentCodegree G u w : ℝ)+currentCodegree G v w-2*s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w ∈ commonNeighbors G u v, 2*η*s := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨huw,hvw⟩ := (mem_commonNeighbors G u v w).mp hw
      have hh := abs_add_le ((currentCodegree G u w : ℝ)-s) ((currentCodegree G v w : ℝ)-s)
      have he : (currentCodegree G u w : ℝ)+currentCodegree G v w-2*s =
          ((currentCodegree G u w : ℝ)-s)+((currentCodegree G v w : ℝ)-s) := by ring
      rw [he]
      linarith only [hh,hrow u w huw,hrow v w hvw]
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,currentCodegree]; ring

lemma normalized_pair_drift_factor {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (u v : Fin n) (huv : u ≠ v) (s t : ℝ) (hs : s ≠ 0) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)/t)-
      (currentCodegree G u v : ℝ)/s =
      edgeStabilityScalar s t (triangles G).card (if {u,v} ∈ G then 1 else 0)*
        ((currentCodegree G u v : ℝ)/s)-
      centeredCodegreeNeighborSum G u v s/((triangles G).card*t) := by
  rw [normalized_codegree_centered_drift hG u v huv]
  unfold edgeStabilityScalar edgeStabilityRate
  field_simp [hs]
  ring

lemma normalized_pair_drift_bound {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (u v : Fin n) (huv : u ≠ v) {s t S lam r η : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hS : 0 < S) (hl : 0 ≤ lam)
    (hscale : t = s*(1-lam)^2) (hratio : s ≤ 2*t)
    (hident : s = lam*S) (hr : r ≤ 1/2)
    (hQerr : |(triangles G).card/S-1| ≤ r) (hη : 0 ≤ η)
    (hrow : ∀ a b, {a,b} ∈ G → |(currentCodegree G a b : ℝ)-s| ≤ η*s)
    (hcap : (currentCodegree G u v : ℝ) ≤ 2*s) :
    |pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)/t)-
      (currentCodegree G u v : ℝ)/s| ≤
      16*r*lam+4*lam^2+8*lam/s+16*η*lam := by
  have hκ0 : (0 : ℝ) ≤ if {u,v} ∈ G then 1 else 0 := by split_ifs <;> norm_num
  have hκ1 : (if {u,v} ∈ G then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hb := edge_stability_coefficients hs ht hS hl hscale hratio hident hr hQerr hκ0 hκ1
  have hQ := (triangle_relative_inverse_bound hS hr hQerr).1
  have hc : 0 ≤ (currentCodegree G u v : ℝ)/s := by positivity
  have hc' : (currentCodegree G u v : ℝ)/s ≤ 2 := (div_le_iff₀ hs).mpr hcap
  have hneigh : |centeredCodegreeNeighborSum G u v s| ≤ 4*η*s^2 := by
    apply (centered_neighbor_sum_bound hG u v hη hs.le hrow).trans
    exact (mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 2*η*s)).trans_eq (by ring)
  have hquot : |centeredCodegreeNeighborSum G u v s/((triangles G).card*t)| ≤ 16*η*lam := by
    rw [abs_div,abs_of_pos (mul_pos hQ ht)]
    calc
      _ ≤ (4*η*s^2)/((triangles G).card*t) := div_le_div_of_nonneg_right hneigh (mul_pos hQ ht).le
      _ = 4*η*edgeStabilityRate s t (triangles G).card := by unfold edgeStabilityRate; ring
      _ ≤ 4*η*(4*lam) := mul_le_mul_of_nonneg_left hb.1.2 (by positivity)
      _ = _ := by ring
  rw [normalized_pair_drift_factor hG u v huv s t hs.ne']
  calc
    _ ≤ |edgeStabilityScalar s t (triangles G).card (if {u,v} ∈ G then 1 else 0)*
          ((currentCodegree G u v : ℝ)/s)|+
        |centeredCodegreeNeighborSum G u v s/((triangles G).card*t)| := abs_sub _ _
    _ ≤ (8*r*lam+2*lam^2+4*lam/s)*2+16*η*lam := by
      apply add_le_add _ hquot
      rw [abs_mul,abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left hc' (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hb.2 (by norm_num))
    _ = _ := by ring

theorem prefix_pair_compensator_bound : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ u v : Fin n, u ≠ v →
    (∀ i < j, (currentCodegree (ω (historyIndex (prefixTime n) i)) u v : ℝ) ≤ 2*earlyTemplateScale 1 2 n i) →
    |historyCompensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω| ≤
      16*prefixTriangleRadius n*Real.log n+4/prefixD n+24*Real.log n/(n : ℝ)+
        16*prefixEdgeRadius n*Real.log n := by
  filter_upwards [prefix_triangle_tracking,earlyTemplateScale_regular 1 2,
    earlyTriangleScale_regular,prefix_triangle_radius_small,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n htrack hreg htri hr hp hn
  intro ω hω hnoise j hj hsafe u v huv hcap
  have hn0 : 0 < n := by omega
  have hη : 0 ≤ prefixEdgeRadius n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hterm (i : ℕ) (hi : i < j) :
      |pmfMean (step (ω (historyIndex (prefixTime n) i))) (prefixNormalizedCodegree u v (i+1))-
        prefixNormalizedCodegree u v i (ω (historyIndex (prefixTime n) i))| ≤
        16*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)^2+
        8*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        16*prefixEdgeRadius n*(6/(n : ℝ)^2/earlyDensity n i) := by
    have hs := hsafe i hi
    have hc := htrack ω hω hnoise i (by omega) (fun k hk => hsafe k (by omega))
    have hg := early_codegree_grid hn0 hp (by omega : i < prefixTime n)
    have hrow (a b : Fin n) (he : {a,b} ∈ ω (historyIndex (prefixTime n) i)) :
        |(currentCodegree (ω (historyIndex (prefixTime n) i)) a b : ℝ)-earlyTemplateScale 1 2 n i| ≤
          prefixEdgeRadius n*earlyTemplateScale 1 2 n i := by
      have hh := hs.2.2 {a,b} he
      rw [triangleDegree_eq_codegree hs.1 he] at hh
      simpa only [earlyTemplateScale,pow_one] using hh
    change |pmfMean (step (ω (historyIndex (prefixTime n) i))) (fun H => (currentCodegree H u v : ℝ)/earlyTemplateScale 1 2 n (i+1))-
      (currentCodegree (ω (historyIndex (prefixTime n) i)) u v : ℝ)/earlyTemplateScale 1 2 n i| ≤ _
    simpa only [earlyTemplateScale,pow_one] using
      normalized_pair_drift_bound hs.1 u v huv (hreg.1 i (by omega)) (hreg.1 (i+1) (by omega))
        (htri.1 i (by omega)) hg.2.2.1 hg.1 (hreg.2.2 i (by omega)) hg.2.1 hr.2 hc hη hrow (hcap i hi)
  unfold historyCompensator historyCounter
  rw [Nat.min_eq_left hj]
  have hg := early_grid_sum_bounds hn0 hp j hj
  calc
    _ ≤ ∑ i ∈ Finset.range j, |pmfMean (step (ω (historyIndex (prefixTime n) i))) (prefixNormalizedCodegree u v (i+1))-
        prefixNormalizedCodegree u v i (ω (historyIndex (prefixTime n) i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j,
        (16*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)^2+
        8*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        16*prefixEdgeRadius n*(6/(n : ℝ)^2/earlyDensity n i)) :=
      Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
    _ = 16*prefixTriangleRadius n*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i)+
        4*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)^2)+
        8*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2))+
        16*prefixEdgeRadius n*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hg.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hr.1)
      have h₂ := mul_le_mul_of_nonneg_left hg.2.2 (by norm_num : (0 : ℝ) ≤ 4)
      have h₃ := mul_le_mul_of_nonneg_left hg.2.1 (by norm_num : (0 : ℝ) ≤ 8)
      have h₄ := mul_le_mul_of_nonneg_left hg.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hη)
      simp only [div_eq_mul_inv,mul_inv_rev] at h₁ h₂ h₃ h₄ ⊢
      norm_num at h₃
      nlinarith only [h₁,h₂,h₃,h₄]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixPairClosureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma prefix_pair_closure_budget : ∀ᶠ n : ℕ in atTop,
    prefixEdgeForcingBound n+16*prefixEdgeRadius n*Real.log n ≤ prefixWheelRadius n/2 ∧
      prefixWheelRadius n ≤ 1 := by
  filter_upwards [prefix_edge_forcing_power,
    prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/80000)
      (by norm_num : (0 : ℝ) < 1/130),eventually_ge_atTop (1 : ℕ)] with n hF hlog hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hl := Real.log_nonneg hn1
  have hη : 0 ≤ prefixEdgeRadius n := Real.rpow_nonneg hn0.le _
  have hr : prefixTriangleRadius n ≤ prefixEdgeRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hlog' : 1+Real.log (n : ℝ) ≤ 1/130*(n : ℝ)^(1/80000 : ℝ) := by
    simpa only [prefixTemplateFactor,Real.rpow_one] using hlog
  have he : (n : ℝ)^(1/80000 : ℝ)*prefixEdgeRadius n = prefixWheelRadius n := by
    unfold prefixEdgeRadius prefixWheelRadius
    rw [← Real.rpow_add hn0]
    congr 1
    norm_num
  refine ⟨?_,Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)⟩
  calc
    _ ≤ 49*(1+Real.log (n : ℝ))*prefixEdgeRadius n+16*prefixEdgeRadius n*Real.log n := by
      exact add_le_add (hF.2.trans (mul_le_mul_of_nonneg_left hr (by positivity))) le_rfl
    _ ≤ 65*(1+Real.log (n : ℝ))*prefixEdgeRadius n := by nlinarith only [hη]
    _ ≤ 65*(1/130*(n : ℝ)^(1/80000 : ℝ))*prefixEdgeRadius n := by gcongr
    _ = prefixWheelRadius n/2 := by rw [show 65*(1/130*(n : ℝ)^(1/80000 : ℝ))*prefixEdgeRadius n =
        ((n : ℝ)^(1/80000 : ℝ)*prefixEdgeRadius n)/2 by ring,he]

lemma initial_normalized_pair_bound {n : ℕ} (hn : 2 ≤ n)
    (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (u v : Fin n) (huv : u ≠ v) :
    |prefixNormalizedCodegree u v 0 (ω (historyIndex (prefixTime n) 0))-1| ≤ 4/(n : ℝ) := by
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by simpa using hi
  unfold prefixNormalizedCodegree
  rw [hi',initial_normalized_codegree_error hn u v huv,
    neg_div,abs_neg,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((n : ℝ)-1)^2)]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero (by linarith)) (by linarith : (0 : ℝ) < n)).mpr
  nlinarith

theorem prefix_pair_barrier_improvement : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ u v : Fin n, u ≠ v →
    (∀ i < j, (currentCodegree (ω (historyIndex (prefixTime n) i)) u v : ℝ) ≤ 2*earlyTemplateScale 1 2 n i) →
    |prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1| ≤ prefixWheelRadius n/2 := by
  filter_upwards [prefix_pair_compensator_bound,prefix_pair_closure_budget,
    eventually_ge_atTop (2 : ℕ)] with n hcomp hbudget hn
  intro ω hω htri hnoise j hj hsafe u v huv hcap
  have hc := hcomp ω hω htri j hj hsafe u v huv hcap
  have hnse : |historyNoise (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω| < codegreeNoiseRadius n := by
    apply lt_of_not_ge
    intro hx
    exact hnoise u v ⟨j,hj,hcap,hx⟩
  have hi := initial_normalized_pair_bound hn ω hω u v huv
  have he := history_noise_compensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j hj ω
  have he' : prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1 =
      (prefixNormalizedCodegree u v 0 (ω (historyIndex (prefixTime n) 0))-1)+
      historyNoise (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω+
      historyCompensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω := by linarith only [he]
  rw [he']
  apply le_trans _ hbudget.1
  have hab := (abs_add_le ((prefixNormalizedCodegree u v 0 (ω (historyIndex (prefixTime n) 0))-1)+
      historyNoise (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω)
      (historyCompensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  apply hab.trans
  unfold prefixEdgeForcingBound
  linarith only [hi,hnse,hc]

theorem prefix_all_pair_closure_oai : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    ∀ j ≤ prefixTime n, ∀ u v : Fin n, u ≠ v →
      |prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1| ≤ prefixWheelRadius n/2 := by
  filter_upwards [prefix_present_edge_closure,prefix_pair_barrier_improvement,
    prefix_pair_closure_budget,earlyTemplateScale_regular 1 2] with n hedge hpair hbudget hreg
  intro ω hω hroot hbalanced htri hnoise j
  have hs := hedge ω hω hroot hbalanced htri hnoise
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj u v huv
    apply hpair ω hω htri hnoise j hj (fun i hi => hs i (by omega)) u v huv
    intro i hi
    have hh := (le_abs_self (prefixNormalizedCodegree u v i (ω (historyIndex (prefixTime n) i))-1)).trans
      (ih i hi (by omega) u v huv)
    have hc : prefixNormalizedCodegree u v i (ω (historyIndex (prefixTime n) i)) ≤ 2 := by
      linarith only [hh,hbudget.2]
    exact (div_le_iff₀ (hreg.1 i (by omega))).mp hc

end SharpTerminalLeave
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpTerminalLeave.prefix_all_pair_closure_oai := @OAI.SharpTerminalLeave.prefix_all_pair_closure_oai
