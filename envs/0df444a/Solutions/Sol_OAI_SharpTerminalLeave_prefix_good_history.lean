-- Prove2me | solution 1 for OAI.SharpTerminalLeave.prefix_good_history
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:59:14.349479+00:00
-- url     : https://prove2.me/submissions/eed53617-fe06-43ce-a34d-42e392669ad2

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000
import Theorems.Thm_OAI_SharpTerminalLeave_prefix_all_pair_closure
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

theorem sum_card_le_card_biUnion_add_pair_overlaps {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α) (F : α → Finset β) :
    (∑ a ∈ s, (F a).card) ≤ (s.biUnion F).card +
      ∑ a ∈ s, ∑ b ∈ s.erase a, ((F a) ∩ F b).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>

    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    have hi : ((F a) ∩ s.biUnion F).card ≤ ∑ b ∈ s, ((F a) ∩ F b).card := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le
    have hcard := Finset.card_union_add_card_inter (F a) (s.biUnion F)
    have hsum : (∑ x ∈ s, ∑ b ∈ s.erase x, ((F x) ∩ F b).card) ≤
        ∑ x ∈ s, ∑ b ∈ (insert a s).erase x, ((F x) ∩ F b).card := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.erase_subset_erase x (Finset.subset_insert a s)
      · intro i _ _; exact Nat.zero_le _
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    omega

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

theorem incident_pair_card_le_one {n : ℕ} (G : Graph n)
    {e f : Finset (Fin n)} (hef : e ≠ f) :
    ((incidentTriangles G e) ∩ incidentTriangles G f).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht u hu
  simp only [incidentTriangles, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_powersetCard] at ht hu
  exact triangle_eq_of_two_edges (mem_triangles.mp ht.1.1).1
    (mem_triangles.mp hu.1.1).1 ht.1.2.2 ht.2.2.2 hef
    ht.1.2.1 ht.2.2.1 hu.1.2.1 hu.2.2.1

theorem hittingTriangles_card_le_degree_sum {n : ℕ} (G F : Graph n) :
    (hittingTriangles G F).card ≤ ∑ e ∈ F, triangleDegree G e := by
  rw [hittingTriangles_eq_biUnion]
  exact Finset.card_biUnion_le

theorem degree_sum_le_hittingTriangles_add {n : ℕ} (G F : Graph n) :
    (∑ e ∈ F, triangleDegree G e) ≤ (hittingTriangles G F).card + F.card ^ 2 := by
  rw [hittingTriangles_eq_biUnion]
  refine (sum_card_le_card_biUnion_add_pair_overlaps F (incidentTriangles G)).trans ?_
  apply Nat.add_le_add_left
  calc
    (∑ e ∈ F, ∑ f ∈ F.erase e, ((incidentTriangles G e) ∩ incidentTriangles G f).card)
        ≤ ∑ _e ∈ F, F.card := by
          apply Finset.sum_le_sum
          intro e _
          calc
            (∑ f ∈ F.erase e, ((incidentTriangles G e) ∩ incidentTriangles G f).card)
                ≤ ∑ _f ∈ F.erase e, 1 := by
                  apply Finset.sum_le_sum
                  intro f hf
                  exact incident_pair_card_le_one G (Finset.ne_of_mem_erase hf).symm
            _ = (F.erase e).card := by simp
            _ ≤ F.card := Finset.card_le_card (Finset.erase_subset e F)
    _ = F.card ^ 2 := by simp [pow_two]

theorem hittingTriangles_degree_error {n : ℕ} (G F : Graph n) (D δ : ℝ)
    (h : ∀ e ∈ F, |(triangleDegree G e : ℝ) - D| ≤ δ) :
    |((hittingTriangles G F).card : ℝ) - (F.card : ℝ) * D| ≤
      (F.card : ℝ) * δ + (F.card : ℝ) ^ 2 := by
  have hsumlo : (F.card : ℝ) * (D - δ) ≤ ∑ e ∈ F, (triangleDegree G e : ℝ) := by
    calc
      _ = ∑ _e ∈ F, (D - δ) := by simp [mul_sub]
      _ ≤ _ := Finset.sum_le_sum fun e he => by
        have hh := (abs_le.mp (h e he)).1
        linarith
  have hsumhi : (∑ e ∈ F, (triangleDegree G e : ℝ)) ≤ (F.card : ℝ) * (D + δ) := by
    calc
      _ ≤ ∑ _e ∈ F, (D + δ) := Finset.sum_le_sum fun e he => by
        have hh := (abs_le.mp (h e he)).2
        linarith
      _ = _ := by simp [mul_add]
  have hhitlo : (∑ e ∈ F, (triangleDegree G e : ℝ)) ≤
      ((hittingTriangles G F).card : ℝ) + (F.card : ℝ) ^ 2 := by
    exact_mod_cast degree_sum_le_hittingTriangles_add G F
  have hhithi : ((hittingTriangles G F).card : ℝ) ≤
      ∑ e ∈ F, (triangleDegree G e : ℝ) := by
    exact_mod_cast hittingTriangles_card_le_degree_sum G F
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (F.card : ℝ)]

theorem copyCount_drift_error {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (b : ℕ) (D δ : ℝ)
    (hsize : ∀ a, (required a).card = b)
    (hdeg : ∀ e ∈ G, |(triangleDegree G e : ℝ) - D| ≤ δ)
    (hG : (triangles G).Nonempty) :
    |pmfMean (step G) (copyCount required) - copyCount required G +
      ((b : ℝ) * D / (triangles G).card) * copyCount required G| ≤
      (((b : ℝ) * δ + (b : ℝ) ^ 2) / (triangles G).card) * copyCount required G := by
  classical
  let loss (a : α) : ℝ :=
    if required a ⊆ G then ((hittingTriangles G (required a)).card : ℝ) else 0
  have ha (a : α) : |loss a - (b : ℝ) * D * intact (required a) G| ≤
      ((b : ℝ) * δ + (b : ℝ) ^ 2) * intact (required a) G := by
    by_cases hpres : required a ⊆ G
    · have hh := hittingTriangles_degree_error G (required a) D δ
        (fun e he => hdeg e (hpres he))
      simpa only [loss, hpres, ite_eq_left, intact, hsize, mul_one] using hh
    · simp [loss, intact, hpres]
  have hs : |∑ a, (loss a - (b : ℝ) * D * intact (required a) G)| ≤
      ((b : ℝ) * δ + (b : ℝ) ^ 2) * copyCount required G := by
    calc
      _ ≤ ∑ a, |loss a - (b : ℝ) * D * intact (required a) G| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ((b : ℝ) * δ + (b : ℝ) ^ 2) * intact (required a) G :=
        Finset.sum_le_sum fun a _ => ha a
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hG.card_pos
  have hid : pmfMean (step G) (copyCount required) - copyCount required G +
      ((b : ℝ) * D / (triangles G).card) * copyCount required G =
      -(∑ a, (loss a - (b : ℝ) * D * intact (required a) G)) / (triangles G).card := by
    rw [step_mean_copyCount required G hG, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change copyCount required G - (∑ a, loss a) / _ - copyCount required G +
      (_ / _) * copyCount required G = -((∑ a, loss a) - (b : ℝ) * D * copyCount required G) / _
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos hq]
  calc
    _ ≤ (((b : ℝ) * δ + (b : ℝ) ^ 2) * copyCount required G) / (triangles G).card :=
      div_le_div_of_nonneg_right hs hq.le
    _ = _ := by ring

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryAlive
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
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

lemma intact_nonnegative {n : ℕ} (F G : Graph n) : 0 ≤ intact F G := by
  classical
  unfold intact
  split_ifs <;> norm_num

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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_RootedTemplates
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
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

theorem imageEdges_simple {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n)
    {e : Finset (Fin n)} (he : e ∈ imageEdges T φ) : e.card = 2 := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  simpa using T.simple f hf

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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_HistoryLawPathSupport
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

theorem copyCount_nonneg {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) : 0 ≤ copyCount required G := by
  apply Finset.sum_nonneg
  intro a _
  unfold intact
  split <;> norm_num

end SharpTerminalLeave

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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleLiftCount
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

lemma copyEdgeLoad_eq_subfamily {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (e : Finset (Fin n)) :
    copyEdgeLoad required G e =
      copyCount (fun a : {a // e ∈ required a} => required a.val) G := by
  classical
  rw [copyEdgeLoad,copyCount]
  have hh := Finset.sum_subtype (F := inferInstance)
    (Finset.univ.filter (fun a => e ∈ required a))
    (by intro a; simp : ∀ a, a ∈ Finset.univ.filter (fun a => e ∈ required a) ↔
      e ∈ required a) (fun a => intact (required a) G)
  rw [← hh,Finset.sum_filter]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_OverlapVertices
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical

namespace SharpTerminalLeave

lemma rooted_completion_factorization {k n : ℕ} (T : RootedTemplate k)
    (J : Finset (Fin k)) (hJ : T.roots ⊆ J) (p : ℝ) :
    ((n : ℝ)^(J.card-T.roots.card)*p^(T.edges.filter (fun e => e ⊆ J)).card) *
      ((n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card)) =
        rootedScaling T n p := by
  have hi := Finset.card_le_card hJ
  have hj : J.card ≤ k := by simpa only [Fintype.card_fin] using J.card_le_univ
  have he := Finset.card_le_card (Finset.filter_subset (fun e => e ⊆ J) T.edges)
  unfold rootedScaling
  calc
    _ = (n : ℝ)^((J.card-T.roots.card)+(k-J.card))*
        p^((T.edges.filter (fun e => e ⊆ J)).card+
          (T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card)) := by rw [pow_add,pow_add]; ring
    _ = _ := by congr 2 <;> omega

theorem largeTemplate_completion_scale {k n : ℕ} (T : RootedTemplate k)
    {p : ℝ} (hp : 0 ≤ p) (hT : largeTemplateEligible T n p)
    (J : Finset (Fin k)) (hJ : T.roots ⊆ J) :
    (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (fun e => e ⊆ J)).card) ≤
      rootedScaling T n p := by
  have hJscale := hT J hJ (T.edges.filter (fun e => e ⊆ J))
    (Finset.filter_subset _ _) (fun e he => (Finset.mem_filter.mp he).2)
  rw [← rooted_completion_factorization T J hJ p]
  exact le_mul_of_one_le_left (by positivity) hJscale

end SharpTerminalLeave
end
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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_FallingFactorialNormalizedProduct
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

lemma fallingFactorial_normalized_product (r a n : ℕ) (hn : r+a ≤ n) (hn0 : 0 < n) :
    ((n-r).descFactorial a : ℝ)/(n : ℝ)^a =
      ∏ i ∈ Finset.range a, (1-((r+i : ℕ) : ℝ)/(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  have hh : (n : ℝ)^a = ∏ _i ∈ Finset.range a, (n : ℝ) := by simp
  rw [hh,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hri : r+i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [Nat.sub_sub,Nat.cast_sub hri]
  field_simp

theorem fallingFactorial_normalized_error (r a n : ℕ) (hn : r+a ≤ n) (hn0 : 0 < n) :
    |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-1| ≤
      (a : ℝ)*(r+a : ℕ)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [fallingFactorial_normalized_product r a n hn hn0]
  let f := fun i : ℕ => 1-((r+i : ℕ) : ℝ)/(n : ℝ)
  have hf : ∀ i ∈ Finset.range a, f i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    have hri : r+i ≤ n := by have := Finset.mem_range.mp hi; omega
    have h0 : 0 ≤ ((r+i : ℕ) : ℝ)/(n : ℝ) := by positivity
    have h1 : ((r+i : ℕ) : ℝ)/(n : ℝ) ≤ 1 := by
      apply (div_le_one hnR).mpr
      exact_mod_cast hri
    exact ⟨by dsimp [f]; linarith,by dsimp [f]; linarith⟩
  have hh := abs_prod_sub_prod_le_sum (Finset.range a) f (fun _ => 1) hf
    (fun _ _ => ⟨zero_le_one,le_rfl⟩)
  simp only [Finset.prod_const_one] at hh
  apply hh.trans
  calc
    (∑ i ∈ Finset.range a, |f i-1|) =
        ∑ i ∈ Finset.range a, ((r+i : ℕ) : ℝ)/(n : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      have h0 : 0 ≤ ((r+i : ℕ) : ℝ)/(n : ℝ) := by positivity
      rw [show 1-((r+i : ℕ) : ℝ)/(n : ℝ)-1 = -(((r+i : ℕ) : ℝ)/(n : ℝ)) by ring,
        abs_neg,abs_of_nonneg h0]
    _ ≤ ∑ _i ∈ Finset.range a, ((r+a : ℕ) : ℝ)/(n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ hnR.le
      exact_mod_cast (by have := Finset.mem_range.mp hi; omega : r+i ≤ r+a)
    _ = _ := by simp; ring

theorem initialDensity_power_error (b n : ℕ) (hn : 1 ≤ n) :
    |(1-1/(n : ℝ))^b-1| ≤ (b : ℝ)/(n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 ≤ 1-1/(n : ℝ) := by
    have : 1/(n : ℝ) ≤ 1 := by apply (div_le_one (by linarith)).mpr; exact hnR
    linarith
  have hp1 : 1-1/(n : ℝ) ≤ 1 := by
    have : 0 ≤ 1/(n : ℝ) := by positivity
    linarith
  have hh := abs_prod_sub_prod_le_sum (Finset.range b) (fun _ => 1-1/(n : ℝ))
    (fun _ => 1) (fun _ _ => ⟨hp0,hp1⟩) (fun _ _ => ⟨zero_le_one,le_rfl⟩)
  simpa only [Finset.prod_const,Finset.card_range,one_pow,
    show 1-1/(n : ℝ)-1 = -(1/(n : ℝ)) by ring,abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1/(n : ℝ)),Finset.sum_const,
    nsmul_eq_mul,mul_one_div] using hh

theorem initialRootedScaling_error (r a b n : ℕ) (hn : r+a ≤ n) (hn2 : 2 ≤ n) :
    |((n-r).descFactorial a : ℝ) /
      ((n : ℝ)^a * (1-1/(n : ℝ))^b)-1| ≤
      (2 : ℝ)^b * ((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : 0 < n := by omega
  have hnR0 : (0 : ℝ) < n := by linarith
  have hp : (1/2 : ℝ) ≤ 1-1/(n : ℝ) := by
    have hh : 1/(n : ℝ) ≤ 1/2 := (div_le_div_iff₀ hnR0 (by norm_num)).mpr (by linarith)
    linarith
  have hp0 : 0 < (1-1/(n : ℝ))^b := pow_pos (by linarith) _
  have hi : 1/(1-1/(n : ℝ))^b ≤ (2 : ℝ)^b := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hp b
    have hh2 : (1/2 : ℝ)^b = 1/(2 : ℝ)^b := by rw [div_pow,one_pow]
    rw [hh2] at hh
    exact (div_le_iff₀ hp0).mpr (by
      have ht : (0 : ℝ) < (2 : ℝ)^b := by positivity
      have hmul := (div_le_iff₀ ht).mp hh
      simpa only [mul_comm] using hmul)
  have hf := fallingFactorial_normalized_error r a n hn hn0
  have ht := initialDensity_power_error b n (by omega)
  have he : |((n-r).descFactorial a : ℝ) /
      ((n : ℝ)^a*(1-1/(n : ℝ))^b)-1| =
      |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b| /
        (1-1/(n : ℝ))^b := by
    calc
      _ = |(((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b) /
          (1-1/(n : ℝ))^b| := by
        rw [sub_div,div_self (ne_of_gt hp0),div_div]
      _ = _ := by rw [abs_div,abs_of_pos hp0]
  rw [he,div_eq_mul_inv]
  have he2 : |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b| ≤
      ((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ) := by
    calc
      _ ≤ |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-1| +
          |(1-1/(n : ℝ))^b-1| := by
        simpa only [abs_sub_comm (1 : ℝ)] using
          (abs_sub_le (((n-r).descFactorial a : ℝ)/(n : ℝ)^a) 1 ((1-1/(n : ℝ))^b))
      _ ≤ (a : ℝ)*(r+a : ℕ)/(n : ℝ)+(b : ℝ)/(n : ℝ) := add_le_add hf ht
      _ = _ := by ring
  calc
    _ ≤ (((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ)) * (2 : ℝ)^b :=
      mul_le_mul he2 (by simpa only [one_div] using hi) (inv_nonneg.mpr hp0.le)
        (by positivity)
    _ = _ := by ring

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedInjectionEquivFree
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
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

theorem card_rootedInjection {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    Fintype.card (RootedInjection T ψ) =
      (n-T.roots.card).descFactorial (k-T.roots.card) := by
  classical
  rw [Fintype.card_congr (rootedInjectionEquivFree T ψ),Fintype.card_embedding_eq]
  have hfree : Fintype.card {v : Fin k // v ∉ T.roots} = k-T.roots.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using
      (Fintype.card_subtype_compl (fun v : Fin k => v ∈ T.roots))
  have htarget : Fintype.card {w : Fin n // w ∉ Set.range ψ} = n-T.roots.card := by
    calc
      _ = Fintype.card (↑((Set.range ψ)ᶜ)) := Fintype.card_congr (Equiv.refl _)
      _ = n-T.roots.card := by
        rw [Fintype.card_compl_set,Fintype.card_range,Fintype.card_fin,Fintype.card_coe]
  rw [hfree,htarget]

theorem rootedCount_completeGraph {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    rootedCount T ψ (completeGraph n) =
      ((n-T.roots.card).descFactorial (k-T.roots.card) : ℝ) := by
  classical
  unfold rootedCount copyCount
  have hcontains : ∀ φ : RootedInjection T ψ, imageEdges T φ.val ⊆ completeGraph n := by
    intro φ e he
    exact mem_completeGraph.mpr (imageEdges_simple T φ.val he)
  simp only [intact,ite_eq_left (hcontains _),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,card_rootedInjection]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedTemplateEdgesCard
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
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

lemma rootedTemplate_edges_card_le_sq {k : ℕ} (T : RootedTemplate k) :
    T.edges.card ≤ k^2 := by
  have hh : T.edges ⊆ completeGraph k := by
    intro e he
    exact mem_completeGraph.mpr (T.simple e he)
  exact (Finset.card_le_card hh).trans (by rw [card_completeGraph]; exact Nat.choose_le_pow k 2)

theorem rootedCount_initial_uniform_error (H : ℕ) {k n : ℕ} (hk : k ≤ H)
    (hn : H ≤ n) (hn2 : 2 ≤ n) (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    |rootedCount T ψ (completeGraph n) /
      rootedScaling T n (1-1/(n : ℝ))-1| ≤
      (2 : ℝ)^(H^2) * (2*(H : ℝ)^2)/(n : ℝ) := by
  have hr : T.roots.card ≤ k := by simpa using Finset.card_le_univ T.roots
  have hs : T.roots.card+(k-T.roots.card) = k := Nat.add_sub_of_le hr
  have hb : T.edges.card ≤ H^2 := (rootedTemplate_edges_card_le_sq T).trans
    (Nat.pow_le_pow_left hk 2)
  rw [rootedCount_completeGraph]
  unfold rootedScaling
  have hh := initialRootedScaling_error T.roots.card (k-T.roots.card) T.edges.card n
    (by rw [hs]; exact hk.trans hn) hn2
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply mul_le_mul
  · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb
  · rw [hs]
    have ha : (k-T.roots.card : ℕ) ≤ H := (Nat.sub_le _ _).trans hk
    have haR : ((k-T.roots.card : ℕ) : ℝ) ≤ H := by exact_mod_cast ha
    have hkR : (k : ℝ) ≤ H := by exact_mod_cast hk
    have hbR : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by exact_mod_cast hb
    have hmul := mul_le_mul haR hkR (Nat.cast_nonneg k) (Nat.cast_nonneg H)
    nlinarith only [hmul,hbR]
  · positivity
  · positivity

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedCompletionMax
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
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

lemma rootedCompletionMax_large {k n : ℕ} (T : RootedTemplate k) {p : ℝ}
    (hp : 0 ≤ p) (hT : largeTemplateEligible T n p) :
    rootedCompletionMax T n p ≤ rootedScaling T n p := by
  have h1 : 1 ≤ rootedScaling T n p := by
    simpa only [rootedScaling,Finset.card_univ,Fintype.card_fin] using
      hT Finset.univ (Finset.subset_univ _) T.edges (Finset.Subset.refl _)
        (fun _ _ => Finset.subset_univ _)
  apply Finset.sup'_le
  intro J _
  split_ifs with hJ
  · exact largeTemplate_completion_scale T hp hT J hJ
  · exact h1

lemma rootedCompletionMax_small {k n : ℕ} (T : RootedTemplate k) {p : ℝ}
    (hT : smallTemplateEligible T n p) : rootedCompletionMax T n p ≤ 1 := by
  apply Finset.sup'_le
  intro J _
  split_ifs with hJ
  · exact hT J hJ
  · exact le_rfl

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_RerootTemplate
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Filter

namespace SharpTerminalLeave

lemma rerootTemplate_image_subset {k n : ℕ} (T : RootedTemplate k)
    (J : Finset (Fin k)) (φ : Fin k ↪ Fin n) :
    imageEdges (rerootTemplate T J) φ ⊆ imageEdges T φ := by
  exact Finset.image_subset_image (Finset.filter_subset _ _)

lemma rerootTemplate_remaining {k : ℕ} (T : RootedTemplate k)
    (J K : Finset (Fin k)) (hJK : J ⊆ K) :
    (rerootTemplate T J).edges.card-
      ((rerootTemplate T J).edges.filter (· ⊆ K)).card =
        T.edges.card-(T.edges.filter (· ⊆ K)).card := by
  rw [← Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    ← Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  congr 1
  ext e
  simp only [rerootTemplate,Finset.mem_sdiff,Finset.mem_filter]
  constructor
  · rintro ⟨⟨he,hJ⟩,hK⟩
    exact ⟨he,fun hk => hK ⟨⟨he,hJ⟩,hk.2⟩⟩
  · rintro ⟨he,hK⟩
    have hnK : ¬ e ⊆ K := fun hk => hK ⟨he,hk⟩
    exact ⟨⟨he,fun hj => hnK (hj.trans hJK)⟩,fun hk => hnK hk.2⟩

lemma balanced_overlap_scale {k n : ℕ} (T : RootedTemplate k)
    (hT : RootedTwoBalanced T) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Finset (Fin k)) (hJ : T.roots ⊆ J) :
    ((n : ℝ)*p^2)^(J.card-T.roots.card) ≤
      (n : ℝ)^(J.card-T.roots.card)*p^(T.edges.filter (· ⊆ J)).card := by
  rw [mul_pow,← pow_mul]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hp hp1 (hT J hJ)) (by positivity)

lemma balanced_completion_bound {k n : ℕ} (T : RootedTemplate k)
    (hT : RootedTwoBalanced T) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hD : 1 ≤ (n : ℝ)*p^2) (J : Finset (Fin k))
    (hJ : T.roots ⊆ J) (hJ' : T.roots.card < J.card) :
    (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (· ⊆ J)).card) ≤
      rootedScaling T n p/((n : ℝ)*p^2) := by
  have hD0 : 0 < (n : ℝ)*p^2 := lt_of_lt_of_le zero_lt_one hD
  apply (le_div_iff₀ hD0).mpr
  rw [← rooted_completion_factorization T J hJ p]
  have hl : (n : ℝ)*p^2 ≤
      (n : ℝ)^(J.card-T.roots.card)*p^(T.edges.filter (· ⊆ J)).card := by
    apply le_trans _ (balanced_overlap_scale T hT hp.le hp1 J hJ)
    simpa only [pow_one] using (pow_le_pow_right₀ hD (show 1 ≤ J.card-T.roots.card by omega))
  exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans_eq (mul_comm _ _)

theorem balanced_reroot_completion_bound {k n : ℕ} (T : RootedTemplate k)
    (hT : RootedTwoBalanced T) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hD : 1 ≤ (n : ℝ)*p^2) (J : Finset (Fin k))
    (hJ : T.roots ⊆ J) (hJ' : T.roots.card < J.card) :
    rootedCompletionMax (rerootTemplate T J) n p ≤ rootedScaling T n p/((n : ℝ)*p^2) := by
  have h1 : 1 ≤ rootedScaling T n p/((n : ℝ)*p^2) := by
    have hk : T.roots.card < (Finset.univ : Finset (Fin k)).card :=
      lt_of_lt_of_le hJ' (Finset.card_le_card (Finset.subset_univ J))
    simpa using balanced_completion_bound T hT hp hp1 hD Finset.univ (Finset.subset_univ _) hk
  apply Finset.sup'_le
  intro K _
  split_ifs with hK
  · change J ⊆ K at hK
    rw [rerootTemplate_remaining T J K hK]
    exact balanced_completion_bound T hT hp hp1 hD K (hJ.trans hK)
      (hJ'.trans_le (Finset.card_le_card hK))
  · exact h1

lemma fintype_sum_le_injection {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : α → ℝ) (g : β → ℝ)
    (hfg : ∀ a, f a ≤ g (e a)) (hg : ∀ b, 0 ≤ g b) :
    ∑ a, f a ≤ ∑ b, g b := by
  calc
    _ ≤ ∑ a, g (e a) := Finset.sum_le_sum (fun a _ => hfg a)
    _ = ∑ b ∈ Finset.univ.image e, g b := (Finset.sum_image (fun a _ b _ h => he h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => hg b)

lemma rootedEdgePin_card {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n)) :
    Fintype.card (RootedEdgePin T ψ f e) ≤ e.card^f.card := by
  let enc : RootedEdgePin T ψ f e → (f → e) := fun ξ v =>
    ⟨ξ.val ⟨v.val,Finset.mem_union_right _ v.property⟩,ξ.property.2 v⟩
  have hinj : Function.Injective enc := by
    intro ξ χ hh
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    rcases Finset.mem_union.mp v.property with hv | hv
    · exact (ξ.property.1 ⟨v.val,hv⟩).trans (χ.property.1 ⟨v.val,hv⟩).symm
    · exact congrArg Subtype.val (congrFun hh ⟨v.val,hv⟩)
  simpa only [Fintype.card_fun,Fintype.card_coe] using Fintype.card_le_of_injective enc hinj

lemma rootedEdgeFiberEncoding_injective {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n)) :
    Function.Injective (rootedEdgeFiberEncoding T ψ f e) := by
  intro φ χ hh
  have he := congrArg (fun z : Σ ξ : RootedEdgePin T ψ f e,
      RootedInjection (rerootTemplate T (T.roots ∪ f)) ξ.val => z.2.val) hh
  exact Subtype.ext (Subtype.ext he)

lemma intact_antitone_required {n : ℕ} {F J : Graph n} (hF : F ⊆ J) (G : Graph n) :
    intact J G ≤ intact F G := by
  unfold intact
  split_ifs with hJ hFG hFG
  · exact le_rfl
  · exact False.elim (hFG (hF.trans hJ))
  · norm_num
  · norm_num

lemma rooted_edge_fiber_load {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n))
    (G : Graph n) (L : ℝ) (hL : 0 ≤ L)
    (hcounts : ∀ ξ : {v // v ∈ T.roots ∪ f} ↪ Fin n,
      rootedCount (rerootTemplate T (T.roots ∪ f)) ξ G ≤ L) :
    (∑ φ : {φ : RootedInjection T ψ // f.map φ.val = e}, intact (imageEdges T φ.val.val) G) ≤
      (e.card : ℝ)^f.card*L := by
  have hh := fintype_sum_le_injection (rootedEdgeFiberEncoding T ψ f e)
    (rootedEdgeFiberEncoding_injective T ψ f e)
    (fun φ => intact (imageEdges T φ.val.val) G)
    (fun z => intact (imageEdges (rerootTemplate T (T.roots ∪ f)) z.2.val) G)
    (fun φ => intact_antitone_required (rerootTemplate_image_subset T (T.roots ∪ f) φ.val.val) G)
    (fun a => intact_nonnegative _ _)
  apply hh.trans
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _ξ : RootedEdgePin T ψ f e, L := Finset.sum_le_sum (fun ξ _ => hcounts ξ.val)
    _ = (Fintype.card (RootedEdgePin T ψ f e) : ℝ)*L := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast rootedEdgePin_card T ψ f e) hL

theorem rooted_copyEdgeLoad_from_reroots {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (G : Graph n) (e : Finset (Fin n))
    (he : e.card = 2) (L : ℝ) (hL : 0 ≤ L)
    (hcounts : ∀ f ∈ T.edges, ∀ ξ : {v // v ∈ T.roots ∪ f} ↪ Fin n,
      rootedCount (rerootTemplate T (T.roots ∪ f)) ξ G ≤ L) :
    copyEdgeLoad (fun φ : RootedInjection T ψ => imageEdges T φ.val) G e ≤
      4*(T.edges.card : ℝ)*L := by
  let A := {φ : RootedInjection T ψ // e ∈ imageEdges T φ.val}
  let B := Σ f : T.edges, {φ : RootedInjection T ψ // f.val.map φ.val = e}
  have hex (φ : A) : ∃ f ∈ T.edges, f.map φ.val.val = e := Finset.mem_image.mp φ.property
  let enc : A → B := fun φ =>
    ⟨⟨(hex φ).choose,(hex φ).choose_spec.1⟩,φ.val,(hex φ).choose_spec.2⟩
  have hinj : Function.Injective enc := by
    intro φ χ h
    exact Subtype.ext (congrArg (fun z : B => z.2.val) h)
  rw [copyEdgeLoad_eq_subfamily,copyCount]
  have hh := fintype_sum_le_injection enc hinj
    (fun φ : A => intact (imageEdges T φ.val.val) G)
    (fun z : B => intact (imageEdges T z.2.val.val) G)
    (fun _ => le_refl _) (fun _ => intact_nonnegative _ _)
  apply hh.trans
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _f : T.edges, 4*L := by
      apply Finset.sum_le_sum
      intro f _
      have hh := rooted_edge_fiber_load T ψ f.val e G L hL (hcounts f.val f.property)
      simpa only [he,T.simple f.val f.property,Nat.cast_ofNat,show (2 : ℝ)^2 = 4 by norm_num] using hh
    _ = _ := by simp; ring

theorem balanced_rooted_load_bound {H k n : ℕ} (T : RootedTemplate k)
    (hk : k ≤ H) (hT : RootedTwoBalanced T)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (G : Graph n) (hG : G ⊆ completeGraph n)
    {p B : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hB : 0 ≤ B) (hD : 1 ≤ (n : ℝ)*p^2)
    (hupper : ∀ k ≤ H, ∀ U : RootedTemplate k, ∀ ξ : {v // v ∈ U.roots} ↪ Fin n,
      rootedCount U ξ G ≤ B*rootedCompletionMax U n p) :
    copyLoadSafe (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      (4*(T.edges.card : ℝ)*B*rootedScaling T n p/((n : ℝ)*p^2)) G := by
  intro e he
  have hnonneg : 0 ≤ B*(rootedScaling T n p/((n : ℝ)*p^2)) := by
    unfold rootedScaling; positivity
  have hmain := rooted_copyEdgeLoad_from_reroots T ψ G e (mem_completeGraph.mp (hG he))
    (B*(rootedScaling T n p/((n : ℝ)*p^2))) hnonneg ?_
  · convert hmain using 1; ring
  intro f hf ξ
  have hproper : T.roots.card < (T.roots ∪ f).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_union_left,?_⟩
    intro hh
    exact T.independent f hf (hh ▸ Finset.subset_union_right)
  exact (hupper k hk (rerootTemplate T (T.roots ∪ f)) ξ).trans
    (mul_le_mul_of_nonneg_left (balanced_reroot_completion_bound T hT hp hp1 hD
      (T.roots ∪ f) Finset.subset_union_left hproper) hB)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_DegreeTemplate
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
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

lemma degreeTemplate_balanced : RootedTwoBalanced degreeTemplate := by
  unfold RootedTwoBalanced degreeTemplate
  decide

lemma degree_rooted_zero {n : ℕ} (u : Fin n) (φ : RootedInjection degreeTemplate (degreeRoot u)) :
    φ.val 0 = u := φ.property ⟨0,by decide⟩

lemma degree_image_subset {n : ℕ} (u : Fin n) (φ : RootedInjection degreeTemplate (degreeRoot u))
    (G : Graph n) : imageEdges degreeTemplate φ.val ⊆ G ↔ {u,φ.val 1} ∈ G := by
  simp [imageEdges,degreeTemplate,degree_rooted_zero u φ]

lemma degree_restrict_injective {n : ℕ} (u : Fin n) :
    Function.Injective (fun φ : RootedInjection degreeTemplate (degreeRoot u) => φ.val 1) := by
  intro φ χ h
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  fin_cases i
  · exact (degree_rooted_zero u φ).trans (degree_rooted_zero u χ).symm
  · exact h

lemma degree_restrict_surj {n : ℕ} (u v : Fin n) (hne : u ≠ v) :
    ∃ φ : RootedInjection degreeTemplate (degreeRoot u), φ.val 1 = v := by
  let f : Fin 2 → Fin n := ![u,v]
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  refine ⟨⟨⟨f,hf⟩,?_⟩,rfl⟩
  intro r
  have hr : r.val = 0 := Finset.mem_singleton.mp r.property
  change f r.val = u
  rw [hr]
  rfl

theorem degree_rootedCount {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    rootedCount degreeTemplate (degreeRoot u) G = currentDegree G u := by
  let A := Finset.univ.filter (fun φ : RootedInjection degreeTemplate (degreeRoot u) =>
    imageEdges degreeTemplate φ.val ⊆ G)
  have hA : rootedCount degreeTemplate (degreeRoot u) G = (A.card : ℝ) := by
    simp [rootedCount,copyCount,intact,A]
  rw [hA]
  unfold currentDegree
  congr 1
  apply Finset.card_bij (fun φ _ => φ.val 1)
  · intro φ hφ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(degree_image_subset u φ G).mp (Finset.mem_filter.mp hφ).2⟩
  · intro φ _ χ _ h
    exact degree_restrict_injective u h
  · intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    have hne : u ≠ v := by
      intro h
      have hh := mem_completeGraph.mp (hG hv')
      simp [h] at hh
    obtain ⟨φ,hφ⟩ := degree_restrict_surj u v hne
    refine ⟨φ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hφ⟩
    exact (degree_image_subset u φ G).mpr (hφ.symm ▸ hv')

end SharpTerminalLeave
end
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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PowerEulerError
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
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

lemma densityEdgeSafe_rate_error {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (h : densityEdgeSafe n p η G) :
    |(n : ℝ)*p^2/(triangles G).card-6/(n : ℝ)^2/p| ≤
      2*η*(6/(n : ℝ)^2/p) ∧
    1/(triangles G).card ≤ 2*(6/(n : ℝ)^2/p)/((n : ℝ)*p^2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
  let Q₀ : ℝ := (n : ℝ)^3*p^3/6
  let lam : ℝ := 6/(n : ℝ)^2/p
  have hQ₀ : 0 < Q₀ := by dsimp [Q₀]; positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hD : 0 < (n : ℝ)*p^2 := by positivity
  have hid : lam*Q₀ = (n : ℝ)*p^2 := by dsimp [lam,Q₀]; field_simp
  obtain ⟨hlo,hhi⟩ := densityEdgeSafe_triangle_bounds h
  change Q₀*(1-η) ≤ _ at hlo
  change _ ≤ Q₀*(1+η) at hhi
  have hhalf : Q₀/2 ≤ (triangles G).card := by nlinarith [mul_le_mul_of_nonneg_left hη1 hQ₀.le]
  have habs : |Q₀-(triangles G).card| ≤ η*Q₀ := by apply abs_le.mpr; constructor <;> nlinarith only [hlo,hhi]
  constructor
  · have he : (n : ℝ)*p^2/(triangles G).card-lam = lam*(Q₀-(triangles G).card)/(triangles G).card := by rw [← hid]; field_simp
    change |(n : ℝ)*p^2/(triangles G).card-lam| ≤ 2*η*lam
    rw [he,abs_div,abs_mul,abs_of_pos hlam,abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    have hm := mul_le_mul_of_nonneg_left habs hlam.le
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*η*lam by positivity)
    nlinarith only [hm,hh]
  · apply (div_le_div_iff₀ hq hD).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*lam by positivity)
    dsimp only [lam] at hid hh
    nlinarith only [hid,hh]

theorem densityEdgeSafe_copy_euler_error {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (b : ℕ) (hsize : ∀ a, (required a).card = b)
    {p η : ℝ} {G : Graph n} (hn : 0 < n) (hp : 0 < p)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/2) (h : densityEdgeSafe n p η G) :
    |pmfMean (step G) (copyCount required)-copyCount required G+
      (b : ℝ)*(6/(n : ℝ)^2/p)*copyCount required G| ≤
      (4*(b : ℝ)*η*(6/(n : ℝ)^2/p)+
        2*(b : ℝ)^2*(6/(n : ℝ)^2/p)/((n : ℝ)*p^2))*copyCount required G := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
  have hX := copyCount_nonneg required G
  have hD : 0 < (n : ℝ)*p^2 := by positivity
  have hr := densityEdgeSafe_rate_error hn hp hη hη1 h
  have hd := copyCount_drift_error required G b (n*p^2) (η*(n*p^2)) hsize h.2.2 hQ
  let lam := 6/(n : ℝ)^2/p
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hrate : (n : ℝ)*p^2/(triangles G).card ≤ 2*lam := by
    have hh := mul_le_mul_of_nonneg_left hr.2 hD.le
    have he : ((n : ℝ)*p^2)*(1/(triangles G).card) = (n : ℝ)*p^2/(triangles G).card := by ring
    rw [he,mul_div_cancel₀ _ hD.ne'] at hh
    exact hh
  have hcoef : ((b : ℝ)*(η*(n*p^2))+(b : ℝ)^2)/(triangles G).card ≤
      2*(b : ℝ)*η*lam+2*(b : ℝ)^2*lam/((n : ℝ)*p^2) := by
    have h₁ := mul_le_mul_of_nonneg_left hrate (show 0 ≤ (b : ℝ)*η by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hr.2 (sq_nonneg (b : ℝ))
    dsimp only [lam] at h₁ ⊢
    simp only [div_eq_mul_inv] at h₁ h₂ ⊢
    nlinarith only [h₁,h₂]
  calc
    _ ≤ |pmfMean (step G) (copyCount required)-copyCount required G+
        ((b : ℝ)*(n*p^2)/(triangles G).card)*copyCount required G|+
        |((b : ℝ)*(lam-(n*p^2)/(triangles G).card))*copyCount required G| := by
      convert abs_add_le (pmfMean (step G) (copyCount required)-copyCount required G+
        ((b : ℝ)*(n*p^2)/(triangles G).card)*copyCount required G)
        (((b : ℝ)*(lam-(n*p^2)/(triangles G).card))*copyCount required G) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      dsimp only [lam]
      ring
    _ ≤ (2*(b : ℝ)*η*lam+2*(b : ℝ)^2*lam/((n : ℝ)*p^2))*copyCount required G+
        (b : ℝ)*(2*η*lam)*copyCount required G := by
      apply add_le_add (hd.trans (mul_le_mul_of_nonneg_right hcoef hX))
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg b),abs_sub_comm,
        abs_of_nonneg hX]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr.1 (Nat.cast_nonneg b)) hX
    _ = _ := by dsimp [lam]; ring

lemma relative_power_drift_bound {X Y s t r a B : ℝ} {b : ℕ}
    (hX : 0 ≤ X) (hs : 0 < s) (ht : 0 < t) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hscale : t = s*(1-r)^b) (hratio : s ≤ 2*t) (hcap : X ≤ B*s)
    (ha : 0 ≤ a) (h : |Y-X+(b : ℝ)*r*X| ≤ a*X) :
    |Y/t-X/s| ≤ 2*B*(a+(b : ℝ)^2*r^2) := by
  have hpow := power_euler_error b hr hr1
  have he : Y/t-X/s = ((Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r))/t := by
    apply (eq_div_iff ht.ne').mpr
    field_simp [hs.ne']
    rw [hscale]
    ring
  have hnum : |(Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r)| ≤
      (a+(b : ℝ)^2*r^2)*X := by
    calc
      _ ≤ |Y-X+(b : ℝ)*r*X|+|X*((1-r)^b-1+(b : ℝ)*r)| := abs_sub _ _
      _ ≤ a*X+X*((b : ℝ)^2*r^2) := by
        apply add_le_add h
        rw [abs_mul,abs_of_nonneg hX]
        exact mul_le_mul_of_nonneg_left hpow hX
      _ = _ := by ring
  have hB : 0 ≤ B := (mul_nonneg_iff_of_pos_right hs).mp (hX.trans hcap)
  have hX' : X ≤ 2*B*t := hcap.trans (by nlinarith only [mul_le_mul_of_nonneg_left hratio hB])
  rw [he,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  exact hnum.trans (by nlinarith only [mul_le_mul_of_nonneg_left hX' (show 0 ≤ a+(b : ℝ)^2*r^2 by positivity)])

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

theorem early_relative_drift_bound {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (a b : ℕ) (hsize : ∀ x, (required x).card = b)
    (η : ℝ) (hn : 0 < n) (hp : 1/(n : ℝ) ≤ prefixDensity n)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hreg : ∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1))
    (j : ℕ) (hj : j ≤ prefixTime n) (ω : History (Graph n) (prefixTime n))
    (hsafe : ∀ i < j, densityEdgeSafe n (earlyDensity n i) η (ω (historyIndex (prefixTime n) i)))
    (hcap : ∀ i < j, copyCount required (ω (historyIndex (prefixTime n) i)) ≤
      2*earlyTemplateScale a b n i) :
    |copyCount required (ω (historyIndex (prefixTime n) j))/earlyTemplateScale a b n j-
      copyCount required (ω (historyIndex (prefixTime n) 0))/earlyTemplateScale a b n 0-
      historyNoise (fun _ => step) (fun i G => copyCount required G/earlyTemplateScale a b n i)
        (prefixTime n) j ω| ≤
      16*(b : ℝ)*η*Real.log n+4*(b : ℝ)^2/prefixD n+
        24*(b : ℝ)^2*Real.log n/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let p := earlyDensity n
  let h : ℝ := 6/(n : ℝ)^2
  let lam : ℕ → ℝ := fun i => h/p i
  have hpos : ∀ i ≤ prefixTime n, 0 < p i := fun i hi => early_density_positive hn hp hi
  have hstep : ∀ i, p i = p (i+1)+h := fun i => earlyDensity_succ n i
  have hspos : ∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i := by
    intro i hi
    dsimp [earlyTemplateScale]
    have := hpos i hi
    positivity
  have hsingle (i : ℕ) (hi : i < j) :
      |pmfMean (step (ω (historyIndex (prefixTime n) i))) (copyCount required)/
          earlyTemplateScale a b n (i+1)-
        copyCount required (ω (historyIndex (prefixTime n) i))/earlyTemplateScale a b n i| ≤
      4*(4*(b : ℝ)*η*lam i+2*(b : ℝ)^2*lam i/((n : ℝ)*p i^2)+(b : ℝ)^2*(lam i)^2) := by
    have hiT : i < prefixTime n := hi.trans_le hj
    have hp0 := hpos i hiT.le
    have hp1 := hpos (i+1) (by omega)
    have hl : 0 ≤ lam i := by dsimp [lam,h]; positivity
    have hl1 : lam i ≤ 1 := by
      apply (div_le_iff₀ hp0).mpr
      have hh := hstep i
      linarith only [hh,hp1]
    have hscale : earlyTemplateScale a b n (i+1) = earlyTemplateScale a b n i*(1-lam i)^b := by
      have he : p (i+1) = p i*(1-lam i) := by dsimp [lam]; field_simp; linarith only [hstep i]
      change (n : ℝ)^a*p (i+1)^b = ((n : ℝ)^a*p i^b)*(1-lam i)^b
      rw [he,mul_pow]; ring
    have hd := densityEdgeSafe_copy_euler_error required b hsize hn hp0 hη hη1 (hsafe i hi)
    simpa only [lam,h,show (2 : ℝ)*2 = 4 by norm_num] using relative_power_drift_bound (copyCount_nonneg _ _)
      (hspos i hiT.le) (hspos (i+1) (by omega)) hl hl1 hscale (hreg i hiT) (hcap i hi)
      (by positivity) hd
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
  rw [history_relative_drift_sum _ _ _ _ _ hj]
  calc
    _ ≤ ∑ i ∈ Finset.range j,
        |pmfMean (step (ω (historyIndex (prefixTime n) i))) (copyCount required)/earlyTemplateScale a b n (i+1)-
          copyCount required (ω (historyIndex (prefixTime n) i))/earlyTemplateScale a b n i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j,
        4*(4*(b : ℝ)*η*lam i+2*(b : ℝ)^2*lam i/((n : ℝ)*p i^2)+(b : ℝ)^2*(lam i)^2) :=
      Finset.sum_le_sum (fun i hi => hsingle i (Finset.mem_range.mp hi))
    _ = 16*(b : ℝ)*η*(∑ i ∈ Finset.range j, lam i)+
        8*(b : ℝ)^2*(∑ i ∈ Finset.range j, lam i/((n : ℝ)*p i^2))+
        4*(b : ℝ)^2*(∑ i ∈ Finset.range j, (lam i)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16*(b : ℝ)*η by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hlD (show 0 ≤ 8*(b : ℝ)^2 by positivity)
      have h₃ := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*(b : ℝ)^2 by positivity)
      simp only [div_eq_mul_inv,mul_inv_rev] at h₂ h₃ ⊢
      norm_num only [invOf_eq_inv,inv_div,inv_one] at h₂
      nlinarith only [h₁,h₂,h₃]

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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_WheelSpoke
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
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

lemma cycleNext_twice_ne {j : ℕ} (hj : 3 ≤ j) (i : Fin j) :
    cycleNext (cycleNext i) ≠ i := by
  intro h
  have hh := congrArg Fin.val h
  have h1 := cycleNext_val i
  have h2 := cycleNext_val (cycleNext i)
  split_ifs at h1 h2 <;> omega

lemma wheelSpoke_injective (j : ℕ) : Function.Injective (@wheelSpoke j) := by
  intro i k h
  have hh : i.succ ∈ wheelSpoke k := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [wheelSpoke,Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with hh | hh
  · exact (Fin.succ_ne_zero i hh).elim
  · exact Fin.succ_injective _ hh

lemma wheelRim_injective {j : ℕ} (hj : 3 ≤ j) : Function.Injective (@wheelRim j) := by
  intro i k h
  have ha : i.succ ∈ wheelRim k := h ▸ Finset.mem_insert_self _ _
  have hb : (cycleNext i).succ ∈ wheelRim k := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [wheelRim,Finset.mem_insert,Finset.mem_singleton,Fin.succ_inj] at ha hb
  rcases ha with rfl | ha
  · rfl
  rcases hb with hb | hb
  · have hh : cycleNext (cycleNext k) = k := by rw [← ha,hb]
    exact (cycleNext_twice_ne hj k hh).elim
  · exact ((cycleNext_ne (by omega) i) (hb.trans ha.symm)).elim

lemma wheelSpoke_ne_rim {j : ℕ} (i k : Fin j) : wheelSpoke i ≠ wheelRim k := by
  intro h
  have hh : (0 : Fin (j+1)) ∈ wheelRim k := h ▸ Finset.mem_insert_self _ _
  simp only [wheelRim,Finset.mem_insert,Finset.mem_singleton,(Ne.symm (Fin.succ_ne_zero _)),or_self] at hh

@[simp] lemma wheelTemplate_edges_card (j : ℕ) (hj : 3 ≤ j) :
    (wheelTemplate j hj).edges.card = 2*j := by
  have hd : Disjoint (Finset.univ.image (@wheelSpoke j)) (Finset.univ.image (@wheelRim j)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hf
    exact wheelSpoke_ne_rim i k hk.symm
  rw [wheelTemplate,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (wheelSpoke_injective j),
    Finset.card_image_of_injective _ (wheelRim_injective hj)]
  simp
  omega

lemma wheelTemplate_balanced (j : ℕ) (hj : 3 ≤ j) : RootedTwoBalanced (wheelTemplate j hj) := by
  intro J hJ
  have h0 : (0 : Fin (j+1)) ∈ J := hJ (Finset.mem_singleton_self _)
  let A := Finset.univ.filter (fun i : Fin j => i.succ ∈ J)
  have hsub : ((wheelTemplate j hj).edges.filter (· ⊆ J)) ⊆
      A.image wheelSpoke ∪ A.image wheelRim := by
    intro e he
    obtain ⟨he,hsub⟩ := Finset.mem_filter.mp he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩,rfl⟩)
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hsub (Finset.mem_insert_self _ _)⟩,rfl⟩)
  have hA : A.card ≤ (J.erase 0).card := by
    apply Finset.card_le_card_of_injOn Fin.succ
    · intro i hi
      exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i,(Finset.mem_filter.mp hi).2⟩
    · intro a _ b _ hab
      exact Fin.succ_injective _ hab
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := Finset.card_image_le (s := A) (f := wheelSpoke)
  have h2 := Finset.card_image_le (s := A) (f := wheelRim)
  rw [Finset.card_erase_of_mem h0] at hA
  rw [wheelTemplate_roots_card]
  omega

lemma wheelRooted_zero {j n : ℕ} (hj : 3 ≤ j) (u : Fin n)
    (φ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u)) : φ.val 0 = u :=
  φ.property ⟨0,Finset.mem_singleton_self _⟩

lemma wheel_image_subset {j n : ℕ} (hj : 3 ≤ j) (u : Fin n)
    (φ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u)) (G : Graph n) :
    imageEdges (wheelTemplate j hj) φ.val ⊆ G ↔
      ∀ i, {u,wheelRestrict hj u φ i} ∈ G ∧
        {wheelRestrict hj u φ i,wheelRestrict hj u φ (cycleNext i)} ∈ G := by
  have hs (i : Fin j) : (wheelSpoke i).map φ.val = {u,wheelRestrict hj u φ i} := by
    simp [wheelSpoke,wheelRestrict,wheelRooted_zero hj u φ]
  have hr (i : Fin j) : (wheelRim i).map φ.val =
      {wheelRestrict hj u φ i,wheelRestrict hj u φ (cycleNext i)} := by simp [wheelRim,wheelRestrict]
  constructor
  · intro h i
    constructor
    · rw [← hs]
      exact h (Finset.mem_image.mpr ⟨wheelSpoke i,Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩),rfl⟩)
    · rw [← hr]
      exact h (Finset.mem_image.mpr ⟨wheelRim i,Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩),rfl⟩)
  · intro h e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
      rw [hs]; exact (h i).1
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
      rw [hr]; exact (h i).2

lemma wheelRestrict_injective {j n : ℕ} (hj : 3 ≤ j) (u : Fin n) :
    Function.Injective (wheelRestrict hj u) := by
  intro φ χ h
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact (wheelRooted_zero hj u φ).trans (wheelRooted_zero hj u χ).symm
  · exact congrArg (fun f : Fin j ↪ Fin n => f i) h

lemma wheelRestrict_surj {j n : ℕ} (hj : 3 ≤ j) (u : Fin n) (φ : Fin j ↪ Fin n)
    (havoid : ∀ i, φ i ≠ u) :
    ∃ χ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u), wheelRestrict hj u χ = φ := by
  let f : Fin (j+1) → Fin n := Fin.cases u φ
  have hf : Function.Injective f := by
    intro a b h
    revert h
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro _; rfl
      · intro h; exact (havoid b h.symm).elim
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro h; exact (havoid a h).elim
      · intro h; exact congrArg Fin.succ (φ.injective h)
  let χ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u) :=
    ⟨⟨f,hf⟩,by intro v; have hv : v.val = 0 := Finset.mem_singleton.mp v.property; change f v.val = u; rw [hv]; rfl⟩
  exact ⟨χ,by ext i; rfl⟩

theorem wheel_rootedCount {j n : ℕ} (hj : 3 ≤ j) (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    rootedCount (wheelTemplate j hj) (wheelRoot hj u) G = linkCycleCount j G u := by
  let A := Finset.univ.filter (fun φ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u) =>
    imageEdges (wheelTemplate j hj) φ.val ⊆ G)
  let B := Finset.univ.filter (fun φ : Fin j ↪ Fin n =>
    ∀ i, {u,φ i} ∈ G ∧ {φ i,φ (cycleNext i)} ∈ G)
  have hA : rootedCount (wheelTemplate j hj) (wheelRoot hj u) G = (A.card : ℝ) := by
    simp [rootedCount,copyCount,intact,A]
  have hB : linkCycleCount j G u = (B.card : ℝ) := by
    simp [linkCycleCount,B,Finset.sum_boole]
  rw [hA,hB]
  congr 1
  apply Finset.card_bij (fun φ _ => wheelRestrict hj u φ)
  · intro φ hφ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(wheel_image_subset hj u φ G).mp (Finset.mem_filter.mp hφ).2⟩
  · intro φ _ χ _ h
    exact wheelRestrict_injective hj u h
  · intro φ hφ
    have hp := (Finset.mem_filter.mp hφ).2
    have hav : ∀ i, φ i ≠ u := by
      intro i he
      have hh := mem_completeGraph.mp (hG (hp i).1)
      simp [he] at hh
    obtain ⟨χ,hχ⟩ := wheelRestrict_surj hj u φ hav
    refine ⟨χ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hχ⟩
    exact (wheel_image_subset hj u χ G).mpr (hχ.symm ▸ hp)

@[simp] theorem wheel_rootedScaling {j n : ℕ} (hj : 3 ≤ j) (p : ℝ) :
    rootedScaling (wheelTemplate j hj) n p = ((n : ℝ)*p^2)^j := by
  simp only [rootedScaling,wheelTemplate_roots_card,wheelTemplate_edges_card,Nat.add_sub_cancel,
    mul_pow,← pow_mul]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_BalancedJump
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

lemma earlyTemplateScale_uniform_regular (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ a ≤ H, ∀ b ≤ H^2,
      (∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale a b n (i+1) ≤ earlyTemplateScale a b n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1)) ∧
      relativeScaleBudget (earlyTemplateScale a b n) (prefixTime n) ≤ 2*(b : ℝ)*Real.log n := by
  have hh : ∀ z : Fin (H+1) × Fin (H^2+1), ∀ᶠ n : ℕ in atTop,
      (∀ i ≤ prefixTime n, 0 < earlyTemplateScale z.1.val z.2.val n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale z.1.val z.2.val n (i+1) ≤ earlyTemplateScale z.1.val z.2.val n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale z.1.val z.2.val n i ≤ 2*earlyTemplateScale z.1.val z.2.val n (i+1)) ∧
      relativeScaleBudget (earlyTemplateScale z.1.val z.2.val n) (prefixTime n) ≤ 2*(z.2.val : ℝ)*Real.log n := by
    intro z
    filter_upwards [earlyTemplateScale_regular z.1.val z.2.val,
      earlyTemplateScale_log_budget z.1.val z.2.val] with n hr hb
    exact ⟨hr.1,hr.2.1,hr.2.2,hb⟩
  filter_upwards [Filter.eventually_all.mpr hh] with n hn
  intro a ha b hb
  exact hn (⟨a,by omega⟩,⟨b,by omega⟩)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixBalancedNoise
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

lemma balanced_closure_budget (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeRadius n ∧ prefixEdgeRadius n ≤ 1/2 ∧
    prefixWheelRadius n ≤ 1 ∧
    (2 : ℝ)^(H^2)*(2*(H : ℝ)^2)/(n : ℝ)+codegreeNoiseRadius n+
      (16*(H : ℝ)^2*prefixEdgeRadius n*Real.log n+4*((H : ℝ)^2)^2/prefixD n+
        24*((H : ℝ)^2)^2*Real.log n/(n : ℝ)) ≤ prefixWheelRadius n/2 := by
  let C : ℝ := 2^(H^2)*(2*(H : ℝ)^2)+1+16*(H : ℝ)^2+28*((H : ℝ)^2)^2
  have hC : 0 < C := by dsimp [C]; positivity
  have hrad : Tendsto prefixEdgeRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-1/40000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,prefixEdgeRadius,neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/40000)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/80000)
      (by positivity : 0 < 1/(2*C)),prefixD_eventual_envelope,
    hrad.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1 : ℕ)] with n hlog hD hrad hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hη : 0 ≤ prefixEdgeRadius n := Real.rpow_nonneg hn0.le _
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hηlog : C*(1+Real.log (n : ℝ))*prefixEdgeRadius n ≤ prefixWheelRadius n/2 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (show 1+Real.log (n : ℝ) ≤ 1/(2*C)*(n : ℝ)^(1/80000 : ℝ) by
        simpa only [prefixTemplateFactor,Real.rpow_one] using hlog) hC.le) hη
    have he : C*(1/(2*C)*(n : ℝ)^(1/80000 : ℝ))*prefixEdgeRadius n = prefixWheelRadius n/2 := by
      unfold prefixEdgeRadius prefixWheelRadius
      calc
        _ = (C/(2*C))*((n : ℝ)^(1/80000 : ℝ)*(n : ℝ)^(-1/40000 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hn0]; norm_num; field_simp
    exact hh.trans_eq he
  have hnoise : codegreeNoiseRadius n ≤ prefixEdgeRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hinv : 1/(n : ℝ) ≤ prefixEdgeRadius n := by
    simpa only [Real.rpow_neg_one,one_div,prefixEdgeRadius] using
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -1/40000))
  have hDinv : 1/prefixD n ≤ prefixEdgeRadius n := by
    apply (div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hn0 _) hD.1).trans
    rw [one_div,← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  refine ⟨hη,hrad,Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num),?_⟩
  have hinit := mul_le_mul_of_nonneg_left hinv (show 0 ≤ (2 : ℝ)^(H^2)*(2*(H : ℝ)^2) by positivity)
  have hdisc := mul_le_mul_of_nonneg_left hDinv (show 0 ≤ 4*((H : ℝ)^2)^2 by positivity)
  have hgrid := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 24*((H : ℝ)^2)^2*Real.log n by positivity)
  have hηL : prefixEdgeRadius n ≤ (1+Real.log (n : ℝ))*prefixEdgeRadius n := by nlinarith only [mul_nonneg hl hη]
  have hmain := mul_le_mul_of_nonneg_left hηL
    (show 0 ≤ (2 : ℝ)^(H^2)*(2*(H : ℝ)^2)+1+4*((H : ℝ)^2)^2 by positivity)
  dsimp only [C] at hηlog
  simp only [div_eq_mul_inv,one_mul] at hinit hdisc hgrid ⊢
  nlinarith only [hinit,hdisc,hgrid,hnoise,hmain,hηlog,
    mul_nonneg (show 0 ≤ 16*(H : ℝ)^2+24*((H : ℝ)^2)^2 by positivity) hη]

theorem prefix_balanced_tracking (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper H n ω → PrefixBalancedNoise H n ω →
    ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ k ≤ H, ∀ T : RootedTemplate k, RootedTwoBalanced T →
    ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
      |rootedCount T ψ (ω (historyIndex (prefixTime n) j))/rootedScaling T n (earlyDensity n j)-1| ≤
        prefixWheelRadius n/2 := by
  filter_upwards [balanced_closure_budget H,earlyTemplateScale_uniform_regular H,
    prefixDensity_eventually_inverse_lower,prefixD_eventual_envelope,
    eventually_ge_atTop H,eventually_ge_atTop (2 : ℕ)] with n hbud hreg hp hD hnH hn
  intro ω hω hupper hnoise j hj hsafe k hk T hT ψ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hb : T.edges.card ≤ H^2 := (rootedTemplate_edges_card_le_sq T).trans (Nat.pow_le_pow_left hk 2)
  have hbR : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by exact_mod_cast hb
  have hs := hreg (k-T.roots.card) ((Nat.sub_le _ _).trans hk) T.edges.card hb
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by simpa only [PMF.mem_support_pure_iff] using hi
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hcap : ∀ i < j, rootedCount T ψ (ω (historyIndex (prefixTime n) i)) ≤
        2*earlyTemplateScale (k-T.roots.card) T.edges.card n i := by
      intro i hij
      have htracking := ih i hij (by omega) (fun l hl => hsafe l (hl.trans hij))
      have hbnd : rootedCount T ψ (ω (historyIndex (prefixTime n) i))/
          rootedScaling T n (earlyDensity n i) ≤ 2 := by
        have hh := (abs_le.mp htracking).2
        linarith only [hh,hbud.2.2.1]
      exact (div_le_iff₀ (hs.1 i (by omega))).mp hbnd
    have hloads : pastRelativeCopyLoadsSafe (fun φ : RootedInjection T ψ => imageEdges T φ.val)
        (balancedLoad H T n) (prefixTime n) j ω := by
      intro i hi
      have hij : i < j := lt_of_lt_of_le hi (Nat.min_le_left _ _)
      have hiT : i ≤ prefixTime n := by omega
      have hDi : 1 ≤ (n : ℝ)*earlyDensity n i^2 := by
        have hd := earlyCodegreeScale_ge_prefixD n i hiT (le_trans (by positivity) hp)
        have hh := Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 1/1000)
        exact hh.trans (hD.1.trans (by simpa only [earlyTemplateScale,pow_one] using hd))
      exact balanced_rooted_load_bound T hk hT ψ _ (hsafe i hij).1
        (early_density_positive (by omega) hp hiT) (earlyDensity_le_one n i) (by positivity) hDi
        (fun a ha U ξ => (hupper i hiT (fun l hl => hsafe l (hl.trans hij)) a ha U ξ).le)
    have hnse : |historyNoise (fun _ => step)
        (fun i G => rootedCount T ψ G/earlyTemplateScale (k-T.roots.card) T.edges.card n i)
          (prefixTime n) j ω| < codegreeNoiseRadius n := by
      exact lt_of_not_ge (fun hcross => hnoise k hk T ψ ⟨j,hj,hloads,hcap,hcross⟩)
    have hd := early_relative_drift_bound (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      (k-T.roots.card) T.edges.card (fun φ => imageEdges_card T φ.val)
      (prefixEdgeRadius n) (by omega) hp hbud.1 hbud.2.1 hs.2.2.1 j hj ω hsafe hcap
    have hinit := rootedCount_initial_uniform_error H hk hnH hn T ψ
    have he : earlyDensity n 0 = 1-1/(n : ℝ) := by simp [earlyDensity]
    rw [← he,← hi'] at hinit
    have htri := fun x y z : ℝ => (abs_add_le (x+y) z).trans
      (add_le_add (abs_add_le x y) le_rfl)
    have htri := htri
      (rootedCount T ψ (ω (historyIndex (prefixTime n) j))/rootedScaling T n (earlyDensity n j)-
        rootedCount T ψ (ω (historyIndex (prefixTime n) 0))/rootedScaling T n (earlyDensity n 0)-
        historyNoise (fun _ => step) (fun i G => rootedCount T ψ G/earlyTemplateScale (k-T.roots.card) T.edges.card n i)
          (prefixTime n) j ω)
      (historyNoise (fun _ => step) (fun i G => rootedCount T ψ G/earlyTemplateScale (k-T.roots.card) T.edges.card n i)
          (prefixTime n) j ω)
      (rootedCount T ψ (ω (historyIndex (prefixTime n) 0))/rootedScaling T n (earlyDensity n 0)-1)
    have hlarge : 16*(T.edges.card : ℝ)*prefixEdgeRadius n*Real.log n+4*(T.edges.card : ℝ)^2/prefixD n+
        24*(T.edges.card : ℝ)^2*Real.log n/(n : ℝ) ≤
        16*(H : ℝ)^2*prefixEdgeRadius n*Real.log n+4*((H : ℝ)^2)^2/prefixD n+
        24*((H : ℝ)^2)^2*Real.log n/(n : ℝ) := by
      have hdpos : 0 ≤ prefixD n := (Real.rpow_nonneg hn0.le _).trans hD.1
      gcongr
      exact hbud.1
    change |rootedCount T ψ (ω (historyIndex (prefixTime n) j))/rootedScaling T n (earlyDensity n j)-
      rootedCount T ψ (ω (historyIndex (prefixTime n) 0))/rootedScaling T n (earlyDensity n 0)-
        historyNoise (fun _ => step) (fun i G => rootedCount T ψ G/earlyTemplateScale (k-T.roots.card) T.edges.card n i)
          (prefixTime n) j ω| ≤ _ at hd
    have heq : ∀ x y z : ℝ, x-y-z+z+(y-1) = x-1 := by intros; ring
    rw [heq] at htri
    linarith only [htri,hd,hnse,hinit,hlarge,hbud.2.2.2]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_DensityGlobalSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Filter Classical

namespace SharpTerminalLeave

theorem prefix_degree_wheel_tracking : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    ∀ i ≤ prefixTime n,
    historyAlive (fun j => densityEdgeSafe n (earlyDensity n j) (prefixEdgeRadius n)) (prefixTime n) i ω →
    (∀ u : Fin n, |(currentDegree (ω (historyIndex (prefixTime n) i)) u : ℝ)/
      ((n : ℝ)*earlyDensity n i)-1| ≤ prefixWheelRadius n/2) ∧
    (∀ j, 3 ≤ j → j ≤ 8000 → ∀ u : Fin n,
      |linkCycleCount j (ω (historyIndex (prefixTime n) i)) u/
        ((n : ℝ)*earlyDensity n i^2)^j-1| ≤ prefixWheelRadius n/2) := by
  filter_upwards [prefix_balanced_tracking 8001] with n hn
  intro ω hω hu hnse i hi hs
  have hG : ω (historyIndex (prefixTime n) i) ⊆ completeGraph n := complete_history_valid ω hω i hi
  constructor
  · intro u
    have h := hn ω hω hu hnse i hi hs 2 (by decide) degreeTemplate degreeTemplate_balanced (degreeRoot u)
    rwa [degree_rootedCount _ hG,degree_rootedScaling] at h
  · intro j hj hj' u
    have h := hn ω hω hu hnse i hi hs (j+1) (by omega)
      (wheelTemplate j hj) (wheelTemplate_balanced j hj) (wheelRoot hj u)
    rwa [wheel_rootedCount hj _ hG,wheel_rootedScaling] at h

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_NormalizedTrackingAbsolute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Filter Classical

namespace SharpTerminalLeave

lemma normalized_tracking_absolute {X s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (h : |X/s-1| ≤ r/2) : |X-s| ≤ r*s := by
  rw [show X/s-1 = (X-s)/s by rw [sub_div,div_self hs.ne'],abs_div,abs_of_pos hs] at h
  exact ((div_le_iff₀ hs).mp h).trans (mul_le_mul_of_nonneg_right (by linarith only [hr]) hs.le)

theorem prefix_good_history_oai : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    GoodPrefixGraph n (1/80000) (3*(8001 : ℕ)+2 : ℕ) (ω (historyIndex (prefixTime n) (prefixTime n))) := by
  filter_upwards [prefix_present_edge_closure,prefix_all_pair_closure,prefix_degree_wheel_tracking,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (1 : ℕ)] with n hedge hpair hwheel hp hn
  intro ω hω hroot hbalanced htri hnoise
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hedges := hedge ω hω hroot hbalanced htri hnoise
  have halive : historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n))
      (prefixTime n) (prefixTime n) ω := fun i hi => hedges i hi.le
  have he := hedges (prefixTime n) le_rfl
  have hw := hwheel ω hω hroot hbalanced (prefixTime n) le_rfl halive
  have hc := hpair ω hω hroot hbalanced htri hnoise (prefixTime n) le_rfl
  have hpp : 0 < prefixDensity n := (div_pos zero_lt_one hnR).trans_le hp
  have hr : 0 ≤ prefixWheelRadius n := Real.rpow_nonneg hnR.le _
  have hdeg := mul_pos hnR hpp
  have hD : 0 < prefixD n := mul_pos hnR (sq_pos_of_pos hpp)
  refine ⟨he.1,?_,?_,?_,?_,?_⟩
  · simpa only [earlyDensity_prefix,prefixM] using he.2.1
  · intro u
    have hh := hw.1 u
    rw [earlyDensity_prefix] at hh
    simpa only [prefixWheelRadius,neg_div] using normalized_tracking_absolute hdeg hr hh
  · intro u v huv
    have hh := hc u v huv
    simp only [prefixNormalizedCodegree,earlyTemplateScale,pow_one,earlyDensity_prefix] at hh
    simpa only [prefixD,prefixWheelRadius,neg_div] using normalized_tracking_absolute hD hr hh
  · intro j hj hj' u
    have hh := hw.2 j hj hj' u
    rw [earlyDensity_prefix] at hh
    simpa only [prefixD,prefixWheelRadius,neg_div] using normalized_tracking_absolute (pow_pos hD j) hr hh
  · intro k hk T ψ
    have hh := (hroot (prefixTime n) le_rfl halive k hk T ψ).le
    rw [earlyDensity_prefix] at hh
    have hfac : (1+Real.log (n : ℝ))^(3*8001+2) = prefixTemplateFactor n (3*(8001 : ℕ)+2 : ℕ) := by
      simp only [prefixTemplateFactor,Real.rpow_natCast]
    rw [hfac] at hh
    have hfac0 : 0 ≤ prefixTemplateFactor n (3*(8001 : ℕ)+2 : ℕ) := Real.rpow_nonneg (by have := Real.log_nonneg hn1; linarith) _
    constructor
    · intro hlarge
      exact hh.trans (mul_le_mul_of_nonneg_left (rootedCompletionMax_large T hpp.le hlarge) hfac0)
    · intro hsmall
      exact hh.trans ((mul_le_mul_of_nonneg_left (rootedCompletionMax_small T hsmall) hfac0).trans_eq (mul_one _))

end SharpTerminalLeave
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpTerminalLeave.prefix_good_history_oai := @OAI.SharpTerminalLeave.prefix_good_history_oai
