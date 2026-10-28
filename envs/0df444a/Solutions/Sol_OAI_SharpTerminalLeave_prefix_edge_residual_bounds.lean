-- Prove2me | solution 1 for OAI.SharpTerminalLeave.prefix_edge_residual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:58:52.019732+00:00
-- url     : https://prove2.me/submissions/61b7ff92-96aa-4ebc-985a-dff5e2000c7c

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000

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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_ActiveL2Map
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

lemma activeL2_sq {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ) :
    (activeL2 s x)^2 = ∑ e ∈ s, (x e)^2 := by
  change ‖activeL2Map s x‖^2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [activeL2Map]

lemma activeLinf_coordinate {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {e : E} (he : e ∈ s) : |x e| ≤ activeLinf s x := by
  exact Seminorm.le_finset_sup_apply (p := fun e =>
    (normSeminorm ℝ ℝ).comp (LinearMap.proj e)) (x := x) he

lemma activeLinf_bound {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ e ∈ s, |x e| ≤ R) : activeLinf s x ≤ R := by
  exact Seminorm.finset_sup_apply_le hR hx

end SharpTerminalLeave
end
end

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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_StarInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U]

theorem starInclusion_mulVec (S : Finset E) (x : E → ℝ) :
    (starInclusion S)ᴴ *ᵥ x = fun e : S => x e.val := by
  ext e
  simp [starInclusion,Matrix.mulVec,dotProduct]

theorem extendStar_quadratic (S : Finset E) (M : Matrix S S ℝ) (x : E → ℝ) :
    x ⬝ᵥ (extendStar S M *ᵥ x) =
      (fun e : S => x e.val) ⬝ᵥ (M *ᵥ fun e : S => x e.val) := by
  rw [extendStar,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,starInclusion_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  ext e
  simp [starInclusion,Matrix.vecMul,dotProduct]

theorem matrix_quadratic_abs (M : Matrix E E ℝ) (x : E → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ ‖M‖ * ∑ e, (x e)^2 := by
  let y : EuclideanSpace ℝ E := WithLp.toLp 2 x
  let T := (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ)) M
  have heq : x ⬝ᵥ (M *ᵥ x) = inner ℝ y (T y) := by
    simp [T,y,Matrix.toEuclideanCLM_toLp,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      mul_comm]
  have hn : ‖y‖^2 = ∑ e, (x e)^2 := by
    simp [EuclideanSpace.norm_sq_eq,y,Real.norm_eq_abs]
  rw [heq]
  calc
    _ ≤ ‖y‖ * ‖T y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T‖ * ‖y‖) := mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
    _ = ‖M‖ * ∑ e, (x e)^2 := by
      rw [mul_left_comm,← pow_two,hn]
      exact congrArg (fun a : ℝ => a * ∑ e, (x e)^2) (Matrix.l2_opNorm_toEuclideanCLM M)

theorem hermitian_norm_le_of_quadratic (M : Matrix E E ℝ) (hM : M.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a)
    (hquad : ∀ x : E → ℝ, |x ⬝ᵥ (M *ᵥ x)| ≤ a * ∑ e, (x e)^2) : ‖M‖ ≤ a := by
  have hev : ∀ e, |hM.eigenvalues e| ≤ a := by
    intro e
    have h := hquad (hM.eigenvectorBasis e).ofLp
    have hn : ∑ i, ((hM.eigenvectorBasis e).ofLp i)^2 = 1 := by
      have hh := hM.eigenvectorBasis.norm_eq_one e
      have hs := EuclideanSpace.norm_sq_eq (hM.eigenvectorBasis e)
      simpa [hh,Real.norm_eq_abs] using hs.symm
    rw [hn,mul_one] at h
    simpa [hM.eigenvalues_eq e] using h
  conv_lhs => rw [hM.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg ha).mpr (fun e => hev e)

theorem sum_star_norm_bound (S : U → Finset E) (M : (u : U) → Matrix (S u) (S u) ℝ)
    (hM : ∀ u, (M u).IsHermitian) (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hlocal : ∀ u, ‖M u‖ ≤ ε)
    (hoverlap : ∀ e : E, ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) ≤ K) :
    ‖∑ u, extendStar (S u) (M u)‖ ≤ K*ε := by
  have hsym : (∑ u, extendStar (S u) (M u)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.sum_apply,star_sum]
    apply Finset.sum_congr rfl
    intro u _
    exact (Matrix.isHermitian_mul_mul_conjTranspose (starInclusion (S u)) (hM u)).apply i j
  apply hermitian_norm_le_of_quadratic _ hsym (K*ε) (mul_nonneg hK hε)
  intro x
  have hsum : x ⬝ᵥ ((∑ u, extendStar (S u) (M u)) *ᵥ x) =
      ∑ u, (fun e : S u => x e.val) ⬝ᵥ (M u *ᵥ fun e : S u => x e.val) := by
    simp only [Matrix.sum_mulVec,dotProduct_sum,extendStar_quadratic]
  have hcount : (∑ u, ∑ e : S u, (x e.val)^2) ≤ K * ∑ e, (x e)^2 := by
    have hrewrite : ∀ u, (∑ e : S u, (x e.val)^2) =
        ∑ e : E, if e ∈ S u then (x e)^2 else 0 := by
      intro u
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter fun e => e ∈ S u)
        (fun e => by simp only [Finset.mem_filter,Finset.mem_univ,true_and])
        (fun e => (x e)^2)).symm
    simp_rw [hrewrite]
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have heq : (∑ u : U, if e ∈ S u then (x e)^2 else 0) =
        ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) * (x e)^2 := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hoverlap e) (sq_nonneg _)
  rw [hsum]
  calc
    _ ≤ ∑ u, |(fun e : S u => x e.val) ⬝ᵥ (M u *ᵥ fun e : S u => x e.val)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, ε * ∑ e : S u, (x e.val)^2 := by
      apply Finset.sum_le_sum
      intro u _
      exact (matrix_quadratic_abs _ _).trans
        (mul_le_mul_of_nonneg_right (hlocal u) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = ε * (∑ u, ∑ e : S u, (x e.val)^2) := by rw [Finset.mul_sum]
    _ ≤ ε * (K * ∑ e, (x e)^2) := mul_le_mul_of_nonneg_left hcount hε
    _ = K * ε * ∑ e, (x e)^2 := by ring

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ReindexQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem reindex_quadratic (e : I ≃ J) (M : Matrix I I ℝ) (x : J → ℝ) :
    x ⬝ᵥ (Matrix.reindex e e M *ᵥ x) =
      (fun i => x (e i)) ⬝ᵥ (M *ᵥ fun i => x (e i)) := by
  simp only [dotProduct,Matrix.mulVec,Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]

theorem hermitian_reindex_norm_le (e : I ≃ J) (M : Matrix I I ℝ) (hM : M.IsHermitian) :
    ‖Matrix.reindex e e M‖ ≤ ‖M‖ := by
  apply hermitian_norm_le_of_quadratic _ ((Matrix.isHermitian_reindex_iff e).mpr hM)
    ‖M‖ (norm_nonneg _)
  intro x
  rw [reindex_quadratic]
  have h := matrix_quadratic_abs M (fun i => x (e i))
  rw [show (∑ i, (x (e i))^2) = ∑ j, (x j)^2 from Equiv.sum_comp e (fun j => (x j)^2)] at h
  exact h

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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_EdgeStar
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
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

theorem edgeStar_exact_overlap {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (e : G) :
    (Finset.univ.filter fun u => e ∈ edgeStar G u).card = 2 := by
  have he : (Finset.univ.filter fun u => e ∈ edgeStar G u) = e.val := by
    ext u
    simp
  rw [he]
  exact mem_completeGraph.mp (hG e.property)

open scoped Matrix.Norms.L2Operator in

theorem graph_star_error_norm {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : (u : Fin n) → Matrix (edgeStar G u) (edgeStar G u) ℝ)
    (hM : ∀ u, (M u).IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) (hlocal : ∀ u, ‖M u‖ ≤ ε) :
    ‖∑ u, extendStar (edgeStar G u) (M u)‖ ≤ 2*ε := by
  apply sum_star_norm_bound _ _ hM ε 2 hε (by norm_num) hlocal
  intro e
  rw [edgeStar_exact_overlap G hG e]
  norm_num

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_GraphEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

section RootExtension
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V)

variable {H G}

omit [DecidableEq A] [DecidableEq V] in
lemma mem_graphEmbeddings (f : A ↪ V) :
    f ∈ graphEmbeddings H G ↔ ∀ a b, H.Adj a b → G.Adj (f a) (f b) := by
  classical
  simp only [graphEmbeddings, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_rootedEmbeddingFiber (S : Finset A) (ψ : A → V) (f : A ↪ V) :
    f ∈ rootedEmbeddingFiber H G S ψ ↔
      f ∈ graphEmbeddings H G ∧ ∀ a ∈ S, f a = ψ a := by
  classical
  simp only [rootedEmbeddingFiber, Finset.mem_filter]

omit [Fintype A] in

lemma walk_crosses_finset {a b : A} (p : H.Walk a b) (S : Finset A)
    (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, H.Adj x y := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons a c b hac p ih =>
    by_cases hc : c ∈ S
    · exact ih hc hb
    · exact ⟨a, ha, c, hc, hac⟩

lemma connected_crosses_finset (hH : H.Preconnected) (S : Finset A)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    ∃ x ∈ S, ∃ y ∉ S, H.Adj x y := by
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hSc
  obtain ⟨p⟩ := hH a b
  exact walk_crosses_finset p S ha (Finset.mem_compl.mp hb)

lemma root_fiber_fix_one (S : Finset A) (ψ : A → V) (v : A) (hv : v ∉ S) (z : V) :
    ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)) =
      rootedEmbeddingFiber H G (insert v S) (Function.update ψ v z) := by
  classical
  ext f
  simp only [Finset.mem_filter, mem_rootedEmbeddingFiber]
  constructor
  · rintro ⟨⟨hf, hψ⟩, hz⟩
    refine ⟨hf, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa using hz
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem ha hv)]
      exact hψ a ha
  · rintro ⟨hf, hψ⟩
    refine ⟨⟨hf, ?_⟩, ?_⟩
    · intro a ha
      have hh := hψ a (Finset.mem_insert_of_mem ha)
      simpa [Function.update_of_ne (ne_of_mem_of_not_mem ha hv)] using hh
    · simpa using hψ v (Finset.mem_insert_self _ _)

variable [DecidableRel G.Adj]

theorem rootedEmbeddingFiber_le (hH : H.Preconnected) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (S : Finset A) (hS : S.Nonempty) (ψ : A → V) :
    (rootedEmbeddingFiber H G S ψ).card ≤ Δ ^ Sᶜ.card := by
  classical
  induction hm : Sᶜ.card using Nat.strong_induction_on generalizing S ψ with
  | h m ih =>
    rw [← hm]
    by_cases hzero : Sᶜ.card = 0
    · have hSuniv : S = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro a
        by_contra ha
        have : a ∈ Sᶜ := Finset.mem_compl.mpr ha
        rw [Finset.card_eq_zero.mp hzero] at this
        exact Finset.notMem_empty a this
      rw [hzero, pow_zero]
      apply Finset.card_le_one.mpr
      intro f hf g hg
      apply Function.Embedding.ext
      intro a
      have hf' := (mem_rootedEmbeddingFiber S ψ f).mp hf
      have hg' := (mem_rootedEmbeddingFiber S ψ g).mp hg
      rw [hf'.2 a (by simp [hSuniv]), hg'.2 a (by simp [hSuniv])]
    · have hSc : Sᶜ.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
      obtain ⟨u, hu, v, hv, huv⟩ := connected_crosses_finset hH S hS hSc
      let t : Finset V := Finset.univ.filter (G.Adj (ψ u))
      have ht : ∀ f ∈ rootedEmbeddingFiber H G S ψ, f v ∈ t := by
        intro f hf
        obtain ⟨hf, hr⟩ := (mem_rootedEmbeddingFiber S ψ f).mp hf
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hr u hu]
        exact (mem_graphEmbeddings f).mp hf u v huv
      have hcard : (insert v S)ᶜ.card + 1 = Sᶜ.card := by
        rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.mpr hv)]
        exact Nat.sub_add_cancel (Finset.card_pos.mpr hSc)
      have hfib : ∀ z ∈ t,
          ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)).card ≤
            Δ ^ (insert v S)ᶜ.card := by
        intro z _
        rw [root_fiber_fix_one S ψ v hv z]
        exact ih (insert v S)ᶜ.card (by omega) (insert v S)
          (Finset.insert_nonempty _ _) (Function.update ψ v z) rfl
      calc
        _ = ∑ z ∈ t, ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)).card :=
          Finset.card_eq_sum_card_fiberwise ht
        _ ≤ ∑ _z ∈ t, Δ ^ (insert v S)ᶜ.card := Finset.sum_le_sum hfib
        _ = t.card * Δ ^ (insert v S)ᶜ.card := by simp
        _ ≤ Δ * Δ ^ (insert v S)ᶜ.card := Nat.mul_le_mul_right _ (hΔ (ψ u))
        _ = Δ ^ Sᶜ.card := by rw [← hcard, pow_succ']

end RootExtension
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LinkSimpleGraph
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

theorem cycleNext_eq_add_one {j : ℕ} (i : Fin (j+2)) : cycleNext i = i + 1 := by
  apply Fin.ext
  simp [cycleNext, Fin.add_def]

theorem cycleGraph_adj_next {j : ℕ} (i k : Fin (j+2)) :
    (SimpleGraph.cycleGraph (j+2)).Adj i k ↔ i = cycleNext k ∨ k = cycleNext i := by
  rw [SimpleGraph.cycleGraph_adj]
  simp only [cycleNext_eq_add_one, sub_eq_iff_eq_add, add_comm]

theorem link_neighbor_map {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) :
    (Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).map
      (Function.Embedding.subtype _) = commonNeighbors G u v.val := by
  ext w
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    linkSimpleGraph_adj, mem_commonNeighbors, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(Finset.mem_filter.mp x.property).2,hx⟩
  · rintro ⟨hu,hv⟩
    exact ⟨⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩,hv,rfl⟩

theorem link_degree_eq {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) :
    (Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card = currentCodegree G u v.val := by
  rw [← Finset.card_map (Function.Embedding.subtype _), link_neighbor_map]
  rfl

theorem linkCycleCount_eq_graphEmbeddings {n j : ℕ} (G : Graph n)
    (hG : G ⊆ completeGraph n) (u : Fin n) :
    linkCycleCount (j+2) G u =
      ((graphEmbeddings (SimpleGraph.cycleGraph (j+2)) (linkSimpleGraph G hG u)).card : ℝ) := by
  classical
  let S : Finset (Fin (j+2) ↪ Fin n) := Finset.univ.filter (fun φ =>
    ∀ i, {u,φ i} ∈ G ∧ {φ i,φ (cycleNext i)} ∈ G)
  have heq : linkCycleCount (j+2) G u = (S.card : ℝ) := by
    simp [linkCycleCount,S,Finset.sum_boole]
  rw [heq]
  congr 1
  symm
  apply Finset.card_bij (fun (f : Fin (j+2) ↪ neighbors G u) _ =>
    f.trans (Function.Embedding.subtype _))
  · intro f hf
    have hf' := (mem_graphEmbeddings f).mp hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun i => ⟨?_,?_⟩⟩
    · exact (Finset.mem_filter.mp (f i).property).2
    · exact hf' i (cycleNext i) ((cycleGraph_adj_next i (cycleNext i)).mpr (Or.inr rfl))
  · intro f hf g hg hfg
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun (e : Fin (j+2) ↪ Fin n) => e i) hfg
  · intro φ hφ
    have hφ' := (Finset.mem_filter.mp hφ).2
    let f : Fin (j+2) ↪ neighbors G u :=
      ⟨fun i => ⟨φ i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hφ' i).1⟩⟩,
        fun a b h => φ.injective (congrArg Subtype.val h)⟩
    refine ⟨f,?_,?_⟩
    · apply (mem_graphEmbeddings f).mpr
      intro a b hab
      rcases (cycleGraph_adj_next a b).mp hab with hab | hab
      · change {φ a,φ b} ∈ G
        rw [hab,Finset.pair_comm]
        exact (hφ' b).2
      · change {φ a,φ b} ∈ G
        rw [hab]
        exact (hφ' a).2
    · rfl

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EigenProjector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_trace_pow (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (r : ℕ) :
    (A ^ r).trace = ∑ i, hA.eigenvalues i ^ r := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

theorem eigenvalue_tail_of_trace (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (i₀ : ι) (r : ℕ) (hr : Even r) (hr0 : r ≠ 0) (a θ : ℝ)
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hlead : a ≤ hA.eigenvalues i₀)
    (htrace : (A ^ r).trace ≤ a ^ r + θ ^ r) :
    ∀ i, i ≠ i₀ → |hA.eigenvalues i| ≤ θ := by
  intro i hi
  have heig : ∀ j, 0 ≤ hA.eigenvalues j ^ r := fun j => hr.pow_nonneg _
  have hsum : hA.eigenvalues i₀ ^ r + hA.eigenvalues i ^ r ≤
      ∑ j, hA.eigenvalues j ^ r := by
    calc
      _ = ∑ j ∈ ({i₀, i} : Finset ι), hA.eigenvalues j ^ r := by
        simp [Ne.symm hi]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => heig j)
  have hpow : |hA.eigenvalues i| ^ r ≤ θ ^ r := by
    rw [hr.pow_abs]
    have hlead' := pow_le_pow_left₀ ha hlead r
    rw [hermitian_trace_pow A hA r] at htrace
    linarith
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hθ hr0).mp hpow

theorem eigenProjector_approximation (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (i₀ : ι) (θ : ℝ) (hθ : 0 ≤ θ)
    (htail : ∀ i, i ≠ i₀ → |hA.eigenvalues i| ≤ θ) :
    ‖A - hA.eigenvalues i₀ • eigenProjector A hA i₀‖ ≤ θ := by
  have heq : A - hA.eigenvalues i₀ • eigenProjector A hA i₀ =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => if i = i₀ then 0 else hA.eigenvalues i)) := by
    conv_lhs => lhs; rw [hA.spectral_theorem]
    rw [eigenProjector, ← map_smul, ← map_sub, ← Matrix.diagonal_smul,
      Matrix.diagonal_sub]
    congr 2
    ext i
    by_cases hi : i = i₀ <;> simp [hi]
  rw [heq, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hθ).mpr
  intro i
  by_cases hi : i = i₀
  · simp [hi, hθ]
  · simpa [hi] using htail i hi

end SharpTerminalLeave

open scoped BigOperators NNReal
open Matrix

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EigenvalueAbsRowsum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators NNReal
open Matrix

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open scoped Matrix.Norms.Operator in

theorem eigenvalue_abs_le_rowsum (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) (hrow : ∀ i, ∑ j, |A i j| ≤ a) (i : ι) :
    |hA.eigenvalues i| ≤ a := by
  have hnorm : ‖A‖ ≤ a := by
    rw [Matrix.linfty_opNorm_def]
    have hh : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (⟨a, ha⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i _
      apply NNReal.coe_le_coe.mp
      change (↑(∑ j, ‖A i j‖₊) : ℝ) ≤ a
      simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using hrow i
    exact_mod_cast hh
  exact (spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)).trans hnorm

omit [Nonempty ι] in

theorem hermitian_upper_posSemidef (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a : ℝ) (ha : ∀ i, hA.eigenvalues i ≤ a) : (a • 1 - A).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => a - hA.eigenvalues i)).PosSemidef := by
    exact Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (ha i))
  have heq : a • 1 - A =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => a - hA.eigenvalues i)) := by
    rw [← Matrix.diagonal_sub]
    change _ = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun _ => a) - Matrix.diagonal hA.eigenvalues)
    rw [map_sub]
    have hspec : A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal hA.eigenvalues) := hA.spectral_theorem
    rw [← hspec]
    congr 1
    have hdia : Matrix.diagonal (fun _ : ι => a) = a • (1 : Matrix ι ι ℝ) := by
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    rw [hdia, map_smul, map_one]
  rw [heq, Unitary.conjStarAlgAut_apply]
  exact hd.mul_mul_conjTranspose_same _

theorem exists_leading_of_rowsums (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a b : ℝ) (hb : 0 ≤ b)
    (hlower : ∀ i, a ≤ ∑ j, A i j) (hupper : ∀ i, ∑ j, |A i j| ≤ b) :
    ∃ i₀, a ≤ hA.eigenvalues i₀ ∧ |hA.eigenvalues i₀| ≤ b ∧
      ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀ := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues
    Finset.univ_nonempty
  have hm : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀ := fun i => hi₀ i (Finset.mem_univ i)
  refine ⟨i₀, ?_, eigenvalue_abs_le_rowsum A hA b hb hupper i₀, hm⟩
  have hpos := (hermitian_upper_posSemidef A hA (hA.eigenvalues i₀) hm).dotProduct_mulVec_nonneg (fun _ => 1)
  have heval : (star (fun _ : ι => (1 : ℝ))) ⬝ᵥ
      ((hA.eigenvalues i₀ • 1 - A) *ᵥ fun _ => 1) =
      (Fintype.card ι : ℝ) * hA.eigenvalues i₀ - ∑ i, ∑ j, A i j := by
    simp [dotProduct, Finset.sum_sub_distrib, Matrix.mulVec, Matrix.one_apply]
  rw [heval] at hpos
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlower i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hl
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith

end SharpTerminalLeave

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_UnitLineRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace

namespace SharpTerminalLeave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_line_remainder (v j : E) (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) :
    ‖inner ℝ v j • v‖ ≤ 1 ∧
    ‖j - inner ℝ v j • v‖ ^ 2 = 1 - (inner ℝ v j) ^ 2 ∧
    ‖j - inner ℝ v j • v‖ ≤ 1 := by
  have hb : |inner ℝ v j| ≤ 1 := by
    simpa only [hv, hj, one_mul] using abs_real_inner_le_norm v j
  have hs : ‖j - inner ℝ v j • v‖ ^ 2 = 1 - (inner ℝ v j) ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm j v, norm_smul,
      Real.norm_eq_abs, hv, hj]
    rw [mul_one, one_pow, sq_abs]
    ring
  refine ⟨by simpa [norm_smul, hv, Real.norm_eq_abs] using hb, hs, ?_⟩
  have hn := norm_nonneg (j - inner ℝ v j • v)
  nlinarith [sq_nonneg (inner ℝ v j)]

theorem unit_projector_difference (v j : E) (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) :
    ‖rankOne ℝ j j - rankOne ℝ v v‖ ≤ 3 * ‖j - rankOne ℝ v v j‖ := by
  let a : ℝ := inner ℝ v j
  let p : E := a • v
  have hp := unit_line_remainder v j hv hj
  change ‖p‖ ≤ 1 ∧ ‖j - p‖ ^ 2 = 1 - a ^ 2 ∧ ‖j - p‖ ≤ 1 at hp
  have heq : rankOne ℝ j j - rankOne ℝ v v =
      rankOne ℝ (j - p) j + rankOne ℝ p (j - p) +
      (a ^ 2 - 1) • rankOne ℝ v v := by
    ext x
    simp only [add_apply, sub_apply,
      smul_apply, rankOne_apply, inner_sub_left,
      real_inner_smul_left, p]
    simp only [smul_sub, smul_smul]
    module
  have habs : |a ^ 2 - 1| = ‖j - p‖ ^ 2 := by
    have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖j - p‖, hp.2.1]
    rw [abs_of_nonpos (sub_nonpos.mpr ha)]
    linarith [hp.2.1]
  change ‖rankOne ℝ j j - rankOne ℝ v v‖ ≤ 3 * ‖j - p‖
  rw [heq]
  calc
    _ ≤ ‖rankOne ℝ (j - p) j‖ + ‖rankOne ℝ p (j - p)‖ +
        ‖(a ^ 2 - 1) • rankOne ℝ v v‖ := norm_add₃_le
    _ = ‖j - p‖ + ‖p‖ * ‖j - p‖ + ‖j - p‖ ^ 2 := by
      simp only [norm_rankOne, norm_smul, Real.norm_eq_abs, hj, hv, mul_one, habs]
    _ ≤ 3 * ‖j - p‖ := by
      have hmul := mul_le_mul_of_nonneg_right hp.1 (norm_nonneg (j - p))
      have hsq := mul_le_mul_of_nonneg_left hp.2.2 (norm_nonneg (j - p))
      nlinarith

theorem projector_transfer (B : E →L[ℝ] E) (v j : E)
    (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) (lam θ δ ε : ℝ)
    (hB : ‖B - lam • rankOne ℝ v v‖ ≤ θ)
    (hlam : |lam - 1| ≤ δ) (hjB : ‖B j - j‖ ≤ ε) :
    ‖B - rankOne ℝ j j‖ ≤ 4 * (θ + δ) + 3 * ε := by
  let P : E →L[ℝ] E := rankOne ℝ v v
  have hP : ‖P‖ = 1 := by simp [P, norm_rankOne, hv]
  have hBP : ‖B - P‖ ≤ θ + δ := by
    calc
      _ = ‖(B - lam • P) + (lam - 1) • P‖ := by congr 1; module
      _ ≤ ‖B - lam • P‖ + ‖(lam - 1) • P‖ := norm_add_le _ _
      _ ≤ θ + δ := by
        simpa only [norm_smul, Real.norm_eq_abs, hP, mul_one] using (add_le_add hB hlam)
  have hw : ‖j - P j‖ ≤ ε + θ + δ := by
    calc
      _ = ‖(j - B j) + (B - P) j‖ := by congr 1; simp
      _ ≤ ‖j - B j‖ + ‖(B - P) j‖ := norm_add_le _ _
      _ ≤ ε + (θ + δ) * ‖j‖ := by
        apply add_le_add
        · simpa only [norm_sub_rev] using hjB
        · exact ((B - P).le_opNorm j).trans
            (mul_le_mul_of_nonneg_right hBP (norm_nonneg j))
      _ = ε + θ + δ := by rw [hj]; ring
  have hPJ := unit_projector_difference v j hv hj
  calc
    _ = ‖(B - P) + (P - rankOne ℝ j j)‖ := by congr 1; abel
    _ ≤ ‖B - P‖ + ‖P - rankOne ℝ j j‖ := norm_add_le _ _
    _ ≤ (θ + δ) + 3 * ‖j - P j‖ := add_le_add hBP (by
      simpa only [norm_sub_rev] using hPJ)
    _ ≤ 4 * (θ + δ) + 3 * ε := by linarith

end SharpTerminalLeave

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_NormalizedOnes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
theorem normalizedOnes_norm : ‖(normalizedOnes : EuclideanSpace ℝ ι)‖ = 1 := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = Fintype.card ι :=
    Real.sq_sqrt (le_of_lt hn)
  have hnorm : ‖(normalizedOnes : EuclideanSpace ℝ ι)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [normalizedOnes, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow, hs]
    exact mul_inv_cancel₀ (ne_of_gt hn)
  nlinarith [norm_nonneg (normalizedOnes : EuclideanSpace ℝ ι)]

theorem normalizedOnes_residual (A : Matrix ι ι ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrow : ∀ i, |(∑ j, A i j) - 1| ≤ δ) :
    ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes‖ ≤ δ := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = Fintype.card ι :=
    Real.sq_sqrt (le_of_lt hn)
  have hcoords : ∀ i, ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes).ofLp i =
      ((∑ j, A i j) - 1) * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ := by
    intro i
    simp [normalizedOnes, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct,
      Finset.sum_mul, sub_mul]
  have hsq : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes‖ ^ 2 ≤ δ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ i, |((∑ j, A i j) - 1)| ^ 2 * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 := by
        simp only [hcoords, Real.norm_eq_abs, sq_abs, mul_pow]
      _ ≤ ∑ _ : ι, δ ^ 2 * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hrow i) 2) (sq_nonneg _)
      _ = δ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow, hs]
        field_simp
  nlinarith [norm_nonneg ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes)]

omit [Nonempty ι] in
theorem eigenProjector_entry (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k i j : ι) :
    eigenProjector A hA k i j = hA.eigenvectorBasis k i * hA.eigenvectorBasis k j := by
  simp [eigenProjector, Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Pi.single_apply]

omit [Nonempty ι] in
theorem eigenProjector_toCLM (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k : ι) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (eigenProjector A hA k) =
      rankOne ℝ (hA.eigenvectorBasis k) (hA.eigenvectorBasis k) := by
  ext x i
  change ((eigenProjector A hA k) *ᵥ x.ofLp) i = _
  simp only [rankOne_apply, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    eigenProjector_entry, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Nonempty ι] in
theorem averagingProjector_toCLM :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (averagingProjector : Matrix ι ι ℝ) =
      rankOne ℝ (normalizedOnes : EuclideanSpace ℝ ι) normalizedOnes := by
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hn]
  ext x i
  change (averagingProjector *ᵥ x.ofLp) i = _
  simp only [rankOne_apply, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    averagingProjector, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    normalizedOnes]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  nlinarith [congrArg (fun t : ℝ => t * x.ofLp j) hs]

theorem star_approximation_from_trace (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (δ θ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ)
    (hpos : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, |(∑ j, A i j) - 1| ≤ δ)
    (r : ℕ) (hr : Even r) (hr0 : r ≠ 0)
    (htrace : (A ^ r).trace ≤ (1 - δ) ^ r + θ ^ r) :
    ‖A - averagingProjector‖ ≤ 4 * θ + 7 * δ := by
  have hrlo : ∀ i, 1 - δ ≤ ∑ j, A i j := fun i => by
    have hh := (abs_le.mp (hrow i)).1
    linarith
  have hrhi : ∀ i, ∑ j, |A i j| ≤ 1 + δ := fun i => by
    simp_rw [abs_of_nonneg (hpos i _)]
    have hh := (abs_le.mp (hrow i)).2
    linarith
  obtain ⟨k, hklo, hkhi, _⟩ := exists_leading_of_rowsums A hA (1-δ) (1+δ)
    (by linarith) hrlo hrhi
  have hlam : |hA.eigenvalues k - 1| ≤ δ := by
    have hhi := (abs_le.mp hkhi).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htail := eigenvalue_tail_of_trace A hA k r hr hr0 (1-δ) θ
    (by linarith) hθ hklo htrace
  have happrox := eigenProjector_approximation A hA k θ hθ htail
  have heig : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A - hA.eigenvalues k •
      rankOne ℝ (hA.eigenvectorBasis k) (hA.eigenvectorBasis k)‖ ≤ θ := by
    rw [← eigenProjector_toCLM A hA k, ← map_smul, ← map_sub,
      Matrix.l2_opNorm_toEuclideanCLM]
    exact happrox
  have hfinal := projector_transfer ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A)
    (hA.eigenvectorBasis k) normalizedOnes (hA.eigenvectorBasis.norm_eq_one k)
    normalizedOnes_norm (hA.eigenvalues k) θ δ δ heig hlam
    (normalizedOnes_residual A δ hδ0 hrow)
  rw [← averagingProjector_toCLM, ← map_sub, Matrix.l2_opNorm_toEuclideanCLM] at hfinal
  linarith

end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_GraphEmbeddingsRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section EmbeddingCyclicSeed
variable {A B V : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq B] in

theorem graphEmbeddings_restriction_le (hH : H.Preconnected) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (c : B ↪ A) (hB : Nonempty B) (t : Finset (B ↪ V))
    (ht : ∀ f ∈ graphEmbeddings H G, c.trans f ∈ t) :
    (graphEmbeddings H G).card ≤ t.card * Δ ^ (Fintype.card A - Fintype.card B) := by
  classical
  let S : Finset A := Finset.univ.map c
  have hS : S.Nonempty := by
    obtain ⟨b⟩ := hB
    exact ⟨c b, Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  have hSc : Sᶜ.card = Fintype.card A - Fintype.card B := by
    simp [S, Finset.card_compl]
  have hfib : ∀ χ ∈ t,
      ((graphEmbeddings H G).filter (fun f => c.trans f = χ)).card ≤
        Δ ^ (Fintype.card A - Fintype.card B) := by
    intro χ _
    let sf := (graphEmbeddings H G).filter (fun f => c.trans f = χ)
    by_cases hs : sf.Nonempty
    · obtain ⟨f₀, hf₀⟩ := hs
      have hcomp := (Finset.mem_filter.mp hf₀).2
      have heq : sf = rootedEmbeddingFiber H G S f₀ := by
        ext f
        simp only [sf, Finset.mem_filter, mem_rootedEmbeddingFiber]
        constructor
        · rintro ⟨hf, he⟩
          refine ⟨hf, ?_⟩
          intro a ha
          obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
          have hh := congrArg (fun χ : B ↪ V => χ b) (he.trans hcomp.symm)
          exact hh
        · rintro ⟨hf, he⟩
          refine ⟨hf, ?_⟩
          rw [← hcomp]
          apply Function.Embedding.ext
          intro b
          exact he (c b) (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)
      change sf.card ≤ _
      rw [heq, ← hSc]
      exact rootedEmbeddingFiber_le hH Δ hΔ S hS f₀
    · have he : sf = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      change sf.card ≤ _
      rw [he, Finset.card_empty]
      exact Nat.zero_le _
  calc
    _ = ∑ χ ∈ t, ((graphEmbeddings H G).filter (fun f => c.trans f = χ)).card :=
      Finset.card_eq_sum_card_fiberwise ht
    _ ≤ ∑ _χ ∈ t, Δ ^ (Fintype.card A - Fintype.card B) := Finset.sum_le_sum hfib
    _ = _ := by simp

theorem connected_embedding_count (hH : H.Preconnected) (a : A) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ) :
    (graphEmbeddings H G).card ≤ Fintype.card V * Δ ^ (Fintype.card A - 1) := by
  classical
  let c : Unit ↪ A := ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩
  have hh := graphEmbeddings_restriction_le H G hH Δ hΔ c inferInstance
    Finset.univ (fun _ _ => Finset.mem_univ _)
  have hunit : Fintype.card (Unit ↪ V) = Fintype.card V := by
    let e : (Unit ↪ V) ≃ V :=
      { toFun := fun f => f ()
        invFun := fun v => ⟨fun _ => v, fun _ _ _ => Subsingleton.elim _ _⟩
        left_inv := by intro f; ext x; cases x; rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  simpa only [Finset.card_univ, Fintype.card_unit, hunit] using hh

omit [DecidableEq B] in

theorem cyclic_seed_embedding_count (hH : H.Preconnected) (K : SimpleGraph B)
    (c : B ↪ A) (hB : Nonempty B)
    (hc : ∀ b b', K.Adj b b' → H.Adj (c b) (c b')) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ) :
    (graphEmbeddings H G).card ≤
      (graphEmbeddings K G).card * Δ ^ (Fintype.card A - Fintype.card B) := by
  apply graphEmbeddings_restriction_le H G hH Δ hΔ c hB (graphEmbeddings K G)
  intro f hf
  apply (mem_graphEmbeddings (c.trans f)).mpr
  intro b b' hb
  exact (mem_graphEmbeddings f).mp hf _ _ (hc b b' hb)

end EmbeddingCyclicSeed
end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_CountClosedWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem bridge_count_closedWalk {a : V} (p : G.Walk a a) {e : Sym2 V}
    (he : e ∈ p.edges) (hb : G.IsBridge e) : 2 ≤ p.edges.count e := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨i, hi, heq⟩ := (p.mk_mem_edges_iff_exists).mp he
    let q := p.drop i
    have hq : ¬ q.Nil := by
      rw [← SimpleGraph.Walk.length_eq_zero_iff]
      dsimp [q]
      rw [SimpleGraph.Walk.drop_length]
      omega
    have he' : s(p.getVert i, q.snd) = s(x,y) := by
      simpa only [q, SimpleGraph.Walk.snd, SimpleGraph.Walk.drop_getVert] using heq
    have hmem : s(p.getVert i, q.snd) ∈ (q.tail.append (p.take i)).edges := by
      have hh : G.IsBridge s(p.getVert i, q.snd) := he'.symm ▸ hb
      have hwalk := (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp hh)
        (q.tail.append (p.take i)).reverse
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hwalk
    have hcount : 1 ≤ (q.tail.append (p.take i)).edges.count s(x,y) := by
      exact List.one_le_count_iff.mpr (he' ▸ hmem)
    have hp : p.edges = (p.take i).edges ++ s(x,y) :: q.tail.edges := by
      conv_lhs => rw [← p.append_take_drop_eq i]
      rw [SimpleGraph.Walk.edges_append]
      change (p.take i).edges ++ q.edges = _
      rw [← q.cons_tail_eq hq, SimpleGraph.Walk.edges_cons, he']
      simp
    rw [SimpleGraph.Walk.edges_append, List.count_append] at hcount
    rw [hp, List.count_append, List.count_cons_self]
    omega

theorem acyclic_closedWalk_distinct_edges {a : V} (p : G.Walk a a)
    (hG : G.IsAcyclic) : 2 * p.edges.toFinset.card ≤ p.length := by
  classical
  have hh : ∀ e ∈ p.edges.toFinset, 2 ≤ p.edges.count e := by
    intro e he
    have he' := List.mem_toFinset.mp he
    exact bridge_count_closedWalk p he'
      ((SimpleGraph.isAcyclic_iff_forall_isBridge.mp hG) (p.edges_subset_edgeSet he'))
  calc
    _ = ∑ _e ∈ p.edges.toFinset, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ e ∈ p.edges.toFinset, p.edges.count e := Finset.sum_le_sum hh
    _ = p.edges.length := by exact List.sum_toFinset_count_eq_length _
    _ = p.length := p.length_edges

theorem walk_support_card_le_edges {a b : V} (p : G.Walk a b) :
    p.support.toFinset.card ≤ p.edges.toFinset.card + 1 := by
  classical
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.edges_cons,
      List.toFinset_cons]
    by_cases ha : a ∈ p.support.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      exact ih.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.subset_insert _ _)) 1)
    · have he : s(a,b) ∉ p.edges.toFinset := by
        intro he
        exact ha (List.mem_toFinset.mpr
          (p.fst_mem_support_of_mem_edges (List.mem_toFinset.mp he)))
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem he]
      omega

theorem acyclic_spanning_walk_vertices [Fintype V] {a : V} (p : G.Walk a a)
    (hG : G.IsAcyclic) (hspan : ∀ v, v ∈ p.support) :
    Fintype.card V - 1 ≤ p.length / 2 := by
  have hc := acyclic_closedWalk_distinct_edges p hG
  have hv := walk_support_card_le_edges p
  have hs : p.support.toFinset = Finset.univ := by
    exact Finset.eq_univ_iff_forall.mpr (fun v => List.mem_toFinset.mpr (hspan v))
  rw [hs, Finset.card_univ] at hv
  omega

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWalkPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

theorem canonical_cycle_spanning (n : ℕ) (v : Fin (n+3)) :
    v ∈ (SimpleGraph.cycleGraph.cycle n).support := by
  let f : Fin (n+3) → Fin (n+3) := fun i => (SimpleGraph.cycleGraph.cycle n).getVert i
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact SimpleGraph.cycleGraph.isCycle_cycle.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq, SimpleGraph.cycleGraph.length_cycle]; omega)
      (by simp only [Set.mem_ofPred_eq, SimpleGraph.cycleGraph.length_cycle]; omega) hij
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hf v
  exact hi ▸ (SimpleGraph.cycleGraph.cycle n).getVert_mem_support i

section WalkPatterns
variable {r k : ℕ}

lemma pattern_preconnected (σ : Fin r → Fin k) (hσ : PatternProper σ)
    (hs : Function.Surjective σ) : (closedWalkPattern σ).Preconnected :=
  SimpleGraph.Preconnected.map (patternHom σ hσ) hs SimpleGraph.cycleGraph_preconnected

theorem pattern_spanning_walk {n k : ℕ} (σ : Fin (n+3) → Fin k)
    (hσ : PatternProper σ) (hs : Function.Surjective σ) :
    ∃ a : Fin k, ∃ p : (closedWalkPattern σ).Walk a a,
      p.length = n+3 ∧ ∀ v, v ∈ p.support := by
  let p := (SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)
  refine ⟨σ 0, p, ?_, ?_⟩
  · change ((SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)).length = n+3
    rw [SimpleGraph.Walk.length_map, SimpleGraph.cycleGraph.length_cycle]
  · intro v
    obtain ⟨i, rfl⟩ := hs v
    change σ i ∈ ((SimpleGraph.cycleGraph.cycle n).map (patternHom σ hσ)).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨i, canonical_cycle_spanning n i, rfl⟩

end WalkPatterns

section PatternCounting
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]

theorem noninjective_pattern_count (r : ℕ) (hH : H.Preconnected)
    (hsize : Fintype.card A < r) (a : A) (p : H.Walk a a)
    (hlength : p.length = r) (hspan : ∀ v, v ∈ p.support)
    (Δ C : ℕ) (hΔ0 : 1 ≤ Δ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (hcyc : ∀ b, 3 ≤ b → b < r →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ C * Δ ^ b) :
    (graphEmbeddings H G).card ≤
      Fintype.card V * Δ ^ (r / 2) + C * Δ ^ (r-1) := by
  classical
  by_cases htree : H.IsAcyclic
  · have hv := acyclic_spanning_walk_vertices p htree hspan
    rw [hlength] at hv
    calc
      _ ≤ Fintype.card V * Δ ^ (Fintype.card A - 1) :=
        connected_embedding_count H G hH a Δ hΔ
      _ ≤ Fintype.card V * Δ ^ (r/2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hΔ0 hv)
      _ ≤ _ := Nat.le_add_right _ _
  · obtain ⟨v, c, hc⟩ : ∃ v : A, ∃ c : H.Walk v v, c.IsCycle := by
      simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using htree
    have hb : 3 ≤ c.length := hc.three_le_length
    obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < c.length)).mpr
      ⟨v, c, hc, rfl⟩
    have hcard : c.length ≤ Fintype.card A := by
      simpa using Fintype.card_le_of_injective f.toEmbedding f.injective
    have hh := cyclic_seed_embedding_count H G hH (SimpleGraph.cycleGraph c.length)
      f.toEmbedding (by exact Fin.pos_iff_nonempty.mp (by omega))
      (fun i j hij => f.toHom.map_adj hij) Δ hΔ
    have hp : Δ ^ c.length * Δ ^ (Fintype.card A - c.length) =
        Δ ^ Fintype.card A := by rw [← pow_add, Nat.add_sub_of_le hcard]
    calc
      _ ≤ (graphEmbeddings (SimpleGraph.cycleGraph c.length) G).card *
          Δ ^ (Fintype.card A-c.length) := by simpa using hh
      _ ≤ (C * Δ ^ c.length) * Δ ^ (Fintype.card A-c.length) :=
        Nat.mul_le_mul_right _ (hcyc _ hb (hcard.trans_lt hsize))
      _ = C * Δ ^ Fintype.card A := by rw [mul_assoc, hp]
      _ ≤ C * Δ ^ (r-1) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hΔ0 (by omega))
      _ ≤ _ := Nat.le_add_left _ _

end PatternCounting
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section ClosedWords
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem nonsimple_word_factor {r : ℕ} {f : Fin r → V}
    (hf : f ∈ nonsimpleWords G r) :
    ∃ k : Fin r, ∃ σ : Fin r → Fin k.val,
      PatternProper σ ∧ Function.Surjective σ ∧
      ∃ τ ∈ graphEmbeddings (closedWalkPattern σ) G, (fun i => τ (σ i)) = f := by
  classical
  have hfadj : ∀ i j, (SimpleGraph.cycleGraph r).Adj i j → G.Adj (f i) (f j) := by
    simpa only [nonsimpleWords, closedWords, Finset.mem_filter, Finset.mem_univ,
      true_and] using (Finset.mem_filter.mp hf).1
  have hnot := (Finset.mem_filter.mp hf).2
  let S := Finset.univ.image f
  have hcard : S.card < r := by
    have hle : S.card ≤ r := by simpa [S] using (Finset.card_image_le (s := Finset.univ) (f := f))
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnot
    have hi : Set.InjOn f (↑(Finset.univ : Finset (Fin r))) :=
      Finset.card_image_iff.mp (by simpa [S] using heq)
    exact fun i j hij => hi (by simp) (by simp) hij
  let e : S ≃ Fin S.card := (Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))
  let σ : Fin r → Fin S.card := fun i => e ⟨f i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
  let τ : Fin S.card ↪ V := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hτσ : ∀ i, τ (σ i) = f i := by intro i; simp [τ, σ]
  have hs : Function.Surjective σ := by
    intro a
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (e.symm a).property
    refine ⟨i, ?_⟩
    apply e.symm.injective
    apply Subtype.ext
    simpa [σ] using hi
  have hp : PatternProper σ := by
    intro i j hij heq
    exact (hfadj i j hij).ne (by rw [← hτσ i, ← hτσ j, heq])
  refine ⟨⟨S.card, hcard⟩, σ, hp, hs, τ, ?_, funext hτσ⟩
  apply (mem_graphEmbeddings τ).mpr
  intro a b hab
  obtain ⟨_, i, j, hij, hi, hj⟩ := hab
  subst a; subst b
  simpa only [hτσ] using hfadj i j hij

theorem nonsimpleWords_card_le (n : ℕ) (Δ C : ℕ) (hΔ0 : 1 ≤ Δ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ C * Δ ^ b) :
    (nonsimpleWords G (n+3)).card ≤
      (n+3) ^ (n+4) * (Fintype.card V * Δ ^ ((n+3)/2) + C * Δ ^ (n+2)) := by
  classical
  let t : (k : Fin (n+3)) → Finset (Fin (n+3) → Fin k.val) := fun _ =>
    Finset.univ.filter (fun σ => PatternProper σ ∧ Function.Surjective σ)
  let R := fun (k : Fin (n+3)) (σ : Fin (n+3) → Fin k.val) =>
    (graphEmbeddings (closedWalkPattern σ) G).image (fun τ i => τ (σ i))
  have hsub : nonsimpleWords G (n+3) ⊆ Finset.univ.biUnion (fun k => (t k).biUnion (R k)) := by
    intro f hf
    obtain ⟨k, σ, hp, hs, τ, hτ, rfl⟩ := nonsimple_word_factor G hf
    exact Finset.mem_biUnion.mpr ⟨k, by simp, Finset.mem_biUnion.mpr
      ⟨σ, by simp [t, hp, hs], Finset.mem_image.mpr ⟨τ, hτ, rfl⟩⟩⟩
  let B := Fintype.card V * Δ ^ ((n+3)/2) + C * Δ ^ (n+2)
  have hR : ∀ k, ∀ σ ∈ t k, (R k σ).card ≤ B := by
    intro k σ hσ
    have hh : PatternProper σ ∧ Function.Surjective σ := by simpa only
      [t, Finset.mem_filter, Finset.mem_univ, true_and] using hσ
    obtain ⟨a, p, hp, hs⟩ := pattern_spanning_walk σ hh.1 hh.2
    exact (Finset.card_image_le).trans (by
      simpa [B] using noninjective_pattern_count (closedWalkPattern σ) G (n+3)
        (pattern_preconnected σ hh.1 hh.2) (by simpa only [Fintype.card_fin] using k.isLt)
        a p hp hs Δ C hΔ0 hΔ hcyc)
  calc
    _ ≤ (Finset.univ.biUnion (fun k => (t k).biUnion (R k))).card := Finset.card_le_card hsub
    _ ≤ ∑ k : Fin (n+3), ∑ σ ∈ t k, (R k σ).card := by
      exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun k _ => Finset.card_biUnion_le))
    _ ≤ ∑ k : Fin (n+3), (t k).card * B := by
      apply Finset.sum_le_sum
      intro k hk
      simpa using Finset.sum_le_sum (hR k)
    _ ≤ ∑ _k : Fin (n+3), (n+3)^(n+3) * B := by
      apply Finset.sum_le_sum
      intro k hk
      apply Nat.mul_le_mul_right B
      calc
        (t k).card ≤ Fintype.card (Fin (n+3) → Fin k.val) := Finset.card_le_univ _
        _ = k.val^(n+3) := by simp
        _ ≤ (n+3)^(n+3) := Nat.pow_le_pow_left k.isLt.le _
    _ = (n+3)^(n+4) * B := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]; rw [show n+4 = (n+3)+1 by omega, pow_succ]; ring

end ClosedWords
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWalkFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section TraceBridge
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma wordOfWalk_injective {r : ℕ} (hr : 0 < r) :
    Function.Injective (wordOfWalk (G := G) (r := r)) := by
  intro p q hpq
  obtain ⟨a,p,hp⟩ := p
  obtain ⟨b,q,hq⟩ := q
  have hword : (fun i : Fin r => p.getVert i.val) = (fun i : Fin r => q.getVert i.val) :=
    Subtype.ext_iff.mp hpq
  have hab : a = b := by simpa using congrFun hword ⟨0,hr⟩
  subst b
  apply congrArg (Sigma.mk a)
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length (hp.trans hq.symm)
  intro k hk
  by_cases hkr : k < r
  · exact congrFun hword ⟨k,hkr⟩
  · have heq : k = r := by omega
    subst k
    simpa only [hp, hq] using p.getVert_length.trans q.getVert_length.symm

omit [DecidableEq V] in
lemma walkOfWord_injective (n : ℕ) : Function.Injective (walkOfWord G n) := by
  intro f g hfg
  apply Subtype.ext
  funext i
  let k := (SimpleGraph.cycleGraph.cycle n).support.idxOf i
  have hk := (SimpleGraph.cycleGraph.cycle n).getVert_support_idxOf
    (canonical_cycle_spanning n i)
  have hget := congrArg (fun w : closedWalkFamily G (n+3) => w.2.1.getVert k) hfg
  simpa [walkOfWord, SimpleGraph.Walk.getVert_map, k, hk] using hget

theorem trace_adjMatrix_eq_closedWords (n : ℕ) :
    Matrix.trace (G.adjMatrix ℕ ^ (n+3)) = (closedWords G (n+3)).card := by
  have hcard : Fintype.card (closedWalkFamily G (n+3)) =
      Fintype.card (closedWords G (n+3)) := le_antisymm
    (Fintype.card_le_of_injective _ (wordOfWalk_injective G (by omega)))
    (Fintype.card_le_of_injective _ (walkOfWord_injective G n))
  rw [Fintype.card_coe] at hcard
  rw [← hcard, Fintype.card_sigma]
  simp only [Matrix.trace, Matrix.diag_apply, SimpleGraph.adjMatrix_pow_apply_eq_card_walk, Nat.cast_id]
  apply Finset.sum_congr rfl
  intro i hi
  exact Fintype.card_congr (Equiv.refl _)

lemma closedWords_card_eq (r : ℕ) :
    (closedWords G r).card = (graphEmbeddings (SimpleGraph.cycleGraph r) G).card +
      (nonsimpleWords G r).card := by
  classical
  have hfun : ((closedWords G r).filter Function.Injective) =
      (graphEmbeddings (SimpleGraph.cycleGraph r) G).image (fun (τ : Fin r ↪ V) => (τ : Fin r → V)) := by
    ext f
    simp only [Finset.mem_filter, closedWords, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hf, hi⟩
      exact ⟨⟨f,hi⟩, (mem_graphEmbeddings _).mpr hf, rfl⟩
    · rintro ⟨τ,hτ,rfl⟩
      exact ⟨(mem_graphEmbeddings τ).mp hτ, τ.injective⟩
  have hc := Finset.card_filter_add_card_filter_not (s := closedWords G r) Function.Injective
  rw [hfun, Finset.card_image_of_injective _ (fun _ _ h => Function.Embedding.ext (congrFun h))] at hc
  exact hc.symm

end TraceBridge
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_RealTraceAdjMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section RealTrace
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma real_trace_adjMatrix_eq (n : ℕ) :
    Matrix.trace (G.adjMatrix ℝ ^ (n+3)) =
      ((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) +
        (nonsimpleWords G (n+3)).card := by
  have hNat := trace_adjMatrix_eq_closedWords G n
  rw [closedWords_card_eq] at hNat
  have ht : Matrix.trace (G.adjMatrix ℝ ^ (n+3)) =
      ((Matrix.trace (G.adjMatrix ℕ ^ (n+3)) : ℕ) : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Nat.cast_sum,
      SimpleGraph.adjMatrix_pow_apply_eq_card_walk, Nat.cast_id]
  rw [ht, hNat, Nat.cast_add]

theorem normalized_link_trace_bound (n : ℕ) (hr : Even (n+3)) (D δ : ℝ)
    (hD : 1 ≤ D)
    (hdeg : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ 2*D)
    (hmain : |((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)| ≤
      δ * D^(n+3))
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      ((graphEmbeddings (SimpleGraph.cycleGraph b) G).card : ℝ) ≤ 2 * D^b) :
    |Matrix.trace (((D⁻¹) • G.adjMatrix ℝ) ^ (n+3)) - 1| ≤
      δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
  classical
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hD0
  let Δ : ℕ := ⌊2*D⌋₊
  have hΔlo : D ≤ (Δ : ℝ) := by
    have hh := Nat.lt_floor_add_one (2*D)
    change 2*D < (Δ : ℝ)+1 at hh
    linarith
  have hΔhi : (Δ : ℝ) ≤ 2*D := Nat.floor_le (by positivity)
  have hΔ0 : 1 ≤ Δ := by exact_mod_cast hD.trans hΔlo
  have hdeg' : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ := by
    intro x
    exact (Nat.le_floor_iff (by positivity : 0 ≤ 2*D)).mpr (hdeg x)
  have hcyc' : ∀ b, 3 ≤ b → b < n+3 →
      (graphEmbeddings (SimpleGraph.cycleGraph b) G).card ≤ 2 * Δ^b := by
    intro b hb hbr
    have hh := (hcyc b hb hbr).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hD0.le hΔlo b) (by norm_num : (0:ℝ) ≤ 2))
    exact_mod_cast hh
  have hcount := nonsimpleWords_card_le G n Δ 2 hΔ0 hdeg' hcyc'
  have hcountR : ((nonsimpleWords G (n+3)).card : ℝ) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) *
        ((Fintype.card V : ℝ) * (2*D)^((n+3)/2) + 2*(2*D)^(n+2)) := by
    have hh : ((nonsimpleWords G (n+3)).card : ℝ) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) *
        ((Fintype.card V : ℝ) * (Δ:ℝ)^((n+3)/2) + 2*(Δ:ℝ)^(n+2)) := by
      exact_mod_cast hcount
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg Δ) hΔhi _) (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg Δ) hΔhi _) (by norm_num))
  have hhalf : (n+3)/2 + (n+3)/2 = n+3 := by
    obtain ⟨k, hk⟩ := hr
    omega
  have hhalfle : (n+3)/2 ≤ n+3 := Nat.div_le_self _ _
  have hp2 : (2:ℝ)^((n+3)/2) ≤ 2^(n+3) := pow_le_pow_right₀ (by norm_num) hhalfle
  have hpow : D^(n+3) = D^((n+3)/2) * D^((n+3)/2) := by rw [← pow_add, hhalf]
  have hpow' : D^(n+3) = D^(n+2) * D := by rw [← pow_succ]
  have hratio : ((nonsimpleWords G (n+3)).card : ℝ) / D^(n+3) ≤
      ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
    apply (div_le_iff₀ (pow_pos hD0 _)).mpr
    have htree : (Fintype.card V : ℝ) * (2*D)^((n+3)/2) ≤
        2^(n+3) * ((Fintype.card V : ℝ)/D^((n+3)/2)) * D^(n+3) := by
      rw [mul_pow, hpow]
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hp2
        (mul_nonneg (Nat.cast_nonneg (Fintype.card V)) (pow_nonneg hD0.le ((n+3)/2)))]
    have hcycle : 2*(2*D)^(n+2) = 2^(n+3) * (1/D) * D^(n+3) := by
      rw [mul_pow, hpow', show n+3 = (n+2)+1 by omega, pow_succ]
      field_simp
      ring
    calc
      _ ≤ ((n+3 : ℕ) : ℝ)^(n+4) *
          ((Fintype.card V : ℝ) * (2*D)^((n+3)/2) + 2*(2*D)^(n+2)) := hcountR
      _ ≤ ((n+3 : ℕ) : ℝ)^(n+4) *
          (2^(n+3) * ((Fintype.card V : ℝ)/D^((n+3)/2)) * D^(n+3) +
            2^(n+3) * (1/D) * D^(n+3)) := mul_le_mul_of_nonneg_left (add_le_add htree hcycle.le) (by positivity)
      _ = _ := by ring
  have htrace : Matrix.trace (((D⁻¹) • G.adjMatrix ℝ) ^ (n+3)) =
      (((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) +
        (nonsimpleWords G (n+3)).card) / D^(n+3) := by
    rw [smul_pow, Matrix.trace_smul, real_trace_adjMatrix_eq]
    simp only [smul_eq_mul, inv_pow, div_eq_mul_inv, mul_comm]
  rw [htrace]
  calc
    _ = |(((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)) /
          D^(n+3) + (nonsimpleWords G (n+3)).card / D^(n+3)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)) /
          D^(n+3)| + |((nonsimpleWords G (n+3)).card : ℝ) / D^(n+3)| := abs_add_le _ _
    _ ≤ δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D) := by
      apply add_le_add
      · rw [abs_div, abs_of_pos (pow_pos hD0 _)]
        exact (div_le_iff₀ (pow_pos hD0 _)).mpr hmain
      · rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hD0.le _))]
        exact hratio

end RealTrace
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_GraphStarApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
open scoped BigOperators Matrix.Norms.L2Operator

section GraphStar
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graph_star_approximation (n : ℕ) (hr : Even (n+3)) (D δ : ℝ)
    (hD : 1 ≤ D) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hrow : ∀ x : V, |((Finset.univ.filter (G.Adj x)).card : ℝ) - D| ≤ δ*D)
    (hmain : |((graphEmbeddings (SimpleGraph.cycleGraph (n+3)) G).card : ℝ) - D^(n+3)| ≤
      δ * D^(n+3))
    (hcyc : ∀ b, 3 ≤ b → b < n+3 →
      ((graphEmbeddings (SimpleGraph.cycleGraph b) G).card : ℝ) ≤ 2 * D^b) :
    ‖D⁻¹ • G.adjMatrix ℝ - averagingProjector‖ ≤
      4 * (((n+4 : ℕ) : ℝ) * δ + ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D)) ^ (1 / ((n+3 : ℕ) : ℝ)) + 7*δ := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hD0
  let W : ℝ := ((n+3 : ℕ) : ℝ)^(n+4) * 2^(n+3) *
        ((Fintype.card V : ℝ) / D^((n+3)/2) + 1/D)
  let E : ℝ := ((n+4 : ℕ) : ℝ)*δ + W
  let θ : ℝ := E ^ (1 / ((n+3 : ℕ) : ℝ))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hθ : 0 ≤ θ := Real.rpow_nonneg hE _
  have hθpow : θ ^ (n+3) = E := by
    dsimp [θ]
    rw [← Real.rpow_mul_natCast hE]
    have hn : ((n+3 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [div_mul_cancel₀ _ hn,Real.rpow_one]
  have hdeg : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ 2*D := by
    intro x
    have hh := (abs_le.mp (hrow x)).2
    nlinarith
  have htrace := normalized_link_trace_bound G n hr D δ hD hdeg hmain hcyc
  have hber : 1 - ((n+3 : ℕ) : ℝ)*δ ≤ (1-δ)^(n+3) := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -δ) (by linarith) (n+3))
  have htrace' : Matrix.trace ((D⁻¹ • G.adjMatrix ℝ)^(n+3)) ≤ (1-δ)^(n+3) + θ^(n+3) := by
    rw [hθpow]
    have hh := (abs_le.mp htrace).2
    dsimp [E]
    change Matrix.trace ((D⁻¹ • G.adjMatrix ℝ)^(n+3)) - 1 ≤ δ + W at hh
    push_cast at hber ⊢
    nlinarith
  have hrows : ∀ x : V, |(∑ y, (D⁻¹ • G.adjMatrix ℝ) x y) - 1| ≤ δ := by
    intro x
    have hsum : (∑ y, G.adjMatrix ℝ x y) =
        ((Finset.univ.filter (G.Adj x)).card : ℝ) := by
      simp only [SimpleGraph.adjMatrix_apply]
      exact Finset.sum_boole _ _
    simp only [Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum,hsum]
    have heq : D⁻¹ * ((Finset.univ.filter (G.Adj x)).card : ℝ) - 1 =
        D⁻¹ * (((Finset.univ.filter (G.Adj x)).card : ℝ) - D) := by
      field_simp
    rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hD0)]
    calc
      _ ≤ D⁻¹ * (δ*D) := mul_le_mul_of_nonneg_left (hrow x) (inv_nonneg.mpr hD0.le)
      _ = δ := by field_simp
  have hpos : ∀ x y, 0 ≤ (D⁻¹ • G.adjMatrix ℝ) x y := by
    intro x y
    change 0 ≤ D⁻¹ * G.adjMatrix ℝ x y
    exact mul_nonneg (inv_nonneg.mpr hD0.le) (by simp [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num)
  exact star_approximation_from_trace _ ((G.isHermitian_adjMatrix ℝ).smul (isSelfAdjoint_iff.mpr rfl))
    δ θ hδ0 hδ1 hθ hpos hrows (n+3) hr (by omega) htrace'

end GraphStar
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_LinkStarMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

theorem averagingProjector_hermitian {I : Type*} [Fintype I] :
    (averagingProjector : Matrix I I ℝ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [averagingProjector]

theorem prefixSpectralError_nonneg (n : ℕ) (c : ℝ) (hD : 0 ≤ prefixD n) :
    0 ≤ prefixSpectralError n c := by
  unfold prefixSpectralError
  positivity

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IncidenceDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

theorem matrix_norm_le_of_row_abs_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have hh : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (⟨c, hc⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    change (↑(∑ j, ‖A i j‖₊) : ℝ) ≤ c
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h i
  exact_mod_cast hh

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ExtendStarApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in

theorem extendStar_apply (S : Finset E) (M : Matrix S S ℝ) (i j : E) :
    extendStar S M i j = if hi : i ∈ S then if hj : j ∈ S then
      M ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0 := by
  simp only [extendStar,Matrix.mul_apply,Matrix.conjTranspose_apply,starInclusion,
    star_trivial]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · have hei : ∀ x : S, i = x.val ↔ x = ⟨i,hi⟩ := fun x => by
        rw [Subtype.ext_iff]
        exact eq_comm
      have hej : ∀ x : S, j = x.val ↔ x = ⟨j,hj⟩ := fun x => by
        rw [Subtype.ext_iff]
        exact eq_comm
      simp [hi,hj,hei,hej]
    · have hej : ∀ x : S, j ≠ x.val := fun x hx => hj (hx.symm ▸ x.property)
      simp [hi,hj,hej]
  · have hei : ∀ x : S, i ≠ x.val := fun x hx => hi (hx.symm ▸ x.property)
    simp [hi,hei]

end SharpTerminalLeave

open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MatrixRowAbsSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem matrix_row_abs_sum_le {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℝ) (i : I) : ∑ j, |M i j| ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hh : ∑ j, ‖M i j‖₊ ≤ Finset.univ.sup (fun k => ∑ j, ‖M k j‖₊) :=
    Finset.le_sup (f := fun k => ∑ j, ‖M k j‖₊) (Finset.mem_univ i)
  have hc := NNReal.coe_le_coe.mpr hh
  simpa only [NNReal.coe_sum,coe_nnnorm,Real.norm_eq_abs] using hc

theorem extendStar_row_abs_sum {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (M : Matrix S S ℝ) (i : E) :
    ∑ j, |extendStar S M i j| =
      if hi : i ∈ S then ∑ j : S, |M ⟨i,hi⟩ j| else 0 := by
  by_cases hi : i ∈ S
  · rw [dite_eq_left hi]
    have he : ∑ j : E, |extendStar S M i j| = ∑ j ∈ S, |extendStar S M i j| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      simp [extendStar_apply,hj]
    rw [he,← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl
    intro j _
    simp [extendStar_apply,hi,j.property]
  · simp [extendStar_apply,hi]

theorem sum_star_infty_norm_bound {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U]
    (S : U → Finset E) (M : (u : U) → Matrix (S u) (S u) ℝ)
    (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hM : ∀ u, ‖M u‖ ≤ ε)
    (hoverlap : ∀ e, ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) ≤ K) :
    ‖∑ u, extendStar (S u) (M u)‖ ≤ K*ε := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ (mul_nonneg hK hε)
  intro e
  calc
    _ ≤ ∑ f, ∑ u, |extendStar (S u) (M u) e f| := by
      apply Finset.sum_le_sum
      intro f _
      simp only [Matrix.sum_apply]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ u, ∑ f, |extendStar (S u) (M u) e f| := Finset.sum_comm
    _ ≤ ∑ u, if e ∈ S u then ε else 0 := by
      apply Finset.sum_le_sum
      intro u _
      rw [extendStar_row_abs_sum]
      by_cases he : e ∈ S u
      · simp only [he,↓reduceDIte,↓reduceIte]
        exact (matrix_row_abs_sum_le (M u) ⟨e,he⟩).trans (hM u)
      · simp [he]
    _ = ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) * ε := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ K*ε := mul_le_mul_of_nonneg_right (hoverlap e) hε

theorem infty_reindex_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (M : Matrix I I ℝ) : ‖Matrix.reindex e e M‖ ≤ ‖M‖ := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ (norm_nonneg _)
  intro i
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [e.symm.sum_comp (fun j => |M (e.symm i) j|)]
  exact matrix_row_abs_sum_le M (e.symm i)

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_AveragingProjectorInftyOne
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem averagingProjector_infty_le_one {I : Type*} [Fintype I] :
    ‖(averagingProjector : Matrix I I ℝ)‖ ≤ 1 := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ zero_le_one
  intro i
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  simp [averagingProjector,abs_of_pos (inv_pos.mpr hcard),ne_of_gt hcard]

theorem globalStarAverage_infty_le_two {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    ‖globalStarAverage G‖ ≤ 2 := by
  have h := sum_star_infty_norm_bound (edgeStar G) (fun _ => averagingProjector)
    1 2 (by norm_num) (by norm_num) (fun _ => averagingProjector_infty_le_one)
    (fun e => by rw [edgeStar_exact_overlap G hG e]; norm_num)
  simpa only [globalStarAverage,mul_one] using h

end SharpTerminalLeave

end

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_DensityGlobalInfty
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix.Norms.Operator
open Classical Matrix

namespace SharpTerminalLeave

theorem density_global_infty {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (D : ℝ) (hD0 : 0 < D)
    (hrow : ∀ u v : Fin n, {u,v} ∈ G → (currentCodegree G u v : ℝ) ≤ 2*D) :
    ‖D⁻¹ • globalLinkAdjacency G hG‖ ≤ 4 := by
  have hlocal : ∀ u, ‖(D)⁻¹ • linkStarMatrix G hG u‖ ≤ 2 := by
    intro u
    change ‖Matrix.reindex (neighborEdgeEquiv G hG u) (neighborEdgeEquiv G hG u)
      ((D)⁻¹ • (linkSimpleGraph G hG u).adjMatrix ℝ)‖ ≤ 2
    apply (infty_reindex_norm_le _ _).trans
    apply matrix_norm_le_of_row_abs_sum_le _ _ (by norm_num)
    intro v
    have hdeg : ((Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card : ℝ) ≤ 2*D := by
      rw [link_degree_eq G hG u v]
      exact hrow u v.val (Finset.mem_filter.mp v.property).2
    have heq : ∑ j : neighbors G u,
        |((D)⁻¹ • (linkSimpleGraph G hG u).adjMatrix ℝ) v j| =
        (D)⁻¹ * ((Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card : ℝ) := by
      simp only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hD0)]
      rw [← Finset.mul_sum]
      congr 1
      simp only [SimpleGraph.adjMatrix_apply]
      simp only [apply_ite abs,abs_one,abs_zero,Finset.sum_boole]
    rw [heq]
    calc
      _ ≤ (D)⁻¹ * (2 * D) :=
        mul_le_mul_of_nonneg_left hdeg (inv_nonneg.mpr hD0.le)
      _ = 2 := by field_simp
  have hsplit : (D)⁻¹ • globalLinkAdjacency G hG =
      ∑ u, extendStar (edgeStar G u) ((D)⁻¹ • linkStarMatrix G hG u) := by
    simp [globalLinkAdjacency,Finset.smul_sum,extendStar,Matrix.smul_mul,Matrix.mul_smul]
  rw [hsplit]
  simpa only [show (2 : ℝ)*2 = 4 by norm_num] using
    sum_star_infty_norm_bound (edgeStar G) _ 2 2 (by norm_num) (by norm_num) hlocal
    (fun e => by rw [edgeStar_exact_overlap G hG e]; norm_num)

lemma density_residual_infty {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (D : ℝ) (hD0 : 0 < D)
    (hrow : ∀ u v : Fin n, {u,v} ∈ G → (currentCodegree G u v : ℝ) ≤ 2*D) :
    ‖D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G‖ ≤ 6 := by
  have ha := density_global_infty G hG D hD0 hrow
  have hp := globalStarAverage_infty_le_two G hG
  exact (norm_sub_le _ _).trans (by linarith only [ha,hp])

end SharpTerminalLeave
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
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CompleteEdge
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Matrix

namespace SharpTerminalLeave

lemma graphActive_sum {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (f : CompleteEdge n → ℝ) :
    (∑ e ∈ graphActive G, f e) = ∑ e : G, f (graphEdgeEmbed G hG e) := by
  apply Finset.sum_bij (fun e he => (⟨e.val,(mem_graphActive G e).mp he⟩ : G))
  · intro _ _; exact Finset.mem_univ _
  · intro a ha b hb he
    exact Subtype.ext (congrArg (fun e : G => e.val) he)
  · intro e _
    exact ⟨graphEdgeEmbed G hG e,by exact (mem_graphActive G _).mpr e.property,rfl⟩
  · intro _ _; rfl

lemma activeLinf_restrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (x : CompleteEdge n → ℝ) :
    activeLinf (graphActive G) x = ‖graphRestrict G hG x‖ := by
  apply le_antisymm
  · apply activeLinf_bound _ _ (norm_nonneg _)
    intro e he
    have hh := norm_le_pi_norm (graphRestrict G hG x) (⟨e.val,(mem_graphActive G e).mp he⟩ : G)
    exact hh
  · apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
    intro e
    exact activeLinf_coordinate _ _ (e := graphEdgeEmbed G hG e) ((mem_graphActive _ _).mpr e.property)

lemma activeL2_restrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (x : CompleteEdge n → ℝ) :
    activeL2 (graphActive G) x = ‖WithLp.toLp 2 (graphRestrict G hG x)‖ := by
  have hsq : (activeL2 (graphActive G) x)^2 = ‖WithLp.toLp 2 (graphRestrict G hG x)‖^2 := by
    rw [activeL2_sq,EuclideanSpace.real_norm_sq_eq,graphActive_sum G hG]
    rfl
  nlinarith [apply_nonneg (activeL2 (graphActive G)) x,norm_nonneg (WithLp.toLp 2 (graphRestrict G hG x))]

open scoped Matrix.Norms.Operator in

lemma graphMatrixLift_linf {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) (x : CompleteEdge n → ℝ) :
    activeLinf (graphActive G) (graphMatrixLift G hG M x) ≤ ‖M‖*activeLinf (graphActive G) x := by
  rw [activeLinf_restrict G hG,graphMatrixLift_restrict,activeLinf_restrict G hG]
  exact (matrixInfinityAlgHom M).le_opNorm _ |>.trans_eq (by rw [matrixInfinityAlgHom_norm])

open scoped Matrix.Norms.L2Operator in

lemma graphMatrixLift_l2 {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) (x : CompleteEdge n → ℝ) :
    activeL2 (graphActive G) (graphMatrixLift G hG M x) ≤ ‖M‖*activeL2 (graphActive G) x := by
  rw [activeL2_restrict G hG,graphMatrixLift_restrict,activeL2_restrict G hG]
  have hh := (Matrix.toEuclideanCLM (n := G) (𝕜 := ℝ) M).le_opNorm (WithLp.toLp 2 (graphRestrict G hG x))
  simpa only [Matrix.toEuclideanCLM_toLp,← Matrix.l2_opNorm_toEuclideanCLM] using hh

end SharpTerminalLeave
end
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

lemma densityEdgeSafe_pair_upper {n : ℕ} {p η : ℝ} {G : Graph n}
    (hp : 0 ≤ (n : ℝ)*p^2) (hη : η ≤ 1) (h : densityEdgeSafe n p η G)
    (u v : Fin n) (he : {u,v} ∈ G) :
    (currentCodegree G u v : ℝ) ≤ 2*((n : ℝ)*p^2) := by
  have hh := (abs_le.mp (h.2.2 {u,v} he)).2
  rw [triangleDegree_eq_codegree h.1 he] at hh
  nlinarith only [hh,mul_le_mul_of_nonneg_right hη hp]

end SharpTerminalLeave
end
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

theorem density_global_spectral {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (D c : ℝ) (hD : prefixD n ≤ D) (hDmin : 1 ≤ prefixD n)
    (hδ : (n : ℝ)^(-c) ≤ 1) (hne : ∀ u, (neighbors G u).Nonempty)
    (hrow : ∀ u v : Fin n, {u,v} ∈ G →
      |(currentCodegree G u v : ℝ)-D| ≤ (n : ℝ)^(-c)*D)
    (hcyc : ∀ j, 3 ≤ j → j ≤ 8000 → ∀ u : Fin n,
      |linkCycleCount j G u-D^j| ≤ (n : ℝ)^(-c)*D^j) :
    ‖D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G‖ ≤ 2*prefixSpectralError n c := by
  have hD1 : 1 ≤ D := hDmin.trans hD
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hd0 : 0 ≤ (n : ℝ)^(-c) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let M (u : Fin n) : Matrix (neighbors G u) (neighbors G u) ℝ :=
    D⁻¹ • (linkSimpleGraph G hG u).adjMatrix ℝ-averagingProjector
  let N (u : Fin n) : Matrix (edgeStar G u) (edgeStar G u) ℝ :=
    Matrix.reindex (neighborEdgeEquiv G hG u) (neighborEdgeEquiv G hG u) (M u)
  have hM : ∀ u, (M u).IsHermitian := by
    intro u
    exact ((linkSimpleGraph G hG u).isHermitian_adjMatrix ℝ).smul
      (isSelfAdjoint_iff.mpr rfl) |>.sub averagingProjector_hermitian
  have hlocal : ∀ u, ‖N u‖ ≤ prefixSpectralError n c := by
    intro u
    have : Nonempty (neighbors G u) := (hne u).to_subtype
    apply (hermitian_reindex_norm_le _ _ (hM u)).trans
    have hr : ∀ v : neighbors G u,
        |((Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card : ℝ)-D| ≤ (n : ℝ)^(-c)*D := by
      intro v
      rw [link_degree_eq G hG u v]
      exact hrow u v.val (Finset.mem_filter.mp v.property).2
    have hm := hcyc 8000 (by decide) le_rfl u
    rw [linkCycleCount_eq_graphEmbeddings (j := 7998) G hG u] at hm
    have hc : ∀ b, 3 ≤ b → b < 8000 →
        ((graphEmbeddings (SimpleGraph.cycleGraph b) (linkSimpleGraph G hG u)).card : ℝ) ≤ 2*D^b := by
      intro b hb hb'
      have hh := (abs_le.mp (hcyc b hb hb'.le u)).2
      have he : b = b-2+2 := by omega
      have hcount : linkCycleCount b G u =
          ((graphEmbeddings (SimpleGraph.cycleGraph b) (linkSimpleGraph G hG u)).card : ℝ) := by
        rw [he]
        exact linkCycleCount_eq_graphEmbeddings G hG u
      rw [hcount] at hh
      have hx := mul_le_mul_of_nonneg_right hδ (pow_nonneg hD0.le b)
      nlinarith
    have hh := graph_star_approximation (linkSimpleGraph G hG u) 7997 (by decide)
      D ((n : ℝ)^(-c)) hD1 hd0 hδ hr hm hc
    apply hh.trans
    have hn : (Fintype.card (neighbors G u) : ℝ) ≤ n := by
      exact_mod_cast (show Fintype.card (neighbors G u) ≤ n by
        simpa using (neighbors G u).card_le_univ)
    change 4*((8001 : ℝ)*(n : ℝ)^(-c)+(8000 : ℝ)^8001*2^8000*
      ((Fintype.card (neighbors G u) : ℝ)/D^4000+1/D))^(1/(8000 : ℝ))+7*(n : ℝ)^(-c) ≤ _
    unfold prefixSpectralError
    gcongr
  have hsplit : D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G =
      ∑ u, extendStar (edgeStar G u) (N u) := by
    simp only [globalLinkAdjacency,globalStarAverage,Finset.smul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have he : N u = D⁻¹ • linkStarMatrix G hG u-averagingProjector := by
      ext i j
      simp only [N,M,linkStarMatrix,Matrix.reindex_apply,Matrix.submatrix_apply,
        Matrix.sub_apply,Matrix.smul_apply,averagingProjector]
      rw [Fintype.card_congr (neighborEdgeEquiv G hG u)]
    rw [he]
    simp [extendStar,Matrix.mul_sub,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul]
  rw [hsplit]
  exact graph_star_error_norm G hG N (fun u => (Matrix.isHermitian_reindex_iff _).mpr (hM u))
    (prefixSpectralError n c) (prefixSpectralError_nonneg n c (zero_le_one.trans hDmin)) hlocal

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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEdgeResidualBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical Matrix

namespace SharpTerminalLeave

theorem prefix_edge_residual_bounds_oai : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ∀ hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support,
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ i < j, ∀ z : CompleteEdge n → ℝ,
    activeLinf (graphActive (ω (historyIndex (prefixTime n) i))) (prefixEdgeResidual ω hω i z) ≤
      6*activeLinf (graphActive (ω (historyIndex (prefixTime n) i))) z ∧
    activeL2 (graphActive (ω (historyIndex (prefixTime n) i))) (prefixEdgeResidual ω hω i z) ≤
      (2*prefixSpectralError n (1/80000))*activeL2 (graphActive (ω (historyIndex (prefixTime n) i))) z := by
  filter_upwards [prefix_degree_wheel_tracking,prefixD_eventual_envelope,
    triangle_closure_budget,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n htrack hD hη hp hn
  intro ω hω hroot hnoise j hj hsafe i hi z
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hit : i ≤ prefixTime n := by omega
  let G := ω (historyIndex (prefixTime n) i)
  let D := earlyTemplateScale 1 2 n i
  have hG : G ⊆ completeGraph n := history_valid_all ω hω i
  have hs : densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n) G := hsafe i hi
  have hw := htrack ω hω hroot hnoise i hit (fun k hk => hsafe k (by omega))
  have hpi := early_density_positive hn0 hp hit
  have hD0 : 0 < D := by dsimp [D,earlyTemplateScale]; positivity
  have hDmin : 1 ≤ prefixD n := (Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 1/1000)).trans hD.1
  have hDle : prefixD n ≤ D := by
    have hp0 := early_density_positive hn0 hp (le_refl (prefixTime n))
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hp0.le (earlyDensity_antitone n hit) 2) hnR.le
    simpa only [prefixD,D,earlyTemplateScale,pow_one,earlyDensity_prefix] using hh
  have hw0 : 0 ≤ prefixWheelRadius n := Real.rpow_nonneg hnR.le _
  have hw1 : prefixWheelRadius n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hηw : prefixEdgeRadius n ≤ prefixWheelRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hrow : ∀ u v : Fin n, {u,v} ∈ G →
      |(currentCodegree G u v : ℝ)-D| ≤ (n : ℝ)^(-(1/80000 : ℝ))*D := by
    intro u v he
    have hh := hs.2.2 {u,v} he
    rw [triangleDegree_eq_codegree hG he] at hh
    have hh' : |(currentCodegree G u v : ℝ)-D| ≤ prefixEdgeRadius n*D := by
      simpa only [D,earlyTemplateScale,pow_one] using hh
    simpa only [prefixWheelRadius,neg_div] using hh'.trans (mul_le_mul_of_nonneg_right hηw hD0.le)
  have hcyc : ∀ b, 3 ≤ b → b ≤ 8000 → ∀ u : Fin n,
      |linkCycleCount b G u-D^b| ≤ (n : ℝ)^(-(1/80000 : ℝ))*D^b := by
    intro b hb hb' u
    have hh := hw.2 b hb hb' u
    have hh' : |linkCycleCount b G u/D^b-1| ≤ prefixWheelRadius n/2 := by
      simpa only [D,earlyTemplateScale,pow_one,G] using hh
    have hpow := pow_pos hD0 b
    have he : linkCycleCount b G u/D^b-1 = (linkCycleCount b G u-D^b)/D^b := by field_simp
    rw [he,abs_div,abs_of_pos hpow] at hh'
    have hh'' := (div_le_iff₀ hpow).mp hh'
    simpa only [prefixWheelRadius,neg_div] using hh''.trans (mul_le_mul_of_nonneg_right (by linarith only [hw0] : prefixWheelRadius n/2 ≤ prefixWheelRadius n) hpow.le)
  have hne : ∀ u : Fin n, (neighbors G u).Nonempty := by
    intro u
    have hh := (abs_le.mp (hw.1 u)).1
    have hpos : 0 < (n : ℝ)*earlyDensity n i := mul_pos hnR hpi
    have hc : (0 : ℝ) < currentDegree G u := by
      have hr : 0 < (currentDegree G u : ℝ)/((n : ℝ)*earlyDensity n i) := by linarith only [hh,hw1]
      exact (div_pos_iff.mp hr).resolve_right (by intro h; linarith only [h.2,hpos]) |>.1
    apply Finset.card_pos.mp
    exact_mod_cast hc
  have hrow2 : ∀ u v : Fin n, {u,v} ∈ G → (currentCodegree G u v : ℝ) ≤ 2*D := by
    intro u v he
    have hp0 : 0 ≤ (n : ℝ)*earlyDensity n i^2 := by positivity
    simpa only [D,earlyTemplateScale,pow_one] using densityEdgeSafe_pair_upper hp0 (show prefixEdgeRadius n ≤ 1 by linarith only [hη.2.1]) hs u v he
  constructor
  · open scoped Matrix.Norms.Operator in
    have hh := (graphMatrixLift_linf G hG (D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G) z).trans
      (mul_le_mul_of_nonneg_right (density_residual_infty G hG D hD0 hrow2) (apply_nonneg _ _))
    exact hh
  · open scoped Matrix.Norms.L2Operator in
    have hh := (graphMatrixLift_l2 G hG (D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G) z).trans
      (mul_le_mul_of_nonneg_right (density_global_spectral G hG D (1/80000) hDle hDmin (by simpa only [prefixWheelRadius,neg_div] using hw1) hne hrow hcyc)
        (apply_nonneg _ _))
    exact hh

end SharpTerminalLeave
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpTerminalLeave.prefix_edge_residual_bounds_oai := @OAI.SharpTerminalLeave.prefix_edge_residual_bounds_oai
