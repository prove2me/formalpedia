-- Prove2me | solution 1 for OAI.PlanarHalving.PlaneGraph.designated_crossing_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:51:18.978934+00:00
-- url     : https://prove2.me/submissions/8a78daa0-dc05-4970-9256-2ffaf9658e9f

import Mathlib
import Definitions.Def_HalvingLines
import Definitions.Def_OAIQWPHL000
import Theorems.Thm_OAI_PlanarHalving_PlaneGraph_planar_edge_bound

section
-- module Solutions.OAIQW_PlanarHalving.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.PlaneGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving
namespace PlaneGraph

variable {V : Type*} [Fintype V] {P : V → Point}

theorem Drawing.planar_bound (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P) (hD : D.NonCrossing) :
    D.edges.card ≤ 3 * D.vertices.card :=
  planar_edge_bound P hP hx D.vertices D.edges D.right D.ends hD

omit [Fintype V] in
lemma incident_disjoint (hP : Position P) (hx : Function.Injective (fun v => (P v).1))
    {v u w : V} (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w) :
    Disjoint (openSegment ℝ (P v) (P u)) (openSegment ℝ (P v) (P w)) := by
  apply Set.disjoint_left.mpr
  intro z hzu hzw
  have hu := height_of_mem_openSegment (fun h => hvu (hx h)) hzu
  have hw := height_of_mem_openSegment (fun h => hvw (hx h)) hzw
  have he : PlanarHalving.slope (P v) (P u) = PlanarHalving.slope (P v) (P w) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hu.1)
    dsimp only [height] at hu hw
    linarith only [hu.2, hw.2]
  exact huw (slope_eq_implies_eq_ne hP (fun h => hvu (hx h)) (fun h => hvw (hx h)) he)

omit [Fintype V] in
lemma Drawing.crossing_endpoints (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges) (hne : e ≠ f)
    (hc : Crosses P e f) :
    e.1 ≠ e.2 ∧ f.1 ≠ f.2 ∧ e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  have hev : e.1 ≠ e.2 := by intro h; have := D.right _ he; rw [h] at this; exact lt_irrefl _ this
  have hfv : f.1 ≠ f.2 := by intro h; have := D.right _ hf; rw [h] at this; exact lt_irrefl _ this
  have h11 : e.1 ≠ f.1 := by
    intro h
    apply hc
    rw [h]
    exact incident_disjoint hP hx (by simpa only [← h] using hev) hfv
      (fun h' => hne (Prod.ext h h'))
  have h22 : e.2 ≠ f.2 := by
    intro h
    apply hc
    rw [openSegment_symm ℝ (P e.1), openSegment_symm ℝ (P f.1), h]
    exact incident_disjoint hP hx (by simpa only [← h] using hev.symm) hfv.symm
      (fun h' => hne (Prod.ext h' h))
  obtain ⟨z, hze, hzf⟩ := Set.not_disjoint_iff.mp hc
  have hxe := openSegment_horizontal_bounds (D.right _ he) hze
  have hxf := openSegment_horizontal_bounds (D.right _ hf) hzf
  refine ⟨hev, hfv, h11, ?_, ?_, h22⟩
  · intro h
    rw [h] at hxe
    exact lt_irrefl _ (hxe.1.trans hxf.2)
  · intro h
    rw [h] at hxe
    exact lt_irrefl _ (hxf.1.trans hxe.2)

lemma Drawing.uncross_nonCrossing (D : Drawing P) : D.uncross.NonCrossing := by
  classical
  intro e he f hf hne
  by_contra hc
  have he' := Finset.mem_sdiff.mp he
  have hf' := Finset.mem_sdiff.mp hf
  have hi : edgeIndex e ≠ edgeIndex f := fun h => hne (edgeIndex.injective h)
  rcases hi.lt_or_gt with hlt | hlt
  · apply he'.2
    exact Finset.mem_image.mpr ⟨(e,f), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨he'.1, hf'.1⟩, hlt, hc⟩, rfl⟩
  · apply hf'.2
    exact Finset.mem_image.mpr ⟨(f,e), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hf'.1, he'.1⟩, hlt, fun h => hc h.symm⟩, rfl⟩

theorem Drawing.linear_crossing_bound (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P) :
    D.edges.card ≤ 3 * D.vertices.card + D.crossings.card := by
  classical
  have hp := D.uncross.planar_bound hP hx D.uncross_nonCrossing
  change (D.edges \ D.crossings.image Prod.fst).card ≤ 3 * D.vertices.card at hp
  have hi : (D.edges ∩ D.crossings.image Prod.fst).card ≤ D.crossings.card :=
    (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_image_le)
  have he := Finset.card_sdiff_add_card_inter D.edges (D.crossings.image Prod.fst)
  omega

end PlaneGraph
end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.CrossingEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.FiniteSampling
open scoped BigOperators

variable {V : Type*} [Fintype V]

lemma weight_nonneg {p : V → ℝ} (hp : ∀ v, p v ∈ Set.Icc (0 : ℝ) 1) (ω : V → Bool) :
    0 ≤ weight p ω := by
  classical
  apply Finset.prod_nonneg
  intro v _
  split_ifs
  · exact (hp v).1
  · exact sub_nonneg.mpr (hp v).2

lemma expect_prod (p : V → ℝ) (f : V → Bool → ℝ) :
    expect p (fun ω => ∏ v, f v (ω v)) =
      ∏ v, ((1 - p v) * f v false + p v * f v true) := by
  classical
  unfold expect weight
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun v (b : Bool) => (if b then p v else 1 - p v) * f v b)]
  congr 1
  funext v
  simp [add_comm]

@[simp] lemma expect_const (p : V → ℝ) (c : ℝ) : expect p (fun _ => c) = c := by
  classical
  have h := expect_prod p (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one, sub_add_cancel, expect] at h
  unfold expect
  rw [← Finset.sum_mul, h, one_mul]

lemma expect_mono {p : V → ℝ} (hp : ∀ v, p v ∈ Set.Icc (0 : ℝ) 1)
    {f g : (V → Bool) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect p f ≤ expect p g :=
  by
    classical
    exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (weight_nonneg hp ω)

lemma expect_sum {A : Type*} (p : V → ℝ) (s : Finset A) (f : A → (V → Bool) → ℝ) :
    expect p (fun ω => ∑ a ∈ s, f a ω) = ∑ a ∈ s, expect p (f a) := by
  classical
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma expect_add (p : V → ℝ) (f g : (V → Bool) → ℝ) :
    expect p (fun ω => f ω + g ω) = expect p f + expect p g := by
  classical
  simp only [expect, mul_add, Finset.sum_add_distrib]

lemma expect_sub (p : V → ℝ) (f g : (V → Bool) → ℝ) :
    expect p (fun ω => f ω - g ω) = expect p f - expect p g := by
  classical
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

lemma expect_mul_const (p : V → ℝ) (f : (V → Bool) → ℝ) (c : ℝ) :
    expect p (fun ω => f ω * c) = expect p f * c := by
  classical
  simp only [expect, ← mul_assoc, Finset.sum_mul]

lemma expect_const_mul (p : V → ℝ) (f : (V → Bool) → ℝ) (c : ℝ) :
    expect p (fun ω => c * f ω) = c * expect p f := by
  classical
  simp_rw [mul_comm c]
  exact expect_mul_const _ _ _

lemma keep_prod (s : Finset V) (ω : V → Bool) :
    keep s ω = ∏ v ∈ s, if ω v then (1 : ℝ) else 0 := by
  classical
  by_cases h : ∀ v ∈ s, ω v = true
  · rw [keep, ite_eq_left h]
    symm
    exact Finset.prod_eq_one fun v hv => by simp [h v hv]
  · rw [keep, ite_eq_right h]
    push Not at h
    obtain ⟨v, hv, hw⟩ := h
    symm
    exact Finset.prod_eq_zero hv (by simp [hw])

lemma expect_keep (p : V → ℝ) (s : Finset V) :
    expect p (keep s) = ∏ v ∈ s, p v := by
  classical
  have he (ω : V → Bool) : keep s ω =
      ∏ v, if v ∈ s then (if ω v then (1 : ℝ) else 0) else 1 := by
    rw [keep_prod]
    simp only [Finset.prod_ite_mem_eq]
  rw [show keep s = (fun ω => ∏ v, if v ∈ s then (if ω v then (1 : ℝ) else 0) else 1) from funext he]
  rw [expect_prod p (fun v b => if v ∈ s then (if b then (1 : ℝ) else 0) else 1)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h (v : V) : (1 - p v) * (if v ∈ s then 0 else 1) +
      p v * (if v ∈ s then 1 else 1) = if v ∈ s then p v else 1 := by
    split_ifs <;> ring
  simp_rw [h]
  simp

lemma exists_ge_expect {p : V → ℝ} (hp : ∀ v, p v ∈ Set.Icc (0 : ℝ) 1)
    (f : (V → Bool) → ℝ) : ∃ ω, expect p f ≤ f ω := by
  classical
  obtain ⟨ω, _, hω⟩ := Finset.univ.exists_max_image f Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  calc expect p f ≤ expect p (fun _ => f ω) := expect_mono hp fun τ => hω τ (Finset.mem_univ _)
       _ = f ω := expect_const _ _

lemma expect_single (p : V → ℝ) (v : V) :
    expect p (fun ω => if ω v then (1 : ℝ) else 0) = p v := by
  classical
  rw [show (fun ω : V → Bool => if ω v then (1 : ℝ) else 0) = keep {v} from by
    funext ω; simp [keep]]
  simpa using expect_keep p {v}

lemma expect_pair (p : V → ℝ) {u v : V} (hne : u ≠ v) :
    expect p (fun ω => if ω u = true ∧ ω v = true then (1 : ℝ) else 0) = p u * p v := by
  classical
  rw [show (fun ω : V → Bool => if ω u = true ∧ ω v = true then (1 : ℝ) else 0) = keep {u,v} from by
    funext ω; simp [keep]]
  simpa [hne] using expect_keep p {u,v}

lemma expect_xor (p : V → ℝ) {u v : V} (hne : u ≠ v) :
    expect p (fun ω => if ω u ≠ ω v then (1 : ℝ) else 0) = p u + p v - 2 * (p u * p v) := by
  classical
  have he : (fun ω : V → Bool => if ω u ≠ ω v then (1 : ℝ) else 0) =
      (fun ω => (if ω u then (1 : ℝ) else 0) + (if ω v then (1 : ℝ) else 0) -
        2 * (if ω u = true ∧ ω v = true then (1 : ℝ) else 0)) := by
    funext ω
    cases ω u <;> cases ω v <;> norm_num
  rw [he, expect_sub, expect_add, expect_const_mul, expect_single, expect_single, expect_pair p hne]

omit [Fintype V] in
lemma expect_cut (F : Finset V) {u v : V} (hne : u ≠ v) (hF : u ∈ F ∨ v ∈ F) :
    expect (fun _ : ↥F => (1 : ℝ) / 2) (fun ω => if bit F ω u ≠ bit F ω v then (1 : ℝ) else 0) = 1 / 2 := by
  classical
  by_cases hu : u ∈ F
  · by_cases hv : v ∈ F
    · simp only [bit, dite_eq_left hu, dite_eq_left hv]
      rw [expect_xor _ (show (⟨u,hu⟩ : ↥F) ≠ ⟨v,hv⟩ from fun h => hne (congrArg Subtype.val h))]
      norm_num
    · simp only [bit, dite_eq_left hu, dite_eq_right hv, Bool.not_eq_false]
      exact expect_single (fun _ : ↥F => (1 : ℝ) / 2) (⟨u,hu⟩ : ↥F)
  · have hv := hF.resolve_left hu
    have hb (b : Bool) : (false ≠ b) ↔ b = true := by cases b <;> decide
    simp only [bit, dite_eq_right hu, dite_eq_left hv, hb]
    exact expect_single (fun _ : ↥F => (1 : ℝ) / 2) (⟨v,hv⟩ : ↥F)

end PlanarHalving.FiniteSampling

namespace PlanarHalving.PlaneGraph
open scoped BigOperators
open FiniteSampling
variable {V : Type*} [Fintype V] {P : V → Point}

lemma Drawing.sample_crossings (D : Drawing P) (ω : V → Bool) :
    (D.sample ω).crossings = D.crossings.filter (fun ef =>
      ω ef.1.1 = true ∧ ω ef.1.2 = true ∧ ω ef.2.1 = true ∧ ω ef.2.2 = true) := by
  classical
  ext ef
  simp only [Drawing.crossings, Drawing.sample, Finset.mem_filter, Finset.mem_product]
  tauto

lemma Drawing.expect_vertices (D : Drawing P) (p : V → ℝ) :
    expect p (fun ω => ((D.sample ω).vertices.card : ℝ)) = ∑ v ∈ D.vertices, p v := by
  classical
  have h (ω : V → Bool) : ((D.sample ω).vertices.card : ℝ) =
      ∑ v ∈ D.vertices, keep {v} ω := by
    simp [Drawing.sample, keep]
  simp_rw [h]
  rw [expect_sum]
  simp [expect_keep]

lemma Drawing.expect_edges (D : Drawing P) (p : V → ℝ) :
    expect p (fun ω => ((D.sample ω).edges.card : ℝ)) =
      ∑ e ∈ D.edges, p e.1 * p e.2 := by
  classical
  have h (ω : V → Bool) : ((D.sample ω).edges.card : ℝ) =
      ∑ e ∈ D.edges, keep {e.1, e.2} ω := by
    simp [Drawing.sample, keep]
  simp_rw [h]
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hne : e.1 ≠ e.2 := by
    intro h
    have hr := D.right e he
    rw [h] at hr
    exact lt_irrefl _ hr
  simp [expect_keep, hne]

lemma Drawing.expect_crossings (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P) (p : V → ℝ) :
    expect p (fun ω => ((D.sample ω).crossings.card : ℝ)) =
      ∑ ef ∈ D.crossings, p ef.1.1 * p ef.1.2 * p ef.2.1 * p ef.2.2 := by
  classical
  have h (ω : V → Bool) : ((D.sample ω).crossings.card : ℝ) =
      ∑ ef ∈ D.crossings, keep {ef.1.1, ef.1.2, ef.2.1, ef.2.2} ω := by
    simp [D.sample_crossings, keep]
  simp_rw [h]
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro ef hef
  have he := (Finset.mem_filter.mp hef)
  have ends := D.crossing_endpoints hP hx (Finset.mem_product.mp he.1).1
    (Finset.mem_product.mp he.1).2 (fun h => (ne_of_lt he.2.1) (congrArg edgeIndex h)) he.2.2
  rcases ends with ⟨h12, h34, h13, h14, h23, h24⟩
  simp [expect_keep, h12, h34, h13, h14, h23, h24, mul_assoc]

theorem Drawing.sample_crossing_bound (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    (p : V → ℝ) (hp : ∀ v, p v ∈ Set.Icc (0 : ℝ) 1) :
    (∑ e ∈ D.edges, p e.1 * p e.2) ≤ 3 * (∑ v ∈ D.vertices, p v) +
      ∑ ef ∈ D.crossings, p ef.1.1 * p ef.1.2 * p ef.2.1 * p ef.2.2 := by
  have h := expect_mono hp (fun ω =>
    (show ((D.sample ω).edges.card : ℝ) ≤
      3 * ((D.sample ω).vertices.card : ℝ) + ((D.sample ω).crossings.card : ℝ) from
      by exact_mod_cast (D.sample ω).linear_crossing_bound hP hx))
  rw [expect_add, expect_const_mul, D.expect_edges, D.expect_vertices,
    D.expect_crossings hP hx] at h
  exact h

omit [Fintype V] in
lemma Drawing.twoProb_edge {D : Drawing P} {A : Finset V} (hA : D.Bipartite A)
    (p q : ℝ) {e : V × V} (he : e ∈ D.edges) :
    twoProb A p q e.1 * twoProb A p q e.2 = p * q := by
  classical
  rcases hA e he with h | h <;> simp [twoProb, h.1, h.2, mul_comm]

omit [Fintype V] in
lemma Drawing.twoProb_vertices (D : Drawing P) (A : Finset V) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∑ v ∈ D.vertices, twoProb A p q v) ≤ p * A.card + q * D.vertices.card := by
  classical
  have h := Finset.sum_le_sum (s := D.vertices) (fun v _ =>
    show twoProb A p q v ≤ (if v ∈ A then p else 0) + q from by
      unfold twoProb
      split_ifs <;> linarith)
  rw [Finset.sum_add_distrib] at h
  have hc : ((D.vertices.filter (fun v => v ∈ A)).card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_le_card (show D.vertices.filter (fun v => v ∈ A) ⊆ A from
      fun v hv => (Finset.mem_filter.mp hv).2)
  calc (∑ v ∈ D.vertices, twoProb A p q v) ≤
      ∑ v ∈ D.vertices, (if v ∈ A then p else 0) + ∑ _v ∈ D.vertices, q := h
    _ = p * (D.vertices.filter (fun v => v ∈ A)).card + q * D.vertices.card := by
      simp [Finset.filter_mem_eq_inter, mul_comm]
    _ ≤ p * A.card + q * D.vertices.card := add_le_add (mul_le_mul_of_nonneg_left hc hp) le_rfl

lemma Drawing.bipartite_sample_bound (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    (A : Finset V) (hA : D.Bipartite A) (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    p * q * D.edges.card ≤ 3 * (p * A.card + q * D.vertices.card) +
      p ^ 2 * q ^ 2 * D.crossings.card := by
  classical
  have hh : ∀ v, twoProb A p q v ∈ Set.Icc (0 : ℝ) 1 := by
    intro v
    unfold twoProb
    split_ifs <;> assumption
  have h := D.sample_crossing_bound hP hx (twoProb A p q) hh
  have he : (∑ e ∈ D.edges, twoProb A p q e.1 * twoProb A p q e.2) = p * q * D.edges.card := by
    rw [Finset.sum_congr rfl (fun e he => D.twoProb_edge hA p q he)]
    simp [mul_comm]
  have hc : (∑ ef ∈ D.crossings, twoProb A p q ef.1.1 * twoProb A p q ef.1.2 *
      twoProb A p q ef.2.1 * twoProb A p q ef.2.2) = p ^ 2 * q ^ 2 * D.crossings.card := by
    have ht (ef) (hef : ef ∈ D.crossings) : twoProb A p q ef.1.1 * twoProb A p q ef.1.2 *
        twoProb A p q ef.2.1 * twoProb A p q ef.2.2 = p ^ 2 * q ^ 2 := by
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hef).1
      rw [mul_assoc (twoProb A p q ef.1.1 * twoProb A p q ef.1.2),
        D.twoProb_edge hA p q hh.1, D.twoProb_edge hA p q hh.2]
      ring
    rw [Finset.sum_congr rfl ht]
    simp [mul_comm]
  rw [he, hc] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (D.twoProb_vertices A p q hp.1 hq.1)
    (by norm_num : (0 : ℝ) ≤ 3)) le_rfl)

end PlanarHalving.PlaneGraph

namespace PlanarHalving.PlaneGraph

theorem crossing_sampling_algebra {m v e c : ℝ} (hm : 0 < m) (hv : 0 < v) (he : 0 < e)
    (h : (12 * v / e) * (12 * m / e) * e ≤
      3 * ((12 * v / e) * m + (12 * m / e) * v) +
        (12 * v / e) ^ 2 * (12 * m / e) ^ 2 * c) :
    e ^ 3 ≤ 288 * m * v * c := by
  have hK : 0 < 72 * m * v / e ^ 4 := by positivity
  have hh : (72 * m * v / e ^ 4) * e ^ 3 ≤
      (72 * m * v / e ^ 4) * (288 * m * v * c) := by
    calc (72 * m * v / e ^ 4) * e ^ 3 =
        (12 * v / e) * (12 * m / e) * e -
          3 * ((12 * v / e) * m + (12 * m / e) * v) := by field_simp; ring
      _ ≤ (12 * v / e) ^ 2 * (12 * m / e) ^ 2 * c := by linarith only [h]
      _ = (72 * m * v / e ^ 4) * (288 * m * v * c) := by ring
  exact (mul_le_mul_iff_right₀ hK).mp hh

end PlanarHalving.PlaneGraph

namespace PlanarHalving.PlaneGraph
open scoped BigOperators
open FiniteSampling
variable {V : Type*} [Fintype V] {P : V → Point}

theorem Drawing.bipartite_dense (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    (A : Finset V) (hA : D.Bipartite A) (hAv : A ⊆ D.vertices)
    (hd : 12 * (D.vertices.card : ℝ) ≤ D.edges.card) :
    (D.edges.card : ℝ) ^ 3 ≤ 288 * A.card * D.vertices.card * D.crossings.card := by
  classical
  by_cases hempty : D.edges = ∅
  · simp only [hempty, Finset.card_empty, Nat.cast_zero, zero_pow (by omega : 3 ≠ 0)]
    positivity
  have hen : D.edges.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨e, he⟩ := hen
  have hvn : D.vertices.Nonempty := ⟨e.1, (D.ends _ he).1⟩
  have hAn : A.Nonempty := by
    rcases hA e he with h | h
    · exact ⟨e.1, h.1⟩
    · exact ⟨e.2, h.2⟩
  have hepos : 0 < (D.edges.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr ⟨e,he⟩)
  have hvpos : 0 < (D.vertices.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hvn)
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hAn)
  have hAle : (A.card : ℝ) ≤ D.vertices.card := by exact_mod_cast Finset.card_le_card hAv
  have hp : 12 * (D.vertices.card : ℝ) / D.edges.card ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hepos).mpr hd⟩
  have hq : 12 * (A.card : ℝ) / D.edges.card ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hepos).mpr (by linarith)⟩
  exact crossing_sampling_algebra hApos hvpos hepos (D.bipartite_sample_bound hP hx A hA _ _ hp hq)

omit [Fintype V] in
lemma Drawing.cutSide_designated (D : Drawing P) (F : Finset V) (ω : ↥F → Bool) :
    D.cutSide F ω ⊆ F := by
  classical
  intro v hv
  have hh := (Finset.mem_filter.mp hv).2
  by_contra hn
  simp [bit, hn] at hh

omit [Fintype V] in
lemma Drawing.cut_bipartite (D : Drawing P) (F : Finset V) (ω : ↥F → Bool) :
    (D.cut F ω).Bipartite (D.cutSide F ω) := by
  classical
  intro e he
  have hh := Finset.mem_filter.mp he
  have hv := D.ends _ hh.1
  cases h₁ : bit F ω e.1 <;> cases h₂ : bit F ω e.2 <;>
    simp_all [Drawing.cutSide]

lemma Drawing.cut_crossings_le (D : Drawing P) (F : Finset V) (ω : ↥F → Bool) :
    (D.cut F ω).crossings.card ≤ D.crossings.card := by
  classical
  apply Finset.card_le_card
  intro ef he
  have hh := Finset.mem_filter.mp he
  have hedges := Finset.mem_product.mp hh.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨(Finset.mem_filter.mp hedges.1).1, (Finset.mem_filter.mp hedges.2).1⟩, hh.2⟩

omit [Fintype V] in
lemma Drawing.cut_edges (D : Drawing P) (F : Finset V) (ω : ↥F → Bool) :
    (D.cut F ω).edges = D.edges.filter (fun e => bit F ω e.1 ≠ bit F ω e.2) := rfl

omit [Fintype V] in
lemma Drawing.cut_card (D : Drawing P) (F : Finset V) (ω : ↥F → Bool) :
    ((D.cut F ω).edges.card : ℝ) =
      ∑ e ∈ D.edges, if bit F ω e.1 ≠ bit F ω e.2 then (1 : ℝ) else 0 := by
  classical
  rw [D.cut_edges F ω]
  simp only [Finset.sum_boole]

omit [Fintype V] in
lemma Drawing.expect_cut_card (D : Drawing P) (F : Finset V)
    (hF : ∀ e ∈ D.edges, e.1 ∈ F ∨ e.2 ∈ F) :
    expect (fun _ : ↥F => (1 : ℝ) / 2)
      (fun ω => ((D.cut F ω).edges.card : ℝ)) = (D.edges.card : ℝ) / 2 := by
  classical
  simp_rw [D.cut_card]
  rw [expect_sum]
  have hc (e) (he : e ∈ D.edges) :
      expect (fun _ : ↥F => (1 : ℝ) / 2)
        (fun ω => if bit F ω e.1 ≠ bit F ω e.2 then (1 : ℝ) else 0) = 1 / 2 := by
    apply expect_cut F _ (hF e he)
    intro h
    have hr := D.right e he
    rw [h] at hr
    exact lt_irrefl _ hr
  rw [Finset.sum_congr rfl hc]
  simp [div_eq_mul_inv]

omit [Fintype V] in
lemma Drawing.exists_large_cut (D : Drawing P) (F : Finset V)
    (hF : ∀ e ∈ D.edges, e.1 ∈ F ∨ e.2 ∈ F) :
    ∃ ω : ↥F → Bool, (D.edges.card : ℝ) / 2 ≤ (D.cut F ω).edges.card := by
  classical
  have hp : ∀ v : ↥F, (1 : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1 := by intro v; norm_num
  have hh := exists_ge_expect hp (fun ω => ((D.cut F ω).edges.card : ℝ))
  rw [D.expect_cut_card F hF] at hh
  exact hh

theorem Drawing.designated_dense (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    (F : Finset V) (hFv : F ⊆ D.vertices)
    (hF : ∀ e ∈ D.edges, e.1 ∈ F ∨ e.2 ∈ F)
    (hd : 24 * (D.vertices.card : ℝ) ≤ D.edges.card) :
    (D.edges.card : ℝ) ^ 3 ≤ 2304 * F.card * D.vertices.card * D.crossings.card := by
  classical
  obtain ⟨ω, hω⟩ := D.exists_large_cut F hF
  have hv : (D.cut F ω).vertices = D.vertices := rfl
  have hside := (D.cutSide_designated F ω).trans hFv
  have hden : 12 * ((D.cut F ω).vertices.card : ℝ) ≤ (D.cut F ω).edges.card := by
    rw [hv]
    linarith
  have hc := (D.cut F ω).bipartite_dense hP hx (D.cutSide F ω) (D.cut_bipartite F ω)
    (by simpa only [hv] using hside) hden
  rw [hv] at hc
  have hm : ((D.cutSide F ω).card : ℝ) ≤ F.card := by
    exact_mod_cast Finset.card_le_card (D.cutSide_designated F ω)
  have hcr : ((D.cut F ω).crossings.card : ℝ) ≤ D.crossings.card := by
    exact_mod_cast D.cut_crossings_le F ω
  have hbound : ((D.cut F ω).edges.card : ℝ) ^ 3 ≤
      288 * F.card * D.vertices.card * D.crossings.card := hc.trans (by gcongr)
  calc (D.edges.card : ℝ) ^ 3 ≤ (2 * ((D.cut F ω).edges.card : ℝ)) ^ 3 := by gcongr; linarith
    _ = 8 * ((D.cut F ω).edges.card : ℝ) ^ 3 := by ring
    _ ≤ 8 * (288 * F.card * D.vertices.card * D.crossings.card) := by gcongr
    _ = 2304 * F.card * D.vertices.card * D.crossings.card := by ring

theorem Drawing.designated_crossing_core (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    (F : Finset V) (hFv : F ⊆ D.vertices)
    (hF : ∀ e ∈ D.edges, e.1 ∈ F ∨ e.2 ∈ F) :
    (D.edges.card : ℝ) ^ 3 ≤ 2304 * F.card * D.vertices.card * D.crossings.card +
      13824 * (D.vertices.card : ℝ) ^ 3 := by
  by_cases hd : 24 * (D.vertices.card : ℝ) ≤ D.edges.card
  · exact (D.designated_dense hP hx F hFv hF hd).trans (le_add_of_nonneg_right (by positivity))
  · have he : (D.edges.card : ℝ) ≤ 24 * (D.vertices.card : ℝ) := (not_le.mp hd).le
    calc (D.edges.card : ℝ) ^ 3 ≤ (24 * (D.vertices.card : ℝ)) ^ 3 := by gcongr
      _ = 13824 * (D.vertices.card : ℝ) ^ 3 := by ring
      _ ≤ 2304 * F.card * D.vertices.card * D.crossings.card + 13824 * (D.vertices.card : ℝ) ^ 3 :=
        le_add_of_nonneg_left (by positivity)

lemma Drawing.crossings_card_eq (D : Drawing P) :
    D.crossings.card = ((↑(D.edges ×ˢ D.edges) : Set ((V × V) × (V × V))) ∩
      {ef | Fintype.equivFin (V × V) ef.1 < Fintype.equivFin (V × V) ef.2 ∧
        ¬ Disjoint (openSegment ℝ (P ef.1.1) (P ef.1.2)) (openSegment ℝ (P ef.2.1) (P ef.2.2))}).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  unfold Drawing.crossings
  rw [Finset.coe_filter]
  ext ef
  simp [Crosses, edgeIndex]

theorem designated_crossing_bound_oai {W : Type*} [Fintype W] (Q : W → Point)
    (hQ : Function.Injective Q ∧ ∀ i j l, i ≠ j → j ≠ l → i ≠ l → orient (Q i) (Q j) (Q l) ≠ 0)
    (hx : Function.Injective (fun v => (Q v).1))
    (vertices : Finset W) (edges : Finset (W × W))
    (hright : ∀ e ∈ edges, (Q e.1).1 < (Q e.2).1)
    (hends : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices)
    (F : Finset W) (hFv : F ⊆ vertices) (hF : ∀ e ∈ edges, e.1 ∈ F ∨ e.2 ∈ F) :
    (edges.card : ℝ) ^ 3 ≤ 2304 * F.card * vertices.card *
      ((↑(edges ×ˢ edges) : Set ((W × W) × (W × W))) ∩
        {ef | Fintype.equivFin (W × W) ef.1 < Fintype.equivFin (W × W) ef.2 ∧
          ¬ Disjoint (openSegment ℝ (Q ef.1.1) (Q ef.1.2)) (openSegment ℝ (Q ef.2.1) (Q ef.2.2))}).ncard + 13824 * (vertices.card : ℝ) ^ 3 := by
  have h := Drawing.designated_crossing_core (P := Q) hQ hx ⟨vertices, edges, hright, hends⟩ F hFv hF
  rw [Drawing.crossings_card_eq] at h
  exact h

end PlanarHalving.PlaneGraph

end OAI
end

theorem solution.{u_2} : type_of% @OAI.PlanarHalving.PlaneGraph.designated_crossing_bound_oai.{u_2} := @OAI.PlanarHalving.PlaneGraph.designated_crossing_bound_oai.{u_2}
