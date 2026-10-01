-- Prove2me | solution 1 for LovaszSchrijver.Defect.tightGraph_not_colorable_two
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:58:34.784991+00:00
-- url     : https://prove2.me/submissions/cb13b506-08b8-462b-8765-9341d4f89063

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Index
open Finset Matrix LovaszSchrijver.Defect
open Filter Topology
namespace ALSD
variable {V : Type} [Fintype V] [DecidableEq V]

lemma midpoint_max (G : SimpleGraph V) (a x y : V → ℝ)
    (hx : IsFRACMaximizer G a x) (hy : IsFRACMaximizer G a y) :
    IsFRACMaximizer G a (fun i => (x i + y i) / 2) := by
  have he : a ⬝ᵥ x = a ⬝ᵥ y := le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)
  have hd : a ⬝ᵥ (fun i => (x i + y i) / 2) = (a ⬝ᵥ x + a ⬝ᵥ y) / 2 := by
    simp only [dotProduct, mul_div, mul_add]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; linarith [hx.1.1 i, hy.1.1 i]
  · intro i j hij; linarith [hx.1.2 i j hij, hy.1.2 i j hij]
  · intro z hz; rw [hd, he]; linarith [hy.2 z hz]

lemma central (G : SimpleGraph V) (a : V → ℝ)
    (hne : ∃ y, IsFRACMaximizer G a y) :
    ∃ y, IsFRACMaximizer G a y ∧ ∀ i j, G.Adj i j → y i + y j = 1 → (tightGraph G a).Adj i j := by
  classical
  let E (y : V → ℝ) := Finset.univ.filter (fun ij : V × V => G.Adj ij.1 ij.2 ∧ y ij.1 + y ij.2 = 1)
  have hex : ∃ n : ℕ, ∃ y, IsFRACMaximizer G a y ∧ (E y).card = n := by
    obtain ⟨y, hy⟩ := hne; exact ⟨_, y, hy, rfl⟩
  obtain ⟨y, hy, he⟩ := Nat.find_spec hex
  refine ⟨y, hy, ?_⟩
  intro i j hij ht
  refine ⟨hij, ?_⟩
  intro x hx
  by_contra hn
  let z : V → ℝ := fun i => (x i + y i) / 2
  have hz := midpoint_max G a x y hx hy
  have hsub : E z ⊆ E y := by
    intro ij hm
    have hm' := (Finset.mem_filter.mp hm).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'.1, ?_⟩
    have hx' := hx.1.2 _ _ hm'.1
    have hy' := hy.1.2 _ _ hm'.1
    dsimp [z] at hm'
    linarith [hm'.2]
  have hnot : (i,j) ∉ E z := by
    intro hm
    have hm' := (Finset.mem_filter.mp hm).2.2
    dsimp [z] at hm'
    apply hn; linarith
  have hlt : (E z).card < (E y).card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun h => hnot (h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, ht⟩)⟩)
  have hmin := Nat.find_min' hex (show ∃ w, IsFRACMaximizer G a w ∧ (E w).card = (E z).card from ⟨z, hz, rfl⟩)
  omega

lemma extend_feasible (G : SimpleGraph V) (y z : V → ℝ) (hy : y ∈ FRAC G)
    (hz0 : ∀ i, y i = 0 → z i = 0)
    (hze : ∀ i j, G.Adj i j → y i + y j = 1 → z i + z j = 1) :
    ∃ t : ℝ, 0 < t ∧ (fun i => y i + t * (y i - z i)) ∈ FRAC G := by
  have hn (i : V) : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ y i + t * (y i - z i) := by
    by_cases hi : y i = 0
    · simp [hi, hz0 i hi]
    · have hp : 0 < y i := lt_of_le_of_ne (hy.1 i) (Ne.symm hi)
      have hc : ContinuousAt (fun t : ℝ => y i + t * (y i - z i)) 0 := by fun_prop
      filter_upwards [hc.tendsto.eventually (lt_mem_nhds (by simpa using hp))] with t ht
      exact ht.le
  have he (i j : V) : ∀ᶠ t : ℝ in 𝓝 0,
      G.Adj i j → (y i + t * (y i - z i)) + (y j + t * (y j - z j)) ≤ 1 := by
    by_cases hij : G.Adj i j
    · by_cases hh : y i + y j = 1
      · have hz := hze i j hij hh
        filter_upwards [] with t _
        apply le_of_eq
        linear_combination (1+t)*hh-t*hz
      · have hl : y i + y j < 1 := lt_of_le_of_ne (hy.2 i j hij) hh
        have hc : ContinuousAt (fun t : ℝ => (y i + t * (y i - z i)) + (y j + t * (y j - z j))) 0 := by fun_prop
        filter_upwards [hc.tendsto.eventually (gt_mem_nhds (by simpa using hl))] with t ht _
        exact ht.le
    · simp [hij]
  have hall : ∀ᶠ t : ℝ in 𝓝 0, (fun i => y i + t * (y i - z i)) ∈ FRAC G := by
    filter_upwards [Filter.eventually_all.mpr hn, Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (he i))] with t hn he
    exact ⟨hn, he⟩
  obtain ⟨ε, hε, heps⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ε/2, by positivity, heps ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
  exact half_lt_self hε

lemma colors {x y : Fin 2} (h : x ≠ y) : (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0) := by
  fin_cases x <;> fin_cases y <;> simp_all

lemma rounding (G : SimpleGraph V) (a y : V → ℝ) (hy : y ∈ FRAC G)
    (hcent : ∀ i j, G.Adj i j → y i + y j = 1 → (tightGraph G a).Adj i j)
    (C : (tightGraph G a).Coloring (Fin 2)) :
    ∃ z ∈ STAB G, (∀ i, y i = 0 → z i = 0) ∧
      (∀ i j, G.Adj i j → y i + y j = 1 → z i + z j = 1) := by
  classical
  let A := Finset.univ.filter (fun i => 1/2 < y i ∨ y i = 1/2 ∧ C i = 0)
  have hA (i : V) : i ∈ A ↔ 1/2 < y i ∨ y i = 1/2 ∧ C i = 0 := by simp [A]
  have hstable : G.IsIndepSet (A : Set V) := by
    intro i hi j hj hne hij
    have hi := (hA i).mp hi
    have hj := (hA j).mp hj
    have he := hy.2 i j hij
    rcases hi with hi | ⟨hi, hci⟩ <;> rcases hj with hj | ⟨hj, hcj⟩
    · linarith
    · linarith
    · linarith
    · exact C.valid (hcent i j hij (by linarith)) (hci.trans hcj.symm)
  refine ⟨chi A, subset_convexHull ℝ _ ⟨A, hstable, rfl⟩, ?_, ?_⟩
  · intro i hi
    have hnot : i ∉ A := by rw [hA, hi]; norm_num
    simp [chi, hnot]
  · intro i j hij he
    have hcol := colors (C.valid (hcent i j hij he))
    rcases lt_trichotomy (y i) (1/2) with hi | hi | hi
    · have hj : 1/2 < y j := by linarith
      have hni : i ∉ A := by rw [hA]; push_neg; exact ⟨hi.le, fun hh => by linarith⟩
      have hmj : j ∈ A := (hA j).mpr (Or.inl hj)
      simp [chi, hni, hmj]
    · have hj : y j = 1/2 := by linarith
      rcases hcol with ⟨hci, hcj⟩ | ⟨hcj, hci⟩
      · have hmi : i ∈ A := (hA i).mpr (Or.inr ⟨hi, hci⟩)
        have hnj : j ∉ A := by simp [hA, hj, hcj]
        simp [chi, hmi, hnj]
      · have hmj : j ∈ A := (hA j).mpr (Or.inr ⟨hj, hcj⟩)
        have hni : i ∉ A := by simp [hA, hi, hci]
        simp [chi, hni, hmj]
    · have hj : y j < 1/2 := by linarith
      have hnj : j ∉ A := by rw [hA]; push_neg; exact ⟨hj.le, fun hh => by linarith⟩
      have hmi : i ∈ A := (hA i).mpr (Or.inl hi)
      simp [chi, hmi, hnj]

lemma not_colorable (G : SimpleGraph V) (a : V → ℝ) (sS sF : ℝ)
    (hS : IsGreatest {s : ℝ | ∃ x ∈ STAB G, s = a ⬝ᵥ x} sS)
    (hF : IsGreatest {s : ℝ | ∃ x ∈ FRAC G, s = a ⬝ᵥ x} sF)
    (hlt : sS < sF) : ¬ (tightGraph G a).Colorable 2 := by
  rintro ⟨C⟩
  obtain ⟨x, hx, hsF⟩ := hF.1
  have hxmax : IsFRACMaximizer G a x := ⟨hx, fun z hz => by
    have := hF.2 ⟨z, hz, rfl⟩; simpa [hsF] using this⟩
  obtain ⟨y, hy, hcent⟩ := central G a ⟨x, hxmax⟩
  have hye : a ⬝ᵥ y = sF := by
    have h1 := hy.2 x hx
    have h2 := hF.2 ⟨y, hy.1, rfl⟩
    linarith
  obtain ⟨z, hz, hz0, hze⟩ := rounding G a y hy.1 hcent C
  obtain ⟨t, ht, hfeas⟩ := extend_feasible G y z hy.1 hz0 hze
  have hd : a ⬝ᵥ (fun i => y i + t * (y i - z i)) = a ⬝ᵥ y + t * (a ⬝ᵥ y - a ⬝ᵥ z) := by
    simp only [dotProduct]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmax := hy.2 _ hfeas
  rw [hd] at hmax
  have hle : a ⬝ᵥ y ≤ a ⬝ᵥ z := by nlinarith
  have hs := hS.2 ⟨z, hz, rfl⟩
  linarith
lemma walk_alternation (H : SimpleGraph V) (y : V → ℝ)
    (he : ∀ i j, H.Adj i j → y i + y j = 1) {u v : V} (w : H.Walk u v) :
    y v - 1/2 = (-1 : ℝ)^w.length * (y u - 1/2) := by
  induction w with
  | nil => simp
  | @cons u v z huv w ih =>
    rw [SimpleGraph.Walk.length_cons, pow_succ, ih]
    linear_combination ((-1 : ℝ)^w.length) * (he u v huv)

lemma exists_half (G : SimpleGraph V) (a : V → ℝ)
    (hnc : ¬ (tightGraph G a).Colorable 2) :
    ∃ i : V, ∀ y : V → ℝ, IsFRACMaximizer G a y → y i = 1/2 := by
  classical
  by_contra hn
  push_neg at hn
  apply hnc
  rw [SimpleGraph.two_colorable_iff_forall_loop_even]
  intro v w
  by_contra ho
  obtain ⟨y, hy, hne⟩ := hn v
  have he := walk_alternation (tightGraph G a) y (fun i j hij => hij.2 y hy) w
  rw [(Nat.not_even_iff_odd.mp ho).neg_one_pow] at he
  apply hne
  linarith
end ALSD

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (ha : ∀ i, 0 ≤ a i) (sS sF : ℝ)
    (hS : IsGreatest {s : ℝ | ∃ x ∈ STAB G, s = a ⬝ᵥ x} sS)
    (hF : IsGreatest {s : ℝ | ∃ x ∈ FRAC G, s = a ⬝ᵥ x} sF)
    (hlt : sS < sF) :
    ¬ (tightGraph G a).Colorable 2  := by
  exact ALSD.not_colorable G a sS sF hS hF hlt
