-- Prove2me | solution 1 for Hirsch.larman_layer_recursion
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T13:48:33.82605+00:00
-- url     : https://prove2.me/submissions/538d83d1-5c3d-4545-ae1f-94b12ab0d56c

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Theorems.Thm_Hirsch_kalai_kleitman_bound
import Theorems.Thm_Hirsch_tight_row_interval
import Theorems.Thm_Hirsch_gdist_reach

open scoped RealInnerProductSpace
open Hirsch

namespace LarmanAstra

open scoped Classical
set_option maxHeartbeats 1000000

/-- The combinatorial part of the greedy layer argument. The incidence relation
records the distance levels met by each row. -/
private theorem layers {n D M Bd : ℕ} (hit : Fin n → ℕ → Prop) (β : ℕ → ℕ)
    (bounded : ∀ r t, hit r t → t ≤ M)
    (covered : ∀ t ≤ D, ∃ r, hit r t)
    (interval : ∀ r p q t, hit r p → hit r q → p ≤ t → t ≤ q → hit r t)
    (step : ∀ l R r, hit r l → hit r R →
      (∀ j t, hit j l → hit j t → t ≤ R) →
      R ≤ l + β ((Finset.univ.filter fun j => ∃ t, hit j t ∧ l ≤ t ∧ t ≤ R).card))
    (arith : ∀ (k : ℕ) (m : Fin k → ℕ), (∀ i, 1 ≤ m i) →
      ∑ i, m i ≤ 2 * n → ∑ i, β (m i) + k ≤ Bd + 1) : D ≤ Bd := by
  classical
  let C (l : ℕ) : Finset ℕ := (Finset.range (M + 1)).filter fun t =>
    ∃ r, hit r l ∧ hit r t
  let N (l : ℕ) : ℕ := (C l).sup (fun t : ℕ => t)
  have memC (l t : ℕ) : t ∈ C l ↔ ∃ r, hit r l ∧ hit r t := by
    simp only [C, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact And.right
    · intro h
      obtain ⟨r, hr, ht⟩ := h
      exact ⟨by have := bounded r t ht; omega, r, hr, ht⟩
  have next_spec (l : ℕ) (hl : l ≤ D) :
      l ≤ N l ∧ ∃ r, hit r l ∧ hit r (N l) ∧
        ∀ j t, hit j l → hit j t → t ≤ N l := by
    obtain ⟨r, hr⟩ := covered l hl
    have hm : l ∈ C l := (memC l l).mpr ⟨r, hr, hr⟩
    have hmax : ∀ j t, hit j l → hit j t → t ≤ N l := by
      intro j t hj ht
      exact Finset.le_sup (f := id) ((memC l t).mpr ⟨j, hj, ht⟩)
    obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_sup (C l) ⟨l, hm⟩ id
    obtain ⟨q, hql, hqt⟩ := (memC l t).mp ht
    have he' : N l = t := he
    exact ⟨hmax r l hr hr, q, hql, he'.symm ▸ hqt, hmax⟩
  let s : ℕ → ℕ := fun i => Nat.rec (motive := fun _ => ℕ) 0 (fun _ x => max x (N x) + 1) i
  have s0 : s 0 = 0 := rfl
  have ss (i : ℕ) : s (i + 1) = max (s i) (N (s i)) + 1 := rfl
  have sm : StrictMono s := strictMono_nat_of_lt_succ fun i => by
    rw [ss]; have := le_max_left (s i) (N (s i)); omega
  have ids (i : ℕ) : i ≤ s i := by
    induction i with
    | zero => omega
    | succ i ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (sm (Nat.lt_succ_self i)))
  have ex : ∃ i, D < s i := ⟨D + 1, by have := ids (D + 1); omega⟩
  let k : ℕ := @Nat.find (fun i : ℕ => D < s i) (fun _ => Classical.propDecidable _) ex
  have hk : D < s k := @Nat.find_spec (fun i : ℕ => D < s i) (fun _ => Classical.propDecidable _) ex
  have before (i : ℕ) (hi : i < k) : s i ≤ D := by
    have := @Nat.find_min (fun i : ℕ => D < s i) (fun _ => Classical.propDecidable _) ex i hi
    omega
  have good (i : ℕ) (hi : i < k) : s (i + 1) = N (s i) + 1 := by
    rw [ss, max_eq_right (next_spec (s i) (before i hi)).1]
  let T (i : ℕ) : Finset (Fin n) := @Finset.filter (Fin n)
    (fun j : Fin n => ∃ t : ℕ, hit j t ∧ s i ≤ t ∧ t < s (i + 1))
    (fun _ => Classical.propDecidable _) Finset.univ
  have memT (i : ℕ) (j : Fin n) :
      j ∈ T i ↔ ∃ t, hit j t ∧ s i ≤ t ∧ t < s (i + 1) := by simp [T]
  have T_eq (i : ℕ) (hi : i < k) : T i =
      @Finset.filter (Fin n) (fun j => ∃ t, hit j t ∧ s i ≤ t ∧ t ≤ N (s i))
        (fun _ => Classical.propDecidable _) Finset.univ := by
    ext j; simp only [memT, Finset.mem_filter, Finset.mem_univ, true_and, good i hi]
    simp only [Nat.lt_succ_iff]
  have positive (i : ℕ) (hi : i < k) : 1 ≤ (T i).card := by
    obtain ⟨r, hr⟩ := covered (s i) (before i hi)
    exact Finset.card_pos.mpr ⟨r, (memT i r).mpr ⟨s i, hr, le_rfl,
      sm (Nat.lt_succ_self i)⟩⟩
  have width (i : ℕ) (hi : i < k) :
      s (i + 1) ≤ s i + (β (T i).card + 1) := by
    obtain ⟨_, r, hrl, hrR, hmax⟩ := next_spec (s i) (before i hi)
    have h := step (s i) (N (s i)) r hrl hrR hmax
    rw [← T_eq i hi] at h
    rw [good i hi]
    omega
  have separated (i j : ℕ) (hj : j < k) (hij : i + 2 ≤ j) (r : Fin n)
      (hri : r ∈ T i) (hrj : r ∈ T j) : False := by
    obtain ⟨p, hp, hpl, hpu⟩ := (memT i r).mp hri
    obtain ⟨q, hq, hql, hqu⟩ := (memT j r).mp hrj
    have hlevels : s (i + 1) ≤ s j := sm.monotone (a := i + 1) (b := j) (by omega)
    have hrmid : hit r (s (i + 1)) :=
      interval r p q (s (i + 1)) hp hq (by omega) (by omega)
    have hmax := (next_spec (s (i + 1)) (before (i + 1) (by omega))).2
    obtain ⟨_, _, _, hmax⟩ := hmax
    have hqmax := hmax r q hrmid hq
    have hnext : s (i + 2) = N (s (i + 1)) + 1 := good (i + 1) (by omega)
    have hsep : s (i + 2) ≤ s j := sm.monotone hij
    omega
  have count (r : Fin n) : (Finset.univ.filter fun i : Fin k => r ∈ T i.val).card ≤ 2 := by
    let F : Finset (Fin k) := Finset.univ.filter fun i => r ∈ T i.val
    change F.card ≤ 2
    by_cases hF : F.Nonempty
    · let p := F.min' hF
      have hp : p ∈ F := Finset.min'_mem F hF
      have hpr : r ∈ T p.val := (Finset.mem_filter.mp hp).2
      have inj := Finset.card_le_card_of_injOn (s := F)
        (t := Finset.Icc p.val (p.val + 1)) Fin.val
        (fun q hq => ?_) (fun _ _ _ _ h => Fin.ext h)
      · simp only [Nat.card_Icc] at inj
        omega
      · have hpq : p ≤ q := Finset.min'_le F q hq
        have hqr : r ∈ T q.val := (Finset.mem_filter.mp hq).2
        have hn : ¬ p.val + 2 ≤ q.val := fun h => separated p.val q.val q.isLt h r hpr hqr
        exact Finset.mem_Icc.mpr ⟨hpq, by omega⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp hF]; simp
  have total : ∑ i : Fin k, (T i.val).card ≤ 2 * n := by
    calc
      ∑ i : Fin k, (T i.val).card =
          ∑ r : Fin n, (Finset.univ.filter fun i : Fin k => r ∈ T i.val).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        simp only [← Finset.sum_filter]
        simp
      _ ≤ ∑ _r : Fin n, 2 := Finset.sum_le_sum fun r _ => count r
      _ = 2 * n := by simp [Nat.mul_comm]
  have telescope : ∀ j ≤ k, s j ≤ ∑ i ∈ Finset.range j, (β (T i).card + 1) := by
    intro j hj
    induction j with
    | zero => simp [s0]
    | succ j ih =>
      have h := width j (by omega)
      have h' := ih (by omega)
      rw [Finset.sum_range_succ]
      omega
  have ht := telescope k le_rfl
  have ha := arith k (fun i => (T i.val).card) (fun i => positive i.val i.isLt) total
  have he : (∑ i ∈ Finset.range k, (β (T i).card + 1)) =
      (∑ i : Fin k, β (T i.val).card) + k := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [Finset.sum_add_distrib]
  rw [he] at ht
  have hsBd : s k ≤ Bd + 1 := ht.trans ha
  omega


section Walk

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem reach_succ (P : Set E) (L : ℕ) (u v : E) (h : Reach P L u v) :
    Reach P (L + 1) u v := by
  classical
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun i => if i ≤ L then w i else v, by simpa using h0, by simp, ?_⟩
  intro i hi
  rcases lt_or_ge i L with h1 | h1
  · have hi1 : i + 1 ≤ L := h1
    simp only [if_pos h1.le, if_pos hi1]
    exact hstep i h1
  · have hiL : i = L := by omega
    subst hiL
    left
    simp [hL]

private theorem reach_mono (P : Set E) {L L' : ℕ} (hLL : L ≤ L') {u v : E} (h : Reach P L u v) :
    Reach P L' u v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hLL
  clear hLL
  induction k with
  | zero => simpa using h
  | succ m ih => exact (Nat.add_succ L m) ▸ reach_succ P _ u v ih


private theorem adj_right_mem_extremePoints {P : Set E} {a b : E} (h : Adj P a b) :
    b ∈ Set.extremePoints ℝ P := by
  have hb : b ∈ Set.extremePoints ℝ (segment ℝ a b) := by
    refine ⟨right_mem_segment ℝ a b, ?_⟩
    rintro x hx y hy ⟨p, q, hp, hq, hpq, hxy⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h.1)
    rw [segment_eq_image'] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hb' : b = a + (1:ℝ) • (b - a) := by module
    have hcomb : p • (a + s • (b - a)) + q • (a + t • (b - a))
        = a + (p * s + q * t) • (b - a) := by
      calc p • (a + s • (b - a)) + q • (a + t • (b - a))
          = (p + q) • a + (p * s + q * t) • (b - a) := by module
        _ = a + (p * s + q * t) • (b - a) := by rw [hpq]; module
    have hb2 : a + (p * s + q * t) • (b - a) = b := by rw [← hcomb]; exact hxy
    have hco : p * s + q * t = 1 := by
      have h3 : ((p * s + q * t) - 1) • (b - a) = 0 := by
        have e1 : ((p * s + q * t) - 1) • (b - a)
            = (a + (p * s + q * t) • (b - a)) - (a + (1:ℝ) • (b - a)) := by module
        rw [e1, hb2, ← hb', sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith [sub_eq_zero.mp h4]
      · exact absurd h4 hba
    have hs1 : s = 1 := by
      have h5 : p * s + q * t ≤ p * 1 + q * 1 := by
        have := hs.2; have := ht.2
        nlinarith
      nlinarith [hs.2, ht.2, hs.1, ht.1]
    rw [hs1]
    module
  have := h.2.extremePoints_eq (𝕜 := ℝ)
  rw [this] at hb
  exact hb.2

private theorem reach_trans (P : Set E) {L₁ L₂ : ℕ} {u x v : E}
    (h₁ : Reach P L₁ u x) (h₂ : Reach P L₂ x v) : Reach P (L₁ + L₂) u v := by
  classical
  obtain ⟨w₁, a1, b1, s1⟩ := h₁
  obtain ⟨w₂, a2, b2, s2⟩ := h₂
  refine ⟨fun i => if i ≤ L₁ then w₁ i else w₂ (i - L₁), by simpa using a1, ?_, ?_⟩
  · dsimp only
    by_cases hc : L₁ + L₂ ≤ L₁
    · have hz : L₂ = 0 := by omega
      subst hz
      rw [if_pos hc]
      simpa using b1.trans (by rw [← a2, ← b2])
    · rw [if_neg hc]
      have : L₁ + L₂ - L₁ = L₂ := by omega
      rw [this]; exact b2
  · intro i hi
    dsimp only
    by_cases hc : i ≤ L₁
    · by_cases hc1 : i + 1 ≤ L₁
      · rw [if_pos hc, if_pos hc1]; exact s1 i (by omega)
      · have hiL : i = L₁ := by omega
        subst hiL
        rw [if_pos hc, if_neg hc1]
        have : i + 1 - i = 1 := by omega
        rw [this, b1, ← a2]
        exact s2 0 (by omega)
    · rw [if_neg hc, if_neg (by omega : ¬ (i + 1 ≤ L₁))]
      have : i + 1 - L₁ = (i - L₁) + 1 := by omega
      rw [this]
      exact s2 _ (by omega)

private theorem reach_mem_extremePoints {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E}
    {L : ℕ} {u v : E} (hu : u ∈ Set.extremePoints ℝ P) (h : Reach P L u v) :
    v ∈ Set.extremePoints ℝ P := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  have key : ∀ i, i ≤ L → w i ∈ Set.extremePoints ℝ P := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact hu
    | succ i ih =>
        intro hi
        rcases hstep i (by omega) with he | hadj
        · rw [← he]; exact ih (by omega)
        · exact adj_right_mem_extremePoints hadj
  rw [← hL]; exact key L (le_refl L)

/-- A walk of length `L` contains walks of every shorter length to its intermediate
points. -/
private theorem reach_prefix {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E} {L : ℕ} {u : E}
    {w : ℕ → E} (h0 : w 0 = u)
    (hstep : ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))) {r : ℕ} (hr : r ≤ L) :
    Reach P r u (w r) :=
  ⟨w, h0, rfl, fun i hi => hstep i (lt_of_lt_of_le hi hr)⟩

end Walk

/-- A shortest walk has a vertex at each distance level. -/
private theorem exists_level (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (t : ℕ) (ht : t ≤ gdist (Hpoly a b) u v) :
    ∃ w ∈ Set.extremePoints ℝ (Hpoly a b), gdist (Hpoly a b) u w = t := by
  let D := gdist (Hpoly a b) u v
  obtain ⟨w, h0, hD, hs⟩ := gdist_reach d n a b hbd u v hu hv
  have hp : Reach (Hpoly a b) t u (w t) := reach_prefix h0 hs ht
  have hw := reach_mem_extremePoints hu hp
  refine ⟨w t, hw, ?_⟩
  have hshort := gdist_reach d n a b hbd u (w t) hu hw
  have htail : Reach (Hpoly a b) (D - t) (w t) v := by
    refine ⟨fun i => w (t + i), by simp, ?_, ?_⟩
    · change w (t + (D - t)) = v
      rw [Nat.add_sub_of_le (show t ≤ D from ht)]
      exact hD
    · intro i hi
      simpa only [Nat.add_assoc] using hs (t + i) (by change t + i < D; omega)
  have hlow : D ≤ gdist (Hpoly a b) u (w t) + (D - t) :=
    Nat.sInf_le (reach_trans (Hpoly a b) hshort htail)
  have hupp : gdist (Hpoly a b) u (w t) ≤ t := Nat.sInf_le hp
  change t ≤ D at ht
  omega

end LarmanAstra

open LarmanAstra

theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hane : ∀ j, a j ≠ 0) (hbd : Bornology.IsBounded (Hpoly a b))
    (htight : ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), ∃ j, ⟪a j, v⟫ = b j)
    (β : ℕ → ℕ) (Bd : ℕ)
    (hstep : ∀ u ∈ Set.extremePoints ℝ (Hpoly a b), ∀ (r : Fin n) (T : Finset (Fin n)), r ∈ T →
      ∀ y ∈ Set.extremePoints ℝ (Hpoly a b), ∀ z ∈ Set.extremePoints ℝ (Hpoly a b),
      ⟪a r, y⟫ = b r → ⟪a r, z⟫ = b r →
      (∀ j, ⟪a j, y⟫ = b j → j ∈ T) → (∀ j, ⟪a j, z⟫ = b j → j ∈ T) →
      (∀ w ∈ Set.extremePoints ℝ (Hpoly a b), ⟪a r, w⟫ = b r →
        (∃ j, j ∉ T ∧ ⟪a j, w⟫ = b j) → gdist (Hpoly a b) u w + 1 ≤ gdist (Hpoly a b) u y) →
      gdist (Hpoly a b) u z ≤ gdist (Hpoly a b) u y + β T.card)
    (harith : ∀ (k : ℕ) (m : Fin k → ℕ), (∀ i, 1 ≤ m i) →
      ∑ i, m i ≤ 2 * n → ∑ i, β (m i) + k ≤ Bd + 1) :
    DiamLE (Hpoly a b) Bd := by
  classical
  intro u hu v hv
  have hreach := gdist_reach d n a b hbd u v hu hv
  apply LarmanAstra.reach_mono (Hpoly a b) (L := gdist (Hpoly a b) u v) (L' := Bd) _ hreach
  let ρ := gdist (Hpoly a b) u
  let M := ⌊(n : ℝ) ^ (Real.logb 2 d + 2)⌋₊
  have hdiam : DiamLE (Hpoly a b) M :=
    kalai_kleitman_bound d n a b ⟨u, hu.1⟩ hbd
  have hbound (w : EuclideanSpace ℝ (Fin d))
      (hw : w ∈ Set.extremePoints ℝ (Hpoly a b)) : ρ w ≤ M :=
    Nat.sInf_le (hdiam u hu w hw)
  let hit : Fin n → ℕ → Prop := fun r t =>
    ∃ w ∈ Set.extremePoints ℝ (Hpoly a b), ⟪a r, w⟫ = b r ∧ ρ w = t
  apply LarmanAstra.layers (D := ρ v) (M := M) hit β
  · intro r t ht
    obtain ⟨w, hw, _, he⟩ := ht
    rw [← he]
    exact hbound w hw
  · intro t ht
    obtain ⟨w, hw, he⟩ := LarmanAstra.exists_level d n a b hbd u v hu hv t ht
    obtain ⟨r, hr⟩ := htight w hw
    exact ⟨r, w, hw, hr, he⟩
  · intro r p q t hp hq hpt htq
    obtain ⟨x, hx, hxr, hxp⟩ := hp
    obtain ⟨y, hy, hyr, hyq⟩ := hq
    obtain ⟨w, hw, hwr, hwt⟩ := tight_row_interval d n a b hbd u hu r x y hx hy hxr hyr t
      (by change ρ x ≤ t; omega) (by change t ≤ ρ y; omega)
    exact ⟨w, hw, hwr, hwt⟩
  · intro l R r hrl hrR hmax
    obtain ⟨y, hy, hyr, hyl⟩ := hrl
    obtain ⟨z, hz, hzr, hzR⟩ := hrR
    have hrl : hit r l := ⟨y, hy, hyr, hyl⟩
    have hlR : l ≤ R := hmax r l hrl hrl
    let T : Finset (Fin n) := Finset.univ.filter fun j => ∃ t, hit j t ∧ l ≤ t ∧ t ≤ R
    have memT (j : Fin n) : j ∈ T ↔ ∃ t, hit j t ∧ l ≤ t ∧ t ≤ R := by simp [T]
    have hyT (j : Fin n) (hj : ⟪a j, y⟫ = b j) : j ∈ T :=
      (memT j).mpr ⟨l, ⟨y, hy, hj, hyl⟩, le_rfl, hlR⟩
    have hzT (j : Fin n) (hj : ⟪a j, z⟫ = b j) : j ∈ T :=
      (memT j).mpr ⟨R, ⟨z, hz, hj, hzR⟩, hlR, le_rfl⟩
    have back : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b), ⟪a r, w⟫ = b r →
        (∃ j, j ∉ T ∧ ⟪a j, w⟫ = b j) → ρ w + 1 ≤ ρ y := by
      intro w hw hwr houtside
      obtain ⟨j, hj, hjw⟩ := houtside
      have hwR : ρ w ≤ R := hmax r (ρ w) hrl ⟨w, hw, hwr, rfl⟩
      have hwlt : ρ w < l := by
        by_contra hn
        exact hj ((memT j).mpr ⟨ρ w, ⟨w, hw, hjw, rfl⟩, by omega, hwR⟩)
      omega
    have h := hstep u hu r T (hyT r hyr) y hy z hz hyr hzr hyT hzT back
    change ρ z ≤ ρ y + β T.card at h
    rw [hzR, hyl] at h
    exact h
  · exact harith
