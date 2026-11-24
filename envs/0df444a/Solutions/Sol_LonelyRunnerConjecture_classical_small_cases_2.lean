-- Prove2me | solution 2 for LonelyRunnerConjecture.classical_small_cases
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:43:05.872207+00:00
-- url     : https://prove2.me/submissions/a695049f-603c-48b0-a142-e93488c3c8ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs
import Theorems.Thm_LefebvreVariations_lonely_runner_small_coprime_no_top_gap

set_option autoImplicit false

open LonelyRunnerConjecture


private lemma dist_eq (x : ℝ) : distToNearestInt x = |x - round x| :=
  (abs_sub_round_eq_min x).symm

private lemma le_dist (δ x : ℝ) (h : ∀ z : ℤ, δ ≤ |x - z|) : δ ≤ distToNearestInt x := by
  rw [dist_eq]; exact h _

private lemma dist_lip (x y : ℝ) : distToNearestInt y ≤ distToNearestInt x + |x - y| := by
  rw [dist_eq y, dist_eq x]
  calc |y - round y| ≤ |y - round x| := round_le y (round x)
    _ = |(x - round x) + (y - x)| := by ring_nf
    _ ≤ |x - round x| + |y - x| := abs_add_le _ _
    _ = |x - round x| + |x - y| := by rw [abs_sub_comm y x]

/-- Within `δ` of any real there is a point at distance at least `δ` from `ℤ`. -/
private lemma near (δ y : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ x : ℝ, |x - y| ≤ δ ∧ δ ≤ distToNearestInt x := by
  set r : ℤ := round y
  by_cases hy : δ ≤ |y - r|
  · exact ⟨y, by simp [hδ.le], le_dist δ y fun z => hy.trans (round_le y z)⟩
  push Not at hy
  rw [abs_lt] at hy
  by_cases hs : (r : ℝ) ≤ y
  · refine ⟨r + δ, ?_, le_dist δ _ fun z => ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · rcases lt_trichotomy z r with h | h | h
      · have : (z : ℝ) + 1 ≤ r := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
      · subst h; simp [abs_of_pos hδ]
      · have : (r : ℝ) + 1 ≤ z := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
  · push Not at hs
    refine ⟨r - δ, ?_, le_dist δ _ fun z => ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · rcases lt_trichotomy z r with h | h | h
      · have : (z : ℝ) + 1 ≤ r := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
      · subst h; simp [abs_of_pos hδ]
      · have : (r : ℝ) + 1 ≤ z := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith

private lemma frac_good (m n r : ℕ) (hn : 0 < n) (hr : m % n = r) (h3 : n ≤ 3 * r)
    (h3' : 3 * r ≤ 2 * n) : ∀ z : ℤ, 1 / 3 ≤ |(m : ℝ) / n - z| := by
  intro z
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨q, hq⟩ : ∃ q, q = m / n := ⟨_, rfl⟩
  have hm : (m : ℝ) = n * q + r := by
    rw [← hr, hq]; exact_mod_cast (Nat.div_add_mod m n).symm
  have h3r : (n : ℝ) ≤ 3 * r := by exact_mod_cast h3
  have h3r' : 3 * (r : ℝ) ≤ 2 * n := by exact_mod_cast h3'
  have e : (m : ℝ) / n - z = (((q : ℤ) - z : ℤ) : ℝ) + (r : ℝ) / n := by
    rw [hm]; push_cast; field_simp; ring
  have hρ1 : 1 / 3 ≤ (r : ℝ) / n := by rw [le_div_iff₀ hnr]; linarith
  have hρ2 : (r : ℝ) / n ≤ 2 / 3 := by rw [div_le_iff₀ hnr]; linarith
  rw [e]
  rcases le_or_gt 0 ((q : ℤ) - z) with h | h
  · have : (0 : ℝ) ≤ ((((q : ℤ) - z : ℤ)) : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have h' : ((q : ℤ) - z : ℤ) ≤ -1 := by omega
    have : ((((q : ℤ) - z : ℤ)) : ℝ) ≤ -1 := by exact_mod_cast h'
    rw [abs_of_neg (by linarith)]; linarith

/-- Wills: two coprime speeds have a lonely time. -/
private lemma wills (S : Finset ℕ) (hS : S.card = 2) (hpos : ∀ v ∈ S, 0 < v)
    (hgcd : S.gcd id = 1) :
    ∃ t : ℝ, ∀ v ∈ S, (1 : ℝ) / ((2 : ℕ) + 1 : ℝ) ≤ distToNearestInt (t * (v : ℝ)) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hS
  have ha : 0 < a := hpos a (by simp)
  have hb : 0 < b := hpos b (by simp)
  have hcop : Nat.Coprime a b := by
    have : gcd a b = 1 := by simpa [Finset.gcd_insert] using hgcd
    exact this
  set n := a + b
  have hn3 : 3 ≤ n := by omega
  have hcopn : Nat.Coprime a n := Nat.coprime_self_add_right.2 hcop
  set r := (n + 2) / 3
  have hrn : r < n := by omega
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_of_coprime r hcopn (by omega)
  rw [Nat.mod_eq_of_lt hrn] at hj
  have hgood := frac_good (a * j) n r (by omega) hj (by omega) (by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨(j : ℝ) / n, fun v hv => ?_⟩
  have h13 : (1 : ℝ) / ((2 : ℕ) + 1 : ℝ) = 1 / 3 := by norm_num
  rw [h13]
  apply le_dist
  intro z
  rcases Finset.mem_insert.1 hv with rfl | hv
  · have e : (j : ℝ) / n * v = ((v * j : ℕ) : ℝ) / n := by push_cast; ring
    rw [e]; exact hgood z
  · rw [Finset.mem_singleton] at hv
    subst hv
    have e : (j : ℝ) / n * v - z = -(((a * j : ℕ) : ℝ) / n - ((j : ℤ) - z : ℤ)) := by
      have : (v : ℝ) = n - a := by simp [n]
      rw [this]; push_cast; field_simp; ring
    rw [e, abs_neg]; exact hgood _

/-- Top-gap lemma: if `LRC (k-1)` holds and the largest speed `M` is at least `k` times
every other speed, then `S` has a lonely time. -/
private lemma top_gap (k : ℕ) (hk : 1 ≤ k) (hprev : LRC (k - 1)) (S : Finset ℕ)
    (hS : S.card = k) (hpos : ∀ v ∈ S, 0 < v) (M : ℕ) (hM : M ∈ S)
    (hgap : ∀ u ∈ S, u ≠ M → k * u ≤ M) :
    ∃ t : ℝ, ∀ v ∈ S, (1 : ℝ) / (k + 1 : ℝ) ≤ distToNearestInt (t * (v : ℝ)) := by
  have hcard : (S.erase M).card = k - 1 := by rw [Finset.card_erase_of_mem hM, hS]
  obtain ⟨t₀, ht₀⟩ := hprev (S.erase M) hcard
    (fun v hv => hpos v (Finset.mem_of_mem_erase hv))
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by rw [Nat.cast_sub hk]; ring
  rw [hcast] at ht₀
  set δ : ℝ := 1 / (k + 1 : ℝ)
  have hδ : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hpos M hM
  obtain ⟨x, hx, hxd⟩ := near δ (t₀ * M) hδ hδ2
  refine ⟨x / M, fun v hv => ?_⟩
  by_cases hvM : v = M
  · subst hvM; rwa [div_mul_cancel₀ _ hMpos.ne']
  have hv' : v ∈ S.erase M := Finset.mem_erase.2 ⟨hvM, hv⟩
  have h1 := ht₀ v hv'
  have hkv : (k : ℝ) * v ≤ M := by exact_mod_cast hgap v hv hvM
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hpos v hv
  -- the runner `v` moves by at most `δ / k`
  have hmove : |t₀ * v - x / M * v| ≤ δ / k := by
    have e : t₀ * v - x / M * v = -((x - t₀ * M) * v / M) := by field_simp; ring
    rw [e, abs_neg, abs_div, abs_mul, abs_of_pos hvpos, abs_of_pos hMpos,
      div_le_div_iff₀ hMpos (by linarith)]
    have := mul_le_mul hx hkv (by positivity) hδ.le
    nlinarith [abs_nonneg (x - t₀ * M)]
  have hl := dist_lip (x / M * v) (t₀ * v)
  rw [abs_sub_comm] at hl
  have e2 : (1 : ℝ) / k - δ / k = δ := by
    simp only [δ]; field_simp; ring
  linarith

private lemma lrc_zero : LRC 0 := by
  intro S hS _
  rw [Finset.card_eq_zero] at hS
  subst hS
  exact ⟨0, fun v hv => absurd hv (Finset.notMem_empty v)⟩

/-- Every case `1 ≤ k ≤ 6` follows from the previous one, the top-gap lemma, scaling by the
gcd, and the variation. -/
private lemma step (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (hprev : LRC (k - 1)) : LRC k := by
  intro S hS hpos
  have hne : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
  set M := S.max' hne
  have hM : M ∈ S := S.max'_mem hne
  by_cases hjump : ∀ u ∈ S, u ≠ M → k * u ≤ M
  · exact top_gap k hk1 hprev S hS hpos M hM hjump
  push Not at hjump
  obtain ⟨u, hu, huM, hMu⟩ := hjump
  have hk2 : 2 ≤ k := by
    have : 1 < S.card := Finset.one_lt_card.2 ⟨u, hu, M, hM, huM⟩
    omega
  have huleM : u ≤ M := S.le_max' u hu
  -- divide by the gcd
  set g := S.gcd id
  have hg0 : g ≠ 0 := by
    intro h0
    have := (Finset.gcd_eq_zero_iff.1 h0) M hM
    have := hpos M hM
    simp_all
  have hgpos : 0 < g := Nat.pos_of_ne_zero hg0
  have hdvd : ∀ v ∈ S, g ∣ v := fun v hv => Finset.gcd_dvd (f := id) hv
  set S₁ := S.image (· / g)
  have hinj : Set.InjOn (· / g) (S : Set ℕ) := by
    intro a ha b hb hab
    exact (Nat.div_left_inj (hdvd a ha) (hdvd b hb)).1 hab
  have hS₁ : S₁.card = k := by rw [Finset.card_image_of_injOn hinj, hS]
  have hpos₁ : ∀ v ∈ S₁, 0 < v := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact Nat.div_pos (Nat.le_of_dvd (hpos w hw) (hdvd w hw)) hgpos
  have hgcd₁ : S₁.gcd id = 1 := by
    rw [Finset.gcd_image]
    exact Finset.gcd_div_id_eq_one hM (hpos M hM).ne'
  have hgap₁ : ∃ a ∈ S₁, ∃ b ∈ S₁, a < b ∧ (∀ v ∈ S₁, v ≤ b) ∧ b < k * a := by
    obtain ⟨u', hu'⟩ := hdvd u hu
    obtain ⟨M', hM'⟩ := hdvd M hM
    have hu'e : u / g = u' := by rw [hu', Nat.mul_div_cancel_left _ hgpos]
    have hM'e : M / g = M' := by rw [hM', Nat.mul_div_cancel_left _ hgpos]
    refine ⟨u / g, Finset.mem_image_of_mem _ hu, M / g, Finset.mem_image_of_mem _ hM,
      ?_, ?_, ?_⟩
    · rw [hu'e, hM'e]
      have : u < M := lt_of_le_of_ne huleM huM
      rw [hu', hM'] at this
      exact Nat.lt_of_mul_lt_mul_left this
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
      exact Nat.div_le_div_right (S.le_max' w hw)
    · rw [hu'e, hM'e]
      rw [hu', hM'] at hMu
      have : g * M' < g * (k * u') := by
        calc g * M' < k * (g * u') := hMu
          _ = g * (k * u') := by ring
      exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ, ∀ v ∈ S₁,
      (1 : ℝ) / (k + 1 : ℝ) ≤ distToNearestInt (t₁ * (v : ℝ)) := by
    rcases (show k = 2 ∨ 3 ≤ k by omega) with h2 | h3
    · subst h2; exact wills S₁ hS₁ hpos₁ hgcd₁
    · exact LefebvreVariations.lonely_runner_small_coprime_no_top_gap k h3 hk6 S₁ hS₁ hpos₁ hgcd₁ hgap₁
  have hgr : (0 : ℝ) < g := by exact_mod_cast hgpos
  refine ⟨t₁ / g, fun v hv => ?_⟩
  have e : t₁ / g * (v : ℝ) = t₁ * ((v / g : ℕ) : ℝ) := by
    rw [Nat.cast_div (hdvd v hv) hgr.ne']; field_simp
  rw [e]
  exact ht₁ _ (Finset.mem_image_of_mem _ hv)

theorem solution : ∀ k : ℕ, k ≤ 6 → LRC k := by
  intro k hk
  induction k with
  | zero => exact lrc_zero
  | succ n ih => exact step (n + 1) (by omega) hk (by simpa using ih (by omega))
