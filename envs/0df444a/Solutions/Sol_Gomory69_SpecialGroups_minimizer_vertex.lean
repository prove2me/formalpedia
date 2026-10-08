-- Prove2me | solution 1 for Gomory69.SpecialGroups.minimizer_vertex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:40:29.781117+00:00
-- url     : https://prove2.me/submissions/c053d008-d44b-44a6-9818-69f87d501790

import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron



namespace Gomory69.SpecialGroups

section E7
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma e7_gs_add (a b : {g : G // g ≠ 0} → ℕ) : groupSum (a + b) = groupSum a + groupSum b := by
  unfold groupSum; simp [add_smul, Finset.sum_add_distrib]

lemma e7_gs_sub (a b : {g : G // g ≠ 0} → ℕ) (h : b ≤ a) :
    groupSum (a - b) + groupSum b = groupSum a := by
  rw [← e7_gs_add]; congr 1; exact tsub_add_cancel_of_le h

lemma e7_zsmul {p : ℕ} (hG : AllNonzeroOfOrder G p) (g : {g : G // g ≠ 0}) (n : ℤ) :
    n • (g : G) = 0 ↔ (p : ℤ) ∣ n := by
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hG g g.2]

lemma e7_dvd_small (p : ℕ) (hp : p = 2 ∨ p = 3) (a b : ℕ) (ha : a < p) (hb : b < p)
    (h : (p : ℤ) ∣ (a : ℤ) - b) : a = b := by
  rcases hp with rfl | rfl <;> omega

lemma e7_indep_coeff {p : ℕ} (hG : AllNonzeroOfOrder G p) (t : {g : G // g ≠ 0} → ℕ)
    (hI : IsIndependent (support t)) (c : {g : G // g ≠ 0} → ℤ)
    (hc : ∀ g, t g = 0 → c g = 0) (hsum : ∑ g, c g • (g : G) = 0) : ∀ g, (p : ℤ) ∣ c g := by
  classical
  let s : G → ℤ := fun g => if h : g ≠ 0 then c ⟨g, h⟩ else 0
  have hs : ∀ g : {g : G // g ≠ 0}, s g = c g := by intro g; simp [s, g.2]
  have h1 : ∑ g ∈ support t, s g • g = 0 := by
    unfold support
    rw [Finset.sum_map]
    simp only [Function.Embedding.subtype_apply, hs]
    refine Eq.trans ?_ hsum
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro g _ hg
    have : t g = 0 := by simpa using hg
    rw [hc g this]; simp
  intro g
  by_cases hg : t g = 0
  · rw [hc g hg]; exact dvd_zero _
  · have hm : (g : G) ∈ support t :=
      Finset.mem_map.2 ⟨g, by simpa [Nat.pos_iff_ne_zero] using hg, rfl⟩
    have := hI s h1 g hm
    rw [hs] at this
    exact (e7_zsmul hG g _).1 this

lemma e7_lt (p : ℕ) (hG : AllNonzeroOfOrder G p) (t : {g : G // g ≠ 0} → ℕ)
    (hirr : IsIrreducible t) (g : {g : G // g ≠ 0}) : t g < p := by
  by_contra hlt
  rw [not_lt] at hlt
  have hle : (Pi.single g p : {g : G // g ≠ 0} → ℕ) ≤ t := by
    intro h
    by_cases hh : h = g
    · subst hh; simpa using hlt
    · simp [Pi.single_apply, hh]
  have hgs : groupSum (Pi.single g p : {g : G // g ≠ 0} → ℕ) = 0 := by
    unfold groupSum
    rw [Finset.sum_eq_single g]
    · simp only [Pi.single_eq_same]
      have := (addOrderOf_dvd_iff_nsmul_eq_zero (x := (g : G)) (n := p)).1 (by rw [hG g g.2])
      exact this
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have h2 := e7_gs_sub t _ hle
  rw [hgs, add_zero] at h2
  have := hirr t (t - Pi.single g p) le_rfl tsub_le_self h2
  have h3 := congrFun this g
  simp at h3
  have hp0 : 0 < p := by rw [← hG g g.2]; exact addOrderOf_pos _
  omega


lemma e7_sum_cast (r s : {g : G // g ≠ 0} → ℕ) :
    ∑ g, ((r g : ℤ) - (s g : ℤ)) • (g : G) = (groupSum r : G) - groupSum s := by
  unfold groupSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  rw [sub_smul]; simp

lemma e7_irr_of_indep (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (t : {g : G // g ≠ 0} → ℕ) (hI : IsIndependent (support t)) (hlt : ∀ g, t g < p) :
    IsIrreducible t := by
  intro r s hr hs hrs
  funext g
  have h := e7_indep_coeff hG t hI (fun g => (r g : ℤ) - (s g : ℤ))
    (by intro g hg; have h1 : r g ≤ t g := hr g; have h2 : s g ≤ t g := hs g; omega)
    (by rw [e7_sum_cast, hrs, sub_self]) g
  exact e7_dvd_small p hp _ _ (lt_of_le_of_lt (hr g) (hlt g)) (lt_of_le_of_lt (hs g) (hlt g)) h

lemma e7_sol_support (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t)
    (hI : IsIndependent (support t))
    (u : {g : G // g ≠ 0} → ℕ) (hu : u ∈ solutionSet g₀) (hsupp : ∀ g, t g = 0 → u g = 0) :
    ∀ g, u g ≡ t g [MOD p] ∧ t g ≤ u g := by
  intro g
  have h := e7_indep_coeff hG t hI (fun g => (t g : ℤ) - (u g : ℤ))
    (by intro g hg; simp [hg, hsupp g hg])
    (by rw [e7_sum_cast, ht.1, hu.1, sub_self]) g
  have hm : u g ≡ t g [MOD p] := (Nat.modEq_iff_dvd).2 h
  refine ⟨hm, ?_⟩
  have := e7_lt p hG t hirr g
  have h2 : u g % p = t g := by rw [hm, Nat.mod_eq_of_lt this]
  calc t g = u g % p := h2.symm
    _ ≤ u g := Nat.mod_le _ _

lemma e7_indep_of_irr (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (t : {g : G // g ≠ 0} → ℕ) (hirr : IsIrreducible t) : IsIndependent (support t) := by
  classical
  intro s hs g hg
  have hp2 : 2 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hp0 : 0 < p := by omega
  have hp3 : ∀ x : G, p • x = 0 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have := (addOrderOf_dvd_iff_nsmul_eq_zero (x := x) (n := p)).1 (by rw [hG x hx])
      exact this
  let r : {g : G // g ≠ 0} → ℕ := fun g => if 0 < t g ∧ s g % p = 1 then 1 else 0
  let q : {g : G // g ≠ 0} → ℕ := fun g => if 0 < t g ∧ s g % p = 2 then 1 else 0
  have hpt : ∀ g : {g : G // g ≠ 0}, (if 0 < t g then s g • (g : G) else 0) =
      r g • (g : G) + 2 • (q g • (g : G)) := by
    intro g
    by_cases h0 : 0 < t g
    · have hv : s g % p < p := by
        have := Int.emod_lt_of_pos (s g) (show (0 : ℤ) < p by exact_mod_cast hp0); omega
      have hv0 : 0 ≤ s g % p := Int.emod_nonneg _ (by exact_mod_cast hp0.ne')
      have hdec : s g • (g : G) = (s g % p) • (g : G) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv (s g) p]
        rw [add_smul, mul_comm, mul_smul]
        have : (p : ℤ) • (g : G) = 0 := by
          rw [natCast_zsmul]; exact hp3 _
        rw [this]; simp
      rw [if_pos h0, hdec]
      have hcases : s g % p = 0 ∨ s g % p = 1 ∨ s g % p = 2 := by
        rcases hp with rfl | rfl <;> omega
      rcases hcases with h | h | h <;> simp [r, q, h, h0] <;> exact (by norm_cast : ((2:ℤ) • (g : G)) = (2:ℕ) • (g : G))
    · simp [r, q, h0]
  have hsum : groupSum r + 2 • groupSum q = 0 := by
    have h1 : ∑ g ∈ support t, s g • g = ∑ g, (if 0 < t g then s g • (g : G) else 0) := by
      unfold support
      rw [Finset.sum_map, Finset.sum_filter]
      rfl
    rw [h1] at hs
    simp only [hpt] at hs
    rw [Finset.sum_add_distrib, ← Finset.smul_sum] at hs
    exact hs
  have hrq : groupSum r = groupSum q := by
    rcases hp with rfl | rfl
    · have hq0 : q = 0 := by
        funext g; simp only [q, Pi.zero_apply]
        rw [if_neg]; have := Int.emod_lt_of_pos (s g) (show (0 : ℤ) < 2 by norm_num); omega
      have : groupSum q = 0 := by rw [hq0]; simp [groupSum]
      rw [this]
      rw [this] at hsum
      simpa using hsum
    · have h3 := hp3 (groupSum q)
      have : groupSum r = groupSum q + (-(3 • groupSum q)) := by
        have : groupSum r = - (2 • groupSum q) := eq_neg_of_add_eq_zero_left hsum
        rw [this]; simp [add_smul, three_nsmul] ; abel
      rw [this, h3]; simp
  have hrt : r ≤ t := by
    intro g; simp only [r]; split_ifs with h <;> omega
  have hqt : q ≤ t := by
    intro g; simp only [q]; split_ifs with h <;> omega
  have := hirr r q hrt hqt hrq.symm
  by_contra hne
  -- g ∈ support, s g • g ≠ 0
  have hg' : ∃ g' : {g : G // g ≠ 0}, (g' : G) = g ∧ 0 < t g' := by
    unfold support at hg
    rcases Finset.mem_map.1 hg with ⟨g', hg', rfl⟩
    exact ⟨g', rfl, by simpa using hg'⟩
  rcases hg' with ⟨g', rfl, hgt⟩
  apply hne
  rw [e7_zsmul hG g']
  have hv : s g' % p = 0 := by
    by_contra hv0
    have hc : s g' % p = 1 ∨ s g' % p = 2 := by
      have := Int.emod_lt_of_pos (s g') (show (0 : ℤ) < p by exact_mod_cast hp0)
      have := Int.emod_nonneg (s g') (show (p : ℤ) ≠ 0 by exact_mod_cast hp0.ne')
      rcases hp with rfl | rfl <;> omega
    have e := congrFun (this.symm) g'
    simp only [r, q] at e
    rcases hc with h | h <;> simp [h, hgt] at e
  exact Int.dvd_of_emod_eq_zero hv

lemma e7_wsum (w x y : {g : G // g ≠ 0} → ℝ) (a b : ℝ) :
    ∑ g, w g * (a * x g + b * y g) = a * ∑ g, w g * x g + b * ∑ g, w g * y g := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro g _; ring

lemma e7_minimizer (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t) :
    let π : {g : G // g ≠ 0} → ℕ := fun g => if t g = 0 then 1 else 0
    (∀ u ∈ solutionSet g₀, ∑ g, π g * t g ≤ ∑ g, π g * u g) ∧
    (∀ u ∈ solutionSet g₀, ∑ g, π g * u g = ∑ g, π g * t g → t ≤ u) ∧
    toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀) := by
  intro π
  have hI := e7_indep_of_irr p hp hG t hirr
  have hsos := e7_sol_support p hp hG g₀ t ht hirr hI
  have hπt : ∑ g, π g * t g = 0 :=
    Finset.sum_eq_zero (fun g _ => by simp only [π]; split_ifs with h <;> simp [h])
  have hz : ∀ u : {g : G // g ≠ 0} → ℕ, ∑ g, π g * u g = 0 → ∀ g, t g = 0 → u g = 0 := by
    intro u h0 g hg
    have := (Finset.sum_eq_zero_iff.1 h0) g (Finset.mem_univ g)
    simp [π, hg] at this; exact this
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro u _; rw [hπt]; exact Nat.zero_le _
  · intro u hu h0
    rw [hπt] at h0
    intro g; exact (hsos u hu (hz u h0) g).2
  · have hmem : toReal t ∈ masterPolyhedron g₀ := subset_convexHull ℝ _ ⟨t, ht, rfl⟩
    have key : ∀ x ∈ masterPolyhedron g₀, 0 ≤ ∑ g, (π g : ℝ) * x g ∧
        ∀ g, (t g : ℝ) ≤ p * ∑ g, (π g : ℝ) * x g + x g := by
      intro x hx
      have hconv : Convex ℝ {x : {g : G // g ≠ 0} → ℝ | 0 ≤ ∑ g, (π g : ℝ) * x g ∧
          ∀ g, (t g : ℝ) ≤ p * ∑ g, (π g : ℝ) * x g + x g} := by
        intro x hx y hy a b ha hb hab
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [e7_wsum]
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨hy1, hy2⟩ := hy
        refine ⟨by nlinarith [mul_nonneg ha hx1, mul_nonneg hb hy1], fun g => ?_⟩
        have e1 := mul_le_mul_of_nonneg_left (hx2 g) ha
        have e2 := mul_le_mul_of_nonneg_left (hy2 g) hb
        have : (t g : ℝ) = a * t g + b * t g := by rw [← add_mul, hab, one_mul]
        nlinarith
      have hsub : toReal '' solutionSet g₀ ⊆ {x : {g : G // g ≠ 0} → ℝ | 0 ≤ ∑ g, (π g : ℝ) * x g ∧
          ∀ g, (t g : ℝ) ≤ p * ∑ g, (π g : ℝ) * x g + x g} := by
        rintro _ ⟨u, hu, rfl⟩
        have hN : ∑ g, (π g : ℝ) * toReal u g = ((∑ g, π g * u g : ℕ) : ℝ) := by
          push_cast; rfl
        simp only [Set.mem_setOf_eq]
        rw [hN]
        refine ⟨Nat.cast_nonneg _, fun g => ?_⟩
        by_cases hN0 : ∑ g, π g * u g = 0
        · rw [hN0]
          have := (hsos u hu (hz u hN0) g).2
          simp only [toReal]
          have : (t g : ℝ) ≤ u g := by exact_mod_cast this
          simpa using this
        · have h1 : 1 ≤ ∑ g, π g * u g := Nat.one_le_iff_ne_zero.2 hN0
          have h2 : (1 : ℝ) ≤ ((∑ g, π g * u g : ℕ) : ℝ) := by exact_mod_cast h1
          have h3 : (t g : ℝ) < p := by exact_mod_cast e7_lt p hG t hirr g
          have h4 : (0 : ℝ) ≤ toReal u g := Nat.cast_nonneg _
          have h5 : (0 : ℝ) < p := by exact_mod_cast hp0
          nlinarith
      exact convexHull_min hsub hconv hx
    refine ⟨hmem, ?_⟩
    intro x1 hx1 x2 hx2 hseg
    obtain ⟨a, b, ha, hb, hab, hx⟩ := hseg
    have ht0 : ∑ g, (π g : ℝ) * toReal t g = 0 := by
      have : ∑ g, (π g : ℝ) * toReal t g = ((∑ g, π g * t g : ℕ) : ℝ) := by
        push_cast; rfl
      rw [this, hπt]; simp
    have hsum : a * ∑ g, (π g : ℝ) * x1 g + b * ∑ g, (π g : ℝ) * x2 g = 0 := by
      rw [← e7_wsum, ← ht0]
      apply Finset.sum_congr rfl; intro g _
      have := congrFun hx g
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
    obtain ⟨k1, k1'⟩ := key x1 hx1
    obtain ⟨k2, k2'⟩ := key x2 hx2
    have hA : ∑ g, (π g : ℝ) * x1 g = 0 := by nlinarith [mul_nonneg ha.le k1, mul_nonneg hb.le k2]
    have hB : ∑ g, (π g : ℝ) * x2 g = 0 := by nlinarith [mul_nonneg ha.le k1, mul_nonneg hb.le k2]
    have l1 : ∀ g, toReal t g ≤ x1 g := by
      intro g; have := k1' g; rw [hA] at this; simpa [toReal] using this
    have l2 : ∀ g, toReal t g ≤ x2 g := by
      intro g; have := k2' g; rw [hB] at this; simpa [toReal] using this
    funext g
    have := congrFun hx g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have e := this
    have e2 : (a + b) * toReal t g = toReal t g := by rw [hab, one_mul]
    apply le_antisymm
    · by_contra hlt
      rw [not_le] at hlt
      nlinarith [mul_pos ha (sub_pos.2 hlt), mul_le_mul_of_nonneg_left (l2 g) hb.le]
    · exact l1 g

lemma e7_extreme_irr (g₀ : G) (hg₀ : g₀ ≠ 0) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀)
    (h : toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) : IsIrreducible t := by
  intro r s hr hs hrs
  by_contra hne
  have hsol : ∀ u : {g : G // g ≠ 0} → ℕ, groupSum u = g₀ → u ∈ solutionSet g₀ :=
    fun u hu => ⟨hu, fun h => absurd h hg₀⟩
  have g1 := e7_gs_sub t s hs
  have g2 := e7_gs_sub t r hr
  have hu1 : groupSum (t - s + r) = g₀ := by
    rw [e7_gs_add, ← hrs, g1]; exact ht.1
  have hu2 : groupSum (t - r + s) = g₀ := by
    rw [e7_gs_add, hrs, g2]; exact ht.1
  have m1 : toReal (t - s + r) ∈ masterPolyhedron g₀ :=
    subset_convexHull ℝ _ ⟨_, hsol _ hu1, rfl⟩
  have m2 : toReal (t - r + s) ∈ masterPolyhedron g₀ :=
    subset_convexHull ℝ _ ⟨_, hsol _ hu2, rfl⟩
  have hseg : toReal t ∈ openSegment ℝ (toReal (t - s + r)) (toReal (t - r + s)) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toReal]
    have h1 : r g ≤ t g := hr g
    have h2 : s g ≤ t g := hs g
    have : (t g - s g + r g) + (t g - r g + s g) = 2 * t g := by omega
    have h3 : (((t g - s g + r g : ℕ) : ℝ)) + ((t g - r g + s g : ℕ) : ℝ) = 2 * (t g : ℝ) := by
      exact_mod_cast this
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith
  have := h.2 m1 m2 hseg
  apply hne
  funext g
  have h3 := congrFun this g
  simp only [toReal] at h3
  have h4 : t g - s g + r g = t g := by exact_mod_cast h3
  have h1 : r g ≤ t g := hr g
  have h2 : s g ≤ t g := hs g
  omega

lemma e7_theorem_23 (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (hg₀ : g₀ ≠ 0) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) :
    (IsIrreducible t ↔ toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) ∧
    (toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀) → IsIndependent (support t)) :=
  ⟨⟨fun hirr => (e7_minimizer p hp hG g₀ t ht hirr).2.2,
    fun h => e7_extreme_irr g₀ hg₀ t ht h⟩,
   fun h => e7_indep_of_irr p hp hG t (e7_extreme_irr g₀ hg₀ t ht h)⟩

lemma e7_vertex_char (s : ℕ) (hs : s = 2 ∨ s = 3) (hG : AllNonzeroOfOrder G s)
    (t : {g : G // g ≠ 0} → ℕ) (ht : t ≠ 0) :
    (∃ g₀ : G, g₀ ≠ 0 ∧ t ∈ solutionSet g₀ ∧ toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) ↔
      (IsIndependent (support t) ∧ ∀ g, t g < s) := by
  constructor
  · rintro ⟨g₀, hg0, hts, hext⟩
    have hirr := e7_extreme_irr g₀ hg0 t hts hext
    exact ⟨e7_indep_of_irr s hs hG t hirr, e7_lt s hG t hirr⟩
  · rintro ⟨hI, hlt⟩
    have hg0 : groupSum t ≠ 0 := by
      intro h0
      have hd := e7_indep_coeff hG t hI (fun g => (t g : ℤ)) (by intro g hg; simp [hg])
        (Eq.trans (by unfold groupSum; apply Finset.sum_congr rfl; intro g _; simp) h0)
      obtain ⟨g, hg⟩ := Function.ne_iff.1 ht
      have := e7_dvd_small s hs (t g) 0 (hlt g) (by rcases hs with rfl | rfl <;> norm_num)
        (by simpa using hd g)
      exact hg this
    have hts : t ∈ solutionSet (groupSum t) := ⟨rfl, fun h => absurd h hg0⟩
    have hirr := e7_irr_of_indep s hs hG t hI hlt
    exact ⟨groupSum t, hg0, hts, (e7_minimizer s hs hG _ t hts hirr).2.2⟩

end E7
end Gomory69.SpecialGroups

open Gomory69.SpecialGroups


theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t) :
    let π : {g : G // g ≠ 0} → ℕ := fun g => if t g = 0 then 1 else 0
    (∀ u ∈ solutionSet g₀, ∑ g, π g * t g ≤ ∑ g, π g * u g) ∧
    (∀ u ∈ solutionSet g₀, ∑ g, π g * u g = ∑ g, π g * t g → t ≤ u) ∧
    toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀) := by
  exact e7_minimizer p hp hG g₀ t ht hirr
