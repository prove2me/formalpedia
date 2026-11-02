-- Prove2me | solution 1 for IsodiamVar.Simplex.remark_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:42:32.766962+00:00
-- url     : https://prove2.me/submissions/92e9460e-0393-4c6e-bbab-0625fed581bb

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory

namespace IsodiamSolA
open IsodiamVar.Simplex

/-- Key finite identity: points on a sphere of radius `R` around `c` whose weighted mean is `c`. -/
lemma double_sum_eq {n : ℕ} {ι : Type*} [Fintype ι] (p : ι → E n) (w : ι → ℝ) (c : E n) (R : ℝ)
    (hw1 : ∑ i, w i = 1) (hc : ∑ i, w i • p i = c) (hR : ∀ i, ‖p i - c‖ = R) :
    ∑ i, ∑ j, w i * w j * ‖p i - p j‖ ^ 2 = 2 * R ^ 2 := by
  have h0 : ∑ j, w j • (p j - c) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, hc, ← Finset.sum_smul, hw1, one_smul, sub_self]
  have key : ∀ i j, ‖p i - p j‖ ^ 2 = R ^ 2 + R ^ 2 - 2 * inner ℝ (p i - c) (p j - c) := by
    intro i j
    have : p i - p j = (p i - c) - (p j - c) := by abel
    rw [this, norm_sub_sq_real, hR, hR]; ring
  have hinner : ∀ i, ∑ j, w j * inner ℝ (p i - c) (p j - c) = 0 := by
    intro i
    have : ∑ j, w j * inner ℝ (p i - c) (p j - c) = inner ℝ (p i - c) (∑ j, w j • (p j - c)) := by
      rw [inner_sum]; congr 1; ext j; rw [inner_smul_right]
    rw [this, h0, inner_zero_right]
  have hrow : ∀ i, ∑ j, w i * w j * ‖p i - p j‖ ^ 2 =
      w i * (2 * R ^ 2) * ∑ j, w j - 2 * w i * ∑ j, w j * inner ℝ (p i - c) (p j - c) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext j; rw [key]; ring
  simp only [hrow, hinner, hw1, mul_zero, sub_zero, mul_one]
  rw [← Finset.sum_mul, hw1, one_mul]

/-- The finite Jung-type bound with slack terms. -/
lemma finite_slack {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → E n) (w : ι → ℝ) (c : E n) (R d : ℝ)
    (hw1 : ∑ i, w i = 1) (hc : ∑ i, w i • p i = c) (hR : ∀ i, ‖p i - c‖ = R) :
    d ^ 2 * (1 - ∑ i, w i ^ 2) - 2 * R ^ 2 =
      ∑ i, ∑ j, w i * w j * (d ^ 2 - ‖p i - p j‖ ^ 2 - if i = j then d ^ 2 else 0) := by
  rw [← double_sum_eq p w c R hw1 hc hR]
  have e1 : ∑ i, ∑ j, w i * w j * d ^ 2 = d ^ 2 := by
    have : ∀ i, ∑ j, w i * w j * d ^ 2 = w i * d ^ 2 := by
      intro i; rw [← Finset.sum_mul, ← Finset.mul_sum, hw1, mul_one]
    simp only [this]; rw [← Finset.sum_mul, hw1, one_mul]
  have e2 : ∑ i, ∑ j, w i * w j * (if i = j then d ^ 2 else 0) = d ^ 2 * ∑ i, w i ^ 2 := by
    simp [Finset.mul_sum]; congr 1; ext i; ring
  have : ∀ i j, w i * w j * (d ^ 2 - ‖p i - p j‖ ^ 2 - if i = j then d ^ 2 else 0) =
      w i * w j * d ^ 2 - w i * w j * ‖p i - p j‖ ^ 2 - w i * w j * (if i = j then d ^ 2 else 0) := by
    intro i j; ring
  simp_rw [this, Finset.sum_sub_distrib, e1, e2]; ring

lemma sum_sq_ge {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw1 : ∑ i, w i = 1) :
    (∑ i, w i ^ 2) - 1 / (Fintype.card ι) = ∑ i, (w i - 1 / (Fintype.card ι)) ^ 2 := by
  have hne : (Fintype.card ι : ℝ) ≠ 0 := by
    intro h
    have : Fintype.card ι = 0 := by exact_mod_cast h
    rw [Fintype.card_eq_zero_iff] at this
    simp at hw1
  have : ∀ i, (w i - 1 / (Fintype.card ι)) ^ 2 =
      w i ^ 2 - 2 / (Fintype.card ι) * w i + 1 / (Fintype.card ι) ^ 2 := by intro i; ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp; ring

/-- Main finite lemma: bound and rigidity. -/
lemma finite_main {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → E n) (w : ι → ℝ) (c : E n) (R d : ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hc : ∑ i, w i • p i = c)
    (hR : ∀ i, ‖p i - c‖ = R) (hd : ∀ i j, dist (p i) (p j) ≤ d)
    (hcard : Fintype.card ι ≤ n + 1) :
    2 * R ^ 2 * (n + 1) ≤ d ^ 2 * n ∧
      (2 * R ^ 2 * (n + 1) = d ^ 2 * n → 0 < d →
        Fintype.card ι = n + 1 ∧ (∀ i, w i = 1 / (n + 1)) ∧ ∀ i j, i ≠ j → dist (p i) (p j) = d) := by
  have hslack := finite_slack p w c R d hw1 hc hR
  have hsq := sum_sq_ge w hw1
  have hne : 0 < Fintype.card ι := by
    rw [Fintype.card_pos_iff]
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  have hmle : (Fintype.card ι : ℝ) ≤ n + 1 := by exact_mod_cast hcard
  have hterm : ∀ i j, 0 ≤ w i * w j * (d ^ 2 - ‖p i - p j‖ ^ 2 - if i = j then d ^ 2 else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]
      apply mul_nonneg (mul_nonneg (hw i).le (hw j).le)
      have h1 := hd i j
      rw [dist_eq_norm] at h1
      have h2 : 0 ≤ ‖p i - p j‖ := norm_nonneg _
      nlinarith
  have hA : 0 ≤ ∑ i, ∑ j, w i * w j * (d ^ 2 - ‖p i - p j‖ ^ 2 - if i = j then d ^ 2 else 0) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j
  have hB : 0 ≤ ∑ i, (w i - 1 / (Fintype.card ι)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmn : 1 / (n + 1 : ℝ) ≤ 1 / (Fintype.card ι) := one_div_le_one_div_of_le hm hmle
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  -- 2R² ≤ d²(1 - Σw²) ≤ d²(1 - 1/m) ≤ d²(1 - 1/(n+1))
  have main : 2 * R ^ 2 ≤ d ^ 2 * (1 - 1 / (n + 1)) := by
    have : 2 * R ^ 2 ≤ d ^ 2 * (1 - ∑ i, w i ^ 2) := by linarith
    have : ∑ i, w i ^ 2 ≥ 1 / (Fintype.card ι) := by linarith
    nlinarith
  refine ⟨?_, ?_⟩
  · have : d ^ 2 * (1 - 1 / (n + 1)) * (n + 1) = d ^ 2 * n := by field_simp; ring
    nlinarith
  · intro heq hdpos
    have hd2p : 0 < d ^ 2 := by positivity
    have heq' : 2 * R ^ 2 = d ^ 2 * (1 - 1 / (n + 1)) := by
      field_simp; linarith
    -- all slack is zero
    have hA0 : ∑ i, ∑ j, w i * w j * (d ^ 2 - ‖p i - p j‖ ^ 2 - if i = j then d ^ 2 else 0) = 0 ∧
        d ^ 2 * (∑ i, (w i - 1 / (Fintype.card ι)) ^ 2) = 0 ∧
        d ^ 2 * (1 / (Fintype.card ι) - 1 / (n + 1)) = 0 := by
      have e : d ^ 2 * (1 - 1 / (n + 1)) - 2 * R ^ 2 =
          (∑ i, ∑ j, w i * w j * (d ^ 2 - ‖p i - p j‖ ^ 2 - if i = j then d ^ 2 else 0)) +
          d ^ 2 * (∑ i, (w i - 1 / (Fintype.card ι)) ^ 2) +
          d ^ 2 * (1 / (Fintype.card ι) - 1 / (n + 1)) := by
        rw [← hslack, ← hsq]; ring
      rw [heq', sub_self] at e
      have t1 := mul_nonneg hd2 hB
      have t2 : 0 ≤ d ^ 2 * (1 / (Fintype.card ι) - 1 / (n + 1)) :=
        mul_nonneg hd2 (by linarith)
      refine ⟨by linarith, by linarith, by linarith⟩
    obtain ⟨hA0, hB0, hC0⟩ := hA0
    have hcardeq : (Fintype.card ι : ℝ) = n + 1 := by
      have : 1 / (Fintype.card ι : ℝ) - 1 / (n + 1) = 0 := by
        rcases mul_eq_zero.mp hC0 with h | h
        · exact absurd h hd2p.ne'
        · exact h
      have : 1 / (Fintype.card ι : ℝ) = 1 / (n + 1) := by linarith
      field_simp at this
      linarith
    refine ⟨by exact_mod_cast hcardeq, ?_, ?_⟩
    · have hB0' : ∑ i, (w i - 1 / (Fintype.card ι)) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hB0 with h | h
        · exact absurd h hd2p.ne'
        · exact h
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hB0' i
        (Finset.mem_univ _)
      rw [hcardeq] at this
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    · intro i j hij
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => hterm i j)).mp hA0 i (Finset.mem_univ _)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)).mp h1 j
        (Finset.mem_univ _)
      rw [if_neg hij] at h2
      have hwij : 0 < w i * w j := mul_pos (hw i) (hw j)
      have h3 : d ^ 2 - ‖p i - p j‖ ^ 2 - 0 = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h hwij.ne'
        · exact h
      rw [dist_eq_norm]
      have h4 : ‖p i - p j‖ ^ 2 = d ^ 2 := by linarith
      exact (sq_eq_sq₀ (norm_nonneg _) hdpos.le).mp h4

end IsodiamSolA

namespace IsodiamSolB
open IsodiamVar.Simplex

lemma sum_extend_zero {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (e : ι ↪ κ) (g : ι → M) :
    ∑ k, Function.extend e g 0 k = ∑ i, g i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)), Finset.sum_map]
  · congr 1; ext i; exact e.injective.extend_apply g 0 i
  · intro k _ hk
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨i, rfl⟩; exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ i))

lemma card_le_of_affineIndependent {n : ℕ} {ι : Type*} [Fintype ι] {z : ι → E n}
    (hz : AffineIndependent ℝ z) : Fintype.card ι ≤ n + 1 := by
  have h1 := hz.card_le_finrank_succ
  have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ n := by
    have := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    simpa [finrank_euclideanSpace_fin] using this
  omega

lemma isCompact_convexHull {n : ℕ} {s : Set (E n)} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  set f : (Fin (n + 1) → ℝ) × (Fin (n + 1) → E n) → E n := fun q => ∑ i, q.1 i • q.2 i with hfdef
  have hf : Continuous f := by
    apply continuous_finsetSum; intro i _
    exact ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)
  have hK : IsCompact (stdSimplex ℝ (Fin (n + 1)) ×ˢ Set.univ.pi (fun _ : Fin (n + 1) => s)) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin (n + 1))) (isCompact_univ_pi fun _ => hs)
  suffices h : convexHull ℝ s = f '' (stdSimplex ℝ (Fin (n + 1)) ×ˢ
      Set.univ.pi (fun _ : Fin (n + 1) => s)) by
    rw [h]; exact hK.image hf
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ι, _, z, w, hzs, hai, hwpos, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard := card_le_of_affineIndependent hai
    obtain ⟨e⟩ : Nonempty (ι ↪ Fin (n + 1)) := Function.Embedding.nonempty_of_card_le (by simpa using hcard)
    have hne : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simp at hw1
    obtain ⟨i0⟩ := hne
    refine ⟨(Function.extend e w 0, Function.extend e z (fun _ => z i0)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro k
      show 0 ≤ Function.extend e w 0 k
      by_cases hk : ∃ i, e i = k
      · obtain ⟨i, rfl⟩ := hk; rw [e.injective.extend_apply]; exact (hwpos i).le
      · rw [Function.extend_apply' _ _ _ hk]; simp
    · show ∑ k, Function.extend e w 0 k = 1
      rw [sum_extend_zero e w, hw1]
    · intro k _
      show Function.extend e z (fun _ => z i0) k ∈ s
      by_cases hk : ∃ i, e i = k
      · obtain ⟨i, rfl⟩ := hk; rw [e.injective.extend_apply]; exact hzs ⟨i, rfl⟩
      · rw [Function.extend_apply' _ _ _ hk]; exact hzs ⟨i0, rfl⟩
    · simp only [hfdef]
      rw [← hx, ← sum_extend_zero e (fun i => w i • z i)]
      congr 1; ext k
      by_cases hk : ∃ i, e i = k
      · obtain ⟨i, rfl⟩ := hk
        simp only [e.injective.extend_apply]
      · simp only [Function.extend_apply' _ _ _ hk, Pi.zero_apply, zero_smul]
  · rintro x ⟨⟨w, p⟩, ⟨hw, hp⟩, rfl⟩
    simp only [hfdef]
    exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw.1 i) hw.2
      (fun i _ => subset_convexHull ℝ s (hp i (Set.mem_univ i)))

lemma exists_min_ball {n : ℕ} (K : Set (E n)) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ c : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall c R ∧
      ∀ z r, K ⊆ Metric.closedBall z r → R ≤ r := by
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨r0, hr0⟩ := hK.isBounded.subset_closedBall x0
  have hr0nn : 0 ≤ r0 := by
    have := hr0 hx0; rw [Metric.mem_closedBall, dist_self] at this; exact this
  set A : Set (E n × ℝ) := {q | q.2 ≤ r0 ∧ ∀ x ∈ K, dist x q.1 ≤ q.2} with hA
  have hAsub : A ⊆ Metric.closedBall x0 r0 ×ˢ Set.Icc 0 r0 := by
    rintro ⟨z, r⟩ ⟨h1, h2⟩
    have := h2 x0 hx0
    refine ⟨?_, ⟨le_trans dist_nonneg this, h1⟩⟩
    rw [Metric.mem_closedBall, dist_comm]; linarith
  have hAclosed : IsClosed A := by
    have : A = {q : E n × ℝ | q.2 ≤ r0} ∩ ⋂ x ∈ K, {q : E n × ℝ | dist x q.1 ≤ q.2} := by
      ext q; simp [hA]
    rw [this]
    apply IsClosed.inter (isClosed_le continuous_snd continuous_const)
    apply isClosed_biInter; intro x _
    exact isClosed_le (continuous_const.dist continuous_fst) continuous_snd
  have hAcpt : IsCompact A :=
    (IsCompact.prod (isCompact_closedBall x0 r0) isCompact_Icc).of_isClosed_subset hAclosed hAsub
  have hAne : A.Nonempty := ⟨(x0, r0), le_refl _, fun x hx => by
    have := hr0 hx; rwa [Metric.mem_closedBall] at this⟩
  obtain ⟨⟨c, R⟩, hcR, hmin⟩ := hAcpt.exists_isMinOn hAne continuous_snd.continuousOn
  refine ⟨c, R, le_trans dist_nonneg (hcR.2 x0 hx0), fun x hx => ?_, ?_⟩
  · rw [Metric.mem_closedBall]; exact hcR.2 x hx
  · intro z r hzr
    by_cases h : r0 ≤ r
    · exact le_trans hcR.1 h
    · have : (z, r) ∈ A := ⟨le_of_not_ge h, fun x hx => by
        have := hzr hx; rwa [Metric.mem_closedBall] at this⟩
      exact hmin this

lemma center_mem_far_hull {n : ℕ} (K : Set (E n)) (hK : IsCompact K) (hne : K.Nonempty)
    (c : E n) (R : ℝ) (hKc : K ⊆ Metric.closedBall c R)
    (hmin : ∀ z r, K ⊆ Metric.closedBall z r → R ≤ r) :
    c ∈ convexHull ℝ (K ∩ Metric.sphere c R) := by
  by_contra hc
  obtain ⟨x0, hx0⟩ := hne
  have hR0 : 0 ≤ R := le_trans dist_nonneg (Metric.mem_closedBall.mp (hKc hx0))
  rcases hR0.eq_or_lt with hR | hRpos
  · apply hc
    apply subset_convexHull
    have := hKc hx0
    rw [← hR, Metric.closedBall_zero, Set.mem_singleton_iff] at this
    subst this
    exact ⟨hx0, by rw [← hR]; simp⟩
  have hH : IsCompact (convexHull ℝ (K ∩ Metric.sphere c R)) :=
    isCompact_convexHull (hK.inter_right Metric.isClosed_sphere)
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ _) hH (convex_singleton c) isClosed_singleton
    (Set.disjoint_singleton_right.mpr hc)
  have hfc := hfv c rfl
  set δ := v - u with hδ
  have hδpos : 0 < δ := by linarith
  set g : E n := (InnerProductSpace.toDual ℝ (E n)).symm f with hg
  have hgf : ∀ x, inner ℝ g x = f x := fun x => InnerProductSpace.toDual_symm_apply
  -- far points
  have hfar : ∀ a ∈ K, dist a c = R → f c - f a > δ := by
    intro a ha hd
    have := hfu a (subset_convexHull ℝ _ ⟨ha, by rw [Metric.mem_sphere]; exact hd⟩)
    linarith
  -- near region
  set L : Set (E n) := K ∩ {a | f c - f a ≤ δ / 2} with hL
  have hLc : IsCompact L := hK.inter_right (isClosed_le (continuous_const.sub f.continuous)
    continuous_const)
  have hLlt : ∀ a ∈ L, dist a c < R := by
    intro a ⟨haK, ha⟩
    have h1 := Metric.mem_closedBall.mp (hKc haK)
    rcases h1.lt_or_eq with h | h
    · exact h
    · have := hfar a haK h; simp only [Set.mem_setOf_eq] at ha; linarith
  obtain ⟨R', hR'lt, hR'⟩ : ∃ R', R' < R ∧ ∀ a ∈ L, dist a c ≤ R' := by
    rcases L.eq_empty_or_nonempty with hLe | hLne
    · exact ⟨0, hRpos, by simp [hLe]⟩
    · obtain ⟨a, ha, hmax⟩ := hLc.exists_isMaxOn hLne (continuous_id.dist continuous_const).continuousOn
      exact ⟨dist a c, hLlt a ha, fun b hb => hmax hb⟩
  set G := ‖g‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  set t := min (δ / (2 * (G ^ 2 + 1))) ((R - R') / (2 * (G + 1))) with ht
  have ht1 : t ≤ δ / (2 * (G ^ 2 + 1)) := min_le_left _ _
  have ht2 : t ≤ (R - R') / (2 * (G + 1)) := min_le_right _ _
  have htpos : 0 < t := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have htG2 : t * G ^ 2 ≤ δ / 2 := by
    have : t * (G ^ 2 + 1) ≤ δ / 2 := by
      calc t * (G ^ 2 + 1) ≤ δ / (2 * (G ^ 2 + 1)) * (G ^ 2 + 1) :=
            mul_le_mul_of_nonneg_right ht1 (by positivity)
        _ = δ / 2 := by field_simp
    nlinarith
  have htG : t * G < R - R' := by
    have : t * (G + 1) ≤ (R - R') / 2 := by
      calc t * (G + 1) ≤ (R - R') / (2 * (G + 1)) * (G + 1) :=
            mul_le_mul_of_nonneg_right ht2 (by positivity)
        _ = (R - R') / 2 := by field_simp
    nlinarith
  set z := c - t • g with hz
  set r := max (Real.sqrt (R ^ 2 - t * δ / 2)) (R' + t * G) with hr
  have hrlt : r < R := by
    apply max_lt
    · rw [Real.sqrt_lt' hRpos]; nlinarith
    · linarith
  have hsub : K ⊆ Metric.closedBall z r := by
    intro a haK
    rw [Metric.mem_closedBall]
    by_cases haL : f c - f a ≤ δ / 2
    · have h1 : dist a c ≤ R' := hR' a ⟨haK, haL⟩
      have h2 : dist a z ≤ dist a c + dist c z := dist_triangle _ _ _
      have h3 : dist c z = t * G := by
        rw [hz, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_of_nonneg htpos.le]
      exact le_trans (by linarith) (le_max_right _ _)
    · push_neg at haL
      have h1 : ‖a - c‖ ≤ R := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp (hKc haK)
      have hexp : ‖a - z‖ ^ 2 = ‖a - c‖ ^ 2 + 2 * t * inner ℝ (a - c) g + t ^ 2 * G ^ 2 := by
        have : a - z = (a - c) + t • g := by rw [hz]; abel
        rw [this, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg htpos.le]
        ring
      have hin : inner ℝ (a - c) g = f a - f c := by
        rw [real_inner_comm, hgf, map_sub]
      have hsq : dist a z ^ 2 ≤ R ^ 2 - t * δ / 2 := by
        rw [dist_eq_norm, hexp, hin]
        have : ‖a - c‖ ^ 2 ≤ R ^ 2 := by
          have := norm_nonneg (a - c); nlinarith
        nlinarith
      have := Real.abs_le_sqrt hsq
      rw [abs_of_nonneg dist_nonneg] at this
      exact le_trans this (le_max_left _ _)
  have := hmin z r hsub
  linarith

end IsodiamSolB

namespace IsodiamSolC
open IsodiamVar.Simplex

lemma integral_sum_dirac {n : ℕ} {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) (p : ι → E n) (f : E n → G) :
    ∫ x, f x ∂(∑ i, c i • Measure.dirac (p i)) = ∑ i, (c i).toReal • f (p i) := by
  rw [integral_finsetSum_measure (fun i _ => (integrable_dirac enorm_lt_top).smul_measure (hc i))]
  simp [integral_smul_measure, integral_dirac]

lemma eq_sum_dirac {n : ℕ} {ι : Type*} [Fintype ι] (μ : Measure (E n)) (p : ι → E n)
    (hp : Function.Injective p) (h : μ (Set.range p)ᶜ = 0) :
    μ = ∑ i, μ {p i} • Measure.dirac (p i) := by
  classical
  ext s hs
  rw [← measure_inter_conull h]
  have hU : s ∩ Set.range p = ⋃ i ∈ Finset.univ.filter (fun i => p i ∈ s), {p i} := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_range, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨hx, i, rfl⟩; exact ⟨i, hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i, rfl⟩
  rw [hU, measure_biUnion_finset]
  · rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_filter]
    congr 1; ext i
    rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    by_cases hi : p i ∈ s
    · simp [hi]
    · simp [hi]
  · intro i _ j _ hij
    simp only [Function.onFun, Set.disjoint_singleton]
    exact fun h => hij (hp h)
  · intro i _; exact MeasurableSet.singleton _

/-- C5: a point on the circumsphere within distance `d` of all vertices of a regular simplex
spanning the space is a vertex. -/
lemma mem_range_of_close {n : ℕ} {ι : Type*} [Fintype ι] (p : ι → E n) (c : E n) (R d : ℝ)
    (hd : 0 < d) (hai : AffineIndependent ℝ p) (hcard : Fintype.card ι = n + 1)
    (hR : ∀ i, ‖p i - c‖ = R) (hdist : ∀ i j, i ≠ j → dist (p i) (p j) = d)
    (q : E n) (hq : ‖q - c‖ = R) (hqd : ∀ i, dist q (p i) ≤ d) :
    ∃ i, q = p i := by
  classical
  have htop : affineSpan ℝ (Set.range p) = ⊤ := by
    rw [hai.affineSpan_eq_top_iff_card_eq_finrank_add_one, finrank_euclideanSpace_fin, hcard]
  obtain ⟨β, hβ1, hqβ⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    (p1 := q) (p := p) (k := ℝ) (by rw [htop]; exact AffineSubspace.mem_top _ _ _)
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hβ1] at hqβ
  set e : ι → E n := fun i => p i - c with he
  set a : ℝ := d ^ 2 / 2 - R ^ 2 with ha
  have hgram : ∀ i j, inner ℝ (e i) (e j) = if i = j then R ^ 2 else -a := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, real_inner_self_eq_norm_sq, he]; simp only [hR]
    · rw [if_neg hij]
      have h1 := hdist i j hij
      rw [dist_eq_norm] at h1
      have : p i - p j = e i - e j := by simp [he]
      rw [this] at h1
      have h2 := norm_sub_sq_real (e i) (e j)
      rw [h1] at h2
      simp only [he, hR] at h2
      simp only [ha]; linarith
  have hy : q - c = ∑ i, β i • e i := by
    simp only [he, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hβ1, one_smul, hqβ]
  have hye : ∀ j, inner ℝ (q - c) (e j) = β j * (R ^ 2 + a) - a := by
    intro j
    rw [hy, sum_inner]
    simp only [inner_smul_left, hgram, RCLike.conj_to_real]
    have : ∀ i, β i * (if i = j then R ^ 2 else -a) =
        -a * β i + (if i = j then β i * (R ^ 2 + a) else 0) := by
      intro i; split_ifs <;> ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hβ1, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  have hRa : R ^ 2 + a = d ^ 2 / 2 := by simp only [ha]; ring
  have hRapos : 0 < R ^ 2 + a := by rw [hRa]; positivity
  have hβnn : ∀ j, 0 ≤ β j := by
    intro j
    have h1 := hqd j
    rw [dist_eq_norm] at h1
    have : q - p j = (q - c) - e j := by simp [he]
    rw [this] at h1
    have h2 := norm_sub_sq_real (q - c) (e j)
    have h3 : ‖e j‖ = R := hR j
    rw [hq, h3, hye j] at h2
    have h4 : ‖q - c - e j‖ ^ 2 ≤ d ^ 2 := by
      have := norm_nonneg (q - c - e j); nlinarith
    have : 0 ≤ β j * (R ^ 2 + a) := by nlinarith
    exact nonneg_of_mul_nonneg_left this hRapos
  have hsq : ∑ j, β j ^ 2 = 1 := by
    have h1 : ‖q - c‖ ^ 2 = ∑ j, β j * (β j * (R ^ 2 + a) - a) := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [hy]
      rw [inner_sum]
      congr 1; ext j; rw [inner_smul_right, ← hy, hye]
    rw [hq] at h1
    have h2 : ∑ j, β j * (β j * (R ^ 2 + a) - a) = (R ^ 2 + a) * ∑ j, β j ^ 2 - a := by
      have : ∀ j, β j * (β j * (R ^ 2 + a) - a) = (R ^ 2 + a) * β j ^ 2 - a * β j := by
        intro j; ring
      simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hβ1]; ring
    rw [h2] at h1
    have : (R ^ 2 + a) * (∑ j, β j ^ 2 - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hle1 : ∀ j, β j ≤ 1 := by
    intro j
    rw [← hβ1]
    exact Finset.single_le_sum (fun i _ => hβnn i) (Finset.mem_univ j)
  obtain ⟨j0, hj0⟩ : ∃ j, 0 < β j := by
    by_contra h
    push_neg at h
    have : ∑ i, β i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  have hprod : ∑ j, β j * (1 - β j) = 0 := by
    have : ∀ j, β j * (1 - β j) = β j - β j ^ 2 := by intro j; ring
    simp_rw [this, Finset.sum_sub_distrib, hβ1, hsq]; ring
  have hj01 : β j0 = 1 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (hβnn j) (by linarith [hle1 j]))).mp hprod j0 (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hother : ∀ k, k ≠ j0 → β k = 0 := by
    intro k hk
    have h1 : ∑ i, β i = β j0 + ∑ i ∈ Finset.univ.erase j0, β i := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    rw [hβ1, hj01] at h1
    have h2 : ∑ i ∈ Finset.univ.erase j0, β i = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hβnn i)).mp h2 k
      (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)
  refine ⟨j0, ?_⟩
  rw [hqβ, Finset.sum_eq_single j0]
  · rw [hj01, one_smul]
  · intro k _ hk; rw [hother k hk, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- C2: first-order condition. If `c` minimizes `z ↦ ∑ mᵢ v ‖pᵢ - z‖` and all `pᵢ` lie on the sphere
of radius `R > 0` around `c`, with `v` differentiable at `R`, then `c` is the barycenter. -/
lemma bary_eq {n : ℕ} {ι : Type*} [Fintype ι] (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hm1 : ∑ i, m i = 1) (p : ι → E n) (c : E n) (R : ℝ) (hRpos : 0 < R)
    (hR : ∀ i, ‖p i - c‖ = R) (v : ℝ → ℝ) (hvconv : ConvexOn ℝ (Set.Ici 0) v)
    (hvmono : StrictMonoOn v (Set.Ici 0)) (hdiff : DifferentiableAt ℝ v R)
    (hmin : ∀ z, v R ≤ ∑ i, m i * v ‖p i - z‖) :
    ∑ i, m i • p i = c := by
  by_contra hb
  set b := ∑ i, m i • p i with hbdef
  set u := b - c with hu
  set U := ‖u‖ with hU
  have hUpos : 0 < U := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  set v' := deriv v R with hv'
  have hder : HasDerivAt v v' R := hdiff.hasDerivAt
  have hv'pos : 0 < v' := by
    have h1 := hvconv.slope_le_of_hasDerivAt (x := 0) (y := R) (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hRpos.le) hRpos hder
    have h2 : v 0 < v R := hvmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hRpos.le) hRpos
    rw [slope_def_field] at h1
    have : 0 < (v R - v 0) / (R - 0) := div_pos (by linarith) (by linarith)
    linarith
  set ε := v' * U / (4 * R) with hε
  have hεpos : 0 < ε := by positivity
  have hlo := (hasDerivAt_iff_isLittleO.mp hder).def hεpos
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hlo
  set t := min (1 / 2) (δ / (2 * (U + 1))) with ht
  have htpos : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have ht2 : t ≤ δ / (2 * (U + 1)) := min_le_right _ _
  have htU : t * U < δ := by
    have : t * (U + 1) ≤ δ / 2 := by
      calc t * (U + 1) ≤ δ / (2 * (U + 1)) * (U + 1) := mul_le_mul_of_nonneg_right ht2 (by positivity)
        _ = δ / 2 := by field_simp
    nlinarith
  set z := c + t • u with hz
  have hcz : ‖c - z‖ = t * U := by
    rw [hz, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg htpos.le]
  have key : ∀ i, v ‖p i - z‖ ≤ v R + v' * (t ^ 2 * U ^ 2) / (2 * R) + ε * (t * U)
      - v' * t / R * inner ℝ (p i - c) u := by
    intro i
    set s := ‖p i - z‖ with hs
    have ha : |s - R| ≤ t * U := by
      rw [hs, ← hR i, ← hcz]
      have := abs_norm_sub_norm_le (p i - z) (p i - c)
      have e : p i - z - (p i - c) = c - z := by abel
      rwa [e] at this
    have hb' : dist s R < δ := by rw [Real.dist_eq]; linarith
    have he := hδ hb'
    simp only [smul_eq_mul, Real.norm_eq_abs] at he
    have hsq : s ^ 2 = R ^ 2 - 2 * t * inner ℝ (p i - c) u + t ^ 2 * U ^ 2 := by
      have e : p i - z = (p i - c) - t • u := by rw [hz]; abel
      rw [hs, e, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg htpos.le, hR]
      ring
    have hd : s - R ≤ (s ^ 2 - R ^ 2) / (2 * R) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (s - R)]
    have h1 : v s ≤ v R + (s - R) * v' + ε * |s - R| := by
      have := le_abs_self (v s - v R - (s - R) * v'); linarith
    have h2 : (s - R) * v' ≤ (s ^ 2 - R ^ 2) / (2 * R) * v' :=
      mul_le_mul_of_nonneg_right hd hv'pos.le
    have h3 : ε * |s - R| ≤ ε * (t * U) := mul_le_mul_of_nonneg_left ha hεpos.le
    rw [hsq] at h2
    have h4 : (R ^ 2 - 2 * t * inner ℝ (p i - c) u + t ^ 2 * U ^ 2 - R ^ 2) / (2 * R) * v' =
        v' * (t ^ 2 * U ^ 2) / (2 * R) - v' * t / R * inner ℝ (p i - c) u := by
      field_simp; ring
    linarith
  have hsum : ∑ i, m i * inner ℝ (p i - c) u = U ^ 2 := by
    have : ∑ i, m i * inner ℝ (p i - c) u = inner ℝ (∑ i, m i • (p i - c)) u := by
      rw [sum_inner]; congr 1; ext i; rw [inner_smul_left]; simp
    rw [this]
    have e : ∑ i, m i • (p i - c) = u := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hm1, one_smul, hu, hbdef]
    rw [e, real_inner_self_eq_norm_sq]
  have hz' := hmin z
  have hle : ∑ i, m i * v ‖p i - z‖ ≤ ∑ i, m i * (v R + v' * (t ^ 2 * U ^ 2) / (2 * R) +
      ε * (t * U) - v' * t / R * inner ℝ (p i - c) u) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (key i) (hm i)
  have hcalc : ∑ i, m i * (v R + v' * (t ^ 2 * U ^ 2) / (2 * R) +
      ε * (t * U) - v' * t / R * inner ℝ (p i - c) u) =
      (v R + v' * (t ^ 2 * U ^ 2) / (2 * R) + ε * (t * U)) - v' * t / R * U ^ 2 := by
    have : ∀ i, m i * (v R + v' * (t ^ 2 * U ^ 2) / (2 * R) +
      ε * (t * U) - v' * t / R * inner ℝ (p i - c) u) =
        (v R + v' * (t ^ 2 * U ^ 2) / (2 * R) + ε * (t * U)) * m i -
          v' * t / R * (m i * inner ℝ (p i - c) u) := by intro i; ring
    simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hm1, hsum, mul_one]
  rw [hcalc] at hle
  -- the bracket is negative
  have hneg : v' * (t ^ 2 * U ^ 2) / (2 * R) + ε * (t * U) - v' * t / R * U ^ 2 < 0 := by
    have e : v' * (t ^ 2 * U ^ 2) / (2 * R) + ε * (t * U) - v' * t / R * U ^ 2 =
        v' * t * U ^ 2 / R * (t / 2 + 1 / 4 - 1) := by
      rw [hε]; field_simp
    rw [e]
    apply mul_neg_of_pos_of_neg (by positivity)
    linarith
  linarith

/-- Circumradius of a regular simplex given by its vertex family. -/
lemma simplex_circum {n : ℕ} (x : Fin (n + 1) → E n) (d : ℝ)
    (hx : ∀ i j, i ≠ j → dist (x i) (x j) = d) (i : Fin (n + 1)) :
    ‖x i - ((n : ℝ) + 1)⁻¹ • ∑ j, x j‖ ^ 2 = n * d ^ 2 / (2 * (n + 1)) := by
  classical
  set g := ((n : ℝ) + 1)⁻¹ • ∑ j, x j with hg
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hsum0 : ∑ j, (x j - g) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hg,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [show ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + 1)⁻¹ = 1 by push_cast; field_simp]
    simp
  set S := ∑ j, ‖x j - g‖ ^ 2 with hS
  have hrow : ∀ k, ∑ j, ‖x k - x j‖ ^ 2 = (n + 1) * ‖x k - g‖ ^ 2 + S := by
    intro k
    have : ∀ j, ‖x k - x j‖ ^ 2 = ‖x k - g‖ ^ 2 + ‖x j - g‖ ^ 2 - 2 * inner ℝ (x k - g) (x j - g) := by
      intro j
      have e : x k - x j = (x k - g) - (x j - g) := by abel
      rw [e, norm_sub_sq_real]; ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← inner_sum,
      hsum0, inner_zero_right]
    simp [Finset.card_univ]; ring
  have hrowd : ∀ k, ∑ j, ‖x k - x j‖ ^ 2 = n * d ^ 2 := by
    intro k
    have : ∀ j, ‖x k - x j‖ ^ 2 = if j = k then 0 else d ^ 2 := by
      intro j
      split_ifs with h
      · subst h; simp
      · rw [← dist_eq_norm, hx k j (Ne.symm h)]
    simp_rw [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.univ.filter (fun j : Fin (n + 1) => ¬ j = k)).card = n := by
      rw [Finset.filter_ne' Finset.univ k, Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    rw [this]
  have hS' : (n + 1) * S + (n + 1) * S = (n + 1) * (n * d ^ 2) := by
    have h1 : ∑ k, ((n + 1) * ‖x k - g‖ ^ 2 + S) = ∑ k : Fin (n + 1), (n * d ^ 2) := by
      congr 1; ext k; rw [← hrow, hrowd]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hS, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul] at h1
    push_cast at h1; linarith
  have hSv : S = n * d ^ 2 / 2 := by
    have : (n + 1) * (2 * S - n * d ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have := hrow i
  rw [hrowd, hSv] at this
  field_simp
  linarith

/-- The sum of distances to the vertices is minimized at the circumcenter. -/
lemma sum_dist_ge {n : ℕ} {ι : Type*} [Fintype ι] (x : ι → E n) (g : E n) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ i, ‖x i - g‖ = ρ) (hg : ∑ i, (x i - g) = 0) (z : E n) :
    (Fintype.card ι) * ρ ≤ ∑ i, ‖x i - z‖ := by
  rcases hρ0.eq_or_lt with h | hpos
  · rw [← h, mul_zero]; exact Finset.sum_nonneg fun i _ => norm_nonneg _
  have h1 : ∀ i, inner ℝ (x i - z) (x i - g) ≤ ‖x i - z‖ * ρ := by
    intro i; rw [← hρ i]; exact real_inner_le_norm _ _
  have h2 : ∑ i, inner ℝ (x i - z) (x i - g) = (Fintype.card ι) * ρ ^ 2 := by
    have : ∀ i, inner ℝ (x i - z) (x i - g) = ρ ^ 2 + inner ℝ (g - z) (x i - g) := by
      intro i
      have e : x i - z = (x i - g) + (g - z) := by abel
      rw [e, inner_add_left, real_inner_self_eq_norm_sq, hρ]
    simp_rw [this, Finset.sum_add_distrib, ← inner_sum, hg, inner_zero_right]
    simp
  have h3 : (Fintype.card ι) * ρ ^ 2 ≤ (∑ i, ‖x i - z‖) * ρ := by
    rw [← h2, Finset.sum_mul]; exact Finset.sum_le_sum fun i _ => h1 i
  have : (Fintype.card ι) * ρ * ρ ≤ (∑ i, ‖x i - z‖) * ρ := by nlinarith
  exact le_of_mul_le_mul_right this hpos

lemma centroid_sum_zero {n : ℕ} (x : Fin (n + 1) → E n) :
    ∑ j, (x j - ((n : ℝ) + 1)⁻¹ • ∑ j, x j) = 0 := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [show ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + 1)⁻¹ = 1 by push_cast; field_simp]
  simp

end IsodiamSolC

namespace IsodiamSolD
open IsodiamVar.Simplex IsodiamSolA IsodiamSolB IsodiamSolC

lemma jung_struct {n : ℕ} (K : Set (E n)) (hK : IsCompact K) (hne : K.Nonempty) (d : ℝ)
    (hd : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ d) :
    ∃ c : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall c R ∧ 2 * R ^ 2 * (n + 1) ≤ d ^ 2 * n ∧
      ∃ (ι : Type) (_ : Fintype ι) (p : ι → E n) (w : ι → ℝ), (∀ i, p i ∈ K ∧ ‖p i - c‖ = R) ∧
        AffineIndependent ℝ p ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • p i = c := by
  classical
  obtain ⟨c, R, hR0, hKc, hmin⟩ := exists_min_ball K hK hne
  have hc := center_mem_far_hull K hK hne c R hKc hmin
  obtain ⟨ι, hι, z, w, hzs, hai, hwpos, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hc
  have hzK : ∀ i, z i ∈ K ∧ ‖z i - c‖ = R := by
    intro i
    have := hzs ⟨i, rfl⟩
    exact ⟨this.1, by rw [← dist_eq_norm]; exact Metric.mem_sphere.mp this.2⟩
  have hfin := (finite_main z w c R d hwpos hw1 hx (fun i => (hzK i).2)
    (fun i j => hd _ (hzK i).1 _ (hzK j).1) (card_le_of_affineIndependent hai)).1
  exact ⟨c, R, hR0, hKc, hfin, ι, hι, z, w, hzK, hai, hwpos, hw1, hx⟩

lemma rn_nonneg (n : ℕ) : 0 ≤ rn n := Real.sqrt_nonneg _

lemma rn_sq (n : ℕ) : rn n ^ 2 = n / (2 * n + 2) :=
  Real.sq_sqrt (div_nonneg (Nat.cast_nonneg n) (by positivity))

lemma le_rn_mul {n : ℕ} {R d : ℝ} (hR : 0 ≤ R) (hd : 0 ≤ d) (h : 2 * R ^ 2 * (n + 1) ≤ d ^ 2 * n) :
    R ≤ rn n * d := by
  have h1 : R ^ 2 ≤ (rn n * d) ^ 2 := by
    rw [mul_pow, rn_sq]
    have hn : (0 : ℝ) < 2 * n + 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hn]; nlinarith
  exact (pow_le_pow_iff_left₀ hR (mul_nonneg (rn_nonneg n) hd) (by norm_num)).mp h1

end IsodiamSolD

namespace IsodiamSolM
open IsodiamVar.Simplex IsodiamSolA IsodiamSolB IsodiamSolC IsodiamSolD

/-- Reduction from the closed convex hull of a spherical set to a finite configuration. -/
lemma hull_reduce {n : ℕ} (r : ℝ) (K : Set (E n)) (hKs : K ⊆ Metric.sphere (0 : E n) r)
    (hKh : (0 : E n) ∈ closedConvexHull ℝ K) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → E n) (w : ι → ℝ), (∀ i, p i ∈ closure K) ∧
      AffineIndependent ℝ p ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • p i = 0 := by
  have hb : Bornology.IsBounded K := Metric.isBounded_sphere.subset hKs
  have hcK : IsCompact (closure K) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have h1 : closedConvexHull ℝ K ⊆ convexHull ℝ (closure K) := by
    rw [closedConvexHull_eq_closure_convexHull]
    exact closure_minimal (convexHull_mono subset_closure) (isCompact_convexHull hcK).isClosed
  obtain ⟨ι, hι, z, w, hzs, hai, hwpos, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull (h1 hKh)
  exact ⟨ι, hι, z, w, fun i => hzs ⟨i, rfl⟩, hai, hwpos, hw1, hx⟩

lemma closure_facts {n : ℕ} (r : ℝ) (K : Set (E n)) (hKs : K ⊆ Metric.sphere (0 : E n) r)
    (hKd : Metric.diam K ≤ 1) :
    (∀ x ∈ closure K, ‖x‖ = r) ∧ ∀ x ∈ closure K, ∀ y ∈ closure K, dist x y ≤ 1 := by
  have hb : Bornology.IsBounded K := Metric.isBounded_sphere.subset hKs
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have := closure_minimal hKs Metric.isClosed_sphere hx
    simpa using this
  · calc dist x y ≤ Metric.diam (closure K) := Metric.dist_le_diam_of_mem hb.closure hx hy
      _ = Metric.diam K := Metric.diam_closure K
      _ ≤ 1 := hKd

end IsodiamSolM

open IsodiamVar.Simplex IsodiamSolA IsodiamSolB IsodiamSolC IsodiamSolD IsodiamSolM in
theorem solution {n : ℕ} (x : Fin (n + 1) → E n)
    (hx : AffineIndependent ℝ x) (μ : Measure (E n))
    (hμ : InP (Set.range x) μ)
    (hb : (∫ y, y ∂μ) = ((n : ℝ) + 1)⁻¹ • ∑ i, x i) :
    μ = uniformVertexMeasure x := by
  classical
  haveI := hμ.1
  have hμeq := eq_sum_dirac μ x hx.injective hμ.2
  set m : Fin (n + 1) → ℝ := fun i => (μ {x i}).toReal with hm
  have hint_sum : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (f : E n → G), ∫ y, f y ∂μ = ∑ i, m i • f (x i) := by
    intro G _ _ _ f
    have h := integral_sum_dirac (fun i => μ {x i}) (fun i => measure_ne_top μ _) x f
    rw [← hμeq] at h
    rw [h]
  have hm1 : ∑ i, m i = 1 := by
    have := hint_sum (fun _ => (1 : ℝ))
    simp only [integral_const, smul_eq_mul, mul_one] at this
    rw [← this]; simp
  have hbar : ∑ i, m i • x i = ((n : ℝ) + 1)⁻¹ • ∑ i, x i := by
    rw [← hb, hint_sum (fun y => y)]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hw1 : ∑ _i : Fin (n + 1), ((n : ℝ) + 1)⁻¹ = 1 := by
    simp [Finset.card_univ]; field_simp
  have hmw : m = fun _ => ((n : ℝ) + 1)⁻¹ := by
    apply (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ x).mp hx m _ hm1 hw1
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hm1,
      Finset.affineCombination_eq_linear_combination _ _ _ hw1, hbar, Finset.smul_sum]
  have hmass : ∀ i, μ {x i} = ((n : ENNReal) + 1)⁻¹ := by
    intro i
    have h1 : m i = ((n : ℝ) + 1)⁻¹ := by rw [hmw]
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x i})]
    change ENNReal.ofReal (m i) = _
    rw [h1, ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [hμeq]
  unfold uniformVertexMeasure
  congr 1; ext1 i
  rw [hmass]
