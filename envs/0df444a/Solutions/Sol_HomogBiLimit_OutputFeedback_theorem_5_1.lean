-- Prove2me | solution 1 for HomogBiLimit.OutputFeedback.theorem_5_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:26:45.170584+00:00
-- url     : https://prove2.me/submissions/e8ac612c-d579-4d23-af9a-ff33b09507ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems
import Theorems.Thm_HomogBiLimit_OutputFeedback_theorem_2_20
import Theorems.Thm_HomogBiLimit_OutputFeedback_lemma_2_13
import Theorems.Thm_HomogBiLimit_OutputFeedback_display_3_12
import Theorems.Thm_HomogBiLimit_OutputFeedback_display_4_9
import Theorems.Thm_HomogBiLimit_OutputFeedback_lyapunov_sufficient_gas

open HomogBiLimit.OutputFeedback

namespace HBLRed

/-- strong 0-limit convergence: uniform on every compact set (possibly containing 0). -/
def SZ {m : ℕ} (φ : (Fin m → ℝ) → ℝ) (r : Fin m → ℝ) (d : ℝ) (φ₀ : (Fin m → ℝ) → ℝ) : Prop :=
  ∀ C : Set (Fin m → ℝ), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ l₀ : ℝ, 0 < l₀ ∧
    ∀ l : ℝ, 0 < l → l ≤ l₀ → ∀ x ∈ C, |φ (dil r l x) / l ^ d - φ₀ x| ≤ ε

/-- strong ∞-limit convergence. -/
def SI {m : ℕ} (φ : (Fin m → ℝ) → ℝ) (r : Fin m → ℝ) (d : ℝ) (φ₀ : (Fin m → ℝ) → ℝ) : Prop :=
  ∀ C : Set (Fin m → ℝ), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ l₀ : ℝ, 0 < l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ x ∈ C, |φ (dil r l x) / l ^ d - φ₀ x| ≤ ε

lemma dil_dil {m : ℕ} (r : Fin m → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : Fin m → ℝ) :
    dil r a (dil r b x) = dil r (a * b) x := by
  funext i; simp only [dil]; rw [Real.mul_rpow ha hb]; ring

lemma dil_zero {m : ℕ} (r : Fin m → ℝ) (l : ℝ) : dil r l 0 = 0 := by
  funext i; simp [dil]

lemma dil_one {m : ℕ} (r : Fin m → ℝ) (x : Fin m → ℝ) : dil r 1 x = x := by
  funext i; simp [dil]

/-- homogeneous norm -/
noncomputable def hn {m : ℕ} (r : Fin m → ℝ) (x : Fin m → ℝ) : ℝ := ∑ i, |x i| ^ (1 / r i)

lemma hn_nonneg {m : ℕ} (r : Fin m → ℝ) (x : Fin m → ℝ) : 0 ≤ hn r x :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)

lemma hn_continuous {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) : Continuous (hn r) := by
  unfold hn
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact (Real.continuous_rpow_const (le_of_lt (one_div_pos.2 (hr i)))).comp
    ((continuous_apply i).abs)

lemma hn_dil {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) {μ : ℝ} (hμ : 0 ≤ μ)
    (x : Fin m → ℝ) : hn r (dil r μ x) = μ * hn r x := by
  unfold hn dil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hμ _), Real.mul_rpow (Real.rpow_nonneg hμ _)
    (abs_nonneg _), ← Real.rpow_mul hμ, mul_one_div_cancel (ne_of_gt (hr i)), Real.rpow_one]

lemma hn_eq_zero {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (x : Fin m → ℝ)
    (h : hn r x = 0) : x = 0 := by
  unfold hn at h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)] at h
  funext i
  have := h i (Finset.mem_univ _)
  rw [Real.rpow_eq_zero (abs_nonneg _) (ne_of_gt (one_div_pos.2 (hr i)))] at this
  simpa using this

lemma hn_sphere_compact {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) :
    IsCompact {x : Fin m → ℝ | hn r x = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (hn_continuous r hr) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := 1)).subset ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    by_contra hlt
    push Not at hlt
    have h1 : 1 < |x i| ^ (1 / r i) := Real.one_lt_rpow hlt (one_div_pos.2 (hr i))
    have h2 : |x i| ^ (1 / r i) ≤ hn r x :=
      Finset.single_le_sum (f := fun i => |x i| ^ (1 / r i))
        (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
    linarith

lemma decomp {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (x : Fin m → ℝ) (hx : x ≠ 0) :
    0 < hn r x ∧ hn r (dil r (hn r x)⁻¹ x) = 1 ∧ dil r (hn r x) (dil r (hn r x)⁻¹ x) = x := by
  have hpos : 0 < hn r x :=
    lt_of_le_of_ne (hn_nonneg r x) (fun h => hx (hn_eq_zero r hr x h.symm))
  refine ⟨hpos, ?_, ?_⟩
  · rw [hn_dil r hr (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne']
  · rw [dil_dil r hpos.le (inv_nonneg.2 hpos.le), mul_inv_cancel₀ hpos.ne', dil_one]


/-- exact homogeneity of the 0-limit approximation at nonzero points -/
lemma exact_zero_ne {m : ℕ} {φ φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ}
    (h : IsHomogZero φ r d φ₀) {μ : ℝ} (hμ : 0 < μ) (x : Fin m → ℝ) (hx : x ≠ 0) :
    φ₀ (dil r μ x) = μ ^ d * φ₀ x := by
  obtain ⟨hr, hd, -, -, -, hconv⟩ := h
  have hy : dil r μ x ≠ 0 := by
    intro h0
    apply hx
    have := congrArg (dil r μ⁻¹) h0
    rwa [dil_dil r (inv_nonneg.2 hμ.le) hμ.le, inv_mul_cancel₀ hμ.ne', dil_one, dil_zero] at this
  have hC : IsCompact ({x, dil r μ x} : Set (Fin m → ℝ)) := (Set.toFinite _).isCompact
  have h0C : (0 : Fin m → ℝ) ∉ ({x, dil r μ x} : Set (Fin m → ℝ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hx, Ne.symm hy⟩
  have hμd : 0 < μ ^ d := Real.rpow_pos_of_pos hμ d
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  obtain ⟨l₀, hl₀, hl⟩ := hconv _ hC h0C (ε / (μ ^ d + 1)) (by positivity)
  set l := min l₀ (l₀ / μ) with hldef
  have hlpos : 0 < l := lt_min hl₀ (div_pos hl₀ hμ)
  have hl1 : l ≤ l₀ := min_le_left _ _
  have hl2 : l * μ ≤ l₀ := by
    have := min_le_right l₀ (l₀ / μ)
    rw [← hldef] at this
    calc l * μ ≤ (l₀ / μ) * μ := mul_le_mul_of_nonneg_right this hμ.le
      _ = l₀ := div_mul_cancel₀ _ hμ.ne'
  have e1 := hl l hlpos hl1 (dil r μ x) (by simp)
  have e2 := hl (l * μ) (mul_pos hlpos hμ) hl2 x (by simp)
  rw [dil_dil r hlpos.le hμ.le] at e1
  have key : φ (dil r (l * μ) x) / l ^ d = μ ^ d * (φ (dil r (l * μ) x) / (l * μ) ^ d) := by
    rw [Real.mul_rpow hlpos.le hμ.le]
    field_simp
  rw [key] at e1
  rw [Real.dist_eq]
  have e3 : |μ ^ d * (φ (dil r (l * μ) x) / (l * μ) ^ d) - μ ^ d * φ₀ x| ≤ μ ^ d * (ε / (μ ^ d + 1)) := by
    rw [← mul_sub, abs_mul, abs_of_pos hμd]
    exact mul_le_mul_of_nonneg_left e2 hμd.le
  have e4 : μ ^ d * (ε / (μ ^ d + 1)) + ε / (μ ^ d + 1) = ε := by
    field_simp
  calc |φ₀ (dil r μ x) - μ ^ d * φ₀ x|
      ≤ |φ₀ (dil r μ x) - μ ^ d * (φ (dil r (l * μ) x) / (l * μ) ^ d)| +
        |μ ^ d * (φ (dil r (l * μ) x) / (l * μ) ^ d) - μ ^ d * φ₀ x| := abs_sub_le _ _ _
    _ ≤ ε / (μ ^ d + 1) + μ ^ d * (ε / (μ ^ d + 1)) := by
        gcongr
        rw [abs_sub_comm]; exact e1
    _ = ε := by linarith


lemma exact_infty_ne {m : ℕ} {φ φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ}
    (h : IsHomogInfty φ r d φ₀) {μ : ℝ} (hμ : 0 < μ) (x : Fin m → ℝ) (hx : x ≠ 0) :
    φ₀ (dil r μ x) = μ ^ d * φ₀ x := by
  obtain ⟨hr, hd, -, -, -, hconv⟩ := h
  have hy : dil r μ x ≠ 0 := by
    intro h0
    apply hx
    have := congrArg (dil r μ⁻¹) h0
    rwa [dil_dil r (inv_nonneg.2 hμ.le) hμ.le, inv_mul_cancel₀ hμ.ne', dil_one, dil_zero] at this
  have hC : IsCompact ({x, dil r μ x} : Set (Fin m → ℝ)) := (Set.toFinite _).isCompact
  have h0C : (0 : Fin m → ℝ) ∉ ({x, dil r μ x} : Set (Fin m → ℝ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hx, Ne.symm hy⟩
  have hμd : 0 < μ ^ d := Real.rpow_pos_of_pos hμ d
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  obtain ⟨l₀, hl₀, hl⟩ := hconv _ hC h0C (ε / (μ ^ d + 1)) (by positivity)
  set l := max l₀ (l₀ / μ) with hldef
  have hlpos : 0 < l := lt_max_of_lt_left hl₀
  have hl1 : l₀ ≤ l := le_max_left _ _
  have hl2 : l₀ ≤ l * μ := by
    have := le_max_right l₀ (l₀ / μ)
    rw [← hldef] at this
    calc l₀ = (l₀ / μ) * μ := (div_mul_cancel₀ _ hμ.ne').symm
      _ ≤ l * μ := mul_le_mul_of_nonneg_right this hμ.le
  have e1 := hl l hl1 (dil r μ x) (by simp)
  have e2 := hl (l * μ) hl2 x (by simp)
  rw [dil_dil r hlpos.le hμ.le] at e1
  have key : φ (dil r (l * μ) x) / l ^ d = μ ^ d * (φ (dil r (l * μ) x) / (l * μ) ^ d) := by
    rw [Real.mul_rpow hlpos.le hμ.le]
    field_simp
  rw [key] at e1
  rw [Real.dist_eq]
  have e3 : |μ ^ d * (φ (dil r (l * μ) x) / (l * μ) ^ d) - μ ^ d * φ₀ x| ≤ μ ^ d * (ε / (μ ^ d + 1)) := by
    rw [← mul_sub, abs_mul, abs_of_pos hμd]
    exact mul_le_mul_of_nonneg_left e2 hμd.le
  have e4 : μ ^ d * (ε / (μ ^ d + 1)) + ε / (μ ^ d + 1) = ε := by
    field_simp
  calc |φ₀ (dil r μ x) - μ ^ d * φ₀ x|
      ≤ |φ₀ (dil r μ x) - μ ^ d * (φ (dil r (l * μ) x) / (l * μ) ^ d)| +
        |μ ^ d * (φ (dil r (l * μ) x) / (l * μ) ^ d) - μ ^ d * φ₀ x| := abs_sub_le _ _ _
    _ ≤ ε / (μ ^ d + 1) + μ ^ d * (ε / (μ ^ d + 1)) := by
        gcongr
        rw [abs_sub_comm]; exact e1
    _ = ε := by linarith

/-- an exactly homogeneous continuous function of positive degree vanishes at 0 -/
lemma zero_of_exact {m : ℕ} (hm : 0 < m) {φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ}
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (hc : Continuous φ₀)
    (hex : ∀ μ : ℝ, 0 < μ → ∀ x : Fin m → ℝ, x ≠ 0 → φ₀ (dil r μ x) = μ ^ d * φ₀ x) :
    φ₀ 0 = 0 := by
  set y : Fin m → ℝ := Pi.single ⟨0, hm⟩ 1
  have hy : y ≠ 0 := by
    intro h; have := congrFun h ⟨0, hm⟩; simp [y] at this
  have h1 : Filter.Tendsto (fun t => dil r t y) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [tendsto_pi_nhds]
    intro i
    have := (((Real.continuous_rpow_const (hr i).le).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))).mul_const (y i)
    simpa [dil, Real.zero_rpow (hr i).ne'] using this
  have h2 := (hc.tendsto 0).comp h1
  have h3 : Filter.Tendsto (fun t : ℝ => t ^ d * φ₀ y) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (((Real.continuous_rpow_const hd.le).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))).mul_const (φ₀ y)
    simpa [Real.zero_rpow hd.ne'] using this
  have h4 : (φ₀ ∘ fun t => dil r t y) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun t => t ^ d * φ₀ y := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hex t ht y hy
  exact tendsto_nhds_unique (h2.congr' h4) h3

lemma exact_all {m : ℕ} (hm : 0 < m) {φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ}
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (hc : Continuous φ₀)
    (hex : ∀ μ : ℝ, 0 < μ → ∀ x : Fin m → ℝ, x ≠ 0 → φ₀ (dil r μ x) = μ ^ d * φ₀ x)
    (μ : ℝ) (hμ : 0 < μ) (x : Fin m → ℝ) : φ₀ (dil r μ x) = μ ^ d * φ₀ x := by
  by_cases hx : x = 0
  · subst hx; rw [dil_zero, zero_of_exact hm hr hd hc hex, mul_zero]
  · exact hex μ hμ x hx


lemma hn_zero {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) : hn r 0 = 0 := by
  unfold hn
  exact Finset.sum_eq_zero (fun i _ => by
    simp [Real.zero_rpow (inv_pos.2 (hr i)).ne'])

lemma bound_hn {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (C : Set (Fin m → ℝ))
    (hC : IsCompact C) : ∃ M : ℝ, 1 ≤ M ∧ ∀ x ∈ C, hn r x ≤ M := by
  obtain ⟨M, hM⟩ := hC.bddAbove_image (hn_continuous r hr).continuousOn
  exact ⟨max M 1, le_max_right _ _, fun x hx =>
    le_trans (hM ⟨x, hx, rfl⟩) (le_max_left _ _)⟩

lemma SZ_of_homogZero {m : ℕ} (hm : 0 < m) {φ φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ}
    (h : IsHomogZero φ r d φ₀) (hd : 0 < d) (hφ0 : φ 0 = 0) : SZ φ r d φ₀ := by
  have hex0 := fun μ (hμ : (0:ℝ) < μ) x (hx : x ≠ 0) => exact_zero_ne h hμ x hx
  obtain ⟨hr, -, -, hφ₀c, -, hconv⟩ := h
  have hex := exact_all hm hr hd hφ₀c hex0
  have hz := zero_of_exact hm hr hd hφ₀c hex0
  intro C hC ε hε
  obtain ⟨M, hM1, hM⟩ := bound_hn r hr C hC
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMd : 0 < M ^ d := Real.rpow_pos_of_pos hMpos d
  have h0S : (0 : Fin m → ℝ) ∉ {x : Fin m → ℝ | hn r x = 1} := by
    simp [hn_zero r hr]
  obtain ⟨l₀, hl₀, hlc⟩ := hconv _ (hn_sphere_compact r hr) h0S (ε / M ^ d) (div_pos hε hMd)
  refine ⟨l₀ / M, div_pos hl₀ hMpos, fun l hl hll x hx => ?_⟩
  by_cases hx0 : x = 0
  · subst hx0; simp [dil_zero, hφ0, hz]; exact hε.le
  obtain ⟨hμ, hs, hxe⟩ := decomp r hr x hx0
  set μ := hn r x
  set s := dil r μ⁻¹ x
  have hμM : μ ≤ M := hM x hx
  have hlμ : l * μ ≤ l₀ := by
    calc l * μ ≤ (l₀ / M) * M := mul_le_mul hll hμM hμ.le (div_pos hl₀ hMpos).le
      _ = l₀ := div_mul_cancel₀ _ hMpos.ne'
  have e := hlc (l * μ) (mul_pos hl hμ) hlμ s hs
  have h1 : φ (dil r l x) = φ (dil r (l * μ) s) := by
    rw [← dil_dil r hl.le hμ.le, hxe]
  have h2 : φ₀ x = μ ^ d * φ₀ s := by
    have := hex μ hμ s; rw [hxe] at this; exact this
  have h3 : φ (dil r (l * μ) s) / l ^ d = μ ^ d * (φ (dil r (l * μ) s) / (l * μ) ^ d) := by
    rw [Real.mul_rpow hl.le hμ.le]
    have : 0 < l ^ d := Real.rpow_pos_of_pos hl d
    have : 0 < μ ^ d := Real.rpow_pos_of_pos hμ d
    field_simp
  rw [h1, h2, h3, ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hμ d)]
  calc μ ^ d * |φ (dil r (l * μ) s) / (l * μ) ^ d - φ₀ s| ≤ M ^ d * (ε / M ^ d) :=
        mul_le_mul (Real.rpow_le_rpow hμ.le hμM hd.le) e (abs_nonneg _) hMd.le
    _ = ε := by field_simp

lemma SI_of_homogInfty {m : ℕ} (hm : 0 < m) {φ φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ}
    (h : IsHomogInfty φ r d φ₀) (hd : 0 < d) (hφ0 : φ 0 = 0) : SI φ r d φ₀ := by
  have hex0 := fun μ (hμ : (0:ℝ) < μ) x (hx : x ≠ 0) => exact_infty_ne h hμ x hx
  obtain ⟨hr, -, hφc, hφ₀c, -, hconv⟩ := h
  have hex := exact_all hm hr hd hφ₀c hex0
  have hz := zero_of_exact hm hr hd hφ₀c hex0
  intro C hC ε hε
  obtain ⟨M, hM1, hM⟩ := bound_hn r hr C hC
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMd : 0 < M ^ d := Real.rpow_pos_of_pos hMpos d
  set S := {x : Fin m → ℝ | hn r x = 1}
  have hS : IsCompact S := hn_sphere_compact r hr
  have h0S : (0 : Fin m → ℝ) ∉ S := by
    simp [S, hn_zero r hr]
  obtain ⟨l₀, hl₀, hlc⟩ := hconv _ hS h0S (ε / M ^ d) (div_pos hε hMd)
  -- bound of |φ| on the compact set {dil t s : t ∈ [0, l₀], s ∈ S}
  have hdilc : Continuous (fun p : ℝ × (Fin m → ℝ) => dil r p.1 p.2) := by
    apply continuous_pi; intro i
    exact ((Real.continuous_rpow_const (hr i).le).comp continuous_fst).mul
      ((continuous_apply i).comp continuous_snd)
  have hD : IsCompact ((fun p : ℝ × (Fin m → ℝ) => dil r p.1 p.2) '' (Set.Icc 0 l₀ ×ˢ S)) :=
    (isCompact_Icc.prod hS).image hdilc
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn hφc.continuousOn
  obtain ⟨B', hB'⟩ := hS.exists_bound_of_continuousOn hφ₀c.continuousOn
  set Q := (|B| + l₀ ^ d * |B'|) / ε + 1
  have htend := tendsto_rpow_atTop hd
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 htend Q)
  refine ⟨max a 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun l hl x hx => ?_⟩
  have hlpos : 0 < l := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hl)
  have hld : 0 < l ^ d := Real.rpow_pos_of_pos hlpos d
  have hQ : Q ≤ l ^ d := ha l (le_trans (le_max_left _ _) hl)
  by_cases hx0 : x = 0
  · subst hx0; simp [dil_zero, hφ0, hz]; exact hε.le
  obtain ⟨hμ, hs, hxe⟩ := decomp r hr x hx0
  set μ := hn r x
  set s := dil r μ⁻¹ x
  have hμM : μ ≤ M := hM x hx
  have h1 : φ (dil r l x) = φ (dil r (l * μ) s) := by
    rw [← dil_dil r hlpos.le hμ.le, hxe]
  have h2 : φ₀ x = μ ^ d * φ₀ s := by
    have := hex μ hμ s; rw [hxe] at this; exact this
  rw [h1, h2]
  by_cases hcase : l₀ ≤ l * μ
  · have e := hlc (l * μ) hcase s hs
    have h3 : φ (dil r (l * μ) s) / l ^ d = μ ^ d * (φ (dil r (l * μ) s) / (l * μ) ^ d) := by
      rw [Real.mul_rpow hlpos.le hμ.le]
      have : 0 < μ ^ d := Real.rpow_pos_of_pos hμ d
      field_simp
    rw [h3, ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hμ d)]
    calc μ ^ d * |φ (dil r (l * μ) s) / (l * μ) ^ d - φ₀ s| ≤ M ^ d * (ε / M ^ d) :=
          mul_le_mul (Real.rpow_le_rpow hμ.le hμM hd.le) e (abs_nonneg _) hMd.le
      _ = ε := by field_simp
  · push Not at hcase
    have hmem : dil r (l * μ) s ∈ (fun p : ℝ × (Fin m → ℝ) => dil r p.1 p.2) '' (Set.Icc 0 l₀ ×ˢ S) :=
      ⟨(l * μ, s), ⟨⟨(mul_pos hlpos hμ).le, hcase.le⟩, hs⟩, rfl⟩
    have hb1 : |φ (dil r (l * μ) s)| ≤ |B| := le_trans (hB _ hmem) (le_abs_self _)
    have hb2 : |φ₀ s| ≤ |B'| := le_trans (hB' s hs) (le_abs_self _)
    have hμl : μ ≤ l₀ / l := by
      rw [le_div_iff₀ hlpos]; linarith
    have hμd : μ ^ d ≤ l₀ ^ d / l ^ d := by
      rw [← Real.div_rpow hl₀.le hlpos.le]
      exact Real.rpow_le_rpow hμ.le hμl hd.le
    have hQ' : (|B| + l₀ ^ d * |B'|) / l ^ d ≤ ε := by
      rw [div_le_iff₀ hld]
      have : (|B| + l₀ ^ d * |B'|) / ε ≤ l ^ d := by simp only [Q] at hQ; linarith
      rw [div_le_iff₀ hε] at this; linarith
    calc |φ (dil r (l * μ) s) / l ^ d - μ ^ d * φ₀ s|
        ≤ |φ (dil r (l * μ) s) / l ^ d| + |μ ^ d * φ₀ s| := abs_sub _ _
      _ = |φ (dil r (l * μ) s)| / l ^ d + μ ^ d * |φ₀ s| := by
          rw [abs_div, abs_of_pos hld, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hμ d)]
      _ ≤ |B| / l ^ d + (l₀ ^ d / l ^ d) * |B'| := by
          gcongr
      _ = (|B| + l₀ ^ d * |B'|) / l ^ d := by ring
      _ ≤ ε := hQ'


section algebra
variable {m : ℕ} {r : Fin m → ℝ} {d d' : ℝ}

lemma SZ.zero : SZ (fun _ : Fin m → ℝ => (0:ℝ)) r d (fun _ => 0) :=
  fun _ _ ε hε => ⟨1, one_pos, fun l _ _ x _ => by simp; exact hε.le⟩

lemma SI.zero : SI (fun _ : Fin m → ℝ => (0:ℝ)) r d (fun _ => 0) :=
  fun _ _ ε hε => ⟨1, one_pos, fun l _ x _ => by simp; exact hε.le⟩

lemma SZ.add {φ φ₀ ψ ψ₀ : (Fin m → ℝ) → ℝ} (h1 : SZ φ r d φ₀) (h2 : SZ ψ r d ψ₀) :
    SZ (fun x => φ x + ψ x) r d (fun x => φ₀ x + ψ₀ x) := by
  intro C hC ε hε
  obtain ⟨a, ha, ha1⟩ := h1 C hC (ε / 2) (half_pos hε)
  obtain ⟨b, hb, hb'⟩ := h2 C hC (ε / 2) (half_pos hε)
  refine ⟨min a b, lt_min ha hb, fun l hl hll x hx => ?_⟩
  have e1 := ha1 l hl (le_trans hll (min_le_left _ _)) x hx
  have e2 := hb' l hl (le_trans hll (min_le_right _ _)) x hx
  rw [add_div]
  calc |φ (dil r l x) / l ^ d + ψ (dil r l x) / l ^ d - (φ₀ x + ψ₀ x)|
      = |(φ (dil r l x) / l ^ d - φ₀ x) + (ψ (dil r l x) / l ^ d - ψ₀ x)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add e1 e2
    _ = ε := by ring

lemma SI.add {φ φ₀ ψ ψ₀ : (Fin m → ℝ) → ℝ} (h1 : SI φ r d φ₀) (h2 : SI ψ r d ψ₀) :
    SI (fun x => φ x + ψ x) r d (fun x => φ₀ x + ψ₀ x) := by
  intro C hC ε hε
  obtain ⟨a, ha, ha1⟩ := h1 C hC (ε / 2) (half_pos hε)
  obtain ⟨b, hb, hb'⟩ := h2 C hC (ε / 2) (half_pos hε)
  refine ⟨max a b, lt_max_of_lt_left ha, fun l hll x hx => ?_⟩
  have e1 := ha1 l (le_trans (le_max_left _ _) hll) x hx
  have e2 := hb' l (le_trans (le_max_right _ _) hll) x hx
  rw [add_div]
  calc |φ (dil r l x) / l ^ d + ψ (dil r l x) / l ^ d - (φ₀ x + ψ₀ x)|
      = |(φ (dil r l x) / l ^ d - φ₀ x) + (ψ (dil r l x) / l ^ d - ψ₀ x)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add e1 e2
    _ = ε := by ring

lemma SZ.const_mul (c : ℝ) {φ φ₀ : (Fin m → ℝ) → ℝ} (h : SZ φ r d φ₀) :
    SZ (fun x => c * φ x) r d (fun x => c * φ₀ x) := by
  intro C hC ε hε
  obtain ⟨a, ha, h'⟩ := h C hC (ε / (|c| + 1)) (by positivity)
  refine ⟨a, ha, fun l hl hll x hx => ?_⟩
  have e := h' l hl hll x hx
  rw [mul_div_assoc, ← mul_sub, abs_mul]
  calc |c| * |φ (dil r l x) / l ^ d - φ₀ x| ≤ (|c| + 1) * (ε / (|c| + 1)) :=
        mul_le_mul (by linarith) e (abs_nonneg _) (by positivity)
    _ = ε := by field_simp

lemma SI.const_mul (c : ℝ) {φ φ₀ : (Fin m → ℝ) → ℝ} (h : SI φ r d φ₀) :
    SI (fun x => c * φ x) r d (fun x => c * φ₀ x) := by
  intro C hC ε hε
  obtain ⟨a, ha, h'⟩ := h C hC (ε / (|c| + 1)) (by positivity)
  refine ⟨a, ha, fun l hll x hx => ?_⟩
  have e := h' l hll x hx
  rw [mul_div_assoc, ← mul_sub, abs_mul]
  calc |c| * |φ (dil r l x) / l ^ d - φ₀ x| ≤ (|c| + 1) * (ε / (|c| + 1)) :=
        mul_le_mul (by linarith) e (abs_nonneg _) (by positivity)
    _ = ε := by field_simp

lemma mul_est {a a₀ b b₀ A B δ : ℝ} (ha : |a - a₀| ≤ δ) (hb : |b - b₀| ≤ δ) (hA : |a₀| ≤ A)
    (hB : |b₀| ≤ B) (hδ : δ ≤ 1) (hδ0 : 0 ≤ δ) : |a * b - a₀ * b₀| ≤ δ * (A + B + 1) := by
  have hb' : |b| ≤ B + δ := by
    calc |b| = |(b - b₀) + b₀| := by ring_nf
      _ ≤ |b - b₀| + |b₀| := abs_add_le _ _
      _ ≤ δ + B := add_le_add hb hB
      _ = B + δ := by ring
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) hA
  calc |a * b - a₀ * b₀| = |(a - a₀) * b + a₀ * (b - b₀)| := by ring_nf
    _ ≤ |(a - a₀) * b| + |a₀ * (b - b₀)| := abs_add_le _ _
    _ = |a - a₀| * |b| + |a₀| * |b - b₀| := by rw [abs_mul, abs_mul]
    _ ≤ δ * (B + δ) + A * δ := by
        gcongr
    _ ≤ δ * (A + B + 1) := by nlinarith

lemma SZ.mul {φ φ₀ ψ ψ₀ : (Fin m → ℝ) → ℝ} (h1 : SZ φ r d φ₀) (h2 : SZ ψ r d' ψ₀)
    (hc1 : Continuous φ₀) (hc2 : Continuous ψ₀) :
    SZ (fun x => φ x * ψ x) r (d + d') (fun x => φ₀ x * ψ₀ x) := by
  intro C hC ε hε
  obtain ⟨A, hA⟩ := hC.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc2.continuousOn
  set δ := min 1 (ε / (|A| + |B| + 1))
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  obtain ⟨a, ha, ha1⟩ := h1 C hC δ hδ0
  obtain ⟨b, hb, hb'⟩ := h2 C hC δ hδ0
  refine ⟨min a b, lt_min ha hb, fun l hl hll x hx => ?_⟩
  have e1 := ha1 l hl (le_trans hll (min_le_left _ _)) x hx
  have e2 := hb' l hl (le_trans hll (min_le_right _ _)) x hx
  have hsplit : φ (dil r l x) * ψ (dil r l x) / l ^ (d + d') =
      (φ (dil r l x) / l ^ d) * (ψ (dil r l x) / l ^ d') := by
    rw [Real.rpow_add hl]; field_simp
  rw [hsplit]
  have := mul_est e1 e2 (le_trans (hA x hx) (le_abs_self _)) (le_trans (hB x hx) (le_abs_self _))
    (min_le_left _ _) hδ0.le
  calc _ ≤ δ * (|A| + |B| + 1) := this
    _ ≤ (ε / (|A| + |B| + 1)) * (|A| + |B| + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    _ = ε := by field_simp

lemma SI.mul {φ φ₀ ψ ψ₀ : (Fin m → ℝ) → ℝ} (h1 : SI φ r d φ₀) (h2 : SI ψ r d' ψ₀)
    (hc1 : Continuous φ₀) (hc2 : Continuous ψ₀) :
    SI (fun x => φ x * ψ x) r (d + d') (fun x => φ₀ x * ψ₀ x) := by
  intro C hC ε hε
  obtain ⟨A, hA⟩ := hC.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc2.continuousOn
  set δ := min 1 (ε / (|A| + |B| + 1))
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  obtain ⟨a, ha, ha1⟩ := h1 C hC δ hδ0
  obtain ⟨b, hb, hb'⟩ := h2 C hC δ hδ0
  refine ⟨max a b, lt_max_of_lt_left ha, fun l hll x hx => ?_⟩
  have hl : 0 < l := lt_of_lt_of_le ha (le_trans (le_max_left _ _) hll)
  have e1 := ha1 l (le_trans (le_max_left _ _) hll) x hx
  have e2 := hb' l (le_trans (le_max_right _ _) hll) x hx
  have hsplit : φ (dil r l x) * ψ (dil r l x) / l ^ (d + d') =
      (φ (dil r l x) / l ^ d) * (ψ (dil r l x) / l ^ d') := by
    rw [Real.rpow_add hl]; field_simp
  rw [hsplit]
  have := mul_est e1 e2 (le_trans (hA x hx) (le_abs_self _)) (le_trans (hB x hx) (le_abs_self _))
    (min_le_left _ _) hδ0.le
  calc _ ≤ δ * (|A| + |B| + 1) := this
    _ ≤ (ε / (|A| + |B| + 1)) * (|A| + |B| + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    _ = ε := by field_simp

lemma SZ.sum {ι : Type*} (s : Finset ι) {f g : ι → (Fin m → ℝ) → ℝ}
    (h : ∀ i ∈ s, SZ (f i) r d (g i)) :
    SZ (fun x => ∑ i ∈ s, f i x) r d (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SZ.zero (m := m) (r := r) (d := d))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact SZ.add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma SI.sum {ι : Type*} (s : Finset ι) {f g : ι → (Fin m → ℝ) → ℝ}
    (h : ∀ i ∈ s, SI (f i) r d (g i)) :
    SI (fun x => ∑ i ∈ s, f i x) r d (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SI.zero (m := m) (r := r) (d := d))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact SI.add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma SZ.exact {φ : (Fin m → ℝ) → ℝ} (h : ∀ l : ℝ, 0 < l → ∀ x, φ (dil r l x) = l ^ d * φ x) :
    SZ φ r d φ := fun _ _ ε hε => ⟨1, one_pos, fun l hl _ x _ => by
      rw [h l hl x, mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hl d).ne']; simp; exact hε.le⟩

lemma SI.exact {φ : (Fin m → ℝ) → ℝ} (h : ∀ l : ℝ, 0 < l → ∀ x, φ (dil r l x) = l ^ d * φ x) :
    SI φ r d φ := fun _ _ ε hε => ⟨1, one_pos, fun l hl x _ => by
      have hl' : 0 < l := lt_of_lt_of_le one_pos hl
      rw [h l hl' x, mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hl' d).ne']; simp; exact hε.le⟩

lemma SZ.coord (j : Fin m) : SZ (fun x : Fin m → ℝ => x j) r (r j) (fun x => x j) :=
  SZ.exact (fun l _ x => by simp [dil])

lemma SI.coord (j : Fin m) : SI (fun x : Fin m → ℝ => x j) r (r j) (fun x => x j) :=
  SI.exact (fun l _ x => by simp [dil])

lemma SZ.deg {φ φ₀ : (Fin m → ℝ) → ℝ} (h : SZ φ r d φ₀) (e : d = d') : SZ φ r d' φ₀ := e ▸ h
lemma SI.deg {φ φ₀ : (Fin m → ℝ) → ℝ} (h : SI φ r d φ₀) (e : d = d') : SI φ r d' φ₀ := e ▸ h

lemma SZ.congr {φ φ₀ ψ ψ₀ : (Fin m → ℝ) → ℝ} (h : SZ φ r d φ₀) (e1 : φ = ψ) (e2 : φ₀ = ψ₀) :
    SZ ψ r d ψ₀ := e1 ▸ e2 ▸ h
lemma SI.congr {φ φ₀ ψ ψ₀ : (Fin m → ℝ) → ℝ} (h : SI φ r d φ₀) (e1 : φ = ψ) (e2 : φ₀ = ψ₀) :
    SI ψ r d ψ₀ := e1 ▸ e2 ▸ h

lemma SZ.comp {k : ℕ} {ρ : Fin k → ℝ} {φ φ₀ : (Fin m → ℝ) → ℝ} (h : SZ φ r d φ₀)
    (P : (Fin k → ℝ) → (Fin m → ℝ)) (hP : Continuous P)
    (hPd : ∀ l : ℝ, 0 < l → ∀ y, P (dil ρ l y) = dil r l (P y)) :
    SZ (fun y => φ (P y)) ρ d (fun y => φ₀ (P y)) := by
  intro C hC ε hε
  obtain ⟨a, ha, h'⟩ := h (P '' C) (hC.image hP) ε hε
  exact ⟨a, ha, fun l hl hll y hy => by
    beta_reduce; rw [hPd l hl y]; exact h' l hl hll (P y) ⟨y, hy, rfl⟩⟩

lemma SI.comp {k : ℕ} {ρ : Fin k → ℝ} {φ φ₀ : (Fin m → ℝ) → ℝ} (h : SI φ r d φ₀)
    (P : (Fin k → ℝ) → (Fin m → ℝ)) (hP : Continuous P)
    (hPd : ∀ l : ℝ, 0 < l → ∀ y, P (dil ρ l y) = dil r l (P y)) :
    SI (fun y => φ (P y)) ρ d (fun y => φ₀ (P y)) := by
  intro C hC ε hε
  obtain ⟨a, ha, h'⟩ := h (P '' C) (hC.image hP) ε hε
  exact ⟨a, ha, fun l hll y hy => by
    beta_reduce; rw [hPd l (lt_of_lt_of_le ha hll) y]; exact h' l hll (P y) ⟨y, hy, rfl⟩⟩

lemma SZ.toHomog {φ φ₀ : (Fin m → ℝ) → ℝ} (h : SZ φ r d φ₀) (hr : ∀ i, 0 < r i) (hd : 0 ≤ d)
    (hc : Continuous φ) (hc₀ : Continuous φ₀) (hne : ∃ x, φ₀ x ≠ 0) : IsHomogZero φ r d φ₀ :=
  ⟨hr, hd, hc, hc₀, hne, fun C hC _ ε hε => h C hC ε hε⟩

lemma SI.toHomog {φ φ₀ : (Fin m → ℝ) → ℝ} (h : SI φ r d φ₀) (hr : ∀ i, 0 < r i) (hd : 0 ≤ d)
    (hc : Continuous φ) (hc₀ : Continuous φ₀) (hne : ∃ x, φ₀ x ≠ 0) : IsHomogInfty φ r d φ₀ :=
  ⟨hr, hd, hc, hc₀, hne, fun C hC _ ε hε => h C hC ε hε⟩

end algebra

end HBLRed


open HomogBiLimit.OutputFeedback

namespace HBLRed

section weights
variable {n : ℕ} {𝔡 : ℝ}

lemma adm_mul (hn : 2 ≤ n) (h : AdmissibleDegree n 𝔡) : -1 < 𝔡 ∧ 𝔡 * ((n:ℝ) - 1) < 1 := by
  have hn1 : (0:ℝ) < n - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact ⟨h.1, by have := h.2; rwa [lt_div_iff₀ hn1] at this⟩

lemma weight_pos (hn : 2 ≤ n) (h : AdmissibleDegree n 𝔡) {k : ℕ} (hk : k < n) :
    0 < weight n 𝔡 k := by
  unfold weight
  have hk' : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ k := k.cast_nonneg
  obtain ⟨h1, h2⟩ := adm_mul hn h
  rcases le_or_gt 0 𝔡 with hd | hd
  · nlinarith [mul_le_mul_of_nonneg_left (show (n:ℝ) - 1 - k ≤ n - 1 by linarith) hd]
  · nlinarith [mul_nonneg (neg_nonneg.2 hd.le) (show (0:ℝ) ≤ n - 1 - k by linarith)]

lemma weight_dpos (hn : 2 ≤ n) (h : AdmissibleDegree n 𝔡) {k : ℕ} (hk : k < n) :
    0 < 𝔡 + weight n 𝔡 k := by
  unfold weight
  have hk' : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ k := k.cast_nonneg
  obtain ⟨h1, h2⟩ := adm_mul hn h
  rcases le_or_gt 0 𝔡 with hd | hd
  · nlinarith [mul_le_mul_of_nonneg_left (show (n:ℝ) - 2 - k ≤ n - 1 by linarith) hd]
  · nlinarith [mul_nonneg (neg_nonneg.2 hd.le) (show (0:ℝ) ≤ n - 1 - k by linarith)]

lemma weight_lt (hn : 2 ≤ n) (h : AdmissibleDegree n 𝔡) {k : ℕ} (hk : k < n) :
    weight n 𝔡 k < (n:ℝ) + 1 := by
  unfold weight
  have hk' : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ k := k.cast_nonneg
  obtain ⟨h1, h2⟩ := adm_mul hn h
  nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 + 𝔡 by linarith) (show (0:ℝ) ≤ n - 1 - k by linarith)]

lemma weight_succ (k : ℕ) : weight n 𝔡 (k + 1) = 𝔡 + weight n 𝔡 k := by
  unfold weight; push_cast; ring

lemma weight_last (hn : 1 ≤ n) : weight n 𝔡 (n - 1) = 1 := by
  unfold weight; rw [Nat.cast_sub hn]; push_cast; ring

lemma weights_apply (j : Fin n) : weights n 𝔡 0 n j = weight n 𝔡 j.val := by
  simp [weights]

end weights

section gas

lemma gas_zero {m : ℕ} {f : (Fin m → ℝ) → (Fin m → ℝ)} (h : IsGAS f) : f 0 = 0 := by
  have := h.1.1 0 le_rfl
  simp only [euclidField] at this
  have h2 := congrArg (fun v => WithLp.ofLp v) this
  simpa using h2

lemma gas_comp_ne {m : ℕ} {f : (Fin m → ℝ) → (Fin m → ℝ)} (h : IsGAS f) (j : Fin m) :
    ∃ y, f y j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨-, ⟨hex, -⟩, hatt⟩, -⟩ := h
  obtain ⟨x, hx, hx0⟩ := hex (EuclideanSpace.single j 1)
  obtain ⟨T, hT, hTx'⟩ := hatt 2 two_pos (1/2) (by norm_num)
  have hTx := hTx' x hx (by rw [hx0]; simp)
  have hcoord : x T j = 1 := by
    obtain ⟨hint, heq⟩ := hx T hT
    have h1 : (∫ τ in (0:ℝ)..T, euclidField f τ (x τ)) j = 0 := by
      have := ContinuousLinearMap.intervalIntegral_comp_comm
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) j) hint
      simp only [PiLp.proj_apply] at this
      rw [← this]
      simp [euclidField, hcon]
    rw [heq]
    simp [h1, hx0]
  have := le_trans (PiLp.norm_apply_le (x T) j) (hTx T le_rfl)
  rw [hcoord] at this
  norm_num at this

end gas

section fields
variable {n : ℕ}

lemma feedback_apply_lt {φ : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) (i : Fin n) (h : i.val + 1 < n) :
    feedbackField φ x i = x ⟨i.val + 1, h⟩ := by
  simp [feedbackField, shift, lastInput, h, Nat.ne_of_lt h]

lemma feedback_apply_last {φ : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) (i : Fin n) (h : ¬ i.val + 1 < n) :
    feedbackField φ x i = φ x := by
  have h' : i.val + 1 = n := by omega
  simp [feedbackField, shift, lastInput, h']

lemma error_apply {K : (Fin n → ℝ) → (Fin n → ℝ)} (x : Fin n → ℝ) (i : Fin n) :
    errorField K x i = shift n x i + K (axisVec n (first x)) i := by
  simp [errorField]

lemma shift_apply_lt (x : Fin n → ℝ) (i : Fin n) (h : i.val + 1 < n) :
    shift n x i = x ⟨i.val + 1, h⟩ := by simp [shift, h]

lemma shift_apply_last (x : Fin n → ℝ) (i : Fin n) (h : ¬ i.val + 1 < n) :
    shift n x i = 0 := by simp [shift, h]

lemma axisVec_zero : axisVec n 0 = 0 := by funext j; simp [axisVec]

lemma first_zero : first (0 : Fin n → ℝ) = 0 := by simp [first]

lemma feedback_phi_zero {φ : (Fin n → ℝ) → ℝ} (hn : 0 < n) (h : feedbackField φ 0 = 0) :
    φ 0 = 0 := by
  have := congrFun h ⟨n - 1, by omega⟩
  rwa [feedback_apply_last 0 ⟨n - 1, by omega⟩ (by simp; omega)] at this

lemma error_K_zero {K : (Fin n → ℝ) → (Fin n → ℝ)} (h : errorField K 0 = 0) : K 0 = 0 := by
  have h0 : shift n (0 : Fin n → ℝ) = 0 := by funext j; simp [shift]
  simpa [errorField, axisVec_zero, first_zero, h0] using h

lemma axis_first_dil (hn : 0 < n) (r : Fin n → ℝ) (l : ℝ) (x : Fin n → ℝ) :
    axisVec n (first (dil r l x)) = dil r l (axisVec n (first x)) := by
  funext j
  simp only [axisVec, first, dil, hn, dite_true]
  split_ifs with hj
  · have : j = ⟨0, hn⟩ := Fin.ext hj
    subst this; rfl
  · simp

lemma axis_first_cont : Continuous (fun x : Fin n → ℝ => axisVec n (first x)) := by
  apply continuous_pi; intro j
  simp only [axisVec, first]
  split_ifs <;> fun_prop

lemma feedback_cont {φ : (Fin n → ℝ) → ℝ} (h : Continuous φ) : Continuous (feedbackField φ) := by
  apply continuous_pi; intro i
  simp only [feedbackField, shift, lastInput, Pi.add_apply]
  split_ifs <;> fun_prop

lemma error_cont {K : (Fin n → ℝ) → (Fin n → ℝ)} (h : Continuous K) : Continuous (errorField K) := by
  apply continuous_pi; intro i
  have hK : Continuous (fun x : Fin n → ℝ => K (axisVec n (first x)) i) :=
    (continuous_apply i).comp (h.comp axis_first_cont)
  simp only [errorField, Pi.add_apply]
  refine Continuous.add ?_ hK
  simp only [shift]
  split_ifs <;> fun_prop

end fields


section fieldhom
variable {n : ℕ} {𝔡 : ℝ}

lemma wpos (hn : 2 ≤ n) (h : AdmissibleDegree n 𝔡) : ∀ i, 0 < weights n 𝔡 0 n i := by
  intro i; rw [weights_apply]; exact weight_pos hn h i.isLt

lemma wdpos (hn : 2 ≤ n) (h : AdmissibleDegree n 𝔡) (i : Fin n) : 0 < 𝔡 + weights n 𝔡 0 n i := by
  rw [weights_apply]; exact weight_dpos hn h i.isLt

lemma wsucc (i : Fin n) (h : i.val + 1 < n) :
    weights n 𝔡 0 n ⟨i.val + 1, h⟩ = 𝔡 + weights n 𝔡 0 n i := by
  rw [weights_apply, weights_apply, weight_succ]

lemma wlast (i : Fin n) (h : ¬ i.val + 1 < n) : 1 + 𝔡 = 𝔡 + weights n 𝔡 0 n i := by
  rw [weights_apply, show i.val = n - 1 by omega, weight_last (by omega)]; ring

lemma fb_SZ (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {φ φ₀ : (Fin n → ℝ) → ℝ}
    (hφ : IsHomogZero φ (weights n 𝔡 0 n) (1 + 𝔡) φ₀) (hφ0 : φ 0 = 0) (i : Fin n) :
    SZ (fun x => feedbackField φ x i) (weights n 𝔡 0 n) (𝔡 + weights n 𝔡 0 n i)
      (fun x => feedbackField φ₀ x i) := by
  by_cases h : i.val + 1 < n
  · refine ((SZ.coord (r := weights n 𝔡 0 n) ⟨i.val + 1, h⟩).deg (wsucc i h)).congr ?_ ?_
    · funext x; rw [feedback_apply_lt x i h]
    · funext x; rw [feedback_apply_lt x i h]
  · have := SZ_of_homogZero (by omega) hφ (by linarith [h𝔡.1]) hφ0
    refine (this.deg (wlast i h)).congr ?_ ?_
    · funext x; rw [feedback_apply_last x i h]
    · funext x; rw [feedback_apply_last x i h]

lemma fb_SI (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {φ φ₀ : (Fin n → ℝ) → ℝ}
    (hφ : IsHomogInfty φ (weights n 𝔡 0 n) (1 + 𝔡) φ₀) (hφ0 : φ 0 = 0) (i : Fin n) :
    SI (fun x => feedbackField φ x i) (weights n 𝔡 0 n) (𝔡 + weights n 𝔡 0 n i)
      (fun x => feedbackField φ₀ x i) := by
  by_cases h : i.val + 1 < n
  · refine ((SI.coord (r := weights n 𝔡 0 n) ⟨i.val + 1, h⟩).deg (wsucc i h)).congr ?_ ?_
    · funext x; rw [feedback_apply_lt x i h]
    · funext x; rw [feedback_apply_lt x i h]
  · have := SI_of_homogInfty (by omega) hφ (by linarith [h𝔡.1]) hφ0
    refine (this.deg (wlast i h)).congr ?_ ?_
    · funext x; rw [feedback_apply_last x i h]
    · funext x; rw [feedback_apply_last x i h]

lemma shift_SZ (i : Fin n) :
    SZ (fun x => shift n x i) (weights n 𝔡 0 n) (𝔡 + weights n 𝔡 0 n i) (fun x => shift n x i) := by
  by_cases h : i.val + 1 < n
  · refine ((SZ.coord (r := weights n 𝔡 0 n) ⟨i.val + 1, h⟩).deg (wsucc i h)).congr ?_ ?_
    · funext x; rw [shift_apply_lt x i h]
    · funext x; rw [shift_apply_lt x i h]
  · refine SZ.zero.congr ?_ ?_
    · funext x; rw [shift_apply_last x i h]
    · funext x; rw [shift_apply_last x i h]

lemma shift_SI (i : Fin n) :
    SI (fun x => shift n x i) (weights n 𝔡 0 n) (𝔡 + weights n 𝔡 0 n i) (fun x => shift n x i) := by
  by_cases h : i.val + 1 < n
  · refine ((SI.coord (r := weights n 𝔡 0 n) ⟨i.val + 1, h⟩).deg (wsucc i h)).congr ?_ ?_
    · funext x; rw [shift_apply_lt x i h]
    · funext x; rw [shift_apply_lt x i h]
  · refine SI.zero.congr ?_ ?_
    · funext x; rw [shift_apply_last x i h]
    · funext x; rw [shift_apply_last x i h]

lemma Kax_SZ (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hK : IsHomogZeroVF K (weights n 𝔡 0 n) 𝔡 K₀) (hK0 : K 0 = 0) (i : Fin n) :
    SZ (fun x => K (axisVec n (first x)) i) (weights n 𝔡 0 n) (𝔡 + weights n 𝔡 0 n i)
      (fun x => K₀ (axisVec n (first x)) i) :=
  (SZ_of_homogZero (by omega) (hK.2 i).2 (wdpos hn h𝔡 i) (by simp [hK0])).comp
    (fun x => axisVec n (first x)) axis_first_cont (fun l _ x => axis_first_dil (by omega) _ l x)

lemma Kax_SI (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hK : IsHomogInftyVF K (weights n 𝔡 0 n) 𝔡 K₀) (hK0 : K 0 = 0) (i : Fin n) :
    SI (fun x => K (axisVec n (first x)) i) (weights n 𝔡 0 n) (𝔡 + weights n 𝔡 0 n i)
      (fun x => K₀ (axisVec n (first x)) i) :=
  (SI_of_homogInfty (by omega) (hK.2 i).2 (wdpos hn h𝔡 i) (by simp [hK0])).comp
    (fun x => axisVec n (first x)) axis_first_cont (fun l _ x => axis_first_dil (by omega) _ l x)

lemma err_SZ (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hK : IsHomogZeroVF K (weights n 𝔡 0 n) 𝔡 K₀) (hK0 : K 0 = 0) (i : Fin n) :
    SZ (fun x => errorField K x i) (weights n 𝔡 0 n) (𝔡 + weights n 𝔡 0 n i)
      (fun x => errorField K₀ x i) :=
  (SZ.add (shift_SZ i) (Kax_SZ hn h𝔡 hK hK0 i)).congr (by funext x; rw [error_apply])
    (by funext x; rw [error_apply])

lemma err_SI (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hK : IsHomogInftyVF K (weights n 𝔡 0 n) 𝔡 K₀) (hK0 : K 0 = 0) (i : Fin n) :
    SI (fun x => errorField K x i) (weights n 𝔡 0 n) (𝔡 + weights n 𝔡 0 n i)
      (fun x => errorField K₀ x i) :=
  (SI.add (shift_SI i) (Kax_SI hn h𝔡 hK hK0 i)).congr (by funext x; rw [error_apply])
    (by funext x; rw [error_apply])

end fieldhom

section fieldVF
variable {n : ℕ} {𝔡₀ 𝔡inf : ℝ}

lemma fb_VF (hn : 2 ≤ n) (h𝔡₀ : AdmissibleDegree n 𝔡₀) (h𝔡inf : AdmissibleDegree n 𝔡inf)
    {φ φ₀ φinf : (Fin n → ℝ) → ℝ}
    (hφ : IsHomogBiLimit φ (weights n 𝔡₀ 0 n) (1 + 𝔡₀) φ₀ (weights n 𝔡inf 0 n) (1 + 𝔡inf) φinf)
    (hφ0 : φ 0 = 0) (hg₀ : IsGAS (feedbackField φ₀)) (hginf : IsGAS (feedbackField φinf)) :
    IsHomogBiLimitVF (feedbackField φ) (weights n 𝔡₀ 0 n) 𝔡₀ (feedbackField φ₀)
      (weights n 𝔡inf 0 n) 𝔡inf (feedbackField φinf) := by
  refine ⟨⟨wpos hn h𝔡₀, fun i => ⟨(wdpos hn h𝔡₀ i).le, ?_⟩⟩,
    ⟨wpos hn h𝔡inf, fun i => ⟨(wdpos hn h𝔡inf i).le, ?_⟩⟩⟩
  · exact (fb_SZ hn h𝔡₀ hφ.1 hφ0 i).toHomog (wpos hn h𝔡₀) (wdpos hn h𝔡₀ i).le
      ((continuous_apply i).comp (feedback_cont hφ.1.2.2.1))
      ((continuous_apply i).comp (feedback_cont hφ.1.2.2.2.1)) (gas_comp_ne hg₀ i)
  · exact (fb_SI hn h𝔡inf hφ.2 hφ0 i).toHomog (wpos hn h𝔡inf) (wdpos hn h𝔡inf i).le
      ((continuous_apply i).comp (feedback_cont hφ.2.2.2.1))
      ((continuous_apply i).comp (feedback_cont hφ.2.2.2.2.1)) (gas_comp_ne hginf i)

lemma K_cont0 {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)} {r : Fin n → ℝ} {𝔡 : ℝ}
    (h : IsHomogZeroVF K r 𝔡 K₀) : Continuous K ∧ Continuous K₀ :=
  ⟨continuous_pi (fun i => (h.2 i).2.2.2.1), continuous_pi (fun i => (h.2 i).2.2.2.2.1)⟩

lemma K_contI {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)} {r : Fin n → ℝ} {𝔡 : ℝ}
    (h : IsHomogInftyVF K r 𝔡 K₀) : Continuous K ∧ Continuous K₀ :=
  ⟨continuous_pi (fun i => (h.2 i).2.2.2.1), continuous_pi (fun i => (h.2 i).2.2.2.2.1)⟩

lemma err_VF (hn : 2 ≤ n) (h𝔡₀ : AdmissibleDegree n 𝔡₀) (h𝔡inf : AdmissibleDegree n 𝔡inf)
    {K K₀ Kinf : (Fin n → ℝ) → (Fin n → ℝ)}
    (hK : IsHomogBiLimitVF K (weights n 𝔡₀ 0 n) 𝔡₀ K₀ (weights n 𝔡inf 0 n) 𝔡inf Kinf)
    (hK0 : K 0 = 0) (hg₀ : IsGAS (errorField K₀)) (hginf : IsGAS (errorField Kinf)) :
    IsHomogBiLimitVF (errorField K) (weights n 𝔡₀ 0 n) 𝔡₀ (errorField K₀)
      (weights n 𝔡inf 0 n) 𝔡inf (errorField Kinf) := by
  refine ⟨⟨wpos hn h𝔡₀, fun i => ⟨(wdpos hn h𝔡₀ i).le, ?_⟩⟩,
    ⟨wpos hn h𝔡inf, fun i => ⟨(wdpos hn h𝔡inf i).le, ?_⟩⟩⟩
  · exact (err_SZ hn h𝔡₀ hK.1 hK0 i).toHomog (wpos hn h𝔡₀) (wdpos hn h𝔡₀ i).le
      ((continuous_apply i).comp (error_cont (K_cont0 hK.1).1))
      ((continuous_apply i).comp (error_cont (K_cont0 hK.1).2)) (gas_comp_ne hg₀ i)
  · exact (err_SI hn h𝔡inf hK.2 hK0 i).toHomog (wpos hn h𝔡inf) (wdpos hn h𝔡inf i).le
      ((continuous_apply i).comp (error_cont (K_contI hK.2).1))
      ((continuous_apply i).comp (error_cont (K_contI hK.2).2)) (gas_comp_ne hginf i)

end fieldVF

section selfhom
variable {m : ℕ}

lemma self_of_zero (hm : 0 < m) {φ φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ}
    (h : IsHomogZero φ r d φ₀) (hd : 0 < d) : IsHomogBiLimit φ₀ r d φ₀ r d φ₀ := by
  have hex := exact_all hm h.1 hd h.2.2.2.1 (fun μ hμ x hx => exact_zero_ne h hμ x hx)
  exact ⟨(SZ.exact hex).toHomog h.1 hd.le h.2.2.2.1 h.2.2.2.1 h.2.2.2.2.1,
    (SI.exact hex).toHomog h.1 hd.le h.2.2.2.1 h.2.2.2.1 h.2.2.2.2.1⟩

lemma self_of_infty (hm : 0 < m) {φ φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ}
    (h : IsHomogInfty φ r d φ₀) (hd : 0 < d) : IsHomogBiLimit φ₀ r d φ₀ r d φ₀ := by
  have hex := exact_all hm h.1 hd h.2.2.2.1 (fun μ hμ x hx => exact_infty_ne h hμ x hx)
  exact ⟨(SZ.exact hex).toHomog h.1 hd.le h.2.2.2.1 h.2.2.2.1 h.2.2.2.2.1,
    (SI.exact hex).toHomog h.1 hd.le h.2.2.2.1 h.2.2.2.1 h.2.2.2.2.1⟩

lemma selfVF_of_zero (hm : 0 < m) {f f₀ : (Fin m → ℝ) → (Fin m → ℝ)} {r : Fin m → ℝ} {𝔡 : ℝ}
    (h : IsHomogZeroVF f r 𝔡 f₀) (hd : ∀ i, 0 < 𝔡 + r i) : IsHomogBiLimitVF f₀ r 𝔡 f₀ r 𝔡 f₀ :=
  ⟨⟨h.1, fun i => ⟨(h.2 i).1, (self_of_zero hm (h.2 i).2 (hd i)).1⟩⟩,
    ⟨h.1, fun i => ⟨(h.2 i).1, (self_of_zero hm (h.2 i).2 (hd i)).2⟩⟩⟩

lemma selfVF_of_infty (hm : 0 < m) {f f₀ : (Fin m → ℝ) → (Fin m → ℝ)} {r : Fin m → ℝ} {𝔡 : ℝ}
    (h : IsHomogInftyVF f r 𝔡 f₀) (hd : ∀ i, 0 < 𝔡 + r i) : IsHomogBiLimitVF f₀ r 𝔡 f₀ r 𝔡 f₀ :=
  ⟨⟨h.1, fun i => ⟨(h.2 i).1, (self_of_infty hm (h.2 i).2 (hd i)).1⟩⟩,
    ⟨h.1, fun i => ⟨(h.2 i).1, (self_of_infty hm (h.2 i).2 (hd i)).2⟩⟩⟩

end selfhom

end HBLRed


open HomogBiLimit.OutputFeedback

namespace HBLRed

section blocks
variable {n : ℕ}

def Xp (w : Fin (n + n) → ℝ) : Fin n → ℝ := fun i => w (Fin.castAdd n i)
def Ep (w : Fin (n + n) → ℝ) : Fin n → ℝ := fun i => w (Fin.natAdd n i)

lemma Xp_dil (r : Fin n → ℝ) (l : ℝ) (w : Fin (n + n) → ℝ) :
    Xp (dil (Fin.append r r) l w) = dil r l (Xp w) := by
  funext i; simp [Xp, dil, Fin.append_left]

lemma Ep_dil (r : Fin n → ℝ) (l : ℝ) (w : Fin (n + n) → ℝ) :
    Ep (dil (Fin.append r r) l w) = dil r l (Ep w) := by
  funext i; simp only [Ep, dil]; rw [Fin.append_right]

lemma Xp_cont : Continuous (Xp (n := n)) := continuous_pi (fun _ => continuous_apply _)
lemma Ep_cont : Continuous (Ep (n := n)) := continuous_pi (fun _ => continuous_apply _)

lemma Xp_append (a b : Fin n → ℝ) : Xp (Fin.append a b) = a := by
  funext i; simp [Xp, Fin.append_left]
lemma Ep_append (a b : Fin n → ℝ) : Ep (Fin.append a b) = b := by
  funext i; simp only [Ep]; exact Fin.append_right a b i

lemma eq_zero_of_blocks (w : Fin (n + n) → ℝ) (h1 : Xp w = 0) (h2 : Ep w = 0) : w = 0 := by
  rw [← Fin.append_castAdd_natAdd (f := w)]
  have e1 : (fun i => w (Fin.castAdd n i)) = 0 := h1
  have e2 : (fun i => w (Fin.natAdd n i)) = 0 := h2
  rw [e1, e2]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

lemma append_pos {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) : ∀ i, 0 < Fin.append r r i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; exact hr j
  · rw [Fin.append_right]; exact hr j

end blocks

lemma fderiv_eq_sum {m : ℕ} (V : (Fin m → ℝ) → ℝ) (x v : Fin m → ℝ) :
    fderiv ℝ V x v = ∑ i, partialDeriv V i x * v i := by
  have hv : v = ∑ i, v i • (Pi.single i (1:ℝ) : Fin m → ℝ) := by
    funext j; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]; rfl

lemma pd_zero {m : ℕ} {V : (Fin m → ℝ) → ℝ} (hnn : ∀ x, 0 ≤ V x) (h0 : V 0 = 0) (i : Fin m) :
    partialDeriv V i 0 = 0 := by
  have hmin : IsLocalMin V 0 := Filter.Eventually.of_forall (fun y => by rw [h0]; exact hnn y)
  simp [partialDeriv, hmin.fderiv_eq_zero]

lemma pd_cont {m : ℕ} {V : (Fin m → ℝ) → ℝ} (hV : ContDiff ℝ 1 V) (i : Fin m) :
    Continuous (partialDeriv V i) :=
  (hV.continuous_fderiv one_ne_zero).clm_apply continuous_const

section etagamma
variable {n : ℕ} {𝔡 : ℝ}

lemma eta_SZ (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {V V₀ : (Fin n → ℝ) → ℝ} {dU : ℝ}
    (hV₀ : ContDiff ℝ 1 V₀)
    (hVhom : ∀ i, IsHomogZero (partialDeriv V i) (weights n 𝔡 0 n) (dU - weights n 𝔡 0 n i)
      (partialDeriv V₀ i))
    (hVpd0 : ∀ i, partialDeriv V i 0 = 0) (hdU : ∀ i, weights n 𝔡 0 n i < dU)
    {φ φ₀ : (Fin n → ℝ) → ℝ} (hφ : IsHomogZero φ (weights n 𝔡 0 n) (1 + 𝔡) φ₀) (hφ0 : φ 0 = 0)
    {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)} (hK : IsHomogZeroVF K (weights n 𝔡 0 n) 𝔡 K₀)
    (hK0 : K 0 = 0) :
    SZ (fun w => fderiv ℝ V (Xp w) (feedbackField φ (Xp w) + K (axisVec n (first (Ep w)))))
      (Fin.append (weights n 𝔡 0 n) (weights n 𝔡 0 n)) (dU + 𝔡)
      (fun w => fderiv ℝ V₀ (Xp w) (feedbackField φ₀ (Xp w) + K₀ (axisVec n (first (Ep w))))) := by
  set r := weights n 𝔡 0 n
  have hK₀c := (K_cont0 hK).2
  have term : ∀ i, SZ (fun w => partialDeriv V i (Xp w) *
      (feedbackField φ (Xp w) i + K (axisVec n (first (Ep w))) i)) (Fin.append r r) (dU + 𝔡)
      (fun w => partialDeriv V₀ i (Xp w) *
      (feedbackField φ₀ (Xp w) i + K₀ (axisVec n (first (Ep w))) i)) := by
    intro i
    have h1 := (SZ_of_homogZero (by omega) (hVhom i) (by linarith [hdU i]) (hVpd0 i)).comp
      Xp Xp_cont (fun l _ w => Xp_dil r l w)
    have h2 := (fb_SZ hn h𝔡 hφ hφ0 i).comp Xp Xp_cont (fun l _ w => Xp_dil r l w)
    have h3 := (Kax_SZ hn h𝔡 hK hK0 i).comp Ep Ep_cont (fun l _ w => Ep_dil r l w)
    have h23 := SZ.add h2 h3
    refine (SZ.mul h1 h23 ((pd_cont hV₀ i).comp Xp_cont) ?_).deg (by ring)
    exact ((continuous_apply i).comp ((feedback_cont hφ.2.2.2.1).comp Xp_cont)).add
      ((continuous_apply i).comp (hK₀c.comp (axis_first_cont.comp Ep_cont)))
  refine (SZ.sum Finset.univ (fun i _ => term i)).congr ?_ ?_
  · funext w; rw [fderiv_eq_sum]; simp
  · funext w; rw [fderiv_eq_sum]; simp

lemma eta_SI (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {V V₀ : (Fin n → ℝ) → ℝ} {dU : ℝ}
    (hV₀ : ContDiff ℝ 1 V₀)
    (hVhom : ∀ i, IsHomogInfty (partialDeriv V i) (weights n 𝔡 0 n) (dU - weights n 𝔡 0 n i)
      (partialDeriv V₀ i))
    (hVpd0 : ∀ i, partialDeriv V i 0 = 0) (hdU : ∀ i, weights n 𝔡 0 n i < dU)
    {φ φ₀ : (Fin n → ℝ) → ℝ} (hφ : IsHomogInfty φ (weights n 𝔡 0 n) (1 + 𝔡) φ₀) (hφ0 : φ 0 = 0)
    {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)} (hK : IsHomogInftyVF K (weights n 𝔡 0 n) 𝔡 K₀)
    (hK0 : K 0 = 0) :
    SI (fun w => fderiv ℝ V (Xp w) (feedbackField φ (Xp w) + K (axisVec n (first (Ep w)))))
      (Fin.append (weights n 𝔡 0 n) (weights n 𝔡 0 n)) (dU + 𝔡)
      (fun w => fderiv ℝ V₀ (Xp w) (feedbackField φ₀ (Xp w) + K₀ (axisVec n (first (Ep w))))) := by
  set r := weights n 𝔡 0 n
  have hK₀c := (K_contI hK).2
  have term : ∀ i, SI (fun w => partialDeriv V i (Xp w) *
      (feedbackField φ (Xp w) i + K (axisVec n (first (Ep w))) i)) (Fin.append r r) (dU + 𝔡)
      (fun w => partialDeriv V₀ i (Xp w) *
      (feedbackField φ₀ (Xp w) i + K₀ (axisVec n (first (Ep w))) i)) := by
    intro i
    have h1 := (SI_of_homogInfty (by omega) (hVhom i) (by linarith [hdU i]) (hVpd0 i)).comp
      Xp Xp_cont (fun l _ w => Xp_dil r l w)
    have h2 := (fb_SI hn h𝔡 hφ hφ0 i).comp Xp Xp_cont (fun l _ w => Xp_dil r l w)
    have h3 := (Kax_SI hn h𝔡 hK hK0 i).comp Ep Ep_cont (fun l _ w => Ep_dil r l w)
    have h23 := SI.add h2 h3
    refine (SI.mul h1 h23 ((pd_cont hV₀ i).comp Xp_cont) ?_).deg (by ring)
    exact ((continuous_apply i).comp ((feedback_cont hφ.2.2.2.1).comp Xp_cont)).add
      ((continuous_apply i).comp (hK₀c.comp (axis_first_cont.comp Ep_cont)))
  refine (SI.sum Finset.univ (fun i _ => term i)).congr ?_ ?_
  · funext w; rw [fderiv_eq_sum]; simp
  · funext w; rw [fderiv_eq_sum]; simp

lemma gamma_SZ (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {W W₀ : (Fin n → ℝ) → ℝ} {dU : ℝ}
    (hW₀ : ContDiff ℝ 1 W₀)
    (hWhom : ∀ i, IsHomogZero (partialDeriv W i) (weights n 𝔡 0 n) (dU - weights n 𝔡 0 n i)
      (partialDeriv W₀ i))
    (hWpd0 : ∀ i, partialDeriv W i 0 = 0) (hdU : ∀ i, weights n 𝔡 0 n i < dU)
    {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)} (hK : IsHomogZeroVF K (weights n 𝔡 0 n) 𝔡 K₀)
    (hK0 : K 0 = 0) :
    SZ (fun w => -fderiv ℝ W (Ep w) (errorField K (Ep w)))
      (Fin.append (weights n 𝔡 0 n) (weights n 𝔡 0 n)) (dU + 𝔡)
      (fun w => -fderiv ℝ W₀ (Ep w) (errorField K₀ (Ep w))) := by
  set r := weights n 𝔡 0 n
  have hK₀c := (K_cont0 hK).2
  have term : ∀ i, SZ (fun w => partialDeriv W i (Ep w) * errorField K (Ep w) i)
      (Fin.append r r) (dU + 𝔡) (fun w => partialDeriv W₀ i (Ep w) * errorField K₀ (Ep w) i) := by
    intro i
    have h1 := (SZ_of_homogZero (by omega) (hWhom i) (by linarith [hdU i]) (hWpd0 i)).comp
      Ep Ep_cont (fun l _ w => Ep_dil r l w)
    have h2 := (err_SZ hn h𝔡 hK hK0 i).comp Ep Ep_cont (fun l _ w => Ep_dil r l w)
    exact (SZ.mul h1 h2 ((pd_cont hW₀ i).comp Ep_cont)
      ((continuous_apply i).comp ((error_cont hK₀c).comp Ep_cont))).deg (by ring)
  refine ((SZ.sum Finset.univ (fun i _ => term i)).const_mul (-1)).congr ?_ ?_
  · funext w; rw [fderiv_eq_sum]; simp
  · funext w; rw [fderiv_eq_sum]; simp

lemma gamma_SI (hn : 2 ≤ n) (h𝔡 : AdmissibleDegree n 𝔡) {W W₀ : (Fin n → ℝ) → ℝ} {dU : ℝ}
    (hW₀ : ContDiff ℝ 1 W₀)
    (hWhom : ∀ i, IsHomogInfty (partialDeriv W i) (weights n 𝔡 0 n) (dU - weights n 𝔡 0 n i)
      (partialDeriv W₀ i))
    (hWpd0 : ∀ i, partialDeriv W i 0 = 0) (hdU : ∀ i, weights n 𝔡 0 n i < dU)
    {K K₀ : (Fin n → ℝ) → (Fin n → ℝ)} (hK : IsHomogInftyVF K (weights n 𝔡 0 n) 𝔡 K₀)
    (hK0 : K 0 = 0) :
    SI (fun w => -fderiv ℝ W (Ep w) (errorField K (Ep w)))
      (Fin.append (weights n 𝔡 0 n) (weights n 𝔡 0 n)) (dU + 𝔡)
      (fun w => -fderiv ℝ W₀ (Ep w) (errorField K₀ (Ep w))) := by
  set r := weights n 𝔡 0 n
  have hK₀c := (K_contI hK).2
  have term : ∀ i, SI (fun w => partialDeriv W i (Ep w) * errorField K (Ep w) i)
      (Fin.append r r) (dU + 𝔡) (fun w => partialDeriv W₀ i (Ep w) * errorField K₀ (Ep w) i) := by
    intro i
    have h1 := (SI_of_homogInfty (by omega) (hWhom i) (by linarith [hdU i]) (hWpd0 i)).comp
      Ep Ep_cont (fun l _ w => Ep_dil r l w)
    have h2 := (err_SI hn h𝔡 hK hK0 i).comp Ep Ep_cont (fun l _ w => Ep_dil r l w)
    exact (SI.mul h1 h2 ((pd_cont hW₀ i).comp Ep_cont)
      ((continuous_apply i).comp ((error_cont hK₀c).comp Ep_cont))).deg (by ring)
  refine ((SI.sum Finset.univ (fun i _ => term i)).const_mul (-1)).congr ?_ ?_
  · funext w; rw [fderiv_eq_sum]; simp
  · funext w; rw [fderiv_eq_sum]; simp

end etagamma

end HBLRed


open HomogBiLimit.OutputFeedback

namespace HBLRed

section closed
variable {n : ℕ}

noncomputable def xhC (n : ℕ) : (Fin (n + n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.natAdd n i))

noncomputable def EC (n : ℕ) (L : ℝ) : (Fin (n + n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + n) => ℝ) (Fin.natAdd n i) -
      (1 / L ^ (i : ℕ)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + n) => ℝ)
        (Fin.castAdd n i))

lemma xhC_apply (z : Fin (n + n) → ℝ) (i : Fin n) : xhC n z i = z (Fin.natAdd n i) := rfl

lemma EC_apply (L : ℝ) (z : Fin (n + n) → ℝ) (i : Fin n) :
    EC n L z i = z (Fin.natAdd n i) - 1 / L ^ (i : ℕ) * z (Fin.castAdd n i) := by
  simp [EC]

lemma xhC_eq (z : Fin (n + n) → ℝ) : xhC n z = fun i => z (Fin.natAdd n i) := rfl

lemma append_cont {α : Type*} [TopologicalSpace α] {f g : α → (Fin n → ℝ)}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun p => Fin.append (f p) (g p)) := by
  apply continuous_pi; intro k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [Fin.append_left]; exact (continuous_apply j).comp hf
  · simp only [Fin.append_right]; exact (continuous_apply j).comp hg

lemma shift_cont : Continuous (shift n) := by
  apply continuous_pi; intro i; simp only [shift]; split_ifs <;> fun_prop

lemma lastInput_cont : Continuous (lastInput n) := by
  apply continuous_pi; intro i; simp only [lastInput]; split_ifs <;> fun_prop

lemma first_cont : Continuous (first (m := n)) := by
  by_cases h : 0 < n
  · have : (first (m := n)) = fun x => x ⟨0, h⟩ := by funext x; simp [first, h]
    rw [this]; fun_prop
  · have : (first (m := n)) = fun _ => 0 := by funext x; simp [first, h]
    rw [this]; fun_prop

lemma axisVec_cont : Continuous (axisVec n) := by
  apply continuous_pi; intro i; simp only [axisVec]; split_ifs <;> fun_prop

lemma cl_eq (φ : (Fin n → ℝ) → ℝ) (K : (Fin n → ℝ) → (Fin n → ℝ)) (L : ℝ) :
    closedLoop n φ K L = fun z => Fin.append
      (shift n (fun i => z (Fin.castAdd n i)) + lastInput n (L ^ n * φ (fun i => z (Fin.natAdd n i))))
      (L • (shift n (fun i => z (Fin.natAdd n i)) + lastInput n (φ (fun i => z (Fin.natAdd n i))) +
        K (axisVec n (first (fun i => z (Fin.castAdd n i)) - first (fun i => z (Fin.natAdd n i)))))) :=
  rfl

lemma cl_cont {φ : (Fin n → ℝ) → ℝ} {K : (Fin n → ℝ) → (Fin n → ℝ)} (L : ℝ)
    (hφ : Continuous φ) (hK : Continuous K) : Continuous (closedLoop n φ K L) := by
  rw [cl_eq]
  have hx : Continuous (fun z : Fin (n + n) → ℝ => fun i => z (Fin.castAdd n i)) :=
    continuous_pi (fun _ => continuous_apply _)
  have hxh : Continuous (fun z : Fin (n + n) → ℝ => fun i => z (Fin.natAdd n i)) :=
    continuous_pi (fun _ => continuous_apply _)
  apply append_cont
  · exact (shift_cont.comp hx).add (lastInput_cont.comp (continuous_const.mul (hφ.comp hxh)))
  · exact Continuous.const_smul (((shift_cont.comp hxh).add (lastInput_cont.comp (hφ.comp hxh))).add
      (hK.comp (axisVec_cont.comp ((first_cont.comp hx).sub (first_cont.comp hxh))))) L

lemma cl_zero {φ : (Fin n → ℝ) → ℝ} {K : (Fin n → ℝ) → (Fin n → ℝ)} (L : ℝ)
    (hφ0 : φ 0 = 0) (hK0 : K 0 = 0) : closedLoop n φ K L 0 = 0 := by
  rw [cl_eq]
  have h1 : (fun i : Fin n => (0 : Fin (n + n) → ℝ) (Fin.castAdd n i)) = 0 := rfl
  have h2 : (fun i : Fin n => (0 : Fin (n + n) → ℝ) (Fin.natAdd n i)) = 0 := rfl
  have hs : shift n (0 : Fin n → ℝ) = 0 := by funext j; simp [shift]
  have hl : lastInput n 0 = 0 := by funext j; simp [lastInput]
  simp only [h1, h2, hs, hl, hφ0, first_zero, sub_zero, axisVec_zero, hK0, mul_zero, add_zero,
    smul_zero]
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

lemma neg_axis (s : ℝ) : -(axisVec n s) = axisVec n (-s) := by
  funext j; simp only [axisVec, Pi.neg_apply]; split_ifs <;> simp

lemma first_EC (hn : 0 < n) (L : ℝ) (z : Fin (n + n) → ℝ) :
    first (EC n L z) = first (fun i => z (Fin.natAdd n i)) - first (fun i => z (Fin.castAdd n i)) := by
  simp [first, hn, EC_apply]

/-- key identity A: the observer coordinates -/
lemma keyA (hn : 0 < n) (φ : (Fin n → ℝ) → ℝ) (Kp : (Fin n → ℝ) → (Fin n → ℝ)) (L : ℝ)
    (z : Fin (n + n) → ℝ) :
    xhC n (closedLoop n φ (fun y => Kp (-y)) L z) =
      L • (feedbackField φ (xhC n z) + Kp (axisVec n (first (EC n L z)))) := by
  funext i
  rw [xhC_apply, cl_eq]
  simp only
  rw [Fin.append_right, first_EC hn, neg_axis, neg_sub, xhC_eq]
  rfl

/-- key identity B: the error coordinates -/
lemma keyB (hn : 0 < n) (φ : (Fin n → ℝ) → ℝ) (Kp : (Fin n → ℝ) → (Fin n → ℝ)) {L : ℝ}
    (hL : 0 < L) (z : Fin (n + n) → ℝ) :
    EC n L (closedLoop n φ (fun y => Kp (-y)) L z) = L • errorField Kp (EC n L z) := by
  funext i
  rw [EC_apply, cl_eq]
  simp only
  rw [Fin.append_right, Fin.append_left]
  simp only [errorField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [first_EC hn, neg_axis, neg_sub]
  have hLi : (0:ℝ) < L ^ (i : ℕ) := pow_pos hL _
  by_cases h : i.val + 1 < n
  · rw [shift_apply_lt _ i h, shift_apply_lt _ i h, shift_apply_lt _ i h, EC_apply]
    have hl : lastInput n (L ^ n * φ (fun i => z (Fin.natAdd n i))) i = 0 := by
      simp [lastInput, Nat.ne_of_lt h]
    have hl' : lastInput n (φ (fun i => z (Fin.natAdd n i))) i = 0 := by
      simp [lastInput, Nat.ne_of_lt h]
    rw [hl, hl']
    simp only [pow_succ]
    field_simp
    ring
  · rw [shift_apply_last _ i h, shift_apply_last _ i h, shift_apply_last _ i h]
    have h' : i.val + 1 = n := by omega
    have hl : ∀ u : ℝ, lastInput n u i = u := fun u => by simp [lastInput, h']
    rw [hl, hl]
    have hpow : L ^ n = L ^ (i : ℕ) * L := by
      have : n = (i : ℕ) + 1 := h'.symm
      calc L ^ n = L ^ ((i : ℕ) + 1) := by rw [← this]
        _ = L ^ (i : ℕ) * L := pow_succ _ _
    rw [hpow]
    field_simp
    ring

lemma zG {L : ℝ} (hL : 0 < L) (z : Fin (n + n) → ℝ) :
    z = Fin.append (fun i => L ^ (i : ℕ) * (xhC n z i - EC n L z i)) (xhC n z) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · rw [Fin.append_left, EC_apply, xhC_apply]
    have : (0:ℝ) < L ^ (j : ℕ) := pow_pos hL _
    field_simp
    ring
  · rw [Fin.append_right, xhC_apply]

theorem closed_gas (hn : 0 < n) {φ : (Fin n → ℝ) → ℝ} {Kp : (Fin n → ℝ) → (Fin n → ℝ)}
    (hφc : Continuous φ) (hKc : Continuous Kp) (hφ0 : φ 0 = 0) (hK0 : Kp 0 = 0)
    {V W : (Fin n → ℝ) → ℝ} (hV : ContDiff ℝ 1 V) (hW : ContDiff ℝ 1 W)
    (hVnn : ∀ x, 0 ≤ V x) (hWnn : ∀ x, 0 ≤ W x) (hVpd : IsPosDef V) (hWpd : IsPosDef W)
    (hVpr : IsProper V) (hWpr : IsProper W) {c : ℝ} (hc : 0 < c)
    (hkey : ∀ a e : Fin n → ℝ, (a ≠ 0 ∨ e ≠ 0) →
      fderiv ℝ V a (feedbackField φ a + Kp (axisVec n (first e))) +
        c * fderiv ℝ W e (errorField Kp e) < 0)
    (lyap : ∀ (f : (Fin (n + n) → ℝ) → (Fin (n + n) → ℝ)), Continuous f → f 0 = 0 →
      ∀ U : (Fin (n + n) → ℝ) → ℝ, ContDiff ℝ 1 U → IsPosDef U → IsProper U →
        IsNegDef (fun x => fderiv ℝ U x (f x)) → IsGAS f)
    {L : ℝ} (hL : 0 < L) : IsGAS (closedLoop n φ (fun y => Kp (-y)) L) := by
  set F := closedLoop n φ (fun y => Kp (-y)) L
  set U : (Fin (n + n) → ℝ) → ℝ := fun z => V (xhC n z) + c * W (EC n L z)
  have hVd : Differentiable ℝ V := hV.differentiable one_ne_zero
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have hderiv : ∀ z v, fderiv ℝ U z v =
      fderiv ℝ V (xhC n z) (xhC n v) + c * fderiv ℝ W (EC n L z) (EC n L v) := by
    intro z v
    have h := ((hVd _).hasFDerivAt.comp z (xhC n).hasFDerivAt).add
      (((hWd _).hasFDerivAt.comp z (EC n L).hasFDerivAt).const_mul c)
    rw [show U = (V ∘ xhC n + fun y => c * (W ∘ EC n L) y) from rfl, h.fderiv]
    simp
  have hnz : ∀ z, z ≠ 0 → xhC n z ≠ 0 ∨ EC n L z ≠ 0 := by
    intro z hz
    by_contra hcon
    push Not at hcon
    apply hz
    rw [zG hL z, hcon.1, hcon.2]
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; simp
    · rw [Fin.append_right]; rfl
  refine lyap F (cl_cont L hφc (hKc.comp continuous_neg)) (cl_zero L hφ0 (by simp [hK0])) U
    ((hV.comp (xhC n).contDiff).add (contDiff_const.mul (hW.comp (EC n L).contDiff))) ?_ ?_ ?_
  · -- positive definite
    refine ⟨by simp [U, hVpd.1, hWpd.1], fun z hz => ?_⟩
    rcases hnz z hz with h | h
    · have := hVpd.2 _ h
      have := hWnn (EC n L z)
      simp only [U]; nlinarith
    · have := hWpd.2 _ h
      have := hVnn (xhC n z)
      simp only [U]; nlinarith
  · -- proper
    unfold IsProper
    rw [Filter.tendsto_atTop]
    intro b
    obtain ⟨KV, hKVc, hKV⟩ := Filter.mem_cocompact.1 (Filter.tendsto_atTop.1 hVpr b)
    obtain ⟨KW, hKWc, hKW⟩ := Filter.mem_cocompact.1 (Filter.tendsto_atTop.1 hWpr (b / c))
    show {z | b ≤ U z} ∈ Filter.cocompact _
    rw [Filter.mem_cocompact]
    have hGc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (Fin.append (fun i => L ^ (i : ℕ) * (p.1 i - p.2 i)) p.1 : Fin (n + n) → ℝ)) :=
      append_cont (continuous_pi (fun i => continuous_const.mul
        (((continuous_apply i).comp continuous_fst).sub ((continuous_apply i).comp continuous_snd))))
        continuous_fst
    refine ⟨_, (hKVc.prod hKWc).image hGc, fun z hz => ?_⟩
    simp only [Set.mem_ofPred_eq]
    by_cases h1 : xhC n z ∈ KV
    · by_cases h2 : EC n L z ∈ KW
      · exact absurd ⟨(xhC n z, EC n L z), ⟨h1, h2⟩, (zG hL z).symm⟩ hz
      · have h3 : b / c ≤ W (EC n L z) := hKW h2
        have h4 := hVnn (xhC n z)
        have h5 : b ≤ c * W (EC n L z) := by
          rw [div_le_iff₀ hc] at h3; linarith
        simp only [U]; linarith
    · have h3 : b ≤ V (xhC n z) := hKV h1
      have h4 := hWnn (EC n L z)
      simp only [U]; nlinarith
  · -- negative definite derivative
    refine ⟨by
      have h0 : F 0 = 0 := cl_zero L hφ0 (K := fun y => Kp (-y)) (by simp [hK0])
      simp [h0], fun z hz => ?_⟩
    simp only
    rw [hderiv, keyA hn, keyB hn φ Kp hL, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have := hkey (xhC n z) (EC n L z) (hnz z hz)
    nlinarith

end closed

end HBLRed


open HomogBiLimit.OutputFeedback

namespace HBLRed

lemma negdef_nonpos {m : ℕ} {g : (Fin m → ℝ) → ℝ} (h : IsNegDef g) (x : Fin m → ℝ) : g x ≤ 0 := by
  by_cases hx : x = 0
  · rw [hx, h.1]
  · exact (h.2 x hx).le

section mainsec
variable {n : ℕ}

lemma gamma_nonneg {W : (Fin n → ℝ) → ℝ} {K : (Fin n → ℝ) → (Fin n → ℝ)}
    (hWn : IsNegDef (fun x => fderiv ℝ W x (errorField K x))) (w : Fin (n + n) → ℝ) :
    0 ≤ -fderiv ℝ W (Ep w) (errorField K (Ep w)) := by
  have : fderiv ℝ W (Ep w) (errorField K (Ep w)) ≤ 0 := negdef_nonpos hWn (Ep w)
  linarith

lemma hyp_aux {V W : (Fin n → ℝ) → ℝ} {φ : (Fin n → ℝ) → ℝ} {K : (Fin n → ℝ) → (Fin n → ℝ)}
    (hK0 : K 0 = 0) (hVn : IsNegDef (fun x => fderiv ℝ V x (feedbackField φ x)))
    (hWn : IsNegDef (fun x => fderiv ℝ W x (errorField K x))) (w : Fin (n + n) → ℝ)
    (hw : w ≠ 0) (hγ : -fderiv ℝ W (Ep w) (errorField K (Ep w)) = 0) :
    fderiv ℝ V (Xp w) (feedbackField φ (Xp w) + K (axisVec n (first (Ep w)))) < 0 := by
  have hE : Ep w = 0 := by
    by_contra hE
    have : fderiv ℝ W (Ep w) (errorField K (Ep w)) < 0 := hWn.2 _ hE
    linarith
  have hX : Xp w ≠ 0 := fun hX => hw (eq_zero_of_blocks w hX hE)
  rw [hE, first_zero, axisVec_zero, hK0, add_zero]
  exact hVn.2 _ hX

lemma dil_neg {m : ℕ} (r : Fin m → ℝ) (l : ℝ) (x : Fin m → ℝ) : dil r l (-x) = -dil r l x := by
  funext i; simp [dil]

lemma negZ {m : ℕ} {φ φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ} (h : IsHomogZero φ r d φ₀) :
    IsHomogZero (fun x => φ (-x)) r d (fun x => φ₀ (-x)) := by
  obtain ⟨hr, hd, hc, hc0, ⟨x, hx⟩, hconv⟩ := h
  refine ⟨hr, hd, hc.comp continuous_neg, hc0.comp continuous_neg, ⟨-x, by simpa using hx⟩,
    fun C hC h0 ε hε => ?_⟩
  obtain ⟨l₀, hl₀, h'⟩ := hconv ((fun y => -y) '' C) (hC.image continuous_neg)
    (fun ⟨y, hy, hy0⟩ => h0 (by simp at hy0; rw [hy0] at hy; exact hy)) ε hε
  exact ⟨l₀, hl₀, fun l hl hll y hy => by
    beta_reduce; rw [← dil_neg]; exact h' l hl hll (-y) ⟨y, hy, rfl⟩⟩

lemma negI {m : ℕ} {φ φ₀ : (Fin m → ℝ) → ℝ} {r : Fin m → ℝ} {d : ℝ} (h : IsHomogInfty φ r d φ₀) :
    IsHomogInfty (fun x => φ (-x)) r d (fun x => φ₀ (-x)) := by
  obtain ⟨hr, hd, hc, hc0, ⟨x, hx⟩, hconv⟩ := h
  refine ⟨hr, hd, hc.comp continuous_neg, hc0.comp continuous_neg, ⟨-x, by simpa using hx⟩,
    fun C hC h0 ε hε => ?_⟩
  obtain ⟨l₀, hl₀, h'⟩ := hconv ((fun y => -y) '' C) (hC.image continuous_neg)
    (fun ⟨y, hy, hy0⟩ => h0 (by simp at hy0; rw [hy0] at hy; exact hy)) ε hε
  exact ⟨l₀, hl₀, fun l hll y hy => by
    beta_reduce; rw [← dil_neg]; exact h' l hll (-y) ⟨y, hy, rfl⟩⟩

lemma negVF {m : ℕ} {K K₀ Kinf : (Fin m → ℝ) → (Fin m → ℝ)} {r₀ rinf : Fin m → ℝ} {𝔡₀ 𝔡inf : ℝ}
    (h : IsHomogBiLimitVF K r₀ 𝔡₀ K₀ rinf 𝔡inf Kinf) :
    IsHomogBiLimitVF (fun y => K (-y)) r₀ 𝔡₀ (fun y => K₀ (-y)) rinf 𝔡inf (fun y => Kinf (-y)) :=
  ⟨⟨h.1.1, fun i => ⟨(h.1.2 i).1, negZ (h.1.2 i).2⟩⟩, ⟨h.2.1, fun i => ⟨(h.2.2 i).1, negI (h.2.2 i).2⟩⟩⟩

theorem main_gen (hn : 2 ≤ n) {𝔡₀ 𝔡inf : ℝ}
    (h𝔡₀ : AdmissibleDegree n 𝔡₀) (h𝔡inf : AdmissibleDegree n 𝔡inf)
    {φ φ₀ φinf : (Fin n → ℝ) → ℝ} {Kp Kp₀ Kpinf : (Fin n → ℝ) → (Fin n → ℝ)}
    (hφ : IsHomogBiLimit φ (weights n 𝔡₀ 0 n) (1 + 𝔡₀) φ₀ (weights n 𝔡inf 0 n) (1 + 𝔡inf) φinf)
    (hK : IsHomogBiLimitVF Kp (weights n 𝔡₀ 0 n) 𝔡₀ Kp₀ (weights n 𝔡inf 0 n) 𝔡inf Kpinf)
    (hgφ : IsGAS (feedbackField φ) ∧ IsGAS (feedbackField φ₀) ∧ IsGAS (feedbackField φinf))
    (hgK : IsGAS (errorField Kp) ∧ IsGAS (errorField Kp₀) ∧ IsGAS (errorField Kpinf))
    {L : ℝ} (hL : 0 < L) : IsGAS (closedLoop n φ (fun y => Kp (-y)) L) := by
  have hn0 : 0 < n := by omega
  obtain ⟨hg1, hg2, hg3⟩ := hgφ
  obtain ⟨he1, he2, he3⟩ := hgK
  have hφ0 := feedback_phi_zero hn0 (gas_zero hg1)
  have hφ₀0 := feedback_phi_zero hn0 (gas_zero hg2)
  have hφi0 := feedback_phi_zero hn0 (gas_zero hg3)
  have hK0 := error_K_zero (gas_zero he1)
  have hK₀0 := error_K_zero (gas_zero he2)
  have hKi0 := error_K_zero (gas_zero he3)
  have hfVF := fb_VF hn h𝔡₀ h𝔡inf hφ hφ0 hg2 hg3
  have hgVF := err_VF hn h𝔡₀ h𝔡inf hK hK0 he2 he3
  set dU : ℝ := (n : ℝ) + 1 with hdUdef
  have hdU₀ : ∀ i, weights n 𝔡₀ 0 n i < dU := fun i => by
    rw [weights_apply]; exact weight_lt hn h𝔡₀ i.isLt
  have hdUi : ∀ i, weights n 𝔡inf 0 n i < dU := fun i => by
    rw [weights_apply]; exact weight_lt hn h𝔡inf i.isLt
  obtain ⟨V, V₀, Vi, hVc, hV₀c, hVic, hVnn, hVpd, hVpr, hVhom, hVneg, hV₀neg, hVineg⟩ :=
    theorem_2_20 (feedbackField φ) (feedbackField φ₀) (feedbackField φinf) _ _ 𝔡₀ 𝔡inf hfVF
      ⟨hg1, hg3, hg2⟩ dU dU hdUi hdU₀
  obtain ⟨W, W₀, Wi, hWc, hW₀c, hWic, hWnn, hWpd, hWpr, hWhom, hWneg, hW₀neg, hWineg⟩ :=
    theorem_2_20 (errorField Kp) (errorField Kp₀) (errorField Kpinf) _ _ 𝔡₀ 𝔡inf hgVF
      ⟨he1, he3, he2⟩ dU dU hdUi hdU₀
  have hVpd0 : ∀ i, partialDeriv V i 0 = 0 := pd_zero hVnn hVpd.1
  have hWpd0 : ∀ i, partialDeriv W i 0 = 0 := pd_zero hWnn hWpd.1
  have hηZ := eta_SZ hn h𝔡₀ hV₀c (fun i => (hVhom i).1) hVpd0 hdU₀ hφ.1 hφ0 hK.1 hK0
  have hηI := eta_SI hn h𝔡inf hVic (fun i => (hVhom i).2) hVpd0 hdUi hφ.2 hφ0 hK.2 hK0
  have hγZ := gamma_SZ hn h𝔡₀ hW₀c (fun i => (hWhom i).1) hWpd0 hdU₀ hK.1 hK0
  have hγI := gamma_SI hn h𝔡inf hWic (fun i => (hWhom i).2) hWpd0 hdUi hK.2 hK0
  -- continuity
  have cη : ∀ (V' : (Fin n → ℝ) → ℝ), ContDiff ℝ 1 V' → ∀ φ' : (Fin n → ℝ) → ℝ, Continuous φ' →
      ∀ K' : (Fin n → ℝ) → (Fin n → ℝ), Continuous K' →
      Continuous (fun w : Fin (n + n) → ℝ =>
        fderiv ℝ V' (Xp w) (feedbackField φ' (Xp w) + K' (axisVec n (first (Ep w))))) :=
    fun V' hV' φ' hφ' K' hK' => ((hV'.continuous_fderiv one_ne_zero).comp Xp_cont).clm_apply
      (((feedback_cont hφ').comp Xp_cont).add (hK'.comp (axis_first_cont.comp Ep_cont)))
  have cγ : ∀ (W' : (Fin n → ℝ) → ℝ), ContDiff ℝ 1 W' →
      ∀ K' : (Fin n → ℝ) → (Fin n → ℝ), Continuous K' →
      Continuous (fun w : Fin (n + n) → ℝ => -fderiv ℝ W' (Ep w) (errorField K' (Ep w))) :=
    fun W' hW' K' hK' => (((hW'.continuous_fderiv one_ne_zero).comp Ep_cont).clm_apply
      ((error_cont hK').comp Ep_cont)).neg
  have hKc := K_cont0 hK.1
  have hKic := K_contI hK.2
  -- a nonzero vector
  set e0 : Fin n → ℝ := Pi.single ⟨0, hn0⟩ 1
  have he0 : e0 ≠ 0 := by
    intro h; have := congrFun h ⟨0, hn0⟩; simp [e0] at this
  have hne_eta : ∀ (V' : (Fin n → ℝ) → ℝ) (φ' : (Fin n → ℝ) → ℝ) (K' : (Fin n → ℝ) → (Fin n → ℝ)),
      K' 0 = 0 → IsNegDef (fun x => fderiv ℝ V' x (feedbackField φ' x)) →
      ∃ w : Fin (n + n) → ℝ,
        fderiv ℝ V' (Xp w) (feedbackField φ' (Xp w) + K' (axisVec n (first (Ep w)))) ≠ 0 := by
    intro V' φ' K' hK' hneg
    refine ⟨Fin.append e0 0, ?_⟩
    rw [Xp_append, Ep_append, first_zero, axisVec_zero, hK', add_zero]
    exact (hneg.2 e0 he0).ne
  have hne_gamma : ∀ (W' : (Fin n → ℝ) → ℝ) (K' : (Fin n → ℝ) → (Fin n → ℝ)),
      IsNegDef (fun x => fderiv ℝ W' x (errorField K' x)) →
      ∃ w : Fin (n + n) → ℝ, -fderiv ℝ W' (Ep w) (errorField K' (Ep w)) ≠ 0 := by
    intro W' K' hneg
    refine ⟨Fin.append 0 e0, ?_⟩
    rw [Ep_append]
    have : fderiv ℝ W' e0 (errorField K' e0) < 0 := hneg.2 e0 he0
    intro h; linarith
  have hd₀ : 0 ≤ dU + 𝔡₀ := by
    have := h𝔡₀.1; have : (0:ℝ) ≤ n := n.cast_nonneg; linarith
  have hdi : 0 ≤ dU + 𝔡inf := by
    have := h𝔡inf.1; have : (0:ℝ) ≤ n := n.cast_nonneg; linarith
  have hρ₀ := append_pos (wpos hn h𝔡₀)
  have hρi := append_pos (wpos hn h𝔡inf)
  have hη := And.intro
    (hηZ.toHomog hρ₀ hd₀ (cη V hVc φ hφ.1.2.2.1 Kp hKc.1) (cη V₀ hV₀c φ₀ hφ.1.2.2.2.1 Kp₀ hKc.2)
      (hne_eta V₀ φ₀ Kp₀ hK₀0 hV₀neg))
    (hηI.toHomog hρi hdi (cη V hVc φ hφ.1.2.2.1 Kp hKc.1) (cη Vi hVic φinf hφ.2.2.2.2.1 Kpinf hKic.2)
      (hne_eta Vi φinf Kpinf hKi0 hVineg))
  have hγ := And.intro
    (hγZ.toHomog hρ₀ hd₀ (cγ W hWc Kp hKc.1) (cγ W₀ hW₀c Kp₀ hKc.2) (hne_gamma W₀ Kp₀ hW₀neg))
    (hγI.toHomog hρi hdi (cγ W hWc Kp hKc.1) (cγ Wi hWic Kpinf hKic.2) (hne_gamma Wi Kpinf hWineg))
  obtain ⟨cs, hcs⟩ := lemma_2_13 _ _ _ _ _ _ _ _ _ _ hη hγ (gamma_nonneg hWneg)
    (hyp_aux hK0 hVneg hWneg) (hyp_aux hK₀0 hV₀neg hW₀neg) (hyp_aux hKi0 hVineg hWineg)
  set c := max cs 1
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine closed_gas hn0 hφ.1.2.2.1 hKc.1 hφ0 hK0 hVc hWc hVnn hWnn hVpd hWpd hVpr hWpr hc ?_
    (fun f hf hf0 U hU hpd hpr hneg => lyapunov_sufficient_gas f hf hf0 U hU hpd hpr hneg) hL
  intro a e hae
  have hw : Fin.append a e ≠ 0 := by
    intro h
    rcases hae with ha | he
    · apply ha; rw [← Xp_append a e, h]; rfl
    · apply he; rw [← Ep_append a e, h]; rfl
  have := (hcs c (le_max_left _ _) _ hw).1
  simp only [Xp_append, Ep_append] at this
  linarith

end mainsec

end HBLRed

open HBLRed in
theorem solution (n : ℕ) (hn : 2 ≤ n) (𝔡₀ 𝔡inf : ℝ)
    (h𝔡₀ : HomogBiLimit.OutputFeedback.AdmissibleDegree n 𝔡₀)
    (h𝔡inf : HomogBiLimit.OutputFeedback.AdmissibleDegree n 𝔡inf) :
    ∃ (φ φ₀ φinf : (Fin n → ℝ) → ℝ) (K K₀ Kinf : (Fin n → ℝ) → (Fin n → ℝ)),
      HomogBiLimit.OutputFeedback.IsHomogBiLimit φ (HomogBiLimit.OutputFeedback.weights n 𝔡₀ 0 n)
        (1 + 𝔡₀) φ₀ (HomogBiLimit.OutputFeedback.weights n 𝔡inf 0 n) (1 + 𝔡inf) φinf ∧
      HomogBiLimit.OutputFeedback.IsHomogBiLimitVF K (HomogBiLimit.OutputFeedback.weights n 𝔡₀ 0 n)
        𝔡₀ K₀ (HomogBiLimit.OutputFeedback.weights n 𝔡inf 0 n) 𝔡inf Kinf ∧
      ∀ L : ℝ, 0 < L →
        HomogBiLimit.OutputFeedback.IsGAS (HomogBiLimit.OutputFeedback.closedLoop n φ K L) ∧
        HomogBiLimit.OutputFeedback.IsGAS (HomogBiLimit.OutputFeedback.closedLoop n φ₀ K₀ L) ∧
          HomogBiLimit.OutputFeedback.IsGAS (HomogBiLimit.OutputFeedback.closedLoop n φinf Kinf L) := by
  obtain ⟨φ, φ₀, φinf, hφ, hg1, hg2, hg3⟩ := display_4_9 n hn 𝔡₀ 𝔡inf h𝔡₀ h𝔡inf
  obtain ⟨Kp, Kp₀, Kpinf, hK, he1, he2, he3⟩ := display_3_12 n hn 𝔡₀ 𝔡inf h𝔡₀ h𝔡inf
  have hφ' : IsHomogBiLimit φ (weights n 𝔡₀ 0 n) (1 + 𝔡₀) φ₀ (weights n 𝔡inf 0 n) (1 + 𝔡inf)
      φinf := by
    rw [add_comm 1 𝔡₀, add_comm 1 𝔡inf]; exact hφ
  have hn0 : 0 < n := by omega
  have hd₀ : 0 < 1 + 𝔡₀ := by linarith [h𝔡₀.1]
  have hdi : 0 < 1 + 𝔡inf := by linarith [h𝔡inf.1]
  refine ⟨φ, φ₀, φinf, fun y => Kp (-y), fun y => Kp₀ (-y), fun y => Kpinf (-y), hφ', negVF hK,
    fun L hL => ⟨main_gen hn h𝔡₀ h𝔡inf hφ' hK ⟨hg1, hg2, hg3⟩ ⟨he1, he2, he3⟩ hL,
      main_gen hn h𝔡₀ h𝔡₀ (self_of_zero hn0 hφ'.1 hd₀)
        (selfVF_of_zero hn0 hK.1 (wdpos hn h𝔡₀)) ⟨hg2, hg2, hg2⟩ ⟨he2, he2, he2⟩ hL,
      main_gen hn h𝔡inf h𝔡inf (self_of_infty hn0 hφ'.2 hdi)
        (selfVF_of_infty hn0 hK.2 (wdpos hn h𝔡inf)) ⟨hg3, hg3, hg3⟩ ⟨he3, he3, he3⟩ hL⟩⟩

