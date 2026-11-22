-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiLatticeGeneratorSemigroupUnique
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T10:27:59.845813+00:00
-- url     : https://prove2.me/submissions/b8eb0eb3-4b74-4595-bdfb-05026c63108b

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false


namespace GenUniq

lemma pmf_hasSum (p : PMF ℕ) : HasSum (fun n => (p n).toReal) 1 := by
  have h := p.tsum_coe
  have hs : Summable (fun n => (p n).toReal) :=
    ENNReal.summable_toReal (by rw [h]; exact ENNReal.one_ne_top)
  have : ∑' n, (p n).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun n => p.apply_ne_top n), h]; simp
  exact this ▸ hs.hasSum

lemma pmf_le_one (p : PMF ℕ) (n : ℕ) : (p n).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one n)

lemma bind_toReal (p : PMF ℕ) (q : ℕ → PMF ℕ) (k : ℕ) :
    ((p.bind q) k).toReal = ∑' n, (p n).toReal * (q n k).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · simp [ENNReal.toReal_mul]
  · intro n; exact ENNReal.mul_ne_top (p.apply_ne_top n) ((q n).apply_ne_top k)

noncomputable def gen (rate : ℝ≥0) (offspring : PMF ℕ) (z k : ℕ) : ℝ :=
  if k = z then (if z = 0 then 0 else -(rate : ℝ))
  else if 1 ≤ z ∧ z ≤ k + 1 then (rate : ℝ) * (offspring (k + 1 - z)).toReal else 0

noncomputable def shift (offspring : PMF ℕ) (z k : ℕ) : ℝ :=
  if z ≤ k + 1 then (offspring (k + 1 - z)).toReal else 0

lemma shift_hasSum (offspring : PMF ℕ) (z : ℕ) (hz : 1 ≤ z) :
    HasSum (shift offspring z) 1 := by
  have hinj : Function.Injective (fun j : ℕ => j + (z - 1)) := fun a b h => by simpa using h
  rw [← hinj.hasSum_iff]
  · have : (shift offspring z ∘ fun j : ℕ => j + (z - 1)) = fun j => (offspring j).toReal := by
      funext j
      simp only [Function.comp, shift]
      rw [if_pos (by omega)]
      congr 2; omega
    rw [this]; exact pmf_hasSum offspring
  · intro x hx
    simp only [Set.mem_range, not_exists] at hx
    simp only [shift]
    rw [if_neg]
    intro h
    exact hx (x - (z - 1)) (by omega)

lemma gen_eq (rate : ℝ≥0) (offspring : PMF ℕ) (h1 : offspring 1 = 0) (z : ℕ) (hz : 1 ≤ z) :
    gen rate offspring z = fun k =>
      (rate : ℝ) * shift offspring z k - (rate : ℝ) * (if k = z then 1 else 0) := by
  funext k
  simp only [gen, shift]
  by_cases hk : k = z
  · subst hk
    have : k + 1 - k = 1 := by omega
    simp [this, h1, show k ≠ 0 by omega]
  · by_cases h2 : z ≤ k + 1
    · simp [hk, h2, hz]
    · simp [hk, h2]

lemma gen_zero (rate : ℝ≥0) (offspring : PMF ℕ) (k : ℕ) : gen rate offspring 0 k = 0 := by
  simp [gen]

lemma gen_hasSum (rate : ℝ≥0) (offspring : PMF ℕ) (h1 : offspring 1 = 0) (z : ℕ) :
    HasSum (gen rate offspring z) 0 := by
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz
    rw [show gen rate offspring 0 = fun _ => 0 from funext (gen_zero rate offspring)]
    exact hasSum_zero
  · rw [gen_eq rate offspring h1 z hz]
    have := ((shift_hasSum offspring z hz).mul_left (rate : ℝ)).sub
      ((hasSum_ite_eq z (1 : ℝ)).mul_left (rate : ℝ))
    simpa using this

lemma gen_abs_hasSum_le (rate : ℝ≥0) (offspring : PMF ℕ) (h1 : offspring 1 = 0) (z : ℕ) :
    Summable (fun k => |gen rate offspring z k|) ∧
      ∑' k, |gen rate offspring z k| ≤ 2 * rate := by
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz; simp only [gen_zero, abs_zero, tsum_zero]
    exact ⟨summable_zero, by positivity⟩
  · have hB := ((shift_hasSum offspring z hz).mul_left (rate : ℝ)).add
      ((hasSum_ite_eq z (1 : ℝ)).mul_left (rate : ℝ))
    have hle : ∀ k, |gen rate offspring z k| ≤
        (rate : ℝ) * shift offspring z k + (rate : ℝ) * (if k = z then 1 else 0) := by
      intro k
      rw [gen_eq rate offspring h1 z hz]
      have hs : 0 ≤ shift offspring z k := by
        unfold shift; split_ifs <;> simp
      have hr : (0 : ℝ) ≤ rate := rate.2
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (mul_nonneg hr hs), abs_of_nonneg (mul_nonneg hr (by split_ifs <;> simp))]
    have hsum : Summable (fun k => |gen rate offspring z k|) :=
      Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle hB.summable
    refine ⟨hsum, ?_⟩
    calc ∑' k, |gen rate offspring z k| ≤ (rate : ℝ) * 1 + (rate : ℝ) * 1 :=
          hasSum_le hle hsum.hasSum hB
      _ = 2 * rate := by ring

lemma gen_nonneg (rate : ℝ≥0) (offspring : PMF ℕ) (z k : ℕ) (hk : k ≠ z) :
    0 ≤ gen rate offspring z k := by
  simp only [gen, hk, if_false]
  split_ifs
  · exact mul_nonneg rate.2 ENNReal.toReal_nonneg
  · exact le_rfl

lemma scheffe {α : Type*} {l : Filter α} (a : α → ℕ → ℝ) (g : ℕ → ℝ) (z : ℕ)
    (ha : ∀ n, Tendsto (fun h => a h n) l (𝓝 (g n)))
    (hsum : ∀ᶠ h in l, HasSum (a h) 0)
    (hg : HasSum g 0)
    (hnn : ∀ᶠ h in l, ∀ n, n ≠ z → 0 ≤ a h n) :
    Tendsto (fun h => ∑' n, |a h n - g n|) l (𝓝 0) := by
  set e : α → ℕ → ℝ := fun h n => max (g n - a h n) 0 with he_def
  set bound : ℕ → ℝ := fun n => |g n| + (if n = z then 1 else 0) with hb_def
  have hbs : Summable bound := hg.summable.abs.add (hasSum_ite_eq z (1 : ℝ)).summable
  have hz_ev : ∀ᶠ h in l, g z - 1 < a h z := (ha z).eventually (lt_mem_nhds (sub_one_lt (g z)))
  have hdom : ∀ᶠ h in l, ∀ n, ‖e h n‖ ≤ bound n := by
    filter_upwards [hnn, hz_ev] with h h1 h2 n
    have he0 : 0 ≤ e h n := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg he0]
    simp only [he_def, hb_def]
    by_cases hn : n = z
    · subst hn
      simp only [if_true]
      have := abs_nonneg (g n)
      exact max_le (by linarith) (by linarith)
    · simp only [hn, if_false, add_zero]
      have := h1 n hn
      exact max_le (by linarith [le_abs_self (g n)]) (abs_nonneg _)
  have lim : ∀ n, Tendsto (fun h => e h n) l (𝓝 (max (g n - g n) 0)) :=
    fun n => (tendsto_const_nhds.sub (ha n)).max tendsto_const_nhds
  have hDC := tendsto_tsum_of_dominated_convergence hbs lim hdom
  simp only [sub_self, max_self, tsum_zero] at hDC
  have hEq : (fun h => 2 * ∑' n, e h n) =ᶠ[l] (fun h => ∑' n, |a h n - g n|) := by
    filter_upwards [hsum, hdom] with h hs hd
    have hes : Summable (e h) :=
      Summable.of_nonneg_of_le (fun n => le_max_right _ _)
        (fun n => (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hd n)) hbs
    have hpt : (fun n => |a h n - g n|) = fun n => (a h n - g n) + 2 * e h n := by
      funext n
      simp only [he_def]
      rcases le_total (g n) (a h n) with hle | hle
      · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
      · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
    have := (hs.sub hg).add (hes.hasSum.mul_left 2)
    rw [hpt, this.tsum_eq]; ring
  have := hDC.const_mul 2
  rw [mul_zero] at this
  exact this.congr' hEq

section Kernel
variable (K : ℕ → ℝ≥0 → PMF ℕ)

noncomputable def P (z : ℕ) (t : ℝ) (k : ℕ) : ℝ := (K z (Real.toNNReal t) k).toReal

lemma P_nonneg (z : ℕ) (t : ℝ) (k : ℕ) : 0 ≤ P K z t k := ENNReal.toReal_nonneg
lemma P_le_one (z : ℕ) (t : ℝ) (k : ℕ) : P K z t k ≤ 1 := pmf_le_one _ _
lemma P_row (z : ℕ) (t : ℝ) : HasSum (fun n => P K z t n) 1 := pmf_hasSum _

lemma P_zero (hI : ∀ z : ℕ, K z 0 = PMF.pure z) (z k : ℕ) :
    P K z 0 k = if k = z then 1 else 0 := by
  simp only [P, Real.toNNReal_zero, hI, PMF.pure_apply]
  split_ifs <;> simp

lemma P_add (hS : ∀ (y : ℕ) (s t : ℝ≥0), K y (s + t) = (K y s).bind (fun n => K n t))
    (z : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) (k : ℕ) :
    HasSum (fun n => P K z h n * P K n t k) (P K z (h + t) k) := by
  have hs : Summable (fun n => P K z h n * P K n t k) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (P_nonneg K _ _ _) (P_nonneg K _ _ _))
      (fun n => mul_le_of_le_one_right (P_nonneg K _ _ _) (P_le_one K _ _ _)) (P_row K z h).summable
  convert hs.hasSum using 1
  simp only [P]
  rw [Real.toNNReal_add hh ht, hS, bind_toReal]

lemma diff_bound (hS : ∀ (y : ℕ) (s t : ℝ≥0), K y (s + t) = (K y s).bind (fun n => K n t))
    (z : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) (k : ℕ) :
    |P K z (h + t) k - P K z t k| ≤ 1 - P K z h z := by
  have hu : HasSum (fun n => P K z h n * (P K n t k - P K z t k)) (P K z (h + t) k - P K z t k) := by
    have := (P_add K hS z hh ht k).sub ((P_row K z h).mul_right (P K z t k))
    simpa [mul_sub] using this
  have hw : HasSum (fun n => P K z h n - (if n = z then P K z h z else 0)) (1 - P K z h z) :=
    (P_row K z h).sub (hasSum_ite_eq z _)
  have hle : ∀ n, |P K z h n * (P K n t k - P K z t k)| ≤
      P K z h n - (if n = z then P K z h z else 0) := by
    intro n
    by_cases hn : n = z
    · subst hn; simp
    · simp only [hn, if_false, sub_zero]
      rw [abs_mul, abs_of_nonneg (P_nonneg K _ _ _)]
      apply mul_le_of_le_one_right (P_nonneg K _ _ _)
      have := P_nonneg K n t k; have := P_le_one K n t k
      have := P_nonneg K z t k; have := P_le_one K z t k
      rw [abs_le]; constructor <;> linarith
  rw [abs_le]
  constructor
  · have := hasSum_le (fun n => (abs_le.1 (hle n)).1) hw.neg hu
    linarith
  · exact hasSum_le (fun n => (le_abs_self _).trans (hle n)) hu hw

lemma P_max (z : ℕ) (t : ℝ) (k : ℕ) : P K z (max t 0) k = P K z t k := by
  have : Real.toNNReal (max t 0) = Real.toNNReal t := by
    ext; simp [Real.coe_toNNReal']
  simp only [P, this]

lemma P_continuous (hS : ∀ (y : ℕ) (s t : ℝ≥0), K y (s + t) = (K y s).bind (fun n => K n t))
    (hI : ∀ z : ℕ, K z 0 = PMF.pure z) (z k : ℕ)
    (hc : ContinuousWithinAt (fun t => P K z t z) (Ici 0) 0) :
    Continuous (fun s => P K z s k) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 hc ε hε
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y - x < δ → |P K z y k - P K z x k| < ε := by
    intro x y hx hxy hyx
    have h1 := diff_bound K hS z (sub_nonneg.2 hxy) hx k
    rw [sub_add_cancel] at h1
    have h2 := hδ' (x := y - x) (sub_nonneg.2 hxy) (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (sub_nonneg.2 hxy)]; exact hyx)
    rw [P_zero K hI, if_pos rfl, Real.dist_eq] at h2
    have := (abs_lt.1 h2).1
    linarith
  refine ⟨δ, hδ, fun a ha => ?_⟩
  rw [Real.dist_eq, ← P_max K z a k, ← P_max K z b k]
  have hab : |max a 0 - max b 0| < δ :=
    (abs_max_sub_max_le_abs a b 0).trans_lt (by rw [← Real.dist_eq]; exact ha)
  rcases le_total (max b 0) (max a 0) with h | h
  · exact key _ _ (le_max_right _ _) h (lt_of_le_of_lt (le_abs_self _) hab)
  · rw [abs_sub_comm]
    exact key _ _ (le_max_right _ _) h (by rw [abs_sub_comm] at hab; exact lt_of_le_of_lt (le_abs_self _) hab)

lemma P_backward (rate : ℝ≥0) (offspring : PMF ℕ) (h1 : offspring 1 = 0)
    (hS : ∀ (y : ℕ) (s t : ℝ≥0), K y (s + t) = (K y s).bind (fun n => K n t))
    (hI : ∀ z : ℕ, K z 0 = PMF.pure z)
    (hG : ∀ z k : ℕ, HasDerivWithinAt (fun t => P K z t k) (gen rate offspring z k) (Ici 0) 0)
    (z k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => P K z s k) (∑' n, gen rate offspring z n * P K n t k) (Ici t) t := by
  set g := gen rate offspring z with hg_def
  set a : ℝ → ℕ → ℝ := fun h n => (P K z h n - (if n = z then 1 else 0)) / h with ha_def
  have ha : ∀ n, Tendsto (fun h => a h n) (𝓝[>] 0) (𝓝 (g n)) := by
    intro n
    have := hasDerivWithinAt_iff_tendsto_slope.1 (hG z n)
    rw [Ici_sdiff_left] at this
    convert this using 2 with h
    simp [slope_def_field, ha_def, P_zero K hI, eq_comm]
  have hsumAll : ∀ h, HasSum (a h) 0 := by
    intro h
    have := ((P_row K z h).sub (hasSum_ite_eq z (1 : ℝ))).div_const h
    simpa [ha_def] using this
  have hsum : ∀ᶠ h in 𝓝[>] (0 : ℝ), HasSum (a h) 0 := Eventually.of_forall hsumAll
  have hnn : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ n, n ≠ z → 0 ≤ a h n := by
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h) n hn
    simp only [ha_def, hn, if_false, sub_zero]
    exact div_nonneg (P_nonneg K _ _ _) hh.le
  have hsch := scheffe a g z ha hsum (gen_hasSum rate offspring h1 z) hnn
  have hmap : Tendsto (fun s => s - t) (𝓝[>] t) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun s => s - t) (𝓝 t) (𝓝 (t - t)) := (continuous_sub_right t).tendsto t
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
      exact sub_pos.2 hs
  have hsch' := hsch.comp hmap
  obtain ⟨hgs, -⟩ := gen_abs_hasSum_le rate offspring h1 z
  set c : ℕ → ℝ := fun n => P K n t k with hc_def
  have hgc : Summable (fun n => g n * c n) :=
    Summable.of_norm_bounded hgs (fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (by rw [abs_of_nonneg (P_nonneg K _ _ _)]; exact P_le_one K _ _ _))
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsch'
  filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
  set h := s - t with hh_def
  have hpos : 0 < h := sub_pos.2 hs
  have hst : s = h + t := by rw [hh_def]; ring
  have hslope : HasSum (fun n => a h n * c n) (slope (fun s => P K z s k) t s) := by
    have := ((P_add K hS z hpos.le ht k).sub (hasSum_ite_eq z (c z))).div_const h
    rw [← hst] at this
    have hfun : (fun n => a h n * c n) =
        fun i => (P K z h i * P K i t k - if i = z then c z else 0) / h := by
      funext n
      simp only [ha_def, hc_def]
      split_ifs with hn
      · subst hn; ring
      · ring
    rw [hfun, slope_def_field]
    exact this
  have hdiff := hslope.sub hgc.hasSum
  have hag : Summable (fun n => |a h n - g n|) :=
    ((hsumAll h).summable.sub (gen_hasSum rate offspring h1 z).summable).abs
  have hb : ∀ n, |a h n * c n - g n * c n| ≤ |a h n - g n| := by
    intro n
    rw [← sub_mul, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (by rw [abs_of_nonneg (P_nonneg K _ _ _)]; exact P_le_one K _ _ _)
  show ‖_ - ∑' n, g n * c n‖ ≤ ∑' n, |a h n - g n|
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := hasSum_le (fun n => (abs_le.1 (hb n)).1) hag.hasSum.neg hdiff
    linarith
  · exact hasSum_le (fun n => (le_abs_self _).trans (hb n)) hdiff hag.hasSum

end Kernel

lemma gP_summable (rate : ℝ≥0) (offspring : PMF ℕ) (h1 : offspring 1 = 0)
    (K : ℕ → ℝ≥0 → PMF ℕ) (z : ℕ) (x : ℝ) (k : ℕ) :
    Summable (fun n => gen rate offspring z n * P K n x k) :=
  Summable.of_norm_bounded (gen_abs_hasSum_le rate offspring h1 z).1 (fun n => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (by rw [abs_of_nonneg (P_nonneg K _ _ _)]; exact P_le_one K _ _ _))

theorem main (rate : ℝ≥0) (offspring : PMF ℕ) (h1 : offspring 1 = 0)
    (K₁ K₂ : ℕ → ℝ≥0 → PMF ℕ)
    (hS₁ : ∀ (y : ℕ) (s t : ℝ≥0), K₁ y (s + t) = (K₁ y s).bind (fun n => K₁ n t))
    (hS₂ : ∀ (y : ℕ) (s t : ℝ≥0), K₂ y (s + t) = (K₂ y s).bind (fun n => K₂ n t))
    (hI₁ : ∀ z : ℕ, K₁ z 0 = PMF.pure z) (hI₂ : ∀ z : ℕ, K₂ z 0 = PMF.pure z)
    (hG₁ : ∀ z k : ℕ, HasDerivWithinAt (fun t => P K₁ z t k) (gen rate offspring z k) (Ici 0) 0)
    (hG₂ : ∀ z k : ℕ, HasDerivWithinAt (fun t => P K₂ z t k) (gen rate offspring z k) (Ici 0) 0) :
    K₁ = K₂ := by
  set T : ℝ := 1 / (4 * ((rate : ℝ) + 1)) with hT_def
  have hr : (0 : ℝ) ≤ rate := rate.2
  have hTpos : 0 < T := by rw [hT_def]; positivity
  have hrT : 2 * (rate : ℝ) * T ≤ 1 / 2 := by
    rw [hT_def]; rw [div_eq_mul_inv, one_mul, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  -- Step A: equality on [0, T]
  have hA : ∀ k : ℕ, ∀ m : ℕ, ∀ n : ℕ, ∀ s ∈ Icc 0 T,
      |P K₁ n s k - P K₂ n s k| ≤ (1 / 2 : ℝ) ^ m := by
    intro k m
    induction m with
    | zero =>
      intro n s _
      rw [pow_zero, abs_le]
      have := P_nonneg K₁ n s k; have := P_le_one K₁ n s k
      have := P_nonneg K₂ n s k; have := P_le_one K₂ n s k
      constructor <;> linarith
    | succ m ih =>
      intro z s hs
      set c : ℝ := (1 / 2 : ℝ) ^ m with hc_def
      have hc0 : 0 ≤ c := by positivity
      have hcont : ContinuousOn (fun x => P K₁ z x k - P K₂ z x k) (Icc 0 T) :=
        ((P_continuous K₁ hS₁ hI₁ z k (hG₁ z z).continuousWithinAt).sub
          (P_continuous K₂ hS₂ hI₂ z k (hG₂ z z).continuousWithinAt)).continuousOn
      have hder : ∀ x ∈ Ico 0 T, HasDerivWithinAt (fun x => P K₁ z x k - P K₂ z x k)
          (∑' n, gen rate offspring z n * (P K₁ n x k - P K₂ n x k)) (Ici x) x := by
        intro x hx
        have := (P_backward K₁ rate offspring h1 hS₁ hI₁ hG₁ z k hx.1).sub
          (P_backward K₂ rate offspring h1 hS₂ hI₂ hG₂ z k hx.1)
        have heq : ∑' n, gen rate offspring z n * (P K₁ n x k - P K₂ n x k) =
            ∑' n, gen rate offspring z n * P K₁ n x k - ∑' n, gen rate offspring z n * P K₂ n x k := by
          rw [← Summable.tsum_sub (gP_summable rate offspring h1 K₁ z x k)
            (gP_summable rate offspring h1 K₂ z x k)]
          congr 1; funext n; ring
        rw [heq]; exact this
      have hbd : ∀ x ∈ Ico 0 T,
          ‖∑' n, gen rate offspring z n * (P K₁ n x k - P K₂ n x k)‖ ≤ 2 * rate * c := by
        intro x hx
        obtain ⟨hgs, hgle⟩ := gen_abs_hasSum_le rate offspring h1 z
        have hsum1 : HasSum (fun n => gen rate offspring z n * (P K₁ n x k - P K₂ n x k))
            (∑' n, gen rate offspring z n * (P K₁ n x k - P K₂ n x k)) :=
          ((gP_summable rate offspring h1 K₁ z x k).sub
            (gP_summable rate offspring h1 K₂ z x k)).hasSum.congr_fun (fun n => by ring) |>.summable.hasSum
        have hsum2 : HasSum (fun n => |gen rate offspring z n| * c)
            ((∑' n, |gen rate offspring z n|) * c) := hgs.hasSum.mul_right c
        have hpt : ∀ n, |gen rate offspring z n * (P K₁ n x k - P K₂ n x k)| ≤
            |gen rate offspring z n| * c := by
          intro n
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (ih n x ⟨hx.1, hx.2.le⟩) (abs_nonneg _)
        rw [Real.norm_eq_abs, abs_le]
        have hup : (∑' n, |gen rate offspring z n|) * c ≤ 2 * rate * c :=
          mul_le_mul_of_nonneg_right hgle hc0
        constructor
        · have := hasSum_le (fun n => (abs_le.1 (hpt n)).1) hsum2.neg hsum1
          linarith
        · have := hasSum_le (fun n => (le_abs_self _).trans (hpt n)) hsum1 hsum2
          linarith
      have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hder hbd s hs
      rw [P_zero K₁ hI₁, P_zero K₂ hI₂, sub_self, sub_zero, sub_zero, Real.norm_eq_abs] at hmv
      calc |P K₁ z s k - P K₂ z s k| ≤ 2 * rate * c * s := hmv
        _ ≤ 2 * rate * c * T := by
          apply mul_le_mul_of_nonneg_left hs.2; positivity
        _ = (2 * rate * T) * c := by ring
        _ ≤ (1 / 2) * c := mul_le_mul_of_nonneg_right hrT hc0
        _ = (1 / 2 : ℝ) ^ (m + 1) := by rw [hc_def, pow_succ]; ring
  have hA' : ∀ k n : ℕ, ∀ s ∈ Icc 0 T, P K₁ n s k = P K₂ n s k := by
    intro k n s hs
    by_contra hne
    have hpos : 0 < |P K₁ n s k - P K₂ n s k| := abs_pos.2 (sub_ne_zero.2 hne)
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
    exact absurd (hA k m n s hs) (not_le.2 hm)
  set T' : ℝ≥0 := ⟨T, hTpos.le⟩ with hT'_def
  have hB : ∀ t : ℝ≥0, t ≤ T' → ∀ z, K₁ z t = K₂ z t := by
    intro t ht z
    ext k
    have := hA' k z (t : ℝ) ⟨t.2, ht⟩
    simp only [P, Real.toNNReal_coe] at this
    exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 this
  have hC : ∀ m : ℕ, ∀ t : ℝ≥0, t ≤ (m + 1) * T' → ∀ z, K₁ z t = K₂ z t := by
    intro m
    induction m with
    | zero => intro t ht; exact hB t (by simpa using ht)
    | succ m ih =>
      intro t ht z
      by_cases htT : t ≤ T'
      · exact hB t htT z
      · have hle : T' ≤ t := le_of_lt (not_le.1 htT)
        have hsplit : t = (t - T') + T' := (tsub_add_cancel_of_le hle).symm
        have hfun : (fun n => K₁ n T') = (fun n => K₂ n T') := funext (hB T' le_rfl)
        have hih : K₁ z (t - T') = K₂ z (t - T') := ih (t - T') (by
          rw [tsub_le_iff_right]
          calc t ≤ ((m + 1 : ℕ) + 1 : ℝ≥0) * T' := by exact_mod_cast ht
            _ = (m + 1) * T' + T' := by push_cast; ring) z
        rw [hsplit, hS₁, hS₂, hih, hfun]
  funext z t
  have hT'pos : 0 < T' := hTpos
  obtain ⟨m, hm⟩ := exists_nat_ge (t / T')
  refine hC m t ?_ z
  calc t = (t / T') * T' := (div_mul_cancel₀ t hT'pos.ne').symm
    _ ≤ (m : ℝ≥0) * T' := mul_le_mul_of_nonneg_right hm (by positivity)
    _ ≤ (m + 1) * T' := mul_le_mul_of_nonneg_right (by simp) (by positivity)

end GenUniq

theorem solution
    (rate : ℝ≥0) (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (K₁ K₂ : PopulationLaws)
    (hSemi₁ : IsPopulationMarkovSemigroup K₁)
    (hSemi₂ : IsPopulationMarkovSemigroup K₂)
    (hInit₁ : ∀ z : ℕ, K₁ z 0 = PMF.pure z)
    (hInit₂ : ∀ z : ℕ, K₂ z 0 = PMF.pure z)
    (hGen₁ : ∀ z k : ℕ,
        HasDerivWithinAt
          (fun t : ℝ => ((K₁ z (Real.toNNReal t)) k).toReal)
          (if k = z then (if z = 0 then 0 else -(rate : ℝ))
           else if 1 ≤ z ∧ z ≤ k + 1 then
             (rate : ℝ) * (offspring (k + 1 - z)).toReal
           else 0)
          (Set.Ici 0) 0)
    (hGen₂ : ∀ z k : ℕ,
        HasDerivWithinAt
          (fun t : ℝ => ((K₂ z (Real.toNNReal t)) k).toReal)
          (if k = z then (if z = 0 then 0 else -(rate : ℝ))
           else if 1 ≤ z ∧ z ≤ k + 1 then
             (rate : ℝ) * (offspring (k + 1 - z)).toReal
           else 0)
          (Set.Ici 0) 0) :
    K₁ = K₂ :=
  GenUniq.main rate offspring hNoNullJumps K₁ K₂ hSemi₁ hSemi₂ hInit₁ hInit₂ hGen₁ hGen₂
