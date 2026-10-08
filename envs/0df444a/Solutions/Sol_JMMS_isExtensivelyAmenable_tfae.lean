-- Prove2me | solution 1 for JMMS.isExtensivelyAmenable_tfae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T10:54:16.629498+00:00
-- url     : https://prove2.me/submissions/b3ff1bc9-7f95-4485-854c-6b0e6d53c0ed

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_IntervalExchange

section
/-! Finitely additive integration of `[0,1]`-valued functions (copied from
`Solutions/FAmen/HZ/Lib.lean`, Part B1), used for JMMS Lemma 2.2. -/

open scoped ENNReal

namespace JMMS.IETL22


/-- `∑_{k < 2^n} 2^{-n} m {f ≥ (k+1)/2^n}`: the integral of `⌊2^n f⌋ / 2^n`. -/
noncomputable def layerSum {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n

/-- The integral: the supremum of the layer sums. -/
noncomputable def integ {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) : ℝ := ⨆ n, layerSum m f n


namespace PartB1
open scoped ENNReal

open JMMS.IETL22

variable {α : Type*} {m : Set α → ℝ≥0∞}

/-! ### Elementary facts about a finitely additive probability -/

lemma fa_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) {S T : Set α} (h : S ⊆ T) :
    m S ≤ m T := by
  have hd : Disjoint S (T \ S) := Set.disjoint_sdiff_right
  have := hm.2 S (T \ S) hd
  rw [Set.union_sdiff_cancel h] at this
  rw [this]
  exact le_self_add

lemma fa_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (S : Set α) :
    m S ≤ 1 := h1 ▸ fa_mono hm (Set.subset_univ S)

lemma fa_ne_top (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (S : Set α) :
    m S ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (fa_le_one hm h1 S)

lemma fa_union_le (hm : Garrido.IsFinitelyAdditiveMeasure m) (S T : Set α) :
    m (S ∪ T) ≤ m S + m T := by
  have hd : Disjoint S (T \ S) := Set.disjoint_sdiff_right
  have := hm.2 S (T \ S) hd
  rw [Set.union_sdiff_self] at this
  rw [this]
  gcongr
  exact fa_mono hm Set.sdiff_subset

lemma fa_toReal_union (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {S T : Set α} (h : Disjoint S T) :
    (m (S ∪ T)).toReal = (m S).toReal + (m T).toReal := by
  rw [hm.2 S T h, ENNReal.toReal_add (fa_ne_top hm h1 S) (fa_ne_top hm h1 T)]

lemma fa_toReal_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {S T : Set α} (h : S ⊆ T) : (m S).toReal ≤ (m T).toReal :=
  ENNReal.toReal_mono (fa_ne_top hm h1 T) (fa_mono hm h)

lemma fa_toReal_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : (m S).toReal ≤ 1 := by
  have := fa_toReal_mono hm h1 (Set.subset_univ S)
  rwa [h1, ENNReal.toReal_one] at this

/-! ### Bounds on the layer sums -/

lemma layerSum_nonneg (f : α → ℝ) (n : ℕ) : 0 ≤ layerSum m f n := by
  unfold layerSum
  exact Finset.sum_nonneg fun k _ => div_nonneg ENNReal.toReal_nonneg (by positivity)

lemma layerSum_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (f : α → ℝ) (n : ℕ) : layerSum m f n ≤ 1 := by
  unfold layerSum
  calc ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n
      ≤ ∑ _k ∈ Finset.range (2 ^ n), (1 : ℝ) / 2 ^ n := by
        gcongr with k
        exact fa_toReal_le_one hm h1 _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

lemma bddAbove_layerSum (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (f : α → ℝ) : BddAbove (Set.range (layerSum m f)) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact layerSum_le_one hm h1 f n⟩

/-! ### The four easy lemmas -/

theorem integ_indicator (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : integ m (S.indicator 1) = (m S).toReal := by
  have key : ∀ n, layerSum m (S.indicator 1) n = (m S).toReal := by
    intro n
    unfold layerSum
    have hset : ∀ k ∈ Finset.range (2 ^ n),
        {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ S.indicator 1 a} = S := by
      intro k hk
      have hk' : k + 1 ≤ 2 ^ n := Finset.mem_range.1 hk
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / 2 ^ n := by positivity
      have hle : ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast hk'
      push_cast at hpos hle
      ext a
      by_cases ha : a ∈ S
      · simp [ha, hle]
      · simp [ha, hpos]
    rw [Finset.sum_congr rfl fun k hk => by rw [hset k hk], Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  unfold integ
  simp only [key, ciSup_const]

theorem integ_comp_equiv (τ : α ≃ α) (hτ : ∀ S : Set α, m (τ '' S) = m S) (f : α → ℝ) :
    integ m (f ∘ τ) = integ m f := by
  have heq : ∀ c : ℝ, m {a | c ≤ (f ∘ τ) a} = m {a | c ≤ f a} := by
    intro c
    have : {a | c ≤ (f ∘ τ) a} = τ ⁻¹' {a | c ≤ f a} := rfl
    rw [this, ← hτ (τ ⁻¹' {a | c ≤ f a}), Equiv.image_preimage]
  unfold integ layerSum
  simp only [heq]

theorem integ_nonneg_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : 0 ≤ integ m f ∧ integ m f ≤ 1 :=
  ⟨Real.iSup_nonneg fun n => layerSum_nonneg f n,
    Real.iSup_le (fun n => layerSum_le_one hm h1 f n) zero_le_one⟩

/-! ### `ℕ`-valued layer sums: the integral of a finitely-valued function -/

/-- `∑_{k<N} m{φ ≥ k+1}`: the integral of an `ℕ`-valued function `φ ≤ N`. -/
noncomputable def J (m : Set α → ℝ≥0∞) (φ : α → ℕ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (m {a | k + 1 ≤ φ a}).toReal

lemma J_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {φ ψ : α → ℕ} (h : ∀ a, φ a ≤ ψ a) (N : ℕ) : J m φ N ≤ J m ψ N := by
  unfold J
  exact Finset.sum_le_sum fun k _ => fa_toReal_mono hm h1 fun a ha => le_trans ha (h a)

lemma J_extend (hm : Garrido.IsFinitelyAdditiveMeasure m) {φ : α → ℕ} {N : ℕ}
    (h : ∀ a, φ a ≤ N) (N' : ℕ) (hN' : N ≤ N') : J m φ N' = J m φ N := by
  induction N', hN' using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    unfold J at ih ⊢
    rw [Finset.sum_range_succ, ih]
    have : {a | n + 1 ≤ φ a} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact Nat.lt_succ_of_le ((h a).trans hn)
    rw [this, hm.1, ENNReal.toReal_zero, add_zero]

lemma sum_level (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (A : Set α) (φ : α → ℕ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (m {a | a ∈ A ∧ φ a = k}).toReal =
      (m {a | a ∈ A ∧ φ a < N}).toReal := by
  induction N with
  | zero => simp [hm.1]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, ← fa_toReal_union hm h1]
    · congr 2
      ext a
      by_cases ha : a ∈ A <;> (simp [ha]; try omega)
    · rw [Set.disjoint_left]
      rintro a ⟨_, ha⟩ ⟨_, hb⟩
      omega

/-- Adding a `{0,1}`-valued function adds the measure of its support. -/
lemma J_add_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (φ χ : α → ℕ) (N : ℕ) (hχ : ∀ a, χ a ≤ 1) (h : ∀ a, φ a + χ a ≤ N) :
    J m (φ + χ) N = J m φ N + (m {a | 1 ≤ χ a}).toReal := by
  have hterm : ∀ k, (m {a | k + 1 ≤ (φ + χ) a}).toReal =
      (m {a | k + 1 ≤ φ a}).toReal + (m {a | a ∈ {a | 1 ≤ χ a} ∧ φ a = k}).toReal := by
    intro k
    rw [← fa_toReal_union hm h1]
    · congr 2
      ext a
      have := hχ a
      simp only [Pi.add_apply, Set.mem_ofPred_eq, Set.mem_union]
      omega
    · rw [Set.disjoint_left]
      rintro a ha ⟨hb, hc⟩
      simp only [Set.mem_ofPred_eq] at ha hb
      omega
  unfold J
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, sum_level hm h1]
  congr 3
  ext a
  simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
  intro ha
  have := h a
  omega

lemma J_zero (hm : Garrido.IsFinitelyAdditiveMeasure m) (N : ℕ) : J m 0 N = 0 := by
  unfold J
  refine Finset.sum_eq_zero fun k _ => ?_
  have : {a : α | k + 1 ≤ (0 : α → ℕ) a} = ∅ := by
    ext a; simp
  rw [this, hm.1, ENNReal.toReal_zero]

/-- Additivity of `J` (induction on a bound for `ψ`). -/
lemma J_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (N : ℕ) :
    ∀ (M : ℕ) (φ ψ : α → ℕ), (∀ a, ψ a ≤ M) → (∀ a, φ a + ψ a ≤ N) →
      J m (φ + ψ) N = J m φ N + J m ψ N := by
  intro M
  induction M with
  | zero =>
    intro φ ψ hψ _
    have hψ0 : ψ = 0 := funext fun a => Nat.le_zero.1 (hψ a)
    subst hψ0
    rw [add_zero, J_zero hm, add_zero]
  | succ M ih =>
    intro φ ψ hψ h
    have hsplit : ψ = (fun a => min (ψ a) M) + (fun a => ψ a - M) :=
      funext fun a => by simp only [Pi.add_apply]; omega
    have hχ : ∀ a, (fun a => ψ a - M) a ≤ 1 := fun a => by
      have := hψ a; try dsimp only
      omega
    rw [hsplit, ← add_assoc, J_add_le_one hm h1 _ _ N hχ, ih φ _ (fun a => min_le_right _ _),
      J_add_le_one hm h1 _ _ N hχ]
    · ring
    all_goals
      intro a; have := h a; have := hψ a
      try dsimp only [Pi.add_apply]
      omega

/-! ### The layer sums through `J` -/

lemma layerSum_eq (f : α → ℝ) (n : ℕ) :
    layerSum m f n = J m (fun a => ⌊2 ^ n * f a⌋₊) (2 ^ n) / 2 ^ n := by
  unfold layerSum J
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [← Nat.cast_succ, Nat.le_floor_iff' (Nat.succ_ne_zero k), div_le_iff₀ (by positivity),
    mul_comm]

lemma floor_le_pow {f : α → ℝ} (hf1 : ∀ a, f a ≤ 1) (n : ℕ) (a : α) :
    ⌊2 ^ n * f a⌋₊ ≤ 2 ^ n := by
  apply Nat.floor_le_of_le
  push_cast
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith [hf1 a]

lemma layerSum_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : Monotone (layerSum m f) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [layerSum_eq, layerSum_eq]
  set φ : α → ℕ := fun a => ⌊2 ^ n * f a⌋₊ with hφdef
  have hφ : ∀ a, φ a ≤ 2 ^ n := floor_le_pow hf1 n
  have h2 : ∀ a, (φ + φ) a ≤ ⌊2 ^ (n + 1) * f a⌋₊ := by
    intro a
    apply Nat.le_floor
    have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * f a by have := hf a; positivity)
    simp only [Pi.add_apply, hφdef]
    push_cast
    rw [pow_succ]
    linarith
  have key : 2 * J m φ (2 ^ n) ≤ J m (fun a => ⌊2 ^ (n + 1) * f a⌋₊) (2 ^ (n + 1)) := by
    calc 2 * J m φ (2 ^ n) = J m φ (2 ^ (n + 1)) + J m φ (2 ^ (n + 1)) := by
          rw [J_extend hm hφ (2 ^ (n + 1)) (Nat.pow_le_pow_right (by norm_num) (by omega))]
          ring
      _ = J m (φ + φ) (2 ^ (n + 1)) :=
          (J_add hm h1 _ (2 ^ n) φ φ hφ fun a => by have := hφ a; rw [pow_succ]; omega).symm
      _ ≤ _ := J_mono hm h1 h2 _
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_div_iff₀ hp (by positivity)]
  have e : J m φ (2 ^ n) * (2 : ℝ) ^ (n + 1) = 2 * J m φ (2 ^ n) * 2 ^ n := by
    rw [pow_succ]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right key hp.le

/-! ### Additivity -/

theorem integ_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (hfg : ∀ a, f a + g a ≤ 1) :
    integ m (f + g) = integ m f + integ m g := by
  have hfg0 : ∀ a, 0 ≤ (f + g) a := fun a => add_nonneg (hf a) (hg a)
  have hf1 : ∀ a, f a ≤ 1 := fun a => by linarith [hfg a, hg a]
  have hg1 : ∀ a, g a ≤ 1 := fun a => by linarith [hfg a, hf a]
  have hfg1 : ∀ a, (f + g) a ≤ 1 := hfg
  have tf := tendsto_atTop_ciSup (layerSum_mono hm h1 hf hf1) (bddAbove_layerSum hm h1 f)
  have tg := tendsto_atTop_ciSup (layerSum_mono hm h1 hg hg1) (bddAbove_layerSum hm h1 g)
  have tfg := tendsto_atTop_ciSup (layerSum_mono hm h1 hfg0 hfg1) (bddAbove_layerSum hm h1 (f + g))
  have hbound : ∀ n, layerSum m f n + layerSum m g n ≤ layerSum m (f + g) n ∧
      layerSum m (f + g) n ≤ layerSum m f n + layerSum m g n + (1 / 2) ^ n := by
    intro n
    rw [layerSum_eq, layerSum_eq, layerSum_eq]
    set φ : α → ℕ := fun a => ⌊2 ^ n * f a⌋₊ with hφdef
    set ψ : α → ℕ := fun a => ⌊2 ^ n * g a⌋₊ with hψdef
    set χ : α → ℕ := fun a => ⌊2 ^ n * (f + g) a⌋₊ with hχdef
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have hlow : ∀ a, (φ + ψ) a ≤ χ a := by
      intro a
      apply Nat.le_floor
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * f a by have := hf a; positivity)
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * g a by have := hg a; positivity)
      simp only [Pi.add_apply, hφdef, hψdef]
      push_cast
      linarith
    have hup : ∀ a, χ a ≤ (φ + ψ + 1) a := by
      intro a
      have hlt : χ a < φ a + ψ a + 2 := by
        apply (Nat.floor_lt (by have := hfg0 a; positivity)).2
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * f a)
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * g a)
        simp only [Pi.add_apply, hφdef, hψdef]
        push_cast
        linarith
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    have hχ : ∀ a, χ a ≤ 2 ^ n := floor_le_pow hfg1 n
    have hφ : ∀ a, φ a ≤ 2 ^ n := floor_le_pow hf1 n
    have hφψ : ∀ a, φ a + ψ a ≤ 2 ^ n := fun a => le_trans (hlow a) (hχ a)
    have hadd := J_add hm h1 (2 ^ n) (2 ^ n) φ ψ (floor_le_pow hg1 n) hφψ
    have h_lower : J m φ (2 ^ n) + J m ψ (2 ^ n) ≤ J m χ (2 ^ n) :=
      hadd ▸ J_mono hm h1 hlow (2 ^ n)
    have h_upper : J m χ (2 ^ n) ≤ J m φ (2 ^ n) + J m ψ (2 ^ n) + 1 := by
      rw [← J_extend hm hχ (2 ^ n + 1) (by omega)]
      calc J m χ (2 ^ n + 1) ≤ J m (φ + ψ + 1) (2 ^ n + 1) := J_mono hm h1 hup _
        _ = J m (φ + ψ) (2 ^ n + 1) + (m {a | 1 ≤ (1 : α → ℕ) a}).toReal :=
            J_add_le_one hm h1 _ _ _ (fun a => le_refl _)
              (fun a => by have := hφψ a; simp only [Pi.add_apply, Pi.one_apply]; omega)
        _ ≤ J m (φ + ψ) (2 ^ n + 1) + 1 := by gcongr; exact fa_toReal_le_one hm h1 _
        _ = J m φ (2 ^ n) + J m ψ (2 ^ n) + 1 := by
            rw [J_extend hm (N := 2 ^ n) (fun a => by simpa only [Pi.add_apply] using hφψ a)
              (2 ^ n + 1) (by omega), hadd]
    rw [one_div_pow, ← add_div, ← add_div]
    exact ⟨div_le_div_of_nonneg_right h_lower hp.le, div_le_div_of_nonneg_right h_upper hp.le⟩
  have hd : Filter.Tendsto (fun n => layerSum m (f + g) n - (layerSum m f n + layerSum m g n))
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => by linarith [(hbound n).1]) (fun n => by linarith [(hbound n).2])
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have := tendsto_nhds_unique (tfg.sub (tf.add tg)) hd
  unfold integ
  linarith
open Classical in
/-- The integral of `c · 1_T` is at most `c · m T`. -/
theorem integ_const_indicator_le (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (T : Set α) {c : ℝ} (hc : 0 ≤ c) :
    integ m (fun a => if a ∈ T then c else 0) ≤ c * (m T).toReal := by
  unfold integ
  refine ciSup_le fun n => ?_
  unfold layerSum
  set t := (m T).toReal
  set N := ⌊c * 2 ^ n⌋₊
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have ht : 0 ≤ t := ENNReal.toReal_nonneg
  have hterm : ∀ k ∈ Finset.range (2 ^ n),
      (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ (if a ∈ T then c else 0)}).toReal / 2 ^ n ≤
        if k ∈ Finset.range N then t / 2 ^ n else 0 := by
    intro k _
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / 2 ^ n := by positivity
    by_cases hk : k ∈ Finset.range N
    · rw [if_pos hk]
      gcongr
      apply fa_toReal_mono hm h1
      intro a ha
      by_contra haT
      simp only [Set.mem_ofPred_eq, haT, if_false] at ha
      linarith
    · rw [if_neg hk]
      have hempty : {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ (if a ∈ T then c else 0)} = ∅ := by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        have hlt : c < ((k + 1 : ℕ) : ℝ) / 2 ^ n := by
          rw [lt_div_iff₀ hp]
          by_contra hle
          push Not at hle
          apply hk
          rw [Finset.mem_range]
          have : k + 1 ≤ N := Nat.le_floor (by exact_mod_cast hle)
          omega
        split_ifs <;> linarith
      rw [hempty, hm.1, ENNReal.toReal_zero, zero_div]
  calc _ ≤ ∑ k ∈ Finset.range (2 ^ n), (if k ∈ Finset.range N then t / 2 ^ n else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ k ∈ (Finset.range (2 ^ n)).filter (· ∈ Finset.range N), t / 2 ^ n := by
        rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Finset.range N, t / 2 ^ n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk; exact (Finset.mem_filter.1 hk).2
        · intros; positivity
    _ = N * (t / 2 ^ n) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (c * 2 ^ n) * (t / 2 ^ n) := by
        gcongr
        exact Nat.floor_le (by positivity)
    _ = c * t := by field_simp

end PartB1

end JMMS.IETL22
end

section
/-! Means on finite subsets: union-products, powers, pushforwards (for JMMS Lemma 2.2). -/

open scoped ENNReal

namespace JMMS.IETL22

open PartB1 Classical

variable {A B : Type*}

/-- A finitely additive probability on the finite subsets of `A`. -/
def IsMean (μ : Set (Finset A) → ℝ≥0∞) : Prop :=
  Garrido.IsFinitelyAdditiveMeasure μ ∧ μ Set.univ = 1

/-- Invariance of `μ` under the permutation `σ` of `A`. -/
def PInv (μ : Set (Finset A) → ℝ≥0∞) (σ : Equiv.Perm A) : Prop :=
  ∀ S, μ (σ.finsetCongr '' S) = μ S

/-- The weight of the finite sets missing `x`. -/
def bad (μ : Set (Finset A) → ℝ≥0∞) (x : A) : ℝ≥0∞ := μ {E | x ∉ E}

lemma map_eq_finsetCongr (σ : Equiv.Perm A) :
    (fun E : Finset A => E.map σ.toEmbedding) = σ.finsetCongr := by
  funext E; rw [Equiv.finsetCongr_apply]

lemma pinv_iff (μ : Set (Finset A) → ℝ≥0∞) (σ : Equiv.Perm A) :
    PInv μ σ ↔ ∀ S, μ ((fun E : Finset A => E.map σ.toEmbedding) '' S) = μ S := by
  rw [map_eq_finsetCongr]; rfl

lemma IsMean.compl {μ : Set (Finset A) → ℝ≥0∞} (hμ : IsMean μ) (S : Set (Finset A)) :
    μ S + μ Sᶜ = 1 := by
  rw [← hμ.1.2 S Sᶜ disjoint_compl_right, Set.union_compl_self, hμ.2]

lemma IsMean.compl_lt_one {μ : Set (Finset A) → ℝ≥0∞} (hμ : IsMean μ) {S : Set (Finset A)}
    (hS : μ S ≠ 0) : μ Sᶜ < 1 := by
  have h := hμ.compl S
  have hne : μ Sᶜ ≠ ∞ := fa_ne_top hμ.1 hμ.2 _
  refine lt_of_le_of_ne (fa_le_one hμ.1 hμ.2 _) fun h1 => hS ?_
  rw [h1] at h
  have : μ S + 1 = 0 + 1 := by rw [h, zero_add]
  exact (ENNReal.add_left_inj ENNReal.one_ne_top).1 this

/-! ## The union-product -/

/-- `(μ ⋆ ν)(S) = ∫ ν {F | E ∪ F ∈ S} dμ(E)`: the law of `E ∪ F` for independent `E ~ μ`,
`F ~ ν`. -/
noncomputable def star (μ ν : Set (Finset A) → ℝ≥0∞) (S : Set (Finset A)) : ℝ≥0∞ :=
  ENNReal.ofReal (integ μ (fun E => (ν {F | E ∪ F ∈ S}).toReal))

lemma star_isMean {μ ν : Set (Finset A) → ℝ≥0∞} (hμ : IsMean μ) (hν : IsMean ν) :
    IsMean (star μ ν) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : (fun E : Finset A => (ν {F | E ∪ F ∈ (∅ : Set (Finset A))}).toReal) =
        (∅ : Set (Finset A)).indicator 1 := by
      funext E; simp [hν.1.1]
    simp only [star, this, integ_indicator hμ.1 hμ.2, hμ.1.1, ENNReal.toReal_zero,
      ENNReal.ofReal_zero]
  · intro S T hST
    have hfun : (fun E : Finset A => (ν {F | E ∪ F ∈ S ∪ T}).toReal) =
        (fun E => (ν {F | E ∪ F ∈ S}).toReal) + (fun E => (ν {F | E ∪ F ∈ T}).toReal) := by
      funext E
      simp only [Pi.add_apply]
      rw [← fa_toReal_union hν.1 hν.2]
      · rfl
      · exact Set.disjoint_left.2 fun F h1 h2 => Set.disjoint_left.1 hST h1 h2
    have h0 : ∀ (P : Set (Finset A)) E, 0 ≤ (ν {F | E ∪ F ∈ P}).toReal :=
      fun _ _ => ENNReal.toReal_nonneg
    unfold star
    rw [hfun, integ_add hμ.1 hμ.2 (h0 S) (h0 T)]
    · exact ENNReal.ofReal_add (integ_nonneg_le_one hμ.1 hμ.2 (h0 S)
        (fun E => fa_toReal_le_one hν.1 hν.2 _)).1
        (integ_nonneg_le_one hμ.1 hμ.2 (h0 T) (fun E => fa_toReal_le_one hν.1 hν.2 _)).1
    · intro E
      have := congrFun hfun E
      simp only [Pi.add_apply] at this
      rw [← this]
      exact fa_toReal_le_one hν.1 hν.2 _
  · have : (fun E : Finset A => (ν {F | E ∪ F ∈ (Set.univ : Set (Finset A))}).toReal) =
        (Set.univ : Set (Finset A)).indicator 1 := by
      funext E; simp [hν.2]
    simp only [star, this, integ_indicator hμ.1 hμ.2, hμ.2, ENNReal.toReal_one,
      ENNReal.ofReal_one]

lemma star_pinv {μ ν : Set (Finset A) → ℝ≥0∞} (σ : Equiv.Perm A) (hμ : PInv μ σ)
    (hν : PInv ν σ) : PInv (star μ ν) σ := by
  intro S
  set e := σ.finsetCongr
  have hfun : (fun E : Finset A => (ν {F | E ∪ F ∈ e '' S}).toReal) =
      (fun E : Finset A => (ν {F | E ∪ F ∈ S}).toReal) ∘ e.symm := by
    funext E
    simp only [Function.comp_apply]
    have hset : {F | E ∪ F ∈ e '' S} = e '' {F | e.symm E ∪ F ∈ S} := by
      ext F
      simp only [Set.mem_ofPred_eq, Set.mem_image_equiv]
      have : e.symm (E ∪ F) = e.symm E ∪ e.symm F := by
        simp only [e, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_union]
      rw [this]
    rw [hset, hν]
  unfold star
  rw [hfun, integ_comp_equiv e.symm]
  intro P
  have := hμ (e.symm '' P)
  rw [Equiv.image_symm_image] at this
  exact this.symm

lemma star_bad {μ ν : Set (Finset A) → ℝ≥0∞} (hμ : IsMean μ) (hν : IsMean ν) (x : A) :
    bad (star μ ν) x ≤ bad μ x * bad ν x := by
  have hfun : (fun E : Finset A => (ν {F | E ∪ F ∈ {E : Finset A | x ∉ E}}).toReal) =
      fun E => if E ∈ {E : Finset A | x ∉ E} then (bad ν x).toReal else 0 := by
    funext E
    by_cases hx : x ∈ E
    · have : {F | E ∪ F ∈ {E : Finset A | x ∉ E}} = ∅ := by
        ext F; simp [hx]
      simp [this, hν.1.1, hx]
    · have : {F | E ∪ F ∈ {E : Finset A | x ∉ E}} = {F | x ∉ F} := by
        ext F; simp [hx]
      simp [this, hx, bad]
  unfold bad star
  rw [hfun]
  calc _ ≤ ENNReal.ofReal ((bad ν x).toReal * (μ {E | x ∉ E}).toReal) :=
        ENNReal.ofReal_le_ofReal (by
          convert integ_const_indicator_le hμ.1 hμ.2 {E : Finset A | x ∉ E}
            (c := (bad ν x).toReal) ENNReal.toReal_nonneg using 3 with E
          split_ifs <;> rfl)
    _ = bad ν x * μ {E | x ∉ E} := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
          (a := bad ν x) (fa_ne_top hν.1 hν.2 _), ENNReal.ofReal_toReal (fa_ne_top hμ.1 hμ.2 _)]
    _ = _ := mul_comm _ _

/-! ## Powers and amplification -/

/-- `μ^{⋆(n+1)}`. -/
noncomputable def spow (μ : Set (Finset A) → ℝ≥0∞) : ℕ → Set (Finset A) → ℝ≥0∞
  | 0 => μ
  | n + 1 => star μ (spow μ n)

lemma spow_spec {μ : Set (Finset A) → ℝ≥0∞} (hμ : IsMean μ) (n : ℕ) :
    IsMean (spow μ n) ∧ (∀ σ, PInv μ σ → PInv (spow μ n) σ) ∧
      ∀ x, bad (spow μ n) x ≤ bad μ x ^ (n + 1) := by
  induction n with
  | zero => exact ⟨hμ, fun σ h => h, fun x => by simp [spow]⟩
  | succ n ih =>
    refine ⟨star_isMean hμ ih.1, fun σ h => star_pinv σ h (ih.2.1 σ h), fun x => ?_⟩
    calc bad (spow μ (n + 1)) x ≤ bad μ x * bad (spow μ n) x := star_bad hμ ih.1 x
      _ ≤ bad μ x * bad μ x ^ (n + 1) := by gcongr; exact ih.2.2 x
      _ = bad μ x ^ (n + 1 + 1) := by ring

theorem amplify {μ : Set (Finset A) → ℝ≥0∞} (hμ : IsMean μ) (P : Equiv.Perm A → Prop)
    (hP : ∀ σ, P σ → PInv μ σ) (F : Finset A) (hF : ∀ x ∈ F, bad μ x < 1) (k : ℕ) :
    ∃ μ' : Set (Finset A) → ℝ≥0∞, IsMean μ' ∧ (∀ σ, P σ → PInv μ' σ) ∧
      ∀ x ∈ F, bad μ' x ≤ ((k : ℝ≥0∞) + 1)⁻¹ := by
  have hε : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ := by
    rw [ENNReal.inv_pos]; exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, ENNReal.one_ne_top⟩
  have hev : ∀ᶠ n in Filter.atTop, ∀ x ∈ F, bad μ x ^ (n + 1) < ((k : ℝ≥0∞) + 1)⁻¹ := by
    rw [Filter.eventually_all_finset]
    intro x hx
    exact ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (hF x hx)).comp
      (Filter.tendsto_add_atTop_nat 1)).eventually_lt_const hε
  obtain ⟨n, hn⟩ := hev.exists
  have hs := spow_spec hμ n
  exact ⟨spow μ n, hs.1, fun σ h => hs.2.1 σ (hP σ h),
    fun x hx => (hs.2.2 x).trans (hn x hx).le⟩

/-! ## Pushforwards and the Dirac mean at `∅` -/

/-- Pushforward of a mean along a map of finite sets. -/
def push (φ : Finset A → Finset B) (μ : Set (Finset A) → ℝ≥0∞) (T : Set (Finset B)) : ℝ≥0∞ :=
  μ (φ ⁻¹' T)

lemma push_isMean (φ : Finset A → Finset B) {μ : Set (Finset A) → ℝ≥0∞} (hμ : IsMean μ) :
    IsMean (push φ μ) :=
  ⟨⟨by simpa [push] using hμ.1.1, fun S T hST => by
    simpa [push, Set.preimage_union] using hμ.1.2 _ _ (hST.preimage φ)⟩,
    by simpa [push] using hμ.2⟩

lemma push_pinv (φ : Finset A → Finset B) {μ : Set (Finset A) → ℝ≥0∞} (σ : Equiv.Perm A)
    (τ : Equiv.Perm B) (hφ : ∀ E, φ (σ.finsetCongr E) = τ.finsetCongr (φ E)) (hμ : PInv μ σ) :
    PInv (push φ μ) τ := by
  intro T
  unfold push
  have hset : φ ⁻¹' (τ.finsetCongr '' T) = σ.finsetCongr '' (φ ⁻¹' T) := by
    ext E
    simp only [Set.mem_preimage, Set.mem_image_equiv]
    have := hφ (σ.finsetCongr.symm E)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply]
  rw [hset, hμ]

/-- The Dirac mean at the empty set. -/
noncomputable def dirac0 (S : Set (Finset A)) : ℝ≥0∞ := if (∅ : Finset A) ∈ S then 1 else 0

lemma dirac0_isMean : IsMean (dirac0 (A := A)) := by
  refine ⟨⟨by simp [dirac0], fun S T hST => ?_⟩, by simp [dirac0]⟩
  unfold dirac0
  by_cases hS : (∅ : Finset A) ∈ S
  · have hT : (∅ : Finset A) ∉ T := fun h => Set.disjoint_left.1 hST hS h
    simp [hS, hT]
  · by_cases hT : (∅ : Finset A) ∈ T <;> simp [hS, hT]

lemma dirac0_pinv (σ : Equiv.Perm A) : PInv (dirac0 (A := A)) σ := by
  intro S
  unfold dirac0
  have : (∅ : Finset A) ∈ σ.finsetCongr '' S ↔ (∅ : Finset A) ∈ S := by
    rw [Set.mem_image_equiv]
    simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply]
  simp only [this]

end JMMS.IETL22
end

section
/-! # JMMS Lemma 2.2: four forms of extensive amenability

Route: (i) ⇒ (ii) restricts the mean to each orbit; (ii) ⇒ (iii) and (i) ⇒ (iv) are immediate;
(iv) ⇒ (i) and (iii) ⇒ (i) go through `of_approx`: it suffices, for each finite `S ⊆ G`,
finite `F ⊆ X` and `k`, to have an `S`-invariant mean on the finite subsets of `X` giving weight
`≤ 1/(k+1)` to the sets missing any given `x ∈ F` (an ultrafilter limit then gives (i)). Such
means come from union-products (`star`): for (iii) the orbit means of `H = ⟨S⟩` through the
points of `F` are pushed into `X` and multiplied (JMMS's product over orbits), and in both cases
a union-power (Juschenko–Monod Lemma 3.1, (iii) ⇒ (iv)) drives the weight of the sets missing
`x` to zero. -/

open IntervalExchange
open scoped ENNReal

namespace JMMS.IETL22

open PartB1 Classical

/-- The approximation criterion for extensive amenability. -/
theorem of_approx {G X : Type*} [Group G] [MulAction G X]
    (h : ∀ (S : Finset G) (F : Finset X) (k : ℕ), ∃ μ : Set (Finset X) → ℝ≥0∞, IsMean μ ∧
      (∀ g ∈ S, PInv μ (MulAction.toPerm g)) ∧ ∀ x ∈ F, bad μ x ≤ ((k : ℝ≥0∞) + 1)⁻¹) :
    IsExtensivelyAmenable G X := by
  choose μ hμ using h
  let I := Finset G × Finset X × ℕ
  let U : Ultrafilter I := Ultrafilter.of Filter.atTop
  let f : Set (Finset X) → I → ℝ≥0∞ := fun S i => μ i.1 i.2.1 i.2.2 S
  let m : Set (Finset X) → ℝ≥0∞ := fun S => (U.map (f S)).lim
  have hT : ∀ S, Filter.Tendsto (f S) U (nhds (m S)) := fun S => Ultrafilter.le_nhds_lim _
  have hevG : ∀ g : G, ∀ᶠ i in (U : Filter I), g ∈ i.1 := by
    intro g
    apply Ultrafilter.of_le
    rw [Filter.mem_atTop_sets]
    exact ⟨({g}, ∅, 0), fun b hb => hb.1 (Finset.mem_singleton_self g)⟩
  have hevX : ∀ (x : X) (k : ℕ), ∀ᶠ i in (U : Filter I), x ∈ i.2.1 ∧ k ≤ i.2.2 := by
    intro x k
    apply Ultrafilter.of_le
    rw [Filter.mem_atTop_sets]
    exact ⟨(∅, {x}, k), fun b hb => ⟨hb.2.1 (Finset.mem_singleton_self x), hb.2.2⟩⟩
  have huniq : ∀ S (c : ℝ≥0∞), (∀ i, f S i = c) → m S = c := fun S c hc =>
    tendsto_nhds_unique (hT S) (tendsto_const_nhds.congr fun i => (hc i).symm)
  have hm : IsMean m := by
    refine ⟨⟨huniq ∅ 0 fun i => (hμ i.1 i.2.1 i.2.2).1.1.1, fun S T hST => ?_⟩,
      huniq _ 1 fun i => (hμ i.1 i.2.1 i.2.2).1.2⟩
    exact tendsto_nhds_unique (hT (S ∪ T)) (((hT S).add (hT T)).congr
      fun i => ((hμ i.1 i.2.1 i.2.2).1.1.2 S T hST).symm)
  have hzero : ∀ x : X, m {E | x ∉ E} = 0 := by
    intro x
    have hk : ∀ k : ℕ, m {E | x ∉ E} ≤ ((k : ℝ≥0∞) + 1)⁻¹ := fun k =>
      le_of_tendsto (hT _) ((hevX x k).mono fun i hi =>
        ((hμ i.1 i.2.1 i.2.2).2.2 x hi.1).trans (by gcongr; exact_mod_cast hi.2))
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
    have h1 := hk n
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    exact absurd (h1.trans h2) (not_le.2 hn)
  have hcone : ∀ E₀ : Finset X, m {E | E₀ ⊆ E}ᶜ = 0 := by
    intro E₀
    induction E₀ using Finset.induction_on with
    | empty => simp [hm.1.1]
    | insert a s _ ih =>
      apply le_antisymm _ bot_le
      calc m {E | insert a s ⊆ E}ᶜ ≤ m ({E | a ∉ E} ∪ {E | s ⊆ E}ᶜ) := by
            apply fa_mono hm.1
            intro E hE
            simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.insert_subset_iff,
              not_and_or] at hE
            rcases hE with hE | hE
            · exact Or.inl hE
            · exact Or.inr hE
        _ ≤ m {E | a ∉ E} + m {E | s ⊆ E}ᶜ := fa_union_le hm.1 _ _
        _ = 0 := by rw [hzero, ih, add_zero]
  refine ⟨m, hm.1, ?_, hm.2, ?_, ?_⟩
  · have : {E : Finset X | (E : Set X) ⊆ Set.univ} = Set.univ :=
      Set.eq_univ_of_forall fun E => Set.subset_univ _
    rw [this, hm.2]
  · intro g S
    rw [map_eq_finsetCongr]
    exact tendsto_nhds_unique (hT _) ((hT S).congr' ((hevG g).mono fun i hi =>
      ((hμ i.1 i.2.1 i.2.2).2.1 g hi S).symm))
  · intro E₀ _
    have := hm.compl {E | E₀ ⊆ E}
    rwa [hcone, add_zero] at this

end JMMS.IETL22

namespace JMMS

open JMMS.IETL22 JMMS.IETL22.PartB1 Classical

theorem chk_isExtensivelyAmenable_tfae {G X : Type*} [Group G] [MulAction G X] :
    List.TFAE
      [IsExtensivelyAmenable G X,
       ∀ H : Subgroup G, H.FG → ∀ x : X, IsExtensivelyAmenable H (MulAction.orbit H x),
       ∀ H : Subgroup G, H.FG → ∀ x₀ : X,
         ∃ m : Set (Finset (MulAction.orbit H x₀)) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧
           m Set.univ = 1 ∧
           (∀ (h : H) (S : Set (Finset (MulAction.orbit H x₀))),
             m ((fun E => E.map
               (MulAction.toPerm h : Equiv.Perm (MulAction.orbit H x₀)).toEmbedding) '' S) = m S) ∧
           m {E | ⟨x₀, MulAction.mem_orbit_self x₀⟩ ∈ E} ≠ 0,
       ∃ m : Set (Finset X) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
         (∀ (g : G) (S : Set (Finset X)),
           m ((fun E => E.map (MulAction.toPerm g : Equiv.Perm X).toEmbedding) '' S) = m S) ∧
         ∀ x₀ : X, m {E | x₀ ∈ E} ≠ 0] := by
  tfae_have 1 → 2 := by
    rintro ⟨m, hFA, -, h1, hinv, hcone⟩ H _ x
    let Y := MulAction.orbit H x
    let φ : Finset X → Finset Y := fun E => E.subtype (· ∈ Y)
    have hM : IsMean (push φ m) := push_isMean φ ⟨hFA, h1⟩
    refine ⟨push φ m, hM.1, ?_, hM.2, ?_, ?_⟩
    · have : {E : Finset Y | (E : Set Y) ⊆ Set.univ} = Set.univ :=
        Set.eq_univ_of_forall fun E => Set.subset_univ _
      rw [this, hM.2]
    · intro h S
      have hequiv : ∀ E, φ ((MulAction.toPerm (h : G)).finsetCongr E) =
          (MulAction.toPerm h : Equiv.Perm Y).finsetCongr (φ E) := by
        intro E
        ext y
        simp [φ, Equiv.finsetCongr_apply, Finset.mem_map_equiv, MulAction.toPerm_symm_apply]
        exact Iff.rfl
      exact (pinv_iff _ _).1 (push_pinv φ _ _ hequiv ((pinv_iff _ _).2 (hinv (h : G)))) S
    · intro E₀ _
      have hset : φ ⁻¹' {E | E₀ ⊆ E} =
          {E | E₀.map (Function.Embedding.subtype (· ∈ Y)) ⊆ E} := by
        ext E
        simp [φ, Finset.subset_iff]
        exact Iff.rfl
      show m (φ ⁻¹' _) = 1
      rw [hset]
      exact hcone _ (Set.subset_univ _)
  tfae_have 2 → 3 := by
    intro h2 H hH x₀
    obtain ⟨m, hFA, -, h1, hinv, hcone⟩ := h2 H hH x₀
    refine ⟨m, hFA, h1, hinv, ?_⟩
    have := hcone {⟨x₀, MulAction.mem_orbit_self x₀⟩} (Set.subset_univ _)
    simp only [Finset.singleton_subset_iff] at this
    rw [this]
    exact one_ne_zero
  tfae_have 1 → 4 := by
    rintro ⟨m, hFA, -, h1, hinv, hcone⟩
    refine ⟨m, hFA, h1, hinv, fun x₀ => ?_⟩
    have := hcone {x₀} (Set.subset_univ _)
    simp only [Finset.singleton_subset_iff] at this
    rw [this]
    exact one_ne_zero
  tfae_have 4 → 1 := by
    rintro ⟨m, hFA, h1, hinv, hpos⟩
    apply of_approx
    intro S F k
    obtain ⟨μ, hμ, hμinv, hμbad⟩ := amplify ⟨hFA, h1⟩ (fun σ => ∃ g : G, σ = MulAction.toPerm g)
      (by rintro σ ⟨g, rfl⟩; exact (pinv_iff _ _).2 (hinv g)) F
      (fun x _ => IsMean.compl_lt_one ⟨hFA, h1⟩ (hpos x)) k
    exact ⟨μ, hμ, fun g _ => hμinv _ ⟨g, rfl⟩, hμbad⟩
  tfae_have 3 → 1 := by
    intro h3
    apply of_approx
    intro S F k
    let H := Subgroup.closure (S : Set G)
    have hH : H.FG := ⟨S, rfl⟩
    choose mx hmx using h3 H hH
    let φ : ∀ x : X, Finset (MulAction.orbit H x) → Finset X :=
      fun x E => E.map (Function.Embedding.subtype _)
    have hν : ∀ x : X, IsMean (push (φ x) (mx x)) ∧
        (∀ h : H, PInv (push (φ x) (mx x)) (MulAction.toPerm (h : G))) ∧
        bad (push (φ x) (mx x)) x < 1 := by
      intro x
      obtain ⟨hFA, h1, hinv, hpos⟩ := hmx x
      refine ⟨push_isMean _ ⟨hFA, h1⟩, fun h => ?_, ?_⟩
      · refine push_pinv _ (MulAction.toPerm h) _ (fun E => ?_) ((pinv_iff _ _).2 (hinv h))
        simp only [φ, Equiv.finsetCongr_apply, Finset.map_map]
        congr 1
      · have hset : φ x ⁻¹' {E | x ∉ E} = {E | ⟨x, MulAction.mem_orbit_self x⟩ ∈ E}ᶜ := by
          ext E
          simp [φ]
        unfold bad push
        rw [hset]
        exact IsMean.compl_lt_one ⟨hFA, h1⟩ hpos
    have hfold : ∀ F' : Finset X, ∃ μ : Set (Finset X) → ℝ≥0∞, IsMean μ ∧
        (∀ h : H, PInv μ (MulAction.toPerm (h : G))) ∧ ∀ x ∈ F', bad μ x < 1 := by
      intro F'
      induction F' using Finset.induction_on with
      | empty => exact ⟨dirac0, dirac0_isMean, fun h => dirac0_pinv _, by simp⟩
      | insert a s _ ih =>
        obtain ⟨μ, hμ, hμinv, hμbad⟩ := ih
        obtain ⟨hνa, hνinv, hνbad⟩ := hν a
        refine ⟨star (push (φ a) (mx a)) μ, star_isMean hνa hμ,
          fun h => star_pinv _ (hνinv h) (hμinv h), fun y hy => ?_⟩
        refine lt_of_le_of_lt (star_bad hνa hμ y) ?_
        rcases Finset.mem_insert.1 hy with rfl | hy
        · calc _ ≤ bad (push (φ y) (mx y)) y * 1 := by
                gcongr; exact fa_le_one hμ.1 hμ.2 _
            _ < 1 := by rw [mul_one]; exact hνbad
        · calc _ ≤ 1 * bad μ y := by
                gcongr; exact fa_le_one hνa.1 hνa.2 _
            _ < 1 := by rw [one_mul]; exact hμbad y hy
    obtain ⟨μ₀, hμ₀, hμ₀inv, hμ₀bad⟩ := hfold F
    obtain ⟨μ, hμ, hμinv, hμbad⟩ := amplify hμ₀
      (fun σ => ∃ h : H, σ = MulAction.toPerm (h : G))
      (by rintro σ ⟨h, rfl⟩; exact hμ₀inv h) F hμ₀bad k
    exact ⟨μ, hμ, fun g hg => hμinv _ ⟨⟨g, Subgroup.subset_closure hg⟩, rfl⟩, hμbad⟩
  tfae_finish

end JMMS
end

open IntervalExchange
open scoped ENNReal
open JMMS in
theorem solution {G X : Type*} [Group G] [MulAction G X] :
    List.TFAE
      [IsExtensivelyAmenable G X,
       ∀ H : Subgroup G, H.FG → ∀ x : X, IsExtensivelyAmenable H (MulAction.orbit H x),
       ∀ H : Subgroup G, H.FG → ∀ x₀ : X,
         ∃ m : Set (Finset (MulAction.orbit H x₀)) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧
           m Set.univ = 1 ∧
           (∀ (h : H) (S : Set (Finset (MulAction.orbit H x₀))),
             m ((fun E => E.map
               (MulAction.toPerm h : Equiv.Perm (MulAction.orbit H x₀)).toEmbedding) '' S) = m S) ∧
           m {E | ⟨x₀, MulAction.mem_orbit_self x₀⟩ ∈ E} ≠ 0,
       ∃ m : Set (Finset X) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
         (∀ (g : G) (S : Set (Finset X)),
           m ((fun E => E.map (MulAction.toPerm g : Equiv.Perm X).toEmbedding) '' S) = m S) ∧
         ∀ x₀ : X, m {E | x₀ ∈ E} ≠ 0] :=
  JMMS.chk_isExtensivelyAmenable_tfae
