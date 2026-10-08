-- Prove2me | solution 1 for JMMS.isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T10:54:16.453366+00:00
-- url     : https://prove2.me/submissions/72c4c9ad-272c-4714-b847-e18ea05bbedd

import Mathlib
import Definitions.Def_IntervalExchange

section
/-! # JMMS Lemma 2.1 (extensive amenability vs. amenability)

(a) An amenable group acts extensively amenably (copied from `Solutions/FAmen/ChornyiExtensive.lean`).
(b) An extensively amenable action on a nonempty set is amenable: `μ S = ∫ |A ∩ S| / |A| dm(A)`,
with finitely additive integration copied from `Solutions/FAmen/HZ/Lib.lean`. -/

open IntervalExchange
open scoped ENNReal Pointwise

namespace JMMS.IETP21

/-! ## Part B1: integrating `[0,1]`-valued functions against a finitely additive probability -/

/-- `∑_{k < 2^n} 2^{-n} m {f ≥ (k+1)/2^n}`: the integral of `⌊2^n f⌋ / 2^n`. -/
noncomputable def layerSum {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n

/-- The integral: the supremum of the layer sums. -/
noncomputable def integ {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) : ℝ := ⨆ n, layerSum m f n


namespace PartB1
open scoped ENNReal



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

end PartB1

section Chornyi
variable {G X : Type*} [Group G] [MulAction G X]

/-- The action of `g` on finite subsets of `X`, exactly as `IsExtensivelyAmenableOn` writes it. -/
def act (g : G) (E : Finset X) : Finset X := E.map (MulAction.toPerm g).toEmbedding

lemma mem_act {g : G} {E : Finset X} {x : X} : x ∈ act g E ↔ g⁻¹ • x ∈ E := by
  unfold act
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨g⁻¹ • x, h, by simp⟩

lemma act_mul (g h : G) (E : Finset X) : act (g * h) E = act g (act h E) := by
  ext x
  simp only [mem_act, mul_inv_rev, mul_smul]

lemma act_one (E : Finset X) : act (1 : G) E = E := by
  ext x
  simp only [mem_act, inv_one, one_smul]

/-- An ultrafilter on the finite subsets of `X` concentrated on the finite subsets of `Y` and
containing every cone over a finite subset of `Y`. -/
lemma exists_ultrafilter (Y : Set X) : ∃ U : Ultrafilter (Finset X),
    {E : Finset X | (E : Set X) ⊆ Y} ∈ U ∧
      ∀ E₀ : Finset X, (E₀ : Set X) ⊆ Y → {E : Finset X | E₀ ⊆ E} ∈ U := by
  classical
  let f : Finset Y → Finset X := fun s => s.map (Function.Embedding.subtype (· ∈ Y))
  let V : Ultrafilter (Finset Y) := Ultrafilter.of Filter.atTop
  refine ⟨V.map f, ?_, ?_⟩
  · rw [Ultrafilter.mem_map]
    have : f ⁻¹' {E : Finset X | (E : Set X) ⊆ Y} = Set.univ := by
      ext s
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true, f]
      intro x hx
      rw [Finset.mem_coe, Finset.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2
    rw [this]
    exact Filter.univ_mem
  · intro E₀ hE₀
    rw [Ultrafilter.mem_map]
    apply Ultrafilter.of_le (Filter.atTop : Filter (Finset Y))
    rw [Filter.mem_atTop_sets]
    refine ⟨E₀.subtype (· ∈ Y), fun s hs => ?_⟩
    show E₀ ⊆ f s
    intro x hx
    have hxs : (⟨x, hE₀ hx⟩ : Y) ∈ s := hs (Finset.mem_subtype.2 hx)
    exact Finset.mem_map.2 ⟨_, hxs, rfl⟩

/-- The set of `g` such that `g • E ∈ S` for `U`-almost every finite set `E`. -/
def sat (U : Ultrafilter (Finset X)) (S : Set (Finset X)) : Set G :=
  {g | act g ⁻¹' S ∈ U}

lemma sat_empty (U : Ultrafilter (Finset X)) : sat (G := G) U ∅ = ∅ := by
  ext g
  simp only [sat, Set.preimage_empty, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact U.empty_notMem

lemma sat_univ (U : Ultrafilter (Finset X)) : sat (G := G) U Set.univ = Set.univ := by
  ext g
  simp only [sat, Set.preimage_univ, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact Filter.univ_mem

lemma sat_union (U : Ultrafilter (Finset X)) (S T : Set (Finset X)) :
    sat (G := G) U (S ∪ T) = sat U S ∪ sat U T := by
  ext g
  simp only [sat, Set.preimage_union, Set.mem_ofPred_eq, Set.mem_union]
  exact Ultrafilter.union_mem_iff

lemma sat_disjoint (U : Ultrafilter (Finset X)) {S T : Set (Finset X)} (hST : Disjoint S T) :
    Disjoint (sat (G := G) U S) (sat U T) := by
  refine Set.disjoint_left.2 fun g hS hT => ?_
  have h := Filter.inter_mem hS hT
  rw [← Set.preimage_inter, hST.inter_eq, Set.preimage_empty] at h
  exact U.empty_notMem h

lemma sat_image (U : Ultrafilter (Finset X)) (h : G) (S : Set (Finset X)) :
    sat (G := G) U (act h '' S) = h • sat (G := G) U S := by
  ext k
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have : act k ⁻¹' (act h '' S) = act (h⁻¹ * k) ⁻¹' S := by
    ext E
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨F, hF, hFE⟩
      have : F = act (h⁻¹ * k) E := by
        rw [act_mul, ← hFE, ← act_mul, inv_mul_cancel, act_one]
      rwa [← this]
    · intro hE
      refine ⟨act (h⁻¹ * k) E, hE, ?_⟩
      rw [← act_mul, mul_inv_cancel_left]
  simp only [sat, Set.mem_ofPred_eq, this]

/-- **Amenable groups act extensively amenably** on every invariant subset. -/
theorem isExtensivelyAmenableOn_of_isAmenable (Y : Set X)
    (hY : ∀ (g : G) (x : X), x ∈ Y → g • x ∈ Y) (hG : Garrido.IsAmenable G) :
    ThompsonAmenability.IsExtensivelyAmenableOn G X Y := by
  obtain ⟨ν, ⟨hν0, hνadd⟩, hν1, hνinv⟩ := hG
  obtain ⟨U, hUY, hUcone⟩ := exists_ultrafilter Y
  refine ⟨fun S => ν (sat U S), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [sat_empty, hν0]
  · intro S T hST
    simp only [sat_union, hνadd _ _ (sat_disjoint U hST)]
  · have : sat (G := G) U {E : Finset X | (E : Set X) ⊆ Y} = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ?_
      refine Filter.mem_of_superset hUY fun E hE => ?_
      intro x hx
      have := hY g _ (hE (mem_act.1 hx))
      simpa using this
    simp only [this, hν1]
  · simp only [sat_univ, hν1]
  · intro g S
    exact (congrArg ν (sat_image U g S)).trans (hνinv g _)
  · intro E₀ hE₀
    have : sat (G := G) U {E : Finset X | E₀ ⊆ E} = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ?_
      have hsub : ((act g⁻¹ E₀ : Finset X) : Set X) ⊆ Y := by
        intro y hy
        have := hY g⁻¹ _ (hE₀ (mem_act.1 hy))
        simpa using this
      refine Filter.mem_of_superset (hUcone _ hsub) fun E hE => ?_
      intro x hx
      apply mem_act.2
      apply hE
      apply mem_act.2
      simpa using hx
    simp only [this, hν1]

end Chornyi

section PartB
open Classical
variable {G X : Type*} [Group G] [MulAction G X]

/-- The proportion of the finite set `A` lying in `S` (zero for `A = ∅`). -/
noncomputable def frac (S : Set X) (A : Finset X) : ℝ :=
  ((A.filter (· ∈ S)).card : ℝ) / A.card

lemma frac_nonneg (S : Set X) (A : Finset X) : 0 ≤ frac S A := by
  unfold frac; positivity

lemma frac_union {S T : Set X} (h : Disjoint S T) (A : Finset X) :
    frac (S ∪ T) A = frac S A + frac T A := by
  unfold frac
  rw [← add_div]
  congr 1
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint]
  · congr 2
    ext x
    simp [Finset.mem_filter, Set.mem_union, and_or_left]
  · rw [Finset.disjoint_filter]
    intro x _ hS hT
    exact Set.disjoint_left.1 h hS hT

lemma frac_le_one (S : Set X) (A : Finset X) : frac S A ≤ 1 := by
  unfold frac
  rcases Nat.eq_zero_or_pos A.card with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_filter_le _ _

lemma frac_univ (A : Finset X) :
    frac (Set.univ : Set X) A = ({A : Finset X | A.Nonempty} : Set (Finset X)).indicator 1 A := by
  unfold frac
  by_cases hA : A.Nonempty
  · have : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
    simp [hA, this]
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    subst hA
    simp

lemma frac_smul (g : G) (S : Set X) (A : Finset X) :
    frac (g • S) (act g A) = frac S A := by
  unfold frac act
  rw [Finset.card_map, Finset.filter_map, Finset.card_map]
  congr 4
  ext x
  simp [Set.smul_mem_smul_set_iff]

theorem isAmenableAction_of_isExtensivelyAmenable (hX : Nonempty X)
    (h : IsExtensivelyAmenable G X) : IsAmenableAction G X := by
  obtain ⟨m, hm, -, h1, hinv, hcone⟩ := h
  obtain ⟨x₀⟩ := hX
  refine ⟨fun S => ENNReal.ofReal (integ m (frac S)), ⟨?_, ?_⟩, ?_, ?_⟩
  · have : frac (∅ : Set X) = (∅ : Set (Finset X)).indicator 1 := by
      funext A; simp [frac]
    simp only [this, PartB1.integ_indicator hm h1, hm.1, ENNReal.toReal_zero, ENNReal.ofReal_zero]
  · intro S T hST
    dsimp only
    have : frac (S ∪ T) = frac S + frac T := funext (frac_union hST)
    rw [this, PartB1.integ_add hm h1 (frac_nonneg S) (frac_nonneg T)
      (fun A => by rw [← frac_union hST]; exact frac_le_one _ _),
      ENNReal.ofReal_add (PartB1.integ_nonneg_le_one hm h1 (frac_nonneg S) (frac_le_one S)).1
        (PartB1.integ_nonneg_le_one hm h1 (frac_nonneg T) (frac_le_one T)).1]
  · have : frac (Set.univ : Set X) = ({A : Finset X | A.Nonempty} : Set (Finset X)).indicator 1 :=
      funext frac_univ
    dsimp only
    rw [this, PartB1.integ_indicator hm h1]
    have hne : m {A : Finset X | A.Nonempty} = 1 := by
      refine le_antisymm (PartB1.fa_le_one hm h1 _) ?_
      rw [← hcone {x₀} (Set.subset_univ _)]
      exact PartB1.fa_mono hm fun A hA => ⟨x₀, hA (Finset.mem_singleton_self _)⟩
    rw [hne]
    simp
  · intro g S
    let τ : Finset X ≃ Finset X :=
      ⟨act g, act g⁻¹, fun E => by rw [← act_mul, inv_mul_cancel, act_one],
        fun E => by rw [← act_mul, mul_inv_cancel, act_one]⟩
    have hτ : ∀ T : Set (Finset X), m (τ '' T) = m T := fun T => hinv g T
    have hc : frac (g • S) ∘ τ = frac S := funext fun A => frac_smul g S A
    show ENNReal.ofReal (integ m (frac (g • S))) = ENNReal.ofReal (integ m (frac S))
    rw [← hc, PartB1.integ_comp_equiv τ hτ]

end PartB

end JMMS.IETP21

namespace JMMS

theorem chk_isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
    {G X : Type*} [Group G] [MulAction G X] :
    (Garrido.IsAmenable G → IsExtensivelyAmenable G X) ∧
      (Nonempty X → IsExtensivelyAmenable G X → IsAmenableAction G X) :=
  ⟨fun hG => IETP21.isExtensivelyAmenableOn_of_isAmenable Set.univ (fun _ _ _ => Set.mem_univ _) hG,
    IETP21.isAmenableAction_of_isExtensivelyAmenable⟩

end JMMS
end

open IntervalExchange
open scoped ENNReal
open JMMS in
theorem solution
    {G X : Type*} [Group G] [MulAction G X] :
    (Garrido.IsAmenable G → IsExtensivelyAmenable G X) ∧
      (Nonempty X → IsExtensivelyAmenable G X → IsAmenableAction G X) :=
  JMMS.chk_isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
