-- Prove2me | solution 1 for JMMS.isAmenableAction_and_isExtensivelyAmenable_functorProduct_and_isExtensivelyAmenable_of_isTight
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T12:37:35.046976+00:00
-- url     : https://prove2.me/submissions/974c7f79-6f79-4c2a-93a1-cf12b91aaa0c

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
import Theorems.Thm_JMMS_isExtensivelyAmenable_tfae

section

/-!
# JMMS Theorem 1.3, forward half (Proposition 3.7 / Theorem 3.14, pp. 10–13)

If `G ↷ X` is extensively amenable and `F : I → Amen`, then `F(X) ⋊ G ↷ F(X)` is extensively
amenable, hence (Lemma 2.1, the milestone
`JMMS.isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable`) amenable.

Route. For a finite `A ⊆ X` let `K_A ≤ F(X)` be the image of `F(A) → F(X)`; it is amenable, so
(Lemma 2.1 (a)) it carries a `K_A`-invariant mean `ν` on finite subsets of `K_A ⊆ F(X)` giving full
weight to the supersets of any finite subset of `K_A`. Averaging `ν` over the finitely many
restrictions to `A` of the elements of `G` stabilising `A` (the role of `Sym([n])` in the paper's
proof of Theorem 3.14) and transporting along a chosen representative of each `G`-orbit of finite
subsets gives a `G`-equivariant family `A ↦ ν_A`. Integrating `ν_A` against the extensively
amenable mean `m` on finite subsets of `X` gives the required `F(X) ⋊ G`-invariant mean on finite
subsets of `F(X)`: `G`-invariance from `m`'s invariance, `F(X)`-invariance and the full-weight
property because `m` gives full weight to the finite sets containing any given one.
Finitely additive integration is copied from `Solutions/IET/Lemma21.lean`.
-/

open IntervalExchange CategoryTheory
open scoped ENNReal Pointwise

namespace JMMS.IETP13F

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

theorem integ_congr (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (h : m {a | f a ≠ g a} = 0) : integ m f = integ m g := by
  have hle : ∀ (f g : α → ℝ), m {a | f a ≠ g a} = 0 → ∀ c : ℝ,
      m {a | c ≤ f a} ≤ m {a | c ≤ g a} := by
    intro f g h c
    calc m {a | c ≤ f a} ≤ m ({a | c ≤ g a} ∪ {a | f a ≠ g a}) := by
          apply fa_mono hm
          intro a ha
          by_cases hfg : f a = g a
          · left; simp only [Set.mem_ofPred_eq] at ha ⊢; rwa [← hfg]
          · right; exact hfg
      _ ≤ m {a | c ≤ g a} + m {a | f a ≠ g a} := fa_union_le hm _ _
      _ = m {a | c ≤ g a} := by rw [h, add_zero]
  have h' : m {a | g a ≠ f a} = 0 := by
    simpa only [ne_comm] using h
  have heq : ∀ c : ℝ, m {a | c ≤ f a} = m {a | c ≤ g a} := fun c =>
    le_antisymm (hle f g h c) (hle g f h' c)
  unfold integ layerSum
  simp only [heq]

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

open PartB1

/-! ## Finite subsets and pushforward of set functions -/

section Generic

variable {P Y : Type*} [Group P] [MulAction P Y]

/-- The action of `p` on finite subsets, exactly as `IsExtensivelyAmenableOn` writes it. -/
def act (p : P) (E : Finset Y) : Finset Y := E.map (MulAction.toPerm p).toEmbedding

lemma mem_act {p : P} {E : Finset Y} {y : Y} : y ∈ act p E ↔ p⁻¹ • y ∈ E := by
  unfold act
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨p⁻¹ • y, h, by simp⟩

lemma act_mul (p q : P) (E : Finset Y) : act (p * q) E = act p (act q E) := by
  ext y
  simp only [mem_act, mul_inv_rev, mul_smul]

lemma act_one (E : Finset Y) : act (1 : P) E = E := by
  ext y
  simp only [mem_act, inv_one, one_smul]

lemma image_act (p : P) (S : Set (Finset Y)) : act p '' S = act p⁻¹ ⁻¹' S := by
  ext E
  constructor
  · rintro ⟨E', h, rfl⟩
    show act p⁻¹ (act p E') ∈ S
    rwa [← act_mul, inv_mul_cancel, act_one]
  · intro h
    refine ⟨act p⁻¹ E, h, ?_⟩
    rw [← act_mul, mul_inv_cancel, act_one]

/-- Pushforward of a set function on finite subsets along the action. -/
def pf (p : P) (ν : Set (Finset Y) → ℝ≥0∞) : Set (Finset Y) → ℝ≥0∞ :=
  fun S => ν (act p ⁻¹' S)

lemma pf_mul (p q : P) (ν : Set (Finset Y) → ℝ≥0∞) : pf (p * q) ν = pf p (pf q ν) := by
  funext S
  show ν _ = ν _
  congr 1
  ext E
  simp [act_mul]

lemma pf_fa (p : P) {ν : Set (Finset Y) → ℝ≥0∞} (h : Garrido.IsFinitelyAdditiveMeasure ν) :
    Garrido.IsFinitelyAdditiveMeasure (pf p ν) := by
  refine ⟨by simpa [pf] using h.1, fun S T hST => ?_⟩
  show ν _ = ν _ + ν _
  rw [Set.preimage_union]
  exact h.2 _ _ (hST.preimage _)

end Generic

section Measure

variable {α : Type*} {ν : Set α → ℝ≥0∞}

lemma compl_zero (hν : Garrido.IsFinitelyAdditiveMeasure ν) (h1 : ν Set.univ = 1)
    {T : Set α} (hT : ν T = 1) : ν Tᶜ = 0 := by
  have h := hν.2 T Tᶜ disjoint_compl_right
  rw [Set.union_compl_self, h1, hT] at h
  have h' : (1 : ℝ≥0∞) + ν Tᶜ = 1 + 0 := by rw [← h, add_zero]
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h'

lemma eq_inter (hν : Garrido.IsFinitelyAdditiveMeasure ν) (h1 : ν Set.univ = 1)
    {T : Set α} (hT : ν T = 1) (S : Set α) : ν S = ν (S ∩ T) := by
  have h := hν.2 (S ∩ T) (S \ T) Set.disjoint_sdiff_inter.symm
  rw [Set.inter_union_sdiff] at h
  rw [h]
  have : ν (S \ T) = 0 := le_antisymm
    (le_trans (fa_mono hν (fun x hx => hx.2)) (compl_zero hν h1 hT).le) bot_le
  rw [this, add_zero]

lemma eq_one_of_sub (hν : Garrido.IsFinitelyAdditiveMeasure ν) (h1 : ν Set.univ = 1)
    {T T' : Set α} (hT : ν T = 1) (h : T ⊆ T') : ν T' = 1 :=
  le_antisymm (fa_le_one hν h1 _) (hT ▸ fa_mono hν h)

end Measure

/-- The image of an amenable group under a homomorphism is amenable. -/
theorem isAmenable_range {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    (hP : Garrido.IsAmenable P) : Garrido.IsAmenable f.range := by
  obtain ⟨m, ⟨h0, hadd⟩, h1, hinv⟩ := hP
  refine ⟨fun s => m (f.rangeRestrict ⁻¹' s), ⟨by simpa using h0, ?_⟩, by simpa using h1, ?_⟩
  · intro s t hst
    show m (f.rangeRestrict ⁻¹' (s ∪ t)) = _
    rw [Set.preimage_union]
    exact hadd _ _ (hst.preimage _)
  · intro k s
    obtain ⟨c, hc⟩ := f.rangeRestrict_surjective k
    have : f.rangeRestrict ⁻¹' (k • s) = c • (f.rangeRestrict ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, map_mul,
        map_inv, hc]
    show m (f.rangeRestrict ⁻¹' (k • s)) = m (f.rangeRestrict ⁻¹' s)
    rw [this, hinv]

/-! ## The subgroups `K_A = Im(F(A) → F(X))` -/

universe u v

section Functor

variable (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) {X : Type u}

/-- The image of `F(A) → F(X)`. -/
noncomputable def K (A : Finset X) : Subgroup (extend F X) := (extendι F A).hom.range

lemma exists_K (b : extend F X) : ∃ A : Finset X, b ∈ K F A := by
  refine Quot.inductionOn b ?_
  rintro ⟨A, c⟩
  exact ⟨A, c, rfl⟩

lemma K_mono {A B : Finset X} (h : A ⊆ B) : K F A ≤ K F B := by
  rintro _ ⟨c, rfl⟩
  have w := (GrpCat.FilteredColimits.colimitCocone.{u, u} (finsetDiagram X ⋙ F)).w (homOfLE h)
  change F.map _ ≫ extendι F _ = extendι F _ at w
  refine ⟨(F.map ((finsetDiagram X).map (homOfLE h))).hom c, ?_⟩
  have := congrArg (fun φ => φ.hom c) w
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply] at this
  exact this

lemma exists_K_finset (E₀ : Finset (extend F X)) : ∃ A : Finset X, ∀ b ∈ E₀, b ∈ K F A := by
  classical
  induction E₀ using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert b E hb ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨B, hB⟩ := exists_K F b
    refine ⟨A ∪ B, ?_⟩
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact K_mono F Finset.subset_union_right hB
    · exact K_mono F Finset.subset_union_left (hA y hy)

variable (G : Type v) [Group G] [MulAction G X]

lemma aut_K (g : G) (A : Finset X) {b : extend F X} (hb : b ∈ K F A) :
    extendAut F G X g b ∈ K F (act g A) := by
  obtain ⟨c, rfl⟩ := hb
  refine ⟨(F.map (finsetMap (MulAction.toPerm g : Equiv.Perm X).toEmbedding
    (subset_refl (A.map _)))).hom c, ?_⟩
  have := congrArg (fun φ => φ.hom c)
    (extendι_extendMap F (MulAction.toPerm g : Equiv.Perm X).toEmbedding A)
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply] at this
  exact this.symm

lemma aut_inv_aut (g : G) (b : extend F X) :
    extendAut F G X g⁻¹ (extendAut F G X g b) = b := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

lemma aut_K_inv (g : G) (A : Finset X) {b : extend F X} (hb : b ∈ K F (act g A)) :
    extendAut F G X g⁻¹ b ∈ K F A := by
  have := aut_K F G g⁻¹ _ hb
  rwa [← act_mul, inv_mul_cancel, act_one] at this

/-- An element fixing `A` pointwise fixes `K_A` pointwise. -/
lemma aut_fix (g : G) (A : Finset X) (hg : ∀ a ∈ A, g • a = a) {b : extend F X}
    (hb : b ∈ K F A) : extendAut F G X g b = b := by
  obtain ⟨c, rfl⟩ := hb
  set e := (MulAction.toPerm g : Equiv.Perm X).toEmbedding
  have h : A.map e ⊆ A := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    show g • a ∈ A
    rw [hg a ha]; exact ha
  have hid : finsetMap e h = 𝟙 _ := by
    ext a
    exact hg a a.2
  have key := map_finsetMap_comp_extendι F e (subset_refl (A.map e)) h
  have h1 := congrArg (fun φ => φ.hom c) (extendι_extendMap F e A)
  have h2 := congrArg (fun φ => φ.hom c) key
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply] at h1 h2
  show (extendMap F e).hom ((extendι F A).hom c) = _
  rw [h1, h2, hid, F.map_id]
  rfl

lemma inl_smul (k b : extend F X) :
    (SemidirectProduct.inl k : FunctorProduct F G X) • b = k * b := by
  show (SemidirectProduct.inl k : FunctorProduct F G X).left *
    extendAut F G X (SemidirectProduct.inl k : FunctorProduct F G X).right b = k * b
  simp

lemma inr_smul (g : G) (b : extend F X) :
    (SemidirectProduct.inr g : FunctorProduct F G X) • b = extendAut F G X g b := by
  show (SemidirectProduct.inr g : FunctorProduct F G X).left *
    extendAut F G X (SemidirectProduct.inr g : FunctorProduct F G X).right b = _
  simp

end Functor

/-! ## Averages of finitely many set functions -/

section Avg

variable {ι Z : Type*}

/-- The average of finitely many set functions. -/
noncomputable def avg (Q : Finset ι) (μ : ι → Set Z → ℝ≥0∞) : Set Z → ℝ≥0∞ :=
  fun S => (Q.card : ℝ≥0∞)⁻¹ * ∑ i ∈ Q, μ i S

lemma avg_fa {Q : Finset ι} {μ : ι → Set Z → ℝ≥0∞}
    (hμ : ∀ i ∈ Q, Garrido.IsFinitelyAdditiveMeasure (μ i)) :
    Garrido.IsFinitelyAdditiveMeasure (avg Q μ) := by
  refine ⟨?_, ?_⟩
  · simp only [avg]
    rw [Finset.sum_eq_zero (fun i hi => (hμ i hi).1), mul_zero]
  · intro S T hST
    simp only [avg]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => (hμ i hi).2 S T hST)

lemma avg_one {Q : Finset ι} {μ : ι → Set Z → ℝ≥0∞} (hQ : Q.Nonempty) (S : Set Z)
    (h : ∀ i ∈ Q, μ i S = 1) : avg Q μ S = 1 := by
  simp only [avg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hQ))
    (ENNReal.natCast_ne_top _)

end Avg

/-! ## Good means for a finite subset `A ⊆ X` -/

section Means

variable (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) {X : Type u}
variable (G : Type v) [Group G] [MulAction G X]

/-- A mean on finite subsets of `F(X)`, concentrated on finite subsets of `K_A`, giving full weight
to the supersets of any finite subset of `K_A`, and `K_A`-invariant. -/
structure Good (A : Finset X) (ν : Set (Finset (extend F X)) → ℝ≥0∞) : Prop where
  fa : Garrido.IsFinitelyAdditiveMeasure ν
  univ : ν Set.univ = 1
  supp : ν {E | ∀ b ∈ E, b ∈ K F A} = 1
  full : ∀ E₀ : Finset (extend F X), (∀ b ∈ E₀, b ∈ K F A) → ν {E | E₀ ⊆ E} = 1
  inv : ∀ k ∈ K F A, pf (SemidirectProduct.inl k : FunctorProduct F G X) ν = ν

theorem exists_good (hF : IsAmenableValued F) (A : Finset X) : ∃ ν, Good F G A ν := by
  classical
  have hK : Garrido.IsAmenable (K F A) := isAmenable_range _ (hF _)
  obtain ⟨μ, hμ, -, hμ1, hinv, hfull⟩ :=
    (isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
      (G := K F A) (X := K F A)).1 hK
  let ι0 : K F A ↪ extend F X := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨fun S => μ {E : Finset (K F A) | E.map ι0 ∈ S}, ⟨⟨by simpa using hμ.1, ?_⟩, by simpa using hμ1, ?_, ?_, ?_⟩⟩
  · intro S T hST
    show μ {E : Finset (K F A) | E.map ι0 ∈ S ∪ T} =
      μ {E : Finset (K F A) | E.map ι0 ∈ S} + μ {E : Finset (K F A) | E.map ι0 ∈ T}
    exact hμ.2 _ _ (hST.preimage (fun E : Finset (K F A) => E.map ι0))
  · have : {E : Finset (K F A) | ∀ b ∈ E.map ι0, b ∈ K F A} = Set.univ := by
      ext E
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro b hb
      rw [Finset.mem_map] at hb
      obtain ⟨x, -, rfl⟩ := hb
      exact x.2
    show μ {E : Finset (K F A) | ∀ b ∈ E.map ι0, b ∈ K F A} = 1
    rw [this]
    exact hμ1
  · intro E₀ hE₀
    let E₀' : Finset (K F A) := E₀.subtype (· ∈ K F A)
    apply eq_one_of_sub hμ hμ1 (hfull E₀' (Set.subset_univ _))
    intro E hE b hb
    rw [Finset.mem_map]
    exact ⟨⟨b, hE₀ b hb⟩, hE (Finset.mem_subtype.2 hb), rfl⟩
  · intro k hk
    funext S
    have key : ∀ E : Finset (K F A),
        act (SemidirectProduct.inl k : FunctorProduct F G X) (E.map ι0) =
          (act (⟨k, hk⟩ : K F A) E).map ι0 := by
      intro E
      unfold act
      rw [Finset.map_map, Finset.map_map]
      congr 1
      ext x
      show (SemidirectProduct.inl k : FunctorProduct F G X) • (x : extend F X) = k * x
      rw [inl_smul]
    have : {E : Finset (K F A) | E.map ι0 ∈
        act (SemidirectProduct.inl k : FunctorProduct F G X) ⁻¹' S} =
        act (⟨k, hk⟩ : K F A) ⁻¹' {E | E.map ι0 ∈ S} := by
      ext E
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, key]
    show μ _ = μ _
    rw [this, show act (⟨k, hk⟩ : K F A) ⁻¹' {E | E.map ι0 ∈ S} =
      act (⟨k, hk⟩ : K F A)⁻¹ '' {E | E.map ι0 ∈ S} by rw [image_act, inv_inv]]
    exact hinv _ _

theorem good_transport {A : Finset X} {ν : Set (Finset (extend F X)) → ℝ≥0∞}
    (h : Good F G A ν) (g : G) :
    Good F G (act g A) (pf (SemidirectProduct.inr g : FunctorProduct F G X) ν) where
  fa := pf_fa _ h.fa
  univ := h.univ
  supp := by
    show ν _ = 1
    apply eq_one_of_sub h.fa h.univ h.supp
    intro E hE b hb
    have := aut_K F G g A (hE _ (mem_act.1 hb))
    rwa [← inr_smul, smul_inv_smul] at this
  full := by
    intro E₀ hE₀
    show ν _ = 1
    have hE₁ : ∀ b ∈ act (SemidirectProduct.inr g : FunctorProduct F G X)⁻¹ E₀, b ∈ K F A := by
      intro b hb
      rw [mem_act, inv_inv] at hb
      have := aut_K_inv F G g A (hE₀ _ hb)
      rwa [inr_smul, aut_inv_aut] at this
    apply eq_one_of_sub h.fa h.univ (h.full _ hE₁)
    intro E hE b hb
    show b ∈ act _ E
    rw [mem_act]
    apply hE
    rw [mem_act, inv_inv, smul_inv_smul]
    exact hb
  inv := by
    intro k hk
    have hk' := aut_K_inv F G g A hk
    have e : (SemidirectProduct.inl k : FunctorProduct F G X) * SemidirectProduct.inr g =
        SemidirectProduct.inr g * SemidirectProduct.inl (extendAut F G X g⁻¹ k) := by
      ext <;> simp
    rw [← pf_mul, e, pf_mul, h.inv _ hk']

theorem pf_fix {A : Finset X} {ν : Set (Finset (extend F X)) → ℝ≥0∞}
    (h : Good F G A ν) (g : G) (hg : ∀ a ∈ A, g • a = a) :
    pf (SemidirectProduct.inr g : FunctorProduct F G X) ν = ν := by
  have hfix : ∀ E : Finset (extend F X), (∀ b ∈ E, b ∈ K F A) →
      act (SemidirectProduct.inr g : FunctorProduct F G X) E = E := by
    intro E hE
    ext b
    unfold act
    rw [Finset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (MulAction.toPerm (SemidirectProduct.inr g : FunctorProduct F G X)).toEmbedding x
          = x := by
        show (SemidirectProduct.inr g : FunctorProduct F G X) • x = x
        rw [inr_smul, aut_fix F G g A hg (hE x hx)]
      rw [this]
      exact hx
    · intro hb
      refine ⟨b, hb, ?_⟩
      show (SemidirectProduct.inr g : FunctorProduct F G X) • b = b
      rw [inr_smul, aut_fix F G g A hg (hE b hb)]
  funext S
  show ν (act _ ⁻¹' S) = ν S
  rw [eq_inter h.fa h.univ h.supp, eq_inter h.fa h.univ h.supp S]
  congr 1
  ext E
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [hfix E h2] at h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [hfix E h2], h2⟩

/-! ## Averaging over the stabiliser of `A` -/

open Classical in
/-- The maps `A → A` that are restrictions of elements of `G` stabilising `A`. -/
noncomputable def Q (A : Finset X) : Finset (A → A) :=
  Finset.univ.filter (fun f => ∃ g : G, act g A = A ∧ ∀ a : A, g • (a : X) = f a)

open Classical in
/-- A chosen element of `G` restricting to `f`. -/
noncomputable def lift (A : Finset X) (f : A → A) : G :=
  if h : ∃ g : G, act g A = A ∧ ∀ a : A, g • (a : X) = f a then Classical.choose h else 1

open Classical in
lemma lift_spec {A : Finset X} {f : A → A} (hf : f ∈ Q G A) :
    act (lift G A f) A = A ∧ ∀ a : A, lift G A f • (a : X) = f a := by
  have h : ∃ g : G, act g A = A ∧ ∀ a : A, g • (a : X) = f a := by
    unfold Q at hf
    exact (Finset.mem_filter.1 hf).2
  unfold lift
  rw [dif_pos h]
  exact Classical.choose_spec h

lemma mem_of_stab {A : Finset X} {h : G} (hh : act h A = A) {x : X} (hx : x ∈ A) :
    h • x ∈ A := by
  have : h • x ∈ act h A := mem_act.2 (by simpa using hx)
  rwa [hh] at this

open Classical in
/-- Post-composition with the restriction of `h`. -/
noncomputable def tr (A : Finset X) (h : G) (f : A → A) : A → A := fun a =>
  if hx : h • (f a : X) ∈ A then ⟨_, hx⟩ else f a

lemma tr_val {A : Finset X} {h : G} (hh : act h A = A) (f : A → A) (a : A) :
    (tr G A h f a : X) = h • (f a : X) := by
  unfold tr
  rw [dif_pos (mem_of_stab G hh (f a).2)]

open Classical in
lemma mem_Q {A : Finset X} {f : A → A} (g : G) (hg : act g A = A)
    (hgf : ∀ a : A, g • (a : X) = f a) : f ∈ Q G A := by
  unfold Q
  exact Finset.mem_filter.2 ⟨Finset.mem_univ f, g, hg, hgf⟩

theorem exists_stab_good (hF : IsAmenableValued F) (A : Finset X) :
    ∃ N, Good F G A N ∧
      ∀ h : G, act h A = A → pf (SemidirectProduct.inr h : FunctorProduct F G X) N = N := by
  obtain ⟨ν, hν⟩ := exists_good F G hF A
  let μ : (A → A) → Set (Finset (extend F X)) → ℝ≥0∞ := fun f =>
    pf (SemidirectProduct.inr (lift G A f) : FunctorProduct F G X) ν
  have hμ : ∀ f ∈ Q G A, Good F G A (μ f) := fun f hf => by
    have := good_transport F G hν (lift G A f)
    rwa [(lift_spec G hf).1] at this
  have hQ : (Q G A).Nonempty := ⟨id, mem_Q G 1 (act_one A) (fun a => one_smul G _)⟩
  refine ⟨avg (Q G A) μ, ⟨avg_fa fun f hf => (hμ f hf).fa, avg_one hQ _ fun f hf => (hμ f hf).univ,
    avg_one hQ _ fun f hf => (hμ f hf).supp,
    fun E₀ hE₀ => avg_one hQ _ fun f hf => (hμ f hf).full E₀ hE₀, ?_⟩, ?_⟩
  · intro k hk
    funext S
    show ((Q G A).card : ℝ≥0∞)⁻¹ * ∑ i ∈ Q G A, μ i (act _ ⁻¹' S) =
      ((Q G A).card : ℝ≥0∞)⁻¹ * ∑ i ∈ Q G A, μ i S
    congr 1
    exact Finset.sum_congr rfl fun i hi => congrFun ((hμ i hi).inv k hk) S
  intro h hh
  have hh' : act h⁻¹ A = A := by
    conv_lhs => rw [← hh]
    rw [← act_mul, inv_mul_cancel, act_one]
  have hT : ∀ (h : G), act h A = A → ∀ f ∈ Q G A, tr G A h f ∈ Q G A ∧
      pf (SemidirectProduct.inr h : FunctorProduct F G X) (μ f) = μ (tr G A h f) := by
    intro h hh f hf
    obtain ⟨hl1, hl2⟩ := lift_spec G hf
    have hmem : tr G A h f ∈ Q G A := by
      refine mem_Q G (h * lift G A f) ?_ (fun a => ?_)
      · rw [act_mul, hl1, hh]
      · rw [tr_val G hh, mul_smul, hl2]
    refine ⟨hmem, ?_⟩
    obtain ⟨-, hm2⟩ := lift_spec G hmem
    have hc' : ∀ a : A, ((lift G A (tr G A h f))⁻¹ * (h * lift G A f)) • (a : X) = a := by
      intro a
      rw [mul_smul, mul_smul, hl2 a, ← tr_val G hh, ← hm2 a, inv_smul_smul]
    have hc : ∀ a ∈ A, ((lift G A (tr G A h f))⁻¹ * (h * lift G A f)) • a = a :=
      fun a ha => hc' ⟨a, ha⟩
    have e : (SemidirectProduct.inr h : FunctorProduct F G X) *
        SemidirectProduct.inr (lift G A f) =
        SemidirectProduct.inr (lift G A (tr G A h f)) *
          SemidirectProduct.inr ((lift G A (tr G A h f))⁻¹ * (h * lift G A f)) := by
      rw [← map_mul, ← map_mul, mul_inv_cancel_left]
    show pf _ (pf _ ν) = pf _ ν
    rw [← pf_mul, e, pf_mul, pf_fix F G hν _ hc]
  funext S
  show ((Q G A).card : ℝ≥0∞)⁻¹ * ∑ f ∈ Q G A, μ f (act _ ⁻¹' S) =
    ((Q G A).card : ℝ≥0∞)⁻¹ * ∑ f ∈ Q G A, μ f S
  congr 1
  calc ∑ f ∈ Q G A, μ f (act (SemidirectProduct.inr h : FunctorProduct F G X) ⁻¹' S)
      = ∑ f ∈ Q G A, μ (tr G A h f) S :=
        Finset.sum_congr rfl fun f hf => congrFun (hT h hh f hf).2 S
    _ = ∑ f ∈ Q G A, μ f S := by
        refine Finset.sum_nbij' (tr G A h) (tr G A h⁻¹) (fun f hf => (hT h hh f hf).1)
          (fun f hf => (hT h⁻¹ hh' f hf).1) (fun f _ => ?_) (fun f _ => ?_) (fun f _ => rfl)
        · funext a
          apply Subtype.ext
          rw [tr_val G hh', tr_val G hh, inv_smul_smul]
        · funext a
          apply Subtype.ext
          rw [tr_val G hh, tr_val G hh', smul_inv_smul]

/-! ## A `G`-equivariant family of good means -/

/-- The `G`-orbit of a finite subset. -/
def orb (A : Finset X) : Set (Finset X) := {B | ∃ g : G, act g B = A}

lemma orb_act (h : G) (A : Finset X) : orb G (act h A) = orb G A := by
  ext B
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨h⁻¹ * g, by rw [act_mul, hg, ← act_mul, inv_mul_cancel, act_one]⟩
  · rintro ⟨g, hg⟩
    exact ⟨h * g, by rw [act_mul, hg]⟩

/-- A representative of the orbit. -/
noncomputable def rep (A : Finset X) : Finset X := Classical.epsilon (fun B => B ∈ orb G A)

lemma rep_mem (A : Finset X) : rep G A ∈ orb G A :=
  Classical.epsilon_spec (p := fun B => B ∈ orb G A) ⟨A, 1, act_one A⟩

lemma rep_act (h : G) (A : Finset X) : rep G (act h A) = rep G A := by
  unfold rep
  rw [orb_act]

/-- An element carrying the representative to `A`. -/
noncomputable def gsel (A : Finset X) : G := Classical.choose (rep_mem G A)

lemma gsel_spec (A : Finset X) : act (gsel G A) (rep G A) = A := Classical.choose_spec (rep_mem G A)

/-- The stabiliser-invariant good mean on a representative. -/
noncomputable def Nf (hF : IsAmenableValued F) (B : Finset X) :
    Set (Finset (extend F X)) → ℝ≥0∞ :=
  Classical.choose (exists_stab_good F G hF B)

/-- The equivariant family. -/
noncomputable def fam (hF : IsAmenableValued F) (A : Finset X) :
    Set (Finset (extend F X)) → ℝ≥0∞ :=
  pf (SemidirectProduct.inr (gsel G A) : FunctorProduct F G X) (Nf F G hF (rep G A))

lemma fam_good (hF : IsAmenableValued F) (A : Finset X) : Good F G A (fam F G hF A) := by
  have := good_transport F G (Classical.choose_spec (exists_stab_good F G hF (rep G A))).1
    (gsel G A)
  rwa [gsel_spec] at this

lemma fam_equiv (hF : IsAmenableValued F) (h : G) (A : Finset X) :
    pf (SemidirectProduct.inr h : FunctorProduct F G X) (fam F G hF A) = fam F G hF (act h A) := by
  have hst := (Classical.choose_spec (exists_stab_good F G hF (rep G A))).2
  have hs1 := gsel_spec G A
  have hs2 := gsel_spec G (act h A)
  unfold fam
  rw [rep_act] at hs2 ⊢
  generalize gsel G (act h A) = g2 at hs2 ⊢
  have hc : act (g2⁻¹ * (h * gsel G A)) (rep G A) = rep G A := by
    rw [act_mul, act_mul, hs1, ← hs2, ← act_mul, inv_mul_cancel, act_one]
  have e : (SemidirectProduct.inr h : FunctorProduct F G X) * SemidirectProduct.inr (gsel G A) =
      SemidirectProduct.inr g2 * SemidirectProduct.inr (g2⁻¹ * (h * gsel G A)) := by
    rw [← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [← pf_mul, e, pf_mul]
  exact congrArg _ (hst _ hc)

/-! ## Integrating the family against the extensively amenable mean -/

theorem isExtensivelyAmenable_functorProduct (hF : IsAmenableValued F)
    (hGX : IsExtensivelyAmenable G X) :
    IsExtensivelyAmenable (FunctorProduct F G X) (extend F X) := by
  obtain ⟨m, hm, -, hm1, minv, mfull⟩ := hGX
  have hle : ∀ (A : Finset X) S, (fam F G hF A S).toReal ≤ 1 := fun A S =>
    fa_toReal_le_one (fam_good F G hF A).fa (fam_good F G hF A).univ S
  have hnn : ∀ (A : Finset X) S, 0 ≤ (fam F G hF A S).toReal := fun _ _ => ENNReal.toReal_nonneg
  let M : Set (Finset (extend F X)) → ℝ≥0∞ := fun S =>
    ENNReal.ofReal (integ m (fun A => (fam F G hF A S).toReal))
  have hint1 : integ m (fun _ => (1 : ℝ)) = 1 := by
    have h := integ_indicator hm hm1 Set.univ
    have e : (fun _ : Finset X => (1 : ℝ)) = Set.univ.indicator 1 := by
      funext A; simp
    rw [e, h, hm1, ENNReal.toReal_one]
  have hint0 : integ m (fun _ => (0 : ℝ)) = 0 := by
    have h := integ_indicator hm hm1 ∅
    have e : (fun _ : Finset X => (0 : ℝ)) = (∅ : Set (Finset X)).indicator 1 := by
      funext A; simp
    rw [e, h, hm.1, ENNReal.toReal_zero]
  have hae : ∀ (A₁ : Finset X) (f g : Finset X → ℝ), (∀ A, A₁ ⊆ A → f A = g A) →
      integ m f = integ m g := by
    intro A₁ f g hfg
    apply integ_congr hm hm1
    have h1 : m {A | A₁ ⊆ A} = 1 := mfull A₁ (Set.subset_univ _)
    apply le_antisymm _ bot_le
    calc m {A | f A ≠ g A} ≤ m {A | A₁ ⊆ A}ᶜ := fa_mono hm (fun A hA h' => hA (hfg A h'))
      _ = 0 := compl_zero hm hm1 h1
  have hMinr : ∀ g : G, pf (SemidirectProduct.inr g : FunctorProduct F G X) M = M := by
    intro g
    funext S
    show ENNReal.ofReal (integ m (fun A => (fam F G hF A (act _ ⁻¹' S)).toReal)) =
      ENNReal.ofReal (integ m (fun A => (fam F G hF A S).toReal))
    congr 1
    have h1 : (fun A => (fam F G hF A
        (act (SemidirectProduct.inr g : FunctorProduct F G X) ⁻¹' S)).toReal) =
        (fun A => (fam F G hF A S).toReal) ∘ (MulAction.toPerm g : Equiv.Perm X).finsetCongr := by
      funext A
      show _ = (fam F G hF (act g A) S).toReal
      rw [← fam_equiv F G hF g A]
      rfl
    rw [h1, integ_comp_equiv _ (fun S' => minv g S')]
  have hMinl : ∀ a : extend F X, pf (SemidirectProduct.inl a : FunctorProduct F G X) M = M := by
    intro a
    funext S
    obtain ⟨A₁, hA₁⟩ := exists_K F a
    show ENNReal.ofReal (integ m (fun A => (fam F G hF A (act _ ⁻¹' S)).toReal)) =
      ENNReal.ofReal (integ m (fun A => (fam F G hF A S).toReal))
    congr 1
    apply hae A₁
    intro A hA
    have := congrFun ((fam_good F G hF A).inv a (K_mono F hA hA₁)) S
    exact congrArg ENNReal.toReal this
  have hMall : ∀ p : FunctorProduct F G X, pf p M = M := by
    intro p
    rw [← SemidirectProduct.inl_left_mul_inr_right p, pf_mul, hMinr, hMinl]
  have hMuniv : M Set.univ = 1 := by
    show ENNReal.ofReal (integ m _) = 1
    have e : (fun (A : Finset X) => (fam F G hF A Set.univ).toReal) = fun _ => (1 : ℝ) := by
      funext A
      rw [(fam_good F G hF A).univ, ENNReal.toReal_one]
    rw [e, hint1, ENNReal.ofReal_one]
  refine ⟨M, ⟨?_, ?_⟩, ?_, hMuniv, ?_, ?_⟩
  · show ENNReal.ofReal (integ m _) = 0
    have e : (fun (A : Finset X) => (fam F G hF A ∅).toReal) = fun _ => (0 : ℝ) := by
      funext A
      rw [(fam_good F G hF A).fa.1, ENNReal.toReal_zero]
    rw [e, hint0, ENNReal.ofReal_zero]
  · intro S T hST
    show ENNReal.ofReal _ = ENNReal.ofReal _ + ENNReal.ofReal _
    have e : (fun (A : Finset X) => (fam F G hF A (S ∪ T)).toReal) =
        (fun A => (fam F G hF A S).toReal) + (fun A => (fam F G hF A T).toReal) := by
      funext A
      simp only [Pi.add_apply]
      exact fa_toReal_union (fam_good F G hF A).fa (fam_good F G hF A).univ hST
    have hsum : ∀ A, (fam F G hF A S).toReal + (fam F G hF A T).toReal ≤ 1 := by
      intro A
      rw [← fa_toReal_union (fam_good F G hF A).fa (fam_good F G hF A).univ hST]
      exact hle A _
    rw [e, integ_add hm hm1 (fun A => hnn A S) (fun A => hnn A T) hsum,
      ENNReal.ofReal_add (integ_nonneg_le_one hm hm1 (fun A => hnn A S) (fun A => hle A S)).1
        (integ_nonneg_le_one hm hm1 (fun A => hnn A T) (fun A => hle A T)).1]
  · have e : {E : Finset (extend F X) | (E : Set (extend F X)) ⊆ Set.univ} = Set.univ := by
      ext E; simp
    rw [e]
    exact hMuniv
  · intro p S
    show M (act p '' S) = M S
    rw [image_act]
    exact congrFun (hMall p⁻¹) S
  · intro E₀ _
    obtain ⟨A₁, hA₁⟩ := exists_K_finset F E₀
    show ENNReal.ofReal (integ m _) = 1
    rw [hae A₁ _ (fun _ => 1) (fun A hA => by
        rw [(fam_good F G hF A).full E₀ (fun b hb => K_mono F hA (hA₁ b hb)),
          ENNReal.toReal_one]),
      hint1, ENNReal.ofReal_one]

end Means

/-- JMMS Theorem 1.3, forward half: if `G ↷ X` is extensively amenable and `F` takes amenable
values, then `F(X) ⋊ G ↷ F(X)` is amenable and extensively amenable. -/
theorem forward (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) (hF : IsAmenableValued F)
    (G : Type v) [Group G] (X : Type u) [MulAction G X] :
    IsExtensivelyAmenable G X →
      IsAmenableAction (FunctorProduct F G X) (extend F X) ∧
        IsExtensivelyAmenable (FunctorProduct F G X) (extend F X) := by
  intro h
  have hE := isExtensivelyAmenable_functorProduct F G hF h
  exact ⟨(isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable).2
    ⟨1⟩ hE, hE⟩

end JMMS.IETP13F

end

section

/-!
# JMMS Theorem 1.3, converse half (Theorem 3.14, p. 13)

If `F(X) ⋊ G ↷ F(X)` is amenable and `F` is tight on `X`, then `G ↷ X` is extensively amenable.

Route (the paper's): push an invariant mean on `F(X)` forward along the support map
`supp : F(X) → P_f(X)`, `supp b = ⋂ {A finite | b ∈ Im(F(A) → F(X))}`. The pushed mean is
`G`-invariant since `supp` is `G`-equivariant. The set `{b | x₀ ∈ supp b}` contains the complement
of the proper subgroup `H = Im(F(X ∖ {x₀}) → F(X))`, which has positive weight by
`F(X)`-invariance (`H` and `aH`, `a ∉ H`, are disjoint and of equal weight). Lemma 2.2
((iv) ⇒ (i), the milestone `JMMS.isExtensivelyAmenable_tfae`) concludes.
-/

open IntervalExchange CategoryTheory
open scoped ENNReal Pointwise

namespace JMMS
namespace IETP13C

universe u v

variable (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) {X : Type u}

/-- The image of `F(A) → F(X)`. -/
def Rng (A : Finset X) : Set (extend F X) := Set.range (extendι F A).hom

lemma exists_rng (b : extend F X) : ∃ A : Finset X, b ∈ Rng F A := by
  refine Quot.inductionOn b ?_
  rintro ⟨A, c⟩
  exact ⟨A, c, rfl⟩

/-- The support of `b ∈ F(X)`: the intersection of the finite `A` with `b ∈ Im F(A)`. -/
noncomputable def supp (b : extend F X) : Finset X :=
  @Finset.filter _ (fun x => ∀ A : Finset X, b ∈ Rng F A → x ∈ A) (Classical.decPred _)
    (Classical.choose (exists_rng F b))

lemma mem_supp (b : extend F X) (x : X) :
    x ∈ supp F b ↔ ∀ A : Finset X, b ∈ Rng F A → x ∈ A := by
  unfold supp
  rw [@Finset.mem_filter _ _ (Classical.decPred _)]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h _ (Classical.choose_spec (exists_rng F b)), h⟩

lemma extendMap_rng {Y : Type u} (f : X ↪ Y) (A : Finset X) {b : extend F X}
    (hb : b ∈ Rng F A) : (extendMap F f).hom b ∈ Rng F (A.map f) := by
  obtain ⟨c, rfl⟩ := hb
  refine ⟨(F.map (finsetMap f (subset_refl (A.map f)))).hom c, ?_⟩
  have := congrArg (fun φ => φ.hom c) (extendι_extendMap F f A)
  simpa using this.symm

variable (G : Type v) [Group G] [MulAction G X]

lemma aut_rng (g : G) (A : Finset X) {b : extend F X} (hb : b ∈ Rng F A) :
    extendAut F G X g b ∈ Rng F (A.map (MulAction.toPerm g : Equiv.Perm X).toEmbedding) :=
  extendMap_rng F _ A hb

lemma aut_inv_aut (g : G) (b : extend F X) :
    extendAut F G X g⁻¹ (extendAut F G X g b) = b := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

lemma aut_aut_inv (g : G) (b : extend F X) :
    extendAut F G X g (extendAut F G X g⁻¹ b) = b := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

lemma supp_aut (g : G) (b : extend F X) :
    supp F (extendAut F G X g b) =
      (supp F b).map (MulAction.toPerm g : Equiv.Perm X).toEmbedding := by
  ext x
  rw [Finset.mem_map_equiv, mem_supp, mem_supp]
  have hx : (MulAction.toPerm g : Equiv.Perm X).symm x = g⁻¹ • x := rfl
  rw [hx]
  constructor
  · intro h A hA
    have := h _ (aut_rng F G g A hA)
    rw [Finset.mem_map_equiv] at this
    exact this
  · intro h A hA
    have h1 := aut_rng F G g⁻¹ A hA
    rw [aut_inv_aut] at h1
    have := h _ h1
    rw [Finset.mem_map_equiv] at this
    have e : (MulAction.toPerm g⁻¹ : Equiv.Perm X).symm (g⁻¹ • x) = x := by
      show g⁻¹⁻¹ • g⁻¹ • x = x
      simp
    rwa [e] at this

/-- An element of `Im F(A)` with `x₀ ∉ A` lies in the image of `F(X ∖ {x₀})`. -/
lemma mem_range_of_rng (x₀ : X) (A : Finset X) (hA : x₀ ∉ A) {b : extend F X}
    (hb : b ∈ Rng F A) :
    b ∈ (extendMap F (Function.Embedding.subtype fun y => y ≠ x₀)).hom.range := by
  classical
  obtain ⟨c, rfl⟩ := hb
  set f := Function.Embedding.subtype fun y : X => y ≠ x₀
  set A' : Finset {y // y ≠ x₀} := A.subtype (fun y => y ≠ x₀)
  have hsub : A'.map f ⊆ A := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact (Finset.mem_subtype.1 hz)
  have hne : ∀ a : A, (a : X) ≠ x₀ := fun a h => hA (h ▸ a.2)
  let ψ : finsetObj A ⟶ finsetObj A' :=
    ⟨FintypeCat.homMk fun a => ⟨⟨a.1, hne a⟩, Finset.mem_subtype.2 a.2⟩, by
      intro a b hab
      have := congrArg (fun z : A' => ((z : {y // y ≠ x₀}) : X)) hab
      exact Subtype.ext this⟩
  have hψ : ψ ≫ finsetMap f hsub = 𝟙 _ := by ext a; rfl
  have key := map_finsetMap_comp_extendι F f hsub (subset_refl (A'.map f))
  refine ⟨(extendι F A').hom ((F.map ψ).hom c), ?_⟩
  have h1 := congrArg (fun φ => φ.hom ((F.map ψ).hom c)) (extendι_extendMap F f A')
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply] at h1
  rw [h1]
  have h2 := congrArg (fun φ => φ.hom ((F.map ψ).hom c)) key
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply] at h2
  rw [← h2]
  have h3 := congrArg (fun φ => φ.hom c) (F.map_comp ψ (finsetMap f hsub))
  simp only [hψ, F.map_id, GrpCat.hom_comp, GrpCat.hom_id, MonoidHom.coe_comp,
    Function.comp_apply, MonoidHom.id_apply] at h3
  rw [← h3]

lemma measure_le {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    {s t : Set α} (h : s ⊆ t) : m s ≤ m t := by
  have : t = s ∪ (t \ s) := (Set.union_sdiff_cancel h).symm
  rw [this, hm.2 _ _ Set.disjoint_sdiff_right]
  exact le_self_add

lemma measure_compl {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    (s : Set α) : m Set.univ = m s + m sᶜ := by
  rw [← hm.2 _ _ disjoint_compl_right, Set.union_compl_self]

theorem converse
    (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) (_hF : IsAmenableValued F)
    (G : Type v) [Group G] (X : Type u) [MulAction G X] :
    IsAmenableAction (FunctorProduct F G X) (extend F X) → IsTight F X →
      IsExtensivelyAmenable G X := by
  rintro ⟨m, hm, hm1, hinv⟩ htight
  refine (JMMS.isExtensivelyAmenable_tfae (G := G) (X := X)).out 0 3 |>.2 ?_
  refine ⟨fun S => m (supp F ⁻¹' S), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa using hm.1
  · intro s t hst
    show m _ = m _ + m _
    rw [Set.preimage_union]
    exact hm.2 _ _ (hst.preimage _)
  · simpa using hm1
  · intro g S
    have e : supp F ⁻¹' ((fun E => E.map (MulAction.toPerm g : Equiv.Perm X).toEmbedding) '' S) =
        (⟨1, g⟩ : FunctorProduct F G X) • (supp F ⁻¹' S) := by
      ext c
      have hs : ∀ b : extend F X, (⟨1, g⟩ : FunctorProduct F G X) • b = extendAut F G X g b :=
        fun b => one_mul _
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_smul_set, hs]
      constructor
      · rintro ⟨E, hE, hEc⟩
        refine ⟨extendAut F G X g⁻¹ c, ?_, aut_aut_inv F G g c⟩
        convert hE using 1
        rw [supp_aut, ← hEc]
        ext y
        rw [Finset.mem_map_equiv, Finset.mem_map_equiv]
        show g⁻¹ • g⁻¹⁻¹ • y ∈ E ↔ y ∈ E
        simp
      · rintro ⟨b, hb, rfl⟩
        exact ⟨supp F b, hb, (supp_aut F G g b).symm⟩
    show m _ = m _
    rw [e]
    exact hinv _ _
  · intro x₀
    set H := (extendMap F (Function.Embedding.subtype fun y => y ≠ x₀)).hom.range
    have hsub : ((H : Set (extend F X)))ᶜ ⊆ supp F ⁻¹' {E | x₀ ∈ E} := by
      intro b hb
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_supp]
      intro A hA
      by_contra hx
      exact hb (mem_range_of_rng F x₀ A hx hA)
    intro h0
    have hc : m ((H : Set (extend F X)))ᶜ = 0 :=
      le_antisymm (h0 ▸ measure_le hm hsub) (by simp)
    have hH : m (H : Set (extend F X)) = 1 := by
      rw [← hm1, measure_compl hm (H : Set (extend F X)), hc, add_zero]
    obtain ⟨a, ha⟩ : ∃ a, a ∉ H := by
      by_contra hall
      push Not at hall
      exact htight x₀ fun b => hall b
    have hs : ∀ b : extend F X, (⟨a, 1⟩ : FunctorProduct F G X) • b = a * b := by
      intro b
      show a * extendAut F G X 1 b = a * b
      rw [map_one, MulAut.one_apply]
    have haH : m ((⟨a, 1⟩ : FunctorProduct F G X) • (H : Set (extend F X))) = 1 := by
      rw [hinv, hH]
    have hdisj : Disjoint (H : Set (extend F X))
        ((⟨a, 1⟩ : FunctorProduct F G X) • (H : Set (extend F X))) := by
      rw [Set.disjoint_left]
      rintro b hbH ⟨h, hh, rfl⟩
      change (⟨a, 1⟩ : FunctorProduct F G X) • h ∈ H at hbH
      rw [hs] at hbH
      apply ha
      have := H.mul_mem hbH (H.inv_mem hh)
      simpa using this
    have := measure_le hm (Set.subset_univ
      ((H : Set (extend F X)) ∪ (⟨a, 1⟩ : FunctorProduct F G X) • (H : Set (extend F X))))
    rw [hm.2 _ _ hdisj, hH, haH, hm1] at this
    norm_num at this

end IETP13C
end JMMS

end

section
open IntervalExchange
universe u v

namespace JMMS

theorem chk_isAmenableAction_and_isExtensivelyAmenable_functorProduct_and_isExtensivelyAmenable_of_isTight
    (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) (hF : IsAmenableValued F)
    (G : Type v) [Group G] (X : Type u) [MulAction G X] :
    (IsExtensivelyAmenable G X →
      IsAmenableAction (FunctorProduct F G X) (extend F X) ∧
        IsExtensivelyAmenable (FunctorProduct F G X) (extend F X)) ∧
    (IsAmenableAction (FunctorProduct F G X) (extend F X) → IsTight F X →
      IsExtensivelyAmenable G X) :=
  ⟨IETP13F.forward F hF G X, IETP13C.converse F hF G X⟩

end JMMS
end

open IntervalExchange
universe u v
open JMMS in
theorem solution
    (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) (hF : IsAmenableValued F)
    (G : Type v) [Group G] (X : Type u) [MulAction G X] :
    (IsExtensivelyAmenable G X →
      IsAmenableAction (FunctorProduct F G X) (extend F X) ∧
        IsExtensivelyAmenable (FunctorProduct F G X) (extend F X)) ∧
    (IsAmenableAction (FunctorProduct F G X) (extend F X) → IsTight F X →
      IsExtensivelyAmenable G X) :=
  JMMS.chk_isAmenableAction_and_isExtensivelyAmenable_functorProduct_and_isExtensivelyAmenable_of_isTight F hF G X
