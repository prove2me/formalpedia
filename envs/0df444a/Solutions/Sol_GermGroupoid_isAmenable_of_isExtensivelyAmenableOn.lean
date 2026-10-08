-- Prove2me | solution 1 for GermGroupoid.isAmenable_of_isExtensivelyAmenableOn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T17:13:05.042355+00:00
-- url     : https://prove2.me/submissions/d93b996b-cc54-447d-b17d-e06f424cbaee

import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Definitions.Def_HomeomorphAction
import Definitions.Def_GermGroupoid
import Theorems.Thm_Garrido_isAmenable_subgroup
import Theorems.Thm_Garrido_isAmenable_of_isAmenable_of_isAmenable_quotient
import Mathlib


section
section
/-!
# A JMMS-type criterion, generic in the lamp group

Parts A, B1, B2, B3 of the Chornyi child (`Solutions/FAmenChild`, assembled in
`f-amenability-mission/solutions/Sol_isAmenable_F_of_isExtensivelyAmenableOn.lean`), with the
lamp group `ℤ` replaced by an arbitrary additive commutative group `L`.

* (A) A free action with an invariant finitely additive probability makes the group amenable.
* (B) Extensive amenability of `G ↷ Y ⊆ X` gives a finitely additive probability on
  `Set (X →₀ L)` invariant under the linear action of `G` and under translations supported
  in `Y`.
-/

open scoped ENNReal Pointwise

namespace FAmenHZ.Lib

variable {L : Type*} [AddCommGroup L]

/-! ## Part A -/


namespace PartA
open scoped ENNReal Pointwise

/-- The chosen representative of the orbit of `y`. -/
noncomputable def rep (G : Type*) {Y : Type*} [Group G] [MulAction G Y] (y : Y) : Y :=
  (Quotient.mk (MulAction.orbitRel G Y) y).out

lemma exists_smul_rep {G Y : Type*} [Group G] [MulAction G Y] (y : Y) :
    ∃ g : G, g • rep G y = y := by
  have h : rep G y ∈ MulAction.orbit G y := by
    have := Quotient.mk_out (s := MulAction.orbitRel G Y) y
    exact (MulAction.orbitRel_apply).1 this
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

lemma rep_smul {G Y : Type*} [Group G] [MulAction G Y] (h : G) (y : Y) :
    rep G (h • y) = rep G y := by
  unfold rep
  congr 1
  exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit y h))

/-- The coordinate of `y`: the group element carrying the representative to `y`. -/
noncomputable def coord (G : Type*) {Y : Type*} [Group G] [MulAction G Y] (y : Y) : G :=
  (exists_smul_rep (G := G) y).choose

lemma coord_smul_rep {G Y : Type*} [Group G] [MulAction G Y] (y : Y) :
    coord G y • rep G y = y :=
  (exists_smul_rep (G := G) y).choose_spec

end PartA

/-! ## Part B1: integrating `[0,1]`-valued functions against a finitely additive probability -/

/-- `∑_{k < 2^n} 2^{-n} m {f ≥ (k+1)/2^n}`: the integral of `⌊2^n f⌋ / 2^n`. -/
noncomputable def layerSum {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n

/-- The integral: the supremum of the layer sums. -/
noncomputable def integ {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) : ℝ := ⨆ n, layerSum m f n


namespace PartB1
open scoped ENNReal

open FAmenHZ.Lib

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

section B1
variable {α : Type*} {m : Set α → ℝ≥0∞}

alias integ_indicator := PartB1.integ_indicator

alias integ_add := PartB1.integ_add

alias integ_congr := PartB1.integ_congr

alias integ_comp_equiv := PartB1.integ_comp_equiv

alias integ_nonneg_le_one := PartB1.integ_nonneg_le_one

end B1

/-! ## Part B2: symmetric translation-invariant means on finitely supported `L`-functions -/


namespace PartB2
open scoped ENNReal Pointwise

end PartB2


namespace PartB2
open scoped ENNReal Pointwise
section B2
variable {X : Type*}

end B2

end PartB2

section B2
variable {X : Type*}

end B2

/-! ## Part B3: the mean on `X →₀ L` from extensive amenability -/


namespace PartB3
open scoped ENNReal Pointwise

lemma fam_mono {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    {s t : Set α} (hst : s ⊆ t) : m s ≤ m t := by
  have := hm.2 s (t \ s) disjoint_sdiff_self_right
  rw [Set.union_sdiff_cancel hst] at this
  rw [this]
  exact le_self_add

lemma fam_compl_eq_zero {α : Type*} {m : Set α → ℝ≥0∞}
    (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) {s : Set α}
    (hs : m s = 1) : m sᶜ = 0 := by
  have := hm.2 s sᶜ disjoint_compl_right
  rw [Set.union_compl_self, h1, hs] at this
  have h' : (1 : ℝ≥0∞) + m sᶜ = 1 + 0 := by rw [← this, add_zero]
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h'

end PartB3

end FAmenHZ.Lib

end
end

section
section
section
open scoped ENNReal Pointwise
namespace GermGroupoid.JN.PartA
open FAmenHZ.Lib FAmenHZ.Lib.PartA
/-!
# Part A: amenability bookkeeping

Transport of amenability along isomorphisms and injective homomorphisms, and JNdlS
Proposition 2.3: a group with an invariant mean on a set it acts on, all of whose stabilizers are
amenable, is amenable.
-/
theorem isAmenable_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : Garrido.IsAmenable G) : Garrido.IsAmenable H := by
  obtain ⟨m, hm, h1, hinv⟩ := hG
  refine ⟨fun S => m (e ⁻¹' S), ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa using hm.1
  · intro s t hst
    simpa [Set.preimage_union] using hm.2 _ _ (hst.preimage _)
  · simpa using h1
  · intro h S
    have : e ⁻¹' (h • S) = e.symm h • (e ⁻¹' S) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
    simp only
    rw [this, hinv]

end GermGroupoid.JN.PartA
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
/-!
# Blueprint: the Juschenko–Nekrashevych–de la Salle theorem, extensive amenability form

JMMS (arXiv:1503.04977) Theorem 6.5, from JNdlS (arXiv:1305.2637) Theorem 3.1. Every lemma below
is `sorry`; the main theorem `chk_isAmenable_of_isExtensivelyAmenableOn` is proved from them.

Proof outline (JNdlS §3.2 with recurrence replaced by extensive amenability):
* the lamp space `Lamp G 𝓗`: germs of `G` modulo right multiplication by germs in `𝓗`,
  as the quotient of `G × X` (the germ of `g` at `y`); `G` acts on the left; `base x` is the class
  of the identity germ at `x`, and `h • base x = base (h x)` exactly when the germ of `h` at `x`
  lies in `𝓗`;
* `FinSec`: functions `ψ : X → Lamp` with `ψ x = base x` for all but finitely many `x`, with `G`
  acting by `(h • ψ) x = h • ψ (h⁻¹ x)` (finite support is kept by condition (i));
* a `G`-invariant mean on `FinSec` (fiber means from amenable germ groups, symmetrised iterated
  products, integrated against the extensive-amenability mean);
* every stabilizer `G_ψ` is amenable (de Cornulier's induction over the support, then the germ
  filtration with kernel in `[[𝓗]]`);
* amenable action + amenable stabilizers ⇒ amenable group.
-/
/-! ## Part A: amenability bookkeeping -/
alias isAmenable_of_mulEquiv := GermGroupoid.JN.PartA.isAmenable_of_mulEquiv

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise
namespace GermGroupoid.JN.PartA
open FAmenHZ.Lib FAmenHZ.Lib.PartA
theorem isAmenable_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (hH : Garrido.IsAmenable H) : Garrido.IsAmenable G :=
  isAmenable_of_mulEquiv (MonoidHom.ofInjective hf).symm
    (Garrido.isAmenable_subgroup hH f.range)

end GermGroupoid.JN.PartA
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
alias isAmenable_of_injective := GermGroupoid.JN.PartA.isAmenable_of_injective

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise
namespace GermGroupoid.JN.PartA
open FAmenHZ.Lib FAmenHZ.Lib.PartA
/-- JNdlS Proposition 2.3: an action with an invariant mean and amenable stabilizers. -/
theorem isAmenable_of_invariant_of_stabilizer {G Y : Type*} [Group G] [MulAction G Y]
    (m : Set Y → ℝ≥0∞) (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (hinv : Garrido.IsInvariant G m)
    (hstab : ∀ y : Y, Garrido.IsAmenable (MulAction.stabilizer G y)) :
    Garrido.IsAmenable G := by
  choose mr hmr hmr1 hmrinv using hstab
  have mr_ne_top : ∀ r (A : Set (MulAction.stabilizer G r)), mr r A ≠ ∞ := fun r A =>
    PartB1.fa_ne_top (hmr r) (hmr1 r) A
  have mr_le_one : ∀ r (A : Set (MulAction.stabilizer G r)), (mr r A).toReal ≤ 1 := fun r A =>
    PartB1.fa_toReal_le_one (hmr r) (hmr1 r) A
  -- the integrand
  let f : Set G → Y → ℝ := fun S y =>
    (mr (rep G y) {k : MulAction.stabilizer G (rep G y) | coord G y * (k : G) ∈ S}).toReal
  have f0 : ∀ S y, 0 ≤ f S y := fun _ _ => ENNReal.toReal_nonneg
  have f1 : ∀ S y, f S y ≤ 1 := fun _ _ => mr_le_one _ _
  have fadd : ∀ s t : Set G, Disjoint s t → f (s ∪ t) = f s + f t := by
    intro s t hst
    funext y
    simp only [f, Pi.add_apply]
    rw [← ENNReal.toReal_add (mr_ne_top _ _) (mr_ne_top _ _), ← (hmr _).2]
    · rfl
    · rw [Set.disjoint_left]
      intro k hk hk'
      exact Set.disjoint_left.1 hst hk hk'
  refine ⟨fun S => ENNReal.ofReal (integ m (f S)), ⟨?_, ?_⟩, ?_, ?_⟩
  · have h0 : f ∅ = (∅ : Set Y).indicator 1 := by
      funext y
      simp only [f, Set.mem_empty_iff_false, Set.ofPred_false, (hmr _).1, Set.indicator_empty]
      rfl
    simp only
    rw [h0, integ_indicator hm h1, hm.1]
    simp
  · intro s t hst
    have hle : ∀ y, f s y + f t y ≤ 1 := fun y => by
      have := f1 (s ∪ t) y
      rwa [fadd s t hst] at this
    simp only
    rw [fadd s t hst, integ_add hm h1 (f0 s) (f0 t) hle,
      ENNReal.ofReal_add (integ_nonneg_le_one hm h1 (f0 s) (f1 s)).1
        (integ_nonneg_le_one hm h1 (f0 t) (f1 t)).1]
  · have hu : f Set.univ = (Set.univ : Set Y).indicator 1 := by
      funext y
      simp only [f, Set.mem_univ, Set.ofPred_true, hmr1, Set.indicator_univ]
      rfl
    simp only
    rw [hu, integ_indicator hm h1, h1]
    simp
  · intro g S
    simp only
    congr 1
    let τ : Y ≃ Y := MulAction.toPerm g⁻¹
    have hτ : ∀ T : Set Y, m (τ '' T) = m T := fun T => hinv g⁻¹ T
    -- moving the representative-indexed mean along an equality of representatives
    have transport : ∀ (r r' : Y), r' = r → ∀ c : G,
        mr r' {k : MulAction.stabilizer G r' | c * (k : G) ∈ S} =
          mr r {k : MulAction.stabilizer G r | c * (k : G) ∈ S} := by
      rintro r _ rfl c; rfl
    have hfun : f (g • S) = f S ∘ τ := by
      funext y
      simp only [f, Function.comp_apply]
      congr 1
      have hy : τ y = g⁻¹ • y := rfl
      rw [hy, transport (rep G y) (rep G (g⁻¹ • y)) (rep_smul g⁻¹ y)]
      set r := rep G y
      set c := coord G y
      set c' := coord G (g⁻¹ • y)
      have hc : c • r = y := coord_smul_rep y
      have hc' : c' • r = g⁻¹ • y := by
        have := coord_smul_rep (G := G) (g⁻¹ • y)
        rwa [rep_smul] at this
      have hsmem : c'⁻¹ * g⁻¹ * c ∈ MulAction.stabilizer G r := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hc, ← hc', inv_smul_smul]
      set s : MulAction.stabilizer G r := ⟨_, hsmem⟩
      have hset : {k : MulAction.stabilizer G r | c * (k : G) ∈ g • S} =
          s⁻¹ • {k : MulAction.stabilizer G r | c' * (k : G) ∈ S} := by
        ext k
        simp only [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_inv,
          Subgroup.coe_mul, s]
        constructor <;> intro hk <;> convert hk using 1 <;> group
      rw [hset, hmrinv]
    rw [hfun, integ_comp_equiv τ hτ]

end GermGroupoid.JN.PartA
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
alias isAmenable_of_invariant_of_stabilizer := GermGroupoid.JN.PartA.isAmenable_of_invariant_of_stabilizer

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise
namespace GermGroupoid.JN.PartB
open FAmenHZ.Lib
/-!
# Part B: extensive amenability is hereditary

Restriction of an extensively amenable action to a subgroup, and the invariant mean on an orbit
`O = G v` (`v ∈ Y`) obtained by averaging the uniform measures on `E ∩ O` against the mean of the
definition.
-/
theorem isExtensivelyAmenableOn_subgroup {G X : Type*} [Group G] [MulAction G X] {Y : Set X}
    (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) (K : Subgroup G) :
    ThompsonAmenability.IsExtensivelyAmenableOn K X Y := by
  obtain ⟨m, hm, hY, h1, hinv, hfull⟩ := h
  exact ⟨m, hm, hY, h1, fun g S => hinv (g : G) S, hfull⟩

end GermGroupoid.JN.PartB
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
/-! ## Part B: extensive amenability is hereditary -/
alias isExtensivelyAmenableOn_subgroup := GermGroupoid.JN.PartB.isExtensivelyAmenableOn_subgroup

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise
namespace GermGroupoid.JN.PartB
open FAmenHZ.Lib
open Classical in
/-- The points of `E` lying in the orbit `O`. -/
noncomputable def inOrbit {G X : Type*} [Group G] [MulAction G X] (v : X) (E : Finset X) :
    Finset (MulAction.orbit G v) :=
  E.subtype (· ∈ MulAction.orbit G v)

open Classical in
/-- The proportion of `E ∩ O` lying in `A` (`0` when `E ∩ O = ∅`). -/
noncomputable def frac {G X : Type*} [Group G] [MulAction G X] (v : X)
    (A : Set (MulAction.orbit G v)) (E : Finset X) : ℝ :=
  (((inOrbit (G := G) v E).filter (· ∈ A)).card : ℝ) / ((inOrbit (G := G) v E).card : ℝ)

open Classical in
lemma card_filter_map {G X : Type*} [Group G] [MulAction G X] (v : X) (g : G)
    (A : Set (MulAction.orbit G v)) (E : Finset X) :
    ((inOrbit (G := G) v (E.map (MulAction.toPerm g⁻¹ : Equiv.Perm X).toEmbedding)).filter
        (· ∈ A)).card = ((inOrbit (G := G) v E).filter (· ∈ g • A)).card := by
  refine Finset.card_bij' (fun x _ => g • x) (fun x _ => g⁻¹ • x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [inOrbit, Finset.mem_filter, Finset.mem_subtype, Finset.mem_map_equiv] at hx ⊢
    refine ⟨?_, Set.smul_mem_smul_set hx.2⟩
    have := hx.1
    simpa [MulAction.orbit.coe_smul] using this
  · intro x hx
    simp only [inOrbit, Finset.mem_filter, Finset.mem_subtype, Finset.mem_map_equiv] at hx ⊢
    refine ⟨?_, ?_⟩
    · simpa [MulAction.orbit.coe_smul] using hx.1
    · exact (Set.mem_smul_set_iff_inv_smul_mem).1 hx.2
  · intro x _; simp
  · intro x _; simp

lemma frac_smul {G X : Type*} [Group G] [MulAction G X] (v : X) (g : G)
    (A : Set (MulAction.orbit G v)) (E : Finset X) :
    frac (G := G) v (g • A) E =
      frac (G := G) v A (E.map (MulAction.toPerm g⁻¹ : Equiv.Perm X).toEmbedding) := by
  classical
  unfold frac
  have h1 := card_filter_map (G := G) v g A E
  have h2 := card_filter_map (G := G) v g Set.univ E
  simp only [Set.mem_univ, Finset.filter_true, Set.smul_set_univ] at h2
  rw [h1, h2]

theorem exists_orbit_mean {G X : Type*} [Group G] [MulAction G X] {Y : Set X}
    (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) {v : X} (hv : v ∈ Y) :
    ∃ m : Set (MulAction.orbit G v) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧
      m Set.univ = 1 ∧ Garrido.IsInvariant G m := by
  classical
  obtain ⟨m, hm, -, h1, hinv, hfull⟩ := h
  have f0 : ∀ A E, 0 ≤ frac (G := G) v A E := fun A E => by unfold frac; positivity
  have f1 : ∀ A E, frac (G := G) v A E ≤ 1 := fun A E => by
    unfold frac
    exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_filter_le _ _) (by positivity)
  have fadd : ∀ s t : Set (MulAction.orbit G v), Disjoint s t →
      frac (G := G) v (s ∪ t) = frac (G := G) v s + frac (G := G) v t := by
    intro s t hst
    funext E
    simp only [frac, Pi.add_apply]
    rw [← add_div]
    congr 1
    rw [← Nat.cast_add, ← Finset.card_union_of_disjoint]
    · congr 2
      ext x
      simp [Finset.mem_filter, Finset.mem_union, Set.mem_union, and_or_left]
    · rw [Finset.disjoint_left]
      intro x hx hx'
      exact Set.disjoint_left.1 hst (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hx').2
  -- the null set where `E` misses `v`
  have hnull : m {E : Finset X | {v} ⊆ E}ᶜ = 0 :=
    PartB3.fam_compl_eq_zero hm h1 (hfull {v} (by simpa using hv))
  refine ⟨fun A => ENNReal.ofReal (integ m (frac (G := G) v A)), ⟨?_, ?_⟩, ?_, ?_⟩
  · have h0 : frac (G := G) v ∅ = (∅ : Set (Finset X)).indicator 1 := by
      funext E
      simp [frac]
    simp only
    rw [h0, integ_indicator hm h1, hm.1]
    simp
  · intro s t hst
    have hle : ∀ E, frac (G := G) v s E + frac (G := G) v t E ≤ 1 := fun E => by
      have := f1 (s ∪ t) E
      rwa [fadd s t hst] at this
    simp only
    rw [fadd s t hst, integ_add hm h1 (f0 s) (f0 t) hle,
      ENNReal.ofReal_add (integ_nonneg_le_one hm h1 (f0 s) (f1 s)).1
        (integ_nonneg_le_one hm h1 (f0 t) (f1 t)).1]
  · have hu : integ m (frac (G := G) v Set.univ) =
        integ m ((Set.univ : Set (Finset X)).indicator 1) := by
      apply integ_congr hm h1
      have hsub : {E | frac (G := G) v Set.univ E ≠ (Set.univ : Set (Finset X)).indicator 1 E}
          ⊆ {E : Finset X | {v} ⊆ E}ᶜ := by
        intro E hE hvE
        apply hE
        have hvE' : v ∈ E := by simpa using hvE
        have hne : (inOrbit (G := G) v E).card ≠ 0 := by
          rw [Finset.card_ne_zero]
          exact ⟨⟨v, MulAction.mem_orbit_self v⟩, by simp [inOrbit, hvE']⟩
        simp only [frac, Set.mem_univ, Finset.filter_true, Set.indicator_univ, Pi.one_apply]
        exact div_self (by exact_mod_cast hne)
      exact le_antisymm (hnull ▸ PartB3.fam_mono hm hsub) bot_le
    simp only
    rw [hu, integ_indicator hm h1, h1]
    simp
  · intro g A
    simp only
    congr 1
    let τ : Finset X ≃ Finset X := (MulAction.toPerm g⁻¹ : Equiv.Perm X).finsetCongr
    have hτ : ∀ T : Set (Finset X), m (τ '' T) = m T := fun T => hinv g⁻¹ T
    have hfun : frac (G := G) v (g • A) = frac (G := G) v A ∘ τ := by
      funext E
      exact frac_smul v g A E
    rw [hfun, integ_comp_equiv τ hτ]

end GermGroupoid.JN.PartB
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
alias exists_orbit_mean := GermGroupoid.JN.PartB.exists_orbit_mean

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise
namespace GermGroupoid.JN.PartC
/-- One step of de Cornulier's induction: if `K'` acts on the orbit of `v` with an invariant mean,
and the conjugate `k⁻¹ s k` of every stabilizer element `s` of `k • v` lies in an amenable `L`,
then `K'` is amenable. -/
theorem step {G X : Type*} [Group G] [MulAction G X] {Y : Set X}
    (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) {v : X} (hv : v ∈ Y)
    (K' L : Subgroup G) (hL : Garrido.IsAmenable L)
    (hmap : ∀ k ∈ K', ∀ s ∈ K', s • (k • v) = k • v → k⁻¹ * s * k ∈ L) :
    Garrido.IsAmenable K' := by
  obtain ⟨m, hm, hm1, hinv⟩ :=
    GermGroupoid.JN.exists_orbit_mean (GermGroupoid.JN.isExtensivelyAmenableOn_subgroup h K') hv
  refine GermGroupoid.JN.isAmenable_of_invariant_of_stabilizer m hm hm1 hinv ?_
  intro y
  obtain ⟨k, hk⟩ := y.2
  let f : MulAction.stabilizer K' y →* L :=
    { toFun := fun s => ⟨(k : G)⁻¹ * ((s : K') : G) * (k : G), by
        apply hmap _ k.2 _ (s : K').2
        have hs : (s : K') • y = y := s.2
        have hs' := congrArg Subtype.val hs
        have hk' : (k : G) • v = (y : X) := hk
        rw [hk']
        exact hs'⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  refine GermGroupoid.JN.isAmenable_of_injective f ?_ hL
  intro a b hab
  have := congrArg (fun z : L => (z : G)) hab
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at this
  exact Subtype.ext (Subtype.ext this)

theorem isAmenable_of_isAmenable_inf_fixingSubgroup {G X : Type*} [Group G] [MulAction G X]
    {Y : Set X} (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) (F : Finset X)
    (hF : (F : Set X) ⊆ Y) (K : Subgroup G)
    (hK : Garrido.IsAmenable (K ⊓ fixingSubgroup G (F : Set X) : Subgroup G)) :
    Garrido.IsAmenable K := by
  classical
  induction F using Finset.induction_on generalizing K with
  | empty =>
    have : (K ⊓ fixingSubgroup G ((∅ : Finset X) : Set X) : Subgroup G) = K := by
      ext g; simp
    rw [this] at hK; exact hK
  | insert v F' _ ih =>
    have hv : v ∈ Y := hF (by simp)
    have hF' : (F' : Set X) ⊆ Y := fun x hx => hF (by simp [hx])
    apply ih hF' K
    apply step h hv _ _ hK
    intro k hk s hs hsk
    simp only [Subgroup.mem_inf, mem_fixingSubgroup_iff] at hk hs ⊢
    refine ⟨K.mul_mem (K.mul_mem (K.inv_mem hk.1) hs.1) hk.1, ?_⟩
    intro w hw
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hw
    rcases hw with rfl | hw
    · rw [mul_smul, mul_smul, hsk, inv_smul_smul]
    · rw [mul_smul, mul_smul, hk.2 w hw, hs.2 w hw, inv_smul_eq_iff, hk.2 w hw]

end GermGroupoid.JN.PartC
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
/-! ## Part C: de Cornulier's induction over a finite set -/
alias isAmenable_of_isAmenable_inf_fixingSubgroup := GermGroupoid.JN.PartC.isAmenable_of_isAmenable_inf_fixingSubgroup

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartD
variable {X : Type*} [TopologicalSpace X]
/-!
# Part D: the germ filtration

Induction on the finite set `F`: the germ at the new point `y` gives a homomorphism
`K → GermGroup G y` (using `hfix`); its kernel is handled by the induction hypothesis and its image
is a subgroup of an amenable group.
-/
/-- The germ homomorphism at a point `y` fixed by every element of `K`. -/
def germHom (G : Subgroup (X ≃ₜ X)) (K : Subgroup G) (y : X)
    (hy : ∀ k ∈ K, ((k : G) : X ≃ₜ X) y = y) : K →* GermGroup G y :=
  (QuotientGroup.mk' (germKernel G y)).comp
    { toFun := fun k => ⟨(k : G), hy k k.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem isAmenable_of_germs_fixing (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
    (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x)) (h4 : Garrido.IsAmenable (fullGroup 𝓗))
    (K : Subgroup G) (F : Finset X) (hfix : ∀ k ∈ K, ∀ y ∈ F, ((k : G) : X ≃ₜ X) y = y)
    (hker : ∀ k ∈ K, (∀ y ∈ F, ∀ᶠ z in 𝓝 y, ((k : G) : X ≃ₜ X) z = z) →
      ((k : G) : X ≃ₜ X) ∈ fullGroup 𝓗) :
    Garrido.IsAmenable K := by
  classical
  induction F using Finset.induction_on generalizing K with
  | empty =>
    let f : K →* fullGroup 𝓗 :=
      { toFun := fun k => ⟨((k : G) : X ≃ₜ X), hker k k.2 (by simp)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine GermGroupoid.JN.isAmenable_of_injective f ?_ h4
    intro a b hab
    have : ((a : G) : X ≃ₜ X) = ((b : G) : X ≃ₜ X) :=
      congrArg (fun z : fullGroup 𝓗 => (z : X ≃ₜ X)) hab
    exact Subtype.ext (Subtype.ext this)
  | insert y F' hyF ih =>
    have hy : ∀ k ∈ K, ((k : G) : X ≃ₜ X) y = y := fun k hk => hfix k hk y (by simp)
    set φ := germHom G K y hy
    -- the kernel, as a subgroup of `G`
    let K' : Subgroup G := φ.ker.map K.subtype
    have memK' : ∀ g : G, g ∈ K' ↔ ∃ hg : g ∈ K, (⟨g, hg⟩ : K) ∈ φ.ker := by
      intro g
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k.2, hk⟩
      · rintro ⟨hg, hk⟩
        exact ⟨_, hk, rfl⟩
    have memKer : ∀ k : K, k ∈ φ.ker ↔ ∀ᶠ z in 𝓝 y, ((k : G) : X ≃ₜ X) z = z := by
      intro k
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk _ : GermGroup G y) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      rfl
    have hK' : Garrido.IsAmenable K' := by
      refine ih K' (fun k hk z hz => ?_) (fun k hk hev => ?_)
      · obtain ⟨hkK, -⟩ := (memK' k).1 hk
        exact hfix k hkK z (by simp [hz])
      · obtain ⟨hkK, hker'⟩ := (memK' k).1 hk
        refine hker k hkK fun z hz => ?_
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact (memKer _).1 hker'
        · exact hev z hz
    have hker_am : Garrido.IsAmenable φ.ker :=
      GermGroupoid.JN.isAmenable_of_mulEquiv
        (Subgroup.equivMapOfInjective φ.ker K.subtype K.subtype_injective).symm hK'
    have hQ : Garrido.IsAmenable (K ⧸ φ.ker) :=
      GermGroupoid.JN.isAmenable_of_mulEquiv
        (QuotientGroup.quotientKerEquivRange φ).symm
        (Garrido.isAmenable_subgroup (h2 y) φ.range)
    exact Garrido.isAmenable_of_isAmenable_of_isAmenable_quotient φ.ker hker_am hQ

end GermGroupoid.JN.PartD
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
/-! ## Part D: the germ filtration -/
alias isAmenable_of_germs_fixing := GermGroupoid.JN.PartD.isAmenable_of_germs_fixing

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartE
open GermGroupoid GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
/-!
# Part E: germ calculus and the lamp space
-/
theorem germMem_one (𝓗 : StructureGroupoid X) (x : X) : GermMem 𝓗 1 x :=
  ⟨OpenPartialHomeomorph.refl X, 𝓗.id_mem, by simp, Filter.Eventually.of_forall fun _ => rfl⟩

end GermGroupoid.JN.PartE
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
/-! ## Part E: germ calculus and the lamp space -/

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartE
open GermGroupoid GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
theorem germMem_mul {𝓗 : StructureGroupoid X} {f g : X ≃ₜ X} {x : X}
    (hf : GermMem 𝓗 f (g x)) (hg : GermMem 𝓗 g x) : GermMem 𝓗 (f * g) x := by
  obtain ⟨e₂, he₂, hx₂, hg₂⟩ := hg
  obtain ⟨e₁, he₁, hx₁, hf₁⟩ := hf
  have hgx : g x = e₂ x := hg₂.self_of_nhds
  refine ⟨e₂.trans e₁, 𝓗.trans he₂ he₁, ?_, ?_⟩
  · simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hx₂, hgx ▸ hx₁⟩
  · have hcont : Filter.Tendsto g (𝓝 x) (𝓝 (g x)) := g.continuous.tendsto x
    filter_upwards [hg₂, hcont.eventually hf₁] with y hy hfy
    change f (g y) = e₁ (e₂ y)
    rw [hfy, hy]

end GermGroupoid.JN.PartE
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartE
open GermGroupoid GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
theorem germMem_inv {𝓗 : StructureGroupoid X} {f : X ≃ₜ X} {x : X}
    (hf : GermMem 𝓗 f x) : GermMem 𝓗 f⁻¹ (f x) := by
  obtain ⟨e, he, hxe, hfe⟩ := hf
  have hfx : f x = e x := hfe.self_of_nhds
  refine ⟨e.symm, 𝓗.symm he, ?_, ?_⟩
  · simp only [OpenPartialHomeomorph.symm_source]
    rw [hfx]
    exact e.map_source hxe
  · have hU : {y | f y = e y} ∩ e.source ∈ 𝓝 x :=
      Filter.inter_mem hfe (e.open_source.mem_nhds hxe)
    have hV : f '' ({y | f y = e y} ∩ e.source) ∈ 𝓝 (f x) :=
      f.isOpenMap.image_mem_nhds hU
    filter_upwards [hV] with z hz
    obtain ⟨y, ⟨hy, hys⟩, rfl⟩ := hz
    show f.symm (f y) = e.symm (f y)
    rw [Homeomorph.symm_apply_apply, show f y = e y from hy, e.left_inv hys]

end GermGroupoid.JN.PartE
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartE
open GermGroupoid GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
theorem germMem_of_eventually_id {𝓗 : StructureGroupoid X} {f : X ≃ₜ X} {x : X}
    (hf : ∀ᶠ y in 𝓝 x, f y = y) : GermMem 𝓗 f x :=
  ⟨OpenPartialHomeomorph.refl X, 𝓗.id_mem, by simp, hf⟩

end GermGroupoid.JN.PartE
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
alias germMem_of_eventually_id := GermGroupoid.JN.PartE.germMem_of_eventually_id

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
/-- Two germs `(g, y)` and `(g', y')` of `G` (from `y` to `g y`) are equivalent when they have the
same target and `(g', y')⁻¹ (g, y)`, the germ of `g'⁻¹ g` at `y`, lies in `𝓗`. -/
def lampRel (p q : G × X) : Prop :=
  ((p.1 : G) : X ≃ₜ X) p.2 = ((q.1 : G) : X ≃ₜ X) q.2 ∧
    GermMem 𝓗 (((q.1 : G) : X ≃ₜ X)⁻¹ * ((p.1 : G) : X ≃ₜ X)) p.2

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartE
open GermGroupoid GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
theorem lampRel_equivalence : Equivalence (lampRel G 𝓗) := by
  refine ⟨fun p => ⟨rfl, ?_⟩, fun {p q} hpq => ⟨hpq.1.symm, ?_⟩, fun {p q r} hpq hqr =>
    ⟨hpq.1.trans hqr.1, ?_⟩⟩
  · show GermMem 𝓗 (((p.1 : G) : X ≃ₜ X)⁻¹ * ((p.1 : G) : X ≃ₜ X)) p.2
    rw [inv_mul_cancel]; exact germMem_one 𝓗 _
  · have h := germMem_inv hpq.2
    have e : (((q.1 : G) : X ≃ₜ X)⁻¹ * ((p.1 : G) : X ≃ₜ X)) p.2 = q.2 := by
      change ((q.1 : G) : X ≃ₜ X).symm (((p.1 : G) : X ≃ₜ X) p.2) = _
      rw [hpq.1]; exact Homeomorph.symm_apply_apply _ _
    rw [e] at h
    convert h using 1
    group
  · have e : (((q.1 : G) : X ≃ₜ X)⁻¹ * ((p.1 : G) : X ≃ₜ X)) p.2 = q.2 := by
      change ((q.1 : G) : X ≃ₜ X).symm (((p.1 : G) : X ≃ₜ X) p.2) = _
      rw [hpq.1]; exact Homeomorph.symm_apply_apply _ _
    have h := germMem_mul (e ▸ hqr.2) hpq.2
    convert h using 1
    group

end GermGroupoid.JN.PartE
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
alias lampRel_equivalence := GermGroupoid.JN.PartE.lampRel_equivalence

/-- The setoid of `lampRel`. -/
def lampSetoid : Setoid (G × X) := ⟨lampRel G 𝓗, lampRel_equivalence G 𝓗⟩

/-- The lamp space: germs of `G` modulo right multiplication by germs in `𝓗`. -/
def Lamp : Type _ := Quotient (lampSetoid G 𝓗)

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartE
open GermGroupoid GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
theorem lampRel_smul (h : G) {p q : G × X} (hpq : lampRel G 𝓗 p q) :
    lampRel G 𝓗 (h * p.1, p.2) (h * q.1, q.2) := by
  refine ⟨?_, ?_⟩
  · change ((h : G) : X ≃ₜ X) (((p.1 : G) : X ≃ₜ X) p.2) =
      ((h : G) : X ≃ₜ X) (((q.1 : G) : X ≃ₜ X) q.2)
    rw [hpq.1]
  · convert hpq.2 using 1
    simp only [Subgroup.coe_mul]
    group

end GermGroupoid.JN.PartE
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
alias lampRel_smul := GermGroupoid.JN.PartE.lampRel_smul

noncomputable instance lampAction : MulAction G (Lamp G 𝓗) where
  smul h := Quotient.map (fun p : G × X => (h * p.1, p.2)) fun _ _ hpq => lampRel_smul G 𝓗 h hpq
  one_smul z := by
    induction z using Quotient.inductionOn with
    | h p => exact congrArg (Quotient.mk _) (by simp)
  mul_smul a b z := by
    induction z using Quotient.inductionOn with
    | h p => exact congrArg (Quotient.mk _) (by simp [mul_assoc])

/-- The class of the identity germ at `x`. -/
def base (x : X) : Lamp G 𝓗 := Quotient.mk (lampSetoid G 𝓗) (1, x)

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartE
open GermGroupoid GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
theorem smul_base_eq_iff (h : G) (x : X) :
    h • base G 𝓗 x = base G 𝓗 (((h : G) : X ≃ₜ X) x) ↔ GermMem 𝓗 ((h : G) : X ≃ₜ X) x := by
  change Quotient.mk (lampSetoid G 𝓗) (h * 1, x) = Quotient.mk (lampSetoid G 𝓗) (1, _) ↔ _
  rw [Quotient.eq]
  change lampRel G 𝓗 _ _ ↔ _
  simp [lampRel]

end GermGroupoid.JN.PartE
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
alias smul_base_eq_iff := GermGroupoid.JN.PartE.smul_base_eq_iff

/-- Condition (i) of the theorem. -/
abbrev CondOne : Prop := ∀ g ∈ G, {x | ¬ GermMem 𝓗 g x}.Finite

/-- The sections `ψ : X → Lamp` equal to `base` off a finite set. -/
def FinSec (_h1 : CondOne G 𝓗) : Type _ :=
  {ψ : X → Lamp G 𝓗 // {x | ψ x ≠ base G 𝓗 x}.Finite}

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartE
open GermGroupoid GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
theorem finSec_smul_finite (h1 : CondOne G 𝓗) (h : G) (ψ : X → Lamp G 𝓗)
    (hψ : {x | ψ x ≠ base G 𝓗 x}.Finite) :
    {x | h • ψ ((h⁻¹ : G) • x) ≠ base G 𝓗 x}.Finite := by
  refine ((hψ.union (h1 _ h.2)).image ((h : G) : X ≃ₜ X)).subset ?_
  intro x hx
  refine ⟨(h⁻¹ : G) • x, ?_, ?_⟩
  · by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    apply hx
    rw [hc.1, (smul_base_eq_iff G 𝓗 h _).2 hc.2]
    congr 1
    exact smul_inv_smul h x
  · exact smul_inv_smul h x

end GermGroupoid.JN.PartE
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
alias finSec_smul_finite := GermGroupoid.JN.PartE.finSec_smul_finite

noncomputable instance finSecAction (h1 : CondOne G 𝓗) : MulAction G (FinSec G 𝓗 h1) where
  smul h ψ := ⟨fun x => h • ψ.1 ((h⁻¹ : G) • x), finSec_smul_finite G 𝓗 h1 h ψ.1 ψ.2⟩
  one_smul ψ := Subtype.ext (funext fun x =>
    show (1 : G) • ψ.1 ((1 : G)⁻¹ • x) = ψ.1 x by simp)
  mul_smul a b ψ := Subtype.ext (funext fun x =>
    show (a * b) • ψ.1 ((a * b)⁻¹ • x) = a • (b • ψ.1 (b⁻¹ • (a⁻¹ • x))) by
      rw [mul_inv_rev, mul_smul, mul_smul])

theorem finSec_smul_apply (h1 : CondOne G 𝓗) (h : G) (ψ : FinSec G 𝓗 h1) (x : X) :
    (h • ψ).1 x = h • ψ.1 ((h⁻¹ : G) • x) := rfl

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartF
open GermGroupoid GermGroupoid.JN FAmenHZ.Lib.PartA
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
/-!
# Part F: fiber means from amenable germ groups

For each `r : X`, a left-invariant mean `m_r` on the germ group `GermGroup G r` is pushed to the
lamp space along `γ ↦ γ ⋆ base r` (`[k] ↦ ⟦(k, r)⟧`); the resulting mean `λ_r` is invariant under
the stabilizer of `r`. It is transported along the orbit by the coordinates of Lib's `PartA`:
`λ_x(S) = λ_{rep x}((coord x)⁻¹ • S)`.
-/
/-- `γ ⋆ base r`: the lamp `⟦(k, r)⟧` for a representative `k` of the germ `γ` at `r`. -/
noncomputable def germLamp (r : X) : GermGroup G r → Lamp G 𝓗 :=
  Quotient.lift (fun k : MulAction.stabilizer G r => Quotient.mk (lampSetoid G 𝓗) ((k : G), r))
    (by
      intro a b hab
      apply Quotient.sound
      replace hab : a⁻¹ * b ∈ germKernel G r := QuotientGroup.leftRel_apply.1 hab
      refine ⟨?_, ?_⟩
      · change ((a : G) : X ≃ₜ X) r = ((b : G) : X ≃ₜ X) r
        have ha : ((a : G) : X ≃ₜ X) r = r := a.2
        have hb : ((b : G) : X ≃ₜ X) r = r := b.2
        rw [ha, hb]
      · apply germMem_of_eventually_id
        have hk' : ∀ᶠ y in 𝓝 r,
            (((a⁻¹ * b : MulAction.stabilizer G r)⁻¹ : MulAction.stabilizer G r) :
              X ≃ₜ X) y = y :=
          (germKernel G r).inv_mem hab
        filter_upwards [hk'] with y hy
        convert hy using 2
        simp)

theorem germLamp_mul (r : X) (s : MulAction.stabilizer G r) (γ : GermGroup G r) :
    germLamp G 𝓗 r ((QuotientGroup.mk s : GermGroup G r) * γ) = (s : G) • germLamp G 𝓗 r γ := by
  induction γ using QuotientGroup.induction_on with
  | H k => rfl

/-- The chosen invariant mean on the germ group at `r`. -/
noncomputable def germMean (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x)) (r : X) :
    Set (GermGroup G r) → ℝ≥0∞ :=
  (h2 r).choose

/-- The fiber mean at `r`, invariant under the stabilizer of `r`. -/
noncomputable def lamR (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x)) (r : X)
    (S : Set (Lamp G 𝓗)) : ℝ≥0∞ :=
  germMean G h2 r (germLamp G 𝓗 r ⁻¹' S)

theorem lamR_fa (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x)) (r : X) :
    Garrido.IsFinitelyAdditiveMeasure (lamR G 𝓗 h2 r) ∧ lamR G 𝓗 h2 r Set.univ = 1 := by
  obtain ⟨⟨h0, hadd⟩, h1, -⟩ := (h2 r).choose_spec
  refine ⟨⟨?_, fun s t hst => ?_⟩, ?_⟩
  · exact h0
  · exact hadd _ _ (hst.preimage _)
  · exact h1

theorem lamR_inv (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x)) (r : X)
    (s : MulAction.stabilizer G r) (S : Set (Lamp G 𝓗)) :
    lamR G 𝓗 h2 r ((s : G) • S) = lamR G 𝓗 h2 r S := by
  obtain ⟨-, -, hinv⟩ := (h2 r).choose_spec
  have e : germLamp G 𝓗 r ⁻¹' ((s : G) • S) =
      (QuotientGroup.mk s : GermGroup G r) • (germLamp G 𝓗 r ⁻¹' S) := by
    ext γ
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem,
      Set.mem_preimage, smul_eq_mul, ← QuotientGroup.mk_inv, germLamp_mul]
    rfl
  unfold lamR
  rw [e]
  exact hinv _ _

theorem exists_fiber_means (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x)) :
    ∃ lam : X → Set (Lamp G 𝓗) → ℝ≥0∞,
      (∀ x, Garrido.IsFinitelyAdditiveMeasure (lam x) ∧ lam x Set.univ = 1) ∧
      ∀ (h : G) (x : X) (S : Set (Lamp G 𝓗)), lam ((h : G) • x) (h • S) = lam x S := by
  refine ⟨fun x S => lamR G 𝓗 h2 (rep G x) ((coord G x)⁻¹ • S), fun x => ?_, ?_⟩
  · obtain ⟨⟨h0, hadd⟩, h1⟩ := lamR_fa G 𝓗 h2 (rep G x)
    refine ⟨⟨?_, fun s t hst => ?_⟩, ?_⟩
    · simp only [Set.smul_set_empty]; exact h0
    · simp only [Set.smul_set_union]
      exact hadd _ _ (Set.disjoint_smul_set.2 hst)
    · simp only [Set.smul_set_univ]; exact h1
  · intro h x S
    simp only
    have hr : rep G (h • x) = rep G x := rep_smul h x
    -- `s = coord(hx)⁻¹ * h * coord x` fixes `rep x`
    have key : ∀ (r : X) (hr' : rep G (h • x) = r),
        lamR G 𝓗 h2 r ((coord G (h • x))⁻¹ • h • S) =
          lamR G 𝓗 h2 r ((coord G x)⁻¹ • S) := by
      intro r hr'
      have hrx : rep G x = r := hr ▸ hr'
      let s : G := (coord G (h • x))⁻¹ * h * coord G x
      have hs : s ∈ MulAction.stabilizer G r := by
        rw [MulAction.mem_stabilizer_iff]
        have e1 := coord_smul_rep (G := G) (h • x)
        have e2 := coord_smul_rep (G := G) x
        rw [hr'] at e1
        rw [hrx] at e2
        simp only [s, mul_smul, e2]
        rw [inv_smul_eq_iff]
        exact e1.symm
      have := lamR_inv G 𝓗 h2 r ⟨s, hs⟩ ((coord G x)⁻¹ • S)
      rw [← this, smul_smul, smul_smul]
      congr 2
      simp only [s]
      group
    rw [hr]
    exact key _ hr

end GermGroupoid.JN.PartF
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
/-! ## Part F: fiber means from amenable germ groups -/
alias exists_fiber_means := GermGroupoid.JN.PartF.exists_fiber_means

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
open FAmenHZ.Lib
namespace GermGroupoid.JN.PartG
variable {α β : Type*}
/-!
# Part G: the invariant mean on `FinSec`

Iterated fiber means `iter l σ` along a list `l` of points (each step integrates the fiber mean at
the head of the list), symmetrised over all orderings of a finite set `E` (`symIter`), then
integrated against the extensive-amenability mean on finite subsets.
-/
/-! ### Mixtures of finitely additive probabilities -/
lemma integ_one {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    (h1 : m Set.univ = 1) : integ m (fun _ => (1 : ℝ)) = 1 := by
  have := integ_indicator hm h1 Set.univ
  rw [Set.indicator_univ, h1, ENNReal.toReal_one] at this
  exact this

lemma integ_comp_of_preimage {γ : Type*} {m : Set α → ℝ≥0∞} {m' : Set γ → ℝ≥0∞} (τ : γ → α)
    (hτ : ∀ T : Set α, m' (τ ⁻¹' T) = m T) (f : α → ℝ) : integ m' (f ∘ τ) = integ m f := by
  have heq : ∀ c : ℝ, m' {a | c ≤ (f ∘ τ) a} = m {a | c ≤ f a} := fun c => hτ {a | c ≤ f a}
  unfold integ layerSum
  simp only [heq]

/-- The mixture `S ↦ ∫ ν_a(S) dm(a)`. -/
noncomputable def mix (m : Set α → ℝ≥0∞) (ν : α → Set β → ℝ≥0∞) (S : Set β) : ℝ≥0∞ :=
  ENNReal.ofReal (integ m (fun a => (ν a S).toReal))

lemma mix_spec {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    (h1 : m Set.univ = 1) {ν : α → Set β → ℝ≥0∞}
    (hν : ∀ a, Garrido.IsFinitelyAdditiveMeasure (ν a) ∧ ν a Set.univ = 1) :
    Garrido.IsFinitelyAdditiveMeasure (mix m ν) ∧ mix m ν Set.univ = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h0 : (fun a => (ν a ∅).toReal) = (∅ : Set α).indicator 1 := by
      funext a
      rw [(hν a).1.1, Set.indicator_empty]
      rfl
    unfold mix
    rw [h0, integ_indicator hm h1, hm.1]
    simp
  · intro s t hst
    have hne : ∀ a (u : Set β), ν a u ≠ ∞ := fun a u =>
      PartB1.fa_ne_top (hν a).1 (hν a).2 u
    have hadd : ∀ a, ν a (s ∪ t) = ν a s + ν a t := fun a => (hν a).1.2 s t hst
    have hfun : (fun a => (ν a (s ∪ t)).toReal)
        = (fun a => (ν a s).toReal) + (fun a => (ν a t).toReal) := by
      funext a
      rw [hadd a, Pi.add_apply, ENNReal.toReal_add (hne a s) (hne a t)]
    have hle : ∀ a, (ν a s).toReal + (ν a t).toReal ≤ 1 := by
      intro a
      rw [← ENNReal.toReal_add (hne a s) (hne a t), ← hadd a]
      exact PartB1.fa_toReal_le_one (hν a).1 (hν a).2 _
    have hf0 : ∀ a, 0 ≤ (ν a s).toReal := fun a => ENNReal.toReal_nonneg
    have hg0 : ∀ a, 0 ≤ (ν a t).toReal := fun a => ENNReal.toReal_nonneg
    have hf1 : ∀ a, (ν a s).toReal ≤ 1 := fun a =>
      le_trans (le_add_of_nonneg_right (hg0 a)) (hle a)
    have hg1 : ∀ a, (ν a t).toReal ≤ 1 := fun a =>
      le_trans (le_add_of_nonneg_left (hf0 a)) (hle a)
    unfold mix
    rw [hfun, integ_add hm h1 hf0 hg0 hle,
      ENNReal.ofReal_add (integ_nonneg_le_one hm h1 hf0 hf1).1
        (integ_nonneg_le_one hm h1 hg0 hg1).1]
  · have hu : (fun a => (ν a Set.univ).toReal) = fun _ => (1 : ℝ) := by
      funext a
      rw [(hν a).2, ENNReal.toReal_one]
    unfold mix
    rw [hu, integ_one hm h1, ENNReal.ofReal_one]

lemma mix_eq_one {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    (h1 : m Set.univ = 1) {ν : α → Set β → ℝ≥0∞} {S : Set β} (hS : ∀ a, ν a S = 1) :
    mix m ν S = 1 := by
  have hu : (fun a => (ν a S).toReal) = fun _ => (1 : ℝ) := by
    funext a
    rw [hS a, ENNReal.toReal_one]
  unfold mix
  rw [hu, integ_one hm h1, ENNReal.ofReal_one]

end GermGroupoid.JN.PartG
end

section
open scoped ENNReal Pointwise Topology
open FAmenHZ.Lib
namespace GermGroupoid.JN.PartG
open Classical
variable {X L : Type*} (lam : X → Set L → ℝ≥0∞)
/-! ### Iterated means along a list -/
/-- `iter [] σ S = 𝟙_S(σ)`, `iter (x :: l) σ S = ∫ iter l (σ[x ↦ z]) S d(lam x)(z)`. -/
noncomputable def iter : List X → (X → L) → Set (X → L) → ℝ≥0∞
  | [], σ, S => S.indicator (fun _ => (1 : ℝ≥0∞)) σ
  | x :: l, σ, S => mix (lam x) (fun z => iter l (Function.update σ x z)) S

lemma iter_nil (σ : X → L) (S : Set (X → L)) :
    iter lam [] σ S = S.indicator (fun _ => (1 : ℝ≥0∞)) σ := rfl

lemma iter_cons (x : X) (l : List X) (σ : X → L) :
    iter lam (x :: l) σ = mix (lam x) (fun z => iter lam l (Function.update σ x z)) := rfl

end GermGroupoid.JN.PartG
end

section
open scoped ENNReal Pointwise Topology
open FAmenHZ.Lib
namespace GermGroupoid.JN.PartG
open Classical
variable {X L : Type*} (lam : X → Set L → ℝ≥0∞)
variable {lam}
lemma iter_spec (hlam : ∀ x, Garrido.IsFinitelyAdditiveMeasure (lam x) ∧ lam x Set.univ = 1)
    (l : List X) : ∀ σ : X → L,
    Garrido.IsFinitelyAdditiveMeasure (iter lam l σ) ∧ iter lam l σ Set.univ = 1 := by
  induction l with
  | nil =>
    intro σ
    refine ⟨⟨by simp [iter_nil], fun s t hst => ?_⟩, by simp [iter_nil]⟩
    simp only [iter_nil]
    rw [Set.indicator_union_of_disjoint hst]
  | cons x l ih =>
    intro σ
    rw [iter_cons]
    exact mix_spec (hlam x).1 (hlam x).2 fun z => ih _

lemma iter_eq_one (hlam : ∀ x, Garrido.IsFinitelyAdditiveMeasure (lam x) ∧ lam x Set.univ = 1)
    (l : List X) : ∀ (σ : X → L) (S : Set (X → L)),
    (∀ τ : X → L, (∀ y, y ∉ l → τ y = σ y) → τ ∈ S) → iter lam l σ S = 1 := by
  induction l with
  | nil =>
    intro σ S hS
    rw [iter_nil, Set.indicator_of_mem (hS σ fun _ _ => rfl)]
  | cons x l ih =>
    intro σ S hS
    rw [iter_cons]
    refine mix_eq_one (hlam x).1 (hlam x).2 fun z => ih _ S fun τ hτ => hS τ fun y hy => ?_
    have hyx : y ≠ x := fun h => hy (h ▸ List.mem_cons_self)
    have hyl : y ∉ l := fun h => hy (List.mem_cons_of_mem x h)
    rw [hτ y hyl, Function.update_of_ne hyx]

lemma iter_local (l : List X) : ∀ (σ σ' : X → L) (S : Set (X → L)),
    (∀ y, y ∉ l → σ y = σ' y) → iter lam l σ S = iter lam l σ' S := by
  induction l with
  | nil =>
    intro σ σ' S h
    have : σ = σ' := funext fun y => h y List.not_mem_nil
    rw [this]
  | cons x l ih =>
    intro σ σ' S h
    rw [iter_cons, iter_cons]
    unfold mix
    congr 2
    funext z
    show (iter lam l (Function.update σ x z) S).toReal
      = (iter lam l (Function.update σ' x z) S).toReal
    rw [ih _ (Function.update σ' x z) S]
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp
    · rw [Function.update_of_ne hyx, Function.update_of_ne hyx]
      exact h y fun hm => (List.mem_cons.1 hm).elim hyx hy

end GermGroupoid.JN.PartG
end

section
open scoped ENNReal Pointwise Topology
open FAmenHZ.Lib
namespace GermGroupoid.JN.PartG
open Classical
variable {X L : Type*} (lam : X → Set L → ℝ≥0∞)
variable {lam}
variable {K : Type*} [Group K] [MulAction K X] [MulAction K L]
/-! ### Equivariance -/
/-- `(h ⋆ σ) x = h • σ (h⁻¹ • x)`. -/
def star (h : K) (σ : X → L) : X → L := fun x => h • σ (h⁻¹ • x)

lemma star_inv_star (h : K) (σ : X → L) : star h⁻¹ (star h σ) = σ := by
  funext x
  simp [star]

lemma star_injective (h : K) : Function.Injective (star (X := X) (L := L) h) := by
  intro a b hab
  rw [← star_inv_star h a, hab, star_inv_star]

lemma update_star (h : K) (σ : X → L) (x : X) (z : L) :
    Function.update (star h σ) (h • x) z = star h (Function.update σ x (h⁻¹ • z)) := by
  funext y
  by_cases hy : y = h • x
  · subst hy
    simp [star]
  · have hne : h⁻¹ • y ≠ x := fun e => hy (by rw [← e, smul_inv_smul])
    simp only [star, Function.update_of_ne hy, Function.update_of_ne hne]

lemma iter_star (hlaminv : ∀ (h : K) (x : X) (T : Set L), lam (h • x) (h • T) = lam x T)
    (h : K) (l : List X) : ∀ (σ : X → L) (S : Set (X → L)),
    iter lam (l.map (fun x => h • x)) (star h σ) (star h '' S) = iter lam l σ S := by
  induction l with
  | nil =>
    intro σ S
    simp only [List.map_nil, iter_nil, Set.indicator_apply, (star_injective h).mem_set_image]
  | cons x l ih =>
    intro σ S
    rw [List.map_cons, iter_cons, iter_cons]
    unfold mix
    congr 1
    have hfun : (fun z => (iter lam (l.map (fun x => h • x))
          (Function.update (star h σ) (h • x) z) (star h '' S)).toReal)
        = (fun z => (iter lam l (Function.update σ x z) S).toReal) ∘ (fun z => h⁻¹ • z) := by
      funext z
      simp only [Function.comp, update_star, ih]
    rw [hfun]
    exact integ_comp_of_preimage _ (fun T => by rw [Set.preimage_smul_inv]; exact hlaminv h x T) _

/-! ### Symmetrisation over the orderings of a finite set -/
lemma lists_map {α β : Type*} (f : α → β) (s : Multiset α) :
    (s.map f).lists = s.lists.map (List.map f) := by
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, Multiset.coe_toList s⟩
  rw [Multiset.map_coe, Multiset.lists_coe, Multiset.lists_coe, Multiset.map_coe,
    List.map_permutations]

lemma lists_card_ne_zero (E : Finset X) : Multiset.card E.val.lists ≠ 0 := by
  rw [Ne, Multiset.card_eq_zero]
  intro h
  have hm : E.val.toList ∈ E.val.lists := by
    rw [Multiset.mem_lists_iff]
    exact (Multiset.coe_toList E.val).symm
  rw [h] at hm
  exact Multiset.notMem_zero _ hm

lemma avg_const {γ : Type*} (s : Multiset γ) (hs : Multiset.card s ≠ 0) (f : γ → ℝ≥0∞) (c : ℝ≥0∞)
    (hf : ∀ a ∈ s, f a = c) : ((Multiset.card s : ℕ) : ℝ≥0∞)⁻¹ * (s.map f).sum = c := by
  rw [Multiset.map_congr rfl hf, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hs) (ENNReal.natCast_ne_top _),
    one_mul]

variable (lam) in
/-- The average of `iter l σ₀` over all orderings `l` of `E`. -/
noncomputable def symIter (σ₀ : X → L) (E : Finset X) (S : Set (X → L)) : ℝ≥0∞ :=
  ((Multiset.card E.val.lists : ℕ) : ℝ≥0∞)⁻¹ * (E.val.lists.map (fun l => iter lam l σ₀ S)).sum

lemma symIter_eq_one (σ₀ : X → L) (E : Finset X) (S : Set (X → L))
    (hS : ∀ l ∈ E.val.lists, iter lam l σ₀ S = 1) : symIter lam σ₀ E S = 1 :=
  avg_const _ (lists_card_ne_zero E) _ _ hS

lemma symIter_spec (hlam : ∀ x, Garrido.IsFinitelyAdditiveMeasure (lam x) ∧ lam x Set.univ = 1)
    (σ₀ : X → L) (E : Finset X) :
    Garrido.IsFinitelyAdditiveMeasure (symIter lam σ₀ E) ∧ symIter lam σ₀ E Set.univ = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact avg_const _ (lists_card_ne_zero E) _ _ fun l _ => (iter_spec hlam l σ₀).1.1
  · intro s t hst
    unfold symIter
    rw [Multiset.map_congr rfl fun l _ => (iter_spec hlam l σ₀).1.2 s t hst,
      Multiset.sum_map_add, mul_add]
  · exact symIter_eq_one σ₀ E _ fun l _ => (iter_spec hlam l σ₀).2

lemma symIter_star (hlaminv : ∀ (h : K) (x : X) (T : Set L), lam (h • x) (h • T) = lam x T)
    (σ₀ : X → L) (h : K) (E : Finset X) (T : Set (X → L))
    (hloc : ∀ x, x ∉ E → h • σ₀ x = σ₀ (h • x)) :
    symIter lam σ₀ (E.map (MulAction.toPerm h : Equiv.Perm X).toEmbedding) (star h '' T)
      = symIter lam σ₀ E T := by
  unfold symIter
  rw [Finset.map_val, lists_map, Multiset.card_map, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun l hl => ?_
  show iter lam (l.map (fun x => h • x)) σ₀ (star h '' T) = iter lam l σ₀ T
  have hlE : ∀ x, x ∈ l ↔ x ∈ E := by
    intro x
    rw [Multiset.mem_lists_iff] at hl
    rw [← Finset.mem_val, hl]
    rfl
  rw [iter_local _ σ₀ (star h σ₀) _ ?_, iter_star hlaminv]
  intro y hy
  have hy' : h⁻¹ • y ∉ E := by
    rw [← hlE]
    intro hm
    exact hy (List.mem_map.2 ⟨_, hm, smul_inv_smul h y⟩)
  simp only [star]
  rw [hloc _ hy', smul_inv_smul]

end GermGroupoid.JN.PartG
end

section
open scoped ENNReal Pointwise Topology
open FAmenHZ.Lib
namespace GermGroupoid.JN.PartG
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
/-! ### The mean on `FinSec` -/
theorem exists_finSec_mean (h1 : CondOne G 𝓗)
    (lam : X → Set (Lamp G 𝓗) → ℝ≥0∞)
    (hlam : ∀ x, Garrido.IsFinitelyAdditiveMeasure (lam x) ∧ lam x Set.univ = 1)
    (hlaminv : ∀ (h : G) (x : X) (S : Set (Lamp G 𝓗)), lam ((h : G) • x) (h • S) = lam x S)
    (h3 : ThompsonAmenability.IsExtensivelyAmenableOn G X Set.univ) :
    ∃ m : Set (FinSec G 𝓗 h1) → ℝ≥0∞, Garrido.IsFinitelyAdditiveMeasure m ∧
      m Set.univ = 1 ∧ Garrido.IsInvariant G m := by
  classical
  obtain ⟨μ, hμ, -, hμ1, hμinv, hfull⟩ := h3
  let v : FinSec G 𝓗 h1 → (X → Lamp G 𝓗) := fun ψ => ψ.1
  have hv : Function.Injective v := fun a b hab => Subtype.ext hab
  let ν : Finset X → Set (FinSec G 𝓗 h1) → ℝ≥0∞ :=
    fun E T => symIter lam (base G 𝓗) E (v '' T)
  have hν : ∀ E, Garrido.IsFinitelyAdditiveMeasure (ν E) ∧ ν E Set.univ = 1 := by
    intro E
    obtain ⟨⟨h0, hadd⟩, -⟩ := symIter_spec hlam (base G 𝓗) E
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show symIter lam (base G 𝓗) E (v '' ∅) = 0
      rw [Set.image_empty]
      exact h0
    · intro s t hst
      show symIter lam (base G 𝓗) E (v '' (s ∪ t)) = _
      rw [Set.image_union]
      exact hadd _ _ ((Set.disjoint_image_iff hv).2 hst)
    · refine symIter_eq_one _ E _ fun l _ => iter_eq_one hlam l _ _ fun τ hτ => ?_
      refine ⟨⟨τ, (List.finite_toSet l).subset fun y hy => ?_⟩, Set.mem_univ _, rfl⟩
      by_contra hyl
      exact hy (hτ y hyl)
  refine ⟨mix μ ν, (mix_spec hμ hμ1 hν).1, (mix_spec hμ hμ1 hν).2, ?_⟩
  intro g S
  have himg : v '' (g • S) = star g '' (v '' S) := by
    ext σ
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, hφ, rfl⟩
      obtain ⟨ψ, hψ, rfl⟩ := Set.mem_smul_set.1 hφ
      exact ⟨ψ.1, ⟨ψ, hψ, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      exact ⟨g • ψ, Set.smul_mem_smul_set hψ, rfl⟩
  unfold mix
  congr 1
  let τ : Finset X ≃ Finset X := (MulAction.toPerm g : Equiv.Perm X).finsetCongr
  have hτ : ∀ T : Set (Finset X), μ (τ '' T) = μ T := fun T => hμinv g T
  rw [← integ_comp_equiv τ hτ (fun E => (ν E (g • S)).toReal)]
  apply integ_congr hμ hμ1
  set F : Finset X := (h1 ((g : G) : X ≃ₜ X) g.2).toFinset with hF
  have hsub : {E : Finset X | ((fun E => (ν E (g • S)).toReal) ∘ τ) E ≠ (ν E S).toReal}
      ⊆ {E : Finset X | F ⊆ E}ᶜ := by
    intro E hE hFE
    apply hE
    show (symIter lam (base G 𝓗) (τ E) (v '' (g • S))).toReal
      = (symIter lam (base G 𝓗) E (v '' S)).toReal
    rw [himg, Equiv.finsetCongr_apply, symIter_star hlaminv]
    intro x hx
    have hgx : GermMem 𝓗 ((g : G) : X ≃ₜ X) x := by
      by_contra hn
      exact hx (hFE (by rw [hF, Set.Finite.mem_toFinset]; exact hn))
    exact (smul_base_eq_iff G 𝓗 g x).2 hgx
  have hc : μ {E : Finset X | F ⊆ E}ᶜ = 0 :=
    PartB3.fam_compl_eq_zero hμ hμ1 (hfull F (Set.subset_univ _))
  exact le_antisymm (hc ▸ PartB1.fa_mono hμ hsub) bot_le

end GermGroupoid.JN.PartG
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
/-! ## Part G: the invariant mean on `FinSec` -/
alias exists_finSec_mean := GermGroupoid.JN.PartG.exists_finSec_mean

end GermGroupoid.JN
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN.PartH
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
/-!
# Part H: stabilizers of finite sections are amenable

`F` is the finite support of `ψ`. De Cornulier's induction (Part C) reduces to the elements of the
stabilizer fixing `F` pointwise; the germ filtration (Part D) handles those, since off `F` such an
element maps `base x = ψ x` to `ψ (k x) = base (k x)`, so its germ lies in `𝓗`.
-/
theorem isAmenable_stabilizer (h1 : CondOne G 𝓗) (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x))
    (h3 : ThompsonAmenability.IsExtensivelyAmenableOn G X Set.univ)
    (h4 : Garrido.IsAmenable (fullGroup 𝓗)) (ψ : FinSec G 𝓗 h1) :
    Garrido.IsAmenable (MulAction.stabilizer G ψ) := by
  classical
  set F : Finset X := ψ.2.toFinset with hFdef
  have memF : ∀ x, x ∈ F ↔ ψ.1 x ≠ base G 𝓗 x := fun x => by simp [hFdef]
  set K := MulAction.stabilizer G ψ
  refine GermGroupoid.JN.isAmenable_of_isAmenable_inf_fixingSubgroup h3 F (Set.subset_univ _) K ?_
  refine GermGroupoid.JN.isAmenable_of_germs_fixing G 𝓗 h2 h4 _ F ?_ ?_
  · intro k hk y hy
    exact (mem_fixingSubgroup_iff G).1 (Subgroup.mem_inf.1 hk).2 y (Finset.mem_coe.2 hy)
  · intro k hk hev x
    obtain ⟨hkK, hkF⟩ := Subgroup.mem_inf.1 hk
    have hfixF : ∀ y ∈ F, ((k : G) : X ≃ₜ X) y = y := fun y hy =>
      (mem_fixingSubgroup_iff G).1 hkF y (Finset.mem_coe.2 hy)
    by_cases hx : x ∈ F
    · exact GermGroupoid.JN.germMem_of_eventually_id (hev x hx)
    · have hkx : ((k : G) : X ≃ₜ X) x ∉ F := by
        intro hkx
        have h := hfixF _ hkx
        exact hx (((k : G) : X ≃ₜ X).injective h ▸ hkx)
      have hψx : ψ.1 x = base G 𝓗 x := by
        by_contra h; exact hx ((memF x).2 h)
      have hψkx : ψ.1 (((k : G) : X ≃ₜ X) x) = base G 𝓗 (((k : G) : X ≃ₜ X) x) := by
        by_contra h; exact hkx ((memF _).2 h)
      have hkψ : k • ψ = ψ := hkK
      have happ := congrArg (fun φ : FinSec G 𝓗 h1 => φ.1 (((k : G) : X ≃ₜ X) x)) hkψ
      simp only [GermGroupoid.JN.finSec_smul_apply] at happ
      have hinv : (k⁻¹ : G) • (((k : G) : X ≃ₜ X) x) = x := by
        show ((k : G) : X ≃ₜ X)⁻¹ (((k : G) : X ≃ₜ X) x) = x
        exact ((k : G) : X ≃ₜ X).symm_apply_apply x
      rw [hinv, hψx, hψkx] at happ
      exact (GermGroupoid.JN.smul_base_eq_iff G 𝓗 k x).1 happ

end GermGroupoid.JN.PartH
end

section
open scoped ENNReal Pointwise Topology
namespace GermGroupoid.JN
variable {X : Type*} [TopologicalSpace X]
variable (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
/-! ## Part H: stabilizers are amenable -/
alias isAmenable_stabilizer := GermGroupoid.JN.PartH.isAmenable_stabilizer

/-! ## The theorem -/
theorem chk_isAmenable_of_isExtensivelyAmenableOn
    (h1 : ∀ g ∈ G, {x | ¬ GermMem 𝓗 g x}.Finite)
    (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x))
    (h3 : ThompsonAmenability.IsExtensivelyAmenableOn G X Set.univ)
    (h4 : Garrido.IsAmenable (fullGroup 𝓗)) :
    Garrido.IsAmenable G := by
  obtain ⟨lam, hlam, hlaminv⟩ := exists_fiber_means G 𝓗 h2
  obtain ⟨m, hm, hm1, hminv⟩ := exists_finSec_mean G 𝓗 h1 lam hlam hlaminv h3
  exact isAmenable_of_invariant_of_stabilizer m hm hm1 hminv
    (isAmenable_stabilizer G 𝓗 h1 h2 h3 h4)

end GermGroupoid.JN
end

end
end

section
section
namespace GermGroupoid

theorem isAmenable_of_isExtensivelyAmenableOn {X : Type*} [TopologicalSpace X]
    (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
    (h1 : ∀ g ∈ G, {x | ¬ GermMem 𝓗 g x}.Finite)
    (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x))
    (h3 : ThompsonAmenability.IsExtensivelyAmenableOn G X Set.univ)
    (h4 : Garrido.IsAmenable (fullGroup 𝓗)) :
    Garrido.IsAmenable G :=
  JN.chk_isAmenable_of_isExtensivelyAmenableOn G 𝓗 h1 h2 h3 h4

end GermGroupoid

end
end

section
open GermGroupoid

theorem solution {X : Type*} [TopologicalSpace X]
    (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
    (h1 : ∀ g ∈ G, {x | ¬ GermMem 𝓗 g x}.Finite)
    (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x))
    (h3 : ThompsonAmenability.IsExtensivelyAmenableOn G X Set.univ)
    (h4 : Garrido.IsAmenable (fullGroup 𝓗)) :
    Garrido.IsAmenable G := by
  apply GermGroupoid.isAmenable_of_isExtensivelyAmenableOn <;> assumption

end
