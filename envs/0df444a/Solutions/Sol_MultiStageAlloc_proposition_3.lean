-- Prove2me | solution 1 for MultiStageAlloc.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:16:38.226411+00:00
-- url     : https://prove2.me/submissions/d545df05-be55-4065-9ae8-9682554aaaca

import Mathlib
import Definitions.Def_MultiStageAlloc_Lagrangian

namespace Aux_MultiStageAlloc_proposition_3

section Cone

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [Fintype W]

def LI (g : ι → (W → ℝ)) (T : Finset ι) : Prop :=
  ∀ f : ι → ℝ, ∑ i ∈ T, f i • g i = 0 → ∀ i ∈ T, f i = 0

theorem carath (g : ι → (W → ℝ)) : ∀ (K : ℕ) (lam : ι → ℝ), (∀ i, 0 ≤ lam i) →
    (Finset.univ.filter (fun i => lam i ≠ 0)).card ≤ K →
    ∃ T : Finset ι, LI g T ∧ ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧
      ∑ i, μ i • g i = ∑ i, lam i • g i := by
  intro K
  induction K with
  | zero =>
    intro lam hlam hcard
    refine ⟨∅, fun f _ i hi => absurd hi (Finset.notMem_empty i), lam, hlam, ?_, rfl⟩
    intro i _
    by_contra h
    have hi : i ∈ Finset.univ.filter (fun i => lam i ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  | succ K ih =>
    intro lam hlam hcard
    obtain ⟨S, hS⟩ : ∃ S : Finset ι, S = Finset.univ.filter (fun i => lam i ≠ 0) := ⟨_, rfl⟩
    have memS : ∀ i, i ∈ S ↔ lam i ≠ 0 := by intro i; rw [hS]; simp
    rw [← hS] at hcard
    by_cases hLI : LI g S
    · refine ⟨S, hLI, lam, hlam, fun i hi => ?_, rfl⟩
      by_contra h
      exact hi ((memS i).mpr h)
    · unfold LI at hLI
      push_neg at hLI
      obtain ⟨f, hf, i₀, hi₀S, hfi₀⟩ := hLI
      have hc : ∑ i, (if i ∈ S then f i else 0) • g i = 0 := by
        calc ∑ i, (if i ∈ S then f i else 0) • g i
            = ∑ i ∈ S, (if i ∈ S then f i else 0) • g i :=
              Eq.symm (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi]))
          _ = ∑ i ∈ S, f i • g i := Finset.sum_congr rfl (fun i hi => by simp [hi])
          _ = 0 := hf
      obtain ⟨d, hd0, hdS, hdi₀⟩ : ∃ d : ι → ℝ, ∑ i, d i • g i = 0 ∧
          (∀ i, i ∉ S → d i = 0) ∧ 0 < d i₀ := by
        rcases lt_or_gt_of_ne hfi₀ with hneg | hpos
        · refine ⟨fun i => -(if i ∈ S then f i else 0), ?_, ?_, ?_⟩
          · simp only [neg_smul, Finset.sum_neg_distrib, hc, neg_zero]
          · intro i hi; simp [hi]
          · simp only [if_pos hi₀S]; linarith
        · refine ⟨fun i => if i ∈ S then f i else 0, hc, ?_, ?_⟩
          · intro i hi; simp [hi]
          · simp only [if_pos hi₀S]; exact hpos
      have hdpos : ∀ i, 0 < d i → i ∈ S := by
        intro i hi
        by_contra h
        rw [hdS i h] at hi
        exact lt_irrefl _ hi
      obtain ⟨P, hP⟩ : ∃ P : Finset ι, P = Finset.univ.filter (fun i => 0 < d i) := ⟨_, rfl⟩
      have memP : ∀ i, i ∈ P ↔ 0 < d i := by intro i; rw [hP]; simp
      have hPne : P.Nonempty := ⟨i₀, (memP i₀).mpr hdi₀⟩
      obtain ⟨i₁, hi₁P, hmin⟩ := Finset.exists_min_image P (fun i => lam i / d i) hPne
      have hd1 : 0 < d i₁ := (memP i₁).mp hi₁P
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = lam i₁ / d i₁ := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (hlam i₁) hd1.le
      have hlam' : ∀ i, 0 ≤ lam i - t * d i := by
        intro i
        by_cases hdi : 0 < d i
        · have h1 : t ≤ lam i / d i := by rw [ht]; exact hmin i ((memP i).mpr hdi)
          rw [le_div_iff₀ hdi] at h1
          linarith
        · push_neg at hdi
          nlinarith [hlam i, ht0, hdi]
      have hzero : lam i₁ - t * d i₁ = 0 := by
        rw [ht, div_mul_cancel₀ _ hd1.ne', sub_self]
      have hsupp : Finset.univ.filter (fun i => lam i - t * d i ≠ 0) ⊆ S.erase i₁ := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_erase]
        refine ⟨fun h => hi.2 (by rw [h]; exact hzero), ?_⟩
        by_contra hiS
        apply hi.2
        rw [hdS i hiS]
        have : lam i = 0 := by
          by_contra h'
          exact hiS ((memS i).mpr h')
        rw [this]
        ring
      have hcard' : (Finset.univ.filter (fun i => lam i - t * d i ≠ 0)).card ≤ K := by
        have h1 := Finset.card_le_card hsupp
        have h2 := Finset.card_erase_of_mem (hdpos i₁ hd1)
        omega
      obtain ⟨T, hT, μ, hμ0, hμT, hμsum⟩ := ih (fun i => lam i - t * d i) hlam' hcard'
      refine ⟨T, hT, μ, hμ0, hμT, ?_⟩
      have hsplit : ∑ i, (lam i - t * d i) • g i = ∑ i, lam i • g i - t • ∑ i, d i • g i := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [sub_smul, mul_smul]
      rw [hμsum, hsplit, hd0, smul_zero, sub_zero]

def coneOf (g : ι → (W → ℝ)) : Set (W → ℝ) :=
  {x | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • g i = x}

theorem mem_coneOf (g : ι → (W → ℝ)) (x : W → ℝ) :
    x ∈ coneOf g ↔ ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • g i = x := Iff.rfl

def coneT (g : ι → (W → ℝ)) (T : Finset ι) : Set (W → ℝ) :=
  {x | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • g i = x}

theorem mem_coneT (g : ι → (W → ℝ)) (T : Finset ι) (x : W → ℝ) :
    x ∈ coneT g T ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • g i = x := Iff.rfl

theorem sum_ext_T (g : ι → (W → ℝ)) (T : Finset ι) (μ : T → ℝ) :
    ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i = ∑ i : T, μ i • g i := by
  have h1 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i =
      ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i :=
    Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [dif_neg hi, zero_smul])
  rw [← h1, ← Finset.sum_coe_sort T]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.2]

theorem sum_restrict_T (g : ι → (W → ℝ)) (T : Finset ι) (μ : ι → ℝ)
    (hμT : ∀ i, i ∉ T → μ i = 0) :
    ∑ i : T, μ i • g i = ∑ i, μ i • g i := by
  have h1 : ∑ i : T, μ i • g i = ∑ i ∈ T, μ i • g i := Finset.sum_coe_sort T (fun i => μ i • g i)
  rw [h1]
  exact Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [hμT i hi, zero_smul])

theorem coneT_closed (g : ι → (W → ℝ)) (T : Finset ι) (hT : LI g T) :
    IsClosed (coneT g T) := by
  let L : (T → ℝ) →ₗ[ℝ] (W → ℝ) := Fintype.linearCombination ℝ (fun i : T => g i)
  have hL : ∀ μ : T → ℝ, L μ = ∑ i : T, μ i • g i := fun μ => rfl
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro μ hμ
    rw [hL] at hμ
    have h1 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i = 0 := by
      have h3 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i =
          ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i :=
        Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [dif_neg hi, zero_smul])
      rw [h3, sum_ext_T]
      exact hμ
    have h2 := hT _ h1
    funext i
    have := h2 i i.2
    rw [dif_pos i.2] at this
    exact this
  have hA : IsClosed {μ : T → ℝ | ∀ i, 0 ≤ μ i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have heq : coneT g T = L '' {μ : T → ℝ | ∀ i, 0 ≤ μ i} := by
    ext x
    rw [mem_coneT]
    constructor
    · rintro ⟨μ, hμ0, hμT, rfl⟩
      refine ⟨fun i => μ i, fun i => hμ0 i, ?_⟩
      rw [hL]
      exact sum_restrict_T g T μ hμT
    · rintro ⟨μ, hμ0, rfl⟩
      refine ⟨fun i => if h : i ∈ T then μ ⟨i, h⟩ else 0, ?_, ?_, ?_⟩
      · intro i
        show 0 ≤ (if h : i ∈ T then μ ⟨i, h⟩ else 0)
        by_cases h : i ∈ T
        · rw [dif_pos h]; exact hμ0 _
        · rw [dif_neg h]
      · intro i hi
        show (if h : i ∈ T then μ ⟨i, h⟩ else 0) = 0
        rw [dif_neg hi]
      · rw [hL]
        exact sum_ext_T g T μ
  rw [heq]
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap _ hA

theorem cone_closed (g : ι → (W → ℝ)) : IsClosed (coneOf g) := by
  have heq : coneOf g = ⋃ (T : Finset ι), ⋃ (_ : LI g T), coneT g T := by
    ext x
    rw [mem_coneOf, Set.mem_iUnion₂]
    constructor
    · rintro ⟨lam, hlam, rfl⟩
      obtain ⟨T, hT, μ, hμ0, hμT, hμ⟩ :=
        carath g (Finset.univ.filter (fun i => lam i ≠ 0)).card lam hlam le_rfl
      exact ⟨T, hT, (mem_coneT g T _).mpr ⟨μ, hμ0, hμT, hμ⟩⟩
    · rintro ⟨T, _, hx⟩
      obtain ⟨μ, hμ0, _, hμ⟩ := (mem_coneT g T x).mp hx
      exact ⟨μ, hμ0, hμ⟩
  rw [heq]
  exact isClosed_iUnion_of_finite (fun T => isClosed_iUnion_of_finite (fun hT => coneT_closed g T hT))

end Cone


/-! ### Affine Farkas lemma -/

section Farkas

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coneOf_convex {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] (g : ι → (W → ℝ)) :
    Convex ℝ (coneOf g) := by
  intro x hx y hy a b ha hb _
  obtain ⟨l1, hl1, rfl⟩ := (mem_coneOf g x).mp hx
  obtain ⟨l2, hl2, rfl⟩ := (mem_coneOf g y).mp hy
  refine (mem_coneOf g _).mpr ⟨fun i => a * l1 i + b * l2 i,
    fun i => add_nonneg (mul_nonneg ha (hl1 i)) (mul_nonneg hb (hl2 i)), ?_⟩
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_smul, mul_smul, mul_smul]

/-- generators of the homogenised cone. -/
def g1 {P : Type*} [Fintype P] [DecidableEq P] (G : P → V → ℝ) (h : P → ℝ) (j : P) : Option V → ℝ :=
  fun o => Option.elim o (h j) (G j)

def g3 {R : Type*} [Fintype R] [DecidableEq R] (K : R → V → ℝ) (e : R → ℝ) (l : R) : Option V → ℝ :=
  fun o => Option.elim o (e l) (K l)

def g4 : Option V → ℝ := fun o => Option.elim o 1 (fun _ => 0)

def gens {P R : Type*} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] (G : P → V → ℝ) (h : P → ℝ) (K : R → V → ℝ) (e : R → ℝ) :
    ((P ⊕ P) ⊕ (R ⊕ Unit)) → (Option V → ℝ) :=
  Sum.elim (Sum.elim (g1 G h) (fun j => -(g1 G h j))) (Sum.elim (g3 K e) (fun _ => g4))

lemma farkas {P R : Type*} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] (G : P → V → ℝ) (h : P → ℝ) (K : R → V → ℝ)
    (e : R → ℝ) (a : V → ℝ) (β : ℝ)
    (hne : ∃ z : V → ℝ, (∀ j, ∑ v, G j v * z v = h j) ∧ (∀ l, ∑ v, K l v * z v ≤ e l))
    (hval : ∀ z : V → ℝ, (∀ j, ∑ v, G j v * z v = h j) → (∀ l, ∑ v, K l v * z v ≤ e l) →
      ∑ v, a v * z v ≤ β) :
    ∃ (μ : P → ℝ) (lam : R → ℝ), (∀ l, 0 ≤ lam l) ∧
      (∀ v, a v = ∑ j, μ j * G j v + ∑ l, lam l * K l v) ∧
      ∑ j, μ j * h j + ∑ l, lam l * e l ≤ β := by
  classical
  have hmem : (fun o => Option.elim o β a) ∈ coneOf (gens G h K e) := by
    by_contra hnot
    obtain ⟨f, u, hfu, hut⟩ :=
      geometric_hahn_banach_closed_point (coneOf_convex _) (cone_closed _) hnot
    have h0mem : (0 : Option V → ℝ) ∈ coneOf (gens G h K e) :=
      (mem_coneOf _ 0).mpr ⟨0, fun _ => le_rfl, by simp⟩
    have hu : 0 < u := by
      have := hfu 0 h0mem
      simpa using this
    have hg : ∀ i, f (gens G h K e i) ≤ 0 := by
      intro i
      by_contra hneg
      push_neg at hneg
      have hm : (u / f (gens G h K e i)) • gens G h K e i ∈ coneOf (gens G h K e) := by
        refine (mem_coneOf _ _).mpr ⟨fun j => if j = i then u / f (gens G h K e i) else 0,
          fun j => ?_, ?_⟩
        · show 0 ≤ (if j = i then u / f (gens G h K e i) else 0)
          by_cases hj : j = i
          · rw [if_pos hj]; exact le_of_lt (div_pos hu hneg)
          · rw [if_neg hj]
        · simp [ite_smul]
      have := hfu _ hm
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne'] at this
      exact lt_irrefl _ this
    have hfx : ∀ w : Option V → ℝ, f w = ∑ o, w o * f (fun j => if o = j then (1 : ℝ) else 0) := by
      intro w
      conv_lhs => rw [pi_eq_sum_univ w]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [map_smul, smul_eq_mul]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = f (fun j => if (none : Option V) = j then (1 : ℝ) else 0) :=
      ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : V → ℝ, y = fun v => f (fun j => if (some v : Option V) = j then (1 : ℝ) else 0) :=
      ⟨_, rfl⟩
    have hf' : ∀ w : Option V → ℝ, f w = w none * t + ∑ v, w (some v) * y v := by
      intro w
      rw [hfx, Fintype.sum_option, ht, hy]
    have hunit := hg (Sum.inr (Sum.inr ()))
    simp only [gens, Sum.elim_inr, hf', g4, Option.elim_none, Option.elim_some, one_mul,
      zero_mul, Finset.sum_const_zero, add_zero] at hunit
    have heq : ∀ j, h j * t + ∑ v, G j v * y v = 0 := by
      intro j
      have h1 := hg (Sum.inl (Sum.inl j))
      have h2 := hg (Sum.inl (Sum.inr j))
      simp only [gens, Sum.elim_inl, Sum.elim_inr, map_neg, hf', g1, Option.elim_none,
        Option.elim_some,
        Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at h1 h2
      linarith
    have hineq : ∀ l, e l * t + ∑ v, K l v * y v ≤ 0 := by
      intro l
      have h1 := hg (Sum.inr (Sum.inl l))
      simp only [gens, Sum.elim_inr, Sum.elim_inl, hf', g3, Option.elim_none,
        Option.elim_some] at h1
      exact h1
    have htop : u < β * t + ∑ v, a v * y v := by
      have := hut
      simp only [hf', Option.elim_none, Option.elim_some] at this
      exact this
    rcases lt_or_eq_of_le hunit with htn | htz
    · have htp : 0 < -t := by linarith
      have hz : ∑ v, a v * (y v / -t) ≤ β := hval (fun v => y v / (-t)) (fun j => by
          show ∑ v, G j v * (y v / -t) = h j
          have := heq j
          rw [show ∑ v, G j v * (y v / -t) = (∑ v, G j v * y v) / (-t) by
            rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring)]
          rw [div_eq_iff htp.ne']
          linarith)
        (fun l => by
          show ∑ v, K l v * (y v / -t) ≤ e l
          have := hineq l
          rw [show ∑ v, K l v * (y v / -t) = (∑ v, K l v * y v) / (-t) by
            rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring)]
          rw [div_le_iff₀ htp]
          linarith)
      rw [show ∑ v, a v * (y v / -t) = (∑ v, a v * y v) / (-t) by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring),
        div_le_iff₀ htp] at hz
      nlinarith
    · rw [htz] at heq hineq htop
      simp only [mul_zero, zero_add] at heq hineq htop
      obtain ⟨z0, hz0e, hz0l⟩ := hne
      have hv0 := hval z0 hz0e hz0l
      have hay : 0 < ∑ v, a v * y v := by linarith
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (β - ∑ v, a v * z0 v + 1) / ∑ v, a v * y v := ⟨_, rfl⟩
      have hs0 : 0 ≤ s := by
        rw [hs]
        apply div_nonneg _ hay.le
        linarith
      have hsplit : ∀ c : V → ℝ, ∑ v, c v * (z0 v + s * y v)
          = ∑ v, c v * z0 v + s * ∑ v, c v * y v := by
        intro c
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun v _ => by ring)
      have hz : ∑ v, a v * (z0 v + s * y v) ≤ β := hval (fun v => z0 v + s * y v)
        (fun j => by
          show ∑ v, G j v * (z0 v + s * y v) = h j
          rw [hsplit, hz0e j, heq j, mul_zero, add_zero])
        (fun l => by
          show ∑ v, K l v * (z0 v + s * y v) ≤ e l
          rw [hsplit]
          have := hineq l
          have := hz0l l
          nlinarith)
      rw [hsplit] at hz
      have hsa : s * ∑ v, a v * y v = β - ∑ v, a v * z0 v + 1 := by
        rw [hs, div_mul_cancel₀ _ hay.ne']
      linarith
  obtain ⟨lam, hlam, hsum⟩ := (mem_coneOf _ _).mp hmem
  refine ⟨fun j => lam (Sum.inl (Sum.inl j)) - lam (Sum.inl (Sum.inr j)),
    fun l => lam (Sum.inr (Sum.inl l)), fun l => hlam _, ?_, ?_⟩
  · intro v
    have := congrFun hsum (some v)
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, gens, Sum.elim_inl,
      Sum.elim_inr, g1, g3, g4, Pi.neg_apply, Option.elim_some, Fintype.sum_unique,
      mul_zero, add_zero] at this
    rw [← this]
    simp only [sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
    ring
  · have := congrFun hsum none
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, gens, Sum.elim_inl,
      Sum.elim_inr, g1, g3, g4, Pi.neg_apply, Option.elim_none, Fintype.sum_unique,
      mul_one] at this
    have hl4 := hlam (Sum.inr (Sum.inr default))
    have e1 : ∑ j, (lam (Sum.inl (Sum.inl j)) - lam (Sum.inl (Sum.inr j))) * h j
        = ∑ j, lam (Sum.inl (Sum.inl j)) * h j + ∑ j, lam (Sum.inl (Sum.inr j)) * -h j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [e1]
    linarith

/-- the slack identity coming from a Farkas certificate. -/
lemma farkas_slack {P R : Type*} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] (G : P → V → ℝ) (h : P → ℝ) (K : R → V → ℝ)
    (e : R → ℝ) (a : V → ℝ) (μ : P → ℝ) (lam : R → ℝ)
    (ha : ∀ v, a v = ∑ j, μ j * G j v + ∑ l, lam l * K l v)
    (z : V → ℝ) (hz : ∀ j, ∑ v, G j v * z v = h j) :
    ∑ v, a v * z v = ∑ j, μ j * h j + ∑ l, lam l * ∑ v, K l v * z v := by
  simp only [ha, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hz j, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => by ring)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => by ring)

end Farkas


/-! ### Facts about `slope` and `regFext` -/

section Slope

open MultiStageAlloc

lemma clamp_mem (s : ℝ) : max 0 (min 1 s) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma clamp_mono : Monotone (fun s : ℝ => max 0 (min 1 s)) := by
  intro a b hab
  exact max_le_max le_rfl (min_le_min le_rfl hab)

lemma regPoly_mono' (K k : ℕ) (hk : k < K) {a b : ℝ} (ha : 0 ≤ a) (hb1 : b ≤ 1) (hab : a ≤ b) :
    regPoly K k a ≤ regPoly K k b := by
  unfold regPoly
  rw [if_pos hk, if_pos hk]
  have hn : (1:ℝ) ≤ ((K - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ K - k)
  have h1 : (1 - (1 - a) / ((K - k : ℕ) : ℝ)) ≤ (1 - (1 - b) / ((K - k : ℕ) : ℝ)) := by
    have : (1 - b) / ((K - k : ℕ) : ℝ) ≤ (1 - a) / ((K - k : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  have h0 : 0 ≤ 1 - (1 - a) / ((K - k : ℕ) : ℝ) := by
    have : (1 - a) / ((K - k : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  exact pow_le_pow_left₀ h0 h1 _

lemma slope_mono (K k : ℕ) : Monotone (MultiStageAlloc.slope K k) := by
  intro a b hab
  unfold MultiStageAlloc.slope
  by_cases hk : k < K
  · rw [if_pos hk, if_pos hk]
    exact regPoly_mono' K k hk (clamp_mem a).1 (clamp_mem b).2 (clamp_mono hab)
  · rw [if_neg hk, if_neg hk]

lemma slope_cont (K k : ℕ) : Continuous (MultiStageAlloc.slope K k) := by
  by_cases hk : k < K
  · have : MultiStageAlloc.slope K k = fun s => (1 - (1 - max 0 (min 1 s)) / ((K - k : ℕ) : ℝ)) ^ (K - k) := by
      funext s
      unfold MultiStageAlloc.slope regPoly
      rw [if_pos hk, if_pos hk]
    rw [this]
    have hc : Continuous (fun s : ℝ => max 0 (min 1 s)) :=
      continuous_const.max (continuous_const.min continuous_id)
    exact (continuous_const.sub ((continuous_const.sub hc).div_const _)).pow _
  · have : MultiStageAlloc.slope K k = fun _ => 0 := by
      funext s
      unfold MultiStageAlloc.slope
      rw [if_neg hk]
    rw [this]
    exact continuous_const

lemma regFext_deriv (K k : ℕ) (t : ℝ) : HasDerivAt (regFext K k) (MultiStageAlloc.slope K k t) t :=
  ((slope_cont K k).integral_hasStrictDerivAt 0 t).hasDerivAt

lemma regFext_tangent (K k : ℕ) (a b : ℝ) :
    MultiStageAlloc.slope K k a * (b - a) ≤ regFext K k b - regFext K k a := by
  have hint : ∀ c d : ℝ, IntervalIntegrable (MultiStageAlloc.slope K k) MeasureTheory.volume c d :=
    fun c d => (slope_cont K k).intervalIntegrable c d
  have hdiff : regFext K k b - regFext K k a = ∫ s in a..b, MultiStageAlloc.slope K k s := by
    unfold regFext
    exact intervalIntegral.integral_interval_sub_left (hint 0 b) (hint 0 a)
  rw [hdiff]
  rcases le_total a b with hab | hab
  · have h := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const (c := MultiStageAlloc.slope K k a)) (hint a b)
      (fun s hs => slope_mono K k hs.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  · have h := intervalIntegral.integral_mono_on hab (hint b a)
      (intervalIntegrable_const (c := MultiStageAlloc.slope K k a))
      (fun s hs => slope_mono K k hs.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    rw [intervalIntegral.integral_symm]
    linarith

lemma regF_eq (K k : ℕ) (hk : k ≤ K) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    regF K k t = regFext K k t := by
  unfold regF regFext
  rcases lt_or_eq_of_le hk with hk' | hk'
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    unfold MultiStageAlloc.slope
    rw [if_pos hk']
    have : max 0 (min 1 s) = s := by
      rw [min_eq_right (le_trans hs.2 ht.2), max_eq_right hs.1]
    rw [this]
  · subst hk'
    have h1 : ∫ s in (0:ℝ)..t, MultiStageAlloc.slope k k s = 0 := by
      have : MultiStageAlloc.slope k k = fun _ => 0 := by
        funext s; unfold MultiStageAlloc.slope; rw [if_neg (lt_irrefl k)]
      rw [this]; simp
    rw [h1]
    have h2 : ∫ s in (0:ℝ)..t, regPoly k k s = ∫ s in (0:ℝ)..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr_ae
      have hae : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), regPoly k k s = 0 := by
        rw [MeasureTheory.ae_iff]
        apply MeasureTheory.measure_mono_null _ (Real.volume_singleton (a := 1))
        intro s hs
        simp only [Set.mem_setOf_eq] at hs
        simp only [Set.mem_singleton_iff]
        by_contra hne
        apply hs
        unfold regPoly
        rw [if_neg (lt_irrefl k), if_neg hne]
      filter_upwards [hae] with s hs
      intro _
      exact hs
    rw [h2]
    simp

end Slope

/-! ### The stage program -/

section Stage

open MultiStageAlloc

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

noncomputable def Phi (I : Instance U V K) (k : ℕ) (y : V → ℝ) (z : U → V → ℝ) : ℝ :=
  ∑ j, (I.w j * ∑ i, z i j - I.cap j * I.w j * regFext K k (level I y z j))

lemma level_mem (I : Instance U V K) (k : ℕ) (y : V → ℝ) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1)
    (z : U → V → ℝ) (hz : StageFeasible I k y z) (j : V) :
    level I y z j ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨hnn, -, -, hcol⟩ := hz
  have hc := I.cap_pos j
  have hs : 0 ≤ ∑ i, z i j / I.cap j := Finset.sum_nonneg (fun i _ => div_nonneg (hnn i j) hc.le)
  have hs2 : ∑ i, z i j / I.cap j ≤ 1 - y j := by
    rw [← Finset.sum_div, div_le_iff₀ hc]
    linarith [hcol j]
  unfold level
  exact ⟨by linarith [(hy j).1], by linarith⟩

lemma stageObj_eq (I : Instance U V K) (k : ℕ) (hk : k ≤ K) (y : V → ℝ)
    (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) (z : U → V → ℝ) (hz : StageFeasible I k y z) :
    stageObj I k y z = Phi I k y z := by
  unfold stageObj Phi
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [regF_eq K k hk _ (level_mem I k y hy z hz j)]

lemma level_diff (I : Instance U V K) (y : V → ℝ) (z x : U → V → ℝ) (j : V) :
    level I y z j - level I y x j = (∑ i, z i j - ∑ i, x i j) / I.cap j := by
  unfold level
  rw [← Finset.sum_div, ← Finset.sum_div]
  ring

lemma Phi_concave (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x z : U → V → ℝ) :
    Phi I k y z ≤ Phi I k y x +
      ∑ i, ∑ j, I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) * (z i j - x i j) := by
  have hj : ∀ j, (I.w j * ∑ i, z i j - I.cap j * I.w j * regFext K k (level I y z j)) ≤
      (I.w j * ∑ i, x i j - I.cap j * I.w j * regFext K k (level I y x j)) +
      I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) * (∑ i, z i j - ∑ i, x i j) := by
    intro j
    have ht := regFext_tangent K k (level I y x j) (level I y z j)
    rw [level_diff] at ht
    have hcw : 0 ≤ I.cap j * I.w j := mul_nonneg (I.cap_pos j).le (I.w_nonneg j)
    have h2 := mul_le_mul_of_nonneg_left ht hcw
    have hc0 : I.cap j ≠ 0 := (I.cap_pos j).ne'
    have e1 : I.cap j * I.w j * (MultiStageAlloc.slope K k (level I y x j) * ((∑ i, z i j - ∑ i, x i j) / I.cap j))
        = I.w j * MultiStageAlloc.slope K k (level I y x j) * (∑ i, z i j - ∑ i, x i j) := by
      first | (field_simp; ring1) | field_simp
    rw [e1] at h2
    have e2 : I.cap j * I.w j * (regFext K k (level I y z j) - regFext K k (level I y x j)) =
        I.cap j * I.w j * regFext K k (level I y z j) -
          I.cap j * I.w j * regFext K k (level I y x j) := by ring
    rw [e2] at h2
    linarith
  calc Phi I k y z ≤ ∑ j, ((I.w j * ∑ i, x i j - I.cap j * I.w j * regFext K k (level I y x j)) +
      I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) * (∑ i, z i j - ∑ i, x i j)) :=
        Finset.sum_le_sum (fun j _ => hj j)
    _ = Phi I k y x + ∑ i, ∑ j, I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) * (z i j - x i j) := by
        unfold Phi
        rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun i j =>
          I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) * (z i j - x i j))]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]

lemma Phi_deriv (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x d : U → V → ℝ) :
    HasDerivAt (fun t => Phi I k y (fun i j => x i j + t * d i j))
      (∑ i, ∑ j, I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) * d i j) 0 := by
  have hfun : (fun t => Phi I k y (fun i j => x i j + t * d i j)) = fun t =>
      ∑ j, (I.w j * ((∑ i, x i j) + t * ∑ i, d i j) - I.cap j * I.w j *
        regFext K k (level I y x j + t * ((∑ i, d i j) / I.cap j))) := by
    funext t
    unfold Phi
    apply Finset.sum_congr rfl
    intro j _
    have e1 : ∑ i, (x i j + t * d i j) = (∑ i, x i j) + t * ∑ i, d i j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : level I y (fun i j => x i j + t * d i j) j =
        level I y x j + t * ((∑ i, d i j) / I.cap j) := by
      unfold level
      rw [← Finset.sum_div, ← Finset.sum_div, e1]
      ring
    rw [e1, e2]
  rw [hfun]
  have hterm : ∀ j ∈ Finset.univ, HasDerivAt (fun t =>
      I.w j * ((∑ i, x i j) + t * ∑ i, d i j) - I.cap j * I.w j *
        regFext K k (level I y x j + t * ((∑ i, d i j) / I.cap j)))
      (I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) * ∑ i, d i j) 0 := by
    intro j _
    have h1 : HasDerivAt (fun t => I.w j * ((∑ i, x i j) + t * ∑ i, d i j))
        (I.w j * (1 * ∑ i, d i j)) 0 :=
      (((hasDerivAt_id' 0).mul_const (∑ i, d i j)).const_add (∑ i, x i j)).const_mul (I.w j)
    have h2 : HasDerivAt (fun t => level I y x j + t * ((∑ i, d i j) / I.cap j))
        (1 * ((∑ i, d i j) / I.cap j)) 0 :=
      ((hasDerivAt_id' 0).mul_const ((∑ i, d i j) / I.cap j)).const_add (level I y x j)
    have h3 := (regFext_deriv K k (level I y x j + 0 * ((∑ i, d i j) / I.cap j))).comp 0 h2
    have h4 := (h1.sub (h3.const_mul (I.cap j * I.w j)))
    refine h4.congr_deriv ?_
    have hc0 : I.cap j ≠ 0 := (I.cap_pos j).ne'
    simp only [zero_mul, add_zero, one_mul]
    first | (field_simp; ring1) | field_simp
  have := HasDerivAt.fun_sum hterm
  refine this.congr_deriv ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

lemma feas_comb (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x z : U → V → ℝ)
    (hx : StageFeasible I k y x) (hz : StageFeasible I k y z) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : StageFeasible I k y (fun i j => x i j + t * (z i j - x i j)) := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    have h1 := mul_nonneg ht0 (hz1 i j)
    have h2 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) (hx1 i j)
    show 0 ≤ x i j + t * (z i j - x i j)
    nlinarith
  · intro i j hne
    by_cases h : x i j = 0
    · have hz0 : z i j ≠ 0 := by
        intro h'; apply hne; simp [h, h']
      exact hz2 i j hz0
    · exact hx2 i j h
  · intro i
    have e : ∑ j, (x i j + t * (z i j - x i j)) = (1 - t) * ∑ j, x i j + t * ∑ j, z i j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left (hx3 i) (by linarith : (0:ℝ) ≤ 1 - t)
    have h2 := mul_le_mul_of_nonneg_left (hz3 i) ht0
    linarith
  · intro j
    have e : ∑ i, (x i j + t * (z i j - x i j)) = (1 - t) * ∑ i, x i j + t * ∑ i, z i j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left (hx4 j) (by linarith : (0:ℝ) ≤ 1 - t)
    have h2 := mul_le_mul_of_nonneg_left (hz4 j) ht0
    linarith

lemma deriv_nonpos (ψ : ℝ → ℝ) (ψ' : ℝ) (hψ : HasDerivAt ψ ψ' 0)
    (hmax : ∀ t ∈ Set.Ioo (0:ℝ) 1, ψ t ≤ ψ 0) : ψ' ≤ 0 := by
  have h := hψ.tendsto_slope_zero_right
  apply le_of_tendsto h
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  rw [smul_eq_mul, zero_add]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.1.le) (by linarith [hmax t ht])

end Stage

end Aux_MultiStageAlloc_proposition_3


namespace Aux_MultiStageAlloc_proposition_3

open MultiStageAlloc

section Sums

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

lemma A_diff (I : Instance U V K) (k : ℕ) (lam : U → ℝ) (z x : U → V → ℝ) :
    (∑ i with I.batch i = k, lam i * (∑ j, z i j - 1)) -
      (∑ i with I.batch i = k, lam i * (∑ j, x i j - 1)) =
    ∑ i, ∑ j, (if I.batch i = k then lam i else 0) * (z i j - x i j) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : I.batch i = k
  · rw [if_pos h]
    simp only [if_pos h]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  · rw [if_neg h]
    simp only [if_neg h, zero_mul, Finset.sum_const_zero]

lemma B_diff (I : Instance U V K) (θ : V → ℝ) (y : V → ℝ) (z x : U → V → ℝ) :
    (∑ j, θ j * (level I y z j - 1)) - (∑ j, θ j * (level I y x j - 1)) =
    ∑ i, ∑ j, θ j / I.cap j * (z i j - x i j) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h := level_diff I y z x j
  have e : θ j * (level I y z j - 1) - θ j * (level I y x j - 1) =
      θ j * (level I y z j - level I y x j) := by ring
  rw [e, h, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma C_diff (γ z x : U → V → ℝ) :
    (∑ i, ∑ j, γ i j * z i j) - (∑ i, ∑ j, γ i j * x i j) =
    ∑ i, ∑ j, γ i j * (z i j - x i j) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sum_single [DecidableEq U] [DecidableEq V] (F : U → V → ℝ) (i : U) (j : V) :
    ∑ i', ∑ j', F i' j' * (if i' = i ∧ j' = j then 1 else 0) = F i j := by
  rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero (fun c _ => by simp [hb]))
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.sum_eq_single j (fun c _ hc => by simp [hc]) (fun h => absurd (Finset.mem_univ j) h)]
  simp

end Sums

end Aux_MultiStageAlloc_proposition_3

open MultiStageAlloc Aux_MultiStageAlloc_proposition_3 in
theorem solution {U V : Type*} [Fintype U] [Fintype V] {K : ℕ} (I : Instance U V K)
    (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) (y : V → ℝ) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1)
    (x : U → V → ℝ) (hx : IsStageOptimal I k y x) :
    (∀ (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ), DualNonneg I k lam θ γ →
      stageObj I k y x ≤ lagrangian I k y x lam θ γ) ∧
    (∃ (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ), DualNonneg I k lam θ γ ∧
      lagrangian I k y x lam θ γ = stageObj I k y x ∧
      ∀ z, StageSupported I k z → lagrangian I k y z lam θ γ ≤ stageObj I k y x) ∧
    (∀ (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ), DualNonneg I k lam θ γ →
      (∀ z, StageSupported I k z → lagrangian I k y z lam θ γ ≤ stageObj I k y x) →
      (∀ i j, I.edge i j → I.batch i = k →
        I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) - lam i - θ j / I.cap j + γ i j = 0) ∧
      (∀ i j, I.edge i j → I.batch i = k → γ i j = 0 ∨ (0 < γ i j ∧ x i j = 0)) ∧
      (∀ i, I.batch i = k → lam i = 0 ∨ (0 < lam i ∧ ∑ j, x i j = 1)) ∧
      (∀ j, θ j = 0 ∨ (0 < θ j ∧ level I y x j = 1))) := by
  classical
  obtain ⟨hfeas, hmax⟩ := hx
  have hfeas' := hfeas
  obtain ⟨hnn, hsupp, hrow, hcol⟩ := hfeas'
  have hobj : stageObj I k y x = Phi I k y x := stageObj_eq I k hkK y hy x hfeas
  have hlev : ∀ j, level I y x j ∈ Set.Icc (0:ℝ) 1 := level_mem I k y hy x hfeas
  -- the three penalty terms at x
  have pen : ∀ (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ), DualNonneg I k lam θ γ →
      (∑ i with I.batch i = k, lam i * (∑ j, x i j - 1)) ≤ 0 ∧
      (∑ j, θ j * (level I y x j - 1)) ≤ 0 ∧ 0 ≤ ∑ i, ∑ j, γ i j * x i j := by
    intro lam θ γ hdn
    obtain ⟨hdl, hdθ, hdγ⟩ := hdn
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.sum_nonpos
      intro i hi
      have hb := (Finset.mem_filter.mp hi).2
      exact mul_nonpos_of_nonneg_of_nonpos (hdl i hb) (by linarith [hrow i])
    · apply Finset.sum_nonpos
      intro j _
      exact mul_nonpos_of_nonneg_of_nonpos (hdθ j) (by linarith [(hlev j).2])
    · apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      by_cases h0 : x i j = 0
      · rw [h0, mul_zero]
      · obtain ⟨he, hb⟩ := hsupp i j h0
        exact mul_nonneg (hdγ i j he hb) (hnn i j)
  have hlag : ∀ (z : U → V → ℝ) (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ),
      lagrangian I k y z lam θ γ = Phi I k y z - (∑ i with I.batch i = k, lam i * (∑ j, z i j - 1))
        - (∑ j, θ j * (level I y z j - 1)) + ∑ i, ∑ j, γ i j * z i j := fun _ _ _ _ => rfl
  have P1 : ∀ (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ), DualNonneg I k lam θ γ →
      stageObj I k y x ≤ lagrangian I k y x lam θ γ := by
    intro lam θ γ hdn
    obtain ⟨h1, h2, h3⟩ := pen lam θ γ hdn
    rw [hobj, hlag]
    linarith
  refine ⟨P1, ?_, ?_⟩
  · ---------------- existence of multipliers
    -- gradient
    obtain ⟨g, hg⟩ : ∃ g : U → V → ℝ, g = fun i j => I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) :=
      ⟨_, rfl⟩
    -- first-order condition
    have hA : ∀ z, StageFeasible I k y z → ∑ i, ∑ j, g i j * (z i j - x i j) ≤ 0 := by
      intro z hz
      have hd : HasDerivAt (fun t => Phi I k y (fun i j => x i j + t * (z i j - x i j)))
          (∑ i, ∑ j, g i j * (z i j - x i j)) 0 := by
        rw [hg]
        exact Phi_deriv I k y x (fun i j => z i j - x i j)
      apply deriv_nonpos _ _ hd
      intro t ht
      have hc := feas_comb I k y x z ⟨hnn, hsupp, hrow, hcol⟩ hz t ht.1.le ht.2.le
      have hle := isMaxOn_iff.mp hmax _ hc
      rw [stageObj_eq I k hkK y hy _ hc, hobj] at hle
      have h0 : (fun i j => x i j + (0:ℝ) * (z i j - x i j)) = x := by
        funext i j; ring
      simp only [h0]
      exact hle
    -- Farkas data
    obtain ⟨G, hG⟩ : ∃ G : U × V → U × V → ℝ, G = fun e v =>
        if ¬ (I.edge e.1 e.2 ∧ I.batch e.1 = k) ∧ v = e then 1 else 0 := ⟨_, rfl⟩
    obtain ⟨Kc, hKc⟩ : ∃ Kc : (U × V) ⊕ (U ⊕ V) → U × V → ℝ, Kc =
        Sum.elim (fun e v => if v = e then -1 else 0)
          (Sum.elim (fun i v => if v.1 = i then 1 else 0) (fun j v => if v.2 = j then 1 else 0)) :=
      ⟨_, rfl⟩
    obtain ⟨ec, hec⟩ : ∃ ec : (U × V) ⊕ (U ⊕ V) → ℝ, ec =
        Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun j => I.cap j * (1 - y j))) := ⟨_, rfl⟩
    have S1 : ∀ (e : U × V) (z : U × V → ℝ), ∑ v, G e v * z v =
        if ¬ (I.edge e.1 e.2 ∧ I.batch e.1 = k) then z e else 0 := by
      intro e z
      simp only [hG]
      by_cases h : I.edge e.1 e.2 ∧ I.batch e.1 = k
      · rw [if_neg (not_not.mpr h)]
        apply Finset.sum_eq_zero
        intro v _
        rw [if_neg (fun hh => hh.1 h)]
        ring
      · rw [if_pos h, Finset.sum_eq_single e]
        · rw [if_pos ⟨h, rfl⟩]; ring
        · intro b _ hb
          rw [if_neg (fun hh => hb hh.2)]
          ring
        · intro h'
          exact absurd (Finset.mem_univ e) h'
    have S2 : ∀ (e : U × V) (z : U × V → ℝ), ∑ v, Kc (Sum.inl e) v * z v = -z e := by
      intro e z
      simp only [hKc, Sum.elim_inl, ite_mul, neg_one_mul, zero_mul]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    have S3 : ∀ (i : U) (z : U × V → ℝ), ∑ v, Kc (Sum.inr (Sum.inl i)) v * z v =
        ∑ j, z (i, j) := by
      intro i z
      simp only [hKc, Sum.elim_inr, Sum.elim_inl, ite_mul, one_mul, zero_mul]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    have S4 : ∀ (j : V) (z : U × V → ℝ), ∑ v, Kc (Sum.inr (Sum.inr j)) v * z v =
        ∑ i, z (i, j) := by
      intro j z
      simp only [hKc, Sum.elim_inr, ite_mul, one_mul, zero_mul]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    have hxf : ∀ e : U × V, ∑ v, G e v * x v.1 v.2 = (fun _ => (0:ℝ)) e := by
      intro e
      rw [S1]
      by_cases hs : I.edge e.1 e.2 ∧ I.batch e.1 = k
      · rw [if_neg (not_not.mpr hs)]
      · rw [if_pos hs]
        show x e.1 e.2 = 0
        by_contra hne
        exact hs (hsupp e.1 e.2 hne)
    have hxK : ∀ r, ∑ v, Kc r v * x v.1 v.2 ≤ ec r := by
      intro r
      rcases r with e | i | j
      · rw [S2, hec]; simp only [Sum.elim_inl]; linarith [hnn e.1 e.2]
      · rw [S3, hec]; simp only [Sum.elim_inr, Sum.elim_inl]; exact hrow i
      · rw [S4, hec]; simp only [Sum.elim_inr]; exact hcol j
    obtain ⟨μ, lamF, hlamF, ha, hβ⟩ := farkas G (fun _ => (0:ℝ)) Kc ec
      (fun v : U × V => g v.1 v.2) (∑ v : U × V, g v.1 v.2 * x v.1 v.2)
      ⟨fun v : U × V => x v.1 v.2, hxf, hxK⟩
      (by
        intro z hzG hzK
        let zf : U → V → ℝ := fun i j => z (i, j)
        have hzf : StageFeasible I k y zf := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro i j
            have := hzK (Sum.inl (i, j))
            rw [S2, hec] at this
            simp only [Sum.elim_inl] at this
            show 0 ≤ z (i, j)
            linarith
          · intro i j hne
            by_contra hns
            have := hzG (i, j)
            rw [S1, if_pos hns] at this
            exact hne this
          · intro i
            have := hzK (Sum.inr (Sum.inl i))
            rw [S3, hec] at this
            show ∑ j, z (i, j) ≤ 1
            simpa using this
          · intro j
            have := hzK (Sum.inr (Sum.inr j))
            rw [S4, hec] at this
            show ∑ i, z (i, j) ≤ I.cap j * (1 - y j)
            simpa using this
        have h1 := hA zf hzf
        have e1 : ∑ v : U × V, g v.1 v.2 * z v = ∑ i, ∑ j, g i j * zf i j := by
          rw [Fintype.sum_prod_type]
        have e2 : ∑ v : U × V, g v.1 v.2 * x v.1 v.2 = ∑ i, ∑ j, g i j * x i j := by
          rw [Fintype.sum_prod_type]
        have e3 : ∑ i, ∑ j, g i j * (zf i j - x i j) =
            ∑ i, ∑ j, g i j * zf i j - ∑ i, ∑ j, g i j * x i j := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro j _
          ring
        show ∑ v : U × V, g v.1 v.2 * z v ≤ ∑ v : U × V, g v.1 v.2 * x v.1 v.2
        rw [e1, e2]
        linarith)
    -- multipliers
    refine ⟨fun i => lamF (Sum.inr (Sum.inl i)), fun j => I.cap j * lamF (Sum.inr (Sum.inr j)),
      fun i j => lamF (Sum.inl (i, j)), ?_, ?_⟩
    · exact ⟨fun i _ => hlamF _, fun j => mul_nonneg (I.cap_pos j).le (hlamF _),
        fun i j _ _ => hlamF _⟩
    -- stationarity
    have hstat : ∀ i j, I.edge i j → I.batch i = k →
        g i j = -lamF (Sum.inl (i, j)) + lamF (Sum.inr (Sum.inl i)) +
          lamF (Sum.inr (Sum.inr j)) := by
      intro i j he hb
      have := ha (i, j)
      simp only at this
      rw [this]
      have hGz : ∑ e, μ e * G e (i, j) = 0 := by
        apply Finset.sum_eq_zero
        intro e _
        rw [hG]
        simp only
        rw [if_neg]
        · ring
        · rintro ⟨hns, rfl⟩
          exact hns ⟨he, hb⟩
      rw [hGz, zero_add, Fintype.sum_sum_type, Fintype.sum_sum_type, hKc]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_ite, mul_neg, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    -- complementary slackness
    have hslack := farkas_slack G (fun _ => (0:ℝ)) Kc ec (fun v : U × V => g v.1 v.2) μ lamF ha
      (fun v : U × V => x v.1 v.2) hxf
    simp only [mul_zero, Finset.sum_const_zero, zero_add] at hslack
    have hterm : ∀ r, lamF r * (ec r - ∑ v, Kc r v * x v.1 v.2) = 0 := by
      have hsum : ∑ r, lamF r * (ec r - ∑ v, Kc r v * x v.1 v.2) = 0 := by
        apply le_antisymm
        · have e1 : ∑ r, lamF r * (ec r - ∑ v, Kc r v * x v.1 v.2) =
              ∑ r, lamF r * ec r - ∑ r, lamF r * ∑ v, Kc r v * x v.1 v.2 := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro r _; ring
          rw [e1, ← hslack]
          simp only [mul_zero, Finset.sum_const_zero, zero_add] at hβ
          linarith
        · exact Finset.sum_nonneg (fun r _ => mul_nonneg (hlamF r) (sub_nonneg.mpr (hxK r)))
      intro r
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => mul_nonneg (hlamF r)
        (sub_nonneg.mpr (hxK r)))).mp hsum r (Finset.mem_univ r)
    have cγ : ∀ i j, lamF (Sum.inl (i, j)) * x i j = 0 := by
      intro i j
      have := hterm (Sum.inl (i, j))
      rw [S2, hec] at this
      simp only [Sum.elim_inl] at this
      linarith
    have cLam : ∀ i, lamF (Sum.inr (Sum.inl i)) * (∑ j, x i j - 1) = 0 := by
      intro i
      have := hterm (Sum.inr (Sum.inl i))
      rw [S3, hec] at this
      simp only [Sum.elim_inr, Sum.elim_inl] at this
      linarith
    have cθ : ∀ j, I.cap j * lamF (Sum.inr (Sum.inr j)) * (level I y x j - 1) = 0 := by
      intro j
      have := hterm (Sum.inr (Sum.inr j))
      rw [S4, hec] at this
      simp only [Sum.elim_inr] at this
      have hc0 : I.cap j ≠ 0 := (I.cap_pos j).ne'
      have e : I.cap j * lamF (Sum.inr (Sum.inr j)) * (level I y x j - 1) =
          -(lamF (Sum.inr (Sum.inr j)) * (I.cap j * (1 - y j) - ∑ i, x i j)) := by
        unfold level
        rw [← Finset.sum_div]
        first | (field_simp; ring1) | field_simp
      rw [e]
      linarith
    have hLx : lagrangian I k y x (fun i => lamF (Sum.inr (Sum.inl i)))
        (fun j => I.cap j * lamF (Sum.inr (Sum.inr j))) (fun i j => lamF (Sum.inl (i, j))) =
        Phi I k y x := by
      rw [hlag]
      have h1 : (∑ i with I.batch i = k, lamF (Sum.inr (Sum.inl i)) * (∑ j, x i j - 1)) = 0 :=
        Finset.sum_eq_zero (fun i _ => cLam i)
      have h2 : (∑ j, I.cap j * lamF (Sum.inr (Sum.inr j)) * (level I y x j - 1)) = 0 :=
        Finset.sum_eq_zero (fun j _ => cθ j)
      have h3 : (∑ i, ∑ j, lamF (Sum.inl (i, j)) * x i j) = 0 :=
        Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => cγ i j))
      rw [h1, h2, h3]
      ring
    refine ⟨by rw [hLx, hobj], ?_⟩
    intro z hz
    rw [hobj, ← hLx, hlag, hlag]
    have hc : Phi I k y z ≤ Phi I k y x + ∑ i, ∑ j, g i j * (z i j - x i j) := by
      rw [hg]
      exact Phi_concave I k y x z
    have hA' := A_diff I k (fun i => lamF (Sum.inr (Sum.inl i))) z x
    have hB' := B_diff I (fun j => I.cap j * lamF (Sum.inr (Sum.inr j))) y z x
    have hC' := C_diff (fun i j => lamF (Sum.inl (i, j))) z x
    have hgrad : ∑ i, ∑ j, g i j * (z i j - x i j) =
        -(∑ i, ∑ j, lamF (Sum.inl (i, j)) * (z i j - x i j)) +
        (∑ i, ∑ j, (if I.batch i = k then lamF (Sum.inr (Sum.inl i)) else 0) * (z i j - x i j)) +
        (∑ i, ∑ j, I.cap j * lamF (Sum.inr (Sum.inr j)) / I.cap j * (z i j - x i j)) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      have hc0 : I.cap j ≠ 0 := (I.cap_pos j).ne'
      have hcc : I.cap j * lamF (Sum.inr (Sum.inr j)) / I.cap j = lamF (Sum.inr (Sum.inr j)) :=
        mul_div_cancel_left₀ _ hc0
      rw [hcc]
      by_cases hs : I.edge i j ∧ I.batch i = k
      · rw [hstat i j hs.1 hs.2, if_pos hs.2]
        ring
      · have hz0 : z i j = 0 := by
          by_contra hne; exact hs (hz i j hne)
        have hx0 : x i j = 0 := by
          by_contra hne; exact hs (hsupp i j hne)
        rw [hz0, hx0]
        ring
    linarith
  · ---------------- part 3
    intro lam θ γ hdn hmaxL
    obtain ⟨hdl, hdθ, hdγ⟩ := hdn
    obtain ⟨h1, h2, h3⟩ := pen lam θ γ ⟨hdl, hdθ, hdγ⟩
    have hLx := hmaxL x hsupp
    have hP1 := P1 lam θ γ ⟨hdl, hdθ, hdγ⟩
    rw [hobj, hlag] at hLx
    have eA : (∑ i with I.batch i = k, lam i * (∑ j, x i j - 1)) = 0 := by linarith
    have eB : (∑ j, θ j * (level I y x j - 1)) = 0 := by linarith
    have eC : (∑ i, ∑ j, γ i j * x i j) = 0 := by linarith
    have tA : ∀ i, I.batch i = k → lam i * (∑ j, x i j - 1) = 0 := by
      intro i hb
      have hle : ∀ i' ∈ Finset.univ.filter (fun i' => I.batch i' = k),
          lam i' * (∑ j, x i' j - 1) ≤ 0 := by
        intro i' hi'
        exact mul_nonpos_of_nonneg_of_nonpos (hdl i' (Finset.mem_filter.mp hi').2)
          (by linarith [hrow i'])
      exact (Finset.sum_eq_zero_iff_of_nonpos hle).mp eA i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    have tB : ∀ j, θ j * (level I y x j - 1) = 0 := by
      intro j
      have hle : ∀ j' ∈ (Finset.univ : Finset V), θ j' * (level I y x j' - 1) ≤ 0 :=
        fun j' _ => mul_nonpos_of_nonneg_of_nonpos (hdθ j') (by linarith [(hlev j').2])
      exact (Finset.sum_eq_zero_iff_of_nonpos hle).mp eB j (Finset.mem_univ _)
    have hγx : ∀ i j, 0 ≤ γ i j * x i j := by
      intro i j
      by_cases h0 : x i j = 0
      · rw [h0, mul_zero]
      · obtain ⟨he, hb⟩ := hsupp i j h0
        exact mul_nonneg (hdγ i j he hb) (hnn i j)
    have tC : ∀ i j, γ i j * x i j = 0 := by
      intro i j
      have hrow0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ =>
        Finset.sum_nonneg (fun j' _ => hγx i' j'))).mp eC i (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j' _ => hγx i j')).mp hrow0 j (Finset.mem_univ _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- stationarity
      intro i j he hb
      obtain ⟨d, hd⟩ : ∃ d : U → V → ℝ, d = fun i' j' => if i' = i ∧ j' = j then 1 else 0 :=
        ⟨_, rfl⟩
      have hzs : ∀ t : ℝ, StageSupported I k (fun i' j' => x i' j' + t * d i' j') := by
        intro t i' j' hne
        by_cases hx0 : x i' j' = 0
        · have hd0 : d i' j' ≠ 0 := by
            intro h0; apply hne; show x i' j' + t * d i' j' = 0; rw [hx0, h0]; ring
          simp only [hd] at hd0
          have hij : i' = i ∧ j' = j := by
            by_contra hn; exact hd0 (if_neg hn)
          obtain ⟨rfl, rfl⟩ := hij
          exact ⟨he, hb⟩
        · exact hsupp i' j' hx0
      -- derivative of t ↦ L(x + t d)
      have H1 := Phi_deriv I k y x d
      have H2 : HasDerivAt (fun t => ∑ i' with I.batch i' = k,
          lam i' * (∑ j', (x i' j' + t * d i' j') - 1))
          (∑ i' with I.batch i' = k, lam i' * ∑ j', 1 * d i' j') 0 := by
        apply HasDerivAt.fun_sum
        intro i' _
        apply HasDerivAt.const_mul
        apply HasDerivAt.sub_const
        apply HasDerivAt.fun_sum
        intro j' _
        exact ((hasDerivAt_id' 0).mul_const (d i' j')).const_add (x i' j')
      have H3 : HasDerivAt (fun t => ∑ j', θ j' *
          (level I y (fun i' j' => x i' j' + t * d i' j') j' - 1))
          (∑ j', θ j' * ∑ i', 1 * d i' j' / I.cap j') 0 := by
        apply HasDerivAt.fun_sum
        intro j' _
        apply HasDerivAt.const_mul
        apply HasDerivAt.sub_const
        unfold level
        apply HasDerivAt.const_add
        apply HasDerivAt.fun_sum
        intro i' _
        exact (((hasDerivAt_id' 0).mul_const (d i' j')).const_add (x i' j')).div_const (I.cap j')
      have H4 : HasDerivAt (fun t => ∑ i', ∑ j', γ i' j' * (x i' j' + t * d i' j'))
          (∑ i', ∑ j', γ i' j' * (1 * d i' j')) 0 := by
        apply HasDerivAt.fun_sum
        intro i' _
        apply HasDerivAt.fun_sum
        intro j' _
        exact (((hasDerivAt_id' 0).mul_const (d i' j')).const_add (x i' j')).const_mul (γ i' j')
      have H := ((H1.fun_sub H2).fun_sub H3).fun_add H4
      have hloc : IsLocalMax (fun t => lagrangian I k y (fun i' j' => x i' j' + t * d i' j') lam θ γ)
          0 := by
        apply Filter.Eventually.of_forall
        intro t
        have h0 : (fun i' j' => x i' j' + (0:ℝ) * d i' j') = x := by funext i' j'; ring
        show lagrangian I k y (fun i' j' => x i' j' + t * d i' j') lam θ γ ≤
          lagrangian I k y (fun i' j' => x i' j' + (0:ℝ) * d i' j') lam θ γ
        rw [h0]
        have := hmaxL _ (hzs t)
        rw [hobj] at this
        rw [hobj] at hP1
        linarith
      have hz := hloc.hasDerivAt_eq_zero H
      have e1 : ∑ i', ∑ j', I.w j' * (1 - MultiStageAlloc.slope K k (level I y x j')) * d i' j' =
          I.w j * (1 - MultiStageAlloc.slope K k (level I y x j)) := by
        simp only [hd]
        exact sum_single (fun i' j' => I.w j' * (1 - MultiStageAlloc.slope K k (level I y x j'))) i j
      have e2 : (∑ i' with I.batch i' = k, lam i' * ∑ j', 1 * d i' j') = lam i := by
        rw [Finset.sum_filter]
        simp only [hd]
        have : ∑ i', ∑ j', (if I.batch i' = k then lam i' else 0) *
            (if i' = i ∧ j' = j then (1:ℝ) else 0) = (if I.batch i = k then lam i else 0) :=
          sum_single (fun i' j' => (if I.batch i' = k then lam i' else 0)) i j
        rw [if_pos hb] at this
        rw [← this]
        apply Finset.sum_congr rfl; intro i' _
        split_ifs with h
        · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j' _; ring
        · simp
      have e3 : (∑ j', θ j' * ∑ i', 1 * d i' j' / I.cap j') = θ j / I.cap j := by
        simp only [hd]
        have : ∑ i', ∑ j', θ j' / I.cap j' * (if i' = i ∧ j' = j then (1:ℝ) else 0) =
            θ j / I.cap j := sum_single (fun i' j' => θ j' / I.cap j') i j
        rw [← this, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j' _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i' _
        ring
      have e4 : (∑ i', ∑ j', γ i' j' * (1 * d i' j')) = γ i j := by
        simp only [hd]
        have : ∑ i', ∑ j', γ i' j' * (if i' = i ∧ j' = j then (1:ℝ) else 0) = γ i j :=
          sum_single γ i j
        rw [← this]
        apply Finset.sum_congr rfl; intro i' _
        apply Finset.sum_congr rfl; intro j' _
        ring
      rw [e1, e2, e3, e4] at hz
      exact hz
    · intro i j he hb
      rcases eq_or_lt_of_le (hdγ i j he hb) with h | h
      · exact Or.inl h.symm
      · right
        refine ⟨h, ?_⟩
        have := tC i j
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · exact h'
    · intro i hb
      rcases eq_or_lt_of_le (hdl i hb) with h | h
      · exact Or.inl h.symm
      · right
        refine ⟨h, ?_⟩
        have := tA i hb
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · linarith
    · intro j
      rcases eq_or_lt_of_le (hdθ j) with h | h
      · exact Or.inl h.symm
      · right
        refine ⟨h, ?_⟩
        have := tB j
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · linarith
