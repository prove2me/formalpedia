-- Prove2me | solution 1 for ModernConvex.LPDuality.theorem_on_alternative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:09:08.561019+00:00
-- url     : https://prove2.me/submissions/9c1c8162-d491-4952-9bb2-b75376d4a631

import Mathlib
import Definitions.Def_ModernConvex_LPDuality_AlternativeSystems

open Matrix

theorem g69a1_cara {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E] (v : ι → E)
    (t : Finset ι) : ∀ l : ι → ℝ, (∀ i, 0 ≤ l i) → ∃ s ⊆ t, ∃ l' : ι → ℝ, (∀ i, 0 ≤ l' i) ∧
      LinearIndepOn ℝ v (s : Set ι) ∧ ∑ i ∈ s, l' i • v i = ∑ i ∈ t, l i • v i := by
  induction t using Finset.strongInduction with
  | H t ih =>
  intro l hl
  by_cases hli : LinearIndepOn ℝ v (t : Set ι)
  · exact ⟨t, subset_rfl, l, hl, hli, rfl⟩
  rw [not_linearIndepOn_finset_iffₛ] at hli
  obtain ⟨f, g, hfg, i0, hi0t, hi0⟩ := hli
  have hsum0 : ∑ i ∈ t, (f i - g i) • v i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hfg, sub_self]
  -- get ν supported on t with positive entry
  obtain ⟨ν, hνsum, hνsupp, i1, hi1t, hi1⟩ : ∃ ν : ι → ℝ, ∑ i ∈ t, ν i • v i = 0 ∧
      (∀ i, i ∉ t → ν i = 0) ∧ ∃ i ∈ t, 0 < ν i := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hi0) with h | h
    · refine ⟨fun i => if i ∈ t then -(f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then -(f i - g i) else 0) • v i = -((f i - g i) • v i) := by
          intro i hi; rw [if_pos hi, neg_smul]
        beta_reduce
        rw [Finset.sum_congr rfl hc, Finset.sum_neg_distrib, hsum0, neg_zero]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
    · refine ⟨fun i => if i ∈ t then (f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then (f i - g i) else 0) • v i = (f i - g i) • v i := by
          intro i hi; rw [if_pos hi]
        beta_reduce
        rw [Finset.sum_congr rfl hc, hsum0]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
  set P := t.filter (fun i => 0 < ν i) with hP
  have hPne : P.Nonempty := ⟨i1, by simp [hP, hi1t, hi1]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image P (fun i => l i / ν i) hPne
  have hjt : j ∈ t := (Finset.mem_filter.mp hjP).1
  have hjpos : 0 < ν j := (Finset.mem_filter.mp hjP).2
  set θ := l j / ν j with hθ
  have hθnn : 0 ≤ θ := div_nonneg (hl j) hjpos.le
  set l' : ι → ℝ := fun i => l i - θ * ν i with hl'
  have hl'nn : ∀ i, 0 ≤ l' i := by
    intro i
    simp only [hl']
    by_cases hit : i ∈ t
    · by_cases hνi : 0 < ν i
      · have hiP : i ∈ P := by simp [hP, hit, hνi]
        have := hjmin i hiP
        rw [le_div_iff₀ hνi] at this
        linarith
      · push Not at hνi
        nlinarith [hl i]
    · rw [hνsupp i hit]; simp [hl i]
  have hl'j : l' j = 0 := by
    simp only [hl', hθ]; field_simp; ring
  have hsum' : ∑ i ∈ t.erase j, l' i • v i = ∑ i ∈ t, l i • v i := by
    rw [Finset.sum_erase _ (by rw [hl'j, zero_smul])]
    simp only [hl', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hνsum,
      smul_zero, sub_zero]
  obtain ⟨s, hs, l'', hl'', hli, hs'⟩ := ih (t.erase j) (Finset.erase_ssubset hjt) l' hl'nn
  exact ⟨s, hs.trans (Finset.erase_subset _ _), l'', hl'', hli, hs'.trans hsum'⟩

theorem g69a1_cone_closed {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] (v : ι → κ → ℝ) :
    IsClosed {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} := by
  classical
  have heq : {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} =
      ⋃ s ∈ {s : Finset ι | LinearIndepOn ℝ v (s : Set ι)},
        (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) '' {m | ∀ i, 0 ≤ m i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨s, -, l', hl', hli, hs⟩ := g69a1_cara v Finset.univ l hl
      refine ⟨s, hli, fun i => l' i, fun i => hl' i, ?_⟩
      rw [Fintype.linearCombination_apply, ← hs]
      exact (Finset.sum_coe_sort s (fun i => l' i • v i))
    · rintro ⟨s, -, m, hm, rfl⟩
      refine ⟨fun i => if h : i ∈ s then m ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i; by_cases h : i ∈ s <;> simp [h, hm]
      · rw [Fintype.linearCombination_apply]
        rw [← Finset.sum_subset (Finset.subset_univ s)]
        · rw [← Finset.sum_coe_sort s]
          apply Finset.sum_congr rfl
          intro i _
          simp
        · intro i _ hi; simp [hi]
  rw [heq]
  apply Set.Finite.isClosed_biUnion (Set.toFinite _)
  intro s hs
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (linearIndependent_iff_injective_fintypeLinearCombination).mp hs
  apply (LinearMap.isClosedEmbedding_of_injective hinj).isClosedMap
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

theorem g69a1_farkas {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : ι → κ → ℝ) (a : κ → ℝ)
    (ha : ¬ ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ a = ∑ i, l i • v i) :
    ∃ x : κ → ℝ, a ⬝ᵥ x < 0 ∧ ∀ i, 0 ≤ v i ⬝ᵥ x := by
  classical
  set C := {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} with hC
  have hconv : Convex ℝ C := by
    rintro y ⟨l, hl, rfl⟩ z ⟨m, hm, rfl⟩ α β hα hβ _
    refine ⟨fun i => α * l i + β * m i, fun i => by have := hl i; have := hm i; positivity, ?_⟩
    simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]
  obtain ⟨f, u, hfa, hfC⟩ := geometric_hahn_banach_point_closed hconv (g69a1_cone_closed v) ha
  have hu : u < 0 := by
    have := hfC 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hfnn : ∀ y ∈ C, 0 ≤ f y := by
    intro y hy
    by_contra hneg
    push Not at hneg
    obtain ⟨l, hl, rfl⟩ := hy
    set t : ℝ := u / f (∑ i, l i • v i) with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg hu hneg
    have hmem : t • (∑ i, l i • v i) ∈ C :=
      ⟨fun i => t * l i, fun i => mul_nonneg htpos.le (hl i), by
        simp only [Finset.smul_sum, mul_smul]⟩
    have := hfC _ hmem
    rw [map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  let x : κ → ℝ := fun j => f (Pi.single j 1)
  have hfx : ∀ y : κ → ℝ, f y = y ⬝ᵥ x := by
    intro y
    conv_lhs => rw [show y = ∑ j, y j • Pi.single j (1:ℝ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, dotProduct, x]
  refine ⟨x, ?_, ?_⟩
  · rw [← hfx]; linarith
  · intro i
    rw [← hfx]
    apply hfnn
    refine ⟨Pi.single i 1, fun j => ?_, ?_⟩
    · by_cases h : j = i <;> simp [Pi.single_apply, h]
    · simp [Pi.single_apply]

theorem g69a1_alt {m n : ℕ} (ms : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (h : ¬ ∃ x : Fin n → ℝ, ∀ i : Fin m,
      ((i : ℕ) < ms → b i < a i ⬝ᵥ x) ∧ (ms ≤ (i : ℕ) → b i ≤ a i ⬝ᵥ x)) :
    ∃ l : Fin m → ℝ, 0 ≤ l ∧ ∑ i, l i • a i = 0 ∧
      ((0 ≤ ∑ i, l i * b i ∧ 0 < ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < ms), l i)
        ∨ 0 < ∑ i, l i * b i) := by
  classical
  let w : Option (Fin m) → (Fin n ⊕ Fin 2 → ℝ) := fun o =>
    match o with
    | none => Sum.elim 0 ![1, -1]
    | some i => Sum.elim (a i) ![-b i, if (i : ℕ) < ms then -1 else 0]
  let c : Fin n ⊕ Fin 2 → ℝ := Sum.elim 0 ![0, -1]
  have hno : ¬ ∃ z : Fin n ⊕ Fin 2 → ℝ, c ⬝ᵥ z < 0 ∧ ∀ o, 0 ≤ w o ⬝ᵥ z := by
    rintro ⟨z, hz, hw⟩
    apply h
    have hs : 0 < z (Sum.inr 1) := by
      simp [c, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at hz
      linarith
    have hts : z (Sum.inr 1) ≤ z (Sum.inr 0) := by
      have := hw none
      simp [w, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at this
      linarith
    have ht : 0 < z (Sum.inr 0) := lt_of_lt_of_le hs hts
    refine ⟨(z (Sum.inr 0))⁻¹ • (fun j => z (Sum.inl j)), fun i => ?_⟩
    have hi := hw (some i)
    simp only [w, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] at hi
    have hdot : a i ⬝ᵥ ((z (Sum.inr 0))⁻¹ • (fun j => z (Sum.inl j))) =
        (z (Sum.inr 0))⁻¹ * ∑ j, a i j * z (Sum.inl j) := by
      rw [dotProduct_smul, smul_eq_mul]; rfl
    rw [hdot]
    constructor
    · intro hlt
      rw [if_pos hlt] at hi
      rw [lt_inv_mul_iff₀ ht]
      nlinarith
    · intro hle
      by_cases hlt : (i : ℕ) < ms
      · rw [if_pos hlt] at hi
        rw [le_inv_mul_iff₀ ht]
        nlinarith
      · rw [if_neg hlt] at hi
        rw [le_inv_mul_iff₀ ht]
        nlinarith
  have hmem : ∃ l : Option (Fin m) → ℝ, (∀ o, 0 ≤ l o) ∧ c = ∑ o, l o • w o := by
    by_contra hne
    exact hno (g69a1_farkas w c hne)
  obtain ⟨l, hl, hc⟩ := hmem
  have hx : ∑ i, l (some i) • a i = 0 := by
    funext j
    have := congrFun hc (Sum.inl j)
    simp [c, w, Finset.sum_apply, Fintype.sum_option] at this
    simp [Finset.sum_apply, this]
  have h0 := congrFun hc (Sum.inr 0)
  simp [c, w, Finset.sum_apply, Fintype.sum_option] at h0
  have h1 := congrFun hc (Sum.inr 1)
  simp [c, w, Finset.sum_apply, Fintype.sum_option] at h1
  have hfilt : ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < ms), l (some i) =
      ∑ i, l (some i) * (if (i : ℕ) < ms then 1 else 0) := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  refine ⟨fun i => l (some i), fun i => hl (some i), hx, ?_⟩
  rcases (hl none).lt_or_eq with hpos | hzero
  · right
    show 0 < ∑ i, l (some i) * b i
    linarith
  · left
    have h2 : ∑ x : Fin m, (if (x : ℕ) < ms then -l (some x) else 0) =
        -∑ i, l (some i) * (if (i : ℕ) < ms then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
    refine ⟨?_, ?_⟩
    · show 0 ≤ ∑ i, l (some i) * b i
      linarith
    · show 0 < ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < ms), l (some i)
      linarith

open ModernConvex.LPDuality

theorem solution {m n : ℕ} (ms : ℕ) (hms : ms ≤ m) (a : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) :
    (¬ ∃ x : Fin n → ℝ, SystemS ms a b x) ↔
      (∃ l : Fin m → ℝ, SystemTI ms a b l) ∨ (∃ l : Fin m → ℝ, SystemTII a b l) := by
  constructor
  · intro h
    obtain ⟨l, hl0, hsum, h1 | h2⟩ := g69a1_alt ms a b h
    · exact Or.inl ⟨l, hl0, hsum, h1.1, h1.2⟩
    · exact Or.inr ⟨l, hl0, hsum, h2⟩
  · intro hT
    rintro ⟨x, hx⟩
    have hge : ∀ i, b i ≤ a i ⬝ᵥ x := by
      intro i
      by_cases h : (i : ℕ) < ms
      · exact ((hx i).1 h).le
      · exact (hx i).2 (by omega)
    have hdot : ∀ l : Fin m → ℝ, (∑ i, l i • a i) ⬝ᵥ x = ∑ i, l i * (a i ⬝ᵥ x) := by
      intro l; simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul]
    rcases hT with ⟨l, hl0, hsum, hb, hpos⟩ | ⟨l, hl0, hsum, hb⟩
    · have hz : ∑ i, l i * (a i ⬝ᵥ x) = 0 := by rw [← hdot, hsum, zero_dotProduct]
      have hdiff : 0 < ∑ i, l i * (a i ⬝ᵥ x - b i) := by
        by_contra hc
        push Not at hc
        have hall : ∀ i, 0 ≤ l i * (a i ⬝ᵥ x - b i) :=
          fun i => mul_nonneg (hl0 i) (by linarith [hge i])
        have hzero : ∀ i ∈ Finset.univ, l i * (a i ⬝ᵥ x - b i) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hall i)).mp (le_antisymm hc
            (Finset.sum_nonneg fun i _ => hall i))
        have : ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < ms), l i ≤ 0 := by
          apply Finset.sum_nonpos
          intro i hi
          simp only [Finset.mem_filter] at hi
          have h1 := hzero i (Finset.mem_univ _)
          have h2 := (hx i).1 hi.2
          rcases mul_eq_zero.mp h1 with h | h
          · exact h.le
          · linarith
        linarith
      simp only [mul_sub, Finset.sum_sub_distrib] at hdiff
      linarith
    · have hz : ∑ i, l i * (a i ⬝ᵥ x) = 0 := by rw [← hdot, hsum, zero_dotProduct]
      have : ∑ i, l i * b i ≤ ∑ i, l i * (a i ⬝ᵥ x) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hge i) (hl0 i)
      linarith
