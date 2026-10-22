-- Prove2me | solution 1 for ModernConvex.LPDuality.lp_duality_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:47:20.622191+00:00
-- url     : https://prove2.me/submissions/eb6e85cc-f11c-427f-a911-59bd148f6c29

import Mathlib
import Definitions.Def_ModernConvex_LPDuality_LinearProgram

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

theorem g69a1_lp_dualG {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (b : ι → ℝ) (c : κ → ℝ)
    (hfeas : ∃ x0, b ≤ A *ᵥ x0) (a : ℝ) (hlb : ∀ x, b ≤ A *ᵥ x → a ≤ c ⬝ᵥ x) :
    ∃ y : ι → ℝ, 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ a ≤ b ⬝ᵥ y := by
  classical
  obtain ⟨x0, hx0⟩ := hfeas
  let w : Option ι → (κ ⊕ Unit → ℝ) := fun o =>
    match o with
    | none => Sum.elim 0 (fun _ => 1)
    | some i => Sum.elim (fun j => A i j) (fun _ => -b i)
  let q : κ ⊕ Unit → ℝ := Sum.elim c (fun _ => -a)
  have hno : ¬ ∃ z : κ ⊕ Unit → ℝ, q ⬝ᵥ z < 0 ∧ ∀ o, 0 ≤ w o ⬝ᵥ z := by
    rintro ⟨z, hz, hw⟩
    set x : κ → ℝ := fun j => z (Sum.inl j) with hxdef
    set t : ℝ := z (Sum.inr ()) with htdef
    have hqz : q ⬝ᵥ z = c ⬝ᵥ x - a * t := by
      simp [q, dotProduct, Fintype.sum_sum_type, x, t]; ring
    have ht0 : 0 ≤ t := by
      have := hw none
      simpa [w, dotProduct, Fintype.sum_sum_type, t] using this
    have hAx : ∀ i, b i * t ≤ (A *ᵥ x) i := by
      intro i
      have := hw (some i)
      simp [w, dotProduct, Fintype.sum_sum_type, t] at this
      simp only [mulVec, dotProduct, x]
      linarith
    rcases ht0.lt_or_eq with htpos | htz
    · have hfe : b ≤ A *ᵥ (t⁻¹ • x) := by
        intro i
        rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, le_inv_mul_iff₀ htpos]
        linarith [hAx i]
      have := hlb _ hfe
      rw [dotProduct_smul, smul_eq_mul, le_inv_mul_iff₀ htpos] at this
      linarith
    · have hcx : c ⬝ᵥ x < 0 := by rw [← htz] at hqz; linarith
      have hAx0 : ∀ i, 0 ≤ (A *ᵥ x) i := by
        intro i; have := hAx i; rw [← htz] at this; simpa using this
      have hca := hlb x0 hx0
      set s : ℝ := (c ⬝ᵥ x0 - a + 1) / (-(c ⬝ᵥ x)) with hs
      have hspos : 0 ≤ s := div_nonneg (by linarith) (by linarith)
      have hfe : b ≤ A *ᵥ (x0 + s • x) := by
        intro i
        rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hx0 i
        nlinarith [hAx0 i]
      have := hlb _ hfe
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hs, div_mul_eq_mul_div,
        div_neg, mul_div_assoc, div_self hcx.ne, mul_one] at this
      linarith
  have hmem : ∃ l : Option ι → ℝ, (∀ o, 0 ≤ l o) ∧ q = ∑ o, l o • w o := by
    by_contra hne
    exact hno (g69a1_farkas w q hne)
  obtain ⟨l, hl, hq⟩ := hmem
  refine ⟨fun i => l (some i), fun i => hl (some i), ?_, ?_⟩
  · funext j
    have := congrFun hq (Sum.inl j)
    simp [q, w, Finset.sum_apply, Fintype.sum_option] at this
    rw [this]
    simp [mulVec, dotProduct, mul_comm]
  · have := congrFun hq (Sum.inr ())
    simp [q, w, Finset.sum_apply, Fintype.sum_option] at this
    have h1 := hl none
    simp only [dotProduct]
    have h2 : ∑ x, l (some x) * b x = ∑ x, b x * l (some x) := by
      apply Finset.sum_congr rfl; intro i _; ring
    linarith

theorem g69a1_weak {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y : Fin m → ℝ)
    (hy : 0 ≤ y) (x : Fin n → ℝ) (hx : b ≤ A *ᵥ x) : b ⬝ᵥ y ≤ (Aᵀ *ᵥ y) ⬝ᵥ x := by
  rw [mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy i)

open ModernConvex.LPDuality

theorem g69a1_M_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) :
    dualAsLPMatrix A *ᵥ y = Sum.elim y (Sum.elim (Aᵀ *ᵥ y) (-(Aᵀ *ᵥ y))) := by
  ext r
  rcases r with i | j | j <;>
    simp [dualAsLPMatrix, mulVec, dotProduct, Matrix.one_apply]

theorem g69a1_MT_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ) :
    (dualAsLPMatrix A)ᵀ *ᵥ w = (fun i => w (Sum.inl i)) +
      A *ᵥ (fun j => w (Sum.inr (Sum.inl j))) - A *ᵥ (fun j => w (Sum.inr (Sum.inr j))) := by
  ext i
  simp [dualAsLPMatrix, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply,
    Finset.sum_neg_distrib, mul_comm]
  ring

theorem g69a1_rhs_dot {m n : ℕ} (c : Fin n → ℝ) (w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ) :
    dualAsLPRhs c ⬝ᵥ w = -(c ⬝ᵥ (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j)))) := by
  simp [dualAsLPRhs, dotProduct, Fintype.sum_sum_type, mul_sub, Finset.sum_sub_distrib]
  ring

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    -- 1. the duality is symmetric
    ((∀ y : Fin m → ℝ,
        PrimalFeasible (dualAsLPMatrix A) (dualAsLPRhs (m := Fin m) c) y ↔ DualFeasible A c y) ∧
      (∀ w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ, DualFeasible (dualAsLPMatrix A) (-b) w →
        PrimalFeasible A b (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))) ∧
        dualAsLPRhs c ⬝ᵥ w =
          -(c ⬝ᵥ (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))))) ∧
      (∀ x : Fin n → ℝ, PrimalFeasible A b x →
        ∃ w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ, DualFeasible (dualAsLPMatrix A) (-b) w ∧
          (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))) = x ∧
          dualAsLPRhs c ⬝ᵥ w = -(c ⬝ᵥ x))) ∧
    -- 2. weak duality
    (∀ (x : Fin n → ℝ) (y : Fin m → ℝ), PrimalFeasible A b x → DualFeasible A c y →
      b ⬝ᵥ y ≤ c ⬝ᵥ x) ∧
    -- 3. (i) ≡ (ii) ≡ (iii) ≡ (iv) ≡ (v)
    [PrimalIsFeasible A b ∧ PrimalBoundedBelow A b c,
      DualIsFeasible A c ∧ DualBoundedAbove A b c,
      PrimalSolvable A b c,
      DualSolvable A b c,
      PrimalIsFeasible A b ∧ DualIsFeasible A c].TFAE ∧
    -- ... and then the optimal values of the primal and the dual are equal
    (PrimalIsFeasible A b ∧ PrimalBoundedBelow A b c →
      ∃ v : ℝ, IsPrimalOptimalValue A b c v ∧ IsDualOptimalValue A b c v) := by
  classical
  -- symmetry facts
  have S1 : ∀ y : Fin m → ℝ,
      PrimalFeasible (dualAsLPMatrix A) (dualAsLPRhs (m := Fin m) c) y ↔ DualFeasible A c y := by
    intro y
    unfold PrimalFeasible DualFeasible
    rw [g69a1_M_apply]
    constructor
    · intro h
      refine ⟨?_, fun i => by simpa [dualAsLPRhs] using h (Sum.inl i)⟩
      ext j
      have h1 := h (Sum.inr (Sum.inl j))
      have h2 := h (Sum.inr (Sum.inr j))
      simp [dualAsLPRhs] at h1 h2
      linarith
    · rintro ⟨h1, h2⟩ r
      rcases r with i | j | j
      · simpa [dualAsLPRhs] using h2 i
      · simp [dualAsLPRhs, h1]
      · simp [dualAsLPRhs, h1]
  have S2 : ∀ w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ, DualFeasible (dualAsLPMatrix A) (-b) w →
      PrimalFeasible A b (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))) ∧
      dualAsLPRhs c ⬝ᵥ w =
        -(c ⬝ᵥ (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j)))) := by
    rintro w ⟨hT, hw⟩
    refine ⟨?_, g69a1_rhs_dot c w⟩
    rw [g69a1_MT_apply] at hT
    intro i
    have h := congrFun hT i
    have h0 : 0 ≤ w (Sum.inl i) := hw (Sum.inl i)
    have hsub : A *ᵥ (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))) =
        A *ᵥ (fun j => w (Sum.inr (Sum.inr j))) - A *ᵥ (fun j => w (Sum.inr (Sum.inl j))) := by
      rw [← mulVec_sub]; rfl
    rw [hsub]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at h ⊢
    linarith
  have S3 : ∀ x : Fin n → ℝ, PrimalFeasible A b x →
      ∃ w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ, DualFeasible (dualAsLPMatrix A) (-b) w ∧
        (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))) = x ∧
        dualAsLPRhs c ⬝ᵥ w = -(c ⬝ᵥ x) := by
    intro x hx
    let w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ :=
      Sum.elim (A *ᵥ x - b) (Sum.elim (fun j => max (-x j) 0) (fun j => max (x j) 0))
    have hx' : (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))) = x := by
      ext j
      show max (x j) 0 - max (-x j) 0 = x j
      rcases le_total 0 (x j) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    refine ⟨w, ⟨?_, ?_⟩, hx', ?_⟩
    · rw [g69a1_MT_apply]
      have hsub : A *ᵥ (fun j => w (Sum.inr (Sum.inl j))) - A *ᵥ (fun j => w (Sum.inr (Sum.inr j)))
          = -(A *ᵥ x) := by
        rw [← mulVec_sub, ← mulVec_neg]
        congr 1
        rw [← hx']
        ext j; simp
      rw [add_sub_assoc, hsub]
      ext i
      simp [w]
      ring
    · intro r
      rcases r with i | j | j
      · simp only [w, Sum.elim_inl, Pi.zero_apply, Pi.sub_apply]; linarith [hx i]
      · simp [w]
      · simp [w]
    · rw [g69a1_rhs_dot, hx']
  have WD : ∀ (x : Fin n → ℝ) (y : Fin m → ℝ), PrimalFeasible A b x → DualFeasible A c y →
      b ⬝ᵥ y ≤ c ⬝ᵥ x := by
    rintro x y hx ⟨hAy, hy⟩
    have := g69a1_weak A b y hy x hx
    rwa [hAy] at this
  -- P ⇒ D
  have PD : PrimalIsFeasible A b ∧ PrimalBoundedBelow A b c →
      DualIsFeasible A c ∧ DualBoundedAbove A b c := by
    rintro ⟨⟨x0, hx0⟩, ⟨L, hL⟩⟩
    obtain ⟨y, hy, hAy, -⟩ := g69a1_lp_dualG A b c ⟨x0, hx0⟩ L hL
    exact ⟨⟨y, hAy, hy⟩, ⟨c ⬝ᵥ x0, fun y' hy' => WD x0 y' hx0 hy'⟩⟩
  -- D ⇒ PS
  have DPS : DualIsFeasible A c ∧ DualBoundedAbove A b c → PrimalSolvable A b c := by
    rintro ⟨⟨y0, hy0⟩, ⟨U, hU⟩⟩
    set T : Set ℝ := {t | ∃ y, DualFeasible A c y ∧ t = b ⬝ᵥ y} with hT
    have hTne : T.Nonempty := ⟨_, y0, hy0, rfl⟩
    have hTbdd : BddAbove T := ⟨U, by rintro _ ⟨y, hy, rfl⟩; exact hU y hy⟩
    set d := sSup T
    have hle : ∀ y, DualFeasible A c y → b ⬝ᵥ y ≤ d := fun y hy => le_csSup hTbdd ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hMw, hdw⟩ := g69a1_lp_dualG (dualAsLPMatrix A) (dualAsLPRhs (m := Fin m) c)
      (-b) ⟨y0, (S1 y0).mpr hy0⟩ (-d) (by
        intro y hy
        have := hle y ((S1 y).mp hy)
        rw [neg_dotProduct]; linarith)
    obtain ⟨hxf, hval⟩ := S2 w ⟨hMw, hw⟩
    set x := (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j)))
    refine ⟨x, hxf, fun x' hx' => ?_⟩
    have h1 : d ≤ c ⬝ᵥ x' := csSup_le hTne (by rintro _ ⟨y, hy, rfl⟩; exact WD x' y hx' hy)
    rw [hval] at hdw
    linarith
  -- PS ⇒ DS (with equal values)
  have PSDS : ∀ x0, IsPrimalOptimal A b c x0 → ∃ y0, IsDualOptimal A b c y0 ∧
      b ⬝ᵥ y0 = c ⬝ᵥ x0 := by
    rintro x0 ⟨hx0, hopt⟩
    obtain ⟨y, hy, hAy, hv⟩ := g69a1_lp_dualG A b c ⟨x0, hx0⟩ (c ⬝ᵥ x0) hopt
    have hd : DualFeasible A c y := ⟨hAy, hy⟩
    have := WD x0 y hx0 hd
    refine ⟨y, ⟨hd, fun y' hy' => ?_⟩, by linarith⟩
    have := WD x0 y' hx0 hy'
    linarith
  refine ⟨⟨S1, S2, S3⟩, WD, ?_, ?_⟩
  · tfae_have 1 → 2 := PD
    tfae_have 2 → 3 := DPS
    tfae_have 3 → 4 := by
      rintro ⟨x0, hx0⟩
      obtain ⟨y0, hy0, -⟩ := PSDS x0 hx0
      exact ⟨y0, hy0⟩
    tfae_have 4 → 2 := by
      rintro ⟨y0, hy0, hopt⟩
      exact ⟨⟨y0, hy0⟩, ⟨b ⬝ᵥ y0, hopt⟩⟩
    tfae_have 3 → 1 := by
      rintro ⟨x0, hx0, hopt⟩
      exact ⟨⟨x0, hx0⟩, ⟨c ⬝ᵥ x0, hopt⟩⟩
    tfae_have 1 → 5 := fun h => ⟨h.1, (PD h).1⟩
    tfae_have 5 → 1 := by
      rintro ⟨⟨x0, hx0⟩, ⟨y0, hy0⟩⟩
      exact ⟨⟨x0, hx0⟩, ⟨b ⬝ᵥ y0, fun x hx => WD x y0 hx hy0⟩⟩
    tfae_finish
  · intro h
    obtain ⟨x0, hx0⟩ := DPS (PD h)
    obtain ⟨y0, ⟨hy0, hyopt⟩, heq⟩ := PSDS x0 hx0
    refine ⟨c ⬝ᵥ x0, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rintro _ ⟨x, hx, rfl⟩; exact hx0.2 x hx
    · intro v hv; exact hv ⟨x0, hx0.1, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩; exact WD x0 y hx0.1 hy
    · intro v hv; rw [← heq]; exact hv ⟨y0, hy0, rfl⟩
