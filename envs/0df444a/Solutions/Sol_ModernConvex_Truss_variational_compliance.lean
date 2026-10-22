-- Prove2me | solution 1 for ModernConvex.Truss.variational_compliance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:38:57.43555+00:00
-- url     : https://prove2.me/submissions/dd9c14d8-d04b-4a43-8a19-c742666055b1

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

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
theorem g69a1_Qexp {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hs : ∀ v w : Fin m → ℝ, v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v)) (b v w : Fin m → ℝ) (t : ℝ) :
    (1 / 2 : ℝ) * ((v + t • w) ⬝ᵥ (A *ᵥ (v + t • w))) - b ⬝ᵥ (v + t • w) =
      ((1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v)) - b ⬝ᵥ v) + t * (w ⬝ᵥ (A *ᵥ v) - b ⬝ᵥ w) +
        (1 / 2 : ℝ) * t ^ 2 * (w ⬝ᵥ (A *ᵥ w)) := by
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  rw [hs v w]
  ring

theorem g69a1_range_of_bdd {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hsym : Aᵀ = A)
    (hs : ∀ v w : Fin m → ℝ, v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v)) (b : Fin m → ℝ) (L : ℝ)
    (hL : ∀ v, L ≤ (1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v)) - b ⬝ᵥ v) : ∃ v, A *ᵥ v = b := by
  classical
  by_contra hne
  let gen : Fin m ⊕ Fin m → (Fin m → ℝ) := fun o =>
    match o with
    | Sum.inl j => fun i => A i j
    | Sum.inr j => -(fun i => A i j)
  have hncone : ¬ ∃ l : Fin m ⊕ Fin m → ℝ, (∀ o, 0 ≤ l o) ∧ b = ∑ o, l o • gen o := by
    rintro ⟨l, -, hl⟩
    apply hne
    refine ⟨fun j => l (Sum.inl j) - l (Sum.inr j), ?_⟩
    rw [hl]
    ext i
    simp [gen, Fintype.sum_sum_type, mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
      Finset.sum_apply, mul_comm] <;> ring
  obtain ⟨x, hbx, hx⟩ := g69a1_farkas gen b hncone
  have hAx : A *ᵥ x = 0 := by
    have hcol : ∀ j, (fun i => A i j) ⬝ᵥ x = 0 := by
      intro j
      have h1 := hx (Sum.inl j)
      have h2 := hx (Sum.inr j)
      simp only [gen, neg_dotProduct] at h1 h2
      linarith
    rw [← hsym]
    ext j
    have := hcol j
    simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply] at this ⊢
    exact this
  have key := hL (0 + ((1 - L) / (b ⬝ᵥ x)) • x)
  rw [g69a1_Qexp A hs b 0 x] at key
  simp only [hAx, mulVec_zero, dotProduct_zero, zero_dotProduct] at key
  have hne0 : b ⬝ᵥ x ≠ 0 := hbx.ne
  have e : (1 - L) / b ⬝ᵥ x * (0 - b ⬝ᵥ x) = -(1 - L) := by
    rw [zero_sub, mul_neg, div_mul_cancel₀ _ hne0]
  rw [e] at key
  linarith

open ModernConvex.Truss

theorem g69a1_stiff_sym {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) :
    (stiffness B t)ᵀ = stiffness B t := by
  unfold stiffness
  rw [transpose_sum]
  simp [transpose_smul, transpose_mul, transpose_transpose]

theorem g69a1_stiff_psd {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ (stiffness B t *ᵥ v) := by
  unfold stiffness
  rw [sum_mulVec, dotProduct_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
  apply mul_nonneg (ht i)
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg _

theorem solution {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (f : Fin m → ℝ) (t : Fin n → ℝ)
    (ht : 0 ≤ t) :
    ((∃ c : ℝ, compliance B f t = (c : EReal)) ↔ BddBelow (Set.range (potentialEnergy B t f))) ∧
    (∀ c : ℝ, compliance B f t = (c : EReal) →
      (∃ v, potentialEnergy B t f v = -c) ∧ ∀ v, -c ≤ potentialEnergy B t f v) := by
  classical
  set A := stiffness B t with hAdef
  have hsym : Aᵀ = A := g69a1_stiff_sym B t
  have hs : ∀ v w : Fin m → ℝ, v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v) := by
    intro v w
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  have hpsd : ∀ x : Fin m → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := g69a1_stiff_psd B t ht
  have hPE : ∀ v, potentialEnergy B t f v = (1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v)) - f ⬝ᵥ v :=
    fun v => rfl
  have K1 : ∀ v₀, A *ᵥ v₀ = f → ∀ v, potentialEnergy B t f v₀ ≤ potentialEnergy B t f v := by
    intro v₀ hv₀ v
    rw [hPE, hPE]
    have := g69a1_Qexp A hs f v₀ (v - v₀) 1
    rw [one_smul, add_sub_cancel] at this
    rw [this, hv₀, dotProduct_comm (v - v₀) f]
    have := hpsd (v - v₀)
    nlinarith
  have K1v : ∀ v₀, A *ᵥ v₀ = f → potentialEnergy B t f v₀ = -((1 / 2 : ℝ) * (f ⬝ᵥ v₀)) := by
    intro v₀ hv₀
    rw [hPE, hv₀, dotProduct_comm v₀ f]
    ring
  have hcomp : ∀ c : ℝ, compliance B f t = (c : EReal) →
      ∃ v₀, A *ᵥ v₀ = f ∧ c = (1 / 2 : ℝ) * (f ⬝ᵥ v₀) := by
    intro c hc
    unfold compliance at hc
    split_ifs at hc with h
    · exact ⟨h.choose, h.choose_spec, (EReal.coe_injective hc).symm⟩
    · exact absurd hc.symm (EReal.coe_ne_top c)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨c, hc⟩
    obtain ⟨v₀, hv₀, -⟩ := hcomp c hc
    exact ⟨potentialEnergy B t f v₀, by rintro _ ⟨v, rfl⟩; exact K1 v₀ hv₀ v⟩
  · rintro ⟨L, hL⟩
    have h : ∃ v, stiffness B t *ᵥ v = f :=
      g69a1_range_of_bdd A hsym hs f L (fun v => hL (Set.mem_range_self v))
    refine ⟨(1 / 2 : ℝ) * (f ⬝ᵥ h.choose), ?_⟩
    unfold compliance
    rw [dif_pos h]
  · intro c hc
    obtain ⟨v₀, hv₀, rfl⟩ := hcomp c hc
    refine ⟨⟨v₀, K1v v₀ hv₀⟩, fun v => ?_⟩
    rw [← K1v v₀ hv₀]
    exact K1 v₀ hv₀ v
