-- Prove2me | solution 1 for NonstatRL.Oracle.lp_dual_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:21:59.559442+00:00
-- url     : https://prove2.me/submissions/4664957e-a812-49a2-8b76-333667322456

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

theorem lpd_cone_closed_li {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (v : Fin n → E) (hli : LinearIndependent ℝ v) :
    IsClosed {x : E | ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i} := by
  let L : (Fin n → ℝ) →ₗ[ℝ] E :=
    { toFun := fun c => ∑ i, c i • v i
      map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro r a; simp [Finset.smul_sum, smul_smul] }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext i
    exact Fintype.linearIndependent_iff.mp hli c hc i
  have hemb := LinearMap.isClosedEmbedding_of_injective hker
  have hset : {x : E | ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i} =
      L '' {c | ∀ i, 0 ≤ c i} := by
    ext x; constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  rw [hset]
  apply hemb.isClosedMap
  have : {c : Fin n → ℝ | ∀ i, 0 ≤ c i} = ⋂ i, {c | 0 ≤ c i} := by ext c; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

theorem lpd_cone_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ∀ (n : ℕ) (v : Fin n → E),
    IsClosed {x : E | ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i} := by
  intro n
  induction n with
  | zero => intro v; exact lpd_cone_closed_li v (linearIndependent_empty_type)
  | succ k ih =>
    intro v
    by_cases hli : LinearIndependent ℝ v
    · exact lpd_cone_closed_li v hli
    obtain ⟨g₀, hg₀, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hli
    obtain ⟨g, hg, hpos⟩ : ∃ g : Fin (k + 1) → ℝ, ∑ i, g i • v i = 0 ∧ ∃ i, 0 < g i := by
      rcases lt_or_gt_of_ne hi₀ with h | h
      · refine ⟨-g₀, ?_, i₀, by simp; linarith⟩
        simp [neg_smul, Finset.sum_neg_distrib, hg₀]
      · exact ⟨g₀, hg₀, i₀, h⟩
    have hset : {x : E | ∃ c : Fin (k + 1) → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i} =
        ⋃ j : Fin (k + 1),
          {x : E | ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • (v ∘ j.succAbove) i} := by
      ext x; constructor
      · rintro ⟨c, hc, rfl⟩
        set P := Finset.univ.filter (fun i => 0 < g i) with hP
        have hPne : P.Nonempty := by
          obtain ⟨i, hi⟩ := hpos; exact ⟨i, by simp [hP, hi]⟩
        obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image P (fun i => c i / g i) hPne
        have hgj : 0 < g j := by simpa [hP] using hjP
        set t := c j / g j with ht
        have ht0 : 0 ≤ t := div_nonneg (hc j) hgj.le
        set c' : Fin (k + 1) → ℝ := fun i => c i - t * g i with hc'
        have hc'0 : ∀ i, 0 ≤ c' i := by
          intro i
          by_cases hgi : 0 < g i
          · have := hjmin i (by simp [hP, hgi])
            rw [div_le_div_iff₀ hgj hgi] at this
            simp only [hc', ht]
            rw [div_mul_eq_mul_div, sub_nonneg, div_le_iff₀ hgj]
            linarith
          · push_neg at hgi
            simp only [hc']
            nlinarith [hc i]
        have hc'j : c' j = 0 := by
          simp only [hc', ht]; field_simp; ring
        have hsum : ∑ i, c i • v i = ∑ i, c' i • v i := by
          simp only [hc', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hg,
            smul_zero, sub_zero]
        refine Set.mem_iUnion.mpr ⟨j, fun i => c' (j.succAbove i), fun i => hc'0 _, ?_⟩
        rw [hsum, Fin.sum_univ_succAbove _ j, hc'j, zero_smul, zero_add]
        rfl
      · intro hx
        obtain ⟨j, d, hd, rfl⟩ := Set.mem_iUnion.mp hx
        refine ⟨Fin.insertNth j 0 d, ?_, ?_⟩
        · intro i
          rcases Fin.eq_self_or_eq_succAbove j i with h | ⟨l, rfl⟩
          · rw [h, Fin.insertNth_apply_same]
          · rw [Fin.insertNth_apply_succAbove]; exact hd l
        · rw [Fin.sum_univ_succAbove _ j, Fin.insertNth_apply_same, zero_smul, zero_add]
          simp [Fin.insertNth_apply_succAbove]
    rw [hset]
    exact isClosed_iUnion_of_finite fun j => ih _

theorem lpd_farkas {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (A : I → J → ℝ) (b : I → ℝ) (h : ¬ ∃ γ : J → ℝ, ∀ i, b i ≤ ∑ j, A i j * γ j) :
    ∃ y : I → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ 0 < ∑ i, y i * b i := by
  classical
  let w : J ⊕ J ⊕ I → (I → ℝ) := fun m =>
    match m with
    | Sum.inl j => fun i => A i j
    | Sum.inr (Sum.inl j) => fun i => -A i j
    | Sum.inr (Sum.inr i₀) => -Pi.single i₀ 1
  let e := Fintype.equivFin (J ⊕ J ⊕ I)
  let n := Fintype.card (J ⊕ J ⊕ I)
  let v : Fin n → (I → ℝ) := w ∘ e.symm
  set K := {x : I → ℝ | ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i} with hK
  have hclosed : IsClosed K := lpd_cone_closed n v
  have hconv : Convex ℝ K := by
    rintro x ⟨c₁, hc₁, rfl⟩ y ⟨c₂, hc₂, rfl⟩ a b' ha hb' _
    refine ⟨fun i => a * c₁ i + b' * c₂ i, fun i => by
      have := hc₁ i; have := hc₂ i; positivity, ?_⟩
    simp only [Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K := by
    rintro x ⟨c, hc, rfl⟩ t ht
    refine ⟨fun i => t * c i, fun i => mul_nonneg ht (hc i), ?_⟩
    simp only [Finset.smul_sum, smul_smul]
  have hzero : (0 : I → ℝ) ∈ K := ⟨0, fun _ => le_rfl, by simp⟩
  have hgen : ∀ m, w m ∈ K := by
    intro m
    refine ⟨Pi.single (e m) 1, fun i => ?_, ?_⟩
    · by_cases hi : i = e m
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    · rw [Finset.sum_eq_single (e m)]
      · simp [v]
      · intro i _ hi; simp [Pi.single_apply, hi]
      · intro hc; exact absurd (Finset.mem_univ _) hc
  have hb : b ∉ K := by
    rintro ⟨c, hc, hbc⟩
    apply h
    let c' : J ⊕ J ⊕ I → ℝ := fun m => c (e m)
    have hsum : ∑ i, c i • v i = ∑ m, c' m • w m := by
      rw [← e.sum_comp]; simp [v, c']
    refine ⟨fun j => c' (Sum.inl j) - c' (Sum.inr (Sum.inl j)), fun i => ?_⟩
    have hbi := congrFun hbc i
    rw [hsum, Fintype.sum_sum_type, Fintype.sum_sum_type] at hbi
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, w,
      Pi.neg_apply, Pi.single_apply] at hbi
    have hz : 0 ≤ ∑ x : I, c' (Sum.inr (Sum.inr x)) * (if i = x then 1 else 0) := by
      apply Finset.sum_nonneg; intro x _
      have := hc (e (Sum.inr (Sum.inr x)))
      split_ifs <;> simp [c', this]
    have : ∑ j, A i j * (c' (Sum.inl j) - c' (Sum.inr (Sum.inl j))) =
        ∑ j, c' (Sum.inl j) * A i j + ∑ j, c' (Sum.inr (Sum.inl j)) * -A i j := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring
    rw [this]
    have hneg : ∑ x : I, c' (Sum.inr (Sum.inr x)) * -(if i = x then (1:ℝ) else 0) =
        -∑ x : I, c' (Sum.inr (Sum.inr x)) * (if i = x then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro x _; ring
    rw [hneg] at hbi
    linarith
  obtain ⟨f, u, hfK, hfb⟩ := geometric_hahn_banach_closed_point hconv hclosed hb
  have hu : 0 < u := by have := hfK 0 hzero; simpa using this
  have hfle : ∀ x ∈ K, f x ≤ 0 := by
    intro x hx
    by_contra hpos; push_neg at hpos
    have := hfK ((u / f x + 1) • x) (hsmul x hx _ (by positivity))
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  set y : I → ℝ := fun i => f (Pi.single i 1) with hy
  have hexp : ∀ x : I → ℝ, f x = ∑ i, x i * y i := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [show (Pi.single i (x i) : I → ℝ) = x i • Pi.single i (1 : ℝ) by
      ext k; simp [Pi.single_apply]]
    rw [map_smul, smul_eq_mul]
  refine ⟨y, fun i => ?_, fun j => ?_, ?_⟩
  · have := hfle _ (hgen (Sum.inr (Sum.inr i)))
    simp only [w, map_neg] at this
    simp only [hy]; linarith
  · have h1 := hfle _ (hgen (Sum.inl j))
    have h2 := hfle _ (hgen (Sum.inr (Sum.inl j)))
    simp only [w] at h1 h2
    rw [hexp] at h1 h2
    have : ∑ i, -A i j * y i = -∑ i, A i j * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this] at h2
    have : ∑ i, y i * A i j = ∑ i, A i j * y i := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this]; linarith
  · rw [hexp] at hfb
    have : ∑ i, y i * b i = ∑ i, b i * y i := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this]; linarith

end NonstatRL.Oracle

open NonstatRL.Oracle

theorem solution {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) :
    ∃ γ : Fin S → ℝ,
      DualFeasible M.r (fun s a s' => (M.P s a s' : ℝ)) As (optGain M As) γ := by
  classical
  by_contra hno
  set ρ := optGain M As with hρ
  let A' : Fin S × Fin A → Fin S → ℝ := fun p j =>
    if p.2 ∈ As p.1 then (if j = p.1 then 1 else 0) - (M.P p.1 p.2 j : ℝ) else 0
  let b' : Fin S × Fin A → ℝ := fun p => if p.2 ∈ As p.1 then M.r p.1 p.2 - ρ else -1
  have hinf : ¬ ∃ γ : Fin S → ℝ, ∀ p, b' p ≤ ∑ j, A' p j * γ j := by
    rintro ⟨γ, hγ⟩
    apply hno
    refine ⟨γ, fun s a ha => ?_⟩
    have h1 := hγ (s, a)
    simp only [A', b', if_pos ha, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    simp only
    linarith
  obtain ⟨y, hy0, hcol, hobj⟩ := lpd_farkas A' b' hinf
  have hsplit : ∀ (s : Fin S) (g : Fin A → ℝ),
      ∑ a ∈ As s, g a = ∑ a, (if a ∈ As s then g a else 0) := by
    intro s g; rw [Finset.sum_ite_mem, Finset.univ_inter]
  -- objective restricted to allowed pairs
  set V := ∑ s : Fin S, ∑ a ∈ As s, y (s, a) * (M.r s a - ρ) with hV
  have hV0 : 0 < V := by
    have : ∑ p, y p * b' p ≤ V := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_le_sum; intro s _
      rw [hsplit]
      apply Finset.sum_le_sum; intro a _
      by_cases ha : a ∈ As s
      · simp [b', ha]
      · have := hy0 (s, a); simp [b', ha]; linarith
    linarith
  set Y := ∑ s : Fin S, ∑ a ∈ As s, y (s, a) with hY
  have hY0 : 0 < Y := by
    have hYnn : 0 ≤ Y := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => hy0 _
    rcases hYnn.lt_or_eq with h | h
    · exact h
    exfalso
    have hz : ∀ s, ∀ a ∈ As s, y (s, a) = 0 := by
      intro s a ha
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ => Finset.sum_nonneg fun a _ => hy0 (s, a))).mp h.symm s (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hy0 (s, a))).mp h1 a ha
    have : V = 0 := by
      apply Finset.sum_eq_zero; intro s _
      apply Finset.sum_eq_zero; intro a ha
      rw [hz s a ha, zero_mul]
    linarith
  -- flow constraints
  have hflowy : ∀ j : Fin S, ∑ a ∈ As j, y (j, a) =
      ∑ s : Fin S, ∑ a ∈ As s, (M.P s a j : ℝ) * y (s, a) := by
    intro j
    have h1 := hcol j
    rw [Fintype.sum_prod_type] at h1
    have h2 : ∀ s : Fin S, ∑ a, y (s, a) * A' (s, a) j =
        ∑ a ∈ As s, (y (s, a) * (if j = s then 1 else 0) - (M.P s a j : ℝ) * y (s, a)) := by
      intro s
      rw [hsplit]
      apply Finset.sum_congr rfl; intro a _
      by_cases ha : a ∈ As s
      · simp only [A', ha, if_true]; ring
      · simp [A', ha]
    simp only [h2, Finset.sum_sub_distrib] at h1
    have h3 : ∑ s : Fin S, ∑ a ∈ As s, y (s, a) * (if j = s then 1 else 0) =
        ∑ a ∈ As j, y (j, a) := by
      have : ∀ s : Fin S, ∑ a ∈ As s, y (s, a) * (if j = s then 1 else 0) =
          if j = s then ∑ a ∈ As s, y (s, a) else 0 := by
        intro s; split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_ite_eq]
      simp
    linarith
  set x : Fin S → Fin A → ℝ := fun s a => if a ∈ As s then y (s, a) / Y else 0 with hx
  have hxa : ∀ s, ∀ a ∈ As s, x s a = y (s, a) / Y := fun s a ha => if_pos ha
  have hsumx : ∀ s, ∑ a ∈ As s, x s a = (∑ a ∈ As s, y (s, a)) / Y := by
    intro s; rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun a ha => hxa s a ha)
  have hmem : (∑ s : Fin S, ∑ a ∈ As s, M.r s a * x s a) ∈
      {v : ℝ | ∃ x : Fin S → Fin A → ℝ,
        (∀ s a, 0 ≤ x s a) ∧
        (∀ s a, a ∉ As s → x s a = 0) ∧
        (∀ s, (∑ a ∈ As s, x s a) =
          ∑ s' : Fin S, ∑ a' ∈ As s', (M.P s' a' s : ℝ) * x s' a') ∧
        (∑ s : Fin S, ∑ a ∈ As s, x s a) = 1 ∧
        v = ∑ s : Fin S, ∑ a ∈ As s, M.r s a * x s a} := by
    refine ⟨x, fun s a => ?_, fun s a ha => if_neg ha, fun s => ?_, ?_, rfl⟩
    · simp only [hx]; split_ifs
      · exact div_nonneg (hy0 _) hY0.le
      · exact le_rfl
    · rw [hsumx, hflowy s, Finset.sum_div]
      apply Finset.sum_congr rfl; intro s' _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro a' ha'
      rw [hxa s' a' ha']; ring
    · simp only [hsumx]; rw [← Finset.sum_div, ← hY, div_self hY0.ne']
  have hbdd : BddAbove {v : ℝ | ∃ x : Fin S → Fin A → ℝ,
        (∀ s a, 0 ≤ x s a) ∧
        (∀ s a, a ∉ As s → x s a = 0) ∧
        (∀ s, (∑ a ∈ As s, x s a) =
          ∑ s' : Fin S, ∑ a' ∈ As s', (M.P s' a' s : ℝ) * x s' a') ∧
        (∑ s : Fin S, ∑ a ∈ As s, x s a) = 1 ∧
        v = ∑ s : Fin S, ∑ a ∈ As s, M.r s a * x s a} := by
    refine ⟨1, ?_⟩
    rintro v ⟨x, hx0, -, -, hsum, rfl⟩
    calc ∑ s : Fin S, ∑ a ∈ As s, M.r s a * x s a ≤ ∑ s : Fin S, ∑ a ∈ As s, x s a := by
          apply Finset.sum_le_sum; intro s _
          apply Finset.sum_le_sum; intro a _
          have := (M.r_mem_Icc s a).2
          nlinarith [hx0 s a]
      _ = 1 := hsum
  have hle := le_csSup hbdd hmem
  have hρdef : ρ = sSup {v : ℝ | ∃ x : Fin S → Fin A → ℝ,
        (∀ s a, 0 ≤ x s a) ∧
        (∀ s a, a ∉ As s → x s a = 0) ∧
        (∀ s, (∑ a ∈ As s, x s a) =
          ∑ s' : Fin S, ∑ a' ∈ As s', (M.P s' a' s : ℝ) * x s' a') ∧
        (∑ s : Fin S, ∑ a ∈ As s, x s a) = 1 ∧
        v = ∑ s : Fin S, ∑ a ∈ As s, M.r s a * x s a} := rfl
  rw [← hρdef] at hle
  have hval : ∑ s : Fin S, ∑ a ∈ As s, M.r s a * x s a =
      (∑ s : Fin S, ∑ a ∈ As s, M.r s a * y (s, a)) / Y := by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro s _
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro a ha
    rw [hxa s a ha]; ring
  rw [hval, div_le_iff₀ hY0] at hle
  have hVexp : V = ∑ s : Fin S, ∑ a ∈ As s, M.r s a * y (s, a) - ρ * Y := by
    simp only [hV, hY, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro a _
    ring
  linarith
