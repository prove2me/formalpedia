-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:47:08.451057+00:00
-- url     : https://prove2.me/submissions/544b843f-6632-4152-99d5-25bc85d4cd33

import Theorems.Thm_MaxCutSample2027_Coreset_theorem_2_1
import Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_2_10
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

private theorem empirical_sum {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (x : Fin k → V) (f : V → ℝ) : ∑ v, empirical x v * f v = (∑ i, f (x i)) / (k : ℝ) := by
  calc
    _ = (∑ v, ((Finset.univ.filter (fun i => x i = v)).card : ℝ) * f v) / (k : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ => by simp only [empirical]; ring
    _ = _ := by
      congr 1
      rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := x) (fun _ _ => Finset.mem_univ _) (fun i => f (x i))]
      apply Finset.sum_congr rfl
      intro v _
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

private theorem empirical_probability {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (hk : 1 ≤ k) (x : Fin k → V) : IsProbabilityVector (empirical x) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨fun v => div_nonneg (Nat.cast_nonneg _) hk'.le, ?_⟩
  simpa [hk'.ne'] using empirical_sum x (fun _ => 1)

private theorem sample_le {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (f g : (Fin k → V) → ℝ) (h : ∀ x, f x ≤ g x) :
    sampleAverage p k f ≤ sampleAverage p k g := by
  unfold sampleAverage
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x)
    (Finset.prod_nonneg fun i _ => hp (x i))

private theorem sample_smul {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (a : ℝ) (f : (Fin k → V) → ℝ) : sampleAverage p k (fun x => a * f x) = a * sampleAverage p k f := by
  unfold sampleAverage
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
private theorem sample_product {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ) (f : Fin k → V → ℝ) :
    sampleAverage p k (fun x => ∏ i, f i (x i)) = ∏ i, ∑ v, p v * f i v := by
  unfold sampleAverage sampleWeight
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i v => p v * f i v)).symm

private theorem sample_one {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ} (hp : IsProbabilityVector p)
    (i : Fin k) (f : V → ℝ) : sampleAverage p k (fun x => f (x i)) = ∑ v, p v * f v := by
  let h : Fin k → V → ℝ := Function.update (fun _ _ => 1) i f
  have prod (x : Fin k → V) : (∏ j, h j (x j)) = f (x i) := by
    rw [Finset.prod_eq_single i]
    · simp [h]
    · intro j _ hji
      simp [h, hji]
    · simp
  have e := sample_product p h
  simp_rw [prod] at e
  rw [e, Finset.prod_eq_single i]
  · simp [h]
  · intro j _ hji
    simp [h, hji, hp.2]
  · simp

private theorem sample_two {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ} (hp : IsProbabilityVector p)
    (i j : Fin k) (hij : i ≠ j) (f g : V → ℝ) :
    sampleAverage p k (fun x => f (x i) * g (x j)) = (∑ v, p v * f v) * ∑ v, p v * g v := by
  let h : Fin k → V → ℝ := Function.update (Function.update (fun _ _ => 1) i f) j g
  have prod (x : Fin k → V) : (∏ l, h l (x l)) = f (x i) * g (x j) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Finset.prod_eq_single i]
    · simp [h, hij]
    · intro l hl hli
      simp [h, hli, (Finset.mem_erase.mp hl).1]
    · simp [hij]
  have e := sample_product p h
  simp_rw [prod] at e
  rw [e, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Finset.prod_eq_single i]
  · simp [h, hij]
  · intro l hl hli
    simp [h, hli, (Finset.mem_erase.mp hl).1, hp.2]
  · simp [hij]

private theorem sample_const {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : IsProbabilityVector p) (a : ℝ) : sampleAverage p k (fun _ => a) = a := by
  have h := sample_product (k := k) p (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one, hp.2] at h
  change (∑ x : Fin k → V, sampleWeight p x * 1) = 1 at h
  simp only [mul_one] at h
  unfold sampleAverage
  rw [← Finset.sum_mul, h, one_mul]

private theorem sample_sum {V I : Type*} [Fintype V] [Fintype I] {k : ℕ} (p : V → ℝ)
    (f : I → (Fin k → V) → ℝ) : sampleAverage p k (fun x => ∑ i, f i x) = ∑ i, sampleAverage p k (f i) := by
  simp only [sampleAverage, Finset.mul_sum]
  exact Finset.sum_comm

private theorem sample_empirical {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} {p : V → ℝ}
    (hp : IsProbabilityVector p) (hk : 1 ≤ k) (v : V) : sampleAverage p k (fun x => empirical x v) = p v := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have empirical_indicator (x : Fin k → V) : empirical x v = ((∑ i, if x i = v then 1 else 0) : ℝ) / (k : ℝ) := by
    rw [empirical, Finset.sum_boole]
  have h (i : Fin k) : sampleAverage p k (fun x => if x i = v then 1 else 0) = p v := by
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      sample_one hp i (fun u => if u = v then 1 else 0)
  simp only [empirical_indicator, div_eq_inv_mul, sample_smul, sample_sum, h, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hk'.ne']

private theorem sample_add {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (f g : (Fin k → V) → ℝ) : sampleAverage p k (fun x => f x + g x) = sampleAverage p k f + sampleAverage p k g := by
  simp only [sampleAverage, mul_add, Finset.sum_add_distrib]

private theorem sample_sub {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (f g : (Fin k → V) → ℝ) : sampleAverage p k (fun x => f x - g x) = sampleAverage p k f - sampleAverage p k g := by
  simp only [sampleAverage, mul_sub, Finset.sum_sub_distrib]

private theorem sample_abs {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (f : (Fin k → V) → ℝ) :
    |sampleAverage p k f| ≤ sampleAverage p k (fun x => |f x|) := by
  unfold sampleAverage
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro x _
  have h : 0 ≤ sampleWeight p x := Finset.prod_nonneg fun i _ => hp (x i)
  rw [abs_mul, abs_of_nonneg h]

private theorem sample_mean {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : IsProbabilityVector p) (hk : 1 ≤ k) (f : V → ℝ) :
    sampleAverage p k (fun x => (∑ i, f (x i)) / (k : ℝ)) = ∑ v, p v * f v := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h (i : Fin k) : sampleAverage p k (fun x => f (x i)) = ∑ v, p v * f v := sample_one hp i f
  simp only [div_eq_inv_mul, sample_smul, sample_sum, h, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hk'.ne', one_mul]

private theorem sample_pair_permute {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (swap : ((Fin k → V) × (Fin k → V)) ≃ ((Fin k → V) × (Fin k → V)))
    (h : ∀ x y, sampleWeight p (swap (x, y)).1 * sampleWeight p (swap (x, y)).2 =
      sampleWeight p x * sampleWeight p y)
    (f : (Fin k → V) → (Fin k → V) → ℝ) :
    sampleAverage p k (fun x => sampleAverage p k (fun y => f (swap (x, y)).1 (swap (x, y)).2)) =
      sampleAverage p k (fun x => sampleAverage p k (f x)) := by
  unfold sampleAverage
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [← Fintype.sum_prod_type (fun z : (Fin k → V) × (Fin k → V) =>
        (sampleWeight p z.1 * sampleWeight p z.2) * f (swap z).1 (swap z).2),
    ← Fintype.sum_prod_type (fun z : (Fin k → V) × (Fin k → V) => (sampleWeight p z.1 * sampleWeight p z.2) * f z.1 z.2)]
  refine Fintype.sum_equiv swap _ _ ?_
  rintro ⟨x, y⟩
  simp only
  rw [h x y]
private theorem cutValue_all {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → ℝ) (S : Finset V) :
    cutValue A S = ∑ u, ∑ v, if u ∈ S ∧ v ∉ S then A u v else 0 := by
  unfold cutValue
  have inner (u : V) : (∑ v, if u ∈ S ∧ v ∉ S then A u v else 0) =
      if u ∈ S then ∑ v ∈ Sᶜ, A u v else 0 := by
    by_cases hu : u ∈ S
    · simp only [hu, true_and, if_true, ← Finset.sum_filter]
      have h : Finset.univ.filter (fun v => v ∉ S) = Sᶜ := by ext v; simp
      rw [h]
    · simp [hu]
  simp only [inner, ← Finset.sum_filter]
  simp

private theorem maxCut_restriction {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : V → V → ℝ) (e : W → V) (he : Function.Injective e)
    (row_zero : ∀ u ∉ Set.range e, ∀ v, A u v = 0)
    (col_zero : ∀ v ∉ Set.range e, ∀ u, A u v = 0) :
    maxCut (fun u v => A (e u) (e v)) = maxCut A := by
  classical
  let B (u v : W) := A (e u) (e v)
  have same_cut (S : Finset V) (T : Finset W) (hm : ∀ u, u ∈ T ↔ e u ∈ S) :
      cutValue B T = cutValue A S := by
    rw [cutValue_all, cutValue_all]
    apply Fintype.sum_of_injective e he
    · intro u hu
      exact Finset.sum_eq_zero fun v _ => by simp [row_zero u hu v]
    · intro u
      apply Fintype.sum_of_injective e he
      · intro v hv
        simp [col_zero v hv (e u)]
      · intro v
        simp only [hm, B]
  apply le_antisymm
  · unfold maxCut
    apply Finset.sup'_le
    intro T _
    have h := same_cut (T.image e) T (fun u => by simp [he.eq_iff])
    change cutValue B T = _ at h
    exact h.le.trans (Finset.le_sup' _ (Finset.mem_univ (T.image e)))
  · unfold maxCut
    apply Finset.sup'_le
    intro S _
    let T : Finset W := Finset.univ.filter fun u => e u ∈ S
    have h := same_cut S T (fun u => by simp [T])
    exact h.ge.trans (Finset.le_sup' _ (Finset.mem_univ T))

private theorem sample_restriction {V W : Type*} [Fintype V] [Fintype W] {k : ℕ}
    (e : W → V) (he : Function.Injective e) (p : V → ℝ) (h : ∀ v ∉ Set.range e, p v = 0)
    (f : (Fin k → V) → ℝ) :
    sampleAverage (p ∘ e) k (fun y => f (e ∘ y)) = sampleAverage p k f := by
  classical
  unfold sampleAverage
  let E (y : Fin k → W) := e ∘ y
  have inj : Function.Injective E := by intro x y h; funext i; exact he (congrFun h i)
  apply Fintype.sum_of_injective E inj
  · intro x hx
    have bad : ∃ i, x i ∉ Set.range e := by
      by_contra! hgood
      choose y hy using hgood
      exact hx ⟨y, funext hy⟩
    obtain ⟨i, hi⟩ := bad
    have zero_weight : sampleWeight p x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h (x i) hi)
    rw [zero_weight, zero_mul]
  · intro x
    rfl

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hbound : ∀ u v, A u v ≤ 1)
    (hp : IsProbabilityVector p)
    (hdegree : ∀ v, weightedDegree A v / (Fintype.card V : ℝ) ^ 2 ≤ p v)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (k : ℕ) (hsize : 2304 * ε ^ (-2 : ℤ) * δ ^ (-2 : ℤ) ≤ (k : ℝ)) :
    1 - δ ≤ eventProbability p k
      (fun x => |maxCut (Ahat A p x) - maxCut A| ≤ ε * (Fintype.card V : ℝ) ^ 2) := by
  classical
  let W := {v : V // 0 < p v}
  let e : W → V := Subtype.val
  let B (u v : W) := A (e u) (e v)
  let q : W → ℝ := p ∘ e
  let N : ℝ := Fintype.card V
  let M : ℝ := Fintype.card W
  have hN : 0 < N := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos (α := V)
  have he : Function.Injective e := Subtype.val_injective
  have outside (v : V) (hv : v ∉ Set.range e) : p v = 0 := by
    by_contra hp0
    have pos := lt_of_le_of_ne (hp.1 v) (Ne.symm hp0)
    exact hv ⟨⟨v, pos⟩, rfl⟩
  have qprob : IsPositiveProbabilityVector q := by
    refine ⟨fun v => v.property, ?_⟩
    have h := Fintype.sum_of_injective e he q p outside (fun _ => rfl)
    exact h.trans hp.2
  let _ : Nonempty W := by
    by_contra h
    let _ : IsEmpty W := not_nonempty_iff.mp h
    simpa using qprob.2
  have hM : 0 < M := by
    change 0 < (Fintype.card W : ℝ)
    exact_mod_cast Fintype.card_pos (α := W)
  have hMN : M ≤ N := by
    change (Fintype.card W : ℝ) ≤ (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_le_of_injective e he
  have row_zero (u : V) (hu : u ∉ Set.range e) (v : V) : A u v = 0 := by
    have bound := hdegree u
    change weightedDegree A u / N ^ 2 ≤ p u at bound
    rw [outside u hu] at bound
    have upper := (div_le_iff₀ (by positivity : 0 < N ^ 2)).1 bound
    have lower := Finset.sum_nonneg (s := Finset.univ) (fun v _ => hA.2.2 u v)
    have hzero : weightedDegree A u = 0 := by unfold weightedDegree at *; linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hA.2.2 u v)).1 hzero v (Finset.mem_univ v)
  have col_zero (v : V) (hv : v ∉ Set.range e) (u : V) : A u v = 0 := (hA.1 u v).trans (row_zero v hv u)
  have cut := maxCut_restriction A e he row_zero col_zero
  change maxCut B = maxCut A at cut
  have degree (u : W) : weightedDegree B u = weightedDegree A (e u) :=
    Fintype.sum_of_injective e he (B u) (A (e u)) (fun v hv => col_zero v hv _) (fun _ => rfl)
  have sq_bound : H B q ^ 2 ≤ (N / M) ^ 2 := by
    have hB : IsWeightMatrix B := ⟨fun u v => hA.1 _ _, fun u => hA.2.1 _, fun u v => hA.2.2 _ _⟩
    have h := (lemma_2_10 B q hB qprob (fun u v => hbound _ _)).1
    change H B q ^ 2 ≤ (∑ u, weightedDegree B u / q u) / M ^ 3 at h
    refine h.trans ?_
    have bound (u : W) : weightedDegree B u / q u ≤ N ^ 2 := by
      apply (div_le_iff₀ (qprob.1 u)).2
      rw [degree, mul_comm]
      exact (div_le_iff₀ (by positivity : 0 < N ^ 2)).1 (hdegree (e u))
    have hs : (∑ u, weightedDegree B u / q u) ≤ M * N ^ 2 := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, M] using
        (Finset.sum_le_sum (s := Finset.univ) fun u _ => bound u)
    refine (div_le_div_of_nonneg_right hs (by positivity)).trans_eq ?_
    field_simp [hM.ne']
  have Hbound : H B q ≤ N / M := by
    have hn : 0 ≤ H B q := Finset.sum_nonneg (fun u _ => mul_nonneg (qprob.1 u).le (Real.sqrt_nonneg _))
    exact (sq_le_sq₀ hn (by positivity)).mp sq_bound
  have kpos : (0 : ℝ) < k := by
    exact lt_of_lt_of_le (by positivity : 0 < 2304 * ε ^ (-2 : ℤ) * δ ^ (-2 : ℤ)) hsize
  have hk : 1 ≤ k := by exact_mod_cast kpos
  have hroot : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 kpos
  let loss (x : Fin k → V) := |maxCut (Ahat A p x) - maxCut A| / N ^ 2
  let reduced (x : Fin k → W) := |(maxCut (Ahat B q x) - maxCut B) / M ^ 2|
  have hB : IsWeightMatrix B := ⟨fun u v => hA.1 _ _, fun u => hA.2.1 _, fun u v => hA.2.2 _ _⟩
  have expected := theorem_2_1 B q hB qprob k hk
  change sampleAverage q k reduced ≤ 48 * H B q / Real.sqrt (k : ℝ) at expected
  have reduction (x : Fin k → W) : loss (e ∘ x) = (M ^ 2 / N ^ 2) * reduced x := by
    have eq : Ahat A p (e ∘ x) = Ahat B q x := rfl
    dsimp only [loss, reduced]
    rw [eq, ← cut, abs_div, abs_of_pos (by positivity : 0 < M ^ 2)]
    field_simp [hN.ne', hM.ne']
  have expectation : sampleAverage p k loss ≤ 48 / Real.sqrt (k : ℝ) := by
    rw [← sample_restriction e he p outside loss]
    change sampleAverage q k (fun x => loss (e ∘ x)) ≤ _
    simp only [reduction, sample_smul]
    have bound : 48 * H B q / Real.sqrt (k : ℝ) ≤ 48 * (N / M) / Real.sqrt (k : ℝ) := by
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith
    calc
      _ ≤ (M ^ 2 / N ^ 2) * (48 * (N / M) / Real.sqrt (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (expected.trans bound) (by positivity)
      _ = (M / N) * (48 / Real.sqrt (k : ℝ)) := by field_simp [hN.ne', hM.ne', hroot.ne']
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right ((div_le_one hN).2 hMN)
          (show 0 ≤ 48 / Real.sqrt (k : ℝ) by positivity)
        simpa only [one_mul] using h
  have threshold : 48 / Real.sqrt (k : ℝ) ≤ ε * δ := by
    have hscale : (48 / (ε * δ)) ^ 2 ≤ (k : ℝ) := by
      have eq : (48 / (ε * δ)) ^ 2 = 2304 * ε ^ (-2 : ℤ) * δ ^ (-2 : ℤ) := by
        rw [show (-2 : ℤ) = -(2 : ℤ) by decide]
        simp only [zpow_neg]
        field_simp [hε.ne', hδ.ne']
        norm_num
      rwa [eq]
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 48 / (ε * δ)) (Real.sqrt_nonneg (k : ℝ))).mp
      (by simpa only [Real.sq_sqrt kpos.le] using hscale)
    apply (div_le_iff₀ hroot).2
    exact (div_le_iff₀ (mul_pos hε hδ)).1 h |>.trans_eq (mul_comm _ _)
  let good (x : Fin k → V) := if loss x ≤ ε then (1 : ℝ) else 0
  let bad (x : Fin k → V) := if loss x ≤ ε then (0 : ℝ) else 1
  have bad_bound : ε * sampleAverage p k bad ≤ ε * δ := by
    rw [← sample_smul]
    have h (x : Fin k → V) : ε * bad x ≤ loss x := by
      by_cases hx : loss x ≤ ε
      · simp only [bad, if_pos hx, mul_zero]
        exact div_nonneg (abs_nonneg _) (by positivity)
      · simpa only [bad, if_neg hx, mul_one] using (le_of_not_ge hx)
    exact (sample_le hp.1 _ _ h).trans (expectation.trans threshold)
  have total : sampleAverage p k good + sampleAverage p k bad = 1 := by
    rw [← sample_add]
    have h (x : Fin k → V) : good x + bad x = 1 := by dsimp [good, bad]; split_ifs <;> norm_num
    simp only [h, sample_const hp]
  have event : eventProbability p k (fun x => |maxCut (Ahat A p x) - maxCut A| ≤ ε * (Fintype.card V : ℝ) ^ 2) =
      sampleAverage p k good := by
    unfold eventProbability
    apply congrArg (sampleAverage p k)
    funext x
    have h : loss x ≤ ε ↔ |maxCut (Ahat A p x) - maxCut A| ≤ ε * N ^ 2 := div_le_iff₀ (by positivity)
    simp only [good, h, N]
  rw [event]
  linarith [(mul_le_mul_iff_right₀ hε).mp bad_bound]
