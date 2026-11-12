-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.entire_product_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:17:56.95391+00:00
-- url     : https://prove2.me/submissions/c06283b1-911e-4503-ade1-ae0704291556

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator

section
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.EntireProduct

open MomentAmbiguitySecretary.Secretary

/-- Expansion of the finite product over digit vectors. -/
lemma finiteProduct_expand (B N M : ℕ) (z : ℂ) :
    finiteProduct B N M z =
      ∑ c : FiniteDigits N M, ((B : ℂ)⁻¹) ^ (digitExponent c) * z ^ (digitTotal c) := by
  unfold finiteProduct factor
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, digitTotal,
    digitExponent]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  ring

lemma finiteProduct_fun (B N M : ℕ) : finiteProduct B N M = fun z => ∑ c : FiniteDigits N M,
      ((B : ℂ)⁻¹) ^ (digitExponent c) * z ^ (digitTotal c) := funext (finiteProduct_expand B N M)

lemma finiteProduct_differentiable (B N M : ℕ) : Differentiable ℂ (finiteProduct B N M) := by
  rw [finiteProduct_fun]
  fun_prop

lemma finiteTaylor_eq (B N M j : ℕ) :
    finiteTaylor B N M j = (finiteOccupancySum B N M j : ℂ) := by
  unfold finiteTaylor finiteOccupancySum
  rw [finiteProduct_fun, iteratedDeriv_fun_sum (fun c _ => by fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : j = digitTotal c
  · rw [if_pos h, if_pos h.symm]
    have : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    push_cast
    field_simp
    rw [← h]; ring
  · simp [h, Ne.symm h]

lemma factor_sub_one_norm_le (B N m : ℕ) (hN : 1 ≤ N) (z : ℂ)
    (hx : ‖z * ((B : ℂ)⁻¹) ^ m‖ ≤ 1) :
    ‖factor B N m z - 1‖ ≤ N * ‖z * ((B : ℂ)⁻¹) ^ m‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set x := z * ((B : ℂ)⁻¹) ^ m with hxdef
  have h1 : factor B (n + 1) m z = ∑ i ∈ Finset.range (n + 1), x ^ i := by
    unfold factor
    exact Fin.sum_univ_eq_sum_range (fun i => x ^ i) (n + 1)
  rw [h1, Finset.sum_range_succ']
  simp only [pow_zero, add_sub_cancel_right]
  calc ‖∑ i ∈ Finset.range n, x ^ (i + 1)‖
      ≤ ∑ i ∈ Finset.range n, ‖x ^ (i + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, ‖x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_pow]
        calc ‖x‖ ^ (i + 1) ≤ ‖x‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hx (by omega)
          _ = ‖x‖ := pow_one _
    _ = n * ‖x‖ := by simp
    _ ≤ ((n + 1 : ℕ) : ℝ) * ‖x‖ := by
        gcongr
        simp

lemma tlu_finsetRange (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    TendstoLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) => ∏ m ∈ Finset.range n, factor B N m z)
      (entireProduct B N) atTop univ := by
  have hq : (B : ℝ)⁻¹ < 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hq0 : 0 ≤ (B : ℝ)⁻¹ := by positivity
  have hP : HasProdLocallyUniformlyOn (fun (m : ℕ) (z : ℂ) => 1 + (factor B N m z - 1))
      (fun z => ∏' m : ℕ, (1 + (factor B N m z - 1))) univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    have hsum : Summable (fun m : ℕ => (N : ℝ) * |R| * ((B : ℝ)⁻¹) ^ m) :=
      (summable_geometric_of_lt_one hq0 hq).mul_left _
    refine Summable.hasProdUniformlyOn_nat_one_add hK hsum ?_ ?_
    · have ht : Tendsto (fun m : ℕ => |R| * ((B : ℝ)⁻¹) ^ m) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul |R|
      filter_upwards [ht.eventually (gt_mem_nhds one_pos)] with m hm z hz
      have hz' : ‖z‖ ≤ |R| := by
        have := hR hz
        simp only [Metric.mem_closedBall, dist_zero_right] at this
        exact this.trans (le_abs_self R)
      have hx : ‖z * ((B : ℂ)⁻¹) ^ m‖ ≤ |R| * ((B : ℝ)⁻¹) ^ m := by
        rw [norm_mul, norm_pow, norm_inv]
        simp only [Complex.norm_natCast]
        gcongr
      have := factor_sub_one_norm_le B N m (by omega) z (hx.trans hm.le)
      calc ‖factor B N m z - 1‖ ≤ N * ‖z * ((B : ℂ)⁻¹) ^ m‖ := this
        _ ≤ N * (|R| * ((B : ℝ)⁻¹) ^ m) := by gcongr
        _ = N * |R| * ((B : ℝ)⁻¹) ^ m := by ring
    · intro m
      unfold factor
      fun_prop
  have e : (fun (m : ℕ) (z : ℂ) => 1 + (factor B N m z - 1)) = factor B N := by
    funext m z; ring
  rw [e] at hP
  simp only [add_sub_cancel] at hP
  exact hP.tendstoLocallyUniformlyOn_finsetRange

lemma tlu_finiteProduct (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    TendstoLocallyUniformlyOn (fun M : ℕ => finiteProduct B N M)
      (entireProduct B N) atTop univ := by
  have h := tlu_finsetRange B N hB hN
  intro v hv r hr
  obtain ⟨t, ht, htr⟩ := h v hv r hr
  refine ⟨t, ht, (tendsto_add_atTop_nat 1).eventually htr |>.mono fun M hM y hy => ?_⟩
  have := hM y hy
  simpa [finiteProduct, Fin.prod_univ_eq_prod_range (fun m => factor B N m y)] using this

lemma tlu_iteratedDeriv (j : ℕ) : ∀ (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    (∀ n, Differentiable ℂ (F n)) → TendstoLocallyUniformlyOn F f atTop univ →
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv j (F n)) (iteratedDeriv j f) atTop univ := by
  induction j with
  | zero => intro F f _ h; simpa using h
  | succ j ih =>
    intro F f hF h
    simp_rw [iteratedDeriv_succ']
    exact ih (fun n => deriv (F n)) (deriv f) (fun n => (hF n).deriv)
      (h.deriv (Filter.Eventually.of_forall fun n => (hF n).differentiableOn) isOpen_univ)

/-! ### Occupancy -/

/-- Embedding of digit vectors into finitely supported sequences. -/
noncomputable def phi (N M : ℕ) (c : FiniteDigits N M) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range (M + 1))
    (fun m => if h : m < M + 1 then (c ⟨m, h⟩ : ℕ) else 0)
    (by
      intro a ha
      rw [Finset.mem_range]
      by_contra hh
      exact ha (by simp [hh]))

lemma phi_apply (N M : ℕ) (c : FiniteDigits N M) (m : ℕ) :
    phi N M c m = if h : m < M + 1 then (c ⟨m, h⟩ : ℕ) else 0 := rfl

lemma phi_injective (N M : ℕ) : Function.Injective (phi N M) := by
  intro c d h
  funext i
  have := congrArg (fun f => f (i : ℕ)) h
  simp only [phi_apply, dif_pos i.isLt] at this
  exact Fin.ext (by simpa using this)

lemma phi_sum (N M : ℕ) (c : FiniteDigits N M) :
    (phi N M c).sum (fun _ u => u) = digitTotal c := by
  rw [Finsupp.sum_of_support_subset (phi N M c) Finsupp.support_onFinset_subset _ (by simp)]
  rw [Finset.sum_range, digitTotal]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [phi_apply, i.isLt]

lemma phi_exp (N M : ℕ) (c : FiniteDigits N M) :
    (phi N M c).sum (fun m u => m * u) = digitExponent c := by
  rw [Finsupp.sum_of_support_subset (phi N M c) Finsupp.support_onFinset_subset _ (by simp)]
  rw [Finset.sum_range (fun m => m * phi N M c m), digitExponent]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [phi_apply, i.isLt]

open Classical in
/-- The finite set of occupancies supported in `{0, …, M}`. -/
noncomputable def Sfin (N M j : ℕ) : Finset (Occupancy N j) :=
  ((Finset.univ : Finset (FiniteDigits N M)).image (phi N M)).subtype
    (fun c => (∀ m, c m < N) ∧ c.sum (fun _ u => u) = j)

lemma mem_Sfin (N M j : ℕ) (c : Occupancy N j) :
    c ∈ Sfin N M j ↔ ∀ m, M + 1 ≤ m → c.val m = 0 := by
  classical
  simp only [Sfin, Finset.mem_subtype, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd⟩ m hm
    rw [← hd, phi_apply, dif_neg (by omega)]
  · intro h
    refine ⟨fun i => ⟨c.val i, c.2.1 i⟩, ?_⟩
    ext m
    rw [phi_apply]
    by_cases hm : m < M + 1
    · simp [hm]
    · simp [hm, h m (by omega)]

lemma Sfin_mono (N j : ℕ) : Monotone (fun M => Sfin N M j) := by
  refine monotone_nat_of_le_succ fun M c hc => ?_
  rw [mem_Sfin] at hc ⊢
  exact fun m hm => hc m (by omega)

lemma sum_Sfin (B N M j : ℕ) :
    ∑ c ∈ Sfin N M j, ((B : ℝ)⁻¹) ^ (occupancyExponent c) = finiteOccupancySum B N M j := by
  classical
  unfold Sfin finiteOccupancySum occupancyExponent
  rw [Finset.sum_subtype_eq_sum_filter
    (fun c : ℕ →₀ ℕ => ((B : ℝ)⁻¹) ^ (c.sum (fun m u => m * u)))]
  rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => phi_injective N M h),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hp : ((∀ m, phi N M c m < N) ∧ (phi N M c).sum (fun _ u => u) = j) ↔
      digitTotal c = j := by
    rw [phi_sum]
    refine ⟨fun h => h.2, fun h => ⟨fun m => ?_, h⟩⟩
    rw [phi_apply]
    split_ifs with hm
    · exact (c ⟨m, hm⟩).isLt
    · exact lt_of_lt_of_le (by omega) (Nat.succ_le_of_lt (c 0).pos)
  simp only [hp, phi_exp]


lemma T_mono (B N j : ℕ) : Monotone (fun M => finiteOccupancySum B N M j) := by
  refine monotone_nat_of_le_succ fun M => ?_
  rw [← sum_Sfin, ← sum_Sfin]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Sfin_mono N j (Nat.le_succ M))
    (fun c _ _ => by positivity)

lemma hasSum_occ (B N j : ℕ) (L : ℝ)
    (hL : Tendsto (fun M => finiteOccupancySum B N M j) atTop (𝓝 L)) :
    HasSum (fun c : Occupancy N j => ((B : ℝ)⁻¹) ^ (occupancyExponent c)) L := by
  refine hasSum_of_isLUB_of_nonneg _ (fun c => by positivity) ⟨?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    set M := s.sup (fun c : Occupancy N j => c.val.support.sup id) with hM
    have hs : s ⊆ Sfin N M j := by
      intro c hc
      rw [mem_Sfin]
      intro m hm
      by_contra h
      have h1 : m ∈ c.val.support := Finsupp.mem_support_iff.2 h
      have h2 : m ≤ c.val.support.sup id := Finset.le_sup (f := id) h1
      have h3 : c.val.support.sup id ≤ M :=
        Finset.le_sup (f := fun c : Occupancy N j => c.val.support.sup id) hc
      omega
    calc ∑ c ∈ s, ((B : ℝ)⁻¹) ^ (occupancyExponent c)
        ≤ ∑ c ∈ Sfin N M j, ((B : ℝ)⁻¹) ^ (occupancyExponent c) :=
          Finset.sum_le_sum_of_subset_of_nonneg hs (fun c _ _ => by positivity)
      _ = finiteOccupancySum B N M j := sum_Sfin B N M j
      _ ≤ L := (T_mono B N j).ge_of_tendsto hL M
  · intro b hb
    refine le_of_tendsto' hL fun M => ?_
    rw [← sum_Sfin]
    exact hb ⟨Sfin N M j, rfl⟩

end MomentAmbiguitySecretary.Secretary.Dev.EntireProduct

namespace MomentAmbiguitySecretary.Secretary

open MomentAmbiguitySecretary.Secretary.Dev.EntireProduct

theorem chk_entire_product_coefficients (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    TendstoLocallyUniformlyOn (fun M : ℕ => finiteProduct B N M)
      (entireProduct B N) atTop univ ∧
    Differentiable ℂ (entireProduct B N) ∧
    (∀ M j : ℕ, finiteTaylor B N M j = (finiteOccupancySum B N M j : ℂ)) ∧
    (∀ M : ℕ, ∀ z : ℂ,
      HasSum (fun j : ℕ => finiteTaylor B N M j * z ^ j) (finiteProduct B N M z)) ∧
    (∀ z : ℂ, HasSum (fun j : ℕ => (coefficient B N j : ℂ) * z ^ j)
      (entireProduct B N z)) ∧
    (∀ j : ℕ, Monotone (fun M : ℕ => finiteOccupancySum B N M j) ∧
      Tendsto (fun M : ℕ => finiteOccupancySum B N M j) atTop (𝓝 (coefficient B N j)) ∧
      HasSum (fun c : Occupancy N j => ((B : ℝ)⁻¹) ^ occupancyExponent c)
        (coefficient B N j) ∧
      HasSum (fun c : Occupancy N j => (B : ℝ) ^ (-(occupancyExponent c : ℤ)))
        (coefficient B N j)) := by
  have hTLU := tlu_finiteProduct B N hB hN
  have hdiff : Differentiable ℂ (entireProduct B N) := fun z =>
    (hTLU.differentiableOn (Filter.Eventually.of_forall fun M =>
      (finiteProduct_differentiable B N M).differentiableOn) isOpen_univ).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ z))
  have hconv : ∀ j : ℕ, Tendsto (fun M => finiteTaylor B N M j) atTop
      (𝓝 ((j.factorial : ℂ)⁻¹ * iteratedDeriv j (entireProduct B N) 0)) := by
    intro j
    have := (tlu_iteratedDeriv j _ _ (finiteProduct_differentiable B N) hTLU).tendsto_at
      (mem_univ (0 : ℂ))
    exact this.const_mul _
  have hreal : ∀ j : ℕ, Tendsto (fun M => finiteOccupancySum B N M j) atTop
      (𝓝 (coefficient B N j)) := by
    intro j
    have h := (Complex.continuous_re.tendsto _).comp (hconv j)
    simp only [Function.comp_def, finiteTaylor_eq, Complex.ofReal_re] at h
    exact h
  have hw : ∀ j : ℕ, (j.factorial : ℂ)⁻¹ * iteratedDeriv j (entireProduct B N) 0 =
      (coefficient B N j : ℂ) := by
    intro j
    refine tendsto_nhds_unique (hconv j) ?_
    have h := (Complex.continuous_ofReal.tendsto _).comp (hreal j)
    simpa only [Function.comp_def, finiteTaylor_eq] using h
  refine ⟨hTLU, hdiff, finiteTaylor_eq B N, ?_, ?_, ?_⟩
  · intro M z
    have := Complex.hasSum_taylorSeries_of_entire (finiteProduct_differentiable B N M) 0 z
    have e : (fun j : ℕ => finiteTaylor B N M j * z ^ j) = fun n : ℕ =>
        (n.factorial : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n (finiteProduct B N M) 0 := by
      funext n
      simp only [finiteTaylor, sub_zero, smul_eq_mul]
      ring
    rw [e]; exact this
  · intro z
    have := Complex.hasSum_taylorSeries_of_entire hdiff 0 z
    have e : (fun j : ℕ => (coefficient B N j : ℂ) * z ^ j) = fun n : ℕ =>
        (n.factorial : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n (entireProduct B N) 0 := by
      funext n
      simp only [sub_zero, smul_eq_mul]
      rw [← hw n]
      ring
    rw [e]; exact this
  · intro j
    have hs := hasSum_occ B N j _ (hreal j)
    refine ⟨T_mono B N j, hreal j, hs, ?_⟩
    convert hs using 2 with c
    rw [zpow_neg, zpow_natCast, inv_pow]

end MomentAmbiguitySecretary.Secretary

end

theorem solution : type_of% @MomentAmbiguitySecretary.Secretary.chk_entire_product_coefficients := @MomentAmbiguitySecretary.Secretary.chk_entire_product_coefficients
