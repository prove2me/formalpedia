-- Prove2me | solution 1 for MasulloGRH.brislawn_trace_eq_integral_diagonal_average
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:09:13.61216+00:00
-- url     : https://prove2.me/submissions/3c926339-7545-4547-a0af-6a53e1e5fe0b

import Definitions.Def_MasulloGRH_HilbertNuclear

open MeasureTheory Filter Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_brislawn_trace_eq_integral_diagonal_average

theorem tendsto_tsum_of_le_tendsto {ι : Type*} {l : Filter ι} (f : ι → ℕ → ℂ) (g : ℕ → ℂ)
    (B : ι → ℕ → ℝ) (β : ℕ → ℝ)
    (hf : ∀ m, Tendsto (fun i => f i m) l (𝓝 (g m)))
    (hB : ∀ m, Tendsto (fun i => B i m) l (𝓝 (β m)))
    (hBs : ∀ᶠ i in l, Summable (B i)) (hβ : Summable β)
    (hsum : Tendsto (fun i => ∑' m, B i m) l (𝓝 (∑' m, β m)))
    (hle : ∀ᶠ i in l, ∀ m, ‖f i m‖ ≤ B i m) :
    Tendsto (fun i => ∑' m, f i m) l (𝓝 (∑' m, g m)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hgβ : ∀ m, ‖g m‖ ≤ β m := fun m =>
    le_of_tendsto_of_tendsto ((hf m).norm) (hB m) (hle.mono fun i hi => hi m)
  have hg : Summable g := hβ.of_norm_bounded hgβ
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε5 : (0:ℝ) < ε / 5 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_sum_nat_add β) (ε / 5) hε5
  have hNt : |∑' k, β (k + N)| < ε / 5 := by
    simpa [Real.dist_eq] using hN N le_rfl
  have h1 := Metric.tendsto_nhds.1
    (tendsto_finsetSum (Finset.range N) (fun m _ => hf m)) (ε / 5) hε5
  have h2 := Metric.tendsto_nhds.1
    (tendsto_finsetSum (Finset.range N) (fun m _ => hB m)) (ε / 5) hε5
  have h3 := Metric.tendsto_nhds.1 hsum (ε / 5) hε5
  filter_upwards [h1, h2, h3, hBs, hle] with i h1 h2 h3 hBsi hlei
  have hfs : Summable (f i) := hBsi.of_norm_bounded hlei
  rw [← hfs.sum_add_tsum_nat_add N, ← hg.sum_add_tsum_nat_add N]
  have hBN := hBsi.sum_add_tsum_nat_add N
  have hβN := hβ.sum_add_tsum_nat_add N
  have t1 : ‖∑' m, f i (m + N)‖ ≤ ∑' m, B i (m + N) :=
    tsum_of_norm_bounded ((summable_nat_add_iff N).2 hBsi).hasSum (fun m => hlei (m + N))
  have t2 : ‖∑' m, g (m + N)‖ ≤ ∑' m, β (m + N) :=
    tsum_of_norm_bounded ((summable_nat_add_iff N).2 hβ).hasSum (fun m => hgβ (m + N))
  rw [Real.dist_eq] at h2 h3
  rw [dist_eq_norm] at h1 ⊢
  have key : (∑ m ∈ Finset.range N, f i m + ∑' m, f i (m + N)) -
      (∑ m ∈ Finset.range N, g m + ∑' m, g (m + N)) =
      (∑ m ∈ Finset.range N, f i m - ∑ m ∈ Finset.range N, g m) +
        (∑' m, f i (m + N) - ∑' m, g (m + N)) := by ring
  rw [key]
  have := norm_add_le (∑ m ∈ Finset.range N, f i m - ∑ m ∈ Finset.range N, g m)
    (∑' m, f i (m + N) - ∑' m, g (m + N))
  have := norm_sub_le (∑' m, f i (m + N)) (∑' m, g (m + N))
  have := abs_lt.1 h2
  have := abs_lt.1 h3
  have := abs_lt.1 hNt
  linarith

theorem exists_balanced {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (x y : ℕ → H) (hs : Summable (fun m => ‖x m‖ * ‖y m‖))
    (hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) :
    ∃ a b : ℕ → H, Summable (fun m => ‖a m‖ ^ 2 + ‖b m‖ ^ 2) ∧
      Summable (fun m => ‖a m‖ * ‖b m‖) ∧
      ∀ u : H, HasSum (fun m => inner ℂ (a m) u • b m) (T u) := by
  classical
  let c : ℕ → ℝ := fun m => if x m = 0 ∨ y m = 0 then 0 else Real.sqrt (‖y m‖ / ‖x m‖)
  have key : ∀ m, ‖((c m : ℝ) : ℂ) • x m‖ ^ 2 = ‖x m‖ * ‖y m‖ ∧
      ‖(((c m)⁻¹ : ℝ) : ℂ) • y m‖ ^ 2 = ‖x m‖ * ‖y m‖ ∧
      ‖((c m : ℝ) : ℂ) • x m‖ * ‖(((c m)⁻¹ : ℝ) : ℂ) • y m‖ = ‖x m‖ * ‖y m‖ ∧
      ∀ u : H, inner ℂ (((c m : ℝ) : ℂ) • x m) u • ((((c m)⁻¹ : ℝ) : ℂ) • y m) =
        inner ℂ (x m) u • y m := by
    intro m
    by_cases h : x m = 0 ∨ y m = 0
    · have hc : c m = 0 := by simp [c, h]
      rcases h with h | h <;> simp [hc, h]
    · have hx : x m ≠ 0 := fun h' => h (Or.inl h')
      have hy : y m ≠ 0 := fun h' => h (Or.inr h')
      have hnx : 0 < ‖x m‖ := norm_pos_iff.2 hx
      have hny : 0 < ‖y m‖ := norm_pos_iff.2 hy
      have hc : c m = Real.sqrt (‖y m‖ / ‖x m‖) := by simp [c, h]
      have hcpos : 0 < c m := by rw [hc]; exact Real.sqrt_pos.2 (div_pos hny hnx)
      have hc2 : c m ^ 2 = ‖y m‖ / ‖x m‖ := by
        rw [hc]; exact Real.sq_sqrt (div_pos hny hnx).le
      have na : ‖((c m : ℝ) : ℂ) • x m‖ = c m * ‖x m‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
      have nb : ‖(((c m)⁻¹ : ℝ) : ℂ) • y m‖ = (c m)⁻¹ * ‖y m‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hcpos).le]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [na, mul_pow, hc2]; field_simp
      · rw [nb, mul_pow, inv_pow, hc2]; field_simp
      · rw [na, nb]; field_simp
      · intro u
        rw [inner_smul_left, smul_smul, Complex.conj_ofReal]
        have h1 : ((c m : ℝ) : ℂ) * (((c m)⁻¹ : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, mul_inv_cancel₀ hcpos.ne', Complex.ofReal_one]
        congr 1
        linear_combination (inner ℂ (x m) u) * h1
  refine ⟨fun m => ((c m : ℝ) : ℂ) • x m, fun m => (((c m)⁻¹ : ℝ) : ℂ) • y m, ?_, ?_, ?_⟩
  · have : (fun m => ‖((c m : ℝ) : ℂ) • x m‖ ^ 2 + ‖(((c m)⁻¹ : ℝ) : ℂ) • y m‖ ^ 2) =
        fun m => 2 * (‖x m‖ * ‖y m‖) := by
      funext m; rw [(key m).1, (key m).2.1]; ring
    simp only [this]; exact hs.mul_left 2
  · simp only [fun m => (key m).2.2.1]; exact hs
  · intro u; simp only [fun m => (key m).2.2.2 u]; exact hxy u

theorem ae_tendsto_avg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) {f : (Fin n → ℝ) → F} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
      Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r, f y) (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (μ := volume) hf 1] with x hx
  refine hx (fun _ => x) id tendsto_id ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := Set.mem_Ioi.1 hr
  show x ∈ Metric.closedBall x (1 * r)
  exact Metric.mem_closedBall_self (by linarith)

theorem norm_sq_setAverage_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (h0 : μ s ≠ 0) (ht : μ s ≠ ⊤) {f : α → ℂ} (hf : IntegrableOn f s μ)
    (hf2 : IntegrableOn (fun x => ‖f x‖ ^ 2) s μ) :
    ‖⨍ x in s, f x ∂μ‖ ^ 2 ≤ ⨍ x in s, ‖f x‖ ^ 2 ∂μ := by
  have hconv : ConvexOn ℝ Set.univ ((norm : ℂ → ℝ) ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have hcont : ContinuousOn ((norm : ℂ → ℝ) ^ 2) Set.univ :=
    (continuous_norm.pow 2).continuousOn
  exact hconv.map_set_average_le hcont isClosed_univ h0 ht (ae_of_all _ fun _ => trivial) hf hf2

theorem integral_norm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  simp only [← RCLike.ofReal_pow] at h
  rw [integral_ofReal] at h
  exact_mod_cast h.symm

theorem integrable_tsum_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : ℕ → α → ℝ} (hg : ∀ m, Integrable (g m) μ) (h0 : ∀ m x, 0 ≤ g m x)
    (hs : Summable (fun m => ∫ x, g m x ∂μ)) :
    Integrable (fun x => ∑' m, g m x) μ ∧ ∀ᵐ x ∂μ, Summable (fun m => g m x) := by
  set F : α → ENNReal := fun x => ∑' m, ENNReal.ofReal (g m x) with hFdef
  have hmeas : AEMeasurable F μ :=
    AEMeasurable.tsum fun m => (hg m).aemeasurable.ennreal_ofReal
  have hlint : ∫⁻ x, F x ∂μ ≠ ⊤ := by
    rw [hFdef, lintegral_tsum fun m => (hg m).aemeasurable.ennreal_ofReal]
    have : ∀ m, ∫⁻ x, ENNReal.ofReal (g m x) ∂μ = ENNReal.ofReal (∫ x, g m x ∂μ) := fun m =>
      (ofReal_integral_eq_lintegral_ofReal (hg m) (ae_of_all _ (h0 m))).symm
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => integral_nonneg (h0 m)) hs]
    exact ENNReal.ofReal_ne_top
  have heq : (fun x => ∑' m, g m x) = fun x => (F x).toReal := by
    funext x
    rw [hFdef, ENNReal.tsum_toReal_eq (fun m => ENNReal.ofReal_ne_top)]
    simp [ENNReal.toReal_ofReal (h0 _ x)]
  refine ⟨?_, ?_⟩
  · rw [heq]; exact integrable_toReal_of_lintegral_ne_top hmeas hlint
  · filter_upwards [ae_lt_top' hmeas hlint] with x hx
    have := ENNReal.summable_toReal hx.ne
    simpa [ENNReal.toReal_ofReal (h0 _ x)] using this

theorem hasSum_setAverage_kernel {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (a b : ℕ → Lp ℂ 2 μ)
    (hab : ∀ u, HasSum (fun m => inner ℂ (a m) u • b m) (T u))
    (k : α → α → ℂ) (hk : MemLp (fun p : α × α => k p.1 p.2) 2 (μ.prod μ))
    (hTk : ∀ u : Lp ℂ 2 μ, (T u : α → ℂ) =ᵐ[μ] fun x => ∫ y, k x y * u y ∂μ)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) :
    HasSum (fun m => inner ℂ (⨍ y in s, a m y ∂μ) (⨍ y in s, b m y ∂μ))
      (⨍ p in s ×ˢ s, k p.1 p.2 ∂(μ.prod μ)) := by
  set u : Lp ℂ 2 μ := indicatorConstLp 2 hs hμs (1 : ℂ) with hu
  have hinner : ∀ f : Lp ℂ 2 μ, inner ℂ u f = ∫ x in s, f x ∂μ := fun f =>
    L2.inner_indicatorConstLp_one hs hμs f
  have h1 : HasSum (fun m => inner ℂ (a m) u * inner ℂ u (b m)) (inner ℂ u (T u)) := by
    simpa using (hab u).mapL (innerSL ℂ u)
  have hss : (μ.prod μ) (s ×ˢ s) ≠ ⊤ := by
    rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hμs
  have hint : IntegrableOn (fun p : α × α => k p.1 p.2) (s ×ˢ s) (μ.prod μ) := by
    have : IsFiniteMeasure ((μ.prod μ).restrict (s ×ˢ s)) := isFiniteMeasure_restrict.2 hss
    exact (hk.restrict (s ×ˢ s)).integrable one_le_two
  have hker : ∀ x, ∫ y, k x y * u y ∂μ = ∫ y in s, k x y ∂μ := by
    intro x
    rw [← integral_indicator hs]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℂ))]
      with y hy
    rw [hu, hy]
    by_cases hys : y ∈ s <;> simp [Set.indicator, hys]
  have h2 : inner ℂ u (T u) = ∫ p in s ×ˢ s, k p.1 p.2 ∂(μ.prod μ) := by
    rw [hinner, setIntegral_prod _ hint]
    refine integral_congr_ae ?_
    refine ae_restrict_of_ae ?_
    filter_upwards [hTk u] with x hx
    rw [hx, hker x]
  have hterm : ∀ m, inner ℂ (a m) u * inner ℂ u (b m) =
      (starRingEnd ℂ) (∫ x in s, a m x ∂μ) * ∫ x in s, b m x ∂μ := by
    intro m
    rw [hinner, ← inner_conj_symm, hinner]
  rw [h2] at h1
  simp only [hterm] at h1
  have h3 := h1.mul_left ((((μ.real s)⁻¹ * (μ.real s)⁻¹ : ℝ)) : ℂ)
  have e1 : (fun m => inner ℂ (⨍ y in s, a m y ∂μ) (⨍ y in s, b m y ∂μ)) = fun i =>
      ((((μ.real s)⁻¹ * (μ.real s)⁻¹ : ℝ)) : ℂ) *
        ((starRingEnd ℂ) (∫ x in s, a i x ∂μ) * ∫ x in s, b i x ∂μ) := by
    funext m
    rw [setAverage_eq, setAverage_eq, RCLike.inner_apply, Complex.real_smul, Complex.real_smul,
      map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have e2 : (⨍ p in s ×ˢ s, k p.1 p.2 ∂(μ.prod μ)) =
      ((((μ.real s)⁻¹ * (μ.real s)⁻¹ : ℝ)) : ℂ) * ∫ p in s ×ˢ s, k p.1 p.2 ∂(μ.prod μ) := by
    rw [setAverage_eq, Complex.real_smul, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
    push_cast
    rw [mul_inv, measureReal_def]
  rw [e1, e2]
  exact h3

theorem operatorTrace_eq_tsum_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) (a b : ℕ → H)
    (hab2 : Summable (fun m => ‖a m‖ ^ 2 + ‖b m‖ ^ 2))
    (hab : ∀ u : H, HasSum (fun m => inner ℂ (a m) u • b m) (T u)) :
    MasulloGRH.operatorTrace T = ∑' m, inner ℂ (a m) (b m) := by
  set e := MasulloGRH.chosenHilbertBasis H with he
  have hon := e.orthonormal
  let f : ℕ → (exists_hilbertBasis ℂ H).choose → ℂ := fun m i =>
    inner ℂ (a m) (e i) * inner ℂ (e i) (b m)
  have hrow : ∀ i, HasSum (fun m => f m i) (inner ℂ (e i) (T (e i))) := by
    intro i
    simpa [f] using (hab (e i)).mapL (innerSL ℂ (e i))
  have hcol : ∀ m, HasSum (f m) (inner ℂ (a m) (b m)) := fun m =>
    e.hasSum_inner_mul_inner (a m) (b m)
  let G : ℕ × (exists_hilbertBasis ℂ H).choose → ℝ := fun p =>
    ‖inner ℂ (e p.2) (a p.1)‖ ^ 2 + ‖inner ℂ (e p.2) (b p.1)‖ ^ 2
  have hG0 : 0 ≤ G := fun p => by positivity
  have hGs : Summable G := by
    rw [summable_prod_of_nonneg hG0]
    refine ⟨fun m => (hon.inner_products_summable (a m)).add (hon.inner_products_summable (b m)),
      ?_⟩
    refine Summable.of_nonneg_of_le (fun m => tsum_nonneg fun i => hG0 (m, i)) (fun m => ?_) hab2
    show ∑' i, (‖inner ℂ (e i) (a m)‖ ^ 2 + ‖inner ℂ (e i) (b m)‖ ^ 2) ≤ _
    rw [Summable.tsum_add (hon.inner_products_summable (a m)) (hon.inner_products_summable (b m))]
    exact add_le_add (hon.tsum_inner_products_le (a m)) (hon.tsum_inner_products_le (b m))
  have hFs : Summable (Function.uncurry f) := by
    refine Summable.of_norm_bounded hGs (fun p => ?_)
    show ‖inner ℂ (a p.1) (e p.2) * inner ℂ (e p.2) (b p.1)‖ ≤
      ‖inner ℂ (e p.2) (a p.1)‖ ^ 2 + ‖inner ℂ (e p.2) (b p.1)‖ ^ 2
    rw [norm_mul, norm_inner_symm (a p.1)]
    have h1 := norm_nonneg (inner ℂ (e p.2) (a p.1))
    have h2 := norm_nonneg (inner ℂ (e p.2) (b p.1))
    nlinarith
  unfold MasulloGRH.operatorTrace
  calc ∑' i, inner ℂ (e i) (T (e i)) = ∑' i, ∑' m, f m i :=
        tsum_congr fun i => (hrow i).tsum_eq.symm
    _ = ∑' m, ∑' i, f m i :=
        Summable.tsum_comm' hFs (fun m => (hcol m).summable) (fun i => (hrow i).summable)
    _ = _ := tsum_congr fun m => (hcol m).tsum_eq

end Sol_MasulloGRH_brislawn_trace_eq_integral_diagonal_average

open MasulloGRH Sol_MasulloGRH_brislawn_trace_eq_integral_diagonal_average

theorem solution (n : ℕ)
    (T : Lp ℂ 2 (volume : Measure (Fin n → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (Fin n → ℝ)))
    (hT : IsNuclearOperator T)
    (k : (Fin n → ℝ) → (Fin n → ℝ) → ℂ)
    (hk : MemLp (fun p : (Fin n → ℝ) × (Fin n → ℝ) => k p.1 p.2) 2
      ((volume : Measure (Fin n → ℝ)).prod volume))
    (hTk : ∀ u : Lp ℂ 2 (volume : Measure (Fin n → ℝ)),
      (T u : (Fin n → ℝ) → ℂ) =ᵐ[volume] fun x => ∫ y, k x y * u y) :
    ∃ d : (Fin n → ℝ) → ℂ,
      (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        Tendsto (fun r : ℝ => ⨍ p in Metric.closedBall (x, x) r, k p.1 p.2
            ∂((volume : Measure (Fin n → ℝ)).prod volume))
          (𝓝[>] 0) (𝓝 (d x))) ∧
      Integrable d (volume : Measure (Fin n → ℝ)) ∧
      ∫ x, d x = operatorTrace T := by
  obtain ⟨x, y, hxy_s, hxy⟩ := hT
  obtain ⟨a, b, hab2, hab1, hab⟩ := exists_balanced T x y hxy_s hxy
  set g : ℕ → (Fin n → ℝ) → ℝ := fun m z => ‖a m z‖ ^ 2 + ‖b m z‖ ^ 2 with hg
  have hasq : ∀ m, Integrable (fun z => ‖a m z‖ ^ 2) (volume : Measure (Fin n → ℝ)) := fun m =>
    (Lp.memLp (a m)).integrable_norm_pow two_ne_zero
  have hbsq : ∀ m, Integrable (fun z => ‖b m z‖ ^ 2) (volume : Measure (Fin n → ℝ)) := fun m =>
    (Lp.memLp (b m)).integrable_norm_pow two_ne_zero
  have hgint : ∀ m, Integrable (g m) (volume : Measure (Fin n → ℝ)) := fun m =>
    (hasq m).add (hbsq m)
  have hg0 : ∀ m z, 0 ≤ g m z := fun m z => by positivity
  have hgI : ∀ m, ∫ z, g m z = ‖a m‖ ^ 2 + ‖b m‖ ^ 2 := fun m => by
    rw [integral_add (hasq m) (hbsq m), integral_norm_sq_eq, integral_norm_sq_eq]
  have hgs : Summable (fun m => ∫ z, g m z) := by simp_rw [hgI]; exact hab2
  obtain ⟨hGint, hGsum⟩ := integrable_tsum_nonneg hgint hg0 hgs
  have hinner_le : ∀ m z, ‖inner ℂ (a m z) (b m z)‖ ≤ g m z := fun m z => by
    calc ‖inner ℂ (a m z) (b m z)‖ ≤ ‖a m z‖ * ‖b m z‖ := norm_inner_le_norm _ _
      _ ≤ ‖a m z‖ ^ 2 + ‖b m z‖ ^ 2 := by nlinarith [norm_nonneg (a m z), norm_nonneg (b m z)]
  refine ⟨fun z => ∑' m, inner ℂ (a m z) (b m z), ?_, ?_, ?_⟩
  · have hloc : ∀ f : Lp ℂ 2 (volume : Measure (Fin n → ℝ)),
        LocallyIntegrable (f : (Fin n → ℝ) → ℂ) volume := fun f =>
      (Lp.memLp f).locallyIntegrable (by norm_num)
    filter_upwards [ae_all_iff.2 fun m => ae_tendsto_avg n (hloc (a m)),
      ae_all_iff.2 fun m => ae_tendsto_avg n (hloc (b m)),
      ae_all_iff.2 fun m => ae_tendsto_avg n (hgint m).locallyIntegrable,
      ae_tendsto_avg n hGint.locallyIntegrable, hGsum] with z hza hzb hzg hzG hzs
    have hpos : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r := self_mem_nhdsWithin
    have hBs : ∀ r : ℝ, 0 < r → HasSum (fun m => ⨍ w in Metric.closedBall z r, g m w)
        (⨍ w in Metric.closedBall z r, ∑' m, g m w) := by
      intro r hr
      have hsum' : Summable (fun m => ∫ w in Metric.closedBall z r, ‖g m w‖) := by
        refine Summable.of_nonneg_of_le (fun m => integral_nonneg (fun _ => norm_nonneg _))
          (fun m => ?_) hgs
        have : ∀ w, ‖g m w‖ = g m w := fun w => Real.norm_of_nonneg (hg0 m w)
        simp_rw [this]
        exact setIntegral_le_integral (hgint m) (ae_of_all _ (hg0 m))
      have h := hasSum_integral_of_summable_integral_norm
        (μ := (volume : Measure (Fin n → ℝ)).restrict (Metric.closedBall z r)) (F := g)
        (fun m => (hgint m).restrict) hsum'
      simp only [setAverage_eq]
      exact h.const_smul _
    have hdom : ∀ r : ℝ, 0 < r → ∀ m,
        ‖inner ℂ (⨍ w in Metric.closedBall z r, a m w) (⨍ w in Metric.closedBall z r, b m w)‖ ≤
          ⨍ w in Metric.closedBall z r, g m w := by
      intro r hr m
      have h0 : (volume : Measure (Fin n → ℝ)) (Metric.closedBall z r) ≠ 0 :=
        (Metric.measure_closedBall_pos volume z hr).ne'
      have ht : (volume : Measure (Fin n → ℝ)) (Metric.closedBall z r) ≠ ⊤ :=
        measure_closedBall_lt_top.ne
      have ja := norm_sq_setAverage_le h0 ht
        ((hloc (a m)).integrableOn_isCompact (isCompact_closedBall z r)) (hasq m).integrableOn
      have jb := norm_sq_setAverage_le h0 ht
        ((hloc (b m)).integrableOn_isCompact (isCompact_closedBall z r)) (hbsq m).integrableOn
      have hadd : (⨍ w in Metric.closedBall z r, g m w) =
          (⨍ w in Metric.closedBall z r, ‖a m w‖ ^ 2) +
            ⨍ w in Metric.closedBall z r, ‖b m w‖ ^ 2 := by
        simp only [setAverage_eq, hg]
        rw [integral_add (hasq m).integrableOn (hbsq m).integrableOn, smul_add]
      rw [hadd]
      have hA := norm_nonneg (⨍ w in Metric.closedBall z r, a m w)
      have hB := norm_nonneg (⨍ w in Metric.closedBall z r, b m w)
      calc _ ≤ ‖⨍ w in Metric.closedBall z r, a m w‖ * ‖⨍ w in Metric.closedBall z r, b m w‖ :=
            norm_inner_le_norm _ _
        _ ≤ ‖⨍ w in Metric.closedBall z r, a m w‖ ^ 2 +
            ‖⨍ w in Metric.closedBall z r, b m w‖ ^ 2 := by nlinarith
        _ ≤ _ := add_le_add ja jb
    have hmain := tendsto_tsum_of_le_tendsto (l := 𝓝[>] (0:ℝ))
      (fun r m => inner ℂ (⨍ w in Metric.closedBall z r, a m w)
        (⨍ w in Metric.closedBall z r, b m w))
      (fun m => inner ℂ (a m z) (b m z)) (fun r m => ⨍ w in Metric.closedBall z r, g m w)
      (fun m => g m z) (fun m => (hza m).inner (hzb m)) hzg
      (hpos.mono fun r hr => (hBs r hr).summable) hzs
      (hzG.congr' (hpos.mono fun r hr => (hBs r hr).tsum_eq.symm))
      (hpos.mono fun r hr => hdom r hr)
    refine hmain.congr' ?_
    filter_upwards [hpos] with r hr
    rw [← closedBall_prod_same]
    exact (hasSum_setAverage_kernel T a b hab k hk hTk measurableSet_closedBall
      measure_closedBall_lt_top.ne).tsum_eq
  · have hmeas : AEStronglyMeasurable (fun z => ∑' m, inner ℂ (a m z) (b m z))
        (volume : Measure (Fin n → ℝ)) := by
      refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun N z => ∑ m ∈ Finset.range N, inner ℂ (a m z) (b m z)) (fun N => ?_) ?_
      · exact Finset.aestronglyMeasurable_fun_sum _
          (fun m _ => (L2.integrable_inner (𝕜 := ℂ) (a m) (b m)).aestronglyMeasurable)
      · filter_upwards [hGsum] with z hz
        exact (Summable.of_norm_bounded hz (fun m => hinner_le m z)).hasSum.tendsto_sum_nat
    refine Integrable.mono' hGint hmeas ?_
    filter_upwards [hGsum] with z hz
    exact tsum_of_norm_bounded hz.hasSum (fun m => hinner_le m z)
  · have hsum' : Summable (fun m => ∫ z, ‖inner ℂ (a m z) (b m z)‖) := by
      refine Summable.of_nonneg_of_le (fun m => integral_nonneg (fun _ => norm_nonneg _))
        (fun m => integral_mono (L2.integrable_inner (𝕜 := ℂ) (a m) (b m)).norm (hgint m)
          (fun z => hinner_le m z)) hgs
    have h := hasSum_integral_of_summable_integral_norm
      (F := fun m z => inner ℂ (a m z) (b m z))
      (fun m => L2.integrable_inner (𝕜 := ℂ) (a m) (b m)) hsum'
    have e : ∀ m, inner ℂ (a m) (b m) = ∫ z, inner ℂ (a m z) (b m z) := fun m =>
      L2.inner_def (𝕜 := ℂ) (a m) (b m)
    rw [operatorTrace_eq_tsum_inner T a b hab2 hab, ← h.tsum_eq]
    exact tsum_congr fun m => (e m).symm
