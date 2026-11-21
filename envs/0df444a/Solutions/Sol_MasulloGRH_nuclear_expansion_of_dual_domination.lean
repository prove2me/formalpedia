-- Prove2me | solution 1 for MasulloGRH.nuclear_expansion_of_dual_domination
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T23:35:20.583668+00:00
-- url     : https://prove2.me/submissions/f5cf3ea6-31f8-4581-a8ce-b0e2121e5b8e

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
open MasulloGRH
universe u

private lemma memℓp_two_of {v : ℕ → ℂ} (h : Summable fun n => ‖v n‖ ^ 2) :
    Memℓp v 2 := by
  apply memℓp_gen
  simpa using h

private lemma sum_sq_le_norm_sq (a : lp (fun _ : ℕ => ℂ) 2) (s : Finset ℕ) :
    ∑ n ∈ s, ‖a n‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) a s
  simpa using this

private lemma scale_bound {E : Type u} [AddCommGroup E] [Module ℂ E] (P : Seminorm ℂ E)
    (g : E →ₗ[ℂ] ℂ) (T : ℝ) (h : ∀ x, P x ≤ 1 → ‖g x‖ ≤ T) (x : E) : ‖g x‖ ≤ P x * T := by
  by_cases hx : P x = 0
  · have key : ∀ t : ℝ, 0 < t → t * ‖g x‖ ≤ T := by
      intro t ht
      have h1 : P ((t : ℂ) • x) ≤ 1 := by
        rw [map_smul_eq_mul, hx, mul_zero]; exact zero_le_one
      have := h _ h1
      rwa [map_smul, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at this
    have hg : ‖g x‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖g x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have := key ((|T| + 1) / ‖g x‖) (by positivity)
      rw [div_mul_cancel₀ _ hne] at this
      linarith [le_abs_self T]
    rw [hg, hx, zero_mul]
  · have hpos : 0 < P x := lt_of_le_of_ne (apply_nonneg P x) (Ne.symm hx)
    have h1 : P ((((P x)⁻¹ : ℝ) : ℂ) • x) ≤ 1 := by
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
        inv_mul_cancel₀ hx]
    have := h _ h1
    rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 hpos.le)] at this
    rw [inv_mul_le_iff₀ hpos] at this
    exact this

/-- AM-GM -/
private lemma sqrt_mul_le (c a : ℝ) (hc : 0 ≤ c) : Real.sqrt c * a ≤ (c + a ^ 2) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt c - a), Real.sq_sqrt hc]

local notation "H" => lp (fun _ : ℕ => ℂ) 2

private lemma step_one {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (q p : Seminorm ℂ E) (y : ℕ → E) (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c)
    (hy : ∀ n, q (y n) ≤ 1)
    (hd : ∀ f : StrongDual ℂ E, (∀ x, ‖f x‖ ≤ q x) →
      ∀ x, p x ≤ 1 → ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖) :
    ∃ (φ : ℕ → E →ₗ[ℂ] ℂ) (C : ℝ), 0 ≤ C ∧
      (∀ x (s : Finset ℕ), ∑ n ∈ s, ‖φ n x‖ ^ 2 ≤ (C * p x) ^ 2) ∧
      (∀ f : StrongDual ℂ E, (∀ x, ‖f x‖ ≤ q x) → ∀ x,
        HasSum (fun n => φ n x * ((Real.sqrt (c n) : ℂ) * f (y n))) (f x)) := by
  set C := Real.sqrt (∑' n, c n) with hCdef
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  -- the subspace of functionals dominated by a multiple of `q`
  let V : Submodule ℂ (StrongDual ℂ E) :=
    { carrier := {f | ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖f x‖ ≤ K * q x}
      add_mem' := by
        rintro f g ⟨K, hK, hf⟩ ⟨L, hL, hg⟩
        refine ⟨K + L, add_nonneg hK hL, fun x => ?_⟩
        calc ‖(f + g) x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
          _ ≤ K * q x + L * q x := add_le_add (hf x) (hg x)
          _ = (K + L) * q x := by ring
      zero_mem' := ⟨0, le_rfl, fun x => by simp⟩
      smul_mem' := by
        rintro t f ⟨K, hK, hf⟩
        refine ⟨‖t‖ * K, mul_nonneg (norm_nonneg _) hK, fun x => ?_⟩
        rw [smul_apply, smul_eq_mul, norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _) }
  have hmem : ∀ f : V, Memℓp (fun n => (Real.sqrt (c n) : ℂ) * (f : StrongDual ℂ E) (y n)) 2 := by
    rintro ⟨f, K, hK, hf⟩
    apply memℓp_two_of
    refine (hcs.mul_right (K ^ 2)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hc0 n)]
    refine mul_le_mul_of_nonneg_left ?_ (hc0 n)
    have h1 : ‖f (y n)‖ ≤ K := by
      have := hf (y n)
      nlinarith [hy n, apply_nonneg q (y n)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  let Φ : V →ₗ[ℂ] H :=
    { toFun := fun f => ⟨_, hmem f⟩
      map_add' := by
        intro f g; ext n
        simp only [Submodule.coe_add, add_apply, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := by
        intro t f; ext n
        simp only [Submodule.coe_smul, smul_apply, smul_eq_mul,
          lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        ring }
  have hΦ : ∀ f n, (Φ f : ℕ → ℂ) n = (Real.sqrt (c n) : ℂ) * (f : StrongDual ℂ E) (y n) :=
    fun _ _ => rfl
  -- the key domination estimate
  have hbd : ∀ (f : V) x, ‖(f : StrongDual ℂ E) x‖ ≤ C * p x * ‖Φ f‖ := by
    rintro ⟨f, K, hK, hf⟩ x
    have hK1 : 0 < K + 1 := by linarith
    have hT : ∀ x, p x ≤ 1 → ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
      intro x hx
      have := hd (((K + 1)⁻¹ : ℝ) • f) (fun z => by
        rw [smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hK1.le),
          inv_mul_le_iff₀ hK1]
        have := hf z
        nlinarith [apply_nonneg q z]) x hx
      simp only [smul_apply, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 hK1.le)] at this
      have e : ∀ n, c n * ((K + 1)⁻¹ * ‖f (y n)‖) = (K + 1)⁻¹ * (c n * ‖f (y n)‖) :=
        fun n => by ring
      simp_rw [e] at this
      rw [tsum_mul_left] at this
      exact le_of_mul_le_mul_left this (inv_pos.2 hK1)
    have hT2 : ∑' n, c n * ‖f (y n)‖ ≤ C * ‖Φ ⟨f, K, hK, hf⟩‖ := by
      refine Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (hc0 n) (norm_nonneg _)) ?_
      intro N
      calc ∑ i ∈ Finset.range N, c i * ‖f (y i)‖
          = ∑ i ∈ Finset.range N, Real.sqrt (c i) * (Real.sqrt (c i) * ‖f (y i)‖) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← mul_assoc, Real.mul_self_sqrt (hc0 i)]
        _ ≤ Real.sqrt (∑ i ∈ Finset.range N, Real.sqrt (c i) ^ 2) *
            Real.sqrt (∑ i ∈ Finset.range N, (Real.sqrt (c i) * ‖f (y i)‖) ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ ≤ C * ‖Φ ⟨f, K, hK, hf⟩‖ := by
            apply mul_le_mul _ _ (Real.sqrt_nonneg _) hC0
            · apply Real.sqrt_le_sqrt
              simp_rw [Real.sq_sqrt (hc0 _)]
              exact hcs.sum_le_tsum _ (fun i _ => hc0 i)
            · rw [← Real.sqrt_sq (norm_nonneg (Φ ⟨f, K, hK, hf⟩))]
              apply Real.sqrt_le_sqrt
              refine le_trans (le_of_eq ?_) (sum_sq_le_norm_sq _ (Finset.range N))
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hΦ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have := scale_bound p f.toLinearMap _ hT x
    calc ‖f x‖ ≤ p x * ∑' n, c n * ‖f (y n)‖ := this
      _ ≤ p x * (C * ‖Φ ⟨f, K, hK, hf⟩‖) := mul_le_mul_of_nonneg_left hT2 (apply_nonneg p x)
      _ = C * p x * ‖Φ ⟨f, K, hK, hf⟩‖ := by ring
  -- representing vectors
  have hrep : ∀ x : E, ∃ u : H, ‖u‖ ≤ C * p x ∧
      ∀ f : V, inner ℂ u (Φ f) = (f : StrongDual ℂ E) x := by
    intro x
    have hwd : ∀ f g : V, Φ f = Φ g → (f : StrongDual ℂ E) x = (g : StrongDual ℂ E) x := by
      intro f g hfg
      have := hbd (f - g) x
      have e : Φ (f - g) = 0 := by
        ext n
        rw [hΦ, Submodule.coe_sub, sub_apply, mul_sub, ← hΦ, ← hΦ, hfg]
        simp
      rw [e, norm_zero, mul_zero] at this
      have h0 := norm_le_zero_iff.1 this
      rw [Submodule.coe_sub, sub_apply] at h0
      exact sub_eq_zero.1 h0
    let pick : LinearMap.range Φ → V := fun v => Classical.choose v.2
    have hpick : ∀ v : LinearMap.range Φ, Φ (pick v) = v := fun v => Classical.choose_spec v.2
    let ℓ : LinearMap.range Φ →ₗ[ℂ] ℂ :=
      { toFun := fun v => (pick v : StrongDual ℂ E) x
        map_add' := fun v w => by
          have := hwd (pick (v + w)) (pick v + pick w) (by
            rw [map_add, hpick, hpick, hpick, Submodule.coe_add])
          rw [this]; simp
        map_smul' := fun t v => by
          have := hwd (pick (t • v)) (t • pick v) (by
            rw [map_smul, hpick, hpick, Submodule.coe_smul])
          rw [this]; simp }
    have hℓ : ∀ f : V, ℓ ⟨Φ f, LinearMap.mem_range_self Φ f⟩ = (f : StrongDual ℂ E) x := by
      intro f
      exact hwd _ _ (hpick _)
    have hCp : 0 ≤ C * p x := mul_nonneg hC0 (apply_nonneg p x)
    have hℓb : ∀ v : LinearMap.range Φ, ‖ℓ v‖ ≤ C * p x * ‖v‖ := by
      rintro ⟨v, f, rfl⟩
      rw [hℓ]
      exact hbd f x
    let L : StrongDual ℂ (LinearMap.range Φ) := ℓ.mkContinuous (C * p x) hℓb
    obtain ⟨F, hFe, hFn⟩ := exists_extension_norm_eq (LinearMap.range Φ) L
    refine ⟨(InnerProductSpace.toDual ℂ H).symm F, ?_, fun f => ?_⟩
    · rw [LinearIsometryEquiv.norm_map, hFn]
      exact LinearMap.mkContinuous_norm_le _ hCp _
    · rw [InnerProductSpace.toDual_symm_apply]
      have := hFe ⟨Φ f, LinearMap.mem_range_self Φ f⟩
      rw [this]
      exact hℓ f
  choose u hu_norm hu_inner using hrep
  set R := LinearMap.range Φ
  set K := R.topologicalClosure
  have : CompleteSpace K := R.isClosed_topologicalClosure.completeSpace_coe
  let a : E → H := fun x => K.starProjection (u x)
  have ha_mem : ∀ x, a x ∈ K := fun x => K.starProjection_apply_mem _
  have ha_inner : ∀ x (f : V), inner ℂ (a x) (Φ f) = (f : StrongDual ℂ E) x := by
    intro x f
    have hv : Φ f ∈ K := R.le_topologicalClosure (LinearMap.mem_range_self Φ f)
    have := K.starProjection_inner_eq_zero (u x) (Φ f) hv
    rw [inner_sub_left, sub_eq_zero] at this
    rw [← this, hu_inner]
  have ha_norm : ∀ x, ‖a x‖ ≤ C * p x := fun x =>
    (K.norm_starProjection_apply_le (u x)).trans (hu_norm x)
  have uniq : ∀ w ∈ K, (∀ f : V, inner ℂ w (Φ f) = 0) → w = 0 := by
    intro w hw h
    have h1 : w ∈ Rᗮ := by
      rw [Submodule.mem_orthogonal']
      rintro v ⟨f, rfl⟩
      exact h f
    rw [← Submodule.orthogonal_closure] at h1
    have : w ∈ K ⊓ Kᗮ := ⟨hw, h1⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  have ha_add : ∀ x z, a (x + z) = a x + a z := by
    intro x z
    refine sub_eq_zero.1 (uniq _ (K.sub_mem (ha_mem _) (K.add_mem (ha_mem _) (ha_mem _))) ?_)
    intro f
    rw [inner_sub_left, inner_add_left, ha_inner, ha_inner, ha_inner, map_add]
    ring
  have ha_smul : ∀ (t : ℂ) x, a (t • x) = (starRingEnd ℂ t) • a x := by
    intro t x
    refine sub_eq_zero.1 (uniq _ (K.sub_mem (ha_mem _) (K.smul_mem _ (ha_mem _))) ?_)
    intro f
    rw [inner_sub_left, inner_smul_left, ha_inner, ha_inner, map_smul, smul_eq_mul,
      Complex.conj_conj]
    ring
  let φ : ℕ → E →ₗ[ℂ] ℂ := fun n =>
    { toFun := fun x => starRingEnd ℂ ((a x : ℕ → ℂ) n)
      map_add' := fun x z => by
        rw [ha_add, lp.coeFn_add, Pi.add_apply, map_add]
      map_smul' := fun t x => by
        rw [ha_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj,
          RingHom.id_apply, smul_eq_mul] }
  refine ⟨φ, C, hC0, fun x s => ?_, fun f hf x => ?_⟩
  · calc ∑ n ∈ s, ‖φ n x‖ ^ 2 = ∑ n ∈ s, ‖(a x : ℕ → ℂ) n‖ ^ 2 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          simp [φ]
      _ ≤ ‖a x‖ ^ 2 := sum_sq_le_norm_sq _ _
      _ ≤ (C * p x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (ha_norm x) 2
  · let f' : V := ⟨f, 1, zero_le_one, fun z => by rw [one_mul]; exact hf z⟩
    have := lp.hasSum_inner (𝕜 := ℂ) (a x) (Φ f')
    rw [ha_inner] at this
    have e : (fun n => φ n x * ((Real.sqrt (c n) : ℂ) * f (y n))) =
        (fun i => inner ℂ ((a x : ℕ → ℂ) i) ((Φ f' : ℕ → ℂ) i)) := by
      funext n
      rw [RCLike.inner_apply', hΦ]
      rfl
    rw [e]
    exact this

private lemma exists_norming {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] (q : Seminorm ℂ E) (hq : Continuous q) (z : E) :
    ∃ f : StrongDual ℂ E, (∀ w, ‖f w‖ ≤ q w) ∧ ‖f z‖ = q z := by
  by_cases hz : q z = 0
  · exact ⟨0, fun w => by simp, by simp [hz]⟩
  have hz0 : z ≠ 0 := fun h => hz (by rw [h, map_zero])
  have H0 : ∀ c : ℂ, c • z = 0 → (RingHom.id ℂ) c • ((q z : ℝ) : ℂ) = 0 := fun c hc =>
    (smul_eq_zero.1 hc).elim (fun hc => by rw [hc, RingHom.map_zero, zero_smul])
      fun hx' => absurd hx' hz0
  let g := LinearPMap.mkSpanSingleton' (σ := RingHom.id ℂ) z ((q z : ℝ) : ℂ) H0
  have hg : ∀ (t : ℂ) (h : t • z ∈ g.domain), g ⟨t • z, h⟩ = t * (q z : ℂ) := by
    intro t h
    have := LinearPMap.mkSpanSingleton'_apply (σ := RingHom.id ℂ) z ((q z : ℝ) : ℂ) H0 t h
    rw [this, RingHom.id_apply, smul_eq_mul]
  obtain ⟨f, hfe, hfb⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm g.domain
    g.toFun hq (by
      rintro ⟨v, hv⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
      change ‖g ⟨t • z, hv⟩‖ ≤ q (t • z)
      rw [hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q z),
        map_smul_eq_mul])
  refine ⟨f, hfb, ?_⟩
  have hzmem : z ∈ g.domain := Submodule.mem_span_singleton_self z
  have := hfe ⟨z, hzmem⟩
  simp only at this
  rw [this]
  have h1 := hg 1 (by simpa using hzmem)
  simp only [one_smul, one_mul] at h1
  change ‖g ⟨z, hzmem⟩‖ = q z
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q z)]

private lemma tail_tendsto {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] (q : Seminorm ℂ E) (hq : Continuous q) (y : ℕ → E) (c : ℕ → ℝ)
    (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c) (hy : ∀ n, q (y n) ≤ 1)
    (φ : ℕ → E →ₗ[ℂ] ℂ) (x : E) (B : ℝ)
    (hsq : ∀ N, ∑ n ∈ Finset.range N, ‖φ n x‖ ^ 2 ≤ B)
    (hrep : ∀ f : StrongDual ℂ E, (∀ w, ‖f w‖ ≤ q w) →
      HasSum (fun n => φ n x * ((Real.sqrt (c n) : ℂ) * f (y n))) (f x)) :
    Filter.Tendsto
      (fun N : ℕ => q (x - ∑ n ∈ Finset.range N, ((Real.sqrt (c n) : ℂ) * φ n x) • y n))
      Filter.atTop (nhds 0) := by
  set b : ℕ → ℝ := fun n => Real.sqrt (c n) * ‖φ n x‖ with hbdef
  have hs2 : Summable (fun n => ‖φ n x‖ ^ 2) :=
    summable_of_sum_range_le (fun n => by positivity) hsq
  have hb : Summable b :=
    ((hcs.add hs2).div_const 2).of_nonneg_of_le
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (fun n => sqrt_mul_le (c n) _ (hc0 n))
  have key : ∀ N : ℕ, q (x - ∑ n ∈ Finset.range N, ((Real.sqrt (c n) : ℂ) * φ n x) • y n) ≤
      ∑' k, b (k + N) := by
    intro N
    obtain ⟨f, hfq, hfz⟩ := exists_norming q hq
      (x - ∑ n ∈ Finset.range N, ((Real.sqrt (c n) : ℂ) * φ n x) • y n)
    rw [← hfz]
    have hS := hrep f hfq
    set t : ℕ → ℂ := fun n => φ n x * ((Real.sqrt (c n) : ℂ) * f (y n)) with htdef
    have e : f (x - ∑ n ∈ Finset.range N, ((Real.sqrt (c n) : ℂ) * φ n x) • y n) =
        ∑' k, t (k + N) := by
      have h1 := hS.summable.sum_add_tsum_nat_add N
      rw [hS.tsum_eq] at h1
      have h2 : f (∑ n ∈ Finset.range N, ((Real.sqrt (c n) : ℂ) * φ n x) • y n) =
          ∑ n ∈ Finset.range N, t n := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [map_smul, smul_eq_mul, htdef]
        ring
      rw [map_sub, h2, ← h1]
      ring
    have hbt : ∀ k, ‖t (k + N)‖ ≤ b (k + N) := by
      intro k
      rw [htdef, hbdef]
      simp only
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have h1 : ‖f (y (k + N))‖ ≤ 1 := (hfq _).trans (hy _)
      have h2 : 0 ≤ ‖φ (k + N) x‖ * Real.sqrt (c (k + N)) :=
        mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
      calc ‖φ (k + N) x‖ * (Real.sqrt (c (k + N)) * ‖f (y (k + N))‖)
          = ‖φ (k + N) x‖ * Real.sqrt (c (k + N)) * ‖f (y (k + N))‖ := by ring
        _ ≤ ‖φ (k + N) x‖ * Real.sqrt (c (k + N)) * 1 := mul_le_mul_of_nonneg_left h1 h2
        _ = Real.sqrt (c (k + N)) * ‖φ (k + N) x‖ := by ring
    have hbN : Summable (fun k => b (k + N)) := (summable_nat_add_iff N).2 hb
    have htN : Summable (fun k => ‖t (k + N)‖) :=
      hbN.of_nonneg_of_le (fun k => norm_nonneg _) hbt
    rw [e]
    exact (norm_tsum_le_tsum_norm htN).trans (htN.tsum_le_tsum hbt hbN)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_sum_nat_add b)
    (fun N => apply_nonneg q _) key

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (hdom : ∀ q : Seminorm ℂ E, Continuous q →
      ∃ (p : Seminorm ℂ E) (y : ℕ → E) (c : ℕ → ℝ),
        Continuous p ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n, q (y n) ≤ 1) ∧
        ∀ f : StrongDual ℂ E, (∀ x, ‖f x‖ ≤ q x) →
          ∀ x, p x ≤ 1 → ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖)
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (r : Seminorm ℂ E) (y : ℕ → E) (g : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      Continuous r ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n, q (y n) ≤ 1) ∧
      (∀ n x, ‖g n x‖ ≤ r x) ∧
      ∀ x, Filter.Tendsto
        (fun N : ℕ => q (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * g n x) • y n))
        Filter.atTop (nhds 0) := by
  obtain ⟨ι, _, pf, hpf⟩ := hE.1
  have : PolynormableSpace ℂ E := hpf.toPolynormableSpace
  obtain ⟨p, y, c, hp, hc0, hcs, hy, hd⟩ := hdom q hq
  obtain ⟨φ, C, hC0, hsq, hrep⟩ := step_one q p y c hc0 hcs hy hd
  obtain ⟨r, w, d, hr, hd0, hds, hw, hdd⟩ := hdom p hp
  have hφp : ∀ n x, ‖φ n x‖ ≤ C * p x := by
    intro n x
    have := hsq x {n}
    rw [Finset.sum_singleton] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC0 (apply_nonneg p x))
      two_ne_zero).1 this
  have hcont : ∀ (g : E →ₗ[ℂ] ℂ) (M : NNReal) (P : Seminorm ℂ E), Continuous P →
      (∀ x, ‖g x‖ ≤ M * P x) → Continuous g := by
    intro g M P hP hg
    refine (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng ℂ g
      ⟨{⟨P, hP⟩}, M, fun x => ?_⟩
    simpa [NNReal.smul_def, smul_eq_mul] using hg x
  let ψ : ℕ → StrongDual ℂ E := fun n => ⟨φ n, hcont (φ n) ⟨C, hC0⟩ p hp (hφp n)⟩
  have hψ : ∀ n x, ψ n x = φ n x := fun _ _ => rfl
  let t : ℕ → ℝ := fun n => ∑' m, d m * ‖φ n (w m)‖
  have hdsum : ∀ n, Summable (fun m => d m * ‖φ n (w m)‖) := by
    intro n
    refine (hds.mul_right C).of_nonneg_of_le
      (fun m => mul_nonneg (hd0 m) (norm_nonneg _)) (fun m => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hd0 m)
    calc ‖φ n (w m)‖ ≤ C * p (w m) := hφp n _
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (hw m) hC0
      _ = C := mul_one C
  have ht0 : ∀ n, 0 ≤ t n := fun n => tsum_nonneg fun m => mul_nonneg (hd0 m) (norm_nonneg _)
  have hφr : ∀ n x, ‖φ n x‖ ≤ r x * t n := by
    intro n
    apply scale_bound r (φ n) (t n)
    intro x hx
    have hC1 : 0 < C + 1 := by linarith
    have := hdd (((C + 1)⁻¹ : ℝ) • ψ n) (fun z => by
      rw [smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hC1.le),
        inv_mul_le_iff₀ hC1, hψ]
      have := hφp n z
      nlinarith [apply_nonneg p z]) x hx
    simp only [smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hC1.le), hψ] at this
    have e : ∀ m, d m * ((C + 1)⁻¹ * ‖φ n (w m)‖) = (C + 1)⁻¹ * (d m * ‖φ n (w m)‖) :=
      fun m => by ring
    simp_rw [e] at this
    rw [tsum_mul_left] at this
    exact le_of_mul_le_mul_left this (inv_pos.2 hC1)
  let c' : ℕ → ℝ := fun n => Real.sqrt (c n) * t n
  let g : ℕ → StrongDual ℂ E := fun n => ((t n : ℂ))⁻¹ • ψ n
  have hc'0 : ∀ n, 0 ≤ c' n := fun n => mul_nonneg (Real.sqrt_nonneg _) (ht0 n)
  have hc's : Summable c' := by
    refine summable_of_sum_range_le hc'0 (c := ((∑' n, c n) + C ^ 2) / 2 * ∑' m, d m)
      (fun N => ?_)
    calc ∑ n ∈ Finset.range N, c' n
        = ∑ n ∈ Finset.range N, ∑' m, Real.sqrt (c n) * (d m * ‖φ n (w m)‖) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [tsum_mul_left]
      _ = ∑' m, ∑ n ∈ Finset.range N, Real.sqrt (c n) * (d m * ‖φ n (w m)‖) :=
          (Summable.tsum_finsetSum fun n _ => (hdsum n).mul_left _).symm
      _ ≤ ∑' m, ((∑' n, c n) + C ^ 2) / 2 * d m := by
          refine Summable.tsum_le_tsum (fun m => ?_)
            (summable_sum fun n _ => (hdsum n).mul_left _) (hds.mul_left _)
          have e : ∑ n ∈ Finset.range N, Real.sqrt (c n) * (d m * ‖φ n (w m)‖) =
              d m * ∑ n ∈ Finset.range N, Real.sqrt (c n) * ‖φ n (w m)‖ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            ring
          rw [e, mul_comm _ (d m)]
          refine mul_le_mul_of_nonneg_left ?_ (hd0 m)
          calc ∑ n ∈ Finset.range N, Real.sqrt (c n) * ‖φ n (w m)‖
              ≤ ∑ n ∈ Finset.range N, (c n + ‖φ n (w m)‖ ^ 2) / 2 :=
                Finset.sum_le_sum fun n _ => sqrt_mul_le _ _ (hc0 n)
            _ = ((∑ n ∈ Finset.range N, c n) + ∑ n ∈ Finset.range N, ‖φ n (w m)‖ ^ 2) / 2 := by
                rw [← Finset.sum_add_distrib, Finset.sum_div]
            _ ≤ ((∑' n, c n) + C ^ 2) / 2 := by
                have h1 := hcs.sum_le_tsum (Finset.range N) (fun i _ => hc0 i)
                have h2 := hsq (w m) (Finset.range N)
                have h3 : (C * p (w m)) ^ 2 ≤ C ^ 2 := by
                  rw [mul_pow]
                  have : p (w m) ^ 2 ≤ 1 := by
                    have := hw m
                    nlinarith [apply_nonneg p (w m)]
                  nlinarith [sq_nonneg C]
                linarith
      _ = ((∑' n, c n) + C ^ 2) / 2 * ∑' m, d m := tsum_mul_left
  have hg : ∀ n x, ‖g n x‖ ≤ r x := by
    intro n x
    simp only [g, smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (ht0 n), hψ]
    rcases (ht0 n).eq_or_lt with h | h
    · rw [← h, inv_zero, zero_mul]; exact apply_nonneg r x
    · rw [inv_mul_le_iff₀ h, mul_comm]; exact hφr n x
  refine ⟨r, y, g, c', hr, hc'0, hc's, hy, hg, fun x => ?_⟩
  have e : ∀ N, ∑ n ∈ Finset.range N, ((c' n : ℂ) * g n x) • y n =
      ∑ n ∈ Finset.range N, ((Real.sqrt (c n) : ℂ) * φ n x) • y n := by
    intro N
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    simp only [c', g, smul_apply, smul_eq_mul, hψ, Complex.ofReal_mul]
    rcases (ht0 n).eq_or_lt with h | h
    · have : φ n x = 0 := by
        have := hφr n x
        rw [← h, mul_zero] at this
        exact norm_le_zero_iff.1 this
      rw [this]; ring
    · have : (t n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h.ne'
      field_simp
  simp_rw [e]
  exact tail_tendsto q hq y c hc0 hcs hy φ x ((C * p x) ^ 2) (fun N => hsq x _)
    (fun f hf => hrep f hf x)
