-- Prove2me | solution 1 for MasulloGRH.nuclear_equicontinuous_basis_absolute
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T19:36:57.989174+00:00
-- url     : https://prove2.me/submissions/c9381062-a086-4523-9ae8-f279cbc4e763

import Mathlib
import Definitions.Def_MasulloGRH_SchauderBases
import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination

set_option autoImplicit false

namespace MasulloGRHBasisAbsAux

open MasulloGRH Finset InnerProductSpace

lemma sq_bound {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (h : A ≤ c * √A) : A ≤ c ^ 2 := by
  have hs := Real.sq_sqrt hA
  have h0 := Real.sqrt_nonneg A
  by_cases hz : √A = 0
  · rw [hz] at hs; nlinarith
  · have hpos : 0 < √A := lt_of_le_of_ne h0 (Ne.symm hz)
    have h1 : √A ≤ c := by
      by_contra hlt
      rw [not_le] at hlt
      nlinarith
    have := pow_le_pow_left₀ h0 h1 2
    rwa [hs] at this

lemma cs_tsum (e t : ℕ → ℝ) (he : ∀ j, 0 ≤ e j) (ht : ∀ j, 0 ≤ t j) (hse : Summable e)
    (hs2 : Summable fun j => e j * t j ^ 2) :
    ∑' j, e j * t j ≤ √(∑' j, e j) * √(∑' j, e j * t j ^ 2) := by
  have key : ∀ G : Finset ℕ, ∑ j ∈ G, e j * t j ≤ √(∑' j, e j) * √(∑' j, e j * t j ^ 2) := by
    intro G
    calc ∑ j ∈ G, e j * t j = ∑ j ∈ G, √(e j) * (√(e j) * t j) :=
          sum_congr rfl fun j _ => by rw [← mul_assoc, Real.mul_self_sqrt (he j)]
      _ ≤ √(∑ j ∈ G, √(e j) ^ 2) * √(∑ j ∈ G, (√(e j) * t j) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ _ := by
          apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          · apply Real.sqrt_le_sqrt
            rw [sum_congr rfl fun j _ => Real.sq_sqrt (he j)]
            exact hse.sum_le_tsum G (fun j _ => he j)
          · apply Real.sqrt_le_sqrt
            rw [sum_congr rfl fun j _ => by rw [mul_pow, Real.sq_sqrt (he j)]]
            exact hs2.sum_le_tsum G (fun j _ => mul_nonneg (he j) (sq_nonneg _))
  exact Real.tsum_le_of_sum_le (fun j => mul_nonneg (he j) (ht j)) key

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

lemma bessel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Θ : E →ₗ[ℂ] H)
    (g : E →ₗ[ℂ] ℂ) (κ : ℝ) (hκ : 0 ≤ κ) (hg : ∀ u, ‖g u‖ ≤ κ * ‖Θ u‖) (w : ℕ → E)
    (F : Finset ℕ)
    (hon : ∀ i ∈ F, ∀ j ∈ F, inner ℂ (Θ (w i)) (Θ (w j)) = if i = j then (1 : ℂ) else 0) :
    ∑ i ∈ F, ‖g (w i)‖ ^ 2 ≤ κ ^ 2 := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ i ∈ F, ‖g (w i)‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : E, u = ∑ i ∈ F, (starRingEnd ℂ) (g (w i)) • w i := ⟨_, rfl⟩
  have hA : 0 ≤ A := hAdef ▸ sum_nonneg fun _ _ => sq_nonneg _
  have hgu : g u = (A : ℂ) := by
    rw [hu, hAdef, map_sum]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; rfl
  have hin : inner ℂ (Θ u) (Θ u) = (A : ℂ) := by
    rw [hu, hAdef, map_sum, inner_sum]
    push_cast
    refine sum_congr rfl fun j hj => ?_
    rw [sum_inner, sum_eq_single_of_mem j hj]
    · rw [map_smul, inner_smul_left, inner_smul_right, hon j hj j hj, if_pos rfl, mul_one,
        Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    · intro i hi hij
      rw [map_smul, map_smul, inner_smul_left, inner_smul_right, hon i hi j hj, if_neg hij]
      simp
  have hΘ : ‖Θ u‖ ^ 2 = A := by
    rw [inner_self_eq_norm_sq_to_K] at hin
    have h' : ((‖Θ u‖ ^ 2 : ℝ) : ℂ) = (A : ℂ) := by push_cast; exact hin
    exact Complex.ofReal_injective h'
  have hΘ' : ‖Θ u‖ = √A := by rw [← hΘ, Real.sqrt_sq (norm_nonneg _)]
  rw [← hAdef]
  apply sq_bound hA hκ
  have := hg u
  rwa [hgu, Complex.norm_real, Real.norm_of_nonneg hA, hΘ'] at this

lemma stepA [TopologicalSpace E] (hE : IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (heq : IsEquicontinuousBasis x f) (a : Seminorm ℂ E) (ha : Continuous a) :
    ∃ b : Seminorm ℂ E, Continuous b ∧ ∀ m u, ‖f m u‖ * a (x m) ≤ b u := by
  obtain ⟨⟨ι, _, P, hP⟩, _⟩ := hE
  have := hP.topologicalAddGroup
  have := hP.continuousSMul
  obtain ⟨V, hV, hVU⟩ := heq (a.ball 0 1) (Seminorm.ball_mem_nhds ha one_pos)
  obtain ⟨⟨s, ε⟩, hε, hsV⟩ := hP.hasBasis_zero_ball.mem_iff.1 hV
  simp only at hε hsV
  obtain ⟨S, hSdef⟩ : ∃ S : Seminorm ℂ E, S = s.sup P := ⟨_, rfl⟩
  rw [← hSdef] at hsV
  have hS : Continuous S := by
    refine Seminorm.continuous (r := ε) ?_
    rw [hSdef]
    exact hP.hasBasis_zero_ball.mem_of_mem (i := (s, ε)) hε
  have hlin : ∀ k (c : ℂ) u, basicProjection x f k (c • u) = c • basicProjection x f k u := by
    intro k c u; simp [basicProjection, Finset.smul_sum, smul_smul]
  have hP1 : ∀ k u, a (basicProjection x f k u) ≤ S u / ε := by
    intro k u
    apply le_of_forall_pos_lt_add
    intro δ hδ
    have hT : 0 < S u + ε * δ := add_pos_of_nonneg_of_pos (apply_nonneg S u) (mul_pos hε hδ)
    have hc : 0 ≤ ε / (S u + ε * δ) := (div_pos hε hT).le
    have hmem : (((ε / (S u + ε * δ) : ℝ) : ℂ) • u) ∈ S.ball 0 ε := by
      rw [Seminorm.mem_ball_zero, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hc,
        div_mul_eq_mul_div, div_lt_iff₀ hT]
      nlinarith [mul_pos hε hδ]
    have h1 := hVU k _ (hsV hmem)
    rw [hlin, Seminorm.mem_ball_zero, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hc,
      div_mul_eq_mul_div, div_lt_one hT] at h1
    have h2 : a (basicProjection x f k u) < (S u + ε * δ) / ε := by
      rw [lt_div_iff₀ hε]; linarith
    have h3 : (S u + ε * δ) / ε = S u / ε + δ := by field_simp
    linarith
  have h2ε : 0 ≤ 2 / ε := by positivity
  refine ⟨Real.toNNReal (2 / ε) • S, ?_, ?_⟩
  · rw [FunLike.coe_smul]; exact hS.const_smul _
  · intro m u
    have hval : (Real.toNNReal (2 / ε) • S) u = 2 / ε * S u := by
      simp [NNReal.smul_def, Real.coe_toNNReal _ h2ε]
    rw [hval, ← map_smul_eq_mul]
    have hSu : 0 ≤ S u / ε := div_nonneg (apply_nonneg _ _) hε.le
    have e2 : 2 / ε * S u = S u / ε + S u / ε := by ring
    cases m with
    | zero =>
      have : f 0 u • x 0 = basicProjection x f 0 u := by simp [basicProjection]
      rw [this]
      linarith [hP1 0 u]
    | succ m =>
      have : f (m + 1) u • x (m + 1) = basicProjection x f (m + 1) u - basicProjection x f m u := by
        simp [basicProjection, Finset.sum_range_succ _ (m + 1)]
      rw [this]
      linarith [hP1 (m + 1) u, hP1 m u,
        map_sub_le_add a (basicProjection x f (m + 1) u) (basicProjection x f m u)]

noncomputable abbrev H2 := lp (fun _ : ℕ => ℂ) 2

lemma stepB [TopologicalSpace E] [IsTopologicalAddGroup E] (hN : IsNuclear E)
    (b : Seminorm ℂ E) (hb : Continuous b) :
    ∃ (Θ : E →ₗ[ℂ] H2) (K : ℝ), 0 ≤ K ∧ Continuous (fun u => ‖Θ u‖) ∧
      (∀ u, b u ≤ K * ‖Θ u‖) ∧
      ∀ (w : ℕ → E) (F : Finset ℕ),
        (∀ i ∈ F, ∀ j ∈ F, inner ℂ (Θ (w i)) (Θ (w j)) = if i = j then (1 : ℂ) else 0) →
        ∑ i ∈ F, b (w i) ^ 2 ≤ K ^ 2 := by
  obtain ⟨s, g, c, hs, hc, hcs, hgs, hbc⟩ := nuclear_quasinuclear_domination E hN b hb
  obtain ⟨s', h, e, hs', he, hes, hhs, hse⟩ := nuclear_quasinuclear_domination E hN s hs
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have h2' : (2 : ENNReal).toReal = (2 : ℕ) := by norm_num
  have hsum : ∀ u, Summable fun j => e j * ‖h j u‖ ^ 2 := fun u =>
    Summable.of_nonneg_of_le (fun j => mul_nonneg (he j) (sq_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hhs j u) 2) (he j))
      (hes.mul_right _)
  have hnorm : ∀ j u, ‖((√(e j) : ℝ) : ℂ) * h j u‖ ^ (2 : ENNReal).toReal
      = e j * ‖h j u‖ ^ 2 := by
    intro j u
    rw [h2', Real.rpow_natCast, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (he j)]
  have hmem : ∀ u, Memℓp (fun j => ((√(e j) : ℝ) : ℂ) * h j u) 2 := fun u =>
    memℓp_gen (by simp only [hnorm]; exact hsum u)
  let Θ : E →ₗ[ℂ] H2 :=
    { toFun := fun u => ⟨_, hmem u⟩
      map_add' := by intro u v; ext j; exact (congrArg _ (map_add (h j) u v)).trans (mul_add _ _ _)
      map_smul' := by
        intro c u; ext j
        show _ * h j (c • u) = c * (_ * h j u)
        rw [map_smul, smul_eq_mul]; ring }
  have hΘ : ∀ u, ‖Θ u‖ ^ 2 = ∑' j, e j * ‖h j u‖ ^ 2 := by
    intro u
    have e1 : ‖Θ u‖ ^ (2 : ENNReal).toReal = ‖Θ u‖ ^ 2 := by rw [h2', Real.rpow_natCast]
    rw [← e1, lp.norm_rpow_eq_tsum h2]
    exact tsum_congr fun j => hnorm j u
  obtain ⟨Se, hSedef⟩ : ∃ Se : ℝ, Se = ∑' j, e j := ⟨_, rfl⟩
  obtain ⟨Sc, hScdef⟩ : ∃ Sc : ℝ, Sc = ∑' j, c j := ⟨_, rfl⟩
  have hSe : 0 ≤ Se := hSedef ▸ tsum_nonneg he
  have hSc : 0 ≤ Sc := hScdef ▸ tsum_nonneg hc
  have hΘle : ∀ u, ‖Θ u‖ ≤ √Se * s' u := by
    intro u
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)) two_ne_zero, hΘ, mul_pow,
      Real.sq_sqrt hSe, hSedef, ← tsum_mul_right]
    exact (hsum u).tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hhs j u) 2) (he j))
      (hes.mul_right _)
  have hcont : Continuous (fun u => ‖Θ u‖) := by
    have hle : (normSeminorm ℂ H2).comp Θ ≤ Real.toNNReal (√Se) • s' := by
      intro u
      have : (Real.toNNReal (√Se) • s') u = √Se * s' u := by
        simp [NNReal.smul_def, Real.coe_toNNReal _ (Real.sqrt_nonneg Se)]
      rw [this]
      exact hΘle u
    have hc2 : Continuous (Real.toNNReal (√Se) • s') := by
      rw [FunLike.coe_smul]; exact hs'.const_smul _
    exact Seminorm.continuous_of_le hc2 hle
  have hgκ : ∀ n u, ‖g n u‖ ≤ √Se * ‖Θ u‖ := by
    intro n u
    calc ‖g n u‖ ≤ s u := hgs n u
      _ ≤ ∑' j, e j * ‖h j u‖ := hse u
      _ ≤ √(∑' j, e j) * √(∑' j, e j * ‖h j u‖ ^ 2) :=
          cs_tsum e _ he (fun _ => norm_nonneg _) hes (hsum u)
      _ = √Se * ‖Θ u‖ := by rw [← hΘ, Real.sqrt_sq (norm_nonneg _), hSedef]
  have hsm : ∀ u, Summable fun n => c n * ‖g n u‖ := fun u =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hc n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hgs n u) (hc n)) (hcs.mul_right _)
  have hK : 0 ≤ Sc * √Se := mul_nonneg hSc (Real.sqrt_nonneg _)
  refine ⟨Θ, Sc * √Se, hK, hcont, ?_, ?_⟩
  · intro u
    calc b u ≤ ∑' n, c n * ‖g n u‖ := hbc u
      _ ≤ ∑' n, c n * (√Se * ‖Θ u‖) :=
          (hsm u).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hgκ n u) (hc n))
            (hcs.mul_right _)
      _ = Sc * √Se * ‖Θ u‖ := by rw [tsum_mul_right, hScdef]; ring
  · intro w F hon
    obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ i ∈ F, b (w i) ^ 2 := ⟨_, rfl⟩
    have hA : 0 ≤ A := hAdef ▸ sum_nonneg (fun _ _ => sq_nonneg _)
    rw [← hAdef]
    apply sq_bound hA hK
    have hbes : ∀ n, ∑ i ∈ F, ‖g n (w i)‖ ^ 2 ≤ (√Se) ^ 2 := fun n =>
      bessel Θ (g n : E →ₗ[ℂ] ℂ) (√Se) (Real.sqrt_nonneg _) (hgκ n) w F hon
    have h1 : ∀ i ∈ F, b (w i) ^ 2 ≤ ∑' n, b (w i) * (c n * ‖g n (w i)‖) := by
      intro i _
      rw [tsum_mul_left, sq]
      exact mul_le_mul_of_nonneg_left (hbc _) (apply_nonneg _ _)
    calc A ≤ ∑ i ∈ F, ∑' n, b (w i) * (c n * ‖g n (w i)‖) := hAdef ▸ sum_le_sum h1
      _ = ∑' n, ∑ i ∈ F, b (w i) * (c n * ‖g n (w i)‖) :=
          (Summable.tsum_finsetSum fun i _ => (hsm (w i)).mul_left _).symm
      _ ≤ ∑' n, c n * (√A * √Se) := by
          refine Summable.tsum_le_tsum ?_ (summable_sum fun i _ => (hsm (w i)).mul_left _)
            (hcs.mul_right _)
          intro n
          calc ∑ i ∈ F, b (w i) * (c n * ‖g n (w i)‖)
              = c n * ∑ i ∈ F, b (w i) * ‖g n (w i)‖ := by
                rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
            _ ≤ c n * (√A * √Se) := by
                apply mul_le_mul_of_nonneg_left _ (hc n)
                calc ∑ i ∈ F, b (w i) * ‖g n (w i)‖
                    ≤ √(∑ i ∈ F, b (w i) ^ 2) * √(∑ i ∈ F, ‖g n (w i)‖ ^ 2) :=
                      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
                  _ ≤ √A * √Se := by
                      rw [← hAdef]
                      exact mul_le_mul_of_nonneg_left
                        ((Real.sqrt_le_sqrt (hbes n)).trans_eq (Real.sqrt_sq (Real.sqrt_nonneg _)))
                        (Real.sqrt_nonneg _)
      _ = Sc * √Se * √A := by rw [tsum_mul_right, hScdef]; ring

lemma level [TopologicalSpace E] [IsTopologicalAddGroup E] (hE : IsHLCS E) (hN : IsNuclear E)
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hbi : ∀ m n, f m (x n) = if m = n then 1 else 0)
    (heq : IsEquicontinuousBasis x f) (a : Seminorm ℂ E) (ha : Continuous a) :
    ∃ (r : Seminorm ℂ E) (C : ℝ), Continuous r ∧ (∀ m, r (x m) = 0 → a (x m) = 0) ∧
      ∀ F : Finset ℕ, ∑ m ∈ F, (a (x m) / r (x m)) ^ 2 ≤ C := by
  obtain ⟨b, hb, hfb⟩ := stepA hE x f heq a ha
  obtain ⟨Θ, K, hK, hΘc, hB1, hB2⟩ := stepB hN b hb
  have h0 : ∀ m, ‖Θ (x m)‖ = 0 → a (x m) = 0 := by
    intro m hm
    have h1 := hfb m (x m)
    rw [hbi, if_pos rfl, norm_one, one_mul] at h1
    have h2 := hB1 (x m)
    rw [hm, mul_zero] at h2
    exact le_antisymm (h1.trans h2) (apply_nonneg _ _)
  refine ⟨(normSeminorm ℂ H2).comp Θ, K ^ 2, hΘc, h0, ?_⟩
  intro F
  show ∑ m ∈ F, (a (x m) / ‖Θ (x m)‖) ^ 2 ≤ K ^ 2
  obtain ⟨y, hy⟩ : ∃ y : ℕ → E, ∀ m, y m = (((‖Θ (x m)‖)⁻¹ : ℝ) : ℂ) • x m := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → H2, G = gramSchmidt ℂ (fun m => Θ (y m)) := ⟨_, rfl⟩
  have hpull : ∀ m, ∃ z ∈ Submodule.span ℂ (y '' Set.Iio m), Θ z = Θ (y m) - G m := by
    intro m
    have hmem : Θ (y m) - G m ∈ Submodule.span ℂ ((fun m => Θ (y m)) '' Set.Iio m) := by
      rw [← span_gramSchmidt_Iio ℂ, ← hGdef]
      have := gramSchmidt_def'' ℂ (fun m => Θ (y m)) m
      rw [← hGdef] at this
      rw [sub_eq_of_eq_add' this]
      exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)
    rw [show (fun m => Θ (y m)) '' Set.Iio m = Θ '' (y '' Set.Iio m) by rw [Set.image_image],
      ← Submodule.map_span] at hmem
    exact hmem
  choose z hz hΘz using hpull
  have hfz : ∀ m, f m (z m) = 0 := by
    intro m
    have : Submodule.span ℂ (y '' Set.Iio m) ≤ LinearMap.ker (f m : E →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have hne : m ≠ i := ne_of_gt hi
      simp [hy, hbi, hne]
    exact this (hz m)
  have hGz : ∀ m, inner ℂ (G m) (Θ (z m)) = 0 := by
    intro m
    have : Submodule.span ℂ (y '' Set.Iio m) ≤ LinearMap.ker ((innerₛₗ ℂ (G m)).comp Θ) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      show inner ℂ (G m) (Θ (y i)) = 0
      rw [hGdef]
      exact gramSchmidt_inv_triangular ℂ (fun m => Θ (y m)) hi
    exact this (hz m)
  have hGle : ∀ m, ‖G m‖ ≤ ‖Θ (y m)‖ := by
    intro m
    have h1 : inner ℂ (G m) (Θ (y m)) = inner ℂ (G m) (G m) := by
      have : Θ (y m) = G m + Θ (z m) := by rw [hΘz]; abel
      rw [this, inner_add_right, hGz, add_zero]
    have h2 : ‖G m‖ * ‖G m‖ ≤ ‖G m‖ * ‖Θ (y m)‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) (G m) (Θ (y m))
      rw [h1, inner_self_eq_norm_sq_to_K] at this
      simpa [sq] using this
    by_cases hz0 : ‖G m‖ = 0
    · rw [hz0]; exact norm_nonneg _
    · exact le_of_mul_le_mul_left h2 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0))
  obtain ⟨W, hW⟩ : ∃ W : ℕ → E, ∀ m, W m = (((‖G m‖)⁻¹ : ℝ) : ℂ) • (y m - z m) :=
    ⟨_, fun _ => rfl⟩
  have hΘw : ∀ m, Θ (y m - z m) = G m := by intro m; rw [map_sub, hΘz]; abel
  have hgood : ∀ m, a (x m) ≠ 0 → 0 < ‖G m‖ ∧ a (x m) / ‖Θ (x m)‖ ≤ b (W m) := by
    intro m ham
    have hρ : 0 < ‖Θ (x m)‖ := lt_of_le_of_ne (norm_nonneg _) (fun h => ham (h0 m h.symm))
    have hapos : 0 < a (x m) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm ham)
    have hfy : f m (y m - z m) = (((‖Θ (x m)‖)⁻¹ : ℝ) : ℂ) := by
      rw [map_sub, hfz, sub_zero, hy, map_smul, hbi, if_pos rfl, smul_eq_mul, mul_one]
    have hd : a (x m) / ‖Θ (x m)‖ ≤ K * ‖G m‖ := by
      have h1 := hfb m (y m - z m)
      rw [hfy, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hρ.le)] at h1
      have h2 := hB1 (y m - z m)
      rw [hΘw] at h2
      rw [div_eq_inv_mul]
      exact h1.trans h2
    have hGpos : 0 < ‖G m‖ := by
      by_contra hc
      have : ‖G m‖ = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
      rw [this, mul_zero] at hd
      exact absurd hd (not_le.2 (div_pos hapos hρ))
    have hG1 : ‖G m‖ ≤ 1 := by
      refine (hGle m).trans ?_
      rw [hy, map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hρ.le)]
      exact (inv_mul_cancel₀ hρ.ne').le
    refine ⟨hGpos, ?_⟩
    have h3 := hfb m (W m)
    rw [hW, map_smul, hfy, smul_eq_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 hρ.le), Real.norm_of_nonneg (inv_nonneg.2 hGpos.le),
      ← hW] at h3
    refine le_trans ?_ h3
    have h4 : 1 ≤ ‖G m‖⁻¹ := (one_le_inv₀ hGpos).2 hG1
    have h5 : 0 ≤ ‖Θ (x m)‖⁻¹ * a (x m) := mul_nonneg (inv_nonneg.2 hρ.le) hapos.le
    calc a (x m) / ‖Θ (x m)‖ = 1 * (‖Θ (x m)‖⁻¹ * a (x m)) := by rw [div_eq_inv_mul, one_mul]
      _ ≤ ‖G m‖⁻¹ * (‖Θ (x m)‖⁻¹ * a (x m)) := mul_le_mul_of_nonneg_right h4 h5
      _ = _ := by ring
  have hon : ∀ i ∈ F.filter (fun m => a (x m) ≠ 0), ∀ j ∈ F.filter (fun m => a (x m) ≠ 0),
      inner ℂ (Θ (W i)) (Θ (W j)) = if i = j then (1 : ℂ) else 0 := by
    intro i hi j hj
    rw [hW, hW, map_smul, map_smul, hΘw, hΘw, inner_smul_left, inner_smul_right]
    split_ifs with hij
    · subst hij
      have hne : (‖G i‖ : ℂ) ≠ 0 := by
        exact_mod_cast (hgood i (Finset.mem_filter.1 hi).2).1.ne'
      rw [inner_self_eq_norm_sq_to_K]
      simp
      field_simp
    · rw [hGdef, gramSchmidt_orthogonal ℂ _ hij]; simp
  have hfin := hB2 W _ hon
  calc ∑ m ∈ F, (a (x m) / ‖Θ (x m)‖) ^ 2
      = ∑ m ∈ F.filter (fun m => a (x m) ≠ 0), (a (x m) / ‖Θ (x m)‖) ^ 2 :=
        (Finset.sum_filter_of_ne (p := fun m => a (x m) ≠ 0) fun m _ h h' => h (by rw [h']; simp)).symm
    _ ≤ ∑ m ∈ F.filter (fun m => a (x m) ≠ 0), b (W m) ^ 2 :=
        sum_le_sum fun m hm => pow_le_pow_left₀
          (div_nonneg (apply_nonneg _ _) (norm_nonneg _)) (hgood m (Finset.mem_filter.1 hm).2).2 2
    _ ≤ K ^ 2 := hfin

lemma amgm (P R0 R1 φ B : ℝ) (hR0 : R0 ≠ 0) (hR1 : R1 ≠ 0) (hP : 0 ≤ P) (h0 : 0 ≤ R0)
    (h1 : 0 ≤ R1) (hB : 0 ≤ B) (h : φ * R1 ≤ B) :
    φ * P ≤ ((P / R0) ^ 2 + (R0 / R1) ^ 2) / 2 * B := by
  have e : P = (P / R0) * (R0 / R1) * R1 := by field_simp
  have hd : 0 ≤ (P / R0) * (R0 / R1) := mul_nonneg (div_nonneg hP h0) (div_nonneg h0 h1)
  have h2 : (P / R0) * (R0 / R1) ≤ ((P / R0) ^ 2 + (R0 / R1) ^ 2) / 2 := by
    nlinarith [sq_nonneg (P / R0 - R0 / R1)]
  calc φ * P = (P / R0) * (R0 / R1) * (φ * R1) := by
        conv_lhs => rw [e]
        ring
    _ ≤ (P / R0) * (R0 / R1) * B := mul_le_mul_of_nonneg_left h hd
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 hB

end MasulloGRHBasisAbsAux

open MasulloGRHBasisAbsAux in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : MasulloGRH.IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hx : MasulloGRH.IsSchauderBasis x f)
    (hN : MasulloGRH.IsNuclear E) (heq : MasulloGRH.IsEquicontinuousBasis x f) :
    MasulloGRH.IsAbsoluteBasis x f := by
  obtain ⟨ι, _, P, hP⟩ := hE.1
  have := hP.topologicalAddGroup
  intro p hp
  obtain ⟨r0, C0, hr0, hz0, hs0⟩ := level hE hN x f hx.biorthogonal heq p hp
  obtain ⟨r1, C1, hr1, hz1, hs1⟩ := level hE hN x f hx.biorthogonal heq r0 hr0
  obtain ⟨b, hb, hfb⟩ := stepA hE x f heq r1 hr1
  have hC : 0 ≤ (C0 + C1) / 2 := by
    have h0 := hs0 ∅
    have h1 := hs1 ∅
    simp at h0 h1
    linarith
  refine ⟨Real.toNNReal ((C0 + C1) / 2) • b, by rw [FunLike.coe_smul]; exact hb.const_smul _,
    fun u => ?_⟩
  have hval : (Real.toNNReal ((C0 + C1) / 2) • b) u = (C0 + C1) / 2 * b u := by
    simp [NNReal.smul_def, Real.coe_toNNReal _ hC]
  rw [hval]
  have hb0 : 0 ≤ b u := apply_nonneg _ _
  have hterm : ∀ m, p (f m u • x m) ≤
      ((p (x m) / r0 (x m)) ^ 2 + (r0 (x m) / r1 (x m)) ^ 2) / 2 * b u := by
    intro m
    rw [map_smul_eq_mul]
    by_cases h1 : r1 (x m) = 0
    · rw [hz0 m (hz1 m h1), mul_zero]; positivity
    by_cases h0 : r0 (x m) = 0
    · rw [hz0 m h0, mul_zero]; positivity
    exact amgm _ _ _ _ _ h0 h1 (apply_nonneg _ _) (apply_nonneg _ _) (apply_nonneg _ _) hb0
      (hfb m u)
  have hfin : ∀ T : Finset ℕ, ∑ m ∈ T, p (f m u • x m) ≤ (C0 + C1) / 2 * b u := by
    intro T
    calc ∑ m ∈ T, p (f m u • x m)
        ≤ ∑ m ∈ T, ((p (x m) / r0 (x m)) ^ 2 + (r0 (x m) / r1 (x m)) ^ 2) / 2 * b u :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = (∑ m ∈ T, (p (x m) / r0 (x m)) ^ 2 + ∑ m ∈ T, (r0 (x m) / r1 (x m)) ^ 2) / 2 * b u := by
          rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ (C0 + C1) / 2 * b u := by
          apply mul_le_mul_of_nonneg_right _ hb0
          linarith [hs0 T, hs1 T]
  exact ⟨summable_of_sum_le (fun m => apply_nonneg _ _) hfin,
    Real.tsum_le_of_sum_le (fun m => apply_nonneg _ _) hfin⟩
