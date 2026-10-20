-- Prove2me | solution 1 for NAGFlow.Flow.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T03:04:59.102579+00:00
-- url     : https://prove2.me/submissions/e115f0f9-2ee8-40a2-93a2-5fa42a5eaaa6

-- Licensed under Apache 2.0. Complete global NAG flow existence, uniqueness and weighted Lyapunov decay.
import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting


namespace NAGFlowProof

open Set Filter NAGFlow.Flow

end NAGFlowProof


namespace NAGFlowProof

open Set Filter NAGFlow.Flow

theorem gamma_hasDerivAt (μ γ₀ t : ℝ) :
    HasDerivAt (gammaFn μ γ₀) (μ - gammaFn μ γ₀ t) t := by
  have h : HasDerivAt (fun s : ℝ => μ + (γ₀ - μ) * Real.exp (-s))
      ((γ₀ - μ) * (Real.exp (-t) * (-1))) t := by
    convert (((hasDerivAt_id t).neg.exp).const_mul (γ₀ - μ)).const_add μ using 1 <;> rfl
  convert h using 1 <;> try rfl
  unfold gammaFn
  ring

theorem gamma_continuous (μ γ₀ : ℝ) : Continuous (gammaFn μ γ₀) :=
  continuous_iff_continuousAt.mpr fun t => (gamma_hasDerivAt μ γ₀ t).continuousAt

theorem gamma_zero (μ γ₀ : ℝ) : gammaFn μ γ₀ 0 = γ₀ := by
  simp [gammaFn]

theorem gamma_decompose (μ γ₀ t : ℝ) :
    gammaFn μ γ₀ t = γ₀ * Real.exp (-t) + μ * (1 - Real.exp (-t)) := by
  unfold gammaFn
  ring

theorem gamma_lower {μ γ₀ T t : ℝ} (hμ : 0 ≤ μ) (hγ : 0 < γ₀)
    (ht : 0 ≤ t) (htT : t ≤ T) : γ₀ * Real.exp (-T) ≤ gammaFn μ γ₀ t := by
  rw [gamma_decompose]
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hem : Real.exp (-T) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  nlinarith [mul_nonneg hμ (sub_nonneg.mpr he), mul_le_mul_of_nonneg_left hem hγ.le]

theorem gamma_pos {μ γ₀ t : ℝ} (hμ : 0 ≤ μ) (hγ : 0 < γ₀)
    (ht : 0 ≤ t) : 0 < gammaFn μ γ₀ t :=
  lt_of_lt_of_le (mul_pos hγ (Real.exp_pos _)) (gamma_lower hμ hγ ht le_rfl)

end NAGFlowProof


namespace NAGFlowProof

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Matching classical pieces give a classical solution on the union of intervals. -/
theorem ode_glue {F : ℝ → E → E} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {x y : ℝ → E} (he : x b = y b)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (F t (x t)) (Icc a b) t)
    (hy : ∀ t ∈ Icc b c, HasDerivWithinAt y (F t (y t)) (Icc b c) t) :
    ∃ z : ℝ → E, EqOn z x (Icc a b) ∧ EqOn z y (Icc b c) ∧
      ∀ t ∈ Icc a c, HasDerivWithinAt z (F t (z t)) (Icc a c) t := by
  classical
  let z : ℝ → E := fun t => if t ≤ b then x t else y t
  have hzx : EqOn z x (Icc a b) := fun t ht => if_pos ht.2
  have hzy : EqOn z y (Icc b c) := by
    intro t ht
    by_cases h : t ≤ b
    · have : t = b := le_antisymm h ht.1
      subst t
      simpa only [z, if_pos le_rfl] using he
    · exact if_neg h
  refine ⟨z, hzx, hzy, ?_⟩
  intro t ht
  by_cases htb : t < b
  · have hmem : Icc a b ∈ 𝓝[Icc a c] t := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds htb).filter_mono nhdsWithin_le_nhds] with s hs hsb
      exact ⟨hs.1, hsb.le⟩
    have ht' : t ∈ Icc a b := ⟨ht.1, htb.le⟩
    rw [hzx ht']
    exact ((hx t ht').congr_of_mem hzx ht').mono_of_mem_nhdsWithin hmem
  · by_cases hbt : b < t
    · have hmem : Icc b c ∈ 𝓝[Icc a c] t := by
        filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hbt).filter_mono nhdsWithin_le_nhds] with s hs hbs
        exact ⟨hbs.le, hs.2⟩
      have ht' : t ∈ Icc b c := ⟨hbt.le, ht.2⟩
      rw [hzy ht']
      exact ((hy t ht').congr_of_mem hzy ht').mono_of_mem_nhdsWithin hmem
    · have h : t = b := le_antisymm (le_of_not_gt hbt) (le_of_not_gt htb)
      subst t
      have h1 := (hx b ⟨hab, le_rfl⟩).congr_of_mem hzx ⟨hab, le_rfl⟩
      have h2 := (hy b ⟨le_rfl, hbc⟩).congr_of_mem hzy ⟨le_rfl, hbc⟩
      rw [← hzx ⟨hab, le_rfl⟩] at h1
      rw [← hzy ⟨le_rfl, hbc⟩] at h2
      simpa only [Icc_union_Icc_eq_Icc hab hbc] using h1.union h2

end NAGFlowProof


namespace NAGFlowProof

open Set Filter Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem ode_short_step (F : ℝ → E → E) {a b : ℝ} (hab : a ≤ b)
    (K B : ℝ≥0) (hLip : ∀ t ∈ Icc a b, LipschitzWith K (F t))
    (hcont : ∀ z, ContinuousOn (fun t => F t z) (Icc a b))
    (hzero : ∀ t ∈ Icc a b, ‖F t 0‖ ≤ B)
    (hstep : (2 * (K : ℝ) + B) * (b - a) ≤ 1) (z : E) :
    ∃ x : ℝ → E, x a = z ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt x (F t (x t)) (Icc a b) t := by
  let R : ℝ≥0 := 1 + ‖z‖₊
  let C : ℝ≥0 := 2 * K + B
  have hR : (R : ℝ) = 1 + ‖z‖ := rfl
  have hR0 : 0 ≤ (R : ℝ) := R.coe_nonneg
  have hC : (C : ℝ) = 2 * (K : ℝ) + B := rfl
  have hnorm : ∀ t ∈ Icc a b, ∀ w ∈ closedBall z R, ‖F t w‖ ≤ (C * R : ℝ≥0) := by
    intro t ht w hw
    have hw' : ‖w - z‖ ≤ (R : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hwbound : ‖w‖ ≤ 2 * (R : ℝ) := by
      have := norm_le_norm_sub_add w z
      rw [hR] at *
      linarith
    have hl := (hLip t ht).norm_sub_le w 0
    simp only [sub_zero] at hl
    have hn := norm_le_norm_sub_add (F t w) (F t 0)
    have hk := mul_le_mul_of_nonneg_left hwbound K.coe_nonneg
    have hb := hzero t ht
    change ‖F t w‖ ≤ (C : ℝ) * R
    rw [hC]
    have hB := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ R by rw [hR]; linarith [norm_nonneg z]) B.coe_nonneg
    nlinarith
  have hp : IsPicardLindelof F (⟨a, le_rfl, hab⟩ : Icc a b) z R 0 (C * R) K := {
    lipschitzOnWith := fun t ht => (hLip t ht).lipschitzOnWith
    continuousOn := fun w _ => hcont w
    norm_le := hnorm
    mul_max_le := by
      simp only [sub_self, max_eq_left (sub_nonneg.mpr hab), NNReal.coe_mul,
        NNReal.coe_zero, sub_zero]
      have h := mul_le_mul_of_nonneg_right hstep hR0
      rw [← hC] at h
      nlinarith }
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end NAGFlowProof


namespace NAGFlowProof

open Set Filter
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem ode_finite_interval (F : ℝ → E → E) {T : ℝ} (hT : 0 < T)
    (K B : ℝ≥0) (hLip : ∀ t ∈ Icc 0 T, LipschitzWith K (F t))
    (hcont : ∀ z, ContinuousOn (fun t => F t z) (Icc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, ‖F t 0‖ ≤ B) (z : E) :
    ∃ x : ℝ → E, x 0 = z ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt x (F t (x t)) (Icc 0 T) t := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * (K : ℝ) + B + 1) * T)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  let h : ℝ := T / N
  have hh : 0 < h := div_pos hT hNpos
  have hNh : (N : ℝ) * h = T := by dsimp [h]; field_simp
  have hstep : (2 * (K : ℝ) + B) * h ≤ 1 := by
    dsimp [h]
    rw [← mul_div_assoc, div_le_iff₀ hNpos]
    nlinarith
  have hi : ∀ i : ℕ, i ≤ N → ∃ x : ℝ → E, x 0 = z ∧
      ∀ t ∈ Icc 0 ((i : ℝ) * h),
        HasDerivWithinAt x (F t (x t)) (Icc 0 ((i : ℝ) * h)) t := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨fun _ => z, rfl, ?_⟩
      intro t ht
      simp only [Nat.cast_zero, zero_mul, Icc_self, mem_singleton_iff] at ht
      subst t
      simpa only [Nat.cast_zero, zero_mul, Icc_self] using
        (show HasDerivWithinAt (fun _ : ℝ => z) (F 0 z) ({0} : Set ℝ) 0 from
          HasFDerivWithinAt.singleton)
    | succ i ih =>
      intro hiN
      obtain ⟨x, hx0, hx⟩ := ih (Nat.le_trans (Nat.le_succ i) hiN)
      have hia : 0 ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
      have hiab : (i : ℝ) * h ≤ ((i + 1 : ℕ) : ℝ) * h := by
        push_cast
        nlinarith
      have hic : ((i + 1 : ℕ) : ℝ) * h ≤ T := by
        rw [← hNh]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hiN) hh.le
      have hsub : Icc ((i : ℝ) * h) (((i + 1 : ℕ) : ℝ) * h) ⊆ Icc 0 T :=
        fun t ht => ⟨hia.trans ht.1, ht.2.trans hic⟩
      obtain ⟨y, hy0, hy⟩ := ode_short_step F hiab K B
        (fun t ht => hLip t (hsub ht)) (fun w => (hcont w).mono hsub)
        (fun t ht => hzero t (hsub ht)) (by
          convert hstep using 1
          push_cast
          ring) (x ((i : ℝ) * h))
      obtain ⟨w, hwx, _, hw⟩ := ode_glue hia hiab hy0.symm hx hy
      exact ⟨w, (hwx ⟨le_rfl, hia⟩).trans hx0, hw⟩
  simpa only [hNh] using hi N le_rfl

end NAGFlowProof


namespace NAGFlowProof

open Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ode_interval_unique (F : ℝ → E → E) {T : ℝ} (K : ℝ≥0)
    (hLip : ∀ t ∈ Icc 0 T, LipschitzWith K (F t))
    {x y : ℝ → E}
    (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (F t (x t)) (Icc 0 T) t)
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (F t (y t)) (Icc 0 T) t)
    (he : x 0 = y 0) : EqOn x y (Icc 0 T) := by
  have hr {w : ℝ → E}
      (hw : ∀ t ∈ Icc 0 T, HasDerivWithinAt w (F t (w t)) (Icc 0 T) t) :
      ∀ t ∈ Ico 0 T, HasDerivWithinAt w (F t (w t)) (Ici t) t := by
    intro t ht
    apply (hw t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds] with s hs hsT
    exact ⟨ht.1.trans hs, hsT.le⟩
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun t ht => (hLip t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hx) (hr hx) (fun _ _ => mem_univ _)
    (HasDerivWithinAt.continuousOn hy) (hr hy) (fun _ _ => mem_univ _) he

end NAGFlowProof


namespace NAGFlowProof

open Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem ode_halfline_exists (F : ℝ → E → E)
    (hstrip : ∀ T : ℝ, 0 < T → ∃ K B : ℝ≥0,
      (∀ t ∈ Icc 0 T, LipschitzWith K (F t)) ∧
      (∀ z, ContinuousOn (fun t => F t z) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, ‖F t 0‖ ≤ B)) (z₀ : E) :
    ∃ z : ℝ → E, z 0 = z₀ ∧
      ∀ t ∈ Ici 0, HasDerivWithinAt z (F t (z t)) (Ici 0) t := by
  classical
  have hex (n : ℕ) : ∃ x : ℝ → E, x 0 = z₀ ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1),
        HasDerivWithinAt x (F t (x t)) (Icc 0 ((n : ℝ) + 1)) t := by
    obtain ⟨K, B, hK, hc, hb⟩ := hstrip (n + 1) (by positivity)
    exact ode_finite_interval F (by positivity) K B hK hc hb z₀
  choose x hx0 hx using hex
  have hcompat (i j : ℕ) {t : ℝ} (ht : 0 ≤ t)
      (hi : t ≤ (i : ℝ) + 1) (hj : t ≤ (j : ℝ) + 1) : x i t = x j t := by
    let T : ℝ := min ((i : ℝ) + 1) ((j : ℝ) + 1)
    have hT : 0 < T := lt_min (by positivity) (by positivity)
    obtain ⟨K, _, hK, _, _⟩ := hstrip T hT
    have hsi : Icc 0 T ⊆ Icc 0 ((i : ℝ) + 1) :=
      fun s hs => ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
    have hsj : Icc 0 T ⊆ Icc 0 ((j : ℝ) + 1) :=
      fun s hs => ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
    exact ode_interval_unique F K hK
      (fun s hs => (hx i s (hsi hs)).mono hsi)
      (fun s hs => (hx j s (hsj hs)).mono hsj)
      ((hx0 i).trans (hx0 j).symm) ⟨ht, le_min hi hj⟩
  let idx : ℝ → ℕ := fun t => ⌈t⌉₊
  have hidx (t : ℝ) : t < (idx t : ℝ) + 1 := by
    have h := Nat.le_ceil t
    dsimp [idx]
    linarith
  let z : ℝ → E := fun t => x (idx t) t
  have hEq (n : ℕ) : EqOn z (x n) (Icc 0 ((n : ℝ) + 1)) := by
    intro t ht
    exact hcompat (idx t) n ht.1 (hidx t).le ht.2
  refine ⟨z, hx0 (idx 0), ?_⟩
  intro t ht
  let n := idx t
  have htN : t < (n : ℝ) + 1 := hidx t
  have ht' : t ∈ Icc 0 ((n : ℝ) + 1) := ⟨ht, htN.le⟩
  have hmem : Icc 0 ((n : ℝ) + 1) ∈ 𝓝[Ici 0] t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds htN).filter_mono nhdsWithin_le_nhds] with s hs hsN
    exact ⟨hs, hsN.le⟩
  rw [hEq n ht']
  exact ((hx n t ht').congr_of_mem (hEq n) ht').mono_of_mem_nhdsWithin hmem

omit [CompleteSpace E] in
theorem ode_halfline_unique (F : ℝ → E → E)
    (hstrip : ∀ T : ℝ, 0 < T → ∃ K : ℝ≥0,
      ∀ t ∈ Icc 0 T, LipschitzWith K (F t))
    {x y : ℝ → E}
    (hx : ∀ t ∈ Ici 0, HasDerivWithinAt x (F t (x t)) (Ici 0) t)
    (hy : ∀ t ∈ Ici 0, HasDerivWithinAt y (F t (y t)) (Ici 0) t)
    (he : x 0 = y 0) : EqOn x y (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  obtain ⟨K, hK⟩ := hstrip (t + 1) (by linarith)
  have hs : Icc 0 (t + 1) ⊆ Ici 0 := fun _ h => h.1
  exact ode_interval_unique F K hK
    (fun s hs' => (hx s hs'.1).mono hs)
    (fun s hs' => (hy s hs'.1).mono hs) he ⟨ht, by linarith⟩

end NAGFlowProof


namespace NAGFlowProof

open Set Filter NAGFlow.Flow
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def nagField (g : V → V) (μ γ₀ : ℝ) (t : ℝ) (z : V × V) : V × V :=
  (z.2 - z.1, (gammaFn μ γ₀ t)⁻¹ • (μ • (z.1 - z.2) - g z.1))

theorem nagField_continuousOn {g : V → V} {μ γ₀ : ℝ}
    (hg : Continuous g) (hμ : 0 ≤ μ) (hγ : 0 < γ₀) :
    ContinuousOn (fun p : ℝ × (V × V) => nagField g μ γ₀ p.1 p.2)
      (Ici 0 ×ˢ univ) := by
  unfold nagField
  apply ContinuousOn.prodMk
  · fun_prop
  · apply ContinuousOn.smul
    · exact ((gamma_continuous μ γ₀).comp continuous_fst).continuousOn.inv₀
        (fun p hp => ne_of_gt (gamma_pos hμ hγ hp.1))
    · fun_prop

theorem field_difference_bound (g : V → V) {μ L γ : ℝ}
    (hμ : 0 ≤ μ) (hL : 0 ≤ L) (hγ : 0 < γ)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (z w : V × V) :
    ‖γ⁻¹ • (μ • (z.1 - z.2) - g z.1) -
      γ⁻¹ • (μ • (w.1 - w.2) - g w.1)‖ ≤
      γ⁻¹ * (2 * μ + L) * ‖z - w‖ := by
  have hfst : ‖z.1 - w.1‖ ≤ ‖z - w‖ := norm_fst_le (z - w)
  have hsnd : ‖z.2 - w.2‖ ≤ ‖z - w‖ := norm_snd_le (z - w)
  have hd : ‖(z.1 - z.2) - (w.1 - w.2)‖ ≤ 2 * ‖z - w‖ := by
    calc
      _ = ‖(z.1 - w.1) - (z.2 - w.2)‖ := by congr 1; abel
      _ ≤ ‖z.1 - w.1‖ + ‖z.2 - w.2‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have he : (μ • (z.1 - z.2) - g z.1) - (μ • (w.1 - w.2) - g w.1) =
      μ • ((z.1 - z.2) - (w.1 - w.2)) - (g z.1 - g w.1) := by
    simp only [smul_sub]
    abel
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ), he]
  have hn := norm_sub_le (μ • ((z.1 - z.2) - (w.1 - w.2))) (g z.1 - g w.1)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at hn
  have hi : ‖μ • ((z.1 - z.2) - (w.1 - w.2)) - (g z.1 - g w.1)‖ ≤
      (2 * μ + L) * ‖z - w‖ := by
    have hd' := mul_le_mul_of_nonneg_left hd hμ
    have hg' := (hg z.1 w.1).trans (mul_le_mul_of_nonneg_left hfst hL)
    nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (inv_pos.mpr hγ).le

end NAGFlowProof


namespace NAGFlowProof

open Set Filter NAGFlow.Flow
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem nagField_lipschitz {g : V → V} {μ L γ₀ t : ℝ}
    (hμ : 0 ≤ μ) (hL : 0 ≤ L) (hγ : 0 < gammaFn μ γ₀ t)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (K : ℝ≥0) (hK1 : 2 ≤ (K : ℝ))
    (hK2 : (gammaFn μ γ₀ t)⁻¹ * (2 * μ + L) ≤ K) :
    LipschitzWith K (nagField g μ γ₀ t) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro z w
  change max ‖(z.2 - z.1) - (w.2 - w.1)‖
      ‖(gammaFn μ γ₀ t)⁻¹ • (μ • (z.1 - z.2) - g z.1) -
        (gammaFn μ γ₀ t)⁻¹ • (μ • (w.1 - w.2) - g w.1)‖ ≤ _
  apply max_le
  · have hd : ‖(z.2 - z.1) - (w.2 - w.1)‖ ≤ 2 * ‖z - w‖ := by
      calc
        _ = ‖(z.2 - w.2) - (z.1 - w.1)‖ := by congr 1; abel
        _ ≤ ‖z.2 - w.2‖ + ‖z.1 - w.1‖ := norm_sub_le _ _
        _ ≤ _ := by
          have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := norm_fst_le (z - w)
          have h2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := norm_snd_le (z - w)
          linarith
    exact hd.trans (mul_le_mul_of_nonneg_right hK1 (norm_nonneg _))
  · exact (field_difference_bound g hμ hL hγ hg z w).trans
      (mul_le_mul_of_nonneg_right hK2 (norm_nonneg _))

theorem nagField_zero {g : V → V} {μ γ₀ t : ℝ} (hγ : 0 < gammaFn μ γ₀ t) :
    ‖nagField g μ γ₀ t 0‖ = (gammaFn μ γ₀ t)⁻¹ * ‖g 0‖ := by
  simp only [nagField, Prod.fst_zero, Prod.snd_zero, sub_self, smul_zero, zero_sub,
    Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ),
    norm_neg]
  exact max_eq_right (mul_nonneg (inv_pos.mpr hγ).le (norm_nonneg _))

theorem nagField_strip [CompleteSpace V] {f : V → ℝ} {g : V → V} {μ L γ₀ : ℝ}
    (hf : NAGFlow.PredCorr.IsS11 f g μ L) (hγ : 0 < γ₀) (T : ℝ) (_hT : 0 < T) :
    ∃ K B : ℝ≥0,
      (∀ t ∈ Icc 0 T, LipschitzWith K (nagField g μ γ₀ t)) ∧
      (∀ z, ContinuousOn (fun t => nagField g μ γ₀ t z) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, ‖nagField g μ γ₀ t 0‖ ≤ B) := by
  let A : ℝ := (γ₀ * Real.exp (-T))⁻¹
  have hA : 0 < A := inv_pos.mpr (mul_pos hγ (Real.exp_pos _))
  let K : ℝ≥0 := ⟨max 2 (A * (2 * μ + L)), le_trans (by norm_num) (le_max_left _ _)⟩
  let B : ℝ≥0 := ⟨A * ‖g 0‖, mul_nonneg hA.le (norm_nonneg _)⟩
  have hinv {t : ℝ} (ht : t ∈ Icc 0 T) : (gammaFn μ γ₀ t)⁻¹ ≤ A :=
    inv_anti₀ (mul_pos hγ (Real.exp_pos _)) (gamma_lower hf.mu_nonneg hγ ht.1 ht.2)
  refine ⟨K, B, ?_, ?_, ?_⟩
  · intro t ht
    apply nagField_lipschitz hf.mu_nonneg hf.L_pos.le (gamma_pos hf.mu_nonneg hγ ht.1)
      hf.grad_lip K (le_max_left _ _)
    exact (mul_le_mul_of_nonneg_right (hinv ht) (by linarith [hf.mu_nonneg, hf.L_pos])).trans (le_max_right _ _)
  · intro z
    exact (nagField_continuousOn hf.grad_cont hf.mu_nonneg hγ).comp
      (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht.1, mem_univ _⟩)
  · intro t ht
    rw [nagField_zero (gamma_pos hf.mu_nonneg hγ ht.1)]
    exact mul_le_mul_of_nonneg_right (hinv ht) (norm_nonneg _)

end NAGFlowProof


namespace NAGFlowProof

open Set Filter NAGFlow.Flow
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem system_exists {f : V → ℝ} {g : V → V} {μ L γ₀ : ℝ}
    (hf : NAGFlow.PredCorr.IsS11 f g μ L) (hγ : 0 < γ₀) (x₀ v₀ : V) :
    ∃ x v : ℝ → V, IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v := by
  obtain ⟨z, hz0, hz⟩ := ode_halfline_exists (nagField g μ γ₀)
    (nagField_strip hf hγ) (x₀, v₀)
  have hc := HasDerivWithinAt.continuousOn hz
  have hfc : ContinuousOn (fun t => nagField g μ γ₀ t (z t)) (Ici 0) :=
    (nagField_continuousOn hf.grad_cont hf.mu_nonneg hγ).comp
      (continuousOn_id.prodMk hc) (fun _ ht => ⟨ht, mem_univ _⟩)
  have hC : ContDiffOn ℝ 1 z (Ici 0) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
    refine ⟨fun t ht => (hz t ht).differentiableWithinAt, ?_⟩
    exact hfc.congr fun t ht => (hz t ht).derivWithin (uniqueDiffOn_Ici 0 t ht)
  have hx {t : ℝ} (ht : 0 ≤ t) : HasDerivWithinAt (fun s => (z s).1)
      ((z t).2 - (z t).1) (Ici 0) t := by
    exact (ContinuousLinearMap.fst ℝ V V).hasFDerivAt.comp_hasDerivWithinAt t (hz t ht)
  have hv {t : ℝ} (ht : 0 ≤ t) : HasDerivWithinAt (fun s => (z s).2)
      ((gammaFn μ γ₀ t)⁻¹ • (μ • ((z t).1 - (z t).2) - g (z t).1)) (Ici 0) t := by
    exact (ContinuousLinearMap.snd ℝ V V).hasFDerivAt.comp_hasDerivWithinAt t (hz t ht)
  refine ⟨fun t => (z t).1, fun t => (z t).2, hC.fst, hC.snd, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hx ht).derivWithin (uniqueDiffOn_Ici 0 t ht)
  · intro t ht
    rw [show dI (fun s => (z s).2) t = _ from (hv ht).derivWithin (uniqueDiffOn_Ici 0 t ht)]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (gamma_pos hf.mu_nonneg hγ ht)), one_smul]
  · exact congrArg Prod.fst hz0
  · exact congrArg Prod.snd hz0

end NAGFlowProof


namespace NAGFlowProof

open Set NAGFlow.Flow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {f : V → ℝ} {g : V → V} {μ γ₀ : ℝ} {γ : ℝ → ℝ} {x₀ v₀ : V} {x v : ℝ → V}

theorem system_deriv_x (h : IsSys56 f g μ γ x₀ v₀ x v) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt x (dI x t) (Ici 0) t :=
  (h.contDiff_x.differentiableOn (by norm_num) t ht).hasDerivWithinAt

theorem system_deriv_v (h : IsSys56 f g μ γ x₀ v₀ x v) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt v (dI v t) (Ici 0) t :=
  (h.contDiff_v.differentiableOn (by norm_num) t ht).hasDerivWithinAt

theorem system_derivative_contDiff (h : IsSys56 f g μ γ x₀ v₀ x v) :
    ContDiffOn ℝ 1 (dI x) (Ici 0) :=
  (h.contDiff_v.sub h.contDiff_x).congr (fun t ht => h.eq_x t ht)

theorem system_second_derivative (h : IsSys56 f g μ γ x₀ v₀ x v)
    {t : ℝ} (ht : 0 ≤ t) :
    dI (dI x) t = dI v t - dI x t := by
  have hd := ((system_deriv_v h ht).sub (system_deriv_x h ht)).congr_of_mem
    (fun s hs => h.eq_x s hs) ht
  exact hd.derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem system_to_second (h : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v) :
    IsNAGSolution2 f g μ γ₀ x₀ v₀ x := by
  refine ⟨?_, ?_, h.init_x, ?_⟩
  · apply (contDiffOn_succ_iff_derivWithin (n := 1) (uniqueDiffOn_Ici 0)).2
    exact ⟨h.contDiff_x.differentiableOn (by norm_num), by norm_num,
      system_derivative_contDiff h⟩
  · intro t ht
    rw [system_second_derivative h ht, smul_sub, add_smul]
    have hv := h.eq_v t ht
    have hx := h.eq_x t ht
    rw [hx] at *
    rw [show x t - v t = -(v t - x t) by abel, smul_neg] at hv
    rw [hv]
    abel
  · rw [h.eq_x 0 le_rfl, h.init_x, h.init_v]

theorem second_to_system (h : IsNAGSolution2 f g μ γ₀ x₀ v₀ x) :
    IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x (fun t => x t + dI x t) := by
  have hx : ContDiffOn ℝ 1 x (Ici 0) := h.contDiff.of_le (by norm_num)
  have hd : ContDiffOn ℝ 1 (dI x) (Ici 0) :=
    h.contDiff.derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
  refine ⟨hx, hx.add hd, ?_, ?_, h.init_x, ?_⟩
  · intro t ht
    abel
  · intro t ht
    have he := ((hx.differentiableOn (by norm_num) t ht).hasDerivWithinAt.add
      (hd.differentiableOn (by norm_num) t ht).hasDerivWithinAt).derivWithin
        (uniqueDiffOn_Ici 0 t ht)
    change dI (fun s => x s + dI x s) t = dI x t + dI (dI x) t at he
    rw [he, smul_add]
    have ho := h.ode t ht
    rw [add_smul] at ho
    rw [show x t - (x t + dI x t) = -(dI x t) by abel, smul_neg]
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero]
    convert ho using 1
    abel
  · rw [h.init_x, h.init_dx]
    abel

end NAGFlowProof


namespace NAGFlowProof

open Set NAGFlow.Flow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem system_pair_derivative {f : V → ℝ} {g : V → V} {μ γ₀ : ℝ}
    {x₀ v₀ : V} {x v : ℝ → V} (hμ : 0 ≤ μ) (hγ : 0 < γ₀)
    (h : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => (x s, v s))
      (nagField g μ γ₀ t (x t, v t)) (Ici 0) t := by
  have hv : dI v t = (gammaFn μ γ₀ t)⁻¹ • (μ • (x t - v t) - g (x t)) := by
    rw [← h.eq_v t ht, inv_smul_smul₀ (ne_of_gt (gamma_pos hμ hγ ht))]
  simpa only [nagField, h.eq_x t ht, hv] using
    (system_deriv_x h ht).prodMk (system_deriv_v h ht)

theorem system_unique {f : V → ℝ} {g : V → V} {μ L γ₀ : ℝ}
    (hf : NAGFlow.PredCorr.IsS11 f g μ L) (hγ : 0 < γ₀)
    {x₀ v₀ : V} {x v y w : ℝ → V}
    (hx : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v)
    (hy : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ y w) : EqOn y x (Ici 0) := by
  have hp := ode_halfline_unique (nagField g μ γ₀)
    (fun T hT => by
      obtain ⟨K, B, hK, _, _⟩ := nagField_strip hf hγ T hT
      exact ⟨K, hK⟩)
    (fun t ht => system_pair_derivative hf.mu_nonneg hγ hy ht)
    (fun t ht => system_pair_derivative hf.mu_nonneg hγ hx ht)
    (show (y 0, w 0) = (x 0, v 0) by rw [hy.init_x, hy.init_v, hx.init_x, hx.init_v])
  exact fun t ht => congrArg Prod.fst (hp ht)

end NAGFlowProof


namespace NAGFlowProof

open NAGFlow.Flow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem energy_polarization (μ γ : ℝ) (x v z g : V) :
    inner ℝ g (v - x) + (μ - γ) / 2 * ‖v - z‖ ^ 2 +
      inner ℝ (μ • (x - v) - g) (v - z) =
    μ / 2 * ‖x - z‖ ^ 2 - inner ℝ g (x - z) - γ / 2 * ‖v - z‖ ^ 2 -
      μ / 2 * ‖v - x‖ ^ 2 := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, norm_sub_sq_real, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v x]
  ring

theorem energy_differential_bound {f : V → ℝ} {g : V → V} {μ : ℝ}
    (hf : NAGFlow.PredCorr.IsS1 f g μ) (γ : ℝ) (x v z : V) :
    inner ℝ (g x) (v - x) + (μ - γ) / 2 * ‖v - z‖ ^ 2 +
      inner ℝ (μ • (x - v) - g x) (v - z) ≤
    -(f x - f z + γ / 2 * ‖v - z‖ ^ 2) - μ / 2 * ‖v - x‖ ^ 2 := by
  rw [energy_polarization]
  have hc := hf.mu_convex z x
  rw [norm_sub_rev z x, show z - x = -(x - z) by abel, inner_neg_right] at hc
  linarith

end NAGFlowProof


namespace NAGFlowProof

open Set NAGFlow.Flow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

noncomputable def energySlope (g : V → V) (μ : ℝ) (γ : ℝ → ℝ)
    (x v : ℝ → V) (z : V) (t : ℝ) : ℝ :=
  inner ℝ (g (x t)) (v t - x t) + (μ - γ t) / 2 * ‖v t - z‖ ^ 2 +
    inner ℝ (μ • (x t - v t) - g (x t)) (v t - z)

variable {f : V → ℝ} {g : V → V} {μ γ₀ : ℝ} {x₀ v₀ : V} {x v : ℝ → V}

theorem system_lyapunov_derivative (hf : NAGFlow.PredCorr.IsS1 f g μ)
    (h : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v) (z : V)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (lyapFlow f z (gammaFn μ γ₀) x v)
      (energySlope g μ (gammaFn μ γ₀) x v z t) (Ici 0) t := by
  have hx := system_deriv_x h ht
  have hv := system_deriv_v h ht
  have hf' : HasDerivWithinAt (fun s => f (x s)) (inner ℝ (g (x t)) (dI x t))
      (Ici 0) t := by
    exact (hf.hasGrad (x t)).hasFDerivAt.comp_hasDerivWithinAt t hx
  have hn := (hv.sub_const z).norm_sq
  have hg : HasDerivWithinAt (gammaFn μ γ₀) (μ - gammaFn μ γ₀ t) (Ici 0) t :=
    (gamma_hasDerivAt μ γ₀ t).hasDerivWithinAt
  have he := (hf'.sub_const (f z)).add ((hg.div_const 2).mul hn)
  have hi : gammaFn μ γ₀ t * inner ℝ (v t - z) (dI v t) =
      inner ℝ (μ • (x t - v t) - g (x t)) (v t - z) := by
    rw [← real_inner_smul_right, h.eq_v t ht, real_inner_comm]
  convert he using 1 <;> try rfl
  dsimp [energySlope]
  rw [h.eq_x t ht]
  nlinarith [hi]

theorem system_lyapunov_bound (hf : NAGFlow.PredCorr.IsS1 f g μ)
    (h : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v) (z : V)
    {t : ℝ} (ht : 0 ≤ t) :
    energySlope g μ (gammaFn μ γ₀) x v z t ≤
      -lyapFlow f z (gammaFn μ γ₀) x v t - μ / 2 * ‖dI x t‖ ^ 2 := by
  rw [h.eq_x t ht]
  exact energy_differential_bound hf (gammaFn μ γ₀ t) (x t) (v t) z

theorem system_energy_continuous (hf : NAGFlow.PredCorr.IsS1 f g μ)
    (h : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v) (z : V) :
    ContinuousOn (lyapFlow f z (gammaFn μ γ₀) x v) (Ici 0) :=
  fun _ ht => (system_lyapunov_derivative hf h z ht).continuousWithinAt

theorem system_slope_continuous (hf : NAGFlow.PredCorr.IsS1 f g μ)
    (h : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v) (z : V) :
    ContinuousOn (energySlope g μ (gammaFn μ γ₀) x v z) (Ici 0) := by
  have hx := h.contDiff_x.continuousOn
  have hv := h.contDiff_v.continuousOn
  have hg := hf.grad_cont.comp_continuousOn hx
  exact ((hg.inner (hv.sub hx)).add
    (((continuousOn_const.sub (gamma_continuous μ γ₀).continuousOn).div_const 2).mul
      ((hv.sub continuousOn_const).norm.pow 2))).add
        (((continuousOn_const.smul (hx.sub hv)).sub hg).inner (hv.sub continuousOn_const))

end NAGFlowProof


namespace NAGFlowProof

open Set MeasureTheory

 theorem weighted_decay {E D q : ℝ → ℝ} {a : ℝ}
    (hE : ContinuousOn E (Ici 0)) (hD : ContinuousOn D (Ici 0))
    (hq : ContinuousOn q (Ici 0))
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt E (D t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → D t ≤ -E t - a * q t)
    {t : ℝ} (ht : 0 ≤ t) :
    E t + a * ∫ s in (0 : ℝ)..t, Real.exp (s - t) * q s ≤ Real.exp (-t) * E 0 := by
  have hc : ContinuousOn (fun s => Real.exp s * E s) (Icc 0 t) :=
    (Real.continuous_exp.continuousOn.mul hE).mono Icc_subset_Ici_self
  have hdc : ContinuousOn (fun s => Real.exp s * (E s + D s)) (Icc 0 t) :=
    (Real.continuous_exp.continuousOn.mul (hE.add hD)).mono Icc_subset_Ici_self
  have hqc : ContinuousOn (fun s => -a * (Real.exp s * q s)) (Icc 0 t) :=
    (continuousOn_const.mul (Real.continuous_exp.continuousOn.mul hq)).mono
      Icc_subset_Ici_self
  have hi : IntervalIntegrable (fun s => Real.exp s * (E s + D s)) volume 0 t :=
    hdc.intervalIntegrable_of_Icc ht
  have hqi : IntervalIntegrable (fun s => -a * (Real.exp s * q s)) volume 0 t :=
    hqc.intervalIntegrable_of_Icc ht
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc
    (fun s hs => by
      have hd' := (Real.hasDerivAt_exp s).hasDerivWithinAt.mul (hd s hs.1.le)
      have hv : HasDerivWithinAt (fun u => Real.exp u * E u)
          (Real.exp s * (E s + D s)) (Ici 0) s := by
        convert hd' using 1 <;> try rfl
        ring
      exact hv.mono (fun u hu => le_trans hs.1.le hu.le)) hi
  have hm := intervalIntegral.integral_mono_on ht hi hqi (fun s hs => by
    have hh := mul_le_mul_of_nonneg_left (hb s hs.1) (Real.exp_pos s).le
    nlinarith)
  rw [he, intervalIntegral.integral_const_mul] at hm
  simp only [Real.exp_zero, one_mul] at hm
  have hm' := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-t)).le
  have hex : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have hint : (∫ s in (0 : ℝ)..t, Real.exp (s - t) * q s) =
      Real.exp (-t) * ∫ s in (0 : ℝ)..t, Real.exp s * q s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    change Real.exp (s - t) * q s = Real.exp (-t) * (Real.exp s * q s)
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [mul_sub, ← mul_assoc, hex, one_mul] at hm'
  rw [hint]
  nlinarith

end NAGFlowProof


namespace NAGFlowProof

open Set MeasureTheory NAGFlow.Flow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {f : V → ℝ} {g : V → V} {μ γ₀ : ℝ} {x₀ v₀ : V} {x v : ℝ → V}

theorem system_weighted_decay (hf : NAGFlow.PredCorr.IsS1 f g μ)
    (h : IsSys56 f g μ (gammaFn μ γ₀) x₀ v₀ x v) (z : V)
    {t : ℝ} (ht : 0 ≤ t) :
    lyapFlow f z (gammaFn μ γ₀) x v t +
      μ / 2 * ∫ s in (0 : ℝ)..t, Real.exp (s - t) * ‖dI x s‖ ^ 2 ≤
    Real.exp (-t) * lyapFlow f z (gammaFn μ γ₀) x v 0 := by
  apply weighted_decay (system_energy_continuous hf h z) (system_slope_continuous hf h z)
    ((system_derivative_contDiff h).continuousOn.norm.pow 2)
    (fun s hs => system_lyapunov_derivative hf h z hs)
    (fun s hs => system_lyapunov_bound hf h z hs) ht

end NAGFlowProof


namespace NAGFlowProof

open Set NAGFlow.Flow

/-- Lemma 3.2, p. 13. Let `f ∈ S^{1,1}_{μ,L}` with `μ ≥ 0`, `γ₀ > 0`, `γ(t) = μ + (γ₀ − μ)e^{−t}`
(the solution of (54)), `x₀, v₀ ∈ V`, and `x*` a global minimizer of `f`. Then the NAG flow (57)
`γx″ + (μ + γ)x′ + ∇f(x) = 0`, `x(0) = x₀`, `x′(0) = v₀ − x₀`, admits a solution
`x ∈ C²([0, ∞); V)`, unique on `[0, ∞)`; and, with `v = x + x′` and the Lyapunov function (58)
`ℒ(t) = f(x(t)) − f(x*) + γ(t)/2 ‖v(t) − x*‖²`, `ℒ` is differentiable on `[0, ∞)` (right derivative
at `0`) with
`ℒ′(t) ≤ −ℒ(t) − μ/2 ‖x′(t)‖²` (59), and
`ℒ(t) + μ/2 ∫₀ᵗ e^{s−t} ‖x′(s)‖² ds ≤ e^{−t} ℒ(0)` for all `t ≥ 0` (60). -/
theorem full_native_flow {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L) (hγ₀ : 0 < γ₀)
    (x₀ v₀ xstar : V) (_hxstar : ∀ y, f xstar ≤ f y) :
    ∃ x : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ x ∧
      (∀ y : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ y → EqOn y x (Ici 0)) ∧
      (∀ t : ℝ, 0 ≤ t → ∃ dL : ℝ,
        HasDerivWithinAt (lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s)) dL
          (Ici 0) t ∧
        dL ≤ -lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) t
          - μ / 2 * ‖dI x t‖ ^ 2) ∧
      (∀ t : ℝ, 0 ≤ t →
        lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) t
          + μ / 2 * ∫ s in (0 : ℝ)..t, Real.exp (s - t) * ‖dI x s‖ ^ 2
        ≤ Real.exp (-t) * lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) 0)  := by
  obtain ⟨x, v, hs⟩ := system_exists hf hγ₀ x₀ v₀
  have hx := system_to_second hs
  have hc := second_to_system hx
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · intro y hy
    exact system_unique hf hγ₀ hs (second_to_system hy)
  · intro t ht
    exact ⟨_, system_lyapunov_derivative hf.toIsS1 hc xstar ht,
      system_lyapunov_bound hf.toIsS1 hc xstar ht⟩
  · intro t ht
    exact system_weighted_decay hf.toIsS1 hc xstar ht

end NAGFlowProof


open NAGFlow.Flow

namespace NAGFlow.Flow

open Set

/-- Lemma 3.2, p. 13. Let `f ∈ S^{1,1}_{μ,L}` with `μ ≥ 0`, `γ₀ > 0`, `γ(t) = μ + (γ₀ − μ)e^{−t}`
(the solution of (54)), `x₀, v₀ ∈ V`, and `x*` a global minimizer of `f`. Then the NAG flow (57)
`γx″ + (μ + γ)x′ + ∇f(x) = 0`, `x(0) = x₀`, `x′(0) = v₀ − x₀`, admits a solution
`x ∈ C²([0, ∞); V)`, unique on `[0, ∞)`; and, with `v = x + x′` and the Lyapunov function (58)
`ℒ(t) = f(x(t)) − f(x*) + γ(t)/2 ‖v(t) − x*‖²`, `ℒ` is differentiable on `[0, ∞)` (right derivative
at `0`) with
`ℒ′(t) ≤ −ℒ(t) − μ/2 ‖x′(t)‖²` (59), and
`ℒ(t) + μ/2 ∫₀ᵗ e^{s−t} ‖x′(s)‖² ds ≤ e^{−t} ℒ(0)` for all `t ≥ 0` (60). -/
theorem lemma_3_2 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L) (hγ₀ : 0 < γ₀)
    (x₀ v₀ xstar : V) (hxstar : ∀ y, f xstar ≤ f y) :
    ∃ x : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ x ∧
      (∀ y : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ y → EqOn y x (Ici 0)) ∧
      (∀ t : ℝ, 0 ≤ t → ∃ dL : ℝ,
        HasDerivWithinAt (lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s)) dL
          (Ici 0) t ∧
        dL ≤ -lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) t
          - μ / 2 * ‖dI x t‖ ^ 2) ∧
      (∀ t : ℝ, 0 ≤ t →
        lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) t
          + μ / 2 * ∫ s in (0 : ℝ)..t, Real.exp (s - t) * ‖dI x s‖ ^ 2
        ≤ Real.exp (-t) * lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) 0) := by
  exact NAGFlowProof.full_native_flow f gradf μ L γ₀ hf hγ₀ x₀ v₀ xstar hxstar

end NAGFlow.Flow

open NAGFlow.Flow Set

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L γ₀ : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L) (hγ₀ : 0 < γ₀)
    (x₀ v₀ xstar : V) (hxstar : ∀ y, f xstar ≤ f y) :
    ∃ x : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ x ∧
      (∀ y : ℝ → V, IsNAGSolution2 f gradf μ γ₀ x₀ v₀ y → EqOn y x (Ici 0)) ∧
      (∀ t : ℝ, 0 ≤ t → ∃ dL : ℝ,
        HasDerivWithinAt (lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s)) dL
          (Ici 0) t ∧
        dL ≤ -lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) t
          - μ / 2 * ‖dI x t‖ ^ 2) ∧
      (∀ t : ℝ, 0 ≤ t →
        lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) t
          + μ / 2 * ∫ s in (0 : ℝ)..t, Real.exp (s - t) * ‖dI x s‖ ^ 2
        ≤ Real.exp (-t) * lyapFlow f xstar (gammaFn μ γ₀) x (fun s => x s + dI x s) 0) := NAGFlow.Flow.lemma_3_2 f gradf μ L γ₀ hf hγ₀ x₀ v₀ xstar hxstar
