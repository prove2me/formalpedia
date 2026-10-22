-- Prove2me | solution 1 for MaxPressure.FluidStab.explicit_emptying_time
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:32:34.834001+00:00
-- url     : https://prove2.me/submissions/86babed7-3210-454b-bba7-683d4b5942c5

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network



namespace MaxPressure.FluidStab

open Matrix MeasureTheory Set

lemma eet_hA0 {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (k : Fin K) (j : Fin J) :
    0 ≤ N.A k j := by
  rcases hN.1 k j with h | h <;> rw [h] <;> norm_num

lemma eet_R_input_nonpos {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (j : Fin J)
    (hj : IsInputActivity N j) (i : Fin I) : R N i j ≤ 0 := by
  obtain ⟨_, hB01, -, -, -, -, -, -, hm, hP, -⟩ := hN
  unfold R μ
  have hμ : 0 < 1 / N.m j := by have := hm j; positivity
  have : 0 ≤ ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ := by
    apply Finset.sum_nonneg; intro i' _
    rcases hB01 j i' with h | h <;> rw [h]
    · simp
    · simpa using hP j i' i.succ
  rw [hj.2 i]
  exact mul_nonpos_of_nonneg_of_nonpos hμ.le (by linarith)

lemma eet_exists_xh {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (h2 : Assumption2 N) :
    ∃ xh : Fin J → ℝ, (∀ j, 0 ≤ xh j) ∧ (∀ i, 0 < (R N *ᵥ xh) i) ∧
      (∀ k, N.inputProc k → ∑ j, N.A k j * xh j = 0) := by
  classical
  obtain ⟨x, hx0, hxR⟩ := h2
  refine ⟨fun j => if IsInputActivity N j then 0 else x j, ?_, ?_, ?_⟩
  · intro j; dsimp only; split_ifs
    · exact le_rfl
    · exact hx0 j
  · intro i
    refine lt_of_lt_of_le (hxR i) ?_
    simp only [mulVec, dotProduct]
    apply Finset.sum_le_sum; intro j _
    split_ifs with h
    · rw [mul_zero]; exact mul_nonpos_of_nonpos_of_nonneg (eet_R_input_nonpos N hN j h i) (hx0 j)
    · exact le_rfl
  · intro k hk
    apply Finset.sum_eq_zero; intro j _
    rcases hN.1 k j with h | h
    · simp [h]
    · have : IsInputActivity N j := (hN.2.2.2.2.2.1 k j h).1 hk
      simp [this]

lemma eet_exists_xstar {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (h2 : Assumption2 N)
    (hLP : ∃ (x : Fin J → ℝ) (ρ : ℝ), ρ < 1 ∧ LPFeasible N x ρ) :
    ∃ xs ∈ allocSet N, ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ (R N *ᵥ xs) i := by
  obtain ⟨xh, hxh0, hxhR, hxhin⟩ := eet_exists_xh N hN h2
  obtain ⟨xt, ρ, hρ, hR0, hserv, hinp, hxt0⟩ := hLP
  have hA0 := eet_hA0 N hN
  have hrow0 : ∀ k, 0 ≤ ∑ j, N.A k j * xh j := fun k =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hA0 k j) (hxh0 j)
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ k, ∑ j, N.A k j * xh j := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun k _ => hrow0 k
  have hrow : ∀ k, ∑ j, N.A k j * xh j ≤ S := fun k => hS ▸
    Finset.single_le_sum (f := fun k => ∑ j, N.A k j * xh j) (fun k _ => hrow0 k)
      (Finset.mem_univ k)
  obtain ⟨c, hc⟩ : ∃ c, c = (1 - ρ) / (S + 1) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ div_pos (by linarith) (by linarith)
  have hcS : c * S ≤ 1 - ρ := by
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨δ, hδ, hδR⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ (R N *ᵥ xh) i := by
    rcases isEmpty_or_nonempty (Fin I) with hI | hI
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i => (R N *ᵥ xh) i)
      exact ⟨_, hxhR i0, hi0⟩
  have e : ∀ k, ∑ j, N.A k j * (xt + c • xh) j
      = ∑ j, N.A k j * xt j + c * ∑ j, N.A k j * xh j := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intros; ring
  refine ⟨xt + c • xh, ⟨?_, ?_, ?_⟩, c * δ, mul_pos hc0 hδ, ?_⟩
  · intro j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hxt0 j; have := hxh0 j; positivity
  · intro k
    rw [e]
    by_cases hk : N.inputProc k
    · rw [hinp k hk, hxhin k hk]; simp
    · have h1 := hserv k hk
      have h2 := mul_le_mul_of_nonneg_left (hrow k) hc0.le
      linarith
  · intro k hk; rw [e, hinp k hk, hxhin k hk]; simp
  · intro i
    rw [mulVec_add, mulVec_smul, hR0]
    simp only [zero_add, Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hδR i) hc0.le

lemma eet_allocSet_convex {I J K : ℕ} (N : Network I J K) : Convex ℝ (allocSet N) := by
  intro x ⟨hx0, hx1, hx2⟩ y ⟨hy0, hy1, hy2⟩ a b ha hb hab
  have e : ∀ k, ∑ j, N.A k j * (a • x + b • y) j
      = a * ∑ j, N.A k j * x j + b * ∑ j, N.A k j * y j := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intros; ring
  refine ⟨fun j => ?_, fun k => ?_, fun k hk => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx0 j; have := hy0 j; positivity
  · rw [e]
    have := mul_le_mul_of_nonneg_left (hx1 k) ha
    have := mul_le_mul_of_nonneg_left (hy1 k) hb
    linarith
  · rw [e, hx2 k hk, hy2 k hk]; linarith

lemma eet_allocSet_isCompact {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    IsCompact (allocSet N) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : allocSet N = ((⋂ j, {a : Fin J → ℝ | 0 ≤ a j}) ∩
        (⋂ k, {a : Fin J → ℝ | ∑ j, N.A k j * a j ≤ 1})) ∩
        (⋂ k, {a : Fin J → ℝ | N.inputProc k → ∑ j, N.A k j * a j = 1}) := by
      ext a; simp [allocSet, and_assoc]
    rw [this]
    refine ((isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_iInter fun k => isClosed_le (by fun_prop) continuous_const)).inter
      (isClosed_iInter fun k => ?_)
    by_cases hk : N.inputProc k
    · simp only [hk, forall_const]; exact isClosed_eq (by fun_prop) continuous_const
    · simp only [hk, IsEmpty.forall_iff, ofPred_true]; exact isClosed_univ
  · refine (Metric.isBounded_closedBall (x := (0 : Fin J → ℝ)) (r := 1)).subset ?_
    rintro a ⟨h0, h1, _⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 j)]
    calc a j = N.A k j * a j := by rw [hk, one_mul]
      _ ≤ ∑ j', N.A k j' * a j' :=
          Finset.single_le_sum (f := fun j' => N.A k j' * a j')
            (fun j' _ => mul_nonneg (eet_hA0 N hN k j') (h0 j')) (Finset.mem_univ j)
      _ ≤ 1 := h1 k

lemma eet_pressure_le_of_extreme {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (z : Fin I → ℝ) (M : ℝ) (h : ∀ a ∈ extremeAllocs N, pressure N a z ≤ M) :
    ∀ a ∈ allocSet N, pressure N a z ≤ M := by
  intro a ha
  have hlin : IsLinearMap ℝ (fun a => pressure N a z) :=
    ⟨fun x y => by simp [pressure, mulVec_add, dotProduct_add],
     fun c x => by simp [pressure, mulVec_smul, dotProduct_smul]⟩
  have hcont : Continuous (fun a => pressure N a z) := by
    unfold pressure; fun_prop
  have hsub : closure (convexHull ℝ (extremeAllocs N)) ⊆ {a | pressure N a z ≤ M} := by
    apply closure_minimal
    · exact convexHull_min h (convex_halfSpace_le hlin M)
    · exact isClosed_le hcont continuous_const
  rw [extremeAllocs, closure_convexHull_extremePoints (eet_allocSet_isCompact N hN)
    (eet_allocSet_convex N)] at hsub
  exact hsub ha

lemma eet_Tb_lip {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    ∀ s t, 0 ≤ s → s ≤ t → ∀ j, 0 ≤ Tb t j - Tb s j ∧ Tb t j - Tb s j ≤ t - s := by
  intro s t hs hst j
  obtain ⟨-, -, -, h17, hmono, -⟩ := hsol
  have hm : ∀ j', 0 ≤ Tb t j' - Tb s j' := fun j' =>
    sub_nonneg.2 (hmono (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst j')
  refine ⟨hm j, ?_⟩
  obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
  calc Tb t j - Tb s j = N.A k j * (Tb t j - Tb s j) := by rw [hk, one_mul]
    _ ≤ ∑ j', N.A k j' * (Tb t j' - Tb s j') :=
        Finset.single_le_sum (f := fun j' => N.A k j' * (Tb t j' - Tb s j'))
          (fun j' _ => mul_nonneg (eet_hA0 N hN k j') (hm j')) (Finset.mem_univ j)
    _ ≤ t - s := h17 s t hs hst k

lemma eet_Tb_abs {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (j : Fin J) : |Tb t j - Tb s j| ≤ |t - s| := by
  rcases le_total s t with h | h
  · obtain ⟨h1, h2⟩ := eet_Tb_lip N hN Zb Tb hsol s t hs h j
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]; exact h2
  · obtain ⟨h1, h2⟩ := eet_Tb_lip N hN Zb Tb hsol t s ht h j
    rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (by linarith)]; exact h2

/-- the affine expression of `Zb` -/
noncomputable def eetV {I J K : ℕ} (N : Network I J K) (Zb : ℝ → Fin I → ℝ)
    (Tb : ℝ → Fin J → ℝ) (u : ℝ) : Fin I → ℝ :=
  fun i => Zb 0 i - ∑ j, R N i j * Tb u j

noncomputable def eetG {I J K : ℕ} (N : Network I J K) (Zb : ℝ → Fin I → ℝ)
    (Tb : ℝ → Fin J → ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (∑ i, eetV N Zb Tb u i ^ 2)

lemma eet_V_eq {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb)
    (t : ℝ) (ht : 0 ≤ t) : eetV N Zb Tb t = Zb t := by
  funext i
  rw [hsol.1 t ht i, eetV]
  have h1 : ∑ j, R N i j * Tb t j = ∑ j, Tb t j * μ N j * N.B j i.succ -
      ∑ i', ∑ j, Tb t j * μ N j * N.B j i' * N.P j i' i.succ := by
    rw [Finset.sum_comm (f := fun i' j => Tb t j * μ N j * N.B j i' * N.P j i' i.succ)]
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _
    show μ N j * (N.B j i.succ - ∑ i', N.B j i' * N.P j i' i.succ) * Tb t j = _
    rw [mul_sub, Finset.mul_sum, sub_mul, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intros; ring
  rw [h1]; ring

lemma eet_sqrt_sum_sq_le_sum {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (∑ i, w i ^ 2) ≤ ∑ i, w i := by
  calc Real.sqrt (∑ i, w i ^ 2) ≤ Real.sqrt ((∑ i, w i) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hw i))
    _ = ∑ i, w i := Real.sqrt_sq (Finset.sum_nonneg fun i _ => hw i)

lemma eet_abs_sqrt_sub {n : ℕ} (x y : Fin n → ℝ) :
    |Real.sqrt (∑ i, x i ^ 2) - Real.sqrt (∑ i, y i ^ 2)| ≤ ∑ i, |x i - y i| := by
  have hn : ∀ z : Fin n → ℝ,
      Real.sqrt (∑ i, z i ^ 2) = ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))‖ := by
    intro z; rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
  rw [hn x, hn y]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← WithLp.toLp_sub, ← hn]
  have := eet_sqrt_sum_sq_le_sum (fun i => |(x - y) i|) (fun i => abs_nonneg _)
  simpa [sq_abs] using this

lemma eet_G_lip {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    LipschitzOnWith (Real.toNNReal (∑ i, ∑ j, |R N i j|)) (eetG N Zb Tb) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, eetG, eetG]
  refine (eet_abs_sqrt_sub _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  simp only [eetV, sub_sub_sub_cancel_left]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (by rw [abs_sub_comm x y]; exact eet_Tb_abs N hN Zb Tb hsol x y hx hy j) (abs_nonneg _)

lemma eet_Tb_ae_diff {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    ∀ᵐ u ∂(volume : Measure ℝ), 0 < u → DifferentiableAt ℝ Tb u := by
  have hlip : LipschitzOnWith (Real.toNNReal 1) Tb (Ioi 0) := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    rw [one_mul, dist_pi_le_iff dist_nonneg]
    intro j
    rw [Real.dist_eq, Real.dist_eq]
    exact eet_Tb_abs N hN Zb Tb hsol y x (le_of_lt hy) (le_of_lt hx) j
  filter_upwards [hlip.ae_differentiableWithinAt_of_mem] with u hu hpos
  exact (hu hpos).differentiableAt (Ioi_mem_nhds hpos)

lemma eet_G_deriv {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hsol : IsFluidSolution N Zb Tb) (hmp : MPFluidEq N Zb Tb)
    (xs : Fin J → ℝ) (hxs : xs ∈ allocSet N) (ε : ℝ) (hε : 0 < ε)
    (hR : ∀ i, ε ≤ (R N *ᵥ xs) i) (s : ℝ) (hs : 0 < s) (hd : DifferentiableAt ℝ Tb s)
    (hG : 0 < eetG N Zb Tb s) : deriv (eetG N Zb Tb) s ≤ -ε := by
  have hT : ∀ j, HasDerivAt (fun u => Tb u j) (deriv Tb s j) s :=
    fun j => (hasDerivAt_pi.1 hd.hasDerivAt) j
  have hv : ∀ i, HasDerivAt (fun u => eetV N Zb Tb u i)
      (-(∑ j, R N i j * deriv Tb s j)) s := by
    intro i
    have := (HasDerivAt.sum (u := Finset.univ)
      (fun j _ => (hT j).const_mul (R N i j))).const_sub (Zb 0 i)
    simpa [eetV] using this
  have hVZ : eetV N Zb Tb s = Zb s := eet_V_eq N Zb Tb hsol s hs.le
  have hF : HasDerivAt (fun u => ∑ i, eetV N Zb Tb u i ^ 2)
      (-2 * pressure N (deriv Tb s) (Zb s)) s := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hv i).pow 2)
    refine this.congr_deriv ?_
    simp only [pressure, dotProduct, mulVec, ← hVZ, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    norm_num; ring
  have hF0 : (∑ i, eetV N Zb Tb s i ^ 2) ≠ 0 := by
    intro h; rw [eetG, h, Real.sqrt_zero] at hG; exact lt_irrefl _ hG
  have hGd := hF.sqrt hF0
  have hderiv : deriv (eetG N Zb Tb) s = -2 * pressure N (deriv Tb s) (Zb s) /
      (2 * eetG N Zb Tb s) := hGd.deriv
  -- pressure bound
  have hreg : IsRegular Zb Tb s := by
    refine ⟨hs, ?_, hd⟩
    have hdv : DifferentiableAt ℝ (eetV N Zb Tb) s :=
      differentiableAt_pi.2 fun i => (hv i).differentiableAt
    refine hdv.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (Ioi_mem_nhds hs)
      fun u hu => (eet_V_eq N Zb Tb hsol u (le_of_lt hu)).symm
  have hmax := hmp s hreg
  have hub : ∀ a ∈ extremeAllocs N, pressure N a (Zb s) ≤ pressure N (deriv Tb s) (Zb s) :=
    fun a ha => hmax.2 ⟨a, ha, rfl⟩
  have h1 := eet_pressure_le_of_extreme N hN (Zb s) _ hub xs hxs
  have hZ0 : ∀ i, 0 ≤ Zb s i := hsol.2.1 s hs.le
  have h2 : ε * ∑ i, Zb s i ≤ pressure N xs (Zb s) := by
    simp only [pressure, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hR i) (hZ0 i)
  have h3 : eetG N Zb Tb s ≤ ∑ i, Zb s i := by
    rw [eetG, hVZ]; exact eet_sqrt_sum_sq_le_sum _ hZ0
  have hp : ε * eetG N Zb Tb s ≤ pressure N (deriv Tb s) (Zb s) := by
    have := mul_le_mul_of_nonneg_left h3 hε.le
    linarith
  rw [hderiv, div_le_iff₀ (by linarith)]
  linarith

lemma eet_G_drop {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hsol : IsFluidSolution N Zb Tb) (hmp : MPFluidEq N Zb Tb)
    (xs : Fin J → ℝ) (hxs : xs ∈ allocSet N) (ε : ℝ) (hε : 0 < ε)
    (hR : ∀ i, ε ≤ (R N *ᵥ xs) i) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hpos : ∀ u ∈ Ioc a b, 0 < eetG N Zb Tb u) :
    eetG N Zb Tb b - eetG N Zb Tb a ≤ -ε * (b - a) := by
  have hac : AbsolutelyContinuousOnInterval (eetG N Zb Tb) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    refine (eet_G_lip N hN Zb Tb hsol).mono ?_
    rw [uIcc_of_le hab]; intro u hu; exact mem_Ici.2 (ha.trans hu.1)
  rw [← hac.integral_deriv_eq_sub]
  have hc : ∫ _ in a..b, (-ε) = -ε * (b - a) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [← hc]
  apply intervalIntegral.integral_mono_ae_restrict hab hac.intervalIntegrable_deriv
    intervalIntegrable_const
  have hrs : (volume : Measure ℝ).restrict (Icc a b) = volume.restrict (Ioc a b) :=
    (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm
  rw [hrs, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [eet_Tb_ae_diff N hN Zb Tb hsol] with u hu hmem
  have hu0 : 0 < u := lt_of_le_of_lt ha hmem.1
  exact eet_G_deriv N hN Zb Tb hsol hmp xs hxs ε hε hR u hu0 (hu hu0) (hpos u hmem)

theorem explicit_emptying_time_core {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (h2 : Assumption2 N)
    (hLP : ∃ (x : Fin J → ℝ) (ρ : ℝ), ρ < 1 ∧ LPFeasible N x ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ),
      IsFluidSolution N Zb Tb → MPFluidEq N Zb Tb →
      ∀ t, Real.sqrt (∑ i, Zb 0 i ^ 2) / ε ≤ t → Zb t = 0 := by
  obtain ⟨xs, hxs, ε, hε, hR⟩ := eet_exists_xstar N hN h2 hLP
  refine ⟨ε, hε, fun Zb Tb hsol hmp t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (div_nonneg (Real.sqrt_nonneg _) hε.le) ht
  have hG0 : eetG N Zb Tb 0 = Real.sqrt (∑ i, Zb 0 i ^ 2) := by
    rw [eetG, eet_V_eq N Zb Tb hsol 0 le_rfl]
  have hGt : eetG N Zb Tb t = Real.sqrt (∑ i, Zb t i ^ 2) := by
    rw [eetG, eet_V_eq N Zb Tb hsol t ht0]
  rw [← hG0, div_le_iff₀ hε] at ht
  have hGnn : ∀ u, 0 ≤ eetG N Zb Tb u := fun u => Real.sqrt_nonneg _
  have key : eetG N Zb Tb t ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hcont : ContinuousOn (eetG N Zb Tb) (Icc 0 t) :=
      (eet_G_lip N hN Zb Tb hsol).continuousOn.mono (fun u hu => mem_Ici.2 hu.1)
    have hSc : IsClosed (Icc 0 t ∩ eetG N Zb Tb ⁻¹' {0}) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    by_cases hS : (Icc 0 t ∩ eetG N Zb Tb ⁻¹' {0}).Nonempty
    · obtain ⟨a, ⟨ha, haz⟩, hamax⟩ :=
        (isCompact_Icc.of_isClosed_subset hSc inter_subset_left).exists_isGreatest hS
      have haz' : eetG N Zb Tb a = 0 := haz
      have hat : a < t := by
        rcases lt_or_eq_of_le ha.2 with h | h
        · exact h
        · rw [h] at haz'; linarith
      have hp : ∀ u ∈ Ioc a t, 0 < eetG N Zb Tb u := by
        intro u hu
        rcases lt_or_eq_of_le (hGnn u) with h | h
        · exact h
        · have : u ≤ a := hamax ⟨⟨ha.1.trans hu.1.le, hu.2⟩, h.symm⟩
          linarith [hu.1]
      have := eet_G_drop N hN Zb Tb hsol hmp xs hxs ε hε hR a t ha.1 hat.le hp
      nlinarith
    · have hp : ∀ u ∈ Ioc 0 t, 0 < eetG N Zb Tb u := by
        intro u hu
        rcases lt_or_eq_of_le (hGnn u) with h | h
        · exact h
        · exact absurd ⟨u, ⟨hu.1.le, hu.2⟩, h.symm⟩ hS
      have := eet_G_drop N hN Zb Tb hsol hmp xs hxs ε hε hR 0 t le_rfl ht0 hp
      nlinarith
  have hz : eetG N Zb Tb t = 0 := le_antisymm key (hGnn t)
  rw [hGt, Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at hz
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (Zb t i))).1 hz i
    (Finset.mem_univ i)
  simpa using this

end MaxPressure.FluidStab

open MaxPressure.FluidStab


theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hEAA : EAA N) (h2 : Assumption2 N)
    (hLP : ∃ (x : Fin J → ℝ) (ρ : ℝ), ρ < 1 ∧ LPFeasible N x ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ),
      IsFluidSolution N Zb Tb → MPFluidEq N Zb Tb →
      ∀ t, Real.sqrt (∑ i, Zb 0 i ^ 2) / ε ≤ t → Zb t = 0 := by
  exact explicit_emptying_time_core N hN h2 hLP
