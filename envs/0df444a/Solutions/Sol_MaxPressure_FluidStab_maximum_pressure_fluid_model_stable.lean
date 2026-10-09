-- Prove2me | solution 1 for MaxPressure.FluidStab.maximum_pressure_fluid_model_stable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:45:27.428986+00:00
-- url     : https://prove2.me/submissions/df78b35f-ad7f-4ef1-9157-28506d3086d5

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

set_option autoImplicit false

open MaxPressure.FluidStab Matrix in
/-- The pressure as a linear map in the allocation. -/
noncomputable def mp98PressureLin {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) :
    (Fin J → ℝ) →ₗ[ℝ] ℝ where
  toFun a := pressure N a z
  map_add' a b := by simp [pressure, Matrix.mulVec_add, dotProduct_add]
  map_smul' c a := by simp [pressure, Matrix.mulVec_smul, dotProduct_smul]

open MaxPressure.FluidStab Matrix in
lemma mp98_allocSet_isCompact {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    IsCompact (allocSet N) := by
  obtain ⟨hA01, -, -, -, hAk, -⟩ := hN
  have hcl : IsClosed (allocSet N) := by
    have h1 : IsClosed {a : Fin J → ℝ | ∀ j, 0 ≤ a j} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
    have h2 : IsClosed {a : Fin J → ℝ | ∀ k, ∑ j, N.A k j * a j ≤ 1} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
        continuous_const
    have h3 : IsClosed {a : Fin J → ℝ | ∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_eq
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
        continuous_const
    have : allocSet N = {a : Fin J → ℝ | ∀ j, 0 ≤ a j} ∩
        {a : Fin J → ℝ | ∀ k, ∑ j, N.A k j * a j ≤ 1} ∩
        {a : Fin J → ℝ | ∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1} := by
      ext a; simp [allocSet, and_assoc]
    rw [this]; exact (h1.inter h2).inter h3
  refine (isCompact_Icc (a := (0 : Fin J → ℝ)) (b := 1)).of_isClosed_subset hcl ?_
  intro a ha
  obtain ⟨hpos, hle, -⟩ := ha
  refine ⟨fun j => hpos j, fun j => ?_⟩
  obtain ⟨k, hk⟩ := hAk j
  have hnn : ∀ j' ∈ (Finset.univ : Finset (Fin J)), 0 ≤ N.A k j' * a j' := by
    intro j' _
    rcases hA01 k j' with h | h <;> simp [h, hpos j']
  have := Finset.single_le_sum hnn (Finset.mem_univ j)
  simp only [hk, one_mul] at this
  simpa using this.trans (hle k)

open MaxPressure.FluidStab Matrix in
lemma mp98_max_extreme {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hne : (allocSet N).Nonempty) (z : Fin I → ℝ) :
    ∃ e ∈ extremeAllocs N, ∀ a ∈ allocSet N, pressure N a z ≤ pressure N e z := by
  have hc := mp98_allocSet_isCompact N hN
  let l : StrongDual ℝ (Fin J → ℝ) := LinearMap.toContinuousLinearMap (mp98PressureLin N z)
  have hl : ∀ a, l a = pressure N a z := fun a => rfl
  have hexp : IsExposed ℝ (allocSet N) (l.toExposed (allocSet N)) :=
    ContinuousLinearMap.toExposed.isExposed
  have hSc : IsCompact (l.toExposed (allocSet N)) := hexp.isCompact hc
  have hSne : (l.toExposed (allocSet N)).Nonempty := by
    obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hne l.continuous.continuousOn
    exact ⟨x, hx, fun y hy => hmax hy⟩
  obtain ⟨e, he⟩ := hSc.extremePoints_nonempty hSne
  refine ⟨e, hexp.isExtreme.extremePoints_subset_extremePoints he, fun a ha => ?_⟩
  have := he.1.2 a ha
  simpa [hl] using this

open MaxPressure.FluidStab Matrix in
lemma mp98_R_input_nonpos {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (j : Fin J) (hj : IsInputActivity N j) (i : Fin I) : R N i j ≤ 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hm, hP, _⟩ := hN
  obtain ⟨h0, hs⟩ := hj
  have hR : R N i j = -(μ N j * N.B j 0 * N.P j 0 i.succ) := by
    unfold R
    rw [Fin.sum_univ_succ]
    simp only [hs, zero_mul, Finset.sum_const_zero, add_zero, zero_sub]
    ring
  rw [hR, h0]
  have hμ : 0 < μ N j := by unfold μ; exact one_div_pos.mpr (hm j)
  have := hP j 0 i.succ
  have : 0 ≤ μ N j * 1 * N.P j 0 i.succ := by positivity
  linarith

open MaxPressure.FluidStab Matrix in
lemma mp98_input_zeroed {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (h2 : Assumption2 N) :
    ∃ xh : Fin J → ℝ, (∀ j, 0 ≤ xh j) ∧ (∀ i, 0 < (R N *ᵥ xh) i) ∧
      (∀ k, N.inputProc k → ∑ j, N.A k j * xh j = 0) := by
  classical
  obtain ⟨x, hx0, hxR⟩ := h2
  obtain ⟨hA01, -, -, -, -, hAin, -⟩ := id hN
  refine ⟨fun j => if IsInputActivity N j then 0 else x j, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hx0 j
  · intro i
    refine lt_of_lt_of_le (hxR i) ?_
    simp only [mulVec, dotProduct]
    refine Finset.sum_le_sum (fun j _ => ?_)
    split_ifs with hj
    · have h1 := mp98_R_input_nonpos N hN j hj i
      have h2 := hx0 j
      have : R N i j * x j ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2
      simpa using this
    · exact le_rfl
  · intro k hk
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rcases hA01 k j with h | h
    · simp [h]
    · have hj : IsInputActivity N j := (hAin k j h).mp hk
      simp [hj]

open MaxPressure.FluidStab Matrix in
lemma mp98_xstar {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (h2 : Assumption2 N) (hLP : ∃ (x : Fin J → ℝ) (ρ : ℝ), ρ < 1 ∧ LPFeasible N x ρ) :
    ∃ xs : Fin J → ℝ, xs ∈ allocSet N ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ (R N *ᵥ xs) i := by
  obtain ⟨xh, hxh0, hxhR, hxhin⟩ := mp98_input_zeroed N hN h2
  obtain ⟨xt, ρ, hρ, hR0, hsvc, hinp, hxt0⟩ := hLP
  obtain ⟨hA01, -⟩ := hN
  have hAnn : ∀ k j, 0 ≤ N.A k j := fun k j => by rcases hA01 k j with h | h <;> simp [h]
  have hSk : ∀ k, 0 ≤ ∑ j, N.A k j * xh j := fun k =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hAnn k j) (hxh0 j))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ k, ∑ j, N.A k j * xh j := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; exact Finset.sum_nonneg (fun k _ => hSk k)
  have hSkM : ∀ k, ∑ j, N.A k j * xh j ≤ M := fun k => by
    rw [hMdef]
    exact Finset.single_le_sum (f := fun k => ∑ j, N.A k j * xh j) (fun k _ => hSk k)
      (Finset.mem_univ k)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (1 - ρ) / (1 + M) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; exact div_pos (by linarith) (by linarith)
  have hcM' : c * (1 + M) = 1 - ρ := by
    rw [hcdef]; field_simp
  have hcM : c * M ≤ 1 - ρ := by nlinarith
  have hsplit : ∀ k, ∑ j, N.A k j * (xt j + c * xh j) =
      ∑ j, N.A k j * xt j + c * ∑ j, N.A k j * xh j := by
    intro k
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hRs : ∀ i, (R N *ᵥ (fun j => xt j + c * xh j)) i = c * (R N *ᵥ xh) i := by
    intro i
    have h0 : (R N *ᵥ xt) i = 0 := by rw [hR0]; rfl
    have : (R N *ᵥ (fun j => xt j + c * xh j)) i = (R N *ᵥ xt) i + c * (R N *ᵥ xh) i := by
      simp only [mulVec, dotProduct]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, h0, zero_add]
  obtain ⟨ε0, hε0, hε0le⟩ : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ i, ε0 ≤ (R N *ᵥ xh) i := by
    rcases isEmpty_or_nonempty (Fin I) with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ
        (fun i => (R N *ᵥ xh) i) Finset.univ_nonempty
      exact ⟨_, hxhR i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨fun j => xt j + c * xh j, ⟨?_, ?_, ?_⟩, c * ε0, mul_pos hc0 hε0, ?_⟩
  · intro j
    exact add_nonneg (hxt0 j) (mul_nonneg hc0.le (hxh0 j))
  · intro k
    rw [hsplit k]
    by_cases hk : N.inputProc k
    · rw [hinp k hk, hxhin k hk]; simp
    · have h1 := hsvc k hk
      have h2 := mul_le_mul_of_nonneg_left (hSkM k) hc0.le
      linarith
  · intro k hk
    rw [hsplit k, hinp k hk, hxhin k hk]; simp
  · intro i
    rw [hRs i]
    exact mul_le_mul_of_nonneg_left (hε0le i) hc0.le

open Matrix MaxPressure.FluidStab in
theorem mp98_fluid_vec {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    ∀ s, 0 ≤ s → Zb s = Zb 0 - R N *ᵥ Tb s := by
  intro s hs
  funext i
  rw [hsol.1 s hs i]
  have key : (R N *ᵥ Tb s) i = ∑ j : Fin J, Tb s j * μ N j * N.B j i.succ
      - ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb s j * μ N j * N.B j i' * N.P j i' i.succ := by
    rw [Finset.sum_comm (f := fun i' j => Tb s j * μ N j * N.B j i' * N.P j i' i.succ),
      ← Finset.sum_sub_distrib]
    simp only [mulVec, dotProduct, R]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · refine Finset.sum_congr rfl (fun i' _ => ?_)
      ring
  rw [Pi.sub_apply, key]
  ring

open Matrix MaxPressure.FluidStab in
theorem mp98_deriv_eq {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    ∀ t, IsRegular Zb Tb t →
      HasDerivAt (fun s => ∑ i, Zb s i ^ 2) (2 * (deriv Zb t ⬝ᵥ Zb t)) t ∧
      2 * (deriv Zb t ⬝ᵥ Zb t) = -2 * pressure N (deriv Tb t) (Zb t) := by
  have hvec := mp98_fluid_vec N Zb Tb hsol
  intro t ht
  obtain ⟨htpos, hZdiff, hTdiff⟩ := ht
  have hZd : HasDerivAt Zb (deriv Zb t) t := hZdiff.hasDerivAt
  have hTd : HasDerivAt Tb (deriv Tb t) t := hTdiff.hasDerivAt
  have hZi : ∀ i, HasDerivAt (fun s => Zb s i) (deriv Zb t i) t := hasDerivAt_pi.mp hZd
  have hTj : ∀ j, HasDerivAt (fun s => Tb s j) (deriv Tb t j) t := hasDerivAt_pi.mp hTd
  refine ⟨?_, ?_⟩
  · have hp : ∀ i, HasDerivAt (fun s => Zb s i ^ 2) (2 * Zb t i * deriv Zb t i) t := by
      intro i
      exact ((hZi i).fun_pow 2).congr_deriv (by norm_num)
    have hs : HasDerivAt (∑ i, fun s => Zb s i ^ 2) (∑ i, 2 * Zb t i * deriv Zb t i) t :=
      HasDerivAt.sum (fun i _ => hp i)
    have hf : (fun s => ∑ i, Zb s i ^ 2) = ∑ i, (fun s => Zb s i ^ 2) := by
      funext s
      simp [Finset.sum_apply]
    rw [hf]
    refine hs.congr_deriv ?_
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · have hg : HasDerivAt (fun s => Zb 0 - R N *ᵥ Tb s) (-(R N *ᵥ deriv Tb t)) t := by
      refine hasDerivAt_pi.mpr (fun i => ?_)
      have h1 := ((HasDerivAt.sum (u := Finset.univ)
        (fun j _ => (hTj j).const_mul (R N i j))).const_sub (Zb 0 i))
      convert h1 using 1
      · funext s
        simp [mulVec, dotProduct]
      · simp [mulVec, dotProduct]
    have heq : Zb =ᶠ[nhds t] (fun s => Zb 0 - R N *ᵥ Tb s) := by
      filter_upwards [Ioi_mem_nhds htpos] with s hs
      exact hvec s (le_of_lt hs)
    have hZ' : deriv Zb t = -(R N *ᵥ deriv Tb t) :=
      (hg.congr_of_eventuallyEq heq).deriv
    rw [hZ', pressure, neg_dotProduct, dotProduct_comm]
    ring

open MaxPressure.FluidStab Matrix in
lemma mp98_drift {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hsol : IsFluidSolution N Zb Tb) (hmp : MPFluidEq N Zb Tb)
    (xs : Fin J → ℝ) (hxs : xs ∈ allocSet N) (ε : ℝ) (hε : 0 < ε)
    (hR : ∀ i, ε ≤ (R N *ᵥ xs) i) (t : ℝ) (ht : IsRegular Zb Tb t) :
    HasDerivAt (fun s => ∑ i, Zb s i ^ 2) (-2 * pressure N (deriv Tb t) (Zb t)) t ∧
    ε * Real.sqrt (∑ i, Zb t i ^ 2) ≤ pressure N (deriv Tb t) (Zb t) := by
  obtain ⟨hd, heq⟩ := mp98_deriv_eq N Zb Tb hsol t ht
  refine ⟨by rw [← heq]; exact hd, ?_⟩
  obtain ⟨e, he, hemax⟩ := mp98_max_extreme N hN ⟨xs, hxs⟩ (Zb t)
  have h1 : pressure N xs (Zb t) ≤ pressure N (deriv Tb t) (Zb t) :=
    (hemax xs hxs).trans ((hmp t ht).2 ⟨e, he, rfl⟩)
  have hZ : ∀ i, 0 ≤ Zb t i := hsol.2.1 t ht.1.le
  have h2 : ε * ∑ i, Zb t i ≤ pressure N xs (Zb t) := by
    unfold pressure
    simp only [dotProduct]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      rw [mul_comm ε]; exact mul_le_mul_of_nonneg_left (hR i) (hZ i))
  have h3 : Real.sqrt (∑ i, Zb t i ^ 2) ≤ ∑ i, Zb t i := by
    calc Real.sqrt (∑ i, Zb t i ^ 2) ≤ Real.sqrt ((∑ i, Zb t i) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hZ i))
      _ = ∑ i, Zb t i := Real.sqrt_sq (Finset.sum_nonneg fun i _ => hZ i)
  have h4 := mul_le_mul_of_nonneg_left h3 hε.le
  linarith

open MaxPressure.FluidStab Matrix in
lemma mp98_T_lip {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    ∀ s, 0 ≤ s → ∀ u, 0 ≤ u → dist (Tb s) (Tb u) ≤ dist s u := by
  obtain ⟨hA01, -, -, -, hAk, -⟩ := hN
  obtain ⟨-, -, -, h17, hmono, -⟩ := hsol
  have key : ∀ s u, 0 ≤ s → s ≤ u → ∀ j,
      0 ≤ Tb u j - Tb s j ∧ Tb u j - Tb s j ≤ u - s := by
    intro s u hs hsu j
    have hinc : ∀ j', 0 ≤ Tb u j' - Tb s j' := fun j' =>
      sub_nonneg.mpr (hmono (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr (hs.trans hsu)) hsu j')
    refine ⟨hinc j, ?_⟩
    obtain ⟨k, hk⟩ := hAk j
    have hnn : ∀ j' ∈ (Finset.univ : Finset (Fin J)),
        0 ≤ N.A k j' * (Tb u j' - Tb s j') := by
      intro j' _
      rcases hA01 k j' with h | h <;> simp [h, hinc j']
    have := Finset.single_le_sum hnn (Finset.mem_univ j)
    simp only [hk, one_mul] at this
    exact this.trans (h17 s u hs hsu k)
  intro s hs u hu
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total s u with h | h
  · obtain ⟨h1, h2⟩ := key s u hs h j
    have e1 : |Tb s j - Tb u j| = Tb u j - Tb s j := by
      rw [abs_sub_comm]; exact abs_of_nonneg h1
    have e2 : |s - u| = u - s := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [e1, e2]; exact h2
  · obtain ⟨h1, h2⟩ := key u s hu h j
    have e1 : |Tb s j - Tb u j| = Tb s j - Tb u j := abs_of_nonneg h1
    have e2 : |s - u| = s - u := abs_of_nonneg (by linarith)
    rw [e1, e2]; exact h2

open MaxPressure.FluidStab Matrix in
lemma mp98_g_lip {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    ∃ C : NNReal, LipschitzOnWith C (fun s => Real.sqrt (∑ i, Zb s i ^ 2)) (Set.Ici 0) := by
  let E := (EuclideanSpace.equiv (Fin I) ℝ).symm
  let L : (Fin J → ℝ) →L[ℝ] (Fin I → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (R N))
  have hL : ∀ v, L v = R N *ᵥ v := fun v => rfl
  obtain ⟨CE, hCE⟩ : ∃ C, LipschitzWith C E := ⟨_, E.lipschitz⟩
  obtain ⟨CL, hCL⟩ : ∃ C, LipschitzWith C L := ⟨_, L.lipschitz⟩
  have hg : (fun s => Real.sqrt (∑ i, Zb s i ^ 2)) = fun s => ‖E (Zb s)‖ := by
    funext s
    rw [EuclideanSpace.norm_eq]
    simp [E]
  have hvec := mp98_fluid_vec N Zb Tb hsol
  have hT := mp98_T_lip N hN Zb Tb hsol
  refine ⟨Real.toNNReal ((CE : ℝ) * CL), ?_⟩
  rw [hg]
  refine LipschitzOnWith.of_dist_le' (fun s hs u hu => ?_)
  have hs' : (0:ℝ) ≤ s := hs
  have hu' : (0:ℝ) ≤ u := hu
  calc dist ‖E (Zb s)‖ ‖E (Zb u)‖ ≤ dist (E (Zb s)) (E (Zb u)) := dist_norm_norm_le _ _
    _ ≤ CE * dist (Zb s) (Zb u) := hCE.dist_le_mul _ _
    _ = CE * dist (L (Tb s)) (L (Tb u)) := by
        rw [hvec s hs', hvec u hu', dist_sub_left, hL, hL]
    _ ≤ CE * (CL * dist (Tb s) (Tb u)) := by
        gcongr
        exact hCL.dist_le_mul _ _
    _ ≤ CE * (CL * dist s u) := by
        gcongr
        exact hT s hs' u hu'
    _ = (CE : ℝ) * CL * dist s u := by ring

open MaxPressure.FluidStab Matrix MeasureTheory in
lemma mp98_ae_regular {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → IsRegular Zb Tb t := by
  have hT := mp98_T_lip N hN Zb Tb hsol
  have hTL : LipschitzOnWith 1 Tb (Set.Ioi 0) := by
    refine LipschitzOnWith.of_dist_le_mul (fun s hs u hu => ?_)
    simpa using hT s (le_of_lt hs) u (le_of_lt hu)
  have hvec := mp98_fluid_vec N Zb Tb hsol
  let L : (Fin J → ℝ) →L[ℝ] (Fin I → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (R N))
  have hL : ∀ v, L v = R N *ᵥ v := fun v => rfl
  filter_upwards [hTL.ae_differentiableWithinAt_of_mem] with t ht htpos
  have hTd : DifferentiableAt ℝ Tb t := (ht htpos).differentiableAt (Ioi_mem_nhds htpos)
  refine ⟨htpos, ?_, hTd⟩
  have hd : DifferentiableAt ℝ (fun s => Zb 0 - L (Tb s)) t :=
    (L.differentiableAt.comp t hTd).const_sub _
  have heq : Zb =ᶠ[nhds t] (fun s => Zb 0 - L (Tb s)) := by
    filter_upwards [Ioi_mem_nhds htpos] with s hs
    rw [hL]
    exact hvec s (le_of_lt hs)
  exact hd.congr_of_eventuallyEq heq

open MeasureTheory in
theorem mp98_ae_ne_zero : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
  rw [ae_iff]; simp

open MeasureTheory in
theorem mp98_deriv_nonpos (g : ℝ → ℝ)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε) :
    ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → deriv g t ≤ 0 := by
  filter_upwards [hdrift] with t ht htpos
  by_cases hd : DifferentiableAt ℝ g t
  · rcases (hg t htpos.le).lt_or_eq with hpos | hzero
    · have := ht htpos hpos (deriv g t) hd.hasDerivAt
      linarith
    · have hmin : IsLocalMin g t := by
        filter_upwards [lt_mem_nhds htpos] with y hy
        rw [← hzero]
        exact hg y hy.le
      exact (hmin.deriv_eq_zero).le
  · rw [deriv_zero_of_not_differentiableAt hd]

open MeasureTheory in
theorem mp98_antitone (g : ℝ → ℝ)
    (hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε) :
    AntitoneOn g (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : (0:ℝ) ≤ a := ha
  have hF := (hac a b ha' hab).integral_deriv_eq_sub
  have hI : ∫ x in a..b, deriv g x ≤ ∫ x in a..b, (0:ℝ) := by
    apply intervalIntegral.integral_mono_ae_restrict hab
      (hac a b ha' hab).intervalIntegrable_deriv intervalIntegrable_const
    have h1 := mp98_deriv_nonpos g hg ε hε hdrift
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h1,
      ae_restrict_of_ae mp98_ae_ne_zero] with x hx hx1 hx0
    exact hx1 (lt_of_le_of_ne (le_trans ha' hx.1) (Ne.symm hx0))
  simp at hI
  linarith

open MeasureTheory in
theorem mp98_extinct (g : ℝ → ℝ)
    (hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε) :
    ∀ t, g 0 / ε ≤ t → g t = 0 := by
  have hanti := mp98_antitone g hac hg ε hε hdrift
  intro t ht
  have hg0 : 0 ≤ g 0 := hg 0 le_rfl
  have hT : 0 ≤ g 0 / ε := div_nonneg hg0 hε.le
  have ht0 : 0 ≤ t := le_trans hT ht
  by_contra hne
  have hpos : 0 < g t := lt_of_le_of_ne (hg t ht0) (Ne.symm hne)
  have hall : ∀ s, 0 ≤ s → s ≤ t → 0 < g s := fun s hs hst =>
    lt_of_lt_of_le hpos (hanti (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr ht0) hst)
  have hAC := hac 0 t le_rfl ht0
  have hF := hAC.integral_deriv_eq_sub
  have hI : ∫ x in (0:ℝ)..t, deriv g x ≤ ∫ x in (0:ℝ)..t, (-ε) := by
    apply intervalIntegral.integral_mono_ae_restrict ht0
      hAC.intervalIntegrable_deriv intervalIntegrable_const
    have hd := hAC.ae_differentiableAt
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hdrift,
      ae_restrict_of_ae hd, ae_restrict_of_ae mp98_ae_ne_zero] with x hx hx1 hx2 hx0
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hxu : x ∈ Set.uIcc (0:ℝ) t := by
      rw [Set.uIcc_of_le ht0]; exact hx
    exact hx1 hxpos (hall x hx.1 hx.2) _ (hx2 hxu).hasDerivAt
  simp at hI
  have hεt : g 0 ≤ ε * t := by
    have := (div_le_iff₀ hε).mp ht
    linarith
  linarith

open MaxPressure.FluidStab Matrix MeasureTheory in
theorem solution {I J K : ℕ} (N : Network I J K)
    (hN : N.Standing) (hEAA : EAA N) (h2 : Assumption2 N)
    (hLP : ∃ (x : Fin J → ℝ) (ρ : ℝ), ρ < 1 ∧ LPFeasible N x ρ) :
    FluidStable (fun (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) =>
      IsFluidSolution N Zb Tb ∧ MPFluidEq N Zb Tb) := by
  obtain ⟨xs, hxs, ε, hε, hR⟩ := mp98_xstar N hN h2 hLP
  refine ⟨1 / ε, by positivity, ?_⟩
  rintro Zb Tb ⟨hsol, hmp⟩ hZ0 t ht
  obtain ⟨C, hC⟩ := mp98_g_lip N hN Zb Tb hsol
  have hac : ∀ a b, 0 ≤ a → a ≤ b →
      AbsolutelyContinuousOnInterval (fun s => Real.sqrt (∑ i, Zb s i ^ 2)) a b := by
    intro a b ha hab
    refine (hC.mono ?_).absolutelyContinuousOnInterval
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact le_trans ha hx.1
  have hgnn : ∀ s : ℝ, 0 ≤ s → 0 ≤ (fun s => Real.sqrt (∑ i, Zb s i ^ 2)) s :=
    fun s _ => Real.sqrt_nonneg _
  have hdrift : ∀ᵐ s ∂(volume : Measure ℝ), 0 < s →
      0 < (fun s => Real.sqrt (∑ i, Zb s i ^ 2)) s →
      ∀ d, HasDerivAt (fun s => Real.sqrt (∑ i, Zb s i ^ 2)) d s → d ≤ -ε := by
    filter_upwards [mp98_ae_regular N hN Zb Tb hsol] with s hs hspos hgpos d hd
    obtain ⟨hf, hle⟩ := mp98_drift N hN Zb Tb hsol hmp xs hxs ε hε hR s (hs hspos)
    have hsq : (fun u => Real.sqrt (∑ i, Zb u i ^ 2) * Real.sqrt (∑ i, Zb u i ^ 2)) =
        fun u => ∑ i, Zb u i ^ 2 := by
      funext u
      exact Real.mul_self_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have h2' : HasDerivAt (fun u => ∑ i, Zb u i ^ 2)
        (d * Real.sqrt (∑ i, Zb s i ^ 2) + Real.sqrt (∑ i, Zb s i ^ 2) * d) s := by
      rw [← hsq]
      exact hd.mul hd
    have huniq := h2'.unique hf
    have hgpos' : 0 < Real.sqrt (∑ i, Zb s i ^ 2) := hgpos
    by_contra hcon
    have hcon : -ε < d := not_le.mp hcon
    have := mul_pos hgpos' (by linarith : 0 < d + ε)
    nlinarith
  have hext := mp98_extinct _ hac hgnn ε hε hdrift
  have hgt : Real.sqrt (∑ i, Zb t i ^ 2) = 0 := hext t (by
    calc Real.sqrt (∑ i, Zb 0 i ^ 2) / ε ≤ 1 / ε := div_le_div_of_nonneg_right hZ0 hε.le
      _ ≤ t := ht)
  have hsum : ∑ i, Zb t i ^ 2 = 0 := by
    rwa [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at hgt
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (Zb t i))).mp hsum i
    (Finset.mem_univ i)
  simpa using this
