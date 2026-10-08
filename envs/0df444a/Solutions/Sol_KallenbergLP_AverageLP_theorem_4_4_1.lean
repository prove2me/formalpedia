-- Prove2me | solution 1 for KallenbergLP.AverageLP.theorem_4_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:46:34.254989+00:00
-- url     : https://prove2.me/submissions/9dc49f2a-8b29-4595-bbe4-9fd47c7b2c9f

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace K441

open Matrix Filter Topology BlackwellDiscreteDP.NearOne

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma mulVec_bound (P : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (y : n → ℝ) (B : ℝ) (hy : ∀ j, |y j| ≤ B) (i : n) : |(P *ᵥ y) i| ≤ B := by
  rw [Matrix.mulVec, dotProduct]
  calc |∑ j, P i j * y j| ≤ ∑ j, |P i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, P i j * B := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (hnn i j)]
        exact mul_le_mul_of_nonneg_left (hy j) (hnn i j)
    _ = B := by rw [← Finset.sum_mul, hs i, one_mul]

lemma pow_mulVec_bound (P : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (y : n → ℝ) (B : ℝ) (hy : ∀ j, |y j| ≤ B) (k : ℕ) : ∀ i, |(P ^ k *ᵥ y) i| ≤ B := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    intro i
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact mulVec_bound P hnn hs _ B ih i

lemma telescope (P : Matrix n n ℝ) (y : n → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, P ^ k *ᵥ (y - P *ᵥ y) = y - P ^ N *ᵥ y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_succ]
    abel

lemma pow_fixed (P : Matrix n n ℝ) (a : n → ℝ) (ha : P *ᵥ a = a) (k : ℕ) : P ^ k *ᵥ a = a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, ha, ih]

lemma one_sub_mulVec (P : Matrix n n ℝ) (y : n → ℝ) : (1 - P) *ᵥ y = y - P *ᵥ y := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

lemma exists_bound (y : n → ℝ) : ∃ B : ℝ, ∀ j, |y j| ≤ B :=
  ⟨∑ j, |y j|, fun j => Finset.single_le_sum (f := fun j => |y j|)
    (fun j _ => abs_nonneg (y j)) (Finset.mem_univ j)⟩

lemma disj (P : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1) :
    Disjoint (LinearMap.ker (1 - P).mulVecLin) (LinearMap.range (1 - P).mulVecLin) := by
  rw [Submodule.disjoint_def]
  intro x hk hr
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, one_sub_mulVec, sub_eq_zero] at hk
  obtain ⟨y, hy⟩ := hr
  rw [Matrix.mulVecLin_apply, one_sub_mulVec] at hy
  obtain ⟨B, hB⟩ := exists_bound y
  funext i
  by_contra hne
  have hpos : 0 < |x i| := abs_pos.mpr hne
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B / |x i|)
  have h1 : ∑ k ∈ Finset.range N, P ^ k *ᵥ x = (N : ℝ) • x := by
    simp only [pow_fixed P x hk.symm, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have h2 : ∑ k ∈ Finset.range N, P ^ k *ᵥ x = y - P ^ N *ᵥ y := by
    rw [← hy]; exact telescope P y N
  have h3 := congrFun (h1.symm.trans h2) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h3
  have hb := abs_le.mp (pow_mulVec_bound P hnn hs y B hB N i)
  have hyi := abs_le.mp (hB i)
  have : |(N : ℝ) * x i| ≤ 2 * B := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, Nat.abs_cast] at this
  rw [div_lt_iff₀ hpos] at hN
  linarith

lemma isCompl_ker_range (P : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1) :
    IsCompl (LinearMap.ker (1 - P).mulVecLin) (LinearMap.range (1 - P).mulVecLin) := by
  rw [Submodule.isCompl_iff_disjoint]
  · exact disj P hnn hs
  · have := LinearMap.finrank_range_add_finrank_ker (1 - P).mulVecLin
    omega

/-- The four structural facts about the limit matrix, plus convergence of Cesàro means. -/
theorem limit_facts (P : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) ∧
    (∀ x, P *ᵥ (limitMatrix P *ᵥ x) = limitMatrix P *ᵥ x) ∧
    (∀ y, limitMatrix P *ᵥ (y - P *ᵥ y) = 0) ∧
    (∀ a, P *ᵥ a = a → limitMatrix P *ᵥ a = a) ∧
    (∀ x, ∃ y, x - limitMatrix P *ᵥ x = y - P *ᵥ y) := by
  set K := LinearMap.ker (1 - P).mulVecLin
  set R := LinearMap.range (1 - P).mulVecLin
  have hc : IsCompl K R := isCompl_ker_range P hnn hs
  set pr := K.projection R hc
  -- convergence of Cesàro means on vectors
  have hvec : ∀ x : n → ℝ, ∀ i : n,
      Tendsto (fun N => (cesaroMean P N *ᵥ x) i) atTop (𝓝 (pr x i)) := by
    intro x i
    have hdec := Submodule.projection_add_projection_eq_self hc x
    have hRmem : R.projection K hc.symm x ∈ R := Submodule.projection_apply_mem _ _
    obtain ⟨y, hy⟩ := hRmem
    rw [Matrix.mulVecLin_apply, one_sub_mulVec] at hy
    have hKmem : pr x ∈ K := Submodule.projection_apply_mem _ _
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, one_sub_mulVec, sub_eq_zero] at hKmem
    obtain ⟨B, hB⟩ := exists_bound y
    have hform : ∀ N : ℕ, (cesaroMean P N *ᵥ x) i
        = pr x i + ((N : ℝ) + 1)⁻¹ * (y i - (P ^ (N + 1) *ᵥ y) i) := by
      intro N
      have hx : x = pr x + (y - P *ᵥ y) := by rw [hy]; exact hdec.symm
      have hsum : ∑ k ∈ Finset.range (N + 1), P ^ k *ᵥ x
          = ((N : ℝ) + 1) • pr x + (y - P ^ (N + 1) *ᵥ y) := by
        conv_lhs => rw [hx]
        simp only [Matrix.mulVec_add, Finset.sum_add_distrib, telescope,
          pow_fixed P (pr x) hKmem.symm, Finset.sum_const, Finset.card_range]
        rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one]
      have hpos : ((N : ℝ) + 1) ≠ 0 := by positivity
      unfold cesaroMean
      rw [Matrix.smul_mulVec, Matrix.sum_mulVec, hsum]
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
    simp_rw [hform]
    have h0 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * (y i - (P ^ (N + 1) *ᵥ y) i))
        atTop (𝓝 0) := by
      have hlim : Tendsto (fun N : ℕ => 2 * B * (1 / ((N : ℝ) + 1))) atTop (𝓝 (2 * B * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
      rw [mul_zero] at hlim
      apply squeeze_zero_norm _ hlim
      intro N
      rw [Real.norm_eq_abs, abs_mul, abs_inv, one_div]
      have hN : (0 : ℝ) < |(N : ℝ) + 1| := by positivity
      have hb := abs_le.mp (pow_mulVec_bound P hnn hs y B hB (N + 1) i)
      have hyi := abs_le.mp (hB i)
      have : |y i - (P ^ (N + 1) *ᵥ y) i| ≤ 2 * B := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)] at hN ⊢
      calc ((N : ℝ) + 1)⁻¹ * |y i - (P ^ (N + 1) *ᵥ y) i| ≤ ((N : ℝ) + 1)⁻¹ * (2 * B) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 2 * B * ((N : ℝ) + 1)⁻¹ := by ring
    simpa using (tendsto_const_nhds (x := pr x i)).add h0
  -- matrix convergence
  set Lm : Matrix n n ℝ := Matrix.of fun i j => pr (Pi.single j 1) i
  have hmat : Tendsto (cesaroMean P) atTop (𝓝 Lm) := by
    refine tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => ?_))
    have := hvec (Pi.single j 1) i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simpa [Lm] using this
  have hL : limitMatrix P = Lm := hmat.limUnder_eq
  have hLx : ∀ x, limitMatrix P *ᵥ x = pr x := by
    intro x
    have h1 : Tendsto (fun N => cesaroMean P N *ᵥ x) atTop (𝓝 (limitMatrix P *ᵥ x)) := by
      have hc' : Continuous (fun A : Matrix n n ℝ => A *ᵥ x) :=
        continuous_id.matrix_mulVec continuous_const
      rw [hL]
      exact (hc'.tendsto Lm).comp hmat
    have h2 : Tendsto (fun N => cesaroMean P N *ᵥ x) atTop (𝓝 (pr x)) :=
      tendsto_pi_nhds.mpr (hvec x)
    exact tendsto_nhds_unique h1 h2
  refine ⟨hL ▸ hmat, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hLx]
    have hKmem : pr x ∈ K := Submodule.projection_apply_mem _ _
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, one_sub_mulVec, sub_eq_zero] at hKmem
    exact hKmem.symm
  · intro y
    rw [hLx]
    apply Submodule.projection_apply_of_mem_right
    exact ⟨y, by rw [Matrix.mulVecLin_apply, one_sub_mulVec]⟩
  · intro a ha
    rw [hLx]
    apply Submodule.projection_apply_of_mem_left
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, one_sub_mulVec, ha, sub_self]
  · intro x
    have hRmem : R.projection K hc.symm x ∈ R := Submodule.projection_apply_mem _ _
    obtain ⟨y, hy⟩ := hRmem
    rw [Matrix.mulVecLin_apply, one_sub_mulVec] at hy
    refine ⟨y, ?_⟩
    rw [hy, hLx, Submodule.projection_eq_self_sub_projection hc]

end K441

namespace K441

open Matrix Filter Topology BlackwellDiscreteDP.NearOne

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem system_facts (P : Matrix n n ℝ) (hnn : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (r : n → ℝ) :
    (∃ φ u w : n → ℝ, (1 - P) *ᵥ φ = 0 ∧ φ + (1 - P) *ᵥ u = r ∧ u + (1 - P) *ᵥ w = 0) ∧
    ∀ φ u w : n → ℝ, (1 - P) *ᵥ φ = 0 → φ + (1 - P) *ᵥ u = r → u + (1 - P) *ᵥ w = 0 →
      φ = limitMatrix P *ᵥ r ∧ u = deviationMatrix P *ᵥ r := by
  obtain ⟨-, h1, h2, h3, h4⟩ := limit_facts P hnn hs
  have hAv : ∀ v, (1 - P + limitMatrix P) *ᵥ v = v - P *ᵥ v + limitMatrix P *ᵥ v := by
    intro v; rw [Matrix.add_mulVec, one_sub_mulVec]
  have hLP : ∀ v, limitMatrix P *ᵥ (P *ᵥ v) = limitMatrix P *ᵥ v := by
    intro v
    have := h2 v
    rw [Matrix.mulVec_sub, sub_eq_zero] at this
    exact this.symm
  have hLL : ∀ v, limitMatrix P *ᵥ (limitMatrix P *ᵥ v) = limitMatrix P *ᵥ v :=
    fun v => h3 _ (h1 v)
  have hLA : ∀ v, limitMatrix P *ᵥ ((1 - P + limitMatrix P) *ᵥ v) = limitMatrix P *ᵥ v := by
    intro v
    rw [hAv, Matrix.mulVec_add, Matrix.mulVec_sub, hLP, hLL, sub_self, zero_add]
  have hAL : ∀ v, (1 - P + limitMatrix P) *ᵥ (limitMatrix P *ᵥ v) = limitMatrix P *ᵥ v := by
    intro v; rw [hAv, h1, hLL, sub_self, zero_add]
  have hinj : ∀ v, (1 - P + limitMatrix P) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hLv : limitMatrix P *ᵥ v = 0 := by
      have := hLA v
      rw [hv, Matrix.mulVec_zero] at this
      exact this.symm
    rw [hAv, hLv, add_zero, sub_eq_zero] at hv
    rw [← h3 v hv.symm, hLv]
  have hdet : IsUnit (1 - P + limitMatrix P).det := by
    rw [isUnit_iff_ne_zero]
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    exact hv0 (hinj v hv)
  have hinvA : ∀ v, (1 - P + limitMatrix P)⁻¹ *ᵥ ((1 - P + limitMatrix P) *ᵥ v) = v := by
    intro v; rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hAinv : ∀ v, (1 - P + limitMatrix P) *ᵥ ((1 - P + limitMatrix P)⁻¹ *ᵥ v) = v := by
    intro v; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hD : ∀ v, deviationMatrix P *ᵥ v
      = (1 - P + limitMatrix P)⁻¹ *ᵥ v - limitMatrix P *ᵥ v := by
    intro v; rw [deviationMatrix, Matrix.sub_mulVec]
  constructor
  · obtain ⟨z, hz⟩ : ∃ z, (1 - P + limitMatrix P) *ᵥ z = r := ⟨_, hAinv r⟩
    have hLz : limitMatrix P *ᵥ z = limitMatrix P *ᵥ r := by rw [← hLA z, hz]
    have hLu : limitMatrix P *ᵥ (z - limitMatrix P *ᵥ r) = 0 := by
      rw [Matrix.mulVec_sub, hLz, hLL, sub_self]
    have hTu : (z - limitMatrix P *ᵥ r) - P *ᵥ (z - limitMatrix P *ᵥ r)
        = r - limitMatrix P *ᵥ r := by
      have e := hAv (z - limitMatrix P *ᵥ r)
      rw [hLu, add_zero, Matrix.mulVec_sub, hz, hAL] at e
      exact e.symm
    obtain ⟨y, hy⟩ := h4 (z - limitMatrix P *ᵥ r)
    rw [hLu, sub_zero] at hy
    refine ⟨limitMatrix P *ᵥ r, z - limitMatrix P *ᵥ r, -y, ?_, ?_, ?_⟩
    · rw [one_sub_mulVec, h1, sub_self]
    · rw [one_sub_mulVec, hTu]; abel
    · rw [one_sub_mulVec, Matrix.mulVec_neg, hy]; abel
  · intro φ u w hφ hu hw
    rw [one_sub_mulVec, sub_eq_zero] at hφ
    rw [one_sub_mulVec] at hu hw
    have hLφ : limitMatrix P *ᵥ φ = φ := h3 φ hφ.symm
    have hφr : φ = limitMatrix P *ᵥ r := by
      rw [← hu, Matrix.mulVec_add, h2, add_zero, hLφ]
    have hLu : limitMatrix P *ᵥ u = 0 := by
      have := congrArg (fun v => limitMatrix P *ᵥ v) hw
      simpa only [Matrix.mulVec_add, h2, add_zero, Matrix.mulVec_zero] using this
    refine ⟨hφr, ?_⟩
    have hAu : (1 - P + limitMatrix P) *ᵥ (u + limitMatrix P *ᵥ r) = r := by
      rw [Matrix.mulVec_add, hAL, hAv, hLu, add_zero, ← hφr]
      rw [← hu]; abel
    have hz := hinvA (u + limitMatrix P *ᵥ r)
    rw [hAu] at hz
    rw [hD, hz, add_sub_cancel_right]

end K441

open MarkovDecisionProcesses KallenbergLP.AverageLP Matrix Filter Topology
  BlackwellDiscreteDP.NearOne in
lemma K441_totalReward_eq {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (N : ℕ) :
    ∀ t h s, totalReward (stationaryPolicy M f hf) N t h s
      = (∑ k ∈ Finset.range N, Pf M f ^ k *ᵥ rf M f) s := by
  induction N with
  | zero => intro t h s; simp [totalReward]
  | succ N ih =>
    intro t h s
    have hstep : ∑ k ∈ Finset.range (N + 1), Pf M f ^ k *ᵥ rf M f
        = rf M f + Pf M f *ᵥ ∑ k ∈ Finset.range N, Pf M f ^ k *ᵥ rf M f := by
      rw [Finset.sum_range_succ', Matrix.mulVec_sum]
      simp only [pow_succ', ← Matrix.mulVec_mulVec, pow_zero, Matrix.one_mulVec]
      abel
    rw [hstep]
    simp only [totalReward, ih]
    simp only [stationaryPolicy, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (M.admissible s) (f s), if_pos (hf s)]
    simp [Matrix.mulVec, dotProduct, rf, Pf]

open MarkovDecisionProcesses KallenbergLP.AverageLP Matrix Filter Topology
  BlackwellDiscreteDP.NearOne in
lemma K441_gainInf_eq {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (s : S) :
    gainInf (stationaryPolicy M f hf) s = (limitMatrix (Pf M f) *ᵥ rf M f) s := by
  have hnn : ∀ i j, 0 ≤ Pf M f i j := fun i j => by
    simp only [Pf, Matrix.of_apply]; exact M.trans_nonneg _ _ _
  have hs : ∀ i, ∑ j, Pf M f i j = 1 := fun i => by
    simp only [Pf, Matrix.of_apply]; exact M.trans_sum _ _
  obtain ⟨hT, -⟩ := K441.limit_facts (Pf M f) hnn hs
  have hv : Tendsto (fun N => cesaroMean (Pf M f) N *ᵥ rf M f) atTop
      (𝓝 (limitMatrix (Pf M f) *ᵥ rf M f)) :=
    (((continuous_id.matrix_mulVec continuous_const).tendsto _)).comp hT
  have hs' := tendsto_pi_nhds.mp hv s
  unfold gainInf
  apply Tendsto.liminf_eq
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine hs'.congr (fun N => ?_)
  rw [K441_totalReward_eq]
  unfold cesaroMean
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [div_eq_inv_mul]

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter KallenbergLP.AverageLP in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    (∃ φ u w : S → ℝ, (1 - Pf M f) *ᵥ φ = 0 ∧ φ + (1 - Pf M f) *ᵥ u = rf M f ∧
        u + (1 - Pf M f) *ᵥ w = 0) ∧
    ∀ φ u w : S → ℝ, (1 - Pf M f) *ᵥ φ = 0 → φ + (1 - Pf M f) *ᵥ u = rf M f →
        u + (1 - Pf M f) *ᵥ w = 0 →
      φ = (fun i => gainInf (stationaryPolicy M f hf) i) ∧ u = uPure M f := by
  have hnn : ∀ i j, 0 ≤ Pf M f i j := fun i j => by
    simp only [Pf, Matrix.of_apply]; exact M.trans_nonneg _ _ _
  have hs : ∀ i, ∑ j, Pf M f i j = 1 := fun i => by
    simp only [Pf, Matrix.of_apply]; exact M.trans_sum _ _
  obtain ⟨hex, huniq⟩ := K441.system_facts (Pf M f) hnn hs (rf M f)
  refine ⟨hex, fun φ u w e1 e2 e3 => ?_⟩
  obtain ⟨g1, g2⟩ := huniq φ u w e1 e2 e3
  refine ⟨?_, ?_⟩
  · rw [g1]; funext i; exact (K441_gainInf_eq M f hf i).symm
  · rw [g2]; rfl
