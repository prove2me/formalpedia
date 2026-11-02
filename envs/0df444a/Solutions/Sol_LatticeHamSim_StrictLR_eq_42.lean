-- Prove2me | solution 1 for LatticeHamSim.StrictLR.eq_42
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:51:51.408203+00:00
-- url     : https://prove2.me/submissions/f3fc15ba-58f5-4945-8b3d-70cba46e34cc

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
import Theorems.Thm_LatticeHamSim_StrictLR_eq_24
import Theorems.Thm_LatticeHamSim_StrictLR_eq_28
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Aux_LHS_42

open LatticeHamSim.CommLR LatticeHamSim.StrictLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

noncomputable local instance : NormedAlgebra ℚ (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

lemma comm_bound (P B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖P * B - B * P‖ ≤ 2 * ‖P‖ * ‖B‖ := by
  calc ‖P * B - B * P‖ ≤ ‖P * B‖ + ‖B * P‖ := norm_sub_le _ _
    _ ≤ ‖P‖ * ‖B‖ + ‖B‖ * ‖P‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖B‖ := by ring

lemma evolve_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (t : ℝ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖evolve (H h) t O‖ = ‖O‖ := by
  have hsa : star (H h) = H h := by
    unfold H
    rw [star_sum]
    exact Finset.sum_congr rfl (fun X _ => hherm X)
  have key : ∀ s : ℝ, NormedSpace.exp ((Complex.I * (s : ℂ)) • H h) ∈
      unitary (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
    intro s
    have hs : ((s : ℂ) • H h) ∈ selfAdjoint (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
    have := (selfAdjoint.expUnitary ⟨(s : ℂ) • H h, hs⟩).prop
    simp only [selfAdjoint.expUnitary_coe, smul_smul] at this
    exact this
  unfold evolve
  have hU := key t
  have hV := key (-t)
  rw [show (-(Complex.I * (t : ℂ))) = Complex.I * ((-t : ℝ) : ℂ) by push_cast; ring]
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

lemma supportedOn_smul (X : Finset Λ) (c : ℂ) (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : SupportedOn X A) : SupportedOn X (c • A) := by
  obtain ⟨m, hm⟩ := hA
  refine ⟨c • m, fun σ τ => ?_⟩
  simp only [Matrix.smul_apply, hm σ τ, smul_eq_mul, mul_ite, mul_zero]

lemma cb_bddAbove (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    BddAbove {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖} := by
  refine ⟨2 * ‖B‖, ?_⟩
  rintro r ⟨A, -, hA1, rfl⟩
  refine le_trans (comm_bound _ _) ?_
  rw [evolve_norm h hherm]
  nlinarith [norm_nonneg A, norm_nonneg B]

lemma cb_set_nonempty (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖}.Nonempty := by
  refine ⟨0, 0, ⟨0, fun σ τ => by simp⟩, by simp, ?_⟩
  simp [evolve]

lemma db_le_norm_mul_cb (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, SupportedOn X (h X))
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) (s : ℝ) :
    DB h B Z s ≤ ‖h Z‖ * CB h B Z s := by
  unfold DB
  by_cases hZ0 : ‖h Z‖ = 0
  · have hZz : h Z = 0 := norm_eq_zero.mp hZ0
    simp [hZz, hZ0, evolve]
  · have hZpos : 0 < ‖h Z‖ := lt_of_le_of_ne (norm_nonneg (h Z)) (Ne.symm hZ0)
    set c : ℂ := ((‖h Z‖⁻¹ : ℝ) : ℂ)
    set A' : Matrix (Λ → Fin q) (Λ → Fin q) ℂ := c • h Z
    have hA'supp : SupportedOn Z A' := supportedOn_smul Z c (h Z) (hsupp Z)
    have hA'norm : ‖A'‖ ≤ 1 := by
      change ‖((‖h Z‖⁻¹ : ℝ) : ℂ) • h Z‖ ≤ 1
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hZpos)),
        inv_mul_cancel₀ hZ0]
    have hev : evolve (H h) s A' * B - B * evolve (H h) s A' =
        c • (evolve (H h) s (h Z) * B - B * evolve (H h) s (h Z)) := by
      unfold A' evolve
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have hmem : ‖h Z‖⁻¹ * ‖evolve (H h) s (h Z) * B - B * evolve (H h) s (h Z)‖ ∈
        {r : ℝ | ∃ M : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
          SupportedOn Z M ∧ ‖M‖ ≤ 1 ∧
          r = ‖evolve (H h) s M * B - B * evolve (H h) s M‖} := by
      refine ⟨A', hA'supp, hA'norm, ?_⟩
      rw [hev, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hZpos))]
    have hle : ‖h Z‖⁻¹ * ‖evolve (H h) s (h Z) * B - B * evolve (H h) s (h Z)‖ ≤ CB h B Z s :=
      le_csSup (cb_bddAbove h hherm B Z s) hmem
    calc ‖evolve (H h) s (h Z) * B - B * evolve (H h) s (h Z)‖
        = ‖h Z‖ * (‖h Z‖⁻¹ * ‖evolve (H h) s (h Z) * B - B * evolve (H h) s (h Z)‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hZ0, one_mul]
      _ ≤ ‖h Z‖ * CB h B Z s := mul_le_mul_of_nonneg_left hle (le_of_lt hZpos)

lemma continuous_exp_line (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (c : ℂ) :
    Continuous (fun s : ℝ => NormedSpace.exp ((c * (s : ℂ)) • J)) := by
  exact NormedSpace.exp_continuous.comp ((continuous_const.mul Complex.continuous_ofReal).smul continuous_const)

lemma continuous_evolve (J A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    Continuous (fun s : ℝ => evolve J s A) := by
  unfold evolve
  have h1 : Continuous (fun s : ℝ => NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) :=
    continuous_exp_line J Complex.I
  have h2 : Continuous (fun s : ℝ => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) := by
    have : (fun s : ℝ => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) =
        (fun s : ℝ => NormedSpace.exp (((-Complex.I) * (s : ℂ)) • J)) := by
      ext s; rw [neg_mul]
    rw [this]
    exact continuous_exp_line J (-Complex.I)
  exact (h1.mul continuous_const).mul h2

lemma continuous_DB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) :
    Continuous (fun s : ℝ => DB h B Z s) := by
  unfold DB
  have hev := continuous_evolve (H h) (h Z)
  exact ((hev.mul continuous_const).sub (continuous_const.mul hev)).norm

lemma cb_sub_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) (s₁ s₂ : ℝ) :
    CB h B Z s₁ - CB h B Z s₂ ≤
      2 * ‖B‖ * (‖NormedSpace.exp ((Complex.I * (s₁ : ℂ)) • H h) -
          NormedSpace.exp ((Complex.I * (s₂ : ℂ)) • H h)‖ *
        ‖NormedSpace.exp ((-(Complex.I * (s₁ : ℂ))) • H h)‖ +
        ‖NormedSpace.exp ((Complex.I * (s₂ : ℂ)) • H h)‖ *
        ‖NormedSpace.exp ((-(Complex.I * (s₁ : ℂ))) • H h) -
          NormedSpace.exp ((-(Complex.I * (s₂ : ℂ))) • H h)‖) := by
  set U : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((Complex.I * (s : ℂ)) • H h)
  set V : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H h)
  set M : ℝ := 2 * ‖B‖ * (‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖)
  rw [sub_le_iff_le_add]
  unfold CB
  refine csSup_le (cb_set_nonempty h B Z s₁) ?_
  rintro r ⟨A, hAsupp, hA1, rfl⟩
  have hmem2 : ‖evolve (H h) s₂ A * B - B * evolve (H h) s₂ A‖ ≤ CB h B Z s₂ := by
    refine le_csSup (cb_bddAbove h hherm B Z s₂) ⟨A, hAsupp, hA1, rfl⟩
  have hdiff : evolve (H h) s₁ A - evolve (H h) s₂ A =
      (U s₁ - U s₂) * A * V s₁ + U s₂ * A * (V s₁ - V s₂) := by
    unfold evolve U V
    noncomm_ring
  have hev_diff : ‖evolve (H h) s₁ A - evolve (H h) s₂ A‖ ≤
      ‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖ := by
    rw [hdiff]
    calc ‖(U s₁ - U s₂) * A * V s₁ + U s₂ * A * (V s₁ - V s₂)‖
        ≤ ‖(U s₁ - U s₂) * A * V s₁‖ + ‖U s₂ * A * (V s₁ - V s₂)‖ := norm_add_le _ _
      _ ≤ ‖(U s₁ - U s₂) * A‖ * ‖V s₁‖ + ‖U s₂ * A‖ * ‖V s₁ - V s₂‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (‖U s₁ - U s₂‖ * ‖A‖) * ‖V s₁‖ + (‖U s₂‖ * ‖A‖) * ‖V s₁ - V s₂‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖U s₁ - U s₂‖ * 1) * ‖V s₁‖ + (‖U s₂‖ * 1) * ‖V s₁ - V s₂‖ := by
          gcongr
      _ = ‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖ := by ring
  have hcomm_diff : ‖(evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
      (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A)‖ ≤ M := by
    have heq : (evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
        (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A) =
        (evolve (H h) s₁ A - evolve (H h) s₂ A) * B - B * (evolve (H h) s₁ A - evolve (H h) s₂ A) := by
      noncomm_ring
    rw [heq]
    calc ‖(evolve (H h) s₁ A - evolve (H h) s₂ A) * B - B * (evolve (H h) s₁ A - evolve (H h) s₂ A)‖
        ≤ 2 * ‖evolve (H h) s₁ A - evolve (H h) s₂ A‖ * ‖B‖ := comm_bound _ _
      _ ≤ 2 * (‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖) * ‖B‖ := by
          gcongr
      _ = M := by unfold M; ring
  calc ‖evolve (H h) s₁ A * B - B * evolve (H h) s₁ A‖
      ≤ ‖evolve (H h) s₂ A * B - B * evolve (H h) s₂ A‖ +
        ‖(evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
          (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A)‖ := norm_le_insert' _ _
    _ ≤ CB h B Z s₂ + M := add_le_add hmem2 hcomm_diff
    _ = M + CB h B Z s₂ := add_comm _ _

lemma continuous_CB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) :
    Continuous (fun s : ℝ => CB h B Z s) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set U : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((Complex.I * (s : ℂ)) • H h)
  set V : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H h)
  have hU : Continuous U := continuous_exp_line (H h) Complex.I
  have hV : Continuous V := by
    have : V = fun s : ℝ => NormedSpace.exp (((-Complex.I) * (s : ℂ)) • H h) := by
      ext s; unfold V; rw [neg_mul]
    rw [this]
    exact continuous_exp_line (H h) (-Complex.I)
  set F : ℝ → ℝ := fun s =>
    max (2 * ‖B‖ * (‖U s - U s₀‖ * ‖V s‖ + ‖U s₀‖ * ‖V s - V s₀‖))
        (2 * ‖B‖ * (‖U s₀ - U s‖ * ‖V s₀‖ + ‖U s‖ * ‖V s₀ - V s‖))
  have hF_cont : Continuous F := by
    unfold F
    refine Continuous.max ?_ ?_
    · exact continuous_const.mul (((hU.sub continuous_const).norm.mul hV.norm).add
        (continuous_const.mul (hV.sub continuous_const).norm))
    · exact continuous_const.mul (((continuous_const.sub hU).norm.mul continuous_const).add
        (hU.norm.mul (continuous_const.sub hV).norm))
  have hF0 : F s₀ = 0 := by
    unfold F
    simp
  have hFtend : Filter.Tendsto F (nhds s₀) (nhds 0) := by
    rw [← hF0]
    exact hF_cont.continuousAt
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hFtend
  rw [Real.norm_eq_abs, abs_le]
  have h1 : CB h B Z s₀ - CB h B Z s ≤ F s :=
    (cb_sub_le h hherm B Z s₀ s).trans (le_max_right _ _)
  have h2 : CB h B Z s - CB h B Z s₀ ≤ F s :=
    (cb_sub_le h hherm B Z s s₀).trans (le_max_left _ _)
  constructor <;> linarith

end Aux_LHS_42

open LatticeHamSim.CommLR LatticeHamSim.StrictLR Aux_LHS_42 in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    LatticeHamSim.CommLR.CB h B X t ≤ LatticeHamSim.CommLR.CB h B X 0 +
      2 * ∑ Z ∈ Finset.univ.filter (fun Z => LatticeHamSim.CommLR.meets X Z),
        ‖h Z‖ * ∫ s in (0 : ℝ)..t, LatticeHamSim.CommLR.CB h B Z s := by
  have h24 := eq_24 h hherm hsupp B X t ht
  have hfilter : Finset.univ.filter (fun Z => meets Z X) =
      Finset.univ.filter (fun Z => meets X Z) := by
    refine Finset.filter_congr (fun Z _ => ?_)
    simp only [meets, Finset.inter_comm]
  rw [hfilter] at h24
  refine h24.trans ?_
  rw [Finset.mul_sum]
  refine add_le_add le_rfl (Finset.sum_le_sum (fun Z _ => ?_))
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on ht
    ((continuous_DB h B Z).intervalIntegrable 0 t)
    ((continuous_const.mul (continuous_CB h hherm B Z)).intervalIntegrable 0 t)
    (fun s _ => db_le_norm_mul_cb h hherm hsupp B Z s)
