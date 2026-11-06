-- Prove2me | solution 1 for KleywegtSAA.ValueCLT.joint_clt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:18:57.082534+00:00
-- url     : https://prove2.me/submissions/f7ac386d-f911-4fa3-98f2-faade2250373

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open KleywegtSAA.ValueCLT

open Classical in
theorem solution
    {X : Type*} (S : Finset X)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (T : Finset X) (hT : T ⊆ S)
    (hT2 : ∀ x ∈ T, MemLp (fun ω => G x (W 0 ω)) 2 P) :
    ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
      (Y : Ω' → EuclideanSpace ℝ T),
      HasLaw Y (multivariateGaussian 0 (covMat G P W T)) Q →
      TendstoInDistribution (fun (N : ℕ) ω => scaledDev G P W T N ω) atTop Y (fun _ => P) Q := by
  intro Ω' _ Q _ Y hY
  have hGT : ∀ x : T, Measurable (G x) := fun x => hG x (hT x.2)
  have hL2 : ∀ x : T, MemLp (fun ω => G x (W 0 ω)) 2 P := fun x => hT2 x x.2
  -- variance of a linear combination
  have hvar : ∀ t : T → ℝ, Var[fun ω => ∑ x, t x * G x (W 0 ω); P] =
      ∑ x, t x * ∑ y, covMat G P W T x y * t y := by
    intro t
    rw [variance_fun_sum (fun x => (hL2 x).const_mul (t x))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [covariance_const_mul_left, covariance_const_mul_right]
    simp only [covMat]
    ring
  have hPSD : (covMat G P W T).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
    · ext x y
      simp [covMat, covariance_comm]
    · have := variance_nonneg (fun ω => ∑ x, v x * G x (W 0 ω)) P
      rw [hvar v] at this
      simpa [dotProduct, Matrix.mulVec] using this
  have hZm : ∀ N : ℕ, Measurable (fun ω => scaledDev G P W T N ω) := by
    intro N
    unfold scaledDev
    refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
    refine measurable_pi_lambda _ (fun x => ?_)
    unfold KleywegtSAA.ExpRate.sampleObj
    refine Measurable.const_mul (Measurable.sub_const (Measurable.const_mul ?_ _) _) _
    exact Finset.measurable_sum _ (fun n _ => (hGT x).comp (hWm n))
  refine ⟨fun N => (hZm N).aemeasurable, hY.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 (fun t => ?_)
  simp only [ProbabilityMeasure.coe_mk]
  rw [hY.map_eq, charFun_multivariateGaussian hPSD]
  -- the scalar sequence `ξ_n = ∑_x t_x G(x, W_n)`
  let φ : 𝒲 → ℝ := fun w => ∑ x, t x * G x w
  have hφ : Measurable φ :=
    Finset.measurable_sum _ (fun x _ => (hGT x).const_mul _)
  let ξ : ℕ → Ω → ℝ := fun n => φ ∘ W n
  have hξind : iIndepFun ξ P := hind.comp (fun _ => φ) (fun _ => hφ)
  have hξid : ∀ n, IdentDistrib (ξ n) (ξ 0) P P := fun n => (hid n).comp hφ
  have hξL2 : MemLp (ξ 0) 2 P := by
    have : ξ 0 = fun ω => ∑ x, t x * G x (W 0 ω) := rfl
    rw [this]
    exact memLp_finsetSum _ (fun x _ => (hL2 x).const_mul (t x))
  set v := Var[ξ 0; P] with hv
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (Y := id)
    (P' := gaussianReal 0 v.toNNReal) HasLaw.id hξL2 hξind hξid
  have hch := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hclt.tendsto) 1
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id, charFun_gaussianReal] at hch
  have hmean : P[ξ 0] = ∑ x, t x * KleywegtSAA.ExpRate.trueObj G P W x := by
    have : ξ 0 = fun ω => ∑ x, t x * G x (W 0 ω) := rfl
    rw [this, integral_finsetSum _ (fun x _ => ((hL2 x).integrable one_le_two).const_mul (t x))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [integral_const_mul]
    rfl
  have hinner : ∀ (n : ℕ) (ω : Ω), inner ℝ (scaledDev G P W T n ω) t =
      (√n)⁻¹ * (∑ k ∈ Finset.range n, ξ k ω - n * P[ξ 0]) := by
    intro n ω
    rw [hmean]
    simp only [PiLp.inner_apply, scaledDev, ξ, φ, Function.comp_apply,
      KleywegtSAA.ExpRate.sampleObj]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [Finset.sum_comm (s := Finset.range n)]
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum (s := Finset.univ) (a := (n : ℝ)), ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
      have hs0 : √(n : ℝ) ≠ 0 := by positivity
      have key : ∀ (s A g c : ℝ), s ≠ 0 →
          s * (1 / (s * s) * A - g) * c = s⁻¹ * (c * A - (s * s) * (c * g)) := by
        intro s A g c hs; field_simp
      have := key (√(n : ℝ)) (∑ k ∈ Finset.range n, G x (W k ω))
        (KleywegtSAA.ExpRate.trueObj G P W x) (t x) hs0
      rw [hs] at this
      rw [← this]
      ring
  have hlim : Complex.exp (↑(inner ℝ t 0) * Complex.I - ↑(t.ofLp ⬝ᵥ (covMat G P W T).mulVec t.ofLp) / 2)
      = Complex.exp (↑(1:ℝ) * ↑(0:ℝ) * Complex.I - ↑(v.toNNReal : ℝ) * ↑(1:ℝ) ^ 2 / 2) := by
    rw [Real.coe_toNNReal _ (variance_nonneg _ _)]
    have : ξ 0 = fun ω => ∑ x, t x * G x (W 0 ω) := rfl
    rw [this, hvar]
    simp [dotProduct, Matrix.mulVec]
  rw [hlim]
  convert hch using 2 with n
  rw [charFun_apply, charFun_apply, integral_map (hZm n).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop)), integral_map (by fun_prop)
      (Continuous.aestronglyMeasurable (by fun_prop))]
  congr 1
  funext ω
  rw [hinner]
  simp
