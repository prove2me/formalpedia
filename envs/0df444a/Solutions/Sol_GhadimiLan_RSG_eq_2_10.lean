-- Prove2me | solution 1 for GhadimiLan.RSG.eq_2_10
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T23:06:03.736988+00:00
-- url     : https://prove2.me/submissions/2e0288ca-8ce6-48c3-9d18-936ffb8b7f6a

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Theorems.Thm_GhadimiLan_RSG_iterate_measurable
import Theorems.Thm_GhadimiLan_RSG_grad_sq_integrable
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

/-- Pull-out property for inner products on `ℝⁿ`, proved coordinatewise. -/
private theorem condExp_inner_left {n : ℕ} {Ω : Type*} {m m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {a b : Ω → E n}
    (ha : StronglyMeasurable[m] a) (ha2 : MemLp a 2 μ) (hb2 : MemLp b 2 μ) :
    μ[fun ω => ⟪a ω, b ω⟫_ℝ | m] =ᵐ[μ] fun ω => ⟪a ω, (μ[b | m]) ω⟫_ℝ := by
  have hb_int : Integrable b μ := hb2.integrable one_le_two
  have hai : ∀ i : Fin n, StronglyMeasurable[m] (fun ω => a ω i) := fun i =>
    (EuclideanSpace.proj i).continuous.comp_stronglyMeasurable ha
  have hai2 : ∀ i : Fin n, MemLp (fun ω => a ω i) 2 μ := fun i => by
    have h := ha2.continuousLinearMap_comp (EuclideanSpace.proj i : E n →L[ℝ] ℝ)
    exact h
  have hbi2 : ∀ i : Fin n, MemLp (fun ω => b ω i) 2 μ := fun i => by
    have h := hb2.continuousLinearMap_comp (EuclideanSpace.proj i : E n →L[ℝ] ℝ)
    exact h
  have hbi_int : ∀ i : Fin n, Integrable (fun ω => b ω i) μ := fun i =>
    (hbi2 i).integrable one_le_two
  have habi_int : ∀ i : Fin n, Integrable ((fun ω => a ω i) * (fun ω => b ω i)) μ := fun i =>
    (hai2 i).integrable_mul (hbi2 i)
  have hsum : (fun ω => ⟪a ω, b ω⟫_ℝ) = ∑ i : Fin n, (fun ω => a ω i) * (fun ω => b ω i) := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, mul_comm]
  have hi : ∀ i : Fin n, μ[(fun ω => a ω i) * (fun ω => b ω i) | m] =ᵐ[μ]
      fun ω => a ω i * (μ[b | m]) ω i := by
    intro i
    refine (condExp_mul_of_stronglyMeasurable_left (hai i) (habi_int i) (hbi_int i)).trans ?_
    have hc : μ[fun ω => b ω i | m] =ᵐ[μ] fun ω => (μ[b | m]) ω i :=
      (ContinuousLinearMap.comp_condExp_comm (m := m) hb_int (EuclideanSpace.proj i)).symm
    filter_upwards [hc] with ω hω
    simp only [Pi.mul_apply]
    rw [hω]
  rw [hsum]
  refine (condExp_finsetSum (fun i _ => habi_int i) m).trans ?_
  have hall : ∀ᵐ ω ∂μ, ∀ i : Fin n,
      (μ[(fun ω => a ω i) * (fun ω => b ω i) | m]) ω = a ω i * (μ[b | m]) ω i :=
    ae_all_iff.2 hi
  filter_upwards [hall] with ω hω
  simp only [Finset.sum_apply, hω, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

theorem solution {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ) μ ∧
    μ[fun ω => ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ | ℱ (k - 1)] =ᵐ[μ] 0 := by
  -- `g = ∇f` is `L`-Lipschitz, hence continuous, hence Borel measurable.
  have hgL : LipschitzWith ⟨L, hf.1⟩ g := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact hf.2.2 p q
  have hg_meas : Measurable g := hgL.continuous.measurable
  have hm : ℱ (k - 1) ≤ ‹MeasurableSpace Ω› := ℱ.le (k - 1)
  -- `x k` is `ℱ (k-1)`-measurable (platform theorem `iterate_measurable`).
  have hxk : Measurable[ℱ (k - 1)] (x k) :=
    GhadimiLan.RSG.iterate_measurable G hG ℱ ξ hA1.adapted γ x1 x hx k hk
  -- `a := ∇f(x_k)` is `ℱ (k-1)`-measurable, hence `ℱ (k-1)`-strongly measurable and measurable.
  have ha_m : Measurable[ℱ (k - 1)] (fun ω => g (x k ω)) := hg_meas.comp hxk
  have ha_sm : StronglyMeasurable[ℱ (k - 1)] (fun ω => g (x k ω)) := ha_m.stronglyMeasurable
  have ha_meas : Measurable (fun ω => g (x k ω)) := ha_m.mono hm le_rfl
  have hxk_meas : Measurable (x k) := hxk.mono hm le_rfl
  have hξk_meas : Measurable (ξ k) := (hA1.adapted k hk).mono (ℱ.le k) le_rfl
  -- `b := G(x_k, ξ_k)` is measurable, so is the noise `δ_k = b - a`.
  have hb_meas : Measurable (fun ω => G (x k ω) (ξ k ω)) :=
    hG.comp (hxk_meas.prodMk hξk_meas)
  have hδ_meas : Measurable (fun ω => rsgNoise G g ξ x k ω) := hb_meas.sub ha_meas
  -- Square integrability: `a ∈ L²` (platform theorem `grad_sq_integrable`), `δ_k ∈ L²` (A1).
  have ha2 : MemLp (fun ω => g (x k ω)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm ha_meas.aestronglyMeasurable).2
      (GhadimiLan.RSG.grad_sq_integrable f g L hf G hG μ ℱ ξ σ γ x1 x hx hA1 k hk)
  have hδ2 : MemLp (fun ω => rsgNoise G g ξ x k ω) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hδ_meas.aestronglyMeasurable).2
      (hA1.integrable_sq_error k hk)
  -- The inner product of two `L²` functions is integrable: `|⟪u, v⟫| ≤ ‖u‖‖v‖ ≤ ‖u‖² + ‖v‖²`.
  have hinner_int : ∀ (u v : Ω → E n), Measurable u → Measurable v →
      MemLp u 2 μ → MemLp v 2 μ → Integrable (fun ω => ⟪u ω, v ω⟫_ℝ) μ := by
    intro u v hu hv hu2 hv2
    have hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu2
    have hv_sq : Integrable (fun ω => ‖v ω‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv2
    refine (hu_sq.add hv_sq).mono' (hu.inner hv).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    show |⟪u ω, v ω⟫_ℝ| ≤ ‖u ω‖ ^ 2 + ‖v ω‖ ^ 2
    have h1 := abs_real_inner_le_norm (u ω) (v ω)
    have h2 := two_mul_le_add_sq ‖u ω‖ ‖v ω‖
    have h3 := mul_nonneg (norm_nonneg (u ω)) (norm_nonneg (v ω))
    linarith
  -- `E[δ_k | ℱ (k-1)] = 0`: linearity, unbiasedness (1.2), and `a` is `ℱ (k-1)`-measurable.
  have ha_int : Integrable (fun ω => g (x k ω)) μ := ha2.integrable one_le_two
  have hb_int : Integrable (fun ω => G (x k ω) (ξ k ω)) μ := hA1.integrable_oracle k hk
  have hδ_eq : (fun ω => rsgNoise G g ξ x k ω) =
      (fun ω => G (x k ω) (ξ k ω)) - (fun ω => g (x k ω)) := by
    funext ω
    simp only [Pi.sub_apply, rsgNoise]
  have hδ_condExp : μ[fun ω => rsgNoise G g ξ x k ω | ℱ (k - 1)] =ᵐ[μ] 0 := by
    rw [hδ_eq]
    refine (condExp_sub hb_int ha_int (ℱ (k - 1))).trans ?_
    have h3 := hA1.unbiased k hk
    have h4 : μ[fun ω => g (x k ω) | ℱ (k - 1)] = fun ω => g (x k ω) :=
      condExp_of_stronglyMeasurable hm ha_sm ha_int
    rw [h4]
    filter_upwards [h3] with ω hω
    simp only [Pi.sub_apply, Pi.zero_apply, hω, sub_self]
  refine ⟨hinner_int _ _ ha_meas hδ_meas ha2 hδ2, ?_⟩
  -- Pull-out: `E[⟪a, δ_k⟫ | ℱ (k-1)] = ⟪a, E[δ_k | ℱ (k-1)]⟫ = ⟪a, 0⟫ = 0`.
  refine (condExp_inner_left ha_sm ha2 hδ2).trans ?_
  filter_upwards [hδ_condExp] with ω hω
  simp only [Pi.zero_apply] at hω ⊢
  rw [hω, inner_zero_right]
