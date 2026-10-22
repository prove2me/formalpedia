-- Prove2me | solution 1 for NatureSLT.IllPosed.tikhonov_convergence_hilbert
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:04:32.573011+00:00
-- url     : https://prove2.me/submissions/02bf9ea6-c29e-41bd-9d71-8c6dbac868eb

import Mathlib
import Definitions.Def_NatureSLT_IllPosed_tikhonovFunctional
open NatureSLT.IllPosed
open Filter Topology
open scoped InnerProductSpace

theorem g70slt_dense {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (A : E₁ →L[ℝ] E₂) (hA : Function.Injective A) (f : E₁) :
    f ∈ closure ((Submodule.span ℝ (Set.range fun φ : StrongDual ℝ E₂ =>
      (InnerProductSpace.toDual ℝ E₁).symm (φ.comp A)) : Submodule ℝ E₁) : Set E₁) := by
  set K := Submodule.span ℝ (Set.range fun φ : StrongDual ℝ E₂ =>
      (InnerProductSpace.toDual ℝ E₁).symm (φ.comp A))
  have hK : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]; intro v hv
    apply hA; rw [map_zero]
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ); intro φ
    have := Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self φ)) hv
    rwa [InnerProductSpace.toDual_symm_apply] at this
  have : K.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hK, Submodule.bot_orthogonal_eq_top]
  rw [← Submodule.topologicalClosure_coe, this]; trivial

theorem g70slt_weak {E₁ ι : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    {l : Filter ι} (x : ι → E₁) (C : ℝ) (hb : ∀ᶠ i in l, ‖x i‖ ≤ C) (S : Set E₁)
    (hD : ∀ u ∈ S, Tendsto (fun i => ⟪x i, u⟫_ℝ) l (𝓝 0)) (f : E₁) (hf : f ∈ closure S) :
    Tendsto (fun i => ⟪x i, f⟫_ℝ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro ε hε
  have hc : 0 < ε / (2 * (|C| + 1)) := by positivity
  obtain ⟨v, hv, hd⟩ := Metric.mem_closure_iff.mp hf _ hc
  filter_upwards [hb, Metric.tendsto_nhds.mp (hD v hv) (ε/2) (half_pos hε)] with i h1 h2
  rw [Real.dist_eq, sub_zero] at h2 ⊢
  have e : ⟪x i, f⟫_ℝ = ⟪x i, v⟫_ℝ + ⟪x i, f - v⟫_ℝ := by rw [inner_sub_right]; ring
  have h3 : |⟪x i, f - v⟫_ℝ| ≤ ‖x i‖ * ‖f - v‖ := abs_real_inner_le_norm _ _
  have h4 : ‖f - v‖ < ε / (2 * (|C| + 1)) := by rwa [dist_eq_norm] at hd
  have h5 : ‖x i‖ * ‖f - v‖ ≤ (|C| + 1) * (ε / (2 * (|C| + 1))) := by
    apply mul_le_mul (by linarith [le_abs_self C]) h4.le (norm_nonneg _) (by positivity)
  have h6 : (|C| + 1) * (ε / (2 * (|C| + 1))) = ε / 2 := by field_simp
  rw [e]
  calc |⟪x i, v⟫_ℝ + ⟪x i, f - v⟫_ℝ| ≤ |⟪x i, v⟫_ℝ| + |⟪x i, f - v⟫_ℝ| := abs_add_le _ _
    _ < ε := by linarith


open Filter Topology
open scoped ENNReal

/-- Theorem 7.2 (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §7.6.1, p. 238;
Tikhonov and Arsenin 1977). `E₁` is a real Hilbert space and `Ω(f) = ‖f‖²`. The operator
`A : E₁ → E₂` is linear, continuous and one-to-one (the standing setting of pp. 233–234; linearity
needs `E₂` to be a real normed space), `f` solves `A f = F`, and for every `δ > 0` an
approximation `F_δ` with `ρ_{E₂}(F, F_δ) ≤ δ` is given. If `γ(δ) > 0` satisfies (7.18),
`γ(δ) → 0` and `δ²/γ(δ) → 0` as `δ → 0`, then any choice of minimizers `f_δ` of
`W*_T(g) = ρ²_{E₂}(A g, F_δ) + γ(δ) ‖g‖²` (7.19) converges to `f` in the norm of `E₁`
as `δ → 0⁺`. -/
theorem solution {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (A : E₁ →L[ℝ] E₂) (hAinj : Function.Injective A)
    (F : E₂) (f : E₁) (hf : A f = F)
    (Fδ : ℝ → E₂) (hFδ : ∀ δ : ℝ, 0 < δ → dist F (Fδ δ) ≤ δ)
    (γ : ℝ → ℝ) (hγpos : ∀ δ : ℝ, 0 < δ → 0 < γ δ)
    (hγ : Tendsto γ (𝓝[>] 0) (𝓝 0))
    (hratio : Tendsto (fun δ : ℝ => δ ^ 2 / γ δ) (𝓝[>] 0) (𝓝 0))
    (fδ : ℝ → E₁)
    (hmin : ∀ δ : ℝ, 0 < δ → ∀ g : E₁,
      tikhonovFunctional A (fun h : E₁ => ENNReal.ofReal (‖h‖ ^ 2)) (γ δ) (Fδ δ) (fδ δ) ≤
        tikhonovFunctional A (fun h : E₁ => ENNReal.ofReal (‖h‖ ^ 2)) (γ δ) (Fδ δ) g) :
    Tendsto fδ (𝓝[>] 0) (𝓝 f) := by
  have hγδ : ∀ δ : ℝ, 0 < δ → dist (A (fδ δ)) (Fδ δ) ^ 2 + γ δ * ‖fδ δ‖ ^ 2 ≤
      δ ^ 2 + γ δ * ‖f‖ ^ 2 := by
    intro δ hδ
    have h := hmin δ hδ f
    simp only [tikhonovFunctional] at h
    have hγ0 := (hγpos δ hδ).le
    rw [← ENNReal.ofReal_mul hγ0, ← ENNReal.ofReal_mul hγ0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    have h2 : dist (A f) (Fδ δ) ^ 2 ≤ δ ^ 2 := by
      rw [hf]; exact pow_le_pow_left₀ dist_nonneg (hFδ δ hδ) 2
    linarith
  have hδ0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hpos : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  have hAF : Tendsto (fun δ => A (fδ δ)) (𝓝[>] 0) (𝓝 F) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hb : Tendsto (fun δ => Real.sqrt (δ ^ 2 + γ δ * ‖f‖ ^ 2) + δ) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun δ => δ ^ 2 + γ δ * ‖f‖ ^ 2) (𝓝[>] 0)
          (𝓝 ((0:ℝ) ^ 2 + 0 * ‖f‖ ^ 2)) := (hδ0.pow 2).add (hγ.mul_const _)
      have h2 := (h1.sqrt).add hδ0
      simpa using h2
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hb
    filter_upwards [hpos] with δ hδ
    have h1 := hγδ δ hδ
    have h3 : dist (A (fδ δ)) (Fδ δ) ≤ Real.sqrt (δ ^ 2 + γ δ * ‖f‖ ^ 2) :=
      le_trans (le_abs_self _) (Real.abs_le_sqrt (by nlinarith [hγpos δ hδ, sq_nonneg ‖fδ δ‖]))
    calc dist (A (fδ δ)) F ≤ dist (A (fδ δ)) (Fδ δ) + dist (Fδ δ) F := dist_triangle _ _ _
      _ ≤ _ := add_le_add h3 (by rw [dist_comm]; exact hFδ δ hδ)
  have hratio1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ ^ 2 / γ δ < 1 := hratio (Iio_mem_nhds one_pos)
  have hnormsq : ∀ δ : ℝ, 0 < δ → ‖fδ δ‖ ^ 2 ≤ δ ^ 2 / γ δ + ‖f‖ ^ 2 := by
    intro δ hδ
    have := hγδ δ hδ
    have hg := hγpos δ hδ
    rw [div_add' _ _ _ hg.ne', le_div_iff₀ hg]
    nlinarith [sq_nonneg (dist (A (fδ δ)) (Fδ δ))]
  have hbdd : ∀ᶠ δ in 𝓝[>] (0:ℝ), ‖fδ δ - f‖ ≤ Real.sqrt (1 + ‖f‖ ^ 2) + ‖f‖ := by
    filter_upwards [hpos, hratio1] with δ hδ h1
    have : ‖fδ δ‖ ≤ Real.sqrt (1 + ‖f‖ ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg (fδ δ))]
      exact Real.sqrt_le_sqrt (by linarith [hnormsq δ hδ])
    calc ‖fδ δ - f‖ ≤ ‖fδ δ‖ + ‖f‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hweak : Tendsto (fun δ => ⟪fδ δ - f, f⟫_ℝ) (𝓝[>] 0) (𝓝 0) := by
    refine g70slt_weak (fun δ => fδ δ - f) _ hbdd _ ?_ f (g70slt_dense A hAinj f)
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨φ, rfl⟩ := hu
      have e : ∀ δ, ⟪fδ δ - f, (InnerProductSpace.toDual ℝ E₁).symm (φ.comp A)⟫_ℝ
          = φ (A (fδ δ) - F) := by
        intro δ
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, ← hf]
        simp
      simp only [e]
      have := (φ.continuous.tendsto _).comp (hAF.sub_const F)
      simpa [Function.comp_def] using this
    | zero => simp
    | add u v _ _ hu hv =>
      simp only [inner_add_right]; simpa using hu.add hv
    | smul a u _ hu =>
      simp only [real_inner_smul_right]; simpa using hu.const_mul a
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ δ : ℝ, 0 < δ → ‖fδ δ - f‖ ^ 2 ≤ δ ^ 2 / γ δ - 2 * ⟪fδ δ - f, f⟫_ℝ := by
    intro δ hδ
    rw [@norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
    linarith [hnormsq δ hδ]
  have hlim : Tendsto (fun δ => Real.sqrt (δ ^ 2 / γ δ - 2 * ⟪fδ δ - f, f⟫_ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := (hratio.sub (hweak.const_mul 2)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hpos] with δ hδ
  rw [← Real.sqrt_sq (norm_nonneg (fδ δ - f))]
  exact Real.sqrt_le_sqrt (hsq δ hδ)

