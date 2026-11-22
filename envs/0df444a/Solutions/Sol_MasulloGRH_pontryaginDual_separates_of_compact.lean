-- Prove2me | solution 1 for MasulloGRH.pontryaginDual_separates_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:08:51.318979+00:00
-- url     : https://prove2.me/submissions/bd820b72-8aa7-43b3-8cef-319eac3b1b8e

import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false

open MeasureTheory Topology Filter ComplexConjugate
open scoped BoundedContinuousFunction

set_option linter.unusedSectionVars false

namespace MasulloGRHCompactCharAux

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem eventually_translate_close (φ : G → ℂ) (hφ : Continuous φ) (x₀ : G) (ε : ℝ)
    (hε : 0 < ε) : ∀ᶠ x in 𝓝 x₀, ∀ y : G, ‖φ (x * y) - φ (x₀ * y)‖ < ε := by
  have key := (isCompact_univ (X := G)).eventually_forall_of_forall_eventually
    (P := fun x y => ‖φ (x * y) - φ (x₀ * y)‖ < ε) (x₀ := x₀) ?_
  · filter_upwards [key] with x hx y using hx y (Set.mem_univ y)
  intro y _
  have h1 : Continuous (fun p : G × G => φ (p.1 * p.2)) := hφ.comp (by fun_prop)
  have h2 : Continuous (fun p : G × G => φ (x₀ * p.2)) := hφ.comp (by fun_prop)
  have e1 := Metric.tendsto_nhds.mp (h1.tendsto (x₀, y)) (ε / 2) (half_pos hε)
  have e2 := Metric.tendsto_nhds.mp (h2.tendsto (x₀, y)) (ε / 2) (half_pos hε)
  filter_upwards [e1, e2] with p hp1 hp2
  simp only [dist_eq_norm] at hp1 hp2
  calc ‖φ (p.1 * p.2) - φ (x₀ * p.2)‖
      = ‖(φ (p.1 * p.2) - φ (x₀ * y)) - (φ (x₀ * p.2) - φ (x₀ * y))‖ := by ring_nf
    _ ≤ ‖φ (p.1 * p.2) - φ (x₀ * y)‖ + ‖φ (x₀ * p.2) - φ (x₀ * y)‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hp1 hp2
    _ = ε := add_halves ε

/-- The kernel row `y ↦ conj (φ (x * y⁻¹))` as a bounded continuous function. -/
noncomputable def row (φ : G → ℂ) (hφ : Continuous φ) (x : G) : G →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => conj (φ (x * y⁻¹)), Complex.continuous_conj.comp (hφ.comp (by fun_prop))⟩

theorem row_apply (φ : G → ℂ) (hφ : Continuous φ) (x y : G) :
    row φ hφ x y = conj (φ (x * y⁻¹)) := rfl

theorem continuous_row (φ : G → ℂ) (hφ : Continuous φ) : Continuous (row φ hφ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hev := eventually_translate_close φ hφ x₀ (ε / 2) (half_pos hε)
  filter_upwards [hev] with x hx'
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).mpr ?_)
    (half_lt_self hε)
  intro y
  rw [row_apply, row_apply, dist_eq_norm, ← map_sub, Complex.norm_conj]
  exact (hx' y⁻¹).le

section spectral
open Module End

/-- A commuting family of endomorphisms has a common eigenvector in any nonzero
finite-dimensional invariant subspace (over `ℂ`). -/
theorem exists_common_eigenvector {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (A : ι → End ℂ V) (hA : ∀ i j x, A i (A j x) = A j (A i x)) :
    ∀ (n : ℕ) (W : Submodule ℂ V) [FiniteDimensional ℂ W], finrank ℂ W = n → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, A i x ∈ W) →
      ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i v = c • v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ hn hW hinv
  by_cases hscal : ∀ i, ∃ c : ℂ, ∀ x ∈ W, A i x = c • x
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨v, hv, hv0, fun i => (hscal i).imp fun c hc => hc v hv⟩
  push Not at hscal
  obtain ⟨j, hj⟩ := hscal
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((A j).restrict (hinv j))
  obtain ⟨⟨u, huW⟩, hu, hu0⟩ := hc.exists_hasEigenvector
  have hu' : A j u = c • u := by
    rw [mem_eigenspace_iff] at hu
    simpa using congrArg Subtype.val hu
  set W' : Submodule ℂ V := W ⊓ eigenspace (A j) c
  have hW'le : W' ≤ W := inf_le_left
  have : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hW'le
  have hlt : W' < W := by
    refine lt_of_le_of_ne hW'le fun heq => ?_
    obtain ⟨x, hx, hne⟩ := hj c
    have : x ∈ W' := heq ▸ hx
    exact hne (mem_eigenspace_iff.mp this.2)
  have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨v, hv, hv0, hvc⟩ := ih (finrank ℂ W') (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt)
    W' rfl ((Submodule.ne_bot_iff _).mpr ⟨u, ⟨huW, mem_eigenspace_iff.mpr hu'⟩, hu0'⟩)
    (fun i x hx => ⟨hinv i x hx.1, by
      show A i x ∈ eigenspace (A j) c
      rw [mem_eigenspace_iff, hA, mem_eigenspace_iff.mp hx.2, map_smul]⟩)
  exact ⟨v, hW'le hv, hv0, hvc⟩

section HilbertSp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An inner-product-preserving operator which is not the identity on a nonzero
finite-dimensional invariant subspace has an eigenvector there with eigenvalue `≠ 1`. -/
theorem exists_eigenvector_ne_one (A : E →ₗᵢ[ℂ] E) (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (hinv : ∀ x ∈ W, A x ∈ W) (w₀ : E) (hw₀ : w₀ ∈ W) (hne : A w₀ ≠ w₀) :
    ∃ c : ℂ, c ≠ 1 ∧ ∃ u ∈ W, u ≠ 0 ∧ A u = c • u := by
  set K : Submodule ℂ E := W ⊓ eigenspace (A.toLinearMap) 1
  have hKW : K ≤ W := inf_le_left
  have : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le hKW
  set P : Submodule ℂ E := W ⊓ Kᗮ
  have hPW : P ≤ W := inf_le_left
  have : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le hPW
  -- `P` is nonzero
  set p := w₀ - K.starProjection w₀
  have hpP : p ∈ P := ⟨W.sub_mem hw₀ (hKW (K.starProjection_apply_mem w₀)),
    K.sub_starProjection_mem_orthogonal w₀⟩
  have hp0 : p ≠ 0 := by
    intro h
    have : K.starProjection w₀ = w₀ := (sub_eq_zero.mp h).symm
    rw [Submodule.starProjection_eq_self_iff] at this
    exact hne (by simpa using mem_eigenspace_iff.mp this.2)
  have hPinv : ∀ x ∈ P, A x ∈ P := by
    intro x hx
    refine ⟨hinv x hx.1, fun k hk => ?_⟩
    have hAk : A k = k := by simpa using mem_eigenspace_iff.mp hk.2
    rw [← hAk, LinearIsometry.inner_map_map]
    exact hx.2 k hk
  have : Nontrivial P := ⟨⟨⟨p, hpP⟩, 0, fun h => hp0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((A.toLinearMap).restrict hPinv)
  obtain ⟨⟨u, huP⟩, hu, hu0⟩ := hc.exists_hasEigenvector
  have hu' : A u = c • u := by
    rw [mem_eigenspace_iff] at hu
    simpa using congrArg Subtype.val hu
  have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
  refine ⟨c, fun hc1 => hu0' ?_, u, hPW huP, hu0', hu'⟩
  have huK : u ∈ K := ⟨hPW huP, mem_eigenspace_iff.mpr (by simpa [hc1] using hu')⟩
  have := huP.2 u huK
  exact inner_self_eq_zero.mp this

variable [CompleteSpace E]

/-- Abstract spectral lemma: a compact self-adjoint operator commuting with a commuting
family of isometries, with `U g ∘ T ≠ T`, has a joint eigenvector in a nonzero eigenspace on
which `U g` acts nontrivially. -/
theorem exists_joint_eigenvector {ι : Type*} (T : E →L[ℂ] E) (hTc : IsCompactOperator T)
    (hTs : (T : E →ₗ[ℂ] E).IsSymmetric) (U : ι → E →ₗᵢ[ℂ] E)
    (hUU : ∀ i j x, U i (U j x) = U j (U i x)) (hTU : ∀ i x, T (U i x) = U i (T x))
    (g : ι) (hg : ∃ v, U g (T v) ≠ T v) :
    ∃ l : ℂ, l ≠ 0 ∧ ∃ w : E, w ≠ 0 ∧ T w = l • w ∧ (∀ i, ∃ c : ℂ, U i w = c • w) ∧
      U g w ≠ w := by
  -- Step 1: some nonzero eigenspace on which `U g` is not the identity
  have step1 : ∃ l : ℂ, l ≠ 0 ∧ ∃ w ∈ eigenspace (T : E →ₗ[ℂ] E) l, U g w ≠ w := by
    by_contra! H
    obtain ⟨v, hv⟩ := hg
    set S : E →L[ℂ] E := (U g).toContinuousLinearMap.comp T - T
    have hle : (⨆ l, eigenspace (T : E →ₗ[ℂ] E) l) ≤ LinearMap.ker (S : E →ₗ[ℂ] E) := by
      refine iSup_le fun l w hw => ?_
      have hTw : T w = l • w := mem_eigenspace_iff.mp hw
      show U g (T w) - T w = 0
      rw [hTw, map_smul]
      by_cases hl : l = 0
      · simp [hl]
      · rw [H l hl w hw, sub_self]
    have hclosed : IsClosed ((LinearMap.ker (S : E →ₗ[ℂ] E) : Submodule ℂ E) : Set E) :=
      S.isClosed_ker
    have htop : (⨆ l, eigenspace (T : E →ₗ[ℂ] E) l).topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure,
        T.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs, Submodule.bot_orthogonal_eq_top]
    have : v ∈ LinearMap.ker (S : E →ₗ[ℂ] E) := by
      have := Submodule.topologicalClosure_minimal _ hle hclosed
      rw [htop] at this
      exact this Submodule.mem_top
    exact hv (sub_eq_zero.mp this)
  obtain ⟨l, hl, w₀, hw₀, hne⟩ := step1
  set W : Submodule ℂ E := eigenspace (T : E →ₗ[ℂ] E) l
  have : FiniteDimensional ℂ W := T.finite_dimensional_eigenspace hTc l hl
  have hWinv : ∀ i, ∀ x ∈ W, U i x ∈ W := by
    intro i x hx
    show U i x ∈ eigenspace (T : E →ₗ[ℂ] E) l
    rw [mem_eigenspace_iff]
    have : T x = l • x := mem_eigenspace_iff.mp hx
    change T (U i x) = l • U i x
    rw [hTU, this, map_smul]
  obtain ⟨c, hc1, u, huW, hu0, hu⟩ := exists_eigenvector_ne_one (U g) W (hWinv g) w₀ hw₀ hne
  set W' : Submodule ℂ E := W ⊓ eigenspace ((U g).toLinearMap) c
  have hW'le : W' ≤ W := inf_le_left
  have : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hW'le
  obtain ⟨v, hv, hv0, hvc⟩ := exists_common_eigenvector (fun i => (U i).toLinearMap)
    (fun i j x => hUU i j x) _ W' rfl
    ((Submodule.ne_bot_iff _).mpr ⟨u, ⟨huW, mem_eigenspace_iff.mpr hu⟩, hu0⟩)
    (fun i x hx => ⟨hWinv i x hx.1, by
      show U i x ∈ eigenspace ((U g).toLinearMap) c
      rw [mem_eigenspace_iff]
      have : U g x = c • x := mem_eigenspace_iff.mp hx.2
      change U g (U i x) = c • U i x
      rw [hUU, this, map_smul]⟩)
  refine ⟨l, hl, v, hv0, mem_eigenspace_iff.mp hv.1, hvc, fun h => ?_⟩
  have hgv : U g v = c • v := mem_eigenspace_iff.mp hv.2
  rw [hgv] at h
  have : (c - 1) • v = 0 := by rw [sub_smul, one_smul, h, sub_self]
  exact hv0 ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1))

end HilbertSp


end spectral

section measure

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]

/-- `ψ x = [y ↦ conj (φ (x y⁻¹))] ∈ L²(μ)`. -/
noncomputable def psi (φ : G → ℂ) (hφ : Continuous φ) (x : G) : Lp ℂ 2 μ :=
  BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (row φ hφ x)

theorem continuous_psi (φ : G → ℂ) (hφ : Continuous φ) : Continuous (psi μ φ hφ) :=
  (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ).continuous.comp (continuous_row φ hφ)

theorem exists_psi_bound (φ : G → ℂ) (hφ : Continuous φ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖psi μ φ hφ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_psi μ φ hφ)).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ ⟨x, rfl⟩).trans (le_max_left _ _)⟩

noncomputable def psiBound (φ : G → ℂ) (hφ : Continuous φ) : ℝ :=
  (exists_psi_bound μ φ hφ).choose

theorem psiBound_nonneg (φ : G → ℂ) (hφ : Continuous φ) : 0 ≤ psiBound μ φ hφ :=
  (exists_psi_bound μ φ hφ).choose_spec.1

theorem norm_psi_le (φ : G → ℂ) (hφ : Continuous φ) (x : G) :
    ‖psi μ φ hφ x‖ ≤ psiBound μ φ hφ :=
  (exists_psi_bound μ φ hφ).choose_spec.2 x

/-- `K f (x) = ⟪ψ x, f⟫ = ∫ φ (x y⁻¹) f y dμ(y)`, as a bounded continuous function. -/
noncomputable def kernelFun (φ : G → ℂ) (hφ : Continuous φ) (f : Lp ℂ 2 μ) : G →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => inner ℂ (psi μ φ hφ x) f, (continuous_psi μ φ hφ).inner continuous_const⟩

theorem kernelFun_apply (φ : G → ℂ) (hφ : Continuous φ) (f : Lp ℂ 2 μ) (x : G) :
    kernelFun μ φ hφ f x = inner ℂ (psi μ φ hφ x) f := rfl

noncomputable def kernelOp (φ : G → ℂ) (hφ : Continuous φ) : Lp ℂ 2 μ →L[ℂ] (G →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := kernelFun μ φ hφ
      map_add' := fun f g => by
        ext x
        simp [kernelFun_apply, inner_add_right]
      map_smul' := fun c f => by
        ext x
        simp [kernelFun_apply, inner_smul_right] }
    (psiBound μ φ hφ) (fun f => by
      refine (BoundedContinuousFunction.norm_le
        (mul_nonneg (psiBound_nonneg μ φ hφ) (norm_nonneg f))).mpr fun x => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, kernelFun_apply]
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_psi_le μ φ hφ x) (norm_nonneg f)))

theorem kernelOp_apply (φ : G → ℂ) (hφ : Continuous φ) (f : Lp ℂ 2 μ) (x : G) :
    kernelOp μ φ hφ f x = inner ℂ (psi μ φ hφ x) f := rfl

theorem isCompactOperator_kernelOp (φ : G → ℂ) (hφ : Continuous φ) :
    IsCompactOperator (kernelOp μ φ hφ) := by
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image]
  refine ⟨Metric.ball 0 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
  refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 (psiBound μ φ hφ))
    (isCompact_closedBall _ _) _ ?_ ?_
  · rintro _ x ⟨f, hf, rfl⟩
    rw [mem_ball_zero_iff] at hf
    rw [mem_closedBall_zero_iff, kernelOp_apply]
    calc ‖inner ℂ (psi μ φ hφ x) f‖ ≤ ‖psi μ φ hφ x‖ * ‖f‖ := norm_inner_le_norm _ _
      _ ≤ psiBound μ φ hφ * 1 := mul_le_mul (norm_psi_le μ φ hφ x) hf.le (norm_nonneg _)
          (psiBound_nonneg μ φ hφ)
      _ = psiBound μ φ hφ := mul_one _
  · intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have hc := (continuous_psi μ φ hφ).tendsto x₀
    filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with x hx
    rintro ⟨_, f, hf, rfl⟩
    rw [mem_ball_zero_iff] at hf
    simp only [kernelOp_apply, dist_eq_norm, ← inner_sub_left]
    rw [dist_eq_norm] at hx
    calc ‖inner ℂ (psi μ φ hφ x₀ - psi μ φ hφ x) f‖
        ≤ ‖psi μ φ hφ x₀ - psi μ φ hφ x‖ * ‖f‖ := norm_inner_le_norm _ _
      _ ≤ ‖psi μ φ hφ x₀ - psi μ φ hφ x‖ * 1 := by gcongr
      _ < ε := by rw [mul_one, norm_sub_rev]; exact hx

/-- The convolution operator `T = J ∘ K` on `L²(μ)`. -/
noncomputable def convOp (φ : G → ℂ) (hφ : Continuous φ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ).comp (kernelOp μ φ hφ)

theorem isCompactOperator_convOp (φ : G → ℂ) (hφ : Continuous φ) :
    IsCompactOperator (convOp μ φ hφ) :=
  (isCompactOperator_kernelOp μ φ hφ).clm_comp (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ)

theorem kernelOp_apply_eq_integral (φ : G → ℂ) (hφ : Continuous φ) (f : Lp ℂ 2 μ) (x : G) :
    kernelOp μ φ hφ f x = ∫ y, φ (x * y⁻¹) * f y ∂μ := by
  rw [kernelOp_apply, psi, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) ℂ (row φ hφ x)]
    with y hy
  rw [hy, row_apply, RCLike.inner_apply', Complex.conj_conj]

theorem convOp_coeFn (φ : G → ℂ) (hφ : Continuous φ) (f : Lp ℂ 2 μ) :
    (convOp μ φ hφ f : G → ℂ) =ᵐ[μ] kernelOp μ φ hφ f :=
  BoundedContinuousFunction.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) ℂ _

theorem exists_norm_bound (φ : G → ℂ) (hφ : Continuous φ) : ∃ c, ∀ z, ‖φ z‖ ≤ c := by
  obtain ⟨c, hc⟩ := (isCompact_range hφ).isBounded.exists_norm_le
  exact ⟨c, fun z => hc _ ⟨z, rfl⟩⟩

theorem integrable_L2 (f : Lp ℂ 2 μ) : Integrable (f : G → ℂ) μ :=
  (Lp.memLp f).integrable (by norm_num)

theorem isSymmetric_convOp (φ : G → ℂ) (hφ : Continuous φ)
    (hsym : ∀ z, φ z⁻¹ = conj (φ z)) : (convOp μ φ hφ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).IsSymmetric := by
  intro f h
  simp only [ContinuousLinearMap.coe_coe]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  obtain ⟨c, hc⟩ := exists_norm_bound φ hφ
  have hmeas : AEStronglyMeasurable (fun p : G × G => conj (φ (p.1 * p.2⁻¹))) (μ.prod μ) :=
    (HasCompactSupport.stronglyMeasurable_of_prod
      (Complex.continuous_conj.comp (hφ.comp (by fun_prop)))
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun x y =>
      conj (φ (x * y⁻¹)) * (conj (f y) * h x)) (μ.prod μ) := by
    have h1 : Integrable (fun p : G × G => h p.1 * conj (f p.2)) (μ.prod μ) :=
      (integrable_L2 μ h).mul_prod
        (Complex.conjCLE.toContinuousLinearMap.integrable_comp (integrable_L2 μ f))
    have h2 := h1.bdd_mul hmeas (c := c) (Eventually.of_forall fun p => by
      rw [Complex.norm_conj]; exact hc _)
    refine h2.congr (Eventually.of_forall fun p => ?_)
    obtain ⟨x, y⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  calc ∫ x, inner ℂ (convOp μ φ hφ f x) (h x) ∂μ
      = ∫ x, ∫ y, conj (φ (x * y⁻¹)) * (conj (f y) * h x) ∂μ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [convOp_coeFn μ φ hφ f] with x hx
        rw [hx, kernelOp_apply_eq_integral, RCLike.inner_apply', ← integral_conj,
          ← integral_mul_const]
        congr 1 with y
        simp only [map_mul]
        ring
    _ = ∫ y, ∫ x, conj (φ (x * y⁻¹)) * (conj (f y) * h x) ∂μ ∂μ :=
        integral_integral_swap hint
    _ = ∫ y, inner ℂ (f y) (convOp μ φ hφ h y) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [convOp_coeFn μ φ hφ h] with y hy
        rw [hy, kernelOp_apply_eq_integral, RCLike.inner_apply', ← integral_const_mul]
        congr 1 with x
        have : φ (y * x⁻¹) = conj (φ (x * y⁻¹)) := by
          rw [← hsym]; congr 1; group
        rw [this]
        ring

section invariant

variable [μ.IsMulLeftInvariant]

/-- Left translation `(τ s f)(y) = f (s * y)` on `L²(μ)`. -/
noncomputable def tr (s : G) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun y => s * y) (measurePreserving_mul_left μ s)

theorem tr_coeFn (s : G) (f : Lp ℂ 2 μ) : (tr μ s f : G → ℂ) =ᵐ[μ] fun y => f (s * y) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem ae_comp_mul_left {s : G} {u v : G → ℂ} (h : u =ᵐ[μ] v) :
    (fun y => u (s * y)) =ᵐ[μ] fun y => v (s * y) :=
  (measurePreserving_mul_left μ s).quasiMeasurePreserving.ae_eq_comp h

theorem tr_psi (φ : G → ℂ) (hφ : Continuous φ) (s x : G) :
    tr μ s (psi μ φ hφ x) = psi μ φ hφ (s⁻¹ * x) := by
  apply Lp.ext
  have h1 := BoundedContinuousFunction.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) ℂ (row φ hφ x)
  have h2 := BoundedContinuousFunction.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) ℂ
    (row φ hφ (s⁻¹ * x))
  filter_upwards [tr_coeFn μ s (psi μ φ hφ x), ae_comp_mul_left μ (s := s) h1, h2]
    with y hy1 hy2 hy3
  rw [hy1, psi, hy2, psi, hy3, row_apply, row_apply]
  congr 2
  group
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem kernelOp_tr (φ : G → ℂ) (hφ : Continuous φ) (s : G) (f : Lp ℂ 2 μ) (x : G) :
    kernelOp μ φ hφ (tr μ s f) x = kernelOp μ φ hφ f (s * x) := by
  rw [kernelOp_apply, kernelOp_apply]
  have : psi μ φ hφ x = tr μ s (psi μ φ hφ (s * x)) := by
    rw [tr_psi]; congr 1; group
  rw [this, LinearIsometry.inner_map_map]

theorem convOp_tr (φ : G → ℂ) (hφ : Continuous φ) (s : G) (f : Lp ℂ 2 μ) :
    convOp μ φ hφ (tr μ s f) = tr μ s (convOp μ φ hφ f) := by
  apply Lp.ext
  filter_upwards [convOp_coeFn μ φ hφ (tr μ s f), tr_coeFn μ s (convOp μ φ hφ f),
    ae_comp_mul_left μ (s := s) (convOp_coeFn μ φ hφ f)] with y hy1 hy2 hy3
  rw [hy1, hy2, hy3, kernelOp_tr]

theorem tr_comm (s t : G) (f : Lp ℂ 2 μ) : tr μ s (tr μ t f) = tr μ t (tr μ s f) := by
  apply Lp.ext
  filter_upwards [tr_coeFn μ s (tr μ t f), tr_coeFn μ t (tr μ s f),
    ae_comp_mul_left μ (s := s) (tr_coeFn μ t f), ae_comp_mul_left μ (s := t) (tr_coeFn μ s f)]
    with y h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp only [mul_left_comm]

theorem exists_char_of_eigen (φ : G → ℂ) (hφ : Continuous φ) (g : G) (w : Lp ℂ 2 μ) (l : ℂ)
    (hl : l ≠ 0) (hw0 : w ≠ 0) (hTw : convOp μ φ hφ w = l • w)
    (hc : ∀ s, ∃ c : ℂ, tr μ s w = c • w) (hg : tr μ g w ≠ w) :
    ∃ χ : PontryaginDual G, χ g ≠ 1 := by
  set F := kernelOp μ φ hφ w with hFdef
  choose c hc using hc
  have hF : ∀ s y, F (s * y) = c s * F y := by
    intro s y
    rw [hFdef, ← kernelOp_tr, hc s, map_smul]
    rfl
  have hFne : ∃ x₀, F x₀ ≠ 0 := by
    by_contra! H
    have hF0 : F = 0 := BoundedContinuousFunction.ext H
    have : convOp μ φ hφ w = 0 := by
      show BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (kernelOp μ φ hφ w) = 0
      rw [← hFdef, hF0, map_zero]
    rw [hTw] at this
    exact hw0 ((smul_eq_zero.mp this).resolve_left hl)
  obtain ⟨x₀, hx₀⟩ := hFne
  have hcs : ∀ s, c s = F (s * x₀) / F x₀ := fun s => by
    rw [hF, mul_div_assoc, div_self hx₀, mul_one]
  have hnorm : ∀ s, ‖c s‖ = 1 := by
    intro s
    have h1 : ‖tr μ s w‖ = ‖w‖ := LinearIsometry.norm_map _ _
    rw [hc s, norm_smul] at h1
    have : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    field_simp at h1
    exact h1
  have hmul : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    have := hF (s * t) x₀
    rw [mul_assoc, hF, hF, ← mul_assoc] at this
    exact (mul_right_cancel₀ hx₀ this).symm
  have hcont : Continuous c := by
    have : c = fun s => F (s * x₀) / F x₀ := funext hcs
    rw [this]
    exact (F.continuous.comp (continuous_mul_const x₀)).div_const _
  let χ : PontryaginDual G :=
    { toFun := fun s => ⟨c s, mem_sphere_zero_iff_norm.mpr (hnorm s)⟩
      map_one' := by
        apply Circle.ext
        show c 1 = 1
        rw [hcs, one_mul, div_self hx₀]
      map_mul' := fun s t => by
        apply Circle.ext
        show c (s * t) = c s * c t
        exact hmul s t
      continuous_toFun := by
        exact Continuous.subtype_mk hcont _ }
  refine ⟨χ, fun h => hg ?_⟩
  have hcg : c g = 1 := by
    have := congrArg (fun z : Circle => (z : ℂ)) h
    exact this
  rw [hc g, hcg, one_smul]

end invariant

end measure

/-- **Characters of a compact Hausdorff abelian group separate points.** -/
theorem exists_pontryaginDual_ne_one [T2Space G] (g : G) (hg : g ≠ 1) :
    ∃ χ : PontryaginDual G, χ g ≠ 1 := by
  borelize G
  set μ : Measure G := Measure.haarMeasure ⊤ with hμ
  have : IsProbabilityMeasure μ :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G))⟩
  obtain ⟨V, hVo, hV1, hVV⟩ :=
    exists_open_nhds_one_mul_subset (isOpen_compl_singleton.mem_nhds (Ne.symm hg))
  obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed hVo.isClosed_compl
    isClosed_singleton (Set.disjoint_singleton_right.mpr (fun h => h hV1))
  set φ : G → ℂ := fun z => ((f z * f z⁻¹ : ℝ) : ℂ) with hφdef
  have hφ : Continuous φ :=
    Complex.continuous_ofReal.comp (f.continuous.mul (f.continuous.comp continuous_inv))
  have hsym : ∀ z, φ z⁻¹ = conj (φ z) := by
    intro z
    simp only [hφdef, inv_inv, Complex.conj_ofReal, mul_comm]
  have hsupp : ∀ z, φ z ≠ 0 → z ∈ V ∧ z⁻¹ ∈ V := by
    intro z hz
    by_contra H
    rw [not_and_or] at H
    apply hz
    rcases H with H | H
    · simp [hφdef, hf0 H]
    · simp [hφdef, hf0 H]
  have hφ1 : φ 1 = 1 := by
    simp [hφdef, hf1 (Set.mem_singleton (1 : G))]
  set T := convOp μ φ hφ
  set v := psi μ φ hφ 1
  have hv0 : v ≠ 0 := by
    intro h
    have h' : row φ hφ 1 = 0 :=
      BoundedContinuousFunction.toLp_injective μ (h.trans (map_zero _).symm)
    have := congrArg (fun F : G →ᵇ ℂ => F 1) h'
    simp only [row_apply, mul_one, inv_one, BoundedContinuousFunction.coe_zero,
      Pi.zero_apply, hφ1, map_one] at this
    exact one_ne_zero this
  have hK1 : kernelOp μ φ hφ v 1 ≠ 0 := by
    rw [kernelOp_apply]
    exact inner_self_ne_zero.mpr hv0
  have hKg : kernelOp μ φ hφ v g = 0 := by
    rw [kernelOp_apply_eq_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [BoundedContinuousFunction.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) ℂ
      (row φ hφ 1)] with y hy
    show φ (g * y⁻¹) * (psi μ φ hφ 1 : G → ℂ) y = 0
    rw [psi, hy, row_apply, one_mul]
    by_cases h1 : φ (g * y⁻¹) = 0
    · simp [h1]
    by_cases h2 : φ y⁻¹ = 0
    · simp [h2]
    exfalso
    have hm := hVV (Set.mul_mem_mul (hsupp _ h1).1 (by simpa using (hsupp _ h2).2))
    simp at hm
  have hgT : ∃ u, tr μ g (T u) ≠ T u := by
    refine ⟨v, fun heq => ?_⟩
    have hae : (fun y => kernelOp μ φ hφ v (g * y)) =ᵐ[μ] kernelOp μ φ hφ v := by
      filter_upwards [tr_coeFn μ g (T v), ae_comp_mul_left μ (s := g) (convOp_coeFn μ φ hφ v),
        convOp_coeFn μ φ hφ v] with y h1 h2 h3
      rw [← h2, ← h1, heq, h3]
    have heq2 := ((kernelOp μ φ hφ v).continuous.comp (continuous_const_mul g)).ae_eq_iff_eq μ
      (kernelOp μ φ hφ v).continuous |>.mp hae
    have := congrFun heq2 1
    simp only [Function.comp_apply, mul_one] at this
    exact hK1 (this ▸ hKg)
  obtain ⟨l, hl, w, hw0, hTw, hc, hgw⟩ := exists_joint_eigenvector T
    (isCompactOperator_convOp μ φ hφ) (isSymmetric_convOp μ φ hφ hsym) (tr μ)
    (fun s t x => tr_comm μ s t x) (fun s x => convOp_tr μ φ hφ s x) g hgT
  exact exists_char_of_eigen μ φ hφ g w l hl hw0 hTw hc hgw

end MasulloGRHCompactCharAux

namespace MasulloGRHCompactCharAux

/-- Annihilator separation for a closed subgroup of a compact Hausdorff abelian group. -/
theorem exists_eq_one_on_subgroup_ne_one_of_compact
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 := by
  have : IsClosed (H : Set G) := hH
  have : T2Space (G ⧸ H) := inferInstance
  have hne : (QuotientGroup.mk g : G ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_ne_one (G := G ⧸ H) _ hne
  refine ⟨ψ.comp ⟨QuotientGroup.mk' H, continuous_quot_mk⟩, fun h hh => ?_, hψ⟩
  show ψ (QuotientGroup.mk h) = 1
  rw [(QuotientGroup.eq_one_iff h).mpr hh, _root_.map_one]

end MasulloGRHCompactCharAux

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 :=
  MasulloGRHCompactCharAux.exists_eq_one_on_subgroup_ne_one_of_compact H hH g hg
