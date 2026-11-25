-- Prove2me | solution 1 for John.exists_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:16.426261+00:00
-- url     : https://prove2.me/submissions/44b78753-11c1-4acd-8988-6ac07c875080

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John
public import Theorems.Thm_John_exists_johnPosition
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_John_norm_inner_le_of_contact
public import Theorems.Thm_John_john_decomposition
public import Theorems.Thm_John_norm_sum_weight_smul_le
attribute [local simp] John.rankOneSA_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V] :
    ∃ P : Y →L[𝕜] Y, P.comp P = P ∧
      LinearMap.range (P : Y →ₗ[𝕜] Y) = V ∧ ‖P‖ ≤ Real.sqrt (Module.finrank 𝕜 V) := by
  classical
  set k := Module.finrank 𝕜 V with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `V = ⊥`: the zero map works.
    refine ⟨0, by simp, ?_, ?_⟩
    · have hV : V = ⊥ := Submodule.finrank_eq_zero.mp (hk.symm.trans hk0)
      rw [hV]; simp
    · rw [hk0]; simp
  -- From now on `0 < k`.
  -- A continuous linear equivalence `𝕜^k ≃L V` (both have dimension `k`), and the
  -- John position along it: `M = L ∘ T₀` with `‖M z‖ = q z`.
  have hEfin : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := finrank_euclideanSpace_fin
  obtain ⟨M, q, hqc, hq1, hqmax, hqM₀⟩ :=
    exists_johnPosition hkpos (ContinuousLinearEquiv.ofFinrankEq (hEfin.trans hk) :
      EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] V)
  have hqM : ∀ z, ‖(M z : Y)‖ = q z := fun z => by
    rw [Submodule.norm_coe]; exact hqM₀ z
  -- The John decomposition of identity in John position.
  obtain ⟨N, u, c, hcontact, hcnn, hcsum, hdec⟩ := john_decomposition q hqc hq1 hqmax
  -- Functionals `φ i = ⟪u i, M.symm ·⟫` on `V`, of norm `≤ 1`.
  set φ : Fin N → (V →L[𝕜] 𝕜) :=
    fun i => (innerSL 𝕜 (u i)).comp (M.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k)) with hφ
  have hφapply : ∀ i (w : V), φ i w = ⟪u i, M.symm w⟫_𝕜 := fun i w => by
    simp only [hφ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      innerSL_apply_apply]
  have hφnorm : ∀ i, ‖φ i‖ ≤ 1 := fun i => by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hφapply]
    calc ‖⟪u i, M.symm w⟫_𝕜‖ = ‖⟪M.symm w, u i⟫_𝕜‖ := by
          rw [← inner_conj_symm (M.symm w) (u i), RCLike.norm_conj]
      _ ≤ q (M.symm w) := norm_inner_le_of_contact (hcontact i) (M.symm w)
      _ = ‖(M (M.symm w) : Y)‖ := (hqM (M.symm w)).symm
      _ = ‖w‖ := by rw [M.apply_symm_apply, Submodule.norm_coe]
  -- Hahn–Banach: extend each `φ i` to `g i ∈ Y*` without increasing the norm.
  choose g hg_ext hg_norm using fun i => exists_extension_norm_eq V (φ i)
  have hgnorm1 : ∀ i, ‖g i‖ ≤ 1 := fun i => (hg_norm i).trans_le (hφnorm i)
  -- The projection `P = ∑ᵢ cᵢ · g i ⊗ (M (u i))`.
  set P : Y →L[𝕜] Y := ∑ i, (c i : 𝕜) • ((g i).smulRight ((M (u i) : V) : Y)) with hP
  have hPapply : ∀ y, P y = ∑ i, ((c i : 𝕜) * g i y) • ((M (u i) : Y)) := fun y => by
    rw [hP]
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_smul]
  have hPmem : ∀ y, P y ∈ V := fun y => by
    rw [hPapply]
    exact V.sum_mem fun i _ => V.smul_mem _ (M (u i)).2
  -- `P` is the identity on `V`.
  have hPV : ∀ w : V, P (w : Y) = (w : Y) := fun w => by
    rw [hPapply]
    have hgi : ∀ i, g i (w : Y) = ⟪u i, M.symm w⟫_𝕜 := fun i => by rw [hg_ext i w, hφapply i w]
    simp only [hgi]
    have hpull : ((M (∑ i, ((c i : 𝕜) * ⟪u i, M.symm w⟫_𝕜) • u i) : V) : Y)
        = ∑ i, ((c i : 𝕜) * ⟪u i, M.symm w⟫_𝕜) • ((M (u i) : V) : Y) := by
      rw [map_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Submodule.coe_smul]
    rw [← hpull, hdec (M.symm w), M.apply_symm_apply]
  refine ⟨P, ?_, ?_, ?_⟩
  · -- `P ∘ P = P`, since `P` fixes its range `⊆ V`.
    ext y
    simpa [ContinuousLinearMap.comp_apply] using hPV ⟨P y, hPmem y⟩
  · -- `range P = V`.
    apply le_antisymm
    · rintro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨y, rfl⟩ := hx
      exact hPmem y
    · intro w hw
      rw [LinearMap.mem_range]
      exact ⟨w, by simpa using hPV ⟨w, hw⟩⟩
  · -- `‖P‖ ≤ √k`.
    refine ContinuousLinearMap.opNorm_le_bound P (Real.sqrt_nonneg _) fun y => ?_
    have hpull : ((M (∑ i, ((c i : 𝕜) * g i y) • u i) : V) : Y)
        = ∑ i, ((c i : 𝕜) * g i y) • ((M (u i) : V) : Y) := by
      rw [map_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Submodule.coe_smul]
    have hPyeq : P y = ((M (∑ i, ((c i : 𝕜) * g i y) • u i) : V) : Y) := by rw [hPapply, hpull]
    have hb : ∑ i, c i * ‖g i y‖ ^ 2 ≤ (k : ℝ) * ‖y‖ ^ 2 := by
      have hstep : ∀ i, c i * ‖g i y‖ ^ 2 ≤ c i * ‖y‖ ^ 2 := fun i => by
        apply mul_le_mul_of_nonneg_left _ (hcnn i)
        calc ‖g i y‖ ^ 2 ≤ (‖g i‖ * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ (norm_nonneg _) ((g i).le_opNorm y)
          _ ≤ (1 * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity)
              exact mul_le_mul_of_nonneg_right (hgnorm1 i) (norm_nonneg _)
          _ = ‖y‖ ^ 2 := by rw [one_mul]
      calc ∑ i, c i * ‖g i y‖ ^ 2 ≤ ∑ i, c i * ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => hstep i
        _ = (∑ i, c i) * ‖y‖ ^ 2 := (Finset.sum_mul _ _ _).symm
        _ = (k : ℝ) * ‖y‖ ^ 2 := by rw [hcsum]
    calc ‖P y‖ = q (∑ i, ((c i : 𝕜) * g i y) • u i) := by rw [hPyeq, hqM]
      _ ≤ ‖∑ i, ((c i : 𝕜) * g i y) • u i‖ := hq1 _
      _ ≤ Real.sqrt (∑ i, c i * ‖g i y‖ ^ 2) :=
          norm_sum_weight_smul_le c u hdec hcnn (fun i => g i y)
      _ ≤ Real.sqrt ((k : ℝ) * ‖y‖ ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (k : ℝ) * ‖y‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq (norm_nonneg _)]
end John
