-- Prove2me | solution 1 for GlobalTheory.DriftUnitary.exists_drift_function
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:19.670043+00:00
-- url     : https://prove2.me/submissions/06082b02-650f-48aa-a5f9-3f0ea3f7610e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionOrthonormalHermitianFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FrameStepOfRightMulRealUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionRealUnitaryGroup
import Theorems.Thm_GlobalTheory_DriftUnitary_continuous_orbit
import Theorems.Thm_GlobalTheory_LineHeight_nonempty_cmType
import Theorems.Thm_GlobalTheory_UnitaryFrames_unitary_group_frames
import Theorems.Thm_GlobalTheory_UnitaryLift_step_of_right_mul
import Theorems.Thm_GlobalTheory_exists_drift_function_orthFrames
import Theorems.Thm_GlobalTheory_exists_finite_symmetric_irreducible_rotations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
namespace GlobalTheory.DriftUnitary
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem single_one_mulVec_eq_pi_single (r : ℕ) (j k : Fin r) (w : Fin r → ℂ) :
    (Matrix.single j k (1 : ℂ)).mulVec w = Pi.single j (w k) := by
  ext i
  by_cases hi : i = j
  · subst hi; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hi, Ne.symm hi]
open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem eq_bot_or_eq_whole_of_single_mulVec_invariant (r p : ℕ) (hp : 0 < p) (hpr : p < r)
    (W : Submodule ℂ (Fin r → ℂ))
    (hW : ∀ (j k : Fin r), (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
      (Matrix.single j k 1).mulVec v ∈ W ∧ (Matrix.single k j 1).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have hsmul : ∀ (i : Fin r) (z : ℂ), z ≠ 0 → Pi.single i z ∈ W → Pi.single i (1 : ℂ) ∈ W := by
    intro i z hz h
    have e : z⁻¹ • (Pi.single i z : Fin r → ℂ) = Pi.single i 1 := by
      ext l
      by_cases hl : l = i <;> simp [hl, hz]
    rw [← e]
    exact W.smul_mem _ h
  let j0 : Fin r := ⟨0, by omega⟩
  let k0 : Fin r := ⟨p, hpr⟩
  have hj0 : (j0 : ℕ) < p := hp
  have hk0' : p ≤ (k0 : ℕ) := le_rfl
  have hk0 : Pi.single k0 (1 : ℂ) ∈ W := by
    rcases Nat.lt_or_ge (m : ℕ) p with h | h
    · have h1 := (hW m k0 h hk0' v hvW).2
      rw [single_one_mulVec_eq_pi_single] at h1
      exact hsmul _ _ hm h1
    · have h1 := (hW j0 m hj0 h v hvW).1
      rw [single_one_mulVec_eq_pi_single] at h1
      have h3 := (hW j0 k0 hj0 hk0' _ (hsmul _ _ hm h1)).2
      rw [single_one_mulVec_eq_pi_single] at h3
      simpa using h3
  have he0 : Pi.single j0 (1 : ℂ) ∈ W := by
    have h1 := (hW j0 k0 hj0 hk0' _ hk0).1
    rw [single_one_mulVec_eq_pi_single] at h1
    simpa using h1
  have hall : ∀ i : Fin r, Pi.single i (1 : ℂ) ∈ W := by
    intro i
    rcases Nat.lt_or_ge (i : ℕ) p with h | h
    · have h1 := (hW i k0 h hk0' _ hk0).1
      rw [single_one_mulVec_eq_pi_single] at h1
      simpa using h1
    · have h1 := (hW j0 i hj0 h _ he0).2
      rw [single_one_mulVec_eq_pi_single] at h1
      simpa using h1
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact Submodule.sum_mem _ fun i _ => W.smul_mem _ (hall i)
end GlobalTheory.DriftUnitary
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.DriftUnitary
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.DriftUnitary
namespace _root_.GlobalTheory.DriftUnitary
theorem _root_.solution :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < X.p0 → X.p0 < r → ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  intro r X H hH _ _ hp0 hpr x0 hx0
  obtain ⟨S, hSne, hS1, hS2, hS3⟩ := _root_.GlobalTheory.exists_finite_symmetric_irreducible_rotations
    eq_bot_or_eq_whole_of_single_mulVec_invariant r X.p0 hp0 hpr
  obtain ⟨τ0⟩ := _root_.GlobalTheory.LineHeight.nonempty_cmType X
  obtain ⟨f, c, b, hc0, hc1, hb, hlsc, hf0, hfinv, hdrift, hla⟩ :=
    _root_.GlobalTheory.exists_drift_function_orthFrames r X hp0 hpr τ0 S hS1 hS2 (fun a ha => (hS3 a ha).1)
  have horb := (((_root_.GlobalTheory.UnitaryFrames.unitary_group_frames (E := E)).2 r X H hH).2.2 x0 hx0).1
  have hstep := fun a : S => _root_.GlobalTheory.UnitaryLift.step_of_right_mul r X H hH x0 hx0 τ0 a.1
    (hS3 a.1 a.2).2.choose (hS3 a.1 a.2).1 (hS3 a.1 a.2).2.choose_spec.1 (hS3 a.1 a.2).2.choose_spec.2
  choose hS kS hkS hupd using hstep
  refine ⟨S, inferInstance, hSne.to_subtype, hS,
    fun g => f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0), c, b,
    fun s => ⟨kS s, hkS s⟩, ?_, fun g => hf0 _ (horb g), ?_, hc0, hc1, hb, ?_, ?_⟩
  · have hcont := _root_.GlobalTheory.DriftUnitary.continuous_orbit X H x0
    have hl : LowerSemicontinuous fun g : H =>
        f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
      intro g y hy
      have ht : Filter.Tendsto (fun g : H =>
          X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) (𝓝 g)
          (𝓝[{x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x}] (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) :=
        tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto g, Filter.Eventually.of_forall fun g' => show _ ∈ {x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x} from horb g'⟩
      exact ht.eventually (hlsc _ (horb g) y hy)
    exact hl.measurable
  · rintro u ⟨γ, hγ, hu⟩ g
    have e : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
      funext τ
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hu τ,
        Matrix.mul_assoc]
      rfl
    show f _ = f _
    rw [e]
    exact hfinv γ hγ _ (horb g)
  · intro g
    simp only [hupd, Fintype.card_coe]
    exact (Finset.sum_coe_sort S _).trans_le (hdrift _ (horb g))
  · intro M
    obtain ⟨ε, hε, h⟩ := hla M
    exact ⟨ε, hε, fun g hg => h _ (horb g) hg⟩
end _root_.GlobalTheory.DriftUnitary
end GlobalTheory.DriftUnitary
