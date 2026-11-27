-- Prove2me | solution 1 for GroundTheory.Automorphic.ratGram_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:48.080172+00:00
-- url     : https://prove2.me/submissions/261a8799-1332-4eeb-97b0-113b6c9b71a4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_trace_eq_sum_realEmb
import Theorems.Thm_GroundTheory_Automorphic_linearIndependent_realEmb_integralBasis
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.hermTraceBilin_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {H b}
namespace GroundTheory.Automorphic
theorem _root_.solution (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    (v : (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ v) := by
  set ω := integralBasis K
  let u : InfinitePlace K → ι × κ → ℝ := fun w a => ∑ t, v (a, t) * realEmb hreal w (ω t)
  have hexp : v ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ v) =
      ∑ w, ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := by
    simp only [dotProduct, mulVec, Matrix.map_apply, ratGram, trace_eq_sum_realEmb hreal,
      Finset.mul_sum, Finset.sum_mul]
    have step : ∀ f : (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) →
        (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → InfinitePlace K → ℝ,
        ∑ x, ∑ y, ∑ i, f x y i = ∑ i, ∑ x, ∑ y, f x y i := by
      intro f
      calc ∑ x, ∑ y, ∑ i, f x y i = ∑ x, ∑ i, ∑ y, f x y i :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ i, ∑ x, ∑ y, f x y i := Finset.sum_comm
    have swap4 : ∀ F : ι × κ → Free.ChooseBasisIndex ℤ (𝓞 K) → ι × κ →
        Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ,
        ∑ a, ∑ t, ∑ c, ∑ t', F a t c t' = ∑ a, ∑ c, ∑ t, ∑ t', F a t c t' :=
      fun F => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [step]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [u, Finset.sum_mul, Finset.mul_sum]
    simp only [Fintype.sum_prod_type (α₁ := ι × κ) (α₂ := Free.ChooseBasisIndex ℤ (𝓞 K))]
    have swap2 : ∀ F : Free.ChooseBasisIndex ℤ (𝓞 K) → Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ,
        ∑ t, ∑ t', F t t' = ∑ t', ∑ t, F t t' := fun F => Finset.sum_comm
    rw [swap4]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [swap2]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    simp only [map_mul]
    ring
  rw [hexp]
  have hnonneg : ∀ w, 0 ≤ ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := by
    intro w
    by_cases hu : u w = 0
    · simp [hu]
    · exact (hθ w (hreal w) (u w) hu).le
  obtain ⟨w, hw⟩ : ∃ w, u w ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext ⟨a, t⟩
    have hli := linearIndependent_realEmb_integralBasis hreal
    have hsum : (∑ t, v (a, t) • (fun w : {w : InfinitePlace K // w.IsReal} =>
        embedding_of_isReal w.2 (ω t)) : {w : InfinitePlace K // w.IsReal} → ℝ) = 0 := by
      funext w'
      have := congrFun (h w'.1) a
      simpa [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    exact Fintype.linearIndependent_iff.1 hli (fun t => v (a, t)) hsum t
  calc 0 < ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := hθ w (hreal w) (u w) hw
    _ ≤ _ := Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ w)
end GroundTheory.Automorphic
