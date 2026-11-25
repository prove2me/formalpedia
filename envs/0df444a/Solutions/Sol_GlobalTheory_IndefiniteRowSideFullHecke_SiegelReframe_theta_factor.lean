-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.theta_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:54.525915+00:00
-- url     : https://prove2.me/submissions/05133b3a-27ca-4ccc-aeb9-52db520cd721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SiegelReframe_thetaExp_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped Real ContDiff
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) :
    IsFactor B τ (stdLat g)
      (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)) ∧
    InducesPolarisation B τ (stdLat g)
      (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)) := by
  have hint : ∀ l ∈ stdLat g, ∀ i, ∃ k : ℤ, l i = k := by
    intro l hl i
    obtain ⟨k, hk⟩ := ((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ l).1 hl i
    exact ⟨k, by simpa using hk.symm⟩
  refine ⟨⟨fun l _ => ⟨?_, fun _ _ => Complex.exp_ne_zero _⟩, fun l hl l' hl' P hP => ?_⟩,
    fun b hb => ⟨thetaExp (τ b), fun l _ => ⟨?_, fun _ => rfl⟩, fun l _ l' _ z => ?_⟩⟩
  · have hd : ∀ i j, DifferentiableOn ℂ (fun P : Pt E g => τ P.1 i j) (cov B g) := fun i j =>
      (hτ.2.1 i j).comp differentiableOn_fst fun P hP => hP.1
    simp only [thetaExp, dotProduct, Matrix.vecMul, div_eq_mul_inv]
    have hz : ∀ i, DifferentiableOn ℂ (fun P : Pt E g => P.2 i) (cov B g) := fun i =>
      Differentiable.differentiableOn (by fun_prop)
    refine DifferentiableOn.cexp (DifferentiableOn.const_mul (DifferentiableOn.sub
      (DifferentiableOn.mul_const (DifferentiableOn.neg (DifferentiableOn.fun_sum fun i _ =>
        DifferentiableOn.mul_const (DifferentiableOn.fun_sum fun k _ =>
          (hd k i).const_mul _) _)) _)
      (DifferentiableOn.fun_sum fun i _ => (hz i).const_mul _)) _)
  · choose a ha using hint l hl
    choose a' ha' using hint l' hl'
    have hs : ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ) =
        ((∑ i, a (Sum.inl i) * a' (Sum.inr i) : ℤ) : ℂ) := by simp [ha, ha']
    simp only [transl]
    rw [thetaExp_add (hτ.2.2 _ hP.1).1, hs, mul_add, mul_add, Complex.exp_add, Complex.exp_add,
      mul_comm (2 * π * Complex.I) ((_ : ℤ) : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · unfold thetaExp dotProduct
    fun_prop
  · have e1 := thetaExp_add (hτ.2.2 b hb).1 l l' z
    have e2 := thetaExp_add (hτ.2.2 b hb).1 l' l z
    rw [add_comm l' l] at e2
    have e3 : (riem l l' : ℂ) = ∑ i, (l' (Sum.inl i) : ℂ) * (l (Sum.inr i) : ℂ) -
        ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ) := by
      simp [riem, mul_comm]
    rw [e3]
    linear_combination e2 - e1
end GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
