-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.eval_eq_base_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:53.983794+00:00
-- url     : https://prove2.me/submissions/70cd3874-70c9-4548-ace8-7e83fc67e781

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
import Theorems.Thm_GlobalTheory_PairingInvariants_act_diagonal
import Theorems.Thm_GlobalTheory_PairingInvariants_differentiable_eval
import Theorems.Thm_GlobalTheory_PairingInvariants_eq_at_zero_of_countable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.PairingInvariants
variable {T : Type} {n N : ℕ}
namespace GlobalTheory.PairingInvariants
theorem _root_.solution (hN : N ≤ n) (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ g h : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, g t * (h t)ᵀ = 1) →
      ∀ z, MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p)
    (G : T → Matrix (Fin n) (Fin n) ℂ) (hG : ∀ t, IsUnit (G t))
    (z : T × Bool × Fin n × Fin N → ℂ) (hz : ∀ t k j, z (t, true, k, j) = G t k (Fin.castLE hN j)) :
    MvPolynomial.eval z p = MvPolynomial.eval (base z) p := by
  have hinv : ∀ t, (G t)⁻¹ * G t = 1 := fun t =>
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hG t))
  set y := act (fun t => (G t)⁻¹) (fun t => (G t)ᵀ) z with hy
  have h1 : MvPolynomial.eval y p = MvPolynomial.eval z p := hp _ _ (by simpa using hinv) z
  have hyt : ∀ t k j, y (t, true, k, j) = if k.val = j.val then 1 else 0 := by
    intro t k j
    have := congrFun (congrFun (hinv t) k) (Fin.castLE hN j)
    simp only [hy, act, hz, if_true]
    rw [← Matrix.mul_apply, this, Matrix.one_apply]
    simp [Fin.ext_iff]
  let Y : ℂ → T × Bool × Fin n × Fin N → ℂ := fun c v =>
    if v.2.1 then y v else (if v.2.2.1.val < N then 1 else c) * y v
  have hY : Differentiable ℂ (fun c => MvPolynomial.eval (Y c) p) := by
    apply differentiable_eval
    intro v
    simp only [Y]
    split_ifs <;> fun_prop
  have h2 : MvPolynomial.eval (Y 0) p = MvPolynomial.eval y p := by
    refine eq_at_zero_of_countable hY (differentiable_const _) (Set.countable_singleton 0) ?_
    intro c hc
    have hc : c ≠ 0 := hc
    rw [← hp (fun _ => diagonal fun k => if k.val < N then 1 else c⁻¹)
      (fun _ => diagonal fun k => if k.val < N then 1 else c) ?_ y, act_diagonal]
    · congr 2
      funext ⟨t, b, k, j⟩
      cases b
      · simp [Y]
      · simp only [Y, if_true, hyt]
        have := j.2
        split_ifs <;> first | omega | simp
    · intro t
      rw [diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      split_ifs <;> simp [hc]
  rw [← h1, ← h2]
  congr 2
  funext ⟨t, b, k, j⟩
  cases b
  · simp only [Y, base, Bool.false_eq_true, if_false]
    split_ifs with h
    · simp only [hy, act, hz, Bool.false_eq_true, if_false, one_mul, transpose_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]
      rfl
    · simp
  · simp only [Y, base, if_true, hyt]
end GlobalTheory.PairingInvariants
