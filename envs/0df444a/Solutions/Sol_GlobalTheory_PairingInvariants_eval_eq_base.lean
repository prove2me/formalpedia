-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.eval_eq_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:37:37.054934+00:00
-- url     : https://prove2.me/submissions/96177f4b-d07b-47f6-906f-f6f1f05f66df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
import Theorems.Thm_GlobalTheory_PairingInvariants_differentiable_eval
import Theorems.Thm_GlobalTheory_PairingInvariants_eq_at_zero_of_countable
import Theorems.Thm_GlobalTheory_PairingInvariants_eval_eq_base_of_isUnit

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
theorem _root_.solution [Finite T] (hN : N ≤ n) (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ g h : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, g t * (h t)ᵀ = 1) →
      ∀ z, MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p)
    (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval z p = MvPolynomial.eval (base z) p := by
  let G : T → Matrix (Fin n) (Fin n) ℂ := fun t k l =>
    if h : l.val < N then z (t, true, k, ⟨l.val, h⟩) else 0
  let Z : ℂ → T × Bool × Fin n × Fin N → ℂ := fun c v =>
    z v - (if v.2.1 then (if v.2.2.1.val = v.2.2.2.val then 1 else 0) else 0) * c
  have hZ : ∀ v, Differentiable ℂ (fun c => Z c v) := by
    intro v
    simp only [Z]
    fun_prop
  have hZ0 : Z 0 = z := by
    funext v
    simp [Z]
  have := eq_at_zero_of_countable (F := fun c => MvPolynomial.eval (Z c) p)
    (G := fun c => MvPolynomial.eval (base (Z c)) p) (differentiable_eval p _ hZ)
    (differentiable_eval p _ ?_) (S := ⋃ t, spectrum ℂ (G t))
    (Set.countable_iUnion fun t => (Matrix.finite_spectrum (G t)).countable) ?_
  · simpa [hZ0] using this
  · intro v
    simp only [base]
    split_ifs
    · fun_prop
    · fun_prop
    · exact Differentiable.fun_sum fun l _ => (hZ _).fun_mul (hZ _)
    · fun_prop
  · intro c hc
    simp only [Set.mem_iUnion, not_exists, spectrum.mem_iff, not_not] at hc
    refine eval_eq_base_of_isUnit hN p hp (fun t => -(algebraMap ℂ _ c - G t))
      (fun t => (hc t).neg) _ ?_
    intro t k j
    rw [Matrix.neg_apply, Matrix.sub_apply, Matrix.algebraMap_matrix_apply]
    simp [Z, G, Fin.ext_iff]
end GlobalTheory.PairingInvariants
