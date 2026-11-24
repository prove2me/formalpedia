-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.eval_act_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:43.253632+00:00
-- url     : https://prove2.me/submissions/cc8d0383-0765-4097-b935-01bc63b45432

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
import Theorems.Thm_GlobalTheory_PairingInvariants_exists_unitary_diagonal_unitary
import Theorems.Thm_GlobalTheory_PairingInvariants_act_mul
import Theorems.Thm_GlobalTheory_PairingInvariants_eval_act_diagonal

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
theorem _root_.solution (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ z, MvPolynomial.eval (act u (fun t => (u t).map conj) z) p = MvPolynomial.eval z p)
    (g h : T → Matrix (Fin n) (Fin n) ℂ) (hgh : ∀ t, g t * (h t)ᵀ = 1)
    (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p := by
  have hg : ∀ t, IsUnit (g t) := fun t => IsUnit.of_mul_eq_one _ (hgh t)
  choose u₁ u₂ a h₁ h₂ e using fun t => exists_unitary_diagonal_unitary (g t) (hg t)
  have eh : h = fun t => (u₁ t).map conj * diagonal (fun i => cexp (-(a t i : ℂ))) * (u₂ t).map conj := by
    funext t
    apply Matrix.transpose_injective
    apply (hg t).mul_left_cancel
    rw [hgh t, e t]
    have h2 : diagonal (fun i => cexp (a t i : ℂ)) * diagonal (fun i => cexp (-(a t i : ℂ))) = 1 := by
      rw [diagonal_mul_diagonal]
      simp [← Complex.exp_add]
    have k₁ : u₁ t * ((u₁ t).map conj)ᵀ = 1 := Matrix.mem_unitaryGroup_iff.1 (h₁ t)
    have k₂ : u₂ t * ((u₂ t).map conj)ᵀ = 1 := Matrix.mem_unitaryGroup_iff.1 (h₂ t)
    rw [transpose_mul, transpose_mul, diagonal_transpose, Matrix.mul_assoc _ (u₂ t), ← Matrix.mul_assoc (u₂ t), k₂, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), h2, Matrix.one_mul, k₁]
  have eg : g = fun t => u₁ t * diagonal (fun i => cexp (a t i)) * u₂ t := funext e
  rw [eh, eg, act_mul, act_mul, hp _ h₁, eval_act_diagonal p hp, hp _ h₂]
end GlobalTheory.PairingInvariants
