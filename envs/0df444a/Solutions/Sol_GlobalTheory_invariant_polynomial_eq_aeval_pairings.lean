-- Prove2me | solution 1 for GlobalTheory.invariant_polynomial_eq_aeval_pairings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:52:56.438642+00:00
-- url     : https://prove2.me/submissions/3eb54b74-4601-4db0-a061-5cabd0090c5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
import Theorems.Thm_GlobalTheory_PairingInvariants_eval_act_of_mul_eq_one
import Theorems.Thm_GlobalTheory_PairingInvariants_eval_eq_base

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
open GlobalTheory.PairingInvariants
namespace GlobalTheory
theorem _root_.solution :
    ∀ (T : Type) [Fintype T] [DecidableEq T] (n N : ℕ), N ≤ n → ∀ p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ, (∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ z : T × Bool × Fin n × Fin N → ℂ, MvPolynomial.eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l else conj (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) p = MvPolynomial.eval z p) → ∃ s : MvPolynomial (T × Fin N × Fin N) ℂ, p = MvPolynomial.aeval (fun v : T × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)) s := by
  intro T _ _ n N hN p hp
  have key := eval_eq_base hN p (eval_act_of_mul_eq_one p hp)
  refine ⟨MvPolynomial.aeval (fun v : T × Bool × Fin n × Fin N =>
    if v.2.1 then (if v.2.2.1.val = v.2.2.2.val then 1 else 0) else
      if h : v.2.2.1.val < N then MvPolynomial.X (v.1, v.2.2.2, ⟨v.2.2.1.val, h⟩) else 0) p, ?_⟩
  apply MvPolynomial.funext
  intro z
  rw [key z, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, ← MvPolynomial.coe_aeval_eq_eval,
    ← MvPolynomial.coe_aeval_eq_eval]
  simp only [RingHom.coe_coe]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext v
  simp only [base]
  split_ifs <;> simp
end GlobalTheory
