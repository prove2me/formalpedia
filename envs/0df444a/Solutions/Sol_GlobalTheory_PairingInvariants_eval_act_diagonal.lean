-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.eval_act_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:53.044569+00:00
-- url     : https://prove2.me/submissions/72f50101-ccb7-44c0-81f9-d3e959771888

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
import Theorems.Thm_GlobalTheory_PairingInvariants_act_diagonal
import Theorems.Thm_GlobalTheory_PairingInvariants_differentiable_eval

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
    (a : T → Fin n → ℝ) (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval (act (fun t => diagonal fun i => cexp (a t i))
      (fun t => diagonal fun i => cexp (-(a t i : ℂ))) z) p = MvPolynomial.eval z p := by
  let F : ℂ → ℂ := fun c => MvPolynomial.eval (act (fun t => diagonal fun i => cexp (c * a t i))
      (fun t => diagonal fun i => cexp (-(c * a t i : ℂ))) z) p
  have hF : Differentiable ℂ F := by
    apply differentiable_eval
    rintro ⟨t, b, k, j⟩
    simp only [act_diagonal]
    cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;> fun_prop
  have hI : ∀ y : ℝ, F (y * I) = MvPolynomial.eval z p := by
    intro y
    rw [← hp (fun t => diagonal fun i => cexp (y * I * a t i)) ?_ z]
    · simp only [F]
      congr 3
      funext t
      rw [diagonal_map (by simp)]
      congr 1
      funext i
      simp [← Complex.exp_conj]
    · intro t
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      simp [← Complex.exp_conj, ← Complex.exp_add]
  have hfr : ∃ᶠ c in 𝓝[≠] (0 : ℂ), F c = (fun _ => MvPolynomial.eval z p) c := by
    have ht : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Continuous (fun y : ℝ => (y : ℂ) * I) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa using hy
    exact ht.frequently (Frequently.of_forall hI)
  have := AnalyticOnNhd.eq_of_frequently_eq (fun c _ => hF.analyticAt c) analyticOnNhd_const hfr
  simpa [F] using congrFun this 1
end GlobalTheory.PairingInvariants
