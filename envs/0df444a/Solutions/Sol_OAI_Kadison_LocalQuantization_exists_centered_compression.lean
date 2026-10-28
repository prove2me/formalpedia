-- Prove2me | solution 1 for OAI.Kadison.LocalQuantization.exists_centered_compression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:27:54.474201+00:00
-- url     : https://prove2.me/submissions/7392ae15-faa7-41e8-89a1-78dc7ac5ca80

import Mathlib
import Definitions.Def_OAIQ039C012
import Definitions.Def_OAIQ039C032
import Theorems.Thm_OAI_Kadison_IrreducibleTowerAveraging_expectation_tendsto
import Theorems.Thm_OAI_Kadison_LocalQuantization_exists_small_projection

section
-- module Solutions.OAIQ039_CM.Commutator_IrreducibleTowerAveraging
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.IrreducibleTowerAveraging

open TracialGNS NormalGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem expectation_tendsto_any
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) :
    Tendsto (fun n => algebraVector τ (expectation (stage n) a)) atTop
      (𝓝 ((τ a) • vacuum τ)) := by
  let c : ℝ := ‖a‖+1
  have hc : 0 < c := by dsimp [c]; positivity
  have hci : 0 ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
  have hb : ‖c⁻¹ • a‖≤1 := by
    rw [norm_smul,Real.norm_of_nonneg hci]
    exact (inv_mul_le_one₀ hc).mpr (by dsimp [c]; linarith)
  have h := expectation_tendsto M τ hτ stage hmono hnormal hfaith hone hirr
    (c⁻¹ • a) hb
  have h' := tendsto_const_nhds.smul h (c:=c)
  simpa only [LinearMap.map_smul_of_tower,PositiveLinearMap.map_smul_of_tower,
    ←smul_assoc,smul_smul,smul_eq_mul,mul_inv_cancel₀ (ne_of_gt hc),one_smul] using h'

end Kadison.IrreducibleTowerAveraging

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_LocalQuantization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology BigOperators

open Filter

namespace Kadison.LocalQuantization

open TracialGNS

section ActualGeometry

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype J]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, LinearOrder (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem exists_centered_compression_oai
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (x : J → M) (hx : ∀ j, τ (x j)=0)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ (n : ℕ) (q : M), q∈(stage n).range ∧ IsStarProjection q ∧
      0<(τ q).re ∧ (τ q).re<η ∧
      (∑ j, ‖algebraVector τ (q*x j*q)‖^2)<ε^2*(τ q).re := by
  apply exists_small_projection τ hτ hone stage hgrow x _ hε hη
  intro j
  simpa only [hx,zero_smul] using
    IrreducibleTowerAveraging.expectation_tendsto_any M τ hτ stage hmono
      hnormal hfaith hone hirr (x j)

end ActualGeometry

end Kadison.LocalQuantization

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.LocalQuantization.exists_centered_compression_oai.{u_1, u_2, u_3} := @OAI.Kadison.LocalQuantization.exists_centered_compression_oai.{u_1, u_2, u_3}
