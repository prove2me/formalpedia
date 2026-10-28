-- Prove2me | solution 1 for OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:42:42.905314+00:00
-- url     : https://prove2.me/submissions/51387313-367b-48d1-a1b0-c3440b5696a9

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C038
import Theorems.Thm_OAI_Kadison_IrreducibleTowerAveraging_orbit_subset_eventualFiber
import Theorems.Thm_OAI_Kadison_IrreducibleTowerAveraging_scalar_mem_hull

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

omit [∀ n, Nonempty (ι n)] in
lemma eventualFiber_convex (a : M) : Convex ℝ (eventualFiber M τ stage a) := by
  rintro x ⟨b,rfl,hb⟩ y ⟨c,rfl,hc⟩ r s _ _ hrs
  have hvec (t : ℝ) (d : M) :
      algebraVector τ (t • d) = t • algebraVector τ d := by
    rw [← Complex.coe_smul, (algebraVector τ).map_smul, Complex.coe_smul]
  have hexp (n : ℕ) (t : ℝ) (d : M) :
      expectation (stage n) (t • d) = t • expectation (stage n) d := by
    rw [← Complex.coe_smul, (expectation (stage n)).map_smul, Complex.coe_smul]
  refine ⟨r • b+s • c,?_,?_⟩
  · simp only [map_add, hvec]
  · filter_upwards [hb,hc] with n hn kn
    simp only [map_add, hexp, hvec, hn, kn, ←add_smul, hrs, one_smul]

include hτ hmono in
theorem expectation_tendsto_oai
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) (ha : ‖a‖≤1) :
    Tendsto (fun n => algebraVector τ (expectation (stage n) a)) atTop
      (𝓝 ((τ a) • vacuum τ)) := by
  have hh := scalar_mem_hull M τ hτ stage hmono hnormal hfaith hone hirr a ha
  rw [closedConvexHull_eq_closure_convexHull] at hh
  have hf : convexHull ℝ (orbit M τ stage hmono a) ⊆ eventualFiber M τ stage a :=
    convexHull_min (orbit_subset_eventualFiber M τ hτ stage hmono a)
      (eventualFiber_convex M τ stage a)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v,hv,hd⟩ := Metric.mem_closure_iff.mp hh ε hε
  obtain ⟨b,hb,hba⟩ := hf hv
  filter_upwards [hba] with n hn
  rw [dist_comm] at hd
  have hvac : algebraVector τ ((τ a) • (1:M)) = (τ a) • vacuum τ :=
    (algebraVector τ).map_smul (τ a) 1
  have hsub : algebraVector τ (b-(τ a) • (1:M)) =
      algebraVector τ b - (τ a) • vacuum τ := by
    rw [(algebraVector τ).map_sub b ((τ a) • (1:M)), hvac]
  have hsmall : ‖algebraVector τ (b-(τ a) • (1:M))‖<ε := by
    simpa only [dist_eq_norm, hsub, hb] using hd
  have he : algebraVector τ (expectation (stage n) (b-(τ a) • (1:M)))=
      algebraVector τ (expectation (stage n) a)-(τ a) • vacuum τ := by
    have hexp : expectation (stage n) (b-(τ a) • (1:M)) =
        expectation (stage n) b - (τ a) • (1:M) :=
      ((expectation (stage n)).map_sub b ((τ a) • (1:M))).trans
        (congrArg (fun d : M => expectation (stage n) b - d)
          (fixes_scalar (stage n) (τ a)))
    have hvec : algebraVector τ (expectation (stage n) b - (τ a) • (1:M)) =
        algebraVector τ (expectation (stage n) b) - (τ a) • vacuum τ :=
      ((algebraVector τ).map_sub (expectation (stage n) b) ((τ a) • (1:M))).trans
        (congrArg (fun v : τ.GNS => algebraVector τ (expectation (stage n) b) - v) hvac)
    exact (congrArg (algebraVector τ) hexp).trans
      (hvec.trans (congrArg (fun v : τ.GNS => v - (τ a) • vacuum τ) hn))
  rw [dist_eq_norm,←he]
  exact (norm_vector_le (stage n) τ hτ _).trans_lt hsmall

end Kadison.IrreducibleTowerAveraging

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto_oai.{u_1, u_2} := @OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto_oai.{u_1, u_2}
