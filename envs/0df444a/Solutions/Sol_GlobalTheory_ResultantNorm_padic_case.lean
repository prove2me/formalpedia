-- Prove2me | solution 1 for GlobalTheory.ResultantNorm.padic_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:12.132747+00:00
-- url     : https://prove2.me/submissions/d4eab29e-8c24-4bd7-a9d8-b4fc46f58ba0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
import Theorems.Thm_GlobalTheory_ResultantNorm_rat_case

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.ResultantNorm
open Polynomial Filter Topology
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
namespace GlobalTheory.ResultantNorm
theorem _root_.solution (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖)
    (F : ℚ_[l][X]) :
    ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖ := by
  set n := F.natDegree + 1
  let φ : Multiset Ω → (Fin n → ℚ_[l]) → ℝ := fun c v =>
    ‖(c.map fun x => ∑ i : Fin n, algebraMap ℚ_[l] Ω (v i) * x ^ (i : ℕ)).prod‖
  have hc : ∀ c, Continuous (φ c) := fun c =>
    (continuous_multiset_prod c fun x _ => continuous_finsetSum _ fun i _ =>
      ((continuous_algebraMap ℚ_[l] Ω).comp (continuous_apply i)).mul continuous_const).norm
  have hd : DenseRange (Pi.map (fun (_ : Fin n) => ((↑) : ℚ → ℚ_[l]))) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have heq : φ a = φ b := by
    refine Continuous.ext_on hd (hc a) (hc b) ?_
    rintro _ ⟨v, rfl⟩
    have := rat_case (l := l) a b h (∑ i : Fin n, monomial (i : ℕ) (v i))
    simpa [φ, Polynomial.map_sum, aeval_monomial] using this
  have := congrFun heq fun i => F.coeff i
  have hx : ∀ x : Ω, aeval x F = ∑ i : Fin n, algebraMap ℚ_[l] Ω (F.coeff i) * x ^ (i : ℕ) := by
    intro x
    rw [aeval_eq_sum_range, Finset.sum_range]
    simp only [Algebra.smul_def]
    rfl
  simpa only [hx] using this
end GlobalTheory.ResultantNorm
