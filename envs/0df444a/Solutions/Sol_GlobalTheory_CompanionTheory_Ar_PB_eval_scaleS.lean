-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.eval_scaleS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:42.832279+00:00
-- url     : https://prove2.me/submissions/f17b29ee-16c2-4ad6-9efc-d6489ca00924

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsTwiceDifferentiableAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {D N : ℕ} {Ψ : Type} [Fintype Ψ] {S : AnSys D (Option (Ψ × Fin N))} {P : Ideal (MRing ι)}
  (Re : Realis S P) (II : IntersectionSystem)
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution {τ : Type} (k : ℕ) (Q : MvPolynomial (Option τ) ℝ) (lam : τ → ℝ) (s : ℝ) :
    eval (fun o : Option τ => o.elim s lam) (scaleS k Q) = eval (fun o : Option τ => o.elim (s / k) lam) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [scaleS]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p o hp =>
    simp only [map_mul, hp, eval_X]
    congr 1
    cases o <;> simp [scaleS, div_eq_inv_mul]
end GlobalTheory.CompanionTheory.Ar.PB
