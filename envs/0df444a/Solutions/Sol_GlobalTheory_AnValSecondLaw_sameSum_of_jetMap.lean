-- Prove2me | solution 1 for GlobalTheory.AnValSecondLaw.sameSum_of_jetMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:09.779365+00:00
-- url     : https://prove2.me/submissions/ab85259d-dff8-4f12-bcaa-afb551d0c272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSecondPartialLawTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnValSecondLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
namespace GlobalTheory.AnValSecondLaw
theorem _root_.solution {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)} {ε : K → ℤ}
    {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    {φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)} {ε' : K' → ℤ}
    {Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (h : ∀ k, Φ.JetMap m (φ k) (Λ k)) (h' : ∀ k, Φ.JetMap m (φ' k) (Λ' k))
    (hs : ∀ f : ((Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) → ℤ, ∑ k, ε k * f (Λ k) = ∑ k, ε' k * f (Λ' k)) :
    LB.SameSum φ ε φ' ε' := by
  classical
  intro ψ
  have key : ∀ (χ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) M, Φ.JetMap m χ M → (χ = ψ ↔ Φ.JetMap m ψ M) := by
    rintro χ M ⟨h1, h2⟩
    exact ⟨fun e => ⟨h1, e ▸ h2⟩, fun ⟨_, h4⟩ => h2.trans h4.symm⟩
  have := hs fun M => if Φ.JetMap m ψ M then 1 else 0
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (this.trans (Finset.sum_congr rfl fun k _ => ?_))
  · rw [key _ _ (h k)]
    split_ifs <;> simp
  · rw [key _ _ (h' k)]
    split_ifs <;> simp
end GlobalTheory.AnValSecondLaw
