-- Prove2me | solution 1 for GlobalTheory.AnValPh1.sameSum_of_jetMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:50:45.486145+00:00
-- url     : https://prove2.me/submissions/34c329eb-be34-485d-8dad-f49d890d7164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProductsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameFirstPartialLawTrivial
import Theorems.Thm_GlobalTheory_AnValPh1_sameSum_of_factor

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
open GlobalTheory GlobalTheory.AnValPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnValPh1
theorem _root_.solution {n : ℕ} (m : ℕ) {K K' J : Type} [Fintype K] [Fintype K'] [Fintype J] [DecidableEq J]
    (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ)
    (Λ : J → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (σ : K → J) (σ' : K' → J)
    (h : ∀ k, Φ.JetMap m (φ k) (Λ (σ k))) (h' : ∀ k, Φ.JetMap m (φ' k) (Λ (σ' k)))
    (hc : ∀ I, (∑ k, if σ k = I then ε k else 0) = ∑ k, if σ' k = I then ε' k else 0) :
    LB.SameSum φ ε φ' ε' := by
  classical
  let F : J → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) := fun I =>
    if hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ I (colsOf n g v))).left) then
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hol m
    else spMap (algebraMap ℂ _) ≫ (Φ.e 0).left
  refine sameSum_of_factor φ ε φ' ε' F σ σ' (fun k => ?_) (fun k => ?_) hc
  · obtain ⟨hol, e⟩ := h k
    simp only [F, dif_pos hol]; exact e
  · obtain ⟨hol, e⟩ := h' k
    simp only [F, dif_pos hol]; exact e
end GlobalTheory.AnValPh1
