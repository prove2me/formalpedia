-- Prove2me | solution 1 for GlobalTheory.JetLinSub.jetRd_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:47:55.7528+00:00
-- url     : https://prove2.me/submissions/e2ff650c-d87c-4fdd-ae54-bcfb8301a7b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Theorems.Thm_GlobalTheory_JetLinSub_subst_jetN
import Theorems.Thm_P2M_GlobalTheory_JetLinSub_appTop_to__0f0c9eb1fee2
import Theorems.Thm_GlobalTheory_JetLinSub_res_pull
import Theorems.Thm_GlobalTheory_JetLinSub_jetMap_sub
import Theorems.Thm_GlobalTheory_JetLinSub_jetMap_closedPoint
import Theorems.Thm_GlobalTheory_JetLinSub_contDiffAt_fr

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.JetLinSub
theorem _root_.solution {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    {K : Type} [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetRd m φ ε τ Λ) :
    Φ.JetRd m (fun k => spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε
      (LB.pullGen L.L φ ε τ (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m)))
      (fun k => Λ k ∘ₗ B) := by
  obtain ⟨h1, h2⟩ := h
  have h1' := fun k => jetMap_sub Φ B σ hσ (φ k) (Λ k) (h1 k)
  refine ⟨h1', fun j hj => ?_⟩
  have hU : ∀ k, (Φ.e 0).left PullbackSections.cpt ∈ L.L.U (j k) := fun k => by
    rw [← jetMap_closedPoint Φ _ _ (h1' k)]
    exact (hj.trans (LB.wchart_le _ _ j k)) (Set.mem_univ _)
  have hj0 : ⊤ ≤ LB.wchart L.L φ j := by
    intro y _
    refine Set.mem_iInter.2 fun k => ?_
    have hk : φ k (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) ∈ L.L.U (j k) := by
      rw [jetMap_closedPoint Φ _ _ (h1 k)]; exact hU k
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (Jet ℂ (Fin n × Fin g) m)) (φ k) hk).ge
      (Set.mem_univ y)
  refine (res_pull _ _ _ hj0 hj _ (τ.s j).val).trans ?_
  rw [h2 j hj0, appTop_toΓ]
  congr 1
  exact subst_jetN B σ hσ _ (contDiffAt_prod fun k _ => contDiffAt_fr Φ (j k) (hU k) (ε k) (Λ k))
end GlobalTheory.JetLinSub
