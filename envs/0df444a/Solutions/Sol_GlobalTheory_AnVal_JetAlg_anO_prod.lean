-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.anO_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:19.126652+00:00
-- url     : https://prove2.me/submissions/a7d06a21-43ec-4d3d-b97f-62594e8f621f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_AnO_zpow
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_origin_mem
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_anO_fr

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
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {n m : ℕ}
variable {K : Type} [Fintype K] {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)}
  {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
namespace GlobalTheory.AnVal.JetAlg
theorem _root_.solution (hφ : ∀ k, Φ.JetMap m (φ k) (Λ k)) (ε : K → ℤ) {j : K → L.L.ι} (h : ⊤ ≤ LB.wchart L.L φ j) :
    AnO fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ε k := by
  classical
  have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ L.L.U (j k) := fun k x _ => by
    have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
    unfold LB.wchart at hx
    exact Set.mem_iInter.1 hx k
  have hne : ∀ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ≠ 0 := fun k => Φ.fr_ne _ _ (origin_mem Φ (hφ k) (hk k))
  have hfr : ∀ k, AnO fun w => Φ.fr (j k) (Λ k w) := fun k => anO_fr Φ (hφ k) (hk k)
  have key : ∀ s : Finset K,
      ContDiffAt ℂ ω (fun v => ∏ k ∈ s, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.prod_empty]
      exact contDiffAt_const
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact (show ContDiffAt ℂ ω (fun v => Φ.fr (j a) (Λ a (colsOf n g v)) ^ ε a) 0 from
        AnO.zpow (hfr a) (hne a) (ε a)).mul ih
  exact key Finset.univ
end GlobalTheory.AnVal.JetAlg
