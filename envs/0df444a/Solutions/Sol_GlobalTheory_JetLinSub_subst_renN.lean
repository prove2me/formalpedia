-- Prove2me | solution 1 for GlobalTheory.JetLinSub.subst_renN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:22:35.939195+00:00
-- url     : https://prove2.me/submissions/b14c26dd-a393-4603-8f53-5d7f98769aeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Theorems.Thm_GlobalTheory_JetLinSub_psJet_X
import Theorems.Thm_GlobalTheory_JetLinSub_jetOf_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetOf_comp_anLin


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
namespace GlobalTheory.JetLinSub
theorem _root_.solution {n n' g m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (a : Jet ℂ (Fin 1 × Fin (n * g)) m) :
    σ (renN n g m a) = renN n' g m (jetMap (anLin (flatL B)) (anLin_mem _) a) := by
  have key : (σ.comp (renN n g m)).comp (Ideal.Quotient.mkₐ ℂ _) =
      ((renN n' g m).comp (jetMap (m := m) (anLin (flatL B)) (anLin_mem _))).comp (Ideal.Quotient.mkₐ ℂ _) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, k⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have e1 : renN n g m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), k))) =
        psJet m (MvPowerSeries.X (finProdFinEquiv.symm k)) := by
      rw [psJet_X]
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
      rw [MvPolynomial.aeval_X]
    have hθ : ContDiffAt ℂ ω (fun v : Fin (n * g) → ℂ => v k) 0 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) k).contDiff.contDiffAt
    have e2 := jetOf_comp_anLin m hθ (flatL B)
    rw [jetOf_coord] at e2
    show σ (renN n g m (Ideal.Quotient.mk _ _)) =
      renN n' g m (jetMap (m := m) (anLin (flatL B)) (anLin_mem _) (Ideal.Quotient.mk _ _))
    rw [e1, hσ, ← e2]
    rfl
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact DFunLike.congr_fun key p
end GlobalTheory.JetLinSub
