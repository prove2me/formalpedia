-- Prove2me | solution 1 for GlobalTheory.AnVal.JetUniq.renInv_renN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:17.134043+00:00
-- url     : https://prove2.me/submissions/41bbd784-0e0f-48e3-ab90-2facc6bc0624

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf

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
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetUniq
namespace GlobalTheory.AnVal.JetUniq
theorem _root_.solution (n g m : ℕ) (a : Jet ℂ (Fin 1 × Fin (n * g)) m) : renInv n g m (renN n g m a) = a := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hcomp : ((MvPolynomial.aeval fun p : Fin n × Fin g =>
        (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv p) : MvPolynomial (Fin 1 × Fin (n * g)) ℂ)).comp
      (MvPolynomial.aeval fun p : Fin 1 × Fin (n * g) =>
        (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ))) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [Fin.fin_one_eq_zero i]
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.id_apply]
    rw [Equiv.apply_symm_apply]
  change Ideal.Quotient.mk _ ((MvPolynomial.aeval fun p : Fin n × Fin g =>
        (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv p) : MvPolynomial (Fin 1 × Fin (n * g)) ℂ))
      ((MvPolynomial.aeval fun p : Fin 1 × Fin (n * g) =>
        (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ)) P)) = Ideal.Quotient.mk _ P
  rw [← AlgHom.comp_apply, hcomp, AlgHom.id_apply]
end GlobalTheory.AnVal.JetUniq
