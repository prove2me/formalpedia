-- Prove2me | solution 1 for GlobalTheory.AnVal.JetUniq.jet_zero_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:27.197418+00:00
-- url     : https://prove2.me/submissions/507bbe13-0f4b-400b-96ae-07c5494c5258

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_IsTayF_eq


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
theorem _root_.solution {κ : Type} (a b : Jet ℂ κ 0)
    (h : (jetAug : Jet ℂ κ 0 →ₐ[ℂ] ℂ) a = (jetAug : Jet ℂ κ 0 →ₐ[ℂ] ℂ) b) : a = b := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hcc : ∀ R : MvPolynomial κ ℂ, MvPolynomial.aeval (fun _ => (0 : ℂ)) R = MvPolynomial.constantCoeff R := by
    intro R
    induction R using MvPolynomial.induction_on <;> simp_all
  change MvPolynomial.aeval (fun _ => (0 : ℂ)) P = MvPolynomial.aeval (fun _ => (0 : ℂ)) Q at h
  rw [hcc, hcc] at h
  rw [Ideal.Quotient.eq, zero_add, pow_one]
  change P - Q ∈ Ideal.span (Set.range MvPolynomial.X)
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro d hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, sub_ne_zero] at hd
    exact hd h
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd0
  exact ⟨i, Set.mem_univ i, hi⟩
end GlobalTheory.AnVal.JetUniq
