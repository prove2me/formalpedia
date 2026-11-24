-- Prove2me | solution 1 for GlobalTheory.EtaCard.span_sup_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:54.065859+00:00
-- url     : https://prove2.me/submissions/daa0a788-4468-42be-859b-4b6d9df356f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsNullVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardLevGrpAndSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaCard
namespace GlobalTheory.EtaCard
theorem _root_.solution (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O) (S : Submodule O M)
    (h : S ⊔ Ideal.span {a} • ⊤ = ⊤) (k : ℕ) : S ⊔ Ideal.span {a ^ k} • ⊤ = ⊤ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine eq_top_iff.2 (ih.ge.trans (sup_le le_sup_left ?_))
    have h2 := congrArg (fun T : Submodule O M => Ideal.span {a ^ k} • T) h
    simp only [Submodule.smul_sup, ← Submodule.mul_smul, Ideal.span_singleton_mul_span_singleton,
      ← pow_succ] at h2
    exact h2.ge.trans (sup_le_sup_right Submodule.smul_le_right _)
end GlobalTheory.EtaCard
