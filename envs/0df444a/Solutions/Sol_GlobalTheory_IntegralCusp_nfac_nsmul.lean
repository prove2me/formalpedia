-- Prove2me | solution 1 for GlobalTheory.IntegralCusp.nfac_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:09.56723+00:00
-- url     : https://prove2.me/submissions/94e19c56-9c96-4fbf-adab-6b643fb7db84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_BddOfMemHolSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
noncomputable section
open GlobalTheory
open GlobalTheory.IntegralCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.IntegralCusp
namespace _root_.GlobalTheory.IntegralCusp
theorem _root_.solution {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (k : ℕ) (h : ∀ τ i, la' τ i = k * la τ i) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la' x = X.nfac la x ^ k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring
end _root_.GlobalTheory.IntegralCusp
end GlobalTheory.IntegralCusp
