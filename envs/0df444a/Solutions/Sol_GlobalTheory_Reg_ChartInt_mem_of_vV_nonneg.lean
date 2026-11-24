-- Prove2me | solution 1 for GlobalTheory.Reg.ChartInt.mem_of_vV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:14.236049+00:00
-- url     : https://prove2.me/submissions/9865e91c-c756-436e-ad4a-98aae0aa994e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IntegralityTrivialValuationsOfNormalAffineCharts
import Theorems.Thm_Formalism_L2_Pj_valV_ne_zero


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
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.ChartInt
open IsLocalRing Formalism.L2.PjFree
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory.Reg.ChartInt
theorem _root_.solution (y : FractionRing V) (hy : y ≠ 0) (h : 0 ≤ vV V y) :
    ∃ w : V, algebraMap V (FractionRing V) w = y := by
  have h0 : valV V y ≠ 0 := valV_ne_zero hy
  have hle : valV V y ≤ 1 := by
    rw [← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one]
    unfold vV at h
    omega
  obtain ⟨w, hw⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V)
    (K := FractionRing V) y (fun v => by
      have hv : v = IsDiscreteValuationRing.maximalIdeal V := by
        have hm : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
        ext1
        exact IsLocalRing.eq_maximalIdeal hm
      rw [hv]
      exact hle)
  exact ⟨w, hw⟩
end GlobalTheory.Reg.ChartInt
