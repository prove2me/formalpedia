-- Prove2me | solution 1 for GlobalTheory.Reg.ChartInt.chval_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:12.457948+00:00
-- url     : https://prove2.me/submissions/0bc6dccc-4a7d-4a79-9214-67b4e96d3573

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
import Theorems.Thm_GlobalTheory_Reg_ChartInt_nval_nonneg
import Theorems.Thm_GlobalTheory_Reg_ChartInt_nval_unit
import Theorems.Thm_GlobalTheory_Reg_ChartInt_chval_eq

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
variable {A : Type} [CommRing A] [IsDomain A]
namespace GlobalTheory.Reg.ChartInt
theorem _root_.solution (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a s : A)
    (hfs : f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) (hs : φ s ∉ maximalIdeal V) :
    0 ≤ r := by
  have hs0 : φ s ≠ 0 := fun h0 => hs (h0 ▸ (maximalIdeal V).zero_mem)
  rw [chval_eq φ e f r h a s hfs hs0, nval_unit e _ hs, sub_zero]
  exact nval_nonneg e _
end GlobalTheory.Reg.ChartInt
