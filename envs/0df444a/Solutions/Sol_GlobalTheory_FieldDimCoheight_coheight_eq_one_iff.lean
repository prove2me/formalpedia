-- Prove2me | solution 1 for GlobalTheory.FieldDimCoheight.coheight_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:01:04.788293+00:00
-- url     : https://prove2.me/submissions/a77cb1dc-47be-4409-8afa-03644278f8aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfOpenImmersionIntegralSche
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedComplementDimBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoheightEqOneIffClosureDimProjective
import Theorems.Thm_GlobalTheory_FieldDimCoheight_coheight_add_dim_closure_eq
import Theorems.Thm_GlobalTheory_FieldDimCoheight_eq_one_iff_of_add_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isProper_str


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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory GlobalTheory.FieldDimCoheight
namespace GlobalTheory.FieldDimCoheight
theorem _root_.solution : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F)
    (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ z : X,
    Order.coheight z = 1 ↔ topologicalKrullDim (closure ({z} : Set X)) = e := by
  intro F _ X _ p e hp hd z
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  exact eq_one_iff_of_add_eq ((coheight_add_dim_closure_eq F X p z).trans hd)
end GlobalTheory.FieldDimCoheight
