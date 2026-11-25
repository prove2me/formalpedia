-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights.unitIndep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:28.902654+00:00
-- url     : https://prove2.me/submissions/abe7fdb3-e491-4319-bb41-3f1006a34ed5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AlgebraicPointWeights
import Theorems.Thm_Formalism_L2_Pj_nval_mul_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
theorem _root_.solution (h₁ : WeightOverFields Xo c) (h₂ : IntegralDiagUnit Xo c) : UnitIndep Xo c := by
  intro a n f hf T io y y' t hb e
  letI := io.toAlgebra
  have hw : evI y' f = wchar (ex Dw a n) t * evI y f := h₁ a n f hf T.Fr t y.1 y'.1 hb
  choose u hu using h₂ T io y y' t hb
  have hU : (wchar (ex Dw a n) t : T.Fr) = algebraMap T.V T.Fr ((∏ i, u i ^ ex Dw a n i : T.Vˣ) : T.V) := by
    simp [wchar, hu]
  rw [hw, hU, nval_mul_unit]
  · exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 (Units.ne_zero _)
  · have : valV T.V (algebraMap T.V T.Fr ((∏ i, u i ^ ex Dw a n i : T.Vˣ) : T.V)) = 1 := by
      unfold valV
      rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h (Units.isUnit _)
    simp only [vV, this, WithZero.log_one, neg_zero]
end GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
