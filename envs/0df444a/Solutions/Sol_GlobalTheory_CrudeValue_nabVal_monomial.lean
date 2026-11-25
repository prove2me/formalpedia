-- Prove2me | solution 1 for GlobalTheory.CrudeValue.nabVal_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:22.52122+00:00
-- url     : https://prove2.me/submissions/7420d4b5-f434-4e89-9895-e043d3b2aa6a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.CrudeValue
variable {k : Type} [CommRing k] {d : ℕ}
variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] [Algebra ℚ k] [Algebra R k]
namespace GlobalTheory.CrudeValue
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (e : ι →₀ ℕ) :
    B.nabVal k h w0 q f u (MvPolynomial.monomial e 1) =
      constantCoeff (DmonOf (B.G.mapF (algebraMap R k)) u e
        (f * FB.expS k ((q : k) • B.hL k h w0))) := by
  classical
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  · simp only [FB.nabVal, FB.FK, DpolyOf, MvPolynomial.support_monomial,
      if_neg (one_ne_zero : (1 : k) ≠ 0), Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_true, map_one, one_mul]
end GlobalTheory.CrudeValue
