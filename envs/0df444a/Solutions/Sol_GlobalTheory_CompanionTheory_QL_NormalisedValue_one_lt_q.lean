-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.one_lt_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:57.16104+00:00
-- url     : https://prove2.me/submissions/0016a70f-d343-4061-8cc8-75f9c4c5093c

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
theorem _root_.solution (h : LF O ϖ nrm q) : 1 < q := by
  have hq0 : q ≠ 0 := by
    intro hq
    have hp := h.nrm_pi
    rw [hq, Nat.cast_zero, _root_.inv_zero] at hp
    exact h.ne ((AbsoluteValue.eq_zero nrm).1 hp)
  have hq1 : q ≠ 1 := by
    intro hq
    have hc := h.card
    rw [hq] at hc
    have hs := (Nat.card_eq_one_iff_unique.1 hc.symm).1
    exact not_subsingleton (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) hs
  omega
end GlobalTheory.CompanionTheory.QL.NormalisedValue
