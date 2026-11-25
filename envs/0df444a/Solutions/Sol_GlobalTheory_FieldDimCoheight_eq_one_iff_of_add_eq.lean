-- Prove2me | solution 1 for GlobalTheory.FieldDimCoheight.eq_one_iff_of_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:59:23.218133+00:00
-- url     : https://prove2.me/submissions/ce483644-d963-4908-a2b3-a7498db78c16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfOpenImmersionIntegralSche
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedComplementDimBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoheightEqOneIffClosureDimProjective

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
theorem _root_.solution {c : ℕ∞} {t : WithBot ℕ∞} {e : ℕ}
    (h : (c : WithBot ℕ∞) + t = (e + 1 : ℕ)) : c = 1 ↔ t = e := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h; exact absurd h.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h' : c + t = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have hc : c ≠ ⊤ := by rintro rfl; rw [top_add] at h'; exact ENat.natCast_ne_top _ h'.symm
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h'; exact ENat.natCast_ne_top _ h'.symm
    lift c to ℕ using hc
    lift t to ℕ using ht
    have h'' : c + t = e + 1 := by exact_mod_cast h'
    constructor
    · intro h1
      have : c = 1 := by exact_mod_cast h1
      have : t = e := by omega
      exact_mod_cast this
    · intro h1
      have : t = e := by exact_mod_cast h1
      have : c = 1 := by omega
      exact_mod_cast this
end GlobalTheory.FieldDimCoheight
