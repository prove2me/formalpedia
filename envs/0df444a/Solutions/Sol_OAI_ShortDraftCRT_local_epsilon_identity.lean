-- Prove2me | solution 1 for OAI.ShortDraftCRT.local_epsilon_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:10.779957+00:00
-- url     : https://prove2.me/submissions/fe374ad5-3b83-469d-938c-ca7205edea45

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCRT
theorem _root_.solution (lam t σ h : K)
    (hlam : lam ≠ 0) (ht : t ≠ 0) (hσ : σ ≠ 0) (hh : h ≠ 0) :
    (-(lam ^ 3 * t * σ)⁻¹) * h⁻¹ * lam ^ 3 =
      -((σ * h)⁻¹) * t⁻¹ := by
  field_simp
end OAI.ShortDraftCRT
