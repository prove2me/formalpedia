-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jone_direct_not_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:46:00.2178+00:00
-- url     : https://prove2.me/submissions/b4811984-28ad-4ed1-959f-e63f87e3cb7a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_ShortDraftLocal_direct_theta_jone_not_quadratic


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open OAI.ActualEisensteinCubic
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    canonicalSextic P hgood ≠ (canonicalSextic P hgood) ^ 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hχ₂ : canonicalSextic P hgood ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  exact ShortDraftLocal.direct_theta_jone_not_quadratic
    (canonicalSextic P hgood) hχ₂
end OAI.ActualEisensteinCubic
