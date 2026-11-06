-- Prove2me | solution 1 for OAI.ShortDraftCRT.normalized_crt_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:31.281554+00:00
-- url     : https://prove2.me/submissions/17a215a7-3894-457f-a2bd-43f6c040216e

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Theorems.Thm_OAI_ShortDraftCRT_addChar_crt_pair

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
namespace OAI.ShortDraftCRT
theorem _root_.solution {R : Type*} [CommRing R]
    (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam c₀ r d x u w : R)
    (hlam : ι lam ≠ 0) (hc₀ : ι c₀ ≠ 0) (hr : ι r ≠ 0)
    (hbez : u * r + (lam ^ 3 * w) * c₀ = 1) :
    ψ (-(ι d * (ι x / ι lam ^ 4)) / (ι c₀ * ι r)) =
      ψ (-(ι d * ι u * (ι x / ι lam ^ 4)) / ι c₀) *
        ψ (ι (-d * w * x) / (ι lam * ι r)) := by
  have hbezK : ι u * ι r + ι (lam ^ 3 * w) * ι c₀ = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg ι hbez
  have hsplit := addChar_crt_pair ψ (ι c₀) (ι r) (ι u)
    (ι (lam ^ 3 * w)) (-(ι d * (ι x / ι lam ^ 4))) hc₀ hr hbezK
  rw [hsplit]
  congr 1
  · congr 1
    ring
  · congr 1
    simp only [map_mul, map_pow, map_neg]
    field_simp
end OAI.ShortDraftCRT
