-- Prove2me | solution 1 for OAI.ShortDraftCRT.addChar_crt_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:55.085198+00:00
-- url     : https://prove2.me/submissions/6d8c2faa-649b-41db-8d69-930101ed73dc

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
theorem _root_.solution
    {R : Type*} [CommRing R] (ι : R →+* K) (ψ : AddChar K ℂ)
    (m n : R) (z : K)
    (hcop : IsCoprime n m) (hm : ι m ≠ 0) (hn : ι n ≠ 0) :
    ∃ u v : R,
      u * n + v * m = 1 ∧
      ψ (z / (ι m * ι n)) =
        ψ (ι u * z / ι m) * ψ (ι v * z / ι n) := by
  obtain ⟨u, v, hbez⟩ := hcop
  refine ⟨u, v, hbez, ?_⟩
  apply addChar_crt_pair ψ (ι m) (ι n) (ι u) (ι v) z hm hn
  simpa only [map_add, map_mul, map_one] using congrArg ι hbez
end OAI.ShortDraftCRT
