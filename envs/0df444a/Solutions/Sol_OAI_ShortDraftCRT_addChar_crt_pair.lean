-- Prove2me | solution 1 for OAI.ShortDraftCRT.addChar_crt_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:16:54.762523+00:00
-- url     : https://prove2.me/submissions/06774005-9d95-4910-a118-338c4dcaefad

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
namespace OAI.ShortDraftCRT
theorem _root_.solution (ψ : AddChar K ℂ) (m n u v z : K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hbez : u * n + v * m = 1) :
    ψ (z / (m * n)) = ψ (u * z / m) * ψ (v * z / n) := by
  rw [← map_add_eq_mul]
  congr 1
  calc
    z / (m * n) = z * (u * n + v * m) / (m * n) := by rw [hbez, mul_one]
    _ = u * z / m + v * z / n := by
      field_simp
end OAI.ShortDraftCRT
