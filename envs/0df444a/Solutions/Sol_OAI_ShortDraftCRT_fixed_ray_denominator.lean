-- Prove2me | solution 1 for OAI.ShortDraftCRT.fixed_ray_denominator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:10.080786+00:00
-- url     : https://prove2.me/submissions/7e6ea07d-ea96-4588-9d9b-c056a735b126

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Theorems.Thm_OAI_ShortDraftCRT_coprime_cross_num_list
import Theorems.Thm_OAI_ShortDraftCRT_crossDen_eq_product
import Theorems.Thm_OAI_ShortDraftCRT_goodRows_of_pairwise

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
theorem _root_.solution (a c₀ : R) (rows : List (R × R))
    (hbase : IsCoprime a c₀)
    (hfixed : ∀ ph ∈ rows, IsCoprime c₀ ph.1)
    (hfreq : ∀ ph ∈ rows, IsCoprime ph.2 ph.1)
    (hpair : rows.Pairwise fun x y => IsCoprime x.1 y.1) :
    IsCoprime (crossNum a c₀ rows) (crossDen c₀ rows) ∧
      crossDen c₀ rows = c₀ * (rows.map Prod.fst).prod := by
  exact ⟨coprime_cross_num_list a c₀ rows hbase
    (goodRows_of_pairwise c₀ rows hfixed hfreq hpair),
    crossDen_eq_product c₀ rows⟩
end OAI.ShortDraftCRT
