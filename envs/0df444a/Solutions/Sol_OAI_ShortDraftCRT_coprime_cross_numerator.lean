-- Prove2me | solution 1 for OAI.ShortDraftCRT.coprime_cross_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:00.880199+00:00
-- url     : https://prove2.me/submissions/dbe57f88-c038-40e1-8ecf-230d75c5a4e0

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
theorem _root_.solution
    {R : Type*} [CommRing R] (a c₀ h r : R)
    (hfixed : IsCoprime a c₀)
    (hmoving : IsCoprime h r)
    (hmod : IsCoprime c₀ r) :
    IsCoprime (a * r + h * c₀) (c₀ * r) := by
  have hc₀ : IsCoprime (a * r + h * c₀) c₀ := by
    have hbase : IsCoprime (a * r) c₀ := hfixed.mul_left hmod.symm
    exact (IsCoprime.add_mul_right_left_iff).mpr hbase
  have hr : IsCoprime (a * r + h * c₀) r := by
    have hbase : IsCoprime (h * c₀) r := hmoving.mul_left hmod
    rw [add_comm]
    exact (IsCoprime.add_mul_right_left_iff).mpr hbase
  exact hc₀.mul_right hr
end OAI.ShortDraftCRT
