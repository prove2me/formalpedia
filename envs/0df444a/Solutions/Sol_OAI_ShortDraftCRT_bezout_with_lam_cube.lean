-- Prove2me | solution 1 for OAI.ShortDraftCRT.bezout_with_lam_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:30.66621+00:00
-- url     : https://prove2.me/submissions/f9b32401-cbf6-4543-9e3f-2e327afadad1

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
theorem _root_.solution {R : Type*} [CommRing R] (lam c₀ r : R)
    (hcop : IsCoprime r (lam ^ 3 * c₀)) :
    ∃ u v : R,
      u * r + v * c₀ = 1 ∧
      lam ^ 3 ∣ v ∧
      lam ^ 3 * c₀ ∣ u * r - 1 := by
  obtain ⟨u, w, hbez⟩ := hcop
  refine ⟨u, w * lam ^ 3, ?_, ⟨w, by ring⟩, ?_⟩
  · calc
      u * r + (w * lam ^ 3) * c₀ = u * r + w * (lam ^ 3 * c₀) := by ring
      _ = 1 := hbez
  · refine ⟨-w, ?_⟩
    linear_combination hbez
end OAI.ShortDraftCRT
