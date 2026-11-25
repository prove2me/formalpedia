-- Prove2me | solution 1 for GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:56:58.967226+00:00
-- url     : https://prove2.me/submissions/e30d4365-0e80-4e24-a3e1-5ca4d995b3a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemValuationSubringOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralInValuationSubring
namespace GlobalTheory.IntegralInValuationSubring
theorem _root_.solution {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    [Algebra R Ω] (A : ValuationSubring Ω) (h : ∀ r : R, algebraMap R Ω r ∈ A) {b : Ω}
    (hb : IsIntegral R b) : b ∈ A := by
  let f : R →+* A := (algebraMap R Ω).codRestrict A h
  letI : Algebra R A := f.toAlgebra
  haveI : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hA : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hA
  rw [← hy]
  exact y.2
end GlobalTheory.IntegralInValuationSubring
