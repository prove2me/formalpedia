-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.first_prime_product_canonicalSextic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:39.207234+00:00
-- url     : https://prove2.me/submissions/75ac6c61-940f-43dc-b66b-8dcebe851c6a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_PoissonFirstLocal_first_prime_product_identity_ring
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_six


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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (S : Finset (O ⧸ P))
    (parityBit ε₁ ε₂ : O ⧸ P → Bool) (side : Bool) :
    (∏ z ∈ S,
      PoissonFirstLocal.oldFactorRing side
        (parityBit z) (ε₁ z) (ε₂ z) z
        (canonicalSextic P hgood)) =
      (canonicalSextic P hgood
        (∏ z ∈ S with
          PoissonFirstLocal.retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      PoissonFirstLocal.quotientUnitMask
        (∏ z ∈ S with
          ¬PoissonFirstLocal.retained (parityBit z) (ε₁ z) (ε₂ z), z) := by
  exact PoissonFirstLocal.first_prime_product_identity_ring side S
    parityBit ε₁ ε₂ (canonicalSextic P hgood)
    (canonicalSextic_pow_six P hgood)
end OAI.ActualEisensteinCubic
