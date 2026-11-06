-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.first_local_identity_canonicalSextic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:18:35.053849+00:00
-- url     : https://prove2.me/submissions/fa1118cb-1581-46ce-8943-d7c4c16f8a77

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_PoissonFirstLocal_first_local_identity_ring
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
    (side parityBit ε₁ ε₂ : Bool) (z : O ⧸ P) :
    PoissonFirstLocal.oldFactorRing side parityBit ε₁ ε₂ z
        (canonicalSextic P hgood) =
      PoissonFirstLocal.newFactorRing parityBit ε₁ ε₂ z
        (canonicalSextic P hgood) := by
  exact PoissonFirstLocal.first_local_identity_ring
    side parityBit ε₁ ε₂ z (canonicalSextic P hgood)
    (canonicalSextic_pow_six P hgood)
end OAI.ActualEisensteinCubic
