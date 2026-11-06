-- Prove2me | solution 1 for OAI.PoissonFirstLocal.first_poisson_local_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:14:33.327291+00:00
-- url     : https://prove2.me/submissions/96064a52-b5fb-439b-b26b-04be48edcade

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.PoissonFirstLocal
namespace OAI.PoissonFirstLocal
theorem _root_.solution
    (parityBit ε₁ ε₂ : Bool) (p : ℕ) :
    localC parityBit ε₁ ε₂ p * localCorrectionE parityBit ε₁ ε₂ p *
        (localJ2 parityBit ε₁ ε₂ p) ^ 2 =
      localA ε₁ p * localA ε₂ p * localS parityBit p := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;>
    simp [localC, localCorrectionE, localJ2, localS, localA,
      localE, bit,
      show (1 : ZMod 6) ≠ 0 by decide,

      show (3 : ZMod 6) ≠ 0 by decide,
      ] <;> ring_nf <;>
      (intro h; exfalso; revert h; decide)
end OAI.PoissonFirstLocal
