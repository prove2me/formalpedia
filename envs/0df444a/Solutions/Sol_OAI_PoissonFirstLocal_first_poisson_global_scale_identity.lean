-- Prove2me | solution 1 for OAI.PoissonFirstLocal.first_poisson_global_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:37.160018+00:00
-- url     : https://prove2.me/submissions/efb392ac-d3f6-40f2-8da2-ec794f060f4c

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_PoissonFirstLocal_first_poisson_local_scale_identity
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
    (P : Finset ℕ) (parityBit ε₁ ε₂ : ℕ → Bool) :
    (∏ p ∈ P, localC (parityBit p) (ε₁ p) (ε₂ p) p) *
      (∏ p ∈ P, localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p) *
      (∏ p ∈ P, localJ2 (parityBit p) (ε₁ p) (ε₂ p) p) ^ 2 =
    (∏ p ∈ P, localA (ε₁ p) p) *
      (∏ p ∈ P, localA (ε₂ p) p) *
      (∏ p ∈ P, localS (parityBit p) p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    simp only [Finset.prod_insert hp]
    calc
      (localC (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localC (parityBit q) (ε₁ q) (ε₂ q) q) *
        (localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localCorrectionE (parityBit q) (ε₁ q) (ε₂ q) q) *
        (localJ2 (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localJ2 (parityBit q) (ε₁ q) (ε₂ q) q) ^ 2 =
        (localC (parityBit p) (ε₁ p) (ε₂ p) p *
          localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p *
          localJ2 (parityBit p) (ε₁ p) (ε₂ p) p ^ 2) *
        ((∏ q ∈ P, localC (parityBit q) (ε₁ q) (ε₂ q) q) *
          (∏ q ∈ P, localCorrectionE (parityBit q) (ε₁ q) (ε₂ q) q) *
          (∏ q ∈ P, localJ2 (parityBit q) (ε₁ q) (ε₂ q) q) ^ 2) := by ring
      _ = (localA (ε₁ p) p * localA (ε₂ p) p * localS (parityBit p) p) *
        ((∏ q ∈ P, localA (ε₁ q) q) *
          (∏ q ∈ P, localA (ε₂ q) q) *
          (∏ q ∈ P, localS (parityBit q) q)) := by
        rw [first_poisson_local_scale_identity, ih]
      _ = (localA (ε₁ p) p * ∏ q ∈ P, localA (ε₁ q) q) *
          (localA (ε₂ p) p * ∏ q ∈ P, localA (ε₂ q) q) *
          (localS (parityBit p) p * ∏ q ∈ P, localS (parityBit q) q) := by ring
end OAI.PoissonFirstLocal
