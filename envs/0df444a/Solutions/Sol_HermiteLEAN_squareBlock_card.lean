-- Prove2me | solution 1 for HermiteLEAN.squareBlock_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:25.941842+00:00
-- url     : https://prove2.me/submissions/cf6589fb-9975-4bf1-87d3-5ef725de1e6a

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset Filter
open scoped BigOperators ComplexConjugate Topology
noncomputable section
open HermiteLEAN
namespace HermiteLEAN
theorem _root_.solution (ℓ : ℕ) : (squareBlock ℓ).card = 2 * ℓ + 1 := by
  rw [squareBlock, Nat.card_Ico]
  ring_nf
  omega
end HermiteLEAN
