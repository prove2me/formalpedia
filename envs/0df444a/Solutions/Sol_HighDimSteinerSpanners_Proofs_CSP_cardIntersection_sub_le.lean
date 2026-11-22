-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.cardIntersection_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:03.489603+00:00
-- url     : https://prove2.me/submissions/30d54a10-67dc-482e-961c-74c7fe59b899

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {α : Type*} [DecidableEq α] (M A B : Finset α) (r : ℕ)
    (h : (A.card : ℝ) - 11 / 40 * r ≤ B.card) :
    (M ∩ A).card - (11 * r) / 40 ≤ B.card := by
  have h40 : (40 : ℝ) * A.card ≤ 40 * B.card + 11 * r := by linarith
  have h40_nat : 40 * A.card ≤ 40 * B.card + 11 * r := by exact_mod_cast h40
  have hMA : (M ∩ A).card ≤ A.card := Finset.card_le_card Finset.inter_subset_right
  omega
end HighDimSteinerSpanners.Proofs.CSP
