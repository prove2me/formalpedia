-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.homQueries_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:13.742527+00:00
-- url     : https://prove2.me/submissions/c123ac47-54dd-4151-b111-6be5fde2e850

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_ordered_pairs_card
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_homQueryMap_injective

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} : ∀ x : Fin N → Fin q, (homQueries x).card = N.choose 2 := by
  classical
  intro x
  unfold homQueries
  rw [Finset.card_image_of_injective _ (homQueryMap_injective x)]
  have huniv_eq : (Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2)) =
      ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
        (fun uv => uv.1 < uv.2) := by
    ext uv
    simp
  rw [huniv_eq, ordered_pairs_card, Finset.card_univ, Fintype.card_fin]
end HighDimSteinerSpanners.Proofs.CSP
