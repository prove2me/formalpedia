-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.homQueries_union_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:30.054221+00:00
-- url     : https://prove2.me/submissions/9ccf6dcb-1148-44ae-9e2c-3ab6cd18e979

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_twice_choose_two_int
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_choose_two_le_product
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_ordered_pairs_card
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_homQueryMap_injective
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_homQueries_card

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} (hN_ge1 : 1 ≤ N) : ∀ x y : Fin N → Fin q,
    (homQueries x ∪ homQueries y).card =
      N.choose 2 + dHam x y * (N - 1) - (dHam x y).choose 2 := by
  classical
  intro x y
  let S := disagreeSet x y
  let s := dHam x y
  let A : Finset (Fin N) := Finset.univ \ S
  have hs_eq : S.card = s := rfl
  have hs_le_N : s ≤ N := by
    simpa [hs_eq, Fintype.card_fin] using Finset.card_le_univ S
  have hA_card : A.card = N - s := by
    dsimp [A]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hs_eq]
  have hinter_eq : homQueries x ∩ homQueries y =
      ((A ×ˢ A).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).image
        (fun uv => (uv.1, uv.2, x uv.1, x uv.2)) := by
    ext t
    simp only [Finset.mem_inter, homQueries, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_product, A, Finset.mem_sdiff, S, disagreeSet,
      not_not]
    constructor
    · rintro ⟨⟨uv₁, h₁, rfl⟩, ⟨uv₂, h₂, heq⟩⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨heq1, heq2, heq3, heq4⟩
      refine ⟨uv₁, ⟨⟨?_, ?_⟩, h₁⟩, rfl⟩
      · rw [← heq3, heq1]
      · rw [← heq4, heq2]
    · rintro ⟨uv, ⟨⟨hx1, hx2⟩, huv⟩, rfl⟩
      refine ⟨⟨uv, huv, rfl⟩, ⟨uv, huv, ?_⟩⟩
      rw [hx1, hx2]
  have hinter_card : (homQueries x ∩ homQueries y).card = (N - s).choose 2 := by
    rw [hinter_eq, Finset.card_image_of_injective _ (homQueryMap_injective x),
        ordered_pairs_card, hA_card]
  have hunion_ie := Finset.card_union_add_card_inter (homQueries x) (homQueries y)
  rw [hinter_card, homQueries_card x, homQueries_card y] at hunion_ie
  have hs_choose_le : s.choose 2 ≤ s * (N - 1) := choose_two_le_product s hs_le_N
  have hs_choose_le_tot : s.choose 2 ≤ N.choose 2 + s * (N - 1) :=
    le_trans hs_choose_le (Nat.le_add_left _ _)
  suffices h_int : ((homQueries x ∪ homQueries y).card : ℤ) =
      ((N.choose 2 + s * (N - 1) - s.choose 2 : ℕ) : ℤ) from Int.ofNat.inj h_int
  have hie_int : ((homQueries x ∪ homQueries y).card : ℤ) + ((N - s).choose 2 : ℤ) =
      (N.choose 2 : ℤ) + (N.choose 2 : ℤ) := by exact_mod_cast hunion_ie
  have h2N := twice_choose_two_int N
  have h2s := twice_choose_two_int s
  have h2Ns := twice_choose_two_int (N - s)
  rw [Nat.cast_sub hs_le_N] at h2Ns
  rw [Nat.cast_sub hs_choose_le_tot, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN_ge1]
  push_cast
  have hpoly : ((N : ℤ) - (s : ℤ)) * ((N : ℤ) - (s : ℤ) - 1) +
      ((N : ℤ) * ((N : ℤ) - 1) + 2 * (s : ℤ) * ((N : ℤ) - 1) - (s : ℤ) * ((s : ℤ) - 1)) =
      2 * ((N : ℤ) * ((N : ℤ) - 1)) := by ring
  linarith only [hie_int, h2N, h2s, h2Ns, hpoly]
end HighDimSteinerSpanners.Proofs.CSP
