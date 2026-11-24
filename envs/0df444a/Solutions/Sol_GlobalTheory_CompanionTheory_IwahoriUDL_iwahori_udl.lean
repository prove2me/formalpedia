-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.iwahori_udl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:15:16.126122+00:00
-- url     : https://prove2.me/submissions/df49d698-8b21-4b16-8ba4-bcdc293326e9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_exists_udl_of_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwahoriUDL
open Matrix
variable {R : Type*} [CommRing R]
namespace GlobalTheory.CompanionTheory.IwahoriUDL
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ)
    (ϖ : R) (m : ℕ), Irreducible ϖ → 1 ≤ m → ∀ g : Matrix (Fin n) (Fin n) R,
    (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
    ∃ (u d l : Matrix (Fin n) (Fin n) R),
      (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by
  intro R _ _ _ n ϖ m hϖ hm g hg
  have hmem : ϖ ^ m ∈ IsLocalRing.maximalIdeal R :=
    Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) m (by omega)
  have hle : Ideal.span {ϖ ^ m} ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have hI : ∀ x ∈ Ideal.span {ϖ ^ m}, IsUnit (1 + x) := by
    intro x hx
    by_contra hnu
    have h1 : 1 + x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      simpa using Ideal.sub_mem _ h1 (hle hx)
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2
  obtain ⟨u, d, l, hu, hd, hl, h⟩ := exists_udl_of_isUnit _ hI n g hg
  exact ⟨u, d, l, hu.1, hd.1, hl.1, hu.2.1, hu.2.2, hd.2, hl.2.1, hl.2.2, h⟩
end GlobalTheory.CompanionTheory.IwahoriUDL
