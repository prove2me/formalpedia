-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.exists_isUniv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:47.489646+00:00
-- url     : https://prove2.me/submissions/4dfc3405-a046-4673-ac4f-a912ed6df066

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_subsetPoly_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_exists_fin_enum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubsetSum
namespace GlobalTheory.CompanionTheory.SubsetSum
theorem _root_.solution (n r : ℕ) : ∃ Φ, IsUniv n r Φ := by
  classical
  let M₀ : Multiset (MvPolynomial (Fin n) ℤ) := Finset.univ.val.map MvPolynomial.X
  let f : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℤ :=
    (MvPolynomial.aeval fun i : Fin n => MvPolynomial.esymm (Fin n) ℤ (i + 1)).toRingHom
  have hsym : ∀ k, (subsetPoly r M₀).coeff k ∈ Set.range f := by
    intro k
    have hs : ((subsetPoly r M₀).coeff k).IsSymmetric := by
      intro e
      have hM : M₀.map (MvPolynomial.rename e : _ →ₐ[ℤ] _).toRingHom = M₀ := by
        have : M₀ = (Finset.univ.val.map e).map MvPolynomial.X := by
          rw [Multiset.map_univ_val_equiv]
        conv_rhs => rw [this]
        simp only [M₀, Multiset.map_map]
        apply Multiset.map_congr rfl
        intro i _
        simp
      have := subsetPoly_map (MvPolynomial.rename e : _ →ₐ[ℤ] _).toRingHom r M₀
      rw [hM] at this
      conv_rhs => rw [← this]
      rw [coeff_map]
      rfl
    obtain ⟨q, hq⟩ := (MvPolynomial.esymmAlgEquiv (Fin n) ℤ (Fintype.card_fin n)).surjective
      ⟨_, hs⟩
    refine ⟨q, ?_⟩
    have := congrArg Subtype.val hq
    exact (MvPolynomial.esymmAlgHom_apply q).symm.trans this
  obtain ⟨Φ, hΦ⟩ := (mem_lifts _).1 ((lifts_iff_coeff_lifts _).2 hsym)
  refine ⟨Φ, ?_⟩
  intro R _ M hM
  obtain ⟨x, rfl⟩ := exists_fin_enum M n hM
  let g : MvPolynomial (Fin n) ℤ →+* R := (MvPolynomial.aeval x : _ →ₐ[ℤ] R).toRingHom
  have h1 : M₀.map g = Finset.univ.val.map x := by
    simp only [M₀, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i _
    simp [g]
  have h2 : g.comp f = evalCoef n ((Finset.univ.val.map x).map fun x => X + C x).prod := by
    apply MvPolynomial.ringHom_ext
    · intro k; simp [evalCoef]
    · intro j
      have hj := j.2
      have hcard : Multiset.card (Finset.univ.val.map x) = n := hM
      simp only [RingHom.comp_apply, evalCoef, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [Multiset.prod_X_add_C_coeff _ (by omega), hcard,
        show n - (n - ((j : ℕ) + 1)) = j + 1 by omega]
      simp [f, g, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  rw [← h2, ← Polynomial.map_map, hΦ, subsetPoly_map, h1]
end GlobalTheory.CompanionTheory.SubsetSum
