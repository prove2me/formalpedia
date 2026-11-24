-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.IntBasis.exists_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:56.803641+00:00
-- url     : https://prove2.me/submissions/effc4311-4346-47aa-8cff-e694bc161f6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_le_one_iff
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_eq_one_iff
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_map
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_exists_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis
open IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr.IntBasis
theorem _root_.solution (h : IsUnrExt K K' d φ) :
    ∃ w : Fin d → K'.E, ∀ (a : Fin d → K.E) (m : Fin d), (∀ k, adicVal K (a k) ≤ adicVal K (a m)) →
      adicVal K' (∑ k, φ (a k) * w k) = adicVal K (a m) := by
  obtain ⟨ι, hι⟩ := exists_lift h
  haveI : IsLocalHom ι := ⟨fun a ha => by
    rw [← adicVal_eq_one_iff] at ha ⊢; rwa [hι, adicVal_map h] at ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ι).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hf : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have hc := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, K'.card_res, K.card_res, h.1, ← pow_mul,
      mul_comm, pow_mul] at hc
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← K.card_res]; exact Finite.one_lt_card
    exact (Nat.pow_right_injective h2 hc).symm
  haveI : Module.Finite (ResidueField K.O) (ResidueField K'.O) := Module.Finite.of_finite
  let bk := Module.finBasisOfFinrankEq _ _ hf
  choose w' hw' using fun i => residue_surjective (bk i)
  refine ⟨fun i => algebraMap K'.O K'.E (w' i), fun a m hm => ?_⟩
  by_cases ham : a m = 0
  · have h0 : ∀ k, a k = 0 := fun k => by
      have := hm k; rw [ham, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
    simp [h0]
  have hb : ∀ k, ∃ b : K.O, algebraMap K.O K.E b = a k / a m := fun k =>
    (adicVal_le_one_iff K _).1 (by rw [map_div₀]; exact div_le_one_of_le₀ (hm k) zero_le')
  choose b hb using hb
  have hbm : b m = 1 := IsFractionRing.injective K.O K.E (by rw [hb, div_self ham, map_one])
  set s : K'.O := ∑ k, ι (b k) * w' k with hs
  have hsum : ∑ k, φ (a k) * algebraMap K'.O K'.E (w' k) = φ (a m) * algebraMap K'.O K'.E s := by
    rw [hs, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hι, hb, map_div₀, ← mul_assoc, mul_div_cancel₀ _ ((map_ne_zero φ).2 ham)]
  have hres : residue K'.O s ≠ 0 := by
    have e1 : residue K'.O s = ∑ k, residue K.O (b k) • bk k := by
      rw [hs, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hw', Algebra.smul_def, RingHom.algebraMap_toAlgebra, ResidueField.map_residue]
    rw [e1]; intro h0
    have := Fintype.linearIndependent_iff.1 bk.linearIndependent _ h0 m
    rw [hbm, map_one] at this; exact one_ne_zero this
  have hsu : IsUnit s := by
    by_contra hn
    exact hres ((residue_eq_zero_iff s).2 ((mem_maximalIdeal s).2 hn))
  rw [hsum, Valuation.map_mul, (adicVal_eq_one_iff K' s).2 hsu, mul_one, adicVal_map h]
end GlobalTheory.UnitLemma.Unr.IntBasis
