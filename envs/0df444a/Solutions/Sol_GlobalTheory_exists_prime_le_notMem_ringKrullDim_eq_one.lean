-- Prove2me | solution 1 for GlobalTheory.exists_prime_le_notMem_ringKrullDim_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:24.845846+00:00
-- url     : https://prove2.me/submissions/c4a514a3-fe21-40d4-9720-82d9ed010c3c

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
import Theorems.Thm_GlobalTheory_exists_mem_height_map_le_one
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field
import Theorems.Thm_ReciprocityTheory_CA_height_eq_of_isMaximal_of_trdeg_eq_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → h ∈ m →
      ∃ p : Ideal B, p.IsPrime ∧ p ≤ m ∧ h ∉ p ∧ ringKrullDim (B ⧸ p) = 1 := by
  intro k _ _ B _ _ _ _ m h hm h0 hhm
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨q, hq, hqm, h1⟩ := exists_mem_height_map_le_one m
    (PrimeSpectrum.basicOpen h).isOpen ⟨⟨⊥, inferInstance⟩, by simpa using h0, bot_le⟩
  have hq' : h ∉ q.asIdeal := hq
  refine ⟨q.asIdeal, q.isPrime, hqm, hq', ?_⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hmax : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have h2 : (m.map (Ideal.Quotient.mk q.asIdeal)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro e
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk q.asIdeal) hhm
    rw [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hq' this
  have h3 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := B ⧸ q.asIdeal)
  have h4 := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field s hs2
    (m.map (Ideal.Quotient.mk q.asIdeal))
  rw [h3] at h4
  have h5 : s = 1 := by exact_mod_cast h4.symm
  rw [hs1, h5]
  rfl
end GlobalTheory
