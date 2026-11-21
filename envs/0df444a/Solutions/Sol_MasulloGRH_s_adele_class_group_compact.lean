-- Prove2me | solution 1 for MasulloGRH.s_adele_class_group_compact
-- status  : ACCEPTED   (disprove)
-- author  : @shivm
-- created : 2026-11-21T05:23:34.253888+00:00
-- url     : https://prove2.me/submissions/a3857bf1-152d-4b34-8d56-27f2d275e9f6

import Definitions.Def_MasulloGRH_SAdeles

set_option autoImplicit false


open MasulloGRH NumberField IsDedekindDomain

namespace Aux_MasulloGRH_s_adele_class_group_compact

/-- `2` is not a unit in the ring of integers of a number field. -/
theorem two_not_isUnit (F : Type*) [Field F] [NumberField F] : ¬ IsUnit (2 : 𝓞 F) := by
  intro h
  have h1 : IsUnit (Algebra.norm ℤ (2 : 𝓞 F)) := h.map (Algebra.norm ℤ)
  have h2 : (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 := by simp
  rw [h2, Algebra.norm_algebraMap, RingOfIntegers.rank] at h1
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  rcases Int.isUnit_iff.mp h1 with h3 | h3
  · have h4 : (2 : ℤ) ≤ 2 ^ Module.finrank ℚ F := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Module.finrank ℚ F := pow_le_pow_right₀ (by norm_num) hd
    omega
  · have h4 : (0 : ℤ) < 2 ^ Module.finrank ℚ F := by positivity
    omega

/-- `1/2` is not an `∅`-integer. -/
theorem half_not_mem (F : Type*) [Field F] [NumberField F] :
    ((1 : F) / 2) ∉ (SIntegers (∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set F) := by
  intro h
  have h' : ((1 : F) / 2) ∈ (⊥ : Subalgebra (𝓞 F) F) := by
    have e : SIntegers (∅ : Finset (HeightOneSpectrum (𝓞 F))) = ⊥ := by
      simp only [SIntegers, Finset.coe_empty]
      exact integer_empty (𝓞 F) F
    rw [← e]
    exact h
  rcases Algebra.mem_bot.mp h' with ⟨r, hr⟩
  apply two_not_isUnit F
  refine IsUnit.of_mul_eq_one r ?_
  apply RingOfIntegers.coe_injective
  rw [map_mul, map_one, hr]
  have e2 : (algebraMap (𝓞 F) F) 2 = (2 : F) := map_ofNat _ 2
  rw [e2]
  norm_num

theorem not_injective (F : Type*) [Field F] [NumberField F] :
    ¬ Function.Injective (fun x : SAdeleRing F (∅ : Finset (HeightOneSpectrum (𝓞 F))) ⧸
        sIntegerLattice (∅ : Finset (HeightOneSpectrum (𝓞 F))) => (2 : ℕ) • x) := by
  intro hinj
  set L := sIntegerLattice (∅ : Finset (HeightOneSpectrum (𝓞 F)))
  set x : SAdeleRing F (∅ : Finset (HeightOneSpectrum (𝓞 F))) ⧸ L :=
    QuotientAddGroup.mk (sDiagonal (∅ : Finset (HeightOneSpectrum (𝓞 F))) ((1 : F) / 2))
  have hone : sDiagonal (∅ : Finset (HeightOneSpectrum (𝓞 F))) (1 : F) ∈ L :=
    ⟨1, (SIntegers (∅ : Finset (HeightOneSpectrum (𝓞 F)))).one_mem, rfl⟩
  have h2x : (2 : ℕ) • x = (2 : ℕ) • (0 : SAdeleRing F (∅ : Finset (HeightOneSpectrum (𝓞 F))) ⧸ L) := by
    rw [smul_zero]
    simp only [x, ← QuotientAddGroup.mk_nsmul]
    rw [QuotientAddGroup.eq_zero_iff]
    have : (2 : ℕ) • sDiagonal (∅ : Finset (HeightOneSpectrum (𝓞 F))) ((1 : F) / 2) =
        sDiagonal (∅ : Finset (HeightOneSpectrum (𝓞 F))) (1 : F) := by
      rw [← map_nsmul]
      congr 1
      rw [nsmul_eq_mul]
      push_cast
      field_simp
    rw [this]
    exact hone
  have hx0 : x = 0 := hinj h2x
  rw [QuotientAddGroup.eq_zero_iff] at hx0
  rcases hx0 with ⟨s, hs, hseq⟩
  have hs' : s = (1 : F) / 2 :=
    (sDiagonal (∅ : Finset (HeightOneSpectrum (𝓞 F)))).injective hseq
  have hs2 : s ∈ (SIntegers (∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set F) := hs
  rw [hs'] at hs2
  exact half_not_mem F hs2

end Aux_MasulloGRH_s_adele_class_group_compact

open Aux_MasulloGRH_s_adele_class_group_compact in
theorem solution : ¬ (∀ (F : Type) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ A : Set F, A ⊆ (SIntegers Sf : Set F) → IsClosed (sDiagonal Sf '' A)) ∧
    DiscreteTopology (sIntegerLattice Sf) ∧
    CompactSpace (SAdeleRing F Sf ⧸ sIntegerLattice Sf) ∧
    T2Space (SAdeleRing F Sf ⧸ sIntegerLattice Sf) ∧
    (∀ n : ℕ, 0 < n → Function.Bijective
      (fun x : SAdeleRing F Sf ⧸ sIntegerLattice Sf => n • x))) := by
  intro h
  exact not_injective ℚ
    ((h ℚ ∅).2.2.2.2 2 (by norm_num)).1
