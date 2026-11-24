-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:37.413845+00:00
-- url     : https://prove2.me/submissions/b02e3c6c-eabb-4e16-8e0d-c06dd3795725

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_valuation_map_eq_of_unr
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_intMap_of_unr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_intMap_of_unr hU
  have hv := valuation_map_eq_of_unr hU
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hvdef
  set v' := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv'def

  have memK : ∀ a : K.O, a ∈ maximalIdeal K.O ↔ v (algebraMap K.O K.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K.O) a).symm
  have memK' : ∀ a : K'.O, a ∈ maximalIdeal K'.O ↔ v' (algebraMap K'.O K'.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K'.O) a).symm
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal K.O := (mem_maximalIdeal a).2 hna
    have h2 : ψ a ∈ maximalIdeal K'.O := by
      rw [memK', hψ, hv]; exact (memK a).1 h1
    exact (mem_maximalIdeal _).1 h2 ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ψ).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hfr : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have h1 := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    have c1 : Fintype.card (ResidueField K.O) = K.q ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact K.card_res
    have c2 : Fintype.card (ResidueField K'.O) = (K.q ^ 2) ^ d := by
      rw [← Nat.card_eq_fintype_card, K'.card_res, hU.1, ← pow_mul, ← pow_mul, mul_comm]
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← c1]; exact Fintype.one_lt_card
    rw [c1, c2] at h1
    exact (Nat.pow_right_injective h2 h1).symm
  let b := Module.finBasisOfFinrankEq (ResidueField K.O) (ResidueField K'.O) hfr
  choose u hu using fun i => IsLocalRing.residue_surjective (b i)

  have hres : ∀ c : Fin d → K.O, ∀ j, c j = 1 → ∑ i, ψ (c i) * u i ∉ maximalIdeal K'.O := by
    intro c j hj hmem
    have h0 : residue K'.O (∑ i, ψ (c i) * u i) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    rw [map_sum] at h0
    simp only [map_mul, ← ResidueField.map_residue, hu] at h0
    have h1 : ∑ i, residue K.O (c i) • b i = 0 := by
      simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h0
    have := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 j
    rw [hj, map_one] at this
    exact one_ne_zero this

  set U : Fin d → K'.E := fun i => algebraMap K'.O K'.E (u i) with hUdef

  have key : ∀ e : Fin d → K.E, ∀ j, (∀ i, v (e i) ≤ v (e j)) → e j ≠ 0 →
      v (e j) ≤ v' (∑ i, φ (e i) * U i) := by
    intro e j hmax hj
    have hpos : 0 < v (e j) := zero_lt_iff.2 (by simpa using hj)
    have hc : ∀ i, ∃ a : K.O, algebraMap K.O K.E a = e i / e j := fun i =>
      IsDiscreteValuationRing.exists_lift_of_le_one (by
        rw [map_div₀]; exact (div_le_one₀ hpos).2 (hmax i))
    choose a ha using hc
    have haj : a j = 1 := IsFractionRing.injective K.O K.E (by rw [ha, div_self hj, map_one])
    have h1 := hres a j haj
    rw [memK', not_lt] at h1
    have h2 : algebraMap K'.O K'.E (∑ i, ψ (a i) * u i) = ∑ i, φ (e i / e j) * U i := by
      simp only [map_sum, map_mul, hψ, ha, hUdef]
    have h3 : ∑ i, φ (e i) * U i = φ (e j) * ∑ i, φ (e i / e j) * U i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hj]
    rw [h3, map_mul, hv, ← h2]
    exact le_mul_of_one_le_right' h1
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hsmul : ∀ (x : K.E) (y : K'.E), x • y = φ x * y := fun x y => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent K.E U := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i)) ⟨i, Finset.mem_univ i⟩
    have hgi : 0 < v (g i) := zero_lt_iff.2 (by simpa using hi)
    have hgj : g j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd this (not_le.2 hgi)
    have := key g j (fun i => hj i (Finset.mem_univ i)) hgj
    simp only [← hsmul] at this
    rw [hg, map_zero] at this
    exact hgj ((map_eq_zero v).1 (le_antisymm this zero_le'))
  have hd : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : Nonempty (Fin d) := by
    have : 0 < d := hfr ▸ Module.finrank_pos
    exact ⟨⟨0, this⟩⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hd])
  refine ⟨u, fun y => ?_⟩
  have hy : algebraMap K'.O K'.E y ∈ Submodule.span K.E (Set.range U) := hspan ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun K.E).1 hy
  have hint : ∀ i, v (e i) ≤ 1 := by
    intro i
    by_contra hi
    rw [not_le] at hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (e i)) ⟨i, Finset.mem_univ i⟩
    have hej : e j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd (lt_of_lt_of_le hi this) (not_lt.2 zero_le')
    have h1 := key e j (fun i => hj i (Finset.mem_univ i)) hej
    simp only [← hsmul] at h1
    rw [he] at h1
    have h2 := HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K'.O) (K := K'.E) y
    exact absurd (lt_of_lt_of_le hi (le_trans (hj i (Finset.mem_univ i)) (le_trans h1 h2))) (lt_irrefl _)
  choose a ha using fun i => IsDiscreteValuationRing.exists_lift_of_le_one (hint i)
  refine ⟨a, ?_⟩
  rw [← he]
  simp only [hsmul, ha, hUdef]
end GlobalTheory.UnitLemma.Unr
