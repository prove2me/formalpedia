-- Prove2me | solution 1 for NumberField.PlaceDecomp.finsum_div_natCard_decomp_eq_finrank_smul_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/14c26d10-caf6-55a1-afd4-e37d83e2149c

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_finsum_div_natCard_decomp_eq_finrank_smul_finsum
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_finsum_div_natCard_decomp_eq_finrank_smul_finsum.NumberField IsDedekindDomain M4aHerbrand"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_finsum_div_natCard_decomp_eq_finrank_smul_finsum.NumberField.PlaceDecomp"

set_option linter.unusedSectionVars false

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp natCard_decomp_eq_ramificationIdx_mul_inertiaDeg"
namespace DegreeSum
p2m_open "NumberField.PlaceDecomp NumberField"

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F] (E' : IntermediateField E F)

noncomputable def ef (v' : HeightOneSpectrum (𝓞 ↥E')) : ℕ :=
  Ideal.ramificationIdx' (v'.under (𝓞 E)).asIdeal v'.asIdeal * Ideal.inertiaDeg' (v'.under (𝓞 E)).asIdeal v'.asIdeal

theorem natCard_decomp_eq_ef_mul (v' : HeightOneSpectrum (𝓞 ↥E')) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F (v'.under (𝓞 E)))) =
      ef E F E' v' * Nat.card ↥(NumberField.PlaceDecomp.decomp ↥E' F (NumberField.PlaceAbove.above ↥E' F v')) := by
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  set v : HeightOneSpectrum (𝓞 E) := v'.under (𝓞 E) with hv
  set w' : HeightOneSpectrum (𝓞 F) := NumberField.PlaceAbove.above ↥E' F v' with hw'
  set w : HeightOneSpectrum (𝓞 F) := NumberField.PlaceAbove.above E F v with hw

  have hw'v' : w'.under (𝓞 ↥E') = v' := HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above ↥E' F v')
  have hwv : w.under (𝓞 E) = v := HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above E F v)
  have hw'v : w'.under (𝓞 E) = v := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, ← Ideal.under_under (B := 𝓞 ↥E'), ← HeightOneSpectrum.under_asIdeal,
      ← HeightOneSpectrum.under_asIdeal, hw'v']
  haveI : w'.asIdeal.IsPrime := w'.isPrime
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : v'.asIdeal.IsMaximal := v'.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w'.asIdeal.LiesOver v'.asIdeal := ⟨by rw [← hw'v']; rfl⟩
  haveI : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw'v]; rfl⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hwv]; rfl⟩
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩

  have hD := NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg E F w
  have hD' := NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg ↥E' F w'
  rw [hwv] at hD
  rw [hw'v'] at hD'

  have he : Ideal.ramificationIdx' v.asIdeal w.asIdeal = Ideal.ramificationIdx' v.asIdeal w'.asIdeal := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal (F ≃ₐ[E] F)
  have hf : Ideal.inertiaDeg' v.asIdeal w.asIdeal = Ideal.inertiaDeg' v.asIdeal w'.asIdeal := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal (F ≃ₐ[E] F)

  have het : Ideal.ramificationIdx' v.asIdeal w'.asIdeal = Ideal.ramificationIdx' v.asIdeal v'.asIdeal * Ideal.ramificationIdx' v'.asIdeal w'.asIdeal :=
    Ideal.ramificationIdx_algebra_tower' v.asIdeal v'.asIdeal w'.asIdeal
  have hft : Ideal.inertiaDeg' v.asIdeal w'.asIdeal = Ideal.inertiaDeg' v.asIdeal v'.asIdeal * Ideal.inertiaDeg' v'.asIdeal w'.asIdeal :=
    Ideal.inertiaDeg_algebra_tower v.asIdeal v'.asIdeal w'.asIdeal
  rw [hD, hD', he, hf, het, hft, ef]
  ring

theorem fiber_finite (v : HeightOneSpectrum (𝓞 E)) : {v' : HeightOneSpectrum (𝓞 ↥E') | v'.under (𝓞 E) = v}.Finite := by
  have h : {v' : HeightOneSpectrum (𝓞 ↥E') | v'.under (𝓞 E) = v} = (fun v' => v'.asIdeal) ⁻¹' (v.asIdeal.primesOver (𝓞 ↥E')) := by
    ext v'
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨v'.isPrime, ⟨by rw [← h]; rfl⟩⟩
    · rintro ⟨-, hlo⟩
      apply HeightOneSpectrum.ext
      rw [HeightOneSpectrum.under_asIdeal]
      exact hlo.over.symm
  rw [h]
  exact (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 ↥E')).preimage (fun a _ b _ hab => HeightOneSpectrum.ext hab)

theorem sum_fiber_ef (v : HeightOneSpectrum (𝓞 E)) :
    ∑ v' ∈ (fiber_finite E F E' v).toFinset, ef E F E' v' = Module.finrank E ↥E' := by
  classical
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  rw [← Ideal.sum_ramification_inertia (𝓞 ↥E') E (↥E') (p := v.asIdeal) v.ne_bot]
  have hcoe := IsDedekindDomain.coe_primesOverFinset v.ne_bot (𝓞 ↥E')
  refine Finset.sum_nbij (fun v' => v'.asIdeal) ?_ ?_ ?_ ?_
  · intro v' hv'
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv'
    rw [← Finset.mem_coe, hcoe]
    exact ⟨v'.isPrime, ⟨by rw [← hv']; rfl⟩⟩
  · intro a _ b _ hab
    exact HeightOneSpectrum.ext hab
  · intro P hP
    rw [hcoe] at hP
    have hne : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot hP
    refine ⟨⟨P, hP.1, hne⟩, ?_, rfl⟩
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal]
    exact hP.2.over.symm
  · intro v' hv'
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv'
    rw [ef, hv']

end NumberField.PlaceDecomp.DegreeSum

open NumberField.PlaceDecomp.DegreeSum in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (E' : IntermediateField E F) (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (hfin : (Function.support fun v : HeightOneSpectrum (𝓞 E) =>
      ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))).Finite) :
    (∑ᶠ v' : HeightOneSpectrum (𝓞 ↥E'),
        ((((n (v'.under (𝓞 E)) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥E' F (NumberField.PlaceAbove.above ↥E' F v')) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) =
      Module.finrank E ↥E' •
        (∑ᶠ v : HeightOneSpectrum (𝓞 E),
          ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  set g : HeightOneSpectrum (𝓞 E) → AddCircle (1 : ℚ) := fun v =>
    ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) with hg
  set h : HeightOneSpectrum (𝓞 ↥E') → AddCircle (1 : ℚ) := fun v' =>
    ((((n (v'.under (𝓞 E)) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥E' F (NumberField.PlaceAbove.above ↥E' F v')) : ℚ) : ℚ) : AddCircle (1 : ℚ))) with hh

  have hpt : ∀ v', h v' = ef E F E' v' • g (v'.under (𝓞 E)) := by
    intro v'
    simp only [hh, hg]
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    congr 1
    have hD := natCard_decomp_eq_ef_mul E F E' v'
    have hpos : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F (v'.under (𝓞 E)))) := Nat.card_pos
    have hD'0 : (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥E' F (NumberField.PlaceAbove.above ↥E' F v')) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    have hef : (ef E F E' v' : ℚ) ≠ 0 := by
      have : ef E F E' v' ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hD
        exact hpos.ne' hD
      exact_mod_cast this
    rw [hD, Nat.cast_mul]
    field_simp

  have hgS : Function.support g ⊆ ↑hfin.toFinset := by
    intro v hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hv
  have hT : Function.support h ⊆ ↑(hfin.toFinset.biUnion fun v => (fiber_finite E F E' v).toFinset) := by
    intro v' hv'
    rw [Function.mem_support, hpt] at hv'
    have hgv : g (v'.under (𝓞 E)) ≠ 0 := fun h0 => hv' (by rw [h0, smul_zero])
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨v'.under (𝓞 E), ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]; exact hgv
    · rw [Set.Finite.mem_toFinset]; exact rfl
  rw [finsum_eq_sum_of_support_subset h hT, finsum_eq_sum_of_support_subset g hgS]
  rw [Finset.sum_biUnion]
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [← sum_fiber_ef E F E' v, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro v' hv'
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv'
    rw [hpt, hv']
  · intro v₁ _ v₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro v' h₁ h₂
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h₁ h₂
    exact hne (h₁.symm.trans h₂)

end S_NumberField_PlaceDecomp_finsum_div_natCard_decomp_eq_finrank_smul_finsum
end P2MW
export P2MW.S_NumberField_PlaceDecomp_finsum_div_natCard_decomp_eq_finrank_smul_finsum (solution)
