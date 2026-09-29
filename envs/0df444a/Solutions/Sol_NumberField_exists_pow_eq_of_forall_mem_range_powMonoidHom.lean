-- Prove2me | solution 1 for NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b80e70d0-fd65-5c7d-b00e-fa002324680a

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_ideleBox_le_range_idelicNorm
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_pow_eq
import Theorems.Thm_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_sup_ideleBox_eq_top
import Theorems.Thm_M4aHerbrand_ideleClass_normCoset_index_ne_zero_and_finrank_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_pow_eq_of_forall_mem_range_powMonoidHom
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

namespace P2mS26N2

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial

variable {E : Type*} [Field E] [NumberField E]

theorem nonempty_extension {F : Type*} [Field F] [NumberField F] [Algebra E F]
    (v : HeightOneSpectrum (𝓞 E)) : Nonempty (v.Extension (𝓞 F)) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) v.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply v.ne_bot
    have h1 := hQ.over
    rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 F))] at h1
    exact h1
  exact ⟨⟨⟨Q, hQmax.isPrime, hQ0⟩, HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal]; exact hQ.over.symm)⟩⟩

end P2mS26N2

theorem solution
    (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p E).Nonempty)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)))
    (hSp : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E),
      (p : NumberField.RingOfIntegers E) ∈ v.asIdeal → v ∈ S)
    (hS : M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers E) E ↑S = ⊤)
    (hsurj : ∀ x : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → (v.adicCompletion E)ˣ,
      (∀ v ∈ T, v ∉ S → Valued.v ((x v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1) →
      ∃ s : Eˣ, (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S →
          v.valuation E (s : E) = 1) ∧
        ∀ v ∈ T, v ∉ S → ∃ c : (v.adicCompletion E)ˣ,
          x v * (Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) s)⁻¹ = c ^ p)
    (u : E) (hu : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S → v ∉ T →
      v.valuation E u = 1)
    (huS : ∀ v ∈ S, ∃ b : v.adicCompletion E, algebraMap E (v.adicCompletion E) u = b ^ p)
    (huinf : ∀ w : NumberField.InfinitePlace E, w.IsReal → ∃ b : w.Completion, algebraMap E w.Completion u = b ^ p) :
    ∃ c : E, u = c ^ p := by
  classical
  by_contra hnot

  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C u : Polynomial E) :=
    X_pow_sub_C_irreducible_of_prime hp (fun b hb => hnot ⟨b, hb.symm⟩)
  haveI := Fact.mk hirr
  let M := AdjoinRoot (Polynomial.X ^ p - Polynomial.C u : Polynomial E)
  haveI hsf : (Polynomial.X ^ p - Polynomial.C u : Polynomial E).IsSplittingField E M := isSplittingField_AdjoinRoot_X_pow_sub_C hζ hirr
  haveI : FiniteDimensional E M := Polynomial.IsSplittingField.finiteDimensional M (Polynomial.X ^ p - Polynomial.C u : Polynomial E)
  haveI : IsGalois E M := isGalois_of_isSplittingField_X_pow_sub_C hζ hirr M
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsCyclic (M ≃ₐ[E] M) := isCyclic_of_isSplittingField_X_pow_sub_C hζ hirr M
  have hfin : Module.finrank E M = p := finrank_of_isSplittingField_X_pow_sub_C hζ hirr M
  haveI : NumberField M := NumberField.of_module_finite E M

  let α : M := AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C u : Polynomial E)
  have hα : α ^ p = algebraMap E M u := by
    have h := AdjoinRoot.eval₂_root (Polynomial.X ^ p - Polynomial.C u : Polynomial E)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
    exact h
  have hadj : Algebra.adjoin E {α} = ⊤ := AdjoinRoot.adjoinRoot_eq_top
  have hgen : IntermediateField.adjoin E {α} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin E {α} := by rw [hadj]; trivial
    exact IntermediateField.algebra_adjoin_le_adjoin E _ hx
  have hgenσ : ∀ σ : M ≃ₐ[E] M, σ α = α → σ = 1 := by
    intro σ hσ
    apply AlgEquiv.coe_algHom_injective
    exact AlgHom.ext_of_adjoin_eq_top hadj fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simpa using hσ

  have hpv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S →
      ((p : ℕ) : NumberField.RingOfIntegers E) ∉ v.asIdeal := fun v hv h => hv (hSp v h)

  let B := M4aHerbrand.GenuineDescent.genuineBaseChange E M
  let H : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → Subgroup (v.adicCompletion E)ˣ :=
    fun v => if v ∈ S then ⊤ else (powMonoidHom p : (v.adicCompletion E)ˣ →* (v.adicCompletion E)ˣ).range
  have hW : NumberField.AdeleRing.ideleBox (NumberField.RingOfIntegers E) E ↑(S ∪ T) H ⊤ ≤ B.idelicNorm.range := by
    refine M4aHerbrand.AdeleBaseChange.ideleBox_le_range_idelicNorm E M B (dvd_of_eq hfin) (S ∪ T) H ⊤ ?_ ?_ ?_
    · intro v hv
      by_cases hvS : v ∈ S
      · right
        obtain ⟨w⟩ := P2mS26N2.nonempty_extension (F := M) v
        exact ⟨w, IsDedekindDomain.HeightOneSpectrum.Extension.finrank_adicCompletion_eq_one_of_pow_eq E M hζ u α hα
          hgenσ v (huS v hvS) w⟩
      · left
        simp only [H, if_neg hvS]
        exact le_rfl
    · intro v hv w
      rw [Finset.mem_union, not_or] at hv
      exact IsDedekindDomain.HeightOneSpectrum.Extension.inertia_eq_bot_of_pow_eq E M u α hα hgenσ v
        (hu v hv.1 hv.2) (hpv v hv.1) w
    · intro w hw
      exact absurd (NumberField.InfinitePlace.isUnramifiedIn_of_pow_eq E M hp hζ u α hα hgen w (huinf w)) hw

  have hEW : M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.ideleBox (NumberField.RingOfIntegers E) E ↑(S ∪ T) H ⊤ = ⊤ := by
    refine NumberField.AdeleRing.principalIdeles_sup_ideleBox_eq_top E S (S ∪ T) Finset.subset_union_left hS H
      (fun v hv => by simp only [H, if_pos hv]) ?_
    intro x hx
    obtain ⟨s, hsS, hsT⟩ := hsurj x (fun v hvT hvS => hx v (Finset.mem_union_right S hvT) hvS)
    refine ⟨s, hsS, fun v hv hvS => ?_⟩
    rw [Finset.mem_union] at hv
    obtain ⟨c, hc⟩ := hsT v (hv.resolve_left hvS) hvS
    simp only [H, if_neg hvS]
    exact ⟨c, hc.symm⟩

  have htop : M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔ B.idelicNorm.range = ⊤ :=
    top_le_iff.mp (hEW ▸ sup_le_sup_left hW _)
  have h1 := M4aHerbrand.ideleClass_normCoset_index_ne_zero_and_finrank_dvd E M B
  rw [htop, Subgroup.index_top, hfin] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1.2)

end S_NumberField_exists_pow_eq_of_forall_mem_range_powMonoidHom
end P2MW
export P2MW.S_NumberField_exists_pow_eq_of_forall_mem_range_powMonoidHom (solution)
