-- Prove2me | solution 1 for M4aHerbrand.prod_idelicArtinMap_single_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d33d6d2c-fd18-56f8-9b22-918529d89e9d

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_prod_idelicArtinMap_single_eq_one
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (a : Eˣ) (x : HeightOneSpectrum (𝓞 E) → (AdeleRing (𝓞 E) E)ˣ)
    (hx : ∀ v : HeightOneSpectrum (𝓞 E), x v ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hxv : ∀ v : HeightOneSpectrum (𝓞 E), finPart v (x v) = Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a)
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS𝔣 : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣 → v ∈ S)
    (hSa : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S → (v.valuation E) (a : E) = 1) :
    ∏ v ∈ S, r (x v) = 1 := by
  classical

  have nonempty_extension : ∀ v : HeightOneSpectrum (𝓞 E), Nonempty (v.Extension (𝓞 F)) := by
    intro v
    haveI := v.isMaximal
    obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) v.asIdeal
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hP.over, Ideal.under_def]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
    exact ⟨⟨⟨P, hPm.isPrime, hP0⟩, HeightOneSpectrum.ext hP.over.symm⟩⟩

  have false_of_forall_isComplex : ∀ (v : InfinitePlace E), v.IsReal →
      (∀ w : InfinitePlace F, w.comap (algebraMap E F) = v → w.IsComplex) → False := by
    intro v hv hall
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := E) (K := F) v
    have hw' : w.comap (algebraMap E F) = v := hw
    have hnot : ¬ InfinitePlace.IsUnramified E w :=
      InfinitePlace.not_isUnramified_iff.mpr ⟨hall w hw', by rw [hw']; exact hv⟩
    rw [InfinitePlace.isUnramified_iff_stabilizer_eq_bot] at hnot
    exact hnot ((Subgroup.eq_bot_iff_forall _).mpr fun g hg => hinf w g hg)

  set A : (AdeleRing (𝓞 E) E)ˣ := Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) a with hA_def
  set ainf : (AdeleRing (𝓞 E) E)ˣ := (MulEquiv.prodUnits (M := InfiniteAdeleRing E) (N := FiniteAdeleRing (𝓞 E) E)).symm
    (infPart A, 1) with hainf_def
  set P : (AdeleRing (𝓞 E) E)ˣ := ∏ v ∈ S, x v with hP_def
  set u : (AdeleRing (𝓞 E) E)ˣ := A * ainf⁻¹ * P⁻¹ with hu_def

  have hA_fin : ∀ w : HeightOneSpectrum (𝓞 E),
      finPart w A = Units.map (algebraMap E (w.adicCompletion E) : E →* w.adicCompletion E) a :=
    fun w => Units.ext rfl
  have hainf_inf : infPart ainf = infPart A := Units.ext rfl
  have hainf_fin : ∀ w : HeightOneSpectrum (𝓞 E), finPart w ainf = 1 := fun w => Units.ext rfl
  have hainf_snd : ((ainf : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 = 1 := rfl

  have hx_inf : ∀ v : HeightOneSpectrum (𝓞 E), infPart (x v) = 1 := fun v => (hx v).1
  have hx_off : ∀ v w : HeightOneSpectrum (𝓞 E), w ≠ v → finPart w (x v) = 1 :=
    fun v w hvw => (hx v).2 w (Set.mem_compl_singleton_iff.mpr hvw)

  have hu_inf : infPart u = 1 := by
    simp only [hu_def, map_mul, map_inv, hP_def, map_prod, hainf_inf]
    rw [Finset.prod_eq_one (fun v _ => hx_inf v), inv_one, mul_one, mul_inv_cancel]
  have hu_on : ∀ w ∈ S, finPart w u = 1 := by
    intro w hw
    simp only [hu_def, map_mul, map_inv, hP_def, map_prod, hainf_fin, inv_one, mul_one]
    rw [Finset.prod_eq_single_of_mem w hw (fun v _ hvw => hx_off v w hvw.symm), hxv w, hA_fin w, mul_inv_cancel]
  have hu_off : ∀ w, w ∉ S → finPart w u = finPart w A := by
    intro w hw
    simp only [hu_def, map_mul, map_inv, hP_def, map_prod, hainf_fin, inv_one, mul_one]
    rw [Finset.prod_eq_one (fun v hv => hx_off v w (fun h => hw (h ▸ hv))), inv_one, mul_one]

  have hu1 : u * (Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) 1)⁻¹ = u := by
    rw [map_one, inv_one, mul_one]
  have hadj : IsAdjuster E 𝔣 u 1 := by
    refine ⟨fun v hv => ?_, fun τ => ?_⟩
    · rw [hu1]
      have h1 : (((u : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v = 1 := by
        show (finPart v u : v.adicCompletion E) = 1
        rw [hu_on v (hS𝔣 v hv), Units.val_one]
      rw [h1, sub_self, map_one, map_zero]
      exact ⟨rfl, zero_le'⟩
    · rw [hu1]
      exact archSign_of_fst_eq_one E τ (congrArg Units.val hu_inf)
  have hord : ∀ v : HeightOneSpectrum (𝓞 E), placeOrd E (projFin E u) v = 0 := by
    intro v
    rw [placeOrd_eq_zero_iff]
    show Valued.v (finPart v u : v.adicCompletion E) = 1
    by_cases hv : v ∈ S
    · rw [hu_on v hv, Units.val_one, map_one]
    · rw [hu_off v hv, hA_fin v]
      show Valued.v (algebraMap E (v.adicCompletion E) (a : E)) = 1
      rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hSa v hv
  have hr_u : r u = 1 := by
    rw [hr₄ u hadj]
    simp_rw [hord, zpow_zero]
    exact finprod_one

  have hr_A : r A = 1 := hr₁ ⟨a, rfl⟩

  have hainf_norm : ainf ∈ (genuineBaseChange E F).idelicNorm.range := by
    refine M4aHerbrand.AdeleBaseChange.mem_range_idelicNorm_of_forall_exists_norm_eq E F (genuineBaseChange E F) ainf
      (fun v => ?_) (fun v hv hall => (false_of_forall_isComplex v hv hall).elim)
    obtain ⟨w⟩ := nonempty_extension v
    refine ⟨w, 1, ?_⟩
    rw [map_one, hainf_snd]
    rfl
  have hr_ainf : r ainf = 1 := by
    have : ainf ∈ r.ker := by rw [hr₂]; exact Subgroup.mem_sup_right hainf_norm
    exact this

  have hrP : r P = 1 := by
    have h := hr_u
    rw [hu_def, map_mul, map_mul, map_inv, map_inv, hr_A, hr_ainf, inv_one, mul_one, one_mul, inv_eq_one] at h
    exact h
  rw [← map_prod]
  exact hrP

end S_M4aHerbrand_prod_idelicArtinMap_single_eq_one
end P2MW
export P2MW.S_M4aHerbrand_prod_idelicArtinMap_single_eq_one (solution)
