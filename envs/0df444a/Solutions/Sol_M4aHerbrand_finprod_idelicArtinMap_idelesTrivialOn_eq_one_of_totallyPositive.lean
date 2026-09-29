-- Prove2me | solution 1 for M4aHerbrand.finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/788275b3-6906-556f-a09d-a0d3e4669b29

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_HeckeCharacter_archSign_unitsMap_algebraMap_mul_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

universe u v

namespace XA

variable {E : Type*} [Field E] [NumberField E]

noncomputable def diag (α : E) (hα : α ≠ 0) : (AdeleRing (𝓞 E) E)ˣ :=
  Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) (Units.mk0 α hα)

theorem diag_mem_principalIdeles (α : E) (hα : α ≠ 0) : diag α hα ∈ principalIdeles (𝓞 E) E := ⟨Units.mk0 α hα, rfl⟩

theorem coe_finPart_diag (α : E) (hα : α ≠ 0) (v : HeightOneSpectrum (𝓞 E)) :
    ((finPart v (diag α hα) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) α := rfl

theorem fst_diag (α : E) (hα : α ≠ 0) : ((diag α hα : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).1 = algebraMap E (InfiniteAdeleRing E) α := rfl

theorem finite_valued_ne_one (α : E) (hα : α ≠ 0) :
    {v : HeightOneSpectrum (𝓞 E) | Valued.v (algebraMap E (v.adicCompletion E) α) ≠ 1}.Finite := by
  classical
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 E) α
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hα
    rw [← hab, map_zero, zero_div]
  have hfa : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {a}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha0)
  have hfb : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {b}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0)
  refine (hfa.union hfb).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, Set.mem_union] at hv ⊢
  by_contra h
  rw [not_or] at h
  apply hv
  have hval : Valued.v (algebraMap E (v.adicCompletion E) α) = v.valuation E α :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v α
  rw [hval, ← hab, map_div₀,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 (fun ha => h.1 (Ideal.dvd_span_singleton.2 ha)),
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 (fun hb' => h.2 (Ideal.dvd_span_singleton.2 hb')), div_one]

theorem snd_apply_eq_coe_finPart (u : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    (((u : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v) = ((finPart v u : (v.adicCompletion E)ˣ) : v.adicCompletion E) := rfl

theorem projFin_apply (u : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    ((projFin E u : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) v = ((finPart v u : (v.adicCompletion E)ˣ) : v.adicCompletion E) := rfl

theorem fst_prod_eq_one {ι : Type*} (s : Finset ι) (f : ι → (AdeleRing (𝓞 E) E)ˣ) (h : ∀ i ∈ s, infPart (f i) = 1) :
    (((∏ i ∈ s, f i : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E)).1 = 1 := by
  rw [← coe_infPart_apply, map_prod, Finset.prod_eq_one h, Units.val_one]

theorem apply_eq_one_of_isAdjuster {G : Type*} [CommGroup G] (𝔣 : Ideal (𝓞 E)) (f : HeightOneSpectrum (𝓞 E) → G)
    (r : (AdeleRing (𝓞 E) E)ˣ →* G)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 → r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), f v ^ placeOrd E (projFin E u) v)
    (u : (AdeleRing (𝓞 E) E)ˣ) (hu : IsAdjuster E 𝔣 u 1)
    (hunit : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v ((finPart v u : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1) :
    r u = 1 := by
  rw [hr₄ u hu]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [(placeOrd_eq_zero_iff E (projFin E u) v).2 (by rw [projFin_apply]; exact hunit v), zpow_zero]

end XA

theorem solution
    (E : Type u) (F : Type v) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (α : E) (hpos : ∀ τ : E →+* ℝ, 0 < τ α)
    (x : HeightOneSpectrum (𝓞 E) → (AdeleRing (𝓞 E) E)ˣ)
    (hx : ∀ u : HeightOneSpectrum (𝓞 E), x u ∈ idelesTrivialOn (𝓞 E) E ({u}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hxu : ∀ u : HeightOneSpectrum (𝓞 E),
      ((finPart u (x u) : (u.adicCompletion E)ˣ) : u.adicCompletion E) = algebraMap E (u.adicCompletion E) α) :
    (Function.mulSupport fun u : HeightOneSpectrum (𝓞 E) => r (x u)).Finite ∧
      ∏ᶠ u : HeightOneSpectrum (𝓞 E), r (x u) = 1 := by
  classical

  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  let u₀ : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩
  have hα : α ≠ 0 := by
    intro h
    have := (finPart u₀ (x u₀)).ne_zero
    rw [hxu u₀, h, map_zero] at this
    exact this rfl

  set d := XA.diag α hα with hd
  have hfin_eq : ∀ v : HeightOneSpectrum (𝓞 E), finPart v (x v) = finPart v d := fun v =>
    Units.ext (by rw [hxu v, XA.coe_finPart_diag])
  have hfin_ne : ∀ (u v : HeightOneSpectrum (𝓞 E)), v ≠ u → finPart v (x u) = 1 := fun u v huv =>
    ((mem_idelesTrivialOn_iff _ _).1 (hx u)).2 v (by simpa using huv)
  have hinf : ∀ u : HeightOneSpectrum (𝓞 E), infPart (x u) = 1 := fun u => ((mem_idelesTrivialOn_iff _ _).1 (hx u)).1

  have h𝔣 : 𝔣 ≠ ⊥ := hadm.1
  set S : Finset (HeightOneSpectrum (𝓞 E)) := (Ideal.finite_factors h𝔣).toFinset ∪ (XA.finite_valued_ne_one α hα).toFinset with hS
  have hS𝔣 : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣 → v ∈ S := fun v hv =>
    Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 hv)
  have hSα : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S → Valued.v (algebraMap E (v.adicCompletion E) α) = 1 := fun v hv => by
    by_contra h
    exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))

  have hout : ∀ u : HeightOneSpectrum (𝓞 E), u ∉ S → r (x u) = 1 := by
    intro u hu
    refine XA.apply_eq_one_of_isAdjuster 𝔣 (artinFrob E F) r hr₄ (x u) ⟨fun v hv => ?_, fun τ => ?_⟩ fun v => ?_
    · have hvu : v ≠ u := fun h => hu (h ▸ hS𝔣 v hv)
      have h1 : x u * (Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) 1)⁻¹ = x u := by
        rw [map_one, inv_one, mul_one]
      rw [h1, XA.snd_apply_eq_coe_finPart, hfin_ne u v hvu, Units.val_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le'⟩
    · rw [map_one, inv_one, mul_one]
      exact archSign_of_fst_eq_one E τ (by rw [← coe_infPart_apply, hinf u, Units.val_one])
    · by_cases hvu : v = u
      · subst hvu
        rw [hfin_eq, XA.coe_finPart_diag]
        exact hSα v hu
      · rw [hfin_ne u v hvu, Units.val_one, map_one]

  set P : (AdeleRing (𝓞 E) E)ˣ := ∏ u ∈ S, x u with hP
  have hfinP : ∀ v : HeightOneSpectrum (𝓞 E), finPart v P = if v ∈ S then finPart v d else 1 := by
    intro v
    rw [hP, map_prod]
    split_ifs with hv
    · rw [Finset.prod_eq_single v (fun u _ huv => hfin_ne u v (Ne.symm huv)) (fun h => absurd hv h), hfin_eq]
    · exact Finset.prod_eq_one fun u hu => hfin_ne u v (fun h => hv (h ▸ hu))
  set z : (AdeleRing (𝓞 E) E)ˣ := d * P⁻¹ with hz
  have hfinz : ∀ v : HeightOneSpectrum (𝓞 E), finPart v z = if v ∈ S then 1 else finPart v d := by
    intro v
    rw [hz, map_mul, map_inv, hfinP]
    split_ifs <;> simp
  have hzunit : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v ((finPart v z : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 := by
    intro v
    rw [hfinz]
    split_ifs with hv
    · rw [Units.val_one, map_one]
    · rw [XA.coe_finPart_diag]; exact hSα v hv
  have hzadj : IsAdjuster E 𝔣 z 1 := by
    refine ⟨fun v hv => ?_, fun τ => ?_⟩
    · have h1 : z * (Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) 1)⁻¹ = z := by
        rw [map_one, inv_one, mul_one]
      rw [h1, XA.snd_apply_eq_coe_finPart, hfinz, if_pos (hS𝔣 v hv), Units.val_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le'⟩
    · rw [map_one, inv_one, mul_one, hz, hd, XA.diag, HeckeCharacter.archSign_unitsMap_algebraMap_mul_iff, archSign_inv]
      exact iff_of_true (hpos τ) (archSign_of_fst_eq_one E τ (XA.fst_prod_eq_one S x fun u _ => hinf u))
  have hrz : r z = 1 := XA.apply_eq_one_of_isAdjuster 𝔣 (artinFrob E F) r hr₄ z hzadj hzunit
  have hrd : r d = 1 := hr₁ (XA.diag_mem_principalIdeles α hα)
  have hrP : r P = 1 := by
    have : r d * (r P)⁻¹ = 1 := by rw [← map_inv, ← map_mul, ← hz, hrz]
    rw [hrd, one_mul, inv_eq_one] at this
    exact this

  have hsupp : (Function.mulSupport fun u : HeightOneSpectrum (𝓞 E) => r (x u)) ⊆ ↑S := by
    intro u hu
    by_contra huS
    exact hu (hout u huS)
  refine ⟨S.finite_toSet.subset hsupp, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, ← map_prod, ← hP, hrP]

end S_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
end P2MW
export P2MW.S_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive (solution)
