-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.Resolution.mem_support_iff_eq_addVal_of_comp_toCrossing_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a95ea2ed-5a39-56a5-891d-e9c718ad7871

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry MvPolynomial P2MW.S_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq.MvPolynomial.CrossingQuotient"

universe u

namespace MvPolynomial
p2m_export "MvPolynomial" "map map_injective ext support ringHom_ext comap C map_id CrossingQuotient.mk_C_eq_algebraMap CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient.U_mul_V CrossingQuotient.lift CrossingQuotient.lift_U CrossingQuotient.lift_V CrossingQuotient CrossingQuotient.mk"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "mk_C_eq_algebraMap chartScheme Resolution Resolution.ι Resolution.exists_ι_apply_eq Resolution.toCrossing Resolution.ι_toCrossing Resolution.toSpec Resolution.ι_toSpec U V U_mul_V lift lift_U lift_V resolutionChart resolutionChart_U mk"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq toCrossing ι_toCrossing toSpec ι_toSpec"
namespace SectPos
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

section table

variable (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)))
include hF

theorem ι_apply_mem_support_iff (i : Fin e) (k : Fin (e + 1)) (P : chartScheme t) :
    Resolution.ι t e i P ∈ (F k).support ↔
      (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤) ≤
        P.asIdeal := by
  set J : Ideal (CrossingQuotient W t) :=
    (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤) with hJ
  have h1 : Resolution.ι t e i P ∈ (F k).support ↔ P ∈ ((F k).comap (Resolution.ι t e i)).support := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hbij := (ConcreteCategory.bijective_of_isIso (C := CommRingCat)
    (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv)
  have hpre : ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv : _ → _) ⁻¹'
      (J.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom : Set _) = J := by
    ext c
    simp only [Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hc
      obtain ⟨c', hc', hcc'⟩ := (Ideal.mem_map_iff_of_surjective _ hbij.2).mp hc
      rwa [← hbij.1 hcc']
    · exact Ideal.mem_map_of_mem _
  rw [h1, hF, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus, hpre]
  exact PrimeSpectrum.mem_zeroLocus _ _

theorem specMap_lift_closedPoint_mem_support_iff [IsLocalRing W] (i : Fin e) (k : Fin (e + 1)) (a b : W)
    (hab : a * b = algebraMap W W t) :
    Resolution.ι t e i (Spec.map (CommRingCat.ofHom (CrossingQuotient.lift t a b hab).toRingHom)
        (IsLocalRing.closedPoint W)) ∈ (F k).support ↔
      ((k : ℕ) = i ∧ b ∈ IsLocalRing.maximalIdeal W) ∨ ((k : ℕ) = i + 1 ∧ a ∈ IsLocalRing.maximalIdeal W) := by
  rw [ι_apply_mem_support_iff t e F hF]
  change _ ≤ (IsLocalRing.maximalIdeal W).comap (CrossingQuotient.lift t a b hab).toRingHom ↔ _
  split_ifs with h1 h2
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simp [CrossingQuotient.lift_V, h1]
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simp [CrossingQuotient.lift_U, h2]
  · simp only [h1, h2, false_and, or_self, iff_false, top_le_iff]
    exact Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _)

end table

theorem exists_eq_specMap_lift_comp_ι [IsLocalRing W]
    (s : Spec (CommRingCat.of W) ⟶ Resolution t e) (hst : s ≫ Resolution.toSpec t e = 𝟙 _)
    (ψ : CrossingQuotient W (t ^ e) →+* W)
    (hs : s ≫ Resolution.toCrossing t e = Spec.map (CommRingCat.ofHom ψ)) :
    ∃ (i : Fin e) (a b : W) (hab : a * b = algebraMap W W t),
      Spec.map (CommRingCat.ofHom (CrossingQuotient.lift t a b hab).toRingHom) ≫ Resolution.ι t e i = s ∧
      ψ (CrossingQuotient.U (t ^ e)) = t ^ (i : ℕ) * a := by

  obtain ⟨i, Q, hQ⟩ := Resolution.exists_ι_apply_eq t e (s (IsLocalRing.closedPoint W))
  have hrange : Set.range s.base ⊆ Set.range (Resolution.ι t e i).base := by
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem (f := s) (U := (Resolution.ι t e i).opensRange) ⟨Q, hQ⟩
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ s ⁻¹ᵁ (Resolution.ι t e i).opensRange := by rw [htop]; trivial
    exact hx
  obtain ⟨φ, hφ⟩ : ∃ φ : CommRingCat.of (CrossingQuotient W t) ⟶ CommRingCat.of W,
      Spec.map φ ≫ Resolution.ι t e i = s :=
    ⟨Spec.preimage (IsOpenImmersion.lift (Resolution.ι t e i) s hrange), by
      rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

  have hcomp : CommRingCat.ofHom (resolutionChart t e i).toRingHom ≫ φ = CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hs, ← hφ, Category.assoc, Resolution.ι_toCrossing]

  have hφalg : CommRingCat.ofHom (algebraMap W (CrossingQuotient W t)) ≫ φ = 𝟙 _ := by
    have h1 : Spec.map φ ≫ (Resolution.ι t e i ≫ Resolution.toSpec t e) = 𝟙 _ := by
      rw [← Category.assoc, hφ, hst]
    rw [Resolution.ι_toSpec, ← Spec.map_comp, ← Spec.map_id] at h1
    exact Spec.map_injective h1
  have hw : ∀ w : W, φ.hom (algebraMap W (CrossingQuotient W t) w) = w := fun w => by
    have := congrArg (fun f : CommRingCat.of W ⟶ CommRingCat.of W => f.hom w) hφalg
    simpa using this
  set a : W := φ.hom (CrossingQuotient.U t) with ha
  set b : W := φ.hom (CrossingQuotient.V t) with hb
  have hab : a * b = algebraMap W W t := by
    rw [ha, hb, ← map_mul, CrossingQuotient.U_mul_V, hw]; rfl
  have hφlift : φ = CommRingCat.ofHom (CrossingQuotient.lift t a b hab).toRingHom := by
    ext1
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro w
      change φ.hom (CrossingQuotient.mk t (MvPolynomial.C w)) =
        CrossingQuotient.lift t a b hab (CrossingQuotient.mk t (MvPolynomial.C w))
      rw [CrossingQuotient.mk_C_eq_algebraMap, hw, AlgHom.commutes]; rfl
    · intro n
      fin_cases n
      · change φ.hom (CrossingQuotient.U t) = CrossingQuotient.lift t a b hab (CrossingQuotient.U t)
        rw [CrossingQuotient.lift_U]
      · change φ.hom (CrossingQuotient.V t) = CrossingQuotient.lift t a b hab (CrossingQuotient.V t)
        rw [CrossingQuotient.lift_V]
  refine ⟨i, a, b, hab, hφlift ▸ hφ, ?_⟩

  have hU := congrArg (fun f : CommRingCat.of (CrossingQuotient W (t ^ e)) ⟶ CommRingCat.of W =>
      f.hom (CrossingQuotient.U (t ^ e))) hcomp
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U, map_mul] at hU
  rw [← hU, hw]

end MvPolynomial.CrossingQuotient.Resolution.SectPos

open _root_.MvPolynomial.CrossingQuotient.Resolution _root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq.MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient.Resolution.SectPos in

theorem solution
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ)
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤)))
    (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e) (ht : t ≫ Resolution.toSpec ϖ e = 𝟙 _)
    (ψ : CrossingQuotient O (ϖ ^ e) →+* O)
    (hψ : t ≫ Resolution.toCrossing ϖ e = Spec.map (CommRingCat.ofHom ψ))
    (k : Fin (e + 1)) :
    t.base (IsLocalRing.closedPoint O) ∈ (F k).support ↔
      ((k : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal O (ψ (CrossingQuotient.U (ϖ ^ e))) := by
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  obtain ⟨i, a, b, hab, ht, hA⟩ := exists_eq_specMap_lift_comp_ι ϖ e t ht ψ hψ
  have hpt : t.base (IsLocalRing.closedPoint O) = Resolution.ι ϖ e i
      (Spec.map (CommRingCat.ofHom (CrossingQuotient.lift ϖ a b hab).toRingHom) (IsLocalRing.closedPoint O)) := by
    rw [← ht]; rfl
  rw [hpt, specMap_lift_closedPoint_mem_support_iff ϖ e F hF i k a b hab]
  have hab' : a * b = ϖ := hab
  by_cases hau : IsUnit a
  ·
    have hbm : b ∈ IsLocalRing.maximalIdeal O := by
      rw [hϖ, Ideal.mem_span_singleton']
      exact ⟨((hau.unit⁻¹ : Oˣ) : O), by
        rw [← hab', ← mul_assoc, IsUnit.val_inv_mul, one_mul]⟩
    have ham : a ∉ IsLocalRing.maximalIdeal O := fun h => (IsLocalRing.mem_maximalIdeal _).mp h hau
    have hvA : IsDiscreteValuationRing.addVal O (ψ (CrossingQuotient.U (ϖ ^ e))) = (i : ℕ) := by
      rw [hA, mul_comm, ← IsUnit.unit_spec hau]
      exact IsDiscreteValuationRing.addVal_def' hau.unit hirr i
    rw [hvA]
    simp only [hbm, and_true, ham, and_false, or_false, Nat.cast_inj]
  ·
    have ham : a ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hau)
    rw [hϖ, Ideal.mem_span_singleton'] at ham
    obtain ⟨c, rfl⟩ := ham
    have hϖ0 : ϖ ≠ 0 := hirr.ne_zero
    have hcb : c * b = 1 := by
      have h1 : ϖ * (c * b) = ϖ * 1 := by rw [mul_one, ← mul_assoc, mul_comm ϖ c, hab']
      exact mul_left_cancel₀ hϖ0 h1
    have hbu : IsUnit b := IsUnit.of_mul_eq_one _ ((mul_comm b c).trans hcb)
    have hcu : IsUnit c := IsUnit.of_mul_eq_one _ hcb
    have hbm : b ∉ IsLocalRing.maximalIdeal O := fun h => (IsLocalRing.mem_maximalIdeal _).mp h hbu
    have ham' : c * ϖ ∈ IsLocalRing.maximalIdeal O := by
      rw [hϖ]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self ϖ)
    have hvA : IsDiscreteValuationRing.addVal O (ψ (CrossingQuotient.U (ϖ ^ e))) = ((i : ℕ) + 1 : ℕ) := by
      rw [hA, show ϖ ^ (i : ℕ) * (c * ϖ) = (hcu.unit : O) * ϖ ^ ((i : ℕ) + 1) by
        rw [IsUnit.unit_spec, pow_succ]; ring]
      exact IsDiscreteValuationRing.addVal_def' hcu.unit hirr ((i : ℕ) + 1)
    rw [hvA]
    simp only [hbm, and_false, ham', and_true, false_or, Nat.cast_inj]

end S_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq (solution)
