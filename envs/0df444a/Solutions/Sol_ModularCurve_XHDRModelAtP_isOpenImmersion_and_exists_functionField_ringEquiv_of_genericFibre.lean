-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a81c68f3-cf88-5ed1-9ecd-240dcbe342d6

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre

set_option autoImplicit false
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre.ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP xHFunctionFieldBar qExpFunctionFieldC jqModC JZeroNeronObjectAtP"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "eeta w Meta heeta comp"
namespace GenFibre
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

theorem isLocalization_away_natCast {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) : IsLocalization.Away ((p : ℕ) : ↥A) (AlgebraicClosure ℚ) where
  map_units y := by
    obtain ⟨n, hn⟩ := y.2
    have hp0 : ((p : ℕ) : ↥A) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (y : ↥A) ≠ 0 := by rw [← hn]; exact pow_ne_zero _ hp0
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective (↥A) (AlgebraicClosure ℚ))).mpr this)
  surj z := by
    by_cases hz : z ∈ A
    · exact ⟨(⟨z, hz⟩, 1), by simp⟩

    have hz0 : z ≠ 0 := by rintro rfl; exact hz A.zero_mem
    have hw : z⁻¹ ∈ A := (A.mem_or_inv_mem z).resolve_left hz
    set w : ↥A := ⟨z⁻¹, hw⟩ with hw_def
    have hw0 : w ≠ 0 := by
      intro h; apply hz0; have := congrArg Subtype.val h; simpa [hw_def] using this

    have hpmax : ((p : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      have h1 : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
      rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at h1
      obtain ⟨ha, hmem⟩ := h1
      have : (⟨((p : ℕ) : AlgebraicClosure ℚ), ha⟩ : ↥A) = ((p : ℕ) : ↥A) := Subtype.ext (by push_cast; rfl)
      rw [← this]; exact hmem
    have hrad : ((p : ℕ) : ↥A) ∈ (Ideal.span {w}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro J ⟨hJle, hJprime⟩
      have hJne : J ≠ ⊥ := by
        intro hJ; apply hw0
        have : w ∈ J := hJle (Ideal.subset_span rfl)
        rw [hJ] at this; exact (Submodule.mem_bot ↥A).mp this
      have hJmax : J = IsLocalRing.maximalIdeal ↥A := by
        by_contra hne
        exact hJne (ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime hp A hA J hne)
      rw [hJmax]; exact hpmax
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn

    refine ⟨(a, ⟨((p : ℕ) : ↥A) ^ n, n, rfl⟩), ?_⟩
    show z * algebraMap (↥A) (AlgebraicClosure ℚ) (((p : ℕ) : ↥A) ^ n) = algebraMap (↥A) (AlgebraicClosure ℚ) a
    rw [← ha, map_mul]
    show z * (((a : ↥A) : AlgebraicClosure ℚ) * (z⁻¹)) = ((a : ↥A) : AlgebraicClosure ℚ)
    field_simp
  exists_of_eq {x y} h := ⟨1, by simpa using (IsFractionRing.injective (↥A) (AlgebraicClosure ℚ)) h⟩

end ModularCurve.XHDRModelAtP.GenFibre

open ModularCurve.XHDRModelAtP.GenFibre in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl) :
    IsOpenImmersion gA ∧
    ∃ e : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H),
      ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
        haveI : Nonempty (Scheme.Opens.toScheme U) := by
          obtain ⟨⟨x, hx⟩⟩ := hne
          exact ⟨⟨gA.base x, hx⟩⟩
        e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) =
          𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : IsLocalization.Away ((p : ℕ) : ↥Pl) (AlgebraicClosure ℚ) := isLocalization_away_natCast hp Pl hPl
  have hbar : barPt Pl = Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (AlgebraicClosure ℚ))) := rfl
  haveI hbarOI : IsOpenImmersion (barPt Pl) := by
    rw [hbar]; exact IsOpenImmersion.of_isLocalization ((p : ℕ) : ↥Pl)
  have hcomp : barPt Pl ≫ Spec.map (CommRingCat.ofHom ρ) =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [← hρ, CommRingCat.ofHom_comp, Spec.map_comp]

  have hbig : IsPullback (gA ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) 𝔛.Meta.toBase
      (toBase p (ΓM M H) hj) (barPt Pl ≫ Spec.map (CommRingCat.ofHom ρ)) := by
    rw [hgA₁, hcomp]
    refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso 𝔛.eeta) (by simp) 𝔛.heeta
    rw [Category.assoc, pullback.condition, ← Category.assoc, 𝔛.heeta]
  have hsq : IsPullback gA 𝔛.Meta.toBase (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
      (barPt Pl) :=
    IsPullback.of_right hbig hgA₂ (IsPullback.of_hasPullback _ _)
  have hoi : IsOpenImmersion gA := MorphismProperty.of_isPullback hsq.flip hbarOI
  refine ⟨hoi, ?_⟩

  haveI := hoi
  have hη : gA.base (genericPoint 𝔛.Meta.C) =
      genericPoint ((Limits.pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) : Scheme) :=
    genericPoint_eq_of_isOpenImmersion gA
  let e1 : (Limits.pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk
        (genericPoint ((Limits.pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) : Scheme)) ≅
      (Limits.pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk (gA.base (genericPoint 𝔛.Meta.C)) :=
    (Limits.pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkCongr (.of_eq hη.symm)
  let e2 : (Limits.pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk (gA.base (genericPoint 𝔛.Meta.C)) ≅
      𝔛.Meta.C.presheaf.stalk (genericPoint 𝔛.Meta.C) :=
    asIso (gA.stalkMap (genericPoint 𝔛.Meta.C))
  let e : (Limits.pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H) :=
    ((e1 ≪≫ e2).commRingCatIsoToRingEquiv).trans 𝔛.Meta.ffEquiv.symm
  refine ⟨e, fun U hne a => ?_⟩
  haveI : Nonempty (Scheme.Opens.toScheme U) := by
    obtain ⟨⟨x, hx⟩⟩ := hne
    exact ⟨⟨gA.base x, hx⟩⟩
  change 𝔛.Meta.ffEquiv.symm ((e1.hom ≫ e2.hom).hom
    ((Limits.pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a)) = _
  congr 1
  simp only [e1, e2, TopCat.Presheaf.stalkCongr_hom, asIso_hom, CommRingCat.comp_apply,
    Scheme.germToFunctionField]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [Scheme.Hom.germ_stalkMap_apply]

end S_ModularCurve_XHDRModelAtP_isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre (solution)
