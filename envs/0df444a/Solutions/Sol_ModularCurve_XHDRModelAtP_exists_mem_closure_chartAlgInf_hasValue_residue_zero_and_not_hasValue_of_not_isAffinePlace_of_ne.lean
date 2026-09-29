-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_mem_closure_chartAlgInf_hasValue_residue_zero_and_not_hasValue_of_not_isAffinePlace_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/26178b81-45ba-5468-b832-1c90153cd4c5

import Theorems.Thm_ModularCurve_XHDRModelAtP_coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHCuspChartSet
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_mem_closure_chartAlgInf_hasValue_residue_zero_and_not_hasValue_of_not_isAffinePlace_of_ne

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws47
namespace B2
open AlgebraicCurve

theorem hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g g' : F} {c c' : K} (h : u.HasValue g c) (h' : u.HasValue g' c') : u.HasValue (g + g') (c + c') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have : (⟨g + g', add_mem hg hg'⟩ : u.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [this, map_add, hr, hr', map_add]

theorem hasValue_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) : u.HasValue (-g) (-c) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have : (⟨-g, neg_mem hg⟩ : u.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [this, map_neg, hr, map_neg]

theorem hasValue_sub {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g g' : F} {c c' : K} (h : u.HasValue g c) (h' : u.HasValue g' c') : u.HasValue (g - g') (c - c') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hasValue_add u h (hasValue_neg u h')

theorem hasValue_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {a : K} (hg : g ∈ u.toValuationSubring)
    (h : g - algebraMap K F a ∈ u.toValuationSubring.nonunits) : u.HasValue g a := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  refine ⟨hg, ?_⟩
  have hsub : (⟨g - algebraMap K F a, hmem⟩ : u.toValuationSubring) = ⟨g, hg⟩ - algebraMap K u.toValuationSubring a :=
    Subtype.ext (by simp)
  have h0 : IsLocalRing.residue u.toValuationSubring ⟨g - algebraMap K F a, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  rw [hsub, map_sub, sub_eq_zero, u.residue_algebraMap] at h0
  exact h0

theorem spec_field_eq {K : Type*} [Field K] (q q' : PrimeSpectrum K) : q = q' := by
  apply PrimeSpectrum.ext
  rw [Ideal.eq_bot_of_prime q.asIdeal, Ideal.eq_bot_of_prime q'.asIdeal]

end Ws47.B2

namespace Ws47
namespace B2
open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel IsLocalRing

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem exists_comp_efib_eq_specMap_comp_iotaInf
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (w : Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)))
    (hw : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w) :
    ∃ β : ↥(chartAlgInf p (ΓN p M H hpM) hj) →+* ResidueField ↥A,
      ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm w).1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _ =
        Spec.map (CommRingCat.ofHom β) ≫ ιInf p (ΓN p M H hpM) hj := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have spec_pt : ∀ q : Spec (CommRingCat.of (ResidueField ↥A)), q = IsLocalRing.closedPoint (ResidueField ↥A) :=
    fun q => spec_field_eq q _
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) _ (jAt (ΓN p M H hpM) hj)
      ((((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm w).1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _).base
        (IsLocalRing.closedPoint (ResidueField ↥A))) with ⟨x₀, hx₀⟩ | ⟨x₀, hx₀⟩
  ·
    exfalso
    have hsub : Set.range (((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm w).1 ≫ 𝔛.efib A hA ρ hρ ≫
        pullback.fst (toBase p (ΓN p M H hpM) hj) _).base ⊆ Set.range (ιFin p (ΓN p M H hpM) hj).base := by
      rintro x ⟨q, rfl⟩
      rw [spec_pt q, ← hx₀]
      exact ⟨x₀, rfl⟩
    obtain ⟨l, hlfac⟩ : ∃ l : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj)),
        l ≫ ιFin p (ΓN p M H hpM) hj = ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm w).1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _ :=
      ⟨IsOpenImmersion.lift _ _ hsub, IsOpenImmersion.lift_fac _ _ _⟩
    have hfac : ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm w).1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _ =
        Spec.map (CommRingCat.ofHom (Spec.preimage l).hom) ≫ ιFin p (ΓN p M H hpM) hj := by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, hlfac]
    have hj1 : coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
    have hj2 : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
    have hj3 : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := map_jqModC _
    have hlift : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ)
        (((TwoChartIntegralModel.jChartFin (R p) _ (jAt (ΓN p M H hpM) hj) : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
          ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := by
      rw [TwoChartIntegralModel.coe_jChartFin, coe_jAt, hj1, hj2]
    obtain ⟨hmem, hO, hnu⟩ := (ModularCurve.XHDRModelAtP.coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq
      p M H hpM hj 𝔛 A hA ρ hρ).1 _ _ hfac _ (jqModC ↥A) hlift
    have hval := hasValue_of_sub_mem_nonunits _ hO hnu
    rw [Equiv.apply_symm_apply] at hval
    exact hw ⟨_, _, hj3, hval⟩
  · have hsub : Set.range (((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm w).1 ≫ 𝔛.efib A hA ρ hρ ≫
        pullback.fst (toBase p (ΓN p M H hpM) hj) _).base ⊆ Set.range (ιInf p (ΓN p M H hpM) hj).base := by
      rintro x ⟨q, rfl⟩
      rw [spec_pt q, ← hx₀]
      exact ⟨x₀, rfl⟩
    obtain ⟨l, hlfac⟩ : ∃ l : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj)),
        l ≫ ιInf p (ΓN p M H hpM) hj = ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm w).1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _ :=
      ⟨IsOpenImmersion.lift _ _ hsub, IsOpenImmersion.lift_fac _ _ _⟩
    refine ⟨(Spec.preimage l).hom, ?_⟩
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hlfac]

end Ws47.B2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (hB : ∀ b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})), α b ∈ Rpd.R₁.integers)
    (v v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hvna : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) v)
    (hv'na : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) v')
    (hne : v' ≠ v) :
    ∃ (b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hb : b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)}))),
      v'.HasValue (Rpd.R₁.residue ⟨α b, hB b hb⟩) (0 : (ResidueField ↥A)) ∧ ¬ v.HasValue (Rpd.R₁.residue ⟨α b, hB b hb⟩) (0 : (ResidueField ↥A)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := 𝔛.efib_iso A hA ρ hρ
  have hRQ : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap (R p) ℚ) = A.subtype.comp ρ := by
    rw [hρ]; exact (IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)).symm
  have hInf := (ModularCurve.XHDRModelAtP.coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq
    p M H hpM hj 𝔛 A hA ρ hρ).2

  obtain ⟨β, hβ⟩ := Ws47.B2.exists_comp_efib_eq_specMap_comp_iotaInf p M H hpM hj 𝔛 A hA ρ hρ v hvna
  obtain ⟨β', hβ'⟩ := Ws47.B2.exists_comp_efib_eq_specMap_comp_iotaInf p M H hpM hj 𝔛 A hA ρ hρ v' hv'na
  have hββ' : β ≠ β' := by
    intro h
    apply hne
    have h1 : ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm v).1 ≫ 𝔛.efib A hA ρ hρ =
        ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm v').1 ≫ 𝔛.efib A hA ρ hρ := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hβ, hβ', h]
      · rw [Category.assoc, Category.assoc, 𝔛.hefib A hA ρ hρ, ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm v).2,
          ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm v').2]
    have h2 := (cancel_mono (𝔛.efib A hA ρ hρ)).mp h1
    have h3 : (𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm v = (𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm v' := Subtype.ext h2
    exact ((𝔛.Mfib A hA ρ hρ).pointEquivPlace.symm.injective h3).symm
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ↥(chartAlgInf p (ΓN p M H hpM) hj), β b₀ ≠ β' b₀ := by
    by_contra h
    push Not at h
    exact hββ' (RingHom.ext h)

  obtain ⟨y₀, hy₀⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj)).2 b₀
  have hyb : coeffMap A.subtype (coeffMap ρ y₀) = coeffEmb (AlgebraicClosure ℚ)
      ((b₀ : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := by
    rw [coeffMap_coeffMap, ← hRQ, ← coeffMap_coeffMap, hy₀]; rfl
  let g₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ⟨coeffEmb (AlgebraicClosure ℚ) ((b₀ : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b₀ : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2⟩
  obtain ⟨a', ha'⟩ := IsLocalRing.residue_surjective (R := ↥A) (β' b₀)
  have hbsep : g₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a' : AlgebraicClosure ℚ) ∈
      Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)}) :=
    sub_mem (Subring.subset_closure (Or.inr ⟨b₀, rfl⟩)) (Subring.subset_closure (Or.inl ⟨a', rfl⟩))
  refine ⟨g₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a' : AlgebraicClosure ℚ), hbsep, ?_⟩

  have hcoe_g₀ : ((α g₀ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (coeffMap ρ y₀) := by
    rw [hα_coe, hyb]
  have hYmem : coeffMap A.subtype (coeffMap ρ y₀) ∈ xHFunctionFieldBar M H := by
    rw [← hcoe_g₀]; exact (α g₀).2
  obtain ⟨h1, hres1⟩ := Rpd.residue₁_coeffMap (coeffMap ρ y₀) hYmem
  have eel : (⟨coeffMap A.subtype (coeffMap ρ y₀), hYmem⟩ : ↥(xHFunctionFieldBar M H)) = α g₀ := Subtype.ext hcoe_g₀.symm
  have hg₀R : α g₀ ∈ Rpd.R₁.integers := eel ▸ h1
  obtain ⟨hmem, hO, hnu⟩ := hInf _ β hβ b₀ (coeffMap ρ y₀) hyb
  obtain ⟨hmem', hO', hnu'⟩ := hInf _ β' hβ' b₀ (coeffMap ρ y₀) hyb
  have hres_g₀ : Rpd.R₁.residue ⟨α g₀, hg₀R⟩ =
      (⟨coeffMap (IsLocalRing.residue ↥A) (coeffMap ρ y₀), hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) := by
    have eint : (⟨α g₀, hg₀R⟩ : Rpd.R₁.integers) = ⟨_, h1⟩ := Subtype.ext eel.symm
    apply Subtype.ext
    rw [eint, hres1]
  have haR : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a' : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers :=
    (Rpd.R₁.algebraMap_mem_iff _).mpr a'.2
  have hres_a : Rpd.R₁.residue ⟨_, haR⟩ = algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) (β' b₀) := by
    have h := Rpd.R₁.residue_algebraMap a'
    rw [h, ha']
  have hαb : α (g₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a' : AlgebraicClosure ℚ)) =
      α g₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a' : AlgebraicClosure ℚ) := by
    rw [map_sub, AlgHom.commutes]
  have hres : Rpd.R₁.residue ⟨α (g₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a' : AlgebraicClosure ℚ)), hB _ hbsep⟩ =
      (⟨coeffMap (IsLocalRing.residue ↥A) (coeffMap ρ y₀), hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) - algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) (β' b₀) := by
    have eint : (⟨α (g₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a' : AlgebraicClosure ℚ)), hB _ hbsep⟩ : Rpd.R₁.integers) =
        ⟨α g₀, hg₀R⟩ - ⟨_, haR⟩ := Subtype.ext hαb
    rw [eint, map_sub, hres_g₀, hres_a]

  have hv1 : v.HasValue (⟨coeffMap (IsLocalRing.residue ↥A) (coeffMap ρ y₀), hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) (β b₀) := by
    have h := Ws47.B2.hasValue_of_sub_mem_nonunits _ hO hnu
    rwa [Equiv.apply_symm_apply] at h
  have hv2 : v'.HasValue (⟨coeffMap (IsLocalRing.residue ↥A) (coeffMap ρ y₀), hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) (β' b₀) := by
    have h := Ws47.B2.hasValue_of_sub_mem_nonunits _ hO' hnu'
    rwa [Equiv.apply_symm_apply] at h
  rw [hres]
  refine ⟨?_, ?_⟩
  · have h := Ws47.B2.hasValue_sub v' hv2 (v'.hasValue_algebraMap (β' b₀))
    rwa [sub_self] at h
  · intro h0
    have h := Ws47.B2.hasValue_sub v hv1 (v.hasValue_algebraMap (β' b₀))
    exact hb₀ (sub_eq_zero.mp (h.unique h0))

end S_ModularCurve_XHDRModelAtP_exists_mem_closure_chartAlgInf_hasValue_residue_zero_and_not_hasValue_of_not_isAffinePlace_of_ne
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_mem_closure_chartAlgInf_hasValue_residue_zero_and_not_hasValue_of_not_isAffinePlace_of_ne (solution)
