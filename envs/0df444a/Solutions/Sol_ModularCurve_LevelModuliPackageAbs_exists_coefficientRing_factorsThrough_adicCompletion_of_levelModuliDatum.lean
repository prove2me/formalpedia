-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_coefficientRing_factorsThrough_adicCompletion_of_levelModuliDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/232347ef-10b6-5875-b80b-eecc29183500

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs

import Theorems.Thm_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
import Theorems.Thm_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField
import Theorems.Thm_IsDiscreteValuationRing_ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_coefficientRing_factorsThrough_adicCompletion_of_levelModuliDatum
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

open ModularCurve IsLocalRing

set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime]

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Finite (ResidueField A₀)]

    {D : LevelModuliDatum.{0} A₀} (P₀ : LevelModuliPackageAbs A₀ D) [Algebra.FiniteType A₀ P₀.B₀]
    (𝔪 : Ideal P₀.B₀) [𝔪.IsMaximal] (hq𝔪 : algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔪) :
    letI : Field (P₀.B₀ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    ∃ (_ : IsLocalRing (AdicCompletion 𝔪 P₀.B₀)) (_ : IsNoetherianRing (AdicCompletion 𝔪 P₀.B₀))
      (_ : IsAdicComplete (maximalIdeal (AdicCompletion 𝔪 P₀.B₀)) (AdicCompletion 𝔪 P₀.B₀))
      (_ : IsScalarTower A₀ P₀.B₀ (AdicCompletion 𝔪 P₀.B₀))
      (resR : AdicCompletion 𝔪 P₀.B₀ →+* P₀.B₀ ⧸ 𝔪) (_ : Function.Surjective resR)
      (_ : RingHom.ker resR = maximalIdeal (AdicCompletion 𝔪 P₀.B₀))
      (_ : resR.comp (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀)) = Ideal.Quotient.mk 𝔪)
      (W₀ : Type) (_ : CommRing W₀) (_ : IsDomain W₀) (_ : IsDiscreteValuationRing W₀)
      (_ : IsAdicComplete (maximalIdeal W₀) W₀) (_ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
      (res₀ : W₀ →+* P₀.B₀ ⧸ 𝔪) (_ : Function.Surjective res₀) (_ : RingHom.ker res₀ = maximalIdeal W₀)
      (_ : Algebra W₀ (AdicCompletion 𝔪 P₀.B₀)) (_ : Algebra A₀ W₀) (_ : IsScalarTower A₀ W₀ (AdicCompletion 𝔪 P₀.B₀))
      (_ : ∀ w : W₀, resR (algebraMap W₀ (AdicCompletion 𝔪 P₀.B₀) w) = res₀ w),
      CharP (P₀.B₀ ⧸ 𝔪) q ∧
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* P₀.B₀ ⧸ 𝔪), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀) b)) →
          ∃! Φ : AdicCompletion 𝔪 P₀.B₀ →ₐ[W₀] T,
            (∀ r : AdicCompletion 𝔪 P₀.B₀, resT (Φ r) = resR r) ∧
            ∀ b : P₀.B₀, Φ (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀) b) = φ b := by
  classical
  letI instF : Field (P₀.B₀ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : IsNoetherianRing P₀.B₀ := Algebra.FiniteType.isNoetherianRing A₀ P₀.B₀
  have hqprime : q.Prime := Fact.out

  obtain ⟨instLoc, instNoe, instCpl, hmax, hsurj, hker, hlift⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing P₀.B₀ 𝔪

  let eκ : ResidueField (AdicCompletion 𝔪 P₀.B₀) ≃+* P₀.B₀ ⧸ 𝔪 :=
    (RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hker)
  let resR : AdicCompletion 𝔪 P₀.B₀ →+* P₀.B₀ ⧸ 𝔪 := eκ.toRingHom.comp (residue (AdicCompletion 𝔪 P₀.B₀))
  have hresR : Function.Surjective resR := eκ.surjective.comp residue_surjective
  have hkerR : RingHom.ker resR = maximalIdeal (AdicCompletion 𝔪 P₀.B₀) := by
    ext r; simp only [resR, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_eq_zero_iff _ eκ.injective, residue_eq_zero_iff]
  have hrescomp : resR.comp (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀)) = Ideal.Quotient.mk 𝔪 := by
    ext b
    simp only [resR, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, eκ,
      RingEquiv.coe_trans]
    have : (RingHom.quotientKerEquivOfSurjective hsurj).symm
        ((residue (AdicCompletion 𝔪 P₀.B₀)) (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀) b)) = Ideal.Quotient.mk _ b := by
      rw [RingEquiv.symm_apply_eq]; exact (RingHom.quotientKerEquivOfSurjective_apply_mk hsurj b).symm
    rw [this, Ideal.quotEquivOfEq_mk]
  have hresR_alg : ∀ b : P₀.B₀, resR (algebraMap P₀.B₀ (AdicCompletion 𝔪 P₀.B₀) b) = Ideal.Quotient.mk 𝔪 b :=
    fun b => congrArg (fun f : P₀.B₀ →+* P₀.B₀ ⧸ 𝔪 => f b) hrescomp

  haveI instTow : IsScalarTower A₀ P₀.B₀ (AdicCompletion 𝔪 P₀.B₀) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      ext n; simp [AdicCompletion.algebraMap_apply, IsScalarTower.algebraMap_apply A₀ P₀.B₀ (P₀.B₀ ⧸ (𝔪 ^ n • ⊤ : Ideal P₀.B₀))])

  have hqR : algebraMap A₀ (AdicCompletion 𝔪 P₀.B₀) (q : A₀) ∈ maximalIdeal (AdicCompletion 𝔪 P₀.B₀) := by
    rw [IsScalarTower.algebraMap_apply A₀ P₀.B₀, hmax]; exact Ideal.mem_map_of_mem _ hq𝔪
  haveI : IsLocalHom (algebraMap A₀ (AdicCompletion 𝔪 P₀.B₀)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : a ∈ maximalIdeal A₀ := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hna)
    rw [hA₀q, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, rfl⟩ := hmem
    rw [map_mul] at ha
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hqR)) (isUnit_of_mul_isUnit_left ha)

  have hcomap : 𝔪.comap (algebraMap A₀ P₀.B₀) = maximalIdeal A₀ := by
    have hle : maximalIdeal A₀ ≤ 𝔪.comap (algebraMap A₀ P₀.B₀) := by
      rw [hA₀q, Ideal.span_le]; intro x hx; rcases hx with rfl; exact hq𝔪
    exact ((maximalIdeal.isMaximal A₀).eq_of_le (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance)) hle).symm
  haveI : Finite (P₀.B₀ ⧸ 𝔪) := by
    let I := 𝔪.comap (algebraMap A₀ P₀.B₀)
    haveI hImax : I.IsMaximal := by change (𝔪.comap (algebraMap A₀ P₀.B₀)).IsMaximal; rw [hcomap]; exact maximalIdeal.isMaximal A₀
    letI : Field (A₀ ⧸ I) := Ideal.Quotient.field I
    haveI : IsScalarTower A₀ (A₀ ⧸ I) (P₀.B₀ ⧸ 𝔪) :=
      IsScalarTower.of_algebraMap_eq (fun a => rfl)
    haveI : Algebra.FiniteType A₀ (P₀.B₀ ⧸ 𝔪) := inferInstance
    haveI : Algebra.FiniteType (A₀ ⧸ I) (P₀.B₀ ⧸ 𝔪) := Algebra.FiniteType.of_restrictScalars_finiteType A₀ _ _
    haveI : Module.Finite (A₀ ⧸ I) (P₀.B₀ ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing (A₀ ⧸ I) (P₀.B₀ ⧸ 𝔪)
    haveI : Finite (A₀ ⧸ I) := Finite.of_equiv (ResidueField A₀) (Ideal.quotEquivOfEq hcomap.symm).toEquiv
    exact Module.finite_of_finite (A₀ ⧸ I)
  haveI : Finite (ResidueField (AdicCompletion 𝔪 P₀.B₀)) := Finite.of_equiv _ eκ.toEquiv.symm

  obtain ⟨W₀, instCRW, instDomW, instDVRW, instCplW, σ, hW₀σ, τ, hτloc, hτsurj, hτσ⟩ :=
    IsLocalRing.exists_isDiscreteValuationRing_ringHom_of_finite_residueField A₀ (q : A₀) hA₀q
      (AdicCompletion 𝔪 P₀.B₀)
  haveI := hτloc
  have hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)} := by rw [hW₀σ, map_natCast]
  letI instW₀R : Algebra W₀ (AdicCompletion 𝔪 P₀.B₀) := τ.toAlgebra
  letI instA₀W₀ : Algebra A₀ W₀ := σ.toAlgebra
  haveI instTow₂ : IsScalarTower A₀ W₀ (AdicCompletion 𝔪 P₀.B₀) :=
    IsScalarTower.of_algebraMap_eq (fun a => (congrArg (fun f : A₀ →+* AdicCompletion 𝔪 P₀.B₀ => f a) hτσ).symm)
  let res₀ : W₀ →+* P₀.B₀ ⧸ 𝔪 := resR.comp τ
  have hres₀ : Function.Surjective res₀ := by
    change Function.Surjective (eκ.toRingHom.comp ((residue (AdicCompletion 𝔪 P₀.B₀)).comp τ))
    exact eκ.surjective.comp hτsurj
  have hker₀ : RingHom.ker res₀ = maximalIdeal W₀ := by
    rw [← maximalIdeal_comap τ, ← hkerR]; rfl
  have hresR₀ : ∀ w : W₀, resR (algebraMap W₀ (AdicCompletion 𝔪 P₀.B₀) w) = res₀ w := fun _ => rfl

  have hqk : ((q : ℕ) : P₀.B₀ ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem, ← map_natCast (algebraMap A₀ P₀.B₀)]
    exact hq𝔪
  haveI hchar : CharP (P₀.B₀ ⧸ 𝔪) q := (CharP.charP_iff_prime_eq_zero hqprime).mpr hqk

  haveI : CharP (ResidueField W₀) q := by
    have e₀ : ResidueField W₀ ≃+* P₀.B₀ ⧸ 𝔪 :=
      (Ideal.quotEquivOfEq hker₀.symm).trans (RingHom.quotientKerEquivOfSurjective hres₀)
    exact (CharP.charP_iff_prime_eq_zero hqprime).mpr (by
      apply e₀.injective; rw [map_natCast, map_zero, hqk])
  haveI : Finite (ResidueField W₀) :=
    Finite.of_equiv (P₀.B₀ ⧸ 𝔪) ((Ideal.quotEquivOfEq hker₀.symm).trans (RingHom.quotientKerEquivOfSurjective hres₀)).toEquiv.symm
  haveI : PerfectRing (ResidueField W₀) q := PerfectRing.ofFiniteOfIsReduced (p := q) _
  refine ⟨instLoc, instNoe, instCpl, instTow, resR, hresR, hkerR, hrescomp, W₀, instCRW, instDomW, instDVRW, instCplW, hW₀,
    res₀, hres₀, hker₀, instW₀R, instA₀W₀, instTow₂, hresR₀, hchar, ?_⟩

  intro T _ _ _ _ _ _ resT hresT hkerT hresT₀ φ hφ
  have hφ𝔪 : ∀ b ∈ 𝔪, (φ : P₀.B₀ →+* T) b ∈ maximalIdeal T := by
    intro b hb
    rw [← hkerT, RingHom.mem_ker]
    change resT (φ b) = 0
    rw [hφ, hresR_alg, Ideal.Quotient.eq_zero_iff_mem]; exact hb
  obtain ⟨Φ₀, ⟨hΦ₀loc, hΦ₀comp⟩, hΦ₀uniq⟩ := hlift T (φ : P₀.B₀ →+* T) hφ𝔪
  haveI := hΦ₀loc

  have hΦ₀res : ∀ r : AdicCompletion 𝔪 P₀.B₀, resT (Φ₀ r) = resR r := by
    intro r
    obtain ⟨b, hb⟩ := hsurj (residue _ r)
    have hrb : r - algebraMap P₀.B₀ _ b ∈ maximalIdeal (AdicCompletion 𝔪 P₀.B₀) := by
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]; exact hb.symm
    have h1 : Φ₀ (r - algebraMap P₀.B₀ _ b) ∈ maximalIdeal T := map_nonunit Φ₀ _ hrb
    have h2 : resT (Φ₀ (r - algebraMap P₀.B₀ _ b)) = 0 := by rw [← RingHom.mem_ker, hkerT]; exact h1
    have h3 : resR (r - algebraMap P₀.B₀ _ b) = 0 := by rw [← RingHom.mem_ker, hkerR]; exact hrb
    rw [map_sub, map_sub, sub_eq_zero] at h2
    rw [map_sub, sub_eq_zero] at h3
    rw [h2, h3]
    change resT ((Φ₀.comp (algebraMap P₀.B₀ _)) b) = _
    rw [hΦ₀comp]; exact hφ b

  haveI hgloc : IsLocalHom (algebraMap W₀ T) := by
    refine ⟨fun w hw => ?_⟩
    by_contra hnw
    have hwm : w ∈ maximalIdeal W₀ := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnw)
    have : algebraMap W₀ T w ∈ maximalIdeal T := by
      rw [← hkerT, RingHom.mem_ker, hresT₀, ← RingHom.mem_ker, hker₀]; exact hwm
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp this)) hw
  have hfg : (Φ₀.comp τ) = algebraMap W₀ T := by
    haveI : IsLocalHom (Φ₀.comp τ) := RingHom.isLocalHom_comp _ _
    refine IsDiscreteValuationRing.ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast q W₀ hW₀ T
      (Φ₀.comp τ) (algebraMap W₀ T) ?_
    ext w
    change residue T (Φ₀ (τ w)) = residue T (algebraMap W₀ T w)
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← hkerT, RingHom.mem_ker, map_sub, sub_eq_zero,
      hΦ₀res, hresT₀]
    try rfl
  let Φ : AdicCompletion 𝔪 P₀.B₀ →ₐ[W₀] T :=
    { Φ₀ with commutes' := fun w => congrArg (fun f : W₀ →+* T => f w) hfg }
  refine ⟨Φ, ⟨hΦ₀res, fun b => congrArg (fun f : P₀.B₀ →+* T => f b) hΦ₀comp⟩, ?_⟩
  rintro Φ' ⟨hΦ'res, hΦ'comp⟩
  have hΦ'loc : IsLocalHom (Φ' : AdicCompletion 𝔪 P₀.B₀ →+* T) := by
    refine ⟨fun r hr => ?_⟩
    by_contra hnr
    have hrm : r ∈ maximalIdeal _ := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnr)
    have : (Φ' : AdicCompletion 𝔪 P₀.B₀ →+* T) r ∈ maximalIdeal T := by
      rw [← hkerT, RingHom.mem_ker]
      change resT (Φ' r) = 0
      rw [hΦ'res, ← RingHom.mem_ker, hkerR]; exact hrm
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp this)) hr
  have := hΦ₀uniq (Φ' : AdicCompletion 𝔪 P₀.B₀ →+* T) ⟨hΦ'loc, RingHom.ext hΦ'comp⟩
  exact AlgHom.ext (fun r => congrArg (fun f : AdicCompletion 𝔪 P₀.B₀ →+* T => f r) this)

end S_ModularCurve_LevelModuliPackageAbs_exists_coefficientRing_factorsThrough_adicCompletion_of_levelModuliDatum
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_coefficientRing_factorsThrough_adicCompletion_of_levelModuliDatum (solution)
