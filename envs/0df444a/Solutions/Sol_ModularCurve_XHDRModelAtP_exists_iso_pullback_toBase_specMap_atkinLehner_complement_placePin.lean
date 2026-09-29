-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c4d9158e-a2a0-59cf-8a45-0f6e7bb2cfd2

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isPullback_toBase_specMap_and_iotaFin_comp_eq_of_isPushout_of_chartAlg_eq_span
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_IsCyclotomicExtension_exists_int_dvd_pow_totient_and_algebraMap_eq_discr_powerBasis
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

universe u v

section PartH1

open Polynomial ModularCurve.XHDRLevel

namespace H1

def valuationSubring (p : ℕ) [Fact p.Prime] : ValuationSubring ℚ :=
  { GaloisRep.ratLocalizedAt p with
    mem_or_inv_mem' := fun q => by
      by_cases h : q.den.Coprime p
      · exact Or.inl h
      · right
        show (q⁻¹).den.Coprime p
        rw [Rat.den_inv]
        split_ifs with h0
        · exact Nat.coprime_one_left p
        · have hp : p.Prime := Fact.out
          have hpd : p ∣ q.den := by
            by_contra hnd
            exact h (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hnd))
          exact Nat.Coprime.coprime_dvd_right hpd q.reduced }

theorem mem_valuationSubring_iff (p : ℕ) [Fact p.Prime] (q : ℚ) : q ∈ valuationSubring p ↔ q ∈ GaloisRep.ratLocalizedAt p := Iff.rfl

scoped instance isIntegrallyClosed_R (p : ℕ) [Fact p.Prime] : IsIntegrallyClosed (R p) :=
  inferInstanceAs (IsIntegrallyClosed ↥(valuationSubring p))

scoped instance isFractionRing_R (p : ℕ) [Fact p.Prime] : IsFractionRing (R p) ℚ :=
  inferInstanceAs (IsFractionRing ↥(valuationSubring p) ℚ)

theorem order (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ n) :
    IsDomain ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ∧
    Module.Free (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ∧
    Module.Finite (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ∧
    IsFractionRing ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L := by
  classical
  set R'' := Algebra.adjoin (R p) ({ζ} : Set L) with hR''
  have hn : 0 < n := NeZero.pos n

  have hζint : IsIntegral (R p) ζ := (hζ.isIntegral hn).tower_top
  haveI : Module.IsTorsionFree (R p) L := inferInstance
  let pb : PowerBasis (R p) ↥R'' := Algebra.adjoin.powerBasis' hζint
  refine ⟨inferInstance, Module.Free.of_basis pb.basis, Module.Finite.of_basis pb.basis, ?_⟩

  haveI : FaithfulSMul ↥R'' L := inferInstance
  refine IsFractionRing.of_field ↥R'' L fun z => ?_
  let B := hζ.powerBasis ℚ

  have hz : z = ∑ i, B.basis.repr z i • B.basis i := (B.basis.sum_repr z).symm

  let d : ℕ := ∏ i, (B.basis.repr z i).den
  have hd : (d : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Finset.prod_ne_zero_iff.mpr fun i _ => (B.basis.repr z i).den_nz
  have hdi : ∀ i, ∃ m : ℤ, (d : ℚ) * B.basis.repr z i = m := by
    intro i
    have hdvd : (B.basis.repr z i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k * (B.basis.repr z i).num, ?_⟩
    rw [hk, Nat.cast_mul, mul_comm ((B.basis.repr z i).den : ℚ), mul_assoc, Rat.den_mul_eq_num, Int.cast_mul, Int.cast_natCast]
  choose m hm using hdi
  have hζmem : ζ ∈ R'' := Algebra.self_mem_adjoin_singleton (R p) ζ
  refine ⟨∑ i, (m i : ↥R'') * ⟨ζ, hζmem⟩ ^ (i : ℕ), (d : ↥R''), ?_⟩
  rw [map_natCast, eq_div_iff (by exact_mod_cast hd : (d : L) ≠ 0), map_sum]
  rw [hz, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_intCast, PowerBasis.coe_basis, IsPrimitiveRoot.powerBasis_gen]
  have hmi : ((m i : ℤ) : L) = (d : L) * algebraMap ℚ L (B.basis.repr z i) := by
    rw [← map_intCast (algebraMap ℚ L), ← hm i, map_mul, map_natCast]
  have hcoe : algebraMap (↥R'') L ⟨ζ, hζmem⟩ = ζ := rfl
  rw [hcoe, hmi, Algebra.smul_def]
  ring

end H1
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

end PartH1
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

section PartH2

open ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

namespace LD

theorem linearIndependent_coeffEmb (L : Type u) [Field L] [CharZero L]
    {ι : Type*} {v : ι → LaurentSeries ℚ} (hv : LinearIndependent ℚ v) :
    LinearIndependent L (fun i => coeffEmb L (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let b := Module.Free.chooseBasis ℚ L

  have hcoeff : ∀ (k) (n : ℤ), ∑ j ∈ s, b.repr (g j) k * (v j).coeff n = 0 := by
    intro k n
    have h := congrArg (fun x : LaurentSeries L => b.repr (x.coeff n) k) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, coeffEmb_coeff, HahnSeries.coeff_zero,
      map_zero, Finsupp.zero_apply, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

  have hrepr : ∀ k, b.repr (g i) k = 0 := by
    intro k
    refine hv s (fun j => b.repr (g j) k) ?_ i hi
    ext n
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    exact hcoeff k n
  exact b.repr.map_eq_zero_iff.mp (Finsupp.ext fun k => hrepr k)

section Span

variable (L : Type u) [Field L] [CharZero L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem span_mul_mem {x y : LaurentSeries L}
    (hx : x ∈ Submodule.span L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))))
    (hy : y ∈ Submodule.span L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) :
    x * y ∈ Submodule.span L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) := by
  induction hy using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨b, hb, rfl⟩ := hb
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      exact Submodule.subset_span ⟨a * b, F₀.mul_mem ha hb, map_mul _ _ _⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul l u _ hu =>
      rw [← HahnSeries.C_mul_eq_smul, mul_assoc, HahnSeries.C_mul_eq_smul]; exact Submodule.smul_mem _ l hu
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
  | smul l u _ hu =>
    rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul]; exact Submodule.smul_mem _ l hu

set_option maxHeartbeats 3200000 in

theorem coe_laurentBaseChange_eq_span [FiniteDimensional ℚ L] :
    (laurentBaseChange L F₀ : Set (LaurentSeries L)) =
      (Submodule.span L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) : Set (LaurentSeries L)) := by
  classical
  set M := Submodule.span L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) with hM
  apply Set.Subset.antisymm
  swap
  · show (M : Set (LaurentSeries L)) ⊆ laurentBaseChange L F₀
    intro z hz
    refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ => ?_) (fun l x _ hx => ?_) hz
    · obtain ⟨x, hx, rfl⟩ := hx; exact coeffEmb_mem_laurentBaseChange L hx
    · exact (laurentBaseChange L F₀).zero_mem
    · exact (laurentBaseChange L F₀).add_mem
    · rw [← HahnSeries.C_mul_eq_smul]
      exact (laurentBaseChange L F₀).mul_mem (by rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; exact (laurentBaseChange L F₀).algebraMap_mem l) hx

  have h1 : (1 : LaurentSeries L) ∈ M := Submodule.subset_span ⟨1, F₀.one_mem, map_one _⟩
  have hCmem : ∀ (l : L) {m : LaurentSeries L}, m ∈ M → HahnSeries.C l * m ∈ M := fun l m hm => by
    rw [HahnSeries.C_mul_eq_smul]; exact M.smul_mem l hm
  let S : Subalgebra L (LaurentSeries L) :=
    { carrier := M
      mul_mem' := fun hx hy => span_mul_mem L F₀ hx hy
      one_mem' := h1
      add_mem' := fun hx hy => M.add_mem hx hy
      zero_mem' := M.zero_mem
      algebraMap_mem' := fun l => by
        rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, ← mul_one (HahnSeries.C l)]
        exact hCmem l h1 }

  let ι : ↥F₀ →+* LaurentSeries L := (coeffEmb L).comp F₀.toSubfield.subtype
  letI : Algebra (↥F₀) (LaurentSeries L) := ι.toAlgebra
  have hιapp : ∀ x : ↥F₀, algebraMap (↥F₀) (LaurentSeries L) x = coeffEmb L (x : LaurentSeries ℚ) := fun x => rfl
  let S₀ : Subalgebra (↥F₀) (LaurentSeries L) :=
    { carrier := M
      mul_mem' := fun hx hy => span_mul_mem L F₀ hx hy
      one_mem' := h1
      add_mem' := fun hx hy => M.add_mem hx hy
      zero_mem' := M.zero_mem
      algebraMap_mem' := fun x => Submodule.subset_span ⟨x, x.2, rfl⟩ }

  have hint : ∀ z ∈ M, IsIntegral (↥F₀) z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [← hιapp ⟨a, ha⟩]; exact isIntegral_algebraMap
    | zero => exact isIntegral_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul l x _ hx =>
      rw [← HahnSeries.C_mul_eq_smul]
      refine IsIntegral.mul ?_ hx

      have hl : IsAlgebraic ℚ l := Algebra.IsAlgebraic.isAlgebraic l
      obtain ⟨P, hP0, hPl⟩ := hl
      have halgC : IsAlgebraic (↥F₀) (HahnSeries.C l : LaurentSeries L) := by
        refine ⟨P.map (algebraMap ℚ ↥F₀), (Polynomial.map_ne_zero_iff (algebraMap ℚ ↥F₀).injective).mpr hP0, ?_⟩
        rw [Polynomial.aeval_def, Polynomial.eval₂_map,
          RingHom.ext_rat ((algebraMap (↥F₀) (LaurentSeries L)).comp (algebraMap ℚ ↥F₀)) ((HahnSeries.C : L →+* LaurentSeries L).comp (algebraMap ℚ L)),
          ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hPl, map_zero]
      exact halgC.isIntegral

  have hinv : ∀ z ∈ M, z⁻¹ ∈ M := by
    intro z hz
    have halg : IsAlgebraic (↥F₀) z := (hint z hz).isAlgebraic
    have h := @Subalgebra.inv_mem_of_algebraic (↥F₀) (LaurentSeries L) _ _ _ S₀ ⟨z, hz⟩ halg
    exact h

  have hle : laurentBaseChange L F₀ ≤ S.toIntermediateField (fun x hx => hinv x hx) := by
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  intro z hz
  exact hle hz

end Span
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

end LD
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

open ModularCurve ModularCurve.XHDRLevel

namespace W5H2

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (L : Type) [Field L] [CharZero L]

noncomputable def toLForm : ↥(qExpFunctionFieldC ℚ (ΓM M H)) →+* ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
  ((coeffEmb L).comp (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) (LaurentSeries ℚ))).codRestrict
    (laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
    (fun x => coeffEmb_mem_laurentBaseChange L (x := (x : LaurentSeries ℚ)) x.2)

theorem coe_toLForm (x : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
    ((toLForm M H L x : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) = coeffEmb L (x : LaurentSeries ℚ) := rfl

noncomputable abbrev algLForm : Algebra ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
  (toLForm M H L).toAlgebra

end W5H2
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

set_option synthInstance.maxHeartbeats 1600000 in
theorem W5H2.isScalarTower_rat (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (L : Type) [Field L] [CharZero L] :
    letI := W5H2.algLForm M H L
    IsScalarTower ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) := by
  letI := W5H2.algLForm M H L
  refine IsScalarTower.of_algebraMap_eq (fun q => ?_)
  exact (RingHom.congr_fun (RingHom.ext_rat
    ((algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))).comp
      (algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H))))
    (algebraMap ℚ ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))) q).symm

attribute [local instance] W5H2.algLForm W5H2.isScalarTower_rat

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem H2a_isPushout (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L] :
    letI := W5H2.algLForm M H L
    haveI := W5H2.isScalarTower_rat M H L
    Algebra.IsPushout ℚ L ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) := by
  classical
  set F0 := qExpFunctionFieldC ℚ (ΓM M H) with hF0
  set F' := laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)) with hF'

  let ψ : L ⊗[ℚ] ↥F0 →ₐ[L] ↥F' :=
    Algebra.TensorProduct.lift (R := ℚ) (S := L) (A := L) (B := ↥F0) (C := ↥F') (Algebra.ofId L ↥F') (IsScalarTower.toAlgHom ℚ ↥F0 ↥F') (fun x y => Commute.all _ _)
  have hψ : ∀ (l : L) (x : ↥F0), ψ (l ⊗ₜ x) = Algebra.ofId L ↥F' l * IsScalarTower.toAlgHom ℚ ↥F0 ↥F' x := fun l x =>
    Algebra.TensorProduct.lift_tmul _ _ _ l x
  have hcoe : ∀ x : ↥F0, ((algebraMap ↥F0 ↥F' x : ↥F') : LaurentSeries L) = coeffEmb L (x : LaurentSeries ℚ) := fun x =>
    show ((W5H2.toLForm M H L x : ↥F') : LaurentSeries L) = _ from W5H2.coe_toLForm M H L x

  let bF := Module.Free.chooseBasis ℚ ↥F0
  let b := Algebra.TensorProduct.basis L bF
  have hliQ : LinearIndependent ℚ (fun i => ((bF i : ↥F0) : LaurentSeries ℚ)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h0 : (∑ j ∈ s, g j • bF j : ↥F0) = 0 := by
      apply Subtype.val_injective
      rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (map_rat_smul (AddMonoidHom.mk' (fun x : ↥F0 => (x : LaurentSeries ℚ)) (fun _ _ => rfl)) (g j) (bF j))
    exact linearIndependent_iff'.mp bF.linearIndependent s g h0 i hi
  have hLD1 := LD.linearIndependent_coeffEmb L hliQ

  have hψb : ∀ i, ((ψ (b i) : ↥F') : LaurentSeries L) = coeffEmb L ((bF i : ↥F0) : LaurentSeries ℚ) := fun i => by
    rw [Algebra.TensorProduct.basis_apply, hψ, map_one, one_mul]; exact hcoe _

  have hsmulF : ∀ (l : L) (y : ↥F') (n : ℤ), ((l • y : ↥F') : LaurentSeries L).coeff n = l * (y : LaurentSeries L).coeff n := by
    intro l y n
    rw [Algebra.smul_def, MulMemClass.coe_mul, show ((algebraMap L ↥F' l : ↥F') : LaurentSeries L) = algebraMap L (LaurentSeries L) l from rfl,
      algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  have hli : LinearIndependent L (fun i => ψ (b i)) := by
    rw [linearIndependent_iff'] at hLD1 ⊢
    intro s g hg i hi
    refine hLD1 s g ?_ i hi
    ext n
    have h := congrArg (fun y : ↥F' => (y : LaurentSeries L).coeff n) hg
    simp only [AddSubmonoidClass.coe_finsetSum, HahnSeries.coeff_sum, hsmulF, hψb, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [HahnSeries.coeff_smul, smul_eq_mul]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hrepr := b.linearCombination_repr z
    rw [← hrepr, Finsupp.linearCombination_apply, map_finsuppSum] at hz
    simp only [map_smul] at hz
    have h0 := linearIndependent_iff.mp hli (b.repr z) (by rw [Finsupp.linearCombination_apply]; exact hz)
    rw [← hrepr, h0, map_zero]

  have hmemF' : ∀ u : LaurentSeries L, u ∈ Submodule.span L (⇑(coeffEmb L) '' (F0 : Set (LaurentSeries ℚ))) → u ∈ F' := fun u hu => by
    rw [← SetLike.mem_coe, hF', LD.coe_laurentBaseChange_eq_span]; exact hu
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : LaurentSeries L) ∈ (Submodule.span L (⇑(coeffEmb L) '' (F0 : Set (LaurentSeries ℚ))) : Set (LaurentSeries L)) := by
      rw [← LD.coe_laurentBaseChange_eq_span L F0]; exact y.2

    suffices h : ∀ z : LaurentSeries L, z ∈ Submodule.span L (⇑(coeffEmb L) '' (F0 : Set (LaurentSeries ℚ))) →
        ∀ hz : z ∈ F', ∃ t, ψ t = ⟨z, hz⟩ by
      obtain ⟨t, ht⟩ := h y hy y.2
      exact ⟨t, by rw [ht]⟩
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro hz
      exact ⟨1 ⊗ₜ ⟨a, ha⟩, Subtype.ext (by rw [hψ, map_one, one_mul]; exact hcoe ⟨a, ha⟩)⟩
    | zero => intro hz; exact ⟨0, Subtype.ext (by rw [map_zero]; rfl)⟩
    | add u v hu hv ihu ihv =>
      intro hz
      have hu' : u ∈ F' := hmemF' u hu
      have hv' : v ∈ F' := hmemF' v hv
      obtain ⟨tu, htu⟩ := ihu hu'
      obtain ⟨tv, htv⟩ := ihv hv'
      exact ⟨tu + tv, Subtype.ext (by rw [map_add, AddMemClass.coe_add, htu, htv])⟩
    | smul l u hu ihu =>
      intro hz
      have hu' : u ∈ F' := hmemF' u hu
      obtain ⟨tu, htu⟩ := ihu hu'
      refine ⟨l • tu, Subtype.ext ?_⟩
      ext n
      rw [map_smul, hsmulF, htu, HahnSeries.coeff_smul, smul_eq_mul]

  let e : L ⊗[ℚ] ↥F0 ≃ₗ[L] ↥F' := LinearEquiv.ofBijective ψ.toLinearMap ⟨hinj, hsurj⟩
  exact ⟨IsBaseChange.of_equiv e (fun x => by
    show ψ (1 ⊗ₜ x) = IsScalarTower.toAlgHom ℚ ↥F0 ↥F' x
    rw [hψ, map_one, one_mul])⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem H2b_powerBasis (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (L : Type) [Field L] [CharZero L]
    (Q : ℕ) [NeZero Q] [IsCyclotomicExtension {Q} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ Q) :
    letI := W5H2.algLForm M H L
    ∃ (B : PowerBasis ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))),
      B.gen = algebraMap L _ ζ ∧ B.dim = Module.finrank ℚ L ∧ IsIntegral ℤ B.gen ∧
      Algebra.discr ↥(qExpFunctionFieldC ℚ (ΓM M H)) (fun i : Fin B.dim => B.gen ^ (i : ℕ)) =
        algebraMap ℚ _ (Algebra.discr ℚ (fun i : Fin B.dim => (hζ.powerBasis ℚ).gen ^ (i : ℕ))) := by
  classical
  set F0 := qExpFunctionFieldC ℚ (ΓM M H) with hF0
  set F' := laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)) with hF'
  have hQ : 0 < Q := NeZero.pos Q
  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {Q} ℚ L
  haveI : IsScalarTower ℚ L ↥F' := IsScalarTower.of_algebraMap_eq (fun q =>
    (RingHom.congr_fun (RingHom.ext_rat ((algebraMap L ↥F').comp (algebraMap ℚ L)) (algebraMap ℚ ↥F')) q).symm)
  have hP : Algebra.IsPushout ℚ ↥F0 L ↥F' := (H2a_isPushout M H L).symm
  let e : ↥F0 ⊗[ℚ] L ≃ₐ[↥F0] ↥F' := Algebra.IsPushout.equiv ℚ ↥F0 L ↥F'
  have he : ∀ (a : ↥F0) (l : L), e (a ⊗ₜ l) = algebraMap ↥F0 ↥F' a * algebraMap L ↥F' l :=
    Algebra.IsPushout.equiv_tmul ℚ ↥F0 L ↥F'
  let pb := hζ.powerBasis ℚ
  let bT := Algebra.TensorProduct.basis ↥F0 pb.basis
  let bB := bT.map e.toLinearEquiv
  have hbB : ∀ i, bB i = algebraMap L ↥F' ζ ^ (i : ℕ) := fun i => by
    show e (bT i) = _
    rw [Algebra.TensorProduct.basis_apply, he, map_one, one_mul, PowerBasis.coe_basis, IsPrimitiveRoot.powerBasis_gen, map_pow]
  let B : PowerBasis ↥F0 ↥F' := ⟨algebraMap L ↥F' ζ, pb.dim, bB, hbB⟩
  refine ⟨B, rfl, (PowerBasis.finrank pb).symm, (hζ.isIntegral hQ).map (algebraMap L ↥F').toIntAlgHom, ?_⟩

  show Algebra.discr ↥F0 (fun i : Fin pb.dim => algebraMap L ↥F' ζ ^ (i : ℕ)) = algebraMap ℚ ↥F0 (Algebra.discr ℚ (fun i : Fin pb.dim => pb.gen ^ (i : ℕ)))
  have h1 : (fun i : Fin pb.dim => algebraMap L ↥F' ζ ^ (i : ℕ)) = ⇑e ∘ ⇑bT := by
    funext i; exact (hbB i).symm
  rw [h1, ← Algebra.discr_eq_discr_of_algEquiv bT e, ← PowerBasis.coe_basis, Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.traceForm_apply,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.trace_apply, Algebra.trace_apply]
  have h2 : (Algebra.lmul ↥F0 (↥F0 ⊗[ℚ] L) ((1 : ↥F0) ⊗ₜ[ℚ] (pb.basis i * pb.basis j)) : ↥F0 ⊗[ℚ] L →ₗ[↥F0] ↥F0 ⊗[ℚ] L) =
      LinearMap.baseChange ↥F0 (Algebra.lmul ℚ L (pb.basis i * pb.basis j) : L →ₗ[ℚ] L) := by
    refine TensorProduct.AlgebraTensorModule.ext fun a l => ?_
    rw [LinearMap.baseChange_tmul]
    show ((1 : ↥F0) ⊗ₜ[ℚ] (pb.basis i * pb.basis j)) * (a ⊗ₜ[ℚ] l) = a ⊗ₜ[ℚ] ((pb.basis i * pb.basis j) * l)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h2, LinearMap.trace_baseChange]

end PartH2
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

section PartH567

namespace Ws6
namespace W5

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

section TwoBase

variable (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] (F : Type u) [Field F]
  [Algebra R R'] [Algebra R' F] [Algebra R F] [IsScalarTower R R' F]

theorem adjoin_le_integralClosure_adjoin [Algebra.IsIntegral R R'] (S : Set F) :
    (Algebra.adjoin R' S).toSubring ≤
      (integralClosure (Algebra.adjoin R S) F).toSubring := by
  let C' : Subalgebra R' F :=
    { (integralClosure (Algebra.adjoin R S) F).toSubring with
      algebraMap_mem' := fun r => by
        change IsIntegral (Algebra.adjoin R S) (algebraMap R' F r)
        have h : IsIntegral R (algebraMap R' F r) :=
          (Algebra.IsIntegral.isIntegral (R := R) r).map (IsScalarTower.toAlgHom R R' F)
        exact h.tower_top }
  have hle : Algebra.adjoin R' S ≤ C' := Algebra.adjoin_le fun s hs => by
    change IsIntegral (Algebra.adjoin R S) s
    exact isIntegral_algebraMap (R := Algebra.adjoin R S) (x := (⟨s, Algebra.subset_adjoin hs⟩ : Algebra.adjoin R S))
  intro x hx
  exact hle hx

theorem chartAlg_toSubring_eq_of_isIntegral [Algebra.IsIntegral R R'] (S : Set F) :
    (chartAlg R' F S).toSubring = (chartAlg R F S).toSubring := by
  refine le_antisymm ?_ (chartAlg_le_chartAlg R F R' S)
  intro x hx
  change IsIntegral (Algebra.adjoin R S) x
  have hx' : IsIntegral (Algebra.adjoin R' S) x := hx
  have hC : IsIntegral (integralClosure (Algebra.adjoin R S) F) x :=
    hx'.map_of_comp_eq (Subring.inclusion (adjoin_le_integralClosure_adjoin R R' F S)) (RingHom.id F)
      (by ext; rfl)
  exact isIntegral_trans (R := Algebra.adjoin R S) (A := integralClosure (Algebra.adjoin R S) F) (B := F) x hC

theorem coe_chartAlg_eq_of_isIntegral [Algebra.IsIntegral R R'] (S : Set F) :
    (chartAlg R' F S : Set F) = (chartAlg R F S : Set F) :=
  congrArg (fun T : Subring F => (T : Set F)) (chartAlg_toSubring_eq_of_isIntegral R R' F S)

theorem mem_chartAlg_iff_of_isIntegral [Algebra.IsIntegral R R'] (S : Set F) (x : F) :
    x ∈ chartAlg R' F S ↔ x ∈ chartAlg R F S :=
  Set.ext_iff.mp (coe_chartAlg_eq_of_isIntegral R R' F S) x

theorem restrictScalars_chartAlg_eq_of_isIntegral [Algebra.IsIntegral R R'] (S : Set F) :
    (chartAlg R' F S).restrictScalars R = chartAlg R F S :=
  SetLike.ext fun x => mem_chartAlg_iff_of_isIntegral R R' F S x

theorem modInput_of_isIntegral [Algebra.IsIntegral R R'] (j j' : F)
    (h : j' ∈ chartAlgFin R' F j ∧ j ∈ chartAlgFin R' F j' ∧
      (∀ y ∈ chartAlgInf R' F j', ∃ s ∈ chartAlgInf R' F j, (∃ a ∈ chartAlgInf R' F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R' F j) ∧
      (∀ y ∈ chartAlgInf R' F j, ∃ s ∈ chartAlgInf R' F j', (∃ a ∈ chartAlgInf R' F j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ chartAlgInf R' F j')) :
    j' ∈ chartAlgFin R F j ∧ j ∈ chartAlgFin R F j' ∧
      (∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j, (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j) ∧
      (∀ y ∈ chartAlgInf R F j, ∃ s ∈ chartAlgInf R F j', (∃ a ∈ chartAlgInf R F j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j') := by
  obtain ⟨hfin, hfin', hvis, hvis'⟩ := h
  simp only [chartAlgFin, chartAlgInf, mem_chartAlg_iff_of_isIntegral R R' F] at hfin hfin' hvis hvis'
  exact ⟨hfin, hfin', hvis, hvis'⟩

theorem finiteType_chartAlg_of_isIntegral [Algebra.IsIntegral R R'] (S : Set F)
    [h : Algebra.FiniteType R ↥(chartAlg R F S)] : Algebra.FiniteType R' ↥(chartAlg R' F S) := by
  have e : ↥(chartAlg R F S) ≃ₐ[R] ↥((chartAlg R' F S).restrictScalars R) :=
    Subalgebra.equivOfEq _ _ (restrictScalars_chartAlg_eq_of_isIntegral R R' F S).symm
  have hR : Algebra.FiniteType R ↥((chartAlg R' F S).restrictScalars R) := h.equiv e
  have hR' : Algebra.FiniteType R ↥(chartAlg R' F S) := hR
  exact Algebra.FiniteType.of_restrictScalars_finiteType R R' _

end TwoBase
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

section Transport

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]

theorem mem_chartAlg_image_of_mem (σ : F ≃ₐ[R] F) (S : Set F) {x : F} (hx : x ∈ chartAlg R F S) :
    σ x ∈ chartAlg R F (σ '' S) := by
  rw [mem_chartAlg_iff] at hx ⊢
  have hmap : Algebra.adjoin R S ≤ (Algebra.adjoin R (σ '' S)).comap (σ : F →ₐ[R] F) :=
    Algebra.adjoin_le fun s hs => Algebra.subset_adjoin ⟨s, hs, rfl⟩
  let φ : ↥(Algebra.adjoin R S) →+* ↥(Algebra.adjoin R (σ '' S)) :=
    ((σ : F →+* F).comp (algebraMap (Algebra.adjoin R S) F)).codRestrict (Algebra.adjoin R (σ '' S))
      (fun a => hmap a.2)
  exact hx.map_of_comp_eq (T := Algebra.adjoin R (σ '' S)) φ (σ : F →+* F) (by ext a; rfl)

theorem map_chartAlg_algEquiv (σ : F ≃ₐ[R] F) (S : Set F) :
    (chartAlg R F S).map (σ : F →ₐ[R] F) = chartAlg R F (σ '' S) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_chartAlg_image_of_mem R F σ S hx
  · intro y hy
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    have h := mem_chartAlg_image_of_mem R F σ.symm (σ '' S) hy
    simpa [Set.image_image] using h

noncomputable def chartAlgEquivOfAlgEquiv (σ : F ≃ₐ[R] F) (S : Set F) :
    ↥(chartAlg R F S) ≃ₐ[R] ↥(chartAlg R F (σ '' S)) :=
  (σ.subalgebraMap (chartAlg R F S)).trans (Subalgebra.equivOfEq _ _ (map_chartAlg_algEquiv R F σ S))

@[scoped simp] theorem coe_chartAlgEquivOfAlgEquiv (σ : F ≃ₐ[R] F) (S : Set F) (x : ↥(chartAlg R F S)) :
    ((chartAlgEquivOfAlgEquiv R F σ S x : ↥(chartAlg R F (σ '' S))) : F) = σ (x : F) := rfl

theorem finiteType_chartAlg_image_algEquiv (σ : F ≃ₐ[R] F) (S : Set F)
    [h : Algebra.FiniteType R ↥(chartAlg R F S)] : Algebra.FiniteType R ↥(chartAlg R F (σ '' S)) :=
  h.equiv (chartAlgEquivOfAlgEquiv R F σ S)

variable (j : F)

theorem finiteType_chartAlgFin_algEquiv (σ : F ≃ₐ[R] F) [Algebra.FiniteType R ↥(chartAlgFin R F j)] :
    Algebra.FiniteType R ↥(chartAlgFin R F (σ j)) := by
  have h := finiteType_chartAlg_image_algEquiv R F σ {j}
  rwa [Set.image_singleton] at h

theorem finiteType_chartAlgInf_algEquiv (σ : F ≃ₐ[R] F) [Algebra.FiniteType R ↥(chartAlgInf R F j)] :
    Algebra.FiniteType R ↥(chartAlgInf R F (σ j)) := by
  have h := finiteType_chartAlg_image_algEquiv R F σ {j⁻¹}
  rwa [Set.image_singleton, map_inv₀] at h

theorem isSeparated_toBase [IsNoetherianRing R] [Fact (j ≠ 0)]
    [Algebra.FiniteType R ↥(chartAlgFin R F j)] [Algebra.FiniteType R ↥(chartAlgInf R F j)] :
    IsSeparated (toBase R F j) := by
  haveI := AlgebraicCurve.TwoChartIntegralModel.isProper_toBase R F j
  infer_instance

end Transport
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

section Span

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
  (R'' : Type u) [CommRing R''] [Algebra R R'']
  (F' : Type u) [Field F'] [Algebra R F'] [Algebra R'' F'] [Algebra F F'] [IsScalarTower R R'' F'] [IsScalarTower R F F']

theorem fg_chartAlg_of_toSubmodule_eq_span [Algebra.IsIntegral R R''] (S : Set F)
    (hchart : Subalgebra.toSubmodule (chartAlg R F' (algebraMap F F' '' S)) =
        (Submodule.span R'' (algebraMap F F' '' (chartAlg R F S : Set F))).restrictScalars R)
    (hfg : (chartAlg R F S).FG) :
    (chartAlg R'' F' (algebraMap F F' '' S)).FG := by
  classical
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t.image (algebraMap F F'), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ chartAlg R F S := ht ▸ Algebra.subset_adjoin hx
    have h1 : algebraMap F F' x ∈ Subalgebra.toSubmodule (chartAlg R F' (algebraMap F F' '' S)) := by
      rw [hchart]
      exact Submodule.subset_span ⟨x, hx', rfl⟩
    exact chartAlg_le_chartAlg R F' R'' _ h1
  · intro y hy
    have hy' : y ∈ Subalgebra.toSubmodule (chartAlg R F' (algebraMap F F' '' S)) :=
      (mem_chartAlg_iff_of_isIntegral R R'' F' _ y).mp hy
    rw [hchart, Submodule.restrictScalars_mem] at hy'
    refine (Submodule.span_le.mpr ?_ :
      Submodule.span R'' (algebraMap F F' '' (chartAlg R F S : Set F)) ≤
        Subalgebra.toSubmodule (Algebra.adjoin R'' ((algebraMap F F') '' (t : Set F)))) hy'
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Algebra.adjoin R (t : Set F) := by rw [ht]; exact hx
    have hle : Algebra.adjoin R (t : Set F) ≤
        (Algebra.adjoin R ((algebraMap F F') '' (t : Set F))).comap (IsScalarTower.toAlgHom R F F') :=
      Algebra.adjoin_le fun s hs => Algebra.subset_adjoin ⟨s, hs, rfl⟩
    exact adjoin_le_adjoin_restrictScalars R F' R'' _ (hle hx')

theorem finiteType_chartAlg_of_toSubmodule_eq_span [Algebra.IsIntegral R R''] (S : Set F)
    (hchart : Subalgebra.toSubmodule (chartAlg R F' (algebraMap F F' '' S)) =
        (Submodule.span R'' (algebraMap F F' '' (chartAlg R F S : Set F))).restrictScalars R)
    [h : Algebra.FiniteType R ↥(chartAlg R F S)] :
    Algebra.FiniteType R'' ↥(chartAlg R'' F' (algebraMap F F' '' S)) :=
  (Subalgebra.fg_iff_finiteType _).mp
    (fg_chartAlg_of_toSubmodule_eq_span R F R'' F' S hchart ((Subalgebra.fg_iff_finiteType _).mpr h))

variable (j : F)

theorem finiteType_chartAlgFin_of_toSubmodule_eq_span [Algebra.IsIntegral R R''] (j' : F') (hj' : algebraMap F F' j = j')
    (hchart : Subalgebra.toSubmodule (chartAlg R F' (algebraMap F F' '' {j})) =
        (Submodule.span R'' (algebraMap F F' '' (chartAlg R F {j} : Set F))).restrictScalars R)
    [Algebra.FiniteType R ↥(chartAlgFin R F j)] :
    Algebra.FiniteType R'' ↥(chartAlgFin R'' F' j') := by
  subst hj'
  have h := finiteType_chartAlg_of_toSubmodule_eq_span R F R'' F' {j} hchart
  rwa [Set.image_singleton] at h

theorem finiteType_chartAlgInf_of_toSubmodule_eq_span [Algebra.IsIntegral R R''] (j' : F') (hj' : algebraMap F F' j = j')
    (hchart : Subalgebra.toSubmodule (chartAlg R F' (algebraMap F F' '' {j⁻¹})) =
        (Submodule.span R'' (algebraMap F F' '' (chartAlg R F {j⁻¹} : Set F))).restrictScalars R)
    [Algebra.FiniteType R ↥(chartAlgInf R F j)] :
    Algebra.FiniteType R'' ↥(chartAlgInf R'' F' j') := by
  subst hj'
  have h := finiteType_chartAlg_of_toSubmodule_eq_span R F R'' F' {j⁻¹} hchart
  rwa [Set.image_singleton, map_inv₀] at h

end Span
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

open ModularCurve ModularCurve.XHDRLevel in

theorem isNoetherianRing_of_moduleFinite_R (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (R p) A]
    [Module.Finite (R p) A] : IsNoetherianRing A := by
  haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsNoetherianRing (R p) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing (R p) A

section Face

open ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (L : Type) [Field L] [CharZero L]
  (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
  [Algebra A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))]
  [IsScalarTower A L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))]
  (j' : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))
  (hj' : ((j' : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) = coeffEmb L (jqModC ℚ))
  [Fact (j' ≠ 0)]
  (σ : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) ≃ₐ[L] ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))
  (hσ : ∀ (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) (u : ↥(qExpFunctionFieldC ℚ (ΓM p (H.map (ZMod.unitsMap hpM))))),
      (f : LaurentSeries L) = coeffEmb L (u : LaurentSeries ℚ) →
        ((σ f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) = coeffEmb L (qExpand ℚ (M / p) (u : LaurentSeries ℚ)))
  [Fact (σ j' ≠ 0)]

include hpM hj hj' hσ in
omit [Fact p.Prime] [NeZero M] [Fact (j' ≠ 0)] [Fact (σ j' ≠ 0)] in

theorem coe_algEquiv_j' :
    ((σ j' : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) =
      coeffEmb L (qExpand ℚ (M / p) (jqModC ℚ)) :=
  hσ j' (jAt (ΓM p (H.map (ZMod.unitsMap hpM))) hj) hj'

include hpM hj hj' hσ in
omit [Fact p.Prime] [NeZero M] in

theorem H5_modInput :
    σ j' ∈ chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ∧
    j' ∈ chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (σ j') ∧
    (∀ y ∈ chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (σ j'),
      ∃ s ∈ chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j',
        (∃ a ∈ chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j', s = 1 + j'⁻¹ * a) ∧
        s * y ∈ chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') ∧
    (∀ y ∈ chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j',
      ∃ s ∈ chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (σ j'),
        (∃ a ∈ chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (σ j'), s = 1 + (σ j')⁻¹ * a) ∧
        s * y ∈ chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (σ j')) := by
  have hσj := coe_algEquiv_j' p M H hpM hj L j' hj' σ hσ
  rcases (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (M / p))).eq_or_lt with hQ | hQ
  ·
    have hid : ∀ (N : ℕ) [NeZero N], 1 = N → ∀ f : LaurentSeries ℚ, qExpand ℚ N f = f := by
      rintro N _ rfl f
      exact qExpand_one_apply f
    have e : σ j' = j' := Subtype.ext (by rw [hσj, hid (M / p) hQ, ← hj'])
    rw [e]
    refine ⟨subset_chartAlg A _ _ (Set.mem_singleton _), subset_chartAlg A _ _ (Set.mem_singleton _),
      fun y hy => ⟨1, one_mem _, ⟨0, zero_mem _, by ring⟩, by rwa [one_mul]⟩,
      fun y hy => ⟨1, one_mem _, ⟨0, zero_mem _, by ring⟩, by rwa [one_mul]⟩⟩
  · exact ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
      (M / p) hQ L (laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) A j' hj' (σ j') hσj

include hpM hj hj' hσ in
omit [Fact p.Prime] [NeZero M] in

theorem H7_exists_iso [IsNoetherianRing A]
    [Algebra.FiniteType A ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')]
    [Algebra.FiniteType A ↥(chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')] :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ≅
          AlgebraicCurve.TwoChartIntegralModel A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')
      (θ : ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') ≃ₐ[A]
          ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')),
      w.hom ≫ toBase A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' =
        toBase A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ∧
      (∀ b : ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'),
        ((θ b : ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')) :
          ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) = (σ.restrictScalars A) (b : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))) ∧
      ιFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ≫ w.hom =
        Spec.map (CommRingCat.ofHom θ.toRingEquiv.toRingHom) ≫ ιFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ∧
      w.hom ⁻¹ᵁ (ιFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j').opensRange =
        (ιFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j').opensRange := by
  obtain ⟨hfin, hfin', hvis, hvis'⟩ := H5_modInput p M H hpM hj L A j' hj' σ hσ
  haveI : Fact ((σ.restrictScalars A) j' ≠ 0) := ‹Fact (σ j' ≠ 0)›
  haveI : Algebra.FiniteType A ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) ((σ.restrictScalars A) j')) :=
    finiteType_chartAlgFin_algEquiv A _ j' (σ.restrictScalars A)
  haveI : Algebra.FiniteType A ↥(chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) ((σ.restrictScalars A) j')) :=
    finiteType_chartAlgInf_algEquiv A _ j' (σ.restrictScalars A)
  haveI : IsSeparated (toBase A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') :=
    isSeparated_toBase A _ j'
  haveI : IsSeparated (toBase A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) ((σ.restrictScalars A) j')) :=
    isSeparated_toBase A _ _
  exact AlgebraicCurve.TwoChartIntegralModel.exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv A
    ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' (σ.restrictScalars A) hfin hfin' hvis hvis'

include hpM hj hj' hσ in
omit [NeZero M] in

theorem H567_exists_iso
    [Algebra (R p) A] [Module.Finite (R p) A]
    [Algebra (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))]
    [IsScalarTower (R p) A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))]
    [Algebra ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))]
    [IsScalarTower (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))]
    (hj4 : algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj) = j')
    (hchart : ∀ S : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)),
      S = {jAt (ΓM M H) hj} ∨ S = {(jAt (ΓM M H) hj)⁻¹} ∨ S = {jAt (ΓM M H) hj, (jAt (ΓM M H) hj)⁻¹} →
      Subalgebra.toSubmodule (chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
          (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) '' S)) =
        (Submodule.span A (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) ''
          (chartAlg (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) S : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))))).restrictScalars (R p))
    [Algebra.FiniteType (R p) ↥(chartAlgFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))]
    [Algebra.FiniteType (R p) ↥(chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))] :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ≅
          AlgebraicCurve.TwoChartIntegralModel A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')
      (θ : ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') ≃ₐ[A]
          ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')),
      w.hom ≫ toBase A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' =
        toBase A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ∧
      (∀ b : ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'),
        ((θ b : ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')) :
          ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) = (σ.restrictScalars A) (b : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))) ∧
      ιFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ≫ w.hom =
        Spec.map (CommRingCat.ofHom θ.toRingEquiv.toRingHom) ≫ ιFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ∧
      w.hom ⁻¹ᵁ (ιFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j').opensRange =
        (ιFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j').opensRange := by
  haveI : IsNoetherianRing A := isNoetherianRing_of_moduleFinite_R p A
  haveI : Algebra.FiniteType A ↥(chartAlgFin A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') :=
    finiteType_chartAlgFin_of_toSubmodule_eq_span (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) A
      ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj) j' hj4 (hchart _ (Or.inl rfl))
  haveI : Algebra.FiniteType A ↥(chartAlgInf A ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') :=
    finiteType_chartAlgInf_of_toSubmodule_eq_span (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) A
      ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj) j' hj4 (hchart _ (Or.inr (Or.inl rfl)))
  exact H7_exists_iso p M H hpM hj L A j' hj' σ hσ

end Face
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1"

end Ws6.W5
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6"

end PartH567
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

section PartH9

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem H9_baseChange_modelAut
    (R : Type u) [CommRing R] (X : Scheme.{u}) (toBaseX : X ⟶ Spec (CommRingCat.of R))
    (R'' : Type u) [CommRing R''] [Algebra R R'']
    (X' : Scheme.{u}) (t' : X' ⟶ Spec (CommRingCat.of R'')) (u : X' ⟶ X)
    (hsq : IsPullback u t' toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R R''))))
    (w : X' ≅ X') (hw : w.hom ≫ t' = t')
    (A : Type u) [CommRing A] [Algebra R A] (g : R'' →+* A) (hg : g.comp (algebraMap R R'') = algebraMap R A) :
    ∃ (φ : pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≅
        pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
      (v : pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ X'),

      φ.hom ≫ pullback.snd toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) =
        pullback.snd toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) ∧

      v ≫ u = pullback.fst toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) ∧
      v ≫ t' = pullback.snd toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ Spec.map (CommRingCat.ofHom g) ∧
      IsPullback v (pullback.snd toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A)))) t' (Spec.map (CommRingCat.ofHom g)) ∧

      φ.hom ≫ v = v ≫ w.hom := by

  set sR : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R R'')) with hsR
  set sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A)) with hsA
  set sg : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R'') := Spec.map (CommRingCat.ofHom g) with hsg

  have hsgR : sg ≫ sR = sA := by
    rw [hsg, hsR, hsA, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]

  have hw' : w.inv ≫ t' = t' := by
    rw [← cancel_epi w.hom, ← Category.assoc, w.hom_inv_id, Category.id_comp, hw]

  have hP0 : IsPullback (pullback.fst toBaseX sA) (pullback.snd toBaseX sA) toBaseX sA := IsPullback.of_hasPullback _ _

  have hcomm : pullback.fst toBaseX sA ≫ toBaseX = (pullback.snd toBaseX sA ≫ sg) ≫ sR := by
    rw [Category.assoc, hsgR]; exact pullback.condition
  let v : pullback toBaseX sA ⟶ X' := hsq.lift (pullback.fst toBaseX sA) (pullback.snd toBaseX sA ≫ sg) hcomm
  have hvu : v ≫ u = pullback.fst toBaseX sA := hsq.lift_fst _ _ _
  have hvt : v ≫ t' = pullback.snd toBaseX sA ≫ sg := hsq.lift_snd _ _ _

  have hbig : IsPullback (v ≫ u) (pullback.snd toBaseX sA) toBaseX (sg ≫ sR) := by
    rw [hvu, hsgR]; exact hP0
  have hP : IsPullback v (pullback.snd toBaseX sA) t' sg := IsPullback.of_right hbig hvt hsq

  have hc1 : (v ≫ w.hom) ≫ t' = pullback.snd toBaseX sA ≫ sg := by rw [Category.assoc, hw, hvt]
  have hc2 : (v ≫ w.inv) ≫ t' = pullback.snd toBaseX sA ≫ sg := by rw [Category.assoc, hw', hvt]
  let φh : pullback toBaseX sA ⟶ pullback toBaseX sA := hP.lift (v ≫ w.hom) (pullback.snd toBaseX sA) hc1
  let φi : pullback toBaseX sA ⟶ pullback toBaseX sA := hP.lift (v ≫ w.inv) (pullback.snd toBaseX sA) hc2
  have hφh_v : φh ≫ v = v ≫ w.hom := hP.lift_fst _ _ _
  have hφh_s : φh ≫ pullback.snd toBaseX sA = pullback.snd toBaseX sA := hP.lift_snd _ _ _
  have hφi_v : φi ≫ v = v ≫ w.inv := hP.lift_fst _ _ _
  have hφi_s : φi ≫ pullback.snd toBaseX sA = pullback.snd toBaseX sA := hP.lift_snd _ _ _
  have hhi : φh ≫ φi = 𝟙 _ := by
    apply hP.hom_ext
    · rw [Category.assoc, hφi_v, ← Category.assoc, hφh_v, Category.assoc, w.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hφi_s, hφh_s, Category.id_comp]
  have hih : φi ≫ φh = 𝟙 _ := by
    apply hP.hom_ext
    · rw [Category.assoc, hφh_v, ← Category.assoc, hφi_v, Category.assoc, w.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hφh_s, hφi_s, Category.id_comp]
  let φ : pullback toBaseX sA ≅ pullback toBaseX sA := ⟨φh, φi, hhi, hih⟩
  exact ⟨φ, v, hφh_s, hvu, hvt, hP, hφh_v⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem K_genericPoint_square_of_baseChange_modelAut
    (R : Type u) [CommRing R] (X : Scheme.{u}) (toBaseX : X ⟶ Spec (CommRingCat.of R))
    (R'' : Type u) [CommRing R''] [Algebra R R'']
    (X' : Scheme.{u}) (t' : X' ⟶ Spec (CommRingCat.of R'')) (u : X' ⟶ X)
    (hsq : IsPullback u t' toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R R''))))
    (w : X' ≅ X')

    (A : Type u) [CommRing A] [Algebra R A] (gA : R'' →+* A)
    (vA : pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ X')
    (hvAu : vA ≫ u = pullback.fst toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (hvAt : vA ≫ t' = pullback.snd toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ Spec.map (CommRingCat.ofHom gA))
    (φ : pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≅
        pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (hφv : φ.hom ≫ vA = vA ≫ w.hom)

    (K : Type u) [CommRing K] [Algebra R K] (gK : R'' →+* K)
    (vK : pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ X')
    (hvKu : vK ≫ u = pullback.fst toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hvKt : vK ≫ t' = pullback.snd toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ Spec.map (CommRingCat.ofHom gK))

    (i : A →+* K) (hi : i.comp gA = gK)
    (kA : pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
        pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (hkA₁ : kA ≫ pullback.fst toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) =
        pullback.fst toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hkA₂ : kA ≫ pullback.snd toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R A))) =
        pullback.snd toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ Spec.map (CommRingCat.ofHom i)) :
    kA ≫ vA = vK ∧
    ∀ {T : Scheme.{u}} (a a' : T ⟶ pullback toBaseX (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      a' ≫ kA ≫ φ.hom = a ≫ kA → a ≫ vK = a' ≫ vK ≫ w.hom := by

  have hig : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom gA) = Spec.map (CommRingCat.ofHom gK) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hi]

  have hsq' : kA ≫ vA = vK := by
    apply hsq.hom_ext
    · rw [Category.assoc, hvAu, hkA₁, hvKu]
    · rw [Category.assoc, hvAt, ← Category.assoc, hkA₂, Category.assoc, hig, hvKt]
  refine ⟨hsq', ?_⟩

  intro T a a' h
  have h' := congrArg (fun f => f ≫ vA) h
  simp only [Category.assoc] at h'
  rw [hφv, ← Category.assoc kA vA, hsq'] at h'

  simpa only [Category.assoc] using h'.symm

end PartH9
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

section PartF

namespace Ws6
namespace PlacePin

open AlgebraicCurve AlgebraicGeometry CategoryTheory

theorem isIntegral_toAlgHom_of_algEquiv {K F : Type*} [Field K] [Field F] [Algebra K F] (θ : F ≃ₐ[K] F) :
    θ.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ θ.surjective

theorem finiteAlong_toAlgHom_of_algEquiv {K F : Type*} [Field K] [Field F] [Algebra K F] (θ : F ≃ₐ[K] F) :
    FiniteAlong K θ.toAlgHom := by
  unfold FiniteAlong
  exact RingHom.Finite.of_surjective θ.toAlgHom.toRingHom θ.surjective

theorem smul_eq_of_eq_restrictAlong {K F : Type*} [Field K] [Field F] [Algebra K F]
    (θ : F ≃ₐ[K] F) (hint : θ.toAlgHom.toRingHom.IsIntegral)
    (P P' : Place K F) (h : P = P'.restrictAlong θ.toAlgHom hint) :
    P' = SemilinearAut.ofAlgAut θ • P := by
  rw [h, AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul, smul_smul, ← map_mul, AlgEquiv.aut_mul,
    AlgEquiv.symm_trans_self, ← AlgEquiv.aut_one, map_one, one_smul]

theorem pointEquivPlace_eq_ofAlgAut_smul_of_eq_restrictAlong
    {K : Type*} [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F] (C : CurveModel K F)
    (θ : F ≃ₐ[K] F) (hint : θ.toAlgHom.toRingHom.IsIntegral)
    (y y' : {q : Spec (CommRingCat.of K) ⟶ C.C // q ≫ C.toBase = 𝟙 _})
    (h584 : C.pointEquivPlace y = (C.pointEquivPlace y').restrictAlong θ.toAlgHom hint) :
    C.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • C.pointEquivPlace y :=
  smul_eq_of_eq_restrictAlong θ hint _ _ h584

end Ws6.PlacePin
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

end PartF
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

namespace W5H10

section Generic

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem germToFunctionField_app_chart_comp
    {M X X'' : Scheme.{u}} [IsIntegral M] (π'' : M ⟶ X'') (ũ : X'' ⟶ X)
    {A A'' : CommRingCat.{u}} (ι : Spec A ⟶ X) [IsOpenImmersion ι] (ι'' : Spec A'' ⟶ X'') [IsOpenImmersion ι'']
    (c : A ⟶ A'') (h : ι'' ≫ ũ = Spec.map c ≫ ι)
    [Nonempty (Scheme.Opens.toScheme ((π'' ≫ ũ) ⁻¹ᵁ (ι ''ᵁ ⊤)))] [Nonempty (Scheme.Opens.toScheme (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤)))]
    (a : A) :
    M.germToFunctionField ((π'' ≫ ũ) ⁻¹ᵁ (ι ''ᵁ ⊤))
        (((π'' ≫ ũ).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a))) =
      M.germToFunctionField (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤))
        ((π''.app (ι'' ''ᵁ ⊤)).hom ((ι''.appIso ⊤).inv ((Scheme.ΓSpecIso A'').inv (c a)))) := by

  have hle : ι'' ''ᵁ ⊤ ≤ ũ ⁻¹ᵁ (ι ''ᵁ ⊤) := by
    rintro x ⟨y, -, rfl⟩
    have hy := Scheme.Hom.comp_apply ι'' ũ y
    rw [h, Scheme.Hom.comp_apply] at hy
    exact ⟨Spec.map c y, trivial, hy⟩
  have hle' : π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤) ≤ (π'' ≫ ũ) ⁻¹ᵁ (ι ''ᵁ ⊤) := fun x hx => hle hx

  have keyHom : (ι''.appIso ⊤).hom ((ũ.appLE (ι ''ᵁ ⊤) (ι'' ''ᵁ ⊤) hle).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a))) =
      (Scheme.ΓSpecIso A'').inv (c a) := by
    have H : ∀ {g : Spec A'' ⟶ X} (hg : Spec.map c ≫ ι = g) (e : (⊤ : (Spec A'').Opens) ≤ g ⁻¹ᵁ (ι ''ᵁ ⊤)),
        g.appLE (ι ''ᵁ ⊤) ⊤ e = (Spec.map c ≫ ι).appLE (ι ''ᵁ ⊤) ⊤ (hg ▸ e) := by
      rintro _ rfl _; rfl
    have htop : (Spec.map c).appLE ⊤ ⊤ le_rfl = (Spec.map c).appTop := Scheme.Hom.appLE_eq_app _
    rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, H h.symm,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map c) ι (ι ''ᵁ ⊤) ⊤ ⊤ (ι.preimage_image_eq ⊤).ge le_rfl,
      ← Scheme.Hom.appIso_hom', htop, CommRingCat.comp_apply, Iso.inv_hom_id_apply,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  have key : (ũ.appLE (ι ''ᵁ ⊤) (ι'' ''ᵁ ⊤) hle).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)) =
      (ι''.appIso ⊤).inv ((Scheme.ΓSpecIso A'').inv (c a)) := by
    rw [← keyHom, Iso.hom_inv_id_apply]

  have e3 : (π'' ≫ ũ).appLE (ι ''ᵁ ⊤) (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤)) hle' =
      ũ.appLE (ι ''ᵁ ⊤) (ι'' ''ᵁ ⊤) hle ≫ π''.app (ι'' ''ᵁ ⊤) := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
  calc M.germToFunctionField ((π'' ≫ ũ) ⁻¹ᵁ (ι ''ᵁ ⊤))
        (((π'' ≫ ũ).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))
      = M.germToFunctionField (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤))
          (((π'' ≫ ũ).appLE (ι ''ᵁ ⊤) (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤)) hle').hom
            ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a))) := by
        rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
        exact (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hle') _ _ _).symm
    _ = M.germToFunctionField (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤))
          ((π''.app (ι'' ''ᵁ ⊤)).hom ((ι''.appIso ⊤).inv ((Scheme.ΓSpecIso A'').inv (c a)))) := by
        rw [e3, CommRingCat.comp_apply, key]

theorem germToFunctionField_app_chart_base
    {M X'' : Scheme.{u}} [IsIntegral M] (π'' : M ⟶ X'')
    {K R A'' : CommRingCat.{u}} (s : M ⟶ Spec K) (β : X'' ⟶ Spec R) (φ : R ⟶ K)
    (hπ : π'' ≫ β = s ≫ Spec.map φ)
    (ι'' : Spec A'' ⟶ X'') [IsOpenImmersion ι''] (τ : R ⟶ A'') (hτ : ι'' ≫ β = Spec.map τ)
    [Nonempty (Scheme.Opens.toScheme (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤)))] (r : R) :
    M.germToFunctionField (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤))
        ((π''.app (ι'' ''ᵁ ⊤)).hom ((ι''.appIso ⊤).inv ((Scheme.ΓSpecIso A'').inv (τ r)))) =
      (M.presheaf.germ ⊤ (genericPoint M) trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso K).inv (φ r))) := by

  have keyHom : (ι''.appIso ⊤).hom ((β.appLE ⊤ (ι'' ''ᵁ ⊤) le_top).hom ((Scheme.ΓSpecIso R).inv r)) =
      (Scheme.ΓSpecIso A'').inv (τ r) := by
    have H : ∀ {g : Spec A'' ⟶ Spec R} (hg : Spec.map τ = g) (e : (⊤ : (Spec A'').Opens) ≤ g ⁻¹ᵁ ⊤),
        g.appLE ⊤ ⊤ e = (Spec.map τ).appLE ⊤ ⊤ (hg ▸ e) := by
      rintro _ rfl _; rfl
    have htop : (Spec.map τ).appLE ⊤ ⊤ le_rfl = (Spec.map τ).appTop := Scheme.Hom.appLE_eq_app _
    rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, H hτ.symm, htop,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  have key : (ι''.appIso ⊤).inv ((Scheme.ΓSpecIso A'').inv (τ r)) =
      (β.appLE ⊤ (ι'' ''ᵁ ⊤) le_top).hom ((Scheme.ΓSpecIso R).inv r) := by
    rw [← keyHom, Iso.hom_inv_id_apply]

  have e3 : β.appLE ⊤ (ι'' ''ᵁ ⊤) le_top ≫ π''.app (ι'' ''ᵁ ⊤) = (π'' ≫ β).appLE ⊤ (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤)) le_top := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
  calc M.germToFunctionField (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤))
        ((π''.app (ι'' ''ᵁ ⊤)).hom ((ι''.appIso ⊤).inv ((Scheme.ΓSpecIso A'').inv (τ r))))
      = M.germToFunctionField (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤))
          ((π''.app (ι'' ''ᵁ ⊤)).hom ((β.appLE ⊤ (ι'' ''ᵁ ⊤) le_top).hom ((Scheme.ΓSpecIso R).inv r))) := by rw [key]
    _ = M.germToFunctionField (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤))
          (((π'' ≫ β).appLE ⊤ (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤)) le_top).hom ((Scheme.ΓSpecIso R).inv r)) := by rw [← e3]; rfl
    _ = M.germToFunctionField (π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤))
          ((M.presheaf.map (homOfLE (le_top : π'' ⁻¹ᵁ (ι'' ''ᵁ ⊤) ≤ ⊤)).op).hom
            (((π'' ≫ β).appTop).hom ((Scheme.ΓSpecIso R).inv r))) := rfl
    _ = (M.presheaf.germ ⊤ (genericPoint M) trivial).hom (((π'' ≫ β).appTop).hom ((Scheme.ΓSpecIso R).inv r)) := by
        exact TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE le_top) _ _ _
    _ = (M.presheaf.germ ⊤ (genericPoint M) trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso K).inv (φ r))) := by
        rw [hπ]
        change (M.presheaf.germ ⊤ (genericPoint M) trivial).hom
            (s.appTop.hom (((Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop).hom r)) = _
        rw [← Scheme.ΓSpecIso_inv_naturality]
        rfl

theorem germToFunctionField_app_congr_hom {M X : Scheme.{u}} [IsIntegral M] {f g : M ⟶ X} (hfg : f = g) (V : X.Opens)
    [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ V))] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V))] (s : Γ(X, V)) :
    M.germToFunctionField (f ⁻¹ᵁ V) ((f.app V).hom s) = M.germToFunctionField (g ⁻¹ᵁ V) ((g.app V).hom s) := by
  subst hfg; rfl

end Generic
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

end W5H10
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

section PartH10

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups

noncomputable section

namespace W5H10

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)
  (L : Type) [Field L] [CharZero L] (ιA : L →+* AlgebraicClosure ℚ)

theorem coeffMap_ιA_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap ιA (coeffEmb L x) = coeffEmb (AlgebraicClosure ℚ) x := by
  unfold coeffEmb
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_rat _ _) x

theorem coeffMap_mem_xHFunctionFieldBar (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) :
    coeffMap ιA (f : LaurentSeries L) ∈ xHFunctionFieldBar M H := by
  obtain ⟨x, hx0⟩ := f
  change coeffMap ιA x ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (ΓM M H))
  unfold laurentBaseChange at hx0
  induction hx0 using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨x0, hm, rfl⟩ := hx
    rw [coeffMap_ιA_coeffEmb]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hm
  | algebraMap l =>
    rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact IntermediateField.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

variable (R'' : Type) [CommRing R''] [Algebra (R p) R''] [Algebra R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))]
  [Algebra R'' (AlgebraicClosure ℚ)]
  (j' : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) [Fact (j' ≠ 0)]

abbrev X'' : Scheme.{0} := AlgebraicCurve.TwoChartIntegralModel R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'

def ι'' (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')) : ↥(xHFunctionFieldBar M H) :=
  ⟨coeffMap ιA ((b : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L),
    coeffMap_mem_xHFunctionFieldBar M H L ιA b⟩

theorem readingPin
    (ũ : X'' M H L R'' j' ⟶ X p (ΓM M H) hj)
    (hũ : ũ ≫ toBase p (ΓM M H) hj =
      AlgebraicCurve.TwoChartIntegralModel.toBase R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ≫
        Spec.map (CommRingCat.ofHom (algebraMap (R p) R'')))
    (c : ↥(chartAlgFin p (ΓM M H) hj) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'))
    (hc : ∀ a, (((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' _ j')) : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) =
      coeffEmb L ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))
    (hũchart : AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j' ≫ ũ = Spec.map (CommRingCat.ofHom c) ≫ ιFin p (ΓM M H) hj)
    (τ : R'' →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'))
    (hτ : ∀ r, ((τ r : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' _ j')) : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) = algebraMap R'' _ r)
    (hτchart : AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j' ≫
      AlgebraicCurve.TwoChartIntegralModel.toBase R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' =
        Spec.map (CommRingCat.ofHom τ))
    (hspan : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'),
      (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' _ j')) ∈ Subring.closure (Set.range c ∪ Set.range τ))
    (vK : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ X'' M H L R'' j')
    (hvKu : vK ≫ ũ = pullback.fst _ _)
    (hvK : IsPullback vK (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
      (AlgebraicCurve.TwoChartIntegralModel.toBase R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')
      (Spec.map (CommRingCat.ofHom (algebraMap R'' (AlgebraicClosure ℚ)))))
    (hιAR : ∀ r : R'', algebraMap R'' (AlgebraicClosure ℚ) r =
      ιA ((((algebraMap R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) r : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L).coeff 0)))

    (hR''const : ∀ r : R'', coeffMap ιA (((algebraMap R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) r :
        ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap R'' (AlgebraicClosure ℚ) r)) :
    [Nonempty (Scheme.Opens.toScheme
      ((((𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j') ''ᵁ ⊤))))] →
    ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'),
      𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField
          (((𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j') ''ᵁ ⊤))
          ((((𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j') ''ᵁ ⊤)).hom
            (((AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j').appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'))).inv b)))) =
      ι'' M H L ιA R'' j' b := by

  intro hne b

  have hπ'' : (𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _ = 𝔛.eeta ≫ vK := by
    rw [Category.assoc, IsPullback.isoPullback_hom_fst]
  have hπũ : ((𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _) ≫ ũ =
      𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
    rw [hπ'', Category.assoc, hvKu]
  have hπβ : ((𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _) ≫
      AlgebraicCurve.TwoChartIntegralModel.toBase R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' =
        𝔛.Meta.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap R'' (AlgebraicClosure ℚ))) := by
    rw [hπ'', Category.assoc, hvK.w, ← Category.assoc, 𝔛.heeta]
  haveI : Nonempty (Scheme.Opens.toScheme
      ((((𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _) ≫ ũ) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) := by
    rw [hπũ]; infer_instance

  let Rd : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') →+*
      ↥(xHFunctionFieldBar M H) :=
    𝔛.Meta.ffEquiv.symm.toRingHom.comp
      ((𝔛.Meta.C.germToFunctionField
          (((𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j') ''ᵁ ⊤))).hom.comp
        (((((𝔛.eeta ≫ hvK.isoPullback.hom) ≫ pullback.fst _ _).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j') ''ᵁ ⊤)).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin R'' _ j').appIso ⊤).inv.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'))).inv.hom)))))
  let ιh : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') →+*
      ↥(xHFunctionFieldBar M H) :=
    { toFun := ι'' M H L ιA R'' j'
      map_one' := Subtype.ext (by simp [ι''])
      map_mul' := fun x y => Subtype.ext (by simp [ι''])
      map_zero' := Subtype.ext (by simp [ι''])
      map_add' := fun x y => Subtype.ext (by simp [ι'']) }

  have key : Set.EqOn Rd ιh (Set.range c ∪ Set.range τ) := by
    rintro _ (⟨a, rfl⟩ | ⟨r, rfl⟩)
    · have h1 : Rd (c a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField
          ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓM M H) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv a)))) := by
        show 𝔛.Meta.ffEquiv.symm _ = _
        exact congrArg 𝔛.Meta.ffEquiv.symm
          ((germToFunctionField_app_chart_comp _ ũ (ιFin p (ΓM M H) hj) _ (CommRingCat.ofHom c) hũchart a).symm.trans
            (germToFunctionField_app_congr_hom hπũ _ _))
      apply Subtype.ext
      rw [h1]
      refine (𝔛.Meta_pin a).trans ?_
      change _ = coeffMap ιA (((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' _ j')) :
        ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L)
      rw [hc, coeffMap_ιA_coeffEmb]
    · have h2 : Rd (τ r) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (algebraMap R'' (AlgebraicClosure ℚ) r) := by
        show 𝔛.Meta.ffEquiv.symm _ = _
        rw [RingEquiv.symm_apply_eq, 𝔛.Meta.ffEquiv_algebraMap]
        exact germToFunctionField_app_chart_base _ 𝔛.Meta.toBase
          (AlgebraicCurve.TwoChartIntegralModel.toBase R'' ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')
          (CommRingCat.ofHom (algebraMap R'' (AlgebraicClosure ℚ))) hπβ _ (CommRingCat.ofHom τ) hτchart r
      apply Subtype.ext
      rw [h2]
      change algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap R'' (AlgebraicClosure ℚ) r) =
        coeffMap ιA (((τ r : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R'' _ j')) :
          ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L)
      rw [hτ, hR''const]

  exact RingHom.eqOn_set_closure key (hspan b)

end W5H10
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

end PartH10
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

section PartH2cWs44

open ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

namespace W5H2c

open W5H2

variable (p : ℕ) [Fact p.Prime]

theorem exists_mul_natCast_mem_adjoin (L : Type) [Field L] [CharZero L] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ n) (z : L) :
    ∃ d : ℕ, d ≠ 0 ∧ z * (d : L) ∈ Algebra.adjoin (R p) ({ζ} : Set L) := by
  classical
  let B := hζ.powerBasis ℚ
  have hz : z = ∑ i, B.basis.repr z i • B.basis i := (B.basis.sum_repr z).symm
  let d : ℕ := ∏ i, (B.basis.repr z i).den
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (B.basis.repr z i).den_nz
  have hdi : ∀ i, ∃ m : ℤ, (d : ℚ) * B.basis.repr z i = m := by
    intro i
    have hdvd : (B.basis.repr z i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k * (B.basis.repr z i).num, ?_⟩
    rw [hk, Nat.cast_mul, mul_comm ((B.basis.repr z i).den : ℚ), mul_assoc, Rat.den_mul_eq_num, Int.cast_mul, Int.cast_natCast]
  choose m hm using hdi
  have hζmem : ζ ∈ Algebra.adjoin (R p) ({ζ} : Set L) := Algebra.self_mem_adjoin_singleton (R p) ζ
  refine ⟨d, hd, ?_⟩
  have hzd : z * (d : L) = ∑ i, ((m i : ℤ) : L) * ζ ^ (i : ℕ) := by
    rw [hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerBasis.coe_basis, IsPrimitiveRoot.powerBasis_gen]
    have hmi : ((m i : ℤ) : L) = (d : L) * algebraMap ℚ L (B.basis.repr z i) := by
      rw [← map_intCast (algebraMap ℚ L), ← hm i, map_mul, map_natCast]
    rw [hmi, Algebra.smul_def]
    ring
  rw [hzd]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Subalgebra.pow_mem _ hζmem _)

theorem isLocalization_adjoin (L : Type) [Field L] [CharZero L] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ n) :
    IsLocalization (Algebra.algebraMapSubmonoid ↥(Algebra.adjoin (R p) ({ζ} : Set L)) (nonZeroDivisors (R p))) L := by
  classical
  set R'' := Algebra.adjoin (R p) ({ζ} : Set L) with hR''
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, r, hr, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [← IsScalarTower.algebraMap_apply]
    have hr0 : (r : R p) ≠ 0 := nonZeroDivisors.ne_zero hr
    intro h
    apply hr0
    have hinj : Function.Injective (algebraMap (R p) L) :=
      (algebraMap ℚ L).injective.comp Subtype.val_injective
    exact hinj (by rw [h, map_zero])
  · intro z
    obtain ⟨d, hd, hzd⟩ := exists_mul_natCast_mem_adjoin p L ζ hζ z
    have hdR : ((d : R p)) ∈ nonZeroDivisors (R p) := mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hd)
    refine ⟨(⟨z * (d : L), hzd⟩, ⟨algebraMap (R p) ↥R'' d, (d : R p), hdR, rfl⟩), ?_⟩
    show z * algebraMap ↥R'' L (algebraMap (R p) ↥R'' (d : R p)) = z * (d : L)
    rw [← IsScalarTower.algebraMap_apply, map_natCast]
  · intro x y hxy
    exact ⟨1, by rw [Subtype.val_injective hxy]⟩

theorem isPushout_rat_adjoin (L : Type) [Field L] [CharZero L] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ n) :
    Algebra.IsPushout (R p) ℚ ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L := by
  haveI := isLocalization_adjoin p L ζ hζ
  exact (Algebra.isPushout_of_isLocalization (nonZeroDivisors (R p)) ℚ ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L).symm

theorem ringHom_Rp_eq {X : Type*} [DivisionRing X] [CharZero X] (f g : R p →+* X) : f = g := by
  refine RingHom.ext fun r => ?_
  have hden : (((r : ℚ).den : ℕ) : X) ≠ 0 := Nat.cast_ne_zero.mpr (r : ℚ).den_nz
  have hR : r * (((r : ℚ).den : ℕ) : R p) = (((r : ℚ).num : ℤ) : R p) := by
    apply Subtype.ext
    show (r : ℚ) * ((((r : ℚ).den : ℕ) : R p) : ℚ) = ((((r : ℚ).num : ℤ) : R p) : ℚ)
    rw [show ((((r : ℚ).den : ℕ) : R p) : ℚ) = ((r : ℚ).den : ℚ) from rfl,
      show ((((r : ℚ).num : ℤ) : R p) : ℚ) = ((r : ℚ).num : ℚ) from rfl]
    exact Rat.mul_den_eq_num (r : ℚ)
  have key : ∀ h : R p →+* X, h r * (((r : ℚ).den : ℕ) : X) = (((r : ℚ).num : ℤ) : X) := fun h => by
    have h2 := congrArg h hR
    rwa [map_mul, map_natCast, map_intCast] at h2
  exact mul_right_cancel₀ hden ((key f).trans (key g).symm)

theorem isScalarTower_Rp (A B : Type*) [CommSemiring A] [DivisionRing B] [CharZero B]
    [Algebra (R p) A] [Algebra (R p) B] [Algebra A B] : IsScalarTower (R p) A B :=
  IsScalarTower.of_algebraMap_eq fun r =>
    RingHom.congr_fun (ringHom_Rp_eq p (algebraMap (R p) B) ((algebraMap A B).comp (algebraMap (R p) A))) r

end W5H2c
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

set_option synthInstance.maxHeartbeats 1600000 in

theorem W5H2.isScalarTower_R (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (L : Type) [Field L] [CharZero L] :
    letI := W5H2.algLForm M H L
    IsScalarTower (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) := by
  letI := W5H2.algLForm M H L
  exact W5H2c.isScalarTower_Rp p ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))

set_option synthInstance.maxHeartbeats 1600000 in

theorem W5H2.isScalarTower_R'' (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (L : Type) [Field L] [CharZero L] (ζ : L) :
    IsScalarTower (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) := by
  exact W5H2c.isScalarTower_Rp p ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem W5H2.H2c_isPushout (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (L : Type) [Field L] [CharZero L]
    {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ n) :
    letI := W5H2.algLForm M H L
    haveI := W5H2.isScalarTower_R p M H L
    haveI := W5H2.isScalarTower_R'' p M H L ζ
    Algebra.IsPushout (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) := by
  letI := W5H2.algLForm M H L
  haveI := W5H2.isScalarTower_rat M H L
  haveI := W5H2.isScalarTower_R p M H L
  haveI := W5H2.isScalarTower_R'' p M H L ζ
  haveI : IsScalarTower (R p) L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    W5H2c.isScalarTower_Rp p L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {n} ℚ L
  haveI : IsScalarTower ℚ L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    IsScalarTower.of_algebraMap_eq (fun q => (RingHom.congr_fun (RingHom.ext_rat
      ((algebraMap L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))).comp (algebraMap ℚ L))
      (algebraMap ℚ ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))) q).symm)
  haveI : IsScalarTower (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) :=
    W5H2c.isScalarTower_Rp p ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H))
  haveI : IsScalarTower (R p) ℚ L := W5H2c.isScalarTower_Rp p ℚ L
  haveI : IsScalarTower (R p) ℚ ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    W5H2c.isScalarTower_Rp p ℚ ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
  haveI hleft : Algebra.IsPushout (R p) ℚ ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L := W5H2c.isPushout_rat_adjoin p L ζ hζ
  have hright : Algebra.IsPushout ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    (H2a_isPushout M H L).symm
  have hbig : Algebra.IsPushout (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(Algebra.adjoin (R p) ({ζ} : Set L))
      ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    (Algebra.IsPushout.comp_iff (R := R p) (S := ℚ) (R' := ↥(Algebra.adjoin (R p) ({ζ} : Set L))) (S' := L)
      (T := ↥(qExpFunctionFieldC ℚ (ΓM M H))) (T' := ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))).mpr hright
  exact hbig.symm

end PartH2cWs44
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

section PartH3Ws44

open ModularCurve ModularCurve.XHDRLevel AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups TensorProduct

namespace W5H3

theorem chartAlg_toSubmodule_eq_span
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (R'' : Type u) [CommRing R''] [Algebra R R''] [Algebra.IsIntegral R R'']
    (F' : Type u) [Field F'] [Algebra R F'] [Algebra R'' F'] [Algebra F F']
    [IsScalarTower R R'' F'] [IsScalarTower R F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (B : PowerBasis F F') (hgen : IsIntegral R B.gen)
    (hdisc : ∃ d : Rˣ, algebraMap R F (d : R) = Algebra.discr F (fun i : Fin B.dim => B.gen ^ (i : ℕ)))
    (hζ : B.gen ∈ Set.range (algebraMap R'' F'))
    (S : Set F) :
    Subalgebra.toSubmodule (chartAlg R F' (algebraMap F F' '' S)) =
      (Submodule.span R'' (algebraMap F F' '' (chartAlg R F S : Set F))).restrictScalars R := by
  classical
  obtain ⟨hiff, -⟩ := AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr R F F' B hgen hdisc S
  obtain ⟨z, hz⟩ := hζ
  have hmapS : ∀ y : F, y ∈ chartAlg R F S → algebraMap F F' y ∈ chartAlg R F' (algebraMap F F' '' S) := by
    intro y hy
    rw [mem_chartAlg_iff] at hy ⊢
    have hle : (Algebra.adjoin R S).map (IsScalarTower.toAlgHom R F F') ≤ Algebra.adjoin R (algebraMap F F' '' S) := by
      rw [AlgHom.map_adjoin]; rfl
    have h1 : IsIntegral ((Algebra.adjoin R S).map (IsScalarTower.toAlgHom R F F')) (algebraMap F F' y) :=
      hy.map_of_comp_eq (((IsScalarTower.toAlgHom R F F').subalgebraMap (Algebra.adjoin R S)).toRingHom)
        (algebraMap F F') (by ext; rfl)
    exact h1.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id F') (by ext; rfl)
  have hR'' : ∀ r : R'', algebraMap R'' F' r ∈ chartAlg R F' (algebraMap F F' '' S) := by
    intro r
    rw [mem_chartAlg_iff]
    have hr : IsIntegral R (algebraMap R'' F' r) :=
      (Algebra.IsIntegral.isIntegral (R := R) r).map (IsScalarTower.toAlgHom R R'' F')
    exact hr.tower_top
  apply le_antisymm
  · intro x hx
    rw [Subalgebra.mem_toSubmodule] at hx
    obtain ⟨b, rfl⟩ := (hiff x).mp hx
    rw [Submodule.restrictScalars_mem]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hz, ← map_pow, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, (b i).2, rfl⟩)
  · let N : Submodule R'' F' :=
      { carrier := chartAlg R F' (algebraMap F F' '' S)
        add_mem' := fun ha hb => Subalgebra.add_mem _ ha hb
        zero_mem' := Subalgebra.zero_mem _
        smul_mem' := fun r x hx => by
          rw [Algebra.smul_def]
          exact Subalgebra.mul_mem _ (hR'' r) hx }
    have hle : Submodule.span R'' (algebraMap F F' '' (chartAlg R F S : Set F)) ≤ N := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact hmapS y hy
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    exact hle hx

theorem discr_pow_fin_congr {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {m n : ℕ} (h : m = n) (x : A) :
    Algebra.discr K (fun i : Fin m => x ^ (i : ℕ)) = Algebra.discr K (fun i : Fin n => x ^ (i : ℕ)) := by
  subst h; rfl

theorem exists_unit_R_coe_eq_intCast (p : ℕ) [Fact p.Prime] (D : ℤ) (hD : ¬ (p : ℤ) ∣ D) :
    ∃ d : (R p)ˣ, ((d : R p) : ℚ) = D := by
  have hp : p.Prime := Fact.out
  have hD0 : (D : ℚ) ≠ 0 := by
    rw [Int.cast_ne_zero]; rintro rfl; exact hD (dvd_zero _)
  have hmem : (D : ℚ) ∈ GaloisRep.ratLocalizedAt p := by
    show (D : ℚ).den.Coprime p
    rw [Rat.den_intCast]; exact Nat.coprime_one_left p
  have hmem' : (D : ℚ)⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
    show ((D : ℚ)⁻¹).den.Coprime p
    rw [Rat.inv_intCast_den, if_neg (by rintro rfl; exact hD (dvd_zero _))]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hD (Int.natCast_dvd.mpr h))).symm
  exact ⟨⟨⟨(D : ℚ), hmem⟩, ⟨(D : ℚ)⁻¹, hmem'⟩, Subtype.ext (mul_inv_cancel₀ hD0), Subtype.ext (inv_mul_cancel₀ hD0)⟩, rfl⟩

theorem hdisc (p Q : ℕ) [Fact p.Prime] [NeZero Q] (hpQ : ¬ p ∣ Q)
    (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {Q} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ Q)
    (F : Type*) [CommRing F] [Algebra ℚ F] [Algebra (R p) F] [IsScalarTower (R p) ℚ F]
    {F' : Type*} [CommRing F'] [Algebra F F'] {n : ℕ} (g : F') (hn : n = Module.finrank ℚ L)
    (hdiscr : Algebra.discr F (fun i : Fin n => g ^ (i : ℕ)) =
      algebraMap ℚ F (Algebra.discr ℚ (fun i : Fin n => (hζ.powerBasis ℚ).gen ^ (i : ℕ)))) :
    ∃ d : (R p)ˣ, algebraMap (R p) F (d : R p) = Algebra.discr F (fun i : Fin n => g ^ (i : ℕ)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨D, hDdvd, hDeq⟩ := IsCyclotomicExtension.exists_int_dvd_pow_totient_and_algebraMap_eq_discr_powerBasis (K := ℚ) hζ
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos Q))
  have hnd : n = (hζ.powerBasis ℚ).dim := hn.trans (PowerBasis.finrank (hζ.powerBasis ℚ))
  have hpD : ¬ (p : ℤ) ∣ D := by
    intro h
    have h' : (p : ℤ) ∣ (Q : ℤ) ^ Q.totient := h.trans hDdvd
    have hpQ' : (p : ℤ) ∣ (Q : ℤ) := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h'
    exact hpQ (Int.natCast_dvd_natCast.mp hpQ')
  obtain ⟨d, hd⟩ := exists_unit_R_coe_eq_intCast p D hpD
  refine ⟨d, ?_⟩
  rw [hdiscr, discr_pow_fin_congr hnd, ← hDeq, IsScalarTower.algebraMap_apply (R p) ℚ F, eq_intCast]
  exact congrArg (algebraMap ℚ F) hd

theorem hchart (p Q : ℕ) [Fact p.Prime] [NeZero Q] (hpQ : ¬ p ∣ Q)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {Q} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ Q)
    (R'' : Type) [CommRing R''] [Algebra (R p) R''] [Algebra.IsIntegral (R p) R'']
    (F : Type) [Field F] [Algebra ℚ F] [Algebra (R p) F] [IsScalarTower (R p) ℚ F]
    (F' : Type) [Field F'] [Algebra F F'] [Algebra (R p) F'] [IsScalarTower (R p) F F'] [Algebra L F']
    [Algebra R'' F'] [IsScalarTower (R p) R'' F']
    (hζR'' : algebraMap L F' ζ ∈ Set.range (algebraMap R'' F'))
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (B : PowerBasis F F') (hBgen : B.gen = algebraMap L F' ζ) (hBdim : B.dim = Module.finrank ℚ L)
    (hBint : IsIntegral ℤ B.gen)
    (hBdiscr : Algebra.discr F (fun i : Fin B.dim => B.gen ^ (i : ℕ)) =
      algebraMap ℚ F (Algebra.discr ℚ (fun i : Fin B.dim => (hζ.powerBasis ℚ).gen ^ (i : ℕ))))
    (S : Set F) :
    Subalgebra.toSubmodule (chartAlg (R p) F' (algebraMap F F' '' S)) =
      (Submodule.span R'' (algebraMap F F' '' (chartAlg (R p) F S : Set F))).restrictScalars (R p) :=
  chartAlg_toSubmodule_eq_span (R p) F R'' F' B hBint.tower_top
    (hdisc p Q hpQ L ζ hζ F B.gen hBdim hBdiscr) (hBgen ▸ hζR'') S

theorem algebraMap_zeta_mem_range (p : ℕ) (L : Type) [Field L] [CharZero L] (ζ : L) (F' : Type) [Field F'] [Algebra L F'] :
    algebraMap L F' ζ ∈ Set.range (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) F') :=
  ⟨⟨ζ, Algebra.self_mem_adjoin_singleton (R p) ζ⟩,
    (IsScalarTower.algebraMap_apply ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L F' _).symm⟩

end W5H3
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

namespace W5H3

theorem ringHom_R_ext (p : ℕ) {K : Type*} [DivisionRing K] [CharZero K] (f g : R p →+* K) : f = g := by
  refine RingHom.ext fun r => ?_
  have hden : (((r : ℚ).den : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (r : ℚ).den_nz
  have hmul : r * (((r : ℚ).den : ℕ) : R p) = (((r : ℚ).num : ℤ) : R p) := by
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (r : ℚ)
  have key : ∀ h : R p →+* K, h r * (((r : ℚ).den : ℕ) : K) = (((r : ℚ).num : ℤ) : K) := by
    intro h
    have := congrArg h hmul
    rwa [map_mul, map_natCast, map_intCast] at this
  exact mul_right_cancel₀ hden ((key f).trans (key g).symm)

end W5H3
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem W5H2.H3_chartAlg_toSubmodule_eq_span (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (L : Type) [Field L] [CharZero L] {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ n)
    (hpn : ¬ p ∣ n) (S : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
    letI := W5H2.algLForm M H L
    haveI := W5H2.isScalarTower_R'' p M H L ζ
    Subalgebra.toSubmodule (chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) '' S)) =
      (Submodule.span ↥(Algebra.adjoin (R p) ({ζ} : Set L)) (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) '' (chartAlg (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) S : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))))).restrictScalars (R p) := by
  letI := W5H2.algLForm M H L
  haveI := W5H2.isScalarTower_R'' p M H L ζ
  haveI := W5H2.isScalarTower_R p M H L
  obtain ⟨B, hBgen, hBdim, hBint, hBdiscr⟩ := H2b_powerBasis M H L n ζ hζ
  haveI : FiniteDimensional ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) := PowerBasis.finite B
  haveI : Algebra.IsSeparable ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) := inferInstance
  haveI : Algebra.IsIntegral (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) :=
    Algebra.IsIntegral.adjoin (fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]; exact (hζ.isIntegral (NeZero.pos n)).tower_top)
  exact W5H3.hchart p n hpn L ζ hζ ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
    (W5H3.algebraMap_zeta_mem_range p L ζ ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) B hBgen hBdim hBint hBdiscr S

set_option synthInstance.maxHeartbeats 1600000 in

theorem W5H2.H3_hchart (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (L : Type) [Field L] [CharZero L] {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ n)
    (hpn : ¬ p ∣ n) :
    letI := W5H2.algLForm M H L
    haveI := W5H2.isScalarTower_R'' p M H L ζ
    ∀ S : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)), S = {jAt (ΓM M H) hj} ∨ S = {(jAt (ΓM M H) hj)⁻¹} ∨ S = {jAt (ΓM M H) hj, (jAt (ΓM M H) hj)⁻¹} →
      Subalgebra.toSubmodule (chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) '' S)) =
        (Submodule.span ↥(Algebra.adjoin (R p) ({ζ} : Set L)) (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) '' (chartAlg (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) S : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))))).restrictScalars (R p) := by
  intro S _
  exact W5H2.H3_chartAlg_toSubmodule_eq_span p M H L ζ hζ hpn S

end PartH3Ws44
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

namespace Ws6
namespace W5

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

section TwoBaseIso

open CategoryTheory.Limits

variable (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] (F : Type u) [Field F]
  [Algebra R R'] [Algebra R' F] [Algebra R F] [IsScalarTower R R' F]

noncomputable def chartBaseChangeEquiv [Algebra.IsIntegral R R'] (S : Set F) :
    ↥(chartAlg R F S) ≃+* ↥(chartAlg R' F S) :=
  RingEquiv.ofBijective (chartBaseChange R F R' S)
    ⟨fun x y h => Subtype.ext (by
        simpa only [coe_chartBaseChange] using congrArg (fun z : ↥(chartAlg R' F S) => (z : F)) h),
     fun y => ⟨⟨(y : F), (mem_chartAlg_iff_of_isIntegral R R' F S y).mp y.2⟩,
        Subtype.ext (coe_chartBaseChange R F R' S _)⟩⟩

theorem chartBaseChangeEquiv_apply [Algebra.IsIntegral R R'] (S : Set F) (x : ↥(chartAlg R F S)) :
    chartBaseChangeEquiv R R' F S x = chartBaseChange R F R' S x := by
  rw [chartBaseChangeEquiv, RingEquiv.ofBijective_apply]

@[scoped simp] theorem coe_chartBaseChangeEquiv [Algebra.IsIntegral R R'] (S : Set F) (x : ↥(chartAlg R F S)) :
    ((chartBaseChangeEquiv R R' F S x : ↥(chartAlg R' F S)) : F) = x := by
  rw [chartBaseChangeEquiv_apply, coe_chartBaseChange]

@[scoped simp] theorem coe_chartBaseChangeEquiv_symm [Algebra.IsIntegral R R'] (S : Set F) (y : ↥(chartAlg R' F S)) :
    (((chartBaseChangeEquiv R R' F S).symm y : ↥(chartAlg R F S)) : F) = y := by
  have h := coe_chartBaseChangeEquiv R R' F S ((chartBaseChangeEquiv R R' F S).symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

@[scoped simp] theorem coe_toRingHom_chartBaseChangeEquiv [Algebra.IsIntegral R R'] (S : Set F) (x : ↥(chartAlg R F S)) :
    (((chartBaseChangeEquiv R R' F S).toRingHom x : ↥(chartAlg R' F S)) : F) = x := by
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact coe_chartBaseChangeEquiv R R' F S x

@[scoped simp] theorem coe_symm_toRingHom_chartBaseChangeEquiv [Algebra.IsIntegral R R'] (S : Set F) (y : ↥(chartAlg R' F S)) :
    (((chartBaseChangeEquiv R R' F S).symm.toRingHom y : ↥(chartAlg R F S)) : F) = y := by
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact coe_chartBaseChangeEquiv_symm R R' F S y

theorem toRingHom_chartBaseChangeEquiv_apply [Algebra.IsIntegral R R'] (S : Set F) (x : ↥(chartAlg R F S)) :
    (chartBaseChangeEquiv R R' F S).toRingHom x = chartBaseChange R F R' S x := by
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, chartBaseChangeEquiv_apply]

theorem toRingHom_comp_symm_toRingHom [Algebra.IsIntegral R R'] (S : Set F) :
    (chartBaseChangeEquiv R R' F S).toRingHom.comp (chartBaseChangeEquiv R R' F S).symm.toRingHom = RingHom.id _ :=
  RingHom.ext fun y => by
    simp only [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]

theorem symm_toRingHom_comp_toRingHom [Algebra.IsIntegral R R'] (S : Set F) :
    (chartBaseChangeEquiv R R' F S).symm.toRingHom.comp (chartBaseChangeEquiv R R' F S).toRingHom = RingHom.id _ :=
  RingHom.ext fun x => by
    simp only [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]

theorem toRingHom_chartBaseChangeEquiv_comp_algebraMap [Algebra.IsIntegral R R'] (S : Set F) :
    (chartBaseChangeEquiv R R' F S).toRingHom.comp (algebraMap R ↥(chartAlg R F S)) =
      (algebraMap R' ↥(chartAlg R' F S)).comp (algebraMap R R') :=
  RingHom.ext fun r => by
    rw [RingHom.comp_apply, RingHom.comp_apply, toRingHom_chartBaseChangeEquiv_apply, chartBaseChange_algebraMap]

variable (j : F) [Fact (j ≠ 0)]

omit [Fact (j ≠ 0)] in
theorem coe_toRingHom_inclFin (y : ↥(chartAlgFin R F j)) :
    (((inclFin R F j).toRingHom y : ↥(chartAlgMid R F j)) : F) = y := by
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  exact coe_chartIncl R F (sFin_subset F j) y

omit [Fact (j ≠ 0)] in
theorem coe_toRingHom_inclInf (y : ↥(chartAlgInf R F j)) :
    (((inclInf R F j).toRingHom y : ↥(chartAlgMid R F j)) : F) = y := by
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  exact coe_chartIncl R F (sInf_subset F j) y

omit [Fact (j ≠ 0)] in
theorem inclFin_comp_chartBaseChange [Algebra.IsIntegral R R'] :
    (inclFin R' F j).toRingHom.comp (chartBaseChangeEquiv R R' F {j}).toRingHom =
      (chartBaseChangeEquiv R R' F {j, j⁻¹}).toRingHom.comp (inclFin R F j).toRingHom :=
  RingHom.ext fun x => Subtype.ext (by
    simp only [RingHom.comp_apply, coe_toRingHom_inclFin, coe_toRingHom_chartBaseChangeEquiv])

omit [Fact (j ≠ 0)] in
theorem inclInf_comp_chartBaseChange [Algebra.IsIntegral R R'] :
    (inclInf R' F j).toRingHom.comp (chartBaseChangeEquiv R R' F {j⁻¹}).toRingHom =
      (chartBaseChangeEquiv R R' F {j, j⁻¹}).toRingHom.comp (inclInf R F j).toRingHom :=
  RingHom.ext fun x => Subtype.ext (by
    simp only [RingHom.comp_apply, coe_toRingHom_inclInf, coe_toRingHom_chartBaseChangeEquiv])

omit [Fact (j ≠ 0)] in
theorem inclFin_comp_chartBaseChange_symm [Algebra.IsIntegral R R'] :
    (inclFin R F j).toRingHom.comp (chartBaseChangeEquiv R R' F {j}).symm.toRingHom =
      (chartBaseChangeEquiv R R' F {j, j⁻¹}).symm.toRingHom.comp (inclFin R' F j).toRingHom :=
  RingHom.ext fun x => Subtype.ext (by
    simp only [RingHom.comp_apply, coe_toRingHom_inclFin, coe_symm_toRingHom_chartBaseChangeEquiv])

omit [Fact (j ≠ 0)] in
theorem inclInf_comp_chartBaseChange_symm [Algebra.IsIntegral R R'] :
    (inclInf R F j).toRingHom.comp (chartBaseChangeEquiv R R' F {j⁻¹}).symm.toRingHom =
      (chartBaseChangeEquiv R R' F {j, j⁻¹}).symm.toRingHom.comp (inclInf R' F j).toRingHom :=
  RingHom.ext fun x => Subtype.ext (by
    simp only [RingHom.comp_apply, coe_toRingHom_inclInf, coe_symm_toRingHom_chartBaseChangeEquiv])

omit [Fact (j ≠ 0)] in
theorem fFin_comp_spec_chartBaseChange [Algebra.IsIntegral R R'] :
    fFin R' F j ≫ Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).toRingHom) =
      Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j, j⁻¹}).toRingHom) ≫ fFin R F j := by
  simp only [fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp, inclFin_comp_chartBaseChange]

omit [Fact (j ≠ 0)] in
theorem fInf_comp_spec_chartBaseChange [Algebra.IsIntegral R R'] :
    fInf R' F j ≫ Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).toRingHom) =
      Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j, j⁻¹}).toRingHom) ≫ fInf R F j := by
  simp only [fInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, inclInf_comp_chartBaseChange]

omit [Fact (j ≠ 0)] in
theorem fFin_comp_spec_chartBaseChange_symm [Algebra.IsIntegral R R'] :
    fFin R F j ≫ Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).symm.toRingHom) =
      Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j, j⁻¹}).symm.toRingHom) ≫ fFin R' F j := by
  simp only [fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp, inclFin_comp_chartBaseChange_symm]

omit [Fact (j ≠ 0)] in
theorem fInf_comp_spec_chartBaseChange_symm [Algebra.IsIntegral R R'] :
    fInf R F j ≫ Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).symm.toRingHom) =
      Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j, j⁻¹}).symm.toRingHom) ≫ fInf R' F j := by
  simp only [fInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, inclInf_comp_chartBaseChange_symm]

noncomputable def twoBaseHom [Algebra.IsIntegral R R'] :
    AlgebraicCurve.TwoChartIntegralModel R' F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  pushout.desc (Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).toRingHom) ≫ ιFin R F j)
    (Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).toRingHom) ≫ ιInf R F j)
    (by rw [← Category.assoc, fFin_comp_spec_chartBaseChange, Category.assoc, glue_condition,
          ← Category.assoc, ← fInf_comp_spec_chartBaseChange, Category.assoc])

noncomputable def twoBaseInv [Algebra.IsIntegral R R'] :
    AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R' F j :=
  pushout.desc (Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).symm.toRingHom) ≫ ιFin R' F j)
    (Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).symm.toRingHom) ≫ ιInf R' F j)
    (by rw [← Category.assoc, fFin_comp_spec_chartBaseChange_symm, Category.assoc, glue_condition,
          ← Category.assoc, ← fInf_comp_spec_chartBaseChange_symm, Category.assoc])

@[reassoc] theorem ιFin_twoBaseHom [Algebra.IsIntegral R R'] :
    ιFin R' F j ≫ twoBaseHom R R' F j = Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).toRingHom) ≫ ιFin R F j :=
  pushout.inl_desc _ _ _

@[reassoc] theorem ιInf_twoBaseHom [Algebra.IsIntegral R R'] :
    ιInf R' F j ≫ twoBaseHom R R' F j = Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).toRingHom) ≫ ιInf R F j :=
  pushout.inr_desc _ _ _

@[reassoc] theorem ιFin_twoBaseInv [Algebra.IsIntegral R R'] :
    ιFin R F j ≫ twoBaseInv R R' F j = Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).symm.toRingHom) ≫ ιFin R' F j :=
  pushout.inl_desc _ _ _

@[reassoc] theorem ιInf_twoBaseInv [Algebra.IsIntegral R R'] :
    ιInf R F j ≫ twoBaseInv R R' F j = Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).symm.toRingHom) ≫ ιInf R' F j :=
  pushout.inr_desc _ _ _

theorem ιFin_hom_inv [Algebra.IsIntegral R R'] :
    ιFin R' F j ≫ twoBaseHom R R' F j ≫ twoBaseInv R R' F j = ιFin R' F j ≫ 𝟙 _ := by
  rw [ιFin_twoBaseHom_assoc, ιFin_twoBaseInv, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]

theorem ιInf_hom_inv [Algebra.IsIntegral R R'] :
    ιInf R' F j ≫ twoBaseHom R R' F j ≫ twoBaseInv R R' F j = ιInf R' F j ≫ 𝟙 _ := by
  rw [ιInf_twoBaseHom_assoc, ιInf_twoBaseInv, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]

theorem ιFin_inv_hom [Algebra.IsIntegral R R'] :
    ιFin R F j ≫ twoBaseInv R R' F j ≫ twoBaseHom R R' F j = ιFin R F j ≫ 𝟙 _ := by
  rw [ιFin_twoBaseInv_assoc, ιFin_twoBaseHom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]

theorem ιInf_inv_hom [Algebra.IsIntegral R R'] :
    ιInf R F j ≫ twoBaseInv R R' F j ≫ twoBaseHom R R' F j = ιInf R F j ≫ 𝟙 _ := by
  rw [ιInf_twoBaseInv_assoc, ιInf_twoBaseHom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]

noncomputable def twoBaseIso [Algebra.IsIntegral R R'] :
    AlgebraicCurve.TwoChartIntegralModel R' F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j where
  hom := twoBaseHom R R' F j
  inv := twoBaseInv R R' F j
  hom_inv_id := pushout.hom_ext (by first | exact ιFin_hom_inv R R' F j | simpa only [Category.assoc] using ιFin_hom_inv R R' F j)
    (by first | exact ιInf_hom_inv R R' F j | simpa only [Category.assoc] using ιInf_hom_inv R R' F j)
  inv_hom_id := pushout.hom_ext (by first | exact ιFin_inv_hom R R' F j | simpa only [Category.assoc] using ιFin_inv_hom R R' F j)
    (by first | exact ιInf_inv_hom R R' F j | simpa only [Category.assoc] using ιInf_inv_hom R R' F j)

@[reassoc] theorem ιFin_twoBaseIso_hom [Algebra.IsIntegral R R'] :
    ιFin R' F j ≫ (twoBaseIso R R' F j).hom =
      Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).toRingHom) ≫ ιFin R F j :=
  ιFin_twoBaseHom R R' F j

@[reassoc] theorem ιInf_twoBaseIso_hom [Algebra.IsIntegral R R'] :
    ιInf R' F j ≫ (twoBaseIso R R' F j).hom =
      Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).toRingHom) ≫ ιInf R F j :=
  ιInf_twoBaseHom R R' F j

@[reassoc] theorem ιFin_twoBaseIso_inv [Algebra.IsIntegral R R'] :
    ιFin R F j ≫ (twoBaseIso R R' F j).inv =
      Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).symm.toRingHom) ≫ ιFin R' F j :=
  ιFin_twoBaseInv R R' F j

@[reassoc] theorem ιInf_twoBaseIso_inv [Algebra.IsIntegral R R'] :
    ιInf R F j ≫ (twoBaseIso R R' F j).inv =
      Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).symm.toRingHom) ≫ ιInf R' F j :=
  ιInf_twoBaseInv R R' F j

@[reassoc] theorem twoBaseIso_hom_toBase [Algebra.IsIntegral R R'] :
    (twoBaseIso R R' F j).hom ≫ toBase R F j = toBase R' F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  refine pushout.hom_ext ?_ ?_
  · change ιFin R' F j ≫ _ ≫ _ = ιFin R' F j ≫ _ ≫ _
    rw [ιFin_twoBaseIso_hom_assoc, ιFin_toBase, ιFin_toBase_assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, toRingHom_chartBaseChangeEquiv_comp_algebraMap]
  · change ιInf R' F j ≫ _ ≫ _ = ιInf R' F j ≫ _ ≫ _
    rw [ιInf_twoBaseIso_hom_assoc, ιInf_toBase, ιInf_toBase_assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, toRingHom_chartBaseChangeEquiv_comp_algebraMap]

theorem twoBaseIso_hom_comp_eq_toBase [Algebra.IsIntegral R R']
    (t' : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Spec (CommRingCat.of R'))
    (ht' : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = toBase R F j)
    (τ : R' →+* ↥(chartAlgFin R F j)) (hτ : ∀ r : R', ((τ r : ↥(chartAlgFin R F j)) : F) = algebraMap R' F r)
    (hτt : ιFin R F j ≫ t' = Spec.map (CommRingCat.ofHom τ)) :
    (twoBaseIso R R' F j).hom ≫ t' = toBase R' F j := by
  have hring : (chartBaseChangeEquiv R R' F {j}).toRingHom.comp τ = algebraMap R' ↥(chartAlgFin R' F j) :=
    RingHom.ext fun r => Subtype.ext (by
      rw [RingHom.comp_apply, coe_toRingHom_chartBaseChangeEquiv, hτ, Subalgebra.coe_algebraMap])
  refine AlgebraicCurve.TwoChartIntegralModel.hom_ext_of_iotaFin_comp_eq R' F j _ _
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ?_ ?_
  · rw [Category.assoc, ht', twoBaseIso_hom_toBase]
  · rw [ιFin_twoBaseIso_hom_assoc, hτt, ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]

theorem isIso_specMap_chartBaseChangeEquiv_symm [Algebra.IsIntegral R R'] (S : Set F) :
    IsIso (Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F S).symm.toRingHom)) :=
  ⟨⟨Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F S).toRingHom),
    by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id],
    by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id]⟩⟩

theorem isIso_specMap_chartBaseChangeEquiv [Algebra.IsIntegral R R'] (S : Set F) :
    IsIso (Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F S).toRingHom)) :=
  ⟨⟨Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F S).symm.toRingHom),
    by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id],
    by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id]⟩⟩

@[scoped simp] theorem twoBaseIso_hom_preimage_chartFinOpen [Algebra.IsIntegral R R'] :
    (twoBaseIso R R' F j).hom ⁻¹ᵁ chartFinOpen R F j = chartFinOpen R' F j := by
  haveI := isIso_specMap_chartBaseChangeEquiv_symm R R' F {j}
  rw [chartFinOpen, chartFinOpen, ← Scheme.Hom.inv_image, ← Scheme.Hom.opensRange_comp]
  have h2 : (ιFin R F j ≫ (twoBaseIso R R' F j).inv).opensRange =
      (Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j}).symm.toRingHom) ≫ ιFin R' F j).opensRange :=
    TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange, ιFin_twoBaseIso_inv])
  rw [h2, Scheme.Hom.opensRange_comp_of_isIso]

@[scoped simp] theorem twoBaseIso_hom_preimage_chartInfOpen [Algebra.IsIntegral R R'] :
    (twoBaseIso R R' F j).hom ⁻¹ᵁ chartInfOpen R F j = chartInfOpen R' F j := by
  haveI := isIso_specMap_chartBaseChangeEquiv_symm R R' F {j⁻¹}
  rw [chartInfOpen, chartInfOpen, ← Scheme.Hom.inv_image, ← Scheme.Hom.opensRange_comp]
  have h2 : (ιInf R F j ≫ (twoBaseIso R R' F j).inv).opensRange =
      (Spec.map (CommRingCat.ofHom (chartBaseChangeEquiv R R' F {j⁻¹}).symm.toRingHom) ≫ ιInf R' F j).opensRange :=
    TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange, ιInf_twoBaseIso_inv])
  rw [h2, Scheme.Hom.opensRange_comp_of_isIso]

theorem exists_iso_twoBase [Algebra.IsIntegral R R'] :
    ∃ (ι2 : AlgebraicCurve.TwoChartIntegralModel R' F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
      (idFin : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R' F j)) (idInf : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R' F j)),
      (∀ a, ((idFin a : ↥(chartAlgFin R' F j)) : F) = a) ∧ (∀ a, ((idInf a : ↥(chartAlgInf R' F j)) : F) = a) ∧
      ιFin R' F j ≫ ι2.hom = Spec.map (CommRingCat.ofHom idFin) ≫ ιFin R F j ∧
      ιInf R' F j ≫ ι2.hom = Spec.map (CommRingCat.ofHom idInf) ≫ ιInf R F j ∧
      ι2.hom ≫ toBase R F j = toBase R' F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
      (∀ (t' : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Spec (CommRingCat.of R'))
          (τ : R' →+* ↥(chartAlgFin R F j)),
        t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = toBase R F j →
        (∀ r : R', ((τ r : ↥(chartAlgFin R F j)) : F) = algebraMap R' F r) →
        ιFin R F j ≫ t' = Spec.map (CommRingCat.ofHom τ) → ι2.hom ≫ t' = toBase R' F j) :=
  ⟨twoBaseIso R R' F j, (chartBaseChangeEquiv R R' F {j}).toRingHom, (chartBaseChangeEquiv R R' F {j⁻¹}).toRingHom,
    coe_toRingHom_chartBaseChangeEquiv R R' F {j}, coe_toRingHom_chartBaseChangeEquiv R R' F {j⁻¹},
    ιFin_twoBaseIso_hom R R' F j, ιInf_twoBaseIso_hom R R' F j, twoBaseIso_hom_toBase R R' F j,
    fun t' τ ht' hτ hτt => twoBaseIso_hom_comp_eq_toBase R R' F j t' ht' τ hτ hτt⟩

theorem exists_iso_twoBase_of_eq [Algebra.IsIntegral R R'] (j' : F) [Fact (j' ≠ 0)] (hjj' : j = j') :
    ∃ (ι2 : AlgebraicCurve.TwoChartIntegralModel R' F j' ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
      (c2 : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R' F j')) (c2inf : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R' F j')),
      (∀ (t' : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Spec (CommRingCat.of R'))
          (τ : R' →+* ↥(chartAlgFin R F j)),
        t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = toBase R F j →
        (∀ r : R', ((τ r : ↥(chartAlgFin R F j)) : F) = algebraMap R' F r) →
        ιFin R F j ≫ t' = Spec.map (CommRingCat.ofHom τ) → ι2.hom ≫ t' = toBase R' F j') ∧
      (∀ a, ((c2 a : ↥(chartAlgFin R' F j')) : F) = a) ∧
      ιFin R' F j' ≫ ι2.hom = Spec.map (CommRingCat.ofHom c2) ≫ ιFin R F j ∧
      (∀ a, ((c2inf a : ↥(chartAlgInf R' F j')) : F) = a) ∧
      ιInf R' F j' ≫ ι2.hom = Spec.map (CommRingCat.ofHom c2inf) ≫ ιInf R F j ∧
      ι2.hom ≫ toBase R F j = toBase R' F j' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
      ι2.hom ⁻¹ᵁ chartFinOpen R F j = chartFinOpen R' F j' ∧
      ι2.hom ⁻¹ᵁ chartInfOpen R F j = chartInfOpen R' F j' := by
  subst hjj'
  exact ⟨twoBaseIso R R' F j, (chartBaseChangeEquiv R R' F {j}).toRingHom, (chartBaseChangeEquiv R R' F {j⁻¹}).toRingHom,
    fun t' τ ht' hτ hτt => twoBaseIso_hom_comp_eq_toBase R R' F j t' ht' τ hτ hτt,
    coe_toRingHom_chartBaseChangeEquiv R R' F {j}, ιFin_twoBaseIso_hom R R' F j,
    coe_toRingHom_chartBaseChangeEquiv R R' F {j⁻¹}, ιInf_twoBaseIso_hom R R' F j,
    twoBaseIso_hom_toBase R R' F j, twoBaseIso_hom_preimage_chartFinOpen R R' F j, twoBaseIso_hom_preimage_chartInfOpen R R' F j⟩

end TwoBaseIso
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

end Ws6.W5
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.H1 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6 P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin.Ws6.W5"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [Algebra (R p) ↥A] (hRA : ∀ r : R p, ((algebraMap (R p) ↥A r : ↥A) : AlgebraicClosure ℚ) = algebraMap (R p) (AlgebraicClosure ℚ) r)
    (kA : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hkA₁ : kA ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkA₂ : kA ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ barPt A)

    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {M / p} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ (M / p))
    (ιA : L →+* AlgebraicClosure ℚ)
    (hιA : ∀ r : R p, ιA (algebraMap (R p) L r) = algebraMap (R p) (AlgebraicClosure ℚ) r)
    (hιAζ : ιA ζ ∈ A)

    (j' : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))
    (hj' : ((j' : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) = coeffEmb L (jqModC ℚ)) [Fact (j' ≠ 0)]
    (σ : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) ≃ₐ[L] ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))
    (hσ : ∀ (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) (u : ↥(qExpFunctionFieldC ℚ (ΓM p (H.map (ZMod.unitsMap hpM))))),
        (f : LaurentSeries L) = coeffEmb L (u : LaurentSeries ℚ) →
          ((σ f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) = coeffEmb L (qExpand ℚ (M / p) (u : LaurentSeries ℚ)))
    [Fact (σ j' ≠ 0)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθσ : ∀ (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) (g : ↥(xHFunctionFieldBar M H)),
        (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap ιA (f : LaurentSeries L) →
          ((θ g : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffMap ιA ((σ f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L)) :
    ∃ (φ : pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ≅ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A)),

      φ.hom ≫ baseChange (R p) (toBase p (ΓM M H) hj) ↥A = baseChange (R p) (toBase p (ΓM M H) hj) ↥A ∧

      (∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ kA ≫ φ.hom = y.1 ≫ 𝔛.eeta ≫ kA →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) := by
  classical

  obtain ⟨hRdom, hRfree, hRfin, hRfrac⟩ := H1.order p L (n := M / p) ζ hζ
  haveI := hRdom; haveI := hRfree; haveI := hRfin; haveI := hRfrac

  letI instAlgF := W5H2.algLForm M H L
  haveI instTowF := W5H2.isScalarTower_rat M H L
  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {M / p} ℚ L
  obtain ⟨B, hBgen, hBdim, hBint, hBdisc⟩ := H2b_powerBasis M H L (M / p) ζ hζ

  haveI instTowRLF : IsScalarTower ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)

  have hj4 : algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj) = j' := by
    apply Subtype.ext
    rw [hj']
    change coeffEmb L ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = coeffEmb L (jqModC ℚ)
    rw [coe_jAt]

  haveI instTowQLF : IsScalarTower ℚ L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    IsScalarTower.of_algebraMap_eq (fun q =>
      (RingHom.congr_fun (RingHom.ext_rat ((algebraMap L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))).comp (algebraMap ℚ L))
        (algebraMap ℚ ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))) q).symm)

  have _p1 : ∀ r : R p, algebraMap (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) r =
      algebraMap ℚ ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (r : ℚ) := fun r => rfl
  have _p2 : ∀ r : R p, algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) r = algebraMap ℚ _ (r : ℚ) := fun r => rfl
  have _p3 : ∀ r : R p, algebraMap (R p) L r = algebraMap ℚ L (r : ℚ) := fun r => rfl
  have _p4 : ∀ r : R p, (algebraMap (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) r : L) = algebraMap (R p) L r := fun r => rfl
  haveI instTowRF0F : IsScalarTower (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [_p1, _p2]; exact IsScalarTower.algebraMap_apply ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ (r : ℚ))
  haveI instTowRRF : IsScalarTower (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [_p1, IsScalarTower.algebraMap_apply ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))]
      change _ = algebraMap L _ ((algebraMap (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) r : L))
      rw [_p4, _p3]
      exact IsScalarTower.algebraMap_apply ℚ L _ (r : ℚ))

  have H2c : Algebra.IsPushout (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L))
      ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) := by
    exact W5H2.H2c_isPushout p M H L ζ hζ

  have hchart : ∀ S : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)),
      S = {jAt (ΓM M H) hj} ∨ S = {(jAt (ΓM M H) hj)⁻¹} ∨ S = {jAt (ΓM M H) hj, (jAt (ΓM M H) hj)⁻¹} →
      Subalgebra.toSubmodule (TwoChartIntegralModel.chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
          (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) '' S)) =
        (Submodule.span ↥(Algebra.adjoin (R p) ({ζ} : Set L))
          (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) ''
            (TwoChartIntegralModel.chartAlg (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) S : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))))).restrictScalars (R p) := by
    have hpn : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two, ← Nat.mul_div_cancel' hpM]; exact Nat.mul_dvd_mul_left p h)
    exact W5H2.H3_hchart p M H hj L ζ hζ hpn

  have hTM : ModularGroup.T ∈ ΓM M H := translation_mem_GammaH M H
  haveI hFI_M : (ΓM M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  obtain ⟨hFTfin, hFTinf⟩ :=
    ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H) hTM (jAt (ΓM M H) hj) (coe_jAt _ hj)
  haveI := hFTfin; haveI := hFTinf

  haveI : Fact (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj) ≠ 0) := by
    rw [hj4]; infer_instance
  haveI := H2c
  obtain ⟨t', u, ht', hu, hsq, hpreFin, hpreInf, ⟨cR, hcR, hucR⟩, ⟨τR, hτR, htτR⟩⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_isPullback_toBase_specMap_and_iotaFin_comp_eq_of_isPushout_of_chartAlg_eq_span
      (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
      (jAt (ΓM M H) hj) hchart

  obtain ⟨w, θc, hwover, hθc, hwchart, hwpre⟩ :=
    Ws6.W5.H567_exists_iso p M H hpM hj L ↥(Algebra.adjoin (R p) ({ζ} : Set L)) j' hj' σ hσ hj4 hchart

  have twoBase : ∃ (ι2 : AlgebraicCurve.TwoChartIntegralModel ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' ≅
        AlgebraicCurve.TwoChartIntegralModel (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
          (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj)))
      (c2 : ↥(TwoChartIntegralModel.chartAlgFin (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
          (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj))) →+*
        ↥(TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')),
      ι2.hom ≫ t' = AlgebraicCurve.TwoChartIntegralModel.toBase ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j' ∧
      (∀ a, ((c2 a : ↥(TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j')) : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) = a) ∧
      AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j' ≫ ι2.hom =
        Spec.map (CommRingCat.ofHom c2) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin (R p) _ _ ∧
      ι2.hom ⁻¹ᵁ AlgebraicCurve.TwoChartIntegralModel.chartFinOpen (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
          (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj)) =
        AlgebraicCurve.TwoChartIntegralModel.chartFinOpen ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' := by

    obtain ⟨ι2, c2, c2inf, hiii, hc2v, hiFin, -, -, -, hpre, -⟩ :=
      Ws6.W5.exists_iso_twoBase_of_eq (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))
        (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) (jAt (ΓM M H) hj)) j' hj4
    exact ⟨ι2, c2, hiii t' τR ht' hτR htτR, hc2v, hiFin, hpre⟩
  obtain ⟨ι2, c2, hι2t, hc2, hι2chart, hι2pre⟩ := twoBase

  set ũ := ι2.hom ≫ u with hũdef
  have hsq'' : IsPullback ũ (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j')
      (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L))))) := by
    have hleft : IsPullback ι2.hom (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j') t' (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hι2t]⟩
    have := hleft.paste_horiz hsq
    rwa [Category.id_comp] at this
  have hũchart : AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j' ≫ ũ =
      Spec.map (CommRingCat.ofHom (c2.comp cR)) ≫ ιFin p (ΓM M H) hj := by
    rw [hũdef, ← Category.assoc, hι2chart, Category.assoc, hucR, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hιAmem : ∀ r : ↥(Algebra.adjoin (R p) ({ζ} : Set L)), ιA (r : L) ∈ A := by
    intro r
    refine Algebra.adjoin_induction (fun x hx => ?_) (fun r0 => ?_) (fun _ _ _ _ hx hy => ?_) (fun _ _ _ _ hx hy => ?_) r.2
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hιAζ
    · rw [hιA, ← hRA]; exact (algebraMap (R p) ↥A r0).2
    · rw [map_add]; exact A.add_mem _ _ hx hy
    · rw [map_mul]; exact A.mul_mem _ _ hx hy
  let gA : ↥(Algebra.adjoin (R p) ({ζ} : Set L)) →+* ↥A :=
    (ιA.comp (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L)).codRestrict A.toSubring (fun r => hιAmem r)
  have hgA : gA.comp (algebraMap (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L))) = algebraMap (R p) ↥A := by
    refine RingHom.ext fun r0 => Subtype.ext ?_
    change ιA (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L (algebraMap (R p) _ r0)) = _
    rw [← IsScalarTower.algebraMap_apply, hιA, hRA]

  obtain ⟨φ, vA, hφover, hvAu, hvAt, hsqA, hφv⟩ :=
    H9_baseChange_modelAut (R p) (X p (ΓM M H) hj) (toBase p (ΓM M H) hj) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j') ũ hsq'' w hwover ↥A gA hgA

  letI algRK : Algebra ↥(Algebra.adjoin (R p) ({ζ} : Set L)) (AlgebraicClosure ℚ) :=
    (ιA.comp (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L)).toAlgebra
  have hgK : (ιA.comp (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L)).comp (algebraMap (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L))) =
      algebraMap (R p) (AlgebraicClosure ℚ) := by
    refine RingHom.ext fun r0 => ?_
    change ιA (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L (algebraMap (R p) _ r0)) = _
    rw [← IsScalarTower.algebraMap_apply, hιA]
  obtain ⟨-, vK, -, hvKu, hvKt, hsqK, -⟩ :=
    H9_baseChange_modelAut (R p) (X p (ΓM M H) hj) (toBase p (ΓM M H) hj) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j') ũ hsq'' w hwover
      (AlgebraicClosure ℚ) (ιA.comp (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L)) hgK

  have hi : A.subtype.comp gA = ιA.comp (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L) := by
    refine RingHom.ext fun r => ?_
    rfl
  obtain ⟨hkAv, hconv⟩ :=
    K_genericPoint_square_of_baseChange_modelAut (R p) (X p (ΓM M H) hj) (toBase p (ΓM M H) hj) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j') ũ hsq'' w
      ↥A gA vA hvAu hvAt φ hφv (AlgebraicClosure ℚ) (ιA.comp (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L)) vK hvKu hvKt
      A.subtype hi kA hkA₁ hkA₂
  refine ⟨φ, hφover, ?_⟩
  intro y y' hyy'

  haveI : Nonempty (Scheme.Opens.toScheme
      ((((𝔛.eeta ≫ hsqK.isoPullback.hom) ≫ pullback.fst _ _) ⁻¹ᵁ
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j') ''ᵁ ⊤)))) := by
    have hopen : (((𝔛.eeta ≫ hsqK.isoPullback.hom) ≫ pullback.fst _ _) ⁻¹ᵁ
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') ''ᵁ ⊤)) =
        (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
          ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) := by
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← hvKu, hũdef]
      simp only [Scheme.Hom.comp_preimage]
      congr 2
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
      change _ = ι2.hom ⁻¹ᵁ (u ⁻¹ᵁ AlgebraicCurve.TwoChartIntegralModel.chartFinOpen (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
      rw [hpreFin, hι2pre]
      rfl
    rw [hopen]
    exact 𝔛.Meta_chart_nonempty
  have hιAR : ∀ r : ↥(Algebra.adjoin (R p) ({ζ} : Set L)), algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) (AlgebraicClosure ℚ) r =
      ιA ((((algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) r :
        ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L).coeff 0)) := by
    intro r
    change ιA (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L r) =
      ιA ((algebraMap L (LaurentSeries L) (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L r)).coeff 0)
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_same]
  have hspan : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'),
      b ∈ Subring.closure (Set.range (c2.comp cR) ∪
        Set.range (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j'))) := by

    haveI : Algebra.IsIntegral (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) := Algebra.IsIntegral.of_finite (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L))
    have hFinEq := hchart {jAt (ΓM M H) hj} (Or.inl rfl)
    rw [Set.image_singleton, hj4] at hFinEq
    intro b

    have hb0 : (b : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) ∈ TwoChartIntegralModel.chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'} :=
      (Ws6.W5.mem_chartAlg_iff_of_isIntegral (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'} _).mp b.2
    have hb1 : (b : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) ∈ Submodule.span ↥(Algebra.adjoin (R p) ({ζ} : Set L))
        (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) '' (TwoChartIntegralModel.chartAlg (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) {jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))) := by
      have : (b : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) ∈ Subalgebra.toSubmodule (TwoChartIntegralModel.chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'}) := hb0
      rw [hFinEq] at this
      exact this

    suffices h : ∀ (x : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))), x ∈ Submodule.span ↥(Algebra.adjoin (R p) ({ζ} : Set L))
        (algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) '' (TwoChartIntegralModel.chartAlg (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) {jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))) →
        ∀ hx : x ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j',
          (⟨x, hx⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')) ∈
            Subring.closure (Set.range (c2.comp cR) ∪
              Set.range (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j'))) by
      exact h b hb1 b.2
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro hx'
      obtain ⟨a, ha, rfl⟩ := hx
      refine Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, Subtype.ext ?_⟩)
      rw [RingHom.comp_apply, hc2, hcR]
    | zero => intro hx'; exact Subring.zero_mem _
    | add x y hxm hym hx hy =>
      intro hx'
      have hxm' : x ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' := by
        refine (Ws6.W5.mem_chartAlg_iff_of_isIntegral (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'} _).mpr ?_
        have : x ∈ Subalgebra.toSubmodule (TwoChartIntegralModel.chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'}) := by rw [hFinEq]; exact hxm
        exact this
      have hym' : y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' := by
        refine (Ws6.W5.mem_chartAlg_iff_of_isIntegral (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'} _).mpr ?_
        have : y ∈ Subalgebra.toSubmodule (TwoChartIntegralModel.chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'}) := by rw [hFinEq]; exact hym
        exact this
      exact Subring.add_mem _ (hx hxm') (hy hym')
    | smul r x hxm hx =>
      intro hx'
      have hxm' : x ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j' := by
        refine (Ws6.W5.mem_chartAlg_iff_of_isIntegral (R p) ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'} _).mpr ?_
        have : x ∈ Subalgebra.toSubmodule (TwoChartIntegralModel.chartAlg (R p) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) {j'}) := by rw [hFinEq]; exact hxm
        exact this
      have heq : (⟨r • x, hx'⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j')) =
          algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j') r * ⟨x, hxm'⟩ :=
        Subtype.ext (by change r • x = _; rw [Algebra.smul_def]; rfl)
      rw [heq]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inr ⟨r, rfl⟩)) (hx hxm')

  have hR''const : ∀ r : ↥(Algebra.adjoin (R p) ({ζ} : Set L)),
      coeffMap ιA (((algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) r :
        ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
        (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) (AlgebraicClosure ℚ) r) := by
    intro r
    change coeffMap ιA (algebraMap L (LaurentSeries L) (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L r)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ιA (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) L r))
    rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
  have pin := W5H10.readingPin p M H hpM hj 𝔛 L ιA ↥(Algebra.adjoin (R p) ({ζ} : Set L)) j' ũ hsq''.w (c2.comp cR)
    (fun a => by rw [RingHom.comp_apply, hc2, hcR]; rfl) hũchart
    (algebraMap ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _) (fun r => rfl)
    (AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase _ _ _) hspan vK hvKu hsqK hιAR hR''const

  have hread : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'),
      θ (W5H10.ι'' M H L ιA ↥(Algebra.adjoin (R p) ({ζ} : Set L)) j' b) =
        W5H10.ι'' M H L ιA ↥(Algebra.adjoin (R p) ({ζ} : Set L)) j' (θc b) := by
    intro b
    apply Subtype.ext
    change ((θ _ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap ιA (((θc b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j')) :
        ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L)
    rw [hθc b]
    exact hθσ _ _ rfl
  have hint := Ws6.PlacePin.isIntegral_toAlgHom_of_algEquiv θ
  have hfinA := Ws6.PlacePin.finiteAlong_toAlgHom_of_algEquiv θ
  have hwchart' : AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j' ≫ w.hom =
      Spec.map (CommRingCat.ofHom (θc : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j') →ₐ[↥(Algebra.adjoin (R p) ({ζ} : Set L))]
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j')).toRingHom) ≫
      AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(Algebra.adjoin (R p) ({ζ} : Set L)) _ j' := hwchart
  have he : (𝔛.eeta ≫ hsqK.isoPullback.hom) ≫ pullback.snd _ _ = 𝔛.Meta.toBase := by
    rw [Category.assoc, IsPullback.isoPullback_hom_snd]; exact 𝔛.heeta

  have hyx : y.1 ≫ (𝔛.eeta ≫ hsqK.isoPullback.hom) ≫ pullback.fst _ _ =
      y'.1 ≫ (𝔛.eeta ≫ hsqK.isoPullback.hom) ≫ pullback.fst _ _ ≫ w.hom := by
    have h2 := hconv (y.1 ≫ 𝔛.eeta) (y'.1 ≫ 𝔛.eeta) (by simpa only [Category.assoc] using hyy')
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc] at h2 ⊢
    exact h2
  have h1 := AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin
    ↥(Algebra.adjoin (R p) ({ζ} : Set L)) (AlgebraicClosure ℚ) ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'
    ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) j'
    (W5H10.ι'' M H L ιA ↥(Algebra.adjoin (R p) ({ζ} : Set L)) j') (W5H10.ι'' M H L ιA ↥(Algebra.adjoin (R p) ({ζ} : Set L)) j')
    𝔛.Meta (𝔛.eeta ≫ hsqK.isoPullback.hom) he inferInstance pin 𝔛.Meta (𝔛.eeta ≫ hsqK.isoPullback.hom) he inferInstance pin
    w.hom hwover _ hwchart' θ.toAlgHom hread hint hfinA y' y hyx
  exact Ws6.PlacePin.pointEquivPlace_eq_ofAlgAut_smul_of_eq_restrictAlong 𝔛.Meta θ hint y y' h1

end S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_iso_pullback_toBase_specMap_atkinLehner_complement_placePin (solution)
