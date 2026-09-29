-- Prove2me | solution 1 for NumberField.finite_and_ncard_places_not_mem_range_norm_add_ne_one_of_forall_mem_zpowers_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5a188713-932e-5729-94d1-298580b63cb1

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_ne_bot_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
import Theorems.Thm_NumberField_PlaceDecomp_adicCompletionSemialgHom_norm_eq_finprod_smul
import Theorems.Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
import Theorems.Thm_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Theorems.Thm_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace
import Theorems.Thm_NumberField_finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_finite_and_ncard_places_not_mem_range_norm_add_ne_one_of_forall_mem_zpowers_of_prime
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply"

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

namespace K57N2P

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped TensorProduct TensorProduct.RightActions NumberField.PlaceDecomp IsMulCommutative

theorem isMulCommutative_of_gen {G : Type*} [Group G] (σ : G) (hgen : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    IsMulCommutative G := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen b)
  rw [← zpow_add, ← zpow_add, add_comm]

section Local

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

def IsLocNorm (c : Kv) : Prop :=
  c ∈ Set.range (fun x : (L ⊗[K] Kv)ˣ => Algebra.norm Kv (x : L ⊗[K] Kv))

theorem nonempty_extension : Nonempty (v.Extension (𝓞 L)) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsub : Subsingleton (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) := inferInstance
  have : Subsingleton (L ⊗[K] Kv) :=
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toEquiv.subsingleton
  exact not_subsingleton (L ⊗[K] Kv) this

theorem isLocNorm_of_norm_eq (w₀ : v.Extension (𝓞 L)) (b : (w₀.1.adicCompletion L)ˣ) (c : Kv)
    (h : Algebra.norm Kv (b : w₀.1.adicCompletion L) = c) : IsLocNorm K L v c := by
  classical
  obtain ⟨hprod, -, -⟩ :=
    HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm K L v
  set e := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with hedef
  refine ⟨⟨e.symm (Pi.mulSingle w₀ (b : w₀.1.adicCompletion L)),
      e.symm (Pi.mulSingle w₀ ((b⁻¹ : (w₀.1.adicCompletion L)ˣ) : w₀.1.adicCompletion L)), ?_, ?_⟩, ?_⟩
  · rw [← map_mul, ← Pi.mulSingle_mul, Units.mul_inv, Pi.mulSingle_one, map_one]
  · rw [← map_mul, ← Pi.mulSingle_mul, Units.inv_mul, Pi.mulSingle_one, map_one]
  · show Algebra.norm Kv (e.symm (Pi.mulSingle w₀ (b : w₀.1.adicCompletion L))) = c
    rw [hprod, AlgEquiv.apply_symm_apply,
      finprod_eq_single _ w₀ (fun w hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one]),
      Pi.mulSingle_eq_same, h]

theorem exists_units_norm_eq_prod (z : (L ⊗[K] Kv)ˣ) :
    ∃ b : Π w : v.Extension (𝓞 L), (w.1.adicCompletion L)ˣ,
      ∀ [Fintype (v.Extension (𝓞 L))],
        Algebra.norm Kv (z : L ⊗[K] Kv) = ∏ w, Algebra.norm Kv (b w : w.1.adicCompletion L) := by
  classical
  obtain ⟨hprod, -, -⟩ :=
    HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm K L v
  set e := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with hedef
  have hz : IsUnit (e (z : L ⊗[K] Kv)) := z.isUnit.map e
  refine ⟨fun w => ((Pi.isUnit_iff.mp hz) w).unit, ?_⟩
  intro _
  rw [hprod, finprod_eq_prod_of_fintype]
  rfl

end Local

section Ideles

variable (K : Type) [Field K] [NumberField K]

def iotaFin (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)).comp (NumberField.AdelicLevel.localUnit (𝓞 K) K v)

def infIncl : InfiniteAdeleRing K →* AdeleRing (𝓞 K) K where
  toFun x := (x, (1 : FiniteAdeleRing (𝓞 K) K))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

def iotaInf : (InfiniteAdeleRing K)ˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (infIncl K)

theorem infPart_iotaFin (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) :
    infPart (iotaFin K v c) = 1 := Units.ext rfl

theorem finPart_iotaFin_self (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) :
    finPart v (iotaFin K v c) = c :=
  Units.ext (NumberField.AdelicLevel.localUnit_apply_self (𝓞 K) K v c)

theorem finPart_iotaFin_of_ne (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) : finPart w (iotaFin K v c) = 1 :=
  Units.ext (NumberField.AdelicLevel.localUnit_apply_of_ne (𝓞 K) K v c hw)

theorem iotaFin_mem_idelesTrivialOn (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) :
    iotaFin K v c ∈ idelesTrivialOn (𝓞 K) K ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) :=
  ⟨infPart_iotaFin K v c, fun _ hw => finPart_iotaFin_of_ne K v c (fun h => hw (h ▸ rfl))⟩

theorem infPart_iotaInf (x : (InfiniteAdeleRing K)ˣ) : infPart (iotaInf K x) = x := Units.ext rfl

theorem finPart_iotaInf (v : HeightOneSpectrum (𝓞 K)) (x : (InfiniteAdeleRing K)ˣ) :
    finPart v (iotaInf K x) = 1 := Units.ext rfl

def prin (a : Kˣ) : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a

theorem prin_mem_principalIdeles (a : Kˣ) : prin K a ∈ principalIdeles (𝓞 K) K := ⟨a, rfl⟩

def locFin (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a

def locInf (a : Kˣ) : (InfiniteAdeleRing K)ˣ :=
  Units.map (algebraMap K (InfiniteAdeleRing K) : K →* InfiniteAdeleRing K) a

theorem finPart_prin (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : finPart v (prin K a) = locFin K v a :=
  Units.ext rfl

theorem infPart_prin (a : Kˣ) : infPart (prin K a) = locInf K a := Units.ext rfl

theorem idele_ext {x y : (AdeleRing (𝓞 K) K)ˣ} (hinf : infPart x = infPart y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), finPart v x = finPart v y) : x = y := by
  apply Units.ext
  refine Prod.ext (congrArg Units.val hinf) (FiniteAdeleRing.ext K fun v => ?_)
  exact congrArg Units.val (hfin v)

end Ideles

section Artin

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
  (𝔣 : Ideal (𝓞 K)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L (Module.finrank K L) 𝔣)
  (r : (AdeleRing (𝓞 K) K)ˣ →* (L ≃ₐ[K] L))
  (hr₁ : principalIdeles (𝓞 K) K ≤ r.ker)
  (hr₂ : r.ker = principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range)
  (hr₃ : Function.Surjective r)
  (hr₄ : ∀ u : (AdeleRing (𝓞 K) K)ˣ, IsAdjuster K 𝔣 u 1 →
    r u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob K L v ^ placeOrd K (projFin K u) v)

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in

theorem coe_finprod_smul (w : HeightOneSpectrum (𝓞 L))
    (b : (w.adicCompletion L)ˣ) :
    (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp K L w), σ • b : (w.adicCompletion L)ˣ) : (w.adicCompletion L)ˣ) :
        w.adicCompletion L) =
      ∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp K L w), σ • (b : w.adicCompletion L) := by
  exact (Units.coeHom (w.adicCompletion L)).map_finprod (f := fun σ : ↥(NumberField.PlaceDecomp.decomp K L w) => σ • b) (Set.toFinite _)

include hadm hr₁ hr₂ hr₃ hr₄ in
theorem r_iotaFin_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) :
    r (iotaFin K v c) = 1 ↔ IsLocNorm K L v (c : v.adicCompletion K) := by
  classical
  obtain ⟨w₀⟩ := nonempty_extension K L v
  constructor
  · intro h1
    obtain ⟨b, hb⟩ := (M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq K L 𝔣 hadm r
      hr₁ hr₂ hr₃ hr₄ v c (iotaFin K v c) (iotaFin_mem_idelesTrivialOn K v c) (finPart_iotaFin_self K v c)
      w₀.1 w₀.2).mp h1
    have hN := NumberField.PlaceDecomp.adicCompletionSemialgHom_norm_eq_finprod_smul K L v w₀
      (b : w₀.1.adicCompletion L)
    rw [← coe_finprod_smul K L w₀.1 b, hb] at hN

    have hinj : Function.Injective
        (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w₀ :
          v.adicCompletion K →+* w₀.1.adicCompletion L) := RingHom.injective _
    have hNb : Algebra.norm (v.adicCompletion K) (b : w₀.1.adicCompletion L) = (c : v.adicCompletion K) :=
      hinj hN
    exact isLocNorm_of_norm_eq K L v w₀ b _ hNb
  · rintro ⟨z, hz⟩
    have hz' : Algebra.norm (v.adicCompletion K) (z : L ⊗[K] v.adicCompletion K) = (c : v.adicCompletion K) := hz
    haveI := IsDedekindDomain.HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
    letI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
    obtain ⟨b, hb⟩ := exists_units_norm_eq_prod K L v z
    have hc : c = ∏ w : v.Extension (𝓞 L),
        Units.map (Algebra.norm (v.adicCompletion K) : w.1.adicCompletion L →* v.adicCompletion K) (b w) := by
      apply Units.ext
      rw [← hz', hb, Units.coe_prod]
      rfl
    rw [hc, map_prod]
    refine Finset.prod_induction _ (fun g => r g = 1) (fun a b ha hb => show r (a * b) = 1 by rw [map_mul, show r a = 1 from ha, show r b = 1 from hb, one_mul])
      (map_one r) (fun w _ => ?_)
    show r (iotaFin K v _) = 1
    refine (M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq K L 𝔣 hadm r
      hr₁ hr₂ hr₃ hr₄ v _ (iotaFin K v _) (iotaFin_mem_idelesTrivialOn K v _) (finPart_iotaFin_self K v _)
      w.1 w.2).mpr ⟨b w, ?_⟩
    rw [coe_finprod_smul K L w.1 (b w), Units.coe_map]
    exact (NumberField.PlaceDecomp.adicCompletionSemialgHom_norm_eq_finprod_smul K L v w (b w : w.1.adicCompletion L)).symm

end Artin

section Arch

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def commInf : (L ⊗[K] InfiniteAdeleRing K) ≃ₐ[InfiniteAdeleRing K] (InfiniteAdeleRing K ⊗[K] L) :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)).toRingEquiv) (fun x => by
    show Algebra.TensorProduct.comm K L (InfiniteAdeleRing K) (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) x) =
      x ⊗ₜ[K] (1 : L)
    rw [show algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) x = (1 : L) ⊗ₜ[K] x from rfl]
    exact Algebra.TensorProduct.comm_tmul (R := K) (1 : L) x)

theorem norm_archIdent (t : L ⊗[K] InfiniteAdeleRing K) :
    (letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra;
      Algebra.norm (InfiniteAdeleRing K) (AutomorphicForm.archIdent K L t)) =
    Algebra.norm (InfiniteAdeleRing K) t := by
  letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).adeleAlgebra
  have h : AutomorphicForm.archIdent K L t =
      (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeAlgEquiv (commInf K L t) := rfl
  rw [h, Algebra.norm_eq_of_algEquiv, Algebra.norm_eq_of_algEquiv]

theorem iotaInf_mem_range_idelicNorm (a : (InfiniteAdeleRing K)ˣ)
    (h : (a : InfiniteAdeleRing K) ∈ Set.range
      (fun t : (L ⊗[K] InfiniteAdeleRing K)ˣ => Algebra.norm (InfiniteAdeleRing K) (t : L ⊗[K] InfiniteAdeleRing K))) :
    iotaInf K a ∈ ((genuineBaseChange K L).idelicNorm).range := by
  obtain ⟨t, ht⟩ := h
  have ht' : Algebra.norm (InfiniteAdeleRing K) (t : L ⊗[K] InfiniteAdeleRing K) = (a : InfiniteAdeleRing K) := ht
  set tL : (InfiniteAdeleRing L)ˣ := Units.map (AutomorphicForm.archIdent K L : _ →* _) t with htL
  refine ⟨MulEquiv.prodUnits.symm (tL, 1), ?_⟩
  apply Units.ext
  obtain ⟨h1, h2⟩ := M4aHerbrand.genuineAdelicNorm_componentwise K L
    ((tL : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L))
  show (letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra; Algebra.norm (AdeleRing (𝓞 K) K) (S := AdeleRing (𝓞 L) L)
      ((tL : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L))) =
      ((((a : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K))) : AdeleRing (𝓞 K) K)
  refine Prod.ext ?_ ?_
  · rw [h1]
    show (letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra;
      Algebra.norm (InfiniteAdeleRing K) (AutomorphicForm.archIdent K L (t : L ⊗[K] InfiniteAdeleRing K))) = (a : InfiniteAdeleRing K)
    rw [norm_archIdent, ht']
  · apply FiniteAdeleRing.ext K
    intro v
    letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    rw [h2 v]
    simp [HeckeCharacter.fad_one_apply]

end Arch

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
  (𝔣 : Ideal (𝓞 K)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L (Module.finrank K L) 𝔣)
  (r : (AdeleRing (𝓞 K) K)ˣ →* (L ≃ₐ[K] L))
  (hr₁ : principalIdeles (𝓞 K) K ≤ r.ker)
  (hr₂ : r.ker = principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range)
  (hr₃ : Function.Surjective r)
  (hr₄ : ∀ u : (AdeleRing (𝓞 K) K)ˣ, IsAdjuster K 𝔣 u 1 →
    r u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob K L v ^ placeOrd K (projFin K u) v)

def IsLocNormInf (w : InfinitePlace K) (c : w.Completion) : Prop :=
  c ∈ Set.range (fun x : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (x : L ⊗[K] w.Completion))

omit [IsGalois K L] in
include hr₂ in
theorem r_eq_one_of_mem_range {x : (AdeleRing (𝓞 K) K)ˣ}
    (hx : x ∈ ((genuineBaseChange K L).idelicNorm).range) : r x = 1 := by
  have : x ∈ r.ker := by rw [hr₂]; exact Subgroup.mem_sup_right hx
  exact this

include hadm hr₂ in

theorem r_iotaFin_eq_one_of_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣)
    (c : (v.adicCompletion K)ˣ) (hc : Valued.v (c : v.adicCompletion K) = 1) :
    r (iotaFin K v c) = 1 := by
  classical
  apply r_eq_one_of_mem_range K L r hr₂
  apply LanglandsTunnell.P2.Artin.unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree K L 𝔣 hadm
  refine ⟨fun w => ?_, fun w hw => ?_, fun τ => HeckeCharacter.archSign_of_fst_eq_one K τ rfl⟩
  · change Valued.v ((finPart w (iotaFin K v c) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1
    by_cases h : w = v
    · subst h; rw [finPart_iotaFin_self]; exact hc
    · rw [finPart_iotaFin_of_ne K v c h, Units.val_one, map_one]
  · change Valued.v (((finPart w (iotaFin K v c) : (w.adicCompletion K)ˣ) : w.adicCompletion K) - 1) ≤ _
    have h : w ≠ v := fun h => hv (h ▸ hw)
    rw [finPart_iotaFin_of_ne K v c h, Units.val_one, sub_self, map_zero]
    exact zero_le'

include hadm hr₁ hr₂ hr₃ hr₄ in

theorem isLocNorm_of_forall_ne (a : Kˣ) (v₀ : HeightOneSpectrum (𝓞 K))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ v₀ → IsLocNorm K L v (algebraMap K (v.adicCompletion K) (a : K)))
    (hinf : ∀ w : InfinitePlace K, IsLocNormInf K L w (algebraMap K w.Completion (a : K))) :
    IsLocNorm K L v₀ (algebraMap K (v₀.adicCompletion K) (a : K)) := by
  classical

  have hT₁ : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔣}.Finite := Ideal.finite_factors hadm.1
  have hT₂ : {v : HeightOneSpectrum (𝓞 K) | Valued.v ((locFin K v a : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 1}.Finite := by
    refine (HeckeCharacter.finite_support_placeOrd K (projFin K (prin K a))).subset fun v hv => ?_
    rw [Function.mem_support, ne_eq, HeckeCharacter.placeOrd_eq_zero_iff]
    exact hv
  set S : Finset (HeightOneSpectrum (𝓞 K)) := (hT₁.union hT₂).toFinset ∪ {v₀} with hS
  have hv₀S : v₀ ∈ S := by simp [hS]
  have hS𝔣 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → v ∈ S := fun v hv => by simp [hS, hv]
  have hSunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      Valued.v ((locFin K v a : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    intro v hv
    by_contra h
    exact hv (by simp [hS, h])

  set u : (AdeleRing (𝓞 K) K)ˣ :=
    prin K a * (iotaInf K (locInf K a))⁻¹ * (∏ v ∈ S, iotaFin K v (locFin K v a))⁻¹ with hu
  have hterm : ∀ v s : HeightOneSpectrum (𝓞 K),
      finPart v (iotaFin K s (locFin K s a)) = if v = s then locFin K v a else 1 := by
    intro v s
    by_cases h : v = s
    · subst h; rw [if_pos rfl, finPart_iotaFin_self]
    · rw [if_neg h, finPart_iotaFin_of_ne K s _ h]
  have hfinPart : ∀ v : HeightOneSpectrum (𝓞 K), finPart v u = if v ∈ S then 1 else locFin K v a := by
    intro v
    rw [hu, map_mul, map_mul, map_inv, map_inv, map_prod, finPart_prin, finPart_iotaInf, inv_one, mul_one]
    simp_rw [hterm]
    rw [Finset.prod_ite_eq]
    split_ifs <;> simp
  have hinfPart : infPart u = 1 := by
    rw [hu, map_mul, map_mul, map_inv, map_inv, map_prod, infPart_prin, infPart_iotaInf]
    simp [infPart_iotaFin]

  have hu_unit : u ∈ unitIdeles K 𝔣 := by
    refine ⟨fun v => ?_, fun v hv => ?_, fun τ => ?_⟩
    · change Valued.v ((finPart v u : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1
      rw [hfinPart]
      split_ifs with h
      · rw [Units.val_one, map_one]
      · exact hSunit v h
    · change Valued.v (((finPart v u : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) ≤ _
      rw [hfinPart, if_pos (hS𝔣 v hv), Units.val_one, sub_self, map_zero]
      exact zero_le'
    · exact HeckeCharacter.archSign_of_fst_eq_one K τ (congrArg Units.val hinfPart)
  have hru : r u = 1 :=
    r_eq_one_of_mem_range K L r hr₂
      (LanglandsTunnell.P2.Artin.unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree K L 𝔣 hadm hu_unit)
  have hrP : r (prin K a) = 1 := hr₁ (prin_mem_principalIdeles K a)
  have hrinf : r (iotaInf K (locInf K a)) = 1 := by
    apply r_eq_one_of_mem_range K L r hr₂
    apply iotaInf_mem_range_idelicNorm K L
    exact (NumberField.InfiniteAdeleRing.mem_range_norm_tensorProduct_iff_forall_infinitePlace K L (locInf K a)).mpr
      (fun w => hinf w)
  have hrS : ∀ s ∈ S.erase v₀, r (iotaFin K s (locFin K s a)) = 1 := fun s hs =>
    (r_iotaFin_eq_one_iff K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ s (locFin K s a)).mpr (hfin s (Finset.ne_of_mem_erase hs))
  have hprod : r (∏ v ∈ S, iotaFin K v (locFin K v a)) = r (iotaFin K v₀ (locFin K v₀ a)) := by
    rw [← Finset.mul_prod_erase S (fun v => iotaFin K v (locFin K v a)) hv₀S, map_mul]
    have : r (∏ v ∈ S.erase v₀, iotaFin K v (locFin K v a)) = 1 :=
      Finset.prod_induction _ (fun g => r g = 1)
        (fun x y hx hy => show r (x * y) = 1 by rw [map_mul, show r x = 1 from hx, show r y = 1 from hy, one_mul])
        (map_one r) (fun s hs => hrS s hs)
    rw [this, mul_one]
  have key : r (iotaFin K v₀ (locFin K v₀ a)) = 1 := by
    have h : r u = r (prin K a) * (r (iotaInf K (locInf K a)))⁻¹ * (r (∏ v ∈ S, iotaFin K v (locFin K v a)))⁻¹ := by
      rw [hu, map_mul, map_mul, map_inv, map_inv]
    rw [hru, hrP, hrinf, hprod, inv_one, mul_one, one_mul] at h
    exact inv_eq_one.mp h.symm
  exact (r_iotaFin_eq_one_iff K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v₀ (locFin K v₀ a)).mp key

end Main

section Finite

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
  (𝔣 : Ideal (𝓞 K)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L (Module.finrank K L) 𝔣)
  (r : (AdeleRing (𝓞 K) K)ˣ →* (L ≃ₐ[K] L))
  (hr₁ : principalIdeles (𝓞 K) K ≤ r.ker)
  (hr₂ : r.ker = principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range)
  (hr₃ : Function.Surjective r)
  (hr₄ : ∀ u : (AdeleRing (𝓞 K) K)ˣ, IsAdjuster K 𝔣 u 1 →
    r u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob K L v ^ placeOrd K (projFin K u) v)

include L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ in

theorem finite_setOf_not_isLocNorm (a : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | ¬ IsLocNorm K L v (algebraMap K (v.adicCompletion K) (a : K))}.Finite := by
  classical
  have hT₁ : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔣}.Finite := Ideal.finite_factors hadm.1
  have hT₂ : {v : HeightOneSpectrum (𝓞 K) |
      Valued.v ((locFin K v a : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 1}.Finite := by
    refine (HeckeCharacter.finite_support_placeOrd K (projFin K (prin K a))).subset fun v hv => ?_
    rw [Function.mem_support, ne_eq, HeckeCharacter.placeOrd_eq_zero_iff]
    exact hv
  refine (hT₁.union hT₂).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
  exact hv ((r_iotaFin_eq_one_iff K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v (locFin K v a)).mp
    (r_iotaFin_eq_one_of_valued_eq_one K L 𝔣 hadm r hr₂ v h.1 (locFin K v a) h.2))

end Finite

section OddArch

open NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] [Algebra K L] in

theorem exists_pow_eq_of_odd (w : InfinitePlace K) {n : ℕ} (hn : Odd n) (c : w.Completion) :
    ∃ d : w.Completion, d ^ n = c := by
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ^ n = e c := by
      rcases le_or_gt 0 (e c) with h | h
      · exact ⟨(e c) ^ ((n : ℝ)⁻¹), Real.rpow_inv_natCast_pow h hn.pos.ne'⟩
      · refine ⟨-((-(e c)) ^ ((n : ℝ)⁻¹)), ?_⟩
        rw [hn.neg_pow, Real.rpow_inv_natCast_pow (neg_pos.mpr h).le hn.pos.ne', neg_neg]
    exact ⟨e.symm t, e.injective (by rw [map_pow, e.apply_symm_apply, ht])⟩
  · have hcx : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hcx
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e c) hn.pos
    exact ⟨e.symm t, e.injective (by rw [map_pow, e.apply_symm_apply, ht])⟩

omit [NumberField L] in

theorem isLocNormInf_of_odd [FiniteDimensional K L] (hodd : Odd (Module.finrank K L)) (w : InfinitePlace K)
    (c : w.Completion) (hc : c ≠ 0) :
    c ∈ Set.range (fun x : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (x : L ⊗[K] w.Completion)) := by
  obtain ⟨d, hd⟩ := exists_pow_eq_of_odd K w hodd c
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hc
    rw [← hd, zero_pow hodd.pos.ne']
  refine ⟨Units.map (algebraMap w.Completion (L ⊗[K] w.Completion) : w.Completion →* L ⊗[K] w.Completion)
    (Units.mk0 d hd0), ?_⟩
  show Algebra.norm w.Completion (algebraMap w.Completion (L ⊗[K] w.Completion) d) = c
  rw [Algebra.norm_algebraMap_of_basis
    (TensorProduct.RightActions.Algebra.TensorProduct.basis (w.Completion) (Module.finBasis K L)),
    Fintype.card_fin, hd]

end OddArch

end K57N2P

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

open K57N2P LanglandsTunnell.P2.Artin in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (a : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | algebraMap K (v.adicCompletion K) (a : K) ∉
        Set.range (fun x : (L ⊗[K] v.adicCompletion K)ˣ =>
          Algebra.norm (v.adicCompletion K) (x : L ⊗[K] v.adicCompletion K))}.Finite ∧
    {v : HeightOneSpectrum (𝓞 K) | algebraMap K (v.adicCompletion K) (a : K) ∉
        Set.range (fun x : (L ⊗[K] v.adicCompletion K)ˣ =>
          Algebra.norm (v.adicCompletion K) (x : L ⊗[K] v.adicCompletion K))}.ncard +
      {w : InfinitePlace K | algebraMap K w.Completion (a : K) ∉
        Set.range (fun x : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (x : L ⊗[K] w.Completion))}.ncard ≠ 1 := by
  classical
  rcases hprime.eq_two_or_odd' with h2 | hodd
  ·
    obtain ⟨hF, hE⟩ := NumberField.finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two K L h2 a
    exact ⟨hF, fun h1 => Nat.not_even_one (h1 ▸ hE)⟩
  ·
    haveI : IsMulCommutative (L ≃ₐ[K] L) := K57N2P.isMulCommutative_of_gen σ hgen
    have ha0 : ∀ w : InfinitePlace K, algebraMap K w.Completion (a : K) ≠ 0 := fun w =>
      (map_ne_zero_iff _ (algebraMap K w.Completion).injective).mpr a.ne_zero
    obtain ⟨𝔯, h𝔯, H𝔯⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd K L
    obtain ⟨𝔣, -, -, hadm⟩ :=
      LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd K L 𝔯 h𝔯
        (fun v hv => H𝔯 v (primeAbove K L v) inferInstance (under_primeAbove K L v) hv) (Module.finrank K L)
    obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ :=
      NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
        K L 𝔣 hadm
    have hFfin := finite_setOf_not_isLocNorm K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ a
    have hI : {w : InfinitePlace K | algebraMap K w.Completion (a : K) ∉
        Set.range (fun x : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (x : L ⊗[K] w.Completion))} = ∅ :=
      Set.eq_empty_of_forall_notMem fun w hw => hw (isLocNormInf_of_odd K L hodd w _ (ha0 w))
    refine ⟨hFfin, fun h1 => ?_⟩
    rw [hI, Set.ncard_empty, add_zero] at h1
    obtain ⟨v₀, hFv⟩ := Set.ncard_eq_one.mp h1
    have hv₀ : v₀ ∈ ({v₀} : Set (HeightOneSpectrum (𝓞 K))) := Set.mem_singleton v₀
    rw [← hFv] at hv₀
    apply hv₀
    refine isLocNorm_of_forall_ne K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ a v₀ (fun v hv => ?_)
      (fun w => isLocNormInf_of_odd K L hodd w _ (ha0 w))
    by_contra h
    have : v ∈ ({v₀} : Set (HeightOneSpectrum (𝓞 K))) := by rw [← hFv]; exact h
    exact hv this

end

end S_NumberField_finite_and_ncard_places_not_mem_range_norm_add_ne_one_of_forall_mem_zpowers_of_prime
end P2MW
export P2MW.S_NumberField_finite_and_ncard_places_not_mem_range_norm_add_ne_one_of_forall_mem_zpowers_of_prime (solution)
