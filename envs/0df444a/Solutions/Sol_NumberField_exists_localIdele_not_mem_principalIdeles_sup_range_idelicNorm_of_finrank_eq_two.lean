-- Prove2me | solution 1 for NumberField.exists_localIdele_not_mem_principalIdeles_sup_range_idelicNorm_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f30651d2-b650-5330-b878-e006edc529c9

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ArithFrobResidue
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq
import Theorems.Thm_NumberField_exists_artinSymbol_principalUnit_ne_one_of_not_isReal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_localIdele_not_mem_principalIdeles_sup_range_idelicNorm_of_finrank_eq_two
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite"
p2m_attr_erase "instance" "LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply AutomorphicForm.CuspidalityNotion.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain NumberField.AdelicLevel NumberField.AdelicVolume M4aHerbrand M4aHerbrand.GenuineDescent LanglandsTunnell.P2.Artin HeckeCharacter Deep.NTSupply NumberField.NormIndex

open scoped TensorProduct TensorProduct.RightActions IsMulCommutative nonZeroDivisors

noncomputable section

namespace QuadLocalIdele

section NormBaseChange

variable {K : Type*} [Field K] {L : Type*} [Ring L] [Algebra K L]
variable {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

theorem basis_repr_map {ι : Type*} [Fintype ι] (b : Module.Basis ι K L) (φ : A →ₐ[K] B) (T : A ⊗[K] L) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map φ (AlgHom.id K L) T) i =
      φ ((Algebra.TensorProduct.basis A b).repr T i) := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

theorem leftMulMatrix_map {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) (φ : A →ₐ[K] B)
    (T : A ⊗[K] L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis B b) (Algebra.TensorProduct.map φ (AlgHom.id K L) T) =
      (φ : A →+* B).mapMatrix (Algebra.leftMulMatrix (Algebra.TensorProduct.basis A b) T) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply]
  have : Algebra.TensorProduct.map φ (AlgHom.id K L) T * (1 : B) ⊗ₜ[K] b j =
      Algebra.TensorProduct.map φ (AlgHom.id K L) (T * (1 : A) ⊗ₜ[K] b j) := by
    rw [map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [this, basis_repr_map]
  rfl

theorem map_norm_eq_norm_map [FiniteDimensional K L] (φ : A →ₐ[K] B) (T : A ⊗[K] L) :
    φ (Algebra.norm A T) = Algebra.norm B (Algebra.TensorProduct.map φ (AlgHom.id K L) T) := by
  classical
  let b := Module.finBasis K L
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis A b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis B b), leftMulMatrix_map]
  exact RingHom.map_det (φ : A →+* B) _

end NormBaseChange

section Eval

variable (K : Type) [Field K] [NumberField K]

def evF (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K where
  toRingHom := (finAdeleEval (𝓞 K) K v).comp (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  commutes' k := rfl

def evI (w : InfinitePlace K) : AdeleRing (𝓞 K) K →ₐ[K] w.Completion where
  toRingHom := (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  commutes' k := rfl

theorem evF_apply (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 K) K) : evF K v x = x.2 v := rfl

theorem evI_apply (w : InfinitePlace K) (x : AdeleRing (𝓞 K) K) : evI K w x = x.1 w := rfl

def finCompHom (v : HeightOneSpectrum (𝓞 K)) : (AdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (evF K v : AdeleRing (𝓞 K) K →* v.adicCompletion K)

def infCompHom (w : InfinitePlace K) : (AdeleRing (𝓞 K) K)ˣ →* (w.Completion)ˣ :=
  Units.map (evI K w : AdeleRing (𝓞 K) K →* w.Completion)

theorem val_finCompHom (v : HeightOneSpectrum (𝓞 K)) (t : (AdeleRing (𝓞 K) K)ˣ) :
    ((finCompHom K v t : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (t : AdeleRing (𝓞 K) K).2 v := rfl

theorem val_infCompHom (w : InfinitePlace K) (t : (AdeleRing (𝓞 K) K)ˣ) :
    ((infCompHom K w t : (w.Completion)ˣ) : w.Completion) = (t : AdeleRing (𝓞 K) K).1 w := rfl

abbrev principalIdele (a : Kˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a

theorem principalIdele_mem (a : Kˣ) : principalIdele K a ∈ principalIdeles (𝓞 K) K := ⟨a, rfl⟩

theorem finCompHom_principal (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    finCompHom K v (principalIdele K a) =
      Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a := by
  refine Units.ext ?_
  rw [val_finCompHom, Units.coe_map, Units.coe_map]
  show evF K v (algebraMap K (AdeleRing (𝓞 K) K) (a : K)) = _
  exact (evF K v).commutes (a : K)

theorem infCompHom_principal (w : InfinitePlace K) (a : Kˣ) :
    infCompHom K w (principalIdele K a) = Units.map (algebraMap K w.Completion : K →* w.Completion) a := by
  refine Units.ext ?_
  rw [val_infCompHom, Units.coe_map, Units.coe_map]
  show evI K w (algebraMap K (AdeleRing (𝓞 K) K) (a : K)) = _
  exact (evI K w).commutes (a : K)

abbrev localIdele (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)

theorem localIdele_snd_apply (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) (v' : HeightOneSpectrum (𝓞 K)) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v' =
      ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v' := rfl

theorem localIdele_fst (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem finCompHom_localIdele_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    finCompHom K v (localIdele K v t) = t := by
  refine Units.ext ?_
  rw [val_finCompHom]
  exact localUnit_apply_self (𝓞 K) K v t

theorem finCompHom_localIdele_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    {v' : HeightOneSpectrum (𝓞 K)} (h : v' ≠ v) : finCompHom K v' (localIdele K v t) = 1 := by
  refine Units.ext ?_
  rw [val_finCompHom, Units.val_one]
  exact localUnit_apply_of_ne (𝓞 K) K v t h

theorem infCompHom_localIdele (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) (w : InfinitePlace K) :
    infCompHom K w (localIdele K v t) = 1 := by
  refine Units.ext ?_
  rw [val_infCompHom, Units.val_one]
  rfl

open scoped Classical in
theorem infCompHom_archCentralUnit_self (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    infCompHom K w (archCentralUnit K w a) = a := by
  refine Units.ext ?_
  rw [val_infCompHom]
  exact archCentralUnit_fst_self w a

theorem infCompHom_archCentralUnit_of_ne (w : InfinitePlace K) (a : (w.Completion)ˣ) {w' : InfinitePlace K}
    (h : w' ≠ w) : infCompHom K w' (archCentralUnit K w a) = 1 := by
  refine Units.ext ?_
  rw [val_infCompHom, Units.val_one]
  exact archCentralUnit_fst_of_ne w a h

theorem finCompHom_archCentralUnit (w : InfinitePlace K) (a : (w.Completion)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finCompHom K v (archCentralUnit K w a) = 1 := by
  refine Units.ext ?_
  rw [val_finCompHom, Units.val_one]
  rfl

abbrev finDiag (a : Kˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K) : K →* FiniteAdeleRing (𝓞 K) K) a)

theorem finDiag_fst (a : Kˣ) : ((finDiag K a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem finDiag_snd_apply (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finDiag K a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = ((a : K) : v.adicCompletion K) := rfl

theorem finCompHom_finDiag (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finCompHom K v (finDiag K a) = finCompHom K v (principalIdele K a) :=
  Units.ext rfl

theorem infCompHom_finDiag (a : Kˣ) (w : InfinitePlace K) : infCompHom K w (finDiag K a) = 1 :=
  Units.ext rfl

end Eval

section Norms

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

abbrev TA : Type := AdeleRing (𝓞 K) K ⊗[K] L

def transport : (TA K L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  letI := (genuineBaseChange K L).β.toAlgebra
  Units.map ((genuineBaseChange K L).tensorEquiv : TA K L →* AdeleRing (𝓞 L) L)

def transportInv : (AdeleRing (𝓞 L) L)ˣ →* (TA K L)ˣ :=
  letI := (genuineBaseChange K L).β.toAlgebra
  Units.map ((genuineBaseChange K L).tensorEquiv.symm : AdeleRing (𝓞 L) L →* TA K L)

theorem transport_transportInv (b : (AdeleRing (𝓞 L) L)ˣ) : transport K L (transportInv K L b) = b := by
  letI := (genuineBaseChange K L).β.toAlgebra
  refine Units.ext ?_
  show (genuineBaseChange K L).tensorEquiv ((genuineBaseChange K L).tensorEquiv.symm (b : AdeleRing (𝓞 L) L)) = b
  exact AlgEquiv.apply_symm_apply _ _

theorem val_idelicNorm_transport (T : (TA K L)ˣ) :
    (((genuineBaseChange K L).idelicNorm (transport K L T) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      Algebra.norm (AdeleRing (𝓞 K) K) (T : TA K L) := by
  letI := (genuineBaseChange K L).β.toAlgebra
  show (genuineBaseChange K L).adelicNorm ((genuineBaseChange K L).tensorEquiv (T : TA K L)) = _
  exact Algebra.norm_eq_of_algEquiv (genuineBaseChange K L).tensorEquiv (T : TA K L)

abbrev Nfin (v : HeightOneSpectrum (𝓞 K)) : Subgroup (v.adicCompletion K)ˣ :=
  (Units.map (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range

abbrev Ninf (w : InfinitePlace K) : Subgroup (w.Completion)ˣ :=
  (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range

abbrev normClassGroup : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range

theorem map_norm_left_mem_Nfin (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    Units.map (Algebra.norm (v.adicCompletion K) : v.adicCompletion K ⊗[K] L →* v.adicCompletion K) z ∈
      Nfin K L v := by
  set e : v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] L ⊗[K] v.adicCompletion K :=
    TensorProduct.RightActions.Algebra.TensorProduct.comm K (v.adicCompletion K) L with he
  refine ⟨Units.map (e : v.adicCompletion K ⊗[K] L →* L ⊗[K] v.adicCompletion K) z, ?_⟩
  refine Units.ext ?_
  simp only [Units.coe_map]
  exact (Algebra.norm_eq_of_algEquiv e (z : v.adicCompletion K ⊗[K] L))

theorem map_norm_left_mem_Ninf (w : InfinitePlace K) (z : (w.Completion ⊗[K] L)ˣ) :
    Units.map (Algebra.norm w.Completion : w.Completion ⊗[K] L →* w.Completion) z ∈ Ninf K L w := by
  set e : w.Completion ⊗[K] L ≃ₐ[w.Completion] L ⊗[K] w.Completion :=
    TensorProduct.RightActions.Algebra.TensorProduct.comm K w.Completion L with he
  refine ⟨Units.map e.toAlgHom.toRingHom.toMonoidHom z, ?_⟩
  refine Units.ext ?_
  rw [Units.coe_map, Units.coe_map]
  exact (Algebra.norm_eq_of_algEquiv e (z : w.Completion ⊗[K] L))

theorem finCompHom_idelicNorm_mem (b : (AdeleRing (𝓞 L) L)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finCompHom K v ((genuineBaseChange K L).idelicNorm b) ∈ Nfin K L v := by
  have key : finCompHom K v ((genuineBaseChange K L).idelicNorm b) =
      Units.map (Algebra.norm (v.adicCompletion K) : v.adicCompletion K ⊗[K] L →* v.adicCompletion K)
        (Units.map (Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) : TA K L →* v.adicCompletion K ⊗[K] L)
          (transportInv K L b)) := by
    refine Units.ext ?_
    rw [val_finCompHom, Units.coe_map, Units.coe_map]
    show _ = Algebra.norm _ (Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) (transportInv K L b : TA K L))
    rw [← map_norm_eq_norm_map, ← evF_apply K v, ← val_idelicNorm_transport, transport_transportInv]
  rw [key]
  exact map_norm_left_mem_Nfin K L v _

theorem infCompHom_idelicNorm_mem (b : (AdeleRing (𝓞 L) L)ˣ) (w : InfinitePlace K) :
    infCompHom K w ((genuineBaseChange K L).idelicNorm b) ∈ Ninf K L w := by
  have key : infCompHom K w ((genuineBaseChange K L).idelicNorm b) =
      Units.map (Algebra.norm w.Completion : w.Completion ⊗[K] L →* w.Completion)
        (Units.map (Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) : TA K L →* w.Completion ⊗[K] L)
          (transportInv K L b)) := by
    refine Units.ext ?_
    rw [val_infCompHom, Units.coe_map, Units.coe_map]
    show _ = Algebra.norm _ (Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) (transportInv K L b : TA K L))
    rw [← map_norm_eq_norm_map, ← evI_apply K w, ← val_idelicNorm_transport, transport_transportInv]
  rw [key]
  exact map_norm_left_mem_Ninf K L w _

end Norms

section LocalGlobal

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

def extAbove (v : HeightOneSpectrum (𝓞 K)) : v.Extension (𝓞 L) :=
  ⟨⟨primeAbove K L v, inferInstance, primeAbove_ne_bot K L v⟩, by
    ext1
    simp [under_primeAbove K L v]⟩

theorem extAbove_asIdeal (v : HeightOneSpectrum (𝓞 K)) : (extAbove K L v).1.asIdeal = primeAbove K L v := rfl

theorem mem_range_idelicNorm_of (u : (AdeleRing (𝓞 K) K)ˣ)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ (w : v.Extension (𝓞 L)) (y : w.1.adicCompletion L),
      Algebra.norm (v.adicCompletion K) y = ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)
    (harch : ∀ (v : InfinitePlace K) (hv : v.IsReal),
      (∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → w.IsComplex) →
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v)) :
    u ∈ (genuineBaseChange K L).idelicNorm.range :=
  M4aHerbrand.AdeleBaseChange.mem_range_idelicNorm_of_forall_exists_norm_eq K L (genuineBaseChange K L) u hfin harch

theorem finCompHom_mem_Nfin_of_mem_range {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ (genuineBaseChange K L).idelicNorm.range)
    (v : HeightOneSpectrum (𝓞 K)) : finCompHom K v u ∈ Nfin K L v := by
  obtain ⟨b, rfl⟩ := hu
  exact finCompHom_idelicNorm_mem K L b v

theorem infCompHom_mem_Ninf_of_mem_range {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ (genuineBaseChange K L).idelicNorm.range)
    (w : InfinitePlace K) : infCompHom K w u ∈ Ninf K L w := by
  obtain ⟨b, rfl⟩ := hu
  exact infCompHom_idelicNorm_mem K L b w

theorem range_idelicNorm_le : (genuineBaseChange K L).idelicNorm.range ≤ normClassGroup K L := le_sup_right

end LocalGlobal

section Finite

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem projFin_apply (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v =
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := rfl

theorem isAdjuster_localIdele {𝔣 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔣) (t : (v.adicCompletion K)ˣ) :
    IsAdjuster K 𝔣 (localIdele K v t) 1 := by
  refine ⟨fun w hw => ?_, fun τ => ?_⟩
  · have hwv : w ≠ v := fun h => hv (h ▸ hw)
    have key : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
        (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 →
        Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 ∧
          Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w - 1) ≤
            WithZero.exp (-((Associates.mk w.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) := by
      intro u hu
      rw [hu, sub_self, map_one, map_zero]
      exact ⟨rfl, zero_le'⟩
    simp only [map_one, inv_one, mul_one]
    exact key _ (localUnit_apply_of_ne (𝓞 K) K v t hwv)
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one K τ rfl

theorem placeOrd_projFin_localIdele_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    placeOrd K (projFin K (localIdele K v t)) v = -WithZero.log (Valued.v (t : v.adicCompletion K)) := by
  unfold placeOrd
  rw [projFin_apply, localIdele_snd_apply, localUnit_apply_self]

theorem placeOrd_projFin_localIdele_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) : placeOrd K (projFin K (localIdele K v t)) w = 0 := by
  unfold placeOrd
  rw [projFin_apply, localIdele_snd_apply, localUnit_apply_of_ne (𝓞 K) K v t hw, map_one, WithZero.log_one, neg_zero]

theorem finprod_artinFrob_pow_placeOrd_localIdele [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob K L w ^ placeOrd K (projFin K (localIdele K v t)) w =
      artinFrob K L v ^ (-WithZero.log (Valued.v (t : v.adicCompletion K))) := by
  rw [finprod_eq_single (fun w => artinFrob K L w ^ placeOrd K (projFin K (localIdele K v t)) w) v ?_]
  · rw [placeOrd_projFin_localIdele_self]
  · intro w hw
    beta_reduce
    rw [placeOrd_projFin_localIdele_of_ne K v t hw, zpow_zero]

attribute [local instance] Ideal.Quotient.field in

theorem orderOf_artinFrob_eq_inertiaDeg [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (hI : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥) :
    orderOf (artinFrob K L v) = v.asIdeal.inertiaDeg' (primeAbove K L v) := by
  haveI : ((primeAbove K L v).under (𝓞 K)).IsMaximal := by
    rw [under_primeAbove]; exact v.isMaximal
  haveI : Finite (𝓞 K ⧸ (primeAbove K L v).under (𝓞 K)) := by
    rw [under_primeAbove]; exact Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Fintype (𝓞 K ⧸ (primeAbove K L v).under (𝓞 K)) := Fintype.ofFinite _
  have h1 := ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
    (A := 𝓞 K) (P := primeAbove K L v) (G := L ≃ₐ[K] L) hI
    ⟨artinFrob K L v, (isArithFrobAt_artinFrob K L v).mem_stabilizer⟩
    (isArithFrobAt_artinFrob K L v)
  rw [h1, ← Ideal.inertiaDeg_algebraMap]
  rw [show ((primeAbove K L v).under (𝓞 K)).inertiaDeg' (primeAbove K L v)
      = v.asIdeal.inertiaDeg' (primeAbove K L v) by rw [under_primeAbove]]

attribute [local instance] Ideal.Quotient.field in

theorem inertia_eq_bot_of_liesOver [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (hI : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] : Q.inertia (L ≃ₐ[K] L) = ⊥ := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
  have hP := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal (primeAbove K L v)
  have hQ' := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal Q
  rw [hI, Subgroup.card_bot] at hP
  rw [← hP] at hQ'
  exact Subgroup.card_eq_one.mp hQ'

attribute [local instance] Ideal.Quotient.field in

theorem ramificationIdx_eq_one [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (hI : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥) :
    v.asIdeal.ramificationIdx' (primeAbove K L v) = 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have h := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal (primeAbove K L v)
  rw [hI, Subgroup.card_bot] at h
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal (primeAbove K L v) v.ne_bot,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove K L v) (L ≃ₐ[K] L), ← h]

theorem not_dvd_of_inertia_eq_bot [IsGalois K L] {𝔣₀ : Ideal (𝓞 K)}
    (hsupp : ∀ v₀ : HeightOneSpectrum (𝓞 K), v₀.asIdeal ∣ 𝔣₀ →
      ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v₀.asIdeal ∧ Q.inertia (L ≃ₐ[K] L) ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 K)) (hI : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥) :
    ¬ v.asIdeal ∣ 𝔣₀ := by
  intro hdvd
  obtain ⟨Q, hQp, hQo, hQI⟩ := hsupp v hdvd
  haveI := hQp
  haveI := hQo
  exact hQI (inertia_eq_bot_of_liesOver K L v hI Q)

theorem nfin_eq_top_of_split (v : HeightOneSpectrum (𝓞 K))
    (he : v.asIdeal.ramificationIdx' (primeAbove K L v) = 1)
    (hf : v.asIdeal.inertiaDeg' (primeAbove K L v) = 1) : Nfin K L v = ⊤ := by
  set w₀ : v.Extension (𝓞 L) := extAbove K L v with hw₀
  have hrank : Module.finrank (v.adicCompletion K) (w₀.1.adicCompletion L) = 1 := by
    rw [← HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w₀]
    show v.asIdeal.ramificationIdx' (primeAbove K L v) * v.asIdeal.inertiaDeg' (primeAbove K L v) = 1
    rw [he, hf]
  rw [eq_top_iff]
  rintro x -
  have hmem : localIdele K v x ∈ (genuineBaseChange K L).idelicNorm.range := by
    refine mem_range_idelicNorm_of K L _ (fun v' => ?_) (fun v' hv' _ => ?_)
    · by_cases hv' : v' = v
      · subst hv'
        refine ⟨w₀, algebraMap (v'.adicCompletion K) (w₀.1.adicCompletion L) (x : v'.adicCompletion K), ?_⟩
        rw [Algebra.norm_algebraMap, hrank, pow_one, localIdele_snd_apply, localUnit_apply_self]
      · refine ⟨extAbove K L v', 1, ?_⟩
        rw [map_one, localIdele_snd_apply, localUnit_apply_of_ne (𝓞 K) K v x hv']
    · rw [localIdele_fst]
      show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv' 1
      rw [map_one]
      exact one_pos
  have h := finCompHom_mem_Nfin_of_mem_range K L hmem v
  rwa [finCompHom_localIdele_self] at h

theorem exists_unit_valued_eq_exp_neg_one (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer K v
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  exact ⟨Units.mk0 _ hπ0, hπ⟩

theorem finClause (h2 : Module.finrank K L = 2) (v : HeightOneSpectrum (𝓞 K)) (hN : Nfin K L v ≠ ⊤) :
    ∃ x : (v.adicCompletion K)ˣ,
      Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v x) ∉ normClassGroup K L := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  haveI : IsMulCommutative (L ≃ₐ[K] L) := inferInstance
  by_cases hI : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥
  ·
    obtain ⟨𝔣₀, hadm, hsupp⟩ := LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported K L
    have hvf : ¬ v.asIdeal ∣ 𝔣₀ := not_dvd_of_inertia_eq_bot K L hsupp v hI
    have hadm2 : IsAdmissibleModulusOfDegree K L (Module.finrank K L) 𝔣₀ := by
      rw [h2]
      exact (isAdmissibleModulusOfDegree_iff_at K L Nat.prime_two 𝔣₀).mpr
        (PrimeNormIndex.isAdmissibleModulusAt_two K L hadm)
    obtain ⟨r, -, hker, -, hfrob⟩ :=
      NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
        K L 𝔣₀ hadm2
    obtain ⟨π, hπ⟩ := exists_unit_valued_eq_exp_neg_one K v
    refine ⟨π, fun hmem => ?_⟩
    have hr : r (localIdele K v π) = artinFrob K L v := by
      rw [hfrob _ (isAdjuster_localIdele K hvf π), finprod_artinFrob_pow_placeOrd_localIdele, hπ,
        WithZero.log_exp, neg_neg, zpow_one]
    have h1 : artinFrob K L v = 1 := by
      rw [← hr, ← MonoidHom.mem_ker, hker]
      exact hmem
    have hf : v.asIdeal.inertiaDeg' (primeAbove K L v) = 1 := by
      rw [← orderOf_artinFrob_eq_inertiaDeg K L v hI, h1, orderOf_one]
    exact hN (nfin_eq_top_of_split K L v (ramificationIdx_eq_one K L v hI) hf)
  ·
    have hprime : (Module.finrank K L).Prime := by rw [h2]; exact Nat.prime_two
    obtain ⟨t, -, -, ht⟩ :=
      LanglandsTunnell.P2.Artin.exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
        K L hprime v hI
    exact ⟨t, ht⟩

end Finite

section Infinite

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

def intUnit (β : 𝓞 K) (hβ : β ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K β) ((map_ne_zero_iff _ (RingOfIntegers.coe_injective)).mpr hβ)

theorem val_intUnit (β : 𝓞 K) (hβ : β ≠ 0) : ((intUnit K β hβ : Kˣ) : K) = algebraMap (𝓞 K) K β := rfl

theorem valued_finDiag_intUnit (β : 𝓞 K) (hβ : β ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((finDiag K (intUnit K β hβ) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) =
      WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {β})).factors : ℤ)) := by
  rw [finDiag_snd_apply, val_intUnit, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v hβ]

theorem placeOrd_finDiag_intUnit (β : 𝓞 K) (hβ : β ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (projFin K (finDiag K (intUnit K β hβ))) v =
      FractionalIdeal.count K v ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
  have hJ0 : (Ideal.span {β} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hβ
  unfold placeOrd
  rw [projFin_apply, valued_finDiag_intUnit, WithZero.log_exp, neg_neg, FractionalIdeal.count_coe K v hJ0]

theorem isAdjuster_finDiag_intUnit {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (β : 𝓞 K) (hβ : β ≠ 0) (hβ1 : β - 1 ∈ 𝔣) :
    IsAdjuster K 𝔣 (finDiag K (intUnit K β hβ)) 1 := by
  classical
  refine ⟨fun v hv => ?_, fun τ => ?_⟩
  · simp only [map_one, inv_one, mul_one]
    set n : ℕ := (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors with hn

    have hle : 𝔣 ≤ v.asIdeal ^ n := by
      have h1 := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h𝔣) v.associates_irreducible).mpr
        (le_refl n)
      rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at h1
      exact Ideal.le_of_dvd h1
    have hcong : Valued.v (((finDiag K (intUnit K β hβ) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v - 1) ≤
        WithZero.exp (-(n : ℤ)) := by
      rw [finDiag_snd_apply, val_intUnit]
      have hcast : ((algebraMap (𝓞 K) K β : K) : v.adicCompletion K) - 1 =
          ((algebraMap (𝓞 K) K (β - 1) : K) : v.adicCompletion K) := by
        rw [map_sub, map_one]
        have h := map_sub (algebraMap K (v.adicCompletion K)) (algebraMap (𝓞 K) K β) 1
        rw [map_one] at h
        exact h.symm
      rw [hcast, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact hle hβ1
    refine ⟨?_, hcong⟩

    have hn0 : n ≠ 0 := (Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mpr hv
    have hlt : Valued.v (((finDiag K (intUnit K β hβ) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v - 1) < 1 := by
      refine lt_of_le_of_lt hcong ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have := Valuation.map_one_add_of_lt Valued.v hlt
    rwa [add_sub_cancel] at this
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one K τ rfl

theorem artinMap_finDiag_intUnit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (β : 𝓞 K) (hβ : β ≠ 0) (hβ1 : β - 1 ∈ 𝔣)
    (r : (AdeleRing (𝓞 K) K)ˣ →* (L ≃ₐ[K] L))
    (hfrob : ∀ u : (AdeleRing (𝓞 K) K)ˣ, IsAdjuster K 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob K L v ^ placeOrd K (projFin K u) v) :
    r (finDiag K (intUnit K β hβ)) =
      artinSymbol K L 𝔣 ⟨principalUnit K β hβ, principalUnit_mem_coprimeToModulus K hβ hβ1⟩ := by
  rw [hfrob _ (isAdjuster_finDiag_intUnit K h𝔣 β hβ hβ1)]
  unfold artinSymbol
  rw [raySymbolHom_apply, principalUnit_val]
  unfold raySymbol
  exact finprod_congr fun v => by rw [placeOrd_finDiag_intUnit]

theorem embedding_of_isReal_ne {v w : InfinitePlace K} (hv : v.IsReal) (hw : w.IsReal) (hvw : v ≠ w) :
    InfinitePlace.embedding_of_isReal hv ≠ InfinitePlace.embedding_of_isReal hw := by
  intro heq
  apply hvw
  have hemb : v.embedding = w.embedding := by
    ext x
    have h := congrArg (fun f : K →+* ℝ => ((f x : ℝ) : ℂ)) heq
    simpa only [InfinitePlace.embedding_of_isReal_apply] using h
  rw [← InfinitePlace.mk_embedding v, hemb, InfinitePlace.mk_embedding]

theorem extensionEmbeddingOfIsReal_algebraMap {v : InfinitePlace K} (hv : v.IsReal) (k : K) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (algebraMap K v.Completion k) =
      InfinitePlace.embedding_of_isReal hv k := by
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal hv ((WithAbs.toAbs v.1 k : WithAbs v.1) : v.Completion) = _
  rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  rfl

theorem archPart_mem_range_idelicNorm {w : InfinitePlace K} (hw : w.IsReal) (β : 𝓞 K) (hβ : β ≠ 0)
    (hpos : ∀ τ' : K →+* ℝ, τ' ≠ InfinitePlace.embedding_of_isReal hw → 0 < τ' (algebraMap (𝓞 K) K β)) :
    principalIdele K (intUnit K β hβ) * (finDiag K (intUnit K β hβ))⁻¹ *
        (archCentralUnit K w (Units.map (algebraMap K w.Completion : K →* w.Completion) (intUnit K β hβ)))⁻¹ ∈
      (genuineBaseChange K L).idelicNorm.range := by
  set a : Kˣ := intUnit K β hβ with ha
  set Y : (AdeleRing (𝓞 K) K)ˣ := principalIdele K a * (finDiag K a)⁻¹ *
    (archCentralUnit K w (Units.map (algebraMap K w.Completion : K →* w.Completion) a))⁻¹ with hY
  have hfinY : ∀ v : HeightOneSpectrum (𝓞 K), finCompHom K v Y = 1 := fun v => by
    rw [hY, map_mul, map_mul, map_inv, map_inv, finCompHom_finDiag, finCompHom_archCentralUnit, mul_inv_cancel,
      inv_one, mul_one]
  have hinfY_self : infCompHom K w Y = 1 := by
    rw [hY, map_mul, map_mul, map_inv, map_inv, infCompHom_finDiag, infCompHom_archCentralUnit_self,
      infCompHom_principal, inv_one, mul_one, mul_inv_cancel]
  have hinfY_of_ne : ∀ {v : InfinitePlace K}, v ≠ w →
      infCompHom K v Y = Units.map (algebraMap K v.Completion : K →* v.Completion) a := fun {v} hvw => by
    rw [hY, map_mul, map_mul, map_inv, map_inv, infCompHom_finDiag, infCompHom_archCentralUnit_of_ne K w _ hvw,
      infCompHom_principal, inv_one, mul_one, mul_one]
  refine mem_range_idelicNorm_of K L Y (fun v => ⟨extAbove K L v, 1, ?_⟩) (fun v hv hcx => ?_)
  · rw [map_one, ← val_finCompHom, hfinY, Units.val_one]
  · rw [← val_infCompHom]
    by_cases hvw : v = w
    · subst hvw
      rw [hinfY_self, Units.val_one, map_one]
      exact one_pos
    · rw [hinfY_of_ne hvw, Units.coe_map, MonoidHom.coe_coe, extensionEmbeddingOfIsReal_algebraMap, ha, val_intUnit]
      exact hpos _ (embedding_of_isReal_ne K hv hw hvw)

theorem exists_isComplex_of_ninf_ne_top (w : InfinitePlace K) (hN : Ninf K L w ≠ ⊤) :
    ∃ (hw : w.IsReal) (w' : InfinitePlace L), w'.comap (algebraMap K L) = w ∧ w'.IsComplex := by
  by_contra hcon
  apply hN
  rw [eq_top_iff]
  rintro x -
  have hmem : archCentralUnit K w x ∈ (genuineBaseChange K L).idelicNorm.range := by
    refine mem_range_idelicNorm_of K L _ (fun v => ⟨extAbove K L v, 1, ?_⟩) (fun v hv hall => ?_)
    · rw [map_one]
      rfl
    · by_cases hvw : v = w
      · subst hvw
        obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
        exact (hcon ⟨hv, w', hw', hall w' hw'⟩).elim
      · rw [archCentralUnit_fst_of_ne w x hvw, map_one]
        exact one_pos
  have h := infCompHom_mem_Ninf_of_mem_range K L hmem w
  rwa [infCompHom_archCentralUnit_self] at h

theorem infClause (h2 : Module.finrank K L = 2) (w : InfinitePlace K) (hN : Ninf K L w ≠ ⊤) :
    ∃ x : (w.Completion)ˣ, archCentralUnit K w x ∉ normClassGroup K L := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  haveI : IsMulCommutative (L ≃ₐ[K] L) := inferInstance

  obtain ⟨hw, w', hw', hw'c⟩ := exists_isComplex_of_ninf_ne_top K L w hN

  set τ : K →+* ℝ := InfinitePlace.embedding_of_isReal hw with hτ
  have hemb : w.embedding = w'.embedding.comp (algebraMap K L) := by
    have h := InfinitePlace.comap_embedding_of_isReal (algebraMap K L) (w := w') (by rw [hw']; exact hw)
    rwa [hw'] at h
  have hφ : ∀ x : K, w'.embedding (algebraMap K L x) = τ x := fun x => by
    rw [hτ, InfinitePlace.embedding_of_isReal_apply, hemb]
    rfl
  have hφr : ¬ ComplexEmbedding.IsReal w'.embedding := InfinitePlace.isComplex_iff.mp hw'c

  obtain ⟨𝔣, hadm, -⟩ := LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported K L
  have h𝔣 : 𝔣 ≠ ⊥ := hadm.1
  have hadm2 : IsAdmissibleModulusOfDegree K L (Module.finrank K L) 𝔣 := by
    rw [h2]
    exact (isAdmissibleModulusOfDegree_iff_at K L Nat.prime_two 𝔣).mpr (PrimeNormIndex.isAdmissibleModulusAt_two K L hadm)
  obtain ⟨r, -, hker, -, hfrob⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
      K L 𝔣 hadm2
  obtain ⟨β, hβ, hβ1, -, hpos, hart⟩ :=
    NumberField.exists_artinSymbol_principalUnit_ne_one_of_not_isReal K L 𝔣 h𝔣 τ w'.embedding hφ hφr

  set a : Kˣ := intUnit K β hβ with ha
  set x : (w.Completion)ˣ := Units.map (algebraMap K w.Completion : K →* w.Completion) a with hx
  have huf : finDiag K a ∉ normClassGroup K L := by
    intro hmem
    have h1 : r (finDiag K a) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hmem
    rw [ha, artinMap_finDiag_intUnit K L h𝔣 β hβ hβ1 r hfrob] at h1
    exact hart 𝔣 (principalUnit_mem_coprimeToModulus K hβ hβ1) h1
  have hP : principalIdele K a ∈ normClassGroup K L :=
    Subgroup.mem_sup_left (principalIdele_mem K a)
  have hY : principalIdele K a * (finDiag K a)⁻¹ * (archCentralUnit K w x)⁻¹ ∈ normClassGroup K L :=
    range_idelicNorm_le K L (archPart_mem_range_idelicNorm K L hw β hβ hpos)

  refine ⟨x, fun hA => huf ?_⟩
  have heq : finDiag K a =
      (archCentralUnit K w x)⁻¹ * (principalIdele K a * (finDiag K a)⁻¹ * (archCentralUnit K w x)⁻¹)⁻¹ *
        principalIdele K a := by
    group
  rw [heq]
  exact mul_mem (mul_mem (inv_mem hA) (inv_mem hY)) hP

end Infinite

end QuadLocalIdele

end

open QuadLocalIdele in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range ≠ ⊤ →
        ∃ x : (v.adicCompletion K)ˣ,
          Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v x) ∉
            principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range) ∧
    (∀ w : InfinitePlace K,
      (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range ≠ ⊤ →
        ∃ x : (w.Completion)ˣ,
          archCentralUnit K w x ∉ principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range) :=
  ⟨fun v hv => finClause K L h2 v hv, fun w hw => infClause K L h2 w hw⟩

end S_NumberField_exists_localIdele_not_mem_principalIdeles_sup_range_idelicNorm_of_finrank_eq_two
end P2MW
export P2MW.S_NumberField_exists_localIdele_not_mem_principalIdeles_sup_range_idelicNorm_of_finrank_eq_two (solution)
