-- Prove2me | solution 1 for NumberField.localChar_ne_one_of_range_norm_ne_top_of_isIdeleClassChar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1261a2fd-7d5f-5cda-9591-318e01f3eb1c

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_exists_localIdele_not_mem_principalIdeles_sup_range_idelicNorm_of_finrank_eq_two
import Theorems.Thm_NumberField_ideleClass_normCoset_index_dvd_finrank
import Theorems.Thm_M4aHerbrand_ideleClass_normCoset_index_ne_zero_and_finrank_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_localChar_ne_one_of_range_norm_ne_top_of_isIdeleClassChar_of_finrank_eq_two
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1"
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq GroupCohomology.RepPi.proj_hom_apply"
p2m_attr_erase "simp" "GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain Topology Filter
open NumberField.AdelicLevel NumberField.AdelicVolume
open scoped TensorProduct

noncomputable section

namespace QuadLGC

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

theorem eq_of_forall_repr_eq {ι : Type*} [Fintype ι] (b : Module.Basis ι K L) {T T' : A ⊗[K] L}
    (h : ∀ i, (Algebra.TensorProduct.basis A b).repr T i = (Algebra.TensorProduct.basis A b).repr T' i) : T = T' :=
  (Algebra.TensorProduct.basis A b).repr.injective (Finsupp.ext h)

end NormBaseChange

section Eval

open scoped Classical

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

theorem AdeleRing.ext' {x y : AdeleRing (𝓞 K) K} (hI : ∀ w, x.1 w = y.1 w) (hF : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext (funext hI) (FiniteAdeleRing.ext K hF)

def finSingle (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) : FiniteAdeleRing (𝓞 K) K :=
  ⟨Pi.single v c, Filter.eventually_cofinite.2 ((Set.finite_singleton v).subset fun w hw => by
    by_contra hwv
    exact hw (by rw [Pi.single_eq_of_ne hwv]; exact zero_mem _))⟩

theorem finSingle_apply_self (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) : finSingle K v c v = c := by
  show (Pi.single v c : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) v = c
  simp

theorem finSingle_apply_of_ne (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) {w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) : finSingle K v c w = 0 := by
  show (Pi.single v c : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) w = 0
  rw [Pi.single_eq_of_ne h]

def inclF (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K →ₗ[K] AdeleRing (𝓞 K) K where
  toFun c := (0, finSingle K v c)
  map_add' c d := AdeleRing.ext' K (fun _ => (add_zero _).symm) fun w => by
    show finSingle K v (c + d) w = finSingle K v c w + finSingle K v d w
    by_cases h : w = v
    · subst h; rw [finSingle_apply_self, finSingle_apply_self, finSingle_apply_self]
    · rw [finSingle_apply_of_ne K v _ h, finSingle_apply_of_ne K v _ h, finSingle_apply_of_ne K v _ h, add_zero]
  map_smul' k c := by
    show ((0 : InfiniteAdeleRing K), finSingle K v (k • c)) = k • ((0 : InfiniteAdeleRing K), finSingle K v c)
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, smul_zero]
    · rw [Prod.smul_snd]
      refine FiniteAdeleRing.ext K fun w => ?_
      rw [Algebra.smul_def k (finSingle K v c)]
      rw [show (algebraMap K (FiniteAdeleRing (𝓞 K) K) k * finSingle K v c) w =
        (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) w * finSingle K v c w from rfl]
      by_cases h : w = v
      · subst h
        rw [finSingle_apply_self, finSingle_apply_self, Algebra.smul_def]
        rfl
      · rw [finSingle_apply_of_ne K v _ h, finSingle_apply_of_ne K v _ h, mul_zero]

theorem evF_inclF_self (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) : evF K v (inclF K v c) = c :=
  finSingle_apply_self K v c

theorem evF_inclF_of_ne (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) {w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) : evF K w (inclF K v c) = 0 :=
  finSingle_apply_of_ne K v c h

theorem evI_inclF (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) (w : InfinitePlace K) :
    evI K w (inclF K v c) = 0 := rfl

def inclI (w : InfinitePlace K) : w.Completion →ₗ[K] AdeleRing (𝓞 K) K :=
  (LinearMap.inl K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (LinearMap.single K (fun w : InfinitePlace K => w.Completion) w)

theorem evI_inclI_self (w : InfinitePlace K) (c : w.Completion) : evI K w (inclI K w c) = c := by
  show (Pi.single w c : InfiniteAdeleRing K) w = c
  simp

theorem evI_inclI_of_ne (w : InfinitePlace K) (c : w.Completion) {w' : InfinitePlace K} (h : w' ≠ w) :
    evI K w' (inclI K w c) = 0 := by
  show (Pi.single w c : InfiniteAdeleRing K) w' = 0
  rw [Pi.single_eq_of_ne h]

theorem evF_inclI (w : InfinitePlace K) (c : w.Completion) (v : HeightOneSpectrum (𝓞 K)) :
    evF K v (inclI K w c) = 0 := rfl

end Eval

variable (K : Type) [Field K] [NumberField K]

def localIdele (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (finIncl (𝓞 K) K)).comp (localUnit (𝓞 K) K v)

theorem localIdele_apply (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    localIdele K v t = Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t) := rfl

theorem fst_prod {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K) :
    (∏ i ∈ s, f i).1 = ∏ i ∈ s, (f i).1 :=
  map_prod (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) f s

theorem snd_prod {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 :=
  map_prod (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) f s

theorem finAdele_prod_apply {ι : Type*} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) : (∏ i ∈ s, f i) w = ∏ i ∈ s, f i w :=
  map_prod (finAdeleEval (𝓞 K) K w) f s

omit [NumberField K] in
theorem infAdele_prod_apply {ι : Type*} (s : Finset ι) (f : ι → InfiniteAdeleRing K)
    (w : InfinitePlace K) : (∏ i ∈ s, f i) w = ∏ i ∈ s, f i w :=
  Finset.prod_apply w s f

theorem fst_val_mul (a b : (AdeleRing (𝓞 K) K)ˣ) :
    ((a * b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 =
      (a : AdeleRing (𝓞 K) K).1 * (b : AdeleRing (𝓞 K) K).1 :=
  rfl

theorem snd_val_mul_apply (a b : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    ((a * b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w =
      (a : AdeleRing (𝓞 K) K).2 w * (b : AdeleRing (𝓞 K) K).2 w :=
  rfl

theorem snd_val_mul_inv_apply (t : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (t : AdeleRing (𝓞 K) K).2 w * ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  rw [← snd_val_mul_apply, mul_inv_cancel]; rfl

theorem snd_val_inv_mul_apply (t : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w * (t : AdeleRing (𝓞 K) K).2 w = 1 := by
  rw [← snd_val_mul_apply, inv_mul_cancel]; rfl

theorem val_localIdele_fst (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem val_localIdele_snd (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 =
      (localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) := rfl

theorem val_localIdele_snd_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = t := by
  rw [val_localIdele_snd]; exact localUnit_apply_self (𝓞 K) K v t

theorem val_localIdele_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  rw [val_localIdele_snd]; exact localUnit_apply_of_ne (𝓞 K) K v t hw

theorem val_prod_localIdele_fst (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) :
    ((∏ v ∈ S, localIdele K v (f v) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  rw [Units.coe_prod, fst_prod]
  exact Finset.prod_eq_one fun v _ => val_localIdele_fst K v (f v)

open scoped Classical in

theorem val_prod_localIdele_snd_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    ((∏ v ∈ S, localIdele K v (f v) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w =
      if w ∈ S then ((f w : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
  rw [Units.coe_prod, snd_prod, finAdele_prod_apply]
  by_cases h : w ∈ S
  · rw [if_pos h, Finset.prod_eq_single w]
    · exact val_localIdele_snd_self K w (f w)
    · intro v _ hv
      exact val_localIdele_snd_of_ne K v (f v) (Ne.symm hv)
    · intro h'; exact absurd h h'
  · rw [if_neg h]
    refine Finset.prod_eq_one fun v hv => val_localIdele_snd_of_ne K v (f v) ?_
    rintro rfl
    exact h hv

theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt {z : ℂ} (h : ∀ n : ℕ, ‖z ^ (2 ^ n) - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have key : ∀ n : ℕ, (3 / 2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 ^ n) - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt := h n
      have hfac : z ^ (2 ^ (n + 1)) - 1 = (z ^ (2 ^ n) - 1) * (z ^ (2 ^ n) + 1) := by ring
      have hge : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ n) + 1‖ := by
        have h2 := norm_sub_norm_le (2 : ℂ) (1 - z ^ (2 ^ n))
        have h3 : (2 : ℂ) - (1 - z ^ (2 ^ n)) = z ^ (2 ^ n) + 1 := by ring
        rw [h3, norm_sub_rev, Complex.norm_two] at h2
        linarith
      calc (3 / 2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3 / 2) ^ n * ‖z - 1‖ * (3 / 2) := by ring
        _ ≤ ‖z ^ (2 ^ n) - 1‖ * ‖z ^ (2 ^ n) + 1‖ :=
            mul_le_mul ih hge (by norm_num) (norm_nonneg _)
        _ = ‖z ^ (2 ^ (n + 1)) - 1‖ := by rw [hfac, norm_mul]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key n
  have h2 := h n
  rw [div_lt_iff₀ hd] at hn
  linarith

abbrev UnitPi (K : Type) [Field K] [NumberField K] : Type :=
  ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ

def finOf (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) : FiniteAdeleRing (𝓞 K) K :=
  ⟨fun v => (x v : v.adicCompletion K), Filter.Eventually.of_forall fun v => (x v).2⟩

theorem finOf_apply (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) (v : HeightOneSpectrum (𝓞 K)) :
    finOf K x v = (x v : v.adicCompletion K) := rfl

theorem finOf_one : finOf K 1 = 1 := FiniteAdeleRing.ext K fun _ => rfl

theorem finOf_mul (x y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) :
    finOf K (x * y) = finOf K x * finOf K y := FiniteAdeleRing.ext K fun _ => rfl

theorem continuous_finOf : Continuous (finOf K) := by
  have h1 := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => ((v.adicCompletionIntegers K : Set (v.adicCompletion K))))
    (𝓕 := Filter.cofinite)).continuous
  have h2 : Continuous fun x : (∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) =>
      fun v => (⟨(x v : v.adicCompletion K), (x v).2⟩ :
        ((v.adicCompletionIntegers K : Set (v.adicCompletion K)))) :=
    continuous_pi fun v => (continuous_subtype_val.comp (continuous_apply v)).subtype_mk _
  exact h1.comp h2

def unitIdele : UnitPi K →* (AdeleRing (𝓞 K) K)ˣ where
  toFun u :=
    ⟨((1 : InfiniteAdeleRing K), finOf K fun v => (u v : v.adicCompletionIntegers K)),
      ((1 : InfiniteAdeleRing K), finOf K fun v => (((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ) :
        v.adicCompletionIntegers K)),
      Prod.ext (one_mul _) (by
        show (finOf K fun v => (u v : v.adicCompletionIntegers K)) *
            (finOf K fun v => (((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)) = 1
        rw [← finOf_mul, ← finOf_one]
        congr 1
        funext v
        exact Units.mul_inv (u v)),
      Prod.ext (one_mul _) (by
        show (finOf K fun v => (((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)) *
            (finOf K fun v => (u v : v.adicCompletionIntegers K)) = 1
        rw [← finOf_mul, ← finOf_one]
        congr 1
        funext v
        exact Units.inv_mul (u v))⟩
  map_one' := Units.ext (Prod.ext rfl (FiniteAdeleRing.ext K fun _ => rfl))
  map_mul' _ _ := Units.ext (Prod.ext (one_mul _).symm (FiniteAdeleRing.ext K fun _ => rfl))

theorem val_unitIdele_fst (u : UnitPi K) : ((unitIdele K u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 :=
  rfl

theorem val_unitIdele_snd_apply (u : UnitPi K) (v : HeightOneSpectrum (𝓞 K)) :
    ((unitIdele K u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = ((u v : v.adicCompletionIntegers K) :
      v.adicCompletion K) :=
  rfl

theorem continuous_unitIdele : Continuous (unitIdele K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : UnitPi K =>
      (((1 : InfiniteAdeleRing K), finOf K fun v => (u v : v.adicCompletionIntegers K)) : AdeleRing (𝓞 K) K)
    exact continuous_const.prodMk ((continuous_finOf K).comp
      (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)))
  · show Continuous fun u : UnitPi K =>
      (((1 : InfiniteAdeleRing K), finOf K fun v => (((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ) :
        v.adicCompletionIntegers K)) : AdeleRing (𝓞 K) K)
    exact continuous_const.prodMk ((continuous_finOf K).comp
      (continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v)))

variable {K}
variable (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

def ηC : (AdeleRing (𝓞 K) K)ˣ →* ℂ := (Units.coeHom ℂ).comp η

theorem ηC_apply (t : (AdeleRing (𝓞 K) K)ˣ) : ηC η t = ((η t : ℂˣ) : ℂ) := rfl

theorem continuous_ηC (hc : Continuous η) : Continuous (ηC η) :=
  Units.continuous_val.comp hc

theorem exists_finset_forall_norm_sub_one_lt (hc : Continuous η) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ u : UnitPi K, (∀ v ∈ T, u v = 1) →
      ‖ηC η (unitIdele K u) - 1‖ < 1 / 2 := by
  have hopen : IsOpen {u : UnitPi K | ‖ηC η (unitIdele K u) - 1‖ < 1 / 2} :=
    isOpen_lt (((continuous_ηC η hc).comp (continuous_unitIdele K)).sub continuous_const).norm continuous_const
  have hmem : (1 : UnitPi K) ∈ {u : UnitPi K | ‖ηC η (unitIdele K u) - 1‖ < 1 / 2} := by
    show ‖ηC η (unitIdele K 1) - 1‖ < 1 / 2
    rw [map_one, map_one, sub_self, norm_zero]
    norm_num
  obtain ⟨I, t, ht, hsub⟩ := isOpen_pi_iff.1 hopen 1 hmem
  refine ⟨I, fun u hu => hsub (Set.mem_pi.2 fun v hv => ?_)⟩
  rw [hu v (Finset.mem_coe.1 hv)]
  exact (ht v (Finset.mem_coe.1 hv)).2

theorem apply_unitIdele_eq_one {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ u : UnitPi K, (∀ v ∈ T, u v = 1) → ‖ηC η (unitIdele K u) - 1‖ < 1 / 2)
    (u : UnitPi K) (hu : ∀ v ∈ T, u v = 1) : ηC η (unitIdele K u) = 1 := by
  refine eq_one_of_forall_norm_pow_two_pow_sub_one_lt fun n => ?_
  rw [← map_pow, ← map_pow]
  exact hT _ fun v hv => by rw [Pi.pow_apply, hu v hv, one_pow]

theorem apply_eq_one_of_integral {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ u : UnitPi K, (∀ v ∈ T, u v = 1) → ‖ηC η (unitIdele K u) - 1‖ < 1 / 2)
    (r : (AdeleRing (𝓞 K) K)ˣ) (h1 : (r : AdeleRing (𝓞 K) K).1 = 1)
    (hint : ∀ v : HeightOneSpectrum (𝓞 K), (r : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K ∧
      ((r⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K)
    (hT' : ∀ v ∈ T, (r : AdeleRing (𝓞 K) K).2 v = 1) : η r = 1 := by
  let u : UnitPi K := fun v =>
    ⟨⟨_, (hint v).1⟩, ⟨_, (hint v).2⟩, Subtype.ext (snd_val_mul_inv_apply K r v),
      Subtype.ext (snd_val_inv_mul_apply K r v)⟩
  have hru : unitIdele K u = r := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact h1.symm
    · exact FiniteAdeleRing.ext K fun v => rfl
  have h : ηC η (unitIdele K u) = 1 := apply_unitIdele_eq_one η hT u fun v hv => Units.ext (Subtype.ext (hT' v hv))
  rw [hru, ηC_apply] at h
  exact Units.val_eq_one.mp h

theorem apply_localIdele (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    η (localIdele K v t) = localChar η v t := rfl

theorem localChar_eq_one_of_not_mem {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ u : UnitPi K, (∀ v ∈ T, u v = 1) → ‖ηC η (unitIdele K u) - 1‖ < 1 / 2)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ T) (t : (v.adicCompletion K)ˣ)
    (ht : (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (ht' : ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    localChar η v t = 1 := by
  rw [← apply_localIdele]
  have hinv : (localIdele K v t)⁻¹ = localIdele K v t⁻¹ := (map_inv _ _).symm
  refine apply_eq_one_of_integral η hT _ (val_localIdele_fst K v t) (fun w => ?_) (fun w hw => ?_)
  · by_cases hw : w = v
    · subst hw
      rw [hinv, val_localIdele_snd_self, val_localIdele_snd_self]
      exact ⟨ht, ht'⟩
    · rw [hinv, val_localIdele_snd_of_ne K v t hw, val_localIdele_snd_of_ne K v _ hw]
      exact ⟨one_mem _, one_mem _⟩
  · have hw' : w ≠ v := fun h => hv (h ▸ hw)
    exact val_localIdele_snd_of_ne K v t hw'

theorem prod_archCentralUnit_eq (x : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    ((∏ w : InfinitePlace K, archCentralUnit K w (x w) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      ((fun w => (x w : w.Completion)), 1) := by
  classical
  rw [Units.coe_prod]
  refine Prod.ext ?_ ?_
  · rw [fst_prod]
    funext w'
    rw [infAdele_prod_apply]
    rw [Finset.prod_eq_single w']
    · show Function.update (1 : InfiniteAdeleRing K) w' ((x w' : (w'.Completion)ˣ) : w'.Completion) w' = _
      rw [Function.update_self]
    · intro w _ hw
      show Function.update (1 : InfiniteAdeleRing K) w ((x w : (w.Completion)ˣ) : w.Completion) w' = 1
      rw [Function.update_of_ne (Ne.symm hw)]
      rfl
    · intro h; exact absurd (Finset.mem_univ w') h
  · rw [snd_prod]
    exact Finset.prod_eq_one fun w _ => archCentralUnit_snd w (x w)

section ProductFormula

variable (K)
variable (t : (AdeleRing (𝓞 K) K)ˣ)

def finComp (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  ⟨(t : AdeleRing (𝓞 K) K).2 v, ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v,
    snd_val_mul_inv_apply K t v, snd_val_inv_mul_apply K t v⟩

theorem fst_val_mul_inv_apply (w : InfinitePlace K) :
    (t : AdeleRing (𝓞 K) K).1 w * ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 :=
  congrArg (fun u : (AdeleRing (𝓞 K) K)ˣ => (u : AdeleRing (𝓞 K) K).1 w) (mul_inv_cancel t)

theorem fst_val_inv_mul_apply (w : InfinitePlace K) :
    ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w * (t : AdeleRing (𝓞 K) K).1 w = 1 :=
  congrArg (fun u : (AdeleRing (𝓞 K) K)ˣ => (u : AdeleRing (𝓞 K) K).1 w) (inv_mul_cancel t)

def infComp (w : InfinitePlace K) : (w.Completion)ˣ :=
  ⟨(t : AdeleRing (𝓞 K) K).1 w, ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w,
    fst_val_mul_inv_apply K t w, fst_val_inv_mul_apply K t w⟩

theorem val_finComp (v : HeightOneSpectrum (𝓞 K)) : ((finComp K t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
    (t : AdeleRing (𝓞 K) K).2 v := rfl

theorem val_finComp_inv (v : HeightOneSpectrum (𝓞 K)) :
    (((finComp K t v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v := rfl

theorem val_infComp (w : InfinitePlace K) : ((infComp K t w : (w.Completion)ˣ) : w.Completion) =
    (t : AdeleRing (𝓞 K) K).1 w := rfl

def badUnits : Finset (HeightOneSpectrum (𝓞 K)) :=
  ((Filter.eventually_cofinite.1 ((t : AdeleRing (𝓞 K) K).2).2).union
    (Filter.eventually_cofinite.1 (((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2).2)).toFinset

theorem finComp_mem_integers_of_not_mem_badUnits {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ badUnits K t) :
    ((finComp K t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      (((finComp K t v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [badUnits, Set.Finite.mem_toFinset, Set.mem_union, not_or] at hv
  simp only [Set.mem_setOf_eq, not_not] at hv
  exact ⟨hv.1, hv.2⟩

theorem apply_eq_prod {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ u : UnitPi K, (∀ v ∈ T, u v = 1) → ‖ηC η (unitIdele K u) - 1‖ < 1 / 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hTS : T ⊆ S) (haS : badUnits K t ⊆ S) :
    η t = (∏ w : InfinitePlace K, archLocalChar η w (infComp K t w)) * ∏ v ∈ S, localChar η v (finComp K t v) := by
  classical

  set A : (AdeleRing (𝓞 K) K)ˣ := ∏ w : InfinitePlace K, archCentralUnit K w (infComp K t w) with hA
  set P : (AdeleRing (𝓞 K) K)ˣ := ∏ v ∈ S, localIdele K v (finComp K t v) with hP
  set Q : (AdeleRing (𝓞 K) K)ˣ := ∏ v ∈ S, localIdele K v (finComp K t v)⁻¹ with hQ
  have hPQ : P⁻¹ = Q := by
    rw [hP, hQ, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => (map_inv (localIdele K v) _).symm
  have hQP : Q⁻¹ = P := by rw [← hPQ, inv_inv]
  set r : (AdeleRing (𝓞 K) K)ˣ := Q * A⁻¹ * t with hr
  have hdec : t = A * P * r := by
    rw [hr, ← hPQ]
    group

  have hAval : ((A : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      ((fun w => ((infComp K t w : (w.Completion)ˣ) : w.Completion)), 1) := by
    rw [hA]; exact prod_archCentralUnit_eq (fun w => infComp K t w)
  have hA2 : ∀ v : HeightOneSpectrum (𝓞 K), ((A : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := by
    intro v; rw [hAval]; rfl
  have hAi2 : ∀ v : HeightOneSpectrum (𝓞 K), ((A⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := by
    intro v
    have h := snd_val_mul_inv_apply K A v
    rwa [hA2, one_mul] at h
  have hA1 : ((A : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = ((t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 := by
    rw [hAval]; rfl

  have hr2 : ∀ v : HeightOneSpectrum (𝓞 K), (r : AdeleRing (𝓞 K) K).2 v =
      if v ∈ S then 1 else ((finComp K t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
    intro v
    rw [hr, snd_val_mul_apply, snd_val_mul_apply, hAi2, mul_one, hQ, val_prod_localIdele_snd_apply, ← val_finComp]
    split_ifs with h
    · exact Units.inv_mul _
    · exact one_mul _
  have hri2 : ∀ v : HeightOneSpectrum (𝓞 K), ((r⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v =
      if v ∈ S then 1 else (((finComp K t v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
    intro v
    have : r⁻¹ = t⁻¹ * A * P := by rw [hr, mul_inv_rev, mul_inv_rev, inv_inv, hQP, mul_assoc]
    rw [this, snd_val_mul_apply, snd_val_mul_apply, hA2, mul_one, hP, val_prod_localIdele_snd_apply, ← val_finComp_inv]
    split_ifs with h
    · exact Units.inv_mul _
    · exact mul_one _
  have hr1 : (r : AdeleRing (𝓞 K) K).1 = 1 := by
    rw [hr, fst_val_mul, fst_val_mul, hQ, val_prod_localIdele_fst, one_mul, ← hA1, ← fst_val_mul, inv_mul_cancel]
    rfl

  have hηr : η r = 1 := by
    refine apply_eq_one_of_integral η hT r hr1 (fun v => ?_) (fun v hv => ?_)
    · rw [hr2, hri2]
      by_cases h : v ∈ S
      · rw [if_pos h, if_pos h]
        exact ⟨one_mem _, one_mem _⟩
      · rw [if_neg h, if_neg h]
        exact finComp_mem_integers_of_not_mem_badUnits K t fun h' => h (haS h')
    · rw [hr2, if_pos (hTS hv)]

  have hηt : η t = η A * η P * η r := by rw [← map_mul, ← map_mul, ← hdec]
  rw [hηt, hηr, mul_one, hA, hP, map_prod, map_prod]
  rfl

end ProductFormula

section Norms

open M4aHerbrand M4aHerbrand.GenuineDescent

variable (K) (L : Type) [Field L] [NumberField L] [Algebra K L]

abbrev TA : Type := AdeleRing (𝓞 K) K ⊗[K] L

def transport : (TA K L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  letI := (genuineBaseChange K L).β.toAlgebra
  Units.map ((genuineBaseChange K L).tensorEquiv : TA K L →* AdeleRing (𝓞 L) L)

def transportInv : (AdeleRing (𝓞 L) L)ˣ →* (TA K L)ˣ :=
  letI := (genuineBaseChange K L).β.toAlgebra
  Units.map ((genuineBaseChange K L).tensorEquiv.symm : AdeleRing (𝓞 L) L →* TA K L)

theorem transport_transportInv (β : (AdeleRing (𝓞 L) L)ˣ) : transport K L (transportInv K L β) = β := by
  letI := (genuineBaseChange K L).β.toAlgebra
  refine Units.ext ?_
  show (genuineBaseChange K L).tensorEquiv ((genuineBaseChange K L).tensorEquiv.symm (β : AdeleRing (𝓞 L) L)) = β
  exact AlgEquiv.apply_symm_apply _ _

theorem val_idelicNorm_transport (T : (TA K L)ˣ) :
    (((genuineBaseChange K L).idelicNorm (transport K L T) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      Algebra.norm (AdeleRing (𝓞 K) K) (T : TA K L) := by
  letI := (genuineBaseChange K L).β.toAlgebra
  show (genuineBaseChange K L).adelicNorm ((genuineBaseChange K L).tensorEquiv (T : TA K L)) = _
  exact Algebra.norm_eq_of_algEquiv (genuineBaseChange K L).tensorEquiv (T : TA K L)

theorem finComp_idelicNorm_eq (β : (AdeleRing (𝓞 L) L)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finComp K ((genuineBaseChange K L).idelicNorm β) v =
      Units.map (Algebra.norm (v.adicCompletion K) : v.adicCompletion K ⊗[K] L →* v.adicCompletion K)
        (Units.map (Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) : TA K L →* v.adicCompletion K ⊗[K] L)
          (transportInv K L β)) := by
  refine Units.ext ?_
  rw [val_finComp, Units.coe_map, Units.coe_map]
  show _ = Algebra.norm _ (Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) (transportInv K L β : TA K L))
  rw [← map_norm_eq_norm_map, ← evF_apply K v, ← val_idelicNorm_transport, transport_transportInv]

theorem infComp_idelicNorm_eq (β : (AdeleRing (𝓞 L) L)ˣ) (w : InfinitePlace K) :
    infComp K ((genuineBaseChange K L).idelicNorm β) w =
      Units.map (Algebra.norm w.Completion : w.Completion ⊗[K] L →* w.Completion)
        (Units.map (Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) : TA K L →* w.Completion ⊗[K] L)
          (transportInv K L β)) := by
  refine Units.ext ?_
  rw [val_infComp, Units.coe_map, Units.coe_map]
  show _ = Algebra.norm _ (Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) (transportInv K L β : TA K L))
  rw [← map_norm_eq_norm_map, ← evI_apply K w, ← val_idelicNorm_transport, transport_transportInv]

end Norms

theorem ker_eq_of_index_eq_two {G : Type*} [Group G] (χ : G →* ℂˣ) (H : Subgroup G) (hidx : H.index = 2)
    (hle : H ≤ χ.ker) (hne : χ ≠ 1) : χ.ker = H := by
  have hK : χ.ker.index ∣ 2 := hidx ▸ Subgroup.index_dvd_of_le hle
  have hKtop : χ.ker ≠ ⊤ := fun h => hne (MonoidHom.ker_eq_top_iff.mp h)
  have hK2 : χ.ker.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hK with h | h
    · exact absurd (Subgroup.index_eq_one.mp h) hKtop
    · exact h
  have hrel := Subgroup.relIndex_mul_index hle
  rw [hK2, hidx] at hrel
  have hrel1 : H.relIndex χ.ker = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) hle

open scoped TensorProduct.RightActions in
theorem main (L : Type) [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2)
    (hη : IsIdeleClassChar (𝓞 K) K η) (hcont : Continuous η)
    (hne : η ≠ 1)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ),
      x ∈ (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range →
        localChar η v x = 1)
    (hinf : ∀ (w : InfinitePlace K) (x : (w.Completion)ˣ),
      x ∈ (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range →
        archLocalChar η w x = 1) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range ≠ ⊤ →
        localChar η v ≠ 1) ∧
    (∀ w : InfinitePlace K,
      (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range ≠ ⊤ →
        archLocalChar η w ≠ 1) := by
  classical
  haveI hq : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  haveI : IsMulCommutative (L ≃ₐ[K] L) := inferInstance
  set H : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
    M4aHerbrand.principalIdeles (𝓞 K) K ⊔ (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range with hH

  obtain ⟨T, hT⟩ := exists_finset_forall_norm_sub_one_lt η hcont
  have hnorm : ∀ β : (AdeleRing (𝓞 L) L)ˣ, η ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm β) = 1 := by
    intro β
    set t := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm β with ht
    rw [apply_eq_prod K η t hT (T ∪ badUnits K t) Finset.subset_union_left Finset.subset_union_right]
    have hF : ∀ v ∈ T ∪ badUnits K t, localChar η v (finComp K t v) = 1 := by
      intro v _
      refine hfin v _ ?_
      rw [ht, finComp_idelicNorm_eq]
      set z' := Units.map (Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) : TA K L →* v.adicCompletion K ⊗[K] L)
        (transportInv K L β)
      set e : v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] L ⊗[K] v.adicCompletion K :=
        TensorProduct.RightActions.Algebra.TensorProduct.comm K (v.adicCompletion K) L
      refine ⟨Units.map (e : v.adicCompletion K ⊗[K] L →* L ⊗[K] v.adicCompletion K) z', Units.ext ?_⟩
      simp only [Units.coe_map]
      exact Algebra.norm_eq_of_algEquiv e (z' : v.adicCompletion K ⊗[K] L)
    have hI : ∀ w : InfinitePlace K, archLocalChar η w (infComp K t w) = 1 := by
      intro w
      refine hinf w _ ?_
      rw [ht, infComp_idelicNorm_eq]
      set z' := Units.map (Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) : TA K L →* w.Completion ⊗[K] L)
        (transportInv K L β)
      set e : w.Completion ⊗[K] L ≃ₐ[w.Completion] L ⊗[K] w.Completion :=
        TensorProduct.RightActions.Algebra.TensorProduct.comm K w.Completion L
      refine ⟨Units.map (e : w.Completion ⊗[K] L →* L ⊗[K] w.Completion) z', Units.ext ?_⟩
      simp only [Units.coe_map]
      exact Algebra.norm_eq_of_algEquiv e (z' : w.Completion ⊗[K] L)
    rw [Finset.prod_eq_one hF, Finset.prod_eq_one (fun w _ => hI w), mul_one]

  have hle : H ≤ η.ker := by
    rw [hH, sup_le_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨u, rfl⟩
      exact hη u
    · rintro _ ⟨β, rfl⟩
      exact hnorm β

  have hidx : H.index = 2 := by
    have h1 : H.index ∣ 2 := h2 ▸ NumberField.ideleClass_normCoset_index_dvd_finrank K L
    have h2' := M4aHerbrand.ideleClass_normCoset_index_ne_zero_and_finrank_dvd K L
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L)
    rw [h2] at h2'
    exact Nat.dvd_antisymm h1 h2'.2
  have hker : η.ker = H := ker_eq_of_index_eq_two η H hidx hle hne

  obtain ⟨hcF, hcI⟩ := NumberField.exists_localIdele_not_mem_principalIdeles_sup_range_idelicNorm_of_finrank_eq_two K L h2
  refine ⟨fun v hv h1 => ?_, fun w hw h1 => ?_⟩
  · obtain ⟨x, hx⟩ := hcF v hv
    apply hx
    rw [← hH, ← hker, MonoidHom.mem_ker]
    exact (localChar_apply η v x).symm.trans (by rw [h1]; rfl)
  · obtain ⟨x, hx⟩ := hcI w hw
    apply hx
    rw [← hH, ← hker, MonoidHom.mem_ker]
    exact (archLocalChar_apply η w x).symm.trans (by rw [h1]; rfl)

end QuadLGC

end

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2)
    (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 K) K η) (hcont : Continuous η)
    (hne : η ≠ 1)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ),
      x ∈ (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range →
        localChar η v x = 1)
    (hinf : ∀ (w : InfinitePlace K) (x : (w.Completion)ˣ),
      x ∈ (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range →
        archLocalChar η w x = 1) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range ≠ ⊤ →
        localChar η v ≠ 1) ∧
    (∀ w : InfinitePlace K,
      (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range ≠ ⊤ →
        archLocalChar η w ≠ 1) :=
  QuadLGC.main η L h2 hη hcont hne hfin hinf

end S_NumberField_localChar_ne_one_of_range_norm_ne_top_of_isIdeleClassChar_of_finrank_eq_two
end P2MW
export P2MW.S_NumberField_localChar_ne_one_of_range_norm_ne_top_of_isIdeleClassChar_of_finrank_eq_two (solution)
