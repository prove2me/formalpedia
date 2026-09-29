-- Prove2me | solution 1 for ModularCurve.exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c02ce4e8-6fd5-5cc9-89d9-cccf45bc7af0

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff
import Theorems.Thm_BialgHom_exists_comp_eq_comp_of_surjective_of_ker_le
import Theorems.Thm_HopfAlgebra_exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing
import Theorems.Thm_HopfAlgebra_ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP
p2m_attr_erase "simp" "PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open ModularCurve

namespace Ws47
namespace MTASM

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section RDPL

noncomputable abbrev RD (Pl : ValuationSubring (AlgebraicClosure ℚ)) : Subring (AlgebraicClosure ℚ) :=
  Pl.toSubring ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring

variable (Pl : ValuationSubring (AlgebraicClosure ℚ))

theorem mem_Pl_of_mem_RD {x : AlgebraicClosure ℚ} (hx : x ∈ RD Pl) : x ∈ Pl := hx.1

noncomputable def inclRD : ↥(RD Pl) →+* ↥Pl where
  toFun x := ⟨x.1, mem_Pl_of_mem_RD Pl x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable scoped instance algRDPl : Algebra ↥(RD Pl) ↥Pl := (inclRD Pl).toAlgebra

theorem algebraMap_RD_Pl_apply (x : ↥(RD Pl)) : ((algebraMap ↥(RD Pl) ↥Pl x : ↥Pl) : AlgebraicClosure ℚ) = x := rfl

scoped instance towerRDPl : IsScalarTower ↥(RD Pl) ↥Pl (AlgebraicClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance faithfulRDPl : FaithfulSMul ↥(RD Pl) ↥Pl := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply Subtype.ext
  have := congrArg (fun z : ↥Pl => (z : AlgebraicClosure ℚ)) hxy
  simpa [algebraMap_RD_Pl_apply] using this

scoped instance isLocalHomRDPl : IsLocalHom (algebraMap ↥(RD Pl) ↥Pl) where
  map_nonunit x hx := by
    obtain ⟨u, hu⟩ := hx
    have hinvPl : ((u⁻¹ : (↥Pl)ˣ) : ↥Pl).1 * (x : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : ↥Pl => (z : AlgebraicClosure ℚ)) u.inv_mul
      simpa [hu, algebraMap_RD_Pl_apply] using this
    have hx0 : (x : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hinvPl; exact zero_ne_one hinvPl
    have hinv_eq : ((u⁻¹ : (↥Pl)ˣ) : ↥Pl).1 = (x : AlgebraicClosure ℚ)⁻¹ :=
      eq_inv_of_mul_eq_one_left hinvPl
    have hmemPl : (x : AlgebraicClosure ℚ)⁻¹ ∈ Pl := hinv_eq ▸ ((u⁻¹ : (↥Pl)ˣ) : ↥Pl).2
    have hmemK : (x : AlgebraicClosure ℚ)⁻¹ ∈ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring :=
      IntermediateField.inv_mem _ x.2.2
    have hmem : (x : AlgebraicClosure ℚ)⁻¹ ∈ RD Pl := ⟨hmemPl, hmemK⟩
    refine ⟨⟨x, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; exact mul_inv_cancel₀ hx0
    · apply Subtype.ext; exact inv_mul_cancel₀ hx0

section inst
variable [IsDiscreteValuationRing ↥(RD Pl)]

scoped instance flatRDPl : Module.Flat ↥(RD Pl) ↥Pl := inferInstance

scoped instance ffRDPl : Module.FaithfullyFlat ↥(RD Pl) ↥Pl := Module.FaithfullyFlat.of_flat_of_isLocalHom

end inst

theorem exists_algHom_Pl (C : Type) [CommRing C] [Algebra ↥(RD Pl) C] [Module.Finite ↥(RD Pl) C]
    (χ : C →ₐ[↥(RD Pl)] AlgebraicClosure ℚ) :
    ∃ χ' : C →ₐ[↥(RD Pl)] ↥Pl, ∀ c, ((χ' c : ↥Pl) : AlgebraicClosure ℚ) = χ c := by
  have hmem : ∀ c, χ c ∈ Pl := by
    intro c
    have hint : IsIntegral ↥(RD Pl) (χ c) := (Algebra.IsIntegral.isIntegral (R := ↥(RD Pl)) c).map χ
    have hint' : IsIntegral ↥Pl (χ c) := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥Pl) (K := AlgebraicClosure ℚ)).mp hint'
    rw [← hy]; exact y.2
  refine ⟨{ toFun := fun c => ⟨χ c, hmem c⟩, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
            commutes' := ?_ }, fun c => rfl⟩
  · apply Subtype.ext; simp
  · intro a b; apply Subtype.ext; simp
  · apply Subtype.ext; simp
  · intro a b; apply Subtype.ext; simp
  · intro r; apply Subtype.ext; simp [algebraMap_RD_Pl_apply]; rfl

theorem red_translate (C : Type) [CommRing C] [HopfAlgebra ↥(RD Pl) C] [Module.Finite ↥(RD Pl) C]
    (hred : ∀ (χ : C →ₐ[↥(RD Pl)] ↥Pl) (c : C),
      χ c - algebraMap ↥(RD Pl) ↥Pl (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal ↥Pl)
    (χ : C →ₐ[↥(RD Pl)] AlgebraicClosure ℚ) (c : C) :
    Pl.valuation (χ c - algebraMap ↥(RD Pl) (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1 := by
  obtain ⟨χ', hχ'⟩ := exists_algHom_Pl Pl C χ
  have h := (ValuationSubring.valuation_lt_one_iff Pl _).mp (hred χ' c)
  convert h using 2
  rw [← hχ' c]
  rfl

end RDPL

theorem ringHom_subring_rat_apply (S : Subring ℚ) {L : Type*} [Field L] [CharZero L] (f : ↥S →+* L) (x : ↥S) :
    f x = ((x : ℚ) : L) := by
  set q : ℚ := (x : ℚ) with hq
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hS : x * (⟨(q.den : ℚ), natCast_mem S q.den⟩ : ↥S) = ⟨(q.num : ℚ), intCast_mem S q.num⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_mul]
    rw [← hq]
    exact Rat.mul_den_eq_num q
  have h1 : f x * (q.den : L) = (q.num : L) := by
    have := congr_arg f hS
    rw [map_mul] at this
    have e1 : f ⟨(q.den : ℚ), natCast_mem S q.den⟩ = (q.den : L) := by
      rw [← map_natCast f q.den]; rfl
    have e2 : f ⟨(q.num : ℚ), intCast_mem S q.num⟩ = (q.num : L) := by
      rw [← map_intCast f q.num]; rfl
    rw [e1] at this; rw [this, e2]
  have hdenL : (q.den : L) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [eq_div_iff hdenL |>.mpr h1 |> fun h => h, Rat.cast_def]

theorem ringHom_ratLocalizedAt_ext (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (f g : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl) : f = g := by
  apply RingHom.ext
  intro x
  apply Subtype.val_injective
  have hf := ringHom_subring_rat_apply (GaloisRep.ratLocalizedAt p) (Pl.subtype.comp f) x
  have hg := ringHom_subring_rat_apply (GaloisRep.ratLocalizedAt p) (Pl.subtype.comp g) x
  simp only [RingHom.coe_comp, Function.comp_apply] at hf hg
  exact hf.trans hg.symm

section SIGMA

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)}

theorem sigmaA_eq_specMap (Λ : JHNeronObjectAtP.LevelData p M H hpM Pl) (τ : XHDRLevel.R p →+* ↥Pl) :
    Λ.σA = Spec.map (CommRingCat.ofHom τ) := by
  obtain ⟨σ, hσ⟩ := Spec.map_surjective Λ.σA
  rw [← hσ]
  congr 1
  have : σ.hom = τ := ringHom_ratLocalizedAt_ext p Pl σ.hom τ
  rw [← CommRingCat.ofHom_hom σ, this]

end SIGMA

section BCLIFT

variable {R : Type} [CommRing R] (K : Type) [CommRing K] [Algebra R K]
  {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R))
  (A₁ : Type) [CommRing A₁] [Algebra R A₁]

noncomputable def bcLift (i₁ : Spec (CommRingCat.of A₁) ⟶ Y)
    (h₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₁))) :
    Spec (CommRingCat.of (K ⊗[R] A₁)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i₁)
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A₁)))
    (by
      rw [Category.assoc, h₁, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      change (1 : K) ⊗ₜ[R] algebraMap R A₁ r = algebraMap R K r ⊗ₜ[R] (1 : A₁)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul'])

variable {K f A₁}

@[reassoc (attr := simp)]
theorem bcLift_fst (i₁ : Spec (CommRingCat.of A₁) ⟶ Y) (h₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₁))) :
    bcLift K f A₁ i₁ h₁ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcLift_snd (i₁ : Spec (CommRingCat.of A₁) ⟶ Y) (h₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₁))) :
    bcLift K f A₁ i₁ h₁ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A₁)) :=
  pullback.lift_snd _ _ _

theorem isPullback_bcLift (i₁ : Spec (CommRingCat.of A₁) ⟶ Y) (h₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₁))) :
    IsPullback (bcLift K f A₁ i₁ h₁)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)))
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) i₁ := by
  refine IsPullback.of_right ?_ (bcLift_fst i₁ h₁) (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).flip
  rw [bcLift_snd, h₁]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K A₁)

theorem isClosedImmersion_bcLift (i₁ : Spec (CommRingCat.of A₁) ⟶ Y)
    (h₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₁))) [IsClosedImmersion i₁] :
    IsClosedImmersion (bcLift K f A₁ i₁ h₁) :=
  MorphismProperty.of_isPullback (isPullback_bcLift i₁ h₁).flip ‹_›

end BCLIFT

section IB

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl} (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh ↥Pl] (ρh : XHDRLevel.R p →+* Rh)
  {C K₁ : Type} [CommRing C] [CommRing K₁] [Algebra Rh C] [Algebra Rh K₁] (q : C →ₐ[Rh] K₁)
  (ι₁ : Spec (CommRingCat.of C) ⟶ O.G)
  (hιbase₁ : ι₁ ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh C)) ≫ Spec.map (CommRingCat.ofHom ρh))

noncomputable def jRh : Spec (CommRingCat.of C) ⟶ pullback O.g (Spec.map (CommRingCat.ofHom ρh)) :=
  pullback.lift ι₁ (Spec.map (CommRingCat.ofHom (algebraMap Rh C))) hιbase₁

noncomputable def iRh : Spec (CommRingCat.of K₁) ⟶ pullback O.g (Spec.map (CommRingCat.ofHom ρh)) :=
  Spec.map (CommRingCat.ofHom (q : C →+* K₁)) ≫ jRh O ρh ι₁ hιbase₁

theorem iRh_snd : iRh O ρh q ι₁ hιbase₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap Rh K₁)) := by
  rw [iRh, jRh, Category.assoc, pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact q.comp_algebraMap

theorem iRh_fst : iRh O ρh q ι₁ hιbase₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (q : C →+* K₁)) ≫ ι₁ := by
  rw [iRh, jRh, Category.assoc, pullback.lift_fst]

theorem specMap_algebraMap_comp_eq_sigmaA :
    Spec.map (CommRingCat.ofHom (algebraMap Rh ↥Pl)) ≫ Spec.map (CommRingCat.ofHom ρh) = Λ.σA := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, sigmaA_eq_specMap Λ ((algebraMap Rh ↥Pl).comp ρh)]

noncomputable def iB : Spec (CommRingCat.of (↥Pl ⊗[Rh] K₁)) ⟶ pullback O.g Λ.σA :=
  bcLift ↥Pl (pullback.snd O.g (Spec.map (CommRingCat.ofHom ρh))) K₁ (iRh O ρh q ι₁ hιbase₁) (iRh_snd O ρh q ι₁ hιbase₁) ≫
    (pullbackLeftPullbackSndIso O.g (Spec.map (CommRingCat.ofHom ρh)) (Spec.map (CommRingCat.ofHom (algebraMap Rh ↥Pl)))).hom ≫
      (pullback.congrHom rfl (specMap_algebraMap_comp_eq_sigmaA (Λ := Λ) ρh)).hom

theorem iB_snd : iB O ρh q ι₁ hιbase₁ ≫ pullback.snd O.g Λ.σA =
    Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (↥Pl ⊗[Rh] K₁))) := by
  rw [iB, Category.assoc, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd, bcLift_snd]

theorem iB_fst : iB O ρh q ι₁ hιbase₁ ≫ pullback.fst O.g Λ.σA =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : K₁ →+* ↥Pl ⊗[Rh] K₁)) ≫
      Spec.map (CommRingCat.ofHom (q : C →+* K₁)) ≫ ι₁ := by
  rw [iB, Category.assoc, Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst, bcLift_fst_assoc, iRh_fst]

theorem isClosedImmersion_iB (hq : Function.Surjective q)
    (hιcl₁ : IsClosedImmersion (jRh O ρh ι₁ hιbase₁)) : IsClosedImmersion (iB O ρh q ι₁ hιbase₁) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (q : C →+* K₁))) :=
    IsClosedImmersion.spec_of_surjective _ hq
  haveI : IsClosedImmersion (iRh O ρh q ι₁ hιbase₁) := by
    rw [iRh]; infer_instance
  haveI := isClosedImmersion_bcLift (K := ↥Pl) (f := pullback.snd O.g (Spec.map (CommRingCat.ofHom ρh)))
    (iRh O ρh q ι₁ hιbase₁) (iRh_snd O ρh q ι₁ hιbase₁)
  rw [iB]
  infer_instance

noncomputable def iOver : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (↥Pl ⊗[Rh] K₁))))
    (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
  ⟨iB O ρh q ι₁ hιbase₁, iB_snd O ρh q ι₁ hιbase₁⟩

end IB

section CONV

variable {R S L : Type*} [CommRing R] [CommRing S] [CommRing L] [Algebra R S] [Algebra S L] [Algebra R L]
  [IsScalarTower R S L] {C : Type*} [CommRing C] [Bialgebra R C]

def resPt (η : S ⊗[R] C →ₐ[S] L) : C →ₐ[R] L := (η.restrictScalars R).comp Algebra.TensorProduct.includeRight

@[scoped simp] theorem resPt_apply (η : S ⊗[R] C →ₐ[S] L) (c : C) : resPt η c = η (1 ⊗ₜ c) := rfl

theorem resPt_convMul (χ χ' : WithConv (S ⊗[R] C →ₐ[S] L)) :
    resPt (χ * χ').ofConv = (WithConv.toConv (resPt χ.ofConv) * WithConv.toConv (resPt χ'.ofConv)).ofConv := by
  apply AlgHom.ext
  intro c
  let 𝓡 := Coalgebra.Repr.arbitrary R c
  have hc : Coalgebra.comul (R := R) c = 𝓡.index.sum fun i => 𝓡.left i ⊗ₜ[R] 𝓡.right i := 𝓡.eq.symm
  simp only [resPt_apply, AlgHom.convMul_def, WithConv.ofConv_toConv, AlgHom.coe_comp, Function.comp_apply,
    Bialgebra.comulAlgHom_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply, hc, TensorProduct.tmul_sum,
    map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lmul'_apply_tmul, resPt_apply]

theorem resPt_lift (χ₀ : C →ₐ[R] L) :
    resPt (Algebra.TensorProduct.lift (Algebra.ofId S L) χ₀ (fun _ _ => .all _ _)) = χ₀ := by
  apply AlgHom.ext
  intro c
  simp [resPt_apply, Algebra.TensorProduct.lift_tmul]

theorem coe_resPt (η : S ⊗[R] C →ₐ[S] L) :
    (resPt η : C →+* L) = (η : S ⊗[R] C →+* L).comp (Algebra.TensorProduct.includeRight.toRingHom : C →+* S ⊗[R] C) := rfl

end CONV

section NAT

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl} (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh ↥Pl] (ρh : XHDRLevel.R p →+* Rh)
  {C K₁ K₂ : Type} [CommRing C] [CommRing K₁] [CommRing K₂] [Algebra Rh C] [Algebra Rh K₁] [Algebra Rh K₂]

theorem specMap_map_comp_iB (q : C →ₐ[Rh] K₁) (r : K₁ →ₐ[Rh] K₂)
    (ι₁ : Spec (CommRingCat.of C) ⟶ O.G)
    (hιbase₁ : ι₁ ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh C)) ≫ Spec.map (CommRingCat.ofHom ρh)) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id ↥Pl ↥Pl) r : ↥Pl ⊗[Rh] K₁ →+* ↥Pl ⊗[Rh] K₂)) ≫
        iB O ρh q ι₁ hιbase₁ = iB O ρh (r.comp q) ι₁ hιbase₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, iB_fst, iB_fst, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
  · rw [Category.assoc, iB_snd, iB_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change (Algebra.TensorProduct.map (AlgHom.id ↥Pl ↥Pl) r) (a ⊗ₜ[Rh] (1 : K₁)) = a ⊗ₜ[Rh] (1 : K₂)
    simp [Algebra.TensorProduct.map_tmul]

theorem iB_comp_transition {C' : Type} [CommRing C'] [Algebra Rh C'] (q : C →ₐ[Rh] K₁) (u : C' →ₐ[Rh] C)
    (ι₁ : Spec (CommRingCat.of C) ⟶ O.G)
    (hιbase₁ : ι₁ ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh C)) ≫ Spec.map (CommRingCat.ofHom ρh))
    (ι' : Spec (CommRingCat.of C') ⟶ O.G)
    (hιbase' : ι' ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh C')) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hu : Spec.map (CommRingCat.ofHom (u : C' →+* C)) ≫ ι' = ι₁) :
    iB O ρh (q.comp u) ι' hιbase' = iB O ρh q ι₁ hιbase₁ := by
  apply pullback.hom_ext
  · rw [iB_fst, iB_fst, ← hu]
    simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
  · rw [iB_snd, iB_snd]

end NAT

section FRAMEPTS

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl} (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh (AlgebraicClosure ℚ)] [Algebra Rh ↥Pl]
  [IsScalarTower Rh ↥Pl (AlgebraicClosure ℚ)]
  (ρh : XHDRLevel.R p →+* Rh)
  (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
  {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  (v : ℕ) {K₁ : Type} [CommRing K₁] [HopfAlgebra Rh K₁] (q : 𝒢.level v →ₐc[Rh] K₁)

noncomputable abbrev sRh : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ JZeroNeronObjectAtP.base p :=
  Spec.map (CommRingCat.ofHom (algebraMap Rh (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom ρh)

include hρh in
theorem barPt_comp_sigmaA_eq_sRh : JZeroNeronObjectAtP.barPt Pl ≫ Λ.σA = sRh (p := p) ρh := by
  rw [Λ.hσA, sRh, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρh]

noncomputable def ptOf (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) : 𝒢.Point (AlgebraicClosure ℚ) v :=
  PDivisibleGroup.Point.ofAlgHom ((resPt η).comp (q : 𝒢.level v →ₐ[Rh] K₁))

theorem toAlgHom_ptOf (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) :
    PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 v q η) = (resPt η).comp (q : 𝒢.level v →ₐ[Rh] K₁) := rfl

theorem specMap_comp_iB_fst (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (η : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫ iB O ρh (q : 𝒢.level v →ₐ[Rh] K₁) (ι v) (hιbase v) ≫
        pullback.fst O.g Λ.σA =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 v q η) : 𝒢.level v →ₐ[Rh] AlgebraicClosure ℚ) :
        𝒢.level v →+* AlgebraicClosure ℚ)) ≫ ι v := by
  rw [iB_fst, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

variable (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
    (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) :
        𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
  (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
    (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g =
      (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
    (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g =
      (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
      (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
  (hqpts : ∀ x : 𝒢.Point (AlgebraicClosure ℚ) v,
    (∃ χ₀ : K₁ →ₐ[Rh] AlgebraicClosure ℚ, χ₀.comp (q : 𝒢.level v →ₐ[Rh] K₁) = PDivisibleGroup.Point.toAlgHom x) ↔
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
  (htor : ∀ y : ModularCurve.JH M H, y ∈ O.toricPts (p ^ v) →
    ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)

theorem mul_castOver_val {T : Scheme.{0}} {s₁ s₂ : T ⟶ JZeroNeronObjectAtP.base p} (hs : s₁ = s₂) (a b : SchemeHomOver s₁ O.g) :
    (O.L.mul s₂ (JZeroNeronObjectAtP.castOver hs a) (JZeroNeronObjectAtP.castOver hs b)).1 = (O.L.mul s₁ a b).1 := by
  subst hs
  rfl

include hρh hιmul in

theorem hmul_iB (χ χ' : WithConv (↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ))
    (x x' xx' : SchemeHomOver (JZeroNeronObjectAtP.barPt Pl) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hx : x.1 = Spec.map (CommRingCat.ofHom (χ.ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level v →ₐ[Rh] K₁) (ι v) (hιbase v)).1)
    (hx' : x'.1 = Spec.map (CommRingCat.ofHom (χ'.ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level v →ₐ[Rh] K₁) (ι v) (hιbase v)).1)
    (hxx' : xx'.1 = Spec.map (CommRingCat.ofHom ((χ * χ').ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level v →ₐ[Rh] K₁) (ι v) (hιbase v)).1) :
    xx' = (O.L.baseChange Λ.σA).mul (JZeroNeronObjectAtP.barPt Pl) x x' := by
  have hs := barPt_comp_sigmaA_eq_sRh (Λ := Λ) ρh hρh

  have kx : x.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 v q χ.ofConv) :
      𝒢.level v →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level v →+* AlgebraicClosure ℚ)) ≫ ι v := by
    rw [hx, Category.assoc]; exact specMap_comp_iB_fst O ρh 𝒢 ι hιbase v q χ.ofConv
  have kx' : x'.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 v q χ'.ofConv) :
      𝒢.level v →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level v →+* AlgebraicClosure ℚ)) ≫ ι v := by
    rw [hx', Category.assoc]; exact specMap_comp_iB_fst O ρh 𝒢 ι hιbase v q χ'.ofConv
  have kxx' : xx'.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 v q (χ * χ').ofConv) :
      𝒢.level v →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level v →+* AlgebraicClosure ℚ)) ≫ ι v := by
    rw [hxx', Category.assoc]; exact specMap_comp_iB_fst O ρh 𝒢 ι hιbase v q (χ * χ').ofConv

  have hover : ∀ z : SchemeHomOver (JZeroNeronObjectAtP.barPt Pl) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
      (z.1 ≫ pullback.fst O.g Λ.σA) ≫ O.g = sRh (p := p) ρh := by
    intro z
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, hs]
  have hX := hover x; rw [kx] at hX
  have hX' := hover x'; rw [kx'] at hX'

  have hmulpt : ptOf 𝒢 v q (χ * χ').ofConv = ptOf 𝒢 v q χ.ofConv * ptOf 𝒢 v q χ'.ofConv := by
    apply PDivisibleGroup.Point.ext
    intro a
    change ((resPt (χ * χ').ofConv).comp (q : 𝒢.level v →ₐ[Rh] K₁)) a =
      PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 v q χ.ofConv * ptOf 𝒢 v q χ'.ofConv) a
    rw [resPt_convMul, AlgHom.convMul_comp_bialgHom_distrib]
    rfl
  have H := hιmul v (AlgebraicClosure ℚ) (ptOf 𝒢 v q χ.ofConv) (ptOf 𝒢 v q χ'.ofConv) hX hX'
  rw [← hmulpt, ← kxx'] at H

  apply Subtype.ext
  apply pullback.hom_ext
  · rw [H]
    have e1 : (⟨_, hX⟩ : SchemeHomOver (sRh (p := p) ρh) O.g) =
        JZeroNeronObjectAtP.castOver hs (RelativeGroupLaw.baseChangePointToBase Λ.σA x) := Subtype.ext kx.symm
    have e2 : (⟨_, hX'⟩ : SchemeHomOver (sRh (p := p) ρh) O.g) =
        JZeroNeronObjectAtP.castOver hs (RelativeGroupLaw.baseChangePointToBase Λ.σA x') := Subtype.ext kx'.symm
    rw [e1, e2, mul_castOver_val O hs]
    change _ = ((O.L.baseChange Λ.σA).mul (JZeroNeronObjectAtP.barPt Pl) x x').1 ≫ pullback.fst O.g Λ.σA
    rw [← RelativeGroupLaw.baseChangePointToBase_coe]
    change _ = (RelativeGroupLaw.baseChangePointToBase Λ.σA (RelativeGroupLaw.baseChangePointOfBase Λ.σA
      (O.L.mul _ (RelativeGroupLaw.baseChangePointToBase Λ.σA x) (RelativeGroupLaw.baseChangePointToBase Λ.σA x')))).1
    rw [RelativeGroupLaw.baseChangePointToBase_ofBase]
  · rw [xx'.2, ((O.L.baseChange Λ.σA).mul (JZeroNeronObjectAtP.barPt Pl) x x').2]

include hιpts hqpts htor in

theorem hpts_iB (y : JH M H) :
    y ∈ O.toricPts (p ^ v) ↔ ∃ χ : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ,
      (O.pts y).1 = Spec.map (CommRingCat.ofHom (χ : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
        (iOver O ρh (q : 𝒢.level v →ₐ[Rh] K₁) (ι v) (hιbase v)).1 ≫ pullback.fst O.g Λ.σA := by
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := htor y hy
    obtain ⟨χ₀, hχ₀⟩ := (hqpts x).mpr hy
    refine ⟨Algebra.TensorProduct.lift (Algebra.ofId ↥Pl (AlgebraicClosure ℚ)) χ₀ (fun _ _ => .all _ _), ?_⟩
    rw [hιpts]
    change _ = _ ≫ iB O ρh (q : 𝒢.level v →ₐ[Rh] K₁) (ι v) (hιbase v) ≫ _
    rw [specMap_comp_iB_fst O ρh 𝒢 ι hιbase v q, toAlgHom_ptOf, resPt_lift, hχ₀]
  · rintro ⟨χ, hχ⟩
    change _ = _ ≫ iB O ρh (q : 𝒢.level v →ₐ[Rh] K₁) (ι v) (hιbase v) ≫ _ at hχ
    rw [specMap_comp_iB_fst O ρh 𝒢 ι hιbase v q] at hχ
    have hmem : Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (ptOf 𝒢 v q χ))) ∈ O.toricPts (p ^ v) :=
      (hqpts _).mp ⟨resPt χ, rfl⟩
    have hyx : y = Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (ptOf 𝒢 v q χ))) := by
      apply O.pts.injective
      apply Subtype.ext
      rw [hχ, hιpts]
    rwa [hyx]

end FRAMEPTS

end Ws47.MTASM
p2m_reactivate "P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP.Ws47 P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP.Ws47.MTASM"
p2m_reactivate "P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP.Ws47"

namespace Ws47
namespace MTH3

theorem castPi_surjective (p : ℕ) [Fact p.Prime] (t v : ℕ) :
    Function.Surjective
      (AddMonoidHom.pi fun k : Fin t =>
            ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v))).toAddMonoidHom.comp
              (Pi.evalAddMonoidHom (fun _ => ZMod (p ^ (v + 1))) k))) := by
  intro g
  choose y hy using fun k => ZMod.ringHom_surjective (ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v))) (g k)
  refine ⟨y, funext fun k => ?_⟩
  rw [AddMonoidHom.pi_apply]
  exact hy k

theorem castPi_eq_zero_iff (p : ℕ) [Fact p.Prime] (t v : ℕ) (x : Fin t → ZMod (p ^ (v + 1))) :
    (AddMonoidHom.pi fun k : Fin t =>
            ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v))).toAddMonoidHom.comp
              (Pi.evalAddMonoidHom (fun _ => ZMod (p ^ (v + 1))) k))) x = 0 ↔ ∃ y : Fin t → ZMod (p ^ (v + 1)), x = (p ^ v) • y := by
  constructor
  · intro hx
    have hk : ∀ k, ∃ b : ZMod (p ^ (v + 1)), x k = (p ^ v) • b := by
      intro k
      have h0 := congr_fun hx k
      rw [AddMonoidHom.pi_apply, Pi.zero_apply] at h0
      change ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v)) (x k) = 0 at h0
      rw [ZMod.castHom_apply, ← ZMod.natCast_val, CharP.cast_eq_zero_iff (ZMod (p ^ v)) (p ^ v)] at h0
      obtain ⟨c, hc⟩ := h0
      refine ⟨(c : ZMod (p ^ (v + 1))), ?_⟩
      rw [← ZMod.natCast_zmod_val (x k), hc, Nat.cast_mul, nsmul_eq_mul]
    choose y hy using hk
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩
    rw [map_nsmul]
    funext k
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end Ws47.MTH3
p2m_reactivate "P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP.Ws47 P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP.Ws47.MTASM"
p2m_reactivate "P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP.Ws47 P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP.Ws47.MTASM"

theorem Ws47.MTASM.hopf_assembly
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra R (ZMod p)]
    (hres : ∀ x : R, algebraMap R (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Module.Flat R A] [FaithfulSMul R A] [CharP (IsLocalRing.ResidueField A) p]
    {h : ℕ} (G : PDivisibleGroup R p h)
    (C : ℕ → Type) [∀ v, CommRing (C v)] [∀ v, HopfAlgebra R (C v)] [∀ v, Coalgebra.IsCocomm R (C v)]
    [∀ v, Module.Finite R (C v)] [∀ v, Module.Free R (C v)]
    (π : ∀ v : ℕ, G.level v →ₐc[R] C v) (hπ : ∀ v, Function.Surjective (π v))
    (t : ℕ)
    (e : ∀ v : ℕ, A ⊗[R] C v ≃ₐc[A] AddMonoidAlgebra A (Fin t → ZMod (p ^ v)))
    (hcompat : ∀ (v : ℕ) (w : A ⊗[R] G.level (v + 1)),
      e v (Algebra.TensorProduct.map (AlgHom.id A A)
            (((π v).comp (G.transition v) : G.level (v + 1) →ₐc[R] C v) : G.level (v + 1) →ₐ[R] C v) w) =
        AddMonoidAlgebra.mapDomainBialgHom A
          (AddMonoidHom.pi fun k : Fin t =>
            ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v))).toAddMonoidHom.comp
              (Pi.evalAddMonoidHom (fun _ => ZMod (p ^ (v + 1))) k)))
          (e (v + 1) (Algebra.TensorProduct.map (AlgHom.id A A) (π (v + 1) : G.level (v + 1) →ₐ[R] C (v + 1)) w))) :
    (∀ v : ℕ, ∃ Ver : ZMod p ⊗[R] C v ≃ₐc[ZMod p] ZMod p ⊗[R] C v,
      ∀ χ : CartierDual (ZMod p) (ZMod p ⊗[R] C v),
        CartierDual.map (Ver : ZMod p ⊗[R] C v →ₐc[ZMod p] ZMod p ⊗[R] C v) χ = χ ^ p) ∧
    (∀ (v : ℕ) (χ : C v →ₐ[R] A) (c : C v), χ c - algebraMap R A (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal A) ∧
    (∃ tC : ∀ v : ℕ, C (v + 1) →ₐc[R] C v,
      (∀ v, Function.Surjective (tC v)) ∧
      (∀ v : ℕ, (tC v).comp (π (v + 1)) = (π v).comp (G.transition v)) ∧
      (∀ v, RingHom.ker (tC v) = PDivisibleGroup.Hopf.torsionIdeal R (C (v + 1)) (p ^ v)) ∧
      (∀ v, Module.finrank R (C v) = p ^ (v * t))) := by
  haveI : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hcard : ∀ v : ℕ, Fintype.card (Fin t → ZMod (p ^ v)) = p ^ (v * t) := by
    intro v
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, pow_mul]
  have hMT := fun v : ℕ =>
    HopfAlgebra.exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing
      p hres A (C v) (Fin t → ZMod (p ^ v)) (v * t) (hcard v) (e v)
  refine ⟨fun v => (hMT v).1, fun v => (hMT v).2.1, ?_⟩

  have hker0 : ∀ (v : ℕ) (x : G.level (v + 1)), π (v + 1) x = 0 → π v (G.transition v x) = 0 := by
    intro v x hx
    have h := hcompat v ((1 : A) ⊗ₜ[R] x)
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at h
    have h2 : ((π (v + 1) : G.level (v + 1) →ₐ[R] C (v + 1)) x) = 0 := hx
    rw [h2, TensorProduct.tmul_zero, map_zero, map_zero] at h
    have h3 : (AlgHom.id A A) 1 ⊗ₜ[R] ((π v).comp (G.transition v) : G.level (v + 1) →ₐ[R] C v) x = 0 :=
      (e v).injective (h.trans (map_zero (e v)).symm)
    have hinj := Algebra.TensorProduct.includeRight_injective (R := R) (A := A) (B := C v)
      (FaithfulSMul.algebraMap_injective R A)
    apply hinj
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_zero]
    exact h3
  have hex := fun v : ℕ => BialgHom.exists_comp_eq_comp_of_surjective_of_ker_le (π v) (π (v + 1)) (hπ (v + 1))
    (G.transition v) (hker0 v)
  choose tC htC hsurjC using hex
  have hsurj : ∀ v, Function.Surjective (tC v) := fun v => hsurjC v (hπ v) (G.transition_surjective v)
  refine ⟨tC, hsurj, htC, ?_, fun v => by rw [(hMT v).2.2.1, hcard]⟩
  intro v

  have hms : ∀ z : A ⊗[R] C (v + 1), ∃ w : A ⊗[R] G.level (v + 1),
      Algebra.TensorProduct.map (AlgHom.id A A) (π (v + 1) : G.level (v + 1) →ₐ[R] C (v + 1)) w = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a c =>
      obtain ⟨x, rfl⟩ := hπ (v + 1) c
      exact ⟨a ⊗ₜ[R] x, by rw [Algebra.TensorProduct.map_tmul]; rfl⟩
    | add x y hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ + w₂, map_add _ _ _⟩
  have hte : ∀ z : A ⊗[R] C (v + 1),
      e v (Algebra.TensorProduct.map (AlgHom.id A A) (tC v : C (v + 1) →ₐ[R] C v) z) =
        AddMonoidAlgebra.mapDomainBialgHom A
          (AddMonoidHom.pi fun k : Fin t =>
            ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v))).toAddMonoidHom.comp
              (Pi.evalAddMonoidHom (fun _ => ZMod (p ^ (v + 1))) k)))
          (e (v + 1) z) := by
    intro z
    obtain ⟨w, rfl⟩ := hms z
    rw [← hcompat v w]
    congr 1
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      change a ⊗ₜ[R] tC v (π (v + 1) x) = a ⊗ₜ[R] π v (G.transition v x)
      rw [← BialgHom.comp_apply, htC v, BialgHom.comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact HopfAlgebra.ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective p A (C v) (C (v + 1))
    (Fin t → ZMod (p ^ v)) (Fin t → ZMod (p ^ (v + 1))) (e v) (e (v + 1)) v
    (AddMonoidHom.pi fun k : Fin t =>
            ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v))).toAddMonoidHom.comp
              (Pi.evalAddMonoidHom (fun _ => ZMod (p ^ (v + 1))) k)))
    (Ws47.MTH3.castPi_surjective p t v) (Ws47.MTH3.castPi_eq_zero_iff p t v) (tC v) (hsurj v) hte

open ModularCurve in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    [IsDiscreteValuationRing ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)]

    {h : ℕ} (𝒢D : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p h)
    (ΔD : 𝒢D.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔDinj : Function.Injective ΔD)
    (hΔDlev : ∀ (v : ℕ) (x : ModularCurve.JH M H),
      (∃ y : 𝒢D.Point (AlgebraicClosure ℚ) v, ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = x) ↔ x ∈ O.finPts (p ^ v))
    (hΔDgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → ∀ z : 𝒢D.Points (AlgebraicClosure ℚ), ΔD (τ' • z) = τ • ΔD z)
    (htorD : ∀ v : ℕ, O.toricPts (p ^ v) ≤ O.finPts (p ^ v))

    (ρD : ModularCurve.XHDRLevel.R p →+* (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)))
    (ιD : ∀ v : ℕ, Spec (CommRingCat.of (𝒢D.level v)) ⟶ O.G)
    (hρD : (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (AlgebraicClosure ℚ)).comp ρD = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιDbase : ∀ v : ℕ, ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD))
    (hιDcl : ∀ (v : ℕ) (h1 : ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρD)) (ιD v)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h1))
    (hιDp : ∀ v : ℕ, ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιDmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B] (x y : 𝒢D.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιDt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢D.transition v : 𝒢D.level (v + 1) →+* 𝒢D.level v)) ≫ ιD (v + 1) = ιD v)
    (hιDfin : ∀ (v : ℕ)
      (h3 : ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρD))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρD))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρD))).base x = IsLocalRing.closedPoint (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) →
          x ∈ Set.range jv.base)

    (hιDpts : ∀ (v : ℕ) (x : 𝒢D.Point (AlgebraicClosure ℚ) v),
      (O.pts (ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] (AlgebraicClosure ℚ)) : 𝒢D.level v →+* (AlgebraicClosure ℚ))) ≫ ιD v)

    [Algebra ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (ZMod p)]
    (hresD : ∀ x : ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring), algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))

    (C : ℕ → Type) [∀ v, CommRing (C v)] [∀ v, HopfAlgebra ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v)]
    [∀ v, Coalgebra.IsCocomm ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v)] [∀ v, Module.Finite ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v)] [∀ v, Module.Free ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v)]
    (π : ∀ v : ℕ, 𝒢D.level v →ₐc[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v)
    (hπ : ∀ v, Function.Surjective (π v))
    (hπpts : ∀ (v : ℕ) (x : 𝒢D.Point (AlgebraicClosure ℚ) v),
      (∃ χ : C v →ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ, χ.comp (π v : 𝒢D.level v →ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v) = PDivisibleGroup.Point.toAlgHom x) ↔
      ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    :

    (∀ v : ℕ, ∃ Ver : ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v ≃ₐc[ZMod p] ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v,
      ∀ χ : CartierDual (ZMod p) (ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v), CartierDual.map (Ver : ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v →ₐc[ZMod p] ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v) χ = χ ^ p) ∧

    (∀ (v : ℕ) (χ : C v →ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ) (c : C v),
      Pl.valuation (χ c - algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1) ∧

    (∃ tC : ∀ v : ℕ, C (v + 1) →ₐc[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v,
      (∀ v, Function.Surjective (tC v)) ∧
      (∀ v : ℕ, (tC v).comp (π (v + 1)) = (π v).comp (𝒢D.transition v)) ∧
      (∀ v, RingHom.ker (tC v) = PDivisibleGroup.Hopf.torsionIdeal ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C (v + 1)) (p ^ v)) ∧
      (∀ v, Module.finrank ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v) = p ^ (v * O.toricRank))) := by
  classical
  haveI : Module.FaithfullyFlat ↥(Ws47.MTASM.RD Pl) ↥Pl := Ws47.MTASM.ffRDPl Pl
  have hp : 0 < p := Nat.Prime.pos Fact.out

  have htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢D.Point (AlgebraicClosure ℚ) v, ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y :=
    fun v y hy => (hΔDlev v y).mpr (htorD v hy)

  have key : ∀ v : ℕ, ∃ e : ↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] C v ≃ₐc[↥Pl] AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod (p ^ v)),
      Spec.map (CommRingCat.ofHom ((e.symm : AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod (p ^ v)) →ₐc[↥Pl] ↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] C v) :
          AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod (p ^ v)) →+* ↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] C v)) ≫ (O.toricLift (p ^ v) (pow_pos hp v)).1 =
        (Ws47.MTASM.iOver O ρD (π v : 𝒢D.level v →ₐ[↥(Ws47.MTASM.RD Pl)] C v) (ιD v) (hιDbase v)).1 ∧
      ∀ (m' : ℕ) (hm' : 0 < m') (hmm' : p ^ v ∣ m')
        (B' : Type) [CommRing B'] [Bialgebra ↥Pl B'] (e' : B' ≃ₐc[↥Pl] AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m'))
        (D : Type) [CommRing D] [Algebra ↥Pl D] (j : Spec (CommRingCat.of D) ⟶ pullback O.g Λ.σA) [Mono j]
        (a : D →ₐ[↥Pl] ↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] C v) (a' : D →ₐ[↥Pl] B'),
        Spec.map (CommRingCat.ofHom (a : D →+* ↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] C v)) ≫ j =
          (Ws47.MTASM.iOver O ρD (π v : 𝒢D.level v →ₐ[↥(Ws47.MTASM.RD Pl)] C v) (ιD v) (hιDbase v)).1 →
        Spec.map (CommRingCat.ofHom (a' : D →+* B')) ≫ j =
          Spec.map (CommRingCat.ofHom ((e'.symm : AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m') →ₐc[↥Pl] B') :
            AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m') →+* B')) ≫ (O.toricLift m' hm').1 →
        ∀ z : D, e (a z) =
          AddMonoidAlgebra.mapDomainBialgHom ↥Pl
            (AddMonoidHom.pi fun k : Fin O.toricRank =>
              ((ZMod.castHom hmm' (ZMod (p ^ v))).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ => ZMod m') k)))
            (e' (a' z)) := by
    intro v
    have hcl : IsClosedImmersion (Ws47.MTASM.iOver O ρD (π v : 𝒢D.level v →ₐ[↥(Ws47.MTASM.RD Pl)] C v) (ιD v) (hιDbase v)).1 :=
      Ws47.MTASM.isClosedImmersion_iB O ρD (π v : 𝒢D.level v →ₐ[↥(Ws47.MTASM.RD Pl)] C v) (ιD v) (hιDbase v) (hπ v)
        (hιDcl v (hιDbase v))
    exact ModularCurve.JHNeronObjectAtP.exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff
      p M H hpM Pl hPl Λ O (p ^ v) (pow_pos hp v) (↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] C v)
      (Ws47.MTASM.iOver O ρD (π v : 𝒢D.level v →ₐ[↥(Ws47.MTASM.RD Pl)] C v) (ιD v) (hιDbase v)) hcl
      (fun χ χ' x x' xx' hx hx' hxx' => Ws47.MTASM.hmul_iB O ρD hρD 𝒢D ιD hιDbase v (π v) hιDmul χ χ' x x' xx' hx hx' hxx')
      (fun y => Ws47.MTASM.hpts_iB O ρD 𝒢D ΔD ιD hιDbase v (π v) hιDpts (hπpts v) (htor v) y)
  choose e he1 he2 using key

  have hcompat : ∀ (v : ℕ) (w : ↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] 𝒢D.level (v + 1)),
      e v (Algebra.TensorProduct.map (AlgHom.id ↥Pl ↥Pl)
            (((π v).comp (𝒢D.transition v) : 𝒢D.level (v + 1) →ₐc[↥(Ws47.MTASM.RD Pl)] C v) :
              𝒢D.level (v + 1) →ₐ[↥(Ws47.MTASM.RD Pl)] C v) w) =
        AddMonoidAlgebra.mapDomainBialgHom ↥Pl
          (AddMonoidHom.pi fun k : Fin O.toricRank =>
            ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ v)) (ZMod (p ^ v))).toAddMonoidHom.comp
              (Pi.evalAddMonoidHom (fun _ => ZMod (p ^ (v + 1))) k)))
          (e (v + 1) (Algebra.TensorProduct.map (AlgHom.id ↥Pl ↥Pl)
            (π (v + 1) : 𝒢D.level (v + 1) →ₐ[↥(Ws47.MTASM.RD Pl)] C (v + 1)) w)) := by
    intro v w

    haveI : IsClosedImmersion (Ws47.MTASM.iB O ρD (AlgHom.id ↥(Ws47.MTASM.RD Pl) (𝒢D.level (v + 1))) (ιD (v + 1)) (hιDbase (v + 1))) :=
      Ws47.MTASM.isClosedImmersion_iB O ρD (AlgHom.id ↥(Ws47.MTASM.RD Pl) (𝒢D.level (v + 1))) (ιD (v + 1)) (hιDbase (v + 1))
        Function.surjective_id (hιDcl (v + 1) (hιDbase (v + 1)))
    haveI : Mono (Ws47.MTASM.iB O ρD (AlgHom.id ↥(Ws47.MTASM.RD Pl) (𝒢D.level (v + 1))) (ιD (v + 1)) (hιDbase (v + 1))) := inferInstance
    refine he2 v (p ^ (v + 1)) (pow_pos hp (v + 1)) (pow_dvd_pow p (Nat.le_succ v)) (↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] C (v + 1))
      (e (v + 1)) (↥Pl ⊗[↥(Ws47.MTASM.RD Pl)] 𝒢D.level (v + 1))
      (Ws47.MTASM.iB O ρD (AlgHom.id ↥(Ws47.MTASM.RD Pl) (𝒢D.level (v + 1))) (ιD (v + 1)) (hιDbase (v + 1)))
      (Algebra.TensorProduct.map (AlgHom.id ↥Pl ↥Pl)
        (((π v).comp (𝒢D.transition v) : 𝒢D.level (v + 1) →ₐc[↥(Ws47.MTASM.RD Pl)] C v) :
          𝒢D.level (v + 1) →ₐ[↥(Ws47.MTASM.RD Pl)] C v))
      (Algebra.TensorProduct.map (AlgHom.id ↥Pl ↥Pl) (π (v + 1) : 𝒢D.level (v + 1) →ₐ[↥(Ws47.MTASM.RD Pl)] C (v + 1)))
      ?_ ?_ w
    ·
      change Spec.map _ ≫ _ = Ws47.MTASM.iB O ρD (π v : 𝒢D.level v →ₐ[↥(Ws47.MTASM.RD Pl)] C v) (ιD v) (hιDbase v)
      rw [Ws47.MTASM.specMap_map_comp_iB, AlgHom.comp_id]
      exact Ws47.MTASM.iB_comp_transition O ρD (π v : 𝒢D.level v →ₐ[↥(Ws47.MTASM.RD Pl)] C v)
        (𝒢D.transition v : 𝒢D.level (v + 1) →ₐ[↥(Ws47.MTASM.RD Pl)] 𝒢D.level v) (ιD v) (hιDbase v) (ιD (v + 1)) (hιDbase (v + 1))
        (hιDt v)
    ·
      rw [Ws47.MTASM.specMap_map_comp_iB, AlgHom.comp_id]
      exact (he1 (v + 1)).symm

  obtain ⟨hMULT, hRED, tC, htCsurj, htCcomp, htCker, hrank⟩ :=
    Ws47.MTASM.hopf_assembly p hresD ↥Pl 𝒢D C π hπ O.toricRank e hcompat
  refine ⟨hMULT, ?_, tC, htCsurj, htCcomp, htCker, hrank⟩
  intro v χ c
  exact Ws47.MTASM.red_translate Pl (C v) (hRED v) χ c

end S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP
end P2MW
export P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP (solution)
