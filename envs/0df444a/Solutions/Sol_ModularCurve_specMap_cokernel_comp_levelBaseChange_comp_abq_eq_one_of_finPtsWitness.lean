-- Prove2me | solution 1 for ModularCurve.specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/872419e9-4786-5e9e-9aaf-0f839aabda70

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
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open IsLocalRing ModularCurve

namespace T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

end T1Geom

namespace T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

end T1Geom

namespace T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section CONV

variable {R S L : Type*} [CommRing R] [CommRing S] [CommRing L] [Algebra R S] [Algebra S L] [Algebra R L]
  [IsScalarTower R S L] {C : Type*} [CommRing C] [Bialgebra R C]

private def _root_.T1Geom.resPt (η : S ⊗[R] C →ₐ[S] L) : C →ₐ[R] L := (η.restrictScalars R).comp Algebra.TensorProduct.includeRight

p2m_export "T1Geom" "resPt"
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

section QUOT

variable {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
  {B C K : Type*} [CommRing B] [CommRing C] [CommRing K] [Bialgebra R B] [Bialgebra R C] [Bialgebra R K]
  (ψ : B →ₐc[R] C) (q : C →ₐc[R] K) (hq : Function.Surjective q)
  (hkerq : RingHom.ker (q : C →+* K) = Ideal.map (ψ : B →ₐ[R] C) (RingHom.ker (Bialgebra.counitAlgHom R B)))

include hkerq in

theorem q_psi_apply (b : B) : q (ψ b) = algebraMap R K (Coalgebra.counit b) := by
  have hb : b - algebraMap R B (Coalgebra.counit b) ∈ RingHom.ker (Bialgebra.counitAlgHom R B) := by
    simp [RingHom.mem_ker, Bialgebra.counitAlgHom_apply, Bialgebra.counit_algebraMap]
  have h1 : ψ (b - algebraMap R B (Coalgebra.counit b)) ∈ RingHom.ker (q : C →+* K) := by
    rw [hkerq]
    exact Ideal.mem_map_of_mem _ hb
  rw [RingHom.mem_ker, map_sub, RingHom.coe_coe, map_sub, sub_eq_zero] at h1
  rw [h1]
  have e1 : ψ (algebraMap R B (Coalgebra.counit b)) = algebraMap R C (Coalgebra.counit b) := (ψ : B →ₐ[R] C).commutes _
  have e2 : q (algebraMap R C (Coalgebra.counit b)) = algebraMap R K (Coalgebra.counit b) := (q : C →ₐ[R] K).commutes _
  rw [e1, e2]

end QUOT

end T1Geom
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

namespace T1GeomW

open T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section FRAMEPTSW

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl} (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh (AlgebraicClosure ℚ)] [Algebra Rh ↥Pl]
  [IsScalarTower Rh ↥Pl (AlgebraicClosure ℚ)]
  (ρh : XHDRLevel.R p →+* Rh)
  (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
  {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) {hB : ℕ} (ℬ : PDivisibleGroup Rh p hB)
  (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  {K₁ : Type} [CommRing K₁] [HopfAlgebra Rh K₁] {w : ℕ} (q : 𝒢.level w →ₐc[Rh] K₁)

noncomputable abbrev sRh : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ JZeroNeronObjectAtP.base p :=
  Spec.map (CommRingCat.ofHom (algebraMap Rh (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom ρh)

include hρh in
theorem barPt_comp_sigmaA_eq_sRh : JZeroNeronObjectAtP.barPt Pl ≫ Λ.σA = sRh (p := p) ρh := by
  rw [Λ.hσA, sRh, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρh]

noncomputable def ptOf (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) : 𝒢.Point (AlgebraicClosure ℚ) w :=
  PDivisibleGroup.Point.ofAlgHom ((resPt η).comp (q : 𝒢.level w →ₐ[Rh] K₁))

theorem toAlgHom_ptOf (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) :
    PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q η) = (resPt η).comp (q : 𝒢.level w →ₐ[Rh] K₁) := rfl

theorem specMap_comp_iB_fst (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (η : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫ iB O ρh (q : 𝒢.level w →ₐ[Rh] K₁) (ι w) (hιbase w) ≫
        pullback.fst O.g Λ.σA =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q η) : 𝒢.level w →ₐ[Rh] AlgebraicClosure ℚ) :
        𝒢.level w →+* AlgebraicClosure ℚ)) ≫ ι w := by
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
  (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
    PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
        (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
  (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
    ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
  (hq : Function.Surjective q)
  (hkerq : RingHom.ker (q : 𝒢.level w →+* K₁) =
    Ideal.map (ψ w : ℬ.level w →ₐ[Rh] 𝒢.level w) (RingHom.ker (Bialgebra.counitAlgHom Rh (ℬ.level w))))

theorem mul_castOver_val {T : Scheme.{0}} {s₁ s₂ : T ⟶ JZeroNeronObjectAtP.base p} (hs : s₁ = s₂) (a b : SchemeHomOver s₁ O.g) :
    (O.L.mul s₂ (JZeroNeronObjectAtP.castOver hs a) (JZeroNeronObjectAtP.castOver hs b)).1 = (O.L.mul s₁ a b).1 := by
  subst hs
  rfl

include hρh hιmul in

theorem hmul_iB (χ χ' : WithConv (↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ))
    (x x' xx' : SchemeHomOver (JZeroNeronObjectAtP.barPt Pl) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hx : x.1 = Spec.map (CommRingCat.ofHom (χ.ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level w →ₐ[Rh] K₁) (ι w) (hιbase w)).1)
    (hx' : x'.1 = Spec.map (CommRingCat.ofHom (χ'.ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level w →ₐ[Rh] K₁) (ι w) (hιbase w)).1)
    (hxx' : xx'.1 = Spec.map (CommRingCat.ofHom ((χ * χ').ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level w →ₐ[Rh] K₁) (ι w) (hιbase w)).1) :
    xx' = (O.L.baseChange Λ.σA).mul (JZeroNeronObjectAtP.barPt Pl) x x' := by
  have hs := barPt_comp_sigmaA_eq_sRh (Λ := Λ) ρh hρh

  have kx : x.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q χ.ofConv) :
      𝒢.level w →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level w →+* AlgebraicClosure ℚ)) ≫ ι w := by
    rw [hx, Category.assoc]; exact specMap_comp_iB_fst O ρh 𝒢 ι hιbase q χ.ofConv
  have kx' : x'.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q χ'.ofConv) :
      𝒢.level w →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level w →+* AlgebraicClosure ℚ)) ≫ ι w := by
    rw [hx', Category.assoc]; exact specMap_comp_iB_fst O ρh 𝒢 ι hιbase q χ'.ofConv
  have kxx' : xx'.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q (χ * χ').ofConv) :
      𝒢.level w →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level w →+* AlgebraicClosure ℚ)) ≫ ι w := by
    rw [hxx', Category.assoc]; exact specMap_comp_iB_fst O ρh 𝒢 ι hιbase q (χ * χ').ofConv

  have hover : ∀ z : SchemeHomOver (JZeroNeronObjectAtP.barPt Pl) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
      (z.1 ≫ pullback.fst O.g Λ.σA) ≫ O.g = sRh (p := p) ρh := by
    intro z
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, hs]
  have hX := hover x; rw [kx] at hX
  have hX' := hover x'; rw [kx'] at hX'

  have hmulpt : ptOf 𝒢 q (χ * χ').ofConv = ptOf 𝒢 q χ.ofConv * ptOf 𝒢 q χ'.ofConv := by
    apply PDivisibleGroup.Point.ext
    intro a
    change ((resPt (χ * χ').ofConv).comp (q : 𝒢.level w →ₐ[Rh] K₁)) a =
      PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q χ.ofConv * ptOf 𝒢 q χ'.ofConv) a
    rw [resPt_convMul, AlgHom.convMul_comp_bialgHom_distrib]
    rfl
  have H := hιmul w (AlgebraicClosure ℚ) (ptOf 𝒢 q χ.ofConv) (ptOf 𝒢 q χ'.ofConv) hX hX'
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

end FRAMEPTSW
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

end T1GeomW
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

namespace T1GeomW

open T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section FRAMEPTS2W

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl} (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh (AlgebraicClosure ℚ)] [Algebra Rh ↥Pl]
  [IsScalarTower Rh ↥Pl (AlgebraicClosure ℚ)]
  (ρh : XHDRLevel.R p →+* Rh)
  {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) {hB : ℕ} (ℬ : PDivisibleGroup Rh p hB)
  (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  {K₁ : Type} [CommRing K₁] [HopfAlgebra Rh K₁] {w : ℕ} (q : 𝒢.level w →ₐc[Rh] K₁)
  (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
    (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) :
        𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
  (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
    PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
        (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
  (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
    ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
  (hq : Function.Surjective q)
  (hkerq : RingHom.ker (q : 𝒢.level w →+* K₁) =
    Ideal.map (ψ w : ℬ.level w →ₐ[Rh] 𝒢.level w) (RingHom.ker (Bialgebra.counitAlgHom Rh (ℬ.level w))))

include hkerq in

theorem ofAlgHom_comp_psi_eq_one (χ₀ : K₁ →ₐ[Rh] AlgebraicClosure ℚ) :
    PDivisibleGroup.Point.ofAlgHom ((χ₀.comp (q : 𝒢.level w →ₐ[Rh] K₁)).comp (ψ w : ℬ.level w →ₐ[Rh] 𝒢.level w)) =
      (1 : ℬ.Point (AlgebraicClosure ℚ) w) := by
  apply PDivisibleGroup.Point.ext
  intro b
  rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.one_apply, AlgHom.comp_apply, AlgHom.comp_apply]
  change χ₀ (q (ψ w b)) = _
  rw [q_psi_apply (ψ w) q hkerq, AlgHom.commutes]

include hkerq hq in

theorem exists_comp_q_eq (x : 𝒢.Point (AlgebraicClosure ℚ) w)
    (hx : PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ w : ℬ.level w →ₐ[Rh] 𝒢.level w)) =
      (1 : ℬ.Point (AlgebraicClosure ℚ) w)) :
    ∃ χ₀ : K₁ →ₐ[Rh] AlgebraicClosure ℚ, χ₀.comp (q : 𝒢.level w →ₐ[Rh] K₁) = PDivisibleGroup.Point.toAlgHom x := by
  have hker : ∀ a ∈ RingHom.ker (q : 𝒢.level w →ₐ[Rh] K₁), PDivisibleGroup.Point.toAlgHom x a = 0 := by
    intro a ha
    have ha' : a ∈ RingHom.ker (q : 𝒢.level w →+* K₁) := ha
    rw [hkerq] at ha'
    refine Submodule.span_induction (p := fun a _ => PDivisibleGroup.Point.toAlgHom x a = 0) ?_ ?_ ?_ ?_ ha'
    · rintro _ ⟨b, hb, rfl⟩
      have := congr_arg (fun y : ℬ.Point (AlgebraicClosure ℚ) w => PDivisibleGroup.Point.toAlgHom y b) hx
      simp only [PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.comp_apply, PDivisibleGroup.Point.one_apply] at this
      rw [SetLike.mem_coe, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hb
      rw [this, hb, map_zero]
    · simp
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro r a _ ha; rw [smul_eq_mul, map_mul, ha, mul_zero]
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker (q : 𝒢.level w →ₐ[Rh] K₁)) (PDivisibleGroup.Point.toAlgHom x) hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom, ?_⟩
  apply AlgHom.ext
  intro c
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
  rw [show (q : 𝒢.level w →ₐ[Rh] K₁) c = (q : 𝒢.level w →ₐ[Rh] K₁) c from rfl,
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

include hιpts hψker htor hq hkerq in

theorem hpts_iB (y : JH M H) :
    y ∈ O.toricPts (p ^ w) ↔ ∃ χ : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ,
      (O.pts y).1 = Spec.map (CommRingCat.ofHom (χ : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
        (iOver O ρh (q : 𝒢.level w →ₐ[Rh] K₁) (ι w) (hιbase w)).1 ≫ pullback.fst O.g Λ.σA := by
  have htor1 := htor w
  have hψker1 := hψker w
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := htor1 y hy
    obtain ⟨χ₀, hχ₀⟩ := exists_comp_q_eq 𝒢 ℬ ψ q hq hkerq x ((hψker1 x).mpr hy)
    refine ⟨Algebra.TensorProduct.lift (Algebra.ofId ↥Pl (AlgebraicClosure ℚ)) χ₀ (fun _ _ => .all _ _), ?_⟩
    rw [hιpts]
    change _ = _ ≫ iB O ρh (q : 𝒢.level w →ₐ[Rh] K₁) (ι w) (hιbase w) ≫ _
    rw [specMap_comp_iB_fst O ρh 𝒢 ι hιbase q, toAlgHom_ptOf, resPt_lift, hχ₀]
  · rintro ⟨χ, hχ⟩
    change _ = _ ≫ iB O ρh (q : 𝒢.level w →ₐ[Rh] K₁) (ι w) (hιbase w) ≫ _ at hχ
    rw [specMap_comp_iB_fst O ρh 𝒢 ι hιbase q] at hχ
    have hone := ofAlgHom_comp_psi_eq_one 𝒢 ℬ ψ q hkerq (resPt χ)
    have hmem : Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (ptOf 𝒢 q χ))) ∈ O.toricPts (p ^ w) :=
      (hψker1 _).mp hone
    have hyx : y = Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (ptOf 𝒢 q χ))) := by
      apply O.pts.injective
      apply Subtype.ext
      rw [hχ, hιpts]
    rwa [hyx]

end FRAMEPTS2W
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

end T1GeomW
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

namespace T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable def bialgEquivBaseChange {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    {C D : Type*} [CommRing C] [CommRing D] [Bialgebra R C] [Bialgebra R D] (e : C ≃ₐc[R] D) :
    S ⊗[R] C ≃ₐc[S] S ⊗[R] D :=
  BialgEquiv.ofBijective (Bialgebra.TensorProduct.map (BialgHom.id S S) (e : C →ₐc[R] D)) (by
    change Function.Bijective (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (e : C ≃ₐ[R] D))
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (e : C ≃ₐ[R] D)).bijective)

section RESIDUE

variable {p : ℕ} [Fact p.Prime] {Pl : ValuationSubring (AlgebraicClosure ℚ)}
  {Rh : Type} [CommRing Rh] [Algebra Rh (AlgebraicClosure ℚ)] [Algebra Rh ↥Pl] [IsScalarTower Rh ↥Pl (AlgebraicClosure ℚ)]
  [Algebra Rh (ZMod p)] [Algebra (ZMod p) (ResidueField ↥Pl)]

theorem residue_compat
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1) (x : Rh) :
    algebraMap (ZMod p) (ResidueField ↥Pl) (algebraMap Rh (ZMod p) x) =
      IsLocalRing.residue ↥Pl (algebraMap Rh ↥Pl x) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ZMod p) = algebraMap Rh (ZMod p) x := ⟨(algebraMap Rh (ZMod p) x).val, ZMod.natCast_zmod_val _⟩
  have hx : algebraMap Rh (ZMod p) (x - n) = 0 := by rw [map_sub, map_natCast, ← hn, sub_self]
  have hval : Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) (x - n)) < 1 := (hres _).mp hx
  have hmem : algebraMap Rh ↥Pl (x - n) ∈ IsLocalRing.maximalIdeal ↥Pl := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have e : ((algebraMap Rh ↥Pl (x - n) : ↥Pl) : AlgebraicClosure ℚ) = algebraMap Rh (AlgebraicClosure ℚ) (x - n) :=
      (IsScalarTower.algebraMap_apply Rh ↥Pl (AlgebraicClosure ℚ) _).symm
    rw [e]; exact hval
  have h2 : IsLocalRing.residue ↥Pl (algebraMap Rh ↥Pl (x - n)) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [map_sub, map_sub, map_natCast, map_natCast, sub_eq_zero] at h2
  rw [← hn, map_natCast, h2]

end RESIDUE
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

end T1Geom
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

namespace N1a

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem ringHom_eq_of_specMap_comp_eq {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}}
    (ι : Spec (CommRingCat.of A) ⟶ Y) [Mono ι] (f g : A →+* B)
    (h : Spec.map (CommRingCat.ofHom f) ≫ ι = Spec.map (CommRingCat.ofHom g) ≫ ι) : f = g := by
  rw [cancel_mono] at h
  simpa using congr_arg CommRingCat.Hom.hom (Spec.map_injective h)

theorem specMap_ofHom_comp {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

section NSMUL

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {p h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ)
  (ι : Spec (CommRingCat.of (G.level w)) ⟶ X)
  (hιbase : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level w))))
  (hιmul : ∀ (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B w)
    (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R B))),
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι =
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

def tautPt : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (G.level w)))) f := ⟨ι, hιbase⟩

noncomputable def univPt : G.Point (G.level w) w := PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level w))

theorem specMap_univPt_pow (n : ℕ) :
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w ^ n) : G.level w →ₐ[R] G.level w) :
      G.level w →+* G.level w)) = Spec.map (CommRingCat.ofHom (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) n : G.level w →+* G.level w)) := by
  rw [PDivisibleGroup.Point.toAlgHom_pow, univPt, PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.id_comp]

include hιmul in

theorem nsmul_tautPt_val (n : ℕ) :
    (L.nsmul _ (n + 1) (tautPt G w ι hιbase)).1 =
      Spec.map (CommRingCat.ofHom (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) (n + 1) : G.level w →+* G.level w)) ≫ ι := by
  induction n with
  | zero =>
      rw [L.nsmul_one_apply, PDivisibleGroup.Hopf.nsmulAlgHom_one]
      change ι = Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ ι
      rw [CommRingCat.ofHom_id]; erw [Spec.map_id]; rw [Category.id_comp]
  | succ n ih =>
      rw [L.nsmul_succ]
      have hover : ∀ m : ℕ, (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w ^ m) :
          G.level w →ₐ[R] G.level w) : G.level w →+* G.level w)) ≫ ι) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap R (G.level w))) := by
        intro m
        rw [Category.assoc, hιbase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact (PDivisibleGroup.Point.toAlgHom (univPt G w ^ m)).comp_algebraMap
      have H := hιmul (G.level w) (univPt G w ^ (n + 1)) (univPt G w) (hover (n + 1)) (by simpa using hover 1)
      rw [← pow_succ, specMap_univPt_pow] at H
      rw [H]
      have hid : Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w) : G.level w →ₐ[R] G.level w) :
          G.level w →+* G.level w)) = 𝟙 _ := by
        rw [univPt, PDivisibleGroup.Point.toAlgHom_ofAlgHom]
        change Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
        rw [CommRingCat.ofHom_id]; exact Spec.map_id _
      congr 2
      · apply Subtype.ext
        show (L.nsmul _ (n + 1) (tautPt G w ι hιbase)).1 =
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w ^ (n + 1)) : G.level w →ₐ[R] G.level w) :
            G.level w →+* G.level w)) ≫ ι
        rw [ih, specMap_univPt_pow]
      · apply Subtype.ext
        show ι = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (univPt G w) : G.level w →ₐ[R] G.level w) :
            G.level w →+* G.level w)) ≫ ι
        rw [hid, Category.id_comp]

include hιbase hιmul in

theorem comp_schemeNsmul (n : ℕ) :
    ι ≫ L.schemeNsmul (n + 1) =
      Spec.map (CommRingCat.ofHom (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) (n + 1) : G.level w →+* G.level w)) ≫ ι := by
  rw [← nsmul_tautPt_val L G w ι hιbase hιmul n, RelativeGroupLaw.schemeNsmul]
  have hnat := L.nsmul_natural f (Spec.map (CommRingCat.ofHom (algebraMap R (G.level w)))) ι hιbase (n + 1)
    RelativeGroupLaw.idPoint
  have hpt : GoodReductionJacobian.schemeHomOverComp ι hιbase (RelativeGroupLaw.idPoint (f := f)) = tautPt G w ι hιbase :=
    Subtype.ext (Category.comp_id ι)
  rw [hpt] at hnat
  rw [← hnat]
  rfl

end NSMUL
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

end N1a
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

namespace N1a

section HOMPT

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {p h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ)
  (ι : Spec (CommRingCat.of (G.level w)) ⟶ X)
  (hιbase : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level w))))
  (hιmul : ∀ (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B w)
    (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R B))),
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι =
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

include hιbase in

theorem hover {B : Type} [CommRing B] [Algebra R B] (x : G.Point B w) :
    (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [Category.assoc, hιbase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (PDivisibleGroup.Point.toAlgHom x).comp_algebraMap

include hιbase hιmul in

theorem specMap_one_comp (B : Type) [CommRing B] [Algebra R B] :
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (1 : G.Point B w) : G.level w →ₐ[R] B) : G.level w →+* B)) ≫ ι =
      (L.one (Spec.map (CommRingCat.ofHom (algebraMap R B)))).1 := by
  have h1 := hover G w ι hιbase (1 : G.Point B w)
  have H := hιmul B 1 1 h1 h1
  rw [mul_one] at H
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  have HP : (⟨_, h1⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) *
      (⟨_, h1⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) = ⟨_, h1⟩ :=
    Subtype.ext H.symm
  rw [mul_eq_left] at HP
  exact congr_arg Subtype.val HP

include hιbase hιmul in

theorem comp_schemeNsmul_pow_eq_one [Fact p.Prime] :
    ι ≫ L.schemeNsmul (p ^ w) = (ι ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  obtain ⟨n, hn⟩ : ∃ n, p ^ w = n + 1 := ⟨p ^ w - 1, (Nat.succ_pred_eq_of_pos (pow_pos (Nat.Prime.pos Fact.out) w)).symm⟩
  rw [hn, comp_schemeNsmul L G w ι hιbase hιmul n, ← hn]

  have hpow : (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) (p ^ w) : G.level w →+* G.level w) =
      ((PDivisibleGroup.Point.toAlgHom (1 : G.Point (G.level w) w) : G.level w →ₐ[R] G.level w) : G.level w →+* G.level w) := by
    rw [G.nsmulAlgHom_pow_level w]
    rfl
  rw [hpow, specMap_one_comp L G w ι hιbase hιmul (G.level w), hιbase]
  have := L.one_natural (𝟙 (Spec (CommRingCat.of R))) (Spec.map (CommRingCat.ofHom (algebraMap R (G.level w))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (G.level w)))) (Category.comp_id _)
  rw [← this]
  rfl

end HOMPT
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

end N1a
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

namespace N1a

section CONV

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ)

theorem toAlgHom_includeLeft_mul_includeRight :
    PDivisibleGroup.Point.toAlgHom ((PDivisibleGroup.Point.ofAlgHom (Algebra.TensorProduct.includeLeft :
        G.level w →ₐ[R] G.level w ⊗[R] G.level w) : G.Point (G.level w ⊗[R] G.level w) w) *
      PDivisibleGroup.Point.ofAlgHom Algebra.TensorProduct.includeRight) =
      Bialgebra.comulAlgHom R (G.level w) := by
  apply AlgHom.ext
  intro a
  rw [PDivisibleGroup.Point.mul_apply, PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.toAlgHom_ofAlgHom,
    Algebra.TensorProduct.lift_includeLeft_includeRight, Bialgebra.comulAlgHom_apply, AlgHom.id_apply]

theorem toAlgHom_includeLeft_comp_mul_includeRight_comp {p' h' : ℕ} (G' : PDivisibleGroup R p' h') (w' : ℕ)
    (ρ : G'.level w' →ₐ[R] G.level w) :
    PDivisibleGroup.Point.toAlgHom ((PDivisibleGroup.Point.ofAlgHom ((Algebra.TensorProduct.includeLeft :
        G.level w →ₐ[R] G.level w ⊗[R] G.level w).comp ρ) : G'.Point (G.level w ⊗[R] G.level w) w') *
      PDivisibleGroup.Point.ofAlgHom ((Algebra.TensorProduct.includeRight : G.level w →ₐ[R] G.level w ⊗[R] G.level w).comp ρ)) =
      (Algebra.TensorProduct.map ρ ρ).comp (Bialgebra.comulAlgHom R (G'.level w')) := by
  apply AlgHom.ext
  intro a
  rw [PDivisibleGroup.Point.mul_apply, PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.toAlgHom_ofAlgHom,
    AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [Algebra.TensorProduct.lift_tmul]

end CONV
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

end N1a
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

namespace N1b

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open T1Geom

section HOMIP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl} (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh (ZMod p)]
  (ρh : XHDRLevel.R p →+* Rh) {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) (v : ℕ)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
    (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g =
      (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
    (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g =
      (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
      (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
  (σp : Spec (CommRingCat.of (ZMod p)) ⟶ JZeroNeronObjectAtP.base p)
  (hσp : Spec.map (CommRingCat.ofHom (algebraMap Rh (ZMod p))) ≫ Spec.map (CommRingCat.ofHom ρh) = σp)
  (ιp : ∀ v : ℕ, Spec (CommRingCat.of (ZMod p ⊗[Rh] 𝒢.level v)) ⟶ pullback O.g σp)
  (hιp₁ : ∀ v : ℕ, ιp v ≫ pullback.fst O.g σp =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : 𝒢.level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ ι v)
  (hιp₂ : ∀ v : ℕ, ιp v ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))))

include hιbase hιmul hσp hιp₁ hιp₂ in

theorem hom_ιp (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒢.baseChange (ZMod p)).Point B v)
    (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
        (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ ιp v) ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
    (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
        (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ ιp v) ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) :
    Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
        (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ ιp v =
      ((O.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1 := by
  letI : Algebra Rh B := ((algebraMap (ZMod p) B).comp (algebraMap Rh (ZMod p))).toAlgebra
  haveI : IsScalarTower Rh (ZMod p) B := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let pt : (𝒢.baseChange (ZMod p)).Point B v → 𝒢.Point B v := fun z =>
    PDivisibleGroup.Point.ofAlgHom (resPt (PDivisibleGroup.Point.toAlgHom z))
  have hpt_mul : pt (x * y) = pt x * pt y := by
    apply PDivisibleGroup.Point.ext; intro a
    exact DFunLike.congr_fun (resPt_convMul (R := Rh) (S := ZMod p) (C := 𝒢.level v) (L := B)
      (WithConv.toConv (PDivisibleGroup.Point.toAlgHom x)) (WithConv.toConv (PDivisibleGroup.Point.toAlgHom y))) a

  have kz : ∀ z : (𝒢.baseChange (ZMod p)).Point B v,
      (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom z : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
        (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ ιp v) ≫ pullback.fst O.g σp =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (pt z) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v := by
    intro z
    rw [Category.assoc]
    erw [hιp₁]
    erw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    rfl

  have hs : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) ≫ σp =
      Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [← hσp, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hover : ∀ z : (𝒢.baseChange (ZMod p)).Point B v,
      (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (pt z) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g =
      Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    intro z
    rw [Category.assoc, hιbase, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 2
    exact congr_arg _ (PDivisibleGroup.Point.toAlgHom (pt z)).comp_algebraMap
  have H := hιmul v B (pt x) (pt y) (hover x) (hover y)
  rw [← hpt_mul, ← kz (x * y)] at H
  apply pullback.hom_ext
  · rw [H, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    have e1 : (⟨_, hover x⟩ : SchemeHomOver _ O.g) =
        JZeroNeronObjectAtP.castOver hs (RelativeGroupLaw.baseChangePointToBase σp ⟨_, hx⟩) := Subtype.ext (kz x).symm
    have e2 : (⟨_, hover y⟩ : SchemeHomOver _ O.g) =
        JZeroNeronObjectAtP.castOver hs (RelativeGroupLaw.baseChangePointToBase σp ⟨_, hy⟩) := Subtype.ext (kz y).symm
    rw [e1, e2, T1GeomW.mul_castOver_val O hs]
  · rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd, Category.assoc]
    erw [hιp₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (PDivisibleGroup.Point.toAlgHom (x * y)).comp_algebraMap

end HOMIP
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

end N1b
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

namespace N1b

section TORUS

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl} (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [Algebra Rh ↥Pl] [Algebra Rh (ZMod p)] [Algebra (ZMod p) (ResidueField ↥Pl)]
  (hRκ : ∀ r : Rh, algebraMap (ZMod p) (ResidueField ↥Pl) (algebraMap Rh (ZMod p) r) =
    IsLocalRing.residue ↥Pl (algebraMap Rh ↥Pl r))
  (ρh : XHDRLevel.R p →+* Rh) {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) (v : ℕ)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  {K : Type} [CommRing K] [Algebra Rh K] (qK : 𝒢.level v →ₐ[Rh] K)
  {m : ℕ} (hm : 0 < m) (e : ↥Pl ⊗[Rh] K ≃ₐ[↥Pl] AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m))
  (htl : (O.toricLift m hm).1 =
    Spec.map (CommRingCat.ofHom (e : ↥Pl ⊗[Rh] K →+* AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m))) ≫ T1Geom.iB O ρh qK (ι v) (hιbase v))
  (gK : 𝒢.level v →+* ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K))
  (hgK : ∀ c : 𝒢.level v, gK c = (1 : ResidueField ↥Pl) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[Rh] qK c))

include hRκ hm e htl hgK in
set_option maxHeartbeats 3200000 in

theorem exists_torusPt_comp_eq :
    ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)))))
        (JZeroNeronObjectAtP.torusStr (ResidueField ↥Pl) O.toricRank),
      y.1 ≫ O.torusFibre.1 ≫ pullback.fst O.g (JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) =
        Spec.map (CommRingCat.ofHom gK) ≫ ι v := by
  classical

  haveI : IsScalarTower Rh (ZMod p) (ResidueField ↥Pl) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [hRκ, IsScalarTower.algebraMap_apply Rh ↥Pl (ResidueField ↥Pl), IsLocalRing.ResidueField.algebraMap_eq]

  obtain ⟨τ, hτ_smul, hτe⟩ : ∃ τ : AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m) →+* (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)),
      (∀ (b : ↥Pl) (x : AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m)), τ (b • x) = IsLocalRing.residue ↥Pl b • τ x) ∧
      (∀ k : K, τ (e ((1 : ↥Pl) ⊗ₜ[Rh] k)) = (1 : (ResidueField ↥Pl)) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[Rh] k)) := by
    let τ₁ : ↥Pl ⊗[Rh] K →ₐ[Rh] (ResidueField ↥Pl ⊗[Rh] K) :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom Rh ↥Pl (ResidueField ↥Pl)) (AlgHom.id Rh K)
    let cbc : (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)) ≃ₐ[ResidueField ↥Pl] (ResidueField ↥Pl ⊗[Rh] K) :=
      Algebra.TensorProduct.cancelBaseChange Rh (ZMod p) (ResidueField ↥Pl) (ResidueField ↥Pl) K
    refine ⟨(cbc.symm : (ResidueField ↥Pl ⊗[Rh] K) →ₐ[ResidueField ↥Pl] (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K))).toRingHom.comp
      ((τ₁ : ↥Pl ⊗[Rh] K →+* (ResidueField ↥Pl ⊗[Rh] K)).comp (e.symm : AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m) →+* ↥Pl ⊗[Rh] K)), ?_, ?_⟩
    · intro b x
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [map_smul]
      have h1 : ∀ z : ↥Pl ⊗[Rh] K, τ₁ (b • z) = IsLocalRing.residue ↥Pl b • τ₁ z := by
        intro z
        rw [Algebra.smul_def, map_mul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        congr 1
      rw [h1]
      change cbc.symm (IsLocalRing.residue ↥Pl b • τ₁ (e.symm x)) = IsLocalRing.residue ↥Pl b • cbc.symm (τ₁ (e.symm x))
      rw [map_smul]
    · intro k
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgHom.toRingHom_eq_coe]
      rw [AlgEquiv.symm_apply_apply]
      simp only [τ₁, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      exact Algebra.TensorProduct.cancelBaseChange_symm_tmul Rh (ZMod p) (ResidueField ↥Pl) (ResidueField ↥Pl) K 1 k

  obtain ⟨θ, hθτ⟩ : ∃ θ : AddMonoidAlgebra (ResidueField ↥Pl) (Fin O.toricRank → ZMod m) →ₐ[ResidueField ↥Pl] (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)),
      θ.toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (IsLocalRing.residue ↥Pl)) = τ := by
    refine ⟨AddMonoidAlgebra.lift (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)) (Fin O.toricRank → ZMod m)
      ((τ : AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m) →* (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K))).comp (AddMonoidAlgebra.of ↥Pl (Fin O.toricRank → ZMod m))), ?_⟩
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      simp only [RingHom.coe_comp, Function.comp_apply, AddMonoidAlgebra.mapRingHom_single]
      rw [show AddMonoidAlgebra.single (0 : Fin O.toricRank → ZMod m) b = b • (1 : AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m)) by
        rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one], hτ_smul, map_one]
      rw [show AddMonoidAlgebra.single (0 : Fin O.toricRank → ZMod m) (IsLocalRing.residue ↥Pl b) =
        algebraMap (ResidueField ↥Pl) (AddMonoidAlgebra (ResidueField ↥Pl) (Fin O.toricRank → ZMod m)) (IsLocalRing.residue ↥Pl b) from rfl]
      change AddMonoidAlgebra.lift _ _ _ _ (algebraMap _ _ (IsLocalRing.residue ↥Pl b)) = _
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    · intro a
      simp only [RingHom.coe_comp, Function.comp_apply, AddMonoidAlgebra.mapRingHom_single, map_one]
      simp [AddMonoidAlgebra.lift_single]

  have hcompat : ∀ c : 𝒢.level v,
      θ.toRingHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (IsLocalRing.residue ↥Pl)
        (e ((1 : ↥Pl) ⊗ₜ[Rh] qK c))) = (1 : (ResidueField ↥Pl)) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[Rh] qK c) := by
    intro c
    have := RingHom.congr_fun hθτ (e ((1 : ↥Pl) ⊗ₜ[Rh] qK c))
    rw [RingHom.comp_apply] at this
    rw [this]
    exact hτe (qK c)

  have hy2 : (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ JZeroNeronObjectAtP.muToTorus (ResidueField ↥Pl) O.toricRank m) ≫
      JZeroNeronObjectAtP.torusStr (ResidueField ↥Pl) O.toricRank =
      Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)))) := by
    simp only [JZeroNeronObjectAtP.muToTorus, JZeroNeronObjectAtP.torusStr, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show algebraMap (ResidueField ↥Pl) (JZeroNeronObjectAtP.torusCoord (ResidueField ↥Pl) O.toricRank) c =
        AddMonoidAlgebra.single 0 c from rfl, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      map_zero, show AddMonoidAlgebra.single (0 : Fin O.toricRank → ZMod m) c =
        algebraMap (ResidueField ↥Pl) (AddMonoidAlgebra (ResidueField ↥Pl) (Fin O.toricRank → ZMod m)) c from rfl,
      AlgHom.commutes]
  refine ⟨⟨_, hy2⟩, ?_⟩

  have hring : ((((θ.toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (IsLocalRing.residue ↥Pl))).comp
      (e : ↥Pl ⊗[Rh] K →+* AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod m))).comp
        (Algebra.TensorProduct.includeRight.toRingHom : K →+* ↥Pl ⊗[Rh] K)).comp (qK : 𝒢.level v →+* K)) = gK := by
    refine RingHom.ext fun c => ?_
    rw [hgK]
    exact hcompat c
  have hS' : ∀ {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z) {W : Scheme.{0}}
      (k : Spec (CommRingCat.of X) ⟶ W),
      Spec.map (CommRingCat.ofHom (g.comp f)) ≫ k = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) ≫ k := by
    intros; rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  dsimp only
  rw [Category.assoc, ← O.toricLift_special m hm, htl]
  simp only [Category.assoc]
  rw [T1Geom.iB_fst O ρh qK (ι v) (hιbase v)]
  dsimp only [JZeroNeronObjectAtP.muBaseChange]
  rw [← hS', ← hS', ← hS', ← hS', hring]

end TORUS
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

end N1b
p2m_reactivate "P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness.T1Geom"

open ModularCurve in
set_option maxHeartbeats 3200000 in

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

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [IsDiscreteValuationRing Rh]
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    (S : Set ℕ) (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))

    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (he : ∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    (heinj : Function.Injective e)
    (herange : ∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n))
    (hegal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) = ModularCurve.JH.tateGaloisRep M H p τ (e x))
    (hsat : ∀ y : TateModule p (ModularCurve.JH M H), (p : ℤ_[p]) • y ∈ LinearMap.range e → y ∈ LinearMap.range e)
    (hcoker : Nonempty ((TateModule p (ModularCurve.JH M H) ⧸ LinearMap.range e) ≃ₗ[ℤ_[p]] (Fin O.toricRank → ℤ_[p])))
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    {hB : ℕ}
    (ℬ : PDivisibleGroup Rh p hB)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
    {h' : ℕ}
    (hhB : h = O.toricRank + hB)
    (hhB2 : hB = 2 * h')
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b)
    (hψred : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hperiod : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)

    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ ModularCurve.JZeroNeronObjectAtP.base p)
    (hσp : Spec.map (CommRingCat.ofHom (algebraMap Rh (ZMod p))) ≫ Spec.map (CommRingCat.ofHom ρh) = σp)
    (ιp : ∀ v : ℕ, Spec (CommRingCat.of (ZMod p ⊗[Rh] 𝒢.level v)) ⟶ pullback O.g σp)
    (hιp₁ : ∀ v : ℕ, ιp v ≫ pullback.fst O.g σp =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : 𝒢.level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ ι v)
    (hιp₂ : ∀ v : ℕ, ιp v ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))))
    (q : Fin 2 → NeronModelInfra.SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f))

    [Algebra (ZMod p) (ResidueField ↥Pl)]
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl))) ≫ σp = ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)
    (hqmul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : NeronModelInfra.SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange σp).mul s x y) (q i) =
          (Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x (q i)) (NeronModelInfra.schemeHomOverComp y (q i)))
    (hqbc : ∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1)

    (hjB : ∀ v, Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)))

    {hΛ : ℕ} (𝒜 : PDivisibleGroup (ModularCurve.JZeroNeronObjectAtP.baseRing p) p hΛ)

    (hBΛ : hB = 2 * hΛ)
    [Algebra (ModularCurve.JZeroNeronObjectAtP.baseRing p) (ZMod p)]
    (hσp' : σp = Spec.map (CommRingCat.ofHom (algebraMap (ModularCurve.JZeroNeronObjectAtP.baseRing p) (ZMod p))))
    (ι' : ∀ v : ℕ, Spec (CommRingCat.of ((𝒜.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
    (hι'base : ∀ v : ℕ, ι' v ≫ pullback.snd Λ.f σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v))))
    (hι'cl : ∀ v : ℕ, IsClosedImmersion (ι' v))
    (hι'p : ∀ (v : ℕ), ∃ h3 : ι' v ≫ (Λ.L.baseChange σp).schemeNsmul (p ^ v) =
          (ι' v ≫ pullback.snd Λ.f σp) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1,
      IsIso (pullback.lift (f := (Λ.L.baseChange σp).schemeNsmul (p ^ v)) (g := ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1)
        (ι' v) (ι' v ≫ pullback.snd Λ.f σp) h3))

    (hι'mul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒜.baseChange (ZMod p)).Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v =
        ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

    (hι't : ∀ v : ℕ, Spec.map (CommRingCat.ofHom
        ((𝒜.baseChange (ZMod p)).transition v : (𝒜.baseChange (ZMod p)).level (v + 1) →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' (v + 1) = ι' v)

    (v : ℕ) (K : Type) [CommRing K] [HopfAlgebra Rh K] [Module.Free Rh K]
    (qK : 𝒢.level v →ₐc[Rh] K) (hqK : Function.Surjective qK)
    (hkerK : RingHom.ker (qK : 𝒢.level v →+* K) =
      Ideal.map (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v) (RingHom.ker (Bialgebra.counitAlgHom Rh (ℬ.level v))))
    :
    ∀ i : Fin 2,
      Spec.map (CommRingCat.ofHom (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) qK :
          ZMod p ⊗[Rh] 𝒢.level v →+* ZMod p ⊗[Rh] K)) ≫ ιp v ≫ (q i).1 =
        ((Spec.map (CommRingCat.ofHom (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) qK :
          ZMod p ⊗[Rh] 𝒢.level v →+* ZMod p ⊗[Rh] K)) ≫ ιp v ≫ (q i).1) ≫ pullback.snd Λ.f σp) ≫
          ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 := by
  intro i
  classical
  haveI : Mono (ι' v) := by haveI := hι'cl v; infer_instance

  letI algRP : Algebra Rh ↥Pl := ((algebraMap Rh (AlgebraicClosure ℚ)).codRestrict Pl hRA).toAlgebra
  haveI : IsScalarTower Rh ↥Pl (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Rh K :=
    Module.Finite.of_surjective ((qK : 𝒢.level v →ₐ[Rh] K).toLinearMap) hqK
  haveI : Module.Finite ↥Pl (↥Pl ⊗[Rh] K) := inferInstance
  haveI : Module.Flat ↥Pl (↥Pl ⊗[Rh] K) := inferInstance

  have hm : 0 < p ^ v := pow_pos (Nat.Prime.pos Fact.out) v
  have hcl : IsClosedImmersion (T1Geom.iOver O ρh (qK : 𝒢.level v →ₐ[Rh] K) (ι v) (hιbase v)).1 :=
    T1Geom.isClosedImmersion_iB O ρh (qK : 𝒢.level v →ₐ[Rh] K) (ι v) (hιbase v) hqK (hιcl v (hιbase v))
  obtain ⟨e, he1, -⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff
      p M H hpM Pl hPl Λ O (p ^ v) hm (↥Pl ⊗[Rh] K)
      (T1Geom.iOver O ρh (qK : 𝒢.level v →ₐ[Rh] K) (ι v) (hιbase v)) hcl
      (fun χ χ' x x' xx' hx hx' hxx' => T1GeomW.hmul_iB O ρh hρh 𝒢 ι hιbase qK hιmul χ χ' x x' xx' hx hx' hxx')
      (fun y => T1GeomW.hpts_iB O ρh 𝒢 ℬ ψ Δ ι hιbase qK hιpts hψker htor hqK hkerK y)

  have htl : (O.toricLift (p ^ v) hm).1 =
      Spec.map (CommRingCat.ofHom ((e : ↥Pl ⊗[Rh] K →ₐc[↥Pl] AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod (p ^ v))) :
        ↥Pl ⊗[Rh] K →+* AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod (p ^ v)))) ≫
        T1Geom.iB O ρh (qK : 𝒢.level v →ₐ[Rh] K) (ι v) (hιbase v) := by
    change _ = _ ≫ (T1Geom.iOver O ρh (qK : 𝒢.level v →ₐ[Rh] K) (ι v) (hιbase v)).1
    rw [← he1, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    conv_lhs => rw [← Category.id_comp (O.toricLift (p ^ v) hm).1]
    congr 1
    rw [← Spec.map_id]
    congr 1
    ext c
    · simp
    · simp

  have hq2 : (q i).1 ≫ pullback.snd Λ.f σp = pullback.snd O.g σp := (q i).2
  have hφbase : (ιp v ≫ (q i).1) ≫ pullback.snd Λ.f σp =
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))) := by
    rw [Category.assoc, hq2]; exact hιp₂ v
  have hφmul : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒢.baseChange (ZMod p)).Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
          (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ (ιp v ≫ (q i).1)) ≫ pullback.snd Λ.f σp =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
          (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ (ιp v ≫ (q i).1)) ≫ pullback.snd Λ.f σp =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
          (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ (ιp v ≫ (q i).1) =
        ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1 := by
    intro B _ _ x y hx hy
    have hx' : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
        (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ ιp v) ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) := by
      rw [← hx, Category.assoc, Category.assoc, Category.assoc, hq2]
    have hy' : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) :
        (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ ιp v) ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) := by
      rw [← hy, Category.assoc, Category.assoc, Category.assoc, hq2]
    have H := N1b.hom_ιp O ρh 𝒢 v ι hιbase hιmul σp hσp ιp hιp₁ hιp₂ B x y hx' hy'
    rw [← Category.assoc, H]
    have H2 := congr_arg Subtype.val (hqmul i (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx'⟩ ⟨_, hy'⟩)
    rw [NeronModelInfra.schemeHomOverComp_coe] at H2
    rw [H2]
    congr 2 <;> exact Subtype.ext (Category.assoc _ _ _)
  obtain ⟨ρt, hρt⟩ :=
    ModularCurve.JHNeronObjectAtP.LevelData.exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level p M H hpM Pl Λ σp 𝒜 ι' hι'base
      hι'cl hι'p hι'mul Rh 𝒢 v (ιp v ≫ (q i).1) hφbase hφmul

  set qK' : ZMod p ⊗[Rh] 𝒢.level v →+* ZMod p ⊗[Rh] K :=
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) qK : ZMod p ⊗[Rh] 𝒢.level v →+* ZMod p ⊗[Rh] K) with hqK'
  let jκ : ZMod p ⊗[Rh] K →ₐ[ZMod p] (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)) := Algebra.TensorProduct.includeRight
  have hjκ : Function.Injective jκ :=
    Algebra.TensorProduct.includeRight_injective (algebraMap (ZMod p) (ResidueField ↥Pl)).injective

  have hsK : (Spec.map (CommRingCat.ofHom qK') ≫ ιp v ≫ (q i).1) ≫ pullback.snd Λ.f σp =
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] K))) := by
    rw [Category.assoc]
    erw [hφbase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) qK :
      ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] K).comp_algebraMap
  rw [hsK]

  have hL : Spec.map (CommRingCat.ofHom qK') ≫ ιp v ≫ (q i).1 =
      Spec.map (CommRingCat.ofHom (qK'.comp (ρt : (𝒜.baseChange (ZMod p)).level v →+* (𝒢.baseChange (ZMod p)).level v))) ≫ ι' v := by
    erw [N1a.specMap_ofHom_comp, Category.assoc, hρt]
  have hunit := N1a.specMap_one_comp (Λ.L.baseChange σp) (𝒜.baseChange (ZMod p)) v (ι' v) (hι'base v) (hι'mul v) (ZMod p ⊗[Rh] K)
  have hR : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] K))) ≫
      ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (1 : (𝒜.baseChange (ZMod p)).Point (ZMod p ⊗[Rh] K) v) :
        (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] ZMod p ⊗[Rh] K) : (𝒜.baseChange (ZMod p)).level v →+* ZMod p ⊗[Rh] K)) ≫ ι' v := by
    rw [hunit]
    have := (Λ.L.baseChange σp).one_natural (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] K))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] K)))) (Category.comp_id _)
    rw [← this]
    rfl
  rw [hL, hR]

  suffices hκeq : Spec.map (CommRingCat.ofHom jκ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom qK') ≫ ιp v ≫ (q i).1) =
      Spec.map (CommRingCat.ofHom jκ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] K))) ≫
          ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1) by
    rw [hL, hR, ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at hκeq
    have hre := Spec.map_injective hκeq
    have hr : qK'.comp (ρt : (𝒜.baseChange (ZMod p)).level v →+* (𝒢.baseChange (ZMod p)).level v) =
        ((PDivisibleGroup.Point.toAlgHom (1 : (𝒜.baseChange (ZMod p)).Point (ZMod p ⊗[Rh] K) v) :
          (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] ZMod p ⊗[Rh] K) : (𝒜.baseChange (ZMod p)).level v →+* ZMod p ⊗[Rh] K) := by
      refine RingHom.ext fun a => hjκ ?_
      have ha := congr_arg (fun f : CommRingCat.of ((𝒜.baseChange (ZMod p)).level v) ⟶ CommRingCat.of (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)) =>
        CommRingCat.Hom.hom f a) hre
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using ha
    rw [hr]

  have hfold0 : ∀ {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z),
      Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
    intros; rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hRκ : ∀ r : Rh, algebraMap (ZMod p) (ResidueField ↥Pl) (algebraMap Rh (ZMod p) r) =
      IsLocalRing.residue ↥Pl (algebraMap Rh ↥Pl r) := fun r => T1Geom.residue_compat (p := p) (Pl := Pl) hres r
  haveI : IsScalarTower (ZMod p) (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)) := inferInstance
  let gK : 𝒢.level v →+* (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K)) := jκ.toRingHom.comp (qK'.comp
    (Algebra.TensorProduct.includeRight.toRingHom : 𝒢.level v →+* ZMod p ⊗[Rh] 𝒢.level v))
  have hgK : ∀ c : 𝒢.level v, gK c = (1 : ResidueField ↥Pl) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[Rh] qK c) := by
    intro c
    simp only [gK, RingHom.coe_comp, Function.comp_apply, hqK']
    rfl
  obtain ⟨y, hy⟩ := N1b.exists_torusPt_comp_eq O hRκ ρh 𝒢 v ι hιbase (qK : 𝒢.level v →ₐ[Rh] K) hm
    (e : ↥Pl ⊗[Rh] K ≃ₐc[↥Pl] AddMonoidAlgebra ↥Pl (Fin O.toricRank → ZMod (p ^ v))).toAlgEquiv htl gK hgK

  let xs := NeronModelInfra.schemeHomOverComp y O.torusFibre
  have hxs1 : xs.1 = y.1 ≫ O.torusFibre.1 := rfl
  have hone : ∀ j, NeronModelInfra.schemeHomOverComp xs (O.abqFibre j) =
      (Λ.L.baseChange (JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)).one _ :=
    (O.abqFibre_eq_one_iff _ xs).mpr ⟨y, rfl⟩

  let sκ : Spec (CommRingCat.of (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K))) ⟶ Spec (CommRingCat.of (ResidueField ↥Pl)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K))))
  have hsκ : Spec.map (CommRingCat.ofHom jκ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] K))) =
      sκ ≫ Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl))) := by
    simp only [sκ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    exact IsScalarTower.algebraMap_eq (ZMod p) (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K))

  have key : xs.1 ≫ pullback.map O.g (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) O.g σp (𝟙 _)
        (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
      Spec.map (CommRingCat.ofHom jκ.toRingHom) ≫ Spec.map (CommRingCat.ofHom qK') ≫ ιp v := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, hxs1, Category.assoc, hy, Category.assoc, Category.assoc]
      erw [hιp₁ v]
      simp only [gK, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, xs.2, Category.assoc, Category.assoc]
      erw [hιp₂ v]
      rw [← hsκ, ← hfold0, ← hfold0]
      have hc : (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) qK :
          ZMod p ⊗[Rh] 𝒢.level v →+* ZMod p ⊗[Rh] K).comp (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)) =
          algebraMap (ZMod p) (ZMod p ⊗[Rh] K) :=
        RingHom.ext fun x => AlgHomClass.commutes (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) qK) x
      erw [hc]
      exact hfold0 _ _

  have key' := congrArg (· ≫ (q i).1) key
  simp only [Category.assoc] at key'
  rw [← key', ← hqbc i, ← Category.assoc xs.1, ← NeronModelInfra.schemeHomOverComp_coe, hone i,
    RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe]

  have hτ : (Spec.map (CommRingCat.ofHom jκ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] K)))) ≫
      𝟙 _ ≫ σp = sκ ≫ JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA := by
    rw [Category.id_comp, hsκ, Category.assoc, hfac]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id,
      RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe]
    have h1 := Λ.L.one_natural (𝟙 _ ≫ σp) _
      ((Spec.map (CommRingCat.ofHom jκ.toRingHom) : Spec (CommRingCat.of (ResidueField ↥Pl ⊗[ZMod p] (ZMod p ⊗[Rh] K))) ⟶ Spec (CommRingCat.of (ZMod p ⊗[Rh] K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] K)))) rfl
    have h1' := congr_arg Subtype.val h1
    rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] at h1'
    rw [h1']
    exact (congrArg (fun τ => (Λ.L.one τ).1) hτ).symm
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, RelativeGroupLaw.baseChange_one,
      RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd, Category.comp_id, hsκ, pullback.lift_snd_assoc]

end S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness
end P2MW
export P2MW.S_ModularCurve_specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness (solution)
