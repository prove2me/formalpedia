-- Prove2me | solution 1 for ModularCurve.nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2af356e6-f8e6-58ae-a613-3ebc6301c4c7

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff
import Theorems.Thm_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul
import Theorems.Thm_AddMonoidAlgebra_exists_bialgEquiv_baseChange_tmul_single
import Theorems.Thm_Bialgebra_exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit
import Theorems.Thm_Module_free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq
import Theorems.Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open ModularCurve

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
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

namespace T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section FRAMEPTS

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
  {K₁ : Type} [CommRing K₁] [HopfAlgebra Rh K₁] (q : 𝒢.level 1 →ₐc[Rh] K₁)

noncomputable abbrev sRh : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ JZeroNeronObjectAtP.base p :=
  Spec.map (CommRingCat.ofHom (algebraMap Rh (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom ρh)

include hρh in
theorem barPt_comp_sigmaA_eq_sRh : JZeroNeronObjectAtP.barPt Pl ≫ Λ.σA = sRh (p := p) ρh := by
  rw [Λ.hσA, sRh, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρh]

noncomputable def ptOf (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) : 𝒢.Point (AlgebraicClosure ℚ) 1 :=
  PDivisibleGroup.Point.ofAlgHom ((resPt η).comp (q : 𝒢.level 1 →ₐ[Rh] K₁))

theorem toAlgHom_ptOf (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) :
    PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q η) = (resPt η).comp (q : 𝒢.level 1 →ₐ[Rh] K₁) := rfl

theorem specMap_comp_iB_fst (η : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (η : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫ iB O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1) ≫
        pullback.fst O.g Λ.σA =
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q η) : 𝒢.level 1 →ₐ[Rh] AlgebraicClosure ℚ) :
        𝒢.level 1 →+* AlgebraicClosure ℚ)) ≫ ι 1 := by
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
  (hkerq : RingHom.ker (q : 𝒢.level 1 →+* K₁) =
    Ideal.map (ψ 1 : ℬ.level 1 →ₐ[Rh] 𝒢.level 1) (RingHom.ker (Bialgebra.counitAlgHom Rh (ℬ.level 1))))

theorem mul_castOver_val {T : Scheme.{0}} {s₁ s₂ : T ⟶ JZeroNeronObjectAtP.base p} (hs : s₁ = s₂) (a b : SchemeHomOver s₁ O.g) :
    (O.L.mul s₂ (JZeroNeronObjectAtP.castOver hs a) (JZeroNeronObjectAtP.castOver hs b)).1 = (O.L.mul s₁ a b).1 := by
  subst hs
  rfl

include hρh hιmul in

theorem hmul_iB (χ χ' : WithConv (↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ))
    (x x' xx' : SchemeHomOver (JZeroNeronObjectAtP.barPt Pl) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hx : x.1 = Spec.map (CommRingCat.ofHom (χ.ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1)).1)
    (hx' : x'.1 = Spec.map (CommRingCat.ofHom (χ'.ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1)).1)
    (hxx' : xx'.1 = Spec.map (CommRingCat.ofHom ((χ * χ').ofConv : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
      (iOver O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1)).1) :
    xx' = (O.L.baseChange Λ.σA).mul (JZeroNeronObjectAtP.barPt Pl) x x' := by
  have hs := barPt_comp_sigmaA_eq_sRh (Λ := Λ) ρh hρh

  have kx : x.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q χ.ofConv) :
      𝒢.level 1 →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level 1 →+* AlgebraicClosure ℚ)) ≫ ι 1 := by
    rw [hx, Category.assoc]; exact specMap_comp_iB_fst O ρh 𝒢 ι hιbase q χ.ofConv
  have kx' : x'.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q χ'.ofConv) :
      𝒢.level 1 →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level 1 →+* AlgebraicClosure ℚ)) ≫ ι 1 := by
    rw [hx', Category.assoc]; exact specMap_comp_iB_fst O ρh 𝒢 ι hιbase q χ'.ofConv
  have kxx' : xx'.1 ≫ pullback.fst O.g Λ.σA = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q (χ * χ').ofConv) :
      𝒢.level 1 →ₐ[Rh] AlgebraicClosure ℚ) : 𝒢.level 1 →+* AlgebraicClosure ℚ)) ≫ ι 1 := by
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
    change ((resPt (χ * χ').ofConv).comp (q : 𝒢.level 1 →ₐ[Rh] K₁)) a =
      PDivisibleGroup.Point.toAlgHom (ptOf 𝒢 q χ.ofConv * ptOf 𝒢 q χ'.ofConv) a
    rw [resPt_convMul, AlgHom.convMul_comp_bialgHom_distrib]
    rfl
  have H := hιmul 1 (AlgebraicClosure ℚ) (ptOf 𝒢 q χ.ofConv) (ptOf 𝒢 q χ'.ofConv) hX hX'
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

end FRAMEPTS
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

end T1Geom
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

namespace T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section FRAMEPTS2

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
  {K₁ : Type} [CommRing K₁] [HopfAlgebra Rh K₁] (q : 𝒢.level 1 →ₐc[Rh] K₁)
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
  (hkerq : RingHom.ker (q : 𝒢.level 1 →+* K₁) =
    Ideal.map (ψ 1 : ℬ.level 1 →ₐ[Rh] 𝒢.level 1) (RingHom.ker (Bialgebra.counitAlgHom Rh (ℬ.level 1))))

include hkerq in

theorem ofAlgHom_comp_psi_eq_one (χ₀ : K₁ →ₐ[Rh] AlgebraicClosure ℚ) :
    PDivisibleGroup.Point.ofAlgHom ((χ₀.comp (q : 𝒢.level 1 →ₐ[Rh] K₁)).comp (ψ 1 : ℬ.level 1 →ₐ[Rh] 𝒢.level 1)) =
      (1 : ℬ.Point (AlgebraicClosure ℚ) 1) := by
  apply PDivisibleGroup.Point.ext
  intro b
  rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.one_apply, AlgHom.comp_apply, AlgHom.comp_apply]
  change χ₀ (q (ψ 1 b)) = _
  rw [q_psi_apply (ψ 1) q hkerq, AlgHom.commutes]

include hkerq hq in

theorem exists_comp_q_eq (x : 𝒢.Point (AlgebraicClosure ℚ) 1)
    (hx : PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ 1 : ℬ.level 1 →ₐ[Rh] 𝒢.level 1)) =
      (1 : ℬ.Point (AlgebraicClosure ℚ) 1)) :
    ∃ χ₀ : K₁ →ₐ[Rh] AlgebraicClosure ℚ, χ₀.comp (q : 𝒢.level 1 →ₐ[Rh] K₁) = PDivisibleGroup.Point.toAlgHom x := by
  have hker : ∀ a ∈ RingHom.ker (q : 𝒢.level 1 →ₐ[Rh] K₁), PDivisibleGroup.Point.toAlgHom x a = 0 := by
    intro a ha
    have ha' : a ∈ RingHom.ker (q : 𝒢.level 1 →+* K₁) := ha
    rw [hkerq] at ha'
    refine Submodule.span_induction (p := fun a _ => PDivisibleGroup.Point.toAlgHom x a = 0) ?_ ?_ ?_ ?_ ha'
    · rintro _ ⟨b, hb, rfl⟩
      have := congr_arg (fun y : ℬ.Point (AlgebraicClosure ℚ) 1 => PDivisibleGroup.Point.toAlgHom y b) hx
      simp only [PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.comp_apply, PDivisibleGroup.Point.one_apply] at this
      rw [SetLike.mem_coe, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hb
      rw [this, hb, map_zero]
    · simp
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro r a _ ha; rw [smul_eq_mul, map_mul, ha, mul_zero]
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker (q : 𝒢.level 1 →ₐ[Rh] K₁)) (PDivisibleGroup.Point.toAlgHom x) hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom, ?_⟩
  apply AlgHom.ext
  intro c
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
  rw [show (q : 𝒢.level 1 →ₐ[Rh] K₁) c = (q : 𝒢.level 1 →ₐ[Rh] K₁) c from rfl,
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

include hιpts hψker htor hq hkerq in

theorem hpts_iB (y : JH M H) :
    y ∈ O.toricPts p ↔ ∃ χ : ↥Pl ⊗[Rh] K₁ →ₐ[↥Pl] AlgebraicClosure ℚ,
      (O.pts y).1 = Spec.map (CommRingCat.ofHom (χ : ↥Pl ⊗[Rh] K₁ →+* AlgebraicClosure ℚ)) ≫
        (iOver O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1)).1 ≫ pullback.fst O.g Λ.σA := by
  have htor1 := htor 1
  have hψker1 := hψker 1
  simp only [pow_one] at htor1 hψker1
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := htor1 y hy
    obtain ⟨χ₀, hχ₀⟩ := exists_comp_q_eq 𝒢 ℬ ψ q hq hkerq x ((hψker1 x).mpr hy)
    refine ⟨Algebra.TensorProduct.lift (Algebra.ofId ↥Pl (AlgebraicClosure ℚ)) χ₀ (fun _ _ => .all _ _), ?_⟩
    rw [hιpts]
    change _ = _ ≫ iB O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1) ≫ _
    rw [specMap_comp_iB_fst O ρh 𝒢 ι hιbase q, toAlgHom_ptOf, resPt_lift, hχ₀]
  · rintro ⟨χ, hχ⟩
    change _ = _ ≫ iB O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1) ≫ _ at hχ
    rw [specMap_comp_iB_fst O ρh 𝒢 ι hιbase q] at hχ
    have hone := ofAlgHom_comp_psi_eq_one 𝒢 ℬ ψ q hkerq (resPt χ)
    have hmem : Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) 1 (Additive.ofMul (ptOf 𝒢 q χ))) ∈ O.toricPts p :=
      (hψker1 _).mp hone
    have hyx : y = Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) 1 (Additive.ofMul (ptOf 𝒢 q χ))) := by
      apply O.pts.injective
      apply Subtype.ext
      rw [hχ, hιpts]
    rwa [hyx]

end FRAMEPTS2
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

end T1Geom
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

namespace T1Geom

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section RANK

variable (p : ℕ) [Fact p.Prime] {Rh : Type} [CommRing Rh] [IsDomain Rh] [IsLocalRing Rh]
  [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)] [Algebra Rh (ZMod p)]

noncomputable def residueEquiv (hker : RingHom.ker (algebraMap Rh (ZMod p)) = maximalIdeal Rh) :
    ResidueField Rh ≃ₐ[Rh] ZMod p :=
  (Ideal.quotientEquivAlgOfEq Rh (show maximalIdeal Rh = RingHom.ker (Algebra.ofId Rh (ZMod p)) from
      hker.symm.trans rfl)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId Rh (ZMod p)) (ZMod.ringHom_surjective (algebraMap Rh (ZMod p))))

theorem finrank_residueField_tensor_eq (hker : RingHom.ker (algebraMap Rh (ZMod p)) = maximalIdeal Rh)
    (K₁ : Type) [CommRing K₁] [Algebra Rh K₁] :
    Module.finrank (ResidueField Rh) (ResidueField Rh ⊗[Rh] K₁) = Module.finrank (ZMod p) (ZMod p ⊗[Rh] K₁) := by
  let eκ := residueEquiv p hker
  refine Algebra.finrank_eq_of_equiv_equiv eκ.toRingEquiv
    (Algebra.TensorProduct.congr eκ (AlgEquiv.refl : K₁ ≃ₐ[Rh] K₁)).toRingEquiv ?_
  ext r
  simp [Algebra.TensorProduct.algebraMap_apply]

noncomputable def algHomBaseChangeEquiv (K₁ : Type) [CommRing K₁] [Algebra Rh K₁] :
    (AlgebraicClosure ℚ ⊗[Rh] K₁ →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ) ≃ (K₁ →ₐ[Rh] AlgebraicClosure ℚ) where
  toFun ω := (ω.restrictScalars Rh).comp Algebra.TensorProduct.includeRight
  invFun χ₀ := Algebra.TensorProduct.lift (Algebra.ofId _ _) χ₀ (fun _ _ => .all _ _)
  left_inv ω := by
    apply Algebra.TensorProduct.ext'
    intro a k
    have h1 : ω (a ⊗ₜ[Rh] (1 : K₁)) = a := by
      rw [show a ⊗ₜ[Rh] (1 : K₁) = a • ((1 : AlgebraicClosure ℚ) ⊗ₜ[Rh] (1 : K₁)) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, ← Algebra.TensorProduct.one_def, map_one,
        smul_eq_mul, mul_one]
    calc Algebra.TensorProduct.lift (Algebra.ofId _ _) ((ω.restrictScalars Rh).comp Algebra.TensorProduct.includeRight)
          (fun _ _ => .all _ _) (a ⊗ₜ[Rh] k) = a * ω ((1 : AlgebraicClosure ℚ) ⊗ₜ[Rh] k) := by
            simp [Algebra.TensorProduct.lift_tmul]
      _ = ω (a ⊗ₜ[Rh] (1 : K₁)) * ω ((1 : AlgebraicClosure ℚ) ⊗ₜ[Rh] k) := by rw [h1]
      _ = ω (a ⊗ₜ[Rh] k) := by rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  right_inv χ₀ := by
    apply AlgHom.ext
    intro k
    simp

theorem free_of_finrank_zmod_tensor_eq_of_natCard_algHom_eq
    (hker : RingHom.ker (algebraMap Rh (ZMod p)) = maximalIdeal Rh)
    (K₁ : Type) [CommRing K₁] [HopfAlgebra Rh K₁] [Module.Finite Rh K₁] (n : ℕ)
    (h𝔽 : Module.finrank (ZMod p) (ZMod p ⊗[Rh] K₁) = n)
    (hpts : Nat.card (K₁ →ₐ[Rh] AlgebraicClosure ℚ) = n) : Module.Free Rh K₁ := by
  classical
  letI : Algebra (FractionRing Rh) (AlgebraicClosure ℚ) := FractionRing.liftAlgebra Rh (AlgebraicClosure ℚ)
  haveI : IsScalarTower Rh (FractionRing Rh) (AlgebraicClosure ℚ) := FractionRing.isScalarTower_liftAlgebra Rh _
  haveI : IsReduced (AlgebraicClosure ℚ ⊗[Rh] K₁) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero (AlgebraicClosure ℚ) _
  haveI : Module.Free (FractionRing Rh) (FractionRing Rh ⊗[Rh] K₁) := Module.Free.of_divisionRing _ _
  have hK : Module.finrank (FractionRing Rh) (FractionRing Rh ⊗[Rh] K₁) = n :=
    calc Module.finrank (FractionRing Rh) (FractionRing Rh ⊗[Rh] K₁)
        = Module.finrank (AlgebraicClosure ℚ) (AlgebraicClosure ℚ ⊗[FractionRing Rh] (FractionRing Rh ⊗[Rh] K₁)) :=
          (Module.finrank_baseChange (R := AlgebraicClosure ℚ) (S := FractionRing Rh) (M' := FractionRing Rh ⊗[Rh] K₁)).symm
      _ = Module.finrank (AlgebraicClosure ℚ) (AlgebraicClosure ℚ ⊗[Rh] K₁) :=
          LinearEquiv.finrank_eq (TensorProduct.AlgebraTensorModule.cancelBaseChange Rh (FractionRing Rh)
            (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) K₁)
      _ = Nat.card (AlgebraicClosure ℚ ⊗[Rh] K₁ →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ) :=
          (AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed (AlgebraicClosure ℚ) (AlgebraicClosure ℚ ⊗[Rh] K₁)).symm
      _ = Nat.card (K₁ →ₐ[Rh] AlgebraicClosure ℚ) := Nat.card_congr (algHomBaseChangeEquiv K₁)
      _ = n := hpts
  have hκ : Module.finrank (ResidueField Rh) (ResidueField Rh ⊗[Rh] K₁) = n := by
    rw [finrank_residueField_tensor_eq p hker, h𝔽]
  exact (Module.free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq n hκ hK).1

end RANK
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

end T1Geom
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

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
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

end T1Geom
p2m_reactivate "P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness.T1Geom"

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

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

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

    (hjB : ∀ v, Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)))

    (T : ℕ → Type) [∀ v, CommRing (T v)] [∀ v, HopfAlgebra (ZMod p) (T v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (T v)] [∀ v, Module.Finite (ZMod p) (T v)] [∀ v, Module.Free (ZMod p) (T v)]
    (tT : ∀ v, T (v + 1) →ₐc[ZMod p] T v)
    (πT : ∀ v : ℕ, ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] T v)
    (htT : ∀ v, Function.Surjective (tT v))
    (hrankT : ∀ v, Module.finrank (ZMod p) (T v) = p ^ (v * O.toricRank))
    (hkerT : ∀ v, RingHom.ker (tT v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (T (v + 1)) (p ^ v))
    (hπT : ∀ v, Function.Surjective (πT v))
    (hπTt : ∀ v : ℕ, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (tT v).comp (πT (v + 1)))
    (hexT : ∀ v : ℕ, RingHom.ker (πT v : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] T v) =
      Ideal.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v) : ZMod p ⊗[Rh] ℬ.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)
        (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[Rh] ℬ.level v))))

    [Algebra (ZMod p) (IsLocalRing.ResidueField ↥Pl)] :
    Nonempty ((IsLocalRing.ResidueField ↥Pl) ⊗[ZMod p] T 1 ≃ₐc[IsLocalRing.ResidueField ↥Pl]
      (IsLocalRing.ResidueField ↥Pl) ⊗[ZMod p] AddMonoidAlgebra (ZMod p) (Fin O.toricRank → ZMod p)) := by
  classical

  letI algRP : Algebra Rh ↥Pl := ((algebraMap Rh (AlgebraicClosure ℚ)).codRestrict Pl hRA).toAlgebra
  haveI : IsScalarTower Rh ↥Pl (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI algRκ : Algebra Rh (IsLocalRing.ResidueField ↥Pl) :=
    ((IsLocalRing.residue ↥Pl).comp (algebraMap Rh ↥Pl)).toAlgebra
  haveI : IsScalarTower Rh ↥Pl (IsLocalRing.ResidueField ↥Pl) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Rh (ZMod p) (IsLocalRing.ResidueField ↥Pl) :=
    IsScalarTower.of_algebraMap_eq fun x => (T1Geom.residue_compat (p := p) (Pl := Pl) hres x).symm
  have hker : RingHom.ker (algebraMap Rh (ZMod p)) = IsLocalRing.maximalIdeal Rh := by
    ext x; rw [RingHom.mem_ker, hres, hRloc]
  haveI : IsLocalRing Rh := inferInstance

  obtain ⟨K₁, _, _, q, hq, hkerq, -, hfinK⟩ :=
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit (ψ 1)
  haveI : Module.Finite Rh K₁ := hfinK inferInstance

  obtain ⟨eT, heT⟩ :=
    Bialgebra.exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit (ZMod p)
      (ψ 1) q hq hkerq (πT 1) (hπT 1) (hexT 1)
  have h𝔽 : Module.finrank (ZMod p) (ZMod p ⊗[Rh] K₁) = p ^ O.toricRank := by
    rw [← LinearEquiv.finrank_eq (eT : T 1 ≃ₐc[ZMod p] ZMod p ⊗[Rh] K₁).toLinearEquiv, hrankT 1, one_mul]

  obtain ⟨-, -, -, hcard⟩ :=
    ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard p M H hpM Pl hPl Λ O p
      (Nat.Prime.pos (Fact.out))
  have hψker1 := hψker 1
  have htor1 := htor 1
  simp only [pow_one] at hψker1 htor1
  have hpts_card : Nat.card (K₁ →ₐ[Rh] AlgebraicClosure ℚ) = p ^ O.toricRank := by
    rw [← hcard]

    let F : (K₁ →ₐ[Rh] AlgebraicClosure ℚ) → ↥(O.toricPts p) := fun χ₀ =>
      ⟨Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) 1 (Additive.ofMul
        (PDivisibleGroup.Point.ofAlgHom (χ₀.comp (q : 𝒢.level 1 →ₐ[Rh] K₁))))),
        (hψker1 _).mp (by
          rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom]
          exact T1Geom.ofAlgHom_comp_psi_eq_one 𝒢 ℬ ψ q hkerq χ₀)⟩
    apply Nat.card_eq_of_bijective F
    constructor
    · intro χ₁ χ₂ hχ
      have h1 := congr_arg Subtype.val hχ
      simp only [F] at h1
      have h2 := hΔinj h1
      rw [PDivisibleGroup.pointsMkAdd_eq_pointsMkAdd_iff] at h2
      have h3 := congr_arg PDivisibleGroup.Point.toAlgHom (Additive.ofMul.injective h2)
      apply AlgHom.ext
      intro k
      obtain ⟨c, rfl⟩ := hq k
      exact DFunLike.congr_fun h3 c
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := htor1 y hy
      obtain ⟨χ₀, hχ₀⟩ := T1Geom.exists_comp_q_eq 𝒢 ℬ ψ q hq hkerq x ((hψker1 x).mpr hy)
      refine ⟨χ₀, Subtype.ext ?_⟩
      simp only [F, hχ₀, PDivisibleGroup.Point.ofAlgHom_toAlgHom]

  haveI : Module.Free Rh K₁ :=
    T1Geom.free_of_finrank_zmod_tensor_eq_of_natCard_algHom_eq p hker K₁ (p ^ O.toricRank) h𝔽 hpts_card
  haveI : Module.Flat ↥Pl (↥Pl ⊗[Rh] K₁) := inferInstance
  haveI : Module.Finite ↥Pl (↥Pl ⊗[Rh] K₁) := inferInstance

  have hcl : IsClosedImmersion (T1Geom.iOver O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1)).1 :=
    T1Geom.isClosedImmersion_iB O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1) hq (hιcl 1 (hιbase 1))
  obtain ⟨e, -, -⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff
      p M H hpM Pl hPl Λ O p (Nat.Prime.pos Fact.out) (↥Pl ⊗[Rh] K₁)
      (T1Geom.iOver O ρh (q : 𝒢.level 1 →ₐ[Rh] K₁) (ι 1) (hιbase 1)) hcl
      (fun χ χ' x x' xx' hx hx' hxx' => T1Geom.hmul_iB O ρh hρh 𝒢 ι hιbase q hιmul χ χ' x x' xx' hx hx' hxx')
      (fun y => T1Geom.hpts_iB O ρh 𝒢 ℬ ψ Δ ι hιbase q hιpts hψker htor hq hkerq y)

  obtain ⟨c𝔽, -⟩ := Bialgebra.exists_bialgEquiv_cancelBaseChange_tmul Rh (ZMod p) (IsLocalRing.ResidueField ↥Pl) K₁
  obtain ⟨cPl, -⟩ := Bialgebra.exists_bialgEquiv_cancelBaseChange_tmul Rh ↥Pl (IsLocalRing.ResidueField ↥Pl) K₁
  obtain ⟨gPl, -⟩ := AddMonoidAlgebra.exists_bialgEquiv_baseChange_tmul_single ↥Pl (IsLocalRing.ResidueField ↥Pl)
    (Fin O.toricRank → ZMod p)
  obtain ⟨g𝔽, -⟩ := AddMonoidAlgebra.exists_bialgEquiv_baseChange_tmul_single (ZMod p) (IsLocalRing.ResidueField ↥Pl)
    (Fin O.toricRank → ZMod p)
  exact ⟨(T1Geom.bialgEquivBaseChange (IsLocalRing.ResidueField ↥Pl) eT).trans
    (c𝔽.trans (cPl.symm.trans ((T1Geom.bialgEquivBaseChange (IsLocalRing.ResidueField ↥Pl) e).trans (gPl.trans g𝔽.symm))))⟩

end S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness
end P2MW
export P2MW.S_ModularCurve_nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness (solution)
