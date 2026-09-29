-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8a271559-6729-5b0a-91d1-40bab8ae3098

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_conj_muHom_baseChange
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv
import Theorems.Thm_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false

universe u

noncomputable section

namespace TLGalD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

variable {N₀ p : ℕ} [NeZero N₀] {A : ValuationSubring (AlgebraicClosure ℚ)} {Λ : LevelData N₀ p A}

abbrev sigA (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) : ↥A ≃+* ↥A :=
  MulSemiringAction.toRingAut _ ↥A σ

abbrev sigK (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) :
    ResidueField ↥A ≃+* ResidueField ↥A :=
  MulSemiringAction.toRingAut _ (ResidueField ↥A) σ

abbrev specSigA (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) :
    Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥A) :=
  Spec.map (CommRingCat.ofHom (sigA A σ).toRingHom)

abbrev specSigK (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : ↥(A.decompositionSubgroup ℚ)) :
    Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of (ResidueField ↥A)) :=
  Spec.map (CommRingCat.ofHom (sigK A σ).toRingHom)

theorem coe_sigA (σ : ↥(A.decompositionSubgroup ℚ)) (x : ↥A) :
    ((sigA A σ x : ↥A) : AlgebraicClosure ℚ) = (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x := rfl

theorem sigK_residue (σ : ↥(A.decompositionSubgroup ℚ)) :
    (sigK A σ).toRingHom.comp (residue ↥A) = (residue ↥A).comp (sigA A σ).toRingHom := by
  rfl

theorem barPt_specSigA (σ : ↥(A.decompositionSubgroup ℚ)) :
    barPt A ≫ specSigA A σ =
      Spec.map (CommRingCat.ofHom ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        barPt A := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem resPt_specSigA (σ : ↥(A.decompositionSubgroup ℚ)) :
    resPt A ≫ specSigA A σ = specSigK A σ ≫ resPt A := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem specGal_genPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  show σ (algebraMap (baseRing p) (AlgebraicClosure ℚ) r) = algebraMap _ _ r
  have hr : algebraMap (baseRing p) (AlgebraicClosure ℚ) r = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := rfl
  rw [hr, AlgEquiv.commutes]

theorem specSigA_σA (σ : ↥(A.decompositionSubgroup ℚ)) : specSigA A σ ≫ Λ.σA = Λ.σA := by
  let u : CommRingCat.of (baseRing p) ⟶ CommRingCat.of ↥A := Spec.preimage (specSigA A σ ≫ Λ.σA)
  let v : CommRingCat.of (baseRing p) ⟶ CommRingCat.of ↥A := Spec.preimage Λ.σA
  have hu : Spec.map u = specSigA A σ ≫ Λ.σA := Spec.map_preimage _
  have hv : Spec.map v = Λ.σA := Spec.map_preimage _
  have hgen : barPt A ≫ (specSigA A σ ≫ Λ.σA) = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, barPt_specSigA, Category.assoc, Λ.hσA, specGal_genPt]
  rw [← hu, ← hv] at hgen
  change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map u = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map v at hgen
  rw [← Spec.map_comp, ← Spec.map_comp] at hgen
  have h2 := Spec.map_injective hgen
  have h3 : u = v := by
    ext r
    have h2' : (u ≫ CommRingCat.ofHom A.subtype).hom r = (v ≫ CommRingCat.ofHom A.subtype).hom r := by rw [h2]
    first | exact h2' | exact Subtype.val_injective h2' | exact congrArg Subtype.val h2'
  rw [← hu, ← hv, h3]

theorem specSigK_resPt_σA (σ : ↥(A.decompositionSubgroup ℚ)) :
    specSigK A σ ≫ (resPt A ≫ Λ.σA) = resPt A ≫ Λ.σA := by
  rw [← Category.assoc, ← resPt_specSigA, Category.assoc, specSigA_σA]

theorem sigK_eq_refl_of_mem_inertia {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    ∃ d : ↥(A.decompositionSubgroup ℚ), (d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = σ ∧ sigK A d = RingEquiv.refl _ := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  refine ⟨d, rfl, ?_⟩
  have : MulSemiringAction.toRingAut (↥(A.decompositionSubgroup ℚ)) (ResidueField ↥A) d = 1 := by
    simpa [ValuationSubring.inertiaSubgroup] using hd
  exact this

theorem mem_decomposition_of_mem_inertia {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : σ ∈ A.decompositionSubgroup ℚ := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  exact d.2

def twChar (σ : ↥(A.decompositionSubgroup ℚ)) {t m : ℕ} (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ where
  toRingHom := ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
    (χ.toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (sigA A σ).symm.toRingHom))
  commutes' a := by
    show (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (χ (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (sigA A σ).symm.toRingHom (algebraMap (↥A) (muCoord ↥A t m) a))) =
        algebraMap (↥A) (AlgebraicClosure ℚ) a
    have h1 : AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (sigA A σ).symm.toRingHom (algebraMap (↥A) (muCoord ↥A t m) a) =
        algebraMap (↥A) (muCoord ↥A t m) ((sigA A σ).symm a) := by
      simp [AddMonoidAlgebra.mapRingHom, AddMonoidAlgebra.coe_algebraMap]
    rw [h1, AlgHom.commutes]
    show (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (((sigA A σ).symm a : ↥A) : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ)
    rw [← coe_sigA σ ((sigA A σ).symm a), RingEquiv.apply_symm_apply]

theorem twChar_comp (σ : ↥(A.decompositionSubgroup ℚ)) {t m : ℕ} (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    (twChar σ χ).toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (sigA A σ).toRingHom) =
      ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp χ.toRingHom := by
  show (((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
    (χ.toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (sigA A σ).symm.toRingHom))).comp
      (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (sigA A σ).toRingHom) = _
  simp only [RingHom.comp_assoc]
  congr 1
  conv_rhs => rw [← RingHom.comp_id χ.toRingHom]
  congr 1
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun v => ?_) <;> simp [AddMonoidAlgebra.mapRingHom]

theorem specGal_muPt (σ : ↥(A.decompositionSubgroup ℚ)) {t m : ℕ} (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        (muPt A t m χ).1 =
      (muPt A t m (twChar σ χ)).1 ≫ muBaseChange (sigA A σ).toRingHom t m := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, twChar_comp]

end TLGalD

end

noncomputable section

namespace TLGalLat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SplitTorus

variable {t : ℕ}

abbrev castPi (t m : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

theorem castPi_apply (m : ℕ) (x : Fin t → ℤ) (i : Fin t) : castPi t m x i = (x i : ZMod m) := rfl

def liftPi (m : ℕ) (v : Fin t → ZMod m) : Fin t → ℤ := fun i => (v i).cast

theorem castPi_liftPi (m : ℕ) (v : Fin t → ZMod m) : castPi t m (liftPi m v) = v := by
  funext i; simp [castPi_apply, liftPi, ZMod.intCast_zmod_cast]

theorem castPi_eq_castPi_iff (m : ℕ) (x y : Fin t → ℤ) :
    castPi t m x = castPi t m y ↔ ∃ c : Fin t → ℤ, x - y = m • c := by
  constructor
  · intro h
    have hi : ∀ i, (m : ℤ) ∣ x i - y i := fun i => by
      have := congrFun h i
      simp only [castPi_apply] at this
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub (y i) (x i) m).mp this.symm
    choose c hc using hi
    refine ⟨c, funext fun i => ?_⟩
    simp [hc i, mul_comm]
  · rintro ⟨c, hc⟩
    funext i
    have := congrFun hc i
    simp only [Pi.sub_apply, Pi.smul_apply] at this
    simp only [castPi_apply]
    rw [show x i = y i + m • c i by rw [← this]; abel]
    simp [nsmul_eq_mul]

theorem castPi_map_eq (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) {x y : Fin t → ℤ}
    (h : castPi t m x = castPi t m y) : castPi t m (M x) = castPi t m (M y) := by
  obtain ⟨c, hc⟩ := (castPi_eq_castPi_iff m x y).mp h
  refine (castPi_eq_castPi_iff m (M x) (M y)).mpr ⟨M c, ?_⟩
  rw [← map_sub, hc, map_nsmul]

def latRed (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) : (Fin t → ZMod m) →+ (Fin t → ZMod m) where
  toFun v := castPi t m (M (liftPi m v))
  map_zero' := by
    have h : castPi t m (liftPi m (0 : Fin t → ZMod m)) = castPi t m 0 := by rw [castPi_liftPi, map_zero]
    rw [castPi_map_eq M m h, map_zero, map_zero]
  map_add' v w := by
    have h : castPi t m (liftPi m (v + w)) = castPi t m (liftPi m v + liftPi m w) := by
      rw [map_add, castPi_liftPi, castPi_liftPi, castPi_liftPi]
    rw [castPi_map_eq M m h, map_add, map_add]

theorem latRed_castPi (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) (x : Fin t → ℤ) :
    latRed M m (castPi t m x) = castPi t m (M x) := by
  show castPi t m (M (liftPi m (castPi t m x))) = _
  exact castPi_map_eq M m (castPi_liftPi m _)

theorem latRed_comp_castPi (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) :
    (latRed M m).comp (castPi t m) = (castPi t m).comp M := by
  ext x i; simp only [AddMonoidHom.comp_apply, latRed_castPi]

variable (S : Type u) [CommRing S]

abbrev dTorus (M : (Fin t → ℤ) →+ (Fin t → ℤ)) : torusScheme S t ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S M))

abbrev dMu (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) : muScheme S t m ⟶ muScheme S t m :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (latRed M m)))

theorem mapDomainRingHom_comp_eq {G H K : Type} [AddCommMonoid G] [AddCommMonoid H] [AddCommMonoid K]
    (f : G →+ H) (g : H →+ K) :
    (AddMonoidAlgebra.mapDomainRingHom S g).comp (AddMonoidAlgebra.mapDomainRingHom S f) =
      AddMonoidAlgebra.mapDomainRingHom S (g.comp f) := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun v => ?_) <;>
    simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]

theorem dMu_comp_muToTorus (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) :
    dMu S M m ≫ muToTorus S t m = muToTorus S t m ≫ dTorus S M := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  show (AddMonoidAlgebra.mapDomainRingHom S (latRed M m)).comp (AddMonoidAlgebra.mapDomainRingHom S (castPi t m)) =
    (AddMonoidAlgebra.mapDomainRingHom S (castPi t m)).comp (AddMonoidAlgebra.mapDomainRingHom S M)
  rw [mapDomainRingHom_comp_eq, mapDomainRingHom_comp_eq, latRed_comp_castPi]

theorem muBaseChange_comp_dMu {S' : Type u} [CommRing S'] (φ : S →+* S') (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) :
    muBaseChange φ t m ≫ dMu S M m = dMu S' M m ≫ muBaseChange φ t m := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun v => ?_) <;>
    simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapRingHom]

theorem dMu_comp_muStr (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) : dMu S M m ≫ muStr S t m = muStr S t m := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (AddMonoidAlgebra.mapDomainAlgHom S S (latRed M m)).comp_algebraMap

abbrev dAlg (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) : muCoord S t m →ₐ[S] muCoord S t m :=
  AddMonoidAlgebra.mapDomainAlgHom S S (latRed M m)

theorem dAlg_toRingHom (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ) :
    (dAlg S M m).toRingHom = AddMonoidAlgebra.mapDomainRingHom S (latRed M m) := rfl

theorem comp_dAlg_mul (S' : Type u) [CommRing S'] [Algebra S S'] (M : (Fin t → ℤ) →+ (Fin t → ℤ)) (m : ℕ)
    (χ χ' : WithConv (muCoord S t m →ₐ[S] S')) :
    WithConv.toConv ((χ * χ').ofConv.comp (dAlg S M m)) =
      WithConv.toConv (χ.ofConv.comp (dAlg S M m)) * WithConv.toConv (χ'.ofConv.comp (dAlg S M m)) := by
  have hgl : ∀ (φ ψ : WithConv (muCoord S t m →ₐ[S] S')) (g : Fin t → ZMod m),
      (φ * ψ).ofConv (AddMonoidAlgebra.single g 1) =
        φ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
    intro φ ψ g
    rw [AlgHom.convMul_def]
    simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]
  have hF : ∀ g : Fin t → ZMod m, dAlg S M m (AddMonoidAlgebra.single g 1) = AddMonoidAlgebra.single (latRed M m g) 1 := by
    intro g; simp [AddMonoidAlgebra.mapDomain_single]
  apply WithConv.ofConv_injective
  show (χ * χ').ofConv.comp (dAlg S M m) =
    (WithConv.toConv (χ.ofConv.comp (dAlg S M m)) * WithConv.toConv (χ'.ofConv.comp (dAlg S M m))).ofConv
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro g
  rw [hgl, AlgHom.comp_apply, hF, hgl]
  simp only [WithConv.ofConv_toConv, AlgHom.comp_apply, hF]

theorem muBaseChange_comp_muToTorus {S' : Type u} [CommRing S'] (φ : S →+* S') (m : ℕ) :
    muBaseChange φ t m ≫ muToTorus S t m = muToTorus S' t m ≫ torusBaseChange φ t := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun v => ?_) <;>
    simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapRingHom]

theorem convPow_apply_single (S' : Type u) [CommRing S'] [Algebra S S'] (m : ℕ)
    (χ : WithConv (muCoord S t m →ₐ[S] S')) (c : ℕ) (v : Fin t → ZMod m) :
    (χ ^ c).ofConv (AddMonoidAlgebra.single v 1) = (χ.ofConv (AddMonoidAlgebra.single v 1)) ^ c := by
  have hgl : ∀ (φ ψ : WithConv (muCoord S t m →ₐ[S] S')) (g : Fin t → ZMod m),
      (φ * ψ).ofConv (AddMonoidAlgebra.single g 1) =
        φ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
    intro φ ψ g
    rw [AlgHom.convMul_def]
    simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]
  have hone : ∀ g : Fin t → ZMod m, (1 : WithConv (muCoord S t m →ₐ[S] S')).ofConv (AddMonoidAlgebra.single g 1) = 1 := by
    intro g
    rw [AlgHom.convOne_def]
    simp [AddMonoidAlgebra.counit_single]
  induction c with
  | zero => rw [pow_zero, pow_zero, hone]
  | succ k ih => rw [pow_succ, hgl, ih, pow_succ]

theorem apply_single_pow_eq_one (S' : Type u) [CommRing S'] [Algebra S S'] (m : ℕ)
    (χ : muCoord S t m →ₐ[S] S') (v : Fin t → ZMod m) : (χ (AddMonoidAlgebra.single v 1)) ^ m = 1 := by
  rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
  have hmv : m • v = 0 := by funext j; simp
  rw [hmv]
  exact map_one χ

end TLGalLat

end

section rangestab
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

namespace TLGalGlue

section plumbing

theorem toFibrePt_ofFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : toFibrePt (ofFibrePt y) = y := by
  apply Subtype.ext
  show pullback.lift (y.1 ≫ pullback.fst f ι) (𝟙 _) _ = y.1
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
  · rw [pullback.lift_snd]; exact y.2.symm

theorem ofFibrePt_toFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver ι f) : ofFibrePt (toFibrePt x) = x := by
  apply Subtype.ext
  show pullback.lift x.1 (𝟙 _) _ ≫ pullback.fst f ι = x.1
  rw [pullback.lift_fst]

theorem ofFibrePt_coe {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : (ofFibrePt y).1 = y.1 ≫ pullback.fst f ι := rfl

theorem ofFibrePt_injective {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    {y y' : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)} (h : ofFibrePt y = ofFibrePt y') : y = y' := by
  rw [← toFibrePt_ofFibrePt y, ← toFibrePt_ofFibrePt y', h]

theorem ofFibrePt_one {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) : ofFibrePt ((L.baseChange ι).one (𝟙 _)) = L.one ι := by
  apply Subtype.ext
  rw [ofFibrePt_coe, RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  have h := congrArg Subtype.val (L.one_natural ι (𝟙 _ ≫ ι) (𝟙 _) rfl)
  rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at h
  exact h.symm

theorem comp_schemeHomOverComp {B T T' X Y : Scheme.{0}} {t : T ⟶ B} {t' : T' ⟶ B} {f : X ⟶ B} {f' : Y ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) (φ : SchemeHomOver f f') :
    NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ x) φ =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x φ) :=
  Subtype.ext (Category.assoc _ _ _)

theorem base_mem_range_iff_exists_comp {κ : Type} [Field κ] {Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (y : Spec (CommRingCat.of κ) ⟶ Y) :
    y.base (closedPoint κ) ∈ Set.range i.base ↔ ∃ z : Spec (CommRingCat.of κ) ⟶ Z, z ≫ i = y := by
  constructor
  · intro h
    have H : Set.range y.base ⊆ Set.range i.base := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q (closedPoint κ)]
      exact h
    obtain ⟨z, hz, -⟩ := AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i y H
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.base (closedPoint κ), rfl⟩

end plumbing

end TLGalGlue

theorem TLGalGlue.range_twist_eq_range
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ ModularCurve.JZeroNeronObjectAtP.base p) [Smooth g]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : ModularCurve.JZeroNeronObjectAtP.LevelData N₀ p A)
    (toricRank : ℕ)
    (torusFibre : SchemeHomOver (torusStr (ResidueField ↥A) toricRank)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g))
    (torusFibre_isClosedImmersion : IsClosedImmersion torusFibre.1)
    (abqFibre : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
    (abqFibre_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abqFibre i) =
          (Λ.L.baseChange (resPt A ≫ Λ.σA)).one s) ↔
        ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) toricRank),
          NeronModelInfra.schemeHomOverComp y torusFibre = x)
    (abqFibre_twist : ∀ (β : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)) (i : Fin 2)
      (x : SchemeHomOver (resPt A ≫ Λ.σA) g),
      fibreMap (abqFibre i) (GoodReductionJacobian.schemeHomOverComp β.1 β.2 x) =
        GoodReductionJacobian.schemeHomOverComp β.1 β.2 (fibreMap (abqFibre i) x))

    (sbar : ResidueField ↥A ≃+* ResidueField ↥A)
    (hsbar : Spec.map (CommRingCat.ofHom sbar.toRingHom) ≫ (resPt A ≫ Λ.σA) = resPt A ≫ Λ.σA)

    (Tw : pullback g (resPt A ≫ Λ.σA) ≅ pullback g (resPt A ≫ Λ.σA))
    (τ' : SchemeHomOver (torusStr (ResidueField ↥A) toricRank) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g))
    (hTw1 : Tw.hom ≫ pullback.fst g (resPt A ≫ Λ.σA) = pullback.fst g (resPt A ≫ Λ.σA))
    (hTw2 : Tw.hom ≫ pullback.snd g (resPt A ≫ Λ.σA) =
      pullback.snd g (resPt A ≫ Λ.σA) ≫ Spec.map (CommRingCat.ofHom sbar.symm.toRingHom))
    (hτ' : τ'.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin toricRank → ℤ) sbar.toRingHom)) ≫
      torusFibre.1 ≫ Tw.hom)
    (hτ'ci : IsClosedImmersion τ'.1) :
    Set.range τ'.1.base = Set.range torusFibre.1.base := by
  haveI := torusFibre_isClosedImmersion
  haveI := hτ'ci
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  have hSSi : Spec.map (CommRingCat.ofHom sbar.toRingHom) ≫ Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id]
  have hSiS : Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom sbar.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id]
  haveI : IsIso (Spec.map (CommRingCat.ofHom sbar.toRingHom)) := ⟨⟨_, hSSi, hSiS⟩⟩
  haveI : IsIso (Spec.map (CommRingCat.ofHom sbar.symm.toRingHom)) := ⟨⟨_, hSiS, hSSi⟩⟩
  have hBCi : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin toricRank → ℤ) sbar.symm.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin toricRank → ℤ) sbar.toRingHom)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AddMonoidAlgebra.mapRingHom_comp,
      RingEquiv.symm_toRingHom_comp_toRingHom, AddMonoidAlgebra.mapRingHom_id, CommRingCat.ofHom_id, Spec.map_id]
  have hsbar' : Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ≫ (resPt A ≫ Λ.σA) = resPt A ≫ Λ.σA := by
    conv_lhs => rw [← hsbar]
    rw [← Category.assoc, hSiS, Category.id_comp]

  have hTwinv_fst : Tw.inv ≫ pullback.fst g (resPt A ≫ Λ.σA) = pullback.fst g (resPt A ≫ Λ.σA) := by
    rw [Iso.inv_comp_eq, hTw1]
  have hTwinv_snd : Tw.inv ≫ pullback.snd g (resPt A ≫ Λ.σA) =
      pullback.snd g (resPt A ≫ Λ.σA) ≫ Spec.map (CommRingCat.ofHom sbar.toRingHom) := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hTw2, Category.assoc, hSiS, Category.comp_id]

  apply AlgebraicGeometry.eq_of_isClosed_of_forall_rationalPoint_mem_iff
    (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g) τ'.1.isClosedEmbedding.isClosed_range
    torusFibre.1.isClosedEmbedding.isClosed_range
  intro y hy
  rw [TLGalGlue.base_mem_range_iff_exists_comp τ'.1 y, TLGalGlue.base_mem_range_iff_exists_comp torusFibre.1 y]

  have hb : (∃ z : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ _, z ≫ τ'.1 = y) ↔
      ∃ z : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ _, z ≫ torusFibre.1 = y ≫ Tw.inv := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin toricRank → ℤ) sbar.toRingHom)), ?_⟩
      rw [hτ'] at hz
      rw [Category.assoc, Iso.eq_comp_inv, Category.assoc]
      exact hz
    · rintro ⟨z, hz⟩
      refine ⟨z ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin toricRank → ℤ) sbar.symm.toRingHom)), ?_⟩
      rw [hτ', Category.assoc, ← Category.assoc (Spec.map _) (Spec.map _), hBCi, Category.id_comp, ← Category.assoc, hz,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hb]

  have hy2 : (y ≫ Tw.inv) ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g = Spec.map (CommRingCat.ofHom sbar.toRingHom) := by
    show (y ≫ Tw.inv) ≫ pullback.snd g (resPt A ≫ Λ.σA) = _
    rw [Category.assoc, hTwinv_snd, ← Category.assoc]
    change (y ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g) ≫ _ = _
    rw [hy, Category.id_comp]
  have e0 : (∃ z : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ _, z ≫ torusFibre.1 = y) ↔
      ∃ w : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) toricRank),
        NeronModelInfra.schemeHomOverComp w torusFibre = ⟨y, hy⟩ := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
      rw [← torusFibre.2, ← Category.assoc, hz]; exact hy
    · rintro ⟨w, hw⟩; exact ⟨w.1, congrArg Subtype.val hw⟩
  have e1 : (∃ z : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ _, z ≫ torusFibre.1 = y ≫ Tw.inv) ↔
      ∃ w : SchemeHomOver (Spec.map (CommRingCat.ofHom sbar.toRingHom)) (torusStr (ResidueField ↥A) toricRank),
        NeronModelInfra.schemeHomOverComp w torusFibre = ⟨y ≫ Tw.inv, hy2⟩ := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
      rw [← torusFibre.2, ← Category.assoc, hz]; exact hy2
    · rintro ⟨w, hw⟩; exact ⟨w.1, congrArg Subtype.val hw⟩
  rw [e0, e1, ← abqFibre_eq_one_iff, ← abqFibre_eq_one_iff]

  have hw2 : (Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ≫ y ≫ Tw.inv) ≫
      RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g = 𝟙 _ := by
    rw [Category.assoc, hy2, hSiS]
  have hx1 : (⟨y ≫ Tw.inv, hy2⟩ : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)) =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom sbar.toRingHom)) (Category.comp_id _)
        ⟨Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ≫ y ≫ Tw.inv, hw2⟩ := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, hSSi, Category.id_comp]
  have key1 : ∀ i, NeronModelInfra.schemeHomOverComp (⟨y ≫ Tw.inv, hy2⟩ : SchemeHomOver _ _) (abqFibre i) =
        (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (Spec.map (CommRingCat.ofHom sbar.toRingHom)) ↔
      NeronModelInfra.schemeHomOverComp
          (⟨Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ≫ y ≫ Tw.inv, hw2⟩ : SchemeHomOver _ _) (abqFibre i) =
        (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    intro i
    rw [hx1, TLGalGlue.comp_schemeHomOverComp,
      ← (Λ.L.baseChange (resPt A ≫ Λ.σA)).one_natural (𝟙 _) (Spec.map (CommRingCat.ofHom sbar.toRingHom))
        (Spec.map (CommRingCat.ofHom sbar.toRingHom)) (Category.comp_id _)]
    constructor
    · intro h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      rw [GoodReductionJacobian.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe] at h'
      exact (cancel_epi _).mp h'
    · intro h; rw [h]
  have key0 : ∀ i,
      NeronModelInfra.schemeHomOverComp
          (⟨Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ≫ y ≫ Tw.inv, hw2⟩ : SchemeHomOver _ _) (abqFibre i) =
        (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) ↔
      NeronModelInfra.schemeHomOverComp (⟨y, hy⟩ : SchemeHomOver _ _) (abqFibre i) =
        (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    intro i

    have hW : ofFibrePt (⟨Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ≫ y ≫ Tw.inv, hw2⟩ : SchemeHomOver _ _) =
        GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom sbar.symm.toRingHom)) hsbar'
          (ofFibrePt (⟨y, hy⟩ : SchemeHomOver _ _)) := by
      apply Subtype.ext
      rw [TLGalGlue.ofFibrePt_coe, GoodReductionJacobian.schemeHomOverComp_coe, TLGalGlue.ofFibrePt_coe, Category.assoc,
        Category.assoc, hTwinv_fst]
    have htw := abqFibre_twist ⟨Spec.map (CommRingCat.ofHom sbar.symm.toRingHom), hsbar'⟩ i (ofFibrePt (⟨y, hy⟩ : SchemeHomOver _ _))

    change ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt _) (abqFibre i)) =
      GoodReductionJacobian.schemeHomOverComp _ _ (ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt _) (abqFibre i))) at htw
    rw [← hW, TLGalGlue.toFibrePt_ofFibrePt, TLGalGlue.toFibrePt_ofFibrePt] at htw
    constructor
    · intro h
      rw [h, TLGalGlue.ofFibrePt_one, ← Λ.L.one_natural (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)
        (Spec.map (CommRingCat.ofHom sbar.symm.toRingHom)) hsbar'] at htw
      have h' := congrArg Subtype.val htw
      rw [GoodReductionJacobian.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe] at h'
      apply TLGalGlue.ofFibrePt_injective
      rw [TLGalGlue.ofFibrePt_one]
      exact Subtype.ext ((cancel_epi _).mp h').symm
    · intro h
      rw [h, TLGalGlue.ofFibrePt_one, Λ.L.one_natural] at htw
      apply TLGalGlue.ofFibrePt_injective
      rw [TLGalGlue.ofFibrePt_one]
      exact htw
  exact ⟨fun h i => (key0 i).mp ((key1 i).mp (h i)), fun h i => (key1 i).mpr ((key0 i).mpr (h i))⟩

end rangestab

section head
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP TLGalD TLGalLat

set_option maxHeartbeats 6400000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime]

    {G : Scheme.{0}} (g : G ⟶ base p) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw (baseRing p) g) (hcomm : L.IsCommutative)

    (nsmul_flat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n))
    (nsmul_locallyQuasiFinite : ∀ n : ℕ, 0 < n → LocallyQuasiFinite (L.schemeNsmul n))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) g)
    (hpts_add : ∀ x y : JZero (N₀ * p), pts (x + y) = L.mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)

    (toricRank : ℕ)
    (torusFibre : SchemeHomOver (torusStr (ResidueField ↥A) toricRank)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g))
    (torusFibre_isClosedImmersion : IsClosedImmersion torusFibre.1)
    (torusFibre_mul : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) torusFibre =
        (L.baseChange (resPt A ≫ Λ.σA)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) torusFibre)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) torusFibre))

    (abqFibre : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
    (abqFibre_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abqFibre i) =
          (Λ.L.baseChange (resPt A ≫ Λ.σA)).one s) ↔
        ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) toricRank),
          NeronModelInfra.schemeHomOverComp y torusFibre = x)
    (abqFibre_twist : ∀ (β : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)) (i : Fin 2)
      (x : SchemeHomOver (resPt A ≫ Λ.σA) g),
      fibreMap (abqFibre i) (GoodReductionJacobian.schemeHomOverComp β.1 β.2 x) =
        GoodReductionJacobian.schemeHomOverComp β.1 β.2 (fibreMap (abqFibre i) x))

    (m : ℕ) (hm : 0 < m)
    (ι : SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g))
    (hιmul : ∀ (S : Type) [CommRing S] [Algebra ↥A S] (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] S)),
      NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m (χ * χ').ofConv) ι =
        (L.baseChange Λ.σA).mul _
          (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ.ofConv) ι)
          (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ'.ofConv) ι))
    (hιsp : muBaseChange (residue ↥A) toricRank m ≫ ι.1 ≫ pullback.fst g Λ.σA =
      muToTorus (ResidueField ↥A) toricRank m ≫ torusFibre.1 ≫ pullback.fst g (resPt A ≫ Λ.σA)) :

    (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) →
        ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          σ • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) ι)) =
            c • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) ι))) ∧

    (∀ σ ∈ A.decompositionSubgroup ℚ,
        ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          ∃ χ' : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
            σ • pts.symm (genOfBaseChangePt Λ.hσA
                (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) ι)) =
              pts.symm (genOfBaseChangePt Λ.hσA
                (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ') ι))) := by
  classical

  haveI hA₁ : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  haveI hA₂ : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  have hPm_over : ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      ((muPt A toricRank m χ).1 ≫ ι.1 ≫ pullback.fst g Λ.σA) ≫ g = genPt p := by
    intro χ
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc ι.1, ι.2, ← Category.assoc,
      (muPt A toricRank m χ).2, Λ.hσA]
  have hP_def : ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) ι) =
        ⟨(muPt A toricRank m χ).1 ≫ ι.1 ≫ pullback.fst g Λ.σA, hPm_over χ⟩ := by
    intro χ
    apply Subtype.ext
    simp only [genOfBaseChangePt, castOver, RelativeGroupLaw.baseChangePointToBase_coe,
      NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

  have hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Q : SchemeHomOver (genPt p) g),
      σ • pts.symm Q =
        pts.symm ⟨Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ Q.1, by
          rw [Category.assoc, Q.2, specGal_genPt]⟩ := by
    intro σ Q
    apply pts.injective
    apply Subtype.ext
    rw [hpts_galois, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

  have mul_cast : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ base p} (h : t₁ = t₂) (x y : SchemeHomOver t₁ g),
      (L.mul t₁ x y).1 = (L.mul t₂ ⟨x.1, x.2.trans h⟩ ⟨y.1, y.2.trans h⟩).1 := by
    intro T t₁ t₂ h x y; subst h; rfl

  have hbar : Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ Λ.σA = genPt p := Λ.hσA

  have hP_mul : ∀ χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      pts.symm ⟨(muPt A toricRank m (χ * χ').ofConv).1 ≫ ι.1 ≫ pullback.fst g Λ.σA, hPm_over _⟩ =
        pts.symm ⟨(muPt A toricRank m χ.ofConv).1 ≫ ι.1 ≫ pullback.fst g Λ.σA, hPm_over _⟩ +
          pts.symm ⟨(muPt A toricRank m χ'.ofConv).1 ≫ ι.1 ≫ pullback.fst g Λ.σA, hPm_over _⟩ := by
    intro χ χ'
    apply pts.injective
    rw [hpts_add]
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    have h := congrArg (fun z => z.1 ≫ pullback.fst g Λ.σA) (hιmul (AlgebraicClosure ℚ) χ χ')
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst] at h
    rw [mul_cast hbar] at h
    exact h
  have hP_one : pts.symm ⟨(muPt A toricRank m
        (1 : WithConv (muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv).1 ≫ ι.1 ≫ pullback.fst g Λ.σA,
        hPm_over _⟩ = 0 := by
    have h := hP_mul 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h |>.symm ▸ rfl

  have hP_pow : ∀ (χ : WithConv (muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ)) (c : ℕ),
      pts.symm ⟨(muPt A toricRank m (χ ^ c).ofConv).1 ≫ ι.1 ≫ pullback.fst g Λ.σA, hPm_over _⟩ =
        c • pts.symm ⟨(muPt A toricRank m χ.ofConv).1 ≫ ι.1 ≫ pullback.fst g Λ.σA, hPm_over _⟩ := by
    intro χ c
    induction c with
    | zero => rw [pow_zero, zero_nsmul]; exact hP_one
    | succ k ih => rw [pow_succ, hP_mul, ih, succ_nsmul]

  have decStep : ∀ d : ↥(A.decompositionSubgroup ℚ),
      ∃ ι' : SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g),
        ι'.1 ≫ pullback.fst g Λ.σA = muBaseChange (sigA A d).toRingHom toricRank m ≫ ι.1 ≫ pullback.fst g Λ.σA ∧
        (∀ (S : Type) [CommRing S] [Algebra ↥A S] (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] S)),
          NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m (χ * χ').ofConv) ι' =
            (L.baseChange Λ.σA).mul _
              (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ.ofConv) ι')
              (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ'.ofConv) ι')) ∧
        muBaseChange (residue ↥A) toricRank m ≫ ι'.1 ≫ pullback.fst g Λ.σA =
          muBaseChange (sigK A d).toRingHom toricRank m ≫ muBaseChange (residue ↥A) toricRank m ≫ ι.1 ≫
            pullback.fst g Λ.σA := by
    intro d
    obtain ⟨ι', h1, h2, -, h3⟩ := AlgebraicGeometry.SplitTorus.exists_conj_muHom_baseChange Λ.σA (sigA A d)
      (specSigA_σA d) (sigK A d).toRingHom (sigK_residue d) g L toricRank m ι
    exact ⟨ι', h1, h2 hιmul, h3⟩

  have UNIQ : ∀ (τ₁ : SchemeHomOver (torusStr (ResidueField ↥A) toricRank)
        (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g))
      (h₁ : IsClosedImmersion τ₁.1)
      (h₂ : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
        NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.torusPtId (ResidueField ↥A) toricRank
            (χ * χ').ofConv) τ₁ =
          (L.baseChange (resPt A ≫ Λ.σA)).mul _
            (NeronModelInfra.schemeHomOverComp
              (AlgebraicGeometry.SplitTorus.torusPtId (ResidueField ↥A) toricRank χ.ofConv) τ₁)
            (NeronModelInfra.schemeHomOverComp
              (AlgebraicGeometry.SplitTorus.torusPtId (ResidueField ↥A) toricRank χ'.ofConv) τ₁))
      (ι₁ ι₂ : SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g)),
      (∀ (S : Type) [CommRing S] [Algebra ↥A S] (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] S)),
          NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m (χ * χ').ofConv) ι₁ =
            (L.baseChange Λ.σA).mul _
              (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ.ofConv) ι₁)
              (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ'.ofConv) ι₁)) → (muBaseChange (residue ↥A) toricRank m ≫ ι₁.1 ≫ pullback.fst g Λ.σA =
          muToTorus (ResidueField ↥A) toricRank m ≫ τ₁.1 ≫ pullback.fst g (resPt A ≫ Λ.σA)) → (∀ (S : Type) [CommRing S] [Algebra ↥A S] (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] S)),
          NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m (χ * χ').ofConv) ι₂ =
            (L.baseChange Λ.σA).mul _
              (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ.ofConv) ι₂)
              (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ'.ofConv) ι₂)) → (muBaseChange (residue ↥A) toricRank m ≫ ι₂.1 ≫ pullback.fst g Λ.σA =
          muToTorus (ResidueField ↥A) toricRank m ≫ τ₁.1 ≫ pullback.fst g (resPt A ≫ Λ.σA)) → ι₁ = ι₂ := by
    intro τ₁ h₁ h₂ ι₁ ι₂ hm₁ hs₁ hm₂ hs₂
    obtain ⟨ι₀, -, huniq⟩ :=
      AlgebraicGeometry.SplitTorus.existsUnique_muLift_baseChange_of_torusFibre_of_henselian
        (σ := Λ.σA) g L hcomm m hm (nsmul_locallyQuasiFinite m hm) (nsmul_flat m hm) toricRank τ₁ h₁ h₂
    exact (huniq ι₁ hm₁ hs₁).trans (huniq ι₂ hm₂ hs₂).symm
  refine ⟨?_, ?_⟩
  ·
    intro σ hσ c hc χ
    obtain ⟨d, rfl, hK⟩ := sigK_eq_refl_of_mem_inertia hσ
    obtain ⟨ι', h1, h2, h3⟩ := decStep d

    have hι'sp : muBaseChange (residue ↥A) toricRank m ≫ ι'.1 ≫ pullback.fst g Λ.σA =
        muToTorus (ResidueField ↥A) toricRank m ≫ torusFibre.1 ≫ pullback.fst g (resPt A ≫ Λ.σA) := by
      rw [h3, hK]
      show muBaseChange (RingHom.id _) toricRank m ≫ _ = _
      have hid : muBaseChange (RingHom.id (ResidueField ↥A)) toricRank m = 𝟙 _ := by
        simp only [muBaseChange, ← Spec.map_id, ← CommRingCat.ofHom_id]
        congr 2
        refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun v => ?_) <;> simp [AddMonoidAlgebra.mapRingHom]
      rw [hid, Category.id_comp, hιsp]
    have heq : ι' = ι := UNIQ torusFibre torusFibre_isClosedImmersion torusFibre_mul ι' ι h2 hι'sp hιmul hιsp

    have hχ : twChar d χ = (WithConv.toConv χ ^ c).ofConv := by
      refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
      intro v
      rw [convPow_apply_single]
      show (d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (χ (AddMonoidAlgebra.mapRingHom (Fin toricRank → ZMod m) (sigA A d).symm.toRingHom
          (AddMonoidAlgebra.single v 1))) = (χ (AddMonoidAlgebra.single v 1)) ^ c
      rw [show AddMonoidAlgebra.mapRingHom (Fin toricRank → ZMod m) (sigA A d).symm.toRingHom
          (AddMonoidAlgebra.single v 1) = AddMonoidAlgebra.single v 1 by simp [AddMonoidAlgebra.mapRingHom]]
      exact hc _ (apply_single_pow_eq_one (↥A) (AlgebraicClosure ℚ) m χ v)
    rw [hP_def, hgal]
    have e : Spec.map (CommRingCat.ofHom ((d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (muPt A toricRank m χ).1 ≫ ι.1 ≫ pullback.fst g Λ.σA =
        (muPt A toricRank m (WithConv.toConv χ ^ c).ofConv).1 ≫ ι.1 ≫ pullback.fst g Λ.σA := by
      rw [← Category.assoc, specGal_muPt, Category.assoc, ← h1, heq, hχ]
    rw [show (⟨Spec.map (CommRingCat.ofHom ((d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (muPt A toricRank m χ).1 ≫ ι.1 ≫ pullback.fst g Λ.σA, _⟩ :
          SchemeHomOver (genPt p) g) =
        ⟨(muPt A toricRank m (WithConv.toConv χ ^ c).ofConv).1 ≫ ι.1 ≫ pullback.fst g Λ.σA, hPm_over _⟩
        from Subtype.ext e, hP_pow]
  ·
    intro σ hσ χ
    let d : ↥(A.decompositionSubgroup ℚ) := ⟨σ, hσ⟩
    obtain ⟨ι', h1, h2, h3⟩ := decStep d

    obtain ⟨Tw, τ', hTw1, hTw2, hτ', hτ'mul, hτ'ci⟩ :=
      AlgebraicGeometry.SplitTorus.exists_twist_torusHom_baseChange_of_ringEquiv
        (resPt A ≫ Λ.σA) (sigK A d) (specSigK_resPt_σA d) g L toricRank torusFibre
    have hτ'ci' : IsClosedImmersion τ'.1 := hτ'ci torusFibre_isClosedImmersion
    have hτ'mul' := hτ'mul torusFibre_mul

    have hrange : Set.range τ'.1.base = Set.range torusFibre.1.base :=
      TLGalGlue.range_twist_eq_range g A Λ toricRank torusFibre torusFibre_isClosedImmersion abqFibre
        abqFibre_eq_one_iff abqFibre_twist (sigK A d) (specSigK_resPt_σA d) Tw τ' hTw1 hTw2 hτ' hτ'ci'

    obtain ⟨Mx, hMx⟩ :=
      AlgebraicGeometry.SplitTorus.exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
        (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g) (L.baseChange (resPt A ≫ Λ.σA)) toricRank
        torusFibre τ' torusFibre_isClosedImmersion hτ'ci' torusFibre_mul hτ'mul' hrange

    let ι₂ : SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g) :=
      ⟨dMu (↥A) (Mx : (Fin toricRank → ℤ) →+ (Fin toricRank → ℤ)) m ≫ ι.1, by
        rw [Category.assoc, ι.2, dMu_comp_muStr]⟩
    have hpt₂ : ∀ (S : Type) [CommRing S] [Algebra ↥A S] (ψ : WithConv (muCoord ↥A toricRank m →ₐ[↥A] S)),
        NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m ψ.ofConv) ι₂ =
          NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m
            (WithConv.toConv (ψ.ofConv.comp (dAlg (↥A) (Mx : (Fin toricRank → ℤ) →+ (Fin toricRank → ℤ)) m))).ofConv)
            ι := by
      intro S _ _ ψ
      apply Subtype.ext
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      show (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m ψ.ofConv).1 ≫ dMu (↥A) _ m ≫ ι.1 = _
      rw [← Category.assoc]
      congr 1
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    have hι₂mul : (∀ (S : Type) [CommRing S] [Algebra ↥A S] (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] S)),
          NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m (χ * χ').ofConv) ι₂ =
            (L.baseChange Λ.σA).mul _
              (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ.ofConv) ι₂)
              (NeronModelInfra.schemeHomOverComp (AlgebraicGeometry.SplitTorus.muPt ↥A S toricRank m χ'.ofConv) ι₂)) := by
      intro S _ _ ψ ψ'
      rw [hpt₂, hpt₂, hpt₂, comp_dAlg_mul]
      exact hιmul S _ _
    have hι₂sp : muBaseChange (residue ↥A) toricRank m ≫ ι₂.1 ≫ pullback.fst g Λ.σA =
        muToTorus (ResidueField ↥A) toricRank m ≫ τ'.1 ≫ pullback.fst g (resPt A ≫ Λ.σA) := by
      show muBaseChange (residue ↥A) toricRank m ≫ (dMu (↥A) _ m ≫ ι.1) ≫ pullback.fst g Λ.σA = _
      rw [Category.assoc, ← Category.assoc (muBaseChange _ _ _), muBaseChange_comp_dMu, Category.assoc, hιsp,
        ← Category.assoc, dMu_comp_muToTorus, Category.assoc, hMx, Category.assoc]
    have hι'sp : muBaseChange (residue ↥A) toricRank m ≫ ι'.1 ≫ pullback.fst g Λ.σA =
        muToTorus (ResidueField ↥A) toricRank m ≫ τ'.1 ≫ pullback.fst g (resPt A ≫ Λ.σA) := by
      rw [h3, hιsp, hτ', ← Category.assoc (muBaseChange _ _ _), muBaseChange_comp_muToTorus]
      simp only [Category.assoc, hTw1]
    have heq : ι' = ι₂ := UNIQ τ' hτ'ci' hτ'mul' ι' ι₂ h2 hι'sp hι₂mul hι₂sp
    refine ⟨(twChar d χ).comp (dAlg (↥A) (Mx : (Fin toricRank → ℤ) →+ (Fin toricRank → ℤ)) m), ?_⟩
    rw [hP_def, hP_def, hgal]
    congr 1
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom ((d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (muPt A toricRank m χ).1 ≫ ι.1 ≫ pullback.fst g Λ.σA =
      (muPt A toricRank m ((twChar d χ).comp (dAlg (↥A) (Mx : (Fin toricRank → ℤ) →+ (Fin toricRank → ℤ)) m))).1 ≫
        ι.1 ≫ pullback.fst g Λ.σA
    rw [← Category.assoc, specGal_muPt, Category.assoc, ← h1, heq]
    show (muPt A toricRank m (twChar d χ)).1 ≫ (dMu (↥A) _ m ≫ ι.1) ≫ pullback.fst g Λ.σA = _
    simp only [← Category.assoc]
    congr 2
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
end head

end S_ModularCurve_JZeroNeronObjectAtP_inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift (solution)
