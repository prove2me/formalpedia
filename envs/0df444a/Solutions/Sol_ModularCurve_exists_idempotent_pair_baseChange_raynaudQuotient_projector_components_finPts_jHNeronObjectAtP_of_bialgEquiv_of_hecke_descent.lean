-- Prove2me | solution 1 for ModularCurve.exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ada2588f-7825-57ed-82d1-901880b7fb62

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent

set_option autoImplicit false

section QI_hopf

open scoped TensorProduct
open Bialgebra Coalgebra WithConv

namespace QIdem

section
variable (F : Type*) [CommRing F] (A : Type*) [CommRing A] [Bialgebra F A]

noncomputable abbrev etaEps : A →ₐc[F] A := (unitBialgHom F A).comp (counitBialgHom F A)

theorem unitBialgHom_apply (r : F) : unitBialgHom F A r = algebraMap F A r := rfl

@[scoped simp] theorem etaEps_apply (a : A) : etaEps F A a = algebraMap F A (counit a) := rfl

noncomputable abbrev eL : A ⊗[F] A →ₐc[F] A ⊗[F] A := Bialgebra.TensorProduct.map (BialgHom.id F A) (etaEps F A)
noncomputable abbrev eR : A ⊗[F] A →ₐc[F] A ⊗[F] A := Bialgebra.TensorProduct.map (etaEps F A) (BialgHom.id F A)

theorem eL_eL (x : A ⊗[F] A) : eL F A (eL F A x) = eL F A x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem eR_eR (x : A ⊗[F] A) : eR F A (eR F A x) = eR F A x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem eL_eR (x : A ⊗[F] A) : eL F A (eR F A x) = algebraMap F (A ⊗[F] A) (counit x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [Bialgebra.TensorProduct.map_tmul, etaEps_apply, BialgHom.id_apply, Algebra.algebraMap_eq_smul_one]
      rw [show counit (R := F) (a ⊗ₜ[F] b) = counit (R := F) b • counit (R := F) a from rfl, Algebra.TensorProduct.one_def,
        ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_eq_mul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem eR_eL (x : A ⊗[F] A) : eR F A (eL F A x) = algebraMap F (A ⊗[F] A) (counit x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [Bialgebra.TensorProduct.map_tmul, etaEps_apply, BialgHom.id_apply, Algebra.algebraMap_eq_smul_one]
      rw [show counit (R := F) (a ⊗ₜ[F] b) = counit (R := F) b • counit (R := F) a from rfl, Algebra.TensorProduct.one_def,
        ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_eq_mul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem conv_eL_eR : toConv (eL F A : A ⊗[F] A →ₐ[F] A ⊗[F] A) * toConv (eR F A : A ⊗[F] A →ₐ[F] A ⊗[F] A) =
    toConv (AlgHom.id F (A ⊗[F] A)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [← WithConv.ofConv_toConv ((toConv (eL F A : A ⊗[F] A →ₐ[F] A ⊗[F] A) * toConv (eR F A : A ⊗[F] A →ₐ[F] A ⊗[F] A)).ofConv.toLinearMap),
    AlgHom.toLinearMap_convMul]
  change toConv (TensorProduct.map (LinearMap.id : A →ₗ[F] A) (((etaEps F A : A →ₐ[F] A) : A →ₗ[F] A))) *
      toConv (TensorProduct.map (((etaEps F A : A →ₐ[F] A) : A →ₗ[F] A)) (LinearMap.id : A →ₗ[F] A)) =
        toConv (LinearMap.id : A ⊗[F] A →ₗ[F] A ⊗[F] A)
  have h1 : toConv (((etaEps F A : A →ₐ[F] A) : A →ₗ[F] A)) = (1 : WithConv (A →ₗ[F] A)) := rfl
  have key := TensorProduct.map_convMul_map (R := F) (f := toConv (LinearMap.id : A →ₗ[F] A)) (h := (1 : WithConv (A →ₗ[F] A)))
    (g := (1 : WithConv (A →ₗ[F] A))) (k := toConv (LinearMap.id : A →ₗ[F] A))
  rw [one_mul, mul_one] at key
  rw [← h1] at key
  simpa [TensorProduct.map_id] using key

end

section transport
variable {F : Type*} [CommRing F] {H A : Type*} [CommRing H] [CommRing A] [Bialgebra F H] [Bialgebra F A]
  (κ : H ≃ₐc[F] A ⊗[F] A)

noncomputable def projL : H →ₐc[F] H :=
  (κ.symm : A ⊗[F] A →ₐc[F] H).comp ((eL F A).comp (κ : H →ₐc[F] A ⊗[F] A))

noncomputable def projR : H →ₐc[F] H :=
  (κ.symm : A ⊗[F] A →ₐc[F] H).comp ((eR F A).comp (κ : H →ₐc[F] A ⊗[F] A))

theorem projL_apply (x : H) : projL κ x = κ.symm (eL F A (κ x)) := rfl
theorem projR_apply (x : H) : projR κ x = κ.symm (eR F A (κ x)) := rfl

theorem projL_comp_projL : (projL κ).comp (projL κ) = projL κ := by
  ext x
  simp only [BialgHom.comp_apply, projL_apply, BialgEquiv.apply_symm_apply, eL_eL]

theorem projR_comp_projR : (projR κ).comp (projR κ) = projR κ := by
  ext x
  simp only [BialgHom.comp_apply, projR_apply, BialgEquiv.apply_symm_apply, eR_eR]

theorem counit_κ (x : H) : counit (R := F) (κ x) = counit (R := F) x := CoalgHomClass.counit_comp_apply κ x

theorem projL_comp_projR_toAlgHom : (projL κ : H →ₐ[F] H).comp (projR κ : H →ₐ[F] H) =
    (Algebra.ofId F H).comp (Bialgebra.counitAlgHom F H) := by
  ext x
  change κ.symm (eL F A (κ (κ.symm (eR F A (κ x))))) = algebraMap F H (counit x)
  rw [BialgEquiv.apply_symm_apply, eL_eR, counit_κ]
  exact (κ.symm : A ⊗[F] A →ₐ[F] H).commutes (counit x)

theorem conv_projL_projR : toConv (projL κ : H →ₐ[F] H) * toConv (projR κ : H →ₐ[F] H) = toConv (AlgHom.id F H) := by
  have hL : (projL κ : H →ₐ[F] H) = (κ.symm : A ⊗[F] A →ₐ[F] H).comp ((eL F A : A ⊗[F] A →ₐ[F] A ⊗[F] A).comp (κ : H →ₐc[F] A ⊗[F] A)) := rfl
  have hR : (projR κ : H →ₐ[F] H) = (κ.symm : A ⊗[F] A →ₐ[F] H).comp ((eR F A : A ⊗[F] A →ₐ[F] A ⊗[F] A).comp (κ : H →ₐc[F] A ⊗[F] A)) := rfl
  rw [hL, hR]
  have h1 := AlgHom.comp_convMul_distrib (κ.symm : A ⊗[F] A →ₐ[F] H)
    (toConv ((eL F A : A ⊗[F] A →ₐ[F] A ⊗[F] A).comp ((κ : H →ₐc[F] A ⊗[F] A) : H →ₐ[F] A ⊗[F] A)))
    (toConv ((eR F A : A ⊗[F] A →ₐ[F] A ⊗[F] A).comp (κ : H →ₐc[F] A ⊗[F] A)))
  have h2 := AlgHom.convMul_comp_bialgHom_distrib (toConv (eL F A : A ⊗[F] A →ₐ[F] A ⊗[F] A))
    (toConv (eR F A : A ⊗[F] A →ₐ[F] A ⊗[F] A)) (κ : H →ₐc[F] A ⊗[F] A)
  rw [conv_eL_eR] at h2
  apply WithConv.ofConv_injective
  rw [← h1, ← h2]
  ext x
  simp

end transport

end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

namespace QIdem
variable {F : Type*} [CommRing F] {H A : Type*} [CommRing H] [CommRing A] [Bialgebra F H] [Bialgebra F A]
  (κ : H ≃ₐc[F] A ⊗[F] A)
theorem projR_comp_projL_toAlgHom : (projR κ : H →ₐ[F] H).comp (projL κ : H →ₐ[F] H) =
    (Algebra.ofId F H).comp (Bialgebra.counitAlgHom F H) := by
  ext x
  change κ.symm (eR F A (κ (κ.symm (eL F A (κ x))))) = algebraMap F H (counit x)
  rw [BialgEquiv.apply_symm_apply, eR_eL, counit_κ]
  exact (κ.symm : A ⊗[F] A →ₐ[F] H).commutes (counit x)
end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

namespace QIdem

section naturality
variable {F : Type*} [CommRing F] {H H' A A' : Type*} [CommRing H] [CommRing H'] [CommRing A] [CommRing A']
  [Bialgebra F H] [Bialgebra F H'] [Bialgebra F A] [Bialgebra F A']
  (κ : H ≃ₐc[F] A ⊗[F] A) (κ' : H' ≃ₐc[F] A' ⊗[F] A') (tH : H' →ₐc[F] H) (tA : A' →ₐc[F] A)

theorem eL_map (x : A' ⊗[F] A') :
    eL F A (Bialgebra.TensorProduct.map tA tA x) = Bialgebra.TensorProduct.map tA tA (eL F A' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [unitBialgHom_apply, AlgHomClass.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem eR_map (x : A' ⊗[F] A') :
    eR F A (Bialgebra.TensorProduct.map tA tA x) = Bialgebra.TensorProduct.map tA tA (eR F A' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [unitBialgHom_apply, AlgHomClass.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem transition_comp_projL
    (h : (κ : H →ₐc[F] A ⊗[F] A).comp tH = (Bialgebra.TensorProduct.map tA tA).comp (κ' : H' →ₐc[F] A' ⊗[F] A')) :
    tH.comp (projL κ') = (projL κ).comp tH := by
  have hpt : ∀ x, κ (tH x) = Bialgebra.TensorProduct.map tA tA (κ' x) := fun x => DFunLike.congr_fun h x
  have hsymm : ∀ y, κ.symm (Bialgebra.TensorProduct.map tA tA y) = tH (κ'.symm y) := fun y => by
    have := hpt (κ'.symm y)
    rw [BialgEquiv.apply_symm_apply] at this
    rw [← this, BialgEquiv.symm_apply_apply]

  ext x
  simp only [BialgHom.comp_apply, projL_apply, hpt, eL_map, hsymm]

theorem transition_comp_projR
    (h : (κ : H →ₐc[F] A ⊗[F] A).comp tH = (Bialgebra.TensorProduct.map tA tA).comp (κ' : H' →ₐc[F] A' ⊗[F] A')) :
    tH.comp (projR κ') = (projR κ).comp tH := by
  have hpt : ∀ x, κ (tH x) = Bialgebra.TensorProduct.map tA tA (κ' x) := fun x => DFunLike.congr_fun h x
  have hsymm : ∀ y, κ.symm (Bialgebra.TensorProduct.map tA tA y) = tH (κ'.symm y) := fun y => by
    have := hpt (κ'.symm y)
    rw [BialgEquiv.apply_symm_apply] at this
    rw [← this, BialgEquiv.symm_apply_apply]

  ext x
  simp only [BialgHom.comp_apply, projR_apply, hpt, eR_map, hsymm]

end naturality
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

section coords
variable {F : Type*} [CommRing F] {H A : Type*} [CommRing H] [CommRing A] [Bialgebra F H] [Bialgebra F A]
  (κ : H ≃ₐc[F] A ⊗[F] A)

noncomputable def inL : A →+* H :=
  ((κ.symm.toBialgHom : A ⊗[F] A →ₐc[F] H) : A ⊗[F] A →+* H).comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[F] A)
noncomputable def inR : A →+* H :=
  ((κ.symm.toBialgHom : A ⊗[F] A →ₐc[F] H) : A ⊗[F] A →+* H).comp
    ((Algebra.TensorProduct.includeRight : A →ₐ[F] A ⊗[F] A) : A →+* A ⊗[F] A)

theorem inL_apply (a : A) : inL κ a = κ.symm (a ⊗ₜ 1) := rfl
theorem inR_apply (a : A) : inR κ a = κ.symm (1 ⊗ₜ a) := rfl

theorem projL_inL (a : A) : projL κ (inL κ a) = inL κ a := by
  rw [inL_apply, projL_apply, BialgEquiv.apply_symm_apply]
  simp

theorem projL_inR (a : A) : projL κ (inR κ a) = algebraMap F H (counit a) := by
  rw [inR_apply, projL_apply, BialgEquiv.apply_symm_apply]
  simp only [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply, etaEps_apply]
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
  exact (κ.symm : A ⊗[F] A →ₐ[F] H).commutes (counit a)
theorem projR_inR (a : A) : projR κ (inR κ a) = inR κ a := by
  rw [inR_apply, projR_apply, BialgEquiv.apply_symm_apply]
  simp
theorem projR_inL (a : A) : projR κ (inL κ a) = algebraMap F H (counit a) := by
  rw [inL_apply, projR_apply, BialgEquiv.apply_symm_apply]
  simp only [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply, etaEps_apply]
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
  exact (κ.symm : A ⊗[F] A →ₐ[F] H).commutes (counit a)

private theorem _root_.QIdem.ringHom_ext {T : Type*} [Semiring T] {f g : H →+* T} (hL : f.comp (inL κ) = g.comp (inL κ))
    (hR : f.comp (inR κ) = g.comp (inR κ)) : f = g := by
  have h' : f.comp ((κ.symm : A ⊗[F] A →ₐc[F] H) : A ⊗[F] A →+* H) = g.comp ((κ.symm : A ⊗[F] A →ₐc[F] H) : A ⊗[F] A →+* H) :=
    Algebra.TensorProduct.ringHom_ext hL hR
  apply RingHom.ext fun x => ?_
  have := DFunLike.congr_fun h' (κ x)
  simpa [BialgEquiv.symm_apply_apply] using this

p2m_export "QIdem" "ringHom_ext"
end coords
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

end QI_hopf
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

section QI_geo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace QIdem
namespace Geo

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (hx : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.one t := by rw [hx, L.inv_mul_cancel]

theorem comp_one {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
  apply eq_one_of_mul_self
  rw [← L.mul_natural t t' ψ hψ, L.one_mul]

theorem comp_one_coe {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') : ψ ≫ (L.one t).1 = (L.one t').1 := by
  have := congrArg Subtype.val (comp_one L t t' ψ hψ)
  rwa [GoodReductionJacobian.schemeHomOverComp_coe] at this

theorem hom_one (D : SchemeHomOver f f)
    (hD : ∀ {T' : Scheme.{u}} (s : T' ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) D = L.mul s (NeronModelInfra.schemeHomOverComp x D) (NeronModelInfra.schemeHomOverComp y D))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (L.one t) D = L.one t := by
  apply eq_one_of_mul_self
  rw [← hD, L.one_mul]

theorem comp_schemeHomOverComp {T T' X' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    {f' : X' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) (E : SchemeHomOver f f') :
    NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ x) E =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x E) :=
  Subtype.ext (Category.assoc _ _ _)

end Geo
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"
end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

namespace QIdem
namespace Geo

open Bialgebra

section generic
variable {F : Type} [CommRing F] {X' : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of F)} (L : RelativeGroupLaw F f')

theorem counit_comp_eq_one {p h : ℕ} (G : PDivisibleGroup F p h) (v : ℕ) (ιA : Spec (CommRingCat.of (G.level v)) ⟶ X')
    (hbase : ιA ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap F (G.level v))))
    (hmul : ∀ (x y : G.Point F v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[F] F) : G.level v →+* F)) ≫ ιA) ≫ f' =
        Spec.map (CommRingCat.ofHom (algebraMap F F)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[F] F) : G.level v →+* F)) ≫ ιA) ≫ f' =
        Spec.map (CommRingCat.ofHom (algebraMap F F))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[F] F) : G.level v →+* F)) ≫ ιA =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap F F))) ⟨_, hx⟩ ⟨_, hy⟩).1) :
    Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom F (G.level v) : G.level v →+* F)) ≫ ιA =
      (L.one (𝟙 (Spec (CommRingCat.of F)))).1 := by
  have hidF : Spec.map (CommRingCat.ofHom (algebraMap F F)) = 𝟙 (Spec (CommRingCat.of F)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  let x₀ : G.Point F v := 1
  have hx₀ : ((PDivisibleGroup.Point.toAlgHom x₀ : G.level v →ₐ[F] F) : G.level v →+* F) =
      (Bialgebra.counitAlgHom F (G.level v) : G.level v →+* F) := by
    refine RingHom.ext fun a => ?_
    change PDivisibleGroup.Point.toAlgHom (1 : G.Point F v) a = Coalgebra.counit a
    rw [PDivisibleGroup.Point.one_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x₀ : G.level v →ₐ[F] F) : G.level v →+* F)) ≫ ιA) ≫ f' =
      Spec.map (CommRingCat.ofHom (algebraMap F F)) := by
    rw [Category.assoc, hbase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    change PDivisibleGroup.Point.toAlgHom x₀ (algebraMap F _ r) = algebraMap F F r
    exact (PDivisibleGroup.Point.toAlgHom x₀).commutes r
  have hm := hmul x₀ x₀ hx hx
  rw [show x₀ * x₀ = x₀ from mul_one x₀] at hm
  have hpt := eq_one_of_mul_self L _ (⟨_, hx⟩ : SchemeHomOver _ _) (Subtype.ext hm).symm
  have hval := congrArg Subtype.val hpt
  change Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x₀ : G.level v →ₐ[F] F) : G.level v →+* F)) ≫ ιA = _ at hval
  rw [hx₀] at hval
  rw [hval]
  have h1 := comp_one_coe L (𝟙 (Spec (CommRingCat.of F))) (Spec.map (CommRingCat.ofHom (algebraMap F F))) (𝟙 _)
    (by rw [hidF, Category.comp_id])
  rw [Category.id_comp] at h1
  exact h1.symm

variable {H A : Type} [CommRing H] [CommRing A] [Bialgebra F H] [Bialgebra F A] (κ : H ≃ₐc[F] A ⊗[F] A)
  (ιA : Spec (CommRingCat.of A) ⟶ X') (r0 r1 : Spec (CommRingCat.of H) ⟶ X')
  (hr0 : Spec.map (CommRingCat.ofHom (QIdem.inL κ)) ≫ ιA = r0) (hr1 : Spec.map (CommRingCat.ofHom (QIdem.inR κ)) ≫ ιA = r1)
  (hunit : Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom F A : A →+* F)) ≫ ιA = (L.one (𝟙 (Spec (CommRingCat.of F)))).1)

include hr1 hunit in
theorem pin_L1 : Spec.map (CommRingCat.ofHom (QIdem.projL κ : H →+* H)) ≫ r1 =
    Spec.map (CommRingCat.ofHom (algebraMap F H)) ≫ (L.one (𝟙 (Spec (CommRingCat.of F)))).1 := by
  have hring : (QIdem.projL κ : H →+* H).comp (QIdem.inR κ) = (algebraMap F H).comp (Bialgebra.counitAlgHom F A : A →+* F) :=
    RingHom.ext fun a => QIdem.projL_inR κ a
  rw [← hr1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, hunit]

include hr0 in
theorem pin_L0 : Spec.map (CommRingCat.ofHom (QIdem.projL κ : H →+* H)) ≫ r0 = r0 := by
  have hring : (QIdem.projL κ : H →+* H).comp (QIdem.inL κ) = QIdem.inL κ := RingHom.ext fun a => QIdem.projL_inL κ a
  rw [← hr0, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]

include hr0 hunit in
theorem pin_R0 : Spec.map (CommRingCat.ofHom (QIdem.projR κ : H →+* H)) ≫ r0 =
    Spec.map (CommRingCat.ofHom (algebraMap F H)) ≫ (L.one (𝟙 (Spec (CommRingCat.of F)))).1 := by
  have hring : (QIdem.projR κ : H →+* H).comp (QIdem.inL κ) = (algebraMap F H).comp (Bialgebra.counitAlgHom F A : A →+* F) :=
    RingHom.ext fun a => QIdem.projR_inL κ a
  rw [← hr0, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, hunit]

include hr1 in
theorem pin_R1 : Spec.map (CommRingCat.ofHom (QIdem.projR κ : H →+* H)) ≫ r1 = r1 := by
  have hring : (QIdem.projR κ : H →+* H).comp (QIdem.inR κ) = QIdem.inR κ := RingHom.ext fun a => QIdem.projR_inR κ a
  rw [← hr1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]

end generic
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

end Geo
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"
end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

namespace QIdem
namespace Geo

open Bialgebra

section operators
variable {F : Type} [CommRing F] {X' XG : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of F)} (L : RelativeGroupLaw F f')
  {H HG A : Type} [CommRing H] [CommRing HG] [CommRing A] [Bialgebra F H] [Bialgebra F A]
  (κ : H ≃ₐc[F] A ⊗[F] A) (ιA : Spec (CommRingCat.of A) ⟶ X') [Mono ιA]
  (r0 r1 : Spec (CommRingCat.of H) ⟶ X')
  (hr0 : Spec.map (CommRingCat.ofHom (QIdem.inL κ)) ≫ ιA = r0) (hr1 : Spec.map (CommRingCat.ofHom (QIdem.inR κ)) ≫ ιA = r1)
  (hunit : Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom F A : A →+* F)) ≫ ιA = (L.one (𝟙 (Spec (CommRingCat.of F)))).1)
  (ψ' : H →+* HG) [Epi (Spec.map (CommRingCat.ofHom ψ'))]
  (ιp : Spec (CommRingCat.of HG) ⟶ XG) (q0 q1 : XG ⟶ X')
  (hfac0 : Spec.map (CommRingCat.ofHom ψ') ≫ r0 = ιp ≫ q0) (hfac1 : Spec.map (CommRingCat.ofHom ψ') ≫ r1 = ιp ≫ q1)
  (Fs Ds : X' ⟶ X')
  (hFone : (L.one (𝟙 (Spec (CommRingCat.of F)))).1 ≫ Fs = (L.one (𝟙 (Spec (CommRingCat.of F)))).1)
  (hDone : (L.one (𝟙 (Spec (CommRingCat.of F)))).1 ≫ Ds = (L.one (𝟙 (Spec (CommRingCat.of F)))).1)

theorem intertwine (E : H →+* H) (e' : HG →+* HG) (Eup : XG ⟶ XG) (r : Spec (CommRingCat.of H) ⟶ X') (qq : XG ⟶ X') (tail : X' ⟶ X')
    (hI2 : ψ'.comp E = e'.comp ψ') (hI1 : Spec.map (CommRingCat.ofHom e') ≫ ιp = ιp ≫ Eup)
    (hfac : Spec.map (CommRingCat.ofHom ψ') ≫ r = ιp ≫ qq) (hq : Eup ≫ qq = qq ≫ tail) :
    Spec.map (CommRingCat.ofHom E) ≫ r = r ≫ tail := by
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom ψ'))]
  calc Spec.map (CommRingCat.ofHom ψ') ≫ Spec.map (CommRingCat.ofHom E) ≫ r
      = Spec.map (CommRingCat.ofHom e') ≫ Spec.map (CommRingCat.ofHom ψ') ≫ r := by
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hI2, CommRingCat.ofHom_comp, Spec.map_comp,
            Category.assoc]
    _ = Spec.map (CommRingCat.ofHom e') ≫ ιp ≫ qq := by rw [hfac]
    _ = ιp ≫ Eup ≫ qq := by rw [← Category.assoc, hI1, Category.assoc]
    _ = ιp ≫ qq ≫ tail := by rw [hq]
    _ = Spec.map (CommRingCat.ofHom ψ') ≫ r ≫ tail := by rw [← Category.assoc, ← hfac, Category.assoc]

include hr1 hunit in

theorem comp_inR_eq_of_spec (E : H →+* H)
    (hE : Spec.map (CommRingCat.ofHom E) ≫ r1 = Spec.map (CommRingCat.ofHom (algebraMap F H)) ≫ (L.one (𝟙 (Spec (CommRingCat.of F)))).1) :
    E.comp (QIdem.inR κ) = (algebraMap F H).comp (Bialgebra.counitAlgHom F A : A →+* F) := by
  have key : Spec.map (CommRingCat.ofHom (E.comp (QIdem.inR κ))) =
      Spec.map (CommRingCat.ofHom ((algebraMap F H).comp (Bialgebra.counitAlgHom F A : A →+* F))) := by
    rw [← cancel_mono ιA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hr1, hE, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hunit]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

include hr0 in

theorem comp_inL_eq_of_spec (E E' : H →+* H)
    (hE : Spec.map (CommRingCat.ofHom E) ≫ r0 = Spec.map (CommRingCat.ofHom E') ≫ r0) :
    E.comp (QIdem.inL κ) = E'.comp (QIdem.inL κ) := by
  have key : Spec.map (CommRingCat.ofHom (E.comp (QIdem.inL κ))) = Spec.map (CommRingCat.ofHom (E'.comp (QIdem.inL κ))) := by
    rw [← cancel_mono ιA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hr0, hE, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hr0]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

include hr0 hr1 hunit hfac1 hFone hDone in

private theorem _root_.QIdem.Geo.triangular (uBb : H →ₐc[F] H) (u' : HG →+* HG) (U : XG ⟶ XG)
    (hI2 : ψ'.comp (uBb : H →+* H) = u'.comp ψ') (hI1 : Spec.map (CommRingCat.ofHom u') ≫ ιp = ιp ≫ U)
    (hUq1 : U ≫ q1 = q1 ≫ (Fs ≫ Ds)) :
    (QIdem.projL κ).comp (uBb.comp (QIdem.projL κ)) = (QIdem.projL κ).comp uBb := by
  have hA : Spec.map (CommRingCat.ofHom (uBb : H →+* H)) ≫ r1 = r1 ≫ (Fs ≫ Ds) :=
    intertwine ψ' ιp (uBb : H →+* H) u' U r1 q1 (Fs ≫ Ds) hI2 hI1 hfac1 hUq1
  have hpin := pin_L1 L κ ιA r1 hr1 hunit
  have hB : Spec.map (CommRingCat.ofHom ((QIdem.projL κ : H →+* H).comp (uBb : H →+* H))) ≫ r1 =
      Spec.map (CommRingCat.ofHom (algebraMap F H)) ≫ (L.one (𝟙 (Spec (CommRingCat.of F)))).1 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hA, ← Category.assoc, hpin, Category.assoc, ← Category.assoc _ Fs Ds,
      hFone, hDone]
  have hC := comp_inR_eq_of_spec L κ ιA r1 hr1 hunit _ hB
  have hring : ((QIdem.projL κ : H →+* H).comp ((uBb : H →+* H).comp (QIdem.projL κ : H →+* H))) =
      (QIdem.projL κ : H →+* H).comp (uBb : H →+* H) := by
    apply QIdem.ringHom_ext κ
    · refine RingHom.ext fun a => ?_
      change QIdem.projL κ (uBb (QIdem.projL κ (QIdem.inL κ a))) = QIdem.projL κ (uBb (QIdem.inL κ a))
      rw [QIdem.projL_inL]
    · refine RingHom.ext fun a => ?_
      have hCa := DFunLike.congr_fun hC a
      change QIdem.projL κ (uBb (QIdem.inR κ a)) = algebraMap F H (Coalgebra.counit a) at hCa
      change QIdem.projL κ (uBb (QIdem.projL κ (QIdem.inR κ a))) = QIdem.projL κ (uBb (QIdem.inR κ a))
      rw [hCa, QIdem.projL_inR, AlgHomClass.commutes, AlgHomClass.commutes]
  exact BialgHom.ext fun x => DFunLike.congr_fun hring x

p2m_export "QIdem.Geo" "triangular"
include hr0 hr1 hunit hfac0 hfac1 hDone in

private theorem _root_.QIdem.Geo.diagonal (Db : H →ₐc[F] H) (d' : HG →+* HG) (D : XG ⟶ XG)
    (hI2 : ψ'.comp (Db : H →+* H) = d'.comp ψ') (hI1 : Spec.map (CommRingCat.ofHom d') ≫ ιp = ιp ≫ D)
    (hDq0 : D ≫ q0 = q0 ≫ Ds) (hDq1 : D ≫ q1 = q1 ≫ Ds) :
    (QIdem.projL κ).comp Db = Db.comp (QIdem.projL κ) := by
  have hA0 : Spec.map (CommRingCat.ofHom (Db : H →+* H)) ≫ r0 = r0 ≫ Ds := intertwine ψ' ιp (Db : H →+* H) d' D r0 q0 Ds hI2 hI1 hfac0 hDq0
  have hA1 : Spec.map (CommRingCat.ofHom (Db : H →+* H)) ≫ r1 = r1 ≫ Ds := intertwine ψ' ιp (Db : H →+* H) d' D r1 q1 Ds hI2 hI1 hfac1 hDq1
  have hpin1 := pin_L1 L κ ιA r1 hr1 hunit
  have hpin0 := pin_L0 κ ιA r0 hr0

  have hL := comp_inL_eq_of_spec κ ιA r0 hr0 ((QIdem.projL κ : H →+* H).comp (Db : H →+* H)) ((Db : H →+* H).comp (QIdem.projL κ : H →+* H)) (by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hA0, ← Category.assoc, hpin0,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hpin0, hA0])

  have hR1 : ((QIdem.projL κ : H →+* H).comp (Db : H →+* H)).comp (QIdem.inR κ) =
      (algebraMap F H).comp (Bialgebra.counitAlgHom F A : A →+* F) :=
    comp_inR_eq_of_spec L κ ιA r1 hr1 hunit _ (by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hA1, ← Category.assoc, hpin1, Category.assoc, hDone])
  have hR2 : ((Db : H →+* H).comp (QIdem.projL κ : H →+* H)).comp (QIdem.inR κ) =
      (algebraMap F H).comp (Bialgebra.counitAlgHom F A : A →+* F) := by
    refine RingHom.ext fun a => ?_
    change Db (QIdem.projL κ (QIdem.inR κ a)) = algebraMap F H (Coalgebra.counit a)
    rw [QIdem.projL_inR, AlgHomClass.commutes]
  have hring : (QIdem.projL κ : H →+* H).comp (Db : H →+* H) = (Db : H →+* H).comp (QIdem.projL κ : H →+* H) :=
    QIdem.ringHom_ext κ hL (hR1.trans hR2.symm)
  exact BialgHom.ext fun x => DFunLike.congr_fun hring x

p2m_export "QIdem.Geo" "diagonal"
end operators
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

end Geo
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"
end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

namespace QIdem
namespace Tens

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]
  {B G : Type} [CommRing B] [CommRing G] [Bialgebra R B] [Bialgebra R G]

theorem map_comp_map (ψ : B →ₐc[R] G) (uB : B →ₐc[R] B) (u : G →ₐc[R] G) (h : u.comp ψ = ψ.comp uB) :
    ((Bialgebra.TensorProduct.map (BialgHom.id S S) ψ : S ⊗[R] B →ₐc[S] S ⊗[R] G) : S ⊗[R] B →+* S ⊗[R] G).comp
        ((Bialgebra.TensorProduct.map (BialgHom.id S S) uB : S ⊗[R] B →ₐc[S] S ⊗[R] B) : S ⊗[R] B →+* S ⊗[R] B) =
      ((Bialgebra.TensorProduct.map (BialgHom.id S S) u : S ⊗[R] G →ₐc[S] S ⊗[R] G) : S ⊗[R] G →+* S ⊗[R] G).comp
        ((Bialgebra.TensorProduct.map (BialgHom.id S S) ψ : S ⊗[R] B →ₐc[S] S ⊗[R] G) : S ⊗[R] B →+* S ⊗[R] G) := by
  apply Algebra.TensorProduct.ringHom_ext
  · refine RingHom.ext fun s => ?_
    simp [Bialgebra.TensorProduct.map_tmul]
  · refine RingHom.ext fun b => ?_
    have hb : u (ψ b) = ψ (uB b) := DFunLike.congr_fun h b
    simp [Bialgebra.TensorProduct.map_tmul, hb]

theorem map_comp_includeRight (u : G →ₐc[R] G) :
    ((Bialgebra.TensorProduct.map (BialgHom.id S S) u : S ⊗[R] G →ₐc[S] S ⊗[R] G) : S ⊗[R] G →+* S ⊗[R] G).comp
        (Algebra.TensorProduct.includeRight.toRingHom : G →+* S ⊗[R] G) =
      (Algebra.TensorProduct.includeRight.toRingHom : G →+* S ⊗[R] G).comp (u : G →+* G) := by
  refine RingHom.ext fun g => ?_
  simp [Bialgebra.TensorProduct.map_tmul]

theorem map_comp_algebraMap (u : G →ₐc[R] G) :
    ((Bialgebra.TensorProduct.map (BialgHom.id S S) u : S ⊗[R] G →ₐc[S] S ⊗[R] G) : S ⊗[R] G →+* S ⊗[R] G).comp
        (algebraMap S (S ⊗[R] G)) = algebraMap S (S ⊗[R] G) :=
  RingHom.ext fun s => AlgHomClass.commutes (Bialgebra.TensorProduct.map (BialgHom.id S S) u) s

end Tens
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"
end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

end QI_geo
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

section QI_glue

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace QIdem
namespace Glue

theorem spec_map_comp_ιp {R S G : Type} [CommRing R] [CommRing S] [CommRing G] [Algebra R S] [Bialgebra R G]
    {XG0 Bb : Scheme.{0}} {g : XG0 ⟶ Bb} {σ : Spec (CommRingCat.of S) ⟶ Bb}
    (u : G →ₐc[R] G) (ι : Spec (CommRingCat.of G) ⟶ XG0) (T : XG0 ⟶ XG0)
    (huι : Spec.map (CommRingCat.ofHom (u : G →+* G)) ≫ ι = ι ≫ T)
    (ιp : Spec (CommRingCat.of (S ⊗[R] G)) ⟶ pullback g σ)
    (hιp₁ : ιp ≫ pullback.fst g σ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G →+* S ⊗[R] G)) ≫ ι)
    (hιp₂ : ιp ≫ pullback.snd g σ = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] G))))
    (U : pullback g σ ⟶ pullback g σ) (hU : U ≫ pullback.fst g σ = pullback.fst g σ ≫ T)
    (hU2 : U ≫ pullback.snd g σ = pullback.snd g σ) :
    Spec.map (CommRingCat.ofHom ((Bialgebra.TensorProduct.map (BialgHom.id S S) u : S ⊗[R] G →ₐc[S] S ⊗[R] G) :
        S ⊗[R] G →+* S ⊗[R] G)) ≫ ιp = ιp ≫ U := by
  have h1 : Spec.map (CommRingCat.ofHom ((Bialgebra.TensorProduct.map (BialgHom.id S S) u : S ⊗[R] G →ₐc[S] S ⊗[R] G) :
        S ⊗[R] G →+* S ⊗[R] G)) ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G →+* S ⊗[R] G)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G →+* S ⊗[R] G)) ≫
        Spec.map (CommRingCat.ofHom (u : G →+* G)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, QIdem.Tens.map_comp_includeRight]
  have h2 : Spec.map (CommRingCat.ofHom ((Bialgebra.TensorProduct.map (BialgHom.id S S) u : S ⊗[R] G →ₐc[S] S ⊗[R] G) :
        S ⊗[R] G →+* S ⊗[R] G)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] G))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] G))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, QIdem.Tens.map_comp_algebraMap]
  apply pullback.hom_ext
  · calc (Spec.map _ ≫ ιp) ≫ pullback.fst g σ
        = Spec.map (CommRingCat.ofHom ((Bialgebra.TensorProduct.map (BialgHom.id S S) u : S ⊗[R] G →ₐc[S] S ⊗[R] G) :
            S ⊗[R] G →+* S ⊗[R] G)) ≫ (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G →+* S ⊗[R] G)) ≫ ι) := by
          rw [Category.assoc, hιp₁]
      _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G →+* S ⊗[R] G)) ≫ (ι ≫ T) := by
          rw [← Category.assoc, h1, Category.assoc, huι]
      _ = (ιp ≫ pullback.fst g σ) ≫ T := by rw [hιp₁, Category.assoc]
      _ = (ιp ≫ U) ≫ pullback.fst g σ := by rw [Category.assoc, Category.assoc, hU]
  · rw [Category.assoc, hιp₂, h2, Category.assoc, hU2, hιp₂]

theorem val_eq_of_comp_eq {B X Y : Scheme.{0}} {x : X ⟶ B} {y : Y ⟶ B}
    (U : SchemeHomOver x x) (q : SchemeHomOver x y) (Fz Dz : SchemeHomOver y y)
    (h : schemeHomOverComp U q = schemeHomOverComp (schemeHomOverComp q Fz) Dz) :
    U.1 ≫ q.1 = q.1 ≫ (Fz.1 ≫ Dz.1) := by
  have := congrArg Subtype.val h
  simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc] at this
  exact this

theorem val_eq_of_comp_eq' {B X Y : Scheme.{0}} {x : X ⟶ B} {y : Y ⟶ B}
    (D : SchemeHomOver x x) (q : SchemeHomOver x y) (Dz : SchemeHomOver y y)
    (h : schemeHomOverComp D q = schemeHomOverComp q Dz) :
    D.1 ≫ q.1 = q.1 ≫ Dz.1 := by
  have := congrArg Subtype.val h
  simp only [NeronModelInfra.schemeHomOverComp_coe] at this
  exact this

section law
variable {F : Type} [CommRing F] {X' : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of F)} (L : RelativeGroupLaw F f')

theorem one_comp_hom (D : SchemeHomOver f' f')
    (hD : ∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of F)) (x y : SchemeHomOver s f'),
      schemeHomOverComp (L.mul s x y) D = L.mul s (schemeHomOverComp x D) (schemeHomOverComp y D)) :
    (L.one (𝟙 (Spec (CommRingCat.of F)))).1 ≫ D.1 = (L.one (𝟙 (Spec (CommRingCat.of F)))).1 :=
  congrArg Subtype.val (QIdem.Geo.hom_one L D hD (𝟙 _))

end law
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

theorem one_comp_frob {p : ℕ} [Fact p.Prime] {X' : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of (ZMod p))}
    (L : RelativeGroupLaw (ZMod p) f') (Fs : SchemeHomOver f' f')
    (hF : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p)))) f',
      (schemeHomOverComp x Fs).1 = Spec.map (CommRingCat.ofHom (frobenius (ZMod p) p)) ≫ x.1) :
    (L.one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 ≫ Fs.1 = (L.one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 := by
  have hidF : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p))) = 𝟙 (Spec (CommRingCat.of (ZMod p))) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

  have := hF (L.one _)
  rw [NeronModelInfra.schemeHomOverComp_coe, ZMod.frobenius_zmod] at this
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at this
  exact this

end Glue
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"
end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

namespace QIdem
namespace Wrap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (ZMod p)]
  {hB hG : ℕ} (GB : PDivisibleGroup R p hB) (GG : PDivisibleGroup R p hG)
  {hA : ℕ} (GA : PDivisibleGroup (ZMod p) p hA) (v : ℕ)
  {X' XG0 : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of (ZMod p))} (L : RelativeGroupLaw (ZMod p) f')
  {R0 : Type} [CommRing R0] {g : XG0 ⟶ Spec (CommRingCat.of R0)} {σ : Spec (CommRingCat.of (ZMod p)) ⟶ Spec (CommRingCat.of R0)}
  (κ : (GB.baseChange (ZMod p)).level v ≃ₐc[ZMod p] ((GA.level v) ⊗[ZMod p] (GA.level v)))
  (ιA : Spec (CommRingCat.of (GA.level v)) ⟶ X') (hιAcl : IsClosedImmersion ιA)
  (hιAbase : ιA ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (GA.level v))))
  (hιAmul : ∀ (x y : GA.Point (ZMod p) v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : GA.level v →ₐ[ZMod p] ZMod p) : GA.level v →+* ZMod p)) ≫ ιA) ≫ f' =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p))))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : GA.level v →ₐ[ZMod p] ZMod p) : GA.level v →+* ZMod p)) ≫ ιA) ≫ f' =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p)))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : GA.level v →ₐ[ZMod p] ZMod p) : GA.level v →+* ZMod p)) ≫ ιA =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p)))) ⟨_, hx⟩ ⟨_, hy⟩).1)
  (r0 r1 : Spec (CommRingCat.of ((GB.baseChange (ZMod p)).level v)) ⟶ X')
  (hr0 : Spec.map (CommRingCat.ofHom ((κ.symm.toBialgHom : ((GA.level v) ⊗[ZMod p] (GA.level v)) →+* (GB.baseChange (ZMod p)).level v).comp
        (Algebra.TensorProduct.includeLeftRingHom : GA.level v →+* ((GA.level v) ⊗[ZMod p] (GA.level v))))) ≫ ιA = r0)
  (hr1 : Spec.map (CommRingCat.ofHom ((κ.symm.toBialgHom : ((GA.level v) ⊗[ZMod p] (GA.level v)) →+* (GB.baseChange (ZMod p)).level v).comp
        ((Algebra.TensorProduct.includeRight : GA.level v →ₐ[ZMod p] ((GA.level v) ⊗[ZMod p] (GA.level v))) : GA.level v →+* ((GA.level v) ⊗[ZMod p] (GA.level v))))) ≫ ιA = r1)

include hιAbase hιAmul in
theorem hunit : Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom (ZMod p) (GA.level v) : GA.level v →+* ZMod p)) ≫ ιA =
    (L.one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 :=
  QIdem.Geo.counit_comp_eq_one L GA v ιA hιAbase hιAmul

include hr1 hιAbase hιAmul in
theorem pinL1 : Spec.map (CommRingCat.ofHom ((QIdem.projL κ) : (GB.baseChange (ZMod p)).level v →+* (GB.baseChange (ZMod p)).level v)) ≫ r1 =
    Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((GB.baseChange (ZMod p)).level v))) ≫ (L.one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 :=
  QIdem.Geo.pin_L1 L κ ιA r1 hr1 (hunit GA v L ιA hιAbase hιAmul)

include hr0 in
theorem pinL0 : Spec.map (CommRingCat.ofHom ((QIdem.projL κ) : (GB.baseChange (ZMod p)).level v →+* (GB.baseChange (ZMod p)).level v)) ≫ r0 = r0 :=
  QIdem.Geo.pin_L0 κ ιA r0 hr0

include hr0 hιAbase hιAmul in
theorem pinR0 : Spec.map (CommRingCat.ofHom ((QIdem.projR κ) : (GB.baseChange (ZMod p)).level v →+* (GB.baseChange (ZMod p)).level v)) ≫ r0 =
    Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((GB.baseChange (ZMod p)).level v))) ≫ (L.one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 :=
  QIdem.Geo.pin_R0 L κ ιA r0 hr0 (hunit GA v L ιA hιAbase hιAmul)

include hr1 in
theorem pinR1 : Spec.map (CommRingCat.ofHom ((QIdem.projR κ) : (GB.baseChange (ZMod p)).level v →+* (GB.baseChange (ZMod p)).level v)) ≫ r1 = r1 :=
  QIdem.Geo.pin_R1 κ ιA r1 hr1

variable
  (ψ : GB.level v →ₐc[R] GG.level v)
  (hPepi : Epi (Spec.map (CommRingCat.ofHom
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ψ : ZMod p ⊗[R] GB.level v →+* ZMod p ⊗[R] GG.level v))))
  (ι : Spec (CommRingCat.of (GG.level v)) ⟶ XG0)
  (ιp : Spec (CommRingCat.of (ZMod p ⊗[R] GG.level v)) ⟶ pullback g σ)
  (hιp₁ : ιp ≫ pullback.fst g σ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : GG.level v →+* ZMod p ⊗[R] GG.level v)) ≫ ι)
  (hιp₂ : ιp ≫ pullback.snd g σ = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[R] GG.level v))))
  (q0 q1 : SchemeHomOver (RelativeGroupLaw.baseChangeStr σ g) f')
  (hfac0 : Spec.map (CommRingCat.ofHom
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ψ : ZMod p ⊗[R] GB.level v →+* ZMod p ⊗[R] GG.level v)) ≫ r0 = ιp ≫ q0.1)
  (hfac1 : Spec.map (CommRingCat.ofHom
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ψ : ZMod p ⊗[R] GB.level v →+* ZMod p ⊗[R] GG.level v)) ≫ r1 = ιp ≫ q1.1)
  (Fs Ds : SchemeHomOver f' f')
  (hFs : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p)))) f',
      (schemeHomOverComp x Fs).1 = Spec.map (CommRingCat.ofHom (frobenius (ZMod p) p)) ≫ x.1)
  (hDs : ∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of (ZMod p))) (x y : SchemeHomOver s f'),
      schemeHomOverComp (L.mul s x y) Ds = L.mul s (schemeHomOverComp x Ds) (schemeHomOverComp y Ds))

include hιAcl hιAbase hιAmul hr0 hr1 hPepi hιp₁ hιp₂ hfac1 hFs hDs in

private theorem _root_.QIdem.Wrap.triangular (uB : GB.level v →ₐc[R] GB.level v) (u : GG.level v →ₐc[R] GG.level v) (huB : u.comp ψ = ψ.comp uB)
    (T : XG0 ⟶ XG0) (huι : Spec.map (CommRingCat.ofHom (u : GG.level v →+* GG.level v)) ≫ ι = ι ≫ T)
    (U : SchemeHomOver (RelativeGroupLaw.baseChangeStr σ g) (RelativeGroupLaw.baseChangeStr σ g))
    (hU : U.1 ≫ pullback.fst g σ = pullback.fst g σ ≫ T)
    (hUq1 : schemeHomOverComp U q1 = schemeHomOverComp (schemeHomOverComp q1 Fs) Ds) :
    (QIdem.projL κ).comp ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) uB).comp (QIdem.projL κ)) =
      (QIdem.projL κ).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) uB) := by
  haveI : Mono ιA := by haveI := hιAcl; infer_instance
  exact @QIdem.Geo.triangular (ZMod p) _ X' (pullback g σ) f' L ((GB.baseChange (ZMod p)).level v) (ZMod p ⊗[R] GG.level v) (GA.level v)
    _ _ _ _ _ κ ιA inferInstance r0 r1 hr0 hr1 (hunit GA v L ιA hιAbase hιAmul)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ψ : ZMod p ⊗[R] GB.level v →+* ZMod p ⊗[R] GG.level v) hPepi
    ιp q1.1 hfac1 Fs.1 Ds.1 (QIdem.Glue.one_comp_frob L Fs hFs) (QIdem.Glue.one_comp_hom L Ds hDs)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) uB)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) u : ZMod p ⊗[R] GG.level v →+* ZMod p ⊗[R] GG.level v) U.1
    (QIdem.Tens.map_comp_map (ZMod p) ψ uB u huB)
    (QIdem.Glue.spec_map_comp_ιp u ι T huι ιp hιp₁ hιp₂ U.1 hU U.2)
    (QIdem.Glue.val_eq_of_comp_eq U q1 Fs Ds hUq1)

p2m_export "QIdem.Wrap" "triangular"
include hιAcl hιAbase hιAmul hr0 hr1 hPepi hιp₁ hιp₂ hfac0 hfac1 hDs in

private theorem _root_.QIdem.Wrap.diagonal (DB : GB.level v ≃ₐc[R] GB.level v) (DB' : ZMod p ⊗[R] GB.level v ≃ₐc[ZMod p] ZMod p ⊗[R] GB.level v)
    (hDB' : (DB' : ZMod p ⊗[R] GB.level v →ₐc[ZMod p] ZMod p ⊗[R] GB.level v) =
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (DB : GB.level v →ₐc[R] GB.level v))
    (Dp : GG.level v ≃ₐc[R] GG.level v)
    (hDB : (Dp : GG.level v →ₐc[R] GG.level v).comp ψ = ψ.comp (DB : GB.level v →ₐc[R] GB.level v))
    (T : XG0 ⟶ XG0)
    (hDpι : Spec.map (CommRingCat.ofHom ((Dp : GG.level v →ₐc[R] GG.level v) : GG.level v →+* GG.level v)) ≫ ι = ι ≫ T)
    (D : SchemeHomOver (RelativeGroupLaw.baseChangeStr σ g) (RelativeGroupLaw.baseChangeStr σ g))
    (hD : D.1 ≫ pullback.fst g σ = pullback.fst g σ ≫ T)
    (hDq1 : schemeHomOverComp D q1 = schemeHomOverComp q1 Ds)
    (hDq0 : schemeHomOverComp D q0 = schemeHomOverComp q0 Ds) :
    (QIdem.projL κ).comp (DB' : ZMod p ⊗[R] GB.level v →ₐc[ZMod p] ZMod p ⊗[R] GB.level v) =
      (DB' : ZMod p ⊗[R] GB.level v →ₐc[ZMod p] ZMod p ⊗[R] GB.level v).comp (QIdem.projL κ) := by
  haveI : Mono ιA := by haveI := hιAcl; infer_instance
  have hI2 : (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ψ : ZMod p ⊗[R] GB.level v →+* ZMod p ⊗[R] GG.level v).comp
        ((DB' : ZMod p ⊗[R] GB.level v →ₐc[ZMod p] ZMod p ⊗[R] GB.level v) : ZMod p ⊗[R] GB.level v →+* ZMod p ⊗[R] GB.level v) =
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (Dp : GG.level v →ₐc[R] GG.level v) :
          ZMod p ⊗[R] GG.level v →+* ZMod p ⊗[R] GG.level v).comp
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ψ : ZMod p ⊗[R] GB.level v →+* ZMod p ⊗[R] GG.level v) := by
    rw [hDB']
    exact QIdem.Tens.map_comp_map (ZMod p) ψ (DB : GB.level v →ₐc[R] GB.level v) (Dp : GG.level v →ₐc[R] GG.level v) hDB
  exact @QIdem.Geo.diagonal (ZMod p) _ X' (pullback g σ) f' L ((GB.baseChange (ZMod p)).level v) (ZMod p ⊗[R] GG.level v) (GA.level v)
    _ _ _ _ _ κ ιA inferInstance r0 r1 hr0 hr1 (hunit GA v L ιA hιAbase hιAmul)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ψ : ZMod p ⊗[R] GB.level v →+* ZMod p ⊗[R] GG.level v) hPepi
    ιp q0.1 q1.1 hfac0 hfac1 Ds.1 (QIdem.Glue.one_comp_hom L Ds hDs)
    (DB' : ZMod p ⊗[R] GB.level v →ₐc[ZMod p] ZMod p ⊗[R] GB.level v)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (Dp : GG.level v →ₐc[R] GG.level v) :
      ZMod p ⊗[R] GG.level v →+* ZMod p ⊗[R] GG.level v) D.1
    hI2
    (QIdem.Glue.spec_map_comp_ιp (Dp : GG.level v →ₐc[R] GG.level v) ι T hDpι ιp hιp₁ hιp₂ D.1 hD D.2)
    (QIdem.Glue.val_eq_of_comp_eq' D q0 Ds hDq0) (QIdem.Glue.val_eq_of_comp_eq' D q1 Ds hDq1)

p2m_export "QIdem.Wrap" "diagonal"
end Wrap
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"
end QIdem
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

end QI_glue
p2m_reactivate "P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent.QIdem"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

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

    (u : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hut : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (huι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (u v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)
    (Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] 𝒢.level v)
    (hDpt : ∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] 𝒢.level (v + 1)) =
      (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (𝒢.transition v))
    (hDpι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
      ι v ≫ (O.hecke S (CohCarrier.Gen.dia d)).1)

    (hutor : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v) →
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp (u v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) ∈ O.toricPts (p ^ v))
    (hDptor : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v) →
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) ∈ O.toricPts (p ^ v))

    (uB : ∀ v : ℕ, ℬ.level v →ₐc[Rh] ℬ.level v) (DB : ∀ v : ℕ, ℬ.level v ≃ₐc[Rh] ℬ.level v)
    (DB' : ∀ v : ℕ, ZMod p ⊗[Rh] ℬ.level v ≃ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v)
    (huB : ∀ v : ℕ, (u v).comp (ψ v) = (ψ v).comp (uB v))
    (hDB : ∀ v : ℕ, (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (ψ v) = (ψ v).comp (DB v : ℬ.level v →ₐc[Rh] ℬ.level v))
    (hDB' : ∀ v : ℕ, (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v) =
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (DB v : ℬ.level v →ₐc[Rh] ℬ.level v))

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

    (rS : Fin 2 → ∀ v : ℕ, Spec (CommRingCat.of ((ℬ.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
    (κS : ∀ v : ℕ, (ℬ.baseChange (ZMod p)).level v ≃ₐc[ZMod p] ((𝒜.baseChange (ZMod p)).level v ⊗[ZMod p] (𝒜.baseChange (ZMod p)).level v))

    (hrSfac : ∀ (i : Fin 2) (v : ℕ), Spec.map (CommRingCat.ofHom
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v) : ZMod p ⊗[Rh] ℬ.level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ rS i v = ιp v ≫ (q i).1)

    (hPepi : ∀ v : ℕ, Epi (Spec.map (CommRingCat.ofHom
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v) : ZMod p ⊗[Rh] ℬ.level v →+* ZMod p ⊗[Rh] 𝒢.level v))))

    (hrS0 : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (((κS v).symm.toBialgHom : ((𝒜.baseChange (ZMod p)).level v ⊗[ZMod p] (𝒜.baseChange (ZMod p)).level v) →+* (ℬ.baseChange (ZMod p)).level v).comp
        (Algebra.TensorProduct.includeLeftRingHom : (𝒜.baseChange (ZMod p)).level v →+* ((𝒜.baseChange (ZMod p)).level v ⊗[ZMod p] (𝒜.baseChange (ZMod p)).level v)))) ≫ ι' v = rS 0 v)
    (hrS1 : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (((κS v).symm.toBialgHom : ((𝒜.baseChange (ZMod p)).level v ⊗[ZMod p] (𝒜.baseChange (ZMod p)).level v) →+* (ℬ.baseChange (ZMod p)).level v).comp
        ((Algebra.TensorProduct.includeRight : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] ((𝒜.baseChange (ZMod p)).level v ⊗[ZMod p] (𝒜.baseChange (ZMod p)).level v)) : (𝒜.baseChange (ZMod p)).level v →+* ((𝒜.baseChange (ZMod p)).level v ⊗[ZMod p] (𝒜.baseChange (ZMod p)).level v)))) ≫ ι' v = rS 1 v)
    (hκSt : ∀ v : ℕ, ((κS v).toBialgHom).comp ((ℬ.baseChange (ZMod p)).transition v) =
      (Bialgebra.TensorProduct.map ((𝒜.baseChange (ZMod p)).transition v) ((𝒜.baseChange (ZMod p)).transition v)).comp (κS (v + 1)).toBialgHom)

    (U D : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp O.g))
    (hU : U.1 ≫ pullback.fst O.g σp = pullback.fst O.g σp ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)
    (hD : D.1 ≫ pullback.fst O.g σp = pullback.fst O.g σp ≫ (O.hecke S (CohCarrier.Gen.dia d)).1)

    (Fsch Vsch : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hFsch : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      (schemeHomOverComp x Fsch).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1)

    (DΛ : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hDΛmul : ∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp Λ.f)),
        schemeHomOverComp ((Λ.L.baseChange σp).mul s x y) DΛ =
          (Λ.L.baseChange σp).mul s (schemeHomOverComp x DΛ) (schemeHomOverComp y DΛ))
    (hDq1 : schemeHomOverComp D (q 1) = schemeHomOverComp (q 1) DΛ)
    (hDq0 : schemeHomOverComp D (q 0) = schemeHomOverComp (q 0) DΛ)
    (hUq1 : schemeHomOverComp U (q 1) = schemeHomOverComp (schemeHomOverComp (q 1) Fsch) DΛ)
    :
    ∃ (r : Fin 2 → ∀ v : ℕ, Spec (CommRingCat.of ((ℬ.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
      (ε ε' : ∀ v : ℕ, (ℬ.baseChange (ZMod p)).level v →ₐc[ZMod p] (ℬ.baseChange (ZMod p)).level v),

      (∀ (i : Fin 2) (v : ℕ), Spec.map (CommRingCat.ofHom
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v) : ZMod p ⊗[Rh] ℬ.level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ r i v = ιp v ≫ (q i).1) ∧

      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((ε v) : (ℬ.baseChange (ZMod p)).level v →+* (ℬ.baseChange (ZMod p)).level v)) ≫ r 1 v =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((ε v) : (ℬ.baseChange (ZMod p)).level v →+* (ℬ.baseChange (ZMod p)).level v)) ≫ r 0 v = r 0 v) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((ε' v) : (ℬ.baseChange (ZMod p)).level v →+* (ℬ.baseChange (ZMod p)).level v)) ≫ r 0 v =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((ε' v) : (ℬ.baseChange (ZMod p)).level v →+* (ℬ.baseChange (ZMod p)).level v)) ≫ r 1 v = r 1 v) ∧

      (∀ v, (ε v).comp (ε v) = ε v) ∧ (∀ v, (ε' v).comp (ε' v) = ε' v) ∧
      (∀ v, (ε v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v).comp (ε' v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v) =
        (Algebra.ofId (ZMod p) ((ℬ.baseChange (ZMod p)).level v)).comp (Bialgebra.counitAlgHom (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ∧
      (∀ v, (ε' v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v).comp (ε v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v) =
        (Algebra.ofId (ZMod p) ((ℬ.baseChange (ZMod p)).level v)).comp (Bialgebra.counitAlgHom (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ∧
      (∀ v, WithConv.toConv (ε v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v) *
          WithConv.toConv (ε' v : (ℬ.baseChange (ZMod p)).level v →ₐ[ZMod p] (ℬ.baseChange (ZMod p)).level v) =
        WithConv.toConv (AlgHom.id (ZMod p) ((ℬ.baseChange (ZMod p)).level v))) ∧
      (∀ v, ((ℬ.baseChange (ZMod p)).transition v).comp (ε (v + 1)) = (ε v).comp ((ℬ.baseChange (ZMod p)).transition v)) ∧
      (∀ v, ((ℬ.baseChange (ZMod p)).transition v).comp (ε' (v + 1)) = (ε' v).comp ((ℬ.baseChange (ZMod p)).transition v)) ∧

      (∀ v, (ε v).comp ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (uB v)).comp (ε v)) =
        (ε v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (uB v))) ∧
      (∀ v, (ε v).comp (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v) =
        (DB' v : ZMod p ⊗[Rh] ℬ.level v →ₐc[ZMod p] ZMod p ⊗[Rh] ℬ.level v).comp (ε v)) := by
  refine ⟨rS, fun v => QIdem.projL (κS v), fun v => QIdem.projR (κS v), hrSfac,
    fun v => QIdem.Wrap.pinL1 ℬ (𝒜.baseChange (ZMod p)) v (Λ.L.baseChange σp) (κS v) (ι' v) (hι'base v) (hι'mul v (ZMod p)) (rS 1 v) (hrS1 v),
    fun v => QIdem.Wrap.pinL0 ℬ (𝒜.baseChange (ZMod p)) v (κS v) (ι' v) (rS 0 v) (hrS0 v),
    fun v => QIdem.Wrap.pinR0 ℬ (𝒜.baseChange (ZMod p)) v (Λ.L.baseChange σp) (κS v) (ι' v) (hι'base v) (hι'mul v (ZMod p)) (rS 0 v) (hrS0 v),
    fun v => QIdem.Wrap.pinR1 ℬ (𝒜.baseChange (ZMod p)) v (κS v) (ι' v) (rS 1 v) (hrS1 v),
    fun v => QIdem.projL_comp_projL (κS v), fun v => QIdem.projR_comp_projR (κS v),
    fun v => QIdem.projL_comp_projR_toAlgHom (κS v), fun v => QIdem.projR_comp_projL_toAlgHom (κS v),
    fun v => QIdem.conv_projL_projR (κS v),
    fun v => QIdem.transition_comp_projL (κS v) (κS (v + 1)) ((ℬ.baseChange (ZMod p)).transition v)
      ((𝒜.baseChange (ZMod p)).transition v) (hκSt v),
    fun v => QIdem.transition_comp_projR (κS v) (κS (v + 1)) ((ℬ.baseChange (ZMod p)).transition v)
      ((𝒜.baseChange (ZMod p)).transition v) (hκSt v),
    fun v => QIdem.Wrap.triangular ℬ 𝒢 (𝒜.baseChange (ZMod p)) v (Λ.L.baseChange σp) (κS v) (ι' v) (hι'cl v) (hι'base v) (hι'mul v (ZMod p))
      (rS 0 v) (rS 1 v) (hrS0 v) (hrS1 v) (ψ v) (hPepi v) (ι v) (ιp v) (hιp₁ v) (hιp₂ v) (q 1) (hrSfac 1 v)
      Fsch DΛ (hFsch (ZMod p)) hDΛmul (uB v) (u v) (huB v) _ (huι v) U hU hUq1,
    fun v => QIdem.Wrap.diagonal ℬ 𝒢 (𝒜.baseChange (ZMod p)) v (Λ.L.baseChange σp) (κS v) (ι' v) (hι'cl v) (hι'base v) (hι'mul v (ZMod p))
      (rS 0 v) (rS 1 v) (hrS0 v) (hrS1 v) (ψ v) (hPepi v) (ι v) (ιp v) (hιp₁ v) (hιp₂ v) (q 0) (q 1) (hrSfac 0 v) (hrSfac 1 v)
      DΛ hDΛmul (DB v) (DB' v) (hDB' v) (Dp v) (hDB v) _ (hDpι v) D hD hDq1 hDq0⟩

end S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent
end P2MW
export P2MW.S_ModularCurve_exists_idempotent_pair_baseChange_raynaudQuotient_projector_components_finPts_jHNeronObjectAtP_of_bialgEquiv_of_hecke_descent (solution)
