-- Prove2me | solution 1 for ModularCurve.exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c7a49806-c7a0-51ac-b02f-4a15fefecc4c

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
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range
import Theorems.Thm_Bialgebra_exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit
import Theorems.Thm_Module_free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open scoped TensorProduct
open WithConv

namespace QH

section ConvGroup

variable {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {C : Type} [CommRing C] [Algebra R C]

variable (R G) in

noncomputable def antipodeAlgHom : G →ₐ[R] G :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] lemma antipodeAlgHom_apply (g : G) : antipodeAlgHom R G g = HopfAlgebra.antipode R g :=
  rfl

lemma convMul_comp_antipode_left (φ : WithConv (G →ₐ[R] C)) :
    toConv (φ.ofConv.comp (antipodeAlgHom R G)) * φ = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro g
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let ℛ := Coalgebra.Repr.arbitrary R g
  conv_lhs => rw [← ℛ.eq]
  simp only [map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply,
    antipodeAlgHom_apply]
  rw [← φ.ofConv.commutes, ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ℛ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]

noncomputable scoped instance : Group (WithConv (G →ₐ[R] C)) where
  inv φ := toConv (φ.ofConv.comp (antipodeAlgHom R G))
  inv_mul_cancel φ := convMul_comp_antipode_left φ

lemma convInv_def (φ : WithConv (G →ₐ[R] C)) :
    φ⁻¹ = toConv (φ.ofConv.comp (antipodeAlgHom R G)) := rfl

lemma convInv_apply (φ : WithConv (G →ₐ[R] C)) (g : G) :
    φ⁻¹ g = φ (HopfAlgebra.antipode R g) := rfl

noncomputable scoped instance [Coalgebra.IsCocomm R G] : CommGroup (WithConv (G →ₐ[R] C)) where
  mul_comm := mul_comm

end ConvGroup

section Quot

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [HopfAlgebra R A] (I : Ideal A)
  (h₁ : ∀ a ∈ I, Coalgebra.counit (R := R) a = 0)
  (h₂ : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) a) = 0)
  (h₃ : ∀ a ∈ I, HopfAlgebra.antipode R a ∈ I)

local notation "mkA" => Ideal.Quotient.mkₐ R I

noncomputable def qComul : (A ⧸ I) →ₐ[R] (A ⧸ I) ⊗[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I ((Algebra.TensorProduct.map mkA mkA).comp (Bialgebra.comulAlgHom R A)) h₂

noncomputable def qCounit : (A ⧸ I) →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A) h₁

noncomputable def qAntipode : (A ⧸ I) →ₐ[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom R A)) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (h₃ a ha)

@[scoped simp] lemma qComul_mk (a : A) :
    qComul I h₂ (Ideal.Quotient.mk I a) =
      Algebra.TensorProduct.map mkA mkA (Coalgebra.comul (R := R) a) :=
  Ideal.Quotient.lift_mk I _ _

@[scoped simp] lemma qCounit_mk (a : A) : qCounit I h₁ (Ideal.Quotient.mk I a) = Coalgebra.counit (R := R) a :=
  Ideal.Quotient.lift_mk I _ _

@[scoped simp] lemma qAntipode_mk (a : A) :
    qAntipode I h₃ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (HopfAlgebra.antipode R a) :=
  Ideal.Quotient.lift_mk I _ _

private lemma map_qComul_id_map (c : A ⊗[R] A) :
    Algebra.TensorProduct.map (qComul I h₂) (AlgHom.id R (A ⧸ I))
        (Algebra.TensorProduct.map mkA mkA c) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.map mkA mkA) mkA
        ((Coalgebra.comul (R := R)).rTensor A c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk, qComul_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma map_id_qComul_map (c : A ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id R (A ⧸ I)) (qComul I h₂)
        (Algebra.TensorProduct.map mkA mkA c) =
      Algebra.TensorProduct.map mkA (Algebra.TensorProduct.map mkA mkA)
        ((Coalgebra.comul (R := R)).lTensor A c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk, qComul_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma assoc_map (d : (A ⊗[R] A) ⊗[R] A) :
    Algebra.TensorProduct.assoc R R R (A ⧸ I) (A ⧸ I) (A ⧸ I)
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map mkA mkA) mkA d) =
      Algebra.TensorProduct.map mkA (Algebra.TensorProduct.map mkA mkA)
        (TensorProduct.assoc R A A A d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u z =>
    induction u using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.assoc_tmul, TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma map_qCounit_id_map (c : A ⊗[R] A) :
    Algebra.TensorProduct.map (qCounit I h₁) (AlgHom.id R (A ⧸ I))
        (Algebra.TensorProduct.map mkA mkA c) =
      (Ideal.Quotient.mkₐ R I).toLinearMap.lTensor R ((Coalgebra.counit (R := R)).rTensor A c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, qCounit_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma map_id_qCounit_map (c : A ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id R (A ⧸ I)) (qCounit I h₁)
        (Algebra.TensorProduct.map mkA mkA c) =
      (Ideal.Quotient.mkₐ R I).toLinearMap.rTensor R ((Coalgebra.counit (R := R)).lTensor A c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, qCounit_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma mul'_rTensor_qAntipode_map (c : A ⊗[R] A) :
    LinearMap.mul' R (A ⧸ I) ((qAntipode I h₃).toLinearMap.rTensor (A ⧸ I)
        (Algebra.TensorProduct.map mkA mkA c)) =
      Ideal.Quotient.mk I (LinearMap.mul' R A ((HopfAlgebra.antipode R).rTensor A c)) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      LinearMap.mul'_apply, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      qAntipode_mk, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma mul'_lTensor_qAntipode_map (c : A ⊗[R] A) :
    LinearMap.mul' R (A ⧸ I) ((qAntipode I h₃).toLinearMap.lTensor (A ⧸ I)
        (Algebra.TensorProduct.map mkA mkA c)) =
      Ideal.Quotient.mk I (LinearMap.mul' R A ((HopfAlgebra.antipode R).lTensor A c)) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      LinearMap.mul'_apply, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      qAntipode_mk, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

@[reducible] noncomputable def quotBialgebra : Bialgebra R (A ⧸ I) :=
  Bialgebra.ofAlgHom (qComul I h₂) (qCounit I h₁)
    (by
      refine Ideal.Quotient.algHom_ext R (AlgHom.ext fun a => ?_)
      show Algebra.TensorProduct.assoc R R R (A ⧸ I) (A ⧸ I) (A ⧸ I)
          (Algebra.TensorProduct.map (qComul I h₂) (AlgHom.id R (A ⧸ I))
            (qComul I h₂ (Ideal.Quotient.mkₐ R I a))) =
        Algebra.TensorProduct.map (AlgHom.id R (A ⧸ I)) (qComul I h₂)
          (qComul I h₂ (Ideal.Quotient.mkₐ R I a))
      rw [Ideal.Quotient.mkₐ_eq_mk, qComul_mk, map_qComul_id_map, assoc_map, map_id_qComul_map,
        Coalgebra.coassoc_apply])
    (by
      refine Ideal.Quotient.algHom_ext R (AlgHom.ext fun a => ?_)
      show Algebra.TensorProduct.map (qCounit I h₁) (AlgHom.id R (A ⧸ I))
          (qComul I h₂ (Ideal.Quotient.mkₐ R I a)) =
        (Algebra.TensorProduct.lid R (A ⧸ I)).symm (Ideal.Quotient.mkₐ R I a)
      rw [Ideal.Quotient.mkₐ_eq_mk, qComul_mk, map_qCounit_id_map, Coalgebra.rTensor_counit_comul,
        LinearMap.lTensor_tmul]
      rfl)
    (by
      refine Ideal.Quotient.algHom_ext R (AlgHom.ext fun a => ?_)
      show Algebra.TensorProduct.map (AlgHom.id R (A ⧸ I)) (qCounit I h₁)
          (qComul I h₂ (Ideal.Quotient.mkₐ R I a)) =
        (Algebra.TensorProduct.rid R R (A ⧸ I)).symm (Ideal.Quotient.mkₐ R I a)
      rw [Ideal.Quotient.mkₐ_eq_mk, qComul_mk, map_id_qCounit_map, Coalgebra.lTensor_counit_comul,
        LinearMap.rTensor_tmul]
      rfl)

@[reducible] noncomputable def quotHopfAlgebra : HopfAlgebra R (A ⧸ I) :=
  letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
  { antipode := (qAntipode I h₃).toLinearMap
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show LinearMap.mul' R (A ⧸ I) ((qAntipode I h₃).toLinearMap.rTensor (A ⧸ I)
          (qComul I h₂ (Ideal.Quotient.mk I a))) =
        algebraMap R (A ⧸ I) (qCounit I h₁ (Ideal.Quotient.mk I a))
      rw [qComul_mk, mul'_rTensor_qAntipode_map, HopfAlgebra.mul_antipode_rTensor_comul_apply,
        qCounit_mk]
      rfl
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show LinearMap.mul' R (A ⧸ I) ((qAntipode I h₃).toLinearMap.lTensor (A ⧸ I)
          (qComul I h₂ (Ideal.Quotient.mk I a))) =
        algebraMap R (A ⧸ I) (qCounit I h₁ (Ideal.Quotient.mk I a))
      rw [qComul_mk, mul'_lTensor_qAntipode_map, HopfAlgebra.mul_antipode_lTensor_comul_apply,
        qCounit_mk]
      rfl }

theorem quot_isCocomm [Coalgebra.IsCocomm R A] :
    letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
    Coalgebra.IsCocomm R (A ⧸ I) := by
  letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
  refine ⟨LinearMap.ext fun x => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show TensorProduct.comm R (A ⧸ I) (A ⧸ I) (qComul I h₂ (Ideal.Quotient.mk I a)) =
    qComul I h₂ (Ideal.Quotient.mk I a)
  rw [qComul_mk]
  conv_rhs => rw [← Coalgebra.comm_comul R a]
  generalize Coalgebra.comul (R := R) a = c
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.comm_tmul, TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def mkBialgHom :
    letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
    A →ₐc[R] (A ⧸ I) :=
  letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
  { Ideal.Quotient.mkₐ R I with
    map_smul' := fun r a => map_smul (Ideal.Quotient.mkₐ R I) r a
    counit_comp := by
      apply LinearMap.ext
      intro a
      exact qCounit_mk I h₁ a
    map_comp_comul := by
      apply LinearMap.ext
      intro a
      exact (qComul_mk I h₂ a).symm }

lemma mkBialgHom_apply (a : A) :
    letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
    mkBialgHom I h₁ h₂ a = Ideal.Quotient.mk I a := rfl

variable {L : Type} [CommRing L] [Algebra R L]

noncomputable def ptOfQuot (χ : WithConv ((A ⧸ I) →ₐ[R] L)) : WithConv (A →ₐ[R] L) :=
  toConv (χ.ofConv.comp (Ideal.Quotient.mkₐ R I))

@[scoped simp] lemma ptOfQuot_apply (χ : WithConv ((A ⧸ I) →ₐ[R] L)) (a : A) :
    ptOfQuot I χ a = χ (Ideal.Quotient.mk I a) := rfl

theorem ptOfQuot_injective : Function.Injective (ptOfQuot (R := R) I (L := L)) := by
  intro χ χ' h
  apply WithConv.ext
  refine Ideal.Quotient.algHom_ext R ?_
  exact congrArg WithConv.ofConv h

theorem mem_range_ptOfQuot_iff (φ : WithConv (A →ₐ[R] L)) :
    φ ∈ Set.range (ptOfQuot (R := R) I (L := L)) ↔ ∀ a ∈ I, φ a = 0 := by
  constructor
  · rintro ⟨χ, rfl⟩ a ha
    rw [ptOfQuot_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro h
    exact ⟨toConv (Ideal.Quotient.liftₐ I φ.ofConv h),
      WithConv.ext (Ideal.Quotient.liftₐ_comp I φ.ofConv h)⟩

theorem ptOfQuot_mul (χ χ' : WithConv ((A ⧸ I) →ₐ[R] L)) :
    letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
    ptOfQuot I (χ * χ') = ptOfQuot I χ * ptOfQuot I χ' := by
  letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
  apply WithConv.ext
  exact AlgHom.convMul_comp_bialgHom_distrib χ χ' (mkBialgHom I h₁ h₂)

theorem ptOfQuot_one :
    letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
    ptOfQuot I (1 : WithConv ((A ⧸ I) →ₐ[R] L)) = 1 := by
  letI : Bialgebra R (A ⧸ I) := quotBialgebra I h₁ h₂
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  show (1 : WithConv ((A ⧸ I) →ₐ[R] L)) (Ideal.Quotient.mk I a) = (1 : WithConv (A →ₐ[R] L)) a
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  exact congrArg (algebraMap R L) (qCounit_mk I h₁ a)

end Quot

end QH
p2m_reactivate "P2MW.S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness.QH"

namespace HCOK

variable {R : Type} [CommRing R] {A B : Type} [CommRing A] [HopfAlgebra R A] [CommRing B] [HopfAlgebra R B]
  (ψ : B →ₐc[R] A)

def augI : Ideal A := Ideal.map (ψ : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B))

theorem h₁ : ∀ a ∈ augI ψ, Coalgebra.counit (R := R) a = 0 := by
  intro a ha

  have : augI ψ ≤ RingHom.ker (Bialgebra.counitAlgHom R A) := by
    rw [augI, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
    change Coalgebra.counit (R := R) (ψ b) = 0
    rw [CoalgHomClass.counit_comp_apply]; exact hb
  exact this ha

theorem h₃ : ∀ a ∈ augI ψ, HopfAlgebra.antipode R a ∈ augI ψ := by

  have key : augI ψ ≤ Ideal.comap (QH.antipodeAlgHom R A) (augI ψ) := by
    rw [augI, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change HopfAlgebra.antipode R (ψ b) ∈ Ideal.map (ψ : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B))
    rw [← HopfAlgebra.HopfKerHopf.map_antipode ψ b]
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hb ⊢
    rw [HopfAlgebra.counit_antipode]; exact hb
  intro a ha
  exact key ha

theorem map_map_comul_eq_zero_of_counit_eq_zero {C : Type} [CommRing C] [Algebra R C] (f : B →ₐ[R] C)
    (hf : ∀ b : B, Coalgebra.counit (R := R) b = 0 → f b = 0) (b : B) (hb : Coalgebra.counit (R := R) b = 0) :
    Algebra.TensorProduct.map f f (Coalgebra.comul (R := R) b) = 0 := by
  classical
  let ℛ := Coalgebra.Repr.arbitrary R b

  have hl : ∀ i ∈ ℛ.index, f (ℛ.left i) = algebraMap R C (Coalgebra.counit (R := R) (ℛ.left i)) := by
    intro i _
    have : f (ℛ.left i - algebraMap R B (Coalgebra.counit (R := R) (ℛ.left i))) = 0 := by
      apply hf
      rw [map_sub, Bialgebra.counit_algebraMap]
      exact sub_self _
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  conv_lhs => rw [← ℛ.eq]
  rw [map_sum]
  have step : ∑ i ∈ ℛ.index, Algebra.TensorProduct.map f f (ℛ.left i ⊗ₜ[R] ℛ.right i) =
      (1 : C) ⊗ₜ[R] f (∑ i ∈ ℛ.index, Coalgebra.counit (R := R) (ℛ.left i) • ℛ.right i) := by
    rw [map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Algebra.TensorProduct.map_tmul, hl i hi, Algebra.algebraMap_eq_smul_one, map_smul, TensorProduct.smul_tmul]
  rw [step]

  have hsum : ∑ i ∈ ℛ.index, Coalgebra.counit (R := R) (ℛ.left i) • ℛ.right i = b := by
    have h0 := congrArg (TensorProduct.lid R B) (Coalgebra.sum_counit_tmul_eq ℛ)
    rw [map_sum, TensorProduct.lid_tmul, one_smul] at h0
    simp only [TensorProduct.lid_tmul] at h0
    exact h0
  rw [hsum, hf b hb, TensorProduct.tmul_zero]

theorem map_comul_bialgHom {C : Type} [CommRing C] [Algebra R C] (g : A →ₐ[R] C) (b : B) :
    Algebra.TensorProduct.map g g (Coalgebra.comul (R := R) (ψ b)) =
      Algebra.TensorProduct.map (g.comp (ψ : B →ₐ[R] A)) (g.comp (ψ : B →ₐ[R] A)) (Coalgebra.comul (R := R) b) := by
  rw [← CoalgHomClass.map_comp_comul_apply ψ b]
  generalize Coalgebra.comul (R := R) b = c
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem h₂ : ∀ a ∈ augI ψ, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (augI ψ)) (Ideal.Quotient.mkₐ R (augI ψ))
    (Coalgebra.comul (R := R) a) = 0 := by

  let T : A →ₐ[R] (A ⧸ augI ψ) ⊗[R] (A ⧸ augI ψ) :=
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (augI ψ)) (Ideal.Quotient.mkₐ R (augI ψ))).comp (Bialgebra.comulAlgHom R A)
  have key : augI ψ ≤ RingHom.ker T := by
    change Ideal.map (ψ : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B)) ≤ RingHom.ker T
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (augI ψ)) (Ideal.Quotient.mkₐ R (augI ψ)) (Coalgebra.comul (R := R) (ψ b)) = 0
    rw [map_comul_bialgHom]
    refine map_map_comul_eq_zero_of_counit_eq_zero ((Ideal.Quotient.mkₐ R (augI ψ)).comp (ψ : B →ₐ[R] A)) ?_ b hb
    intro b' hb'
    change Ideal.Quotient.mk (augI ψ) (ψ b') = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hb'
  intro a ha
  exact key ha

section Rank
variable {R : Type} [CommRing R] {A B : Type} [CommRing A] [HopfAlgebra R A] [CommRing B] [HopfAlgebra R B]
  (ψ : B →ₐc[R] A)

theorem finrank_baseChange_quot_mul [Nontrivial R] [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]
    (κ : Type) [Field κ] [Algebra R κ]
    (hφ : Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id κ κ) ψ)) :
    Module.finrank κ (κ ⊗[R] (A ⧸ augI ψ)) * Module.finrank R B = Module.finrank R A := by
  classical
  letI : Bialgebra R (A ⧸ augI ψ) := QH.quotBialgebra (augI ψ) (h₁ ψ) (h₂ ψ)

  let φ := Bialgebra.TensorProduct.map (BialgHom.id κ κ) ψ
  let J : Ideal (κ ⊗[R] A) := augI φ
  letI : Bialgebra κ ((κ ⊗[R] A) ⧸ J) := QH.quotBialgebra J (h₁ φ) (h₂ φ)

  obtain ⟨e, -⟩ := Bialgebra.exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit κ ψ
    (QH.mkBialgHom (augI ψ) (h₁ ψ) (h₂ ψ)) Ideal.Quotient.mk_surjective
    (by change RingHom.ker (Ideal.Quotient.mk (augI ψ)) = _; rw [Ideal.mk_ker]; rfl)
    (QH.mkBialgHom J (h₁ φ) (h₂ φ)) Ideal.Quotient.mk_surjective
    (by change RingHom.ker (Ideal.Quotient.mk J) = _; rw [Ideal.mk_ker]; rfl)
  have hQ : Module.finrank κ ((κ ⊗[R] A) ⧸ J) = Module.finrank κ (κ ⊗[R] (A ⧸ augI ψ)) :=
    e.toLinearEquiv.finrank_eq

  have h5 := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range κ φ
  have hBκ : Module.finrank κ (κ ⊗[R] B) = Module.finrank R B := Module.finrank_baseChange ..
  have hAκ : Module.finrank κ (κ ⊗[R] A) = Module.finrank R A := Module.finrank_baseChange ..
  have hrange : Module.finrank κ (φ : κ ⊗[R] B →ₐ[κ] κ ⊗[R] A).range = Module.finrank R B := by
    rw [← hBκ]
    exact (LinearEquiv.ofInjective ((φ : κ ⊗[R] B →ₐ[κ] κ ⊗[R] A).toLinearMap) hφ).finrank_eq.symm
  rw [hAκ] at h5
  rw [← hQ, h5, hrange]
  rfl

end Rank
p2m_reactivate "P2MW.S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness.QH"

section Main
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {A B : Type} [CommRing A] [HopfAlgebra R A] [CommRing B] [HopfAlgebra R B]
  [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]
  (ψ : B →ₐc[R] A)

theorem coe_tensorMap (κ : Type) [Field κ] [Algebra R κ] (x : κ ⊗[R] B) :
    Bialgebra.TensorProduct.map (BialgHom.id κ κ) ψ x = (ψ : B →ₐ[R] A).toLinearMap.lTensor κ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_hopfCokernel (rA rB rK : ℕ) (hrA : Module.finrank R A = rA) (hrB : Module.finrank R B = rB)
    (hrk : rK * rB = rA) (hrB0 : 0 < rB)
    (hinj : Function.Injective ((ψ : B →ₐ[R] A).toLinearMap.lTensor (IsLocalRing.ResidueField R))) :
    ∃ (K : Type) (_ : CommRing K) (_ : HopfAlgebra R K) (_ : Module.Free R K) (_ : Module.Finite R K)
      (qK : A →ₐc[R] K),
      Function.Surjective qK ∧
      RingHom.ker (qK : A →+* K) = Ideal.map (ψ : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B)) ∧
      Module.finrank R K = rK := by
  classical
  letI hopfK : HopfAlgebra R (A ⧸ augI ψ) := QH.quotHopfAlgebra (augI ψ) (h₁ ψ) (h₂ ψ) (h₃ ψ)
  let qK : A →ₐc[R] (A ⧸ augI ψ) := QH.mkBialgHom (augI ψ) (h₁ ψ) (h₂ ψ)
  haveI : Module.Finite R (A ⧸ augI ψ) := inferInstance

  have hψinj : Function.Injective (ψ : B →ₐ[R] A).toLinearMap := by
    obtain ⟨ρ, hρ⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective (ψ : B →ₐ[R] A).toLinearMap).mpr hinj
    exact Function.LeftInverse.injective (g := ρ) (fun x => LinearMap.congr_fun hρ x)
  have hinjF : Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id (FractionRing R) (FractionRing R)) ψ) := by
    intro x y hxy
    rw [coe_tensorMap, coe_tensorMap] at hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hψinj hxy
  have hinjκ : Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) ψ) := by
    intro x y hxy
    rw [coe_tensorMap, coe_tensorMap] at hxy
    exact hinj hxy

  have hF := finrank_baseChange_quot_mul ψ (FractionRing R) hinjF
  have hκ := finrank_baseChange_quot_mul ψ (IsLocalRing.ResidueField R) hinjκ
  rw [hrA, hrB, ← hrk] at hF hκ
  have hF' := Nat.eq_of_mul_eq_mul_right hrB0 hF
  have hκ' := Nat.eq_of_mul_eq_mul_right hrB0 hκ
  obtain ⟨hfree, hrank⟩ := Module.free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq rK hκ' hF'
  refine ⟨A ⧸ augI ψ, inferInstance, hopfK, hfree, inferInstance, qK, Ideal.Quotient.mk_surjective, ?_, hrank⟩
  change RingHom.ker (Ideal.Quotient.mk (augI ψ)) = _
  rw [Ideal.mk_ker]; rfl

end Main
p2m_reactivate "P2MW.S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness.QH"

end HCOK
p2m_reactivate "P2MW.S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness.QH"

theorem FREEK_hinj {Rh : Type} [CommRing Rh] [IsLocalRing Rh] {p : ℕ} [Fact p.Prime] [Algebra Rh (ZMod p)]
    (hker : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal Rh)
    {A B : Type} [CommRing A] [Algebra Rh A] [CommRing B] [Algebra Rh B] (f : B →ₗ[Rh] A)
    (hinj : Function.Injective (f.lTensor (ZMod p))) :
    Function.Injective (f.lTensor (IsLocalRing.ResidueField Rh)) := by
  classical
  have hsurj : Function.Surjective (Algebra.ofId Rh (ZMod p)) := ZMod.ringHom_surjective (algebraMap Rh (ZMod p))
  have hkereq : IsLocalRing.maximalIdeal Rh = RingHom.ker (Algebra.ofId Rh (ZMod p) : Rh →+* ZMod p) := by
    ext x; rw [RingHom.mem_ker]; exact (hker x).symm
  let e : IsLocalRing.ResidueField Rh ≃ₐ[Rh] ZMod p :=
    (Ideal.quotientEquivAlgOfEq Rh hkereq).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  let eB := (e.toLinearEquiv.rTensor B : IsLocalRing.ResidueField Rh ⊗[Rh] B ≃ₗ[Rh] ZMod p ⊗[Rh] B)
  let eA := (e.toLinearEquiv.rTensor A : IsLocalRing.ResidueField Rh ⊗[Rh] A ≃ₗ[Rh] ZMod p ⊗[Rh] A)
  have hcomm : ∀ x, eA ((f.lTensor (IsLocalRing.ResidueField Rh)) x) = (f.lTensor (ZMod p)) (eB x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  have := congrArg eA hxy
  rw [hcomm, hcomm] at this
  exact eB.injective (hinj this)

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
    :
    ∀ v : ℕ, ∃ (K : Type) (_ : CommRing K) (_ : HopfAlgebra Rh K) (_ : Module.Free Rh K) (_ : Module.Finite Rh K)
      (qK : 𝒢.level v →ₐc[Rh] K),
      Function.Surjective qK ∧
      RingHom.ker (qK : 𝒢.level v →+* K) =
        Ideal.map (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v) (RingHom.ker (Bialgebra.counitAlgHom Rh (ℬ.level v))) ∧
      Module.finrank Rh K = p ^ (v * O.toricRank) := by
  intro v
  have hres' : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal Rh :=
    fun x => (hres x).trans (hRloc x).symm
  have hinj : Function.Injective (((ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v).toLinearMap).lTensor (IsLocalRing.ResidueField Rh)) := by
    apply FREEK_hinj hres'
    intro x y hxy
    apply hjB v
    rw [HCOK.coe_tensorMap, HCOK.coe_tensorMap]
    exact hxy
  have hp : 0 < p := (Fact.out : p.Prime).pos
  exact HCOK.exists_hopfCokernel (ψ v) (p ^ (v * h)) (p ^ (v * hB)) (p ^ (v * O.toricRank))
    (𝒢.finrank_level v) (ℬ.finrank_level v) (by rw [← pow_add, ← Nat.mul_add, hhB]) (pow_pos hp _) hinj

end S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness
end P2MW
export P2MW.S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness (solution)
