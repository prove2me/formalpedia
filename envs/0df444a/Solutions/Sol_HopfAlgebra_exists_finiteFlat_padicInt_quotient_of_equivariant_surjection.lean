-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_padicInt_quotient_of_equivariant_surjection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dc68083b-800a-54df-aebf-a3c51dd8c1d5

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection

open scoped TensorProduct

section FlatClosureInstances

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G]

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

section TripleInclusion

variable [Algebra R G]

noncomputable def tensorInclusion3 (B : Subalgebra F (F ⊗[R] G)) :
    (flatClosure B) ⊗[R] ((flatClosure B) ⊗[R] (flatClosure B)) →ₗ[R] G ⊗[R] (G ⊗[R] G) :=
  ((flatClosure B).val.toLinearMap.rTensor (G ⊗[R] G)).comp
    ((tensorInclusion B).lTensor (flatClosure B))

@[scoped simp]
lemma tensorInclusion3_tmul {B : Subalgebra F (F ⊗[R] G)} (x : flatClosure B)
    (w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B (x ⊗ₜ[R] w) = (x : G) ⊗ₜ[R] (tensorInclusion B w) := by
  simp [tensorInclusion3]

noncomputable def tensorInclusion3' (B : Subalgebra F (F ⊗[R] G)) :
    ((flatClosure B) ⊗[R] (flatClosure B)) ⊗[R] (flatClosure B) →ₗ[R] (G ⊗[R] G) ⊗[R] G :=
  ((tensorInclusion B).rTensor G).comp
    ((flatClosure B).val.toLinearMap.lTensor ((flatClosure B) ⊗[R] (flatClosure B)))

@[scoped simp]
lemma tensorInclusion3'_tmul {B : Subalgebra F (F ⊗[R] G)}
    (w : (flatClosure B) ⊗[R] (flatClosure B)) (z : flatClosure B) :
    tensorInclusion3' B (w ⊗ₜ[R] z) = (tensorInclusion B w) ⊗ₜ[R] (z : G) := by
  simp [tensorInclusion3']

theorem tensorInclusion3_injective [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Function.Injective (tensorInclusion3 B) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free R (flatClosure B) := flatClosure_free B
  unfold tensorInclusion3
  rw [LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective).comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ (tensorInclusion_injective B))

theorem tensorInclusion3_assoc_apply {B : Subalgebra F (F ⊗[R] G)}
    (w : ((flatClosure B) ⊗[R] (flatClosure B)) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B
        (TensorProduct.assoc R (flatClosure B) (flatClosure B) (flatClosure B) w)
      = TensorProduct.assoc R G G G (tensorInclusion3' B w) := by
  induction w with
  | zero => simp
  | tmul a z =>
      induction a with
      | zero => simp
      | tmul x y => simp
      | add a₁ a₂ h₁ h₂ =>
          simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem tensorInclusion_mul {B : Subalgebra F (F ⊗[R] G)}
    (z w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B (z * w) = tensorInclusion B z * tensorInclusion B w := by
  induction z with
  | zero => simp
  | tmul x y =>
      induction w with
      | zero => simp
      | tmul x' y' =>
          simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add b₁ b₂ h₁ h₂ => simp [mul_add, h₁, h₂]
  | add a₁ a₂ h₁ h₂ => simp [add_mul, h₁, h₂]

theorem tensorInclusion_one {B : Subalgebra F (F ⊗[R] G)} :
    tensorInclusion B (1 : (flatClosure B) ⊗[R] (flatClosure B)) = 1 := by
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def, tensorInclusion_tmul]
  simp

theorem val_mul'_tensorInclusion {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((LinearMap.mul' R (flatClosure B) z : flatClosure B) : G)
      = LinearMap.mul' R G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.mul'_apply]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

end TripleInclusion

section CoalgebraBialgebra

variable [Bialgebra R G]

theorem tensorInclusion3'_rTensor_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3' B ((closureComul hB).rTensor (flatClosure B) z)
      = (Coalgebra.comul (R := R) (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem tensorInclusion3_lTensor_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B ((closureComul hB).lTensor (flatClosure B) z)
      = (Coalgebra.comul (R := R) (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem lTensor_val_rTensor_closureCounit {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((flatClosure B).val.toLinearMap.lTensor R)
        ((closureCounit B).rTensor (flatClosure B) z)
      = (Coalgebra.counit (R := R) (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem rTensor_val_lTensor_closureCounit {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((flatClosure B).val.toLinearMap.rTensor R)
        ((closureCounit B).lTensor (flatClosure B) z)
      = (Coalgebra.counit (R := R) (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem closureComul_coassoc [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    TensorProduct.assoc R (flatClosure B) (flatClosure B) (flatClosure B) ∘ₗ
        (closureComul hB).rTensor (flatClosure B) ∘ₗ closureComul hB
      = (closureComul hB).lTensor (flatClosure B) ∘ₗ closureComul hB := by
  apply LinearMap.ext
  intro h
  apply tensorInclusion3_injective B
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [tensorInclusion3_assoc_apply, tensorInclusion3'_rTensor_closureComul,
    tensorInclusion_closureComul, tensorInclusion3_lTensor_closureComul,
    tensorInclusion_closureComul]
  exact Coalgebra.coassoc_apply (h : G)

theorem closureCounit_rTensor_comp_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    (closureCounit B).rTensor (flatClosure B) ∘ₗ closureComul hB
      = TensorProduct.mk R R (flatClosure B) 1 := by
  apply LinearMap.ext
  intro h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    ((flatClosure B).val.toLinearMap) Subtype.val_injective
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul]
  rw [lTensor_val_rTensor_closureCounit, tensorInclusion_closureComul,
    Coalgebra.rTensor_counit_comul]
  rfl

theorem closureCounit_lTensor_comp_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    (closureCounit B).lTensor (flatClosure B) ∘ₗ closureComul hB
      = (TensorProduct.mk R (flatClosure B) R).flip 1 := by
  apply LinearMap.ext
  intro h
  apply Module.Flat.rTensor_preserves_injective_linearMap
    ((flatClosure B).val.toLinearMap) Subtype.val_injective
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearMap.rTensor_tmul]
  rw [rTensor_val_lTensor_closureCounit, tensorInclusion_closureComul,
    Coalgebra.lTensor_counit_comul]
  rfl

theorem closureCounit_one (B : Subalgebra F (F ⊗[R] G)) :
    closureCounit (R := R) (F := F) B 1 = 1 := by
  simp [Bialgebra.counit_one]

theorem closureCounit_mul {B : Subalgebra F (F ⊗[R] G)} (x y : flatClosure B) :
    closureCounit (R := R) (F := F) B (x * y)
      = closureCounit (R := R) (F := F) B x * closureCounit (R := R) (F := F) B y := by
  simp [Bialgebra.counit_mul]

theorem closureComul_one [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    closureComul hB 1 = 1 := by
  apply tensorInclusion_injective B
  rw [tensorInclusion_closureComul, tensorInclusion_one]
  simp [Bialgebra.comul_one]

theorem closureComul_mul [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (x y : flatClosure B) :
    closureComul hB (x * y) = closureComul hB x * closureComul hB y := by
  apply tensorInclusion_injective B
  rw [tensorInclusion_closureComul, tensorInclusion_mul, tensorInclusion_closureComul,
    tensorInclusion_closureComul]
  simp [Bialgebra.comul_mul]

variable (R F) in

@[reducible]
noncomputable def closureCoalgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    Coalgebra R (flatClosure B) where
  comul := closureComul hB
  counit := closureCounit B
  coassoc := closureComul_coassoc hB
  rTensor_counit_comp_comul := closureCounit_rTensor_comp_closureComul hB
  lTensor_counit_comp_comul := closureCounit_lTensor_comp_closureComul hB

variable (R F) in

@[reducible]
noncomputable def closureBialgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    Bialgebra R (flatClosure B) :=
  letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
  Bialgebra.mk' R (flatClosure B)
    (closureCounit_one B)
    (fun {x y} => closureCounit_mul x y)
    (closureComul_one hB)
    (fun {x y} => closureComul_mul hB x y)

end CoalgebraBialgebra

section Hopf

variable [HopfAlgebra R G]

theorem tensorInclusion_rTensor_closureAntipode {B : Subalgebra F (F ⊗[R] G)}
    (hB' : IsAntipodeStable R F B) (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B ((closureAntipode hB').rTensor (flatClosure B) z)
      = (HopfAlgebra.antipode R (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem tensorInclusion_lTensor_closureAntipode {B : Subalgebra F (F ⊗[R] G)}
    (hB' : IsAntipodeStable R F B) (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B ((closureAntipode hB').lTensor (flatClosure B) z)
      = (HopfAlgebra.antipode R (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem closure_mul_antipode_rTensor_comul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    LinearMap.mul' R (flatClosure B) ∘ₗ
        (closureAntipode hB').rTensor (flatClosure B) ∘ₗ closureComul hB
      = (Algebra.linearMap R (flatClosure B)) ∘ₗ closureCounit B := by
  apply LinearMap.ext
  intro h
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply]
  rw [val_mul'_tensorInclusion, tensorInclusion_rTensor_closureAntipode,
    tensorInclusion_closureComul, HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [Algebra.linearMap_apply]

theorem closure_mul_antipode_lTensor_comul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    LinearMap.mul' R (flatClosure B) ∘ₗ
        (closureAntipode hB').lTensor (flatClosure B) ∘ₗ closureComul hB
      = (Algebra.linearMap R (flatClosure B)) ∘ₗ closureCounit B := by
  apply LinearMap.ext
  intro h
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply]
  rw [val_mul'_tensorInclusion, tensorInclusion_lTensor_closureAntipode,
    tensorInclusion_closureComul, HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [Algebra.linearMap_apply]

variable (R F) in

@[reducible]
noncomputable def closureHopfAlgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    HopfAlgebra R (flatClosure B) :=
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  { antipode := closureAntipode hB'
    mul_antipode_rTensor_comul := closure_mul_antipode_rTensor_comul hB hB'
    mul_antipode_lTensor_comul := closure_mul_antipode_lTensor_comul hB hB' }

end Hopf

section Cocomm

variable [HopfAlgebra R G]

theorem tensorInclusion_comm_apply {B : Subalgebra F (F ⊗[R] G)}
    (w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B (TensorProduct.comm R (flatClosure B) (flatClosure B) w)
      = TensorProduct.comm R G G (tensorInclusion B w) := by
  induction w with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => simp [ha, hb]

theorem closureIsCocomm [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    [Coalgebra.IsCocomm R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
    Coalgebra.IsCocomm R (flatClosure B) := by
  letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
  refine ⟨LinearMap.ext fun h => tensorInclusion_injective B ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorInclusion_comm_apply]
  change TensorProduct.comm R G G (tensorInclusion B (closureComul hB h))
    = tensorInclusion B (closureComul hB h)
  rw [tensorInclusion_closureComul]
  exact Coalgebra.comm_comul R (h : G)

end Cocomm

section BialgHomInclusion

variable [HopfAlgebra R G]

noncomputable def closureValBialgHom [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    flatClosure B →ₐc[R] G := by
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  exact
    { toFun := (flatClosure B).val
      map_add' := map_add _
      map_smul' := fun r x => (flatClosure B).val.toLinearMap.map_smul r x
      counit_comp := rfl
      map_comp_comul := LinearMap.ext fun h => tensorInclusion_closureComul hB h
      map_one' := map_one (flatClosure B).val
      map_mul' := map_mul (flatClosure B).val }

@[scoped simp]
theorem closureValBialgHom_apply [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (h : flatClosure B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    closureValBialgHom hB h = (h : G) := rfl

theorem closureValBialgHom_toAlgHom [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    ((closureValBialgHom hB : flatClosure B →ₐc[R] G) : flatClosure B →ₐ[R] G)
      = (flatClosure B).val :=
  AlgHom.ext fun _ => rfl

open WithConv in

theorem convMul_comp_closureVal [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    {L : Type*} [CommRing L] [Algebra R L] (f g : WithConv (G →ₐ[R] L)) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    toConv ((f * g).ofConv.comp (flatClosure B).val)
      = toConv (f.ofConv.comp (flatClosure B).val) * toConv (g.ofConv.comp (flatClosure B).val) := by
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  have h := AlgHom.convMul_comp_bialgHom_distrib f g (closureValBialgHom hB)
  rw [closureValBialgHom_toAlgHom hB] at h
  exact congrArg toConv h

end BialgHomInclusion

end FlatClosureInstances

open scoped TensorProduct

section LyingOver

variable {L : Type*} [Field L] [IsAlgClosed L]

noncomputable def algClosedQuotientMaximal
    {C : Type*} [CommRing C] [Algebra L C] [Algebra.IsIntegral L C]
    (M : Ideal C) [M.IsMaximal] : (C ⧸ M) ≃ₐ[L] L :=
  haveI : Algebra.IsIntegral L (C ⧸ M) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ L M) (Ideal.Quotient.mk_surjective)
  (AlgEquiv.ofBijective (Algebra.ofId L (C ⧸ M))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := C ⧸ M))).symm

theorem algClosedQuotientMaximal_comp_mk_ker
    {C : Type*} [CommRing C] [Algebra L C] [Algebra.IsIntegral L C]
    (M : Ideal C) [M.IsMaximal] :
    RingHom.ker ((algClosedQuotientMaximal M).toAlgHom.comp (Ideal.Quotient.mkₐ L M)) = M := by
  ext c
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem exists_algHom_of_finite_of_isAlgClosed
    {C : Type*} [CommRing C] [Nontrivial C] [Algebra L C] [Module.Finite L C] :
    ∃ _ψ : C →ₐ[L] L, True := by
  haveI : Algebra.IsIntegral L C := .of_finite L C
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  exact ⟨(algClosedQuotientMaximal M).toAlgHom.comp (Ideal.Quotient.mkₐ L M), trivial⟩

omit [IsAlgClosed L] in

theorem algHom_toSelf_ext_ker {A : Type*} [CommRing A] [Algebra L A]
    {f g : A →ₐ[L] L} (h : RingHom.ker (f : A →+* L) = RingHom.ker (g : A →+* L)) : f = g := by
  ext a
  have ha : g (a - algebraMap L A (f a)) = 0 := by
    have : a - algebraMap L A (f a) ∈ RingHom.ker (g : A →+* L) := by
      rw [← h]; simp [RingHom.mem_ker, AlgHom.commutes]
    exact this
  rw [map_sub, sub_eq_zero, g.commutes] at ha
  exact ha.symm

theorem exists_algHom_comp_val_eq
    {C : Type*} [CommRing C] [Algebra L C] [Module.Finite L C]
    (A : Subalgebra L C) (φ : A →ₐ[L] L) :
    ∃ ψ : C →ₐ[L] L, ψ.comp A.val = φ := by
  haveI : Algebra.IsIntegral L C := .of_finite L C
  letI : Algebra A C := A.val.toAlgebra
  haveI : IsScalarTower L A C := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A C := .tower_top L
  have hφsurj : Function.Surjective φ := fun l => ⟨algebraMap L A l, φ.commutes l⟩
  haveI hker_max : (RingHom.ker (φ : A →+* L)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective φ hφsurj
  have hker_le : RingHom.ker (algebraMap A C) ≤ RingHom.ker (φ : A →+* L) :=
    ((RingHom.injective_iff_ker_eq_bot (algebraMap A C)).mp Subtype.val_injective).symm ▸ bot_le
  obtain ⟨M, hM_max, hM_comap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker (φ : A →+* L)) hker_le
  haveI := hM_max
  refine ⟨(algClosedQuotientMaximal M).toAlgHom.comp (Ideal.Quotient.mkₐ L M),
    algHom_toSelf_ext_ker ?_⟩
  rw [← hM_comap]
  ext a
  simp only [RingHom.mem_ker, Ideal.mem_comap]
  show (algClosedQuotientMaximal M) ((Ideal.Quotient.mkₐ L M) (A.val a)) = 0
    ↔ (algebraMap A C) a ∈ M
  rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mkₐ_eq_mk]
  exact ⟨fun h => (algClosedQuotientMaximal M).injective (h.trans (map_zero _).symm),
    fun h => show (algClosedQuotientMaximal M) ((Ideal.Quotient.mk M)
      ((algebraMap A C) a)) = 0 by rw [h, map_zero]⟩

theorem exists_algHom_comp_eq_of_finite_of_injective
    {A : Type*} [CommRing A] [Algebra L A]
    {C : Type*} [CommRing C] [Algebra L C] [Module.Finite L C]
    (ι : A →ₐ[L] C) (hι : Function.Injective ι) (φ : A →ₐ[L] L) :
    ∃ ψ : C →ₐ[L] L, ψ.comp ι = φ := by
  let ι' : A ≃ₐ[L] ι.range := AlgEquiv.ofInjective ι hι
  obtain ⟨ψ, hψ⟩ := exists_algHom_comp_val_eq ι.range (φ.comp ι'.symm.toAlgHom)
  refine ⟨ψ, AlgHom.ext fun a => ?_⟩
  calc ψ (ι a) = (ψ.comp ι.range.val) (ι' a) := by rw [AlgHom.comp_apply]; rfl
    _ = φ (ι'.symm (ι' a)) := by rw [hψ]; rfl
    _ = φ a := by rw [ι'.symm_apply_apply]

end LyingOver

section FinitePoints

variable {L : Type*} [Field L] {C : Type*} [CommRing C] [Algebra L C] [Module.Finite L C]

theorem finite_algHom_of_finite : Finite (C →ₐ[L] L) := by
  haveI : IsArtinianRing C := isArtinian_of_tower L inferInstance
  have hinj : Function.Injective
      (fun ψ : C →ₐ[L] L => (⟨RingHom.ker (ψ : C →+* L),
        RingHom.ker_isPrime (ψ : C →+* L)⟩ : PrimeSpectrum C)) := by
    intro ψ₁ ψ₂ hk
    replace hk := congrArg PrimeSpectrum.asIdeal hk
    exact algHom_toSelf_ext_ker (L := L) hk
  exact Finite.of_injective _ hinj

theorem finite_algHom_toField_of_finite_tensor {R : Type*} [CommRing R]
    {G : Type*} [CommRing G] [Algebra R G] [Algebra R L] [Module.Finite L (L ⊗[R] G)] :
    Finite (G →ₐ[R] L) :=
  Finite.of_equiv _ (AlgHom.liftEquiv R L G L).symm

end FinitePoints

section ResSurjective

open scoped TensorProduct

variable {R : Type*} [CommRing R] {G : Type*} [CommRing G] [Algebra R G]
variable {L : Type*} [Field L] [IsAlgClosed L] [Algebra R L]

noncomputable def subalgebraBaseChange (H : Subalgebra R G) : L ⊗[R] H →ₐ[L] L ⊗[R] G :=
  Algebra.TensorProduct.map (AlgHom.id L L) H.val

omit [IsAlgClosed L] in
theorem subalgebraBaseChange_injective [Module.Flat R L] (H : Subalgebra R G) :
    Function.Injective (subalgebraBaseChange H : L ⊗[R] H →ₐ[L] L ⊗[R] G) := by
  show Function.Injective
    (TensorProduct.map (LinearMap.id : L →ₗ[R] L) H.val.toLinearMap)
  rw [show TensorProduct.map (LinearMap.id : L →ₗ[R] L) H.val.toLinearMap
    = LinearMap.lTensor L H.val.toLinearMap from rfl]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

omit [IsAlgClosed L] in

theorem liftEquiv_comp_subalgebraVal (H : Subalgebra R G) (φ : G →ₐ[R] L) :
    AlgHom.liftEquiv R L H L (φ.comp H.val)
      = (AlgHom.liftEquiv R L G L φ).comp (subalgebraBaseChange H) := by
  apply (AlgHom.liftEquiv R L H L).symm.injective
  ext h
  rfl

theorem res_surjective_abs [Module.Flat R L] [Module.Finite L (L ⊗[R] G)]
    (H : Subalgebra R G) (χ : H →ₐ[R] L) :
    ∃ φ : G →ₐ[R] L, φ.comp H.val = χ := by
  obtain ⟨ψL, hψL⟩ := exists_algHom_comp_eq_of_finite_of_injective
    (subalgebraBaseChange H) (subalgebraBaseChange_injective H)
    (AlgHom.liftEquiv R L H L χ)
  refine ⟨(AlgHom.liftEquiv R L G L).symm ψL, ?_⟩
  apply (AlgHom.liftEquiv R L H L).injective
  rw [liftEquiv_comp_subalgebraVal, Equiv.apply_symm_apply, hψL]

end ResSurjective

section CallSiteInstances

open scoped TensorProduct

theorem flat_field_ext_of_fractionRing {R F L : Type*} [CommRing R] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra R L] [Algebra F L] [IsScalarTower R F L] :
    Module.Flat R L := by
  haveI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  exact Module.Flat.trans R F L

theorem finite_baseChange_of_finite {R G L : Type*} [CommRing R] [CommRing G] [Algebra R G]
    [CommRing L] [Algebra R L] [Module.Finite R G] :
    Module.Finite L (L ⊗[R] G) :=
  inferInstance

end CallSiteInstances

open scoped TensorProduct
open WithConv Algebra.TensorProduct

set_option maxSynthPendingDepth 3

namespace G3

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
  __ := (inferInstance : Group (WithConv (G →ₐ[R] C)))
  mul_comm := mul_comm

end ConvGroup

section Transl

variable {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {L : Type} [CommRing L] [Algebra R L]

variable (R G L) in

noncomputable def iR : WithConv (G →ₐ[R] L ⊗[R] G) := toConv includeRight

variable (G) in

noncomputable def iLpt (κ : WithConv (G →ₐ[R] L)) : WithConv (G →ₐ[R] L ⊗[R] G) :=
  toConv ((includeLeft : L →ₐ[R] L ⊗[R] G).comp κ.ofConv)

@[scoped simp] lemma iR_apply (g : G) : iR R G L g = (1 : L) ⊗ₜ[R] g := rfl

@[scoped simp] lemma iLpt_apply (κ : WithConv (G →ₐ[R] L)) (g : G) :
    iLpt G κ g = κ g ⊗ₜ[R] (1 : G) := rfl

lemma iLpt_mul (κ κ' : WithConv (G →ₐ[R] L)) : iLpt G (κ * κ') = iLpt G κ * iLpt G κ' := by
  apply WithConv.ext
  show (includeLeft : L →ₐ[R] L ⊗[R] G).comp (κ * κ').ofConv = _
  rw [AlgHom.comp_convMul_distrib]
  rfl

lemma iLpt_inv (κ : WithConv (G →ₐ[R] L)) : iLpt G κ⁻¹ = (iLpt G κ)⁻¹ := rfl

noncomputable def translPt (κ : WithConv (G →ₐ[R] L)) : WithConv (G →ₐ[R] L ⊗[R] G) :=
  iLpt G κ * iR R G L

noncomputable def transl (κ : WithConv (G →ₐ[R] L)) : L ⊗[R] G →ₐ[L] L ⊗[R] G :=
  Algebra.TensorProduct.lift (Algebra.ofId L (L ⊗[R] G)) (translPt κ).ofConv fun _ _ => .all _ _

lemma transl_tmul (κ : WithConv (G →ₐ[R] L)) (a : L) (g : G) :
    transl κ (a ⊗ₜ[R] g) = a • translPt κ g := by
  rw [transl, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]

lemma transl_one_tmul (κ : WithConv (G →ₐ[R] L)) (g : G) :
    transl κ ((1 : L) ⊗ₜ[R] g) = translPt κ g := by
  rw [transl_tmul, one_smul]

lemma transl_comp_includeRight (κ : WithConv (G →ₐ[R] L)) :
    ((transl κ).restrictScalars R).comp includeRight = (translPt κ).ofConv :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ _

lemma transl_comp_iR (κ : WithConv (G →ₐ[R] L)) :
    ((transl κ).restrictScalars R).comp (iR R G L).ofConv = (translPt κ).ofConv :=
  transl_comp_includeRight κ

lemma transl_comp_iR' (κ : WithConv (G →ₐ[R] L)) :
    toConv (((transl κ).restrictScalars R).comp (iR R G L).ofConv) = translPt κ :=
  WithConv.ext (transl_comp_includeRight κ)

lemma comp_iLpt (T : L ⊗[R] G →ₐ[L] L ⊗[R] G) (κ : WithConv (G →ₐ[R] L)) :
    toConv ((T.restrictScalars R).comp (iLpt G κ).ofConv) = iLpt G κ := by
  apply WithConv.ext
  apply AlgHom.ext
  intro g
  show T (κ g ⊗ₜ[R] 1) = κ g ⊗ₜ[R] 1
  have : (κ g ⊗ₜ[R] (1 : G)) = algebraMap L (L ⊗[R] G) (κ g) := rfl
  rw [this, AlgHom.commutes]

lemma algHom_ext_iR {C : Type} [Semiring C] [Algebra L C] [Algebra R C] [IsScalarTower R L C]
    {f g : L ⊗[R] G →ₐ[L] C}
    (h : (f.restrictScalars R).comp (iR R G L).ofConv = (g.restrictScalars R).comp (iR R G L).ofConv) :
    f = g :=
  Algebra.TensorProduct.ext (Subsingleton.elim _ _) h

theorem transl_comp_transl (κ κ' : WithConv (G →ₐ[R] L)) :
    (transl κ).comp (transl κ') = transl (κ' * κ) := by
  apply algHom_ext_iR
  show ((transl κ).restrictScalars R).comp (((transl κ').restrictScalars R).comp (iR R G L).ofConv)
    = _
  rw [transl_comp_iR, transl_comp_iR]
  show ((transl κ).restrictScalars R).comp (iLpt G κ' * iR R G L).ofConv = (translPt (κ' * κ)).ofConv
  rw [AlgHom.comp_convMul_distrib, transl_comp_iR', comp_iLpt]
  show (iLpt G κ' * translPt κ).ofConv = (translPt (κ' * κ)).ofConv
  rw [translPt, translPt, iLpt_mul]
  exact congrArg WithConv.ofConv (mul_assoc (iLpt G κ') (iLpt G κ) (iR R G L)).symm

variable (G) in

noncomputable def constPt (X : Type) [CommSemiring X] [Algebra L X] [Algebra R X]
    [IsScalarTower R L X] (κ : WithConv (G →ₐ[R] L)) : WithConv (G →ₐ[R] X) :=
  toConv (((Algebra.ofId L X).restrictScalars R).comp κ.ofConv)

@[scoped simp] lemma constPt_apply (X : Type) [CommSemiring X] [Algebra L X] [Algebra R X]
    [IsScalarTower R L X] (κ : WithConv (G →ₐ[R] L)) (g : G) :
    constPt G X κ g = algebraMap L X (κ g) := rfl

lemma constPt_self (κ : WithConv (G →ₐ[R] L)) : constPt G L κ = κ := by
  apply WithConv.ext; apply AlgHom.ext; intro g; rfl

lemma iLpt_eq_constPt (κ : WithConv (G →ₐ[R] L)) : iLpt G κ = constPt G (L ⊗[R] G) κ := rfl

lemma comp_iLpt_eq_constPt {X : Type} [CommSemiring X] [Algebra L X] [Algebra R X]
    [IsScalarTower R L X] (T : L ⊗[R] G →ₐ[L] X) (κ : WithConv (G →ₐ[R] L)) :
    toConv ((T.restrictScalars R).comp (iLpt G κ).ofConv) = constPt G X κ := by
  apply WithConv.ext
  apply AlgHom.ext
  intro g
  show T (κ g ⊗ₜ[R] 1) = algebraMap L X (κ g)
  have : (κ g ⊗ₜ[R] (1 : G)) = algebraMap L (L ⊗[R] G) (κ g) := rfl
  rw [this, AlgHom.commutes]

section Comul

variable (R G L) in

noncomputable def jL : WithConv (G →ₐ[R] (L ⊗[R] G) ⊗[L] (L ⊗[R] G)) :=
  toConv (((includeLeft : L ⊗[R] G →ₐ[L] (L ⊗[R] G) ⊗[L] (L ⊗[R] G)).restrictScalars R).comp
    (iR R G L).ofConv)

variable (R G L) in

noncomputable def jR : WithConv (G →ₐ[R] (L ⊗[R] G) ⊗[L] (L ⊗[R] G)) :=
  toConv (((includeRight : L ⊗[R] G →ₐ[L] (L ⊗[R] G) ⊗[L] (L ⊗[R] G)).restrictScalars R).comp
    (iR R G L).ofConv)

@[scoped simp] lemma jL_apply (g : G) : jL R G L g = ((1 : L) ⊗ₜ[R] g) ⊗ₜ[L] 1 := rfl

@[scoped simp] lemma jR_apply (g : G) : jR R G L g = 1 ⊗ₜ[L] ((1 : L) ⊗ₜ[R] g) := rfl

lemma comulAlgHom_comp_iR :
    ((Bialgebra.comulAlgHom L (L ⊗[R] G)).restrictScalars R).comp (iR R G L).ofConv =
      (jL R G L * jR R G L).ofConv := by
  apply AlgHom.ext
  intro g
  show Coalgebra.comul (R := L) ((1 : L) ⊗ₜ[R] g) = (jL R G L * jR R G L) g
  rw [AlgHom.convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  generalize Coalgebra.comul (R := R) g = c
  induction c using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.lift_tmul]
    show _ = (((1 : L) ⊗ₜ[R] x) ⊗ₜ[L] (1 : L ⊗[R] G)) * ((1 : L ⊗[R] G) ⊗ₜ[L] ((1 : L) ⊗ₜ[R] y))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add a b ha hb => rw [TensorProduct.tmul_add, LinearEquiv.map_add, map_add, ha, hb]

theorem map_transl_id_comp_comul (κ : WithConv (G →ₐ[R] L)) :
    (Algebra.TensorProduct.map (transl κ) (AlgHom.id L (L ⊗[R] G))).comp
        (Bialgebra.comulAlgHom L (L ⊗[R] G)) =
      (Bialgebra.comulAlgHom L (L ⊗[R] G)).comp (transl κ) := by
  apply algHom_ext_iR
  show ((Algebra.TensorProduct.map (transl κ) (AlgHom.id L (L ⊗[R] G))).restrictScalars R).comp
      (((Bialgebra.comulAlgHom L (L ⊗[R] G)).restrictScalars R).comp (iR R G L).ofConv) =
    ((Bialgebra.comulAlgHom L (L ⊗[R] G)).restrictScalars R).comp
      (((transl κ).restrictScalars R).comp (iR R G L).ofConv)
  rw [comulAlgHom_comp_iR, transl_comp_iR, AlgHom.comp_convMul_distrib, translPt,
    AlgHom.comp_convMul_distrib, comp_iLpt_eq_constPt, comulAlgHom_comp_iR]

  have h1 : toConv (((Algebra.TensorProduct.map (transl κ) (AlgHom.id L (L ⊗[R] G))).restrictScalars
        R).comp (jL R G L).ofConv) =
      constPt G _ κ * jL R G L := by
    show toConv ((((Algebra.TensorProduct.map (transl κ) (AlgHom.id L (L ⊗[R] G))).comp
      includeLeft).restrictScalars R).comp (iR R G L).ofConv) = _
    rw [Algebra.TensorProduct.map_comp_includeLeft]
    show toConv (((includeLeft : L ⊗[R] G →ₐ[L] (L ⊗[R] G) ⊗[L] (L ⊗[R] G)).restrictScalars R).comp
      (((transl κ).restrictScalars R).comp (iR R G L).ofConv)) = _
    rw [transl_comp_iR, translPt, AlgHom.comp_convMul_distrib, comp_iLpt_eq_constPt]
    rfl
  have h2 : toConv (((Algebra.TensorProduct.map (transl κ) (AlgHom.id L (L ⊗[R] G))).restrictScalars
        R).comp (jR R G L).ofConv) = jR R G L := by
    show toConv ((((Algebra.TensorProduct.map (transl κ) (AlgHom.id L (L ⊗[R] G))).comp
      includeRight).restrictScalars R).comp (iR R G L).ofConv) = _
    rw [Algebra.TensorProduct.map_comp_includeRight]
    rfl
  rw [h1, h2]
  exact congrArg WithConv.ofConv (mul_assoc _ _ _)

theorem map_id_transl_comp_comul [Coalgebra.IsCocomm R G] (κ : WithConv (G →ₐ[R] L)) :
    (Algebra.TensorProduct.map (AlgHom.id L (L ⊗[R] G)) (transl κ)).comp
        (Bialgebra.comulAlgHom L (L ⊗[R] G)) =
      (Bialgebra.comulAlgHom L (L ⊗[R] G)).comp (transl κ) := by
  apply algHom_ext_iR
  show ((Algebra.TensorProduct.map (AlgHom.id L (L ⊗[R] G)) (transl κ)).restrictScalars R).comp
      (((Bialgebra.comulAlgHom L (L ⊗[R] G)).restrictScalars R).comp (iR R G L).ofConv) =
    ((Bialgebra.comulAlgHom L (L ⊗[R] G)).restrictScalars R).comp
      (((transl κ).restrictScalars R).comp (iR R G L).ofConv)
  rw [comulAlgHom_comp_iR, transl_comp_iR, AlgHom.comp_convMul_distrib, translPt,
    AlgHom.comp_convMul_distrib, comp_iLpt_eq_constPt, comulAlgHom_comp_iR]
  have h1 : toConv (((Algebra.TensorProduct.map (AlgHom.id L (L ⊗[R] G)) (transl κ)).restrictScalars
        R).comp (jL R G L).ofConv) = jL R G L := by
    show toConv ((((Algebra.TensorProduct.map (AlgHom.id L (L ⊗[R] G)) (transl κ)).comp
      includeLeft).restrictScalars R).comp (iR R G L).ofConv) = _
    rw [Algebra.TensorProduct.map_comp_includeLeft]
    rfl
  have h2 : toConv (((Algebra.TensorProduct.map (AlgHom.id L (L ⊗[R] G)) (transl κ)).restrictScalars
        R).comp (jR R G L).ofConv) =
      constPt G _ κ * jR R G L := by
    show toConv ((((Algebra.TensorProduct.map (AlgHom.id L (L ⊗[R] G)) (transl κ)).comp
      includeRight).restrictScalars R).comp (iR R G L).ofConv) = _
    rw [Algebra.TensorProduct.map_comp_includeRight]
    show toConv (((includeRight : L ⊗[R] G →ₐ[L] (L ⊗[R] G) ⊗[L] (L ⊗[R] G)).restrictScalars R).comp
      (((transl κ).restrictScalars R).comp (iR R G L).ofConv)) = _
    rw [transl_comp_iR, translPt, AlgHom.comp_convMul_distrib, comp_iLpt_eq_constPt]
    rfl
  rw [h1, h2]
  exact congrArg WithConv.ofConv (mul_left_comm _ _ _)

end Comul

noncomputable def ptExt (φ : WithConv (G →ₐ[R] L)) : L ⊗[R] G →ₐ[L] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L L) φ.ofConv fun _ _ => .all _ _

@[scoped simp] lemma ptExt_tmul (φ : WithConv (G →ₐ[R] L)) (a : L) (g : G) :
    ptExt φ (a ⊗ₜ[R] g) = a * φ g := Algebra.TensorProduct.lift_tmul _ _ _ a g

lemma ptExt_comp_iR (φ : WithConv (G →ₐ[R] L)) :
    ((ptExt φ).restrictScalars R).comp (iR R G L).ofConv = φ.ofConv :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ _

theorem ptExt_comp_transl (φ κ : WithConv (G →ₐ[R] L)) :
    (ptExt φ).comp (transl κ) = ptExt (κ * φ) := by
  apply algHom_ext_iR
  show ((ptExt φ).restrictScalars R).comp (((transl κ).restrictScalars R).comp (iR R G L).ofConv) =
    ((ptExt (κ * φ)).restrictScalars R).comp (iR R G L).ofConv
  rw [transl_comp_iR, ptExt_comp_iR, translPt, AlgHom.comp_convMul_distrib, comp_iLpt_eq_constPt,
    constPt_self]
  show (κ * toConv (((ptExt φ).restrictScalars R).comp (iR R G L).ofConv)).ofConv = _
  rw [ptExt_comp_iR]

lemma ptExt_transl (φ κ : WithConv (G →ₐ[R] L)) (x : L ⊗[R] G) :
    ptExt φ (transl κ x) = ptExt (κ * φ) x := by
  rw [← ptExt_comp_transl]; rfl

section Galois

noncomputable def twist (σ : L →ₐ[R] L) : L ⊗[R] G →ₐ[R] L ⊗[R] G :=
  Algebra.TensorProduct.map σ (AlgHom.id R G)

@[scoped simp] lemma twist_tmul (σ : L →ₐ[R] L) (a : L) (g : G) :
    twist (G := G) σ (a ⊗ₜ[R] g) = σ a ⊗ₜ[R] g := rfl

noncomputable def twistPt (σ : L →ₐ[R] L) (κ : WithConv (G →ₐ[R] L)) : WithConv (G →ₐ[R] L) :=
  toConv (σ.comp κ.ofConv)

@[scoped simp] lemma twistPt_apply (σ : L →ₐ[R] L) (κ : WithConv (G →ₐ[R] L)) (g : G) :
    twistPt σ κ g = σ (κ g) := rfl

lemma twist_comp_iR (σ : L →ₐ[R] L) : (twist (G := G) σ).comp (iR R G L).ofConv = (iR R G L).ofConv := by
  apply AlgHom.ext; intro g; show σ 1 ⊗ₜ[R] g = 1 ⊗ₜ[R] g; rw [map_one]

lemma twist_comp_iLpt (σ : L →ₐ[R] L) (κ : WithConv (G →ₐ[R] L)) :
    (twist (G := G) σ).comp (iLpt G κ).ofConv = (iLpt G (twistPt σ κ)).ofConv := rfl

lemma twist_comp_translPt (σ : L →ₐ[R] L) (κ : WithConv (G →ₐ[R] L)) :
    (twist (G := G) σ).comp (translPt κ).ofConv = (translPt (twistPt σ κ)).ofConv := by
  rw [translPt, AlgHom.comp_convMul_distrib, twist_comp_iR, twist_comp_iLpt]
  rfl

theorem twist_comp_transl (σ : L →ₐ[R] L) (κ : WithConv (G →ₐ[R] L)) :
    (twist σ).comp ((transl κ).restrictScalars R) =
      ((transl (twistPt σ κ)).restrictScalars R).comp (twist σ) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro a
    show twist σ (transl κ (a ⊗ₜ[R] 1)) = transl (twistPt σ κ) (twist σ (a ⊗ₜ[R] 1))
    have h1 : (a ⊗ₜ[R] (1 : G)) = algebraMap L (L ⊗[R] G) a := rfl
    have h2 : (σ a ⊗ₜ[R] (1 : G)) = algebraMap L (L ⊗[R] G) (σ a) := rfl
    rw [h1, AlgHom.commutes, ← h1, twist_tmul, h2, AlgHom.commutes]
  · show (twist σ).comp (((transl κ).restrictScalars R).comp (iR R G L).ofConv) =
      ((transl (twistPt σ κ)).restrictScalars R).comp ((twist σ).comp (iR R G L).ofConv)
    rw [transl_comp_iR, twist_comp_iR, transl_comp_iR, twist_comp_translPt]

lemma twist_transl (σ : L →ₐ[R] L) (κ : WithConv (G →ₐ[R] L)) (x : L ⊗[R] G) :
    twist σ (transl κ x) = transl (twistPt σ κ) (twist σ x) :=
  congr($(twist_comp_transl (G := G) σ κ) x)

end Galois

section Antipode

variable (R G L) in

noncomputable def baseAntipode : L ⊗[R] G →ₐ[R] L ⊗[R] G :=
  Algebra.TensorProduct.map (AlgHom.id R L) (antipodeAlgHom R G)

@[scoped simp] lemma baseAntipode_tmul (a : L) (g : G) :
    baseAntipode R G L (a ⊗ₜ[R] g) = a ⊗ₜ[R] HopfAlgebra.antipode R g := rfl

lemma baseAntipode_comp_translPt (κ : WithConv (G →ₐ[R] L)) :
    (baseAntipode R G L).comp (translPt κ).ofConv = (iLpt G κ * (iR R G L)⁻¹).ofConv := by
  rw [translPt, AlgHom.comp_convMul_distrib]
  have h1 : (baseAntipode R G L).comp (iLpt G κ).ofConv = (iLpt G κ).ofConv := by
    apply AlgHom.ext; intro g
    show κ g ⊗ₜ[R] HopfAlgebra.antipode R (1 : G) = κ g ⊗ₜ[R] 1
    rw [HopfAlgebra.antipode_one]
  have h2 : (baseAntipode R G L).comp (iR R G L).ofConv = (iR R G L)⁻¹.ofConv := rfl
  rw [h1, h2]

theorem translPt_antipode [Coalgebra.IsCocomm R G] (κ : WithConv (G →ₐ[R] L)) (g : G) :
    translPt κ (HopfAlgebra.antipode R g) = baseAntipode R G L (translPt κ⁻¹ g) := by
  have h1 : translPt κ (HopfAlgebra.antipode R g) = (translPt κ)⁻¹ g := rfl
  have h2 : (translPt κ)⁻¹ = iLpt G κ⁻¹ * (iR R G L)⁻¹ := mul_inv (iLpt G κ) (iR R G L)
  rw [h1, h2]
  exact (congr($(baseAntipode_comp_translPt (L := L) κ⁻¹) g)).symm

end Antipode

end Transl

section Descent

variable {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {F : Type} [Field F] [Algebra R F] {L : Type} [Field L] [Algebra R L] [Algebra F L]
  [IsScalarTower R F L]

variable (R G F L) in

noncomputable def incl : F ⊗[R] G →ₐ[F] L ⊗[R] G :=
  Algebra.TensorProduct.map (Algebra.ofId F L) (AlgHom.id R G)

@[scoped simp] lemma incl_tmul (q : F) (g : G) : incl R G F L (q ⊗ₜ[R] g) = algebraMap F L q ⊗ₜ[R] g :=
  rfl

lemma incl_one_tmul (g : G) : incl R G F L ((1 : F) ⊗ₜ[R] g) = (1 : L) ⊗ₜ[R] g := by
  rw [incl_tmul, map_one]

theorem incl_injective [Module.Flat R G] : Function.Injective (incl R G F L) := by
  have hcoe : ⇑(incl R G F L) =
      ⇑(((Algebra.ofId F L).toLinearMap.restrictScalars R).rTensor G) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul q g => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hcoe]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap F L).injective

lemma algebraMap_smul_eq (q : F) (y : L ⊗[R] G) : algebraMap F L q • y = q • y :=
  algebraMap_smul L q y

noncomputable abbrev gtwist (σ : L ≃ₐ[F] L) : L ⊗[R] G →ₐ[R] L ⊗[R] G :=
  twist ((σ : L →ₐ[F] L).restrictScalars R)

noncomputable abbrev gtwistPt (σ : L ≃ₐ[F] L) (κ : WithConv (G →ₐ[R] L)) :
    WithConv (G →ₐ[R] L) :=
  twistPt ((σ : L →ₐ[F] L).restrictScalars R) κ

lemma gtwistPt_apply (σ : L ≃ₐ[F] L) (κ : WithConv (G →ₐ[R] L)) (g : G) :
    gtwistPt σ κ g = σ (κ g) := rfl

lemma gtwist_tmul (σ : L ≃ₐ[F] L) (a : L) (g : G) : gtwist (G := G) σ (a ⊗ₜ[R] g) = σ a ⊗ₜ[R] g :=
  rfl

lemma gtwist_incl (σ : L ≃ₐ[F] L) (x : F ⊗[R] G) :
    gtwist (G := G) σ (incl R G F L x) = incl R G F L x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul q g =>
    show σ (algebraMap F L q) ⊗ₜ[R] g = algebraMap F L q ⊗ₜ[R] g
    rw [AlgEquiv.commutes]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

lemma gtwist_smul (σ : L ≃ₐ[F] L) (a : L) (z : L ⊗[R] G) :
    gtwist (G := G) σ (a • z) = σ a • gtwist σ z := by
  have h1 : a • z = (a ⊗ₜ[R] (1 : G)) * z := Algebra.smul_def a z
  have h2 : σ a • gtwist (G := G) σ z = (σ a ⊗ₜ[R] (1 : G)) * gtwist σ z := Algebra.smul_def _ _
  rw [h1, h2, map_mul, gtwist_tmul]

theorem basis_repr_gtwist {ι : Type} (b : Module.Basis ι R G) (σ : L ≃ₐ[F] L) (z : L ⊗[R] G)
    (i : ι) :
    (Algebra.TensorProduct.basis L b).repr (gtwist σ z) i =
      σ ((Algebra.TensorProduct.basis L b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a g =>
    rw [gtwist_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul]
    congr 1
    exact (((σ : L →ₐ[F] L).restrictScalars R).commutes _).symm
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem exists_incl_eq_of_fixed [Module.Free R G] [Module.Finite R G]
    (hfix : ∀ c : L, (∀ σ : L ≃ₐ[F] L, σ c = c) → c ∈ Set.range (algebraMap F L))
    {y : L ⊗[R] G} (hy : ∀ σ : L ≃ₐ[F] L, gtwist σ y = y) :
    ∃ x : F ⊗[R] G, incl R G F L x = y := by
  classical
  let b := Module.Free.chooseBasis R G
  let bL := Algebra.TensorProduct.basis L b
  have hc : ∀ i, ∃ q : F, algebraMap F L q = bL.repr y i := fun i =>
    hfix _ fun σ => by rw [← basis_repr_gtwist b σ y i, hy σ]
  choose q hq using hc
  refine ⟨∑ i, q i • ((1 : F) ⊗ₜ[R] b i), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← bL.sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, incl_one_tmul, ← hq i, algebraMap_smul_eq]
  congr 1
  exact (Algebra.TensorProduct.basis_apply b i).symm

variable (K : Subgroup (WithConv (G →ₐ[R] L))) [Fintype K]

noncomputable def sumTransl : (L ⊗[R] G) →ₗ[L] (L ⊗[R] G) :=
  ∑ κ : K, (transl (κ : WithConv (G →ₐ[R] L))).toLinearMap

lemma sumTransl_apply (y : L ⊗[R] G) :
    sumTransl K y = ∑ κ : K, transl (κ : WithConv (G →ₐ[R] L)) y := by
  simp [sumTransl]

lemma sumTransl_of_fixed {y : L ⊗[R] G}
    (hy : ∀ κ ∈ K, transl κ y = y) : sumTransl K y = Fintype.card K • y := by
  rw [sumTransl_apply, Finset.sum_congr rfl fun (κ : K) _ => hy κ κ.2, Finset.sum_const,
    Finset.card_univ]

lemma transl_sumTransl {κ : WithConv (G →ₐ[R] L)} (hκ : κ ∈ K) (y : L ⊗[R] G) :
    transl κ (sumTransl K y) = sumTransl K y := by
  rw [sumTransl_apply, map_sum]
  have h : ∀ κ' : K, transl κ (transl (κ' : WithConv (G →ₐ[R] L)) y) =
      transl ((κ' * ⟨κ, hκ⟩ : K) : WithConv (G →ₐ[R] L)) y := fun κ' => by
    rw [← AlgHom.comp_apply, transl_comp_transl]; rfl
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.mulRight (⟨κ, hκ⟩ : K)) _ _ fun _ => rfl

lemma gtwist_sumTransl (σ : L ≃ₐ[F] L) (hK : ∀ κ ∈ K, gtwistPt σ κ ∈ K) (y : L ⊗[R] G) :
    gtwist σ (sumTransl K y) = sumTransl K (gtwist σ y) := by
  rw [sumTransl_apply, sumTransl_apply, map_sum]
  let e : K → K := fun κ => ⟨gtwistPt σ κ, hK κ κ.2⟩
  have he : Function.Bijective e := by
    refine Finite.injective_iff_bijective.mp fun κ₁ κ₂ h => ?_
    apply Subtype.ext
    apply WithConv.ext
    apply AlgHom.ext
    intro g
    have h' := congr(($(congrArg Subtype.val h) : WithConv (G →ₐ[R] L)) g)
    exact σ.injective h'
  exact Fintype.sum_bijective e he _ _ fun κ => twist_transl _ _ _

variable [Module.Free R G] [Module.Finite R G]
  (hfix : ∀ c : L, (∀ σ : L ≃ₐ[F] L, σ c = c) → c ∈ Set.range (algebraMap F L))
  (hK : ∀ (σ : L ≃ₐ[F] L), ∀ κ ∈ K, gtwistPt σ κ ∈ K)

include hfix hK in
theorem exists_incl_eq_sumTransl_incl (x : F ⊗[R] G) :
    ∃ x' : F ⊗[R] G, incl R G F L x' = sumTransl K (incl R G F L x) :=
  exists_incl_eq_of_fixed hfix fun σ => by rw [gtwist_sumTransl K σ (hK σ), gtwist_incl]

noncomputable def dSum : (F ⊗[R] G) →ₗ[F] (F ⊗[R] G) where
  toFun x := (exists_incl_eq_sumTransl_incl K hfix hK x).choose
  map_add' x y := incl_injective (L := L) (by
    have hx := (exists_incl_eq_sumTransl_incl K hfix hK x).choose_spec
    have hy := (exists_incl_eq_sumTransl_incl K hfix hK y).choose_spec
    have hxy := (exists_incl_eq_sumTransl_incl K hfix hK (x + y)).choose_spec
    generalize (exists_incl_eq_sumTransl_incl K hfix hK (x + y)).choose = a at hxy ⊢
    generalize (exists_incl_eq_sumTransl_incl K hfix hK x).choose = b at hx ⊢
    generalize (exists_incl_eq_sumTransl_incl K hfix hK y).choose = c at hy ⊢
    rw [map_add, hxy, hx, hy, map_add (incl R G F L), map_add])
  map_smul' q x := incl_injective (L := L) (by
    have hx := (exists_incl_eq_sumTransl_incl K hfix hK x).choose_spec
    have hqx := (exists_incl_eq_sumTransl_incl K hfix hK (q • x)).choose_spec
    generalize (exists_incl_eq_sumTransl_incl K hfix hK (q • x)).choose = a at hqx ⊢
    generalize (exists_incl_eq_sumTransl_incl K hfix hK x).choose = b at hx ⊢
    simp only [RingHom.id_apply]
    rw [map_smul, hx, hqx, map_smul (incl R G F L), ← algebraMap_smul_eq q,
      map_smul (sumTransl K), algebraMap_smul_eq])

lemma incl_dSum (x : F ⊗[R] G) :
    incl R G F L (dSum K hfix hK x) = sumTransl K (incl R G F L x) :=
  (exists_incl_eq_sumTransl_incl K hfix hK x).choose_spec

omit [Fintype K] [Module.Free R G] [Module.Finite R G] in

def invSubalg : Subalgebra F (F ⊗[R] G) where
  carrier := {x | ∀ κ ∈ K, transl κ (incl R G F L x) = incl R G F L x}
  mul_mem' {a b} ha hb κ hκ := by rw [map_mul, map_mul, ha κ hκ, hb κ hκ]
  one_mem' κ hκ := by rw [map_one, map_one]
  add_mem' {a b} ha hb κ hκ := by rw [map_add, map_add, ha κ hκ, hb κ hκ]
  zero_mem' κ hκ := by rw [map_zero, map_zero]
  algebraMap_mem' q κ hκ := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F L (L ⊗[R] G), AlgHom.commutes]

omit [Fintype K] [Module.Free R G] [Module.Finite R G] in
lemma mem_invSubalg_iff {x : F ⊗[R] G} :
    x ∈ invSubalg (F := F) K ↔ ∀ κ ∈ K, transl κ (incl R G F L x) = incl R G F L x :=
  Iff.rfl

lemma dSum_mem (x : F ⊗[R] G) : dSum K hfix hK x ∈ invSubalg (F := F) K := fun κ hκ => by
  rw [incl_dSum, transl_sumTransl K hκ]

lemma dSum_of_mem {x : F ⊗[R] G} (hx : x ∈ invSubalg (F := F) K) :
    dSum K hfix hK x = Fintype.card K • x :=
  incl_injective (L := L) (by rw [incl_dSum, sumTransl_of_fixed K hx, map_nsmul])

omit [Fintype K] [Module.Free R G] [Module.Finite R G] in

theorem mem_flatClosure_invSubalg_iff {g : G} :
    g ∈ flatClosure (invSubalg (F := F) K) ↔ ∀ κ ∈ K, translPt κ g = (1 : L) ⊗ₜ[R] g := by
  rw [mem_flatClosure_iff, mem_invSubalg_iff]
  simp only [incl_one_tmul, transl_one_tmul]

end Descent

section Stability

variable {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {F : Type} [Field F] [Algebra R F] {L : Type} [Field L] [Algebra R L] [Algebra F L]
  [IsScalarTower R F L]
  (K : Subgroup (WithConv (G →ₐ[R] L)))

theorem isAntipodeStable_invSubalg [Coalgebra.IsCocomm R G] :
    IsAntipodeStable R F (invSubalg (F := F) (L := L) K) := by
  intro g hg
  rw [mem_flatClosure_invSubalg_iff] at hg ⊢
  intro κ hκ
  rw [translPt_antipode, hg κ⁻¹ (K.inv_mem hκ), baseAntipode_tmul]

variable (R G L) in

noncomputable def Dpt : WithConv (G →ₐ[R] (L ⊗[R] G) ⊗[R] G) :=
  toConv ((Algebra.TensorProduct.map (iR R G L).ofConv (AlgHom.id R G)).comp
    (Bialgebra.comulAlgHom R G))

variable (R G L) in

noncomputable def y₁ : WithConv (G →ₐ[R] (L ⊗[R] G) ⊗[R] G) :=
  toConv ((includeLeft : L ⊗[R] G →ₐ[R] (L ⊗[R] G) ⊗[R] G).comp (iR R G L).ofConv)

variable (R G L) in

noncomputable def y₂ : WithConv (G →ₐ[R] (L ⊗[R] G) ⊗[R] G) := toConv includeRight

lemma Dpt_apply (g : G) :
    Dpt R G L g = TensorProduct.map (iR R G L).ofConv.toLinearMap LinearMap.id
      (Coalgebra.comul (R := R) g) := rfl

lemma Dpt_eq_mul : Dpt R G L = y₁ R G L * y₂ R G L := by
  apply WithConv.ext
  apply AlgHom.ext
  intro g
  rw [AlgHom.convMul_apply]
  show TensorProduct.map (iR R G L).ofConv.toLinearMap LinearMap.id (Coalgebra.comul (R := R) g) = _
  generalize Coalgebra.comul (R := R) g = c
  induction c using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
    show ((1 : L) ⊗ₜ[R] a) ⊗ₜ[R] b =
      (((1 : L) ⊗ₜ[R] a) ⊗ₜ[R] (1 : G)) * ((1 : L ⊗[R] G) ⊗ₜ[R] b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

noncomputable def transl₃ (κ : WithConv (G →ₐ[R] L)) :
    (L ⊗[R] G) ⊗[R] G →ₐ[R] (L ⊗[R] G) ⊗[R] G :=
  Algebra.TensorProduct.map ((transl κ).restrictScalars R) (AlgHom.id R G)

@[scoped simp] lemma transl₃_tmul (κ : WithConv (G →ₐ[R] L)) (y : L ⊗[R] G) (g : G) :
    transl₃ κ (y ⊗ₜ[R] g) = transl κ y ⊗ₜ[R] g := rfl

variable (R G L) in

noncomputable def Φ : L ⊗[R] G →ₐ[R] (L ⊗[R] G) ⊗[R] G :=
  Algebra.TensorProduct.lift
    ((includeLeft : L ⊗[R] G →ₐ[R] (L ⊗[R] G) ⊗[R] G).comp
      (includeLeft : L →ₐ[R] L ⊗[R] G))
    (Dpt R G L).ofConv fun _ _ => .all _ _

lemma Φ_tmul (a : L) (g : G) :
    Φ R G L (a ⊗ₜ[R] g) = ((a ⊗ₜ[R] (1 : G)) ⊗ₜ[R] (1 : G)) * Dpt R G L g :=
  Algebra.TensorProduct.lift_tmul _ _ _ a g

lemma Φ_one_tmul (g : G) : Φ R G L ((1 : L) ⊗ₜ[R] g) = Dpt R G L g := by
  rw [Φ_tmul]
  exact one_mul _

lemma Φ_comp_iR : (Φ R G L).comp (iR R G L).ofConv = (Dpt R G L).ofConv :=
  AlgHom.ext fun g => Φ_one_tmul g

lemma Φ_comp_iLpt (κ : WithConv (G →ₐ[R] L)) :
    toConv ((Φ R G L).comp (iLpt G κ).ofConv) =
      toConv ((includeLeft : L ⊗[R] G →ₐ[R] (L ⊗[R] G) ⊗[R] G).comp (iLpt G κ).ofConv) := by
  apply WithConv.ext; apply AlgHom.ext; intro g
  show Φ R G L (κ g ⊗ₜ[R] 1) = (κ g ⊗ₜ[R] (1 : G)) ⊗ₜ[R] (1 : G)
  rw [Φ_tmul, map_one, mul_one]

theorem transl₃_comp_Dpt (κ : WithConv (G →ₐ[R] L)) :
    (transl₃ κ).comp (Dpt R G L).ofConv = (Φ R G L).comp (translPt κ).ofConv := by
  rw [Dpt_eq_mul, AlgHom.comp_convMul_distrib, translPt, AlgHom.comp_convMul_distrib,
    Φ_comp_iLpt, Φ_comp_iR, Dpt_eq_mul]
  have h1 : toConv ((transl₃ κ).comp (y₁ R G L).ofConv) =
      toConv ((includeLeft : L ⊗[R] G →ₐ[R] (L ⊗[R] G) ⊗[R] G).comp (iLpt G κ).ofConv) *
        y₁ R G L := by
    show toConv (((transl₃ κ).comp includeLeft).comp (iR R G L).ofConv) = _
    rw [transl₃, Algebra.TensorProduct.map_comp_includeLeft]
    show toConv ((includeLeft : L ⊗[R] G →ₐ[R] (L ⊗[R] G) ⊗[R] G).comp
      (((transl κ).restrictScalars R).comp (iR R G L).ofConv)) = _
    rw [transl_comp_iR, translPt, AlgHom.comp_convMul_distrib]
    rfl
  have h2 : toConv ((transl₃ κ).comp (y₂ R G L).ofConv) = y₂ R G L := by
    show toConv ((transl₃ κ).comp includeRight) = _
    rw [transl₃, Algebra.TensorProduct.map_comp_includeRight]
    rfl
  rw [h1, h2]
  exact congrArg WithConv.ofConv (mul_assoc _ _ _)

lemma transl₃_Dpt (κ : WithConv (G →ₐ[R] L)) (g : G) :
    transl₃ κ (Dpt R G L g) = Φ R G L (translPt κ g) :=
  congr($(transl₃_comp_Dpt (L := L) κ) g)

lemma transl₃_Dpt_of_eq {κ : WithConv (G →ₐ[R] L)} {g : G}
    (hg : translPt κ g = (1 : L) ⊗ₜ[R] g) : transl₃ κ (Dpt R G L g) = Dpt R G L g := by
  rw [transl₃_Dpt, hg, Φ_one_tmul]

variable (R G F L) in

noncomputable def j₃ : (F ⊗[R] G) ⊗[F] (F ⊗[R] G) →ₗ[R] (L ⊗[R] G) ⊗[R] G :=
  ((incl R G F L).toLinearMap.restrictScalars R).rTensor G ∘ₗ
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R F F (F ⊗[R] G) G).restrictScalars
      R).toLinearMap

lemma j₃_tmul (v : F ⊗[R] G) (q : F) (g : G) :
    j₃ R G F L (v ⊗ₜ[F] (q ⊗ₜ[R] g)) = incl R G F L (q • v) ⊗ₜ[R] g := rfl

theorem j₃_injective [Module.Flat R G] : Function.Injective (j₃ R G F L) :=
  (Module.Flat.rTensor_preserves_injective_linearMap
      ((incl R G F L).toLinearMap.restrictScalars R) (incl_injective (L := L))).comp
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R F F (F ⊗[R] G) G).restrictScalars
      R).injective

lemma j₃_tensorToGenericFibre (z : G ⊗[R] G) :
    j₃ R G F L (tensorToGenericFibre R F z) =
      TensorProduct.map (iR R G L).ofConv.toLinearMap LinearMap.id z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [tensorToGenericFibre_zero, map_zero, map_zero]
  | tmul a b =>
    rw [tensorToGenericFibre_tmul, j₃_tmul, one_smul, incl_one_tmul, TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [tensorToGenericFibre_add, map_add, map_add, hx, hy]

lemma j₃_tensorToGenericFibre_comul (g : G) :
    j₃ R G F L (tensorToGenericFibre R F (Coalgebra.comul (R := R) g)) = Dpt R G L g :=
  j₃_tensorToGenericFibre _

lemma transl_smul_algebraMap (κ : WithConv (G →ₐ[R] L)) (q : F) (y : L ⊗[R] G) :
    transl κ (q • y) = q • transl κ y := by
  rw [← algebraMap_smul_eq q, map_smul, algebraMap_smul_eq]

variable [Fintype K] [Module.Free R G] [Module.Finite R G]
  (hfix : ∀ c : L, (∀ σ : L ≃ₐ[F] L, σ c = c) → c ∈ Set.range (algebraMap F L))
  (hK : ∀ (σ : L ≃ₐ[F] L), ∀ κ ∈ K, gtwistPt σ κ ∈ K)

theorem j₃_map_dSum (z : (F ⊗[R] G) ⊗[F] (F ⊗[R] G)) :
    j₃ R G F L (TensorProduct.map (dSum K hfix hK) LinearMap.id z) =
      ∑ κ : K, transl₃ (κ : WithConv (G →ₐ[R] L)) (j₃ R G F L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul q g =>
      rw [j₃_tmul, j₃_tmul, map_smul, incl_dSum, map_smul, sumTransl_apply, Finset.smul_sum,
        TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [transl₃_tmul, transl_smul_algebraMap]
    | add w₁ w₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, h₁, h₂]
      simp only [map_add, Finset.sum_add_distrib]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    simp only [map_add, Finset.sum_add_distrib]

theorem map_dSum_comul {g : G} (hg : g ∈ flatClosure (invSubalg (F := F) (L := L) K)) :
    TensorProduct.map (dSum K hfix hK) LinearMap.id
        (tensorToGenericFibre R F (Coalgebra.comul (R := R) g)) =
      Fintype.card K • tensorToGenericFibre R F (Coalgebra.comul (R := R) g) := by
  apply j₃_injective (L := L)
  rw [j₃_map_dSum, j₃_tensorToGenericFibre_comul, map_nsmul, j₃_tensorToGenericFibre_comul]
  rw [mem_flatClosure_invSubalg_iff] at hg
  rw [Finset.sum_congr rfl fun (κ : K) _ => transl₃_Dpt_of_eq (hg κ κ.2), Finset.sum_const,
    Finset.card_univ]

noncomputable def dAvg : (F ⊗[R] G) →ₗ[F] (F ⊗[R] G) :=
  (Fintype.card K : F)⁻¹ • dSum K hfix hK

lemma dAvg_mem (x : F ⊗[R] G) : dAvg K hfix hK x ∈ invSubalg (F := F) (L := L) K :=
  Subalgebra.smul_mem _ (dSum_mem K hfix hK x) _

variable [CharZero F]

lemma dAvg_of_mem {x : F ⊗[R] G} (hx : x ∈ invSubalg (F := F) (L := L) K) :
    dAvg K hfix hK x = x := by
  rw [dAvg, LinearMap.smul_apply, dSum_of_mem K hfix hK hx, ← Nat.cast_smul_eq_nsmul F,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := K)))]

theorem map_dAvg_id_comul {g : G} (hg : g ∈ flatClosure (invSubalg (F := F) (L := L) K)) :
    TensorProduct.map (dAvg K hfix hK) LinearMap.id
        (tensorToGenericFibre R F (Coalgebra.comul (R := R) g)) =
      tensorToGenericFibre R F (Coalgebra.comul (R := R) g) := by
  rw [dAvg, TensorProduct.map_smul_left, LinearMap.smul_apply, map_dSum_comul K hfix hK hg,
    ← Nat.cast_smul_eq_nsmul F, inv_smul_smul₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := K)))]

omit [Fintype K] [Module.Free R G] [Module.Finite R G] [CharZero F] in
lemma comm_tensorToGenericFibre (z : G ⊗[R] G) :
    TensorProduct.comm F _ _ (tensorToGenericFibre R F z) =
      tensorToGenericFibre R F (TensorProduct.comm R G G z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [tensorToGenericFibre_zero, map_zero, map_zero, tensorToGenericFibre_zero]
  | tmul a b =>
    rw [tensorToGenericFibre_tmul, TensorProduct.comm_tmul, TensorProduct.comm_tmul,
      tensorToGenericFibre_tmul]
  | add x y hx hy =>
    rw [tensorToGenericFibre_add, map_add, map_add, hx, hy, tensorToGenericFibre_add]

theorem map_id_dAvg_comul [Coalgebra.IsCocomm R G] {g : G}
    (hg : g ∈ flatClosure (invSubalg (F := F) (L := L) K)) :
    TensorProduct.map LinearMap.id (dAvg K hfix hK)
        (tensorToGenericFibre R F (Coalgebra.comul (R := R) g)) =
      tensorToGenericFibre R F (Coalgebra.comul (R := R) g) := by
  apply (TensorProduct.comm F (F ⊗[R] G) (F ⊗[R] G)).injective
  rw [← TensorProduct.map_comm, comm_tensorToGenericFibre, Coalgebra.comm_comul,
    map_dAvg_id_comul K hfix hK hg]

include hfix hK in

theorem isComulStable_invSubalg [Coalgebra.IsCocomm R G] :
    IsComulStable R F (invSubalg (F := F) (L := L) K) := by
  intro g hg
  have key : TensorProduct.map (dAvg K hfix hK) (dAvg K hfix hK)
      (tensorToGenericFibre R F (Coalgebra.comul (R := R) g)) =
      tensorToGenericFibre R F (Coalgebra.comul (R := R) g) :=
    calc TensorProduct.map (dAvg K hfix hK) (dAvg K hfix hK)
          (tensorToGenericFibre R F (Coalgebra.comul (R := R) g))
        = TensorProduct.map (dAvg K hfix hK) LinearMap.id (TensorProduct.map LinearMap.id
            (dAvg K hfix hK) (tensorToGenericFibre R F (Coalgebra.comul (R := R) g))) := by
          rw [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp]
      _ = tensorToGenericFibre R F (Coalgebra.comul (R := R) g) := by
          rw [map_id_dAvg_comul K hfix hK hg, map_dAvg_id_comul K hfix hK hg]
  rw [← key]
  generalize tensorToGenericFibre R F (Coalgebra.comul (R := R) g) = z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v w =>
    rw [TensorProduct.map_tmul]
    exact Submodule.subset_span (Set.mem_image2_of_mem (dAvg_mem K hfix hK v) (dAvg_mem K hfix hK w))
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end Stability

section FinitePoints

variable {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {L : Type} [Field L] [Algebra R L]

lemma algHom_eq_of_ker_eq {A : Type} [CommRing A] [Algebra L A] {χ χ' : A →ₐ[L] L}
    (h : RingHom.ker χ = RingHom.ker χ') : χ = χ' := by
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap L A (χ x) ∈ RingHom.ker χ' := by
    rw [← h, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at hx
  exact hx.symm

theorem finite_points [Module.Finite R G] : Finite (WithConv (G →ₐ[R] L)) := by
  haveI : IsArtinianRing (L ⊗[R] G) := IsArtinianRing.of_finite L (L ⊗[R] G)
  refine Finite.of_injective (fun φ : WithConv (G →ₐ[R] L) =>
    (⟨RingHom.ker (ptExt φ), RingHom.ker_isPrime _⟩ : PrimeSpectrum (L ⊗[R] G))) ?_
  intro φ φ' h
  have h' : ptExt φ = ptExt φ' := algHom_eq_of_ker_eq (congrArg PrimeSpectrum.asIdeal h)
  apply WithConv.ext
  rw [← ptExt_comp_iR φ, ← ptExt_comp_iR φ', h']

end FinitePoints

section Separation

variable {R : Type} [CommRing R] [IsDomain R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {F : Type} [Field F] [Algebra R F] [IsFractionRing R F]
  {L : Type} [Field L] [Algebra R L] [Algebra F L] [IsScalarTower R F L]
  (K : Subgroup (WithConv (G →ₐ[R] L)))
  [Fintype K] [Module.Free R G] [Module.Finite R G]
  (hfix : ∀ c : L, (∀ σ : L ≃ₐ[F] L, σ c = c) → c ∈ Set.range (algebraMap F L))
  (hK : ∀ (σ : L ≃ₐ[F] L), ∀ κ ∈ K, gtwistPt σ κ ∈ K)

omit [IsDomain R] [IsFractionRing R F] [Fintype K] [Module.Free R G] [Module.Finite R G] in

lemma pairwise_isCoprime_ker :
    Pairwise (Function.onFun IsCoprime fun ψ : WithConv (G →ₐ[R] L) => RingHom.ker (ptExt ψ)) := by
  intro ψ ψ' hne
  have hmax : ∀ χ : WithConv (G →ₐ[R] L), (RingHom.ker (ptExt χ)).IsMaximal := fun χ =>
    RingHom.ker_isMaximal_of_surjective (ptExt χ) fun c =>
      ⟨c ⊗ₜ[R] 1, by rw [ptExt_tmul, map_one, mul_one]⟩
  refine Ideal.isCoprime_iff_sup_eq.mpr ((hmax ψ).coprime_of_ne (hmax ψ') fun h => hne ?_)
  have h' : ptExt ψ = ptExt ψ' := algHom_eq_of_ker_eq h
  apply WithConv.ext
  rw [← ptExt_comp_iR ψ, ← ptExt_comp_iR ψ', h']

include hfix hK in

theorem inv_mul_mem_of_eqOn [CharZero L] [Coalgebra.IsCocomm R G]
    {φ φ' : WithConv (G →ₐ[R] L)}
    (hres : ∀ g ∈ flatClosure (invSubalg (F := F) (L := L) K), φ g = φ' g) : φ⁻¹ * φ' ∈ K := by
  classical
  by_contra hnot
  haveI : Finite (WithConv (G →ₐ[R] L)) := finite_points

  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal (pairwise_isCoprime_ker (R := R) (L := L))
    fun ψ => if ψ * φ⁻¹ ∈ K then (1 : L ⊗[R] G) else 0
  have hval : ∀ ψ : WithConv (G →ₐ[R] L), ptExt ψ a = if ψ * φ⁻¹ ∈ K then 1 else 0 := by
    intro ψ
    have h := ha ψ
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
    rw [h]
    split_ifs <;> simp

  have hy1 : ptExt φ (sumTransl K a) = Fintype.card K := by
    rw [sumTransl_apply, map_sum]
    have : ∀ κ : K, ptExt φ (transl (κ : WithConv (G →ₐ[R] L)) a) = 1 := fun κ => by
      rw [ptExt_transl, hval, mul_inv_cancel_right, if_pos κ.2]
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hy0 : ptExt φ' (sumTransl K a) = 0 := by
    rw [sumTransl_apply, map_sum]
    refine Finset.sum_eq_zero fun (κ : K) _ => ?_
    rw [ptExt_transl, hval, if_neg]
    intro hmem
    apply hnot
    have h2 : φ⁻¹ * φ' = (κ : WithConv (G →ₐ[R] L))⁻¹ * ((κ : WithConv (G →ₐ[R] L)) * φ' * φ⁻¹) := by
      rw [mul_assoc, ← mul_assoc _ (κ : WithConv (G →ₐ[R] L)), inv_mul_cancel, one_mul, mul_comm]
    rw [h2]
    exact K.mul_mem (K.inv_mem κ.2) hmem

  have hagree : ∀ b ∈ invSubalg (F := F) (L := L) K,
      ptExt φ (incl R G F L b) = ptExt φ' (incl R G F L b) := by
    intro b hb
    have hb' : b ∈ Submodule.span F
        ((fun g : G => (1 : F) ⊗ₜ[R] g) '' (flatClosure (invSubalg (F := F) (L := L) K) : Set G)) := by
      rw [span_image_flatClosure]; exact hb
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb'
    · rintro _ ⟨g, hg, rfl⟩
      rw [incl_one_tmul, ptExt_tmul, ptExt_tmul, hres g hg]
    · rw [map_zero, map_zero, map_zero]
    · intro b₁ b₂ _ _ h₁ h₂
      rw [map_add, map_add, map_add, h₁, h₂]
    · intro q b _ h
      rw [map_smul, ← algebraMap_smul_eq, map_smul, map_smul, h]
  have hagree' : ∀ a' : L ⊗[R] G, ptExt φ (sumTransl K a') = ptExt φ' (sumTransl K a') := by
    intro a'
    induction a' using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul c g =>
      have h1 : c ⊗ₜ[R] g = c • incl R G F L ((1 : F) ⊗ₜ[R] g) := by
        rw [incl_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, ← incl_dSum K hfix hK, map_smul, map_smul,
        hagree _ (dSum_mem K hfix hK _)]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hcard : (Fintype.card K : L) = 0 := by rw [← hy1, hagree', hy0]
  exact Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := K)) hcard

end Separation

end G3
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection.G3"

namespace G3

open scoped TensorProduct
open WithConv

set_option maxSynthPendingDepth 3

section Assembly

variable {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {F : Type} [Field F] [Algebra R F] {L : Type} [Field L] [Algebra R L] [Algebra F L]
  [IsScalarTower R F L]
  {M : Type} [AddCommGroup M] [DistribMulAction (L ≃ₐ[F] L) M]
  (e : WithConv (G →ₐ[R] L) ≃ M)
  (he_add : ∀ f g, e (f * g) = e f + e g)
  (he_act : ∀ (σ : L ≃ₐ[F] L) (f g : WithConv (G →ₐ[R] L)),
    (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
  {N : Type} [AddCommGroup N] [DistribMulAction (L ≃ₐ[F] L) N]
  (π : M →+ N) (hπ : Function.Surjective π)
  (hπ_act : ∀ (σ : L ≃ₐ[F] L) (m : M), π (σ • m) = σ • (π m))

include he_add in
lemma e_one : e 1 = 0 := by
  have h := he_add 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

noncomputable def labHom : WithConv (G →ₐ[R] L) →* Multiplicative N where
  toFun φ := Multiplicative.ofAdd (π (e φ))
  map_one' := by rw [e_one e he_add, map_zero]; rfl
  map_mul' φ ψ := by rw [he_add, map_add]; rfl

lemma labHom_apply (φ : WithConv (G →ₐ[R] L)) :
    labHom e he_add π φ = Multiplicative.ofAdd (π (e φ)) := rfl

noncomputable def Kst : Subgroup (WithConv (G →ₐ[R] L)) := (labHom e he_add π).ker

lemma mem_Kst_iff {κ : WithConv (G →ₐ[R] L)} : κ ∈ Kst e he_add π ↔ π (e κ) = 0 := by
  rw [Kst, MonoidHom.mem_ker, labHom_apply]
  exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

include he_act hπ_act in

lemma Kst_gal (σ : L ≃ₐ[F] L) :
    ∀ κ ∈ Kst e he_add π, gtwistPt σ κ ∈ Kst e he_add π := by
  intro κ hκ
  rw [mem_Kst_iff] at hκ ⊢
  rw [he_act σ κ (gtwistPt σ κ) fun _ => rfl, hπ_act, hκ, smul_zero]

noncomputable scoped instance [Module.Finite R G] : Fintype (Kst e he_add π) :=
  haveI : Finite (WithConv (G →ₐ[R] L)) := finite_points
  Fintype.ofFinite _

variable (F) in

noncomputable def res (B : Subalgebra F (F ⊗[R] G)) (φ : WithConv (G →ₐ[R] L)) :
    WithConv ((flatClosure B) →ₐ[R] L) :=
  toConv (φ.ofConv.comp (flatClosure B).val)

omit [Algebra F L] [IsScalarTower R F L] in
lemma res_apply (B : Subalgebra F (F ⊗[R] G)) (φ : WithConv (G →ₐ[R] L)) (h : flatClosure B) :
    res F B φ h = φ h := rfl

theorem res_eq_of_mem [Coalgebra.IsCocomm R G] (K : Subgroup (WithConv (G →ₐ[R] L)))
    {φ φ' : WithConv (G →ₐ[R] L)} (hmem : φ⁻¹ * φ' ∈ K) :
    res F (invSubalg (F := F) (L := L) K) φ = res F (invSubalg (F := F) (L := L) K) φ' := by
  apply WithConv.ext
  apply AlgHom.ext
  rintro ⟨h, hh⟩
  show φ h = φ' h
  rw [mem_flatClosure_invSubalg_iff] at hh
  have h1 : φ' = (φ⁻¹ * φ') * φ := by rw [mul_comm, mul_inv_cancel_left]
  calc φ h = ptExt φ ((1 : L) ⊗ₜ[R] h) := by rw [ptExt_tmul, one_mul]
    _ = ptExt φ (transl (φ⁻¹ * φ') ((1 : L) ⊗ₜ[R] h)) := by
        rw [transl_one_tmul, hh _ hmem]
    _ = ptExt ((φ⁻¹ * φ') * φ) ((1 : L) ⊗ₜ[R] h) := ptExt_transl _ _ _
    _ = φ' h := by rw [← h1, ptExt_tmul, one_mul]

section Final

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R G] [Module.Flat R G]
  [Coalgebra.IsCocomm R G] [IsFractionRing R F] [CharZero F]
  (hfix : ∀ c : L, (∀ σ : L ≃ₐ[F] L, σ c = c) → c ∈ Set.range (algebraMap F L))

variable (F L) in

noncomputable abbrev Bq : Subalgebra F (F ⊗[R] G) :=
  invSubalg (F := F) (L := L) (Kst e he_add π)

include he_act hπ_act hfix in
omit [IsFractionRing R F] in
theorem isComulStable_Bq : IsComulStable R F (Bq F L e he_add π) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  exact isComulStable_invSubalg (Kst e he_add π) hfix (Kst_gal e he_add he_act π hπ_act)

omit [DistribMulAction (L ≃ₐ[F] L) M] [DistribMulAction (L ≃ₐ[F] L) N] [IsDomain R]
  [IsPrincipalIdealRing R] [Module.Finite R G] [Module.Flat R G] [IsFractionRing R F] [CharZero F] in
theorem isAntipodeStable_Bq : IsAntipodeStable R F (Bq F L e he_add π) :=
  isAntipodeStable_invSubalg _

include he_act hπ hπ_act hfix in

theorem exists_of_res_surjective_of_sep
    (hsurj : Function.Surjective (res F (Bq F L e he_add π) (L := L)))
    (hsep : ∀ φ φ' : WithConv (G →ₐ[R] L),
      res F (Bq F L e he_add π) φ = res F (Bq F L e he_add π) φ' → φ⁻¹ * φ' ∈ Kst e he_add π) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e' : WithConv (H →ₐ[R] L) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : L ≃ₐ[F] L) (f g : WithConv (H →ₐ[R] L)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  have hB : IsComulStable R F (Bq F L e he_add π) :=
    isComulStable_Bq e he_add he_act π hπ_act hfix
  have hB' : IsAntipodeStable R F (Bq F L e he_add π) := isAntipodeStable_Bq e he_add π
  letI hH : HopfAlgebra R (flatClosure (Bq F L e he_add π)) := closureHopfAlgebra R F hB hB'
  have hcc : Coalgebra.IsCocomm R (flatClosure (Bq F L e he_add π)) := closureIsCocomm hB
  have res_mul : ∀ φ ψ : WithConv (G →ₐ[R] L),
      res F (Bq F L e he_add π) (φ * ψ) = res F (Bq F L e he_add π) φ * res F (Bq F L e he_add π) ψ :=
    fun φ ψ => convMul_comp_closureVal hB φ ψ

  have lab_mul : ∀ φ ψ : WithConv (G →ₐ[R] L), π (e (φ * ψ)) = π (e φ) + π (e ψ) :=
    fun φ ψ => by rw [he_add, map_add]
  have lab_eq : ∀ φ φ' : WithConv (G →ₐ[R] L),
      res F (Bq F L e he_add π) φ = res F (Bq F L e he_add π) φ' → π (e φ) = π (e φ') := by
    intro φ φ' h
    have hk := hsep φ φ' h
    rw [mem_Kst_iff] at hk
    rw [← mul_inv_cancel_left φ φ', lab_mul, hk, add_zero]
  have res_eq : ∀ φ φ' : WithConv (G →ₐ[R] L),
      π (e φ) = π (e φ') → res F (Bq F L e he_add π) φ = res F (Bq F L e he_add π) φ' := by
    intro φ φ' h
    refine res_eq_of_mem (Kst e he_add π) ((mem_Kst_iff e he_add π).mpr ?_)
    have h2 : π (e φ') = π (e φ) + π (e (φ⁻¹ * φ')) := by rw [← lab_mul, mul_inv_cancel_left]
    rw [h] at h2
    exact (left_eq_add.mp h2)

  let s := Function.surjInv hsurj
  have hs : ∀ χ, res F (Bq F L e he_add π) (s χ) = χ := Function.surjInv_eq hsurj
  let e'f : WithConv (flatClosure (Bq F L e he_add π) →ₐ[R] L) → N := fun χ => π (e (s χ))
  have e'_res : ∀ φ, e'f (res F (Bq F L e he_add π) φ) = π (e φ) := fun φ => lab_eq _ _ (hs _)
  have e'_bij : Function.Bijective e'f := by
    refine ⟨fun χ χ' h => ?_, fun n => ?_⟩
    · rw [← hs χ, ← hs χ']
      exact res_eq _ _ h
    · obtain ⟨m, rfl⟩ := hπ n
      obtain ⟨φ, rfl⟩ := e.surjective m
      exact ⟨res F (Bq F L e he_add π) φ, e'_res φ⟩
  refine ⟨flatClosure (Bq F L e he_add π), inferInstance, hH, flatClosure_finite _,
    flatClosure_flat _, hcc, Equiv.ofBijective e'f e'_bij, ?_, ?_⟩
  · intro f g
    obtain ⟨φ, rfl⟩ := hsurj f
    obtain ⟨ψ, rfl⟩ := hsurj g
    show e'f (res F (Bq F L e he_add π) φ * res F (Bq F L e he_add π) ψ) =
      e'f (res F (Bq F L e he_add π) φ) + e'f (res F (Bq F L e he_add π) ψ)
    rw [← res_mul, e'_res, e'_res, e'_res, lab_mul]
  · intro σ f g hfg
    obtain ⟨φ, rfl⟩ := hsurj f
    have hg : g = res F (Bq F L e he_add π) (gtwistPt σ φ) :=
      WithConv.ext (AlgHom.ext fun x => hfg x)
    rw [hg]
    show e'f _ = σ • e'f _
    rw [e'_res, e'_res, he_act σ φ _ (fun _ => rfl), hπ_act]

end Final
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection.G3"

section Generic

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R G] [Module.Flat R G]
  [Coalgebra.IsCocomm R G] [IsFractionRing R F] [CharZero F] [IsAlgClosed L] [CharZero L]
  (hfix : ∀ c : L, (∀ σ : L ≃ₐ[F] L, σ c = c) → c ∈ Set.range (algebraMap F L))

include e he_add he_act π hπ hπ_act hfix in

theorem exists_finiteFlat_quotient_points :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e' : WithConv (H →ₐ[R] L) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : L ≃ₐ[F] L) (f g : WithConv (H →ₐ[R] L)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  haveI : Module.Flat R L := flat_field_ext_of_fractionRing (F := F)
  refine exists_of_res_surjective_of_sep e he_add he_act π hπ hπ_act hfix ?_ ?_
  · intro χ
    obtain ⟨φ, hφ⟩ := res_surjective_abs (flatClosure (Bq F L e he_add π)) χ.ofConv
    exact ⟨toConv φ, WithConv.ext hφ⟩
  · intro φ φ' h
    exact inv_mul_mem_of_eqOn (Kst e he_add π) hfix (Kst_gal e he_add he_act π hπ_act)
      fun g hg => DFunLike.congr_fun (congrArg WithConv.ofConv h) ⟨g, hg⟩

end Generic
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection.G3"

end Assembly
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection.G3"

end G3
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection.G3"

open scoped PadicInt in

theorem G3.padicAlgCl_fixed (p : ℕ) [Fact p.Prime] (c : PadicAlgCl p)
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ c = c) :
    c ∈ Set.range (algebraMap ℚ_[p] (PadicAlgCl p)) := by
  haveI : Algebra.IsAlgebraic ℚ_[p] (PadicAlgCl p) := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ_[p] (PadicAlgCl p) := IsAlgClosure.normal ℚ_[p] (PadicAlgCl p)
  haveI : Algebra.IsSeparable ℚ_[p] (PadicAlgCl p) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ_[p] (PadicAlgCl p) := IsGalois.mk
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed c).mpr hc

open scoped PadicInt in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (G : Type) [CommRing G] [HopfAlgebra ℤ_[p] G] [Module.Finite ℤ_[p] G] [Module.Flat ℤ_[p] G]
    [Coalgebra.IsCocomm ℤ_[p] G]
    {M : Type} [AddCommGroup M] [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    (e : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    {N : Type} [AddCommGroup N] [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) N]
    (π : M →+ N) (hπ : Function.Surjective π)
    (hπ_eq : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M), π (σ • m) = σ • (π m)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e' : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f) :=
  G3.exists_finiteFlat_quotient_points (F := ℚ_[p]) e he_add he_act π hπ hπ_eq (G3.padicAlgCl_fixed p)

end S_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection (solution)
