-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c743aa36-fe5b-5ffe-b123-18079a05b5de

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf
import Theorems.Thm_HopfAlgebra_map_antipode_comul_of_isCocomm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass

open scoped TensorProduct

namespace DESCKDN

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

end FlatClosureInstances

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

namespace DESCKDN

section DESCKDClosureAdditions

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G]

section ModuleLevel
variable [Algebra R G]

theorem tensorInclusion_comm (B : Subalgebra F (F ⊗[R] G))
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B (TensorProduct.comm R (flatClosure B) (flatClosure B) z)
      = TensorProduct.comm R G G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [TensorProduct.comm_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

end ModuleLevel
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section Bialgebra
variable [Bialgebra R G]

theorem comm_closureComul [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    [Coalgebra.IsCocomm R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (h : flatClosure B) :
    TensorProduct.comm R (flatClosure B) (flatClosure B) (closureComul hB h)
      = closureComul hB h := by
  apply tensorInclusion_injective B
  rw [tensorInclusion_comm, tensorInclusion_closureComul, Coalgebra.comm_comul]

end Bialgebra
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

end DESCKDClosureAdditions
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

open scoped TensorProduct

namespace DESCKDN

universe u v w x

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G]

section Bialg

variable {L : Type x} [CommRing L] [Algebra R L]
variable [Bialgebra R G]

noncomputable def lTrans (k : G →ₐ[R] L) : G →ₐ[R] L ⊗[R] G :=
  (Algebra.TensorProduct.map k (AlgHom.id R G)).comp (Bialgebra.comulAlgHom R G)

lemma lTrans_eq_sum (k : G →ₐ[R] L) {g : G} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R g ι𝓡) :
    lTrans k g = ∑ i ∈ 𝓡.index, k (𝓡.left i) ⊗ₜ[R] 𝓡.right i := by
  simp only [lTrans, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← 𝓡.eq, map_sum,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

lemma lTrans_toLinearMap_apply (k : G →ₐ[R] L) (g : G) :
    lTrans k g = TensorProduct.map k.toLinearMap LinearMap.id (Coalgebra.comul (R := R) g) := by
  rw [lTrans_eq_sum k (Coalgebra.Repr.arbitrary R g), ← (Coalgebra.Repr.arbitrary R g).eq,
    map_sum]
  simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq]

noncomputable def invSubalgebra (K : Set (G →ₐ[R] L)) : Subalgebra R G :=
  ⨅ k ∈ K, AlgHom.equalizer (lTrans k)
    (Algebra.TensorProduct.includeRight : G →ₐ[R] L ⊗[R] G)

lemma mem_invSubalgebra_iff {K : Set (G →ₐ[R] L)} {g : G} :
    g ∈ invSubalgebra K ↔ ∀ k ∈ K, lTrans k g = (1 : L) ⊗ₜ[R] g := by
  simp only [invSubalgebra, Algebra.mem_iInf, AlgHom.mem_equalizer,
    Algebra.TensorProduct.includeRight_apply]

lemma lTrans_eq_of_mem {K : Set (G →ₐ[R] L)} {g : G} (hg : g ∈ invSubalgebra K)
    {k : G →ₐ[R] L} (hk : k ∈ K) : lTrans k g = (1 : L) ⊗ₜ[R] g :=
  mem_invSubalgebra_iff.mp hg k hk

end Bialg
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section Saturation

variable {L : Type x} [Field L] [Algebra R L]
variable [Bialgebra R G]

lemma smul_eq_zero_iff_of_injective (hRL : Function.Injective (algebraMap R L))
    {r : R} (hr : r ≠ 0) {x : L ⊗[R] G} : r • x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hru : algebraMap R L r ≠ 0 := fun h0 => hr (hRL (by rw [h0, map_zero]))
    have h1 : (algebraMap R L r) • x = 0 := by rwa [algebraMap_smul]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hru
    · exact h2
  · intro h
    rw [h, smul_zero]

theorem mem_invSubalgebra_of_smul_mem (hRL : Function.Injective (algebraMap R L))
    {K : Set (G →ₐ[R] L)} {g : G} {r : R} (hr : r ≠ 0) (hrg : r • g ∈ invSubalgebra K) :
    g ∈ invSubalgebra K := by
  rw [mem_invSubalgebra_iff] at hrg ⊢
  intro k hk
  have h1 := hrg k hk
  rw [map_smul, TensorProduct.tmul_smul] at h1
  have h2 : r • (lTrans k g - (1 : L) ⊗ₜ[R] g) = 0 := by rw [smul_sub, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero_iff_of_injective (G := G) hRL hr).mp h2)

end Saturation
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section GenericFibre

variable {L : Type x} [Field L] [Algebra R L]
variable [Bialgebra R G]

variable (F) in

noncomputable def genB (K : Set (G →ₐ[R] L)) : Subalgebra F (F ⊗[R] G) :=
  Algebra.adjoin F ((fun g : G => (1 : F) ⊗ₜ[R] g) '' (invSubalgebra K : Set G))

lemma one_tmul_mem_genB {K : Set (G →ₐ[R] L)} {g : G} (hg : g ∈ invSubalgebra K) :
    (1 : F) ⊗ₜ[R] g ∈ genB F K :=
  Algebra.subset_adjoin ⟨g, hg, rfl⟩

lemma invSubalgebra_le_flatClosure_genB (K : Set (G →ₐ[R] L)) :
    invSubalgebra K ≤ flatClosure (genB F K) := fun _ hg =>
  mem_flatClosure_iff.mpr (one_tmul_mem_genB hg)

theorem exists_smul_eq_one_tmul_of_mem_genB [IsDomain R] [IsFractionRing R F]
    {K : Set (G →ₐ[R] L)} {x : F ⊗[R] G} (hx : x ∈ genB F K) :
    ∃ r : R, r ≠ 0 ∧ ∃ h ∈ invSubalgebra K, (algebraMap R F r) • x = (1 : F) ⊗ₜ[R] h := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      obtain ⟨g, hg, rfl⟩ := hy
      exact ⟨1, one_ne_zero, g, hg, by rw [map_one, one_smul]⟩
  | algebraMap c =>
      obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors R) c
      refine ⟨s, nonZeroDivisors.coe_ne_zero s, algebraMap R G a,
        Subalgebra.algebraMap_mem _ a, ?_⟩
      have h1 : (algebraMap R F (s : R)) • (algebraMap F (F ⊗[R] G) c)
          = algebraMap F (F ⊗[R] G) (algebraMap R F a) := by
        rw [Algebra.smul_def, ← map_mul, mul_comm (algebraMap R F (s : R)) c, hs]
      rw [h1, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one a]
  | add y z _ _ hy hz =>
      obtain ⟨r₁, hr₁, h₁, hh₁, e₁⟩ := hy
      obtain ⟨r₂, hr₂, h₂, hh₂, e₂⟩ := hz
      refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, r₂ • h₁ + r₁ • h₂,
        add_mem (Subalgebra.smul_mem _ hh₁ r₂) (Subalgebra.smul_mem _ hh₂ r₁), ?_⟩
      have ey : (algebraMap R F (r₁ * r₂)) • y = (1 : F) ⊗ₜ[R] (r₂ • h₁) := by
        rw [map_mul, mul_comm, mul_smul, e₁, ← one_tmul_smul]
      have ez : (algebraMap R F (r₁ * r₂)) • z = (1 : F) ⊗ₜ[R] (r₁ • h₂) := by
        rw [map_mul, mul_smul, e₂, ← one_tmul_smul]
      rw [smul_add, ey, ez, TensorProduct.tmul_add]
  | mul y z _ _ hy hz =>
      obtain ⟨r₁, hr₁, h₁, hh₁, e₁⟩ := hy
      obtain ⟨r₂, hr₂, h₂, hh₂, e₂⟩ := hz
      refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, h₁ * h₂, mul_mem hh₁ hh₂, ?_⟩
      rw [map_mul, ← smul_mul_smul_comm, e₁, e₂, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem flatClosure_genB [IsDomain R] [IsFractionRing R F] [Module.Flat R G]
    (hRL : Function.Injective (algebraMap R L)) (K : Set (G →ₐ[R] L)) :
    flatClosure (genB F K) = invSubalgebra K := by
  apply le_antisymm
  · intro g hg
    rw [mem_flatClosure_iff] at hg
    obtain ⟨r, hr, h, hh, e⟩ := exists_smul_eq_one_tmul_of_mem_genB hg
    rw [← one_tmul_smul] at e
    have hinj : Function.Injective
        (Algebra.TensorProduct.includeRight : G →ₐ[R] F ⊗[R] G) :=
      Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R F)
    have hrg : r • g = h := hinj (by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply]
      exact e)
    exact mem_invSubalgebra_of_smul_mem hRL hr (hrg ▸ hh)
  · exact invSubalgebra_le_flatClosure_genB K

end GenericFibre
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section Coordinates

variable {ι : Type*}
variable {P : Type*} [AddCommGroup P] [Module R P]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma eq_sum_coord_tmul [Fintype ι] (b : Module.Basis ι R P) (z : N ⊗[R] P) :
    z = ∑ j, (TensorProduct.rid R N ((b.coord j).lTensor N z)) ⊗ₜ[R] b j := by
  induction z with
  | zero => simp
  | tmul n g =>
      conv_lhs => rw [← b.sum_repr g, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Module.Basis.coord_apply,
        TensorProduct.smul_tmul]
  | add x y hx hy =>
      simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
      rw [← hx, ← hy]

lemma eq_sum_tmul_coord [Fintype ι] (b : Module.Basis ι R P) (z : P ⊗[R] N) :
    z = ∑ j, b j ⊗ₜ[R] (TensorProduct.lid R N ((b.coord j).rTensor N z)) := by
  induction z with
  | zero => simp
  | tmul g n =>
      conv_lhs => rw [← b.sum_repr g, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply,
        ← TensorProduct.smul_tmul]
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [← hx, ← hy]

lemma apply_rid_lTensor_coord (b : Module.Basis ι R P) (j : ι) (f : N →ₗ[R] M) (z : N ⊗[R] P) :
    f (TensorProduct.rid R N ((b.coord j).lTensor N z))
      = TensorProduct.rid R M ((b.coord j).lTensor M (f.rTensor P z)) := by
  induction z with
  | zero => simp only [map_zero]
  | tmul n g =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.rid_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma apply_lid_rTensor_coord (b : Module.Basis ι R P) (j : ι) (f : N →ₗ[R] M) (z : P ⊗[R] N) :
    f (TensorProduct.lid R N ((b.coord j).rTensor N z))
      = TensorProduct.lid R M ((b.coord j).rTensor M (f.lTensor P z)) := by
  induction z with
  | zero => simp only [map_zero]
  | tmul g n =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Coordinates
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section Calculus

variable {L : Type x} [CommRing L] [Algebra R L]
variable [Bialgebra R G]

lemma rTensor_lTrans_comul_eq_sum (k : G →ₐ[R] L) {g : G} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R g ι𝓡)
    {κ𝓛 : _ → Type*} (𝓛 : ∀ i, Coalgebra.Repr R (𝓡.left i) (κ𝓛 i)) :
    (lTrans k).toLinearMap.rTensor G (Coalgebra.comul (R := R) g)
      = ∑ i ∈ 𝓡.index, ∑ j ∈ (𝓛 i).index,
          (k ((𝓛 i).left j) ⊗ₜ[R] (𝓛 i).right j) ⊗ₜ[R] 𝓡.right i := by
  rw [← 𝓡.eq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, lTrans_eq_sum k (𝓛 i),
    TensorProduct.sum_tmul]

lemma rTensor_lTrans_comul (k : G →ₐ[R] L) (g : G) :
    (lTrans k).toLinearMap.rTensor G (Coalgebra.comul (R := R) g)
      = (TensorProduct.assoc R L G G).symm
          ((Coalgebra.comul (R := R) (A := G)).lTensor L (lTrans k g)) := by
  let 𝓡 := Coalgebra.Repr.arbitrary R g
  let 𝓛 := fun i => Coalgebra.Repr.arbitrary R (𝓡.left i)
  let 𝓜 := fun i => Coalgebra.Repr.arbitrary R (𝓡.right i)
  have h1 := congrArg (TensorProduct.map k.toLinearMap
      (LinearMap.id : G ⊗[R] G →ₗ[R] G ⊗[R] G)) (Coalgebra.sum_tmul_tmul_eq 𝓡 𝓛 𝓜)
  have h2 := congrArg (TensorProduct.assoc R L G G).symm h1
  simp only [map_sum, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe,
    id_eq, TensorProduct.assoc_symm_tmul] at h2
  rw [rTensor_lTrans_comul_eq_sum k 𝓡 𝓛, h2, lTrans_eq_sum k 𝓡, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.lTensor_tmul, ← (𝓜 i).eq, TensorProduct.tmul_sum, map_sum]
  simp only [TensorProduct.assoc_symm_tmul]

lemma rTensor_includeRight_eq (w : G ⊗[R] G) :
    (Algebra.TensorProduct.includeRight : G →ₐ[R] L ⊗[R] G).toLinearMap.rTensor G w
      = (TensorProduct.assoc R L G G).symm ((1 : L) ⊗ₜ[R] w) := by
  induction w with
  | zero => simp only [LinearMap.map_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero]
  | tmul x y =>
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.includeRight_apply, TensorProduct.assoc_symm_tmul]
  | add x y hx hy => rw [map_add, hx, hy, TensorProduct.tmul_add, map_add]

lemma lTensor_includeRight_eq (w : G ⊗[R] G) :
    (Algebra.TensorProduct.includeRight : G →ₐ[R] L ⊗[R] G).toLinearMap.lTensor G w
      = TensorProduct.assoc R G L G
          (TensorProduct.map (TensorProduct.comm R L G).toLinearMap LinearMap.id
            ((Algebra.TensorProduct.includeRight : G →ₐ[R] L ⊗[R] G).toLinearMap.rTensor G
              w)) := by
  induction w with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
  | tmul x y =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.includeRight_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
        TensorProduct.comm_tmul, LinearMap.id_coe, id_eq, TensorProduct.assoc_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_lTrans_comul_of_mem {K : Set (G →ₐ[R] L)} {g : G} (hg : g ∈ invSubalgebra K)
    {k : G →ₐ[R] L} (hk : k ∈ K) :
    (lTrans k).toLinearMap.rTensor G (Coalgebra.comul (R := R) g)
      = (Algebra.TensorProduct.includeRight : G →ₐ[R] L ⊗[R] G).toLinearMap.rTensor G
          (Coalgebra.comul (R := R) g) := by
  rw [rTensor_lTrans_comul, lTrans_eq_of_mem hg hk, LinearMap.lTensor_tmul,
    rTensor_includeRight_eq]

lemma sum_apply_tmul_comm [Coalgebra.IsCocomm R G] {M : Type*} [AddCommMonoid M] [Module R M]
    (ψ : G ⊗[R] G →ₗ[R] M) {a : G} {ι𝓐 : Type*} (𝓐 : Coalgebra.Repr R a ι𝓐) :
    ∑ j ∈ 𝓐.index, ψ (𝓐.right j ⊗ₜ[R] 𝓐.left j)
      = ∑ j ∈ 𝓐.index, ψ (𝓐.left j ⊗ₜ[R] 𝓐.right j) := by
  have h : ∑ j ∈ 𝓐.index, 𝓐.right j ⊗ₜ[R] 𝓐.left j = Coalgebra.comul (R := R) a := by
    rw [← Coalgebra.comm_comul R a, ← 𝓐.eq, map_sum]
    simp only [TensorProduct.comm_tmul]
  rw [← map_sum, ← map_sum, h, 𝓐.eq]

lemma lTensor_lTrans_comul [Coalgebra.IsCocomm R G] (k : G →ₐ[R] L) (g : G) :
    (lTrans k).toLinearMap.lTensor G (Coalgebra.comul (R := R) g)
      = TensorProduct.assoc R G L G
          (TensorProduct.map (TensorProduct.comm R L G).toLinearMap LinearMap.id
            ((lTrans k).toLinearMap.rTensor G (Coalgebra.comul (R := R) g))) := by
  let 𝓡 := Coalgebra.Repr.arbitrary R g
  let 𝓛 := fun i => Coalgebra.Repr.arbitrary R (𝓡.left i)
  let 𝓜 := fun i => Coalgebra.Repr.arbitrary R (𝓡.right i)
  have h1 := congrArg (TensorProduct.map (LinearMap.id : G →ₗ[R] G)
      (TensorProduct.map k.toLinearMap (LinearMap.id : G →ₗ[R] G)))
    (Coalgebra.sum_tmul_tmul_eq 𝓡 𝓛 𝓜)
  simp only [map_sum, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe,
    id_eq] at h1
  have hL : (lTrans k).toLinearMap.lTensor G (Coalgebra.comul (R := R) g)
      = ∑ i ∈ 𝓡.index, ∑ j ∈ (𝓜 i).index,
          𝓡.left i ⊗ₜ[R] (k ((𝓜 i).left j) ⊗ₜ[R] (𝓜 i).right j) := by
    rw [← 𝓡.eq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, lTrans_eq_sum k (𝓜 i),
      TensorProduct.tmul_sum]
  rw [hL, ← h1, rTensor_lTrans_comul_eq_sum k 𝓡 𝓛, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, map_sum]
  simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    LinearMap.id_coe, id_eq, TensorProduct.assoc_tmul]
  let ψ : G ⊗[R] G →ₗ[R] G ⊗[R] (L ⊗[R] G) :=
    ((TensorProduct.mk R L G).flip (𝓡.right i) ∘ₗ k.toLinearMap).lTensor G
  have hψ : ∀ x y : G, x ⊗ₜ[R] (k y ⊗ₜ[R] 𝓡.right i) = ψ (x ⊗ₜ[R] y) := fun x y => rfl
  simp only [hψ]
  exact (sum_apply_tmul_comm ψ (𝓛 i)).symm

theorem lTensor_lTrans_comul_of_mem [Coalgebra.IsCocomm R G] {K : Set (G →ₐ[R] L)} {g : G}
    (hg : g ∈ invSubalgebra K) {k : G →ₐ[R] L} (hk : k ∈ K) :
    (lTrans k).toLinearMap.lTensor G (Coalgebra.comul (R := R) g)
      = (Algebra.TensorProduct.includeRight : G →ₐ[R] L ⊗[R] G).toLinearMap.lTensor G
          (Coalgebra.comul (R := R) g) := by
  rw [lTensor_lTrans_comul, rTensor_lTrans_comul_of_mem hg hk, ← lTensor_includeRight_eq]

end Calculus
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section ComulStable

variable {L : Type x} [Field L] [Algebra R L]
variable [Bialgebra R G]

theorem exists_isCompl_invSubalgebra [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R G]
    [Module.Flat R G] (hRL : Function.Injective (algebraMap R L)) (K : Set (G →ₐ[R] L)) :
    ∃ C : Submodule R G, IsCompl (Subalgebra.toSubmodule (invSubalgebra K)) C := by
  obtain ⟨C, hC⟩ := exists_isCompl_flatClosure (R := R) (F := FractionRing R) (G := G)
    (genB (FractionRing R) K)
  rw [flatClosure_genB hRL K] at hC
  exact ⟨C, hC⟩

theorem comul_mem_span_of_mem_invSubalgebra [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (hRL : Function.Injective (algebraMap R L)) {K : Set (G →ₐ[R] L)} {g : G}
    (hg : g ∈ invSubalgebra K) :
    Coalgebra.comul (R := R) g ∈ Submodule.span R
      (Set.image2 (· ⊗ₜ[R] ·) (invSubalgebra K : Set G) (invSubalgebra K : Set G)) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R G

  have hu : ∀ j, TensorProduct.rid R G ((b.coord j).lTensor G (Coalgebra.comul (R := R) g))
      ∈ invSubalgebra K := by
    intro j
    rw [mem_invSubalgebra_iff]
    intro k hk
    rw [← AlgHom.toLinearMap_apply, apply_rid_lTensor_coord b j (lTrans k).toLinearMap,
      rTensor_lTrans_comul_of_mem hg hk, ← apply_rid_lTensor_coord b j,
      AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply]

  have hv : ∀ j, TensorProduct.lid R G ((b.coord j).rTensor G (Coalgebra.comul (R := R) g))
      ∈ invSubalgebra K := by
    intro j
    rw [mem_invSubalgebra_iff]
    intro k hk
    rw [← AlgHom.toLinearMap_apply, apply_lid_rTensor_coord b j (lTrans k).toLinearMap,
      lTensor_lTrans_comul_of_mem hg hk, ← apply_lid_rTensor_coord b j,
      AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply]

  obtain ⟨C, hC⟩ := exists_isCompl_invSubalgebra hRL K
  have hq_mem : ∀ x, (Subalgebra.toSubmodule (invSubalgebra K)).projection C hC x
      ∈ invSubalgebra K := fun x => Submodule.projection_apply_mem hC x
  have hq_fix : ∀ x ∈ invSubalgebra K,
      (Subalgebra.toSubmodule (invSubalgebra K)).projection C hC x = x := fun x hx =>
    (Submodule.projection_eq_self_iff hC x).mpr hx

  have h1 : ((Subalgebra.toSubmodule (invSubalgebra K)).projection C hC).lTensor G
      (Coalgebra.comul (R := R) g) = Coalgebra.comul (R := R) g := by
    conv_lhs => rw [eq_sum_tmul_coord b (Coalgebra.comul (R := R) g), map_sum]
    conv_rhs => rw [eq_sum_tmul_coord b (Coalgebra.comul (R := R) g)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.lTensor_tmul, hq_fix _ (hv j)]

  have h2 : ((Subalgebra.toSubmodule (invSubalgebra K)).projection C hC).lTensor G
      (Coalgebra.comul (R := R) g)
      = ∑ j, (TensorProduct.rid R G ((b.coord j).lTensor G (Coalgebra.comul (R := R) g)))
          ⊗ₜ[R] (Subalgebra.toSubmodule (invSubalgebra K)).projection C hC (b j) := by
    conv_lhs => rw [eq_sum_coord_tmul b (Coalgebra.comul (R := R) g), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.lTensor_tmul]
  rw [← h1, h2]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.subset_span (Set.mem_image2_of_mem (hu j) (hq_mem _))

theorem isComulStable_genB [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R F]
    [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (hRL : Function.Injective (algebraMap R L)) (K : Set (G →ₐ[R] L)) :
    IsComulStable R F (genB F K) := by
  intro g hg
  rw [flatClosure_genB hRL K] at hg
  have hmem := comul_mem_span_of_mem_invSubalgebra hRL hg
  revert hmem
  generalize Coalgebra.comul (R := R) g = z
  intro hmem
  induction hmem using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, ha, c, hc, rfl⟩ := hw
      rw [tensorToGenericFibre_tmul]
      exact Submodule.subset_span
        (Set.mem_image2_of_mem (one_tmul_mem_genB ha) (one_tmul_mem_genB hc))
  | zero =>
      rw [tensorToGenericFibre_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [tensorToGenericFibre_add]
      exact add_mem hx hy
  | smul r x _ hx =>
      rw [tensorToGenericFibre_smul]
      exact Submodule.smul_mem _ _ hx

end ComulStable
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section Antipode

variable {L : Type x} [CommRing L] [Algebra R L]
variable [HopfAlgebra R G]

theorem antipode_mem_invSubalgebra
    (hSΔ : ∀ a : G, TensorProduct.map (HopfAlgebra.antipode R (A := G))
      (HopfAlgebra.antipode R (A := G)) (Coalgebra.comul (R := R) a)
        = Coalgebra.comul (R := R) (HopfAlgebra.antipode R (A := G) a))
    {K : Set (G →ₐ[R] L)}
    (hKS : ∀ k ∈ K, ∃ k' ∈ K,
      k'.toLinearMap = k.toLinearMap ∘ₗ HopfAlgebra.antipode R (A := G))
    {g : G} (hg : g ∈ invSubalgebra K) :
    HopfAlgebra.antipode R (A := G) g ∈ invSubalgebra K := by
  rw [mem_invSubalgebra_iff] at hg ⊢
  intro k hk
  obtain ⟨k', hk', hk'S⟩ := hKS k hk
  have hfac : TensorProduct.map k'.toLinearMap (HopfAlgebra.antipode R (A := G))
      = (HopfAlgebra.antipode R (A := G)).lTensor L ∘ₗ
          TensorProduct.map k'.toLinearMap LinearMap.id := by
    rw [LinearMap.lTensor_def, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]
  rw [lTrans_toLinearMap_apply, ← hSΔ g, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← hk'S, LinearMap.id_comp, hfac, LinearMap.comp_apply, ← lTrans_toLinearMap_apply,
    hg k' hk', LinearMap.lTensor_tmul]

end Antipode
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section AntipodeGenB

variable {L : Type x} [Field L] [Algebra R L]
variable [HopfAlgebra R G]

theorem isAntipodeStable_genB [IsDomain R] [IsFractionRing R F] [Module.Flat R G]
    (hRL : Function.Injective (algebraMap R L))
    (hSΔ : ∀ a : G, TensorProduct.map (HopfAlgebra.antipode R (A := G))
      (HopfAlgebra.antipode R (A := G)) (Coalgebra.comul (R := R) a)
        = Coalgebra.comul (R := R) (HopfAlgebra.antipode R (A := G) a))
    {K : Set (G →ₐ[R] L)}
    (hKS : ∀ k ∈ K, ∃ k' ∈ K,
      k'.toLinearMap = k.toLinearMap ∘ₗ HopfAlgebra.antipode R (A := G)) :
    IsAntipodeStable R F (genB F K) := by
  intro g hg
  rw [flatClosure_genB hRL K] at hg ⊢
  exact antipode_mem_invSubalgebra hSΔ hKS hg

end AntipodeGenB
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section Averaging

variable {L : Type x} [CommRing L] [Algebra R L]
variable [Bialgebra R G]

open WithConv

noncomputable def mulφ (φ : G →ₐ[R] L) : L ⊗[R] G →ₐ[R] L :=
  Algebra.TensorProduct.lift (AlgHom.id R L) φ (fun _ _ => Commute.all _ _)

@[scoped simp]
lemma mulφ_tmul (φ : G →ₐ[R] L) (c : L) (y : G) : mulφ φ (c ⊗ₜ[R] y) = c * φ y := by
  simp [mulφ, Algebra.TensorProduct.lift_tmul]

theorem convMul_apply_eq (k φ : G →ₐ[R] L) (g : G) :
    (toConv k * toConv φ) g = mulφ φ (lTrans k g) := by
  rw [AlgHom.convMul_apply, lTrans_eq_sum k (Coalgebra.Repr.arbitrary R g),
    ← (Coalgebra.Repr.arbitrary R g).eq, map_sum, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, mulφ_tmul]

theorem convMul_apply_of_mem {K : Set (G →ₐ[R] L)} {g : G} (hg : g ∈ invSubalgebra K)
    {k : G →ₐ[R] L} (hk : k ∈ K) (φ : G →ₐ[R] L) :
    (toConv k * toConv φ) g = φ g := by
  rw [convMul_apply_eq, lTrans_eq_of_mem hg hk, mulφ_tmul, one_mul]

noncomputable def transL (k' : G →ₐ[R] L) : L ⊗[R] G →ₐ[R] L ⊗[R] G :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := R)) (lTrans k')
    (fun _ _ => Commute.all _ _)

omit [Bialgebra R G] in
lemma tmul_one_mul [Algebra R G] (c : L) (x : L ⊗[R] G) : (c ⊗ₜ[R] (1 : G)) * x = c • x := by
  induction x with
  | zero => rw [mul_zero, smul_zero]
  | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [mul_add, hx, hy, smul_add]

lemma transL_tmul (k' : G →ₐ[R] L) (c : L) (y : G) :
    transL k' (c ⊗ₜ[R] y) = c • lTrans k' y := by
  rw [transL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
    tmul_one_mul]

theorem transL_lTrans (k k' : G →ₐ[R] L) (g : G) :
    transL k' (lTrans k g) = lTrans (toConv k * toConv k').ofConv g := by
  let 𝓡 := Coalgebra.Repr.arbitrary R g
  let 𝓛 := fun i => Coalgebra.Repr.arbitrary R (𝓡.left i)
  let 𝓜 := fun i => Coalgebra.Repr.arbitrary R (𝓡.right i)

  let θ : G ⊗[R] (G ⊗[R] G) →ₗ[R] L ⊗[R] G :=
    (LinearMap.mul' R L).rTensor G ∘ₗ (TensorProduct.assoc R L L G).symm.toLinearMap ∘ₗ
      TensorProduct.map k.toLinearMap (TensorProduct.map k'.toLinearMap LinearMap.id)
  have hθ : ∀ x y z : G, θ (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = (k x * k' y) ⊗ₜ[R] z := fun x y z => by
    simp only [θ, LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      LinearMap.id_coe, id_eq, LinearEquiv.coe_toLinearMap, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, LinearMap.mul'_apply]
  have h1 := DFunLike.congr_arg θ (Coalgebra.sum_tmul_tmul_eq 𝓡 𝓛 𝓜)
  simp only [map_sum, hθ] at h1

  have hL : transL k' (lTrans k g)
      = ∑ i ∈ 𝓡.index, ∑ j ∈ (𝓜 i).index,
          (k (𝓡.left i) * k' ((𝓜 i).left j)) ⊗ₜ[R] (𝓜 i).right j := by
    rw [lTrans_eq_sum k 𝓡, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [transL_tmul, lTrans_eq_sum k' (𝓜 i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  have hR : lTrans (toConv k * toConv k').ofConv g
      = ∑ i ∈ 𝓡.index, ∑ j ∈ (𝓛 i).index,
          (k ((𝓛 i).left j) * k' ((𝓛 i).right j)) ⊗ₜ[R] 𝓡.right i := by
    rw [lTrans_eq_sum _ 𝓡]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (toConv k * toConv k').ofConv (𝓡.left i)
        = ∑ j ∈ (𝓛 i).index, k ((𝓛 i).left j) * k' ((𝓛 i).right j) := by
      change (toConv k * toConv k') (𝓡.left i) = _
      rw [AlgHom.convMul_apply, ← (𝓛 i).eq, map_sum]
      simp only [Algebra.TensorProduct.lift_tmul]
    rw [hc, TensorProduct.sum_tmul]
  rw [hL, hR, h1]

noncomputable def avg (Kf : Finset (G →ₐ[R] L)) (g : G) : L ⊗[R] G :=
  ∑ k ∈ Kf, lTrans k g

lemma avg_def (Kf : Finset (G →ₐ[R] L)) (g : G) : avg Kf g = ∑ k ∈ Kf, lTrans k g := rfl

lemma sum_comp_eq_of_injOn {α M : Type*} [DecidableEq α] [AddCommMonoid M] (s : Finset α)
    (e : α → α) (he : ∀ a ∈ s, e a ∈ s) (hinj : Set.InjOn e s) (f : α → M) :
    ∑ a ∈ s, f (e a) = ∑ a ∈ s, f a := by
  have himg : s.image e = s := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact he a ha
    · rw [Finset.card_image_of_injOn hinj]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]

theorem transL_avg (k' : G →ₐ[R] L) {Kf : Finset (G →ₐ[R] L)}
    (hK : ∀ k ∈ Kf, (toConv k * toConv k').ofConv ∈ Kf)
    (hinj : Set.InjOn (fun k : G →ₐ[R] L => (toConv k * toConv k').ofConv) Kf) (g : G) :
    transL k' (avg Kf g) = avg Kf g := by
  classical
  rw [avg_def, map_sum]
  simp only [transL_lTrans]
  exact sum_comp_eq_of_injOn Kf (fun k => (toConv k * toConv k').ofConv) hK hinj
    (fun k => lTrans k g)

theorem mem_invSubalgebra_of_smul_avg_eq {Kf : Finset (G →ₐ[R] L)}
    (hK : ∀ k' ∈ Kf, ∀ k ∈ Kf, (toConv k * toConv k').ofConv ∈ Kf)
    (hinj : ∀ k' ∈ Kf, Set.InjOn (fun k : G →ₐ[R] L => (toConv k * toConv k').ofConv) Kf)
    {g g' : G} {r : R} (h : r • avg Kf g = (1 : L) ⊗ₜ[R] g') :
    g' ∈ invSubalgebra (Kf : Set (G →ₐ[R] L)) := by
  rw [mem_invSubalgebra_iff]
  intro k' hk'
  have hk'f : k' ∈ Kf := hk'
  have h1 : transL k' ((1 : L) ⊗ₜ[R] g') = lTrans k' g' := by rw [transL_tmul, one_smul]
  rw [← h1, ← h, map_smul, transL_avg k' (hK k' hk'f) (hinj k' hk'f)]

theorem apply_of_smul_avg_eq (φ : G →ₐ[R] L) {Kf : Finset (G →ₐ[R] L)} {g g' : G} {r : R}
    (h : r • avg Kf g = (1 : L) ⊗ₜ[R] g') :
    φ g' = r • ∑ k ∈ Kf, (toConv k * toConv φ) g := by
  have h1 : mulφ φ ((1 : L) ⊗ₜ[R] g') = φ g' := by rw [mulφ_tmul, one_mul]
  rw [← h1, ← h, map_smul, avg_def, map_sum]
  simp only [convMul_apply_eq]

end Averaging
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

namespace DESCKDN

section Extension

variable {R A B L : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Field L] [IsAlgClosed L] [Algebra R L]

theorem exists_algHom_extension [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A B)) (φ' : A →ₐ[R] L) :
    ∃ φ : B →ₐ[R] L, ∀ a : A, φ (algebraMap A B a) = φ' a := by
  classical
  haveI hPprime : (RingHom.ker φ').IsPrime := RingHom.ker_isPrime _
  have hbot : (⊥ : Ideal B).comap (algebraMap A B) ≤ RingHom.ker φ' := by
    intro a ha
    have h0 : algebraMap A B a = 0 := by
      simpa [Ideal.mem_comap] using ha
    have ha0 : a = 0 := by
      apply hinj
      rw [h0, map_zero]
    rw [RingHom.mem_ker, ha0, map_zero]
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ') ⊥ hbot
  haveI := hQprime
  set P : Ideal A := RingHom.ker φ' with hP
  have hPle : P ≤ Q.comap (algebraMap A B) := le_of_eq hQcomap.symm
  letI : Algebra (A ⧸ P) (B ⧸ Q) := (Ideal.quotientMap Q (algebraMap A B) hPle).toAlgebra
  have hqinj : Function.Injective (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    show Function.Injective (Ideal.quotientMap Q (algebraMap A B) hPle)
    exact Ideal.quotientMap_injective' (le_of_eq hQcomap)
  haveI : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := by
    constructor
    intro bq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
    obtain ⟨p, hmonic, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    refine ⟨p.map (Ideal.Quotient.mk P), hmonic.map _, ?_⟩
    show Polynomial.eval₂ (algebraMap (A ⧸ P) (B ⧸ Q)) (Ideal.Quotient.mk Q b) (p.map (Ideal.Quotient.mk P)) = 0
    rw [Polynomial.eval₂_map]
    have h4 : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (Ideal.Quotient.mk P)
        = (Ideal.Quotient.mk Q).comp (algebraMap A B) :=
      Ideal.quotientMap_comp_mk hPle
    rw [h4, ← Polynomial.hom_eval₂, hp, map_zero]
  have hvanish : ∀ a ∈ P, (φ' : A →+* L) a = 0 := by
    intro a ha
    rwa [RingHom.mem_ker] at ha
  let φb : (A ⧸ P) →+* L := Ideal.Quotient.lift P (φ' : A →+* L) hvanish
  have hφb_inj : Function.Injective φb := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at hxy
    have hxy' : φ' a = φ' b := hxy
    rw [Ideal.Quotient.eq]
    rw [show P = RingHom.ker φ' from rfl, RingHom.mem_ker, map_sub, hxy', sub_self]
  letI : Algebra (A ⧸ P) L := φb.toAlgebra
  haveI : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  have hreg_ne : ∀ r : A ⧸ P, IsRegular r → r ≠ 0 := by
    intro r hr hr0
    have h01 : r * 1 = r * 0 := by rw [hr0, mul_zero, mul_one]
    exact one_ne_zero (hr.left h01)
  haveI : Module.IsTorsionFree (A ⧸ P) (B ⧸ Q) := by
    constructor
    intro r hr x y hxy
    have hrx : algebraMap (A ⧸ P) (B ⧸ Q) r * x = algebraMap (A ⧸ P) (B ⧸ Q) r * y := by
      rw [← Algebra.smul_def, ← Algebra.smul_def]
      exact hxy
    have hrne : algebraMap (A ⧸ P) (B ⧸ Q) r ≠ 0 := by
      intro h0
      exact hreg_ne r hr (hqinj (by rw [h0, map_zero]))
    exact mul_left_cancel₀ hrne hrx
  haveI : Module.IsTorsionFree (A ⧸ P) L := by
    constructor
    intro r hr x y hxy
    have hrx : algebraMap (A ⧸ P) L r * x = algebraMap (A ⧸ P) L r * y := by
      rw [← Algebra.smul_def, ← Algebra.smul_def]
      exact hxy
    have hrne : algebraMap (A ⧸ P) L r ≠ 0 := by
      intro h0
      refine hreg_ne r hr (hφb_inj ?_)
      show φb r = φb 0
      rw [map_zero]
      exact h0
    exact mul_left_cancel₀ hrne hrx
  haveI : Algebra.IsAlgebraic (A ⧸ P) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let τ : (B ⧸ Q) →ₐ[A ⧸ P] L := IsAlgClosed.lift
  refine ⟨AlgHom.mk ((τ : (B ⧸ Q) →+* L).comp (Ideal.Quotient.mk Q)) ?_, ?_⟩
  · intro r
    show τ ((Ideal.Quotient.mk Q) (algebraMap R B r)) = algebraMap R L r
    have h1 : algebraMap R B r = algebraMap A B (algebraMap R A r) :=
      IsScalarTower.algebraMap_apply R A B r
    have h2 : (Ideal.Quotient.mk Q) (algebraMap A B (algebraMap R A r))
        = algebraMap (A ⧸ P) (B ⧸ Q) (Ideal.Quotient.mk P (algebraMap R A r)) := by
      have h3 := congrArg (fun f => f (algebraMap R A r)) (Ideal.quotientMap_comp_mk hPle)
      exact h3.symm
    rw [h1, h2, AlgHom.commutes]
    show φb (Ideal.Quotient.mk P (algebraMap R A r)) = algebraMap R L r
    rw [Ideal.Quotient.lift_mk]
    exact φ'.commutes r
  · intro a
    show τ ((Ideal.Quotient.mk Q) (algebraMap A B a)) = φ' a
    have h1 : (Ideal.Quotient.mk Q) (algebraMap A B a)
        = algebraMap (A ⧸ P) (B ⧸ Q) (Ideal.Quotient.mk P a) := by
      have h3 := congrArg (fun f => f a) (Ideal.quotientMap_comp_mk hPle)
      exact h3.symm
    rw [h1, AlgHom.commutes]
    show φb (Ideal.Quotient.mk P a) = φ' a
    rw [Ideal.Quotient.lift_mk]
    rfl

end Extension
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

namespace DESCKDN

section Dedekind

variable {R G L : Type} [CommSemiring R] [CommSemiring G] [Algebra R G]
  [CommRing L] [IsDomain L] [Algebra R L]

theorem finset_eq_of_sum_apply_eq (S T : Finset (G →ₐ[R] L))
    (h : ∀ g : G, ∑ χ ∈ S, χ g = ∑ χ ∈ T, χ g) : S = T := by
  classical
  set J : (G →ₐ[R] L) → (G →* L) := fun χ => (χ : G →* L) with hJdef
  have hJ : Function.Injective J := by
    intro χ ψ hχψ
    apply DFunLike.ext
    intro g
    exact DFunLike.congr_fun hχψ g
  have li : LinearIndependent L (fun f : G →* L => (f : G → L)) :=
    linearIndependent_monoidHom G L
  set c : (G →* L) →₀ L :=
    (∑ χ ∈ S, Finsupp.single (J χ) (1 : L)) - ∑ χ ∈ T, Finsupp.single (J χ) (1 : L) with hc
  have hc0 : Finsupp.linearCombination L (fun f : G →* L => (f : G → L)) c = 0 := by
    rw [hc, map_sub, map_sum, map_sum]
    simp only [Finsupp.linearCombination_single, one_smul]
    funext g
    simp only [Pi.sub_apply, Pi.zero_apply, Finset.sum_apply]
    have hg := h g
    simp only [hJdef]
    simp only [MonoidHom.coe_coe]
    rw [hg]
    ring
  have hczero : c = 0 := linearIndependent_iff.mp li c hc0
  apply Finset.ext
  intro χ₀
  have happ := congrArg (fun f => f (J χ₀)) hczero
  simp only [hc, Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply,
    Finsupp.finsetSum_apply] at happ
  have hSsum : (∑ χ ∈ S, (Finsupp.single (J χ) (1 : L)) (J χ₀))
      = if χ₀ ∈ S then (1 : L) else 0 := by
    by_cases hmem : χ₀ ∈ S
    · rw [if_pos hmem]
      rw [Finset.sum_eq_single χ₀]
      · simp
      · intro χ hχ hne
        rw [Finsupp.single_apply, if_neg]
        intro hJeq
        exact hne (hJ hJeq)
      · intro habs
        exact absurd hmem habs
    · rw [if_neg hmem]
      apply Finset.sum_eq_zero
      intro χ hχ
      rw [Finsupp.single_apply, if_neg]
      intro hJeq
      exact hmem (hJ hJeq ▸ hχ)
  have hTsum : (∑ χ ∈ T, (Finsupp.single (J χ) (1 : L)) (J χ₀))
      = if χ₀ ∈ T then (1 : L) else 0 := by
    by_cases hmem : χ₀ ∈ T
    · rw [if_pos hmem]
      rw [Finset.sum_eq_single χ₀]
      · simp
      · intro χ hχ hne
        rw [Finsupp.single_apply, if_neg]
        intro hJeq
        exact hne (hJ hJeq)
      · intro habs
        exact absurd hmem habs
    · rw [if_neg hmem]
      apply Finset.sum_eq_zero
      intro χ hχ
      rw [Finsupp.single_apply, if_neg]
      intro hJeq
      exact hmem (hJ hJeq ▸ hχ)
  rw [hSsum, hTsum] at happ
  by_cases hS : χ₀ ∈ S <;> by_cases hT : χ₀ ∈ T
  · exact iff_of_true hS hT
  · exfalso
    rw [if_pos hS, if_neg hT, sub_zero] at happ
    exact one_ne_zero happ
  · exfalso
    rw [if_neg hS, if_pos hT, zero_sub, neg_eq_zero] at happ
    exact one_ne_zero happ
  · exact iff_of_false hS hT

end Dedekind
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

open scoped TensorProduct

namespace DESCKDN

section AntipodeAlgHom

variable (R A : Type) [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]

noncomputable def antipodeAlgHom : A →ₐ[R] A where
  toFun := HopfAlgebra.antipode R
  map_one' := HopfAlgebra.antipode_one
  map_mul' a b := by rw [HopfAlgebra.antipode_mul, mul_comm]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one]

@[scoped simp]
lemma antipodeAlgHom_apply (a : A) :
    antipodeAlgHom R A a = HopfAlgebra.antipode R a := rfl

end AntipodeAlgHom
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

section ConvInverse

variable {R A L : Type} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing L] [Algebra R L]

private lemma lmul_map_eq (φ : A →ₐ[R] L) (z : A ⊗[R] A) :
    Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map φ (φ.comp (antipodeAlgHom R A)) z)
    = φ (LinearMap.mul' R A (LinearMap.lTensor A (HopfAlgebra.antipode R) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        LinearMap.lTensor_tmul, LinearMap.mul'_apply, map_mul, AlgHom.comp_apply,
        antipodeAlgHom_apply]
  | add y z ihy ihz =>
      simp only [map_add, ihy, ihz]

theorem toConv_mul_toConv_comp_antipodeAlgHom (φ : A →ₐ[R] L) :
    WithConv.toConv φ * WithConv.toConv (φ.comp (antipodeAlgHom R A)) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  show Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map φ (φ.comp (antipodeAlgHom R A))
        (Bialgebra.comulAlgHom R A x))
    = algebraMap R L (Coalgebra.counit x)
  rw [Bialgebra.comulAlgHom_apply, lmul_map_eq φ (Coalgebra.comul x)]
  rw [HopfAlgebra.mul_antipode_lTensor_comul_apply]
  exact φ.commutes _

end ConvInverse
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

namespace DESCKDN

section AGlue

open WithConv

variable {R : Type} [CommRing R]
variable {L : Type} [Field L] [Algebra R L]

lemma map_val_val_eq_tensorInclusion {F : Type} [Field F] [Algebra R F]
    {G : Type} [CommRing G] [Algebra R G]
    (B : Subalgebra F (F ⊗[R] G)) (x : (flatClosure B) ⊗[R] (flatClosure B)) :
    Algebra.TensorProduct.map (flatClosure B).val (flatClosure B).val x = tensorInclusion B x := by
  induction x with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

lemma conv_right_cancel {G : Type} [CommRing G] [HopfAlgebra R G] (a b x : G →ₐ[R] L)
    (h : toConv a * toConv x = toConv b * toConv x) : a = b := by
  have hx := toConv_mul_toConv_comp_antipodeAlgHom (R := R) (A := G) (L := L) x
  have h2 := congrArg (· * toConv (x.comp (antipodeAlgHom R G))) h
  simp only [mul_assoc, hx, mul_one] at h2
  exact WithConv.toConv_injective h2

theorem aMain [IsDomain R] [IsPrincipalIdealRing R] [IsAlgClosed L]
    (hRL : Function.Injective (algebraMap R L))
    (G : Type) [CommRing G] [HopfAlgebra R G]
    [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (K : Finset (G →ₐ[R] L))
    (hKone : (Algebra.ofId R L).comp (Bialgebra.counitAlgHom R G) ∈ K)
    (hKmul : ∀ k ∈ K, ∀ k' ∈ K,
      WithConv.ofConv (WithConv.toConv k * WithConv.toConv k') ∈ K)
    (hKS : ∀ k ∈ K, ∃ k' ∈ K,
      k'.toLinearMap = k.toLinearMap ∘ₗ HopfAlgebra.antipode R)
    (hdesc : ∀ g : G, ∃ (r : R) (g' : G), r ≠ 0 ∧
      r • (∑ k ∈ K, (Algebra.TensorProduct.map k (AlgHom.id R G)).comp
        (Bialgebra.comulAlgHom R G) g) = (1 : L) ⊗ₜ[R] g') :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ ι : H' →ₐc[R] G,
        Function.Surjective (fun φ : G →ₐ[R] L => φ.comp (ι : H' →ₐ[R] G)) ∧
        ∀ φ ψ : G →ₐ[R] L, φ.comp (ι : H' →ₐ[R] G) = ψ.comp (ι : H' →ₐ[R] G) ↔
          ∃ k ∈ K, ψ = WithConv.ofConv (WithConv.toConv k * WithConv.toConv φ) := by
  classical

  let B : Subalgebra (FractionRing R) (FractionRing R ⊗[R] G) :=
    genB (FractionRing R) (K : Set (G →ₐ[R] L))
  have hHB : flatClosure B = invSubalgebra (K : Set (G →ₐ[R] L)) := flatClosure_genB hRL _
  have hB : IsComulStable R (FractionRing R) B := isComulStable_genB hRL _
  have hSΔ := HopfAlgebra.map_antipode_comul_of_isCocomm (R := R) (A := G) inferInstance
  have hB' : IsAntipodeStable R (FractionRing R) B :=
    isAntipodeStable_genB hRL hSΔ (fun k hk => hKS k hk)
  letI hH : HopfAlgebra R (flatClosure B) := closureHopfAlgebra R (FractionRing R) hB hB'
  haveI hcc : Coalgebra.IsCocomm R (flatClosure B) :=
    ⟨LinearMap.ext fun h => comm_closureComul hB h⟩

  let ι : flatClosure B →ₐc[R] G :=
    BialgHom.ofAlgHom (flatClosure B).val (AlgHom.ext fun _ => rfl) (by
      apply AlgHom.ext
      intro h
      change Algebra.TensorProduct.map (flatClosure B).val (flatClosure B).val (closureComul hB h)
        = Coalgebra.comul (R := R) (h : G)
      rw [map_val_val_eq_tensorInclusion, tensorInclusion_closureComul])
  have hι : ∀ h : flatClosure B, (ι : flatClosure B →ₐ[R] G) h = (h : G) := fun _ => rfl
  refine ⟨flatClosure B, inferInstance, hH, flatClosure_finite B, flatClosure_flat B, hcc, ι,
    ?_, ?_⟩
  ·
    intro χ
    haveI : Module.Finite (flatClosure B) G := Module.Finite.of_restrictScalars_finite R _ _
    obtain ⟨φ, hφ⟩ := exists_algHom_extension (R := R) (A := flatClosure B) (B := G) (L := L)
      Subtype.val_injective χ
    exact ⟨φ, AlgHom.ext fun h => hφ h⟩
  · intro φ ψ
    constructor
    · intro hres

      have hsum : ∀ g : G,
          ∑ k ∈ K, (toConv k * toConv φ) g = ∑ k ∈ K, (toConv k * toConv ψ) g := by
        intro g
        obtain ⟨r, g', hr, hrg⟩ := hdesc g
        change r • avg K g = (1 : L) ⊗ₜ[R] g' at hrg
        have hg' : g' ∈ invSubalgebra (K : Set (G →ₐ[R] L)) :=
          mem_invSubalgebra_of_smul_avg_eq (fun k' hk' k hk => hKmul k hk k' hk')
            (fun k' _ a _ b _ hab => conv_right_cancel a b k'
              (by simpa using congrArg toConv hab)) hrg
        have hmem : g' ∈ flatClosure B := by rw [hHB]; exact hg'
        have hφψ : φ g' = ψ g' := DFunLike.congr_fun hres ⟨g', hmem⟩
        have e1 := apply_of_smul_avg_eq φ hrg
        have e2 := apply_of_smul_avg_eq ψ hrg
        rw [hφψ] at e1
        have h12 := e1.symm.trans e2
        rw [Algebra.smul_def, Algebra.smul_def] at h12
        exact mul_left_cancel₀ (fun h0 => hr (hRL (by rw [h0, map_zero]))) h12

      have hinj : ∀ χ : G →ₐ[R] L,
          Set.InjOn (fun k : G →ₐ[R] L => (toConv k * toConv χ).ofConv) K :=
        fun χ a _ b _ hab => conv_right_cancel a b χ (by simpa using congrArg toConv hab)
      have himg : K.image (fun k : G →ₐ[R] L => (toConv k * toConv φ).ofConv)
          = K.image (fun k : G →ₐ[R] L => (toConv k * toConv ψ).ofConv) := by
        apply finset_eq_of_sum_apply_eq
        intro g
        rw [Finset.sum_image (hinj φ), Finset.sum_image (hinj ψ)]
        exact hsum g
      have hψ : ψ ∈ K.image (fun k : G →ₐ[R] L => (toConv k * toConv ψ).ofConv) := by
        refine Finset.mem_image.mpr ⟨_, hKone, ?_⟩
        change (toConv ((Algebra.ofId R L).comp (Bialgebra.counitAlgHom R G)) * toConv ψ).ofConv
          = ψ
        rw [← AlgHom.convOne_def, one_mul]
      rw [← himg] at hψ
      obtain ⟨k, hk, hkψ⟩ := Finset.mem_image.mp hψ
      exact ⟨k, hk, hkψ.symm⟩
    · rintro ⟨k, hk, rfl⟩
      apply AlgHom.ext
      intro h
      have hmem : (h : G) ∈ invSubalgebra (K : Set (G →ₐ[R] L)) := by rw [← hHB]; exact h.2
      exact (convMul_apply_of_mem hmem hk φ).symm

end AGlue
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.DESCKDN"

theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {L : Type} [Field L] [Algebra R L] [IsAlgClosed L]
    (hRL : Function.Injective (algebraMap R L))
    (G : Type) [CommRing G] [HopfAlgebra R G]
    [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (K : Finset (G →ₐ[R] L))
    (hKone : (Algebra.ofId R L).comp (Bialgebra.counitAlgHom R G) ∈ K)
    (hKmul : ∀ k ∈ K, ∀ k' ∈ K,
      WithConv.ofConv (WithConv.toConv k * WithConv.toConv k') ∈ K)
    (hKS : ∀ k ∈ K, ∃ k' ∈ K,
      k'.toLinearMap = k.toLinearMap ∘ₗ HopfAlgebra.antipode R)
    (hdesc : ∀ g : G, ∃ (r : R) (g' : G), r ≠ 0 ∧
      r • (∑ k ∈ K, (Algebra.TensorProduct.map k (AlgHom.id R G)).comp
        (Bialgebra.comulAlgHom R G) g) = (1 : L) ⊗ₜ[R] g') :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ ι : H' →ₐc[R] G,
        Function.Surjective (fun φ : G →ₐ[R] L => φ.comp (ι : H' →ₐ[R] G)) ∧
        ∀ φ ψ : G →ₐ[R] L, φ.comp (ι : H' →ₐ[R] G) = ψ.comp (ι : H' →ₐ[R] G) ↔
          ∃ k ∈ K, ψ = WithConv.ofConv (WithConv.toConv k * WithConv.toConv φ) :=
  DESCKDN.aMain hRL G K hKone hKmul hKS hdesc

end S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent (solution)
