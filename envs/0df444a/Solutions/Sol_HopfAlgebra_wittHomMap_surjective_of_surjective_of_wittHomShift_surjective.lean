-- Prove2me | solution 1 for HopfAlgebra.wittHomMap_surjective_of_surjective_of_wittHomShift_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d241cbae-e218-50bc-86b4-2040546f5897

import Definitions.Def_Dieudonne_WittVectorHom
import Theorems.Thm_HopfAlgebra_wittHom_coeff_mem_map_adjoin_of_surjective_of_wittHomShift_surjective
import Theorems.Thm_HopfAlgebra_convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom
import Theorems.Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_wittHomShift_surjective
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl"

set_option autoImplicit false

universe u v w

namespace WittImageGlue

open scoped TensorProduct

section SubBialgebra

variable {k : Type u} [Field k] {C : Type v} [CommRing C] [Bialgebra k C] (S : Subalgebra k C)

private noncomputable def valL : ↥S →ₗ[k] C := S.val.toLinearMap

@[scoped simp] private theorem valL_apply (s : ↥S) : valL S s = (s : C) := rfl

private noncomputable def ι₂A : ↥S ⊗[k] ↥S →ₐ[k] C ⊗[k] C := Algebra.TensorProduct.map S.val S.val

private noncomputable def ι₂ : ↥S ⊗[k] ↥S →ₗ[k] C ⊗[k] C := (ι₂A S).toLinearMap

private theorem ι₂_eq_map : ι₂ S = TensorProduct.map (valL S) (valL S) :=
  TensorProduct.ext' fun _ _ => rfl

@[scoped simp] private theorem ι₂_tmul (s t : ↥S) : ι₂ S (s ⊗ₜ[k] t) = (s : C) ⊗ₜ[k] (t : C) := rfl

private theorem ι₂_mul (x y : ↥S ⊗[k] ↥S) : ι₂ S (x * y) = ι₂ S x * ι₂ S y := map_mul (ι₂A S) x y

private theorem ι₂_one : ι₂ S 1 = 1 := map_one (ι₂A S)

private theorem ι₂_injective : Function.Injective (ι₂ S) := by
  have h1 : Function.Injective ((valL S).lTensor ↥S) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have h2 : Function.Injective ((valL S).rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [ι₂_eq_map, ← LinearMap.rTensor_comp_lTensor]
  exact h2.comp h1

private noncomputable def ι₃ : ↥S ⊗[k] (↥S ⊗[k] ↥S) →ₗ[k] C ⊗[k] (C ⊗[k] C) :=
  TensorProduct.map (valL S) (ι₂ S)

@[scoped simp] private theorem ι₃_tmul (s : ↥S) (z : ↥S ⊗[k] ↥S) :
    ι₃ S (s ⊗ₜ[k] z) = (s : C) ⊗ₜ[k] ι₂ S z := rfl

private theorem ι₃_injective : Function.Injective (ι₃ S) := by
  have h1 : Function.Injective ((ι₂ S).lTensor ↥S) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (ι₂_injective S)
  have h2 : Function.Injective ((valL S).rTensor (C ⊗[k] C)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [ι₃, ← LinearMap.rTensor_comp_lTensor]
  exact h2.comp h1

private noncomputable def counitS : ↥S →ₗ[k] k := Coalgebra.counit ∘ₗ valL S

@[scoped simp] private theorem counitS_apply (s : ↥S) : counitS S s = Coalgebra.counit (R := k) (s : C) := rfl

private theorem rTensor_counitS (z : ↥S ⊗[k] ↥S) :
    (valL S).lTensor k ((counitS S).rTensor ↥S z)
      = (Coalgebra.counit (R := k) (A := C)).rTensor C (ι₂ S z) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

private theorem lTensor_counitS (z : ↥S ⊗[k] ↥S) :
    (valL S).rTensor k ((counitS S).lTensor ↥S z)
      = (Coalgebra.counit (R := k) (A := C)).lTensor C (ι₂ S z) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

private def ComulStable : Prop :=
  ∀ s : ↥S, Coalgebra.comul (R := k) (s : C) ∈ LinearMap.range (ι₂ S)

private noncomputable def comulS (hS : ComulStable S) : ↥S →ₗ[k] ↥S ⊗[k] ↥S :=
  (LinearEquiv.ofInjective (ι₂ S) (ι₂_injective S)).symm.toLinearMap
    ∘ₗ ((Coalgebra.comul (R := k) (A := C)) ∘ₗ valL S).codRestrict (LinearMap.range (ι₂ S)) hS

@[scoped simp] private theorem ι₂_comulS (hS : ComulStable S) (s : ↥S) :
    ι₂ S (comulS S hS s) = Coalgebra.comul (R := k) (s : C) := by
  simp only [comulS, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply,
    LinearMap.codRestrict_apply, valL_apply]

private theorem ι₃_lTensor_comulS (hS : ComulStable S) (z : ↥S ⊗[k] ↥S) :
    ι₃ S ((comulS S hS).lTensor ↥S z) = (Coalgebra.comul (R := k) (A := C)).lTensor C (ι₂ S z) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

private theorem ι₃_assoc_rTensor_comulS (hS : ComulStable S) (z : ↥S ⊗[k] ↥S) :
    ι₃ S ((TensorProduct.assoc k _ _ _).toLinearMap ((comulS S hS).rTensor ↥S z))
      = (TensorProduct.assoc k C C C).toLinearMap
          ((Coalgebra.comul (R := k) (A := C)).rTensor C (ι₂ S z)) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [LinearMap.rTensor_tmul, ι₂_tmul]
      rw [← ι₂_comulS S hS x]
      induction comulS S hS x with
      | zero => simp only [TensorProduct.zero_tmul, LinearMap.map_zero]
      | add c d hc hd => simp only [TensorProduct.add_tmul, map_add, hc, hd]
      | tmul c d => simp [LinearEquiv.coe_coe]

@[reducible] private noncomputable def subCoalgebra (hS : ComulStable S) : Coalgebra k ↥S where
  comul := comulS S hS
  counit := counitS S
  coassoc := by
    ext s
    apply ι₃_injective S
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      ι₃_assoc_rTensor_comulS, ι₃_lTensor_comulS, ι₂_comulS]
    exact LinearMap.congr_fun (Coalgebra.coassoc (R := k) (A := C)) (s : C)
  rTensor_counit_comp_comul := by
    ext s
    have hinj : Function.Injective ((valL S).lTensor k) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul, valL_apply]
    rw [rTensor_counitS, ι₂_comulS, Coalgebra.rTensor_counit_comul]
  lTensor_counit_comp_comul := by
    ext s
    have hinj : Function.Injective ((valL S).rTensor k) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul, valL_apply]
    rw [lTensor_counitS, ι₂_comulS, Coalgebra.lTensor_counit_comul]

@[reducible] private noncomputable def subBialgebra (hS : ComulStable S) : Bialgebra k ↥S :=
  letI : Coalgebra k ↥S := subCoalgebra S hS
  have hcomul : ∀ s : ↥S, Coalgebra.comul (R := k) s = comulS S hS s := fun _ => rfl
  have hcounit : ∀ s : ↥S, Coalgebra.counit (R := k) s = Coalgebra.counit (R := k) (s : C) :=
    fun _ => rfl
  { counit_one := by rw [hcounit, Subalgebra.coe_one, Bialgebra.counit_one]
    mul_compr₂_counit := by
      ext a b
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply]
      rw [hcounit, hcounit, hcounit, Subalgebra.coe_mul, Bialgebra.counit_mul]
    comul_one := by
      apply ι₂_injective S
      rw [hcomul, ι₂_comulS, ι₂_one, Subalgebra.coe_one, Bialgebra.comul_one]
    mul_compr₂_comul := by
      ext a b
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        LinearMap.mul_apply']
      apply ι₂_injective S
      rw [hcomul, hcomul, hcomul, ι₂_mul, ι₂_comulS, ι₂_comulS, ι₂_comulS, Subalgebra.coe_mul,
        Bialgebra.comul_mul] }

end SubBialgebra

section Coord

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] {n : ℕ}
variable {A : Type v} [CommRing A] [HopfAlgebra k A]

private noncomputable def coordAlg (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] (n : ℕ)
    (A : Type v) [CommRing A] [HopfAlgebra k A] : Subalgebra k A :=
  Algebra.adjoin k {a : A | ∃ x : Deformation.wittHom k p n A, ∃ j : Fin n,
          (x : TruncatedWittVector p n A).coeff j = a}

private theorem coeff_add_mem {D : Type*} [CommRing D] [Algebra k D] (R' : Subalgebra k D)
    (u v : TruncatedWittVector p n D) (hu : ∀ i, u.coeff i ∈ R') (hv : ∀ i, v.coeff i ∈ R')
    (i : Fin n) : (u + v).coeff i ∈ R' := by
  let u' : TruncatedWittVector p n ↥R' := TruncatedWittVector.mk p fun j => ⟨u.coeff j, hu j⟩
  let v' : TruncatedWittVector p n ↥R' := TruncatedWittVector.mk p fun j => ⟨v.coeff j, hv j⟩
  have hu' : Deformation.TruncWitt.map (R'.val : ↥R' →ₐ[k] D).toRingHom u' = u :=
    TruncatedWittVector.ext fun j => by
      simp only [Deformation.TruncWitt.coeff_map, u', TruncatedWittVector.coeff_mk]; rfl
  have hv' : Deformation.TruncWitt.map (R'.val : ↥R' →ₐ[k] D).toRingHom v' = v :=
    TruncatedWittVector.ext fun j => by
      simp only [Deformation.TruncWitt.coeff_map, v', TruncatedWittVector.coeff_mk]; rfl
  rw [← hu', ← hv', ← map_add, Deformation.TruncWitt.coeff_map]
  exact SetLike.coe_mem _

private theorem coeff_mem_coordAlg (x : Deformation.wittHom k p n A) (j : Fin n) :
    (x : TruncatedWittVector p n A).coeff j ∈ coordAlg k p n A :=
  Algebra.subset_adjoin ⟨x, j, rfl⟩

private theorem comulStable_coordAlg : ComulStable (coordAlg k p n A) := by
  intro s
  have key : coordAlg k p n A ≤
      (ι₂A (coordAlg k p n A)).range.comap (Bialgebra.comulAlgHom k A) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨x, j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    have hx := (Deformation.mem_wittHom_iff (x : TruncatedWittVector p n A)).1 x.2
    have hcoe : Bialgebra.comulAlgHom k A ((x : TruncatedWittVector p n A).coeff j) =
        (Deformation.TruncWitt.map (Deformation.comulRingHom k A)
          (x : TruncatedWittVector p n A)).coeff j := by
      rw [Deformation.TruncWitt.coeff_map]; rfl
    rw [hcoe, hx]
    refine coeff_add_mem _ _ _ (fun i => ?_) (fun i => ?_) j
    · rw [Deformation.TruncWitt.coeff_map]
      refine ⟨(⟨_, coeff_mem_coordAlg x i⟩ : ↥(coordAlg k p n A)) ⊗ₜ[k] 1, ?_⟩
      simp [ι₂A, Algebra.TensorProduct.includeLeft_apply]
    · rw [Deformation.TruncWitt.coeff_map]
      refine ⟨(1 : ↥(coordAlg k p n A)) ⊗ₜ[k] ⟨_, coeff_mem_coordAlg x i⟩, ?_⟩
      simp [ι₂A, Algebra.TensorProduct.includeRight_apply]
  obtain ⟨z, hz⟩ := (AlgHom.mem_range _).1 ((Subalgebra.mem_comap _ _ _).1 (key s.2))
  exact LinearMap.mem_range.2 ⟨z, hz⟩

private noncomputable scoped instance instBialgebraCoordAlg : Bialgebra k ↥(coordAlg k p n A) :=
  subBialgebra _ comulStable_coordAlg

private theorem comul_coord (s : ↥(coordAlg k p n A)) :
    Coalgebra.comul (R := k) s = comulS (coordAlg k p n A) comulStable_coordAlg s := rfl

private theorem counit_coord (s : ↥(coordAlg k p n A)) :
    Coalgebra.counit (R := k) s = Coalgebra.counit (R := k) (s : A) := rfl

private theorem ι₂_comm (z : ↥(coordAlg k p n A) ⊗[k] ↥(coordAlg k p n A)) :
    ι₂ (coordAlg k p n A) (TensorProduct.comm k _ _ z) =
      TensorProduct.comm k A A (ι₂ (coordAlg k p n A) z) := by
  rw [ι₂_eq_map, TensorProduct.map_comm]

private scoped instance instIsCocommCoordAlg [Coalgebra.IsCocomm k A] :
    Coalgebra.IsCocomm k ↥(coordAlg k p n A) where
  comm_comp_comul := by
    ext s
    apply ι₂_injective (coordAlg k p n A)
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ι₂_comm, comul_coord, ι₂_comulS,
      Coalgebra.comm_comul]

private scoped instance instFiniteCoordAlg [Module.Finite k A] : Module.Finite k ↥(coordAlg k p n A) :=
  Module.Finite.of_injective (valL (coordAlg k p n A)) Subtype.val_injective

private noncomputable def antipodeAlgHom : A →ₐ[k] A :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode k) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] private theorem antipodeAlgHom_apply (a : A) :
    antipodeAlgHom (k := k) a = HopfAlgebra.antipode k a := rfl

private theorem id_convMul_antipodeAlgHom :
    (WithConv.toConv (AlgHom.id k A) : WithConv (A →ₐ[k] A)) * WithConv.toConv antipodeAlgHom = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  have h : (WithConv.toConv (LinearMap.id : A →ₗ[k] A) : WithConv (A →ₗ[k] A)) *
      WithConv.toConv (HopfAlgebra.antipode k (A := A)) = 1 := by
    apply WithConv.ofConv_injective
    simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv]
    rw [← LinearMap.lTensor_def, HopfAlgebra.mul_antipode_lTensor_comul]
  exact congrArg WithConv.ofConv h

private theorem map_antipode_of_mem_wittHom {x : TruncatedWittVector p n A}
    (hx : x ∈ Deformation.wittHom k p n A) :
    Deformation.TruncWitt.map (antipodeAlgHom (k := k) (A := A)).toRingHom x = -x := by
  have h := Deformation.map_convMul_of_mem_wittHom (T := A) hx (WithConv.toConv (AlgHom.id k A))
    (WithConv.toConv antipodeAlgHom)
  rw [id_convMul_antipodeAlgHom] at h
  have hfac : (1 : WithConv (A →ₐ[k] A)).ofConv.toRingHom =
      (algebraMap k A).comp (Bialgebra.counitAlgHom k A).toRingHom := by
    refine RingHom.ext fun c => ?_
    simp [AlgHom.convOne_apply]
  rw [hfac, ← Deformation.TruncWitt.map_map, Deformation.map_counit_of_mem_wittHom hx, map_zero] at h
  have hid : Deformation.TruncWitt.map
      ((WithConv.toConv (AlgHom.id k A) : WithConv (A →ₐ[k] A)).ofConv.toRingHom) x = x := by
    rw [WithConv.ofConv_toConv]
    exact Deformation.TruncWitt.map_id x
  rw [hid, WithConv.ofConv_toConv] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem antipode_mem_coordAlg (s : ↥(coordAlg k p n A)) :
    HopfAlgebra.antipode k (s : A) ∈ coordAlg k p n A := by
  have key : coordAlg k p n A ≤ (coordAlg k p n A).comap (antipodeAlgHom (k := k) (A := A)) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨x, j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    have h : antipodeAlgHom (k := k) ((x : TruncatedWittVector p n A).coeff j) =
        ((-x : Deformation.wittHom k p n A) : TruncatedWittVector p n A).coeff j := by
      have h2 := congrArg (fun w : TruncatedWittVector p n A => w.coeff j)
        (map_antipode_of_mem_wittHom (p := p) (n := n) x.2)
      simp only [Deformation.TruncWitt.coeff_map] at h2
      exact h2
    rw [h]
    exact Algebra.subset_adjoin ⟨-x, j, rfl⟩
  exact (Subalgebra.mem_comap _ _ _).1 (key s.2)

private noncomputable def antipodeCoord : ↥(coordAlg k p n A) →ₗ[k] ↥(coordAlg k p n A) where
  toFun s := ⟨HopfAlgebra.antipode k (s : A), antipode_mem_coordAlg s⟩
  map_add' s t := Subtype.ext (by simp only [Subalgebra.coe_add, map_add])
  map_smul' r s := Subtype.ext (by simp only [Subalgebra.coe_smul, map_smul, RingHom.id_apply])

private theorem coe_mul'_rTensor_antipodeCoord (z : ↥(coordAlg k p n A) ⊗[k] ↥(coordAlg k p n A)) :
    ((LinearMap.mul' k ↥(coordAlg k p n A)
        (LinearMap.rTensor (↥(coordAlg k p n A)) (antipodeCoord (k := k) (p := p) (n := n) (A := A)) z) :
          ↥(coordAlg k p n A)) : A)
      = LinearMap.mul' k A
          ((HopfAlgebra.antipode k : A →ₗ[k] A).rTensor A (ι₂ (coordAlg k p n A) z)) := by
  induction z with
  | zero => simp only [LinearMap.map_zero, Subalgebra.coe_zero]
  | add x y hx hy => simp only [LinearMap.map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y =>
      simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, Subalgebra.coe_mul, ι₂_tmul]
      rfl

private theorem coe_mul'_lTensor_antipodeCoord (z : ↥(coordAlg k p n A) ⊗[k] ↥(coordAlg k p n A)) :
    ((LinearMap.mul' k ↥(coordAlg k p n A)
        (LinearMap.lTensor (↥(coordAlg k p n A)) (antipodeCoord (k := k) (p := p) (n := n) (A := A)) z) :
          ↥(coordAlg k p n A)) : A)
      = LinearMap.mul' k A
          ((HopfAlgebra.antipode k : A →ₗ[k] A).lTensor A (ι₂ (coordAlg k p n A) z)) := by
  induction z with
  | zero => simp only [LinearMap.map_zero, Subalgebra.coe_zero]
  | add x y hx hy => simp only [LinearMap.map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y =>
      simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply, Subalgebra.coe_mul, ι₂_tmul]
      rfl

private noncomputable scoped instance instHopfCoordAlg : HopfAlgebra k ↥(coordAlg k p n A) where
  antipode := antipodeCoord
  mul_antipode_rTensor_comul := by
    ext s
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Subalgebra.coe_algebraMap]
    rw [coe_mul'_rTensor_antipodeCoord, comul_coord, ι₂_comulS,
      HopfAlgebra.mul_antipode_rTensor_comul_apply, counit_coord]
  mul_antipode_lTensor_comul := by
    ext s
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Subalgebra.coe_algebraMap]
    rw [coe_mul'_lTensor_antipodeCoord, comul_coord, ι₂_comulS,
      HopfAlgebra.mul_antipode_lTensor_comul_apply, counit_coord]

variable {B : Type w} [CommRing B] [Bialgebra k B]

private noncomputable def imageAlg (π : A →ₐc[k] B) : Subalgebra k B :=
  (coordAlg k p n A).map (π : A →ₐ[k] B)

private theorem mem_imageAlg (π : A →ₐc[k] B) (s : ↥(coordAlg k p n A)) :
    π (s : A) ∈ imageAlg (p := p) (n := n) π :=
  Subalgebra.mem_map.2 ⟨s, s.2, rfl⟩

private noncomputable def restrictAlg (π : A →ₐc[k] B) :
    ↥(coordAlg k p n A) →ₐ[k] ↥(imageAlg (p := p) (n := n) π) :=
  ((π : A →ₐ[k] B).comp (coordAlg k p n A).val).codRestrict _ (mem_imageAlg π)

private theorem map_ι₂_eq (π : A →ₐc[k] B) (z : ↥(coordAlg k p n A) ⊗[k] ↥(coordAlg k p n A)) :
    TensorProduct.map (π : A →ₗ[k] B) (π : A →ₗ[k] B) (ι₂ (coordAlg k p n A) z) =
      ι₂ (imageAlg (p := p) (n := n) π)
        (TensorProduct.map (restrictAlg (p := p) (n := n) π).toLinearMap
          (restrictAlg (p := p) (n := n) π).toLinearMap z) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [LinearMap.map_add, hx, hy]
  | tmul x y => rfl

private theorem comulStable_imageAlg (π : A →ₐc[k] B) :
    ComulStable (imageAlg (p := p) (n := n) π) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.1 hb
  obtain ⟨z, hz⟩ := LinearMap.mem_range.1 (comulStable_coordAlg (⟨a, ha⟩ : ↥(coordAlg k p n A)))
  refine LinearMap.mem_range.2 ⟨TensorProduct.map (restrictAlg (p := p) (n := n) π).toLinearMap
    (restrictAlg (p := p) (n := n) π).toLinearMap z, ?_⟩
  rw [← map_ι₂_eq, hz]
  exact CoalgHomClass.map_comp_comul_apply π a

private noncomputable scoped instance instBialgebraImageAlg (π : A →ₐc[k] B) :
    Bialgebra k ↥(imageAlg (p := p) (n := n) π) :=
  subBialgebra _ (comulStable_imageAlg π)

private theorem comul_image (π : A →ₐc[k] B) (t : ↥(imageAlg (p := p) (n := n) π)) :
    Coalgebra.comul (R := k) t = comulS _ (comulStable_imageAlg π) t := rfl

private theorem counit_image (π : A →ₐc[k] B) (t : ↥(imageAlg (p := p) (n := n) π)) :
    Coalgebra.counit (R := k) t = Coalgebra.counit (R := k) (t : B) := rfl

private noncomputable def restrictBialgHom (π : A →ₐc[k] B) :
    ↥(coordAlg k p n A) →ₐc[k] ↥(imageAlg (p := p) (n := n) π) :=
  { restrictAlg (p := p) (n := n) π with
    map_smul' := fun r x => by simp
    counit_comp := by
      ext s
      change Coalgebra.counit (R := k) (π (s : A)) = Coalgebra.counit (R := k) (s : A)
      exact CoalgHomClass.counit_comp_apply π (s : A)
    map_comp_comul := by
      ext s
      apply ι₂_injective (imageAlg (p := p) (n := n) π)
      change ι₂ (imageAlg (p := p) (n := n) π)
          (TensorProduct.map (restrictAlg (p := p) (n := n) π).toLinearMap
            (restrictAlg (p := p) (n := n) π).toLinearMap (Coalgebra.comul (R := k) s)) =
        ι₂ (imageAlg (p := p) (n := n) π)
          (Coalgebra.comul (R := k) (restrictAlg (p := p) (n := n) π s))
      rw [comul_image, ι₂_comulS, comul_coord, ← map_ι₂_eq, ι₂_comulS]
      exact CoalgHomClass.map_comp_comul_apply π (s : A) }

private noncomputable def coordVal : ↥(coordAlg k p n A) →ₐc[k] A :=
  { (coordAlg k p n A).val with
    map_smul' := fun r x => by simp
    counit_comp := rfl
    map_comp_comul := by
      ext s
      change TensorProduct.map (valL (coordAlg k p n A)) (valL (coordAlg k p n A))
          (Coalgebra.comul (R := k) s) = Coalgebra.comul (R := k) (s : A)
      rw [← ι₂_eq_map, comul_coord, ι₂_comulS] }

private theorem ofConv_pow_comp_valL (γ : A →ₗ[k] k) (m : ℕ) :
    ((WithConv.toConv γ : WithConv (A →ₗ[k] k)) ^ m).ofConv ∘ₗ valL (coordAlg k p n A) =
      ((WithConv.toConv (γ ∘ₗ valL (coordAlg k p n A)) :
        WithConv (↥(coordAlg k p n A) →ₗ[k] k)) ^ m).ofConv := by
  induction m with
  | zero =>
      ext s
      simp only [pow_zero, LinearMap.comp_apply, valL_apply, LinearMap.convOne_def,
        WithConv.ofConv_toConv, Algebra.linearMap_apply, counit_coord]
  | succ m ih =>
      ext s
      simp only [pow_succ, LinearMap.comp_apply, valL_apply, LinearMap.convMul_def,
        WithConv.ofConv_toConv]
      rw [comul_coord, ← ι₂_comulS _ comulStable_coordAlg, ι₂_eq_map,
        ← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _),
        ← TensorProduct.map_comp, ← ih]

private theorem hV_coordAlg [CharP k p] [NeZero n] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (β : WithConv (↥(coordAlg k p n A) →ₗ[k] k)) (hβ : β.ofConv 1 = 0) : β ^ p ^ n = 0 := by
  obtain ⟨γ, hγ⟩ := LinearMap.exists_extend (p := (coordAlg k p n A).toSubmodule) β.ofConv
  have hγ' : γ ∘ₗ valL (coordAlg k p n A) = β.ofConv := hγ
  have hγ1 : (WithConv.toConv γ : WithConv (A →ₗ[k] k)).ofConv 1 = 0 := by
    have h1 := LinearMap.congr_fun hγ' 1
    simp only [LinearMap.comp_apply, valL_apply, Subalgebra.coe_one] at h1
    rw [WithConv.ofConv_toConv, h1, hβ]
  have h := ofConv_pow_comp_valL (p := p) (n := n) γ (p ^ n)
  rw [hγ', WithConv.toConv_ofConv] at h
  apply WithConv.ofConv_injective
  rw [← h]
  ext s
  simp only [LinearMap.comp_apply, valL_apply]
  change ((WithConv.toConv γ : WithConv (A →ₗ[k] k)) ^ p ^ n).ofConv (s : A) =
    (0 : WithConv (↥(coordAlg k p n A) →ₗ[k] k)).ofConv s
  rw [HopfAlgebra.convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom k p n A (WithConv.toConv γ)
    hγ1 (s : A) s.2]
  rfl

private theorem restrict_surjective (π : A →ₐc[k] B) :
    Function.Surjective (restrictBialgHom (p := p) (n := n) π) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.1 hb
  exact ⟨⟨a, ha⟩, rfl⟩

private theorem ι₂A_comp_comulRingHom (π : A →ₐc[k] B) :
    (ι₂A (imageAlg (p := p) (n := n) π)).toRingHom.comp
        (Deformation.comulRingHom k ↥(imageAlg (p := p) (n := n) π)) =
      (Deformation.comulRingHom k B).comp (imageAlg (p := p) (n := n) π).val.toRingHom := by
  refine RingHom.ext fun t => ?_
  change ι₂ (imageAlg (p := p) (n := n) π) (Coalgebra.comul (R := k) t) = Coalgebra.comul (R := k) (t : B)
  rw [comul_image, ι₂_comulS]

private theorem ι₂A_comp_includeLeft (π : A →ₐc[k] B) :
    (ι₂A (imageAlg (p := p) (n := n) π)).toRingHom.comp
        (Algebra.TensorProduct.includeLeft :
          ↥(imageAlg (p := p) (n := n) π) →ₐ[k] TensorProduct k _ _).toRingHom =
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] TensorProduct k B B).toRingHom.comp
        (imageAlg (p := p) (n := n) π).val.toRingHom := by
  refine RingHom.ext fun t => ?_
  simp [ι₂A]

private theorem ι₂A_comp_includeRight (π : A →ₐc[k] B) :
    (ι₂A (imageAlg (p := p) (n := n) π)).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          ↥(imageAlg (p := p) (n := n) π) →ₐ[k] TensorProduct k _ _).toRingHom =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k B B).toRingHom.comp
        (imageAlg (p := p) (n := n) π).val.toRingHom := by
  refine RingHom.ext fun t => ?_
  simp [ι₂A]

private theorem exists_wittHom_imageAlg (π : A →ₐc[k] B) (y : Deformation.wittHom k p n B)
    (hy : ∀ i : Fin n, (y : TruncatedWittVector p n B).coeff i ∈ imageAlg (p := p) (n := n) π) :
    ∃ y' : Deformation.wittHom k p n ↥(imageAlg (p := p) (n := n) π),
      ∀ i : Fin n, ((y' : TruncatedWittVector p n ↥(imageAlg (p := p) (n := n) π)).coeff i).val =
        (y : TruncatedWittVector p n B).coeff i := by
  let w : TruncatedWittVector p n ↥(imageAlg (p := p) (n := n) π) :=
    TruncatedWittVector.mk p fun i => ⟨(y : TruncatedWittVector p n B).coeff i, hy i⟩
  have hw : Deformation.TruncWitt.map (imageAlg (p := p) (n := n) π).val.toRingHom w = y :=
    TruncatedWittVector.ext fun i => by
      simp only [Deformation.TruncWitt.coeff_map, w, TruncatedWittVector.coeff_mk]; rfl
  have hinj : Function.Injective (ι₂A (imageAlg (p := p) (n := n) π)) :=
    fun a b h => ι₂_injective (imageAlg (p := p) (n := n) π) h
  have hmem : w ∈ Deformation.wittHom k p n ↥(imageAlg (p := p) (n := n) π) := by
    rw [Deformation.mem_wittHom_iff]
    apply Deformation.TruncWitt.map_injective (f := (ι₂A (imageAlg (p := p) (n := n) π)).toRingHom) hinj
    rw [map_add, Deformation.TruncWitt.map_map, Deformation.TruncWitt.map_map,
      Deformation.TruncWitt.map_map, ι₂A_comp_comulRingHom, ι₂A_comp_includeLeft,
      ι₂A_comp_includeRight, ← Deformation.TruncWitt.map_map, ← Deformation.TruncWitt.map_map,
      ← Deformation.TruncWitt.map_map, hw]
    exact (Deformation.mem_wittHom_iff (y : TruncatedWittVector p n B)).1 y.2
  refine ⟨⟨w, hmem⟩, fun i => ?_⟩
  simp only [w, TruncatedWittVector.coeff_mk]

set_option maxHeartbeats 1600000 in

private theorem exists_wittHom_of_restrict (π : A →ₐc[k] B) (y : Deformation.wittHom k p n B)
    (y' : Deformation.wittHom k p n ↥(imageAlg (p := p) (n := n) π))
    (hy' : ∀ i : Fin n, ((y' : TruncatedWittVector p n ↥(imageAlg (p := p) (n := n) π)).coeff i).val =
        (y : TruncatedWittVector p n B).coeff i)
    (x' : Deformation.wittHom k p n ↥(coordAlg k p n A))
    (hx' : Deformation.wittHomMap p n (restrictBialgHom (p := p) (n := n) π) x' = y') :
    ∃ x : Deformation.wittHom k p n A, Deformation.wittHomMap p n π x = y := by
  refine ⟨Deformation.wittHomMap p n coordVal x', ?_⟩
  apply Subtype.ext
  apply TruncatedWittVector.ext
  intro i
  have h := congrArg (fun z : Deformation.wittHom k p n ↥(imageAlg (p := p) (n := n) π) =>
    ((z : TruncatedWittVector p n ↥(imageAlg (p := p) (n := n) π)).coeff i).val) hx'
  simp only [Deformation.coeff_wittHomMap] at h ⊢
  rw [← hy' i, ← h]
  rfl

end Coord

end WittImageGlue
p2m_reactivate "P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_wittHomShift_surjective.WittImageGlue"

open WittImageGlue in
theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [NeZero n]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (B : Type w) [CommRing B] [Bialgebra k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π)
    (hsat : Function.Surjective (Deformation.wittHomShift k p n A)) :
    Function.Surjective (Deformation.wittHomMap p n π) := by
  intro y
  have hy : ∀ i : Fin n, (y : TruncatedWittVector p n B).coeff i ∈ imageAlg (p := p) (n := n) π :=
    fun i => HopfAlgebra.wittHom_coeff_mem_map_adjoin_of_surjective_of_wittHomShift_surjective
      k p n A B π hπ hsat y i
  obtain ⟨y', hy'⟩ := exists_wittHom_imageAlg π y hy
  obtain ⟨x', hx'⟩ :=
    HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero k p n
      ↥(coordAlg k p n A) ↥(imageAlg (p := p) (n := n) π) (restrictBialgHom π) (restrict_surjective π)
      (fun β hβ => hV_coordAlg β hβ) y'
  exact exists_wittHom_of_restrict π y y' hy' x' hx'

end S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_wittHomShift_surjective
end P2MW
export P2MW.S_HopfAlgebra_wittHomMap_surjective_of_surjective_of_wittHomShift_surjective (solution)
