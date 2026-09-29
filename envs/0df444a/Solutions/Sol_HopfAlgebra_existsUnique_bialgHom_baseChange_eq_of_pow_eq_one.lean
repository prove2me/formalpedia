-- Prove2me | solution 1 for HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e6905777-f565-5d23-b8d8-89e068b28dea

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Theorems.Thm_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange
import Theorems.Thm_HopfOrder_finite_sup_and_span_sup_eq_top
import Theorems.Thm_HopfOrder_counit_mem_range_sup
import Theorems.Thm_HopfOrder_antipode_mem_sup
import Theorems.Thm_HopfOrder_comul_mem_range_sup
import Theorems.Thm_HopfAlgebra_toConv_id_pow_eq_one_baseChange
import Theorems.Thm_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one
import Theorems.Thm_HopfAlgebra_eq_of_baseChange_eq
import Theorems.Thm_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one
import Theorems.Thm_HopfOrder_finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_existsUnique_bialgHom_baseChange_eq_of_pow_eq_one
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace HopfOrder
p2m_export "HopfOrder" "tensorSqHom tensorSqHom_tmul baseChangeHom baseChangeHom_tmul baseChangeHom_surjective one_tmul_injective baseChangeHom_injective tensorSqHom_injective bialgebra tensorSqHom_comul_eq algebraMap_counit_eq inclusion moduleFlat_of_finite hopfAlgebraOfFinite isHopfOrder_range_includeRight_comp_of_surjective_baseChange finite_sup_and_span_sup_eq_top counit_mem_range_sup antipode_mem_sup comul_mem_range_sup finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight"
namespace TorsionAux
p2m_open "HopfOrder"

universe uR uK uA

variable {R : Type uR} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type uA} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
  (S : Subalgebra R A) [Module.Finite R ↥S]
  (hc : (∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range))
  (hu : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
  (ha : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S)

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [Module.Finite R ↥S] in

lemma tensorSqHom_comm (z : ↥S ⊗[R] ↥S) :
    HopfOrder.tensorSqHom S (TensorProduct.comm R ↥S ↥S z)
      = TensorProduct.comm K A A (HopfOrder.tensorSqHom S z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.comm_tmul, HopfOrder.tensorSqHom_tmul, HopfOrder.tensorSqHom_tmul,
      TensorProduct.comm_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

include hc hu ha in

theorem isCocomm [Coalgebra.IsCocomm K A] :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
    Coalgebra.IsCocomm R ↥S := by
  letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
  haveI : Module.Flat R ↥S := HopfOrder.moduleFlat_of_finite (K := K) S
  refine ⟨?_⟩
  apply LinearMap.ext
  intro s
  apply HopfOrder.tensorSqHom_injective (K := K) S
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorSqHom_comm,
    HopfOrder.tensorSqHom_comul_eq hc hu s]
  exact Coalgebra.comm_comul K (s : A)

include ha in

theorem coe_toConv_id_pow_apply (m : ℕ) (s : ↥S) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
    ((((WithConv.toConv (AlgHom.id R ↥S)) ^ m).ofConv s : ↥S) : A)
      = ((WithConv.toConv (AlgHom.id K A)) ^ m).ofConv (s : A) := by
  letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
  haveI : Module.Flat R ↥S := HopfOrder.moduleFlat_of_finite (K := K) S
  induction m generalizing s with
  | zero =>
      rw [pow_zero, pow_zero, AlgHom.convOne_apply, AlgHom.convOne_apply, Subalgebra.coe_algebraMap,
        IsScalarTower.algebraMap_apply R K A, HopfOrder.algebraMap_counit_eq hc hu s]
  | succ m ih =>
      rw [pow_succ, pow_succ, AlgHom.convMul_apply, AlgHom.convMul_apply, WithConv.ofConv_toConv,
        WithConv.ofConv_toConv, ← HopfOrder.tensorSqHom_comul_eq hc hu s]
      induction (Coalgebra.comul (R := R) s) using TensorProduct.induction_on with
      | zero => simp only [map_zero, ZeroMemClass.coe_zero]
      | tmul a b =>
          rw [Algebra.TensorProduct.lift_tmul, HopfOrder.tensorSqHom_tmul, Algebra.TensorProduct.lift_tmul,
            MulMemClass.coe_mul, ih a, AlgHom.id_apply, AlgHom.id_apply]
      | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]

include ha in

theorem toConv_id_pow_eq_one (m : ℕ) (hA : (WithConv.toConv (AlgHom.id K A)) ^ m = 1) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
    (WithConv.toConv (AlgHom.id R ↥S)) ^ m = 1 := by
  letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
  haveI : Module.Flat R ↥S := HopfOrder.moduleFlat_of_finite (K := K) S
  refine WithConv.ext (AlgHom.ext fun s => ?_)
  apply Subtype.ext
  rw [coe_toConv_id_pow_apply S hc hu ha m s, hA, ← pow_zero (WithConv.toConv (AlgHom.id K A)),
    ← coe_toConv_id_pow_apply S hc hu ha 0 s, pow_zero]

include ha in

theorem forall_withConv_pow_eq_one (m : ℕ) (hA : (WithConv.toConv (AlgHom.id K A)) ^ m = 1) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
    ∀ (T : Type uA) [CommRing T] [Algebra R T] (f : WithConv (↥S →ₐ[R] T)), f ^ m = 1 := by
  letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
  exact (HopfAlgebra.forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one m).mpr
    (toConv_id_pow_eq_one S hc hu ha m hA)

omit [IsPrincipalIdealRing R] [Module.Finite R ↥S] in

theorem baseChange_inclusion_surjective {S' : Subalgebra R A} (h : S ≤ S')
    (hspan : Submodule.span K (S : Set A) = ⊤) :
    Function.Surjective ((Subalgebra.inclusion h).toLinearMap.baseChange K) := by
  intro y
  obtain ⟨x, hx⟩ := HopfOrder.baseChangeHom_surjective S hspan (HopfOrder.baseChangeHom S' y)
  refine ⟨x, HopfOrder.baseChangeHom_injective S' ?_⟩
  rw [← hx]
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k s => rw [LinearMap.baseChange_tmul, HopfOrder.baseChangeHom_tmul, HopfOrder.baseChangeHom_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end HopfOrder.TorsionAux

namespace HopfOrder
p2m_export "HopfOrder" "tensorSqHom tensorSqHom_tmul baseChangeHom baseChangeHom_tmul baseChangeHom_surjective one_tmul_injective baseChangeHom_injective tensorSqHom_injective bialgebra tensorSqHom_comul_eq algebraMap_counit_eq inclusion moduleFlat_of_finite hopfAlgebraOfFinite isHopfOrder_range_includeRight_comp_of_surjective_baseChange finite_sup_and_span_sup_eq_top counit_mem_range_sup antipode_mem_sup comul_mem_range_sup finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight"
namespace ExtAux
p2m_open "HopfOrder"

variable {R : Type*} [CommRing R] [IsDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type*} [CommRing H] [HopfAlgebra R H]
  {H' : Type*} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']

omit [IsDomain R] [IsFractionRing R K] in
lemma counit_one_tmul {M : Type*} [CommRing M] [HopfAlgebra R M] (x : M) :
    Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[R] x) = algebraMap R K (Coalgebra.counit (R := R) x) := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, mul_one]

include K in
omit [IsDomain R] in

theorem exists_injective_theta [IsDomain R] :
    ∃ θ : H' ⊗[R] H' →ₗ[R] (K ⊗[R] H') ⊗[K] (K ⊗[R] H'),
      Function.Injective θ ∧
      ∀ a b : H', θ (a ⊗ₜ[R] b) = ((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b) := by
  let ι : H' →ₐ[R] K ⊗[R] H' := Algebra.TensorProduct.includeRight
  have hinj : Function.Injective ι := HopfOrder.one_tmul_injective (K := K)
  let e : H' ≃ₐ[R] ↥ι.range := AlgEquiv.ofInjective ι hinj
  haveI : Module.Flat R ↥ι.range := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  refine ⟨(HopfOrder.tensorSqHom (K := K) ι.range).toLinearMap ∘ₗ
      (Algebra.TensorProduct.congr (S := R) e e).toLinearMap, ?_, fun a b => ?_⟩
  · rw [LinearMap.coe_comp]
    exact (HopfOrder.tensorSqHom_injective (K := K) ι.range).comp
      (Algebra.TensorProduct.congr (S := R) e e).injective
  · rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.toLinearMap_apply, HopfOrder.tensorSqHom_tmul]
    change ((e a : ↥ι.range) : K ⊗[R] H') ⊗ₜ[K] ((e b : ↥ι.range) : K ⊗[R] H') = _
    rw [AlgEquiv.ofInjective_apply, AlgEquiv.ofInjective_apply]
    rfl

omit [IsDomain R] in

theorem exists_algHom (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H'))
    (hψ : ∀ h : H, ∃ h' : H', (1 : K) ⊗ₜ[R] h' = ψ ((1 : K) ⊗ₜ[R] h)) :
    ∃ φ₀ : H →ₐ[R] H', ∀ h, (1 : K) ⊗ₜ[R] (φ₀ h) = ψ ((1 : K) ⊗ₜ[R] h) := by
  classical
  let ι : H' →ₐ[R] K ⊗[R] H' := Algebra.TensorProduct.includeRight
  have hinj : Function.Injective ι := HopfOrder.one_tmul_injective (K := K)
  let g : H →ₐ[R] K ⊗[R] H' :=
    ((ψ : (K ⊗[R] H) →ₐ[K] (K ⊗[R] H')).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H)
  have hgmem : ∀ h, g h ∈ ι.range := fun h => by
    obtain ⟨h', e⟩ := hψ h
    exact ⟨h', e⟩
  let e : H' ≃ₐ[R] ↥ι.range := AlgEquiv.ofInjective ι hinj
  refine ⟨(e.symm : ↥ι.range →ₐ[R] H').comp (g.codRestrict ι.range hgmem), fun h => ?_⟩
  have h1 : ι (e.symm (g.codRestrict ι.range hgmem h)) = g h := by
    rw [← AlgEquiv.ofInjective_apply ι hinj, AlgEquiv.apply_symm_apply, AlgHom.coe_codRestrict]
  exact h1

omit [IsDomain R] [IsFractionRing R K] [Module.Flat R H'] in
theorem theta_comul (θ : H' ⊗[R] H' →ₗ[R] (K ⊗[R] H') ⊗[K] (K ⊗[R] H'))
    (hθ : ∀ a b : H', θ (a ⊗ₜ[R] b) = ((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b)) (h' : H') :
    θ (Coalgebra.comul (R := R) h') = Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[R] h') := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) h' using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [hθ, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | add x y hx hy => rw [map_add, hx, hy, TensorProduct.tmul_add, map_add]

omit [IsDomain R] [IsFractionRing R K] [Module.Flat R H'] in
theorem theta_map_comul (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H'))
    (θ : H' ⊗[R] H' →ₗ[R] (K ⊗[R] H') ⊗[K] (K ⊗[R] H'))
    (hθ : ∀ a b : H', θ (a ⊗ₜ[R] b) = ((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b))
    (φ₀ : H →ₐ[R] H') (hιφ : ∀ h, (1 : K) ⊗ₜ[R] (φ₀ h) = ψ ((1 : K) ⊗ₜ[R] h)) (h : H) :
    θ (Algebra.TensorProduct.map φ₀ φ₀ (Coalgebra.comul (R := R) h))
      = TensorProduct.map (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H')).toLinearMap
          (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H')).toLinearMap
          (Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[R] h)) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) h using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, hθ, hιφ, hιφ,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul]
      try rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add, map_add, map_add]

omit [IsDomain R] [Module.Flat R H'] in
theorem counitAlgHom_comp (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H'))
    (φ₀ : H →ₐ[R] H') (hιφ : ∀ h, (1 : K) ⊗ₜ[R] (φ₀ h) = ψ ((1 : K) ⊗ₜ[R] h)) :
    (Bialgebra.counitAlgHom R H').comp φ₀ = Bialgebra.counitAlgHom R H := by
  apply AlgHom.ext
  intro h
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
  apply IsFractionRing.injective R K
  rw [← counit_one_tmul (K := K) (φ₀ h), ← counit_one_tmul (K := K) h, hιφ]
  exact CoalgHomClass.counit_comp_apply ψ _

theorem map_comp_comulAlgHom (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H'))
    (φ₀ : H →ₐ[R] H') (hιφ : ∀ h, (1 : K) ⊗ₜ[R] (φ₀ h) = ψ ((1 : K) ⊗ₜ[R] h)) :
    (Algebra.TensorProduct.map φ₀ φ₀).comp (Bialgebra.comulAlgHom R H)
      = (Bialgebra.comulAlgHom R H').comp φ₀ := by
  obtain ⟨θ, hθinj, hθ⟩ := exists_injective_theta (R := R) (K := K) (H' := H')
  apply AlgHom.ext
  intro h
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply]
  apply hθinj
  rw [theta_map_comul ψ θ hθ φ₀ hιφ h, theta_comul θ hθ (φ₀ h), hιφ]
  exact CoalgHomClass.map_comp_comul_apply ψ _

omit [IsDomain R] [IsFractionRing R K] [Module.Flat R H'] in
theorem baseChange_eq (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H'))
    (φ₀ : H →ₐ[R] H') (hιφ : ∀ h, (1 : K) ⊗ₜ[R] (φ₀ h) = ψ ((1 : K) ⊗ₜ[R] h)) :
    φ₀.toLinearMap.baseChange K = (ψ : (K ⊗[R] H) →ₐ[K] (K ⊗[R] H')).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k h =>
      rw [LinearMap.baseChange_tmul]
      have e1 : (k ⊗ₜ[R] h : K ⊗[R] H) = k • ((1 : K) ⊗ₜ[R] h) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e2 : (k ⊗ₜ[R] φ₀ h : K ⊗[R] H') = k • ((1 : K) ⊗ₜ[R] φ₀ h) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      show (k ⊗ₜ[R] φ₀ h : K ⊗[R] H') = ψ (k ⊗ₜ[R] h)
      rw [e1, map_smul, ← hιφ, e2]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_bialgHom_of_forall_exists (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H'))
    (hψ : ∀ h : H, ∃ h' : H', (1 : K) ⊗ₜ[R] h' = ψ ((1 : K) ⊗ₜ[R] h)) :
    ∃ φ : H →ₐc[R] H',
      (φ : H →ₐ[R] H').toLinearMap.baseChange K = (ψ : (K ⊗[R] H) →ₐ[K] (K ⊗[R] H')).toLinearMap := by
  obtain ⟨φ₀, hιφ⟩ := exists_algHom (K := K) ψ hψ
  exact ⟨BialgHom.ofAlgHom φ₀ (counitAlgHom_comp (K := K) ψ φ₀ hιφ) (map_comp_comulAlgHom (K := K) ψ φ₀ hιφ),
    baseChange_eq ψ φ₀ hιφ⟩

end HopfOrder.ExtAux

namespace HopfOrder
p2m_export "HopfOrder" "tensorSqHom tensorSqHom_tmul baseChangeHom baseChangeHom_tmul baseChangeHom_surjective one_tmul_injective baseChangeHom_injective tensorSqHom_injective bialgebra tensorSqHom_comul_eq algebraMap_counit_eq inclusion moduleFlat_of_finite hopfAlgebraOfFinite isHopfOrder_range_includeRight_comp_of_surjective_baseChange finite_sup_and_span_sup_eq_top counit_mem_range_sup antipode_mem_sup comul_mem_range_sup finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight"
namespace Cor336
p2m_open "HopfOrder"

theorem exists_inclusion
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S S' : Subalgebra R A) [Module.Finite R ↥S] [Module.Finite R ↥S'] (hle : S ≤ S')
    (hc : (∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range))
    (hu : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (ha : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S)
    (hc' : (∀ x ∈ S', Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range))
    (hu' : ∀ x ∈ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (ha' : ∀ x ∈ S', HopfAlgebra.antipode K x ∈ S') :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
    letI : HopfAlgebra R ↥S' := HopfOrder.hopfAlgebraOfFinite S' hc' hu' ha'
    ∃ j : ↥S →ₐc[R] ↥S', Function.Injective j ∧ (∀ s : ↥S, ((j s : ↥S') : A) = (s : A)) ∧
      (Submodule.span K (S : Set A) = ⊤ →
        Function.Surjective ((j : ↥S →ₐ[R] ↥S').toLinearMap.baseChange K)) := by
  letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebraOfFinite S hc hu ha
  letI : HopfAlgebra R ↥S' := HopfOrder.hopfAlgebraOfFinite S' hc' hu' ha'
  haveI : Module.Flat R ↥S := HopfOrder.moduleFlat_of_finite (K := K) S
  haveI : Module.Flat R ↥S' := HopfOrder.moduleFlat_of_finite (K := K) S'
  refine ⟨HopfOrder.inclusion (K := K) hle hc hu hc' hu', ?_, fun s => rfl, fun hspan => ?_⟩
  · intro a b hab
    apply Subtype.ext
    have h := congrArg (fun c : ↥S' => (c : A)) hab
    exact h
  · exact HopfOrder.TorsionAux.baseChange_inclusion_surjective S hle hspan

universe u w

theorem le_of_toConv_id_pow_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Coalgebra.IsCocomm K A]
    (n : ℕ) (htA : (WithConv.toConv (AlgHom.id K A)) ^ p ^ n = 1)
    {S₁ S₂ : Subalgebra R A} [Module.Finite R ↥S₁] [Module.Finite R ↥S₂]
    (h1s : Submodule.span K (S₁ : Set A) = ⊤)
    (h1c : (∀ x ∈ S₁, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S₁.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S₁.val)).range))
    (h1a : ∀ x ∈ S₁, HopfAlgebra.antipode K x ∈ S₁)
    (h1u : ∀ x ∈ S₁, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (h2c : (∀ x ∈ S₂, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S₂.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S₂.val)).range))
    (h2a : ∀ x ∈ S₂, HopfAlgebra.antipode K x ∈ S₂)
    (h2u : ∀ x ∈ S₂, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    S₂ ≤ S₁ := by
  classical

  obtain ⟨hCf, hCs⟩ := HopfOrder.finite_sup_and_span_sup_eq_top (S := S₁) (S' := S₂) h1s
  have hCc := HopfOrder.comul_mem_range_sup h1c h2c
  have hCa := HopfOrder.antipode_mem_sup h1a h2a
  have hCu := HopfOrder.counit_mem_range_sup h1u h2u
  haveI := hCf

  obtain ⟨j, hj, hjcoe, hjK⟩ := exists_inclusion (K := K) S₁ (S₁ ⊔ S₂) le_sup_left h1c h1u h1a hCc hCu hCa
  letI I₁ : HopfAlgebra R ↥S₁ := HopfOrder.hopfAlgebraOfFinite S₁ h1c h1u h1a
  letI IC : HopfAlgebra R ↥(S₁ ⊔ S₂) := HopfOrder.hopfAlgebraOfFinite (S₁ ⊔ S₂) hCc hCu hCa
  haveI : Module.Flat R ↥S₁ := HopfOrder.moduleFlat_of_finite (K := K) S₁
  haveI : Module.Flat R ↥(S₁ ⊔ S₂) := HopfOrder.moduleFlat_of_finite (K := K) (S₁ ⊔ S₂)
  haveI : Coalgebra.IsCocomm R ↥S₁ := HopfOrder.TorsionAux.isCocomm S₁ h1c h1u h1a
  haveI : Coalgebra.IsCocomm R ↥(S₁ ⊔ S₂) := HopfOrder.TorsionAux.isCocomm (S₁ ⊔ S₂) hCc hCu hCa

  have ht1 := HopfOrder.TorsionAux.forall_withConv_pow_eq_one S₁ h1c h1u h1a (p ^ n) htA
  have htC := HopfOrder.TorsionAux.forall_withConv_pow_eq_one (S₁ ⊔ S₂) hCc hCu hCa (p ^ n) htA

  have hsurj : Function.Surjective j :=
    HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one K p hp2 hunif n
      ht1 htC j hj (hjK h1s)
  intro x hx
  obtain ⟨s, hs⟩ := hsurj ⟨x, (le_sup_right : S₂ ≤ S₁ ⊔ S₂) hx⟩
  have h3 := congrArg (fun c : ↥(S₁ ⊔ S₂) => (c : A)) hs
  simp only [hjcoe] at h3

  rw [← h3]
  exact s.2

universe v

theorem forall_exists
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (n : ℕ)
    (hH' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' →ₐ[R] T)), f ^ p ^ n = 1)
    (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H')) :
    ∀ h : H, ∃ h' : H', (1 : K) ⊗ₜ[R] h' = ψ ((1 : K) ⊗ₜ[R] h) := by
  classical

  have hsurj1 : Function.Surjective
      (((BialgHom.id R H') : H' →ₐ[R] H').toLinearMap.baseChange K) := by
    intro z
    refine ⟨z, ?_⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul k h => rw [LinearMap.baseChange_tmul]; rfl
    | add x y hx hy => rw [map_add, hx, hy]
  obtain ⟨⟨h1f, h1s, h1c, h1a, h1u⟩, -⟩ :=
    HopfOrder.isHopfOrder_range_includeRight_comp_of_surjective_baseChange (F := K)
      (BialgHom.id R H') hsurj1

  obtain ⟨h2f, h2c, h2a, h2u⟩ :=
    HopfOrder.finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight
      (R := R) (F := K) ψ
  haveI := h1f
  haveI := h2f

  have htA : (WithConv.toConv (AlgHom.id K (K ⊗[R] H'))) ^ p ^ n = 1 :=
    HopfAlgebra.toConv_id_pow_eq_one_baseChange K (p ^ n)
      ((HopfAlgebra.forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one (p ^ n)).mp hH')
  have hle := le_of_toConv_id_pow_eq_one K p hp2 hunif n htA h1s h1c h1a h1u h2c h2a h2u
  intro h
  have hm : ψ ((1 : K) ⊗ₜ[R] h) ∈ (((ψ : (K ⊗[R] H) →ₐ[K] (K ⊗[R] H')).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H)).range := ⟨h, rfl⟩
  obtain ⟨h', hh'⟩ := hle hm
  exact ⟨h', hh'⟩

end HopfOrder.Cor336

universe u v

open scoped TensorProduct in

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (n : ℕ)
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1)
    (hH' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' →ₐ[R] T)), f ^ p ^ n = 1)
    (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H')) :
    ∃! φ : H →ₐc[R] H',
      (φ : H →ₐ[R] H').toLinearMap.baseChange K = (ψ : (K ⊗[R] H) →ₐ[K] (K ⊗[R] H')).toLinearMap := by
  obtain ⟨φ, hφ⟩ := HopfOrder.ExtAux.exists_bialgHom_of_forall_exists (R := R) (K := K) ψ
    (HopfOrder.Cor336.forall_exists K p hp2 hunif n hH' ψ)
  exact ⟨φ, hφ, fun φ' hφ' => HopfAlgebra.eq_of_baseChange_eq K φ' φ (by rw [hφ', hφ])⟩

end S_HopfAlgebra_existsUnique_bialgHom_baseChange_eq_of_pow_eq_one
end P2MW
export P2MW.S_HopfAlgebra_existsUnique_bialgHom_baseChange_eq_of_pow_eq_one (solution)
