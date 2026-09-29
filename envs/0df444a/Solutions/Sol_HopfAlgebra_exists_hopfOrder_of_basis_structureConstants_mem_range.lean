-- Prove2me | solution 1 for HopfAlgebra.exists_hopfOrder_of_basis_structureConstants_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/068c49d2-0d2e-5f3b-8559-84c3fd2dde9d

import Mathlib
import Theorems.Thm_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range

open scoped TensorProduct

set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (A : Type) [CommRing A] [HopfAlgebra K A] (hAcocomm : Coalgebra.IsCocomm K A)
    (n : ℕ) (b : Module.Basis (Fin n) K A)
    (hmul : ∀ i j k, b.repr (b i * b j) k ∈ (algebraMap R K).range)
    (hone : ∀ k, b.repr 1 k ∈ (algebraMap R K).range)
    (hcomul : ∀ i jk, (b.tensorProduct b).repr (Coalgebra.comul (R := K) (b i)) jk
        ∈ (algebraMap R K).range)
    (hcounit : ∀ i, Coalgebra.counit (R := K) (b i) ∈ (algebraMap R K).range)
    (hanti : ∀ i k, b.repr (HopfAlgebra.antipode K (b i)) k ∈ (algebraMap R K).range) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ ψ : (K ⊗[R] H) ≃ₐ[K] A,
        ∀ x, Coalgebra.comul (R := K) (ψ x)
          = (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := K) x) := by
  classical
  letI : Algebra R A := ((algebraMap K A).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq fun r => rfl

  have hmem_mul : ∀ i j, b i * b j ∈ Submodule.span R (Set.range b) := by
    intro i j
    rw [show b i * b j = ∑ k, (b.repr (b i * b j) k) • (b k) from (b.sum_repr _).symm]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := hmul i j k
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨k, rfl⟩)
  have hmem_one : (1:A) ∈ Submodule.span R (Set.range b) := by
    rw [show (1:A) = ∑ k, (b.repr 1 k) • (b k) from (b.sum_repr 1).symm]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := hone k
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨k, rfl⟩)
  have hmem_anti : ∀ i, HopfAlgebra.antipode K (b i) ∈ Submodule.span R (Set.range b) := by
    intro i
    rw [show HopfAlgebra.antipode K (b i) = ∑ k, (b.repr _ k) • (b k) from (b.sum_repr _).symm]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := hanti i k
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨k, rfl⟩)
  have hspan_mul : ∀ x ∈ Submodule.span R (Set.range b), ∀ y ∈ Submodule.span R (Set.range b),
      x * y ∈ Submodule.span R (Set.range b) := by
    intro x hx y hy
    refine Submodule.span_induction (p := fun x _ => ∀ y ∈ _, x*y ∈ _)
      ?_ ?_ ?_ ?_ hx y hy
    · rintro _ ⟨i, rfl⟩ y hy
      refine Submodule.span_induction (p := fun y _ => b i * y ∈ _)
        ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨j, rfl⟩; exact hmem_mul i j
      · simpa using Submodule.zero_mem _
      · intro a c _ _ ha hc; simpa [mul_add] using Submodule.add_mem _ ha hc
      · intro r a _ ha; simpa [mul_smul_comm] using Submodule.smul_mem _ r ha
    · intro y _; simpa using Submodule.zero_mem _
    · intro a c _ _ ha hc y hy; simpa [add_mul] using Submodule.add_mem _ (ha y hy) (hc y hy)
    · intro r a _ ha y hy; simpa [smul_mul_assoc] using Submodule.smul_mem _ r (ha y hy)
  let Hsub : Subalgebra R A :=
    { carrier := Submodule.span R (Set.range b)
      mul_mem' := fun {x y} hx hy => hspan_mul x hx y hy
      one_mem' := hmem_one
      add_mem' := fun {x y} hx hy => Submodule.add_mem _ hx hy
      zero_mem' := Submodule.zero_mem _
      algebraMap_mem' := fun r => by
        rw [show algebraMap R A r = r • (1:A) from (Algebra.algebraMap_eq_smul_one r)]
        exact Submodule.smul_mem _ r hmem_one }
  let H := (Hsub : Type)
  letI : CommRing H := inferInstanceAs (CommRing Hsub)
  letI : Algebra R H := inferInstanceAs (Algebra R Hsub)
  let bH : Fin n → H := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hbH_val : ∀ i, (bH i : A) = b i := fun i => rfl
  have hbH_li : LinearIndependent R bH := by
    rw [linearIndependent_iff']
    intro s g hg
    have hb_li := b.linearIndependent
    rw [linearIndependent_iff'] at hb_li
    have hsum : ∑ i ∈ s, (algebraMap R K (g i)) • b i = 0 := by
      have := congrArg (Hsub.val.toLinearMap : H →ₗ[R] A) hg
      rw [map_sum, map_zero] at this
      refine this ▸ Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← algebraMap_smul K (g i)]
      first | rfl | exact congrArg _ (hbH_val i).symm
    intro i hi
    exact hinj ((hb_li s (fun i => algebraMap R K (g i)) hsum i hi).trans (map_zero _).symm)
  have hbH_span : ⊤ ≤ Submodule.span R (Set.range bH) := by
    rintro ⟨x, hx⟩ -
    have hrange : Set.range b = Hsub.toSubmodule.subtype '' Set.range bH := by
      rw [← Set.range_comp]; exact congrArg Set.range (funext fun i => (hbH_val i).symm)
    have hmap : Hsub.toSubmodule = (Submodule.span R (Set.range bH)).map Hsub.toSubmodule.subtype := by
      rw [Submodule.map_span, ← hrange]; rfl
    have hx' : x ∈ (Submodule.span R (Set.range bH)).map Hsub.toSubmodule.subtype := hmap ▸ hx
    obtain ⟨y, hy, hyx⟩ := hx'
    exact (Subtype.ext hyx.symm : (⟨x, hx⟩ : H) = y) ▸ hy
  let bHbasis : Module.Basis (Fin n) R H := Module.Basis.mk hbH_li hbH_span
  have hbHbasis_apply : ∀ i, bHbasis i = bH i := fun i => Module.Basis.mk_apply _ _ i
  haveI : Module.Free R H := Module.Free.of_basis bHbasis
  haveI : Module.Finite R H := Module.Finite.of_basis bHbasis
  haveI : Module.Flat R H := inferInstance

  let ι : H →ₐ[R] A := Hsub.val
  have hι_inj : Function.Injective ι := Subtype.val_injective
  have hι_bH : ∀ i, ι (bH i) = b i := fun i => rfl

  let ι₂ : H ⊗[R] H →ₗ[R] A ⊗[K] A := TensorProduct.lift
    (LinearMap.mk₂ R (fun h h' => (ι h) ⊗ₜ[K] (ι h'))
      (fun h₁ h₂ h' => by simp [map_add, TensorProduct.add_tmul])
      (fun r h h' => by simp [map_smul, TensorProduct.smul_tmul'])
      (fun h h'₁ h'₂ => by simp [map_add, TensorProduct.tmul_add])
      (fun r h h' => by simp [map_smul, TensorProduct.tmul_smul]))
  have hι₂_tmul : ∀ h h', ι₂ (h ⊗ₜ[R] h') = (ι h) ⊗ₜ[K] (ι h') := fun h h' => by
    simp [ι₂, TensorProduct.lift.tmul]
  have hι₂_inj : Function.Injective ι₂ := by
    have h_img2 : ∀ jk : Fin n × Fin n,
        ι₂ ((bHbasis.tensorProduct bHbasis) jk) = (b.tensorProduct b) jk := by
      intro jk
      rw [Module.Basis.tensorProduct_apply, Module.Basis.tensorProduct_apply,
          hbHbasis_apply, hbHbasis_apply, hι₂_tmul, hι_bH, hι_bH]
    have h_li_R2 : LinearIndependent R
        ((b.tensorProduct b) : Fin n × Fin n → A ⊗[K] A) :=
      (b.tensorProduct b).linearIndependent.restrict_scalars
        (Algebra.algebraMap_eq_smul_one' (R := R) (A := K) ▸ hinj)
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hzexp := ((bHbasis.tensorProduct bHbasis).sum_repr z).symm
    rw [hzexp] at hz ⊢
    rw [map_sum] at hz
    simp only [map_smul, h_img2] at hz
    rw [linearIndependent_iff'] at h_li_R2
    have hcoef : ∀ j', (bHbasis.tensorProduct bHbasis).repr z j' = 0 := fun j' =>
      h_li_R2 Finset.univ (fun j' => (bHbasis.tensorProduct bHbasis).repr z j') hz
        j' (Finset.mem_univ _)
    exact Finset.sum_eq_zero fun j' _ => by rw [hcoef j', zero_smul]
  have hι₂_mul : ∀ x y, ι₂ (x * y) = ι₂ x * ι₂ y := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a' c' =>
        simp [hι₂_tmul, Algebra.TensorProduct.tmul_mul_tmul, map_mul]
      | add u v hu hv => simp only [mul_add, map_add, hu, hv]
    | add u v hu hv => simp only [add_mul, map_add, hu, hv]
  have hι₂_one : ι₂ 1 = 1 := by
    rw [show (1 : H⊗[R]H) = (1:H) ⊗ₜ (1:H) from Algebra.TensorProduct.one_def,
        hι₂_tmul, map_one]
    exact (Algebra.TensorProduct.one_def).symm

  let comulH : H →ₗ[R] H ⊗[R] H := bHbasis.constr R fun i =>
    ∑ jk : Fin n × Fin n, Classical.choose (hcomul i jk) • (bH jk.1 ⊗ₜ[R] bH jk.2)
  let counitH : H →ₗ[R] R := bHbasis.constr R fun i => Classical.choose (hcounit i)
  let antipodeH : H →ₗ[R] H := bHbasis.constr R fun i => ⟨_, hmem_anti i⟩

  have key_comul : ∀ h, ι₂ (comulH h) = Coalgebra.comul (R := K) (ι h) := by
    suffices h : ι₂ ∘ₗ comulH = (Coalgebra.comul (R := K) (A := A)).restrictScalars R ∘ₗ ι.toLinearMap from
      fun x => congrFun (congrArg DFunLike.coe h) x
    apply bHbasis.ext
    intro i
    simp only [LinearMap.comp_apply, comulH, Module.Basis.constr_basis,
               LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply]
    simp only [map_sum, map_smul, hι₂_tmul, hι_bH, hbHbasis_apply]
    conv_rhs => rw [show Coalgebra.comul (R := K) (b i)
          = ∑ jk, ((b.tensorProduct b).repr (Coalgebra.comul (b i)) jk) •
              ((b.tensorProduct b) jk) from ((b.tensorProduct b).sum_repr _).symm]
    refine Finset.sum_congr rfl fun jk _ => ?_
    rw [Module.Basis.tensorProduct_apply]
    exact (algebraMap_smul K _ _).symm.trans
      (congrArg (· • (b jk.1 ⊗ₜ[K] b jk.2)) (Classical.choose_spec (hcomul i jk)))
  have key_counit : ∀ h, algebraMap R K (counitH h) = Coalgebra.counit (R := K) (ι h) := by
    suffices h : (Algebra.linearMap R K) ∘ₗ counitH
        = (Coalgebra.counit (R := K) (A := A)).restrictScalars R ∘ₗ ι.toLinearMap from
      fun x => congrFun (congrArg DFunLike.coe h) x
    apply bHbasis.ext; intro i
    simp only [LinearMap.comp_apply, counitH, Module.Basis.constr_basis,
               LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, Algebra.linearMap_apply]
    simp only [hbHbasis_apply, hι_bH]
    exact Classical.choose_spec (hcounit i)
  have key_anti : ∀ h, ι (antipodeH h) = HopfAlgebra.antipode K (ι h) := by
    suffices h : ι.toLinearMap ∘ₗ antipodeH
        = (HopfAlgebra.antipode K (A := A)).restrictScalars R ∘ₗ ι.toLinearMap from
      fun x => congrFun (congrArg DFunLike.coe h) x
    apply bHbasis.ext; intro i
    simp only [LinearMap.comp_apply, antipodeH, Module.Basis.constr_basis,
               AlgHom.toLinearMap_apply, LinearMap.restrictScalars_apply]
    simp only [hbHbasis_apply, hι_bH]
    rfl

  let ψhom : (K ⊗[R] H) →ₐ[K] A := Algebra.TensorProduct.lift
    (Algebra.ofId K A) ι (fun k h => mul_comm _ _)
  have hψhom_tmul : ∀ (k : K) (h : H), ψhom (k ⊗ₜ h) = k • (ι h) := fun k h => by
    rw [show ψhom (k ⊗ₜ h) = (Algebra.ofId K A k) * (ι h) from
        Algebra.TensorProduct.lift_tmul _ _ _ _ _]
    rw [Algebra.ofId_apply, ← Algebra.smul_def]
  have hψhom_basis : ∀ i, ψhom (1 ⊗ₜ (bHbasis i)) = b i := fun i => by
    rw [hψhom_tmul, one_smul, hbHbasis_apply, hι_bH]

  let bKH : Module.Basis (Fin n) K (K ⊗[R] H) := Algebra.TensorProduct.basis K bHbasis
  have hbKH : ∀ i, bKH i = 1 ⊗ₜ (bHbasis i) := fun i => Algebra.TensorProduct.basis_apply _ i
  have hψhom_bij : Function.Bijective ψhom := by
    have heq : ψhom.toLinearMap = (bKH.equiv b (Equiv.refl _)).toLinearMap := by
      apply bKH.ext
      intro i
      simp only [AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
      rw [Module.Basis.equiv_apply, Equiv.refl_apply, hbKH, hψhom_basis]
    rw [show Function.Bijective ψhom ↔ Function.Bijective ψhom.toLinearMap from Iff.rfl, heq]
    exact (bKH.equiv b (Equiv.refl _)).bijective
  let ψ : (K ⊗[R] H) ≃ₐ[K] A := AlgEquiv.ofBijective ψhom hψhom_bij
  have hψ_tmul : ∀ (k : K) (h : H), ψ (k ⊗ₜ h) = k • (ι h) := hψhom_tmul

  have hι₂_swap : ∀ z, ι₂ ((TensorProduct.comm R H H) z) = (TensorProduct.comm K A A) (ι₂ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [TensorProduct.comm_tmul, hι₂_tmul]
    | add u v hu hv => simp only [map_add, hu, hv]

  have hι_mul : ∀ z : H ⊗[R] H, ι ((LinearMap.mul' R H) z) = (LinearMap.mul' K A) (ι₂ z) := by
    intro z; induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul h h' => simp [LinearMap.mul'_apply, hι₂_tmul, map_mul]
    | add u v hu hv => simp only [map_add, hu, hv]
  have hι₂_anti_rTensor : ∀ z, ι₂ ((antipodeH.rTensor H) z)
      = ((HopfAlgebra.antipode K (A := A)).rTensor A) (ι₂ z) := by
    intro z; induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul h h' => simp [LinearMap.rTensor_tmul, hι₂_tmul, key_anti]
    | add u v hu hv => simp only [map_add, hu, hv]
  have hι₂_anti_lTensor : ∀ z, ι₂ ((antipodeH.lTensor H) z)
      = ((HopfAlgebra.antipode K (A := A)).lTensor A) (ι₂ z) := by
    intro z; induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul h h' => simp [LinearMap.lTensor_tmul, hι₂_tmul, key_anti]
    | add u v hu hv => simp only [map_add, hu, hv]

  letI : HopfAlgebra R H := {
    comul := comulH
    counit := counitH
    coassoc := by
      let ι₃R : H ⊗[R] (H ⊗[R] H) →ₗ[R] A ⊗[K] (A ⊗[K] A) := TensorProduct.lift
        (LinearMap.mk₂ R (fun h u => (ι h) ⊗ₜ[K] (ι₂ u))
          (fun h₁ h₂ u => by simp [map_add, TensorProduct.add_tmul])
          (fun r h u => by simp [map_smul, TensorProduct.smul_tmul'])
          (fun h u₁ u₂ => by simp [map_add, TensorProduct.tmul_add])
          (fun r h u => by simp [map_smul, TensorProduct.tmul_smul]))
      have hι₃R_tmul : ∀ h u, ι₃R (h ⊗ₜ u) = ι h ⊗ₜ[K] ι₂ u := fun h u => by
        simp [ι₃R, TensorProduct.lift.tmul]
      have hι₃R_inj : Function.Injective ι₃R := by
        have h_img : ∀ jkl : Fin n × Fin n × Fin n,
            ι₃R ((bHbasis.tensorProduct (bHbasis.tensorProduct bHbasis)) jkl)
            = (b.tensorProduct (b.tensorProduct b)) jkl := by
          intro jkl
          rw [Module.Basis.tensorProduct_apply, Module.Basis.tensorProduct_apply,
              Module.Basis.tensorProduct_apply, Module.Basis.tensorProduct_apply,
              hbHbasis_apply, hbHbasis_apply, hbHbasis_apply, hι₃R_tmul, hι₂_tmul,
              hι_bH, hι_bH, hι_bH]
        have h_li_K : LinearIndependent K
            ((b.tensorProduct (b.tensorProduct b)) : Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A)) :=
          (b.tensorProduct (b.tensorProduct b)).linearIndependent
        have h_li_R : LinearIndependent R
            ((b.tensorProduct (b.tensorProduct b)) : Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A)) :=
          Module.Basis.tensorProduct_tensorProduct_linearIndependent_restrictScalars R K A hinj b
        rw [injective_iff_map_eq_zero]
        intro z hz
        have hzexp := ((bHbasis.tensorProduct (bHbasis.tensorProduct bHbasis)).sum_repr z).symm
        rw [hzexp] at hz ⊢
        rw [map_sum] at hz
        simp only [map_smul, h_img] at hz
        rw [linearIndependent_iff'] at h_li_R
        have hcoef : ∀ j', (bHbasis.tensorProduct (bHbasis.tensorProduct bHbasis)).repr z j' = 0 :=
          fun j' => h_li_R Finset.univ
            (fun j' => (bHbasis.tensorProduct (bHbasis.tensorProduct bHbasis)).repr z j') hz
            j' (Finset.mem_univ _)
        exact Finset.sum_eq_zero fun j' _ => by rw [hcoef j', zero_smul]
      ext x
      apply hι₃R_inj
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have hR : ∀ z, ι₃R ((comulH.lTensor H) z)
          = ((Coalgebra.comul (R := K) (A := A)).lTensor A) (ι₂ z) := by
        intro z; induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul h h' => simp [LinearMap.lTensor_tmul, hι₃R_tmul, hι₂_tmul, key_comul]
        | add u v hu hv => simp only [map_add, hu, hv]
      rw [hR, key_comul]
      have hL : ∀ z, ι₃R ((TensorProduct.assoc R H H H) ((comulH.rTensor H) z))
          = (TensorProduct.assoc K A A A)
              (((Coalgebra.comul (R := K) (A := A)).rTensor A) (ι₂ z)) := by
        intro z; induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul h h' =>
          simp only [LinearMap.rTensor_tmul, hι₂_tmul]
          rw [show (Coalgebra.comul (R := K) (ι h) : A⊗[K]A) = ι₂ (comulH h) from (key_comul h).symm]
          generalize comulH h = w
          induction w using TensorProduct.induction_on with
          | zero => simp
          | tmul a c =>
            simp [TensorProduct.assoc_tmul, hι₃R_tmul, hι₂_tmul, LinearMap.rTensor_tmul]
          | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
        | add u v hu hv => simp only [map_add, hu, hv]
      rw [hL, key_comul]
      exact congrFun (congrArg DFunLike.coe (Coalgebra.coassoc (R := K) (A := A))) (ι x)
    rTensor_counit_comp_comul := by
      ext x
      apply (TensorProduct.lid R H).injective
      apply hι_inj
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply, TensorProduct.lid_tmul, one_smul]

      have key : ∀ z : H ⊗[R] H,
          ι ((TensorProduct.lid R H) ((counitH.rTensor H) z))
          = (TensorProduct.lid K A) (((Coalgebra.counit (R := K) (A := A)).rTensor A) (ι₂ z)) := by
        intro z; induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul h h' =>
          simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hι₂_tmul]
          rw [map_smul, ← key_counit]
          exact (algebraMap_smul K (counitH h) (ι h')).symm
        | add u v hu hv => simp only [map_add, hu, hv]
      rw [key, key_comul]
      have hax := congrFun (congrArg DFunLike.coe
        (Coalgebra.rTensor_counit_comp_comul (R := K) (A := A))) (ι x)
      simp only [LinearMap.comp_apply] at hax
      rw [hax]; simp [TensorProduct.mk_apply, TensorProduct.lid_tmul]
    lTensor_counit_comp_comul := by
      ext x
      apply (TensorProduct.rid R H).injective
      apply hι_inj
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
                 TensorProduct.rid_tmul, one_smul]
      have key : ∀ z : H ⊗[R] H,
          ι ((TensorProduct.rid R H) ((counitH.lTensor H) z))
          = (TensorProduct.rid K A) (((Coalgebra.counit (R := K) (A := A)).lTensor A) (ι₂ z)) := by
        intro z; induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul h h' =>
          simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hι₂_tmul]
          rw [map_smul, ← key_counit]
          exact (algebraMap_smul K (counitH h') (ι h)).symm
        | add u v hu hv => simp only [map_add, hu, hv]
      rw [key, key_comul]
      have hax := congrFun (congrArg DFunLike.coe
        (Coalgebra.lTensor_counit_comp_comul (R := K) (A := A))) (ι x)
      simp only [LinearMap.comp_apply] at hax
      rw [hax]; simp [LinearMap.flip_apply, TensorProduct.mk_apply, TensorProduct.rid_tmul]
    counit_one := by
      apply hinj
      rw [key_counit, map_one ι, map_one (algebraMap R K)]
      exact Bialgebra.counit_one (R := K) (A := A)
    mul_compr₂_counit := by
      ext x y
      apply hinj
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
                 key_counit, map_mul]
      exact congrFun (congrArg DFunLike.coe
        (congrFun (congrArg DFunLike.coe
          (Bialgebra.mul_compr₂_counit (R := K) (A := A))) (ι x))) (ι y)
    comul_one := by
      apply hι₂_inj
      rw [key_comul, map_one, hι₂_one]
      exact Bialgebra.comul_one (R := K) (A := A)
    mul_compr₂_comul := by
      ext x y
      apply hι₂_inj
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply]
      rw [key_comul, map_mul, hι₂_mul, key_comul, key_comul]
      exact congrFun (congrArg DFunLike.coe
        (congrFun (congrArg DFunLike.coe
          (Bialgebra.mul_compr₂_comul (R := K) (A := A))) (ι x))) (ι y)
    antipode := antipodeH
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext
      intro x
      apply hι_inj
      simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
      rw [hι_mul, hι₂_anti_rTensor, key_comul]
      have hax := congrFun (congrArg DFunLike.coe
        (HopfAlgebra.mul_antipode_rTensor_comul (R := K) (A := A))) (ι x)
      simp only [LinearMap.comp_apply] at hax
      rw [hax, Algebra.linearMap_apply, ← key_counit]
      exact (IsScalarTower.algebraMap_apply R K A _).symm
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext
      intro x
      apply hι_inj
      simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
      rw [hι_mul, hι₂_anti_lTensor, key_comul]
      have hax := congrFun (congrArg DFunLike.coe
        (HopfAlgebra.mul_antipode_lTensor_comul (R := K) (A := A))) (ι x)
      simp only [LinearMap.comp_apply] at hax
      rw [hax, Algebra.linearMap_apply, ← key_counit]
      exact (IsScalarTower.algebraMap_apply R K A _).symm
  }
  have hcomulH_eq : (Coalgebra.comul (R := R) (A := H)) = comulH := rfl
  have hcocomm_H : Coalgebra.IsCocomm R H := by
    constructor
    ext x
    apply hι₂_inj
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcomulH_eq]
    simp only [hι₂_swap, key_comul]
    have := hAcocomm.comm_comp_comul
    have := congrFun (congrArg DFunLike.coe this) (ι x)
    simpa using this
  have hψcomul : ∀ x, Coalgebra.comul (R := K) (ψ x)
      = (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := K) x) := by

    suffices h : (Coalgebra.comul (R := K) (A := A)) ∘ₗ ψ.toLinearMap
        = (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) ∘ₗ (Coalgebra.comul (R := K)) from
      fun x => congrFun (congrArg DFunLike.coe h) x
    apply bKH.ext
    intro i
    simp only [LinearMap.comp_apply, hbKH, AlgEquiv.toLinearMap_apply]
    rw [show ψ (1 ⊗ₜ[R] bHbasis i) = b i from by rw [hψ_tmul, one_smul, hbHbasis_apply, hι_bH]]

    have hcomul_KH : Coalgebra.comul (R := K) ((1:K) ⊗ₜ[R] (bHbasis i))
        = (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R K R K K K H H)
            (((1:K) ⊗ₜ[K] (1:K)) ⊗ₜ[R] comulH (bHbasis i)) := by
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one (R := K) (A := K), hcomulH_eq,
          show (1 : K ⊗[K] K) = (1:K) ⊗ₜ[K] (1:K) from Algebra.TensorProduct.one_def]
    rw [hcomul_KH]

    have key : ∀ u : H ⊗[R] H,
        (TensorProduct.map ψ.toLinearMap ψ.toLinearMap)
          ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R K R K K K H H)
            (((1:K) ⊗ₜ[K] (1:K)) ⊗ₜ[R] u)) = ι₂ u := by
      intro u; induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul h h' =>
        simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
                   TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, hψ_tmul, one_smul,
                   hι₂_tmul]
      | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]
    rw [key, hbHbasis_apply, key_comul, hι_bH]
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, hcocomm_H, ψ, hψcomul⟩

end S_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range
end P2MW
export P2MW.S_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range (solution)
