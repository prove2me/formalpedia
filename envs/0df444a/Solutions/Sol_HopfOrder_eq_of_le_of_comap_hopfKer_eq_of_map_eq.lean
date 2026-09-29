-- Prove2me | solution 1 for HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c654ecba-7fe2-5bb0-8b3a-b4d1c429f85e

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfOrderData
import Theorems.Thm_HopfOrder_isHopfOrder_map
import Theorems.Thm_HopfOrder_map_hopfKer_eq_inf_hopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Theorems.Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_eq_of_le_of_comap_hopfKer_eq_of_map_eq

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct

namespace L5D

set_option maxHeartbeats 4000000 in

theorem main
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    {S S' : Subalgebra R A} (hle : S ≤ S')
    (hSfin : Module.Finite R ↥S)
    (hSspan : Submodule.span K (S : Set A) = ⊤)
    (hScomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hSanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hScounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hS'fin : Module.Finite R ↥S')
    (hS'span : Submodule.span K (S' : Set A) = ⊤)
    (hS'comul : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range)
    (hS'anti : ∀ x ∈ S', HopfAlgebra.antipode K (A := A) x ∈ S')
    (hS'counit : ∀ x ∈ S', Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hker : S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)
      = S'.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))
    (himg : S.map ((π : A →ₐ[K] Ā).restrictScalars R) = S'.map ((π : A →ₐ[K] Ā).restrictScalars R)) :
    S = S' := by
  classical

  haveI : Module.Finite R ↥S := hSfin
  haveI : Module.Finite R ↥S' := hS'fin
  haveI : Module.Flat R ↥S := HopfOrder.moduleFlat_of_finite (K := K) S
  haveI : Module.Flat R ↥S' := HopfOrder.moduleFlat_of_finite (K := K) S'
  haveI : Module.Free R ↥S' := HopfOrder.moduleFree_of_finite (K := K) S'
  set T : Subalgebra R Ā := S'.map ((π : A →ₐ[K] Ā).restrictScalars R) with hTdef
  obtain ⟨hTfin, -, hTcomul, hTanti, hTcounit⟩ :=
    HopfOrder.isHopfOrder_map S' hS'fin hS'span hS'comul hS'anti hS'counit π hπ
  haveI : Module.Finite R ↥T := hTfin
  haveI : Module.Flat R ↥T := HopfOrder.moduleFlat_of_finite (K := K) T
  haveI : Module.Free R ↥T := HopfOrder.moduleFree_of_finite (K := K) T
  letI instH : HopfAlgebra R ↥S := HopfOrder.hopfAlgebra S hScomul hScounit hSanti
  letI instH' : HopfAlgebra R ↥S' := HopfOrder.hopfAlgebra S' hS'comul hS'counit hS'anti
  letI instT : HopfAlgebra R ↥T := HopfOrder.hopfAlgebra T hTcomul hTcounit hTanti

  letI algS : Algebra R ↥S := Bialgebra.toAlgebra
  letI algS' : Algebra R ↥S' := Bialgebra.toAlgebra
  letI algT : Algebra R ↥T := Bialgebra.toAlgebra
  letI modS : Module R ↥S := Algebra.toModule
  letI modS' : Module R ↥S' := Algebra.toModule
  letI modT : Module R ↥T := Algebra.toModule

  have hπS' : ∀ x ∈ S', π x ∈ T := fun x hx => Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
  have hπS : ∀ x ∈ S, π x ∈ T := fun x hx => hπS' x (hle hx)

  have htorsor := HopfOrder.map_hopfKer_eq_inf_hopfKer (K := K) S' (H := ↥S') S'.val
      Subtype.val_injective (Subalgebra.range_val S')
      (HopfOrder.val_comul hS'comul hS'counit hS'anti) π (Hbar := ↥T)
      (HopfOrder.mapBialgHom π hπS' hS'comul hS'counit hTcomul hTcounit) T.val
      Subtype.val_injective (fun h => rfl)

  obtain ⟨ι, hιcoe⟩ : ∃ ι : ↥S →ₐc[R] ↥S', ∀ s : ↥S, ((ι s : ↥S') : A) = (s : A) :=
    ⟨HopfOrder.inclusion hle hScomul hScounit hS'comul hS'counit, fun _ => rfl⟩
  obtain ⟨q', hq'coe, htorsor'⟩ : ∃ q' : ↥S' →ₐc[R] ↥T, (∀ s : ↥S', ((q' s : ↥T) : Ā) = π (s : A)) ∧
      (HopfAlgebra.hopfKer q').map S'.val = S' ⊓ (HopfAlgebra.hopfKer π).restrictScalars R :=
    ⟨HopfOrder.mapBialgHom π hπS' hS'comul hS'counit hTcomul hTcounit, fun _ => rfl, htorsor⟩
  clear htorsor
  obtain ⟨q, hqcoe⟩ : ∃ q : ↥S →ₐc[R] ↥T, ∀ s : ↥S, ((q s : ↥T) : Ā) = π (s : A) :=
    ⟨HopfOrder.mapBialgHom π hπS hScomul hScounit hTcomul hTcounit, fun _ => rfl⟩
  have hq'ι : ∀ s : ↥S, q' (ι s) = q s := fun s =>
    Subtype.ext (by rw [hq'coe, hqcoe, hιcoe])
  have hq' : Function.Surjective q' := by
    rintro ⟨t, ht⟩
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp ht
    exact ⟨⟨x, hx⟩, Subtype.ext (hq'coe _)⟩
  have hq : Function.Surjective q := by
    rintro ⟨t, ht⟩
    have ht' : t ∈ S.map ((π : A →ₐ[K] Ā).restrictScalars R) := by rw [himg]; exact ht
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp ht'
    exact ⟨⟨x, hx⟩, Subtype.ext (hqcoe _)⟩

  have hgal : HopfAlgebra.IsHopfGalois q := HopfAlgebra.isHopfGalois_of_surjective q hq
  have hgal' : HopfAlgebra.IsHopfGalois q' := HopfAlgebra.isHopfGalois_of_surjective q' hq'

  let ιA : ↥S →ₐ[R] ↥S' := (ι : ↥S →ₐ[R] ↥S')
  let ΦA : ↥S ⊗[R] ↥T →ₐ[R] ↥S' ⊗[R] ↥T := Algebra.TensorProduct.map ιA (AlgHom.id R ↥T)
  let ΨA : ↥S ⊗[R] ↥S →ₐ[R] ↥S' ⊗[R] ↥S' := Algebra.TensorProduct.map ιA ιA
  let ΛA : ↥S' ⊗[R] ↥S →ₐ[R] ↥S' ⊗[R] ↥S' := Algebra.TensorProduct.map (AlgHom.id R ↥S') ιA
  have hιA : ∀ s, ιA s = ι s := fun _ => rfl

  have hcoact : ∀ y : ↥S, HopfAlgebra.coaction q' (ι y) = ΦA (HopfAlgebra.coaction q y) := by
    intro y
    rw [HopfAlgebra.coaction_apply, HopfAlgebra.coaction_apply,
      ← CoalgHomClass.map_comp_comul_apply ι y]

    suffices hlin : ((Algebra.TensorProduct.map (AlgHom.id R ↥S') (q' : ↥S' →ₐ[R] ↥T)).toLinearMap ∘ₗ
          TensorProduct.map (ι : ↥S →ₗc[R] ↥S').toLinearMap (ι : ↥S →ₗc[R] ↥S').toLinearMap)
        = ΦA.toLinearMap ∘ₗ (Algebra.TensorProduct.map (AlgHom.id R ↥S) (q : ↥S →ₐ[R] ↥T)).toLinearMap by
      exact LinearMap.congr_fun hlin (Coalgebra.comul (R := R) y)
    refine TensorProduct.ext' fun a b => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    show (ι a) ⊗ₜ[R] q' (ι b) = ΦA (a ⊗ₜ[R] q b)
    rw [hq'ι]
    rfl
  have hsquare : ∀ z, HopfAlgebra.canMap q' (ΨA z) = ΦA (HopfAlgebra.canMap q z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, HopfAlgebra.canMap_tmul, HopfAlgebra.canMap_tmul,
          map_mul ΦA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hιA, hιA, hcoact b]

  let W : Submodule R (↥S' ⊗[R] ↥S') := LinearMap.range ΛA.toLinearMap
  have hΨW : ∀ z, ΨA z ∈ W := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y hx hy => rw [map_add]; exact W.add_mem hx hy
    | tmul a b =>
        refine ⟨ιA a ⊗ₜ[R] b, ?_⟩
        show ΛA (ιA a ⊗ₜ[R] b) = ΨA (a ⊗ₜ[R] b)
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hWmul : ∀ (a : ↥S') (w : ↥S' ⊗[R] ↥S'), w ∈ W → (a ⊗ₜ[R] (1 : ↥S')) * w ∈ W := by
    rintro a w ⟨u, rfl⟩
    refine ⟨(a ⊗ₜ[R] (1 : ↥S)) * u, ?_⟩
    show ΛA ((a ⊗ₜ[R] (1 : ↥S)) * u) = (a ⊗ₜ[R] (1 : ↥S')) * ΛA u
    rw [map_mul ΛA, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

  have hWonto : ∀ z' : ↥S' ⊗[R] ↥T, ∃ w ∈ W, HopfAlgebra.canMap q' w = z' := by

    suffices htop : W.map (HopfAlgebra.canMap q') = ⊤ by
      intro z'
      have hz' : z' ∈ W.map (HopfAlgebra.canMap q') := by rw [htop]; exact Submodule.mem_top
      obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hz'
      exact ⟨w, hw, hwz⟩
    have hone : ∀ t : ↥T, (1 : ↥S') ⊗ₜ[R] t ∈ W.map (HopfAlgebra.canMap q') := by
      intro t
      obtain ⟨w0, hw0⟩ := hgal.1 ((1 : ↥S) ⊗ₜ[R] t)
      refine Submodule.mem_map.mpr ⟨ΨA w0, hΨW w0, ?_⟩
      rw [hsquare, hw0]
      show ΦA ((1 : ↥S) ⊗ₜ[R] t) = (1 : ↥S') ⊗ₜ[R] t
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    have hmul : ∀ (a : ↥S') (v : ↥S' ⊗[R] ↥T), v ∈ W.map (HopfAlgebra.canMap q') →
        (a ⊗ₜ[R] (1 : ↥T)) * v ∈ W.map (HopfAlgebra.canMap q') := by
      rintro a v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨(a ⊗ₜ[R] (1 : ↥S')) * w, hWmul a w hw, ?_⟩
      rw [HopfAlgebra.canMap_apply, HopfAlgebra.canMap_apply, map_mul (HopfAlgebra.canAlgHom q'),
        HopfAlgebra.canAlgHom_tmul, map_one, mul_one]
    refine Submodule.eq_top_iff'.mpr fun z' => ?_
    induction z' using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul a t =>
        have : a ⊗ₜ[R] t = (a ⊗ₜ[R] (1 : ↥T)) * ((1 : ↥S') ⊗ₜ[R] t) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this]
        exact hmul a _ (hone t)

  have hdecomp : ∀ z : ↥S' ⊗[R] ↥S', ∃ w ∈ W,
      z - w ∈ Submodule.span R (HopfAlgebra.balancingRelations q') := by
    intro z
    obtain ⟨w, hw, hwz⟩ := hWonto (HopfAlgebra.canMap q' z)
    exact ⟨w, hw, hgal'.2 _ (by rw [map_sub, hwz, sub_self])⟩

  have hC'S : ∀ c : ↥S', c ∈ HopfAlgebra.hopfKer q' → (c : A) ∈ S := by
    intro c hc
    have hcA : (c : A) ∈ (HopfAlgebra.hopfKer q').map S'.val := Subalgebra.mem_map.mpr ⟨c, hc, rfl⟩
    rw [htorsor'] at hcA
    obtain ⟨-, hcker⟩ := Algebra.mem_inf.mp hcA
    rw [Subalgebra.mem_restrictScalars] at hcker

    have hmem' : (⟨(c : A), hcker⟩ : ↥(HopfAlgebra.hopfKer π)) ∈
        S'.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R) := by
      rw [Subalgebra.mem_comap]
      exact c.2
    rw [← hker, Subalgebra.mem_comap] at hmem'
    exact hmem'

  let M : Submodule R ↥S' := (Subalgebra.toSubmodule S).comap (S'.val : ↥S' →ₐ[R] A).toLinearMap
  have hMmem : ∀ x : ↥S', x ∈ M ↔ (x : A) ∈ S := fun x => Iff.rfl
  have hkey : ∀ (f : ↥S' →ₗ[↥(HopfAlgebra.hopfKer q')] ↥(HopfAlgebra.hopfKer q')) (a b : ↥S'),
      ((f a : ↥(HopfAlgebra.hopfKer q')) : ↥S') * b ∈ M := by
    intro f a₀ b₀
    set μ : ↥S' ⊗[R] ↥S' →ₗ[R] ↥S' := TensorProduct.lift ((LinearMap.mul R ↥S').comp
        ((HopfAlgebra.hopfKer q').val.toLinearMap ∘ₗ f.restrictScalars R)) with hμ
    have hμ_tmul : ∀ a b : ↥S', μ (a ⊗ₜ[R] b) = ((f a : ↥(HopfAlgebra.hopfKer q')) : ↥S') * b := by
      intro a b
      rw [hμ, TensorProduct.lift.tmul]
      rfl

    have hμbal : ∀ x ∈ Submodule.span R (HopfAlgebra.balancingRelations q'), μ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨a, h, b, hh, rfl⟩ := hx
          rw [map_sub, hμ_tmul, hμ_tmul]
          have hfa : f (a * h) = (⟨h, hh⟩ : ↥(HopfAlgebra.hopfKer q')) • f a := by
            rw [← map_smul]
            congr 1
            show a * h = h * a
            exact mul_comm a h
          rw [hfa]
          show ((⟨h, hh⟩ : ↥(HopfAlgebra.hopfKer q')) * f a : ↥(HopfAlgebra.hopfKer q')).1 * b
            - ((f a : ↥(HopfAlgebra.hopfKer q')) : ↥S') * (h * b) = 0
          rw [Subalgebra.coe_mul]
          ring
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul r x _ hx => rw [map_smul, hx, smul_zero]

    have hμW : ∀ w ∈ W, μ w ∈ M := by
      rintro w ⟨u, rfl⟩
      show μ (ΛA u) ∈ M
      induction u using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
      | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
      | tmul a y =>
          rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hιA, hμ_tmul, hMmem,
            Subalgebra.coe_mul]
          exact S.mul_mem (hC'S _ (f a).2) (by rw [hιcoe]; exact y.2)

    have hall : ∀ z, μ z ∈ M := by
      intro z
      obtain ⟨w, hw, hzw⟩ := hdecomp z
      have : z = w + (z - w) := by abel
      rw [this, map_add, hμbal _ hzw, add_zero]
      exact hμW w hw
    have h := hall (a₀ ⊗ₜ[R] b₀)
    rwa [hμ_tmul] at h

  obtain ⟨s, hs⟩ := (HopfAlgebra.finite_projective_hopfKer_of_surjective q' hq').2.out
  refine le_antisymm hle fun x hx => ?_
  set x' : ↥S' := ⟨x, hx⟩ with hx'
  suffices hxM : x' ∈ M by exact (hMmem x').mp hxM
  have hrepr : x' = (s x').sum (fun m c => (c : ↥S') * m) := by
    conv_lhs => rw [← hs x']
    rw [Finsupp.linearCombination_apply]
    rfl
  rw [hrepr, Finsupp.sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact hkey ((Finsupp.lapply m).comp s) x' m

end L5D

universe u v w w'

open scoped TensorProduct in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type w'} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    {S S' : Subalgebra R A} (hle : S ≤ S')
    (hSfin : Module.Finite R ↥S)
    (hSspan : Submodule.span K (S : Set A) = ⊤)
    (hScomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hSanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hScounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hS'fin : Module.Finite R ↥S')
    (hS'span : Submodule.span K (S' : Set A) = ⊤)
    (hS'comul : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range)
    (hS'anti : ∀ x ∈ S', HopfAlgebra.antipode K (A := A) x ∈ S')
    (hS'counit : ∀ x ∈ S', Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hker : S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)
      = S'.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))
    (himg : S.map ((π : A →ₐ[K] Ā).restrictScalars R) = S'.map ((π : A →ₐ[K] Ā).restrictScalars R)) :
    S = S' :=
  L5D.main hle hSfin hSspan hScomul hSanti hScounit hS'fin hS'span hS'comul hS'anti hS'counit π hπ hker himg

end S_HopfOrder_eq_of_le_of_comap_hopfKer_eq_of_map_eq
end P2MW
export P2MW.S_HopfOrder_eq_of_le_of_comap_hopfKer_eq_of_map_eq (solution)
