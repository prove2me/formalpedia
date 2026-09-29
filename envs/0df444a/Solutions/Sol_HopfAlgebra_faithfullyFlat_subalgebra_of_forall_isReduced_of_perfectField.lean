-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a8482e2a-a62e-58cd-87c0-717a51bc60a3

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem
import Theorems.Thm_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit
import Theorems.Thm_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField

set_option maxHeartbeats 800000

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace S17Td

end S17Td

namespace S17Ta

universe u₁ u₂ u₃

section Descent

variable (R : Type u₁) [CommRing R] (S : Type u₂) [CommRing S] [Algebra R S]
variable (M : Type u₃) [AddCommGroup M] [Module R M]

noncomputable def cancelIso (N : Type*) [AddCommGroup N] [Module R N] :
    (S ⊗[R] M) ⊗[S] (S ⊗[R] N) ≃ₗ[S] S ⊗[R] (M ⊗[R] N) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (S ⊗[R] M) N).trans
    (TensorProduct.AlgebraTensorModule.assoc R R S S M N)

theorem cancelIso_tmul {N : Type*} [AddCommGroup N] [Module R N] (s s' : S) (m : M) (n : N) :
    cancelIso R S M N ((s ⊗ₜ[R] m) ⊗ₜ[S] (s' ⊗ₜ[R] n)) = (s' * s) ⊗ₜ[R] (m ⊗ₜ[R] n) := by
  simp [cancelIso, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.assoc_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem cancelIso_naturality {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') (z : (S ⊗[R] M) ⊗[S] (S ⊗[R] N)) :
    cancelIso R S M N' (((f.baseChange S).lTensor (S ⊗[R] M)) z)
      = (f.lTensor M).lTensor S (cancelIso R S M N z) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      induction x with
      | zero => simp
      | add x₁ x₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
      | tmul s m =>
          induction y with
          | zero => simp
          | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
          | tmul s' n =>
              rw [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul, cancelIso_tmul, cancelIso_tmul,
                LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]

theorem faithfullyFlat_of_faithfullyFlat_baseChange [Module.FaithfullyFlat R S]
    [Module.FaithfullyFlat S (S ⊗[R] M)] : Module.FaithfullyFlat R M := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  constructor
  ·
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ f hf
    rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective R S]
    have hfS : Function.Injective (f.baseChange S) := Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hg : Function.Injective ((f.baseChange S).lTensor (S ⊗[R] M)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hfS
    have hcomp : ((f.lTensor M).lTensor S : S ⊗[R] (M ⊗[R] N) → S ⊗[R] (M ⊗[R] N'))
        = (cancelIso R S M N') ∘ ((f.baseChange S).lTensor (S ⊗[R] M)) ∘ (cancelIso R S M N).symm := by
      funext z
      simp only [Function.comp_apply]
      rw [cancelIso_naturality, LinearEquiv.apply_symm_apply]
    rw [hcomp]
    exact (cancelIso R S M N').injective.comp (hg.comp (cancelIso R S M N).symm.injective)
  ·
    intro I hI hIM
    let J : Ideal S := I.map (algebraMap R S)
    have hJ : J ≠ ⊤ := by
      intro hJ
      have h1 := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal R S).mp inferInstance).2 I hI
      apply h1
      have hJ' : Ideal.map (algebraMap R S) I = ⊤ := hJ
      rw [Ideal.smul_top_eq_map, hJ']
      rfl
    have h2 := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal S (S ⊗[R] M)).mp inferInstance).2 J hJ
    apply h2

    have hone : ∀ m : M, (1 : S) ⊗ₜ[R] m ∈ J • (⊤ : Submodule S (S ⊗[R] M)) := by
      intro m
      have hm : m ∈ I • (⊤ : Submodule R M) := by rw [hIM]; exact Submodule.mem_top
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro i hi n _
        have : (1 : S) ⊗ₜ[R] (i • n) = (algebraMap R S i) • ((1 : S) ⊗ₜ[R] n) := by
          rw [TensorProduct.tmul_smul, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top
      · intro x y hx hy
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hx hy
    rw [eq_top_iff]
    rintro z -
    induction z with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul s m =>
        have : s ⊗ₜ[R] m = s • ((1 : S) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ s (hone m)

end Descent

end S17Ta

namespace S17Td

theorem codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => RingHom.FaithfullyFlat (R := R) (S := S))
      (fun {R S} [CommRing R] [CommRing S] => RingHom.FaithfullyFlat (R := R) (S := S)) := by
  refine RingHom.CodescendsAlong.mk _ RingHom.FaithfullyFlat.respectsIso ?_
  intro R S T _ _ _ _ _ hRS hST
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hRS hST ⊢
  exact S17Ta.faithfullyFlat_of_faithfullyFlat_baseChange R S T

end S17Td

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open S17Td in
theorem solution
    {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (hred : ∀ K' : Subalgebra k H,
      (∀ x ∈ K', Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) →
      (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') → K'.FG → IsReduced ↥K' →
      Module.FaithfullyFlat ↥K' H)
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) (hfg : K.FG) :
    Module.FaithfullyFlat ↥K H := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨r, K', hK'K, hK'fg, hK'red, hK'set, hΔ', hS'⟩ :=
    HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced p K hΔ hS hfg
  haveI : IsReduced ↥K' := hK'red
  haveI hffK' : Module.FaithfullyFlat ↥K' H := hred K' hΔ' hS' hK'fg hK'red
  have hpowK' : ∀ x ∈ K, x ^ p ^ r ∈ K' := fun x hx => by
    show x ^ p ^ r ∈ (K' : Set H)
    rw [hK'set]; exact ⟨x, hx, rfl⟩

  letI : Algebra ↥K' ↥K := (Subalgebra.inclusion hK'K).toAlgebra
  haveI : IsScalarTower ↥K' ↥K H := IsScalarTower.of_algebraMap_eq (fun x => rfl)

  obtain ⟨Hb, _, _, πc, hπsurj, hker, hcounit, hanti, hsub⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem K' hΔ' hS'
  obtain ⟨hΔb, hSb⟩ := hsub K hΔ hS
  let π : H →ₐ[k] Hb := (πc : H →ₐ[k] Hb)
  have hπsurj' : Function.Surjective π := hπsurj
  have hkerπ : RingHom.ker π = Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0} := hker

  have hnil : IsNilpotent (RingHom.ker ((Bialgebra.counitAlgHom k Hb).comp (K.map π).val)) := by
    have hKfg : (K.map π).FG := hfg.map π
    haveI hKft : Algebra.FiniteType k ↥(K.map π) := (Subalgebra.fg_iff_finiteType _).mp hKfg
    haveI : IsNoetherianRing ↥(K.map π) := Algebra.FiniteType.isNoetherianRing k ↥(K.map π)
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr ?_
    intro y hy
    rw [RingHom.mem_ker] at hy
    have hy' : Coalgebra.counit (R := k) (y : Hb) = 0 := hy
    obtain ⟨x, hxK, hxy⟩ := Subalgebra.mem_map.mp y.2
    have hcx : Coalgebra.counit (R := k) x = 0 := by
      rw [← hcounit x]
      change Coalgebra.counit (R := k) (π x) = 0
      rw [hxy]
      exact hy'
    have hmem : x ^ p ^ r ∈ RingHom.ker π := by
      rw [hkerπ]
      refine Ideal.subset_span ⟨hpowK' x hxK, ?_⟩
      change Bialgebra.counitAlgHom k H (x ^ p ^ r) = 0
      rw [map_pow, show Bialgebra.counitAlgHom k H x = Coalgebra.counit x from rfl, hcx,
        zero_pow (pow_ne_zero _ hp.ne_zero)]
    rw [mem_nilradical]
    refine ⟨p ^ r, Subtype.ext ?_⟩
    rw [Subalgebra.coe_pow, Subalgebra.coe_zero, ← hxy, ← map_pow]
    exact RingHom.mem_ker.mp hmem

  haveI hfree : Module.Free ↥(K.map π) Hb := HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit (K.map π) hΔb hSb hnil

  have hsq := HopfAlgebra.faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span K' K hΔ' hΔ Hb π hπsurj' hkerπ

  haveI : Module.FaithfullyFlat ↥K (↥K ⊗[↥K'] H) := Module.FaithfullyFlat.instTensorProduct ↥K' H ↥K
  have hQS : (algebraMap ↥K (↥K ⊗[↥K'] H)).FaithfullyFlat := (RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance

  let e : (↥K ⊗[↥K'] H) ⊗[↥K] H ≃ₐ[↥K] H ⊗[↥K'] H :=
    (Algebra.TensorProduct.comm ↥K (↥K ⊗[↥K'] H) H).trans (Algebra.TensorProduct.cancelBaseChange ↥K' ↥K ↥K H H)
  have he : ∀ s : ↥K ⊗[↥K'] H, e (s ⊗ₜ[↥K] (1 : H))
      = Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H) s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | tmul a h =>
        show Algebra.TensorProduct.cancelBaseChange ↥K' ↥K ↥K H H
          (Algebra.TensorProduct.comm ↥K (↥K ⊗[↥K'] H) H ((a ⊗ₜ[↥K'] h) ⊗ₜ[↥K] (1 : H))) = _
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply, Algebra.smul_def, mul_one]
    | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
  refine (RingHom.faithfullyFlat_algebraMap_iff).mp
    (RingHom.CodescendsAlong.algebraMap_tensorProduct _ ↥K (↥K ⊗[↥K'] H) H codescendsAlong_faithfullyFlat hQS ?_)

  have h1 := @(RingHom.FaithfullyFlat.respectsIso).1 (↥K ⊗[↥K'] H) (H ⊗[↥K'] H) ((↥K ⊗[↥K'] H) ⊗[↥K] H)
    _ _ _ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H)).toRingHom
    e.symm.toRingEquiv hsq
  have hEq : e.symm.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H)).toRingHom
      = algebraMap (↥K ⊗[↥K'] H) ((↥K ⊗[↥K'] H) ⊗[↥K] H) := by
    apply RingHom.ext
    intro s
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show e.symm (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H) s) = s ⊗ₜ[↥K] 1
    rw [← he, AlgEquiv.symm_apply_apply]
  rw [hEq] at h1
  exact h1

end S_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField (solution)
