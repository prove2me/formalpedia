-- Prove2me | solution 1 for Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f5359ecb-2578-5223-81c0-45cba25bb375

import Mathlib
import Theorems.Thm_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

namespace DualEigen

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

abbrev alg {ι : Type*} (T : ι → Module.End K V) : Subalgebra K (Module.End K V) :=
  Algebra.adjoin K (Set.range T)

theorem T_mem {ι : Type*} (T : ι → Module.End K V) (i : ι) : T i ∈ alg T :=
  Algebra.subset_adjoin ⟨i, rfl⟩

theorem dualMap_eq_smul_of_mem {ι : Type*} (T : ι → Module.End K V) (μ : ι → K)
    (φ : Module.Dual K V) (hφ : ∀ i, (T i).dualMap φ = μ i • φ) (v₀ : V) (hv₀ : φ v₀ = 1) :
    ∀ a ∈ alg T, a.dualMap φ = (φ (a v₀)) • φ := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    rw [hφ i]
    congr 1
    have := congrArg (fun ψ : Module.Dual K V => ψ v₀) (hφ i)
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul, hv₀, mul_one] at this
    exact this.symm
  | algebraMap c =>
    ext v
    simp [Algebra.algebraMap_eq_smul_one, LinearMap.dualMap_apply, hv₀]
  | add a b _ _ ha hb =>
    have hadd : (a + b).dualMap φ = a.dualMap φ + b.dualMap φ := by
      ext v; simp [LinearMap.dualMap_apply, map_add]
    rw [hadd, LinearMap.add_apply, map_add, add_smul, ← ha, ← hb]
  | mul a b _ _ ha hb =>

    have hcomp : (a * b).dualMap φ = b.dualMap (a.dualMap φ) := by
      ext v; rfl
    rw [hcomp, ha, LinearMap.map_smul, hb, smul_smul, Module.End.mul_apply]
    congr 1
    have := congrArg (fun ψ : Module.Dual K V => ψ (b v₀)) ha
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul] at this
    rw [this, mul_comm]

theorem exists_of_dual {ι : Type*} [FiniteDimensional K V] (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j))
    (μ : ι → K) (φ : Module.Dual K V) (hφ0 : φ ≠ 0) (hφ : ∀ i, (T i).dualMap φ = μ i • φ) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, T i v = μ i • v := by
  classical

  obtain ⟨v₁, hv₁⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (LinearMap.ext h)
  set v₀ : V := (φ v₁)⁻¹ • v₁ with hv₀def
  have hv₀ : φ v₀ = 1 := by rw [hv₀def, map_smul, smul_eq_mul, inv_mul_cancel₀ hv₁]
  have key := dualMap_eq_smul_of_mem T μ φ hφ v₀ hv₀

  let A : Subalgebra K (Module.End K V) := alg T
  have hc : ∀ x ∈ Set.range T, ∀ y ∈ Set.range T, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hT i j).eq
  letI : CommRing A := Algebra.adjoinCommRingOfComm K hc
  have hmulcomm : ∀ a b : A, ((a * b : A) : Module.End K V) = ((b * a : A) : Module.End K V) := fun a b =>
    congrArg Subtype.val (mul_comm a b)
  letI : Module A V := Module.compHom V (A.val.toRingHom)
  have hsmul : ∀ (a : A) (v : V), a • v = (a : Module.End K V) v := fun _ _ => rfl
  have hst : IsScalarTower K A V := ⟨fun c a v => by
    rw [hsmul, hsmul, Subalgebra.coe_smul, LinearMap.smul_apply]⟩
  have hfs : FaithfulSMul A V := ⟨fun {a b} h => by
    apply Subtype.ext
    ext v
    have := h v
    rwa [hsmul, hsmul] at this⟩

  let χ : A →ₐ[K] K :=
    { toFun := fun a => φ ((a : Module.End K V) v₀)
      map_one' := by simp [hv₀]
      map_mul' := fun a b => by
        have hb := key b b.2
        have := congrArg (fun ψ : Module.Dual K V => ψ ((a : Module.End K V) v₀)) hb
        simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul] at this

        have hab : ((a * b : A) : Module.End K V) v₀ = (b : Module.End K V) ((a : Module.End K V) v₀) := by
          rw [hmulcomm a b]
          rfl
        rw [hab, this, mul_comm]
      map_zero' := by simp
      map_add' := fun a b => by simp
      commutes' := fun c => by
        simp [Algebra.algebraMap_eq_smul_one, hv₀] }
  obtain ⟨v, hv0, hv⟩ := @Module.exists_ne_zero_forall_smul_eq_smul_of_algHom K A V _ _ (Subalgebra.algebra A) _ _ _ hst _ hfs χ
  refine ⟨v, hv0, fun i => ?_⟩
  have h := hv ⟨T i, T_mem T i⟩

  have h' : (T i) v = (φ ((T i) v₀)) • v := h
  have hχ : φ ((T i) v₀) = μ i := by
    have := congrArg (fun ψ : Module.Dual K V => ψ v₀) (hφ i)
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul, hv₀, mul_one] at this
    exact this
  rw [hχ] at h'
  exact h'

end DualEigen

open DualEigen in
theorem solution
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j)) (μ : ι → K) :
    (∃ v : V, v ≠ 0 ∧ ∀ i, T i v = μ i • v) ↔
      ∃ φ : Module.Dual K V, φ ≠ 0 ∧ ∀ i, (T i).dualMap φ = μ i • φ := by
  constructor
  · rintro ⟨v, hv0, hv⟩

    have hT' : ∀ i j, Commute ((T i).dualMap) ((T j).dualMap) := fun i j => by
      show (T i).dualMap * (T j).dualMap = (T j).dualMap * (T i).dualMap
      apply LinearMap.ext
      intro ψ
      apply LinearMap.ext
      intro w
      show ψ (T j (T i w)) = ψ (T i (T j w))
      rw [← Module.End.mul_apply, (hT j i).eq, Module.End.mul_apply]
    have hev0 : Module.Dual.eval K V v ≠ 0 := fun h => hv0 ((Module.eval_apply_eq_zero_iff K v).mp h)
    have hev : ∀ i, ((T i).dualMap).dualMap (Module.Dual.eval K V v) = μ i • Module.Dual.eval K V v := by
      intro i
      ext ψ
      simp [LinearMap.dualMap_apply, hv i]
    obtain ⟨φ, hφ0, hφ⟩ := exists_of_dual (V := Module.Dual K V) (fun i => (T i).dualMap) hT' μ
      (Module.Dual.eval K V v) hev0 hev
    exact ⟨φ, hφ0, hφ⟩
  · rintro ⟨φ, hφ0, hφ⟩
    exact exists_of_dual T hT μ φ hφ0 hφ

end S_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul
end P2MW
export P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul (solution)
