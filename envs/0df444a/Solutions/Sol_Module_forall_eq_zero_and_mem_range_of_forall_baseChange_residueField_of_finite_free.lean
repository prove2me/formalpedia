-- Prove2me | solution 1 for Module.forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c661cc41-6c13-578f-a998-2b32fb54e3e0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free

set_option autoImplicit false

universe u

open TensorProduct

namespace NakAcyclicPen

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem lTensor_liftQ_injective
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : LinearMap.range f ≤ LinearMap.ker g)
    (hS : ∀ z : ResidueField R ⊗[R] B, g.lTensor (ResidueField R) z = 0 →
      z ∈ LinearMap.range (f.lTensor (ResidueField R))) :
    Function.Injective (((LinearMap.range f).liftQ g hgf).lTensor (ResidueField R)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨z, rfl⟩ :=
    LinearMap.lTensor_surjective (ResidueField R) (Submodule.mkQ_surjective (LinearMap.range f)) w
  have h1 : ((LinearMap.range f).liftQ g hgf).lTensor (ResidueField R)
        (((LinearMap.range f).mkQ).lTensor (ResidueField R) z)
      = g.lTensor (ResidueField R) z := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ]
  rw [h1] at hw
  obtain ⟨y, rfl⟩ := hS z hw
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  have hq : (LinearMap.range f).mkQ ∘ₗ f = 0 :=
    LinearMap.ext fun a => (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self f a)
  rw [hq, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem free_coker (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (h0 : Function.Injective ((δ 0).lTensor (ResidueField R)))
    (hS : ∀ (i : ℕ) (z : ResidueField R ⊗[R] K (i + 1)),
      (δ (i + 1)).lTensor (ResidueField R) z = 0 →
        z ∈ LinearMap.range ((δ i).lTensor (ResidueField R)))
    (i : ℕ) : Module.Free R (K (i + 1) ⧸ LinearMap.range (δ i)) := by
  induction i with
  | zero =>
    exact Module.free_of_lTensor_residueField_injective (δ 0) (LinearMap.range (δ 0)).mkQ
      (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range _) h0
  | succ i ih =>
    have hle : LinearMap.range (δ i) ≤ LinearMap.ker (δ (i + 1)) :=
      LinearMap.range_le_ker_iff.mpr (hdd i)
    haveI := ih
    refine Module.free_of_lTensor_residueField_injective
      ((LinearMap.range (δ i)).liftQ (δ (i + 1)) hle) (LinearMap.range (δ (i + 1))).mkQ
      (Submodule.mkQ_surjective _) ?_ (lTensor_liftQ_injective (δ i) (δ (i + 1)) hle (hS i))
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]

theorem main (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (h0 : Function.Injective ((δ 0).lTensor (ResidueField R)))
    (hS : ∀ (i : ℕ) (z : ResidueField R ⊗[R] K (i + 1)),
      (δ (i + 1)).lTensor (ResidueField R) z = 0 →
        z ∈ LinearMap.range ((δ i).lTensor (ResidueField R))) :
    (∀ z : K 0, δ 0 z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : K (i + 1)), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i) := by
  constructor
  · obtain ⟨l', hl'⟩ :=
      (IsLocalRing.split_injective_iff_lTensor_residueField_injective (δ 0)).mpr h0
    intro z hz
    have h := LinearMap.congr_fun hl' z
    rw [LinearMap.comp_apply, hz, map_zero, LinearMap.id_apply] at h
    exact h.symm
  · intro i z hz
    have hle : LinearMap.range (δ i) ≤ LinearMap.ker (δ (i + 1)) :=
      LinearMap.range_le_ker_iff.mpr (hdd i)
    haveI := free_coker K δ hdd h0 hS i
    obtain ⟨l', hl'⟩ :=
      (IsLocalRing.split_injective_iff_lTensor_residueField_injective
        ((LinearMap.range (δ i)).liftQ (δ (i + 1)) hle)).mpr
        (lTensor_liftQ_injective (δ i) (δ (i + 1)) hle (hS i))
    have hinj : Function.Injective ((LinearMap.range (δ i)).liftQ (δ (i + 1)) hle) :=
      Function.LeftInverse.injective (g := l') fun x => LinearMap.congr_fun hl' x
    have hq : (LinearMap.range (δ i)).mkQ z = 0 := hinj (by
      rw [map_zero, Submodule.mkQ_apply, Submodule.liftQ_apply]; exact hz)
    exact (Submodule.Quotient.mk_eq_zero _).mp hq

end NakAcyclicPen

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, n < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (h0 : ∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K 0,
      (δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 → z = 0)
    (hS : ∀ (i : ℕ) (z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K (i + 1)),
      (δ (i + 1)).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
        z ∈ LinearMap.range ((δ i).baseChange (R ⧸ IsLocalRing.maximalIdeal R))) :
    (∀ z : K 0, δ 0 z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : K (i + 1)), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i) := by
  classical
  have h0' : Function.Injective ((δ 0).lTensor (IsLocalRing.ResidueField R)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact h0 z (by rw [LinearMap.baseChange_eq_ltensor]; exact hz)
  have hS' : ∀ (i : ℕ) (z : IsLocalRing.ResidueField R ⊗[R] K (i + 1)),
      (δ (i + 1)).lTensor (IsLocalRing.ResidueField R) z = 0 →
        z ∈ LinearMap.range ((δ i).lTensor (IsLocalRing.ResidueField R)) := by
    intro i z hz
    obtain ⟨y, hy⟩ := hS i z (by rw [LinearMap.baseChange_eq_ltensor]; exact hz)
    rw [LinearMap.baseChange_eq_ltensor] at hy
    exact ⟨y, hy⟩
  exact NakAcyclicPen.main K δ hdd h0' hS'

end S_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free
end P2MW
export P2MW.S_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free (solution)
