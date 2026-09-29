-- Prove2me | solution 1 for Ideal.eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/505673f5-00c0-510e-bf9a-44d6dfb90585

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq

set_option autoImplicit false

open scoped TensorProduct

namespace GaloisIdealDescent

variable {W W' : Type*} [CommRing W] [CommRing W'] [Algebra W W']
  {Γ : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
  (S : Type*) [CommRing S] [Algebra W S]

private noncomputable def g (γ : Γ) : S ⊗[W] W' →ₐ[S] S ⊗[W] W' :=
  Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom W W' γ)

omit [Fintype Γ] in
private theorem g_tmul (γ : Γ) (a : S) (w : W') : g S γ (a ⊗ₜ[W] w) = a ⊗ₜ[W] (γ • w) := by
  simp [g, Algebra.TensorProduct.map_tmul]

private noncomputable def Tr (m : S ⊗[W] W') : S ⊗[W] W' := ∑ γ : Γ, g S γ m

private theorem Tr_add (m₁ m₂ : S ⊗[W] W') : Tr (Γ := Γ) S (m₁ + m₂) = Tr (Γ := Γ) S m₁ + Tr (Γ := Γ) S m₂ := by
  simp [Tr, map_add, Finset.sum_add_distrib]

private theorem Tr_zero : Tr (Γ := Γ) S (0 : S ⊗[W] W') = 0 := by simp [Tr]

private theorem Tr_tmul (a : S) (w : W') : Tr (Γ := Γ) S (a ⊗ₜ[W] w) = a ⊗ₜ[W] (∑ γ : Γ, γ • w) := by
  simp [Tr, g_tmul, TensorProduct.tmul_sum]

private theorem smul_sum_smul (δ : Γ) (w : W') : δ • (∑ γ : Γ, γ • w) = ∑ γ : Γ, γ • w := by
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft δ) _ _ (fun γ => rfl)

private theorem Tr_mem_range
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') → w' ∈ Set.range (algebraMap W W'))
    (m : S ⊗[W] W') :
    ∃ s : S, Tr (Γ := Γ) S m = (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W') s := by
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [Tr_zero, map_zero]⟩
  | tmul a w =>
    obtain ⟨c, hc⟩ := hinv (∑ γ : Γ, γ • w) (fun δ => smul_sum_smul δ w)
    refine ⟨c • a, ?_⟩
    rw [Tr_tmul, ← hc, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
      Algebra.TensorProduct.includeLeftRingHom_apply]
  | add m₁ m₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁⟩ := h₁
    obtain ⟨s₂, hs₂⟩ := h₂
    exact ⟨s₁ + s₂, by rw [Tr_add, hs₁, hs₂, map_add]⟩

omit [Fintype Γ] in

private theorem g_one (m : S ⊗[W] W') : g S (1 : Γ) m = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a w => rw [g_tmul, one_smul]
  | add m₁ m₂ h₁ h₂ => rw [map_add, h₁, h₂]

private theorem eq_sum_mul_Tr [DecidableEq Γ] {n : ℕ} (x y : Fin n → W')
    (hxy : ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0) (m : S ⊗[W] W') :
    m = ∑ i, ((1 : S) ⊗ₜ[W] x i) * Tr (Γ := Γ) S (((1 : S) ⊗ₜ[W] y i) * m) := by
  have key : ∀ γ : Γ, ∑ i, ((1 : S) ⊗ₜ[W] x i) * g S γ (((1 : S) ⊗ₜ[W] y i) * m) =
      (if γ = 1 then 1 else 0 : S ⊗[W] W') * g S γ m := by
    intro γ
    have h1 : ∀ i, ((1 : S) ⊗ₜ[W] x i) * g S γ (((1 : S) ⊗ₜ[W] y i) * m) =
        ((1 : S) ⊗ₜ[W] (x i * γ • y i)) * g S γ m := by
      intro i
      rw [map_mul, g_tmul, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    simp_rw [h1]
    rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, hxy γ]
    split_ifs with h
    · rw [Algebra.TensorProduct.one_def]
    · rw [TensorProduct.tmul_zero]
  calc m = g S (1 : Γ) m := (g_one S m).symm
    _ = ∑ γ : Γ, (if γ = 1 then 1 else 0 : S ⊗[W] W') * g S γ m := by
        rw [Finset.sum_eq_single (1 : Γ)]
        · simp
        · intro γ _ hγ
          simp [hγ]
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = ∑ γ : Γ, ∑ i, ((1 : S) ⊗ₜ[W] x i) * g S γ (((1 : S) ⊗ₜ[W] y i) * m) := by
        simp_rw [key]
    _ = ∑ i, ((1 : S) ⊗ₜ[W] x i) * Tr (Γ := Γ) S (((1 : S) ⊗ₜ[W] y i) * m) := by
        rw [Finset.sum_comm]
        simp_rw [Tr, Finset.mul_sum]

end GaloisIdealDescent

open GaloisIdealDescent in
theorem solution
    {W W' : Type*} [CommRing W] [CommRing W'] [Algebra W W']
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') → w' ∈ Set.range (algebraMap W W'))
    {n : ℕ} (x y : Fin n → W') (hxy : ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0)
    (S : Type*) [CommRing S] [Algebra W S]
    (J' : Ideal (S ⊗[W] W'))
    (hstab : ∀ γ : Γ, J'.map (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom W W' γ)) = J') :
    J' = (J'.comap (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W')).map
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W') := by
  classical
  refine le_antisymm ?_ Ideal.map_comap_le
  intro m hm

  have hstab' : ∀ γ : Γ, ∀ m' ∈ J', g S γ m' ∈ J' := by
    intro γ m' hm'
    have := Ideal.mem_map_of_mem (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom W W' γ)) hm'
    rwa [hstab γ] at this
  rw [eq_sum_mul_Tr S x y hxy m]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
  have hJ : Tr (Γ := Γ) S (((1 : S) ⊗ₜ[W] y i) * m) ∈ J' :=
    Ideal.sum_mem _ fun γ _ => hstab' γ _ (J'.mul_mem_left _ hm)
  obtain ⟨s, hs⟩ := Tr_mem_range S hinv (((1 : S) ⊗ₜ[W] y i) * m)
  rw [hs] at hJ ⊢
  exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hJ)

end S_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq
end P2MW
export P2MW.S_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq (solution)
