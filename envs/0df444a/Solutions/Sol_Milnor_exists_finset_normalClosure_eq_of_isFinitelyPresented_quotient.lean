-- Prove2me | solution 1 for Milnor.exists_finset_normalClosure_eq_of_isFinitelyPresented_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-19T22:37:00.55568+00:00
-- url     : https://prove2.me/submissions/0400aa87-748a-471e-b862-e08ec706b58e

import Mathlib

namespace Milnor
namespace Lib

open Function Subgroup

/-- Freeness: any homomorphism out of a free group lifts along a surjection. -/
theorem exists_lift_of_surjective {α : Type*} {G H : Type*} [Group G] [Group H]
    {f : G →* H} (hf : Function.Surjective f) (g : FreeGroup α →* H) :
    ∃ θ : FreeGroup α →* G, f.comp θ = g := by
  refine ⟨FreeGroup.lift (fun a => Function.surjInv hf (g (FreeGroup.of a))), ?_⟩
  apply FreeGroup.ext_hom
  intro a
  simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  exact Function.surjInv_eq hf _

/-- Tietze / change of generators (Milnor's citation of Kurosh): the kernel of *any* surjection
from a finite-rank free group onto a finitely presented group is finitely normally generated. -/
theorem ker_isFinitelyNormallyGenerated_of_isFinitelyPresented {C : Type*} [Group C]
    [Group.IsFinitelyPresented C] {n : ℕ} (χ : FreeGroup (Fin n) →* C)
    (hχ : Function.Surjective χ) : χ.ker.IsFinitelyNormallyGenerated := by
  obtain ⟨m, ψ, hψ, R, hRfin, hR⟩ := ‹Group.IsFinitelyPresented C›.out
  obtain ⟨θ, hθ⟩ := exists_lift_of_surjective hψ χ
  obtain ⟨σ, hσ⟩ := exists_lift_of_surjective hχ ψ
  have hθapp : ∀ w, ψ (θ w) = χ w := fun w => DFunLike.congr_fun hθ w
  have hσapp : ∀ w, χ (σ w) = ψ w := fun w => DFunLike.congr_fun hσ w
  set S : Set (FreeGroup (Fin n)) :=
    σ '' R ∪ Set.range (fun i : Fin n => (FreeGroup.of i)⁻¹ * σ (θ (FreeGroup.of i))) with hSdef
  refine ⟨S, (hRfin.image _).union (Set.finite_range _), ?_⟩
  set N : Subgroup (FreeGroup (Fin n)) := normalClosure S with hNdef
  apply le_antisymm
  · -- `normalClosure S ≤ χ.ker`
    apply normalClosure_le_normal
    rintro x (⟨r, hr, rfl⟩ | ⟨i, rfl⟩)
    · have hrk : r ∈ ψ.ker := by rw [← hR]; exact subset_normalClosure hr
      show χ (σ r) = 1
      rw [hσapp]
      exact hrk
    · show χ ((FreeGroup.of i)⁻¹ * σ (θ (FreeGroup.of i))) = 1
      rw [map_mul, map_inv, hσapp, hθapp, inv_mul_cancel]
  · -- `χ.ker ≤ normalClosure S`
    have key : (QuotientGroup.mk' N).comp (σ.comp θ) = QuotientGroup.mk' N := by
      apply FreeGroup.ext_hom
      intro i
      have hmem : (FreeGroup.of i)⁻¹ * σ (θ (FreeGroup.of i)) ∈ N :=
        subset_normalClosure (Or.inr ⟨i, rfl⟩)
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [eq_comm, ← inv_mul_eq_one, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff _).2 hmem
    intro w hw
    have hθw : θ w ∈ ψ.ker := by
      show ψ (θ w) = 1
      rw [hθapp]
      exact hw
    have hmapped : σ (θ w) ∈ N := by
      have h1 : σ (θ w) ∈ (normalClosure R).map σ := ⟨θ w, by rw [hR]; exact hθw, rfl⟩
      have h2 : σ (θ w) ∈ normalClosure (σ '' R) := Subgroup.map_normalClosure_le R σ h1
      exact normalClosure_mono (fun x hx => Or.inl hx) h2
    have hcong : (QuotientGroup.mk' N) (σ (θ w)) = (QuotientGroup.mk' N) w :=
      DFunLike.congr_fun key w
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).2 hmapped] at hcong
    exact (QuotientGroup.eq_one_iff w).1 hcong.symm

/-- Milnor, Lemma 2 (p. 448): if `B` is finitely generated and `B ⧸ A` is finitely presented,
then the normal subgroup `A` is the normal closure of a finite subset of itself. -/
theorem exists_finset_normalClosure_eq_of_isFinitelyPresented_quotient' {B : Type*} [Group B]
    [Group.FG B] (A : Subgroup B) [A.Normal] [IsMulCommutative A]
    [Group.IsFinitelyPresented (B ⧸ A)] :
    ∃ T : Finset B, (T : Set B) ⊆ A ∧ Subgroup.normalClosure (T : Set B) = A := by
  obtain ⟨α, hα, φ₀, hφ₀⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp ‹Group.FG B›
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  set φ : FreeGroup (Fin n) →* B :=
    φ₀.comp (FreeGroup.freeGroupCongr e).symm.toMonoidHom with hφdef
  have hφ : Function.Surjective φ := hφ₀.comp (FreeGroup.freeGroupCongr e).symm.surjective
  set χ : FreeGroup (Fin n) →* B ⧸ A := (QuotientGroup.mk' A).comp φ with hχdef
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective A).comp hφ
  have hker : χ.ker = A.comap φ := by
    rw [hχdef, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hfng : (A.comap φ).IsFinitelyNormallyGenerated := by
    rw [← hker]
    exact ker_isFinitelyNormallyGenerated_of_isFinitelyPresented χ hχ
  have hA : A.IsFinitelyNormallyGenerated := by
    have h := hfng.map hφ
    rwa [Subgroup.map_comap_eq_self_of_surjective hφ] at h
  obtain ⟨S, hSfin, hS⟩ := hA
  refine ⟨hSfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    intro x hx
    have : x ∈ normalClosure S := subset_normalClosure hx
    rw [hS] at this
    exact this
  · rw [Set.Finite.coe_toFinset]
    exact hS

end Lib
end Milnor

open Milnor

theorem solution {B : Type*} [Group B]
    [Group.FG B] (A : Subgroup B) [A.Normal] [IsMulCommutative A]
    [Group.IsFinitelyPresented (B ⧸ A)] :
    ∃ T : Finset B, (T : Set B) ⊆ A ∧ Subgroup.normalClosure (T : Set B) = A :=
  Milnor.Lib.exists_finset_normalClosure_eq_of_isFinitelyPresented_quotient' A
