-- Prove2me | solution 1 for GlobalTheory.card_kernel_quot_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:46.996013+00:00
-- url     : https://prove2.me/submissions/7112949c-88b1-46e3-9dd8-5533ae9267b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardKernelQuotOfBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] (P : Type) [AddCommGroup P]
    [Module O P] (N : Submodule O P) (T : P →ₗ[O] P) (hT : Function.Bijective T)
    (hN : ∀ x ∈ N, T x ∈ N) :
    Nat.card {z : P ⧸ N // ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N} =
      Nat.card (↥N ⧸ (N.map T).comap N.subtype) := by
  let e : P ≃ₗ[O] P := LinearEquiv.ofBijective T hT
  have he1 : ∀ y, T (e.symm y) = y := fun y => e.apply_symm_apply y
  have he2 : ∀ x, e.symm (T x) = x := fun x => e.symm_apply_apply x
  let g : N →ₗ[O] P ⧸ N := N.mkQ ∘ₗ (e.symm : P →ₗ[O] P) ∘ₗ N.subtype
  have hg : ∀ y : N, g y = Submodule.Quotient.mk (e.symm (y : P)) := fun y => rfl
  have hker : LinearMap.ker g = (N.map T).comap N.subtype := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker, hg, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.mem_map]
    constructor
    · intro h
      exact ⟨e.symm y, h, he1 y⟩
    · rintro ⟨x, hx, hxy⟩
      simp only at hxy
      subst hxy
      show e.symm (T x) ∈ N
      rw [he2]
      exact hx
  have hrange : ∀ z : P ⧸ N,
      z ∈ LinearMap.range g ↔ ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N := by
    intro z
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩ x hx
      rw [hg] at hx
      have h1 : x - e.symm y ∈ N := (Submodule.Quotient.eq N).mp hx
      have h2 : T (x - e.symm y) ∈ N := hN _ h1
      rw [map_sub, he1] at h2
      simpa using N.add_mem h2 hy
    · intro h
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
      refine ⟨⟨T x, h x rfl⟩, ?_⟩
      rw [hg]
      simp only
      rw [he2]
  calc Nat.card {z : P ⧸ N // ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N}
      = Nat.card (LinearMap.range g) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun z => (hrange z).symm))
    _ = Nat.card (↥N ⧸ LinearMap.ker g) := Nat.card_congr g.quotKerEquivRange.toEquiv.symm
    _ = Nat.card (↥N ⧸ (N.map T).comap N.subtype) :=
        Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv
end GlobalTheory
