-- Prove2me | solution 1 for GlobalTheory.extend_alg_hom_adjoin_integral_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:48:55.831932+00:00
-- url     : https://prove2.me/submissions/b36e472d-0737-441e-b363-bd1a35859f23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ →
    ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 →
    ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω,
      ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))),
        ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  intro k F Ω _ _ _ _ _ R _ θ hθ ev r hr
  let S : Subalgebra R F := Algebra.adjoin R {θ}
  let e : AdjoinRoot (minpoly R θ) ≃ₐ[R] S := minpoly.equivAdjoin hθ
  let φ : S →+* Ω := (AdjoinRoot.lift (ev : R →+* Ω) r hr).comp (e.symm : S →+* AdjoinRoot (minpoly R θ))
  have hφ : ∀ (x : F) (hx : x ∈ R) (hxS : x ∈ S), φ ⟨x, hxS⟩ = ev ⟨x, hx⟩ := by
    intro x hx hxS
    have h1 : (⟨x, hxS⟩ : S) = algebraMap R S ⟨x, hx⟩ := rfl
    simp only [φ, RingHom.comp_apply, h1]
    rw [show (e.symm : S →+* AdjoinRoot (minpoly R θ)) (algebraMap R S ⟨x, hx⟩)
        = AdjoinRoot.of (minpoly R θ) ⟨x, hx⟩ from e.symm.commutes _]
    exact AdjoinRoot.lift_of hr
  have hle : Algebra.adjoin k (insert θ (R : Set F)) ≤ S.restrictScalars k := by
    rw [Algebra.adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨?_, ?_⟩
    · show θ ∈ S
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · intro y hy
      show y ∈ S
      exact S.algebraMap_mem (⟨y, hy⟩ : R)
  have hmem : ∀ z : Algebra.adjoin k (insert θ (R : Set F)), (z : F) ∈ S := fun z => hle z.2
  let ψ₀ : Algebra.adjoin k (insert θ (R : Set F)) →+* Ω :=
    { toFun := fun z => φ ⟨z.1, hmem z⟩
      map_one' := φ.map_one
      map_mul' := fun a b => φ.map_mul ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩
      map_zero' := φ.map_zero
      map_add' := fun a b => φ.map_add ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩ }
  refine ⟨{ ψ₀ with commutes' := fun c => ?_ }, fun x hx hx' => hφ x hx (hle hx')⟩
  exact (hφ (algebraMap k F c) (R.algebraMap_mem c) _).trans (ev.commutes c)
end GlobalTheory
