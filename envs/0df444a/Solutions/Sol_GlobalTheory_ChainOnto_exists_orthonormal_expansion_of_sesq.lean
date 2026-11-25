-- Prove2me | solution 1 for GlobalTheory.ChainOnto.exists_orthonormal_expansion_of_sesq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:40.228906+00:00
-- url     : https://prove2.me/submissions/d0182f5a-e4e8-4c4d-bb4c-86ea758a03a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemRangeAdjointOfMemSpanEvaluationValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
open GlobalTheory GlobalTheory.ChainOnto
namespace GlobalTheory.ChainOnto
theorem _root_.solution {C : Type} [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
    (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ip x y = conj (ip y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re) :
    ∃ (n : ℕ) (b : Fin n → C), (∀ i j, ip (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x, x = ∑ i, ip x (b i) • b i := by
  let cd : InnerProductSpace.Core ℂ C :=
    { inner := fun x y => ip y x
      conj_inner_symm := fun x y => by simp [hsym y x]
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        change ip x x = 0 at hx
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup C := @InnerProductSpace.Core.toNormedAddCommGroup ℂ C _ _ _ cd
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ C
  refine ⟨_, b, fun i j => ?_, fun x => ?_⟩
  · have h := orthonormal_iff_ite.mp b.orthonormal j i
    have e : ⟪b j, b i⟫_ℂ = ip (b i) (b j) := rfl
    rw [e] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · have h := b.sum_repr' x
    exact h.symm
end GlobalTheory.ChainOnto
