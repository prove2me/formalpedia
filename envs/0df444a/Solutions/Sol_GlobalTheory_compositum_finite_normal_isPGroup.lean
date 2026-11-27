-- Prove2me | solution 1 for GlobalTheory.compositum_finite_normal_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:10.510595+00:00
-- url     : https://prove2.me/submissions/85388e46-a2d9-4a5e-af53-36c7dd5a4c4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompositumFiniteNormalIsPGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IntermediateField Polynomial
namespace GlobalTheory
theorem _root_.solution (K K' Ω : Type) [Field K] [Field K'] [Field Ω]
    [Algebra K K'] [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] (l : ℕ)
    (L : IntermediateField K Ω) (hfin : FiniteDimensional K L) (hn : Normal K L)
    (hp : IsPGroup l (L ≃ₐ[K] L)) :
    FiniteDimensional K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      Normal K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      IsPGroup l (IntermediateField.adjoin K' (L : Set Ω) ≃ₐ[K']
        IntermediateField.adjoin K' (L : Set Ω)) := by
  obtain ⟨p, hsp⟩ := Normal.exists_isSplittingField K L
  obtain ⟨hs, hL⟩ := IntermediateField.isSplittingField_iff.mp hsp
  have hsΩ : (p.map (algebraMap K Ω)).Splits := by
    have := hs.map (algebraMap L Ω)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  have hmm : (p.map (algebraMap K K')).map (algebraMap K' Ω) = p.map (algebraMap K Ω) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hroot : (p.map (algebraMap K K')).rootSet Ω = p.rootSet Ω := by
    simp only [Polynomial.rootSet, Polynomial.aroots, hmm]
  have hE : IntermediateField.adjoin K' (L : Set Ω) =
      IntermediateField.adjoin K' ((p.map (algebraMap K K')).rootSet Ω) := by
    rw [hroot]
    conv_lhs => rw [hL]
    exact IntermediateField.adjoin_adjoin_right _ _
  have hsp' : (p.map (algebraMap K K')).IsSplittingField K'
      (IntermediateField.adjoin K' (L : Set Ω)) := by
    rw [hE]
    exact IntermediateField.adjoin_rootSet_isSplittingField (by rw [hmm]; exact hsΩ)
  refine ⟨Polynomial.IsSplittingField.finiteDimensional _ (p.map (algebraMap K K')),
    Normal.of_isSplittingField (p.map (algebraMap K K')), ?_⟩
  set E := IntermediateField.adjoin K' (L : Set Ω) with hEdef
  let i : L →ₐ[K] E :=
    { toFun := fun x => ⟨x, IntermediateField.subset_adjoin K' _ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  letI : Algebra L E := i.toRingHom.toAlgebra
  haveI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  let r : (E ≃ₐ[K'] E) →* (E ≃ₐ[K] E) :=
    { toFun := fun g => g.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let φ : (E ≃ₐ[K'] E) →* (L ≃ₐ[K] L) := (AlgEquiv.restrictNormalHom L).comp r
  refine hp.of_injective φ ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ x : L, g (i x) = i x := by
    intro x
    have h1 := AlgEquiv.restrictNormal_commutes (r g) L x
    have h2 : (r g).restrictNormal L = 1 := hg
    rw [h2] at h1
    exact h1.symm
  have : (g : E →ₐ[K'] E) = AlgHom.id K' E :=
    IntermediateField.adjoin_algHom_ext K' fun x hx => hfix ⟨x, hx⟩
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun this x)
end GlobalTheory
