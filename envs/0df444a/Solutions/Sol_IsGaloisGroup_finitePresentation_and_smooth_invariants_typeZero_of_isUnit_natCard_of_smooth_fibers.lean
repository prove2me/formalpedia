-- Prove2me | solution 1 for IsGaloisGroup.finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a4884faf-7d7b-5632-af76-6255fba05114

import Mathlib
import Theorems.Thm_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard
import Theorems.Thm_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed
import Theorems.Thm_Algebra_IsIntegral_ringKrullDim_le_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsGaloisGroup_finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers

set_option autoImplicit false

theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O]
    (A B : Type) [CommRing A] [CommRing B] [IsDomain B]
    [Algebra O A] [Algebra O B] [Algebra A B] [IsScalarTower O A B] [Algebra.FiniteType O B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G O B]
    [IsGaloisGroup G A B] [FaithfulSMul A B]
    (hG : IsUnit ((Nat.card G : ℕ) : O)) :

    Algebra.FiniteType O A ∧ Algebra.FinitePresentation O A ∧ Module.Finite A B ∧

    (IsIntegrallyClosed B → IsIntegrallyClosed A) ∧

    (Module.Flat O B → Module.Flat O A) ∧

    (∀ 𝔞 : Ideal O,
      (∀ a : A, algebraMap A B a ∈ 𝔞.map (algebraMap O B) → a ∈ 𝔞.map (algebraMap O A)) ∧
      (∀ b : B, (∀ g : G, g • b - b ∈ 𝔞.map (algebraMap O B)) → ∃ a : A, algebraMap A B a - b ∈ 𝔞.map (algebraMap O B)) ∧
      (∀ n : ℕ, Ring.KrullDimLE n (B ⧸ 𝔞.map (algebraMap O B)) → Ring.KrullDimLE n (A ⧸ 𝔞.map (algebraMap O A)))) ∧

    (Module.Flat O B →
      (∀ (𝔭 : Ideal O) [𝔭.IsPrime], Algebra.FormallySmooth 𝔭.ResidueField (𝔭.Fiber A)) →
      Algebra.Smooth O A) := by
  classical
  obtain ⟨-, h4, hfinAB, hftA, hflat⟩ :=
    IsGaloisGroup.exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard O A B G hG
  haveI := hftA
  haveI := hfinAB
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  haveI hfp : Algebra.FinitePresentation O A := (Algebra.FinitePresentation.of_finiteType (R := O) (A := A)).mp hftA
  refine ⟨hftA, hfp, hfinAB, ?_, hflat, ?_, ?_⟩
  ·
    intro hIC
    haveI := hIC
    haveI : IsDomain A := hinj.isDomain (algebraMap A B)
    exact IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed G (A := A) (B := B)
  ·
    intro 𝔞
    obtain ⟨h4a, h4b⟩ := h4 𝔞
    refine ⟨h4a, h4b, fun n hn => ?_⟩

    have heq : (𝔞.map (algebraMap O B)).comap (algebraMap A B) = 𝔞.map (algebraMap O A) := by
      apply le_antisymm
      · intro a ha
        exact h4a a (Ideal.mem_comap.mp ha)
      · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
        exact Ideal.le_comap_map
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    have hinj' : Function.Injective
        (algebraMap (A ⧸ (𝔞.map (algebraMap O B)).comap (algebraMap A B)) (B ⧸ 𝔞.map (algebraMap O B))) :=
      Ideal.algebraMap_quotient_injective
    have hle := Algebra.IsIntegral.ringKrullDim_le_of_injective hinj'
    rw [Ring.krullDimLE_iff] at hn ⊢
    have e : (A ⧸ 𝔞.map (algebraMap O A)) ≃+* (A ⧸ (𝔞.map (algebraMap O B)).comap (algebraMap A B)) :=
      Ideal.quotEquivOfEq heq.symm
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact hle.trans hn
  ·
    intro hflatB hfib
    haveI := hflat hflatB
    exact Algebra.Smooth.of_formallySmooth_fiber hfib

end S_IsGaloisGroup_finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
end P2MW
export P2MW.S_IsGaloisGroup_finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers (solution)
