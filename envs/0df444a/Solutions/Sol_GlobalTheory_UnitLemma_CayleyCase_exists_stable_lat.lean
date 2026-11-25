-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.exists_stable_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:02:47.547129+00:00
-- url     : https://prove2.me/submissions/b0935171-0931-4a18-89ea-747eb2d3282c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O E] [Algebra E A]
    [Algebra O A] [IsScalarTower O E A] [Module.Finite E A] (g : A) (hg : IsIntegral O g) :
    ∃ M : Submodule O A, IsLat O E M ∧ ∀ y ∈ M, g * y ∈ M := by
  set b := Module.finBasis E A
  let M := Subalgebra.toSubmodule (Algebra.adjoin O ({g} : Set A)) * Submodule.span O (Set.range b)
  have hb : ∀ i, b i ∈ M := fun i => by
    have h1 : (1 : A) ∈ Subalgebra.toSubmodule (Algebra.adjoin O ({g} : Set A)) :=
      (Algebra.adjoin O ({g} : Set A)).one_mem
    have h2 : b i ∈ Submodule.span O (Set.range b) := Submodule.subset_span ⟨i, rfl⟩
    have := Submodule.mul_mem_mul h1 h2
    rwa [one_mul] at this
  refine ⟨M, ⟨hg.fg_adjoin_singleton.mul (Submodule.fg_span (Set.finite_range _)), ?_⟩, ?_⟩
  · rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hb i)
  · have : M ≤ M.comap (LinearMap.mulLeft O g) := by
      rw [Submodule.mul_le]
      intro a ha m hm
      show g * (a * m) ∈ M
      rw [← mul_assoc]
      exact Submodule.mul_mem_mul (Subalgebra.mul_mem _ (Algebra.subset_adjoin rfl) ha) hm
    exact fun y hy => this hy
end GlobalTheory.UnitLemma.CayleyCase
