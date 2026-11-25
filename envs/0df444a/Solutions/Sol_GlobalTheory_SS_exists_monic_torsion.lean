-- Prove2me | solution 1 for GlobalTheory.SS.exists_monic_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:20:42.837896+00:00
-- url     : https://prove2.me/submissions/94fb524f-234f-4a96-ba53-b0d7f26db3ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVectorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPolyNormSqRoots
import Theorems.Thm_GlobalTheory_SS_exists_surj_of_torsion
import Theorems.Thm_GlobalTheory_SS_aeval_intertwine
import Theorems.Thm_GlobalTheory_SS_exists_monic_of_surj
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
open Polynomial
namespace GlobalTheory.SS
theorem _root_.solution {M : Type} [AddCommGroup M] (l : ℕ) (hf : ∀ n : ℕ, Finite {x : M // l ^ n • x = 0})
    (T : Module.End ℤ M) : ∃ r : ℕ, ∀ n : ℕ, ∃ χ : ℤ[X], χ.Monic ∧ χ.natDegree = r ∧
      ∀ x : M, l ^ n • x = 0 → aeval T χ x = 0 := by
  refine ⟨Nat.card {x : M // l ^ 1 • x = 0}, fun n => ?_⟩
  let N : Submodule ℤ M := LinearMap.ker (l ^ n • LinearMap.id)
  have hN : ∀ x : M, x ∈ N ↔ l ^ n • x = 0 := fun x => Iff.rfl
  have : Finite N := by
    have := hf n
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight fun x => (hN x).symm)
  have hT : ∀ x ∈ N, T x ∈ N := fun x hx => by
    rw [hN] at hx ⊢
    rw [← map_nsmul, hx, map_zero]
  have := hf 1
  obtain ⟨π, hπ⟩ := exists_surj_of_torsion (N := N) l n (Nat.card {x : M // l ^ 1 • x = 0})
    (fun x => Subtype.ext ((hN _).1 x.2))
    (Nat.card_le_card_of_injective (fun x => (⟨x.1.1, by rw [pow_one]; exact congrArg Subtype.val x.2⟩ :
      {x : M // l ^ 1 • x = 0})) fun x y h => Subtype.ext (Subtype.ext (by simpa using h)))
  obtain ⟨χ, h1, h2, h3⟩ := exists_monic_of_surj _ π hπ (T.restrict hT)
  refine ⟨χ, h1, h2, fun x hx => ?_⟩
  have h := aeval_intertwine N.subtype (T.restrict hT) T (fun _ => rfl) χ ⟨x, (hN x).2 hx⟩
  rw [h3] at h
  exact h
end GlobalTheory.SS
