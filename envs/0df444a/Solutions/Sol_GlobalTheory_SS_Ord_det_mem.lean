-- Prove2me | solution 1 for GlobalTheory.SS.Ord.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:19.072567+00:00
-- url     : https://prove2.me/submissions/2abfafc7-148d-4549-ad07-4fe9519e9e04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_multilinear_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
namespace GlobalTheory.SS.Ord
theorem _root_.solution {B S L I : Type} [CommRing B] [CommRing S] [CommRing L] [Fintype I] [DecidableEq I]
    (ρ : B →+* S) (φ : S →+* L) (δ : I → L →+ L) (hδ : ∀ i a b, δ i (a * b) = a * δ i b + b * δ i a)
    (hloc : ∀ x : S, ∃ (b c : B), IsUnit (ρ c) ∧ x * ρ c = ρ b)
    (N : AddSubgroup L) (hN : ∀ s : S, ∀ x ∈ N, φ s * x ∈ N)
    (h : ∀ t : I → B, (Matrix.of fun i j => δ i (φ (ρ (t j)))).det ∈ N) (t : I → S) :
    (Matrix.of fun i j => δ i (φ (t j))).det ∈ N := by
  letI := φ.toAlgebra
  let N' : Submodule S L := { N with smul_mem' := fun s x hx => hN s x hx }
  let f : MultilinearMap S (fun _ : I => I → L) L :=
    (Matrix.detRowAlternating (n := I) (R := L)).toMultilinearMap.restrictScalars S
  have hf : ∀ v : I → I → L, f v = (Matrix.of fun i j => v j i).det := fun v =>
    (Matrix.det_transpose (Matrix.of v)).symm
  let col : S → I → L := fun x i => δ i (φ x)
  have := multilinear_mem f (Set.range (col ∘ ρ)) N' (fun v hv => by
    choose t ht using hv
    have := h t
    rw [hf]
    simp only [← ht]
    exact this) (fun j => col (t j)) (fun j => by
      obtain ⟨b, c, ⟨u, hu⟩, e⟩ := hloc (t j)
      have : col (t j) = (u⁻¹ : Sˣ).val • (col (ρ b) - t j • col (ρ c)) := by
        funext i
        have e1 : φ (u⁻¹ : Sˣ).val * φ (ρ c) = 1 := by rw [← map_mul, ← hu]; simp
        show δ i (φ (t j)) = φ (u⁻¹ : Sˣ).val * (δ i (φ (ρ b)) - φ (t j) * δ i (φ (ρ c)))
        rw [← e, map_mul, hδ]
        linear_combination (-δ i (φ (t j))) * e1
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨b, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))))
  rw [hf] at this
  exact this
end GlobalTheory.SS.Ord
