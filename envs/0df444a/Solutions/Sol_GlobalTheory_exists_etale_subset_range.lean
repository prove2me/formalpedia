-- Prove2me | solution 1 for GlobalTheory.exists_etale_subset_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:31.706599+00:00
-- url     : https://prove2.me/submissions/bae7ce74-c858-452d-a2e3-55a344fec097

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K]
namespace GlobalTheory
theorem _root_.solution [IsLocalRing B] [Algebra B K] [Algebra (ResidueField B) K]
    [IsScalarTower B (ResidueField B) K] [Algebra.IsSeparable (ResidueField B) K]
    {ι : Type*} [Finite ι] (b : ι → K) :
    ∃ (P : StandardEtalePair B) (ε : P.Ring →ₐ[B] K), ∀ i, b i ∈ Set.range ε := by
  let k := ResidueField B
  let L := IntermediateField.adjoin k (Set.range b)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k θ := Algebra.IsIntegral.isIntegral θ
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap B k)
    (p := minpoly k θ) (map_surjective _ residue_surjective _) (minpoly.monic hi)
  let P : StandardEtalePair B := ⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩
  have key : ∀ g : B[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap B k)) : L) := fun g => by
    rw [← aeval_map_algebraMap k]
    exact aeval_algHom_apply L.val θ _
  have hP : P.HasMap (θ : K) := by
    refine ⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩
    rw [key, ← derivative_map, hμ]
    exact fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero
      (minpoly.aeval k θ) (Subtype.ext h)
  refine ⟨P, P.lift _ hP, fun i => ?_⟩
  have h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h₁
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨g, rfl⟩ := map_surjective (algebraMap B k) residue_surjective g
  refine ⟨aeval P.X g, ?_⟩
  rw [← aeval_algHom_apply, StandardEtalePair.lift_X, key]
  exact congrArg Subtype.val hg
end GlobalTheory
