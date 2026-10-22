-- Prove2me | solution 1 for MazurTransfer.original_literal_nineteen_roots_cyclic_classification
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-22T01:17:11.225822+00:00
-- url     : https://prove2.me/submissions/c8f0a3c1-9700-4197-8d33-c995e6aeb234

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the same given literal-root Hopf model and original chosen Cartier dual cyclic equivalence, with the original cyclic group-algebra classification and its exact evaluation identity.
Named downstream consumer: normalization of the same selected integral pi quotient arithmetic labels and norm Kummer unit conditions at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalLiteralNineteenRootsCartierDualPointsData20261020
import Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_hopf_classification
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.LiteralNineteenRootsCartierDualPoints
local notation "K" => AlgebraicClosure ℚ
local notation "R" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instFactPrimeOfNatNat_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsCartierDualPoints
namespace MazurTransfer.OriginalLiteralNineteenRootsCyclicClassificationBoundary20261020
end MazurTransfer.OriginalLiteralNineteenRootsCyclicClassificationBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: cyclic order-nineteen group algebra form of the SAME
literal-root Hopf model, retaining the Cartier-dual evaluation identity.
Named downstream consumer: point-label normalization and actual selected
pi quotient Kummer unit conditions at nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalLiteralNineteenRootsCyclicClassificationProof20261020
open NineteenRootsGaloisRepresentation LiteralNineteenRootsCartierDualPoints
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K
variable (H : Type) [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
variable (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K))
variable (he_add : ∀ f g, e (f * g) = e f + e g)
variable (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)),
  (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f))

include e he_add he_act in
theorem exists_cyclic_bialgebra_equivalence :
    ∃ φ : H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 19)),
      ∀ (k : Multiplicative (ZMod 19)) (θ : CartierDual R H),
        algebraMap R K (θ (φ.symm (MonoidAlgebra.single k 1))) =
          ((cyclicEquiv H e he_add he_act).symm k) θ := by
  obtain ⟨φ, hφ⟩ := MazurTransfer.original_literal_nineteen_roots_hopf_classification
    H e he_add he_act
  refine ⟨φ.trans (cyclicAlgebraEquiv H e he_add he_act), ?_⟩
  intro k θ
  have hs : (cyclicAlgebraEquiv H e he_add he_act).symm (MonoidAlgebra.single k 1) =
      MonoidAlgebra.single ((cyclicEquiv H e he_add he_act).symm k) 1 := by
    change (MonoidAlgebra.domCongr R R (cyclicEquiv H e he_add he_act)).symm _ = _
    rw [MonoidAlgebra.domCongr_symm, MonoidAlgebra.domCongr_single]
  change algebraMap R K (θ (φ.symm ((cyclicAlgebraEquiv H e he_add he_act).symm _))) = _
  rw [hs]
  exact hφ _ θ

end MazurTransfer.OriginalLiteralNineteenRootsCyclicClassificationProof20261020

theorem solution : ∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
∃ φ : H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 19)),
      ∀ (k : Multiplicative (ZMod 19)) (θ : CartierDual R H),
        algebraMap R K (θ (φ.symm (MonoidAlgebra.single k 1))) =
          ((cyclicEquiv H e he_add he_act).symm k) θ := by
  exact MazurTransfer.OriginalLiteralNineteenRootsCyclicClassificationProof20261020.exists_cyclic_bialgebra_equivalence
#print axioms solution
