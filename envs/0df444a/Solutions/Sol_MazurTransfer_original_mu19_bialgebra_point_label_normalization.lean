-- Prove2me | solution 1 for MazurTransfer.original_mu19_bialgebra_point_label_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-22T01:36:45.322701+00:00
-- url     : https://prove2.me/submissions/f20b388a-9fd9-466e-8836-c8b9ee6bf52d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: normalize the given cyclic bialgebra equivalence over the same coefficient base so its literal field points equal the given arithmetic root label, pointwise.
Named downstream consumer: exact same selected-pi quotient restriction identity in the literal mu19 model before norm torsor pushforward.
-/
import Definitions.Def_MazurTransfer_OriginalMu19BialgebraPointLabelNormalizationData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
import Definitions.Def_MazurTransfer_OriginalCyclicCharacterConjugationData20261020
import Theorems.Thm_MazurTransfer_original_cyclic_character_conjugation
noncomputable section
open MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.CyclicCharacterConjugation MazurTransfer.Mu19BialgebraPointLabelNormalization
namespace MazurTransfer.OriginalMu19BialgebraPointLabelNormalizationBoundary20261020
end MazurTransfer.OriginalMu19BialgebraPointLabelNormalizationBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: normalize a GIVEN cyclic bialgebra equivalence so its
literal field points equal the GIVEN arithmetic root label, pointwise.
The adjustment is a bialgebra automorphism defined over the SAME base.
Named downstream consumer: exact selected-pi quotient restriction identity
in the literal mu19 model, before actual norm torsor pushforward.
-/

noncomputable section
namespace MazurTransfer.OriginalMu19BialgebraPointLabelNormalizationProof20261020
open CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points
open NineteenRootsGaloisRepresentation CyclicCharacterConjugation
variable {R H K : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable [Field K] [CharZero K] [IsAlgClosed K] [Algebra R K]
variable (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic)
variable (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K))
variable (he_add : ∀ f g, e (f * g) = e f + e g)



include φ e he_add in
theorem exists_normalized_bialgebra_equivalence :
    ∃ ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic,
      ∀ f : WithConv (H →ₐ[R] K), literalPointEquiv ψ K f = (e f).toMul := by
  let A := arithmeticMulEquiv e he_add
  let α : Roots K ≃* Roots K := A.symm.trans (literalPointEquiv φ K)
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  letI : IsCyclic (Roots K) := isCyclic_of_prime_card (roots_card K)
  let r : Cyclic ≃* Roots K := mulEquivOfCyclicCardEq (by
    change Nat.card (ZMod 19) = Nat.card (Roots K)
    rw [Nat.card_zmod, roots_card])
  let γ : Cyclic ≃* Cyclic := conjugate r α
  let ψ := φ.trans (MonoidAlgebra.domCongrBialgEquiv R R γ)
  refine ⟨ψ, fun f => ?_⟩
  have hc := MazurTransfer.original_cyclic_character_conjugation r α.symm
    (pointRootsCharacter R (basisPointEquiv φ K f)) generator
  have hn : literalPointEquiv ψ K f = α.symm (literalPointEquiv φ K f) := by
    apply Subtype.ext
    apply Units.ext
    change f.ofConv (φ.symm ((MonoidAlgebra.domCongr R R γ).symm
      (MonoidAlgebra.single generator 1))) = _
    rw [MonoidAlgebra.domCongr_symm, MonoidAlgebra.domCongr_single]
    exact congrArg (fun ζ : Roots K => ((ζ : Kˣ) : K)) hc
  rw [hn]
  change A ((literalPointEquiv φ K).symm ((literalPointEquiv φ K) f)) = (e f).toMul
  rw [MulEquiv.symm_apply_apply]
  rfl

end MazurTransfer.OriginalMu19BialgebraPointLabelNormalizationProof20261020

theorem solution : ∀ {R H K : Type} [CommRing R] [CommRing H] [Bialgebra R H] [Field K] [CharZero K] [IsAlgClosed K] [Algebra R K] (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g),
∃ ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic,
      ∀ f : WithConv (H →ₐ[R] K), literalPointEquiv ψ K f = (e f).toMul := by
  exact MazurTransfer.OriginalMu19BialgebraPointLabelNormalizationProof20261020.exists_normalized_bialgebra_equivalence
#print axioms solution
