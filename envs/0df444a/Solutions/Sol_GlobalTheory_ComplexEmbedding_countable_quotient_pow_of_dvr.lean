-- Prove2me | solution 1 for GlobalTheory.ComplexEmbedding.countable_quotient_pow_of_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:06.017903+00:00
-- url     : https://prove2.me/submissions/4fd89b61-2d4e-41fc-8739-9cdf951d86db

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldFiniteOverCdv
import Theorems.Thm_GlobalTheory_ComplexEmbedding_exists_digits_of_dvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.L2.Pj
open GlobalTheory GlobalTheory.ComplexEmbedding
open Cardinal IsLocalRing
namespace GlobalTheory.ComplexEmbedding
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Countable (ResidueField V)] (n : ℕ) : Countable (V ⧸ maximalIdeal V ^ n) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let s : ResidueField V → V := Function.surjInv (residue_surjective (R := V))
  have hs : ∀ r, residue V (s r) = r := Function.surjInv_eq _
  have hsurj : Function.Surjective (fun f : Fin n → ResidueField V =>
      Ideal.Quotient.mk (maximalIdeal V ^ n) (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ))) := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨f, hf⟩ := exists_digits_of_dvr V ϖ hϖ s hs n x
    exact ⟨f, (Ideal.Quotient.eq.2 hf).symm⟩
  exact hsurj.countable
end GlobalTheory.ComplexEmbedding
