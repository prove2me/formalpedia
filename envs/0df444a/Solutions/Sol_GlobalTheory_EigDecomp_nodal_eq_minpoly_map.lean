-- Prove2me | solution 1 for GlobalTheory.EigDecomp.nodal_eq_minpoly_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:41.33512+00:00
-- url     : https://prove2.me/submissions/b90dd48c-c77c-44d0-a3c0-142c5bb8323e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueEmbeddingEigenspaceSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField
open GlobalTheory GlobalTheory.EigDecomp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
namespace GlobalTheory.EigDecomp
theorem _root_.solution (c : Coeff l) (α : 𝓞 E)
    (hinj : Function.Injective fun τ : E →+* ℂ => embK c τ α) :
    Lagrange.nodal Finset.univ (fun τ : E →+* ℂ => embK c τ α) = (minpoly ℤ α).map (Int.castRingHom c.F) := by
  have hint : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hintE : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) ?_ ?_
  · rw [Lagrange.nodal]
    refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _) fun τ _ => dvd_iff_isRoot.mpr ?_
    have h := aeval_algHom_apply (embK c τ).toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    rw [IsRoot.def, eval_map, ← algebraMap_int_eq, ← aeval_def]
    exact h
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int _), Lagrange.natDegree_nodal, Finset.card_univ,
      NumberField.Embeddings.card E ℂ, ← RingOfIntegers.minpoly_coe,
      ← natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintE]
    exact minpoly.natDegree_le _
end GlobalTheory.EigDecomp
