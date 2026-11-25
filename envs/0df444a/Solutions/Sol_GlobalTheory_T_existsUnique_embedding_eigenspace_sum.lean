-- Prove2me | solution 1 for GlobalTheory.T.existsUnique_embedding_eigenspace_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:16:48.379862+00:00
-- url     : https://prove2.me/submissions/183b9f2f-7ecc-4c7c-88df-aa028c710a62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueEmbeddingEigenspaceSum
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueEmbeddingEigenspaceSumStatement
import Theorems.Thm_GlobalTheory_EigDecomp_exists_unique_eigen_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R) (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V, (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  first | exact @GlobalTheory.EigDecomp.exists_unique_eigen_sum | exact GlobalTheory.EigDecomp.exists_unique_eigen_sum | (intros; apply GlobalTheory.EigDecomp.exists_unique_eigen_sum <;> assumption)
end _root_.GlobalTheory.T
