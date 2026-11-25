-- Prove2me | solution 1 for GlobalTheory.ComplexEmbedding.mk_le_continuum_of_countable_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:43:35.689355+00:00
-- url     : https://prove2.me/submissions/885a96a4-5576-423f-9917-a91b3e100e7e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldFiniteOverCdv
import Theorems.Thm_GlobalTheory_ComplexEmbedding_countable_quotient_pow_of_dvr

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
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Countable (ResidueField V)] : #V ≤ 𝔠 := by
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    haveI := countable_quotient_pow_of_dvr V n; mk_le_aleph0).trans ?_
  simp
end GlobalTheory.ComplexEmbedding
