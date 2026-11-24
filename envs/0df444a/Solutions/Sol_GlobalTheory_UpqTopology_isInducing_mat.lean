-- Prove2me | solution 1 for GlobalTheory.UpqTopology.isInducing_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:51.982839+00:00
-- url     : https://prove2.me/submissions/f409113c-e7f8-4928-ab54-ffab1d484d7f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Theorems.Thm_GlobalTheory_UpqTopology_left_inv
import Theorems.Thm_GlobalTheory_UpqTopology_mat_unitary
import Theorems.Thm_GlobalTheory_UpqTopology_continuous_mat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.UpqTopology
variable {P Q : ℕ}
namespace GlobalTheory.UpqTopology
theorem _root_.solution : IsInducing (UpqT.mat (P := P) (Q := Q)) := by
  let f : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ × (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᵐᵒᵖ :=
    fun g => (g, MulOpposite.op (Formalism.UG.Jpq P Q * gᴴ * Formalism.UG.Jpq P Q))
  have hf : Continuous f :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ UpqT.mat =
      Units.embedProduct _ ∘ (Subtype.val : Formalism.UG.Upq P Q → GL (Fin P ⊕ Fin Q) ℂ) := by
    funext g
    refine Prod.ext rfl (congrArg MulOpposite.op ?_)
    exact (Units.inv_eq_of_mul_eq_one_left (left_inv (mat_unitary g))).symm
  refine IsInducing.of_comp continuous_mat hf ?_
  rw [hcomp]
  exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal
end GlobalTheory.UpqTopology
