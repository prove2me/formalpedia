-- Prove2me | solution 1 for GlobalTheory.NormSheafDescent.ideal_eq_top_of_forall_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:48.459545+00:00
-- url     : https://prove2.me/submissions/a9bd2c28-5f6c-428a-9b8a-3bbe1ff3c7c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoefficientIdealFamilyEqTopOfDisjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent
namespace GlobalTheory.NormSheafDescent
theorem _root_.solution {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ x ∈ I.support, x ∉ V.1) : I.ideal V = ⊤ := by
  have hV : IsAffineOpen V.1 := V.2
  have hempty : X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) ∩ V.1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxV
    exact h x ((Scheme.IdealSheafData.mem_support_iff_of_mem hxV).2 hx) hxV
  rw [← hV.fromSpec_image_zeroLocus] at hempty
  have h0 : PrimeSpectrum.zeroLocus (I.ideal V : Set Γ(X, V.1)) = ∅ := Set.image_eq_empty.mp hempty
  rw [PrimeSpectrum.zeroLocus_empty_iff_eq_top] at h0
  exact h0
end GlobalTheory.NormSheafDescent
