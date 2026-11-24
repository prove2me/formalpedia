-- Prove2me | solution 1 for GlobalTheory.SplitComp.exists_real_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:40.444009+00:00
-- url     : https://prove2.me/submissions/9848bbff-3763-498e-b595-b98150086e64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
open GlobalTheory GlobalTheory.SplitComp
variable (L : Type) [Field L] [NumberField L] [IsCMField L]
namespace GlobalTheory.SplitComp
theorem _root_.solution (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (x : L) :
    ∃ a b : maximalRealSubfield L, x = a • (1 : L) + b • θ := by
  have h2 : IsCMField.complexConj L (2 : L) = 2 := map_ofNat _ 2
  have ha : (x + IsCMField.complexConj L x) / 2 ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, h2]
    ring
  have hb : (x - IsCMField.complexConj L x) / (2 * θ) ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul,
      IsCMField.complexConj_apply_apply, h2, hθ]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change x = (x + IsCMField.complexConj L x) / 2 * 1 + (x - IsCMField.complexConj L x) / (2 * θ) * θ
  field_simp
  ring
end GlobalTheory.SplitComp
