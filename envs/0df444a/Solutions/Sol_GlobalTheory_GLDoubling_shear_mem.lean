-- Prove2me | solution 1 for GlobalTheory.GLDoubling.shear_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:51.242185+00:00
-- url     : https://prove2.me/submissions/eb3302eb-75f7-4a4b-8f2c-53041f1174de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_fromBlocks_int
import Theorems.Thm_GlobalTheory_GLDoubling_one_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution {B C : Matrix n n k} (h : B * C = 0) (h' : C * B = 0) (hB : ∀ i j, B i j ∈ 𝒪[k])
    (hC : ∀ i j, C i j ∈ 𝒪[k]) : shear B C h h' ∈ KO k (n ⊕ n) :=
  (SplitFlip.mem_KO_iff _).2 ⟨fromBlocks_int one_int hB hC one_int,
    fromBlocks_int one_int (fun i j => neg_mem (hB i j)) (fun i j => neg_mem (hC i j)) one_int⟩
end GlobalTheory.GLDoubling
