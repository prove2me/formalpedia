-- Prove2me | solution 1 for GlobalTheory.GLDoubling.sphSection_io_biinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:07.180287+00:00
-- url     : https://prove2.me/submissions/24ba6133-d8fb-4264-a06c-58eb579e963f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_io_mem_KO
import Theorems.Thm_GlobalTheory_GLDoubling_isIwasawa
import Theorems.Thm_GlobalTheory_GLDoubling_sphSection_left
import Theorems.Thm_GlobalTheory_GLDoubling_sphSection_right
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_keepsDiag_blkMat
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution (s : ℂ) (g : GL n k) {x y : GL n k} (hx : x ∈ KO k n) (hy : y ∈ KO k n) :
    sphSection k n s (io k n (x * g * y, 1)) = sphSection k n s (io k n (g, 1)) := by
  let p : siegel k n := ⟨io k n (x, x), mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)⟩
  have e : io k n (x * g * y, 1) = p * (io k n (g, 1) * io k n (y, x⁻¹)) := by
    show _ = io k n (x, x) * _
    rw [← map_mul, ← map_mul]
    simp [mul_assoc]
  rw [e, sphSection_left, sphSection_right _ _ (io_mem_KO hy (inv_mem hx)), isIwasawa.2 p (io_mem_KO hx hx),
    one_npow, one_mul]
end GlobalTheory.GLDoubling
