-- Prove2me | solution 1 for GlobalTheory.GLDoubling.absRatio_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:50:19.600403+00:00
-- url     : https://prove2.me/submissions/a978afed-cf70-4fc6-8849-2a890e5260a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_coe_absRatio
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl


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
theorem _root_.solution (p : siegel k n) {a d : kˣ} (ha : (a : k) = (leviMat (Equiv.refl (n ⊕ n)) p.1.1).det)
    (hd : (d : k) = (quotMat (Equiv.refl (n ⊕ n)) p.1.1).det) : (absRatio k n p : ℝ) = nabs k a / nabs k d := by
  have h1 : GeneralLinearGroup.det (leviGL (Equiv.refl (n ⊕ n)) p) = a := Units.ext ha.symm
  have h2 : GeneralLinearGroup.det (p : GL (n ⊕ n) k) = a * d :=
    Units.ext (by rw [Units.val_mul, ha, hd]; exact (mem_stabGL_diagSub.1 p.2).det_eq)
  have := (nabs_pos' k a).ne'
  rw [coe_absRatio, h1, h2, nabs_mul']
  field_simp
end GlobalTheory.GLDoubling
