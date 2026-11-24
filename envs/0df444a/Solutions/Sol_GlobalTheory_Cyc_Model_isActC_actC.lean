-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.isActC_actC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:20.128835+00:00
-- url     : https://prove2.me/submissions/f66ab757-c866-4c83-b767-7a3f316e9039

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem norm_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    ‖_root_.GlobalTheory.Cyc.Model.extHom g y‖ = ‖y‖ := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_norm.comp (continuous_cyc_extHom g)) continuous_norm) fun x => ?_
  rw [cyc_extHom_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact (_root_.GlobalTheory.Cyc.Model.isom_gal g).norm_map_of_map_zero (map_zero _) x
end GlobalTheory.Cyc.Model
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
open Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
namespace _root_.GlobalTheory.Cyc.Model
theorem _root_.solution :
    _root_.GlobalTheory.Cyc.IsActC (_root_.GlobalTheory.Cyc.Model.actC (l := l)) :=
  ⟨fun g x => cyc_extHom_coe g x, fun g y => norm_cyc_extHom g y⟩
end _root_.GlobalTheory.Cyc.Model
end GlobalTheory.Cyc.Model
