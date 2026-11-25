-- Prove2me | solution 1 for GlobalTheory.CapelliCentral.prod_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:47:27.807839+00:00
-- url     : https://prove2.me/submissions/6fa609dc-babd-4f29-94e0-fa1e612ef671

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SmoothAddSmul
import Theorems.Thm_GlobalTheory_CapelliCentral_tm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CapelliCentral
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CapelliCentral
theorem _root_.solution (l : List (ℂ × Fin n × Fin n)) (F : smoothSpace ε E)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → F.1 g = f g) :
    ∀ g, inUJ ε g → ((l.map fun p => Tm (eabEnd ε E) p.1 p.2.1 p.2.2).prod F).1 g =
      (l.map fun p => Top (EabV ε) p.1 p.2.1 p.2.2).foldr (fun T h => T h) f g := by
  induction l with
  | nil => intro g hg; simpa using h g hg
  | cons p l ih =>
    intro g hg
    rw [List.map_cons, List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
    exact tm_apply _ _ _ _ ih hg
end GlobalTheory.CapelliCentral
