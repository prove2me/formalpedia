-- Prove2me | solution 1 for GlobalTheory.HL.TraceConjugationCover.stMat_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:22.241831+00:00
-- url     : https://prove2.me/submissions/8b5af33a-1e2d-4263-8145-c1deb26f1dcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StMatSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.HL
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TraceConjugationCover
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}
namespace GlobalTheory.HL.TraceConjugationCover
theorem _root_.solution (G : GFrames A r k) (x : G.GLV)
    (h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) :
    ∀ b, x (G.f' b) = ∑ a, stMat G x a b • G.f' a := by
  unfold stMat; rw [dif_pos h]; exact h.choose_spec
end GlobalTheory.HL.TraceConjugationCover
