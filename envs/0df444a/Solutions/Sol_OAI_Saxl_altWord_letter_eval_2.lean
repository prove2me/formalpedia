-- Prove2me | solution 2 for OAI.Saxl.altWord_letter_eval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:14:25.910588+00:00
-- url     : https://prove2.me/submissions/93fa4a4c-c676-4e68-811b-8447a8f153f9

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/PathAlternation.lean:L197-L213
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.altWord_letter_eval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation

-- ---- from OAI.RepresentationTheory.Saxl.PathAlternation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl.PathLayer

end Saxl.PathLayer

namespace Saxl

lemma altWord_letter_eval {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (G : Subgroup (Equiv.Perm (Fin n))) (a w : Fin n → Fin d) :
    altWord G (φ ∘ a) (φ ∘ w) = altWord G a w := by
  classical
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  change (Pi.single (φ ∘ a) (1:ℂ) : WordSpace n D) ((φ ∘ w) ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace n d) (w ∘ g.val)
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; funext i; exact hφ (congrFun h i)
  · intro h; funext i; exact congrArg φ (congrFun h i)

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.altWord_letter_eval := @_root_.OAI.Saxl.altWord_letter_eval
