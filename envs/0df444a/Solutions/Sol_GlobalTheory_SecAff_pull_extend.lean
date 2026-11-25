-- Prove2me | solution 1 for GlobalTheory.SecAff.pull_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:00.221163+00:00
-- url     : https://prove2.me/submissions/4f43f0dd-0087-477d-9f14-a465d3f96c66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_sec_extend
import Theorems.Thm_GlobalTheory_SecAff_chart_ge
import Theorems.Thm_GlobalTheory_SecAff_whisker_open
import Theorems.Thm_GlobalTheory_SecAff_whisker_range
import Theorems.Thm_GlobalTheory_SecAff_qcqs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
namespace GlobalTheory.SecAff
theorem _root_.solution [IsProper A.hom] [IsAffine T.left] (hL : L.IsLB) (h : T' ⟶ T)
    [IsOpenImmersion h.left] (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r)
    (t : SecM A L a T') : ∃ (N : ℕ) (s : SecM A L a T),
      pull A L a h s = pa h.left (V := ⊤) (le_pre_top _) r ^ N • t := by
  have := whisker_open A h
  obtain ⟨_, _⟩ := qcqs A (T := T)
  obtain ⟨N, s, hN⟩ := sec_extend (h ▷ A).left _ (whisker_range A h r hr) (LPow A L a T)
    (LB.isLB_linComb hL _ _) (LPow A L a T').U (chart_le A L a h) (chart_ge A L a h)
    t.1 (fun i j => (t.2 i j).trans (congrArg (· * _) (pa_g A L a h i j _).symm))
  refine ⟨N, SecM.ofSec A s, Subtype.ext (funext fun j => ?_)⟩
  refine (hN j).trans ?_
  change _ = liftHom A _ (_ ^ N) * t.1 j
  rw [map_pow, ← pa_liftHom A h (le_pre_top _)]
  rfl
end GlobalTheory.SecAff
