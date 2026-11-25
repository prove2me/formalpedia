-- Prove2me | solution 1 for GlobalTheory.SecAff.pull_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:55:08.898638+00:00
-- url     : https://prove2.me/submissions/ba2ab07b-ff76-491f-80ee-dcf3f011eb73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_sec_kill
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
    (s : SecM A L a T) (hs : pull A L a h s = 0) : ∃ N : ℕ, r ^ N • s = 0 := by
  have := whisker_open A h
  obtain ⟨_, _⟩ := qcqs A (T := T)
  obtain ⟨N, hN⟩ := sec_kill (h ▷ A).left _ (whisker_range A h r hr) (LPow A L a T)
    (LB.isLB_linComb hL _ _) (LPow A L a T').U (chart_le A L a h) (chart_ge A L a h)
    (SecM.toSec A s) (fun j => congrFun (congrArg Subtype.val hs) j)
  refine ⟨N, Subtype.ext (funext fun j => ?_)⟩
  have := hN j
  rw [rs_pa] at this
  change liftHom A _ (r ^ N) * s.1 j = 0
  rw [map_pow]
  exact this
end GlobalTheory.SecAff
