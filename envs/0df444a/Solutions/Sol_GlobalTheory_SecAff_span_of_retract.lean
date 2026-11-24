-- Prove2me | solution 1 for GlobalTheory.SecAff.span_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:16:48.860841+00:00
-- url     : https://prove2.me/submissions/ad6ff63a-6605-4937-9e30-9639f302d020

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_map_mem_span
import Theorems.Thm_GlobalTheory_SecAff_pull_pull
import Theorems.Thm_GlobalTheory_SecAff_pull_id

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
theorem _root_.solution (e : T'' ⟶ T') (e' : T' ⟶ T'') (he : e' ≫ e = 𝟙 T') (k : T'' ⟶ T)
    {κ : Type} (b : κ → SecM A L a T)
    (hb : Submodule.span Γ(T''.left, ⊤) (Set.range fun i => pull A L a k (b i)) = ⊤) :
    Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pull A L a (e' ≫ k) (b i)) = ⊤ := by
  refine eq_top_iff.2 fun σ _ => ?_
  have := map_mem_span (pull A L a e') _ (pull A L a e σ) (hb.ge trivial)
  rw [pull_pull, he, pull_id] at this
  simp only [pull_pull] at this
  exact this
end GlobalTheory.SecAff
