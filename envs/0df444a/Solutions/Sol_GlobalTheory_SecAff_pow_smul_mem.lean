-- Prove2me | solution 1 for GlobalTheory.SecAff.pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:58.520184+00:00
-- url     : https://prove2.me/submissions/c63251e3-5c2c-40b6-ba7b-f7042ae330ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_fun_extend
import Theorems.Thm_GlobalTheory_SecAff_pow_smul_mem_of
import Theorems.Thm_GlobalTheory_SecAff_pull_kill

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
    (W : Submodule Γ(T.left, ⊤) (SecM A L a T)) (s : SecM A L a T)
    (hs : pull A L a h s ∈ Submodule.span Γ(T'.left, ⊤) (pull A L a h '' W)) :
    ∃ N : ℕ, r ^ N • s ∈ W :=
  pow_smul_mem_of (pull A L a h) r
    (fun_extend h.left r hr (isAffineOpen_top T.left) (W' := ⊤) (le_pre_top _) le_top)
    (pull_kill A L a hL h r hr) W s hs
end GlobalTheory.SecAff
