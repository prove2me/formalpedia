-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.mul_mem_boxSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:15.564209+00:00
-- url     : https://prove2.me/submissions/6ddab46a-aff2-4d61-81f5-6c29a17f4f90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
import Theorems.Thm_GlobalTheory_DegreeGrowth_monomial_mul_mem

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
open GlobalTheory
open GlobalTheory.DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]
namespace GlobalTheory.DegreeGrowth
theorem _root_.solution {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (z : B)
    (hz : ∀ l, z * b l ∈ boxSpan K y b d) {x : B} (hx : x ∈ boxSpan K y b D) :
    z * x ∈ boxSpan K y b (d + D) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, l⟩, rfl⟩ := hx
    have h := monomial_mul_mem y b d D (fun i => (c i : ℕ))
      (fun i => Nat.le_of_lt_succ (c i).2) (hz l)
    convert h using 1
    ring
  | zero => simp
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.DegreeGrowth
