-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.monomial_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:24.763866+00:00
-- url     : https://prove2.me/submissions/065b510b-c08c-436b-a6f5-707e3dc3b4c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
import Theorems.Thm_GlobalTheory_DegreeGrowth_mem_boxSpan

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
theorem _root_.solution {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (a : Fin s → ℕ)
    (ha : ∀ i, a i ≤ d) {x : B} (hx : x ∈ boxSpan K y b D) :
    (∏ i, y i ^ a i) * x ∈ boxSpan K y b (D + d) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, l⟩, rfl⟩ := hx
    have h := mem_boxSpan (K := K) y b (D + d) (fun i => (c i : ℕ) + a i)
      (fun i => add_le_add (Nat.le_of_lt_succ (c i).2) (ha i)) l
    simp only [pow_add, Finset.prod_mul_distrib] at h
    convert h using 1
    ring
  | zero => simp
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.DegreeGrowth
