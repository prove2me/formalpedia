-- Prove2me | solution 1 for GlobalTheory.CMLattice.embAll_mem_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:56.578867+00:00
-- url     : https://prove2.me/submissions/ca4be209-5cbc-4427-bcac-e096f3d1b6b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMLattice
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (S : Submodule ℝ (Ψ → Fin r → ℂ)) (hS : ∀ v ∈ Λ, embAll Ψ r v ∈ S) (v : Fin r → E) :
    embAll Ψ r v ∈ S := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := hΛ ▸ Submodule.mem_top
  have key : ∀ e : E, embAll Ψ r (e • v) ∈ S := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
      intro e
      have : embAll Ψ r (e • x) = ∑ i, (((integralBasis E).repr e i : ℚ) : ℝ) •
          embAll Ψ r ((RingOfIntegers.basis E i) • x) := by
        ext τ a
        conv_lhs => rw [← (integralBasis E).sum_repr e]
        simp [Finset.sum_apply, Finset.sum_mul, integralBasis_apply, Rat.smul_def, mul_assoc,
          Algebra.smul_def]
      rw [this]
      exact S.sum_mem fun i _ => S.smul_mem _ (hS _ (Λ.smul_mem _ hx))
    | zero => intro e; simp
    | add x y _ _ hx hy => intro e; rw [smul_add, map_add]; exact S.add_mem (hx e) (hy e)
    | smul a x _ hx => intro e; rw [smul_smul]; exact hx _
  simpa using key 1
end GlobalTheory.CMLattice
