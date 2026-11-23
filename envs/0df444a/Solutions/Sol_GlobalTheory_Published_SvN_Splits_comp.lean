-- Prove2me | solution 1 for GlobalTheory.Published.SvN.Splits.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:57.995003+00:00
-- url     : https://prove2.me/submissions/68480c86-2894-4827-8734-a01e65d98cc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
namespace Splits
theorem _root_.solution (hρ : Ops c ρ) (hα : Splits c A α) {a b : W} (ha : a ∈ A) (hb : b ∈ A) (m : M) :
    (α a)⁻¹ • ρ a ((α b)⁻¹ • ρ b m) = (α (a + b))⁻¹ • ρ (a + b) m := by
  rw [map_smul, hρ.mul, smul_smul, smul_smul]
  congr 1
  have := hα.mul a ha b hb
  have h1 := hα.ne a ha
  have h2 := hα.ne b hb
  have h3 := hα.ne _ (A.add_mem ha hb)
  field_simp
  linear_combination -this
end Splits
end GlobalTheory.Published.SvN
