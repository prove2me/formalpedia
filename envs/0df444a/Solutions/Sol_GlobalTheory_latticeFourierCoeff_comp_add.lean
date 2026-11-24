-- Prove2me | solution 1 for GlobalTheory.latticeFourierCoeff_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:22.488128+00:00
-- url     : https://prove2.me/submissions/76edfb29-41b7-446e-867f-fa7822d460cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_isAddFundamentalDomain_latticeCell
import Theorems.Thm_GlobalTheory_cexp_two_pi_I_add
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_eq_setIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}
namespace GlobalTheory
theorem _root_.solution {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {ν : E} (hν : ν ∈ L*) (c : E) :
    latticeFourierCoeff L (fun b ↦ A (b + c)) ν =
      e[⟪ν, c⟫] • latticeFourierCoeff L A ν := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddCommClass E L E := ⟨fun a x b ↦ add_left_comm a (x : E) b⟩
  have hF : IsAddFundamentalDomain L (c +ᵥ latticeCell L) volume :=
    (isAddFundamentalDomain_latticeCell L _).vadd_of_comm c
  rw [latticeFourierCoeff_eq_setIntegral hA hν hF, smul_comm, ← integral_smul,
    latticeFourierCoeff]
  congr 1
  rw [show c +ᵥ latticeCell L = (fun x ↦ c + x) '' latticeCell L from rfl,
    (measurePreserving_add_left volume c).setIntegral_image_emb
    (measurableEmbedding_addLeft c)]
  refine integral_congr_ae (.of_forall fun b ↦ ?_)
  simp only [smul_smul, ← cexp_two_pi_I_add, inner_add_right, add_comm c b]
  congr 4; ring
end GlobalTheory
