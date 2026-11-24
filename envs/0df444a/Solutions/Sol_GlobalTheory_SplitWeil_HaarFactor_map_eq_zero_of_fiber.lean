-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.map_eq_zero_of_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:35.084814+00:00
-- url     : https://prove2.me/submissions/b066cb7e-f411-4539-afc4-b682eb6752f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_slice_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_transl_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_ind_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_exists_subgroup_invariant
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_exists_decomp
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_real_ne_zero
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_fiber_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]
variable [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {M : Type*} [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × A) →ₗ[ℂ] M)
    (hL : ∀ (a : A) (G G' : SB (X₀ × A)), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G)
    (G : SB (X₀ × A)) (hG : ∀ x, ∫ a, G.1 (x, a) ∂μ = 0) : L G = 0 := by
  obtain ⟨U, hUo, hUc, hinv⟩ := exists_subgroup_invariant hbasis G.2
  obtain ⟨T, hT⟩ := exists_decomp hUo G.2 hinv
  have hsum : ∀ x, ∑ q ∈ T, G.1 (x, q.out) = 0 := fun x => by
    have := (fiber_integral μ hUo hUc T hT x).symm.trans (hG x)
    exact (mul_eq_zero.mp this).resolve_right (real_ne_zero μ hUo hUc)
  let e : SB A := ⟨_, ind_mem hUo hUc⟩
  let g : A ⧸ U → SB X₀ := fun q => ⟨_, slice_mem G.2 q.out⟩
  let Gq : A ⧸ U → SB (X₀ × A) := fun q =>
    ⟨fun z => (tensL e (g q)).1 (z.1, z.2 - q.out), transl_mem (tensL e (g q)).2 q.out⟩
  have hdec : G = ∑ q ∈ T, Gq q := by
    apply Subtype.ext
    funext z
    rw [hT z, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hq : ∀ q, L (Gq q) = L (tensL e (g q)) := fun q =>
    (hL q.out (Gq q) (tensL e (g q)) fun z => by simp [Gq, tensL, g, e]).symm
  have hg : ∑ q ∈ T, g q = 0 := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    exact hsum x
  rw [hdec, map_sum, Finset.sum_congr rfl fun q _ => hq q, ← map_sum, ← map_sum, hg, map_zero, map_zero]
end GlobalTheory.SplitWeil.HaarFactor
