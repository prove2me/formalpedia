-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:28.16181+00:00
-- url     : https://prove2.me/submissions/633037d1-c5ac-4231-a66d-3cb42d069d4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_slice_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_fiber_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_ind_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_exists_subgroup_invariant
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_exists_decomp
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_integrable_of_SB
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_real_ne_zero
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_fiber_integral
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_map_eq_zero_of_fiber

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
    (hL : ∀ (a : A) (G G' : SB (X₀ × A)), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) :
    ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G : SB (X₀ × A), ∃ Ψ : SB X₀,
      (∀ x, Ψ.1 x = ∫ a, G.1 (x, a) ∂μ) ∧ L G = l₀ Ψ := by
  obtain ⟨B, hBo, hBc, -⟩ := hbasis Set.univ Filter.univ_mem
  have hpos := real_ne_zero μ hBo hBc
  let φ₀ : SB A := (μ.real (B : Set A) : ℂ)⁻¹ • ⟨_, ind_mem hBo hBc⟩
  have hφ₀ : ∫ a, φ₀.1 a ∂μ = 1 := by
    show ∫ a, (μ.real (B : Set A) : ℂ)⁻¹ * (B : Set A).indicator (fun _ => (1 : ℂ)) a ∂μ = 1
    rw [integral_const_mul, integral_indicator_const _ hBo.measurableSet]
    simp [hpos]
  refine ⟨L ∘ₗ tensL φ₀, fun G => ?_⟩
  obtain ⟨U, hUo, hUc, hinv⟩ := exists_subgroup_invariant hbasis G.2
  obtain ⟨T, hT⟩ := exists_decomp hUo G.2 hinv
  have hΨ : (fun x => ∫ a, G.1 (x, a) ∂μ) ∈ SB X₀ := by
    have := (SB X₀).smul_mem (μ.real (U : Set A) : ℂ)
      (Submodule.sum_mem _ fun q (_ : q ∈ T) => slice_mem G.2 q.out)
    convert this using 1
    funext x
    rw [fiber_integral μ hUo hUc T hT x]
    simp [Finset.sum_apply, mul_comm]
  refine ⟨⟨_, hΨ⟩, fun x => rfl, ?_⟩
  rw [← sub_eq_zero, LinearMap.comp_apply, ← map_sub]
  refine map_eq_zero_of_fiber μ hbasis L hL _ fun x => ?_
  show ∫ a, (G.1 (x, a) - (∫ a', G.1 (x, a') ∂μ) * φ₀.1 a) ∂μ = 0
  rw [integral_sub (integrable_of_SB μ (fiber_mem G.2 x)) ((integrable_of_SB μ φ₀.2).const_mul _),
    integral_const_mul, hφ₀, mul_one, sub_self]
end GlobalTheory.SplitWeil.HaarFactor
