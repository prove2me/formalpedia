-- Prove2me | solution 1 for GlobalTheory.LatBasisAdapted.exists_basis_adapted_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:06:14.816839+00:00
-- url     : https://prove2.me/submissions/0add05f6-3dec-436c-9cc6-2c70d8d9c501

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedTwoSubspaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedMem
import Theorems.Thm_GlobalTheory_LatBasisAdapted_span_range_smul_comp
import Theorems.Thm_GlobalTheory_LatDen_latDen
import Theorems.Thm_GlobalTheory_exists_basis_adapted_two_subspaces


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.LatBasisAdapted
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LatBasisAdapted
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (W₁ W₂ : Submodule E (Fin r → E)), ∃ (a b c : ℕ) (w : Fin a ⊕ Fin b ⊕ Fin c → Fin r → E), LinearIndependent E w ∧ (∀ k, w k ∈ X.Λ) ∧ Submodule.span E (Set.range (w ∘ Sum.inl)) = W₁ ⊓ W₂ ∧ Submodule.span E (Set.range (w ∘ Sum.map id Sum.inl)) = W₁ ∧ Submodule.span E (Set.range (w ∘ Sum.map id Sum.inr)) = W₂ ∧ Submodule.span E (Set.range w) = W₁ ⊔ W₂) := by
  intro r X W₁ W₂
  obtain ⟨a, b, c, w, hw, h0, h1, h2, h3⟩ :=
    GlobalTheory.exists_basis_adapted_two_subspaces E (Fin r → E) W₁ W₂
  choose n hn hm using fun k => (GlobalTheory.LatDen.latDen r X).1 (w k)
  have hc : ∀ k, (n k : E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hn k).ne'
  refine ⟨a, b, c, fun k => (n k : E) • w k, ?_, hm, ?_, ?_, ?_, ?_⟩
  · exact hw.units_smul (fun k => Units.mk0 _ (hc k))
  · rw [span_range_smul_comp _ hc, h0]
  · rw [span_range_smul_comp _ hc, h1]
  · rw [span_range_smul_comp _ hc, h2]
  · exact (span_range_smul_comp _ hc w id).trans h3
end GlobalTheory.LatBasisAdapted
