-- Prove2me | solution 1 for GlobalTheory.BaireDistribution.exists_nhds_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:18.989447+00:00
-- url     : https://prove2.me/submissions/93efc5d8-129a-4939-848f-e91d021ca34f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire
import Theorems.Thm_GlobalTheory_OpTrace_isOpen_leftStabilizer
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BaireDistribution
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.BaireDistribution
theorem _root_.solution (φ : SB G) :
    ∃ U ∈ nhds (1 : G), ∀ a ∈ U, ∀ b ∈ U, ∀ g, φ.1 (a * g * b) = φ.1 g := by
  have h1 := GlobalTheory.OpTrace.isOpen_leftStabilizer φ.2.1 φ.2.2
  have h2 := GlobalTheory.OpTrace.isOpen_leftStabilizer (f := fun g => φ.1 g⁻¹)
    (φ.2.1.comp_continuous continuous_inv) (φ.2.2.comp_homeomorph (Homeomorph.inv G))
  refine ⟨_, (h1.inter h2).mem_nhds ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩,
    fun a ha b hb g => ?_⟩
  have e1 : ∀ g, φ.1 (a * g) = φ.1 g := ha.1
  have e2 : ∀ g, φ.1 (b * g)⁻¹ = φ.1 g⁻¹ := hb.2
  rw [mul_assoc, e1]
  simpa using (e2 (g * b)⁻¹).symm
end GlobalTheory.BaireDistribution
