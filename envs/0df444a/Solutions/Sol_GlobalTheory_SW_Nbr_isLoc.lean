-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.isLoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:10.618658+00:00
-- url     : https://prove2.me/submissions/b66158dd-832e-4c6c-97f9-dbebeebae146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) :
    IsLocalizedModule (𝓞 E)⁰ Λ.subtype := by
  obtain ⟨s, hs, -, -, h2⟩ := h.2.2
  have := isLocalizedModule_id (𝓞 E)⁰ (Fin n → E) E
  refine ⟨IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := Fin n → E)), fun y => ?_,
    fun {x₁ x₂} h => ⟨1, by rw [Subtype.ext h]⟩⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ y
  choose c hc using hd
  have h1 : (d : 𝓞 E) • y ∈ stdL E n := by
    have : (d : 𝓞 E) • y = ∑ i, c i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, ← hc j, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hs' : (s : 𝓞 E) ∈ (𝓞 E)⁰ := mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hs.ne')
  exact ⟨(⟨_, h2 _ h1⟩, ⟨s, hs'⟩ * d), mul_smul _ _ _⟩
end GlobalTheory.SW.Nbr
