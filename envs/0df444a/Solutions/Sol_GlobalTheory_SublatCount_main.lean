-- Prove2me | solution 1 for GlobalTheory.SublatCount.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:50:01.606084+00:00
-- url     : https://prove2.me/submissions/bd5fce06-d39f-44d8-ad96-edf90c427565

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes
import Theorems.Thm_GlobalTheory_SublatCount_encard_eq_of_bijOn
import Theorems.Thm_GlobalTheory_SublatCount_mem_ker_iff
import Theorems.Thm_GlobalTheory_SublatCount_encard_prod
import Theorems.Thm_GlobalTheory_SublatCount_finrank_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.SublatCount
namespace GlobalTheory.SublatCount
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ (T : ℕ) (s : Finset (Ideal (𝓞 K))), T.Prime → (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) → {L : Submodule (𝓞 K) V | L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))}.encard = (((∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ M hM T s hT hs
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  rw [← finrank_lattice M hM, ← encard_prod (N := M) T hT.ne_zero s fun P hP =>
    ⟨(hs P hP).1, by rw [← (hs P hP).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]⟩]
  refine encard_eq_of_bijOn (f := fun L => L.comap M.subtype) ⟨?_, ?_, ?_⟩
  · intro L hL
    exact (mem_ker_iff _ _).2 hL.2
  · intro L hL L' hL' h
    have := congrArg (Submodule.map M.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hL.1,
      inf_eq_right.2 hL'.1] at this
  · intro L hL
    have h : (L.map M.subtype).comap M.subtype = L := Submodule.comap_map_eq_of_injective M.injective_subtype L
    refine ⟨L.map M.subtype, ⟨Submodule.map_subtype_le _ _, ?_⟩, h⟩
    rw [h]
    exact (mem_ker_iff _ _).1 hL
end GlobalTheory.SublatCount
