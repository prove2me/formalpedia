-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.exists_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:28.474144+00:00
-- url     : https://prove2.me/submissions/589febed-b58a-4cde-af3a-757d9046c1bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
import Theorems.Thm_GlobalTheory_UnramSelfDual_sigR_algebraMap
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_of_fixed_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
open GlobalTheory.SelfDualLatticeCompare IsLocalRing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution (h : IsCMExt F E σ) :
    ∃ p q : Ev F E v, p ∈ OEv F E v ∧ sigR (Fv F v) σ p = p ∧ p * q = 1 ∧ q ∉ OEv F E v ∧
      ∀ a ∈ OEv F E v, sigR (Fv F v) σ a = a →
        (∃ b ∈ OEv F E v, a * b = 1) ∨ ∃ b ∈ OEv F E v, a = p * b := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have h0 : (ϖ : Fv F v) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  refine ⟨algebraMap (Fv F v) _ (ϖ : Fv F v), algebraMap (Fv F v) _ (ϖ : Fv F v)⁻¹,
    (OEv F E v).algebraMap_mem ϖ, sigR_algebraMap v _, ?_, fun hq => ?_, fun a ha hc => ?_⟩
  · rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  · obtain ⟨r, hr⟩ := exists_of_fixed_int v h hq (sigR_algebraMap v _)
    have hr' : (r : Fv F v) = (ϖ : Fv F v)⁻¹ := (algebraMap (Fv F v) (Ev F E v)).injective hr
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one r (Subtype.ext ?_))
    show (ϖ : Fv F v) * r = 1
    rw [hr', mul_inv_cancel₀ h0]
  · obtain ⟨r, rfl⟩ := exists_of_fixed_int v h ha hc
    by_cases hr : IsUnit r
    · obtain ⟨b, hb⟩ := hr.exists_right_inv
      exact Or.inl ⟨_, (OEv F E v).algebraMap_mem b, by rw [← map_mul, hb, map_one]⟩
    · have : r ∈ maximalIdeal _ := hr
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
      obtain ⟨b, rfl⟩ := this
      exact Or.inr ⟨_, (OEv F E v).algebraMap_mem b, by rw [map_mul]; rfl⟩
end GlobalTheory.UnramSelfDual
