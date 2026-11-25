-- Prove2me | solution 1 for GlobalTheory.InvH.tsum_orbit_normaliser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:42:59.829471+00:00
-- url     : https://prove2.me/submissions/ed7edf0f-d1a0-4214-9eff-5de968278483

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumOrbitNormaliser
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.InvH
namespace GlobalTheory.InvH
theorem _root_.solution {G X M : Type} [Group G] [MulAction G X] [AddCommMonoid M]
    [TopologicalSpace M] (K : Subgroup G) (h : G) (h1 : ∀ s ∈ K, h * s * h⁻¹ ∈ K)
    (h2 : ∀ s ∈ K, h⁻¹ * s * h ∈ K) (φ ψ : X → M) (hφ : ∀ s ∈ K, ∀ x, φ (s • x) = φ x)
    (hψ : ∀ x, ψ (h • x) = φ x) :
    ∑' o : MulAction.orbitRel.Quotient K X, ψ o.out =
      ∑' o : MulAction.orbitRel.Quotient K X, φ o.out := by
  let e : MulAction.orbitRel.Quotient K X ≃ MulAction.orbitRel.Quotient K X :=
    Quotient.congr (MulAction.toPerm h) (by
      intro a b
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.toPerm_apply]
      constructor
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h1 s s.2⟩, ?_⟩
        rw [← hs]
        simp [Subgroup.smul_def, mul_smul]
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h2 s s.2⟩, ?_⟩
        simp only [Subgroup.smul_def, mul_smul] at hs ⊢
        rw [hs]; simp)
  rw [← e.tsum_eq]
  refine tsum_congr fun o => ?_
  have h3 : e o = Quotient.mk _ (h • o.out) := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have h4 : (MulAction.orbitRel K X) (e o).out (h • o.out) := by
    rw [h3]; exact Quotient.mk_out (s := MulAction.orbitRel K X) _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : (e o).out = h • ((h⁻¹ * s * h) • o.out) := by
    rw [← hs]; simp [Subgroup.smul_def, mul_smul]
  rw [h5, hψ, hφ _ (h2 s s.2)]
end GlobalTheory.InvH
