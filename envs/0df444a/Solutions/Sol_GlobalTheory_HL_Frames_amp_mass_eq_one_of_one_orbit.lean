-- Prove2me | solution 1 for GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:03.039486+00:00
-- url     : https://prove2.me/submissions/88ebdb63-a528-449f-8504-bd3dadd1145c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmplitudeMassEqOneOfSingleOrbit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_hermitianFrames_stabilizer_acts_on_terms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.Frames
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∃ Λ, S.IsTerm d Λ) → (∀ Λ Λ', S.IsTerm d Λ → S.IsTerm d Λ' → ∃ h ∈ S.St, Λ' = h • Λ) → (∀ Λ, S.IsTerm d Λ → P Λ ∧ S.mu Λ = 1 ∧ S.om d Λ = 1) → S.amp d P = 1 ∧ S.mass d P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hex huniq hall
  obtain ⟨Λ, hΛ⟩ := hex
  let o₀ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk'' Λ
  have hout : S.IsTerm d o₀.out := by
    have hm : o₀.out ∈ MulAction.orbit S.St Λ :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St _) Λ)
    obtain ⟨g, hg⟩ := hm
    rw [← hg]
    exact (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hΛ g.1 g.2).1
  have hother : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o ≠ o₀ →
      ¬ S.IsTerm d o.out := by
    intro o ho ht
    obtain ⟨h, hh, e⟩ := huniq Λ o.out hΛ ht
    apply ho
    rw [← Quotient.out_eq' o]
    apply Quotient.sound'
    exact MulAction.orbitRel_apply.2 ⟨⟨h, hh⟩, e.symm⟩
  obtain ⟨hP, hmu, hom⟩ := hall _ hout
  constructor
  · unfold GlobalTheory.HL.Frames.amp
    rw [tsum_eq_single o₀]
    · rw [if_pos ⟨hout, hP⟩, hmu, hom]; simp
    · intro o ho
      exact if_neg fun hc => hother o ho hc.1
  · unfold GlobalTheory.HL.Frames.mass
    rw [tsum_eq_single o₀]
    · rw [if_pos ⟨hout, hP⟩, hmu]; simp
    · intro o ho
      exact if_neg fun hc => hother o ho hc.1
end GlobalTheory.HL.Frames
