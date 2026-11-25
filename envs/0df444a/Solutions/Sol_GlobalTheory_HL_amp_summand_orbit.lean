-- Prove2me | solution 1 for GlobalTheory.HL.amp_summand_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:21.924177+00:00
-- url     : https://prove2.me/submissions/59337f50-73e4-40e3-b622-e88c00af2999

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalAmplitudeSummandAtTermOrbit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_commonStabilizer_stabilizers_commensurable_volume
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
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, ∀ h ∈ S.St, P (h • Λ) ↔ P Λ) → ∀ Λ, S.IsTerm d Λ → IsLat L Λ → ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o = Quotient.mk'' Λ → S.IsTerm d o.out ∧ (∃ h ∈ S.St, o.out = h • Λ) ∧ (if S.IsTerm d o.out ∧ P o.out then (S.mu o.out : ℂ) * S.om d o.out else 0) = (if P Λ then (S.mu Λ : ℂ) * S.om d Λ else 0) ∧ (if S.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (S.mu o.out) else 0) = (if P Λ then ENNReal.ofReal (S.mu Λ) else 0) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hP Λ hT hL o ho
  have hrel : MulAction.orbitRel S.St (Submodule L.O S.V) o.out Λ := by
    have h1 : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) = Quotient.mk'' Λ :=
      (Quotient.out_eq' o).trans ho
    exact Quotient.exact' h1
  obtain ⟨g, hg⟩ := hrel
  have hout : o.out = (g : S.GLV) • Λ := by rw [← hg]; rfl
  have hgm : (g : S.GLV) ∈ S.St := g.2
  obtain ⟨hT', hom, -⟩ := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT _ hgm
  have hmu : S.mu ((g : S.GLV) • Λ) = S.mu Λ := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ hL |>.2.2 _ hgm
  have hPg : P ((g : S.GLV) • Λ) ↔ P Λ := hP Λ _ hgm
  refine ⟨hout ▸ hT', ⟨_, hgm, hout⟩, ?_, ?_⟩
  · rw [hout]; simp only [hT', true_and, hPg, hmu, hom]
  · rw [hout]; simp only [hT', true_and, hPg, hmu]
end GlobalTheory.HL
