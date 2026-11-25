-- Prove2me | solution 1 for GlobalTheory.HL.MassOrbit.mass_orbit_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:21.408965+00:00
-- url     : https://prove2.me/submissions/f2624b70-ae5f-440f-b47b-cc18b59a0a8e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMassEqSumFrameClasses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitClass
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameAct_stabiliser_acts_on_terms
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_HL_mass_eq_sumCls
import Theorems.Thm_GlobalTheory_HL_volSt
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MassOrbit
namespace GlobalTheory.HL.MassOrbit
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d₁ : S.Datum) (Λ₁ : Submodule L.O S.V)
    (h₁ : S.IsTerm d₁ Λ₁) (d : S.Datum) :
    (S.mass d fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • S.Fr d₁ Λ₁) =
      ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ := by
  have act := @GlobalTheory.FrameAct.stabiliser_acts_on_terms F _ _ _ _ _ E _ _ _ L r k S
  have trm := @GlobalTheory.HL.TermBasic.term_basic F _ _ _ _ _ E _ _ _ L r k S
  have vol := (@GlobalTheory.HL.volSt F _ _ _ _ _ E _ _ _ L r k S).2
  have hT : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) := fun d Λ H h hh => (act d Λ H h hh).1
  have hF : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.Fr d (h • Λ) = h • S.Fr d Λ :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.1
  have hB : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.2.2.2.1
  have hI : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ H => (trm d Λ H).2.2.2.2.2.2.1
  rw [GlobalTheory.HL.mass_eq_sumCls L r k S d _ (by
    rintro h hh Λ H ⟨hb, s, hs, e⟩
    refine ⟨(hB d Λ H h hh).2 hb, h * s, S.St.mul_mem hh hs, ?_⟩
    rw [hF d Λ H h hh, e, mul_smul])]
  set C₁ := S.Fr d₁ Λ₁ with hC
  unfold Frames.sumCls
  rw [tsum_eq_single (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁)]
  · have hrel : (MulAction.orbitRel S.St (Set S.FrP))
        (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out C₁ := Quotient.mk_out C₁
    obtain ⟨⟨h, hh⟩, e⟩ := MulAction.orbitRel_apply.1 hrel
    have e' : (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out = h • C₁ := e.symm
    have hint : S.IsIntCls (h • C₁) := by
      rw [hC, ← hF d₁ Λ₁ h₁ h hh]
      exact hI _ _ (hT _ _ h₁ h hh)
    change (if S.IsIntCls (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out then
      ENNReal.ofReal (S.wC (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out) *
        S.nT d (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out _ else 0) = _
    rw [e', if_pos hint, (vol C₁ (hI _ _ h₁).1).2.2.2 h hh]
    congr 1
    unfold Frames.nT
    congr 1
    have hset : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = h • C₁} =
        (fun Λ : Submodule L.O S.V => h • Λ) '' {Λ | S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C₁} := by
      ext Λ
      constructor
      · rintro ⟨H, ⟨hb, -⟩, e⟩
        have hi := S.St.inv_mem hh
        refine ⟨h⁻¹ • Λ, ⟨hT _ _ H _ hi, (hB _ _ H _ hi).2 hb, ?_⟩, smul_inv_smul h Λ⟩
        rw [hF _ _ H _ hi, e, inv_smul_smul]
      · rintro ⟨Λ', ⟨H, hb, e⟩, rfl⟩
        have e2 : S.Fr d (h • Λ') = h • C₁ := by rw [hF _ _ H _ hh, e]
        exact ⟨hT _ _ H _ hh, ⟨(hB _ _ H _ hh).2 hb, h, hh, e2⟩, e2⟩
    rw [hset]
    exact (MulAction.injective h).encard_image _
  · intro o ho
    have h0 : S.nT d o.out (fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) = 0 := by
      unfold Frames.nT
      have : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = o.out} = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨-, s, hs, e⟩, e2⟩
        apply ho
        rw [← Quotient.out_eq o]
        apply Quotient.sound
        exact MulAction.orbitRel_apply.2 ⟨⟨s, hs⟩, by rw [← e2, e]; rfl⟩
      rw [this]
      simp
    simp only [h0, mul_zero, ite_self]
end GlobalTheory.HL.MassOrbit
