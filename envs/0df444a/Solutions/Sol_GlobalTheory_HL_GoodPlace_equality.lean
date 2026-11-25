-- Prove2me | solution 1 for GlobalTheory.HL.GoodPlace.equality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:00:08.783979+00:00
-- url     : https://prove2.me/submissions/a9bbcded-28da-4420-9b88-23342db5f90c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMassEqSumFrameClasses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralOfMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_Equality
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FlagUnipotent_main
import Theorems.Thm_GlobalTheory_FrameAct_stabiliser_acts_on_terms
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameGram_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_HL_Defect_exponents_and_defect
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_main
import Theorems.Thm_GlobalTheory_HL_GoodClass_one_class
import Theorems.Thm_GlobalTheory_HL_StabConj_main
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_HL_UnimodTerm_term_unique
import Theorems.Thm_GlobalTheory_HL_WitIndep_witness_independence
import Theorems.Thm_GlobalTheory_HL_mass_eq_sumCls
import Theorems.Thm_GlobalTheory_HL_volSt
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
import Theorems.Thm_GlobalTheory_PowMulMemOrder_main
import Theorems.Thm_GlobalTheory_PowSmulMem_main
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_norm
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodPlace
namespace GlobalTheory.HL.GoodPlace
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.gg = false → vE L S.ϖ S.G = 0 → (∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0) → (∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ) ∧ S.Hp = 1 ∧ (S.ampSq fun _ _ => True) = S.nn ∧ ∀ d, (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ hgg hG hD
  have hvth : S.vth = 0 := by simp [Frames.vth, hgg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hG]
  have hvD : S.vD = 0 := Finset.sum_eq_zero fun l _ => by
    split_ifs with h
    · exact hD l h.2
    · rfl
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  have key : ∀ d, ((S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1) ∧
      ENNReal.ofReal (‖S.amp d fun _ => True‖ ^ 2) = S.mass d fun _ => True := by
    intro d
    by_cases hex : ∃ Λ, S.IsTerm d Λ
    swap
    · have h0 : ∀ Λ, ¬ S.IsTerm d Λ := fun Λ h => hex ⟨Λ, h⟩
      simp [Frames.mass, Frames.amp, h0]
    obtain ⟨Λ₀, h₀⟩ := hex
    obtain ⟨-, -, hDO, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀
    obtain ⟨-, -, -, -, hDu, -⟩ := GlobalTheory.FrameBasic.main L r k S
    obtain ⟨-, -, -, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
    have hunit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1 := by
      intro l hl
      refine ⟨hDO l, ?_⟩
      obtain ⟨e, he⟩ := GlobalTheory.UnramOrder.exists_norm L (hDO l)
      have he0 : (e : F) ≠ 0 := fun h0 => by
        rw [h0, map_zero] at he
        apply hl
        rw [← L.cj_cj (S.D l), (hDu l hl).mul_right_eq_zero.1 he, map_zero]
      obtain ⟨u, hu⟩ := hvu _ he0
      rw [← he, hD l hl, zpow_zero, one_mul] at hu
      refine ⟨L.cj (S.D l) * algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F),
        L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem L (hDO l))
          ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subtype.property _)), ?_⟩
      rw [← mul_assoc, he, ← map_mul, hu, ← Subring.coe_mul, Units.mul_inv]
      simp
    obtain ⟨hC0, hw0, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hunit
    set C0 := S.frameCls S.f S.f' with hC0def
    have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d
    have hint : ∀ Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun Λ h =>
      (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1

    have hm : (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
      rw [mass_eq_sumCls L r k S d _ (fun _ _ _ _ _ => trivial)]
      unfold Frames.sumCls
      let o₀ : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C0
      rw [tsum_eq_single o₀ (fun o ho => if_neg fun hI => ho (by
        obtain ⟨h, hh, e⟩ := hall _ hI
        rw [← Quotient.out_eq o]
        exact Quotient.sound ⟨⟨h, hh⟩, e.symm⟩))]
      split_ifs with hI
      swap
      · exact Or.inl rfl
      obtain ⟨h, hh, e⟩ := hall _ hI
      have hw : S.wC o₀.out = 1 := by
        rw [e, ((volSt L r k S).2 C0 hC0.1).2.2.2 h hh, hw0]
      rw [hw, ENNReal.ofReal_one, one_mul]
      have hs : ({Λ | S.IsTerm d Λ ∧ True ∧ S.Fr d Λ = o₀.out} : Set (Submodule L.O S.V)).Subsingleton :=
        fun Λ hΛ Λ' hΛ' => (huniq d Λ' hΛ'.1).2 Λ hΛ.1 (hΛ.2.2.trans hΛ'.2.2.symm)
      unfold Frames.nT
      beta_reduce
      rcases hs.eq_empty_or_singleton with h1 | ⟨x, h1⟩
      · left; rw [h1]; simp
      · right; rw [h1]; simp
    refine ⟨hm, ?_⟩

    let o₁ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk _ Λ₀
    have hone : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o ≠ o₁ →
        ¬ (S.IsTerm d o.out ∧ True) := by
      intro o ho hT
      apply ho
      obtain ⟨h, hh, e⟩ := hall _ (hint _ hT.1)
      obtain ⟨h', hh', e'⟩ := hall _ (hint _ h₀)
      have hmem : h * h'⁻¹ ∈ S.St := S.St.mul_mem hh (S.St.inv_mem hh')
      have hA := hact Λ₀ h₀ _ hmem
      have e2 : (h * h'⁻¹) • Λ₀ = o.out := (huniq d _ hT.1).2 _ hA.1 (by
        rw [hA.2.2.2.2.1, e', e, smul_smul, inv_mul_cancel_right])
      rw [← Quotient.out_eq o]
      exact Quotient.sound ⟨⟨_, hmem⟩, e2⟩
    have e1 : (S.mass d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then ENNReal.ofReal (S.mu o₁.out) else 0 := by
      unfold Frames.mass
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    have e2 : (S.amp d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then (S.mu o₁.out : ℂ) * S.om d o₁.out else 0 := by
      unfold Frames.amp
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    rw [e1] at hm ⊢
    rw [e2]
    by_cases hT : S.IsTerm d o₁.out ∧ True
    swap
    · simp only [if_neg hT]; simp
    simp only [if_pos hT] at hm ⊢
    have hom : ‖S.om d o₁.out‖ = 1 := by
      obtain ⟨p, hp⟩ := hT.1
      exact (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have hmu : 0 ≤ S.mu o₁.out := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rw [norm_mul, hom, mul_one, Complex.norm_real, Real.norm_of_nonneg hmu]
    rcases hm with h | h
    · rw [le_antisymm (ENNReal.ofReal_eq_zero.1 h) hmu]; simp
    · rw [ENNReal.ofReal_eq_one.1 h]; simp
  refine ⟨fun d Λ h => (huniq d Λ h).1, by simp [Frames.Hp, hvth, ha, hvD], ?_, fun d => (key d).1⟩
  unfold Frames.ampSq Frames.nn
  congr 1
  funext d
  exact (key d).2
end GlobalTheory.HL.GoodPlace
