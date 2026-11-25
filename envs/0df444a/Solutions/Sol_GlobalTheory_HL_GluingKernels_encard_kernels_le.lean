-- Prove2me | solution 1 for GlobalTheory.HL.GluingKernels.encard_kernels_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:52.286311+00:00
-- url     : https://prove2.me/submissions/fe26ba35-94c5-479d-ba1a-2dd9cd3f431c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGluingHomomorphismDefectGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardGluingHomKernelsLe
import Theorems.Thm_GlobalTheory_HL_GluingKernels_encard_le_of_param
import Theorems.Thm_GlobalTheory_HL_GluingKernels_sat_gens
import Theorems.Thm_GlobalTheory_HL_GluingKernels_tauRel_sum
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameClass_frame_classes
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_mem
import Theorems.Thm_GlobalTheory_SubmoduleCount_card_submodule_and_hom_le
import Theorems.Thm_GlobalTheory_T_exists_gluing_homomorphism_defect_group
import Theorems.Thm_GlobalTheory_T_term_exponents_nonneg_and_defect_group_bound
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GluingKernels
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.GluingKernels
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (Mh : Submodule L.O S.V) (j : ℕ), ((((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) '' {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}).encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d C Mh j
  rcases Set.eq_empty_or_nonempty
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j} with h0 | ⟨Λ₀, h₀, hC₀, hM₀, -⟩
  · rw [h0]; simp
  obtain ⟨-, -, -, -, -, b, -, hb⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ₀ h₀
  obtain ⟨-, -, -, -, -, ⟨i₀, hi₀, hbe⟩, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  let M₀ : Submodule L.O Mh := (S.M d Λ₀).comap Mh.subtype
  have hcard : Nat.card (Mh ⧸ M₀) = S.q ^ i₀ := by
    rw [← hbe, Frames.be, hM₀]
    rfl
  haveI : Finite (Mh ⧸ M₀) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨g, hg⟩ := sat_gens S d Λ₀ h₀
  rw [hM₀] at hg
  have hgm : ∀ i, g i ∈ Mh := fun i => by rw [hg]; exact Submodule.subset_span ⟨i, rfl⟩
  have hgen : Submodule.span L.O (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) = ⊤ := by
    have h1 : Submodule.span L.O (Set.range fun i => (⟨g i, hgm i⟩ : Mh)) = ⊤ := by
      apply Submodule.map_injective_of_injective Mh.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
      exact hg.symm
    have h2 : (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) =
        M₀.mkQ '' Set.range fun i => (⟨g i, hgm i⟩ : Mh) := by
      rw [← Set.range_comp]; rfl
    rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]
  have hsub := (GlobalTheory.SubmoduleCount.card_submodule_and_hom_le L (Mh ⧸ M₀) _ _ hgen).1
  have key := encard_le_of_param (R := L.O) (k - 1) j
    (fun x : Fin (k - 1) → Mh ⧸ M₀ =>
      (LinearMap.ker (Fintype.linearCombination L.O x)).map (Fintype.linearCombination L.O b))
    ((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) ''
      {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}) (by
    rintro _ ⟨Λ, ⟨hΛ, hC, hM, hj⟩, rfl⟩
    obtain ⟨t1, t2, -, t4, t5, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
    rw [hM] at t1 t5
    have hMM : S.M d Λ = S.M d Λ₀ := by
      have hmem : (S.fr d Λ, S.fr' d Λ) ∈ S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) := by
        have := (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
        have h2 : S.frameCls (S.fr d Λ) (S.fr' d Λ) = S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) :=
          hC.trans hC₀.symm
        rwa [h2] at this
      exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 _ hmem).2
    have hbL : ∀ i, b i ∈ S.complementLatticeOfDatum d := fun i => by
      rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩
    choose y hy hty using fun i => t1 (b i) (hbL i)
    refine ⟨((S.Ihat d Λ).comap Mh.subtype).map M₀.mkQ, ?_, fun i => M₀.mkQ ⟨y i, hy i⟩, ?_, ?_⟩
    · rw [← hj, Frames.cardI, hMM,
        ← AddSubgroup.relIndex_addSubgroupOf (L := Mh.toAddSubgroup) t5]
      have hk : (S.M d Λ₀).toAddSubgroup.addSubgroupOf Mh.toAddSubgroup =
          M₀.mkQ.toAddMonoidHom.ker := by
        ext x
        exact (Submodule.Quotient.mk_eq_zero M₀).symm
      rw [hk, AddSubgroup.relIndex_ker]
      rfl
    · intro i
      exact ⟨⟨y i, hy i⟩, Submodule.mem_sup_right (Submodule.subset_span ⟨b i, hbL i, hty i⟩), rfl⟩
    · have hz : ∀ c : Fin (k - 1) → L.O,
          Fintype.linearCombination L.O (fun i => M₀.mkQ ⟨y i, hy i⟩) c = 0 ↔
            S.TauRel d Λ (∑ i, c i • b i) 0 := by
        intro c
        rw [t2 _ _ 0 (tauRel_sum S d Λ hΛ Finset.univ c b y hty), sub_zero, hMM,
          Fintype.linearCombination_apply]
        simp only [← map_smul, ← map_sum]
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        simp [M₀]
      ext w
      simp only [Submodule.mem_map, LinearMap.mem_ker, hz, Submodule.mem_inf,
        Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hL : ∑ i, c i • b i ∈ S.complementLatticeOfDatum d := by
          rw [hb]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        rw [Fintype.linearCombination_apply]
        exact ⟨(t4 _ hL.1).2 ⟨hL, hc⟩, hL.1⟩
      · rintro ⟨hw, hw0⟩
        obtain ⟨hL, ht⟩ := (t4 w hw0).1 hw
        rw [hb] at hL
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hL
        exact ⟨c, ht, Fintype.linearCombination_apply _ _ _⟩)
  have hN : Nat.card (Submodule L.O (Mh ⧸ M₀)) * j ^ (k - 1) ≤
      S.q ^ (S.a.toNat * (2 * r + 2)) * j ^ (k - 1) := by
    refine Nat.mul_le_mul_right _ (hsub.trans ?_)
    rw [hcard, ← pow_mul]
    refine Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have h3 := key.trans (Nat.cast_le.2 hN)
  have h4 := ENat.toENNReal_le.2 h3
  simpa using h4
end GlobalTheory.HL.GluingKernels
