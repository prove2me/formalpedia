-- Prove2me | solution 1 for GlobalTheory.HL.GluingKernels.sat_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:42.164857+00:00
-- url     : https://prove2.me/submissions/bb246040-5bfe-4b2c-8de7-b61bab045c0e

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
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_mem
import Theorems.Thm_GlobalTheory_HL_FrameTri_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_OrderBasis_order_basis
import Theorems.Thm_GlobalTheory_T_frameLattice_gramDet_and_minors_orbit_invariant
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GluingKernels
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.GluingKernels
theorem _root_.solution (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) :
    ∃ b : Fin ((r + 1) + (r + 1)) → S.V, S.sat Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨hSD, hW, -, h1, h2, hli, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.1
  have hfg : (S.sat Λ).FG := by
    haveI : IsNoetherian L.O Λ := isNoetherian_of_fg_of_noetherian Λ hSD.1.1
    exact (isNoetherian_submodule.1 this) _ inf_le_left
  have hsp := (GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant L r k S _ hW.2.2.1 _ hW.2.2.2.1).2.2
  set y := Sum.elim (S.fr d Λ) (S.fr' d Λ) with hy
  have hr : Set.range (y ∘ finSumFinEquiv.symm) = Set.range y :=
    finSumFinEquiv.symm.surjective.range_comp y
  obtain ⟨b, -, hb⟩ := GlobalTheory.OrderBasis.order_basis L (y ∘ finSumFinEquiv.symm)
    (hli.comp _ finSumFinEquiv.symm.injective) (S.sat Λ) hfg (by
      rw [hr]
      apply le_antisymm
      · rw [Submodule.span_le]
        intro x hx
        have hx2 : x ∈ S.ME := hx.2
        rw [← hsp] at hx2
        refine (Submodule.span_le.2 ?_) hx2
        rintro _ ⟨i | i, rfl⟩
        · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
        · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
            (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
      · apply Submodule.span_mono
        rintro _ ⟨i | i, rfl⟩
        · have := (h1 (r + 1) le_rfl (S.fr d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_left this.2⟩
        · have := (h2 (r + 1) le_rfl (S.fr' d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_right this.2⟩)
  exact ⟨b, hb⟩
end GlobalTheory.HL.GluingKernels
