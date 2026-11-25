-- Prove2me | solution 1 for GlobalTheory.MoveFine.Mv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:40.078234+00:00
-- url     : https://prove2.me/submissions/ac32b4b8-6a0c-482e-af59-89809ed5ce19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_lev_add
import Theorems.Thm_GlobalTheory_MoveFine_coords
import Theorems.Thm_GlobalTheory_MoveFine_smul_memO
import Theorems.Thm_GlobalTheory_MoveFine_algO
import Theorems.Thm_GlobalTheory_MoveFine_p_eq_th
import Theorems.Thm_GlobalTheory_MoveFine_mem_lin
import Theorems.Thm_GlobalTheory_MoveFine_mem_intP
import Theorems.Thm_GlobalTheory_MoveFine_sOf_tr
import Theorems.Thm_GlobalTheory_MoveFine_Mv_lin
import Theorems.Thm_GlobalTheory_MoveFine_sOf_diff
import Theorems.Thm_GlobalTheory_MoveFine_p_unit
import Theorems.Thm_GlobalTheory_MoveFine_inTh_pow
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameOnto_coords
import Theorems.Thm_GlobalTheory_T_hermitian_double_coset_term_basic_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.MoveFine
theorem _root_.solution {J : ℕ} (hJ : J ≤ r + 1) {d : S.Datum} {Λ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (A : ℕ)
    (hA : algebraMap F E ((S.ϖ : F) ^ S.a) = algebraMap F E S.ϖ ^ A) (n v : ℕ)
    (hv : algebraMap F E S.ϖ ^ v * algebraMap F E 2⁻¹ ∈ L.O) (w y : S.MW) (hw : S.Mv J d Λ w)
    (hy : y ∈ intP S Λ) (hl : algebraMap F E S.ϖ ^ (n + A + 1 + v) • y ∈ lin S J) :
    S.Mv J d Λ (w + algebraMap F E S.ϖ ^ (n + A + 1 + v) • y) := by
  obtain ⟨hΛ, -, -, hf, hf', -⟩ := GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT
  have hp := fun n => L.O.pow_mem (algO S S.ϖ) n
  have hl' := AddSubgroup.add_mem _ (Mv_lin S hw) hl
  obtain ⟨-, -, ⟨y0, hy0, e0⟩, hlev, hu, -, ⟨c, hc, es⟩, -⟩ := hw
  obtain ⟨z, hz, ez⟩ := sOf_diff S hΛ (n + A + 1) v hv w y hu hy
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (mem_intP S).1 hy
  have hN : n + A + 1 + v = (n + A + v) + 1 := by ring
  have hsum : (w + algebraMap F E S.ϖ ^ (n + A + 1 + v) • y).1.1 + (w + algebraMap F E S.ϖ ^ (n + A + 1 + v) • y).1.2
      = (w.1.1 + w.1.2) + algebraMap F E S.ϖ ^ (n + A + 1 + v) • (y.1.1 + y.1.2) := by
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, smul_add]; abel
  refine ⟨hl'.1.1, hl'.1.2, ?_, ?_, Λ.add_mem hu (smul_memO S (hp _) h3), hl'.2.1, ?_, ?_⟩
  · obtain ⟨y1, hy1, e1⟩ := inTh_pow S (n + A + v) (Λ.add_mem h1 h2)
    exact ⟨y0 + y1, Λ.add_mem hy0 hy1, by rw [hsum, e0, hN, e1, smul_add]⟩
  · obtain ⟨a, ha, ea⟩ := coords S _ _ _ ((hf J hJ _).1
      ⟨h1, (Submodule.smul_mem_iff_of_isUnit _ (p_unit S _)).1 hl.1.1⟩)
    obtain ⟨a', ha', ea'⟩ := coords S _ _ _ ((hf' J hJ _).1
      ⟨h2, (Submodule.smul_mem_iff_of_isUnit _ (p_unit S _)).1 hl.1.2⟩)
    obtain ⟨e, he, h⟩ := p_eq_th S
    rw [hsum, ← hlev, ← lev_add S (S.fr d Λ) (S.fr' d Λ) (w.1.1 + w.1.2)
      (fun i => algebraMap F E S.ϖ ^ (n + A + 1 + v) * a i) (fun i => algebraMap F E S.ϖ ^ (n + A + 1 + v) * a' i)]
    · congr 2
      rw [ea, ea']
      simp only [smul_add, Finset.smul_sum, mul_smul]
    · intro i
      refine ⟨L.O.mul_mem (hp _) (ha' i), e * algebraMap F E S.ϖ ^ (n + A + v) * (a i + a' i),
        L.O.mul_mem (L.O.mul_mem he (hp _)) (L.O.add_mem (ha i) (ha' i)), ?_⟩
      rw [← mul_assoc, ← mul_assoc, ← h]; ring
  · refine ⟨c + algebraMap F E S.ϖ ^ (n + 1) * z, L.O.add_mem hc (L.O.mul_mem (hp _) hz), ?_⟩
    rw [eq_add_of_sub_eq ez, es, hA]; ring
  · rw [sOf_tr, ((mem_lin S).1 hl').2.2, add_zero]
end GlobalTheory.MoveFine
