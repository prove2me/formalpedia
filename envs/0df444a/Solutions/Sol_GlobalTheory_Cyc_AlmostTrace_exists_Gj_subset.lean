-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.exists_Gj_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:42:51.893153+00:00
-- url     : https://prove2.me/submissions/90c95699-7d48-4172-854b-0fc243c45e0c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_mono
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_exists_mem_Ks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AlmostTrace
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.AlmostTrace
theorem _root_.solution (K : FinExt l) {U : Set (GQ l)} (hU : IsOpen U)
    (hH : (Hinf K : Set (GQ l)) ⊆ U) : ∃ i₀, ∀ i ≥ i₀, (Gj K i : Set (GQ l)) ⊆ U := by
  have hcl : ∀ i, IsClosed ((Gj K i : Set (GQ l))) := fun i =>
    InfiniteGalois.fixingSubgroup_isClosed (Ks K i)
  have hanti : Antitone fun i => ((Gj K i : Set (GQ l))) := fun i j hij =>
    IntermediateField.fixingSubgroup_antitone (Ks_mono K hij)
  have hinter : Uᶜ ∩ ⋂ i, (Gj K i : Set (GQ l)) = ∅ := by
    ext σ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hσU, hσ⟩
    apply hσU
    apply hH
    show σ ∈ (Kinf K).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_Ks K hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Set.mem_iInter.1 hσ i) x hi
  obtain ⟨i₀, hi₀⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun i => (Gj K i : Set (GQ l))) hcl hinter hanti.directed_ge
  refine ⟨i₀, fun i hi σ hσ => ?_⟩
  by_contra hσU
  have hmem : σ ∈ Uᶜ ∩ (Gj K i₀ : Set (GQ l)) := ⟨hσU, hanti hi hσ⟩
  rw [hi₀] at hmem
  exact hmem
end GlobalTheory.Cyc.AlmostTrace
