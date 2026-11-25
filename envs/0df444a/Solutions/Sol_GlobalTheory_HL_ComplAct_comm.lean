-- Prove2me | solution 1 for GlobalTheory.HL.ComplAct.comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:12.957837+00:00
-- url     : https://prove2.me/submissions/a74d0ac3-b9ad-4d1d-8d2e-f3073280d8b1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Theorems.Thm_GlobalTheory_HL_ComplAct_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_ComplAct_nof_mem
import Theorems.Thm_GlobalTheory_HL_ComplAct_perp_map
import Theorems.Thm_GlobalTheory_HL_ComplAct_hermitianFrames_complementUnitary_fixes_ME
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ComplAct
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.ComplAct
theorem _root_.solution {h s : S.GLV} (hh : h ∈ S.H0) (hs : s ∈ S.St) : s * h = h * s := by
  obtain ⟨hli, hco, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hdis := (linearIndependent_sum.1 hli).2.2
  have hle : ∀ g : Fin (r + 1) → S.V, S.spanTo g r ≤ Submodule.span E (Set.range g) := fun g =>
    Submodule.span_mono (Set.image_subset_range _ _)
  have hW : ∀ w ∈ S.W0, s w = w := fun w hw => by
    have h1 := hs.1.2.2 w fun y hy => hw y (Submodule.mem_sup_left (spanTo_mono S _ hy))
    have h2 := hs.2.2.2 w fun y hy => hw y (Submodule.mem_sup_right (spanTo_mono S _ hy))
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hdis _ (hle _ h1) (hle _ h2))
  have hM : ∀ x ∈ S.ME, s x ∈ S.ME := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (nof_mem S (Or.inl ⟨rfl, rfl⟩) hs.1 ha)
      (nof_mem S (Or.inr ⟨rfl, rfl⟩) hs.2 hb)
  ext1 v
  have hv : v ∈ S.ME ⊔ S.W0 := by rw [hco.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  change s (h (a + b)) = h (s (a + b))
  rw [map_add, map_add, map_add, map_add, hermitianFrames_complementUnitary_fixes_ME S hh a ha, hermitianFrames_complementUnitary_fixes_ME S hh _ (hM a ha), hW b hb,
    hW _ (perp_map S hh.1 (hermitianFrames_complementUnitary_fixes_ME S hh) hb)]
end GlobalTheory.HL.ComplAct
