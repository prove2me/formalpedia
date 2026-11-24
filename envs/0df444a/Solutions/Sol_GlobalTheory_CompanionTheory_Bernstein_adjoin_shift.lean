-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bernstein.adjoin_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:30.073312+00:00
-- url     : https://prove2.me/submissions/16d8b848-ed02-46e2-a1fc-689a4ab5d711

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfMemAdjoin
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementCommutative
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bernstein
namespace GlobalTheory.CompanionTheory.Bernstein
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (μ : ℂ) :
    Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ) (fun i : Fin l => a i.succ) :
      Fin (l + 1) → Module.End ℂ V)) = Algebra.adjoin ℂ (Set.range a) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨0, rfl⟩) (Subalgebra.algebraMap_mem _ μ)
    · simp only [Fin.cons_succ]
      exact Algebra.subset_adjoin ⟨j.succ, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 : a 0 - algebraMap ℂ _ μ ∈ Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V)) :=
        Algebra.subset_adjoin ⟨0, by simp⟩
      have := Subalgebra.add_mem _ h0 (Subalgebra.algebraMap_mem (Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V))) μ)
      simpa using this
    · exact Algebra.subset_adjoin ⟨j.succ, by simp⟩
end GlobalTheory.CompanionTheory.Bernstein
