-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.sqfreeO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:46.384805+00:00
-- url     : https://prove2.me/submissions/d92fddc1-d73c-4c23-99d3-4b2f37c24bb8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_labO_eq_of_cuspIso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_cuspIso_of_labO_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_fiber_nonempty
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_injective_of_squarefree_prod
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_exists_equiv_factors
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_labO_spec
import Theorems.Thm_PI_GreenLabelSurjWork_transp_cusp
import Theorems.Thm_PI_GreenLabelSurjWork_transp_simple


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin PI.GreenLabelSurjWork
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Mirrors
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]
namespace GlobalTheory.CompanionTheory.TyFin.Mirrors
theorem _root_.solution (hC : SqfreeCore K) (O : LabelMap K C) (hP : CuspParamO O) : SqfreeO O := by
  obtain ⟨hI, hD, hU⟩ := hC
  refine ⟨?_, ?_⟩
  · intro n s b lam hb hl hinj
    refine ⟨hI n s b lam hb hl fun c c' h => hinj (labO_eq_of_cuspIso O (hl c).1 (hl c').1 h), ?_⟩
    refine hD n s b lam hb fun c => ?_
    haveI := fiber_nonempty hb c
    exact (hP (Fintype.card {i // b i = c}) Fintype.card_pos).2
      (transp (Fintype.equivFin _) (lam c)) (transp_simple _ _ (hl c).1) (transp_cusp _ _ (hl c).2)
  · rintro n f τ τ' hf hτ hτ' ⟨s, b, lam, hb, hl, hc, rfl⟩ ⟨s', b', mu, hb', hl', hc', hf'⟩
    have sp : ∀ c, (labO O (lam c)).Monic ∧ Irreducible (labO O (lam c)) := fun c =>
      haveI := fiber_nonempty hb c
      labO_spec O (hl c).1 (hl c).2
    have sp' : ∀ c, (labO O (mu c)).Monic ∧ Irreducible (labO O (mu c)) := fun c =>
      haveI := fiber_nonempty hb' c
      labO_spec O (hl' c).1 (hl' c).2
    have hj : Function.Injective fun c => labO O (lam c) :=
      injective_of_squarefree_prod (fun c => (sp c).2) hf
    have hj' : Function.Injective fun c => labO O (mu c) :=
      injective_of_squarefree_prod (fun c => (sp' c).2) (hf' ▸ hf)
    obtain ⟨π, hπ⟩ := exists_equiv_factors (fun c => (sp c).2) (fun c => (sp c).1)
      (fun c => (sp' c).2) (fun c => (sp' c).1) hj hj' hf'
    refine hU n s s' b b' lam mu τ τ' hτ hτ' ⟨hb, hl, hc⟩ ⟨hb', hl', hc'⟩
      (fun c c' h => hj (labO_eq_of_cuspIso O (hl c).1 (hl c').1 h)) ⟨π, fun c => ?_⟩
    haveI := fiber_nonempty hb c
    haveI := fiber_nonempty hb' (π c)
    exact cuspIso_of_labO_eq O (hl c).1 (hl c).2 (hl' _).1 (hl' _).2 (hπ c).symm
end GlobalTheory.CompanionTheory.TyFin.Mirrors
