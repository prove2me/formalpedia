-- Prove2me | solution 1 for GlobalTheory.JacquetExact.jacMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:33:49.377705+00:00
-- url     : https://prove2.me/submissions/347f0d9e-396f-4862-8de6-89a07b38a150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
import Theorems.Thm_GlobalTheory_JacquetExact_exists_finset_of_mem_twKer
import Theorems.Thm_GlobalTheory_JacquetExact_mem_twKer_of_compact
import Theorems.Thm_GlobalTheory_InertSupp_unipRad_eq_unipOf
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_IwahoriInj_twKer_mono
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_UnipCompact_exists_compact_subgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.JacquetExact
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {s : ℕ} {d : Fin s → ℕ}
namespace GlobalTheory.JacquetExact
theorem _root_.solution (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (jacMap e f) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  have hN : unipRad k e = unipOf k fun i => ((blk e i).val : ℤ) :=
    unipRad_eq_unipOf k fun i j => by simp
  obtain ⟨S, hS, h2⟩ := exists_finset_of_mem_twKer h1
  obtain ⟨H, hle, hH, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup k n _ S (hN ▸ hS)
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge) (mem_twKer_of_compact hτ f hf hH (h2 H hSH))
end GlobalTheory.JacquetExact
