-- Prove2me | solution 1 for GlobalTheory.JacquetExact.mem_twKer_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:23:24.70673+00:00
-- url     : https://prove2.me/submissions/3b9e4612-6401-4b1a-beec-f2a603f42c5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
import Theorems.Thm_GlobalTheory_JacquetExact_map_mem_twKer
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_IwahoriInj_eq_zero_of_fixed
import Theorems.Thm_GlobalTheory_IwahoriInj_mem_fixed
import Theorems.Thm_GlobalTheory_IwahoriInj_sub_mem_twKer
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_isSmooth
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_injective
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq
import Theorems.Thm_UpperTheory_Reformulated_B_TwistedKernelFixed_eq_zero_of_fixed


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
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.JacquetExact
theorem _root_.solution {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {v : V} (hv : f v ∈ twKer τ H 1) : v ∈ twKer σ H 1 := by
  have hσ : IsSmooth σ := (IsSubquotient.of_injective f hf).isSmooth hτ
  obtain ⟨v', hv', he⟩ := IwahoriOnto.exists_fixed_map_eq hσ hH (twKer σ H 1).mkQ v fun h hh =>
    (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer hh v)
  have h1 : v' - v ∈ twKer σ H 1 := (Submodule.Quotient.eq _).1 he
  have h2 : f v' ∈ twKer τ H 1 := by
    have := add_mem (map_mem_twKer f h1) hv
    rwa [map_sub, sub_add_cancel] at this
  have h3 : f v' ∈ fixed τ H := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => by
    rw [← f.isIntertwining, GlobalTheory.IwahoriInj.mem_fixed.1 hv' h hh]
  have h4 : v' = 0 := hf ((GlobalTheory.IwahoriInj.eq_zero_of_fixed hτ hH h3 h2).trans (map_zero f).symm)
  rw [h4, zero_sub] at h1
  exact neg_mem_iff.1 h1
end GlobalTheory.JacquetExact
