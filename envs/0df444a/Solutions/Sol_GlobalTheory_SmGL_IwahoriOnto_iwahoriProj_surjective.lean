-- Prove2me | solution 1 for GlobalTheory.SmGL.IwahoriOnto.iwahoriProj_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:15:45.433009+00:00
-- url     : https://prove2.me/submissions/83b93c06-674f-48ea-97e6-22f0400021d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_mk_eq
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_isOpen_iwahori
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_isCompact_iwahori
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_iwahori_factor
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_lowerInt_contract
import Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_normalizer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
namespace GlobalTheory.SmGL.IwahoriOnto
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] (V : Type)
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (hπ : IsAdmissible π) :
    Function.Surjective (iwahoriProj π) := by
  rintro ⟨y, hy⟩
  obtain ⟨v, hv, e⟩ := exists_fixed_mk_eq hπ (isOpen_iwahori k n) (isCompact_iwahori k n) (diagT k n)
    (N := unipB k n) (fun _ => leviEmb_mem_normalizer k (points n) _) (torusO k n)
    (fun _ => diagT_mem_iwahori) (lowerInt k n) (iwahori_factor k n) (lowerInt_contract k n) y hy
  exact ⟨⟨v, hv⟩, Subtype.ext e⟩
end GlobalTheory.SmGL.IwahoriOnto
