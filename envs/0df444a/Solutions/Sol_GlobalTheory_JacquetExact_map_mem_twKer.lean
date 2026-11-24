-- Prove2me | solution 1 for GlobalTheory.JacquetExact.map_mem_twKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:11.271744+00:00
-- url     : https://prove2.me/submissions/41dc60e1-1c98-475d-b2b0-361540b5f052

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient

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
namespace GlobalTheory.JacquetExact
theorem _root_.solution {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    {H : Subgroup G} {v : V} (hv : v ∈ twKer σ H 1) : f v ∈ twKer τ H 1 := by
  have h : twKer σ H 1 ≤ (twKer τ H 1).comap f.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, f v, ?_⟩
    simp [f.isIntertwining])
  exact h hv
end GlobalTheory.JacquetExact
