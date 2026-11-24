-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.finite_image_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:09.552103+00:00
-- url     : https://prove2.me/submissions/f939a432-3d38-423d-a739-6b1c8bf08acc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] (H U : Subgroup A)
    (hU : IsOpen (U : Set A)) {Ω : Set A} (hΩ : IsCompact Ω) : (DoubleCoset.mk H U '' Ω).Finite := by
  obtain ⟨t, -, ht, hc⟩ := hΩ.elim_finite_subcover_image (b := Ω) (c := fun a => (fun z => a⁻¹ * z) ⁻¹' (U : Set A))
    (fun a _ => hU.preimage (continuous_const.mul continuous_id))
    (fun a ha => Set.mem_biUnion ha (by simp))
  refine (ht.image (DoubleCoset.mk H U)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨a, ha, haz⟩ := Set.mem_iUnion₂.1 (hc hz)
  exact ⟨a, ha, (DoubleCoset.eq H U a z).2 ⟨1, one_mem _, a⁻¹ * z, haz, by simp⟩⟩
end GlobalTheory.FunObj.FiniteSupport
