-- Prove2me | solution 1 for GlobalTheory.PairOp.sum_units_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:50.213127+00:00
-- url     : https://prove2.me/submissions/d98a2768-bfc5-47fb-a4aa-d337ad2250ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
namespace GlobalTheory.PairOp
theorem _root_.solution [Fintype 𝓀[k]ˣ] (hχ : χ ≠ 1) (a : 𝓀[k]) [Decidable (a = 0)] :
    ∑ d : 𝓀[k]ˣ, χ (d * a) = (if a = 0 then (resCard k : ℂ) else 0) - 1 := by
  classical
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  have hsplit : ∀ f : 𝓀[k] → ℂ, ∑ d : 𝓀[k]ˣ, f d = ∑ x : 𝓀[k], f x - f 0 := by
    intro f
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : 𝓀[k])), add_sub_cancel_right]
    exact Finset.sum_bij' (fun d _ => (d : 𝓀[k])) (fun x hx => Units.mk0 x (Finset.ne_of_mem_erase hx))
      (fun d _ => Finset.mem_erase.mpr ⟨d.ne_zero, Finset.mem_univ _⟩) (fun x _ => Finset.mem_univ _)
      (fun d _ => Units.ext rfl) (fun x _ => rfl) (fun d _ => rfl)
  rw [hsplit (fun x => χ (x * a)), zero_mul, AddChar.map_zero_eq_one]
  split_ifs with ha
  · subst ha
    simp [resCard, Nat.card_eq_fintype_card]
  · have hz : ∑ x : 𝓀[k], χ (x * a) = 0 := by
      rw [← AddChar.sum_eq_zero_of_ne_one hχ]
      exact Fintype.sum_bijective (· * a) (mulRight_bijective₀ a ha) _ _ fun x => rfl
    rw [hz, zero_sub]
end GlobalTheory.PairOp
