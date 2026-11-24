-- Prove2me | solution 1 for GlobalTheory.CapelliTop.prod_add_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:08:19.760902+00:00
-- url     : https://prove2.me/submissions/59109bb1-81dd-427d-9c6c-70b406271a5b

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}
namespace GlobalTheory.CapelliTop
theorem _root_.solution [Algebra ℂ A] (c : Fin n → ℂ) (e : Fin n → A) :
    (List.ofFn fun k => c k • (1 : A) + e k).prod =
      ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, c k) • oprod S e := by
  have h := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_add_univ e (fun k => c k • (1 : A))
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at h
  have h0 : (fun k => c k • (1 : A) + e k) = e + fun k => c k • (1 : A) := by
    funext k; simp [add_comm]
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_smul_univ (fun k => if k ∈ S then 1 else c k)
    (fun k => if k ∈ S then e k else 1)
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at h1
  have h2 : S.piecewise e (fun k => c k • (1 : A)) =
      fun k => (if k ∈ S then (1 : ℂ) else c k) • (if k ∈ S then e k else 1) := by
    funext k; by_cases hk : k ∈ S <;> simp [hk]
  rw [h2, h1, oprod]
  congr 1
  rw [← Finset.prod_mul_prod_compl S, Finset.prod_eq_one (s := S) (fun k hk => by simp [hk]), one_mul]
  exact Finset.prod_congr rfl fun k hk => by simp [Finset.mem_compl.1 hk]
end GlobalTheory.CapelliTop
