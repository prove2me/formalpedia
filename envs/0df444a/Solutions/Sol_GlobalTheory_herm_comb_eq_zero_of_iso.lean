-- Prove2me | solution 1 for GlobalTheory.herm_comb_eq_zero_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:01.487934+00:00
-- url     : https://prove2.me/submissions/34773fcb-c0e2-49db-bf8c-61bfbc7b83a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCuspPseudoBasisAdaptedLattice
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (e : Fin ρ → Fin r → E)
    (h : ∀ a b, herm G (e a) (e b) = 0) (u v : Fin ρ → E) :
    herm G (∑ i, u i • e i) (∑ j, v j • e j) = 0 := by
  have key : herm G (∑ i, u i • e i) (∑ j, v j • e j)
      = ∑ i, ∑ j, u i * cc (v j) * herm G (e i) (e j) := by
    have h1 : ∀ (y : Fin r → E), herm G (∑ i, u i • e i) y = ∑ i, u i * herm G (e i) y := by
      intro y
      simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∀ (x : Fin r → E), herm G x (∑ j, v j • e j) = ∑ j, cc (v j) * herm G x (e j) := by
      intro x
      simp only [herm, cc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [h1, h2, Finset.mul_sum, mul_assoc]
  rw [key]
  simp [h]
end GlobalTheory
