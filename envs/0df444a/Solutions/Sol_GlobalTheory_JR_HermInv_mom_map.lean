-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mom_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:24.69758+00:00
-- url     : https://prove2.me/submissions/02cd0e19-639e-4595-8524-ae32e24addd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_pow_r_mulVec
import Theorems.Thm_GlobalTheory_JR_HermInv_mom_add_r
import Theorems.Thm_GlobalTheory_JR_HermInv_seq_eq
import Theorems.Thm_GlobalTheory_JR_HermInv_sec_rec
import Theorems.Thm_GlobalTheory_JR_HermInv_mom_sec_lt
import Theorems.Thm_GlobalTheory_JR_HermInv_hasInv_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (X : Hn r F E) (a : Inv r F) (h : HasInv X a) (n : ℕ) :
    mom X.toGl n = algebraMap F E (mom (sec a) n) := by
  obtain ⟨h1, h2, -⟩ := (hasInv_iff X a).1 h
  have hq : X.toGl.1 ^ r *ᵥ X.toGl.2.1 = -(Bm X.toGl *ᵥ fun i => algebraMap F E (a.1 i)) := by
    have := pow_r_mulVec X.toGl
    rwa [show (fun i : Fin r => X.toGl.1.charpoly.coeff i) = fun i => algebraMap F E (a.1 i) from funext h1] at this
  have hS : ∀ k, algebraMap F E (mom (sec a) (k + r)) =
      -((fun j : Fin r => algebraMap F E (mom (sec a) (k + j))) ⬝ᵥ fun i => algebraMap F E (a.1 i)) := by
    intro k
    rw [sec_rec]
    simp [dotProduct, map_sum, map_mul]
  have := seq_eq (u := fun n => mom X.toGl n) (v := fun n => algebraMap F E (mom (sec a) n)) _
    (mom_add_r X.toGl _ hq) hS (fun k hk => by
      have e1 := h2 ⟨k, hk⟩
      have e2 := mom_sec_lt a ⟨k, hk⟩
      simp only at e1 e2 ⊢
      rw [e1, e2])
  exact congrFun this n
end GlobalTheory.JR.HermInv
