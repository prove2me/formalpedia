-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JStable.sum_extendByZero_fin_eq_sum_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:19.561802+00:00
-- url     : https://prove2.me/submissions/ac975af7-ca10-4bf3-8318-1bec92b31cb2

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace
import Theorems.Thm_GlobalTheory_CompanionTheory_JStable_extendByZero_apply_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JStable
variable {n : ℕ} (ε : Fin n → Bool)
namespace GlobalTheory.CompanionTheory.JStable
theorem _root_.solution (s : Bool) (x y : EuclideanSpace ℂ {i : Fin n // ε i = s}) :
    ∑ a, star (ext0 ε s x a) * ext0 ε s y a = inner ℂ x y := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => ε a = s)
    (fun a => star (ext0 ε s x a) * ext0 ε s y a)]
  have h2 : ∑ a : {a // ¬ ε a = s}, star (ext0 ε s x a) * ext0 ε s y a = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [extendByZero_apply_of_ne ε x a.2, star_zero, zero_mul])
  rw [h2, add_zero, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hx : ∀ z : EuclideanSpace ℂ {i : Fin n // ε i = s}, ext0 ε s z i.1 = z i := by
    intro z
    simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.2]
  rw [hx x, hx y]
  simp [mul_comm]
end GlobalTheory.CompanionTheory.JStable
