-- Prove2me | solution 1 for LovaszTheta.indepNum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:59:14.546671+00:00
-- url     : https://prove2.me/submissions/80ee6d68-845e-468b-b03f-135f976af934

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_indepNum_le_gen

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution [Finite V] (G : SimpleGraph V) {d : ℕ} {u : V → Fin d → ℝ}
    (hu : IsOrthonormalRep G u) {c : Fin d → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) :
    (G.indepNum : ℝ) ≤ t :=
  indepNum_le_gen G u hu.1 hu.2 hc ht0 ht
end LovaszTheta
