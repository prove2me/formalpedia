-- Prove2me | solution 1 for GlobalTheory.GalOfCusp.IsAttached.frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:11:48.102584+00:00
-- url     : https://prove2.me/submissions/b1152c55-c208-4d02-8cb5-3f229b05bacf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__TrivialOnInertiaOfUnr_d5f82434e8467b70

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GalOfCusp
open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Matrix
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
variable {A}
variable {i : N.Loc} {a : ℕ} {π : A.CG a} {s : ℝ} {r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))}
namespace GlobalTheory.GalOfCusp
namespace IsAttached
theorem _root_.solution (h : IsAttached A i π s r) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i))
    (hu : A.unr (A.locG π w)) :
    (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), r σ = 1) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.map (A.iotaQC i).toRingHom =
        galPol A (A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)) := by
  have h1 : A.unr (A.wdOf i r w) := by rw [h.away w hw]; exact (A.unr_tw _ _).2 hu
  refine ⟨(A.wdOf_unr i r w hw h.cont).1 h1, fun B σ hB hσ => ?_⟩
  rw [A.wdOf_frob i r w hw h.cont h1 B σ hB hσ, h.away w hw]
  rfl
end IsAttached
end GlobalTheory.GalOfCusp
