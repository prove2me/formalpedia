-- Prove2me | solution 1 for GlobalTheory.GalOfCusp.IsAttached.pol_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:19.464666+00:00
-- url     : https://prove2.me/submissions/d59f0706-0a19-41ea-bfdd-09934053ca64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__TrivialOnInertiaOfUnr_d5f82434e8467b70
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



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
theorem _root_.solution (h : IsAttached A i π 0 r) {c : N.Om ≃+* N.Om} (hc : IsCMConjOm H.E N.Om c) :
    IsConjDual c r (cycBar H.E N.Om (N.l i) ^ (1 - (a : ℤ))) := by
  simpa using h.pol c hc 0 (by simp)
end IsAttached
end GlobalTheory.GalOfCusp
