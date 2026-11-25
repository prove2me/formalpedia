-- Prove2me | solution 1 for GlobalTheory.GalOfCusp.isConjDual_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:47:23.334868+00:00
-- url     : https://prove2.me/submissions/0eeefcce-8abb-48a5-a181-916d0a34662b

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
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {k : Type} [Field k] {a : ℕ}
namespace GlobalTheory.GalOfCusp
theorem _root_.solution (c : Ω ≃+* Ω) : IsConjDual c (1 : G E Ω →* GL (Fin a) k) 1 :=
  ⟨1, fun _ _ _ => by simp⟩
end GlobalTheory.GalOfCusp
