-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.disc_eq_of_isometric_prod_ofUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:31.007795+00:00
-- url     : https://prove2.me/submissions/6085766a-d33d-4439-a298-e694355371e8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_disc_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_ofUnit
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
open GroundTheory.Automorphic.HermitianForm
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [FiniteDimensional E V] (h : HermitianForm F E V)
    {W : Submodule E V} {h₀ : HermitianForm F E W} {a : Fˣ}
    (H : Isometric ((ofUnit (E := E) a).prod h₀) h) :
    h.disc = QuotientGroup.mk a * h₀.disc := by
  rw [← H.disc_eq, disc_prod, disc_ofUnit]
end GroundTheory.Automorphic.HermitianForm
