-- Prove2me | solution 1 for GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:43.544494+00:00
-- url     : https://prove2.me/submissions/132529a8-b6b7-4362-9406-dabf1cdea411

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Restricted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [CommRing E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
namespace GroundTheory.Automorphic
theorem _root_.solution (hH : IsUnit H.det)
    (g : unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K)) (v : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleUnitaryEquiv H b hH g v = unitaryMap K E H (finiteAdeleEval K v) g := rfl
end GroundTheory.Automorphic
