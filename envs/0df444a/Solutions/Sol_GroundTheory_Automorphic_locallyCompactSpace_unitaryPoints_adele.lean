-- Prove2me | solution 1 for GroundTheory.Automorphic.locallyCompactSpace_unitaryPoints_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:41.449826+00:00
-- url     : https://prove2.me/submissions/f9211767-ee5f-4a39-ba18-b08e1e6f0f18

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_LatticeCompact
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Theorems.Thm_GroundTheory_Automorphic_locallyCompactSpace_unitaryPoints


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable [NumberField K]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
namespace GroundTheory.Automorphic
theorem _root_.solution (hH : IsUnit H.det) :
    LocallyCompactSpace (unitaryPoints K E H 𝔸[K]) :=
  locallyCompactSpace_unitaryPoints H 𝔸[K] hH
end GroundTheory.Automorphic
