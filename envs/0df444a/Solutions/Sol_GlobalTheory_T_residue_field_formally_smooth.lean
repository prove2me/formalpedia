-- Prove2me | solution 1 for GlobalTheory.T.residue_field_formally_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:12.285083+00:00
-- url     : https://prove2.me/submissions/483a3a39-fdd1-4960-8417-307d27595921

import Mathlib
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsEtCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldFormallySmooth
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_ResidueFieldFormallySmooth
import Theorems.Thm_GlobalTheory_residueField_formallySmooth_of_isClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsClosed ({x} : Set X) → letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra; Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  first | exact @_root_.GlobalTheory.residueField_formallySmooth_of_isClosed | exact _root_.GlobalTheory.residueField_formallySmooth_of_isClosed | (intros; apply _root_.GlobalTheory.residueField_formallySmooth_of_isClosed <;> assumption)
end _root_.GlobalTheory.T
