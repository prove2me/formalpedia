-- Prove2me | solution 1 for GlobalTheory.WeylRowAll.map_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:54.047714+00:00
-- url     : https://prove2.me/submissions/f74a5535-6ea3-4d7a-985b-3f4c52f7c71b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.WeylRowAll
namespace GlobalTheory.WeylRowAll
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.rowAct R g f) = Formalism.GradedWeylDivisibility.rowAct S (g.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct]
end GlobalTheory.WeylRowAll
