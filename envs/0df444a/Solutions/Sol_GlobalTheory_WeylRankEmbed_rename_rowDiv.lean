-- Prove2me | solution 1 for GlobalTheory.WeylRankEmbed.rename_rowDiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:57.574314+00:00
-- url     : https://prove2.me/submissions/767a90a5-55ea-4e72-8c80-a2cda0024c20

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_RenameUpperLeftCornerMemWeylLattice
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
open MvPolynomial Formalism.GradedWeylDivisibility
open GlobalTheory
open GlobalTheory.WeylRankEmbed
variable (R : Type) [CommRing R] {a b : ℕ} (hab : a ≤ b)
namespace GlobalTheory.WeylRankEmbed
theorem _root_.solution (x y : Fin a) (k : ℕ) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (rowDiv R x y k f) =
      rowDiv R (Fin.castLE hab x) (Fin.castLE hab y) k (rename (corner hab) f) := by
  have key : (Polynomial.mapAlgHom (rename (R := R) (corner hab))).comp (rowGen R x y) =
      (rowGen R (Fin.castLE hab x) (Fin.castLE hab y)).comp (rename (corner hab)) := by
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v.1 = y
    · simp [rowGen, hv, corner]
    · have hv' : Fin.castLE hab v.1 ≠ Fin.castLE hab y := fun e => hv (Fin.castLE_injective hab e)
      simp [rowGen, hv, corner]
  have h2 := congrArg (fun φ => (φ f).coeff k) key
  simpa [rowDiv, Polynomial.coeff_map] using h2
end GlobalTheory.WeylRankEmbed
