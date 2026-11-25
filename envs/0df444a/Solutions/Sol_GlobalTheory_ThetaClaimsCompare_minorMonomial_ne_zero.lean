-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.minorMonomial_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:57.884076+00:00
-- url     : https://prove2.me/submissions/32b79680-86f5-413a-bab3-2ca518ebbe5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution (hcol : ∀ σ, Function.Injective (col σ)) (a : T → ℕ → ℕ) :
    minorsP r n col k a ≠ 0 := by
  classical
  intro h
  have h1 : MvPolynomial.eval (fun ℓ : Letter T r n => if ℓ.2.2 = col ℓ.1 ℓ.2.1 then (1 : k) else 0)
      (minorsP r n col k a) = 1 := by
    simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
    refine Finset.prod_eq_one fun σ _ => Finset.prod_eq_one fun s _ => ?_
    rw [show (MvPolynomial.eval _).mapMatrix _ = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) k) from ?_,
      Matrix.det_one, one_pow]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X, Matrix.one_apply,
      (hcol σ).eq_iff, (Fin.castLE_injective _).eq_iff, eq_comm]
  rw [h, map_zero] at h1
  exact zero_ne_one h1
end GlobalTheory.ThetaClaimsCompare
