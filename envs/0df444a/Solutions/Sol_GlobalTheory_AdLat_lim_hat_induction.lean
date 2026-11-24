-- Prove2me | solution 1 for GlobalTheory.AdLat.lim_hat_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:42:39.219641+00:00
-- url     : https://prove2.me/submissions/c7e9a9d6-6dcd-4bf3-9c70-1264da53d455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
import Theorems.Thm_GlobalTheory_AdLat_lim_gen_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat
theorem _root_.solution {L : Set (Fin n → E)} (P : (Fin n → RA F E) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hneg : ∀ x, P x → P (-x))
    (hgen : ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) →
      ∀ x ∈ L, P (a • fv F x)) {z : Fin n → RA F E} (hz : z ∈ hat F L) : P z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [lim_gen_eq]; exact hgen a ha x hx
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | neg x _ hx => exact hneg x hx
end GlobalTheory.AdLat
