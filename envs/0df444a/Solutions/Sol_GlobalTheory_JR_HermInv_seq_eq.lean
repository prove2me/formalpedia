-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.seq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:52.10871+00:00
-- url     : https://prove2.me/submissions/6384389a-5fc4-45da-99dc-5703ed9b6d00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ} {K : Type} [CommRing K]
namespace GlobalTheory.JR.HermInv
theorem _root_.solution {u v : ℕ → K} (q : Fin r → K) (hu : ∀ k, u (k + r) = -((fun j : Fin r => u (k + j)) ⬝ᵥ q))
    (hv : ∀ k, v (k + r) = -((fun j : Fin r => v (k + j)) ⬝ᵥ q)) (h : ∀ k < r, u k = v k) : u = v := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < r
    · exact h n hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + r := ⟨n - r, by omega⟩
      rw [hu, hv]
      congr 2
      funext j
      exact ih _ (by omega)
end GlobalTheory.JR.HermInv
