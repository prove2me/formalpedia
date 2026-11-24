-- Prove2me | solution 1 for GlobalTheory.EtIsom.rec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:51.712609+00:00
-- url     : https://prove2.me/submissions/f59fc100-94bd-4039-bb3d-78152d10449c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.EtIsom
theorem _root_.solution {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (q : Fin r → R)
    (u w : ℕ → M) (hu : ∀ m, u (m + r) = -∑ i, q i • u (m + i))
    (hw : ∀ m, w (m + r) = -∑ i, q i • w (m + i)) (h0 : ∀ n < r, u n = w n) : ∀ n, u n = w n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < r
    · exact h0 n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + r := ⟨n - r, by omega⟩
      rw [hu, hw]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih _ (by have := i.2; omega)]
end GlobalTheory.EtIsom
