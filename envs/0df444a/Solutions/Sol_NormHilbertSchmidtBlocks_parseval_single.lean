-- Prove2me | solution 1 for NormHilbertSchmidtBlocks.parseval_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:52.920513+00:00
-- url     : https://prove2.me/submissions/298b440d-ac53-4e55-8f4d-ac236cab085d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_Change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open NormHilbertSchmidtBlocks
namespace NormHilbertSchmidtBlocks
theorem _root_.solution {C' V' : Type*} [Fintype C'] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (x y : PiLp 2 (fun _ : C' => V')) :
    ∑ p : (Σ _ : C', Fin (Module.finrank ℂ V')),
      inner ℂ x (WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V')) *
      inner ℂ (WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V')) y =
      inner ℂ x y := by
  have h1 : ∀ (c : C') (v : V'),
      inner ℂ x (WithLp.toLp 2 (Pi.single c v : C' → V')) = inner ℂ (x c) v := by
    intro c v
    rw [PiLp.inner_apply, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [Pi.single_apply, hd]
    · simp
  have h2 : ∀ (c : C') (v : V'),
      inner ℂ (WithLp.toLp 2 (Pi.single c v : C' → V')) y = inner ℂ v (y c) := by
    intro c v
    rw [PiLp.inner_apply, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [Pi.single_apply, hd]
    · simp
  rw [Fintype.sum_sigma]
  simp only [h1, h2, OrthonormalBasis.sum_inner_mul_inner]
  exact (PiLp.inner_apply x y).symm
end NormHilbertSchmidtBlocks
