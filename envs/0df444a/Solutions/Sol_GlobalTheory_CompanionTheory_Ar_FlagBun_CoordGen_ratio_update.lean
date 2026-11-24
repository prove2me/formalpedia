-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.ratio_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:35.800831+00:00
-- url     : https://prove2.me/submissions/408d8688-fbed-4490-a598-fe8f064aba2f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}
variable {E : Type} [AddCommGroup E] [Module Ω E] {n : S → ℕ}
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
theorem _root_.solution {Q : Type*} [Fintype Q] [DecidableEq Q] {T : Q → Type*} {K : Type*} [Field K]
    (D : ∀ q, T q → K) (ρ : ∀ q, T q) (hρ : ∀ q, D q (ρ q) ≠ 0) (q : Q) (f : T q) (a : K) (ha : a ≠ 0) :
    (a * ∏ q', D q' (Function.update ρ q f q')) / (a * ∏ q', D q' (ρ q')) = D q f / D q (ρ q) := by
  have hP : (∏ q' ∈ Finset.univ.erase q, D q' (ρ q')) ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ => hρ q
  rw [mul_div_mul_left _ _ ha, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q),
    ← Finset.mul_prod_erase Finset.univ (fun q' => D q' (ρ q')) (Finset.mem_univ q),
    Function.update_self,
    Finset.prod_congr rfl (g := fun q' => D q' (ρ q'))
      (fun q' hq' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')])]
  exact mul_div_mul_right _ _ hP
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
