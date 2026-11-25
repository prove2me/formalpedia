-- Prove2me | solution 1 for GlobalTheory.WachLettersCompare.isUnit_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:03.531663+00:00
-- url     : https://prove2.me/submissions/40c5ce8a-4c1d-42ae-9f65-a5ae2d8e7f70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LettersFreeOfRank
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachLettersFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LetterSandwichOfFrobMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.WachLettersCompare
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
attribute [local instance] letterModule
namespace GlobalTheory.WachLettersCompare
theorem _root_.solution : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    have h1 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simpa [letπ, LocWach.q] using W.q₀_def
    set x := algebraMap (LetA O n) W.EE letπ with hx
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : W.EE) x
    obtain ⟨u, hu⟩ : IsUnit (x ^ PD.p) := W.EE_π.pow _
    have := W.EE_complete
    have hj : ((PD.p : ℕ) : W.EE) ∈ Ideal.jacobson (⊥ : Ideal W.EE) :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
        (Ideal.mem_span_singleton_self _)
    have h2 := (Ideal.mem_jacobson_bot.1 hj) (x * r * (↑u⁻¹ : W.EE))
    have h3 : x * algebraMap (LetA O n) W.EE W.q =
        (((PD.p : ℕ) : W.EE) * (x * r * (↑u⁻¹ : W.EE)) + 1) * u := by
      rw [hx, ← map_mul, h1, map_sub, map_pow, map_add, map_one, ← hx, hr, ← hu]
      have := u.inv_mul
      linear_combination (-((PD.p : ℕ) : W.EE) * x * r) * this
    exact isUnit_of_mul_isUnit_right (h3 ▸ h2.mul u.isUnit)
  have key : ∀ k : ℕ, IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) W.q)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      rw [pow_succ', AlgHom.mul_apply]
      have := W.φE_ext ((W.φA ^ k) W.q)
      exact this ▸ ih.map W.φE
  exact key _
end GlobalTheory.WachLettersCompare
