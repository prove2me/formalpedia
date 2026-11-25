-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.exists_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:59.586048+00:00
-- url     : https://prove2.me/submissions/50adfb17-1bfc-436c-89bc-f8e17138d590

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace IsBlockDiag
theorem _root_.solution {G : Matrix (Fin N) (Fin N) R} (hG : IsBlockDiag j G)
    (hu : ∀ b : Fin N, IsUnit (G.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det) :
    ∃ B, IsBlockDiag j B ∧ B.BlockTriangular id ∧ IsLowerUni (G * B) := by
  let P : Fin N → Fin N → Prop := fun b a => a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  let v : ∀ b, {a // P b a} → R := fun b c =>
    (G.submatrix (Subtype.val : {a // P b a} → Fin N) Subtype.val)⁻¹ c (⟨b, le_rfl, Iff.rfl⟩ : {a // P b a})
  let B : Matrix (Fin N) (Fin N) R := fun c b => if h : P b c then v b ⟨c, h⟩ else 0
  have key : ∀ a b, (G * B) a b = ∑ c : {c // P b c}, G a c * v b c := fun a b => by
    rw [Matrix.mul_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ (P b),
      Finset.sum_eq_zero (s := Finset.univ.filter fun c => ¬ P b c) (fun c hc => by
        rw [show B c b = 0 from dif_neg (Finset.mem_filter.1 hc).2, mul_zero]), add_zero,
      Finset.sum_subtype (p := P b) _ (by simp)]
    exact Finset.sum_congr rfl fun c _ => by rw [show B c b = v b c from dif_pos c.2]
  have key2 : ∀ a b (h : P b a), (G * B) a b = if a = b then 1 else 0 := fun a b h => by
    have := congrFun (congrFun (Matrix.mul_nonsing_inv _ (hu b)) ⟨a, h⟩) ⟨b, le_rfl, Iff.rfl⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [key]
    refine this.trans ?_
    simp [Subtype.ext_iff]
  refine ⟨B, fun a b h => dif_neg fun e => h e.2, fun a b h => dif_neg fun e => absurd e.1 (not_le.2 h),
    fun a => by rw [key2 a a ⟨le_rfl, Iff.rfl⟩, if_pos rfl], fun a b h => ?_⟩
  by_cases e : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · rw [key2 a b ⟨h.le, e⟩, if_neg h.ne]
  · rw [key]
    exact Finset.sum_eq_zero fun c _ => by rw [hG a c fun e' => e (e'.trans c.2.2), zero_mul]
end IsBlockDiag
end GlobalTheory.CompanionTheory.Ar.PB
