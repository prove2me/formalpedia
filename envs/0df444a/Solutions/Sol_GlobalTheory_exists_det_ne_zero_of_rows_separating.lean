-- Prove2me | solution 1 for GlobalTheory.exists_det_ne_zero_of_rows_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:16.133081+00:00
-- url     : https://prove2.me/submissions/3327ee36-99a1-4d23-bb6c-7e96fef48c10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetNeZeroOfRowsSeparating

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K),
      (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) →
      ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  intro K _ σ h M hM
  have hsp : Submodule.span K (Set.range M) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have ha : (fun j => f (fun k => if j = k then 1 else 0)) = 0 := by
      apply hM
      intro s
      have h1 : f (M s) = 0 := hf (Submodule.subset_span ⟨s, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      refine (Finset.sum_congr rfl fun j _ => ?_).trans h1
      rw [smul_eq_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [Pi.zero_apply] at this
    rw [this, smul_zero]
  obtain ⟨b, hbS, hbsp, hli⟩ := exists_linearIndependent K (Set.range M)
  have hsp' : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin h → K)) := by
    rw [Subtype.range_coe, hbsp, hsp]
  let B := Module.Basis.mk hli hsp'
  let e : Fin h ≃ b := (Pi.basisFun K (Fin h)).indexEquiv B
  have hmem : ∀ i, ∃ s, M s = (e i : Fin h → K) := fun i => hbS (e i).2
  choose s hs using hmem
  refine ⟨s, ?_⟩
  have hrows : LinearIndependent K (Matrix.of fun i j => M (s i) j).row := by
    have : (Matrix.of fun i j => M (s i) j).row = (fun x : b => (x : Fin h → K)) ∘ e := by
      funext i j
      simp [Matrix.row, hs]
    rw [this]
    exact hli.comp e e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
end GlobalTheory
