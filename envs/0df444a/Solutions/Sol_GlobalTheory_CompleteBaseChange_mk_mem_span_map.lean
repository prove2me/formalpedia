-- Prove2me | solution 1 for GlobalTheory.CompleteBaseChange.mk_mem_span_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:11.650442+00:00
-- url     : https://prove2.me/submissions/c1940f7d-873a-42e8-91d8-70554bd5bb2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
import Theorems.Thm_GlobalTheory_CompleteBaseChange_exists_polynomial_sub_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange
namespace GlobalTheory.CompleteBaseChange
theorem _root_.solution : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O] (I : Ideal T), I.FG → IsAdicComplete (I.map (algebraMap T O)) O → ∀ (σ : Type) [Fintype σ] (f : σ → MvPowerSeries σ T), (∃ N : ℕ, ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : T) : MvPowerSeries σ T) ∈ Ideal.span (Set.range f) ⊔ I.map (MvPowerSeries.C : T →+* MvPowerSeries σ T)) → Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → ∀ g : MvPowerSeries σ O, Ideal.Quotient.mk (Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap T O) (f j))) g ∈ Submodule.span O (Set.range fun h : MvPowerSeries σ T => Ideal.Quotient.mk (Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap T O) (f j))) (MvPowerSeries.map (algebraMap T O) h)) := by
  intro T O _ _ _ I hI hO σ _ f ⟨N, hN⟩ _ g
  obtain ⟨p, hp⟩ := exists_polynomial_sub_mem (hI.map (algebraMap T O))
    (fun j => MvPowerSeries.map (algebraMap T O) (f j)) N (fun α hα => by
      have hC : (MvPowerSeries.map (σ := σ) (algebraMap T O)).comp C =
          (C : O →+* MvPowerSeries σ O).comp (algebraMap T O) := RingHom.ext fun a => map_C _ a
      have := Ideal.mem_map_of_mem (MvPowerSeries.map (σ := σ) (algebraMap T O)) (hN α hα)
      rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp, Ideal.map_map, hC,
        ← Ideal.map_map, map_monomial, map_one] at this
      exact this) g
  rw [Ideal.Quotient.eq.2 hp]
  clear hp
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have : ((MvPolynomial.monomial α c : MvPolynomial σ O) : MvPowerSeries σ O) =
        c • MvPowerSeries.map (algebraMap T O) (monomial α 1) := by
      rw [MvPolynomial.coe_monomial, map_monomial, map_one, ← map_smul, smul_eq_mul, mul_one]
    rw [this, ← Ideal.Quotient.mkₐ_eq_mk O, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, map_add]
    exact add_mem hp hq
end GlobalTheory.CompleteBaseChange
