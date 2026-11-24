-- Prove2me | solution 1 for GlobalTheory.SeriesNakayama.span_mod_equations_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:12.157722+00:00
-- url     : https://prove2.me/submissions/eec8799f-81ed-458a-9163-789611ea3417

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift
import Theorems.Thm_GlobalTheory_SeriesNakayama_surjective_of_mod
import Theorems.Thm_GlobalTheory_SeriesNakayama_exists_projection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama
namespace GlobalTheory.SeriesNakayama
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (K : Type) [Field K] (f : O →+* K) (g N : ℕ)
    (Y : Type) (F : Y → Fin g → (MvPowerSeries (Fin g) O))
    (ρ : Y → Fin N → (MvPowerSeries (Fin g) O))
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O)
    (h : ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y,
      G y - ∑ k, v k • MvPowerSeries.map f (ρ y k) ∈
        Ideal.span (Set.range fun i => MvPowerSeries.map f (F y i)))
    (G : Y → (MvPowerSeries (Fin g) O)) :
    ∃ v : Fin N → O, ∀ y, G y - ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y)) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := hπ.maximalIdeal_eq
  have : IsAdicComplete (Ideal.span {π}) O := hm ▸ ‹_›
  obtain ⟨μ, l, hl, hμ, hμ1⟩ := exists_projection f hf
  let Φ : (Fin N ⊕ (Y × Fin g × (Fin g →₀ ℕ)) → O) →ₗ[O] (Y × (Fin g →₀ ℕ) → O) :=
    { toFun := fun x j => ∑ k, x (.inl k) * MvPowerSeries.coeff j.2 (ρ j.1 k) +
        ∑ i, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j.2,
          x (.inr (j.1, i, p.1)) * MvPowerSeries.coeff p.2 (F j.1 i)
      map_add' := fun x x' => funext fun j => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => funext fun j => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_assoc] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mod π Φ fun G => ?_
    let G' : Y → MvPowerSeries (Fin g) K := fun y d => f (G (y, d))
    obtain ⟨v, hv⟩ := h G'
    choose H hH using fun y => (Ideal.mem_span_range_iff_exists_fun).1 (hv y)
    refine ⟨Sum.elim (fun k => l (v k)) fun q => l (MvPowerSeries.coeff q.2.2 (H q.1 q.2.1)), ?_⟩
    rintro ⟨y, d⟩
    rw [← hm, ← hf, RingHom.mem_ker]
    have h1 := congrArg (fun s => μ (MvPowerSeries.coeff d s)) (eq_sub_iff_add_eq.1 (hH y))
    have h2 : MvPowerSeries.coeff d (G' y) = f (G (y, d)) := rfl
    simp only [map_add, map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_smul, hμ, hμ1, h2] at h1
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_add, map_sum, map_mul, Sum.elim_inl,
      Sum.elim_inr, hl]
    rw [← h1, add_comm, sub_self]
  obtain ⟨x, hx⟩ := hΦ fun j => MvPowerSeries.coeff j.2 (G j.1)
  refine ⟨fun k => x (.inl k), fun y => Ideal.mem_span_range_iff_exists_fun.2
    ⟨fun i => (show MvPowerSeries (Fin g) O from fun d => x (.inr (y, i, d))), ?_⟩⟩
  ext d
  have h1 : _ = MvPowerSeries.coeff d (G y) := congrFun hx (y, d)
  simp only [map_sub, map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_smul, ← h1, Φ,
    LinearMap.coe_mk, AddHom.coe_mk, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun i _ => MvPowerSeries.coeff_mul d _ _
end GlobalTheory.SeriesNakayama
