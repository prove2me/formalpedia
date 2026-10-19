-- Prove2me | solution 1 for Giddings1999.boundary_S_matrix_eq_CFT_correlator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:41:45.426384+00:00
-- url     : https://prove2.me/submissions/49f4b450-208d-477c-b991-1ec8636c5f73

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology MeasureTheory
open Giddings1999

theorem solution {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    {N : ℕ} (dV : MeasureTheory.Measure X) (db : MeasureTheory.Measure B)
    [MeasureTheory.SigmaFinite dV] [MeasureTheory.SigmaFinite db]
    (K : B → X → ℂ) (Z : Fin N → ℂ) (f : Fin N → B → ℂ) (GT : (Fin N → X) → ℂ)
    (CFT : (Fin N → B) → ℂ)
    (hWitten : ∀ b : Fin N → B, CFT b =
      ∫ x, (∏ a, K (b a) (x a)) * GT x ∂(MeasureTheory.Measure.pi fun _ => dV))
    (hint : MeasureTheory.Integrable
      (fun p : (Fin N → B) × (Fin N → X) => (∏ a, f a (p.1 a) * K (p.1 a) (p.2 a)) * GT p.2)
      ((MeasureTheory.Measure.pi fun _ => db).prod (MeasureTheory.Measure.pi fun _ => dV))) :
    lszBoundarySMatrix dV db K Z f GT =
      ∫ b, (∏ a, f a (b a) / Z a) * CFT b ∂(MeasureTheory.Measure.pi fun _ => db) := by
  set c : ℂ := ∏ a, (Z a)⁻¹
  set F : (Fin N → B) → (Fin N → X) → ℂ := fun b x => (∏ a, f a (b a) * K (b a) (x a)) * GT x
  have hswap := integral_integral_swap (f := F) hint
  have hL : lszBoundarySMatrix dV db K Z f GT =
      ∫ x, c * ∫ b, F b x ∂(Measure.pi fun _ => db) ∂(Measure.pi fun _ => dV) := by
    unfold lszBoundarySMatrix
    congr 1; ext x
    simp only [F, wavePacket, div_eq_mul_inv, Finset.prod_mul_distrib]
    rw [integral_mul_const]
    rw [← integral_fintype_prod_eq_prod (fun a b => f a b * K b (x a))]
    simp only [c, Finset.prod_mul_distrib]
    ring
  have hR : (∫ b, (∏ a, f a (b a) / Z a) * CFT b ∂(Measure.pi fun _ => db)) =
      ∫ b, c * ∫ x, F b x ∂(Measure.pi fun _ => dV) ∂(Measure.pi fun _ => db) := by
    congr 1; ext b
    rw [hWitten b, ← integral_const_mul, ← integral_const_mul]
    congr 1; ext x
    simp only [F, div_eq_mul_inv, Finset.prod_mul_distrib, c]
    ring
  rw [hL, hR, integral_const_mul, integral_const_mul, hswap]
