-- Prove2me | solution 1 for MazurTransfer.PlaceOrderOfRangeUnit.ord_image_unit
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:40:58.407839+00:00
-- url     : https://prove2.me/submissions/7434ba8f-cd84-488d-9739-a5d229b218a4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual ring map whose range is a place's valuation ring
sends units to elements of order zero. Named downstream consumer: the Pell
function at ordinary-chart closed points.
-/
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

noncomputable section
universe u v w
open AlgebraicCurve

theorem solution (K : Type u) [Field K] (F : Type v) [Field F] [Algebra K F]
    (A : Type w) [CommRing A] (v : Place K F) (f : A →+* F)
    (hrange : f.range = v.toValuationSubring.toSubring) (a : A) (ha : IsUnit a) :
    v.ord (f a) = 0 := by
  let g : A →+* v.toValuationSubring := f.codRestrict v.toValuationSubring.toSubring
    (fun b => hrange ▸ RingHom.mem_range_self f b)
  obtain ⟨u, hu⟩ := ha.map g
  have H : (u.val : F) = f a := congrArg (fun b : v.toValuationSubring => (b : F)) hu
  rw [← H]
  exact v.ord_coe_unit u

#print axioms solution
