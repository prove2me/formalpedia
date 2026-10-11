-- Prove2me | solution 1 for MazurTransfer.place_ord_image_unit_of_range
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T14:07:44.856114+00:00
-- url     : https://prove2.me/submissions/1612a8b3-e6d3-41ad-86eb-5a5165c57bea

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual ring map whose range is a place's valuation ring
sends units to elements of order zero. Named downstream consumer: the Pell
function at ordinary-chart closed points.
-/
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

noncomputable section
universe u v w
namespace MazurTransfer.PublicPlaceRangeUnitProof
open AlgebraicCurve

theorem ord_image_unit (K : Type u) [Field K] (F : Type v) [Field F] [Algebra K F]
    (A : Type w) [CommRing A] (v : Place K F) (f : A →+* F)
    (hrange : f.range = v.toValuationSubring.toSubring) (a : A) (ha : IsUnit a) :
    v.ord (f a) = 0 := by
  let g : A →+* v.toValuationSubring := f.codRestrict v.toValuationSubring.toSubring
    (fun b => hrange ▸ RingHom.mem_range_self f b)
  obtain ⟨u, hu⟩ := ha.map g
  have H : (u.val : F) = f a := congrArg (fun b : v.toValuationSubring => (b : F)) hu
  rw [← H]
  exact v.ord_coe_unit u

end MazurTransfer.PublicPlaceRangeUnitProof
#print axioms MazurTransfer.PublicPlaceRangeUnitProof.ord_image_unit

open AlgebraicCurve
theorem solution
    (K : Type u) [Field K] (F : Type v) [Field F] [Algebra K F]
    (A : Type w) [CommRing A] (p : Place K F) (f : A →+* F)
    (hrange : f.range = p.toValuationSubring.toSubring) (a : A) (ha : IsUnit a) :
    p.ord (f a) = 0 := by
  exact MazurTransfer.PublicPlaceRangeUnitProof.ord_image_unit K F A p f hrange a ha

#print axioms solution
