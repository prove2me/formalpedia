-- Prove2me | solution 1 for GlobalTheory.ChartQF.isAlgebraic_of_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:43.73289+00:00
-- url     : https://prove2.me/submissions/8e8a1923-edcd-4466-944a-ac586dbcab54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF
variable {A R : Type} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R] (f : A →+* R)
namespace GlobalTheory.ChartQF
theorem _root_.solution {K : Type} [Field K] [Algebra (ResidueField A) K] (ev : R →+* K)
    (hev : ∀ a, ev (f a) = algebraMap (ResidueField A) K (residue A a)) {T G : Set R} (hT : T ⊆ Set.range f)
    {D : Subalgebra (ResidueField A) K} (hG : ∀ g ∈ G, ev g ∈ D) {b : R} (hb : b ∈ Subring.closure (T ∪ G)) :
    ev b ∈ D := by
  induction hb using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨a, rfl⟩ := hT hx
      rw [hev]
      exact D.algebraMap_mem _
    · exact hG x hx
  | zero => rw [map_zero]; exact D.zero_mem
  | one => rw [map_one]; exact D.one_mem
  | add x y _ _ hx hy => rw [map_add]; exact D.add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact D.neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact D.mul_mem hx hy
end GlobalTheory.ChartQF
