-- Prove2me | solution 1 for GlobalTheory.TorusNil.isNilpotent_of_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:33:56.395084+00:00
-- url     : https://prove2.me/submissions/6596acdb-d7dd-4495-8ec1-8f80abce6116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
namespace GlobalTheory.TorusNil
theorem _root_.solution {C : Type} [CommRing C] [Algebra A C] {J : Ideal A}
    (hJ : IsNilpotent J) (k : ℕ) (x : C) (hx : x ∈ (J ^ (k + 1)).map (algebraMap A C)) :
    IsNilpotent x := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow hx n
  rw [← Ideal.map_pow, ← pow_mul, mul_comm, pow_mul, hn] at this
  simpa using this
end GlobalTheory.TorusNil
