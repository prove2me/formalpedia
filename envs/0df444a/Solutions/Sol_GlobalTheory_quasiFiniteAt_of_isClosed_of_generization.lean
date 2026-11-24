-- Prove2me | solution 1 for GlobalTheory.quasiFiniteAt_of_isClosed_of_generization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:39.800015+00:00
-- url     : https://prove2.me/submissions/e228a886-18ff-4b6b-9570-d80f99b74880

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiFiniteAtAffineSpaceHomOfVectorOfCoord
import Theorems.Thm_GlobalTheory_isOpen_singleton_of_isClosed_of_generization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → f y = f x → y = x) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have hemb := (f.fiberι (f x)).isEmbedding
  have hx' : f.fiberι (f x) (f.asFiber x) = x := by simp
  apply isOpen_singleton_of_isClosed_of_generization
  · have := hx.preimage hemb.continuous
    convert this using 1
    ext z
    exact ⟨fun hz => by rw [hz]; exact hx', fun hz => hemb.injective (hz.trans hx'.symm)⟩
  · intro y hy
    apply hemb.injective
    rw [hx']
    apply h
    · have := hy.map hemb.continuous
      rwa [hx'] at this
    · have : f.fiberι (f x) y ∈ f ⁻¹' {f x} := by
        rw [← f.range_fiberι]; exact ⟨y, rfl⟩
      exact this
end GlobalTheory
