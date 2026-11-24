-- Prove2me | solution 1 for GlobalTheory.SqZero.spMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:14.184291+00:00
-- url     : https://prove2.me/submissions/beb7f4de-47e9-4b18-9327-680fb5889b8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {X : Over (Spec (CommRingCat.of R))} {A A₀ B : Type} [CommRing A] [Algebra R A]
  [CommRing A₀] [Algebra R A₀] [CommRing B] [Algebra R B]
namespace GlobalTheory.SqZero
theorem _root_.solution (q : A →ₐ[R] A₀) (hq : Function.Surjective q)
    (hn : ∀ a, q a = 0 → IsNilpotent a) : Function.Surjective (spMap q).left := by
  intro p
  have := range_comap_of_surjective A₀ (q : A →+* A₀) hq
  have hp : (p : PrimeSpectrum A) ∈ PrimeSpectrum.zeroLocus (RingHom.ker (q : A →+* A₀) : Set A) :=
    fun a ha => by
      obtain ⟨n, hn⟩ := hn a ha
      exact (p : PrimeSpectrum A).isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  rw [← this] at hp
  exact hp
end GlobalTheory.SqZero
