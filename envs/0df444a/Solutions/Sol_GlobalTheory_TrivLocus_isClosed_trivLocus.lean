-- Prove2me | solution 1 for GlobalTheory.TrivLocus.isClosed_trivLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:56.565802+00:00
-- url     : https://prove2.me/submissions/f1b6e9dc-5350-4b39-849e-3f20e974e4fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors
import Theorems.Thm_GlobalTheory_TrivLocus_triv_fibre_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.TrivLocus
variable {X Y : Scheme.{0}}
namespace GlobalTheory.TrivLocus
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → IsClosed {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
  rintro R _ X f M hM ⟨P⟩ ⟨Q⟩ _ _
  convert PrimeSpectrum.isClosed_zeroLocus
    ((Set.range fun σ : Fin P.a → Fin P.b => (P.D₀.submatrix σ id).det) ∪
      Set.range fun σ : Fin Q.a → Fin Q.b => (Q.D₀.submatrix σ id).det)
  ext p
  rw [PrimeSpectrum.mem_zeroLocus, Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]
  constructor
  · rintro ⟨K, _, g, X', π, f', hg, h, ht⟩
    rw [← hg]
    exact (triv_fibre_iff hM P Q g h).1 ht
  · intro hp
    have hk : RingHom.ker (algebraMap R p.asIdeal.ResidueField) = p.asIdeal := Ideal.ker_algebraMap_residueField _
    refine ⟨p.asIdeal.ResidueField, inferInstance, algebraMap R _, _, _, _, hk, IsPullback.of_hasPullback _ _, ?_⟩
    refine (triv_fibre_iff hM P Q _ (IsPullback.of_hasPullback _ _)).2 ?_
    rw [hk]
    exact hp
end GlobalTheory.TrivLocus
