-- Prove2me | solution 1 for GlobalTheory.cubeComplex_above_exactAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:35.492678+00:00
-- url     : https://prove2.me/submissions/64a0f8a9-d592-43e5-9740-f51818a79fcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_of_bijective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
variable {ι : Type} (R : Type) [CommRing R]
namespace GlobalTheory
theorem _root_.solution [LinearOrder ι] [Fintype ι] (w : Finset ι) {p : ℕ}
    (hp : p ≠ Fintype.card ι) : (cubeComplex (Cube.above R w)).ExactAt p := by
  by_cases hw : w = Finset.univ
  · subst hw
    have : Subsingleton (Cube.Term (Cube.above R (Finset.univ : Finset ι)) p) := by
      refine ⟨fun x y => funext fun s => ?_⟩
      refine Finsupp.ext fun a => absurd ?_ hp
      rw [← s.2, Finset.univ_subset_iff.1 a.down, Finset.card_univ]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Cube.Term _ p)))
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ w := by
      by_contra! h
      exact hw (Finset.eq_univ_iff_forall.2 h)
    refine cubeComplex_exactAt_of_bijective _ i (fun s _ => ?_) p
    refine ⟨Finsupp.mapDomain_injective fun _ _ _ => Subsingleton.elim _ _,
      Finsupp.mapDomain_surjective fun x => ⟨⟨?_⟩, Subsingleton.elim _ _⟩⟩
    exact (Finset.subset_insert_iff_of_notMem hi).1 x.down
end GlobalTheory
