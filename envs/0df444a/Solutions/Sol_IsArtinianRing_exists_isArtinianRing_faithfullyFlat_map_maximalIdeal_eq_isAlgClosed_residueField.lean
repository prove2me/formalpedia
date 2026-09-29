-- Prove2me | solution 1 for IsArtinianRing.exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b9c59b11-f023-5bd9-91b0-b4eee98de325

import Mathlib
import Theorems.Thm_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsArtinianRing_exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField

set_option autoImplicit false

open IsLocalRing

theorem solution
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] :
    ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D) (_ : Algebra C D),
      Module.FaithfullyFlat C D ∧ IsLocalHom (algebraMap C D) ∧
      Ideal.map (algebraMap C D) (maximalIdeal C) = maximalIdeal D ∧
      IsAlgClosed (ResidueField D) := by
  classical

  obtain ⟨B, iB, iLB, iNB, iAlg, iLoc, hFF, hmap, ⟨e⟩⟩ :=
    IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
      C (AlgebraicClosure (ResidueField C))
  letI : CommRing B := iB
  haveI : IsLocalRing B := iLB
  haveI : IsNoetherianRing B := iNB
  letI : Algebra C B := iAlg
  haveI : IsLocalHom (algebraMap C B) := iLoc

  have hnilC : IsNilpotent (maximalIdeal C) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
  have hnilB : IsNilpotent (maximalIdeal B) := by
    obtain ⟨n, hn⟩ := hnilC
    refine ⟨n, ?_⟩
    rw [← hmap, ← Ideal.map_pow, hn]
    simp
  haveI : IsArtinianRing B := (isArtinianRing_iff_isNilpotent_maximalIdeal B).mpr hnilB
  haveI : IsAlgClosed (ResidueField B) :=
    IsAlgClosed.of_ringEquiv (AlgebraicClosure (ResidueField C)) (ResidueField B) e.symm.toRingEquiv
  exact ⟨B, iB, iLB, inferInstance, iAlg, hFF, iLoc, hmap, inferInstance⟩

end S_IsArtinianRing_exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField
end P2MW
export P2MW.S_IsArtinianRing_exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField (solution)
