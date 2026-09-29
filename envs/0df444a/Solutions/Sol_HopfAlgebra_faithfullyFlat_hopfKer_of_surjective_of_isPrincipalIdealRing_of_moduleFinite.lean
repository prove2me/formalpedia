-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3945424c-4e15-5c1a-b8dd-10b6d3973c8f

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite

set_option autoImplicit false

universe u v w

open HopfAlgebra in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H]
    (H' : Type w) [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H := by
  classical

  haveI : Module.Free R H' := inferInstance
  obtain ⟨hfin, hproj⟩ := HopfAlgebra.finite_projective_hopfKer_of_surjective qc hqc
  haveI : Module.Flat ↥(hopfKer qc) H := Module.Flat.of_projective
  refine ⟨fun m hm htop => ?_⟩

  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (⊤ : Submodule ↥(hopfKer qc) H) hfin.fg_top (by rw [htop])
  have h1 : r • (1 : H) = 0 := hr0 1 Submodule.mem_top
  rw [Algebra.smul_def, mul_one, Subalgebra.algebraMap_def, Algebra.algebraMap_self,
    RingHom.id_apply] at h1
  have hr : r = 0 := Subtype.ext h1
  rw [hr, zero_sub] at hr1
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.neg_mem hr1))

end S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite (solution)
