-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/301bd8c1-db94-5347-b013-009ba6c4e37a

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3

set_option autoImplicit false

open IsDedekindDomain

open LanglandsTunnell.CubicInduction

namespace IntegralEntriesOpen

private theorem continuous_entry {A : Type*} [CommRing A] [TopologicalSpace A] (i j : Fin 3) :
    Continuous fun k : GL (Fin 3) A => (k : Matrix (Fin 3) (Fin 3) A) i j :=
  Units.continuous_val.matrix_elem i j

private theorem continuous_inv_entry {A : Type*} [CommRing A] [TopologicalSpace A] (i j : Fin 3) :
    Continuous fun k : GL (Fin 3) A => ((k⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) i j :=
  Units.continuous_coe_inv.matrix_elem i j

private theorem coe_localMaximalCompact3_eq (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    ((LanglandsTunnell.CubicInduction.localMaximalCompact3 R K v :
        Subgroup (GL (Fin 3) (v.adicCompletion K))) : Set (GL (Fin 3) (v.adicCompletion K))) =
      (⋂ i : Fin 3, ⋂ j : Fin 3,
          (fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ⁻¹'
            (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∩
        (⋂ i : Fin 3, ⋂ j : Fin 3,
          (fun k : GL (Fin 3) (v.adicCompletion K) =>
              ((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ⁻¹'
            (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
  ext k
  simp only [SetLike.mem_coe, LanglandsTunnell.CubicInduction.mem_localMaximalCompact3_iff, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_preimage, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

end IntegralEntriesOpen

open IntegralEntriesOpen

theorem solution
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsOpen ((localMaximalCompact3 R K v : Subgroup (GL (Fin 3) (v.adicCompletion K))) :
      Set (GL (Fin 3) (v.adicCompletion K))) := by
  have hO : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isOpen_valuationSubring _
  rw [coe_localMaximalCompact3_eq R K v]
  refine IsOpen.inter ?_ ?_
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (continuous_entry i j)
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (continuous_inv_entry i j)

end S_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3 (solution)
