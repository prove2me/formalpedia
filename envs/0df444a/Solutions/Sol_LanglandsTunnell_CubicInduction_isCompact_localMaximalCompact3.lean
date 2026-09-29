-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isCompact_localMaximalCompact3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/feee9b40-b917-54e0-bbe0-b07c5daa46a1

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3

set_option autoImplicit false

open IsDedekindDomain NumberField

open LanglandsTunnell.CubicInduction

noncomputable section

open Matrix

private theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))

private def integralMatrices3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submonoid (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) where
  carrier := {a | ∀ i j, Valued.v (a i j) ≤ 1}
  one_mem' := by
    intro i j
    exact valued_one_entry_le3 (𝓞 ℚ) ℚ v i j
  mul_mem' := by
    intro a b ha hb i j
    exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ha i l) (fun l => hb l j)

private theorem mem_integralMatrices3 (v : HeightOneSpectrum (𝓞 ℚ)) {a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} :
    a ∈ integralMatrices3 v ↔ ∀ i j, Valued.v (a i j) ≤ 1 :=
  Iff.rfl

private theorem isCompact_integralMatrices3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
  have hpi : IsCompact (Set.pi Set.univ fun _ : Fin 3 =>
      Set.pi Set.univ fun _ : Fin 3 => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers v
  have hset : (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) =
      (Set.pi Set.univ fun _ : Fin 3 =>
        Set.pi Set.univ fun _ : Fin 3 => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := by
    ext a
    rw [SetLike.mem_coe, mem_integralMatrices3]
    constructor
    · intro h i _ j _
      exact h i j
    · intro h i j
      exact h i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hset]
  exact hpi

private theorem localMaximalCompact3_eq_units (v : HeightOneSpectrum (𝓞 ℚ)) :
    localMaximalCompact3 (𝓞 ℚ) ℚ v = (integralMatrices3 v).units := by
  ext k
  simp only [mem_localMaximalCompact3_iff, Submonoid.mem_units_iff, mem_integralMatrices3]

theorem solution (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  rw [localMaximalCompact3_eq_units]
  exact Submonoid.units_isCompact (isCompact_integralMatrices3 v)

end
end S_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3 (solution)
