-- Prove2me | solution 1 for GroundTheory.Global.exists_eq_of_forall_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:04.321982+00:00
-- url     : https://prove2.me/submissions/b9119c0b-0c24-49da-872a-897224bd0176

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Theorems.Thm_GroundTheory_Global_coe_mem_adicCompletionIntegers_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (k : K)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ∃ z : 𝓞 K, (z : K) = k := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K k ≤ 1 := fun v =>
    (coe_mem_adicCompletionIntegers_iff v k).mp (h v)
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K k hv
  exact ⟨z, hz⟩
end GroundTheory.Global
