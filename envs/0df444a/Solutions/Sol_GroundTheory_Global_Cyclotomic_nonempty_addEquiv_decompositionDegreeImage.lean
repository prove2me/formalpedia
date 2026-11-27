-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.nonempty_addEquiv_decompositionDegreeImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:31.433113+00:00
-- url     : https://prove2.me/submissions/a2a2418f-3e36-47fc-83e6-20c27f08b41b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_degreeComponent_ne_one
import Theorems.Thm_GroundTheory_Global_Cyclotomic_isClosed_decompositionDegreeImage
import Theorems.Thm_GroundTheory_Global_Cyclotomic_topologicalClosure_decompositionDegreeImage
import Theorems.Thm_GroundTheory_Global_Cyclotomic_nonempty_addEquiv_of_isClosed
import Theorems.Thm_GroundTheory_Global_Cyclotomic_toPadicInt_degree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
variable (q : Nat.Primes) (P : Ideal (𝓞 ℚ̄))
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nonempty ((decompositionDegreeImage P).topologicalClosure ≃+ ℤ̂) := by
  rw [topologicalClosure_decompositionDegreeImage]
  refine nonempty_addEquiv_of_isClosed _ (isClosed_decompositionDegreeImage P) fun q => ?_
  obtain ⟨σ, hσ, hne⟩ := exists_mem_stabilizer_degreeComponent_ne_one (p := p) P q
  refine ⟨_, ⟨σ, hσ, rfl⟩, ?_⟩
  rw [toPadicInt_degree]
  exact fun h => hne (by rw [← ofAdd_toAdd (degreeComponent q σ), h, ofAdd_zero])
end GroundTheory.Global.Cyclotomic
