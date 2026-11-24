-- Prove2me | solution 1 for GlobalTheory.AdLat.prod_mem_adelicCompletionOfElementSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:00.550879+00:00
-- url     : https://prove2.me/submissions/0dc18631-fe37-48aa-b19f-39069815c272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_adelicCompletion_fractionalIdeal_properties
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (x : ι → RA F E) (h : ∀ i ∈ s, x i ∈ hat1 F (I i : Set E)) :
    ∏ i ∈ s, x i ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Algebra.TensorProduct.one_def]
    exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (h a (Finset.mem_insert_self _ _)) _
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end GlobalTheory.AdLat
