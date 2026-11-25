-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.diagUnits_eq_localIdele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:00:39.014599+00:00
-- url     : https://prove2.me/submissions/7d0fd070-a907-460a-a406-6b4c33947550

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_localIdele_fst
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_diagUnits_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]
namespace GlobalTheory.Mem.Chr.Model
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ) (x : (v.adicCompletion L)ˣ)
    (h : diagUnits L a = localIdele L v x) : a = 1 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have h1 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) h
  simp only [diagUnits_fst, localIdele_fst] at h1
  apply Units.ext
  apply (algebraMap L w.Completion).injective
  rw [h1, Units.val_one, map_one]
  rfl
end GlobalTheory.Mem.Chr.Model
