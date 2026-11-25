-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.localIdele_eq_infIdele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:01:23.462196+00:00
-- url     : https://prove2.me/submissions/88c0641b-c774-4788-8798-c7b4318b0fc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_localIdele_snd_self
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_localIdele_fst
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_infIdele_fst_self
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_infIdele_snd

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (v.adicCompletion L)ˣ)
    (y : (w.Completion)ˣ) (h : localIdele L v x = infIdele L w y) : x = 1 ∧ y = 1 := by
  have h1 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).2 v) h
  have h2 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) h
  simp only [localIdele_snd_self, infIdele_snd, localIdele_fst, infIdele_fst_self] at h1 h2
  exact ⟨Units.ext (h1.trans rfl), Units.ext (h2.symm.trans rfl)⟩
end GlobalTheory.Mem.Chr.Model
