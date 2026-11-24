-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.eq_of_isFirstMax_of_isFirstMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:36.72674+00:00
-- url     : https://prove2.me/submissions/69b90f4e-3b37-4b64-a11c-8424bde313ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionInverseIntoSlice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer
namespace GlobalTheory.RankFibreKer
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J) (h' : IsFirstMax Y J') :
    J = J' := by
  apply idx.injective
  rcases lt_trichotomy (idx J) (idx J') with hl | he | hl
  · exact absurd ((h'.2 J).2 hl) (not_lt.2 (h.2 J').1)
  · exact he
  · exact absurd ((h.2 J').2 hl) (not_lt.2 (h'.2 J).1)
end GlobalTheory.RankFibreKer
