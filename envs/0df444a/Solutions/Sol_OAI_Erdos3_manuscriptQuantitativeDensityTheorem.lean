-- Prove2me | solution 1 for OAI.Erdos3.manuscriptQuantitativeDensityTheorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T05:27:35.395982+00:00
-- url     : https://prove2.me/submissions/bcdf1469-5607-492e-8369-986c3d4dd51d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1395
import Theorems.Thm_OAI_Erdos3_manuscript_main_theorems

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Conclusions
namespace OAI

section

namespace Erdos3

theorem manuscriptQuantitativeDensityTheorem_oai : QuantitativeDensityTheorem :=
  manuscript_main_theorems.1

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.manuscriptQuantitativeDensityTheorem_oai := @OAI.Erdos3.manuscriptQuantitativeDensityTheorem_oai
