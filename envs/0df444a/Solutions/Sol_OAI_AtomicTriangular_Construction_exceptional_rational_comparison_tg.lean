-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.exceptional_rational_comparison_tg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:00:10.559373+00:00
-- url     : https://prove2.me/submissions/d8e5339e-1169-4f71-8a07-c2db20a2a206

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T163
import Definitions.Def_OAIQ262T164
import Definitions.Def_OAIQ262T165
import Definitions.Def_OAIQ262T166
import Definitions.Def_OAIQ262T167
import Definitions.Def_OAIQ262T168
import Definitions.Def_OAIQ262T169
import Definitions.Def_OAIQ262T170
import Definitions.Def_OAIQ262T171
import Definitions.Def_OAIQ262T172
import Definitions.Def_OAIQ262T173
import Definitions.Def_OAIQ262T174
import Definitions.Def_OAIQ262T175
import Definitions.Def_OAIQ262T176
import Definitions.Def_OAIQ262T177
import Definitions.Def_OAIQ262T178
import Definitions.Def_OAIQ262T179
import Definitions.Def_OAIQ262T180
import Definitions.Def_OAIQ262T181
import Definitions.Def_OAIQ262T182
import Definitions.Def_OAIQ262T183
import Definitions.Def_OAIQ262T184
import Definitions.Def_OAIQ262T185
import Definitions.Def_OAIQ262T195
import Definitions.Def_OAIQ262T196
import Definitions.Def_OAIQ262T197
import Definitions.Def_OAIQ262T198
import Definitions.Def_OAIQ262T259
import Definitions.Def_OAIQ262T260

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma spectrumBox_mem (side q : Fin 2) (j : Fin 31) (r : Fin 8) :
    (spectrumBox side q j r).Mem (finiteSpectrum side q j r) := by
  unfold spectrumBox finiteSpectrum
  split_ifs
  · exact CI.mem_mul (atomPolynomial_coeff_mem j) (CI.mem_ofReal (ATable_mem side 22 r))
  · exact CI.mem_sum (fun col => CI.mem_mul (columnTable_mem ⟨col.val,by omega⟩ j) (CI.mem_ofReal (ATable_mem side ⟨col.val,by omega⟩ r)))

lemma spectrum0_0_mem (j : Fin 31) (r : Fin 8) : (spectrum0_0 j r).Mem (finiteSpectrum 0 0 j r) := by
  have he : spectrumBox 0 0 j r = spectrum0_0 j r := by
    fin_cases j
    · exact spectrum0_0_0_calc r
    · exact spectrum0_0_1_calc r
    · exact spectrum0_0_2_calc r
    · exact spectrum0_0_3_calc r
    · exact spectrum0_0_4_calc r
    · exact spectrum0_0_5_calc r
    · exact spectrum0_0_6_calc r
    · exact spectrum0_0_7_calc r
    · exact spectrum0_0_8_calc r
    · exact spectrum0_0_9_calc r
    · exact spectrum0_0_10_calc r
    · exact spectrum0_0_11_calc r
    · exact spectrum0_0_12_calc r
    · exact spectrum0_0_13_calc r
    · exact spectrum0_0_14_calc r
    · exact spectrum0_0_15_calc r
    · exact spectrum0_0_16_calc r
    · exact spectrum0_0_17_calc r
    · exact spectrum0_0_18_calc r
    · exact spectrum0_0_19_calc r
    · exact spectrum0_0_20_calc r
    · exact spectrum0_0_21_calc r
    · exact spectrum0_0_22_calc r
    · exact spectrum0_0_23_calc r
    · exact spectrum0_0_24_calc r
    · exact spectrum0_0_25_calc r
    · exact spectrum0_0_26_calc r
    · exact spectrum0_0_27_calc r
    · exact spectrum0_0_28_calc r
    · exact spectrum0_0_29_calc r
    · exact spectrum0_0_30_calc r
  rw [← he]
  exact spectrumBox_mem 0 0 j r
lemma spectrum0_1_mem (j : Fin 31) (r : Fin 8) : (spectrum0_1 j r).Mem (finiteSpectrum 0 1 j r) := by
  have he : spectrumBox 0 1 j r = spectrum0_1 j r := by
    fin_cases j
    · exact spectrum0_1_0_calc r
    · exact spectrum0_1_1_calc r
    · exact spectrum0_1_2_calc r
    · exact spectrum0_1_3_calc r
    · exact spectrum0_1_4_calc r
    · exact spectrum0_1_5_calc r
    · exact spectrum0_1_6_calc r
    · exact spectrum0_1_7_calc r
    · exact spectrum0_1_8_calc r
    · exact spectrum0_1_9_calc r
    · exact spectrum0_1_10_calc r
    · exact spectrum0_1_11_calc r
    · exact spectrum0_1_12_calc r
    · exact spectrum0_1_13_calc r
    · exact spectrum0_1_14_calc r
    · exact spectrum0_1_15_calc r
    · exact spectrum0_1_16_calc r
    · exact spectrum0_1_17_calc r
    · exact spectrum0_1_18_calc r
    · exact spectrum0_1_19_calc r
    · exact spectrum0_1_20_calc r
    · exact spectrum0_1_21_calc r
    · exact spectrum0_1_22_calc r
    · exact spectrum0_1_23_calc r
    · exact spectrum0_1_24_calc r
    · exact spectrum0_1_25_calc r
    · exact spectrum0_1_26_calc r
    · exact spectrum0_1_27_calc r
    · exact spectrum0_1_28_calc r
    · exact spectrum0_1_29_calc r
    · exact spectrum0_1_30_calc r
  rw [← he]
  exact spectrumBox_mem 0 1 j r
lemma spectrum1_0_mem (j : Fin 31) (r : Fin 8) : (spectrum1_0 j r).Mem (finiteSpectrum 1 0 j r) := by
  have he : spectrumBox 1 0 j r = spectrum1_0 j r := by
    fin_cases j
    · exact spectrum1_0_0_calc r
    · exact spectrum1_0_1_calc r
    · exact spectrum1_0_2_calc r
    · exact spectrum1_0_3_calc r
    · exact spectrum1_0_4_calc r
    · exact spectrum1_0_5_calc r
    · exact spectrum1_0_6_calc r
    · exact spectrum1_0_7_calc r
    · exact spectrum1_0_8_calc r
    · exact spectrum1_0_9_calc r
    · exact spectrum1_0_10_calc r
    · exact spectrum1_0_11_calc r
    · exact spectrum1_0_12_calc r
    · exact spectrum1_0_13_calc r
    · exact spectrum1_0_14_calc r
    · exact spectrum1_0_15_calc r
    · exact spectrum1_0_16_calc r
    · exact spectrum1_0_17_calc r
    · exact spectrum1_0_18_calc r
    · exact spectrum1_0_19_calc r
    · exact spectrum1_0_20_calc r
    · exact spectrum1_0_21_calc r
    · exact spectrum1_0_22_calc r
    · exact spectrum1_0_23_calc r
    · exact spectrum1_0_24_calc r
    · exact spectrum1_0_25_calc r
    · exact spectrum1_0_26_calc r
    · exact spectrum1_0_27_calc r
    · exact spectrum1_0_28_calc r
    · exact spectrum1_0_29_calc r
    · exact spectrum1_0_30_calc r
  rw [← he]
  exact spectrumBox_mem 1 0 j r
lemma spectrum1_1_mem (j : Fin 31) (r : Fin 8) : (spectrum1_1 j r).Mem (finiteSpectrum 1 1 j r) := by
  have he : spectrumBox 1 1 j r = spectrum1_1 j r := by
    fin_cases j
    · exact spectrum1_1_0_calc r
    · exact spectrum1_1_1_calc r
    · exact spectrum1_1_2_calc r
    · exact spectrum1_1_3_calc r
    · exact spectrum1_1_4_calc r
    · exact spectrum1_1_5_calc r
    · exact spectrum1_1_6_calc r
    · exact spectrum1_1_7_calc r
    · exact spectrum1_1_8_calc r
    · exact spectrum1_1_9_calc r
    · exact spectrum1_1_10_calc r
    · exact spectrum1_1_11_calc r
    · exact spectrum1_1_12_calc r
    · exact spectrum1_1_13_calc r
    · exact spectrum1_1_14_calc r
    · exact spectrum1_1_15_calc r
    · exact spectrum1_1_16_calc r
    · exact spectrum1_1_17_calc r
    · exact spectrum1_1_18_calc r
    · exact spectrum1_1_19_calc r
    · exact spectrum1_1_20_calc r
    · exact spectrum1_1_21_calc r
    · exact spectrum1_1_22_calc r
    · exact spectrum1_1_23_calc r
    · exact spectrum1_1_24_calc r
    · exact spectrum1_1_25_calc r
    · exact spectrum1_1_26_calc r
    · exact spectrum1_1_27_calc r
    · exact spectrum1_1_28_calc r
    · exact spectrum1_1_29_calc r
    · exact spectrum1_1_30_calc r
  rw [← he]
  exact spectrumBox_mem 1 1 j r
lemma spectrumTable_mem (side q : Fin 2) (j : Fin 31) (r : Fin 8) :
    (spectrumTable side q j r).Mem (finiteSpectrum side q j r) := by
  fin_cases side <;> fin_cases q
  · exact spectrum0_0_mem j r
  · exact spectrum0_1_mem j r
  · exact spectrum1_0_mem j r
  · exact spectrum1_1_mem j r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorWaveBox_mem (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) :
    (taylorWaveBox q br n l j).Mem (taylorWave q br (nearNode n) l.val (frequency j)) := by
  exact CI.mem_divNat (CI.mem_mul (CI.mem_mul (taylorAmplitudeBox_mem q br j) (taylorExpTable_mem q br n j))
    (CI.mem_pow (taylorPhaseTable_mem q br j) (l.val+2))) (Nat.factorial_pos _)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_0_mem (l : Fin 21) (j : Fin 31) : (tw0_0_0 l j).Mem (taylorWave 0 0 (nearNode 0) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 0 l j = tw0_0_0 l j := by
    fin_cases l
    · exact tw0_0_0_0_calc j
    · exact tw0_0_0_1_calc j
    · exact tw0_0_0_2_calc j
    · exact tw0_0_0_3_calc j
    · exact tw0_0_0_4_calc j
    · exact tw0_0_0_5_calc j
    · exact tw0_0_0_6_calc j
    · exact tw0_0_0_7_calc j
    · exact tw0_0_0_8_calc j
    · exact tw0_0_0_9_calc j
    · exact tw0_0_0_10_calc j
    · exact tw0_0_0_11_calc j
    · exact tw0_0_0_12_calc j
    · exact tw0_0_0_13_calc j
    · exact tw0_0_0_14_calc j
    · exact tw0_0_0_15_calc j
    · exact tw0_0_0_16_calc j
    · exact tw0_0_0_17_calc j
    · exact tw0_0_0_18_calc j
    · exact tw0_0_0_19_calc j
    · exact tw0_0_0_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 0 0 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_1_mem (l : Fin 21) (j : Fin 31) : (tw0_0_1 l j).Mem (taylorWave 0 0 (nearNode 1) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 1 l j = tw0_0_1 l j := by
    fin_cases l
    · exact tw0_0_1_0_calc j
    · exact tw0_0_1_1_calc j
    · exact tw0_0_1_2_calc j
    · exact tw0_0_1_3_calc j
    · exact tw0_0_1_4_calc j
    · exact tw0_0_1_5_calc j
    · exact tw0_0_1_6_calc j
    · exact tw0_0_1_7_calc j
    · exact tw0_0_1_8_calc j
    · exact tw0_0_1_9_calc j
    · exact tw0_0_1_10_calc j
    · exact tw0_0_1_11_calc j
    · exact tw0_0_1_12_calc j
    · exact tw0_0_1_13_calc j
    · exact tw0_0_1_14_calc j
    · exact tw0_0_1_15_calc j
    · exact tw0_0_1_16_calc j
    · exact tw0_0_1_17_calc j
    · exact tw0_0_1_18_calc j
    · exact tw0_0_1_19_calc j
    · exact tw0_0_1_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 0 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_2_mem (l : Fin 21) (j : Fin 31) : (tw0_0_2 l j).Mem (taylorWave 0 0 (nearNode 2) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 2 l j = tw0_0_2 l j := by
    fin_cases l
    · exact tw0_0_2_0_calc j
    · exact tw0_0_2_1_calc j
    · exact tw0_0_2_2_calc j
    · exact tw0_0_2_3_calc j
    · exact tw0_0_2_4_calc j
    · exact tw0_0_2_5_calc j
    · exact tw0_0_2_6_calc j
    · exact tw0_0_2_7_calc j
    · exact tw0_0_2_8_calc j
    · exact tw0_0_2_9_calc j
    · exact tw0_0_2_10_calc j
    · exact tw0_0_2_11_calc j
    · exact tw0_0_2_12_calc j
    · exact tw0_0_2_13_calc j
    · exact tw0_0_2_14_calc j
    · exact tw0_0_2_15_calc j
    · exact tw0_0_2_16_calc j
    · exact tw0_0_2_17_calc j
    · exact tw0_0_2_18_calc j
    · exact tw0_0_2_19_calc j
    · exact tw0_0_2_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 0 2 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_3_mem (l : Fin 21) (j : Fin 31) : (tw0_0_3 l j).Mem (taylorWave 0 0 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 3 l j = tw0_0_3 l j := by
    fin_cases l
    · exact tw0_0_3_0_calc j
    · exact tw0_0_3_1_calc j
    · exact tw0_0_3_2_calc j
    · exact tw0_0_3_3_calc j
    · exact tw0_0_3_4_calc j
    · exact tw0_0_3_5_calc j
    · exact tw0_0_3_6_calc j
    · exact tw0_0_3_7_calc j
    · exact tw0_0_3_8_calc j
    · exact tw0_0_3_9_calc j
    · exact tw0_0_3_10_calc j
    · exact tw0_0_3_11_calc j
    · exact tw0_0_3_12_calc j
    · exact tw0_0_3_13_calc j
    · exact tw0_0_3_14_calc j
    · exact tw0_0_3_15_calc j
    · exact tw0_0_3_16_calc j
    · exact tw0_0_3_17_calc j
    · exact tw0_0_3_18_calc j
    · exact tw0_0_3_19_calc j
    · exact tw0_0_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 0 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_4_mem (l : Fin 21) (j : Fin 31) : (tw0_0_4 l j).Mem (taylorWave 0 0 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 4 l j = tw0_0_4 l j := by
    fin_cases l
    · exact tw0_0_4_0_calc j
    · exact tw0_0_4_1_calc j
    · exact tw0_0_4_2_calc j
    · exact tw0_0_4_3_calc j
    · exact tw0_0_4_4_calc j
    · exact tw0_0_4_5_calc j
    · exact tw0_0_4_6_calc j
    · exact tw0_0_4_7_calc j
    · exact tw0_0_4_8_calc j
    · exact tw0_0_4_9_calc j
    · exact tw0_0_4_10_calc j
    · exact tw0_0_4_11_calc j
    · exact tw0_0_4_12_calc j
    · exact tw0_0_4_13_calc j
    · exact tw0_0_4_14_calc j
    · exact tw0_0_4_15_calc j
    · exact tw0_0_4_16_calc j
    · exact tw0_0_4_17_calc j
    · exact tw0_0_4_18_calc j
    · exact tw0_0_4_19_calc j
    · exact tw0_0_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 0 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave005
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_5_mem (l : Fin 21) (j : Fin 31) : (tw0_0_5 l j).Mem (taylorWave 0 0 (nearNode 5) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 5 l j = tw0_0_5 l j := by
    fin_cases l
    · exact tw0_0_5_0_calc j
    · exact tw0_0_5_1_calc j
    · exact tw0_0_5_2_calc j
    · exact tw0_0_5_3_calc j
    · exact tw0_0_5_4_calc j
    · exact tw0_0_5_5_calc j
    · exact tw0_0_5_6_calc j
    · exact tw0_0_5_7_calc j
    · exact tw0_0_5_8_calc j
    · exact tw0_0_5_9_calc j
    · exact tw0_0_5_10_calc j
    · exact tw0_0_5_11_calc j
    · exact tw0_0_5_12_calc j
    · exact tw0_0_5_13_calc j
    · exact tw0_0_5_14_calc j
    · exact tw0_0_5_15_calc j
    · exact tw0_0_5_16_calc j
    · exact tw0_0_5_17_calc j
    · exact tw0_0_5_18_calc j
    · exact tw0_0_5_19_calc j
    · exact tw0_0_5_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 0 5 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_6_mem (l : Fin 21) (j : Fin 31) : (tw0_0_6 l j).Mem (taylorWave 0 0 (nearNode 6) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 6 l j = tw0_0_6 l j := by
    fin_cases l
    · exact tw0_0_6_0_calc j
    · exact tw0_0_6_1_calc j
    · exact tw0_0_6_2_calc j
    · exact tw0_0_6_3_calc j
    · exact tw0_0_6_4_calc j
    · exact tw0_0_6_5_calc j
    · exact tw0_0_6_6_calc j
    · exact tw0_0_6_7_calc j
    · exact tw0_0_6_8_calc j
    · exact tw0_0_6_9_calc j
    · exact tw0_0_6_10_calc j
    · exact tw0_0_6_11_calc j
    · exact tw0_0_6_12_calc j
    · exact tw0_0_6_13_calc j
    · exact tw0_0_6_14_calc j
    · exact tw0_0_6_15_calc j
    · exact tw0_0_6_16_calc j
    · exact tw0_0_6_17_calc j
    · exact tw0_0_6_18_calc j
    · exact tw0_0_6_19_calc j
    · exact tw0_0_6_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 0 6 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw0_0 n l j).Mem (taylorWave 0 0 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw0_0_0_mem l j
  · exact tw0_0_1_mem l j
  · exact tw0_0_2_mem l j
  · exact tw0_0_3_mem l j
  · exact tw0_0_4_mem l j
  · exact tw0_0_5_mem l j
  · exact tw0_0_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_0_mem (l : Fin 21) (j : Fin 31) : (tw0_1_0 l j).Mem (taylorWave 0 1 (nearNode 0) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 0 l j = tw0_1_0 l j := by
    fin_cases l
    · exact tw0_1_0_0_calc j
    · exact tw0_1_0_1_calc j
    · exact tw0_1_0_2_calc j
    · exact tw0_1_0_3_calc j
    · exact tw0_1_0_4_calc j
    · exact tw0_1_0_5_calc j
    · exact tw0_1_0_6_calc j
    · exact tw0_1_0_7_calc j
    · exact tw0_1_0_8_calc j
    · exact tw0_1_0_9_calc j
    · exact tw0_1_0_10_calc j
    · exact tw0_1_0_11_calc j
    · exact tw0_1_0_12_calc j
    · exact tw0_1_0_13_calc j
    · exact tw0_1_0_14_calc j
    · exact tw0_1_0_15_calc j
    · exact tw0_1_0_16_calc j
    · exact tw0_1_0_17_calc j
    · exact tw0_1_0_18_calc j
    · exact tw0_1_0_19_calc j
    · exact tw0_1_0_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 1 0 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_1_mem (l : Fin 21) (j : Fin 31) : (tw0_1_1 l j).Mem (taylorWave 0 1 (nearNode 1) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 1 l j = tw0_1_1 l j := by
    fin_cases l
    · exact tw0_1_1_0_calc j
    · exact tw0_1_1_1_calc j
    · exact tw0_1_1_2_calc j
    · exact tw0_1_1_3_calc j
    · exact tw0_1_1_4_calc j
    · exact tw0_1_1_5_calc j
    · exact tw0_1_1_6_calc j
    · exact tw0_1_1_7_calc j
    · exact tw0_1_1_8_calc j
    · exact tw0_1_1_9_calc j
    · exact tw0_1_1_10_calc j
    · exact tw0_1_1_11_calc j
    · exact tw0_1_1_12_calc j
    · exact tw0_1_1_13_calc j
    · exact tw0_1_1_14_calc j
    · exact tw0_1_1_15_calc j
    · exact tw0_1_1_16_calc j
    · exact tw0_1_1_17_calc j
    · exact tw0_1_1_18_calc j
    · exact tw0_1_1_19_calc j
    · exact tw0_1_1_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 1 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave012
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_2_mem (l : Fin 21) (j : Fin 31) : (tw0_1_2 l j).Mem (taylorWave 0 1 (nearNode 2) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 2 l j = tw0_1_2 l j := by
    fin_cases l
    · exact tw0_1_2_0_calc j
    · exact tw0_1_2_1_calc j
    · exact tw0_1_2_2_calc j
    · exact tw0_1_2_3_calc j
    · exact tw0_1_2_4_calc j
    · exact tw0_1_2_5_calc j
    · exact tw0_1_2_6_calc j
    · exact tw0_1_2_7_calc j
    · exact tw0_1_2_8_calc j
    · exact tw0_1_2_9_calc j
    · exact tw0_1_2_10_calc j
    · exact tw0_1_2_11_calc j
    · exact tw0_1_2_12_calc j
    · exact tw0_1_2_13_calc j
    · exact tw0_1_2_14_calc j
    · exact tw0_1_2_15_calc j
    · exact tw0_1_2_16_calc j
    · exact tw0_1_2_17_calc j
    · exact tw0_1_2_18_calc j
    · exact tw0_1_2_19_calc j
    · exact tw0_1_2_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 1 2 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_3_mem (l : Fin 21) (j : Fin 31) : (tw0_1_3 l j).Mem (taylorWave 0 1 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 3 l j = tw0_1_3 l j := by
    fin_cases l
    · exact tw0_1_3_0_calc j
    · exact tw0_1_3_1_calc j
    · exact tw0_1_3_2_calc j
    · exact tw0_1_3_3_calc j
    · exact tw0_1_3_4_calc j
    · exact tw0_1_3_5_calc j
    · exact tw0_1_3_6_calc j
    · exact tw0_1_3_7_calc j
    · exact tw0_1_3_8_calc j
    · exact tw0_1_3_9_calc j
    · exact tw0_1_3_10_calc j
    · exact tw0_1_3_11_calc j
    · exact tw0_1_3_12_calc j
    · exact tw0_1_3_13_calc j
    · exact tw0_1_3_14_calc j
    · exact tw0_1_3_15_calc j
    · exact tw0_1_3_16_calc j
    · exact tw0_1_3_17_calc j
    · exact tw0_1_3_18_calc j
    · exact tw0_1_3_19_calc j
    · exact tw0_1_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 1 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave014
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_4_mem (l : Fin 21) (j : Fin 31) : (tw0_1_4 l j).Mem (taylorWave 0 1 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 4 l j = tw0_1_4 l j := by
    fin_cases l
    · exact tw0_1_4_0_calc j
    · exact tw0_1_4_1_calc j
    · exact tw0_1_4_2_calc j
    · exact tw0_1_4_3_calc j
    · exact tw0_1_4_4_calc j
    · exact tw0_1_4_5_calc j
    · exact tw0_1_4_6_calc j
    · exact tw0_1_4_7_calc j
    · exact tw0_1_4_8_calc j
    · exact tw0_1_4_9_calc j
    · exact tw0_1_4_10_calc j
    · exact tw0_1_4_11_calc j
    · exact tw0_1_4_12_calc j
    · exact tw0_1_4_13_calc j
    · exact tw0_1_4_14_calc j
    · exact tw0_1_4_15_calc j
    · exact tw0_1_4_16_calc j
    · exact tw0_1_4_17_calc j
    · exact tw0_1_4_18_calc j
    · exact tw0_1_4_19_calc j
    · exact tw0_1_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 1 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_5_mem (l : Fin 21) (j : Fin 31) : (tw0_1_5 l j).Mem (taylorWave 0 1 (nearNode 5) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 5 l j = tw0_1_5 l j := by
    fin_cases l
    · exact tw0_1_5_0_calc j
    · exact tw0_1_5_1_calc j
    · exact tw0_1_5_2_calc j
    · exact tw0_1_5_3_calc j
    · exact tw0_1_5_4_calc j
    · exact tw0_1_5_5_calc j
    · exact tw0_1_5_6_calc j
    · exact tw0_1_5_7_calc j
    · exact tw0_1_5_8_calc j
    · exact tw0_1_5_9_calc j
    · exact tw0_1_5_10_calc j
    · exact tw0_1_5_11_calc j
    · exact tw0_1_5_12_calc j
    · exact tw0_1_5_13_calc j
    · exact tw0_1_5_14_calc j
    · exact tw0_1_5_15_calc j
    · exact tw0_1_5_16_calc j
    · exact tw0_1_5_17_calc j
    · exact tw0_1_5_18_calc j
    · exact tw0_1_5_19_calc j
    · exact tw0_1_5_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 1 5 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_6_mem (l : Fin 21) (j : Fin 31) : (tw0_1_6 l j).Mem (taylorWave 0 1 (nearNode 6) l.val (frequency j)) := by
  have he : taylorWaveBox 0 1 6 l j = tw0_1_6 l j := by
    fin_cases l
    · exact tw0_1_6_0_calc j
    · exact tw0_1_6_1_calc j
    · exact tw0_1_6_2_calc j
    · exact tw0_1_6_3_calc j
    · exact tw0_1_6_4_calc j
    · exact tw0_1_6_5_calc j
    · exact tw0_1_6_6_calc j
    · exact tw0_1_6_7_calc j
    · exact tw0_1_6_8_calc j
    · exact tw0_1_6_9_calc j
    · exact tw0_1_6_10_calc j
    · exact tw0_1_6_11_calc j
    · exact tw0_1_6_12_calc j
    · exact tw0_1_6_13_calc j
    · exact tw0_1_6_14_calc j
    · exact tw0_1_6_15_calc j
    · exact tw0_1_6_16_calc j
    · exact tw0_1_6_17_calc j
    · exact tw0_1_6_18_calc j
    · exact tw0_1_6_19_calc j
    · exact tw0_1_6_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 0 1 6 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw0_1 n l j).Mem (taylorWave 0 1 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw0_1_0_mem l j
  · exact tw0_1_1_mem l j
  · exact tw0_1_2_mem l j
  · exact tw0_1_3_mem l j
  · exact tw0_1_4_mem l j
  · exact tw0_1_5_mem l j
  · exact tw0_1_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_0_mem (l : Fin 21) (j : Fin 31) : (tw1_0_0 l j).Mem (taylorWave 1 0 (nearNode 0) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 0 l j = tw1_0_0 l j := by
    fin_cases l
    · exact tw1_0_0_0_calc j
    · exact tw1_0_0_1_calc j
    · exact tw1_0_0_2_calc j
    · exact tw1_0_0_3_calc j
    · exact tw1_0_0_4_calc j
    · exact tw1_0_0_5_calc j
    · exact tw1_0_0_6_calc j
    · exact tw1_0_0_7_calc j
    · exact tw1_0_0_8_calc j
    · exact tw1_0_0_9_calc j
    · exact tw1_0_0_10_calc j
    · exact tw1_0_0_11_calc j
    · exact tw1_0_0_12_calc j
    · exact tw1_0_0_13_calc j
    · exact tw1_0_0_14_calc j
    · exact tw1_0_0_15_calc j
    · exact tw1_0_0_16_calc j
    · exact tw1_0_0_17_calc j
    · exact tw1_0_0_18_calc j
    · exact tw1_0_0_19_calc j
    · exact tw1_0_0_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 0 0 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_1_mem (l : Fin 21) (j : Fin 31) : (tw1_0_1 l j).Mem (taylorWave 1 0 (nearNode 1) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 1 l j = tw1_0_1 l j := by
    fin_cases l
    · exact tw1_0_1_0_calc j
    · exact tw1_0_1_1_calc j
    · exact tw1_0_1_2_calc j
    · exact tw1_0_1_3_calc j
    · exact tw1_0_1_4_calc j
    · exact tw1_0_1_5_calc j
    · exact tw1_0_1_6_calc j
    · exact tw1_0_1_7_calc j
    · exact tw1_0_1_8_calc j
    · exact tw1_0_1_9_calc j
    · exact tw1_0_1_10_calc j
    · exact tw1_0_1_11_calc j
    · exact tw1_0_1_12_calc j
    · exact tw1_0_1_13_calc j
    · exact tw1_0_1_14_calc j
    · exact tw1_0_1_15_calc j
    · exact tw1_0_1_16_calc j
    · exact tw1_0_1_17_calc j
    · exact tw1_0_1_18_calc j
    · exact tw1_0_1_19_calc j
    · exact tw1_0_1_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 0 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_2_mem (l : Fin 21) (j : Fin 31) : (tw1_0_2 l j).Mem (taylorWave 1 0 (nearNode 2) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 2 l j = tw1_0_2 l j := by
    fin_cases l
    · exact tw1_0_2_0_calc j
    · exact tw1_0_2_1_calc j
    · exact tw1_0_2_2_calc j
    · exact tw1_0_2_3_calc j
    · exact tw1_0_2_4_calc j
    · exact tw1_0_2_5_calc j
    · exact tw1_0_2_6_calc j
    · exact tw1_0_2_7_calc j
    · exact tw1_0_2_8_calc j
    · exact tw1_0_2_9_calc j
    · exact tw1_0_2_10_calc j
    · exact tw1_0_2_11_calc j
    · exact tw1_0_2_12_calc j
    · exact tw1_0_2_13_calc j
    · exact tw1_0_2_14_calc j
    · exact tw1_0_2_15_calc j
    · exact tw1_0_2_16_calc j
    · exact tw1_0_2_17_calc j
    · exact tw1_0_2_18_calc j
    · exact tw1_0_2_19_calc j
    · exact tw1_0_2_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 0 2 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_mem (l : Fin 21) (j : Fin 31) : (tw1_0_3 l j).Mem (taylorWave 1 0 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 3 l j = tw1_0_3 l j := by
    fin_cases l
    · exact tw1_0_3_0_calc j
    · exact tw1_0_3_1_calc j
    · exact tw1_0_3_2_calc j
    · exact tw1_0_3_3_calc j
    · exact tw1_0_3_4_calc j
    · exact tw1_0_3_5_calc j
    · exact tw1_0_3_6_calc j
    · exact tw1_0_3_7_calc j
    · exact tw1_0_3_8_calc j
    · exact tw1_0_3_9_calc j
    · exact tw1_0_3_10_calc j
    · exact tw1_0_3_11_calc j
    · exact tw1_0_3_12_calc j
    · exact tw1_0_3_13_calc j
    · exact tw1_0_3_14_calc j
    · exact tw1_0_3_15_calc j
    · exact tw1_0_3_16_calc j
    · exact tw1_0_3_17_calc j
    · exact tw1_0_3_18_calc j
    · exact tw1_0_3_19_calc j
    · exact tw1_0_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 0 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_4_mem (l : Fin 21) (j : Fin 31) : (tw1_0_4 l j).Mem (taylorWave 1 0 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 4 l j = tw1_0_4 l j := by
    fin_cases l
    · exact tw1_0_4_0_calc j
    · exact tw1_0_4_1_calc j
    · exact tw1_0_4_2_calc j
    · exact tw1_0_4_3_calc j
    · exact tw1_0_4_4_calc j
    · exact tw1_0_4_5_calc j
    · exact tw1_0_4_6_calc j
    · exact tw1_0_4_7_calc j
    · exact tw1_0_4_8_calc j
    · exact tw1_0_4_9_calc j
    · exact tw1_0_4_10_calc j
    · exact tw1_0_4_11_calc j
    · exact tw1_0_4_12_calc j
    · exact tw1_0_4_13_calc j
    · exact tw1_0_4_14_calc j
    · exact tw1_0_4_15_calc j
    · exact tw1_0_4_16_calc j
    · exact tw1_0_4_17_calc j
    · exact tw1_0_4_18_calc j
    · exact tw1_0_4_19_calc j
    · exact tw1_0_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 0 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_5_mem (l : Fin 21) (j : Fin 31) : (tw1_0_5 l j).Mem (taylorWave 1 0 (nearNode 5) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 5 l j = tw1_0_5 l j := by
    fin_cases l
    · exact tw1_0_5_0_calc j
    · exact tw1_0_5_1_calc j
    · exact tw1_0_5_2_calc j
    · exact tw1_0_5_3_calc j
    · exact tw1_0_5_4_calc j
    · exact tw1_0_5_5_calc j
    · exact tw1_0_5_6_calc j
    · exact tw1_0_5_7_calc j
    · exact tw1_0_5_8_calc j
    · exact tw1_0_5_9_calc j
    · exact tw1_0_5_10_calc j
    · exact tw1_0_5_11_calc j
    · exact tw1_0_5_12_calc j
    · exact tw1_0_5_13_calc j
    · exact tw1_0_5_14_calc j
    · exact tw1_0_5_15_calc j
    · exact tw1_0_5_16_calc j
    · exact tw1_0_5_17_calc j
    · exact tw1_0_5_18_calc j
    · exact tw1_0_5_19_calc j
    · exact tw1_0_5_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 0 5 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_6_mem (l : Fin 21) (j : Fin 31) : (tw1_0_6 l j).Mem (taylorWave 1 0 (nearNode 6) l.val (frequency j)) := by
  have he : taylorWaveBox 1 0 6 l j = tw1_0_6 l j := by
    fin_cases l
    · exact tw1_0_6_0_calc j
    · exact tw1_0_6_1_calc j
    · exact tw1_0_6_2_calc j
    · exact tw1_0_6_3_calc j
    · exact tw1_0_6_4_calc j
    · exact tw1_0_6_5_calc j
    · exact tw1_0_6_6_calc j
    · exact tw1_0_6_7_calc j
    · exact tw1_0_6_8_calc j
    · exact tw1_0_6_9_calc j
    · exact tw1_0_6_10_calc j
    · exact tw1_0_6_11_calc j
    · exact tw1_0_6_12_calc j
    · exact tw1_0_6_13_calc j
    · exact tw1_0_6_14_calc j
    · exact tw1_0_6_15_calc j
    · exact tw1_0_6_16_calc j
    · exact tw1_0_6_17_calc j
    · exact tw1_0_6_18_calc j
    · exact tw1_0_6_19_calc j
    · exact tw1_0_6_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 0 6 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw1_0 n l j).Mem (taylorWave 1 0 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw1_0_0_mem l j
  · exact tw1_0_1_mem l j
  · exact tw1_0_2_mem l j
  · exact tw1_0_3_mem l j
  · exact tw1_0_4_mem l j
  · exact tw1_0_5_mem l j
  · exact tw1_0_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_0_mem (l : Fin 21) (j : Fin 31) : (tw1_1_0 l j).Mem (taylorWave 1 1 (nearNode 0) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 0 l j = tw1_1_0 l j := by
    fin_cases l
    · exact tw1_1_0_0_calc j
    · exact tw1_1_0_1_calc j
    · exact tw1_1_0_2_calc j
    · exact tw1_1_0_3_calc j
    · exact tw1_1_0_4_calc j
    · exact tw1_1_0_5_calc j
    · exact tw1_1_0_6_calc j
    · exact tw1_1_0_7_calc j
    · exact tw1_1_0_8_calc j
    · exact tw1_1_0_9_calc j
    · exact tw1_1_0_10_calc j
    · exact tw1_1_0_11_calc j
    · exact tw1_1_0_12_calc j
    · exact tw1_1_0_13_calc j
    · exact tw1_1_0_14_calc j
    · exact tw1_1_0_15_calc j
    · exact tw1_1_0_16_calc j
    · exact tw1_1_0_17_calc j
    · exact tw1_1_0_18_calc j
    · exact tw1_1_0_19_calc j
    · exact tw1_1_0_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 1 0 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_1_mem (l : Fin 21) (j : Fin 31) : (tw1_1_1 l j).Mem (taylorWave 1 1 (nearNode 1) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 1 l j = tw1_1_1 l j := by
    fin_cases l
    · exact tw1_1_1_0_calc j
    · exact tw1_1_1_1_calc j
    · exact tw1_1_1_2_calc j
    · exact tw1_1_1_3_calc j
    · exact tw1_1_1_4_calc j
    · exact tw1_1_1_5_calc j
    · exact tw1_1_1_6_calc j
    · exact tw1_1_1_7_calc j
    · exact tw1_1_1_8_calc j
    · exact tw1_1_1_9_calc j
    · exact tw1_1_1_10_calc j
    · exact tw1_1_1_11_calc j
    · exact tw1_1_1_12_calc j
    · exact tw1_1_1_13_calc j
    · exact tw1_1_1_14_calc j
    · exact tw1_1_1_15_calc j
    · exact tw1_1_1_16_calc j
    · exact tw1_1_1_17_calc j
    · exact tw1_1_1_18_calc j
    · exact tw1_1_1_19_calc j
    · exact tw1_1_1_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 1 1 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_2_mem (l : Fin 21) (j : Fin 31) : (tw1_1_2 l j).Mem (taylorWave 1 1 (nearNode 2) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 2 l j = tw1_1_2 l j := by
    fin_cases l
    · exact tw1_1_2_0_calc j
    · exact tw1_1_2_1_calc j
    · exact tw1_1_2_2_calc j
    · exact tw1_1_2_3_calc j
    · exact tw1_1_2_4_calc j
    · exact tw1_1_2_5_calc j
    · exact tw1_1_2_6_calc j
    · exact tw1_1_2_7_calc j
    · exact tw1_1_2_8_calc j
    · exact tw1_1_2_9_calc j
    · exact tw1_1_2_10_calc j
    · exact tw1_1_2_11_calc j
    · exact tw1_1_2_12_calc j
    · exact tw1_1_2_13_calc j
    · exact tw1_1_2_14_calc j
    · exact tw1_1_2_15_calc j
    · exact tw1_1_2_16_calc j
    · exact tw1_1_2_17_calc j
    · exact tw1_1_2_18_calc j
    · exact tw1_1_2_19_calc j
    · exact tw1_1_2_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 1 2 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_3_mem (l : Fin 21) (j : Fin 31) : (tw1_1_3 l j).Mem (taylorWave 1 1 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 3 l j = tw1_1_3 l j := by
    fin_cases l
    · exact tw1_1_3_0_calc j
    · exact tw1_1_3_1_calc j
    · exact tw1_1_3_2_calc j
    · exact tw1_1_3_3_calc j
    · exact tw1_1_3_4_calc j
    · exact tw1_1_3_5_calc j
    · exact tw1_1_3_6_calc j
    · exact tw1_1_3_7_calc j
    · exact tw1_1_3_8_calc j
    · exact tw1_1_3_9_calc j
    · exact tw1_1_3_10_calc j
    · exact tw1_1_3_11_calc j
    · exact tw1_1_3_12_calc j
    · exact tw1_1_3_13_calc j
    · exact tw1_1_3_14_calc j
    · exact tw1_1_3_15_calc j
    · exact tw1_1_3_16_calc j
    · exact tw1_1_3_17_calc j
    · exact tw1_1_3_18_calc j
    · exact tw1_1_3_19_calc j
    · exact tw1_1_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 1 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_4_mem (l : Fin 21) (j : Fin 31) : (tw1_1_4 l j).Mem (taylorWave 1 1 (nearNode 4) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 4 l j = tw1_1_4 l j := by
    fin_cases l
    · exact tw1_1_4_0_calc j
    · exact tw1_1_4_1_calc j
    · exact tw1_1_4_2_calc j
    · exact tw1_1_4_3_calc j
    · exact tw1_1_4_4_calc j
    · exact tw1_1_4_5_calc j
    · exact tw1_1_4_6_calc j
    · exact tw1_1_4_7_calc j
    · exact tw1_1_4_8_calc j
    · exact tw1_1_4_9_calc j
    · exact tw1_1_4_10_calc j
    · exact tw1_1_4_11_calc j
    · exact tw1_1_4_12_calc j
    · exact tw1_1_4_13_calc j
    · exact tw1_1_4_14_calc j
    · exact tw1_1_4_15_calc j
    · exact tw1_1_4_16_calc j
    · exact tw1_1_4_17_calc j
    · exact tw1_1_4_18_calc j
    · exact tw1_1_4_19_calc j
    · exact tw1_1_4_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 1 4 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_5_mem (l : Fin 21) (j : Fin 31) : (tw1_1_5 l j).Mem (taylorWave 1 1 (nearNode 5) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 5 l j = tw1_1_5 l j := by
    fin_cases l
    · exact tw1_1_5_0_calc j
    · exact tw1_1_5_1_calc j
    · exact tw1_1_5_2_calc j
    · exact tw1_1_5_3_calc j
    · exact tw1_1_5_4_calc j
    · exact tw1_1_5_5_calc j
    · exact tw1_1_5_6_calc j
    · exact tw1_1_5_7_calc j
    · exact tw1_1_5_8_calc j
    · exact tw1_1_5_9_calc j
    · exact tw1_1_5_10_calc j
    · exact tw1_1_5_11_calc j
    · exact tw1_1_5_12_calc j
    · exact tw1_1_5_13_calc j
    · exact tw1_1_5_14_calc j
    · exact tw1_1_5_15_calc j
    · exact tw1_1_5_16_calc j
    · exact tw1_1_5_17_calc j
    · exact tw1_1_5_18_calc j
    · exact tw1_1_5_19_calc j
    · exact tw1_1_5_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 1 5 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_6_mem (l : Fin 21) (j : Fin 31) : (tw1_1_6 l j).Mem (taylorWave 1 1 (nearNode 6) l.val (frequency j)) := by
  have he : taylorWaveBox 1 1 6 l j = tw1_1_6 l j := by
    fin_cases l
    · exact tw1_1_6_0_calc j
    · exact tw1_1_6_1_calc j
    · exact tw1_1_6_2_calc j
    · exact tw1_1_6_3_calc j
    · exact tw1_1_6_4_calc j
    · exact tw1_1_6_5_calc j
    · exact tw1_1_6_6_calc j
    · exact tw1_1_6_7_calc j
    · exact tw1_1_6_8_calc j
    · exact tw1_1_6_9_calc j
    · exact tw1_1_6_10_calc j
    · exact tw1_1_6_11_calc j
    · exact tw1_1_6_12_calc j
    · exact tw1_1_6_13_calc j
    · exact tw1_1_6_14_calc j
    · exact tw1_1_6_15_calc j
    · exact tw1_1_6_16_calc j
    · exact tw1_1_6_17_calc j
    · exact tw1_1_6_18_calc j
    · exact tw1_1_6_19_calc j
    · exact tw1_1_6_20_calc j
  rw [← he]
  exact taylorWaveBox_mem 1 1 6 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw1_1 n l j).Mem (taylorWave 1 1 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw1_1_0_mem l j
  · exact tw1_1_1_mem l j
  · exact tw1_1_2_mem l j
  · exact tw1_1_3_mem l j
  · exact tw1_1_4_mem l j
  · exact tw1_1_5_mem l j
  · exact tw1_1_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma taylorWaveTable_mem (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) :
    (taylorWaveTable q br n l j).Mem (taylorWave q br (nearNode n) l.val (frequency j)) := by
  fin_cases q <;> fin_cases br
  · exact tw0_0_mem n l j
  · exact tw0_1_mem n l j
  · exact tw1_0_mem n l j
  · exact tw1_1_mem n l j

lemma taylorRowBox_mem (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) :
    (taylorRowBox side n y l r).Mem
      (taylorRow side (nearNode n) (nearDisplacement n y) l.val r) := by
  exact RI.mem_mul (RI.mem_pow (nearDisplacementBox_mem n y) l.val)
    (CI.mem_sum (fun q => CI.mem_sum (fun j => CI.mem_add
      (CI.mem_mul (spectrumTable_mem side q j r) (taylorWaveTable_mem q 0 n l j))
      (CI.mem_mul (spectrumTable_mem (otherSide side) q j r) (taylorWaveTable_mem q 1 n l j))))).1

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_0_1_mem (l : Fin 21) (r : Fin 8) : (tr0_0_1 l r).Mem (taylorRow 0 (nearNode 0) (nearDisplacement 0 1) l.val r) := by
  have he : taylorRowBox 0 0 1 l r = tr0_0_1 l r := by
    fin_cases l
    · exact tr0_0_1_0_calc r
    · exact tr0_0_1_1_calc r
    · exact tr0_0_1_2_calc r
    · exact tr0_0_1_3_calc r
    · exact tr0_0_1_4_calc r
    · exact tr0_0_1_5_calc r
    · exact tr0_0_1_6_calc r
    · exact tr0_0_1_7_calc r
    · exact tr0_0_1_8_calc r
    · exact tr0_0_1_9_calc r
    · exact tr0_0_1_10_calc r
    · exact tr0_0_1_11_calc r
    · exact tr0_0_1_12_calc r
    · exact tr0_0_1_13_calc r
    · exact tr0_0_1_14_calc r
    · exact tr0_0_1_15_calc r
    · exact tr0_0_1_16_calc r
    · exact tr0_0_1_17_calc r
    · exact tr0_0_1_18_calc r
    · exact tr0_0_1_19_calc r
    · exact tr0_0_1_20_calc r
  rw [← he]
  exact taylorRowBox_mem 0 0 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma exceptional_tr_mem (l : Fin 21) (r : Fin 8) :
    (tr0_0_1 l r).Mem (taylorRow 0 1 1 l.val r) := by
  have hh := tr0_0_1_mem l r
  have hn : nearNode 0 = 1 := by norm_num [nearNode, finiteNode, residue]
  have hy : nearDisplacement 0 1 = 1 := by norm_num [nearDisplacement,nearDisplacementNum]
  simpa only [hn,hy] using hh
lemma frozenTaylorRowBox_mem {z : RI} {x : ℝ} (hz : z.Mem x) (l : Fin 21) (r : Fin 8) :
    (frozenTaylorRowBox z l r).Mem (frozenTaylorRow x l.val r) := by
  unfold frozenTaylorRowBox frozenTaylorRow
  apply RI.mem_sub
  · split_ifs
    · exact ep0
    · exact RI.mem_neg (exceptional_tr_mem l r)
  · split_ifs
    · exact RI.mem_mul hz (exceptional_tr_mem l 0)
    · exact ep0

lemma exceptionalRowBox_mem (test : Fin 4) (l : Fin 23) (r : Fin 8) :
    (exceptionalRowBox test l r).Mem (exceptionalRow test l r) := by
  unfold exceptionalRowBox exceptionalRow
  apply RI.mem_add (exceptionalOffsetBox_mem test l.val r)
  apply RI.mem_sum
  intro ep
  apply RI.mem_sum
  intro j
  split
  · apply RI.mem_mul (exceptionalWeightBox_mem test ep j)
    apply frozenTaylorRowBox_mem
    split_ifs
    · exact ep0
    · exact ZBox_mem
  · exact ep0
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex0r_mem (l : Fin 23) (r : Fin 8) : (ex0r l r).Mem (exceptionalRow 0 l r) := by
  have he : exceptionalRowBox 0 l r = ex0r l r := by
    fin_cases l
    · exact ex0r0_calc r
    · exact ex0r1_calc r
    · exact ex0r2_calc r
    · exact ex0r3_calc r
    · exact ex0r4_calc r
    · exact ex0r5_calc r
    · exact ex0r6_calc r
    · exact ex0r7_calc r
    · exact ex0r8_calc r
    · exact ex0r9_calc r
    · exact ex0r10_calc r
    · exact ex0r11_calc r
    · exact ex0r12_calc r
    · exact ex0r13_calc r
    · exact ex0r14_calc r
    · exact ex0r15_calc r
    · exact ex0r16_calc r
    · exact ex0r17_calc r
    · exact ex0r18_calc r
    · exact ex0r19_calc r
    · exact ex0r20_calc r
    · exact ex0r21_calc r
    · exact ex0r22_calc r
  rw [←he]
  exact exceptionalRowBox_mem 0 l r
lemma ex0b_mem (l : Fin 23) (r : Fin 8) : (ex0b l r).Mem (bernsteinRows 22 (exceptionalRow 0) l r) := by
  have he : bernsteinRowsBox 22 ex0r l r = ex0b l r := by
    fin_cases l
    · exact ex0b0_calc r
    · exact ex0b1_calc r
    · exact ex0b2_calc r
    · exact ex0b3_calc r
    · exact ex0b4_calc r
    · exact ex0b5_calc r
    · exact ex0b6_calc r
    · exact ex0b7_calc r
    · exact ex0b8_calc r
    · exact ex0b9_calc r
    · exact ex0b10_calc r
    · exact ex0b11_calc r
    · exact ex0b12_calc r
    · exact ex0b13_calc r
    · exact ex0b14_calc r
    · exact ex0b15_calc r
    · exact ex0b16_calc r
    · exact ex0b17_calc r
    · exact ex0b18_calc r
    · exact ex0b19_calc r
    · exact ex0b20_calc r
    · exact ex0b21_calc r
    · exact ex0b22_calc r
  rw [←he]
  exact bernsteinRowsBox_mem 22 ex0r_mem l r
lemma ex0b_lower (d : Fin 23) : (46/1000:ℝ) < rowLower (bernsteinRows 22 (exceptionalRow 0) d) := by
  have hc : ∀ d : Fin 23, (46:ℤ)*scale < 1000*(rowLowerBox (ex0b d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (ex0b_mem d)).1
  have hnum : (46:ℝ)*(scale:ℝ) < 1000*((rowLowerBox (ex0b d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma exceptional_sign_0 (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (46/1000:ℝ) < exceptionalValue 0 e τ := by
  rw [←exceptionalRow_eval 0 e (polytope_one e he)]
  exact polytope_polynomial_lower 22 (exceptionalRow 0) _ ex0b_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex1r_mem (l : Fin 23) (r : Fin 8) : (ex1r l r).Mem (exceptionalRow 1 l r) := by
  have he : exceptionalRowBox 1 l r = ex1r l r := by
    fin_cases l
    · exact ex1r0_calc r
    · exact ex1r1_calc r
    · exact ex1r2_calc r
    · exact ex1r3_calc r
    · exact ex1r4_calc r
    · exact ex1r5_calc r
    · exact ex1r6_calc r
    · exact ex1r7_calc r
    · exact ex1r8_calc r
    · exact ex1r9_calc r
    · exact ex1r10_calc r
    · exact ex1r11_calc r
    · exact ex1r12_calc r
    · exact ex1r13_calc r
    · exact ex1r14_calc r
    · exact ex1r15_calc r
    · exact ex1r16_calc r
    · exact ex1r17_calc r
    · exact ex1r18_calc r
    · exact ex1r19_calc r
    · exact ex1r20_calc r
    · exact ex1r21_calc r
    · exact ex1r22_calc r
  rw [←he]
  exact exceptionalRowBox_mem 1 l r
lemma ex1b_mem (l : Fin 23) (r : Fin 8) : (ex1b l r).Mem (bernsteinRows 22 (exceptionalRow 1) l r) := by
  have he : bernsteinRowsBox 22 ex1r l r = ex1b l r := by
    fin_cases l
    · exact ex1b0_calc r
    · exact ex1b1_calc r
    · exact ex1b2_calc r
    · exact ex1b3_calc r
    · exact ex1b4_calc r
    · exact ex1b5_calc r
    · exact ex1b6_calc r
    · exact ex1b7_calc r
    · exact ex1b8_calc r
    · exact ex1b9_calc r
    · exact ex1b10_calc r
    · exact ex1b11_calc r
    · exact ex1b12_calc r
    · exact ex1b13_calc r
    · exact ex1b14_calc r
    · exact ex1b15_calc r
    · exact ex1b16_calc r
    · exact ex1b17_calc r
    · exact ex1b18_calc r
    · exact ex1b19_calc r
    · exact ex1b20_calc r
    · exact ex1b21_calc r
    · exact ex1b22_calc r
  rw [←he]
  exact bernsteinRowsBox_mem 22 ex1r_mem l r
lemma ex1b_lower (d : Fin 23) : (56/1000:ℝ) < rowLower (bernsteinRows 22 (exceptionalRow 1) d) := by
  have hc : ∀ d : Fin 23, (56:ℤ)*scale < 1000*(rowLowerBox (ex1b d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (ex1b_mem d)).1
  have hnum : (56:ℝ)*(scale:ℝ) < 1000*((rowLowerBox (ex1b d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma exceptional_sign_1 (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (56/1000:ℝ) < exceptionalValue 1 e τ := by
  rw [←exceptionalRow_eval 1 e (polytope_one e he)]
  exact polytope_polynomial_lower 22 (exceptionalRow 1) _ ex1b_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex2r_mem (l : Fin 23) (r : Fin 8) : (ex2r l r).Mem (exceptionalRow 2 l r) := by
  have he : exceptionalRowBox 2 l r = ex2r l r := by
    fin_cases l
    · exact ex2r0_calc r
    · exact ex2r1_calc r
    · exact ex2r2_calc r
    · exact ex2r3_calc r
    · exact ex2r4_calc r
    · exact ex2r5_calc r
    · exact ex2r6_calc r
    · exact ex2r7_calc r
    · exact ex2r8_calc r
    · exact ex2r9_calc r
    · exact ex2r10_calc r
    · exact ex2r11_calc r
    · exact ex2r12_calc r
    · exact ex2r13_calc r
    · exact ex2r14_calc r
    · exact ex2r15_calc r
    · exact ex2r16_calc r
    · exact ex2r17_calc r
    · exact ex2r18_calc r
    · exact ex2r19_calc r
    · exact ex2r20_calc r
    · exact ex2r21_calc r
    · exact ex2r22_calc r
  rw [←he]
  exact exceptionalRowBox_mem 2 l r
lemma ex2b_mem (l : Fin 23) (r : Fin 8) : (ex2b l r).Mem (bernsteinRows 22 (exceptionalRow 2) l r) := by
  have he : bernsteinRowsBox 22 ex2r l r = ex2b l r := by
    fin_cases l
    · exact ex2b0_calc r
    · exact ex2b1_calc r
    · exact ex2b2_calc r
    · exact ex2b3_calc r
    · exact ex2b4_calc r
    · exact ex2b5_calc r
    · exact ex2b6_calc r
    · exact ex2b7_calc r
    · exact ex2b8_calc r
    · exact ex2b9_calc r
    · exact ex2b10_calc r
    · exact ex2b11_calc r
    · exact ex2b12_calc r
    · exact ex2b13_calc r
    · exact ex2b14_calc r
    · exact ex2b15_calc r
    · exact ex2b16_calc r
    · exact ex2b17_calc r
    · exact ex2b18_calc r
    · exact ex2b19_calc r
    · exact ex2b20_calc r
    · exact ex2b21_calc r
    · exact ex2b22_calc r
  rw [←he]
  exact bernsteinRowsBox_mem 22 ex2r_mem l r
lemma ex2b_lower (d : Fin 23) : (24/1000:ℝ) < rowLower (bernsteinRows 22 (exceptionalRow 2) d) := by
  have hc : ∀ d : Fin 23, (24:ℤ)*scale < 1000*(rowLowerBox (ex2b d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (ex2b_mem d)).1
  have hnum : (24:ℝ)*(scale:ℝ) < 1000*((rowLowerBox (ex2b d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma exceptional_sign_2 (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (24/1000:ℝ) < exceptionalValue 2 e τ := by
  rw [←exceptionalRow_eval 2 e (polytope_one e he)]
  exact polytope_polynomial_lower 22 (exceptionalRow 2) _ ex2b_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex3r_mem (l : Fin 23) (r : Fin 8) : (ex3r l r).Mem (exceptionalRow 3 l r) := by
  have he : exceptionalRowBox 3 l r = ex3r l r := by
    fin_cases l
    · exact ex3r0_calc r
    · exact ex3r1_calc r
    · exact ex3r2_calc r
    · exact ex3r3_calc r
    · exact ex3r4_calc r
    · exact ex3r5_calc r
    · exact ex3r6_calc r
    · exact ex3r7_calc r
    · exact ex3r8_calc r
    · exact ex3r9_calc r
    · exact ex3r10_calc r
    · exact ex3r11_calc r
    · exact ex3r12_calc r
    · exact ex3r13_calc r
    · exact ex3r14_calc r
    · exact ex3r15_calc r
    · exact ex3r16_calc r
    · exact ex3r17_calc r
    · exact ex3r18_calc r
    · exact ex3r19_calc r
    · exact ex3r20_calc r
    · exact ex3r21_calc r
    · exact ex3r22_calc r
  rw [←he]
  exact exceptionalRowBox_mem 3 l r
lemma ex3b_mem (l : Fin 23) (r : Fin 8) : (ex3b l r).Mem (bernsteinRows 22 (exceptionalRow 3) l r) := by
  have he : bernsteinRowsBox 22 ex3r l r = ex3b l r := by
    fin_cases l
    · exact ex3b0_calc r
    · exact ex3b1_calc r
    · exact ex3b2_calc r
    · exact ex3b3_calc r
    · exact ex3b4_calc r
    · exact ex3b5_calc r
    · exact ex3b6_calc r
    · exact ex3b7_calc r
    · exact ex3b8_calc r
    · exact ex3b9_calc r
    · exact ex3b10_calc r
    · exact ex3b11_calc r
    · exact ex3b12_calc r
    · exact ex3b13_calc r
    · exact ex3b14_calc r
    · exact ex3b15_calc r
    · exact ex3b16_calc r
    · exact ex3b17_calc r
    · exact ex3b18_calc r
    · exact ex3b19_calc r
    · exact ex3b20_calc r
    · exact ex3b21_calc r
    · exact ex3b22_calc r
  rw [←he]
  exact bernsteinRowsBox_mem 22 ex3r_mem l r
lemma ex3b_lower (d : Fin 23) : (27/1000:ℝ) < rowLower (bernsteinRows 22 (exceptionalRow 3) d) := by
  have hc : ∀ d : Fin 23, (27:ℤ)*scale < 1000*(rowLowerBox (ex3b d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (ex3b_mem d)).1
  have hnum : (27:ℝ)*(scale:ℝ) < 1000*((rowLowerBox (ex3b d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma exceptional_sign_3 (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (27/1000:ℝ) < exceptionalValue 3 e τ := by
  rw [←exceptionalRow_eval 3 e (polytope_one e he)]
  exact polytope_polynomial_lower 22 (exceptionalRow 3) _ ex3b_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma exceptional_adjusted_nonneg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {v z : ℝ} (hv : v∈Icc 0 1) (hz : 0 ≤ z) (hzB : z ≤ Z) :
    0 ≤ Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*
      ((1-z/Z)*(frozenTaylor 0 e v-3/1000)+(z/Z)*(frozenTaylor Z e v-3/1000)) := by
  let A := frozenTaylor 0 e v
  let D := frozenTaylor Z e v
  let B0 := v^2
  let B1 := v^2+2*Z*v
  let B2 := v^2+4*Z*v+6*Z^2
  have h0 := exceptional_sign_0 e he hv
  have h1 := exceptional_sign_1 e he hv
  have h2 := exceptional_sign_2 e he hv
  have h3 := exceptional_sign_3 e he hv
  change 46/1000 < Q 1+v*A at h0
  change 56/1000 < Q 1*(v+Z)+(2*B1*A+B0*D)/3 at h1
  change 24/1000 < Q 1*(v+2*Z)+(B2*A+2*B1*D)/3 at h2
  change 27/1000 < Q 1*(v+3*Z)+B2*D at h3
  have hv2 : v^2 ≤ 1 := by nlinarith [hv.1,hv.2]
  have hB0 : B0 ≤ 7/2 := by dsimp[B0] <;> linarith
  have hB1 : B1 ≤ 7/2 := by dsimp[B1,Z] <;> nlinarith [hv.1,hv.2]
  have hB2 : B2 ≤ 7/2 := by dsimp[B2,Z] <;> nlinarith [hv.1,hv.2]
  let b0 := v*(Q 1+v*(A-3/1000))
  let b1 := Q 1*(v+Z)+(2*B1*(A-3/1000)+B0*(D-3/1000))/3
  let b2 := Q 1*(v+2*Z)+(B2*(A-3/1000)+2*B1*(D-3/1000))/3
  let b3 := Q 1*(v+3*Z)+B2*(D-3/1000)
  have hb0 : 0 ≤ b0 := by dsimp[b0]; apply mul_nonneg hv.1; nlinarith [hv.2]
  have hb1 : 0 ≤ b1 := by dsimp[b1] <;> nlinarith
  have hb2 : 0 ≤ b2 := by dsimp[b2] <;> nlinarith
  have hb3 : 0 ≤ b3 := by dsimp[b3] <;> nlinarith
  let t := z/Z
  have ht0 : 0 ≤ t := div_nonneg hz (by norm_num[Z])
  have ht1 : t ≤ 1 := (div_le_one (by norm_num[Z])).mpr hzB
  have hzt : z=t*Z := by dsimp[t]; rw [div_mul_cancel₀ _ (by norm_num[Z] : Z≠0)]
  have hid : Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*
      ((1-z/Z)*(A-3/1000)+(z/Z)*(D-3/1000)) =
      b0*(1-t)^3+3*b1*t*(1-t)^2+3*b2*t^2*(1-t)+b3*t^3 := by
    change Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*((1-t)*(A-3/1000)+t*(D-3/1000))=_
    rw[hzt]
    dsimp[b0,b1,b2,b3,B0,B1,B2]
    ring
  change 0 ≤ Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*((1-z/Z)*(A-3/1000)+(z/Z)*(D-3/1000))
  rw[hid]
  positivity
lemma exceptional_rational_comparison_tg_oai (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {v : ℝ} (hv : v∈Icc 0 1) (hz : 0<e 0) (hzB : e 0 ≤ Z) :
    finiteTaylor 0 1 1 e v+3/1000 ≤ Q 1*((3*(e 0)+v)/(6*(e 0)^2+4*(e 0)*v+v^2)) := by
  have hh := exceptional_adjusted_nonneg e he hv hz.le hzB
  have ha := frozenTaylor_affine (e 0) e v
  rw [frozenTaylor_actual e (polytope_one e he)] at ha
  have hv0 := hv.1
  have hd : 0<6*(e 0)^2+4*(e 0)*v+v^2 := by positivity
  rw [←mul_div_assoc,le_div_iff₀ hd]
  nlinarith
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.exceptional_rational_comparison_tg_oai := @OAI.AtomicTriangular.Construction.exceptional_rational_comparison_tg_oai
