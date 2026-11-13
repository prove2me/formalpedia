-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_5_1_tg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:35:04.273034+00:00
-- url     : https://prove2.me/submissions/eb198629-0a35-4922-94f5-c436fc4e43be

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
import Definitions.Def_OAIQ262T191
import Definitions.Def_OAIQ262T195
import Definitions.Def_OAIQ262T196
import Definitions.Def_OAIQ262T222
import Definitions.Def_OAIQ262T239
import Definitions.Def_OAIQ262T246
import Definitions.Def_OAIQ262T247
import Definitions.Def_OAIQ262T248
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
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_5_1_mem (l : Fin 21) (r : Fin 8) : (tr1_5_1 l r).Mem (taylorRow 1 (nearNode 5) (nearDisplacement 5 1) l.val r) := by
  have he : taylorRowBox 1 5 1 l r = tr1_5_1 l r := by
    fin_cases l
    · exact tr1_5_1_0_calc r
    · exact tr1_5_1_1_calc r
    · exact tr1_5_1_2_calc r
    · exact tr1_5_1_3_calc r
    · exact tr1_5_1_4_calc r
    · exact tr1_5_1_5_calc r
    · exact tr1_5_1_6_calc r
    · exact tr1_5_1_7_calc r
    · exact tr1_5_1_8_calc r
    · exact tr1_5_1_9_calc r
    · exact tr1_5_1_10_calc r
    · exact tr1_5_1_11_calc r
    · exact tr1_5_1_12_calc r
    · exact tr1_5_1_13_calc r
    · exact tr1_5_1_14_calc r
    · exact tr1_5_1_15_calc r
    · exact tr1_5_1_16_calc r
    · exact tr1_5_1_17_calc r
    · exact tr1_5_1_18_calc r
    · exact tr1_5_1_19_calc r
    · exact tr1_5_1_20_calc r
  rw [← he]
  exact taylorRowBox_mem 1 5 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma bs1_5_1_mem (d : Fin 21) (r : Fin 8) : (bs1_5_1 d r).Mem (bernsteinRows 20 (ordinarySignRow 1 5 1) d r) := by
  have he : bernsteinRowsBox 20 (ordinarySignRowBox 1 5 tr1_5_1) d r = bs1_5_1 d r := by
    fin_cases d
    · exact bs1_5_1_0_calc r
    · exact bs1_5_1_1_calc r
    · exact bs1_5_1_2_calc r
    · exact bs1_5_1_3_calc r
    · exact bs1_5_1_4_calc r
    · exact bs1_5_1_5_calc r
    · exact bs1_5_1_6_calc r
    · exact bs1_5_1_7_calc r
    · exact bs1_5_1_8_calc r
    · exact bs1_5_1_9_calc r
    · exact bs1_5_1_10_calc r
    · exact bs1_5_1_11_calc r
    · exact bs1_5_1_12_calc r
    · exact bs1_5_1_13_calc r
    · exact bs1_5_1_14_calc r
    · exact bs1_5_1_15_calc r
    · exact bs1_5_1_16_calc r
    · exact bs1_5_1_17_calc r
    · exact bs1_5_1_18_calc r
    · exact bs1_5_1_19_calc r
    · exact bs1_5_1_20_calc r
  rw [← he]
  exact bernsteinRowsBox_mem 20 (ordinarySignRowBox_mem 1 5 1 tr1_5_1_mem) d r
lemma bs1_5_1_lower (d : Fin 21) : (2000/1000000:ℝ) < rowLower (bernsteinRows 20 (ordinarySignRow 1 5 1) d) := by
  have hc : ∀ d : Fin 21, (2000:ℤ)*scale < 1000000*(rowLowerBox (bs1_5_1 d)).lo := by decide +kernel
  have hh := (rowLowerBox_mem (bs1_5_1_mem d)).1
  have hnum : (2000:ℝ)*(scale:ℝ) < 1000000*((rowLowerBox (bs1_5_1 d)).lo:ℝ) := by exact_mod_cast hc d
  nlinarith [scale_pos]
lemma ordinary_sign_1_5_1_tg_oai (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (2000/1000000:ℝ) < ordinarySignValue 1 5 1 e τ := by
  rw [ordinarySignValue_eq]
  exact polytope_polynomial_lower 20 (ordinarySignRow 1 5 1) _ bs1_5_1_lower e he hτ
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_5_1_tg_oai := @OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_5_1_tg_oai
