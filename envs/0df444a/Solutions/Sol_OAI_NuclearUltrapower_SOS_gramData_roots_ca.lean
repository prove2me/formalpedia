-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.gramData_roots_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:58:17.980086+00:00
-- url     : https://prove2.me/submissions/d6595348-eff5-416e-bff3-c755cd5c4ea5

import Mathlib
import Definitions.Def_OAIQ229C015
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_100_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_101_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_103_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_104_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_105_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_106_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_107_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_108_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_109_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_10_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_110_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_111_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_113_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_114_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_115_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_11_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_12_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_13_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_14_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_15_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_16_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_17_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_18_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_19_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_20_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_21_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_23_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_24_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_25_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_27_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_28_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_29_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_2_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_31_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_32_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_33_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_35_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_36_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_37_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_38_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_39_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_40_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_41_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_42_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_43_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_44_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_45_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_46_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_47_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_49_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_51_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_52_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_53_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_55_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_56_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_57_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_59_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_5_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_61_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_63_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_64_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_65_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_67_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_68_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_69_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_6_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_71_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_75_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_76_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_77_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_78_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_79_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_7_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_80_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_81_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_82_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_83_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_84_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_85_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_87_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_88_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_89_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_91_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_92_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_93_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_95_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_96_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_97_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_99_ca
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_9_ca

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- Exact rational SOS data. All asserted computed identities reduce in the
   stock Lean kernel; the numerical program and these literals are untrusted. -/
namespace NuclearUltrapower.SL3Certificate
theorem gram_row_0 : columns.map (dot q0) = g0 := by decide +kernel
theorem gram_row_1 : columns.map (dot q1) = g1 := by decide +kernel
theorem gram_row_3 : columns.map (dot q3) = g3 := by decide +kernel
theorem gram_row_4 : columns.map (dot q4) = g4 := by decide +kernel
theorem gram_row_8 : columns.map (dot q8) = g8 := by decide +kernel
theorem gram_row_22 : columns.map (dot q22) = g22 := by decide +kernel
theorem gram_row_26 : columns.map (dot q26) = g26 := by decide +kernel
theorem gram_row_30 : columns.map (dot q30) = g30 := by decide +kernel
theorem gram_row_34 : columns.map (dot q34) = g34 := by decide +kernel
theorem gram_row_48 : columns.map (dot q48) = g48 := by decide +kernel
theorem gram_row_50 : columns.map (dot q50) = g50 := by decide +kernel
theorem gram_row_54 : columns.map (dot q54) = g54 := by decide +kernel
theorem gram_row_58 : columns.map (dot q58) = g58 := by decide +kernel
theorem gram_row_60 : columns.map (dot q60) = g60 := by decide +kernel
theorem gram_row_62 : columns.map (dot q62) = g62 := by decide +kernel
theorem gram_row_66 : columns.map (dot q66) = g66 := by decide +kernel
theorem gram_row_70 : columns.map (dot q70) = g70 := by decide +kernel
theorem gram_row_72 : columns.map (dot q72) = g72 := by decide +kernel
theorem gram_row_73 : columns.map (dot q73) = g73 := by decide +kernel
theorem gram_row_74 : columns.map (dot q74) = g74 := by decide +kernel
theorem gram_row_86 : columns.map (dot q86) = g86 := by decide +kernel
theorem gram_row_90 : columns.map (dot q90) = g90 := by decide +kernel
theorem gram_row_94 : columns.map (dot q94) = g94 := by decide +kernel
theorem gram_row_98 : columns.map (dot q98) = g98 := by decide +kernel
theorem gram_row_102 : columns.map (dot q102) = g102 := by decide +kernel
theorem gram_row_112 : columns.map (dot q112) = g112 := by decide +kernel
theorem gram_row_116 : columns.map (dot q116) = g116 := by decide +kernel
theorem gram_row_117 : columns.map (dot q117) = g117 := by decide +kernel
theorem gram_row_118 : columns.map (dot q118) = g118 := by decide +kernel
theorem gram_row_119 : columns.map (dot q119) = g119 := by decide +kernel
theorem gram_row_120 : columns.map (dot q120) = g120 := by decide +kernel
end NuclearUltrapower.SL3Certificate
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate
theorem gramData_eq : gramData = SL3Certificate.gram := by rfl
theorem gramData_roots_ca_oai : gramData = columns.map (fun q => columns.map (dot q)) := by
  rw [gramData_eq]
  change _ = [columns.map (dot q0), columns.map (dot q1), columns.map (dot q2), columns.map (dot q3), columns.map (dot q4), columns.map (dot q5), columns.map (dot q6), columns.map (dot q7), columns.map (dot q8), columns.map (dot q9), columns.map (dot q10), columns.map (dot q11), columns.map (dot q12), columns.map (dot q13), columns.map (dot q14), columns.map (dot q15), columns.map (dot q16), columns.map (dot q17), columns.map (dot q18), columns.map (dot q19), columns.map (dot q20), columns.map (dot q21), columns.map (dot q22), columns.map (dot q23), columns.map (dot q24), columns.map (dot q25), columns.map (dot q26), columns.map (dot q27), columns.map (dot q28), columns.map (dot q29), columns.map (dot q30), columns.map (dot q31), columns.map (dot q32), columns.map (dot q33), columns.map (dot q34), columns.map (dot q35), columns.map (dot q36), columns.map (dot q37), columns.map (dot q38), columns.map (dot q39), columns.map (dot q40), columns.map (dot q41), columns.map (dot q42), columns.map (dot q43), columns.map (dot q44), columns.map (dot q45), columns.map (dot q46), columns.map (dot q47), columns.map (dot q48), columns.map (dot q49), columns.map (dot q50), columns.map (dot q51), columns.map (dot q52), columns.map (dot q53), columns.map (dot q54), columns.map (dot q55), columns.map (dot q56), columns.map (dot q57), columns.map (dot q58), columns.map (dot q59), columns.map (dot q60), columns.map (dot q61), columns.map (dot q62), columns.map (dot q63), columns.map (dot q64), columns.map (dot q65), columns.map (dot q66), columns.map (dot q67), columns.map (dot q68), columns.map (dot q69), columns.map (dot q70), columns.map (dot q71), columns.map (dot q72), columns.map (dot q73), columns.map (dot q74), columns.map (dot q75), columns.map (dot q76), columns.map (dot q77), columns.map (dot q78), columns.map (dot q79), columns.map (dot q80), columns.map (dot q81), columns.map (dot q82), columns.map (dot q83), columns.map (dot q84), columns.map (dot q85), columns.map (dot q86), columns.map (dot q87), columns.map (dot q88), columns.map (dot q89), columns.map (dot q90), columns.map (dot q91), columns.map (dot q92), columns.map (dot q93), columns.map (dot q94), columns.map (dot q95), columns.map (dot q96), columns.map (dot q97), columns.map (dot q98), columns.map (dot q99), columns.map (dot q100), columns.map (dot q101), columns.map (dot q102), columns.map (dot q103), columns.map (dot q104), columns.map (dot q105), columns.map (dot q106), columns.map (dot q107), columns.map (dot q108), columns.map (dot q109), columns.map (dot q110), columns.map (dot q111), columns.map (dot q112), columns.map (dot q113), columns.map (dot q114), columns.map (dot q115), columns.map (dot q116), columns.map (dot q117), columns.map (dot q118), columns.map (dot q119), columns.map (dot q120)]
  rw [gram_row_0, gram_row_1, gram_row_2_ca, gram_row_3, gram_row_4, gram_row_5_ca, gram_row_6_ca, gram_row_7_ca, gram_row_8, gram_row_9_ca, gram_row_10_ca, gram_row_11_ca, gram_row_12_ca, gram_row_13_ca, gram_row_14_ca, gram_row_15_ca, gram_row_16_ca, gram_row_17_ca, gram_row_18_ca, gram_row_19_ca, gram_row_20_ca, gram_row_21_ca, gram_row_22, gram_row_23_ca, gram_row_24_ca, gram_row_25_ca, gram_row_26, gram_row_27_ca, gram_row_28_ca, gram_row_29_ca, gram_row_30, gram_row_31_ca, gram_row_32_ca, gram_row_33_ca, gram_row_34, gram_row_35_ca, gram_row_36_ca, gram_row_37_ca, gram_row_38_ca, gram_row_39_ca, gram_row_40_ca, gram_row_41_ca, gram_row_42_ca, gram_row_43_ca, gram_row_44_ca, gram_row_45_ca, gram_row_46_ca, gram_row_47_ca, gram_row_48, gram_row_49_ca, gram_row_50, gram_row_51_ca, gram_row_52_ca, gram_row_53_ca, gram_row_54, gram_row_55_ca, gram_row_56_ca, gram_row_57_ca, gram_row_58, gram_row_59_ca, gram_row_60, gram_row_61_ca, gram_row_62, gram_row_63_ca, gram_row_64_ca, gram_row_65_ca, gram_row_66, gram_row_67_ca, gram_row_68_ca, gram_row_69_ca, gram_row_70, gram_row_71_ca, gram_row_72, gram_row_73, gram_row_74, gram_row_75_ca, gram_row_76_ca, gram_row_77_ca, gram_row_78_ca, gram_row_79_ca, gram_row_80_ca, gram_row_81_ca, gram_row_82_ca, gram_row_83_ca, gram_row_84_ca, gram_row_85_ca, gram_row_86, gram_row_87_ca, gram_row_88_ca, gram_row_89_ca, gram_row_90, gram_row_91_ca, gram_row_92_ca, gram_row_93_ca, gram_row_94, gram_row_95_ca, gram_row_96_ca, gram_row_97_ca, gram_row_98, gram_row_99_ca, gram_row_100_ca, gram_row_101_ca, gram_row_102, gram_row_103_ca, gram_row_104_ca, gram_row_105_ca, gram_row_106_ca, gram_row_107_ca, gram_row_108_ca, gram_row_109_ca, gram_row_110_ca, gram_row_111_ca, gram_row_112, gram_row_113_ca, gram_row_114_ca, gram_row_115_ca, gram_row_116, gram_row_117, gram_row_118, gram_row_119, gram_row_120]
  rfl

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.gramData_roots_ca_oai := @OAI.NuclearUltrapower.SOS.gramData_roots_ca_oai
