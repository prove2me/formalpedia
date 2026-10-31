-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.gramData_roots
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:54:59.204642+00:00
-- url     : https://prove2.me/submissions/f548281f-4170-4565-b0dd-cf8c1aeb5e1e

import Mathlib
import Definitions.Def_OAIQ019N041
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_100
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_101
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_102
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_103
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_104
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_105
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_106
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_107
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_108
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_109
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_110
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_111
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_112
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_113
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_114
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_115
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_116
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_117
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_118
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_119
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_120
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_20
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_21
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_22
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_23
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_24
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_25
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_26
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_27
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_28
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_29
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_30
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_31
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_32
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_33
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_34
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_35
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_36
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_37
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_38
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_39
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_40
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_41
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_42
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_43
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_44
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_45
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_46
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_47
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_48
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_49
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_50
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_51
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_52
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_53
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_54
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_55
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_56
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_57
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_58
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_59
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_60
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_61
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_62
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_63
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_64
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_65
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_66
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_67
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_68
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_69
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_70
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_71
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_72
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_73
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_74
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_75
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_76
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_77
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_78
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_79
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_80
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_81
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_82
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_83
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_84
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_85
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_86
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_87
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_88
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_89
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_90
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_91
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_92
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_93
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_94
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_95
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_96
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_97
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_98
import Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_99
import Theorems.Thm_OAI_NuclearUltrapower_SOS_gramData_eq

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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
theorem gram_row_2 : columns.map (dot q2) = g2 := by decide +kernel
theorem gram_row_3 : columns.map (dot q3) = g3 := by decide +kernel
theorem gram_row_4 : columns.map (dot q4) = g4 := by decide +kernel
theorem gram_row_5 : columns.map (dot q5) = g5 := by decide +kernel
theorem gram_row_6 : columns.map (dot q6) = g6 := by decide +kernel
theorem gram_row_7 : columns.map (dot q7) = g7 := by decide +kernel
theorem gram_row_8 : columns.map (dot q8) = g8 := by decide +kernel
theorem gram_row_9 : columns.map (dot q9) = g9 := by decide +kernel
theorem gram_row_10 : columns.map (dot q10) = g10 := by decide +kernel
theorem gram_row_11 : columns.map (dot q11) = g11 := by decide +kernel
theorem gram_row_12 : columns.map (dot q12) = g12 := by decide +kernel
theorem gram_row_13 : columns.map (dot q13) = g13 := by decide +kernel
theorem gram_row_14 : columns.map (dot q14) = g14 := by decide +kernel
theorem gram_row_15 : columns.map (dot q15) = g15 := by decide +kernel
theorem gram_row_16 : columns.map (dot q16) = g16 := by decide +kernel
theorem gram_row_17 : columns.map (dot q17) = g17 := by decide +kernel
theorem gram_row_18 : columns.map (dot q18) = g18 := by decide +kernel
theorem gram_row_19 : columns.map (dot q19) = g19 := by decide +kernel
end NuclearUltrapower.SL3Certificate
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate
theorem gramData_roots_oai : gramData = columns.map (fun q => columns.map (dot q)) := by
  rw [gramData_eq]
  change _ = [columns.map (dot q0), columns.map (dot q1), columns.map (dot q2), columns.map (dot q3), columns.map (dot q4), columns.map (dot q5), columns.map (dot q6), columns.map (dot q7), columns.map (dot q8), columns.map (dot q9), columns.map (dot q10), columns.map (dot q11), columns.map (dot q12), columns.map (dot q13), columns.map (dot q14), columns.map (dot q15), columns.map (dot q16), columns.map (dot q17), columns.map (dot q18), columns.map (dot q19), columns.map (dot q20), columns.map (dot q21), columns.map (dot q22), columns.map (dot q23), columns.map (dot q24), columns.map (dot q25), columns.map (dot q26), columns.map (dot q27), columns.map (dot q28), columns.map (dot q29), columns.map (dot q30), columns.map (dot q31), columns.map (dot q32), columns.map (dot q33), columns.map (dot q34), columns.map (dot q35), columns.map (dot q36), columns.map (dot q37), columns.map (dot q38), columns.map (dot q39), columns.map (dot q40), columns.map (dot q41), columns.map (dot q42), columns.map (dot q43), columns.map (dot q44), columns.map (dot q45), columns.map (dot q46), columns.map (dot q47), columns.map (dot q48), columns.map (dot q49), columns.map (dot q50), columns.map (dot q51), columns.map (dot q52), columns.map (dot q53), columns.map (dot q54), columns.map (dot q55), columns.map (dot q56), columns.map (dot q57), columns.map (dot q58), columns.map (dot q59), columns.map (dot q60), columns.map (dot q61), columns.map (dot q62), columns.map (dot q63), columns.map (dot q64), columns.map (dot q65), columns.map (dot q66), columns.map (dot q67), columns.map (dot q68), columns.map (dot q69), columns.map (dot q70), columns.map (dot q71), columns.map (dot q72), columns.map (dot q73), columns.map (dot q74), columns.map (dot q75), columns.map (dot q76), columns.map (dot q77), columns.map (dot q78), columns.map (dot q79), columns.map (dot q80), columns.map (dot q81), columns.map (dot q82), columns.map (dot q83), columns.map (dot q84), columns.map (dot q85), columns.map (dot q86), columns.map (dot q87), columns.map (dot q88), columns.map (dot q89), columns.map (dot q90), columns.map (dot q91), columns.map (dot q92), columns.map (dot q93), columns.map (dot q94), columns.map (dot q95), columns.map (dot q96), columns.map (dot q97), columns.map (dot q98), columns.map (dot q99), columns.map (dot q100), columns.map (dot q101), columns.map (dot q102), columns.map (dot q103), columns.map (dot q104), columns.map (dot q105), columns.map (dot q106), columns.map (dot q107), columns.map (dot q108), columns.map (dot q109), columns.map (dot q110), columns.map (dot q111), columns.map (dot q112), columns.map (dot q113), columns.map (dot q114), columns.map (dot q115), columns.map (dot q116), columns.map (dot q117), columns.map (dot q118), columns.map (dot q119), columns.map (dot q120)]
  rw [gram_row_0, gram_row_1, gram_row_2, gram_row_3, gram_row_4, gram_row_5, gram_row_6, gram_row_7, gram_row_8, gram_row_9, gram_row_10, gram_row_11, gram_row_12, gram_row_13, gram_row_14, gram_row_15, gram_row_16, gram_row_17, gram_row_18, gram_row_19, gram_row_20, gram_row_21, gram_row_22, gram_row_23, gram_row_24, gram_row_25, gram_row_26, gram_row_27, gram_row_28, gram_row_29, gram_row_30, gram_row_31, gram_row_32, gram_row_33, gram_row_34, gram_row_35, gram_row_36, gram_row_37, gram_row_38, gram_row_39, gram_row_40, gram_row_41, gram_row_42, gram_row_43, gram_row_44, gram_row_45, gram_row_46, gram_row_47, gram_row_48, gram_row_49, gram_row_50, gram_row_51, gram_row_52, gram_row_53, gram_row_54, gram_row_55, gram_row_56, gram_row_57, gram_row_58, gram_row_59, gram_row_60, gram_row_61, gram_row_62, gram_row_63, gram_row_64, gram_row_65, gram_row_66, gram_row_67, gram_row_68, gram_row_69, gram_row_70, gram_row_71, gram_row_72, gram_row_73, gram_row_74, gram_row_75, gram_row_76, gram_row_77, gram_row_78, gram_row_79, gram_row_80, gram_row_81, gram_row_82, gram_row_83, gram_row_84, gram_row_85, gram_row_86, gram_row_87, gram_row_88, gram_row_89, gram_row_90, gram_row_91, gram_row_92, gram_row_93, gram_row_94, gram_row_95, gram_row_96, gram_row_97, gram_row_98, gram_row_99, gram_row_100, gram_row_101, gram_row_102, gram_row_103, gram_row_104, gram_row_105, gram_row_106, gram_row_107, gram_row_108, gram_row_109, gram_row_110, gram_row_111, gram_row_112, gram_row_113, gram_row_114, gram_row_115, gram_row_116, gram_row_117, gram_row_118, gram_row_119, gram_row_120]
  rfl

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.gramData_roots_oai := @OAI.NuclearUltrapower.SOS.gramData_roots_oai
