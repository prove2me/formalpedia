-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.bottom_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:24:18.422676+00:00
-- url     : https://prove2.me/submissions/bb3ab6a2-37e0-40ab-9019-04711b4213ff

import Mathlib
import Definitions.Def_OAIEG011

section
-- module Solutions.OAIEG.SeedContraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem d1_h0_cert_7 : ∀ v : Fin 103,
    rowEval (d1Row 7) (h0Coeff v) =
      (if 7 = v then 1 else 0) - (if 7 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_8 : ∀ v : Fin 103,
    rowEval (d1Row 8) (h0Coeff v) =
      (if 8 = v then 1 else 0) - (if 8 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_9 : ∀ v : Fin 103,
    rowEval (d1Row 9) (h0Coeff v) =
      (if 9 = v then 1 else 0) - (if 9 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_68 : ∀ v : Fin 103,
    rowEval (d1Row 68) (h0Coeff v) =
      (if 68 = v then 1 else 0) - (if 68 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_69 : ∀ v : Fin 103,
    rowEval (d1Row 69) (h0Coeff v) =
      (if 69 = v then 1 else 0) - (if 69 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_70 : ∀ v : Fin 103,
    rowEval (d1Row 70) (h0Coeff v) =
      (if 70 = v then 1 else 0) - (if 70 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_71 : ∀ v : Fin 103,
    rowEval (d1Row 71) (h0Coeff v) =
      (if 71 = v then 1 else 0) - (if 71 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_72 : ∀ v : Fin 103,
    rowEval (d1Row 72) (h0Coeff v) =
      (if 72 = v then 1 else 0) - (if 72 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_73 : ∀ v : Fin 103,
    rowEval (d1Row 73) (h0Coeff v) =
      (if 73 = v then 1 else 0) - (if 73 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_74 : ∀ v : Fin 103,
    rowEval (d1Row 74) (h0Coeff v) =
      (if 74 = v then 1 else 0) - (if 74 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_75 : ∀ v : Fin 103,
    rowEval (d1Row 75) (h0Coeff v) =
      (if 75 = v then 1 else 0) - (if 75 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_76 : ∀ v : Fin 103,
    rowEval (d1Row 76) (h0Coeff v) =
      (if 76 = v then 1 else 0) - (if 76 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_77 : ∀ v : Fin 103,
    rowEval (d1Row 77) (h0Coeff v) =
      (if 77 = v then 1 else 0) - (if 77 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_78 : ∀ v : Fin 103,
    rowEval (d1Row 78) (h0Coeff v) =
      (if 78 = v then 1 else 0) - (if 78 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_79 : ∀ v : Fin 103,
    rowEval (d1Row 79) (h0Coeff v) =
      (if 79 = v then 1 else 0) - (if 79 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_80 : ∀ v : Fin 103,
    rowEval (d1Row 80) (h0Coeff v) =
      (if 80 = v then 1 else 0) - (if 80 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_81 : ∀ v : Fin 103,
    rowEval (d1Row 81) (h0Coeff v) =
      (if 81 = v then 1 else 0) - (if 81 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_82 : ∀ v : Fin 103,
    rowEval (d1Row 82) (h0Coeff v) =
      (if 82 = v then 1 else 0) - (if 82 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_83 : ∀ v : Fin 103,
    rowEval (d1Row 83) (h0Coeff v) =
      (if 83 = v then 1 else 0) - (if 83 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_84 : ∀ v : Fin 103,
    rowEval (d1Row 84) (h0Coeff v) =
      (if 84 = v then 1 else 0) - (if 84 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_85 : ∀ v : Fin 103,
    rowEval (d1Row 85) (h0Coeff v) =
      (if 85 = v then 1 else 0) - (if 85 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_86 : ∀ v : Fin 103,
    rowEval (d1Row 86) (h0Coeff v) =
      (if 86 = v then 1 else 0) - (if 86 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_87 : ∀ v : Fin 103,
    rowEval (d1Row 87) (h0Coeff v) =
      (if 87 = v then 1 else 0) - (if 87 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_88 : ∀ v : Fin 103,
    rowEval (d1Row 88) (h0Coeff v) =
      (if 88 = v then 1 else 0) - (if 88 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_89 : ∀ v : Fin 103,
    rowEval (d1Row 89) (h0Coeff v) =
      (if 89 = v then 1 else 0) - (if 89 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_90 : ∀ v : Fin 103,
    rowEval (d1Row 90) (h0Coeff v) =
      (if 90 = v then 1 else 0) - (if 90 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_91 : ∀ v : Fin 103,
    rowEval (d1Row 91) (h0Coeff v) =
      (if 91 = v then 1 else 0) - (if 91 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_92 : ∀ v : Fin 103,
    rowEval (d1Row 92) (h0Coeff v) =
      (if 92 = v then 1 else 0) - (if 92 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_93 : ∀ v : Fin 103,
    rowEval (d1Row 93) (h0Coeff v) =
      (if 93 = v then 1 else 0) - (if 93 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_94 : ∀ v : Fin 103,
    rowEval (d1Row 94) (h0Coeff v) =
      (if 94 = v then 1 else 0) - (if 94 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_95 : ∀ v : Fin 103,
    rowEval (d1Row 95) (h0Coeff v) =
      (if 95 = v then 1 else 0) - (if 95 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_96 : ∀ v : Fin 103,
    rowEval (d1Row 96) (h0Coeff v) =
      (if 96 = v then 1 else 0) - (if 96 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_97 : ∀ v : Fin 103,
    rowEval (d1Row 97) (h0Coeff v) =
      (if 97 = v then 1 else 0) - (if 97 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_98 : ∀ v : Fin 103,
    rowEval (d1Row 98) (h0Coeff v) =
      (if 98 = v then 1 else 0) - (if 98 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_99 : ∀ v : Fin 103,
    rowEval (d1Row 99) (h0Coeff v) =
      (if 99 = v then 1 else 0) - (if 99 = 0 then 1 else 0) := by decide +kernel

theorem d1_h0_cert_blk_0 (i : Fin 103) (hb : 0 ≤ i.val ∧ i.val < 30) (v : Fin 103) :
    rowEval (d1Row i) (h0Coeff v) =
      (if i = v then 1 else 0) - (if i = 0 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_h0_cert_0 v
  · exact d1_h0_cert_1 v
  · exact d1_h0_cert_2 v
  · exact d1_h0_cert_3 v
  · exact d1_h0_cert_4 v
  · exact d1_h0_cert_5 v
  · exact d1_h0_cert_6 v
  · exact d1_h0_cert_7 v
  · exact d1_h0_cert_8 v
  · exact d1_h0_cert_9 v
  · exact d1_h0_cert_10 v
  · exact d1_h0_cert_11 v
  · exact d1_h0_cert_12 v
  · exact d1_h0_cert_13 v
  · exact d1_h0_cert_14 v
  · exact d1_h0_cert_15 v
  · exact d1_h0_cert_16 v
  · exact d1_h0_cert_17 v
  · exact d1_h0_cert_18 v
  · exact d1_h0_cert_19 v
  · exact d1_h0_cert_20 v
  · exact d1_h0_cert_21 v
  · exact d1_h0_cert_22 v
  · exact d1_h0_cert_23 v
  · exact d1_h0_cert_24 v
  · exact d1_h0_cert_25 v
  · exact d1_h0_cert_26 v
  · exact d1_h0_cert_27 v
  · exact d1_h0_cert_28 v
  · exact d1_h0_cert_29 v

theorem d1_h0_cert_blk_1 (i : Fin 103) (hb : 30 ≤ i.val ∧ i.val < 60) (v : Fin 103) :
    rowEval (d1Row i) (h0Coeff v) =
      (if i = v then 1 else 0) - (if i = 0 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_h0_cert_30 v
  · exact d1_h0_cert_31 v
  · exact d1_h0_cert_32 v
  · exact d1_h0_cert_33 v
  · exact d1_h0_cert_34 v
  · exact d1_h0_cert_35 v
  · exact d1_h0_cert_36 v
  · exact d1_h0_cert_37 v
  · exact d1_h0_cert_38 v
  · exact d1_h0_cert_39 v
  · exact d1_h0_cert_40 v
  · exact d1_h0_cert_41 v
  · exact d1_h0_cert_42 v
  · exact d1_h0_cert_43 v
  · exact d1_h0_cert_44 v
  · exact d1_h0_cert_45 v
  · exact d1_h0_cert_46 v
  · exact d1_h0_cert_47 v
  · exact d1_h0_cert_48 v
  · exact d1_h0_cert_49 v
  · exact d1_h0_cert_50 v
  · exact d1_h0_cert_51 v
  · exact d1_h0_cert_52 v
  · exact d1_h0_cert_53 v
  · exact d1_h0_cert_54 v
  · exact d1_h0_cert_55 v
  · exact d1_h0_cert_56 v
  · exact d1_h0_cert_57 v
  · exact d1_h0_cert_58 v
  · exact d1_h0_cert_59 v

theorem d1_h0_cert_blk_2 (i : Fin 103) (hb : 60 ≤ i.val ∧ i.val < 90) (v : Fin 103) :
    rowEval (d1Row i) (h0Coeff v) =
      (if i = v then 1 else 0) - (if i = 0 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_h0_cert_60 v
  · exact d1_h0_cert_61 v
  · exact d1_h0_cert_62 v
  · exact d1_h0_cert_63 v
  · exact d1_h0_cert_64 v
  · exact d1_h0_cert_65 v
  · exact d1_h0_cert_66 v
  · exact d1_h0_cert_67 v
  · exact d1_h0_cert_68 v
  · exact d1_h0_cert_69 v
  · exact d1_h0_cert_70 v
  · exact d1_h0_cert_71 v
  · exact d1_h0_cert_72 v
  · exact d1_h0_cert_73 v
  · exact d1_h0_cert_74 v
  · exact d1_h0_cert_75 v
  · exact d1_h0_cert_76 v
  · exact d1_h0_cert_77 v
  · exact d1_h0_cert_78 v
  · exact d1_h0_cert_79 v
  · exact d1_h0_cert_80 v
  · exact d1_h0_cert_81 v
  · exact d1_h0_cert_82 v
  · exact d1_h0_cert_83 v
  · exact d1_h0_cert_84 v
  · exact d1_h0_cert_85 v
  · exact d1_h0_cert_86 v
  · exact d1_h0_cert_87 v
  · exact d1_h0_cert_88 v
  · exact d1_h0_cert_89 v

theorem d1_h0_cert_blk_3 (i : Fin 103) (hb : 90 ≤ i.val ∧ i.val < 103) (v : Fin 103) :
    rowEval (d1Row i) (h0Coeff v) =
      (if i = v then 1 else 0) - (if i = 0 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_h0_cert_90 v
  · exact d1_h0_cert_91 v
  · exact d1_h0_cert_92 v
  · exact d1_h0_cert_93 v
  · exact d1_h0_cert_94 v
  · exact d1_h0_cert_95 v
  · exact d1_h0_cert_96 v
  · exact d1_h0_cert_97 v
  · exact d1_h0_cert_98 v
  · exact d1_h0_cert_99 v
  · exact d1_h0_cert_100 v
  · exact d1_h0_cert_101 v
  · exact d1_h0_cert_102 v

theorem d1_h0_cert (i : Fin 103) (v : Fin 103) :
    rowEval (d1Row i) (h0Coeff v) =
      (if i = v then 1 else 0) - (if i = 0 then 1 else 0) := by
  have hlt := i.isLt
  rcases (by omega : (0 ≤ i.val ∧ i.val < 30) ∨ (30 ≤ i.val ∧ i.val < 60) ∨ (60 ≤ i.val ∧ i.val < 90) ∨ (90 ≤ i.val ∧ i.val < 103)) with h | h | h | h
  · exact d1_h0_cert_blk_0 i h v
  · exact d1_h0_cert_blk_1 i h v
  · exact d1_h0_cert_blk_2 i h v
  · exact d1_h0_cert_blk_3 i h v

attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions
theorem bottom_identity_oai (v : Fin 103) : d₁ (h₀ (Pi.single v 1)) = Pi.single v 1 - Pi.single 0 1 :=
by
  apply FiniteIntegralContraction.certificate_bottom d1Row h0Coeff 0
  intro i v
  simpa only [rowEval,FiniteIntegralContraction.rowEval,fin_ite] using d1_h0_cert i v

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.bottom_identity_oai := @OAI.EilenbergGanea.SeedChainCertificate.bottom_identity_oai
