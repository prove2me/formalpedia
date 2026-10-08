-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block08_part03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T12:05:39.248528+00:00
-- url     : https://prove2.me/submissions/864dac47-386a-4a93-bf13-099a3dfcd317

import Definitions.Def_Snaky21Data08
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_part02_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl
theorem valid_0 : Valid card_0 := block00_valid.1
theorem valid_1 : Valid card_1 := block00_valid.2.1
theorem valid_2 : Valid card_2 := block00_valid.2.2.1
theorem valid_3 : Valid card_3 := block00_valid.2.2.2.1
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_5 : Valid card_5 := block00_valid.2.2.2.2.2.1
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_8 : Valid card_8 := block00_valid.2.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_10 : Valid card_10 := block00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_12 : Valid card_12 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_16 : Valid card_16 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_17 : Valid card_17 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_18 : Valid card_18 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_19 : Valid card_19 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_20 : Valid card_20 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_21 : Valid card_21 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_23 : Valid card_23 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_24 : Valid card_24 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_25 : Valid card_25 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_26 : Valid card_26 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_27 : Valid card_27 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_28 : Valid card_28 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_29 : Valid card_29 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_30 : Valid card_30 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_31 : Valid card_31 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_32 : Valid card_32 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_33 : Valid card_33 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_34 : Valid card_34 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_35 : Valid card_35 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_36 : Valid card_36 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_37 : Valid card_37 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_38 : Valid card_38 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_39 : Valid card_39 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_40 : Valid card_40 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_41 : Valid card_41 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_42 : Valid card_42 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_43 : Valid card_43 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_45 : Valid card_45 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_46 : Valid card_46 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_47 : Valid card_47 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_48 : Valid card_48 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_49 : Valid card_49 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_50 : Valid card_50 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_51 : Valid card_51 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_54 : Valid card_54 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_55 : Valid card_55 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_57 : Valid card_57 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_58 : Valid card_58 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_59 : Valid card_59 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_60 : Valid card_60 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_61 : Valid card_61 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_62 : Valid card_62 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_63 : Valid card_63 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_64 : Valid card_64 := block01_valid.1
theorem valid_65 : Valid card_65 := block01_valid.2.1
theorem valid_66 : Valid card_66 := block01_valid.2.2.1
theorem valid_67 : Valid card_67 := block01_valid.2.2.2.1
theorem valid_68 : Valid card_68 := block01_valid.2.2.2.2.1
theorem valid_69 : Valid card_69 := block01_valid.2.2.2.2.2.1
theorem valid_70 : Valid card_70 := block01_valid.2.2.2.2.2.2.1
theorem valid_71 : Valid card_71 := block01_valid.2.2.2.2.2.2.2.1
theorem valid_72 : Valid card_72 := block01_valid.2.2.2.2.2.2.2.2.1
theorem valid_73 : Valid card_73 := block01_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_74 : Valid card_74 := block01_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_75 : Valid card_75 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_76 : Valid card_76 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_77 : Valid card_77 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_78 : Valid card_78 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_79 : Valid card_79 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_80 : Valid card_80 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_81 : Valid card_81 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_82 : Valid card_82 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_83 : Valid card_83 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_84 : Valid card_84 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_85 : Valid card_85 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_86 : Valid card_86 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_87 : Valid card_87 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_88 : Valid card_88 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_89 : Valid card_89 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_90 : Valid card_90 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_91 : Valid card_91 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_92 : Valid card_92 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_93 : Valid card_93 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_94 : Valid card_94 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_95 : Valid card_95 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_96 : Valid card_96 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_97 : Valid card_97 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_98 : Valid card_98 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_99 : Valid card_99 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_100 : Valid card_100 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_101 : Valid card_101 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_102 : Valid card_102 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_103 : Valid card_103 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_104 : Valid card_104 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_105 : Valid card_105 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_106 : Valid card_106 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_107 : Valid card_107 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_108 : Valid card_108 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_109 : Valid card_109 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_110 : Valid card_110 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_111 : Valid card_111 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_112 : Valid card_112 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_113 : Valid card_113 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_114 : Valid card_114 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_115 : Valid card_115 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_116 : Valid card_116 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_117 : Valid card_117 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_118 : Valid card_118 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_119 : Valid card_119 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_120 : Valid card_120 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_121 : Valid card_121 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_122 : Valid card_122 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_123 : Valid card_123 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_124 : Valid card_124 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_125 : Valid card_125 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_126 : Valid card_126 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_127 : Valid card_127 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_128 : Valid card_128 := block02_valid.1
theorem valid_129 : Valid card_129 := block02_valid.2.1
theorem valid_130 : Valid card_130 := block02_valid.2.2.1
theorem valid_131 : Valid card_131 := block02_valid.2.2.2.1
theorem valid_132 : Valid card_132 := block02_valid.2.2.2.2.1
theorem valid_133 : Valid card_133 := block02_valid.2.2.2.2.2.1
theorem valid_134 : Valid card_134 := block02_valid.2.2.2.2.2.2.1
theorem valid_135 : Valid card_135 := block02_valid.2.2.2.2.2.2.2.1
theorem valid_136 : Valid card_136 := block02_valid.2.2.2.2.2.2.2.2.1
theorem valid_137 : Valid card_137 := block02_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_138 : Valid card_138 := block02_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_139 : Valid card_139 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_140 : Valid card_140 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_141 : Valid card_141 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_142 : Valid card_142 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_143 : Valid card_143 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_144 : Valid card_144 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_145 : Valid card_145 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_146 : Valid card_146 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_147 : Valid card_147 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_148 : Valid card_148 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_149 : Valid card_149 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_150 : Valid card_150 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_151 : Valid card_151 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_152 : Valid card_152 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_153 : Valid card_153 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_154 : Valid card_154 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_155 : Valid card_155 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_156 : Valid card_156 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_157 : Valid card_157 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_158 : Valid card_158 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_159 : Valid card_159 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_160 : Valid card_160 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_161 : Valid card_161 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_162 : Valid card_162 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_163 : Valid card_163 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_164 : Valid card_164 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_165 : Valid card_165 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_166 : Valid card_166 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_167 : Valid card_167 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_168 : Valid card_168 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_169 : Valid card_169 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_170 : Valid card_170 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_171 : Valid card_171 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_172 : Valid card_172 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_173 : Valid card_173 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_174 : Valid card_174 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_175 : Valid card_175 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_176 : Valid card_176 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_177 : Valid card_177 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_178 : Valid card_178 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_179 : Valid card_179 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_181 : Valid card_181 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_182 : Valid card_182 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_183 : Valid card_183 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_184 : Valid card_184 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_185 : Valid card_185 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_186 : Valid card_186 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_187 : Valid card_187 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_188 : Valid card_188 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_189 : Valid card_189 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_190 : Valid card_190 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_191 : Valid card_191 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_192 : Valid card_192 := block03_valid.1
theorem valid_193 : Valid card_193 := block03_valid.2.1
theorem valid_194 : Valid card_194 := block03_valid.2.2.1
theorem valid_195 : Valid card_195 := block03_valid.2.2.2.1
theorem valid_196 : Valid card_196 := block03_valid.2.2.2.2.1
theorem valid_197 : Valid card_197 := block03_valid.2.2.2.2.2.1
theorem valid_198 : Valid card_198 := block03_valid.2.2.2.2.2.2.1
theorem valid_199 : Valid card_199 := block03_valid.2.2.2.2.2.2.2.1
theorem valid_200 : Valid card_200 := block03_valid.2.2.2.2.2.2.2.2.1
theorem valid_201 : Valid card_201 := block03_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_202 : Valid card_202 := block03_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_203 : Valid card_203 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_204 : Valid card_204 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_205 : Valid card_205 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_206 : Valid card_206 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_207 : Valid card_207 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_208 : Valid card_208 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_209 : Valid card_209 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_210 : Valid card_210 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_211 : Valid card_211 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_212 : Valid card_212 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_213 : Valid card_213 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_214 : Valid card_214 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_215 : Valid card_215 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_216 : Valid card_216 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_217 : Valid card_217 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_218 : Valid card_218 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_219 : Valid card_219 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_220 : Valid card_220 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_221 : Valid card_221 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_222 : Valid card_222 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_223 : Valid card_223 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_224 : Valid card_224 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_225 : Valid card_225 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_226 : Valid card_226 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_227 : Valid card_227 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_228 : Valid card_228 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_229 : Valid card_229 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_230 : Valid card_230 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_231 : Valid card_231 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_232 : Valid card_232 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_233 : Valid card_233 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_234 : Valid card_234 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_235 : Valid card_235 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_236 : Valid card_236 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_237 : Valid card_237 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_238 : Valid card_238 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_239 : Valid card_239 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_240 : Valid card_240 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_241 : Valid card_241 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_242 : Valid card_242 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_243 : Valid card_243 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_244 : Valid card_244 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_245 : Valid card_245 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_246 : Valid card_246 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_247 : Valid card_247 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_248 : Valid card_248 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_249 : Valid card_249 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_250 : Valid card_250 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_251 : Valid card_251 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_252 : Valid card_252 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_253 : Valid card_253 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_254 : Valid card_254 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_255 : Valid card_255 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_256 : Valid card_256 := block04_valid.1
theorem valid_257 : Valid card_257 := block04_valid.2.1
theorem valid_258 : Valid card_258 := block04_valid.2.2.1
theorem valid_259 : Valid card_259 := block04_valid.2.2.2.1
theorem valid_260 : Valid card_260 := block04_valid.2.2.2.2.1
theorem valid_261 : Valid card_261 := block04_valid.2.2.2.2.2.1
theorem valid_262 : Valid card_262 := block04_valid.2.2.2.2.2.2.1
theorem valid_263 : Valid card_263 := block04_valid.2.2.2.2.2.2.2.1
theorem valid_264 : Valid card_264 := block04_valid.2.2.2.2.2.2.2.2.1
theorem valid_265 : Valid card_265 := block04_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_266 : Valid card_266 := block04_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_267 : Valid card_267 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_268 : Valid card_268 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_269 : Valid card_269 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_270 : Valid card_270 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_271 : Valid card_271 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_272 : Valid card_272 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_273 : Valid card_273 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_274 : Valid card_274 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_275 : Valid card_275 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_276 : Valid card_276 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_277 : Valid card_277 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_278 : Valid card_278 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_279 : Valid card_279 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_280 : Valid card_280 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_281 : Valid card_281 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_282 : Valid card_282 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_283 : Valid card_283 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_284 : Valid card_284 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_285 : Valid card_285 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_286 : Valid card_286 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_287 : Valid card_287 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_288 : Valid card_288 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_289 : Valid card_289 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_290 : Valid card_290 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_291 : Valid card_291 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_292 : Valid card_292 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_293 : Valid card_293 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_294 : Valid card_294 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_295 : Valid card_295 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_296 : Valid card_296 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_297 : Valid card_297 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_298 : Valid card_298 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_299 : Valid card_299 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_300 : Valid card_300 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_301 : Valid card_301 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_302 : Valid card_302 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_303 : Valid card_303 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_304 : Valid card_304 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_305 : Valid card_305 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_306 : Valid card_306 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_307 : Valid card_307 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_308 : Valid card_308 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_309 : Valid card_309 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_310 : Valid card_310 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_311 : Valid card_311 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_312 : Valid card_312 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_313 : Valid card_313 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_314 : Valid card_314 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_315 : Valid card_315 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_316 : Valid card_316 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_317 : Valid card_317 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_318 : Valid card_318 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_319 : Valid card_319 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_320 : Valid card_320 := block05_valid.1
theorem valid_321 : Valid card_321 := block05_valid.2.1
theorem valid_322 : Valid card_322 := block05_valid.2.2.1
theorem valid_323 : Valid card_323 := block05_valid.2.2.2.1
theorem valid_324 : Valid card_324 := block05_valid.2.2.2.2.1
theorem valid_325 : Valid card_325 := block05_valid.2.2.2.2.2.1
theorem valid_326 : Valid card_326 := block05_valid.2.2.2.2.2.2.1
theorem valid_327 : Valid card_327 := block05_valid.2.2.2.2.2.2.2.1
theorem valid_328 : Valid card_328 := block05_valid.2.2.2.2.2.2.2.2.1
theorem valid_329 : Valid card_329 := block05_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_330 : Valid card_330 := block05_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_331 : Valid card_331 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_332 : Valid card_332 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_333 : Valid card_333 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_334 : Valid card_334 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_335 : Valid card_335 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_336 : Valid card_336 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_337 : Valid card_337 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_338 : Valid card_338 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_339 : Valid card_339 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_340 : Valid card_340 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_341 : Valid card_341 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_342 : Valid card_342 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_343 : Valid card_343 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_344 : Valid card_344 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_345 : Valid card_345 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_346 : Valid card_346 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_347 : Valid card_347 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_348 : Valid card_348 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_349 : Valid card_349 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_350 : Valid card_350 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_351 : Valid card_351 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_352 : Valid card_352 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_353 : Valid card_353 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_354 : Valid card_354 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_355 : Valid card_355 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_356 : Valid card_356 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_357 : Valid card_357 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_358 : Valid card_358 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_359 : Valid card_359 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_360 : Valid card_360 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_361 : Valid card_361 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_362 : Valid card_362 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_363 : Valid card_363 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_364 : Valid card_364 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_365 : Valid card_365 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_366 : Valid card_366 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_367 : Valid card_367 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_368 : Valid card_368 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_369 : Valid card_369 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_370 : Valid card_370 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_371 : Valid card_371 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_372 : Valid card_372 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_373 : Valid card_373 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_374 : Valid card_374 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_375 : Valid card_375 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_376 : Valid card_376 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_377 : Valid card_377 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_378 : Valid card_378 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_379 : Valid card_379 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_380 : Valid card_380 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_381 : Valid card_381 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_382 : Valid card_382 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_383 : Valid card_383 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_384 : Valid card_384 := block06_valid.1
theorem valid_385 : Valid card_385 := block06_valid.2.1
theorem valid_386 : Valid card_386 := block06_valid.2.2.1
theorem valid_387 : Valid card_387 := block06_valid.2.2.2.1
theorem valid_388 : Valid card_388 := block06_valid.2.2.2.2.1
theorem valid_389 : Valid card_389 := block06_valid.2.2.2.2.2.1
theorem valid_390 : Valid card_390 := block06_valid.2.2.2.2.2.2.1
theorem valid_391 : Valid card_391 := block06_valid.2.2.2.2.2.2.2.1
theorem valid_392 : Valid card_392 := block06_valid.2.2.2.2.2.2.2.2.1
theorem valid_393 : Valid card_393 := block06_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_394 : Valid card_394 := block06_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_395 : Valid card_395 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_396 : Valid card_396 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_397 : Valid card_397 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_398 : Valid card_398 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_399 : Valid card_399 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_400 : Valid card_400 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_401 : Valid card_401 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_402 : Valid card_402 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_403 : Valid card_403 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_404 : Valid card_404 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_405 : Valid card_405 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_406 : Valid card_406 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_407 : Valid card_407 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_408 : Valid card_408 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_409 : Valid card_409 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_410 : Valid card_410 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_411 : Valid card_411 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_412 : Valid card_412 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_413 : Valid card_413 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_414 : Valid card_414 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_415 : Valid card_415 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_416 : Valid card_416 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_417 : Valid card_417 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_418 : Valid card_418 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_419 : Valid card_419 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_420 : Valid card_420 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_421 : Valid card_421 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_422 : Valid card_422 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_423 : Valid card_423 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_424 : Valid card_424 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_425 : Valid card_425 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_426 : Valid card_426 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_427 : Valid card_427 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_428 : Valid card_428 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_429 : Valid card_429 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_430 : Valid card_430 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_431 : Valid card_431 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_432 : Valid card_432 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_433 : Valid card_433 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_434 : Valid card_434 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_436 : Valid card_436 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_437 : Valid card_437 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_438 : Valid card_438 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_439 : Valid card_439 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_440 : Valid card_440 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_441 : Valid card_441 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_442 : Valid card_442 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_443 : Valid card_443 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_444 : Valid card_444 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_445 : Valid card_445 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_446 : Valid card_446 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_447 : Valid card_447 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_448 : Valid card_448 := block07_valid.1
theorem valid_449 : Valid card_449 := block07_valid.2.1
theorem valid_450 : Valid card_450 := block07_valid.2.2.1
theorem valid_451 : Valid card_451 := block07_valid.2.2.2.1
theorem valid_452 : Valid card_452 := block07_valid.2.2.2.2.1
theorem valid_453 : Valid card_453 := block07_valid.2.2.2.2.2.1
theorem valid_454 : Valid card_454 := block07_valid.2.2.2.2.2.2.1
theorem valid_455 : Valid card_455 := block07_valid.2.2.2.2.2.2.2.1
theorem valid_456 : Valid card_456 := block07_valid.2.2.2.2.2.2.2.2.1
theorem valid_457 : Valid card_457 := block07_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_458 : Valid card_458 := block07_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_459 : Valid card_459 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_460 : Valid card_460 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_461 : Valid card_461 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_462 : Valid card_462 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_463 : Valid card_463 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_464 : Valid card_464 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_465 : Valid card_465 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_466 : Valid card_466 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_467 : Valid card_467 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_468 : Valid card_468 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_469 : Valid card_469 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_470 : Valid card_470 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_471 : Valid card_471 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_472 : Valid card_472 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_473 : Valid card_473 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_474 : Valid card_474 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_475 : Valid card_475 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_476 : Valid card_476 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_477 : Valid card_477 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_478 : Valid card_478 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_479 : Valid card_479 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_480 : Valid card_480 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_481 : Valid card_481 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_482 : Valid card_482 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_483 : Valid card_483 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_484 : Valid card_484 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_485 : Valid card_485 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_486 : Valid card_486 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_487 : Valid card_487 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_488 : Valid card_488 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_489 : Valid card_489 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_490 : Valid card_490 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_491 : Valid card_491 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_492 : Valid card_492 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_493 : Valid card_493 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_494 : Valid card_494 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_495 : Valid card_495 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_496 : Valid card_496 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_497 : Valid card_497 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_498 : Valid card_498 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_499 : Valid card_499 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_500 : Valid card_500 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_501 : Valid card_501 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_502 : Valid card_502 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_503 : Valid card_503 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_504 : Valid card_504 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_505 : Valid card_505 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_506 : Valid card_506 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_507 : Valid card_507 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_508 : Valid card_508 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_509 : Valid card_509 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_510 : Valid card_510 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_511 : Valid card_511 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_512 : Valid card_512 := block08_part00_valid.1
theorem valid_513 : Valid card_513 := block08_part00_valid.2.1
theorem valid_514 : Valid card_514 := block08_part00_valid.2.2.1
theorem valid_515 : Valid card_515 := block08_part00_valid.2.2.2.1
theorem valid_516 : Valid card_516 := block08_part00_valid.2.2.2.2.1
theorem valid_517 : Valid card_517 := block08_part00_valid.2.2.2.2.2.1
theorem valid_518 : Valid card_518 := block08_part00_valid.2.2.2.2.2.2.1
theorem valid_519 : Valid card_519 := block08_part00_valid.2.2.2.2.2.2.2.1
theorem valid_520 : Valid card_520 := block08_part00_valid.2.2.2.2.2.2.2.2.1
theorem valid_521 : Valid card_521 := block08_part00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_522 : Valid card_522 := block08_part00_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_523 : Valid card_523 := block08_part00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_524 : Valid card_524 := block08_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_525 : Valid card_525 := block08_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_526 : Valid card_526 := block08_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_527 : Valid card_527 := block08_part00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_528 : Valid card_528 := block08_part01_valid.1
theorem valid_529 : Valid card_529 := block08_part01_valid.2.1
theorem valid_530 : Valid card_530 := block08_part01_valid.2.2.1
theorem valid_531 : Valid card_531 := block08_part01_valid.2.2.2.1
theorem valid_532 : Valid card_532 := block08_part01_valid.2.2.2.2.1
theorem valid_533 : Valid card_533 := block08_part01_valid.2.2.2.2.2.1
theorem valid_534 : Valid card_534 := block08_part01_valid.2.2.2.2.2.2.1
theorem valid_535 : Valid card_535 := block08_part01_valid.2.2.2.2.2.2.2.1
theorem valid_536 : Valid card_536 := block08_part01_valid.2.2.2.2.2.2.2.2.1
theorem valid_537 : Valid card_537 := block08_part01_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_538 : Valid card_538 := block08_part01_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_539 : Valid card_539 := block08_part01_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_540 : Valid card_540 := block08_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_541 : Valid card_541 := block08_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_542 : Valid card_542 := block08_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_543 : Valid card_543 := block08_part01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_544 : Valid card_544 := block08_part02_valid.1
theorem valid_545 : Valid card_545 := block08_part02_valid.2.1
theorem valid_546 : Valid card_546 := block08_part02_valid.2.2.1
theorem valid_547 : Valid card_547 := block08_part02_valid.2.2.2.1
theorem valid_548 : Valid card_548 := block08_part02_valid.2.2.2.2.1
theorem valid_549 : Valid card_549 := block08_part02_valid.2.2.2.2.2.1
theorem valid_550 : Valid card_550 := block08_part02_valid.2.2.2.2.2.2.1
theorem valid_551 : Valid card_551 := block08_part02_valid.2.2.2.2.2.2.2.1
theorem valid_552 : Valid card_552 := block08_part02_valid.2.2.2.2.2.2.2.2.1
theorem valid_553 : Valid card_553 := block08_part02_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_554 : Valid card_554 := block08_part02_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_555 : Valid card_555 := block08_part02_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_556 : Valid card_556 := block08_part02_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_557 : Valid card_557 := block08_part02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_558 : Valid card_558 := block08_part02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_559 : Valid card_559 := block08_part02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem eq_inline_298 : inline_298 = combine (5, 2) [placed 1 (2, 1) card_44, placed 2 (3, 5) card_156] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_298 : Valid inline_298 := by
  rw [eq_inline_298]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_44
  subst c
  exact placed_valid 2 (3, 5) valid_156

theorem eq_inline_299 : inline_299 = combine (5, 1) [placed 3 (6, 1) card_44, placed 3 (6, 1) card_52, inline_298] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_299 : Valid inline_299 := by
  rw [eq_inline_299]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 1) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 1) valid_52
  subst c
  exact valid_inline_298

theorem eq_inline_300 : inline_300 = combine (4, 1) [placed 5 (3, 4) card_5, inline_299] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_300 : Valid inline_300 := by
  rw [eq_inline_300]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_5
  subst c
  exact valid_inline_299

theorem eq_inline_301 : inline_301 = combine (6, 5) [placed 7 (6, 5) card_153, inline_300] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_301 : Valid inline_301 := by
  rw [eq_inline_301]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_153
  subst c
  exact valid_inline_300

theorem eq_inline_302 : inline_302 = combine (3, 1) [placed 1 (3, 1) card_5, inline_301] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_302 : Valid inline_302 := by
  rw [eq_inline_302]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 1) valid_5
  subst c
  exact valid_inline_301

theorem eq_inline_303 : inline_303 = combine (5, 3) [placed 0 (3, 1) card_227, placed 7 (6, 5) card_245, placed 2 (2, 7) card_274] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_303 : Valid inline_303 := by
  rw [eq_inline_303]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_227
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_245
  subst c
  exact placed_valid 2 (2, 7) valid_274

theorem eq_card_560 : card_560 = combine (5, 4) [placed 5 (1, 5) card_67, placed 0 (2, 1) card_228, placed 2 (2, 5) card_373, placed 2 (2, 7) card_435, placed 0 (3, 1) card_531, inline_302, inline_303, placed 2 (0, 5) card_559] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_560 : Valid card_560 := by
  rw [eq_card_560]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_228
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 5) valid_373
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_531
  rcases hc with rfl | hc
  · exact valid_inline_302
  rcases hc with rfl | hc
  · exact valid_inline_303
  subst c
  exact placed_valid 2 (0, 5) valid_559

theorem eq_inline_304 : inline_304 = combine (2, 4) [placed 7 (2, 7) card_1, placed 0 (0, 2) card_57] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_304 : Valid inline_304 := by
  rw [eq_inline_304]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 7) valid_1
  subst c
  exact placed_valid 0 (0, 2) valid_57

theorem eq_card_561 : card_561 = combine (2, 7) [placed 0 (1, 3) card_154, placed 2 (0, 10) card_319, placed 0 (0, 3) card_335, inline_304] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_561 : Valid card_561 := by
  rw [eq_card_561]
  apply combination_rule (2, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_154
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 10) valid_319
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_335
  subst c
  exact valid_inline_304

theorem eq_inline_305 : inline_305 = combine (3, 5) [placed 4 (4, 1) card_13, placed 0 (2, 1) card_14, placed 4 (4, 1) card_33, placed 0 (1, 2) card_122, placed 2 (1, 6) card_388] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_305 : Valid inline_305 := by
  rw [eq_inline_305]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_122
  subst c
  exact placed_valid 2 (1, 6) valid_388

theorem eq_card_562 : card_562 = combine (3, 3) [placed 5 (0, 4) card_52, placed 6 (4, 7) card_506, inline_305] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_562 : Valid card_562 := by
  rw [eq_card_562]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_506
  subst c
  exact valid_inline_305

theorem eq_inline_306 : inline_306 = combine (2, 6) [placed 7 (2, 7) card_0, placed 2 (1, 7) card_393] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_306 : Valid inline_306 := by
  rw [eq_inline_306]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 7) valid_0
  subst c
  exact placed_valid 2 (1, 7) valid_393

theorem eq_inline_307 : inline_307 = combine (2, 4) [placed 6 (5, 5) card_0, inline_306] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_307 : Valid inline_307 := by
  rw [eq_inline_307]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_0
  subst c
  exact valid_inline_306

theorem eq_inline_308 : inline_308 = combine (3, 3) [placed 6 (3, 7) card_11, placed 7 (4, 6) card_38] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_308 : Valid inline_308 := by
  rw [eq_inline_308]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_11
  subst c
  exact placed_valid 7 (4, 6) valid_38

theorem eq_inline_309 : inline_309 = combine (3, 6) [placed 2 (3, 7) card_15, inline_308] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_309 : Valid inline_309 := by
  rw [eq_inline_309]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_15
  subst c
  exact valid_inline_308

theorem eq_inline_310 : inline_310 = combine (3, 4) [placed 2 (0, 5) card_0, inline_309] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_310 : Valid inline_310 := by
  rw [eq_inline_310]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_0
  subst c
  exact valid_inline_309

theorem eq_inline_311 : inline_311 = combine (4, 4) [placed 2 (1, 5) card_5, inline_310] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_311 : Valid inline_311 := by
  rw [eq_inline_311]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_5
  subst c
  exact valid_inline_310

theorem eq_inline_312 : inline_312 = combine (4, 5) [placed 1 (1, 4) card_18, inline_307, inline_311] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_312 : Valid inline_312 := by
  rw [eq_inline_312]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_18
  rcases hc with rfl | hc
  · exact valid_inline_307
  subst c
  exact valid_inline_311

theorem eq_card_563 : card_563 = combine (3, 5) [placed 2 (0, 7) card_134, placed 2 (0, 7) card_180, placed 2 (1, 8) card_258, placed 2 (0, 8) card_435, placed 0 (0, 2) card_507, inline_312, placed 0 (0, 0) card_561, placed 0 (0, 1) card_562] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_563 : Valid card_563 := by
  rw [eq_card_563]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_258
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_507
  rcases hc with rfl | hc
  · exact valid_inline_312
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_561
  subst c
  exact placed_valid 0 (0, 1) valid_562

theorem eq_inline_313 : inline_313 = combine (2, 4) [placed 0 (2, 4) card_5, placed 4 (5, 3) card_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_313 : Valid inline_313 := by
  rw [eq_inline_313]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_5
  subst c
  exact placed_valid 4 (5, 3) valid_453

theorem eq_inline_314 : inline_314 = combine (3, 5) [placed 0 (2, 5) card_5, placed 4 (5, 2) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_314 : Valid inline_314 := by
  rw [eq_inline_314]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_5
  subst c
  exact placed_valid 4 (5, 2) valid_55

theorem eq_inline_315 : inline_315 = combine (2, 4) [placed 4 (5, 4) card_5, placed 4 (5, 2) card_342] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_315 : Valid inline_315 := by
  rw [eq_inline_315]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 4) valid_5
  subst c
  exact placed_valid 4 (5, 2) valid_342

theorem eq_inline_316 : inline_316 = combine (2, 5) [placed 3 (6, 4) card_102, inline_314, inline_315] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_316 : Valid inline_316 := by
  rw [eq_inline_316]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_102
  rcases hc with rfl | hc
  · exact valid_inline_314
  subst c
  exact valid_inline_315

theorem eq_inline_317 : inline_317 = combine (4, 5) [placed 7 (5, 8) card_0, inline_316] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_317 : Valid inline_317 := by
  rw [eq_inline_317]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 8) valid_0
  subst c
  exact valid_inline_316

theorem eq_inline_318 : inline_318 = combine (5, 7) [placed 4 (5, 4) card_16, placed 6 (6, 8) card_235, inline_317] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_318 : Valid inline_318 := by
  rw [eq_inline_318]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 4) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_235
  subst c
  exact valid_inline_317

theorem eq_inline_319 : inline_319 = combine (5, 6) [placed 4 (6, 2) card_67, placed 3 (7, 3) card_134, placed 3 (7, 3) card_180, placed 7 (9, 7) card_327, placed 0 (2, 2) card_504, placed 3 (7, 4) card_558, inline_318] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_319 : Valid inline_319 := by
  rw [eq_inline_319]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 7) valid_327
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_504
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_558
  subst c
  exact valid_inline_318

theorem eq_inline_320 : inline_320 = combine (5, 5) [placed 1 (2, 4) card_44, inline_313, inline_319, placed 1 (1, 1) card_560, placed 1 (0, 3) card_563] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_320 : Valid inline_320 := by
  rw [eq_inline_320]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_44
  rcases hc with rfl | hc
  · exact valid_inline_313
  rcases hc with rfl | hc
  · exact valid_inline_319
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_560
  subst c
  exact placed_valid 1 (0, 3) valid_563

theorem eq_inline_321 : inline_321 = combine (5, 4) [placed 1 (1, 3) card_12, placed 5 (1, 5) card_12, placed 1 (2, 1) card_79, placed 1 (1, 2) card_135, placed 5 (1, 6) card_182, inline_320] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_321 : Valid inline_321 := by
  rw [eq_inline_321]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_182
  subst c
  exact valid_inline_320

theorem eq_card_564 : card_564 = combine (4, 4) [placed 1 (1, 1) card_119, placed 4 (4, 0) card_497, placed 0 (0, 0) card_498, inline_321] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_564 : Valid card_564 := by
  rw [eq_card_564]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_119
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_497
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_498
  subst c
  exact valid_inline_321

theorem eq_inline_322 : inline_322 = combine (5, 3) [placed 2 (2, 3) card_5, placed 0 (1, 1) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_322 : Valid inline_322 := by
  rw [eq_inline_322]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 3) valid_5
  subst c
  exact placed_valid 0 (1, 1) valid_179

theorem eq_inline_323 : inline_323 = combine (1, 3) [placed 2 (1, 3) card_4, placed 0 (0, 0) card_142] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_323 : Valid inline_323 := by
  rw [eq_inline_323]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 3) valid_4
  subst c
  exact placed_valid 0 (0, 0) valid_142

theorem eq_card_565 : card_565 = combine (5, 2) [placed 5 (1, 3) card_140, inline_322, inline_323] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_565 : Valid card_565 := by
  rw [eq_card_565]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 3) valid_140
  rcases hc with rfl | hc
  · exact valid_inline_322
  subst c
  exact valid_inline_323

theorem eq_card_566 : card_566 = combine (3, 5) [placed 1 (0, 2) card_116, placed 5 (0, 6) card_116, placed 1 (0, 2) card_172, placed 5 (0, 6) card_172, placed 0 (1, 1) card_182, placed 3 (6, 1) card_565] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_566 : Valid card_566 := by
  rw [eq_card_566]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_172
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_172
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_182
  subst c
  exact placed_valid 3 (6, 1) valid_565

theorem eq_inline_324 : inline_324 = combine (4, 3) [placed 1 (4, 2) card_5, placed 7 (6, 5) card_92] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_324 : Valid inline_324 := by
  rw [eq_inline_324]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 2) valid_5
  subst c
  exact placed_valid 7 (6, 5) valid_92

theorem eq_inline_325 : inline_325 = combine (4, 2) [placed 2 (3, 5) card_94, placed 2 (3, 6) card_102, inline_324] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_325 : Valid inline_325 := by
  rw [eq_inline_325]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_94
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_102
  subst c
  exact valid_inline_324

theorem eq_inline_326 : inline_326 = combine (4, 4) [placed 6 (7, 5) card_0, inline_325] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_326 : Valid inline_326 := by
  rw [eq_inline_326]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 5) valid_0
  subst c
  exact valid_inline_325

theorem eq_inline_327 : inline_327 = combine (6, 5) [placed 5 (3, 5) card_16, placed 7 (7, 6) card_235, inline_326] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_327 : Valid inline_327 := by
  rw [eq_inline_327]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_235
  subst c
  exact valid_inline_326

theorem eq_inline_328 : inline_328 = combine (5, 5) [placed 5 (1, 6) card_67, placed 2 (2, 7) card_134, placed 2 (2, 7) card_180, placed 6 (6, 9) card_327, placed 1 (1, 2) card_504, placed 2 (3, 7) card_558, inline_327] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_328 : Valid inline_328 := by
  rw [eq_inline_328]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 9) valid_327
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_504
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_558
  subst c
  exact valid_inline_327

theorem eq_card_567 : card_567 = combine (4, 5) [placed 2 (3, 6) card_27, placed 0 (3, 2) card_44, placed 0 (0, 1) card_560, placed 0 (2, 0) card_563, inline_328] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_567 : Valid card_567 := by
  rw [eq_card_567]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_560
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_563
  subst c
  exact valid_inline_328

theorem eq_inline_329 : inline_329 = combine (4, 3) [placed 3 (7, 1) card_255, placed 4 (4, 0) card_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_329 : Valid inline_329 := by
  rw [eq_inline_329]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 1) valid_255
  subst c
  exact placed_valid 4 (4, 0) valid_496

theorem eq_inline_330 : inline_330 = combine (6, 4) [placed 2 (3, 5) card_24, placed 5 (2, 5) card_77] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_330 : Valid inline_330 := by
  rw [eq_inline_330]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_24
  subst c
  exact placed_valid 5 (2, 5) valid_77

theorem eq_inline_331 : inline_331 = combine (3, 7) [placed 0 (3, 3) card_6, placed 3 (5, 3) card_132] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_331 : Valid inline_331 := by
  rw [eq_inline_331]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_6
  subst c
  exact placed_valid 3 (5, 3) valid_132

theorem eq_inline_332 : inline_332 = combine (3, 7) [placed 4 (3, 3) card_6, placed 4 (4, 3) card_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_332 : Valid inline_332 := by
  rw [eq_inline_332]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 3) valid_6
  subst c
  exact placed_valid 4 (4, 3) valid_124

theorem eq_inline_333 : inline_333 = combine (3, 6) [placed 3 (4, 3) card_8, placed 4 (5, 3) card_387, inline_331, inline_332] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_333 : Valid inline_333 := by
  rw [eq_inline_333]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_387
  rcases hc with rfl | hc
  · exact valid_inline_331
  subst c
  exact valid_inline_332

theorem eq_inline_334 : inline_334 = combine (3, 3) [placed 5 (3, 5) card_3, inline_333] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_334 : Valid inline_334 := by
  rw [eq_inline_334]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_3
  subst c
  exact valid_inline_333

theorem eq_inline_335 : inline_335 = combine (3, 5) [placed 3 (6, 4) card_52, inline_330, inline_334] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_335 : Valid inline_335 := by
  rw [eq_inline_335]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_52
  rcases hc with rfl | hc
  · exact valid_inline_330
  subst c
  exact valid_inline_334

theorem eq_inline_336 : inline_336 = combine (5, 4) [placed 1 (2, 1) card_79, placed 5 (1, 5) card_189, placed 5 (0, 7) card_518, inline_335, placed 2 (1, 7) card_565, placed 1 (0, 1) card_567] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_336 : Valid inline_336 := by
  rw [eq_inline_336]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_518
  rcases hc with rfl | hc
  · exact valid_inline_335
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_565
  subst c
  exact placed_valid 1 (0, 1) valid_567

theorem eq_card_568 : card_568 = combine (4, 4) [placed 1 (1, 1) card_110, placed 4 (4, 0) card_497, inline_329, inline_336] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_568 : Valid card_568 := by
  rw [eq_card_568]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_110
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_497
  rcases hc with rfl | hc
  · exact valid_inline_329
  subst c
  exact valid_inline_336

theorem eq_inline_337 : inline_337 = combine (6, 6) [placed 0 (3, 5) card_5, placed 0 (5, 2) card_54] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_337 : Valid inline_337 := by
  rw [eq_inline_337]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_5
  subst c
  exact placed_valid 0 (5, 2) valid_54

theorem eq_inline_338 : inline_338 = combine (5, 3) [placed 1 (0, 2) card_68, inline_337] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_338 : Valid inline_338 := by
  rw [eq_inline_338]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_68
  subst c
  exact valid_inline_337

theorem eq_inline_339 : inline_339 = combine (6, 3) [placed 7 (6, 3) card_169, placed 2 (3, 6) card_202] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_339 : Valid inline_339 := by
  rw [eq_inline_339]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 3) valid_169
  subst c
  exact placed_valid 2 (3, 6) valid_202

theorem eq_inline_340 : inline_340 = combine (6, 5) [placed 0 (3, 4) card_8, inline_338, inline_339] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_340 : Valid inline_340 := by
  rw [eq_inline_340]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_8
  rcases hc with rfl | hc
  · exact valid_inline_338
  subst c
  exact valid_inline_339

theorem eq_inline_341 : inline_341 = combine (5, 3) [placed 1 (0, 2) card_68, placed 0 (3, 0) card_495] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_341 : Valid inline_341 := by
  rw [eq_inline_341]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_68
  subst c
  exact placed_valid 0 (3, 0) valid_495

theorem eq_inline_342 : inline_342 = combine (6, 3) [placed 0 (3, 2) card_99, placed 7 (6, 3) card_169] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_342 : Valid inline_342 := by
  rw [eq_inline_342]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_99
  subst c
  exact placed_valid 7 (6, 3) valid_169

theorem eq_inline_343 : inline_343 = combine (4, 6) [placed 1 (2, 5) card_11, placed 1 (0, 2) card_288] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_343 : Valid inline_343 := by
  rw [eq_inline_343]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_11
  subst c
  exact placed_valid 1 (0, 2) valid_288

theorem eq_inline_344 : inline_344 = combine (6, 5) [placed 5 (2, 6) card_9, inline_342, inline_343] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_344 : Valid inline_344 := by
  rw [eq_inline_344]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_9
  rcases hc with rfl | hc
  · exact valid_inline_342
  subst c
  exact valid_inline_343

theorem eq_card_569 : card_569 = combine (5, 5) [placed 1 (0, 2) card_287, placed 2 (2, 9) card_322, placed 1 (2, 4) card_457, inline_340, inline_341, inline_344] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_569 : Valid card_569 := by
  rw [eq_card_569]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_287
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_457
  rcases hc with rfl | hc
  · exact valid_inline_340
  rcases hc with rfl | hc
  · exact valid_inline_341
  subst c
  exact valid_inline_344

theorem eq_inline_345 : inline_345 = combine (4, 5) [placed 3 (4, 3) card_5, placed 2 (3, 9) card_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_345 : Valid inline_345 := by
  rw [eq_inline_345]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact placed_valid 2 (3, 9) valid_446

theorem eq_inline_346 : inline_346 = combine (5, 3) [placed 5 (2, 4) card_20, placed 1 (2, 3) card_29, placed 0 (2, 0) card_331] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_346 : Valid inline_346 := by
  rw [eq_inline_346]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_29
  subst c
  exact placed_valid 0 (2, 0) valid_331

theorem eq_inline_347 : inline_347 = combine (2, 3) [placed 0 (0, 3) card_1, inline_346] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_347 : Valid inline_347 := by
  rw [eq_inline_347]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_1
  subst c
  exact valid_inline_346

theorem eq_card_570 : card_570 = combine (4, 3) [placed 2 (3, 7) card_150, placed 0 (0, 1) card_283, inline_345, inline_347] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_570 : Valid card_570 := by
  rw [eq_card_570]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_150
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_283
  rcases hc with rfl | hc
  · exact valid_inline_345
  subst c
  exact valid_inline_347

theorem eq_inline_348 : inline_348 = combine (5, 6) [placed 1 (0, 3) card_287, placed 1 (0, 3) card_288, placed 0 (2, 4) card_345, placed 1 (2, 5) card_457] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_348 : Valid inline_348 := by
  rw [eq_inline_348]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_287
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_288
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_345
  subst c
  exact placed_valid 1 (2, 5) valid_457

theorem eq_inline_349 : inline_349 = combine (4, 7) [placed 7 (4, 7) card_2, inline_348] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_349 : Valid inline_349 := by
  rw [eq_inline_349]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_2
  subst c
  exact valid_inline_348

theorem eq_inline_350 : inline_350 = combine (4, 3) [placed 3 (4, 3) card_5, placed 2 (3, 9) card_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_350 : Valid inline_350 := by
  rw [eq_inline_350]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact placed_valid 2 (3, 9) valid_446

theorem eq_inline_351 : inline_351 = combine (4, 5) [placed 7 (4, 7) card_0, inline_350] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_351 : Valid inline_351 := by
  rw [eq_inline_351]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_0
  subst c
  exact valid_inline_350

theorem eq_inline_352 : inline_352 = combine (4, 3) [placed 3 (4, 3) card_5, placed 0 (0, 1) card_283] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_352 : Valid inline_352 := by
  rw [eq_inline_352]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_283

theorem eq_inline_353 : inline_353 = combine (4, 5) [placed 7 (4, 7) card_0, inline_352] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_353 : Valid inline_353 := by
  rw [eq_inline_353]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_0
  subst c
  exact valid_inline_352

theorem eq_inline_354 : inline_354 = combine (5, 3) [placed 5 (4, 6) card_5, placed 1 (2, 3) card_29] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_354 : Valid inline_354 := by
  rw [eq_inline_354]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_5
  subst c
  exact placed_valid 1 (2, 3) valid_29

theorem eq_inline_355 : inline_355 = combine (4, 3) [placed 2 (4, 7) card_7, inline_354, placed 2 (3, 9) card_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_355 : Valid inline_355 := by
  rw [eq_inline_355]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_7
  rcases hc with rfl | hc
  · exact valid_inline_354
  subst c
  exact placed_valid 2 (3, 9) valid_446

theorem eq_inline_356 : inline_356 = combine (4, 5) [placed 7 (4, 7) card_0, inline_355] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_356 : Valid inline_356 := by
  rw [eq_inline_356]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_0
  subst c
  exact valid_inline_355

theorem eq_inline_357 : inline_357 = combine (2, 3) [placed 0 (0, 3) card_1, inline_356] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_357 : Valid inline_357 := by
  rw [eq_inline_357]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_1
  subst c
  exact valid_inline_356

theorem eq_card_571 : card_571 = combine (4, 4) [placed 2 (3, 7) card_250, placed 0 (0, 1) card_569, inline_349, inline_351, inline_353, placed 0 (0, 0) card_570, inline_357] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_571 : Valid card_571 := by
  rw [eq_card_571]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_250
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_569
  rcases hc with rfl | hc
  · exact valid_inline_349
  rcases hc with rfl | hc
  · exact valid_inline_351
  rcases hc with rfl | hc
  · exact valid_inline_353
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_570
  subst c
  exact valid_inline_357

theorem eq_inline_358 : inline_358 = combine (2, 6) [placed 4 (4, 6) card_5, placed 2 (1, 7) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_358 : Valid inline_358 := by
  rw [eq_inline_358]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 6) valid_5
  subst c
  exact placed_valid 2 (1, 7) valid_78

theorem eq_card_572 : card_572 = combine (4, 6) [placed 5 (0, 7) card_97, placed 1 (0, 6) card_98, inline_358, placed 0 (0, 0) card_571] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_572 : Valid card_572 := by
  rw [eq_card_572]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_97
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 6) valid_98
  rcases hc with rfl | hc
  · exact valid_inline_358
  subst c
  exact placed_valid 0 (0, 0) valid_571

theorem eq_inline_359 : inline_359 = combine (3, 5) [placed 1 (2, 3) card_8, placed 1 (0, 3) card_115, placed 3 (4, 3) card_197, placed 0 (0, 2) card_286, placed 0 (0, 2) card_339] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_359 : Valid inline_359 := by
  rw [eq_inline_359]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_286
  subst c
  exact placed_valid 0 (0, 2) valid_339

theorem eq_inline_360 : inline_360 = combine (3, 5) [placed 0 (3, 2) card_7, placed 1 (2, 3) card_8, placed 4 (4, 2) card_9, placed 5 (1, 7) card_473] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_360 : Valid inline_360 := by
  rw [eq_inline_360]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_9
  subst c
  exact placed_valid 5 (1, 7) valid_473

theorem eq_inline_361 : inline_361 = combine (3, 5) [placed 1 (2, 3) card_8, placed 0 (0, 2) card_403, placed 0 (0, 3) card_487, placed 0 (0, 2) card_492] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_361 : Valid inline_361 := by
  rw [eq_inline_361]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_403
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_487
  subst c
  exact placed_valid 0 (0, 2) valid_492

theorem eq_inline_362 : inline_362 = combine (3, 5) [placed 0 (0, 2) card_87, placed 0 (0, 3) card_487] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_362 : Valid inline_362 := by
  rw [eq_inline_362]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_87
  subst c
  exact placed_valid 0 (0, 3) valid_487

theorem eq_inline_363 : inline_363 = combine (1, 7) [placed 0 (0, 3) card_107, placed 0 (0, 0) card_572] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_363 : Valid inline_363 := by
  rw [eq_inline_363]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_107
  subst c
  exact placed_valid 0 (0, 0) valid_572

theorem eq_inline_364 : inline_364 = combine (3, 5) [placed 4 (4, 2) card_9, placed 0 (0, 2) card_249, placed 7 (5, 6) card_383, placed 0 (0, 2) card_403] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_364 : Valid inline_364 := by
  rw [eq_inline_364]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_249
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_383
  subst c
  exact placed_valid 0 (0, 2) valid_403

theorem eq_card_573 : card_573 = combine (3, 6) [placed 0 (0, 2) card_384, placed 0 (0, 2) card_385, placed 0 (0, 2) card_493, placed 0 (0, 2) card_494, inline_359, inline_360, inline_361, inline_362, inline_363, inline_364] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_573 : Valid card_573 := by
  rw [eq_card_573]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_384
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_385
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_493
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_494
  rcases hc with rfl | hc
  · exact valid_inline_359
  rcases hc with rfl | hc
  · exact valid_inline_360
  rcases hc with rfl | hc
  · exact valid_inline_361
  rcases hc with rfl | hc
  · exact valid_inline_362
  rcases hc with rfl | hc
  · exact valid_inline_363
  subst c
  exact valid_inline_364

theorem eq_inline_365 : inline_365 = combine (3, 3) [placed 1 (1, 2) card_43, placed 6 (4, 6) card_64] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_365 : Valid inline_365 := by
  rw [eq_inline_365]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_43
  subst c
  exact placed_valid 6 (4, 6) valid_64

theorem eq_inline_366 : inline_366 = combine (4, 4) [placed 7 (4, 5) card_5, placed 0 (1, 1) card_223] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_366 : Valid inline_366 := by
  rw [eq_inline_366]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_5
  subst c
  exact placed_valid 0 (1, 1) valid_223

theorem eq_inline_367 : inline_367 = combine (4, 2) [placed 0 (1, 2) card_5, inline_366] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_367 : Valid inline_367 := by
  rw [eq_inline_367]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_5
  subst c
  exact valid_inline_366

theorem eq_inline_368 : inline_368 = combine (4, 2) [placed 7 (4, 5) card_5, placed 6 (5, 6) card_236] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_368 : Valid inline_368 := by
  rw [eq_inline_368]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_5
  subst c
  exact placed_valid 6 (5, 6) valid_236

theorem eq_inline_369 : inline_369 = combine (4, 4) [placed 0 (3, 2) card_18, placed 6 (4, 6) card_61, inline_368] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_369 : Valid inline_369 := by
  rw [eq_inline_369]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_18
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_61
  subst c
  exact valid_inline_368

theorem eq_inline_370 : inline_370 = combine (3, 2) [placed 1 (1, 2) card_130, inline_365, inline_367, inline_369] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_370 : Valid inline_370 := by
  rw [eq_inline_370]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_130
  rcases hc with rfl | hc
  · exact valid_inline_365
  rcases hc with rfl | hc
  · exact valid_inline_367
  subst c
  exact valid_inline_369

theorem eq_card_574 : card_574 = combine (4, 5) [placed 4 (5, 2) card_184, placed 1 (0, 2) card_384, placed 1 (0, 2) card_385, placed 1 (0, 2) card_493, placed 1 (0, 2) card_494, inline_370] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_574 : Valid card_574 := by
  rw [eq_card_574]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_184
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_384
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_385
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_493
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_494
  subst c
  exact valid_inline_370

theorem eq_inline_371 : inline_371 = combine (2, 4) [placed 6 (4, 4) card_3, placed 0 (2, 3) card_8] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_371 : Valid inline_371 := by
  rw [eq_inline_371]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_3
  subst c
  exact placed_valid 0 (2, 3) valid_8

theorem eq_inline_372 : inline_372 = combine (2, 4) [placed 6 (4, 4) card_3, placed 5 (2, 4) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_372 : Valid inline_372 := by
  rw [eq_inline_372]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_3
  subst c
  exact placed_valid 5 (2, 4) valid_6

theorem eq_inline_373 : inline_373 = combine (6, 4) [inline_372, placed 3 (7, 4) card_554] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_373 : Valid inline_373 := by
  rw [eq_inline_373]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_372
  subst c
  exact placed_valid 3 (7, 4) valid_554

theorem eq_inline_374 : inline_374 = combine (6, 4) [placed 1 (0, 3) card_280, placed 3 (7, 4) card_554] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_374 : Valid inline_374 := by
  rw [eq_inline_374]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_280
  subst c
  exact placed_valid 3 (7, 4) valid_554

theorem eq_card_575 : card_575 = combine (5, 4) [placed 0 (2, 1) card_257, placed 0 (0, 0) card_326, inline_371, inline_373, inline_374] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_575 : Valid card_575 := by
  rw [eq_card_575]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_326
  rcases hc with rfl | hc
  · exact valid_inline_371
  rcases hc with rfl | hc
  · exact valid_inline_373
  subst c
  exact valid_inline_374


end OAI.Snaky21.Certificate

theorem solution : Valid card_560 ∧ Valid card_561 ∧ Valid card_562 ∧ Valid card_563 ∧ Valid card_564 ∧ Valid card_565 ∧ Valid card_566 ∧ Valid card_567 ∧ Valid card_568 ∧ Valid card_569 ∧ Valid card_570 ∧ Valid card_571 ∧ Valid card_572 ∧ Valid card_573 ∧ Valid card_574 ∧ Valid card_575 ∧ True :=
  ⟨valid_560, valid_561, valid_562, valid_563, valid_564, valid_565, valid_566, valid_567, valid_568, valid_569, valid_570, valid_571, valid_572, valid_573, valid_574, valid_575, True.intro⟩
