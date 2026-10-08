-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T08:32:52.927921+00:00
-- url     : https://prove2.me/submissions/ad19a87a-6a46-4adb-89b2-80dab63d14d8

import Definitions.Def_Snaky21Data02
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl
end OAI.Snaky21.Certificate
namespace OAI.Snaky21.Certificate
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
end OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_128 : card_128 = combine (1, 5) [placed 2 (0, 6) card_9, placed 4 (1, 2) card_16, placed 0 (0, 1) card_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_128 : Valid card_128 := by
  rw [eq_card_128]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 2) valid_16
  subst c
  exact placed_valid 0 (0, 1) valid_124

theorem eq_card_129 : card_129 = combine (1, 2) [placed 7 (1, 5) card_0, placed 7 (1, 4) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_129 : Valid card_129 := by
  rw [eq_card_129]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 7 (1, 4) valid_3

theorem eq_card_130 : card_130 = combine (1, 4) [placed 1 (0, 0) card_3, placed 0 (0, 0) card_129] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_130 : Valid card_130 := by
  rw [eq_card_130]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_3
  subst c
  exact placed_valid 0 (0, 0) valid_129

theorem eq_card_131 : card_131 = combine (1, 3) [placed 4 (4, 2) card_0, placed 0 (0, 0) card_15] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_131 : Valid card_131 := by
  rw [eq_card_131]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_15

theorem eq_card_132 : card_132 = combine (1, 3) [placed 4 (4, 2) card_5, placed 0 (1, 0) card_131] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_132 : Valid card_132 := by
  rw [eq_card_132]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_131

theorem eq_card_133 : card_133 = combine (1, 1) [placed 6 (4, 2) card_5, placed 0 (0, 0) card_132] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_133 : Valid card_133 := by
  rw [eq_card_133]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_132

theorem eq_card_134 : card_134 = combine (4, 2) [placed 1 (1, 2) card_16, placed 2 (1, 3) card_24, placed 4 (5, 0) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_134 : Valid card_134 := by
  rw [eq_card_134]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 3) valid_24
  subst c
  exact placed_valid 4 (5, 0) valid_133

theorem eq_card_135 : card_135 = combine (2, 5) [placed 0 (2, 1) card_7, placed 6 (3, 6) card_9, placed 1 (0, 1) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_135 : Valid card_135 := by
  rw [eq_card_135]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_9
  subst c
  exact placed_valid 1 (0, 1) valid_133

theorem eq_card_136 : card_136 = combine (2, 4) [placed 4 (2, 1) card_21, placed 0 (1, 1) card_37, placed 5 (0, 5) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_136 : Valid card_136 := by
  rw [eq_card_136]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_37
  subst c
  exact placed_valid 5 (0, 5) valid_133

theorem eq_card_137 : card_137 = combine (4, 2) [placed 1 (0, 2) card_7, placed 5 (0, 3) card_9, placed 4 (5, 0) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_137 : Valid card_137 := by
  rw [eq_card_137]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_9
  subst c
  exact placed_valid 4 (5, 0) valid_133

theorem eq_card_138 : card_138 = combine (1, 4) [placed 1 (0, 0) card_3, placed 7 (1, 4) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_138 : Valid card_138 := by
  rw [eq_card_138]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_3
  subst c
  exact placed_valid 7 (1, 4) valid_3

theorem eq_card_139 : card_139 = combine (1, 3) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_138] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_139 : Valid card_139 := by
  rw [eq_card_139]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_138

theorem eq_card_140 : card_140 = combine (1, 3) [placed 1 (0, 0) card_0, placed 0 (0, 1) card_43] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_140 : Valid card_140 := by
  rw [eq_card_140]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_43

theorem eq_card_141 : card_141 = combine (1, 4) [placed 0 (0, 0) card_53, placed 6 (1, 6) card_53, placed 1 (0, 2) card_76] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_141 : Valid card_141 := by
  rw [eq_card_141]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_53
  subst c
  exact placed_valid 1 (0, 2) valid_76

theorem eq_card_142 : card_142 = combine (1, 2) [placed 6 (4, 3) card_5, placed 0 (1, 0) card_141] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_142 : Valid card_142 := by
  rw [eq_card_142]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_141

theorem eq_card_143 : card_143 = combine (4, 1) [placed 1 (0, 1) card_6, placed 5 (0, 1) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_143 : Valid card_143 := by
  rw [eq_card_143]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_6
  subst c
  exact placed_valid 5 (0, 1) valid_11

theorem eq_card_144 : card_144 = combine (3, 2) [placed 0 (0, 0) card_46, placed 5 (0, 2) card_103, placed 0 (0, 1) card_143] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_144 : Valid card_144 := by
  rw [eq_card_144]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_46
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_103
  subst c
  exact placed_valid 0 (0, 1) valid_143

theorem eq_card_145 : card_145 = combine (3, 2) [placed 0 (0, 1) card_5, placed 0 (2, 0) card_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_145 : Valid card_145 := by
  rw [eq_card_145]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_10

theorem eq_card_146 : card_146 = combine (2, 1) [placed 0 (0, 1) card_5, placed 5 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_146 : Valid card_146 := by
  rw [eq_card_146]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 5 (1, 4) valid_5

theorem eq_card_147 : card_147 = combine (3, 2) [placed 0 (0, 1) card_5, placed 0 (2, 0) card_39] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_147 : Valid card_147 := by
  rw [eq_card_147]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_39

theorem eq_card_148 : card_148 = combine (1, 4) [placed 7 (1, 4) card_4, placed 0 (1, 1) card_21] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_148 : Valid card_148 := by
  rw [eq_card_148]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 0 (1, 1) valid_21

theorem eq_card_149 : card_149 = combine (1, 3) [placed 7 (1, 4) card_5, placed 0 (0, 0) card_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_149 : Valid card_149 := by
  rw [eq_card_149]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_124

theorem eq_card_150 : card_150 = combine (1, 2) [placed 7 (1, 4) card_5, placed 0 (1, 0) card_7] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_150 : Valid card_150 := by
  rw [eq_card_150]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_7

theorem eq_card_151 : card_151 = combine (4, 2) [placed 0 (3, 1) card_21, placed 7 (4, 4) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_151 : Valid card_151 := by
  rw [eq_card_151]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_21
  subst c
  exact placed_valid 7 (4, 4) valid_35

theorem eq_card_152 : card_152 = combine (2, 3) [placed 2 (1, 3) card_5, placed 4 (4, 0) card_99] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_152 : Valid card_152 := by
  rw [eq_card_152]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 3) valid_5
  subst c
  exact placed_valid 4 (4, 0) valid_99

theorem eq_card_153 : card_153 = combine (1, 4) [placed 7 (1, 4) card_4, placed 4 (4, 3) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_153 : Valid card_153 := by
  rw [eq_card_153]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 4 (4, 3) valid_5

theorem eq_card_154 : card_154 = combine (1, 3) [placed 7 (1, 5) card_0, placed 7 (1, 4) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_154 : Valid card_154 := by
  rw [eq_card_154]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 7 (1, 4) valid_3

theorem eq_card_155 : card_155 = combine (4, 2) [placed 5 (0, 2) card_7, placed 1 (0, 1) card_9, placed 0 (1, 0) card_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_155 : Valid card_155 := by
  rw [eq_card_155]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_46

theorem eq_card_156 : card_156 = combine (3, 1) [placed 5 (2, 4) card_2, placed 2 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_156 : Valid card_156 := by
  rw [eq_card_156]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_2
  subst c
  exact placed_valid 2 (0, 1) valid_5

theorem eq_card_157 : card_157 = combine (4, 0) [placed 2 (0, 1) card_4, placed 0 (1, 0) card_156] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_157 : Valid card_157 := by
  rw [eq_card_157]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact placed_valid 0 (1, 0) valid_156

theorem eq_card_158 : card_158 = combine (0, 4) [placed 0 (0, 1) card_6, placed 2 (0, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_158 : Valid card_158 := by
  rw [eq_card_158]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_6
  subst c
  exact placed_valid 2 (0, 5) valid_6

theorem eq_card_159 : card_159 = combine (3, 1) [placed 1 (0, 1) card_23, placed 0 (1, 0) card_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_159 : Valid card_159 := by
  rw [eq_card_159]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_23
  subst c
  exact placed_valid 0 (1, 0) valid_66

theorem eq_card_160 : card_160 = combine (1, 2) [placed 7 (1, 4) card_5, placed 2 (1, 5) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_160 : Valid card_160 := by
  rw [eq_card_160]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 2 (1, 5) valid_11

theorem eq_card_161 : card_161 = combine (4, 3) [placed 1 (0, 3) card_6, placed 0 (0, 0) card_142] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_161 : Valid card_161 := by
  rw [eq_card_161]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_6
  subst c
  exact placed_valid 0 (0, 0) valid_142

theorem eq_card_162 : card_162 = combine (4, 3) [placed 5 (0, 3) card_6, placed 0 (0, 0) card_142] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_162 : Valid card_162 := by
  rw [eq_card_162]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_6
  subst c
  exact placed_valid 0 (0, 0) valid_142

theorem eq_card_163 : card_163 = combine (0, 2) [placed 1 (0, 0) card_3, placed 0 (0, 0) card_129] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_163 : Valid card_163 := by
  rw [eq_card_163]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_3
  subst c
  exact placed_valid 0 (0, 0) valid_129

theorem eq_card_164 : card_164 = combine (3, 3) [placed 6 (4, 3) card_0, placed 0 (0, 0) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_164 : Valid card_164 := by
  rw [eq_card_164]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_55

theorem eq_card_165 : card_165 = combine (4, 3) [placed 0 (3, 0) card_44, placed 1 (0, 2) card_64] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_165 : Valid card_165 := by
  rw [eq_card_165]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_44
  subst c
  exact placed_valid 1 (0, 2) valid_64

theorem eq_card_166 : card_166 = combine (3, 3) [placed 4 (4, 0) card_14, placed 3 (4, 2) card_28, placed 0 (0, 1) card_58, placed 0 (0, 1) card_100] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_166 : Valid card_166 := by
  rw [eq_card_166]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_58
  subst c
  exact placed_valid 0 (0, 1) valid_100

theorem eq_card_167 : card_167 = combine (3, 2) [placed 0 (0, 1) card_5, placed 5 (0, 5) card_152] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_167 : Valid card_167 := by
  rw [eq_card_167]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 5 (0, 5) valid_152

theorem eq_card_168 : card_168 = combine (2, 2) [placed 6 (4, 2) card_5, placed 0 (1, 0) card_131] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_168 : Valid card_168 := by
  rw [eq_card_168]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_131

theorem eq_card_169 : card_169 = combine (1, 4) [placed 1 (0, 0) card_1, placed 7 (1, 6) card_1] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_169 : Valid card_169 := by
  rw [eq_card_169]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_1
  subst c
  exact placed_valid 7 (1, 6) valid_1

theorem eq_card_170 : card_170 = combine (1, 2) [placed 4 (4, 2) card_2, placed 7 (1, 4) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_170 : Valid card_170 := by
  rw [eq_card_170]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_2
  subst c
  exact placed_valid 7 (1, 4) valid_3

theorem eq_card_171 : card_171 = combine (4, 3) [placed 5 (0, 3) card_6, placed 2 (1, 4) card_26, placed 0 (1, 0) card_116] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_171 : Valid card_171 := by
  rw [eq_card_171]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 4) valid_26
  subst c
  exact placed_valid 0 (1, 0) valid_116

theorem eq_card_172 : card_172 = combine (4, 3) [placed 0 (0, 0) card_142, placed 6 (5, 6) card_142] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_172 : Valid card_172 := by
  rw [eq_card_172]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_142
  subst c
  exact placed_valid 6 (5, 6) valid_142

theorem eq_card_173 : card_173 = combine (4, 3) [placed 0 (0, 0) card_142, placed 4 (5, 0) card_142] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_173 : Valid card_173 := by
  rw [eq_card_173]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_142
  subst c
  exact placed_valid 4 (5, 0) valid_142

theorem eq_card_174 : card_174 = combine (3, 5) [placed 1 (0, 2) card_116, placed 5 (0, 6) card_117, placed 0 (1, 1) card_135, placed 6 (5, 7) card_135, placed 5 (0, 6) card_173, placed 3 (6, 2) card_173] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_174 : Valid card_174 := by
  rw [eq_card_174]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_117
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_173
  subst c
  exact placed_valid 3 (6, 2) valid_173

theorem eq_card_175 : card_175 = combine (1, 5) [placed 4 (1, 1) card_7, placed 1 (0, 2) card_32, placed 2 (0, 6) card_60] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_175 : Valid card_175 := by
  rw [eq_card_175]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_32
  subst c
  exact placed_valid 2 (0, 6) valid_60

theorem eq_card_176 : card_176 = combine (2, 2) [placed 4 (4, 2) card_0, placed 4 (4, 0) card_60] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_176 : Valid card_176 := by
  rw [eq_card_176]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_0
  subst c
  exact placed_valid 4 (4, 0) valid_60

theorem eq_card_177 : card_177 = combine (1, 1) [placed 6 (4, 2) card_0, placed 0 (0, 0) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_177 : Valid card_177 := by
  rw [eq_card_177]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_23

theorem eq_card_178 : card_178 = combine (1, 1) [placed 6 (4, 2) card_5, placed 0 (1, 0) card_177] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_178 : Valid card_178 := by
  rw [eq_card_178]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_177

theorem eq_card_179 : card_179 = combine (1, 3) [placed 4 (4, 2) card_5, placed 0 (0, 0) card_178] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_179 : Valid card_179 := by
  rw [eq_card_179]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_178

theorem eq_card_180 : card_180 = combine (4, 2) [placed 1 (1, 2) card_16, placed 2 (1, 3) card_24, placed 4 (5, 0) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_180 : Valid card_180 := by
  rw [eq_card_180]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 3) valid_24
  subst c
  exact placed_valid 4 (5, 0) valid_179

theorem eq_card_181 : card_181 = combine (4, 2) [placed 1 (0, 2) card_7, placed 5 (0, 3) card_9, placed 4 (5, 0) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_181 : Valid card_181 := by
  rw [eq_card_181]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_9
  subst c
  exact placed_valid 4 (5, 0) valid_179

theorem eq_card_182 : card_182 = combine (2, 5) [placed 2 (2, 6) card_7, placed 0 (1, 1) card_9, placed 1 (0, 1) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_182 : Valid card_182 := by
  rw [eq_card_182]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_9
  subst c
  exact placed_valid 1 (0, 1) valid_179

theorem eq_card_183 : card_183 = combine (4, 2) [placed 0 (1, 2) card_5, placed 4 (5, 0) card_178] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_183 : Valid card_183 := by
  rw [eq_card_183]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_5
  subst c
  exact placed_valid 4 (5, 0) valid_178

theorem eq_card_184 : card_184 = combine (2, 3) [placed 4 (4, 0) card_99, placed 6 (5, 5) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_184 : Valid card_184 := by
  rw [eq_card_184]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_99
  subst c
  exact placed_valid 6 (5, 5) valid_179

theorem eq_card_185 : card_185 = combine (1, 4) [placed 1 (0, 1) card_5, placed 0 (0, 0) card_113] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_185 : Valid card_185 := by
  rw [eq_card_185]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_113

theorem eq_card_186 : card_186 = combine (1, 1) [placed 6 (1, 5) card_6, placed 0 (1, 0) card_185] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_186 : Valid card_186 := by
  rw [eq_card_186]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 5) valid_6
  subst c
  exact placed_valid 0 (1, 0) valid_185

theorem eq_card_187 : card_187 = combine (0, 6) [placed 0 (0, 2) card_6, placed 0 (0, 2) card_7, placed 2 (0, 7) card_185] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_187 : Valid card_187 := by
  rw [eq_card_187]
  apply combination_rule (0, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_7
  subst c
  exact placed_valid 2 (0, 7) valid_185

theorem eq_card_188 : card_188 = combine (2, 5) [placed 1 (1, 2) card_8, placed 3 (3, 2) card_26, placed 5 (0, 6) card_133, placed 2 (1, 7) card_186, placed 0 (2, 0) card_187] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_188 : Valid card_188 := by
  rw [eq_card_188]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 2) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_133
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_186
  subst c
  exact placed_valid 0 (2, 0) valid_187

theorem eq_card_189 : card_189 = combine (1, 5) [placed 1 (0, 2) card_8, placed 1 (0, 2) card_26, placed 2 (0, 6) card_62, placed 6 (2, 7) card_186, placed 4 (1, 0) card_187] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_189 : Valid card_189 := by
  rw [eq_card_189]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_62
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 7) valid_186
  subst c
  exact placed_valid 4 (1, 0) valid_187

theorem eq_card_190 : card_190 = combine (2, 5) [placed 1 (1, 2) card_8, placed 1 (1, 2) card_26, placed 5 (0, 6) card_179, placed 6 (3, 7) card_186, placed 4 (2, 0) card_187] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_190 : Valid card_190 := by
  rw [eq_card_190]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_179
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_186
  subst c
  exact placed_valid 4 (2, 0) valid_187

theorem eq_card_191 : card_191 = combine (0, 1) [placed 7 (1, 4) card_5, placed 0 (0, 1) card_89] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_191 : Valid card_191 := by
  rw [eq_card_191]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_89

theorem block02_valid : Valid card_128 ∧ Valid card_129 ∧ Valid card_130 ∧ Valid card_131 ∧ Valid card_132 ∧ Valid card_133 ∧ Valid card_134 ∧ Valid card_135 ∧ Valid card_136 ∧ Valid card_137 ∧ Valid card_138 ∧ Valid card_139 ∧ Valid card_140 ∧ Valid card_141 ∧ Valid card_142 ∧ Valid card_143 ∧ Valid card_144 ∧ Valid card_145 ∧ Valid card_146 ∧ Valid card_147 ∧ Valid card_148 ∧ Valid card_149 ∧ Valid card_150 ∧ Valid card_151 ∧ Valid card_152 ∧ Valid card_153 ∧ Valid card_154 ∧ Valid card_155 ∧ Valid card_156 ∧ Valid card_157 ∧ Valid card_158 ∧ Valid card_159 ∧ Valid card_160 ∧ Valid card_161 ∧ Valid card_162 ∧ Valid card_163 ∧ Valid card_164 ∧ Valid card_165 ∧ Valid card_166 ∧ Valid card_167 ∧ Valid card_168 ∧ Valid card_169 ∧ Valid card_170 ∧ Valid card_171 ∧ Valid card_172 ∧ Valid card_173 ∧ Valid card_174 ∧ Valid card_175 ∧ Valid card_176 ∧ Valid card_177 ∧ Valid card_178 ∧ Valid card_179 ∧ Valid card_180 ∧ Valid card_181 ∧ Valid card_182 ∧ Valid card_183 ∧ Valid card_184 ∧ Valid card_185 ∧ Valid card_186 ∧ Valid card_187 ∧ Valid card_188 ∧ Valid card_189 ∧ Valid card_190 ∧ Valid card_191 ∧ True :=
  ⟨valid_128, valid_129, valid_130, valid_131, valid_132, valid_133, valid_134, valid_135, valid_136, valid_137, valid_138, valid_139, valid_140, valid_141, valid_142, valid_143, valid_144, valid_145, valid_146, valid_147, valid_148, valid_149, valid_150, valid_151, valid_152, valid_153, valid_154, valid_155, valid_156, valid_157, valid_158, valid_159, valid_160, valid_161, valid_162, valid_163, valid_164, valid_165, valid_166, valid_167, valid_168, valid_169, valid_170, valid_171, valid_172, valid_173, valid_174, valid_175, valid_176, valid_177, valid_178, valid_179, valid_180, valid_181, valid_182, valid_183, valid_184, valid_185, valid_186, valid_187, valid_188, valid_189, valid_190, valid_191, True.intro⟩

end OAI.Snaky21.Certificate

theorem solution : Valid card_128 ∧ Valid card_129 ∧ Valid card_130 ∧ Valid card_131 ∧ Valid card_132 ∧ Valid card_133 ∧ Valid card_134 ∧ Valid card_135 ∧ Valid card_136 ∧ Valid card_137 ∧ Valid card_138 ∧ Valid card_139 ∧ Valid card_140 ∧ Valid card_141 ∧ Valid card_142 ∧ Valid card_143 ∧ Valid card_144 ∧ Valid card_145 ∧ Valid card_146 ∧ Valid card_147 ∧ Valid card_148 ∧ Valid card_149 ∧ Valid card_150 ∧ Valid card_151 ∧ Valid card_152 ∧ Valid card_153 ∧ Valid card_154 ∧ Valid card_155 ∧ Valid card_156 ∧ Valid card_157 ∧ Valid card_158 ∧ Valid card_159 ∧ Valid card_160 ∧ Valid card_161 ∧ Valid card_162 ∧ Valid card_163 ∧ Valid card_164 ∧ Valid card_165 ∧ Valid card_166 ∧ Valid card_167 ∧ Valid card_168 ∧ Valid card_169 ∧ Valid card_170 ∧ Valid card_171 ∧ Valid card_172 ∧ Valid card_173 ∧ Valid card_174 ∧ Valid card_175 ∧ Valid card_176 ∧ Valid card_177 ∧ Valid card_178 ∧ Valid card_179 ∧ Valid card_180 ∧ Valid card_181 ∧ Valid card_182 ∧ Valid card_183 ∧ Valid card_184 ∧ Valid card_185 ∧ Valid card_186 ∧ Valid card_187 ∧ Valid card_188 ∧ Valid card_189 ∧ Valid card_190 ∧ Valid card_191 ∧ True := block02_valid
