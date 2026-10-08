-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block07_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T10:59:35.989409+00:00
-- url     : https://prove2.me/submissions/ca9b9330-f794-43d5-b58e-63b5678da405

import Definitions.Def_Snaky21Data07
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
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
end OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_448 : card_448 = combine (1, 3) [placed 6 (4, 6) card_56, placed 1 (0, 2) card_447] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_448 : Valid card_448 := by
  rw [eq_card_448]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_56
  subst c
  exact placed_valid 1 (0, 2) valid_447

theorem eq_card_449 : card_449 = combine (4, 3) [placed 5 (1, 4) card_10, placed 1 (1, 3) card_27, placed 5 (1, 4) card_48, placed 5 (1, 4) card_63, placed 0 (0, 0) card_448] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_449 : Valid card_449 := by
  rw [eq_card_449]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_48
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_63
  subst c
  exact placed_valid 0 (0, 0) valid_448

theorem eq_card_450 : card_450 = combine (3, 4) [placed 6 (5, 4) card_0, placed 2 (0, 7) card_448] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_450 : Valid card_450 := by
  rw [eq_card_450]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact placed_valid 2 (0, 7) valid_448

theorem eq_inline_93 : inline_93 = combine (2, 3) [placed 6 (4, 3) card_0, placed 0 (0, 0) card_402] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_93 : Valid inline_93 := by
  rw [eq_inline_93]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_402

theorem eq_card_451 : card_451 = combine (1, 4) [placed 4 (1, 0) card_11, inline_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_451 : Valid card_451 := by
  rw [eq_card_451]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_11
  subst c
  exact valid_inline_93

theorem eq_inline_94 : inline_94 = combine (6, 4) [placed 6 (6, 4) card_5, placed 0 (3, 1) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_94 : Valid inline_94 := by
  rw [eq_inline_94]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 4) valid_5
  subst c
  exact placed_valid 0 (3, 1) valid_55

theorem eq_card_452 : card_452 = combine (4, 4) [placed 7 (6, 4) card_52, placed 0 (2, 0) card_317, inline_94] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_452 : Valid card_452 := by
  rw [eq_card_452]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_317
  subst c
  exact valid_inline_94

theorem eq_inline_95 : inline_95 = combine (3, 3) [placed 4 (3, 0) card_21, placed 0 (2, 0) card_37, placed 3 (4, 0) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_95 : Valid inline_95 := by
  rw [eq_inline_95]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_37
  subst c
  exact placed_valid 3 (4, 0) valid_354

theorem eq_inline_96 : inline_96 = combine (3, 0) [placed 2 (0, 1) card_5, inline_95] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_96 : Valid inline_96 := by
  rw [eq_inline_96]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_95

theorem eq_card_453 : card_453 = combine (3, 2) [placed 0 (0, 1) card_5, inline_96] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_453 : Valid card_453 := by
  rw [eq_card_453]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_96

theorem eq_card_454 : card_454 = combine (1, 3) [placed 1 (1, 1) card_5, placed 5 (0, 4) card_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_454 : Valid card_454 := by
  rw [eq_card_454]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_453

theorem eq_card_455 : card_455 = combine (1, 1) [placed 0 (0, 0) card_8, placed 1 (0, 1) card_16, placed 2 (0, 2) card_24, placed 0 (0, 0) card_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_455 : Valid card_455 := by
  rw [eq_card_455]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_24
  subst c
  exact placed_valid 0 (0, 0) valid_453

theorem eq_card_456 : card_456 = combine (2, 4) [placed 1 (1, 1) card_5, placed 5 (0, 4) card_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_456 : Valid card_456 := by
  rw [eq_card_456]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_453

theorem eq_card_457 : card_457 = combine (1, 4) [placed 0 (1, 0) card_7, placed 1 (0, 1) card_8, placed 4 (2, 0) card_9, placed 2 (0, 5) card_456] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_457 : Valid card_457 := by
  rw [eq_card_457]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_9
  subst c
  exact placed_valid 2 (0, 5) valid_456

theorem eq_card_458 : card_458 = combine (1, 4) [placed 0 (1, 0) card_7, placed 0 (0, 0) card_9, placed 0 (0, 0) card_62, placed 0 (0, 0) card_456] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_458 : Valid card_458 := by
  rw [eq_card_458]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_62
  subst c
  exact placed_valid 0 (0, 0) valid_456

theorem eq_card_459 : card_459 = combine (1, 6) [placed 4 (2, 2) card_12, placed 4 (2, 2) card_13, placed 6 (2, 8) card_33, placed 4 (2, 2) card_189, placed 2 (0, 8) card_192, placed 4 (2, 1) card_369, placed 0 (0, 3) card_457, placed 2 (0, 7) card_458] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_459 : Valid card_459 := by
  rw [eq_card_459]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 8) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_457
  subst c
  exact placed_valid 2 (0, 7) valid_458

theorem eq_card_460 : card_460 = combine (1, 4) [placed 0 (0, 1) card_13, placed 4 (2, 1) card_14, placed 0 (0, 1) card_33, placed 2 (0, 6) card_457, placed 0 (0, 2) card_458] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_460 : Valid card_460 := by
  rw [eq_card_460]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_457
  subst c
  exact placed_valid 0 (0, 2) valid_458

theorem eq_card_461 : card_461 = combine (3, 3) [placed 3 (4, 1) card_28, placed 0 (0, 0) card_100, placed 0 (0, 0) card_429, placed 0 (2, 0) card_457] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_461 : Valid card_461 := by
  rw [eq_card_461]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 1) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_100
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_429
  subst c
  exact placed_valid 0 (2, 0) valid_457

theorem eq_card_462 : card_462 = combine (1, 5) [placed 4 (2, 1) card_13, placed 6 (2, 7) card_14, placed 2 (0, 7) card_31, placed 4 (2, 1) card_189, placed 2 (0, 7) card_367, placed 2 (0, 6) card_428, placed 0 (0, 2) card_457] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_462 : Valid card_462 := by
  rw [eq_card_462]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_367
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_428
  subst c
  exact placed_valid 0 (0, 2) valid_457

theorem eq_inline_97 : inline_97 = combine (2, 6) [placed 1 (1, 2) card_4, placed 1 (0, 3) card_348] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_97 : Valid inline_97 := by
  rw [eq_inline_97]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_4
  subst c
  exact placed_valid 1 (0, 3) valid_348

theorem eq_card_463 : card_463 = combine (4, 5) [placed 1 (0, 2) card_147, placed 1 (0, 2) card_167, inline_97, placed 0 (0, 0) card_353, placed 2 (3, 8) card_460] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_463 : Valid card_463 := by
  rw [eq_card_463]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_147
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_167
  rcases hc with rfl | hc
  · exact valid_inline_97
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_353
  subst c
  exact placed_valid 2 (3, 8) valid_460

theorem eq_inline_98 : inline_98 = combine (1, 1) [placed 3 (1, 0) card_0, placed 0 (1, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_98 : Valid inline_98 := by
  rw [eq_inline_98]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 0) valid_0
  subst c
  exact placed_valid 0 (1, 0) valid_11

theorem eq_inline_99 : inline_99 = combine (2, 2) [placed 4 (4, 2) card_0, inline_98] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_99 : Valid inline_99 := by
  rw [eq_inline_99]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_0
  subst c
  exact valid_inline_98

theorem eq_inline_100 : inline_100 = combine (1, 5) [placed 4 (1, 2) card_29, placed 5 (0, 5) card_38] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_100 : Valid inline_100 := by
  rw [eq_inline_100]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 2) valid_29
  subst c
  exact placed_valid 5 (0, 5) valid_38

theorem eq_card_464 : card_464 = combine (1, 2) [placed 4 (1, 1) card_15, inline_99, inline_100] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_464 : Valid card_464 := by
  rw [eq_card_464]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_15
  rcases hc with rfl | hc
  · exact valid_inline_99
  subst c
  exact valid_inline_100

theorem eq_inline_101 : inline_101 = combine (3, 4) [placed 2 (0, 4) card_4, placed 0 (0, 4) card_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_101 : Valid inline_101 := by
  rw [eq_inline_101]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_4
  subst c
  exact placed_valid 0 (0, 4) valid_4

theorem eq_inline_102 : inline_102 = combine (2, 4) [placed 1 (1, 1) card_5, inline_101] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_102 : Valid inline_102 := by
  rw [eq_inline_102]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_101

theorem eq_inline_103 : inline_103 = combine (0, 4) [placed 3 (1, 1) card_5, inline_102] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_103 : Valid inline_103 := by
  rw [eq_inline_103]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact valid_inline_102

theorem eq_inline_104 : inline_104 = combine (4, 5) [placed 0 (3, 1) card_39, placed 0 (3, 1) card_42, inline_103] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_104 : Valid inline_104 := by
  rw [eq_inline_104]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_42
  subst c
  exact valid_inline_103

theorem eq_card_465 : card_465 = combine (3, 2) [placed 5 (0, 4) card_25, inline_104] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_465 : Valid card_465 := by
  rw [eq_card_465]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_25
  subst c
  exact valid_inline_104

theorem eq_card_466 : card_466 = combine (1, 4) [placed 4 (1, 0) card_7, placed 1 (0, 1) card_8, placed 0 (0, 0) card_9, placed 0 (0, 0) card_465] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_466 : Valid card_466 := by
  rw [eq_card_466]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_9
  subst c
  exact placed_valid 0 (0, 0) valid_465

theorem eq_card_467 : card_467 = combine (4, 6) [placed 6 (5, 8) card_31, placed 1 (1, 4) card_398, placed 6 (5, 7) card_444, placed 6 (5, 7) card_466] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_467 : Valid card_467 := by
  rw [eq_card_467]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_398
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_444
  subst c
  exact placed_valid 6 (5, 7) valid_466

theorem eq_inline_105 : inline_105 = combine (3, 3) [placed 6 (4, 6) card_71, placed 4 (4, 2) card_71, placed 6 (4, 6) card_73, placed 4 (4, 2) card_73] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_105 : Valid inline_105 := by
  rw [eq_inline_105]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_73
  subst c
  exact placed_valid 4 (4, 2) valid_73

theorem eq_inline_106 : inline_106 = combine (3, 6) [placed 1 (2, 3) card_8, placed 4 (4, 3) card_17, placed 4 (4, 1) card_75, placed 0 (3, 1) card_266, placed 0 (2, 2) card_447] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_106 : Valid inline_106 := by
  rw [eq_inline_106]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_75
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_266
  subst c
  exact placed_valid 0 (2, 2) valid_447

theorem eq_inline_107 : inline_107 = combine (3, 3) [placed 4 (4, 2) card_71, placed 6 (4, 6) card_73, placed 6 (5, 6) card_426, inline_106] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_107 : Valid inline_107 := by
  rw [eq_inline_107]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_73
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_426
  subst c
  exact valid_inline_106

theorem eq_inline_108 : inline_108 = combine (3, 5) [placed 5 (0, 5) card_54, inline_105, inline_107] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_108 : Valid inline_108 := by
  rw [eq_inline_108]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_54
  rcases hc with rfl | hc
  · exact valid_inline_105
  subst c
  exact valid_inline_107

theorem eq_card_468 : card_468 = combine (3, 4) [placed 1 (0, 3) card_28, placed 1 (0, 3) card_126, placed 5 (0, 5) card_126, inline_108] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_468 : Valid card_468 := by
  rw [eq_card_468]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_126
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_126
  subst c
  exact valid_inline_108

theorem eq_inline_109 : inline_109 = combine (2, 3) [placed 5 (0, 3) card_101, placed 3 (2, 1) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_109 : Valid inline_109 := by
  rw [eq_inline_109]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_101
  subst c
  exact placed_valid 3 (2, 1) valid_314

theorem eq_card_469 : card_469 = combine (3, 2) [placed 5 (0, 4) card_78, inline_109] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_469 : Valid card_469 := by
  rw [eq_card_469]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_78
  subst c
  exact valid_inline_109

theorem eq_inline_110 : inline_110 = combine (2, 3) [placed 6 (3, 6) card_54, placed 6 (4, 6) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_110 : Valid inline_110 := by
  rw [eq_inline_110]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_54
  subst c
  exact placed_valid 6 (4, 6) valid_78

theorem eq_inline_111 : inline_111 = combine (2, 3) [placed 7 (3, 6) card_2, placed 6 (4, 6) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_111 : Valid inline_111 := by
  rw [eq_inline_111]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_2
  subst c
  exact placed_valid 6 (4, 6) valid_78

theorem eq_inline_112 : inline_112 = combine (3, 6) [placed 2 (1, 8) card_56, inline_111] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_112 : Valid inline_112 := by
  rw [eq_inline_112]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_56
  subst c
  exact valid_inline_111

theorem eq_card_470 : card_470 = combine (3, 3) [placed 0 (1, 0) card_319, placed 2 (1, 7) card_335, inline_110, inline_112] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_470 : Valid card_470 := by
  rw [eq_card_470]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_319
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_335
  rcases hc with rfl | hc
  · exact valid_inline_110
  subst c
  exact valid_inline_112

theorem eq_inline_113 : inline_113 = combine (3, 4) [placed 4 (3, 0) card_11, placed 3 (4, 1) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_113 : Valid inline_113 := by
  rw [eq_inline_113]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_11
  subst c
  exact placed_valid 3 (4, 1) valid_354

theorem eq_card_471 : card_471 = combine (3, 3) [placed 0 (0, 2) card_5, inline_113] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_471 : Valid card_471 := by
  rw [eq_card_471]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact valid_inline_113

theorem eq_card_472 : card_472 = combine (4, 3) [placed 0 (1, 2) card_5, placed 4 (4, 0) card_471] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_472 : Valid card_472 := by
  rw [eq_card_472]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_5
  subst c
  exact placed_valid 4 (4, 0) valid_471

theorem eq_card_473 : card_473 = combine (1, 1) [placed 6 (4, 2) card_5, placed 0 (0, 0) card_472] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_473 : Valid card_473 := by
  rw [eq_card_473]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_472

theorem eq_card_474 : card_474 = combine (4, 2) [placed 1 (0, 2) card_7, placed 0 (1, 1) card_8, placed 5 (0, 3) card_9, placed 4 (5, 0) card_473] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_474 : Valid card_474 := by
  rw [eq_card_474]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_9
  subst c
  exact placed_valid 4 (5, 0) valid_473

theorem eq_card_475 : card_475 = combine (2, 5) [placed 2 (1, 7) card_13, placed 6 (3, 7) card_14, placed 2 (1, 7) card_31, placed 2 (0, 8) card_396, placed 1 (0, 2) card_474] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_475 : Valid card_475 := by
  rw [eq_card_475]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_396
  subst c
  exact placed_valid 1 (0, 2) valid_474

theorem eq_card_476 : card_476 = combine (3, 5) [placed 0 (2, 1) card_12, placed 4 (4, 1) card_12, placed 2 (2, 7) card_12, placed 4 (4, 2) card_264, placed 5 (1, 6) card_474] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_476 : Valid card_476 := by
  rw [eq_card_476]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_264
  subst c
  exact placed_valid 5 (1, 6) valid_474

theorem eq_card_477 : card_477 = combine (4, 2) [placed 1 (0, 2) card_7, placed 1 (0, 1) card_9, placed 1 (0, 1) card_62, placed 0 (0, 0) card_473] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_477 : Valid card_477 := by
  rw [eq_card_477]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_62
  subst c
  exact placed_valid 0 (0, 0) valid_473

theorem eq_card_478 : card_478 = combine (2, 2) [placed 6 (4, 2) card_5, placed 0 (0, 0) card_472] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_478 : Valid card_478 := by
  rw [eq_card_478]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_472

theorem eq_inline_114 : inline_114 = combine (3, 2) [placed 7 (4, 5) card_8, placed 3 (5, 2) card_386] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_114 : Valid inline_114 := by
  rw [eq_inline_114]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_8
  subst c
  exact placed_valid 3 (5, 2) valid_386

theorem eq_card_479 : card_479 = combine (3, 5) [placed 6 (4, 7) card_14, placed 2 (2, 7) card_31, placed 1 (1, 2) card_181, placed 2 (2, 7) card_367, inline_114, placed 3 (6, 2) card_435, placed 1 (1, 2) card_474] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_479 : Valid card_479 := by
  rw [eq_card_479]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_367
  rcases hc with rfl | hc
  · exact valid_inline_114
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_435
  subst c
  exact placed_valid 1 (1, 2) valid_474

theorem eq_card_480 : card_480 = combine (3, 3) [placed 2 (2, 7) card_13, placed 2 (2, 7) card_14, placed 4 (4, 1) card_192, placed 1 (0, 1) card_298, placed 7 (6, 6) card_435, placed 7 (5, 6) card_474, placed 3 (5, 2) card_477] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_480 : Valid card_480 := by
  rw [eq_card_480]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_298
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_474
  subst c
  exact placed_valid 3 (5, 2) valid_477

theorem eq_card_481 : card_481 = combine (2, 4) [placed 0 (1, 1) card_13, placed 4 (3, 1) card_14, placed 0 (1, 1) card_33, placed 2 (1, 6) card_457, placed 1 (0, 2) card_477] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_481 : Valid card_481 := by
  rw [eq_card_481]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_457
  subst c
  exact placed_valid 1 (0, 2) valid_477

theorem eq_card_482 : card_482 = combine (2, 2) [placed 1 (0, 2) card_7, placed 0 (1, 1) card_24, placed 1 (0, 1) card_124, placed 0 (0, 0) card_472] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_482 : Valid card_482 := by
  rw [eq_card_482]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_24
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_124
  subst c
  exact placed_valid 0 (0, 0) valid_472

theorem eq_card_483 : card_483 = combine (2, 5) [placed 0 (1, 1) card_13, placed 4 (3, 1) card_14, placed 0 (1, 1) card_33, placed 0 (1, 2) card_458, placed 5 (0, 6) card_474] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_483 : Valid card_483 := by
  rw [eq_card_483]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_458
  subst c
  exact placed_valid 5 (0, 6) valid_474

theorem eq_inline_115 : inline_115 = combine (2, 2) [placed 5 (1, 5) card_5, placed 5 (0, 5) card_96] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_115 : Valid inline_115 := by
  rw [eq_inline_115]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_5
  subst c
  exact placed_valid 5 (0, 5) valid_96

theorem eq_inline_116 : inline_116 = combine (4, 4) [placed 0 (3, 2) card_18, placed 2 (3, 7) card_33, placed 6 (4, 5) card_130] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_116 : Valid inline_116 := by
  rw [eq_inline_116]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_18
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_33
  subst c
  exact placed_valid 6 (4, 5) valid_130

theorem eq_inline_117 : inline_117 = combine (2, 2) [placed 5 (1, 5) card_5, placed 5 (0, 5) card_223] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_117 : Valid inline_117 := by
  rw [eq_inline_117]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_5
  subst c
  exact placed_valid 5 (0, 5) valid_223

theorem eq_inline_118 : inline_118 = combine (4, 2) [placed 0 (3, 1) card_39, placed 4 (5, 0) card_268, inline_117] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_118 : Valid inline_118 := by
  rw [eq_inline_118]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 0) valid_268
  subst c
  exact valid_inline_117

theorem eq_inline_119 : inline_119 = combine (3, 2) [inline_115, inline_116, inline_118] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_119 : Valid inline_119 := by
  rw [eq_inline_119]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_115
  rcases hc with rfl | hc
  · exact valid_inline_116
  subst c
  exact valid_inline_118

theorem eq_inline_120 : inline_120 = combine (4, 4) [placed 0 (1, 2) card_58, placed 6 (5, 6) card_168, placed 6 (4, 5) card_357] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_120 : Valid inline_120 := by
  rw [eq_inline_120]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_58
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_168
  subst c
  exact placed_valid 6 (4, 5) valid_357

theorem eq_inline_121 : inline_121 = combine (2, 4) [placed 3 (2, 2) card_314, inline_120] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_121 : Valid inline_121 := by
  rw [eq_inline_121]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 2) valid_314
  subst c
  exact valid_inline_120

theorem eq_card_484 : card_484 = combine (4, 5) [placed 1 (0, 2) card_81, placed 2 (0, 8) card_204, inline_119, inline_121] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_484 : Valid card_484 := by
  rw [eq_card_484]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_81
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_204
  rcases hc with rfl | hc
  · exact valid_inline_119
  subst c
  exact valid_inline_121

theorem eq_inline_122 : inline_122 = combine (4, 5) [placed 1 (0, 2) card_81, placed 2 (0, 8) card_204, placed 0 (0, 0) card_353, placed 2 (2, 8) card_481] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_122 : Valid inline_122 := by
  rw [eq_inline_122]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_81
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_204
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_353
  subst c
  exact placed_valid 2 (2, 8) valid_481

theorem eq_inline_123 : inline_123 = combine (4, 4) [placed 4 (5, 1) card_14, placed 0 (3, 1) card_189, placed 4 (5, 1) card_192, placed 4 (5, 1) card_193, placed 0 (3, 2) card_457, placed 5 (2, 6) card_477] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_123 : Valid inline_123 := by
  rw [eq_inline_123]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_193
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_457
  subst c
  exact placed_valid 5 (2, 6) valid_477

theorem eq_inline_124 : inline_124 = combine (2, 4) [placed 0 (1, 1) card_166, placed 3 (2, 2) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_124 : Valid inline_124 := by
  rw [eq_inline_124]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_166
  subst c
  exact placed_valid 3 (2, 2) valid_314

theorem eq_inline_125 : inline_125 = combine (4, 5) [placed 1 (0, 2) card_81, placed 1 (0, 2) card_167, inline_123, inline_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_125 : Valid inline_125 := by
  rw [eq_inline_125]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_81
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_167
  rcases hc with rfl | hc
  · exact valid_inline_123
  subst c
  exact valid_inline_124

theorem eq_card_485 : card_485 = combine (4, 3) [placed 5 (0, 5) card_313, placed 0 (0, 1) card_469, inline_122, inline_125, placed 0 (0, 0) card_484] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_485 : Valid card_485 := by
  rw [eq_card_485]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_313
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_469
  rcases hc with rfl | hc
  · exact valid_inline_122
  rcases hc with rfl | hc
  · exact valid_inline_125
  subst c
  exact placed_valid 0 (0, 0) valid_484

theorem eq_inline_126 : inline_126 = combine (1, 4) [placed 4 (4, 3) card_5, placed 5 (0, 4) card_156] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_126 : Valid inline_126 := by
  rw [eq_inline_126]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_156

theorem eq_inline_127 : inline_127 = combine (4, 2) [placed 2 (1, 3) card_5, inline_126] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_127 : Valid inline_127 := by
  rw [eq_inline_127]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 3) valid_5
  subst c
  exact valid_inline_126

theorem eq_inline_128 : inline_128 = combine (1, 2) [placed 6 (4, 3) card_5, inline_127] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_128 : Valid inline_128 := by
  rw [eq_inline_128]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_5
  subst c
  exact valid_inline_127

theorem eq_card_486 : card_486 = combine (4, 3) [placed 1 (0, 2) card_19, placed 1 (0, 2) card_84, placed 0 (1, 2) card_314, inline_128] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_486 : Valid card_486 := by
  rw [eq_card_486]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_84
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_314
  subst c
  exact valid_inline_128

theorem eq_card_487 : card_487 = combine (2, 3) [placed 3 (3, 0) card_5, placed 0 (0, 0) card_486] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_487 : Valid card_487 := by
  rw [eq_card_487]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 0) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_486

theorem eq_inline_129 : inline_129 = combine (1, 6) [placed 1 (1, 3) card_5, placed 5 (0, 6) card_34] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_129 : Valid inline_129 := by
  rw [eq_inline_129]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_5
  subst c
  exact placed_valid 5 (0, 6) valid_34

theorem eq_inline_130 : inline_130 = combine (2, 6) [placed 1 (1, 2) card_4, inline_129] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_130 : Valid inline_130 := by
  rw [eq_inline_130]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_4
  subst c
  exact valid_inline_129

theorem eq_inline_131 : inline_131 = combine (4, 4) [placed 0 (4, 2) card_7, placed 4 (5, 2) card_9, placed 0 (1, 3) card_357] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_131 : Valid inline_131 := by
  rw [eq_inline_131]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_9
  subst c
  exact placed_valid 0 (1, 3) valid_357

theorem eq_card_488 : card_488 = combine (4, 6) [placed 6 (5, 9) card_95, inline_130, inline_131] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_488 : Valid card_488 := by
  rw [eq_card_488]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 9) valid_95
  rcases hc with rfl | hc
  · exact valid_inline_130
  subst c
  exact valid_inline_131

theorem eq_inline_132 : inline_132 = combine (5, 7) [placed 0 (4, 4) card_10, placed 6 (5, 8) card_44, placed 0 (4, 4) card_63, placed 5 (2, 8) card_486] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_132 : Valid inline_132 := by
  rw [eq_inline_132]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_63
  subst c
  exact placed_valid 5 (2, 8) valid_486

theorem eq_inline_133 : inline_133 = combine (5, 6) [placed 0 (2, 5) card_5, inline_132] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_133 : Valid inline_133 := by
  rw [eq_inline_133]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_5
  subst c
  exact valid_inline_132

theorem eq_inline_134 : inline_134 = combine (5, 8) [placed 0 (2, 4) card_81, placed 0 (2, 4) card_167, placed 3 (8, 6) card_481, placed 1 (0, 4) card_488] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_134 : Valid inline_134 := by
  rw [eq_inline_134]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_81
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_167
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 6) valid_481
  subst c
  exact placed_valid 1 (0, 4) valid_488

theorem eq_card_489 : card_489 = combine (3, 8) [placed 4 (5, 4) card_313, placed 2 (1, 10) card_470, inline_133, inline_134] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_489 : Valid card_489 := by
  rw [eq_card_489]
  apply combination_rule (3, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 4) valid_313
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_470
  rcases hc with rfl | hc
  · exact valid_inline_133
  subst c
  exact valid_inline_134

theorem eq_card_490 : card_490 = combine (5, 7) [placed 0 (2, 3) card_321, placed 2 (2, 11) card_321, placed 1 (0, 6) card_485, placed 5 (0, 8) card_485, placed 0 (0, 2) card_489, placed 2 (0, 12) card_489] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_490 : Valid card_490 := by
  rw [eq_card_490]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_321
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 11) valid_321
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 6) valid_485
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 8) valid_485
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_489
  subst c
  exact placed_valid 2 (0, 12) valid_489

theorem eq_inline_135 : inline_135 = combine (5, 3) [placed 5 (2, 4) card_60, placed 7 (6, 4) card_60, placed 2 (3, 4) card_83, placed 1 (1, 2) card_106] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_135 : Valid inline_135 := by
  rw [eq_inline_135]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_60
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_60
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_83
  subst c
  exact placed_valid 1 (1, 2) valid_106

theorem eq_inline_136 : inline_136 = combine (5, 3) [placed 5 (2, 4) card_60, placed 7 (5, 3) card_70, placed 2 (2, 5) card_345] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_136 : Valid inline_136 := by
  rw [eq_inline_136]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_60
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 3) valid_70
  subst c
  exact placed_valid 2 (2, 5) valid_345

theorem eq_card_491 : card_491 = combine (3, 3) [placed 4 (4, 0) card_44, placed 0 (1, 1) card_270, inline_135, inline_136] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_491 : Valid card_491 := by
  rw [eq_card_491]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_270
  rcases hc with rfl | hc
  · exact valid_inline_135
  subst c
  exact valid_inline_136

theorem eq_inline_137 : inline_137 = combine (2, 3) [placed 6 (4, 3) card_0, placed 3 (4, 1) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_137 : Valid inline_137 := by
  rw [eq_inline_137]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 3 (4, 1) valid_32

theorem eq_inline_138 : inline_138 = combine (1, 3) [placed 7 (1, 5) card_0, inline_137] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_138 : Valid inline_138 := by
  rw [eq_inline_138]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact valid_inline_137

theorem eq_card_492 : card_492 = combine (1, 2) [placed 7 (4, 4) card_78, inline_138] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_492 : Valid card_492 := by
  rw [eq_card_492]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_78
  subst c
  exact valid_inline_138

theorem eq_card_493 : card_493 = combine (3, 3) [placed 0 (0, 0) card_87, placed 3 (4, 1) card_197, placed 0 (0, 0) card_492] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_493 : Valid card_493 := by
  rw [eq_card_493]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_87
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 1) valid_197
  subst c
  exact placed_valid 0 (0, 0) valid_492

theorem eq_card_494 : card_494 = combine (3, 3) [placed 0 (3, 0) card_7, placed 0 (0, 0) card_87, placed 0 (0, 0) card_286, placed 0 (0, 0) card_492] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_494 : Valid card_494 := by
  rw [eq_card_494]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_87
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_286
  subst c
  exact placed_valid 0 (0, 0) valid_492

theorem eq_inline_139 : inline_139 = combine (2, 2) [placed 3 (2, 2) card_5, placed 2 (0, 5) card_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_139 : Valid inline_139 := by
  rw [eq_inline_139]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 2) valid_5
  subst c
  exact placed_valid 2 (0, 5) valid_221

theorem eq_card_495 : card_495 = combine (2, 4) [placed 0 (1, 2) card_10, placed 4 (2, 2) card_52, placed 6 (2, 6) card_52, inline_139] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_495 : Valid card_495 := by
  rw [eq_card_495]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_52
  subst c
  exact valid_inline_139

theorem eq_inline_140 : inline_140 = combine (1, 2) [placed 5 (0, 5) card_0, placed 1 (0, 1) card_30] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_140 : Valid inline_140 := by
  rw [eq_inline_140]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_0
  subst c
  exact placed_valid 1 (0, 1) valid_30

theorem eq_card_496 : card_496 = combine (1, 1) [placed 5 (0, 4) card_5, inline_140] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_496 : Valid card_496 := by
  rw [eq_card_496]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_5
  subst c
  exact valid_inline_140

theorem eq_card_497 : card_497 = combine (0, 3) [placed 1 (0, 1) card_5, placed 0 (0, 0) card_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_497 : Valid card_497 := by
  rw [eq_card_497]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_496

theorem eq_card_498 : card_498 = combine (4, 3) [placed 1 (1, 1) card_114, placed 4 (4, 0) card_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_498 : Valid card_498 := by
  rw [eq_card_498]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_114
  subst c
  exact placed_valid 4 (4, 0) valid_496

theorem eq_inline_141 : inline_141 = combine (4, 3) [placed 6 (4, 3) card_1, placed 0 (1, 1) card_347] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_141 : Valid inline_141 := by
  rw [eq_inline_141]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_1
  subst c
  exact placed_valid 0 (1, 1) valid_347

theorem eq_inline_142 : inline_142 = combine (3, 3) [placed 1 (0, 2) card_43, placed 0 (2, 0) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_142 : Valid inline_142 := by
  rw [eq_inline_142]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_43
  subst c
  exact placed_valid 0 (2, 0) valid_52

theorem eq_card_499 : card_499 = combine (2, 1) [placed 4 (2, 0) card_15, inline_141, inline_142] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_499 : Valid card_499 := by
  rw [eq_card_499]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_15
  rcases hc with rfl | hc
  · exact valid_inline_141
  subst c
  exact valid_inline_142

theorem eq_inline_143 : inline_143 = combine (1, 1) [placed 3 (1, 1) card_5, placed 0 (0, 0) card_146] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_143 : Valid inline_143 := by
  rw [eq_inline_143]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_146

theorem eq_card_500 : card_500 = combine (1, 2) [placed 7 (1, 5) card_0, inline_143] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_500 : Valid card_500 := by
  rw [eq_card_500]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact valid_inline_143

theorem eq_card_501 : card_501 = combine (1, 3) [placed 4 (4, 3) card_2, placed 0 (0, 0) card_500] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_501 : Valid card_501 := by
  rw [eq_card_501]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_2
  subst c
  exact placed_valid 0 (0, 0) valid_500

theorem eq_inline_144 : inline_144 = combine (2, 4) [placed 1 (0, 3) card_11, placed 2 (2, 6) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_144 : Valid inline_144 := by
  rw [eq_inline_144]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_11
  subst c
  exact placed_valid 2 (2, 6) valid_53

theorem eq_card_502 : card_502 = combine (4, 3) [placed 1 (0, 3) card_7, placed 2 (1, 5) card_69, inline_144] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_502 : Valid card_502 := by
  rw [eq_card_502]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_69
  subst c
  exact valid_inline_144

theorem eq_card_503 : card_503 = combine (2, 3) [placed 2 (0, 3) card_0, placed 0 (0, 0) card_502] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_503 : Valid card_503 := by
  rw [eq_card_503]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_502

theorem eq_inline_145 : inline_145 = combine (2, 3) [placed 7 (3, 6) card_0, placed 1 (0, 1) card_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_145 : Valid inline_145 := by
  rw [eq_inline_145]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_0
  subst c
  exact placed_valid 1 (0, 1) valid_56

theorem eq_inline_146 : inline_146 = combine (3, 5) [placed 0 (3, 1) card_6, placed 0 (2, 2) card_18, inline_145] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_146 : Valid inline_146 := by
  rw [eq_inline_146]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_18
  subst c
  exact valid_inline_145

theorem eq_card_504 : card_504 = combine (3, 1) [placed 7 (4, 4) card_32, inline_146] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_504 : Valid card_504 := by
  rw [eq_card_504]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_32
  subst c
  exact valid_inline_146

theorem eq_inline_147 : inline_147 = combine (4, 2) [placed 0 (1, 1) card_5, placed 0 (1, 0) card_350] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_147 : Valid inline_147 := by
  rw [eq_inline_147]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_350

theorem eq_inline_148 : inline_148 = combine (4, 3) [placed 7 (4, 4) card_5, placed 0 (4, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_148 : Valid inline_148 := by
  rw [eq_inline_148]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_5
  subst c
  exact placed_valid 0 (4, 1) valid_6

theorem eq_inline_149 : inline_149 = combine (4, 2) [placed 0 (1, 1) card_5, inline_148] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_149 : Valid inline_149 := by
  rw [eq_inline_149]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_5
  subst c
  exact valid_inline_148

theorem eq_card_505 : card_505 = combine (4, 1) [placed 5 (0, 1) card_6, inline_147, inline_149] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_505 : Valid card_505 := by
  rw [eq_card_505]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_6
  rcases hc with rfl | hc
  · exact valid_inline_147
  subst c
  exact valid_inline_149

theorem eq_inline_150 : inline_150 = combine (1, 2) [placed 2 (1, 6) card_7, placed 5 (0, 5) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_150 : Valid inline_150 := by
  rw [eq_inline_150]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_7
  subst c
  exact placed_valid 5 (0, 5) valid_32

theorem eq_card_506 : card_506 = combine (1, 5) [placed 2 (1, 6) card_44, placed 0 (0, 1) card_67, inline_150] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_506 : Valid card_506 := by
  rw [eq_card_506]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_67
  subst c
  exact valid_inline_150

theorem eq_inline_151 : inline_151 = combine (3, 5) [placed 6 (4, 7) card_33, placed 6 (3, 6) card_44, placed 5 (1, 6) card_47] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_151 : Valid inline_151 := by
  rw [eq_inline_151]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_44
  subst c
  exact placed_valid 5 (1, 6) valid_47

theorem eq_card_507 : card_507 = combine (3, 4) [placed 1 (0, 3) card_44, placed 0 (0, 0) card_274, placed 4 (4, 0) card_506, inline_151] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_507 : Valid card_507 := by
  rw [eq_card_507]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_274
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_506
  subst c
  exact valid_inline_151

theorem eq_card_508 : card_508 = combine (4, 3) [placed 1 (0, 2) card_12, placed 1 (0, 2) card_13, placed 1 (0, 2) card_14, placed 0 (0, 0) card_297, placed 0 (0, 0) card_298, placed 2 (1, 5) card_474, placed 0 (1, 0) card_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_508 : Valid card_508 := by
  rw [eq_card_508]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_297
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_298
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_474
  subst c
  exact placed_valid 0 (1, 0) valid_507

theorem eq_card_509 : card_509 = combine (4, 3) [placed 5 (0, 4) card_12, placed 1 (0, 2) card_127, placed 1 (0, 2) card_128, placed 0 (1, 1) card_474, placed 0 (1, 0) card_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_509 : Valid card_509 := by
  rw [eq_card_509]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_127
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_128
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_474
  subst c
  exact placed_valid 0 (1, 0) valid_507

theorem eq_inline_152 : inline_152 = combine (1, 4) [placed 4 (5, 3) card_0, placed 3 (4, 3) card_138] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_152 : Valid inline_152 := by
  rw [eq_inline_152]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_0
  subst c
  exact placed_valid 3 (4, 3) valid_138

theorem eq_card_510 : card_510 = combine (4, 3) [placed 5 (1, 4) card_10, inline_152, placed 0 (1, 0) card_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_510 : Valid card_510 := by
  rw [eq_card_510]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_10
  rcases hc with rfl | hc
  · exact valid_inline_152
  subst c
  exact placed_valid 0 (1, 0) valid_507

theorem eq_inline_153 : inline_153 = combine (4, 4) [placed 6 (4, 4) card_2, placed 0 (3, 1) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_153 : Valid inline_153 := by
  rw [eq_inline_153]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_2
  subst c
  exact placed_valid 0 (3, 1) valid_44

theorem eq_inline_154 : inline_154 = combine (3, 5) [placed 0 (3, 1) card_7, placed 4 (4, 1) card_9, placed 0 (1, 2) card_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_154 : Valid inline_154 := by
  rw [eq_inline_154]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_9
  subst c
  exact placed_valid 0 (1, 2) valid_221

theorem eq_inline_155 : inline_155 = combine (2, 4) [placed 6 (4, 4) card_0, inline_154] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_155 : Valid inline_155 := by
  rw [eq_inline_155]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_0
  subst c
  exact valid_inline_154

theorem eq_inline_156 : inline_156 = combine (3, 4) [placed 4 (4, 0) card_13, placed 4 (4, 0) card_14, placed 0 (0, 1) card_240, inline_153, inline_155] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_156 : Valid inline_156 := by
  rw [eq_inline_156]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_240
  rcases hc with rfl | hc
  · exact valid_inline_153
  subst c
  exact valid_inline_155

theorem eq_card_511 : card_511 = combine (1, 4) [placed 6 (1, 5) card_15, inline_156] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_511 : Valid card_511 := by
  rw [eq_card_511]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 5) valid_15
  subst c
  exact valid_inline_156

theorem block07_valid : Valid card_448 ∧ Valid card_449 ∧ Valid card_450 ∧ Valid card_451 ∧ Valid card_452 ∧ Valid card_453 ∧ Valid card_454 ∧ Valid card_455 ∧ Valid card_456 ∧ Valid card_457 ∧ Valid card_458 ∧ Valid card_459 ∧ Valid card_460 ∧ Valid card_461 ∧ Valid card_462 ∧ Valid card_463 ∧ Valid card_464 ∧ Valid card_465 ∧ Valid card_466 ∧ Valid card_467 ∧ Valid card_468 ∧ Valid card_469 ∧ Valid card_470 ∧ Valid card_471 ∧ Valid card_472 ∧ Valid card_473 ∧ Valid card_474 ∧ Valid card_475 ∧ Valid card_476 ∧ Valid card_477 ∧ Valid card_478 ∧ Valid card_479 ∧ Valid card_480 ∧ Valid card_481 ∧ Valid card_482 ∧ Valid card_483 ∧ Valid card_484 ∧ Valid card_485 ∧ Valid card_486 ∧ Valid card_487 ∧ Valid card_488 ∧ Valid card_489 ∧ Valid card_490 ∧ Valid card_491 ∧ Valid card_492 ∧ Valid card_493 ∧ Valid card_494 ∧ Valid card_495 ∧ Valid card_496 ∧ Valid card_497 ∧ Valid card_498 ∧ Valid card_499 ∧ Valid card_500 ∧ Valid card_501 ∧ Valid card_502 ∧ Valid card_503 ∧ Valid card_504 ∧ Valid card_505 ∧ Valid card_506 ∧ Valid card_507 ∧ Valid card_508 ∧ Valid card_509 ∧ Valid card_510 ∧ Valid card_511 ∧ True :=
  ⟨valid_448, valid_449, valid_450, valid_451, valid_452, valid_453, valid_454, valid_455, valid_456, valid_457, valid_458, valid_459, valid_460, valid_461, valid_462, valid_463, valid_464, valid_465, valid_466, valid_467, valid_468, valid_469, valid_470, valid_471, valid_472, valid_473, valid_474, valid_475, valid_476, valid_477, valid_478, valid_479, valid_480, valid_481, valid_482, valid_483, valid_484, valid_485, valid_486, valid_487, valid_488, valid_489, valid_490, valid_491, valid_492, valid_493, valid_494, valid_495, valid_496, valid_497, valid_498, valid_499, valid_500, valid_501, valid_502, valid_503, valid_504, valid_505, valid_506, valid_507, valid_508, valid_509, valid_510, valid_511, True.intro⟩

end OAI.Snaky21.Certificate

theorem solution : Valid card_448 ∧ Valid card_449 ∧ Valid card_450 ∧ Valid card_451 ∧ Valid card_452 ∧ Valid card_453 ∧ Valid card_454 ∧ Valid card_455 ∧ Valid card_456 ∧ Valid card_457 ∧ Valid card_458 ∧ Valid card_459 ∧ Valid card_460 ∧ Valid card_461 ∧ Valid card_462 ∧ Valid card_463 ∧ Valid card_464 ∧ Valid card_465 ∧ Valid card_466 ∧ Valid card_467 ∧ Valid card_468 ∧ Valid card_469 ∧ Valid card_470 ∧ Valid card_471 ∧ Valid card_472 ∧ Valid card_473 ∧ Valid card_474 ∧ Valid card_475 ∧ Valid card_476 ∧ Valid card_477 ∧ Valid card_478 ∧ Valid card_479 ∧ Valid card_480 ∧ Valid card_481 ∧ Valid card_482 ∧ Valid card_483 ∧ Valid card_484 ∧ Valid card_485 ∧ Valid card_486 ∧ Valid card_487 ∧ Valid card_488 ∧ Valid card_489 ∧ Valid card_490 ∧ Valid card_491 ∧ Valid card_492 ∧ Valid card_493 ∧ Valid card_494 ∧ Valid card_495 ∧ Valid card_496 ∧ Valid card_497 ∧ Valid card_498 ∧ Valid card_499 ∧ Valid card_500 ∧ Valid card_501 ∧ Valid card_502 ∧ Valid card_503 ∧ Valid card_504 ∧ Valid card_505 ∧ Valid card_506 ∧ Valid card_507 ∧ Valid card_508 ∧ Valid card_509 ∧ Valid card_510 ∧ Valid card_511 ∧ True := block07_valid
