-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block05_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T10:38:12.656677+00:00
-- url     : https://prove2.me/submissions/4fcb1dd1-bc29-42aa-898e-dfb5eed4e014

import Definitions.Def_Snaky21Data05
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
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
end OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_320 : card_320 = combine (3, 5) [placed 0 (0, 4) card_5, placed 0 (2, 0) card_316] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_320 : Valid card_320 := by
  rw [eq_card_320]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 4) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_316

theorem eq_card_321 : card_321 = combine (3, 3) [placed 2 (0, 4) card_5, placed 0 (0, 0) card_320] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_321 : Valid card_321 := by
  rw [eq_card_321]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_320

theorem eq_card_322 : card_322 = combine (4, 4) [placed 5 (0, 4) card_7, placed 1 (0, 3) card_9, placed 0 (1, 0) card_321] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_322 : Valid card_322 := by
  rw [eq_card_322]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_321

theorem eq_card_323 : card_323 = combine (2, 4) [placed 7 (5, 4) card_11, placed 4 (4, 0) card_320] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_323 : Valid card_323 := by
  rw [eq_card_323]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_11
  subst c
  exact placed_valid 4 (4, 0) valid_320

theorem eq_card_324 : card_324 = combine (1, 3) [placed 2 (0, 6) card_60, placed 0 (0, 2) card_237, placed 0 (0, 2) card_307, placed 4 (2, 0) card_316] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_324 : Valid card_324 := by
  rw [eq_card_324]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_60
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_237
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_307
  subst c
  exact placed_valid 4 (2, 0) valid_316

theorem eq_card_325 : card_325 = combine (3, 4) [placed 4 (4, 4) card_5, placed 0 (1, 0) card_321] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_325 : Valid card_325 := by
  rw [eq_card_325]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 4) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_321

theorem eq_card_326 : card_326 = combine (2, 4) [placed 6 (4, 4) card_3, placed 0 (2, 0) card_321] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_326 : Valid card_326 := by
  rw [eq_card_326]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_3
  subst c
  exact placed_valid 0 (2, 0) valid_321

theorem eq_card_327 : card_327 = combine (4, 4) [placed 0 (1, 3) card_32, placed 4 (4, 0) card_321] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_327 : Valid card_327 := by
  rw [eq_card_327]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_32
  subst c
  exact placed_valid 4 (4, 0) valid_321

theorem eq_card_328 : card_328 = combine (3, 4) [placed 1 (0, 4) card_7, placed 5 (0, 5) card_9, placed 0 (1, 0) card_321] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_328 : Valid card_328 := by
  rw [eq_card_328]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_321

theorem eq_card_329 : card_329 = combine (1, 4) [placed 2 (0, 6) card_10, placed 4 (1, 2) card_52, placed 6 (1, 6) card_52, placed 0 (0, 2) card_315] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_329 : Valid card_329 := by
  rw [eq_card_329]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_52
  subst c
  exact placed_valid 0 (0, 2) valid_315

theorem eq_card_330 : card_330 = combine (3, 4) [placed 5 (0, 4) card_7, placed 1 (0, 3) card_9, placed 0 (1, 0) card_321] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_330 : Valid card_330 := by
  rw [eq_card_330]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_321

theorem eq_inline_2 : inline_2 = combine (3, 5) [placed 0 (2, 2) card_20, placed 6 (3, 5) card_29] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_2 : Valid inline_2 := by
  rw [eq_inline_2]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_20
  subst c
  exact placed_valid 6 (3, 5) valid_29

theorem eq_inline_3 : inline_3 = combine (3, 2) [placed 2 (0, 3) card_5, inline_2] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_3 : Valid inline_3 := by
  rw [eq_inline_3]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact valid_inline_2

theorem eq_card_331 : card_331 = combine (3, 4) [placed 0 (0, 3) card_5, inline_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_331 : Valid card_331 := by
  rw [eq_card_331]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact valid_inline_3

theorem eq_card_332 : card_332 = combine (4, 3) [placed 1 (0, 2) card_9, placed 1 (0, 3) card_11, placed 4 (4, 0) card_331] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_332 : Valid card_332 := by
  rw [eq_card_332]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_11
  subst c
  exact placed_valid 4 (4, 0) valid_331

theorem eq_inline_4 : inline_4 = combine (0, 2) [placed 7 (1, 5) card_0, placed 1 (0, 0) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_4 : Valid inline_4 := by
  rw [eq_inline_4]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 1 (0, 0) valid_3

theorem eq_card_333 : card_333 = combine (1, 4) [placed 7 (1, 4) card_3, inline_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_333 : Valid card_333 := by
  rw [eq_card_333]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_3
  subst c
  exact valid_inline_4

theorem eq_card_334 : card_334 = combine (1, 5) [placed 0 (0, 1) card_101, placed 6 (1, 6) card_101, placed 0 (0, 2) card_333, placed 6 (1, 5) card_333] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_334 : Valid card_334 := by
  rw [eq_card_334]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_101
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_101
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_333
  subst c
  exact placed_valid 6 (1, 5) valid_333

theorem eq_card_335 : card_335 = combine (3, 3) [placed 1 (0, 2) card_52, placed 4 (3, 0) card_334] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_335 : Valid card_335 := by
  rw [eq_card_335]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_52
  subst c
  exact placed_valid 4 (3, 0) valid_334

theorem eq_inline_5 : inline_5 = combine (1, 5) [placed 7 (1, 5) card_4, placed 4 (2, 2) card_37] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_5 : Valid inline_5 := by
  rw [eq_inline_5]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_4
  subst c
  exact placed_valid 4 (2, 2) valid_37

theorem eq_inline_6 : inline_6 = combine (2, 3) [placed 1 (1, 0) card_5, inline_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_6 : Valid inline_6 := by
  rw [eq_inline_6]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_5
  subst c
  exact valid_inline_5

theorem eq_card_336 : card_336 = combine (1, 4) [placed 0 (1, 0) card_6, placed 0 (0, 1) card_18, inline_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_336 : Valid card_336 := by
  rw [eq_card_336]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_18
  subst c
  exact valid_inline_6

theorem eq_card_337 : card_337 = combine (1, 2) [placed 2 (1, 6) card_7, placed 5 (0, 5) card_143, placed 0 (0, 2) card_336] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_337 : Valid card_337 := by
  rw [eq_card_337]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_143
  subst c
  exact placed_valid 0 (0, 2) valid_336

theorem eq_card_338 : card_338 = combine (2, 4) [placed 6 (2, 6) card_44, placed 5 (0, 6) card_47, placed 0 (1, 0) card_337] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_338 : Valid card_338 := by
  rw [eq_card_338]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_47
  subst c
  exact placed_valid 0 (1, 0) valid_337

theorem eq_card_339 : card_339 = combine (4, 2) [placed 7 (4, 4) card_35, placed 4 (4, 1) card_336] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_339 : Valid card_339 := by
  rw [eq_card_339]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_35
  subst c
  exact placed_valid 4 (4, 1) valid_336

theorem eq_inline_7 : inline_7 = combine (1, 6) [placed 3 (1, 3) card_5, placed 0 (0, 3) card_91] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_7 : Valid inline_7 := by
  rw [eq_inline_7]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 3) valid_5
  subst c
  exact placed_valid 0 (0, 3) valid_91

theorem eq_card_340 : card_340 = combine (0, 6) [placed 4 (1, 2) card_139, placed 2 (0, 6) card_148, inline_7] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_340 : Valid card_340 := by
  rw [eq_card_340]
  apply combination_rule (0, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 2) valid_139
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_148
  subst c
  exact valid_inline_7

theorem eq_card_341 : card_341 = combine (4, 4) [placed 7 (6, 4) card_53, placed 3 (6, 2) card_57, placed 0 (2, 0) card_340] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_341 : Valid card_341 := by
  rw [eq_card_341]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_57
  subst c
  exact placed_valid 0 (2, 0) valid_340

theorem eq_inline_8 : inline_8 = combine (3, 4) [placed 4 (3, 0) card_11, placed 3 (4, 1) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_8 : Valid inline_8 := by
  rw [eq_inline_8]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_11
  subst c
  exact placed_valid 3 (4, 1) valid_78

theorem eq_card_342 : card_342 = combine (3, 1) [placed 2 (0, 2) card_5, inline_8] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_342 : Valid card_342 := by
  rw [eq_card_342]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact valid_inline_8

theorem eq_card_343 : card_343 = combine (3, 3) [placed 0 (0, 2) card_5, placed 0 (0, 0) card_342] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_343 : Valid card_343 := by
  rw [eq_card_343]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_342

theorem eq_card_344 : card_344 = combine (1, 3) [placed 4 (4, 2) card_5, placed 0 (1, 0) card_343] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_344 : Valid card_344 := by
  rw [eq_card_344]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_343

theorem eq_card_345 : card_345 = combine (4, 2) [placed 0 (1, 1) card_8, placed 1 (0, 2) card_11, placed 0 (0, 0) card_344] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_345 : Valid card_345 := by
  rw [eq_card_345]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_11
  subst c
  exact placed_valid 0 (0, 0) valid_344

theorem eq_card_346 : card_346 = combine (2, 3) [placed 6 (4, 3) card_0, placed 2 (0, 5) card_342] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_346 : Valid card_346 := by
  rw [eq_card_346]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 2 (0, 5) valid_342

theorem eq_inline_9 : inline_9 = combine (2, 3) [placed 1 (1, 0) card_5, placed 5 (0, 3) card_94] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_9 : Valid inline_9 := by
  rw [eq_inline_9]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_5
  subst c
  exact placed_valid 5 (0, 3) valid_94

theorem eq_inline_10 : inline_10 = combine (0, 3) [placed 3 (1, 0) card_5, inline_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_10 : Valid inline_10 := by
  rw [eq_inline_10]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 0) valid_5
  subst c
  exact valid_inline_9

theorem eq_card_347 : card_347 = combine (1, 3) [placed 0 (0, 0) card_20, placed 4 (1, 0) card_29, inline_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_347 : Valid card_347 := by
  rw [eq_card_347]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_29
  subst c
  exact valid_inline_10

theorem eq_inline_11 : inline_11 = combine (3, 0) [placed 2 (0, 1) card_5, placed 1 (2, 0) card_311] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_11 : Valid inline_11 := by
  rw [eq_inline_11]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 1 (2, 0) valid_311

theorem eq_card_348 : card_348 = combine (3, 1) [placed 0 (0, 1) card_5, inline_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_348 : Valid card_348 := by
  rw [eq_card_348]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_11

theorem eq_inline_12 : inline_12 = combine (4, 3) [placed 4 (4, 2) card_10, placed 5 (0, 4) card_54] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_12 : Valid inline_12 := by
  rw [eq_inline_12]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_10
  subst c
  exact placed_valid 5 (0, 4) valid_54

theorem eq_card_349 : card_349 = combine (3, 5) [placed 4 (4, 1) card_12, placed 0 (0, 2) card_165, placed 2 (0, 6) card_216, inline_12] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_349 : Valid card_349 := by
  rw [eq_card_349]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_165
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_216
  subst c
  exact valid_inline_12

theorem eq_inline_13 : inline_13 = combine (4, 1) [placed 5 (3, 4) card_1, placed 2 (1, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_13 : Valid inline_13 := by
  rw [eq_inline_13]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_1
  subst c
  exact placed_valid 2 (1, 1) valid_5

theorem eq_card_350 : card_350 = combine (4, 0) [placed 2 (0, 1) card_4, inline_13] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_350 : Valid card_350 := by
  rw [eq_card_350]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact valid_inline_13

theorem eq_card_351 : card_351 = combine (3, 1) [placed 0 (0, 1) card_5, placed 0 (0, 0) card_350] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_351 : Valid card_351 := by
  rw [eq_card_351]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_350

theorem eq_card_352 : card_352 = combine (4, 2) [placed 0 (0, 1) card_4, placed 0 (1, 0) card_351] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_352 : Valid card_352 := by
  rw [eq_card_352]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_4
  subst c
  exact placed_valid 0 (1, 0) valid_351

theorem eq_card_353 : card_353 = combine (4, 6) [placed 6 (5, 9) card_95, placed 1 (0, 2) card_352] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_353 : Valid card_353 := by
  rw [eq_card_353]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 9) valid_95
  subst c
  exact placed_valid 1 (0, 2) valid_352

theorem eq_inline_14 : inline_14 = combine (3, 2) [placed 0 (0, 1) card_5, placed 4 (3, 0) card_70] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_14 : Valid inline_14 := by
  rw [eq_inline_14]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_70

theorem eq_card_354 : card_354 = combine (3, 0) [placed 2 (0, 1) card_5, inline_14] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_354 : Valid card_354 := by
  rw [eq_card_354]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_14

theorem eq_card_355 : card_355 = combine (3, 4) [placed 1 (2, 1) card_8, placed 7 (4, 4) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_355 : Valid card_355 := by
  rw [eq_card_355]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_8
  subst c
  exact placed_valid 7 (4, 4) valid_354

theorem eq_inline_15 : inline_15 = combine (2, 3) [placed 4 (3, 2) card_21, placed 7 (4, 5) card_121] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_15 : Valid inline_15 := by
  rw [eq_inline_15]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_21
  subst c
  exact placed_valid 7 (4, 5) valid_121

theorem eq_card_356 : card_356 = combine (3, 5) [placed 2 (3, 6) card_7, placed 1 (2, 2) card_8, inline_15] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_356 : Valid card_356 := by
  rw [eq_card_356]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_8
  subst c
  exact valid_inline_15

theorem eq_inline_16 : inline_16 = combine (1, 4) [placed 1 (0, 0) card_3, placed 4 (4, 3) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_16 : Valid inline_16 := by
  rw [eq_inline_16]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_3
  subst c
  exact placed_valid 4 (4, 3) valid_5

theorem eq_inline_17 : inline_17 = combine (1, 3) [placed 6 (4, 3) card_4, inline_16] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_17 : Valid inline_17 := by
  rw [eq_inline_17]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_4
  subst c
  exact valid_inline_16

theorem eq_inline_18 : inline_18 = combine (4, 3) [placed 1 (3, 0) card_5, inline_17] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_18 : Valid inline_18 := by
  rw [eq_inline_18]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 0) valid_5
  subst c
  exact valid_inline_17

theorem eq_card_357 : card_357 = combine (2, 3) [placed 3 (3, 0) card_5, inline_18] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_357 : Valid card_357 := by
  rw [eq_card_357]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 0) valid_5
  subst c
  exact valid_inline_18

theorem eq_card_358 : card_358 = combine (2, 4) [placed 1 (1, 1) card_5, placed 5 (0, 4) card_357] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_358 : Valid card_358 := by
  rw [eq_card_358]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_357

theorem eq_inline_19 : inline_19 = combine (1, 6) [placed 7 (1, 6) card_5, placed 4 (2, 2) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_19 : Valid inline_19 := by
  rw [eq_inline_19]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 6) valid_5
  subst c
  exact placed_valid 4 (2, 2) valid_9

theorem eq_card_359 : card_359 = combine (1, 4) [placed 2 (0, 6) card_10, placed 4 (1, 2) card_52, placed 6 (1, 6) card_52, inline_19] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_359 : Valid card_359 := by
  rw [eq_card_359]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_52
  subst c
  exact valid_inline_19

theorem eq_inline_20 : inline_20 = combine (2, 3) [placed 7 (2, 4) card_5, placed 5 (0, 4) card_45] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_20 : Valid inline_20 := by
  rw [eq_inline_20]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 4) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_45

theorem eq_card_360 : card_360 = combine (2, 4) [placed 4 (2, 0) card_22, placed 1 (0, 1) card_347, inline_20] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_360 : Valid card_360 := by
  rw [eq_card_360]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_347
  subst c
  exact valid_inline_20

theorem eq_card_361 : card_361 = combine (3, 1) [placed 4 (3, 0) card_15, placed 1 (0, 0) card_57, placed 1 (1, 1) card_360] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_361 : Valid card_361 := by
  rw [eq_card_361]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_57
  subst c
  exact placed_valid 1 (1, 1) valid_360

theorem eq_inline_21 : inline_21 = combine (1, 4) [placed 6 (4, 4) card_2, placed 6 (1, 6) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_21 : Valid inline_21 := by
  rw [eq_inline_21]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_2
  subst c
  exact placed_valid 6 (1, 6) valid_53

theorem eq_card_362 : card_362 = combine (1, 3) [placed 0 (0, 3) card_2, inline_21] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_362 : Valid card_362 := by
  rw [eq_card_362]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_2
  subst c
  exact valid_inline_21

theorem eq_card_363 : card_363 = combine (4, 4) [placed 0 (3, 1) card_44, placed 0 (0, 0) card_362] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_363 : Valid card_363 := by
  rw [eq_card_363]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_44
  subst c
  exact placed_valid 0 (0, 0) valid_362

theorem eq_card_364 : card_364 = combine (4, 4) [placed 0 (3, 1) card_52, placed 0 (0, 0) card_362] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_364 : Valid card_364 := by
  rw [eq_card_364]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_52
  subst c
  exact placed_valid 0 (0, 0) valid_362

theorem eq_inline_22 : inline_22 = combine (0, 4) [placed 3 (1, 0) card_0, placed 7 (1, 7) card_0] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_22 : Valid inline_22 := by
  rw [eq_inline_22]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 0) valid_0
  subst c
  exact placed_valid 7 (1, 7) valid_0

theorem eq_inline_23 : inline_23 = combine (0, 3) [placed 7 (1, 6) card_5, inline_22] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_23 : Valid inline_23 := by
  rw [eq_inline_23]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 6) valid_5
  subst c
  exact valid_inline_22

theorem eq_card_365 : card_365 = combine (1, 6) [placed 0 (1, 2) card_6, inline_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_365 : Valid card_365 := by
  rw [eq_card_365]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_6
  subst c
  exact valid_inline_23

theorem eq_card_366 : card_366 = combine (1, 1) [placed 6 (1, 5) card_6, placed 4 (2, 0) card_365] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_366 : Valid card_366 := by
  rw [eq_card_366]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 5) valid_6
  subst c
  exact placed_valid 4 (2, 0) valid_365

theorem eq_card_367 : card_367 = combine (1, 5) [placed 1 (0, 2) card_8, placed 6 (2, 6) card_9, placed 0 (0, 0) card_366] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_367 : Valid card_367 := by
  rw [eq_card_367]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_9
  subst c
  exact placed_valid 0 (0, 0) valid_366

theorem eq_card_368 : card_368 = combine (4, 5) [placed 2 (3, 7) card_14, placed 2 (3, 7) card_31, placed 3 (6, 2) card_181, placed 0 (3, 1) card_189, placed 3 (7, 2) card_257, placed 2 (1, 6) card_355, placed 6 (5, 7) card_367] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_368 : Valid card_368 := by
  rw [eq_card_368]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 2) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_355
  subst c
  exact placed_valid 6 (5, 7) valid_367

theorem eq_inline_24 : inline_24 = combine (1, 7) [placed 4 (1, 3) card_6, placed 1 (0, 4) card_8, placed 0 (0, 2) card_365] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_24 : Valid inline_24 := by
  rw [eq_inline_24]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_8
  subst c
  exact placed_valid 0 (0, 2) valid_365

theorem eq_card_369 : card_369 = combine (1, 6) [placed 6 (1, 7) card_7, placed 0 (0, 2) card_19, placed 6 (1, 8) card_187, inline_24] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_369 : Valid card_369 := by
  rw [eq_card_369]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 8) valid_187
  subst c
  exact valid_inline_24

theorem eq_inline_25 : inline_25 = combine (1, 2) [placed 1 (1, 1) card_16, placed 0 (0, 0) card_210] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_25 : Valid inline_25 := by
  rw [eq_inline_25]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_16
  subst c
  exact placed_valid 0 (0, 0) valid_210

theorem eq_card_370 : card_370 = combine (4, 1) [placed 5 (0, 1) card_6, inline_25] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_370 : Valid card_370 := by
  rw [eq_card_370]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_6
  subst c
  exact valid_inline_25

theorem eq_inline_26 : inline_26 = combine (3, 2) [placed 4 (6, 1) card_0, placed 0 (0, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_26 : Valid inline_26 := by
  rw [eq_inline_26]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_0
  subst c
  exact placed_valid 0 (0, 1) valid_5

theorem eq_inline_27 : inline_27 = combine (2, 2) [placed 0 (1, 0) card_210, inline_26] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_27 : Valid inline_27 := by
  rw [eq_inline_27]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_210
  subst c
  exact valid_inline_26

theorem eq_inline_28 : inline_28 = combine (5, 1) [placed 5 (1, 1) card_6, inline_27] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_28 : Valid inline_28 := by
  rw [eq_inline_28]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 1) valid_6
  subst c
  exact valid_inline_27

theorem eq_card_371 : card_371 = combine (4, 1) [placed 1 (0, 1) card_6, placed 0 (1, 0) card_8, placed 0 (1, 0) card_370, inline_28] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_371 : Valid card_371 := by
  rw [eq_card_371]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_370
  subst c
  exact valid_inline_28

theorem eq_inline_29 : inline_29 = combine (4, 4) [placed 1 (0, 1) card_81, placed 0 (1, 0) card_351] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_29 : Valid inline_29 := by
  rw [eq_inline_29]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_81
  subst c
  exact placed_valid 0 (1, 0) valid_351

theorem eq_card_372 : card_372 = combine (4, 2) [placed 5 (0, 4) card_96, inline_29] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_372 : Valid card_372 := by
  rw [eq_card_372]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_96
  subst c
  exact valid_inline_29

theorem eq_card_373 : card_373 = combine (1, 4) [placed 5 (1, 4) card_5, placed 0 (0, 0) card_372] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_373 : Valid card_373 := by
  rw [eq_card_373]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_372

theorem eq_inline_30 : inline_30 = combine (4, 1) [placed 7 (4, 4) card_1, placed 0 (1, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_30 : Valid inline_30 := by
  rw [eq_inline_30]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_1
  subst c
  exact placed_valid 0 (1, 1) valid_5

theorem eq_card_374 : card_374 = combine (4, 2) [placed 0 (0, 1) card_4, inline_30] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_374 : Valid card_374 := by
  rw [eq_card_374]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_4
  subst c
  exact valid_inline_30

theorem eq_card_375 : card_375 = combine (3, 1) [placed 2 (0, 1) card_5, placed 0 (0, 0) card_374] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_375 : Valid card_375 := by
  rw [eq_card_375]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_374

theorem eq_inline_31 : inline_31 = combine (2, 4) [placed 5 (2, 4) card_2, placed 3 (4, 0) card_77] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_31 : Valid inline_31 := by
  rw [eq_inline_31]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_2
  subst c
  exact placed_valid 3 (4, 0) valid_77

theorem eq_card_376 : card_376 = combine (3, 0) [placed 2 (0, 1) card_5, inline_31] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_376 : Valid card_376 := by
  rw [eq_card_376]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_31

theorem eq_card_377 : card_377 = combine (1, 4) [placed 4 (1, 0) card_7, placed 0 (0, 0) card_9, placed 1 (0, 1) card_376] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_377 : Valid card_377 := by
  rw [eq_card_377]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_9
  subst c
  exact placed_valid 1 (0, 1) valid_376

theorem eq_inline_32 : inline_32 = combine (3, 3) [placed 0 (0, 2) card_5, placed 0 (2, 0) card_18] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_32 : Valid inline_32 := by
  rw [eq_inline_32]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_18

theorem eq_card_378 : card_378 = combine (3, 1) [placed 2 (0, 2) card_5, inline_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_378 : Valid card_378 := by
  rw [eq_card_378]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact valid_inline_32

theorem eq_card_379 : card_379 = combine (3, 2) [placed 5 (0, 2) card_21, placed 1 (0, 1) card_37, placed 0 (0, 0) card_378] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_379 : Valid card_379 := by
  rw [eq_card_379]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_37
  subst c
  exact placed_valid 0 (0, 0) valid_378

theorem eq_inline_33 : inline_33 = combine (3, 0) [placed 2 (0, 1) card_5, placed 1 (1, 0) card_379] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_33 : Valid inline_33 := by
  rw [eq_inline_33]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 1 (1, 0) valid_379

theorem eq_card_380 : card_380 = combine (3, 2) [placed 0 (0, 1) card_5, inline_33] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_380 : Valid card_380 := by
  rw [eq_card_380]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_33

theorem eq_inline_34 : inline_34 = combine (4, 1) [placed 5 (3, 4) card_0, placed 2 (1, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_34 : Valid inline_34 := by
  rw [eq_inline_34]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_0
  subst c
  exact placed_valid 2 (1, 1) valid_5

theorem eq_inline_35 : inline_35 = combine (4, 0) [placed 2 (0, 1) card_4, inline_34] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_35 : Valid inline_35 := by
  rw [eq_inline_35]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact valid_inline_34

theorem eq_card_381 : card_381 = combine (3, 1) [placed 0 (0, 1) card_5, inline_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_381 : Valid card_381 := by
  rw [eq_card_381]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_35

theorem eq_card_382 : card_382 = combine (1, 4) [placed 4 (1, 0) card_22, placed 3 (4, 1) card_381] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_382 : Valid card_382 := by
  rw [eq_card_382]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_22
  subst c
  exact placed_valid 3 (4, 1) valid_381

theorem eq_inline_36 : inline_36 = combine (3, 3) [placed 0 (0, 2) card_5, placed 2 (2, 5) card_219] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_36 : Valid inline_36 := by
  rw [eq_inline_36]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact placed_valid 2 (2, 5) valid_219

theorem eq_card_383 : card_383 = combine (3, 1) [placed 2 (0, 2) card_5, inline_36] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_383 : Valid card_383 := by
  rw [eq_card_383]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact valid_inline_36

theorem block05_valid : Valid card_320 ∧ Valid card_321 ∧ Valid card_322 ∧ Valid card_323 ∧ Valid card_324 ∧ Valid card_325 ∧ Valid card_326 ∧ Valid card_327 ∧ Valid card_328 ∧ Valid card_329 ∧ Valid card_330 ∧ Valid card_331 ∧ Valid card_332 ∧ Valid card_333 ∧ Valid card_334 ∧ Valid card_335 ∧ Valid card_336 ∧ Valid card_337 ∧ Valid card_338 ∧ Valid card_339 ∧ Valid card_340 ∧ Valid card_341 ∧ Valid card_342 ∧ Valid card_343 ∧ Valid card_344 ∧ Valid card_345 ∧ Valid card_346 ∧ Valid card_347 ∧ Valid card_348 ∧ Valid card_349 ∧ Valid card_350 ∧ Valid card_351 ∧ Valid card_352 ∧ Valid card_353 ∧ Valid card_354 ∧ Valid card_355 ∧ Valid card_356 ∧ Valid card_357 ∧ Valid card_358 ∧ Valid card_359 ∧ Valid card_360 ∧ Valid card_361 ∧ Valid card_362 ∧ Valid card_363 ∧ Valid card_364 ∧ Valid card_365 ∧ Valid card_366 ∧ Valid card_367 ∧ Valid card_368 ∧ Valid card_369 ∧ Valid card_370 ∧ Valid card_371 ∧ Valid card_372 ∧ Valid card_373 ∧ Valid card_374 ∧ Valid card_375 ∧ Valid card_376 ∧ Valid card_377 ∧ Valid card_378 ∧ Valid card_379 ∧ Valid card_380 ∧ Valid card_381 ∧ Valid card_382 ∧ Valid card_383 ∧ True :=
  ⟨valid_320, valid_321, valid_322, valid_323, valid_324, valid_325, valid_326, valid_327, valid_328, valid_329, valid_330, valid_331, valid_332, valid_333, valid_334, valid_335, valid_336, valid_337, valid_338, valid_339, valid_340, valid_341, valid_342, valid_343, valid_344, valid_345, valid_346, valid_347, valid_348, valid_349, valid_350, valid_351, valid_352, valid_353, valid_354, valid_355, valid_356, valid_357, valid_358, valid_359, valid_360, valid_361, valid_362, valid_363, valid_364, valid_365, valid_366, valid_367, valid_368, valid_369, valid_370, valid_371, valid_372, valid_373, valid_374, valid_375, valid_376, valid_377, valid_378, valid_379, valid_380, valid_381, valid_382, valid_383, True.intro⟩

end OAI.Snaky21.Certificate

theorem solution : Valid card_320 ∧ Valid card_321 ∧ Valid card_322 ∧ Valid card_323 ∧ Valid card_324 ∧ Valid card_325 ∧ Valid card_326 ∧ Valid card_327 ∧ Valid card_328 ∧ Valid card_329 ∧ Valid card_330 ∧ Valid card_331 ∧ Valid card_332 ∧ Valid card_333 ∧ Valid card_334 ∧ Valid card_335 ∧ Valid card_336 ∧ Valid card_337 ∧ Valid card_338 ∧ Valid card_339 ∧ Valid card_340 ∧ Valid card_341 ∧ Valid card_342 ∧ Valid card_343 ∧ Valid card_344 ∧ Valid card_345 ∧ Valid card_346 ∧ Valid card_347 ∧ Valid card_348 ∧ Valid card_349 ∧ Valid card_350 ∧ Valid card_351 ∧ Valid card_352 ∧ Valid card_353 ∧ Valid card_354 ∧ Valid card_355 ∧ Valid card_356 ∧ Valid card_357 ∧ Valid card_358 ∧ Valid card_359 ∧ Valid card_360 ∧ Valid card_361 ∧ Valid card_362 ∧ Valid card_363 ∧ Valid card_364 ∧ Valid card_365 ∧ Valid card_366 ∧ Valid card_367 ∧ Valid card_368 ∧ Valid card_369 ∧ Valid card_370 ∧ Valid card_371 ∧ Valid card_372 ∧ Valid card_373 ∧ Valid card_374 ∧ Valid card_375 ∧ Valid card_376 ∧ Valid card_377 ∧ Valid card_378 ∧ Valid card_379 ∧ Valid card_380 ∧ Valid card_381 ∧ Valid card_382 ∧ Valid card_383 ∧ True := block05_valid
