-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block04_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T10:27:02.231345+00:00
-- url     : https://prove2.me/submissions/24192cfe-5953-4729-ae0c-84f724197851

import Definitions.Def_Snaky21Data04
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
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
end OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_256 : card_256 = combine (3, 4) [placed 0 (0, 3) card_5, placed 0 (0, 0) card_255] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_256 : Valid card_256 := by
  rw [eq_card_256]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_255

theorem eq_card_257 : card_257 = combine (4, 3) [placed 1 (0, 3) card_7, placed 5 (0, 4) card_9, placed 0 (1, 0) card_256] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_257 : Valid card_257 := by
  rw [eq_card_257]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_256

theorem eq_card_258 : card_258 = combine (3, 3) [placed 0 (0, 2) card_8, placed 2 (0, 6) card_161, placed 2 (0, 6) card_162, placed 0 (0, 0) card_256] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_258 : Valid card_258 := by
  rw [eq_card_258]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_161
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_162
  subst c
  exact placed_valid 0 (0, 0) valid_256

theorem eq_card_259 : card_259 = combine (2, 4) [placed 0 (1, 1) card_15, placed 2 (0, 5) card_159] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_259 : Valid card_259 := by
  rw [eq_card_259]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_15
  subst c
  exact placed_valid 2 (0, 5) valid_159

theorem eq_card_260 : card_260 = combine (3, 0) [placed 2 (0, 1) card_5, placed 3 (4, 0) card_208] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_260 : Valid card_260 := by
  rw [eq_card_260]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 3 (4, 0) valid_208

theorem eq_card_261 : card_261 = combine (1, 3) [placed 1 (0, 0) card_3, placed 0 (0, 0) card_129] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_261 : Valid card_261 := by
  rw [eq_card_261]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_3
  subst c
  exact placed_valid 0 (0, 0) valid_129

theorem eq_card_262 : card_262 = combine (1, 1) [placed 0 (1, 0) card_15, placed 5 (0, 3) card_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_262 : Valid card_262 := by
  rw [eq_card_262]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_15
  subst c
  exact placed_valid 5 (0, 3) valid_66

theorem eq_card_263 : card_263 = combine (3, 4) [placed 0 (3, 0) card_7, placed 4 (4, 0) card_9, placed 3 (4, 1) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_263 : Valid card_263 := by
  rw [eq_card_263]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_9
  subst c
  exact placed_valid 3 (4, 1) valid_78

theorem eq_card_264 : card_264 = combine (1, 4) [placed 1 (0, 1) card_8, placed 5 (0, 4) card_201] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_264 : Valid card_264 := by
  rw [eq_card_264]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  subst c
  exact placed_valid 5 (0, 4) valid_201

theorem eq_card_265 : card_265 = combine (1, 4) [placed 7 (1, 4) card_4, placed 1 (0, 1) card_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_265 : Valid card_265 := by
  rw [eq_card_265]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 1 (0, 1) valid_93

theorem eq_card_266 : card_266 = combine (0, 6) [placed 0 (0, 2) card_6, placed 0 (0, 3) card_16, placed 2 (0, 7) card_113] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_266 : Valid card_266 := by
  rw [eq_card_266]
  apply combination_rule (0, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_16
  subst c
  exact placed_valid 2 (0, 7) valid_113

theorem eq_card_267 : card_267 = combine (2, 5) [placed 1 (1, 2) card_8, placed 0 (1, 2) card_17, placed 0 (1, 0) card_75, placed 5 (0, 6) card_179, placed 4 (2, 0) card_266] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_267 : Valid card_267 := by
  rw [eq_card_267]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_75
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_179
  subst c
  exact placed_valid 4 (2, 0) valid_266

theorem eq_card_268 : card_268 = combine (1, 4) [placed 6 (1, 6) card_7, placed 1 (0, 2) card_8, placed 6 (2, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_268 : Valid card_268 := by
  rw [eq_card_268]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  subst c
  exact placed_valid 6 (2, 6) valid_9

theorem eq_card_269 : card_269 = combine (1, 5) [placed 2 (1, 6) card_7, placed 4 (1, 2) card_21] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_269 : Valid card_269 := by
  rw [eq_card_269]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_7
  subst c
  exact placed_valid 4 (1, 2) valid_21

theorem eq_card_270 : card_270 = combine (4, 2) [placed 7 (4, 2) card_70, placed 1 (0, 1) card_106, placed 1 (1, 0) card_122, placed 1 (0, 1) card_269] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_270 : Valid card_270 := by
  rw [eq_card_270]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 2) valid_70
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_106
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_122
  subst c
  exact placed_valid 1 (0, 1) valid_269

theorem eq_card_271 : card_271 = combine (2, 3) [placed 2 (0, 3) card_5, placed 4 (3, 0) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_271 : Valid card_271 := by
  rw [eq_card_271]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_52

theorem eq_card_272 : card_272 = combine (2, 1) [placed 0 (0, 1) card_5, placed 0 (2, 0) card_39] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_272 : Valid card_272 := by
  rw [eq_card_272]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_39

theorem eq_card_273 : card_273 = combine (3, 3) [placed 0 (0, 3) card_2, placed 0 (3, 0) card_206] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_273 : Valid card_273 := by
  rw [eq_card_273]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_2
  subst c
  exact placed_valid 0 (3, 0) valid_206

theorem eq_card_274 : card_274 = combine (3, 2) [placed 0 (2, 0) card_13, placed 5 (0, 3) card_44, placed 3 (4, 2) card_83] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_274 : Valid card_274 := by
  rw [eq_card_274]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_44
  subst c
  exact placed_valid 3 (4, 2) valid_83

theorem eq_card_275 : card_275 = combine (4, 2) [placed 5 (1, 2) card_16, placed 0 (1, 1) card_24, placed 4 (5, 0) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_275 : Valid card_275 := by
  rw [eq_card_275]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 2) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_24
  subst c
  exact placed_valid 4 (5, 0) valid_179

theorem eq_card_276 : card_276 = combine (2, 4) [placed 6 (2, 6) card_44, placed 6 (2, 6) card_52, placed 5 (0, 6) card_155, placed 1 (0, 2) card_275] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_276 : Valid card_276 := by
  rw [eq_card_276]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_155
  subst c
  exact placed_valid 1 (0, 2) valid_275

theorem eq_card_277 : card_277 = combine (1, 3) [placed 4 (5, 2) card_0, placed 4 (4, 0) card_69] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_277 : Valid card_277 := by
  rw [eq_card_277]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_0
  subst c
  exact placed_valid 4 (4, 0) valid_69

theorem eq_card_278 : card_278 = combine (4, 2) [placed 5 (0, 2) card_6, placed 0 (0, 0) card_277] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_278 : Valid card_278 := by
  rw [eq_card_278]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_6
  subst c
  exact placed_valid 0 (0, 0) valid_277

theorem eq_card_279 : card_279 = combine (4, 3) [placed 5 (0, 3) card_6, placed 0 (1, 0) card_141] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_279 : Valid card_279 := by
  rw [eq_card_279]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_6
  subst c
  exact placed_valid 0 (1, 0) valid_141

theorem eq_card_280 : card_280 = combine (1, 2) [placed 7 (1, 4) card_3, placed 0 (1, 2) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_280 : Valid card_280 := by
  rw [eq_card_280]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_3
  subst c
  exact placed_valid 0 (1, 2) valid_6

theorem eq_card_281 : card_281 = combine (1, 3) [placed 4 (4, 3) card_2, placed 1 (0, 0) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_281 : Valid card_281 := by
  rw [eq_card_281]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_2
  subst c
  exact placed_valid 1 (0, 0) valid_3

theorem eq_card_282 : card_282 = combine (3, 2) [placed 5 (0, 3) card_20, placed 1 (0, 2) card_29, placed 0 (0, 0) card_92] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_282 : Valid card_282 := by
  rw [eq_card_282]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_29
  subst c
  exact placed_valid 0 (0, 0) valid_92

theorem eq_card_283 : card_283 = combine (2, 2) [placed 0 (0, 2) card_1, placed 0 (2, 0) card_282] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_283 : Valid card_283 := by
  rw [eq_card_283]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_1
  subst c
  exact placed_valid 0 (2, 0) valid_282

theorem eq_card_284 : card_284 = combine (1, 3) [placed 1 (0, 3) card_8, placed 0 (0, 3) card_17, placed 2 (0, 7) card_19, placed 0 (0, 1) card_75] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_284 : Valid card_284 := by
  rw [eq_card_284]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_19
  subst c
  exact placed_valid 0 (0, 1) valid_75

theorem eq_card_285 : card_285 = combine (4, 3) [placed 1 (0, 3) card_6, placed 0 (1, 2) card_26, placed 0 (1, 0) card_117] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_285 : Valid card_285 := by
  rw [eq_card_285]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_26
  subst c
  exact placed_valid 0 (1, 0) valid_117

theorem eq_card_286 : card_286 = combine (4, 2) [placed 7 (4, 4) card_35, placed 3 (6, 1) card_253] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_286 : Valid card_286 := by
  rw [eq_card_286]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_35
  subst c
  exact placed_valid 3 (6, 1) valid_253

theorem eq_card_287 : card_287 = combine (1, 6) [placed 6 (1, 6) card_169, placed 3 (5, 2) card_230] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_287 : Valid card_287 := by
  rw [eq_card_287]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_169
  subst c
  exact placed_valid 3 (5, 2) valid_230

theorem eq_card_288 : card_288 = combine (1, 5) [placed 5 (0, 5) card_54, placed 0 (0, 0) card_68] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_288 : Valid card_288 := by
  rw [eq_card_288]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_54
  subst c
  exact placed_valid 0 (0, 0) valid_68

theorem eq_card_289 : card_289 = combine (1, 2) [placed 0 (0, 0) card_22, placed 2 (0, 5) card_28, placed 6 (2, 5) card_126] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_289 : Valid card_289 := by
  rw [eq_card_289]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_28
  subst c
  exact placed_valid 6 (2, 5) valid_126

theorem eq_card_290 : card_290 = combine (2, 1) [placed 4 (4, 1) card_5, placed 0 (0, 0) card_203] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_290 : Valid card_290 := by
  rw [eq_card_290]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_203

theorem eq_card_291 : card_291 = combine (3, 4) [placed 4 (3, 0) card_7, placed 3 (4, 1) card_25] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_291 : Valid card_291 := by
  rw [eq_card_291]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_7
  subst c
  exact placed_valid 3 (4, 1) valid_25

theorem eq_card_292 : card_292 = combine (4, 3) [placed 1 (0, 3) card_6, placed 1 (0, 2) card_19, placed 0 (0, 0) card_214] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_292 : Valid card_292 := by
  rw [eq_card_292]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_19
  subst c
  exact placed_valid 0 (0, 0) valid_214

theorem eq_card_293 : card_293 = combine (4, 3) [placed 1 (1, 2) card_17, placed 4 (4, 0) card_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_293 : Valid card_293 := by
  rw [eq_card_293]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_17
  subst c
  exact placed_valid 4 (4, 0) valid_56

theorem eq_card_294 : card_294 = combine (3, 3) [placed 1 (0, 2) card_10, placed 1 (0, 2) card_48, placed 5 (0, 6) card_165] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_294 : Valid card_294 := by
  rw [eq_card_294]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_48
  subst c
  exact placed_valid 5 (0, 6) valid_165

theorem eq_card_295 : card_295 = combine (3, 1) [placed 3 (5, 1) card_34, placed 3 (6, 0) card_180] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_295 : Valid card_295 := by
  rw [eq_card_295]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_34
  subst c
  exact placed_valid 3 (6, 0) valid_180

theorem eq_card_296 : card_296 = combine (2, 3) [placed 7 (2, 5) card_0, placed 5 (0, 5) card_132] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_296 : Valid card_296 := by
  rw [eq_card_296]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 5) valid_0
  subst c
  exact placed_valid 5 (0, 5) valid_132

theorem eq_card_297 : card_297 = combine (5, 3) [placed 7 (6, 4) card_9, placed 0 (1, 0) card_142, placed 2 (2, 6) card_162] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_297 : Valid card_297 := by
  rw [eq_card_297]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_142
  subst c
  exact placed_valid 2 (2, 6) valid_162

theorem eq_card_298 : card_298 = combine (5, 3) [placed 7 (6, 3) card_7, placed 0 (1, 0) card_142, placed 2 (2, 6) card_161] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_298 : Valid card_298 := by
  rw [eq_card_298]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_142
  subst c
  exact placed_valid 2 (2, 6) valid_161

theorem eq_card_299 : card_299 = combine (3, 5) [placed 2 (2, 7) card_12, placed 0 (0, 2) card_165, placed 4 (4, 2) card_264] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_299 : Valid card_299 := by
  rw [eq_card_299]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_165
  subst c
  exact placed_valid 4 (4, 2) valid_264

theorem eq_card_300 : card_300 = combine (2, 5) [placed 6 (2, 6) card_44, placed 6 (2, 6) card_52, placed 0 (1, 1) card_128, placed 5 (0, 6) card_155] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_300 : Valid card_300 := by
  rw [eq_card_300]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_128
  subst c
  exact placed_valid 5 (0, 6) valid_155

theorem eq_card_301 : card_301 = combine (3, 3) [placed 5 (0, 3) card_23, placed 0 (0, 0) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_301 : Valid card_301 := by
  rw [eq_card_301]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_23
  subst c
  exact placed_valid 0 (0, 0) valid_55

theorem eq_card_302 : card_302 = combine (5, 3) [placed 7 (5, 3) card_6, placed 2 (1, 6) card_214] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_302 : Valid card_302 := by
  rw [eq_card_302]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 3) valid_6
  subst c
  exact placed_valid 2 (1, 6) valid_214

theorem eq_card_303 : card_303 = combine (3, 4) [placed 2 (1, 6) card_55, placed 5 (0, 4) card_234] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_303 : Valid card_303 := by
  rw [eq_card_303]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_55
  subst c
  exact placed_valid 5 (0, 4) valid_234

theorem eq_card_304 : card_304 = combine (1, 4) [placed 4 (1, 1) card_7, placed 1 (0, 2) card_8, placed 6 (2, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_304 : Valid card_304 := by
  rw [eq_card_304]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  subst c
  exact placed_valid 6 (2, 6) valid_9

theorem eq_card_305 : card_305 = combine (1, 3) [placed 7 (1, 4) card_5, placed 2 (0, 5) card_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_305 : Valid card_305 := by
  rw [eq_card_305]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 2 (0, 5) valid_124

theorem eq_card_306 : card_306 = combine (4, 1) [placed 4 (4, 1) card_18, placed 7 (4, 4) card_207] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_306 : Valid card_306 := by
  rw [eq_card_306]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_18
  subst c
  exact placed_valid 7 (4, 4) valid_207

theorem eq_card_307 : card_307 = combine (4, 2) [placed 6 (4, 2) card_5, placed 0 (1, 0) card_131] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_307 : Valid card_307 := by
  rw [eq_card_307]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_131

theorem eq_card_308 : card_308 = combine (1, 5) [placed 6 (1, 6) card_44, placed 6 (1, 6) card_52, placed 0 (0, 2) card_63, placed 6 (1, 6) card_158] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_308 : Valid card_308 := by
  rw [eq_card_308]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_63
  subst c
  exact placed_valid 6 (1, 6) valid_158

theorem eq_card_309 : card_309 = combine (4, 3) [placed 1 (0, 2) card_19, placed 5 (0, 4) card_19, placed 4 (4, 0) card_115] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_309 : Valid card_309 := by
  rw [eq_card_309]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_19
  subst c
  exact placed_valid 4 (4, 0) valid_115

theorem eq_card_310 : card_310 = combine (1, 3) [placed 7 (1, 4) card_5, placed 0 (0, 1) card_76] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_310 : Valid card_310 := by
  rw [eq_card_310]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_76

theorem eq_inline_0 : inline_0 = combine (4, 1) [placed 2 (1, 1) card_5, placed 1 (0, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_0 : Valid inline_0 := by
  rw [eq_inline_0]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 1) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_6

theorem eq_card_311 : card_311 = combine (3, 1) [placed 2 (0, 1) card_4, inline_0] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_311 : Valid card_311 := by
  rw [eq_card_311]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact valid_inline_0

theorem eq_card_312 : card_312 = combine (2, 1) [placed 5 (1, 4) card_5, placed 2 (0, 2) card_311] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_312 : Valid card_312 := by
  rw [eq_card_312]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 2 (0, 2) valid_311

theorem eq_card_313 : card_313 = combine (3, 0) [placed 2 (0, 1) card_5, placed 3 (4, 0) card_312] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_313 : Valid card_313 := by
  rw [eq_card_313]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 3 (4, 0) valid_312

theorem eq_inline_1 : inline_1 = combine (3, 0) [placed 2 (0, 1) card_5, placed 1 (1, 0) card_20] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_1 : Valid inline_1 := by
  rw [eq_inline_1]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 1 (1, 0) valid_20

theorem eq_card_314 : card_314 = combine (4, 1) [placed 5 (0, 1) card_6, placed 0 (1, 0) card_8, placed 1 (1, 0) card_17, inline_1] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_314 : Valid card_314 := by
  rw [eq_card_314]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_17
  subst c
  exact valid_inline_1

theorem eq_card_315 : card_315 = combine (1, 4) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_315 : Valid card_315 := by
  rw [eq_card_315]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_314

theorem eq_card_316 : card_316 = combine (1, 2) [placed 5 (0, 5) card_8, placed 1 (0, 2) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_316 : Valid card_316 := by
  rw [eq_card_316]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_8
  subst c
  exact placed_valid 1 (0, 2) valid_314

theorem eq_card_317 : card_317 = combine (3, 5) [placed 1 (0, 4) card_44, placed 4 (4, 2) card_60, placed 0 (2, 0) card_316] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_317 : Valid card_317 := by
  rw [eq_card_317]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_60
  subst c
  exact placed_valid 0 (2, 0) valid_316

theorem eq_card_318 : card_318 = combine (1, 3) [placed 2 (0, 6) card_10, placed 4 (1, 2) card_52, placed 6 (1, 6) card_52, placed 0 (0, 2) card_315] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_318 : Valid card_318 := by
  rw [eq_card_318]
  apply combination_rule (1, 3) _ (by simp)
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

theorem eq_card_319 : card_319 = combine (3, 4) [placed 5 (0, 5) card_52, placed 0 (2, 0) card_318] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_319 : Valid card_319 := by
  rw [eq_card_319]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_52
  subst c
  exact placed_valid 0 (2, 0) valid_318

theorem block04_valid : Valid card_256 ∧ Valid card_257 ∧ Valid card_258 ∧ Valid card_259 ∧ Valid card_260 ∧ Valid card_261 ∧ Valid card_262 ∧ Valid card_263 ∧ Valid card_264 ∧ Valid card_265 ∧ Valid card_266 ∧ Valid card_267 ∧ Valid card_268 ∧ Valid card_269 ∧ Valid card_270 ∧ Valid card_271 ∧ Valid card_272 ∧ Valid card_273 ∧ Valid card_274 ∧ Valid card_275 ∧ Valid card_276 ∧ Valid card_277 ∧ Valid card_278 ∧ Valid card_279 ∧ Valid card_280 ∧ Valid card_281 ∧ Valid card_282 ∧ Valid card_283 ∧ Valid card_284 ∧ Valid card_285 ∧ Valid card_286 ∧ Valid card_287 ∧ Valid card_288 ∧ Valid card_289 ∧ Valid card_290 ∧ Valid card_291 ∧ Valid card_292 ∧ Valid card_293 ∧ Valid card_294 ∧ Valid card_295 ∧ Valid card_296 ∧ Valid card_297 ∧ Valid card_298 ∧ Valid card_299 ∧ Valid card_300 ∧ Valid card_301 ∧ Valid card_302 ∧ Valid card_303 ∧ Valid card_304 ∧ Valid card_305 ∧ Valid card_306 ∧ Valid card_307 ∧ Valid card_308 ∧ Valid card_309 ∧ Valid card_310 ∧ Valid card_311 ∧ Valid card_312 ∧ Valid card_313 ∧ Valid card_314 ∧ Valid card_315 ∧ Valid card_316 ∧ Valid card_317 ∧ Valid card_318 ∧ Valid card_319 ∧ True :=
  ⟨valid_256, valid_257, valid_258, valid_259, valid_260, valid_261, valid_262, valid_263, valid_264, valid_265, valid_266, valid_267, valid_268, valid_269, valid_270, valid_271, valid_272, valid_273, valid_274, valid_275, valid_276, valid_277, valid_278, valid_279, valid_280, valid_281, valid_282, valid_283, valid_284, valid_285, valid_286, valid_287, valid_288, valid_289, valid_290, valid_291, valid_292, valid_293, valid_294, valid_295, valid_296, valid_297, valid_298, valid_299, valid_300, valid_301, valid_302, valid_303, valid_304, valid_305, valid_306, valid_307, valid_308, valid_309, valid_310, valid_311, valid_312, valid_313, valid_314, valid_315, valid_316, valid_317, valid_318, valid_319, True.intro⟩

end OAI.Snaky21.Certificate

theorem solution : Valid card_256 ∧ Valid card_257 ∧ Valid card_258 ∧ Valid card_259 ∧ Valid card_260 ∧ Valid card_261 ∧ Valid card_262 ∧ Valid card_263 ∧ Valid card_264 ∧ Valid card_265 ∧ Valid card_266 ∧ Valid card_267 ∧ Valid card_268 ∧ Valid card_269 ∧ Valid card_270 ∧ Valid card_271 ∧ Valid card_272 ∧ Valid card_273 ∧ Valid card_274 ∧ Valid card_275 ∧ Valid card_276 ∧ Valid card_277 ∧ Valid card_278 ∧ Valid card_279 ∧ Valid card_280 ∧ Valid card_281 ∧ Valid card_282 ∧ Valid card_283 ∧ Valid card_284 ∧ Valid card_285 ∧ Valid card_286 ∧ Valid card_287 ∧ Valid card_288 ∧ Valid card_289 ∧ Valid card_290 ∧ Valid card_291 ∧ Valid card_292 ∧ Valid card_293 ∧ Valid card_294 ∧ Valid card_295 ∧ Valid card_296 ∧ Valid card_297 ∧ Valid card_298 ∧ Valid card_299 ∧ Valid card_300 ∧ Valid card_301 ∧ Valid card_302 ∧ Valid card_303 ∧ Valid card_304 ∧ Valid card_305 ∧ Valid card_306 ∧ Valid card_307 ∧ Valid card_308 ∧ Valid card_309 ∧ Valid card_310 ∧ Valid card_311 ∧ Valid card_312 ∧ Valid card_313 ∧ Valid card_314 ∧ Valid card_315 ∧ Valid card_316 ∧ Valid card_317 ∧ Valid card_318 ∧ Valid card_319 ∧ True := block04_valid
