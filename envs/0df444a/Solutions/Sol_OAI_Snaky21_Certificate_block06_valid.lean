-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block06_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T10:49:55.765985+00:00
-- url     : https://prove2.me/submissions/1ef5629f-06f7-4338-bfdc-d58740e0ed9e

import Definitions.Def_Snaky21Data06
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
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
end OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_384 : card_384 = combine (3, 3) [placed 1 (2, 1) card_8, placed 7 (5, 4) card_383] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_384 : Valid card_384 := by
  rw [eq_card_384]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_8
  subst c
  exact placed_valid 7 (5, 4) valid_383

theorem eq_card_385 : card_385 = combine (3, 3) [placed 1 (0, 1) card_115, placed 7 (5, 4) card_383] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_385 : Valid card_385 := by
  rw [eq_card_385]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_115
  subst c
  exact placed_valid 7 (5, 4) valid_383

theorem eq_inline_37 : inline_37 = combine (3, 4) [placed 3 (3, 1) card_5, placed 4 (3, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_37 : Valid inline_37 := by
  rw [eq_inline_37]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 1) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_11

theorem eq_inline_38 : inline_38 = combine (3, 3) [placed 0 (0, 2) card_5, inline_37] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_38 : Valid inline_38 := by
  rw [eq_inline_38]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact valid_inline_37

theorem eq_card_386 : card_386 = combine (3, 1) [placed 2 (0, 2) card_5, inline_38] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_386 : Valid card_386 := by
  rw [eq_card_386]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact valid_inline_38

theorem eq_card_387 : card_387 = combine (4, 2) [placed 1 (0, 1) card_200, placed 1 (1, 0) card_376, placed 1 (0, 0) card_386] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_387 : Valid card_387 := by
  rw [eq_card_387]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_200
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_376
  subst c
  exact placed_valid 1 (0, 0) valid_386

theorem eq_card_388 : card_388 = combine (2, 4) [placed 4 (2, 0) card_11, placed 0 (0, 1) card_387] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_388 : Valid card_388 := by
  rw [eq_card_388]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_11
  subst c
  exact placed_valid 0 (0, 1) valid_387

theorem eq_inline_39 : inline_39 = combine (1, 3) [placed 1 (0, 0) card_5, placed 0 (0, 1) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_39 : Valid inline_39 := by
  rw [eq_inline_39]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_23

theorem eq_card_389 : card_389 = combine (0, 4) [placed 0 (0, 0) card_6, placed 0 (0, 1) card_21, placed 0 (0, 1) card_27, inline_39] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_389 : Valid card_389 := by
  rw [eq_card_389]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_27
  subst c
  exact valid_inline_39

theorem eq_card_390 : card_390 = combine (1, 7) [placed 4 (1, 3) card_11, placed 0 (0, 4) card_17, placed 6 (1, 7) card_389] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_390 : Valid card_390 := by
  rw [eq_card_390]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 4) valid_17
  subst c
  exact placed_valid 6 (1, 7) valid_389

theorem eq_inline_40 : inline_40 = combine (3, 1) [placed 4 (4, 1) card_0, placed 2 (2, 4) card_36] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_40 : Valid inline_40 := by
  rw [eq_inline_40]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 2 (2, 4) valid_36

theorem eq_inline_41 : inline_41 = combine (2, 1) [placed 5 (1, 4) card_5, inline_40] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_41 : Valid inline_41 := by
  rw [eq_inline_41]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_40

theorem eq_card_391 : card_391 = combine (2, 4) [placed 1 (1, 1) card_5, inline_41] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_391 : Valid card_391 := by
  rw [eq_card_391]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_41

theorem eq_card_392 : card_392 = combine (3, 3) [placed 6 (4, 3) card_0, placed 0 (0, 0) card_391] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_392 : Valid card_392 := by
  rw [eq_card_392]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_391

theorem eq_card_393 : card_393 = combine (1, 4) [placed 0 (1, 0) card_11, placed 0 (0, 1) card_20, placed 2 (0, 5) card_391] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_393 : Valid card_393 := by
  rw [eq_card_393]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_20
  subst c
  exact placed_valid 2 (0, 5) valid_391

theorem eq_card_394 : card_394 = combine (1, 4) [placed 0 (0, 1) card_17, placed 0 (0, 0) card_241, placed 0 (0, 0) card_392] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_394 : Valid card_394 := by
  rw [eq_card_394]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_241
  subst c
  exact placed_valid 0 (0, 0) valid_392

theorem eq_inline_42 : inline_42 = combine (3, 1) [placed 2 (0, 2) card_5, placed 0 (1, 0) card_217] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_42 : Valid inline_42 := by
  rw [eq_inline_42]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_217

theorem eq_card_395 : card_395 = combine (3, 3) [placed 0 (0, 2) card_5, inline_42] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_395 : Valid card_395 := by
  rw [eq_card_395]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact valid_inline_42

theorem eq_card_396 : card_396 = combine (2, 6) [placed 4 (2, 2) card_7, placed 4 (3, 2) card_9, placed 5 (0, 6) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_396 : Valid card_396 := by
  rw [eq_card_396]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_9
  subst c
  exact placed_valid 5 (0, 6) valid_395

theorem eq_card_397 : card_397 = combine (3, 3) [placed 0 (0, 2) card_8, placed 0 (0, 0) card_161, placed 0 (0, 0) card_162, placed 0 (0, 1) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_397 : Valid card_397 := by
  rw [eq_card_397]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_161
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_162
  subst c
  exact placed_valid 0 (0, 1) valid_395

theorem eq_card_398 : card_398 = combine (3, 3) [placed 0 (0, 0) card_171, placed 0 (0, 2) card_197, placed 2 (0, 4) card_197, placed 0 (0, 0) card_285, placed 0 (0, 1) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_398 : Valid card_398 := by
  rw [eq_card_398]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_171
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_285
  subst c
  exact placed_valid 0 (0, 1) valid_395

theorem eq_card_399 : card_399 = combine (2, 5) [placed 0 (1, 1) card_12, placed 0 (0, 1) card_135, placed 1 (0, 2) card_181, placed 0 (0, 0) card_396, placed 2 (0, 8) card_396] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_399 : Valid card_399 := by
  rw [eq_card_399]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_396
  subst c
  exact placed_valid 2 (0, 8) valid_396

theorem eq_card_400 : card_400 = combine (3, 2) [placed 6 (4, 2) card_5, placed 0 (1, 0) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_400 : Valid card_400 := by
  rw [eq_card_400]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_395

theorem eq_card_401 : card_401 = combine (2, 4) [placed 6 (4, 4) card_3, placed 2 (2, 7) card_397] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_401 : Valid card_401 := by
  rw [eq_card_401]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_3
  subst c
  exact placed_valid 2 (2, 7) valid_397

theorem eq_inline_43 : inline_43 = combine (2, 4) [placed 3 (3, 0) card_0, placed 1 (1, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_43 : Valid inline_43 := by
  rw [eq_inline_43]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 0) valid_0
  subst c
  exact placed_valid 1 (1, 1) valid_5

theorem eq_card_402 : card_402 = combine (3, 1) [placed 5 (0, 4) card_38, inline_43] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_402 : Valid card_402 := by
  rw [eq_card_402]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_38
  subst c
  exact valid_inline_43

theorem eq_inline_44 : inline_44 = combine (2, 5) [placed 3 (3, 1) card_4, placed 3 (4, 2) card_381] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_44 : Valid inline_44 := by
  rw [eq_inline_44]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 1) valid_4
  subst c
  exact placed_valid 3 (4, 2) valid_381

theorem eq_card_403 : card_403 = combine (1, 5) [placed 0 (0, 0) card_86, inline_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_403 : Valid card_403 := by
  rw [eq_card_403]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_86
  subst c
  exact valid_inline_44

theorem eq_inline_45 : inline_45 = combine (3, 1) [placed 4 (4, 1) card_0, placed 0 (0, 0) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_45 : Valid inline_45 := by
  rw [eq_inline_45]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_354

theorem eq_inline_46 : inline_46 = combine (2, 1) [placed 5 (1, 4) card_5, inline_45] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_46 : Valid inline_46 := by
  rw [eq_inline_46]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_45

theorem eq_card_404 : card_404 = combine (2, 4) [placed 1 (1, 1) card_5, inline_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_404 : Valid card_404 := by
  rw [eq_card_404]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_46

theorem eq_card_405 : card_405 = combine (1, 4) [placed 7 (1, 5) card_0, placed 0 (0, 0) card_404] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_405 : Valid card_405 := by
  rw [eq_card_405]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_404

theorem eq_card_406 : card_406 = combine (1, 4) [placed 0 (0, 0) card_199, placed 2 (0, 6) card_199, placed 0 (0, 1) card_405, placed 2 (0, 5) card_405] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_406 : Valid card_406 := by
  rw [eq_card_406]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_199
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_199
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_405
  subst c
  exact placed_valid 2 (0, 5) valid_405

theorem eq_inline_47 : inline_47 = combine (0, 4) [placed 3 (1, 1) card_5, placed 2 (0, 5) card_404] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_47 : Valid inline_47 := by
  rw [eq_inline_47]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact placed_valid 2 (0, 5) valid_404

theorem eq_card_407 : card_407 = combine (1, 4) [placed 0 (1, 0) card_7, placed 1 (0, 1) card_8, placed 4 (2, 0) card_9, inline_47] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_407 : Valid card_407 := by
  rw [eq_card_407]
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
  exact valid_inline_47

theorem eq_card_408 : card_408 = combine (1, 5) [placed 6 (1, 6) card_44, placed 0 (0, 1) card_127, placed 2 (0, 6) card_407] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_408 : Valid card_408 := by
  rw [eq_card_408]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_127
  subst c
  exact placed_valid 2 (0, 6) valid_407

theorem eq_card_409 : card_409 = combine (1, 4) [placed 6 (1, 6) card_44, placed 0 (0, 1) card_127, placed 2 (0, 6) card_407] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_409 : Valid card_409 := by
  rw [eq_card_409]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_127
  subst c
  exact placed_valid 2 (0, 6) valid_407

theorem eq_card_410 : card_410 = combine (1, 5) [placed 0 (0, 2) card_10, placed 4 (2, 1) card_12, placed 2 (0, 7) card_12, placed 2 (0, 6) card_407] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_410 : Valid card_410 := by
  rw [eq_card_410]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_12
  subst c
  exact placed_valid 2 (0, 6) valid_407

theorem eq_card_411 : card_411 = combine (1, 5) [placed 6 (1, 6) card_15, placed 2 (0, 7) card_65, placed 2 (0, 6) card_407] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_411 : Valid card_411 := by
  rw [eq_card_411]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_65
  subst c
  exact placed_valid 2 (0, 6) valid_407

theorem eq_inline_48 : inline_48 = combine (3, 1) [placed 4 (4, 1) card_0, placed 0 (0, 0) card_358] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_48 : Valid inline_48 := by
  rw [eq_inline_48]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_358

theorem eq_card_412 : card_412 = combine (2, 1) [placed 5 (1, 4) card_5, inline_48] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_412 : Valid card_412 := by
  rw [eq_card_412]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_48

theorem eq_inline_49 : inline_49 = combine (2, 3) [placed 7 (2, 4) card_5, placed 1 (0, 1) card_45] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_49 : Valid inline_49 := by
  rw [eq_inline_49]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_45

theorem eq_card_413 : card_413 = combine (2, 4) [placed 1 (1, 1) card_5, inline_49] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_413 : Valid card_413 := by
  rw [eq_card_413]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_49

theorem eq_card_414 : card_414 = combine (1, 4) [placed 5 (1, 5) card_0, placed 0 (0, 0) card_413] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_414 : Valid card_414 := by
  rw [eq_card_414]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_413

theorem eq_card_415 : card_415 = combine (3, 2) [placed 2 (0, 2) card_2, placed 4 (5, 0) card_414] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_415 : Valid card_415 := by
  rw [eq_card_415]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_2
  subst c
  exact placed_valid 4 (5, 0) valid_414

theorem eq_inline_50 : inline_50 = combine (3, 1) [placed 2 (0, 2) card_5, placed 2 (0, 5) card_239] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_50 : Valid inline_50 := by
  rw [eq_inline_50]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact placed_valid 2 (0, 5) valid_239

theorem eq_card_416 : card_416 = combine (3, 3) [placed 0 (0, 2) card_5, inline_50] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_416 : Valid card_416 := by
  rw [eq_card_416]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact valid_inline_50

theorem eq_card_417 : card_417 = combine (3, 2) [placed 4 (4, 2) card_0, placed 0 (0, 0) card_416] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_417 : Valid card_417 := by
  rw [eq_card_417]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_416

theorem eq_inline_51 : inline_51 = combine (2, 2) [placed 0 (0, 2) card_5, placed 4 (3, 0) card_29] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_51 : Valid inline_51 := by
  rw [eq_inline_51]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_29

theorem eq_inline_52 : inline_52 = combine (3, 3) [placed 1 (2, 0) card_8, placed 3 (4, 0) card_25, placed 0 (2, 0) card_41, inline_51] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_52 : Valid inline_52 := by
  rw [eq_inline_52]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 0) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 0) valid_25
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_41
  subst c
  exact valid_inline_51

theorem eq_inline_53 : inline_53 = combine (3, 2) [placed 0 (0, 1) card_5, inline_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_53 : Valid inline_53 := by
  rw [eq_inline_53]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_52

theorem eq_card_418 : card_418 = combine (3, 0) [placed 2 (0, 1) card_5, inline_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_418 : Valid card_418 := by
  rw [eq_card_418]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_53

theorem eq_card_419 : card_419 = combine (2, 1) [placed 5 (1, 4) card_5, placed 1 (0, 1) card_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_419 : Valid card_419 := by
  rw [eq_card_419]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_418

theorem eq_card_420 : card_420 = combine (3, 1) [placed 4 (4, 1) card_0, placed 0 (0, 0) card_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_420 : Valid card_420 := by
  rw [eq_card_420]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_418

theorem eq_card_421 : card_421 = combine (1, 4) [placed 1 (0, 1) card_8, placed 0 (1, 0) card_11, placed 0 (0, 0) card_419] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_421 : Valid card_421 := by
  rw [eq_card_421]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_11
  subst c
  exact placed_valid 0 (0, 0) valid_419

theorem eq_inline_54 : inline_54 = combine (4, 2) [placed 0 (1, 0) card_69, placed 3 (5, 1) card_413] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_54 : Valid inline_54 := by
  rw [eq_inline_54]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_69
  subst c
  exact placed_valid 3 (5, 1) valid_413

theorem eq_card_422 : card_422 = combine (2, 2) [placed 0 (0, 2) card_0, inline_54] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_422 : Valid card_422 := by
  rw [eq_card_422]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_0
  subst c
  exact valid_inline_54

theorem eq_inline_55 : inline_55 = combine (1, 2) [placed 6 (4, 3) card_5, placed 0 (0, 0) card_244] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_55 : Valid inline_55 := by
  rw [eq_inline_55]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_244

theorem eq_card_423 : card_423 = combine (2, 3) [placed 2 (1, 5) card_383, inline_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_423 : Valid card_423 := by
  rw [eq_card_423]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_383
  subst c
  exact valid_inline_55

theorem eq_inline_56 : inline_56 = combine (4, 2) [placed 2 (0, 3) card_2, placed 0 (3, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_56 : Valid inline_56 := by
  rw [eq_inline_56]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_2
  subst c
  exact placed_valid 0 (3, 0) valid_11

theorem eq_card_424 : card_424 = combine (3, 4) [placed 0 (3, 0) card_7, placed 3 (4, 1) card_25, inline_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_424 : Valid card_424 := by
  rw [eq_card_424]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 1) valid_25
  subst c
  exact valid_inline_56

theorem eq_inline_57 : inline_57 = combine (3, 2) [placed 0 (0, 2) card_2, placed 0 (3, 0) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_57 : Valid inline_57 := by
  rw [eq_inline_57]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_2
  subst c
  exact placed_valid 0 (3, 0) valid_44

theorem eq_card_425 : card_425 = combine (4, 3) [placed 6 (4, 3) card_2, inline_57] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_425 : Valid card_425 := by
  rw [eq_card_425]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_2
  subst c
  exact valid_inline_57

theorem eq_inline_58 : inline_58 = combine (3, 3) [placed 6 (5, 3) card_0, placed 4 (4, 1) card_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_58 : Valid inline_58 := by
  rw [eq_inline_58]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 3) valid_0
  subst c
  exact placed_valid 4 (4, 1) valid_221

theorem eq_card_426 : card_426 = combine (2, 4) [placed 4 (2, 0) card_11, inline_58] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_426 : Valid card_426 := by
  rw [eq_card_426]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_11
  subst c
  exact valid_inline_58

theorem eq_inline_59 : inline_59 = combine (4, 3) [placed 5 (0, 4) card_70, placed 0 (1, 0) card_226] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_59 : Valid inline_59 := by
  rw [eq_inline_59]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_70
  subst c
  exact placed_valid 0 (1, 0) valid_226

theorem eq_inline_60 : inline_60 = combine (4, 1) [placed 0 (1, 1) card_5, inline_59] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_60 : Valid inline_60 := by
  rw [eq_inline_60]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_5
  subst c
  exact valid_inline_59

theorem eq_inline_61 : inline_61 = combine (4, 2) [placed 0 (0, 1) card_4, inline_60] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_61 : Valid inline_61 := by
  rw [eq_inline_61]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_4
  subst c
  exact valid_inline_60

theorem eq_inline_62 : inline_62 = combine (3, 3) [placed 4 (4, 3) card_0, placed 3 (3, 0) card_2] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_62 : Valid inline_62 := by
  rw [eq_inline_62]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_0
  subst c
  exact placed_valid 3 (3, 0) valid_2

theorem eq_inline_63 : inline_63 = combine (2, 3) [placed 5 (2, 4) card_2, inline_62] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_63 : Valid inline_63 := by
  rw [eq_inline_63]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_2
  subst c
  exact valid_inline_62

theorem eq_inline_64 : inline_64 = combine (3, 0) [placed 5 (0, 1) card_52, inline_63] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_64 : Valid inline_64 := by
  rw [eq_inline_64]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_52
  subst c
  exact valid_inline_63

theorem eq_inline_65 : inline_65 = combine (3, 1) [placed 5 (0, 2) card_17, placed 5 (0, 4) card_357, inline_61, inline_64] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_65 : Valid inline_65 := by
  rw [eq_inline_65]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_357
  rcases hc with rfl | hc
  · exact valid_inline_61
  subst c
  exact valid_inline_64

theorem eq_inline_66 : inline_66 = combine (0, 1) [placed 7 (1, 4) card_5, inline_65] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_66 : Valid inline_66 := by
  rw [eq_inline_66]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact valid_inline_65

theorem eq_inline_67 : inline_67 = combine (0, 4) [placed 3 (1, 1) card_5, inline_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_67 : Valid inline_67 := by
  rw [eq_inline_67]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact valid_inline_66

theorem eq_inline_68 : inline_68 = combine (2, 4) [placed 1 (1, 1) card_5, inline_67] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_68 : Valid inline_68 := by
  rw [eq_inline_68]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_67

theorem eq_card_427 : card_427 = combine (2, 1) [placed 5 (1, 4) card_5, inline_68] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_427 : Valid card_427 := by
  rw [eq_card_427]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_68

theorem eq_card_428 : card_428 = combine (1, 4) [placed 0 (1, 0) card_7, placed 1 (0, 1) card_8, placed 4 (2, 0) card_9, placed 2 (0, 5) card_427] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_428 : Valid card_428 := by
  rw [eq_card_428]
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
  exact placed_valid 2 (0, 5) valid_427

theorem eq_inline_69 : inline_69 = combine (4, 3) [placed 0 (0, 2) card_2, placed 3 (5, 1) card_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_69 : Valid inline_69 := by
  rw [eq_inline_69]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_2
  subst c
  exact placed_valid 3 (5, 1) valid_46

theorem eq_card_429 : card_429 = combine (3, 4) [placed 4 (3, 0) card_7, placed 1 (2, 1) card_8, placed 0 (2, 0) card_9, inline_69] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_429 : Valid card_429 := by
  rw [eq_card_429]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_9
  subst c
  exact valid_inline_69

theorem eq_card_430 : card_430 = combine (3, 5) [placed 2 (2, 7) card_14, placed 2 (2, 7) card_31, placed 0 (0, 2) card_58, placed 2 (0, 6) card_100, placed 0 (0, 2) card_429] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_430 : Valid card_430 := by
  rw [eq_card_430]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_58
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_100
  subst c
  exact placed_valid 0 (0, 2) valid_429

theorem eq_card_431 : card_431 = combine (4, 4) [placed 7 (5, 4) card_160, placed 4 (5, 0) card_243, placed 0 (1, 1) card_429] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_431 : Valid card_431 := by
  rw [eq_card_431]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_160
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 0) valid_243
  subst c
  exact placed_valid 0 (1, 1) valid_429

theorem eq_inline_70 : inline_70 = combine (4, 1) [placed 2 (1, 1) card_5, placed 3 (5, 0) card_146] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_70 : Valid inline_70 := by
  rw [eq_inline_70]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 1) valid_5
  subst c
  exact placed_valid 3 (5, 0) valid_146

theorem eq_card_432 : card_432 = combine (4, 0) [placed 2 (0, 1) card_4, inline_70] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_432 : Valid card_432 := by
  rw [eq_card_432]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact valid_inline_70

theorem eq_card_433 : card_433 = combine (3, 4) [placed 0 (0, 0) card_86, placed 3 (4, 1) card_432] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_433 : Valid card_433 := by
  rw [eq_card_433]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_86
  subst c
  exact placed_valid 3 (4, 1) valid_432

theorem eq_inline_71 : inline_71 = combine (5, 1) [placed 2 (1, 2) card_1, placed 4 (5, 0) card_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_71 : Valid inline_71 := by
  rw [eq_inline_71]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 2) valid_1
  subst c
  exact placed_valid 4 (5, 0) valid_10

theorem eq_inline_72 : inline_72 = combine (4, 4) [placed 3 (5, 1) card_8, placed 0 (3, 1) card_41, placed 1 (1, 1) card_253, placed 3 (7, 1) card_256, placed 0 (3, 1) card_336] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_72 : Valid inline_72 := by
  rw [eq_inline_72]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_41
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_253
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 1) valid_256
  subst c
  exact placed_valid 0 (3, 1) valid_336

theorem eq_card_434 : card_434 = combine (3, 2) [placed 3 (5, 1) card_80, inline_71, inline_72] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_434 : Valid card_434 := by
  rw [eq_card_434]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_80
  rcases hc with rfl | hc
  · exact valid_inline_71
  subst c
  exact valid_inline_72

theorem eq_inline_73 : inline_73 = combine (3, 2) [placed 2 (0, 3) card_0, placed 4 (4, 1) card_212] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_73 : Valid inline_73 := by
  rw [eq_inline_73]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_0
  subst c
  exact placed_valid 4 (4, 1) valid_212

theorem eq_inline_74 : inline_74 = combine (3, 2) [placed 5 (3, 5) card_5, placed 4 (3, 1) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_74 : Valid inline_74 := by
  rw [eq_inline_74]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_5
  subst c
  exact placed_valid 4 (3, 1) valid_11

theorem eq_inline_75 : inline_75 = combine (3, 5) [placed 4 (4, 2) card_76, placed 2 (3, 5) card_130, inline_74] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_75 : Valid inline_75 := by
  rw [eq_inline_75]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_76
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_130
  subst c
  exact valid_inline_74

theorem eq_inline_76 : inline_76 = combine (3, 4) [placed 1 (0, 3) card_52, placed 3 (4, 2) card_76, inline_73, inline_75] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_76 : Valid inline_76 := by
  rw [eq_inline_76]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 2) valid_76
  rcases hc with rfl | hc
  · exact valid_inline_73
  subst c
  exact valid_inline_75

theorem eq_card_435 : card_435 = combine (4, 2) [placed 5 (1, 3) card_130, placed 5 (0, 3) card_140, placed 2 (0, 5) card_183, inline_76] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_435 : Valid card_435 := by
  rw [eq_card_435]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 3) valid_130
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_140
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_183
  subst c
  exact valid_inline_76

theorem eq_card_436 : card_436 = combine (3, 5) [placed 0 (2, 2) card_10, placed 5 (1, 6) card_47, placed 6 (3, 6) card_52, placed 3 (6, 2) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_436 : Valid card_436 := by
  rw [eq_card_436]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_47
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_52
  subst c
  exact placed_valid 3 (6, 2) valid_435

theorem eq_card_437 : card_437 = combine (3, 4) [placed 0 (2, 2) card_10, placed 5 (1, 6) card_47, placed 6 (3, 6) card_52, placed 3 (6, 2) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_437 : Valid card_437 := by
  rw [eq_card_437]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_47
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_52
  subst c
  exact placed_valid 3 (6, 2) valid_435

theorem eq_card_438 : card_438 = combine (4, 3) [placed 7 (6, 4) card_10, placed 6 (6, 5) card_47, placed 0 (2, 0) card_436] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_438 : Valid card_438 := by
  rw [eq_card_438]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 5) valid_47
  subst c
  exact placed_valid 0 (2, 0) valid_436

theorem eq_inline_77 : inline_77 = combine (4, 2) [placed 6 (4, 2) card_2, placed 5 (3, 5) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_77 : Valid inline_77 := by
  rw [eq_inline_77]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_2
  subst c
  exact placed_valid 5 (3, 5) valid_5

theorem eq_inline_78 : inline_78 = combine (4, 1) [placed 5 (3, 4) card_5, placed 4 (4, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_78 : Valid inline_78 := by
  rw [eq_inline_78]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_5
  subst c
  exact placed_valid 4 (4, 1) valid_5

theorem eq_inline_79 : inline_79 = combine (3, 1) [placed 7 (3, 4) card_5, inline_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_79 : Valid inline_79 := by
  rw [eq_inline_79]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact valid_inline_78

theorem eq_inline_80 : inline_80 = combine (2, 1) [placed 7 (3, 5) card_4, inline_79] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_80 : Valid inline_80 := by
  rw [eq_inline_80]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 5) valid_4
  subst c
  exact valid_inline_79

theorem eq_inline_81 : inline_81 = combine (3, 2) [placed 7 (4, 5) card_251, placed 7 (4, 5) card_432, inline_77, inline_80] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_81 : Valid inline_81 := by
  rw [eq_inline_81]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_251
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_432
  rcases hc with rfl | hc
  · exact valid_inline_77
  subst c
  exact valid_inline_80

theorem eq_card_439 : card_439 = combine (3, 3) [placed 2 (0, 4) card_5, inline_81] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_439 : Valid card_439 := by
  rw [eq_card_439]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_5
  subst c
  exact valid_inline_81

theorem eq_inline_82 : inline_82 = combine (1, 1) [placed 7 (1, 4) card_5, placed 7 (5, 4) card_439] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_82 : Valid inline_82 := by
  rw [eq_inline_82]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 7 (5, 4) valid_439

theorem eq_card_440 : card_440 = combine (0, 1) [placed 0 (0, 1) card_18, inline_82] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_440 : Valid card_440 := by
  rw [eq_card_440]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_18
  subst c
  exact valid_inline_82

theorem eq_card_441 : card_441 = combine (3, 3) [placed 1 (0, 2) card_28, placed 4 (4, 1) card_58, placed 0 (0, 0) card_440] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_441 : Valid card_441 := by
  rw [eq_card_441]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_58
  subst c
  exact placed_valid 0 (0, 0) valid_440

theorem eq_card_442 : card_442 = combine (3, 3) [placed 7 (5, 4) card_40, placed 7 (5, 4) card_149, placed 0 (0, 0) card_440] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_442 : Valid card_442 := by
  rw [eq_card_442]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_149
  subst c
  exact placed_valid 0 (0, 0) valid_440

theorem eq_inline_83 : inline_83 = combine (5, 3) [placed 4 (5, 3) card_3, placed 1 (4, 0) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_83 : Valid inline_83 := by
  rw [eq_inline_83]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_3
  subst c
  exact placed_valid 1 (4, 0) valid_5

theorem eq_inline_84 : inline_84 = combine (3, 3) [placed 3 (4, 0) card_5, inline_83] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_84 : Valid inline_84 := by
  rw [eq_inline_84]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 0) valid_5
  subst c
  exact valid_inline_83

theorem eq_inline_85 : inline_85 = combine (4, 1) [placed 2 (1, 1) card_5, inline_84] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_85 : Valid inline_85 := by
  rw [eq_inline_85]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 1) valid_5
  subst c
  exact valid_inline_84

theorem eq_inline_86 : inline_86 = combine (2, 4) [placed 1 (1, 1) card_5, inline_85] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_86 : Valid inline_86 := by
  rw [eq_inline_86]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_85

theorem eq_inline_87 : inline_87 = combine (4, 0) [placed 2 (0, 1) card_4, inline_86] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_87 : Valid inline_87 := by
  rw [eq_inline_87]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact valid_inline_86

theorem eq_inline_88 : inline_88 = combine (3, 1) [placed 0 (0, 1) card_4, inline_87] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_88 : Valid inline_88 := by
  rw [eq_inline_88]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_4
  subst c
  exact valid_inline_87

theorem eq_inline_89 : inline_89 = combine (0, 1) [placed 7 (1, 4) card_5, inline_88] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_89 : Valid inline_89 := by
  rw [eq_inline_89]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact valid_inline_88

theorem eq_card_443 : card_443 = combine (2, 1) [placed 5 (1, 4) card_5, inline_89] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_443 : Valid card_443 := by
  rw [eq_card_443]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_89

theorem eq_card_444 : card_444 = combine (1, 4) [placed 0 (1, 0) card_7, placed 1 (0, 1) card_8, placed 4 (2, 0) card_9, placed 2 (0, 5) card_443] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_444 : Valid card_444 := by
  rw [eq_card_444]
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
  exact placed_valid 2 (0, 5) valid_443

theorem eq_inline_90 : inline_90 = combine (3, 3) [placed 0 (2, 0) card_20, placed 4 (3, 0) card_29, placed 0 (1, 0) card_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_90 : Valid inline_90 := by
  rw [eq_inline_90]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_29
  subst c
  exact placed_valid 0 (1, 0) valid_221

theorem eq_card_445 : card_445 = combine (3, 0) [placed 2 (0, 1) card_5, inline_90] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_445 : Valid card_445 := by
  rw [eq_card_445]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_90

theorem eq_inline_91 : inline_91 = combine (2, 4) [placed 5 (1, 7) card_0, placed 2 (0, 5) card_72] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_91 : Valid inline_91 := by
  rw [eq_inline_91]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_0
  subst c
  exact placed_valid 2 (0, 5) valid_72

theorem eq_card_446 : card_446 = combine (2, 3) [placed 5 (1, 6) card_5, inline_91] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_446 : Valid card_446 := by
  rw [eq_card_446]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_5
  subst c
  exact valid_inline_91

theorem eq_inline_92 : inline_92 = combine (2, 3) [placed 1 (1, 0) card_0, placed 1 (0, 1) card_445] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_92 : Valid inline_92 := by
  rw [eq_inline_92]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_0
  subst c
  exact placed_valid 1 (0, 1) valid_445

theorem eq_card_447 : card_447 = combine (2, 4) [placed 1 (1, 1) card_5, inline_92] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_447 : Valid card_447 := by
  rw [eq_card_447]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_92

theorem block06_valid : Valid card_384 ∧ Valid card_385 ∧ Valid card_386 ∧ Valid card_387 ∧ Valid card_388 ∧ Valid card_389 ∧ Valid card_390 ∧ Valid card_391 ∧ Valid card_392 ∧ Valid card_393 ∧ Valid card_394 ∧ Valid card_395 ∧ Valid card_396 ∧ Valid card_397 ∧ Valid card_398 ∧ Valid card_399 ∧ Valid card_400 ∧ Valid card_401 ∧ Valid card_402 ∧ Valid card_403 ∧ Valid card_404 ∧ Valid card_405 ∧ Valid card_406 ∧ Valid card_407 ∧ Valid card_408 ∧ Valid card_409 ∧ Valid card_410 ∧ Valid card_411 ∧ Valid card_412 ∧ Valid card_413 ∧ Valid card_414 ∧ Valid card_415 ∧ Valid card_416 ∧ Valid card_417 ∧ Valid card_418 ∧ Valid card_419 ∧ Valid card_420 ∧ Valid card_421 ∧ Valid card_422 ∧ Valid card_423 ∧ Valid card_424 ∧ Valid card_425 ∧ Valid card_426 ∧ Valid card_427 ∧ Valid card_428 ∧ Valid card_429 ∧ Valid card_430 ∧ Valid card_431 ∧ Valid card_432 ∧ Valid card_433 ∧ Valid card_434 ∧ Valid card_435 ∧ Valid card_436 ∧ Valid card_437 ∧ Valid card_438 ∧ Valid card_439 ∧ Valid card_440 ∧ Valid card_441 ∧ Valid card_442 ∧ Valid card_443 ∧ Valid card_444 ∧ Valid card_445 ∧ Valid card_446 ∧ Valid card_447 ∧ True :=
  ⟨valid_384, valid_385, valid_386, valid_387, valid_388, valid_389, valid_390, valid_391, valid_392, valid_393, valid_394, valid_395, valid_396, valid_397, valid_398, valid_399, valid_400, valid_401, valid_402, valid_403, valid_404, valid_405, valid_406, valid_407, valid_408, valid_409, valid_410, valid_411, valid_412, valid_413, valid_414, valid_415, valid_416, valid_417, valid_418, valid_419, valid_420, valid_421, valid_422, valid_423, valid_424, valid_425, valid_426, valid_427, valid_428, valid_429, valid_430, valid_431, valid_432, valid_433, valid_434, valid_435, valid_436, valid_437, valid_438, valid_439, valid_440, valid_441, valid_442, valid_443, valid_444, valid_445, valid_446, valid_447, True.intro⟩

end OAI.Snaky21.Certificate

theorem solution : Valid card_384 ∧ Valid card_385 ∧ Valid card_386 ∧ Valid card_387 ∧ Valid card_388 ∧ Valid card_389 ∧ Valid card_390 ∧ Valid card_391 ∧ Valid card_392 ∧ Valid card_393 ∧ Valid card_394 ∧ Valid card_395 ∧ Valid card_396 ∧ Valid card_397 ∧ Valid card_398 ∧ Valid card_399 ∧ Valid card_400 ∧ Valid card_401 ∧ Valid card_402 ∧ Valid card_403 ∧ Valid card_404 ∧ Valid card_405 ∧ Valid card_406 ∧ Valid card_407 ∧ Valid card_408 ∧ Valid card_409 ∧ Valid card_410 ∧ Valid card_411 ∧ Valid card_412 ∧ Valid card_413 ∧ Valid card_414 ∧ Valid card_415 ∧ Valid card_416 ∧ Valid card_417 ∧ Valid card_418 ∧ Valid card_419 ∧ Valid card_420 ∧ Valid card_421 ∧ Valid card_422 ∧ Valid card_423 ∧ Valid card_424 ∧ Valid card_425 ∧ Valid card_426 ∧ Valid card_427 ∧ Valid card_428 ∧ Valid card_429 ∧ Valid card_430 ∧ Valid card_431 ∧ Valid card_432 ∧ Valid card_433 ∧ Valid card_434 ∧ Valid card_435 ∧ Valid card_436 ∧ Valid card_437 ∧ Valid card_438 ∧ Valid card_439 ∧ Valid card_440 ∧ Valid card_441 ∧ Valid card_442 ∧ Valid card_443 ∧ Valid card_444 ∧ Valid card_445 ∧ Valid card_446 ∧ Valid card_447 ∧ True := block06_valid
