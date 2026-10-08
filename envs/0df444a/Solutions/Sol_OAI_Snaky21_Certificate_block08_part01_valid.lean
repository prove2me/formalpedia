-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block08_part01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T11:27:11.789267+00:00
-- url     : https://prove2.me/submissions/419eab43-3005-4af6-ba51-e48d3cdd6de7

import Definitions.Def_Snaky21Data08
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_part00_valid
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

theorem eq_inline_180 : inline_180 = combine (1, 3) [placed 3 (1, 3) card_4, placed 7 (2, 6) card_49] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_180 : Valid inline_180 := by
  rw [eq_inline_180]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 3) valid_4
  subst c
  exact placed_valid 7 (2, 6) valid_49

theorem eq_inline_181 : inline_181 = combine (1, 7) [placed 3 (1, 4) card_5, placed 0 (0, 1) card_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_181 : Valid inline_181 := by
  rw [eq_inline_181]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_446

theorem eq_card_528 : card_528 = combine (0, 7) [placed 4 (1, 3) card_61, inline_180, inline_181] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_528 : Valid card_528 := by
  rw [eq_card_528]
  apply combination_rule (0, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 3) valid_61
  rcases hc with rfl | hc
  · exact valid_inline_180
  subst c
  exact valid_inline_181

theorem eq_inline_182 : inline_182 = combine (3, 6) [placed 6 (6, 6) card_4, placed 2 (3, 6) card_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_182 : Valid inline_182 := by
  rw [eq_inline_182]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 6) valid_4
  subst c
  exact placed_valid 2 (3, 6) valid_4

theorem eq_inline_183 : inline_183 = combine (7, 3) [placed 5 (4, 6) card_38, placed 2 (4, 7) card_351] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_183 : Valid inline_183 := by
  rw [eq_inline_183]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_38
  subst c
  exact placed_valid 2 (4, 7) valid_351

theorem eq_inline_184 : inline_184 = combine (7, 5) [inline_182, inline_183] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_184 : Valid inline_184 := by
  rw [eq_inline_184]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_182
  subst c
  exact valid_inline_183

theorem eq_inline_185 : inline_185 = combine (4, 6) [placed 3 (5, 3) card_5, inline_184] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_185 : Valid inline_185 := by
  rw [eq_inline_185]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_5
  subst c
  exact valid_inline_184

theorem eq_inline_186 : inline_186 = combine (6, 6) [placed 1 (5, 3) card_5, inline_185] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_186 : Valid inline_186 := by
  rw [eq_inline_186]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 3) valid_5
  subst c
  exact valid_inline_185

theorem eq_inline_187 : inline_187 = combine (5, 3) [placed 5 (3, 7) card_133, inline_186, placed 7 (6, 6) card_505] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_187 : Valid inline_187 := by
  rw [eq_inline_187]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_133
  rcases hc with rfl | hc
  · exact valid_inline_186
  subst c
  exact placed_valid 7 (6, 6) valid_505

theorem eq_card_529 : card_529 = combine (5, 6) [placed 4 (6, 2) card_12, placed 1 (3, 3) card_181, placed 4 (6, 2) card_189, placed 4 (6, 1) card_369, placed 1 (3, 3) card_474, placed 0 (4, 0) card_528, inline_187] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_529 : Valid card_529 := by
  rw [eq_card_529]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_474
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 0) valid_528
  subst c
  exact valid_inline_187

theorem eq_inline_188 : inline_188 = combine (2, 5) [placed 5 (2, 5) card_5, placed 0 (1, 2) card_20] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_188 : Valid inline_188 := by
  rw [eq_inline_188]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_5
  subst c
  exact placed_valid 0 (1, 2) valid_20

theorem eq_inline_189 : inline_189 = combine (3, 2) [placed 5 (0, 3) card_51, inline_188] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_189 : Valid inline_189 := by
  rw [eq_inline_189]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_51
  subst c
  exact valid_inline_188

theorem eq_inline_190 : inline_190 = combine (2, 2) [placed 6 (2, 5) card_23, inline_189] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_190 : Valid inline_190 := by
  rw [eq_inline_190]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 5) valid_23
  subst c
  exact valid_inline_189

theorem eq_card_530 : card_530 = combine (2, 4) [placed 2 (0, 5) card_72, placed 2 (0, 5) card_360, placed 0 (0, 1) card_499, inline_190] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_530 : Valid card_530 := by
  rw [eq_card_530]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_72
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_360
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_499
  subst c
  exact valid_inline_190

theorem eq_card_531 : card_531 = combine (1, 4) [placed 1 (0, 0) card_0, placed 0 (0, 0) card_530] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_531 : Valid card_531 := by
  rw [eq_card_531]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_530

theorem eq_inline_191 : inline_191 = combine (2, 6) [placed 4 (3, 2) card_19, placed 4 (3, 2) card_84, placed 3 (3, 3) card_314, placed 2 (1, 7) card_521] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_191 : Valid inline_191 := by
  rw [eq_inline_191]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_84
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 3) valid_314
  subst c
  exact placed_valid 2 (1, 7) valid_521

theorem eq_card_532 : card_532 = combine (2, 3) [placed 0 (2, 2) card_44, placed 0 (2, 2) card_52, placed 5 (0, 6) card_134, inline_191] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_532 : Valid card_532 := by
  rw [eq_card_532]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_134
  subst c
  exact valid_inline_191

theorem eq_inline_192 : inline_192 = combine (3, 4) [placed 0 (2, 0) card_53, placed 2 (1, 6) card_55, placed 7 (5, 4) card_392] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_192 : Valid inline_192 := by
  rw [eq_inline_192]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_55
  subst c
  exact placed_valid 7 (5, 4) valid_392

theorem eq_card_533 : card_533 = combine (4, 3) [placed 5 (0, 3) card_11, placed 0 (1, 0) card_279, inline_192] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_533 : Valid card_533 := by
  rw [eq_card_533]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_279
  subst c
  exact valid_inline_192

theorem eq_inline_193 : inline_193 = combine (2, 6) [placed 1 (2, 3) card_5, placed 1 (0, 3) card_177] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_193 : Valid inline_193 := by
  rw [eq_inline_193]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_5
  subst c
  exact placed_valid 1 (0, 3) valid_177

theorem eq_inline_194 : inline_194 = combine (3, 5) [placed 1 (2, 2) card_0, placed 7 (5, 6) card_239] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_194 : Valid inline_194 := by
  rw [eq_inline_194]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_0
  subst c
  exact placed_valid 7 (5, 6) valid_239

theorem eq_inline_195 : inline_195 = combine (3, 6) [placed 0 (2, 2) card_139, inline_193, inline_194] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_195 : Valid inline_195 := by
  rw [eq_inline_195]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_139
  rcases hc with rfl | hc
  · exact valid_inline_193
  subst c
  exact valid_inline_194

theorem eq_card_534 : card_534 = combine (2, 5) [placed 2 (2, 6) card_44, placed 2 (2, 6) card_52, placed 5 (0, 5) card_388, inline_195] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_534 : Valid card_534 := by
  rw [eq_card_534]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_388
  subst c
  exact valid_inline_195

theorem eq_card_535 : card_535 = combine (3, 5) [placed 2 (0, 7) card_345, placed 5 (0, 6) card_421, placed 2 (0, 7) card_522, placed 2 (1, 8) card_530, placed 0 (0, 0) card_532, placed 0 (0, 2) card_533, placed 2 (0, 8) card_534] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_535 : Valid card_535 := by
  rw [eq_card_535]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_345
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_421
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_522
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_530
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_532
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_533
  subst c
  exact placed_valid 2 (0, 8) valid_534

theorem eq_card_536 : card_536 = combine (3, 5) [placed 4 (4, 1) card_14, placed 7 (6, 6) card_88, placed 3 (6, 2) card_213, placed 5 (0, 6) card_534] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_536 : Valid card_536 := by
  rw [eq_card_536]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_88
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_213
  subst c
  exact placed_valid 5 (0, 6) valid_534

theorem eq_inline_196 : inline_196 = combine (3, 3) [placed 6 (4, 5) card_45, placed 0 (1, 2) card_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_196 : Valid inline_196 := by
  rw [eq_inline_196]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_45
  subst c
  exact placed_valid 0 (1, 2) valid_418

theorem eq_inline_197 : inline_197 = combine (2, 5) [placed 6 (2, 6) card_15, placed 0 (1, 2) card_425] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_197 : Valid inline_197 := by
  rw [eq_inline_197]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_15
  subst c
  exact placed_valid 0 (1, 2) valid_425

theorem eq_inline_198 : inline_198 = combine (2, 5) [placed 1 (2, 2) card_0, placed 4 (2, 2) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_198 : Valid inline_198 := by
  rw [eq_inline_198]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_0
  subst c
  exact placed_valid 4 (2, 2) valid_23

theorem eq_inline_199 : inline_199 = combine (3, 5) [placed 3 (4, 2) card_0, inline_198] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_199 : Valid inline_199 := by
  rw [eq_inline_199]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 2) valid_0
  subst c
  exact valid_inline_198

theorem eq_inline_200 : inline_200 = combine (3, 6) [placed 4 (4, 2) card_139, placed 0 (1, 2) card_382, inline_199] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_200 : Valid inline_200 := by
  rw [eq_inline_200]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_139
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_382
  subst c
  exact valid_inline_199

theorem eq_inline_201 : inline_201 = combine (4, 4) [placed 4 (5, 1) card_13, placed 5 (1, 4) card_30, inline_200] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_201 : Valid inline_201 := by
  rw [eq_inline_201]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_30
  subst c
  exact valid_inline_200

theorem eq_inline_202 : inline_202 = combine (4, 5) [placed 0 (1, 1) card_166, placed 2 (1, 7) card_464, inline_197, inline_201] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_202 : Valid inline_202 := by
  rw [eq_inline_202]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_166
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_464
  rcases hc with rfl | hc
  · exact valid_inline_197
  subst c
  exact valid_inline_201

theorem eq_card_537 : card_537 = combine (4, 3) [placed 1 (1, 3) card_74, placed 0 (0, 1) card_108, inline_196, inline_202] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_537 : Valid card_537 := by
  rw [eq_card_537]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_74
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_108
  rcases hc with rfl | hc
  · exact valid_inline_196
  subst c
  exact valid_inline_202

theorem eq_inline_203 : inline_203 = combine (5, 7) [placed 0 (3, 3) card_190, placed 4 (7, 3) card_190, placed 3 (8, 5) card_258, placed 2 (1, 9) card_273, placed 0 (1, 4) card_415, placed 1 (2, 4) card_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_203 : Valid inline_203 := by
  rw [eq_inline_203]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_258
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_273
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_415
  subst c
  exact placed_valid 1 (2, 4) valid_507

theorem eq_inline_204 : inline_204 = combine (4, 6) [placed 2 (1, 6) card_2, placed 2 (3, 9) card_512] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_204 : Valid inline_204 := by
  rw [eq_inline_204]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 2 (3, 9) valid_512

theorem eq_inline_205 : inline_205 = combine (5, 7) [placed 0 (5, 3) card_7, placed 4 (6, 3) card_9, placed 3 (6, 4) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_205 : Valid inline_205 := by
  rw [eq_inline_205]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_9
  subst c
  exact placed_valid 3 (6, 4) valid_354

theorem eq_inline_206 : inline_206 = combine (4, 6) [placed 2 (1, 6) card_2, placed 4 (5, 3) card_15] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_206 : Valid inline_206 := by
  rw [eq_inline_206]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 4 (5, 3) valid_15

theorem eq_inline_207 : inline_207 = combine (5, 7) [placed 1 (4, 4) card_8, placed 7 (6, 7) card_505] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_207 : Valid inline_207 := by
  rw [eq_inline_207]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_8
  subst c
  exact placed_valid 7 (6, 7) valid_505

theorem eq_inline_208 : inline_208 = combine (5, 4) [placed 2 (3, 7) card_136, inline_205, inline_206, inline_207] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_208 : Valid inline_208 := by
  rw [eq_inline_208]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_136
  rcases hc with rfl | hc
  · exact valid_inline_205
  rcases hc with rfl | hc
  · exact valid_inline_206
  subst c
  exact valid_inline_207

theorem eq_inline_209 : inline_209 = combine (4, 6) [placed 2 (1, 6) card_2, placed 0 (3, 2) card_517] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_209 : Valid inline_209 := by
  rw [eq_inline_209]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 0 (3, 2) valid_517

theorem eq_inline_210 : inline_210 = combine (5, 7) [placed 5 (2, 8) card_116, placed 3 (7, 4) card_180, placed 3 (8, 5) card_258, placed 2 (1, 9) card_273, placed 1 (3, 4) card_275, placed 0 (1, 4) card_415, placed 4 (8, 2) card_518] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_210 : Valid inline_210 := by
  rw [eq_inline_210]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_258
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_273
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_275
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_415
  subst c
  exact placed_valid 4 (8, 2) valid_518

theorem eq_inline_211 : inline_211 = combine (4, 6) [placed 2 (1, 6) card_2, placed 2 (3, 9) card_527] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_211 : Valid inline_211 := by
  rw [eq_inline_211]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 2 (3, 9) valid_527

theorem eq_inline_212 : inline_212 = combine (4, 6) [placed 2 (1, 6) card_2, placed 2 (3, 9) card_537] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_212 : Valid inline_212 := by
  rw [eq_inline_212]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 2 (3, 9) valid_537

theorem eq_card_538 : card_538 = combine (5, 6) [placed 0 (4, 1) card_459, inline_203, inline_204, inline_208, inline_209, inline_210, inline_211, placed 0 (0, 1) card_529, placed 2 (3, 10) card_535, inline_212] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_538 : Valid card_538 := by
  rw [eq_card_538]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_459
  rcases hc with rfl | hc
  · exact valid_inline_203
  rcases hc with rfl | hc
  · exact valid_inline_204
  rcases hc with rfl | hc
  · exact valid_inline_208
  rcases hc with rfl | hc
  · exact valid_inline_209
  rcases hc with rfl | hc
  · exact valid_inline_210
  rcases hc with rfl | hc
  · exact valid_inline_211
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_529
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_535
  subst c
  exact valid_inline_212

theorem eq_inline_213 : inline_213 = combine (3, 5) [placed 2 (0, 5) card_5, placed 2 (3, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_213 : Valid inline_213 := by
  rw [eq_inline_213]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_5
  subst c
  exact placed_valid 2 (3, 5) valid_6

theorem eq_inline_214 : inline_214 = combine (3, 4) [placed 7 (3, 4) card_5, inline_213] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_214 : Valid inline_214 := by
  rw [eq_inline_214]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact valid_inline_213

theorem eq_inline_215 : inline_215 = combine (4, 2) [placed 0 (0, 1) card_1, placed 4 (4, 2) card_153] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_215 : Valid inline_215 := by
  rw [eq_inline_215]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_1
  subst c
  exact placed_valid 4 (4, 2) valid_153

theorem eq_inline_216 : inline_216 = combine (3, 5) [placed 2 (0, 5) card_5, inline_215] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_216 : Valid inline_216 := by
  rw [eq_inline_216]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_5
  subst c
  exact valid_inline_215

theorem eq_inline_217 : inline_217 = combine (3, 4) [placed 7 (3, 4) card_5, inline_216] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_217 : Valid inline_217 := by
  rw [eq_inline_217]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact valid_inline_216

theorem eq_inline_218 : inline_218 = combine (1, 2) [placed 4 (4, 1) card_0, placed 7 (1, 5) card_2] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_218 : Valid inline_218 := by
  rw [eq_inline_218]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 7 (1, 5) valid_2

theorem eq_inline_219 : inline_219 = combine (1, 1) [placed 0 (0, 1) card_5, inline_218] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_219 : Valid inline_219 := by
  rw [eq_inline_219]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_218

theorem eq_inline_220 : inline_220 = combine (4, 1) [placed 0 (2, 0) card_83, placed 3 (4, 1) card_281] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_220 : Valid inline_220 := by
  rw [eq_inline_220]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_83
  subst c
  exact placed_valid 3 (4, 1) valid_281

theorem eq_inline_221 : inline_221 = combine (2, 1) [inline_214, inline_217, inline_219, inline_220] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_221 : Valid inline_221 := by
  rw [eq_inline_221]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_214
  rcases hc with rfl | hc
  · exact valid_inline_217
  rcases hc with rfl | hc
  · exact valid_inline_219
  subst c
  exact valid_inline_220

theorem eq_inline_222 : inline_222 = combine (2, 5) [placed 5 (1, 9) card_4, inline_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_222 : Valid inline_222 := by
  rw [eq_inline_222]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 9) valid_4
  subst c
  exact valid_inline_221

theorem eq_inline_223 : inline_223 = combine (0, 5) [placed 7 (1, 8) card_5, inline_222] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_223 : Valid inline_223 := by
  rw [eq_inline_223]
  apply combination_rule (0, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 8) valid_5
  subst c
  exact valid_inline_222

theorem eq_card_539 : card_539 = combine (1, 9) [placed 0 (1, 5) card_6, inline_223] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_539 : Valid card_539 := by
  rw [eq_card_539]
  apply combination_rule (1, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 5) valid_6
  subst c
  exact valid_inline_223

theorem eq_inline_224 : inline_224 = combine (2, 3) [placed 1 (1, 2) card_237, placed 3 (4, 3) card_281] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_224 : Valid inline_224 := by
  rw [eq_inline_224]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_237
  subst c
  exact placed_valid 3 (4, 3) valid_281

theorem eq_inline_225 : inline_225 = combine (4, 4) [placed 5 (1, 5) card_164, placed 2 (3, 7) card_199, placed 0 (0, 1) card_283] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_225 : Valid inline_225 := by
  rw [eq_inline_225]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_164
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_199
  subst c
  exact placed_valid 0 (0, 1) valid_283

theorem eq_inline_226 : inline_226 = combine (4, 5) [placed 0 (0, 3) card_170, inline_225] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_226 : Valid inline_226 := by
  rw [eq_inline_226]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_170
  subst c
  exact valid_inline_225

theorem eq_inline_227 : inline_227 = combine (0, 6) [placed 4 (1, 6) card_16, inline_226] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_227 : Valid inline_227 := by
  rw [eq_inline_227]
  apply combination_rule (0, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 6) valid_16
  subst c
  exact valid_inline_226

theorem eq_card_540 : card_540 = combine (4, 3) [placed 2 (3, 6) card_44, inline_224, inline_227] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_540 : Valid card_540 := by
  rw [eq_card_540]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_44
  rcases hc with rfl | hc
  · exact valid_inline_224
  subst c
  exact valid_inline_227

theorem eq_inline_228 : inline_228 = combine (4, 2) [placed 5 (3, 6) card_0, placed 7 (4, 4) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_228 : Valid inline_228 := by
  rw [eq_inline_228]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_0
  subst c
  exact placed_valid 7 (4, 4) valid_35

theorem eq_inline_229 : inline_229 = combine (4, 3) [placed 0 (0, 1) card_170, inline_228] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_229 : Valid inline_229 := by
  rw [eq_inline_229]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_170
  subst c
  exact valid_inline_228

theorem eq_inline_230 : inline_230 = combine (3, 4) [placed 2 (3, 5) card_6, placed 0 (0, 0) card_86, inline_229] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_230 : Valid inline_230 := by
  rw [eq_inline_230]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_86
  subst c
  exact valid_inline_229

theorem eq_inline_231 : inline_231 = combine (3, 5) [placed 6 (4, 5) card_0, inline_230] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_231 : Valid inline_231 := by
  rw [eq_inline_231]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_0
  subst c
  exact valid_inline_230

theorem eq_inline_232 : inline_232 = combine (2, 5) [placed 5 (1, 9) card_4, inline_231] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_232 : Valid inline_232 := by
  rw [eq_inline_232]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 9) valid_4
  subst c
  exact valid_inline_231

theorem eq_inline_233 : inline_233 = combine (0, 4) [placed 7 (1, 8) card_4, inline_232] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_233 : Valid inline_233 := by
  rw [eq_inline_233]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 8) valid_4
  subst c
  exact valid_inline_232

theorem eq_inline_234 : inline_234 = combine (1, 9) [placed 0 (1, 5) card_6, inline_233] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_234 : Valid inline_234 := by
  rw [eq_inline_234]
  apply combination_rule (1, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 5) valid_6
  subst c
  exact valid_inline_233

theorem eq_card_541 : card_541 = combine (1, 8) [placed 4 (1, 4) card_6, inline_234] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_541 : Valid card_541 := by
  rw [eq_card_541]
  apply combination_rule (1, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 4) valid_6
  subst c
  exact valid_inline_234

theorem eq_inline_235 : inline_235 = combine (5, 2) [placed 6 (6, 2) card_0, placed 2 (1, 3) card_1] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_235 : Valid inline_235 := by
  rw [eq_inline_235]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 2) valid_0
  subst c
  exact placed_valid 2 (1, 3) valid_1

theorem eq_inline_236 : inline_236 = combine (4, 3) [placed 0 (3, 1) card_29, inline_235] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_236 : Valid inline_236 := by
  rw [eq_inline_236]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_29
  subst c
  exact valid_inline_235

theorem eq_inline_237 : inline_237 = combine (4, 2) [placed 0 (0, 1) card_1, inline_236] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_237 : Valid inline_237 := by
  rw [eq_inline_237]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_1
  subst c
  exact valid_inline_236

theorem eq_inline_238 : inline_238 = combine (2, 1) [placed 7 (3, 4) card_5, inline_237] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_238 : Valid inline_238 := by
  rw [eq_inline_238]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact valid_inline_237

theorem eq_card_542 : card_542 = combine (1, 3) [placed 7 (1, 5) card_3, inline_238] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_542 : Valid card_542 := by
  rw [eq_card_542]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_3
  subst c
  exact valid_inline_238

theorem eq_inline_239 : inline_239 = combine (5, 7) [placed 0 (4, 3) card_261, placed 1 (1, 6) card_370] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_239 : Valid inline_239 := by
  rw [eq_inline_239]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_261
  subst c
  exact placed_valid 1 (1, 6) valid_370

theorem eq_inline_240 : inline_240 = combine (5, 5) [placed 0 (4, 3) card_154, placed 0 (1, 3) card_170] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_240 : Valid inline_240 := by
  rw [eq_inline_240]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_154
  subst c
  exact placed_valid 0 (1, 3) valid_170

theorem eq_inline_241 : inline_241 = combine (5, 7) [placed 6 (5, 7) card_1, inline_240] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_241 : Valid inline_241 := by
  rw [eq_inline_241]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_1
  subst c
  exact valid_inline_240

theorem eq_inline_242 : inline_242 = combine (3, 7) [placed 0 (2, 7) card_16, inline_241] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_242 : Valid inline_242 := by
  rw [eq_inline_242]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 7) valid_16
  subst c
  exact valid_inline_241

theorem eq_inline_243 : inline_243 = combine (1, 6) [placed 7 (2, 10) card_4, inline_242] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_243 : Valid inline_243 := by
  rw [eq_inline_243]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 10) valid_4
  subst c
  exact valid_inline_242

theorem eq_inline_244 : inline_244 = combine (2, 10) [placed 4 (2, 6) card_6, inline_243] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_244 : Valid inline_244 := by
  rw [eq_inline_244]
  apply combination_rule (2, 10) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 6) valid_6
  subst c
  exact valid_inline_243

theorem eq_inline_245 : inline_245 = combine (2, 10) [placed 4 (2, 6) card_6, placed 0 (1, 2) card_539] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_245 : Valid inline_245 := by
  rw [eq_inline_245]
  apply combination_rule (2, 10) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 6) valid_6
  subst c
  exact placed_valid 0 (1, 2) valid_539

theorem eq_inline_246 : inline_246 = combine (4, 6) [placed 0 (4, 2) card_7, placed 0 (1, 2) card_86, placed 0 (1, 2) card_542] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_246 : Valid inline_246 := by
  rw [eq_inline_246]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_86
  subst c
  exact placed_valid 0 (1, 2) valid_542

theorem eq_inline_247 : inline_247 = combine (4, 5) [placed 0 (1, 2) card_433, inline_239, inline_244, inline_245, placed 0 (1, 0) card_540, placed 0 (1, 2) card_541, inline_246] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_247 : Valid inline_247 := by
  rw [eq_inline_247]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_433
  rcases hc with rfl | hc
  · exact valid_inline_239
  rcases hc with rfl | hc
  · exact valid_inline_244
  rcases hc with rfl | hc
  · exact valid_inline_245
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_540
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_541
  subst c
  exact valid_inline_246

theorem eq_inline_248 : inline_248 = combine (2, 5) [placed 7 (2, 7) card_3, placed 1 (2, 5) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_248 : Valid inline_248 := by
  rw [eq_inline_248]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 7) valid_3
  subst c
  exact placed_valid 1 (2, 5) valid_5

theorem eq_inline_249 : inline_249 = combine (3, 8) [placed 1 (0, 6) card_278, inline_248] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_249 : Valid inline_249 := by
  rw [eq_inline_249]
  apply combination_rule (3, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 6) valid_278
  subst c
  exact valid_inline_248

theorem eq_card_543 : card_543 = combine (2, 9) [placed 1 (1, 6) card_8, placed 0 (1, 3) card_280, inline_247, inline_249] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_543 : Valid card_543 := by
  rw [eq_card_543]
  apply combination_rule (2, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 6) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_280
  rcases hc with rfl | hc
  · exact valid_inline_247
  subst c
  exact valid_inline_249


end OAI.Snaky21.Certificate

theorem solution : Valid card_528 ∧ Valid card_529 ∧ Valid card_530 ∧ Valid card_531 ∧ Valid card_532 ∧ Valid card_533 ∧ Valid card_534 ∧ Valid card_535 ∧ Valid card_536 ∧ Valid card_537 ∧ Valid card_538 ∧ Valid card_539 ∧ Valid card_540 ∧ Valid card_541 ∧ Valid card_542 ∧ Valid card_543 ∧ True :=
  ⟨valid_528, valid_529, valid_530, valid_531, valid_532, valid_533, valid_534, valid_535, valid_536, valid_537, valid_538, valid_539, valid_540, valid_541, valid_542, valid_543, True.intro⟩
