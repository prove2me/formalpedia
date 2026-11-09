-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T13:22:57.519339+00:00
-- url     : https://prove2.me/submissions/4bb1f292-ac6a-48f2-af2d-b7f8b04b251f

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E149
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_boundarySound26_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_boundarySound49_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_boundarySound58_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_boundarySound73_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound1800_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2390_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2400_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2864_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2867_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2878_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2880_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2888_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2913_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2920_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2927_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2928_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2968_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3001_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3011_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3012_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3017_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3040_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3042_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3052_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3065_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3066_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3067_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3069_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3075_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3081_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3144_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3146_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3149_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3166_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3167_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3170_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3174_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3195_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3205_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3206_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3208_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3213_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3295_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3296_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3334_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3351_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3393_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3433_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3436_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3439_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3441_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3442_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3447_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound0_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound100_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound101_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound102_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound103_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound104_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound105_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound106_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound107_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound108_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound10_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound110_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound111_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound112_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound113_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound114_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound115_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound116_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound117_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound118_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound119_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound120_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound121_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound123_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound124_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound125_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound127_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound128_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound129_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound12_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound130_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound131_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound132_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound133_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound134_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound135_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound136_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound137_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound138_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound139_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound140_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound141_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound142_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound143_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound144_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound145_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound146_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound147_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound148_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound149_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound14_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound150_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound151_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound152_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound153_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound154_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound155_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound156_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound157_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound158_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound159_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound15_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound160_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound161_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound162_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound163_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound164_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound165_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound166_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound167_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound168_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound16_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound170_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound171_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound172_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound174_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound175_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound176_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound177_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound178_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound179_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound17_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound180_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound181_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound182_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound183_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound184_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound185_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound186_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound187_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound188_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound189_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound18_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound190_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound191_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound192_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound193_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound194_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound195_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound196_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound197_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound198_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound199_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound19_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound1_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound200_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound202_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound203_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound204_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound205_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound206_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound207_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound208_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound209_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound20_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound210_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound211_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound212_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound213_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound214_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound215_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound216_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound217_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound218_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound219_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound21_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound220_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound221_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound222_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound223_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound224_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound225_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound226_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound227_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound228_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound229_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound22_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound230_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound231_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound232_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound233_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound234_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound235_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound236_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound237_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound238_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound239_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound23_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound240_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound241_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound242_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound243_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound244_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound245_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound246_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound247_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound248_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound249_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound24_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound250_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound251_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound252_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound253_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound254_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound26_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound27_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound28_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound29_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound2_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound30_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound31_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound32_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound34_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound35_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound36_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound37_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound38_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound39_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound3_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound40_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound41_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound42_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound43_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound44_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound45_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound46_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound47_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound49_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound4_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound50_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound51_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound52_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound53_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound54_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound55_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound56_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound58_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound59_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound5_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound60_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound61_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound62_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound63_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound64_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound65_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound66_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound67_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound69_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound6_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound70_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound72_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound73_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound74_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound75_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound76_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound77_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound78_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound79_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound7_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound80_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound81_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound82_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound83_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound84_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound85_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound86_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound87_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound88_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound89_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound8_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound90_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound91_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound92_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound93_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound94_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound95_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound96_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound97_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound98_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound99_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_rowSound9_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SamplingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

theorem unused_card {p n : ℕ} (e : Fin p ↪ Fin n)
    [Fintype {i // i ∉ Set.range e}] :
    Fintype.card {i // i ∉ Set.range e} = n - p := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {i // i ∈ Set.range e} = p := by
    rw [Fintype.card_range, Fintype.card_fin]
  rw [hr, Fintype.card_fin]

theorem embedding_succ_card (p n : ℕ) :
    Fintype.card (Fin (p + 1) ↪ Fin n) =
      Fintype.card (Fin p ↪ Fin n) * (n - p) := by
  rw [Fintype.card_congr (Equiv.embeddingFinSucc p (Fin n)), Fintype.card_sigma]
  simp only [unused_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem sum_dropFirst {p n : ℕ} (f : (Fin p ↪ Fin n) → ℝ) :
    (∑ e : Fin (p + 1) ↪ Fin n, f (dropFirst e)) =
      (n - p : ℕ) * ∑ e, f e := by
  have hs := sum_injective_extension (fun e (_ : Fin n) => f e)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin, Fintype.card_fin]

/-- Deleting a coordinate of a uniform injection leaves a uniform injection. -/
theorem average_dropFirst {p n : ℕ} (hp : p < n) (f : (Fin p ↪ Fin n) → ℝ) :
    average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e)) = average f := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  unfold average
  rw [embedding_succ_card, Nat.cast_mul, sum_dropFirst, mul_inv_rev]
  calc
    _ = (((n - p : ℕ) : ℝ)⁻¹ * (n - p : ℕ)) *
        ((Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ * ∑ e, f e) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

/-- At saturation the old labels exhaust the population, so only the occupied
contractions occur. This statement never defines a seven-row moment. -/
theorem saturated_average_contraction (n : ℕ)
    (f : (Fin n ↪ Fin n) → Fin n → ℝ) (h : ∀ e, ∑ b, f e b = 0) :
    (∑ j : Fin n, average (fun e : Fin n ↪ Fin n => f e (e j))) = 0 := by
  simp only [average]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs : (∑ e : Fin n ↪ Fin n, ∑ j : Fin n, f e (e j)) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have he : Function.Bijective e :=
      ⟨e.injective, Finite.surjective_of_injective e.injective⟩
    rw [he.sum_comp]
    exact h e
  rw [hs, mul_zero]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The seven-row boundary equation. All six terms are moments of six-row
matrices. There is no term for sampling seven distinct labels from six. -/
theorem injectiveMoment_seven_row_boundary {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin 7) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    (∑ j : Fin 6, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.saturated_average_contraction 6
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord => ∑ j : Fin 6,
      average (fun ρ : Fin 6 ↪ Coord => contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_occupied hH,
    contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3470 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3470 = injectiveMoment H node3017 := by
  calc
    injectiveMoment H raw3470 = injectiveMoment H raw3470step0 := by
      have heq : raw3470step0 = -raw3470 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3470).symm
    injectiveMoment H raw3470step0 = injectiveMoment H raw3470step1 := by
      have heq : raw3470step1 = (fun i j => raw3470step0 (permutation325 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3470step0 permutation325 permutation23
    _ = injectiveMoment H node3017 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7271 = injectiveMoment H node2878 := by
  calc
    injectiveMoment H raw7271 = injectiveMoment H raw7271step0 := by
      have heq : raw7271step0 = -raw7271 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7271).symm
    injectiveMoment H raw7271step0 = injectiveMoment H raw7271step1 := by
      have heq : raw7271step1 = (fun i j => raw7271step0 (permutation325 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7271step0 permutation325 permutation23
    _ = injectiveMoment H node2878 := by rfl

theorem canonical7272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7272 = injectiveMoment H node3011 := by
  calc
    injectiveMoment H raw7272 = injectiveMoment H raw7272step0 := by
      have heq : raw7272step0 = -raw7272 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7272).symm
    injectiveMoment H raw7272step0 = injectiveMoment H raw7272step1 := by
      have heq : raw7272step1 = (fun i j => raw7272step0 (permutation325 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7272step0 permutation325 permutation23
    _ = injectiveMoment H node3011 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7334 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7334 = injectiveMoment H node2878 := by
  calc
    injectiveMoment H raw7334 = injectiveMoment H raw7334step0 := by
      have heq : raw7334step0 = -raw7334 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7334).symm
    injectiveMoment H raw7334step0 = injectiveMoment H raw7334step1 := by
      have heq : raw7334step1 = (fun i j => raw7334step0 (permutation324 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7334step0 permutation324 permutation23
    _ = injectiveMoment H node2878 := by rfl

theorem canonical7335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7335 = injectiveMoment H node3012 := by
  calc
    injectiveMoment H raw7335 = injectiveMoment H raw7335step0 := by
      have heq : raw7335step0 = -raw7335 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7335).symm
    injectiveMoment H raw7335step0 = injectiveMoment H raw7335step1 := by
      have heq : raw7335step1 = (fun i j => raw7335step0 (permutation325 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7335step0 permutation325 permutation23
    _ = injectiveMoment H node3012 := by rfl

theorem canonical7336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7336 = injectiveMoment H node3439 := by
  calc
    injectiveMoment H raw7336 = injectiveMoment H raw7336step0 := by
      have heq : raw7336step0 = (fun i j => raw7336 (permutation152 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7336 permutation152 permutation11
    _ = injectiveMoment H node3439 := by rfl

theorem canonical7338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7338 = injectiveMoment H node3439 := by
  calc
    injectiveMoment H raw7338 = injectiveMoment H raw7338step0 := by
      have heq : raw7338step0 = (fun i j => raw7338 (permutation154 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7338 permutation154 permutation11
    _ = injectiveMoment H node3439 := by rfl

theorem canonical7339 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7339 = injectiveMoment H node2888 := by
  calc
    injectiveMoment H raw7339 = injectiveMoment H raw7339step0 := by
      have heq : raw7339step0 = -raw7339 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7339).symm
    injectiveMoment H raw7339step0 = injectiveMoment H raw7339step1 := by
      have heq : raw7339step1 = (fun i j => raw7339step0 (permutation324 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7339step0 permutation324 permutation23
    _ = injectiveMoment H node2888 := by rfl

theorem canonical7340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7340 = injectiveMoment H node3441 := by
  calc
    injectiveMoment H raw7340 = injectiveMoment H raw7340step0 := by
      have heq : raw7340step0 = (fun i j => raw7340 (permutation152 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7340 permutation152 permutation11
    _ = injectiveMoment H node3441 := by rfl

theorem canonical7341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7341 = injectiveMoment H node3441 := by
  calc
    injectiveMoment H raw7341 = injectiveMoment H raw7341step0 := by
      have heq : raw7341step0 = (fun i j => raw7341 (permutation154 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7341 permutation154 permutation11
    _ = injectiveMoment H node3441 := by rfl

theorem canonical7342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7342 = injectiveMoment H node3081 := by
  calc
    injectiveMoment H raw7342 = injectiveMoment H raw7342step0 := by
      have heq : raw7342step0 = (fun i j => raw7342 (permutation366 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7342 permutation366 permutation27
    _ = injectiveMoment H node3081 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8324 = injectiveMoment H node3195 := by
  calc
    injectiveMoment H raw8324 = injectiveMoment H raw8324step0 := by
      have heq : raw8324step0 = (fun i j => raw8324 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8324 permutation258 permutation9
    _ = injectiveMoment H node3195 := by rfl

theorem canonical8332 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8332 = injectiveMoment H node3170 := by
  calc
    injectiveMoment H raw8332 = injectiveMoment H raw8332step0 := by
      have heq : raw8332step0 = -raw8332 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8332).symm
    injectiveMoment H raw8332step0 = injectiveMoment H raw8332step1 := by
      have heq : raw8332step1 = (fun i j => raw8332step0 (permutation342 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8332step0 permutation342 permutation18
    _ = injectiveMoment H node3170 := by rfl

theorem canonical8333 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8333 = injectiveMoment H node3206 := by
  calc
    injectiveMoment H raw8333 = injectiveMoment H raw8333step0 := by
      have heq : raw8333step0 = (fun i j => raw8333 (permutation338 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8333 permutation338 permutation13
    _ = injectiveMoment H node3206 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical284
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9102 = injectiveMoment H node3296 := by
  calc
    injectiveMoment H raw9102 = injectiveMoment H raw9102step0 := by
      have heq : raw9102step0 = (fun i j => raw9102 (permutation278 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9102 permutation278 permutation10
    _ = injectiveMoment H node3296 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9144 = injectiveMoment H node3075 := by
  calc
    injectiveMoment H raw9144 = injectiveMoment H raw9144step0 := by
      have heq : raw9144step0 = (fun i j => raw9144 (permutation335 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9144 permutation335 permutation10
    _ = injectiveMoment H node3075 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical286
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9172 = injectiveMoment H node3149 := by
  calc
    injectiveMoment H raw9172 = injectiveMoment H raw9172step0 := by
      have heq : raw9172step0 = (fun i j => raw9172 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9172 permutation323 permutation16
    _ = injectiveMoment H node3149 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical288
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9219 = injectiveMoment H node3436 := by
  calc
    injectiveMoment H raw9219 = injectiveMoment H raw9219step0 := by
      have heq : raw9219step0 = (fun i j => raw9219 (permutation237 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9219 permutation237 permutation27
    _ = injectiveMoment H node3436 := by rfl

theorem canonical9220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9220 = injectiveMoment H node3442 := by
  calc
    injectiveMoment H raw9220 = injectiveMoment H raw9220step0 := by
      have heq : raw9220step0 = (fun i j => raw9220 (permutation291 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9220 permutation291 permutation30
    _ = injectiveMoment H node3442 := by rfl

theorem canonical9232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9232 = injectiveMoment H node3296 := by
  calc
    injectiveMoment H raw9232 = injectiveMoment H raw9232step0 := by
      have heq : raw9232step0 = (fun i j => raw9232 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9232 permutation259 permutation10
    _ = injectiveMoment H node3296 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical291
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9317 = injectiveMoment H node3213 := by
  calc
    injectiveMoment H raw9317 = injectiveMoment H raw9317step0 := by
      have heq : raw9317step0 = (fun i j => raw9317 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9317 permutation258 permutation9
    _ = injectiveMoment H node3213 := by rfl

theorem canonical9320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9320 = injectiveMoment H node3052 := by
  calc
    injectiveMoment H raw9320 = injectiveMoment H raw9320step0 := by
      have heq : raw9320step0 = (fun i j => raw9320 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9320 permutation258 permutation9
    _ = injectiveMoment H node3052 := by rfl

theorem canonical9322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9322 = injectiveMoment H node3447 := by
  calc
    injectiveMoment H raw9322 = injectiveMoment H raw9322step0 := by
      have heq : raw9322step0 = -raw9322 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9322).symm
    injectiveMoment H raw9322step0 = injectiveMoment H raw9322step1 := by
      have heq : raw9322step1 = (fun i j => raw9322step0 (permutation236 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9322step0 permutation236 permutation16
    _ = injectiveMoment H node3447 := by rfl

theorem canonical9324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9324 = injectiveMoment H node3042 := by
  calc
    injectiveMoment H raw9324 = injectiveMoment H raw9324step0 := by
      have heq : raw9324step0 = (fun i j => raw9324 (permutation393 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9324 permutation393 permutation29
    _ = injectiveMoment H node3042 := by rfl

theorem canonical9334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9334 = injectiveMoment H node3295 := by
  calc
    injectiveMoment H raw9334 = injectiveMoment H raw9334step0 := by
      have heq : raw9334step0 = (fun i j => raw9334 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9334 permutation259 permutation10
    _ = injectiveMoment H node3295 := by rfl

theorem canonical9336 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9336 = injectiveMoment H node3040 := by
  calc
    injectiveMoment H raw9336 = injectiveMoment H raw9336step0 := by
      have heq : raw9336step0 = -raw9336 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9336).symm
    injectiveMoment H raw9336step0 = injectiveMoment H raw9336step1 := by
      have heq : raw9336step1 = (fun i j => raw9336step0 (permutation387 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9336step0 permutation387 permutation21
    _ = injectiveMoment H node3040 := by rfl

theorem canonical9337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9337 = injectiveMoment H node3208 := by
  calc
    injectiveMoment H raw9337 = injectiveMoment H raw9337step0 := by
      have heq : raw9337step0 = (fun i j => raw9337 (permutation284 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9337 permutation284 permutation14
    _ = injectiveMoment H node3208 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical294
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9412 = injectiveMoment H node1800 := by
  calc
    injectiveMoment H raw9412 = injectiveMoment H raw9412step0 := by
      have hz : ∀ j, raw9412 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9412step0 = (fun i j => raw9412 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9412 permutation202 hz
    injectiveMoment H raw9412step0 = injectiveMoment H raw9412step1 := by
      have heq : raw9412step1 = (fun i j => raw9412step0 (permutation132 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9412step0 permutation132 permutation10
    _ = injectiveMoment H node1800 := by rfl

theorem canonical9421 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9421 = injectiveMoment H node3436 := by
  calc
    injectiveMoment H raw9421 = injectiveMoment H raw9421step0 := by
      have heq : raw9421step0 = (fun i j => raw9421 (permutation219 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9421 permutation219 permutation27
    _ = injectiveMoment H node3436 := by rfl

theorem canonical9422 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9422 = injectiveMoment H node3393 := by
  calc
    injectiveMoment H raw9422 = injectiveMoment H raw9422step0 := by
      have heq : raw9422step0 = -raw9422 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9422).symm
    injectiveMoment H raw9422step0 = injectiveMoment H raw9422step1 := by
      have heq : raw9422step1 = (fun i j => raw9422step0 (permutation349 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9422step0 permutation349 permutation18
    _ = injectiveMoment H node3393 := by rfl

theorem canonical9438 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9438 = injectiveMoment H node3166 := by
  calc
    injectiveMoment H raw9438 = injectiveMoment H raw9438step0 := by
      have heq : raw9438step0 = -raw9438 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9438).symm
    injectiveMoment H raw9438step0 = injectiveMoment H raw9438step1 := by
      have heq : raw9438step1 = (fun i j => raw9438step0 (permutation338 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9438step0 permutation338 permutation18
    _ = injectiveMoment H node3166 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical295
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9443 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9443 = injectiveMoment H node3167 := by
  calc
    injectiveMoment H raw9443 = injectiveMoment H raw9443step0 := by
      have heq : raw9443step0 = (fun i j => raw9443 (permutation337 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9443 permutation337 permutation14
    _ = injectiveMoment H node3167 := by rfl

theorem canonical9445 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9445 = injectiveMoment H node3393 := by
  calc
    injectiveMoment H raw9445 = injectiveMoment H raw9445step0 := by
      have heq : raw9445step0 = -raw9445 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9445).symm
    injectiveMoment H raw9445step0 = injectiveMoment H raw9445step1 := by
      have heq : raw9445step1 = (fun i j => raw9445step0 (permutation326 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9445step0 permutation326 permutation20
    _ = injectiveMoment H node3393 := by rfl

theorem canonical9464 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9464 = injectiveMoment H node3205 := by
  calc
    injectiveMoment H raw9464 = injectiveMoment H raw9464step0 := by
      have heq : raw9464step0 = (fun i j => raw9464 (permutation338 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9464 permutation338 permutation13
    _ = injectiveMoment H node3205 := by rfl

theorem canonical9470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9470 = injectiveMoment H node3433 := by
  calc
    injectiveMoment H raw9470 = injectiveMoment H raw9470step0 := by
      have heq : raw9470step0 = (fun i j => raw9470 (permutation219 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9470 permutation219 permutation27
    _ = injectiveMoment H node3433 := by rfl

theorem canonical9471 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9471 = injectiveMoment H node3442 := by
  calc
    injectiveMoment H raw9471 = injectiveMoment H raw9471step0 := by
      have heq : raw9471step0 = (fun i j => raw9471 (permutation250 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9471 permutation250 permutation20
    _ = injectiveMoment H node3442 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical297
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9519 = injectiveMoment H node3066 := by
  calc
    injectiveMoment H raw9519 = injectiveMoment H raw9519step0 := by
      have heq : raw9519step0 = (fun i j => raw9519 (permutation335 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9519 permutation335 permutation10
    _ = injectiveMoment H node3066 := by rfl

theorem canonical9532 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9532 = injectiveMoment H node3065 := by
  calc
    injectiveMoment H raw9532 = injectiveMoment H raw9532step0 := by
      have heq : raw9532step0 = (fun i j => raw9532 (permutation335 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9532 permutation335 permutation10
    _ = injectiveMoment H node3065 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical298
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9540 = injectiveMoment H node3067 := by
  calc
    injectiveMoment H raw9540 = injectiveMoment H raw9540step0 := by
      have heq : raw9540step0 = (fun i j => raw9540 (permutation335 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9540 permutation335 permutation10
    _ = injectiveMoment H node3067 := by rfl

theorem canonical9541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9541 = injectiveMoment H node3069 := by
  calc
    injectiveMoment H raw9541 = injectiveMoment H raw9541step0 := by
      have heq : raw9541step0 = (fun i j => raw9541 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9541 permutation312 permutation9
    _ = injectiveMoment H node3069 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical300
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9604 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9604 = injectiveMoment H node2968 := by
  calc
    injectiveMoment H raw9604 = injectiveMoment H raw9604step0 := by
      have heq : raw9604step0 = (fun i j => raw9604 (permutation383 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9604 permutation383 permutation19
    _ = injectiveMoment H node2968 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical303
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9712 = injectiveMoment H node2400 := by
  calc
    injectiveMoment H raw9712 = injectiveMoment H raw9712step0 := by
      have hz : ∀ j, raw9712 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9712step0 = (fun i j => raw9712 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9712 permutation151 hz
    injectiveMoment H raw9712step0 = injectiveMoment H raw9712step1 := by
      have heq : raw9712step1 = (fun i j => raw9712step0 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9712step0 permutation136 permutation21
    _ = injectiveMoment H node2400 := by rfl

theorem canonical9727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9727 = injectiveMoment H node2390 := by
  calc
    injectiveMoment H raw9727 = injectiveMoment H raw9727step0 := by
      have hz : ∀ j, raw9727 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9727step0 = (fun i j => raw9727 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9727 permutation151 hz
    injectiveMoment H raw9727step0 = injectiveMoment H raw9727step1 := by
      have heq : raw9727step1 = (fun i j => raw9727step0 (permutation128 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9727step0 permutation128 permutation21
    _ = injectiveMoment H node2390 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical287
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9211 = injectiveMoment H node3195 := by
  calc
    injectiveMoment H raw9211 = injectiveMoment H raw9211step0 := by
      have heq : raw9211step0 = (fun i j => raw9211 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9211 permutation277 permutation9
    _ = injectiveMoment H node3195 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical305
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9776 = injectiveMoment H node2400 := by
  calc
    injectiveMoment H raw9776 = injectiveMoment H raw9776step0 := by
      have hz : ∀ j, raw9776 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9776step0 = (fun i j => raw9776 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9776 permutation202 hz
    injectiveMoment H raw9776step0 = injectiveMoment H raw9776step1 := by
      have heq : raw9776step1 = (fun i j => raw9776step0 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9776step0 permutation136 permutation21
    _ = injectiveMoment H node2400 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9922 = injectiveMoment H node3334 := by
  calc
    injectiveMoment H raw9922 = injectiveMoment H raw9922step0 := by
      have heq : raw9922step0 = (fun i j => raw9922 (permutation340 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9922 permutation340 permutation21
    _ = injectiveMoment H node3334 := by rfl

theorem canonical9923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9923 = injectiveMoment H node2864 := by
  calc
    injectiveMoment H raw9923 = injectiveMoment H raw9923step0 := by
      have heq : raw9923step0 = (fun i j => raw9923 (permutation339 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9923 permutation339 permutation21
    _ = injectiveMoment H node2864 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical289
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9272 = injectiveMoment H node3351 := by
  calc
    injectiveMoment H raw9272 = injectiveMoment H raw9272step0 := by
      have heq : raw9272step0 = -raw9272 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9272).symm
    injectiveMoment H raw9272step0 = injectiveMoment H raw9272step1 := by
      have heq : raw9272step1 = (fun i j => raw9272step0 (permutation309 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9272step0 permutation309 permutation15
    _ = injectiveMoment H node3351 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical306
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9823 = injectiveMoment H node2920 := by
  calc
    injectiveMoment H raw9823 = injectiveMoment H raw9823step0 := by
      have heq : raw9823step0 = (fun i j => raw9823 (permutation355 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9823 permutation355 permutation11
    _ = injectiveMoment H node2920 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical307
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9840 = injectiveMoment H node2927 := by
  calc
    injectiveMoment H raw9840 = injectiveMoment H raw9840step0 := by
      have heq : raw9840step0 = (fun i j => raw9840 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9840 permutation308 permutation9
    _ = injectiveMoment H node2927 := by rfl

theorem canonical9843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9843 = injectiveMoment H node2928 := by
  calc
    injectiveMoment H raw9843 = injectiveMoment H raw9843step0 := by
      have heq : raw9843step0 = (fun i j => raw9843 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9843 permutation308 permutation9
    _ = injectiveMoment H node2928 := by rfl

theorem canonical9844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9844 = injectiveMoment H node2867 := by
  calc
    injectiveMoment H raw9844 = injectiveMoment H raw9844step0 := by
      have heq : raw9844step0 = (fun i j => raw9844 (permutation366 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9844 permutation366 permutation21
    _ = injectiveMoment H node2867 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical309
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9890 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9890 = injectiveMoment H node2913 := by
  calc
    injectiveMoment H raw9890 = injectiveMoment H raw9890step0 := by
      have heq : raw9890step0 = (fun i j => raw9890 (permutation337 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9890 permutation337 permutation11
    _ = injectiveMoment H node2913 := by rfl

theorem canonical9913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9913 = injectiveMoment H node2913 := by
  calc
    injectiveMoment H raw9913 = injectiveMoment H raw9913step0 := by
      have heq : raw9913step0 = (fun i j => raw9913 (permutation357 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9913 permutation357 permutation11
    _ = injectiveMoment H node2913 := by rfl

theorem canonical9919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9919 = injectiveMoment H node2927 := by
  calc
    injectiveMoment H raw9919 = injectiveMoment H raw9919step0 := by
      have heq : raw9919step0 = (fun i j => raw9919 (permutation337 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9919 permutation337 permutation11
    _ = injectiveMoment H node2927 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3452 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3452 = injectiveMoment H node2880 := by
  calc
    injectiveMoment H raw3452 = injectiveMoment H raw3452step0 := by
      have heq : raw3452step0 = -raw3452 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3452).symm
    injectiveMoment H raw3452step0 = injectiveMoment H raw3452step1 := by
      have heq : raw3452step1 = (fun i j => raw3452step0 (permutation324 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3452step0 permutation324 permutation23
    _ = injectiveMoment H node2880 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound11 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow11 (momentVector H) = 0 := by
  have hshape : boundaryMatrix11 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix11 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix11 (0 : Fin 6)) =
      Sparse.eval value3170 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (0 : Fin 6) = raw8332 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8332 hH).trans (sound3170_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix11 (1 : Fin 6)) =
      Sparse.eval value3436 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (1 : Fin 6) = raw9219 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9219 hH).trans (sound3436_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix11 (2 : Fin 6)) =
      Sparse.eval value3436 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (2 : Fin 6) = raw9421 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9421 hH).trans (sound3436_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix11 (3 : Fin 6)) =
      Sparse.eval value3166 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (3 : Fin 6) = raw9438 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9438 hH).trans (sound3166_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix11 (4 : Fin 6)) =
      Sparse.eval value3167 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (4 : Fin 6) = raw9443 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9443 hH).trans (sound3167_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix11 (5 : Fin 6)) =
      Sparse.eval value3393 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix11 (5 : Fin 6) = raw9445 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9445 hH).trans (sound3393_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix11 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix11 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow11, value3166, value3167, value3170, value3393, value3436, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

theorem boundarySound13 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow13 (momentVector H) = 0 := by
  have hshape : boundaryMatrix13 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix13 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix13 (0 : Fin 6)) =
      Sparse.eval value3206 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (0 : Fin 6) = raw8333 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8333 hH).trans (sound3206_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix13 (1 : Fin 6)) =
      Sparse.eval value3442 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (1 : Fin 6) = raw9220 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9220 hH).trans (sound3442_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix13 (2 : Fin 6)) =
      Sparse.eval value3393 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (2 : Fin 6) = raw9422 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9422 hH).trans (sound3393_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix13 (3 : Fin 6)) =
      Sparse.eval value3205 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (3 : Fin 6) = raw9464 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9464 hH).trans (sound3205_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix13 (4 : Fin 6)) =
      Sparse.eval value3433 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (4 : Fin 6) = raw9470 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9470 hH).trans (sound3433_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix13 (5 : Fin 6)) =
      Sparse.eval value3442 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix13 (5 : Fin 6) = raw9471 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9471 hH).trans (sound3442_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix13 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix13 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow13, value3205, value3206, value3393, value3433, value3442, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound302 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow302 (momentVector H) = 0 := by
  have hshape : boundaryMatrix302 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix302 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix302 (0 : Fin 6)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (0 : Fin 6) = raw9712 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9712 hH).trans (sound2400_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix302 (1 : Fin 6)) =
      Sparse.eval value2400 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (1 : Fin 6) = raw9776 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9776 hH).trans (sound2400_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix302 (2 : Fin 6)) =
      Sparse.eval value2920 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (2 : Fin 6) = raw9823 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9823 hH).trans (sound2920_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix302 (3 : Fin 6)) =
      Sparse.eval value2927 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (3 : Fin 6) = raw9840 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9840 hH).trans (sound2927_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix302 (4 : Fin 6)) =
      Sparse.eval value2928 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (4 : Fin 6) = raw9843 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9843 hH).trans (sound2928_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix302 (5 : Fin 6)) =
      Sparse.eval value2867 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix302 (5 : Fin 6) = raw9844 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9844 hH).trans (sound2867_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix302 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix302 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow302, value2400, value2867, value2920, value2927, value2928, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical302
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9676 = injectiveMoment H node3146 := by
  calc
    injectiveMoment H raw9676 = injectiveMoment H raw9676step0 := by
      have heq : raw9676step0 = (fun i j => raw9676 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9676 permutation323 permutation16
    _ = injectiveMoment H node3146 := by rfl

theorem canonical9680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9680 = injectiveMoment H node3001 := by
  calc
    injectiveMoment H raw9680 = injectiveMoment H raw9680step0 := by
      have heq : raw9680step0 = (fun i j => raw9680 (permutation363 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9680 permutation363 permutation19
    _ = injectiveMoment H node3001 := by rfl

theorem canonical9684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9684 = injectiveMoment H node3144 := by
  calc
    injectiveMoment H raw9684 = injectiveMoment H raw9684step0 := by
      have heq : raw9684step0 = (fun i j => raw9684 (permutation323 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9684 permutation323 permutation16
    _ = injectiveMoment H node3144 := by rfl

theorem canonical9685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9685 = injectiveMoment H node3174 := by
  calc
    injectiveMoment H raw9685 = injectiveMoment H raw9685step0 := by
      have heq : raw9685step0 = (fun i j => raw9685 (permutation383 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9685 permutation383 permutation19
    _ = injectiveMoment H node3174 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound306 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow306 (momentVector H) = 0 := by
  have hshape : boundaryMatrix306 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix306 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix306 (0 : Fin 6)) =
      Sparse.eval value2390 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (0 : Fin 6) = raw9727 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9727 hH).trans (sound2390_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix306 (1 : Fin 6)) =
      Sparse.eval value2913 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (1 : Fin 6) = raw9890 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9890 hH).trans (sound2913_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix306 (2 : Fin 6)) =
      Sparse.eval value2913 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (2 : Fin 6) = raw9913 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9913 hH).trans (sound2913_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix306 (3 : Fin 6)) =
      Sparse.eval value2927 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (3 : Fin 6) = raw9919 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9919 hH).trans (sound2927_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix306 (4 : Fin 6)) =
      Sparse.eval value3334 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (4 : Fin 6) = raw9922 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9922 hH).trans (sound3334_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix306 (5 : Fin 6)) =
      Sparse.eval value2864 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix306 (5 : Fin 6) = raw9923 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9923 hH).trans (sound2864_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix306 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix306 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow306, value2390, value2864, value2913, value2927, value3334, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary12
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound368 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow368 (momentVector H) = 0 := by
  have hshape : boundaryMatrix368 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix368 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix368 (0 : Fin 6)) =
      Sparse.eval value3195 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (0 : Fin 6) = raw8324 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8324 hH).trans (sound3195_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix368 (1 : Fin 6)) =
      Sparse.eval value3195 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (1 : Fin 6) = raw9211 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9211 hH).trans (sound3195_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix368 (2 : Fin 6)) =
      Sparse.eval value3351 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (2 : Fin 6) = raw9272 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9272 hH).trans (sound3351_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix368 (3 : Fin 6)) =
      Sparse.eval value3213 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (3 : Fin 6) = raw9317 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9317 hH).trans (sound3213_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix368 (4 : Fin 6)) =
      Sparse.eval value3052 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (4 : Fin 6) = raw9320 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9320 hH).trans (sound3052_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix368 (5 : Fin 6)) =
      Sparse.eval value3447 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix368 (5 : Fin 6) = raw9322 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9322 hH).trans (sound3447_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix368 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix368 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow368, value3052, value3195, value3213, value3351, value3447, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound34 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow34 (momentVector H) = 0 := by
  have hshape : boundaryMatrix34 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix34 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix34 (0 : Fin 6)) =
      Sparse.eval value3017 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (0 : Fin 6) = raw3470 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3470 hH).trans (sound3017_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix34 (1 : Fin 6)) =
      Sparse.eval value3011 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (1 : Fin 6) = raw7272 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7272 hH).trans (sound3011_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix34 (2 : Fin 6)) =
      Sparse.eval value3012 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (2 : Fin 6) = raw7335 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7335 hH).trans (sound3012_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix34 (3 : Fin 6)) =
      Sparse.eval value3441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (3 : Fin 6) = raw7340 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7340 hH).trans (sound3441_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix34 (4 : Fin 6)) =
      Sparse.eval value3441 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (4 : Fin 6) = raw7341 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7341 hH).trans (sound3441_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix34 (5 : Fin 6)) =
      Sparse.eval value3081 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix34 (5 : Fin 6) = raw7342 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7342 hH).trans (sound3081_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix34 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix34 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow34, value3011, value3012, value3017, value3081, value3441, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound79 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow79 (momentVector H) = 0 := by
  have hshape : boundaryMatrix79 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix79 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix79 (0 : Fin 6)) =
      Sparse.eval value2880 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (0 : Fin 6) = raw3452 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3452 hH).trans (sound2880_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix79 (1 : Fin 6)) =
      Sparse.eval value2878 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (1 : Fin 6) = raw7271 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7271 hH).trans (sound2878_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix79 (2 : Fin 6)) =
      Sparse.eval value2878 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (2 : Fin 6) = raw7334 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7334 hH).trans (sound2878_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix79 (3 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (3 : Fin 6) = raw7336 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7336 hH).trans (sound3439_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix79 (4 : Fin 6)) =
      Sparse.eval value3439 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (4 : Fin 6) = raw7338 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7338 hH).trans (sound3439_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix79 (5 : Fin 6)) =
      Sparse.eval value2888 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix79 (5 : Fin 6) = raw7339 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7339 hH).trans (sound2888_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix79 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix79 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow79, value2878, value2880, value2888, value3439, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary7
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound140 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow140 (momentVector H) = 0 := by
  have hshape : boundaryMatrix140 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix140 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix140 (0 : Fin 6)) =
      Sparse.eval value3296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (0 : Fin 6) = raw9102 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9102 hH).trans (sound3296_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix140 (1 : Fin 6)) =
      Sparse.eval value3296 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (1 : Fin 6) = raw9232 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9232 hH).trans (sound3296_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix140 (2 : Fin 6)) =
      Sparse.eval value3042 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (2 : Fin 6) = raw9324 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9324 hH).trans (sound3042_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix140 (3 : Fin 6)) =
      Sparse.eval value3295 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (3 : Fin 6) = raw9334 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9334 hH).trans (sound3295_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix140 (4 : Fin 6)) =
      Sparse.eval value3040 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (4 : Fin 6) = raw9336 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9336 hH).trans (sound3040_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix140 (5 : Fin 6)) =
      Sparse.eval value3208 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix140 (5 : Fin 6) = raw9337 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9337 hH).trans (sound3208_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix140 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix140 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow140, value3040, value3042, value3208, value3295, value3296, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

theorem boundarySound162 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow162 (momentVector H) = 0 := by
  have hshape : boundaryMatrix162 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix162 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix162 (0 : Fin 6)) =
      Sparse.eval value3075 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (0 : Fin 6) = raw9144 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9144 hH).trans (sound3075_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix162 (1 : Fin 6)) =
      Sparse.eval value1800 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (1 : Fin 6) = raw9412 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9412 hH).trans (sound1800_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix162 (2 : Fin 6)) =
      Sparse.eval value3066 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (2 : Fin 6) = raw9519 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9519 hH).trans (sound3066_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix162 (3 : Fin 6)) =
      Sparse.eval value3065 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (3 : Fin 6) = raw9532 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9532 hH).trans (sound3065_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix162 (4 : Fin 6)) =
      Sparse.eval value3067 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (4 : Fin 6) = raw9540 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9540 hH).trans (sound3067_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix162 (5 : Fin 6)) =
      Sparse.eval value3069 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix162 (5 : Fin 6) = raw9541 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9541 hH).trans (sound3069_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix162 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix162 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow162, value1800, value3065, value3066, value3067, value3069, value3075, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary8
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound168 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow168 (momentVector H) = 0 := by
  have hshape : boundaryMatrix168 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix168 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix168 (0 : Fin 6)) =
      Sparse.eval value3149 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (0 : Fin 6) = raw9172 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9172 hH).trans (sound3149_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix168 (1 : Fin 6)) =
      Sparse.eval value2968 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (1 : Fin 6) = raw9604 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9604 hH).trans (sound2968_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix168 (2 : Fin 6)) =
      Sparse.eval value3146 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (2 : Fin 6) = raw9676 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9676 hH).trans (sound3146_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix168 (3 : Fin 6)) =
      Sparse.eval value3001 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (3 : Fin 6) = raw9680 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9680 hH).trans (sound3001_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix168 (4 : Fin 6)) =
      Sparse.eval value3144 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (4 : Fin 6) = raw9684 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9684 hH).trans (sound3144_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix168 (5 : Fin 6)) =
      Sparse.eval value3174 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix168 (5 : Fin 6) = raw9685 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9685 hH).trans (sound3174_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix168 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix168 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow168, value2968, value3001, value3144, value3146, value3149, value3174, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck11 : Integer.Sparse.reindex coordinateMap (PairData.rows 11) =
    PairSemantics.boundaryRow11 := by decide +kernel

theorem rowSound11 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 11) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck11]
  exact PairSemantics.boundarySound11 hH

theorem rowCheck13 : Integer.Sparse.reindex coordinateMap (PairData.rows 13) =
    PairSemantics.boundaryRow13 := by decide +kernel

theorem rowSound13 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 13) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck13]
  exact PairSemantics.boundarySound13 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck25 : Integer.Sparse.reindex coordinateMap (PairData.rows 25) =
    PairSemantics.boundaryRow26 := by decide +kernel

theorem rowSound25 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 25) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck25]
  exact PairSemantics.boundarySound26_e hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck169 : Integer.Sparse.reindex coordinateMap (PairData.rows 169) =
    PairSemantics.boundaryRow302 := by decide +kernel

theorem rowSound169 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 169) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck169]
  exact PairSemantics.boundarySound302 hH

theorem rowCheck173 : Integer.Sparse.reindex coordinateMap (PairData.rows 173) =
    PairSemantics.boundaryRow306 := by decide +kernel

theorem rowSound173 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 173) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck173]
  exact PairSemantics.boundarySound306 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck201 : Integer.Sparse.reindex coordinateMap (PairData.rows 201) =
    PairSemantics.boundaryRow368 := by decide +kernel

theorem rowSound201 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 201) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck201]
  exact PairSemantics.boundarySound368 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck33 : Integer.Sparse.reindex coordinateMap (PairData.rows 33) =
    PairSemantics.boundaryRow34 := by decide +kernel

theorem rowSound33 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 33) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck33]
  exact PairSemantics.boundarySound34 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck48 : Integer.Sparse.reindex coordinateMap (PairData.rows 48) =
    PairSemantics.boundaryRow49 := by decide +kernel

theorem rowSound48 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 48) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck48]
  exact PairSemantics.boundarySound49_e hH

theorem rowCheck57 : Integer.Sparse.reindex coordinateMap (PairData.rows 57) =
    PairSemantics.boundaryRow58 := by decide +kernel

theorem rowSound57 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 57) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck57]
  exact PairSemantics.boundarySound58_e hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck68 : Integer.Sparse.reindex coordinateMap (PairData.rows 68) =
    PairSemantics.boundaryRow73 := by decide +kernel

theorem rowSound68 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 68) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck68]
  exact PairSemantics.boundarySound73_e hH

theorem rowCheck71 : Integer.Sparse.reindex coordinateMap (PairData.rows 71) =
    PairSemantics.boundaryRow79 := by decide +kernel

theorem rowSound71 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 71) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck71]
  exact PairSemantics.boundarySound79 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck109 : Integer.Sparse.reindex coordinateMap (PairData.rows 109) =
    PairSemantics.boundaryRow140 := by decide +kernel

theorem rowSound109 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 109) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck109]
  exact PairSemantics.boundarySound140 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck122 : Integer.Sparse.reindex coordinateMap (PairData.rows 122) =
    PairSemantics.boundaryRow162 := by decide +kernel

theorem rowSound122 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 122) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck122]
  exact PairSemantics.boundarySound162 hH

theorem rowCheck126 : Integer.Sparse.reindex coordinateMap (PairData.rows 126) =
    PairSemantics.boundaryRow168 := by decide +kernel

theorem rowSound126 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 126) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck126]
  exact PairSemantics.boundarySound168 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem allRowsSound_e_oai {H : CMatrix} (hH : IsHadamard H) (k : Fin 255) :
    Integer.Sparse.eval (PairData.rows k) (momentVector H) = 0 := by
  fin_cases k
  · exact rowSound0_e hH
  · exact rowSound1_e hH
  · exact rowSound2_e hH
  · exact rowSound3_e hH
  · exact rowSound4_e hH
  · exact rowSound5_e hH
  · exact rowSound6_e hH
  · exact rowSound7_e hH
  · exact rowSound8_e hH
  · exact rowSound9_e hH
  · exact rowSound10_e hH
  · exact rowSound11 hH
  · exact rowSound12_e hH
  · exact rowSound13 hH
  · exact rowSound14_e hH
  · exact rowSound15_e hH
  · exact rowSound16_e hH
  · exact rowSound17_e hH
  · exact rowSound18_e hH
  · exact rowSound19_e hH
  · exact rowSound20_e hH
  · exact rowSound21_e hH
  · exact rowSound22_e hH
  · exact rowSound23_e hH
  · exact rowSound24_e hH
  · exact rowSound25 hH
  · exact rowSound26_e hH
  · exact rowSound27_e hH
  · exact rowSound28_e hH
  · exact rowSound29_e hH
  · exact rowSound30_e hH
  · exact rowSound31_e hH
  · exact rowSound32_e hH
  · exact rowSound33 hH
  · exact rowSound34_e hH
  · exact rowSound35_e hH
  · exact rowSound36_e hH
  · exact rowSound37_e hH
  · exact rowSound38_e hH
  · exact rowSound39_e hH
  · exact rowSound40_e hH
  · exact rowSound41_e hH
  · exact rowSound42_e hH
  · exact rowSound43_e hH
  · exact rowSound44_e hH
  · exact rowSound45_e hH
  · exact rowSound46_e hH
  · exact rowSound47_e hH
  · exact rowSound48 hH
  · exact rowSound49_e hH
  · exact rowSound50_e hH
  · exact rowSound51_e hH
  · exact rowSound52_e hH
  · exact rowSound53_e hH
  · exact rowSound54_e hH
  · exact rowSound55_e hH
  · exact rowSound56_e hH
  · exact rowSound57 hH
  · exact rowSound58_e hH
  · exact rowSound59_e hH
  · exact rowSound60_e hH
  · exact rowSound61_e hH
  · exact rowSound62_e hH
  · exact rowSound63_e hH
  · exact rowSound64_e hH
  · exact rowSound65_e hH
  · exact rowSound66_e hH
  · exact rowSound67_e hH
  · exact rowSound68 hH
  · exact rowSound69_e hH
  · exact rowSound70_e hH
  · exact rowSound71 hH
  · exact rowSound72_e hH
  · exact rowSound73_e hH
  · exact rowSound74_e hH
  · exact rowSound75_e hH
  · exact rowSound76_e hH
  · exact rowSound77_e hH
  · exact rowSound78_e hH
  · exact rowSound79_e hH
  · exact rowSound80_e hH
  · exact rowSound81_e hH
  · exact rowSound82_e hH
  · exact rowSound83_e hH
  · exact rowSound84_e hH
  · exact rowSound85_e hH
  · exact rowSound86_e hH
  · exact rowSound87_e hH
  · exact rowSound88_e hH
  · exact rowSound89_e hH
  · exact rowSound90_e hH
  · exact rowSound91_e hH
  · exact rowSound92_e hH
  · exact rowSound93_e hH
  · exact rowSound94_e hH
  · exact rowSound95_e hH
  · exact rowSound96_e hH
  · exact rowSound97_e hH
  · exact rowSound98_e hH
  · exact rowSound99_e hH
  · exact rowSound100_e hH
  · exact rowSound101_e hH
  · exact rowSound102_e hH
  · exact rowSound103_e hH
  · exact rowSound104_e hH
  · exact rowSound105_e hH
  · exact rowSound106_e hH
  · exact rowSound107_e hH
  · exact rowSound108_e hH
  · exact rowSound109 hH
  · exact rowSound110_e hH
  · exact rowSound111_e hH
  · exact rowSound112_e hH
  · exact rowSound113_e hH
  · exact rowSound114_e hH
  · exact rowSound115_e hH
  · exact rowSound116_e hH
  · exact rowSound117_e hH
  · exact rowSound118_e hH
  · exact rowSound119_e hH
  · exact rowSound120_e hH
  · exact rowSound121_e hH
  · exact rowSound122 hH
  · exact rowSound123_e hH
  · exact rowSound124_e hH
  · exact rowSound125_e hH
  · exact rowSound126 hH
  · exact rowSound127_e hH
  · exact rowSound128_e hH
  · exact rowSound129_e hH
  · exact rowSound130_e hH
  · exact rowSound131_e hH
  · exact rowSound132_e hH
  · exact rowSound133_e hH
  · exact rowSound134_e hH
  · exact rowSound135_e hH
  · exact rowSound136_e hH
  · exact rowSound137_e hH
  · exact rowSound138_e hH
  · exact rowSound139_e hH
  · exact rowSound140_e hH
  · exact rowSound141_e hH
  · exact rowSound142_e hH
  · exact rowSound143_e hH
  · exact rowSound144_e hH
  · exact rowSound145_e hH
  · exact rowSound146_e hH
  · exact rowSound147_e hH
  · exact rowSound148_e hH
  · exact rowSound149_e hH
  · exact rowSound150_e hH
  · exact rowSound151_e hH
  · exact rowSound152_e hH
  · exact rowSound153_e hH
  · exact rowSound154_e hH
  · exact rowSound155_e hH
  · exact rowSound156_e hH
  · exact rowSound157_e hH
  · exact rowSound158_e hH
  · exact rowSound159_e hH
  · exact rowSound160_e hH
  · exact rowSound161_e hH
  · exact rowSound162_e hH
  · exact rowSound163_e hH
  · exact rowSound164_e hH
  · exact rowSound165_e hH
  · exact rowSound166_e hH
  · exact rowSound167_e hH
  · exact rowSound168_e hH
  · exact rowSound169 hH
  · exact rowSound170_e hH
  · exact rowSound171_e hH
  · exact rowSound172_e hH
  · exact rowSound173 hH
  · exact rowSound174_e hH
  · exact rowSound175_e hH
  · exact rowSound176_e hH
  · exact rowSound177_e hH
  · exact rowSound178_e hH
  · exact rowSound179_e hH
  · exact rowSound180_e hH
  · exact rowSound181_e hH
  · exact rowSound182_e hH
  · exact rowSound183_e hH
  · exact rowSound184_e hH
  · exact rowSound185_e hH
  · exact rowSound186_e hH
  · exact rowSound187_e hH
  · exact rowSound188_e hH
  · exact rowSound189_e hH
  · exact rowSound190_e hH
  · exact rowSound191_e hH
  · exact rowSound192_e hH
  · exact rowSound193_e hH
  · exact rowSound194_e hH
  · exact rowSound195_e hH
  · exact rowSound196_e hH
  · exact rowSound197_e hH
  · exact rowSound198_e hH
  · exact rowSound199_e hH
  · exact rowSound200_e hH
  · exact rowSound201 hH
  · exact rowSound202_e hH
  · exact rowSound203_e hH
  · exact rowSound204_e hH
  · exact rowSound205_e hH
  · exact rowSound206_e hH
  · exact rowSound207_e hH
  · exact rowSound208_e hH
  · exact rowSound209_e hH
  · exact rowSound210_e hH
  · exact rowSound211_e hH
  · exact rowSound212_e hH
  · exact rowSound213_e hH
  · exact rowSound214_e hH
  · exact rowSound215_e hH
  · exact rowSound216_e hH
  · exact rowSound217_e hH
  · exact rowSound218_e hH
  · exact rowSound219_e hH
  · exact rowSound220_e hH
  · exact rowSound221_e hH
  · exact rowSound222_e hH
  · exact rowSound223_e hH
  · exact rowSound224_e hH
  · exact rowSound225_e hH
  · exact rowSound226_e hH
  · exact rowSound227_e hH
  · exact rowSound228_e hH
  · exact rowSound229_e hH
  · exact rowSound230_e hH
  · exact rowSound231_e hH
  · exact rowSound232_e hH
  · exact rowSound233_e hH
  · exact rowSound234_e hH
  · exact rowSound235_e hH
  · exact rowSound236_e hH
  · exact rowSound237_e hH
  · exact rowSound238_e hH
  · exact rowSound239_e hH
  · exact rowSound240_e hH
  · exact rowSound241_e hH
  · exact rowSound242_e hH
  · exact rowSound243_e hH
  · exact rowSound244_e hH
  · exact rowSound245_e hH
  · exact rowSound246_e hH
  · exact rowSound247_e hH
  · exact rowSound248_e hH
  · exact rowSound249_e hH
  · exact rowSound250_e hH
  · exact rowSound251_e hH
  · exact rowSound252_e hH
  · exact rowSound253_e hH
  · exact rowSound254_e hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e_oai
