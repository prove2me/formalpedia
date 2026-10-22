-- Prove2me | solution 1 for HardyCapset20261020.hyperplane_completion_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T18:25:47.111788+00:00
-- url     : https://prove2.me/submissions/ac3636a2-da01-450a-a1cf-574342aa4add

import Definitions.Def_HardyCapsetOrbitVerifier20261021
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Theorems.Thm_HardyCapset20261020_Cert_generator00_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_generator01_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_generator02_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_generator03_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_generator04_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_generator05_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_generator06_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_generator07_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_generator08_preserves_baseline
import Theorems.Thm_HardyCapset20261020_Cert_case000_bound
import Theorems.Thm_HardyCapset20261020_Cert_case001_bound
import Theorems.Thm_HardyCapset20261020_Cert_case002_bound
import Theorems.Thm_HardyCapset20261020_Cert_case003_bound
import Theorems.Thm_HardyCapset20261020_Cert_case004_bound
import Theorems.Thm_HardyCapset20261020_Cert_case005_bound
import Theorems.Thm_HardyCapset20261020_Cert_case006_bound
import Theorems.Thm_HardyCapset20261020_Cert_case007_bound
import Theorems.Thm_HardyCapset20261020_Cert_case008_bound
import Theorems.Thm_HardyCapset20261020_Cert_case009_bound
import Theorems.Thm_HardyCapset20261020_Cert_case010_bound
import Theorems.Thm_HardyCapset20261020_Cert_case011_bound
import Theorems.Thm_HardyCapset20261020_Cert_case012_bound
import Theorems.Thm_HardyCapset20261020_Cert_case013_bound
import Theorems.Thm_HardyCapset20261020_Cert_case014_bound
import Theorems.Thm_HardyCapset20261020_Cert_case015_bound
import Theorems.Thm_HardyCapset20261020_Cert_case016_bound
import Theorems.Thm_HardyCapset20261020_Cert_case017_bound
import Theorems.Thm_HardyCapset20261020_Cert_case018_bound
import Theorems.Thm_HardyCapset20261020_Cert_case019_bound
import Theorems.Thm_HardyCapset20261020_Cert_case020_bound
import Theorems.Thm_HardyCapset20261020_Cert_case021_bound
import Theorems.Thm_HardyCapset20261020_Cert_case022_bound
import Theorems.Thm_HardyCapset20261020_Cert_case023_bound
import Theorems.Thm_HardyCapset20261020_Cert_case024_bound
import Theorems.Thm_HardyCapset20261020_Cert_case025_bound
import Theorems.Thm_HardyCapset20261020_Cert_case026_bound
import Theorems.Thm_HardyCapset20261020_Cert_case027_bound
import Theorems.Thm_HardyCapset20261020_Cert_case028_bound
import Theorems.Thm_HardyCapset20261020_Cert_case029_bound
import Theorems.Thm_HardyCapset20261020_Cert_case030_bound
import Theorems.Thm_HardyCapset20261020_Cert_case031_bound
import Theorems.Thm_HardyCapset20261020_Cert_case032_bound
import Theorems.Thm_HardyCapset20261020_Cert_case033_bound
import Theorems.Thm_HardyCapset20261020_Cert_case034_bound
import Theorems.Thm_HardyCapset20261020_Cert_case035_bound
import Theorems.Thm_HardyCapset20261020_Cert_case036_bound
import Theorems.Thm_HardyCapset20261020_Cert_case037_bound
import Theorems.Thm_HardyCapset20261020_Cert_case038_bound
import Theorems.Thm_HardyCapset20261020_Cert_case039_bound
import Theorems.Thm_HardyCapset20261020_Cert_case040_bound
import Theorems.Thm_HardyCapset20261020_Cert_case041_bound
import Theorems.Thm_HardyCapset20261020_Cert_case042_bound
import Theorems.Thm_HardyCapset20261020_Cert_case043_bound
import Theorems.Thm_HardyCapset20261020_Cert_case044_bound
import Theorems.Thm_HardyCapset20261020_Cert_case045_bound
import Theorems.Thm_HardyCapset20261020_Cert_case046_bound
import Theorems.Thm_HardyCapset20261020_Cert_case047_bound
import Theorems.Thm_HardyCapset20261020_Cert_case048_bound
import Theorems.Thm_HardyCapset20261020_Cert_case049_bound
import Theorems.Thm_HardyCapset20261020_Cert_case050_bound
import Theorems.Thm_HardyCapset20261020_Cert_case051_bound
import Theorems.Thm_HardyCapset20261020_Cert_case052_bound
import Theorems.Thm_HardyCapset20261020_Cert_case053_bound
import Theorems.Thm_HardyCapset20261020_Cert_case054_bound
import Theorems.Thm_HardyCapset20261020_Cert_case055_bound
import Theorems.Thm_HardyCapset20261020_Cert_case056_bound
import Theorems.Thm_HardyCapset20261020_Cert_case057_bound
import Theorems.Thm_HardyCapset20261020_Cert_case058_bound
import Theorems.Thm_HardyCapset20261020_Cert_case059_bound
import Theorems.Thm_HardyCapset20261020_Cert_case060_bound
import Theorems.Thm_HardyCapset20261020_Cert_case061_bound
import Theorems.Thm_HardyCapset20261020_Cert_case062_bound
import Theorems.Thm_HardyCapset20261020_Cert_case063_bound
import Theorems.Thm_HardyCapset20261020_Cert_case064_bound
import Theorems.Thm_HardyCapset20261020_Cert_case065_bound
import Theorems.Thm_HardyCapset20261020_Cert_case066_bound
import Theorems.Thm_HardyCapset20261020_Cert_case067_bound
import Theorems.Thm_HardyCapset20261020_Cert_case068_bound
import Theorems.Thm_HardyCapset20261020_Cert_case069_bound
import Theorems.Thm_HardyCapset20261020_Cert_case070_bound
import Theorems.Thm_HardyCapset20261020_Cert_case071_bound
import Theorems.Thm_HardyCapset20261020_Cert_case072_bound
import Theorems.Thm_HardyCapset20261020_Cert_case073_bound
import Theorems.Thm_HardyCapset20261020_Cert_case074_bound
import Theorems.Thm_HardyCapset20261020_Cert_case075_bound
import Theorems.Thm_HardyCapset20261020_Cert_case076_bound
import Theorems.Thm_HardyCapset20261020_Cert_case077_bound
import Theorems.Thm_HardyCapset20261020_Cert_case078_bound
import Theorems.Thm_HardyCapset20261020_Cert_case079_bound
import Theorems.Thm_HardyCapset20261020_Cert_case080_bound
import Theorems.Thm_HardyCapset20261020_Cert_case081_bound
import Theorems.Thm_HardyCapset20261020_Cert_case082_bound
import Theorems.Thm_HardyCapset20261020_Cert_case083_bound
import Theorems.Thm_HardyCapset20261020_Cert_case084_bound
import Theorems.Thm_HardyCapset20261020_Cert_case085_bound
import Theorems.Thm_HardyCapset20261020_Cert_case086_bound
import Theorems.Thm_HardyCapset20261020_Cert_case087_bound
import Theorems.Thm_HardyCapset20261020_Cert_case088_bound
import Theorems.Thm_HardyCapset20261020_Cert_case089_bound
import Theorems.Thm_HardyCapset20261020_Cert_case090_bound
import Theorems.Thm_HardyCapset20261020_Cert_case091_bound
import Theorems.Thm_HardyCapset20261020_Cert_case092_bound
import Theorems.Thm_HardyCapset20261020_Cert_case093_bound
import Theorems.Thm_HardyCapset20261020_Cert_case094_bound
import Theorems.Thm_HardyCapset20261020_Cert_case095_bound
import Theorems.Thm_HardyCapset20261020_Cert_case096_bound
import Theorems.Thm_HardyCapset20261020_Cert_case097_bound
import Theorems.Thm_HardyCapset20261020_Cert_case098_bound
import Theorems.Thm_HardyCapset20261020_Cert_case099_bound
import Theorems.Thm_HardyCapset20261020_Cert_case100_bound
import Theorems.Thm_HardyCapset20261020_Cert_case101_bound
import Theorems.Thm_HardyCapset20261020_Cert_case102_bound
import Theorems.Thm_HardyCapset20261020_Cert_case103_bound
import Theorems.Thm_HardyCapset20261020_Cert_case104_bound
import Theorems.Thm_HardyCapset20261020_Cert_case105_bound
import Theorems.Thm_HardyCapset20261020_Cert_case106_bound
import Theorems.Thm_HardyCapset20261020_Cert_case107_bound
import Theorems.Thm_HardyCapset20261020_Cert_case108_bound
import Theorems.Thm_HardyCapset20261020_Cert_case109_bound
import Theorems.Thm_HardyCapset20261020_Cert_case110_bound
import Theorems.Thm_HardyCapset20261020_Cert_case111_bound
import Theorems.Thm_HardyCapset20261020_Cert_case112_bound
import Theorems.Thm_HardyCapset20261020_Cert_case113_bound
import Theorems.Thm_HardyCapset20261020_Cert_case114_bound
import Theorems.Thm_HardyCapset20261020_Cert_case115_bound
import Theorems.Thm_HardyCapset20261020_Cert_case116_bound
import Theorems.Thm_HardyCapset20261020_Cert_case117_bound
import Theorems.Thm_HardyCapset20261020_Cert_case118_bound
import Theorems.Thm_HardyCapset20261020_Cert_case119_bound
import Theorems.Thm_HardyCapset20261020_Cert_case120_bound
import Theorems.Thm_HardyCapset20261020_Cert_case121_bound
import Theorems.Thm_HardyCapset20261020_Cert_case122_bound
import Theorems.Thm_HardyCapset20261020_Cert_case123_bound
import Theorems.Thm_HardyCapset20261020_Cert_case124_bound
import Theorems.Thm_HardyCapset20261020_Cert_case125_bound
import Theorems.Thm_HardyCapset20261020_Cert_case126_bound
import Theorems.Thm_HardyCapset20261020_Cert_case127_bound
import Theorems.Thm_HardyCapset20261020_Cert_case128_bound
import Theorems.Thm_HardyCapset20261020_Cert_case129_bound
import Theorems.Thm_HardyCapset20261020_Cert_case130_bound
import Theorems.Thm_HardyCapset20261020_Cert_case131_bound
import Theorems.Thm_HardyCapset20261020_Cert_case132_bound
import Theorems.Thm_HardyCapset20261020_Cert_case133_bound
import Theorems.Thm_HardyCapset20261020_Cert_case134_bound
import Theorems.Thm_HardyCapset20261020_Cert_case135_bound
import Theorems.Thm_HardyCapset20261020_Cert_case136_bound
import Theorems.Thm_HardyCapset20261020_Cert_case137_bound
import Theorems.Thm_HardyCapset20261020_Cert_case138_bound
import Theorems.Thm_HardyCapset20261020_Cert_case139_bound
import Theorems.Thm_HardyCapset20261020_Cert_case140_bound
import Theorems.Thm_HardyCapset20261020_Cert_case141_bound
import Theorems.Thm_HardyCapset20261020_Cert_case142_bound
import Theorems.Thm_HardyCapset20261020_Cert_case143_bound
import Theorems.Thm_HardyCapset20261020_Cert_case144_bound
import Theorems.Thm_HardyCapset20261020_Cert_case145_bound
import Theorems.Thm_HardyCapset20261020_Cert_case146_bound
import Theorems.Thm_HardyCapset20261020_Cert_case147_bound
import Theorems.Thm_HardyCapset20261020_Cert_case148_bound
import Theorems.Thm_HardyCapset20261020_Cert_case149_bound
import Theorems.Thm_HardyCapset20261020_Cert_case150_bound
import Theorems.Thm_HardyCapset20261020_Cert_case151_bound
import Theorems.Thm_HardyCapset20261020_Cert_case152_bound
import Theorems.Thm_HardyCapset20261020_Cert_case153_bound
import Theorems.Thm_HardyCapset20261020_Cert_case154_bound
import Theorems.Thm_HardyCapset20261020_Cert_case155_bound
import Theorems.Thm_HardyCapset20261020_Cert_case156_bound
import Theorems.Thm_HardyCapset20261020_Cert_case157_bound
import Theorems.Thm_HardyCapset20261020_Cert_case158_bound
import Theorems.Thm_HardyCapset20261020_Cert_case159_bound
import Theorems.Thm_HardyCapset20261020_Cert_case160_bound
import Theorems.Thm_HardyCapset20261020_Cert_case161_bound
import Theorems.Thm_HardyCapset20261020_Cert_case162_bound
import Theorems.Thm_HardyCapset20261020_Cert_case163_bound
import Theorems.Thm_HardyCapset20261020_Cert_case164_bound
import Theorems.Thm_HardyCapset20261020_Cert_case165_bound
import Theorems.Thm_HardyCapset20261020_Cert_case166_bound
import Theorems.Thm_HardyCapset20261020_Cert_case167_bound
import Theorems.Thm_HardyCapset20261020_Cert_case168_bound
import Theorems.Thm_HardyCapset20261020_Cert_case169_bound
import Theorems.Thm_HardyCapset20261020_Cert_case170_bound
import Theorems.Thm_HardyCapset20261020_Cert_case171_bound
import Theorems.Thm_HardyCapset20261020_Cert_case172_bound
import Theorems.Thm_HardyCapset20261020_Cert_case173_bound
import Theorems.Thm_HardyCapset20261020_Cert_case174_bound
import Theorems.Thm_HardyCapset20261020_Cert_case175_bound
import Theorems.Thm_HardyCapset20261020_Cert_case176_bound
import Theorems.Thm_HardyCapset20261020_Cert_case177_bound
import Theorems.Thm_HardyCapset20261020_Cert_case178_bound
import Theorems.Thm_HardyCapset20261020_Cert_case179_bound
import Theorems.Thm_HardyCapset20261020_Cert_case180_bound
import Theorems.Thm_HardyCapset20261020_Cert_case181_bound
import Theorems.Thm_HardyCapset20261020_Cert_case182_bound
import Theorems.Thm_HardyCapset20261020_Cert_case183_bound
import Theorems.Thm_HardyCapset20261020_Cert_case184_bound
import Theorems.Thm_HardyCapset20261020_Cert_case185_bound
import Theorems.Thm_HardyCapset20261020_Cert_case186_bound
import Theorems.Thm_HardyCapset20261020_Cert_case187_bound
import Theorems.Thm_HardyCapset20261020_Cert_case188_bound
import Theorems.Thm_HardyCapset20261020_Cert_case189_bound
import Theorems.Thm_HardyCapset20261020_Cert_case190_bound
import Theorems.Thm_HardyCapset20261020_Cert_case191_bound
import Theorems.Thm_HardyCapset20261020_Cert_case192_bound
import Theorems.Thm_HardyCapset20261020_Cert_case193_bound
import Theorems.Thm_HardyCapset20261020_Cert_case194_bound
import Theorems.Thm_HardyCapset20261020_Cert_case195_bound
import Theorems.Thm_HardyCapset20261020_Cert_case196_bound
import Theorems.Thm_HardyCapset20261020_Cert_case197_bound
import Theorems.Thm_HardyCapset20261020_Cert_case198_bound
import Theorems.Thm_HardyCapset20261020_Cert_case199_bound
import Theorems.Thm_HardyCapset20261020_Cert_case200_bound
import Theorems.Thm_HardyCapset20261020_Cert_case201_bound
import Theorems.Thm_HardyCapset20261020_Cert_case202_bound
import Theorems.Thm_HardyCapset20261020_Cert_case203_bound
import Theorems.Thm_HardyCapset20261020_Cert_case204_bound
import Theorems.Thm_HardyCapset20261020_Cert_case205_bound
import Theorems.Thm_HardyCapset20261020_Cert_case206_bound
import Theorems.Thm_HardyCapset20261020_Cert_case207_bound
import Theorems.Thm_HardyCapset20261020_Cert_case208_bound
import Theorems.Thm_HardyCapset20261020_Cert_case209_bound
import Theorems.Thm_HardyCapset20261020_Cert_case210_bound
import Theorems.Thm_HardyCapset20261020_Cert_case211_bound
import Theorems.Thm_HardyCapset20261020_Cert_case212_bound
import Theorems.Thm_HardyCapset20261020_Cert_case213_bound
import Theorems.Thm_HardyCapset20261020_Cert_case214_bound
import Theorems.Thm_HardyCapset20261020_Cert_case215_bound
import Theorems.Thm_HardyCapset20261020_Cert_case216_bound
import Theorems.Thm_HardyCapset20261020_Cert_case217_bound
import Theorems.Thm_HardyCapset20261020_Cert_case218_bound
import Theorems.Thm_HardyCapset20261020_Cert_case219_bound
import Theorems.Thm_HardyCapset20261020_Cert_case220_bound
import Theorems.Thm_HardyCapset20261020_Cert_case221_bound
import Theorems.Thm_HardyCapset20261020_Cert_case222_bound
import Theorems.Thm_HardyCapset20261020_Cert_case223_bound
import Theorems.Thm_HardyCapset20261020_Cert_case224_bound
import Theorems.Thm_HardyCapset20261020_Cert_case225_bound
import Theorems.Thm_HardyCapset20261020_Cert_case226_bound
import Theorems.Thm_HardyCapset20261020_Cert_case227_bound
import Theorems.Thm_HardyCapset20261020_Cert_case228_bound
import Theorems.Thm_HardyCapset20261020_Cert_case229_bound
import Theorems.Thm_HardyCapset20261020_Cert_case230_bound
import Theorems.Thm_HardyCapset20261020_Cert_case231_bound
import Theorems.Thm_HardyCapset20261020_Cert_case232_bound
import Theorems.Thm_HardyCapset20261020_Cert_case233_bound
import Theorems.Thm_HardyCapset20261020_Cert_case234_bound
import Theorems.Thm_HardyCapset20261020_Cert_case235_bound
import Theorems.Thm_HardyCapset20261020_Cert_case236_bound
import Theorems.Thm_HardyCapset20261020_Cert_case237_bound
import Theorems.Thm_HardyCapset20261020_Cert_case238_bound
import Theorems.Thm_HardyCapset20261020_Cert_case239_bound
import Theorems.Thm_HardyCapset20261020_Cert_case240_bound
import Theorems.Thm_HardyCapset20261020_Cert_case241_bound
import Theorems.Thm_HardyCapset20261020_Cert_case242_bound
import Theorems.Thm_HardyCapset20261020_Cert_case243_bound
import Theorems.Thm_HardyCapset20261020_Cert_case244_bound
import Theorems.Thm_HardyCapset20261020_Cert_case245_bound
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage00
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage01
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage02
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage03
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage04
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage05
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage06
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage07
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage08
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage09
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage10
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage11
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage12
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage13
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage14
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage15
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage16
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage17
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage18
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage19
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage20
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage21
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage22
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage23
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage24
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage25
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage26
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage27
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage28
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage29
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage30
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage31
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage32
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage33
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage34
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage35
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage36
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage37
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage38
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage39
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage40
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage41
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage42
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage43
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage44
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage45
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage46
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage47
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage48
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage49
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage50
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage51
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage52
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage53
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage54
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage55
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage56
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage57
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage58
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage59
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage60
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage61
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage62
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage63
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage64
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage65
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage66
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage67
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage68
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage69
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage70
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage71
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage72
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage73
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage74
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage75
import Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage76
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
theorem decode_inj (q r : ℕ) (hq : q < 6561) (hr : r < 6561)
    (h : decode q = decode r) : q = r := by
  have h0 := congrArg (fun p : Point => (p 0).val) h
  have h1 := congrArg (fun p : Point => (p 1).val) h
  have h2 := congrArg (fun p : Point => (p 2).val) h
  have h3 := congrArg (fun p : Point => (p 3).val) h
  have h4 := congrArg (fun p : Point => (p 4).val) h
  have h5 := congrArg (fun p : Point => (p 5).val) h
  have h6 := congrArg (fun p : Point => (p 6).val) h
  have h7 := congrArg (fun p : Point => (p 7).val) h
  norm_num [decode, ZMod.val_natCast] at h0 h1 h2 h3 h4 h5 h6 h7
  omega

theorem decode_surjective : Function.Surjective (fun q : Fin 6561 => decode q.val) := by
  have hinj : Function.Injective (fun q : Fin 6561 => decode q.val) := by
    intro q r h
    apply Fin.ext
    exact decode_inj q.val r.val q.isLt r.isLt h
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩).2
  norm_num [Point, Fintype.card_pi]

end HardyCapset20261020.Cert
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace HardyCapset20261020.Cert

theorem signed_orthogonal (π : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3)
    (hs : ∀ i, s i * s i = 1) : Orthogonal (signedEquiv π s hs) := by
  intro n x
  change (∑ i, (s i * n (π i)) * (s i * x (π i))) = ∑ i, n i * x i
  calc
    _ = ∑ i : Fin 8, n (π i) * x (π i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_mul_mul_comm, hs, one_mul]
    _ = ∑ i : Fin 8, n i * x i := Equiv.sum_comp π (fun i => n i * x i)

theorem orthogonal_refl : Orthogonal (AddEquiv.refl Point) := by
  intro n x
  rfl

theorem orthogonal_trans (g h : Point ≃+ Point)
    (hg : Orthogonal g) (hh : Orthogonal h) : Orthogonal (g.trans h) := by
  intro n x
  exact (hh (g n) (g x)).trans (hg n x)

theorem preserves_refl : PreservesBaseline (AddEquiv.refl Point) := by
  simp [PreservesBaseline]

theorem preserves_trans (g h : Point ≃+ Point)
    (hg : PreservesBaseline g) (hh : PreservesBaseline h) :
    PreservesBaseline (g.trans h) := by
  unfold PreservesBaseline at *
  have he : (g.trans h : Point → Point) = h ∘ g := rfl
  rw [he, ← Finset.image_image, hg, hh]

theorem preserves_of_list (g : Point ≃+ Point) (l : List ℕ)
    (hp : l.Perm baselineIds)
    (hm : (baselineIds.map decode).map g = l.map decode) : PreservesBaseline g := by
  unfold PreservesBaseline
  calc
    baseline.image g = ((baselineIds.map decode).map g).toFinset := by
      ext x
      simp [baseline]
    _ = (l.map decode).toFinset := congrArg List.toFinset hm
    _ = baseline := by
      ext x
      change x ∈ (l.map decode).toFinset ↔ x ∈ (baselineIds.map decode).toFinset
      simp only [List.mem_toFinset]
      exact (hp.map decode).mem_iff

theorem word_orthogonal (generators : Array (Point ≃+ Point))
    (h : ∀ i : Fin generators.size, Orthogonal generators[i]) :
    ∀ w : List ℕ, Orthogonal (wordMap generators w) := by
  intro w
  induction w with
  | nil => exact orthogonal_refl
  | cons i rest ih =>
      apply orthogonal_trans _ _ ih
      by_cases hi : i < generators.size
      · simpa [genGet, hi] using h ⟨i, hi⟩
      · simpa [genGet, hi] using orthogonal_refl

theorem word_preserves (generators : Array (Point ≃+ Point))
    (h : ∀ i : Fin generators.size, PreservesBaseline generators[i]) :
    ∀ w : List ℕ, PreservesBaseline (wordMap generators w) := by
  intro w
  induction w with
  | nil => exact preserves_refl
  | cons i rest ih =>
      apply preserves_trans _ _ ih
      by_cases hi : i < generators.size
      · simpa [genGet, hi] using h ⟨i, hi⟩
      · simpa [genGet, hi] using preserves_refl

theorem bound_transport (g : Point ≃+ Point) (hg : Orthogonal g)
    (hS : PreservesBaseline g) (n n' : Point) (t t' a : ZMod 3)
    (ha : a ≠ 0) (hn : n' = a • g n) (ht : t' = a * t)
    (hbound : CompletionBound n t) : CompletionBound n' t' := by
  intro A hA hcore
  let A' := A.image g.symm
  have hmem : ∀ x : Point, x ∈ A' ↔ g x ∈ A := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      simpa [← he] using hy
    · intro hx
      apply Finset.mem_image.mpr
      exact ⟨g x, hx, g.symm_apply_apply x⟩
  have hcap : IsCap A' := by
    intro x hx y hy z hz hxy hxz hyz hline
    apply hA (g x) ((hmem x).mp hx) (g y) ((hmem y).mp hy)
      (g z) ((hmem z).mp hz)
      (fun h => hxy (g.injective h)) (fun h => hxz (g.injective h))
      (fun h => hyz (g.injective h))
    have h := congrArg g hline
    simpa only [map_add, map_zero] using h
  have hfix : core n t ⊆ A' := by
    intro x hx
    obtain ⟨hxS, hxH⟩ := Finset.mem_sdiff.mp hx
    apply (hmem x).mpr
    apply hcore
    apply Finset.mem_sdiff.mpr
    constructor
    · have hm : g x ∈ baseline.image g := Finset.mem_image.mpr ⟨x, hxS, rfl⟩
      rw [show baseline.image g = baseline from hS] at hm
      exact hm
    · intro hH
      apply hxH
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hd : dot n' (g x) = a * dot n x := by
        rw [hn]
        simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
        exact congrArg (fun z => a * z) (hg n x)
      have heq : a * dot n x = a * t := by
        rw [← hd]
        exact (Finset.mem_filter.mp hH).2.trans ht
      have hinv : a * a = 1 := by
        have h : ∀ b : ZMod 3, b ≠ 0 → b * b = 1 := by decide
        exact h a ha
      have hh := congrArg (fun z => a * z) heq
      simpa only [← mul_assoc, hinv, one_mul, dot] using hh
  have hb := hbound A' hcap hfix
  simpa [A', Finset.card_image_of_injective _ g.symm.injective] using hb

end HardyCapset20261020.Cert
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HardyCapset20261020.Cert

theorem completion_from_orbits
    (horth : ∀ i : Fin generators.size, Orthogonal generators[i])
    (hpres : ∀ i : Fin generators.size, PreservesBaseline generators[i])
    (hreps : ∀ r : Fin 246,
      CompletionBound (decode (entry representativeNormals r.val))
        (entry representativeLevels r.val))
    (hcover : ∀ (q : Fin 6561) (t : Fin 3), q.val ≠ 0 →
      ∃ (r : Fin 246) (w : List ℕ) (a : ZMod 3), a ≠ 0 ∧
        decode q.val = a • wordMap generators w (decode (entry representativeNormals r.val)) ∧
        (t.val : ZMod 3) = a * (entry representativeLevels r.val : ZMod 3))
    (n : Point) (hn : n ≠ 0) (t : ZMod 3) : CompletionBound n t := by
  obtain ⟨q, hq⟩ := decode_surjective n
  change decode q.val = n at hq
  have hzero : decode 0 = (0 : Point) := by
    funext i
    simp [decode]
  have hqn : q.val ≠ 0 := by
    intro h
    apply hn
    rw [← hq, h, hzero]
  obtain ⟨r, w, a, ha, heq, hlevel⟩ := hcover q ⟨t.val, t.val_lt⟩ hqn
  have ht : (t.val : ZMod 3) = t := ZMod.natCast_zmod_val t
  apply bound_transport (wordMap generators w)
    (word_orthogonal _ horth w) (word_preserves _ hpres w)
    (decode (entry representativeNormals r.val)) n
    (entry representativeLevels r.val) t a ha
  · exact hq.symm.trans heq
  · exact ht.symm.trans hlevel
  · exact hreps r

end HardyCapset20261020.Cert
namespace HardyCapset20261020.Cert
private theorem every_orbit_index (q : Fin 19680) : OrbitCovered q.val := by
  by_cases h0 : q.val < 256
  · simpa only [Nat.zero_add] using orbit_coverage00 ⟨q.val,h0⟩
  by_cases h1 : q.val < 512
  · have hl : 256 ≤ q.val := by omega
    have he : 256 + (q.val-256) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage01 ⟨q.val-256,by omega⟩
  by_cases h2 : q.val < 768
  · have hl : 512 ≤ q.val := by omega
    have he : 512 + (q.val-512) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage02 ⟨q.val-512,by omega⟩
  by_cases h3 : q.val < 1024
  · have hl : 768 ≤ q.val := by omega
    have he : 768 + (q.val-768) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage03 ⟨q.val-768,by omega⟩
  by_cases h4 : q.val < 1280
  · have hl : 1024 ≤ q.val := by omega
    have he : 1024 + (q.val-1024) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage04 ⟨q.val-1024,by omega⟩
  by_cases h5 : q.val < 1536
  · have hl : 1280 ≤ q.val := by omega
    have he : 1280 + (q.val-1280) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage05 ⟨q.val-1280,by omega⟩
  by_cases h6 : q.val < 1792
  · have hl : 1536 ≤ q.val := by omega
    have he : 1536 + (q.val-1536) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage06 ⟨q.val-1536,by omega⟩
  by_cases h7 : q.val < 2048
  · have hl : 1792 ≤ q.val := by omega
    have he : 1792 + (q.val-1792) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage07 ⟨q.val-1792,by omega⟩
  by_cases h8 : q.val < 2304
  · have hl : 2048 ≤ q.val := by omega
    have he : 2048 + (q.val-2048) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage08 ⟨q.val-2048,by omega⟩
  by_cases h9 : q.val < 2560
  · have hl : 2304 ≤ q.val := by omega
    have he : 2304 + (q.val-2304) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage09 ⟨q.val-2304,by omega⟩
  by_cases h10 : q.val < 2816
  · have hl : 2560 ≤ q.val := by omega
    have he : 2560 + (q.val-2560) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage10 ⟨q.val-2560,by omega⟩
  by_cases h11 : q.val < 3072
  · have hl : 2816 ≤ q.val := by omega
    have he : 2816 + (q.val-2816) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage11 ⟨q.val-2816,by omega⟩
  by_cases h12 : q.val < 3328
  · have hl : 3072 ≤ q.val := by omega
    have he : 3072 + (q.val-3072) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage12 ⟨q.val-3072,by omega⟩
  by_cases h13 : q.val < 3584
  · have hl : 3328 ≤ q.val := by omega
    have he : 3328 + (q.val-3328) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage13 ⟨q.val-3328,by omega⟩
  by_cases h14 : q.val < 3840
  · have hl : 3584 ≤ q.val := by omega
    have he : 3584 + (q.val-3584) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage14 ⟨q.val-3584,by omega⟩
  by_cases h15 : q.val < 4096
  · have hl : 3840 ≤ q.val := by omega
    have he : 3840 + (q.val-3840) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage15 ⟨q.val-3840,by omega⟩
  by_cases h16 : q.val < 4352
  · have hl : 4096 ≤ q.val := by omega
    have he : 4096 + (q.val-4096) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage16 ⟨q.val-4096,by omega⟩
  by_cases h17 : q.val < 4608
  · have hl : 4352 ≤ q.val := by omega
    have he : 4352 + (q.val-4352) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage17 ⟨q.val-4352,by omega⟩
  by_cases h18 : q.val < 4864
  · have hl : 4608 ≤ q.val := by omega
    have he : 4608 + (q.val-4608) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage18 ⟨q.val-4608,by omega⟩
  by_cases h19 : q.val < 5120
  · have hl : 4864 ≤ q.val := by omega
    have he : 4864 + (q.val-4864) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage19 ⟨q.val-4864,by omega⟩
  by_cases h20 : q.val < 5376
  · have hl : 5120 ≤ q.val := by omega
    have he : 5120 + (q.val-5120) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage20 ⟨q.val-5120,by omega⟩
  by_cases h21 : q.val < 5632
  · have hl : 5376 ≤ q.val := by omega
    have he : 5376 + (q.val-5376) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage21 ⟨q.val-5376,by omega⟩
  by_cases h22 : q.val < 5888
  · have hl : 5632 ≤ q.val := by omega
    have he : 5632 + (q.val-5632) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage22 ⟨q.val-5632,by omega⟩
  by_cases h23 : q.val < 6144
  · have hl : 5888 ≤ q.val := by omega
    have he : 5888 + (q.val-5888) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage23 ⟨q.val-5888,by omega⟩
  by_cases h24 : q.val < 6400
  · have hl : 6144 ≤ q.val := by omega
    have he : 6144 + (q.val-6144) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage24 ⟨q.val-6144,by omega⟩
  by_cases h25 : q.val < 6656
  · have hl : 6400 ≤ q.val := by omega
    have he : 6400 + (q.val-6400) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage25 ⟨q.val-6400,by omega⟩
  by_cases h26 : q.val < 6912
  · have hl : 6656 ≤ q.val := by omega
    have he : 6656 + (q.val-6656) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage26 ⟨q.val-6656,by omega⟩
  by_cases h27 : q.val < 7168
  · have hl : 6912 ≤ q.val := by omega
    have he : 6912 + (q.val-6912) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage27 ⟨q.val-6912,by omega⟩
  by_cases h28 : q.val < 7424
  · have hl : 7168 ≤ q.val := by omega
    have he : 7168 + (q.val-7168) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage28 ⟨q.val-7168,by omega⟩
  by_cases h29 : q.val < 7680
  · have hl : 7424 ≤ q.val := by omega
    have he : 7424 + (q.val-7424) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage29 ⟨q.val-7424,by omega⟩
  by_cases h30 : q.val < 7936
  · have hl : 7680 ≤ q.val := by omega
    have he : 7680 + (q.val-7680) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage30 ⟨q.val-7680,by omega⟩
  by_cases h31 : q.val < 8192
  · have hl : 7936 ≤ q.val := by omega
    have he : 7936 + (q.val-7936) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage31 ⟨q.val-7936,by omega⟩
  by_cases h32 : q.val < 8448
  · have hl : 8192 ≤ q.val := by omega
    have he : 8192 + (q.val-8192) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage32 ⟨q.val-8192,by omega⟩
  by_cases h33 : q.val < 8704
  · have hl : 8448 ≤ q.val := by omega
    have he : 8448 + (q.val-8448) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage33 ⟨q.val-8448,by omega⟩
  by_cases h34 : q.val < 8960
  · have hl : 8704 ≤ q.val := by omega
    have he : 8704 + (q.val-8704) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage34 ⟨q.val-8704,by omega⟩
  by_cases h35 : q.val < 9216
  · have hl : 8960 ≤ q.val := by omega
    have he : 8960 + (q.val-8960) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage35 ⟨q.val-8960,by omega⟩
  by_cases h36 : q.val < 9472
  · have hl : 9216 ≤ q.val := by omega
    have he : 9216 + (q.val-9216) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage36 ⟨q.val-9216,by omega⟩
  by_cases h37 : q.val < 9728
  · have hl : 9472 ≤ q.val := by omega
    have he : 9472 + (q.val-9472) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage37 ⟨q.val-9472,by omega⟩
  by_cases h38 : q.val < 9984
  · have hl : 9728 ≤ q.val := by omega
    have he : 9728 + (q.val-9728) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage38 ⟨q.val-9728,by omega⟩
  by_cases h39 : q.val < 10240
  · have hl : 9984 ≤ q.val := by omega
    have he : 9984 + (q.val-9984) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage39 ⟨q.val-9984,by omega⟩
  by_cases h40 : q.val < 10496
  · have hl : 10240 ≤ q.val := by omega
    have he : 10240 + (q.val-10240) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage40 ⟨q.val-10240,by omega⟩
  by_cases h41 : q.val < 10752
  · have hl : 10496 ≤ q.val := by omega
    have he : 10496 + (q.val-10496) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage41 ⟨q.val-10496,by omega⟩
  by_cases h42 : q.val < 11008
  · have hl : 10752 ≤ q.val := by omega
    have he : 10752 + (q.val-10752) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage42 ⟨q.val-10752,by omega⟩
  by_cases h43 : q.val < 11264
  · have hl : 11008 ≤ q.val := by omega
    have he : 11008 + (q.val-11008) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage43 ⟨q.val-11008,by omega⟩
  by_cases h44 : q.val < 11520
  · have hl : 11264 ≤ q.val := by omega
    have he : 11264 + (q.val-11264) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage44 ⟨q.val-11264,by omega⟩
  by_cases h45 : q.val < 11776
  · have hl : 11520 ≤ q.val := by omega
    have he : 11520 + (q.val-11520) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage45 ⟨q.val-11520,by omega⟩
  by_cases h46 : q.val < 12032
  · have hl : 11776 ≤ q.val := by omega
    have he : 11776 + (q.val-11776) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage46 ⟨q.val-11776,by omega⟩
  by_cases h47 : q.val < 12288
  · have hl : 12032 ≤ q.val := by omega
    have he : 12032 + (q.val-12032) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage47 ⟨q.val-12032,by omega⟩
  by_cases h48 : q.val < 12544
  · have hl : 12288 ≤ q.val := by omega
    have he : 12288 + (q.val-12288) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage48 ⟨q.val-12288,by omega⟩
  by_cases h49 : q.val < 12800
  · have hl : 12544 ≤ q.val := by omega
    have he : 12544 + (q.val-12544) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage49 ⟨q.val-12544,by omega⟩
  by_cases h50 : q.val < 13056
  · have hl : 12800 ≤ q.val := by omega
    have he : 12800 + (q.val-12800) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage50 ⟨q.val-12800,by omega⟩
  by_cases h51 : q.val < 13312
  · have hl : 13056 ≤ q.val := by omega
    have he : 13056 + (q.val-13056) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage51 ⟨q.val-13056,by omega⟩
  by_cases h52 : q.val < 13568
  · have hl : 13312 ≤ q.val := by omega
    have he : 13312 + (q.val-13312) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage52 ⟨q.val-13312,by omega⟩
  by_cases h53 : q.val < 13824
  · have hl : 13568 ≤ q.val := by omega
    have he : 13568 + (q.val-13568) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage53 ⟨q.val-13568,by omega⟩
  by_cases h54 : q.val < 14080
  · have hl : 13824 ≤ q.val := by omega
    have he : 13824 + (q.val-13824) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage54 ⟨q.val-13824,by omega⟩
  by_cases h55 : q.val < 14336
  · have hl : 14080 ≤ q.val := by omega
    have he : 14080 + (q.val-14080) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage55 ⟨q.val-14080,by omega⟩
  by_cases h56 : q.val < 14592
  · have hl : 14336 ≤ q.val := by omega
    have he : 14336 + (q.val-14336) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage56 ⟨q.val-14336,by omega⟩
  by_cases h57 : q.val < 14848
  · have hl : 14592 ≤ q.val := by omega
    have he : 14592 + (q.val-14592) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage57 ⟨q.val-14592,by omega⟩
  by_cases h58 : q.val < 15104
  · have hl : 14848 ≤ q.val := by omega
    have he : 14848 + (q.val-14848) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage58 ⟨q.val-14848,by omega⟩
  by_cases h59 : q.val < 15360
  · have hl : 15104 ≤ q.val := by omega
    have he : 15104 + (q.val-15104) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage59 ⟨q.val-15104,by omega⟩
  by_cases h60 : q.val < 15616
  · have hl : 15360 ≤ q.val := by omega
    have he : 15360 + (q.val-15360) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage60 ⟨q.val-15360,by omega⟩
  by_cases h61 : q.val < 15872
  · have hl : 15616 ≤ q.val := by omega
    have he : 15616 + (q.val-15616) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage61 ⟨q.val-15616,by omega⟩
  by_cases h62 : q.val < 16128
  · have hl : 15872 ≤ q.val := by omega
    have he : 15872 + (q.val-15872) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage62 ⟨q.val-15872,by omega⟩
  by_cases h63 : q.val < 16384
  · have hl : 16128 ≤ q.val := by omega
    have he : 16128 + (q.val-16128) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage63 ⟨q.val-16128,by omega⟩
  by_cases h64 : q.val < 16640
  · have hl : 16384 ≤ q.val := by omega
    have he : 16384 + (q.val-16384) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage64 ⟨q.val-16384,by omega⟩
  by_cases h65 : q.val < 16896
  · have hl : 16640 ≤ q.val := by omega
    have he : 16640 + (q.val-16640) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage65 ⟨q.val-16640,by omega⟩
  by_cases h66 : q.val < 17152
  · have hl : 16896 ≤ q.val := by omega
    have he : 16896 + (q.val-16896) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage66 ⟨q.val-16896,by omega⟩
  by_cases h67 : q.val < 17408
  · have hl : 17152 ≤ q.val := by omega
    have he : 17152 + (q.val-17152) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage67 ⟨q.val-17152,by omega⟩
  by_cases h68 : q.val < 17664
  · have hl : 17408 ≤ q.val := by omega
    have he : 17408 + (q.val-17408) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage68 ⟨q.val-17408,by omega⟩
  by_cases h69 : q.val < 17920
  · have hl : 17664 ≤ q.val := by omega
    have he : 17664 + (q.val-17664) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage69 ⟨q.val-17664,by omega⟩
  by_cases h70 : q.val < 18176
  · have hl : 17920 ≤ q.val := by omega
    have he : 17920 + (q.val-17920) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage70 ⟨q.val-17920,by omega⟩
  by_cases h71 : q.val < 18432
  · have hl : 18176 ≤ q.val := by omega
    have he : 18176 + (q.val-18176) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage71 ⟨q.val-18176,by omega⟩
  by_cases h72 : q.val < 18688
  · have hl : 18432 ≤ q.val := by omega
    have he : 18432 + (q.val-18432) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage72 ⟨q.val-18432,by omega⟩
  by_cases h73 : q.val < 18944
  · have hl : 18688 ≤ q.val := by omega
    have he : 18688 + (q.val-18688) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage73 ⟨q.val-18688,by omega⟩
  by_cases h74 : q.val < 19200
  · have hl : 18944 ≤ q.val := by omega
    have he : 18944 + (q.val-18944) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage74 ⟨q.val-18944,by omega⟩
  by_cases h75 : q.val < 19456
  · have hl : 19200 ≤ q.val := by omega
    have he : 19200 + (q.val-19200) = q.val := Nat.add_sub_of_le hl
    simpa only [he] using orbit_coverage75 ⟨q.val-19200,by omega⟩
  have hl : 19456 ≤ q.val := by omega
  have he : 19456 + (q.val-19456) = q.val := Nat.add_sub_of_le hl
  simpa only [he] using orbit_coverage76 ⟨q.val-19456,by omega⟩
end HardyCapset20261020.Cert
open HardyCapset20261020 HardyCapset20261020.Cert
theorem solution (n : Point) (hn : n ≠ 0) (t : ZMod 3) : CompletionBound n t := by
  have ho : forall i : Fin generators.size, Orthogonal generators[i] := by
    intro i
    fin_cases i <;> exact signed_orthogonal _ _ (by intro j; fin_cases j <;> decide)
  have hp : forall i : Fin generators.size, PreservesBaseline generators[i] := by
    intro i
    fin_cases i
    · exact generator00_preserves_baseline
    · exact generator01_preserves_baseline
    · exact generator02_preserves_baseline
    · exact generator03_preserves_baseline
    · exact generator04_preserves_baseline
    · exact generator05_preserves_baseline
    · exact generator06_preserves_baseline
    · exact generator07_preserves_baseline
    · exact generator08_preserves_baseline
  have hr : forall r : Fin 246, CompletionBound (decode (entry representativeNormals r.val)) (entry representativeLevels r.val) := by
    intro r
    fin_cases r
    · exact case000_bound
    · exact case001_bound
    · exact case002_bound
    · exact case003_bound
    · exact case004_bound
    · exact case005_bound
    · exact case006_bound
    · exact case007_bound
    · exact case008_bound
    · exact case009_bound
    · exact case010_bound
    · exact case011_bound
    · exact case012_bound
    · exact case013_bound
    · exact case014_bound
    · exact case015_bound
    · exact case016_bound
    · exact case017_bound
    · exact case018_bound
    · exact case019_bound
    · exact case020_bound
    · exact case021_bound
    · exact case022_bound
    · exact case023_bound
    · exact case024_bound
    · exact case025_bound
    · exact case026_bound
    · exact case027_bound
    · exact case028_bound
    · exact case029_bound
    · exact case030_bound
    · exact case031_bound
    · exact case032_bound
    · exact case033_bound
    · exact case034_bound
    · exact case035_bound
    · exact case036_bound
    · exact case037_bound
    · exact case038_bound
    · exact case039_bound
    · exact case040_bound
    · exact case041_bound
    · exact case042_bound
    · exact case043_bound
    · exact case044_bound
    · exact case045_bound
    · exact case046_bound
    · exact case047_bound
    · exact case048_bound
    · exact case049_bound
    · exact case050_bound
    · exact case051_bound
    · exact case052_bound
    · exact case053_bound
    · exact case054_bound
    · exact case055_bound
    · exact case056_bound
    · exact case057_bound
    · exact case058_bound
    · exact case059_bound
    · exact case060_bound
    · exact case061_bound
    · exact case062_bound
    · exact case063_bound
    · exact case064_bound
    · exact case065_bound
    · exact case066_bound
    · exact case067_bound
    · exact case068_bound
    · exact case069_bound
    · exact case070_bound
    · exact case071_bound
    · exact case072_bound
    · exact case073_bound
    · exact case074_bound
    · exact case075_bound
    · exact case076_bound
    · exact case077_bound
    · exact case078_bound
    · exact case079_bound
    · exact case080_bound
    · exact case081_bound
    · exact case082_bound
    · exact case083_bound
    · exact case084_bound
    · exact case085_bound
    · exact case086_bound
    · exact case087_bound
    · exact case088_bound
    · exact case089_bound
    · exact case090_bound
    · exact case091_bound
    · exact case092_bound
    · exact case093_bound
    · exact case094_bound
    · exact case095_bound
    · exact case096_bound
    · exact case097_bound
    · exact case098_bound
    · exact case099_bound
    · exact case100_bound
    · exact case101_bound
    · exact case102_bound
    · exact case103_bound
    · exact case104_bound
    · exact case105_bound
    · exact case106_bound
    · exact case107_bound
    · exact case108_bound
    · exact case109_bound
    · exact case110_bound
    · exact case111_bound
    · exact case112_bound
    · exact case113_bound
    · exact case114_bound
    · exact case115_bound
    · exact case116_bound
    · exact case117_bound
    · exact case118_bound
    · exact case119_bound
    · exact case120_bound
    · exact case121_bound
    · exact case122_bound
    · exact case123_bound
    · exact case124_bound
    · exact case125_bound
    · exact case126_bound
    · exact case127_bound
    · exact case128_bound
    · exact case129_bound
    · exact case130_bound
    · exact case131_bound
    · exact case132_bound
    · exact case133_bound
    · exact case134_bound
    · exact case135_bound
    · exact case136_bound
    · exact case137_bound
    · exact case138_bound
    · exact case139_bound
    · exact case140_bound
    · exact case141_bound
    · exact case142_bound
    · exact case143_bound
    · exact case144_bound
    · exact case145_bound
    · exact case146_bound
    · exact case147_bound
    · exact case148_bound
    · exact case149_bound
    · exact case150_bound
    · exact case151_bound
    · exact case152_bound
    · exact case153_bound
    · exact case154_bound
    · exact case155_bound
    · exact case156_bound
    · exact case157_bound
    · exact case158_bound
    · exact case159_bound
    · exact case160_bound
    · exact case161_bound
    · exact case162_bound
    · exact case163_bound
    · exact case164_bound
    · exact case165_bound
    · exact case166_bound
    · exact case167_bound
    · exact case168_bound
    · exact case169_bound
    · exact case170_bound
    · exact case171_bound
    · exact case172_bound
    · exact case173_bound
    · exact case174_bound
    · exact case175_bound
    · exact case176_bound
    · exact case177_bound
    · exact case178_bound
    · exact case179_bound
    · exact case180_bound
    · exact case181_bound
    · exact case182_bound
    · exact case183_bound
    · exact case184_bound
    · exact case185_bound
    · exact case186_bound
    · exact case187_bound
    · exact case188_bound
    · exact case189_bound
    · exact case190_bound
    · exact case191_bound
    · exact case192_bound
    · exact case193_bound
    · exact case194_bound
    · exact case195_bound
    · exact case196_bound
    · exact case197_bound
    · exact case198_bound
    · exact case199_bound
    · exact case200_bound
    · exact case201_bound
    · exact case202_bound
    · exact case203_bound
    · exact case204_bound
    · exact case205_bound
    · exact case206_bound
    · exact case207_bound
    · exact case208_bound
    · exact case209_bound
    · exact case210_bound
    · exact case211_bound
    · exact case212_bound
    · exact case213_bound
    · exact case214_bound
    · exact case215_bound
    · exact case216_bound
    · exact case217_bound
    · exact case218_bound
    · exact case219_bound
    · exact case220_bound
    · exact case221_bound
    · exact case222_bound
    · exact case223_bound
    · exact case224_bound
    · exact case225_bound
    · exact case226_bound
    · exact case227_bound
    · exact case228_bound
    · exact case229_bound
    · exact case230_bound
    · exact case231_bound
    · exact case232_bound
    · exact case233_bound
    · exact case234_bound
    · exact case235_bound
    · exact case236_bound
    · exact case237_bound
    · exact case238_bound
    · exact case239_bound
    · exact case240_bound
    · exact case241_bound
    · exact case242_bound
    · exact case243_bound
    · exact case244_bound
    · exact case245_bound
  apply completion_from_orbits ho hp hr ?_ n hn t
  intro q u hq
  let v := (q.val-1)*3+u.val
  have hv : v < 19680 := by dsimp [v]; omega
  obtain ⟨r,w,a,ha,he,ht⟩ := every_orbit_index ⟨v,hv⟩
  have heq : v/3+1 = q.val := by dsimp [v]; omega
  have hmod : v%3 = u.val := by dsimp [v]; omega
  refine ⟨r,w,a,ha,?_,?_⟩
  · simpa only [heq] using he
  · simpa only [hmod] using ht
#print axioms solution
