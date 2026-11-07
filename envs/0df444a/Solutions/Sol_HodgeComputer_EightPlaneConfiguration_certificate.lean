-- Prove2me | solution 1 for HodgeComputer.EightPlaneConfiguration.certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-06T23:05:25.346699+00:00
-- url     : https://prove2.me/submissions/a2d8405d-db84-40c9-a210-2e2940d4f8fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerEightPlaneConfiguration
import Definitions.Def_HodgeComputerNormalChart
import Theorems.Thm_HodgeComputer_NormalChart_certificate_of_residue
import Theorems.Thm_HodgeComputer_EightPlaneConfiguration_normalDerivative_relPrime
import Theorems.Thm_HodgeComputer_EightPlaneConfiguration_normalChart_residue_solvable
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open HodgeComputer HodgeComputer.EightPlaneConfiguration MvPolynomial

private theorem nat_homogeneous (c : ℕ) : (c : AmbientPoly 5).IsHomogeneous 0 := by
  simpa only [map_natCast] using (isHomogeneous_C (Fin 6) (c : ℂ))

private theorem F_homogeneous : F.IsHomogeneous 6 := by
  unfold F
  exact
    ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((nat_homogeneous 31218).mul (isHomogeneous_X_pow 0 6)).mul (isHomogeneous_C (Fin 6) (1 / 31213 : ℂ))).add
    ((((nat_homogeneous 40).mul (isHomogeneous_X_pow 0 5)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 31213 : ℂ)))).add
    ((((nat_homogeneous 60).mul (isHomogeneous_X_pow 0 5)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 31213 : ℂ)))).add
    ((((nat_homogeneous 1600).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_C (Fin 6) (1 / 343343 : ℂ)))).add
    (((((nat_homogeneous 360).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 31213 : ℂ)))).add
    ((((nat_homogeneous 4455).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_C (Fin 6) (1 / 405769 : ℂ)))).add
    ((((nat_homogeneous 3265).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    (((((nat_homogeneous 60).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    (((((nat_homogeneous 80).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((nat_homogeneous 17995).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    (((((nat_homogeneous 120).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((nat_homogeneous 7505).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 2393209 : ℂ)))).add
    ((((nat_homogeneous 4140).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_C (Fin 6) (1 / 343343 : ℂ)))).add
    (((((nat_homogeneous 12120).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 343343 : ℂ)))).add
    (((((nat_homogeneous 25380).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_C (Fin 6) (1 / 405769 : ℂ)))).add
    (((((nat_homogeneous 18840).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    ((((((nat_homogeneous 240).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 320).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    (((((nat_homogeneous 124000).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    ((((((nat_homogeneous 480).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    (((((nat_homogeneous 522260).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 16752463 : ℂ)))).add
    ((((nat_homogeneous 37260).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_C (Fin 6) (1 / 405769 : ℂ)))).add
    (((((nat_homogeneous 28260).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    ((((((nat_homogeneous 360).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 480).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    (((((nat_homogeneous 212010).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    ((((((nat_homogeneous 720).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    (((((nat_homogeneous 1329600).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 16752463 : ℂ)))).add
    ((((nat_homogeneous 710).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_C (Fin 6) (1 / 31213 : ℂ)))).add
    (((((nat_homogeneous 2580).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 31213 : ℂ)))).add
    (((((nat_homogeneous 71160).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_C (Fin 6) (1 / 405769 : ℂ)))).add
    (((((nat_homogeneous 665400).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 99226127 : ℂ)))).add
    ((((((nat_homogeneous 12720).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1090397 : ℂ)))).add
    ((((((nat_homogeneous 21440).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1090397 : ℂ)))).add
    (((((nat_homogeneous 65610).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 2025023 : ℂ)))).add
    ((((((nat_homogeneous 45600).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1090397 : ℂ)))).add
    (((((nat_homogeneous 22674000).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184277093 : ℂ)))).add
    (((((nat_homogeneous 166500).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_C (Fin 6) (1 / 405769 : ℂ)))).add
    ((((((nat_homogeneous 125880).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    (((((((nat_homogeneous 720).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    (((((((nat_homogeneous 960).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 93720).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1288651 : ℂ)))).add
    (((((((nat_homogeneous 1440).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 922380).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 2393209 : ℂ)))).add
    ((((nat_homogeneous 140715).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_C (Fin 6) (1 / 405769 : ℂ)))).add
    (((((nat_homogeneous 235530).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    ((((((nat_homogeneous 143100).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1288651 : ℂ)))).add
    ((((((nat_homogeneous 331920).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1288651 : ℂ)))).add
    (((((nat_homogeneous 304260).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1288651 : ℂ)))).add
    ((((((nat_homogeneous 1102680).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1288651 : ℂ)))).add
    (((((nat_homogeneous 22486950).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 16752463 : ℂ)))).add
    ((((nat_homogeneous 34950).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_C (Fin 6) (1 / 131938037 : ℂ)))).add
    (((((nat_homogeneous 167325).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 131938037 : ℂ)))).add
    (((((nat_homogeneous 248090).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 131938037 : ℂ)))).add
    (((((nat_homogeneous 668300).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 131938037 : ℂ)))).add
    ((((((nat_homogeneous 1246785).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 131938037 : ℂ)))).add
    (((((nat_homogeneous 39587650).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 1715194481 : ℂ)))).add
    (((((nat_homogeneous 254565).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_C (Fin 6) (1 / 18848291 : ℂ)))).add
    ((((((nat_homogeneous 695320).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 18848291 : ℂ)))).add
    ((((((nat_homogeneous 33880365).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    (((((nat_homogeneous 5962430).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 22275253 : ℂ)))).add
    ((((nat_homogeneous 244215).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_C (Fin 6) (1 / 18848291 : ℂ)))).add
    (((((nat_homogeneous 1002195).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 18848291 : ℂ)))).add
    (((((nat_homogeneous 61115240).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    (((((nat_homogeneous 216859245).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    ((((nat_homogeneous 249197420).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    ((((nat_homogeneous 1215).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 5)).mul (isHomogeneous_C (Fin 6) (1 / 49049 : ℂ)))).add
    (((((nat_homogeneous 450).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 3773 : ℂ)))).add
    (((((nat_homogeneous 185440).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_C (Fin 6) (1 / 637637 : ℂ)))).add
    (((((nat_homogeneous 1120160).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 99226127 : ℂ)))).add
    ((((((nat_homogeneous 4320).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 7680).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((nat_homogeneous 793395).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    ((((((nat_homogeneous 17280).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((nat_homogeneous 37499200).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184277093 : ℂ)))).add
    (((((nat_homogeneous 63680).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_C (Fin 6) (1 / 91091 : ℂ)))).add
    ((((((nat_homogeneous 3104240).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 99226127 : ℂ)))).add
    (((((((nat_homogeneous 5760).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((((nat_homogeneous 10240).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 175410).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1090397 : ℂ)))).add
    (((((((nat_homogeneous 23040).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 135620000).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184277093 : ℂ)))).add
    (((((nat_homogeneous 59100).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_C (Fin 6) (1 / 57967 : ℂ)))).add
    ((((((nat_homogeneous 688440).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    (((((((nat_homogeneous 51840).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((((nat_homogeneous 122880).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((((nat_homogeneous 9371640).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    (((((((nat_homogeneous 414720).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((((nat_homogeneous 61808220).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 16752463 : ℂ)))).add
    (((((nat_homogeneous 80).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 240).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 320).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 8700).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1090397 : ℂ)))).add
    (((((((nat_homogeneous 480).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 57920).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 1288651 : ℂ)))).add
    ((((((nat_homogeneous 4320).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((((nat_homogeneous 7680).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((((nat_homogeneous 51840).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((((nat_homogeneous 122880).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 4860).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 17280).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 1161960).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 2025023 : ℂ)))).add
    ((((((nat_homogeneous 414720).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 491520).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((nat_homogeneous 31000).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 5)).mul (isHomogeneous_C (Fin 6) (1 / 57967 : ℂ)))).add
    (((((nat_homogeneous 626460).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    ((((((nat_homogeneous 64800).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((((nat_homogeneous 153600).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 9760910).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    ((((((nat_homogeneous 518400).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 64869400).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 16752463 : ℂ)))).add
    (((((nat_homogeneous 120).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 360).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 480).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 11930).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1090397 : ℂ)))).add
    (((((((nat_homogeneous 720).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 4320).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 75803 : ℂ)))).add
    ((((((nat_homogeneous 5760).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((((nat_homogeneous 10240).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((((nat_homogeneous 64800).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((((nat_homogeneous 153600).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 6480).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 23040).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 209870).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 289289 : ℂ)))).add
    ((((((nat_homogeneous 518400).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 614400).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((nat_homogeneous 49589).mul (isHomogeneous_X_pow 1 6)).mul (isHomogeneous_C (Fin 6) (1 / 49049 : ℂ)))).add
    ((((nat_homogeneous 3375).mul (isHomogeneous_X_pow 1 5)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 49049 : ℂ)))).add
    ((((nat_homogeneous 128780).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_C (Fin 6) (1 / 637637 : ℂ)))).add
    ((((nat_homogeneous 712960).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 99226127 : ℂ)))).add
    (((((nat_homogeneous 3240).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((nat_homogeneous 5760).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((nat_homogeneous 487755).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    (((((nat_homogeneous 12960).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((nat_homogeneous 21766400).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184277093 : ℂ)))).add
    ((((nat_homogeneous 301520).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_C (Fin 6) (1 / 637637 : ℂ)))).add
    (((((nat_homogeneous 2748960).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 99226127 : ℂ)))).add
    ((((((nat_homogeneous 8640).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 15360).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((nat_homogeneous 1859895).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    ((((((nat_homogeneous 34560).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((nat_homogeneous 94326720).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184277093 : ℂ)))).add
    ((((nat_homogeneous 75120).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_C (Fin 6) (1 / 91091 : ℂ)))).add
    (((((nat_homogeneous 7008360).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 99226127 : ℂ)))).add
    ((((((nat_homogeneous 455040).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 2025023 : ℂ)))).add
    ((((((nat_homogeneous 1034240).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 2025023 : ℂ)))).add
    (((((nat_homogeneous 562860).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1090397 : ℂ)))).add
    ((((((nat_homogeneous 3340800).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 2025023 : ℂ)))).add
    (((((nat_homogeneous 493383120).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184277093 : ℂ)))).add
    ((((nat_homogeneous 2104240).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_C (Fin 6) (1 / 1451318407 : ℂ)))).add
    (((((nat_homogeneous 1019160).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 131938037 : ℂ)))).add
    (((((nat_homogeneous 16813600).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1451318407 : ℂ)))).add
    (((((nat_homogeneous 33134100).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1451318407 : ℂ)))).add
    ((((((nat_homogeneous 81897720).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1451318407 : ℂ)))).add
    (((((nat_homogeneous 1349734240).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 18867139291 : ℂ)))).add
    (((((nat_homogeneous 8977240).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_C (Fin 6) (1 / 207331201 : ℂ)))).add
    ((((((nat_homogeneous 2696160).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 18848291 : ℂ)))).add
    ((((((nat_homogeneous 954313560).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 2695305613 : ℂ)))).add
    (((((nat_homogeneous 1433297120).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 2695305613 : ℂ)))).add
    ((((nat_homogeneous 7250535).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_C (Fin 6) (1 / 207331201 : ℂ)))).add
    (((((nat_homogeneous 32310400).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 207331201 : ℂ)))).add
    (((((nat_homogeneous 216172800).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 385043659 : ℂ)))).add
    (((((nat_homogeneous 4527451800).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 2695305613 : ℂ)))).add
    ((((nat_homogeneous 4984688000).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 2695305613 : ℂ)))).add
    ((((nat_homogeneous 500).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 5)).mul (isHomogeneous_C (Fin 6) (1 / 637 : ℂ)))).add
    (((((nat_homogeneous 939320).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    ((((((nat_homogeneous 86400).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((((nat_homogeneous 204800).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 13469240).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    ((((((nat_homogeneous 691200).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 963700).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 240).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 720).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 960).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 1140).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 64141 : ℂ)))).add
    (((((((nat_homogeneous 1440).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 99127 : ℂ)))).add
    ((((((nat_homogeneous 102080).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 1288651 : ℂ)))).add
    ((((((nat_homogeneous 8640).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((((nat_homogeneous 15360).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    (((((((nat_homogeneous 86400).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((((nat_homogeneous 204800).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 9720).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 34560).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 155771 : ℂ)))).add
    ((((((nat_homogeneous 2003160).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 2025023 : ℂ)))).add
    ((((((nat_homogeneous 691200).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 819200).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((nat_homogeneous 74842).mul (isHomogeneous_X_pow 2 6)).mul (isHomogeneous_C (Fin 6) (1 / 57967 : ℂ)))).add
    ((((nat_homogeneous 509045).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 9020557 : ℂ)))).add
    (((((nat_homogeneous 54000).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    (((((nat_homogeneous 128000).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((nat_homogeneous 603765).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1090397 : ℂ)))).add
    (((((nat_homogeneous 432000).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 184093 : ℂ)))).add
    ((((nat_homogeneous 51468875).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 16752463 : ℂ)))).add
    ((((nat_homogeneous 9412020).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_C (Fin 6) (1 / 1715194481 : ℂ)))).add
    (((((nat_homogeneous 62085015).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1715194481 : ℂ)))).add
    (((((nat_homogeneous 106920360).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1715194481 : ℂ)))).add
    (((((nat_homogeneous 1486370).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 14175161 : ℂ)))).add
    ((((((nat_homogeneous 566305605).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1715194481 : ℂ)))).add
    (((((nat_homogeneous 542511880).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 1715194481 : ℂ)))).add
    (((((nat_homogeneous 38527855).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    ((((((nat_homogeneous 164423170).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    ((((((nat_homogeneous 313889655).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    (((((nat_homogeneous 299349720).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    ((((nat_homogeneous 24249915).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    (((((nat_homogeneous 128600795).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    (((((nat_homogeneous 376100840).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    (((((nat_homogeneous 809485665).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    ((((nat_homogeneous 772902080).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 245027783 : ℂ)))).add
    (((nat_homogeneous 158399).mul (isHomogeneous_X_pow 3 6)).mul (isHomogeneous_C (Fin 6) (1 / 158389 : ℂ)))).add
    ((((nat_homogeneous 15).mul (isHomogeneous_X_pow 3 5)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 22627 : ℂ)))).add
    ((((nat_homogeneous 10).mul (isHomogeneous_X_pow 3 5)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 9317 : ℂ)))).add
    ((((nat_homogeneous 5575).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 1742279 : ℂ)))).add
    (((((nat_homogeneous 1305).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 158389 : ℂ)))).add
    ((((nat_homogeneous 3030).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 294151 : ℂ)))).add
    ((((nat_homogeneous 1515).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_C (Fin 6) (1 / 158389 : ℂ)))).add
    (((((nat_homogeneous 50200).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1742279 : ℂ)))).add
    (((((nat_homogeneous 130590).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 2059057 : ℂ)))).add
    ((((nat_homogeneous 149150).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 2059057 : ℂ)))).add
    ((((nat_homogeneous 33015).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_C (Fin 6) (1 / 1742279 : ℂ)))).add
    (((((nat_homogeneous 118095).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 1742279 : ℂ)))).add
    (((((nat_homogeneous 3882330).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 22649627 : ℂ)))).add
    (((((nat_homogeneous 740280).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 2059057 : ℂ)))).add
    ((((nat_homogeneous 579340).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 2059057 : ℂ)))).add
    ((((nat_homogeneous 5600).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 5)).mul (isHomogeneous_C (Fin 6) (1 / 248897 : ℂ)))).add
    (((((nat_homogeneous 2400).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 22627 : ℂ)))).add
    (((((nat_homogeneous 927325).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 3235661 : ℂ)))).add
    (((((nat_homogeneous 2239350).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 3235661 : ℂ)))).add
    (((((nat_homogeneous 290535).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 294151 : ℂ)))).add
    ((((nat_homogeneous 154840).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 5)).mul (isHomogeneous_C (Fin 6) (1 / 294151 : ℂ)))).add
    (((nat_homogeneous 251777).mul (isHomogeneous_X_pow 4 6)).mul (isHomogeneous_C (Fin 6) (1 / 248897 : ℂ)))).add
    ((((nat_homogeneous 18080).mul (isHomogeneous_X_pow 4 5)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 248897 : ℂ)))).add
    ((((nat_homogeneous 737865).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 3235661 : ℂ)))).add
    ((((nat_homogeneous 1795265).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 3235661 : ℂ)))).add
    ((((nat_homogeneous 3164115).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 3235661 : ℂ)))).add
    ((((nat_homogeneous 281505).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X_pow 5 5)).mul (isHomogeneous_C (Fin 6) (1 / 294151 : ℂ)))).add
    (((nat_homogeneous 403911).mul (isHomogeneous_X_pow 5 6)).mul (isHomogeneous_C (Fin 6) (1 / 294151 : ℂ))))

private theorem A_homogeneous : A.IsHomogeneous 6 := by
  unfold A
  exact (isHomogeneous_X_pow 0 3).mul (isHomogeneous_X_pow 3 3)

private theorem F_nonzero : F ≠ 0 := by
  have h1 : (1 : Fin 6) ≠ 0 := by decide
  have h2 : (2 : Fin 6) ≠ 0 := by decide
  have h3 : (3 : Fin 6) ≠ 0 := by decide
  have h4 : (4 : Fin 6) ≠ 0 := by decide
  have h5 : (5 : Fin 6) ≠ 0 := by decide
  have he : eval (fun i : Fin 6 => if i = 0 then (1 : ℂ) else 0) F = (31218 / 31213 : ℂ) := by
    norm_num only [F, map_add, map_mul, map_pow, eval_X, eval_C, map_ofNat,
      h1, h2, h3, h4, h5, if_pos, if_neg, one_pow, zero_pow, zero_mul, mul_zero,
      mul_one, one_mul, zero_add, add_zero]
  intro hz
  rw [hz, map_zero] at he
  norm_num at he

private theorem normal_nonzero : NormalChart.normal F ≠ 0 := by
  have hc : pderiv (0 : Fin 6) (31218 : AmbientPoly 5) = 0 :=
    (pderiv (0 : Fin 6)).map_natCast 31218
  have h1 : (1 : Fin 6) ≠ 0 := by decide
  have h2 : (2 : Fin 6) ≠ 0 := by decide
  have h3 : (3 : Fin 6) ≠ 0 := by decide
  have h4 : (4 : Fin 6) ≠ 0 := by decide
  have h5 : (5 : Fin 6) ≠ 0 := by decide
  have he : eval (fun i : Fin 6 => if i = 0 then (1 : ℂ) else 0)
      (NormalChart.normal F) = (187308 / 31213 : ℂ) := by
    norm_num only [NormalChart.normal, F, map_add, map_mul, map_pow,
      pderiv_mul, pderiv_pow, pderiv_X, pderiv_C, Derivation.map_natCast,
      eval_X, eval_C, Pi.single_apply, map_ofNat, map_zero, hc, h1, h2, h3, h4, h5,
      if_pos, if_neg, one_pow, zero_pow, zero_mul, mul_zero, mul_one, one_mul,
      zero_add, add_zero]
  intro hz
  rw [hz, map_zero] at he
  norm_num at he

theorem solution :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.EightPlaneConfiguration.n)
      HodgeComputer.EightPlaneConfiguration.F
      HodgeComputer.EightPlaneConfiguration.A
      HodgeComputer.EightPlaneConfiguration.d
      HodgeComputer.EightPlaneConfiguration.q := by
  obtain ⟨S, W, Q, hS, hShom, hFS, hWhom, hres⟩ := normalChart_residue_solvable
  refine ⟨NormalChart.denominator F S, NormalChart.numerator F A S W, Q, ?_⟩
  exact NormalChart.certificate_of_residue F A S W Q
    F_nonzero F_homogeneous A_homogeneous normal_nonzero normalDerivative_relPrime
    hS hShom hFS hWhom hres

#print axioms solution
