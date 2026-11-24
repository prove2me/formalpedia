-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_detM_b1
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T09:08:40.494747+00:00
-- url     : https://prove2.me/submissions/1102290b-5430-469a-9f1b-9f30590ed78a

import Definitions.Def_HodgeComputerSSR_CoverParams
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    let A : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 693, 99, 24, 990, 960, 985, 475, 392, 1002, 880, 11, 207, 304, 568, 772, 17, 347, 14, 576, 559, 434], [0, 860, 810, 759, 131, 61, 838, 967, 865, 440, 1007, 195, 776, 254, 783, 532, 1007, 241, 289, 723, 854, 784, 543, 526])
    let B : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 429, 199, 513, 792, 600, 635, 347, 337, 528, 568, 167, 415, 801, 885, 523, 3, 804, 798, 616, 46, 263], [0, 148, 851, 828, 316, 522, 347, 488, 259, 813, 676, 805, 819, 12, 908, 678, 484, 979, 934, 835, 725, 297, 486, 342])
    let Cc : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 84, 433, 932, 51, 490, 800, 352, 199, 218, 586, 1002, 172, 998, 920, 49, 547, 613, 987, 206, 500, 678], [0, 410, 989, 283, 772, 203, 720, 462, 192, 842, 234, 77, 313, 766, 989, 984, 711, 228, 928, 960, 349, 264, 794, 287])
    let xS : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 739, 371, 735, 197, 216, 711, 347, 456, 471, 808, 940, 318, 476, 9, 274, 0, 500, 895, 559, 223, 195], [0, 556, 955, 807, 889, 101, 277, 125, 95, 493, 478, 188, 782, 262, 81, 317, 423, 260, 411, 323, 464, 644, 891, 971])
    let xQ : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 125, 304, 231, 229, 488, 234, 330, 930, 32, 936, 153, 459, 1007, 353, 559, 617, 846, 989, 565, 261, 719], [0, 490, 730, 745, 736, 17, 425, 964, 290, 479, 349, 242, 880, 220, 445, 571, 722, 834, 132, 723, 449, 316, 961, 160])
    let b2 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([388, 547, 726, 876, 141, 665, 938, 146, 59, 895, 210, 685, 306, 997, 757, 757, 448, 564, 390, 278, 101, 652, 965, 208, 141, 325, 126, 268, 586, 393, 206, 107, 207, 396], [293, 897, 49, 166, 459, 517, 450, 253, 996, 150, 571, 210, 736, 995, 180, 58, 656, 710, 714, 64, 968, 466, 549, 1003, 939, 625, 182, 725, 46, 146, 412, 34, 526, 761])
    let b0 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([75, 359, 568, 759, 464, 753, 649, 910, 799, 16, 771, 344, 455, 264, 31, 787, 948, 44, 396, 725, 856, 311, 243, 899, 384, 641, 716, 599, 693, 195, 521, 527, 741, 237], [957, 464, 714, 222, 692, 453, 746, 310, 507, 961, 361, 393, 671, 2, 587, 103, 80, 143, 515, 830, 93, 222, 500, 52, 773, 639, 58, 815, 438, 866, 962, 973, 238, 74])
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.c_dH_dQ_homP A B ([], []) = b2) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.c_dH_dQ_homP xS xQ Cc = b0) :=
  ⟨by decide +kernel, by decide +kernel⟩
