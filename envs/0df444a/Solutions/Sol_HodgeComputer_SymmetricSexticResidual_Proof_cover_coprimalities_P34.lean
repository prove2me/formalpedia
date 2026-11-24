-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T09:16:16.416797+00:00
-- url     : https://prove2.me/submissions/3eda43ad-94c5-4e6a-83a1-0c0f6810160c

import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_CoverFactors
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_detM_a
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_detM_b1
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_detM_b2
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.K5Field QuadraticCovers Polynomial
open scoped BigOperators

noncomputable section CoverCoprimeP34Proof

namespace Poly1009
lemma check_bez_P34_P34d : checkBez P34_m_list 34 (pderiv P34_m_list) bez_P34_P34d = true := by decide +kernel
lemma check_bez_P34_X : checkBez P34_m_list 34 [0, 1] bez_P34_X = true := by decide +kernel
lemma check_bez_P34_Xm1 : checkBez P34_m_list 34 [-1, 1] bez_P34_Xm1 = true := by decide +kernel
lemma check_bez_P34_Q5 : checkBez P34_m_list 34 c_Q5 bez_P34_Q5 = true := by decide +kernel
lemma check_bez_P34_cbh : checkBez P34_m_list 34 c_cb_h bez_P34_cbh = true := by decide +kernel
lemma check_bez_P34_cah : checkBez P34_m_list 34 c_ca_h bez_P34_cah = true := by decide +kernel
lemma check_bez_P34_nmWU : checkBez P34_m_list 34 c_nm_WU bez_P34_nmWU = true := by decide +kernel
lemma check_bez_P34_discE0 : checkBez P34_m_list 34 c_disc_E0 bez_P34_discE0 = true := by decide +kernel
lemma check_bez_P34_nmd1 : checkBez P34_m_list 34 (qnm c_d1_z) bez_P34_nmd1 = true := by decide +kernel
lemma check_bez_P34_nmdiscE2 : checkBez P34_m_list 34 (qnm c_disc_E2z) bez_P34_nmdiscE2 = true := by decide +kernel

private def detM_a2 : Pair1009 := ([950, 858, 321, 742, 159, 570, 523, 24, 870, 55, 220, 198, 814, 879, 28, 223, 354, 739, 761, 826, 80, 299, 685, 853, 939, 749, 319, 227, 892, 486, 971, 844, 118, 239], [32, 980, 181, 59, 72, 17, 179, 888, 369, 855, 328, 929, 782, 134, 486, 6, 897, 780, 382, 136, 391, 183, 430, 160, 964, 190, 28, 404, 802, 591, 93, 492, 199, 45])
private def detM_a0 : Pair1009 := ([364, 80, 930, 853, 79, 156, 738, 602, 816, 649, 124, 186, 364, 226, 355, 293, 743, 801, 938, 692, 286, 796, 985, 55, 290, 333, 894, 639, 285, 144, 562, 228, 169, 701], [304, 527, 903, 155, 9, 98, 865, 718, 656, 770, 114, 485, 848, 353, 136, 146, 457, 373, 149, 949, 757, 787, 14, 730, 379, 191, 523, 303, 202, 61, 53, 38, 482, 1007])
private def detM_a1 : Pair1009 := ([644, 9, 297, 10, 842, 400, 476, 350, 661, 37, 670, 31, 328, 102, 739, 848, 699, 995, 59, 373, 292, 129, 382, 852, 776, 329, 812, 423, 202, 341, 540, 129, 958, 663], [259, 401, 476, 392, 327, 604, 402, 165, 807, 310, 583, 809, 949, 358, 138, 589, 621, 419, 654, 207, 4, 469, 855, 288, 552, 1, 122, 88, 736, 257, 176, 354, 560, 4])
private def detM_b2 : Pair1009 := ([388, 547, 726, 876, 141, 665, 938, 146, 59, 895, 210, 685, 306, 997, 757, 757, 448, 564, 390, 278, 101, 652, 965, 208, 141, 325, 126, 268, 586, 393, 206, 107, 207, 396], [293, 897, 49, 166, 459, 517, 450, 253, 996, 150, 571, 210, 736, 995, 180, 58, 656, 710, 714, 64, 968, 466, 549, 1003, 939, 625, 182, 725, 46, 146, 412, 34, 526, 761])
private def detM_b0 : Pair1009 := ([75, 359, 568, 759, 464, 753, 649, 910, 799, 16, 771, 344, 455, 264, 31, 787, 948, 44, 396, 725, 856, 311, 243, 899, 384, 641, 716, 599, 693, 195, 521, 527, 741, 237], [957, 464, 714, 222, 692, 453, 746, 310, 507, 961, 361, 393, 671, 2, 587, 103, 80, 143, 515, 830, 93, 222, 500, 52, 773, 639, 58, 815, 438, 866, 962, 973, 238, 74])
private def detM_b1 : Pair1009 := ([154, 116, 803, 694, 845, 697, 275, 69, 651, 363, 124, 723, 381, 209, 5, 684, 623, 568, 818, 592, 169, 660, 966, 691, 841, 90, 133, 224, 138, 397, 415, 87, 840, 629], [44, 783, 15, 677, 206, 983, 247, 481, 461, 409, 631, 596, 970, 815, 209, 698, 826, 963, 718, 295, 587, 510, 418, 945, 450, 936, 367, 84, 479, 166, 404, 438, 545, 322])
private def detM_d20 : Pair1009 := ([773, 599, 557, 71, 1002, 208, 740, 274, 161, 148, 938, 248, 250, 972, 444, 842, 18, 706, 382, 750, 371, 955, 537, 177, 738, 914, 70, 475, 747, 326, 402, 339, 29, 665], [671, 639, 6, 849, 527, 168, 930, 255, 122, 162, 979, 871, 887, 271, 381, 649, 430, 635, 861, 427, 261, 510, 382, 805, 581, 329, 85, 550, 146, 438, 882, 286, 772, 891])
private def detM_d21 : Pair1009 := ([916, 464, 398, 847, 535, 247, 750, 846, 879, 251, 653, 224, 85, 545, 232, 656, 405, 595, 113, 133, 116, 828, 206, 283, 566, 506, 279, 106, 985, 110, 31, 818, 704, 401], [767, 323, 902, 668, 483, 997, 439, 975, 405, 479, 620, 384, 214, 186, 546, 866, 429, 184, 223, 406, 169, 925, 205, 134, 282, 874, 743, 128, 590, 600, 341, 764, 264, 989])
private def detM_d10 : Pair1009 := ([538, 786, 383, 208, 381, 441, 311, 325, 647, 439, 747, 441, 861, 238, 335, 1003, 448, 112, 860, 46, 330, 174, 408, 305, 340, 182, 37, 342, 522, 103, 416, 335, 222, 989], [187, 873, 577, 105, 304, 534, 358, 86, 138, 86, 348, 897, 933, 247, 387, 271, 944, 13, 70, 777, 443, 389, 150, 27, 830, 901, 903, 857, 934, 467, 1, 474, 499, 612])
private def detM_val : Pair1009 := ([18, 312, 750, 324, 330, 322, 35, 194, 730, 805, 774, 222, 794, 307, 439, 342, 768, 65, 100, 7, 691, 598, 560, 450, 551, 775, 988, 883, 998, 133, 796, 364, 649, 931], [578, 755, 681, 621, 539, 289, 984, 946, 957, 18, 227, 352, 417, 658, 638, 734, 198, 893, 900, 80, 786, 791, 653, 888, 632, 304, 69, 439, 372, 66, 612, 562, 132, 287])
private def nm_detMP_val : Poly1009 := [843, 32, 591, 541, 345, 788, 246, 592, 294, 1007, 395, 435, 447, 106, 231, 236, 498, 517, 904, 967, 202, 949, 102, 267, 666, 636, 363, 835, 503, 202, 830, 244, 893, 995]
private lemma h_detM_d20 : qsubP (qmulP detM_a2 detM_b0) (qmulP detM_a0 detM_b2) = detM_d20 := by decide +kernel
private lemma h_detM_d21 : qsubP (qmulP detM_a2 detM_b1) (qmulP detM_a1 detM_b2) = detM_d21 := by decide +kernel
private lemma h_detM_d10 : qsubP (qmulP detM_a1 detM_b0) (qmulP detM_a0 detM_b1) = detM_d10 := by decide +kernel
private lemma h_detM_val : qsubP (qmulP detM_d20 detM_d20) (qmulP detM_d21 detM_d10) = detM_val := by decide +kernel
private lemma h_c_detM_WP : c_detM_WP = detM_val := by
  obtain ⟨hA, hB, hCc, hxS, hxQ, hax, hbx, ha2, ha0, ha1_0, ha1⟩ := HodgeComputer.SymmetricSexticResidual.Proof.cover_detM_a
  obtain ⟨hb2, hb0⟩ := HodgeComputer.SymmetricSexticResidual.Proof.cover_detM_b1
  obtain ⟨hb1_0, hb1_x, hb1⟩ := HodgeComputer.SymmetricSexticResidual.Proof.cover_detM_b2
  unfold c_detM_WP; dsimp only
  rw [hA, hB, hCc, hxS, hxQ, hax, hbx, ha2, ha0, ha1_0, ha1, hb2, hb0, hb1_0, hb1_x, hb1]
  change qsubP (qmulP (qsubP (qmulP detM_a2 detM_b0) (qmulP detM_a0 detM_b2))
      (qsubP (qmulP detM_a2 detM_b0) (qmulP detM_a0 detM_b2)))
    (qmulP (qsubP (qmulP detM_a2 detM_b1) (qmulP detM_a1 detM_b2))
      (qsubP (qmulP detM_a1 detM_b0) (qmulP detM_a0 detM_b1))) = detM_val
  rw [h_detM_d20, h_detM_d21, h_detM_d10, h_detM_val]
private lemma h_c_nm_detMP : c_nm_detMP = nm_detMP_val := by
  unfold c_nm_detMP; rw [h_c_detM_WP]; decide +kernel
lemma check_bez_P34_nmdetM :
    peq (padd (pmul bez_P34_nmdetM.1 P34_m_list) (pmul bez_P34_nmdetM.2 c_nm_detMP)) pone = true := by
  rw [h_c_nm_detMP]; decide +kernel
end Poly1009

lemma isCoprime_P34_P34_deriv : IsCoprime P34_K5 P34_K5.derivative := by
  have hcop : IsCoprime (P34_loc.map evLoc) (P34_loc.derivative.map evLoc) := by
    rw [← Polynomial.derivative_map, P34_loc_spec.2.2.1, ← Poly1009.toPoly_pderiv]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_P34d
  simpa only [P34_K5, Polynomial.derivative_map] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_X : IsCoprime P34_K5 (X : K5[X]) := by
  have hcop : IsCoprime (P34_loc.map evLoc) ((X : LocK5[X]).map evLoc) := by
    rw [P34_loc_spec.2.2.1, Polynomial.map_X]
    simpa [Poly1009.toPoly] using Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_X
  simpa only [P34_K5, Polynomial.map_X] using isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_X_sub_1 : IsCoprime P34_K5 (X - 1 : K5[X]) := by
  have hcop : IsCoprime (P34_loc.map evLoc) ((X - 1 : LocK5[X]).map evLoc) := by
    rw [P34_loc_spec.2.2.1, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
    have hX1 : Poly1009.toPoly [-1, 1] = (X - 1 : (ZMod 1009)[X]) := by simp [Poly1009.toPoly]; ring
    rw [← hX1]; exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_Xm1
  simpa only [P34_K5, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_Q5 : IsCoprime P34_K5 k5Params.Q5_z := by
  have hcop : IsCoprime (P34_loc.map evLoc) (locParams.Q5_z.map evLoc) := by
    rw [P34_loc_spec.2.2.1, CoverParams.map_Q5_z, locParams_map_evLoc, ← Poly1009.toPoly_c_Q5]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_Q5
  simpa only [P34_K5, CoverParams.map_Q5_z, k5Params] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_cb_h : IsCoprime P34_K5 k5Params.cb_h := by
  have hcop : IsCoprime (P34_loc.map evLoc) (locParams.cb_h.map evLoc) := by
    rw [P34_loc_spec.2.2.1, CoverParams.map_cb_h, locParams_map_evLoc, ← Poly1009.toPoly_c_cb_h]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_cbh
  simpa only [P34_K5, CoverParams.map_cb_h, k5Params] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_ca_h : IsCoprime P34_K5 k5Params.ca_h := by
  have hcop : IsCoprime (P34_loc.map evLoc) (locParams.ca_h.map evLoc) := by
    rw [P34_loc_spec.2.2.1, CoverParams.map_ca_h, locParams_map_evLoc, ← Poly1009.toPoly_c_ca_h]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_cah
  simpa only [P34_K5, CoverParams.map_ca_h, k5Params] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_nm_WU : IsCoprime P34_K5 k5Params.nm_WU := by
  have hcop : IsCoprime (P34_loc.map evLoc) (locParams.nm_WU.map evLoc) := by
    rw [P34_loc_spec.2.2.1, CoverParams.map_nm_WU, locParams_map_evLoc, ← Poly1009.toPoly_c_nm_WU]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_nmWU
  simpa only [P34_K5, CoverParams.map_nm_WU, k5Params] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_disc_E0 : IsCoprime P34_K5 k5Params.disc_E0 := by
  have hcop : IsCoprime (P34_loc.map evLoc) (locParams.disc_E0.map evLoc) := by
    rw [P34_loc_spec.2.2.1, CoverParams.map_disc_E0, locParams_map_evLoc, ← Poly1009.toPoly_c_disc_E0]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_discE0
  simpa only [P34_K5, CoverParams.map_disc_E0, k5Params] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_nm_d1_z : IsCoprime P34_K5 (k5Params.pnm k5Params.d1_z) := by
  have hcop : IsCoprime (P34_loc.map evLoc) ((locParams.pnm locParams.d1_z).map evLoc) := by
    rw [P34_loc_spec.2.2.1, CoverParams.map_pnm, CoverParams.map_d1_z, locParams_map_evLoc,
      ← Poly1009.pairToAlg_c_d1_z, ← Poly1009.toPoly_qnm]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_nmd1
  simpa only [P34_K5, CoverParams.map_pnm, CoverParams.map_d1_z, k5Params] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_nm_disc_E2z : IsCoprime P34_K5 (k5Params.pnm k5Params.disc_E2z) := by
  have hcop : IsCoprime (P34_loc.map evLoc) ((locParams.pnm locParams.disc_E2z).map evLoc) := by
    rw [P34_loc_spec.2.2.1, CoverParams.map_pnm, CoverParams.map_disc_E2z, locParams_map_evLoc,
      ← Poly1009.pairToAlg_c_disc_E2z, ← Poly1009.toPoly_qnm]
    exact Poly1009.isCoprime_of_checkBez Poly1009.check_bez_P34_nmdiscE2
  simpa only [P34_K5, CoverParams.map_pnm, CoverParams.map_disc_E2z, k5Params] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop

lemma isCoprime_P34_nm_detM_W : IsCoprime P34_K5 (k5Params.pnm k5Params.detM_W) := by
  have hcop : IsCoprime (P34_loc.map evLoc) ((locParams.pnm locParams.detM_W).map evLoc) := by
    rw [P34_loc_spec.2.2.1, CoverParams.map_pnm, CoverParams.map_detM_W, locParams_map_evLoc]
    exact Poly1009.isCoprime_of_bezout_congr Poly1009.nm_detM_W_congrP Poly1009.check_bez_P34_nmdetM
  simpa only [P34_K5, CoverParams.map_pnm, CoverParams.map_detM_W, k5Params] using
    isCoprime_of_evLoc_monic P34_loc_spec.1 hcop


private theorem cover_coprimalities_P34_proof : CoverCoprimalityP34Spec :=
  ⟨isCoprime_P34_P34_deriv, isCoprime_P34_X, isCoprime_P34_X_sub_1, isCoprime_P34_Q5,
   isCoprime_P34_cb_h, isCoprime_P34_ca_h, isCoprime_P34_nm_WU, isCoprime_P34_disc_E0,
   isCoprime_P34_nm_d1_z, isCoprime_P34_nm_disc_E2z, isCoprime_P34_nm_detM_W⟩

end CoverCoprimeP34Proof
end SymmetricSexticResidual.CoverAlgebra

theorem solution : SymmetricSexticResidual.CoverAlgebra.CoverCoprimalityP34Spec :=
  SymmetricSexticResidual.CoverAlgebra.cover_coprimalities_P34_proof
