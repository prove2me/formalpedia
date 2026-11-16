-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.srcS_inj
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T12:13:53.802+00:00
-- url     : https://prove2.me/submissions/489d98a1-9041-4f87-933d-958e111902af

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

def srcS_vals : List ℕ := [
  0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 77, 84, 91, 98, 105,
  112, 119, 126, 133, 140, 149, 156, 162, 168, 174, 180, 186, 192, 198, 204, 210,
  216, 222, 228, 234, 240, 246, 252, 258, 264, 271, 277, 283, 289, 295, 301, 307,
  313, 319, 325, 331, 337, 343, 349, 355, 361, 367, 373, 379, 386, 393, 399, 405,
  411, 417, 423, 429, 435, 441, 447, 453, 459, 465, 471, 477, 483, 489, 496, 502,
  508, 514, 520, 526, 532, 538, 544, 550, 556, 562, 568, 574, 580, 586, 592, 599,
  606, 612, 618, 624, 630, 636, 642, 648, 654, 660, 666, 672, 678, 684, 690, 697,
  703, 709, 715, 721, 727, 733, 739, 745, 751, 757, 763, 769, 775, 781, 788, 795,
  801, 807, 813, 819, 825, 831, 837, 843, 849, 855, 861, 867, 874, 880, 886, 892,
  898, 904, 910, 916, 922, 928, 934, 940, 946, 953, 960, 966, 972, 978, 984, 990,
  996, 1002, 1008, 1014, 1020, 1027, 1033, 1039, 1045, 1051, 1057, 1063, 1069, 1075, 1081, 1087,
  1094, 1101, 1107, 1113, 1119, 1125, 1131, 1137, 1143, 1149, 1156, 1162, 1168, 1174, 1180, 1186,
  1192, 1198, 1204, 1211, 1218, 1224, 1230, 1236, 1242, 1248, 1254, 1261, 1267, 1273, 1279, 1285,
  1291, 1297, 1304, 1311, 1317, 1323, 1329, 1335, 1342, 1348, 1354, 1360, 1366, 1373, 1380, 1386,
  1392, 1399, 1405, 1411, 1418, 1425, 1432, 1439, 1446, 1452, 1458, 1464, 1470, 1476, 1482, 1488,
  1494, 1500, 1506, 1512, 1518, 1524, 1530, 1536, 1542, 1548, 1554, 1561, 1567, 1573, 1579, 1585,
  1591, 1597, 1603, 1609, 1615, 1621, 1627, 1633, 1639, 1645, 1651, 1657, 1663, 1669, 1676, 1683,
  1689, 1695, 1701, 1707, 1713, 1719, 1725, 1731, 1737, 1743, 1749, 1755, 1761, 1767, 1773, 1779,
  1786, 1792, 1798, 1804, 1810, 1816, 1822, 1828, 1834, 1840, 1846, 1852, 1858, 1864, 1870, 1876,
  1882, 1889, 1896, 1902, 1908, 1914, 1920, 1926, 1932, 1938, 1944, 1950, 1956, 1962, 1968, 1974,
  1980, 1987, 1993, 1999, 2005, 2011, 2017, 2023, 2029, 2035, 2041, 2047, 2053, 2059, 2065, 2071,
  2078, 2085, 2091, 2097, 2103, 2109, 2115, 2121, 2127, 2133, 2139, 2145, 2151, 2157, 2164, 2170,
  2176, 2182, 2188, 2194, 2200, 2206, 2212, 2218, 2224, 2230, 2236, 2243, 2250, 2256, 2262, 2268,
  2274, 2280, 2286, 2292, 2298, 2304, 2310, 2317, 2323, 2329, 2335, 2341, 2347, 2353, 2359, 2365,
  2371, 2377, 2384, 2391, 2397, 2403, 2409, 2415, 2421, 2427, 2433, 2439, 2446, 2452, 2458, 2464,
  2470, 2476, 2482, 2488, 2494, 2501, 2508, 2514, 2520, 2526, 2532, 2538, 2544, 2551, 2557, 2563,
  2569, 2575, 2581, 2587, 2594, 2601, 2607, 2613, 2619, 2625, 2632, 2638, 2644, 2650, 2656, 2663,
  2670, 2676, 2682, 2689, 2695, 2701, 2708, 2715, 2722, 2729, 2736, 2743, 2750, 2757, 2764, 2771,
  2778, 2785, 2792, 2799, 2806, 2813, 2820, 2827, 2834, 2841, 2848, 2855, 2864, 2871, 2877, 2883,
  2889, 2895, 2901, 2907, 2913, 2919, 2925, 2931, 2937, 2943, 2949, 2955, 2961, 2967, 2974, 2980,
  2986, 2992, 2998, 3004, 3010, 3016, 3022, 3028, 3034, 3040, 3046, 3052, 3058, 3064, 3070, 3077,
  3084, 3090, 3096, 3102, 3108, 3114, 3120, 3126, 3132, 3138, 3144, 3150, 3156, 3162, 3168, 3175,
  3181, 3187, 3193, 3199, 3205, 3211, 3217, 3223, 3229, 3235, 3241, 3247, 3253, 3259, 3266, 3273,
  3279, 3285, 3291, 3297, 3303, 3309, 3315, 3321, 3327, 3333, 3339, 3345, 3352, 3358, 3364, 3370,
  3376, 3382, 3388, 3394, 3400, 3406, 3412, 3418, 3424, 3431, 3438, 3444, 3450, 3456, 3462, 3468,
  3474, 3480, 3486, 3492, 3498, 3505, 3511, 3517, 3523, 3529, 3535, 3541, 3547, 3553, 3559, 3565,
  3572, 3579, 3585, 3591, 3597, 3603, 3609, 3615, 3621, 3627, 3634, 3640, 3646, 3652, 3658, 3664,
  3670, 3676, 3682, 3689, 3696, 3702, 3708, 3714, 3720, 3726, 3732, 3739, 3745, 3751, 3757, 3763,
  3769, 3775, 3782, 3789, 3795, 3801, 3807, 3813, 3820, 3826, 3832, 3838, 3844, 3851, 3858, 3864,
  3870, 3877, 3883, 3889, 3896, 3903, 3910, 3917, 3924, 3930, 3936, 3942, 3948, 3954, 3960, 3966,
  3972, 3978, 3984, 3990, 3996, 4002, 4008, 4014, 4020, 4027, 4033, 4039, 4045, 4051, 4057, 4063,
  4069, 4075, 4081, 4087, 4093, 4099, 4105, 4111, 4117, 4123, 4130, 4137, 4143, 4149, 4155, 4161,
  4167, 4173, 4179, 4185, 4191, 4197, 4203, 4209, 4215, 4221, 4228, 4234, 4240, 4246, 4252, 4258,
  4264, 4270, 4276, 4282, 4288, 4294, 4300, 4306, 4312, 4319, 4326, 4332, 4338, 4344, 4350, 4356,
  4362, 4368, 4374, 4380, 4386, 4392, 4398, 4405, 4411, 4417, 4423, 4429, 4435, 4441, 4447, 4453,
  4459, 4465, 4471, 4477, 4484, 4491, 4497, 4503, 4509, 4515, 4521, 4527, 4533, 4539, 4545, 4551,
  4558, 4564, 4570, 4576, 4582, 4588, 4594, 4600, 4606, 4612, 4618, 4625, 4632, 4638, 4644, 4650,
  4656, 4662, 4668, 4674, 4680, 4687, 4693, 4699, 4705, 4711, 4717, 4723, 4729, 4735, 4742, 4749,
  4755, 4761, 4767, 4773, 4779, 4785, 4792, 4798, 4804, 4810, 4816, 4822, 4828, 4835, 4842, 4848,
  4854, 4860, 4866, 4873, 4879, 4885, 4891, 4897, 4904, 4911, 4917, 4923, 4930, 4936, 4942, 4949,
  4956, 4963, 4970, 4977, 4984, 4991, 4998, 5005, 5012, 5019, 5026, 5033, 5040, 5047, 5054, 5061,
  5068, 5075, 5082, 5091, 5098, 5104, 5110, 5116, 5122, 5128, 5134, 5140, 5146, 5152, 5158, 5164,
  5170, 5176, 5182, 5189, 5195, 5201, 5207, 5213, 5219, 5225, 5231, 5237, 5243, 5249, 5255, 5261,
  5267, 5273, 5280, 5287, 5293, 5299, 5305, 5311, 5317, 5323, 5329, 5335, 5341, 5347, 5353, 5359,
  5366, 5372, 5378, 5384, 5390, 5396, 5402, 5408, 5414, 5420, 5426, 5432, 5438, 5445, 5452, 5458,
  5464, 5470, 5476, 5482, 5488, 5494, 5500, 5506, 5512, 5519, 5525, 5531, 5537, 5543, 5549, 5555,
  5561, 5567, 5573, 5579, 5586, 5593, 5599, 5605, 5611, 5617, 5623, 5629, 5635, 5641, 5648, 5654,
  5660, 5666, 5672, 5678, 5684, 5690, 5696, 5703, 5710, 5716, 5722, 5728, 5734, 5740, 5746, 5753,
  5759, 5765, 5771, 5777, 5783, 5789, 5796, 5803, 5809, 5815, 5821, 5827, 5834, 5840, 5846, 5852,
  5858, 5865, 5872, 5878, 5884, 5891, 5897, 5903, 5910, 5917, 5924, 5931, 5938, 5944, 5950, 5956,
  5962, 5968, 5974, 5980, 5986, 5992, 5998, 6004, 6010, 6016, 6022, 6029, 6035, 6041, 6047, 6053,
  6059, 6065, 6071, 6077, 6083, 6089, 6095, 6101, 6107, 6113, 6120, 6127, 6133, 6139, 6145, 6151,
  6157, 6163, 6169, 6175, 6181, 6187, 6193, 6199, 6206, 6212, 6218, 6224, 6230, 6236, 6242, 6248,
  6254, 6260, 6266, 6272, 6278, 6285, 6292, 6298, 6304, 6310, 6316, 6322, 6328, 6334, 6340, 6346,
  6352, 6359, 6365, 6371, 6377, 6383, 6389, 6395, 6401, 6407, 6413, 6419, 6426, 6433, 6439, 6445,
  6451, 6457, 6463, 6469, 6475, 6481, 6488, 6494, 6500, 6506, 6512, 6518, 6524, 6530, 6536, 6543,
  6550, 6556, 6562, 6568, 6574, 6580, 6586, 6593, 6599, 6605, 6611, 6617, 6623, 6629, 6636, 6643,
  6649, 6655, 6661, 6667, 6674, 6680, 6686, 6692, 6698, 6705, 6712, 6718, 6724, 6731, 6737, 6743,
  6750, 6757, 6764, 6771, 6778, 6785, 6792, 6799, 6806, 6813, 6820, 6827, 6834, 6841, 6848, 6855,
  6862, 6869, 6878, 6885, 6891, 6897, 6903, 6909, 6915, 6921, 6927, 6933, 6939, 6945, 6951, 6957,
  6964, 6970, 6976, 6982, 6988, 6994, 7000, 7006, 7012, 7018, 7024, 7030, 7036, 7043, 7050, 7056,
  7062, 7068, 7074, 7080, 7086, 7092, 7098, 7104, 7110, 7117, 7123, 7129, 7135, 7141, 7147, 7153,
  7159, 7165, 7171, 7177, 7184, 7191, 7197, 7203, 7209, 7215, 7221, 7227, 7233, 7239, 7246, 7252,
  7258, 7264, 7270, 7276, 7282, 7288, 7294, 7301, 7308, 7314, 7320, 7326, 7332, 7338, 7344, 7351,
  7357, 7363, 7369, 7375, 7381, 7387, 7394, 7401, 7407, 7413, 7419, 7425, 7432, 7438, 7444, 7450,
  7456, 7463, 7470, 7476, 7482, 7489, 7495, 7501, 7508, 7515, 7522, 7529, 7536, 7542, 7548, 7554,
  7560, 7566, 7572, 7578, 7584, 7590, 7596, 7602, 7608, 7615, 7621, 7627, 7633, 7639, 7645, 7651,
  7657, 7663, 7669, 7675, 7681, 7687, 7694, 7701, 7707, 7713, 7719, 7725, 7731, 7737, 7743, 7749,
  7755, 7761, 7768, 7774, 7780, 7786, 7792, 7798, 7804, 7810, 7816, 7822, 7828, 7835, 7842, 7848,
  7854, 7860, 7866, 7872, 7878, 7884, 7890, 7897, 7903, 7909, 7915, 7921, 7927, 7933, 7939, 7945,
  7952, 7959, 7965, 7971, 7977, 7983, 7989, 7995, 8002, 8008, 8014, 8020, 8026, 8032, 8038, 8045,
  8052, 8058, 8064, 8070, 8076, 8083, 8089, 8095, 8101, 8107, 8114, 8121, 8127, 8133, 8140, 8146,
  8152, 8159, 8166, 8173, 8180, 8187, 8194, 8201, 8208, 8215, 8222, 8229, 8236, 8243, 8250, 8257,
  8264, 8273, 8280, 8286, 8292, 8298, 8304, 8310, 8316, 8322, 8328, 8334, 8340, 8347, 8353, 8359,
  8365, 8371, 8377, 8383, 8389, 8395, 8401, 8407, 8414, 8421, 8427, 8433, 8439, 8445, 8451, 8457,
  8463, 8469, 8476, 8482, 8488, 8494, 8500, 8506, 8512, 8518, 8524, 8531, 8538, 8544, 8550, 8556,
  8562, 8568, 8574, 8581, 8587, 8593, 8599, 8605, 8611, 8617, 8624, 8631, 8637, 8643, 8649, 8655,
  8662, 8668, 8674, 8680, 8686, 8693, 8700, 8706, 8712, 8719, 8725, 8731, 8738, 8745, 8752, 8759,
  8766, 8772, 8778, 8784, 8790, 8796, 8802, 8808, 8814, 8820, 8826, 8833, 8839, 8845, 8851, 8857,
  8863, 8869, 8875, 8881, 8887, 8893, 8900, 8907, 8913, 8919, 8925, 8931, 8937, 8943, 8949, 8955,
  8962, 8968, 8974, 8980, 8986, 8992, 8998, 9004, 9010, 9017, 9024, 9030, 9036, 9042, 9048, 9054,
  9060, 9067, 9073, 9079, 9085, 9091, 9097, 9103, 9110, 9117, 9123, 9129, 9135, 9141, 9148, 9154,
  9160, 9166, 9172, 9179, 9186, 9192, 9198, 9205, 9211, 9217, 9224, 9231, 9238, 9245, 9252, 9259,
  9266, 9273, 9280, 9287, 9294, 9301, 9308, 9315, 9324, 9331, 9337, 9343, 9349, 9355, 9361, 9367,
  9373, 9379, 9386, 9392, 9398, 9404, 9410, 9416, 9422, 9428, 9434, 9441, 9448, 9454, 9460, 9466,
  9472, 9478, 9484, 9491, 9497, 9503, 9509, 9515, 9521, 9527, 9534, 9541, 9547, 9553, 9559, 9565,
  9572, 9578, 9584, 9590, 9596, 9603, 9610, 9616, 9622, 9629, 9635, 9641, 9648, 9655, 9662, 9669,
  9676, 9682, 9688, 9694, 9700, 9706, 9712, 9718, 9724, 9731, 9737, 9743, 9749, 9755, 9761, 9767,
  9773, 9779, 9786, 9793, 9799, 9805, 9811, 9817, 9823, 9829, 9836, 9842, 9848, 9854, 9860, 9866,
  9872, 9879, 9886, 9892, 9898, 9904, 9910, 9917, 9923, 9929, 9935, 9941, 9948, 9955, 9961, 9967,
  9974, 9980, 9986, 9993, 10000, 10007, 10014, 10021, 10028, 10035, 10042, 10049, 10056, 10063, 10070, 10079,
  10086, 10092, 10098, 10104, 10110, 10116, 10122, 10129, 10135, 10141, 10147, 10153, 10159, 10165, 10172, 10179,
  10185, 10191, 10197, 10203, 10210, 10216, 10222, 10228, 10234, 10241, 10248, 10254, 10260, 10267, 10273, 10279,
  10286, 10293, 10300, 10307, 10314, 10320, 10326, 10332, 10338, 10344, 10350, 10357, 10363, 10369, 10375, 10381,
  10387, 10393, 10400, 10407, 10413, 10419, 10425, 10431, 10438, 10444, 10450, 10456, 10462, 10469, 10476, 10482,
  10488, 10495, 10501, 10507, 10514, 10521, 10528, 10535, 10542, 10549, 10556, 10563, 10570, 10577, 10586, 10593,
  10599, 10605, 10611, 10617, 10624, 10630, 10636, 10642, 10648, 10655, 10662, 10668, 10674, 10681, 10687, 10693,
  10700, 10707, 10714, 10721, 10728, 10734, 10740, 10746, 10752, 10759, 10765, 10771, 10777, 10783, 10790, 10797,
  10803, 10809, 10816, 10822, 10828, 10835, 10842, 10849, 10856, 10863, 10870, 10877, 10884, 10893, 10900, 10906,
  10912, 10919, 10925, 10931, 10938, 10945, 10952, 10959, 10966, 10972, 10978, 10985, 10991, 10997, 11004, 11011,
  11018, 11025, 11032, 11039, 11048, 11055, 11062, 11069, 11076, 11083, 11090
]

def srcS_mask : ℕ := 0x4081020408100810204081020820410408102040820810410201020408102040810410208204082082081041041020408102082041040810410410208208204020408102040810204082081041020410410408208208102082082082041041041040810204082081041020410410408208208102082082082041041041040804081020408102040810204104082081020820820410410408104104104102082082082040820820820820810410410410410204081020820410408104104102082082040820820820810410410410204104104104104082082082082081008102040810204081020408102082041040810410410208208204082082082081041041041020410410410410408208208208208102082082082082082041041041041041040810204082081041020410410408208208102082082082041041041040810410410410410208208208208204082082082082082081041041041041041020102040810204081020408102040810410208204082082081041041020410410410408208208208102082082082082041041041041040810410410410410410208208208208208204082082082082082082081041041041041041041020408102082041040810410410208208204082082082081041041041020410410410410408208208208208102082082082082082041041041041041040810410410410410410410208208208208208208204020408102040810204081020408102040820810410204104104082082081020820820820410410410408104104104104102082082082082040820820820820820810410410410410410204104104104104104104082082082082082082081020820820820820820820820410410410410410410410408102040820810410204104104082082081020820820820410410410408104104104104102082082082082040820820820820820810410410410410410204104104104104104104082082082082082082081020820820820820820820820410410410410410410410408040810204081020408102040810204081020410408208102082082041041040810410410410208208208204082082082082081041041041041020410410410410410408208208208208208102082082082082082082041041041041041041040810410410410410410410410208208208208208208208204082082082082082082082082081041041041041041041041041020408102082041040810410410208208204082082082081041041041020410410410410408208208208208102082082082082082041041041041041040810410410410410410410208208208208208208204082082082082082082082081041041041041041041041020410410410410410410410410408208208208208208208208208100810204081020408102040810204081020408102082041040810410410208208204082082082081041041041020410410410410408208208208208102082082082082082041041041041041040810410410410410410410208208208208208208204082082082082082082082081041041041041041041041020410410410410410410410410408208208208208208208208208102082082082082082082082082082041041041041041041041041041040810204082081041020410410408208208102082082082041041041040810410410410410208208208208204082082082082082081041041041041041020410410410410410410408208208208208208208102082082082082082082082041041041041041041041040810410410410410410410410410208208208208208208208208204082082082082082082082082082081041041041041041041041041041020102040810204081020408102040810204081

def orBit (acc q : ℕ) : ℕ := acc ||| (1 <<< q)

def pop4 (n : ℕ) : ℕ :=
  let k := n &&& 15
  if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 1 else if k = 3 then 2
  else if k = 4 then 1 else if k = 5 then 2 else if k = 6 then 2 else if k = 7 then 3
  else if k = 8 then 1 else if k = 9 then 2 else if k = 10 then 2 else if k = 11 then 3
  else if k = 12 then 2 else if k = 13 then 3 else if k = 14 then 3 else 4

def pop16 (n : ℕ) : ℕ :=
  pop4 n + pop4 (n >>> 4) + pop4 (n >>> 8) + pop4 (n >>> 12)

def popcntF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel+1, n => if n = 0 then 0 else pop16 n + popcntF fuel (n >>> 16)

def popcnt (n : ℕ) : ℕ := popcntF 700 n

/-- Bit-support of `n` as a finite set. Abstract only; never reduced on the mask. -/
def bitFinset (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun i => n.testBit i = true)

def pop1 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else (n &&& 1) + pop1 (n >>> 1)
termination_by n
decreasing_by
  have hn : 0 < n := Nat.pos_of_ne_zero h
  simpa [Nat.shiftRight_eq_div_pow] using
    Nat.div_lt_self hn (by decide : (1 : ℕ) < 2)

theorem srcS_vals_len : srcS_vals.length = 1771 := rfl
theorem srcS_mask_fold : srcS_vals.foldl orBit 0 = srcS_mask := rfl
theorem srcS_mask_pop : popcnt srcS_mask = 1771 := rfl
theorem srcS_map_eq : (List.range v).map srcS = srcS_vals := rfl

theorem mem_bitFinset {n k : ℕ} : k ∈ bitFinset n ↔ n.testBit k = true := by
  constructor
  · intro h
    simp only [bitFinset, Finset.mem_filter] at h
    exact h.2
  · intro h
    simp only [bitFinset, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, h⟩
    have hx : 2 ^ k ≤ n := Nat.ge_two_pow_of_testBit h
    have hk : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
    exact Nat.lt_succ_of_le (le_trans hk hx)

theorem testBit_one_shift (q k : ℕ) :
    ((1 : ℕ) <<< q).testBit k = true ↔ k = q := by
  have h1 : (1 : ℕ) <<< q = 2 ^ q := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h1, Nat.testBit_two_pow]
  simp [eq_comm]

theorem testBit_orBit (acc q k : ℕ) :
    (orBit acc q).testBit k = true ↔ acc.testBit k = true ∨ k = q := by
  simp only [orBit, Nat.testBit_or, Bool.or_eq_true, testBit_one_shift]

theorem testBit_foldl (acc : ℕ) (L : List ℕ) (k : ℕ) :
    (L.foldl orBit acc).testBit k = true ↔ acc.testBit k = true ∨ k ∈ L := by
  induction L generalizing acc with
  | nil =>
    simp
  | cons q L ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    constructor
    · intro h
      rcases h with h | h
      · rcases (testBit_orBit acc q k).1 h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · intro h
      rcases h with h | h | h
      · exact Or.inl ((testBit_orBit acc q k).2 (Or.inl h))
      · exact Or.inl ((testBit_orBit acc q k).2 (Or.inr h))
      · exact Or.inr h

theorem testBit_fold_zero (L : List ℕ) (k : ℕ) :
    (L.foldl orBit 0).testBit k = true ↔ k ∈ L := by
  simpa [Nat.zero_testBit] using testBit_foldl 0 L k

theorem bitFinset_fold (L : List ℕ) :
    bitFinset (L.foldl orBit 0) = L.toFinset := by
  ext k
  simp [mem_bitFinset, testBit_fold_zero, List.mem_toFinset]


theorem and_one_eq_testBit (n : ℕ) :
    n &&& 1 = if n.testBit 0 = true then 1 else 0 := by
  rw [Nat.and_comm, Nat.one_and_eq_mod_two]
  have hbit : n.testBit 0 = decide (n % 2 = 1) := by
    simp [Nat.testBit_zero]
  rw [hbit]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [h]
  · simp [h]

theorem bitFinset_decomp (n : ℕ) :
    bitFinset n =
      (if n.testBit 0 = true then ({0} : Finset ℕ) else ∅) ∪
        (bitFinset (n >>> 1)).map ⟨Nat.succ, Nat.succ_injective⟩ := by
  ext k
  constructor
  · intro hk
    have hbit : n.testBit k = true := mem_bitFinset.1 hk
    cases k with
    | zero =>
      simp [hbit]
    | succ k =>
      refine Finset.mem_union.2 (Or.inr ?_)
      refine Finset.mem_map.2 ⟨k, ?_, rfl⟩
      have hbit' : n.testBit (1 + k) = true := by
        rwa [Nat.add_comm]
      exact mem_bitFinset.2 (by simpa [Nat.testBit_shiftRight] using hbit')
  · intro hk
    simp only [Finset.mem_union] at hk
    rcases hk with hk | hk
    · split_ifs at hk with ht
      · simp only [Finset.mem_singleton] at hk
        subst k
        exact mem_bitFinset.2 ht
      · simp at hk
    · rcases Finset.mem_map.1 hk with ⟨k', hk', rfl⟩
      have hbit' : (n >>> 1).testBit k' = true := mem_bitFinset.1 hk'
      have : n.testBit (1 + k') = true := by
        simpa [Nat.testBit_shiftRight] using hbit'
      exact mem_bitFinset.2 (by rwa [Nat.add_comm] at this)

theorem disjoint_bitFinset_decomp (n : ℕ) :
    Disjoint (if n.testBit 0 = true then ({0} : Finset ℕ) else ∅)
      ((bitFinset (n >>> 1)).map ⟨Nat.succ, Nat.succ_injective⟩) := by
  refine Finset.disjoint_left.2 ?_
  intro a ha hb
  rcases Finset.mem_map.1 hb with ⟨k, -, hka⟩
  have hsucc : a = Nat.succ k := by
    simpa [Function.Embedding.coeFn_mk] using hka.symm
  have ha0 : a = 0 := by
    split_ifs at ha with _ht
    · exact Finset.mem_singleton.1 ha
    · exact False.elim (by simp at ha)
  exact Nat.succ_ne_zero k (hsucc.symm.trans ha0)

theorem pop1_zero : pop1 0 = 0 := by
  simp [pop1]

theorem bitFinset_zero : bitFinset 0 = ∅ := by
  ext k
  simp [mem_bitFinset, Nat.zero_testBit]

theorem pop1_pos {n : ℕ} (h : n ≠ 0) : pop1 n = (n &&& 1) + pop1 (n >>> 1) := by
  rw [pop1, dif_neg h]

theorem pop1_eq_card (n : ℕ) : pop1 n = (bitFinset n).card := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · subst n
      rw [pop1_zero, bitFinset_zero, Finset.card_empty]
    · have hlt : n >>> 1 < n := by
        have hn : 0 < n := Nat.pos_of_ne_zero h
        simpa [Nat.shiftRight_eq_div_pow] using
          Nat.div_lt_self hn (by decide : (1 : ℕ) < 2)
      rw [pop1_pos h, ih (n >>> 1) hlt, bitFinset_decomp n,
        Finset.card_union_of_disjoint (disjoint_bitFinset_decomp n),
        Finset.card_map, and_one_eq_testBit]
      split_ifs with _ht
      · rw [Finset.card_singleton]
      · rw [Finset.card_empty, Nat.zero_add]


theorem bitFinset_or (a b : ℕ) :
    bitFinset (a ||| b) = bitFinset a ∪ bitFinset b := by
  ext k
  simp only [mem_bitFinset, Nat.testBit_or, Bool.or_eq_true, Finset.mem_union]

theorem pop1_or_disjoint (a b : ℕ)
    (h : ∀ i, a.testBit i = true → b.testBit i = true → False) :
    pop1 (a ||| b) = pop1 a + pop1 b := by
  rw [pop1_eq_card, pop1_eq_card, pop1_eq_card, bitFinset_or,
    Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.2 ?_
  intro x hx hy
  exact h x (mem_bitFinset.1 hx) (mem_bitFinset.1 hy)

theorem decompose_mod_shift (n k : ℕ) :
    (n % 2 ^ k) ||| ((n >>> k) <<< k) = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases hi : i < k
  · simp [hi]
  · have hik : k ≤ i := Nat.le_of_not_gt hi
    have hadd : k + (i - k) = i := Nat.add_sub_cancel' hik
    have : ((n >>> k).testBit (i - k)) = n.testBit i := by
      rw [Nat.testBit_shiftRight, hadd]
    simp [hi, hik, this]

theorem bitFinset_shiftLeft (n k : ℕ) :
    bitFinset (n <<< k) =
      (bitFinset n).map ⟨fun i => i + k, add_left_injective k⟩ := by
  ext j
  constructor
  · intro hj
    have hshift : (n <<< k).testBit j = true := mem_bitFinset.1 hj
    have hbits : (decide (k ≤ j) && n.testBit (j - k)) = true := by
      simpa [Nat.testBit_shiftLeft] using hshift
    have hpair : decide (k ≤ j) = true ∧ n.testBit (j - k) = true := by
      simpa [Bool.and_eq_true] using hbits
    have hkj : k ≤ j := of_decide_eq_true hpair.1
    refine Finset.mem_map.2 ⟨j - k, mem_bitFinset.2 hpair.2, ?_⟩
    exact Nat.sub_add_cancel hkj
  · intro hj
    rcases Finset.mem_map.1 hj with ⟨i, hi, rfl⟩
    have hbit : n.testBit i = true := mem_bitFinset.1 hi
    have : (n <<< k).testBit (i + k) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_left, Nat.add_sub_cancel_left, hbit]
    exact mem_bitFinset.2 this

theorem pop1_shiftLeft (n k : ℕ) : pop1 (n <<< k) = pop1 n := by
  rw [pop1_eq_card, pop1_eq_card, bitFinset_shiftLeft, Finset.card_map]

theorem pop1_add_shift (n k : ℕ) :
    pop1 n = pop1 (n % 2 ^ k) + pop1 (n >>> k) := by
  have hdec : n = (n % 2 ^ k) ||| ((n >>> k) <<< k) :=
    (decompose_mod_shift n k).symm
  conv_lhs => rw [hdec]
  rw [pop1_or_disjoint]
  · rw [pop1_shiftLeft]
  · intro i hlo hhi
    have hilt : i < k := by
      have hmod : (n % 2 ^ k).testBit i = (decide (i < k) && n.testBit i) :=
        Nat.testBit_mod_two_pow n k i
      have hand : (decide (i < k) && n.testBit i) = true := by
        rwa [← hmod]
      have hpair : decide (i < k) = true ∧ n.testBit i = true := by
        simpa [Bool.and_eq_true] using hand
      exact of_decide_eq_true hpair.1
    have hkle : k ≤ i := by
      have hshift : (decide (k ≤ i) && (n >>> k).testBit (i - k)) = true := by
        simpa [Nat.testBit_shiftLeft] using hhi
      have hpair : decide (k ≤ i) = true ∧ (n >>> k).testBit (i - k) = true := by
        simpa [Bool.and_eq_true] using hshift
      exact of_decide_eq_true hpair.1
    exact (Nat.not_le_of_gt hilt) hkle


theorem pop1_lt_16 (n : ℕ) (h : n < 16) : pop1 n = pop4 n := by
  interval_cases n <;> simp [pop1, pop4]

theorem pop4_eq_low (n : ℕ) : pop4 n = pop4 (n &&& 15) := by
  unfold pop4
  have h : (n &&& 15) &&& 15 = n &&& 15 := by
    rw [Nat.and_assoc, show ((15 : ℕ) &&& 15) = 15 from rfl]
  rw [h]

theorem pop4_eq_pop1_mod16 (n : ℕ) : pop4 n = pop1 (n % 16) := by
  have h15 : (15 : ℕ) = 2 ^ 4 - 1 := rfl
  have hand : n &&& 15 = n % 16 := by
    rw [h15, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : n &&& 15 < 16 := by
    have : (15 : ℕ) < 2 ^ 4 := by decide
    exact Nat.and_lt_two_pow n this
  rw [pop4_eq_low, hand, pop1_lt_16 _ (by rwa [hand] at hlt)]

theorem mod_pow_mod (n a b : ℕ) (h : b ≤ a) : n % 2 ^ a % 2 ^ b = n % 2 ^ b := by
  have : 2 ^ b ∣ 2 ^ a := Nat.pow_dvd_pow (2 : ℕ) h
  exact Nat.mod_mod_of_dvd n this

theorem shiftRight_mod_pow (n k m : ℕ) :
    (n % 2 ^ (k + m)) >>> k = (n >>> k) % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  simp [Nat.add_lt_add_iff_left]

theorem pop16_eq_pop1_mod (n : ℕ) : pop16 n = pop1 (n % 2 ^ 16) := by
  have peel4 (x : ℕ) : pop1 x = pop1 (x % 16) + pop1 (x >>> 4) := by
    change pop1 x = pop1 (x % 2 ^ 4) + pop1 (x >>> 4)
    exact pop1_add_shift x 4
  have hsr : ∀ (x a b : ℕ), (x >>> a) >>> b = x >>> (a + b) := by
    intro x a b
    simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_add]
  have h0 := peel4 (n % 2 ^ 16)
  have h1 := peel4 ((n % 2 ^ 16) >>> 4)
  have h2 := peel4 (((n % 2 ^ 16) >>> 4) >>> 4)
  have h3 := peel4 ((((n % 2 ^ 16) >>> 4) >>> 4) >>> 4)
  have htail' : (((((n % 2 ^ 16) >>> 4) >>> 4) >>> 4) >>> 4) = 0 := by
    rw [hsr, hsr, hsr]
    change (n % 2 ^ 16) >>> 16 = 0
    have : n % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (Nat.two_pow_pos _)
    simp [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt this]
  have r0 : (n % 2 ^ 16) % 16 = n % 16 := by
    change (n % 2 ^ 16) % (2 ^ 4) = n % (2 ^ 4)
    exact mod_pow_mod n 16 4 (by decide)
  have r1 : ((n % 2 ^ 16) >>> 4) % 16 = (n >>> 4) % 16 := by
    have hsh : (n % 2 ^ 16) >>> 4 = (n >>> 4) % 2 ^ 12 := by
      change (n % 2 ^ (4 + 12)) >>> 4 = (n >>> 4) % 2 ^ 12
      exact shiftRight_mod_pow n 4 12
    change ((n % 2 ^ 16) >>> 4) % (2 ^ 4) = (n >>> 4) % (2 ^ 4)
    rw [hsh]
    exact mod_pow_mod (n >>> 4) 12 4 (by decide)
  have r2 : (((n % 2 ^ 16) >>> 4) >>> 4) % 16 = (n >>> 8) % 16 := by
    have hx : ((n % 2 ^ 16) >>> 4) >>> 4 = (n % 2 ^ 16) >>> 8 := by
      rw [hsr]
    have hsh : (n % 2 ^ 16) >>> 8 = (n >>> 8) % 2 ^ 8 := by
      change (n % 2 ^ (8 + 8)) >>> 8 = (n >>> 8) % 2 ^ 8
      exact shiftRight_mod_pow n 8 8
    change (((n % 2 ^ 16) >>> 4) >>> 4) % (2 ^ 4) = (n >>> 8) % (2 ^ 4)
    rw [hx, hsh]
    exact mod_pow_mod (n >>> 8) 8 4 (by decide)
  have r3 : ((((n % 2 ^ 16) >>> 4) >>> 4) >>> 4) % 16 = (n >>> 12) % 16 := by
    have hx : (((n % 2 ^ 16) >>> 4) >>> 4) >>> 4 = (n % 2 ^ 16) >>> 12 := by
      rw [hsr, hsr]
    have hsh : (n % 2 ^ 16) >>> 12 = (n >>> 12) % 2 ^ 4 := by
      change (n % 2 ^ (12 + 4)) >>> 12 = (n >>> 12) % 2 ^ 4
      exact shiftRight_mod_pow n 12 4
    change ((((n % 2 ^ 16) >>> 4) >>> 4) >>> 4) % (2 ^ 4) = (n >>> 12) % (2 ^ 4)
    rw [hx, hsh]
    exact Nat.mod_mod _ _
  rw [pop16, pop4_eq_pop1_mod16, pop4_eq_pop1_mod16, pop4_eq_pop1_mod16,
    pop4_eq_pop1_mod16, h0, r0, h1, r1, h2, r2, h3, r3, htail', pop1_zero]
  ac_rfl


theorem pop1_eq_popcntF (fuel n : ℕ) (h : n < 2 ^ (16 * fuel)) :
    pop1 n = popcntF fuel n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := Nat.lt_one_iff.mp (by simpa using h)
    rw [hn, pop1_zero]
    simp [popcntF]
  | succ fuel ih =>
    unfold popcntF
    by_cases hn : n = 0
    · rw [hn, pop1_zero]
      simp
    · have hsplit : pop1 n = pop16 n + pop1 (n >>> 16) := by
        have := pop1_add_shift n 16
        rwa [pop16_eq_pop1_mod]
      have hlt : n >>> 16 < 2 ^ (16 * fuel) := by
        have hpow : 16 * fuel.succ = 16 * fuel + 16 := Nat.mul_succ _ _
        have hnlt : n < 2 ^ (16 * fuel + 16) := by
          rwa [hpow] at h
        have hpa : 2 ^ (16 * fuel + 16) = 2 ^ (16 * fuel) * 2 ^ 16 :=
          Nat.pow_add _ _ _
        have : n < 2 ^ (16 * fuel) * 2 ^ 16 := by rwa [hpa] at hnlt
        have : n / 2 ^ 16 < 2 ^ (16 * fuel) :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at this)
        simpa [Nat.shiftRight_eq_div_pow] using this
      rw [if_neg hn, hsplit, ih (n >>> 16) hlt]

theorem srcS_vals_all_lt : srcS_vals.all (fun q => decide (q < 11091)) = true := rfl

theorem srcS_vals_lt_11091 : ∀ q ∈ srcS_vals, q < 11091 := by
  intro q hq
  have hall : ∀ q ∈ srcS_vals, decide (q < 11091) = true := by
    simpa [List.all_eq_true] using srcS_vals_all_lt
  exact of_decide_eq_true (hall q hq)

theorem lt_two_pow_of_high_bits {n M : ℕ}
    (h : ∀ k, n.testBit k = true → k < M) : n < 2 ^ M := by
  by_contra hge
  have : 2 ^ M ≤ n := Nat.le_of_not_gt hge
  rcases Nat.exists_ge_and_testBit_of_ge_two_pow this with ⟨i, hi, hbit⟩
  have htrue : n.testBit i = true := by
    simpa using hbit
  have : i < M := h i htrue
  exact (Nat.not_le_of_gt this) hi

theorem srcS_mask_lt : srcS_mask < 2 ^ (16 * 700) := by
  have hbits : ∀ k, srcS_mask.testBit k = true → k < 11091 := by
    intro k hk
    have : (srcS_vals.foldl orBit 0).testBit k = true := by
      rwa [srcS_mask_fold]
    have : k ∈ srcS_vals := (testBit_fold_zero srcS_vals k).1 this
    exact srcS_vals_lt_11091 k this
  have hlt : srcS_mask < 2 ^ 11091 := lt_two_pow_of_high_bits hbits
  have hle : 2 ^ 11091 ≤ 2 ^ (16 * 700) :=
    Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2) (by decide : 11091 ≤ 16 * 700)
  exact Nat.lt_of_lt_of_le hlt hle

theorem srcS_vals_nodup : srcS_vals.Nodup := by
  have hpop1 : pop1 srcS_mask = 1771 := by
    have h := pop1_eq_popcntF 700 srcS_mask srcS_mask_lt
    have hp : popcntF 700 srcS_mask = 1771 := srcS_mask_pop
    exact h.trans hp
  have hcard : srcS_vals.toFinset.card = srcS_vals.length := by
    calc
      srcS_vals.toFinset.card
          = (bitFinset (srcS_vals.foldl orBit 0)).card := by
            rw [bitFinset_fold]
      _ = (bitFinset srcS_mask).card := by rw [srcS_mask_fold]
      _ = pop1 srcS_mask := (pop1_eq_card srcS_mask).symm
      _ = 1771 := hpop1
      _ = srcS_vals.length := srcS_vals_len.symm
  have hm :
      (↑srcS_vals : Multiset ℕ).toFinset.card =
        Multiset.card (↑srcS_vals : Multiset ℕ) := by
    rw [List.toFinset_coe, Multiset.coe_card]
    exact hcard
  have hnd : (↑srcS_vals : Multiset ℕ).Nodup :=
    (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑srcS_vals : Multiset ℕ))).1 hm
  exact Multiset.coe_nodup.1 hnd

theorem solution {t t' : ℕ} (ht : t < v) (ht' : t' < v)
    (heq : srcS t = srcS t') : t = t' := by
  have nd : srcS_vals.Nodup := srcS_vals_nodup
  have hlen : srcS_vals.length = v := by
    have hv : v = 1771 := rfl
    rw [srcS_vals_len, hv]
  have htL : t < srcS_vals.length := by rw [hlen]; exact ht
  have htL' : t' < srcS_vals.length := by rw [hlen]; exact ht'
  have hget_t : srcS t = srcS_vals[t]'htL := by
    have hidx : t < ((List.range v).map srcS).length := by
      simpa [srcS_map_eq] using htL
    have heql : srcS_vals[t]'htL = ((List.range v).map srcS)[t]'hidx := by
      simp [srcS_map_eq]
    rw [heql, List.getElem_map, List.getElem_range]
  have hget_t' : srcS t' = srcS_vals[t']'htL' := by
    have hidx : t' < ((List.range v).map srcS).length := by
      simpa [srcS_map_eq] using htL'
    have heql : srcS_vals[t']'htL' = ((List.range v).map srcS)[t']'hidx := by
      simp [srcS_map_eq]
    rw [heql, List.getElem_map, List.getElem_range]
  have : srcS_vals.get ⟨t, htL⟩ = srcS_vals.get ⟨t', htL'⟩ := by
    change srcS_vals[t] = srcS_vals[t']
    rw [← hget_t, ← hget_t', heq]
  exact Fin.val_eq_of_eq ((List.Nodup.get_inj_iff nd).1 this)
