-- Prove2me | solution 1 for LeanEval.NumberTheory.lagarias_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:57:20.501642+00:00
-- url     : https://prove2.me/submissions/c0154243-1c35-4f5d-a422-b34868aef5fc

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped ArithmeticFunction.sigma
open Finset

namespace LagariasFiniteCertificate

def lowerHarmonicInt : ℕ → ℕ
  | 0 => 0
  | n + 1 => lowerHarmonicInt n + 1000000 / (n + 1)

def lowerHarmonic (n : ℕ) : ℚ := (lowerHarmonicInt n : ℚ) / 1000000

def lowerExp (x : ℚ) : ℚ := ∑ k ∈ range 18, x ^ k / (k.factorial : ℚ)

def lowerLog (x : ℚ) : ℚ :=
  2 * ∑ k ∈ range 5, ((x - 1) / (x + 1)) ^ (2 * k + 1) / (2 * k + 1)


set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Integer-coefficient Horner evaluation, with a single final factorial division. -/
def lowerExpFast (q : ℚ) : ℚ :=
  (((((((((((((((((1 * q + 17) * q + 272) * q + 4080) * q + 57120) * q + 742560) * q + 8910720) * q + 98017920) * q + 980179200) * q + 8821612800) * q + 70572902400) * q + 494010316800) * q + 2964061900800) * q + 14820309504000) * q + 59281238016000) * q + 177843714048000) * q + 355687428096000) * q + 355687428096000) / 355687428096000

/-- Horner evaluation in z² of the five-term odd logarithm expansion. -/
def lowerLogFast (q : ℚ) : ℚ :=
  let z := (q - 1) / (q + 1)
  let t := z * z
  2 * z * (315 + t * (105 + t * (63 + t * (45 + 35 * t)))) / 315

lemma lowerExpFast_eq (q : ℚ) : lowerExpFast q = lowerExp q := by
  norm_num [lowerExpFast, lowerExp, sum_range_succ, Nat.factorial]
  ring

lemma lowerLogFast_eq (q : ℚ) : lowerLogFast q = lowerLog q := by
  norm_num [lowerLogFast, lowerLog, sum_range_succ]
  ring


def sigmaFast (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, ∑ i ∈ range (n.primeFactorsList.count p + 1), p ^ i

theorem sigmaFast_eq {n : ℕ} (hn : n ≠ 0) : sigmaFast n = σ 1 n := by
  simpa only [sigmaFast, Nat.primeFactorsList_count_eq, mul_one] using
    (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) hn).symm

def expressionAtInt (q : ℕ) : ℚ :=
  (q : ℚ) / 1000000 + lowerExp ((q : ℚ) / 1000000) * lowerLog ((q : ℚ) / 1000000)

def certifiedList (n h : ℕ) : List ℕ → Bool
  | [] => true
  | q :: qs =>
    decide (q = h + 1000000 / (n + 1)) &&
    decide (1 < n + 1 → (sigmaFast (n + 1) : ℚ) < expressionAtInt q) &&
    certifiedList (n + 1) q qs

def expressionAtIntFast (q : ℕ) : ℚ :=
  (q : ℚ) / 1000000 + lowerExpFast ((q : ℚ) / 1000000) * lowerLogFast ((q : ℚ) / 1000000)

lemma expressionAtIntFast_eq (q : ℕ) : expressionAtIntFast q = expressionAtInt q := by
  simp only [expressionAtIntFast, expressionAtInt, lowerExpFast_eq, lowerLogFast_eq]

def certifiedListFast (n h : ℕ) : List ℕ → Bool
  | [] => true
  | q :: qs =>
    decide (q = h + 1000000 / (n + 1)) &&
    decide (1 < n + 1 → (sigmaFast (n + 1) : ℚ) < expressionAtIntFast q) &&
    certifiedListFast (n + 1) q qs

lemma certifiedListFast_eq (n h : ℕ) (xs : List ℕ) :
    certifiedListFast n h xs = certifiedList n h xs := by
  induction xs generalizing n h with
  | nil => rfl
  | cons q qs ih =>
    simp only [certifiedListFast, certifiedList, expressionAtIntFast_eq, ih]


theorem certifiedList_sound (xs : List ℕ) :
    ∀ n h : ℕ, certifiedList n h xs = true → h = lowerHarmonicInt n →
      ∀ i : ℕ, n < i → i ≤ n + xs.length → 1 < i →
        (sigmaFast i : ℚ) < lowerHarmonic i +
          lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  induction xs with
  | nil =>
    intro n h hc hh i hi hmax hi1
    simp only [List.length_nil, Nat.add_zero] at hmax
    omega
  | cons q qs ih =>
    intro n h hc hh i hi hmax hi1
    have hp : ((q = h + 1000000 / (n + 1)) ∧
        (1 < n + 1 → (sigmaFast (n + 1) : ℚ) < expressionAtInt q)) ∧
        certifiedList (n + 1) q qs = true := by
      simpa only [certifiedList, Bool.and_eq_true, decide_eq_true_eq] using hc
    have hq : q = lowerHarmonicInt (n + 1) := by
      simpa only [lowerHarmonicInt, ← hh] using hp.1.1
    by_cases heq : i = n + 1
    · subst i
      simpa only [expressionAtInt, hq, lowerHarmonic] using hp.1.2 hi1
    · apply ih (n + 1) q hp.2 hq i (by omega)
      · simp only [List.length_cons] at hmax
        omega
      · exact hi1


def values0 : List ℕ := [
  1000000, 1500000, 1833333, 2083333, 2283333, 2449999, 2592856, 2717856, 2828967, 2928967, 3019876, 3103209, 3180132, 3251560, 3318226, 3380726,
  3439549, 3495104, 3547735, 3597735, 3645354, 3690808, 3734286, 3775952, 3815952, 3854413, 3891450, 3927164, 3961646, 3994979, 4027237, 4058487,
  4088790, 4118201, 4146772, 4174549, 4201576, 4227891, 4253532, 4278532, 4302922, 4326731, 4349986, 4372713, 4394935, 4416674, 4437950, 4458783,
  4479191, 4499191, 4518798, 4538028, 4556895, 4575413, 4593594, 4611451, 4628994, 4646235, 4663184, 4679850, 4696243, 4712372, 4728245, 4743870,
  4759254, 4774405, 4789330, 4804035, 4818527, 4832812, 4846896, 4860784, 4874482, 4887995, 4901328, 4914485, 4927472, 4940292, 4952950, 4965450,
  4977795, 4989990, 5002038, 5013942, 5025706, 5037333, 5048827, 5060190, 5071425, 5082536, 5093525, 5104394, 5115146, 5125784, 5136310, 5146726,
  5157035, 5167239, 5177340, 5187340
]
theorem checked0 : certifiedList 0 0 values0 = true := by
  have h : certifiedListFast 0 0 values0 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block0 (i : ℕ) (hlo : 0 < i) (hhi : i ≤ 100) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values0.length = 100 := by decide +kernel
  have hh : 0 = lowerHarmonicInt 0 := by decide +kernel
  have h := certifiedList_sound values0 0 0 checked0 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values1 : List ℕ := [
  5197240, 5207043, 5216751, 5226366, 5235889, 5245322, 5254667, 5263926, 5273100, 5282190, 5291199, 5300127, 5308976, 5317747, 5326442, 5335062,
  5343609, 5352083, 5360486, 5368819, 5377083, 5385279, 5393409, 5401473, 5409473, 5417409, 5425283, 5433095, 5440846, 5448538, 5456171, 5463746,
  5471264, 5478726, 5486133, 5493485, 5500784, 5508030, 5515224, 5522366, 5529458, 5536500, 5543493, 5550437, 5557333, 5564182, 5570984, 5577740,
  5584451, 5591117, 5597739, 5604317, 5610852, 5617345, 5623796, 5630206, 5636575, 5642904, 5649193, 5655443, 5661654, 5667826, 5673960, 5680057,
  5686117, 5692141, 5698129, 5704081, 5709998, 5715880, 5721727, 5727540, 5733320, 5739067, 5744781, 5750462, 5756111, 5761728, 5767314, 5772869,
  5778393, 5783887, 5789351, 5794785, 5800190, 5805566, 5810913, 5816232, 5821523, 5826786, 5832021, 5837229, 5842410, 5847564, 5852692, 5857794,
  5862870, 5867920, 5872945, 5877945
]
theorem checked1 : certifiedList 100 5187340 values1 = true := by
  have h : certifiedListFast 100 5187340 values1 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block1 (i : ℕ) (hlo : 100 < i) (hhi : i ≤ 200) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values1.length = 100 := by decide +kernel
  have hh : 5187340 = lowerHarmonicInt 100 := by decide +kernel
  have h := certifiedList_sound values1 100 5187340 checked1 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values2 : List ℕ := [
  5882920, 5887870, 5892796, 5897697, 5902575, 5907429, 5912259, 5917066, 5921850, 5926611, 5931350, 5936066, 5940760, 5945432, 5950083, 5954712,
  5959320, 5963907, 5968473, 5973018, 5977542, 5982046, 5986530, 5990994, 5995438, 5999862, 6004267, 6008652, 6013018, 6017365, 6021694, 6026004,
  6030295, 6034568, 6038823, 6043060, 6047279, 6051480, 6055664, 6059830, 6063979, 6068111, 6072226, 6076324, 6080405, 6084470, 6088518, 6092550,
  6096566, 6100566, 6104550, 6108518, 6112470, 6116407, 6120328, 6124234, 6128125, 6132000, 6135861, 6139707, 6143538, 6147354, 6151156, 6154943,
  6158716, 6162475, 6166220, 6169951, 6173668, 6177371, 6181061, 6184737, 6188400, 6192049, 6195685, 6199308, 6202918, 6206515, 6210099, 6213670,
  6217228, 6220774, 6224307, 6227828, 6231336, 6234832, 6238316, 6241788, 6245248, 6248696, 6252132, 6255556, 6258968, 6262369, 6265758, 6269136,
  6272503, 6275858, 6279202, 6282535
]
theorem checked2 : certifiedList 200 5877945 values2 = true := by
  have h : certifiedListFast 200 5877945 values2 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block2 (i : ℕ) (hlo : 200 < i) (hhi : i ≤ 300) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values2.length = 100 := by decide +kernel
  have hh : 5877945 = lowerHarmonicInt 200 := by decide +kernel
  have h := certifiedList_sound values2 200 5877945 checked2 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values3 : List ℕ := [
  6285857, 6289168, 6292468, 6295757, 6299035, 6302302, 6305559, 6308805, 6312041, 6315266, 6318481, 6321686, 6324880, 6328064, 6331238, 6334402,
  6337556, 6340700, 6343834, 6346959, 6350074, 6353179, 6356274, 6359360, 6362436, 6365503, 6368561, 6371609, 6374648, 6377678, 6380699, 6383711,
  6386714, 6389708, 6392693, 6395669, 6398636, 6401594, 6404543, 6407484, 6410416, 6413339, 6416254, 6419160, 6422058, 6424948, 6427829, 6430702,
  6433567, 6436424, 6439273, 6442113, 6444945, 6447769, 6450585, 6453393, 6456194, 6458987, 6461772, 6464549, 6467319, 6470081, 6472835, 6475582,
  6478321, 6481053, 6483777, 6486494, 6489204, 6491906, 6494601, 6497289, 6499969, 6502642, 6505308, 6507967, 6510619, 6513264, 6515902, 6518533,
  6521157, 6523774, 6526384, 6528988, 6531585, 6534175, 6536758, 6539335, 6541905, 6544469, 6547026, 6549577, 6552121, 6554659, 6557190, 6559715,
  6562233, 6564745, 6567251, 6569751
]
theorem checked3 : certifiedList 300 6282535 values3 = true := by
  have h : certifiedListFast 300 6282535 values3 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block3 (i : ℕ) (hlo : 300 < i) (hhi : i ≤ 400) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values3.length = 100 := by decide +kernel
  have hh : 6282535 = lowerHarmonicInt 300 := by decide +kernel
  have h := certifiedList_sound values3 300 6282535 checked3 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values4 : List ℕ := [
  6572244, 6574731, 6577212, 6579687, 6582156, 6584619, 6587076, 6589526, 6591970, 6594409, 6596842, 6599269, 6601690, 6604105, 6606514, 6608917,
  6611315, 6613707, 6616093, 6618473, 6620848, 6623217, 6625581, 6627939, 6630291, 6632638, 6634979, 6637315, 6639646, 6641971, 6644291, 6646605,
  6648914, 6651218, 6653516, 6655809, 6658097, 6660380, 6662657, 6664929, 6667196, 6669458, 6671715, 6673967, 6676214, 6678456, 6680693, 6682925,
  6685152, 6687374, 6689591, 6691803, 6694010, 6696212, 6698409, 6700601, 6702789, 6704972, 6707150, 6709323, 6711492, 6713656, 6715815, 6717970,
  6720120, 6722265, 6724406, 6726542, 6728674, 6730801, 6732924, 6735042, 6737156, 6739265, 6741370, 6743470, 6745566, 6747658, 6749745, 6751828,
  6753907, 6755981, 6758051, 6760117, 6762178, 6764235, 6766288, 6768337, 6770381, 6772421, 6774457, 6776489, 6778517, 6780541, 6782561, 6784577,
  6786589, 6788597, 6790601, 6792601
]
theorem checked4 : certifiedList 400 6569751 values4 = true := by
  have h : certifiedListFast 400 6569751 values4 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block4 (i : ℕ) (hlo : 400 < i) (hhi : i ≤ 500) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values4.length = 100 := by decide +kernel
  have hh : 6569751 = lowerHarmonicInt 400 := by decide +kernel
  have h := certifiedList_sound values4 400 6569751 checked4 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values5 : List ℕ := [
  6794597, 6796589, 6798577, 6800561, 6802541, 6804517, 6806489, 6808457, 6810421, 6812381, 6814337, 6816290, 6818239, 6820184, 6822125, 6824062,
  6825996, 6827926, 6829852, 6831775, 6833694, 6835609, 6837521, 6839429, 6841333, 6843234, 6845131, 6847024, 6848914, 6850800, 6852683, 6854562,
  6856438, 6858310, 6860179, 6862044, 6863906, 6865764, 6867619, 6869470, 6871318, 6873163, 6875004, 6876842, 6878676, 6880507, 6882335, 6884159,
  6885980, 6887798, 6889612, 6891423, 6893231, 6895036, 6896837, 6898635, 6900430, 6902222, 6904010, 6905795, 6907577, 6909356, 6911132, 6912905,
  6914674, 6916440, 6918203, 6919963, 6921720, 6923474, 6925225, 6926973, 6928718, 6930460, 6932199, 6933935, 6935668, 6937398, 6939125, 6940849,
  6942570, 6944288, 6946003, 6947715, 6949424, 6951130, 6952833, 6954533, 6956230, 6957924, 6959616, 6961305, 6962991, 6964674, 6966354, 6968031,
  6969706, 6971378, 6973047, 6974713
]
theorem checked5 : certifiedList 500 6792601 values5 = true := by
  have h : certifiedListFast 500 6792601 values5 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block5 (i : ℕ) (hlo : 500 < i) (hhi : i ≤ 600) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values5.length = 100 := by decide +kernel
  have hh : 6792601 = lowerHarmonicInt 500 := by decide +kernel
  have h := certifiedList_sound values5 500 6792601 checked5 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values6 : List ℕ := [
  6976376, 6978037, 6979695, 6981350, 6983002, 6984652, 6986299, 6987943, 6989585, 6991224, 6992860, 6994493, 6996124, 6997752, 6999378, 7001001,
  7002621, 7004239, 7005854, 7007466, 7009076, 7010683, 7012288, 7013890, 7015490, 7017087, 7018681, 7020273, 7021862, 7023449, 7025033, 7026615,
  7028194, 7029771, 7031345, 7032917, 7034486, 7036053, 7037617, 7039179, 7040739, 7042296, 7043851, 7045403, 7046953, 7048500, 7050045, 7051588,
  7053128, 7054666, 7056202, 7057735, 7059266, 7060795, 7062321, 7063845, 7065367, 7066886, 7068403, 7069918, 7071430, 7072940, 7074448, 7075954,
  7077457, 7078958, 7080457, 7081954, 7083448, 7084940, 7086430, 7087918, 7089403, 7090886, 7092367, 7093846, 7095323, 7096797, 7098269, 7099739,
  7101207, 7102673, 7104137, 7105598, 7107057, 7108514, 7109969, 7111422, 7112873, 7114322, 7115769, 7117214, 7118657, 7120097, 7121535, 7122971,
  7124405, 7125837, 7127267, 7128695
]
theorem checked6 : certifiedList 600 6974713 values6 = true := by
  have h : certifiedListFast 600 6974713 values6 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block6 (i : ℕ) (hlo : 600 < i) (hhi : i ≤ 700) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values6.length = 100 := by decide +kernel
  have hh : 6974713 = lowerHarmonicInt 600 := by decide +kernel
  have h := certifiedList_sound values6 600 6974713 checked6 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values7 : List ℕ := [
  7130121, 7131545, 7132967, 7134387, 7135805, 7137221, 7138635, 7140047, 7141457, 7142865, 7144271, 7145675, 7147077, 7148477, 7149875, 7151271,
  7152665, 7154057, 7155447, 7156835, 7158221, 7159606, 7160989, 7162370, 7163749, 7165126, 7166501, 7167874, 7169245, 7170614, 7171981, 7173347,
  7174711, 7176073, 7177433, 7178791, 7180147, 7181502, 7182855, 7184206, 7185555, 7186902, 7188247, 7189591, 7190933, 7192273, 7193611, 7194947,
  7196282, 7197615, 7198946, 7200275, 7201603, 7202929, 7204253, 7205575, 7206896, 7208215, 7209532, 7210847, 7212161, 7213473, 7214783, 7216091,
  7217398, 7218703, 7220006, 7221308, 7222608, 7223906, 7225203, 7226498, 7227791, 7229082, 7230372, 7231660, 7232947, 7234232, 7235515, 7236797,
  7238077, 7239355, 7240632, 7241907, 7243180, 7244452, 7245722, 7246991, 7248258, 7249523, 7250787, 7252049, 7253310, 7254569, 7255826, 7257082,
  7258336, 7259589, 7260840, 7262090
]
theorem checked7 : certifiedList 700 7128695 values7 = true := by
  have h : certifiedListFast 700 7128695 values7 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block7 (i : ℕ) (hlo : 700 < i) (hhi : i ≤ 800) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values7.length = 100 := by decide +kernel
  have hh : 7128695 = lowerHarmonicInt 700 := by decide +kernel
  have h := certifiedList_sound values7 700 7128695 checked7 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values8 : List ℕ := [
  7263338, 7264584, 7265829, 7267072, 7268314, 7269554, 7270793, 7272030, 7273266, 7274500, 7275733, 7276964, 7278194, 7279422, 7280648, 7281873,
  7283096, 7284318, 7285539, 7286758, 7287976, 7289192, 7290407, 7291620, 7292832, 7294042, 7295251, 7296458, 7297664, 7298868, 7300071, 7301272,
  7302472, 7303671, 7304868, 7306064, 7307258, 7308451, 7309642, 7310832, 7312021, 7313208, 7314394, 7315578, 7316761, 7317943, 7319123, 7320302,
  7321479, 7322655, 7323830, 7325003, 7326175, 7327345, 7328514, 7329682, 7330848, 7332013, 7333177, 7334339, 7335500, 7336660, 7337818, 7338975,
  7340131, 7341285, 7342438, 7343590, 7344740, 7345889, 7347037, 7348183, 7349328, 7350472, 7351614, 7352755, 7353895, 7355033, 7356170, 7357306,
  7358441, 7359574, 7360706, 7361837, 7362966, 7364094, 7365221, 7366347, 7367471, 7368594, 7369716, 7370837, 7371956, 7373074, 7374191, 7375307,
  7376421, 7377534, 7378646, 7379757
]
theorem checked8 : certifiedList 800 7262090 values8 = true := by
  have h : certifiedListFast 800 7262090 values8 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block8 (i : ℕ) (hlo : 800 < i) (hhi : i ≤ 900) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values8.length = 100 := by decide +kernel
  have hh : 7262090 = lowerHarmonicInt 800 := by decide +kernel
  have h := certifiedList_sound values8 800 7262090 checked8 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values9 : List ℕ := [
  7380866, 7381974, 7383081, 7384187, 7385291, 7386394, 7387496, 7388597, 7389697, 7390795, 7391892, 7392988, 7394083, 7395177, 7396269, 7397360,
  7398450, 7399539, 7400627, 7401713, 7402798, 7403882, 7404965, 7406047, 7407128, 7408207, 7409285, 7410362, 7411438, 7412513, 7413587, 7414659,
  7415730, 7416800, 7417869, 7418937, 7420004, 7421070, 7422134, 7423197, 7424259, 7425320, 7426380, 7427439, 7428497, 7429554, 7430609, 7431663,
  7432716, 7433768, 7434819, 7435869, 7436918, 7437966, 7439013, 7440059, 7441103, 7442146, 7443188, 7444229, 7445269, 7446308, 7447346, 7448383,
  7449419, 7450454, 7451488, 7452521, 7453552, 7454582, 7455611, 7456639, 7457666, 7458692, 7459717, 7460741, 7461764, 7462786, 7463807, 7464827,
  7465846, 7466864, 7467881, 7468897, 7469912, 7470926, 7471939, 7472951, 7473962, 7474972, 7475981, 7476989, 7477996, 7479002, 7480007, 7481011,
  7482014, 7483016, 7484017, 7485017
]
theorem checked9 : certifiedList 900 7379757 values9 = true := by
  have h : certifiedListFast 900 7379757 values9 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block9 (i : ℕ) (hlo : 900 < i) (hhi : i ≤ 1000) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values9.length = 100 := by decide +kernel
  have hh : 7379757 = lowerHarmonicInt 900 := by decide +kernel
  have h := certifiedList_sound values9 900 7379757 checked9 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values10 : List ℕ := [
  7486016, 7487014, 7488011, 7489007, 7490002, 7490996, 7491989, 7492981, 7493972, 7494962, 7495951, 7496939, 7497926, 7498912, 7499897, 7500881,
  7501864, 7502846, 7503827, 7504807, 7505786, 7506764, 7507741, 7508717, 7509692, 7510666, 7511639, 7512611, 7513582, 7514552, 7515521, 7516489,
  7517457, 7518424, 7519390, 7520355, 7521319, 7522282, 7523244, 7524205, 7525165, 7526124, 7527082, 7528039, 7528995, 7529951, 7530906, 7531860,
  7532813, 7533765, 7534716, 7535666, 7536615, 7537563, 7538510, 7539456, 7540402, 7541347, 7542291, 7543234, 7544176, 7545117, 7546057, 7546996,
  7547934, 7548872, 7549809, 7550745, 7551680, 7552614, 7553547, 7554479, 7555410, 7556341, 7557271, 7558200, 7559128, 7560055, 7560981, 7561906,
  7562831, 7563755, 7564678, 7565600, 7566521, 7567441, 7568360, 7569279, 7570197, 7571114, 7572030, 7572945, 7573859, 7574773, 7575686, 7576598,
  7577509, 7578419, 7579328, 7580237
]
theorem checked10 : certifiedList 1000 7485017 values10 = true := by
  have h : certifiedListFast 1000 7485017 values10 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block10 (i : ℕ) (hlo : 1000 < i) (hhi : i ≤ 1100) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values10.length = 100 := by decide +kernel
  have hh : 7485017 = lowerHarmonicInt 1000 := by decide +kernel
  have h := certifiedList_sound values10 1000 7485017 checked10 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values11 : List ℕ := [
  7581145, 7582052, 7582958, 7583863, 7584767, 7585671, 7586574, 7587476, 7588377, 7589277, 7590177, 7591076, 7591974, 7592871, 7593767, 7594663,
  7595558, 7596452, 7597345, 7598237, 7599129, 7600020, 7600910, 7601799, 7602687, 7603575, 7604462, 7605348, 7606233, 7607117, 7608001, 7608884,
  7609766, 7610647, 7611528, 7612408, 7613287, 7614165, 7615042, 7615919, 7616795, 7617670, 7618544, 7619418, 7620291, 7621163, 7622034, 7622905,
  7623775, 7624644, 7625512, 7626380, 7627247, 7628113, 7628978, 7629843, 7630707, 7631570, 7632432, 7633294, 7634155, 7635015, 7635874, 7636733,
  7637591, 7638448, 7639304, 7640160, 7641015, 7641869, 7642722, 7643575, 7644427, 7645278, 7646129, 7646979, 7647828, 7648676, 7649524, 7650371,
  7651217, 7652063, 7652908, 7653752, 7654595, 7655438, 7656280, 7657121, 7657962, 7658802, 7659641, 7660479, 7661317, 7662154, 7662990, 7663826,
  7664661, 7665495, 7666329, 7667162
]
theorem checked11 : certifiedList 1100 7580237 values11 = true := by
  have h : certifiedListFast 1100 7580237 values11 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block11 (i : ℕ) (hlo : 1100 < i) (hhi : i ≤ 1200) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values11.length = 100 := by decide +kernel
  have hh : 7580237 = lowerHarmonicInt 1100 := by decide +kernel
  have h := certifiedList_sound values11 1100 7580237 checked11 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values12 : List ℕ := [
  7667994, 7668825, 7669656, 7670486, 7671315, 7672144, 7672972, 7673799, 7674626, 7675452, 7676277, 7677102, 7677926, 7678749, 7679572, 7680394,
  7681215, 7682036, 7682856, 7683675, 7684494, 7685312, 7686129, 7686945, 7687761, 7688576, 7689390, 7690204, 7691017, 7691830, 7692642, 7693453,
  7694264, 7695074, 7695883, 7696692, 7697500, 7698307, 7699114, 7699920, 7700725, 7701530, 7702334, 7703137, 7703940, 7704742, 7705543, 7706344,
  7707144, 7707944, 7708743, 7709541, 7710339, 7711136, 7711932, 7712728, 7713523, 7714317, 7715111, 7715904, 7716697, 7717489, 7718280, 7719071,
  7719861, 7720650, 7721439, 7722227, 7723015, 7723802, 7724588, 7725374, 7726159, 7726943, 7727727, 7728510, 7729293, 7730075, 7730856, 7731637,
  7732417, 7733197, 7733976, 7734754, 7735532, 7736309, 7737086, 7737862, 7738637, 7739412, 7740186, 7740959, 7741732, 7742504, 7743276, 7744047,
  7744818, 7745588, 7746357, 7747126
]
theorem checked12 : certifiedList 1200 7667162 values12 = true := by
  have h : certifiedListFast 1200 7667162 values12 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block12 (i : ℕ) (hlo : 1200 < i) (hhi : i ≤ 1300) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values12.length = 100 := by decide +kernel
  have hh : 7667162 = lowerHarmonicInt 1200 := by decide +kernel
  have h := certifiedList_sound values12 1200 7667162 checked12 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values13 : List ℕ := [
  7747894, 7748662, 7749429, 7750195, 7750961, 7751726, 7752491, 7753255, 7754018, 7754781, 7755543, 7756305, 7757066, 7757827, 7758587, 7759346,
  7760105, 7760863, 7761621, 7762378, 7763135, 7763891, 7764646, 7765401, 7766155, 7766909, 7767662, 7768415, 7769167, 7769918, 7770669, 7771419,
  7772169, 7772918, 7773667, 7774415, 7775162, 7775909, 7776655, 7777401, 7778146, 7778891, 7779635, 7780379, 7781122, 7781864, 7782606, 7783347,
  7784088, 7784828, 7785568, 7786307, 7787046, 7787784, 7788522, 7789259, 7789995, 7790731, 7791466, 7792201, 7792935, 7793669, 7794402, 7795135,
  7795867, 7796599, 7797330, 7798060, 7798790, 7799519, 7800248, 7800976, 7801704, 7802431, 7803158, 7803884, 7804610, 7805335, 7806060, 7806784,
  7807508, 7808231, 7808954, 7809676, 7810398, 7811119, 7811839, 7812559, 7813278, 7813997, 7814715, 7815433, 7816150, 7816867, 7817583, 7818299,
  7819014, 7819729, 7820443, 7821157
]
theorem checked13 : certifiedList 1300 7747126 values13 = true := by
  have h : certifiedListFast 1300 7747126 values13 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block13 (i : ℕ) (hlo : 1300 < i) (hhi : i ≤ 1400) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values13.length = 100 := by decide +kernel
  have hh : 7747126 = lowerHarmonicInt 1300 := by decide +kernel
  have h := certifiedList_sound values13 1300 7747126 checked13 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values14 : List ℕ := [
  7821870, 7822583, 7823295, 7824007, 7824718, 7825429, 7826139, 7826849, 7827558, 7828267, 7828975, 7829683, 7830390, 7831097, 7831803, 7832509,
  7833214, 7833919, 7834623, 7835327, 7836030, 7836733, 7837435, 7838137, 7838838, 7839539, 7840239, 7840939, 7841638, 7842337, 7843035, 7843733,
  7844430, 7845127, 7845823, 7846519, 7847214, 7847909, 7848603, 7849297, 7849990, 7850683, 7851376, 7852068, 7852760, 7853451, 7854142, 7854832,
  7855522, 7856211, 7856900, 7857588, 7858276, 7858963, 7859650, 7860336, 7861022, 7861707, 7862392, 7863076, 7863760, 7864443, 7865126, 7865809,
  7866491, 7867173, 7867854, 7868535, 7869215, 7869895, 7870574, 7871253, 7871931, 7872609, 7873286, 7873963, 7874640, 7875316, 7875992, 7876667,
  7877342, 7878016, 7878690, 7879363, 7880036, 7880708, 7881380, 7882052, 7882723, 7883394, 7884064, 7884734, 7885403, 7886072, 7886740, 7887408,
  7888076, 7888743, 7889410, 7890076
]
theorem checked14 : certifiedList 1400 7821157 values14 = true := by
  have h : certifiedListFast 1400 7821157 values14 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block14 (i : ℕ) (hlo : 1400 < i) (hhi : i ≤ 1500) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values14.length = 100 := by decide +kernel
  have hh : 7821157 = lowerHarmonicInt 1400 := by decide +kernel
  have h := certifiedList_sound values14 1400 7821157 checked14 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values15 : List ℕ := [
  7890742, 7891407, 7892072, 7892736, 7893400, 7894064, 7894727, 7895390, 7896052, 7896714, 7897375, 7898036, 7898696, 7899356, 7900016, 7900675,
  7901334, 7901992, 7902650, 7903307, 7903964, 7904621, 7905277, 7905933, 7906588, 7907243, 7907897, 7908551, 7909205, 7909858, 7910511, 7911163,
  7911815, 7912466, 7913117, 7913768, 7914418, 7915068, 7915717, 7916366, 7917014, 7917662, 7918310, 7918957, 7919604, 7920250, 7920896, 7921541,
  7922186, 7922831, 7923475, 7924119, 7924762, 7925405, 7926048, 7926690, 7927332, 7927973, 7928614, 7929255, 7929895, 7930535, 7931174, 7931813,
  7932451, 7933089, 7933727, 7934364, 7935001, 7935637, 7936273, 7936909, 7937544, 7938179, 7938813, 7939447, 7940081, 7940714, 7941347, 7941979,
  7942611, 7943243, 7943874, 7944505, 7945135, 7945765, 7946395, 7947024, 7947653, 7948281, 7948909, 7949537, 7950164, 7950791, 7951417, 7952043,
  7952669, 7953294, 7953919, 7954544
]
theorem checked15 : certifiedList 1500 7890076 values15 = true := by
  have h : certifiedListFast 1500 7890076 values15 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block15 (i : ℕ) (hlo : 1500 < i) (hhi : i ≤ 1600) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values15.length = 100 := by decide +kernel
  have hh : 7890076 = lowerHarmonicInt 1500 := by decide +kernel
  have h := certifiedList_sound values15 1500 7890076 checked15 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values16 : List ℕ := [
  7955168, 7955792, 7956415, 7957038, 7957661, 7958283, 7958905, 7959526, 7960147, 7960768, 7961388, 7962008, 7962627, 7963246, 7963865, 7964483,
  7965101, 7965719, 7966336, 7966953, 7967569, 7968185, 7968801, 7969416, 7970031, 7970646, 7971260, 7971874, 7972487, 7973100, 7973713, 7974325,
  7974937, 7975548, 7976159, 7976770, 7977380, 7977990, 7978600, 7979209, 7979818, 7980427, 7981035, 7981643, 7982250, 7982857, 7983464, 7984070,
  7984676, 7985282, 7985887, 7986492, 7987096, 7987700, 7988304, 7988907, 7989510, 7990113, 7990715, 7991317, 7991919, 7992520, 7993121, 7993721,
  7994321, 7994921, 7995520, 7996119, 7996718, 7997316, 7997914, 7998512, 7999109, 7999706, 8000303, 8000899, 8001495, 8002090, 8002685, 8003280,
  8003874, 8004468, 8005062, 8005655, 8006248, 8006841, 8007433, 8008025, 8008617, 8009208, 8009799, 8010390, 8010980, 8011570, 8012159, 8012748,
  8013337, 8013925, 8014513, 8015101
]
theorem checked16 : certifiedList 1600 7954544 values16 = true := by
  have h : certifiedListFast 1600 7954544 values16 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block16 (i : ℕ) (hlo : 1600 < i) (hhi : i ≤ 1700) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values16.length = 100 := by decide +kernel
  have hh : 7954544 = lowerHarmonicInt 1600 := by decide +kernel
  have h := certifiedList_sound values16 1600 7954544 checked16 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values17 : List ℕ := [
  8015688, 8016275, 8016862, 8017448, 8018034, 8018620, 8019205, 8019790, 8020375, 8020959, 8021543, 8022127, 8022710, 8023293, 8023876, 8024458,
  8025040, 8025622, 8026203, 8026784, 8027365, 8027945, 8028525, 8029105, 8029684, 8030263, 8030842, 8031420, 8031998, 8032576, 8033153, 8033730,
  8034307, 8034883, 8035459, 8036035, 8036610, 8037185, 8037760, 8038334, 8038908, 8039482, 8040055, 8040628, 8041201, 8041773, 8042345, 8042917,
  8043488, 8044059, 8044630, 8045200, 8045770, 8046340, 8046909, 8047478, 8048047, 8048615, 8049183, 8049751, 8050318, 8050885, 8051452, 8052018,
  8052584, 8053150, 8053715, 8054280, 8054845, 8055409, 8055973, 8056537, 8057101, 8057664, 8058227, 8058790, 8059352, 8059914, 8060476, 8061037,
  8061598, 8062159, 8062719, 8063279, 8063839, 8064398, 8064957, 8065516, 8066074, 8066632, 8067190, 8067748, 8068305, 8068862, 8069419, 8069975,
  8070531, 8071087, 8071642, 8072197
]
theorem checked17 : certifiedList 1700 8015101 values17 = true := by
  have h : certifiedListFast 1700 8015101 values17 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block17 (i : ℕ) (hlo : 1700 < i) (hhi : i ≤ 1800) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values17.length = 100 := by decide +kernel
  have hh : 8015101 = lowerHarmonicInt 1700 := by decide +kernel
  have h := certifiedList_sound values17 1700 8015101 checked17 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values18 : List ℕ := [
  8072752, 8073306, 8073860, 8074414, 8074968, 8075521, 8076074, 8076627, 8077179, 8077731, 8078283, 8078834, 8079385, 8079936, 8080486, 8081036,
  8081586, 8082136, 8082685, 8083234, 8083783, 8084331, 8084879, 8085427, 8085974, 8086521, 8087068, 8087615, 8088161, 8088707, 8089253, 8089798,
  8090343, 8090888, 8091432, 8091976, 8092520, 8093064, 8093607, 8094150, 8094693, 8095235, 8095777, 8096319, 8096861, 8097402, 8097943, 8098484,
  8099024, 8099564, 8100104, 8100643, 8101182, 8101721, 8102260, 8102798, 8103336, 8103874, 8104411, 8104948, 8105485, 8106022, 8106558, 8107094,
  8107630, 8108165, 8108700, 8109235, 8109770, 8110304, 8110838, 8111372, 8111905, 8112438, 8112971, 8113504, 8114036, 8114568, 8115100, 8115631,
  8116162, 8116693, 8117224, 8117754, 8118284, 8118814, 8119343, 8119872, 8120401, 8120930, 8121458, 8121986, 8122514, 8123041, 8123568, 8124095,
  8124622, 8125148, 8125674, 8126200
]
theorem checked18 : certifiedList 1800 8072197 values18 = true := by
  have h : certifiedListFast 1800 8072197 values18 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block18 (i : ℕ) (hlo : 1800 < i) (hhi : i ≤ 1900) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values18.length = 100 := by decide +kernel
  have hh : 8072197 = lowerHarmonicInt 1800 := by decide +kernel
  have h := certifiedList_sound values18 1800 8072197 checked18 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values19 : List ℕ := [
  8126726, 8127251, 8127776, 8128301, 8128825, 8129349, 8129873, 8130397, 8130920, 8131443, 8131966, 8132489, 8133011, 8133533, 8134055, 8134576,
  8135097, 8135618, 8136139, 8136659, 8137179, 8137699, 8138219, 8138738, 8139257, 8139776, 8140294, 8140812, 8141330, 8141848, 8142365, 8142882,
  8143399, 8143916, 8144432, 8144948, 8145464, 8145979, 8146494, 8147009, 8147524, 8148038, 8148552, 8149066, 8149580, 8150093, 8150606, 8151119,
  8151632, 8152144, 8152656, 8153168, 8153680, 8154191, 8154702, 8155213, 8155723, 8156233, 8156743, 8157253, 8157762, 8158271, 8158780, 8159289,
  8159797, 8160305, 8160813, 8161321, 8161828, 8162335, 8162842, 8163349, 8163855, 8164361, 8164867, 8165373, 8165878, 8166383, 8166888, 8167393,
  8167897, 8168401, 8168905, 8169409, 8169912, 8170415, 8170918, 8171421, 8171923, 8172425, 8172927, 8173429, 8173930, 8174431, 8174932, 8175433,
  8175933, 8176433, 8176933, 8177433
]
theorem checked19 : certifiedList 1900 8126200 values19 = true := by
  have h : certifiedListFast 1900 8126200 values19 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block19 (i : ℕ) (hlo : 1900 < i) (hhi : i ≤ 2000) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values19.length = 100 := by decide +kernel
  have hh : 8126200 = lowerHarmonicInt 1900 := by decide +kernel
  have h := certifiedList_sound values19 1900 8126200 checked19 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values20 : List ℕ := [
  8177932, 8178431, 8178930, 8179429, 8179927, 8180425, 8180923, 8181421, 8181918, 8182415, 8182912, 8183409, 8183905, 8184401, 8184897, 8185393,
  8185888, 8186383, 8186878, 8187373, 8187867, 8188361, 8188855, 8189349, 8189842, 8190335, 8190828, 8191321, 8191813, 8192305, 8192797, 8193289,
  8193780, 8194271, 8194762, 8195253, 8195743, 8196233, 8196723, 8197213, 8197702, 8198191, 8198680, 8199169, 8199657, 8200145, 8200633, 8201121,
  8201609, 8202096, 8202583, 8203070, 8203557, 8204043, 8204529, 8205015, 8205501, 8205986, 8206471, 8206956, 8207441, 8207925, 8208409, 8208893,
  8209377, 8209861, 8210344, 8210827, 8211310, 8211793, 8212275, 8212757, 8213239, 8213721, 8214202, 8214683, 8215164, 8215645, 8216126, 8216606,
  8217086, 8217566, 8218046, 8218525, 8219004, 8219483, 8219962, 8220440, 8220918, 8221396, 8221874, 8222352, 8222829, 8223306, 8223783, 8224260,
  8224736, 8225212, 8225688, 8226164
]
theorem checked20 : certifiedList 2000 8177433 values20 = true := by
  have h : certifiedListFast 2000 8177433 values20 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block20 (i : ℕ) (hlo : 2000 < i) (hhi : i ≤ 2100) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values20.length = 100 := by decide +kernel
  have hh : 8177433 = lowerHarmonicInt 2000 := by decide +kernel
  have h := certifiedList_sound values20 2000 8177433 checked20 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values21 : List ℕ := [
  8226639, 8227114, 8227589, 8228064, 8228539, 8229013, 8229487, 8229961, 8230435, 8230908, 8231381, 8231854, 8232327, 8232800, 8233272, 8233744,
  8234216, 8234688, 8235159, 8235630, 8236101, 8236572, 8237043, 8237513, 8237983, 8238453, 8238923, 8239392, 8239861, 8240330, 8240799, 8241268,
  8241736, 8242204, 8242672, 8243140, 8243607, 8244074, 8244541, 8245008, 8245475, 8245941, 8246407, 8246873, 8247339, 8247804, 8248269, 8248734,
  8249199, 8249664, 8250128, 8250592, 8251056, 8251520, 8251984, 8252447, 8252910, 8253373, 8253836, 8254298, 8254760, 8255222, 8255684, 8256146,
  8256607, 8257068, 8257529, 8257990, 8258451, 8258911, 8259371, 8259831, 8260291, 8260750, 8261209, 8261668, 8262127, 8262586, 8263044, 8263502,
  8263960, 8264418, 8264876, 8265333, 8265790, 8266247, 8266704, 8267161, 8267617, 8268073, 8268529, 8268985, 8269440, 8269895, 8270350, 8270805,
  8271260, 8271714, 8272168, 8272622
]
theorem checked21 : certifiedList 2100 8226164 values21 = true := by
  have h : certifiedListFast 2100 8226164 values21 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block21 (i : ℕ) (hlo : 2100 < i) (hhi : i ≤ 2200) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values21.length = 100 := by decide +kernel
  have hh : 8226164 = lowerHarmonicInt 2100 := by decide +kernel
  have h := certifiedList_sound values21 2100 8226164 checked21 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values22 : List ℕ := [
  8273076, 8273530, 8273983, 8274436, 8274889, 8275342, 8275795, 8276247, 8276699, 8277151, 8277603, 8278055, 8278506, 8278957, 8279408, 8279859,
  8280310, 8280760, 8281210, 8281660, 8282110, 8282560, 8283009, 8283458, 8283907, 8284356, 8284805, 8285253, 8285701, 8286149, 8286597, 8287045,
  8287492, 8287939, 8288386, 8288833, 8289280, 8289726, 8290172, 8290618, 8291064, 8291510, 8291955, 8292400, 8292845, 8293290, 8293735, 8294179,
  8294623, 8295067, 8295511, 8295955, 8296398, 8296841, 8297284, 8297727, 8298170, 8298612, 8299054, 8299496, 8299938, 8300380, 8300821, 8301262,
  8301703, 8302144, 8302585, 8303025, 8303465, 8303905, 8304345, 8304785, 8305224, 8305663, 8306102, 8306541, 8306980, 8307418, 8307856, 8308294,
  8308732, 8309170, 8309608, 8310045, 8310482, 8310919, 8311356, 8311793, 8312229, 8312665, 8313101, 8313537, 8313973, 8314408, 8314843, 8315278,
  8315713, 8316148, 8316582, 8317016
]
theorem checked22 : certifiedList 2200 8272622 values22 = true := by
  have h : certifiedListFast 2200 8272622 values22 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block22 (i : ℕ) (hlo : 2200 < i) (hhi : i ≤ 2300) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values22.length = 100 := by decide +kernel
  have hh : 8272622 = lowerHarmonicInt 2200 := by decide +kernel
  have h := certifiedList_sound values22 2200 8272622 checked22 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values23 : List ℕ := [
  8317450, 8317884, 8318318, 8318752, 8319185, 8319618, 8320051, 8320484, 8320917, 8321349, 8321781, 8322213, 8322645, 8323077, 8323508, 8323939,
  8324370, 8324801, 8325232, 8325663, 8326093, 8326523, 8326953, 8327383, 8327813, 8328242, 8328671, 8329100, 8329529, 8329958, 8330387, 8330815,
  8331243, 8331671, 8332099, 8332527, 8332954, 8333381, 8333808, 8334235, 8334662, 8335088, 8335514, 8335940, 8336366, 8336792, 8337218, 8337643,
  8338068, 8338493, 8338918, 8339343, 8339767, 8340191, 8340615, 8341039, 8341463, 8341887, 8342310, 8342733, 8343156, 8343579, 8344002, 8344425,
  8344847, 8345269, 8345691, 8346113, 8346535, 8346956, 8347377, 8347798, 8348219, 8348640, 8349061, 8349481, 8349901, 8350321, 8350741, 8351161,
  8351580, 8351999, 8352418, 8352837, 8353256, 8353675, 8354093, 8354511, 8354929, 8355347, 8355765, 8356183, 8356600, 8357017, 8357434, 8357851,
  8358268, 8358685, 8359101, 8359517
]
theorem checked23 : certifiedList 2300 8317016 values23 = true := by
  have h : certifiedListFast 2300 8317016 values23 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block23 (i : ℕ) (hlo : 2300 < i) (hhi : i ≤ 2400) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values23.length = 100 := by decide +kernel
  have hh : 8317016 = lowerHarmonicInt 2300 := by decide +kernel
  have h := certifiedList_sound values23 2300 8317016 checked23 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values24 : List ℕ := [
  8359933, 8360349, 8360765, 8361180, 8361595, 8362010, 8362425, 8362840, 8363255, 8363669, 8364083, 8364497, 8364911, 8365325, 8365739, 8366152,
  8366565, 8366978, 8367391, 8367804, 8368217, 8368629, 8369041, 8369453, 8369865, 8370277, 8370689, 8371100, 8371511, 8371922, 8372333, 8372744,
  8373155, 8373565, 8373975, 8374385, 8374795, 8375205, 8375615, 8376024, 8376433, 8376842, 8377251, 8377660, 8378068, 8378476, 8378884, 8379292,
  8379700, 8380108, 8380515, 8380922, 8381329, 8381736, 8382143, 8382550, 8382957, 8383363, 8383769, 8384175, 8384581, 8384987, 8385393, 8385798,
  8386203, 8386608, 8387013, 8387418, 8387823, 8388227, 8388631, 8389035, 8389439, 8389843, 8390247, 8390650, 8391053, 8391456, 8391859, 8392262,
  8392665, 8393067, 8393469, 8393871, 8394273, 8394675, 8395077, 8395478, 8395879, 8396280, 8396681, 8397082, 8397483, 8397883, 8398283, 8398683,
  8399083, 8399483, 8399883, 8400283
]
theorem checked24 : certifiedList 2400 8359517 values24 = true := by
  have h : certifiedListFast 2400 8359517 values24 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block24 (i : ℕ) (hlo : 2400 < i) (hhi : i ≤ 2500) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values24.length = 100 := by decide +kernel
  have hh : 8359517 = lowerHarmonicInt 2400 := by decide +kernel
  have h := certifiedList_sound values24 2400 8359517 checked24 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values25 : List ℕ := [
  8400682, 8401081, 8401480, 8401879, 8402278, 8402677, 8403075, 8403473, 8403871, 8404269, 8404667, 8405065, 8405462, 8405859, 8406256, 8406653,
  8407050, 8407447, 8407843, 8408239, 8408635, 8409031, 8409427, 8409823, 8410219, 8410614, 8411009, 8411404, 8411799, 8412194, 8412589, 8412983,
  8413377, 8413771, 8414165, 8414559, 8414953, 8415347, 8415740, 8416133, 8416526, 8416919, 8417312, 8417705, 8418097, 8418489, 8418881, 8419273,
  8419665, 8420057, 8420449, 8420840, 8421231, 8421622, 8422013, 8422404, 8422795, 8423185, 8423575, 8423965, 8424355, 8424745, 8425135, 8425525,
  8425914, 8426303, 8426692, 8427081, 8427470, 8427859, 8428247, 8428635, 8429023, 8429411, 8429799, 8430187, 8430575, 8430962, 8431349, 8431736,
  8432123, 8432510, 8432897, 8433283, 8433669, 8434055, 8434441, 8434827, 8435213, 8435599, 8435984, 8436369, 8436754, 8437139, 8437524, 8437909,
  8438294, 8438678, 8439062, 8439446
]
theorem checked25 : certifiedList 2500 8400283 values25 = true := by
  have h : certifiedListFast 2500 8400283 values25 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block25 (i : ℕ) (hlo : 2500 < i) (hhi : i ≤ 2600) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values25.length = 100 := by decide +kernel
  have hh : 8400283 = lowerHarmonicInt 2500 := by decide +kernel
  have h := certifiedList_sound values25 2500 8400283 checked25 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values26 : List ℕ := [
  8439830, 8440214, 8440598, 8440982, 8441365, 8441748, 8442131, 8442514, 8442897, 8443280, 8443662, 8444044, 8444426, 8444808, 8445190, 8445572,
  8445954, 8446335, 8446716, 8447097, 8447478, 8447859, 8448240, 8448621, 8449001, 8449381, 8449761, 8450141, 8450521, 8450901, 8451281, 8451660,
  8452039, 8452418, 8452797, 8453176, 8453555, 8453934, 8454312, 8454690, 8455068, 8455446, 8455824, 8456202, 8456580, 8456957, 8457334, 8457711,
  8458088, 8458465, 8458842, 8459219, 8459595, 8459971, 8460347, 8460723, 8461099, 8461475, 8461851, 8462226, 8462601, 8462976, 8463351, 8463726,
  8464101, 8464476, 8464850, 8465224, 8465598, 8465972, 8466346, 8466720, 8467094, 8467467, 8467840, 8468213, 8468586, 8468959, 8469332, 8469705,
  8470077, 8470449, 8470821, 8471193, 8471565, 8471937, 8472309, 8472681, 8473052, 8473423, 8473794, 8474165, 8474536, 8474907, 8475278, 8475648,
  8476018, 8476388, 8476758, 8477128
]
theorem checked26 : certifiedList 2600 8439446 values26 = true := by
  have h : certifiedListFast 2600 8439446 values26 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block26 (i : ℕ) (hlo : 2600 < i) (hhi : i ≤ 2700) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values26.length = 100 := by decide +kernel
  have hh : 8439446 = lowerHarmonicInt 2600 := by decide +kernel
  have h := certifiedList_sound values26 2600 8439446 checked26 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values27 : List ℕ := [
  8477498, 8477868, 8478237, 8478606, 8478975, 8479344, 8479713, 8480082, 8480451, 8480820, 8481188, 8481556, 8481924, 8482292, 8482660, 8483028,
  8483396, 8483763, 8484130, 8484497, 8484864, 8485231, 8485598, 8485965, 8486331, 8486697, 8487063, 8487429, 8487795, 8488161, 8488527, 8488893,
  8489258, 8489623, 8489988, 8490353, 8490718, 8491083, 8491448, 8491812, 8492176, 8492540, 8492904, 8493268, 8493632, 8493996, 8494360, 8494723,
  8495086, 8495449, 8495812, 8496175, 8496538, 8496901, 8497263, 8497625, 8497987, 8498349, 8498711, 8499073, 8499435, 8499797, 8500158, 8500519,
  8500880, 8501241, 8501602, 8501963, 8502324, 8502685, 8503045, 8503405, 8503765, 8504125, 8504485, 8504845, 8505205, 8505564, 8505923, 8506282,
  8506641, 8507000, 8507359, 8507718, 8508077, 8508435, 8508793, 8509151, 8509509, 8509867, 8510225, 8510583, 8510941, 8511298, 8511655, 8512012,
  8512369, 8512726, 8513083, 8513440
]
theorem checked27 : certifiedList 2700 8477128 values27 = true := by
  have h : certifiedListFast 2700 8477128 values27 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block27 (i : ℕ) (hlo : 2700 < i) (hhi : i ≤ 2800) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values27.length = 100 := by decide +kernel
  have hh : 8477128 = lowerHarmonicInt 2700 := by decide +kernel
  have h := certifiedList_sound values27 2700 8477128 checked27 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values28 : List ℕ := [
  8513797, 8514153, 8514509, 8514865, 8515221, 8515577, 8515933, 8516289, 8516644, 8516999, 8517354, 8517709, 8518064, 8518419, 8518774, 8519129,
  8519483, 8519837, 8520191, 8520545, 8520899, 8521253, 8521607, 8521961, 8522314, 8522667, 8523020, 8523373, 8523726, 8524079, 8524432, 8524785,
  8525137, 8525489, 8525841, 8526193, 8526545, 8526897, 8527249, 8527601, 8527952, 8528303, 8528654, 8529005, 8529356, 8529707, 8530058, 8530409,
  8530760, 8531110, 8531460, 8531810, 8532160, 8532510, 8532860, 8533210, 8533560, 8533909, 8534258, 8534607, 8534956, 8535305, 8535654, 8536003,
  8536352, 8536700, 8537048, 8537396, 8537744, 8538092, 8538440, 8538788, 8539136, 8539483, 8539830, 8540177, 8540524, 8540871, 8541218, 8541565,
  8541912, 8542258, 8542604, 8542950, 8543296, 8543642, 8543988, 8544334, 8544680, 8545026, 8545371, 8545716, 8546061, 8546406, 8546751, 8547096,
  8547441, 8547786, 8548130, 8548474
]
theorem checked28 : certifiedList 2800 8513440 values28 = true := by
  have h : certifiedListFast 2800 8513440 values28 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block28 (i : ℕ) (hlo : 2800 < i) (hhi : i ≤ 2900) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values28.length = 100 := by decide +kernel
  have hh : 8513440 = lowerHarmonicInt 2800 := by decide +kernel
  have h := certifiedList_sound values28 2800 8513440 checked28 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values29 : List ℕ := [
  8548818, 8549162, 8549506, 8549850, 8550194, 8550538, 8550881, 8551224, 8551567, 8551910, 8552253, 8552596, 8552939, 8553282, 8553625, 8553967,
  8554309, 8554651, 8554993, 8555335, 8555677, 8556019, 8556361, 8556702, 8557043, 8557384, 8557725, 8558066, 8558407, 8558748, 8559089, 8559430,
  8559770, 8560110, 8560450, 8560790, 8561130, 8561470, 8561810, 8562150, 8562490, 8562829, 8563168, 8563507, 8563846, 8564185, 8564524, 8564863,
  8565202, 8565540, 8565878, 8566216, 8566554, 8566892, 8567230, 8567568, 8567906, 8568244, 8568581, 8568918, 8569255, 8569592, 8569929, 8570266,
  8570603, 8570940, 8571277, 8571613, 8571949, 8572285, 8572621, 8572957, 8573293, 8573629, 8573965, 8574301, 8574636, 8574971, 8575306, 8575641,
  8575976, 8576311, 8576646, 8576981, 8577316, 8577650, 8577984, 8578318, 8578652, 8578986, 8579320, 8579654, 8579988, 8580322, 8580655, 8580988,
  8581321, 8581654, 8581987, 8582320
]
theorem checked29 : certifiedList 2900 8548474 values29 = true := by
  have h : certifiedListFast 2900 8548474 values29 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block29 (i : ℕ) (hlo : 2900 < i) (hhi : i ≤ 3000) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values29.length = 100 := by decide +kernel
  have hh : 8548474 = lowerHarmonicInt 2900 := by decide +kernel
  have h := certifiedList_sound values29 2900 8548474 checked29 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values30 : List ℕ := [
  8582653, 8582986, 8583319, 8583651, 8583983, 8584315, 8584647, 8584979, 8585311, 8585643, 8585975, 8586307, 8586638, 8586969, 8587300, 8587631,
  8587962, 8588293, 8588624, 8588955, 8589286, 8589616, 8589946, 8590276, 8590606, 8590936, 8591266, 8591596, 8591926, 8592256, 8592585, 8592914,
  8593243, 8593572, 8593901, 8594230, 8594559, 8594888, 8595217, 8595545, 8595873, 8596201, 8596529, 8596857, 8597185, 8597513, 8597841, 8598169,
  8598496, 8598823, 8599150, 8599477, 8599804, 8600131, 8600458, 8600785, 8601112, 8601439, 8601765, 8602091, 8602417, 8602743, 8603069, 8603395,
  8603721, 8604047, 8604373, 8604698, 8605023, 8605348, 8605673, 8605998, 8606323, 8606648, 8606973, 8607298, 8607622, 8607946, 8608270, 8608594,
  8608918, 8609242, 8609566, 8609890, 8610214, 8610538, 8610861, 8611184, 8611507, 8611830, 8612153, 8612476, 8612799, 8613122, 8613445, 8613767,
  8614089, 8614411, 8614733, 8615055
]
theorem checked30 : certifiedList 3000 8582320 values30 = true := by
  have h : certifiedListFast 3000 8582320 values30 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block30 (i : ℕ) (hlo : 3000 < i) (hhi : i ≤ 3100) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values30.length = 100 := by decide +kernel
  have hh : 8582320 = lowerHarmonicInt 3000 := by decide +kernel
  have h := certifiedList_sound values30 3000 8582320 checked30 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values31 : List ℕ := [
  8615377, 8615699, 8616021, 8616343, 8616665, 8616986, 8617307, 8617628, 8617949, 8618270, 8618591, 8618912, 8619233, 8619554, 8619875, 8620195,
  8620515, 8620835, 8621155, 8621475, 8621795, 8622115, 8622435, 8622755, 8623075, 8623394, 8623713, 8624032, 8624351, 8624670, 8624989, 8625308,
  8625627, 8625946, 8626264, 8626582, 8626900, 8627218, 8627536, 8627854, 8628172, 8628490, 8628808, 8629126, 8629443, 8629760, 8630077, 8630394,
  8630711, 8631028, 8631345, 8631662, 8631979, 8632296, 8632612, 8632928, 8633244, 8633560, 8633876, 8634192, 8634508, 8634824, 8635140, 8635456,
  8635771, 8636086, 8636401, 8636716, 8637031, 8637346, 8637661, 8637976, 8638291, 8638606, 8638920, 8639234, 8639548, 8639862, 8640176, 8640490,
  8640804, 8641118, 8641432, 8641746, 8642059, 8642372, 8642685, 8642998, 8643311, 8643624, 8643937, 8644250, 8644563, 8644876, 8645188, 8645500,
  8645812, 8646124, 8646436, 8646748
]
theorem checked31 : certifiedList 3100 8615055 values31 = true := by
  have h : certifiedListFast 3100 8615055 values31 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block31 (i : ℕ) (hlo : 3100 < i) (hhi : i ≤ 3200) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values31.length = 100 := by decide +kernel
  have hh : 8615055 = lowerHarmonicInt 3100 := by decide +kernel
  have h := certifiedList_sound values31 3100 8615055 checked31 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values32 : List ℕ := [
  8647060, 8647372, 8647684, 8647996, 8648308, 8648619, 8648930, 8649241, 8649552, 8649863, 8650174, 8650485, 8650796, 8651107, 8651418, 8651728,
  8652038, 8652348, 8652658, 8652968, 8653278, 8653588, 8653898, 8654208, 8654518, 8654827, 8655136, 8655445, 8655754, 8656063, 8656372, 8656681,
  8656990, 8657299, 8657608, 8657917, 8658225, 8658533, 8658841, 8659149, 8659457, 8659765, 8660073, 8660381, 8660689, 8660997, 8661304, 8661611,
  8661918, 8662225, 8662532, 8662839, 8663146, 8663453, 8663760, 8664067, 8664374, 8664680, 8664986, 8665292, 8665598, 8665904, 8666210, 8666516,
  8666822, 8667128, 8667434, 8667739, 8668044, 8668349, 8668654, 8668959, 8669264, 8669569, 8669874, 8670179, 8670484, 8670789, 8671093, 8671397,
  8671701, 8672005, 8672309, 8672613, 8672917, 8673221, 8673525, 8673829, 8674133, 8674436, 8674739, 8675042, 8675345, 8675648, 8675951, 8676254,
  8676557, 8676860, 8677163, 8677466
]
theorem checked32 : certifiedList 3200 8646748 values32 = true := by
  have h : certifiedListFast 3200 8646748 values32 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block32 (i : ℕ) (hlo : 3200 < i) (hhi : i ≤ 3300) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values32.length = 100 := by decide +kernel
  have hh : 8646748 = lowerHarmonicInt 3200 := by decide +kernel
  have h := certifiedList_sound values32 3200 8646748 checked32 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values33 : List ℕ := [
  8677768, 8678070, 8678372, 8678674, 8678976, 8679278, 8679580, 8679882, 8680184, 8680486, 8680788, 8681089, 8681390, 8681691, 8681992, 8682293,
  8682594, 8682895, 8683196, 8683497, 8683798, 8684099, 8684399, 8684699, 8684999, 8685299, 8685599, 8685899, 8686199, 8686499, 8686799, 8687099,
  8687399, 8687698, 8687997, 8688296, 8688595, 8688894, 8689193, 8689492, 8689791, 8690090, 8690389, 8690688, 8690986, 8691284, 8691582, 8691880,
  8692178, 8692476, 8692774, 8693072, 8693370, 8693668, 8693966, 8694263, 8694560, 8694857, 8695154, 8695451, 8695748, 8696045, 8696342, 8696639,
  8696936, 8697233, 8697530, 8697826, 8698122, 8698418, 8698714, 8699010, 8699306, 8699602, 8699898, 8700194, 8700490, 8700786, 8701081, 8701376,
  8701671, 8701966, 8702261, 8702556, 8702851, 8703146, 8703441, 8703736, 8704031, 8704325, 8704619, 8704913, 8705207, 8705501, 8705795, 8706089,
  8706383, 8706677, 8706971, 8707265
]
theorem checked33 : certifiedList 3300 8677466 values33 = true := by
  have h : certifiedListFast 3300 8677466 values33 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block33 (i : ℕ) (hlo : 3300 < i) (hhi : i ≤ 3400) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values33.length = 100 := by decide +kernel
  have hh : 8677466 = lowerHarmonicInt 3300 := by decide +kernel
  have h := certifiedList_sound values33 3300 8677466 checked33 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values34 : List ℕ := [
  8707559, 8707852, 8708145, 8708438, 8708731, 8709024, 8709317, 8709610, 8709903, 8710196, 8710489, 8710782, 8711074, 8711366, 8711658, 8711950,
  8712242, 8712534, 8712826, 8713118, 8713410, 8713702, 8713994, 8714286, 8714577, 8714868, 8715159, 8715450, 8715741, 8716032, 8716323, 8716614,
  8716905, 8717196, 8717487, 8717778, 8718068, 8718358, 8718648, 8718938, 8719228, 8719518, 8719808, 8720098, 8720388, 8720678, 8720968, 8721258,
  8721547, 8721836, 8722125, 8722414, 8722703, 8722992, 8723281, 8723570, 8723859, 8724148, 8724437, 8724726, 8725014, 8725302, 8725590, 8725878,
  8726166, 8726454, 8726742, 8727030, 8727318, 8727606, 8727894, 8728182, 8728469, 8728756, 8729043, 8729330, 8729617, 8729904, 8730191, 8730478,
  8730765, 8731052, 8731339, 8731626, 8731912, 8732198, 8732484, 8732770, 8733056, 8733342, 8733628, 8733914, 8734200, 8734486, 8734772, 8735058,
  8735343, 8735628, 8735913, 8736198
]
theorem checked34 : certifiedList 3400 8707265 values34 = true := by
  have h : certifiedListFast 3400 8707265 values34 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block34 (i : ℕ) (hlo : 3400 < i) (hhi : i ≤ 3500) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values34.length = 100 := by decide +kernel
  have hh : 8707265 = lowerHarmonicInt 3400 := by decide +kernel
  have h := certifiedList_sound values34 3400 8707265 checked34 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values35 : List ℕ := [
  8736483, 8736768, 8737053, 8737338, 8737623, 8737908, 8738193, 8738478, 8738762, 8739046, 8739330, 8739614, 8739898, 8740182, 8740466, 8740750,
  8741034, 8741318, 8741602, 8741886, 8742170, 8742453, 8742736, 8743019, 8743302, 8743585, 8743868, 8744151, 8744434, 8744717, 8745000, 8745283,
  8745566, 8745848, 8746130, 8746412, 8746694, 8746976, 8747258, 8747540, 8747822, 8748104, 8748386, 8748668, 8748950, 8749232, 8749513, 8749794,
  8750075, 8750356, 8750637, 8750918, 8751199, 8751480, 8751761, 8752042, 8752323, 8752604, 8752884, 8753164, 8753444, 8753724, 8754004, 8754284,
  8754564, 8754844, 8755124, 8755404, 8755684, 8755964, 8756244, 8756523, 8756802, 8757081, 8757360, 8757639, 8757918, 8758197, 8758476, 8758755,
  8759034, 8759313, 8759592, 8759871, 8760149, 8760427, 8760705, 8760983, 8761261, 8761539, 8761817, 8762095, 8762373, 8762651, 8762929, 8763207,
  8763485, 8763762, 8764039, 8764316
]
theorem checked35 : certifiedList 3500 8736198 values35 = true := by
  have h : certifiedListFast 3500 8736198 values35 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block35 (i : ℕ) (hlo : 3500 < i) (hhi : i ≤ 3600) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values35.length = 100 := by decide +kernel
  have hh : 8736198 = lowerHarmonicInt 3500 := by decide +kernel
  have h := certifiedList_sound values35 3500 8736198 checked35 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values36 : List ℕ := [
  8764593, 8764870, 8765147, 8765424, 8765701, 8765978, 8766255, 8766532, 8766809, 8767086, 8767362, 8767638, 8767914, 8768190, 8768466, 8768742,
  8769018, 8769294, 8769570, 8769846, 8770122, 8770398, 8770674, 8770949, 8771224, 8771499, 8771774, 8772049, 8772324, 8772599, 8772874, 8773149,
  8773424, 8773699, 8773974, 8774249, 8774523, 8774797, 8775071, 8775345, 8775619, 8775893, 8776167, 8776441, 8776715, 8776989, 8777263, 8777537,
  8777811, 8778084, 8778357, 8778630, 8778903, 8779176, 8779449, 8779722, 8779995, 8780268, 8780541, 8780814, 8781087, 8781360, 8781633, 8781905,
  8782177, 8782449, 8782721, 8782993, 8783265, 8783537, 8783809, 8784081, 8784353, 8784625, 8784897, 8785169, 8785440, 8785711, 8785982, 8786253,
  8786524, 8786795, 8787066, 8787337, 8787608, 8787879, 8788150, 8788421, 8788692, 8788963, 8789233, 8789503, 8789773, 8790043, 8790313, 8790583,
  8790853, 8791123, 8791393, 8791663
]
theorem checked36 : certifiedList 3600 8764316 values36 = true := by
  have h : certifiedListFast 3600 8764316 values36 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block36 (i : ℕ) (hlo : 3600 < i) (hhi : i ≤ 3700) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values36.length = 100 := by decide +kernel
  have hh : 8764316 = lowerHarmonicInt 3600 := by decide +kernel
  have h := certifiedList_sound values36 3600 8764316 checked36 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values37 : List ℕ := [
  8791933, 8792203, 8792473, 8792742, 8793011, 8793280, 8793549, 8793818, 8794087, 8794356, 8794625, 8794894, 8795163, 8795432, 8795701, 8795970,
  8796239, 8796507, 8796775, 8797043, 8797311, 8797579, 8797847, 8798115, 8798383, 8798651, 8798919, 8799187, 8799455, 8799723, 8799991, 8800258,
  8800525, 8800792, 8801059, 8801326, 8801593, 8801860, 8802127, 8802394, 8802661, 8802928, 8803195, 8803462, 8803729, 8803995, 8804261, 8804527,
  8804793, 8805059, 8805325, 8805591, 8805857, 8806123, 8806389, 8806655, 8806921, 8807187, 8807453, 8807718, 8807983, 8808248, 8808513, 8808778,
  8809043, 8809308, 8809573, 8809838, 8810103, 8810368, 8810633, 8810898, 8811163, 8811427, 8811691, 8811955, 8812219, 8812483, 8812747, 8813011,
  8813275, 8813539, 8813803, 8814067, 8814331, 8814595, 8814859, 8815122, 8815385, 8815648, 8815911, 8816174, 8816437, 8816700, 8816963, 8817226,
  8817489, 8817752, 8818015, 8818278
]
theorem checked37 : certifiedList 3700 8791663 values37 = true := by
  have h : certifiedListFast 3700 8791663 values37 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block37 (i : ℕ) (hlo : 3700 < i) (hhi : i ≤ 3800) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values37.length = 100 := by decide +kernel
  have hh : 8791663 = lowerHarmonicInt 3700 := by decide +kernel
  have h := certifiedList_sound values37 3700 8791663 checked37 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values38 : List ℕ := [
  8818541, 8818804, 8819066, 8819328, 8819590, 8819852, 8820114, 8820376, 8820638, 8820900, 8821162, 8821424, 8821686, 8821948, 8822210, 8822472,
  8822733, 8822994, 8823255, 8823516, 8823777, 8824038, 8824299, 8824560, 8824821, 8825082, 8825343, 8825604, 8825865, 8826126, 8826387, 8826647,
  8826907, 8827167, 8827427, 8827687, 8827947, 8828207, 8828467, 8828727, 8828987, 8829247, 8829507, 8829767, 8830027, 8830287, 8830546, 8830805,
  8831064, 8831323, 8831582, 8831841, 8832100, 8832359, 8832618, 8832877, 8833136, 8833395, 8833654, 8833913, 8834172, 8834430, 8834688, 8834946,
  8835204, 8835462, 8835720, 8835978, 8836236, 8836494, 8836752, 8837010, 8837268, 8837526, 8837784, 8838041, 8838298, 8838555, 8838812, 8839069,
  8839326, 8839583, 8839840, 8840097, 8840354, 8840611, 8840868, 8841125, 8841382, 8841639, 8841896, 8842152, 8842408, 8842664, 8842920, 8843176,
  8843432, 8843688, 8843944, 8844200
]
theorem checked38 : certifiedList 3800 8818278 values38 = true := by
  have h : certifiedListFast 3800 8818278 values38 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block38 (i : ℕ) (hlo : 3800 < i) (hhi : i ≤ 3900) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values38.length = 100 := by decide +kernel
  have hh : 8818278 = lowerHarmonicInt 3800 := by decide +kernel
  have h := certifiedList_sound values38 3800 8818278 checked38 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values39 : List ℕ := [
  8844456, 8844712, 8844968, 8845224, 8845480, 8845736, 8845991, 8846246, 8846501, 8846756, 8847011, 8847266, 8847521, 8847776, 8848031, 8848286,
  8848541, 8848796, 8849051, 8849306, 8849561, 8849815, 8850069, 8850323, 8850577, 8850831, 8851085, 8851339, 8851593, 8851847, 8852101, 8852355,
  8852609, 8852863, 8853117, 8853371, 8853625, 8853878, 8854131, 8854384, 8854637, 8854890, 8855143, 8855396, 8855649, 8855902, 8856155, 8856408,
  8856661, 8856914, 8857167, 8857420, 8857672, 8857924, 8858176, 8858428, 8858680, 8858932, 8859184, 8859436, 8859688, 8859940, 8860192, 8860444,
  8860696, 8860948, 8861200, 8861452, 8861703, 8861954, 8862205, 8862456, 8862707, 8862958, 8863209, 8863460, 8863711, 8863962, 8864213, 8864464,
  8864715, 8864966, 8865217, 8865468, 8865718, 8865968, 8866218, 8866468, 8866718, 8866968, 8867218, 8867468, 8867718, 8867968, 8868218, 8868468,
  8868718, 8868968, 8869218, 8869468
]
theorem checked39 : certifiedList 3900 8844200 values39 = true := by
  have h : certifiedListFast 3900 8844200 values39 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block39 (i : ℕ) (hlo : 3900 < i) (hhi : i ≤ 4000) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values39.length = 100 := by decide +kernel
  have hh : 8844200 = lowerHarmonicInt 3900 := by decide +kernel
  have h := certifiedList_sound values39 3900 8844200 checked39 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values40 : List ℕ := [
  8869717, 8869966, 8870215, 8870464, 8870713, 8870962, 8871211, 8871460, 8871709, 8871958, 8872207, 8872456, 8872705, 8872954, 8873203, 8873452,
  8873700, 8873948, 8874196, 8874444, 8874692, 8874940, 8875188, 8875436, 8875684, 8875932, 8876180, 8876428, 8876676, 8876924, 8877172, 8877420,
  8877667, 8877914, 8878161, 8878408, 8878655, 8878902, 8879149, 8879396, 8879643, 8879890, 8880137, 8880384, 8880631, 8880878, 8881125, 8881372,
  8881618, 8881864, 8882110, 8882356, 8882602, 8882848, 8883094, 8883340, 8883586, 8883832, 8884078, 8884324, 8884570, 8884816, 8885062, 8885308,
  8885554, 8885799, 8886044, 8886289, 8886534, 8886779, 8887024, 8887269, 8887514, 8887759, 8888004, 8888249, 8888494, 8888739, 8888984, 8889229,
  8889474, 8889718, 8889962, 8890206, 8890450, 8890694, 8890938, 8891182, 8891426, 8891670, 8891914, 8892158, 8892402, 8892646, 8892890, 8893134,
  8893378, 8893622, 8893865, 8894108
]
theorem checked40 : certifiedList 4000 8869468 values40 = true := by
  have h : certifiedListFast 4000 8869468 values40 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block40 (i : ℕ) (hlo : 4000 < i) (hhi : i ≤ 4100) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values40.length = 100 := by decide +kernel
  have hh : 8869468 = lowerHarmonicInt 4000 := by decide +kernel
  have h := certifiedList_sound values40 4000 8869468 checked40 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values41 : List ℕ := [
  8894351, 8894594, 8894837, 8895080, 8895323, 8895566, 8895809, 8896052, 8896295, 8896538, 8896781, 8897024, 8897267, 8897510, 8897753, 8897995,
  8898237, 8898479, 8898721, 8898963, 8899205, 8899447, 8899689, 8899931, 8900173, 8900415, 8900657, 8900899, 8901141, 8901383, 8901625, 8901867,
  8902108, 8902349, 8902590, 8902831, 8903072, 8903313, 8903554, 8903795, 8904036, 8904277, 8904518, 8904759, 8905000, 8905241, 8905482, 8905723,
  8905964, 8906204, 8906444, 8906684, 8906924, 8907164, 8907404, 8907644, 8907884, 8908124, 8908364, 8908604, 8908844, 8909084, 8909324, 8909564,
  8909804, 8910044, 8910283, 8910522, 8910761, 8911000, 8911239, 8911478, 8911717, 8911956, 8912195, 8912434, 8912673, 8912912, 8913151, 8913390,
  8913629, 8913868, 8914107, 8914346, 8914584, 8914822, 8915060, 8915298, 8915536, 8915774, 8916012, 8916250, 8916488, 8916726, 8916964, 8917202,
  8917440, 8917678, 8917916, 8918154
]
theorem checked41 : certifiedList 4100 8894108 values41 = true := by
  have h : certifiedListFast 4100 8894108 values41 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block41 (i : ℕ) (hlo : 4100 < i) (hhi : i ≤ 4200) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values41.length = 100 := by decide +kernel
  have hh : 8894108 = lowerHarmonicInt 4100 := by decide +kernel
  have h := certifiedList_sound values41 4100 8894108 checked41 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values42 : List ℕ := [
  8918392, 8918629, 8918866, 8919103, 8919340, 8919577, 8919814, 8920051, 8920288, 8920525, 8920762, 8920999, 8921236, 8921473, 8921710, 8921947,
  8922184, 8922421, 8922658, 8922894, 8923130, 8923366, 8923602, 8923838, 8924074, 8924310, 8924546, 8924782, 8925018, 8925254, 8925490, 8925726,
  8925962, 8926198, 8926434, 8926670, 8926906, 8927141, 8927376, 8927611, 8927846, 8928081, 8928316, 8928551, 8928786, 8929021, 8929256, 8929491,
  8929726, 8929961, 8930196, 8930431, 8930666, 8930901, 8931136, 8931370, 8931604, 8931838, 8932072, 8932306, 8932540, 8932774, 8933008, 8933242,
  8933476, 8933710, 8933944, 8934178, 8934412, 8934646, 8934880, 8935114, 8935348, 8935581, 8935814, 8936047, 8936280, 8936513, 8936746, 8936979,
  8937212, 8937445, 8937678, 8937911, 8938144, 8938377, 8938610, 8938843, 8939076, 8939309, 8939542, 8939774, 8940006, 8940238, 8940470, 8940702,
  8940934, 8941166, 8941398, 8941630
]
theorem checked42 : certifiedList 4200 8918154 values42 = true := by
  have h : certifiedListFast 4200 8918154 values42 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block42 (i : ℕ) (hlo : 4200 < i) (hhi : i ≤ 4300) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values42.length = 100 := by decide +kernel
  have hh : 8918154 = lowerHarmonicInt 4200 := by decide +kernel
  have h := certifiedList_sound values42 4200 8918154 checked42 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values43 : List ℕ := [
  8941862, 8942094, 8942326, 8942558, 8942790, 8943022, 8943254, 8943486, 8943718, 8943950, 8944181, 8944412, 8944643, 8944874, 8945105, 8945336,
  8945567, 8945798, 8946029, 8946260, 8946491, 8946722, 8946953, 8947184, 8947415, 8947646, 8947877, 8948108, 8948339, 8948569, 8948799, 8949029,
  8949259, 8949489, 8949719, 8949949, 8950179, 8950409, 8950639, 8950869, 8951099, 8951329, 8951559, 8951789, 8952019, 8952249, 8952479, 8952708,
  8952937, 8953166, 8953395, 8953624, 8953853, 8954082, 8954311, 8954540, 8954769, 8954998, 8955227, 8955456, 8955685, 8955914, 8956143, 8956372,
  8956601, 8956830, 8957058, 8957286, 8957514, 8957742, 8957970, 8958198, 8958426, 8958654, 8958882, 8959110, 8959338, 8959566, 8959794, 8960022,
  8960250, 8960478, 8960706, 8960934, 8961162, 8961389, 8961616, 8961843, 8962070, 8962297, 8962524, 8962751, 8962978, 8963205, 8963432, 8963659,
  8963886, 8964113, 8964340, 8964567
]
theorem checked43 : certifiedList 4300 8941630 values43 = true := by
  have h : certifiedListFast 4300 8941630 values43 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block43 (i : ℕ) (hlo : 4300 < i) (hhi : i ≤ 4400) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values43.length = 100 := by decide +kernel
  have hh : 8941630 = lowerHarmonicInt 4300 := by decide +kernel
  have h := certifiedList_sound values43 4300 8941630 checked43 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values44 : List ℕ := [
  8964794, 8965021, 8965248, 8965475, 8965702, 8965928, 8966154, 8966380, 8966606, 8966832, 8967058, 8967284, 8967510, 8967736, 8967962, 8968188,
  8968414, 8968640, 8968866, 8969092, 8969318, 8969544, 8969770, 8969996, 8970221, 8970446, 8970671, 8970896, 8971121, 8971346, 8971571, 8971796,
  8972021, 8972246, 8972471, 8972696, 8972921, 8973146, 8973371, 8973596, 8973821, 8974046, 8974271, 8974496, 8974720, 8974944, 8975168, 8975392,
  8975616, 8975840, 8976064, 8976288, 8976512, 8976736, 8976960, 8977184, 8977408, 8977632, 8977856, 8978080, 8978304, 8978528, 8978752, 8978976,
  8979199, 8979422, 8979645, 8979868, 8980091, 8980314, 8980537, 8980760, 8980983, 8981206, 8981429, 8981652, 8981875, 8982098, 8982321, 8982544,
  8982767, 8982990, 8983213, 8983436, 8983658, 8983880, 8984102, 8984324, 8984546, 8984768, 8984990, 8985212, 8985434, 8985656, 8985878, 8986100,
  8986322, 8986544, 8986766, 8986988
]
theorem checked44 : certifiedList 4400 8964567 values44 = true := by
  have h : certifiedListFast 4400 8964567 values44 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block44 (i : ℕ) (hlo : 4400 < i) (hhi : i ≤ 4500) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values44.length = 100 := by decide +kernel
  have hh : 8964567 = lowerHarmonicInt 4400 := by decide +kernel
  have h := certifiedList_sound values44 4400 8964567 checked44 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values45 : List ℕ := [
  8987210, 8987432, 8987654, 8987876, 8988097, 8988318, 8988539, 8988760, 8988981, 8989202, 8989423, 8989644, 8989865, 8990086, 8990307, 8990528,
  8990749, 8990970, 8991191, 8991412, 8991633, 8991854, 8992075, 8992296, 8992516, 8992736, 8992956, 8993176, 8993396, 8993616, 8993836, 8994056,
  8994276, 8994496, 8994716, 8994936, 8995156, 8995376, 8995596, 8995816, 8996036, 8996256, 8996476, 8996696, 8996916, 8997135, 8997354, 8997573,
  8997792, 8998011, 8998230, 8998449, 8998668, 8998887, 8999106, 8999325, 8999544, 8999763, 8999982, 9000201, 9000420, 9000639, 9000858, 9001077,
  9001296, 9001515, 9001733, 9001951, 9002169, 9002387, 9002605, 9002823, 9003041, 9003259, 9003477, 9003695, 9003913, 9004131, 9004349, 9004567,
  9004785, 9005003, 9005221, 9005439, 9005657, 9005875, 9006093, 9006310, 9006527, 9006744, 9006961, 9007178, 9007395, 9007612, 9007829, 9008046,
  9008263, 9008480, 9008697, 9008914
]
theorem checked45 : certifiedList 4500 8986988 values45 = true := by
  have h : certifiedListFast 4500 8986988 values45 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block45 (i : ℕ) (hlo : 4500 < i) (hhi : i ≤ 4600) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values45.length = 100 := by decide +kernel
  have hh : 8986988 = lowerHarmonicInt 4500 := by decide +kernel
  have h := certifiedList_sound values45 4500 8986988 checked45 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values46 : List ℕ := [
  9009131, 9009348, 9009565, 9009782, 9009999, 9010216, 9010433, 9010650, 9010866, 9011082, 9011298, 9011514, 9011730, 9011946, 9012162, 9012378,
  9012594, 9012810, 9013026, 9013242, 9013458, 9013674, 9013890, 9014106, 9014322, 9014538, 9014754, 9014970, 9015186, 9015401, 9015616, 9015831,
  9016046, 9016261, 9016476, 9016691, 9016906, 9017121, 9017336, 9017551, 9017766, 9017981, 9018196, 9018411, 9018626, 9018841, 9019056, 9019271,
  9019486, 9019701, 9019916, 9020130, 9020344, 9020558, 9020772, 9020986, 9021200, 9021414, 9021628, 9021842, 9022056, 9022270, 9022484, 9022698,
  9022912, 9023126, 9023340, 9023554, 9023768, 9023982, 9024196, 9024410, 9024623, 9024836, 9025049, 9025262, 9025475, 9025688, 9025901, 9026114,
  9026327, 9026540, 9026753, 9026966, 9027179, 9027392, 9027605, 9027818, 9028031, 9028244, 9028457, 9028670, 9028883, 9029096, 9029308, 9029520,
  9029732, 9029944, 9030156, 9030368
]
theorem checked46 : certifiedList 4600 9008914 values46 = true := by
  have h : certifiedListFast 4600 9008914 values46 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block46 (i : ℕ) (hlo : 4600 < i) (hhi : i ≤ 4700) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values46.length = 100 := by decide +kernel
  have hh : 9008914 = lowerHarmonicInt 4600 := by decide +kernel
  have h := certifiedList_sound values46 4600 9008914 checked46 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values47 : List ℕ := [
  9030580, 9030792, 9031004, 9031216, 9031428, 9031640, 9031852, 9032064, 9032276, 9032488, 9032700, 9032912, 9033124, 9033336, 9033548, 9033760,
  9033971, 9034182, 9034393, 9034604, 9034815, 9035026, 9035237, 9035448, 9035659, 9035870, 9036081, 9036292, 9036503, 9036714, 9036925, 9037136,
  9037347, 9037558, 9037769, 9037980, 9038191, 9038402, 9038613, 9038823, 9039033, 9039243, 9039453, 9039663, 9039873, 9040083, 9040293, 9040503,
  9040713, 9040923, 9041133, 9041343, 9041553, 9041763, 9041973, 9042183, 9042393, 9042603, 9042813, 9043023, 9043233, 9043442, 9043651, 9043860,
  9044069, 9044278, 9044487, 9044696, 9044905, 9045114, 9045323, 9045532, 9045741, 9045950, 9046159, 9046368, 9046577, 9046786, 9046995, 9047204,
  9047413, 9047622, 9047831, 9048040, 9048248, 9048456, 9048664, 9048872, 9049080, 9049288, 9049496, 9049704, 9049912, 9050120, 9050328, 9050536,
  9050744, 9050952, 9051160, 9051368
]
theorem checked47 : certifiedList 4700 9030368 values47 = true := by
  have h : certifiedListFast 4700 9030368 values47 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block47 (i : ℕ) (hlo : 4700 < i) (hhi : i ≤ 4800) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values47.length = 100 := by decide +kernel
  have hh : 9030368 = lowerHarmonicInt 4700 := by decide +kernel
  have h := certifiedList_sound values47 4700 9030368 checked47 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values48 : List ℕ := [
  9051576, 9051784, 9051992, 9052200, 9052408, 9052616, 9052824, 9053031, 9053238, 9053445, 9053652, 9053859, 9054066, 9054273, 9054480, 9054687,
  9054894, 9055101, 9055308, 9055515, 9055722, 9055929, 9056136, 9056343, 9056550, 9056757, 9056964, 9057171, 9057378, 9057585, 9057791, 9057997,
  9058203, 9058409, 9058615, 9058821, 9059027, 9059233, 9059439, 9059645, 9059851, 9060057, 9060263, 9060469, 9060675, 9060881, 9061087, 9061293,
  9061499, 9061705, 9061911, 9062117, 9062323, 9062529, 9062734, 9062939, 9063144, 9063349, 9063554, 9063759, 9063964, 9064169, 9064374, 9064579,
  9064784, 9064989, 9065194, 9065399, 9065604, 9065809, 9066014, 9066219, 9066424, 9066629, 9066834, 9067039, 9067244, 9067449, 9067653, 9067857,
  9068061, 9068265, 9068469, 9068673, 9068877, 9069081, 9069285, 9069489, 9069693, 9069897, 9070101, 9070305, 9070509, 9070713, 9070917, 9071121,
  9071325, 9071529, 9071733, 9071937
]
theorem checked48 : certifiedList 4800 9051368 values48 = true := by
  have h : certifiedListFast 4800 9051368 values48 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block48 (i : ℕ) (hlo : 4800 < i) (hhi : i ≤ 4900) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values48.length = 100 := by decide +kernel
  have hh : 9051368 = lowerHarmonicInt 4800 := by decide +kernel
  have h := certifiedList_sound values48 4800 9051368 checked48 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values49 : List ℕ := [
  9072141, 9072344, 9072547, 9072750, 9072953, 9073156, 9073359, 9073562, 9073765, 9073968, 9074171, 9074374, 9074577, 9074780, 9074983, 9075186,
  9075389, 9075592, 9075795, 9075998, 9076201, 9076404, 9076607, 9076810, 9077013, 9077216, 9077418, 9077620, 9077822, 9078024, 9078226, 9078428,
  9078630, 9078832, 9079034, 9079236, 9079438, 9079640, 9079842, 9080044, 9080246, 9080448, 9080650, 9080852, 9081054, 9081256, 9081458, 9081660,
  9081862, 9082064, 9082265, 9082466, 9082667, 9082868, 9083069, 9083270, 9083471, 9083672, 9083873, 9084074, 9084275, 9084476, 9084677, 9084878,
  9085079, 9085280, 9085481, 9085682, 9085883, 9086084, 9086285, 9086486, 9086687, 9086888, 9087089, 9087289, 9087489, 9087689, 9087889, 9088089,
  9088289, 9088489, 9088689, 9088889, 9089089, 9089289, 9089489, 9089689, 9089889, 9090089, 9090289, 9090489, 9090689, 9090889, 9091089, 9091289,
  9091489, 9091689, 9091889, 9092089
]
theorem checked49 : certifiedList 4900 9071937 values49 = true := by
  have h : certifiedListFast 4900 9071937 values49 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block49 (i : ℕ) (hlo : 4900 < i) (hhi : i ≤ 5000) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values49.length = 100 := by decide +kernel
  have hh : 9071937 = lowerHarmonicInt 4900 := by decide +kernel
  have h := certifiedList_sound values49 4900 9071937 checked49 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

def values50 : List ℕ := [
  9092288, 9092487, 9092686, 9092885, 9093084, 9093283, 9093482, 9093681, 9093880, 9094079, 9094278, 9094477, 9094676, 9094875, 9095074, 9095273,
  9095472, 9095671, 9095870, 9096069, 9096268, 9096467, 9096666, 9096865, 9097064, 9097262, 9097460, 9097658, 9097856, 9098054, 9098252, 9098450,
  9098648, 9098846, 9099044, 9099242, 9099440, 9099638, 9099836, 9100034
]
theorem checked50 : certifiedList 5000 9092089 values50 = true := by
  have h : certifiedListFast 5000 9092089 values50 = true := by decide +kernel
  simpa only [certifiedListFast_eq] using h

theorem block50 (i : ℕ) (hlo : 5000 < i) (hhi : i ≤ 5040) (hi1 : 1 < i) :
    (σ 1 i : ℚ) < lowerHarmonic i +
      lowerExp (lowerHarmonic i) * lowerLog (lowerHarmonic i) := by
  have hlen : values50.length = 40 := by decide +kernel
  have hh : 9092089 = lowerHarmonicInt 5000 := by decide +kernel
  have h := certifiedList_sound values50 5000 9092089 checked50 hh i hlo
    (by rw [hlen]; omega) hi1
  simpa only [sigmaFast_eq (by omega : i ≠ 0)] using h

theorem checkSmall : ∀ n : Fin 5041, 1 < n.val →
    (σ 1 n.val : ℚ) < lowerHarmonic n.val +
      lowerExp (lowerHarmonic n.val) * lowerLog (lowerHarmonic n.val) := by
  intro n hn
  by_cases hb0 : n.val ≤ 100
  · exact block0 n.val (by omega) hb0 hn
  by_cases hb1 : n.val ≤ 200
  · exact block1 n.val (by omega) hb1 hn
  by_cases hb2 : n.val ≤ 300
  · exact block2 n.val (by omega) hb2 hn
  by_cases hb3 : n.val ≤ 400
  · exact block3 n.val (by omega) hb3 hn
  by_cases hb4 : n.val ≤ 500
  · exact block4 n.val (by omega) hb4 hn
  by_cases hb5 : n.val ≤ 600
  · exact block5 n.val (by omega) hb5 hn
  by_cases hb6 : n.val ≤ 700
  · exact block6 n.val (by omega) hb6 hn
  by_cases hb7 : n.val ≤ 800
  · exact block7 n.val (by omega) hb7 hn
  by_cases hb8 : n.val ≤ 900
  · exact block8 n.val (by omega) hb8 hn
  by_cases hb9 : n.val ≤ 1000
  · exact block9 n.val (by omega) hb9 hn
  by_cases hb10 : n.val ≤ 1100
  · exact block10 n.val (by omega) hb10 hn
  by_cases hb11 : n.val ≤ 1200
  · exact block11 n.val (by omega) hb11 hn
  by_cases hb12 : n.val ≤ 1300
  · exact block12 n.val (by omega) hb12 hn
  by_cases hb13 : n.val ≤ 1400
  · exact block13 n.val (by omega) hb13 hn
  by_cases hb14 : n.val ≤ 1500
  · exact block14 n.val (by omega) hb14 hn
  by_cases hb15 : n.val ≤ 1600
  · exact block15 n.val (by omega) hb15 hn
  by_cases hb16 : n.val ≤ 1700
  · exact block16 n.val (by omega) hb16 hn
  by_cases hb17 : n.val ≤ 1800
  · exact block17 n.val (by omega) hb17 hn
  by_cases hb18 : n.val ≤ 1900
  · exact block18 n.val (by omega) hb18 hn
  by_cases hb19 : n.val ≤ 2000
  · exact block19 n.val (by omega) hb19 hn
  by_cases hb20 : n.val ≤ 2100
  · exact block20 n.val (by omega) hb20 hn
  by_cases hb21 : n.val ≤ 2200
  · exact block21 n.val (by omega) hb21 hn
  by_cases hb22 : n.val ≤ 2300
  · exact block22 n.val (by omega) hb22 hn
  by_cases hb23 : n.val ≤ 2400
  · exact block23 n.val (by omega) hb23 hn
  by_cases hb24 : n.val ≤ 2500
  · exact block24 n.val (by omega) hb24 hn
  by_cases hb25 : n.val ≤ 2600
  · exact block25 n.val (by omega) hb25 hn
  by_cases hb26 : n.val ≤ 2700
  · exact block26 n.val (by omega) hb26 hn
  by_cases hb27 : n.val ≤ 2800
  · exact block27 n.val (by omega) hb27 hn
  by_cases hb28 : n.val ≤ 2900
  · exact block28 n.val (by omega) hb28 hn
  by_cases hb29 : n.val ≤ 3000
  · exact block29 n.val (by omega) hb29 hn
  by_cases hb30 : n.val ≤ 3100
  · exact block30 n.val (by omega) hb30 hn
  by_cases hb31 : n.val ≤ 3200
  · exact block31 n.val (by omega) hb31 hn
  by_cases hb32 : n.val ≤ 3300
  · exact block32 n.val (by omega) hb32 hn
  by_cases hb33 : n.val ≤ 3400
  · exact block33 n.val (by omega) hb33 hn
  by_cases hb34 : n.val ≤ 3500
  · exact block34 n.val (by omega) hb34 hn
  by_cases hb35 : n.val ≤ 3600
  · exact block35 n.val (by omega) hb35 hn
  by_cases hb36 : n.val ≤ 3700
  · exact block36 n.val (by omega) hb36 hn
  by_cases hb37 : n.val ≤ 3800
  · exact block37 n.val (by omega) hb37 hn
  by_cases hb38 : n.val ≤ 3900
  · exact block38 n.val (by omega) hb38 hn
  by_cases hb39 : n.val ≤ 4000
  · exact block39 n.val (by omega) hb39 hn
  by_cases hb40 : n.val ≤ 4100
  · exact block40 n.val (by omega) hb40 hn
  by_cases hb41 : n.val ≤ 4200
  · exact block41 n.val (by omega) hb41 hn
  by_cases hb42 : n.val ≤ 4300
  · exact block42 n.val (by omega) hb42 hn
  by_cases hb43 : n.val ≤ 4400
  · exact block43 n.val (by omega) hb43 hn
  by_cases hb44 : n.val ≤ 4500
  · exact block44 n.val (by omega) hb44 hn
  by_cases hb45 : n.val ≤ 4600
  · exact block45 n.val (by omega) hb45 hn
  by_cases hb46 : n.val ≤ 4700
  · exact block46 n.val (by omega) hb46 hn
  by_cases hb47 : n.val ≤ 4800
  · exact block47 n.val (by omega) hb47 hn
  by_cases hb48 : n.val ≤ 4900
  · exact block48 n.val (by omega) hb48 hn
  by_cases hb49 : n.val ≤ 5000
  · exact block49 n.val (by omega) hb49 hn
  exact block50 n.val (by omega) (by omega) hn


lemma lowerHarmonicInt_monotone : Monotone lowerHarmonicInt := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_add_right _ _

lemma one_le_lowerHarmonic {n : ℕ} (hn : 1 ≤ n) : 1 ≤ lowerHarmonic n := by
  have h := lowerHarmonicInt_monotone hn
  norm_num [lowerHarmonicInt] at h
  unfold lowerHarmonic
  rw [le_div_iff₀ (by norm_num)]
  exact_mod_cast h

lemma lowerHarmonic_le_harmonic (n : ℕ) : lowerHarmonic n ≤ harmonic n := by
  induction n with
  | zero => simp [lowerHarmonic, lowerHarmonicInt, harmonic_zero]
  | succ n ih =>
    rw [lowerHarmonic, lowerHarmonicInt, Nat.cast_add, add_div, harmonic_succ]
    apply add_le_add ih
    calc
      ((1000000 / (n + 1) : ℕ) : ℚ) / 1000000 ≤
          (1000000 / (n + 1) : ℚ) / 1000000 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast (Nat.cast_div_le (α := ℚ) (m := 1000000) (n := n + 1))
      _ = ((n + 1 : ℕ) : ℚ)⁻¹ := by push_cast; ring

lemma lowerExp_nonneg {q : ℚ} (hq : 0 ≤ q) : 0 ≤ (lowerExp q : ℝ) := by
  have hq' : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  unfold lowerExp
  push_cast
  exact sum_nonneg fun k hk => div_nonneg (pow_nonneg hq' _) (by positivity)

lemma lowerExp_le {q : ℚ} (hq : 0 ≤ q) : (lowerExp q : ℝ) ≤ Real.exp q := by
  have hq' : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  simpa only [lowerExp, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    using Real.sum_le_exp_of_nonneg hq' 18

lemma lowerLog_nonneg {q : ℚ} (hq : 1 ≤ q) : 0 ≤ (lowerLog q : ℝ) := by
  have hq' : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  unfold lowerLog
  push_cast
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro k hk
  apply div_nonneg
  · exact pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  · positivity

lemma lowerLog_le {q : ℚ} (hq : 1 ≤ q) : (lowerLog q : ℝ) ≤ Real.log q := by
  have hq' : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  let z : ℝ := ((q : ℝ) - 1) / ((q : ℝ) + 1)
  have hz₀ : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz₁ : z < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have heq : (1 + z) / (1 - z) = (q : ℝ) := by
    dsimp [z]
    have hpos : (q : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  have h := Real.sum_range_le_log_div hz₀ hz₁ 5
  rw [heq] at h
  have hcast : (lowerLog q : ℝ) =
      2 * ∑ k ∈ range 5, z ^ (2 * k + 1) / (2 * k + 1) := by
    simp [lowerLog, z]
  rw [hcast]
  linarith

lemma lowerExpression_le {n : ℕ} (hn : 1 ≤ n) :
    ((lowerHarmonic n + lowerExp (lowerHarmonic n) * lowerLog (lowerHarmonic n) : ℚ) : ℝ)
      ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) := by
  have hq := one_le_lowerHarmonic hn
  have hqh := lowerHarmonic_le_harmonic n
  have hq' : 1 ≤ (lowerHarmonic n : ℝ) := by exact_mod_cast hq
  have hqh' : (lowerHarmonic n : ℝ) ≤ (harmonic n : ℝ) := by exact_mod_cast hqh
  have he : (lowerExp (lowerHarmonic n) : ℝ) ≤ Real.exp (harmonic n) :=
    (lowerExp_le (by linarith : 0 ≤ lowerHarmonic n)).trans (Real.exp_le_exp.mpr hqh')
  have hl : (lowerLog (lowerHarmonic n) : ℝ) ≤ Real.log (harmonic n) :=
    (lowerLog_le hq).trans (Real.log_le_log (by linarith) hqh')
  push_cast
  exact add_le_add hqh' (mul_le_mul he hl (lowerLog_nonneg hq) (Real.exp_pos _).le)


theorem finish
    (hcert : ∀ n : Fin 5041, 1 < n.val →
      (σ 1 n.val : ℚ) < lowerHarmonic n.val +
        lowerExp (lowerHarmonic n.val) * lowerLog (lowerHarmonic n.val))
    (n : ℕ) (hn : 0 < n) (hbound : n ≤ 5040) :
    (((σ 1 n : ℕ) : ℝ) ≤ (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) ∧
      ((((σ 1 n : ℕ) : ℝ) = (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) ↔ n = 1) := by
  by_cases h1 : n = 1
  · subst n
    norm_num [harmonic, ArithmeticFunction.sigma]
  · have hc := hcert ⟨n, by omega⟩ (by change 1 < n; omega)
    have hc' : ((σ 1 n : ℕ) : ℝ) <
        ((lowerHarmonic n + lowerExp (lowerHarmonic n) *
          lowerLog (lowerHarmonic n) : ℚ) : ℝ) := by exact_mod_cast hc
    have hs := hc'.trans_le (lowerExpression_le (by omega : 1 ≤ n))
    exact ⟨hs.le, ⟨fun h => False.elim (hs.ne h), fun h => False.elim (h1 h)⟩⟩

end LagariasFiniteCertificate

theorem solution (n : ℕ) (hn : 0 < n) (hbound : n ≤ 5040) :
    (((σ 1 n : ℕ) : ℝ) ≤ (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) ∧
      ((((σ 1 n : ℕ) : ℝ) = (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) ↔ n = 1) :=
  LagariasFiniteCertificate.finish LagariasFiniteCertificate.checkSmall n hn hbound

#print axioms solution
