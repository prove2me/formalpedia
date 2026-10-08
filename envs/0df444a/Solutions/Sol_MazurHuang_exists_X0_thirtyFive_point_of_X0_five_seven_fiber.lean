-- Prove2me | solution 1 for MazurHuang.exists_X0_thirtyFive_point_of_X0_five_seven_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:12:40.911763+00:00
-- url     : https://prove2.me/submissions/75ed4013-9013-498f-99f5-0e0e5e648631

/-
From the fibre product X_0(5) x_j X_0(7) to Kubert's hyperelliptic model of X_0(35).

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135.lean (the fibre equation, the hyperelliptic model, the inverse map and its certificate, the
    coefficient tables, inverse_residual_zero, inverse_hyperelliptic_relation, fiber_to_X035; the
    nonvanishing of the numerator and the denominator is taken from the published theorem)
  * the published statement
-/
import Mathlib
import Theorems.Thm_MazurHuang_X0_five_seven_fiber_inverse_ne_zero

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open Polynomial

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 23-39
/-- The standard `X₀(5)` numerator in its Hauptmodul `a`. -/
def J5Numerator (a : ℚ) : ℚ := (a ^ 2 + 10 * a + 5) ^ 3

/-- The standard `X₀(7)` numerator in its Hauptmodul `b`. -/
def J7Numerator (b : ℚ) : ℚ :=
  (b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3

/-- The affine fiber product `X₀(5) ×_j X₀(7)`. -/
def X035FiberEquation (a b : ℚ) : Prop :=
  b * J5Numerator a = a * J7Numerator b

/-- Kubert's hyperelliptic polynomial for `X₀(35)`. -/
def hyperellipticF35 (x : ℚ) : ℚ :=
  x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 +
    4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1

def OnX035 (x y : ℚ) : Prop := y ^ 2 = hyperellipticF35 x

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 123-189
def inverseXDen (a b : ℚ) : ℚ :=
  347 * b + 384 * b ^ 2 + 133 * b ^ 3 + 19 * b ^ 4 + b ^ 5 - 136 * a -
    15 * a * b + 4 * a * b ^ 2 - 51 * a ^ 2 - 8 * a ^ 2 * b +
    a ^ 2 * b ^ 2 - 4 * a ^ 3 - a ^ 3 * b

def inverseXNum (a b : ℚ) : ℚ :=
  3 - 74 * b - 63 * b ^ 2 - 14 * b ^ 3 - b ^ 4 + 23 * a - 54 * a * b -
    63 * a * b ^ 2 - 14 * a * b ^ 3 - a * b ^ 4 + 4 * a ^ 2 +
    4 * a ^ 2 * b

def inverseB7Num (a b : ℚ) : ℚ :=
  inverseXNum a b ^ 2 - 3 * inverseXNum a b * inverseXDen a b -
    inverseXDen a b ^ 2

def inverseA7Num (a b : ℚ) : ℚ :=
  -inverseXDen a b ^ 6 - 5 * inverseXNum a b * inverseXDen a b ^ 5 +
    5 * inverseXNum a b ^ 3 * inverseXDen a b ^ 3 -
    5 * inverseXNum a b ^ 5 * inverseXDen a b + inverseXNum a b ^ 6

def inverseYNum (a b : ℚ) : ℚ :=
  2 * inverseXNum a b * b * inverseXDen a b ^ 5 - inverseA7Num a b

def hyperellipticHomogeneous (a b : ℚ) : ℚ :=
  inverseXNum a b ^ 8 - 4 * inverseXNum a b ^ 7 * inverseXDen a b -
    6 * inverseXNum a b ^ 6 * inverseXDen a b ^ 2 -
    4 * inverseXNum a b ^ 5 * inverseXDen a b ^ 3 -
    9 * inverseXNum a b ^ 4 * inverseXDen a b ^ 4 +
    4 * inverseXNum a b ^ 3 * inverseXDen a b ^ 5 -
    6 * inverseXNum a b ^ 2 * inverseXDen a b ^ 6 +
    4 * inverseXNum a b * inverseXDen a b ^ 7 + inverseXDen a b ^ 8

private def inverseCertificate (a b : ℚ) : ℚ :=
  ((33048 + a * (1279233 + a * (20121237 + a * (163084770 + a * (708120690 + a * (1534001333 + a * (1366888193 +
  a * (639169912 + a * (175810800 + a * (29606400 + a * (3010304 + a * (169984 + a * 4096)))))))))))) + b *
  (((-4035825) + a * ((-126892224) + a * ((-1539142371) + a * ((-8783732490) + a * ((-7579289140) + a *
  ((-1626022212) + a * (810151009 + a * (596244846 + a * (172498840 + a * (29263040 + a * (3161088 + a * (206336
  + a * 6144)))))))))))) + b * ((192680154 + a * (4635032247 + a * (38908280673 + a * ((-26560285045) + a *
  ((-36823447840) + a * ((-9698738810) + a * (712679744 + a * (775786236 + a * (162714175 + a * (18248400 + a *
  (1364640 + a * (88320 + a * 3840)))))))))))) + b * (((-4425749082) + a * ((-72066649479) + a * (257709805474 +
  a * (34466009110 + a * ((-86611519905) + a * ((-32752544549) + a * ((-2389478406) + a * (658593946 + a *
  (151940370 + a * (13768420 + a * (559312 + a * (9920 + a * 1280)))))))))))) + b * ((46411120203 + a *
  ((-615560262767) + a * (609224161182 + a * (310952898075 + a * ((-72102505065) + a * ((-48969617588) + a *
  ((-6519840541) + a * (72210211 + a * (82461850 + a * (7784765 + a * (345151 + a * ((-4040) + a *
  240)))))))))))) + b * ((484883113735 + a * ((-1930254912702) + a * (615383188597 + a * (627526261980 + a *
  (22133736000 + a * ((-37637675359) + a * ((-6523213885) + a * ((-265699725) + a * (24416445 + a * (2369020 + a
  * (160365 + a * ((-1554) + a * 24)))))))))))) + b * ((1738772919632 + a * ((-3350100852216) + a * (75559051656
  + a * (663717442400 + a * (92506283615 + a * ((-15832506736) + a * ((-3622825619) + a * ((-230751651) + a *
  (4154605 + a * (281285 + a * (44252 + a * ((-206) + a * 1)))))))))))) + b * ((3507146002154 + a *
  ((-3705133472166) + a * ((-491273623644) + a * (437241300800 + a * (88670291575 + a * ((-2981755159) + a *
  ((-1237709057) + a * ((-104677048) + a * (583070 + a * ((-35585) + a * (7265 + a * (-10)))))))))))) + b *
  ((4627199025039 + a * ((-2810292565030) + a * ((-620970090710) + a * (191967735860 + a * (50488411355 + a *
  (419708404 + a * ((-256062543) + a * ((-31342577) + a * (137715 + a * ((-16885) + a * 708)))))))))) + b *
  ((4304989682835 + a * ((-1528922544326) + a * ((-419355614539) + a * (56833690110 + a * (20022558825 + a *
  (437376174 + a * ((-24415961) + a * ((-6590759) + a * (32210 + a * ((-2435) + a * 39)))))))))) + b *
  ((2954814201672 + a * ((-614290420987) + a * ((-189267892703) + a * (10554672830 + a * (5897714785 + a *
  (139071272 + a * (2236827 + a * ((-982157) + a * (4460 + a * ((-170) + a * 1)))))))))) + b * ((1541476171660 +
  a * ((-185708581373) + a * ((-61403299752) + a * (720185565 + a * (1329109705 + a * (27020077 + a * (1116377 +
  a * ((-101572) + a * (325 + a * (-5)))))))))) + b * ((623851276046 + a * ((-42686026144) + a * ((-14786596691)
  + a * ((-229842800) + a * (231390995 + a * (3618807 + a * (175648 + a * ((-6923) + a * 10)))))))) + b *
  ((198614490857 + a * ((-7481162621) + a * ((-2677908579) + a * ((-91055290) + a * (30957145 + a * (351386 + a
  * (15204 + a * (-279)))))))) + b * ((50178738727 + a * ((-994520920) + a * ((-364771985) + a * ((-17313985) +
  a * (3123235 + a * (25502 + a * (725 + a * (-5)))))))) + b * ((10101745512 + a * ((-98765699) + a *
  ((-36915126) + a * ((-2137915) + a * (229440 + a * (1386 + a * 15)))))) + b * ((1619728823 + a * ((-7112229) +
  a * ((-2698521) + a * ((-179235) + a * (11550 + a * 52))))) + b * ((205711822 + a * ((-351495) + a *
  ((-134990) + a * ((-9930) + a * (355 + a * 1))))) + b * ((20451653 + a * ((-10686) + a * ((-4144) + a *
  ((-330) + a * 5)))) + b * ((1559412 + a * ((-151) + a * ((-59) + a * (-5)))) + b * (88140 + b * (3483 + b *
  (86 + b * 1)))))))))))))))))))))))

/-- The denominator of the inverse map does not vanish on the fibre away from `b = 0` (statement
as in `FLT/Assumptions/MazurProof/RationalPointsX135.lean`), here from the published theorem
`MazurHuang.X0_five_seven_fiber_inverse_ne_zero`. -/
theorem inverseXDen_ne_zero {a b : ℚ} (hb : b ≠ 0)
    (h : X035FiberEquation a b) : inverseXDen a b ≠ 0 :=
  (MazurHuang.X0_five_seven_fiber_inverse_ne_zero h).2 hb

/-- The numerator of the inverse map does not vanish on the fibre (statement as in the source
file), from the same published theorem. -/
theorem inverseXNum_ne_zero {a b : ℚ}
    (h : X035FiberEquation a b) : inverseXNum a b ≠ 0 :=
  (MazurHuang.X0_five_seven_fiber_inverse_ne_zero h).1

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 360-711
private def inverseResidual (a b : ℚ) : ℚ :=
  b ^ 2 * inverseXDen a b ^ 5 * inverseXNum a b +
    b * inverseXDen a b ^ 6 +
    5 * b * inverseXDen a b ^ 5 * inverseXNum a b -
    5 * b * inverseXDen a b ^ 3 * inverseXNum a b ^ 3 +
    5 * b * inverseXDen a b * inverseXNum a b ^ 5 -
    b * inverseXNum a b ^ 6 +
    49 * inverseXDen a b * inverseXNum a b ^ 5

/-! ### Coefficient tables (port v4.33.1)

Polynomials in `ℤ[a][b]` as tables `List (List ℤ)`: the outer list runs over powers of `b`, the
inner lists over powers of `a`, constant terms first.  The operations below are computable, so a
polynomial identity between tables is checked by kernel evaluation; the lemmas `ev_*` transfer
it to `ℚ`. -/

section PolyTable

/-- Horner value of a coefficient list. -/
private def ev1 : List ℤ → ℚ → ℚ
  | [], _ => 0
  | c :: p, x => (c : ℚ) + x * ev1 p x

private def add1 : List ℤ → List ℤ → List ℤ
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => (c + d) :: add1 p q

private def smul1 (k : ℤ) : List ℤ → List ℤ
  | [] => []
  | c :: p => (k * c) :: smul1 k p

private def mul1 : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | c :: p, q => add1 (smul1 c q) (0 :: mul1 p q)

private def isZero1 : List ℤ → Bool
  | [] => true
  | c :: p => decide (c = 0) && isZero1 p

private theorem ev1_add1 (p q : List ℤ) (x : ℚ) :
    ev1 (add1 p q) x = ev1 p x + ev1 q x := by
  induction p generalizing q with
  | nil => simp [add1, ev1]
  | cons c p ih =>
    cases q with
    | nil => simp [add1, ev1]
    | cons d q =>
      simp only [add1, ev1, ih, Int.cast_add]
      ring

private theorem ev1_smul1 (k : ℤ) (p : List ℤ) (x : ℚ) :
    ev1 (smul1 k p) x = (k : ℚ) * ev1 p x := by
  induction p with
  | nil => simp [smul1, ev1]
  | cons c p ih =>
    simp only [smul1, ev1, ih, Int.cast_mul]
    ring

private theorem ev1_mul1 (p q : List ℤ) (x : ℚ) :
    ev1 (mul1 p q) x = ev1 p x * ev1 q x := by
  induction p with
  | nil => simp [mul1, ev1]
  | cons c p ih =>
    simp only [mul1, ev1_add1, ev1_smul1, ev1, ih, Int.cast_zero]
    ring

private theorem ev1_eq_zero (p : List ℤ) (h : isZero1 p = true) (x : ℚ) : ev1 p x = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [isZero1, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [ev1, h.1, ih h.2]

/-- Value of a coefficient table at `(a, b)`. -/
private def ev2 : List (List ℤ) → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | c :: p, a, b => ev1 c a + b * ev2 p a b

private def add2 : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => add1 c d :: add2 p q

private def smul2 (k : List ℤ) : List (List ℤ) → List (List ℤ)
  | [] => []
  | c :: p => mul1 k c :: smul2 k p

private def mul2 : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], _ => []
  | c :: p, q => add2 (smul2 c q) ([] :: mul2 p q)

private def pow2 (p : List (List ℤ)) : ℕ → List (List ℤ)
  | 0 => [[1]]
  | n + 1 => mul2 p (pow2 p n)

private def isZero2 : List (List ℤ) → Bool
  | [] => true
  | c :: p => isZero1 c && isZero2 p

private theorem ev2_add2 (p q : List (List ℤ)) (a b : ℚ) :
    ev2 (add2 p q) a b = ev2 p a b + ev2 q a b := by
  induction p generalizing q with
  | nil => simp [add2, ev2]
  | cons c p ih =>
    cases q with
    | nil => simp [add2, ev2]
    | cons d q =>
      simp only [add2, ev2, ih, ev1_add1]
      ring

private theorem ev2_smul2 (k : List ℤ) (p : List (List ℤ)) (a b : ℚ) :
    ev2 (smul2 k p) a b = ev1 k a * ev2 p a b := by
  induction p with
  | nil => simp [smul2, ev2]
  | cons c p ih =>
    simp only [smul2, ev2, ih, ev1_mul1]
    ring

private theorem ev2_mul2 (p q : List (List ℤ)) (a b : ℚ) :
    ev2 (mul2 p q) a b = ev2 p a b * ev2 q a b := by
  induction p with
  | nil => simp [mul2, ev2]
  | cons c p ih =>
    simp only [mul2, ev2_add2, ev2_smul2, ev2, ev1, ih]
    ring

private theorem ev2_pow2 (p : List (List ℤ)) (n : ℕ) (a b : ℚ) :
    ev2 (pow2 p n) a b = ev2 p a b ^ n := by
  induction n with
  | zero => simp [pow2, ev2, ev1]
  | succ n ih =>
    simp only [pow2, ev2_mul2, ih]
    ring

private theorem ev2_eq_zero (p : List (List ℤ)) (h : isZero2 p = true) (a b : ℚ) :
    ev2 p a b = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [isZero2, Bool.and_eq_true] at h
    simp [ev2, ev1_eq_zero c h.1, ih h.2]

end PolyTable

/-- Table of `inverseXNum`. -/
private def numTable : List (List ℤ) :=
  [[3, 23, 4],
   [-74, -54, 4],
   [-63, -63],
   [-14, -14],
   [-1, -1]]

/-- Table of `inverseXDen`. -/
private def denTable : List (List ℤ) :=
  [[0, -136, -51, -4],
   [347, -15, -8, -1],
   [384, 4, 1],
   [133],
   [19],
   [1]]

/-- Table of `inverseCertificate`. -/
private def certTable : List (List ℤ) :=
  [[33048, 1279233, 20121237, 163084770, 708120690, 1534001333, 1366888193, 639169912, 175810800,
    29606400, 3010304, 169984, 4096],
   [-4035825, -126892224, -1539142371, -8783732490, -7579289140, -1626022212, 810151009, 596244846,
    172498840, 29263040, 3161088, 206336, 6144],
   [192680154, 4635032247, 38908280673, -26560285045, -36823447840, -9698738810, 712679744,
    775786236, 162714175, 18248400, 1364640, 88320, 3840],
   [-4425749082, -72066649479, 257709805474, 34466009110, -86611519905, -32752544549, -2389478406,
    658593946, 151940370, 13768420, 559312, 9920, 1280],
   [46411120203, -615560262767, 609224161182, 310952898075, -72102505065, -48969617588, -6519840541,
    72210211, 82461850, 7784765, 345151, -4040, 240],
   [484883113735, -1930254912702, 615383188597, 627526261980, 22133736000, -37637675359,
    -6523213885, -265699725, 24416445, 2369020, 160365, -1554, 24],
   [1738772919632, -3350100852216, 75559051656, 663717442400, 92506283615, -15832506736,
    -3622825619, -230751651, 4154605, 281285, 44252, -206, 1],
   [3507146002154, -3705133472166, -491273623644, 437241300800, 88670291575, -2981755159,
    -1237709057, -104677048, 583070, -35585, 7265, -10],
   [4627199025039, -2810292565030, -620970090710, 191967735860, 50488411355, 419708404, -256062543,
    -31342577, 137715, -16885, 708],
   [4304989682835, -1528922544326, -419355614539, 56833690110, 20022558825, 437376174, -24415961,
    -6590759, 32210, -2435, 39],
   [2954814201672, -614290420987, -189267892703, 10554672830, 5897714785, 139071272, 2236827,
    -982157, 4460, -170, 1],
   [1541476171660, -185708581373, -61403299752, 720185565, 1329109705, 27020077, 1116377, -101572,
    325, -5],
   [623851276046, -42686026144, -14786596691, -229842800, 231390995, 3618807, 175648, -6923, 10],
   [198614490857, -7481162621, -2677908579, -91055290, 30957145, 351386, 15204, -279],
   [50178738727, -994520920, -364771985, -17313985, 3123235, 25502, 725, -5],
   [10101745512, -98765699, -36915126, -2137915, 229440, 1386, 15],
   [1619728823, -7112229, -2698521, -179235, 11550, 52],
   [205711822, -351495, -134990, -9930, 355, 1],
   [20451653, -10686, -4144, -330, 5],
   [1559412, -151, -59, -5],
   [88140],
   [3483],
   [86],
   [1]]

/-- Table of the fibre polynomial `b * J5Numerator a - a * J7Numerator b`. -/
private def fiberTable : List (List ℤ) :=
  [[0, -49],
   [125, 2, 1575, 1300, 315, 30, 1],
   [0, -4018],
   [0, -8624],
   [0, -5915],
   [0, -1904],
   [0, -322],
   [0, -28],
   [0, -1]]

/-- The table of `inverseResidual - inverseCertificate * (b * J5Numerator a - a * J7Numerator b)`,
assembled from the four tables by the table operations.  With `N = inverseXNum`, `D = inverseXDen`
the residual is written in Horner form in `D`:
`D * ((5 * b + 49) * N ^ 5 + D ^ 2 * (-5 * b * N ^ 3 + D ^ 2 * ((b ^ 2 + 5 * b) * N + b * D))) - b * N ^ 6`. -/
private def residualTable : List (List ℤ) :=
  add2
    (add2
      (mul2 denTable
        (add2
          (mul2 (pow2 denTable 2)
            (add2
              (mul2 (pow2 denTable 2)
                (add2 (mul2 [[], [5], [1]] numTable) (mul2 [[], [1]] denTable)))
              (mul2 [[], [-5]] (pow2 numTable 3))))
          (mul2 [[49], [5]] (pow2 numTable 5))))
      (mul2 [[], [-1]] (pow2 numTable 6)))
    (mul2 [[-1]] (mul2 fiberTable certTable))

set_option maxRecDepth 100000 in
private theorem residualTable_isZero : isZero2 residualTable = true := by
  decide +kernel

private theorem ev2_numTable (a b : ℚ) : ev2 numTable a b = inverseXNum a b := by
  simp only [numTable, ev2, ev1, inverseXNum]
  push_cast
  ring

private theorem ev2_denTable (a b : ℚ) : ev2 denTable a b = inverseXDen a b := by
  simp only [denTable, ev2, ev1, inverseXDen]
  push_cast
  ring

set_option maxRecDepth 100000 in
private theorem ev2_certTable (a b : ℚ) : ev2 certTable a b = inverseCertificate a b := by
  simp only [certTable, ev2, ev1, inverseCertificate]
  push_cast
  ring

private theorem ev2_fiberTable (a b : ℚ) :
    ev2 fiberTable a b = b * J5Numerator a - a * J7Numerator b := by
  simp only [fiberTable, ev2, ev1, J5Numerator, J7Numerator]
  push_cast
  ring

/-- The residual is the certificate times the fibre polynomial (a polynomial identity). -/
private theorem inverseResidual_eq_certificate_mul (a b : ℚ) :
    inverseResidual a b =
      inverseCertificate a b * (b * J5Numerator a - a * J7Numerator b) := by
  have hz := ev2_eq_zero residualTable residualTable_isZero a b
  simp only [residualTable, ev2_add2, ev2_mul2, ev2_pow2, ev2_numTable, ev2_denTable,
    ev2_certTable, ev2_fiberTable, ev2, ev1] at hz
  push_cast at hz
  unfold inverseResidual
  linear_combination hz

/- port v4.33.1: the fork's proof is
     unfold X035FiberEquation J5Numerator J7Numerator at h
     unfold inverseResidual inverseXNum inverseXDen
     linear_combination (norm := (simp only [inverseCertificate]; ring)) (inverseCertificate a b) * h
   (one `ring` call whose proof term needs about 60 s to process); here the same identity
   `inverseResidual = inverseCertificate * fibre` is the lemma above. -/
private theorem inverse_residual_zero {a b : ℚ}
    (h : X035FiberEquation a b) : inverseResidual a b = 0 := by
  unfold X035FiberEquation at h
  rw [inverseResidual_eq_certificate_mul, sub_eq_zero.mpr h, mul_zero]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The kernel-checked ideal-membership certificate for the inverse map. -/
theorem inverse_hyperelliptic_relation {a b : ℚ}
    (h : X035FiberEquation a b) :
    inverseYNum a b ^ 2 =
      inverseB7Num a b ^ 2 * hyperellipticHomogeneous a b := by
  have hr := inverse_residual_zero h
  unfold inverseYNum inverseA7Num inverseB7Num hyperellipticHomogeneous
  have hfactor :
      (2 * inverseXNum a b * b * inverseXDen a b ^ 5 -
            (-inverseXDen a b ^ 6 -
              5 * inverseXNum a b * inverseXDen a b ^ 5 +
              5 * inverseXNum a b ^ 3 * inverseXDen a b ^ 3 -
              5 * inverseXNum a b ^ 5 * inverseXDen a b +
              inverseXNum a b ^ 6)) ^ 2 -
          (inverseXNum a b ^ 2 -
              3 * inverseXNum a b * inverseXDen a b -
              inverseXDen a b ^ 2) ^ 2 *
            (inverseXNum a b ^ 8 -
              4 * inverseXNum a b ^ 7 * inverseXDen a b -
              6 * inverseXNum a b ^ 6 * inverseXDen a b ^ 2 -
              4 * inverseXNum a b ^ 5 * inverseXDen a b ^ 3 -
              9 * inverseXNum a b ^ 4 * inverseXDen a b ^ 4 +
              4 * inverseXNum a b ^ 3 * inverseXDen a b ^ 5 -
              6 * inverseXNum a b ^ 2 * inverseXDen a b ^ 6 +
              4 * inverseXNum a b * inverseXDen a b ^ 7 +
              inverseXDen a b ^ 8) =
        4 * inverseXDen a b ^ 5 * inverseXNum a b * inverseResidual a b := by
    unfold inverseResidual
    ring
  apply sub_eq_zero.mp
  rw [hfactor, hr]
  ring

def inverseX (a b : ℚ) : ℚ := inverseXNum a b / inverseXDen a b

def inverseY (a b : ℚ) : ℚ :=
  inverseYNum a b / (inverseB7Num a b * inverseXDen a b ^ 4)

private theorem inverseB7Num_ne_zero {a b : ℚ} (hb : b ≠ 0)
    (h : X035FiberEquation a b) : inverseB7Num a b ≠ 0 := by
  have hd := inverseXDen_ne_zero hb h
  intro hzero
  have hquad :
      (inverseXNum a b / inverseXDen a b) ^ 2 -
          3 * (inverseXNum a b / inverseXDen a b) - 1 = 0 := by
    unfold inverseB7Num at hzero
    field_simp [hd]
    linear_combination hzero
  have hsquare :
      (2 * (inverseXNum a b / inverseXDen a b) - 3) ^ 2 = 13 := by
    nlinarith
  have hnot : ¬ IsSquare (13 : ℚ) := by norm_num
  exact hnot ⟨2 * (inverseXNum a b / inverseXDen a b) - 3,
    by simpa [pow_two] using hsquare.symm⟩

/-- Every noncuspidal point of the Hauptmodul fiber lies on Kubert's affine
hyperelliptic model. -/
theorem fiber_to_X035 {a b : ℚ} (hb : b ≠ 0)
    (h : X035FiberEquation a b) :
    inverseX a b ≠ 0 ∧ OnX035 (inverseX a b) (inverseY a b) := by
  have hd := inverseXDen_ne_zero hb h
  have hn := inverseXNum_ne_zero h
  have hB7 := inverseB7Num_ne_zero hb h
  constructor
  · exact div_ne_zero hn hd
  · have hrel := inverse_hyperelliptic_relation h
    unfold OnX035 inverseX inverseY hyperellipticF35
    field_simp [hd, hB7]
    unfold hyperellipticHomogeneous at hrel
    rw [hrel]
    ring


end

end MazurProof.RationalPointsX135

end

theorem solution
    {a b : ℚ} (hb : b ≠ 0)
    (h : b * (a ^ 2 + 10 * a + 5) ^ 3 = a * ((b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3)) :
    ∃ x y : ℚ, x ≠ 0 ∧
      y ^ 2 = x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 + 4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1 :=
  ⟨MazurProof.RationalPointsX135.inverseX a b, MazurProof.RationalPointsX135.inverseY a b,
    (MazurProof.RationalPointsX135.fiber_to_X035 hb h).1,
    (MazurProof.RationalPointsX135.fiber_to_X035 hb h).2⟩
