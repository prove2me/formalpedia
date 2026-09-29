-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.phi_eq_phiThree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/18736d39-fdd4-5a56-81ba-2be0e9eb2da9

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_coeff_jNum_le_twelve
import Theorems.Thm_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Polynomial PowerSeries
p2m_open "ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum jNumQ jq ofPowerSeries_coeff_of_neg dedekindPsi evalAtJ ModularPolynomialData ModularPolynomialData.Φ qTwist qTwist_coeff qTwist_one_apply jqModC phiThreeC3 phiThreeC2 phiThreeC1 phiThreeC0 phiThree laurentMap laurentMap_coeff laurentMap_single laurentMap_ofPowerSeries coeff_jNum_le_twelve eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero ModularPolynomialData.natDegree_coeff_le PhiGen.splits_prime_of_isPrimitiveRoot"
p2m_open "ModularCurve"
namespace PhiThreeCalc

abbrev K3 : Type := CyclotomicField 3 ℚ

scoped instance instCyc3 : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

noncomputable def ζ : K3 := IsCyclotomicExtension.zeta 3 ℚ K3
theorem hζ : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K3
theorem ζ_ne_zero : ζ ≠ 0 := hζ.ne_zero (by norm_num)
noncomputable def ζu : K3ˣ := Units.mk0 ζ ζ_ne_zero
theorem ζu_val : (ζu : K3) = ζ := rfl
theorem hζu : IsPrimitiveRoot (ζu : K3) 3 := hζ

variable {R : Type*} [CommRing R]

def LowCoeffs (f : R⟦X⟧) (L : List R) : Prop :=
  ∀ i : ℕ, i < L.length → PowerSeries.coeff i f = L.getD i 0

def conv (L M : List R) : List R :=
  (List.range (min L.length M.length)).map
    fun k => ((List.range (k + 1)).map fun i => L.getD i 0 * M.getD (k - i) 0).sum

theorem length_conv (L M : List R) : (conv L M).length = min L.length M.length := by simp [conv]

theorem finset_sum_range_eq_list_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem getD_conv (L M : List R) {k : ℕ} (hk : k < min L.length M.length) :
    (conv L M).getD k 0 = ∑ i ∈ Finset.range (k + 1), L.getD i 0 * M.getD (k - i) 0 := by
  rw [conv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp [finset_sum_range_eq_list_sum]

theorem LowCoeffs.mul {f g : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (hg : LowCoeffs g M) :
    LowCoeffs (f * g) (conv L M) := by
  intro k hk
  rw [length_conv] at hk
  rw [getD_conv L M hk, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hf i (by omega), hg (k - i) (by omega)]

theorem getD_map_intCast (l : List ℤ) (i : ℕ) : (l.map (Int.cast : ℤ → R)).getD i 0 = ((l.getD i 0 : ℤ) : R) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp

theorem conv_map_intCast (L M : List ℤ) :
    conv (L.map (Int.cast : ℤ → R)) (M.map (Int.cast : ℤ → R)) = (conv L M).map (Int.cast : ℤ → R) := by
  simp only [conv, List.length_map, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, getD_map_intCast]
  rw [Int.cast_list_sum, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp [Function.comp_apply, Int.cast_mul]

noncomputable abbrev ofPS (F : K3⟦X⟧) : LaurentSeries K3 := HahnSeries.ofPowerSeries ℤ K3 F

theorem coeff_ofPS (F : K3⟦X⟧) (m : ℤ) :
    (ofPS F).coeff m = if 0 ≤ m then PowerSeries.coeff m.toNat F else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Int.toNat_natCast, HahnSeries.ofPowerSeries_apply_coeff]
  · exact ofPowerSeries_coeff_of_neg F (by omega)

theorem coeff_single_mul_ofPS (a : ℤ) (r : K3) (F : K3⟦X⟧) (m : ℤ) :
    (HahnSeries.single a r * ofPS F).coeff m = if a ≤ m then r * PowerSeries.coeff (m - a).toNat F else 0 := by
  rw [HahnSeries.coeff_single_mul, coeff_ofPS]
  by_cases h : a ≤ m
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h, mul_zero]

theorem eq_single_mul_ofPS (x : LaurentSeries K3) (a : ℤ) (hx : ∀ m < a, x.coeff m = 0) :
    x = HahnSeries.single a 1 * ofPS (PowerSeries.mk fun i => x.coeff (a + i)) := by
  ext m
  rw [coeff_single_mul_ofPS, one_mul]
  split_ifs with h
  · rw [PowerSeries.coeff_mk]; congr 1; omega
  · exact hx m (by omega)

def NF (x : LaurentSeries K3) (a : ℤ) (L : List ℤ) : Prop :=
  ∃ F : K3⟦X⟧, x = HahnSeries.single a 1 * ofPS F ∧ LowCoeffs F (L.map (Int.cast : ℤ → K3))

theorem NF.mul {x y : LaurentSeries K3} {a b : ℤ} {L M : List ℤ} (hx : NF x a L) (hy : NF y b M) :
    NF (x * y) (a + b) (conv L M) := by
  obtain ⟨F, rfl, hF⟩ := hx
  obtain ⟨G, rfl, hG⟩ := hy
  refine ⟨F * G, ?_, ?_⟩
  · rw [mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul]
    congr 1
    exact (map_mul (HahnSeries.ofPowerSeries ℤ K3) F G).symm
  · rw [← conv_map_intCast]; exact hF.mul hG

theorem NF.congr {x : LaurentSeries K3} {a : ℤ} {L M : List ℤ} (hx : NF x a L) (h : L = M) : NF x a M := h ▸ hx

theorem NF.coeff {x : LaurentSeries K3} {a : ℤ} {L : List ℤ} (hx : NF x a L) (m : ℤ) (hm : (m - a).toNat < L.length) :
    x.coeff m = if a ≤ m then ((L.getD (m - a).toNat 0 : ℤ) : K3) else 0 := by
  obtain ⟨F, rfl, hF⟩ := hx
  rw [coeff_single_mul_ofPS, one_mul]
  split_ifs with h
  · rw [hF _ (by simpa using hm), getD_map_intCast]
  · rfl

theorem NF.coeff_lt {x : LaurentSeries K3} {a : ℤ} {L : List ℤ} (hx : NF x a L) (m : ℤ) (hm : m < a) : x.coeff m = 0 := by
  obtain ⟨F, rfl, hF⟩ := hx
  rw [coeff_single_mul_ofPS, if_neg (by omega)]

theorem NF.of_coeff {x : LaurentSeries K3} {a : ℤ} {L : List ℤ} (hlow : ∀ m < a, x.coeff m = 0)
    (hco : ∀ i : ℕ, i < L.length → x.coeff (a + i) = ((L.getD i 0 : ℤ) : K3)) : NF x a L := by
  refine ⟨PowerSeries.mk fun i => x.coeff (a + i), eq_single_mul_ofPS x a hlow, ?_⟩
  intro i hi
  rw [List.length_map] at hi
  rw [PowerSeries.coeff_mk, hco i hi, getD_map_intCast]

noncomputable abbrev J : LaurentSeries K3 := jqModC K3

theorem J_def : J = HahnSeries.single (-1 : ℤ) (1 : K3) * ofPS (jNum.map (Int.castRingHom K3)) := rfl

theorem coeff_J (i : ℕ) : J.coeff (-1 + (i : ℤ)) = ((PowerSeries.coeff i jNum : ℤ) : K3) := by
  rw [J_def, coeff_single_mul_ofPS, one_mul, if_pos (by omega), show (-1 + (i : ℤ) - -1).toNat = i by omega,
    PowerSeries.coeff_map]
  simp

theorem coeff_J_lt {m : ℤ} (hm : m < -1) : J.coeff m = 0 := by
  rw [J_def, coeff_single_mul_ofPS, if_neg (by omega)]

def LJ : List ℤ := [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600, 4252023300096, 44656994071935, 401490886656000, 3176440229784420, 22567393309593600, 146211911499519294]

theorem coeff_jNum_eq_LJ (i : ℕ) (hi : i < 13) : (PowerSeries.coeff i jNum : ℤ) = LJ.getD i 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := ModularCurve.coeff_jNum_le_twelve
  interval_cases i <;> simp [LJ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

theorem nf_J : NF J (-1) LJ :=
  NF.of_coeff (fun m hm => coeff_J_lt hm) (fun i hi => by
    simp only [LJ, List.length_cons, List.length_nil] at hi
    rw [coeff_J, coeff_jNum_eq_LJ i (by omega)])

theorem NF.qExpand {x : LaurentSeries K3} {a : ℤ} {L : List ℤ} (hx : NF x a L) (N : ℕ) [NeZero N] (M : List ℤ)
    (hlen : ∀ i, i < M.length → i / N < L.length)
    (hM : ∀ i, i < M.length → M.getD i 0 = if N ∣ i then L.getD (i / N) 0 else 0) :
    NF (ModularCurve.qExpand K3 N x) ((N : ℤ) * a) M := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine NF.of_coeff (fun m hm => ?_) (fun i hi => ?_)
  · by_cases h : (N : ℤ) ∣ m
    · obtain ⟨c, rfl⟩ := h
      rw [qExpand_coeff_mul]
      exact hx.coeff_lt c (by nlinarith)
    · exact qExpand_coeff_of_not_dvd N x h
  · rw [hM i hi]
    by_cases h : N ∣ i
    · obtain ⟨c, rfl⟩ := h
      rw [if_pos (dvd_mul_right N c), Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero (NeZero.ne N)),
        show (N : ℤ) * a + ((N * c : ℕ) : ℤ) = (N : ℤ) * (a + c) by push_cast; ring, qExpand_coeff_mul,
        hx.coeff (a + c) (by have := hlen (N * c) hi; rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero (NeZero.ne N))] at this; simpa using this),
        if_pos (by omega)]
      congr 2; omega
    · rw [if_neg h, qExpand_coeff_of_not_dvd N x (by
        intro hd
        apply h
        have : (N : ℤ) ∣ (i : ℤ) := by simpa [dvd_add_right (dvd_mul_right (N : ℤ) a)] using hd
        exact_mod_cast this)]
      simp

theorem coeff_sum_qTwist (x : LaurentSeries K3) (n : ℤ) :
    (∑ b ∈ Finset.range 3, qTwist (ζu ^ b) x).coeff n = (if (3 : ℤ) ∣ n then 3 else 0) * x.coeff n := by
  rw [HahnSeries.coeff_sum]
  simp only [qTwist_coeff]
  rw [← Finset.sum_mul]
  congr 1
  have hw3 : ((ζu : K3) ^ n) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζu.pow_eq_one, one_zpow]
  have hsum : ∑ b ∈ Finset.range 3, (((ζu ^ b) ^ n : K3ˣ) : K3) = ∑ b ∈ Finset.range 3, ((ζu : K3) ^ n) ^ b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [hsum]
  by_cases h : (3 : ℤ) ∣ n
  · rw [if_pos h, (hζu.zpow_eq_one_iff_dvd n).mpr h]
    norm_num
  · rw [if_neg h]
    have hne : (ζu : K3) ^ n ≠ 1 := fun h1 => h ((hζu.zpow_eq_one_iff_dvd n).mp h1)
    have := geom_sum_mul ((ζu : K3) ^ n) 3
    rw [hw3, sub_self, mul_eq_zero] at this
    exact this.resolve_right (sub_ne_zero.mpr hne)

theorem NF.msect {x : LaurentSeries K3} {a : ℤ} {L : List ℤ} (hx : NF x a L) (M : List ℤ) (hlen : M.length = L.length)
    (hM : ∀ i, i < M.length → M.getD i 0 = if (3 : ℤ) ∣ a + i then 3 * L.getD i 0 else 0) :
    NF (∑ b ∈ Finset.range 3, qTwist (ζu ^ b) x) a M := by
  refine NF.of_coeff (fun m hm => by rw [coeff_sum_qTwist, hx.coeff_lt m hm, mul_zero]) (fun i hi => ?_)
  rw [coeff_sum_qTwist, hx.coeff (a + i) (by rw [← hlen]; simpa using hi), hM i hi,
    show (a + (i : ℤ) - a).toNat = i by omega, if_pos (show a ≤ a + (i : ℤ) by omega)]
  by_cases h3 : (3 : ℤ) ∣ a + i
  · rw [if_pos h3, if_pos h3]; push_cast; ring
  · rw [if_neg h3, if_neg h3]; push_cast; ring

noncomputable def A : LaurentSeries K3 := ModularCurve.qExpand K3 9 J
noncomputable def Q : LaurentSeries K3 := ModularCurve.qExpand K3 3 J
noncomputable def P1 : LaurentSeries K3 := ∑ b ∈ Finset.range 3, qTwist (ζu ^ b) J
noncomputable def P2 : LaurentSeries K3 := ∑ b ∈ Finset.range 3, qTwist (ζu ^ b) (J ^ 2)
noncomputable def P3 : LaurentSeries K3 := ∑ b ∈ Finset.range 3, qTwist (ζu ^ b) (J ^ 3)

theorem nf_J2 : NF (J ^ 2) (-2) [1, 1488, 947304, 335950912, 72474624276, 9790124955552, 833107628914688, 45630592148400000, 1754954450906393538, 51062104386000089648, 1186840963302480101376, 22924552119951492244800, 378933532779364657975000] := by rw [sq]; exact (nf_J.mul nf_J).congr (by decide)
theorem nf_J3 : NF (J ^ 3) (-3) [1, 2232, 2251260, 1355202240, 541778118390, 151522053809760, 30456116651640888, 4460775211418664960, 479919718908048515625, 38292247221915373896560, 2309356967925215526546564, 108570959012192293978767360, 4111854826236389868361040550] := by
  rw [pow_succ]; exact (nf_J2.mul nf_J).congr (by decide)
theorem nf_A : NF A (-9) [1, 0, 0, 0, 0, 0, 0, 0, 0, 744, 0, 0, 0] :=
  nf_J.qExpand 9 _ (fun i hi => by simp [LJ] at hi ⊢; omega) (fun i hi => by simp at hi; interval_cases i <;> decide)
theorem nf_Q : NF Q (-3) [1, 0, 0, 744, 0, 0, 196884, 0, 0, 21493760, 0, 0, 864299970] :=
  nf_J.qExpand 3 _ (fun i hi => by simp [LJ] at hi ⊢; omega) (fun i hi => by simp at hi; interval_cases i <;> decide)
theorem nf_P1 : NF P1 (-1) [0, 2232, 0, 0, 2592899910, 0, 0, 12756069900288, 0, 0, 9529320689353260, 0, 0] := nf_J.msect _ rfl (fun i hi => by simp at hi; interval_cases i <;> decide)
theorem nf_P2 : NF P2 (-2) [0, 0, 2841912, 0, 0, 29370374866656, 0, 0, 5264863352719180614, 0, 0, 68773656359854476734400, 0] := nf_J2.msect _ rfl (fun i hi => by simp at hi; interval_cases i <;> decide)
theorem nf_P3 : NF P3 (-3) [3, 0, 0, 4065606720, 0, 0, 91368349954922664, 0, 0, 114876741665746121689680, 0, 0, 12335564478709169605083121650] := nf_J3.msect _ rfl (fun i hi => by simp at hi; interval_cases i <;> decide)
theorem nf_AP1 : NF (A * P1) (-10) [0, 2232, 0, 0, 2592899910, 0, 0, 12756069900288, 0, 0, 9529320691013868, 0, 0] := (nf_A.mul nf_P1).congr (by decide)
theorem nf_P1sq : NF (P1 * P1) (-2) [0, 0, 4981824, 0, 0, 11574705198240, 0, 0, 6780073039312893732, 0, 0, 66192963880378201300800, 0] := (nf_P1.mul nf_P1).congr (by decide)
theorem nf_P1cu : NF (P1 * P1 * P1) (-3) [0, 0, 0, 11119431168, 0, 0, 38752113003707520, 0, 0, 45208723585714339333536, 0, 0, 17875488690791322993533989080] := (nf_P1sq.mul nf_P1).congr (by decide)
theorem nf_P1P2 : NF (P1 * P2) (-3) [0, 0, 0, 6343147584, 0, 0, 72923470071404112, 0, 0, 87941868979810282802064, 0, 0, 14179444150710601565903355588] := (nf_P1.mul nf_P2).congr (by decide)
theorem nf_AP1sq : NF (A * (P1 * P1)) (-11) [0, 0, 4981824, 0, 0, 11574705198240, 0, 0, 6780073039312893732, 0, 0, 66192963880381907777856, 0] := (nf_A.mul nf_P1sq).congr (by decide)
theorem nf_AP2 : NF (A * P2) (-11) [0, 0, 2841912, 0, 0, 29370374866656, 0, 0, 5264863352719180614, 0, 0, 68773656359856591116928, 0] := (nf_A.mul nf_P2).congr (by decide)
theorem nf_AP1cu : NF (A * (P1 * P1 * P1)) (-12) [0, 0, 0, 11119431168, 0, 0, 38752113003707520, 0, 0, 45208723585714339333536, 0, 0, 17875488690791331266390778072] := (nf_A.mul nf_P1cu).congr (by decide)
theorem nf_AP1P2 : NF (A * (P1 * P2)) (-12) [0, 0, 0, 6343147584, 0, 0, 72923470071404112, 0, 0, 87941868979810282802064, 0, 0, 14179444150710606285205158084] := (nf_A.mul nf_P1P2).congr (by decide)
theorem nf_AP3 : NF (A * P3) (-12) [3, 0, 0, 4065606720, 0, 0, 91368349954922664, 0, 0, 114876741665746121691912, 0, 0, 12335564478709172629894521330] := (nf_A.mul nf_P3).congr (by decide)
theorem nf_Q2 : NF (Q * Q) (-6) [1, 0, 0, 1488, 0, 0, 947304, 0, 0, 335950912, 0, 0, 72474624276] := (nf_Q.mul nf_Q).congr (by decide)
theorem nf_Q3 : NF (Q * Q * Q) (-9) [1, 0, 0, 2232, 0, 0, 2251260, 0, 0, 1355202240, 0, 0, 541778118390] := (nf_Q2.mul nf_Q).congr (by decide)
theorem nf_Q4 : NF (Q * Q * Q * Q) (-12) [1, 0, 0, 2976, 0, 0, 4108752, 0, 0, 3491078528, 0, 0, 2042124031080] := (nf_Q3.mul nf_Q).congr (by decide)

end PhiThreeCalc
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve.PhiThreeCalc"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve.PhiThreeCalc P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum jNumQ jq ofPowerSeries_coeff_of_neg dedekindPsi evalAtJ ModularPolynomialData ModularPolynomialData.Φ qTwist qTwist_coeff qTwist_one_apply jqModC phiThreeC3 phiThreeC2 phiThreeC1 phiThreeC0 phiThree laurentMap laurentMap_coeff laurentMap_single laurentMap_ofPowerSeries coeff_jNum_le_twelve eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero ModularPolynomialData.natDegree_coeff_le PhiGen.splits_prime_of_isPrimitiveRoot"
p2m_open "ModularCurve"
namespace PhiThreeCalc

theorem eval₂_qExpand_three (P : Polynomial ℤ) :
    Polynomial.eval₂ (Int.castRingHom (LaurentSeries K3)) Q P
      = ModularCurve.qExpand K3 3 (Polynomial.eval₂ (Int.castRingHom (LaurentSeries K3)) J P) := by
  have : (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K3)) Q)
      = (ModularCurve.qExpand K3 3).comp (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K3)) J) := by
    refine Polynomial.ringHom_ext (fun z => by simp) ?_
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    rfl
  exact congrArg (fun f => f P) (congrArg DFunLike.coe this)

theorem quartic_expand (a b0 b1 b2 : LaurentSeries K3) :
    (Polynomial.X - Polynomial.C a) * ((Polynomial.X - Polynomial.C b0) * (Polynomial.X - Polynomial.C b1) * (Polynomial.X - Polynomial.C b2))
      = Polynomial.X ^ 4 - Polynomial.C (a + (b0 + b1 + b2)) * Polynomial.X ^ 3
        + Polynomial.C (a * (b0 + b1 + b2) + (b0 * b1 + b0 * b2 + b1 * b2)) * Polynomial.X ^ 2
        - Polynomial.C (a * (b0 * b1 + b0 * b2 + b1 * b2) + b0 * b1 * b2) * Polynomial.X
        + Polynomial.C (a * (b0 * b1 * b2)) := by
  simp only [map_add, map_mul]
  ring

local notation:max "evalK " P:max => Polynomial.eval₂ (Int.castRingHom (LaurentSeries K3)) J P

theorem quartic_coeffs (a s e2 e3 : LaurentSeries K3) :
    (Polynomial.X ^ 4 - Polynomial.C (a + s) * Polynomial.X ^ 3 + Polynomial.C (a * s + e2) * Polynomial.X ^ 2
        - Polynomial.C (a * e2 + e3) * Polynomial.X + Polynomial.C (a * e3)).coeff 3 = -(a + s) ∧
    (Polynomial.X ^ 4 - Polynomial.C (a + s) * Polynomial.X ^ 3 + Polynomial.C (a * s + e2) * Polynomial.X ^ 2
        - Polynomial.C (a * e2 + e3) * Polynomial.X + Polynomial.C (a * e3)).coeff 2 = a * s + e2 ∧
    (Polynomial.X ^ 4 - Polynomial.C (a + s) * Polynomial.X ^ 3 + Polynomial.C (a * s + e2) * Polynomial.X ^ 2
        - Polynomial.C (a * e2 + e3) * Polynomial.X + Polynomial.C (a * e3)).coeff 1 = -(a * e2 + e3) ∧
    (Polynomial.X ^ 4 - Polynomial.C (a + s) * Polynomial.X ^ 3 + Polynomial.C (a * s + e2) * Polynomial.X ^ 2
        - Polynomial.C (a * e2 + e3) * Polynomial.X + Polynomial.C (a * e3)).coeff 0 = a * e3 := by
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_X_pow, Polynomial.coeff_C]
  norm_num
local notation:max "Φq " d:max k:max => ModularCurve.qExpand K3 3 (Polynomial.eval₂ (Int.castRingHom (LaurentSeries K3)) J (Polynomial.coeff (ModularPolynomialData.Φ d) k))

theorem coeff_identities (data : ModularPolynomialData 3) :
    Φq data 3 = -(A + P1) ∧
    2 * Φq data 2 = 2 * (A * P1) + P1 * P1 - P2 ∧
    6 * Φq data 1 = -(3 * (A * (P1 * P1)) - 3 * (A * P2) + P1 * P1 * P1 - 3 * (P1 * P2) + 2 * P3) ∧
    6 * Φq data 0 = A * (P1 * P1 * P1) - 3 * (A * (P1 * P2)) + 2 * (A * P3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := ModularCurve.PhiGen.splits_prime_of_isPrimitiveRoot (K := K3) 3 ζu hζu data
  have e9 : ModularCurve.qExpand K3 (3 * 3) J = A := rfl
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    pow_zero, qTwist_one_apply, pow_one, e9, quartic_expand] at h
  have hc : ∀ k, Φq data k
      = (Polynomial.X ^ 4 - Polynomial.C (A + (J + qTwist ζu J + qTwist (ζu ^ 2) J)) * Polynomial.X ^ 3
        + Polynomial.C (A * (J + qTwist ζu J + qTwist (ζu ^ 2) J)
            + (J * qTwist ζu J + J * qTwist (ζu ^ 2) J + qTwist ζu J * qTwist (ζu ^ 2) J)) * Polynomial.X ^ 2
        - Polynomial.C (A * (J * qTwist ζu J + J * qTwist (ζu ^ 2) J + qTwist ζu J * qTwist (ζu ^ 2) J)
            + J * qTwist ζu J * qTwist (ζu ^ 2) J) * Polynomial.X
        + Polynomial.C (A * (J * qTwist ζu J * qTwist (ζu ^ 2) J))).coeff k := by
    intro k
    rw [← h, Polynomial.coeff_map, Polynomial.coe_eval₂RingHom, show ModularCurve.qExpand K3 3 (jqModC K3) = Q from rfl,
      eval₂_qExpand_three]
  have hq := quartic_coeffs A (J + qTwist ζu J + qTwist (ζu ^ 2) J)
    (J * qTwist ζu J + J * qTwist (ζu ^ 2) J + qTwist ζu J * qTwist (ζu ^ 2) J) (J * qTwist ζu J * qTwist (ζu ^ 2) J)
  obtain ⟨c3, c2, c1, c0⟩ := hq
  have hP1 : P1 = J + qTwist ζu J + qTwist (ζu ^ 2) J := by
    rw [P1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, qTwist_one_apply, pow_one]
  have hP2 : P2 = J ^ 2 + qTwist ζu J ^ 2 + qTwist (ζu ^ 2) J ^ 2 := by
    rw [P2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, qTwist_one_apply, pow_one, map_pow, map_pow]
  have hP3 : P3 = J ^ 3 + qTwist ζu J ^ 3 + qTwist (ζu ^ 2) J ^ 3 := by
    rw [P3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, qTwist_one_apply, pow_one, map_pow, map_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc 3, c3, hP1]
  · rw [hc 2, c2, hP1, hP2]; ring
  · rw [hc 1, c1, hP1, hP2, hP3]; ring
  · rw [hc 0, c0, hP1, hP2, hP3]; ring

theorem phiThree_coeff :
    phiThree.coeff 0 = phiThreeC0 ∧ phiThree.coeff 1 = phiThreeC1 ∧ phiThree.coeff 2 = phiThreeC2 ∧
      phiThree.coeff 3 = phiThreeC3 ∧ phiThree.coeff 4 = 1 ∧ ∀ n, 5 ≤ n → phiThree.coeff n = 0 := by
  have hdeg : phiThree.natDegree ≤ 4 := by unfold phiThree; compute_degree!
  refine ⟨?_, ?_, ?_, ?_, ?_, fun n hn => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)⟩ <;>
    simp [phiThree, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]

theorem natDegree_phiThreeC :
    phiThreeC0.natDegree ≤ 4 ∧ phiThreeC1.natDegree ≤ 4 ∧ phiThreeC2.natDegree ≤ 4 ∧ phiThreeC3.natDegree ≤ 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold phiThreeC0; compute_degree!
  · unfold phiThreeC1; compute_degree!
  · unfold phiThreeC2; compute_degree!
  · unfold phiThreeC3; compute_degree!

theorem qExpand_evalK_phiThreeC :
    ModularCurve.qExpand K3 3 (evalK phiThreeC3)
      = -(Q * Q * Q) + HahnSeries.C (2232 : K3) * (Q * Q) - HahnSeries.C (1069956 : K3) * Q + HahnSeries.C (36864000 : K3) ∧
    ModularCurve.qExpand K3 3 (evalK phiThreeC2)
      = HahnSeries.C (2232 : K3) * (Q * Q * Q) + HahnSeries.C (2587918086 : K3) * (Q * Q)
        + HahnSeries.C (8900222976000 : K3) * Q + HahnSeries.C (452984832000000 : K3) ∧
    ModularCurve.qExpand K3 3 (evalK phiThreeC1)
      = -(HahnSeries.C (1069956 : K3) * (Q * Q * Q)) + HahnSeries.C (8900222976000 : K3) * (Q * Q)
        - HahnSeries.C (770845966336000000 : K3) * Q + HahnSeries.C (1855425871872000000000 : K3) ∧
    ModularCurve.qExpand K3 3 (evalK phiThreeC0)
      = Q * Q * Q * Q + HahnSeries.C (36864000 : K3) * (Q * Q * Q) + HahnSeries.C (452984832000000 : K3) * (Q * Q)
        + HahnSeries.C (1855425871872000000000 : K3) * Q := by
  simp only [map_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [← eval₂_qExpand_three]
    simp only [phiThreeC3, phiThreeC2, phiThreeC1, phiThreeC0, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_neg]
    ring

theorem coeff_C_mul' (r : K3) (x : LaurentSeries K3) (m : ℤ) : (HahnSeries.C r * x).coeff m = r * x.coeff m := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem coeff_C' (r : K3) (m : ℤ) : (HahnSeries.C r : LaurentSeries K3).coeff m = if m = 0 then r else 0 := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem coeff_natCast_mul (n : ℕ) (x : LaurentSeries K3) (m : ℤ) :
    ((n : LaurentSeries K3) * x).coeff m = (n : K3) * x.coeff m := by
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := K3)) n, coeff_C_mul']

theorem coeff_two_mul (x : LaurentSeries K3) (m : ℤ) : ((2 : LaurentSeries K3) * x).coeff m = 2 * x.coeff m := by
  rw [show (2 : LaurentSeries K3) = ((2 : ℕ) : LaurentSeries K3) by norm_num, coeff_natCast_mul]; norm_num
theorem coeff_three_mul (x : LaurentSeries K3) (m : ℤ) : ((3 : LaurentSeries K3) * x).coeff m = 3 * x.coeff m := by
  rw [show (3 : LaurentSeries K3) = ((3 : ℕ) : LaurentSeries K3) by norm_num, coeff_natCast_mul]; norm_num
theorem coeff_six_mul (x : LaurentSeries K3) (m : ℤ) : ((6 : LaurentSeries K3) * x).coeff m = 6 * x.coeff m := by
  rw [show (6 : LaurentSeries K3) = ((6 : ℕ) : LaurentSeries K3) by norm_num, coeff_natCast_mul]; norm_num

theorem coeff_ofNat_mul (n : ℕ) [n.AtLeastTwo] (x : LaurentSeries K3) (m : ℤ) :
    ((OfNat.ofNat n : LaurentSeries K3) * x).coeff m = (OfNat.ofNat n : K3) * x.coeff m := by
  rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := K3)) n, coeff_C_mul']

theorem coeff_eq_coeff_qExpand_three (f : LaurentSeries K3) (m : ℤ) : f.coeff m = (ModularCurve.qExpand K3 3 f).coeff (3 * m) := by
  have h := qExpand_coeff_mul (R := K3) 3 f m
  rw [Nat.cast_ofNat] at h
  exact h.symm

theorem map_jNumQ : PowerSeries.map (algebraMap ℚ K3) jNumQ = PowerSeries.map (Int.castRingHom K3) jNum := by
  ext n
  simp only [jNumQ, PowerSeries.coeff_map, eq_intCast, map_intCast]

theorem laurentMap_jq : laurentMap (algebraMap ℚ K3) jq = J := by
  rw [show jq = HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.ofPowerSeries ℤ ℚ jNumQ from rfl, map_mul, laurentMap_single,
    laurentMap_ofPowerSeries, map_one, map_jNumQ]
  rfl

theorem laurentMap_evalAtJ (P : Polynomial ℤ) : laurentMap (algebraMap ℚ K3) (evalAtJ P) = evalK P := by
  rw [show evalAtJ P = Polynomial.eval₂ (algebraMap ℤ (LaurentSeries ℚ)) jq P from Polynomial.aeval_def jq P,
    Polynomial.hom_eval₂, laurentMap_jq]
  congr 1
  exact RingHom.ext_int _ _

set_option maxHeartbeats 6400000 in
theorem ModularPolynomialData.phi_eq_phiThree' (data : ModularPolynomialData 3) : data.Φ = phiThree := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h3, h2, h1, h0⟩ := coeff_identities data
  obtain ⟨p0, p1, p2, p3, p4, pge⟩ := phiThree_coeff
  obtain ⟨e3, e2, e1, e0⟩ := qExpand_evalK_phiThreeC
  obtain ⟨d0, d1, d2, d3⟩ := natDegree_phiThreeC
  have hdeg4 : data.Φ.natDegree = 4 := by
    rw [data.natDegree_eq, dedekindPsi, Nat.prime_three.divisors, Finset.filter_insert, if_pos squarefree_one,
      Finset.filter_singleton, if_pos Nat.prime_three.squarefree, Finset.sum_insert (by simp), Finset.sum_singleton]
  have cA_m12 := nf_A.coeff (-12) (by decide)
  have cA_m9 := nf_A.coeff (-9) (by decide)
  have cA_m6 := nf_A.coeff (-6) (by decide)
  have cA_m3 := nf_A.coeff (-3) (by decide)
  have cA_0 := nf_A.coeff (0) (by decide)
  have cP1_m12 := nf_P1.coeff (-12) (by decide)
  have cP1_m9 := nf_P1.coeff (-9) (by decide)
  have cP1_m6 := nf_P1.coeff (-6) (by decide)
  have cP1_m3 := nf_P1.coeff (-3) (by decide)
  have cP1_0 := nf_P1.coeff (0) (by decide)
  have cP2_m12 := nf_P2.coeff (-12) (by decide)
  have cP2_m9 := nf_P2.coeff (-9) (by decide)
  have cP2_m6 := nf_P2.coeff (-6) (by decide)
  have cP2_m3 := nf_P2.coeff (-3) (by decide)
  have cP2_0 := nf_P2.coeff (0) (by decide)
  have cP3_m12 := nf_P3.coeff (-12) (by decide)
  have cP3_m9 := nf_P3.coeff (-9) (by decide)
  have cP3_m6 := nf_P3.coeff (-6) (by decide)
  have cP3_m3 := nf_P3.coeff (-3) (by decide)
  have cP3_0 := nf_P3.coeff (0) (by decide)
  have cAP1_m12 := nf_AP1.coeff (-12) (by decide)
  have cAP1_m9 := nf_AP1.coeff (-9) (by decide)
  have cAP1_m6 := nf_AP1.coeff (-6) (by decide)
  have cAP1_m3 := nf_AP1.coeff (-3) (by decide)
  have cAP1_0 := nf_AP1.coeff (0) (by decide)
  have cP1sq_m12 := nf_P1sq.coeff (-12) (by decide)
  have cP1sq_m9 := nf_P1sq.coeff (-9) (by decide)
  have cP1sq_m6 := nf_P1sq.coeff (-6) (by decide)
  have cP1sq_m3 := nf_P1sq.coeff (-3) (by decide)
  have cP1sq_0 := nf_P1sq.coeff (0) (by decide)
  have cP1cu_m12 := nf_P1cu.coeff (-12) (by decide)
  have cP1cu_m9 := nf_P1cu.coeff (-9) (by decide)
  have cP1cu_m6 := nf_P1cu.coeff (-6) (by decide)
  have cP1cu_m3 := nf_P1cu.coeff (-3) (by decide)
  have cP1cu_0 := nf_P1cu.coeff (0) (by decide)
  have cP1P2_m12 := nf_P1P2.coeff (-12) (by decide)
  have cP1P2_m9 := nf_P1P2.coeff (-9) (by decide)
  have cP1P2_m6 := nf_P1P2.coeff (-6) (by decide)
  have cP1P2_m3 := nf_P1P2.coeff (-3) (by decide)
  have cP1P2_0 := nf_P1P2.coeff (0) (by decide)
  have cAP1sq_m12 := nf_AP1sq.coeff (-12) (by decide)
  have cAP1sq_m9 := nf_AP1sq.coeff (-9) (by decide)
  have cAP1sq_m6 := nf_AP1sq.coeff (-6) (by decide)
  have cAP1sq_m3 := nf_AP1sq.coeff (-3) (by decide)
  have cAP1sq_0 := nf_AP1sq.coeff (0) (by decide)
  have cAP2_m12 := nf_AP2.coeff (-12) (by decide)
  have cAP2_m9 := nf_AP2.coeff (-9) (by decide)
  have cAP2_m6 := nf_AP2.coeff (-6) (by decide)
  have cAP2_m3 := nf_AP2.coeff (-3) (by decide)
  have cAP2_0 := nf_AP2.coeff (0) (by decide)
  have cAP1cu_m12 := nf_AP1cu.coeff (-12) (by decide)
  have cAP1cu_m9 := nf_AP1cu.coeff (-9) (by decide)
  have cAP1cu_m6 := nf_AP1cu.coeff (-6) (by decide)
  have cAP1cu_m3 := nf_AP1cu.coeff (-3) (by decide)
  have cAP1cu_0 := nf_AP1cu.coeff (0) (by decide)
  have cAP1P2_m12 := nf_AP1P2.coeff (-12) (by decide)
  have cAP1P2_m9 := nf_AP1P2.coeff (-9) (by decide)
  have cAP1P2_m6 := nf_AP1P2.coeff (-6) (by decide)
  have cAP1P2_m3 := nf_AP1P2.coeff (-3) (by decide)
  have cAP1P2_0 := nf_AP1P2.coeff (0) (by decide)
  have cAP3_m12 := nf_AP3.coeff (-12) (by decide)
  have cAP3_m9 := nf_AP3.coeff (-9) (by decide)
  have cAP3_m6 := nf_AP3.coeff (-6) (by decide)
  have cAP3_m3 := nf_AP3.coeff (-3) (by decide)
  have cAP3_0 := nf_AP3.coeff (0) (by decide)
  have cQ_m12 := nf_Q.coeff (-12) (by decide)
  have cQ_m9 := nf_Q.coeff (-9) (by decide)
  have cQ_m6 := nf_Q.coeff (-6) (by decide)
  have cQ_m3 := nf_Q.coeff (-3) (by decide)
  have cQ_0 := nf_Q.coeff (0) (by decide)
  have cQ2_m12 := nf_Q2.coeff (-12) (by decide)
  have cQ2_m9 := nf_Q2.coeff (-9) (by decide)
  have cQ2_m6 := nf_Q2.coeff (-6) (by decide)
  have cQ2_m3 := nf_Q2.coeff (-3) (by decide)
  have cQ2_0 := nf_Q2.coeff (0) (by decide)
  have cQ3_m12 := nf_Q3.coeff (-12) (by decide)
  have cQ3_m9 := nf_Q3.coeff (-9) (by decide)
  have cQ3_m6 := nf_Q3.coeff (-6) (by decide)
  have cQ3_m3 := nf_Q3.coeff (-3) (by decide)
  have cQ3_0 := nf_Q3.coeff (0) (by decide)
  have cQ4_m12 := nf_Q4.coeff (-12) (by decide)
  have cQ4_m9 := nf_Q4.coeff (-9) (by decide)
  have cQ4_m6 := nf_Q4.coeff (-6) (by decide)
  have cQ4_m3 := nf_Q4.coeff (-3) (by decide)
  have cQ4_0 := nf_Q4.coeff (0) (by decide)
  apply Polynomial.ext
  intro k
  rcases Nat.lt_or_ge k 4 with hk | hk
  ·
    rw [← sub_eq_zero]
    apply ModularCurve.eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero _ 4
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (ModularPolynomialData.natDegree_coeff_le 3 data k).trans (by norm_num)
      · interval_cases k
        · rw [p0]; exact d0
        · rw [p1]; exact d1
        · rw [p2]; exact d2
        · rw [p3]; exact d3
    · intro m hm1 hm2

      rw [← (map_eq_zero_iff (algebraMap ℚ K3) (algebraMap ℚ K3).injective), ← laurentMap_coeff, laurentMap_evalAtJ,
        Polynomial.eval₂_sub, HahnSeries.coeff_sub, coeff_eq_coeff_qExpand_three, coeff_eq_coeff_qExpand_three (evalK _), sub_eq_zero]
      have hm1' : -4 ≤ m := by omega
      interval_cases k
      · rw [p0, e0]
        refine mul_left_cancel₀ (show (6 : K3) ≠ 0 by norm_num) ?_
        rw [← coeff_six_mul, h0]
        interval_cases m <;>
        · simp only [Int.reduceMul, Int.reduceNeg, Int.reduceAdd, Int.reduceSub, Int.reduceToNat, Int.reduceLE,
            HahnSeries.coeff_neg, HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_C_mul', coeff_C', coeff_two_mul, coeff_three_mul, coeff_six_mul,
            cA_m12, cA_m9, cA_m6, cA_m3, cA_0, cP1_m12, cP1_m9, cP1_m6, cP1_m3, cP1_0, cP2_m12, cP2_m9, cP2_m6, cP2_m3, cP2_0, cP3_m12, cP3_m9, cP3_m6, cP3_m3, cP3_0, cAP1_m12, cAP1_m9, cAP1_m6, cAP1_m3, cAP1_0, cP1sq_m12, cP1sq_m9, cP1sq_m6, cP1sq_m3, cP1sq_0, cP1cu_m12, cP1cu_m9, cP1cu_m6, cP1cu_m3, cP1cu_0, cP1P2_m12, cP1P2_m9, cP1P2_m6, cP1P2_m3, cP1P2_0, cAP1sq_m12, cAP1sq_m9, cAP1sq_m6, cAP1sq_m3, cAP1sq_0, cAP2_m12, cAP2_m9, cAP2_m6, cAP2_m3, cAP2_0, cAP1cu_m12, cAP1cu_m9, cAP1cu_m6, cAP1cu_m3, cAP1cu_0, cAP1P2_m12, cAP1P2_m9, cAP1P2_m6, cAP1P2_m3, cAP1P2_0, cAP3_m12, cAP3_m9, cAP3_m6, cAP3_m3, cAP3_0, cQ_m12, cQ_m9, cQ_m6, cQ_m3, cQ_0, cQ2_m12, cQ2_m9, cQ2_m6, cQ2_m3, cQ2_0, cQ3_m12, cQ3_m9, cQ3_m6, cQ3_m3, cQ3_0, cQ4_m12, cQ4_m9, cQ4_m6, cQ4_m3, cQ4_0]
          norm_num [Int.reduceToNat, Int.reduceSub, Int.reduceNeg]
      · rw [p1, e1]
        refine mul_left_cancel₀ (show (6 : K3) ≠ 0 by norm_num) ?_
        rw [← coeff_six_mul, h1]
        interval_cases m <;>
        · simp only [Int.reduceMul, Int.reduceNeg, Int.reduceAdd, Int.reduceSub, Int.reduceToNat, Int.reduceLE,
            HahnSeries.coeff_neg, HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_C_mul', coeff_C', coeff_two_mul, coeff_three_mul, coeff_six_mul,
            cA_m12, cA_m9, cA_m6, cA_m3, cA_0, cP1_m12, cP1_m9, cP1_m6, cP1_m3, cP1_0, cP2_m12, cP2_m9, cP2_m6, cP2_m3, cP2_0, cP3_m12, cP3_m9, cP3_m6, cP3_m3, cP3_0, cAP1_m12, cAP1_m9, cAP1_m6, cAP1_m3, cAP1_0, cP1sq_m12, cP1sq_m9, cP1sq_m6, cP1sq_m3, cP1sq_0, cP1cu_m12, cP1cu_m9, cP1cu_m6, cP1cu_m3, cP1cu_0, cP1P2_m12, cP1P2_m9, cP1P2_m6, cP1P2_m3, cP1P2_0, cAP1sq_m12, cAP1sq_m9, cAP1sq_m6, cAP1sq_m3, cAP1sq_0, cAP2_m12, cAP2_m9, cAP2_m6, cAP2_m3, cAP2_0, cAP1cu_m12, cAP1cu_m9, cAP1cu_m6, cAP1cu_m3, cAP1cu_0, cAP1P2_m12, cAP1P2_m9, cAP1P2_m6, cAP1P2_m3, cAP1P2_0, cAP3_m12, cAP3_m9, cAP3_m6, cAP3_m3, cAP3_0, cQ_m12, cQ_m9, cQ_m6, cQ_m3, cQ_0, cQ2_m12, cQ2_m9, cQ2_m6, cQ2_m3, cQ2_0, cQ3_m12, cQ3_m9, cQ3_m6, cQ3_m3, cQ3_0, cQ4_m12, cQ4_m9, cQ4_m6, cQ4_m3, cQ4_0]
          norm_num [Int.reduceToNat, Int.reduceSub, Int.reduceNeg]
      · rw [p2, e2]
        refine mul_left_cancel₀ (show (2 : K3) ≠ 0 by norm_num) ?_
        rw [← coeff_two_mul, h2]
        interval_cases m <;>
        · simp only [Int.reduceMul, Int.reduceNeg, Int.reduceAdd, Int.reduceSub, Int.reduceToNat, Int.reduceLE,
            HahnSeries.coeff_neg, HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_C_mul', coeff_C', coeff_two_mul, coeff_three_mul, coeff_six_mul,
            cA_m12, cA_m9, cA_m6, cA_m3, cA_0, cP1_m12, cP1_m9, cP1_m6, cP1_m3, cP1_0, cP2_m12, cP2_m9, cP2_m6, cP2_m3, cP2_0, cP3_m12, cP3_m9, cP3_m6, cP3_m3, cP3_0, cAP1_m12, cAP1_m9, cAP1_m6, cAP1_m3, cAP1_0, cP1sq_m12, cP1sq_m9, cP1sq_m6, cP1sq_m3, cP1sq_0, cP1cu_m12, cP1cu_m9, cP1cu_m6, cP1cu_m3, cP1cu_0, cP1P2_m12, cP1P2_m9, cP1P2_m6, cP1P2_m3, cP1P2_0, cAP1sq_m12, cAP1sq_m9, cAP1sq_m6, cAP1sq_m3, cAP1sq_0, cAP2_m12, cAP2_m9, cAP2_m6, cAP2_m3, cAP2_0, cAP1cu_m12, cAP1cu_m9, cAP1cu_m6, cAP1cu_m3, cAP1cu_0, cAP1P2_m12, cAP1P2_m9, cAP1P2_m6, cAP1P2_m3, cAP1P2_0, cAP3_m12, cAP3_m9, cAP3_m6, cAP3_m3, cAP3_0, cQ_m12, cQ_m9, cQ_m6, cQ_m3, cQ_0, cQ2_m12, cQ2_m9, cQ2_m6, cQ2_m3, cQ2_0, cQ3_m12, cQ3_m9, cQ3_m6, cQ3_m3, cQ3_0, cQ4_m12, cQ4_m9, cQ4_m6, cQ4_m3, cQ4_0]
          norm_num [Int.reduceToNat, Int.reduceSub, Int.reduceNeg]
      · rw [p3, e3, show ModularCurve.qExpand K3 3 (evalK (data.Φ.coeff 3)) = Φq data 3 from rfl, h3]
        interval_cases m <;>
        · simp only [Int.reduceMul, Int.reduceNeg, Int.reduceAdd, Int.reduceSub, Int.reduceToNat, Int.reduceLE,
            HahnSeries.coeff_neg, HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_C_mul', coeff_C', coeff_two_mul, coeff_three_mul, coeff_six_mul,
            cA_m12, cA_m9, cA_m6, cA_m3, cA_0, cP1_m12, cP1_m9, cP1_m6, cP1_m3, cP1_0, cP2_m12, cP2_m9, cP2_m6, cP2_m3, cP2_0, cP3_m12, cP3_m9, cP3_m6, cP3_m3, cP3_0, cAP1_m12, cAP1_m9, cAP1_m6, cAP1_m3, cAP1_0, cP1sq_m12, cP1sq_m9, cP1sq_m6, cP1sq_m3, cP1sq_0, cP1cu_m12, cP1cu_m9, cP1cu_m6, cP1cu_m3, cP1cu_0, cP1P2_m12, cP1P2_m9, cP1P2_m6, cP1P2_m3, cP1P2_0, cAP1sq_m12, cAP1sq_m9, cAP1sq_m6, cAP1sq_m3, cAP1sq_0, cAP2_m12, cAP2_m9, cAP2_m6, cAP2_m3, cAP2_0, cAP1cu_m12, cAP1cu_m9, cAP1cu_m6, cAP1cu_m3, cAP1cu_0, cAP1P2_m12, cAP1P2_m9, cAP1P2_m6, cAP1P2_m3, cAP1P2_0, cAP3_m12, cAP3_m9, cAP3_m6, cAP3_m3, cAP3_0, cQ_m12, cQ_m9, cQ_m6, cQ_m3, cQ_0, cQ2_m12, cQ2_m9, cQ2_m6, cQ2_m3, cQ2_0, cQ3_m12, cQ3_m9, cQ3_m6, cQ3_m3, cQ3_0, cQ4_m12, cQ4_m9, cQ4_m6, cQ4_m3, cQ4_0]
          norm_num [Int.reduceToNat, Int.reduceSub, Int.reduceNeg]
  ·
    rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · have : k = 4 := by omega
      subst this
      rw [p4]
      have := data.monic
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg4] at this
      exact this
    · rw [pge k hk5, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg4]; omega)]

end PhiThreeCalc
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve.PhiThreeCalc P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve.PhiThreeCalc P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree.ModularCurve Polynomial"

theorem solution (data : ModularPolynomialData 3) : data.Φ = phiThree :=
  ModularCurve.PhiThreeCalc.ModularPolynomialData.phi_eq_phiThree' data

end S_ModularCurve_ModularPolynomialData_phi_eq_phiThree
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree (solution)
