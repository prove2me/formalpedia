-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.evalSymm_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ca3166e2-6023-5f05-a18e-337fba1a2583

import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import Theorems.Thm_ModularCurve_phiIrreducible_all
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible
import Theorems.Thm_ModularCurve_swapBivar_monic_of_coeff_bounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen Polynomial

namespace Aux1LevelSymm

section PoleToolkit

variable {K : Type*} [Field K]

theorem tp_mono {f : LaurentSeries K} {m n : ℕ} (hf : TPoleOrderLE f m) (hmn : m ≤ n) : TPoleOrderLE f n :=
  fun k hk => hf k (by omega)

theorem tp_zero (n : ℕ) : TPoleOrderLE (0 : LaurentSeries K) n := fun _ _ => rfl

theorem tp_one : TPoleOrderLE (1 : LaurentSeries K) 0 := by
  intro m hm
  rw [HahnSeries.coeff_one, if_neg (by omega)]

theorem tp_neg {f : LaurentSeries K} {n : ℕ} (hf : TPoleOrderLE f n) : TPoleOrderLE (-f) n := by
  intro m hm
  rw [HahnSeries.coeff_neg, hf m hm, neg_zero]

theorem tp_add {f g : LaurentSeries K} {n : ℕ} (hf : TPoleOrderLE f n) (hg : TPoleOrderLE g n) :
    TPoleOrderLE (f + g) n := by
  intro m hm
  rw [HahnSeries.coeff_add, hf m hm, hg m hm, add_zero]

theorem tp_mul {f g : LaurentSeries K} {m n : ℕ} (hf : TPoleOrderLE f m) (hg : TPoleOrderLE g n) :
    TPoleOrderLE (f * g) (m + n) := by
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 < -(m : ℤ)
  · rw [hf ij.1 hi, zero_mul]
  · refine mul_eq_zero_of_right _ (hg ij.2 ?_)
    push_cast at hk
    omega

theorem tp_prod {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (n : ι → ℕ)
    (hf : ∀ i ∈ s, TPoleOrderLE (f i) (n i)) : TPoleOrderLE (∏ i ∈ s, f i) (∑ i ∈ s, n i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using tp_one
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact tp_mul (hf a (Finset.mem_cons_self a s)) (ih fun i hi => hf i (Finset.mem_cons_of_mem hi))

theorem coeff_mul_lead {f g : LaurentSeries K} {m n : ℕ} (hf : TPoleOrderLE f m) (hg : TPoleOrderLE g n) :
    (f * g).coeff (-((m + n : ℕ) : ℤ)) = f.coeff (-(m : ℤ)) * g.coeff (-(n : ℤ)) := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_single ((-(m : ℤ), -(n : ℤ))) ?_ ?_
  · rintro ⟨i, j⟩ hij hne
    obtain ⟨hi, hj, hsum⟩ := Finset.mem_antidiagonal.mp hij
    rw [HahnSeries.mem_support] at hi hj
    have him : ¬ i < -(m : ℤ) := fun h => hi (hf i h)
    have hjn : ¬ j < -(n : ℤ) := fun h => hj (hg j h)
    push_cast at hsum
    have hi' : i = -(m : ℤ) := by omega
    have hj' : j = -(n : ℤ) := by omega
    exact absurd (by rw [hi', hj']) hne
  · intro hni
    by_contra hne
    refine hni (Finset.mem_antidiagonal.mpr ⟨?_, ?_, by push_cast; ring⟩) <;> rw [HahnSeries.mem_support]
    · exact fun h0 => hne (by rw [h0, zero_mul])
    · exact fun h0 => hne (by rw [h0, mul_zero])

theorem coeff_prod_lead {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (n : ι → ℕ)
    (hf : ∀ i ∈ s, TPoleOrderLE (f i) (n i)) :
    (∏ i ∈ s, f i).coeff (-((∑ i ∈ s, n i : ℕ) : ℤ)) = ∏ i ∈ s, (f i).coeff (-(n i : ℤ)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, Finset.prod_cons,
      coeff_mul_lead (hf a (Finset.mem_cons_self a s)) (tp_prod s f n fun i hi => hf i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_cons_of_mem hi)]

theorem tp_coeff_X_sub_C {a : LaurentSeries K} {n : ℕ} (ha : TPoleOrderLE a n) (k : ℕ) :
    TPoleOrderLE ((X - C a).coeff k) n := by
  match k with
  | 0 =>
    simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
    exact tp_neg ha
  | 1 =>
    simp only [coeff_sub, coeff_X_one, coeff_C, if_neg (one_ne_zero), sub_zero]
    exact tp_mono tp_one (Nat.zero_le _)
  | (k + 2) =>
    simp only [coeff_sub, coeff_X, coeff_C]
    rw [if_neg (by omega), if_neg (by omega), sub_zero]
    exact tp_zero _

theorem tp_coeff_prod_X_sub_C {ι : Type*} (s : Finset ι) (a : ι → LaurentSeries K) (n : ι → ℕ)
    (ha : ∀ i ∈ s, TPoleOrderLE (a i) (n i)) (hn : ∀ i ∈ s, 1 ≤ n i) :
    ∀ k : ℕ, TPoleOrderLE ((∏ i ∈ s, (X - C (a i))).coeff k) ((∑ i ∈ s, n i) - k) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using tp_one
    · rw [Finset.prod_empty, coeff_one, if_neg (by omega)]
      exact tp_zero _
  | cons a₀ s ha₀ ih =>
    intro k
    have hmem : ∀ i ∈ s, TPoleOrderLE (a i) (n i) := fun i hi => ha i (Finset.mem_cons_of_mem hi)
    have hnmem : ∀ i ∈ s, 1 ≤ n i := fun i hi => hn i (Finset.mem_cons_of_mem hi)
    have hn0 : 1 ≤ n a₀ := hn a₀ (Finset.mem_cons_self a₀ s)
    have hcard : s.card ≤ ∑ i ∈ s, n i := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum hnmem
    rw [Finset.prod_cons, Finset.sum_cons]
    match k with
    | 0 =>
      rw [mul_coeff_zero]
      exact tp_mono (tp_mul (tp_coeff_X_sub_C (ha a₀ (Finset.mem_cons_self a₀ s)) 0) (ih hmem hnmem 0)) (by omega)
    | (k + 1) =>
      rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, sub_eq_add_neg]
      refine tp_add ?_ (tp_neg ?_)
      · exact tp_mono (ih hmem hnmem k) (by omega)
      · by_cases hks : k + 1 ≤ ∑ i ∈ s, n i
        · exact tp_mono (tp_mul (ha a₀ (Finset.mem_cons_self a₀ s)) (ih hmem hnmem (k + 1))) (by omega)
        · rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
          · exact tp_zero _
          · rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
            simp only [natDegree_X_sub_C, ← Finset.card_eq_sum_ones]
            omega

theorem coeff_zero_prod_X_sub_C {ι : Type*} (s : Finset ι) (a : ι → LaurentSeries K) :
    (∏ i ∈ s, (X - C (a i))).coeff 0 = ∏ i ∈ s, (-(a i)) := by
  rw [coeff_zero_eq_eval_zero, eval_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [eval_sub, eval_X, eval_C, zero_sub]

theorem tp_qTwist {f : LaurentSeries K} {n : ℕ} (hf : TPoleOrderLE f n) (u : Kˣ) :
    TPoleOrderLE (qTwist u f) n := by
  intro m hm
  rw [qTwist_coeff, hf m hm, mul_zero]

theorem tp_qExpand {f : LaurentSeries K} {n : ℕ} (hf : TPoleOrderLE f n) (M : ℕ) [NeZero M] :
    TPoleOrderLE (qExpand K M f) (M * n) := by
  intro m hm
  by_cases hdvd : (M : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    refine hf c ?_
    have hM : 0 < (M : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    push_cast at hm
    nlinarith
  · exact qExpand_coeff_of_not_dvd M f hdvd

theorem prod_neg_pow_eq_neg_one {d : ℕ} (hd : 0 < d) {θ : K} (hθ : IsPrimitiveRoot θ d) :
    ∏ b ∈ Finset.range d, (-(θ ^ b)) = -1 := by
  rw [Finset.prod_neg, Finset.card_range, Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ b ∈ Finset.range d, b) * 2 = d * (d - 1) := Finset.sum_range_id_mul_two d
  rcases Nat.even_or_odd d with ⟨e, he⟩ | ⟨e, he⟩
  ·
    have he2 : d = e * 2 := by omega
    have hθe : θ ^ e = -1 := (hθ.pow hd he2).eq_neg_one_of_two_right
    have hs : ∑ b ∈ Finset.range d, b = e * (d - 1) := by
      have : (∑ b ∈ Finset.range d, b) * 2 = (e * (d - 1)) * 2 := by rw [hsum, he2]; ring
      omega
    have hd1 : Odd (d - 1) := ⟨e - 1, by omega⟩
    rw [hs, pow_mul, hθe, hd1.neg_one_pow, Even.neg_one_pow ⟨e, he⟩]
    ring
  ·
    have hs : ∑ b ∈ Finset.range d, b = d * e := by
      have : (∑ b ∈ Finset.range d, b) * 2 = (d * e) * 2 := by rw [hsum, show d - 1 = 2 * e by omega]; ring
      omega
    rw [hs, pow_mul, hθ.pow_eq_one, one_pow, mul_one, Odd.neg_one_pow ⟨e, he⟩]

theorem prod_neg_pow_slotFilter_eq_one {a d : ℕ} (hd : 0 < d) (hg : Nat.gcd a d ≠ 1) {θ : K}
    (hθ : IsPrimitiveRoot θ d) :
    ∏ b ∈ (Finset.range d).filter (fun b => Nat.gcd (Nat.gcd a b) d = 1), (-(θ ^ b)) = 1 := by
  have hmem : ∀ b ∈ (Finset.range d).filter (fun b => Nat.gcd (Nat.gcd a b) d = 1),
      b < d ∧ Nat.gcd (Nat.gcd a d) b = 1 := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨hb1, ?_⟩
    rwa [Nat.gcd_assoc a b d, Nat.gcd_comm b d, ← Nat.gcd_assoc a d b] at hb2
  have hne0 : ∀ b ∈ (Finset.range d).filter (fun b => Nat.gcd (Nat.gcd a b) d = 1), b ≠ 0 := by
    intro b hb hb0
    have h := (hmem b hb).2
    rw [hb0, Nat.gcd_zero_right] at h
    exact hg h
  refine Finset.prod_involution (fun b _ => d - b) (fun b hb => ?_) (fun b hb hfb => ?_) (fun b hb => ?_)
    (fun b hb => ?_)
  ·
    show -(θ ^ b) * -(θ ^ (d - b)) = 1
    rw [neg_mul_neg, ← pow_add, Nat.add_sub_cancel' (hmem b hb).1.le, hθ.pow_eq_one]
  ·
    intro h
    have h' : d - b = b := h
    apply hfb
    show -(θ ^ b) = 1
    obtain ⟨hbd, hcop⟩ := hmem b hb
    have h2b : b + b = d := by omega
    have hbb : θ ^ b * θ ^ b = 1 := by rw [← pow_add, h2b, hθ.pow_eq_one]
    rcases mul_self_eq_one_iff.mp hbb with h1 | h1
    · exfalso
      have hb0 : b = 0 := Nat.eq_zero_of_dvd_of_lt ((hθ.pow_eq_one_iff_dvd b).mp h1) hbd
      exact hne0 b hb hb0
    · rw [h1, neg_neg]
  ·
    show d - b ∈ (Finset.range d).filter (fun b => Nat.gcd (Nat.gcd a b) d = 1)
    obtain ⟨hbd, hcop⟩ := hmem b hb
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.sub_lt hd (Nat.pos_of_ne_zero (hne0 b hb)), ?_⟩
    rw [Nat.gcd_assoc a (d - b) d, Nat.gcd_comm (d - b) d, ← Nat.gcd_assoc a d (d - b)]
    apply Nat.dvd_one.mp
    rw [← hcop]
    refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
    have h1 : Nat.gcd (Nat.gcd a d) (d - b) ∣ d := Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right a d)
    have h2 : Nat.gcd (Nat.gcd a d) (d - b) ∣ d - b := Nat.gcd_dvd_right _ _
    have h3 := Nat.dvd_sub h1 h2
    rwa [Nat.sub_sub_self hbd.le] at h3
  ·
    show d - (d - b) = b
    exact Nat.sub_sub_self (hmem b hb).1.le

end PoleToolkit

section EvalAtJ

theorem evalAtJ_coeff (P : Polynomial ℤ) (m : ℤ) :
    (evalAtJ P).coeff m = ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℚ) * (jq ^ i).coeff m := by
  rw [evalAtJ_def]
  show (aeval jq P).coeff m = _
  rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eq_intCast, ← map_intCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ), HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul]

theorem tp_evalAtJ (P : Polynomial ℤ) : TPoleOrderLE (evalAtJ P) P.natDegree := by
  intro m hm
  rw [evalAtJ_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [coeff_jq_pow_of_lt (lt_of_lt_of_le hm (by omega)), mul_zero]

theorem evalAtJ_lead (P : Polynomial ℤ) : (evalAtJ P).coeff (-(P.natDegree : ℤ)) = (P.leadingCoeff : ℚ) := by
  rw [evalAtJ_coeff, Finset.sum_eq_single P.natDegree, coeff_jq_pow_self, mul_one, leadingCoeff]
  · intro i hi hne
    have hi' := Finset.mem_range.mp hi
    rw [coeff_jq_pow_of_lt (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem tp_coeffEmb {f : LaurentSeries ℚ} {n : ℕ} (hf : TPoleOrderLE f n) : TPoleOrderLE (coeffEmb K f) n := by
  intro m hm
  rw [coeffEmb_coeff, hf m hm, map_zero]

theorem tp_iota (N : ℕ) [NeZero N] (P : Polynomial ℤ) :
    TPoleOrderLE ((((coeffEmb K).comp (qExpand ℚ N)).comp evalAtJ) P) (N * P.natDegree) :=
  tp_coeffEmb (tp_qExpand (tp_evalAtJ P) N)

theorem iota_lead (N : ℕ) [NeZero N] (P : Polynomial ℤ) :
    ((((coeffEmb K).comp (qExpand ℚ N)).comp evalAtJ) P).coeff (-((N * P.natDegree : ℕ) : ℤ))
      = algebraMap ℚ K (P.leadingCoeff : ℚ) := by
  rw [RingHom.comp_apply, RingHom.comp_apply, coeffEmb_coeff,
    show (-((N * P.natDegree : ℕ) : ℤ)) = (N : ℤ) * (-(P.natDegree : ℤ)) by push_cast; ring,
    qExpand_coeff_mul, evalAtJ_lead]

end EvalAtJ

section Slots

variable {K : Type*} [Field K] [Algebra ℚ K] (ζ : Kˣ)

noncomputable def slot (a b : ℕ) : LaurentSeries K :=
  if h : a = 0 then 0 else letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))

theorem slot_of_ne {a : ℕ} (ha : a ≠ 0) (b : ℕ) :
    slot ζ a b = (letI : NeZero a := ⟨ha⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))) :=
  dif_neg ha

theorem tp_slot {a : ℕ} (ha : a ≠ 0) (b : ℕ) : TPoleOrderLE (slot ζ a b) (a * a) := by
  rw [slot_of_ne ζ ha]
  letI : NeZero a := ⟨ha⟩
  simpa using tp_qExpand (tp_qTwist (tp_coeffEmb (K := K) (f := jq) (n := 1) fun m hm => coeff_jq_of_lt (by
    push_cast at hm; exact hm)) (ζ ^ (b * a))) (a * a)

theorem slot_lead {a : ℕ} (ha : a ≠ 0) (b : ℕ) :
    (slot ζ a b).coeff (-((a * a : ℕ) : ℤ)) = (((ζ ^ (b * a))⁻¹ : Kˣ) : K) := by
  rw [slot_of_ne ζ ha]
  letI : NeZero a := ⟨ha⟩
  rw [show (-((a * a : ℕ) : ℤ)) = ((a * a : ℕ) : ℤ) * (-1 : ℤ) by ring, qExpand_coeff_mul, qTwist_coeff, coeffEmb_coeff,
    coeff_jq_neg_one, map_one, mul_one, zpow_neg_one]

theorem slot_one_zero : slot ζ 1 0 = coeffEmb K jq := by
  rw [slot_of_ne ζ one_ne_zero, zero_mul, pow_zero, qTwist_one_apply,
    qExpand_congr (show 1 * 1 = 1 by norm_num), qExpand_one_apply]

end Slots

section SlotCount

theorem card_filter_range_mul_gcd_eq_one (g m : ℕ) :
    ((Finset.range (g * m)).filter (fun b => Nat.gcd g b = 1)).card = m * Nat.totient g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_add_one, Finset.range_eq_Ico,
      ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (g * m)) (Nat.le_add_right (g * m) g), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 0 (g * m) (g * m + g))),
      ← Finset.range_eq_Ico, ih, add_one_mul]
    congr 1
    exact Nat.filter_coprime_Ico_eq_totient g (g * m)

theorem card_slotFilter (a d : ℕ) :
    ((Finset.range d).filter (fun b => Nat.gcd (Nat.gcd a b) d = 1)).card
      = d / Nat.gcd a d * Nat.totient (Nat.gcd a d) := by
  have hg : Nat.gcd a d ∣ d := Nat.gcd_dvd_right a d
  have hfilt : (Finset.range d).filter (fun b => Nat.gcd (Nat.gcd a b) d = 1)
      = (Finset.range d).filter (fun b => Nat.gcd (Nat.gcd a d) b = 1) :=
    Finset.filter_congr fun b _ => by rw [Nat.gcd_assoc a b d, Nat.gcd_comm b d, ← Nat.gcd_assoc a d b]
  have key := card_filter_range_mul_gcd_eq_one (Nat.gcd a d) (d / Nat.gcd a d)
  rw [Nat.mul_div_cancel' hg] at key
  rw [hfilt]
  exact key

theorem mul_card_slotFilter_comm (a d : ℕ) :
    a * ((Finset.range d).filter (fun b => Nat.gcd (Nat.gcd a b) d = 1)).card
      = d * ((Finset.range a).filter (fun b => Nat.gcd (Nat.gcd d b) a = 1)).card := by
  rw [card_slotFilter, card_slotFilter, Nat.gcd_comm d a, ← mul_assoc, ← mul_assoc,
    ← Nat.mul_div_assoc a (Nat.gcd_dvd_right a d), ← Nat.mul_div_assoc d (Nat.gcd_dvd_left a d), mul_comm a d]

theorem sum_slots_sq (N : ℕ) (hN : N ≠ 0) :
    ∑ p ∈ N.divisors.sigma (fun a => (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1)),
        p.1 * p.1
      = N * (N.divisors.sigma (fun a => (Finset.range (N / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1))).card := by
  rw [Finset.card_sigma, Finset.mul_sum, Finset.sum_sigma]
  conv_rhs => rw [← Nat.sum_div_divisors N]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hdvd : a ∣ N := Nat.dvd_of_mem_divisors ha
  have haN : a * (N / a) = N := Nat.mul_div_cancel' hdvd
  simp only [Finset.sum_const, smul_eq_mul, Nat.div_div_self hdvd hN]
  rw [mul_comm _ (a * a), mul_assoc, mul_card_slotFilter_comm, ← mul_assoc, haN]

end SlotCount

theorem evalSymm_of_primitiveRoot {K : Type*} [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N]
    (hN : 1 < N) (ζ : Kˣ) (hζ' : IsPrimitiveRoot (ζ : K) N) (data : ModularPolynomialData N) : EvalSymm data.Φ := by
  classical
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNne : N ≠ 0 := NeZero.ne N

  set ι : Polynomial ℤ →+* LaurentSeries K := ((coeffEmb K).comp (qExpand ℚ N)).comp evalAtJ with hιdef
  set S : Finset (Σ _ : ℕ, ℕ) :=
    N.divisors.sigma (fun a => (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1)) with hSdef
  set sl : (Σ _ : ℕ, ℕ) → LaurentSeries K := fun p => slot ζ p.1 p.2 with hsldef

  have hall : ∀ d : ℕ, d ∣ N → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d ∧ modularFunctionField d = modularFunctionFieldFull d :=
    fun d _ _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩
  have hprod := minpoly_jqN_map_eq_prod_slots (K := K) N ζ hζ' hall
  rw [minpoly_jqN_eq_toAdjoin data (phiIrreducible_all N data), ModularPolynomialData.toAdjoin, Polynomial.map_map,
    RingHom.comp_assoc, algebraMap_comp_evalAtJGen] at hprod
  have hprodS : data.Φ.map ι = ∏ p ∈ S, (X - C (sl p)) := by
    rw [Finset.prod_sigma]
    refine hprod.trans (Finset.prod_congr rfl fun a ha => ?_)
    rfl

  have hS1 : ∀ p ∈ S, p.1 ≠ 0 := fun p hp => (Nat.pos_of_mem_divisors (Finset.mem_sigma.mp hp).1).ne'
  have hcardS : S.card = dedekindPsi N := by
    have h1 : (data.Φ.map ι).natDegree = dedekindPsi N := by rw [data.monic.natDegree_map, data.natDegree_eq]
    have h2 : (∏ p ∈ S, (X - C (sl p))).natDegree = S.card := by
      rw [natDegree_prod_of_monic _ _ (fun p _ => monic_X_sub_C (sl p))]
      simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    rw [← h2, ← hprodS, h1]
  have hsumS : ∑ p ∈ S, p.1 * p.1 = N * dedekindPsi N := by
    rw [← hcardS, hSdef]
    exact sum_slots_sq N hNne

  have htpS : ∀ p ∈ S, TPoleOrderLE (sl p) (p.1 * p.1) := fun p hp => tp_slot ζ (hS1 p hp) p.2
  have hwS : ∀ p ∈ S, 1 ≤ p.1 * p.1 := fun p hp => Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (hS1 p hp) (hS1 p hp))
  have hcoef : ∀ k : ℕ, TPoleOrderLE (ι (data.Φ.coeff k)) (N * dedekindPsi N - k) := by
    intro k
    rw [← Polynomial.coeff_map, hprodS, ← hsumS]
    exact tp_coeff_prod_X_sub_C S sl (fun p => p.1 * p.1) htpS hwS k

  have hdeg : ∀ (P : Polynomial ℤ) (B : ℕ), P ≠ 0 → TPoleOrderLE (ι P) B → N * P.natDegree ≤ B := by
    intro P B hP hB
    by_contra hlt
    push Not at hlt
    have h0 : (ι P).coeff (-((N * P.natDegree : ℕ) : ℤ)) = 0 := hB _ (by push_cast; omega)
    rw [iota_lead] at h0
    have h1 : ((P.leadingCoeff : ℤ) : ℚ) = 0 := (algebraMap ℚ K).injective (by rw [h0, map_zero])
    exact hP (leadingCoeff_eq_zero.mp (by exact_mod_cast h1))

  have hk : ∀ k, k ≠ 0 → (data.Φ.coeff k).degree < (dedekindPsi N : WithBot ℕ) := by
    intro k hk0
    by_cases hP : data.Φ.coeff k = 0
    · rw [hP, degree_zero]; exact WithBot.bot_lt_coe _
    rw [degree_eq_natDegree hP, Nat.cast_lt]
    have h := hdeg _ _ hP (hcoef k)
    have hψ : 0 < dedekindPsi N := by rw [← hcardS, Finset.card_pos]; exact ⟨⟨1, 0⟩, by
      rw [Finset.mem_sigma]; exact ⟨Nat.one_mem_divisors.mpr hNne, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        rw [Nat.div_one]; exact hNpos), by simp⟩⟩⟩
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0

    have : N * (data.Φ.coeff k).natDegree < N * dedekindPsi N := by
      have hle : N * dedekindPsi N - k < N * dedekindPsi N := Nat.sub_lt (Nat.mul_pos hNpos hψ) (by omega)
      omega
    exact Nat.lt_of_mul_lt_mul_left this

  have hlead : (ι (data.Φ.coeff 0)).coeff (-((N * dedekindPsi N : ℕ) : ℤ)) = 1 := by
    rw [← Polynomial.coeff_map, hprodS, coeff_zero_prod_X_sub_C, ← hsumS,
      coeff_prod_lead S (fun p => -(sl p)) (fun p => p.1 * p.1) (fun p hp => tp_neg (htpS p hp))]

    have hterm : ∀ p ∈ S, (-(sl p)).coeff (-((p.1 * p.1 : ℕ) : ℤ)) = -((((ζ ^ (p.2 * p.1))⁻¹ : Kˣ) : K)) := by
      intro p hp
      rw [HahnSeries.coeff_neg, slot_lead ζ (hS1 p hp)]
    rw [Finset.prod_congr rfl hterm, hSdef, ← Finset.prod_sigma' N.divisors
      (fun a => (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1))
      (fun a b => -((((ζ ^ (b * a))⁻¹ : Kˣ) : K)))]

    have hinner : ∀ a ∈ N.divisors,
        ∏ b ∈ (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
          (-((((ζ ^ (b * a))⁻¹ : Kˣ) : K))) = if Nat.gcd a (N / a) = 1 then -1 else 1 := by
      intro a ha
      have haN : N = a * (N / a) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)).symm
      have hdpos : 0 < N / a :=
        Nat.div_pos (Nat.le_of_dvd hNpos (Nat.dvd_of_mem_divisors ha)) (Nat.pos_of_mem_divisors ha)
      have hθ : IsPrimitiveRoot (((ζ⁻¹ : Kˣ) : K) ^ a) (N / a) := by
        refine IsPrimitiveRoot.pow hNpos ?_ haN
        rw [Units.val_inv_eq_inv_val]
        exact hζ'.inv
      have hterm' : ∀ b : ℕ, -((((ζ ^ (b * a))⁻¹ : Kˣ) : K)) = -((((ζ⁻¹ : Kˣ) : K) ^ a) ^ b) := fun b => by
        rw [← pow_mul, mul_comm a b, ← inv_pow, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      rw [Finset.prod_congr rfl fun b _ => hterm' b]
      split_ifs with hg
      · have hall' : ∀ b ∈ Finset.range (N / a), Nat.gcd (Nat.gcd a b) (N / a) = 1 := fun b _ =>
          Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a b) hg
        rw [Finset.filter_true_of_mem hall']
        exact prod_neg_pow_eq_neg_one hdpos hθ
      · exact prod_neg_pow_slotFilter_eq_one hdpos hg hθ
    rw [Finset.prod_congr rfl hinner]

    refine Finset.prod_involution (fun a _ => N / a) (fun a ha => ?_) (fun a ha hne => ?_)
      (fun a ha => Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ha), hNne⟩)
      (fun a ha => Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hNne)
    · have hga : Nat.gcd (N / a) (N / (N / a)) = Nat.gcd a (N / a) := by
        rw [Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hNne, Nat.gcd_comm]
      show (if Nat.gcd a (N / a) = 1 then (-1 : K) else 1) *
          (if Nat.gcd (N / a) (N / (N / a)) = 1 then (-1 : K) else 1) = 1
      by_cases hg : Nat.gcd a (N / a) = 1
      · rw [if_pos hg, if_pos (hga.trans hg)]
        norm_num
      · rw [if_neg hg, if_neg (fun h => hg (hga.symm.trans h))]
        norm_num
    · intro h
      have h' : N / a = a := h
      apply hne
      show (if Nat.gcd a (N / a) = 1 then (-1 : K) else 1) = 1
      have hg1 : Nat.gcd a (N / a) ≠ 1 := by
        rw [h', Nat.gcd_self]
        intro ha1
        have haN : a * (N / a) = N := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)
        rw [h', ha1] at haN
        omega
      rw [if_neg hg1]
  have h0ne : data.Φ.coeff 0 ≠ 0 := by
    intro h
    rw [h, map_zero, HahnSeries.coeff_zero] at hlead
    exact zero_ne_one hlead
  have h0deg : (data.Φ.coeff 0).natDegree = dedekindPsi N := by
    refine le_antisymm (Nat.le_of_mul_le_mul_left (by simpa using hdeg _ _ h0ne (hcoef 0)) hNpos) ?_

    by_contra hlt
    push Not at hlt
    have := tp_iota (K := K) N (data.Φ.coeff 0) (-((N * dedekindPsi N : ℕ) : ℤ)) (by
      push_cast
      have := Nat.mul_lt_mul_of_pos_left hlt hNpos
      omega)
    rw [hlead] at this
    exact one_ne_zero this
  have h0 : (data.Φ.coeff 0).Monic := by
    have h := iota_lead (K := K) N (data.Φ.coeff 0)
    rw [h0deg, hlead] at h
    have h' : ((data.Φ.coeff 0).leadingCoeff : ℚ) = 1 := (algebraMap ℚ K).injective (by rw [map_one]; exact h.symm)
    exact_mod_cast h'

  have hιq : (coeffEmb K).comp (evalAtJqN N) = ι := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [hιdef, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, evalAtJqN_X, evalAtJ_X]
    rfl
  have hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0 := by
    apply (coeffEmb K).injective
    rw [map_zero, hom_eval₂, hιq, ← eval_map, hprodS, eval_prod]
    refine Finset.prod_eq_zero (i := ⟨1, 0⟩) ?_ ?_
    · exact Finset.mem_sigma.mpr ⟨Nat.one_mem_divisors.mpr hNne, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by rw [Nat.div_one]; exact hNpos), by simp⟩⟩
    · rw [eval_sub, eval_X, eval_C]
      show coeffEmb K jq - slot ζ 1 0 = 0
      rw [slot_one_zero, sub_self]

  obtain ⟨hTmonic, hTdeg⟩ := swapBivar_monic_of_coeff_bounds h0 h0deg hk
  exact ModularPolynomialData.evalSymm_of_irreducible data (phiIrreducible_all N data) hswap
    (hTmonic.map evalAtJGen) ((natDegree_map_le).trans hTdeg.le)

theorem evalSymm_main (N : ℕ) [NeZero N] (hN : 1 < N) (data : ModularPolynomialData N) :
    EvalSymm data.Φ :=
  have hζ := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  evalSymm_of_primitiveRoot N hN (hζ.isUnit (NeZero.ne N)).unit (by rw [IsUnit.unit_spec]; exact hζ) data

end Aux1LevelSymm

theorem solution (N : ℕ) [NeZero N] (hN : 1 < N) (data : ModularPolynomialData N) : EvalSymm data.Φ :=
  Aux1LevelSymm.evalSymm_main N hN data

end S_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt (solution)
