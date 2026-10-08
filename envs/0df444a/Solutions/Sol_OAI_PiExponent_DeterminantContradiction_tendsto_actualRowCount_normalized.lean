-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.tendsto_actualRowCount_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:47:59.317305+00:00
-- url     : https://prove2.me/submissions/108a015a-842e-4c8c-b326-e7bf951c64eb

-- Proof adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Tactic

set_option autoImplicit false
open Filter Topology
open scoped BigOperators
noncomputable section

namespace OAI

open Filter Topology

namespace PiExponent

theorem tendsto_natFloor_affine_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => ⌊a * x + b⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id))

theorem tendsto_natFloor_affine_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => (⌊a * x + b⌋₊ : ℝ) / x) atTop (𝓝 a) := by
  have hy : Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id)
  have hratio : Tendsto (fun x : ℝ => (a * x + b) / x) atTop (𝓝 a) := by
    have h : Tendsto (fun x : ℝ => a + b * x⁻¹) atTop (𝓝 (a + b * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have h := (tendsto_nat_floor_div_atTop.comp hy).mul hratio
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hy.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  change (⌊a * x + b⌋₊ : ℝ) / (a * x + b) * ((a * x + b) / x) = _
  field_simp

theorem tendsto_normalized_natFloor_affine {f : ℕ → ℝ} {d : ℕ} {L a : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ d) atTop (𝓝 L))
    (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => f ⌊a * x + b⌋₊ / x ^ d) atTop (𝓝 (L * a ^ d)) := by
  have hfloor := tendsto_natFloor_affine_atTop ha b
  have h := (hf.comp hfloor).mul ((tendsto_natFloor_affine_div ha b).pow d)
  apply h.congr'
  filter_upwards [hfloor.eventually (eventually_ge_atTop 1)] with x hx
  have hn : (⌊a * x + b⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : ⌊a * x + b⌋₊ ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem tendsto_normalized_natFloor_affine_nat {f : ℕ → ℝ} {d : ℕ} {L a : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ d) atTop (𝓝 L))
    (ha : 0 < a) (b : ℝ) :
    Tendsto (fun N : ℕ => f ⌊a * (N : ℝ) + b⌋₊ / (N : ℝ) ^ d)
      atTop (𝓝 (L * a ^ d)) :=
  (tendsto_normalized_natFloor_affine hf ha b).comp tendsto_natCast_atTop_atTop

end PiExponent

end OAI

namespace OAI

open scoped BigOperators

namespace PiExponent

def unweightedSimplex (d N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, a i ≤ N)

@[simp] theorem mem_unweightedSimplex {d N : ℕ} {a : Fin d → ℕ} :
    a ∈ unweightedSimplex d N ↔ ∑ i, a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    omega

theorem card_unweightedSimplex (d N : ℕ) :
    (unweightedSimplex d N).card = (N + d).choose d := by
  classical
  let target : Finset (Fin (d + 1) →₀ ℕ) := Finset.univ.finsuppAntidiag N
  have hc : target.card = (N + d).choose d := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show d + 1 + N - 1 = N + d by omega, Nat.choose_symm_add]
  rw [← hc]
  let f : (Fin d → ℕ) → (Fin (d + 1) →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (N - ∑ i, a i) a)
  apply Finset.card_bij (fun a _ => f a)
  · intro a ha
    apply Finset.mem_finsuppAntidiag.mpr
    constructor
    · simp only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      exact Nat.sub_add_cancel (mem_unweightedSimplex.mp ha)
    · exact Finset.subset_univ _
  · intro a ha b hb hab
    funext i
    have h := congrArg (fun g : Fin (d + 1) →₀ ℕ => g i.succ) hab
    simpa only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.cons_succ] using h
  · intro b hb
    obtain ⟨hs, _⟩ := Finset.mem_finsuppAntidiag.mp hb
    have hs' : b 0 + ∑ i : Fin d, b i.succ = N := by
      simpa only [Fin.sum_univ_succ] using hs
    refine ⟨fun i => b i.succ, mem_unweightedSimplex.mpr (by omega), ?_⟩
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change N - ∑ j : Fin d, b j.succ = b 0
      omega
    · change b j.succ = b j.succ
      rfl

open Filter Topology Asymptotics

theorem tendsto_choose_normalized (d : ℕ) :
    Tendsto (fun N : ℕ => (N.choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h := (isEquivalent_choose d).div
    (IsEquivalent.refl : (fun N : ℕ => (N : ℝ) ^ d) ~[atTop]
      (fun N : ℕ => (N : ℝ) ^ d))
  apply h.symm.tendsto_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  change 1 / (d.factorial : ℝ) = ((N : ℝ) ^ d / (d.factorial : ℝ)) / (N : ℝ) ^ d
  field_simp

theorem tendsto_choose_add_normalized (d c : ℕ) :
    Tendsto (fun N : ℕ => ((N + c).choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h₁ := (tendsto_choose_normalized d).comp (tendsto_add_atTop_nat c)
  have h₂ : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c : ℝ) 0 1 (d := 1) (by norm_num))
  have h := h₁.mul (h₂.pow d)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : ((N + c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + c ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem tendsto_card_unweightedSimplex (d : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex] using tendsto_choose_add_normalized d d

theorem tendsto_card_unweightedSimplex_add (d c : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d (N + c)).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex, Nat.add_assoc] using
    tendsto_choose_add_normalized d (c + d)

end PiExponent

end OAI

namespace OAI

open scoped BigOperators

namespace PiExponent

def natWeightedSimplex {d : ℕ} (w : Fin d → ℕ) (N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, w i * a i ≤ N)

theorem mem_natWeightedSimplex {d : ℕ} {w : Fin d → ℕ}
    (hw : ∀ i, 0 < w i) {N : ℕ} {a : Fin d → ℕ} :
    a ∈ natWeightedSimplex w N ↔ ∑ i, w i * a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have h₁ : a i ≤ w i * a i := Nat.le_mul_of_pos_left (a i) (hw i)
    have h₂ : w i * a i ≤ ∑ j, w j * a j :=
      Finset.single_le_sum (f := fun j => w j * a j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

def residueRectangle {d : ℕ} (w : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (w i))

@[simp] theorem mem_residueRectangle {d : ℕ} {w r : Fin d → ℕ} :
    r ∈ residueRectangle w ↔ ∀ i, r i < w i := by
  simp [residueRectangle, Fintype.mem_piFinset]

@[simp] theorem card_residueRectangle {d : ℕ} (w : Fin d → ℕ) :
    (residueRectangle w).card = ∏ i, w i := by
  simp [residueRectangle, Fintype.card_piFinset]

theorem simplex_count_lower_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex (fun _ : Fin d => 1) N).card ≤
      (natWeightedSimplex w N).card * ∏ i, w i := by
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : (Fin d → ℕ) → (Fin d → ℕ) × (Fin d → ℕ) :=
    fun b => (fun i => b i / w i, fun i => b i % w i)
  apply Finset.card_le_card_of_injOn f
  · intro b hb
    apply Finset.mem_product.mpr
    constructor
    · apply (mem_natWeightedSimplex hw).mpr
      have hb' := (mem_natWeightedSimplex (fun _ => by decide)).mp hb
      simp only [one_mul] at hb'
      exact (Finset.sum_le_sum (fun i _ => Nat.mul_div_le (b i) (w i))).trans hb'
    · exact mem_residueRectangle.mpr (fun i => Nat.mod_lt (b i) (hw i))
  · intro a ha b hb hab
    have hq := congrArg Prod.fst hab
    have hr := congrArg Prod.snd hab
    funext i
    have hqi := congrFun hq i
    have hri := congrFun hr i
    change a i / w i = b i / w i at hqi
    change a i % w i = b i % w i at hri
    have ha' := Nat.div_add_mod (a i) (w i)
    have hb' := Nat.div_add_mod (b i) (w i)
    calc
      a i = w i * (a i / w i) + a i % w i := ha'.symm
      _ = w i * (b i / w i) + b i % w i := by rw [hqi, hri]
      _ = b i := hb'

theorem simplex_count_upper_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex w N).card * (∏ i, w i) ≤
      (natWeightedSimplex (fun _ : Fin d => 1) (N + ∑ i, (w i - 1))).card := by
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : ((Fin d → ℕ) × (Fin d → ℕ)) → (Fin d → ℕ) :=
    fun ar i => w i * ar.1 i + ar.2 i
  apply Finset.card_le_card_of_injOn f
  · intro ar har
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    apply (mem_natWeightedSimplex (fun _ => by decide)).mpr
    simp only [one_mul]
    change ∑ i, (w i * ar.1 i + ar.2 i) ≤ _
    rw [Finset.sum_add_distrib]
    apply Nat.add_le_add ((mem_natWeightedSimplex hw).mp ha)
    apply Finset.sum_le_sum
    intro i hi
    have := mem_residueRectangle.mp hr i
    omega
  · intro ar har bs hbs hab
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    obtain ⟨hb, hs⟩ := Finset.mem_product.mp hbs
    apply Prod.ext
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hdiv := congrArg (fun n => n / w i) hi
      rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (ar.1 i)),
        Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (bs.1 i))] at hdiv
      simpa [Nat.div_eq_of_lt hri, Nat.div_eq_of_lt hsi,
        Nat.mul_div_cancel_left _ (hw i)] using hdiv
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hmod := congrArg (fun n => n % w i) hi
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hri, Nat.mod_eq_of_lt hsi] using hmod

@[simp] theorem natWeightedSimplex_one (d N : ℕ) :
    natWeightedSimplex (fun _ : Fin d => 1) N = unweightedSimplex d N := by
  ext a
  rw [mem_natWeightedSimplex (w := fun _ : Fin d => 1) (fun _ => by decide), mem_unweightedSimplex]
  simp only [one_mul]

open Filter Topology

theorem tendsto_card_natWeightedSimplex {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)))) := by
  let P : ℝ := ∏ i, (w i : ℝ)
  have hP : 0 < P := Finset.prod_pos (fun i _ => by exact_mod_cast hw i)
  have hs : Tendsto
      (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_card_unweightedSimplex d)
      (tendsto_card_unweightedSimplex_add d (∑ i, (w i - 1)))
    · intro N
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := simplex_count_lower_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
    · intro N
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := simplex_count_upper_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
  have h := hs.div_const P
  have heq : 1 / (d.factorial : ℝ) / P =
      1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)) := by
    simp only [P, div_div]
  rw [heq] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun N => by
    change ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d / P = _
    field_simp)





theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

theorem mem_strictWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by
  classical
  simp only [strictWeightedSimplex, Finset.mem_filter, mem_realWeightedSimplex hw,
    and_iff_right_iff_imp]
  exact fun h => h.le

theorem realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c H : ℝ} (hc : 0 < c) (hH : 0 ≤ H) :
    realWeightedSimplex (fun i => (w i : ℝ) / c) H =
      natWeightedSimplex w ⌊c * H⌋₊ := by
  ext a
  rw [mem_realWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc),
    mem_natWeightedSimplex hw, Nat.le_floor_iff (mul_nonneg hc.le hH)]
  have hs : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
      ((∑ i, w i * a i : ℕ) : ℝ) / c := by
    simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
  rw [hs, div_le_iff₀ hc, mul_comm H c]

theorem strictWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    strictWeightedSimplex (fun i => (w i : ℝ) / c) H =
      natWeightedSimplex w (⌈c * H⌉₊ - 1) := by
  ext a
  rw [mem_strictWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc),
    mem_natWeightedSimplex hw]
  have hs : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
      ((∑ i, w i * a i : ℕ) : ℝ) / c := by
    simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
  rw [hs, div_lt_iff₀ hc, mul_comm H c, ← Nat.lt_ceil]
  have hp : 0 < ⌈c * H⌉₊ := by
    apply Nat.lt_ceil.mpr
    simpa using mul_pos hc hH
  omega

theorem tendsto_card_realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((realWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by
  have h := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc 0
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp only [add_zero, realWeightedSimplex_scaled w hw hc hH]

theorem tendsto_card_strictWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((strictWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by
  have hlo := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc (-1)
  have hhi := tendsto_card_realWeightedSimplex_scaled w hw hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (1 / c)] with H hH
    have hHpos : 0 < H := (div_pos zero_lt_one hc).trans_le hH
    have hcH : 1 ≤ c * H := by
      have := (div_le_iff₀ hc).mp hH
      nlinarith
    apply div_le_div_of_nonneg_right _ (pow_nonneg hHpos.le d)
    exact_mod_cast (Finset.card_le_card (show
      natWeightedSimplex w ⌊c * H + -1⌋₊ ⊆
      strictWeightedSimplex (fun i => (w i : ℝ) / c) H from by
        intro a ha
        apply (mem_strictWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc)).mpr
        have ha' := (mem_natWeightedSimplex hw).mp ha
        have hs : ((∑ i, w i * a i : ℕ) : ℝ) ≤ c * H + -1 :=
          (Nat.le_floor_iff (by linarith)).mp ha'
        have heq : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
            ((∑ i, w i * a i : ℕ) : ℝ) / c := by
          simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
        rw [heq, div_lt_iff₀ hc]
        nlinarith))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    apply div_le_div_of_nonneg_right _ (pow_nonneg hH d)
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset
      (fun a : Fin d → ℕ => ∑ i, (w i : ℝ) / c * (a i : ℝ) < H)
      (realWeightedSimplex (fun i => (w i : ℝ) / c) H)))


end PiExponent
end OAI

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem positive_rational_weights_common_denominator {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    ∃ D : ℕ, 0 < D ∧ ∃ w : Fin d → ℕ,
      (∀ i, 0 < w i) ∧ ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ) := by
  classical
  let D : ℕ := ∏ i, (ρ i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (ρ i).den_pos)
  have hd : ∀ i, (ρ i).den ∣ D :=
    fun i => Finset.dvd_prod_of_mem (fun j => (ρ j).den) (Finset.mem_univ i)
  choose k hk using hd
  have hkpos : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have hkzero : k i = 0 := by omega
    have := hk i
    rw [hkzero, mul_zero] at this
    omega
  let w : Fin d → ℕ := fun i => (ρ i).num.toNat * k i
  refine ⟨D, hD, w, ?_, ?_⟩
  · intro i
    have hn : 0 < (ρ i).num := Rat.num_pos.mpr (hρ i)
    exact Nat.mul_pos (by omega) (hkpos i)
  · intro i
    have hnum : (((ρ i).num.toNat : ℕ) : ℝ) = ((ρ i).num : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (Rat.num_pos.mpr (hρ i)).le)
    have hcastD : (D : ℝ) = ((ρ i).den : ℝ) * (k i : ℝ) := by
      exact_mod_cast hk i
    have hkne : (k i : ℝ) ≠ 0 := by exact_mod_cast (hkpos i).ne'
    have hdenne : ((ρ i).den : ℝ) ≠ 0 := by exact_mod_cast (ρ i).den_ne_zero
    rw [Rat.cast_def, hcastD]
    change ((ρ i).num : ℝ) / ((ρ i).den : ℝ) =
      (((ρ i).num.toNat * k i : ℕ) : ℝ) / (((ρ i).den : ℝ) * (k i : ℝ))
    rw [Nat.cast_mul, hnum]
    field_simp

end PiExponent

end OAI

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

theorem common_denominator_simplex_constant {d D : ℕ} {ρ : Fin d → ℚ}
    {w : Fin d → ℕ} (hD : 0 < D) (hw : ∀ i, 0 < w i)
    (hweights : ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ)) :
    (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * (D : ℝ) ^ d =
      1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)) := by
  have hprod : (∏ i, (ρ i : ℝ)) = (∏ i, (w i : ℝ)) / (D : ℝ) ^ d := by
    simp_rw [hweights]
    rw [Finset.prod_div_distrib]
    simp
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPne : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)).ne'
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [hprod]
  field_simp

theorem tendsto_card_realWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((realWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_realWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

theorem tendsto_card_strictWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((strictWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_strictWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h


end PiExponent
end OAI

namespace OAI.PiExponent.InterpolationMatrix
@[simp] theorem row_card {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) :
    Fintype.card (Row K v0 θ w H) =
      K * (PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H).card := by
  classical
  simp [Row]

end OAI.PiExponent.InterpolationMatrix

namespace OAI.PiExponent.MatrixArithmetic
theorem ceil_log_weight_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  exact lt_of_lt_of_le (Real.log_pos hqR) (Nat.le_ceil _)

end OAI.PiExponent.MatrixArithmetic

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent.MatrixCounting

noncomputable def rowCount {m : ℕ} (K : ℕ) (v0 θ : ℚ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  Fintype.card (InterpolationMatrix.Row K (v0 : ℝ) (θ : ℝ) (MatrixArithmetic.logWeights q) H)

noncomputable def lowIndexCount {m : ℕ} (A : ℚ) (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights q) ((A : ℝ) * H)).card

noncomputable def rationalLogWeights {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℚ :=
  (⌈Real.log (q i)⌉₊ : ℚ)

@[simp] theorem rationalLogWeights_cast {m : ℕ} (q : Fin m → ℕ) (i : Fin m) :
    (rationalLogWeights q i : ℝ) = MatrixArithmetic.logWeights q i := by
  simp [rationalLogWeights, MatrixArithmetic.logWeights]

theorem rationalLogWeights_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (i : Fin m) : 0 < rationalLogWeights q i := by
  have h := MatrixArithmetic.ceil_log_weight_pos (hq i)
  unfold rationalLogWeights
  exact_mod_cast h

theorem tendsto_rowCount_normalized {m : ℕ} (K : ℕ) (v0 θ : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => rowCount K v0 θ q H / H ^ (m + 1)) atTop
      (𝓝 ((K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i))) := by
  let V : Fin (m + 1) → ℚ := Fin.cases v0 (fun i => rationalLogWeights q i / θ)
  have hV : ∀ i, 0 < V i := by
    intro i
    exact Fin.cases hv0 (fun j => div_pos (rationalLogWeights_pos q hq j) hθ) i
  have hcast : (fun i => (V i : ℝ)) =
      InterpolationMatrix.rowWeights (v0 : ℝ) (θ : ℝ) (MatrixArithmetic.logWeights q) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [V, InterpolationMatrix.rowWeights]
    · simp [V, InterpolationMatrix.rowWeights]
  have hp : ∏ i, (V i : ℝ) =
      (v0 : ℝ) * (∏ i, MatrixArithmetic.logWeights q i) / (θ : ℝ) ^ m := by
    rw [Fin.prod_univ_succ]
    simp [V, Finset.prod_div_distrib, mul_div_assoc]
  have ht := (tendsto_card_strictWeightedSimplex_rational V hV).const_mul (K : ℝ)
  have hθ0 : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
  have he : (K : ℝ) * (1 / (((m + 1).factorial : ℝ) * ∏ i, (V i : ℝ))) =
      (K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) := by
    rw [hp]
    field_simp
  rw [he] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun H => by
    simp only [rowCount, InterpolationMatrix.row_card, Nat.cast_mul]
    rw [← hcast]
    ring)

theorem tendsto_lowIndexCount_normalized {m : ℕ} (A : ℚ)
    (q : Fin m → ℕ) (hA : 0 < A) (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => lowIndexCount A q H / H ^ m) atTop
      (𝓝 ((A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i))) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have ht : Tendsto (fun H : ℝ => (A : ℝ) * H) atTop atTop :=
    Tendsto.const_mul_atTop hAR tendsto_id
  have h := ((tendsto_card_realWeightedSimplex_rational (rationalLogWeights q)
    (rationalLogWeights_pos q hq)).comp ht).mul_const ((A : ℝ) ^ m)
  simp only [rationalLogWeights_cast] at h
  have he : 1 / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) * (A : ℝ) ^ m =
      (A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) := by ring
  rw [he] at h
  have hweights : (fun i => (rationalLogWeights q i : ℝ)) = MatrixArithmetic.logWeights q := by
    funext i
    exact rationalLogWeights_cast q i
  apply h.congr'
  exact Eventually.of_forall (fun H => by
    simp only [Function.comp_apply, lowIndexCount, mul_pow]
    field_simp)

theorem tendsto_row_lowIndex_ratio {m : ℕ} (K : ℕ) (v0 θ A : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => rowCount K v0 θ q H / (H * lowIndexCount A q H)) atTop
      (𝓝 ((K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m))) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hvR : (0 : ℝ) < v0 := by exact_mod_cast hv0
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hP : 0 < ∏ i, MatrixArithmetic.logWeights q i :=
    Finset.prod_pos (fun i _ => MatrixArithmetic.ceil_log_weight_pos (hq i))
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hd : (A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) ≠ 0 :=
    (div_pos (pow_pos hAR m) (mul_pos hfac hP)).ne'
  have h := (tendsto_rowCount_normalized K v0 θ q hv0 hθ hq).div
    (tendsto_lowIndexCount_normalized A q hA hq) hd
  have he :
      ((K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i)) /
        ((A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i)) =
      (K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  change (rowCount K v0 θ q H / H ^ (m + 1)) / (lowIndexCount A q H / H ^ m) =
    rowCount K v0 θ q H / (H * lowIndexCount A q H)
  by_cases hn : lowIndexCount A q H = 0
  · simp [hn]
  · simp only [pow_succ]
    field_simp [hH.ne', hn]

theorem tendsto_collisionRatio {m : ℕ} (K : ℕ) (v0 θ A : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) (c η : ℝ) :
    Tendsto (fun H : ℝ => c * η ^ 2 * rowCount K v0 θ q H /
      (H * lowIndexCount A q H)) atTop
      (𝓝 (c * η ^ 2 * (K : ℝ) * (θ : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m))) := by
  have ht := (tendsto_row_lowIndex_ratio K v0 θ A q hv0 hθ hA hq).const_mul (c * η ^ 2)
  have he : (c * η ^ 2) *
      ((K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m)) =
      c * η ^ 2 * (K : ℝ) * (θ : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m) := by ring
  rw [he] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun H => by
    change (c * η ^ 2) * (rowCount K v0 θ q H / (H * lowIndexCount A q H)) = _
    ring)

end PiExponent.MatrixCounting

end OAI

namespace OAI.PiExponent.DeterminantContradiction
theorem finiteDenominators_two_le {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

end OAI.PiExponent.DeterminantContradiction

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    Tendsto (fun H : ℝ => (actualRowCount d H : ℝ) / H ^ (d.m + 1)) atTop
      (𝓝 ((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
        (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
          ∏ i, MatrixArithmetic.logWeights (finiteDenominators d) i))) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hh := MatrixCounting.tendsto_rowCount_normalized d.K d.v0 d.base.theta
    (finiteDenominators d) hv ht (finiteDenominators_two_le d)
  apply hh.congr'
  filter_upwards with H
  simp [MatrixCounting.rowCount, actualRowCount, Row]