-- Prove2me | solution 1 for NoSignalPA.secure_of_entrywise
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T22:05:36.23121+00:00
-- url     : https://prove2.me/submissions/7dd3d65b-81af-4859-85f2-c6b2198cfc64

import Mathlib
import Definitions.Def_NoSignalPA_IsSecure
import Definitions.Def_NoSignalPA_SatisfiesEq6
import Theorems.Thm_NoSignalPA_lemma_1
import Theorems.Thm_NoSignalPA_sum_mu
import Theorems.Thm_NoSignalPA_chsh_tensor_entry

open scoped ENNReal

namespace NoSignalPAEq7Aux

lemma tsum_finset_sum {α ι : Type*} (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑' e, ∑ i ∈ s, f i e = ∑ i ∈ s, ∑' e, f i e :=
  Summable.tsum_finsetSum fun _ _ => ENNReal.summable

lemma chshPow_nonneg {n : ℕ} (a b x y : NoSignalPA.Str n) : 0 ≤ NoSignalPA.chshPow a b x y := by
  rw [NoSignalPA.chsh_tensor_entry]
  positivity

/-- `pairing` is linear in its first argument. -/
lemma pairing_sum_left {n : ℕ} {ι : Type} (s : Finset ι)
    (c : ι → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ)
    (Q : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ) :
    ∑ i ∈ s, NoSignalPA.pairing (c i) Q =
      NoSignalPA.pairing (fun a b x y => ∑ i ∈ s, c i a b x y) Q := by
  unfold NoSignalPA.pairing
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

/-- `ofReal (Σ_{abxy} w · t.toReal) = Σ_{abxy} ofReal w · t` for nonnegative weights and finite
`t`. -/
lemma ofReal_sum4 {n : ℕ} (w : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n →
      NoSignalPA.Str n → ℝ) (hw : ∀ a b x y, 0 ≤ w a b x y)
    (t : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ≥0∞)
    (ht : ∀ a b x y, t a b x y ≠ ∞) :
    ENNReal.ofReal (∑ a, ∑ b, ∑ x, ∑ y, w a b x y * (t a b x y).toReal) =
      ∑ a, ∑ b, ∑ x, ∑ y, ENNReal.ofReal (w a b x y) * t a b x y := by
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hw a b x y) ENNReal.toReal_nonneg]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun b _ => Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => mul_nonneg (hw a b x y) ENNReal.toReal_nonneg]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hw a b x y) ENNReal.toReal_nonneg]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun y _ => mul_nonneg (hw a b x y) ENNReal.toReal_nonneg]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.ofReal_mul (hw a b x y), ENNReal.ofReal_toReal (ht a b x y)]

lemma pairing_sub {n : ℕ}
    (G1 G2 Q : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ)
    (c : ℝ) :
    NoSignalPA.pairing G1 Q - c * NoSignalPA.pairing G2 Q =
      NoSignalPA.pairing (fun a b x y => G1 a b x y - c * G2 a b x y) Q := by
  unfold NoSignalPA.pairing
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma pairing_abs_le {n : ℕ}
    (F W Q : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ)
    (hQ : ∀ a b x y, 0 ≤ Q a b x y) (hF : ∀ a b x y, |F a b x y| ≤ W a b x y) :
    |NoSignalPA.pairing F Q| ≤ NoSignalPA.pairing W Q := by
  unfold NoSignalPA.pairing
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (hQ a b x y)]
  exact mul_le_mul_of_nonneg_right (hF a b x y) (hQ a b x y)

lemma tsum_e_ne_top.{v} {Nr : ℕ} {Z E : Type v} (P : NoSignalPA.Box Nr Z E)
    (x y : NoSignalPA.Str Nr) (z : Z) (a b : NoSignalPA.Str Nr) :
    ∑' e, P x y z (a, b, e) ≠ ∞ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← PMF.tsum_coe (P x y z)]
  exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun e : E => (a, b, e))
    (fun e e' h => by simpa using h) _

end NoSignalPAEq7Aux

open NoSignalPAEq7Aux in
theorem solution.{u} {Nr Ns : ℕ} (h : NoSignalPA.Str Nr → NoSignalPA.Str Ns)
    (hh : NoSignalPA.SatisfiesEq6 h) : NoSignalPA.IsSecure.{u} h := by
  intro Z E P hNS y z₀
  classical
  set x0 : NoSignalPA.Str Nr := fun _ => false with hx0
  set C : ℝ := Real.sqrt ((2 : ℝ) ^ ((Ns : ℝ) + Real.sqrt Nr)) with hCdef
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hfin : ∀ x y' z a b e, P x y' z (a, b, e) ≠ ∞ := fun x y' z a b e => PMF.apply_ne_top _ _
  -- the slices `Q_{z,e}`
  let Q : Z → E → NoSignalPA.Str Nr → NoSignalPA.Str Nr → NoSignalPA.Str Nr → NoSignalPA.Str Nr → ℝ :=
    fun z e a b x y' => (P x y' z (a, b, e)).toReal
  have hQnn : ∀ z e a b x y', 0 ≤ Q z e a b x y' := fun _ _ _ _ _ _ => ENNReal.toReal_nonneg
  have hA : ∀ z e (i : Fin Nr) (x : NoSignalPA.Str Nr) (c : Bool) (y' a b : NoSignalPA.Str Nr),
      ∑ t : Bool, Q z e (Function.update a i t) b x y'
        = ∑ t : Bool, Q z e (Function.update a i t) b (Function.update x i c) y' := by
    intro z e i x c y' a b
    have := congrArg ENNReal.toReal (hNS.1 i x c y' z a b e)
    rwa [ENNReal.toReal_sum (fun t _ => hfin _ _ _ _ _ _),
      ENNReal.toReal_sum (fun t _ => hfin _ _ _ _ _ _)] at this
  have hB : ∀ z e (a x y1 y2 : NoSignalPA.Str Nr),
      ∑ b : NoSignalPA.Str Nr, Q z e a b x y1 = ∑ b : NoSignalPA.Str Nr, Q z e a b x y2 := by
    intro z e a x y1 y2
    have := congrArg ENNReal.toReal (hNS.2.1 x y1 y2 z a e)
    rwa [ENNReal.toReal_sum (fun b _ => hfin _ _ _ _ _ _),
      ENNReal.toReal_sum (fun b _ => hfin _ _ _ _ _ _)] at this
  -- Lemma 1 on each slice
  have hL1 : ∀ z e s, ∑ b, Q z e s b x0 y = NoSignalPA.pairing (NoSignalPA.gammaVec s) (Q z e) :=
    fun z e s => NoSignalPA.lemma_1 (Q z e) (hA z e) (hB z e) s y
  -- the per-slice bound
  have hslice : ∀ (k : NoSignalPA.Str Ns) z e,
      |(NoSignalPA.keyEveMarg h P x0 y z k e).toReal
          - ((2 : ℝ) ^ Ns)⁻¹ * (NoSignalPA.eveMarg P x0 y z e).toReal|
        ≤ ((2 : ℝ) ^ Ns)⁻¹ * C * NoSignalPA.pairing NoSignalPA.chshPow (Q z e) := by
    intro k z e
    have hK : (NoSignalPA.keyEveMarg h P x0 y z k e).toReal =
        ∑ s ∈ Finset.univ.filter (fun s => h s = k), NoSignalPA.pairing (NoSignalPA.gammaVec s) (Q z e) := by
      simp only [NoSignalPA.keyEveMarg]
      rw [ENNReal.toReal_sum (fun s _ => ENNReal.sum_ne_top.mpr fun b _ => hfin _ _ _ _ _ _)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ENNReal.toReal_sum (fun b _ => hfin _ _ _ _ _ _), ← hL1]
    have hEv : (NoSignalPA.eveMarg P x0 y z e).toReal =
        ∑ s, NoSignalPA.pairing (NoSignalPA.gammaVec s) (Q z e) := by
      simp only [NoSignalPA.eveMarg]
      rw [ENNReal.toReal_sum (fun s _ => ENNReal.sum_ne_top.mpr fun b _ => hfin _ _ _ _ _ _)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ENNReal.toReal_sum (fun b _ => hfin _ _ _ _ _ _), ← hL1]
    rw [hK, hEv, pairing_sum_left, pairing_sum_left, pairing_sub]
    have hsumΓ : ∀ a b x y', ∑ s, NoSignalPA.gammaVec s a b x y' = ((4 : ℝ) ^ Nr)⁻¹ :=
      fun a b x y' => (NoSignalPA.sum_mu a b x y').1
    have h2 : (0 : ℝ) < (2 : ℝ) ^ Ns := by positivity
    refine (pairing_abs_le _ (fun a b x y' => ((2 : ℝ) ^ Ns)⁻¹ * C * NoSignalPA.chshPow a b x y')
      _ (hQnn z e) ?_).trans (le_of_eq ?_)
    · intro a b x y'
      simp only [hsumΓ]
      have hv := hh k a b x y'
      rw [show (∑ s ∈ Finset.univ.filter (fun s => h s = k), NoSignalPA.gammaVec s a b x y')
            - ((2 : ℝ) ^ Ns)⁻¹ * ((4 : ℝ) ^ Nr)⁻¹ =
          ((2 : ℝ) ^ Ns)⁻¹ * ((2 : ℝ) ^ Ns *
            ∑ s ∈ Finset.univ.filter (fun s => h s = k), NoSignalPA.gammaVec s a b x y'
            - ((4 : ℝ) ^ Nr)⁻¹) by field_simp,
        abs_mul, abs_of_pos (inv_pos.mpr h2), mul_assoc]
      exact mul_le_mul_of_nonneg_left hv (inv_pos.mpr h2).le
    · unfold NoSignalPA.pairing
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y' _ => ?_
      ring
  -- sum over Eve's outcomes: Eve's no-signalling removes the dependence on `z`
  set X : ℝ := C * NoSignalPA.pairing NoSignalPA.chshPow (NoSignalPA.abMarg P z₀) with hX
  have hw : ∀ a b x y' : NoSignalPA.Str Nr,
      0 ≤ ((2 : ℝ) ^ Ns)⁻¹ * C * NoSignalPA.chshPow a b x y' :=
    fun a b x y' => mul_nonneg (mul_nonneg (by positivity) hC) (chshPow_nonneg a b x y')
  have hz : ∀ (k : NoSignalPA.Str Ns) z, ∑' e : E,
      ENNReal.ofReal |(NoSignalPA.keyEveMarg h P x0 y z k e).toReal
        - ((2 : ℝ) ^ Ns)⁻¹ * (NoSignalPA.eveMarg P x0 y z e).toReal|
      ≤ ENNReal.ofReal (((2 : ℝ) ^ Ns)⁻¹ * X) := by
    intro k z
    calc _ ≤ ∑' e : E, ENNReal.ofReal (((2 : ℝ) ^ Ns)⁻¹ * C *
            NoSignalPA.pairing NoSignalPA.chshPow (Q z e)) :=
          ENNReal.tsum_le_tsum fun e => ENNReal.ofReal_le_ofReal (hslice k z e)
      _ = ∑' e : E, ∑ a, ∑ b, ∑ x, ∑ y',
            ENNReal.ofReal (((2 : ℝ) ^ Ns)⁻¹ * C * NoSignalPA.chshPow a b x y') *
              P x y' z (a, b, e) := by
          refine tsum_congr fun e => ?_
          rw [← ofReal_sum4 _ hw (fun a b x y' => P x y' z (a, b, e))
            (fun a b x y' => hfin _ _ _ _ _ _)]
          congr 1
          unfold NoSignalPA.pairing
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y' _ => ?_
          ring
      _ = ∑ a, ∑ b, ∑ x, ∑ y',
            ENNReal.ofReal (((2 : ℝ) ^ Ns)⁻¹ * C * NoSignalPA.chshPow a b x y') *
              ∑' e : E, P x y' z₀ (a, b, e) := by
          rw [tsum_finset_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [tsum_finset_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [tsum_finset_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [tsum_finset_sum]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [ENNReal.tsum_mul_left, hNS.2.2 x y' z z₀ a b]
      _ = ENNReal.ofReal (((2 : ℝ) ^ Ns)⁻¹ * X) := by
          rw [← ofReal_sum4 _ hw (fun a b x y' => ∑' e : E, P x y' z₀ (a, b, e))
            (fun a b x y' => tsum_e_ne_top P x y' z₀ a b)]
          congr 1
          rw [hX]
          unfold NoSignalPA.pairing NoSignalPA.abMarg
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y' _ => ?_
          ring
  -- sum over the `2^Ns` keys
  have hX0 : 0 ≤ X := mul_nonneg hC (by
    unfold NoSignalPA.pairing
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun x _ =>
      Finset.sum_nonneg fun y' _ => mul_nonneg (chshPow_nonneg _ _ _ _) ENNReal.toReal_nonneg)
  calc _ ≤ ∑ _k : NoSignalPA.Str Ns, ENNReal.ofReal (((2 : ℝ) ^ Ns)⁻¹ * X) :=
        Finset.sum_le_sum fun k _ => iSup_le fun z => hz k z
    _ = ENNReal.ofReal X := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : (Fintype.card (NoSignalPA.Str Ns) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ Ns) := by
          rw [ENNReal.ofReal_pow (by norm_num)]
          simp [NoSignalPA.Str, Fintype.card_bool, Fintype.card_fin]
        rw [hcard, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
          mul_inv_cancel₀ (by positivity), one_mul]
