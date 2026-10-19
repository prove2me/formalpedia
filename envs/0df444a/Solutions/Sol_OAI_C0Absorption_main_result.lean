-- Prove2me | solution 1 for OAI.C0Absorption.main_result
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:18:56.22149+00:00
-- url     : https://prove2.me/submissions/0346bb34-3260-441b-acb5-299f4127a131

import Mathlib
import Definitions.Def_C0Absorption

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

section
section
namespace OAI

namespace C0Absorption

open scoped ZeroAtInfty

end C0Absorption

end OAI
end
end

section
section
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section Molecules

variable (S : Type*)

def MoleculeSpace : Submodule ℝ (S →₀ ℝ) :=
  (Finsupp.linearCombination ℝ (fun _ : S => (1 : ℝ))).ker

abbrev Molecule := MoleculeSpace S

noncomputable def pairing (f : S → ℝ) : Molecule S →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ f).comp (MoleculeSpace S).subtype

variable {S}

noncomputable def molecule (s t : S) : Molecule S :=
  ⟨Finsupp.single s 1 - Finsupp.single t 1, by
    simp [MoleculeSpace, LinearMap.mem_ker]⟩

@[simp] theorem pairing_molecule (f : S → ℝ) (s t : S) :
    pairing S f (molecule s t) = f s - f t := by
  simp [pairing, molecule]

@[simp] theorem pairing_const (c : ℝ) (m : Molecule S) :
    pairing S (fun _ => c) m = 0 := by
  have hm := m.property
  change (Finsupp.linearCombination ℝ (fun _ : S => (1 : ℝ))) m.val = 0 at hm
  simp only [Finsupp.linearCombination_apply, smul_eq_mul, mul_one] at hm
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul]
  rw [← Finsupp.sum_mul, hm, zero_mul]

theorem molecule_decomposition (m : Molecule S) (o : S) :
    m = ∑ s ∈ m.val.support, m.val s • molecule s o := by
  classical
  have hm := m.property
  change (Finsupp.linearCombination ℝ (fun _ : S => (1 : ℝ))) m.val = 0 at hm
  simp only [Finsupp.linearCombination_apply, smul_eq_mul, mul_one,
    Finsupp.sum] at hm
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, molecule, smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hm, zero_smul, sub_zero]
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum] using (Finsupp.sum_single m.val).symm

@[simp] theorem molecule_self (s : S) : molecule s s = 0 := by
  apply Subtype.ext
  simp [molecule]

theorem molecule_sub_molecule (s t o : S) : molecule s o - molecule t o = molecule s t := by
  apply Subtype.ext
  change (Finsupp.single s 1 - Finsupp.single o 1) -
    (Finsupp.single t 1 - Finsupp.single o 1) = Finsupp.single s 1 - Finsupp.single t 1
  abel

end Molecules

section TestLists

variable {S : Type*} [MetricSpace S]

structure AdmissibleList (L : Set (S → ℝ)) (C : ℝ≥0) where
  length : ℕ
  test : Fin length → S → ℝ
  mem : ∀ i, test i ∈ L
  signed_lipschitz : ∀ ε : Fin length → ℝ, (∀ i, |ε i| = 1) →
    LipschitzWith C (fun s => ∑ i, ε i * test i s)

def AdmissibleList.empty (L : Set (S → ℝ)) (C : ℝ≥0) : AdmissibleList L C where
  length := 0
  test := Fin.elim0
  mem i := Fin.elim0 i
  signed_lipschitz ε hε := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Fin.sum_univ_zero, dist_self]
    positivity

instance (L : Set (S → ℝ)) (C : ℝ≥0) : Nonempty (AdmissibleList L C) :=
  ⟨AdmissibleList.empty L C⟩

theorem AdmissibleList.sum_abs_sub_le {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (s t : S) :
    ∑ i, |l.test i s - l.test i t| ≤ C * dist s t := by
  classical
  let ε : Fin l.length → ℝ := fun i => if 0 ≤ l.test i s - l.test i t then 1 else -1
  have hε : ∀ i, |ε i| = 1 := by
    intro i
    dsimp [ε]
    split <;> norm_num
  have heq : ∀ i, ε i * (l.test i s - l.test i t) =
      |l.test i s - l.test i t| := by
    intro i
    dsimp [ε]
    split
    · simp [abs_of_nonneg, *]
    · simp [abs_of_neg (lt_of_not_ge ‹¬ 0 ≤ l.test i s - l.test i t›)]
  have h := (l.signed_lipschitz ε hε).dist_le_mul s t
  rw [Real.dist_eq, ← Finset.sum_sub_distrib] at h
  simp_rw [← mul_sub, heq] at h
  rwa [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h

theorem finite_lp_norm_le_sum {ι : Type*} [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : PiLp p (fun _ : ι => ℝ)) : ‖f‖ ≤ ∑ i, |f i| := by
  classical
  have heq : f = ∑ i, PiLp.single p (β := fun _ : ι => ℝ) i (f i) := by
    apply PiLp.ext
    intro j
    simp [← WithLp.toLp_sum, PiLp.single, Function.update, Pi.single]
  calc
    ‖f‖ = ‖∑ i, PiLp.single p (β := fun _ : ι => ℝ) i (f i)‖ := congrArg norm heq
    _ ≤ ∑ i, ‖PiLp.single p (β := fun _ : ι => ℝ) i (f i)‖ := norm_sum_le _ _
    _ = ∑ i, |f i| := by simp [PiLp.norm_single, Real.norm_eq_abs]

def AdmissibleList.eval {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) :
    Molecule S →ₗ[ℝ] PiLp p (fun _ : Fin l.length => ℝ) :=
  (WithLp.linearEquiv p ℝ _).symm.toLinearMap.comp
    (LinearMap.pi fun i => pairing S (l.test i))

@[simp] theorem AdmissibleList.eval_apply {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) (m : Molecule S) (i : Fin l.length) :
    (l.eval p m) i = pairing S (l.test i) m := rfl

def AdmissibleList.seminorm {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Seminorm ℝ (Molecule S) :=
  (normSeminorm ℝ (PiLp p (fun _ : Fin l.length => ℝ))).comp (l.eval p)

@[simp] theorem AdmissibleList.seminorm_apply {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : Molecule S) :
    l.seminorm p m = ‖l.eval p m‖ := rfl

theorem AdmissibleList.seminorm_molecule_le {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) [Fact (1 ≤ p)] (s t : S) :
    l.seminorm p (molecule s t) ≤ C * dist s t := by
  calc
    l.seminorm p (molecule s t) ≤ ∑ i, |(l.eval p (molecule s t)) i| :=
      finite_lp_norm_le_sum p _
    _ = ∑ i, |l.test i s - l.test i t| := by simp
    _ ≤ C * dist s t := l.sum_abs_sub_le s t

theorem AdmissibleList.seminorm_le {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) (m : Molecule S) :
    l.seminorm p m ≤ C * ∑ s ∈ m.val.support, |m.val s| * dist s o := by
  classical
  conv_lhs => rw [molecule_decomposition m o]
  simp only [AdmissibleList.seminorm_apply, map_sum, map_smul]
  calc
    ‖∑ s ∈ m.val.support, m.val s • l.eval p (molecule s o)‖
        ≤ ∑ s ∈ m.val.support, |m.val s| * ‖l.eval p (molecule s o)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using
        norm_sum_le m.val.support (fun s => m.val s • l.eval p (molecule s o))
    _ ≤ ∑ s ∈ m.val.support, |m.val s| * (C * dist s o) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (l.seminorm_molecule_le p s o) (abs_nonneg _)
    _ = C * ∑ s ∈ m.val.support, |m.val s| * dist s o := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring

def sigma (L : Set (S → ℝ)) (C : ℝ≥0) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Seminorm ℝ (Molecule S) :=
  ⨆ l : AdmissibleList L C, l.seminorm p

theorem list_seminorms_bddAbove (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) :
    BddAbove (Set.range fun l : AdmissibleList L C => l.seminorm p) := by
  rw [Seminorm.bddAbove_range_iff]
  intro m
  refine ⟨C * ∑ s ∈ m.val.support, |m.val s| * dist s o, ?_⟩
  rintro _ ⟨l, rfl⟩
  exact l.seminorm_le p o m

theorem sigma_apply (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) (m : Molecule S) :
    sigma L C p m = ⨆ l : AdmissibleList L C, ‖l.eval p m‖ := by
  exact Seminorm.iSup_apply (list_seminorms_bddAbove L C p o)

theorem sigma_molecule_le (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (s t : S) :
    sigma L C p (molecule s t) ≤ C * dist s t := by
  rw [sigma_apply L C p s]
  exact ciSup_le fun l => l.seminorm_molecule_le p s t

theorem list_le_sigma (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) (l : AdmissibleList L C) :
    l.seminorm p ≤ sigma L C p :=
  le_ciSup (list_seminorms_bddAbove L C p o) l

theorem sigma_le (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) (m : Molecule S) :
    sigma L C p m ≤ C * ∑ s ∈ m.val.support, |m.val s| * dist s o := by
  rw [sigma_apply L C p o]
  exact ciSup_le fun l => l.seminorm_le p o m

end TestLists

section SquareSum

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (q : ℕ → Seminorm ℝ M)
variable (hq : ∀ x, Summable (fun n => (q n x) ^ 2))

def squareVector (x : M) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun n => q n x, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
      using hq x)⟩

@[simp] theorem squareVector_apply (x : M) (n : ℕ) :
    squareVector q hq x n = q n x := rfl

def squareSeminorm : Seminorm ℝ M :=
  Seminorm.of (fun x => ‖squareVector q hq x‖)
    (by
      intro x y
      calc
        ‖squareVector q hq (x + y)‖ ≤ ‖squareVector q hq x + squareVector q hq y‖ := by
          apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          intro n
          change ‖q n (x + y)‖ ≤ ‖q n x + q n y‖
          rw [Real.norm_of_nonneg (apply_nonneg _ _),
            Real.norm_of_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))]
          exact map_add_le_add _ _ _
        _ ≤ ‖squareVector q hq x‖ + ‖squareVector q hq y‖ := norm_add_le _ _)
    (by
      intro a x
      have h : squareVector q hq (a • x) = ‖a‖ • squareVector q hq x := by
        apply lp.ext
        funext n
        change q n (a • x) = ‖a‖ * q n x
        exact map_smul_eq_mul _ _ _
      rw [h, norm_smul, norm_norm])

@[simp] theorem squareSeminorm_apply (x : M) :
    squareSeminorm q hq x = ‖squareVector q hq x‖ := rfl

theorem squareSeminorm_sq (x : M) :
    (squareSeminorm q hq x) ^ 2 = ∑' n, (q n x) ^ 2 := by
  simpa only [squareSeminorm_apply, ENNReal.toReal_ofNat, Real.rpow_two,
    Real.norm_eq_abs, sq_abs, squareVector_apply] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (squareVector q hq x)

theorem coordinate_le_squareSeminorm (n : ℕ) (x : M) :
    q n x ≤ squareSeminorm q hq x := by
  simpa only [squareSeminorm_apply, squareVector_apply,
    Real.norm_of_nonneg (apply_nonneg _ _)] using
    lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (squareVector q hq x) n

theorem seminorm_abs_sub_le (r : Seminorm ℝ M) (x y : M) :
    |r x - r y| ≤ r (x - y) := by
  have hxy := map_add_le_add r (x - y) y
  have hyx := map_add_le_add r (y - x) x
  rw [sub_add_cancel] at hxy hyx
  have hn : r (y - x) = r (x - y) := by rw [← neg_sub x y, map_neg_eq_map]
  rw [hn] at hyx
  apply abs_le.mpr
  constructor <;> linarith

theorem squareVector_sub_norm_le (x y : M) :
    ‖squareVector q hq x - squareVector q hq y‖ ≤ squareSeminorm q hq (x - y) := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  change ‖q n x - q n y‖ ≤ ‖q n (x - y)‖
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (apply_nonneg _ _)]
  exact seminorm_abs_sub_le _ _ _

end SquareSum

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section SelectedNorm

variable {S : Type*} [MetricSpace S]

def triple (n : ℕ) : ℕ × ℕ × ℕ :=
  ((Nat.unpair n).1, Nat.unpair (Nat.unpair n).2)

theorem triple_surjective : Function.Surjective triple := by
  rintro ⟨h, C, k⟩
  exact ⟨Nat.pair h (Nat.pair C k), by simp [triple]⟩

def listConstant (n : ℕ) : ℝ≥0 := (triple n).2.1 + 1

theorem listConstant_pos (n : ℕ) : 0 < listConstant n := by
  dsimp [listConstant]
  positivity

def listExponent (n : ℕ) : ℝ≥0∞ := 1 + ((triple n).2.2 + 1 : ℝ≥0∞)⁻¹

instance (n : ℕ) : Fact (1 ≤ listExponent n) := ⟨by simp [listExponent]⟩

theorem listExponent_ne_top (n : ℕ) : listExponent n ≠ ∞ := by
  simp [listExponent]

theorem listExponent_toReal (n : ℕ) :
    (listExponent n).toReal = 1 + 1 / ((triple n).2.2 + 1 : ℝ) := by
  simp [listExponent, ENNReal.toReal_add, one_div]

def alpha (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1) / (listConstant n : ℝ) ^ 2

theorem alpha_pos (n : ℕ) : 0 < alpha n := by
  have hC : 0 < (listConstant n : ℝ) := by exact_mod_cast listConstant_pos n
  dsimp [alpha]
  positivity

def squareWeight (n : ℕ) : ℝ≥0 :=
  ⟨Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) / (listConstant n : ℝ), by positivity⟩

theorem squareWeight_sq (n : ℕ) : (squareWeight n : ℝ) ^ 2 = alpha n := by
  change (Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) / (listConstant n : ℝ)) ^ 2 =
    (1 / 2 : ℝ) ^ (n + 1) / (listConstant n : ℝ) ^ 2
  rw [div_pow, Real.sq_sqrt (by positivity)]

theorem squareWeight_pos (n : ℕ) : 0 < (squareWeight n : ℝ) := by
  have h := alpha_pos n
  rw [← squareWeight_sq] at h
  have hn := (squareWeight n).coe_nonneg
  nlinarith

def selectedCoordinate (L : ℕ → Set (S → ℝ)) (n : ℕ) : Seminorm ℝ (Molecule S) :=
  squareWeight n • sigma (L (triple n).1) (listConstant n) (listExponent n)

theorem selectedCoordinate_apply (L : ℕ → Set (S → ℝ)) (n : ℕ) (m : Molecule S) :
    selectedCoordinate L n m = (squareWeight n : ℝ) *
      sigma (L (triple n).1) (listConstant n) (listExponent n) m := rfl

theorem weighted_bound (n : ℕ) (a b : ℝ) (h : a ≤ (listConstant n : ℝ) * b) :
    (squareWeight n : ℝ) * a ≤ Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) * b := by
  have hC : (listConstant n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast listConstant_pos n)
  have h' := mul_le_mul_of_nonneg_left h (squareWeight n).coe_nonneg
  calc
    (squareWeight n : ℝ) * a ≤
      (Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) / (listConstant n : ℝ)) *
        ((listConstant n : ℝ) * b) := h'
    _ = Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) * b := by field_simp

theorem selectedCoordinate_bound (L : ℕ → Set (S → ℝ)) (o : S) (n : ℕ) (m : Molecule S) :
    selectedCoordinate L n m ≤ Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) *
      ∑ s ∈ m.val.support, |m.val s| * dist s o := by
  exact weighted_bound n _ _
    (sigma_le (L (triple n).1) (listConstant n) (listExponent n) o m)

theorem geometric_summable : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
  simpa only [pow_succ] using
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)

theorem geometric_tsum : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem selectedCoordinate_summable (L : ℕ → Set (S → ℝ)) (o : S) (m : Molecule S) :
    Summable (fun n => (selectedCoordinate L n m) ^ 2) := by
  classical
  let b := ∑ s ∈ m.val.support, |m.val s| * dist s o
  have hb : 0 ≤ b := Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) dist_nonneg)
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (geometric_summable.mul_right (b ^ 2))
  intro n
  calc
    (selectedCoordinate L n m) ^ 2 ≤ (Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) * b) ^ 2 := by
      apply pow_le_pow_left₀ (apply_nonneg _ _) (selectedCoordinate_bound L o n m)
    _ = (1 / 2 : ℝ) ^ (n + 1) * b ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]

def selectedNorm (L : ℕ → Set (S → ℝ)) (o : S) : Seminorm ℝ (Molecule S) :=
  squareSeminorm (selectedCoordinate L) (selectedCoordinate_summable L o)

theorem selectedNorm_sq (L : ℕ → Set (S → ℝ)) (o : S) (m : Molecule S) :
    (selectedNorm L o m) ^ 2 = ∑' n, alpha n *
      (sigma (L (triple n).1) (listConstant n) (listExponent n) m) ^ 2 := by
  rw [selectedNorm, squareSeminorm_sq]
  apply tsum_congr
  intro n
  rw [selectedCoordinate_apply, mul_pow, squareWeight_sq]

theorem selectedNorm_molecule_le (L : ℕ → Set (S → ℝ)) (o s t : S) :
    selectedNorm L o (molecule s t) ≤ dist s t := by
  have hh : ∀ n, (selectedCoordinate L n (molecule s t)) ^ 2 ≤
      (1 / 2 : ℝ) ^ (n + 1) * (dist s t) ^ 2 := by
    intro n
    have h := weighted_bound n _ _
      (sigma_molecule_le (L (triple n).1) (listConstant n) (listExponent n) s t)
    calc
      (selectedCoordinate L n (molecule s t)) ^ 2
          ≤ (Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) * dist s t) ^ 2 :=
        pow_le_pow_left₀ (apply_nonneg _ _) h 2
      _ = (1 / 2 : ℝ) ^ (n + 1) * dist s t ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsq : (selectedNorm L o (molecule s t)) ^ 2 ≤ dist s t ^ 2 := by
    rw [selectedNorm, squareSeminorm_sq]
    calc
      ∑' n, (selectedCoordinate L n (molecule s t)) ^ 2
          ≤ ∑' n, (1 / 2 : ℝ) ^ (n + 1) * dist s t ^ 2 :=
        Summable.tsum_le_tsum hh (selectedCoordinate_summable L o _)
          (geometric_summable.mul_right _)
      _ = dist s t ^ 2 := by rw [tsum_mul_right, geometric_tsum, one_mul]
  nlinarith [apply_nonneg (selectedNorm L o) (molecule s t), dist_nonneg (x := s) (y := t)]

end SelectedNorm

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedSeminorms

open UniformSpace Completion

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

theorem seminorm_lipschitz (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) : LipschitzWith C q := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact (seminorm_abs_sub_le q x y).trans (h (x - y))

theorem completion_lipschitz {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {f : X → Y} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (Completion.extension f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x y =>
    simpa only [Completion.extension_coe hf.uniformContinuous, Completion.dist_eq] using hf.dist_le_mul x y

def completedSeminorm (q : Seminorm ℝ X) (C : ℝ≥0) (h : ∀ x, q x ≤ C * ‖x‖) :
    Seminorm ℝ (Completion X) :=
  Seminorm.of (Completion.extension q)
    (by
      intro x y
      induction x, y using Completion.induction_on₂ with
      | hp =>
        exact isClosed_le
          (Completion.continuous_extension.comp (continuous_fst.add continuous_snd))
          ((Completion.continuous_extension.comp continuous_fst).add
            (Completion.continuous_extension.comp continuous_snd))
      | ih x y =>
        simpa only [← Completion.coe_add,
          Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous] using
          map_add_le_add q x y)
    (by
      intro a x
      induction x using Completion.induction_on with
      | hp =>
        exact isClosed_eq
          (Completion.continuous_extension.comp (continuous_const_smul a))
          (continuous_const.mul Completion.continuous_extension)
      | ih x =>
        simpa only [← Completion.coe_smul,
          Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous] using
          map_smul_eq_mul q a x)

@[simp] theorem completedSeminorm_coe (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) (x : X) : completedSeminorm q C h (x : Completion X) = q x :=
  Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous x

theorem completedSeminorm_continuous (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) : Continuous (completedSeminorm q C h) :=
  Completion.continuous_extension

theorem completedSeminorm_le (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) (x : Completion X) : completedSeminorm q C h x ≤ C * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (completedSeminorm_continuous q C h) (by fun_prop)
  | ih x => simpa using h x

end CompletedSeminorms

section SelectedCompletion

open UniformSpace Completion

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def PreSpace (_L : ℕ → Set (S → ℝ)) (_o : S) : Type _ := Molecule S

instance : SeminormedAddCommGroup (PreSpace L o) :=
  (selectedNorm L o).toAddGroupSeminorm.toSeminormedAddCommGroup
instance : NormedSpace ℝ (PreSpace L o) where
  __ : Module ℝ (PreSpace L o) := inferInstanceAs (Module ℝ (Molecule S))
  norm_smul_le a x := by
    change selectedNorm L o (a • x) ≤ ‖a‖ * selectedNorm L o x
    exact (map_smul_eq_mul (selectedNorm L o) a x).le

instance : IsBoundedSMul ℝ (PreSpace L o) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := PreSpace L o)

def TestSpace := Completion (PreSpace L o)

instance : NormedAddCommGroup (TestSpace L o) :=
  inferInstanceAs (NormedAddCommGroup (Completion (PreSpace L o)))
instance : NormedSpace ℝ (TestSpace L o) :=
  inferInstanceAs (NormedSpace ℝ (Completion (PreSpace L o)))
instance : CompleteSpace (TestSpace L o) :=
  inferInstanceAs (CompleteSpace (Completion (PreSpace L o)))

def toTestSpace : PreSpace L o →L[ℝ] TestSpace L o :=
  (Completion.toComplL : PreSpace L o →L[ℝ] Completion (PreSpace L o))

@[simp] theorem norm_toTestSpace (m : PreSpace L o) :
    ‖toTestSpace L o m‖ = selectedNorm L o m := Completion.norm_coe m

def initialCoordinates (m : PreSpace L o) : lp (fun _ : ℕ => ℝ) 2 :=
  squareVector (selectedCoordinate L) (selectedCoordinate_summable L o) m

theorem initialCoordinates_lipschitz : LipschitzWith 1 (initialCoordinates L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact squareVector_sub_norm_le (selectedCoordinate L) (selectedCoordinate_summable L o) x y

def normCoordinates : TestSpace L o → lp (fun _ : ℕ => ℝ) 2 :=
  Completion.extension (initialCoordinates L o)

theorem normCoordinates_continuous : Continuous (normCoordinates L o) :=
  Completion.continuous_extension

@[simp] theorem normCoordinates_coe (m : PreSpace L o) :
    normCoordinates L o (toTestSpace L o m) = initialCoordinates L o m :=
  Completion.extension_coe (initialCoordinates_lipschitz L o).uniformContinuous m

theorem normCoordinates_norm (z : TestSpace L o) : ‖normCoordinates L o z‖ = ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (normCoordinates_continuous L o).norm continuous_norm
  | ih m =>
    change ‖normCoordinates L o (toTestSpace L o m)‖ = ‖toTestSpace L o m‖
    rw [normCoordinates_coe, norm_toTestSpace]
    rfl

theorem selectedCoordinate_le_norm (n : ℕ) (m : PreSpace L o) :
    selectedCoordinate L n m ≤ (1 : ℝ≥0) * ‖m‖ := by
  change selectedCoordinate L n m ≤ (1 : ℝ) * selectedNorm L o m
  rw [one_mul]
  exact coordinate_le_squareSeminorm (selectedCoordinate L) (selectedCoordinate_summable L o) n m

def completedCoordinate (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  completedSeminorm (X := PreSpace L o) (selectedCoordinate L n) 1
    (selectedCoordinate_le_norm L o n)

theorem completedCoordinate_continuous (n : ℕ) : Continuous (completedCoordinate L o n) :=
  completedSeminorm_continuous _ _ _

@[simp] theorem completedCoordinate_coe (n : ℕ) (m : PreSpace L o) :
    completedCoordinate L o n (toTestSpace L o m) = selectedCoordinate L n m :=
  completedSeminorm_coe _ _ _ m

theorem normCoordinates_apply (z : TestSpace L o) (n : ℕ) :
    normCoordinates L o z n = completedCoordinate L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((lp.lipschitzWith_one_eval 2 n).continuous.comp (normCoordinates_continuous L o))
      (completedCoordinate_continuous L o n)
  | ih m =>
    change normCoordinates L o (toTestSpace L o m) n =
      completedCoordinate L o n (toTestSpace L o m)
    rw [normCoordinates_coe, completedCoordinate_coe]
    rfl

theorem completedCoordinate_summable (z : TestSpace L o) :
    Summable (fun n => (completedCoordinate L o n z) ^ 2) := by
  have h := (lp.memℓp (normCoordinates L o z)).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    normCoordinates_apply] using h

theorem completedNorm_sq (z : TestSpace L o) :
    ‖z‖ ^ 2 = ∑' n, (completedCoordinate L o n z) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (normCoordinates L o z)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    normCoordinates_norm, normCoordinates_apply] using h

def prePoint (s : S) : PreSpace L o := molecule s o

theorem prePoint_lipschitz : LipschitzWith 1 (prePoint L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  change selectedNorm L o (molecule s o - molecule t o) ≤ (1 : ℝ) * dist s t
  rw [molecule_sub_molecule, one_mul]
  exact selectedNorm_molecule_le L o s t

theorem prePoint_span : Submodule.span ℝ (Set.range (prePoint L o)) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro m
  have heq : m = ∑ s ∈ m.val.support, m.val s • prePoint L o s := molecule_decomposition m o
  rw [heq]
  apply Submodule.sum_mem
  intro s hs
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

instance [TopologicalSpace.SeparableSpace S] : TopologicalSpace.SeparableSpace (PreSpace L o) := by
  have hsep := (TopologicalSpace.isSeparable_range (prePoint_lipschitz L o).continuous).span (R := ℝ)
  rw [prePoint_span, Submodule.top_coe] at hsep
  exact TopologicalSpace.isSeparable_univ_iff.mp hsep

instance [TopologicalSpace.SeparableSpace S] : TopologicalSpace.SeparableSpace (TestSpace L o) :=
  inferInstanceAs (TopologicalSpace.SeparableSpace (Completion (PreSpace L o)))

def zeta (s : S) : TestSpace L o := toTestSpace L o (prePoint L o s)

@[simp] theorem zeta_base : zeta L o o = 0 := by
  have h : prePoint L o o = (0 : PreSpace L o) := molecule_self o
  rw [zeta, h, map_zero]

theorem zeta_lipschitz : LipschitzWith 1 (zeta L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist ((prePoint L o s : PreSpace L o) : Completion (PreSpace L o))
    ((prePoint L o t : PreSpace L o) : Completion (PreSpace L o)) ≤ (1 : ℝ) * dist s t
  rw [Completion.dist_eq]
  exact (prePoint_lipschitz L o).dist_le_mul s t

end SelectedCompletion

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section Signs

def realSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem realSign_true : realSign true = 1 := rfl
@[simp] theorem realSign_false : realSign false = -1 := rfl
@[simp] theorem abs_realSign (b : Bool) : |realSign b| = 1 := by cases b <;> norm_num

theorem sum_sign_sq (n : ℕ) (a : Fin n → ℝ) :
    ∑ ε : Fin n → Bool, (∑ i, realSign (ε i) * a i) ^ 2 =
      (2 : ℝ) ^ n * ∑ i, a i ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
      (fun p : Bool × (Fin n → Bool) =>
        (∑ i : Fin (n + 1), realSign ((Fin.consEquiv (fun _ => Bool)) p i) * a i) ^ 2)
      (fun ε : Fin (n + 1) → Bool => (∑ i, realSign (ε i) * a i) ^ 2)
      (fun _ => rfl)]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ, Fintype.sum_bool, realSign_true, realSign_false,
      one_mul, neg_one_mul]
    rw [← Finset.sum_add_distrib]
    have heq (x y : ℝ) : (x + y) ^ 2 + (-x + y) ^ 2 = 2 * x ^ 2 + 2 * y ^ 2 := by ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, ih]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    ring

theorem finite_detector_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) (m : Fin n → X) (u : Fin n → X →ₗ[ℝ] ℝ)
    (α M δ : ℝ) (hα : 0 ≤ α) (_hM : 0 ≤ M)
    (hsum : ∀ ε : Fin n → Bool, ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hdual : ∀ x, α * ∑ k, (u k x) ^ 2 ≤ ‖x‖ ^ 2)
    (hdetect : ∀ i, δ ^ 2 ≤ (u i (m i)) ^ 2) :
    α * (n : ℝ) * δ ^ 2 ≤ M ^ 2 := by
  classical
  have hdiag : (n : ℝ) * δ ^ 2 ≤ ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2 := by
    calc
      (n : ℝ) * δ ^ 2 = ∑ k : Fin n, δ ^ 2 := by simp
      _ ≤ ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hdetect k).trans (Finset.single_le_sum (fun i _ => sq_nonneg (u k (m i))) (mem_univ k))
  have havg : (2 : ℝ) ^ n * (α * ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) ≤
      (2 : ℝ) ^ n * M ^ 2 := by
    calc
      (2 : ℝ) ^ n * (α * ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) =
          ∑ ε : Fin n → Bool, α * ∑ k : Fin n,
            (u k (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := by
        simp only [map_sum, map_smul, smul_eq_mul]
        conv_rhs => rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [sum_sign_sq]
        rw [← Finset.mul_sum]
        ring
      _ ≤ ∑ ε : Fin n → Bool, M ^ 2 := by
        apply Finset.sum_le_sum
        intro ε hε
        exact (hdual _).trans (pow_le_pow_left₀ (norm_nonneg _) (hsum ε) 2)
      _ = (2 : ℝ) ^ n * M ^ 2 := by
        simp
  have ht : α * (∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) ≤ M ^ 2 :=
    le_of_mul_le_mul_left havg (by positivity)
  calc
    α * (n : ℝ) * δ ^ 2 = α * ((n : ℝ) * δ ^ 2) := by ring
    _ ≤ α * (∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiag hα
    _ ≤ M ^ 2 := ht

theorem no_infinite_detectors {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (u : ℕ → X →ₗ[ℝ] ℝ) (α M δ : ℝ)
    (hα : 0 < α) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hdual : ∀ n x, α * ∑ k : Fin n, (u k x) ^ 2 ≤ ‖x‖ ^ 2)
    (hdetect : ∀ i, δ ≤ |u i (m i)|) : False := by
  have hbound (n : ℕ) : α * (n : ℝ) * δ ^ 2 ≤ M ^ 2 := by
    apply finite_detector_bound n (fun i => m i) (fun i => u i) α M δ hα.le hM
      (hsum n) (hdual n)
    intro i
    simpa only [sq_abs] using pow_le_pow_left₀ hδ.le (hdetect i) 2
  obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 2 / (α * δ ^ 2))
  have hpos : 0 < α * δ ^ 2 := mul_pos hα (sq_pos_of_pos hδ)
  have hn' : M ^ 2 < (n : ℝ) * (α * δ ^ 2) := (div_lt_iff₀ hpos).mp hn
  nlinarith [hbound n]

def flipSign {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun ε j := if j = i then !(ε j) else ε j
  invFun ε j := if j = i then !(ε j) else ε j
  left_inv ε := by funext j; by_cases h : j = i <;> simp [h]
  right_inv ε := by funext j; by_cases h : j = i <;> simp [h]

@[simp] theorem realSign_not (b : Bool) : realSign (!b) = -realSign b := by
  cases b <;> norm_num

theorem signed_sum_sub_flip {X : Type*} [AddCommGroup X] [Module ℝ X]
    {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    (∑ j, realSign (ε j) • m j) - (∑ j, realSign (flipSign i ε j) • m j) =
      (2 * realSign (ε i)) • m i := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp [flipSign, two_mul, add_smul]
  · intro j hj hji
    simp [flipSign, hji]
  · simp

theorem seminorm_sign_pair {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    2 * (q (m i)) ^ 2 ≤
      (q (∑ j, realSign (ε j) • m j)) ^ 2 +
      (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2 := by
  have heq : q ((∑ j, realSign (ε j) • m j) -
      (∑ j, realSign (flipSign i ε j) • m j)) = 2 * q (m i) := by
    rw [signed_sum_sub_flip, map_smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_realSign]
    norm_num
  have ht := map_add_le_add q
    (∑ j, realSign (ε j) • m j) (-(∑ j, realSign (flipSign i ε j) • m j))
  rw [← sub_eq_add_neg, heq, map_neg_eq_map] at ht
  have hp := apply_nonneg q (m i)
  have ha := apply_nonneg q (∑ j, realSign (ε j) • m j)
  have hb := apply_nonneg q (∑ j, realSign (flipSign i ε j) • m j)
  nlinarith [sq_nonneg (q (∑ j, realSign (ε j) • m j) -
    q (∑ j, realSign (flipSign i ε j) • m j))]

theorem sum_sign_seminorm_sq_ge {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (i : Fin n) :
    (2 : ℝ) ^ n * (q (m i)) ^ 2 ≤
      ∑ ε : Fin n → Bool, (q (∑ j, realSign (ε j) • m j)) ^ 2 := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ε _ => seminorm_sign_pair q m ε i)
  rw [Finset.sum_add_distrib] at h
  have heq : (∑ ε : Fin n → Bool, (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2) =
      ∑ ε : Fin n → Bool, (q (∑ j, realSign (ε j) • m j)) ^ 2 :=
    Fintype.sum_equiv (flipSign i) _ _ (fun _ => rfl)
  rw [heq] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  linarith

theorem sum_coordinate_choice_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hdom : ∀ (s : Finset ℕ) x, ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (s : Finset ℕ) (index : ℕ → ℕ) :
    ∑ d ∈ s, (q d (m (index d))) ^ 2 ≤ M ^ 2 := by
  classical
  let n := s.sup index + 1
  have hlt (d : ℕ) (hd : d ∈ s) : index d < n :=
    Nat.lt_succ_of_le (Finset.le_sup hd)
  have hmain : (2 : ℝ) ^ n * (∑ d ∈ s, (q d (m (index d))) ^ 2) ≤
      (2 : ℝ) ^ n * M ^ 2 := by
    calc
      (2 : ℝ) ^ n * (∑ d ∈ s, (q d (m (index d))) ^ 2) =
          ∑ d ∈ s, (2 : ℝ) ^ n * (q d (m (index d))) ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ d ∈ s, ∑ ε : Fin n → Bool,
          (q d (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        exact sum_sign_seminorm_sq_ge (q d) (fun i : Fin n => m i) ⟨index d, hlt d hd⟩
      _ = ∑ ε : Fin n → Bool, ∑ d ∈ s,
          (q d (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := Finset.sum_comm
      _ ≤ ∑ ε : Fin n → Bool, M ^ 2 := by
        apply Finset.sum_le_sum
        intro ε hε
        exact (hdom s _).trans (pow_le_pow_left₀ (norm_nonneg _) (hsum n ε) 2)
      _ = (2 : ℝ) ^ n * M ^ 2 := by simp
  exact le_of_mul_le_mul_left hmain (by positivity)

theorem sum_ciSup_le_of_forall_choice {ι κ : Type*} [Nonempty κ]
    (a : ι → κ → ℝ) (s : Finset ι) (K : ℝ)
    (h : ∀ f : ι → κ, ∑ d ∈ s, a d (f d) ≤ K) :
    ∑ d ∈ s, ⨆ k, a d k ≤ K := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => simpa using h (fun _ => Classical.choice (inferInstance : Nonempty κ))
  | @insert d s hd ih =>
    rw [Finset.sum_insert hd]
    rw [← le_sub_iff_add_le]
    apply ciSup_le
    intro k
    have ht : (∑ e ∈ s, ⨆ j, a e j) ≤ K - a d k := by
      apply ih
      intro f
      have hf := h (Function.update f d k)
      rw [Finset.sum_insert hd, Function.update_self] at hf
      have heq : (∑ e ∈ s, a e (Function.update f d k e)) = ∑ e ∈ s, a e (f e) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Function.update_of_ne (by intro heq; subst e; exact hd he)]
      rw [heq] at hf
      linarith
    linarith

theorem coordinate_envelope_summable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hdom : ∀ (s : Finset ℕ) x, ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    Summable (fun d => ⨆ i : ℕ, (q d (m i)) ^ 2) ∧
      (∀ d i, (q d (m i)) ^ 2 ≤ ⨆ j : ℕ, (q d (m j)) ^ 2) := by
  have hb (d : ℕ) : BddAbove (Set.range (fun i : ℕ => (q d (m i)) ^ 2)) := by
    refine ⟨M ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    simpa using sum_coordinate_choice_le q hdom m M hsum {d} (fun _ => i)
  have hle (d i : ℕ) : (q d (m i)) ^ 2 ≤ ⨆ j : ℕ, (q d (m j)) ^ 2 :=
    le_ciSup (hb d) i
  constructor
  · apply summable_of_sum_le (c := M ^ 2)
    · intro d
      exact (sq_nonneg _).trans (hle d 0)
    · intro s
      apply sum_ciSup_le_of_forall_choice (fun d i => (q d (m i)) ^ 2)
      exact fun f => sum_coordinate_choice_le q hdom m M hsum s f
  · exact hle

theorem square_norm_tendsto_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hq : ∀ x, Summable (fun d => (q d x) ^ 2))
    (hnorm : ∀ x, ‖x‖ ^ 2 = ∑' d, (q d x) ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hzero : ∀ d, Filter.Tendsto (fun i => q d (m i)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun i => ‖m i‖ ^ 2) Filter.atTop (nhds 0) := by
  have hdom (s : Finset ℕ) (x : X) : ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hnorm]
    exact Summable.sum_le_tsum s (fun _ _ => sq_nonneg _) (hq x)
  obtain ⟨hb, hle⟩ := coordinate_envelope_summable q hdom m M hsum
  have hp (d : ℕ) : Filter.Tendsto (fun i => (q d (m i)) ^ 2) Filter.atTop (nhds 0) := by
    simpa using (hzero d).pow 2
  have ht := tendsto_tsum_of_dominated_convergence hb hp
    (Filter.Eventually.of_forall fun i d => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hle d i)
  simpa only [← hnorm, tsum_zero] using ht

theorem exists_nonzero_coordinate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hq : ∀ x, Summable (fun d => (q d x) ^ 2))
    (hnorm : ∀ x, ‖x‖ ^ 2 = ∑' d, (q d x) ^ 2)
    (m : ℕ → X) (M r : ℝ) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    ∃ d, ¬ Filter.Tendsto (fun i => q d (m i)) Filter.atTop (nhds 0) := by
  by_contra! h
  have ht := square_norm_tendsto_zero q hq hnorm m M hsum h
  have hl : r ^ 2 ≤ (0 : ℝ) := ge_of_tendsto ht
    (Filter.Eventually.of_forall fun i => pow_le_pow_left₀ hr.le (hlower i) 2)
  nlinarith [sq_pos_of_pos hr]

end Signs

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedLists

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def completedSigma (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  (squareWeight n)⁻¹ • completedCoordinate L o n

@[simp] theorem completedSigma_coe (n : ℕ) (m : PreSpace L o) :
    completedSigma L o n (toTestSpace L o m) =
      sigma (L (triple n).1) (listConstant n) (listExponent n) m := by
  simp only [completedSigma, smul_apply, NNReal.smul_def, NNReal.coe_inv,
    completedCoordinate_coe, smul_eq_mul]
  change (squareWeight n : ℝ)⁻¹ * ((squareWeight n : ℝ) *
    sigma (L (triple n).1) (listConstant n) (listExponent n) m) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul]

theorem completedSigma_continuous (n : ℕ) : Continuous (completedSigma L o n) :=
  continuous_const.mul (completedCoordinate_continuous L o n)

theorem sigma_le_preNorm (n : ℕ) (m : PreSpace L o) :
    sigma (L (triple n).1) (listConstant n) (listExponent n) m ≤
      (squareWeight n : ℝ)⁻¹ * ‖m‖ := by
  have h := selectedCoordinate_le_norm L o n m
  change (squareWeight n : ℝ) *
    sigma (L (triple n).1) (listConstant n) (listExponent n) m ≤ 1 * ‖m‖ at h
  rw [one_mul] at h
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (squareWeight n).coe_nonneg)
  simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul] using hm

theorem completedSigma_le (n : ℕ) (z : TestSpace L o) :
    completedSigma L o n z ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (completedSigma_continuous L o n) (by fun_prop)
  | ih m =>
    change completedSigma L o n (toTestSpace L o m) ≤
      (squareWeight n : ℝ)⁻¹ * ‖toTestSpace L o m‖
    rw [completedSigma_coe, norm_toTestSpace]
    exact sigma_le_preNorm L o n m

def initialList (n : ℕ) (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    PreSpace L o →L[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) :=
  (show PreSpace L o →ₗ[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) from
    l.eval (listExponent n)).mkContinuous (squareWeight n : ℝ)⁻¹ (fun m => by
      exact (list_le_sigma _ _ _ o l m).trans (sigma_le_preNorm L o n m))

def completedList (n : ℕ) (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    TestSpace L o →L[ℝ] PiLp (listExponent n) (fun _ : Fin l.length => ℝ) :=
  (initialList L o n l).extend (toTestSpace L o)

@[simp] theorem completedList_coe (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (m : PreSpace L o) :
    completedList L o n l (toTestSpace L o m) = l.eval (listExponent n) m :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (PreSpace L o)) m

theorem completedList_le_sigma (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (z : TestSpace L o) :
    ‖completedList L o n l z‖ ≤ completedSigma L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_le (completedList L o n l).continuous.norm
      (completedSigma_continuous L o n)
  | ih m =>
    change ‖completedList L o n l (toTestSpace L o m)‖ ≤
      completedSigma L o n (toTestSpace L o m)
    rw [completedList_coe, completedSigma_coe]
    exact list_le_sigma _ _ _ o l m

def completedListNorm (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) : Seminorm ℝ (TestSpace L o) :=
  (normSeminorm ℝ _).comp (completedList L o n l).toLinearMap

theorem completedListNorm_bddAbove (n : ℕ) :
    BddAbove (Set.range (completedListNorm L o n)) := by
  refine ⟨completedSigma L o n, ?_⟩
  rintro _ ⟨l, rfl⟩ z
  exact completedList_le_sigma L o n l z

def sigmaFromLists (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  ⨆ l, completedListNorm L o n l

theorem sigmaFromLists_le (n : ℕ) (z : TestSpace L o) :
    sigmaFromLists L o n z ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖ := by
  rw [sigmaFromLists, Seminorm.iSup_apply (completedListNorm_bddAbove L o n)]
  exact ciSup_le fun l => (completedList_le_sigma L o n l z).trans
    (completedSigma_le L o n z)

theorem sigmaFromLists_eq (n : ℕ) (z : TestSpace L o) :
    sigmaFromLists L o n z = completedSigma L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq (seminorm_lipschitz (sigmaFromLists L o n) ((squareWeight n)⁻¹)
      (sigmaFromLists_le L o n)).continuous (completedSigma_continuous L o n)
  | ih m =>
    change sigmaFromLists L o n (toTestSpace L o m) =
      completedSigma L o n (toTestSpace L o m)
    rw [sigmaFromLists, Seminorm.iSup_apply (completedListNorm_bddAbove L o n),
      completedSigma_coe]
    refine Eq.trans ?_ (sigma_apply _ _ _ o (show Molecule S from m)).symm
    apply congrArg iSup
    funext l
    exact congrArg norm (completedList_coe L o n l m)

theorem completedSigma_eq_iSup (n : ℕ) (z : TestSpace L o) :
    completedSigma L o n z =
      ⨆ l : AdmissibleList (L (triple n).1) (listConstant n), ‖completedList L o n l z‖ := by
  rw [← sigmaFromLists_eq, sigmaFromLists,
    Seminorm.iSup_apply (completedListNorm_bddAbove L o n)]
  rfl

end CompletedLists

section InterpolationAndDenseLimits

 theorem finite_lp_norm_rpow {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (hp : 0 < p.toReal) (x : PiLp p (fun _ : ι => ℝ)) :
    ‖x‖ ^ p.toReal = ∑ i, |x i| ^ p.toReal := by
  rw [PiLp.norm_eq_sum hp, ← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [Real.norm_eq_abs]

 theorem finite_lp_interpolation {ι : Type*} [Fintype ι]
    (p q : ℝ≥0∞) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (hqp : q.toReal < p.toReal) (x : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, |x i| ≤ δ) :
    ‖WithLp.toLp p x‖ ^ p.toReal ≤
      δ ^ (p.toReal - q.toReal) * ‖WithLp.toLp q x‖ ^ q.toReal := by
  rw [finite_lp_norm_rpow p hp, finite_lp_norm_rpow q hq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change |x i| ^ p.toReal ≤ δ ^ (p.toReal - q.toReal) * |x i| ^ q.toReal
  calc
    |x i| ^ p.toReal = |x i| ^ (p.toReal - q.toReal) * |x i| ^ q.toReal := by
      rw [← Real.rpow_add' (abs_nonneg _) (by simpa using hp.ne'), sub_add_cancel]
    _ ≤ δ ^ (p.toReal - q.toReal) * |x i| ^ q.toReal := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (abs_nonneg _) (hδ i) (sub_nonneg.mpr hqp.le))
        (Real.rpow_nonneg (abs_nonneg _) _)

theorem exists_uniform_lp_detector (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hqp : q.toReal < p.toReal)
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : Fin n → ℝ),
      a ≤ ‖WithLp.toLp p x‖ → ‖WithLp.toLp q x‖ ≤ B →
      ∃ i, δ < |x i| := by
  let A := a ^ p.toReal
  let D := B ^ q.toReal
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hD : 0 < D := Real.rpow_pos_of_pos hB _
  have hs : 0 < p.toReal - q.toReal := sub_pos.mpr hqp
  let δ := (A / (2 * D)) ^ (1 / (p.toReal - q.toReal))
  have hδ : 0 < δ := Real.rpow_pos_of_pos (div_pos hA (mul_pos (by norm_num) hD)) _
  have hpow : δ ^ (p.toReal - q.toReal) = A / (2 * D) := by
    rw [show δ = (A / (2 * D)) ^ (1 / (p.toReal - q.toReal)) from rfl,
      ← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
  refine ⟨δ, hδ, ?_⟩
  intro n x hlow hupp
  by_contra! hnone
  have hint := finite_lp_interpolation p q hp hq hqp x δ hnone
  have hlu : A ≤ ‖WithLp.toLp p x‖ ^ p.toReal := Real.rpow_le_rpow ha.le hlow hp.le
  have huu : ‖WithLp.toLp q x‖ ^ q.toReal ≤ D :=
    Real.rpow_le_rpow (norm_nonneg _) hupp hq.le
  have hb := mul_le_mul_of_nonneg_left huu (Real.rpow_nonneg hδ.le (p.toReal - q.toReal))
  rw [hpow] at hint hb
  have heq : A / (2 * D) * D = A / 2 := by field_simp [ne_of_gt hD]
  rw [heq] at hb
  linarith

theorem tendsto_of_dense_lipschitz {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (d : A → X) (hd : DenseRange d) (f : ℕ → X → Y) (g : X → Y) (K : ℝ≥0)
    (hf : ∀ n, LipschitzWith K (f n)) (hg : LipschitzWith K g)
    (h : ∀ a, Filter.Tendsto (fun n => f n (d a)) Filter.atTop (nhds (g (d a))))
    (x : X) : Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hK : 0 < 3 * ((K : ℝ) + 1) := by positivity
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x (div_pos hε hK)
  have hδ : (K : ℝ) * dist x (d a) < ε / 3 := by
    have hr := (lt_div_iff₀ hK).mp ha
    have hn := dist_nonneg (x := x) (y := d a)
    nlinarith
  filter_upwards [Metric.tendsto_nhds.mp (h a) (ε / 3) (by positivity)] with n hn
  have h₁ := (hf n).dist_le_mul x (d a)
  have h₂ := hg.dist_le_mul (d a) x
  rw [dist_comm (d a) x] at h₂
  have ht := dist_triangle4 (f n x) (f n (d a)) (g (d a)) (g x)
  linarith

end InterpolationAndDenseLimits

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedPairings

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def completedPairing (f : S → ℝ) : TestSpace L o → ℝ :=
  Completion.extension (fun m : PreSpace L o => pairing S f m)

def initialPairing (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) : PreSpace L o →L[ℝ] ℝ :=
  (show PreSpace L o →ₗ[ℝ] ℝ from pairing S f).mkContinuous (E := PreSpace L o) K
    (fun m => h m)

theorem initialPairing_lipschitz (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) :
    LipschitzWith K (fun m : PreSpace L o => pairing S f m) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let T := initialPairing L o f K h
  change dist (T x) (T y) ≤ K * dist x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact h (x-y)

@[simp] theorem completedPairing_coe (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) (m : PreSpace L o) :
    completedPairing L o f (toTestSpace L o m) = pairing S f m :=
  Completion.extension_coe (initialPairing_lipschitz L o f K h).uniformContinuous m

theorem completedPairing_lipschitz (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) :
    LipschitzWith K (completedPairing L o f) :=
  completion_lipschitz (initialPairing_lipschitz L o f K h)

def completedTest (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) : TestSpace L o →L[ℝ] ℝ :=
  (initialPairing L o f K h).extend (toTestSpace L o)

theorem completedTest_eq (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) (z : TestSpace L o) :
    completedTest L o f K h z = completedPairing L o f z := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (completedTest L o f K h).continuous Completion.continuous_extension
  | ih m =>
    change (initialPairing L o f K h).extend (toTestSpace L o) (toTestSpace L o m) =
      completedPairing L o f (toTestSpace L o m)
    rw [ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
      (Completion.isUniformInducing_coe (PreSpace L o)), completedPairing_coe L o f K h]
    rfl

def AdmissibleList.singleton {L₀ : Set (S → ℝ)} {C : ℝ≥0}
    (f : S → ℝ) (hf : f ∈ L₀) (hC : LipschitzWith C f) : AdmissibleList L₀ C where
  length := 1
  test _ := f
  mem _ := hf
  signed_lipschitz ε hε := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Fin.sum_univ_one, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul]
    exact hC.dist_le_mul s t

theorem singleton_norm {L₀ : Set (S → ℝ)} {C : ℝ≥0}
    (f : S → ℝ) (hf : f ∈ L₀) (hC : LipschitzWith C f)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : Molecule S) :
    ‖(AdmissibleList.singleton f hf hC).eval p m‖ = |pairing S f m| := by
  change ‖WithLp.toLp p (fun _ : Fin 1 => pairing S f m)‖ = |pairing S f m|
  apply le_antisymm
  · simpa only [Fin.sum_univ_one, WithLp.ofLp_toLp] using
      finite_lp_norm_le_sum p (WithLp.toLp p (fun _ : Fin 1 => pairing S f m))
  · exact PiLp.norm_apply_le (WithLp.toLp p (fun _ : Fin 1 => pairing S f m)) 0

theorem test_pairing_bound (n : ℕ) (f : S → ℝ) (hf : f ∈ L (triple n).1)
    (hC : LipschitzWith (listConstant n) f) (m : PreSpace L o) :
    |pairing S f m| ≤ (squareWeight n)⁻¹ * ‖m‖ := by
  have h₁ := list_le_sigma (L (triple n).1) (listConstant n) (listExponent n) o
    (AdmissibleList.singleton f hf hC) (show Molecule S from m)
  have hs := singleton_norm f hf hC (listExponent n) (show Molecule S from m)
  change ‖(AdmissibleList.singleton f hf hC).eval (listExponent n) m‖ ≤ _ at h₁
  rw [hs] at h₁
  exact h₁.trans (sigma_le_preNorm L o n m)

theorem list_test_pairing_bound (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (i : Fin l.length)
    (m : PreSpace L o) : |pairing S (l.test i) m| ≤ (squareWeight n)⁻¹ * ‖m‖ := by
  have h := PiLp.norm_apply_le (l.eval (listExponent n) (show Molecule S from m)) i
  change |pairing S (l.test i) m| ≤ ‖l.eval (listExponent n) m‖ at h
  exact h.trans ((list_le_sigma _ _ _ o l m).trans (sigma_le_preNorm L o n m))

theorem completedList_apply (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (z : TestSpace L o) (i : Fin l.length) :
    completedList L o n l z i = completedPairing L o (l.test i) z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((PiLp.proj (listExponent n) (𝕜 := ℝ) (fun _ : Fin l.length => ℝ) i).continuous.comp
      (completedList L o n l).continuous) Completion.continuous_extension
  | ih m =>
    change completedList L o n l (toTestSpace L o m) i =
      completedPairing L o (l.test i) (toTestSpace L o m)
    rw [completedList_coe, completedPairing_coe L o (l.test i) ((squareWeight n)⁻¹)
      (list_test_pairing_bound L o n l i)]
    rfl

theorem pairing_tendsto {S : Type*} [MetricSpace S]
    (f : ℕ → S → ℝ) (g : S → ℝ)
    (h : ∀ s, Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s)))
    (m : Molecule S) :
    Filter.Tendsto (fun n => pairing S (f n) m) Filter.atTop (nhds (pairing S g m)) := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum]
  exact tendsto_finsetSum _ (fun s _ => (h s).const_mul (m.val s))

theorem completedPairing_tendsto (f : ℕ → S → ℝ) (g : S → ℝ) (K : ℝ≥0)
    (hbound : ∀ n (m : PreSpace L o), |pairing S (f n) m| ≤ K * ‖m‖)
    (hpoint : ∀ s, Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s))) :
    (∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖) ∧
    ∀ z : TestSpace L o,
      Filter.Tendsto (fun n => completedPairing L o (f n) z) Filter.atTop
        (nhds (completedPairing L o g z)) := by
  have hg : ∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖ := by
    intro m
    exact le_of_tendsto (pairing_tendsto f g hpoint (show Molecule S from m)).abs
      (Filter.Eventually.of_forall fun n => hbound n m)
  refine ⟨hg, ?_⟩
  intro z
  apply tendsto_of_dense_lipschitz (toTestSpace L o) Completion.denseRange_coe
    (fun n => completedPairing L o (f n)) (completedPairing L o g) K
    (fun n => completedPairing_lipschitz L o (f n) K (hbound n))
    (completedPairing_lipschitz L o g K hg) _ z
  intro m
  have heq : (fun n => completedPairing L o (f n) (toTestSpace L o m)) =
      (fun n => pairing S (f n) m) :=
    funext (fun n => completedPairing_coe L o (f n) K (hbound n) m)
  rw [heq, completedPairing_coe L o g K hg]
  exact pairing_tendsto f g hpoint m

def transferredList (n n' : ℕ) (hL : (triple n').1 = (triple n).1)
    (hC : listConstant n' = listConstant n)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    AdmissibleList (L (triple n').1) (listConstant n') where
  length := l.length
  test := l.test
  mem i := by rw [hL]; exact l.mem i
  signed_lipschitz ε hε := by rw [hC]; exact l.signed_lipschitz ε hε

theorem listExponent_toReal_pos (n : ℕ) : 0 < (listExponent n).toReal := by
  rw [listExponent_toReal]
  positivity

theorem exists_smaller_exponent (n : ℕ) :
    ∃ n', (triple n').1 = (triple n).1 ∧ listConstant n' = listConstant n ∧
      (listExponent n').toReal < (listExponent n).toReal := by
  obtain ⟨n', hn'⟩ := triple_surjective ((triple n).1, (triple n).2.1, (triple n).2.2 + 1)
  refine ⟨n', by rw [hn'], by simp [listConstant, hn'], ?_⟩
  rw [listExponent_toReal, listExponent_toReal, hn']
  simp only [Nat.cast_add, Nat.cast_one]
  have hh : 1 / ((triple n).2.2 + 1 + 1 : ℝ) < 1 / ((triple n).2.2 + 1 : ℝ) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

theorem fixed_sigma_detector (n : ℕ) (a M : ℝ) (ha : 0 < a) (hM : 0 < M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TestSpace L o,
      a ≤ completedSigma L o n z → ‖z‖ ≤ M →
      ∃ f ∈ L (triple n).1, δ ≤ |completedPairing L o f z| := by
  obtain ⟨n', hL, hC, hp⟩ := exists_smaller_exponent n
  let B := (squareWeight n' : ℝ)⁻¹ * M + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨δ, hδ, hdetect⟩ := exists_uniform_lp_detector (listExponent n) (listExponent n')
    (listExponent_toReal_pos n) (listExponent_toReal_pos n') hp (a / 2) B (by positivity) hB
  refine ⟨δ, hδ, ?_⟩
  intro z hsig hz
  have hex : ∃ l : AdmissibleList (L (triple n).1) (listConstant n),
      a / 2 < ‖completedList L o n l z‖ := by
    by_contra! hl
    have hs : completedSigma L o n z ≤ a / 2 := by
      rw [completedSigma_eq_iSup]
      exact ciSup_le hl
    linarith
  obtain ⟨l, hl⟩ := hex
  let l' := transferredList L n n' hL hC l
  let x : Fin l.length → ℝ := fun i => completedPairing L o (l.test i) z
  have heq : completedList L o n l z = WithLp.toLp (listExponent n) x := by
    apply PiLp.ext
    intro i
    exact completedList_apply L o n l z i
  have heq' : completedList L o n' l' z = WithLp.toLp (listExponent n') x := by
    apply PiLp.ext
    intro i
    exact completedList_apply L o n' l' z i
  have hu : ‖WithLp.toLp (listExponent n') x‖ ≤ B := by
    rw [← heq']
    calc
      ‖completedList L o n' l' z‖ ≤ completedSigma L o n' z := completedList_le_sigma L o n' l' z
      _ ≤ (squareWeight n' : ℝ)⁻¹ * ‖z‖ := completedSigma_le L o n' z
      _ ≤ (squareWeight n' : ℝ)⁻¹ * M :=
        mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (squareWeight n').coe_nonneg)
      _ ≤ B := by dsimp [B]; linarith
  rw [heq] at hl
  obtain ⟨i, hi⟩ := hdetect l.length x hl.le hu
  exact ⟨l.test i, l.mem i, hi.le⟩

end CompletedPairings

section FurtherDetectors

 theorem nonnegative_has_positive_subsequence (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hn : ¬ Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∃ a : ℝ, 0 < a ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, a ≤ f (φ i) := by
  rw [Metric.tendsto_nhds] at hn
  push Not at hn
  obtain ⟨a, ha, hfrequent⟩ := hn
  have hf' : ∃ᶠ i in Filter.atTop, a ≤ f i := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hf _)] using hfrequent
  obtain ⟨φ, hm, hl⟩ := Filter.extraction_of_frequently_atTop hf'
  exact ⟨a, ha, φ, hm, hl⟩

theorem bounded_signs_norm_each {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) (i : ℕ) :
    ‖m i‖ ≤ M := by
  have hM : 0 ≤ M := by simpa using hsum 0 Fin.elim0
  let ε : Fin (i+1) → Bool := fun _ => true
  let j : Fin (i+1) := ⟨i, Nat.lt_succ_self i⟩
  have h := seminorm_sign_pair (normSeminorm ℝ X) (fun j : Fin (i+1) => m j) ε j
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (hsum (i+1) ε) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (hsum (i+1) (flipSign j ε)) 2
  change 2 * ‖m i‖ ^ 2 ≤ ‖∑ k : Fin (i+1), realSign (ε k) • m k‖ ^ 2 +
    ‖∑ k : Fin (i+1), realSign (flipSign j ε k) • m k‖ ^ 2 at h
  nlinarith [norm_nonneg (m i)]

theorem bounded_signs_weak_null {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (u : X →L[ℝ] ℝ) : Filter.Tendsto (fun i => u (m i)) Filter.atTop (nhds 0) := by
  classical
  have hb (n : ℕ) : ∑ i : Fin n, |u (m i)| ≤ ‖u‖ * M := by
    let ε : Fin n → Bool := fun i => if 0 ≤ u (m i) then true else false
    have hε (i : Fin n) : realSign (ε i) * u (m i) = |u (m i)| := by
      dsimp [ε]
      split
      · rw [realSign_true, one_mul, abs_of_nonneg ‹_›]
      · rw [realSign_false, neg_one_mul, abs_of_neg (lt_of_not_ge ‹_›)]
    have heq : u (∑ i : Fin n, realSign (ε i) • m i) = ∑ i : Fin n, |u (m i)| := by
      simp only [map_sum, map_smul, smul_eq_mul, hε]
    calc
      ∑ i : Fin n, |u (m i)| = ‖u (∑ i : Fin n, realSign (ε i) • m i)‖ := by
        rw [heq, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
      _ ≤ ‖u‖ * ‖∑ i : Fin n, realSign (ε i) • m i‖ := u.le_opNorm _
      _ ≤ ‖u‖ * M := mul_le_mul_of_nonneg_left (hsum n ε) (norm_nonneg _)
  have hs : Summable (fun i => |u (m i)|) :=
    summable_of_sum_range_le (c := ‖u‖ * M) (fun i => abs_nonneg _) (fun n => by
      rw [Finset.sum_range]
      exact hb n)
  have hs' : Summable (fun i => u (m i)) := summable_norm_iff.mp (by simpa using hs)
  exact hs'.tendsto_atTop_zero

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedCoordinate_eq_weight_sigma (n : ℕ) (z : TestSpace L o) :
    completedCoordinate L o n z = (squareWeight n : ℝ) * completedSigma L o n z := by
  change completedCoordinate L o n z = (squareWeight n : ℝ) *
    ((squareWeight n : ℝ)⁻¹ * completedCoordinate L o n z)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul]

theorem one_class_detects (m : ℕ → TestSpace L o) (M r : ℝ) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : ℕ → S → ℝ, ∀ i, f i ∈ L h ∧ δ ≤ |completedPairing L o (f i) (m (φ i))| := by
  have hnorm := bounded_signs_norm_each m M hsum
  have hM : 0 < M := hr.trans_le ((hlower 0).trans (hnorm 0))
  obtain ⟨n, hn⟩ := exists_nonzero_coordinate (completedCoordinate L o)
    (completedCoordinate_summable L o) (completedNorm_sq L o) m M r hr hlower hsum
  have hnσ : ¬ Filter.Tendsto (fun i => completedSigma L o n (m i))
      Filter.atTop (nhds 0) := by
    intro hh
    apply hn
    have hh' := hh.const_mul (squareWeight n : ℝ)
    simpa only [mul_zero, ← completedCoordinate_eq_weight_sigma] using hh'
  obtain ⟨a, ha, φ, hφ, hφa⟩ := nonnegative_has_positive_subsequence
    (fun i => completedSigma L o n (m i)) (fun i => apply_nonneg _ _) hnσ
  obtain ⟨δ, hδ, hδdetect⟩ := fixed_sigma_detector L o n a M ha hM
  have hchoose : ∀ i, ∃ f ∈ L (triple n).1, δ ≤ |completedPairing L o f (m (φ i))| :=
    fun i => hδdetect (m (φ i)) (hφa i) (hnorm (φ i))
  choose f hf hd using hchoose
  exact ⟨(triple n).1, δ, hδ, φ, hφ, f, fun i => ⟨hf i, hd i⟩⟩

end FurtherDetectors

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

theorem dist_le_of_local_interval {Y : Type*} [PseudoMetricSpace Y]
    {a b K : ℝ} (hab : a ≤ b) {f : ℝ → Y}
    (hf : ContinuousOn f (Icc a b))
    (hloc : ∀ x ∈ Icc a b, ∀ᶠ y in nhdsWithin x (Icc a b),
      dist (f x) (f y) ≤ K * dist x y) :
    dist (f a) (f b) ≤ K * (b-a) := by
  let s : Set ℝ := {x | dist (f a) (f x) ≤ K * (x-a)}
  have hclosed : IsClosed (s ∩ Icc a b) := by
    have hc : ContinuousOn (fun x => (dist (f a) (f x), K * (x-a))) (Icc a b) :=
      (show ContinuousOn (fun x => dist (f a) (f x)) (Icc a b) from
        fun x hx => tendsto_const_nhds.dist (hf x hx)).prodMk (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))
    simpa only [s, inter_comm, Set.preimage_ofPred_eq] using hc.preimage_isClosed_of_isClosed isClosed_Icc
      OrderClosedTopology.isClosed_le'
  have ha : a ∈ s := by simp [s]
  have hs := hclosed.Icc_subset_of_forall_exists_gt ha
  apply hs ?_ ⟨hab, le_rfl⟩
  rintro x ⟨hx : dist (f a) (f x) ≤ K * (x-a), hxab⟩ y hxy
  have hh : ∀ᶠ z in nhdsWithin x (Ioi x), dist (f x) (f z) ≤ K * dist x z :=
    nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hxab) (hloc x ⟨hxab.1, hxab.2.le⟩)
  obtain ⟨z, hz, hxz, hzy⟩ := (hh.and (Ioc_mem_nhdsGT hxy)).exists
  refine ⟨z, ?_, hxz, hzy⟩
  change dist (f a) (f z) ≤ K * (z-a)
  have hdist : dist x z = z-x := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxz.le)]; ring
  rw [hdist] at hz
  calc
    dist (f a) (f z) ≤ dist (f a) (f x) + dist (f x) (f z) := dist_triangle _ _ _
    _ ≤ K * (x-a) + K * (z-x) := add_le_add hx hz
    _ = K * (z-a) := by ring

theorem lipschitzOn_convex_of_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : E → Y} {K : ℝ≥0}
    (hf : ContinuousOn f B)
    (hloc : ∀ x ∈ B, ∀ᶠ y in nhdsWithin x B, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzOnWith K f B := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let g : ℝ → E := AffineMap.lineMap x y
  have hg : Continuous g := by
    change Continuous (fun t : ℝ => t • (y-x) + x)
    fun_prop
  have hmap : MapsTo g (Icc 0 1) B := fun t ht => hB.lineMap_mem hx hy ht
  have hc : ContinuousOn (f ∘ g) (Icc 0 1) := hf.comp hg.continuousOn hmap
  have hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ u in nhdsWithin t (Icc 0 1),
      dist ((f ∘ g) t) ((f ∘ g) u) ≤ (K * dist x y) * dist t u := by
    intro t ht
    have hgt := (hg.continuousAt (x := t)).continuousWithinAt.tendsto_nhdsWithin hmap
    filter_upwards [hgt (hloc (g t) (hmap ht))] with u hu
    change dist (f (g t)) (f (g u)) ≤ _
    calc
      dist (f (g t)) (f (g u)) ≤ K * dist (g t) (g u) := hu
      _ = (K * dist x y) * dist t u := by
        rw [show dist (g t) (g u) = dist t u * dist x y from dist_lineMap_lineMap x y t u]
        ring
  have h := dist_le_of_local_interval (by norm_num : (0 : ℝ) ≤ 1) hc hh
  simpa [g, Function.comp_def] using h

theorem lipschitz_convex_subtype_of_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : B → Y} {K : ℝ≥0}
    (hf : Continuous f)
    (hloc : ∀ x, ∀ᶠ y in nhds x, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let F : E → Y := fun z => if h : z ∈ B then f ⟨z, h⟩ else f x
  have hF (z : B) : F z = f z := by simp [F]
  have hc : ContinuousOn F B := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hf using 1
    exact funext hF
  have hl : ∀ z ∈ B, ∀ᶠ w in nhdsWithin z B,
      dist (F z) (F w) ≤ K * dist z w := by
    intro z hz
    rw [nhdsWithin_eq_map_subtype_coe hz]
    change ∀ᶠ w : B in nhds ⟨z, hz⟩, dist (F z) (F w) ≤ K * dist z (w : E)
    simpa only [show F z = f ⟨z, hz⟩ from hF ⟨z, hz⟩, hF, Subtype.dist_eq] using hloc ⟨z, hz⟩
  have hh := (lipschitzOn_convex_of_local hB hc hl).dist_le_mul x x.property y y.property
  simpa only [hF, Subtype.dist_eq] using hh

theorem eventually_zero_of_not_tsupport {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {x : X} (hx : x ∉ tsupport f) : ∀ᶠ y in nhds x, f y = 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

theorem disjoint_supports_signed_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    {ι : Type*} [Fintype ι] (f : ι → B → ℝ) (K : ℝ≥0)
    (hf : ∀ i, LipschitzWith K (f i))
    (hdisj : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))))
    (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith K (fun x => ∑ i, ε i * f i x) := by
  classical
  apply lipschitz_convex_subtype_of_local hB
  · exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hf i).continuous)
  intro x
  by_cases hex : ∃ j, x ∈ tsupport (f j)
  · obtain ⟨j, hj⟩ := hex
    have hz : ∀ i, i ≠ j → ∀ᶠ y in nhds x, f i y = 0 := by
      intro i hij
      apply eventually_zero_of_not_tsupport
      intro hi
      exact Set.disjoint_left.mp (hdisj hij) hi hj
    have he : ∀ᶠ y in nhds x, ∀ i, i ≠ j → f i y = 0 :=
      Filter.eventually_all.mpr (fun i => if hi : i = j then by simp [hi] else
        (hz i hi).mono (fun y hy _ => hy))
    filter_upwards [he] with y hy
    have hx (i) (hi : i ≠ j) : f i x = 0 := (hz i hi).self_of_nhds
    have sx : (∑ i, ε i * f i x) = ε j * f j x := by
      apply Finset.sum_eq_single j
      · intro i hi hij; simp [hx i hij]
      · simp
    have sy : (∑ i, ε i * f i y) = ε j * f j y := by
      apply Finset.sum_eq_single j
      · intro i hi hij; simp [hy i hij]
      · simp
    rw [sx, sy, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul, ← Real.dist_eq]
    exact (hf j).dist_le_mul x y
  · push Not at hex
    have he : ∀ᶠ y in nhds x, ∀ i, f i y = 0 :=
      Filter.eventually_all.mpr (fun i => eventually_zero_of_not_tsupport (hex i))
    filter_upwards [he] with y hy
    have hx (i) : f i x = 0 := image_eq_zero_of_notMem_tsupport (hex i)
    simp only [hx, hy, mul_zero, Finset.sum_const_zero, dist_self]
    positivity

theorem nested_supports_signed_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    (n : ℕ) (u b : Fin n → B → ℝ) (e : Fin n → ℝ)
    (C : Fin n → Set B) (K : ℝ≥0) (Kb : Fin n → ℝ≥0)
    (_hu : ∀ i, Continuous (u i)) (hb : ∀ i, LipschitzWith (Kb i) (b i))
    (hF : ∀ i, LipschitzWith K (fun x => u i x * b i x))
    (hC : ∀ i, IsOpen (C i)) (hc : ∀ i, ∀ x ∈ C i, u i x = e i)
    (hnest : ∀ i j, i < j → tsupport (u j) ⊆ C i)
    (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith (K + ∑ i, ‖e i‖₊ * Kb i)
      (fun x => ∑ i, ε i * (u i x * b i x)) := by
  classical
  apply lipschitz_convex_subtype_of_local hB
  · exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hF i).continuous)
  intro x
  let H : Finset (Fin n) := Finset.univ.filter (fun i => x ∈ tsupport (u i))
  by_cases hH : H.Nonempty
  · let j := H.max' hH
    have hj : x ∈ tsupport (u j) := (Finset.mem_filter.mp (H.max'_mem hH)).2
    have he (i) (hij : i < j) : ∀ᶠ y in nhds x, u i y = e i := by
      filter_upwards [(hC i).mem_nhds (hnest i j hij hj)] with y hy
      exact hc i y hy
    have hz (i) (hji : j < i) : ∀ᶠ y in nhds x, u i y = 0 := by
      apply eventually_zero_of_not_tsupport
      intro hi
      have hiH : i ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      exact (not_lt_of_ge (H.le_max' i hiH)) hji
    have hall : ∀ᶠ y in nhds x, ∀ i,
        (i < j → u i y = e i) ∧ (j < i → u i y = 0) := by
      apply Filter.eventually_all.mpr
      intro i
      rcases lt_trichotomy i j with hij | rfl | hji
      · filter_upwards [he i hij] with y hy
        exact ⟨fun _ => hy, fun h => (not_lt_of_ge hij.le h).elim⟩
      · exact Filter.Eventually.of_forall (by simp)
      · filter_upwards [hz i hji] with y hy
        exact ⟨fun h => (not_lt_of_ge hji.le h).elim, fun _ => hy⟩
    filter_upwards [hall] with y hy
    have hi (i : Fin n) :
        dist (ε i * (u i x * b i x)) (ε i * (u i y * b i y)) ≤
          ((if i = j then (K : ℝ) else 0) + |e i| * Kb i) * dist x y := by
      rcases lt_trichotomy i j with hij | rfl | hji
      · have hx := (he i hij).self_of_nhds
        rw [hx, (hy i).1 hij, ite_eq_right (ne_of_lt hij), zero_add,
          Real.dist_eq, ← mul_sub, ← mul_sub, abs_mul, abs_mul, hε i, one_mul]
        calc
          |e i| * |b i x - b i y| ≤ |e i| * (Kb i * dist x y) := by
            apply mul_le_mul_of_nonneg_left ((hb i).dist_le_mul x y) (abs_nonneg _)
          _ = |e i| * Kb i * dist x y := by ring
      · rw [ite_eq_left rfl, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul,
          ← Real.dist_eq]
        exact ((hF j).dist_le_mul x y).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (dist_nonneg))
      · rw [(hz i hji).self_of_nhds, (hy i).2 hji]
        simp only [zero_mul, mul_zero, dist_self]
        positivity
    calc
      dist (∑ i, ε i * (u i x * b i x)) (∑ i, ε i * (u i y * b i y))
          ≤ ∑ i, dist (ε i * (u i x * b i x)) (ε i * (u i y * b i y)) :=
        dist_sum_sum_le _ _ _
      _ ≤ ∑ i, ((if i = j then (K : ℝ) else 0) + |e i| * Kb i) * dist x y :=
        Finset.sum_le_sum (fun i _ => hi i)
      _ = (K + ∑ i, ‖e i‖₊ * Kb i : ℝ≥0) * dist x y := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp [Real.norm_eq_abs]
  · have hz (i : Fin n) : ∀ᶠ y in nhds x, u i y = 0 := by
      apply eventually_zero_of_not_tsupport
      intro hi
      exact hH ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    have hx (i : Fin n) : u i x = 0 := (hz i).self_of_nhds
    simp only [hx, hy, zero_mul, mul_zero, Finset.sum_const_zero, dist_self]
    positivity

noncomputable section

def chi (t : ℝ) : ℝ := min 1 (max 0 (2*t-1))

def cutoff {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) : ℝ :=
  1 - chi (dist x q / ε)

def localG {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  u q + chi (dist x q / ε) * (u x-u q)

def localR {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  localG q ε u x-u x

theorem cutoff_nonneg {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) :
    0 ≤ cutoff q ε x := by
  dsimp [cutoff, chi]
  have := min_le_left (1 : ℝ) (max 0 (2 * (dist x q / ε) - 1))
  linarith

theorem cutoff_le_one {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) :
    cutoff q ε x ≤ 1 := by
  dsimp [cutoff, chi]
  have : 0 ≤ min (1 : ℝ) (max 0 (2 * (dist x q / ε) - 1)) := by positivity
  linarith

theorem localR_eq {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) :
    localR q ε u x = cutoff q ε x * (u q-u x) := by
  dsimp [localR, localG, cutoff]
  ring

theorem localG_eq {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) :
    localG q ε u x = u x + localR q ε u x := by
  simp [localR]

theorem cutoff_eq_zero {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ} (hε : 0 < ε)
    (x : X) (hx : ε ≤ dist x q) : cutoff q ε x = 0 := by
  have hh : 1 ≤ dist x q / ε := (le_div_iff₀ hε).mpr (by simpa using hx)
  simp [cutoff, chi, max_eq_right (by linarith : 0 ≤ 2*(dist x q/ε)-1),
    min_eq_left (by linarith : (1:ℝ) ≤ 2*(dist x q/ε)-1)]

theorem dist_lt_of_cutoff_ne_zero {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (x : X) (hx : cutoff q ε x ≠ 0) : dist x q < ε := by
  by_contra! hh
  exact hx (cutoff_eq_zero q hε x hh)

theorem localG_plateau {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ} (hε : 0 < ε)
    (u : X → ℝ) (x : X) (hx : dist x q ≤ ε/2) : localG q ε u x = u q := by
  have hh : dist x q / ε ≤ 1/2 := (div_le_iff₀ hε).mpr (by linarith)
  simp [localG, chi, max_eq_left (by linarith : 2*(dist x q/ε)-1 ≤ 0)]

theorem chi_lipschitz : LipschitzWith 2 chi := by
  have h : LipschitzWith 2 (fun t : ℝ => 2*t-1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, show (2*x-1)-(2*y-1)=2*(x-y) by ring, abs_mul]
    norm_num
  change LipschitzWith 2 (fun t : ℝ => min 1 (max 0 (2*t-1)))
  exact (h.const_max 0).const_min 1

theorem cutoff_dist_le {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (x y : X) :
    |cutoff q ε x-cutoff q ε y| ≤ (2 / ε) * dist x y := by
  have h := chi_lipschitz.dist_le_mul (dist x q / ε) (dist y q / ε)
  simp only [Real.dist_eq, NNReal.coe_ofNat] at h
  have heq : |cutoff q ε x-cutoff q ε y| =
      |chi (dist x q/ε)-chi (dist y q/ε)| := by
    rw [cutoff, cutoff, sub_sub_sub_cancel_left, abs_sub_comm]
  rw [heq]
  calc
    |chi (dist x q/ε)-chi (dist y q/ε)| ≤ 2 * |dist x q/ε-dist y q/ε| := h
    _ = (2/ε)*|dist x q-dist y q| := by rw [← sub_div, abs_div, abs_of_pos hε]; ring
    _ ≤ (2/ε)*dist x y := mul_le_mul_of_nonneg_left
      (abs_dist_sub_le x y q) (by positivity)

theorem localR_sup_lip {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) (x : X) :
    |localR q ε u x| ≤ ε * L := by
  rw [localR_eq, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _)]
  by_cases hx : cutoff q ε x = 0
  · rw [hx, zero_mul]; positivity
  have hd := (dist_lt_of_cutoff_ne_zero q hε x hx).le
  have hb : |u q-u x| ≤ ε * L := by
    calc
      |u q-u x| ≤ L * dist q x := hu.dist_le_mul q x
      _ ≤ L * ε := mul_le_mul_of_nonneg_left (by rwa [dist_comm]) L.coe_nonneg
      _ = ε*L := mul_comm _ _
  exact (mul_le_mul_of_nonneg_right (cutoff_le_one q ε x) (abs_nonneg _)).trans (by simpa using hb)

theorem localR_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) :
    LipschitzWith (3*L) (localR q ε u) := by
  have hb (x y : X) (hy : cutoff q ε y ≠ 0) :
      |localR q ε u x-localR q ε u y| ≤ (3*L : ℝ≥0)*dist x y := by
    have hd := (dist_lt_of_cutoff_ne_zero q hε y hy).le
    have huq : |u q-u y| ≤ ε*L := by
      calc
        |u q-u y| ≤ L*dist q y := hu.dist_le_mul q y
        _ ≤ L*ε := mul_le_mul_of_nonneg_left (by rwa [dist_comm]) L.coe_nonneg
        _ = ε*L := mul_comm _ _
    have heq : localR q ε u x-localR q ε u y =
        cutoff q ε x*(u y-u x)+(cutoff q ε x-cutoff q ε y)*(u q-u y) := by
      simp only [localR_eq]; ring
    rw [heq]
    calc
      |cutoff q ε x*(u y-u x)+(cutoff q ε x-cutoff q ε y)*(u q-u y)|
          ≤ |cutoff q ε x*(u y-u x)| + |(cutoff q ε x-cutoff q ε y)*(u q-u y)| := abs_add_le _ _
      _ = cutoff q ε x*|u y-u x| + |cutoff q ε x-cutoff q ε y| * |u q-u y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _)]
      _ ≤ 1 * (L*dist x y) + ((2/ε)*dist x y)*(ε*L) := by
        apply add_le_add
        · apply mul_le_mul (cutoff_le_one q ε x)
          · have hd := hu.dist_le_mul y x
            rw [dist_comm y x] at hd
            exact hd
          · exact abs_nonneg _
          · norm_num
        · exact mul_le_mul (cutoff_dist_le q hε x y) huq (abs_nonneg _) (by positivity)
      _ = (3*L : ℝ≥0)*dist x y := by
        push_cast
        field_simp
        ; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hy : cutoff q ε y = 0
  · by_cases hx : cutoff q ε x = 0
    · simp [localR_eq, hx, hy]; positivity
    · simpa only [abs_sub_comm, dist_comm] using hb y x hx
  · exact hb x y hy

theorem localG_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) :
    LipschitzWith (4*L) (localG q ε u) := by
  have heq : localG q ε u = fun x => u x+localR q ε u x := funext (localG_eq q ε u)
  rw [heq]
  have hc : L+3*L=4*L := by ring
  rw [← hc]
  exact hu.add (localR_lipschitz q hε u hu)

theorem localG_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localG q ε u x| ≤ A := by
  have ha := cutoff_nonneg q ε x
  have ha' := cutoff_le_one q ε x
  have heq : localG q ε u x = (1-cutoff q ε x)*u x+cutoff q ε x*u q := by
    rw [localG_eq, localR_eq]; ring
  rw [heq]
  calc
    |(1-cutoff q ε x)*u x+cutoff q ε x*u q|
        ≤ |(1-cutoff q ε x)*u x|+|cutoff q ε x*u q| := abs_add_le _ _
    _ = (1-cutoff q ε x)*|u x|+cutoff q ε x*|u q| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (by linarith : 0 ≤ 1-cutoff q ε x)]
    _ ≤ (1-cutoff q ε x)*A+cutoff q ε x*A := add_le_add
      (mul_le_mul_of_nonneg_left (hu x) (by linarith)) (mul_le_mul_of_nonneg_left (hu q) ha)
    _ = A := by ring

theorem localR_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localR q ε u x| ≤ 2*A := by
  calc
    |localR q ε u x| = |localG q ε u x-u x| := rfl
    _ ≤ |localG q ε u x|+|u x| := abs_sub _ _
    _ ≤ A+A := add_le_add (localG_sup q ε u A hu x) (hu x)
    _ = 2*A := by ring

def localGLinear {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun := localG q ε
  map_add' u v := by ext x; simp only [localG, Pi.add_apply]; ring
  map_smul' c u := by ext x; simp only [localG, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def localRLinear {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) := localGLinear q ε - LinearMap.id

@[simp] theorem localRLinear_apply {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) : localRLinear q ε u = localR q ε u := rfl

def localOp {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) := if isG then localGLinear q ε else localRLinear q ε

theorem localOp_nonzero_old {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u : X → ℝ) (x : X) (hx : localOp isG q ε u x ≠ 0) :
    ∃ y, u y ≠ 0 ∧ dist x y ≤ ε := by
  by_cases hu : u x = 0
  · refine ⟨q, ?_, ?_⟩
    · intro hq
      cases isG <;> simp [localOp, localGLinear, localRLinear, localG, hu, hq] at hx
    · have ha : cutoff q ε x ≠ 0 := by
        intro ha
        cases isG
        · change localR q ε u x ≠ 0 at hx
          simp [localR_eq, ha] at hx
        · change localG q ε u x ≠ 0 at hx
          simp [localG_eq, localR_eq, hu, ha] at hx
      exact (dist_lt_of_cutoff_ne_zero q hε x ha).le
  · exact ⟨x, hu, by simpa using hε.le⟩

theorem localOp_support {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u : X → ℝ) :
    tsupport (localOp isG q ε u) ⊆ Metric.cthickening ε (tsupport u) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  obtain ⟨y, hy, hd⟩ := localOp_nonzero_old isG q hε u x hx
  exact Metric.mem_cthickening_of_dist_le x y ε (tsupport u) (subset_tsupport u hy) hd

theorem localR_support_ball {X : Type*} [PseudoMetricSpace X] (q : X)
    {ε : ℝ} (hε : 0 < ε) (u : X → ℝ) :
    tsupport (localR q ε u) ⊆ Metric.closedBall q ε := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have ha : cutoff q ε x ≠ 0 := by
    intro ha
    have hx' : localR q ε u x ≠ 0 := hx
    simp [localR_eq, ha] at hx'
  exact (dist_lt_of_cutoff_ne_zero q hε x ha).le

theorem localOp_support_bound {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u v : X → ℝ) {K : ℝ≥0} (hv : LipschitzWith K v)
    (a : ℝ) (ha : ∀ x ∈ tsupport u, v x ≤ a) :
    ∀ x ∈ tsupport (localOp isG q ε u), v x ≤ a+ε*K := by
  have hclosed : IsClosed {x | v x ≤ a+ε*K} := isClosed_le hv.continuous continuous_const
  apply closure_minimal _ hclosed
  intro x hx
  obtain ⟨y, hy, hd⟩ := localOp_nonzero_old isG q hε u x hx
  have hb := ha y (subset_tsupport u hy)
  have hd' := hv.dist_le_mul x y
  rw [Real.dist_eq] at hd'
  have hle : v x-v y ≤ K*ε := (le_abs_self _).trans (hd'.trans
    (mul_le_mul_of_nonneg_left hd K.coe_nonneg))
  change v x ≤ a+ε*K
  nlinarith

end

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace C0Absorption
noncomputable section

abbrev C0Ball := Metric.closedBall (0 : C0) 1

abbrev Cube (I : Finset ℕ) := (i : I) → Icc (-1 : ℝ) 1

theorem c0_norm_apply_le (s : C0) (i : ℕ) : |s i| ≤ ‖s‖ := by
  exact s.toBCF.norm_coe_le_norm i

theorem c0_norm_le (s : C0) {a : ℝ} (ha : 0 ≤ a) (hs : ∀ i, |s i| ≤ a) : ‖s‖ ≤ a := by
  exact (s.toBCF.norm_le ha).mpr hs

def c0Eval (i : ℕ) : C0 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun s : C0 => s i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun s => by simpa using c0_norm_apply_le s i)

@[simp] theorem c0Eval_apply (i : ℕ) (s : C0) : c0Eval i s = s i := rfl

def cubeRestrict (I : Finset ℕ) (s : C0Ball) : Cube I := fun i =>
  ⟨s.val i, by
    have hnorm : ‖s.val‖ ≤ 1 := by
      have hh := s.property
      change dist s.val 0 ≤ 1 at hh
      rwa [dist_zero_right] at hh
    exact abs_le.mp ((c0_norm_apply_le s.val i).trans hnorm)⟩

def finsuppToC0 (f : ℕ →₀ ℝ) : C0 where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := (HasCompactSupport.of_support_subset_isCompact
    f.hasFiniteSupport.isCompact (Set.Subset.refl _)).is_zero_at_infty

@[simp] theorem finsuppToC0_apply (f : ℕ →₀ ℝ) (i : ℕ) : finsuppToC0 f i = f i := rfl

def atom (i : ℕ) : C0 := finsuppToC0 (Finsupp.single i 1)

@[simp] theorem atom_apply (i j : ℕ) : atom i j = if i=j then 1 else 0 := by
  simp [atom, Finsupp.single_apply]

@[simp] theorem atom_norm (i : ℕ) : ‖atom i‖ = 1 := by
  apply le_antisymm
  · apply c0_norm_le _ zero_le_one
    intro j
    simp only [atom_apply]
    split <;> norm_num
  · simpa using c0_norm_apply_le (atom i) i

def truncate (N : ℕ) (s : C0) : C0 := ∑ i ∈ Finset.range N, s i • atom i

@[simp] theorem truncate_apply (N : ℕ) (s : C0) (i : ℕ) :
    truncate N s i = if i < N then s i else 0 := by
  classical
  change c0Eval i (∑ j ∈ Finset.range N, s j • atom j) = _
  simp only [map_sum, map_smul, smul_eq_mul, c0Eval_apply, atom_apply]
  by_cases hi : i < N
  · rw [ite_eq_left hi, Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [hji]
    · intro hnot; exact (hnot (Finset.mem_range.mpr hi)).elim
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi (Finset.mem_range.mp hj)
    simp [hji]

theorem c0_tendsto_zero (s : C0) : Tendsto s atTop (nhds 0) := by
  simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty s

theorem truncate_tendsto (s : C0) : Tendsto (fun N => truncate N s) atTop (nhds s) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : ∀ᶠ i in atTop, |s i| < ε/2 := by
    simpa only [Real.dist_eq, sub_zero] using
      (Metric.tendsto_nhds.mp (c0_tendsto_zero s) (ε/2) (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply c0_norm_le _ (by positivity : 0 ≤ ε/2)
  intro i
  simp only [ZeroAtInftyContinuousMap.sub_apply, truncate_apply]
  by_cases hi : i < n
  · simp [hi]; positivity
  · simp only [ite_eq_right hi, zero_sub, abs_neg]
    exact (hN i (hn.trans (Nat.le_of_not_gt hi))).le

theorem truncate_mem_span (N : ℕ) (s : C0) :
    truncate N s ∈ Submodule.span ℝ (Set.range atom) := by
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem c0_span_dense : Dense (↑(Submodule.span ℝ (Set.range atom)) : Set C0) := by
  intro s
  exact mem_closure_of_tendsto (truncate_tendsto s)
    (Filter.Eventually.of_forall (fun N => truncate_mem_span N s))

instance c0_separable : TopologicalSpace.SeparableSpace C0 := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have hh := (Set.countable_range atom).isSeparable.span (R := ℝ)
  rw [← c0_span_dense.closure_eq]
  exact hh.closure

def extendFinite (I : Finset ℕ) (x : I → ℝ) : C0 := by
  classical
  exact finsuppToC0 (Finsupp.onFinset I (fun j => if h : j ∈ I then x ⟨j,h⟩ else 0)
    (by intro j hj; by_contra h; simp [h] at hj))

@[simp] theorem extendFinite_apply (I : Finset ℕ) (x : I → ℝ) (j : ℕ) :
    extendFinite I x j = if h : j ∈ I then x ⟨j,h⟩ else 0 := by
  classical
  rfl

theorem extendFinite_norm_le (I : Finset ℕ) (x : I → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hx : ∀ i, |x i| ≤ a) : ‖extendFinite I x‖ ≤ a := by
  classical
  apply c0_norm_le _ ha
  intro j
  rw [extendFinite_apply]
  split
  · exact hx _
  · simpa using ha

def cubeExtend (I : Finset ℕ) (x : Cube I) : C0Ball :=
  ⟨extendFinite I (fun i => (x i).val), by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply extendFinite_norm_le _ _ zero_le_one
    intro i
    exact abs_le.mpr (x i).property⟩

@[simp] theorem cubeRestrict_extend (I : Finset ℕ) (x : Cube I) :
    cubeRestrict I (cubeExtend I x) = x := by
  classical
  ext i
  change extendFinite I (fun i => (x i).val) i = (x i).val
  simp

theorem cubeRestrict_lipschitz (I : Finset ℕ) : LipschitzWith 1 (cubeRestrict I) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  change dist (s.val i) (t.val i) ≤ dist s.val t.val
  exact BoundedContinuousFunction.dist_coe_le_dist (f := s.val.toBCF) (g := t.val.toBCF) i

theorem cubeExtend_lipschitz (I : Finset ℕ) : LipschitzWith 1 (cubeExtend I) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  apply c0_norm_le _ dist_nonneg
  intro j
  change |extendFinite I (fun i => (s i).val) j-extendFinite I (fun i => (t i).val) j| ≤ dist s t
  simp only [extendFinite_apply]
  split
  · exact dist_le_pi_dist s t _
  · simp

theorem cubeExtend_isometry (I : Finset ℕ) : Isometry (cubeExtend I) := by
  rw [isometry_iff_dist_eq]
  intro x y
  apply le_antisymm
  · simpa using (cubeExtend_lipschitz I).dist_le_mul x y
  · simpa using (cubeRestrict_lipschitz I).dist_le_mul (cubeExtend I x) (cubeExtend I y)

abbrev GridIndex (n : ℕ) := Icc (-(n : ℤ)) (n : ℤ)

def gridPoint (n : ℕ) (hn : 0 < n) (z : GridIndex n) : Icc (-1 : ℝ) 1 :=
  ⟨(z.val : ℝ) / n, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hl : -(n : ℝ) ≤ (z.val : ℝ) := by exact_mod_cast z.property.1
    have hu : (z.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast z.property.2
    constructor
    · apply (le_div_iff₀ hn').mpr; simpa using hl
    · apply (div_le_iff₀ hn').mpr; simpa using hu⟩

def nearestGridIndex (n : ℕ) (_hn : 0 < n) (x : Icc (-1 : ℝ) 1) : GridIndex n :=
  ⟨round ((n : ℝ) * x.val), by
    have hb := abs_le.mp (abs_sub_round ((n : ℝ) * x.val))
    have hxlo : -(n : ℝ) ≤ (n : ℝ) * x.val := by nlinarith [x.property.1, Nat.cast_nonneg (α := ℝ) n]
    have hxhi : (n : ℝ) * x.val ≤ n := by nlinarith [x.property.2, Nat.cast_nonneg (α := ℝ) n]
    constructor
    · by_contra h
      have hh : round ((n : ℝ) * x.val) ≤ -(n : ℤ)-1 := by omega
      have hh' : (round ((n : ℝ) * x.val) : ℝ) ≤ -(n : ℝ)-1 := by exact_mod_cast hh
      linarith
    · by_contra h
      have hh : (n : ℤ)+1 ≤ round ((n : ℝ) * x.val) := by omega
      have hh' : (n : ℝ)+1 ≤ (round ((n : ℝ) * x.val) : ℝ) := by exact_mod_cast hh
      linarith⟩

theorem nearestGrid_dist (n : ℕ) (hn : 0 < n) (x : Icc (-1 : ℝ) 1) :
    dist x (gridPoint n hn (nearestGridIndex n hn x)) ≤ 1 / (2*(n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change |x.val - (round ((n : ℝ)*x.val) : ℝ)/(n : ℝ)| ≤ _
  rw [show x.val - (round ((n : ℝ)*x.val) : ℝ)/(n : ℝ) =
    ((n : ℝ)*x.val-(round ((n : ℝ)*x.val) : ℝ))/(n : ℝ) by field_simp,
    abs_div, abs_of_pos hn', div_le_iff₀ hn']
  have hb := abs_sub_round ((n : ℝ)*x.val)
  have he : 1 / (2*(n : ℝ)) * (n : ℝ) = (1 : ℝ)/2 := by field_simp
  rwa [he]

def dyadic (a : ℕ) : ℝ := ((2 : ℝ)^a)⁻¹

theorem dyadic_pos (a : ℕ) : 0 < dyadic a := by unfold dyadic; positivity

theorem dyadic_tendsto : Tendsto dyadic atTop (nhds 0) := by
  change Tendsto (fun a : ℕ => ((2 : ℝ)^a)⁻¹) atTop (nhds 0)
  simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)

abbrev OperationGrid (I : Finset ℕ) (a : ℕ) := I → GridIndex (2^(a+3))

def operationGridPoint (I : Finset ℕ) (a : ℕ) (q : OperationGrid I a) : Cube I :=
  fun i => gridPoint _ (by positivity) (q i)

def nearestOperationGrid (I : Finset ℕ) (a : ℕ) (x : Cube I) : OperationGrid I a :=
  fun i => nearestGridIndex _ (by positivity) (x i)

theorem operationGrid_mesh (a : ℕ) : (1 : ℝ) / (2^(a+3)) = dyadic a / 8 := by
  rw [dyadic, pow_add]; norm_num; ring

theorem nearestOperationGrid_dist (I : Finset ℕ) (a : ℕ) (x : Cube I) :
    dist x (operationGridPoint I a (nearestOperationGrid I a x)) ≤ dyadic a / 16 := by
  apply (dist_pi_le_iff (div_nonneg (dyadic_pos a).le (by norm_num) : 0 ≤ dyadic a / 16)).mpr
  intro i
  have hh := nearestGrid_dist (2^(a+3)) (by positivity) (x i)
  change dist (x i) (gridPoint _ _ (nearestGridIndex _ _ (x i))) ≤ _
  refine hh.trans_eq ?_
  push_cast
  rw [dyadic, pow_add]
  norm_num
  ring

def coordinateTail (N : ℕ) (s : C0) : C0 := s - truncate (N+1) s

@[simp] theorem coordinateTail_apply (N : ℕ) (s : C0) (i : ℕ) :
    coordinateTail N s i = if N < i then s i else 0 := by
  simp only [coordinateTail, ZeroAtInftyContinuousMap.sub_apply, truncate_apply]
  split_ifs <;> simp_all; omega

def tau (N : ℕ) (s : C0) : ℝ := ‖coordinateTail N s‖

theorem tau_nonneg (N : ℕ) (s : C0) : 0 ≤ tau N s := norm_nonneg _

theorem coordinateTail_sub (N : ℕ) (s t : C0) :
    coordinateTail N (s-t) = coordinateTail N s-coordinateTail N t := by
  ext i
  simp only [coordinateTail_apply, ZeroAtInftyContinuousMap.sub_apply]
  split_ifs <;> simp

theorem tau_le_norm (N : ℕ) (s : C0) : tau N s ≤ ‖s‖ := by
  apply c0_norm_le _ (norm_nonneg s)
  intro i
  rw [coordinateTail_apply]
  split_ifs
  · exact c0_norm_apply_le s i
  · simp

theorem tau_lipschitz (N : ℕ) : LipschitzWith 1 (tau N) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  calc
    |tau N s-tau N t| ≤ ‖coordinateTail N s-coordinateTail N t‖ := abs_norm_sub_norm_le _ _
    _ = tau N (s-t) := by rw [tau, coordinateTail_sub]
    _ ≤ ‖s-t‖ := tau_le_norm _ _
    _ = dist s t := (dist_eq_norm _ _).symm

theorem tau_antitone (s : C0) : Antitone (fun N => tau N s) := by
  intro M N hMN
  apply c0_norm_le _ (tau_nonneg M s)
  intro i
  rw [coordinateTail_apply]
  split_ifs with hi
  · have hh := c0_norm_apply_le (coordinateTail M s) i
    simpa [tau, coordinateTail_apply, lt_of_le_of_lt hMN hi] using hh
  · simpa using tau_nonneg M s

theorem tau_tendsto_zero (s : C0) : Tendsto (fun N => tau N s) atTop (nhds 0) := by
  have hh := ((show Tendsto (fun _ : ℕ => s) atTop (nhds s) from tendsto_const_nhds).sub (truncate_tendsto s)).norm
  have hshift : Tendsto (fun N : ℕ => N+1) atTop atTop := tendsto_add_atTop_nat 1
  simpa [Function.comp_def, tau, coordinateTail] using hh.comp hshift

def tailFactor (c : ℝ) (N : ℕ) (s : C0) : ℝ := min 1 (max (2-tau N s/c) 0)

theorem tailFactor_nonneg (c : ℝ) (N : ℕ) (s : C0) : 0 ≤ tailFactor c N s := by
  exact le_min zero_le_one (le_max_right _ _)

theorem tailFactor_le_one (c : ℝ) (N : ℕ) (s : C0) : tailFactor c N s ≤ 1 := min_le_left _ _

theorem tailFactor_eq_one {c : ℝ} (hc : 0 < c) (N : ℕ) (s : C0) (hs : tau N s ≤ c) :
    tailFactor c N s = 1 := by
  apply min_eq_left
  apply (le_max_left _ _).trans'
  have hdiv := (div_le_one hc).mpr hs
  linarith

theorem tailFactor_eq_zero {c : ℝ} (hc : 0 < c) (N : ℕ) (s : C0) (hs : 2*c ≤ tau N s) :
    tailFactor c N s = 0 := by
  have hdiv : 2 ≤ tau N s/c := (le_div_iff₀ hc).mpr hs
  simp [tailFactor, max_eq_right (show 2-tau N s/c ≤ 0 by linarith)]

theorem tailFactor_lipschitz {c : ℝ} (hc : 0 < c) (N : ℕ) :
    LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ (tailFactor c N) := by
  have ht : LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ (fun s => (2 : ℝ)-tau N s/c) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.dist_eq]
    change |(2-tau N s/c)-(2-tau N t/c)| ≤ c⁻¹ * dist s t
    calc
      _ = |tau N s-tau N t| / c := by
        rw [← abs_neg, neg_sub, show (2-tau N t/c)-(2-tau N s/c) = (tau N s-tau N t)/c by ring,
          abs_div, abs_of_pos hc]
      _ ≤ dist s t/c := div_le_div_of_nonneg_right
        (by simpa [Real.dist_eq] using (tau_lipschitz N).dist_le_mul s t) hc.le
      _ = _ := by ring
  have hh := (LipschitzWith.const (1 : ℝ)).min (ht.max (LipschitzWith.const (0 : ℝ)))
  change LipschitzWith _ (fun s => min 1 (max (2-tau N s/c) 0))
  apply hh.weaken
  exact max_le bot_le (max_le le_rfl bot_le)

theorem tailFactor_tendsto_one {c : ℝ} (hc : 0 < c) (s : C0) :
    Tendsto (fun N => tailFactor c N s) atTop (nhds 1) := by
  have hh : ∀ᶠ N in atTop, tau N s ≤ c :=
    (tau_tendsto_zero s).eventually (eventually_le_nhds hc)
  apply tendsto_const_nhds.congr'
  filter_upwards [hh] with N hN
  exact (tailFactor_eq_one hc N s hN).symm

theorem tailFactor_support {c : ℝ} (hc : 0 < c) (N : ℕ) :
    tsupport (tailFactor c N) ⊆ {s | tau N s ≤ 2*c} := by
  apply closure_minimal
  · intro s hs
    by_contra hh
    exact hs (tailFactor_eq_zero hc N s (le_of_not_ge hh))
  · exact isClosed_le (tau_lipschitz N).continuous continuous_const

theorem remainderTail_support {c : ℝ} (hc : 0 < c) (N : ℕ) :
    tsupport (fun s => tailFactor c N s-1) ⊆ {s | c ≤ tau N s} := by
  apply closure_minimal
  · intro s hs
    by_contra hh
    have he := tailFactor_eq_one hc N s (le_of_not_ge hh)
    exact hs (by simp only [he, sub_self])
  · exact isClosed_le continuous_const (tau_lipschitz N).continuous

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

open Set Filter Topology
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E U Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def absorptionMap (Q : Z →L[ℝ] U) (K : E × U → Z) (x : Z × E) : Z :=
  x.1 + K (x.2, Q x.1)

theorem absorption_onto {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) (g : E × U → U)
    (hg : Function.Surjective g)
    (hQK : ∀ x : E × U, Q (K x) = g x - x.2) :
    Function.Surjective (absorptionMap Q K) := by
  intro z
  obtain ⟨⟨t,u⟩, htu⟩ := hg (Q z)
  refine ⟨(z-K (t,u),t), ?_⟩
  have hQ : Q (z-K (t,u)) = u := by rw [map_sub, hQK, htu]; abel
  simp only [absorptionMap, hQ]
  abel

theorem absorption_upper {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) {LK : ℝ}
    (hLK : 0 ≤ LK) (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y) :
    ∀ x y, dist (absorptionMap Q K x) (absorptionMap Q K y) ≤
      (1+LK * max 1 ‖Q‖) * dist x y := by
  intro x y
  have hq : dist (Q x.1) (Q y.1) ≤ ‖Q‖ * dist x y :=
    (Q.lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left ((by rw [Prod.dist_eq]; exact le_max_left _ _ : dist x.1 y.1 ≤ dist x y)) (norm_nonneg Q))
  have ht : dist x.2 y.2 ≤ max 1 ‖Q‖ * dist x y := by
    calc
      dist x.2 y.2 ≤ dist x y := (by rw [Prod.dist_eq]; exact le_max_right _ _ : dist x.2 y.2 ≤ dist x y)
      _ = 1 * dist x y := (one_mul _).symm
      _ ≤ max 1 ‖Q‖ * dist x y := mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  have hinput : dist (x.2, Q x.1) (y.2, Q y.1) ≤ max 1 ‖Q‖ * dist x y := by
    rw [Prod.dist_eq]
    exact max_le ht (hq.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg))
  calc
    dist (absorptionMap Q K x) (absorptionMap Q K y)
      ≤ dist x.1 y.1 + dist (K (x.2,Q x.1)) (K (y.2,Q y.1)) := dist_add_add_le _ _ _ _
    _ ≤ dist x y + LK * (max 1 ‖Q‖ * dist x y) :=
      add_le_add ((by rw [Prod.dist_eq]; exact le_max_left _ _ : dist x.1 y.1 ≤ dist x y)) ((hK _ _).trans (mul_le_mul_of_nonneg_left hinput hLK))
    _ = _ := by ring

theorem absorption_inverse_bound {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) (g : E × U → U)
    {LK cg : ℝ} (hLK : 0 ≤ LK) (hcg : 0 < cg)
    (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y)
    (hg : ∀ x y, cg * dist x y ≤ dist (g x) (g y))
    (hQK : ∀ x : E × U, Q (K x) = g x-x.2) :
    ∀ x y, dist x y ≤ max (1+LK*‖Q‖/cg) (‖Q‖/cg) *
      dist (absorptionMap Q K x) (absorptionMap Q K y) := by
  intro x y
  let F := absorptionMap Q K
  have hQF (a : Z × E) : Q (F a) = g (a.2, Q a.1) := by
    simp only [F, absorptionMap, map_add, hQK]
    abel
  have hinput : dist (x.2,Q x.1) (y.2,Q y.1) ≤ (‖Q‖/cg) * dist (F x) (F y) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hcg).mpr
    calc
      dist (x.2, Q x.1) (y.2, Q y.1) * cg
        = cg * dist (x.2, Q x.1) (y.2, Q y.1) := mul_comm _ _
      _ ≤ dist (g (x.2,Q x.1)) (g (y.2,Q y.1)) := hg _ _
      _ = dist (Q (F x)) (Q (F y)) := by rw [hQF, hQF]
      _ ≤ ‖Q‖ * dist (F x) (F y) := Q.lipschitz.dist_le_mul _ _
  have hf : dist x.1 y.1 ≤ (1+LK*‖Q‖/cg) * dist (F x) (F y) := by
    calc
      dist x.1 y.1 = dist (F x-K (x.2,Q x.1)) (F y-K (y.2,Q y.1)) := by
        simp [F, absorptionMap]
      _ ≤ dist (F x) (F y)+dist (K (x.2,Q x.1)) (K (y.2,Q y.1)) := dist_sub_sub_le _ _ _ _
      _ ≤ dist (F x) (F y)+LK*((‖Q‖/cg)*dist (F x) (F y)) :=
        add_le_add_right ((hK _ _).trans (mul_le_mul_of_nonneg_left hinput hLK)) _
      _ = _ := by ring
  have hs : dist x.2 y.2 ≤ (‖Q‖/cg)*dist (F x) (F y) :=
    (show dist x.2 y.2 ≤ dist (x.2,Q x.1) (y.2,Q y.1) by rw [Prod.dist_eq]; exact le_max_left _ _).trans hinput
  rw [Prod.dist_eq]
  exact max_le (hf.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg))
    (hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg))

end
end C0Absorption

open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem normalize_norm_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (norm_normalize hx).le

theorem normalization_bound (x y : E) :
    ‖x‖ * dist (normalize x) (normalize y) ≤ 2 * dist x y := by
  have he : ‖x‖ • (normalize x-normalize y) = x-y+(‖y‖-‖x‖) • normalize y := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖x‖ * ‖normalize x-normalize y‖ = ‖‖x‖ • (normalize x-normalize y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = ‖x-y+(‖y‖-‖x‖) • normalize y‖ := by rw [he]
    _ ≤ ‖x-y‖ + ‖(‖y‖-‖x‖) • normalize y‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ + |‖y‖-‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add_right (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (normalize_norm_le_one y) (abs_nonneg (‖y‖-‖x‖))) _
    _ ≤ ‖x-y‖+‖x-y‖ := by
      apply add_le_add_right
      simpa only [abs_sub_comm] using abs_norm_sub_norm_le x y
    _ = 2*‖x-y‖ := by ring

def normalizedBall (x : E) : Metric.closedBall (0 : E) 1 :=
  ⟨normalize x, by simpa only [Metric.mem_closedBall, dist_zero_right] using normalize_norm_le_one x⟩

def zeroBall : Metric.closedBall (0 : E) 1 := ⟨0, by simp⟩

@[simp] theorem normalizedBall_zero : normalizedBall (0 : E) = zeroBall := by
  apply Subtype.ext
  simp [normalizedBall, zeroBall]

def radialLift (ζ : Metric.closedBall (0 : E) 1 → Z) (x : E) : Z :=
  ‖x‖ • ζ (normalizedBall x)

@[simp] theorem radialLift_zero (ζ : Metric.closedBall (0 : E) 1 → Z) : radialLift ζ 0 = 0 := by
  simp [radialLift]

theorem norm_pointMap_le_one {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ζ : Metric.closedBall (0 : E) 1 → Z)
    (hζ : LipschitzWith 1 ζ) (h0 : ζ zeroBall = 0) (s : Metric.closedBall (0 : E) 1) :
    ‖ζ s‖ ≤ 1 := by
  have hh := hζ.dist_le_mul s zeroBall
  rw [h0, dist_zero_right, NNReal.coe_one, one_mul] at hh
  have hb : dist s zeroBall ≤ 1 := s.property
  exact hh.trans hb

theorem radialLift_lipschitz (ζ : Metric.closedBall (0 : E) 1 → Z)
    (hζ : LipschitzWith 1 ζ) (h0 : ζ zeroBall = 0) : LipschitzWith 3 (radialLift ζ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : radialLift ζ x-radialLift ζ y =
      (‖x‖-‖y‖) • ζ (normalizedBall x) +
        ‖y‖ • (ζ (normalizedBall x)-ζ (normalizedBall y)) := by
    simp only [radialLift, sub_smul, smul_sub]
    abel
  have hdist : ‖ζ (normalizedBall x)-ζ (normalizedBall y)‖ ≤ dist (normalize x) (normalize y) := by
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, normalizedBall, dist_eq_norm, Subtype.coe_mk] using
      hζ.dist_le_mul (normalizedBall x) (normalizedBall y)
  calc
    dist (radialLift ζ x) (radialLift ζ y) = ‖radialLift ζ x-radialLift ζ y‖ := dist_eq_norm _ _
    _ ≤ |‖x‖-‖y‖|+‖y‖*dist (normalize x) (normalize y) := by
      rw [he]
      apply (norm_add_le _ _).trans
      rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
      exact add_le_add
        (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (norm_pointMap_le_one ζ hζ h0 (normalizedBall x)) (abs_nonneg (‖x‖-‖y‖)))
        (mul_le_mul_of_nonneg_left hdist (norm_nonneg y))
    _ ≤ dist x y + 2*dist x y := by
      apply add_le_add
      · simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y
      · simpa only [dist_comm] using normalization_bound y x
    _ = (3 : ℝ≥0)*dist x y := by norm_num; ring

theorem radialLift_homogeneous (ζ : Metric.closedBall (0 : E) 1 → Z) {r : ℝ}
    (hr : 0 ≤ r) (x : E) : radialLift ζ (r • x) = r • radialLift ζ x := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have he : normalizedBall (r • x) = normalizedBall x := by
    apply Subtype.ext
    exact normalize_smul_of_pos hr x
  simp only [radialLift, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_smul]

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure CylinderOperation (I : Finset ℕ) where
  scaleIndex : ℕ
  center : OperationGrid I scaleIndex
  isG : Bool

namespace CylinderOperation
variable {I : Finset ℕ}
def scale (r : CylinderOperation I) : ℝ := dyadic r.scaleIndex
def point (r : CylinderOperation I) : Cube I := operationGridPoint I r.scaleIndex r.center
def act (r : CylinderOperation I) : (Cube I → ℝ) →ₗ[ℝ] (Cube I → ℝ) :=
  localOp r.isG r.point r.scale

theorem scale_pos (r : CylinderOperation I) : 0 < r.scale := dyadic_pos r.scaleIndex

theorem act_lipschitz (r : CylinderOperation I) {K : ℝ≥0} {u : Cube I → ℝ}
    (hu : LipschitzWith K u) : LipschitzWith (4*K) (r.act u) := by
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact (localR_lipschitz r.point r.scale_pos u hu).weaken (by nlinarith)
  · exact localG_lipschitz r.point r.scale_pos u hu

theorem act_sup (r : CylinderOperation I) {A : ℝ} (hA : 0 ≤ A)
    {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) : ∀ x, |r.act u x| ≤ 2*A := by
  intro x
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact localR_sup r.point r.scale u A hu x
  · exact (localG_sup r.point r.scale u A hu x).trans (by linarith)

end CylinderOperation

def applyOperations {I : Finset ℕ} (ops : List (CylinderOperation I)) :
    (Cube I → ℝ) →ₗ[ℝ] (Cube I → ℝ) :=
  match ops with
  | [] => LinearMap.id
  | r :: rs => (applyOperations rs).comp r.act

@[simp] theorem applyOperations_nil {I : Finset ℕ} (u : Cube I → ℝ) : applyOperations [] u = u := rfl
@[simp] theorem applyOperations_cons {I : Finset ℕ} (r : CylinderOperation I)
    (rs : List (CylinderOperation I)) (u : Cube I → ℝ) :
    applyOperations (r::rs) u = applyOperations rs (r.act u) := rfl

theorem applyOperations_append {I : Finset ℕ} (rs ss : List (CylinderOperation I))
    (u : Cube I → ℝ) : applyOperations (rs++ss) u = applyOperations ss (applyOperations rs u) := by
  induction rs generalizing u with
  | nil => rfl
  | cons r rs ih => simpa using ih (r.act u)

theorem applyOperations_lipschitz {I : Finset ℕ} (ops : List (CylinderOperation I))
    {K : ℝ≥0} {u : Cube I → ℝ} (hu : LipschitzWith K u) :
    LipschitzWith (4^ops.length*K) (applyOperations ops u) := by
  induction ops generalizing K u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (r.act_lipschitz hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh

theorem applyOperations_sup {I : Finset ℕ} (ops : List (CylinderOperation I))
    {A : ℝ} (hA : 0 ≤ A) {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) :
    ∀ x, |applyOperations ops u x| ≤ 2^ops.length*A := by
  induction ops generalizing A u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (by positivity : 0 ≤ 2*A) (r.act_sup hA hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh

theorem applyOperations_support_bound {I : Finset ℕ} (ops : List (CylinderOperation I))
    (u : Cube I → ℝ) {φ : Cube I → ℝ} (hφ : LipschitzWith 1 φ) {b : ℝ}
    (hu : ∀ x ∈ tsupport u, φ x ≤ b) :
    ∀ x ∈ tsupport (applyOperations ops u), φ x ≤ b+(ops.map CylinderOperation.scale).sum := by
  induction ops generalizing u b with
  | nil => simpa using hu
  | cons r rs ih =>
    have hnew : ∀ x ∈ tsupport (r.act u), φ x ≤ b+r.scale := by
      simpa only [CylinderOperation.act, NNReal.coe_one, mul_one] using localOp_support_bound r.isG r.point r.scale_pos u φ hφ b hu
    have hh := ih (r.act u) hnew
    simpa only [List.map_cons, List.sum_cons, applyOperations_cons, add_assoc] using hh

structure CylinderBases (Γ : Type*) where
  coordinates : Γ → Finset ℕ
  coordinates_nonempty : ∀ γ, (coordinates γ).Nonempty
  band : Γ → ℕ
  ell : ℕ → ℝ
  ell_pos : ∀ j, 0 < ell j
  base : (γ : Γ) → Cube (coordinates γ) → ℝ
  A : ℝ≥0
  L0 : ℝ≥0
  base_sup : ∀ γ x, |base γ x| ≤ A
  base_lipschitz : ∀ γ, LipschitzWith L0 (base γ)

structure GeneratedRepresentation {Γ : Type*} (B : CylinderBases Γ) (γ : Γ) where
  operations : List (CylinderOperation (B.coordinates γ))
  ordered : operations.Pairwise (fun p q => q.scale ≤ p.scale)
  budget : (operations.map CylinderOperation.scale).sum < B.ell (B.band γ)/2

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

def cubeValue (r : GeneratedRepresentation B γ) : Cube (B.coordinates γ) → ℝ :=
  applyOperations r.operations (B.base γ)

def value (r : GeneratedRepresentation B γ) : C0Ball → ℝ :=
  r.cubeValue ∘ cubeRestrict (B.coordinates γ)

def baseRepresentation (B : CylinderBases Γ) (γ : Γ) : GeneratedRepresentation B γ :=
  ⟨[], by simp, by simpa using half_pos (B.ell_pos (B.band γ))⟩

theorem cubeValue_lipschitz (r : GeneratedRepresentation B γ) :
    LipschitzWith (4^r.operations.length*B.L0) r.cubeValue :=
  applyOperations_lipschitz _ (B.base_lipschitz γ)

theorem value_lipschitz (r : GeneratedRepresentation B γ) :
    LipschitzWith (4^r.operations.length*B.L0) r.value := by
  simpa only [value, mul_one] using r.cubeValue_lipschitz.comp (cubeRestrict_lipschitz (B.coordinates γ))

theorem cubeValue_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.cubeValue x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  applyOperations_sup _ B.A.coe_nonneg (B.base_sup γ)

theorem value_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.value x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  fun point => r.cubeValue_sup (cubeRestrict (B.coordinates γ) point)

end GeneratedRepresentation

def TClass {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) : Set (C0Ball → ℝ) :=
  {f | ∃ γ, ∃ r : GeneratedRepresentation B γ, r.operations.length ≤ h ∧ f = r.value}

structure TailOperation where
  scaleIndex : ℕ
  tailIndex : ℕ
  isBasic : Bool

namespace TailOperation

def factor (t : TailOperation) (s : C0Ball) : ℝ :=
  if t.isBasic then tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  else tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val-1

theorem factor_abs_le (t : TailOperation) (s : C0Ball) : |t.factor s| ≤ 1 := by
  have hl := tailFactor_nonneg (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  have hu := tailFactor_le_one (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  rw [abs_le]
  unfold factor
  split <;> constructor <;> linarith

theorem factor_lipschitz (t : TailOperation) : LipschitzWith (2^t.scaleIndex) t.factor := by
  apply LipschitzWith.of_dist_le_mul
  intro s u
  have hh := (tailFactor_lipschitz (dyadic_pos t.scaleIndex) (t.tailIndex+1)).dist_le_mul s.val u.val
  change dist (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val)
      (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) u.val) ≤
      (dyadic t.scaleIndex)⁻¹ * dist s u at hh
  simp only [dyadic, inv_inv] at hh
  simp only [NNReal.coe_pow, NNReal.coe_ofNat]
  cases ht : t.isBasic
  · simpa only [factor, dyadic, ht, Bool.false_eq_true, ↓reduceIte, dist_sub_right] using hh
  · simpa only [factor, dyadic, ht, ↓reduceIte] using hh

end TailOperation

def tailProduct (ts : List TailOperation) (s : C0Ball) : ℝ := (ts.map (fun t => t.factor s)).prod

@[simp] theorem tailProduct_nil (s : C0Ball) : tailProduct [] s = 1 := rfl
@[simp] theorem tailProduct_cons (t : TailOperation) (ts : List TailOperation) (s : C0Ball) :
    tailProduct (t::ts) s = t.factor s * tailProduct ts s := rfl

theorem tailProduct_abs_le (ts : List TailOperation) (s : C0Ball) : |tailProduct ts s| ≤ 1 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [tailProduct_cons, abs_mul]
    exact (mul_le_mul (t.factor_abs_le s) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem bounded_product_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfB : ∀ x, |f x| ≤ A) (hgB : ∀ x, |g x| ≤ B) :
    LipschitzWith (A*L+B*K) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x*g x-f y*g y = f x*(g x-g y)+g y*(f x-f y) := by ring
  rw [he]
  calc
    _ ≤ |f x*(g x-g y)|+|g y*(f x-f y)| := abs_add_le _ _
    _ = |f x| * |g x-g y|+|g y| * |f x-f y| := by rw [abs_mul, abs_mul]
    _ ≤ A*(L*dist x y)+B*(K*dist x y) := add_le_add
      (mul_le_mul (hfB x) (hg.dist_le_mul x y) (abs_nonneg _) A.coe_nonneg)
      (mul_le_mul (hgB y) (hf.dist_le_mul x y) (abs_nonneg _) B.coe_nonneg)
    _ = _ := by push_cast; ring

theorem tailProduct_lipschitz (ts : List TailOperation) :
    LipschitzWith ((ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum) (tailProduct ts) := by
  induction ts with
  | nil =>
    change LipschitzWith 0 (fun _ : C0Ball => (1 : ℝ))
    exact LipschitzWith.const 1
  | cons t ts ih =>
    have hh := bounded_product_lipschitz (A := 1) (B := 1) t.factor_lipschitz ih t.factor_abs_le (tailProduct_abs_le ts)
    convert hh using 1 <;> first | rfl | simp only [List.map_cons, List.sum_cons, one_mul, add_comm]

theorem tailProduct_lipschitz_bound (ts : List TailOperation) (h : ℕ)
    (hlen : ts.length ≤ h) (hscale : ∀ t ∈ ts, t.scaleIndex ≤ h) :
    LipschitzWith ((h : ℝ≥0)*2^h) (tailProduct ts) := by
  apply (tailProduct_lipschitz ts).weaken
  calc
    (ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum ≤
        (ts.map (fun _ => (2 : ℝ≥0)^h)).sum := List.sum_le_sum
          (fun t ht => pow_le_pow_right₀ (by norm_num) (hscale t ht))
    _ = (ts.length : ℝ≥0)*2^h := by simp
    _ ≤ (h : ℝ≥0)*2^h := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)

def VClass {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) : Set (C0Ball → ℝ) :=
  {f | ∃ γ, ∃ r : GeneratedRepresentation B γ, ∃ ts : List TailOperation,
    r.operations.length ≤ h ∧ B.band γ ≤ h ∧ ts.length ≤ h ∧
      (∀ t ∈ ts, t.scaleIndex ≤ h) ∧ f = fun s => r.value s*tailProduct ts s}

theorem TClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ TClass B h) : LipschitzWith (4^h*B.L0) f := by
  obtain ⟨γ,r,hlen,rfl⟩ := hf
  apply r.value_lipschitz.weaken
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) B.L0.coe_nonneg

theorem TClass_sup {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ TClass B h) : ∀ s, |f s| ≤ (2 : ℝ)^h*B.A := by
  obtain ⟨γ,r,hlen,rfl⟩ := hf
  intro s
  exact (r.value_sup s).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hlen) B.A.coe_nonneg)

theorem VClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : LipschitzWith (4^h*B.L0+h*4^h*B.A) f := by
  obtain ⟨γ,r,ts,hren,hband,hlen,hscale,rfl⟩ := hf
  have hu : LipschitzWith (4^h*B.L0) r.value := TClass_lipschitz B h ⟨γ,r,hren,rfl⟩
  have hb := tailProduct_lipschitz_bound ts h hlen hscale
  have hsup : ∀ s, |r.value s| ≤ ((2 : ℝ≥0)^h*B.A : ℝ≥0) := by
    intro s
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] using TClass_sup B h ⟨γ,r,hren,rfl⟩ s
  have hh := bounded_product_lipschitz (B := 1) hu hb hsup (tailProduct_abs_le ts)
  convert hh using 1 ; try rfl
  rw [one_mul]
  have hp : (4 : ℝ≥0)^h = 2^h*2^h := by rw [← mul_pow]; norm_num
  rw [hp]
  ring

theorem VClass_sup {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : ∀ s, |f s| ≤ (2 : ℝ)^h*B.A := by
  obtain ⟨γ,r,ts,hren,hband,hlen,hscale,rfl⟩ := hf
  intro s
  rw [abs_mul]
  exact (mul_le_mul (TClass_sup B h ⟨γ,r,hren,rfl⟩ s) (tailProduct_abs_le ts s)
    (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

def sourceClasses {Γ : Type*} (B : CylinderBases Γ) (n : ℕ) : Set (C0Ball → ℝ) :=
  if n % 2 = 0 then TClass B (n/2+1) else VClass B (n/2+1)

@[simp] theorem sourceClasses_even {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) :
    sourceClasses B (2*h) = TClass B (h+1) := by simp [sourceClasses]

@[simp] theorem sourceClasses_odd {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) :
    sourceClasses B (2*h+1) = VClass B (h+1) := by
  have hh : (2*h+1)/2 = h := by omega
  simp [sourceClasses, hh]

theorem tsupport_comp_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) {π : X → Y} (hπ : Continuous π) :
    tsupport (f ∘ π) ⊆ π ⁻¹' tsupport f := by
  apply closure_minimal
  · intro x hx; exact subset_tsupport f hx
  · exact (isClosed_tsupport f).preimage hπ

theorem tsupport_product_subset_left {X : Type*} [TopologicalSpace X] (f g : X → ℝ) :
    tsupport (fun x => f x*g x) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  exact subset_tsupport f (left_ne_zero_of_mul (show f x*g x ≠ 0 from hx))

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem support_bound (r : GeneratedRepresentation B γ) {φ : Cube (B.coordinates γ) → ℝ}
    (hφ : LipschitzWith 1 φ) {b : ℝ} (hu : ∀ x ∈ tsupport (B.base γ), φ x ≤ b) :
    ∀ s ∈ tsupport r.value,
      φ (cubeRestrict (B.coordinates γ) s) ≤ b+(r.operations.map CylinderOperation.scale).sum := by
  intro s hs
  have hm := tsupport_comp_subset r.cubeValue (cubeRestrict_lipschitz (B.coordinates γ)).continuous hs
  exact applyOperations_support_bound r.operations (B.base γ) hφ hu _ hm

def append (r : GeneratedRepresentation B γ) (op : CylinderOperation (B.coordinates γ))
    (hord : ∀ p ∈ r.operations, op.scale ≤ p.scale)
    (hbudget : (r.operations.map CylinderOperation.scale).sum+op.scale < B.ell (B.band γ)/2) :
    GeneratedRepresentation B γ where
  operations := r.operations++[op]
  ordered := List.pairwise_append.mpr ⟨r.ordered, by simp, by
    intro p hp q hq; have hq' : q=op := by simpa using hq
    subst q; exact hord p hp⟩
  budget := by simpa using hbudget

@[simp] theorem append_cubeValue (r : GeneratedRepresentation B γ) (op : CylinderOperation (B.coordinates γ))
    (hord : ∀ p ∈ r.operations, op.scale ≤ p.scale)
    (hbudget : (r.operations.map CylinderOperation.scale).sum+op.scale < B.ell (B.band γ)/2) :
    (r.append op hord hbudget).cubeValue = op.act r.cubeValue := by
  exact applyOperations_append r.operations [op] (B.base γ)

theorem eventually_append_allowed (r : GeneratedRepresentation B γ) :
    ∀ᶠ a in atTop, (∀ p ∈ r.operations, dyadic a ≤ p.scale) ∧
      (r.operations.map CylinderOperation.scale).sum+dyadic a < B.ell (B.band γ)/2 := by
  have h1 : ∀ᶠ a in atTop, ∀ p ∈ r.operations, dyadic a ≤ p.scale := by
    apply r.operations.finite_toSet.eventually_all.mpr
    intro p hp
    exact dyadic_tendsto.eventually (eventually_le_nhds p.scale_pos)
  have h2 : ∀ᶠ a in atTop, dyadic a < B.ell (B.band γ)/2-(r.operations.map CylinderOperation.scale).sum :=
    dyadic_tendsto.eventually (eventually_lt_nhds (sub_pos.mpr r.budget))
  filter_upwards [h1,h2] with a ha hb
  exact ⟨ha, by linarith⟩

end GeneratedRepresentation

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section ClassDuality
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def BoundedTest (f : S → ℝ) : Prop :=
  ∃ K : ℝ≥0, ∀ m : PreSpace L o, |pairing S f m| ≤ K*‖m‖

theorem class_pairing_bound (j : ℕ) (K : ℝ≥0)
    (hK : ∀ f ∈ L j, LipschitzWith K f) :
    ∃ A : ℝ≥0, ∀ f ∈ L j, ∀ m : PreSpace L o, |pairing S f m| ≤ A*‖m‖ := by
  obtain ⟨C,hC⟩ := exists_nat_gt (K : ℝ)
  obtain ⟨n,hn⟩ := triple_surjective (j,C,0)
  refine ⟨(squareWeight n)⁻¹,?_⟩
  intro f hf m
  apply test_pairing_bound L o n f
  · simpa only [hn] using hf
  · apply (hK f hf).weaken
    change K ≤ ((triple n).2.1 : ℝ≥0)+1
    rw [hn]
    exact_mod_cast (show (K : ℝ) ≤ (C : ℝ)+1 by linarith)

theorem BoundedTest.continuous {f : S → ℝ} (hf : BoundedTest L o f) :
    Continuous (completedPairing L o f) := by
  obtain ⟨K,hK⟩ := hf
  exact (completedPairing_lipschitz L o f K hK).continuous

theorem BoundedTest.weak_null {f : S → ℝ} (hf : BoundedTest L o f)
    (m : ℕ → TestSpace L o) (M : ℝ)
    (hm : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    Tendsto (fun i => completedPairing L o f (m i)) atTop (nhds 0) := by
  obtain ⟨K,hK⟩ := hf
  simpa only [completedTest_eq] using bounded_signs_weak_null m M hm (completedTest L o f K hK)

theorem pairing_add {S : Type*} [MetricSpace S]
    (f g : S → ℝ) (m : Molecule S) :
    pairing S (fun s => f s+g s) m = pairing S f m+pairing S g m := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, mul_add, Finsupp.sum, Finset.sum_add_distrib]

theorem pairing_smul {S : Type*} [MetricSpace S]
    (a : ℝ) (f : S → ℝ) (m : Molecule S) :
    pairing S (fun s => a*f s) m = a*pairing S f m := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem BoundedTest.add {f g : S → ℝ} (hf : BoundedTest L o f) (hg : BoundedTest L o g) :
    BoundedTest L o (fun s => f s+g s) := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨A,hA⟩ := hg
  refine ⟨K+A,fun m => ?_⟩
  erw [pairing_add]
  exact (abs_add_le _ _).trans ((add_le_add (hK m) (hA m)).trans_eq (by push_cast; ring))

theorem BoundedTest.smul {f : S → ℝ} (hf : BoundedTest L o f) (a : ℝ) :
    BoundedTest L o (fun s => a*f s) := by
  obtain ⟨K,hK⟩ := hf
  refine ⟨‖a‖₊*K,fun m => ?_⟩
  erw [pairing_smul, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hK m) (abs_nonneg a)).trans_eq (by
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]; ring)

theorem completedPairing_add (f g : S → ℝ) (hf : BoundedTest L o f) (hg : BoundedTest L o g)
    (z : TestSpace L o) : completedPairing L o (fun s => f s+g s) z =
      completedPairing L o f z+completedPairing L o g z := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨A,hA⟩ := hg
  obtain ⟨B,hB⟩ := (BoundedTest.add L o ⟨K,hK⟩ ⟨A,hA⟩)
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (completedPairing_lipschitz L o _ B hB).continuous
      ((completedPairing_lipschitz L o _ K hK).continuous.add (completedPairing_lipschitz L o _ A hA).continuous)
  | ih m =>
    change completedPairing L o _ (toTestSpace L o m) = _
    erw [completedPairing_coe L o _ B hB, completedPairing_coe L o _ K hK,
      completedPairing_coe L o _ A hA]
    exact pairing_add f g m

theorem completedPairing_smul (a : ℝ) (f : S → ℝ) (hf : BoundedTest L o f)
    (z : TestSpace L o) : completedPairing L o (fun s => a*f s) z = a*completedPairing L o f z := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨B,hB⟩ := BoundedTest.smul L o ⟨K,hK⟩ a
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (completedPairing_lipschitz L o _ B hB).continuous
      (continuous_const.mul (completedPairing_lipschitz L o _ K hK).continuous)
  | ih m =>
    change completedPairing L o _ (toTestSpace L o m) = _
    erw [completedPairing_coe L o _ B hB, completedPairing_coe L o _ K hK]
    exact pairing_smul a f m

end ClassDuality

variable {Γ : Type*} {B : CylinderBases Γ}

def c0Origin : C0Ball := ⟨0,by simp⟩
abbrev SourceSpace (B : CylinderBases Γ) := TestSpace (sourceClasses B) c0Origin

theorem TClass_mono {h k : ℕ} (hk : h ≤ k) : TClass B h ⊆ TClass B k := by
  rintro f ⟨γ,r,hr,rfl⟩
  exact ⟨γ,r,hr.trans hk,rfl⟩

theorem VClass_mono {h k : ℕ} (hk : h ≤ k) : VClass B h ⊆ VClass B k := by
  rintro f ⟨γ,r,ts,hr,hj,ht,hs,rfl⟩
  exact ⟨γ,r,ts,hr.trans hk,hj.trans hk,ht.trans hk,fun t hm => (hs t hm).trans hk,rfl⟩

theorem representation_mem_VClass {γ : Γ} (r : GeneratedRepresentation B γ) {h : ℕ}
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h) : r.value ∈ VClass B h := by
  refine ⟨γ,r,[],hr,hj,by simp,by simp,?_⟩
  funext s
  simp

theorem sourceClasses_lipschitz (B : CylinderBases Γ) (n : ℕ) :
    ∃ K : ℝ≥0, ∀ f ∈ sourceClasses B n, LipschitzWith K f := by
  unfold sourceClasses
  split
  · exact ⟨_, fun _ hf => TClass_lipschitz B _ hf⟩
  · exact ⟨_, fun _ hf => VClass_lipschitz B _ hf⟩

theorem TClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ TClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h) (4^(h+1)*B.L0) (by
    simpa only [sourceClasses_even] using (fun f hf => TClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_even] using TClass_mono (Nat.le_succ h) hf)⟩

theorem VClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ VClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h+1)
    (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A) (by
      simpa only [sourceClasses_odd, Nat.cast_add, Nat.cast_one] using (fun f hf => VClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) hf)⟩

theorem TClass_bounded {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ TClass B h) :
    BoundedTest (sourceClasses B) c0Origin f := by
  obtain ⟨A,hA⟩ := TClass_pairing_bound B h
  exact ⟨A,hA f hf⟩

theorem VClass_bounded {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ VClass B h) :
    BoundedTest (sourceClasses B) c0Origin f := by
  obtain ⟨A,hA⟩ := VClass_pairing_bound B h
  exact ⟨A,hA f hf⟩

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def flattenOperation (I : Finset ℕ) (a : ℕ) (v : Cube I) : CylinderOperation I :=
  ⟨a,nearestOperationGrid I a v,true⟩

@[simp] theorem flattenOperation_scale (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    (flattenOperation I a v).scale = dyadic a := rfl

@[simp] theorem flattenOperation_act (I : Finset ℕ) (a : ℕ) (v : Cube I) (u : Cube I → ℝ) :
    (flattenOperation I a v).act u = localG (flattenOperation I a v).point (dyadic a) u := rfl

theorem flattenOperation_center (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    dist v (flattenOperation I a v).point ≤ dyadic a/16 := nearestOperationGrid_dist I a v

theorem flattenOperation_plateau (I : Finset ℕ) (a : ℕ) (v : Cube I) (u : Cube I → ℝ)
    (x : Cube I) (hx : dist x v < 3*dyadic a/8) :
    (flattenOperation I a v).act u x = u (flattenOperation I a v).point := by
  apply localG_plateau _ (dyadic_pos a) u x
  have hh := dist_triangle x v (flattenOperation I a v).point
  have hc := flattenOperation_center I a v
  linarith [dyadic_pos a]

theorem flattenOperation_difference (I : Finset ℕ) (a : ℕ) (v : Cube I)
    {u : Cube I → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (x : Cube I) :
    |(flattenOperation I a v).act u x-u x| ≤ dyadic a*K := by
  rw [flattenOperation_act, localG_eq, add_sub_cancel_left]
  exact localR_sup_lip _ (dyadic_pos a) u hu x

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem exists_flatten (r : GeneratedRepresentation B γ) (ts : List TailOperation)
    (h : ℕ) (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ts.length ≤ h) (hs : ∀ t ∈ ts, t.scaleIndex ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin (fun s => r'.value s*tailProduct ts s) z-
        completedPairing (sourceClasses B) c0Origin (fun s => r.value s*tailProduct ts s) z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by
  have he := r.eventually_append_allowed.and (dyadic_tendsto.eventually (eventually_lt_nhds hcap))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let op (n : ℕ) := flattenOperation (B.coordinates γ) (N+n) v
  have ho (n : ℕ) : ∀ p ∈ r.operations, (op n).scale ≤ p.scale := (hN (N+n) (by omega)).1.1
  have hb (n : ℕ) : (r.operations.map CylinderOperation.scale).sum+(op n).scale < B.ell (B.band γ)/2 :=
    (hN (N+n) (by omega)).1.2
  let rr (n : ℕ) := r.append (op n) (ho n) (hb n)
  let f (n : ℕ) (s : C0Ball) := (rr n).value s*tailProduct ts s
  let g (s : C0Ball) := r.value s*tailProduct ts s
  have hf (n : ℕ) : f n ∈ VClass B (h+1) := by
    refine ⟨γ,rr n,ts,?_,hj.trans (Nat.le_succ h),ht.trans (Nat.le_succ h),
      fun t hm => (hs t hm).trans (Nat.le_succ h),rfl⟩
    simpa only [rr, append, List.length_append, List.length_singleton] using Nat.add_le_add_right hr 1
  have hsc : Tendsto (fun n => dyadic (N+n)) atTop (nhds 0) :=
    dyadic_tendsto.comp (tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ N+n) tendsto_id)
  have hp (s : C0Ball) : Tendsto (fun n => f n s) atTop (nhds (g s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound (n : ℕ) : dist (f n s) (g s) ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
      simp only [f,g,Real.dist_eq,← sub_mul,abs_mul]
      have hd : |(rr n).value s-r.value s| ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
        change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)-r.cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
        rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
        exact flattenOperation_difference _ (N+n) v r.cubeValue_lipschitz _
      exact (mul_le_mul hd (tailProduct_abs_le ts s) (abs_nonneg _) (mul_nonneg (dyadic_pos _).le (NNReal.coe_nonneg _))).trans_eq (mul_one _)
    exact squeeze_zero (fun n => dist_nonneg) hbound (by simpa using hsc.mul_const ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ))
  obtain ⟨A,hA⟩ := VClass_pairing_bound B (h+1)
  have hconv := (completedPairing_tendsto (sourceClasses B) c0Origin f g A
    (fun n => hA (f n) (hf n)) hp).2 z
  have hev : ∀ᶠ n in atTop, |completedPairing (sourceClasses B) c0Origin (f n) z-
      completedPairing (sourceClasses B) c0Origin g z| < δ := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hconv) δ hδ
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨N+n,rr n,(hN (N+n) (by omega)).2,rfl,hn,?_,?_⟩
  · intro s hss
    change (rr n).cubeValue (cubeRestrict (B.coordinates γ) s) = _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact flattenOperation_plateau _ _ _ r.cubeValue _ hss
  · intro s
    change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact localG_sup _ _ _ _ r.cubeValue_sup _

theorem exists_flatten_T (r : GeneratedRepresentation B γ)
    (h : ℕ) (hr : r.operations.length ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin r'.value z-
        completedPairing (sourceClasses B) c0Origin r.value z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by
  have he := r.eventually_append_allowed.and (dyadic_tendsto.eventually (eventually_lt_nhds hcap))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let op (n : ℕ) := flattenOperation (B.coordinates γ) (N+n) v
  have ho (n : ℕ) : ∀ p ∈ r.operations, (op n).scale ≤ p.scale := (hN (N+n) (by omega)).1.1
  have hb (n : ℕ) : (r.operations.map CylinderOperation.scale).sum+(op n).scale < B.ell (B.band γ)/2 :=
    (hN (N+n) (by omega)).1.2
  let rr (n : ℕ) := r.append (op n) (ho n) (hb n)
  let f (n : ℕ) (s : C0Ball) := (rr n).value s
  let g (s : C0Ball) := r.value s
  have hf (n : ℕ) : f n ∈ TClass B (h+1) := by
    refine ⟨γ,rr n,?_,rfl⟩
    simpa only [rr, append, List.length_append, List.length_singleton] using Nat.add_le_add_right hr 1
  have hsc : Tendsto (fun n => dyadic (N+n)) atTop (nhds 0) :=
    dyadic_tendsto.comp (tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ N+n) tendsto_id)
  have hp (s : C0Ball) : Tendsto (fun n => f n s) atTop (nhds (g s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound (n : ℕ) : dist (f n s) (g s) ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
      change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)-r.cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
      rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
      exact flattenOperation_difference _ (N+n) v r.cubeValue_lipschitz _
    exact squeeze_zero (fun n => dist_nonneg) hbound (by simpa using hsc.mul_const ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ))
  obtain ⟨A,hA⟩ := TClass_pairing_bound B (h+1)
  have hconv := (completedPairing_tendsto (sourceClasses B) c0Origin f g A
    (fun n => hA (f n) (hf n)) hp).2 z
  have hev : ∀ᶠ n in atTop, |completedPairing (sourceClasses B) c0Origin (f n) z-
      completedPairing (sourceClasses B) c0Origin g z| < δ := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hconv) δ hδ
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨N+n,rr n,(hN (N+n) (by omega)).2,rfl,hn,?_,?_⟩
  · intro s hss
    change (rr n).cubeValue (cubeRestrict (B.coordinates γ) s) = _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact flattenOperation_plateau _ _ _ r.cubeValue _ hss
  · intro s
    change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact localG_sup _ _ _ _ r.cubeValue_sup _

end GeneratedRepresentation
end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology

theorem thin_sequence {r : ℕ → ℕ → Prop} (hr : ∀ i, ∀ᶠ j in atTop, r i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i j, i < j → r (φ i) (φ j) := by
  have he (t : Set ℕ) (ht : t.Finite) : ∀ᶠ j in atTop, ∀ i ∈ t, i<j ∧ r i j :=
    (eventually_all_finite ht).mpr (fun i _ => (eventually_gt_atTop i).and (hr i))
  obtain ⟨φ,hφ⟩ := seq_of_forall_finite_exists (fun t ht => (he t ht).exists)
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_comm.mp hφ.1, forall_comm.mp hφ.2⟩

theorem finite_constant_subsequence {A : Type*} [Finite A] (f : ℕ → A) :
    ∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a := by
  have hh : ∃ a, ∃ᶠ i in atTop, f i=a := by
    by_contra hn
    push Not at hn
    have hf : ∀ᶠ i in atTop, ∀ a, f i≠a := Filter.eventually_all.mpr hn
    obtain ⟨i,hi⟩ := hf.exists
    exact hi (f i) rfl
  obtain ⟨a,ha⟩ := hh
  obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
  exact ⟨a,φ,hm,hp⟩

theorem constant_or_injective_subsequence {A : Type*} (f : ℕ → A) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Function.Injective (f ∘ φ)) := by
  by_cases h : ∃ a, ∃ᶠ i in atTop, f i=a
  · obtain ⟨a,ha⟩ := h
    obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
    exact Or.inl ⟨a,φ,hm,hp⟩
  · push Not at h
    obtain ⟨φ,hm,hp⟩ := thin_sequence (r := fun i j => f i≠f j) (fun i => by
      simpa only [ne_eq, eq_comm] using h (f i))
    refine Or.inr ⟨φ,hm,?_⟩
    intro i j hij
    apply le_antisymm <;> by_contra hn
    · exact hp j i (lt_of_not_ge hn) hij.symm
    · exact hp i j (lt_of_not_ge hn) hij

theorem nat_constant_or_tendsto (f : ℕ → ℕ) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    Tendsto f atTop atTop := by
  by_cases h : ∃ a, ∃ᶠ i in atTop, f i=a
  · obtain ⟨a,ha⟩ := h
    obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
    exact Or.inl ⟨a,φ,hm,hp⟩
  · push Not at h
    apply Or.inr
    apply tendsto_atTop.mpr
    intro N
    have hh : ∀ᶠ i in atTop, ∀ a ∈ Finset.range N, f i≠a :=
      (eventually_all_finite (Finset.range N).finite_toSet).mpr (fun a _ => h a)
    filter_upwards [hh] with i hi
    by_contra hn
    exact hi (f i) (Finset.mem_range.mpr (lt_of_not_ge hn)) rfl

theorem finite_subsequence_selection {A : Type*} [Finite A]
    (P : A → (ℕ → ℕ) → Prop)
    (hstable : ∀ a (φ ψ : ℕ → ℕ), StrictMono φ → StrictMono ψ → P a φ → P a (φ ∘ ψ))
    (hselect : ∀ a (φ : ℕ → ℕ), StrictMono φ → ∃ ψ, StrictMono ψ ∧ P a (φ ∘ ψ)) :
    ∃ φ, StrictMono φ ∧ ∀ a, P a φ := by
  classical
  let := Fintype.ofFinite A
  suffices h : ∀ s : Finset A, ∃ φ, StrictMono φ ∧ ∀ a ∈ s, P a φ from
    by simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨id,strictMono_id,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨φ,hm,hp⟩ := ih
    obtain ⟨ψ,hn,hq⟩ := hselect a φ hm
    refine ⟨φ ∘ ψ,hm.comp hn,?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hq
    · exact hstable b φ ψ hm hn (hp b hb)

theorem choose_mono_sequence {P : ℕ → ℕ → Prop} (hP : ∀ i, ∀ᶠ j in atTop, P i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, P i (φ i) := by
  have he (i j : ℕ) : ∃ k, j<k ∧ P i k := ((eventually_gt_atTop j).and (hP i)).exists
  choose next hn using he
  let φ : ℕ → ℕ := fun n => Nat.rec (next 0 0) (fun n prev => next (n+1) prev) n
  have hφs (n : ℕ) : φ (n+1) = next (n+1) (φ n) := rfl
  refine ⟨φ,strictMono_nat_of_lt_succ (fun n => ?_),?_⟩
  · rw [hφs]; exact (hn (n+1) (φ n)).1
  · intro i
    cases i with
    | zero => exact (hn 0 0).2
    | succ i => exact (hn (i+1) (φ i)).2

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem nested_selection_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (u b : ℕ → S → ℝ) (C : ℕ → Set S) (e : ℕ → ℝ)
    (K Kb : ℝ≥0) (hu : ∀ i, Continuous (u i)) (hb : ∀ i, LipschitzWith Kb (b i))
    (hF : ∀ i, LipschitzWith K (fun x => u i x*b i x))
    (hC : ∀ i, IsOpen (C i)) (hc : ∀ i, ∀ x ∈ C i, u i x=e i)
    (hnest : ∀ i, ∀ᶠ j in atTop, tsupport (u j) ⊆ C i)
    (hsmall : Tendsto (fun i => |e i| *(Kb : ℝ)) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (K+1) (fun x => ∑ i, ε i * (u (φ i) x*b (φ i) x)) := by
  have he (i : ℕ) : ∀ᶠ j in atTop, |e j| *(Kb : ℝ) ≤ (1/2 : ℝ)^(i+1) :=
    hsmall.eventually (eventually_le_nhds (by positivity))
  obtain ⟨ψ,hψ,heψ⟩ := choose_mono_sequence he
  obtain ⟨η,hη,hrel⟩ := thin_sequence (r := fun i j => tsupport (u (ψ j)) ⊆ C (ψ i))
    (fun i => hψ.tendsto_atTop.eventually (hnest (ψ i)))
  let φ := ψ ∘ η
  refine ⟨φ,hψ.comp hη,?_⟩
  have hprod (i : ℕ) : |e (φ i)| *(Kb : ℝ) ≤ (1/2 : ℝ)^(i+1) := by
    exact (heψ (η i)).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.add_le_add_right (hη.id_le i) 1))
  intro n ε hε
  have hh := nested_supports_signed_lipschitz hS n
    (fun i : Fin n => u (φ i)) (fun i : Fin n => b (φ i))
    (fun i : Fin n => e (φ i)) (fun i : Fin n => C (φ i)) K
    (fun _ : Fin n => Kb) (fun i => hu _) (fun i => hb _) (fun i => hF _)
    (fun i => hC _) (fun i => hc _) (fun i j hij => hrel i j hij) ε hε
  apply hh.weaken
  refine add_le_add le_rfl ?_
  have hsum : (∑ i : Fin n, |e (φ i)| *(Kb : ℝ)) ≤ 1 := by
    calc
      _ ≤ ∑ i : Fin n, (1/2 : ℝ)^(i.val+1) := Finset.sum_le_sum (fun i _ => hprod i)
      _ = ∑ i ∈ Finset.range n, (1/2 : ℝ)^(i+1) := (Finset.sum_range (fun i : ℕ => (1/2 : ℝ)^(i+1))).symm
      _ ≤ ∑' i : ℕ, (1/2 : ℝ)^(i+1) := Summable.sum_le_tsum _ (fun _ _ => by positivity) geometric_summable
      _ = 1 := geometric_tsum
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using hsum

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure TagLocalization {Γ : Type*} (B : CylinderBases Γ) where
  tag : Γ → ℕ → Icc (-1 : ℝ) 1
  contains_prefix : ∀ γ, Finset.range (B.band γ) ⊆ B.coordinates γ
  ell_tendsto : Tendsto B.ell atTop (nhds 0)
  base_support : ∀ γ (k : B.coordinates γ), k.val < B.band γ →
    ∀ x ∈ tsupport (B.base γ), dist (x k) (tag γ k.val) ≤ 2*dyadic (B.band γ)

namespace TagLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)

theorem representation_support {γ : Γ} (r : GeneratedRepresentation B γ)
    (k : ℕ) (hk : k < B.band γ) (s : C0Ball) (hs : s ∈ tsupport r.value) :
    dist (s.val k) (loc.tag γ k).val ≤ 2*dyadic (B.band γ)+B.ell (B.band γ)/2 := by
  let l : B.coordinates γ := ⟨k,loc.contains_prefix γ (Finset.mem_range.mpr hk)⟩
  let φ : Cube (B.coordinates γ) → ℝ := fun x => dist (x l) (loc.tag γ k)
  have hφ : LipschitzWith 1 φ := by
    simpa only [φ,Function.comp_def,one_mul] using (LipschitzWith.dist_left (loc.tag γ k)).comp (LipschitzWith.eval l)
  have hp := r.support_bound hφ (loc.base_support γ l hk) s hs
  exact hp.trans (add_le_add le_rfl r.budget.le)

theorem projected_concentration (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (hj : Tendsto (fun i => B.band (γ i)) atTop atTop)
    (v : ℕ → Icc (-1 : ℝ) 1) (hv : Tendsto (fun i => loc.tag (γ i)) atTop (nhds v))
    (I : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ s ∈ tsupport (r i).value,
      dist (cubeRestrict I s) (fun k : I => v k.val) < ε := by
  have ha : Tendsto (fun i => 2*dyadic (B.band (γ i))+B.ell (B.band (γ i))/2) atTop (nhds 0) := by
    simpa only [Function.comp_def,mul_zero,zero_div,zero_add] using
      ((dyadic_tendsto.comp hj).const_mul 2).add ((loc.ell_tendsto.comp hj).div_const 2)
  have he := ha.eventually (eventually_lt_nhds (half_pos hε))
  have hall : ∀ᶠ i in atTop, ∀ k : I, k.val < B.band (γ i) ∧
      dist (loc.tag (γ i) k.val) (v k.val) < ε/2 := by
    apply Filter.eventually_all.mpr
    intro k
    exact (hj.eventually (eventually_gt_atTop k.val)).and
      ((Metric.tendsto_nhds.mp (tendsto_pi_nhds.mp hv k.val)) (ε/2) (half_pos hε))
  filter_upwards [he,hall] with i hi htag
  intro s hs
  apply (dist_pi_lt_iff hε).mpr
  intro k
  have hb := loc.representation_support (r i) k.val (htag k).1 s hs
  have hc := (htag k).2
  have hd := dist_triangle (cubeRestrict I s k) (loc.tag (γ i) k.val) (v k.val)
  change dist (s.val k.val) (v k.val).val < ε
  change dist (s.val k.val) (v k.val).val ≤
    dist (s.val k.val) (loc.tag (γ i) k.val).val + dist (loc.tag (γ i) k.val) (v k.val) at hd
  linarith

end TagLocalization

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem high_bands_compatible {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)
    (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i)) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h)
    (hj : Tendsto (fun i => B.band (γ i)) atTop atTop)
    (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (r i).value (m i)|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ TClass B (h+1)) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (4^(h+1)*B.L0+1) (fun s => ∑ i, ε i*F i s) := by
  obtain ⟨v,hv,ψ,hψ,hvψ⟩ := isCompact_univ.isSeqCompact.subseq_of_frequently_in
    (x := fun i => loc.tag (γ i)) (Filter.Eventually.of_forall (fun _ => mem_univ _)).frequently
  have hfl (i : ℕ) := (r (ψ i)).exists_flatten_T h (hr (ψ i))
    (fun k => v k.val) (m (ψ i)) (half_pos hδ) (show (0 : ℝ)<1 by norm_num)
  choose a rr hcap hops hdif hflat hsup using hfl
  have hmem (i : ℕ) : (rr i).value ∈ TClass B (h+1) := by
    refine ⟨γ (ψ i),rr i,?_,rfl⟩
    rw [hops i,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (hr (ψ i)) 1
  let C (i : ℕ) : Set C0Ball :=
    {s | dist (cubeRestrict (B.coordinates (γ (ψ i))) s)
      (fun k => v k.val) < 3*dyadic (a i)/8}
  let e (i : ℕ) := (r (ψ i)).cubeValue
    (flattenOperation (B.coordinates (γ (ψ i))) (a i) (fun k => v k.val)).point
  have hC (i : ℕ) : IsOpen (C i) :=
    Metric.isOpen_ball.preimage (cubeRestrict_lipschitz _).continuous
  have hnest (i : ℕ) : ∀ᶠ j in atTop, tsupport (rr j).value ⊆ C i := by
    have hp := loc.projected_concentration (γ ∘ ψ) rr (hj.comp hψ.tendsto_atTop) v hvψ
      (B.coordinates (γ (ψ i))) (show 0 < 3*dyadic (a i)/8 by have := dyadic_pos (a i); positivity)
    exact hp
  obtain ⟨η,hη,hLip⟩ := nested_selection_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i => (rr i).value) (fun _ _ => 1) C e (4^(h+1)*B.L0) 0
    (fun i => (rr i).value_lipschitz.continuous) (fun _ => LipschitzWith.const 1)
    (fun i => by simpa only [mul_one] using TClass_lipschitz B (h+1) (hmem i))
    hC (fun i s hs => hflat i s hs) hnest (by simp only [NNReal.coe_zero,mul_zero]; exact tendsto_const_nhds)
  refine ⟨ψ ∘ η,hψ.comp hη,fun i => (rr (η i)).value,fun i => hmem _,?_,?_⟩
  · intro i
    have hb := hdif (η i)
    have ha := hd (ψ (η i))
    have hab := abs_sub_abs_le_abs_sub
      (completedPairing (sourceClasses B) c0Origin (r (ψ (η i))).value (m (ψ (η i))))
      (completedPairing (sourceClasses B) c0Origin (rr (η i)).value (m (ψ (η i))))
    rw [abs_sub_comm] at hab
    change δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (rr (η i)).value (m (ψ (η i)))|
    linarith
  · intro n ε hε
    simpa only [mul_one] using hLip n ε hε

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem tsupport_product_subset_right {X : Type*} [TopologicalSpace X] (f g : X → ℝ) :
    tsupport (fun x => f x*g x) ⊆ tsupport g := by
  simpa only [mul_comm] using tsupport_product_subset_left g f

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_mul_tail {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ VClass B h) (a N : ℕ) :
    (fun s => f s*tailFactor (dyadic a) (N+1) s.val) ∈ VClass B (h+a+1) := by
  obtain ⟨γ,r,ts,hr,hj,ht,hs,rfl⟩ := hf
  let t : TailOperation := ⟨a,N,true⟩
  refine ⟨γ,r,t::ts,by omega,by omega,by simpa using (show ts.length+1 ≤ h+a+1 by omega),?_,?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · change a ≤ h+a+1; omega
    · have hh := hs q hq; omega
  · funext s
    simp only [tailProduct_cons, t, TailOperation.factor, ↓reduceIte]
    ring

theorem tail_separation {h : ℕ} (F : ℕ → C0Ball → ℝ) (m : ℕ → SourceSpace B)
    (hF : ∀ i, F i ∈ VClass B h) {δ cstar : ℝ} (hδ : 0 < δ) (hcstar : 0 < cstar)
    (hdetect : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hsupport : ∀ i s, s ∈ tsupport (F i) → cstar ≤ tau (M i) s.val) :
    ∃ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℕ → C0Ball → ℝ,
      (∀ i, G i ∈ VClass B H) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (G i) (m (φ i))|) ∧
      Pairwise (fun i j => Disjoint (tsupport (G i)) (tsupport (G j))) := by
  have he : ∀ᶠ a in atTop, dyadic a < cstar/2 :=
    dyadic_tendsto.eventually (eventually_lt_nhds (half_pos hcstar))
  obtain ⟨a,ha⟩ := he.exists
  let H := h+a+1
  let f (i N : ℕ) (s : C0Ball) := F i s*tailFactor (dyadic a) (N+1) s.val
  have hf (i N : ℕ) : f i N ∈ VClass B H := VClass_mul_tail (hF i) a N
  obtain ⟨A,hA⟩ := VClass_pairing_bound B H
  have hconv (i : ℕ) : Tendsto
      (fun N => completedPairing (sourceClasses B) c0Origin (f i N) (m i)) atTop
      (nhds (completedPairing (sourceClasses B) c0Origin (F i) (m i))) := by
    apply (completedPairing_tendsto (sourceClasses B) c0Origin (f i) (F i) A
      (fun N => hA (f i N) (hf i N)) ?_).2
    intro s
    have hh := (tailFactor_tendsto_one (dyadic_pos a) s.val).comp
      (tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id)
    simpa only [f,mul_one,Function.comp_def,Nat.succ_eq_add_one] using hh.const_mul (F i s)
  have hchoose (i : ℕ) : ∃ N, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (f i N) (m i)| := by
    have hev := (Metric.tendsto_nhds.mp (hconv i)) (δ/2) (half_pos hδ)
    obtain ⟨N,hN⟩ := hev.exists
    refine ⟨N,?_⟩
    rw [Real.dist_eq] at hN
    have hab := abs_sub_abs_le_abs_sub
      (completedPairing (sourceClasses B) c0Origin (F i) (m i))
      (completedPairing (sourceClasses B) c0Origin (f i N) (m i))
    rw [abs_sub_comm] at hab
    linarith [hdetect i]
  choose N hN using hchoose
  obtain ⟨φ,hφ,hrel⟩ := thin_sequence (r := fun i j => N i+1 ≤ M j) (fun i =>
    hM.eventually (eventually_ge_atTop (N i+1)))
  refine ⟨H,φ,hφ,fun i => f (φ i) (N (φ i)),fun i => hf _ _,fun i => hN _,?_⟩
  have hdis (i j : ℕ) (hij : i<j) : Disjoint
      (tsupport (f (φ i) (N (φ i)))) (tsupport (f (φ j) (N (φ j)))) := by
    apply Set.disjoint_left.mpr
    intro s hi hj
    have hi' := tsupport_product_subset_right (F (φ i))
      (fun s : C0Ball => tailFactor (dyadic a) (N (φ i)+1) s.val) hi
    have hi'' := tsupport_comp_subset (tailFactor (dyadic a) (N (φ i)+1)) continuous_subtype_val hi'
    have hupper := tailFactor_support (dyadic_pos a) (N (φ i)+1) hi''
    have hj' := tsupport_product_subset_left (F (φ j))
      (fun s : C0Ball => tailFactor (dyadic a) (N (φ j)+1) s.val) hj
    have hlower := hsupport (φ j) s hj'
    have hord := tau_antitone s.val (hrel i j hij)
    change tau (N (φ i)+1) s.val ≤ 2*dyadic a at hupper
    linarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hdis i j hlt
  · exact (hdis j i hgt).symm

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem tau_cubeExtend_restrict_le (I : Finset ℕ) (N : ℕ) (s : C0Ball) :
    tau N (cubeExtend I (cubeRestrict I s)).val ≤ tau N s.val := by
  classical
  apply c0_norm_le _ (tau_nonneg _ _)
  intro k
  rw [coordinateTail_apply]
  by_cases hk : N < k
  · simp only [hk, ↓reduceIte]
    change |extendFinite I (fun i => (cubeRestrict I s i).val) k| ≤ _
    rw [extendFinite_apply]
    split_ifs with hi
    · have hb := c0_norm_apply_le (coordinateTail N s.val) k
      simpa only [coordinateTail_apply,hk,↓reduceIte,tau,cubeRestrict] using hb
    · simpa using tau_nonneg N s.val
  · simpa only [hk,↓reduceIte,abs_zero] using tau_nonneg N s.val

structure RadiusLocalization {Γ : Type*} (B : CylinderBases Γ) where
  terminal : Γ → Prop
  firstCoordinate : Γ → ℕ
  finite_exceptions : ∀ j N, {γ | B.band γ ≤ j ∧ (terminal γ ∨ firstCoordinate γ ≤ N)}.Finite
  base_radius : ∀ γ, ¬terminal γ → ∀ N, N < firstCoordinate γ →
    ∀ x ∈ tsupport (B.base γ), B.ell (B.band γ) ≤ tau N (cubeExtend (B.coordinates γ) x).val

namespace RadiusLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : RadiusLocalization B)

theorem representation_tail_lower {γ : Γ} (r : GeneratedRepresentation B γ)
    (ht : ¬loc.terminal γ) (N : ℕ) (hN : N < loc.firstCoordinate γ)
    (s : C0Ball) (hs : s ∈ tsupport r.value) :
    B.ell (B.band γ)/2 ≤ tau N s.val := by
  let φ : Cube (B.coordinates γ) → ℝ := fun x => -tau N (cubeExtend (B.coordinates γ) x).val
  have hφ : LipschitzWith 1 φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [φ,dist_neg_neg,NNReal.coe_one,one_mul]
    calc
      _ ≤ dist (cubeExtend (B.coordinates γ) x).val (cubeExtend (B.coordinates γ) y).val :=
        by simpa only [NNReal.coe_one,one_mul] using (tau_lipschitz N).dist_le_mul _ _
      _ ≤ dist x y := by
        simpa only [NNReal.coe_one,one_mul,Subtype.dist_eq] using (cubeExtend_lipschitz (B.coordinates γ)).dist_le_mul x y
  have hb : ∀ x ∈ tsupport (B.base γ), φ x ≤ -B.ell (B.band γ) := by
    intro x hx
    exact neg_le_neg (loc.base_radius γ ht N hN x hx)
  have hh := r.support_bound hφ hb s hs
  have htau := tau_cubeExtend_restrict_le (B.coordinates γ) N s
  have hbudget := r.budget
  dsimp only [φ] at hh
  linarith

include loc in

theorem low_bands_disjoint (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (ts : ℕ → List TailOperation) (h j : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : ∀ i, B.band (γ i)=j) (hjh : j ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (hγ : Function.Injective γ) (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) :
    ∃ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ VClass B H) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      Pairwise (fun i k => Disjoint (tsupport (F i)) (tsupport (F k))) := by
  have hgood (N : ℕ) : ∀ᶠ i in atTop, ¬loc.terminal (γ i) ∧ N < loc.firstCoordinate (γ i) := by
    have he := (hγ.tendsto_cofinite).eventually ((loc.finite_exceptions j N).eventually_cofinite_notMem)
    rw [Nat.cofinite_eq_atTop] at he
    filter_upwards [he] with i hi
    have hh : ¬(loc.terminal (γ i) ∨ loc.firstCoordinate (γ i) ≤ N) := by
      intro hn
      exact hi ⟨(hj i).le,hn⟩
    simpa only [not_or,not_le] using hh
  obtain ⟨ψ,hψ,hψgood⟩ := choose_mono_sequence hgood
  let f (i : ℕ) (s : C0Ball) := (r (ψ i)).value s*tailProduct (ts (ψ i)) s
  have hf (i : ℕ) : f i ∈ VClass B h :=
    ⟨γ (ψ i),r (ψ i),ts (ψ i),hr _,by rw [hj]; exact hjh,ht _,ha _,rfl⟩
  obtain ⟨H,η,hη,F,hF,hdet,hdis⟩ := tail_separation f (m ∘ ψ) hf hδ
    (half_pos (B.ell_pos j)) (fun i => hd (ψ i)) id tendsto_id (by
      intro i s hs
      have hsu := tsupport_product_subset_left (r (ψ i)).value (tailProduct (ts (ψ i))) hs
      have hh := loc.representation_tail_lower (r (ψ i)) (hψgood i).1 i (hψgood i).2 s hsu
      simpa only [hj,id_eq] using hh)
  exact ⟨H,ψ ∘ η,hψ.comp hη,F,hF,hdet,hdis⟩

end RadiusLocalization
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem small_supports_compatible {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (q : ℕ → Cube (B.coordinates γ)) (a b : ℕ → ℝ)
    (haPos : ∀ i, 0 < a i) (ha0 : Tendsto a atTop (nhds 0)) (hb0 : Tendsto b atTop (nhds 0))
    (hsup : ∀ i x, |(r i).cubeValue x| ≤ b i)
    (hsupp : ∀ i x, x ∈ tsupport (r i).cubeValue → dist x (q i) ≤ a i)
    (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ VClass B (h+1)) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A+1)
          (fun s => ∑ i, ε i*F i s) := by
  obtain ⟨v,hv,ψ,hψ,hvψ⟩ := isCompact_univ.isSeqCompact.subseq_of_frequently_in
    (x := q) (Filter.Eventually.of_forall (fun _ => mem_univ _)).frequently
  have hfl (i : ℕ) := (r (ψ i)).exists_flatten (ts (ψ i)) h (hr _) hj (ht _) (ha _)
    v (m (ψ i)) (half_pos hδ) (haPos (ψ i))
  choose θ rr hcap hops hdif hflat hsupold using hfl
  have hmem (i : ℕ) : (fun s => (rr i).value s*tailProduct (ts (ψ i)) s) ∈ VClass B (h+1) := by
    refine ⟨γ,rr i,ts (ψ i),?_,hj.trans (Nat.le_succ _),(ht _).trans (Nat.le_succ _),
      fun t hm => (ha _ t hm).trans (Nat.le_succ _),rfl⟩
    rw [hops i,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (hr (ψ i)) 1
  have hnew (i : ℕ) (s : C0Ball) (hs : s ∈ tsupport (rr i).value) :
      dist (cubeRestrict (B.coordinates γ) s) (q (ψ i)) ≤ 2*a (ψ i) := by
    have he : (rr i).cubeValue = (flattenOperation (B.coordinates γ) (θ i) v).act (r (ψ i)).cubeValue := by
      simp only [GeneratedRepresentation.cubeValue,hops i,applyOperations_append,applyOperations_cons,applyOperations_nil]
    have hcube := tsupport_comp_subset (rr i).cubeValue (cubeRestrict_lipschitz _).continuous hs
    rw [he] at hcube
    have hh := localOp_support_bound true (flattenOperation (B.coordinates γ) (θ i) v).point
      (dyadic_pos (θ i)) (r (ψ i)).cubeValue (fun x => dist x (q (ψ i)))
      (LipschitzWith.dist_left _) (a (ψ i)) (hsupp (ψ i)) _ hcube
    simp only [NNReal.coe_one] at hh
    linarith [hcap i]
  let C (i : ℕ) : Set C0Ball :=
    {s | dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic (θ i)/8}
  let e (i : ℕ) := (r (ψ i)).cubeValue (flattenOperation (B.coordinates γ) (θ i) v).point
  have hC (i : ℕ) : IsOpen (C i) :=
    Metric.isOpen_ball.preimage (cubeRestrict_lipschitz _).continuous
  have hnest (i : ℕ) : ∀ᶠ j in atTop, tsupport (rr j).value ⊆ C i := by
    have hrad : Tendsto (fun j => 2*a (ψ j)+dist (q (ψ j)) v) atTop (nhds 0) := by
      simpa only [Function.comp_def,mul_zero,dist_self,zero_add] using
        ((ha0.comp hψ.tendsto_atTop).const_mul 2).add (hvψ.dist (show Tendsto (fun _ : ℕ => v) atTop (nhds v) from tendsto_const_nhds))
    have he := hrad.eventually (eventually_lt_nhds
      (show (0 : ℝ)<3*dyadic (θ i)/8 by have := dyadic_pos (θ i); positivity))
    filter_upwards [he] with j hj
    intro s hs
    exact lt_of_le_of_lt ((dist_triangle _ (q (ψ j)) _).trans (add_le_add (hnew j s hs) le_rfl)) hj
  have hesmall : Tendsto (fun i => |e i| * ((h : ℝ≥0)*2^h : ℝ≥0)) atTop (nhds 0) := by
    have he0 : Tendsto (fun i => |e i|) atTop (nhds 0) := squeeze_zero
      (fun _ => abs_nonneg _) (fun i => hsup (ψ i) _) (hb0.comp hψ.tendsto_atTop)
    simpa only [zero_mul] using he0.mul_const (((h : ℝ≥0)*2^h : ℝ≥0) : ℝ)
  obtain ⟨η,hη,hLip⟩ := nested_selection_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i => (rr i).value) (fun i => tailProduct (ts (ψ i))) C e
    (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A) ((h : ℝ≥0)*2^h)
    (fun i => (rr i).value_lipschitz.continuous)
    (fun i => tailProduct_lipschitz_bound _ h (ht _) (ha _))
    (fun i => by simpa only [Nat.cast_add,Nat.cast_one] using VClass_lipschitz B (h+1) (hmem i)) hC (fun i s hs => hflat i s hs) hnest hesmall
  refine ⟨ψ ∘ η,hψ.comp hη,fun i s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s,
    fun i => hmem _,?_,hLip⟩
  intro i
  have hb := hdif (η i)
  have hh := hd (ψ (η i))
  have hab := abs_sub_abs_le_abs_sub
    (completedPairing (sourceClasses B) c0Origin
      (fun s => (r (ψ (η i))).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i))))
    (completedPairing (sourceClasses B) c0Origin
      (fun s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i))))
  rw [abs_sub_comm] at hab
  change δ/2 ≤ |completedPairing (sourceClasses B) c0Origin
    (fun s => (rr (η i)).value s*tailProduct (ts (ψ (η i))) s) (m (ψ (η i)))|
  linarith

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def SignedBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ) : Prop :=
  ∀ n (ι : Fin n → ℕ), Function.Injective ι → ∀ ε : Fin n → Bool,
    ‖∑ i, realSign (ε i) • m (ι i)‖ ≤ M

namespace SignedBound
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ → X} {M : ℝ} (hm : SignedBound m M)

include hm

theorem initial : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M :=
  fun n ε => hm n Fin.val Fin.val_injective ε

theorem subsequence {φ : ℕ → ℕ} (hφ : Function.Injective φ) : SignedBound (m ∘ φ) M :=
  fun n ι hι ε => hm n (φ ∘ ι) (hφ.comp hι) ε

theorem nonneg : 0 ≤ M := by
  simpa using hm.initial 0 (fun i => Fin.elim0 i)

end SignedBound

theorem compatible_detectors_false {S : Type*} [MetricSpace S]
    (L : ℕ → Set (S → ℝ)) (o : S)
    (m : ℕ → TestSpace L o) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → S → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ L h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ) (hd : ∀ i, δ ≤ |completedPairing L o (F i) (m i)|) : False := by
  obtain ⟨C,hC⟩ := exists_nat_gt (K : ℝ)
  obtain ⟨d,hdtriple⟩ := triple_surjective (h,C,0)
  have hKC : K ≤ listConstant d := by
    change K ≤ ((triple d).2.1 : ℝ≥0)+1
    rw [hdtriple]
    exact_mod_cast (show (K : ℝ) ≤ (C : ℝ)+1 by linarith)
  let l (n : ℕ) : AdmissibleList (L (triple d).1) (listConstant d) :=
    ⟨n,fun i => F i,fun i => by simpa only [hdtriple] using hF i,
      fun ε hε => (hLip n ε hε).weaken hKC⟩
  have hExp : (listExponent d).toReal = 2 := by rw [listExponent_toReal,hdtriple]; norm_num
  have hb (i : ℕ) : ∃ A : ℝ≥0, ∀ z : PreSpace L o, |pairing S (F i) z| ≤ A*‖z‖ := by
    let j : Fin (i+1) := ⟨i,Nat.lt_succ_self i⟩
    exact ⟨(squareWeight d)⁻¹,list_test_pairing_bound L o d (l (i+1)) j⟩
  choose A hA using hb
  let u (i : ℕ) : TestSpace L o →ₗ[ℝ] ℝ := (completedTest L o (F i) (A i) (hA i)).toLinearMap
  have hu (i : ℕ) (z : TestSpace L o) : u i z = completedPairing L o (F i) z :=
    completedTest_eq L o _ _ _ _
  apply no_infinite_detectors m u ((squareWeight d : ℝ)^2) M δ
    (sq_pos_of_pos (squareWeight_pos d)) hm.nonneg hδ hm.initial
  · intro n z
    have hl := (completedList_le_sigma L o d (l n) z).trans (completedSigma_le L o d z)
    have heq : ‖completedList L o d (l n) z‖^2 = ∑ i : Fin n, (u i z)^2 := by
      have he := finite_lp_norm_rpow (listExponent d) (by rw [hExp]; norm_num)
        (completedList L o d (l n) z)
      rw [hExp] at he
      simp only [Real.rpow_two,sq_abs] at he
      rw [he]
      apply Finset.sum_congr rfl
      intro i hi
      change (completedList L o d (l n) z i)^2 = (u i z)^2
      rw [completedList_apply,hu]
    have hleft : 0 ≤ ‖completedList L o d (l n) z‖ := norm_nonneg _
    have hscale : (squareWeight d : ℝ)*‖completedList L o d (l n) z‖ ≤ ‖z‖ := by
      calc
        _ ≤ (squareWeight d : ℝ)*((squareWeight d : ℝ)⁻¹*‖z‖) :=
          mul_le_mul_of_nonneg_left hl (squareWeight d).coe_nonneg
        _ = ‖z‖ := by rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt (squareWeight_pos d)),one_mul]
    have hs := pow_le_pow_left₀ (mul_nonneg (squareWeight d).coe_nonneg hleft) hscale 2
    simpa only [mul_pow,heq] using hs
  · intro i
    simpa only [hu] using hd i

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_compatible_false (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ VClass B h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  apply compatible_detectors_false (sourceClasses B) c0Origin m M hm F (2*h+1) K _ hLip hδ hd
  intro i
  simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) (hF i)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem detection_split (a b : ℕ → ℝ) {δ : ℝ}
    (hd : ∀ i, δ ≤ |a i+b i|) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, δ/2 ≤ |a (φ i)|) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, δ/2 ≤ |b (φ i)|) := by
  have hh : ∀ i, δ/2 ≤ |a i| ∨ δ/2 ≤ |b i| := by
    intro i
    by_contra hn
    push Not at hn
    have h := (hd i).trans (abs_add_le (a i) (b i))
    linarith [hn.1,hn.2]
  have hf := Filter.frequently_or_distrib.mp (show ∀ᶠ i in atTop, δ/2 ≤ |a i| ∨ δ/2 ≤ |b i| from Filter.Eventually.of_forall hh).frequently
  rcases hf with hf | hf
  · exact Or.inl (extraction_of_frequently_atTop hf)
  · exact Or.inr (extraction_of_frequently_atTop hf)

namespace CylinderOperation
variable {I : Finset ℕ}

def remainder (op : CylinderOperation I) : CylinderOperation I := {op with isG := false}
@[simp] theorem remainder_scale (op : CylinderOperation I) : op.remainder.scale=op.scale := rfl
@[simp] theorem remainder_point (op : CylinderOperation I) : op.remainder.point=op.point := rfl
@[simp] theorem remainder_act (op : CylinderOperation I) (u : Cube I → ℝ) :
    op.remainder.act u = localR op.point op.scale u := rfl

theorem act_split (op : CylinderOperation I) (hG : op.isG=true) (u : Cube I → ℝ) :
    op.act u = u+op.remainder.act u := by
  rw [remainder_act]
  have he : op.act u = localG op.point op.scale u := by
    unfold act localOp
    rw [hG]
    rfl
  rw [he]
  ext x
  exact localG_eq op.point op.scale u x

theorem finite_scale_fiber (a : ℕ) : Finite {op : CylinderOperation I // op.scaleIndex=a} := by
  apply Finite.of_surjective
    (fun p : OperationGrid I a × Bool => (⟨⟨a,p.1,p.2⟩,rfl⟩ : {op : CylinderOperation I // op.scaleIndex=a}))
  rintro ⟨⟨a',c,g⟩,hh⟩
  change a'=a at hh
  subst a'
  exact ⟨(c,g),rfl⟩

theorem constant_or_small (op : ℕ → CylinderOperation I) :
    (∃ p, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, op (φ i)=p) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i => (op (φ i)).scale) atTop (nhds 0) ∧
      ∃ g : Bool, ∀ i, (op (φ i)).isG=g) := by
  rcases nat_constant_or_tendsto (fun i => (op i).scaleIndex) with ⟨a,ψ,hψ,ha⟩ | ha
  · let := finite_scale_fiber (I := I) a
    obtain ⟨p,η,hη,hp⟩ := finite_constant_subsequence
      (fun i => (⟨op (ψ i),ha i⟩ : {p : CylinderOperation I // p.scaleIndex=a}))
    exact Or.inl ⟨p.val,ψ ∘ η,hψ.comp hη,fun i => congrArg Subtype.val (hp i)⟩
  · obtain ⟨g,ψ,hψ,hg⟩ := finite_constant_subsequence (fun i => (op i).isG)
    exact Or.inr ⟨ψ,hψ,(dyadic_tendsto.comp ha).comp hψ.tendsto_atTop,g,hg⟩

end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

def subrepresentation (r : GeneratedRepresentation B γ) (ops : List (CylinderOperation (B.coordinates γ)))
    (ho : ops.Sublist r.operations) : GeneratedRepresentation B γ where
  operations := ops
  ordered := r.ordered.sublist ho
  budget := lt_of_le_of_lt ((ho.map CylinderOperation.scale).sum_le_sum (by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    exact p.scale_pos.le)) r.budget

def sameScales (r : GeneratedRepresentation B γ) (ops : List (CylinderOperation (B.coordinates γ)))
    (hs : ops.map CylinderOperation.scale = r.operations.map CylinderOperation.scale) :
    GeneratedRepresentation B γ where
  operations := ops
  ordered := by
    apply (List.pairwise_map (R := fun a b : ℝ => b ≤ a)).mp
    rw [hs]
    exact List.pairwise_map.mpr r.ordered
  budget := by rw [hs]; exact r.budget

theorem length_le_of_prefix (r : GeneratedRepresentation B γ)
    (pre suf : List (CylinderOperation (B.coordinates γ))) (he : r.operations=pre++suf) {h : ℕ}
    (hh : r.operations.length ≤ h) : pre.length ≤ h := by
  rw [he,List.length_append] at hh
  omega

end GeneratedRepresentation

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_disjoint_false (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (h : ℕ) (hF : ∀ i, F i ∈ VClass B h)
    (hdisj : Pairwise (fun i j => Disjoint (tsupport (F i)) (tsupport (F j))))
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  refine VClass_compatible_false m M hm F h (4^h*B.L0+h*4^h*B.A) hF ?_ hδ hd
  intro n ε hε
  apply disjoint_supports_signed_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i : Fin n => F i) (4^h*B.L0+h*4^h*B.A) (fun i => VClass_lipschitz B h (hF i)) _ ε hε
  intro i j hij
  exact hdisj (show (i : ℕ) ≠ (j : ℕ) from fun he => hij (Fin.ext he))

theorem tail_escape_false (F : ℕ → C0Ball → ℝ) (m : ℕ → SourceSpace B)
    (h : ℕ) (hF : ∀ i, F i ∈ VClass B h) (M : ℝ) (hm : SignedBound m M)
    {δ cstar : ℝ} (hδ : 0 < δ) (hcstar : 0 < cstar)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hs : ∀ i s, s ∈ tsupport (F i) → cstar ≤ tau (N i) s.val) : False := by
  obtain ⟨H,φ,hφ,G,hG,hdG,hdis⟩ := tail_separation F m hF hδ hcstar hd N hN hs
  exact VClass_disjoint_false (m ∘ φ) M (hm.subsequence hφ.injective) G H hG hdis (half_pos hδ) hdG

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem small_remainders_false {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (op : ℕ → CylinderOperation (B.coordinates γ))
    (hsmall : Tendsto (fun i => (op i).scale) atTop (nhds 0))
    (p : Cube (B.coordinates γ) → ℝ) (K : ℝ≥0) (hp : LipschitzWith K p)
    (suf : ℕ → List (CylinderOperation (B.coordinates γ)))
    (hlen : ∀ i, (suf i).length ≤ h)
    (horder : ∀ i t, t ∈ suf i → t.scale ≤ (op i).scale)
    (heq : ∀ i, (r i).cubeValue = applyOperations (suf i) ((op i).remainder.act p))
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  let a (i : ℕ) : ℝ := (h+1)*(op i).scale
  let b (i : ℕ) : ℝ := 2^h*K*(op i).scale
  have haPos (i : ℕ) : 0 < a i := by
    dsimp [a]; have := (op i).scale_pos; positivity
  have ha0 : Tendsto a atTop (nhds 0) := by simpa only [a,mul_zero] using hsmall.const_mul (h+1 : ℝ)
  have hb0 : Tendsto b atTop (nhds 0) := by simpa only [b,mul_zero] using hsmall.const_mul (2^h*(K : ℝ))
  have hsup (i : ℕ) (x : Cube (B.coordinates γ)) : |(r i).cubeValue x| ≤ b i := by
    rw [heq i]
    have hh := applyOperations_sup (suf i) (mul_nonneg (op i).scale_pos.le K.coe_nonneg)
      (fun x => localR_sup_lip (op i).point (op i).scale_pos p hp x) x
    rw [CylinderOperation.remainder_act]
    calc
      _ ≤ 2^(suf i).length*((op i).scale*K) := hh
      _ ≤ 2^h*((op i).scale*K) := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (hlen i)) (mul_nonneg (op i).scale_pos.le K.coe_nonneg)
      _ = b i := by dsimp [b]; ring
  have hsupp (i : ℕ) (x : Cube (B.coordinates γ)) (hx : x ∈ tsupport (r i).cubeValue) :
      dist x (op i).point ≤ a i := by
    rw [heq i,CylinderOperation.remainder_act] at hx
    have hh := applyOperations_support_bound (suf i) (localR (op i).point (op i).scale p)
      (LipschitzWith.dist_left (op i).point) (fun x hx => localR_support_ball (op i).point (op i).scale_pos p hx) x hx
    have hs : ((suf i).map CylinderOperation.scale).sum ≤ (h : ℝ)*(op i).scale := by
      calc
        _ ≤ ((suf i).map (fun _ => (op i).scale)).sum := List.sum_le_sum (fun t ht => horder i t ht)
        _ = ((suf i).length : ℝ)*(op i).scale := by simp
        _ ≤ (h : ℝ)*(op i).scale := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen i) (op i).scale_pos.le
    dsimp [a]
    linarith
  obtain ⟨φ,hφ,F,hF,hdF,hLip⟩ := small_supports_compatible r ts h hr hj ht ha
    (fun i => (op i).point) a b haPos ha0 hb0 hsup hsupp m hδ hd
  exact VClass_compatible_false (m ∘ φ) M (hm.subsequence hφ.injective) F (h+1) _ hF hLip (half_pos hδ) hdF

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TailOperation
@[ext] theorem ext' {a b : TailOperation} (hs : a.scaleIndex=b.scaleIndex)
    (hn : a.tailIndex=b.tailIndex) (hg : a.isBasic=b.isBasic) : a=b := by
  cases a; cases b; simp_all

def remainder (t : TailOperation) : TailOperation := {t with isBasic := false}
@[simp] theorem remainder_scaleIndex (t : TailOperation) : t.remainder.scaleIndex=t.scaleIndex := rfl
@[simp] theorem remainder_tailIndex (t : TailOperation) : t.remainder.tailIndex=t.tailIndex := rfl
@[simp] theorem remainder_isBasic (t : TailOperation) : t.remainder.isBasic=false := rfl

theorem factor_split (t : TailOperation) (ht : t.isBasic=true) (s : C0Ball) :
    t.factor s = 1+t.remainder.factor s := by simp [factor,remainder,ht]

theorem constant_or_escape (t : ℕ → TailOperation) (h : ℕ) (ht : ∀ i, (t i).scaleIndex ≤ h) :
    (∃ p, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, t (φ i)=p) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a g,
      (∀ i, (t (φ i)).scaleIndex=a) ∧ (∀ i, (t (φ i)).isBasic=g) ∧
      Tendsto (fun i => (t (φ i)).tailIndex) atTop atTop) := by
  obtain ⟨ag,ψ,hψ,hag⟩ := finite_constant_subsequence
    (fun i => ((⟨(t i).scaleIndex,Nat.lt_succ_of_le (ht i)⟩ : Fin (h+1)),(t i).isBasic))
  have ha (i : ℕ) : (t (ψ i)).scaleIndex=ag.1.val := congrArg (fun p : Fin (h+1) × Bool => p.1.val) (hag i)
  have hg (i : ℕ) : (t (ψ i)).isBasic=ag.2 := congrArg Prod.snd (hag i)
  rcases nat_constant_or_tendsto (fun i => (t (ψ i)).tailIndex) with ⟨N,η,hη,hN⟩ | hN
  · exact Or.inl ⟨⟨ag.1.val,N,ag.2⟩,ψ ∘ η,hψ.comp hη,fun i => ext' (ha _) (hN _) (hg _)⟩
  · exact Or.inr ⟨ψ,hψ,ag.1.val,ag.2,ha,hg,hN⟩
end TailOperation

@[simp] theorem tailProduct_append (pre post : List TailOperation) (s : C0Ball) :
    tailProduct (pre++post) s = tailProduct pre s*tailProduct post s := by
  simp only [tailProduct,List.map_append,List.prod_append]

theorem tailProduct_eq_zero (ts : List TailOperation) (t : TailOperation) (ht : t ∈ ts)
    (s : C0Ball) (hz : t.factor s=0) : tailProduct ts s=0 := by
  unfold tailProduct
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨t,ht,hz⟩

theorem full_tail_support (f : C0Ball → ℝ) (ts : List TailOperation) (t : TailOperation)
    (ht : t ∈ ts) (hg : t.isBasic=false) :
    tsupport (fun s => f s*tailProduct ts s) ⊆ {s | dyadic t.scaleIndex ≤ tau (t.tailIndex+1) s.val} := by
  apply closure_minimal
  · intro s hs
    have hn : t.factor s ≠ 0 := by
      intro hz
      exact hs (by change f s*tailProduct ts s=0; rw [tailProduct_eq_zero ts t ht s hz,mul_zero])
    have hh := remainderTail_support (dyadic_pos t.scaleIndex) (t.tailIndex+1)
      (subset_tsupport _ (show tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val-1 ≠ 0 by
        simpa only [TailOperation.factor,hg,Bool.false_eq_true,↓reduceIte] using hn))
    exact hh
  · exact isClosed_le continuous_const ((tau_lipschitz _).continuous.comp continuous_subtype_val)

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

theorem constant_detector_false (f : C0Ball → ℝ) (hf : BoundedTest (sourceClasses B) c0Origin f)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin f (m i)|) : False := by
  have hh := (hf.weak_null (sourceClasses B) c0Origin m M hm.initial).abs
  have he : ∀ᶠ i in atTop, |completedPairing (sourceClasses B) c0Origin f (m i)| < δ :=
    hh.eventually (show ∀ᶠ x in nhds |(0 : ℝ)|, x<δ by simpa only [abs_zero] using eventually_lt_nhds hδ)
  obtain ⟨i,hi⟩ := he.exists
  exact (not_lt_of_ge (hd i)) hi

theorem tail_remainder_false (f : ℕ → C0Ball → ℝ) (ts : ℕ → List TailOperation)
    (t : ℕ → TailOperation) (ht : ∀ i, t i ∈ ts i) (hg : ∀ i, (t i).isBasic=false)
    (a : ℕ) (ha : ∀ i, (t i).scaleIndex=a) (hN : Tendsto (fun i => (t i).tailIndex) atTop atTop)
    (h : ℕ) (hF : ∀ i, (fun s => f i s*tailProduct (ts i) s) ∈ VClass B h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => f i s*tailProduct (ts i) s) (m i)|) : False := by
  apply tail_escape_false (fun i s => f i s*tailProduct (ts i) s) m h hF M hm hδ (dyadic_pos a) hd
    (fun i => (t i).tailIndex+1) (tendsto_atTop_mono (fun i => Nat.le_succ _) hN)
  intro i s hs
  simpa only [ha i,Set.mem_ofPred_eq] using full_tail_support (f i) (ts i) (t i) (ht i) (hg i) hs

theorem fixed_cylinder_tails_false_aux {γ : Γ} (r : GeneratedRepresentation B γ) (h : ℕ)
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h) (n : ℕ) :
    ∀ (pre : List TailOperation) (post : ℕ → List TailOperation),
      (∀ i, (post i).length=n) →
      (∀ i, (pre++post i).length ≤ h) →
      (∀ i t, t ∈ pre++post i → t.scaleIndex ≤ h) →
      ∀ (m : ℕ → SourceSpace B) (M : ℝ), SignedBound m M →
      ∀ δ : ℝ, 0 < δ →
      (∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
        (fun s => r.value s*tailProduct (pre++post i) s) (m i)|) → False := by
  induction n with
  | zero =>
    intro pre post hn hlen hscale m M hm δ hδ hd
    have hz (i : ℕ) : post i=[] := List.length_eq_zero_iff.mp (hn i)
    have hmem : (fun s => r.value s*tailProduct pre s) ∈ VClass B h := by
      refine ⟨γ,r,pre,hr,hj,?_,?_,rfl⟩
      · simpa only [hz 0,List.append_nil] using hlen 0
      · intro t ht
        apply hscale 0 t
        exact List.mem_append.mpr (Or.inl ht)
    apply constant_detector_false _ (VClass_bounded hmem) m M hm hδ
    intro i
    simpa only [hz i,List.append_nil] using hd i
  | succ n ih =>
    intro pre post hn hlen hscale m M hm δ hδ hd
    have hc (i : ℕ) : ∃ t rest, post i=t::rest ∧ rest.length=n := by
      obtain ⟨t,rest,he⟩ := List.length_pos_iff_exists_cons.mp (show 0<(post i).length by rw [hn]; omega)
      refine ⟨t,rest,he,?_⟩
      have hh := hn i
      rw [he,List.length_cons] at hh
      omega
    choose t rest he hrest using hc
    have ht (i : ℕ) : t i ∈ pre++post i := List.mem_append.mpr (Or.inr (by rw [he]; exact List.mem_cons_self))
    rcases TailOperation.constant_or_escape t h (fun i => hscale i _ (ht i)) with
      ⟨p,ψ,hψ,hp⟩ | ⟨ψ,hψ,a,g,ha,hg,hN⟩
    · have heq (i : ℕ) : (pre++[p])++rest (ψ i)=pre++post (ψ i) := by
        rw [he,hp,List.append_assoc,List.singleton_append]
      apply ih (pre++[p]) (fun i => rest (ψ i)) (fun i => hrest _) (fun i => by rw [heq]; exact hlen _)
        (fun i t ht => hscale (ψ i) t (by rw [← heq]; exact ht)) (m ∘ ψ) M
        (hm.subsequence hψ.injective) δ hδ
      intro i
      simpa only [heq,Function.comp_def] using hd (ψ i)
    · let ts0 (i : ℕ) := pre++post (ψ i)
      have hmem0 (i : ℕ) : (fun s => r.value s*tailProduct (ts0 i) s) ∈ VClass B h :=
        ⟨γ,r,ts0 i,hr,hj,hlen _,hscale _,rfl⟩
      cases g with
      | false =>
        exact tail_remainder_false (fun _ => r.value) ts0 (t ∘ ψ) (fun i => ht _) hg a ha hN
          h hmem0 (m ∘ ψ) M (hm.subsequence hψ.injective) hδ (fun i => hd (ψ i))
      | true =>
        let tsA (i : ℕ) := pre++rest (ψ i)
        let tsB (i : ℕ) := pre++(t (ψ i)).remainder::rest (ψ i)
        have hlenA (i : ℕ) : (tsA i).length ≤ h := by
          have hh := hlen (ψ i)
          simp only [he,List.length_append,List.length_cons] at hh
          simp only [tsA,List.length_append]
          omega
        have hscaleA (i : ℕ) (q : TailOperation) (hq : q ∈ tsA i) : q.scaleIndex ≤ h := by
          apply hscale (ψ i) q
          rw [he,List.mem_append,List.mem_cons]
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl hq
          · exact Or.inr (Or.inr hq)
        have hlenB (i : ℕ) : (tsB i).length ≤ h := by
          simpa only [tsB,he,List.length_append,List.length_cons] using hlen (ψ i)
        have hscaleB (i : ℕ) (q : TailOperation) (hq : q ∈ tsB i) : q.scaleIndex ≤ h := by
          rcases List.mem_append.mp hq with hq | hq
          · exact hscale (ψ i) q (List.mem_append.mpr (Or.inl hq))
          · rcases List.mem_cons.mp hq with rfl | hq
            · exact hscale (ψ i) (t (ψ i)) (ht _)
            · exact hscaleA i q (List.mem_append.mpr (Or.inr hq))
        let FA (i : ℕ) (s : C0Ball) := r.value s*tailProduct (tsA i) s
        let FB (i : ℕ) (s : C0Ball) := r.value s*tailProduct (tsB i) s
        have hmemA (i : ℕ) : FA i ∈ VClass B h := ⟨γ,r,tsA i,hr,hj,hlenA i,hscaleA i,rfl⟩
        have hmemB (i : ℕ) : FB i ∈ VClass B h := ⟨γ,r,tsB i,hr,hj,hlenB i,hscaleB i,rfl⟩
        have hsplit (i : ℕ) : (fun s => r.value s*tailProduct (ts0 i) s)=fun s => FA i s+FB i s := by
          funext s
          simp only [ts0,he,tailProduct_append,tailProduct_cons,FA,FB,tsA,tsB]
          rw [TailOperation.factor_split _ (hg i)]
          ring
        have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (FA i) (m (ψ i))+
            completedPairing (sourceClasses B) c0Origin (FB i) (m (ψ i))| := by
          rw [← completedPairing_add _ _ _ _ (VClass_bounded (hmemA i)) (VClass_bounded (hmemB i))]
          rw [← hsplit]
          exact hd (ψ i)
        rcases detection_split _ _ hdet with ⟨η,hη,hdA⟩ | ⟨η,hη,hdB⟩
        · exact ih pre (fun i => rest (ψ (η i))) (fun i => hrest _) (fun i => hlenA _)
            (fun i => hscaleA _) (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective)
            (δ/2) (half_pos hδ) hdA
        · apply tail_remainder_false (fun _ => r.value) (tsB ∘ η) (fun i => (t (ψ (η i))).remainder)
            (fun i => List.mem_append.mpr (Or.inr List.mem_cons_self)) (fun _ => rfl) a
            (fun i => ha _) (hN.comp hη.tendsto_atTop) h (fun i => hmemB _)
            (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective) (half_pos hδ) hdB

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem fixed_cylinder_tails_false {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => r.value s*tailProduct (ts i) s) (m i)|) : False := by
  obtain ⟨n,φ,hφ,hn⟩ := finite_constant_subsequence
    (fun i => (⟨(ts i).length,Nat.lt_succ_of_le (ht i)⟩ : Fin (h+1)))
  apply fixed_cylinder_tails_false_aux r h hr hj n.val [] (ts ∘ φ)
    (fun i => congrArg Fin.val (hn i)) (fun i => ht _) (fun i => ha _)
    (m ∘ φ) M (hm.subsequence hφ.injective) δ hδ (fun i => hd (φ i))

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem repeated_label_false_aux (h : ℕ) (hj : B.band γ ≤ h) (n : ℕ) :
    ∀ (pre : List (CylinderOperation (B.coordinates γ)))
      (post : ℕ → List (CylinderOperation (B.coordinates γ)))
      (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation),
    (∀ i, (post i).length=n) → (∀ i, (r i).operations=pre++post i) →
    (∀ i, (r i).operations.length ≤ h) →
    (∀ i, (ts i).length ≤ h) → (∀ i t, t ∈ ts i → t.scaleIndex ≤ h) →
    ∀ (m : ℕ → SourceSpace B) (M : ℝ), SignedBound m M →
    ∀ δ : ℝ, 0<δ →
    (∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) → False := by
  induction n with
  | zero =>
    intro pre post r ts hn he hr ht ha m M hm δ hδ hd
    have hz (i : ℕ) : post i=[] := List.length_eq_zero_iff.mp (hn i)
    have hval (i : ℕ) : (r i).value=(r 0).value := by
      simp only [GeneratedRepresentation.value,GeneratedRepresentation.cubeValue,he,hz,List.append_nil]
    apply fixed_cylinder_tails_false (r 0) ts h (hr 0) hj ht ha m M hm hδ
    intro i
    simpa only [hval i] using hd i
  | succ n ih =>
    intro pre post r ts hn he hr ht ha m M hm δ hδ hd
    have hc (i : ℕ) : ∃ t rest, post i=t::rest ∧ rest.length=n := by
      obtain ⟨t,rest,heq⟩ := List.length_pos_iff_exists_cons.mp (show 0<(post i).length by rw [hn]; omega)
      refine ⟨t,rest,heq,?_⟩
      have hh := hn i
      rw [heq,List.length_cons] at hh
      omega
    choose op suf hop hsuf using hc
    have hops (i : ℕ) : (r i).operations=pre++op i::suf i := (he i).trans (congrArg (pre++·) (hop i))
    have hsuflen (i : ℕ) : (suf i).length ≤ h := by
      have hh := hr i
      rw [hops,List.length_append,List.length_cons] at hh
      omega
    have horder (i : ℕ) (t : CylinderOperation (B.coordinates γ)) (ht : t ∈ suf i) : t.scale ≤ (op i).scale := by
      have hh := (r i).ordered
      rw [hops] at hh
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hh).2.1).1 t ht
    rcases CylinderOperation.constant_or_small op with ⟨p,ψ,hψ,hp⟩ | ⟨ψ,hψ,hsmall,g,hg⟩
    · have heq (i : ℕ) : (r (ψ i)).operations=(pre++[p])++suf (ψ i) := by
        rw [hops,hp,List.append_assoc,List.singleton_append]
      exact ih (pre++[p]) (suf ∘ ψ) (r ∘ ψ) (ts ∘ ψ) (fun i => hsuf _) heq
        (fun i => hr _) (fun i => ht _) (fun i => ha _) (m ∘ ψ) M (hm.subsequence hψ.injective) δ hδ (fun i => hd (ψ i))
    · let p : Cube (B.coordinates γ) → ℝ := applyOperations pre (B.base γ)
      have hp : LipschitzWith (4^pre.length*B.L0) p := applyOperations_lipschitz pre (B.base_lipschitz γ)
      cases g with
      | false =>
        apply small_remainders_false (r ∘ ψ) (ts ∘ ψ) h (fun i => hr _) hj (fun i => ht _) (fun i => ha _)
          (op ∘ ψ) hsmall p (4^pre.length*B.L0) hp (suf ∘ ψ) (fun i => hsuflen _) (fun i => horder _) _
          (m ∘ ψ) M (hm.subsequence hψ.injective) hδ (fun i => hd (ψ i))
        intro i
        simp only [Function.comp_def,GeneratedRepresentation.cubeValue,hops,applyOperations_append,applyOperations_cons,p]
        have he' : (op (ψ i)).act p=(op (ψ i)).remainder.act p := by
          simp only [CylinderOperation.act,localOp,hg i,Bool.false_eq_true,↓reduceIte]
          rfl
        exact congrArg (applyOperations (suf (ψ i))) he'
      | true =>
        have hsub (i : ℕ) : (pre++suf (ψ i)).Sublist (r (ψ i)).operations := by
          rw [hops]
          exact (List.sublist_cons_self _ _).append_left pre
        let rA (i : ℕ) := (r (ψ i)).subrepresentation (pre++suf (ψ i)) (hsub i)
        have hsame (i : ℕ) : (pre++(op (ψ i)).remainder::suf (ψ i)).map CylinderOperation.scale =
            (r (ψ i)).operations.map CylinderOperation.scale := by
          simp only [hops,List.map_append,List.map_cons,CylinderOperation.remainder_scale]
        let rB (i : ℕ) := (r (ψ i)).sameScales (pre++(op (ψ i)).remainder::suf (ψ i)) (hsame i)
        have hlenA (i : ℕ) : (rA i).operations.length ≤ h := (hsub i).length_le.trans (hr _)
        have hlenB (i : ℕ) : (rB i).operations.length ≤ h := by
          simpa only [rB,GeneratedRepresentation.sameScales,hops,List.length_append,List.length_cons] using hr (ψ i)
        have hcubeB (i : ℕ) : (rB i).cubeValue=applyOperations (suf (ψ i)) ((op (ψ i)).remainder.act p) := by
          simp only [rB,GeneratedRepresentation.sameScales,GeneratedRepresentation.cubeValue,
            applyOperations_append,applyOperations_cons,p]
        let FA (i : ℕ) (s : C0Ball) := (rA i).value s*tailProduct (ts (ψ i)) s
        let FB (i : ℕ) (s : C0Ball) := (rB i).value s*tailProduct (ts (ψ i)) s
        have hmemA (i : ℕ) : FA i ∈ VClass B h := ⟨γ,rA i,ts (ψ i),hlenA i,hj,ht _,ha _,rfl⟩
        have hmemB (i : ℕ) : FB i ∈ VClass B h := ⟨γ,rB i,ts (ψ i),hlenB i,hj,ht _,ha _,rfl⟩
        have hcube (i : ℕ) : (r (ψ i)).cubeValue=(rA i).cubeValue+(rB i).cubeValue := by
          rw [hcubeB]
          change applyOperations (r (ψ i)).operations (B.base γ)=applyOperations (pre++suf (ψ i)) (B.base γ)+_
          rw [hops,applyOperations_append,applyOperations_cons,applyOperations_append]
          rw [CylinderOperation.act_split _ (hg i),map_add]
        have hsplit (i : ℕ) : (fun s => (r (ψ i)).value s*tailProduct (ts (ψ i)) s)=fun s => FA i s+FB i s := by
          funext s
          simp only [GeneratedRepresentation.value,Function.comp_def,hcube,Pi.add_apply,FA,FB]
          ring
        have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (FA i) (m (ψ i))+
            completedPairing (sourceClasses B) c0Origin (FB i) (m (ψ i))| := by
          rw [← completedPairing_add _ _ _ _ (VClass_bounded (hmemA i)) (VClass_bounded (hmemB i)),← hsplit]
          exact hd (ψ i)
        rcases detection_split _ _ hdet with ⟨η,hη,hdA⟩ | ⟨η,hη,hdB⟩
        · exact ih pre (suf ∘ ψ ∘ η) (rA ∘ η) (ts ∘ ψ ∘ η) (fun i => hsuf _)
            (fun i => rfl) (fun i => hlenA _) (fun i => ht _) (fun i => ha _)
            (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective) (δ/2) (half_pos hδ) hdA
        · exact small_remainders_false (rB ∘ η) (ts ∘ ψ ∘ η) h (fun i => hlenB _) hj
            (fun i => ht _) (fun i => ha _) (op ∘ ψ ∘ η) (hsmall.comp hη.tendsto_atTop) p
            (4^pre.length*B.L0) hp (suf ∘ ψ ∘ η) (fun i => hsuflen _) (fun i => horder _)
            (fun i => hcubeB _) (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective)
            (half_pos hδ) hdB

theorem repeated_label_false (r : ℕ → GeneratedRepresentation B γ)
    (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  obtain ⟨n,φ,hφ,hn⟩ := finite_constant_subsequence
    (fun i => (⟨(r i).operations.length,Nat.lt_succ_of_le (hr i)⟩ : Fin (h+1)))
  exact repeated_label_false_aux h hj n.val [] (fun i => (r (φ i)).operations) (r ∘ φ) (ts ∘ φ)
    (fun i => congrArg Fin.val (hn i)) (fun i => rfl) (fun i => hr _) (fun i => ht _) (fun i => ha _)
    (m ∘ φ) M (hm.subsequence hφ.injective) δ hδ (fun i => hd (φ i))

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

namespace GeneratedRepresentation

def relabel {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') : GeneratedRepresentation B γ' := he ▸ r

@[simp] theorem relabel_length {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') :
    (r.relabel he).operations.length=r.operations.length := by subst γ'; rfl

@[simp] theorem relabel_value {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') :
    (r.relabel he).value=r.value := by subst γ'; rfl
end GeneratedRepresentation

theorem bounded_band_detectors_false (loc : RadiusLocalization B)
    (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : ∀ i, B.band (γ i) ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  rcases constant_or_injective_subsequence γ with ⟨γ0,ψ,hψ,hγ⟩ | ⟨ψ,hψ,hγ⟩
  · let rr (i : ℕ) := (r (ψ i)).relabel (hγ i)
    apply repeated_label_false rr (ts ∘ ψ) h (fun i => by simpa only [rr,GeneratedRepresentation.relabel_length] using hr (ψ i))
      (by rw [← hγ 0]; exact hj _) (fun i => ht _) (fun i => ha _) (m ∘ ψ) M
      (hm.subsequence hψ.injective) hδ
    intro i
    simpa only [rr,GeneratedRepresentation.relabel_value,Function.comp_def] using hd (ψ i)
  · obtain ⟨j,η,hη,hjη⟩ := finite_constant_subsequence
      (fun i => (⟨B.band (γ (ψ i)),Nat.lt_succ_of_le (hj _)⟩ : Fin (h+1)))
    obtain ⟨H,φ,hφ,F,hF,hdF,hdis⟩ := loc.low_bands_disjoint (γ ∘ ψ ∘ η) (fun i => r (ψ (η i)))
      (ts ∘ ψ ∘ η) h j.val (fun i => hr _) (fun i => congrArg Fin.val (hjη i))
      (Nat.le_of_lt_succ j.isLt) (fun i => ht _) (fun i => ha _) (hγ.comp hη.injective)
      (m ∘ ψ ∘ η) hδ (fun i => hd (ψ (η i)))
    exact VClass_disjoint_false (m ∘ ψ ∘ η ∘ φ) M (hm.subsequence ((hψ.comp hη).comp hφ).injective)
      F H hF hdis (half_pos hδ) hdF

theorem source_detectors_false (locT : TagLocalization B) (locR : RadiusLocalization B)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (d : ℕ) (hF : ∀ i, F i ∈ sourceClasses B d)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  let h := d/2+1
  by_cases hdEven : d%2=0
  · have ht (i : ℕ) : F i ∈ TClass B h := by simpa only [sourceClasses,hdEven,↓reduceIte,h] using hF i
    choose γ r hr he using ht
    have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (r i).value (m i)| := by
      simpa only [he i] using hd i
    rcases nat_constant_or_tendsto (fun i => B.band (γ i)) with ⟨j,ψ,hψ,hj⟩ | hj
    · apply bounded_band_detectors_false locR (γ ∘ ψ) (fun i => r (ψ i)) (fun _ => []) (h+j)
        (fun i => (hr _).trans (Nat.le_add_right h j)) (fun i => by change B.band (γ (ψ i)) ≤ h+j; rw [hj]; omega)
        (by simp) (by simp) (m ∘ ψ) M (hm.subsequence hψ.injective) hδ
      intro i
      simpa only [tailProduct_nil,mul_one,Function.comp_def] using hdet (ψ i)
    · obtain ⟨φ,hφ,G,hG,hdG,hLip⟩ := high_bands_compatible locT γ r h hr hj m hδ hdet
      apply compatible_detectors_false (sourceClasses B) c0Origin (m ∘ φ) M (hm.subsequence hφ.injective)
        G (2*h) (4^(h+1)*B.L0+1) _ hLip (half_pos hδ) hdG
      intro i
      simpa only [sourceClasses_even] using hG i
  · have ht (i : ℕ) : F i ∈ VClass B h := by simpa only [sourceClasses,hdEven,↓reduceIte,h] using hF i
    choose γ r ts hr hj hts ha he using ht
    apply bounded_band_detectors_false locR γ r ts h hr hj hts ha m M hm hδ
    intro i
    simpa only [he i] using hd i

theorem source_no_bounded_signs_lower (locT : TagLocalization B) (locR : RadiusLocalization B)
    (m : ℕ → SourceSpace B) (M r : ℝ) (hm : SignedBound m M) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖) : False := by
  obtain ⟨h,δ,hδ,φ,hφ,F,hF⟩ := one_class_detects (sourceClasses B) c0Origin m M r hr hlower hm.initial
  exact source_detectors_false locT locR (m ∘ φ) M (hm.subsequence hφ.injective) F h
    (fun i => (hF i).1) hδ (fun i => (hF i).2)

theorem atoms_signed_bound : SignedBound atom 1 := by
  classical
  intro n ι hι ε
  apply c0_norm_le _ zero_le_one
  intro k
  change |c0Eval k (∑ i, realSign (ε i) • atom (ι i))| ≤ 1
  simp only [map_sum,map_smul,smul_eq_mul,c0Eval_apply,atom_apply]
  by_cases hex : ∃ i, ι i=k
  · obtain ⟨i,hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · simpa only [hi,ite_true,mul_one] using (abs_realSign (ε i)).le
    · intro j hj hji
      have hneq : ι j≠k := by intro he; exact hji (hι (he.trans hi.symm))
      simp only [hneq,ite_false,mul_zero]
    · simp
  · push Not at hex
    simp only [hex,ite_false,mul_zero,Finset.sum_const_zero,abs_zero,zero_le_one]

theorem source_noLinearC0 (locT : TagLocalization B) (locR : RadiusLocalization B) :
    NoLinearC0 (SourceSpace B) := by
  intro T hT
  obtain ⟨c,hc,hcT⟩ := hT
  let m (i : ℕ) := T (atom i)
  have hm : SignedBound m ‖T‖ := by
    intro n ι hι ε
    change ‖∑ i, realSign (ε i) • T (atom (ι i))‖ ≤ ‖T‖
    rw [show (∑ i, realSign (ε i) • T (atom (ι i))) = T (∑ i, realSign (ε i) • atom (ι i)) by simp only [map_sum,map_smul]]
    calc
      _ ≤ ‖T‖ * ‖∑ i, realSign (ε i) • atom (ι i)‖ := T.le_opNorm _
      _ ≤ ‖T‖*1 := mul_le_mul_of_nonneg_left (atoms_signed_bound n ι hι ε) (ContinuousLinearMap.opNorm_nonneg T)
      _ = ‖T‖ := mul_one _
  exact source_no_bounded_signs_lower locT locR m ‖T‖ c hm hc
    (fun i => by simpa only [atom_norm,mul_one] using hcT (atom i))

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

abbrev BandGrid (j : ℕ) := Fin j → GridIndex (2^j)
abbrev PrefixCube (j : ℕ) := Fin j → Icc (-1 : ℝ) 1

def bandPoint (j : ℕ) (ξ : BandGrid j) : PrefixCube j :=
  fun k => gridPoint (2^j) (by positivity) (ξ k)

def prefixRestrict (j : ℕ) (s : C0Ball) : PrefixCube j := fun k =>
  ⟨s.val k, abs_le.mp ((c0_norm_apply_le s.val k).trans (by
    have hh := s.property
    simpa only [Metric.mem_closedBall,dist_zero_right] using hh))⟩

theorem prefixRestrict_lipschitz (j : ℕ) : LipschitzWith 1 (prefixRestrict j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro k
  exact BoundedContinuousFunction.dist_coe_le_dist (f := x.val.toBCF) (g := y.val.toBCF) k

def bandBump (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  max 0 (1-dist s (bandPoint j ξ)/dyadic j)

def bandVector (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  min 1 (max 0 (2-dist s (bandPoint j ξ)/dyadic j))

def bandDenominator (j : ℕ) (s : PrefixCube j) : ℝ := ∑ ξ : BandGrid j, bandBump j ξ s

def bandRow (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  bandBump j ξ s / bandDenominator j s

theorem bandBump_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandBump j ξ s := le_max_left _ _

theorem bandVector_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandVector j ξ s := le_min zero_le_one (le_max_left _ _)

theorem bandVector_le_one (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    bandVector j ξ s ≤ 1 := min_le_left _ _

theorem bandVector_eq_one {j : ℕ} {ξ : BandGrid j} {s : PrefixCube j}
    (h : bandBump j ξ s ≠ 0) : bandVector j ξ s=1 := by
  have hh : 0 < 1-dist s (bandPoint j ξ)/dyadic j := by
    by_contra hn
    exact h (max_eq_left (by linarith))
  unfold bandVector
  rw [min_eq_left]
  exact le_max_of_le_right (by linarith)

theorem bandVector_support {j : ℕ} {ξ : BandGrid j} {s : PrefixCube j}
    (h : bandVector j ξ s ≠ 0) : dist s (bandPoint j ξ) < 2*dyadic j := by
  have hmax : max 0 (2-dist s (bandPoint j ξ)/dyadic j) ≠ 0 := by
    intro hh
    exact h (by simp only [bandVector,hh,min_eq_right zero_le_one])
  have hh : 0 < 2-dist s (bandPoint j ξ)/dyadic j := by
    by_contra hn
    exact hmax (max_eq_left (by linarith))
  exact (div_lt_iff₀ (dyadic_pos j)).mp (by linarith)

theorem const_dist_div_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) (a : ℝ) (j : ℕ) :
    LipschitzWith (2^j) (fun s => a-dist s q/dyadic j) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,sub_sub_sub_cancel_left,← sub_div,abs_div,abs_of_pos (dyadic_pos j)]
  calc
    _ ≤ dist t s/dyadic j := div_le_div_of_nonneg_right (abs_dist_sub_le t s q) (dyadic_pos j).le
    _ = (2^j : ℝ≥0)*dist s t := by simp only [dyadic,div_inv_eq_mul,NNReal.coe_pow,NNReal.coe_ofNat,dist_comm]; ring

theorem bandBump_lipschitz (j : ℕ) (ξ : BandGrid j) :
    LipschitzWith (2^j) (bandBump j ξ) :=
  (const_dist_div_lipschitz (bandPoint j ξ) 1 j).const_max 0

theorem bandVector_lipschitz (j : ℕ) (ξ : BandGrid j) :
    LipschitzWith (2^j) (bandVector j ξ) :=
  ((const_dist_div_lipschitz (bandPoint j ξ) 2 j).const_max 0).const_min 1

theorem bandDenominator_ge (j : ℕ) (s : PrefixCube j) : 1/2 ≤ bandDenominator j s := by
  classical
  let ξ : BandGrid j := fun k => nearestGridIndex (2^j) (by positivity) (s k)
  have hd : dist s (bandPoint j ξ) ≤ dyadic j/2 := by
    apply (dist_pi_le_iff (div_nonneg (dyadic_pos j).le (by norm_num) : 0 ≤ dyadic j/2)).mpr
    intro k
    have hh := nearestGrid_dist (2^j) (by positivity) (s k)
    change dist (s k) (gridPoint _ _ (nearestGridIndex _ _ (s k))) ≤ _
    refine hh.trans_eq ?_
    push_cast
    unfold dyadic
    ring
  have hb : 1/2 ≤ bandBump j ξ s := by
    apply le_max_of_le_right
    have hh : dist s (bandPoint j ξ)/dyadic j ≤ 1/2 := (div_le_iff₀ (dyadic_pos j)).mpr (by linarith)
    linarith
  exact hb.trans (Finset.single_le_sum (fun a _ => bandBump_nonneg j a s) (Finset.mem_univ ξ))

theorem bandDenominator_pos (j : ℕ) (s : PrefixCube j) : 0 < bandDenominator j s :=
  lt_of_lt_of_le (by norm_num) (bandDenominator_ge j s)

theorem bandRow_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandRow j ξ s := div_nonneg (bandBump_nonneg j ξ s) (bandDenominator_pos j s).le

theorem bandRow_sum (j : ℕ) (s : PrefixCube j) : ∑ ξ : BandGrid j, bandRow j ξ s=1 := by
  simp only [bandRow,← Finset.sum_div]
  change bandDenominator j s/bandDenominator j s=1
  exact div_self (bandDenominator_pos j s).ne'

theorem bandRow_vector (j : ℕ) (s : PrefixCube j) :
    ∑ ξ : BandGrid j, bandRow j ξ s*bandVector j ξ s=1 := by
  rw [← bandRow_sum j s]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases h : bandBump j ξ s=0
  · simp only [bandRow,h,zero_div,zero_mul]
  · rw [bandVector_eq_one h,mul_one]

theorem normalized_sum_distance {A : Type*} [Fintype A] (b c : A → ℝ)
    (_hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hB : 1/2 ≤ ∑ i,b i) (hC : 1/2 ≤ ∑ i,c i) :
    (∑ i, |b i/(∑ i,b i)-c i/(∑ i,c i)|) ≤ 4*∑ i,|b i-c i| := by
  let B := ∑ i,b i
  let C := ∑ i,c i
  have hB' : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hC' : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hdist : |C-B| ≤ ∑ i,|b i-c i| := by
    rw [abs_sub_comm]
    change |(∑ i,b i)-(∑ i,c i)| ≤ _
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hrow : ∑ i,c i/C=1 := by rw [← Finset.sum_div]; exact div_self hC'.ne'
  have he (i : A) : b i/B-c i/C=(b i-c i)/B+(c i/C)*((C-B)/B) := by
    field_simp
    ; ring
  calc
    _ ≤ ∑ i, (|b i-c i|/B+(c i/C)*(|C-B|/B)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [he]
      refine (abs_add_le _ _).trans_eq ?_
      simp only [abs_mul,abs_div,abs_of_pos hB',abs_of_nonneg (hc i),abs_of_pos hC']
    _ = (∑ i,|b i-c i|)/B+|C-B|/B := by
      rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul,hrow,one_mul]
    _ ≤ (∑ i,|b i-c i|)/B+(∑ i,|b i-c i|)/B :=
      add_le_add_right ((div_le_div_iff_of_pos_right hB').mpr hdist) _
    _ ≤ 4*∑ i,|b i-c i| := by
      have hh : (∑ i,|b i-c i|)/B ≤ 2*∑ i,|b i-c i| := by
        apply (div_le_iff₀ hB').mpr
        have ha : 0 ≤ ∑ i,|b i-c i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
        nlinarith
      linarith

def bandL (j : ℕ) : ℝ≥0 := 4*Fintype.card (BandGrid j)*2^j

theorem bandRow_distance (j : ℕ) (s t : PrefixCube j) :
    (∑ ξ : BandGrid j,|bandRow j ξ s-bandRow j ξ t|) ≤ bandL j*dist s t := by
  refine (normalized_sum_distance (fun ξ => bandBump j ξ s) (fun ξ => bandBump j ξ t)
    (fun ξ => bandBump_nonneg j ξ s) (fun ξ => bandBump_nonneg j ξ t)
    (bandDenominator_ge j s) (bandDenominator_ge j t)).trans ?_
  calc
    _ ≤ 4*∑ ξ : BandGrid j, (2 : ℝ)^j*dist s t := by
      gcongr with ξ
      simpa only [Real.dist_eq,NNReal.coe_pow,NNReal.coe_ofNat] using
        (bandBump_lipschitz j ξ).dist_le_mul s t
    _ = bandL j*dist s t := by simp [bandL]; ring

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def eta : ℝ := 1/1000
def scheduleH : ℝ := 10000

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem scheduleH_pos : 0 < scheduleH := by norm_num [scheduleH]
theorem schedule_speed : Real.pi/scheduleH ≤ eta/2 := by
  have h := Real.pi_lt_four
  norm_num [scheduleH,eta]
  linarith

theorem bandL_pos (j : ℕ) : 0 < (bandL j : ℝ) := by
  let : Nonempty (BandGrid j) := ⟨fun _ => ⟨0,by constructor; exact neg_nonpos.mpr (Int.natCast_nonneg _); exact Int.natCast_nonneg _⟩⟩
  have hc : (0 : ℝ) < Fintype.card (BandGrid j) := by exact_mod_cast Fintype.card_pos
  simp only [bandL,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,NNReal.coe_pow]
  positivity

def rho : ℕ → ℝ
  | 0 => 1/2
  | j+1 => min (Real.exp (-scheduleH)*rho j/2) (eta/(8*bandL (j+1)))

theorem rho_pos (j : ℕ) : 0 < rho j := by
  induction j with
  | zero => norm_num [rho]
  | succ j ih =>
    change 0 < min _ _
    exact lt_min (by positivity) (div_pos eta_pos (mul_pos (by norm_num) (bandL_pos _)))

theorem rho_step (j : ℕ) : rho (j+1) < Real.exp (-scheduleH)*rho j := by
  have hp : 0 < Real.exp (-scheduleH)*rho j := mul_pos (Real.exp_pos _) (rho_pos j)
  exact (min_le_left _ _).trans_lt (by linarith)

theorem rho_half_step (j : ℕ) : rho (j+1) ≤ rho j/2 := by
  have he : Real.exp (-scheduleH) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num [scheduleH])
  exact (min_le_left _ _).trans (div_le_div_of_nonneg_right
    (by nlinarith [rho_pos j]) (by norm_num))

theorem rho_bound (j : ℕ) : rho j ≤ (1/2 : ℝ)^(j+1) := by
  induction j with
  | zero => norm_num [rho]
  | succ j ih =>
    refine (rho_half_step j).trans ?_
    rw [pow_succ]
    linarith

theorem rho_lt_one (j : ℕ) : rho j < 1 := by
  have hh := rho_bound j
  have hp : (1/2 : ℝ)^(j+1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  exact hh.trans_lt hp

theorem rho_lip_budget {j : ℕ} (hj : 0 < j) : bandL j*rho j ≤ eta/4 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hh : rho (k+1) ≤ eta/(8*bandL (k+1)) := min_le_right _ _
  have hp := bandL_pos (k+1)
  have he := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) hp)).mp hh
  linarith [eta_pos]

theorem rho_tendsto : Tendsto rho atTop (nhds 0) := by
  apply squeeze_zero (fun j => (rho_pos j).le) rho_bound
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp
    (tendsto_add_atTop_nat 1)

def ell (j : ℕ) : ℝ := Real.exp (-scheduleH)*rho (j+1)

theorem ell_pos (j : ℕ) : 0 < ell j := mul_pos (Real.exp_pos _) (rho_pos _)
theorem ell_tendsto : Tendsto ell atTop (nhds 0) := by
  change Tendsto (fun j => Real.exp (-scheduleH)*rho (j+1)) atTop (nhds 0)
  convert (tendsto_const_nhds (x := Real.exp (-scheduleH))).mul (rho_tendsto.comp (tendsto_add_atTop_nat 1)) using 1 <;> simp

theorem log_rho_step (j : ℕ) : Real.log (rho (j+1)) < Real.log (rho j)-scheduleH := by
  have hh := Real.strictMonoOn_log (rho_pos (j+1))
    (mul_pos (Real.exp_pos _) (rho_pos j)) (rho_step j)
  rwa [Real.log_mul (Real.exp_pos _).ne' (rho_pos j).ne',Real.log_exp,neg_add_eq_sub] at hh

def transitionAngle (j : ℕ) (u : ℝ) : ℝ :=
  Real.pi/(2*scheduleH) * min scheduleH (max 0 (Real.log (rho j)-u))

theorem transitionAngle_nonneg (j : ℕ) (u : ℝ) : 0 ≤ transitionAngle j u := by
  unfold transitionAngle
  exact mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num [scheduleH] : 0 ≤ 2*scheduleH))
    (le_min scheduleH_pos.le (le_max_left _ _))

theorem transitionAngle_le (j : ℕ) (u : ℝ) : transitionAngle j u ≤ Real.pi/2 := by
  have hh : min scheduleH (max 0 (Real.log (rho j)-u)) ≤ scheduleH := min_le_left _ _
  have hc : 0 ≤ Real.pi/(2*scheduleH) := div_nonneg Real.pi_pos.le (by norm_num [scheduleH])
  have hb := mul_le_mul_of_nonneg_left hh hc
  have he : Real.pi/(2*scheduleH)*scheduleH=Real.pi/2 := by norm_num [scheduleH]; ring
  exact hb.trans_eq he

theorem transitionAngle_zero (j : ℕ) {u : ℝ} (hu : Real.log (rho j) ≤ u) :
    transitionAngle j u=0 := by
  simp only [transitionAngle,max_eq_left (by linarith : Real.log (rho j)-u ≤ 0),
    min_eq_right scheduleH_pos.le,mul_zero]

theorem transitionAngle_full (j : ℕ) {u : ℝ} (hu : u ≤ Real.log (rho j)-scheduleH) :
    transitionAngle j u=Real.pi/2 := by
  unfold transitionAngle
  rw [min_eq_left (le_max_of_le_right (by linarith : scheduleH ≤ Real.log (rho j)-u))]
  norm_num [scheduleH]
  ring

theorem transitionAngle_dichotomy (j : ℕ) (u : ℝ) :
    transitionAngle (j+1) u=0 ∨ transitionAngle j u=Real.pi/2 := by
  by_cases hu : Real.log (rho (j+1)) ≤ u
  · exact Or.inl (transitionAngle_zero (j+1) hu)
  · exact Or.inr (transitionAngle_full j (by linarith [log_rho_step j]))

def transitionInterval (j : ℕ) : Set ℝ := Icc (Real.log (rho j)-scheduleH) (Real.log (rho j))

theorem log_rho_antitone : Antitone (fun j => Real.log (rho j)) := by
  apply antitone_nat_of_succ_le
  intro j
  linarith [log_rho_step j,scheduleH_pos]

theorem transitionInterval_disjoint : Pairwise (fun i j => Disjoint (transitionInterval i) (transitionInterval j)) := by
  suffices ∀ i j, i<j → Disjoint (transitionInterval i) (transitionInterval j) by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hh|hh
    · exact this i j hh
    · exact (this j i hh).symm
  intro i j hij
  have hh := (log_rho_antitone (Nat.succ_le_of_lt hij)).trans_lt (log_rho_step i)
  apply Set.disjoint_left.mpr
  intro u hi hj
  exact (not_le_of_gt hh) (hi.1.trans hj.2)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem finite_variation_sum_lipschitz {A : Type*} [Fintype A]
    (f : A → ℝ → ℝ) (C : A → Set ℝ) {K : ℝ≥0}
    (hdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hf : ∀ i, LipschitzWith K (f i))
    (hconst : ∀ i x, x ∉ C i → ∀ᶠ y in nhds x, f i y=f i x) :
    LipschitzWith K (fun x => ∑ i,f i x) := by
  classical
  have hloc (x : ℝ) : ∀ᶠ y in nhds x,
      dist (∑ i,f i x) (∑ i,f i y) ≤ K*dist x y := by
    by_cases h : ∃ i, x ∈ C i
    · obtain ⟨j,hj⟩ := h
      have hh (i : A) : i ≠ j → ∀ᶠ y in nhds x, f i y=f i x := by
        intro hij
        exact hconst i x (fun hi => Set.disjoint_left.mp (hdis hij) hi hj)
      have he : ∀ᶠ y in nhds x, ∀ i, i≠j → f i y=f i x :=
        Filter.eventually_all.mpr (fun i => by
          by_cases hij : i=j
          · exact Filter.Eventually.of_forall (by simp [hij])
          · filter_upwards [hh i hij] with y hy using fun _ => hy)
      filter_upwards [he] with y hy
      rw [Real.dist_eq,← Finset.sum_sub_distrib,
        Finset.sum_eq_single j (fun i _ hij => by rw [hy i hij,sub_self]) (by simp)]
      exact (hf j).dist_le_mul x y
    · push Not at h
      filter_upwards [Filter.eventually_all.mpr (fun i => hconst i x (h i))] with y hy
      simp only [hy,dist_self]
      positivity
  have hc : Continuous (fun x => ∑ i,f i x) := continuous_finsetSum _ (fun i _ => (hf i).continuous)
  have hl := lipschitzOn_convex_of_local (convex_univ : Convex ℝ (univ : Set ℝ)) hc.continuousOn
    (fun x _ => by simpa only [nhdsWithin_univ] using hloc x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact hl.dist_le_mul x (mem_univ _) y (mem_univ _)

def angleSpeed : ℝ≥0 := ⟨Real.pi/(2*scheduleH),div_nonneg Real.pi_pos.le (by norm_num [scheduleH])⟩

theorem transitionAngle_lipschitz (j : ℕ) : LipschitzWith angleSpeed (transitionAngle j) := by
  have hl : LipschitzWith 1 (fun u : ℝ => Real.log (rho j)-u) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [Real.dist_eq,sub_sub_sub_cancel_left,NNReal.coe_one,one_mul,abs_sub_comm,le_refl]
  have hb := (hl.const_max 0).const_min scheduleH
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change |angleSpeed*(min scheduleH (max 0 (Real.log (rho j)-u)))-
      angleSpeed*(min scheduleH (max 0 (Real.log (rho j)-v)))| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg angleSpeed.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using hb.dist_le_mul u v) angleSpeed.coe_nonneg

theorem transitionAngle_antitone (j : ℕ) : Antitone (transitionAngle j) := by
  intro u v huv
  apply mul_le_mul_of_nonneg_left _ angleSpeed.coe_nonneg
  exact min_le_min_left _ (max_le_max_left _ (by linarith))

theorem transitionAngle_locally_constant (j : ℕ) (u : ℝ) (hu : u ∉ transitionInterval j) :
    ∀ᶠ v in nhds u, transitionAngle j v=transitionAngle j u := by
  have h : u < Real.log (rho j)-scheduleH ∨ Real.log (rho j)<u := by
    change ¬(Real.log (rho j)-scheduleH ≤ u ∧ u ≤ Real.log (rho j)) at hu
    rcases lt_or_ge u (Real.log (rho j)-scheduleH) with h|h
    · exact Or.inl h
    · right
      by_contra hn
      exact hu ⟨h,le_of_not_gt hn⟩
  rcases h with h|h
  · filter_upwards [eventually_lt_nhds h] with v hv
    rw [transitionAngle_full j hv.le,transitionAngle_full j h.le]
  · filter_upwards [eventually_gt_nhds h] with v hv
    rw [transitionAngle_zero j hv.le,transitionAngle_zero j h.le]

theorem angle_sum_distance (J : ℕ) (u v : ℝ) :
    (∑ j : Fin J, |transitionAngle (j+1) u-transitionAngle (j+1) v|) ≤
      angleSpeed*dist u v := by
  have hh := finite_variation_sum_lipschitz
    (fun j : Fin J => transitionAngle (j+1)) (fun j : Fin J => transitionInterval (j+1))
    (fun i j hij => transitionInterval_disjoint (by intro he; exact hij (Fin.ext (by omega))))
    (fun j => transitionAngle_lipschitz (j+1))
    (fun j => transitionAngle_locally_constant (j+1))
  have he (x y : ℝ) (hxy : x≤y) :
      (∑ j : Fin J, |transitionAngle (j+1) x-transitionAngle (j+1) y|) =
        dist (∑ j : Fin J,transitionAngle (j+1) x) (∑ j : Fin J,transitionAngle (j+1) y) := by
    rw [Real.dist_eq,← Finset.sum_sub_distrib,abs_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j _
      exact abs_of_nonneg (sub_nonneg.mpr (transitionAngle_antitone (j+1) hxy))
    · exact Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (transitionAngle_antitone (j+1) hxy))
  rcases le_total u v with huv|hvu
  · rw [he u v huv]
    exact hh.dist_le_mul u v
  · have heq : (∑ j : Fin J, |transitionAngle (j+1) u-transitionAngle (j+1) v|)=
        ∑ j : Fin J, |transitionAngle (j+1) v-transitionAngle (j+1) u| :=
        Finset.sum_congr rfl (fun j _ => abs_sub_comm _ _)
    rw [heq,he v u hvu]
    simpa only [dist_comm] using hh.dist_le_mul v u

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def boundedAngle (J : ℕ) (u : ℝ) (j : ℕ) : ℝ :=
  if j=0 then Real.pi/2 else if J<j then 0 else transitionAngle j u

@[simp] theorem boundedAngle_zero (J : ℕ) (u : ℝ) : boundedAngle J u 0=Real.pi/2 := by simp [boundedAngle]
@[simp] theorem boundedAngle_last (J : ℕ) (u : ℝ) : boundedAngle J u (J+1)=0 := by simp [boundedAngle]

theorem boundedAngle_inner {J j : ℕ} (hj : 0<j) (hJ : j≤J) (u : ℝ) :
    boundedAngle J u j=transitionAngle j u := by simp [boundedAngle,hj.ne',not_lt.mpr hJ]

theorem boundedAngle_range (J j : ℕ) (u : ℝ) :
    0 ≤ boundedAngle J u j ∧ boundedAngle J u j ≤ Real.pi/2 := by
  unfold boundedAngle
  split_ifs
  · exact ⟨by positivity,le_rfl⟩
  · exact ⟨le_rfl,by positivity⟩
  · exact ⟨transitionAngle_nonneg j u,transitionAngle_le j u⟩

theorem boundedAngle_dichotomy (J j : ℕ) (u : ℝ) :
    boundedAngle J u (j+1)=0 ∨ boundedAngle J u j=Real.pi/2 := by
  by_cases hj : j=0
  · exact Or.inr (by simp [hj])
  by_cases hJ : J<j+1
  · exact Or.inl (by simp [boundedAngle,hJ])
  · rw [boundedAngle_inner (by omega) (by omega),boundedAngle_inner (by omega) (by omega)]
    exact transitionAngle_dichotomy j u

def thetaLog (J : ℕ) (u : ℝ) (j : ℕ) : ℝ :=
  Real.sin (boundedAngle J u j)+Real.cos (boundedAngle J u (j+1))-1

theorem thetaLog_mul (J j : ℕ) (u : ℝ) : thetaLog J u j=
    Real.sin (boundedAngle J u j)*Real.cos (boundedAngle J u (j+1)) := by
  rcases boundedAngle_dichotomy J j u with h|h <;> simp [thetaLog,h]

theorem thetaLog_nonneg (J j : ℕ) (u : ℝ) : 0 ≤ thetaLog J u j := by
  rw [thetaLog_mul]
  apply mul_nonneg
  · exact Real.sin_nonneg_of_nonneg_of_le_pi (boundedAngle_range J j u).1
      ((boundedAngle_range J j u).2.trans (by linarith [Real.pi_pos]))
  · exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [(boundedAngle_range J (j+1) u).1,Real.pi_pos])
      (boundedAngle_range J (j+1) u).2

theorem thetaLog_le_one (J j : ℕ) (u : ℝ) : thetaLog J u j ≤ 1 := by
  rcases boundedAngle_dichotomy J j u with h|h
  · simpa only [thetaLog,h,Real.cos_zero,add_sub_cancel_right] using Real.sin_le_one (boundedAngle J u j)
  · simpa only [thetaLog,h,Real.sin_pi_div_two,add_sub_cancel_left] using Real.cos_le_one (boundedAngle J u (j+1))

theorem thetaLog_sq (J j : ℕ) (u : ℝ) : thetaLog J u j^2=
    Real.sin (boundedAngle J u j)^2-Real.sin (boundedAngle J u (j+1))^2 := by
  rcases boundedAngle_dichotomy J j u with h|h
  · simp [thetaLog,h]
  · have hs := Real.sin_sq_add_cos_sq (boundedAngle J u (j+1))
    simp only [thetaLog,h,Real.sin_pi_div_two,one_pow]
    nlinarith

theorem sum_range_differences (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (f j-f (j+1))=f 0-f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

theorem thetaLog_squares (J : ℕ) (u : ℝ) : ∑ j : Fin (J+1), thetaLog J u j^2=1 := by
  simp_rw [thetaLog_sq]
  rw [Fin.sum_univ_eq_sum_range (fun j => Real.sin (boundedAngle J u j)^2-Real.sin (boundedAngle J u (j+1))^2),sum_range_differences]
  simp

theorem transitionAngle_unique (u : ℝ) :
    Set.Subsingleton {j | transitionAngle j u ≠ 0 ∧ transitionAngle j u ≠ Real.pi/2} := by
  intro i hi j hj
  by_contra hij
  have mem (k : ℕ) (hk : transitionAngle k u ≠ 0 ∧ transitionAngle k u ≠ Real.pi/2) :
      u ∈ transitionInterval k := by
    constructor
    · by_contra hn
      exact hk.2 (transitionAngle_full k (by linarith))
    · by_contra hn
      exact hk.1 (transitionAngle_zero k (by linarith))
  exact Set.disjoint_left.mp (transitionInterval_disjoint hij) (mem i hi) (mem j hj)

theorem thetaLog_sum_formula (J : ℕ) (u : ℝ) :
    (∑ j : Fin (J+1),thetaLog J u j)=1+
      ∑ j : Fin J, (Real.sin (transitionAngle (j+1) u)+Real.cos (transitionAngle (j+1) u)-1) := by
  rw [Fin.sum_univ_eq_sum_range (thetaLog J u),Fin.sum_univ_eq_sum_range (fun j => Real.sin (transitionAngle (j+1) u)+Real.cos (transitionAngle (j+1) u)-1)]
  simp only [thetaLog,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul,mul_one]
  rw [Finset.sum_range_succ' (fun j => Real.sin (boundedAngle J u j)),
    Finset.sum_range_succ (fun j => Real.cos (boundedAngle J u (j+1)))]
  simp only [boundedAngle_zero,boundedAngle_last,Real.sin_pi_div_two,Real.cos_zero]
  have hs : (∑ j ∈ Finset.range J,Real.sin (boundedAngle J u (j+1)))=
      ∑ j ∈ Finset.range J,Real.sin (transitionAngle (j+1) u) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [boundedAngle_inner (by omega) (by have := Finset.mem_range.mp hj; omega)]
  have hc : (∑ j ∈ Finset.range J,Real.cos (boundedAngle J u (j+1)))=
      ∑ j ∈ Finset.range J,Real.cos (transitionAngle (j+1) u) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [boundedAngle_inner (by omega) (by have := Finset.mem_range.mp hj; omega)]
  rw [hs,hc]
  push_cast
  ring

theorem thetaLog_sum_le (J : ℕ) (u : ℝ) : (∑ j : Fin (J+1),thetaLog J u j) ≤ 2 := by
  classical
  rw [thetaLog_sum_formula]
  let f (j : Fin J) := Real.sin (transitionAngle (j+1) u)+Real.cos (transitionAngle (j+1) u)-1
  have hz (j : Fin J) (hj : transitionAngle (j+1) u=0 ∨ transitionAngle (j+1) u=Real.pi/2) : f j=0 := by
    rcases hj with h|h <;> simp [f,h]
  suffices (∑ j,f j) ≤ 1 by linarith
  by_cases h : ∃ j : Fin J, transitionAngle (j+1) u≠0 ∧ transitionAngle (j+1) u≠Real.pi/2
  · obtain ⟨j,hj⟩ := h
    rw [Finset.sum_eq_single j]
    · dsimp [f]
      linarith [Real.sin_le_one (transitionAngle (j+1) u),Real.cos_le_one (transitionAngle (j+1) u)]
    · intro k _ hkj
      apply hz
      by_contra hh
      push Not at hh
      exact hkj (Fin.ext (by have he := transitionAngle_unique u hh hj; omega))
    · simp
  · have hh (j : Fin J) : f j=0 := by
      apply hz
      have hn := not_exists.mp h j
      tauto
    simp only [hh,Finset.sum_const_zero,zero_le_one]

theorem boundedAngle_difference_sum (J : ℕ) (u v : ℝ) :
    (∑ j : Fin (J+1), (|boundedAngle J u j-boundedAngle J v j|+
      |boundedAngle J u (j+1)-boundedAngle J v (j+1)|)) =
      2*∑ j : Fin J, |transitionAngle (j+1) u-transitionAngle (j+1) v| := by
  simp only [Finset.sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun j => |boundedAngle J u j-boundedAngle J v j|),
    Fin.sum_univ_eq_sum_range (fun j => |boundedAngle J u (j+1)-boundedAngle J v (j+1)|),
    Fin.sum_univ_eq_sum_range (fun j => |transitionAngle (j+1) u-transitionAngle (j+1) v|),
    Finset.sum_range_succ' (fun j => |boundedAngle J u j-boundedAngle J v j|),
    Finset.sum_range_succ (fun j => |boundedAngle J u (j+1)-boundedAngle J v (j+1)|)]
  simp only [boundedAngle_zero,boundedAngle_last,sub_self,abs_zero,add_zero]
  have hh : (∑ j ∈ Finset.range J,|boundedAngle J u (j+1)-boundedAngle J v (j+1)|)=
      ∑ j ∈ Finset.range J,|transitionAngle (j+1) u-transitionAngle (j+1) v| := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [boundedAngle_inner (by omega) (by have := Finset.mem_range.mp hj; omega),
      boundedAngle_inner (by omega) (by have := Finset.mem_range.mp hj; omega)]
  rw [hh]
  ring

theorem thetaLog_distance (J : ℕ) (u v : ℝ) :
    (∑ j : Fin (J+1), |thetaLog J u j-thetaLog J v j|) ≤ (Real.pi/scheduleH)*dist u v := by
  calc
    _ ≤ ∑ j : Fin (J+1), (|boundedAngle J u j-boundedAngle J v j|+
        |boundedAngle J u (j+1)-boundedAngle J v (j+1)|) := by
      apply Finset.sum_le_sum
      intro j _
      have he : thetaLog J u j-thetaLog J v j =
          (Real.sin (boundedAngle J u j)-Real.sin (boundedAngle J v j))+
          (Real.cos (boundedAngle J u (j+1))-Real.cos (boundedAngle J v (j+1))) := by unfold thetaLog; ring
      rw [he]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using Real.lipschitzWith_sin.dist_le_mul (boundedAngle J u j) (boundedAngle J v j)
      · simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using Real.lipschitzWith_cos.dist_le_mul (boundedAngle J u (j+1)) (boundedAngle J v (j+1))
    _ = 2*∑ j : Fin J,|transitionAngle (j+1) u-transitionAngle (j+1) v| := boundedAngle_difference_sum J u v
    _ ≤ 2*(angleSpeed*dist u v) := mul_le_mul_of_nonneg_left (angle_sum_distance J u v) (by norm_num)
    _ = (Real.pi/scheduleH)*dist u v := by change 2*(Real.pi/(2*scheduleH)*dist u v)=_; ring

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def theta (J : ℕ) (r : ℝ) (j : ℕ) : ℝ :=
  if r≤0 then if j=J then 1 else 0 else thetaLog J (Real.log r) j

theorem theta_nonneg (J j : ℕ) (r : ℝ) : 0 ≤ theta J r j := by
  unfold theta
  split_ifs <;> first | exact thetaLog_nonneg J j _ | norm_num

theorem theta_le_one (J j : ℕ) (r : ℝ) : theta J r j ≤ 1 := by
  unfold theta
  split_ifs <;> first | exact thetaLog_le_one J j _ | norm_num

theorem theta_squares (J : ℕ) (r : ℝ) : (∑ j : Fin (J+1),theta J r j^2)=1 := by
  classical
  by_cases hr : r≤0
  · simp only [theta,hr,↓reduceIte,ite_pow,one_pow,zero_pow (two_ne_zero)]
    have he (j : Fin (J+1)) : (j.val=J) ↔ j=Fin.last J := by simp only [Fin.ext_iff,Fin.val_last]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  · simp only [theta,hr,↓reduceIte]
    exact thetaLog_squares J _

theorem theta_sum_le (J : ℕ) (r : ℝ) : (∑ j : Fin (J+1),theta J r j) ≤ 2 := by
  classical
  by_cases hr : r≤0
  · simp only [theta,hr,↓reduceIte]
    have he (j : Fin (J+1)) : (j.val=J) ↔ j=Fin.last J := by simp only [Fin.ext_iff,Fin.val_last]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    norm_num
  · simp only [theta,hr,↓reduceIte]
    exact thetaLog_sum_le J _

theorem log_radius_lower {r : ℝ} (hr : 0<r) (j : ℕ)
    (hle : r ≤ Real.exp (-scheduleH)*rho j) : Real.log r ≤ Real.log (rho j)-scheduleH := by
  have hh := (Real.log_le_log_iff hr (mul_pos (Real.exp_pos _) (rho_pos j))).mpr hle
  rwa [Real.log_mul (Real.exp_pos _).ne' (rho_pos j).ne',Real.log_exp,neg_add_eq_sub] at hh

theorem boundedAngle_full_of_small {J j : ℕ} (hj : j≤J) {r : ℝ} (hr : 0<r)
    (hle : r≤Real.exp (-scheduleH)*rho J) : boundedAngle J (Real.log r) j=Real.pi/2 := by
  by_cases hz : j=0
  · simp [hz]
  · rw [boundedAngle_inner (by omega) hj]
    exact transitionAngle_full j ((log_radius_lower hr J hle).trans (sub_le_sub_right (log_rho_antitone hj) _))

theorem theta_terminal (J j : ℕ) {r : ℝ} (hr : r ≤ Real.exp (-scheduleH)*rho J) :
    theta J r j=if j=J then 1 else 0 := by
  by_cases h : r≤0
  · simp only [theta,h,↓reduceIte]
  have hp : 0<r := lt_of_not_ge h
  simp only [theta,h,↓reduceIte,thetaLog]
  rcases lt_trichotomy j J with hj|rfl|hj
  · rw [boundedAngle_full_of_small hj.le hp hr,boundedAngle_full_of_small (by omega) hp hr,
      Real.sin_pi_div_two,Real.cos_pi_div_two,ite_eq_right hj.ne]
    ring
  · simp only [boundedAngle_full_of_small le_rfl hp hr,boundedAngle_last,
      Real.sin_pi_div_two,Real.cos_zero,ite_true]
    ring
  · simp only [boundedAngle,show j≠0 by omega,show j+1≠0 by omega,hj,
      show J<j+1 by omega,↓reduceIte,Real.sin_zero,Real.cos_zero,ite_eq_right hj.ne',zero_add,sub_self]

theorem boundedAngle_continuous (J j : ℕ) : Continuous (fun u => boundedAngle J u j) := by
  unfold boundedAngle
  split_ifs
  · exact continuous_const
  · exact continuous_const
  · exact (transitionAngle_lipschitz j).continuous

theorem thetaLog_continuous (J j : ℕ) : Continuous (fun u => thetaLog J u j) :=
  ((Real.continuous_sin.comp (boundedAngle_continuous J j)).add (Real.continuous_cos.comp (boundedAngle_continuous J (j+1)))).sub continuous_const

theorem theta_continuous (J j : ℕ) : Continuous (fun r => theta J r j) := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : 0<r
  · apply ((thetaLog_continuous J j).continuousAt.comp (Real.continuousAt_log hr.ne')).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr] with s hs
    simp only [theta,not_le.mpr hs,↓reduceIte,Function.comp_def]
  · have hR : r<Real.exp (-scheduleH)*rho J := lt_of_le_of_lt (le_of_not_gt hr)
      (mul_pos (Real.exp_pos _) (rho_pos J))
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hR] with s hs
    exact theta_terminal J j hs.le

theorem theta_upper_support {J j : ℕ} (hj : 0<j) (hJ : j≤J) {r : ℝ}
    (_hr : 0≤r) (ht : theta J r j≠0) : r≤rho j := by
  by_contra hn
  have hp : 0<r := (rho_pos j).trans (lt_of_not_ge hn)
  have hlog : Real.log (rho j) ≤ Real.log r :=
    (Real.log_le_log_iff (rho_pos j) hp).mpr (le_of_not_ge hn)
  have ha := transitionAngle_zero j hlog
  apply ht
  simp only [theta,not_le.mpr hp,↓reduceIte,thetaLog_mul,boundedAngle_inner hj hJ,ha,Real.sin_zero,zero_mul]

theorem theta_lower_support {J j : ℕ} (hj : j<J) {r : ℝ}
    (_hr : 0≤r) (ht : theta J r j≠0) : ell j≤r := by
  by_contra hn
  have hp : 0<r := by
    by_contra hh
    have hz : r≤0 := le_of_not_gt hh
    exact ht (by simp [theta,hz,hj.ne])
  have hlog := log_radius_lower hp (j+1) (le_of_not_ge hn)
  have ha := transitionAngle_full (j+1) hlog
  apply ht
  simp only [theta,not_le.mpr hp,↓reduceIte,thetaLog_mul,
    boundedAngle_inner (by omega : 0<j+1) (by omega : j+1≤J),ha,Real.cos_pi_div_two,mul_zero]

theorem min_mul_log_distance {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    min r s*|Real.log r-Real.log s| ≤ |r-s| := by
  have oneOrder (r s : ℝ) (hr : 0<r) (hs : 0<s) (hle : r ≤ s) :
      r*|Real.log r-Real.log s| ≤ |r-s| := by
    have hlog := (Real.log_le_log_iff hr hs).mpr hle
    rw [abs_of_nonpos (sub_nonpos.mpr hlog),abs_of_nonpos (sub_nonpos.mpr hle)]
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hs hr)) hr.le
    rw [Real.log_div hs.ne' hr.ne'] at hh
    have he : r*(s/r-1)=s-r := by field_simp
    rw [he] at hh
    linarith
  rcases le_total r s with h|h
  · rw [min_eq_left h]
    exact oneOrder r s hr hs h
  · rw [min_eq_right h,abs_sub_comm (Real.log r),abs_sub_comm r]
    exact oneOrder s r hs hr h

theorem theta_weighted_distance (J : ℕ) {r s : ℝ} (hr : 0≤r) (hs : 0 ≤ s) :
    min r s*(∑ j : Fin (J+1),|theta J r j-theta J s j|) ≤
      (Real.pi/scheduleH)*|r-s| := by
  by_cases hr0 : r=0
  · simp only [hr0,min_eq_left hs,zero_mul]
    exact mul_nonneg (div_nonneg Real.pi_pos.le scheduleH_pos.le) (abs_nonneg _)
  by_cases hs0 : s=0
  · simp only [hs0,min_eq_right hr,zero_mul]
    exact mul_nonneg (div_nonneg Real.pi_pos.le scheduleH_pos.le) (abs_nonneg _)
  have hr' : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hs' : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  simp only [theta,not_le.mpr hr',not_le.mpr hs',↓reduceIte]
  calc
    _ ≤ min r s*((Real.pi/scheduleH)*|Real.log r-Real.log s|) :=
      mul_le_mul_of_nonneg_left (thetaLog_distance J _ _) (le_min hr hs)
    _ = (Real.pi/scheduleH)*(min r s*|Real.log r-Real.log s|) := by ring
    _ ≤ (Real.pi/scheduleH)*|r-s| := mul_le_mul_of_nonneg_left (min_mul_log_distance hr' hs')
      (div_nonneg Real.pi_pos.le scheduleH_pos.le)

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

abbrev Level := ℕ × ℕ
def levelJ (lev : Level) : ℕ := lev.1+lev.2+2
abbrev Block (lev : Level) := (j : Fin (levelJ lev+1)) × BandGrid j.val

structure Label where
  level : Level
  band : Fin (levelJ level+1)
  tag : BandGrid band.val

instance : Countable Label := by
  apply Function.Injective.countable (f := fun γ : Label => (⟨γ.level,⟨γ.band,γ.tag⟩⟩ : (lev : Level) × Block lev))
  intro a b h
  cases a
  cases b
  cases h
  rfl

instance : TopologicalSpace Label := ⊥
instance : DiscreteTopology Label := ⟨rfl⟩

abbrev InputCoordinate := ℕ ⊕ Label

def coordinateEnumeration : InputCoordinate ≃ ℕ := Classical.choice inferInstance

def rowIndex (i : ℕ) : ℕ := coordinateEnumeration (Sum.inl i)
def labelIndex (γ : Label) : ℕ := coordinateEnumeration (Sum.inr γ)
def blockLabel (lev : Level) (b : Block lev) : Label := ⟨lev,b.1,b.2⟩

@[simp] theorem blockLabel_level (lev : Level) (b : Block lev) : (blockLabel lev b).level=lev := rfl

theorem blockLabel_injective (lev : Level) : Function.Injective (blockLabel lev) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

theorem labelIndex_injective : Function.Injective labelIndex := by
  intro a b h
  exact Sum.inr.inj (coordinateEnumeration.injective h)

theorem rowIndex_injective : Function.Injective rowIndex := by
  intro a b h
  exact Sum.inl.inj (coordinateEnumeration.injective h)

theorem rowIndex_ne_labelIndex (i : ℕ) (γ : Label) : rowIndex i≠labelIndex γ := by
  intro h
  cases coordinateEnumeration.injective h

def blockCoordinates (lev : Level) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun b : Block lev => labelIndex (blockLabel lev b))

theorem mem_blockCoordinates {lev : Level} {k : ℕ} : k ∈ blockCoordinates lev ↔
    ∃ γ : Label, γ.level=lev ∧ labelIndex γ=k := by
  classical
  constructor
  · intro hk
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hk
    exact ⟨blockLabel lev b,rfl,hb⟩
  · rintro ⟨⟨μ,j,ξ⟩,h,rfl⟩
    cases h
    exact Finset.mem_image.mpr ⟨⟨j,ξ⟩,Finset.mem_univ _,rfl⟩

theorem blockCoordinates_nonempty (lev : Level) : (blockCoordinates lev).Nonempty := by
  classical
  let j : Fin (levelJ lev+1) := ⟨0,by omega⟩
  let ξ : BandGrid 0 := Fin.elim0
  exact ⟨labelIndex (⟨lev,j,ξ⟩ : Label),mem_blockCoordinates.mpr ⟨⟨lev,j,ξ⟩,rfl,rfl⟩⟩

def predecessorCoordinates (lev : Level) : Finset ℕ :=
  match lev.2 with
  | 0 => {rowIndex lev.1}
  | n+1 => blockCoordinates (lev.1,n)

def radiusCoordinates (lev : Level) : Finset ℕ := predecessorCoordinates lev ∪ blockCoordinates lev

theorem radiusCoordinates_nonempty (lev : Level) : (radiusCoordinates lev).Nonempty :=
  (blockCoordinates_nonempty lev).mono Finset.subset_union_right

def levelSuccessor (lev : Level) : Level := (lev.1,lev.2+1)

def coordinateLevels (k : ℕ) : Finset Level := by
  classical
  exact match coordinateEnumeration.symm k with
  | Sum.inl i => {(i,0)}
  | Sum.inr γ => {γ.level,levelSuccessor γ.level}

theorem radius_incidence (lev : Level) (k : ℕ) :
    k ∈ radiusCoordinates lev ↔ lev ∈ coordinateLevels k := by
  classical
  obtain ⟨c,rfl⟩ := coordinateEnumeration.surjective k
  cases c with
  | inl i =>
    have hk : ∀ μ, coordinateEnumeration (Sum.inl i) ∉ blockCoordinates μ := by
      intro μ h
      obtain ⟨γ,_,he⟩ := mem_blockCoordinates.mp h
      exact rowIndex_ne_labelIndex i γ he.symm
    simp only [radiusCoordinates,Finset.mem_union,coordinateLevels,Equiv.symm_apply_apply,
      Finset.mem_singleton,hk,or_false]
    rcases lev with ⟨l,n⟩
    cases n with
    | zero => simp only [predecessorCoordinates,Finset.mem_singleton,Prod.mk.injEq,and_true]
              change rowIndex i=rowIndex l ↔ l=i
              rw [rowIndex_injective.eq_iff]
              exact eq_comm
    | succ n => simp only [predecessorCoordinates,hk,Prod.mk.injEq,Nat.succ_ne_zero,and_false]
  | inr γ =>
    have hk (μ : Level) : coordinateEnumeration (Sum.inr γ) ∈ blockCoordinates μ ↔ γ.level=μ := by
      rw [mem_blockCoordinates]
      constructor
      · rintro ⟨δ,hδ,he⟩
        exact (labelIndex_injective he) ▸ hδ
      · intro h
        exact ⟨γ,h,rfl⟩
    simp only [radiusCoordinates,Finset.mem_union,coordinateLevels,Equiv.symm_apply_apply,
      Finset.mem_insert,Finset.mem_singleton,hk]
    rcases lev with ⟨i,n⟩
    rcases hγ : γ.level with ⟨l,m⟩
    cases n with
    | zero =>
      simp only [predecessorCoordinates,Finset.mem_singleton]
      have hn : coordinateEnumeration (Sum.inr γ)≠rowIndex i := (rowIndex_ne_labelIndex i γ).symm
      simp only [hn,false_or,levelSuccessor,Prod.mk.injEq,Nat.zero_ne_add_one,and_false,or_false]
      tauto
    | succ n =>
      simp only [predecessorCoordinates,hk,hγ,levelSuccessor,Prod.mk.injEq]
      omega

theorem radius_finite_exceptions (N : ℕ) :
    {lev : Level | ∃ k≤N, k ∈ radiusCoordinates lev}.Finite := by
  classical
  have he : {lev : Level | ∃ k≤N, k ∈ radiusCoordinates lev} ⊆
      ↑((Finset.range (N+1)).biUnion coordinateLevels) := by
    rintro lev ⟨k,hk,hlev⟩
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_range.mpr (by omega),(radius_incidence lev k).mp hlev⟩
  exact (Finset.finite_toSet _).subset he

def finiteProjection (I : Finset ℕ) : C0 →L[ℝ] C0 :=
  LinearMap.mkContinuous
    ({
      toFun := fun s : C0 => extendFinite I (fun k => s k)
      map_add' := by
        intro s t
        ext k
        simp only [extendFinite_apply,ZeroAtInftyContinuousMap.add_apply]
        split_ifs <;> simp
      map_smul' := by
        intro a s
        ext k
        simp only [extendFinite_apply,ZeroAtInftyContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
        split_ifs <;> simp } : C0 →ₗ[ℝ] C0) 1 (fun s => by
      change ‖extendFinite I (fun k => s k)‖ ≤ 1 * ‖s‖
      simpa only [one_mul] using extendFinite_norm_le I (fun k => s k) (norm_nonneg s) (fun k => c0_norm_apply_le s k))

@[simp] theorem finiteProjection_apply (I : Finset ℕ) (s : C0) (k : ℕ) :
    finiteProjection I s k = if k∈I then s k else 0 := by
  classical
  rfl

def finiteRadius (I : Finset ℕ) (s : C0) : ℝ := ‖finiteProjection I s‖
def localRadius (lev : Level) : C0 → ℝ := finiteRadius (radiusCoordinates lev)

theorem finiteRadius_nonneg (I : Finset ℕ) (s : C0) : 0 ≤ finiteRadius I s := norm_nonneg _

theorem finiteRadius_le (I : Finset ℕ) (s : C0) : finiteRadius I s≤‖s‖ := by
  apply c0_norm_le _ (norm_nonneg s)
  intro k
  rw [finiteProjection_apply]
  split_ifs
  · exact c0_norm_apply_le s k
  · simp

theorem coordinate_le_finiteRadius {I : Finset ℕ} (s : C0) {k : ℕ} (hk : k∈I) :
    |s k| ≤ finiteRadius I s := by
  simpa only [finiteRadius,finiteProjection_apply,hk,↓reduceIte] using c0_norm_apply_le (finiteProjection I s) k

theorem finiteRadius_lipschitz (I : Finset ℕ) : LipschitzWith 1 (finiteRadius I) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [finiteRadius,NNReal.coe_one,one_mul,dist_eq_norm]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← map_sub]
  exact finiteRadius_le I (s-t)

theorem finiteRadius_le_tau {I : Finset ℕ} (N : ℕ) (hI : ∀ k∈I, N<k) (s : C0) :
    finiteRadius I s ≤ tau N s := by
  apply c0_norm_le _ (tau_nonneg _ _)
  intro k
  rw [finiteProjection_apply]
  split_ifs with hk
  · have hh := c0_norm_apply_le (coordinateTail N s) k
    simpa only [tau,coordinateTail_apply,hI k hk,↓reduceIte] using hh
  · simpa using tau_nonneg N s

theorem finiteRadius_smul (I : Finset ℕ) (a : ℝ) (s : C0) :
    finiteRadius I (a • s)=|a| * finiteRadius I s := by
  simp only [finiteRadius,map_smul,norm_smul,Real.norm_eq_abs]

theorem localRadius_tendsto (s : C0) : Tendsto (fun lev => localRadius lev s) cofinite (nhds 0) := by
  have ht := tau_tendsto_zero s
  rw [Metric.tendsto_atTop] at ht
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N,hN⟩ := ht ε hε
  filter_upwards [(radius_finite_exceptions N).eventually_cofinite_notMem] with lev hlev
  have he : ∀ k∈radiusCoordinates lev, N<k := by
    intro k hk
    by_contra hn
    exact hlev ⟨k,by omega,hk⟩
  have hh := finiteRadius_le_tau N he s
  have hτ := hN N le_rfl
  simpa only [Real.dist_eq,sub_zero,localRadius,abs_of_nonneg (finiteRadius_nonneg _ s)] using
    hh.trans_lt (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (tau_nonneg _ s)] using hτ)

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def blockVector (lev : Level) (s : C0Ball) (b : Block lev) : ℝ :=
  theta (levelJ lev) (localRadius lev s.val) b.1 * bandVector b.1 b.2 (prefixRestrict b.1 s)

def blockRow (lev : Level) (s : C0Ball) (b : Block lev) : ℝ :=
  theta (levelJ lev) (localRadius lev s.val) b.1 * bandRow b.1 b.2 (prefixRestrict b.1 s)

theorem blockVector_nonneg (lev : Level) (s : C0Ball) (b : Block lev) :
    0≤blockVector lev s b := mul_nonneg (theta_nonneg _ _ _) (bandVector_nonneg _ _ _)

theorem blockVector_le_one (lev : Level) (s : C0Ball) (b : Block lev) :
    blockVector lev s b ≤ 1 := by
  calc
    _ ≤ 1*1 := mul_le_mul (theta_le_one _ _ _) (bandVector_le_one _ _ _) (bandVector_nonneg _ _ _) zero_le_one
    _ = 1 := one_mul _

theorem blockRow_nonneg (lev : Level) (s : C0Ball) (b : Block lev) :
    0≤blockRow lev s b := mul_nonneg (theta_nonneg _ _ _) (bandRow_nonneg _ _ _)

theorem blockRow_sum (lev : Level) (s : C0Ball) : ∑ b : Block lev,blockRow lev s b ≤ 2 := by
  change (∑ b : (j : Fin (levelJ lev+1)) × BandGrid j.val,
    theta (levelJ lev) (localRadius lev s.val) b.1 * bandRow b.1 b.2 (prefixRestrict b.1 s)) ≤ 2
  rw [Fintype.sum_sigma]
  simp only [← Finset.mul_sum,bandRow_sum,mul_one]
  exact theta_sum_le _ _

theorem blockRow_vector (lev : Level) (s : C0Ball) :
    ∑ b : Block lev, blockRow lev s b*blockVector lev s b=1 := by
  change (∑ b : (j : Fin (levelJ lev+1)) × BandGrid j.val,
    (theta (levelJ lev) (localRadius lev s.val) b.1 * bandRow b.1 b.2 (prefixRestrict b.1 s))*
    (theta (levelJ lev) (localRadius lev s.val) b.1 * bandVector b.1 b.2 (prefixRestrict b.1 s)))=1
  rw [Fintype.sum_sigma]
  have he (j : Fin (levelJ lev+1)) : (∑ ξ : BandGrid j,
    (theta (levelJ lev) (localRadius lev s.val) j*bandRow j ξ (prefixRestrict j s))*
    (theta (levelJ lev) (localRadius lev s.val) j*bandVector j ξ (prefixRestrict j s)))=
    theta (levelJ lev) (localRadius lev s.val) j^2 := by
    calc
      _ = ∑ ξ : BandGrid j, theta (levelJ lev) (localRadius lev s.val) j^2*
          (bandRow j ξ (prefixRestrict j s)*bandVector j ξ (prefixRestrict j s)) := by
        apply Finset.sum_congr rfl
        intro ξ _
        ring
      _ = _ := by rw [← Finset.mul_sum,bandRow_vector,mul_one]
  simp only [he]
  exact theta_squares _ _

theorem bandL_ge_dyadic_inv (j : ℕ) : (2 : ℝ)^j ≤ bandL j := by
  let : Nonempty (BandGrid j) := ⟨fun _ => ⟨0,by constructor; exact neg_nonpos.mpr (Int.natCast_nonneg _); exact Int.natCast_nonneg _⟩⟩
  have hc : (1 : ℝ) ≤ Fintype.card (BandGrid j) := by exact_mod_cast Fintype.card_pos
  simp only [bandL,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,NNReal.coe_pow]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) j]

theorem bandVector_distance (j : ℕ) (ξ : BandGrid j) (s t : PrefixCube j) :
    |bandVector j ξ s-bandVector j ξ t| ≤ bandL j*dist s t := by
  exact ((bandVector_lipschitz j ξ).dist_le_mul s t).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast bandL_ge_dyadic_inv j) dist_nonneg)

theorem theta_band_budget (J : ℕ) (j : Fin (J+1)) {r s δ D : ℝ}
    (hr : 0≤r) (hs : 0 ≤ s) (hδ : 0≤δ) (hD : D≤bandL j*δ) (hD0 : j.val=0 → D=0) :
    min r s*(theta J r j*D) ≤ (eta/4)*theta J r j*δ := by
  by_cases hj : j.val=0
  · rw [hD0 hj,mul_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg eta_pos.le (by norm_num)) (theta_nonneg _ _ _)) hδ
  by_cases ht : theta J r j=0
  · simp only [ht,zero_mul,mul_zero,le_refl]
  have hm : min r s≤rho j := (min_le_left _ _).trans (theta_upper_support (by omega) (by omega) hr ht)
  have hL : min r s*bandL j≤eta/4 := by
    calc
      _ ≤ rho j*bandL j := mul_le_mul_of_nonneg_right hm (bandL j).coe_nonneg
      _ = bandL j*rho j := mul_comm _ _
      _ ≤ eta/4 := rho_lip_budget (by omega)
  calc
    _ ≤ min r s*(theta J r j*(bandL j*δ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD (theta_nonneg _ _ _)) (le_min hr hs)
    _ = (min r s*bandL j)*theta J r j*δ := by ring
    _ ≤ (eta/4)*theta J r j*δ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hL (theta_nonneg _ _ _)) hδ

theorem bandRow_scaled_difference {j : ℕ} (a b : ℝ) (ha : 0≤a) (s t : PrefixCube j) :
    (∑ ξ : BandGrid j,|a*bandRow j ξ s-b*bandRow j ξ t|) ≤
      |a-b|+a*(∑ ξ : BandGrid j,|bandRow j ξ s-bandRow j ξ t|) := by
  calc
    _ ≤ ∑ ξ : BandGrid j,(|a-b| *bandRow j ξ t+a*|bandRow j ξ s-bandRow j ξ t|) := by
      apply Finset.sum_le_sum
      intro ξ _
      rw [show a*bandRow j ξ s-b*bandRow j ξ t=(a-b)*bandRow j ξ t+a*(bandRow j ξ s-bandRow j ξ t) by ring]
      refine (abs_add_le _ _).trans_eq ?_
      simp only [abs_mul,abs_of_nonneg ha,abs_of_nonneg (bandRow_nonneg j ξ t)]
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,bandRow_sum,mul_one]

theorem blockRow_distance_decompose (lev : Level) (s t : C0Ball) :
    (∑ b : Block lev,|blockRow lev s b-blockRow lev t b|) ≤
      ∑ j : Fin (levelJ lev+1), (|theta (levelJ lev) (localRadius lev s.val) j-
        theta (levelJ lev) (localRadius lev t.val) j|+
          theta (levelJ lev) (localRadius lev s.val) j*
            ∑ ξ : BandGrid j,|bandRow j ξ (prefixRestrict j s)-bandRow j ξ (prefixRestrict j t)|) := by
  unfold blockRow
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro j _
  exact bandRow_scaled_difference (j := j.val)
    (theta (levelJ lev) (localRadius lev s.val) j.val)
    (theta (levelJ lev) (localRadius lev t.val) j.val)
    (theta_nonneg _ _ _) (prefixRestrict j.val s) (prefixRestrict j.val t)

theorem blockRow_weighted_distance (lev : Level) (s t : C0Ball) :
    min (localRadius lev s.val) (localRadius lev t.val)*
      (∑ b : Block lev,|blockRow lev s b-blockRow lev t b|) ≤ eta*dist s t := by
  let J := levelJ lev
  let r := localRadius lev s.val
  let r' := localRadius lev t.val
  let δ := dist s t
  let D (j : Fin (J+1)) := ∑ ξ : BandGrid j,|bandRow j ξ (prefixRestrict j s)-bandRow j ξ (prefixRestrict j t)|
  have hr : 0≤r := finiteRadius_nonneg _ _
  have hr' : 0≤r' := finiteRadius_nonneg _ _
  have hrad : |r-r'|≤δ := by
    change dist (finiteRadius (radiusCoordinates lev) s.val) (finiteRadius (radiusCoordinates lev) t.val) ≤ dist s.val t.val
    simpa only [NNReal.coe_one,one_mul] using (finiteRadius_lipschitz (radiusCoordinates lev)).dist_le_mul s.val t.val
  have hD (j : Fin (J+1)) : D j≤bandL j*δ := by
    exact (bandRow_distance j _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one,one_mul] using (prefixRestrict_lipschitz j).dist_le_mul s t) (bandL j).coe_nonneg)
  have hD0 (j : Fin (J+1)) (hj : j.val=0) : D j=0 := by
    dsimp [D]
    have he : prefixRestrict j s=prefixRestrict j t := by rw [hj]; exact Subsingleton.elim _ _
    simp only [he,sub_self,abs_zero,Finset.sum_const_zero]
  have hsum := blockRow_distance_decompose lev s t
  have hschedule : min r r'*(∑ j : Fin (J+1),|theta J r j-theta J r' j|) ≤ (eta/2)*δ := by
    calc
      _ ≤ (Real.pi/scheduleH)*|r-r'| := theta_weighted_distance J hr hr'
      _ ≤ (eta/2)*δ := mul_le_mul schedule_speed hrad (abs_nonneg _) (div_nonneg eta_pos.le (by norm_num))
  calc
    _ ≤ min r r'*(∑ j : Fin (J+1),(|theta J r j-theta J r' j|+theta J r j*D j)) :=
      mul_le_mul_of_nonneg_left hsum (le_min hr hr')
    _ = min r r'*(∑ j : Fin (J+1),|theta J r j-theta J r' j|)+
        ∑ j : Fin (J+1),min r r'*(theta J r j*D j) := by
      simp only [Finset.sum_add_distrib,mul_add,Finset.mul_sum]
    _ ≤ (eta/2)*δ+∑ j : Fin (J+1),(eta/4)*theta J r j*δ :=
      add_le_add hschedule (Finset.sum_le_sum (fun j _ => theta_band_budget J j hr hr' dist_nonneg (hD j) (hD0 j)))
    _ = (eta/2)*δ+(eta/4)*(∑ j : Fin (J+1),theta J r j)*δ := by
      rw [← Finset.sum_mul,← Finset.mul_sum]
    _ ≤ (eta/2)*δ+(eta/4)*2*δ := add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (theta_sum_le J r) (show 0 ≤ eta/4 from div_nonneg eta_pos.le (by norm_num))) (show 0 ≤ δ from dist_nonneg))
    _ = eta*dist s t := by dsimp [δ]; ring

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem product_difference_bound {a b u v : ℝ} (ha : 0≤a) (hv : |v|≤1) :
    |a*u-b*v| ≤ |a-b|+a*|u-v| := by
  calc
    _ = |(a-b)*v+a*(u-v)| := by congr 1; ring
    _ ≤ |(a-b)*v|+|a*(u-v)| := abs_add_le _ _
    _ = |a-b| *|v|+a*|u-v| := by rw [abs_mul,abs_mul,abs_of_nonneg ha]
    _ ≤ |a-b| *1+a*|u-v| := add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _)) le_rfl
    _ = _ := by rw [mul_one]

theorem theta_weighted_coordinate (J : ℕ) (j : Fin (J+1)) {r s : ℝ} (hr : 0≤r) (hs : 0 ≤ s) :
    min r s*|theta J r j-theta J s j| ≤ (Real.pi/scheduleH)*|r-s| := by
  apply le_trans _ (theta_weighted_distance J hr hs)
  apply mul_le_mul_of_nonneg_left _ (le_min hr hs)
  exact Finset.single_le_sum (fun (i : Fin (J+1)) _ => abs_nonneg (theta J r i-theta J s i)) (Finset.mem_univ j)

theorem blockVector_weighted_distance (lev : Level) (s t : C0Ball) (b : Block lev) :
    min (localRadius lev s.val) (localRadius lev t.val)*
      |blockVector lev s b-blockVector lev t b| ≤ eta*dist s t := by
  let J := levelJ lev
  let r := localRadius lev s.val
  let r' := localRadius lev t.val
  let δ := dist s t
  let D := |bandVector b.1 b.2 (prefixRestrict b.1 s)-bandVector b.1 b.2 (prefixRestrict b.1 t)|
  have hr : 0≤r := finiteRadius_nonneg _ _
  have hr' : 0≤r' := finiteRadius_nonneg _ _
  have hrad : |r-r'|≤δ := by
    change dist (finiteRadius (radiusCoordinates lev) s.val) (finiteRadius (radiusCoordinates lev) t.val) ≤ dist s.val t.val
    simpa only [NNReal.coe_one,one_mul] using (finiteRadius_lipschitz (radiusCoordinates lev)).dist_le_mul s.val t.val
  have hD : D≤bandL b.1*δ := by
    exact (bandVector_distance b.1 b.2 _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one,one_mul] using (prefixRestrict_lipschitz b.1).dist_le_mul s t) (bandL b.1).coe_nonneg)
  have hD0 (hj : b.1.val=0) : D=0 := by
    dsimp [D]
    have he : prefixRestrict b.1 s=prefixRestrict b.1 t := by rw [hj]; exact Subsingleton.elim _ _
    simp only [he,sub_self,abs_zero]
  have hschedule : min r r'*|theta J r b.1-theta J r' b.1| ≤ (eta/2)*δ := by
    calc
      _ ≤ (Real.pi/scheduleH)*|r-r'| := theta_weighted_coordinate J b.1 hr hr'
      _ ≤ (eta/2)*δ := mul_le_mul schedule_speed hrad (abs_nonneg _) (div_nonneg eta_pos.le (by norm_num))
  have hprod : |blockVector lev s b-blockVector lev t b| ≤
      |theta J r b.1-theta J r' b.1|+theta J r b.1*D :=
    product_difference_bound (theta_nonneg _ _ _) (by rw [abs_of_nonneg (bandVector_nonneg _ _ _)]; exact bandVector_le_one _ _ _)
  calc
    _ ≤ min r r'*(|theta J r b.1-theta J r' b.1|+theta J r b.1*D) :=
      mul_le_mul_of_nonneg_left hprod (le_min hr hr')
    _ = min r r'*|theta J r b.1-theta J r' b.1|+min r r'*(theta J r b.1*D) := mul_add _ _ _
    _ ≤ (eta/2)*δ+(eta/4)*theta J r b.1*δ :=
      add_le_add hschedule (theta_band_budget J b.1 hr hr' dist_nonneg hD hD0)
    _ ≤ (eta/2)*δ+(eta/4)*1*δ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (theta_le_one _ _ _)
        (show 0≤eta/4 from div_nonneg eta_pos.le (by norm_num))) dist_nonneg)
    _ ≤ eta*dist s t := by dsimp [δ]; nlinarith [eta_pos,mul_nonneg eta_pos.le (dist_nonneg (x := s) (y := t))]

theorem bandRow_continuous (j : ℕ) (ξ : BandGrid j) : Continuous (bandRow j ξ) := by
  exact (bandBump_lipschitz j ξ).continuous.div
    (continuous_finsetSum _ (fun ζ _ => (bandBump_lipschitz j ζ).continuous)) (fun s => (bandDenominator_pos j s).ne')

theorem localRadius_continuous (lev : Level) : Continuous (localRadius lev) :=
  (finiteRadius_lipschitz _).continuous

theorem blockVector_continuous (lev : Level) (b : Block lev) : Continuous (fun s => blockVector lev s b) :=
  ((theta_continuous (levelJ lev) b.1).comp ((localRadius_continuous lev).comp continuous_subtype_val)).mul
    ((bandVector_lipschitz b.1 b.2).continuous.comp (prefixRestrict_lipschitz b.1).continuous)

theorem blockRow_continuous (lev : Level) (b : Block lev) : Continuous (fun s => blockRow lev s b) :=
  ((theta_continuous (levelJ lev) b.1).comp ((localRadius_continuous lev).comp continuous_subtype_val)).mul
    ((bandRow_continuous b.1 b.2).comp (prefixRestrict_lipschitz b.1).continuous)

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure FrozenWeights where
  vector : (lev : Level) → Block lev → ℝ
  row : (lev : Level) → Block lev → ℝ
  vector_bound : ∀ lev b, |vector lev b|≤1
  row_bound : ∀ lev, (∑ b : Block lev,|row lev b|)≤2
  pairing : ∀ lev, (∑ b : Block lev,row lev b*vector lev b)=1

def stateWeights (s : C0Ball) : FrozenWeights where
  vector := fun lev => blockVector lev s
  row := fun lev => blockRow lev s
  vector_bound := fun lev b => by rw [abs_of_nonneg (blockVector_nonneg _ _ _)]; exact blockVector_le_one _ _ _
  row_bound := fun lev => by simp only [abs_of_nonneg (blockRow_nonneg _ _ _)]; exact blockRow_sum lev s
  pairing := fun lev => blockRow_vector lev s

def blockInput (lev : Level) (x : C0) (b : Block lev) : ℝ := x (labelIndex (blockLabel lev b))

def rowScalar (W : FrozenWeights) (lev : Level) : C0 →L[ℝ] ℝ :=
  ∑ b : Block lev, (W.row lev b) • c0Eval (labelIndex (blockLabel lev b))

@[simp] theorem rowScalar_apply (W : FrozenWeights) (lev : Level) (x : C0) :
    rowScalar W lev x=∑ b : Block lev,W.row lev b*blockInput lev x b := by
  simp only [rowScalar,sum_apply,smul_apply,smul_eq_mul,c0Eval_apply,blockInput]

def previousScalar (W : FrozenWeights) (lev : Level) : C0 →L[ℝ] ℝ :=
  match lev.2 with
  | 0 => c0Eval (rowIndex lev.1)
  | n+1 => rowScalar W (lev.1,n)

def frozenCorrection (W : FrozenWeights) (γ : Label) : C0 →L[ℝ] ℝ :=
  W.vector γ.level ⟨γ.band,γ.tag⟩ • (previousScalar W γ.level-rowScalar W γ.level)

@[simp] theorem frozenCorrection_apply (W : FrozenWeights) (γ : Label) (x : C0) :
    frozenCorrection W γ x=W.vector γ.level ⟨γ.band,γ.tag⟩*(previousScalar W γ.level x-rowScalar W γ.level x) := rfl

def correction (γ : Label) (s : C0Ball) : ℝ := frozenCorrection (stateWeights s) γ s.val

theorem blockInput_abs_le (lev : Level) (x : C0) (b : Block lev) :
    |blockInput lev x b|≤finiteRadius (blockCoordinates lev) x := by
  apply coordinate_le_finiteRadius
  exact mem_blockCoordinates.mpr ⟨blockLabel lev b,rfl,rfl⟩

theorem finiteRadius_mono {I J : Finset ℕ} (h : I⊆J) (x : C0) : finiteRadius I x≤finiteRadius J x := by
  apply c0_norm_le _ (finiteRadius_nonneg _ _)
  intro k
  rw [finiteProjection_apply]
  split_ifs with hk
  · exact coordinate_le_finiteRadius x (h hk)
  · simpa using finiteRadius_nonneg J x

theorem blockInput_le_radius (lev : Level) (x : C0) (b : Block lev) :
    |blockInput lev x b|≤localRadius lev x :=
  (blockInput_abs_le lev x b).trans (finiteRadius_mono Finset.subset_union_right x)

theorem abs_finite_dot_le {A : Type*} [Fintype A] (u v : A → ℝ) {R : ℝ} (hv : ∀ a, |v a|≤R) :
    |∑ a,u a*v a| ≤ (∑ a,|u a|)*R := by
  calc
    _ ≤ ∑ a,|u a*v a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a,|u a| *R := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv a) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem rowScalar_bound (W : FrozenWeights) (lev : Level) (x : C0) {R : ℝ}
    (hR : 0≤R) (hv : ∀ b,|blockInput lev x b|≤R) : |rowScalar W lev x|≤2*R := by
  rw [rowScalar_apply]
  exact (abs_finite_dot_le _ _ hv).trans (mul_le_mul_of_nonneg_right (W.row_bound lev) hR)

theorem rowScalar_local (W : FrozenWeights) (lev : Level) (x : C0) :
    |rowScalar W lev x|≤2*localRadius lev x :=
  rowScalar_bound W lev x (finiteRadius_nonneg _ _) (blockInput_le_radius lev x)

theorem previousScalar_local (W : FrozenWeights) (lev : Level) (x : C0) :
    |previousScalar W lev x|≤2*localRadius lev x := by
  rcases lev with ⟨i,n⟩
  cases n with
  | zero =>
    change |x (rowIndex i)|≤2*localRadius (i,0) x
    have hle : |x (rowIndex i)|≤localRadius (i,0) x := by
      apply coordinate_le_finiteRadius
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hz : 0≤localRadius (i,0) x := finiteRadius_nonneg _ _
    linarith
  | succ n =>
    apply rowScalar_bound W (i,n) x (finiteRadius_nonneg _ _)
    intro b
    exact (blockInput_abs_le _ _ b).trans (finiteRadius_mono Finset.subset_union_left x)

theorem scalar_difference_bound (W : FrozenWeights) (lev : Level) (x : C0) :
    |previousScalar W lev x-rowScalar W lev x|≤4*localRadius lev x := by
  exact (abs_sub _ _).trans (by linarith [previousScalar_local W lev x,rowScalar_local W lev x])

theorem frozenCorrection_local (W : FrozenWeights) (γ : Label) (x : C0) :
    |frozenCorrection W γ x|≤4*localRadius γ.level x := by
  rw [frozenCorrection_apply,abs_mul]
  calc
    _ ≤ 1*(4*localRadius γ.level x) := mul_le_mul (W.vector_bound _ _) (scalar_difference_bound W _ x) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem frozenCorrection_bound (W : FrozenWeights) (γ : Label) (x : C0) :
    |frozenCorrection W γ x|≤4*‖x‖ :=
  (frozenCorrection_local W γ x).trans (mul_le_mul_of_nonneg_left (finiteRadius_le _ _) (by norm_num))

theorem frozenCorrection_distance (W : FrozenWeights) (γ : Label) (x y : C0) :
    |frozenCorrection W γ x-frozenCorrection W γ y|≤4*dist x y := by
  rw [← map_sub,dist_eq_norm]
  exact frozenCorrection_bound W γ (x-y)

theorem rowScalar_weight_error (W V : FrozenWeights) (lev : Level) (x : C0) {q : ℝ}
    (h : localRadius lev x*(∑ b : Block lev,|W.row lev b-V.row lev b|)≤q) :
    |rowScalar W lev x-rowScalar V lev x|≤q := by
  rw [rowScalar_apply,rowScalar_apply,← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  exact (abs_finite_dot_le _ _ (blockInput_le_radius lev x)).trans (by simpa only [mul_comm] using h)

structure WeightError (W V : FrozenWeights) (x : C0) (q : ℝ) : Prop where
  vector : ∀ lev b, localRadius lev x*|W.vector lev b-V.vector lev b|≤q
  row : ∀ lev, localRadius lev x*(∑ b : Block lev,|W.row lev b-V.row lev b|)≤q

theorem previousScalar_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) (lev : Level) :
    |previousScalar W lev x-previousScalar V lev x|≤q := by
  rcases lev with ⟨i,n⟩
  cases n with
  | zero => simpa only [previousScalar,sub_self,abs_zero] using hq
  | succ n => exact rowScalar_weight_error W V (i,n) x (h.row (i,n))

theorem correction_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) (γ : Label) :
    |frozenCorrection W γ x-frozenCorrection V γ x|≤6*q := by
  let b : Block γ.level := ⟨γ.band,γ.tag⟩
  let a := previousScalar W γ.level x-rowScalar W γ.level x
  let a' := previousScalar V γ.level x-rowScalar V γ.level x
  have hb : |a|≤4*localRadius γ.level x := scalar_difference_bound W γ.level x
  have hs : |a-a'|≤2*q := by
    calc
      _ = |(previousScalar W γ.level x-previousScalar V γ.level x)-
          (rowScalar W γ.level x-rowScalar V γ.level x)| := by dsimp [a,a']; congr 1; ring
      _ ≤ |previousScalar W γ.level x-previousScalar V γ.level x|+
          |rowScalar W γ.level x-rowScalar V γ.level x| := abs_sub _ _
      _ ≤ q+q := add_le_add (previousScalar_weight_error hq h _) (rowScalar_weight_error W V _ x (h.row _))
      _ = 2*q := by ring
  calc
    _ = |(W.vector γ.level b-V.vector γ.level b)*a+V.vector γ.level b*(a-a')| := by
      simp only [frozenCorrection_apply]; dsimp only [a,a',b]; congr 1; ring
    _ ≤ |W.vector γ.level b-V.vector γ.level b| *|a|+|V.vector γ.level b| *|a-a'| := by
      simpa only [abs_mul] using abs_add_le ((W.vector γ.level b-V.vector γ.level b)*a) (V.vector γ.level b*(a-a'))
    _ ≤ |W.vector γ.level b-V.vector γ.level b| *(4*localRadius γ.level x)+1*(2*q) :=
      add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul (V.vector_bound _ _) hs (abs_nonneg _) zero_le_one)
    _ ≤ 4*q+2*q := by nlinarith [h.vector γ.level b]
    _ = 6*q := by ring

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def mixedState (s t : C0Ball) (lev : Level) : C0Ball :=
  if localRadius lev t.val≤localRadius lev s.val then s else t

def mixedWeights (s t : C0Ball) : FrozenWeights where
  vector := fun lev => blockVector lev (mixedState s t lev)
  row := fun lev => blockRow lev (mixedState s t lev)
  vector_bound := fun lev b => (stateWeights (mixedState s t lev)).vector_bound lev b
  row_bound := fun lev => (stateWeights (mixedState s t lev)).row_bound lev
  pairing := fun lev => (stateWeights (mixedState s t lev)).pairing lev

theorem mixed_left_error (s t : C0Ball) :
    WeightError (stateWeights s) (mixedWeights s t) s.val (eta*dist s t) := by
  have hq : 0≤eta*dist s t := mul_nonneg eta_pos.le dist_nonneg
  constructor
  · intro lev b
    change localRadius lev s.val*|blockVector lev s b-blockVector lev (mixedState s t lev) b|≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,mul_zero] using hq
    · have hh := blockVector_weighted_distance lev s t b
      simpa only [mixedState,h,↓reduceIte,min_eq_left (le_of_not_ge h)] using hh
  · intro lev
    change localRadius lev s.val*(∑ b : Block lev,|blockRow lev s b-blockRow lev (mixedState s t lev) b|)≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,Finset.sum_const_zero,mul_zero] using hq
    · have hh := blockRow_weighted_distance lev s t
      simpa only [mixedState,h,↓reduceIte,min_eq_left (le_of_not_ge h)] using hh

theorem mixed_right_error (s t : C0Ball) :
    WeightError (stateWeights t) (mixedWeights s t) t.val (eta*dist s t) := by
  have hq : 0≤eta*dist s t := mul_nonneg eta_pos.le dist_nonneg
  constructor
  · intro lev b
    change localRadius lev t.val*|blockVector lev t b-blockVector lev (mixedState s t lev) b|≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · have hh := blockVector_weighted_distance lev t s b
      simpa only [mixedState,h,↓reduceIte,min_eq_left h,dist_comm t s] using hh
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,mul_zero] using hq
  · intro lev
    change localRadius lev t.val*(∑ b : Block lev,|blockRow lev t b-blockRow lev (mixedState s t lev) b|)≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · have hh := blockRow_weighted_distance lev t s
      simpa only [mixedState,h,↓reduceIte,min_eq_left h,dist_comm t s] using hh
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,Finset.sum_const_zero,mul_zero] using hq

theorem abs_sub_three (a b c d : ℝ) : |a-b|≤|a-c|+|c-d|+|d-b| :=
  (abs_sub_le a c b).trans (by linarith [abs_sub_le c d b])

def correctionL : ℝ≥0 := 4+12/1000

theorem correctionL_coe : (correctionL : ℝ)=4+12*eta := by norm_num [correctionL,eta]

theorem correction_lipschitz (γ : Label) : LipschitzWith correctionL (correction γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,correctionL_coe]
  let W := mixedWeights s t
  let q := eta*dist s t
  have hq : 0≤q := mul_nonneg eta_pos.le dist_nonneg
  have h1 : |correction γ s-frozenCorrection W γ s.val|≤6*q := correction_weight_error hq (mixed_left_error s t) γ
  have h2 : |frozenCorrection W γ t.val-correction γ t|≤6*q := by
    rw [abs_sub_comm]
    exact correction_weight_error hq (mixed_right_error s t) γ
  have h3 : |frozenCorrection W γ s.val-frozenCorrection W γ t.val|≤4*dist s t := frozenCorrection_distance W γ s.val t.val
  have h := abs_sub_three (correction γ s) (correction γ t) (frozenCorrection W γ s.val) (frozenCorrection W γ t.val)
  dsimp only [q] at h1 h2
  nlinarith

theorem correction_local (γ : Label) (s : C0Ball) : |correction γ s|≤4*localRadius γ.level s.val :=
  frozenCorrection_local (stateWeights s) γ s.val

theorem correction_bound (γ : Label) (s : C0Ball) : |correction γ s|≤4 := by
  have hs : ‖s.val‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using s.property
  exact (frozenCorrection_bound (stateWeights s) γ s.val).trans (by linarith)

theorem correction_zero (γ : Label) : correction γ ⟨0,by simp⟩=0 := by
  exact map_zero (frozenCorrection (stateWeights _) γ)

theorem correction_band_support {γ : Label} {s : C0Ball} (h : correction γ s≠0) :
    dist (prefixRestrict γ.band s) (bandPoint γ.band γ.tag) ≤ 2*dyadic γ.band := by
  have hv : bandVector γ.band γ.tag (prefixRestrict γ.band s)≠0 := by
    intro hv
    apply h
    simp only [correction,frozenCorrection_apply,stateWeights,blockVector,hv,mul_zero,zero_mul]
  exact (bandVector_support hv).le

theorem correction_radius_support {γ : Label} {s : C0Ball} (h : correction γ s≠0)
    (hj : γ.band.val<levelJ γ.level) : ell γ.band≤localRadius γ.level s.val := by
  have ht : theta (levelJ γ.level) (localRadius γ.level s.val) γ.band≠0 := by
    intro ht
    apply h
    simp only [correction,frozenCorrection_apply,stateWeights,blockVector,ht,zero_mul]
  exact theta_lower_support hj (finiteRadius_nonneg _ _) ht

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def earlierRadiusCoordinates (lev : Level) : Finset ℕ :=
  match lev.2 with
  | 0 => ∅
  | n+1 => radiusCoordinates (lev.1,n)

def correctionCoordinates (lev : Level) : Finset ℕ :=
  (Finset.range (levelJ lev) ∪ {rowIndex lev.1}) ∪
    (radiusCoordinates lev ∪ earlierRadiusCoordinates lev)

theorem correctionCoordinates_nonempty (lev : Level) : (correctionCoordinates lev).Nonempty := by
  exact (radiusCoordinates_nonempty lev).mono (fun k hk => Finset.mem_union_right _ (Finset.mem_union_left _ hk))

theorem correctionCoordinates_prefix (lev : Level) : Finset.range (levelJ lev) ⊆ correctionCoordinates lev :=
  fun _ hk => Finset.mem_union_left _ (Finset.mem_union_left _ hk)

theorem correctionCoordinates_radius (lev : Level) : radiusCoordinates lev ⊆ correctionCoordinates lev :=
  fun _ hk => Finset.mem_union_right _ (Finset.mem_union_left _ hk)

theorem correctionCoordinates_previous (i n : ℕ) : radiusCoordinates (i,n) ⊆ correctionCoordinates (i,n+1) :=
  fun _ hk => Finset.mem_union_right _ (Finset.mem_union_right _ hk)

theorem correctionCoordinates_row (lev : Level) : rowIndex lev.1∈correctionCoordinates lev :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem prefixRestrict_eq_of_agree {j : ℕ} {s t : C0Ball}
    (h : ∀ k<j,s.val k=t.val k) : prefixRestrict j s=prefixRestrict j t := by
  ext k
  exact h k k.isLt

theorem finiteRadius_eq_of_agree {I : Finset ℕ} {x y : C0}
    (h : ∀ k∈I,x k=y k) : finiteRadius I x=finiteRadius I y := by
  unfold finiteRadius
  congr 1
  ext k
  rw [finiteProjection_apply,finiteProjection_apply]
  split_ifs with hk
  · exact h k hk
  · rfl

theorem blockVector_eq_of_agree {lev : Level} {s t : C0Ball}
    (hp : ∀ k<levelJ lev,s.val k=t.val k)
    (hr : ∀ k∈radiusCoordinates lev,s.val k=t.val k) :
    blockVector lev s=blockVector lev t := by
  funext b
  have hb : prefixRestrict b.1 s=prefixRestrict b.1 t := prefixRestrict_eq_of_agree (fun k hk => hp k (lt_of_lt_of_le hk (by omega)))
  have he : localRadius lev s.val=localRadius lev t.val := finiteRadius_eq_of_agree hr
  simp only [blockVector,he,hb]

theorem blockRow_eq_of_agree {lev : Level} {s t : C0Ball}
    (hp : ∀ k<levelJ lev,s.val k=t.val k)
    (hr : ∀ k∈radiusCoordinates lev,s.val k=t.val k) :
    blockRow lev s=blockRow lev t := by
  funext b
  have hb : prefixRestrict b.1 s=prefixRestrict b.1 t := prefixRestrict_eq_of_agree (fun k hk => hp k (lt_of_lt_of_le hk (by omega)))
  have he : localRadius lev s.val=localRadius lev t.val := finiteRadius_eq_of_agree hr
  simp only [blockRow,he,hb]

theorem state_rowScalar_eq_of_agree {lev : Level} {s t : C0Ball}
    (hp : ∀ k<levelJ lev,s.val k=t.val k)
    (hr : ∀ k∈radiusCoordinates lev,s.val k=t.val k) :
    rowScalar (stateWeights s) lev s.val=rowScalar (stateWeights t) lev t.val := by
  simp only [rowScalar_apply,stateWeights]
  apply Finset.sum_congr rfl
  intro b _
  have hb : blockInput lev s.val b=blockInput lev t.val b :=
    hr _ (Finset.mem_union_right _ (mem_blockCoordinates.mpr ⟨blockLabel lev b,rfl,rfl⟩))
  rw [blockRow_eq_of_agree hp hr,hb]

theorem correction_eq_of_agree (γ : Label) {s t : C0Ball}
    (h : ∀ k∈correctionCoordinates γ.level,s.val k=t.val k) : correction γ s=correction γ t := by
  have hp : ∀ k<levelJ γ.level,s.val k=t.val k := fun k hk => h k (correctionCoordinates_prefix γ.level (Finset.mem_range.mpr hk))
  have hr : ∀ k∈radiusCoordinates γ.level,s.val k=t.val k := fun k hk => h k (correctionCoordinates_radius γ.level hk)
  have hv := blockVector_eq_of_agree hp hr
  have ha := state_rowScalar_eq_of_agree hp hr
  have ha' : previousScalar (stateWeights s) γ.level s.val=previousScalar (stateWeights t) γ.level t.val := by
    rcases γ with ⟨⟨i,n⟩,j,ξ⟩
    cases n with
    | zero => exact h _ (correctionCoordinates_row (i,0))
    | succ n =>
      apply state_rowScalar_eq_of_agree
      · intro k hk
        apply hp k
        simp only [levelJ] at hk ⊢
        omega
      · intro k hk
        exact h k (correctionCoordinates_previous i n hk)
  change blockVector γ.level s ⟨γ.band,γ.tag⟩*(previousScalar (stateWeights s) γ.level s.val-rowScalar (stateWeights s) γ.level s.val)=
    blockVector γ.level t ⟨γ.band,γ.tag⟩*(previousScalar (stateWeights t) γ.level t.val-rowScalar (stateWeights t) γ.level t.val)
  rw [hv,ha,ha']

def correctionBase (γ : Label) : Cube (correctionCoordinates γ.level) → ℝ :=
  correction γ ∘ cubeExtend (correctionCoordinates γ.level)

theorem correctionBase_restrict (γ : Label) (s : C0Ball) :
    correctionBase γ (cubeRestrict (correctionCoordinates γ.level) s)=correction γ s := by
  apply correction_eq_of_agree
  intro k hk
  change extendFinite _ _ k=s.val k
  simp only [extendFinite_apply,hk,↓reduceDIte,cubeRestrict]

theorem correctionBase_bound (γ : Label) (x : Cube (correctionCoordinates γ.level)) : |correctionBase γ x|≤4 :=
  correction_bound γ _

theorem correctionBase_lipschitz (γ : Label) : LipschitzWith correctionL (correctionBase γ) := by
  simpa only [mul_one,correctionBase] using (correction_lipschitz γ).comp (cubeExtend_lipschitz (correctionCoordinates γ.level))

def concreteBases : CylinderBases Label where
  coordinates := fun γ => correctionCoordinates γ.level
  coordinates_nonempty := fun γ => correctionCoordinates_nonempty γ.level
  band := fun γ => γ.band.val
  ell := ell
  ell_pos := ell_pos
  base := correctionBase
  A := 4
  L0 := correctionL
  base_sup := correctionBase_bound
  base_lipschitz := correctionBase_lipschitz

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def fullTag (γ : Label) (k : ℕ) : Icc (-1 : ℝ) 1 :=
  if h : k<γ.band.val then bandPoint γ.band γ.tag ⟨k,h⟩ else ⟨0,by norm_num⟩

theorem band_le_level (γ : Label) : γ.band.val≤levelJ γ.level := Nat.le_of_lt_succ γ.band.isLt

theorem tag_support_base (γ : Label) (k : correctionCoordinates γ.level) (hk : k.val<γ.band.val) :
    ∀ x∈tsupport (correctionBase γ), dist (x k) (fullTag γ k.val)≤2*dyadic γ.band := by
  have hc : IsClosed {x : Cube (correctionCoordinates γ.level) | dist (x k) (fullTag γ k.val)≤2*dyadic γ.band} :=
    isClosed_le ((continuous_apply k).dist continuous_const) continuous_const
  apply closure_minimal _ hc
  intro x hx
  have hb := correction_band_support (γ := γ) (s := cubeExtend (correctionCoordinates γ.level) x) hx
  have hh : dist (prefixRestrict γ.band (cubeExtend (correctionCoordinates γ.level) x) ⟨k.val,hk⟩)
      (bandPoint γ.band γ.tag ⟨k.val,hk⟩) ≤ 2*dyadic γ.band :=
    (dist_le_pi_dist _ _ ⟨k.val,hk⟩).trans hb
  simpa only [Set.mem_ofPred_eq,prefixRestrict,cubeExtend,extendFinite_apply,k.property,↓reduceDIte,fullTag,hk,Subtype.dist_eq] using hh

def concreteTagLocalization : TagLocalization concreteBases where
  tag := fullTag
  contains_prefix := fun γ _index hk => correctionCoordinates_prefix γ.level
    (Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le (band_le_level γ)))
  ell_tendsto := ell_tendsto
  base_support := tag_support_base

def firstRadiusCoordinate (lev : Level) : ℕ := (radiusCoordinates lev).min' (radiusCoordinates_nonempty lev)

theorem firstRadiusCoordinate_mem (lev : Level) : firstRadiusCoordinate lev∈radiusCoordinates lev :=
  Finset.min'_mem _ _

theorem firstRadiusCoordinate_le (lev : Level) {k : ℕ} (hk : k∈radiusCoordinates lev) :
    firstRadiusCoordinate lev≤k := Finset.min'_le _ _ hk

theorem boundedLevels_finite (j : ℕ) : {lev : Level | levelJ lev≤j}.Finite := by
  apply ((Set.finite_Iic j).prod (Set.finite_Iic j)).subset
  intro lev h
  change lev.1≤j ∧ lev.2≤j
  change lev.1+lev.2+2≤j at h
  omega

theorem labels_at_level_finite (lev : Level) : {γ : Label | γ.level=lev}.Finite := by
  apply (Set.finite_range (blockLabel lev)).subset
  rintro ⟨μ,j,ξ⟩ h
  change μ=lev at h
  cases h
  exact ⟨⟨j,ξ⟩,rfl⟩

theorem labels_over_finite {F : Set Level} (hF : F.Finite) : {γ : Label | γ.level∈F}.Finite := by
  apply (hF.biUnion (fun lev _ => labels_at_level_finite lev)).subset
  intro γ hγ
  exact Set.mem_iUnion.mpr ⟨γ.level,Set.mem_iUnion.mpr ⟨hγ,rfl⟩⟩

theorem bounded_or_early_finite (j N : ℕ) :
    {γ : Label | γ.band.val≤j ∧ (γ.band.val=levelJ γ.level ∨ firstRadiusCoordinate γ.level≤N)}.Finite := by
  let F : Set Level := {lev | levelJ lev≤j} ∪ {lev | ∃ k≤N,k∈radiusCoordinates lev}
  have hF : F.Finite := (boundedLevels_finite j).union (radius_finite_exceptions N)
  apply (labels_over_finite hF).subset
  intro γ hγ
  rcases hγ.2 with ht|he
  · exact Or.inl (by change levelJ γ.level≤j; rw [← ht]; exact hγ.1)
  · exact Or.inr ⟨firstRadiusCoordinate γ.level,he,firstRadiusCoordinate_mem _⟩

theorem radius_support_base (γ : Label) (ht : γ.band.val≠levelJ γ.level) (N : ℕ)
    (hN : N<firstRadiusCoordinate γ.level) :
    ∀ x∈tsupport (correctionBase γ), ell γ.band≤tau N (cubeExtend (correctionCoordinates γ.level) x).val := by
  have hc : Continuous (fun x : Cube (correctionCoordinates γ.level) =>
      tau N (cubeExtend (correctionCoordinates γ.level) x).val) :=
    (tau_lipschitz N).continuous.comp (continuous_subtype_val.comp (cubeExtend_lipschitz _).continuous)
  apply closure_minimal _ (isClosed_le continuous_const hc)
  intro x hx
  have hb : ell γ.band≤localRadius γ.level (cubeExtend (correctionCoordinates γ.level) x).val :=
    correction_radius_support hx (lt_of_le_of_ne (band_le_level γ) ht)
  apply hb.trans
  apply finiteRadius_le_tau N
  intro k hk
  exact hN.trans_le (firstRadiusCoordinate_le γ.level hk)

def concreteRadiusLocalization : RadiusLocalization concreteBases where
  terminal := fun γ => γ.band.val=levelJ γ.level
  firstCoordinate := fun γ => firstRadiusCoordinate γ.level
  finite_exceptions := bounded_or_early_finite
  base_radius := radius_support_base

abbrev ConcreteSpace := SourceSpace concreteBases

theorem concrete_noLinearC0 : NoLinearC0 ConcreteSpace :=
  source_noLinearC0 concreteTagLocalization concreteRadiusLocalization

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section GeneralC0
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology A] [DiscreteTopology B]

def cfunOfTendsto (f : A → ℝ) (hf : Tendsto f cofinite (nhds 0)) : C₀(A,ℝ) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by simpa only [cocompact_eq_cofinite] using hf

theorem cfun_tendsto (f : C₀(A,ℝ)) : Tendsto f cofinite (nhds 0) := by
  simpa only [cocompact_eq_cofinite] using zero_at_infty f

theorem cfun_norm_apply_le {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (f : C₀(A,ℝ)) (a : A) : |f a|≤‖f‖ := f.toBCF.norm_coe_le_norm a

theorem cfun_norm_le {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (f : C₀(A,ℝ)) {r : ℝ} (hr : 0≤r) (h : ∀ a,|f a|≤r) : ‖f‖≤r :=
  (f.toBCF.norm_le hr).mpr h

def cfunPull (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) : C₀(A,ℝ) :=
  cfunOfTendsto (fun a => f (j a)) ((cfun_tendsto f).comp hj)

@[simp] theorem cfunPull_apply (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) (a : A) :
    cfunPull j hj f a=f (j a) := rfl

def cfunPullL (j : A → B) (hj : Tendsto j cofinite cofinite) : C₀(B,ℝ) →L[ℝ] C₀(A,ℝ) :=
  LinearMap.mkContinuous
    { toFun := cfunPull j hj
      map_add' := by intro f g; ext a; rfl
      map_smul' := by intro c f; ext a; rfl } 1 (fun f => by
        change ‖cfunPull j hj f‖≤1*‖f‖
        rw [one_mul]
        exact cfun_norm_le _ (norm_nonneg _) (fun a => cfun_norm_apply_le f (j a)))

@[simp] theorem cfunPullL_apply (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) (a : A) :
    cfunPullL j hj f a=f (j a) := rfl

end GeneralC0

theorem tendsto_sumElim_cofinite {A B : Type*} {X : Type*} (f : A → X) (g : B → X)
    (l : Filter X) (hf : Tendsto f cofinite l) (hg : Tendsto g cofinite l) :
    Tendsto (Sum.elim f g) cofinite l := by
  intro s hs
  have h1 : {a | f a∉s}.Finite := hf hs
  have h2 : {b | g b∉s}.Finite := hg hs
  apply ((h1.image Sum.inl).union (h2.image Sum.inr)).subset
  intro x hx
  cases x with
  | inl a => exact Or.inl ⟨a,hx,rfl⟩
  | inr b => exact Or.inr ⟨b,hx,rfl⟩

abbrev BlockC0 := C₀(Label,ℝ)

def inputRows : C0 →L[ℝ] C0 := cfunPullL rowIndex rowIndex_injective.tendsto_cofinite

def inputBlocks : C0 →L[ℝ] BlockC0 := cfunPullL labelIndex labelIndex_injective.tendsto_cofinite

@[simp] theorem inputRows_apply (x : C0) (i : ℕ) : inputRows x i=x (rowIndex i) := rfl
@[simp] theorem inputBlocks_apply (x : C0) (γ : Label) : inputBlocks x γ=x (labelIndex γ) := rfl

def joinInputs (x : C0 × BlockC0) : C0 :=
  cfunOfTendsto (fun k => Sum.elim x.1 x.2 (coordinateEnumeration.symm k))
    ((tendsto_sumElim_cofinite x.1 x.2 (nhds 0) (cfun_tendsto x.1) (cfun_tendsto x.2)).comp
      coordinateEnumeration.symm.injective.tendsto_cofinite)

@[simp] theorem joinInputs_row (x : C0 × BlockC0) (i : ℕ) : joinInputs x (rowIndex i)=x.1 i := by
  change Sum.elim x.1 x.2 (coordinateEnumeration.symm (coordinateEnumeration (Sum.inl i)))=x.1 i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem joinInputs_block (x : C0 × BlockC0) (γ : Label) : joinInputs x (labelIndex γ)=x.2 γ := by
  change Sum.elim x.1 x.2 (coordinateEnumeration.symm (coordinateEnumeration (Sum.inr γ)))=x.2 γ
  rw [Equiv.symm_apply_apply]
  rfl

theorem joinInputs_split (x : C0) : joinInputs (inputRows x,inputBlocks x)=x := by
  ext k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i => exact joinInputs_row _ i
  | inr γ => exact joinInputs_block _ γ

theorem joinInputs_norm (x : C0 × BlockC0) : ‖joinInputs x‖=‖x‖ := by
  apply le_antisymm
  · apply cfun_norm_le _ (norm_nonneg x)
    intro k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => exact (show |joinInputs x (rowIndex i)|≤‖x.1‖ by rw [joinInputs_row]; exact cfun_norm_apply_le _ _).trans (le_max_left _ _)
    | inr γ => exact (show |joinInputs x (labelIndex γ)|≤‖x.2‖ by rw [joinInputs_block]; exact cfun_norm_apply_le _ _).trans (le_max_right _ _)
  · rw [Prod.norm_def]
    apply max_le
    · apply cfun_norm_le _ (norm_nonneg _)
      intro i
      rw [← joinInputs_row x i]
      exact cfun_norm_apply_le _ _
    · apply cfun_norm_le _ (norm_nonneg _)
      intro γ
      rw [← joinInputs_block x γ]
      exact cfun_norm_apply_le _ _

def inputCoordinates : (C0 × BlockC0) ≃ₗᵢ[ℝ] C0 where
  toFun := joinInputs
  invFun := fun x => (inputRows x,inputBlocks x)
  left_inv := by
    intro x
    apply Prod.ext <;> ext k
    · exact joinInputs_row x k
    · exact joinInputs_block x k
  right_inv := joinInputs_split
  map_add' := by
    intro x y
    ext k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => simp only [show coordinateEnumeration (Sum.inl i)=rowIndex i from rfl,joinInputs_row,Prod.fst_add,ZeroAtInftyContinuousMap.add_apply]
    | inr γ => simp only [show coordinateEnumeration (Sum.inr γ)=labelIndex γ from rfl,joinInputs_block,Prod.snd_add,ZeroAtInftyContinuousMap.add_apply]
  map_smul' := by
    intro c x
    ext k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => simp only [show coordinateEnumeration (Sum.inl i)=rowIndex i from rfl,joinInputs_row,ZeroAtInftyContinuousMap.smul_apply]; rfl
    | inr γ => simp only [show coordinateEnumeration (Sum.inr γ)=labelIndex γ from rfl,joinInputs_block,ZeroAtInftyContinuousMap.smul_apply]; rfl
  norm_map' := joinInputs_norm

theorem labelLevel_tendsto : Tendsto Label.level cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton (fun lev => labels_at_level_finite lev)

theorem labelRadius_tendsto (x : C0) : Tendsto (fun γ : Label => localRadius γ.level x) cofinite (nhds 0) :=
  (localRadius_tendsto x).comp labelLevel_tendsto

theorem frozenCorrection_tendsto (W : FrozenWeights) (x : C0) :
    Tendsto (fun γ => frozenCorrection W γ x) cofinite (nhds 0) := by
  apply squeeze_zero_norm (fun γ => frozenCorrection_local W γ x) _
  simpa only [mul_zero] using (labelRadius_tendsto x).const_mul 4

def frozenCorrectionC0 (W : FrozenWeights) (x : C0) : BlockC0 :=
  cfunOfTendsto (fun γ => frozenCorrection W γ x) (frozenCorrection_tendsto W x)

def frozenCorrectionL (W : FrozenWeights) : C0 →L[ℝ] BlockC0 :=
  LinearMap.mkContinuous
    { toFun := frozenCorrectionC0 W
      map_add' := by intro x y; ext γ; exact map_add (frozenCorrection W γ) x y
      map_smul' := by intro c x; ext γ; exact map_smul (frozenCorrection W γ) c x }
    4 (fun x => by
      change ‖frozenCorrectionC0 W x‖≤4*‖x‖
      exact cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg _)) (fun γ => frozenCorrection_bound W γ x))

@[simp] theorem frozenCorrectionL_apply (W : FrozenWeights) (x : C0) (γ : Label) :
    frozenCorrectionL W x γ=frozenCorrection W γ x := rfl

def correctionC0 (s : C0Ball) : BlockC0 := frozenCorrectionL (stateWeights s) s.val

@[simp] theorem correctionC0_apply (s : C0Ball) (γ : Label) : correctionC0 s γ=correction γ s := rfl

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators

section LocalOnto
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem range_mem_nhds_of_approx {f : E → F} {a : E} (S : E ≃L[ℝ] F)
    (s : Set E) (hs : s∈nhds a) (c : ℝ≥0)
    (hc : c<‖(S.symm : F →L[ℝ] E)‖₊⁻¹) (ha : ApproximatesLinearOn f (S : E →L[ℝ] F) s c) :
    Set.range f∈nhds (f a) := by
  have hh := ha.image_mem_nhds S.toNonlinearRightInverse hs (Or.inr hc)
  exact mem_of_superset hh (Set.image_subset_range f s)

theorem surjective_of_punctured_local_onto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial E]
    (f : E → F) {c C : ℝ≥0} (hf : AntilipschitzWith c f) (hLip : LipschitzWith C f)
    (hzero : f 0=0) (hconn : IsPreconnected ({0}ᶜ : Set F))
    (hlocal : ∀ x≠0, Set.range f∈nhds (f x)) : Function.Surjective f := by
  let K : Set F := {0}ᶜ
  let A : Set K := Subtype.val ⁻¹' Set.range f
  let : PreconnectedSpace K := Subtype.preconnectedSpace hconn
  have hclosed : IsClosed A := (hf.isClosed_range hLip.uniformContinuous).preimage continuous_subtype_val
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨x,hx⟩ := hy
    have hx0 : x≠0 := by
      intro hx0
      have he : y.val=0 := by rw [← hx,hx0,hzero]
      exact y.property (by simpa only [Set.mem_singleton_iff] using he)
    have hn : Set.range f∈nhds y.val := by rw [← hx]; exact hlocal x hx0
    exact continuous_subtype_val.continuousAt hn
  have hne : A.Nonempty := by
    obtain ⟨x,hx⟩ := exists_ne (0 : E)
    have hx' : f x≠0 := by intro he; exact hx (hf.injective (he.trans hzero.symm))
    refine ⟨⟨f x,?_⟩,x,rfl⟩
    simpa only [K,Set.mem_compl_iff,Set.mem_singleton_iff] using hx'
  have heq : A=Set.univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hne
  intro y
  by_cases hy : y=0
  · exact ⟨0,hzero.trans hy.symm⟩
  · let yy : K := ⟨y,by simpa only [K,Set.mem_compl_iff,Set.mem_singleton_iff] using hy⟩
    have hh : yy∈A := by rw [heq]; trivial
    exact hh

end LocalOnto
end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def frozenShift (W : FrozenWeights) : C0 →L[ℝ] BlockC0 := inputBlocks+frozenCorrectionL W

@[simp] theorem frozenShift_apply (W : FrozenWeights) (x : C0) (γ : Label) :
    frozenShift W x γ=x (labelIndex γ)+frozenCorrection W γ x := rfl

theorem frozenShift_bound (W : FrozenWeights) (x : C0) : ‖frozenShift W x‖≤5*‖x‖ := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg x))
  intro γ
  rw [frozenShift_apply]
  exact (abs_add_le _ _).trans (by linarith [c0_norm_apply_le x (labelIndex γ),frozenCorrection_bound W γ x])

def blockInclusion : BlockC0 →L[ℝ] C0 :=
  inputCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ C0 BlockC0)

@[simp] theorem blockInclusion_apply (y : BlockC0) (γ : Label) : blockInclusion y (labelIndex γ)=y γ :=
  joinInputs_block (0,y) γ

def outputScalar (W : FrozenWeights) (lev : Level) : BlockC0 →L[ℝ] ℝ :=
  (rowScalar W lev).comp blockInclusion

@[simp] theorem outputScalar_apply (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    outputScalar W lev y=∑ b : Block lev,W.row lev b*y (blockLabel lev b) := by
  simp only [outputScalar,ContinuousLinearMap.comp_apply,rowScalar_apply,blockInput,blockInclusion_apply]

theorem outputScalar_bound (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    |outputScalar W lev y|≤2*‖y‖ := by
  rw [outputScalar_apply]
  exact (abs_finite_dot_le _ _ (fun b => cfun_norm_apply_le y (blockLabel lev b))).trans
    (mul_le_mul_of_nonneg_right (W.row_bound lev) (norm_nonneg y))

theorem outputScalar_tendsto (W : FrozenWeights) (y : BlockC0) :
    Tendsto (fun lev => outputScalar W lev y) cofinite (nhds 0) := by
  apply squeeze_zero_norm (fun lev => rowScalar_local W lev (blockInclusion y)) _
  simpa only [mul_zero] using (localRadius_tendsto (blockInclusion y)).const_mul 2

def firstLevel (i : ℕ) : Level := (i,0)

theorem firstLevel_injective : Function.Injective firstLevel := fun _ _ h => congrArg Prod.fst h

theorem levelSuccessor_injective : Function.Injective levelSuccessor := by
  rintro ⟨i,n⟩ ⟨j,m⟩ h
  simp only [levelSuccessor,Prod.mk.injEq,Nat.add_right_cancel_iff] at h
  exact Prod.ext h.1 h.2

def inverseRows (W : FrozenWeights) (y : BlockC0) : C0 :=
  cfunOfTendsto (fun i => outputScalar W (i,0) y)
    ((outputScalar_tendsto W y).comp firstLevel_injective.tendsto_cofinite)

def inverseBlockFunction (W : FrozenWeights) (y : BlockC0) (γ : Label) : ℝ :=
  y γ-W.vector γ.level ⟨γ.band,γ.tag⟩*(outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)

theorem inverseBlockFunction_tendsto (W : FrozenWeights) (y : BlockC0) :
    Tendsto (inverseBlockFunction W y) cofinite (nhds 0) := by
  have hb : Tendsto (fun γ : Label => outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)
      cofinite (nhds 0) := by
    simpa only [sub_zero,Function.comp_def] using ((outputScalar_tendsto W y).comp labelLevel_tendsto).sub
      ((outputScalar_tendsto W y).comp (levelSuccessor_injective.tendsto_cofinite.comp labelLevel_tendsto))
  have hm : Tendsto (fun γ : Label => W.vector γ.level ⟨γ.band,γ.tag⟩*
      (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)) cofinite (nhds 0) := by
    have hbound (γ : Label) : ‖W.vector γ.level ⟨γ.band,γ.tag⟩*
        (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)‖≤
        |outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y| := by
      simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
        mul_le_mul_of_nonneg_right (W.vector_bound γ.level ⟨γ.band,γ.tag⟩)
          (abs_nonneg (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y))
    exact squeeze_zero_norm hbound (by simpa only [abs_zero] using hb.abs)
  change Tendsto (fun γ : Label => y γ-W.vector γ.level ⟨γ.band,γ.tag⟩*
    (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)) cofinite (nhds 0)
  simpa only [sub_zero] using (cfun_tendsto y).sub hm

def inverseBlocks (W : FrozenWeights) (y : BlockC0) : BlockC0 :=
  cfunOfTendsto (inverseBlockFunction W y) (inverseBlockFunction_tendsto W y)

def frozenInverse (W : FrozenWeights) (y : BlockC0) : C0 := joinInputs (inverseRows W y,inverseBlocks W y)

@[simp] theorem frozenInverse_row (W : FrozenWeights) (y : BlockC0) (i : ℕ) :
    frozenInverse W y (rowIndex i)=outputScalar W (i,0) y := joinInputs_row _ i

@[simp] theorem frozenInverse_block (W : FrozenWeights) (y : BlockC0) (γ : Label) :
    frozenInverse W y (labelIndex γ)=inverseBlockFunction W y γ := joinInputs_block _ γ

theorem frozenInverse_bound (W : FrozenWeights) (y : BlockC0) : ‖frozenInverse W y‖≤5*‖y‖ := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg y))
  intro k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i =>
    have hb := outputScalar_bound W (i,0) y
    change |frozenInverse W y (rowIndex i)|≤_
    rw [frozenInverse_row]
    nlinarith [norm_nonneg y]
  | inr γ =>
    change |frozenInverse W y (labelIndex γ)|≤_
    rw [frozenInverse_block,inverseBlockFunction]
    apply (abs_sub _ _).trans
    have hp : |W.vector γ.level ⟨γ.band,γ.tag⟩*(outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)|≤4*‖y‖ := by
      rw [abs_mul]
      calc
        _ ≤ 1*(|outputScalar W γ.level y|+|outputScalar W (levelSuccessor γ.level) y|) :=
          mul_le_mul (W.vector_bound _ _) (abs_sub _ _) (abs_nonneg _) zero_le_one
        _ ≤ 4*‖y‖ := by linarith [outputScalar_bound W γ.level y,outputScalar_bound W (levelSuccessor γ.level) y]
    linarith [cfun_norm_apply_le y γ]

def frozenInverseL (W : FrozenWeights) : BlockC0 →L[ℝ] C0 :=
  LinearMap.mkContinuous
    { toFun := frozenInverse W
      map_add' := by
        intro y z
        ext k
        obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
        cases a with
        | inl i =>
          change frozenInverse W (y+z) (rowIndex i)=frozenInverse W y (rowIndex i)+frozenInverse W z (rowIndex i)
          simp only [frozenInverse_row,map_add]
        | inr γ =>
          change frozenInverse W (y+z) (labelIndex γ)=frozenInverse W y (labelIndex γ)+frozenInverse W z (labelIndex γ)
          simp only [frozenInverse_block,inverseBlockFunction,ZeroAtInftyContinuousMap.add_apply,map_add]
          ring
      map_smul' := by
        intro c y
        ext k
        obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
        cases a with
        | inl i =>
          change frozenInverse W (c • y) (rowIndex i)=c • frozenInverse W y (rowIndex i)
          simp only [frozenInverse_row,map_smul]
        | inr γ =>
          change frozenInverse W (c • y) (labelIndex γ)=c • frozenInverse W y (labelIndex γ)
          simp only [frozenInverse_block,inverseBlockFunction,ZeroAtInftyContinuousMap.smul_apply,map_smul,smul_eq_mul]
          ring }
    5 (frozenInverse_bound W)

theorem finite_row_cancel {A : Type*} [Fintype A] (w v y : A → ℝ) (h : (∑ a,w a*v a)=1) (b : ℝ) :
    (∑ a,w a*(y a-v a*b))=(∑ a,w a*y a)-b := by
  simp only [mul_sub,← mul_assoc,Finset.sum_sub_distrib,← Finset.sum_mul,h,one_mul]

theorem finite_row_shift {A : Type*} [Fintype A] (w v x : A → ℝ) (h : (∑ a,w a*v a)=1) (b : ℝ) :
    (∑ a,w a*(x a+v a*b))=(∑ a,w a*x a)+b := by
  simp only [mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul,h,one_mul]

theorem rowScalar_frozenInverse (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    rowScalar W lev (frozenInverse W y)=outputScalar W (levelSuccessor lev) y := by
  rw [rowScalar_apply]
  simp only [blockInput,frozenInverse_block,inverseBlockFunction,blockLabel]
  rw [finite_row_cancel _ _ _ (W.pairing lev)]
  have hs := outputScalar_apply W lev y
  simp only [blockLabel] at hs
  rw [← hs]
  ring

theorem previousScalar_frozenInverse (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    previousScalar W lev (frozenInverse W y)=outputScalar W lev y := by
  rcases lev with ⟨i,n⟩
  cases n with
  | zero => exact frozenInverse_row W y i
  | succ n => exact rowScalar_frozenInverse W (i,n) y

theorem frozenShift_frozenInverse (W : FrozenWeights) (y : BlockC0) : frozenShift W (frozenInverse W y)=y := by
  ext γ
  rw [frozenShift_apply,frozenInverse_block,inverseBlockFunction,frozenCorrection_apply,
    previousScalar_frozenInverse,rowScalar_frozenInverse]
  ring

theorem outputScalar_frozenShift (W : FrozenWeights) (lev : Level) (x : C0) :
    outputScalar W lev (frozenShift W x)=previousScalar W lev x := by
  rw [outputScalar_apply]
  simp only [frozenShift_apply,frozenCorrection_apply,blockLabel]
  rw [finite_row_shift _ _ _ (W.pairing lev)]
  rw [rowScalar_apply W lev x]
  simp only [blockInput,blockLabel]
  ring

theorem frozenInverse_frozenShift (W : FrozenWeights) (x : C0) : frozenInverse W (frozenShift W x)=x := by
  ext k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i =>
    change frozenInverse W (frozenShift W x) (rowIndex i)=_
    rw [frozenInverse_row,outputScalar_frozenShift]
    rfl
  | inr γ =>
    change frozenInverse W (frozenShift W x) (labelIndex γ)=_
    rw [frozenInverse_block,inverseBlockFunction,frozenShift_apply,outputScalar_frozenShift,outputScalar_frozenShift,frozenCorrection_apply]
    have he : previousScalar W (levelSuccessor γ.level)=rowScalar W γ.level := by
      rcases γ.level with ⟨i,n⟩
      rfl
    rw [he]
    change x (labelIndex γ)+_ - _=x (labelIndex γ)
    ring

def frozenEquiv (W : FrozenWeights) : C0 ≃L[ℝ] BlockC0 where
  toFun := frozenShift W
  invFun := frozenInverse W
  left_inv := frozenInverse_frozenShift W
  right_inv := frozenShift_frozenInverse W
  map_add' := map_add (frozenShift W)
  map_smul' := map_smul (frozenShift W)
  continuous_toFun := (frozenShift W).continuous
  continuous_invFun := (frozenInverseL W).continuous

theorem frozenShift_lower (W : FrozenWeights) (x : C0) : ‖x‖≤5*‖frozenShift W x‖ := by
  simpa only [frozenInverse_frozenShift] using frozenInverse_bound W (frozenShift W x)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def recomputedShift (x : C0) : BlockC0 := frozenShift (stateWeights (normalizedBall x)) x

@[simp] theorem recomputedShift_zero : recomputedShift 0=0 := map_zero _

theorem WeightError.smul {W V : FrozenWeights} {x : C0} {q : ℝ} (h : WeightError W V x q) (a : ℝ) :
    WeightError W V (a • x) (|a| *q) := by
  constructor
  · intro lev b
    change finiteRadius _ (a • x)*_≤_
    rw [finiteRadius_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.vector lev b) (abs_nonneg a)
  · intro lev
    change finiteRadius _ (a • x)*_≤_
    rw [finiteRadius_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.row lev) (abs_nonneg a)

theorem WeightError.mono {W V : FrozenWeights} {x : C0} {q r : ℝ} (h : WeightError W V x q) (hr : q≤r) :
    WeightError W V x r := ⟨fun lev b => (h.vector lev b).trans hr,fun lev => (h.row lev).trans hr⟩

theorem normalized_error_left (x y : C0) : WeightError (stateWeights (normalizedBall x))
    (mixedWeights (normalizedBall x) (normalizedBall y)) x (2*eta*dist x y) := by
  have hh := (mixed_left_error (normalizedBall x) (normalizedBall y)).smul ‖x‖
  simp only [normalizedBall,Subtype.coe_mk,norm_smul_normalize,abs_of_nonneg (norm_nonneg x)] at hh
  apply hh.mono
  calc
    _ = eta*(‖x‖ * dist (normalize x) (normalize y)) := by rw [Subtype.dist_eq]; ring
    _ ≤ eta*(2*dist x y) := mul_le_mul_of_nonneg_left (normalization_bound x y) eta_pos.le
    _ = _ := by ring

theorem normalized_error_right (x y : C0) : WeightError (stateWeights (normalizedBall y))
    (mixedWeights (normalizedBall x) (normalizedBall y)) y (2*eta*dist x y) := by
  have hh := (mixed_right_error (normalizedBall x) (normalizedBall y)).smul ‖y‖
  simp only [normalizedBall,Subtype.coe_mk,norm_smul_normalize,abs_of_nonneg (norm_nonneg y)] at hh
  apply hh.mono
  calc
    _ = eta*(‖y‖ * dist (normalize y) (normalize x)) := by rw [Subtype.dist_eq,dist_comm]; ring
    _ ≤ eta*(2*dist y x) := mul_le_mul_of_nonneg_left (normalization_bound y x) eta_pos.le
    _ = _ := by rw [dist_comm]; ring

theorem shift_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) : ‖frozenShift W x-frozenShift V x‖≤6*q := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) hq)
  intro γ
  change |frozenShift W x γ-frozenShift V x γ|≤_
  rw [frozenShift_apply,frozenShift_apply,add_sub_add_left_eq_sub]
  exact correction_weight_error hq h γ

theorem recomputed_mixed_left (x y : C0) :
    ‖recomputedShift x-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) x‖≤12*eta*dist x y := by
  have hh := shift_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg) (normalized_error_left x y)
  exact hh.trans (by apply le_of_eq; ring)

theorem recomputed_mixed_right (x y : C0) :
    ‖recomputedShift y-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) y‖≤12*eta*dist x y := by
  have hh := shift_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg) (normalized_error_right x y)
  exact hh.trans (by apply le_of_eq; ring)

theorem recomputed_mixed_approx (x y : C0) :
    ‖recomputedShift x-recomputedShift y-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) (x-y)‖≤24*eta*dist x y := by
  let W := mixedWeights (normalizedBall x) (normalizedBall y)
  have he : recomputedShift x-recomputedShift y-frozenShift W (x-y)=
      (recomputedShift x-frozenShift W x)-(recomputedShift y-frozenShift W y) := by rw [map_sub]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [recomputed_mixed_left x y,recomputed_mixed_right x y])

theorem recomputed_global_bounds (x y : C0) :
    (1/5-24*eta)*dist x y≤dist (recomputedShift x) (recomputedShift y) ∧
    dist (recomputedShift x) (recomputedShift y)≤(5+24*eta)*dist x y := by
  let W := mixedWeights (normalizedBall x) (normalizedBall y)
  let a := recomputedShift x-recomputedShift y
  let b := frozenShift W (x-y)
  have he : ‖a-b‖≤24*eta*dist x y := recomputed_mixed_approx x y
  have hU : ‖b‖≤5*dist x y := by simpa only [dist_eq_norm] using frozenShift_bound W (x-y)
  have hL : dist x y≤5*‖b‖ := by simpa only [dist_eq_norm] using frozenShift_lower W (x-y)
  have hu : ‖a‖≤‖a-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a-b) b
  have hl : ‖b‖≤‖a-b‖+‖a‖ := by simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (b-a) a
  rw [dist_eq_norm (recomputedShift x) (recomputedShift y)]
  change (1/5-24*eta)*dist x y≤‖a‖ ∧ ‖a‖≤(5+24*eta)*dist x y
  constructor <;> nlinarith

theorem recomputed_lipschitz : LipschitzWith (628/125) recomputedShift := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (recomputed_global_bounds x y).2
  norm_num [eta] at hh ⊢
  exact hh

theorem recomputed_antilipschitz : AntilipschitzWith (125/22) recomputedShift := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := (recomputed_global_bounds x y).1
  norm_num [eta] at h ⊢
  nlinarith

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def baseRepresentation (γ : Label) : GeneratedRepresentation concreteBases γ where
  operations := []
  ordered := by simp
  budget := by simpa only [List.map_nil,List.sum_nil] using half_pos (concreteBases.ell_pos (concreteBases.band γ))

theorem baseRepresentation_value (γ : Label) : (baseRepresentation γ).value=correction γ := by
  funext s
  change correctionBase γ (cubeRestrict (correctionCoordinates γ.level) s)=correction γ s
  exact correctionBase_restrict γ s

theorem correction_mem_TClass (γ : Label) : correction γ∈TClass concreteBases 0 :=
  ⟨γ,baseRepresentation γ,Nat.zero_le _,(baseRepresentation_value γ).symm⟩

def correctionDualBound : ℝ≥0 := Classical.choose (TClass_pairing_bound concreteBases 0)

theorem correction_pairing_bound (γ : Label) (m : PreSpace (sourceClasses concreteBases) c0Origin) :
    |pairing C0Ball (correction γ) m|≤correctionDualBound*‖m‖ :=
  Classical.choose_spec (TClass_pairing_bound concreteBases 0) (correction γ) (correction_mem_TClass γ) m

def moleculeCorrection : Molecule C0Ball →ₗ[ℝ] BlockC0 :=
  (Finsupp.linearCombination ℝ correctionC0).comp (MoleculeSpace C0Ball).subtype

theorem moleculeCorrection_apply (m : Molecule C0Ball) (γ : Label) :
    moleculeCorrection m γ=pairing C0Ball (correction γ) m := by
  classical
  simp only [moleculeCorrection,pairing,LinearMap.comp_apply,Submodule.subtype_apply,
    Finsupp.linearCombination_apply,Finsupp.sum]
  induction (m.val.support) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,ZeroAtInftyContinuousMap.add_apply,
      ZeroAtInftyContinuousMap.smul_apply,smul_eq_mul,ih,correctionC0_apply]

def initialCorrection : PreSpace (sourceClasses concreteBases) c0Origin →L[ℝ] BlockC0 :=
  (show PreSpace (sourceClasses concreteBases) c0Origin →ₗ[ℝ] BlockC0 from by unfold PreSpace; exact moleculeCorrection).mkContinuous
    correctionDualBound (fun m => by
      apply cfun_norm_le _ (mul_nonneg correctionDualBound.coe_nonneg (norm_nonneg m))
      intro γ
      change |moleculeCorrection m γ|≤_
      exact (congrArg abs (moleculeCorrection_apply (show Molecule C0Ball from m) γ)).le.trans
        (correction_pairing_bound γ m))

def correctionQ : ConcreteSpace →L[ℝ] BlockC0 :=
  initialCorrection.extend (toTestSpace (sourceClasses concreteBases) c0Origin)

theorem correctionQ_coe (m : PreSpace (sourceClasses concreteBases) c0Origin) :
    correctionQ (toTestSpace (sourceClasses concreteBases) c0Origin m)=moleculeCorrection m :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) m

theorem correctionC0_zero : correctionC0 c0Origin=0 := by
  ext γ
  exact correction_zero γ

theorem correctionQ_zeta (s : C0Ball) :
    correctionQ (zeta (sourceClasses concreteBases) c0Origin s)=correctionC0 s := by
  rw [zeta,correctionQ_coe]
  change moleculeCorrection (molecule s c0Origin)=correctionC0 s
  simp only [moleculeCorrection,molecule,LinearMap.comp_apply,Submodule.subtype_apply,map_sub,
    Finsupp.linearCombination_single,one_smul,correctionC0_zero,sub_zero]

def concreteLift : C0 → ConcreteSpace := radialLift (zeta (sourceClasses concreteBases) c0Origin)

theorem concreteLift_lipschitz : LipschitzWith 3 concreteLift :=
  radialLift_lipschitz _ (zeta_lipschitz _ _) (zeta_base _ _)

theorem concreteLift_zero : concreteLift 0=0 := radialLift_zero _

theorem concreteLift_homogeneous {r : ℝ} (hr : 0≤r) (x : C0) : concreteLift (r • x)=r • concreteLift x :=
  radialLift_homogeneous _ hr x

theorem correctionQ_concreteLift (x : C0) : correctionQ (concreteLift x)=recomputedShift x-inputBlocks x := by
  rw [concreteLift,radialLift,map_smul,correctionQ_zeta]
  change ‖x‖ • (frozenCorrectionL (stateWeights (normalizedBall x)) (normalize x))=_
  rw [← map_smul,norm_smul_normalize]
  change frozenCorrectionL (stateWeights (normalizedBall x)) x=
    (inputBlocks x+frozenCorrectionL (stateWeights (normalizedBall x)) x)-inputBlocks x
  abel

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

section Sparse
variable {A : Type*} [Fintype A]

def sparseC0 (j : A → ℕ) (x : A → ℝ) : C0 :=
  cfunOfTendsto (Function.extend j x 0) (by
    apply tendsto_congr' (show Function.extend j x 0 =ᶠ[cofinite] fun _ => 0 from ?_) |>.mpr
      tendsto_const_nhds
    filter_upwards [(Set.finite_range j).compl_mem_cofinite] with k hk
    exact Function.extend_apply' _ _ _ hk)

@[simp] theorem sparseC0_apply (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) (a : A) :
    sparseC0 j x (j a)=x a := hj.extend_apply _ _ a

theorem sparseC0_outside (j : A → ℕ) (x : A → ℝ) (k : ℕ) (hk : k∉Set.range j) :
    sparseC0 j x k=0 := Function.extend_apply' _ _ _ hk

theorem sparseC0_norm_le (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) : ‖sparseC0 j x‖≤‖x‖ := by
  apply cfun_norm_le _ (norm_nonneg x)
  intro k
  by_cases hk : k∈Set.range j
  · obtain ⟨a,rfl⟩ := hk
    rw [sparseC0_apply j hj]
    exact norm_le_pi_norm x a
  · rw [sparseC0_outside j x k hk,abs_zero]
    exact norm_nonneg x

def sparseC0L (j : A → ℕ) (hj : Function.Injective j) : (A → ℝ) →L[ℝ] C0 :=
  LinearMap.mkContinuous
    { toFun := sparseC0 j
      map_add' := by
        intro x y
        ext k
        by_cases hk : k∈Set.range j
        · obtain ⟨a,rfl⟩ := hk
          simp only [sparseC0_apply j hj,ZeroAtInftyContinuousMap.add_apply,Pi.add_apply]
        · simp only [sparseC0_outside j _ k hk,ZeroAtInftyContinuousMap.add_apply,add_zero]
      map_smul' := by
        intro c x
        ext k
        by_cases hk : k∈Set.range j
        · obtain ⟨a,rfl⟩ := hk
          simp only [sparseC0_apply j hj,ZeroAtInftyContinuousMap.smul_apply,Pi.smul_apply,RingHom.id_apply]
        · simp only [sparseC0_outside j _ k hk,ZeroAtInftyContinuousMap.smul_apply,smul_zero] }
    1 (fun x => by
      change ‖sparseC0 j x‖≤1*‖x‖
      simpa only [one_mul] using sparseC0_norm_le j hj x)

theorem sparseC0_norm (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) : ‖sparseC0 j x‖=‖x‖ := by
  apply le_antisymm (sparseC0_norm_le j hj x)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro a
  rw [← sparseC0_apply j hj x a]
  exact cfun_norm_apply_le _ _

def sparseC0Isometry (j : A → ℕ) (hj : Function.Injective j) : (A → ℝ) →ₗᵢ[ℝ] C0 where
  toLinearMap := (sparseC0L j hj).toLinearMap
  norm_map' := sparseC0_norm j hj

end Sparse

abbrev FLevel (N : ℕ) := Fin (N+1) × Fin (N+1)
abbrev FLabel (N : ℕ) := (lev : FLevel N) × Block (lev.1.val,lev.2.val)
abbrev FCoord (N : ℕ) := Sum (Fin (N+1)) (FLabel N)
abbrev FInput (N : ℕ) := FCoord N → ℝ

def fLabel {N : ℕ} (γ : FLabel N) : Label := blockLabel (γ.1.1.val,γ.1.2.val) γ.2

theorem fLabel_injective (N : ℕ) : Function.Injective (@fLabel N) := by
  rintro ⟨⟨i,n⟩,b⟩ ⟨⟨i',n'⟩,b'⟩ he
  have hl := congrArg Label.level he
  change (i.val,n.val)=(i'.val,n'.val) at hl
  have hi : i=i' := Fin.ext (Prod.mk.inj hl).1
  have hn : n=n' := Fin.ext (Prod.mk.inj hl).2
  subst i'; subst n'
  have hb : b=b' := blockLabel_injective _ he
  subst b'
  rfl

def fCoord {N : ℕ} : FCoord N → ℕ := Sum.elim (fun i => rowIndex i.val) (fun γ => labelIndex (fLabel γ))

theorem fCoord_injective (N : ℕ) : Function.Injective (@fCoord N) := by
  rintro (i|γ) (j|δ) he
  · exact congrArg Sum.inl (Fin.ext (rowIndex_injective he))
  · exact (rowIndex_ne_labelIndex i.val (fLabel δ) he).elim
  · exact (rowIndex_ne_labelIndex j.val (fLabel γ) he.symm).elim
  · exact congrArg Sum.inr (fLabel_injective N (labelIndex_injective he))

def finiteEmbed (N : ℕ) : FInput N →ₗᵢ[ℝ] C0 := sparseC0Isometry fCoord (fCoord_injective N)

@[simp] theorem finiteEmbed_apply {N : ℕ} (x : FInput N) (a : FCoord N) :
    finiteEmbed N x (fCoord a)=x a := sparseC0_apply _ (fCoord_injective N) x a

@[simp] theorem finiteEmbed_row {N : ℕ} (x : FInput N) (i : Fin (N+1)) :
    finiteEmbed N x (rowIndex i.val)=x (.inl i) := finiteEmbed_apply x (.inl i)

@[simp] theorem finiteEmbed_block {N : ℕ} (x : FInput N) (l : FLevel N) (b : Block (l.1.val,l.2.val)) :
    finiteEmbed N x (labelIndex (blockLabel (l.1.val,l.2.val) b))=x (.inr ⟨l,b⟩) := finiteEmbed_apply x (.inr ⟨l,b⟩)

theorem finiteEmbed_row_outside {N : ℕ} (x : FInput N) (i : ℕ) (hi : N < i) : finiteEmbed N x (rowIndex i)=0 := by
  apply sparseC0_outside
  rintro ⟨a,ha⟩
  cases a with
  | inl a => have he := rowIndex_injective ha; have := a.isLt; omega
  | inr γ => exact rowIndex_ne_labelIndex i (fLabel γ) ha.symm

theorem finiteEmbed_block_outside {N : ℕ} (x : FInput N) (γ : Label)
    (hγ : N < γ.level.1 ∨ N < γ.level.2) : finiteEmbed N x (labelIndex γ)=0 := by
  apply sparseC0_outside
  rintro ⟨a,ha⟩
  cases a with
  | inl i => exact rowIndex_ne_labelIndex i.val γ ha
  | inr δ =>
    have he := congrArg Label.level (labelIndex_injective ha)
    change (δ.1.1.val,δ.1.2.val)=γ.level at he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    have := δ.1.1.isLt
    have := δ.1.2.isLt
    omega

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

def finiteRow (W : FrozenWeights) (l : FLevel N) (x : FInput N) : ℝ :=
  ∑ b : Block (l.1.val,l.2.val), W.row (l.1.val,l.2.val) b*x (.inr ⟨l,b⟩)

theorem finiteRow_eq (W : FrozenWeights) (l : FLevel N) (x : FInput N) :
    finiteRow W l x=rowScalar W (l.1.val,l.2.val) (finiteEmbed N x) := by
  rw [rowScalar_apply]
  simp only [finiteRow,blockInput,finiteEmbed_block]

theorem finiteRow_bound (W : FrozenWeights) (l : FLevel N) (x : FInput N) : |finiteRow W l x|≤2*‖x‖ := by
  unfold finiteRow
  exact (abs_finite_dot_le _ _ (fun b => norm_le_pi_norm x (.inr ⟨l,b⟩))).trans
    (mul_le_mul_of_nonneg_right (W.row_bound _) (norm_nonneg x))

def finPred (n : Fin (N+1)) : Fin (N+1) := ⟨n.val-1,(Nat.sub_le _ _).trans_lt n.isLt⟩

def finitePrev (W : FrozenWeights) (l : FLevel N) (x : FInput N) : ℝ :=
  if l.2.val=0 then x (.inl l.1) else finiteRow W (l.1,finPred l.2) x

theorem finitePrev_eq (W : FrozenWeights) (l : FLevel N) (x : FInput N) :
    finitePrev W l x=previousScalar W (l.1.val,l.2.val) (finiteEmbed N x) := by
  rcases l with ⟨i,⟨n,hn⟩⟩
  cases n with
  | zero => simp only [finitePrev,↓reduceIte,previousScalar,c0Eval_apply,finiteEmbed_row]
  | succ n =>
    simp only [finitePrev,Nat.succ_ne_zero,↓reduceIte,finiteRow_eq,finPred,Nat.add_sub_cancel,previousScalar]

def finiteFrozenFunction (W : FrozenWeights) (x : FInput N) : FInput N := fun a =>
  match a with
  | .inl i => finiteRow W (i,Fin.last N) x
  | .inr ⟨l,b⟩ => x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)

@[simp] theorem finiteFrozen_row (W : FrozenWeights) (x : FInput N) (i : Fin (N+1)) :
    finiteFrozenFunction W x (.inl i)=finiteRow W (i,Fin.last N) x := rfl

@[simp] theorem finiteFrozen_block (W : FrozenWeights) (x : FInput N) (γ : FLabel N) :
    finiteFrozenFunction W x (.inr γ)=frozenShift W (finiteEmbed N x) (fLabel γ) := by
  rcases γ with ⟨l,b⟩
  rw [frozenShift_apply,frozenCorrection_apply]
  change x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)=
    finiteEmbed N x (labelIndex (blockLabel (l.1.val,l.2.val) b))+W.vector (l.1.val,l.2.val) b*
      (previousScalar W (l.1.val,l.2.val) (finiteEmbed N x)-rowScalar W (l.1.val,l.2.val) (finiteEmbed N x))
  rw [finiteEmbed_block,finitePrev_eq,finiteRow_eq]

theorem finiteFrozen_bound (W : FrozenWeights) (x : FInput N) : ‖finiteFrozenFunction W x‖≤5*‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg x))).mpr
  rintro (i|γ)
  · change |finiteRow W (i,Fin.last N) x|≤_
    exact (finiteRow_bound W _ x).trans (by nlinarith [norm_nonneg x])
  · rw [finiteFrozen_block]
    exact (cfun_norm_apply_le _ _).trans ((frozenShift_bound W (finiteEmbed N x)).trans_eq (by rw [LinearIsometry.norm_map]))

def finiteFrozen (N : ℕ) (W : FrozenWeights) : FInput N →L[ℝ] FInput N :=
  LinearMap.mkContinuous
    { toFun := finiteFrozenFunction W
      map_add' := by
        intro x y
        funext a
        cases a with
        | inl i => simp only [finiteFrozen_row,finiteRow_eq,map_add,Pi.add_apply]
        | inr γ => simp only [finiteFrozen_block,map_add,ZeroAtInftyContinuousMap.add_apply,Pi.add_apply]
      map_smul' := by
        intro c x
        funext a
        cases a with
        | inl i => simp only [finiteFrozen_row,finiteRow_eq,map_smul,Pi.smul_apply,RingHom.id_apply]
        | inr γ => simp only [finiteFrozen_block,map_smul,ZeroAtInftyContinuousMap.smul_apply,Pi.smul_apply,RingHom.id_apply] }
    5 (finiteFrozen_bound W)

def finiteNext (W : FrozenWeights) (l : FLevel N) (y : FInput N) : ℝ :=
  if h : l.2.val<N then finiteRow W (l.1,⟨l.2.val+1,by omega⟩) y else y (.inl l.1)

theorem finiteNext_bound (W : FrozenWeights) (l : FLevel N) (y : FInput N) : |finiteNext W l y|≤2*‖y‖ := by
  unfold finiteNext
  split_ifs
  · exact finiteRow_bound W _ y
  · exact (norm_le_pi_norm y (.inl l.1)).trans (by nlinarith [norm_nonneg y])

def finiteInverseFunction (W : FrozenWeights) (y : FInput N) : FInput N := fun a =>
  match a with
  | .inl i => finiteRow W (i,0) y
  | .inr ⟨l,b⟩ => y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)

@[simp] theorem finiteInverse_row (W : FrozenWeights) (y : FInput N) (i : Fin (N+1)) :
    finiteInverseFunction W y (.inl i)=finiteRow W (i,0) y := rfl

@[simp] theorem finiteInverse_block (W : FrozenWeights) (y : FInput N) (l : FLevel N) (b : Block (l.1.val,l.2.val)) :
    finiteInverseFunction W y (.inr ⟨l,b⟩)=y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y) := rfl

theorem finiteInverse_bound (W : FrozenWeights) (y : FInput N) : ‖finiteInverseFunction W y‖≤5*‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg y))).mpr
  rintro (i|⟨l,b⟩)
  · exact (finiteRow_bound W _ y).trans (by nlinarith [norm_nonneg y])
  · change |y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)|≤_
    apply (abs_sub _ _).trans
    have hp : |W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)|≤4*‖y‖ := by
      rw [abs_mul]
      calc
        _ ≤ 1*(|finiteRow W l y|+|finiteNext W l y|) :=
          mul_le_mul (W.vector_bound _ _) (abs_sub _ _) (abs_nonneg _) zero_le_one
        _ ≤ 4*‖y‖ := by linarith [finiteRow_bound W l y,finiteNext_bound W l y]
    have hy : |y (.inr ⟨l,b⟩)|≤‖y‖ := norm_le_pi_norm y _
    linarith

theorem finiteRow_inverse (W : FrozenWeights) (y : FInput N) (l : FLevel N) :
    finiteRow W l (finiteInverseFunction W y)=finiteNext W l y := by
  unfold finiteRow
  simp only [finiteInverse_block]
  rw [finite_row_cancel _ _ _ (W.pairing _)]
  change finiteRow W l y-(finiteRow W l y-finiteNext W l y)=_
  ring

theorem finitePrev_inverse (W : FrozenWeights) (y : FInput N) (l : FLevel N) :
    finitePrev W l (finiteInverseFunction W y)=finiteRow W l y := by
  unfold finitePrev
  split_ifs with hn
  · have he : l.2=0 := Fin.ext hn
    rcases l with ⟨i,n⟩
    dsimp at he
    subst n
    rfl
  · rw [finiteRow_inverse]
    have hp : (finPred l.2).val<N := by have := l.2.isLt; dsimp [finPred]; omega
    simp only [finiteNext,hp,↓reduceDIte]
    congr 2
    apply Fin.ext
    dsimp [finPred]
    omega

theorem finiteFrozen_inverse (W : FrozenWeights) (y : FInput N) : finiteFrozen N W (finiteInverseFunction W y)=y := by
  funext a
  cases a with
  | inl i =>
    change finiteRow W (i,Fin.last N) (finiteInverseFunction W y)=_
    rw [finiteRow_inverse]
    simp only [finiteNext,Fin.val_last,lt_self_iff_false,↓reduceDIte]
  | inr γ =>
    rcases γ with ⟨l,b⟩
    change finiteInverseFunction W y (.inr ⟨l,b⟩)+_=_
    rw [finiteInverse_block,finitePrev_inverse,finiteRow_inverse]
    ring

theorem finiteRow_frozen (W : FrozenWeights) (x : FInput N) (l : FLevel N) :
    finiteRow W l (finiteFrozen N W x)=finitePrev W l x := by
  unfold finiteRow
  change (∑ b : Block (l.1.val,l.2.val), W.row (l.1.val,l.2.val) b*
    (x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)))=_
  rw [finite_row_shift _ _ _ (W.pairing _)]
  change finiteRow W l x+(finitePrev W l x-finiteRow W l x)=_
  ring

theorem finiteNext_frozen (W : FrozenWeights) (x : FInput N) (l : FLevel N) :
    finiteNext W l (finiteFrozen N W x)=finiteRow W l x := by
  unfold finiteNext
  split_ifs with hn
  · rw [finiteRow_frozen]
    simp only [finitePrev,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]
    congr 2
  · have he : l.2=Fin.last N := Fin.ext (by have := l.2.isLt; simp only [Fin.val_last]; omega)
    change finiteRow W (l.1,Fin.last N) x=finiteRow W l x
    rw [← he]

theorem finiteInverse_frozen (W : FrozenWeights) (x : FInput N) : finiteInverseFunction W (finiteFrozen N W x)=x := by
  funext a
  cases a with
  | inl i =>
    rw [finiteInverse_row,finiteRow_frozen]
    rfl
  | inr γ =>
    rcases γ with ⟨l,b⟩
    rw [finiteInverse_block,finiteRow_frozen,finiteNext_frozen]
    change x (.inr ⟨l,b⟩)+_ - _=x (.inr ⟨l,b⟩)
    ring

def finiteEquiv (N : ℕ) (W : FrozenWeights) : FInput N ≃L[ℝ] FInput N :=
  ContinuousLinearEquiv.ofBijective (finiteFrozen N W)
    (LinearMap.ker_eq_bot.mpr (fun x y h => by
      change finiteFrozen N W x=finiteFrozen N W y at h
      simpa only [finiteInverse_frozen] using congrArg (finiteInverseFunction W) h))
    (LinearMap.range_eq_top.mpr (fun y => ⟨finiteInverseFunction W y,finiteFrozen_inverse W y⟩))

theorem finiteEquiv_symm_apply (N : ℕ) (W : FrozenWeights) (y : FInput N) :
    (finiteEquiv N W).symm y=finiteInverseFunction W y := by
  apply (finiteEquiv N W).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (finiteFrozen_inverse W y).symm

theorem finiteFrozen_lower (W : FrozenWeights) (x : FInput N) : ‖x‖≤5*‖finiteFrozen N W x‖ := by
  simpa only [finiteInverse_frozen] using finiteInverse_bound W (finiteFrozen N W x)

theorem finiteEquiv_symm_norm (N : ℕ) (W : FrozenWeights) : ‖((finiteEquiv N W).symm : FInput N →L[ℝ] FInput N)‖≤5 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  rw [ContinuousLinearEquiv.coe_coe,finiteEquiv_symm_apply]
  exact finiteInverse_bound W y

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

def finiteRecomputed (N : ℕ) (x : FInput N) : FInput N :=
  finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x))) x

@[simp] theorem finiteRecomputed_zero (N : ℕ) : finiteRecomputed N 0=0 := map_zero _

theorem finiteFrozen_weight_error {W V : FrozenWeights} {x : FInput N} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V (finiteEmbed N x) q) :
    ‖finiteFrozen N W x-finiteFrozen N V x‖≤6*q := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hq)).mpr
  rintro (i|γ)
  · change |finiteRow W (i,Fin.last N) x-finiteRow V (i,Fin.last N) x|≤_
    rw [finiteRow_eq,finiteRow_eq]
    exact (rowScalar_weight_error W V _ _ (h.row _)).trans (by linarith)
  · change |finiteFrozenFunction W x (.inr γ)-finiteFrozenFunction V x (.inr γ)|≤_
    rw [finiteFrozen_block,finiteFrozen_block]
    exact (cfun_norm_apply_le (frozenShift W (finiteEmbed N x)-frozenShift V (finiteEmbed N x)) (fLabel γ)).trans
      (shift_weight_error hq h)

theorem finiteRecomputed_mixed_left (x y : FInput N) :
    ‖finiteRecomputed N x-finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) x‖≤12*eta*dist x y := by
  have hh := finiteFrozen_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg)
    (normalized_error_left (finiteEmbed N x) (finiteEmbed N y))
  rw [LinearIsometry.dist_map] at hh
  exact hh.trans (by apply le_of_eq; ring)

theorem finiteRecomputed_mixed_right (x y : FInput N) :
    ‖finiteRecomputed N y-finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) y‖≤12*eta*dist x y := by
  have hh := finiteFrozen_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg)
    (normalized_error_right (finiteEmbed N x) (finiteEmbed N y))
  rw [LinearIsometry.dist_map] at hh
  exact hh.trans (by apply le_of_eq; ring)

theorem finiteRecomputed_mixed_approx (x y : FInput N) :
    ‖finiteRecomputed N x-finiteRecomputed N y-
      finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) (x-y)‖≤24*eta*dist x y := by
  let W := mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))
  have he : finiteRecomputed N x-finiteRecomputed N y-finiteFrozen N W (x-y)=
      (finiteRecomputed N x-finiteFrozen N W x)-(finiteRecomputed N y-finiteFrozen N W y) := by rw [map_sub]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [finiteRecomputed_mixed_left x y,finiteRecomputed_mixed_right x y])

theorem fiveBounds_of_error {E : Type*} [NormedAddCommGroup E] {a b : E} {d e : ℝ}
    (he : ‖a-b‖≤e*d) (hU : ‖b‖≤5*d) (hL : d≤5*‖b‖) :
    (1/5-e)*d≤‖a‖ ∧ ‖a‖≤(5+e)*d := by
  have hu : ‖a‖≤‖a-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a-b) b
  have hl : ‖b‖≤‖a-b‖+‖a‖ := by simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (b-a) a
  constructor <;> nlinarith

theorem finiteRecomputed_global_bounds (x y : FInput N) :
    (1/5-24*eta)*dist x y≤dist (finiteRecomputed N x) (finiteRecomputed N y) ∧
    dist (finiteRecomputed N x) (finiteRecomputed N y)≤(5+24*eta)*dist x y := by
  let W := mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))
  let a := finiteRecomputed N x-finiteRecomputed N y
  let b := finiteFrozen N W (x-y)
  have he : ‖a-b‖≤24*eta*dist x y := finiteRecomputed_mixed_approx x y
  have hU : ‖b‖≤5*dist x y := by
    change ‖finiteFrozenFunction W (x-y)‖≤5*dist x y
    rw [dist_eq_norm]
    exact finiteFrozen_bound W (x-y)
  have hL : dist x y≤5*‖b‖ := by simpa only [dist_eq_norm] using finiteFrozen_lower W (x-y)
  rw [dist_eq_norm (finiteRecomputed N x) (finiteRecomputed N y)]
  exact fiveBounds_of_error he hU hL

theorem finiteRecomputed_lipschitz (N : ℕ) : LipschitzWith (628/125) (finiteRecomputed N) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (finiteRecomputed_global_bounds x y).2
  norm_num [eta] at hh ⊢
  exact hh

theorem finiteRecomputed_antilipschitz (N : ℕ) : AntilipschitzWith (125/22) (finiteRecomputed N) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := (finiteRecomputed_global_bounds x y).1
  norm_num [eta] at h ⊢
  nlinarith

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

section FiniteOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_operator_norm_le_columns (T : (A → ℝ) →L[ℝ] E) :
    ‖T‖≤∑ a,‖T (Pi.single a 1)‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  intro x
  have he : (∑ a, x a • Pi.single a (1 : ℝ))=x := by
    ext b
    simp [Pi.single_apply]
  have hEq : T x=∑ a,x a • T (Pi.single a 1) := by
    simpa only [map_sum,map_smul] using congrArg T he.symm
  rw [hEq]
  calc
    _ ≤ ∑ a, ‖x a • T (Pi.single a 1)‖ := norm_sum_le _ _
    _ = ∑ a, ‖T (Pi.single a 1)‖*‖x a‖ := by simp only [norm_smul,mul_comm]
    _ ≤ ∑ a, ‖T (Pi.single a 1)‖*‖x‖ := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm x a) (norm_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

theorem tendsto_finiteOperator_of_columns {X : Type*} {l : Filter X}
    (T : X → (A → ℝ) →L[ℝ] E) (S : (A → ℝ) →L[ℝ] E)
    (h : ∀ a, Tendsto (fun z => T z (Pi.single a 1)) l (nhds (S (Pi.single a 1)))) :
    Tendsto T l (nhds S) := by
  classical
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun z => norm_nonneg _) (fun z => finite_operator_norm_le_columns (T z-S))
  have hh : Tendsto (fun z => ∑ a, ‖T z (Pi.single a 1)-S (Pi.single a 1)‖) l (nhds (∑ a : A, (0 : ℝ))) :=
    tendsto_finsetSum _ (fun a _ => tendsto_iff_norm_sub_tendsto_zero.mp (h a))
  simpa only [sub_apply,Finset.sum_const_zero] using hh

end FiniteOperators

theorem diagonal_neighborhood {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup G] (q : X → Y) {x : X} (hq : ContinuousAt q x)
    (A : Y × Y → G) (g : G) (hA : Tendsto A (nhds (q x,q x)) (nhds g))
    {ε : ℝ} (hε : 0<ε) :
    ∃ s : Set X, s∈nhds x ∧ ∀ y∈s, ∀ z∈s, ‖A (q y,q z)-g‖<ε := by
  have hp : Tendsto (fun p : X × X => (q p.1,q p.2)) (nhds (x,x)) (nhds (q x,q x)) :=
    (hq.comp continuous_fst.continuousAt).prodMk (hq.comp continuous_snd.continuousAt)
  have ht := hA.comp hp
  have he : {p : X × X | ‖A (q p.1,q p.2)-g‖<ε}∈nhds (x,x) := by
    have hh := Metric.tendsto_nhds.mp ht ε hε
    change ∀ᶠ p : X × X in nhds (x,x), ‖A (q p.1,q p.2)-g‖<ε
    filter_upwards [hh] with p h
    simpa only [Function.comp_def,dist_eq_norm] using h
  rw [nhds_prod_eq] at he
  obtain ⟨s,hs,t,ht,hst⟩ := Filter.mem_prod_iff.mp he
  exact ⟨s∩t,inter_mem hs ht,fun y hy z hz => @hst (y,z) ⟨hy.1,hz.2⟩⟩

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem mixed_vector_tendsto (s : C0Ball) (lev : Level) (b : Block lev) :
    Tendsto (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).vector lev b)
      (nhds (s,s)) (nhds ((stateWeights s).vector lev b)) := by
  classical
  have h1 : Tendsto (fun p : C0Ball × C0Ball => blockVector lev p.1 b) (nhds (s,s)) (nhds (blockVector lev s b)) :=
    ((blockVector_continuous lev b).comp continuous_fst).continuousAt
  have h2 : Tendsto (fun p : C0Ball × C0Ball => blockVector lev p.2 b) (nhds (s,s)) (nhds (blockVector lev s b)) :=
    ((blockVector_continuous lev b).comp continuous_snd).continuousAt
  have he : (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).vector lev b)=
      (fun p : C0Ball × C0Ball => if localRadius lev p.2.val≤localRadius lev p.1.val then blockVector lev p.1 b else blockVector lev p.2 b) := by
    funext p
    dsimp only [mixedWeights,mixedState]
    split_ifs <;> rfl
  rw [he]
  exact h1.if' h2

theorem mixed_row_tendsto (s : C0Ball) (lev : Level) (b : Block lev) :
    Tendsto (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).row lev b)
      (nhds (s,s)) (nhds ((stateWeights s).row lev b)) := by
  classical
  have h1 : Tendsto (fun p : C0Ball × C0Ball => blockRow lev p.1 b) (nhds (s,s)) (nhds (blockRow lev s b)) :=
    ((blockRow_continuous lev b).comp continuous_fst).continuousAt
  have h2 : Tendsto (fun p : C0Ball × C0Ball => blockRow lev p.2 b) (nhds (s,s)) (nhds (blockRow lev s b)) :=
    ((blockRow_continuous lev b).comp continuous_snd).continuousAt
  have he : (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).row lev b)=
      (fun p : C0Ball × C0Ball => if localRadius lev p.2.val≤localRadius lev p.1.val then blockRow lev p.1 b else blockRow lev p.2 b) := by
    funext p
    dsimp only [mixedWeights,mixedState]
    split_ifs <;> rfl
  rw [he]
  exact h1.if' h2

variable {N : ℕ}

theorem finiteRow_mixed_tendsto (s : C0Ball) (l : FLevel N) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finiteRow (mixedWeights p.1 p.2) l x)
      (nhds (s,s)) (nhds (finiteRow (stateWeights s) l x)) := by
  exact tendsto_finsetSum _ (fun b _ => (mixed_row_tendsto s _ b).mul_const _)

theorem finitePrev_mixed_tendsto (s : C0Ball) (l : FLevel N) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finitePrev (mixedWeights p.1 p.2) l x)
      (nhds (s,s)) (nhds (finitePrev (stateWeights s) l x)) := by
  unfold finitePrev
  split_ifs
  · exact tendsto_const_nhds
  · exact finiteRow_mixed_tendsto s _ x

theorem finiteFrozen_mixed_apply_tendsto (s : C0Ball) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finiteFrozen N (mixedWeights p.1 p.2) x)
      (nhds (s,s)) (nhds (finiteFrozen N (stateWeights s) x)) := by
  apply tendsto_pi_nhds.mpr
  rintro (i|⟨l,b⟩)
  · exact finiteRow_mixed_tendsto s (i,Fin.last N) x
  · exact tendsto_const_nhds.add ((mixed_vector_tendsto s _ b).mul
      ((finitePrev_mixed_tendsto s l x).sub (finiteRow_mixed_tendsto s l x)))

theorem finiteFrozen_mixed_tendsto (N : ℕ) (s : C0Ball) :
    Tendsto (fun p : C0Ball × C0Ball => finiteFrozen N (mixedWeights p.1 p.2))
      (nhds (s,s)) (nhds (finiteFrozen N (stateWeights s))) := by
  classical
  exact tendsto_finiteOperator_of_columns _ _ (fun a => finiteFrozen_mixed_apply_tendsto s _)

theorem normalizedBall_continuousAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x≠0) : ContinuousAt (@normalizedBall E _ _ ) x := by
  apply tendsto_subtype_rng.mpr
  exact (continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

theorem finite_normalized_continuousAt {x : FInput N} (hx : x≠0) :
    ContinuousAt (fun y => normalizedBall (finiteEmbed N y)) x := by
  have he : finiteEmbed N x≠0 := fun he => hx ((finiteEmbed N).injective (he.trans (map_zero _).symm))
  exact (normalizedBall_continuousAt he).comp (finiteEmbed N).continuous.continuousAt

theorem finite_mixed_operator_near {x : FInput N} (hx : x≠0) :
    ∃ s : Set (FInput N), s∈nhds x ∧ ∀ y∈s, ∀ z∈s,
      ‖finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N y)) (normalizedBall (finiteEmbed N z)))-
        finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x)))‖ < 1/20 := by
  exact diagonal_neighborhood (fun y => normalizedBall (finiteEmbed N y))
    (finite_normalized_continuousAt hx) (fun p => finiteFrozen N (mixedWeights p.1 p.2))
    (finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x))))
    (finiteFrozen_mixed_tendsto N _) (by norm_num)

theorem finiteRecomputed_local_onto {x : FInput N} (hx : x≠0) :
    Set.range (finiteRecomputed N)∈nhds (finiteRecomputed N x) := by
  let W := stateWeights (normalizedBall (finiteEmbed N x))
  let S := finiteEquiv N W
  obtain ⟨s,hs,hclose⟩ := finite_mixed_operator_near hx
  apply range_mem_nhds_of_approx S s hs (1/10)
  · have hh : ‖(S.symm : FInput N →L[ℝ] FInput N)‖₊≤5 := by
      exact_mod_cast finiteEquiv_symm_norm N W
    have hpos : 0<‖(S.symm : FInput N →L[ℝ] FInput N)‖₊ := by
      exact S.nnnorm_symm_pos
    rw [inv_eq_one_div,lt_div_iff₀ hpos]
    calc (1/10 : ℝ≥0)*‖(S.symm : FInput N →L[ℝ] FInput N)‖₊ ≤ (1/10)*5 := mul_le_mul_of_nonneg_left hh (by positivity)
         _ < 1 := by norm_num
  · intro y hy z hz
    let V := mixedWeights (normalizedBall (finiteEmbed N y)) (normalizedBall (finiteEmbed N z))
    have he : ‖finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N V (y-z)‖≤24*eta*dist y z :=
      finiteRecomputed_mixed_approx y z
    have hd : ‖(finiteFrozen N V-finiteFrozen N W) (y-z)‖≤(1/20)*dist y z := by
      apply ((finiteFrozen N V-finiteFrozen N W).le_opNorm (y-z)).trans
      rw [← dist_eq_norm y z]
      exact mul_le_mul_of_nonneg_right (hclose y hy z hz).le dist_nonneg
    have hid : finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N W (y-z)=
      (finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N V (y-z))+
        (finiteFrozen N V-finiteFrozen N W) (y-z) := by
      rw [sub_apply]
      abel
    change ‖finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N W (y-z)‖≤(1/10 : ℝ≥0)*‖y-z‖
    rw [hid]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ 24*eta*dist y z+(1/20)*dist y z := add_le_add he hd
      _ = (24*eta+1/20)*dist y z := by ring
      _ ≤ (1/10)*dist y z := mul_le_mul_of_nonneg_right (by norm_num [eta]) dist_nonneg
      _ = _ := by norm_num only [NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]; rw [dist_eq_norm]

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem finiteRecomputed_surjective (N : ℕ) (hN : 0 < N) : Function.Surjective (finiteRecomputed N) := by
  apply surjective_of_punctured_local_onto (finiteRecomputed N)
    (finiteRecomputed_antilipschitz N) (finiteRecomputed_lipschitz N) (finiteRecomputed_zero N)
  · apply (isConnected_compl_singleton_of_one_lt_rank (E := FInput N) _ 0).isPreconnected
    change 1 < Module.rank ℝ (FCoord N → ℝ)
    rw [rank_fun']
    have hh : 1 < Fintype.card (FCoord N) := by
      change 1 < Fintype.card (Sum (Fin (N+1)) (FLabel N))
      rw [Fintype.card_sum,Fintype.card_fin]
      omega
    exact_mod_cast hh
  · exact fun x hx => finiteRecomputed_local_onto hx

variable {N : ℕ}

def finiteTarget (N : ℕ) (y : BlockC0) : FInput N := Sum.elim (fun _ => 0) (fun γ => y (fLabel γ))

theorem finiteRecomputed_block (x : FInput N) (γ : FLabel N) :
    finiteRecomputed N x (.inr γ)=recomputedShift (finiteEmbed N x) (fLabel γ) :=
  finiteFrozen_block _ x γ

theorem finiteRecomputed_row (x : FInput N) (i : Fin (N+1)) :
    finiteRecomputed N x (.inl i)=
      rowScalar (stateWeights (normalizedBall (finiteEmbed N x))) (i.val,N) (finiteEmbed N x) :=
  finiteRow_eq _ (i,Fin.last N) x

theorem finiteEmbed_rowScalar_outside (W : FrozenWeights) (x : FInput N) (lev : Level)
    (hl : N < lev.1 ∨ N < lev.2) : rowScalar W lev (finiteEmbed N x)=0 := by
  classical
  rw [rowScalar_apply]
  apply Finset.sum_eq_zero
  intro b hb
  change W.row lev b*finiteEmbed N x (labelIndex (blockLabel lev b))=0
  rw [finiteEmbed_block_outside x (blockLabel lev b) hl,mul_zero]

theorem finite_solution_gives_infinite (y : BlockC0) (x : FInput N)
    (hy : ∀ γ : Label, N < γ.level.1 ∨ N < γ.level.2 → y γ=0)
    (hx : finiteRecomputed N x=finiteTarget N y) : recomputedShift (finiteEmbed N x)=y := by
  let W := stateWeights (normalizedBall (finiteEmbed N x))
  have hterminal (i : ℕ) (hi : i≤N) : rowScalar W (i,N) (finiteEmbed N x)=0 := by
    have hh := congrFun hx (.inl ⟨i,by omega⟩)
    rw [finiteRecomputed_row] at hh
    exact hh
  ext γ
  by_cases hγ : γ.level.1≤N ∧ γ.level.2≤N
  · let l : FLevel N := (⟨γ.level.1,by omega⟩,⟨γ.level.2,by omega⟩)
    let b : Block (l.1.val,l.2.val) := ⟨γ.band,γ.tag⟩
    let δ : FLabel N := ⟨l,b⟩
    have he : fLabel δ=γ := by cases γ; rfl
    have hh := congrFun hx (.inr δ)
    rw [finiteRecomputed_block] at hh
    change recomputedShift (finiteEmbed N x) (fLabel δ)=y (fLabel δ) at hh
    simpa only [he] using hh
  · have hout : N < γ.level.1 ∨ N < γ.level.2 := by omega
    rw [hy γ hout]
    change frozenShift W (finiteEmbed N x) γ=0
    rw [frozenShift_apply,finiteEmbed_block_outside x γ hout,frozenCorrection_apply,
      finiteEmbed_rowScalar_outside W x γ.level hout]
    have hp : previousScalar W γ.level (finiteEmbed N x)=0 := by
      rcases hl : γ.level with ⟨i,n⟩
      rw [hl] at hout
      change N < i ∨ N < n at hout
      cases n with
      | zero =>
        change finiteEmbed N x (rowIndex i)=0
        exact finiteEmbed_row_outside x i (by omega)
      | succ n =>
        change rowScalar W (i,n) (finiteEmbed N x)=0
        by_cases hi : N < i
        · exact finiteEmbed_rowScalar_outside W x _ (Or.inl hi)
        · by_cases hn : n=N
          · subst n
            exact hterminal i (by omega)
          · exact finiteEmbed_rowScalar_outside W x _ (Or.inr (by omega))
    rw [hp]
    ring

theorem finite_target_mem_range (N : ℕ) (hN : 0 < N) (y : BlockC0)
    (hy : ∀ γ : Label, N < γ.level.1 ∨ N < γ.level.2 → y γ=0) : y∈Set.range recomputedShift := by
  obtain ⟨x,hx⟩ := finiteRecomputed_surjective N hN (finiteTarget N y)
  exact ⟨finiteEmbed N x,finite_solution_gives_infinite y x hy hx⟩

def blockSquare (N : ℕ) (y : BlockC0) : BlockC0 :=
  cfunOfTendsto (fun γ => if γ.level.1≤N ∧ γ.level.2≤N then y γ else 0)
    ((cfun_tendsto y).if' tendsto_const_nhds)

@[simp] theorem blockSquare_apply (N : ℕ) (y : BlockC0) (γ : Label) :
    blockSquare N y γ=if γ.level.1≤N ∧ γ.level.2≤N then y γ else 0 := rfl

theorem blockSquare_outside (N : ℕ) (y : BlockC0) (γ : Label)
    (hγ : N < γ.level.1 ∨ N < γ.level.2) : blockSquare N y γ=0 := by
  rw [blockSquare_apply,ite_eq_right (by omega)]

theorem blockSquare_tendsto (y : BlockC0) : Tendsto (fun N => blockSquare N y) atTop (nhds y) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsmall : ∀ᶠ γ in cofinite, |y γ|<ε/2 := by
    have hh := Metric.tendsto_nhds.mp (cfun_tendsto y) (ε/2) (half_pos hε)
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hh
  have hfin : {γ : Label | ε/2≤|y γ|}.Finite := by
    simpa only [not_lt] using Filter.eventually_cofinite.mp hsmall
  let S := hfin.toFinset
  let M := S.sup (fun γ => max γ.level.1 γ.level.2)
  refine ⟨M,fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply cfun_norm_le _ (half_pos hε).le
  intro γ
  change |blockSquare n y γ-y γ|≤ε/2
  rw [blockSquare_apply]
  split_ifs with hγ
  · simpa only [sub_self,abs_zero] using (half_pos hε).le
  · simp only [zero_sub,abs_neg]
    apply le_of_lt
    by_contra hbad
    have hmem : γ∈S := hfin.mem_toFinset.mpr (le_of_not_gt hbad)
    have hb : max γ.level.1 γ.level.2≤M := Finset.le_sup (f := fun γ : Label => max γ.level.1 γ.level.2) hmem
    have h1 := (le_max_left γ.level.1 γ.level.2).trans (hb.trans hn)
    have h2 := (le_max_right γ.level.1 γ.level.2).trans (hb.trans hn)
    exact hγ ⟨h1,h2⟩

theorem recomputedShift_surjective : Function.Surjective recomputedShift := by
  have hclosed : IsClosed (Set.range recomputedShift) :=
    recomputed_antilipschitz.isClosed_range recomputed_lipschitz.uniformContinuous
  intro y
  apply hclosed.mem_of_tendsto (blockSquare_tendsto y)
  apply Filter.eventually_atTop.mpr
  refine ⟨1,fun N hN => finite_target_mem_range N (by omega) (blockSquare N y) ?_⟩
  exact blockSquare_outside N y

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def absorptionK (x : C0 × BlockC0) : ConcreteSpace := concreteLift (inputCoordinates x)
def absorptionG (x : C0 × BlockC0) : BlockC0 := recomputedShift (inputCoordinates x)

theorem absorptionK_lipschitz : LipschitzWith 3 absorptionK := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := concreteLift_lipschitz.dist_le_mul (inputCoordinates x) (inputCoordinates y)
  rw [inputCoordinates.isometry.dist_eq] at h
  exact h

theorem absorptionG_surjective : Function.Surjective absorptionG :=
  recomputedShift_surjective.comp inputCoordinates.surjective

theorem absorptionG_lower (x y : C0 × BlockC0) :
    (22/125 : ℝ)*dist x y≤dist (absorptionG x) (absorptionG y) := by
  have h := (recomputed_global_bounds (inputCoordinates x) (inputCoordinates y)).1
  rw [inputCoordinates.isometry.dist_eq] at h
  norm_num [eta] at h
  exact h

theorem absorptionQK (x : C0 × BlockC0) : correctionQ (absorptionK x)=absorptionG x-x.2 := by
  rw [absorptionK,correctionQ_concreteLift]
  have he : inputBlocks (inputCoordinates x)=x.2 := by ext γ; exact joinInputs_block x γ
  rw [he]
  rfl

def concreteAbsorption : ConcreteSpace × C0 → ConcreteSpace := absorptionMap correctionQ absorptionK

theorem concreteAbsorption_surjective : Function.Surjective concreteAbsorption :=
  absorption_onto correctionQ absorptionK absorptionG absorptionG_surjective absorptionQK

theorem concreteAbsorption_upper (x y : ConcreteSpace × C0) :
    dist (concreteAbsorption x) (concreteAbsorption y)≤(1+3*max 1 ‖correctionQ‖)*dist x y :=
  absorption_upper correctionQ absorptionK (by norm_num) absorptionK_lipschitz.dist_le_mul x y

theorem concreteAbsorption_inverse_bound (x y : ConcreteSpace × C0) :
    dist x y≤ max (1+3*‖correctionQ‖/(22/125)) (‖correctionQ‖/(22/125))*
      dist (concreteAbsorption x) (concreteAbsorption y) :=
  absorption_inverse_bound correctionQ absorptionK absorptionG (by norm_num) (by norm_num)
    absorptionK_lipschitz.dist_le_mul absorptionG_lower absorptionQK x y

theorem concreteAbsorption_bilip : BiLip concreteAbsorption := by
  let D := max (1+3*‖correctionQ‖/(22/125)) (‖correctionQ‖/(22/125))
  let U := 1+3*max 1 ‖correctionQ‖
  have hD : 0<D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨1/D,max U (1/D),one_div_pos.mpr hD,le_max_right _ _,fun x y => ⟨?_,?_⟩⟩
  · have h := concreteAbsorption_inverse_bound x y
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using h)
  · exact (concreteAbsorption_upper x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)

def concreteC0Embedding (x : C0) : ConcreteSpace := concreteAbsorption (0,x)

theorem concreteC0Embedding_bilip : BiLip concreteC0Embedding := by
  obtain ⟨c,C,hc,hcC,h⟩ := concreteAbsorption_bilip
  refine ⟨c,C,hc,hcC,fun x y => ?_⟩
  simpa only [concreteC0Embedding,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using h (0,x) (0,y)

theorem noLinearC0_not_product_equiv {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (hZ : NoLinearC0 Z) : ¬ Nonempty ((Z × C0) ≃L[ℝ] Z) := by
  rintro ⟨e⟩
  let T : C0 →L[ℝ] Z := e.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ Z C0)
  let B : ℝ := max 1 ‖e.symm.toContinuousLinearMap‖
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply hZ T
  refine ⟨1/B,one_div_pos.mpr hB,fun x => ?_⟩
  have hh : ‖x‖≤B*‖T x‖ := by
    calc
      ‖x‖ = ‖((0,x) : Z × C0)‖ := by simp
      _ = ‖e.symm (T x)‖ := by simp [T]
      _ ≤ ‖e.symm.toContinuousLinearMap‖*‖T x‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B*‖T x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  rw [one_div,mul_comm,← div_eq_mul_inv]
  exact (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hh)

theorem concrete_not_linearly_isomorphic : ¬ Nonempty ((ConcreteSpace × C0) ≃L[ℝ] ConcreteSpace) :=
  noLinearC0_not_product_equiv concrete_noLinearC0

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section Aharoni
variable {M : Type*} [MetricSpace M]

def earlierCut (q : ℕ → M) (r : ℝ) : ℕ → M → ℝ
  | 0, _ => r
  | n+1, x => min (earlierCut q r n x) (dist x (q n)-r/4)

theorem earlierCut_le_scale (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) : earlierCut q r n x≤ r := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (min_le_left _ _).trans ih

theorem earlierCut_le_point (q : ℕ → M) (r : ℝ) {n j : ℕ} (hj : j< n) (x : M) :
    earlierCut q r n x≤ dist x (q j)-r/4 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j=n
    · subst j; exact min_le_right _ _
    · exact (min_le_left _ _).trans (ih (by omega))

theorem le_earlierCut (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) {b : ℝ}
    (hb : b≤ r) (h : ∀ j< n,b≤ dist x (q j)-r/4) : b≤ earlierCut q r n x := by
  induction n with
  | zero => exact hb
  | succ n ih => exact le_min (ih (fun j hj => h j (by omega))) (h n (by omega))

theorem earlierCut_lipschitz (q : ℕ → M) (r : ℝ) (n : ℕ) : LipschitzWith 1 (earlierCut q r n) := by
  induction n with
  | zero => exact (LipschitzWith.const r).weaken (by norm_num)
  | succ n ih =>
    have hd : LipschitzWith 1 (fun x => dist x (q n)-r/4) := by
      simpa only [add_zero] using (LipschitzWith.dist_left (q n)).sub (LipschitzWith.const (r/4))
    simpa only [earlierCut,max_self] using ih.min hd

def metricBump (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) : ℝ :=
  max 0 (min (r-dist x (q n)) (min (dist x (q 0)-r) (earlierCut q r n x)))

theorem metricBump_nonneg (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) : 0≤ metricBump q r n x := le_max_left _ _

theorem metricBump_le_scale (q : ℕ → M) {r : ℝ} (hr : 0≤ r) (n : ℕ) (x : M) : metricBump q r n x≤ r :=
  max_le hr ((min_le_left _ _).trans (sub_le_self _ dist_nonneg))

theorem metricBump_zero_of_far (q : ℕ → M) {r : ℝ} (n : ℕ) (x : M) (h : r≤ dist x (q n)) :
    metricBump q r n x=0 :=
  max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr h))

theorem metricBump_zero_of_base (q : ℕ → M) {r : ℝ} (n : ℕ) (x : M) (h : dist x (q 0)≤ r) :
    metricBump q r n x=0 :=
  max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans (sub_nonpos.mpr h)))

theorem metricBump_lipschitz (q : ℕ → M) (r : ℝ) (n : ℕ) : LipschitzWith 1 (metricBump q r n) := by
  have ha : LipschitzWith 1 (fun x => r-dist x (q n)) := by
    simpa only [zero_add] using (LipschitzWith.const r).sub (LipschitzWith.dist_left (q n))
  have hb : LipschitzWith 1 (fun x => dist x (q 0)-r) := by
    simpa only [add_zero] using (LipschitzWith.dist_left (q 0)).sub (LipschitzWith.const r)
  have hh := (ha.min (hb.min (earlierCut_lipschitz q r n))).const_max 0
  unfold metricBump
  simpa only [max_self] using hh

theorem metricBump_eventually_zero (q : ℕ → M) (hq : DenseRange q) {r : ℝ} (hr : 0< r) (x : M) :
    ∃ N : ℕ, ∀ n, N≤ n → metricBump q r n x=0 := by
  obtain ⟨j,hj⟩ := hq.exists_dist_lt x (show 0< r/4 by positivity)
  refine ⟨j+1,fun n hn => ?_⟩
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_right _ _).trans
    ((earlierCut_le_point q r (n := n) (j := j) (by omega) x).trans (by linarith)))

def dyadicBump (q : ℕ → M) (p : ℤ × ℕ) (x : M) : ℝ := metricBump q ((2 : ℝ)^p.1) p.2 x

theorem dyadicBump_nonneg (q : ℕ → M) (p : ℤ × ℕ) (x : M) : 0 ≤ dyadicBump q p x :=
  metricBump_nonneg q _ _ x

theorem dyadicBump_finite_large (q : ℕ → M) (hq : DenseRange q) (x : M) {ε : ℝ} (hε : 0<ε) :
    {p : ℤ × ℕ | ε≤ dyadicBump q p x}.Finite := by
  classical
  obtain ⟨L,hL,hL'⟩ := exists_mem_Ico_zpow hε (show (1 : ℝ)<2 by norm_num)
  obtain ⟨U,hU,hU'⟩ := exists_mem_Ico_zpow (show 0< max 1 (dist x (q 0)) by positivity)
    (show (1 : ℝ)<2 by norm_num)
  choose N hN using fun k : ℤ => metricBump_eventually_zero q hq (zpow_pos (by norm_num : (0 : ℝ)<2) k) x
  have hfinite : (⋃ k∈Set.Icc L U, ({k} : Set ℤ) ×ˢ Set.Iio (N k)).Finite :=
    (Set.finite_Icc L U).biUnion (fun k hk => (Set.finite_singleton k).prod (Set.finite_Iio _))
  apply hfinite.subset
  rintro ⟨k,n⟩ hp
  have hnonzero : dyadicBump q (k,n) x≠0 := ne_of_gt (hε.trans_le hp)
  have hkL : L≤ k := by
    by_contra hh
    have hr := zpow_lt_zpow_right₀ (a := (2 : ℝ)) (by norm_num) (lt_of_not_ge hh)
    have hb := metricBump_le_scale q (zpow_pos (by norm_num : (0 : ℝ)<2) k).le n x
    change metricBump q ((2 : ℝ)^k) n x≥ε at hp
    linarith
  have hkU : k≤ U := by
    by_contra hh
    have hk : U+1≤ k := by omega
    have hr := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hk
    apply hnonzero
    exact metricBump_zero_of_base q n x ((le_max_right _ _).trans (hU'.le.trans hr))
  have hn : n< N k := by
    by_contra hh
    exact hnonzero (hN k n (le_of_not_gt hh))
  exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨⟨hkL,hkU⟩,⟨rfl,hn⟩⟩⟩

theorem dyadicBump_tendsto (q : ℕ → M) (hq : DenseRange q) (x : M) :
    Tendsto (fun p => dyadicBump q p x) cofinite (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply Filter.eventually_cofinite.mpr
  simpa only [Real.dist_eq,sub_zero,dyadicBump,abs_of_nonneg (metricBump_nonneg q _ _ x),not_lt]
    using dyadicBump_finite_large q hq x hε

def dyadicC0 (q : ℕ → M) (hq : DenseRange q) (x : M) : C₀(ℤ × ℕ,ℝ) :=
  cfunOfTendsto (fun p => dyadicBump q p x) (dyadicBump_tendsto q hq x)

@[simp] theorem dyadicC0_apply (q : ℕ → M) (hq : DenseRange q) (x : M) (p : ℤ × ℕ) :
    dyadicC0 q hq x p=dyadicBump q p x := rfl

theorem dyadicC0_upper (q : ℕ → M) (hq : DenseRange q) (x y : M) : dist (dyadicC0 q hq x) (dyadicC0 q hq y)≤ dist x y := by
  rw [dist_eq_norm]
  apply cfun_norm_le _ dist_nonneg
  intro p
  change |dyadicBump q p x-dyadicBump q p y|≤ dist x y
  simpa only [dyadicBump,NNReal.coe_one,one_mul,Real.dist_eq] using
    (metricBump_lipschitz q ((2 : ℝ)^p.1) p.2).dist_le_mul x y

end Aharoni
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section AharoniLower
variable {M : Type*} [MetricSpace M]

theorem dyadicBump_separates (q : ℕ → M) (hq : DenseRange q) (x y : M)
    (hxy : 0 < dist x y) (hbase : dist x y/2 ≤ dist x (q 0)) :
    ∃ p : ℤ × ℕ, dist x y/32 ≤ dyadicBump q p x ∧ dyadicBump q p y=0 := by
  classical
  obtain ⟨k,hk,hk'⟩ := exists_mem_Ico_zpow (show 0 < dist x y/4 by positivity)
    (show (1 : ℝ)<2 by norm_num)
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ)≠0)] at hk'
  let r : ℝ := (2 : ℝ)^k
  have hr : 0 < r := zpow_pos (by norm_num) k
  have hr_upper : r≤ dist x y/4 := hk
  have hr_lower : dist x y/8 < r := by change dist x y/4 < r*2 at hk'; linarith
  have hex := hq.exists_dist_lt x (half_pos hr)
  let n := Nat.find hex
  have hn : dist x (q n) < r/2 := Nat.find_spec hex
  have hbefore : ∀ j< n, r/2≤ dist x (q j) := fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hcut : r/4≤ earlierCut q r n x := le_earlierCut q r n x (by linarith)
    (fun j hj => by have h := hbefore j hj; linarith)
  have hbx : r/4≤ metricBump q r n x := by
    apply le_trans _ (le_max_right _ _)
    apply le_min (by linarith)
    exact le_min (by linarith) hcut
  have hyfar : r≤ dist y (q n) := by
    have ht := dist_triangle x (q n) y
    rw [dist_comm (q n) y] at ht
    linarith
  exact ⟨(k,n),(by change dist x y/32≤ metricBump q r n x; linarith),
    metricBump_zero_of_far q n y hyfar⟩

theorem dyadicC0_lower (q : ℕ → M) (hq : DenseRange q) (x y : M) :
    (1/32 : ℝ)*dist x y≤ dist (dyadicC0 q hq x) (dyadicC0 q hq y) := by
  by_cases hxy : x=y
  · subst y; simp
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hbase : dist x y/2≤ dist x (q 0) ∨ dist x y/2≤ dist y (q 0) := by
    have ht := dist_triangle x (q 0) y
    rw [dist_comm (q 0) y] at ht
    by_cases h : dist x y/2≤ dist x (q 0)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [dist_eq_norm]
  rcases hbase with hx|hy
  · obtain ⟨p,hp,hp0⟩ := dyadicBump_separates q hq x y hpos hx
    have hb := cfun_norm_apply_le (dyadicC0 q hq x-dyadicC0 q hq y) p
    change |dyadicBump q p x-dyadicBump q p y|≤_ at hb
    rw [hp0,sub_zero,abs_of_nonneg (dyadicBump_nonneg q p x)] at hb
    linarith
  · obtain ⟨p,hp,hp0⟩ := dyadicBump_separates q hq y x (by rwa [dist_comm]) (by rwa [dist_comm])
    have hb := cfun_norm_apply_le (dyadicC0 q hq x-dyadicC0 q hq y) p
    change |dyadicBump q p x-dyadicBump q p y|≤_ at hb
    rw [hp0,zero_sub,abs_neg,abs_of_nonneg (dyadicBump_nonneg q p y)] at hb
    rw [dist_comm y x] at hp
    linarith

end AharoniLower

section C0Reindex
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology A] [DiscreteTopology B]

theorem cfunPull_dist_eq_of_surjective (j : A → B) (hj : Tendsto j cofinite cofinite)
    (hs : Function.Surjective j) (f g : C₀(B,ℝ)) :
    dist (cfunPull j hj f) (cfunPull j hj g)=dist f g := by
  rw [dist_eq_norm,dist_eq_norm]
  apply le_antisymm
  · apply cfun_norm_le _ (norm_nonneg _)
    intro a
    exact cfun_norm_apply_le (f-g) (j a)
  · apply cfun_norm_le _ (norm_nonneg _)
    intro b
    obtain ⟨a,rfl⟩ := hs b
    exact cfun_norm_apply_le (cfunPull j hj f-cfunPull j hj g) a

end C0Reindex

section AharoniEmbedding
variable {M : Type*} [MetricSpace M]

def dyadicEnumeration : (ℤ × ℕ) ≃ ℕ := Denumerable.eqv _

def aharoniEmbedding (q : ℕ → M) (hq : DenseRange q) (x : M) : C0 :=
  cfunPull dyadicEnumeration.symm dyadicEnumeration.symm.injective.tendsto_cofinite (dyadicC0 q hq x)

theorem aharoniEmbedding_dist (q : ℕ → M) (hq : DenseRange q) (x y : M) :
    dist (aharoniEmbedding q hq x) (aharoniEmbedding q hq y)=dist (dyadicC0 q hq x) (dyadicC0 q hq y) :=
  cfunPull_dist_eq_of_surjective _ _ dyadicEnumeration.symm.surjective _ _

theorem aharoniEmbedding_bilip (q : ℕ → M) (hq : DenseRange q) : BiLip (aharoniEmbedding q hq) := by
  refine ⟨1/32,1,by norm_num,by norm_num,fun x y => ?_⟩
  rw [aharoniEmbedding_dist,one_mul]
  exact ⟨dyadicC0_lower q hq x y,dyadicC0_upper q hq x y⟩

end AharoniEmbedding

theorem c0_metricUniversal : MetricUniversal C0 := by
  intro M instM instSep
  rcases isEmpty_or_nonempty M with hM|hM
  · let := hM
    refine ⟨fun x => isEmptyElim x,1,1,by norm_num,by norm_num,fun x y => ?_⟩
    exact isEmptyElim x
  · let := hM
    obtain ⟨q,hq⟩ := TopologicalSpace.exists_dense_seq M
    exact ⟨aharoniEmbedding q hq,aharoniEmbedding_bilip q hq⟩

end
end C0Absorption

end OAI
end
end

section
section
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section

theorem BiLip.comp {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {g : Y → Z} {f : X → Y} (hg : BiLip g) (hf : BiLip f) : BiLip (g ∘ f) := by
  obtain ⟨cg,Cg,hcg,hcgC,hg⟩ := hg
  obtain ⟨cf,Cf,hcf,hcfC,hf⟩ := hf
  have hCg : 0≤Cg := hcg.le.trans hcgC
  have hCf : 0≤Cf := hcf.le.trans hcfC
  refine ⟨cg*cf,Cg*Cf,mul_pos hcg hcf,mul_le_mul hcgC hcfC hcf.le hCg,fun x y => ⟨?_,?_⟩⟩
  · calc
      cg*cf*dist x y = cg*(cf*dist x y) := mul_assoc _ _ _
      _ ≤ cg*dist (f x) (f y) := mul_le_mul_of_nonneg_left (hf x y).1 hcg.le
      _ ≤ dist ((g ∘ f) x) ((g ∘ f) y) := (hg _ _).1
  · calc
      dist ((g ∘ f) x) ((g ∘ f) y) ≤ Cg*dist (f x) (f y) := (hg _ _).2
      _ ≤ Cg*(Cf*dist x y) := mul_le_mul_of_nonneg_left (hf x y).2 hCg
      _ = Cg*Cf*dist x y := (mul_assoc _ _ _).symm

theorem concrete_metricUniversal : MetricUniversal ConcreteSpace := by
  intro M instM instSep
  obtain ⟨f,hf⟩ := c0_metricUniversal M
  exact ⟨concreteC0Embedding ∘ f,concreteC0Embedding_bilip.comp hf⟩

theorem main_result_oai : MainConclusion := by
  refine ⟨ConcreteSpace,inferInstance,inferInstance,inferInstance,inferInstance,
    concrete_noLinearC0,⟨concreteAbsorption,concreteAbsorption_surjective,concreteAbsorption_bilip⟩,
    ⟨concreteC0Embedding,concreteC0Embedding_bilip⟩,concrete_metricUniversal,
    concrete_not_linearly_isomorphic⟩

end
end C0Absorption

end OAI
end
end

theorem solution : type_of% @OAI.C0Absorption.main_result_oai := @OAI.C0Absorption.main_result_oai
