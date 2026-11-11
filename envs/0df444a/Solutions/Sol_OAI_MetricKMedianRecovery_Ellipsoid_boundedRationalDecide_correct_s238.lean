-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:21:57.02394+00:00
-- url     : https://prove2.me/submissions/0beb3d94-692f-4abc-9ca6-a81bba64766a

import Mathlib
import Definitions.Def_Q238K022
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_weakSolve_complete_diameters_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_PolytopeCertificate_approximate_implies_feasible_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

lemma Row.realHolds_cast {n : ℕ} (r : Row n) (x : Fin n → ℚ) :
    r.RealHolds (fun i => (x i : ℝ)) ↔ r.Holds x := by
  unfold Row.RealHolds Row.realValue Row.Holds Row.value
  dsimp only
  norm_cast

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_QuadSmulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V]

lemma quad_smul_matrix (M : Matrix V V ℝ) (x : V → ℝ) (t : ℝ) :
    quad (t • M) x=t*quad M x := by
  simp only [quad,smul_mulVec,dotProduct_smul,smul_eq_mul]

end

open Matrix
open scoped Matrix MatrixOrder

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SqNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma quad_one (x : V → ℝ) : quad (1 : Matrix V V ℝ) x=sqNorm x := by
  simp only [quad,one_mulVec,dotProduct,sqNorm,pow_two]

end

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma inv_smul_real (A : Matrix V V ℝ) (hA : A.PosDef) (t : ℝ) (ht : t≠0) :
    (t • A)⁻¹=t⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    mul_inv_cancel₀ ht,one_smul]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalInflatedShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma real_smul_matrix (r : ℚ) (A : Matrix V V ℚ) :
    realMatrix (r • A)=(r:ℝ) • realMatrix A := by
  ext i j
  simp only [realMatrix,Matrix.smul_apply,smul_eq_mul,Rat.cast_mul]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma badRow_none {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) :
    badRow rows c=none ↔ ∀ r∈rows, r.Holds c := by
  simp only [badRow,List.find?_eq_none,decide_eq_true_eq,not_lt,Row.Holds]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.state_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma realMatrix_one {V : Type*} [DecidableEq V] :
    realMatrix (1:Matrix V V ℚ)=(1:Matrix V V ℝ) := by
  ext i j
  by_cases h : i=j <;> simp [realMatrix,Matrix.one_apply,h]

lemma initial_realShape (n : ℕ) (R : ℚ) :
    realMatrix (initialState n R).shape=(R:ℝ)^2 • (1:Matrix (Fin n) (Fin n) ℝ) := by
  simp only [initialState,real_smul_matrix,realMatrix_one,Rat.cast_pow]

lemma initial_inverse (n : ℕ) (R : ℚ) (hR : 0<R) :
    (realMatrix (initialState n R).shape)⁻¹=
      (1/(R:ℝ)^2) • (1:Matrix (Fin n) (Fin n) ℝ) := by
  rw [initial_realShape,inv_smul_real _ Matrix.PosDef.one _
    (pow_ne_zero _ (Rat.cast_ne_zero.mpr hR.ne')),inv_one,one_div]

lemma initial_contains_box (n : ℕ) (hn : 1≤n) (R : ℚ) (hR : 0<R) (B : ℝ)
    (hB : 0≤B) (hRB : (n:ℝ)*B≤(R:ℝ)) (x : Fin n → ℝ) (hx : ∀ i, |x i|≤B) :
    quad (realMatrix (initialState n R).shape)⁻¹ (x-realVector (initialState n R).center)≤1 := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hR' : 0<(R:ℝ) := Rat.cast_pos.mpr hR
  have hc : realVector (initialState n R).center=0 := by ext i; simp [initialState,realVector]
  rw [hc,sub_zero,initial_inverse n R hR,quad_smul_matrix,quad_one]
  have hs : sqNorm x≤(n:ℝ)*B^2 := by
    unfold sqNorm
    have hh := Finset.sum_le_sum (fun i (_hi : i∈(Finset.univ:Finset (Fin n))) =>
      sq_le_sq₀ (abs_nonneg (x i)) hB |>.mpr (hx i))
    simpa only [sq_abs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hrr : (n:ℝ)*B^2≤(R:ℝ)^2 := by
    have hnB : 0≤(n:ℝ)*B := mul_nonneg (by positivity) hB
    have hsq := (sq_le_sq₀ hnB hR'.le).mpr hRB
    nlinarith [mul_nonneg (show 0≤(n:ℝ)-1 by linarith) (sq_nonneg B)]
  have hmul := mul_le_mul_of_nonneg_left (hs.trans hrr) (by positivity : 0≤1/(R:ℝ)^2)
  simpa only [one_div_mul_cancel (pow_ne_zero _ hR'.ne')] using hmul

lemma single_diameter_bound {n : ℕ} (x : Fin n → ℝ) (B r : ℝ) (hB : ∀ i, |x i|≤B)
    (hr : |r|≤1) (i j : Fin n) : |(x+r • (Pi.single i (1:ℝ) : Fin n → ℝ)) j|≤B+1 := by
  calc
    _ ≤ |x j|+|r*((Pi.single i (1:ℝ) : Fin n → ℝ) j)| := abs_add_le _ _
    _ ≤ B+1 := by
      apply add_le_add (hB j)
      by_cases he : j=i
      · subst j
        simpa using hr
      · simp [Pi.single_eq_of_ne he]

lemma initial_diameters (n : ℕ) (hn : 1≤n) (B : ℚ) (hB : 0≤B)
    (x : Fin n → ℝ) (hx : ∀ i, |x i|≤(B:ℝ)) (r : ℝ) (hr : 0 < r) (hr1 : r≤1) :
    ∀ i, quad (realMatrix (initialState n ((n:ℚ)*(B+1))).shape)⁻¹
      (x+r • Pi.single i 1-realVector (initialState n ((n:ℚ)*(B+1))).center)≤1 ∧
      quad (realMatrix (initialState n ((n:ℚ)*(B+1))).shape)⁻¹
      (x+(-r) • Pi.single i 1-realVector (initialState n ((n:ℚ)*(B+1))).center)≤1 := by
  have hnq : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
  have hRq : 0<(n:ℚ)*(B+1) := mul_pos hnq (by linarith)
  have hB' : 0≤(B:ℝ)+1 := by exact_mod_cast (show (0:ℚ)≤B+1 by linarith)
  have hRB : (n:ℝ)*((B:ℝ)+1)≤((n:ℚ)*(B+1):ℚ) := by push_cast; rfl
  intro i
  constructor
  · exact initial_contains_box n hn _ hRq _ hB' hRB _
      (fun j => single_diameter_bound x (B:ℝ) r hx (by rwa [abs_of_pos hr]) i j)
  · exact initial_contains_box n hn _ hRq _ hB' hRB _
      (fun j => single_diameter_bound x (B:ℝ) (-r) hx (by rwa [abs_neg,abs_of_pos hr]) i j)

lemma weakSolve_sound {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) (c : Fin n → ℚ)
    (hc : weakSolve rows R p s=some c) : ∀ r∈rows, r.Holds c := by
  dsimp only [weakSolve] at hc
  split_ifs at hc with hh
  · cases hc
    exact (badRow_none _ _).mp hh

lemma relaxedRows_feasible {n : ℕ} (eps : ℚ) (heps : 0≤eps) (rows : List (Row n))
    (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x) :
    ∀ q∈relaxedRows eps rows, q.RealHolds x := by
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  have hh := hx a ha
  change a.realValue x≤((a.bound+eps:ℚ):ℝ)
  push_cast
  exact le_trans hh (le_add_of_nonneg_right (Rat.cast_nonneg.mpr heps))

lemma row_value_single {n : ℕ} (q : Row n) (x : Fin n → ℝ) (r : ℝ) (i : Fin n) :
    q.realValue (x+r • Pi.single i 1)=q.realValue x+r*(q.coeff i:ℝ) := by
  change realVector q.coeff ⬝ᵥ (x+r • Pi.single i 1)=realVector q.coeff ⬝ᵥ x+r*(q.coeff i:ℝ)
  rw [dotProduct_add,dotProduct_smul,smul_eq_mul,dotProduct_single]
  simp [realVector]

lemma relaxed_diameter {n : ℕ} (eps H : ℚ) (rows : List (Row n))
    (hH : 0≤(H:ℝ)) (hcoeff : ∀ q∈rows, ∀ j, |(q.coeff j:ℝ)|≤(H:ℝ))
    (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x) (r : ℝ)
    (hr : |r| *(H:ℝ)≤(eps:ℝ)) (i : Fin n) :
    ∀ q∈relaxedRows eps rows, q.RealHolds (x+r • Pi.single i 1) := by
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  change a.realValue (x+r • Pi.single i 1)≤((a.bound+eps:ℚ):ℝ)
  rw [row_value_single]
  push_cast
  have hb := mul_le_mul_of_nonneg_left (hcoeff a ha i) (abs_nonneg r)
  have hab := le_abs_self (r*(a.coeff i:ℝ))
  rw [abs_mul] at hab
  have _ := hH
  exact add_le_add (hx a ha) (hab.trans (hb.trans hr))

theorem weakSolve_complete {n : ℕ} (rows : List (Row n)) (hn : 2≤n)
    (B H eps : ℚ) (hB : 0≤B) (hH : 1≤H) (heps : 0<eps) (heps1 : eps≤1)
    (p s : ℕ) (hRp : ((n:ℚ)*(B+1):ℚ)≤(2:ℚ)^s) (hrp : H/eps≤(2:ℚ)^p)
    (hcoeff : ∀ q∈rows, ∀ j, |q.coeff j|≤H)
    (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x) (hbox : ∀ i, |x i|≤(B:ℝ)) :
    ∃ c, weakSolve (relaxedRows eps rows) ((n:ℚ)*(B+1)) p s=some c := by
  let r : ℝ := (eps:ℝ)/(H:ℝ)
  have hHp : 0<(H:ℝ) := by exact_mod_cast (show (0:ℚ)<H by linarith)
  have hep : 0<(eps:ℝ) := Rat.cast_pos.mpr heps
  have hr : 0 < r := div_pos hep hHp
  have hr1 : r≤1 := (div_le_one hHp).mpr (by exact_mod_cast (show eps≤H by linarith))
  have hR : (1:ℚ)≤(n:ℚ)*(B+1) := by
    have hnq : (1:ℚ)≤n := by exact_mod_cast (show 1≤n by omega)
    nlinarith
  have hpr : 1/r≤(2:ℝ)^p := by
    have hh : ((H/eps:ℚ):ℝ)≤((2:ℚ)^p:ℚ) := by exact_mod_cast hrp
    simpa only [r,one_div_div,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hcoef : ∀ q∈rows, ∀ j, |(q.coeff j:ℝ)|≤(H:ℝ) := by
    intro q hq j
    exact_mod_cast hcoeff q hq j
  have heq : r*(H:ℝ)=(eps:ℝ) := div_mul_cancel₀ _ hHp.ne'
  apply weakSolve_complete_diameters_s238 _ hn _ hR p s r hr (by exact_mod_cast hRp) hpr x
    (relaxedRows_feasible eps heps.le rows x hx) _ (initial_diameters n (by omega) B hB x hbox r hr hr1)
  intro i
  constructor
  · exact relaxed_diameter eps H rows hHp.le hcoef x hx r (by rw [abs_of_pos hr,heq]) i
  · exact relaxed_diameter eps H rows hHp.le hcoef x hx (-r) (by rw [abs_neg,abs_of_pos hr,heq]) i

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundRow
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.integerDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

lemma boundedRows_all {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ)
    (P : Row n → Prop) : (∀ q∈boundedRows A b B, P q) ↔
      ∀ r, P (integerRow (boundedMatrix A r) (boundedBounds b B r)) := by
  constructor
  · intro h r
    apply h
    simp only [boundedRows,List.mem_append,List.mem_ofFn]
    cases r with
    | inl r => exact Or.inl (Or.inl ⟨r,rfl⟩)
    | inr p =>
      rcases p with ⟨s,i⟩
      cases s
      · exact Or.inr ⟨i,rfl⟩
      · exact Or.inl (Or.inr ⟨i,rfl⟩)
  · intro h q hq
    simp only [boundedRows,List.mem_append,List.mem_ofFn] at hq
    rcases hq with ((⟨r,rfl⟩ | ⟨i,rfl⟩) | ⟨i,rfl⟩)
    · exact h (.inl r)
    · exact h (.inr (true,i))
    · exact h (.inr (false,i))

lemma bounded_region {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (B : ℕ) (x : Fin n → ℝ) :
    x∈region (fun r j => (boundedMatrix A r j:ℝ)) (fun r => (boundedBounds b B r:ℝ)) ↔
      (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  have he (s : Bool) (i : Fin n) :
      (∑ j, (boundedMatrix A (.inr (s,i)) j:ℝ)*x j)=if s then x i else -x i := by
    cases s <;> simp [boundedMatrix]
  constructor
  · intro hh
    refine ⟨fun r => hh (.inl r),fun i => abs_le.mpr ?_⟩
    have hp := hh (.inr (true,i))
    have hm := hh (.inr (false,i))
    rw [he] at hp hm
    exact ⟨by
      have hh : -x i≤(B:ℝ) := by simpa [boundedBounds] using hm
      linarith,by simpa [boundedBounds] using hp⟩
  · rintro ⟨ha,hb⟩ r
    cases r with
    | inl r => exact ha r
    | inr p =>
      rcases p with ⟨s,i⟩
      rw [he]
      cases s
      · change -x i≤(B:ℝ)
        linarith [(abs_le.mp (hb i)).1]
      · exact (abs_le.mp (hb i)).2

lemma rows_real_region {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ)
    (x : Fin n → ℝ) : (∀ q∈boundedRows A b B, q.RealHolds x) ↔
      x∈region (fun r j => (boundedMatrix A r j:ℝ)) (fun r => (boundedBounds b B r:ℝ)) := by
  rw [boundedRows_all]
  simp only [integerRow,Row.RealHolds,Row.realValue,Rat.cast_intCast,region,Set.mem_ofPred_eq]

lemma bounded_data_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (B H : ℕ) (hBH : B+1≤H) (hA : ∀ r j, |A r j|≤(H:ℤ)) (hb : ∀ r, |b r|≤(H:ℤ)) :
    (∀ r j, |boundedMatrix A r j|≤(H:ℤ)) ∧ (∀ r, |boundedBounds (n:=n) b B r|≤(H:ℤ)) := by
  have hH : (1:ℤ)≤H := by exact_mod_cast (show 1≤H by omega)
  constructor
  · intro r j
    cases r with
    | inl r => exact hA r j
    | inr p =>
      rcases p with ⟨s,i⟩
      simp only [boundedMatrix]
      split_ifs <;> simp only [abs_one,abs_neg,abs_zero] <;> omega
  · intro r
    cases r with
    | inl r => exact hb r
    | inr p =>
      change |(B:ℤ)|≤(H:ℤ)
      simpa only [Int.natCast_nonneg,abs_of_nonneg] using
        (show (B:ℤ)≤(H:ℤ) by exact_mod_cast (show B≤H by omega))

lemma gapDenominator_pos (m n H : ℕ) (hH : 1≤H) : 0<gapDenominator m n H := by
  unfold gapDenominator
  apply Nat.mul_pos (Nat.factorial_pos _)
  apply pow_pos
  exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

lemma gapEpsilon_bounds (m n H : ℕ) (hH : 1≤H) :
    0<gapEpsilon m n H ∧ gapEpsilon m n H≤1 ∧
      gapEpsilon m n H<1/(gapDenominator m n H:ℚ) := by
  have hQ : (1:ℚ)≤gapDenominator m n H := by exact_mod_cast gapDenominator_pos m n H hH
  have hpos : (0:ℚ)<gapDenominator m n H := by linarith
  refine ⟨by exact div_pos (by norm_num) (mul_pos (by norm_num) hpos),?_,?_⟩
  · exact (div_le_one (by positivity)).mpr (by nlinarith)
  · apply one_div_lt_one_div_of_lt hpos
    nlinarith

lemma gapDenominator_cast (m n B H : ℕ) (hBH : B+1≤H) :
    ((Fintype.card (Option (Fin n))).factorial *
      ((Fintype.card (SlackRow (BoundRow m n) (Fin n)):ℤ)*(max (H:ℤ) (B+1))^2)^
        (Fintype.card (Option (Fin n))) : ℤ)=(gapDenominator m n H:ℤ) := by
  have hh : max (H:ℤ) (B+1)=H := max_eq_left (by exact_mod_cast hBH)
  simp only [Fintype.card_option,Fintype.card_fin,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_bool,SlackRow,BoundRow,hh,gapDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]

lemma precisionLog_bound (m n H : ℕ) (hH : 1≤H) :
    (H:ℚ)/gapEpsilon m n H≤(2:ℚ)^(precisionLog m n H) := by
  have hh : (2*gapDenominator m n H*H:ℕ)<2^(precisionLog m n H) := Nat.lt_log2_self
  have hcast : (2:ℚ)*(gapDenominator m n H)*H≤(2:ℚ)^(precisionLog m n H) := by exact_mod_cast hh.le
  have hQ : (gapDenominator m n H:ℚ)≠0 := by exact_mod_cast (gapDenominator_pos m n H hH).ne'
  convert hcast using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [gapEpsilon]
  field_simp

lemma radiusLog_bound (n B : ℕ) : (n:ℚ)*(B+1)≤(2:ℚ)^(radiusLog n B) := by
  exact_mod_cast (Nat.lt_log2_self (n:=n*(B+1))).le

theorem integerDecide_correct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (B H : ℕ) (hn : 2≤n) (hBH : B+1≤H) (hA : ∀ r j, |A r j|≤(H:ℤ)) (hb : ∀ r, |b r|≤(H:ℤ)) :
    integerDecide A b B H=true ↔
      ∃ x : Fin n → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  have hH : 1≤H := by omega
  have heps := gapEpsilon_bounds m n H hH
  have hdata := bounded_data_bound A b B H hBH hA hb
  constructor
  · intro hyes
    obtain ⟨c,hc⟩ := Option.isSome_iff_exists.mp hyes
    have hrows := weakSolve_sound _ _ _ _ c hc
    have ha : ∀ r, (∑ j, (boundedMatrix A r j:ℝ)*(c j:ℝ))≤
        (boundedBounds b B r:ℝ)+(gapEpsilon m n H:ℝ) := by
      have hall : ∀ q∈boundedRows A b B, (relaxedRow (gapEpsilon m n H) q).Holds c := by
        intro q hq
        exact hrows _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
      have hh := (boundedRows_all A b B _).mp hall
      intro r
      have ht := (Row.realHolds_cast _ c).mpr (hh r)
      simpa only [relaxedRow,integerRow,Row.RealHolds,Row.realValue,Rat.cast_intCast,Rat.cast_add] using ht
    have hcbox : ∀ j, -((B+1:ℕ):ℝ)≤(c j:ℝ) ∧ (c j:ℝ)≤((B+1:ℕ):ℝ) := by
      intro j
      have hp := ha (.inr (true,j))
      have hm := ha (.inr (false,j))
      simp only [boundedMatrix,boundedBounds] at hp hm
      simp at hp hm
      have hepr : (gapEpsilon m n H:ℝ)≤1 := by exact_mod_cast heps.2.1
      push_cast
      constructor <;> linarith
    obtain ⟨y,hy,_⟩ := approximate_implies_feasible_s238 (boundedMatrix A) (boundedBounds b B)
      (B+1) H (by positivity) (by exact_mod_cast hH) hdata.1 hdata.2 (gapEpsilon m n H:ℝ)
      (by exact_mod_cast heps.1.le) (by exact_mod_cast (heps.2.1.trans (by exact_mod_cast hH : (1:ℚ)≤H)))
      (by
        rw [gapDenominator_cast m n B H hBH]
        have hh := (Rat.cast_lt (K:=ℝ)).mpr heps.2.2
        simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Int.cast_natCast] using hh) (fun j => (c j:ℝ))
      (by simpa only [Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_natCast,Int.cast_one] using hcbox) ha
    exact ⟨y,(bounded_region A b B y).mp hy⟩
  · rintro ⟨x,hx,hbox⟩
    have hcoeff : ∀ q∈boundedRows A b B, ∀ j, |q.coeff j|≤(H:ℚ) := by
      refine (boundedRows_all A b B (fun q => ∀ j, |q.coeff j|≤(H:ℚ))).mpr ?_
      intro r j
      change |((boundedMatrix A r j:ℤ):ℚ)|≤(H:ℚ)
      exact_mod_cast hdata.1 r j
    obtain ⟨c,hc⟩ := weakSolve_complete (boundedRows A b B) hn B H (gapEpsilon m n H)
      (by positivity) (by exact_mod_cast hH) heps.1 heps.2.1 (precisionLog m n H) (radiusLog n B)
      (radiusLog_bound n B) (precisionLog_bound m n H hH) hcoeff x
      ((rows_real_region A b B x).mpr ((bounded_region A b B x).mpr ⟨hx,hbox⟩))
      (by exact_mod_cast hbox)
    exact Option.isSome_iff_exists.mpr ⟨c,hc⟩

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DataHeight
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

lemma dataHeight_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    B+1≤dataHeight A b B ∧ (∀ r j, |A r j|≤(dataHeight A b B:ℤ)) ∧
      (∀ r, |b r|≤(dataHeight A b B:ℤ)) := by
  have hr (r : Fin m) : (b r).natAbs+∑ j, (A r j).natAbs≤dataHeight A b B := by
    have hh := Finset.single_le_sum (f:=fun r => (b r).natAbs+∑ j, (A r j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    exact hh.trans (Nat.le_add_left _ _)
  refine ⟨Nat.le_add_right _ _,?_,?_⟩
  · intro r j
    have hj := Finset.single_le_sum (f:=fun j => (A r j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hh : (A r j).natAbs≤dataHeight A b B := hj.trans ((Nat.le_add_left _ _).trans (hr r))
    rw [←Int.natCast_natAbs]
    exact_mod_cast hh
  · intro r
    have hh : (b r).natAbs≤dataHeight A b B := (Nat.le_add_right _ _).trans (hr r)
    rw [←Int.natCast_natAbs]
    exact_mod_cast hh

lemma padMatrix_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (r : Fin m) (y : Fin (n+2) → ℝ) :
    (∑ j, (padMatrix A r j:ℝ)*y j)=∑ j, (A r j:ℝ)*y (Fin.castAdd 2 j) := by
  rw [Fin.sum_univ_add]
  simp [padMatrix]

lemma pad_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    (∃ y : Fin (n+2) → ℝ, (∀ r, (∑ j, (padMatrix A r j:ℝ)*y j)≤(b r:ℝ)) ∧
      (∀ j, |y j|≤(B:ℝ))) ↔
    ∃ x : Fin n → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  constructor
  · rintro ⟨y,hy,hbox⟩
    refine ⟨fun i => y (Fin.castAdd 2 i),?_,fun i => hbox _⟩
    intro r
    simpa only [padMatrix_sum] using hy r
  · rintro ⟨x,hx,hbox⟩
    refine ⟨Fin.append x (fun _ : Fin 2 => 0),?_,?_⟩
    · intro r
      simpa only [padMatrix_sum,Fin.append_left] using hx r
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [Fin.append_left] using hbox i
      · simp

theorem boundedIntegerDecide_correct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    boundedIntegerDecide A b B=true ↔
      ∃ x : Fin n → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  have hh := dataHeight_bounds (padMatrix A) b B
  exact (integerDecide_correct (padMatrix A) b B _ (by omega) hh.1 hh.2.1 hh.2.2).trans
    (pad_feasible A b B)

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.PolytopeCertificate
open Matrix
open scoped BigOperators
variable {J R V : Type*} [Fintype J] [DecidableEq J] [Fintype R] [Fintype V] [DecidableEq V]

omit [DecidableEq J] in
lemma rowDenominator_pos (q : J → ℚ) : 0 < rowDenominator q := by
  apply Finset.prod_pos
  intro i _
  exact_mod_cast (q i).den_pos

lemma rowNumerator_cast (q : J → ℚ) (i : J) :
    (rowNumerator q i:ℝ)=(rowDenominator q:ℝ)*(q i:ℝ) := by
  have hh : rowDenominator q = (q i).den * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ) :=
    (Finset.mul_prod_erase Finset.univ (fun j => ((q j).den:ℤ)) (Finset.mem_univ i)).symm
  rw [hh,Rat.cast_def]
  unfold rowNumerator
  push_cast
  have hn : ((q i).den:ℝ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
  field_simp

end MetricKMedianRecovery.PolytopeCertificate
namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

lemma clearRow_holds {n : ℕ} (q : Row n) (x : Fin n → ℝ) :
    (∑ j, (rowNumerator (rowEntries q) (some j):ℝ)*x j)≤
      (rowNumerator (rowEntries q) none:ℝ) ↔ q.RealHolds x := by
  simp only [rowNumerator_cast,mul_assoc,←Finset.mul_sum]
  have hp : (0:ℝ)<(rowDenominator (rowEntries q):ℝ) := by exact_mod_cast rowDenominator_pos (rowEntries q)
  exact mul_le_mul_iff_right₀ hp

lemma clearedRows_holds {n : ℕ} (rows : List (Row n)) (x : Fin n → ℝ) :
    (∀ r, (∑ j, (clearedMatrix rows r j:ℝ)*x j)≤(clearedBounds rows r:ℝ)) ↔
      ∀ q∈rows, q.RealHolds x := by
  simp only [clearedMatrix,clearedBounds,clearRow_holds]
  constructor
  · intro h q hq
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hq
    have hh : rows[i].RealHolds x := h ⟨i,hi⟩
    rwa [he] at hh
  · intro h i
    exact h _ (List.getElem_mem _)

theorem boundedRationalDecide_correct_s238_oai {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    boundedRationalDecide rows B=true ↔
      ∃ x : Fin n → ℝ, (∀ q∈rows, q.RealHolds x) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  rw [boundedRationalDecide,boundedIntegerDecide_correct]
  exact exists_congr (fun x => and_congr_left (fun _ => clearedRows_holds rows x))

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238_oai := @OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238_oai
