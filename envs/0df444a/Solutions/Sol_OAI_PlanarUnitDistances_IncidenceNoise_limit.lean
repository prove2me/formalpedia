-- Prove2me | solution 1 for OAI.PlanarUnitDistances.IncidenceNoise.limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T03:01:41.132261+00:00
-- url     : https://prove2.me/submissions/c52bd725-2103-4f77-8ac5-c305940ebcb6

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceScale_scale_limit

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteInformation
open scoped InnerProductSpace
open Finset Real

lemma hellinger_pointwise {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : p ≠ 0 → q ≠ 0) :
    (sqrt p - sqrt q)^2 ≤ p * log (p/q) - p + q := by
  by_cases hpz : p = 0
  · simp [hpz, sq_sqrt hq]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm (hac hpz))
  have hspp := sqrt_pos.mpr hpp
  have hsqp := sqrt_pos.mpr hqp
  have hsp := sq_sqrt hp
  have hsq := sq_sqrt hq
  have hl := log_le_sub_one_of_pos (div_pos hsqp hspp)
  rw [log_div (ne_of_gt hsqp) (ne_of_gt hspp), log_sqrt hq, log_sqrt hp] at hl
  have hm : p * (sqrt q / sqrt p) = sqrt p * sqrt q := by
    rw [← mul_div_assoc]
    apply (div_eq_iff (ne_of_gt hspp)).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*p by positivity)
  rw [log_div hpz (hac hpz)]
  nlinarith

theorem hellinger_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) :
    (∑ a, (sqrt (p a) - sqrt (q a))^2) ≤ KL p q := by
  have hh := sum_le_sum (s := univ) (fun a _ => hellinger_pointwise (hp a) (hq a) (hac a))
  simpa only [sum_add_distrib, sum_sub_distrib, hpsum, hqsum, sub_add_cancel, KL] using hh

theorem TV_sq_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : (TV p q)^2 ≤ KL p q := by
  have hH := hellinger_le_KL p q hp hq hpsum hqsum hac
  have hs : (∑ a, (sqrt (p a) + sqrt (q a))^2) ≤ 4 := by
    calc
      _ ≤ ∑ a, (2*p a + 2*q a) := by
        apply sum_le_sum
        intro a _
        nlinarith [sq_nonneg (sqrt (p a) - sqrt (q a)), sq_sqrt (hp a), sq_sqrt (hq a)]
      _ = 4 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hpsum, hqsum]; norm_num
  have hid (a : α) : |p a-q a| =
      |sqrt (p a)-sqrt (q a)| * (sqrt (p a)+sqrt (q a)) := by
    rw [← abs_of_nonneg (show 0 ≤ sqrt (p a)+sqrt (q a) by positivity), ← abs_mul]
    congr 1
    nlinarith [sq_sqrt (hp a), sq_sqrt (hq a)]
  have hcs := sum_mul_sq_le_sq_mul_sq univ
    (fun a => |sqrt (p a)-sqrt (q a)|) (fun a => sqrt (p a)+sqrt (q a))
  simp only [← hid, sq_abs] at hcs
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ∑ a, (sqrt (p a)-sqrt (q a))^2 by positivity)
  unfold TV
  nlinarith

theorem KL_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : 0 ≤ KL p q :=
  (sq_nonneg _).trans (TV_sq_le_KL p q hp hq hpsum hqsum hac)

universe u

end PlanarUnitDistances.FiniteInformation

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceEntropy
open Finset Real FiniteInformation
variable {P Q : Type*} [Fintype P] [Fintype Q]

omit [Fintype Q] in
lemma degree_nonneg (E : P → Q → Prop) (q : Q) : 0 ≤ degree E q :=
  sum_nonneg fun p _ => indicator_nonneg E p q

lemma edgeCount_nonneg (E : P → Q → Prop) : 0 ≤ edgeCount E :=
  sum_nonneg fun q _ => degree_nonneg E q

lemma wedge_nonneg (E : P → Q → Prop) (x : P × P) : 0 ≤ wedge E x := by
  unfold wedge
  exact sum_nonneg fun q _ => div_nonneg
    (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
    (mul_nonneg (edgeCount_nonneg E) (degree_nonneg E _))

lemma pointLaw_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) : ∑ p, pointLaw E p = 1 := by
  unfold pointLaw
  rw [← sum_div, sum_comm]
  exact div_self hE

lemma wedge_fst (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) (p : P) :
    ∑ r, wedge E (p,r) = pointLaw E p := by
  unfold wedge pointLaw
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro q _
  dsimp only
  rw [← sum_div, ← mul_sum]
  change indicator E p q * degree E q / (edgeCount E * degree E q) = _
  exact mul_div_mul_right _ _ (hd q)

lemma wedge_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) (hd : ∀ q, degree E q ≠ 0) :
    ∑ x, wedge E x = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [wedge_fst E hd]
  exact pointLaw_sum E hE

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.GeometricLaw
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
lemma row_count (P Q : Finset Plane) (p : P) :
    (∑q,IncidenceEntropy.indicator (E P Q) p q)=CircleIncidence.degree Q p := by
  change (∑q : Q,if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)=_
  rw [CircleIncidence.degree_sum]
  exact (Finset.sum_coe_sort Q (fun q => if dist (p:Plane) q=1 then (1:ℝ) else 0)).trans
    (by simp only [dist_comm])
end
end PlanarUnitDistances.GeometricLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sequence
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceSequence
open Filter PowerGrowth CircleIncidence
open scoped Classical
noncomputable section
lemma Good.point_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (p : P) : 0 < degree Q p := by
  have hm : (0:ℝ) < P.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).1
  have hh := (le_div_iff₀ h.positive).mp (h.atomP p p.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hm) h.positive).trans_le hh

lemma Good.center_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (q : Q) : 0 < degree P q := by
  have hn : (0:ℝ) < Q.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).2
  have hh := (le_div_iff₀ h.positive).mp (h.atomQ q q.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hn) h.positive).trans_le hh

lemma Good.information_nonneg {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) : 0 ≤ information P Q := by
  have he : IncidenceEntropy.edgeCount (GeometricLaw.E P Q) ≠ 0 := by
    rw [GeometricLaw.edgeCount_eq]; exact h.positive.ne'
  have hd : ∀q : Q,IncidenceEntropy.degree (GeometricLaw.E P Q) q ≠ 0 := by
    intro q; rw [GeometricLaw.degree_eq]; exact (h.center_degree_pos q).ne'
  have hp : ∀p : P,0 < IncidenceEntropy.pointLaw (GeometricLaw.E P Q) p := by
    intro p
    rw [IncidenceEntropy.pointLaw,GeometricLaw.row_count,GeometricLaw.edgeCount_eq]
    exact div_pos (h.point_degree_pos p) h.positive
  exact FiniteInformation.KL_nonneg _ _ (IncidenceEntropy.wedge_nonneg _)
    (fun pr => (mul_pos (hp pr.1) (hp pr.2)).le) (IncidenceEntropy.wedge_sum _ he hd)
    (by rw [Fintype.sum_prod_type,←Finset.sum_mul_sum,IncidenceEntropy.pointLaw_sum _ he,one_mul])
    (fun pr _ => (mul_pos (hp pr.1) (hp pr.2)).ne')

lemma Sequence.tendsto (s : Sequence) : Tendsto s.t atTop atTop :=
  tendsto_atTop_mono (fun i => (by linarith [s.large i] : (i:ℝ) ≤ s.t i))
    tendsto_natCast_atTop_atTop

lemma Sequence.accuracy_limit : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma Sequence.information_limit (s : Sequence) :
    Tendsto (fun i => information (s.P i) (s.Q i)/Real.log (s.t i)) atTop (nhds 0) := by
  apply squeeze_zero (fun i => div_nonneg (s.good i).information_nonneg
    (Real.log_nonneg (by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i])))
    (fun i => (s.good i).info) Sequence.accuracy_limit

end
end PlanarUnitDistances.IncidenceSequence

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LogHistory
open Filter
noncomputable section

lemma length_pos (M : ℕ) (t : ℝ) : 0<length M t := Nat.succ_pos _

lemma bounds {M : ℕ} (hM : 0<M) {t : ℝ} (ht : 1<t) :
    Real.log t/(4*(Real.log M+1)) ≤ (length M t:ℝ) ∧
      (length M t:ℝ) ≤ Real.log t/(4*(Real.log M+1))+1 ∧
      (M:ℝ)^(length M t) ≤ M*t^(1/4:ℝ) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hp : (0:ℝ)<M := by exact_mod_cast hM
  have hl : 0 ≤ Real.log M := Real.log_nonneg hm
  have ha : 0<4*(Real.log M+1) := by positivity
  have ht0 : 0<t := by linarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht.le
  have hf := Nat.floor_le (div_nonneg hlt ha.le)
  have hg := Nat.lt_floor_add_one (Real.log t/(4*(Real.log M+1)))
  have hk : (length M t:ℝ) ≤ Real.log t/(4*(Real.log M+1))+1 := by
    simp only [length,Nat.cast_add,Nat.cast_one]
    linarith
  refine ⟨by simpa only [length,Nat.cast_add,Nat.cast_one] using hg.le,hk,?_⟩
  have hcoef : Real.log M/(4*(Real.log M+1)) ≤ 1/4 := by
    apply (div_le_iff₀ ha).mpr
    linarith
  have he : (length M t:ℝ)*Real.log M ≤ Real.log M+(1/4:ℝ)*Real.log t := by
    have hh := mul_le_mul_of_nonneg_right hk hl
    have hj := mul_le_mul_of_nonneg_right hcoef hlt
    nlinarith [show Real.log t/(4*(Real.log M+1))*Real.log M=
      (Real.log M/(4*(Real.log M+1)))*Real.log t by ring]
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_nat_mul,Real.exp_log hp,Real.exp_add,Real.exp_log hp] at hh
  simpa only [Real.rpow_def_of_pos ht0,mul_comm (Real.log t) (1/4:ℝ)] using hh

lemma ratio_limit {M : ℕ} (hM : 0<M) (t D : ℕ → ℝ)
    (ht : Tendsto t atTop atTop)
    (hD0 : ∀ᶠn in atTop,0 ≤ D n)
    (hD : Tendsto (fun n => D n/Real.log (t n)) atTop (nhds 0)) :
    Tendsto (fun n => D n/(length M (t n):ℝ)) atTop (nhds 0) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hl : 0 ≤ Real.log M := Real.log_nonneg hm
  have ha : 0<4*(Real.log M+1) := by positivity
  have hupper : Tendsto (fun n => (4*(Real.log M+1))*(D n/Real.log (t n))) atTop (nhds 0) := by
    simpa only [mul_zero] using hD.const_mul (4*(Real.log M+1))
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hD0] with n hn
    exact div_nonneg hn (Nat.cast_nonneg _)
  · filter_upwards [hD0,ht.eventually_gt_atTop 1] with n hdn htn
    have hb := (bounds hM htn).1
    have hk : (0:ℝ)<length M (t n) := by exact_mod_cast length_pos M (t n)
    have hlt : 0<Real.log (t n) := Real.log_pos htn
    have hh : Real.log (t n) ≤ (length M (t n):ℝ)*(4*(Real.log M+1)) := (div_le_iff₀ ha).mp hb
    apply (div_le_iff₀ hk).mpr
    have he : (4*(Real.log M+1))*(D n/Real.log (t n))*(length M (t n):ℝ)=
        D n*((length M (t n):ℝ)*(4*(Real.log M+1)))/Real.log (t n) := by ring
    rw [he]
    apply (le_div_iff₀ hlt).mpr
    exact mul_le_mul_of_nonneg_left hh hdn

lemma density_limit {M : ℕ} (hM : 0<M) (t d : ℕ → ℝ)
    (ht : Tendsto t atTop atTop) (hd0 : ∀ᶠn in atTop,0 ≤ d n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ)) :
    Tendsto (fun n => (M:ℝ)^(length M (t n))*d n) atTop (nhds 0) := by
  have hv : Tendsto (fun n => (M:ℝ)*t n^(-1/4:ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_apply,neg_div] using ((_root_.tendsto_rpow_neg_atTop (y := (1/4:ℝ)) (by norm_num)).comp ht).const_mul (M:ℝ)
  apply squeeze_zero' _ _ hv
  · filter_upwards [hd0] with n hn
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg M) _) hn
  · filter_upwards [hd,ht.eventually_gt_atTop 1] with n hdn htn
    have hb := (bounds hM htn).2.2
    calc
      _ ≤ (M:ℝ)^(length M (t n))*t n^(-1/2:ℝ) :=
        mul_le_mul_of_nonneg_left hdn (pow_nonneg (Nat.cast_nonneg M) _)
      _ ≤ ((M:ℝ)*t n^(1/4:ℝ))*t n^(-1/2:ℝ) :=
        mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [mul_assoc,←Real.rpow_add (by linarith : 0<t n)]; norm_num
end
end PlanarUnitDistances.LogHistory

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.BudgetParameters
open Filter CommonTemplate
noncomputable section

lemma vanishing_limit : Tendsto vanishing atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R:=ℝ)))

end
end PlanarUnitDistances.BudgetParameters

namespace PlanarUnitDistances.IncidenceBook
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale ActualScoreBook LevelSnapshot BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params) (i : ℕ)
lemma capacity_pos : 0 < capacity a := pow_pos a.m_pos _
end
end PlanarUnitDistances.IncidenceBook

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_RareBudget
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceNoise
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params)
lemma tpos (i : ℕ) : 0 < s.t i := by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]
lemma dp_nonneg (i : ℕ) : 0 ≤ dp s i := Real.rpow_nonneg (tpos s i).le _
lemma limit_oai : Tendsto (noise s a) atTop (nhds 0) := by
  have h₀ : Tendsto (fun i => |(2*Real.log 2+4)/scale s i|) atTop (nhds 0) := by
    simpa only [abs_zero] using (tendsto_const_nhds.div_atTop (scale_limit s)).abs
  have h₁ : Tendsto (collision s a) atTop (nhds 0) :=
    LogHistory.density_limit (capacity_pos a) s.t (dp s) s.tendsto
      (Eventually.of_forall (dp_nonneg s)) (Eventually.of_forall (fun _ => le_rfl))
  have hi := LogHistory.ratio_limit (capacity_pos a) s.t
    (fun i => IncidenceSequence.information (s.P i) (s.Q i)) s.tendsto
    (Eventually.of_forall (fun i => (s.good i).information_nonneg)) s.information_limit
  have h₂ : Tendsto (rootInfo s a) atTop (nhds 0) := by
    exact hi.rpow_const_nhds_zero (by norm_num)
  change Tendsto (fun i => |(2*Real.log 2+4)/scale s i|+collision s a i+vanishing i+rootInfo s a i) atTop (nhds 0)
  convert ((h₀.add h₁).add vanishing_limit).add h₂ using 1; norm_num
end
end PlanarUnitDistances.IncidenceNoise

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.IncidenceNoise.limit_oai := @OAI.PlanarUnitDistances.IncidenceNoise.limit_oai
