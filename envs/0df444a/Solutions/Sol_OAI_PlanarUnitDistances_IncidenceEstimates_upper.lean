-- Prove2me | solution 1 for OAI.PlanarUnitDistances.IncidenceEstimates.upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T03:01:18.372024+00:00
-- url     : https://prove2.me/submissions/aa4ae589-6dab-4578-83fa-bd27b24c77cf

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000

section
-- module Solutions.OAIQ2_Uni.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Cross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma avg_congr (μ : Law X) {f g : X → ℝ} (h : ∀ x, f x = g x) : avg μ f = avg μ g := by
  unfold avg
  exact sum_congr rfl (fun x _ => congrArg (μ.val x * ·) (h x))

lemma avg_const (μ : Law X) (c : ℝ) : avg μ (fun _ => c) = c := by
  simp [avg,← sum_mul,μ.total]
lemma avg_add (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x+g x)=avg μ f+avg μ g := by simp [avg,mul_add,sum_add_distrib]
lemma avg_sub (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x-g x)=avg μ f-avg μ g := by simp [avg,mul_sub,sum_sub_distrib]
lemma avg_smul (μ : Law X) (c : ℝ) (f : X  →  ℝ) :
    avg μ (fun x => c*f x)=c*avg μ f := by simp [avg,mul_left_comm, mul_sum]
lemma avg_mono (μ : Law X) {f g : X  →  ℝ} (h : ∀ x,f x ≤ g x) : avg μ f ≤ avg μ g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x)
lemma avg_le_const (μ : Law X) {f : X  →  ℝ} {c : ℝ} (h : ∀ x,f x ≤ c) : avg μ f ≤ c :=
  (avg_mono μ h).trans_eq (avg_const μ c)
lemma event_le_one (μ : Law X) (P : X  →  Prop) : event μ P ≤ 1 := by
  classical
  apply avg_le_const; intro x; split <;> norm_num
lemma event_mono (μ : Law X) {P Q : X  →  Prop} (h : ∀ x,P x → Q x) : event μ P ≤ event μ Q := by
  classical
  apply avg_mono; intro x; split_ifs <;> simp_all

lemma pair_avg (μ : Law X) (ν : Law Y) (f : X×Y → ℝ) :
    avg (pair μ ν) f=avg μ (fun x => avg ν (fun y => f (x,y))) := by
  simp [avg,pair,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma pair_fst (μ : Law X) (ν : Law Y) (f : X → ℝ) :
    avg (pair μ ν) (fun x => f x.1)=avg μ f := by
  rw [pair_avg]; simp_rw [avg_const]
lemma pair_snd (μ : Law X) (ν : Law Y) (f : Y → ℝ) :
    avg (pair μ ν) (fun x => f x.2)=avg ν f := by
  rw [pair_avg]; dsimp only; rw [avg_const]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.StarScore
open FiniteLaw StrictCross
noncomputable section
variable {X A B : Type*} [Fintype X]

lemma frequency_nonneg (μ : Law X) (bit : X  →  Bool) : 0 ≤ frequency μ bit := event_nonneg _ _
lemma frequency_le_one (μ : Law X) (bit : X  →  Bool) : frequency μ bit ≤ 1 := event_le_one _ _
lemma variation_nonneg (μ : Law X) (bit : X  →  Bool) : 0 ≤ variation μ bit := by
  unfold variation
  exact mul_nonneg (mul_nonneg (by norm_num) (frequency_nonneg _ _))
    (sub_nonneg.mpr (frequency_le_one _ _))
lemma variation_le_half (μ : Law X) (bit : X  →  Bool) : variation μ bit ≤ 1/2 := by
  unfold variation; nlinarith [sq_nonneg (frequency μ bit-1/2)]

end
end PlanarUnitDistances.StarScore

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
open scoped Classical
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma atom_le_fiber (μ : Law X) (φ : X → Y) (x : X) : μ.val x ≤ fiberMass μ φ (φ x) := by
  classical
  rw [fiberMass_eq]
  have h := single_le_sum (s := univ) (f := fun y => if φ y=φ x then μ.val y else 0)
    (fun y _ => by split_ifs <;> simp [μ.nonneg]) (mem_univ x)
  simpa using h

lemma push_avg (μ : Law X) (φ : X → Y) (g : Y → ℝ) :
    avg (push μ φ) g = avg μ (fun x => g (φ x)) := by
  classical
  unfold avg push
  simp only [fiberMass_eq,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp

omit [Fintype Y] in
lemma cond_weight (μ : Law X) (φ : X → Y) (y : Y) (x : X) :
    fiberMass μ φ y * (cond μ φ y).val x = if φ x=y then μ.val x else 0 := by
  classical
  by_cases hy : 0 < fiberMass μ φ y
  · simp only [cond,hy,↓reduceDIte]
    split_ifs
    · field_simp
    · ring
  · have hz := le_antisymm (le_of_not_gt hy) (fiberMass_nonneg μ φ y)
    simp only [hz,zero_mul]
    split_ifs with hxy
    · have h := atom_le_fiber μ φ x
      rw [hxy,hz] at h
      exact (le_antisymm h (μ.nonneg x)).symm
    · rfl

lemma cond_tower (μ : Law X) (φ : X → Y) (f : X → ℝ) :
    avg (push μ φ) (fun y => avg (cond μ φ y) f) = avg μ f := by
  classical
  unfold avg
  simp only [push,mul_sum,← mul_assoc,cond_weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.RareScore
open FiniteLaw CrossStructure
open scoped Classical
noncomputable section
variable {A B X : Type*}

lemma ind_nonneg (h : Prop) : 0≤ ind h := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (h : Prop) : ind h≤1 := by unfold ind; split_ifs <;> norm_num

end
end PlanarUnitDistances.RareScore

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma event_congr (μ : Law X) {P Q : X → Prop} (h : ∀ x,P x ↔ Q x) :
    event μ P=event μ Q := le_antisymm (event_mono μ (fun x => (h x).mp))
      (event_mono μ (fun x => (h x).mpr))

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Wedges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma mix_avg (μ : Law X) (ν : X → Law Y) (f : Y → ℝ) :
    avg (mix μ ν) f = avg μ (fun x => avg (ν x) f) := by
  simp only [avg,mix,sum_mul,mul_sum,mul_assoc]
  rw [sum_comm]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]
lemma left_val (π : Law (P×Q)) (p : P) : (left π).val p = ∑q,π.val (p,q) := by
  simp only [left,push,fiberMass_eq,Fintype.sum_prod_type]
  rw [sum_comm]
  simp
lemma right_val (π : Law (P×Q)) (q : Q) : (right π).val q = ∑p,π.val (p,q) := by
  simp [right,push,fiberMass_eq,Fintype.sum_prod_type]
lemma row_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (left π).val p*(row π p).val q=π.val (p,q) := by
  simp only [row,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.2=q then fiberMass π Prod.fst p*(cond π Prod.fst p).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma col_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (right π).val q*(col π q).val p=π.val (p,q) := by
  simp only [col,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.1=p then fiberMass π Prod.snd q*(cond π Prod.snd q).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma row_val (π : Law (P×Q)) {p : P} (hp : 0<(left π).val p) (q : Q) :
    (row π p).val q=π.val (p,q)/(left π).val p := by
  apply (eq_div_iff hp.ne').mpr
  simpa only [mul_comm] using row_weight π p q
lemma col_val (π : Law (P×Q)) {q : Q} (hq : 0<(right π).val q) (p : P) :
    (col π q).val p=π.val (p,q)/(right π).val q := by
  apply (eq_div_iff hq.ne').mpr
  simpa only [mul_comm] using col_weight π p q
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.TemplateCoupling
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

lemma slice_weight (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (pq : P×Q) :
    (templates π a).val θ*(slice π a θ).val pq=π.val pq*(a pq.2).val θ := by
  exact col_weight (joint π a) pq θ
end
end PlanarUnitDistances.TemplateCoupling

end OAI
end

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

lemma history_card (C : Type*) [Fintype C] (n : ℕ) :
    Fintype.card (History C n) = (Fintype.card C)^n := by
  induction n with
  | zero =>
      calc
        _ = Fintype.card PUnit := Fintype.card_congr (Equiv.refl _)
        _ = _ := by rw [Fintype.card_punit, pow_zero]
  | succ n ih =>
      calc
        _ = Fintype.card (History C n × C) := Fintype.card_congr (Equiv.refl _)
        _ = _ := by rw [Fintype.card_prod, ih, pow_succ]

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

namespace PlanarUnitDistances.UnitCodegree
open Polynomial Complex
open scoped ComplexConjugate

lemma unit_distance_equation (p q : ℂ) (h : dist p q = 1) :
    (q-p)*(conj q-conj p) = 1 := by
  rw [← map_sub, mul_conj, normSq_eq_norm_sq, ← dist_eq_norm, dist_comm q p, h]
  norm_num

end PlanarUnitDistances.UnitCodegree

namespace PlanarUnitDistances.UniformGraphLaw
open Finset FiniteLaw FiniteStarCoupling IncidenceEntropy
open scoped Classical BigOperators
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma right_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (q : Q) :
    (right (law E hE)).val q=degree E q/edgeCount E := by
  rw [right_val]
  simp only [law,←sum_div,degree]
lemma left_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (p : P) :
    (left (law E hE)).val p=pointLaw E p := by
  rw [left_val]
  simp only [law,←sum_div,pointLaw]
lemma col_eq (E : P → Q → Prop) (hE : 0<edgeCount E) {q : Q}
    (hq : 0<degree E q) (p : P) :
    (col (law E hE) q).val p=indicator E p q/degree E q := by
  rw [col_val (law E hE) (by rw [right_eq]; exact div_pos hq hE),right_eq]
  change (indicator E p q/edgeCount E)/(degree E q/edgeCount E)=_
  field_simp
lemma row_eq (E : P → Q → Prop) (hE : 0<edgeCount E) {p : P}
    (hp : 0<∑q,indicator E p q) (q : Q) :
    (row (law E hE) p).val q=indicator E p q/(∑q,indicator E p q) := by
  rw [row_val (law E hE) (by rw [left_eq]; exact div_pos hp hE),left_eq]
  change (indicator E p q/edgeCount E)/((∑q,indicator E p q)/edgeCount E)=_
  field_simp

end
end PlanarUnitDistances.UniformGraphLaw

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
lemma left_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) :
    (left (graph P Q he)).val p=CircleIncidence.degree Q p/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.left_eq,IncidenceEntropy.pointLaw,edgeCount_eq,row_count]
lemma row_le (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) (q : Q)
    (hp : 0<CircleIncidence.degree Q p) :
    (row (graph P Q he) p).val q ≤ 1/CircleIncidence.degree Q p := by
  rw [graph,UniformGraphLaw.row_eq _ _ (by rw [row_count]; exact hp),row_count]
  apply div_le_div_of_nonneg_right _ hp.le
  unfold IncidenceEntropy.indicator
  split_ifs <;> norm_num

end
end PlanarUnitDistances.GeometricLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sequence
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

end
end PlanarUnitDistances.IncidenceSequence

namespace PlanarUnitDistances.CommonFieldModel
open scoped Classical
noncomputable section
variable (P Q : Finset Plane)

variable {P Q}

namespace Model
variable (M : Model P Q)
lemma point_injective : Function.Injective (M.z ∘ Sum.inl) := by
  intro p r h
  apply Subtype.val_injective
  apply UnitCodegree.zCoordinate.injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inl] using hh
lemma center_injective : Function.Injective (M.z ∘ Sum.inr) := by
  intro q r h
  apply Subtype.val_injective
  apply UnitCodegree.zCoordinate.injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inr] using hh
lemma unit_identity (p : P) (q : Q) (h : dist (p:Plane) (q:Plane)=1) :
    (M.z (.inl p)-M.z (.inr q))*(M.w (.inl p)-M.w (.inr q))=1 := by
  apply Subtype.val_injective
  change ((M.z (.inl p):ℂ)-(M.z (.inr q):ℂ))*((M.w (.inl p):ℂ)-(M.w (.inr q):ℂ))=1
  simp only [M.z_eq,M.w_eq,location,Sum.elim_inl,Sum.elim_inr]
  exact UnitCodegree.unit_distance_equation _ _ (by
    rw [UnitCodegree.zCoordinate.dist_map,dist_comm]; exact h)

lemma wpoint_injective : Function.Injective (M.w ∘ Sum.inl) := by
  intro p r h
  apply M.point_injective
  apply Subtype.val_injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simp only [Function.comp_apply,M.w_eq,location,Sum.elim_inl] at hh
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inl] using star_injective hh
lemma sub_mem (v r : P⊕Q) : M.z v-M.z r ∈ M.support :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(v,r),Finset.mem_univ _,rfl⟩))
lemma wsub_mem (v r : P⊕Q) : M.w v-M.w r ∈ M.support :=
  Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨(v,r),Finset.mem_univ _,rfl⟩))
lemma difference_mem (v r s : P⊕Q) :
    ((M.z v-M.z r)-(M.z v-M.z s))*((M.z v-M.z r)⁻¹-(M.z v-M.z s)⁻¹) ∈ M.support :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v,r,s),Finset.mem_univ _,rfl⟩)
end Model
end
end PlanarUnitDistances.CommonFieldModel

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_AbsoluteValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset
noncomputable section

section Entries
variable (K : Type*) [Field K] [NumberField K]

lemma infiniteEntry_count : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K :=
  AlgHom.card ℚ K ℂ

end Entries

end
end PlanarUnitDistances.WeightedAbsoluteValues

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_HeightTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x-y| < 1 := by
  have hx₁ := Int.floor_le x
  have hx₂ := Int.lt_floor_add_one x
  have hy₁ := Int.floor_le y
  have hy₂ := Int.lt_floor_add_one y
  rw [← h] at hy₁ hy₂
  rw [abs_lt]
  constructor <;> linarith

lemma norm_le_of_same_grid {r : ℝ} (hr : 0 < r) {z w : ℂ} {u : ℝ × ℝ}
    (h : gridLabel r z u = gridLabel r w u) : ‖z-w‖ ≤ 2*r := by
  have hx := abs_sub_lt_one_of_floor_eq (congrArg Prod.fst h)
  have hy := abs_sub_lt_one_of_floor_eq (congrArg Prod.snd h)
  rw [add_sub_add_right_eq_sub,← sub_div,abs_div,abs_of_pos hr,div_lt_one hr] at hx hy
  calc
    _ ≤ |(z-w).re|+|(z-w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ r+r := add_le_add hx.le hy.le
    _ = 2*r := by ring

end
end PlanarUnitDistances.GridShift

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_States
attribute [-instance] _root_.OAI.PlanarUnitDistances.LevelScale.instIsFiniteMeasureProdPlaceRealMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteStates
open MeasureTheory Set Real
open scoped Classical
noncomputable section
variable {V : Type*}

lemma label_eq_iff (r : Setoid V) (x y : V) : label r x=label r y ↔ r.r x y := by
  constructor
  · intro he
    have hh := congrFun he y
    simpa only [label,r.refl y,decide_true,decide_eq_true_eq] using hh
  · intro h
    funext z
    apply Bool.decide_congr
    exact ⟨fun hx => r.trans (r.symm h) hx,fun hy => r.trans h hy⟩

end
end PlanarUnitDistances.FiniteStates

namespace PlanarUnitDistances.FiniteLevels
open MeasureTheory Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSingletonClass J] in
lemma integral_eq (weight : ℝ≥0) (l u : J → ℝ) (f : J × ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀x, |f x| ≤ M) :
    (∫x, f x ∂measure weight l u) =
      (weight : ℝ) * ∑ j, ∫ s in Icc (l j) (u j), f (j,s) := by
  have hm (j : J) : Measurable (fun s : ℝ => (j,s)) :=
    measurable_const.prodMk measurable_id
  have hi (j : J) : Integrable f
      (Measure.map (fun s : ℝ => (j,s)) (volume.restrict (Icc (l j) (u j)))) := by
    apply Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x
  unfold measure
  rw [integral_finsetSum_measure (fun j _ => (hi j).smul_measure_nnreal (c := weight))]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact integral_map (hm j).aemeasurable hf.aestronglyMeasurable

end
end PlanarUnitDistances.FiniteLevels

namespace PlanarUnitDistances.BudgetPlaces
open Real Finset
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]

lemma differenceProduct_ne_zero {d d' : K} (h : d ≠ d') :
    differenceProduct d d' ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr h) (sub_ne_zero.mpr (inv_injective.ne h))

lemma inv_difference_abs (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d ≠ 0) (hd' : d' ≠ 0) :
    v (d⁻¹-d'⁻¹) = v (d-d')/(v d*v d') := by
  have he : d⁻¹-d'⁻¹ = -(d-d')/(d*d') := by field_simp; ring
  rw [he,map_div₀,v.map_neg,v.map_mul]

theorem place_identity (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    -log (v (differenceProduct d d')) =
      2*alpha v d d'-(max (threshold v d) (threshold v d')-
        min (threshold v d) (threshold v d')) := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have hdv := v.pos hd
  have hdv' := v.pos hd'
  have hI := v.pos (sub_ne_zero.mpr (inv_injective.ne hdd))
  rw [differenceProduct,v.map_mul,log_mul hD.ne' hI.ne',inv_difference_abs v hd hd',
    log_div hD.ne' (mul_ne_zero hdv.ne' hdv'.ne'),log_mul hdv.ne' hdv'.ne']
  unfold alpha threshold
  have hm := min_add_max (-log (v d)) (-log (v d'))
  linarith

lemma alpha_nonneg_nonarch (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {d d' : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    0 ≤ alpha v d d' := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have htri : v (d-d') ≤ max (v d) (v d') := by
    simpa only [sub_eq_add_neg,v.map_neg] using hv d (-d')
  unfold alpha threshold
  by_cases hh : v d ≤ v d'
  · rw [max_eq_right hh] at htri
    have hlog := log_le_log (v.pos hd) hh
    rw [min_eq_right (by linarith)]
    linarith [log_le_log hD htri]
  · have hh' := (le_of_not_ge hh)
    rw [max_eq_left hh'] at htri
    have hlog := log_le_log (v.pos hd') hh'
    rw [min_eq_left (by linarith)]
    linarith [log_le_log hD htri]

lemma alpha_add_log_two_nonneg (v : AbsoluteValue K ℝ)
    {d d' : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    0 ≤ alpha v d d'+log 2 := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have htri : v (d-d') ≤ v d+v d' := by
    simpa only [sub_eq_add_neg,v.map_neg] using v.add_le d (-d')
  unfold alpha threshold
  by_cases hh : v d ≤ v d'
  · have hlog := log_le_log (v.pos hd) hh
    have ht : v (d-d') ≤ 2*v d' := by linarith
    have hLt := log_le_log hD ht
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (v.pos hd').ne'] at hLt
    rw [min_eq_right (by linarith)]
    linarith
  · have hh' := (le_of_not_ge hh)
    have hlog := log_le_log (v.pos hd') hh'
    have ht : v (d-d') ≤ 2*v d := by linarith
    have hLt := log_le_log hD ht
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (v.pos hd).ne'] at hLt
    rw [min_eq_left (by linarith)]
    linarith

section Global
open PlanarUnitDistances.WeightedAbsoluteValues
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in

theorem arch_allowance :
    (∑ _σ : K →ₐ[ℚ] ℂ, 2*log 2)/(Module.finrank ℚ K : ℝ) = 2*log 2 := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  simp only [sum_const,card_univ,nsmul_eq_mul,infiniteEntry_count]
  field_simp

end Global
end
end PlanarUnitDistances.BudgetPlaces

namespace PlanarUnitDistances.PlaceLevels
open Finset Real WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

lemma log_off_support {S : Finset K} {x : K} (hx : x∈S)
    {v : Nat.Primes × Gal(K/ℚ)} (hv : v∉finiteSupport K S) :
    log (finiteEntry K v.1 v.2 x)=0 := by
  by_cases h0 : x=0
  · simp [h0]
  have hp : v.1.val ∉ rootDenominators K x ∪ rootDenominators K x⁻¹ := by
    intro hh
    apply hv
    exact mem_biUnion.mpr ⟨x,hx,mem_product.mpr ⟨mem_subtype.mpr hh,mem_univ _⟩⟩
  rw [finiteEntry_eq_one_off_support K h0 _ _ hp,log_one]

lemma radius_nonneg (S : Finset K) (v : Place K S) : 0≤radius K S v :=
  sum_nonneg (fun _ _ => abs_nonneg _)
lemma log_le_radius {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    |log (av K v x)|≤radius K S v := by
  exact single_le_sum (fun y _ => abs_nonneg (log (av K v y))) hx
lemma threshold_in_range {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    -radius K S v ≤ -log (av K v x) ∧ -log (av K v x) ≤ radius K S v := by
  have h := abs_le.mp (log_le_radius K hx v)
  constructor <;> linarith
lemma log_in_range {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    -radius K S v ≤ log (av K v x) ∧ log (av K v x) ≤ radius K S v :=
  abs_le.mp (log_le_radius K hx v)

lemma sum_logs {S : Finset K} {x : K} (hx : x∈S) :
    (∑v : Place K S,log (av K v x)) =
      (∑σ : K →ₐ[ℚ] ℂ,log (infiniteEntry K σ x))+
      ∑ᶠv : Nat.Primes × Gal(K/ℚ), log (finiteEntry K v.1 v.2 x) := by
  change (∑v : (K →ₐ[ℚ] ℂ) ⊕ ↥(finiteSupport K S),log (av K v x))=_
  rw [Fintype.sum_sum_type]
  congr 1
  change (∑v : ↥(finiteSupport K S), log (finiteEntry K v.val.1 v.val.2 x))=_
  rw [Finset.sum_coe_sort (finiteSupport K S) (fun v => log (finiteEntry K v.1 v.2 x))]
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  by_contra hs
  exact hv (log_off_support K hx hs)

lemma sum_log_product_formula [IsGalois ℚ K] {S : Finset K} {x : K}
    (hx : x∈S) (h0 : x≠0) :
    (∑v : Place K S,log (av K v x))/(Module.finrank ℚ K:ℝ)=0 := by
  rw [sum_logs K hx]
  exact weighted_log_product_formula K h0
end
end PlanarUnitDistances.PlaceLevels

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma abs_bit_sub_eq (a b s : ℝ) :
    |bit a s - bit b s| = (Ico (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) s := by
  by_cases ha : s < a <;> by_cases hb : s < b <;>
    simp [bit,ha,hb,Set.indicator,mem_Ico]

lemma bit_sub_integral {l u a b : ℝ} (hla : l ≤ a) (hua : a ≤ u)
    (hlb : l ≤ b) (hub : b ≤ u) :
    ∫ s in Icc l u, |bit a s - bit b s| = |a-b| := by
  simp_rw [abs_bit_sub_eq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  rw [measureReal_restrict_apply measurableSet_Ico]
  have hsub : Ico (min a b) (max a b) ⊆ Icc l u := by
    intro s hs
    exact ⟨(le_min hla hlb).trans hs.1, hs.2.le.trans (max_le hua hub)⟩
  rw [inter_eq_left.mpr hsub,Real.volume_real_Ico]
  simp [smul_eq_mul,max_sub_min_eq_abs,abs_sub_comm]

end
end PlanarUnitDistances.ThresholdProfiles

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Predictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.TemplateCollision
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

lemma collision_eq {X : Type*} [Fintype X] (μ : Law X) :
    event (pair μ μ) (fun xx => xx.1=xx.2)=∑x,μ.val x^2 := by
  simp [event,avg,pair,Fintype.sum_prod_type,pow_two]

lemma atom_le_one {X : Type*} [Fintype X] (μ : Law X) (x : X) : μ.val x≤1 := by
  simpa only [μ.total] using single_le_sum (fun y _ => μ.nonneg y) (mem_univ x)

lemma slice_collision (π : Law (P×Q)) (a : Q → Law Θ) (p : P) (θ : Θ)
    {d : ℝ} (hp : ∀q,π.val (p,q)≤d*(left π).val p) :
    (templates π a).val θ*(left (slice π a θ)).val p*
      event (pair (row (slice π a θ) p) (row (slice π a θ) p)) (fun qq => qq.1=qq.2)≤
      d*(left π).val p := by
  rw [collision_eq,mul_sum]
  calc
    _ = ∑q,π.val (p,q)*(a q).val θ*(row (slice π a θ) p).val q := by
      apply sum_congr rfl
      intro q _
      rw [pow_two,←mul_assoc,mul_assoc ((templates π a).val θ),
        row_weight,slice_weight]
    _ ≤ ∑q,(d*(left π).val p)*(row (slice π a θ) p).val q := by
      apply sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_right _ ((row (slice π a θ) p).nonneg q)
      exact (mul_le_of_le_one_right (π.nonneg (p,q)) (atom_le_one (a q) θ)).trans (hp q)
    _ = _ := by rw [←mul_sum,(row (slice π a θ) p).total,mul_one]

theorem weighted (π : Law (P×Q)) (a : Q → Law Θ) (f : P → ℝ) (hf : ∀p,0≤f p)
    {d : ℝ} (hp : ∀p q,π.val (p,q)≤d*(left π).val p) :
    avg (templates π a) (fun θ => avg (left (slice π a θ)) (fun p =>
      f p*event (pair (row (slice π a θ) p) (row (slice π a θ) p)) (fun qq => qq.1=qq.2)))≤
      (Fintype.card Θ:ℝ)*d*avg (left π) f := by
  simp only [avg,mul_sum]
  calc
    _ = ∑p,∑θ,f p*((templates π a).val θ*(left (slice π a θ)).val p*
      event (pair (row (slice π a θ) p) (row (slice π a θ) p)) (fun qq => qq.1=qq.2)) := by
      rw [sum_comm]
      apply sum_congr rfl; intro p _
      apply sum_congr rfl; intro θ _
      ring
    _ ≤ ∑p,∑_θ : Θ,f p*(d*(left π).val p) := by
      apply sum_le_sum; intro p _
      apply sum_le_sum; intro θ _
      exact mul_le_mul_of_nonneg_left (slice_collision π a p θ (hp p)) (hf p)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; apply sum_congr rfl; intro p _; ring

lemma row_weighted (π : Law (P×Q)) (f : P → ℝ) (hf : ∀p,0≤f p)
    {d : ℝ} (hp : ∀p q,π.val (p,q)≤d*(left π).val p) :
    avg (left π) (fun p => f p*event (pair (row π p) (row π p)) (fun qq => qq.1=qq.2))≤
      d*avg (left π) f := by
  simp only [avg,collision_eq,mul_sum]
  apply sum_le_sum
  intro p _
  calc
    _ = f p*∑q,π.val (p,q)*(row π p).val q := by
      rw [mul_sum]
      apply sum_congr rfl; intro q _
      rw [pow_two,←row_weight π p q]
      ring
    _ ≤ f p*∑q,(d*(left π).val p)*(row π p).val q := by
      apply mul_le_mul_of_nonneg_left _ (hf p)
      apply sum_le_sum; intro q _
      exact mul_le_mul_of_nonneg_right (hp p q) ((row π p).nonneg q)
    _ = _ := by rw [←mul_sum,(row π p).total]; ring
end
end PlanarUnitDistances.TemplateCollision

namespace PlanarUnitDistances.PredictionCoupling
open Finset FiniteLaw FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P H A B : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]

lemma first (μ : Law P) (h : P → H) (f : P → ℝ) :
    avg (coupling μ h) (fun pp => f pp.1)=avg μ f := by
  rw [coupling,mix_avg]
  simp_rw [pair_fst]
  exact cond_tower μ h f
lemma second (μ : Law P) (h : P → H) (f : P → ℝ) :
    avg (coupling μ h) (fun pp => f pp.2)=avg μ f := by
  rw [coupling,mix_avg]
  simp_rw [pair_snd]
  exact cond_tower μ h f

lemma cond_diagonal (μ : Law P) (h : P → H) (j : H) {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀p,μ.val p ≤ d) :
    (push μ h).val j*event (pair (cond μ h j) (cond μ h j)) (fun pp => pp.1=pp.2) ≤ d := by
  rw [TemplateCollision.collision_eq,mul_sum]
  calc
    _ = ∑p,(if h p=j then μ.val p else 0)*(cond μ h j).val p := by
      apply sum_congr rfl
      intro p _
      rw [pow_two,←mul_assoc]
      exact congrArg (fun t => t*(cond μ h j).val p) (cond_weight μ h j p)
    _ ≤ ∑p,d*(cond μ h j).val p := by
      apply sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (by split_ifs; exact hm p; exact hd) ((cond μ h j).nonneg p)
    _ = d := by rw [←mul_sum,(cond μ h j).total,mul_one]

theorem diagonal (μ : Law P) (h : P → H) {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    event (coupling μ h) (fun pp => pp.1=pp.2) ≤ (Fintype.card H:ℝ)*d := by
  unfold event
  rw [coupling,mix_avg]
  calc
    _ ≤ ∑_j : H,d := sum_le_sum (fun j _ => cond_diagonal μ h j hd hm)
    _ = _ := by simp

lemma coordinate_collision (μ : Law P) (φ : P → A) :
    event (pair μ μ) (fun pp => φ pp.1=φ pp.2)=collision μ φ := by
  unfold event
  rw [pair_avg]
  have he : (fun p => avg μ (fun q => if φ p=φ q then (1:ℝ) else 0))=
      (fun p => fiberMass μ φ (φ p)) := by
    funext p
    exact event_congr μ (fun q => eq_comm)
  rw [he,←push_avg μ φ (fun a => fiberMass μ φ a)]
  simp only [avg,push,collision,fiberMass,pow_two]

lemma collision_push (μ : Law P) (x : P → A×B) :
    collision (push μ x) Prod.fst=collision μ (fun p => (x p).1) ∧
    collision (push μ x) Prod.snd=collision μ (fun p => (x p).2) := by
  constructor <;> unfold collision event <;> simp_rw [push_avg]

lemma tau_pair (μ : Law P) (x : P → A×B) :
    avg (pair μ μ) (fun pp => (if (x pp.1).1=(x pp.2).1 then 1 else 0)+
      (if (x pp.1).2=(x pp.2).2 then 1 else 0)-1)=tau (push μ x) := by
  rw [avg_sub,avg_add,avg_const]
  change event (pair μ μ) (fun pp => (x pp.1).1=(x pp.2).1)+
    event (pair μ μ) (fun pp => (x pp.1).2=(x pp.2).2)-1=_
  rw [coordinate_collision μ (fun p => (x p).1),coordinate_collision μ (fun p => (x p).2),tau,(collision_push μ x).1,(collision_push μ x).2]

theorem tau_eq (μ : Law P) (h : P → H) (x : P → A×B) :
    avg (coupling μ h) (fun pp => (if (x pp.1).1=(x pp.2).1 then 1 else 0)+
      (if (x pp.1).2=(x pp.2).2 then 1 else 0)-1)=
      avg μ (fun p => tau (push (cond μ h (h p)) x)) := by
  rw [coupling,mix_avg]
  simp_rw [tau_pair]
  exact push_avg μ h _
end
end PlanarUnitDistances.PredictionCoupling

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma avg_comm (μ : Law X) (ν : Law Y) (f : X → Y → ℝ) :
    avg μ (fun x => avg ν (f x)) = avg ν (fun y => avg μ (fun x => f x y)) := by
  simp only [avg,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteLaw
open MeasureTheory Finset Set
open scoped Classical
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma fromMeasure_avg (μ : Measure S) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ) (f : S → ℝ) :
    avg (fromMeasure μ hμ) f=(∫s,f s ∂μ)/μ.real Set.univ := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [avg,fromMeasure,smul_eq_mul]
  rw [Finset.sum_div]
  apply sum_congr rfl; intro s _; ring

variable {Ω : Type*} [MeasurableSpace Ω]

lemma compress_avg (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ)
    (c : Ω → S) (hc : Measurable c) (f : S → ℝ) :
    avg (compress μ hμ c hc) f=(∫s,f (c s) ∂μ)/μ.real Set.univ := by
  rw [compress,fromMeasure_avg,map_real_univ μ c hc,
    integral_map hc.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scale
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceScale
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence
open scoped Classical
noncomputable section
variable (s : Sequence)
lemma support (n : ℕ) (p : s.P n) (q : s.Q n) (h : 0<(graph s n).val (p,q)) :
    GeometricLaw.E (s.P n) (s.Q n) p q := by
  change 0<IncidenceEntropy.indicator (GeometricLaw.E (s.P n) (s.Q n)) p q/_ at h
  by_contra hn
  simp [IncidenceEntropy.indicator,hn] at h
lemma point_bound (n : ℕ) (p : s.P n) : (left (graph s n)).val p≤ s.t n^(-1/2:ℝ) := by
  rw [graph,GeometricLaw.left_eq]
  exact (s.good n).atomUpper p p.property
lemma row_bound (n : ℕ) (p : s.P n) (q : s.Q n) :
    (row (graph s n) p).val q≤1/(s.t n^(1/2:ℝ)) := by
  have hp := (s.good n).point_degree_pos p
  have he := (s.good n).positive
  have hb := (le_div_iff₀ he).mp ((s.good n).atomP p p.property)
  have hd : s.t n^(1/2:ℝ)≤CircleIncidence.degree (s.Q n) p :=
    (s.good n).degreeP.trans (by simpa only [div_mul_eq_mul_div] using hb)
  exact (GeometricLaw.row_le _ _ he p q hp).trans
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith [s.large n,Nat.cast_nonneg (α:=ℝ) n]) _) hd)
end
end PlanarUnitDistances.IncidenceScale

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Slots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LevelGeometry
open MeasureTheory Set Real FiniteStates PlaceLevels LevelStates BudgetPlaces
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [NumberField K]

lemma allowance_nonneg {S : Finset K} (v : Place K S) : 0 ≤ allowance v := by
  cases v <;> simp [allowance,Real.log_nonneg]

lemma first_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (h : (state S z w u (v,s) x).1=(state S z w u (v,s) y).1) :
    av K v (z x-z y) ≤ exp (allowance v-s) := by
  cases v with
  | inl σ =>
    have hg : GridShift.gridLabel (exp (-s)) (σ (z x)) (u σ).1=
        GridShift.gridLabel (exp (-s)) (σ (z y)) (u σ).1 :=
      (label_eq_iff _ _ _).mp h
    have hb := GridShift.norm_le_of_same_grid (exp_pos (-s)) hg
    simpa only [av,WeightedAbsoluteValues.infiniteEntry_apply,map_sub,allowance,
      sub_eq_add_neg,map_add,map_neg,exp_add,exp_log (by norm_num : (0:ℝ)<2)] using hb
  | inr v =>
    have hb : WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2 (z x-z y) ≤ exp (-s) :=
      (label_eq_iff _ _ _).mp h
    simpa only [av,allowance,zero_sub] using hb

lemma second_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (h : (state S z w u (v,s) x).2=(state S z w u (v,s) y).2) :
    av K v (w x-w y) ≤ exp (allowance v+s) := by
  cases v with
  | inl σ =>
    have hg : GridShift.gridLabel (exp s) (σ (w x)) (u σ).2=
        GridShift.gridLabel (exp s) (σ (w y)) (u σ).2 :=
      (label_eq_iff _ _ _).mp h
    have hb := GridShift.norm_le_of_same_grid (exp_pos s) hg
    simpa only [av,WeightedAbsoluteValues.infiniteEntry_apply,map_sub,allowance,
      exp_add,exp_log (by norm_num : (0:ℝ)<2)] using hb
  | inr v =>
    have hb : WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2 (w x-w y) ≤ exp s :=
      (label_eq_iff _ _ _).mp h
    simpa only [av,allowance,zero_add] using hb

lemma first_log_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (hxy : z x≠z y) (h : (state S z w u (v,s) x).1=(state S z w u (v,s) y).1) :
    log (av K v (z x-z y)) ≤ allowance v-s := by
  have hb := log_le_log ((av K v).pos (sub_ne_zero.mpr hxy)) (first_bound S z w u v s x y h)
  simpa only [log_exp] using hb
lemma second_log_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (hxy : w x≠w y) (h : (state S z w u (v,s) x).2=(state S z w u (v,s) y).2) :
    log (av K v (w x-w y)) ≤ allowance v+s := by
  have hb := log_le_log ((av K v).pos (sub_ne_zero.mpr hxy)) (second_bound S z w u v s x y h)
  simpa only [log_exp] using hb

omit [NumberField K] in
lemma opposite_log {d d' : K} (v : AbsoluteValue K ℝ)
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') :
    log (v (d⁻¹-d'⁻¹)) = max (threshold v d) (threshold v d')-alpha v d d' := by
  rw [inv_difference_abs v hd hd']
  rw [log_div ((v.pos (sub_ne_zero.mpr hdd)).ne') (mul_ne_zero ((v.pos hd).ne') ((v.pos hd').ne')),
    log_mul ((v.pos hd).ne') ((v.pos hd').ne')]
  unfold alpha threshold
  have hm := min_add_max (-log (v d)) (-log (v d'))
  linarith

theorem positive_flanks (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y y' : V)
    (hu : (z x-z y)*(w x-w y)=1) (hu' : (z x-z y')*(w x-w y')=1)
    (hyy : z y≠z y') :
    let d := z x-z y
    let d' := z x-z y'
    let b := min (threshold (av K v) d) (threshold (av K v) d')
    let b' := max (threshold (av K v) d) (threshold (av K v) d')
    let T := alpha (av K v) d d'+allowance v
    ((s<threshold (av K v) d ∧ s<threshold (av K v) d' ∧
        (state S z w u (v,s) y).2=(state S z w u (v,s) y').2) → s∈Icc (b-T) b) ∧
    ((threshold (av K v) d ≤ s ∧ threshold (av K v) d' ≤ s ∧
        (state S z w u (v,s) y).1=(state S z w u (v,s) y').1) → s∈Icc b' (b'+T)) := by
  dsimp only
  have hd : z x-z y≠0 := left_ne_zero_of_mul_eq_one hu
  have hd' : z x-z y'≠0 := left_ne_zero_of_mul_eq_one hu'
  have hdd : z x-z y≠z x-z y' := by exact sub_right_injective.ne hyy
  have hw : w x-w y=(z x-z y)⁻¹ := eq_inv_of_mul_eq_one_right hu
  have hw' : w x-w y'=(z x-z y')⁻¹ := eq_inv_of_mul_eq_one_right hu'
  have he : w y-w y'=-((z x-z y)⁻¹-(z x-z y')⁻¹) := by rw [←hw,←hw']; ring
  have hz : z y-z y'=-((z x-z y)-(z x-z y')) := by ring
  have hwyy : w y≠w y' := by
    intro hh
    have hi : (z x-z y)⁻¹=(z x-z y')⁻¹ := by rw [←hw,←hw',hh]
    exact hdd (inv_injective hi)
  have hm : min (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')) ≤
      max (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')) := min_le_max
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    have hb := second_log_bound S z w u v s y y' hwyy h₃
    rw [he,AbsoluteValue.map_neg,opposite_log (av K v) hd hd' hdd] at hb
    refine ⟨by linarith,(le_min h₁.le h₂.le)⟩
  · rintro ⟨h₁,h₂,h₃⟩
    have hb := first_log_bound S z w u v s y y' hyy h₃
    rw [hz,AbsoluteValue.map_neg] at hb
    refine ⟨max_le h₁ h₂,?_⟩
    unfold alpha threshold at *
    linarith

end
end PlanarUnitDistances.LevelGeometry

namespace PlanarUnitDistances.BudgetIntervals
open Finset Set
open scoped BigOperators
noncomputable section

lemma overlap_le_length {a b l r : ℝ} (hab : a ≤ b) :
    overlap a b l r ≤ b-a := by
  apply max_le
  · linarith
  · linarith [min_le_left b r,le_max_left a l]

lemma overlap_pos_iff {a b l r : ℝ} :
    0 < overlap a b l r ↔ max a l < min b r := by
  simp only [overlap,lt_max_iff,lt_self_iff_false,false_or,sub_pos]

lemma disjoint_overlap_sum {a b c d l r : ℝ} (hbc : b ≤ c) :
    overlap a b l r+overlap c d l r ≤ max 0 (r-l) := by
  by_cases h₁ : 0 < min b r-max a l
  · rw [overlap,max_eq_right h₁.le]
    by_cases h₂ : 0 < min d r-max c l
    · rw [overlap,max_eq_right h₂.le]
      have hbr := min_le_right b r
      have hdl := min_le_right d r
      have hal := le_max_right a l
      have hcl := le_max_left c l
      have hbb := min_le_left b r
      have hr := le_max_right 0 (r-l)
      linarith
    · rw [overlap,max_eq_left (le_of_not_gt h₂),add_zero]
      linarith [min_le_right b r,le_max_right a l,le_max_right 0 (r-l)]
  · rw [overlap,max_eq_left (le_of_not_gt h₁),zero_add]
    apply max_le (le_max_left _ _)
    linarith [min_le_right d r,le_max_right c l,le_max_right 0 (r-l)]

theorem central_envelope {b b' T l r lam : ℝ} (hbb : b ≤ b')
    (hT : 0 ≤ T) (hlam : 0 < lam) (_hlam₁ : lam < 1) :
    max 0 ((1-lam)*2*T+2*lam*(overlap (b-T) b l r+overlap b' (b'+T) l r)-2*T) ≤
      lam*max 0 (r-l)*(if l < b ∧ b < r ∧ l < b' ∧ b' < r then 1 else 0) := by
  let a := overlap (b-T) b l r+overlap b' (b'+T) l r
  have h₁ : overlap (b-T) b l r ≤ T := by
    simpa using overlap_le_length (l := l) (r := r) (show b-T ≤ b by linarith)
  have h₂ : overlap b' (b'+T) l r ≤ T := by
    simpa using overlap_le_length (l := l) (r := r) (show b' ≤ b'+T by linarith)
  have hA : overlap (b-T) b l r+overlap b' (b'+T) l r ≤ 2*T := by linarith
  have hW := disjoint_overlap_sum (a := b-T) (d := b'+T) (l := l) (r := r) hbb
  have hn : 0 ≤ lam*max 0 (r-l) := mul_nonneg hlam.le (le_max_left _ _)
  split_ifs with hi
  · simp only [mul_one]
    apply max_le hn
    nlinarith
  · simp only [mul_zero]
    apply max_le le_rfl
    have ha : overlap (b-T) b l r+overlap b' (b'+T) l r ≤ T := by
      by_contra! he
      have hp₁ : 0 < overlap (b-T) b l r := by linarith
      have hp₂ : 0 < overlap b' (b'+T) l r := by linarith
      have hx := overlap_pos_iff.mp hp₁
      have hy := overlap_pos_iff.mp hp₂
      have hlb : l < b := lt_of_le_of_lt (le_max_right (b-T) l) (hx.trans_le (min_le_left b r))
      have hbr : b' < r := lt_of_le_of_lt (le_max_left b' l) (hy.trans_le (min_le_right (b'+T) r))
      exact hi ⟨hlb,hbb.trans_lt hbr,hlb.trans_le hbb,hbr⟩
    nlinarith

variable {E : Type*} [Fintype E]

lemma interiorMass_nonneg (μ : E → ℝ) (hμ : ∀ e, 0 ≤ μ e) (x : E → ℝ) (l r : ℝ) :
    0 ≤ interiorMass μ x l r := by
  apply sum_nonneg; intro e _; apply mul_nonneg (hμ e); split <;> norm_num

theorem interior_mass_le {μ : E → ℝ} (_hμ : ∀ e, 0 ≤ μ e) (x : E → ℝ)
    {l r δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ s ∈ Ioo l r, |tail μ x s-1/2| ≤ δ) :
    interiorMass μ x l r ≤ 2*δ := by
  classical
  let A := univ.filter (fun e => l < x e ∧ x e < r)
  by_cases ha : A.Nonempty
  · let a := (A.image x).min' (ha.image x)
    let b := (A.image x).max' (ha.image x)
    have haM : a ∈ A.image x := min'_mem _ _
    have hbM : b ∈ A.image x := max'_mem _ _
    obtain ⟨ea,hea,hea'⟩ := mem_image.mp haM
    obtain ⟨eb,heb,heb'⟩ := mem_image.mp hbM
    have hap : l < a ∧ a < r := by
      rw [← hea']; exact (mem_filter.mp hea).2
    have hbp : l < b ∧ b < r := by
      rw [← heb']; exact (mem_filter.mp heb).2
    have hab : a ≤ b := min'_le _ _ hbM
    let u := (l+a)/2
    have hu : u ∈ Ioo l r := by constructor <;> dsimp [u] <;> linarith
    have hum : u < a := by dsimp [u]; linarith
    have hm : interiorMass μ x l r = tail μ x u-tail μ x b := by
      rw [interiorMass,tail,tail,← sum_sub_distrib]
      apply sum_congr rfl
      intro e _
      by_cases he : l < x e ∧ x e < r
      · have heA : e ∈ A := mem_filter.mpr ⟨mem_univ _,he⟩
        have hae : a ≤ x e := min'_le _ _ (mem_image.mpr ⟨e,heA,rfl⟩)
        have heb : x e ≤ b := le_max' _ _ (mem_image.mpr ⟨e,heA,rfl⟩)
        simp [he,hum.trans_le hae,not_lt.mpr heb]
      · by_cases hux : u < x e
        · have hbx : b < x e := by
            by_contra! hle
            exact he ⟨hu.1.trans hux,hle.trans_lt hbp.2⟩
          simp [he,hux,hbx]
        · have hbx : ¬b < x e := by
            intro hh; exact hux (hum.trans_le hab |>.trans hh)
          simp [he,hux,hbx]
    rw [hm]
    have hc₁ := (abs_le.mp (hc u hu)).2
    have hc₂ := (abs_le.mp (hc b hbp)).1
    linarith
  · have hm : interiorMass μ x l r = 0 := by
      apply sum_eq_zero
      intro e _
      have he : ¬(l < x e ∧ x e < r) := by
        intro he
        exact ha ⟨e,mem_filter.mpr ⟨mem_univ _,he⟩⟩
      simp [he]
    rw [hm]; linarith

lemma sorted_interior {x y l r : ℝ} :
    (l < min x y ∧ min x y < r ∧ l < max x y ∧ max x y < r) ↔
    (l < x ∧ x < r) ∧ (l < y ∧ y < r) := by
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨h₁.trans_le (min_le_left _ _),(le_max_left _ _).trans_lt h₄⟩,
      ⟨h₁.trans_le (min_le_right _ _),(le_max_right _ _).trans_lt h₄⟩⟩
  · rintro ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩
    exact ⟨lt_min h₁ h₃,(min_le_left _ _).trans_lt h₂,
      h₁.trans_le (le_max_left _ _),max_lt h₂ h₄⟩

lemma pair_interior_mass (μ : E → ℝ) (x : E → ℝ) (l r : ℝ) :
    (∑ e, ∑ e', μ e*μ e'*
      (if l < min (x e) (x e') ∧ min (x e) (x e') < r ∧
          l < max (x e) (x e') ∧ max (x e) (x e') < r then 1 else 0)) =
      (interiorMass μ x l r)^2 := by
  classical
  rw [pow_two,interiorMass,sum_mul_sum]
  apply sum_congr rfl; intro e _
  apply sum_congr rfl; intro e' _
  simp only [sorted_interior]
  by_cases h₁ : l < x e ∧ x e < r <;>
    by_cases h₂ : l < x e' ∧ x e' < r <;> simp [h₁,h₂]

end
end PlanarUnitDistances.BudgetIntervals

namespace PlanarUnitDistances.PlaceScore
open MeasureTheory Set Real BudgetIntervals StrictCross
open scoped Classical
noncomputable section

lemma coefficient_bounds (ρ : ℝ) : 0 ≤ coefficient ρ ∧ coefficient ρ ≤ 2 := by
  unfold coefficient
  split_ifs <;> norm_num
lemma reward_bounds (ε p ρ : ℝ) (one : Bool) : 0≤reward ε p ρ one ∧ reward ε p ρ one ≤ 2 := by
  unfold reward
  split_ifs <;> try norm_num
  exact coefficient_bounds ρ
lemma reward_true_zero {ε p ρ : ℝ} (hε : ε<1/2) (hp : 1-ε<p) : reward ε p ρ true=0 := by
  have hc : ¬common ε p := fun h => not_lt_of_ge h.2 hp
  have hn : ¬p<ε := by linarith
  simp [reward,hc,hn]
lemma reward_false_zero {ε p ρ : ℝ} (hε : ε<1/2) (hp : p<ε) : reward ε p ρ false=0 := by
  have hc : ¬common ε p := fun h => not_lt_of_ge h.1 hp
  have hn : ¬1-ε<p := by linarith
  simp [reward,hc,hn]

lemma ind_nonneg (A : Set ℝ) (s : ℝ) : 0 ≤ ind A s := by
  unfold ind Set.indicator; split_ifs <;> norm_num
lemma ind_Icc_integrable (a b : ℝ) : Integrable (ind (Icc a b)) := by
  exact (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc a b)).integrable_indicator measurableSet_Icc
lemma ind_Icc_integral (a b : ℝ) : ∫s,ind (Icc a b) s = max 0 (b-a) := by
  change (∫s,(Icc a b).indicator (fun _ => (1:ℝ)) s)=_
  rw [integral_indicator_const (1:ℝ) measurableSet_Icc]
  simp only [smul_eq_mul,mul_one,Real.volume_real_Icc,max_comm]
lemma ind_inter_integrable (a b l r : ℝ) : Integrable (ind (Icc a b ∩ Icc l r)) := by
  rw [Icc_inter_Icc]
  exact ind_Icc_integrable _ _
lemma ind_inter_integral (a b l r : ℝ) :
    ∫s,ind (Icc a b ∩ Icc l r) s=overlap a b l r := by
  rw [Icc_inter_Icc,ind_Icc_integral]
  rfl

lemma low_cap {ε b b' T : ℝ} {g ρ : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (h : g b<ε) (s : ℝ) :
    cap ε g ρ b b' T s ≤ 2*ind (Icc (b-T) b) s := by
  have h₁ : reward ε (g s) (ρ s) true*ind (Icc (b-T) b ∩ Iio b) s ≤
      2*ind (Icc (b-T) b) s := by
    unfold ind Set.indicator
    split_ifs with hi hi'
    · simpa using (reward_bounds ε (g s) (ρ s) true).2
    · exact False.elim (hi' hi.1)
    · norm_num
    · norm_num
  have h₂ : reward ε (g s) (ρ s) false*ind (Icc b' (b'+T)) s=0 := by
    by_cases hs : s∈Icc b' (b'+T)
    · rw [reward_false_zero hε ((hg (hbb.trans hs.1)).trans_lt h),zero_mul]
    · simp [ind,hs]
  unfold cap
  rw [h₂,add_zero]
  exact h₁

lemma high_cap {ε b b' T : ℝ} {g ρ : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (h : 1-ε<g b') (s : ℝ) :
    cap ε g ρ b b' T s ≤ 2*ind (Icc b' (b'+T)) s := by
  have h₁ : reward ε (g s) (ρ s) true*ind (Icc (b-T) b ∩ Iio b) s=0 := by
    by_cases hs : s∈Icc (b-T) b ∩ Iio b
    · rw [reward_true_zero hε (h.trans_le (hg (hs.1.2.trans hbb))),zero_mul]
    · simp [ind,hs]
  have h₂ := mul_le_mul_of_nonneg_right (reward_bounds ε (g s) (ρ s) false).2
    (ind_nonneg (Icc b' (b'+T)) s)
  unfold cap
  rw [h₁,zero_add]
  exact h₂

lemma middle_reward {ε p ρ : ℝ} (one : Bool)
    (hn : ¬(if one then p<ε else 1-ε<p)) :
    reward ε p ρ one ≤ 1-1/20000+2*(1/20000:ℝ)*(if common ε p ∧ |ρ-1/2| ≤ 1/100 then 1 else 0) := by
  by_cases hc : common ε p <;> by_cases hz : |ρ-1/2| ≤ (1/100:ℝ) <;>
    simp only [reward,coefficient,hc,hz,hn,and_self,ite_true,ite_false,and_true] <;> norm_num

lemma middle_cap {ε b b' T l r : ℝ} {g ρ : ℝ → ℝ}
    (hg : Antitone g) (hlow : ε ≤ g b) (hhigh : g b' ≤ 1-ε)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ 1/100 ↔ s∈Ico l r) (s : ℝ) :
    cap ε g ρ b b' T s ≤
      (1-1/20000:ℝ)*(ind (Icc (b-T) b) s+ind (Icc b' (b'+T)) s)+
      2*(1/20000:ℝ)*(ind (Icc (b-T) b ∩ Icc l r) s+ind (Icc b' (b'+T) ∩ Icc l r) s) := by
  have hlo : reward ε (g s) (ρ s) true*ind (Icc (b-T) b ∩ Iio b) s ≤
      (1-1/20000:ℝ)*ind (Icc (b-T) b) s+2*(1/20000:ℝ)*ind (Icc (b-T) b ∩ Icc l r) s := by
    by_cases hs : s∈Icc (b-T) b ∩ Iio b
    · have hn : ¬g s<ε := not_lt.mpr (hlow.trans (hg hs.1.2))
      have hr := middle_reward true (by simpa using hn : ¬(if true then g s<ε else 1-ε<g s)) (ρ:=ρ s)
      have hI : (if common ε (g s) ∧ |ρ s-1/2| ≤ 1/100 then (1:ℝ) else 0) ≤ ind (Icc l r) s := by
        split_ifs with hc
        · have hjs : s∈Icc l r := ⟨((hJ s).mp hc).1,((hJ s).mp hc).2.le⟩
          simp [ind,hjs]
        · exact ind_nonneg _ _
      simp only [ind,Set.indicator_of_mem hs,Set.indicator_of_mem hs.1,mul_one]
      have he : (Icc (b-T) b ∩ Icc l r).indicator (fun _ => (1:ℝ)) s=ind (Icc l r) s := by
        simp [ind,Set.indicator,hs.1]
      rw [he]
      linarith
    · have hn : ind (Icc (b-T) b ∩ Iio b) s=0 := by simp [ind,hs]
      rw [hn,mul_zero]
      exact add_nonneg (mul_nonneg (by norm_num) (ind_nonneg _ _)) (mul_nonneg (by norm_num) (ind_nonneg _ _))
  have hhi : reward ε (g s) (ρ s) false*ind (Icc b' (b'+T)) s ≤
      (1-1/20000:ℝ)*ind (Icc b' (b'+T)) s+2*(1/20000:ℝ)*ind (Icc b' (b'+T) ∩ Icc l r) s := by
    by_cases hs : s∈Icc b' (b'+T)
    · have hn : ¬1-ε<g s := not_lt.mpr ((hg hs.1).trans hhigh)
      have hr := middle_reward false (by simpa using hn : ¬(if false then g s<ε else 1-ε<g s)) (ρ:=ρ s)
      have hI : (if common ε (g s) ∧ |ρ s-1/2| ≤ 1/100 then (1:ℝ) else 0) ≤ ind (Icc l r) s := by
        split_ifs with hc
        · have hjs : s∈Icc l r := ⟨((hJ s).mp hc).1,((hJ s).mp hc).2.le⟩
          simp [ind,hjs]
        · exact ind_nonneg _ _
      simp only [ind,Set.indicator_of_mem hs,mul_one]
      have he : (Icc b' (b'+T) ∩ Icc l r).indicator (fun _ => (1:ℝ)) s=ind (Icc l r) s := by
        simp [ind,Set.indicator,hs]
      rw [he]
      linarith
    · have hn : ind (Icc b' (b'+T)) s=0 := by simp [ind,hs]
      rw [hn,mul_zero,mul_zero,zero_add]
      exact mul_nonneg (by norm_num) (ind_nonneg _ _)
  unfold cap
  linarith

theorem positive_budget {ε b b' T l r : ℝ} {g ρ f : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (hT : 0 ≤ T)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ 1/100 ↔ s∈Ico l r)
    (hf : Integrable f) (hcap : ∀s,f s ≤ cap ε g ρ b b' T s) :
    (∫s,f s) ≤ 2*T+(1/20000:ℝ)*max 0 (r-l)*
      (if l<b ∧ b<r ∧ l<b' ∧ b'<r then 1 else 0) := by
  have hex : 0 ≤ (1/20000:ℝ)*max 0 (r-l)*(if l<b ∧ b<r ∧ l<b' ∧ b'<r then 1 else 0) := by
    split_ifs <;> positivity
  by_cases hlo : g b<ε
  · have hi := integral_mono hf ((ind_Icc_integrable (b-T) b).const_mul 2)
      (fun s => (hcap s).trans (low_cap hε hg hbb hlo s))
    rw [integral_const_mul,ind_Icc_integral] at hi
    have he : max 0 (b-(b-T))=T := by rw [show b-(b-T)=T by ring,max_eq_right hT]
    rw [he] at hi
    linarith
  by_cases hhi : 1-ε<g b'
  · have hi := integral_mono hf ((ind_Icc_integrable b' (b'+T)).const_mul 2)
      (fun s => (hcap s).trans (high_cap hε hg hbb hhi s))
    rw [integral_const_mul,ind_Icc_integral] at hi
    have he : max 0 (b'+T-b')=T := by rw [show b'+T-b'=T by ring,max_eq_right hT]
    rw [he] at hi
    linarith
  have h₁ := ((ind_Icc_integrable (b-T) b).add (ind_Icc_integrable b' (b'+T))).const_mul (1-1/20000:ℝ)
  have h₂ := ((ind_inter_integrable (b-T) b l r).add (ind_inter_integrable b' (b'+T) l r)).const_mul (2*(1/20000:ℝ))
  change Integrable (fun s => (1-1/20000:ℝ)*(ind (Icc (b-T) b) s+ind (Icc b' (b'+T)) s)) at h₁
  change Integrable (fun s => 2*(1/20000:ℝ)*(ind (Icc (b-T) b ∩ Icc l r) s+ind (Icc b' (b'+T) ∩ Icc l r) s)) at h₂
  have hi := integral_mono hf (h₁.add h₂)
    (fun s => (hcap s).trans (middle_cap hg (le_of_not_gt hlo) (le_of_not_gt hhi) hJ s))
  change (∫s,f s) ≤ ∫s,((1-1/20000:ℝ)*(ind (Icc (b-T) b) s+ind (Icc b' (b'+T)) s)+
      2*(1/20000:ℝ)*(ind (Icc (b-T) b ∩ Icc l r) s+ind (Icc b' (b'+T) ∩ Icc l r) s)) at hi
  rw [integral_add h₁ h₂,integral_const_mul,integral_const_mul,
    integral_add (ind_Icc_integrable (b-T) b) (ind_Icc_integrable b' (b'+T)),
    integral_add (ind_inter_integrable (b-T) b l r) (ind_inter_integrable b' (b'+T) l r),
    ind_Icc_integral,ind_Icc_integral,ind_inter_integral,ind_inter_integral] at hi
  have he : max 0 (b-(b-T))=T := by rw [show b-(b-T)=T by ring,max_eq_right hT]
  have he' : max 0 (b'+T-b')=T := by rw [show b'+T-b'=T by ring,max_eq_right hT]
  rw [he,he'] at hi
  have hc := central_envelope (l:=l) (r:=r) (lam:=(1/20000:ℝ)) hbb hT (by norm_num) (by norm_num)
  have hm := le_max_right 0 ((1-(1/20000:ℝ))*2*T+2*(1/20000:ℝ)*
    (overlap (b-T) b l r+overlap b' (b'+T) l r)-2*T)
  linarith
end
end PlanarUnitDistances.PlaceScore

namespace PlanarUnitDistances.LevelScores
open FiniteLaw StrictCross CrossStructure RareScore PlaceScore
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma positive_bounds (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) :
    0 ≤ positive ε p ρ good l base y z b c ∧ positive ε p ρ good l base y z b c ≤ 2 := by
  unfold positive
  split_ifs
  · exact ⟨mul_nonneg (coefficient_bounds ρ).1 (RareScore.ind_nonneg _),
      (mul_le_mul_of_nonneg_left (RareScore.ind_le_one _) (coefficient_bounds ρ).1).trans
        (by simpa using (coefficient_bounds ρ).2)⟩
  · constructor
    · exact mul_nonneg (by norm_num) (RareScore.ind_nonneg _)
    · nlinarith [RareScore.ind_le_one (exceptional (minority p) l base ∧
        b=minority p ∧ c=minority p ∧ nonshared (minority p) y z)]
  · norm_num
lemma score_bounds (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) :
    -1 ≤ score ε p ρ good l base y z b c ∧ score ε p ρ good l base y z b c ≤ 2 := by
  have h := positive_bounds ε p ρ good l base y z b c
  have hn := RareScore.ind_nonneg (b≠c)
  have hm := RareScore.ind_le_one (b≠c)
  unfold score
  constructor <;> linarith

lemma minority_reward {ε p ρ : ℝ} (hε : ε<1/2) (h : ¬common ε p) :
    reward ε p ρ (minority p)=2 := by
  unfold reward
  rw [ite_eq_right h]
  unfold minority
  by_cases hp : p<1/2
  · have hl : p<ε := by unfold common at h; push Not at h; by_contra! hh; have := h hh; linarith
    rw [show decide (p<1/2)=true from decide_eq_true hp]
    simp [hl]
  · have hr : 1-ε<p := by unfold common at h; push Not at h; apply h; linarith
    rw [show decide (p<1/2)=false from decide_eq_false hp]
    simp [hr]

lemma positive_le_rewards {ε p ρ : ℝ} (hε : ε<1/2) (good : Prop)
    (l base y z : A×B) (b c : Bool) :
    positive ε p ρ good l base y z b c ≤
      reward ε p ρ true*RareScore.ind (b=true ∧ c=true ∧ nonshared true y z)+
      reward ε p ρ false*RareScore.ind (b=false ∧ c=false ∧ nonshared false y z) := by
  have hn₀ := (reward_bounds ε p ρ false).1
  have hn₁ := (reward_bounds ε p ρ true).1
  by_cases hc : common ε p
  · unfold positive reward
    rw [ite_eq_left hc,ite_eq_left hc,ite_eq_left hc]
    cases b <;> cases c <;> simp only [RareScore.ind,nonshared,Bool.false_eq_true,
      Bool.true_eq_false,↓reduceIte,true_and,false_and,and_false]
    all_goals try split_ifs
    all_goals nlinarith [(coefficient_bounds ρ).1]
  · have hm := minority_reward (ρ:=ρ) hε hc
    unfold positive
    rw [ite_eq_right hc]
    by_cases hg : good
    · rw [ite_eq_left hg]
      unfold RareScore.ind
      by_cases hp : exceptional (minority p) l base ∧
          b=minority p ∧ c=minority p ∧ nonshared (minority p) y z
      · rw [ite_eq_left hp]
        obtain ⟨_,hb,hc',hns⟩ := hp
        rw [hb,hc']
        cases hr : minority p
        · rw [hr] at hm hns
          simp [hm,hns]
        · rw [hr] at hm hns
          simp [hm,hns]
      · rw [ite_eq_right hp]
        split_ifs <;> nlinarith
    · rw [ite_eq_right hg]
      exact add_nonneg (mul_nonneg hn₁ (RareScore.ind_nonneg _))
        (mul_nonneg hn₀ (RareScore.ind_nonneg _))

end
end PlanarUnitDistances.LevelScores

namespace PlanarUnitDistances.LevelSlotGeometry
open MeasureTheory Set Real FiniteStates PlaceLevels LevelStates LevelGeometry BudgetPlaces LevelScores
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [NumberField K]

theorem positive_le_cap (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s ε : ℝ)
    (g ρ : ℝ → ℝ) (hε : ε<1/2) (good : Prop) (l : (V → Bool)×(V → Bool)) (x y y' : V)
    (hu : (z x-z y)*(w x-w y)=1) (hu' : (z x-z y')*(w x-w y')=1)
    (hyy : z y≠z y') :
    positive ε (g s) (ρ s) good l (state S z w u (v,s) x)
      (state S z w u (v,s) y) (state S z w u (v,s) y')
      (decide (s<threshold (av K v) (z x-z y))) (decide (s<threshold (av K v) (z x-z y'))) ≤
    PlaceScore.cap ε g ρ
      (min (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')))
      (max (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')))
      (alpha (av K v) (z x-z y) (z x-z y')+allowance v) s := by
  have hp := positive_le_rewards hε good l (state S z w u (v,s) x)
    (state S z w u (v,s) y) (state S z w u (v,s) y')
    (decide (s<threshold (av K v) (z x-z y))) (decide (s<threshold (av K v) (z x-z y')))
    (p:=g s) (ρ:=ρ s)
  have hf := positive_flanks S z w u v s x y y' hu hu' hyy
  dsimp only at hf
  refine hp.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ (PlaceScore.reward_bounds ε (g s) (ρ s) true).1)
    (mul_le_mul_of_nonneg_left ?_ (PlaceScore.reward_bounds ε (g s) (ρ s) false).1))
  · unfold RareScore.ind
    split_ifs with h
    · have he₁ : s<threshold (av K v) (z x-z y) := of_decide_eq_true h.1
      have he₂ : s<threshold (av K v) (z x-z y') := of_decide_eq_true h.2.1
      have hi := hf.1 ⟨he₁,he₂,h.2.2⟩
      have hi' := lt_min he₁ he₂
      change 1 ≤ PlaceScore.ind _ s
      rw [PlaceScore.ind,Set.indicator_of_mem (show s∈Icc _ _ ∩ Iio _ from ⟨hi,hi'⟩)]
    · exact PlaceScore.ind_nonneg _ _
  · unfold RareScore.ind
    split_ifs with h
    · have he₁ : threshold (av K v) (z x-z y) ≤ s := le_of_not_gt (of_decide_eq_false h.1)
      have he₂ : threshold (av K v) (z x-z y') ≤ s := le_of_not_gt (of_decide_eq_false h.2.1)
      have hi := hf.2 ⟨he₁,he₂,h.2.2⟩
      simp only [PlaceScore.ind,Set.indicator_of_mem hi,le_refl]
    · exact PlaceScore.ind_nonneg _ _
end
end PlanarUnitDistances.LevelSlotGeometry

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_RareEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LevelBookkeeping
open Finset FiniteLaw FiniteStarCoupling RareLabels RareMoments RareScore
open scoped Classical
noncomputable section
variable {D P Q A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype A]

omit [Fintype D] [Fintype A] in
lemma minority_nonneg (π : Law (P×Q)) (b : P → Q → Bool) : 0 ≤ minorityMass π b :=
  le_min (event_nonneg _ _) (sub_nonneg.mpr (event_le_one _ _))
end
end PlanarUnitDistances.LevelBookkeeping

namespace PlanarUnitDistances.FiniteLaw
open scoped Classical
noncomputable section
variable {D : Type*} [Fintype D]
lemma cut_nonneg (σ : Law D) (c : D → Prop) (f : D → ℝ) (hf : ∀s,0 ≤ f s) : 0 ≤ cut σ c f :=
  avg_nonneg σ (fun s => by split_ifs <;> first | exact hf s | exact le_rfl)
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ScoreBook
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows RareMoments GlobalScores
open scoped Classical
noncomputable section

namespace Book
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype I]

omit [Fintype A] [Fintype H] [Fintype I] in
lemma nonneg (B : Book D P Q H A) : 0 ≤ B.S ∧ 0 ≤ B.M ∧ 0 ≤ B.HP ∧ 0 ≤ B.HQ ∧
    0 ≤ B.CP ∧ 0 ≤ B.CQ ∧ 0 ≤ B.J ∧ 0 ≤ B.WC ∧ 0 ≤ B.WB := by
  refine ⟨avg_nonneg _ (fun _ => LevelBookkeeping.minority_nonneg _ _),avg_nonneg _ (fun _ => event_nonneg _ _),
    cut_nonneg _ _ _ (fun _ => event_nonneg _ _),cut_nonneg _ _ _ (fun _ => event_nonneg _ _),
    cut_nonneg _ _ _ (fun _ => avg_nonneg _ (fun _ => StarScore.variation_nonneg _ _)),
    cut_nonneg _ _ _ (fun _ => avg_nonneg _ (fun _ => StarScore.variation_nonneg _ _)),
    cut_nonneg _ _ _ (fun _ => event_nonneg _ _),event_nonneg _ _,event_nonneg _ _⟩
end Book
end
end PlanarUnitDistances.ScoreBook

namespace PlanarUnitDistances.LevelSnapshot
open MeasureTheory Set Finset FiniteLaw LevelStates PlaceLevels
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

lemma measurable_value {Y : Type*} [MeasurableSpace Y] (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → Y) :
    Measurable (fun a => F (snapshot S z w src tgt u a)) :=
  (measurable_of_finite F).comp (measurable_snapshot S z w src tgt u)

lemma integrable_value (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → ℝ)
    {ν : Measure (Place K S×ℝ)} [IsFiniteMeasure ν] :
    Integrable (fun a => F (snapshot S z w src tgt u a)) ν := by
  apply Integrable.mono' (integrable_const (∑d : Data V E, |F d|))
    (measurable_value S z w src tgt u F).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using
      (single_le_sum (s:=univ) (fun d _ => abs_nonneg (F d)) (mem_univ (snapshot S z w src tgt u a)))

lemma integrable_piece (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → ℝ)
    (v : Place K S) (l r : ℝ) : IntegrableOn (fun s => F (snapshot S z w src tgt u (v,s))) (Icc l r) := by
  apply Integrable.mono' (integrable_const (∑d : Data V E, |F d|))
    ((measurable_value S z w src tgt u F).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using
      (single_le_sum (s:=univ) (fun d _ => abs_nonneg (F d)) (mem_univ (snapshot S z w src tgt u (v,s))))

end
end PlanarUnitDistances.LevelSnapshot

namespace PlanarUnitDistances.ActualSlots
open MeasureTheory Set Finset FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot LevelScores RareScore
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E] [Fintype F]

omit [Fintype V] in
lemma positive_le_active (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (a : Data V E) :
    positive ε μ ν edge y x good label e f a ≤ 2*active ε μ good label x a := by
  by_cases hc : PlaceScore.common ε (frequency μ a)
  · have h := (LevelScores.positive_bounds ε (frequency μ a)
      (event ν (fun j => a.1 (edge j)=true)) (good a) (label a) (a.2 x)
      (a.2 (y e)) (a.2 (y f)) (a.1 (edge e)) (a.1 (edge f))).2
    simpa [positive,active,rareException,hc,ind] using h
  · unfold positive LevelScores.positive active rareException
    rw [ite_eq_right hc]
    by_cases hg : good a
    · rw [ite_eq_left hg]
      by_cases he : exceptional (minority (frequency μ a)) (label a) (a.2 x)
      · simp only [hc,hg,he,true_and,not_false_eq_true,ind,↓reduceIte]
        split_ifs <;> norm_num
      · simp [ind,hc,hg,he]
    · simp [hc,hg,ind]

omit [Fintype V] in
lemma diagonal (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e : F) (a : Data V E) :
    score ε μ ν edge y x good label e e a=positive ε μ ν edge y x good label e e a := by
  simp [score,ind]

lemma measurable_score (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool)) (e f : F) :
    Measurable (fun a => score ε μ ν edge y x good label e f (snapshot S z w src tgt u a)) :=
  measurable_value S z w src tgt u _

lemma score_integrable (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool)) (e f : F) :
    Integrable (fun a => score ε μ ν edge y x good label e f (snapshot S z w src tgt u a))
      (LevelScale.measure S) := integrable_value S z w src tgt u _

lemma negative_integral {l r b c : ℝ} (hlb : l ≤ b) (hbr : b ≤ r) (hlc : l ≤ c) (hcr : c ≤ r) :
    (∫s in Icc l r, ind (decide (s<b)≠decide (s<c)))=|b-c| := by
  have he (s : ℝ) : ind (decide (s<b)≠decide (s<c))=|ThresholdProfiles.bit b s-ThresholdProfiles.bit c s| := by
    by_cases hb : s<b <;> by_cases hc : s<c <;> simp [ind,ThresholdProfiles.bit,hb,hc]
  simp_rw [he]
  exact ThresholdProfiles.bit_sub_integral hlb hbr hlc hcr

lemma integrated_diagonal (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool)) (e : F) :
    (∫a,score ε μ ν edge y x good label e e (snapshot S z w src tgt u a) ∂LevelScale.measure S) ≤
      2*(∫a,active ε μ good label x (snapshot S z w src tgt u a) ∂LevelScale.measure S) := by
  rw [←integral_const_mul]
  apply integral_mono (score_integrable S z w src tgt u ε μ ν edge y x good label e e)
    ((integrable_value S z w src tgt u (active ε μ good label x)).const_mul 2)
  intro a
  dsimp only
  rw [diagonal]
  exact positive_le_active ε μ ν edge y x good label e e _
end
end PlanarUnitDistances.ActualSlots

namespace PlanarUnitDistances.GlobalPairBudget
open MeasureTheory Set Finset Real PlaceLevels BudgetPlaces LevelGeometry PlaceScore
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

lemma total_allowance (S : Finset K) :
    (∑v : Place K S,2*allowance v)/(Module.finrank ℚ K:ℝ)=2*log 2 := by
  rw [Fintype.sum_sum_type]
  simp only [allowance,mul_zero,sum_const_zero,add_zero]
  exact arch_allowance K

lemma thickness_nonneg {S : Finset K} (v : Place K S) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') :
    0 ≤ alpha (av K v) d d'+allowance v := by
  cases v with
  | inl σ => exact alpha_add_log_two_nonneg _ hd hd' hdd
  | inr v =>
    simpa only [av,allowance,add_zero] using alpha_nonneg_nonarch
      (WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2)
      (WeightedAbsoluteValues.finiteEntry_nonarch K v.val.1 v.val.2) hd hd' hdd

lemma cancellation [IsGalois ℚ K] {S : Finset K} {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') (hmem : differenceProduct d d'∈S) :
    (∑v : Place K S,(2*(alpha (av K v) d d'+allowance v)-
      |threshold (av K v) d-threshold (av K v) d'|))/(Module.finrank ℚ K:ℝ)=2*log 2 := by
  have he (v : Place K S) :
      2*(alpha (av K v) d d'+allowance v)-|threshold (av K v) d-threshold (av K v) d'| =
      -log (av K v (differenceProduct d d'))+2*allowance v := by
    rw [place_identity _ hd hd' hdd,max_sub_min_eq_abs,abs_sub_comm (threshold (av K v) d')]
    ring
  simp_rw [he]
  rw [sum_add_distrib,sum_neg_distrib,add_div,neg_div,
    sum_log_product_formula K hmem (differenceProduct_ne_zero hdd),neg_zero,zero_add]
  exact total_allowance S

theorem weighted_pair [IsGalois ℚ K] (S : Finset K) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') (hmem : differenceProduct d d'∈S)
    {ε : ℝ} (hε : ε<1/2) (g ρ f : Place K S → ℝ → ℝ) (l r : Place K S → ℝ)
    (hg : ∀v,Antitone (g v))
    (hJ : ∀v s,common ε (g v s) ∧ |ρ v s-1/2| ≤ 1/100 ↔ s∈Ico (l v) (r v))
    (hf : ∀v,Integrable (f v))
    (hcap : ∀v s,f v s ≤ cap ε (g v) (ρ v)
      (min (threshold (av K v) d) (threshold (av K v) d'))
      (max (threshold (av K v) d) (threshold (av K v) d'))
      (alpha (av K v) d d'+allowance v) s) :
    (∑v : Place K S,((∫s,f v s)-|threshold (av K v) d-threshold (av K v) d'|)) /
      (Module.finrank ℚ K:ℝ) ≤ 2*log 2+
      (∑v : Place K S,(1/20000:ℝ)*max 0 (r v-l v)*
        (if l v < min (threshold (av K v) d) (threshold (av K v) d') ∧
            min (threshold (av K v) d) (threshold (av K v) d')<r v ∧
            l v < max (threshold (av K v) d) (threshold (av K v) d') ∧
            max (threshold (av K v) d) (threshold (av K v) d')<r v then 1 else 0)) /
      (Module.finrank ℚ K:ℝ) := by
  have hb (v : Place K S) := positive_budget hε (hg v) (min_le_max (a:=threshold (av K v) d)
      (b:=threshold (av K v) d')) (thickness_nonneg v hd hd' hdd) (hJ v) (hf v) (hcap v)
  have hs := sum_le_sum (s:=univ) (fun v _ => sub_le_sub_right (hb v)
    |threshold (av K v) d-threshold (av K v) d'|)
  have he (v : Place K S) (e : ℝ) :
      2*(alpha (av K v) d d'+allowance v)+e-|threshold (av K v) d-threshold (av K v) d'| =
      (2*(alpha (av K v) d d'+allowance v)-|threshold (av K v) d-threshold (av K v) d'|)+e := by ring
  simp_rw [he] at hs
  rw [sum_add_distrib] at hs
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Module.finrank ℚ K))
  rw [add_div,cancellation hd hd' hdd hmem] at hh
  exact hh
end
end PlanarUnitDistances.GlobalPairBudget

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Integration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.TailWindows
open Finset Set FiniteLaw
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E]

lemma tail_antitone (μ : Law E) (x : E → ℝ) : Antitone (tail μ x) := by
  intro s t hst
  exact event_mono μ (fun e he => lt_of_le_of_lt hst he)
lemma below_all (μ : Law E) (x : E → ℝ) (s : ℝ) (h : ∀e,s<x e) : tail μ x s=1 := by
  unfold tail event
  simp only [ite_eq_left (h _)]
  exact avg_const μ 1
lemma above_all (μ : Law E) (x : E → ℝ) (s : ℝ) (h : ∀e,x e ≤ s) : tail μ x s=0 := by
  unfold tail event
  simp only [ite_eq_right (not_lt.mpr (h _))]
  exact avg_const μ 0

lemma step (μ : Law E) (x : E → ℝ) (s : ℝ) (hs : tail μ x s<1) :
    ∃e,x e ≤ s ∧ tail μ x (x e)=tail μ x s := by
  let F := univ.filter (fun e => x e ≤ s)
  have hF : F.Nonempty := by
    by_contra h
    have hh : ∀e,s<x e := by
      intro e
      by_contra he
      exact h ⟨e,mem_filter.mpr ⟨mem_univ _,le_of_not_gt he⟩⟩
    linarith [below_all μ x s hh]
  obtain ⟨e,he,hem⟩ := F.exists_max_image x hF
  have hes := (mem_filter.mp he).2
  refine ⟨e,hes,?_⟩
  apply avg_congr
  intro f
  have hh : x e<x f ↔ s<x f := by
    constructor
    · intro h
      by_contra ht
      exact (not_lt_of_ge (hem f (mem_filter.mpr ⟨mem_univ _,le_of_not_gt ht⟩))) h
    · exact fun h => lt_of_le_of_lt hes h
  simp only [hh]

lemma nonempty_type (μ : Law E) : Nonempty E := by
  by_contra h
  have : IsEmpty E := not_nonempty_iff.mp h
  have ht := μ.total
  simp at ht

lemma least_threshold (μ : Law E) (x : E → ℝ) (P : ℝ → Prop)
    (hmono : ∀a b,b ≤ a → P a → P b) (hsmall : ∀a,P a → a<1)
    (hzero : P 0) : ∃l,∀s,P (tail μ x s) ↔ l ≤ s := by
  let F := univ.filter (fun e => P (tail μ x (x e)))
  have hF : F.Nonempty := by
    let _ : Nonempty E := nonempty_type μ
    obtain ⟨e,_,he⟩ := univ.exists_max_image x univ_nonempty
    have hz : tail μ x (x e)=0 := above_all μ x _ (fun f => he f (mem_univ _))
    exact ⟨e,mem_filter.mpr ⟨mem_univ _,by rw [hz]; exact hzero⟩⟩
  obtain ⟨e,he,hem⟩ := F.exists_min_image x hF
  refine ⟨x e,fun s => ⟨?_,?_⟩⟩
  · intro hs
    obtain ⟨f,hf,hv⟩ := step μ x s (hsmall _ hs)
    exact (hem f (mem_filter.mpr ⟨mem_univ _,by rw [hv]; exact hs⟩)).trans hf
  · intro hs
    exact hmono _ _ (tail_antitone μ x hs) (mem_filter.mp he).2

theorem window (μ : Law E) (x : E → ℝ) {L U : ℝ}
    (hL : 0<L) (hLU : L ≤ U) (hU : U<1) :
    ∃l r,l ≤ r ∧ ∀s,(L ≤ tail μ x s ∧ tail μ x s ≤ U) ↔ s∈Set.Ico l r := by
  obtain ⟨l,hl⟩ := least_threshold μ x (fun a => a ≤ U)
    (fun a b hab ha => hab.trans ha) (fun a ha => ha.trans_lt hU) (hL.le.trans hLU)
  obtain ⟨r,hr⟩ := least_threshold μ x (fun a => a<L)
    (fun a b hab ha => hab.trans_lt ha) (fun a ha => (ha.trans_le hLU).trans hU) hL
  have hlr : l ≤ r := (hl r).mp (((hr r).mpr le_rfl).le.trans hLU)
  refine ⟨l,r,hlr,fun s => ?_⟩
  have he : L ≤ tail μ x s ↔ s<r := by
    rw [← not_lt,hr,not_le]
  simp only [he,hl,Set.mem_Ico,and_comm]

end
end PlanarUnitDistances.TailWindows

namespace PlanarUnitDistances.StarWindow
open MeasureTheory Set Real FiniteLaw TailWindows PlaceScore
open scoped Classical
noncomputable section
variable {E F : Type*} [Fintype E] [Fintype F]

lemma common_window (μ : Law E) (x : E → ℝ) {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2) :
    ∃l r,l ≤ r ∧ ∀s,common ε (tail μ x s) ↔ s∈Ico l r :=
  window μ x hε (by linarith) (by linarith)

lemma central_window (μ : Law E) (x : E → ℝ) :
    ∃l r,l ≤ r ∧ ∀s,|tail μ x s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r := by
  obtain ⟨l,r,hlr,h⟩ := window μ x (L:=(1/2-1/100:ℝ)) (U:=(1/2+1/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨l,r,hlr,fun s => ?_⟩
  rw [←h s,abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem exists_joint_window (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2) :
    ∃l r,∀s,common ε (tail μ x s) ∧ |tail ν y s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r := by
  obtain ⟨a,b,_,hg⟩ := common_window μ x hε hε'
  obtain ⟨c,d,_,hr⟩ := central_window ν y
  refine ⟨max a c,min b d,fun s => ?_⟩
  rw [hg,hr]
  simp only [mem_Ico,max_le_iff,lt_min_iff]
  tauto

theorem mean_excess (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε l r : ℝ}
    (hJ : ∀s,common ε (tail μ x s) ∧ |tail ν y s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r) :
    avg (pair ν ν) (fun ef => (1/20000:ℝ)*max 0 (r-l)*
      (if l < min (y ef.1) (y ef.2) ∧ min (y ef.1) (y ef.2)<r ∧
          l < max (y ef.1) (y ef.2) ∧ max (y ef.1) (y ef.2)<r then 1 else 0)) ≤
      4*(1/100:ℝ)^2*(1/20000:ℝ)*max 0 (r-l) := by
  have hc : ∀s∈Ioo l r,|BudgetIntervals.tail ν.val y s-1/2| ≤ (1/100:ℝ) := by
    intro s hs
    exact ((hJ s).mpr ⟨hs.1.le,hs.2⟩).2
  rw [pair_avg]
  unfold avg
  have he := BudgetIntervals.pair_interior_mass ν.val y l r
  have hh : (∑e,ν.val e*∑f,ν.val f*((1/20000:ℝ)*max 0 (r-l)*
      (if l < min (y e) (y f) ∧ min (y e) (y f)<r ∧
          l < max (y e) (y f) ∧ max (y e) (y f)<r then 1 else 0))) =
      ((1/20000:ℝ)*max 0 (r-l))*(BudgetIntervals.interiorMass ν.val y l r)^2 := by
    rw [←he]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    ring
  rw [hh]
  have hm := BudgetIntervals.interior_mass_le ν.nonneg y (by norm_num : (0:ℝ) ≤ 1/100) hc
  have hn := BudgetIntervals.interiorMass_nonneg ν.val ν.nonneg y l r
  have hs : (BudgetIntervals.interiorMass ν.val y l r)^2 ≤ (2*(1/100:ℝ))^2 :=
    (sq_le_sq₀ hn (by norm_num)).mpr hm
  have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1/20000:ℝ)*max 0 (r-l) by positivity)
  nlinarith only [h]
end
end PlanarUnitDistances.StarWindow

namespace PlanarUnitDistances.WindowVariation
open MeasureTheory Set Real FiniteLaw TailWindows PlaceScore StarWindow
open scoped Classical
noncomputable section
variable {E F : Type*} [Fintype E] [Fintype F]

lemma variation_nonneg {ε : ℝ} {g ρ : ℝ → ℝ} (hρ : ∀s,0 ≤ ρ s ∧ ρ s ≤ 1) (s : ℝ) :
    0 ≤ variation ε g ρ s := by
  unfold variation
  split_ifs
  · exact mul_nonneg (mul_nonneg (by norm_num) (hρ s).1) (sub_nonneg.mpr (hρ s).2)
  · exact le_rfl

lemma central_lower {ε l r : ℝ} {g ρ : ℝ → ℝ}
    (hρ : ∀s,0 ≤ ρ s ∧ ρ s ≤ 1)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r) (s : ℝ) :
    (2*((1/4:ℝ)-(1/100:ℝ)^2))*ind (Icc l r) s ≤ variation ε g ρ s ∨ s=r := by
  by_cases he : s=r
  · exact Or.inr he
  left
  by_cases hs : s∈Icc l r
  · have hc := (hJ s).mpr ⟨hs.1,lt_of_le_of_ne hs.2 he⟩
    rw [ind,Set.indicator_of_mem hs,variation,ite_eq_left hc.1,mul_one]
    have hr := abs_le.mp hc.2
    nlinarith [sq_nonneg (ρ s-1/2),mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hr.1)]
  · rw [ind,Set.indicator_of_notMem hs,mul_zero]
    exact variation_nonneg hρ s

lemma window_le_variation {ε l r : ℝ} {g ρ : ℝ → ℝ}
    (hρ : ∀s,0 ≤ ρ s ∧ ρ s ≤ 1)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r)
    (hi : Integrable (variation ε g ρ)) :
    2*((1/4:ℝ)-(1/100:ℝ)^2)*max 0 (r-l) ≤ ∫s,variation ε g ρ s := by
  have hp : ∀ᵐ s : ℝ, (2*((1/4:ℝ)-(1/100:ℝ)^2))*ind (Icc l r) s ≤ variation ε g ρ s := by
    have hne : ∀ᵐ s : ℝ, s≠r := by rw [ae_iff]; simp
    filter_upwards [hne] with s hs
    exact (central_lower hρ hJ s).resolve_right hs
  have h := integral_mono_ae ((ind_Icc_integrable l r).const_mul _) hi hp
  rw [integral_const_mul,ind_Icc_integral] at h
  exact h

lemma excess_le_variation {ε l r : ℝ} {g ρ : ℝ → ℝ}
    (hρ : ∀s,0 ≤ ρ s ∧ ρ s ≤ 1)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ (1/100:ℝ) ↔ s∈Ico l r)
    (hi : Integrable (variation ε g ρ)) :
    4*(1/100:ℝ)^2*(1/20000:ℝ)*max 0 (r-l) ≤
      (1/20000000:ℝ)*(∫s,variation ε g ρ s) := by
  have h := window_le_variation hρ hJ hi
  have hn : 0 ≤ max 0 (r-l) := le_max_left _ _
  nlinarith only [h,hn]
end
end PlanarUnitDistances.WindowVariation

namespace PlanarUnitDistances.FiniteLawIntegral
open MeasureTheory Finset FiniteLaw
open scoped Classical
noncomputable section
variable {X Ω : Type*} [Fintype X] [MeasurableSpace Ω]

lemma integral_avg (μ : Law X) {ν : Measure Ω} (f : X → Ω → ℝ)
    (hf : ∀x,Integrable (f x) ν) :
    (∫a,avg μ (fun x => f x a) ∂ν)=avg μ (fun x => ∫a,f x a ∂ν) := by
  unfold avg
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul _)]
  simp only [integral_const_mul]

lemma avg_sum {I : Type*} [Fintype I] (μ : Law X) (f : I → X → ℝ) :
    avg μ (fun x => ∑i,f i x)=∑i,avg μ (f i) := by
  simp only [avg,Finset.mul_sum]
  exact Finset.sum_comm

lemma avg_div (μ : Law X) (f : X → ℝ) (c : ℝ) :
    avg μ (fun x => f x/c)=avg μ f/c := by
  simp only [avg,mul_div_assoc,Finset.sum_div]

lemma avg_mono_support (μ : Law X) {f g : X → ℝ}
    (h : ∀x,0<μ.val x → f x ≤ g x) : avg μ f ≤ avg μ g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : μ.val x=0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x (lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx))) (μ.nonneg x)

lemma avg_indicator_mul (μ : Law X) (P : X → Prop) (c : ℝ) :
    avg μ (fun x => if P x then c else 0)=c*event μ P := by
  unfold event
  rw [←avg_smul]
  apply avg_congr
  intro x
  split_ifs <;> ring
end
end PlanarUnitDistances.FiniteLawIntegral

namespace PlanarUnitDistances.ExpectedBudget
open MeasureTheory Set Finset Real FiniteLaw FiniteLawIntegral PlaceLevels BudgetPlaces
  LevelGeometry GlobalPairBudget PlaceScore TailWindows StarWindow WindowVariation
open scoped Classical
noncomputable section
variable {K E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype E] [Fintype F]

omit [IsGalois ℚ K] [Fintype F] in
lemma excess_nonneg (S : Finset K) (d : F → K) (l r : Place K S → ℝ) (v : Place K S) (a : F×F) :
    0 ≤ excess S d l r v a := by unfold excess; split_ifs <;> positivity

theorem star_upper (μ : Law E) (ν : Law F) (S : Finset K) (d : F → K)
    (c : Place K S → E → ℝ) (hd : ∀e,0<ν.val e → d e≠0)
    (hinj : ∀e f,0<ν.val e → 0<ν.val f → e≠f → d e≠d f)
    (hmem : ∀e f,0<ν.val e → 0<ν.val f → e≠f → differenceProduct (d e) (d f)∈S)
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (f : F → F → Place K S → ℝ → ℝ)
    (hf : ∀e e' v,Integrable (f e e' v))
    (hcap : ∀e e',0<ν.val e → 0<ν.val e' → e≠e' → ∀v s,f e e' v s ≤ PlaceScore.cap ε (tail μ (c v))
      (tail ν (fun e => threshold (av K v) (d e)))
      (min (threshold (av K v) (d e)) (threshold (av K v) (d e')))
      (max (threshold (av K v) (d e)) (threshold (av K v) (d e')))
      (alpha (av K v) (d e) (d e')+allowance v) s)
    (hv : ∀v,Integrable (variation ε (tail μ (c v)) (tail ν (fun e => threshold (av K v) (d e)))))
    {W : ℝ} (hdiag : ∀e,pairScore S d f (e,e) ≤ W) :
    avg (pair ν ν) (pairScore S d f) ≤ 2*log 2+
      (1/20000000:ℝ)*((∑v : Place K S,∫s,variation ε (tail μ (c v))
        (tail ν (fun e => threshold (av K v) (d e))) s)/(Module.finrank ℚ K:ℝ))+
      W*event (pair ν ν) (fun ef => ef.1=ef.2) := by
  choose l r hJ using fun v : Place K S => exists_joint_window μ ν (c v)
    (fun e => threshold (av K v) (d e)) hε hε'
  let ex (a : F×F) : ℝ := (∑v : Place K S,excess S d l r v a)/(Module.finrank ℚ K:ℝ)
  have hex (a : F×F) : 0 ≤ ex a := div_nonneg (sum_nonneg (fun v _ => excess_nonneg S d l r v a))
    (Nat.cast_nonneg _)
  have hc (a : F×F) (hpos : 0<(pair ν ν).val a) : pairScore S d f a ≤ 2*log 2+ex a+(if a.1=a.2 then W else 0) := by
    have hpa : 0<ν.val a.1 := (mul_pos_iff.mp hpos).elim And.left (fun h => False.elim (not_lt.mpr (ν.nonneg a.1) h.1))
    have hpb : 0<ν.val a.2 := (mul_pos_iff.mp hpos).elim And.right (fun h => False.elim (not_lt.mpr (ν.nonneg a.2) h.2))
    by_cases ha : a.1=a.2
    · rw [ite_eq_left ha]
      have hh : pairScore S d f a ≤ W := by
        rcases a with ⟨a,b⟩
        change a=b at ha
        subst b
        exact hdiag a
      have hl : 0 ≤ log (2:ℝ) := Real.log_nonneg (by norm_num)
      linarith [hex a]
    · rw [ite_eq_right ha,add_zero]
      exact weighted_pair S (hd a.1 hpa) (hd a.2 hpb) (hinj _ _ hpa hpb ha) (hmem _ _ hpa hpb ha) hε'
        (fun v => tail μ (c v)) (fun v => tail ν (fun e => threshold (av K v) (d e)))
        (f a.1 a.2) l r (fun v => tail_antitone μ (c v)) hJ (hf _ _) (hcap _ _ hpa hpb ha)
  have hmean := avg_mono_support (pair ν ν) hc
  rw [avg_add,avg_add,avg_const,avg_indicator_mul] at hmean
  have hm (v : Place K S) : avg (pair ν ν) (excess S d l r v) ≤
      (1/20000000:ℝ)*(∫s,variation ε (tail μ (c v))
        (tail ν (fun e => threshold (av K v) (d e))) s) := by
    refine (mean_excess μ ν (c v) (fun e => threshold (av K v) (d e)) (hJ v)).trans ?_
    apply excess_le_variation _ (hJ v) (hv v)
    intro s
    exact ⟨event_nonneg _ _,event_le_one _ _⟩
  have hexmean : avg (pair ν ν) ex ≤
      (1/20000000:ℝ)*((∑v : Place K S,∫s,variation ε (tail μ (c v))
        (tail ν (fun e => threshold (av K v) (d e))) s)/(Module.finrank ℚ K:ℝ)) := by
    dsimp only [ex]
    rw [avg_div,FiniteLawIntegral.avg_sum]
    have hh := div_le_div_of_nonneg_right (sum_le_sum (s:=univ) (fun v _ => hm v))
      (Nat.cast_nonneg (Module.finrank ℚ K))
    simpa only [←Finset.mul_sum,mul_div_assoc] using hh
  linarith
end
end PlanarUnitDistances.ExpectedBudget

namespace PlanarUnitDistances.SlotIntegration
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E] [Fintype F]

lemma positive_integrable (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (v : Place K S) : Integrable (truncatedPositive S z w src tgt u ε μ ν edge y x good label e f v) := by
  exact (integrable_piece S z w src tgt u (positive ε μ ν edge y x good label e f) v _ _).integrable_indicator measurableSet_Icc

lemma piece_score (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (hm : ∀j,z (src (edge j))-z (tgt (edge j))∈S) (e f : F) (v : Place K S) :
    (∫s in Icc (-radius K S v) (radius K S v),
      score ε μ ν edge y x good label e f (snapshot S z w src tgt u (v,s)))=
    (∫s,truncatedPositive S z w src tgt u ε μ ν edge y x good label e f v s)-
      |threshold (av K v) (z (src (edge e))-z (tgt (edge e)))-
       threshold (av K v) (z (src (edge f))-z (tgt (edge f)))| := by
  have hp := integrable_piece S z w src tgt u (positive ε μ ν edge y x good label e f) v (-radius K S v) (radius K S v)
  have hn := integrable_piece S z w src tgt u
    (fun a : Data V E => RareScore.ind (a.1 (edge e)≠a.1 (edge f))) v (-radius K S v) (radius K S v)
  unfold score truncatedPositive
  rw [integral_sub hp hn,integral_indicator measurableSet_Icc]
  congr 1
  exact negative_integral (threshold_in_range K (hm e) v).1 (threshold_in_range K (hm e) v).2
    (threshold_in_range K (hm f) v).1 (threshold_in_range K (hm f) v).2

lemma score_eq_pairScore (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (hm : ∀j,z (src (edge j))-z (tgt (edge j))∈S) (e f : F) :
    (∫a,score ε μ ν edge y x good label e f (snapshot S z w src tgt u a) ∂LevelScale.measure S)=
      ExpectedBudget.pairScore S (fun j => z (src (edge j))-z (tgt (edge j)))
        (truncatedPositive S z w src tgt u ε μ ν edge y x good label) (e,f) := by
  have hb (a : Place K S×ℝ) : |score ε μ ν edge y x good label e f (snapshot S z w src tgt u a)| ≤ 2 := by
    have h := LevelScores.score_bounds ε (frequency μ (snapshot S z w src tgt u a))
      (event ν (fun j => (snapshot S z w src tgt u a).1 (edge j)=true))
      (good (snapshot S z w src tgt u a)) (label (snapshot S z w src tgt u a))
      ((snapshot S z w src tgt u a).2 x) ((snapshot S z w src tgt u a).2 (y e))
      ((snapshot S z w src tgt u a).2 (y f)) ((snapshot S z w src tgt u a).1 (edge e))
      ((snapshot S z w src tgt u a).1 (edge f))
    apply abs_le.mpr
    change -1 ≤ score ε μ ν edge y x good label e f (snapshot S z w src tgt u a) ∧
      score ε μ ν edge y x good label e f (snapshot S z w src tgt u a) ≤ 2 at h
    constructor <;> linarith
  rw [LevelScale.measure,FiniteLevels.integral_eq _ _ _ _
    (measurable_score S z w src tgt u ε μ ν edge y x good label e f) 2 hb]
  simp_rw [piece_score S z w src tgt u ε μ ν edge y x good label hm e f]
  simp only [ExpectedBudget.pairScore,LevelScale.weight,div_eq_mul_inv,mul_comm]
  rfl
end
end PlanarUnitDistances.SlotIntegration

namespace PlanarUnitDistances.TailVariation
open MeasureTheory Set Finset Real FiniteLaw TailWindows PlaceScore WindowVariation
open scoped Classical
noncomputable section
variable {E F : Type*} [Fintype E] [Fintype F]

lemma tail_measurable (μ : Law E) (x : E → ℝ) : Measurable (tail μ x) := by
  unfold tail event avg
  exact Finset.measurable_sum _ (fun e _ => (Measurable.ite measurableSet_Iio measurable_const measurable_const).const_mul (μ.val e))
lemma variation_measurable (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ) (ε : ℝ) :
    Measurable (variation ε (tail μ x) (tail ν y)) := by
  apply Measurable.ite _ ((measurable_const.mul (tail_measurable ν y)).mul
    (measurable_const.sub (tail_measurable ν y))) measurable_const
  exact (measurableSet_le measurable_const (tail_measurable μ x)).inter
    (measurableSet_le (tail_measurable μ x) measurable_const)
lemma variation_bounds (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ) (ε s : ℝ) :
    0 ≤ variation ε (tail μ x) (tail ν y) s ∧ variation ε (tail μ x) (tail ν y) s ≤ 1/2 := by
  constructor
  · exact variation_nonneg (fun t => ⟨event_nonneg ν _,event_le_one ν _⟩) s
  · unfold variation
    split_ifs <;> nlinarith [sq_nonneg (tail ν y s-1/2)]
lemma variation_off (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε l r : ℝ} (hε : 0<ε) (hl : ∀e,l ≤ x e) (hr : ∀e,x e ≤ r) {s : ℝ} (hs : s∉Icc l r) :
    variation ε (tail μ x) (tail ν y) s=0 := by
  have hc : ¬common ε (tail μ x s) := by
    by_cases hsl : s<l
    · rw [below_all μ x s (fun e => hsl.trans_le (hl e))]
      unfold common
      intro h
      linarith [h.2]
    · have hrs : r<s := by simp only [Set.mem_Icc,not_and_or,not_le] at hs; exact hs.resolve_left hsl
      rw [above_all μ x s (fun e => (hr e).trans hrs.le)]
      exact fun h => not_le.mpr hε h.1
  simp [variation,hc]
lemma variation_integrable (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε l r : ℝ} (hε : 0<ε) (hl : ∀e,l ≤ x e) (hr : ∀e,x e ≤ r) :
    Integrable (variation ε (tail μ x) (tail ν y)) := by
  have hi : IntegrableOn (variation ε (tail μ x) (tail ν y)) (Icc l r) := by
    apply Integrable.mono' (integrable_const (1/2:ℝ)) (variation_measurable μ ν x y ε).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (variation_bounds μ ν x y ε s).1]
      exact (variation_bounds μ ν x y ε s).2
  have he : (Icc l r).indicator (variation ε (tail μ x) (tail ν y))=variation ε (tail μ x) (tail ν y) := by
    ext s
    by_cases hs : s∈Icc l r
    · exact Set.indicator_of_mem hs _
    · rw [Set.indicator_of_notMem hs,variation_off μ ν x y hε hl hr hs]
  rw [←he]
  exact hi.integrable_indicator measurableSet_Icc
lemma variation_integral (μ : Law E) (ν : Law F) (x : E → ℝ) (y : F → ℝ)
    {ε l r : ℝ} (hε : 0<ε) (hl : ∀e,l ≤ x e) (hr : ∀e,x e ≤ r) :
    (∫s in Icc l r,variation ε (tail μ x) (tail ν y) s)=
      ∫s,variation ε (tail μ x) (tail ν y) s := by
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    by_cases hs : s∈Icc l r
    · exact Set.indicator_of_mem hs _
    · rw [Set.indicator_of_notMem hs,variation_off μ ν x y hε hl hr hs]
end
end PlanarUnitDistances.TailVariation

namespace PlanarUnitDistances.ActualBudget
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots SlotIntegration TailWindows
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype V] [Fintype E] [Fintype F]

omit [IsGalois ℚ K] [Fintype V] in
lemma snapshot_frequency (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E) (v : Place K S) (s : ℝ) :
    frequency μ (snapshot S z w src tgt u (v,s))=
      tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))) s := by
  simp only [frequency,snapshot,LevelStates.bit,TailWindows.tail,threshold,decide_eq_true_eq]
omit [IsGalois ℚ K] [Fintype V] [Fintype E] in
lemma snapshot_conditional (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (ν : Law F) (edge : F → E) (v : Place K S) (s : ℝ) :
    event ν (fun j => (snapshot S z w src tgt u (v,s)).1 (edge j)=true)=
      tail ν (fun j => threshold (av K v) (z (src (edge j))-z (tgt (edge j)))) s := by
  simp only [snapshot,LevelStates.bit,TailWindows.tail,threshold,decide_eq_true_eq]

theorem star_upper (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (μ : Law E) (ν : Law F) (edge : F → E) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hsrc : ∀j,0<ν.val j → src (edge j)=x)
    (hu : ∀j,0<ν.val j → (z (src (edge j))-z (tgt (edge j)))*(w (src (edge j))-w (tgt (edge j)))=1)
    (hinj : ∀e f,0<ν.val e → 0<ν.val f → e≠f → z (tgt (edge e))≠z (tgt (edge f)))
    (hm : ∀e,z (src e)-z (tgt e)∈S)
    (hΔ : ∀e f,0<ν.val e → 0<ν.val f → e≠f →
      differenceProduct (z (src (edge e))-z (tgt (edge e))) (z (src (edge f))-z (tgt (edge f)))∈S) :
    avg (pair ν ν) (fun ef => ∫a,score ε μ ν edge (tgt ∘ edge) x good label ef.1 ef.2
      (snapshot S z w src tgt u a) ∂LevelScale.measure S) ≤
    2*log 2+(1/20000000:ℝ)*((∑v : Place K S,∫s,WindowVariation.variation ε
      (tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))))
      (tail ν (fun j => threshold (av K v) (z (src (edge j))-z (tgt (edge j))))) s)/(Module.finrank ℚ K:ℝ))+
    (2*(∫a,active ε μ good label x (snapshot S z w src tgt u a) ∂LevelScale.measure S))*
      event (pair ν ν) (fun ef => ef.1=ef.2) := by
  let d : F → K := fun j => z (src (edge j))-z (tgt (edge j))
  let f := truncatedPositive S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label
  have hpair (e f' : F) := score_eq_pairScore S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label
    (fun j => hm (edge j)) e f'
  simp_rw [hpair]
  apply ExpectedBudget.star_upper μ ν S d
    (fun v e => threshold (av K v) (z (src e)-z (tgt e)))
    (fun j hj => left_ne_zero_of_mul_eq_one (hu j hj))
    (fun e f he hf hef => by
      dsimp [d]
      rw [hsrc e he,hsrc f hf]
      exact fun h => hinj e f he hf hef (sub_right_injective h))
    hΔ hε hε' f
    (fun e f v => positive_integrable S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label e f v)
  · intro e f' he hf hef v s
    dsimp only [f,truncatedPositive]
    by_cases hs : s∈Icc (-radius K S v) (radius K S v)
    · rw [Set.indicator_of_mem hs]
      unfold positive
      rw [snapshot_frequency,snapshot_conditional]
      have hue := hu e he
      have huf := hu f' hf
      rw [hsrc e he] at hue
      rw [hsrc f' hf] at huf
      have hh := LevelSlotGeometry.positive_le_cap S z w u v s ε
        (tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))))
        (tail ν (fun j => threshold (av K v) (d j))) hε'
        (good (snapshot S z w src tgt u (v,s))) (label (snapshot S z w src tgt u (v,s)))
        x (tgt (edge e)) (tgt (edge f')) hue huf (hinj e f' he hf hef)
      convert hh using 1 <;> simp only [snapshot,d,Function.comp_apply,LevelStates.bit,threshold,hsrc e he,hsrc f' hf]
      congr 1
    · rw [Set.indicator_of_notMem hs]
      unfold PlaceScore.cap
      exact add_nonneg (mul_nonneg (PlaceScore.reward_bounds _ _ _ true).1 (PlaceScore.ind_nonneg _ _))
        (mul_nonneg (PlaceScore.reward_bounds _ _ _ false).1 (PlaceScore.ind_nonneg _ _))
  · intro v
    exact TailVariation.variation_integrable μ ν _ _ hε
      (fun e => (threshold_in_range K (hm e) v).1) (fun e => (threshold_in_range K (hm e) v).2)
  · intro e
    rw [←hpair]
    exact integrated_diagonal S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label e
end
end PlanarUnitDistances.ActualBudget

namespace PlanarUnitDistances.ActualBudgetIntegral
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudget FiniteLawIntegral
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype E] [Fintype F]

omit [IsGalois ℚ K] in
lemma variation_integral (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    {ε : ℝ} (hε : 0<ε) (μ : Law E) (ν : Law F) (edge : F → E)
    (hm : ∀e,z (src e)-z (tgt e)∈S) :
    (∫a,commonVariation ε μ ν edge (snapshot S z w src tgt u a) ∂LevelScale.measure S)=
      (∑v : Place K S,∫s,WindowVariation.variation ε
        (TailWindows.tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))))
        (TailWindows.tail ν (fun j => threshold (av K v) (z (src (edge j))-z (tgt (edge j))))) s)/
        (Module.finrank ℚ K:ℝ) := by
  have hB (a : Data V E) : |commonVariation ε μ ν edge a| ≤ 1/2 := by
    unfold commonVariation
    split_ifs
    · rw [abs_of_nonneg (StarScore.variation_nonneg _ _)]
      exact StarScore.variation_le_half _ _
    · norm_num
  rw [LevelScale.measure,FiniteLevels.integral_eq (LevelScale.weight K) _ _ _
    (measurable_value S z w src tgt u _) (1/2) (fun a => hB _)]
  have he (v : Place K S) (s : ℝ) :
      commonVariation ε μ ν edge (snapshot S z w src tgt u (v,s))=
      WindowVariation.variation ε
        (TailWindows.tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))))
        (TailWindows.tail ν (fun j => threshold (av K v) (z (src (edge j))-z (tgt (edge j))))) s := by
    simp only [commonVariation,WindowVariation.variation,StarScore.variation,StarScore.frequency,
      snapshot_frequency,snapshot_conditional]
  simp_rw [he]
  change (Module.finrank ℚ K:ℝ)⁻¹*_=_
  rw [div_eq_inv_mul]
  congr 1
  apply sum_congr rfl
  intro v _
  exact TailVariation.variation_integral μ ν _ _ hε
    (fun e => (threshold_in_range K (hm e) v).1) (fun e => (threshold_in_range K (hm e) v).2)

theorem upper (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (μ : Law E) (ν : Law F) (edge : F → E) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hsrc : ∀j,0<ν.val j → src (edge j)=x)
    (hu : ∀j,0<ν.val j → (z (src (edge j))-z (tgt (edge j)))*(w (src (edge j))-w (tgt (edge j)))=1)
    (hinj : ∀e f,0<ν.val e → 0<ν.val f → e≠f → z (tgt (edge e))≠z (tgt (edge f)))
    (hm : ∀e,z (src e)-z (tgt e)∈S)
    (hΔ : ∀e f,0<ν.val e → 0<ν.val f → e≠f →
      differenceProduct (z (src (edge e))-z (tgt (edge e))) (z (src (edge f))-z (tgt (edge f)))∈S) :
    (∫a,avg (pair ν ν) (fun ef => score ε μ ν edge (tgt ∘ edge) x good label ef.1 ef.2
      (snapshot S z w src tgt u a)) ∂LevelScale.measure S) ≤
    2*log 2+(1/20000000:ℝ)*(∫a,commonVariation ε μ ν edge (snapshot S z w src tgt u a) ∂LevelScale.measure S)+
    (2*(∫a,active ε μ good label x (snapshot S z w src tgt u a) ∂LevelScale.measure S))*
      event (pair ν ν) (fun ef => ef.1=ef.2) := by
  rw [integral_avg (pair ν ν) _ (fun ef => score_integrable S z w src tgt u ε μ ν edge (tgt ∘ edge) x good label ef.1 ef.2),
    variation_integral S z w src tgt u hε μ ν edge hm]
  exact star_upper S z w src tgt u μ ν edge x good label hε hε' hsrc hu hinj hm hΔ
end
end PlanarUnitDistances.ActualBudgetIntegral

namespace PlanarUnitDistances.ActualFamilyBudget
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudgetIntegral FiniteLawIntegral
open scoped Classical
noncomputable section
variable {K V E F B : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype E] [Fintype F] [Fintype B]

theorem upper (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (μ : Law E) (β : Law B) (ν : B → Law F) (edge : B → F → E) (x : B → V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hsrc : ∀b,0<β.val b → ∀j,0<(ν b).val j → src (edge b j)=x b)
    (hu : ∀b,0<β.val b → ∀j,0<(ν b).val j →
      (z (src (edge b j))-z (tgt (edge b j)))*(w (src (edge b j))-w (tgt (edge b j)))=1)
    (hinj : ∀b,0<β.val b → ∀e f,0<(ν b).val e → 0<(ν b).val f → e≠f →
      z (tgt (edge b e))≠z (tgt (edge b f)))
    (hm : ∀e,z (src e)-z (tgt e)∈S)
    (hΔ : ∀b,0<β.val b → ∀e f,0<(ν b).val e → 0<(ν b).val f → e≠f →
      differenceProduct (z (src (edge b e))-z (tgt (edge b e)))
        (z (src (edge b f))-z (tgt (edge b f)))∈S) :
    (∫a,avg β (fun b => avg (pair (ν b) (ν b)) (fun ef =>
      score ε μ (ν b) (edge b) (tgt ∘ edge b) (x b) good label ef.1 ef.2
        (snapshot S z w src tgt u a))) ∂LevelScale.measure S) ≤
      2*log 2+(1/20000000:ℝ)*(∫a,avg β (fun b =>
        commonVariation ε μ (ν b) (edge b) (snapshot S z w src tgt u a)) ∂LevelScale.measure S)+
      2*avg β (fun b => (∫a,active ε μ good label (x b) (snapshot S z w src tgt u a) ∂LevelScale.measure S)*
        event (pair (ν b) (ν b)) (fun ef => ef.1=ef.2)) := by
  rw [integral_avg β (fun b a => avg (pair (ν b) (ν b)) (fun ef =>
      score ε μ (ν b) (edge b) (tgt ∘ edge b) (x b) good label ef.1 ef.2
        (snapshot S z w src tgt u a))) (fun b => integrable_value S z w src tgt u (fun a => avg (pair (ν b) (ν b)) (fun ef =>
      score ε μ (ν b) (edge b) (tgt ∘ edge b) (x b) good label ef.1 ef.2 a))),
    integral_avg β (fun b a => commonVariation ε μ (ν b) (edge b) (snapshot S z w src tgt u a))
      (fun b => integrable_value S z w src tgt u (commonVariation ε μ (ν b) (edge b)))]
  have hh := avg_mono_support β (fun b hb => ActualBudgetIntegral.upper S z w src tgt u μ (ν b)
    (edge b) (x b) good label hε hε' (hsrc b hb) (hu b hb) (hinj b hb) hm (hΔ b hb))
  simp only [avg_add,avg_const,avg_smul] at hh
  convert hh using 1
  congr 1
  rw [←avg_smul]
  apply avg_congr
  intro b
  ring
end
end PlanarUnitDistances.ActualFamilyBudget

namespace PlanarUnitDistances.ActualRowBudget
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudgetIntegral FiniteLawIntegral FiniteStarCoupling RareRows
open scoped Classical
noncomputable section
variable {K V P Q : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q]

theorem raw (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ σ : Law (P×Q))
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<σ.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y))
    (hm : ∀p q,z (x p)-z (y q)∈S)
    (hΔ : ∀p q r,q≠r → differenceProduct (z (x p)-z (y q)) (z (x p)-z (y r))∈S) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫a,scoreP ε (ActualSlots.frequency μ (s a)) σ (fun p q => (s a).1 (p,q))
      (fun p => (s a).2 (x p)) (fun q => (s a).2 (y q)) (good (s a)) (label (s a)) ∂LevelScale.measure S) ≤
    2*log 2+(1/20000000:ℝ)*(∫a,if PlaceScore.common ε (ActualSlots.frequency μ (s a)) then
      VP σ (fun p q => (s a).1 (p,q)) else 0 ∂LevelScale.measure S)+
    2*avg (left σ) (fun p => (∫a,active ε μ good label (x p) (s a) ∂LevelScale.measure S)*
      event (pair (row σ p) (row σ p)) (fun qq => qq.1=qq.2)) := by
  dsimp only
  let src : P×Q → V := fun pq => x pq.1
  let tgt : P×Q → V := fun pq => y pq.2
  let s := snapshot S z w src tgt u
  have hb := ActualFamilyBudget.upper S z w src tgt u μ (left σ) (row σ)
    (fun p q => (p,q)) x good label hε hε'
    (fun _ _ _ _ => rfl)
    (fun p hp q hq => hu p q (by rw [←row_weight σ p q]; exact mul_pos hp hq))
    (fun _ _ _ _ _ _ hqr => hy.ne hqr)
    (fun pq => hm pq.1 pq.2)
    (fun p _ q r _ _ hqr => hΔ p q r hqr)
  have hv (a : Data V (P×Q)) : avg (left σ) (fun p => commonVariation ε μ (row σ p) (fun q => (p,q)) a)=
      (if PlaceScore.common ε (ActualSlots.frequency μ a) then VP σ (fun p q => a.1 (p,q)) else 0) := by
    by_cases hc : PlaceScore.common ε (ActualSlots.frequency μ a)
    · simp only [commonVariation,hc,ite_true,VP]
    · simp only [commonVariation,hc,ite_false,avg_const]
  simp_rw [hv] at hb
  exact hb

theorem compressed_upper (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ σ : Law (P×Q))
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<σ.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y))
    (hm : ∀p q,z (x p)-z (y q)∈S)
    (hΔ : ∀p q r,q≠r → differenceProduct (z (x p)-z (y q)) (z (x p)-z (y r))∈S)
    (hd : ∀p q,σ.val (p,q) ≤ d*(left σ).val p) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫a,scoreP ε (ActualSlots.frequency μ (s a)) σ (fun p q => (s a).1 (p,q))
      (fun p => (s a).2 (x p)) (fun q => (s a).2 (y q)) (good (s a)) (label (s a)) ∂LevelScale.measure S) ≤
    2*log 2+(1/20000000:ℝ)*(∫a,if PlaceScore.common ε (ActualSlots.frequency μ (s a)) then
      VP σ (fun p q => (s a).1 (p,q)) else 0 ∂LevelScale.measure S)+
    2*d*avg (left σ) (fun p => ∫a,active ε μ good label (x p) (s a) ∂LevelScale.measure S) := by
  dsimp only
  have hb := raw S z w x y u μ σ good label hε hε' hu hy hm hΔ
  have hc := TemplateCollision.row_weighted σ
    (fun p => ∫a,active ε μ good label (x p)
      (snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u a) ∂LevelScale.measure S)
    (fun p => integral_nonneg (fun a => add_nonneg (RareScore.ind_nonneg _) (RareScore.ind_nonneg _))) hd
  dsimp only at hb
  linarith
end
end PlanarUnitDistances.ActualRowBudget

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ActualScoreBook
open MeasureTheory FiniteLaw LevelSnapshot ActualSlots ScoreBook FiniteLawIntegral
  FiniteStarCoupling RareRows RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

lemma average (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) (F : Data V (P×Q) → ℝ) :
    (∫a,F (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a) ∂LevelScale.measure S)=
      mass S*avg (make S z w x y u π h ε good label hm).levels F := by
  have he := compress_avg (LevelScale.measure S) hm
    (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u)
    (measurable_snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u) F
  exact (mul_comm _ _).trans ((eq_div_iff hm.ne').mp he) |>.symm

lemma active_point (σ : Law (Data V (P×Q))) (π : Law (P×Q)) (x : P → V)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool)) :
    avg (left π) (fun p => avg σ (fun a => active ε π good label (x p) a))=
      event σ (fun a => PlaceScore.common ε (ActualSlots.frequency π a))+
      cut σ (fun a => ¬PlaceScore.common ε (ActualSlots.frequency π a) ∧ good a)
        (fun a => RareMoments.hp π (fun p q => a.1 (p,q)) (fun p => a.2 (x p)) (label a)) := by
  rw [avg_comm]
  unfold active
  simp_rw [avg_add,avg_const]
  congr 1
  apply avg_congr
  intro a
  by_cases hc : PlaceScore.common ε (ActualSlots.frequency π a)
  · simp [rareException,hc,ind,avg_const]
  · by_cases hg : good a
    · simp only [rareException,hc,hg,not_false_eq_true,true_and,ind,ite_true]
      rfl
    · simp [rareException,hc,hg,ind,avg_const]

lemma point_activity (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) :
    let B := make S z w x y u π h ε good label hm
    avg (left π) (fun p => ∫a,active ε π good label (x p)
      (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a) ∂LevelScale.measure S)=
      mass S*(B.WC+B.HP) := by
  dsimp only
  simp_rw [average S z w x y u π h ε good label hm]
  rw [avg_smul,active_point]
  rfl

lemma active_center (σ : Law (Data V (P×Q))) (π : Law (P×Q)) (y : Q → V)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool)) :
    avg (right π) (fun q => avg σ (fun a => active ε π good label (y q) a))=
      event σ (fun a => PlaceScore.common ε (ActualSlots.frequency π a))+
      cut σ (fun a => ¬PlaceScore.common ε (ActualSlots.frequency π a) ∧ good a)
        (fun a => RareMoments.hq π (fun p q => a.1 (p,q)) (fun q => a.2 (y q)) (label a)) := by
  rw [avg_comm]
  unfold active
  simp_rw [avg_add,avg_const]
  congr 1
  apply avg_congr
  intro a
  by_cases hc : PlaceScore.common ε (ActualSlots.frequency π a)
  · simp [rareException,hc,ind,avg_const]
  · by_cases hg : good a
    · simp only [rareException,hc,hg,not_false_eq_true,true_and,ind,ite_true]
      rfl
    · simp [rareException,hc,hg,ind,avg_const]

lemma center_activity (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) :
    let B := make S z w x y u π h ε good label hm
    avg (right π) (fun q => ∫a,active ε π good label (y q)
      (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a) ∂LevelScale.measure S)=
      mass S*(B.WC+B.HQ) := by
  dsimp only
  simp_rw [average S z w x y u π h ε good label hm]
  rw [avg_smul,active_center]
  rfl
end
end PlanarUnitDistances.ActualScoreBook

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

lemma vanishing_pos (n : ℕ) : 0 < vanishing n := by unfold vanishing; positivity
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
-- module Solutions.OAIQ2_Uni.UnitDistances_PredictionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LevelSnapshot
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]
omit [Fintype V] [Fintype E] in
lemma snapshot_swap (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : PlaceLevels.Place K S×ℝ) :
    snapshot S z w tgt src u a=snapshot S z w src tgt u a := by
  unfold snapshot
  congr 1
  funext e
  dsimp [LevelStates.bit]
  rw [AbsoluteValue.map_sub]
end
end PlanarUnitDistances.LevelSnapshot

namespace PlanarUnitDistances.ActualColumnBudget
open MeasureTheory Set Finset FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudgetIntegral FiniteLawIntegral FiniteStarCoupling RareRows
open scoped Classical
noncomputable section
variable {K V P Q : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q]

theorem raw (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ σ : Law (P×Q))
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<σ.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hx : Function.Injective (z ∘ x))
    (hm : ∀p q,z (y q)-z (x p)∈S)
    (hΔ : ∀q p r,p≠r → differenceProduct (z (y q)-z (x p)) (z (y q)-z (x r))∈S) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫a,scoreQ ε (ActualSlots.frequency μ (s a)) σ (fun p q => (s a).1 (p,q))
      (fun p => (s a).2 (x p)) (fun q => (s a).2 (y q)) (good (s a)) (label (s a)) ∂LevelScale.measure S) ≤
    2*Real.log 2+(1/20000000:ℝ)*(∫a,if PlaceScore.common ε (ActualSlots.frequency μ (s a)) then
      VQ σ (fun p q => (s a).1 (p,q)) else 0 ∂LevelScale.measure S)+
    2*avg (right σ) (fun q => (∫a,active ε μ good label (y q) (s a) ∂LevelScale.measure S)*
      event (pair (col σ q) (col σ q)) (fun pp => pp.1=pp.2)) := by
  dsimp only
  let src : P×Q → V := fun pq => y pq.2
  let tgt : P×Q → V := fun pq => x pq.1
  have hb := ActualFamilyBudget.upper S z w src tgt u μ (right σ) (col σ)
    (fun q p => (p,q)) y good label hε hε'
    (fun _ _ _ _ => rfl)
    (fun q hq p hp => by
      have he := hu p q (by rw [←col_weight σ p q]; exact mul_pos hq hp)
      change (z (y q)-z (x p))*(w (y q)-w (x p))=1
      calc
        _ = (z (x p)-z (y q))*(w (x p)-w (y q)) := by ring
        _ = 1 := he)
    (fun _ _ _ _ _ _ hpr => hx.ne hpr)
    (fun pq => hm pq.1 pq.2)
    (fun q _ p r _ _ hpr => hΔ q p r hpr)
  have hv (a : Data V (P×Q)) : avg (right σ) (fun q => commonVariation ε μ (col σ q) (fun p => (p,q)) a)=
      (if PlaceScore.common ε (ActualSlots.frequency μ a) then VQ σ (fun p q => a.1 (p,q)) else 0) := by
    by_cases hc : PlaceScore.common ε (ActualSlots.frequency μ a)
    · simp only [commonVariation,hc,ite_true,VQ]
    · simp only [commonVariation,hc,ite_false,avg_const]
  simp_rw [hv] at hb
  dsimp [src,tgt] at hb
  simp_rw [snapshot_swap S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u] at hb
  exact hb

lemma col_weighted (π : Law (P×Q)) (f : Q → ℝ) (hf : ∀q,0 ≤ f q)
    {d : ℝ} (hp : ∀p q,π.val (p,q) ≤ d*(right π).val q) :
    avg (right π) (fun q => f q*event (pair (col π q) (col π q)) (fun pp => pp.1=pp.2)) ≤
      d*avg (right π) f := by
  simp only [avg,TemplateCollision.collision_eq,mul_sum]
  apply sum_le_sum
  intro q _
  calc
    _ = f q*∑p,π.val (p,q)*(col π q).val p := by
      rw [mul_sum]
      apply sum_congr rfl; intro p _
      rw [pow_two,←col_weight π p q]
      ring
    _ ≤ f q*∑p,(d*(right π).val q)*(col π q).val p := by
      apply mul_le_mul_of_nonneg_left _ (hf q)
      apply sum_le_sum; intro p _
      exact mul_le_mul_of_nonneg_right (hp p q) ((col π q).nonneg p)
    _ = _ := by rw [←mul_sum,(col π q).total]; ring

theorem upper (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ σ : Law (P×Q))
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<σ.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hx : Function.Injective (z ∘ x))
    (hm : ∀p q,z (y q)-z (x p)∈S)
    (hΔ : ∀q p r,p≠r → differenceProduct (z (y q)-z (x p)) (z (y q)-z (x r))∈S)
    (hd : ∀p q,σ.val (p,q) ≤ d*(right σ).val q) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫a,scoreQ ε (ActualSlots.frequency μ (s a)) σ (fun p q => (s a).1 (p,q))
      (fun p => (s a).2 (x p)) (fun q => (s a).2 (y q)) (good (s a)) (label (s a)) ∂LevelScale.measure S) ≤
    2*Real.log 2+(1/20000000:ℝ)*(∫a,if PlaceScore.common ε (ActualSlots.frequency μ (s a)) then
      VQ σ (fun p q => (s a).1 (p,q)) else 0 ∂LevelScale.measure S)+
    2*d*avg (right σ) (fun q => ∫a,active ε μ good label (y q) (s a) ∂LevelScale.measure S) := by
  dsimp only
  have hb := raw S z w x y u μ σ good label hε hε' hu hx hm hΔ
  have hc := col_weighted σ
    (fun q => ∫a,active ε μ good label (y q)
      (snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u a) ∂LevelScale.measure S)
    (fun q => integral_nonneg (fun a => add_nonneg (RareScore.ind_nonneg _) (RareScore.ind_nonneg _))) hd
  dsimp only at hb
  linarith
end
end PlanarUnitDistances.ActualColumnBudget

namespace PlanarUnitDistances.ActualTemplateBudget
open MeasureTheory Set Finset FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudgetIntegral FiniteLawIntegral FiniteStarCoupling RareRows TemplateCoupling
open scoped Classical
noncomputable section
variable {K V P Q Θ : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q] [Fintype Θ]

theorem upper (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ π : Law (P×Q)) (a : Q → Law Θ)
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y))
    (hm : ∀p q,z (x p)-z (y q)∈S)
    (hΔ : ∀p q r,q≠r → differenceProduct (z (x p)-z (y q)) (z (x p)-z (y r))∈S)
    (hd : ∀p q,π.val (p,q) ≤ d*(left π).val p) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫b,scoreT ε (ActualSlots.frequency μ (s b)) π a (fun p q => (s b).1 (p,q))
      (fun p => (s b).2 (x p)) (fun q => (s b).2 (y q)) (good (s b)) (label (s b)) ∂LevelScale.measure S) ≤
    2*Real.log 2+(1/20000000:ℝ)*(∫b,if PlaceScore.common ε (ActualSlots.frequency μ (s b)) then
      avg (templates π a) (fun θ => VP (slice π a θ) (fun p q => (s b).1 (p,q))) else 0 ∂LevelScale.measure S)+
    2*(Fintype.card Θ:ℝ)*d*avg (left π) (fun p => ∫b,active ε μ good label (x p) (s b) ∂LevelScale.measure S) := by
  dsimp only
  let src : P×Q → V := fun pq => x pq.1
  let tgt : P×Q → V := fun pq => y pq.2
  let s := snapshot S z w src tgt u
  let F (θ : Θ) (b : Data V (P×Q)) := scoreP ε (ActualSlots.frequency μ b) (slice π a θ)
    (fun p q => b.1 (p,q)) (fun p => b.2 (x p)) (fun q => b.2 (y q)) (good b) (label b)
  let G (θ : Θ) (b : Data V (P×Q)) := if PlaceScore.common ε (ActualSlots.frequency μ b) then
    VP (slice π a θ) (fun p q => b.1 (p,q)) else 0
  have hh := avg_mono_support (templates π a) (fun θ hθ => ActualRowBudget.raw S z w x y u μ (slice π a θ)
    good label hε hε' (fun p q hpq => hu p q (by
      have he := slice_weight π a θ (p,q)
      have hp := mul_pos hθ hpq
      rw [he] at hp
      exact (mul_pos_iff.mp hp).elim And.left (fun h => False.elim (not_lt_of_ge ((a q).nonneg θ) h.2)))) hy hm hΔ)
  have hF : (∫b,scoreT ε (ActualSlots.frequency μ (s b)) π a (fun p q => (s b).1 (p,q))
      (fun p => (s b).2 (x p)) (fun q => (s b).2 (y q)) (good (s b)) (label (s b)) ∂LevelScale.measure S)=
      avg (templates π a) (fun θ => ∫b,F θ (s b) ∂LevelScale.measure S) :=
    integral_avg (templates π a) _ (fun θ => integrable_value S z w src tgt u (F θ))
  have hG : (∫b,if PlaceScore.common ε (ActualSlots.frequency μ (s b)) then
      avg (templates π a) (fun θ => VP (slice π a θ) (fun p q => (s b).1 (p,q))) else 0 ∂LevelScale.measure S)=
      avg (templates π a) (fun θ => ∫b,G θ (s b) ∂LevelScale.measure S) := by
    have he (b : Data V (P×Q)) : (if PlaceScore.common ε (ActualSlots.frequency μ b) then
      avg (templates π a) (fun θ => VP (slice π a θ) (fun p q => b.1 (p,q))) else 0)=
      avg (templates π a) (fun θ => G θ b) := by
      dsimp [G]
      split_ifs with hc
      · rfl
      · simp only [avg_const]
    simp_rw [he]
    exact integral_avg (templates π a) _ (fun θ => integrable_value S z w src tgt u (G θ))
  change (∫b,scoreT ε (ActualSlots.frequency μ (s b)) π a (fun p q => (s b).1 (p,q))
      (fun p => (s b).2 (x p)) (fun q => (s b).2 (y q)) (good (s b)) (label (s b)) ∂LevelScale.measure S) ≤ _
  rw [hF,hG]
  simp only [avg_add,avg_const,avg_smul] at hh
  have hc := TemplateCollision.weighted π a
    (fun p => ∫b,active ε μ good label (x p) (s b) ∂LevelScale.measure S)
    (fun p => integral_nonneg (fun b => add_nonneg (RareScore.ind_nonneg _) (RareScore.ind_nonneg _))) hd
  change avg (templates π a) (fun θ => ∫b,F θ (s b) ∂LevelScale.measure S) ≤
    2*Real.log 2+(1/20000000:ℝ)*avg (templates π a) (fun θ => ∫b,G θ (s b) ∂LevelScale.measure S)+_ at hh
  nlinarith
end
end PlanarUnitDistances.ActualTemplateBudget

namespace PlanarUnitDistances.PredictionPairBudget
open MeasureTheory Set Finset Real PlaceLevels LevelGeometry PlaceScore
open scoped Classical
noncomputable section

lemma interval_bound {l u a b c : ℝ} (hlu : l ≤ u) (hla : l ≤ a) (hbu : b ≤ u) (hc : 0 ≤ c)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Icc l u))
    (hcap : ∀s∈Icc l u,f s ≤ (if s ≤ a+c then 1 else 0)+(if b-c ≤ s then 1 else 0)-1) :
    (∫s in Icc l u,f s) ≤ a-b+2*c := by
  let g := fun s => ind (Icc l (min u (a+c))) s+ind (Icc (max l (b-c)) u) s-ind (Icc l u) s
  have hg : Integrable g := ((ind_Icc_integrable _ _).add (ind_Icc_integrable _ _)).sub
    (ind_Icc_integrable _ _)
  have hfg : (Icc l u).indicator f ≤ g := by
    intro s
    by_cases hs : s∈Icc l u
    · have h₁ : s∈Icc l (min u (a+c)) ↔ s ≤ a+c := by simp only [Set.mem_Icc,le_min_iff]; exact ⟨fun h => h.2.2,fun h => ⟨hs.1,hs.2,h⟩⟩
      have h₂ : s∈Icc (max l (b-c)) u ↔ b-c ≤ s := by simp only [Set.mem_Icc,max_le_iff]; exact ⟨fun h => h.1.2,fun h => ⟨⟨hs.1,h⟩,hs.2⟩⟩
      simpa only [g,ind,indicator_of_mem hs,indicator_apply,h₁,h₂,hs,ite_true] using hcap s hs
    · have h₁ : s∉Icc l (min u (a+c)) := fun hh => hs ⟨hh.1,hh.2.trans (min_le_left _ _)⟩
      have h₂ : s∉Icc (max l (b-c)) u := fun hh => hs ⟨(le_max_left _ _).trans hh.1,hh.2⟩
      simp only [g,ind,indicator_of_notMem hs,indicator_of_notMem h₁,indicator_of_notMem h₂]
      norm_num
  have hb := integral_mono (hf.integrable_indicator measurableSet_Icc) hg hfg
  rw [integral_indicator measurableSet_Icc] at hb
  have hpos₁ : 0 ≤ min u (a+c)-l := sub_nonneg.mpr (le_min hlu (by linarith))
  have hpos₂ : 0 ≤ u-max l (b-c) := sub_nonneg.mpr (max_le hlu (by linarith))
  have he : (∫s,g s)=min u (a+c)-max l (b-c) := by
    change (∫s,(ind (Icc l (min u (a+c)))+ind (Icc (max l (b-c)) u)) s-ind (Icc l u) s)=_
    rw [integral_sub ((ind_Icc_integrable _ _).add (ind_Icc_integrable _ _)) (ind_Icc_integrable _ _)]
    change ((∫s,ind (Icc l (min u (a+c))) s+ind (Icc (max l (b-c)) u) s)-_)=_
    rw [integral_add (ind_Icc_integrable _ _) (ind_Icc_integrable _ _)]
    rw [ind_Icc_integral,ind_Icc_integral,ind_Icc_integral,max_eq_right hpos₁,max_eq_right hpos₂,
      max_eq_right (sub_nonneg.mpr hlu)]
    ring
  rw [he] at hb
  linarith [min_le_right u (a+c),le_max_right l (b-c)]

variable {K V : Type*} [Field K] [NumberField K] [Fintype V]

lemma score_bounds (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V) (a : Place K S×ℝ) :
    -1 ≤ score S z w u x y a ∧ score S z w u x y a ≤ 1 := by
  unfold score
  split_ifs <;> norm_num

lemma measurable_score (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V) : Measurable (score S z w u x y) := by
  have h (v : V) := LevelStates.state_measurable S z w u v
  exact ((measurable_const.piecewise (measurableSet_eq_fun (h x).fst (h y).fst) measurable_const).add
    (measurable_const.piecewise (measurableSet_eq_fun (h x).snd (h y).snd) measurable_const)).sub measurable_const

lemma pair_place (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V)
    (hz : z x≠z y) (hw : w x≠w y) (hZ : z x-z y∈S) (hW : w x-w y∈S)
    (v : Place K S) :
    (∫s in Icc (-radius K S v) (radius K S v),score S z w u x y (v,s)) ≤
      -log (av K v (z x-z y))-log (av K v (w x-w y))+2*allowance v := by
  apply interval_bound (neg_le_self (radius_nonneg K S v))
    (threshold_in_range K hZ v).1 (log_in_range K hW v).2 (allowance_nonneg v)
  · apply Integrable.mono' (integrable_const (1:ℝ))
      ((measurable_score S z w u x y).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun s => by
      simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using abs_le.mpr (score_bounds S z w u x y (v,s)))
  · intro s _
    have h₁ : (LevelStates.state S z w u (v,s) x).1=(LevelStates.state S z w u (v,s) y).1 →
        s ≤  -log (av K v (z x-z y))+allowance v := by
      intro hh
      linarith [first_log_bound S z w u v s x y hz hh]
    have h₂ : (LevelStates.state S z w u (v,s) x).2=(LevelStates.state S z w u (v,s) y).2 →
        log (av K v (w x-w y))-allowance v ≤ s := by
      intro hh
      linarith [second_log_bound S z w u v s x y hw hh]
    unfold score
    split_ifs <;> simp_all

theorem full_pair [IsGalois ℚ K] (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V)
    (hz : z x≠z y) (hw : w x≠w y) (hZ : z x-z y∈S) (hW : w x-w y∈S) :
    (∫a,score S z w u x y a ∂LevelScale.measure S) ≤ 2*log 2 := by
  rw [LevelScale.measure,FiniteLevels.integral_eq (LevelScale.weight K) _ _ _
    (measurable_score S z w u x y) 1 (fun a => abs_le.mpr (score_bounds S z w u x y a))]
  change (Module.finrank ℚ K:ℝ)⁻¹ * _  ≤  _
  have hb := mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun v _ => pair_place S z w u x y hz hw hZ hW v))
    (inv_nonneg.mpr (Nat.cast_nonneg (Module.finrank ℚ K)))
  refine hb.trans_eq ?_
  simp only [sum_add_distrib,sum_sub_distrib,sum_neg_distrib]
  rw [mul_add,mul_sub,mul_neg,←div_eq_inv_mul,←div_eq_inv_mul,←div_eq_inv_mul,
    sum_log_product_formula K hZ (sub_ne_zero.mpr hz),sum_log_product_formula K hW (sub_ne_zero.mpr hw),
    GlobalPairBudget.total_allowance]
  ring
end
end PlanarUnitDistances.PredictionPairBudget

namespace PlanarUnitDistances.PredictionCut
open Finset MeasureTheory FiniteLaw RareScore PredictionCoupling FiniteLawIntegral
open scoped Classical
noncomputable section
variable {P H A B Ω : Type*} [Fintype P] [Fintype H]

lemma pairScore_bounds (x y : A×B) : -1 ≤ pairScore x y ∧ pairScore x y ≤ 1 := by
  unfold pairScore
  split_ifs <;> norm_num
lemma pairScore_normal (r : Bool) (l x y : A×B)
    (hx : ¬exceptional r l x) (hy : ¬exceptional r l y) : 0 ≤ pairScore x y := by
  cases r <;> simp only [exceptional,Bool.false_eq_true, ↓reduceIte,not_not] at hx hy
  · have he : x.1=y.1 := hx.trans hy.symm
    unfold pairScore
    simp only [he,ite_true]
    split_ifs <;> norm_num
  · have he : x.2=y.2 := hx.trans hy.symm
    unfold pairScore
    simp only [he,ite_true]
    split_ifs <;> norm_num

lemma cut_bound (c g : Prop) (r : Bool) (l x y : A×B) :
    (if c then pairScore x y else 0) ≤ pairScore x y+
      ind (¬c ∧ g ∧ exceptional r l x)+ind (¬c ∧ g ∧ exceptional r l y)+ind (¬c ∧ ¬g) := by
  by_cases hc : c
  · simp [hc,ind]
  · by_cases hg : g
    · by_cases hx : exceptional r l x
      · simp only [hc,hg,hx,ind,↓reduceIte,true_and,not_false_eq_true,not_true_eq_false]
        have hb := (pairScore_bounds x y).1
        split_ifs <;> linarith
      · by_cases hy : exceptional r l y
        · simp only [hc,hg,hx,hy,ind,↓reduceIte,true_and,not_false_eq_true,not_true_eq_false]
          linarith [(pairScore_bounds x y).1]
        · simpa [hc,hg,hx,hy,ind] using pairScore_normal r l x y hx hy
    · simp only [hc,hg,ind,↓reduceIte,false_and,true_and,not_false_eq_true,add_zero]
      linarith [(pairScore_bounds x y).1]

variable [MeasurableSpace Ω]

theorem integrated (μ : Law P) (h : P → H) (ν : Measure Ω)
    (common good : Ω → Prop) (r : Ω → Bool) (l : Ω → A×B) (x : Ω → P → A×B)
    (C : ℝ) (hC : 0 ≤ C)
    (_hcommon : Integrable (fun a => ind (common a)) ν)
    (hbad : Integrable (fun a => ind (¬common a ∧ ¬good a)) ν)
    (hex : ∀p,Integrable (fun a => ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p))) ν)
    (hfull : ∀p q,Integrable (fun a => pairScore (x a p) (x a q)) ν)
    (hcut : ∀p q,Integrable (fun a => if common a then pairScore (x a p) (x a q) else 0) ν)
    (hbound : ∀p q,p≠q → (∫a,pairScore (x a p) (x a q) ∂ν) ≤ C)
    {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    (∫a,avg (coupling μ h) (fun pp => if common a then pairScore (x a pp.1) (x a pp.2) else 0) ∂ν) ≤
      C+2*avg μ (fun p => ∫a,ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p)) ∂ν)+
      (∫a,ind (¬common a ∧ ¬good a) ∂ν)+
      (∫a,ind (common a) ∂ν)*((Fintype.card H:ℝ)*d) := by
  let e := fun p => ∫a,ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p)) ∂ν
  let wb := ∫a,ind (¬common a ∧ ¬good a) ∂ν
  let wc := ∫a,ind (common a) ∂ν
  have he0 (p : P) : 0 ≤ e p := integral_nonneg (fun a => ind_nonneg _)
  have hw0 : 0 ≤ wb := integral_nonneg (fun a => ind_nonneg _)
  have hc0 : 0 ≤ wc := integral_nonneg (fun a => ind_nonneg _)
  rw [integral_avg (coupling μ h) _ (fun pp => hcut pp.1 pp.2)]
  have hb (p q : P) : (∫a,if common a then pairScore (x a p) (x a q) else 0 ∂ν) ≤
      C+e p+e q+wb+(if p=q then wc else 0) := by
    by_cases hpq : p=q
    · subst q
      have hh : (∫a,if common a then pairScore (x a p) (x a p) else 0 ∂ν)=wc := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun a => by simp [pairScore,ind])
      rw [hh,ite_eq_left rfl]
      linarith [he0 p]
    · rw [ite_eq_right hpq,add_zero]
      have hh := integral_mono (hcut p q) (((hfull p q).add (hex p)).add (hex q) |>.add hbad)
        (fun a => cut_bound (common a) (good a) (r a) (l a) (x a p) (x a q))
      have hi₁ := integral_add (hfull p q) (hex p)
      have hi₂ := integral_add ((hfull p q).add (hex p)) (hex q)
      have hi₃ := integral_add (((hfull p q).add (hex p)).add (hex q)) hbad
      simp only [Pi.add_apply] at hh hi₁ hi₂ hi₃
      rw [hi₃,hi₂,hi₁] at hh
      exact hh.trans (by dsimp only [e,wb]; linarith [hbound p q hpq])
  have hh := avg_mono (coupling μ h) (fun pp => hb pp.1 pp.2)
  simp only [avg_add,avg_const,PredictionCoupling.first,PredictionCoupling.second,avg_indicator_mul] at hh
  have hdg := mul_le_mul_of_nonneg_left (PredictionCoupling.diagonal μ h hd hm) hc0
  change _ ≤ C+2*avg μ e+wb+wc*((Fintype.card H:ℝ)*d)
  linarith
end
end PlanarUnitDistances.PredictionCut

namespace PlanarUnitDistances.ActualPredictionBudget
open Finset MeasureTheory Real FiniteLaw RareScore PredictionCoupling FiniteLawIntegral
  LevelSnapshot PlaceLevels PredictionCut
open scoped Classical
noncomputable section
variable {K V E P H : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype E] [Fintype P] [Fintype H]

theorem upper (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law P) (h : P → H) (pmap : P → V)
    (hz : Function.Injective (z ∘ pmap)) (hw : Function.Injective (w ∘ pmap))
    (hZ : ∀p q,z (pmap p)-z (pmap q)∈S) (hW : ∀p q,w (pmap p)-w (pmap q)∈S)
    (c good : Data V E → Prop) (r : Data V E → Bool)
    (l : Data V E → (V → Bool)×(V → Bool))
    {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    let s := snapshot S z w src tgt u
    let x := fun a p => (s a).2 (pmap p)
    (∫a,(if c (s a) then avg μ (fun p => FiniteMarginalScore.tau (push (cond μ h (h p)) (x a))) else 0)
      ∂LevelScale.measure S) ≤
      2*log 2+2*avg μ (fun p => ∫a,ind (¬c (s a) ∧ good (s a) ∧
        exceptional (r (s a)) (l (s a)) (x a p)) ∂LevelScale.measure S)+
      (∫a,ind (¬c (s a) ∧ ¬good (s a)) ∂LevelScale.measure S)+
      (∫a,ind (c (s a)) ∂LevelScale.measure S)*((Fintype.card H:ℝ)*d) := by
  dsimp only
  let s := snapshot S z w src tgt u
  let x := fun a p => (s a).2 (pmap p)
  have he (a : Place K S×ℝ) :
      (if c (s a) then avg μ (fun p => FiniteMarginalScore.tau (push (cond μ h (h p)) (x a))) else 0)=
      avg (coupling μ h) (fun pp => if c (s a) then pairScore (x a pp.1) (x a pp.2) else 0) := by
    by_cases hc : c (s a)
    · simp only [hc,ite_true]
      exact (tau_eq μ h (x a)).symm
    · simp only [hc,ite_false,avg_const]
  change (∫a,(if c (s a) then avg μ (fun p => FiniteMarginalScore.tau (push (cond μ h (h p)) (x a))) else 0)
      ∂LevelScale.measure S) ≤ _
  simp_rw [he]
  apply integrated μ h (LevelScale.measure S) (c ∘ s) (good ∘ s) (r ∘ s) (l ∘ s) x
    (2*log 2) (mul_nonneg (by norm_num) (log_nonneg (by norm_num)))
  · exact integrable_value S z w src tgt u (fun a => ind (c a))
  · exact integrable_value S z w src tgt u (fun a => ind (¬c a ∧ ¬good a))
  · intro p
    exact integrable_value S z w src tgt u (fun a => ind (¬c a ∧ good a ∧ exceptional (r a) (l a) (a.2 (pmap p))))
  · intro p q
    exact integrable_value S z w src tgt u (fun a => pairScore (a.2 (pmap p)) (a.2 (pmap q)))
  · intro p q
    exact integrable_value S z w src tgt u (fun a => if c a then pairScore (a.2 (pmap p)) (a.2 (pmap q)) else 0)
  · intro p q hpq
    simpa only [PredictionPairBudget.score,pairScore,x,s,snapshot] using
      PredictionPairBudget.full_pair S z w u (pmap p) (pmap q) (hz.ne hpq) (hw.ne hpq) (hZ p q) (hW p q)
  · exact hd
  · exact hm
end
end PlanarUnitDistances.ActualPredictionBudget

namespace PlanarUnitDistances.ActualBookUpper
open MeasureTheory FiniteLaw FiniteStarCoupling LevelSnapshot ActualScoreBook ScoreBook
  RareRows RareMoments CommonTemplate TemplateCoupling RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H I : Type} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q] [Fintype H] [Fintype I]

omit [Fintype I] [Fintype H] in
theorem point (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y)) (hS : ∀v r,z v-z r∈S)
    (hΔ : ∀v r t,(z v-z r-(z v-z t))*((z v-z r)⁻¹-(z v-z t)⁻¹)∈S)
    (hd : ∀p q,π.val (p,q) ≤ d*(left π).val p) :
    let B := make S z w x y u π h ε good label hm
    B.DP ≤ B.CP/20000000+2*Real.log 2/mass S+2*d*(B.WC+B.HP) := by
  let B := make S z w x y u π h ε good label hm
  have hh := ActualRowBudget.compressed_upper S z w x y u π π good label hε hε' hu hy
    (fun p q => hS (x p) (y q)) (fun p q r _ => hΔ (x p) (y q) (y r)) hd
  dsimp only at hh ⊢
  rw [point_activity S z w x y u π h ε good label hm] at hh
  rw [average S z w x y u π h ε good label hm
      (fun a => scoreP ε (ActualSlots.frequency π a) π (fun p q => a.1 (p,q))
        (fun p => a.2 (x p)) (fun q => a.2 (y q)) (good a) (label a)),
    average S z w x y u π h ε good label hm
      (fun a => if PlaceScore.common ε (ActualSlots.frequency π a) then VP π (fun p q => a.1 (p,q)) else 0)] at hh
  change mass S*B.DP ≤ 2*Real.log 2+(1/20000000:ℝ)*(mass S*B.CP)+
    2*d*(mass S*(B.WC+B.HP)) at hh
  change B.DP ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    mass S*B.DP ≤ _ := hh
    _ = _ := by field_simp [hm.ne']; ring

omit [Fintype I] [Fintype H] in
theorem center (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hx : Function.Injective (z ∘ x)) (hS : ∀v r,z v-z r∈S)
    (hΔ : ∀v r t,(z v-z r-(z v-z t))*((z v-z r)⁻¹-(z v-z t)⁻¹)∈S)
    (hd : ∀p q,π.val (p,q) ≤ d*(right π).val q) :
    let B := make S z w x y u π h ε good label hm
    B.DQ ≤ B.CQ/20000000+2*Real.log 2/mass S+2*d*(B.WC+B.HQ) := by
  let B := make S z w x y u π h ε good label hm
  have hh := ActualColumnBudget.upper S z w x y u π π good label hε hε' hu hx
    (fun p q => hS (y q) (x p)) (fun q p r _ => hΔ (y q) (x p) (x r)) hd
  dsimp only at hh ⊢
  rw [center_activity S z w x y u π h ε good label hm] at hh
  rw [average S z w x y u π h ε good label hm
      (fun a => scoreQ ε (ActualSlots.frequency π a) π (fun p q => a.1 (p,q))
        (fun p => a.2 (x p)) (fun q => a.2 (y q)) (good a) (label a)),
    average S z w x y u π h ε good label hm
      (fun a => if PlaceScore.common ε (ActualSlots.frequency π a) then VQ π (fun p q => a.1 (p,q)) else 0)] at hh
  change mass S*B.DQ ≤ 2*Real.log 2+(1/20000000:ℝ)*(mass S*B.CQ)+
    2*d*(mass S*(B.WC+B.HQ)) at hh
  change B.DQ ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    mass S*B.DQ ≤ _ := hh
    _ = _ := by field_simp [hm.ne']; ring

theorem template (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y)) (hS : ∀v r,z v-z r∈S)
    (hΔ : ∀v r t,(z v-z r-(z v-z t))*((z v-z r)⁻¹-(z v-z t)⁻¹)∈S)
    (hd : ∀p q,π.val (p,q) ≤ d*(left π).val p) :
    let B := make S z w x y u π h ε good label hm
    Book.DT (I:=I) B ≤ Book.CT (I:=I) B/20000000+2*Real.log 2/mass S+
      2*(Fintype.card (I → H):ℝ)*d*(B.WC+B.HP) := by
  let B := make S z w x y u π h ε good label hm
  have hh := ActualTemplateBudget.upper S z w x y u π π (templateLaw (I:=I) π h)
    good label hε hε' hu hy
    (fun p q => hS (x p) (y q)) (fun p q r _ => hΔ (x p) (y q) (y r)) hd
  dsimp only at hh ⊢
  rw [point_activity S z w x y u π h ε good label hm] at hh
  rw [average S z w x y u π h ε good label hm
      (fun a => scoreT ε (ActualSlots.frequency π a) π (templateLaw (I:=I) π h) (fun p q => a.1 (p,q))
        (fun p => a.2 (x p)) (fun q => a.2 (y q)) (good a) (label a)),
    average S z w x y u π h ε good label hm
      (fun a => if PlaceScore.common ε (ActualSlots.frequency π a) then avg (templates π (templateLaw (I:=I) π h)) (fun θ => VP (slice π (templateLaw (I:=I) π h) θ) (fun p q => a.1 (p,q))) else 0)] at hh
  change mass S*(Book.DT (I:=I) B) ≤ 2*Real.log 2+(1/20000000:ℝ)*(mass S*(Book.CT (I:=I) B))+
    2*(Fintype.card (I → H):ℝ)*d*(mass S*(B.WC+B.HP)) at hh
  change Book.DT (I:=I) B ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    mass S*(Book.DT (I:=I) B) ≤ _ := hh
    _ = _ := by field_simp [hm.ne']; ring

omit [Fintype I] in
theorem prediction (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) (hz : Function.Injective (z ∘ x)) (hw : Function.Injective (w ∘ x))
    (hZ : ∀v r,z v-z r∈S) (hW : ∀v r,w v-w r∈S)
    {d : ℝ} (hd : 0≤d) (hd' : ∀p,(left π).val p≤d) :
    let B := make S z w x y u π h ε good label hm
    B.T ≤ 2*B.HP+2*Real.log 2/mass S+B.WB+B.WC*((Fintype.card H:ℝ)*d) := by
  let B := make S z w x y u π h ε good label hm
  let c : Data V (P×Q) → Prop := fun a => PlaceScore.common ε (ActualSlots.frequency π a)
  let r : Data V (P×Q) → Bool := fun a => LevelScores.minority (ActualSlots.frequency π a)
  have hh := ActualPredictionBudget.upper S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2)
    u (left π) h x hz hw (fun p q => hZ (x p) (x q)) (fun p q => hW (x p) (x q))
    c good r label hd hd'
  dsimp only at hh ⊢
  rw [average S z w x y u π h ε good label hm
    (fun a => if c a then avg (left π) (fun p => FiniteMarginalScore.tau
      (push (cond (left π) h (h p)) (fun p => a.2 (x p)))) else 0),
    average S z w x y u π h ε good label hm (fun a => ind (¬c a ∧ ¬good a)),
    average S z w x y u π h ε good label hm (fun a => ind (c a))] at hh
  have hi (p : P) := average S z w x y u π h ε good label hm
    (fun a => ind (¬c a ∧ good a ∧ exceptional (r a) (label a) (a.2 (x p))))
  simp_rw [hi] at hh
  rw [avg_smul,avg_comm] at hh
  have hhP : avg B.levels (fun a => avg (left π) (fun p =>
      ind (¬c a ∧ good a ∧ exceptional (r a) (label a) (a.2 (x p)))))=B.HP := by
    apply avg_congr
    intro a
    have hRa : B.R a ↔ ¬c a ∧ good a := by rfl
    simp only [hRa]
    by_cases hc : c a
    · simp [hc,ind,avg_const]
    · by_cases hg : good a
      · simp only [hc,hg,not_false_eq_true,true_and,ite_true]
        rfl
      · simp [hc,hg,ind,avg_const]
  change mass S*B.T ≤ 2*Real.log 2+2*(mass S*avg B.levels (fun a => avg (left π)
    (fun p => ind (¬c a ∧ good a ∧ exceptional (r a) (label a) (a.2 (x p))))))+
    mass S*B.WB+(mass S*B.WC)*((Fintype.card H:ℝ)*d) at hh
  rw [hhP] at hh
  change B.T ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    mass S*B.T ≤ _ := hh
    _ = _ := by field_simp [hm.ne']; ring
end
end PlanarUnitDistances.ActualBookUpper

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
lemma collision_nonneg (i : ℕ) : 0 ≤ collision s a i := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (dp_nonneg s i)
lemma root_nonneg (i : ℕ) : 0 ≤ rootInfo s a i := Real.rpow_nonneg
  (div_nonneg (s.good i).information_nonneg (Nat.cast_nonneg _)) _
lemma nonneg (i : ℕ) : 0 ≤ noise s a i := by
  unfold noise
  have h₁ := collision_nonneg s a i
  have h₂ := root_nonneg s a i
  have h₃ := vanishing_pos i
  positivity
lemma components (i : ℕ) :
    |(2*Real.log 2+4)/scale s i| ≤ noise s a i ∧ collision s a i ≤ noise s a i ∧
      vanishing i ≤ noise s a i ∧ rootInfo s a i ≤ noise s a i := by
  have h₀ := abs_nonneg ((2*Real.log 2+4)/scale s i)
  have h₁ := collision_nonneg s a i
  have h₂ := (vanishing_pos i).le
  have h₃ := root_nonneg s a i
  unfold noise
  constructor; linarith
  constructor; linarith
  constructor <;> linarith
lemma dp_le_collision (i : ℕ) : dp s i ≤ collision s a i := by
  have hc : (1:ℝ) ≤ capacity a := by exact_mod_cast capacity_pos a
  have hh := one_le_pow₀ (n:=length s a i) hc
  exact (one_mul (dp s i)).symm.le.trans (mul_le_mul_of_nonneg_right hh (dp_nonneg s i))
lemma row (i : ℕ) (p : s.P i) (q : s.Q i) :
    (graph s i).val (p,q) ≤ dp s i*(left (graph s i)).val p := by
  rw [←row_weight]
  have hr := row_bound s i p q
  rw [one_div,←Real.rpow_neg (tpos s i).le] at hr
  have hh := mul_le_mul_of_nonneg_left hr ((left (graph s i)).nonneg p)
  simpa only [dp,neg_div,mul_comm] using hh
lemma column (i : ℕ) (p : s.P i) (q : s.Q i) :
    (graph s i).val (p,q) ≤ vanishing i*(right (graph s i)).val q := by
  have hp := (s.good i).center_degree_pos q
  have he := (s.good i).positive
  have hb := (le_div_iff₀ he).mp ((s.good i).atomQ q q.property)
  have hd : (i:ℝ)+1 ≤ CircleIncidence.degree (s.P i) q :=
    (s.good i).degreeQ.trans (by simpa only [div_mul_eq_mul_div] using hb)
  have hv : (col (graph s i) q).val p ≤ vanishing i := by
    rw [graph,GeometricLaw.graph,UniformGraphLaw.col_eq _ _ (by rw [GeometricLaw.degree_eq]; exact hp),GeometricLaw.degree_eq]
    apply le_trans (div_le_div_of_nonneg_right (b:=(1:ℝ)) ?_ hp.le)
    · exact one_div_le_one_div_of_le (by positivity) hd
    · unfold IncidenceEntropy.indicator
      split_ifs <;> norm_num
  rw [←col_weight]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hv ((right (graph s i)).nonneg q)
end
end PlanarUnitDistances.IncidenceNoise

namespace PlanarUnitDistances.IncidenceEstimates
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
variable (R : Realization s a i)

local instance instFintypeProdSubtypePlaneMemFinsetPQ_radc016_1 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
lemma template_collision : (Fintype.card (Fin a.k → FiniteInformation.History
      (Fin a.m×Fin a.m) R.depth):ℝ)*dp s i ≤ collision s a i := by
  have hh : Fintype.card (Fin a.k → FiniteInformation.History (Fin a.m×Fin a.m) R.depth) ≤
      capacity a^(length s a i) := by
    simp only [Fintype.card_fun,FiniteInformation.history_card,Fintype.card_prod,Fintype.card_fin]
    rw [←pow_two,←pow_mul,←pow_mul]
    unfold capacity
    rw [←pow_mul]
    apply Nat.pow_le_pow_right a.m_pos
    nlinarith [R.depth_lt]
  unfold collision
  apply mul_le_mul_of_nonneg_right _ (dp_nonneg s i)
  exact_mod_cast hh
lemma history_collision : (Fintype.card (FiniteInformation.History
      (Fin a.m×Fin a.m) R.depth):ℝ)*dp s i ≤ collision s a i := by
  have hc : Fintype.card (FiniteInformation.History (Fin a.m×Fin a.m) R.depth) ≤
      Fintype.card (Fin a.k → FiniteInformation.History (Fin a.m×Fin a.m) R.depth) := by
    apply Fintype.card_le_of_injective (fun x (_ : Fin a.k) => x)
    intro x y h
    exact congrFun h ⟨0,a.k_pos⟩
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (dp_nonneg s i)).trans (template_collision R)

attribute [local instance] OAI.PlanarUnitDistances.IncidenceEstimates.instFintypeSumSubtypePlaneMemFinsetPQ
attribute [local instance] OAI.PlanarUnitDistances.IncidenceEstimates.instFintypeForallSumSubtypePlaneMemFinsetPQBool
local instance : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
theorem basic {C L : ℝ} (hC : 0<C) (hv : R.Valid C L) (hscale : 0<scale s i) :
    let B := R.book
    let r := noise s a i
    B.M ≤ r*B.S ∧ B.WC ≤ (1/a.epsilon)*B.S ∧ B.WB ≤ (r/a.epsilon)*B.S ∧
    B.HP+B.HQ ≤ BookEnvelope.height C r*B.S ∧
    B.J ≤ BookEnvelope.j a C (27/50) (1/25) (s.ξ i) r*B.S ∧
    B.EP ≤ BookEnvelope.pred a r*B.S := by
  let B := R.book
  let r := noise s a i
  obtain ⟨hf,hS,hM,hcard,hst,hrare,hWC,hWB,hH,hJ,hW,hEP⟩ := hv
  obtain ⟨hSn,hMn,hPn,hQn,hCPn,hCQn,hJn,hWCn,hWBn⟩ := B.nonneg
  have he := a.epsilon_pos
  have hr := nonneg s a i
  have hn := components s a i
  have hd := (dp_le_collision s a i).trans hn.2.1
  have hc : 2*Real.log 2+4 ≤ r*scale s i :=
    (div_le_iff₀ hscale).mp ((le_abs_self _).trans hn.1)
  have hM' : B.M ≤ r*B.S := by
    as_aux_lemma =>
      apply (mul_le_mul_iff_right₀ R.mass_pos).mp
      calc
        mass (model s i).support*B.M ≤ 2*Real.log 2+4 := hM
        _ ≤ r*scale s i := hc
        _ = mass (model s i).support*(r*B.S) := by rw [←hS]; ring
  have hWC' : B.WC ≤ (1/a.epsilon)*B.S := by simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using (show B.WC≤B.S/a.epsilon from hWC)
  have hWB' : B.WB ≤ (r/a.epsilon)*B.S := by
    as_aux_lemma =>
      calc
        _ ≤ B.M/a.epsilon := hWB
        _ ≤ (r*B.S)/a.epsilon := div_le_div_of_nonneg_right hM' a.epsilon_pos.le
        _ = _ := by ring
  have hH' : B.HP+B.HQ ≤ BookEnvelope.height C r*B.S := by
    as_aux_lemma =>
      calc
        _ ≤ C*(B.S+B.M) := hH
        _ ≤ C*(B.S+r*B.S) := by gcongr
        _ = _ := by unfold BookEnvelope.height; ring
  have hj0 : 0 ≤ BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i) := by
    unfold BudgetParameters.joint
    have hx := (s.good i).error_nonneg
    positivity
  have hJ' : B.J ≤ BookEnvelope.j a C (27/50) (1/25) (s.ξ i) r*B.S := by
    as_aux_lemma =>
      calc
        _ ≤ BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i)/2*(B.HP+B.HQ) := hJ
        _ ≤ BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i)/2*(BookEnvelope.height C r*B.S) := by gcongr
        _ = _ := by unfold BookEnvelope.j; ring
  have hEP' : B.EP ≤ BookEnvelope.pred a r*B.S := by
    as_aux_lemma =>
      calc
        _ ≤ B.M+B.WC*(4/(a.m:ℝ)+18*rootInfo s a i) := hEP
        _ ≤ r*B.S+((1/a.epsilon)*B.S)*(4/(a.m:ℝ)+18*r) := by
          gcongr
          · have hroot := root_nonneg s a i; positivity
          · exact hn.2.2.2
        _ = _ := by unfold BookEnvelope.pred; ring
  exact ⟨hM',hWC',hWB',hH',hJ',hEP'⟩

lemma raw_point : R.book.DP ≤ R.book.CP/20000000+2*Real.log 2/mass (model s i).support+2*dp s i*(R.book.WC+R.book.HP) := by
  have hu := fun p q h => (model s i).unit_identity p q (support s i p q h)
  have h := ActualBookUpper.point (model s i).support (model s i).z (model s i).w Sum.inl Sum.inr R.shifts
    (graph s i) R.history a.epsilon_pos a.epsilon_lt R.good R.label R.mass_pos
    hu (model s i).center_injective (model s i).sub_mem (model s i).difference_mem (IncidenceNoise.row s i)
  exact h

lemma raw_center : R.book.DQ ≤ R.book.CQ/20000000+2*Real.log 2/mass (model s i).support+2*vanishing i*(R.book.WC+R.book.HQ) := by
  have hu := fun p q h => (model s i).unit_identity p q (support s i p q h)
  have h := ActualBookUpper.center (model s i).support (model s i).z (model s i).w Sum.inl Sum.inr R.shifts
    (graph s i) R.history a.epsilon_pos a.epsilon_lt R.good R.label R.mass_pos
    hu (model s i).point_injective (model s i).sub_mem (model s i).difference_mem (IncidenceNoise.column s i)
  exact h

lemma raw_template : Book.DT (I:=Fin a.k) R.book ≤ Book.CT (I:=Fin a.k) R.book/20000000+2*Real.log 2/mass (model s i).support+
    2*(Fintype.card (Fin a.k → FiniteInformation.History (Fin a.m×Fin a.m) R.depth):ℝ)*dp s i*(R.book.WC+R.book.HP) := by
  have hu := fun p q h => (model s i).unit_identity p q (support s i p q h)
  have h := ActualBookUpper.template (I:=Fin a.k) (model s i).support (model s i).z (model s i).w Sum.inl Sum.inr R.shifts
    (graph s i) R.history a.epsilon_pos a.epsilon_lt R.good R.label R.mass_pos
    hu (model s i).center_injective (model s i).sub_mem (model s i).difference_mem (IncidenceNoise.row s i)
  simpa only [Fintype.card_fun,Realization.book,Realization.input,ActualProfiles.Input.book] using h

lemma raw_prediction : R.book.T ≤ 2*R.book.HP+2*Real.log 2/mass (model s i).support+R.book.WB+
    R.book.WC*((Fintype.card (FiniteInformation.History (Fin a.m×Fin a.m) R.depth):ℝ)*dp s i) := by
  have h := ActualBookUpper.prediction (model s i).support (model s i).z (model s i).w Sum.inl Sum.inr R.shifts
    (graph s i) R.history a.epsilon R.good R.label R.mass_pos (model s i).point_injective (model s i).wpoint_injective
    (model s i).sub_mem (model s i).wsub_mem (dp_nonneg s i) (point_bound s i)
  exact h

lemma star_upper {D A c d W H r S u v : ℝ}
    (hraw : D≤A/20000000+c+2*d*(W+H)) (hc : c≤r*S) (hd : d≤r) (hr : 0≤r)
    (hW0 : 0≤W) (hH0 : 0≤H) (hW : W≤u*S) (hH : H≤v*S) :
    D≤A/20000000+(r+2*r*(u+v))*S := by
  calc
    _ ≤ _ := hraw
    _ ≤ A/20000000+r*S+2*r*(u*S+v*S) := by gcongr
    _ = _ := by ring
lemma prediction_upper {D H c WB WC d r S ε : ℝ}
    (hraw : D≤2*H+c+WB+WC*d) (hc : c≤r*S) (hB : WB≤(r/ε)*S)
    (hW : WC≤(1/ε)*S) (hW0 : 0≤WC) (hd : d≤r) (hr : 0≤r) :
    D≤2*H+(r+r/ε+r/ε)*S := by
  calc
    _ ≤ _ := hraw
    _ ≤ 2*H+r*S+(r/ε)*S+WC*r := by gcongr
    _ ≤ 2*H+r*S+(r/ε)*S+((1/ε)*S)*r := by gcongr
    _ = _ := by ring

theorem upper_oai {C L : ℝ} (hC : 0<C) (hv : R.Valid C L) (hscale : 0<scale s i) :
    let B := R.book
    let r := noise s a i
    B.M ≤ r*B.S ∧ B.WC ≤ (1/a.epsilon)*B.S ∧ B.WB ≤ (r/a.epsilon)*B.S ∧
    B.HP+B.HQ ≤ BookEnvelope.height C r*B.S ∧
    B.J ≤ BookEnvelope.j a C (27/50) (1/25) (s.ξ i) r*B.S ∧
    B.EP ≤ BookEnvelope.pred a r*B.S ∧
    B.DP ≤ B.CP/20000000+BookEnvelope.star a C r*B.S ∧
    B.DQ ≤ B.CQ/20000000+BookEnvelope.star a C r*B.S ∧
    Book.DT (I:=Fin a.k) B ≤ Book.CT (I:=Fin a.k) B/20000000+BookEnvelope.star a C r*B.S ∧
    B.T ≤ 2*B.HP+BookEnvelope.prediction a r*B.S := by
  let B := R.book
  let r := noise s a i
  have hbasic := basic R hC hv hscale
  obtain ⟨hf,hS,hM,hcard,hst,hrare,hWC,hWB,hH,hJ,hW,hEP⟩ := hv
  obtain ⟨hSn,hMn,hPn,hQn,hCPn,hCQn,hJn,hWCn,hWBn⟩ := B.nonneg
  have he := a.epsilon_pos
  have hr := nonneg s a i
  have hn := components s a i
  have hd := (dp_le_collision s a i).trans hn.2.1
  have hc : 2*Real.log 2+4 ≤ r*scale s i :=
    (div_le_iff₀ hscale).mp ((le_abs_self _).trans hn.1)
  obtain ⟨hM',hWC',hWB',hH',hJ',hEP'⟩ := hbasic
  have hconst : 2*Real.log 2/mass (model s i).support ≤ r*B.S := by
    as_aux_lemma =>
      apply (div_le_iff₀ R.mass_pos).mpr
      rw [←hS] at hc
      nlinarith
  have hP : B.HP ≤ BookEnvelope.height C r*B.S := by linarith
  have hQ : B.HQ ≤ BookEnvelope.height C r*B.S := by linarith
  have hp := star_upper (raw_point R) hconst hd hr hWCn hPn hWC' hP
  have hq := star_upper (raw_center R) hconst hn.2.2.1 hr hWCn hQn hWC' hQ
  have ht0 := raw_template R
  rw [mul_assoc 2 _ (dp s i)] at ht0
  have ht := star_upper ht0 hconst ((template_collision R).trans hn.2.1) hr hWCn hPn hWC' hP
  have hpr := prediction_upper (raw_prediction R) hconst hWB' hWC' hWCn
    ((history_collision R).trans hn.2.1) hr
  exact ⟨hM',hWC',hWB',hH',hJ',hEP',hp,hq,ht,hpr⟩
end
end PlanarUnitDistances.IncidenceEstimates

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.IncidenceEstimates.upper_oai := @OAI.PlanarUnitDistances.IncidenceEstimates.upper_oai
