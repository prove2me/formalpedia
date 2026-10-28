-- Prove2me | solution 1 for OAI.SharpLogRamsey.GeometricCover.uniform_four
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:33:15.642605+00:00
-- url     : https://prove2.me/submissions/c7616f70-4b9f-4e79-99bc-c4fe176c67b8

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_PlanarLearning_full_source_cover_uniform
import Theorems.Thm_OAI_SharpLogRamsey_SpatialPublic_actual_cover

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_LargeCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpLogRamsey.MomentBudgetBridge

lemma anchorBudget_nonneg (p : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ anchorBudget p P := by
  unfold anchorBudget
  positivity

end SharpLogRamsey.MomentBudgetBridge
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incident_mk_iff (v : V) (hv : v ≠ 0) (f : Module.Dual K V) (hf : f ≠ 0) :
    SharpLogRamsey.Incidence.Incident (Projectivization.mk K v hv) (Projectivization.mk K f hf) ↔ f v = 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep K f hf
  unfold SharpLogRamsey.Incidence.Incident
  rw [← ha,← hb]
  simp [Units.smul_def]

lemma collision_center_on_line (z : Projectivization K V)
    (p q : {p : Projectivization K V // p ≠ z})
    (hpq : p.val ≠ q.val) (h : project z p = project z q) :
    z.submodule ≤ p.val.submodule ⊔ q.val.submodule := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hker : p.val.rep-a • q.val.rep ∈ LinearMap.ker z.submodule.mkQ := by
    change z.submodule.mkQ (p.val.rep-a • q.val.rep) = 0
    rw [map_sub,map_smul,ha,sub_self]
  rw [Submodule.ker_mkQ] at hker
  have hne : p.val.rep-a • q.val.rep ≠ 0 := by
    intro he
    apply hpq
    rw [← p.val.mk_rep,← q.val.mk_rep,Projectivization.mk_eq_mk_iff']
    exact ⟨a,(sub_eq_zero.mp he).symm⟩
  let r := Projectivization.mk K (p.val.rep-a • q.val.rep) hne
  have hr : r = z := by
    apply Projectivization.submodule_injective
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
      exact hker
    · simp only [Projectivization.finrank_submodule]
  have hline : r.submodule ≤ p.val.submodule ⊔ q.val.submodule := by
    rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    apply Submodule.sub_mem
    · apply (le_sup_left : p.val.submodule ≤ p.val.submodule ⊔ q.val.submodule)
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    · apply Submodule.smul_mem
      apply (le_sup_right : q.val.submodule ≤ p.val.submodule ⊔ q.val.submodule)
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
  exact (congrArg Projectivization.submodule hr).symm.le.trans hline

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma joining_line_finrank (p q : Projectivization K V) (hpq : p ≠ q) :
    Module.finrank K ↥(p.submodule ⊔ q.submodule : Submodule K V) = 2 := by
  have h := finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr hpq)
  rw [Matrix.range_cons_cons_empty] at h
  rw [Submodule.span_insert] at h
  rw [Projectivization.submodule_eq,Projectivization.submodule_eq]
  exact h

lemma joining_line_card [Finite K] (p q : Projectivization K V) (hpq : p ≠ q) :
    Nat.card {z : Projectivization K V // z.submodule ≤ p.submodule ⊔ q.submodule} =
      Nat.card K+1 := by
  rw [← Nat.card_congr (_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv (p.submodule ⊔ q.submodule))]
  exact Projectivization.card_of_finrank_two K _ (joining_line_finrank p q hpq)

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.Projection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma fiber_on_line (z p q : Projectivization K V) (hp : p ≠ z) (hq : q ≠ z)
    (he : project z ⟨p,hp⟩ = project z ⟨q,hq⟩) :
    q.submodule ≤ z.submodule ⊔ p.submodule := by
  by_cases hpq : p=q
  · subst q
    exact le_sup_right
  have hz := collision_center_on_line z ⟨p,hp⟩ ⟨q,hq⟩ hpq he
  have hsub : z.submodule ⊔ p.submodule ≤ p.submodule ⊔ q.submodule :=
    sup_le hz le_sup_left
  have hEq : z.submodule ⊔ p.submodule = p.submodule ⊔ q.submodule := by
    apply Submodule.eq_of_le_of_finrank_eq hsub
    rw [joining_line_finrank z p hp.symm,joining_line_finrank p q hpq]
  rw [hEq]
  exact le_sup_right

variable [Finite K] [Fintype (Projectivization K V)]

lemma project_fiber_card (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (b : Projectivization K (V ⧸ z.submodule)) :
    ((A.subtype (· ≠ z)).filter (fun p => project z p=b)).card ≤ Nat.card K := by
  let F := (A.subtype (· ≠ z)).filter (fun p => project z p=b)
  by_cases hf : F.Nonempty
  · obtain ⟨p,hp⟩ := hf
    let L : Finset (Projectivization K V) :=
      univ.filter (fun q => q.submodule ≤ z.submodule ⊔ p.val.submodule)
    have hL : L.card = Nat.card K+1 := by
      have h := joining_line_card z p.val p.property.symm
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
      exact h
    have hz : z ∈ L := mem_filter.mpr ⟨mem_univ _,le_sup_left⟩
    have hb : F.card ≤ (L.erase z).card := by
      apply card_le_card_of_injOn Subtype.val
      · intro q hq
        apply mem_erase.mpr
        refine ⟨q.property,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
        exact fiber_on_line z p.val q.val p.property q.property
          ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
      · intro x hx y hy he
        exact Subtype.ext he
    rw [card_erase_of_mem hz,hL] at hb
    simpa using hb
  · have : F=∅ := not_nonempty_iff_eq_empty.mp hf
    change F.card ≤ _
    simp [this]

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace SharpLogRamsey.ScaleSelection
open Filter Real
open scoped Topology
open SharpLogRamsey.MomentBudgetBridge

theorem eventually_polynomial_le_exp_rpow (C a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ Real.exp (c*x^b) := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound (show 0 < (1/(|C|+1) : ℝ) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    C*x^a ≤ (|C|+1)*x^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx0.le _)
    _ ≤ (|C|+1)*((1/(|C|+1))*Real.exp (c*x^b)) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by field_simp

theorem eventually_polynomial_exp_neg_rpow_lt (C a b c ε : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a*Real.exp (-c*x^b) < ε := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound
    (show 0 < ε/(2*(|C|+1)) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    _ ≤ (|C|+1)*x^a*Real.exp (-c*x^b) := by
      gcongr
    _ ≤ (|C|+1)*(ε/(2*(|C|+1))*Real.exp (c*x^b))*Real.exp (-c*x^b) := by
      gcongr
    _ = ε/2 := by
      rw [mul_assoc (|C|+1), mul_assoc, ← Real.exp_add,
        show c*x^b+-c*x^b=0 by ring, Real.exp_zero]
      field_simp
    _ < ε := by linarith

theorem certificate_le_majorant (x P : ℝ) (p D : ℕ) (hx : 1 ≤ x)
    (hP : 0 ≤ P) (hP' : P ≤ x^2) (hp : (p : ℝ) ≤ x^2) (hD : (D : ℝ) ≤ x^2) :
    certificateOverhead p D P ≤ majorant x := by
  have hA : anchorBudget p P ≤ 202*x^2 := by unfold anchorBudget; linarith
  have hA0 : 0 ≤ anchorBudget p P := anchorBudget_nonneg p hP
  unfold certificateOverhead majorant
  gcongr

theorem majorant_le (x : ℝ) (hx : 1 ≤ x) :
    majorant x ≤ (1+4+808+40804+5*2^200 : ℝ)*x^410 := by
  have hx0 : 0 ≤ x := by linarith
  have h0 : (1 : ℝ) ≤ x^410 := one_le_pow₀ hx
  have h4 : x^4 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have h8 : x^8 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have h12 : x^12 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have hD : x^2+4 ≤ 5*x^2 := by nlinarith [sq_nonneg (x-1)]
  have hm : (x^2)^4*(x^2+4)*(2*x^2)^200 ≤ 5*2^200*x^410 := by
    calc
      _ ≤ (x^2)^4*(5*x^2)*(2*x^2)^200 := by gcongr
      _ = _ := by ring
  have he : majorant x = 1+4*x^4+808*x^8+40804*x^12+
      (x^2)^4*(x^2+4)*(2*x^2)^200 := by unfold majorant; ring
  rw [he]
  nlinarith only [h0, h4, h8, h12, hm]

theorem eventually_certificate_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p D : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → (D : ℝ) ≤ x^2 → x^b ≤ P → P ≤ x^2 →
    certificateOverhead p D P ≤ Real.exp (2*P/25) := by
  have hh := eventually_polynomial_le_exp_rpow
    (1+4+808+40804+5*2^200) 410 b (2/25) hb (by norm_num)
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1 p D P hp hD hP hP'
  have hx0 : 0 ≤ x := by linarith
  calc
    _ ≤ majorant x := certificate_le_majorant x P p D hx1
      ((Real.rpow_nonneg hx0 _).trans hP) hP' hp hD
    _ ≤ (1+4+808+40804+5*2^200 : ℝ)*x^410 := majorant_le x hx1
    _ ≤ Real.exp ((2/25)*x^b) := by simpa only [Real.rpow_ofNat] using hx
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_shift_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p D : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → (D : ℝ) ≤ x^2 → x^b ≤ P →
    shiftOverhead p D ≤ Real.exp (2*P/25) := by
  have hh := eventually_polynomial_le_exp_rpow (4+200^200) 402 b (2/25) hb (by norm_num)
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1 p D P hp hD hP
  have hx0 : 0 ≤ x := by linarith
  have hm : shiftOverhead p D ≤ (4+200^200 : ℝ)*x^402 := by
    have h0 : (1 : ℝ) ≤ x^402 := one_le_pow₀ hx1
    have hh : (D : ℝ)*(200*(p : ℝ))^200 ≤ 200^200*x^402 := by
      calc
        _ ≤ x^2*(200*x^2)^200 := mul_le_mul hD
          (pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left hp (by norm_num)) 200)
          (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg p)) 200) (sq_nonneg x)
        _ = _ := by ring
    unfold shiftOverhead
    nlinarith only [h0, hh]
  calc
    _ ≤ (4+200^200 : ℝ)*x^402 := hm
    _ ≤ Real.exp ((2/25)*x^b) := by simpa only [Real.rpow_ofNat] using hx
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_position_budgets (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → x^b ≤ P →
    (p : ℝ)^2 ≤ Real.exp (P/10) ∧ 2*(p : ℝ)+3 ≤ Real.exp (P/10) := by
  have hh := eventually_polynomial_le_exp_rpow 1 4 b (1/10) hb (by norm_num)
  have hh' := eventually_polynomial_le_exp_rpow 5 2 b (1/10) hb (by norm_num)
  filter_upwards [hh, hh', eventually_ge_atTop (1 : ℝ)] with x hx hx' hx1 p P hp hP
  have hx0 : 0 ≤ x := by linarith
  have he : Real.exp ((1/10)*x^b) ≤ Real.exp (P/10) := Real.exp_le_exp.mpr (by linarith)
  constructor
  · calc
      _ ≤ (x^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hp _
      _ = x^4 := by ring
      _ ≤ Real.exp ((1/10)*x^b) := by simpa only [one_mul, Real.rpow_ofNat] using hx
      _ ≤ _ := he
  · have h1 : 1 ≤ x^2 := one_le_pow₀ hx1
    calc
      _ ≤ 5*x^2 := by linarith
      _ ≤ Real.exp ((1/10)*x^b) := by simpa only [Real.rpow_ofNat] using hx'
      _ ≤ _ := he

lemma nineteen_twentieth_pow_le (n : ℕ) :
    (19/20 : ℝ)^n ≤ Real.exp (-(n : ℝ)/20) := by
  have hb : (19/20 : ℝ) ≤ Real.exp (-(1/20 : ℝ)) := by
    linarith only [Real.add_one_le_exp (-(1/20 : ℝ))]
  calc
    _ ≤ (Real.exp (-(1/20 : ℝ)))^n := pow_le_pow_left₀ (by norm_num) hb _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem eventually_root_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p R : ℕ), (p : ℝ) ≤ x^2 → x^b ≤ R →
    ∃ h : ℕ, 0 < h ∧ 400 ≤ R ∧ h ≤ (R/2)/400 ∧
      (p : ℝ)*h*(19/20 : ℝ)^(h-1) < 1/2 := by
  have hh := eventually_polynomial_exp_neg_rpow_lt (Real.exp (1/10)) (2+b) b
    (1/16000) (1/2) hb (by norm_num) (by norm_num)
  filter_upwards [hh, (tendsto_rpow_atTop hb).eventually_ge_atTop 1600,
    eventually_ge_atTop (1 : ℝ)] with x hx hxb hx1 p R hp hR
  have hx0 : 0 < x := by linarith
  let h : ℕ := ⌊x^b/800⌋₊
  have hh1 : 1 ≤ h := by
    apply Nat.le_floor
    norm_num
    linarith
  have hhle : (h : ℝ) ≤ x^b/800 := Nat.floor_le (by positivity)
  have hhgt : x^b/800 < (h : ℝ)+1 := Nat.lt_floor_add_one _
  have hhr : 800*h ≤ R := by
    have hcast : (800 : ℝ)*(h : ℝ) ≤ R := by linarith
    exact_mod_cast hcast
  have hnat : ((h-1 : ℕ) : ℝ) = (h : ℝ)-1 := by rw [Nat.cast_sub hh1]; norm_num
  have hp' : (p : ℝ)*h ≤ x^(2+b) := by
    calc
      _ ≤ x^2*x^b := by gcongr; linarith only [hhle, Real.rpow_nonneg hx0.le b]
      _ = _ := by rw [Real.rpow_add hx0]; simp only [Real.rpow_ofNat]
  have he : (19/20 : ℝ)^(h-1) ≤ Real.exp ((1/10)-(1/16000)*x^b) := by
    apply (nineteen_twentieth_pow_le (h-1)).trans
    apply Real.exp_le_exp.mpr
    rw [hnat]
    linarith
  refine ⟨h, by omega, by omega, by omega, ?_⟩
  calc
    _ ≤ x^(2+b)*Real.exp ((1/10)-(1/16000)*x^b) :=
      mul_le_mul hp' he (by positivity) (by positivity)
    _ = Real.exp (1/10)*x^(2+b)*Real.exp (-(1/16000)*x^b) := by
      rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      ring
    _ < _ := hx

end SharpLogRamsey.ScaleSelection
end

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection SharpLogRamsey.MomentBudgetBridge

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

lemma exponent_gap {η : ℝ} (hη : 0 < η) : 1-η/2+9*beta η < 1 := by
  unfold beta
  linarith

lemma scale_bounds {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0 < η)
    (h : Admissible σ η D R) :
    σ^(9*beta η) ≤ scaleL σ η D ∧
    σ^(10*beta η) ≤ scaleP σ η D R ∧
    scaleP σ η D R ≤ 4*σ^(1-η/2+9*beta η) := by
  have hσ0 : 0 < σ := by linarith
  have hb : 0 < beta η := beta_pos hη
  have hpow : 1 ≤ σ^beta η := Real.one_le_rpow hσ hb.le
  have hD0 : 0 ≤ D := (Real.rpow_nonneg hσ0.le _).trans h.D_lower
  have hL : σ^(9*beta η) ≤ scaleL σ η D := by
    calc
      _ = σ^beta η*σ^(8*beta η) := by rw [← Real.rpow_add hσ0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.D_lower (Real.rpow_nonneg hσ0.le _)
  refine ⟨hL, ?_, ?_⟩
  · calc
      _ = σ^(9*beta η)*σ^beta η := by rw [← Real.rpow_add hσ0]; congr 1; ring
      _ ≤ scaleL σ η D*(R : ℝ) := mul_le_mul hL h.R_lower
        (Real.rpow_nonneg hσ0.le _) (by unfold scaleL; positivity)
      _ = _ := rfl
  · have hR : (R : ℝ) ≤ 4*σ^beta η := by linarith [h.R_upper]
    calc
      _ ≤ (σ^(1-η/2)*σ^(8*beta η))*(4*σ^beta η) := by
        unfold scaleP scaleL
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.D_upper
          (Real.rpow_nonneg hσ0.le _)) hR (Nat.cast_nonneg _) (by positivity)
      _ = 4*σ^(1-η/2+9*beta η) := by
        rw [mul_assoc, mul_left_comm (σ^(8*beta η)) 4, ← mul_assoc,
          mul_comm (σ^(1-η/2)) 4, mul_assoc, ← Real.rpow_add hσ0,
          ← Real.rpow_add hσ0]
        congr 2
        ring

lemma eventually_monomial_le_linear (C a ε : ℝ) (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-1))*x := by
      have hp : x^(a-1)*x = x^a := by
        calc
          _ = x^(a-1)*x^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
      rw [mul_assoc, hp]
    _ ≤ ε*x := mul_le_mul_of_nonneg_right hx.le hx0.le

theorem eventually_P_le_linear {η : ℝ} (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      scaleP σ η D R ≤ ε*σ := by
  filter_upwards [eventually_monomial_le_linear 4 (1-η/2+9*beta η) ε
    (exponent_gap hη) hε, eventually_ge_atTop (1 : ℝ)] with σ hσ hσ1 D R h
  exact (scale_bounds hσ1 hη h).2.2.trans hσ

theorem moment_order_le {σ P : ℝ} {p : ℕ} (hσ : 10002 ≤ σ) (hP : 1 ≤ P)
    (hp : (p : ℝ) ≤ 10000*σ/P+2) : (p : ℝ) ≤ σ^2 := by
  have hσ0 : 0 ≤ σ := by linarith
  have hdiv : 10000*σ/P ≤ 10000*σ := div_le_self (by positivity) hP
  nlinarith [sq_nonneg (σ-10002)]

theorem eventually_enumeration_budgets {η : ℝ} (hη : 0 < η) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R p m : ℕ), Admissible σ η D R →
    (p : ℝ) ≤ 10000*σ/scaleP σ η D R+2 → (m : ℝ) ≤ σ^2 →
    10000 ≤ scaleL σ η D ∧
    certificateOverhead p m (scaleP σ η D R) ≤ Real.exp (2*scaleP σ η D R/25) ∧
    shiftOverhead p m ≤ Real.exp (2*scaleP σ η D R/25) ∧
    (p : ℝ)^2 ≤ Real.exp (scaleP σ η D R/10) ∧
    2*(p : ℝ)+3 ≤ Real.exp (scaleP σ η D R/10) ∧
    ∃ h : ℕ, 0 < h ∧ 400 ≤ R ∧ h ≤ (R/2)/400 ∧
      (p : ℝ)*h*(19/20 : ℝ)^(h-1) < 1/2 := by
  have hb := beta_pos hη
  have h10 : 0 < 10*beta η := by positivity
  have h9 : 0 < 9*beta η := by positivity
  filter_upwards [eventually_certificate_budget (10*beta η) h10,
    eventually_shift_budget (10*beta η) h10,
    eventually_position_budgets (10*beta η) h10,
    eventually_root_budget (beta η) hb,
    (tendsto_rpow_atTop h9).eventually_ge_atTop 10000,
    eventually_P_le_linear hη 1 (by norm_num),
    eventually_ge_atTop (10002 : ℝ)] with σ hc hs hp hr hL hPu hσ D R p m had hp' hm
  have hσ1 : 1 ≤ σ := by linarith
  obtain ⟨hLb, hPb, _⟩ := scale_bounds hσ1 hη had
  have hP1 : 1 ≤ scaleP σ η D R := (Real.one_le_rpow hσ1 h10.le).trans hPb
  have hpm : (p : ℝ) ≤ σ^2 := moment_order_le hσ hP1 hp'
  have hP2 : scaleP σ η D R ≤ σ^2 := by
    have := hPu D R had
    nlinarith [sq_nonneg (σ-1)]
  obtain ⟨hp2, hps⟩ := hp p (scaleP σ η D R) hpm hPb
  exact ⟨hL.trans hLb, hc p m _ hpm hm hPb hP2,
    hs p m _ hpm hm hPb, hp2, hps, hr p R hpm had.R_lower⟩

end SharpLogRamsey.SourceScales
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScaleComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

lemma Kstar_eq (σ η D : ℝ) (hσ : 0<σ) :
    scaleKstar σ η D=scaleL σ η D*σ^(-2*beta η) := by
  unfold scaleKstar scaleL
  rw [mul_assoc,←Real.rpow_add hσ]
  congr 2
  ring

lemma R_bound {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0<η)
    (h : Admissible σ η D R) : (R:ℝ) ≤ 4*σ^beta η := by
  have hh := Real.one_le_rpow hσ (beta_pos hη).le
  linarith [h.R_upper]

lemma L_pos {σ η D : ℝ} {R : ℕ} (hσ : 0<σ) (h : Admissible σ η D R) :
    0 < scaleL σ η D := by
  have hD : 0<D := (Real.rpow_pos_of_pos hσ _).trans_le h.D_lower
  unfold scaleL
  positivity

lemma P_pos {σ η D : ℝ} {R : ℕ} (hσ : 0<σ) (h : Admissible σ η D R) :
    0 < scaleP σ η D R := by
  have hR : (0:ℝ)<R := (Real.rpow_pos_of_pos hσ _).trans_le h.R_lower
  exact mul_pos (L_pos hσ h) hR

theorem eventually_sparse_loss {η : ℝ} (hη : 0<η) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      ∀ b τ : ℝ, b ≤ C*scaleKstar σ η D → τ ≤ C*σ^(-100*beta η) →
      b+scaleP σ η D R*τ ≤ δ*scaleL σ η D := by
  have hb := beta_pos hη
  have h1 : Tendsto (fun σ : ℝ => C*σ^(-2*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<2*beta η by positivity)).const_mul C using 1 <;> simp [neg_mul]
  have h2 : Tendsto (fun σ : ℝ => 4*C*σ^(-99*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<99*beta η by positivity)).const_mul (4*C) using 1 <;> simp [neg_mul]
  have ht : Tendsto (fun σ : ℝ => C*σ^(-2*beta η)+4*C*σ^(-99*beta η)) atTop (𝓝 0) := by
    simpa using h1.add h2
  filter_upwards [ht.eventually (gt_mem_nhds hδ),eventually_ge_atTop (1:ℝ)] with σ he hσ D R had b τ hb' hτ
  have hσ0 : 0<σ := by linarith
  have hL := (L_pos hσ0 had).le
  have hP := (P_pos hσ0 had).le
  have hR := R_bound hσ hη had
  have hh : (R:ℝ)*(C*σ^(-100*beta η)) ≤ 4*C*σ^(-99*beta η) := by
    calc
      _  ≤  (4*σ^beta η)*(C*σ^(-100*beta η)) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
      _ = _ := by
        rw [show (4*σ^beta η)*(C*σ^(-100*beta η))=4*C*(σ^beta η*σ^(-100*beta η)) by ring,
          ←Real.rpow_add hσ0]
        congr 2
        ring
  have hb'' : b ≤ scaleL σ η D*(C*σ^(-2*beta η)) := by
    rw [Kstar_eq σ η D hσ0] at hb'
    nlinarith only [hb']
  have hτ' : scaleP σ η D R*τ ≤ scaleL σ η D*(4*C*σ^(-99*beta η)) := by
    calc
      _  ≤  scaleP σ η D R*(C*σ^(-100*beta η)) := mul_le_mul_of_nonneg_left hτ hP
      _ = scaleL σ η D*((R:ℝ)*(C*σ^(-100*beta η))) := mul_assoc _ _ _
      _  ≤  _ := mul_le_mul_of_nonneg_left hh hL
  calc
    _  ≤  scaleL σ η D*(C*σ^(-2*beta η)+4*C*σ^(-99*beta η)) := by linarith
    _  ≤  scaleL σ η D*δ := mul_le_mul_of_nonneg_left he.le hL
    _ = _ := mul_comm _ _

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourcePencilScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

lemma eventually_uniform_L {η : ℝ} (hη : 0<η) {Q : ℝ→Prop}
    (hQ : ∀ᶠ L : ℝ in atTop,Q L) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R → Q (scaleL σ η D) := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp hQ
  have ht := (tendsto_rpow_atTop (show 0<9*beta η by have := beta_pos hη; positivity)).eventually
    (eventually_ge_atTop a)
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with σ hσ hσ1 D R had
  exact ha _ (hσ.trans (scale_bounds hσ1 hη had).1)

lemma eventually_uniform_R {η : ℝ} (hη : 0<η) (a : ℝ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R → a≤(R:ℝ) := by
  have ht := (tendsto_rpow_atTop (beta_pos hη)).eventually (eventually_ge_atTop a)
  filter_upwards [ht] with σ hσ D R had
  exact hσ.trans had.R_lower

lemma two_pow_le_exp (R : ℕ) : (2:ℝ)^R≤Real.exp (R:ℝ) := by
  have ht : (2:ℝ)≤Real.exp 1 := by
    have hh := Real.add_one_le_exp (1:ℝ)
    norm_num at hh ⊢
    exact hh
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) ht R
  simpa only [←Real.exp_nat_mul,mul_one] using hh

theorem eventually_pencil_scalar_budgets {η : ℝ} (hη : 0<η) (C : ℝ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R N : ℕ),Admissible σ η D R → (N:ℝ)≤σ^2 →
      let L := scaleL σ η D
      let P := scaleP σ η D R
      C*2^R≤Real.exp (P/20) ∧
      (2*L^2)^R≤Real.exp (P/25) ∧
      C^2*Real.exp (L/50)+(N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/20) ∧
      2≤Real.exp (P/20) ∧
      400000*Real.exp (L/1000)≤Real.exp (P/100) := by
  have hconst : ∀ᶠ L : ℝ in atTop,C≤Real.exp (L/1000) ∧ C^2≤Real.exp (L/1000) := by
    have ht : Tendsto (fun L : ℝ => Real.exp (L/1000)) atTop atTop :=
      tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<1000))
    exact (ht.eventually (eventually_ge_atTop C)).and (ht.eventually (eventually_ge_atTop (C^2)))
  have hpoly : ∀ᶠ L : ℝ in atTop,2*L^2≤Real.exp (L/25) := by
    have hh := ScaleSelection.eventually_polynomial_le_exp_rpow 2 2 1 (1/25)
      (by norm_num) (by norm_num)
    simpa only [Real.rpow_one,Real.rpow_ofNat,div_eq_mul_inv,mul_comm,one_mul] using hh
  have hgrid := ScaleSelection.eventually_polynomial_le_exp_rpow 1 2 (9*beta η) (1/1000)
    (by have := beta_pos hη; positivity) (by norm_num)
  have hlarge : ∀ᶠ L : ℝ in atTop,1000000000≤L := eventually_ge_atTop _
  filter_upwards [eventually_uniform_L hη hconst,eventually_uniform_L hη hpoly,
    eventually_uniform_L hη hlarge,eventually_uniform_R hη 400,hgrid,
    eventually_ge_atTop (1:ℝ)] with σ hc hp hl hr hg hσ D R N had hN
  let L := scaleL σ η D
  let P := scaleP σ η D R
  have hL : 1000000000≤L := hl D R had
  have hR : (400:ℝ)≤R := hr D R had
  have hL0 : 0≤L := by linarith
  have hR1 : (1:ℝ)≤R := by linarith
  have hP : P=L*R := rfl
  have hPL : 400*L≤P := by rw [hP]; nlinarith
  have hPR : 1000000000*(R:ℝ)≤P := by rw [hP]; nlinarith
  have hP0 : 0≤P := by linarith
  have hcc := hc D R had
  change C≤Real.exp (L/1000) ∧ C^2≤Real.exp (L/1000) at hcc
  have hNN : (N:ℝ)≤Real.exp (L/1000) := by
    apply hN.trans
    calc
      σ^2≤Real.exp ((1/1000)*σ^(9*beta η)) := by simpa only [one_mul,Real.rpow_ofNat] using hg
      _ ≤ Real.exp (L/1000) := Real.exp_le_exp.mpr (by linarith [(scale_bounds hσ hη had).1])
  have ht := two_pow_le_exp R
  have h2 : (2:ℝ)≤Real.exp (P/40) := by
    have hh := Real.add_one_le_exp (P/40)
    linarith
  dsimp only
  change C*2^R≤Real.exp (P/20) ∧ (2*L^2)^R≤Real.exp (P/25) ∧
    C^2*Real.exp (L/50)+(N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/20) ∧
    2≤Real.exp (P/20) ∧ 400000*Real.exp (L/1000)≤Real.exp (P/100)
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      C*2^R≤Real.exp (L/1000)*Real.exp (R:ℝ) := mul_le_mul hcc.1 ht (by positivity) (Real.exp_pos _).le
      _ = Real.exp (L/1000+R) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (P/20) := Real.exp_le_exp.mpr (by linarith)
  · have hh := pow_le_pow_left₀ (show 0≤2*L^2 by positivity) (hp D R had) R
    apply hh.trans_eq
    rw [←Real.exp_nat_mul]
    congr 1
    rw [hP]
    ring
  · have hfirst : C^2*Real.exp (L/50)≤Real.exp (P/40) := by
      calc
        _ ≤ Real.exp (L/1000)*Real.exp (L/50) := mul_le_mul_of_nonneg_right hcc.2 (Real.exp_pos _).le
        _ = Real.exp (L/1000+L/50) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have hsecond : (N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/40) := by
      calc
        _ ≤ (Real.exp (L/1000)*Real.exp (R:ℝ))*Real.exp (P/50) := by gcongr
        _ = Real.exp (L/1000+R+P/50) := by rw [←Real.exp_add,←Real.exp_add]
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ 2*Real.exp (P/40) := by linarith
      _ ≤ Real.exp (P/40)*Real.exp (P/40) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (P/20) := by rw [←Real.exp_add]; congr 1; ring
  · exact h2.trans (Real.exp_le_exp.mpr (by linarith))
  · have hnum : (400000:ℝ)≤Real.exp (L/1000) := by
      have hh := Real.add_one_le_exp (L/1000)
      linarith
    calc
      _ ≤ Real.exp (L/1000)*Real.exp (L/1000) := mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le
      _ = Real.exp (L/500) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceTrainingScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_training_loss {η : ℝ} (hη : 0<η) (C δ : ℝ)
    (hC : 0≤C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∀ b τ : ℝ,b≤C*scaleKstar σ η D → τ≤C*σ^(-100*beta η) →
        b+2*scaleP σ η D R*τ≤δ*scaleL σ η D := by
  filter_upwards [eventually_sparse_loss hη (2*C) δ (by positivity) hδ,
    eventually_ge_atTop (1:ℝ)] with σ hh hσ D R had b τ hb hτ
  have hK : 0 ≤ scaleKstar σ η D := by
    rw [Kstar_eq _ _ _ (by linarith)]
    exact mul_nonneg (L_pos (by linarith) had).le (Real.rpow_nonneg (by linarith) _)
  have h1 : b≤(2*C)*scaleKstar σ η D := by nlinarith
  have h2 : 2*τ≤(2*C)*σ^(-100*beta η) := by linarith
  have hh' := hh D R had b (2*τ) h1 h2
  nlinarith only [hh']

theorem eventually_exceptional_training {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∀ b τ : ℝ,b≤C*scaleKstar σ η D → τ≤C*σ^(-100*beta η) →
        50000*Real.exp (-(95/100:ℝ)*scaleL σ η D)≤
          Real.exp (-b-2*scaleP σ η D R*τ)/800 := by
  have he : ∀ᶠ L : ℝ in atTop,(40000000:ℝ)≤Real.exp (L/2) := by
    filter_upwards [eventually_ge_atTop (80000000:ℝ)] with L hL
    have hh := Real.add_one_le_exp (L/2)
    linarith
  filter_upwards [eventually_training_loss hη C (1/100) hC (by norm_num),
    eventually_uniform_L hη he,eventually_ge_atTop (1:ℝ)] with σ hl he hσ D R had b τ hb hτ
  have hL := (L_pos (by linarith) had).le
  have hl' := hl D R had b τ hb hτ
  have he' := he D R had
  have hh : 40000000*Real.exp (-(95/100:ℝ)*scaleL σ η D)≤
      Real.exp (-b-2*scaleP σ η D R*τ) := by
    calc
      _ ≤ Real.exp (scaleL σ η D/2)*Real.exp (-(95/100:ℝ)*scaleL σ η D) :=
        mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
      _ = Real.exp (scaleL σ η D/2-(95/100:ℝ)*scaleL σ η D) := by
        rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_UniversalTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

omit [Fintype Ω] in
lemma rows_card_le (n : ℕ) (z : Table Ω n) : (rows n z).card≤n := by
  induction n with
  | zero => simp [rows]
  | succ n ih => exact (card_insert_le _ _).trans (Nat.add_le_add_right (ih _) 1)

omit [Fintype Ω] in
lemma first_none_iff (A : Ω→Prop) (n : ℕ) (z : Table Ω n) :
    first A n z=none ↔ ∀ x∈rows n z,¬A x := by
  induction n with
  | zero => simp [first,rows]
  | succ n ih =>
    by_cases h : A z.1
    · simp [first,rows,h]
    · simpa [first,rows,h] using ih z.2

lemma missed_probability (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (∑ z,tableWeight p n z*(if first A n z=none then 1 else 0))=(1-acceptProb p A)^n := by
  have hh (z : Table Ω n) :
      (if first A n z=none then (1:ℝ) else 0)=1-outcome A (fun _ => 1) n z := by
    unfold outcome
    cases first A n z <;> simp
  simp_rw [hh,mul_sub,mul_one]
  rw [sum_sub_distrib,tableWeight_total]
  change 1-integral p A (fun _ => 1) n=_
  rw [production_probability]
  ring

lemma missing_exp (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (1-acceptProb p A)^n≤exp (-(n:ℝ)*acceptProb p A) := by
  have hh : 1-acceptProb p A≤exp (-acceptProb p A) := by
    have := add_one_le_exp (-acceptProb p A)
    linarith
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr (acceptProb_le_one p A)) hh n
  rw [←exp_nat_mul] at hp
  simpa only [mul_neg,neg_mul] using hp

theorem exists_universal (p : Law Ω) (A : ι→Ω→Prop) (n : ℕ)
    (h : (∑ i,(1-acceptProb p (A i))^n)<1) :
    ∃ z : Table Ω n,∀ i,∃ x∈rows n z,A i x := by
  by_contra! hn
  have hl (z : Table Ω n) :
      (1:ℝ)≤∑ i,if first (A i) n z=none then 1 else 0 := by
    obtain ⟨i,hi⟩ := hn z
    have hm : first (A i) n z=none := (first_none_iff _ _ _).mpr hi
    have hh := single_le_sum (f := fun i => if first (A i) n z=none then (1:ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa [hm] using hh
  have hh : (1:ℝ)≤∑ z,tableWeight p n z*(∑ i,if first (A i) n z=none then 1 else 0) := by
    calc
      _ = ∑ z,tableWeight p n z := (tableWeight_total p n).symm
      _ ≤ _ := by
        apply sum_le_sum
        intro z _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hl z) (tableWeight_nonneg p n z)
  simp_rw [mul_sum] at hh
  rw [sum_comm] at hh
  simp_rw [missed_probability] at hh
  linarith

theorem exists_cover (p : Law Ω) (A : ι→Ω→Prop) (a H : ℝ)
    (ha : 0≤a) (hcard : (Fintype.card ι:ℝ)≤exp H) (hH : H+1≤exp a)
    (hp : ∀ i,exp (-a)≤acceptProb p (A i)) :
    ∃ r : Finset Ω,r.card≤⌈exp (2*a)⌉₊ ∧ (∀ i,∃ x∈r,A i x) ∧
      log ((⌈exp (2*a)⌉₊:ℝ)+1)≤2*a+log 3 := by
  let n := ⌈exp (2*a)⌉₊
  have hN : exp (2*a)≤(n:ℝ) := Nat.le_ceil _
  have hl : (∑ i,(1-acceptProb p (A i))^n)<1 := by
    calc
      _ ≤ (∑ _i : ι,exp (-(n:ℝ)*exp (-a))) := by
        apply sum_le_sum
        intro i _
        apply (missing_exp p (A i) n).trans
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg n : (0:ℝ)≤n)
        nlinarith only [hh]
      _ = (Fintype.card ι:ℝ)*exp (-(n:ℝ)*exp (-a)) := by simp
      _ ≤ exp H*exp (-(n:ℝ)*exp (-a)) := by gcongr
      _ = exp (H-(n:ℝ)*exp (-a)) := by rw [←exp_add]; congr 1; ring
      _ ≤ exp (-1) := by
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hN (exp_pos (-a)).le
        have he : exp (2*a)*exp (-a)=exp a := by rw [←exp_add]; congr 1; ring
        rw [he] at hh
        linarith
      _ < 1 := exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨z,hz⟩ := exists_universal p A n hl
  refine ⟨rows n z,rows_card_le n z,hz,?_⟩
  have hn : (n:ℝ)<exp (2*a)+1 := Nat.ceil_lt_add_one (exp_pos _).le
  have he : 1≤exp (2*a) := one_le_exp_iff.mpr (by linarith)
  have hnp : (0:ℝ)<(n:ℝ)+1 := by positivity
  calc
    _ ≤ log (3*exp (2*a)) := by apply log_le_log hnp; linarith
    _ = _ := by rw [log_mul (by norm_num) (exp_ne_zero _),log_exp]; ring

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_ValidationCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma coverInput_card (W : Finset (Projectivization K V))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ) (C b : ℝ) :
    (Fintype.card {z // CoverInput W U N t C b z}:ℝ) ≤
      exp (((Fintype.card (Projectivization K V):ℝ)+
        Fintype.card (Projectivization K (Module.Dual K V)))*log 2) := by
  have hc := Fintype.card_subtype_le (CoverInput W U N t C b)
  have hc' : (Fintype.card {z // CoverInput W U N t C b z}:ℝ) ≤
      (2:ℝ)^Fintype.card (Projectivization K V)*
      (2:ℝ)^Fintype.card (Projectivization K (Module.Dual K V)) := by
    simpa only [Fintype.card_prod,Fintype.card_finset,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using (show (Fintype.card {x // CoverInput W U N t C b x}:ℝ) ≤ Fintype.card (Finset (Projectivization K V) × Finset (Projectivization K (Module.Dual K V))) by exact_mod_cast hc)
  apply hc'.trans_eq
  rw [add_mul,exp_add,exp_nat_mul,exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]

lemma row_ratio_exp {x w b : ℝ} (_hx : 0<x) (hw : 0<w)
    (h : w ≤ exp b*x) (hrow : ℕ) : exp (-((hrow:ℝ)*b)) ≤ (x/w)^hrow := by
  have hh : exp (-b) ≤ x/w := by
    rw [le_div_iff₀ hw,exp_neg]
    apply (inv_mul_le_iff₀ (exp_pos b)).mpr
    nlinarith only [h]
  have hh' := pow_le_pow_left₀ (exp_pos (-b)).le hh hrow
  rwa [←exp_nat_mul, mul_neg] at hh'

theorem public_validation_cover {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : Finset (Projectivization K V)) (hW : W.Nonempty)
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (htu : t ≤ U.card)
    (C b : ℝ) (hC : 1 ≤ C) (hb : 0 ≤ b)
    (hprod : (N:ℝ)*t ≤ 2*(Nat.card K:ℝ)^(n+3)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card t
    let M := 1000*C*q^(n+3)/N
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let a := (h:ℝ)*b+log 2+log (H+1)
    ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
      (∀ E ∈ caps, E ⊆ U ∧ (E.card:ℝ) ≤ M) ∧
      (∀ z, CoverInput W U N t C b z →
        ∃ E ∈ caps, (99/100:ℝ)*t ≤ (z.2∩E).card) ∧
      log ((caps.card:ℝ)+1) ≤ 2*a+log 3 := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card t
  let M := 1000*C*q^(n+3)/N
  let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
  let a := (h:ℝ)*b+log 2+log (H+1)
  have hq : 0<q := by change 0<(Nat.card K:ℝ); exact_mod_cast Nat.card_pos (α:=K)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have htr : (0:ℝ)<t := by exact_mod_cast ht
  have hw : (0:ℝ)<W.card := by exact_mod_cast card_pos.mpr hW
  have hut : (t:ℝ) ≤ U.card := by exact_mod_cast htu
  have hh : 0<h := scheduleLength_pos hq htr hut
  have hM : 0<M := by
    dsimp [M]
    have : 0<C := by linarith
    positivity
  have hH : 0 ≤ H := by dsimp [H]; exact mul_nonneg (by positivity) (log_nonneg (by norm_num))
  have ha₀ : 0 ≤ (h:ℝ)*b+log 2 := by positivity
  have hHP : 0 < H+1 := by linarith
  have ha : 0 ≤ a := by dsimp [a]; exact add_nonneg ha₀ (log_nonneg (by linarith))
  have hea : H+1 ≤ exp a := by
    dsimp only [a]
    rw [exp_add,exp_log hHP]
    exact le_mul_of_one_le_left hHP.le (one_le_exp_iff.mpr ha₀)
  let ι := {z // CoverInput W U N t C b z}
  let A : ι → (Fin h → Projectivization K V) → Prop := fun i =>
    implementAccept i.1.1 (GoodCap SharpLogRamsey.Incidence.Incident q U i.1.2 M)
  have hprob : ∀ i, exp (-a) ≤ PublicTables.acceptProb (rowLaw W hW h) (A i) := by
    intro i
    obtain ⟨hx,hxw,hcap,hratio,htu',hct,hsp⟩ := i.2
    have hxr : (0:ℝ) < i.1.1.card := by exact_mod_cast card_pos.mpr hx
    have htt : i.1.2.Nonempty := card_pos.mp (by omega)
    have hsize := scheduleLength_size hq htr hut hNr hxr hC hcap hprod
      (pow_nonneg hq.le (n+3))
    have hsp' : (∑ y∈i.1.2,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass i.1.1 x) ≤
        (i.1.2.card:ℝ)/(10000*q) := by
      rw [uniform_incidence_sum]
      apply (div_le_iff₀ hxr).mpr
      apply hsp.trans_eq
      dsimp [q]
      ring
    have hg := projective_ideal_acceptance hdim i.1.1 hx U i.1.2 htt h hh M hM hsize hsp'
    change _ ≤ PublicTables.acceptProb (rowLaw W hW h)
      (implementAccept i.1.1 (GoodCap SharpLogRamsey.Incidence.Incident q U i.1.2 M))
    rw [proposal_acceptance _ _ hx hW hxw]
    have hr := row_ratio_exp hxr hw hratio h
    have hprod' := mul_le_mul hr hg (by norm_num : (0:ℝ) ≤ 9/10) (by positivity)
    apply le_trans _ hprod'
    have he : exp (-((h:ℝ)*b+log 2))= exp (-((h:ℝ)*b))/2 := by
      rw [neg_add,exp_add,exp_neg (log 2),exp_log (by norm_num : (0:ℝ)<2)]
      ring
    calc
      exp (-a) ≤ exp (-((h:ℝ)*b+log 2)) := by
        apply exp_le_exp.mpr
        have hh' : 0 ≤ log (H+1) := log_nonneg (by linarith)
        dsimp [a]; linarith
      _ ≤ _ := by rw [he]; nlinarith [exp_pos (-((h:ℝ)*b))]
  obtain ⟨rows,hcard,hcovers,hlen⟩ := PublicTables.exists_cover (rowLaw W hW h) A a H ha
    (coverInput_card W U N t C b) hea hprob
  let goodrows := rows.filter (fun z => ((cap SharpLogRamsey.Incidence.Incident q U z).card:ℝ) ≤ M)
  let caps := goodrows.image (cap SharpLogRamsey.Incidence.Incident q U)
  refine ⟨caps,?_,?_,?_⟩
  · intro E hE
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hE
    exact ⟨filter_subset _ _,(mem_filter.mp hz).2⟩
  · intro z hz
    obtain ⟨r,hr,hacc⟩ := hcovers ⟨z,hz⟩
    have hg : GoodCap SharpLogRamsey.Incidence.Incident q U z.2 M r := hacc.2
    refine ⟨cap SharpLogRamsey.Incidence.Incident q U r,mem_image.mpr ⟨r,mem_filter.mpr ⟨hr,hg.1⟩,rfl⟩,?_⟩
    have hc := cap_capture hz.2.2.2.2.1 hg
    rw [hz.2.2.2.2.2.1] at hc
    nlinarith only [hc]
  · have hc : caps.card ≤ ⌈exp (2*a)⌉₊ :=
      (card_image_le.trans (card_filter_le _ _)).trans hcard
    apply le_trans _ hlen
    apply log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hc 1

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectiveTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

lemma incident_mapEquiv (e : V ≃ₗ[K] W) (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) :
    SharpLogRamsey.Incidence.Incident (mapEquiv e a) (mapEquiv e.symm.dualMap b) ↔ SharpLogRamsey.Incidence.Incident a b := by
  induction a using Projectivization.ind with
  | h v hv =>
    induction b using Projectivization.ind with
    | h f hf =>
      dsimp only [mapEquiv,Equiv.coe_fn_mk]
      rw [Projectivization.map_mk,Projectivization.map_mk,
        Projection.incident_mk_iff,Projection.incident_mk_iff]
      simp only [LinearEquiv.coe_coe,LinearEquiv.dualMap_apply,e.symm_apply_apply]

lemma incidenceCount_mapEquiv (e : V ≃ₗ[K] W)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount (S.image (mapEquiv e)) (T.image (mapEquiv e.symm.dualMap))=
      incidenceCount S T := by
  unfold incidenceCount
  rw [sum_image (mapEquiv e.symm.dualMap).injective.injOn]
  apply sum_congr rfl
  intro t ht
  rw [filter_image]
  simp only [incident_mapEquiv]
  exact card_image_of_injective _ (mapEquiv e).injective

variable [FiniteDimensional K V]

lemma pullback_cover {α β : Type*} (e : α ≃ β) (U S : Finset α)
    (E : Finset β) (hE : E ⊆ U.image e) :
    E.image e.symm ⊆ U ∧ (E.image e.symm).card=E.card ∧
      (S∩E.image e.symm).card=((S.image e)∩E).card := by
  refine ⟨?_,card_image_of_injective _ e.symm.injective,?_⟩
  · intro a ha
    obtain ⟨b,hb,he⟩ := mem_image.mp ha
    obtain ⟨a₀,ha₀,he₀⟩ := mem_image.mp (hE hb)
    have hba : e.symm b=a₀ := by rw [←he₀,e.symm_apply_apply]
    rw [←he,hba]
    exact ha₀
  · have he : (S∩E.image e.symm).image e=(S.image e)∩E := by
      rw [image_inter _ _ e.injective]
      congr 1
      ext b
      simp
    rw [←he,card_image_of_injective _ e.injective]

end
end SharpLogRamsey.ProjectiveDuality

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real
open scoped Classical BigOperators
noncomputable section

lemma geom_card_le {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    ∑ i ∈ range r,q^i ≤ q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ,pow_succ]
    calc
      _ ≤ q^r+q^r := Nat.add_le_add_right ih _
      _ = q^r*2 := (Nat.mul_two _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hq

lemma projective_log_card {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype (Projectivization K V)]
    (r : ℕ) (hdim : Module.finrank K V=r) :
    log ((Fintype.card (Projectivization K V):ℝ)+1) ≤ ((r:ℝ)+1)*Nat.card K := by
  have hqN : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast hqN.trans' (by norm_num : 1 ≤ 2)
  have hq0 : (0:ℝ) < Nat.card K := by linarith
  have hcard : (Fintype.card (Projectivization K V):ℝ) ≤ (Nat.card K:ℝ)^r := by
    have hn : Fintype.card (Projectivization K V) ≤ Nat.card K^r := by
      rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
      exact geom_card_le hqN r
    exact_mod_cast hn
  have hpow : 1 ≤ (Nat.card K:ℝ)^r := one_le_pow₀ hq
  have hs : (Fintype.card (Projectivization K V):ℝ)+1 ≤ 2*(Nat.card K:ℝ)^r := by linarith
  apply (log_le_log (by positivity) hs).trans
  rw [log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow]
  have hl2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hlq : log (Nat.card K:ℝ) ≤ Nat.card K :=
    (log_le_sub_one_of_pos hq0).trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left hlq (show 0 ≤ (r:ℝ) by positivity)
  linarith

lemma pair_log_card {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype (Projectivization K V)]
    [Fintype (Projectivization K (Module.Dual K V))]
    (r : ℕ) (hdim : Module.finrank K V=r) :
    log (((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2+1) ≤
      (2*(r:ℝ)+2)*Nat.card K := by
  have hA := projective_log_card r hdim
  have hB := projective_log_card (K:=K) (V:=Module.Dual K V) r
    (Subspace.dual_finrank_eq.trans hdim)
  let A : ℝ := Fintype.card (Projectivization K V)
  let B : ℝ := Fintype.card (Projectivization K (Module.Dual K V))
  have ha : 0 ≤ A := by positivity
  have hb : 0 ≤ B := by positivity
  have hl2 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hu2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hh : (A+B)*log 2+1 ≤ (A+1)*(B+1) := by nlinarith [mul_nonneg ha hb]
  have hl := log_le_log (by positivity : 0 < (A+B)*log 2+1) hh
  rw [log_mul (by positivity) (by positivity)] at hl
  change log ((A+B)*log 2+1) ≤ _
  change log (A+1) ≤ _ at hA
  change log (B+1) ≤ _ at hB
  linarith

lemma row_cost {q P d B H C J : ℝ} {h : ℕ}
    (hq : 1 ≤ q) (hP : 1 ≤ P) (hd : 0 ≤ d) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hBP : B ≤ C*P)
    (hh : (h:ℝ) ≤ 20*q*(d+2)+1) (hH : log (H+1) ≤ J*q) :
    2*((h:ℝ)*B+log 2+log (H+1))+log 3 ≤
      (100*C+2*J+10)*q*P*(d+P) := by
  have hu2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hu3 : log (3:ℝ) ≤ 2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hh' : (h:ℝ) ≤ 21*q*(d+2) := by nlinarith
  have hmul := mul_le_mul hh' hBP hB (show 0 ≤ 21*q*(d+2) by positivity)
  have hdP : d+2 ≤ 2*(d+P) := by linarith
  have hmul' := mul_le_mul_of_nonneg_left hdP (show 0 ≤ 21*C*q*P by positivity)
  let v := q*P*(d+P)
  have hvq : q ≤ v := by
    have hp : 1 ≤ P*(d+P) := one_le_mul_of_one_le_of_one_le hP (by linarith)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ q by linarith)
    dsimp only [v]; nlinarith only [hh]
  have hv : 1 ≤ v := hq.trans hvq
  have hj := mul_le_mul_of_nonneg_left hvq hJ
  have hp : 0 ≤ C*v := by positivity
  dsimp only [v] at *
  nlinarith

lemma scheduleLength_le {q u t : ℝ} (hq : 0 ≤ q) (ht : 0 < t) (htu : t ≤ u) :
    (scheduleLength q u t:ℝ) ≤ 20*q*(log (u/t)+2)+1 := by
  have hl : 0 ≤ log (u/t) := log_nonneg ((le_div_iff₀ ht).mpr (by simpa using htu))
  exact (Nat.ceil_lt_add_one (by positivity)).le

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma incidenceCount_mono_left {S S' : Finset (Projectivization K V)}
    (h : S'⊆S) (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount S' T≤ incidenceCount S T := by
  unfold incidenceCount
  exact sum_le_sum (fun _ _ => card_le_card (filter_subset_filter _ h))

theorem extend_cover {n : ℕ} (hdim : Module.finrank K V=n+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (htu : t≤U.card) (b : ℝ) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(n+3)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card t
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let E := 2*((h:ℝ)*(b+log 2)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
      (∀ E∈caps,E⊆U ∧ (E.card:ℝ)≤2000*q^(n+3)/N) ∧
      (∀ S T,S.card=N → T⊆U → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(20000*q) →
        (∃ W∈descriptions,(N:ℝ)/2≤(S∩W).card) →
        ∃ E∈caps,(99/100:ℝ)*t≤(T∩E).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card t
  let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
  let E := 2*((h:ℝ)*(b+log 2)+log 2+log (H+1))+log 3
  have hlog2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have hE : 0≤E := by
    have hH : 0≤H := mul_nonneg (by positivity) hlog2
    have hlogH : 0≤log (H+1) := log_nonneg (by linarith)
    have hlog3 : 0≤log (3:ℝ) := log_nonneg (by norm_num)
    dsimp only [E]
    positivity
  have hall (W : Finset (Projectivization K V)) :
      ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
        (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤2000*q^(n+3)/N) ∧
        (∀ z,CoverInput W U N t 2 (b+log 2) z →
          ∃ F∈caps,(99/100:ℝ)*t≤(z.2∩F).card) ∧
        log ((caps.card:ℝ)+1)≤E := by
    by_cases hW : W.Nonempty
    · obtain ⟨caps,hs,hc,hl⟩ := public_validation_cover hdim W hW U N t hN ht htu
        2 (b+log 2) (by norm_num) (add_nonneg hb hlog2) hprod
      refine ⟨caps,?_,hc,hl⟩
      intro F hF
      simpa only [show (1000:ℝ)*2=2000 by norm_num] using hs F hF
    · have hw : W=∅ := not_nonempty_iff_eq_empty.mp hW
      refine ⟨∅,by simp,?_,?_⟩
      · intro z hz
        exact (hz.1.ne_empty (subset_empty.mp (hw ▸ hz.2.1))).elim
      · simpa using hE
  choose family hfsize hfcapture hflen using hall
  let caps := descriptions.biUnion family
  refine ⟨caps,?_,?_,?_⟩
  · intro F hF
    obtain ⟨W,_,hWF⟩ := mem_biUnion.mp hF
    exact hfsize W F hWF
  · intro S T hSN hTU hTt hsp hcap
    obtain ⟨W,hW,hcapture⟩ := hcap
    let X := S∩W
    have hnr : (0:ℝ)<N := by exact_mod_cast hN
    have hxr : (0:ℝ)<X.card := (half_pos hnr).trans_le hcapture
    have hX : X.Nonempty := card_pos.mp (by exact_mod_cast hxr)
    have hNX : (N:ℝ)≤2*X.card := by linarith
    have hratio : (W.card:ℝ)≤exp (b+log 2)*X.card := by
      apply (hsize W hW).trans
      rw [exp_add,exp_log (by norm_num : (0:ℝ)<2)]
      nlinarith only [mul_le_mul_of_nonneg_right hNX (exp_pos b).le]
    have hq : 0<q := by
      dsimp only [q]
      exact_mod_cast Nat.card_pos (α:=K)
    have hspX : (incidenceCount X T:ℝ)≤(X.card:ℝ)*T.card/(10000*Nat.card K) := by
      have hmono : (incidenceCount X T:ℝ)≤ incidenceCount S T := by
        exact_mod_cast incidenceCount_mono_left inter_subset_left T
      apply hmono.trans (hsp.trans _)
      rw [hTt]
      have ht0 : (0:ℝ)≤t := by positivity
      have hh := mul_le_mul_of_nonneg_right hNX ht0
      dsimp only [q] at hq ⊢
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hh,mul_nonneg (show 0≤2*(X.card:ℝ)*t-N*t by linarith) hq.le]
    have hi : CoverInput W U N t 2 (b+log 2) (X,T) :=
      ⟨hX,inter_subset_right,hNX,hratio,hTU,hTt,hspX⟩
    obtain ⟨F,hF,hcapF⟩ := hfcapture W (X,T) hi
    exact ⟨F,mem_biUnion.mpr ⟨W,hW,hF⟩,hcapF⟩
  · have he := one_le_exp_iff.mpr hE
    have hf (W : Finset (Projectivization K V)) : ((family W).card:ℝ)≤exp E := by
      have hh := exp_le_exp.mpr (hflen W)
      rw [exp_log (by positivity)] at hh
      linarith
    have hc : (caps.card:ℝ)≤(descriptions.card:ℝ)*exp E := by
      calc
        _ ≤ ∑ W∈descriptions,((family W).card:ℝ) := by exact_mod_cast card_biUnion_le (s:=descriptions) (t:=family)
        _ ≤ ∑ _W∈descriptions,exp E := sum_le_sum (fun W _ => hf W)
        _ = _ := by simp
    have hbound : (caps.card:ℝ)+1≤((descriptions.card:ℝ)+1)*exp E := by nlinarith
    have hl := log_le_log (by positivity : (0:ℝ) < caps.card+1) hbound
    rwa [log_mul (by positivity) (exp_ne_zero _),log_exp] at hl

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem extend_cover_fraction {n : ℕ} (hdim : Module.finrank K V=n+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (htu : t≤U.card) (c b : ℝ) (hc : 1 ≤ c) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(n+3)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card t
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let E := 2*((h:ℝ)*(b+log c)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
      (∀ E∈caps,E⊆U ∧ (E.card:ℝ)≤(1000*c)*q^(n+3)/N) ∧
      (∀ S T,S.card=N → T⊆U → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(10000*c*q) →
        (∃ W∈descriptions,(N:ℝ)/c≤(S∩W).card) →
        ∃ E∈caps,(99/100:ℝ)*t≤(T∩E).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card t
  let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
  let E := 2*((h:ℝ)*(b+log c)+log 2+log (H+1))+log 3
  have hlog2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have hlogc : 0≤log c := log_nonneg hc
  have hcp : 0 < c := by linarith
  have hE : 0≤E := by
    have hH : 0≤H := mul_nonneg (by positivity) hlog2
    have hlogH : 0≤log (H+1) := log_nonneg (by linarith)
    have hlog3 : 0≤log (3:ℝ) := log_nonneg (by norm_num)
    dsimp only [E]
    positivity
  have hall (W : Finset (Projectivization K V)) :
      ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
        (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤(1000*c)*q^(n+3)/N) ∧
        (∀ z,CoverInput W U N t c (b+log c) z →
          ∃ F∈caps,(99/100:ℝ)*t≤(z.2∩F).card) ∧
        log ((caps.card:ℝ)+1)≤E := by
    by_cases hW : W.Nonempty
    · obtain ⟨caps,hs,hc,hl⟩ := public_validation_cover hdim W hW U N t hN ht htu
        c (b+log c) hc (add_nonneg hb hlogc) hprod
      refine ⟨caps,?_,hc,hl⟩
      intro F hF
      exact hs F hF
    · have hw : W=∅ := not_nonempty_iff_eq_empty.mp hW
      refine ⟨∅,by simp,?_,?_⟩
      · intro z hz
        exact (hz.1.ne_empty (subset_empty.mp (hw ▸ hz.2.1))).elim
      · simpa using hE
  choose family hfsize hfcapture hflen using hall
  let caps := descriptions.biUnion family
  refine ⟨caps,?_,?_,?_⟩
  · intro F hF
    obtain ⟨W,_,hWF⟩ := mem_biUnion.mp hF
    exact hfsize W F hWF
  · intro S T hSN hTU hTt hsp hcap
    obtain ⟨W,hW,hcapture⟩ := hcap
    let X := S∩W
    have hnr : (0:ℝ)<N := by exact_mod_cast hN
    have hxr : (0:ℝ)<X.card := (div_pos hnr hcp).trans_le hcapture
    have hX : X.Nonempty := card_pos.mp (by exact_mod_cast hxr)
    have hNX : (N:ℝ) ≤ c*X.card := by
      have hh := (div_le_iff₀ hcp).mp hcapture
      linarith
    have hratio : (W.card:ℝ)≤exp (b+log c)*X.card := by
      apply (hsize W hW).trans
      rw [exp_add,exp_log hcp]
      nlinarith only [mul_le_mul_of_nonneg_right hNX (exp_pos b).le]
    have hq : 0<q := by
      dsimp only [q]
      exact_mod_cast Nat.card_pos (α:=K)
    have hspX : (incidenceCount X T:ℝ)≤(X.card:ℝ)*T.card/(10000*Nat.card K) := by
      have hmono : (incidenceCount X T:ℝ)≤ incidenceCount S T := by
        exact_mod_cast incidenceCount_mono_left inter_subset_left T
      apply hmono.trans (hsp.trans _)
      rw [hTt]
      have ht0 : (0:ℝ)≤t := by positivity
      have hh := mul_le_mul_of_nonneg_right hNX ht0
      dsimp only [q] at hq ⊢
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hhq := mul_le_mul_of_nonneg_right hh hq.le
      nlinarith only [hhq]
    have hi : CoverInput W U N t c (b+log c) (X,T) :=
      ⟨hX,inter_subset_right,hNX,hratio,hTU,hTt,hspX⟩
    obtain ⟨F,hF,hcapF⟩ := hfcapture W (X,T) hi
    exact ⟨F,mem_biUnion.mpr ⟨W,hW,hF⟩,hcapF⟩
  · have he := one_le_exp_iff.mpr hE
    have hf (W : Finset (Projectivization K V)) : ((family W).card:ℝ)≤exp E := by
      have hh := exp_le_exp.mpr (hflen W)
      rw [exp_log (by positivity)] at hh
      linarith
    have hc : (caps.card:ℝ)≤(descriptions.card:ℝ)*exp E := by
      calc
        _ ≤ ∑ W∈descriptions,((family W).card:ℝ) := by exact_mod_cast card_biUnion_le (s:=descriptions) (t:=family)
        _ ≤ ∑ _W∈descriptions,exp E := sum_le_sum (fun W _ => hf W)
        _ = _ := by simp
    have hbound : (caps.card:ℝ)+1≤((descriptions.card:ℝ)+1)*exp E := by nlinarith
    have hl := log_le_log (by positivity : (0:ℝ) < caps.card+1) hbound
    rwa [log_mul (by positivity) (exp_ne_zero _),log_exp] at hl

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReturn_2
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReturn_3
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReturn_5
theorem reverse_extend {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V)) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (b : ℝ) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E := 2*((scheduleLength q U.card N:ℝ)*(b+log 2)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤2000*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(20000*q) →
        (∃ W∈descriptions,(t:ℝ)/2≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let e := bidual (K:=K) (V:=V)
  have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
  have hd : Module.finrank K (Module.Dual K V)=r+3 := Subspace.dual_finrank_eq.trans hdim
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hd descriptions (U.image e) t N ht hN
    (by rwa [hcU]) 2 b (by norm_num) hb hsize (by simpa [mul_comm] using hprod)
  refine ⟨A.image (fun W => W.image e.symm),?_,?_,?_⟩
  · intro W hW
    obtain ⟨F,hF,rfl⟩ := mem_image.mp hW
    obtain ⟨hFU,hcard,_⟩ := pullback_cover e U ∅ F (hAs F hF).1
    refine ⟨hFU,?_⟩
    rw [hcard]
    simpa only [show (1000:ℝ)*2=2000 by norm_num] using (hAs F hF).2
  · intro S T hSU hSN hTt hsp hcap
    have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
    have hcS : (S.image e).card=N := (card_image_of_injective _ e.injective).trans hSN
    have hsp' : (incidenceCount T (S.image e):ℝ)≤(t:ℝ)*N/(10000*2*Nat.card K) := by
      rw [hinc]
      convert hsp using 1 <;> first | rfl | ring
    obtain ⟨F,hF,hcapture⟩ := hAc T (S.image e) hTt (image_subset_image hSU) hcS hsp' hcap
    refine ⟨F.image e.symm,mem_image.mpr ⟨F,hF,rfl⟩,?_⟩
    rw [(pullback_cover e U S F (hAs F hF).1).2.2]
    exact hcapture
  · have hc : ((A.image (fun W => W.image e.symm)).card:ℝ)≤A.card := by
      exact_mod_cast card_image_le (s:=A) (f:=fun W => W.image e.symm)
    have hl : log (((A.image (fun W => W.image e.symm)).card:ℝ)+1)≤log ((A.card:ℝ)+1) :=
      log_le_log (by positivity) (by linarith)
    exact hl.trans (by simpa only [hcU] using hAl)

lemma reverse_size (q N t C b : ℝ) (r : ℕ) (_hq : 0<q) (hN : 0<N) (hC : 0<C)
    (hprod : q^r*exp (-b)≤N*t) : C*q^r/N≤t*exp (b+log C) := by
  rw [exp_add,exp_log hC]
  apply (div_le_iff₀ hN).mpr
  have h := mul_le_mul_of_nonneg_right hprod (exp_pos b).le
  rw [mul_assoc,←exp_add,neg_add_cancel,exp_zero,mul_one] at h
  nlinarith only [mul_le_mul_of_nonneg_left h hC.le]

theorem return_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (c B b : ℝ) (hc : 2 ≤ c) (hB : 0≤B) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp B)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3))
    (hprodlo : (Nat.card K:ℝ)^(r+3)*exp (-b)≤(N:ℝ)*t) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let H' := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E₁ := 2*((scheduleLength q UT.card t:ℝ)*(B+log c)+log 2+log (H+1))+log 3
    let E₂ := 2*((scheduleLength q U.card N:ℝ)*(b+log (1000*c)+log 2)+log 2+log (H'+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤2000*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(10000*c*q) →
        (∃ W∈descriptions,(N:ℝ)/c≤(S∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E₁+E₂ := by
  dsimp only
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hdim descriptions UT N t hN ht htU c B
    (by linarith) hB hsize hprod
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hc0 : 0 < c := by linarith
  have hsA (W) (hW : W∈A) : (W.card:ℝ)≤t*exp (b+log (1000*c)) :=
    (hAs W hW).2.trans (reverse_size (Nat.card K) N t (1000*c) b (r+3) hq hn (by positivity) hprodlo)
  obtain ⟨F,hFs,hFc,hFl⟩ := reverse_extend hdim A U N t hN ht hNU (b+log (1000*c))
    (add_nonneg hb (log_nonneg (by linarith))) hsA hprod
  refine ⟨F,hFs,?_,hFl.trans (by linarith only [hAl])⟩
  intro S T hSU hSN hTU hTt hsp hcap
  obtain ⟨W,hW,hcapture⟩ := hAc S T hSN hTU hTt hsp hcap
  apply hFc S T hSU hSN hTt _ ⟨W,hW,by linarith⟩
  apply hsp.trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedValidationReverse_2_r99179f_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReverse_3
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReverse_5
theorem reverse_extend_fraction {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V)) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (c b : ℝ) (hc : 1 ≤ c) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E := 2*((scheduleLength q U.card N:ℝ)*(b+log c)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤(1000*c)*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(10000*c*q) →
        (∃ W∈descriptions,(t:ℝ)/c≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let e := bidual (K:=K) (V:=V)
  have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
  have hd : Module.finrank K (Module.Dual K V)=r+3 := Subspace.dual_finrank_eq.trans hdim
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hd descriptions (U.image e) t N ht hN
    (by rwa [hcU]) c b hc hb hsize (by simpa [mul_comm] using hprod)
  refine ⟨A.image (fun W => W.image e.symm),?_,?_,?_⟩
  · intro W hW
    obtain ⟨F,hF,rfl⟩ := mem_image.mp hW
    obtain ⟨hFU,hcard,_⟩ := pullback_cover e U ∅ F (hAs F hF).1
    refine ⟨hFU,?_⟩
    rw [hcard]
    exact (hAs F hF).2
  · intro S T hSU hSN hTt hsp hcap
    have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
    have hcS : (S.image e).card=N := (card_image_of_injective _ e.injective).trans hSN
    have hsp' : (incidenceCount T (S.image e):ℝ)≤(t:ℝ)*N/(10000*c*Nat.card K) := by
      rw [hinc]
      convert hsp using 1 <;> first | rfl | ring
    obtain ⟨F,hF,hcapture⟩ := hAc T (S.image e) hTt (image_subset_image hSU) hcS hsp' hcap
    refine ⟨F.image e.symm,mem_image.mpr ⟨F,hF,rfl⟩,?_⟩
    rw [(pullback_cover e U S F (hAs F hF).1).2.2]
    exact hcapture
  · have hc : ((A.image (fun W => W.image e.symm)).card:ℝ)≤A.card := by
      exact_mod_cast card_image_le (s:=A) (f:=fun W => W.image e.symm)
    have hl : log (((A.image (fun W => W.image e.symm)).card:ℝ)+1)≤log ((A.card:ℝ)+1) :=
      log_le_log (by positivity) (by linarith)
    exact hl.trans (by simpa only [hcU] using hAl)

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationGapCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

lemma row_cost_sum {q P d e B H J : ℝ} {h : ℕ}
    (hq : 1 ≤ q) (hP : 200000 ≤ P) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hB : 0 ≤ B) (hBP : B ≤ 7*P) (hJ : 0 ≤ J)
    (hh : (h:ℝ) ≤ 20*q*(d+2)+1) (hH : log (H+1) ≤ J*q) :
    2*((h:ℝ)*B+log 2+log (H+1))+log 3 ≤
      (710+2*J)*q*P*(d+e+P) := by
  have hr := row_cost hq (by linarith : 1 ≤ P) hd hB (by norm_num : (0:ℝ) ≤ 7)
    hJ hBP hh hH
  rw [show (100:ℝ)*7+2*J+10=710+2*J by ring] at hr
  apply hr.trans
  gcongr
  linarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma log_hundred : log (100:ℝ) ≤ 99 := by
  have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
  norm_num at hh ⊢
  exact hh
lemma log_hundred_thousand : log (100000:ℝ) ≤ 99999 := by
  have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100000)
  norm_num at hh ⊢
  exact hh

attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationGapCosts_1
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationGapCosts_3
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationGapCosts_5
theorem return_gap_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (P b : ℝ) (hP : 200000≤P) (hb : 0≤b) (hbP : b≤P)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp (6*P))
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3))
    (hprodlo : (Nat.card K:ℝ)^(r+3)*exp (-b)≤(N:ℝ)*t) :
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤100000*(Nat.card K:ℝ)^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(1000000*Nat.card K) →
        (∃ W∈descriptions,(N:ℝ)/100≤(S∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+
        (1500+8*(r:ℝ))*(Nat.card K:ℝ)*P*
          (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/t)+P) := by
  obtain ⟨A,hs,hc,hl⟩ := return_cover hdim descriptions U UT N t hN ht hNU htU
    100 (6*P) b (by norm_num) (by positivity) hb hsize hprod hprodlo
  refine ⟨A,?_,?_,?_⟩
  · intro F hF
    refine ⟨(hs F hF).1,(hs F hF).2.trans ?_⟩
    gcongr
    norm_num
  · intro S T hSU hSN hTU hTt hsp hcap
    exact hc S T hSU hSN hTU hTt (by simpa only [show (10000:ℝ)*100=1000000 by norm_num] using hsp) hcap
  · let q : ℝ := Nat.card K
    let d := log ((U.card:ℝ)/N)
    let e := log ((UT.card:ℝ)/t)
    have hq : 1≤q := by
      change (1:ℝ)≤(Nat.card K:ℝ)
      exact_mod_cast Nat.card_pos (α:=K)
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have ht' : (0:ℝ)<t := by exact_mod_cast ht
    have hnu : (N:ℝ)≤U.card := by exact_mod_cast hNU
    have htu : (t:ℝ)≤UT.card := by exact_mod_cast htU
    have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr (by simpa using hnu))
    have he : 0≤e := log_nonneg ((le_div_iff₀ ht').mpr (by simpa using htu))
    have hB1 : 6*P+log 100≤7*P := by linarith only [log_hundred,hP]
    have hB2 : b+log ((1000:ℝ)*100)+log 2≤7*P := by
      have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      norm_num only [show (1000:ℝ)*100=100000 by norm_num]
      linarith only [hbP,hP,log_hundred_thousand,hh]
    have hH1 := pair_log_card (r+3) hdim
    have hH2 := pair_log_card (K:=K) (V:=Module.Dual K V) (r+3)
      (Subspace.dual_finrank_eq.trans hdim)
    have E1 := row_cost_sum hq hP he hd
      (add_nonneg (by positivity) (log_nonneg (by norm_num))) hB1
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) ht' htu) hH1
    have E2 := row_cost_sum hq hP hd he
      (add_nonneg (add_nonneg hb (log_nonneg (by norm_num))) (log_nonneg (by norm_num))) hB2
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) hn hnu) hH2
    have hz : 0≤q*P*(d+e+P) := by positivity
    simp only [Nat.cast_add,Nat.cast_ofNat] at E1 E2
    change log ((A.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+(1500+8*(r:ℝ))*q*P*(d+e+P)
    dsimp only [q,d,e] at *
    have hcombined := add_le_add E1 E2
    ring_nf at hcombined hl hz ⊢
    linarith only [hl,hcombined,hz]

theorem reverse_gap_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (P : ℝ) (hP : 200000≤P)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp (6*P))
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤100000*(Nat.card K:ℝ)^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(1000000*Nat.card K) →
        (∃ W∈descriptions,(t:ℝ)/100≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+
        (1500+8*(r:ℝ))*(Nat.card K:ℝ)*P*
          (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/t)+P) := by
  obtain ⟨A,hs,hc,hl⟩ := reverse_extend_fraction hdim descriptions U N t hN ht hNU
    100 (6*P) (by norm_num) (by positivity) hsize hprod
  refine ⟨A,?_,?_,?_⟩
  · simpa only [show (1000:ℝ)*100=100000 by norm_num] using hs
  · intro S T hSU hSN hTt hsp hcap
    exact hc S T hSU hSN hTt (by simpa only [show (10000:ℝ)*100=1000000 by norm_num] using hsp) hcap
  · let q : ℝ := Nat.card K
    let d := log ((U.card:ℝ)/N)
    let e := log ((UT.card:ℝ)/t)
    have hq : 1≤q := by
      change (1:ℝ)≤(Nat.card K:ℝ)
      exact_mod_cast Nat.card_pos (α:=K)
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have ht' : (0:ℝ)<t := by exact_mod_cast ht
    have hnu : (N:ℝ)≤U.card := by exact_mod_cast hNU
    have htu : (t:ℝ)≤UT.card := by exact_mod_cast htU
    have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr (by simpa using hnu))
    have he : 0≤e := log_nonneg ((le_div_iff₀ ht').mpr (by simpa using htu))
    have hB : 6*P+log 100≤7*P := by linarith only [log_hundred,hP]
    have hH := pair_log_card (K:=K) (V:=Module.Dual K V) (r+3)
      (Subspace.dual_finrank_eq.trans hdim)
    have E := row_cost_sum hq hP hd he
      (add_nonneg (by positivity) (log_nonneg (by norm_num))) hB
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) hn hnu) hH
    have hz : 0≤q*P*(d+e+P) := by positivity
    have hr : 0≤(r:ℝ)*q*P*(d+e+P) := by positivity
    simp only [Nat.cast_add,Nat.cast_ofNat] at E
    change log ((A.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+(1500+8*(r:ℝ))*q*P*(d+e+P)
    dsimp only [q,d,e] at *
    nlinarith only [hl,E,hz,hr]

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_PlanarScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Topology
noncomputable section

lemma even_order {σ P : ℝ} (hσ : 0<σ) (hP : 0<P) :
    ∃ p : ℕ,0<p ∧ Even p ∧ 10000*σ≤(p:ℝ)*P ∧ (p:ℝ)≤10000*σ/P+2 := by
  let p := 2*⌈5000*σ/P⌉₊
  have hn : 0≤5000*σ/P := by positivity
  have hl := Nat.le_ceil (5000*σ/P)
  have hu := Nat.ceil_lt_add_one hn
  have hp : (p:ℝ)=2*(⌈5000*σ/P⌉₊:ℝ) := by simp only [p,Nat.cast_mul,Nat.cast_ofNat]
  have hlo : 10000*σ≤(p:ℝ)*P := by
    have hh := mul_le_mul_of_nonneg_right hl hP.le
    have he : (5000*σ/P)*P=5000*σ := div_mul_cancel₀ _ hP.ne'
    rw [he] at hh
    rw [hp]
    nlinarith only [hh]
  refine ⟨p,?_,by dsimp [p]; exact even_two_mul _,hlo,?_⟩
  · have hpos : (0:ℝ)<p := by nlinarith only [hlo,hσ,hP]
    exact_mod_cast hpos
  · rw [hp]
    calc
      _ ≤ 2*(5000*σ/P+1) := (mul_lt_mul_of_pos_left hu (by norm_num : (0:ℝ)<2)).le
      _ = _ := by ring

lemma eventually_schedule {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      (R:ℝ)*exp (-(24/25:ℝ)*scaleL σ η D)≤1/10 := by
  have hh := ScaleSelection.eventually_polynomial_le_exp_rpow 40 (beta η) (9*beta η) (24/25)
    (by have := beta_pos hη; positivity) (by norm_num)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with σ hs hσ D R had
  have hR := R_bound hσ hη had
  have hL := (scale_bounds hσ hη had).1
  have he : 10*(R:ℝ)≤exp ((24/25:ℝ)*scaleL σ η D) := by
    calc
      _ ≤ 40*σ^beta η := by linarith
      _ ≤ exp ((24/25:ℝ)*σ^(9*beta η)) := hs
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right he (exp_pos (-(24/25:ℝ)*scaleL σ η D)).le
  have heq : exp ((24/25:ℝ)*scaleL σ η D)*exp (-(24/25:ℝ)*scaleL σ η D)=1 := by
    rw [←exp_add]; ring_nf; exact exp_zero
  rw [heq] at hm
  linarith

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_DescriptionHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DescriptionHeaders
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem card_submodule_le :
    Nat.card (Submodule K V)≤(Nat.card K)^(Module.finrank K V)^2 := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (V→ₗ[K]V) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hs : Function.Surjective (LinearMap.range : (V→ₗ[K]V)→Submodule K V) := by
    intro W
    obtain ⟨Q,hQ⟩ := W.exists_isCompl
    exact ⟨W.projection Q hQ,W.range_projection hQ⟩
  apply (Nat.card_le_card_of_surjective _ hs).trans_eq
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (V→ₗ[K]V) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card,Module.finrank_linearMap,pow_two] using
    (Module.card_eq_pow_finrank (K:=K) (V:=V→ₗ[K]V))

end
end SharpLogRamsey.DescriptionHeaders

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_HeavyPlaneScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology

lemma dyadic_class_count {q : ℕ} {σ : ℝ} (_hq : 0<q) (hex : exp σ=(q:ℝ)) :
    ((Nat.log 2 q+1:ℕ):ℝ)≤σ/log 2+1 := by
  have hh := Real.natLog_le_logb q 2
  rw [Real.logb,show log (q:ℝ)=σ by rw [←hex,log_exp]] at hh
  push_cast
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem eventually_heavy_loss {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ q : ℕ,0<q → exp σ=(q:ℝ) →
    ∀ D R,Admissible σ η D R →
      0≤log (200*(Nat.log 2 q+1:ℕ)) ∧
      log (200*(Nat.log 2 q+1:ℕ))≤ scaleKstar σ η D ∧
      log 50+log (4*(Nat.log 2 q+1:ℕ))≤ scaleP σ η D R := by
  have hβ := beta_pos hη
  have hp := ScaleSelection.eventually_polynomial_le_exp_rpow
    (200*(1/log 2+1)) 1 (7*beta η) 1 (by positivity) (by norm_num)
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with σ hp hσ
  intro q hq hex D R had
  have hσp : 0<σ := by linarith
  have h2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hL : (0:ℝ)<(Nat.log 2 q+1:ℕ) := by positivity
  have hcount := dyadic_class_count hq hex
  have hlin : (200*(Nat.log 2 q+1:ℕ):ℝ)≤200*(1/log 2+1)*σ := by
    push_cast at *
    have ha : (Nat.log 2 q:ℝ)+1≤σ*(1/log 2+1) := by
      calc
        _ ≤ σ/log 2+σ := by linarith
        _ = _ := by ring
    nlinarith
  have hlog : log (200*(Nat.log 2 q+1:ℕ))≤σ^(7*beta η) := by
    have he : (200*(Nat.log 2 q+1:ℕ):ℝ)≤exp (σ^(7*beta η)) := by
      apply hlin.trans
      simpa only [rpow_one,one_mul] using hp
    have hh := log_le_log (by positivity : (0:ℝ)<200*(Nat.log 2 q+1:ℕ)) he
    simpa only [log_exp] using hh
  have hK : σ^(7*beta η)≤ scaleKstar σ η D := by
    unfold scaleKstar
    have hh := mul_le_mul_of_nonneg_right had.D_lower (rpow_nonneg hσp.le (6*beta η))
    rw [←rpow_add hσp] at hh
    simpa only [show beta η+6*beta η=7*beta η by ring] using hh
  have hLP : σ^(7*beta η)≤ scaleP σ η D R := by
    have hLL := (scale_bounds hσ hη had).1
    have hlow : σ^(7*beta η)≤σ^(9*beta η) := rpow_le_rpow_of_exponent_le hσ (by linarith)
    have hR : (1:ℝ)≤R := by
      have hrr := had.R_lower
      have hp1 : 1≤σ^beta η := one_le_rpow hσ hβ.le
      linarith
    exact (hlow.trans hLL).trans (le_mul_of_one_le_right (L_pos hσp had).le hR)
  refine ⟨log_nonneg ?_,hlog.trans hK,?_⟩
  · have hh : (1:ℝ)≤(Nat.log 2 q+1:ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
    linarith
  · rw [←log_mul (by norm_num : (50:ℝ)≠0) (by positivity : (4*(Nat.log 2 q+1:ℕ):ℝ)≠0),
      show (50:ℝ)*(4*(Nat.log 2 q+1:ℕ))=200*(Nat.log 2 q+1:ℕ) by ring]
    exact hlog.trans hLP

end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MultiplicityClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.MultiplicityClass
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

lemma weight_mono (S U : Finset α) (hSU : S⊆U) (f : α→β) (y : β) :
    weight S f y≤weight U f y := card_le_card (filter_subset_filter _ hSU)

lemma weight_pos (S : Finset α) (f : α→β) (x : α) (hx : x∈S) :
    0<weight S f (f x) := card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩

lemma domain_card (U : Finset α) (f : α→β) (h : ℕ) :
    h*(domain U f h).card≤U.card := by
  calc
    _ = ∑ y∈domain U f h,h := by simp [mul_comm]
    _ ≤ ∑ y∈domain U f h,weight U f y :=
      sum_le_sum (fun y hy => (mem_filter.mp hy).2)
    _ ≤ ∑ y∈U.image f,weight U f y := sum_le_sum_of_subset (filter_subset _ _)
    _ = U.card := (card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem f hx)).symm

theorem exists_class (S U : Finset α) (hS : S.Nonempty) (hSU : S⊆U)
    (f : α→β) (q : ℕ) (hq : 1≤q) (hf : ∀ y,weight S f y≤q) :
    ∃ (h : ℕ) (T : Finset β), 1≤h ∧ h≤q ∧ T.Nonempty ∧
      T⊆domain U f h ∧ T⊆S.image f ∧
      (S.card:ℝ)≤2*h*(Nat.log 2 q+1:ℕ)*(T.card:ℝ) ∧
      ∀ y∈T,h≤weight S f y ∧ weight S f y<2*h := by
  let lab : α→ℕ := fun x => Nat.log 2 (weight S f (f x))
  let N := Nat.log 2 q+1
  have hN : 0<N := by dsimp [N]; omega
  have hlab : ∀ x∈S,lab x∈range N := by
    intro x hx
    apply mem_range.mpr
    have hh := Nat.log_mono_right (b := 2) (hf (f x))
    dsimp [lab,N]
    omega
  have hnz : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  obtain ⟨k,hk,hkcard⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (M := ℝ) hlab (nonempty_range_iff.mpr (by omega))
    (show (range N).card • ((S.card:ℝ)/N)≤(S.card:ℝ) by
      simp only [card_range,nsmul_eq_mul]; rw [mul_div_cancel₀ _ hnz])
  let A := S.filter (fun x => lab x=k)
  let T := A.image f
  let h := 2^k
  have hh : 1≤h := Nat.one_le_pow _ _ (by omega)
  have hkq : k≤Nat.log 2 q := by have := mem_range.mp hk; dsimp [N] at this; omega
  have hq' : h≤q :=
    (Nat.pow_le_pow_right (by omega : 0<2) hkq).trans (Nat.pow_log_le_self 2 (by omega))
  have ha : A.Nonempty := by
    apply card_pos.mp
    have hsp : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
    have hp : (0:ℝ)<A.card := lt_of_lt_of_le (div_pos hsp (by exact_mod_cast hN)) hkcard
    exact_mod_cast hp
  have hweights : ∀ y∈T,h≤weight S f y ∧ weight S f y<2*h := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    change Nat.log 2 (weight S f (f x))=k at he
    dsimp [h]
    rw [←he]
    exact ⟨Nat.pow_log_le_self 2 (by have := weight_pos S f x hx; omega),by
      simpa [pow_succ,mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1<2) (weight S f (f x))⟩
  refine ⟨h,T,hh,hq',ha.image f,?_,?_,?_,hweights⟩
  · intro y hy
    apply mem_filter.mpr
    obtain ⟨x,hx,hxy⟩ := mem_image.mp hy
    refine ⟨mem_image.mpr ⟨x,hSU (mem_filter.mp hx).1,hxy⟩,?_⟩
    exact (hweights y hy).1.trans (weight_mono S U hSU f y)
  · exact image_subset_image (filter_subset _ _)
  · have hab : A.card≤(2*h)*T.card := by
      apply card_le_mul_card_image_of_maps_to (f := f)
        (fun x hx => mem_image_of_mem f hx) (2*h)
      intro y hy
      exact (weight_mono A S (filter_subset _ _) f y).trans (hweights y hy).2.le
    have hab' : (A.card:ℝ)≤2*h*(T.card:ℝ) := by exact_mod_cast hab
    have hk' : (S.card:ℝ)≤(A.card:ℝ)*N := (div_le_iff₀ (by exact_mod_cast hN)).mp hkcard
    have hm := mul_le_mul_of_nonneg_right hab' (Nat.cast_nonneg N)
    dsimp [N] at hm hk'
    push_cast at hm hk' ⊢
    nlinarith

end
end SharpLogRamsey.MultiplicityClass

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_HeavyPlaneCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset SharpLogRamsey.Incidence SharpLogRamsey.Projection
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma restrict_eq_project (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (t u : {t : Projectivization K (Module.Dual K V) // t ≠ center W hW})
    (he : restrict W hW t = restrict W hW u) :
    project (center W hW) t = project (center W hW) u := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp he
  have hz : t.val.rep - a • u.val.rep ∈ (center W hW).submodule := by
    rw [center_submodule, ← W.dualRestrict_ker_eq_dualAnnihilator]
    change W.dualRestrict (t.val.rep-a • u.val.rep)=0
    rw [map_sub,map_smul,← ha,sub_self]
  unfold project
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨a,?_⟩
  change a • (center W hW).submodule.mkQ u.val.rep = _
  have hh : (center W hW).submodule.mkQ (t.val.rep-a • u.val.rep)=0 := by
    change _ ∈ LinearMap.ker (center W hW).submodule.mkQ
    rwa [Submodule.ker_mkQ]
  rw [map_sub,map_smul,sub_eq_zero] at hh
  exact hh.symm

omit [FiniteDimensional K V] in
lemma incident_mk_left (v : V) (hv : v ≠ 0)
    (f : Projectivization K (Module.Dual K V)) :
    SharpLogRamsey.Incidence.Incident (Projectivization.mk K v hv) f ↔ f.rep v=0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  unfold SharpLogRamsey.Incidence.Incident
  rw [←ha]
  simp [Units.smul_def]

omit [FiniteDimensional K V] in
lemma incident_mk_right (p : Projectivization K V) (f : Module.Dual K V) (hf : f ≠ 0) :
    SharpLogRamsey.Incidence.Incident p (Projectivization.mk K f hf) ↔ f p.rep=0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K f hf
  unfold SharpLogRamsey.Incidence.Incident
  rw [←ha]
  simp [Units.smul_def]

lemma restrict_incident_iff (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (a : Projectivization K W)
    (t : {t : Projectivization K (Module.Dual K V) // t ≠ center W hW}) :
    SharpLogRamsey.Incidence.Incident a (restrict W hW t) ↔
      SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a) t.val := by
  rw [restrict,incident_mk_right]
  conv_rhs => rw [←a.mk_rep,Projectivization.map_mk,incident_mk_left]
  rfl

variable [Finite K] [Fintype (Projectivization K (Module.Dual K V))]

theorem restrict_fiber_card (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (b : Projectivization K (Module.Dual K W)) :
    ((A.subtype (· ≠ center W hW)).filter (fun t => restrict W hW t=b)).card ≤ Nat.card K := by
  let F := (A.subtype (· ≠ center W hW)).filter (fun t => restrict W hW t=b)
  by_cases hF : F.Nonempty
  · obtain ⟨t,ht⟩ := hF
    apply le_trans _ (project_fiber_card A (center W hW) (project (center W hW) t))
    apply card_le_card
    intro u hu
    obtain ⟨hu,hue⟩ := mem_filter.mp hu
    apply mem_filter.mpr ⟨hu,?_⟩
    exact restrict_eq_project W hW u t (hue.trans (mem_filter.mp ht).2.symm)
  · change F.card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hF]
    simp

end
end SharpLogRamsey.HeavyPlaneRestriction

namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset SharpLogRamsey.Incidence SharpLogRamsey.Projection
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma center_restrict_zero (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V) :
    W.dualRestrict (center W hW).rep=0 := by
  have hm : (center W hW).rep ∈ (center W hW).submodule :=
    (rep_mem_line_iff _ _).mpr rfl
  rw [center_submodule,←W.dualRestrict_ker_eq_dualAnnihilator] at hm
  exact hm

lemma center_incident (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V) (a : Projectivization K W) :
    SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a) (center W hW) := by
  rw [←a.mk_rep,Projectivization.map_mk,incident_mk_left]
  have he := congrArg (fun f : Module.Dual K W => f a.rep) (center_restrict_zero W hW)
  exact he

lemma sparse_noncentral (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V)
    (S : Finset (Projectivization K W)) (hS : S.Nonempty)
    (t : Projectivization K (Module.Dual K V)) (δ : ℝ) (hδ : δ<1)
    (hs : ((S.filter (fun a => SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a) t)).card:ℝ)
      ≤δ*S.card) : t≠center W hW := by
  intro ht
  subst t
  have hf : S.filter (fun a => SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a)
      (center W hW))=S := filter_eq_self.mpr (fun a _ => center_incident W hW a)
  rw [hf] at hs
  have hp : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  nlinarith

variable [Finite K] [Fintype (Projectivization K (Module.Dual K V))]

theorem sparse_restriction_class (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V)
    (S : Finset (Projectivization K W)) (hS : S.Nonempty)
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (hT : T.Nonempty) (hTU : T⊆U) (δ : ℝ) (hδ : δ<1)
    (hs : ∀ t∈T,((S.filter (fun a => SharpLogRamsey.Incidence.Incident
      (Projectivization.map W.subtype W.injective_subtype a) t)).card:ℝ)≤δ*S.card) :
    ∃ (h : ℕ) (T₁ U₁ : Finset (Projectivization K (Module.Dual K W))),
      1≤h ∧ h≤Nat.card K ∧ T₁.Nonempty ∧ T₁⊆U₁ ∧
      h*U₁.card≤U.card ∧
      (T.card:ℝ)≤2*h*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ) ∧
      (∀ t∈T₁,((S.filter (fun a => SharpLogRamsey.Incidence.Incident a t)).card:ℝ)≤δ*S.card) ∧
      U₁=MultiplicityClass.domain (U.subtype (· ≠ center W hW)) (restrict W hW) h := by
  have hn : ∀ t∈T,t≠center W hW := fun t ht => sparse_noncentral W hW S hS t δ hδ (hs t ht)
  let A := T.subtype (· ≠ center W hW)
  let B := U.subtype (· ≠ center W hW)
  have hA : A.Nonempty := by
    obtain ⟨t,ht⟩ := hT
    exact ⟨⟨t,hn t ht⟩,mem_subtype.mpr ht⟩
  have hAB : A⊆B := fun t ht => mem_subtype.mpr (hTU (mem_subtype.mp ht))
  have hAc : A.card=T.card := by
    rw [card_subtype,filter_eq_self.mpr hn]
  have hBc : B.card≤U.card := by rw [card_subtype]; exact card_filter_le _ _
  have hq : 1≤Nat.card K := (Finite.one_lt_card : 1<Nat.card K).le
  obtain ⟨h,T₁,hh,hq',hT₁,hsub,himage,hsize,hweights⟩ :=
    MultiplicityClass.exists_class A B hA hAB (restrict W hW) (Nat.card K) hq
      (fun t => restrict_fiber_card W hW T t)
  refine ⟨h,T₁,MultiplicityClass.domain B (restrict W hW) h,hh,hq',hT₁,hsub,
    (MultiplicityClass.domain_card B (restrict W hW) h).trans hBc,?_,?_,rfl⟩
  · rwa [hAc] at hsize
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp (himage ht)
    have hs' := hs u.val (mem_subtype.mp hu)
    have he : S.filter (fun a => SharpLogRamsey.Incidence.Incident a (restrict W hW u))=
      S.filter (fun a => SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a) u.val) := by
      apply filter_congr
      intro a ha
      exact restrict_incident_iff W hW a u
    rwa [he]

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_HeavyPlaneInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset Real Incidence PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedHeavyPlaneInput_2_r99179f_1 : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
attribute [local instance] OAI.SharpLogRamsey.HeavyPlaneRestriction.flat_JoinedHeavyPlaneInput_3
attribute [local instance] OAI.SharpLogRamsey.HeavyPlaneRestriction.flat_JoinedHeavyPlaneInput_4
lemma planeSupport_image (W : Submodule K V) (S : Finset (Projectivization K V)) :
    (planeSupport W S).image (Projectivization.map W.subtype W.injective_subtype)=S∩planePoints W := by
  ext x
  constructor
  · intro hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    refine mem_inter.mpr ⟨(mem_filter.mp ha).2,mem_planePoints.mpr ?_⟩
    exact (_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv W a).property
  · intro hx
    obtain ⟨hS,hW⟩ := mem_inter.mp hx
    let a := (_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv W).symm ⟨x,mem_planePoints.mp hW⟩
    have he : Projectivization.map W.subtype W.injective_subtype a=x :=
      congrArg Subtype.val ((_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv W).apply_symm_apply _)
    exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,by simpa only [he]⟩,he⟩

lemma planeSupport_card (W : Submodule K V) (S : Finset (Projectivization K V)) :
    (planeSupport W S).card=(S∩planePoints W).card := by
  rw [←planeSupport_image,card_image_of_injective _
    (Projectivization.map_injective W.subtype W.injective_subtype)]

lemma planeSupport_incidence_le (W : Submodule K V) (S : Finset (Projectivization K V))
    (t : Projectivization K (Module.Dual K V)) :
    ((planeSupport W S).filter (fun a => SharpLogRamsey.Incidence.Incident
      (Projectivization.map W.subtype W.injective_subtype a) t)).card≤
      (S.filter (fun a => SharpLogRamsey.Incidence.Incident a t)).card := by
  rw [←card_image_of_injective _ (Projectivization.map_injective W.subtype W.injective_subtype)]
  apply card_le_card
  intro x hx
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨ha,ht⟩ := mem_filter.mp ha
  exact mem_filter.mpr ⟨(mem_filter.mp ha).2,ht⟩

theorem heavy_half (W : Submodule K V) (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (τ : ℝ)
    (hτ : 0<τ) (hA : (planeSupport W S).Nonempty)
    (hheavy : (S.card:ℝ)≤50*(planeSupport W S).card)
    (hs : (incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K) :
    ∃ T₀ : Finset (Projectivization K (Module.Dual K V)),T₀⊆T ∧ T.card≤2*T₀.card ∧
      ∀ t∈T₀,(((planeSupport W S).filter (fun a => SharpLogRamsey.Incidence.Incident
        (Projectivization.map W.subtype W.injective_subtype a) t)).card:ℝ)≤
          (100*τ/Nat.card K)*(planeSupport W S).card := by
  let D := fun t : Projectivization K (Module.Dual K V) =>
    (((planeSupport W S).filter (fun a => SharpLogRamsey.Incidence.Incident
      (Projectivization.map W.subtype W.injective_subtype a) t)).card:ℝ)
  let δ := 100*τ/(Nat.card K:ℝ)
  let A := (planeSupport W S).card
  let T₀ := T.filter (fun t => D t≤δ*A)
  let B := T\T₀
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hAp : (0:ℝ)<A := by exact_mod_cast card_pos.mpr hA
  have hsub : T₀⊆T := filter_subset _ _
  have hsum : ∑ t∈T,D t≤(incidenceCount S T:ℝ) := by
    unfold incidenceCount
    push_cast
    exact sum_le_sum (fun t _ => by
      dsimp only [D]
      exact_mod_cast planeSupport_incidence_le W S t)
  have htot : ∑ t∈T,D t≤δ*A*T.card/2 := by
    apply hsum.trans (hs.trans _)
    calc
      _ ≤ τ*(50*A)*T.card/Nat.card K := by gcongr
      _ = _ := by dsimp [δ]; ring
  have hB : δ*A*B.card≤∑ t∈T,D t := by
    calc
      _ = ∑ _t∈B,δ*A := by simp; ring
      _ ≤ ∑ t∈B,D t := by
        apply sum_le_sum
        intro t ht
        have htt := (mem_sdiff.mp ht).1
        have hn := (mem_sdiff.mp ht).2
        exact (lt_of_not_ge (fun hh => hn (mem_filter.mpr ⟨htt,hh⟩))).le
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (by intros; dsimp [D]; positivity)
  have hc : B.card+T₀.card=T.card := by exact card_sdiff_add_card_eq_card hsub
  have hbr : (B.card:ℝ)≤(T.card:ℝ)/2 := by
    have hp := mul_pos hδ hAp
    nlinarith [hB.trans htot]
  refine ⟨T₀,hsub,?_,fun t ht => (mem_filter.mp ht).2⟩
  have hc' : (B.card:ℝ)+T₀.card=T.card := by exact_mod_cast hc
  have := (show (T.card:ℝ)≤2*T₀.card by linarith)
  exact_mod_cast this

theorem heavy_reduction (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (hT : T.Nonempty) (hTU : T⊆U) (τ b : ℝ)
    (hτ : 0<τ) (hτsmall : 100*τ/(Nat.card K:ℝ)<1)
    (hheavy : (S.card:ℝ)/50≤(S∩planePoints W).card)
    (hprod : (Nat.card K:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card)
    (hs : (incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K) :
    ∃ (h : ℕ) (T₁ U₁ : Finset (Projectivization K (Module.Dual K W))),
      1≤h ∧ h≤Nat.card K ∧ T₁.Nonempty ∧ T₁⊆U₁ ∧ h*U₁.card≤U.card ∧
      (T.card:ℝ)≤4*h*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ) ∧
      (∀ t∈T₁,(((planeSupport W S).filter (fun a => SharpLogRamsey.Incidence.Incident a t)).card:ℝ)≤
        (100*τ/Nat.card K)*(planeSupport W S).card) ∧
      (Nat.card K:ℝ)^3*exp (-b)≤
        200*(Nat.log 2 (Nat.card K)+1:ℕ)*(planeSupport W S).card*(T₁.card:ℝ) ∧
      U₁=MultiplicityClass.domain (U.subtype (· ≠ center W hW)) (restrict W hW) h := by
  have hAp : (0:ℝ)<(planeSupport W S).card := by
    rw [planeSupport_card]
    exact (div_pos (by exact_mod_cast card_pos.mpr hS) (by norm_num)).trans_le hheavy
  have hA : (planeSupport W S).Nonempty := card_pos.mp (by exact_mod_cast hAp)
  have hh : (S.card:ℝ)≤50*(planeSupport W S).card := by rw [planeSupport_card]; linarith
  obtain ⟨T₀,hsub,hhalf,hsp⟩ := heavy_half W S T τ hτ hA hh hs
  have ht₀ : T₀.Nonempty := card_pos.mp (by have := card_pos.mpr hT; omega)
  obtain ⟨h,T₁,U₁,hh1,hhq,ht₁,htu,hcap,hsize,hsp₁,he⟩ :=
    sparse_restriction_class W hW (planeSupport W S) hA T₀ U ht₀ (hsub.trans hTU)
      (100*τ/Nat.card K) hτsmall hsp
  have hhalf' : (T.card:ℝ)≤2*T₀.card := by exact_mod_cast hhalf
  have hsize' : (T.card:ℝ)≤4*h*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ) := by linarith
  refine ⟨h,T₁,U₁,hh1,hhq,ht₁,htu,hcap,hsize',hsp₁,?_,he⟩
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hsize'' : (T.card:ℝ)≤4*(Nat.card K)*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ) := by
    apply hsize'.trans
    gcongr
  have hpr : (Nat.card K:ℝ)^4*exp (-b)≤
      200*(Nat.card K)*(Nat.log 2 (Nat.card K)+1:ℕ)*(planeSupport W S).card*(T₁.card:ℝ) := by
    apply hprod.trans
    calc
      _ ≤ (50*(planeSupport W S).card)*(4*(Nat.card K)*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ)) :=
        mul_le_mul hh hsize'' (by positivity) (by positivity)
      _ = _ := by ring
  nlinarith

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_EnumeratedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DescriptionEnumeration
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*}

lemma choose_exp_bound {N n : ℕ} (hn : 0<n) :
    (N.choose n:ℝ) ≤ exp (n*(log ((N:ℝ)/n)+1)) := by
  by_cases hN : N=0
  · subst N
    rw [Nat.choose_eq_zero_of_lt hn]
    simp only [Nat.cast_zero]
    exact (exp_pos _).le
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hN' : (0:ℝ)<N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hfact : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have he := Real.pow_div_factorial_le_exp (n:ℝ) (show (0:ℝ)≤n by positivity) n
  have hf : (1:ℝ)/n.factorial≤exp n/(n:ℝ)^n := by
    apply (div_le_div_iff₀ hfact (pow_pos hn' n)).mpr
    have hh := (div_le_iff₀ hfact).mp he
    simpa only [one_mul] using hh
  calc
    (N.choose n:ℝ) ≤ (N:ℝ)^n/n.factorial := Nat.choose_le_pow_div n N
    _ ≤ (N:ℝ)^n*(exp n/(n:ℝ)^n) := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hf (pow_nonneg hN'.le n)
    _ = exp n*((N:ℝ)/n)^n := by rw [div_pow]; ring
    _ = exp (n*(log ((N:ℝ)/n)+1)) := by
      rw [mul_add,mul_one,exp_add,exp_nat_mul,exp_log (div_pos hN' hn')]
      ring

theorem public_cover (U : Finset α) (n : ℕ) (hn : 0<n) (hnu : n≤U.card) :
    let caps := U.powersetCard n
    (∀ W∈caps,W⊆U ∧ W.card=n) ∧
    (∀ S,S⊆U → S.card=n → ∃ W∈caps,S∩W=S) ∧
    log ((caps.card:ℝ)+1)≤log 2+n*(log ((U.card:ℝ)/n)+1) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro W hW
    exact mem_powersetCard.mp hW
  · intro S hSU hSn
    exact ⟨S,mem_powersetCard.mpr ⟨hSU,hSn⟩,inter_self S⟩
  · rw [card_powersetCard]
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    have hnu' : (n:ℝ)≤U.card := by exact_mod_cast hnu
    have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr (by linarith))
    have hb : 0≤(n:ℝ)*(log ((U.card:ℝ)/n)+1) := by positivity
    have h := choose_exp_bound (N:=U.card) hn
    have he := one_le_exp_iff.mpr hb
    have hm : ((U.card.choose n:ℝ)+1)≤2*exp (n*(log ((U.card:ℝ)/n)+1)) := by linarith
    have hl := log_le_log (by positivity : (0:ℝ)<(U.card.choose n:ℝ)+1) hm
    rwa [log_mul (by norm_num) (exp_ne_zero _),log_exp] at hl

end
end SharpLogRamsey.DescriptionEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Classical BigOperators Topology NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarDescription_3
lemma plane_card (hdim : Module.finrank K V=3) :
    (Fintype.card (Projectivization K V):ℝ)=1+Nat.card K+(Nat.card K:ℝ)^2 := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
  norm_num [sum_range_succ]

lemma plane_log_card (hdim : Module.finrank K V=3) :
    log ((Fintype.card (Projectivization K V):ℝ)+1)≤2*Nat.card K ∧
    log ((Fintype.card (Projectivization K V):ℝ)*log 2+1)≤2*Nat.card K := by
  let q : ℝ := Nat.card K
  have hq : 1≤q := by
    dsimp only [q]
    exact_mod_cast (show 1≤Nat.card K from Nat.card_pos (α:=K))
  have hQ : (Fintype.card (Projectivization K V):ℝ)+1≤(q+1)^2 := by
    rw [plane_card hdim]; dsimp [q] at *; nlinarith
  have hlog : log ((q+1)^2)≤2*q := by
    rw [log_pow]
    have hh := log_le_sub_one_of_pos (show 0<q+1 by linarith)
    norm_num only [Nat.cast_ofNat]
    linarith
  have hfirst := (log_le_log (by positivity) hQ).trans hlog
  refine ⟨hfirst,?_⟩
  apply le_trans _ hfirst
  apply log_le_log (by have := log_nonneg (by norm_num : (1:ℝ)≤2); positivity)
  have hh : log 2≤(1:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  nlinarith [show (0:ℝ)≤Fintype.card (Projectivization K V) by positivity]

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarBoth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales Incidence
open scoped Classical BigOperators Topology NNReal
noncomputable section

lemma validation_description_cost {q P d H : ℝ} (hq : 1≤q) (hP : 1≤P)
    (hd : 0≤d) (hH : log (H+1)≤4*q) (h : ℕ) (hh : (h:ℝ)≤20*q*(d+2)+1) :
    2*((h:ℝ)*(6*P+log 2)+log 2+log (H+1))+log 3≤1000*q*P*(d+P) := by
  have hl2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have hl2' : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hl3 : log (3:ℝ)≤2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hh' : (h:ℝ)≤21*q*(d+2) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hh' (show 0≤6*P+log 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (show 6*P+log 2≤7*P by linarith)
    (show 0≤21*q*(d+2) by positivity)
  have hqP : q≤q*P := le_mul_of_one_le_right (by linarith) hP
  have hPP : q*P≤q*P*P := le_mul_of_one_le_right (by positivity) hP
  have hqp : 1≤q*P := one_le_mul_of_one_le_of_one_le hq hP
  have hpos : 0≤q*P*d := by positivity
  nlinarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarBoth_2
lemma plane_pair_log_card (hdim : Module.finrank K V=3) :
    log (((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2+1)≤4*Nat.card K := by
  let A : ℝ := Fintype.card (Projectivization K V)
  let B : ℝ := Fintype.card (Projectivization K (Module.Dual K V))
  have ha : 0≤A := by positivity
  have hb : 0≤B := by positivity
  have hl2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have hl2' : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hbound : (A+B)*log 2+1≤(A+1)*(B+1) := by nlinarith [mul_nonneg ha hb]
  have hh := log_le_log (by positivity : 0<(A+B)*log 2+1) hbound
  rw [log_mul (by positivity) (by positivity)] at hh
  have hA := (plane_log_card hdim).1
  have hB := (plane_log_card (K:=K) (V:=Module.Dual K V) (Subspace.dual_finrank_eq.trans hdim)).1
  change log ((A+B)*log 2+1)≤_
  dsimp only [A,B] at hh
  linarith

theorem dual_description
    (hdim : Module.finrank K V=3) (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ)
    (hn : 0<n) (ht : 0<t) (hnu : n≤U.card) (htu : t≤UT.card)
    (P b τ : ℝ) (hP : 1≤P) (hτ : τ≤1/20000)
    (hprod : (n:ℝ)*t≤2*(Nat.card K:ℝ)^3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (hsize : ∀ W∈descriptions,W⊆UT ∧ (W.card:ℝ)≤t*exp (6*P))
    (hcapture : ∀ T,Input UT t b τ T → ∃ W∈descriptions,(t:ℝ)/2≤(T∩W).card)
    (hlen : log ((descriptions.card:ℝ)+1)≤200*(Nat.card K:ℝ)*P*(log ((UT.card:ℝ)/t)+P)) :
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤2000*(Nat.card K:ℝ)^3/t) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t → t≤n →
        (Nat.card K:ℝ)^3*exp (-b)≤(n:ℝ)*t →
        (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/Nat.card K →
        ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤2000*(Nat.card K:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  let e := ProjectiveDuality.bidual (K:=K) (V:=V)
  have hcard : (U.image e).card=U.card := card_image_of_injective _ e.injective
  have hdim' : Module.finrank K (Module.Dual K V)=0+3 := Subspace.dual_finrank_eq.trans hdim
  obtain ⟨caps,hs,hc,hl⟩ := Validation.extend_cover hdim' descriptions (U.image e) t n ht hn
    (by rwa [hcard]) (6*P) (by linarith) (fun W hW => (hsize W hW).2)
    (by simpa only [Nat.zero_add,mul_comm] using hprod)
  let out := caps.image (fun W => W.image e.symm)
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (show 1≤Nat.card K from Nat.card_pos (α:=K))
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr (by simpa only [one_mul] using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hdT : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr (by simpa only [one_mul] using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  refine ⟨out,?_,?_,?_⟩
  · intro W hW
    obtain ⟨F,hF,rfl⟩ := mem_image.mp hW
    obtain ⟨hFU,hsizeF⟩ := hs F hF
    have hp := ProjectiveDuality.pullback_cover e U ∅ F hFU
    exact ⟨hp.1,by rw [hp.2.1]; exact hsizeF⟩
  · intro S T hSU hSn hTU hTt htn hprodlo hsp
    have hS : S.Nonempty := card_pos.mp (by omega)
    have hinc : incidenceCount T (S.image e)=incidenceCount S T :=
      ProjectiveDuality.incidenceCount_bidual S T
    have hcS : (S.image e).card=n := (card_image_of_injective _ e.injective).trans hSn
    have hin : Input UT t b τ T := by
      refine ⟨hTU,hTt,S.image e,hS.image _,?_,?_,?_⟩
      · rw [hTt,hcS]; exact htn
      · rw [hTt,hcS]; nlinarith only [hprodlo]
      · rw [hinc,hTt,hcS]
        convert hsp using 1
        all_goals try with_reducible_and_instances rfl
        ring
    obtain ⟨W,hW,hcap⟩ := hcapture T hin
    have hsp' : (incidenceCount T (S.image e):ℝ)≤(t:ℝ)*n/(20000*Nat.card K) := by
      rw [hinc]
      apply hsp.trans
      have hh := mul_le_mul_of_nonneg_right hτ (show 0≤(n:ℝ)*t/(Nat.card K:ℝ) by positivity)
      convert hh using 1 <;> ring
    obtain ⟨F,hF,hcapF⟩ := hc T (S.image e) hTt (image_subset_image hSU) hcS hsp' ⟨W,hW,hcap⟩
    obtain ⟨hFU,_⟩ := hs F hF
    have hp := ProjectiveDuality.pullback_cover e U S F hFU
    refine ⟨F.image e.symm,mem_image.mpr ⟨F,hF,rfl⟩,?_⟩
    rw [hp.2.2]
    nlinarith
  · have hbound := hl
    rw [hcard] at hbound
    have hh : (Validation.scheduleLength (Nat.card K) U.card n:ℝ)≤
        20*(Nat.card K:ℝ)*(log ((U.card:ℝ)/n)+2)+1 := by
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hcost := validation_description_cost hq hP hd
      (plane_pair_log_card (K:=K) (V:=Module.Dual K V) hdim')
      (Validation.scheduleLength (Nat.card K) U.card n) hh
    have hc' : (out.card:ℝ) ≤ caps.card := by exact_mod_cast card_image_le (s:=caps) (f:=fun W => W.image e.symm)
    have hout : log ((out.card:ℝ)+1)≤log ((caps.card:ℝ)+1) := log_le_log (by positivity) (by linarith)
    apply hout.trans (hbound.trans _)
    have hpos1 : 0≤(Nat.card K:ℝ)*P*log ((U.card:ℝ)/n) := by positivity
    have hpos2 : 0≤(Nat.card K:ℝ)*P*log ((UT.card:ℝ)/t) := by positivity
    have hpositive : 0≤(Nat.card K:ℝ)*P^2 := by positivity
    nlinarith only [hlen,hcost,hpos1,hpos2,hpositive]

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales Incidence
open scoped Classical BigOperators Topology NNReal
noncomputable section

theorem complete_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ D R,Admissible σ η D R → exp σ=(Nat.card K:ℝ) → Module.finrank K V=3 →
    ∀ (U : Finset (Projectivization K V))
      (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    (Nat.card K:ℝ)^3*exp (-b)≤(n:ℝ)*t → (n:ℝ)*t≤2*(Nat.card K:ℝ)^3 →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/Nat.card K →
        ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤2000*(Nat.card K:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [full_source_cover_uniform hη C hC,
    eventually_uniform_L hη (eventually_ge_atTop (2000:ℝ)),eventually_uniform_R hη 1,
    eventually_training_loss hη C 1 (by linarith) (by norm_num),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20000)),
    eventually_ge_atTop (1:ℝ)] with σ hcover hL hR hbsmall ht hσ
  intro K V _ _ _ _ _ D R had hex hdim U UT n t b τ hn ht0 hnu htu hb hbu hτ hτu hprodlo hprodhi
  let P := scaleP σ η D R
  have hL' := hL D R had
  have hR' := hR D R had
  have hLP : scaleL σ η D≤P := le_mul_of_one_le_right (by linarith) hR'
  have hP : 2000≤P := hL'.trans hLP
  have hτsmall : τ≤1/20000 := hτu.trans ht.le
  have hbP : b≤P := by
    have hh := hbsmall D R had b 0 hbu (by positivity)
    simp only [mul_zero,add_zero,one_mul] at hh
    exact hh.trans hLP
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht0
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr
    (by simpa only [one_mul] using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hdT : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr
    (by simpa only [one_mul] using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  by_cases hnt : n≤t
  · obtain ⟨caps,hs,hc,hl⟩ := hcover K V D R had hex hdim U n b τ hn hnu hb hbu hτ hτu
    refine ⟨caps,hs,?_,hl.trans ?_⟩
    · intro S T hSU hSn _ hTt hsp
      apply hc S
      refine ⟨hSU,hSn,T,card_pos.mp (by omega),?_,?_,?_⟩
      · rw [hSn,hTt]; exact hnt
      · rwa [hSn,hTt]
      · rwa [hSn,hTt]
    · have hq : (0:ℝ)≤Nat.card K := by positivity
      have hpos : 0≤(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+P) := by positivity
      have hposT : 0≤(Nat.card K:ℝ)*P*log ((UT.card:ℝ)/t) := by positivity
      nlinarith only [hpos,hposT]
  · have htn : t≤n := (le_of_not_ge hnt)
    have hdim' : Module.finrank K (Module.Dual K V)=3 := Subspace.dual_finrank_eq.trans hdim
    obtain ⟨desc,hs,hc,hl⟩ := hcover K (Module.Dual K V) D R had hex hdim' UT t b τ ht0 htu hb hbu hτ hτu
    obtain ⟨caps,hsize,hcapture,hlen⟩ := dual_description hdim U UT n t hn ht0 hnu htu
      P b τ (by linarith) hτsmall hprodhi desc hs hc hl
    refine ⟨caps,?_,?_,hlen⟩
    · intro W hW
      obtain ⟨hWU,hw⟩ := hsize W hW
      refine ⟨hWU,hw.trans ?_⟩
      have he : (Nat.card K:ℝ)^3≤(n:ℝ)*t*exp b := by
        have hh := mul_le_mul_of_nonneg_right hprodlo (exp_pos b).le
        have heq : exp (-b)*exp b=1 := by rw [←exp_add,neg_add_cancel,exp_zero]
        nlinarith only [hh,show (Nat.card K:ℝ)^3*exp (-b)*exp b=(Nat.card K:ℝ)^3 by rw [mul_assoc,heq,mul_one]]
      have hsize' : 2000*(Nat.card K:ℝ)^3/t≤2000*(n:ℝ)*exp b := by
        apply (div_le_iff₀ ht').mpr
        nlinarith only [he]
      apply hsize'.trans
      have hlog : log (2000:ℝ)≤1999 := by
        have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2000); linarith
      have hexp : 2000*exp b≤exp (6*P) := by
        rw [←exp_log (by norm_num : (0:ℝ)<2000),←exp_add]
        apply exp_le_exp.mpr
        linarith
      nlinarith only [mul_le_mul_of_nonneg_left hexp hn'.le]
    · intro S T hSU hSn hTU hTt hsp
      exact hcapture S T hSU hSn hTU hTt htn hprodlo hsp

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_HeavyPlaneCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset Real Filter SourceScales Incidence PreparedProjectiveGeometry
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedHeavyPlaneCover_2_r99179f_1 : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedHeavyPlaneCover_3_r99179f_1 (W : Submodule K V) : Fintype (Projectivization K W) := by
  let : Finite W := Module.finite_of_finite K
  exact Fintype.ofFinite _
lemma planeSupport_mono (W : Submodule K V) {S U : Finset (Projectivization K V)}
    (h : S⊆U) : planeSupport W S⊆planeSupport W U := by
  intro a ha
  exact mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp ha).2⟩

lemma plane_cap_lift (W : Submodule K V) (U S : Finset (Projectivization K V))
    (E : Finset (Projectivization K W)) (hE : E⊆planeSupport W U) :
    E.image (Projectivization.map W.subtype W.injective_subtype)⊆U ∧
    (E.image (Projectivization.map W.subtype W.injective_subtype)).card=E.card ∧
    (S∩E.image (Projectivization.map W.subtype W.injective_subtype)).card=
      (planeSupport W S∩E).card := by
  have hi := Projectivization.map_injective W.subtype W.injective_subtype
  refine ⟨?_,card_image_of_injective _ hi,?_⟩
  · intro a ha
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    exact (mem_filter.mp (hE hx)).2
  · have he : (planeSupport W S∩E).image (Projectivization.map W.subtype W.injective_subtype)=
        S∩E.image (Projectivization.map W.subtype W.injective_subtype) := by
      ext a
      constructor
      · intro ha
        obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
        exact mem_inter.mpr ⟨(mem_filter.mp (mem_inter.mp hx).1).2,
          mem_image.mpr ⟨x,(mem_inter.mp hx).2,rfl⟩⟩
      · intro ha
        obtain ⟨ha,hE⟩ := mem_inter.mp ha
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hE
        exact mem_image.mpr ⟨x,mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ha⟩,hx⟩,rfl⟩
    rw [←he,card_image_of_injective _ hi]

lemma heavy_domain_gaps (N M N₁ M₁ n t a u h L : ℝ)
    (hN : 0<N) (hM : 0<M) (hn : 0<n) (ht : 0<t)
    (ha : 0<a) (hu : 0<u) (_hh : 0<h) (hL : 0<L)
    (hN₁ : 0<N₁) (hM₁ : 0<M₁) (hcap : N₁≤N) (hheavy : n≤50*a)
    (hdom : h*M₁≤M) (hsize : t≤4*h*L*u) :
    log (N₁/a)≤log (N/n)+log 50 ∧
    log (M₁/u)≤log (M/t)+log (4*L) := by
  constructor
  · rw [←log_mul (div_pos hN hn).ne' (by norm_num : (50:ℝ)≠0)]
    apply log_le_log (div_pos hN₁ ha)
    apply (div_le_iff₀ ha).mpr
    have hratio : N≤N/n*(50*a) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hn).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hheavy hN.le]
    nlinarith
  · rw [←log_mul (div_pos hM ht).ne' (mul_pos (by norm_num) hL).ne']
    apply log_le_log (div_pos hM₁ hu)
    apply (div_le_iff₀ hu).mpr
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (le_div_iff₀ ht).mpr
    have hm := mul_le_mul_of_nonneg_left hsize hM₁.le
    have hd := mul_le_mul_of_nonneg_right hdom (by positivity : 0≤4*L*u)
    nlinarith

theorem fixed_heavy_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ D R,Admissible σ η D R → exp σ=(Nat.card K:ℝ) →
    ∀ (W : Submodule K V),Module.finrank K W=3 →
    ∀ (U : Finset (Projectivization K V))
      (U₁ : Finset (Projectivization K (Module.Dual K W))) (n a t : ℕ) (b τ : ℝ),
    0<a → 0<t → a≤n → n≤50*a → a≤(planeSupport W U).card → t≤U₁.card →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    (Nat.card K:ℝ)^3*exp (-b)≤(a:ℝ)*t → (a:ℝ)*t≤2*(Nat.card K:ℝ)^3 →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ E∈caps,E⊆U ∧ (E.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → (planeSupport W S).card=a → T⊆U₁ → T.card=t →
        (incidenceCount (planeSupport W S) T:ℝ)≤τ*(a:ℝ)*t/Nat.card K →
        ∃ E∈caps,(n:ℝ)/100≤(S∩E).card) ∧
      log ((caps.card:ℝ)+1)≤2000*(Nat.card K:ℝ)*P*
        (log (((planeSupport W U).card:ℝ)/a)+log ((U₁.card:ℝ)/t)+P) := by
  filter_upwards [PlanarLearning.complete_cover hη C hC] with σ hcover
  intro K V _ _ _ _ _ D R had hex W hW U U₁ n a t b τ ha ht han hna hau htu hb hbu hτ hτu hlo hhi
  obtain ⟨caps,hs,hc,hl⟩ := hcover K W D R had hex hW (planeSupport W U) U₁ a t b τ
    ha ht hau htu hb hbu hτ hτu hlo hhi
  let f := fun E : Finset (Projectivization K W) =>
    E.image (Projectivization.map W.subtype W.injective_subtype)
  refine ⟨caps.image f,?_,?_,?_⟩
  · intro E hE
    obtain ⟨E₀,hE₀,rfl⟩ := mem_image.mp hE
    obtain ⟨hEU,hsize⟩ := hs E₀ hE₀
    obtain ⟨hsub,hcard,_⟩ := plane_cap_lift W U ∅ E₀ hEU
    refine ⟨hsub,?_⟩
    dsimp only [f]
    rw [hcard]
    exact hsize.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast han) (exp_pos _).le)
  · intro S T hSU _ hSa hTU hTt hsp
    obtain ⟨E,hE,hcap⟩ := hc (planeSupport W S) T (planeSupport_mono W hSU) hSa hTU hTt hsp
    refine ⟨f E,mem_image.mpr ⟨E,hE,rfl⟩,?_⟩
    obtain ⟨_,_,he⟩ := plane_cap_lift W U S E (hs E hE).1
    dsimp only [f]
    rw [he]
    have hna' : (n:ℝ)≤50*a := by exact_mod_cast hna
    linarith
  · apply le_trans _ hl
    apply log_le_log (by positivity)
    have hh := card_image_le (s:=caps) (f:=f)
    exact_mod_cast Nat.add_le_add_right hh 1

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_HeavyPlanePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset Real Filter SourceScales Incidence PreparedProjectiveGeometry
open scoped Classical BigOperators Topology
noncomputable section

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
attribute [local instance] OAI.SharpLogRamsey.HeavyPlaneRestriction.flat_JoinedHeavyPlanePublic_3
lemma header_card (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (n m : ℕ) :
    Nat.card (HeavyHeaders K V n m)≤Nat.card (Submodule K V)*(Nat.card K+1)*(n+1)*(m+1) := by
  dsimp only [HeavyHeaders]
  simp only [Nat.card_prod,Nat.card_fin]
  simp only [←mul_assoc]
  gcongr
  exact Nat.card_le_card_of_injective (fun x : {W : Submodule K V // Module.finrank K W=3} => x.val)
    Subtype.val_injective

theorem heavy_families {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ D R,Admissible σ η D R → exp σ=(Nat.card K:ℝ) → ∀ hV : Module.finrank K V=4,
    ∀ (U : Finset (Projectivization K V))
      (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    let E := 4000*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)
    ∃ fam : HeavyHeaders K V n UT.card → Finset (Finset (Projectivization K V)),
      ∀ j, (∀ W∈fam j,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,HeaderValid hV U UT n t (Nat.log 2 (Nat.card K)+1:ℕ)
          (b+log (200*(Nat.log 2 (Nat.card K)+1:ℕ))) j →
        S⊆U → S.card=n → (planeSupport (headerPlane j) S).card=j.2.2.1.val →
        T⊆headerDomain hV UT j → T.card=j.2.2.2.val →
        (incidenceCount (planeSupport (headerPlane j) S) T:ℝ)≤100*τ*(j.2.2.1.val:ℝ)*j.2.2.2.val/Nat.card K →
        ∃ W∈fam j,(n:ℝ)/100≤(S∩W).card) ∧ ((fam j).card:ℝ)≤exp E := by
  have hC' : 1≤101*C+2 := by linarith
  have htiny : Tendsto (fun σ : ℝ => 100*C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul (100*C)
  filter_upwards [fixed_heavy_cover hη (101*C+2) hC',eventually_heavy_loss hη,
    htiny.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20)),
    eventually_ge_atTop (1:ℝ)] with σ hcover hloss htiny hσ
  intro K V _ _ _ _ _ D R had hex hV U UT n t b τ hn ht hnu htu hb hbu hτ hτu
  let P := scaleP σ η D R
  let E := 4000*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)
  let L : ℝ := (Nat.log 2 (Nat.card K)+1:ℕ)
  let b₁ := b+log (200*L)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hU : (0:ℝ)<U.card := hn'.trans_le (by exact_mod_cast hnu)
  have hUT : (0:ℝ)<UT.card := ht'.trans_le (by exact_mod_cast htu)
  have hL : 0<L := by dsimp [L]; positivity
  have hP : 0<P := by
    have hh := (scale_bounds hσ hη had).2.1
    exact (rpow_pos_of_pos (by linarith : 0<σ) _).trans_le hh
  obtain ⟨hl0,hlK,hlP⟩ := hloss (Nat.card K) (Finite.card_pos) hex D R had
  change 0≤log (200*L) at hl0
  change log (200*L)≤ scaleKstar σ η D at hlK
  change log 50+log (4*L)≤P at hlP
  have hb₁ : 0≤b₁ := add_nonneg hb hl0
  have hb₁U : b₁≤(101*C+2)*scaleKstar σ η D := by
    have hK := hl0.trans hlK
    dsimp [b₁]
    nlinarith
  have htau : 100*τ≤1/20 := by
    have hp : 0≤σ^(-100*beta η) := rpow_nonneg (by linarith) _
    nlinarith
  have htauU : 100*τ≤(101*C+2)*σ^(-100*beta η) := by
    have hp : 0≤σ^(-100*beta η) := rpow_nonneg (by linarith) _
    nlinarith
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr (by simpa using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hdT : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr (by simpa using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  let J := HeavyHeaders K V n UT.card
  let plane (j : J) := headerPlane j
  have plane_rank (j : J) : Module.finrank K (plane j)=3 := header_rank j
  let dom (j : J) := headerDomain hV UT j
  let valid (j : J) := HeaderValid hV U UT n t L b₁ j
  have each (j : J) : ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,valid j → S⊆U → S.card=n → (planeSupport (plane j) S).card=j.2.2.1.val →
        T⊆dom j → T.card=j.2.2.2.val →
        (incidenceCount (planeSupport (plane j) S) T:ℝ)≤100*τ*(j.2.2.1.val:ℝ)*j.2.2.2.val/Nat.card K →
        ∃ W∈caps,(n:ℝ)/100≤(S∩W).card) ∧ (caps.card:ℝ)≤exp E := by
    by_cases hv : valid j
    · obtain ⟨hj,ha,hu,hheavy,hau,htu₁,hdom,hsize,hlo,hhi⟩ := hv
      obtain ⟨caps,hs,hc,hl⟩ := hcover K V D R had hex (plane j) (plane_rank j) U (dom j) n
        j.2.2.1.val j.2.2.2.val b₁ (100*τ) ha hu (Nat.le_of_lt_succ j.2.2.1.isLt) hheavy
        hau htu₁ hb₁ hb₁U (by positivity) htauU hlo hhi
      have hA : (0:ℝ)<(planeSupport (plane j) U).card := by exact_mod_cast (ha.trans_le hau)
      have hB : (0:ℝ)<(dom j).card := by exact_mod_cast (hu.trans_le htu₁)
      have hsmall : (planeSupport (plane j) U).card≤U.card := by
        rw [planeSupport_card]; exact card_le_card inter_subset_left
      obtain ⟨hd₁,hd₂⟩ := heavy_domain_gaps U.card UT.card (planeSupport (plane j) U).card (dom j).card
        n t j.2.2.1.val j.2.2.2.val j.2.1.val L hU hUT hn' ht' (by exact_mod_cast ha)
        (by exact_mod_cast hu) (by exact_mod_cast hj) hL hA hB (by exact_mod_cast hsmall)
        (by exact_mod_cast hheavy) (by exact_mod_cast hdom) hsize
      have hlen : log ((caps.card:ℝ)+1)≤E := by
        apply hl.trans
        have hqP : 0≤(Nat.card K:ℝ)*P := mul_nonneg hq.le hP.le
        have hh := mul_le_mul_of_nonneg_left (add_le_add hd₁ hd₂) hqP
        have hll := mul_le_mul_of_nonneg_left hlP hqP
        have hadd := mul_nonneg hqP (add_nonneg hd hdT)
        dsimp only [E]
        nlinarith
      refine ⟨caps,hs,fun S T _ => hc S T,?_⟩
      have he := exp_le_exp.mpr hlen
      rw [exp_log (by positivity)] at he
      linarith
    · refine ⟨∅,by simp,?_,?_⟩
      · intro S T hj; exact (hv hj).elim
      · simp only [card_empty,Nat.cast_zero]; exact (exp_pos _).le
  choose fam hf using each
  exact ⟨fam,hf⟩

attribute [local instance] OAI.SharpLogRamsey.HeavyPlaneRestriction.flat_JoinedHeavyPlanePublic_2
attribute [local instance] OAI.SharpLogRamsey.HeavyPlaneRestriction.flat_JoinedHeavyPlanePublic_4
theorem public_heavy_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ D R,Admissible σ η D R → exp σ=(Nat.card K:ℝ) → Module.finrank K V=4 →
    ∀ (U : Finset (Projectivization K V))
      (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    let E := 4000*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (Nat.card K:ℝ)^4*exp (-b)≤(n:ℝ)*t →
        (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/Nat.card K →
        (∃ W : Submodule K V,Module.finrank K W=3 ∧ (n:ℝ)/50≤(S∩planePoints W).card) →
        ∃ W∈caps,(n:ℝ)/100≤(S∩W).card) ∧
      (caps.card:ℝ)≤(Nat.card (Submodule K V):ℝ)*(Nat.card K+1:ℕ)*(n+1:ℕ)*(UT.card+1:ℕ)*exp E := by
  have htiny : Tendsto (fun σ : ℝ => 100*C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul (100*C)
  filter_upwards [heavy_families hη C hC,
    htiny.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20))] with σ hf htiny
  intro K V _ _ _ _ _ D R had hex hV U UT n t b τ hn ht hnu htu hb hbu hτ hτu
  let P := scaleP σ η D R
  let E := 4000*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)
  let L : ℝ := (Nat.log 2 (Nat.card K)+1:ℕ)
  let b₁ := b+log (200*L)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hL : 0<L := by dsimp [L]; positivity
  have htau : 100*τ≤1/20 := by linarith
  let J := HeavyHeaders K V n UT.card
  let plane (j : J) := headerPlane j
  let dom (j : J) := headerDomain hV UT j
  let valid (j : J) := HeaderValid hV U UT n t L b₁ j
  obtain ⟨fam,hfam⟩ := hf K V D R had hex hV U UT n t b τ hn ht hnu htu hb hbu hτ hτu
  have hsize (j : J) := (hfam j).1
  have hcapture (j : J) := (hfam j).2.1
  have hcount (j : J) := (hfam j).2.2
  let caps := (univ : Finset J).biUnion fam
  refine ⟨caps,?_,?_,?_⟩
  · intro W hW
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hW
    exact hsize j W hj
  · intro S T hSU hSn hTU hTt hprod hsparse hheavy
    obtain ⟨W,hW,hheavy⟩ := hheavy
    have hcodim : Module.finrank K W+1=Module.finrank K V := by rw [hW,hV]
    have hτone : 100*τ/(Nat.card K:ℝ)<1 := by
      apply (div_lt_iff₀ hq).mpr
      have hq2 : (2:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)
      linarith
    obtain ⟨h,T₁,U₁,hh1,hhq,hT₁,hT₁U,hU₁,hsize₁,hsp₁,hprod₁,hdom₁⟩ :=
      heavy_reduction W hcodim S (card_pos.mp (by omega)) T UT (card_pos.mp (by omega)) hTU τ b
        hτ hτone (by rwa [hSn]) (by rwa [hSn,hTt]) (by rwa [hSn,hTt])
    have ha : (planeSupport W S).card≤n := by rw [planeSupport_card,←hSn]; exact card_le_card inter_subset_left
    have hTUcard : T₁.card≤UT.card := by
      have hh := card_le_card hT₁U
      exact hh.trans ((Nat.le_mul_of_pos_left _ hh1).trans hU₁)
    let j : J := (⟨W,hW⟩,⟨h,by omega⟩,⟨(planeSupport W S).card,by omega⟩,⟨T₁.card,by omega⟩)
    have hpj : headerPlane j=W := rfl
    have hdj : headerDomain hV UT j=U₁ := hdom₁.symm
    have hsp : (incidenceCount (planeSupport W S) T₁:ℝ)≤
        100*τ*((planeSupport W S).card:ℝ)*T₁.card/Nat.card K := by
      unfold incidenceCount
      push_cast
      calc
        _ ≤ ∑ _t∈T₁,(100*τ/Nat.card K)*(planeSupport W S).card := sum_le_sum hsp₁
        _ = _ := by simp; ring
    have hsp20 : (incidenceCount (planeSupport W S) T₁:ℝ)≤
        ((planeSupport W S).card:ℝ)*T₁.card/(20*Nat.card K) := by
      apply hsp.trans
      convert mul_le_mul_of_nonneg_right htau
        (by positivity : 0≤((planeSupport W S).card:ℝ)*T₁.card/(Nat.card K:ℝ)) using 1 <;> ring
    have hupper := sparse_product_bound_two (n:=0) (by simpa using hW) (planeSupport W S) T₁ hsp20
    have hlo : (Nat.card K:ℝ)^3*exp (-b₁)≤((planeSupport W S).card:ℝ)*T₁.card := by
      have hexp : exp (-b₁)=exp (-b)/(200*L) := by
        dsimp only [b₁]
        rw [neg_add,exp_add,exp_neg (log (200*L)),exp_log (by positivity)]
        ring
      rw [hexp,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<200*L)).mpr
      dsimp only [L]
      nlinarith [hprod₁]
    have hv : valid j := by
      dsimp only [valid,HeaderValid]
      rw [hdj]
      dsimp only [j,headerPlane]
      refine ⟨by omega,?_,card_pos.mpr hT₁,?_,card_le_card (planeSupport_mono W hSU),
        card_le_card hT₁U,hU₁,?_,hlo,?_⟩
      · have hc := hheavy
        rw [←planeSupport_card] at hc
        have := div_pos hn' (by norm_num : (0:ℝ)<50)
        exact_mod_cast this.trans_le hc
      · rw [←planeSupport_card] at hheavy
        have hh : (n:ℝ)≤50*(planeSupport W S).card := by linarith
        exact_mod_cast hh
      · simpa only [hTt] using hsize₁
      · simpa using hupper
    obtain ⟨E,hE,hcap⟩ := hcapture j S T₁ hv hSU hSn rfl (by rwa [hdj]) rfl (by simpa only [j,headerPlane] using hsp)
    exact ⟨E,mem_biUnion.mpr ⟨j,mem_univ _,hE⟩,hcap⟩
  · have hsum : (caps.card:ℝ)≤∑ j : J,((fam j).card:ℝ) := by exact_mod_cast (card_biUnion_le (s:=(univ:Finset J)) (t:=fam))
    apply hsum.trans
    calc
      _ ≤ ∑ _j : J,exp E := sum_le_sum (fun j _ => hcount j)
      _ = (Fintype.card J:ℝ)*exp E := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        have hh := header_card K V n UT.card
        rw [Nat.card_eq_fintype_card] at hh
        exact_mod_cast hh

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_SourceGridShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real Finset
open scoped Topology BigOperators
noncomputable section

lemma log_grid_bound {n : ℕ} (hn : 0<n) (q : ℝ) (hq : 0<q) (j : ℕ)
    (h : (n:ℝ)≤2*q^j) :
    (Nat.log 2 n+2:ℕ)*Real.log 2≤3*Real.log 2+(j:ℝ)*Real.log q := by
  have hp : (2:ℝ)^(Nat.log 2 n)≤n := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have hl := Real.log_le_log (show (0:ℝ)<2^(Nat.log 2 n) by positivity) (hp.trans h)
  rw [Real.log_pow,Real.log_mul (by norm_num) (pow_ne_zero _ hq.ne'),Real.log_pow] at hl
  push_cast
  linarith

theorem eventually_grid_shape (d : ℕ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℝ) (j n : ℕ),0<q → Real.log q=σ → j≤d →
      0<n → (n:ℝ)≤2*q^j → (Nat.log 2 n+2:ℕ)≤σ^2 := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop ((d:ℝ)/Real.log 2+3)] with
    σ hσ hσ' q j n hq hlog hj hn hN
  have hh := log_grid_bound hn q hq j hN
  rw [hlog] at hh
  have hd : (j:ℝ)≤d := by exact_mod_cast hj
  have hmul : (d:ℝ)+3*Real.log 2≤σ*Real.log 2 := by
    have hab := mul_le_mul_of_nonneg_right hσ' hl.le
    rw [add_mul,div_mul_cancel₀ _ hl.ne'] at hab
    exact hab
  have hmul' := mul_le_mul_of_nonneg_right hmul (show 0≤σ by linarith)
  have hl' := mul_le_mul_of_nonneg_left hσ (show 0≤3*Real.log 2 by positivity)
  have hd' := mul_le_mul_of_nonneg_right hd (show 0≤σ by linarith)
  apply (mul_le_mul_iff_left₀ hl).mp
  nlinarith

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real Filter SourceScales
open scoped Topology NNReal
noncomputable section

lemma Budget.mono_grid {σ P : ℝ} {L : ℝ≥0} {R N M p h : ℕ}
    (hb : Budget σ P L R N p h) (hm : M≤N) : Budget σ P L R M p h := by
  have hm' : (M:ℝ)≤N := by exact_mod_cast hm
  have hP : 0≤P := le_trans (by norm_num) hb.large
  refine { hb with sum := ?_, cert := ?_, shift := ?_ }
  · apply le_trans _ hb.sum
    gcongr
  · apply le_trans _ hb.cert
    unfold MomentBudgetBridge.certificateOverhead
    gcongr
  · apply le_trans _ hb.shift
    unfold MomentBudgetBridge.shiftOverhead
    gcongr

theorem eventually_bounded_budget {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R N : ℕ),Admissible σ η D R → (N:ℝ)≤σ^2 →
      ∃ p h : ℕ,(p:ℝ)≤σ^2 ∧ Budget σ (scaleP σ η D R) (Real.toNNReal (scaleL σ η D)) R N p h := by
  filter_upwards [eventually_enumeration_budgets hη,
    eventually_pencil_scalar_budgets hη 400000,eventually_P_le_linear hη (1/12) (by norm_num),
    eventually_uniform_L hη (eventually_ge_atTop (100000000000000:ℝ)),
    eventually_uniform_R hη 400,PlanarLearning.eventually_schedule hη,eventually_ge_atTop (10002:ℝ)]
    with σ he hp hu hl hr hs hσ D R N had hN
  let L := scaleL σ η D
  let P := scaleP σ η D R
  have hL : 100000000000000≤L := hl D R had
  have hR : (400:ℝ)≤R := hr D R had
  have hL0 : 0≤L := by linarith
  have hLP : L≤P := by change L≤L*R; nlinarith
  have hP0 : 0<P := by linarith
  obtain ⟨p,hp0,hpe,hpl,hpu⟩ := PlanarLearning.even_order (by linarith : 0<σ) hP0
  obtain ⟨hLa,hcert,hshift,hpb,hps,h,hh,hR',hhs,hhr⟩ := he D R p N had hpu hN
  obtain ⟨hdiag,hpow,hsum,htwo,hvar⟩ := hp D R N had hN
  have hlu : (Real.toNNReal L:ℝ)=L := Real.coe_toNNReal _ hL0
  have hPu : P≤σ/12 := by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hu D R had
  have hB : 2*exp (6*P)≤exp σ := by
    have h2 : 2≤exp (σ-6*P) := by have := add_one_le_exp (σ-6*P); linarith
    calc
      _ ≤ exp (σ-6*P)*exp (6*P) := mul_le_mul_of_nonneg_right h2 (exp_pos _).le
      _ = _ := by rw [←exp_add]; congr 1; ring
  change ∃ p h : ℕ,(p:ℝ)≤σ^2 ∧ Budget σ P (Real.toNNReal L) R N p h
  refine ⟨p,h,moment_order_le hσ (by linarith) hpu,?_⟩
  constructor
  · linarith
  · exact hL.trans hLP
  · linarith
  · exact hB
  · rw [hlu]; rfl
  · rw [hlu]; linarith
  · exact hR'
  · exact hp0
  · exact hpe
  · exact hpl
  · simpa only [hlu] using hs D R had
  · exact hdiag
  · simpa only [hlu] using hpow
  · simpa only [hlu] using hsum
  · exact htwo
  · simpa only [hlu] using hvar
  · exact hcert
  · exact hshift
  · exact hpb
  · exact hps
  · exact hh
  · exact hhs
  · exact hhr

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialSourceCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales SpatialLearning DescriptionHeaders PreparedProjectiveGeometry
open scoped Classical BigOperators Topology NNReal
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialSourceCover_1
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialSourceCover_2
theorem source_cover {η : ℝ} (hη : 0 < η) (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ = (q:ℝ) →
    ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))) (n : ℕ) (b τ : ℝ),
    0 < n → n ≤ U.card → (n:ℝ) ≤ 2*(q:ℝ)^2 → 200*(q:ℝ)*scaleP σ η D R ≤ n →
    0 ≤ b → b ≤ C*scaleKstar σ η D → 0 < τ → τ ≤ C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    let J := ⌈exp (7*σ/10)⌉₊
    let M := ⌈2*(q:ℝ)*P⌉₊
    let H := (Fintype.card (Projectivization (ZMod q) (Fin 4 → ZMod q)):ℝ)*log 2
    let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
      log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))):ℝ)+1)
    ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))),
      (∀ W ∈ caps, W ⊆ U ∧ (W.card:ℝ) ≤ n*exp (6*P)) ∧
      (∀ (S : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q)))
          (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q)))),
        S ⊆ U → S.card = n → T.Nonempty → S.card ≤ T.card →
        (q:ℝ)^4*exp (-b) ≤ (S.card:ℝ)*T.card →
        (Incidence.incidenceCount S T:ℝ) ≤ τ*(S.card:ℝ)*T.card/q →
        (∃ W : Submodule (ZMod q) (Fin 4 → ZMod q), Module.finrank (ZMod q) W = 3 ∧
          (n:ℝ)/50 ≤ (S ∩ planePoints W).card) ∨
        (∃ W ∈ caps, (n:ℝ)/4 ≤ (S ∩ W).card)) ∧
      (caps.card:ℝ) ≤ (n+1:ℕ)*(J+1:ℕ)*
        (((Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q))*(n+1)+1:ℕ):ℝ)^J)*exp E := by
  have hβ := beta_pos hη
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 100*beta η)).const_mul C
  have hK : ∀ᶠ σ : ℝ in atTop, (1:ℝ) ≤ σ^(7*beta η) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with σ hσ
    exact one_le_rpow hσ (by positivity)
  filter_upwards [actual_cover (beta η) (log 2) hβ,
    eventually_bounded_budget hη,eventually_grid_shape 2,
    eventually_P_le_linear hη (1/40) (by norm_num),
    eventually_training_loss hη (2*C+4) (1/1000000) (by linarith) (by norm_num),
    eventually_exceptional_training hη (2*C+4) (by linarith),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/40)),
    hK,eventually_ge_atTop (1:ℝ)] with σ hcover hbud hgrid hPu hloss herr hτsmall hK hσ
  intro q _ hq hx D R had U n b τ hn hnu hnupper hnlarge hb hbu hτ hτu
  let P := scaleP σ η D R
  let L := Real.toNNReal (scaleL σ η D)
  let g := log (n:ℝ)-3*σ/2
  let J := ⌈exp (7*σ/10)⌉₊
  let M := ⌈2*(q:ℝ)*P⌉₊
  have hσ0 : 0 < σ := by linarith
  have hqp : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hxlog : log (q:ℝ) = σ := by rw [←hx,log_exp]
  have hNgrid : ((Nat.log 2 n+2:ℕ):ℝ) ≤ σ^2 := hgrid q 2 n hqp hxlog le_rfl hn hnupper
  obtain ⟨p,h,hpupper,hbudget⟩ := hbud D R (Nat.log 2 n+2) had hNgrid
  have hP0 : 0 ≤ P := by have := hbudget.large; dsimp [P]; linarith
  have hL0 : 0 ≤ scaleL σ η D := (L_pos hσ0 had).le
  have hLP : scaleL σ η D ≤ P := by
    have hR : (1:ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by have := hbudget.Rlarge; omega)
    dsimp [P,scaleP]
    exact le_mul_of_one_le_right hL0 hR
  have hKlow : 1 ≤ scaleKstar σ η D := by
    apply hK.trans
    unfold scaleKstar
    have hh := mul_le_mul_of_nonneg_right had.D_lower (rpow_nonneg hσ0.le (6*beta η))
    rw [←rpow_add hσ0] at hh
    simpa only [show beta η+6*beta η=7*beta η by ring] using hh
  have hb' : b+log 2 ≤ (2*C+4)*scaleKstar σ η D := by
    have hl : log 2 ≤ (2:ℝ) := (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    nlinarith
  have hτ' : 2*τ ≤ (2*C+4)*σ^(-100*beta η) := by
    have hp : 0 ≤ σ^(-100*beta η) := rpow_nonneg hσ0.le _
    nlinarith
  have hl := hloss D R had (b+log 2) (2*τ) hb' hτ'
  have he := herr D R had (b+log 2) (2*τ) hb' hτ'
  have hPg : σ^beta η ≤ P := by
    apply (rpow_le_rpow_of_exponent_le hσ (by linarith : beta η ≤ 9*beta η)).trans
    exact (scale_bounds hσ hη had).1.trans hLP
  have hPupper : P ≤ σ/40 := by
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using hPu D R had
  have hgu : g ≤ σ/2+log 2 := by
    have hh := log_le_log hnp hnupper
    rw [log_mul (by norm_num) (pow_ne_zero _ hqp.ne'),log_pow,hxlog] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [g]
    linarith
  have hgn : (n:ℝ) = exp (3*σ/2+g) := by
    dsimp [g]
    rw [show 3*σ/2+(log (n:ℝ)-3*σ/2)=log (n:ℝ) by ring,exp_log hnp]
  have hJ : exp (σ/2-2*g/15) ≤ J := by
    apply le_trans _ (Nat.le_ceil (exp (7*σ/10)))
    apply exp_le_exp.mpr
    have hh : 0 ≤ log (n:ℝ) := log_nonneg (by exact_mod_cast hn)
    dsimp [g]
    linarith
  have hms : ∀ m, 0 < m → m ≤ n → n ≤ 2*m →
      Budget σ P L R (Nat.log 2 m+2) p h := by
    intro m _ hmn _
    exact hbudget.mono_grid (Nat.add_le_add_right (Nat.log_mono_right hmn) 2)
  have hl' : b+log 2+4*P*τ ≤ P/1000000 := by
    have hm := mul_le_mul_of_nonneg_right hLP (by norm_num : (0:ℝ) ≤ 1/1000000)
    dsimp [P] at *
    nlinarith
  have he' : 50000*exp (-(95/100:ℝ)*(L:ℝ)) ≤ exp (-(b+log 2)-4*P*τ)/800 := by
    dsimp only [L]
    rw [coe_toNNReal _ hL0]
    simpa only [show (2:ℝ)*scaleP σ η D R*(2*τ)=4*P*τ by dsimp [P]; ring] using he
  exact hcover q hq hx U n J P g b τ L R p h M hn hnu hPg hPupper hgu
    hbudget.p_pos hpupper hgn hJ hms hb hτ (hτu.trans hτsmall.le) hnlarge hl' he' (Nat.le_ceil _)

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales
open scoped Classical BigOperators Topology
noncomputable section

lemma spatial_cost {q P d τ H Q : ℝ} {M : ℕ}
    (hq : 1≤q) (hP : 1≤P) (hd : 0≤d) (hτ : τ≤1)
    (hM : (M:ℝ)≤2*q*P+1) (hH : log (H+1)≤4*q) (hQ : log (Q+1)≤4*q) :
    2*((M:ℝ)*(log 2+d)+4*P*τ+log 4+log (H+1))+log 3+log (Q+1)≤
      300*q*P*(d+P) := by
  have hqP := one_le_mul_of_one_le_of_one_le hq hP
  have hM' : (M:ℝ)≤3*q*P := by nlinarith
  have h2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have h2u : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have h4 : log (4:ℝ)≤3 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4); linarith
  have h3 : log (3:ℝ)≤2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hm := mul_le_mul_of_nonneg_right hM' (add_nonneg h2 hd)
  have hl := mul_le_mul_of_nonneg_left h2u (show 0≤3*q*P by positivity)
  have ht := mul_le_mul_of_nonneg_left hτ (show 0≤4*P by linarith)
  have hPq : P≤q*P := le_mul_of_one_le_left (by linarith) hq
  have hqP' : q≤q*P := le_mul_of_one_le_right (by linarith) hP
  have hbig : q*P≤q*P*P := le_mul_of_one_le_right (by positivity) hP
  have hpos : 0≤q*P*d := by positivity
  nlinarith

lemma spatial_log_card {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype (Projectivization K V)] (hdim : Module.finrank K V=4) :
    log ((Fintype.card (Projectivization K V):ℝ)+1)≤4*Nat.card K ∧
    log ((Fintype.card (Projectivization K V):ℝ)*log 2+1)≤4*Nat.card K := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hc : (Fintype.card (Projectivization K V):ℝ)=1+Nat.card K+(Nat.card K:ℝ)^2+(Nat.card K:ℝ)^3 := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
    norm_num [sum_range_succ]
  have hQ : (Fintype.card (Projectivization K V):ℝ)+1≤(Nat.card K+1:ℝ)^4 := by
    rw [hc]
    nlinarith [sq_nonneg (Nat.card K:ℝ),sq_nonneg ((Nat.card K:ℝ)^2)]
  have hlog : log ((Nat.card K+1:ℝ)^4)≤4*Nat.card K := by
    rw [log_pow]
    have hh := log_le_sub_one_of_pos (show (0:ℝ)<Nat.card K+1 by linarith)
    norm_num only [Nat.cast_ofNat]
    linarith
  have hf := (log_le_log (by positivity) hQ).trans hlog
  refine ⟨hf,(log_le_log (by have := log_nonneg (by norm_num : (1:ℝ)≤2); positivity) ?_).trans hf⟩
  have hl : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  nlinarith [show (0:ℝ)≤Fintype.card (Projectivization K V) by positivity]

lemma eventually_header_budget : ∀ᶠ σ : ℝ in atTop,
    40*σ*(⌈exp (7*σ/10)⌉₊+1:ℕ)≤exp σ := by
  filter_upwards [ScaleSelection.eventually_polynomial_le_exp_rpow 120 1 1 (3/10)
    (by norm_num) (by norm_num),eventually_ge_atTop (1:ℝ)] with σ h hσ
  simp only [rpow_one] at h
  have he : 1≤exp (7*σ/10) := one_le_exp_iff.mpr (by linarith)
  have hJ : (⌈exp (7*σ/10)⌉₊+1:ℕ)≤3*exp (7*σ/10) := by
    have hh := Nat.ceil_lt_add_one (exp_pos (7*σ/10)).le
    push_cast
    linarith
  calc
    _ ≤ 40*σ*(3*exp (7*σ/10)) := by gcongr
    _ = (120*σ)*exp (7*σ/10) := by ring
    _ ≤ exp (3/10*σ)*exp (7*σ/10) := by gcongr
    _ = exp σ := by rw [←exp_add]; congr 1; ring

lemma header_log_bound {q σ : ℝ} {n N J : ℕ} (hq : 3≤q) (hex : exp σ=q)
    (hn : (n:ℝ)≤2*q^2) (hN : (N:ℝ)≤q^16)
    (hJ : J=⌈exp (7*σ/10)⌉₊) (hbudget : 40*σ*(J+1:ℕ)≤q) :
    log ((n+1:ℕ)*(J+1:ℕ)*((N*(n+1)+1:ℕ):ℝ)^J)≤q := by
  have hqp : 0<q := by linarith
  have hs : 0≤σ := by rw [←log_exp σ,hex]; exact log_nonneg (by linarith)
  have hlogq : log q=σ := by rw [←hex,log_exp]
  have hnq : (n+1:ℕ)≤q^3 := by push_cast; nlinarith [sq_nonneg q]
  have hnlog : log (n+1:ℕ)≤3*σ := by
    have hh := log_le_log (by positivity) hnq
    simpa only [log_pow,hlogq,Nat.cast_ofNat] using hh
  have hNq : (N*(n+1)+1:ℕ)≤q^20 := by
    have hh := mul_le_mul hN hnq (by positivity) (by positivity : 0≤q^16)
    have hh' : q^19+1≤q^20 := by
      rw [pow_succ q 19]
      have hpow : 1≤q^19 := one_le_pow₀ (by linarith)
      nlinarith
    push_cast at *
    calc
      _ ≤ q^16*q^3+1 := by linarith
      _ = q^19+1 := by rw [←pow_add]
      _ ≤ q^20 := hh'
  have hNlog : log (N*(n+1)+1:ℕ)≤20*σ := by
    have hh := log_le_log (by positivity) hNq
    simpa only [log_pow,hlogq,Nat.cast_ofNat] using hh
  have hJnum : (J+1:ℕ)≤3*q := by
    have hJe : exp (7*σ/10)≤exp σ := exp_le_exp.mpr (by linarith)
    have hceil := Nat.ceil_lt_add_one (exp_pos (7*σ/10)).le
    rw [←hJ] at hceil
    rw [hex] at hJe
    push_cast
    linarith
  have hJlog : log (J+1:ℕ)≤2*σ := by
    have hJq : (J+1:ℕ)≤q^2 := by nlinarith
    have hh := log_le_log (by positivity) hJq
    simpa only [log_pow,hlogq,Nat.cast_ofNat] using hh
  rw [log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),log_pow]
  have hm := mul_le_mul_of_nonneg_left hNlog (show (0:ℝ)≤J by positivity)
  push_cast at hbudget
  nlinarith

lemma heavy_header_cost {q : ℝ} {N n m : ℕ} (hq : 3≤q) (hN0 : 0<N)
    (hN : (N:ℝ)≤q^16) (hn : (n:ℝ)≤2*q^2) (hm : log (m+1:ℕ)≤4*q) :
    log ((N:ℝ)*(q+1)*(n+1:ℕ)*(m+1:ℕ))≤24*q := by
  have hq0 : 0<q := by linarith
  have hNN : (0:ℝ)<N := by exact_mod_cast hN0
  have hlogq : log q≤q := (log_le_sub_one_of_pos hq0).trans (by linarith)
  have hlogN : log (N:ℝ)≤16*q := by
    have hh := log_le_log hNN hN
    rw [log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hnq : (n+1:ℕ)≤(q+1)^3 := by
    push_cast
    nlinarith [sq_nonneg q]
  have hlogn : log (n+1:ℕ)≤3*q := by
    have hh := log_le_log (by positivity) hnq
    rw [log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have h := log_le_sub_one_of_pos (show 0<q+1 by linarith)
    linarith
  have hlog := log_le_sub_one_of_pos (show 0<q+1 by linarith)
  rw [log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),
    log_mul hNN.ne' (by positivity)]
  linarith

lemma cover_log_bound {a H E B : ℝ} (ha : 0≤a) (hH : 0<H)
    (h : a≤H*exp E) (hB : 0≤B) (hlen : log H+E≤B) : log (a+1)≤B+log 2 := by
  have he : H*exp E≤exp B := by
    rw [←exp_log hH,←exp_add]
    exact exp_le_exp.mpr hlen
  have hone : 1≤exp B := one_le_exp_iff.mpr hB
  apply (log_le_log (by positivity) (show a+1≤2*exp B by linarith)).trans_eq
  rw [log_mul (by norm_num) (exp_pos _).ne',log_exp]
  ring

lemma union_log_bound {α : Type*} [DecidableEq α] (A B : Finset α) {E : ℝ}
    (hA : log ((A.card:ℝ)+1)≤E) (hB : log ((B.card:ℝ)+1)≤E) :
    log (((A∪B).card:ℝ)+1)≤E+log 2 := by
  have hA' := exp_le_exp.mpr hA
  have hB' := exp_le_exp.mpr hB
  rw [exp_log (by positivity)] at hA' hB'
  have hc : ((A∪B).card:ℝ)≤A.card+B.card := by exact_mod_cast card_union_le A B
  apply (log_le_log (by positivity) (show ((A∪B).card:ℝ)+1≤2*exp E by linarith)).trans_eq
  rw [log_mul (by norm_num) (exp_pos _).ne',log_exp]
  ring

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialCostsActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real
open scoped Classical BigOperators
noncomputable section
local instance flat_JoinedSpatialCostsActual_4 (q : ℕ) [Fact q.Prime] : Finite (Submodule (ZMod q) (Fin 4 → ZMod q)) :=
  Finite.of_injective (fun W : Submodule (ZMod q) (Fin 4 → ZMod q) => (W:Set (Fin 4 → ZMod q))) SetLike.coe_injective

attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialCostsActual_1
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialCostsActual_3
lemma prepared_cost (q : ℕ) [Fact q.Prime] (σ P τ dT : ℝ)
    (U : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))) (n : ℕ)
    (hq : 3≤q) (hex : exp σ=(q:ℝ)) (hn : 0<n) (hnu : n≤U.card)
    (hnup : (n:ℝ)≤2*(q:ℝ)^2) (hP : 1≤P) (hτ : τ≤1) (hdT : 0≤dT)
    (hbud : 40*σ*(⌈exp (7*σ/10)⌉₊+1:ℕ)≤(q:ℝ)) :
    let J := ⌈exp (7*σ/10)⌉₊
    let M := ⌈2*(q:ℝ)*P⌉₊
    let H := (Fintype.card (Projectivization (ZMod q) (Fin 4 → ZMod q)):ℝ)*log 2
    let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
      log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))):ℝ)+1)
    ∀ (a : ℝ),0≤a → a≤(n+1:ℕ)*(J+1:ℕ)*
      ((Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q))*(n+1)+1:ℕ):ℝ)^J*exp E →
    log (a+1)≤4000*((q:ℝ)*P*(log ((U.card:ℝ)/n)+dT+P)) := by
  dsimp only
  let d := log ((U.card:ℝ)/n)
  let Z := (q:ℝ)*P*(d+dT+P)
  have hq' : (3:ℝ)≤q := by exact_mod_cast hq
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hU : (0:ℝ)<U.card := hn'.trans_le (by exact_mod_cast hnu)
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn').mpr
    (by simpa only [one_mul] using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hqZ : (q:ℝ)≤Z := by
    calc
      _ ≤ (q:ℝ)*P := le_mul_of_one_le_right (by positivity) hP
      _ ≤ Z := le_mul_of_one_le_right (by positivity) (by linarith)
  have hZ : 1≤Z := by linarith
  have h2 : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  let J := ⌈exp (7*σ/10)⌉₊
  let M := ⌈2*(q:ℝ)*P⌉₊
  let H := (Fintype.card (Projectivization (ZMod q) (Fin 4 → ZMod q)):ℝ)*log 2
  let QT := (Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))):ℝ)
  let N := Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q))
  let Aheader := (n+1:ℕ)*(J+1:ℕ)*((N*(n+1)+1:ℕ):ℝ)^J
  let AE := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+log (QT+1)
  have hdimm : Module.finrank (ZMod q) (Fin 4 → ZMod q)=4 := by simp
  have hcard : Nat.card (ZMod q)=q := by simp
  have hN : (N:ℝ)≤(q:ℝ)^16 := by
    have hh := DescriptionHeaders.card_submodule_le (K:=ZMod q) (V:=Fin 4 → ZMod q)
    rw [hdimm,hcard] at hh
    norm_num only [Nat.reducePow] at hh
    exact_mod_cast hh
  have hhead : log Aheader≤q := header_log_bound hq' hex hnup hN rfl hbud
  have hlogsplit : log (2*U.card/n)=log 2+d := by
    rw [show 2*(U.card:ℝ)/n=2*((U.card:ℝ)/n) by ring,log_mul (by norm_num) (by positivity)]
  have hH : log (H+1)≤4*(q:ℝ) := by simpa only [H,hcard] using (spatial_log_card hdimm).2
  have hQT : log (QT+1)≤4*(q:ℝ) := by
    simpa only [QT,hcard] using (spatial_log_card (V:=Module.Dual (ZMod q) (Fin 4 → ZMod q))
      (Subspace.dual_finrank_eq.trans hdimm)).1
  have hAE : AE≤300*Z := by
    have hc := spatial_cost (by linarith : (1:ℝ)≤q) hP hd hτ
      (Nat.ceil_lt_add_one (by positivity : 0≤2*(q:ℝ)*P)).le hH hQT
    dsimp only [AE]
    rw [hlogsplit]
    apply hc.trans
    change 300*(q:ℝ)*P*(d+P)≤300*((q:ℝ)*P*(d+dT+P))
    nlinarith [show 0≤(q:ℝ)*P*dT by positivity]
  intro a ha hAl
  have hh := cover_log_bound ha (by positivity : 0<Aheader) hAl (by positivity : 0≤301*Z)
    (show log Aheader+AE≤301*Z by linarith)
  change log (a+1)≤4000*Z
  linarith

lemma heavy_cost (q : ℕ) [Fact q.Prime] (P d dT : ℝ)
    (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q)))) (n : ℕ)
    (hq : 3≤q) (hnup : (n:ℝ)≤2*(q:ℝ)^2) (hP : 1≤P) (hd : 0≤d) (hdT : 0≤dT)
    (a : ℝ) (ha : 0≤a)
    (hab : a≤(Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q)):ℝ)*(q+1:ℕ)*(n+1:ℕ)*(UT.card+1:ℕ)*
      exp (4000*(q:ℝ)*P*(d+dT+P))) :
    log (a+1)≤4500*((q:ℝ)*P*(d+dT+P)) := by
  let Z := (q:ℝ)*P*(d+dT+P)
  let N := Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q))
  have hq' : (3:ℝ)≤q := by exact_mod_cast hq
  have hqZ : (q:ℝ)≤Z := by
    calc
      _ ≤ (q:ℝ)*P := le_mul_of_one_le_right (by positivity) hP
      _ ≤ Z := le_mul_of_one_le_right (by positivity) (by linarith)
  have hZ : 1≤Z := by linarith
  have h2 : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hdimm : Module.finrank (ZMod q) (Fin 4 → ZMod q)=4 := by simp
  have hcard : Nat.card (ZMod q)=q := by simp
  have hN : (N:ℝ)≤(q:ℝ)^16 := by
    have hh := DescriptionHeaders.card_submodule_le (K:=ZMod q) (V:=Fin 4 → ZMod q)
    rw [hdimm,hcard] at hh
    norm_num only [Nat.reducePow] at hh
    exact_mod_cast hh
  have hUT : log (UT.card+1:ℕ)≤4*(q:ℝ) := by
    have hQT := (spatial_log_card (V:=Module.Dual (ZMod q) (Fin 4 → ZMod q))
      (Subspace.dual_finrank_eq.trans hdimm)).1
    rw [hcard] at hQT
    apply le_trans _ hQT
    apply log_le_log (by positivity)
    have hc : (UT.card:ℝ)≤Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) := by
      exact_mod_cast card_le_univ UT
    push_cast
    linarith
  have hNpos : 0<N := Nat.card_pos
  have hBH : log ((N:ℝ)*((q:ℝ)+1)*(n+1:ℕ)*(UT.card+1:ℕ))≤24*(q:ℝ) :=
    heavy_header_cost hq' hNpos hN hnup hUT
  have hBbound : a≤(N:ℝ)*((q:ℝ)+1)*(n+1:ℕ)*(UT.card+1:ℕ)*exp (4000*Z) := by
    simpa only [Nat.cast_add,Nat.cast_one,N,Z,mul_assoc] using hab
  have hh := cover_log_bound ha
    (by positivity : 0<(N:ℝ)*((q:ℝ)+1)*(n+1:ℕ)*(UT.card+1:ℕ)) hBbound
    (by positivity : 0≤4024*Z) (show log ((N:ℝ)*((q:ℝ)+1)*(n+1:ℕ)*(UT.card+1:ℕ))+4000*Z≤4024*Z by linarith)
  change log (a+1)≤4500*Z
  linarith

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales Incidence PreparedProjectiveGeometry
open scoped Classical BigOperators Topology
noncomputable section

local instance flat_JoinedSpatialComplete_1_r99179f_1 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Fin 4 → ZMod q)) :=
  Fintype.ofFinite _
theorem complete_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ D R,Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q)))
      (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))))
      (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → n≤t → (n:ℝ)≤2*(q:ℝ)^2 →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (q:ℝ)^4*exp (-b)≤(n:ℝ)*t → (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
        ∃ W∈caps,(n:ℝ)/100≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤5000*(q:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [source_cover hη C hC,HeavyPlaneRestriction.public_heavy_cover hη C hC,
    eventually_uniform_L hη (eventually_ge_atTop (1:ℝ)),eventually_uniform_R hη 1,
    eventually_header_budget,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with σ hs hh hL hR hbud htau
  intro q _ hq hex D R had U UT n t b τ hn ht0 hnu htu hnt hnup hb hbu hτ hτu
  let P := scaleP σ η D R
  let d := log ((U.card:ℝ)/n)
  let dT := log ((UT.card:ℝ)/t)
  let Z := (q:ℝ)*P*(d+dT+P)
  have hq' : (3:ℝ)≤q := by exact_mod_cast hq
  have hP : 1≤P := one_le_mul_of_one_le_of_one_le (hL D R had) (hR D R had)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht0
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn').mpr (by simpa only [one_mul] using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hdT : 0≤dT := log_nonneg ((le_div_iff₀ ht').mpr (by simpa only [one_mul] using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  have hqZ : (q:ℝ)≤Z := by
    calc
      _ ≤ (q:ℝ)*P := le_mul_of_one_le_right (by positivity) hP
      _ ≤ Z := le_mul_of_one_le_right (by positivity) (by linarith)
  have hZ : 1≤Z := by linarith
  have h2 : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  change ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))), _ ∧ _ ∧ log ((caps.card:ℝ)+1)≤5000*(q:ℝ)*P*(d+dT+P)
  rw [show 5000*(q:ℝ)*P*(d+dT+P)=5000*Z by dsimp [Z]; ring]
  by_cases hsmall : (n:ℝ)≤200*(q:ℝ)*P
  · obtain ⟨hsize,hcapture,hlen⟩ := DescriptionEnumeration.public_cover U n hn hnu
    refine ⟨U.powersetCard n,?_,?_,hlen.trans ?_⟩
    · intro W hW
      obtain ⟨hWU,hnW⟩ := hsize W hW
      refine ⟨hWU,?_⟩
      rw [hnW]
      exact le_mul_of_one_le_right (by positivity) (one_le_exp_iff.mpr (by linarith))
    · intro S T hSU hSn _ _ _ _
      obtain ⟨W,hW,he⟩ := hcapture S hSU hSn
      refine ⟨W,hW,?_⟩
      rw [he,hSn]
      linarith
    · have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤d+1 by linarith)
      have hz : (q:ℝ)*P*(d+1)≤Z := by
        dsimp only [Z]
        gcongr
        linarith
      dsimp only [d] at hh hz
      nlinarith
  · have hdimm : Module.finrank (ZMod q) (Fin 4 → ZMod q)=4 := by simp
    have hcard : Nat.card (ZMod q)=q := by simp
    obtain ⟨A,hAs,hAc,hAl⟩ := hs q hq hex D R had U n b τ hn hnu hnup
      (le_of_not_ge hsmall) hb hbu hτ hτu
    have hAl' : log ((A.card:ℝ)+1)≤4000*Z :=
      prepared_cost q σ P τ dT U n hq hex hn hnu hnup hP (hτu.trans htau.le) hdT
        (by rwa [hex] at hbud) A.card (by positivity) hAl
    obtain ⟨B,hBs,hBc,hBl⟩ := hh (ZMod q) (Fin 4 → ZMod q) D R had
      (by simpa only [hcard] using hex) hdimm U UT n t b τ hn ht0 hnu htu hb hbu hτ hτu
    have hBl' : log ((B.card:ℝ)+1)≤4500*Z := heavy_cost q P d dT UT n hq hnup hP hd hdT
      B.card (by positivity) (by simpa only [hcard] using hBl)
    refine ⟨A∪B,?_,?_,(union_log_bound A B (hAl'.trans (by nlinarith)) hBl').trans (by linarith)⟩
    · intro W hW
      rcases mem_union.mp hW with hW|hW
      · exact hAs W hW
      · simpa only [hcard] using hBs W hW
    · intro S T hSU hSn hTU hTt hprod hsp
      rcases hAc S T hSU hSn (card_pos.mp (by omega)) (by omega)
        (by rwa [hSn,hTt]) (by rwa [hSn,hTt]) with hheavy|⟨W,hW,hcap⟩
      · obtain ⟨W,hW,hcap⟩ := hBc S T hSU hSn hTU hTt
          (by simpa only [hcard] using hprod) (by simpa only [hcard] using hsp) hheavy
        exact ⟨W,mem_union_right _ hW,hcap⟩
      · exact ⟨W,mem_union_left _ hW,by linarith⟩

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales Incidence ProjectiveDuality
open scoped Classical Topology
noncomputable section

theorem complete_cover_any {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V=4 → ∀ D R,Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) V))
      (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → n≤t → (n:ℝ)≤2*(q:ℝ)^2 →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization (ZMod q) V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (q:ℝ)^4*exp (-b)≤(n:ℝ)*t → (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
        ∃ W∈caps,(n:ℝ)/100≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤5000*(q:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  filter_upwards [complete_cover hη C hC] with σ hs
  intro q _ hq hex V _ _ _ hd D R had U UT n t b τ hn ht hnu htu hnt hnup hb hbu hτ hτu
  let e : V ≃ₗ[ZMod q] (Fin 4 → ZMod q) := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let f := mapEquiv e
  let g := mapEquiv e.symm.dualMap
  have hcU : (U.image f).card=U.card := card_image_of_injective _ f.injective
  have hcT : (UT.image g).card=UT.card := card_image_of_injective _ g.injective
  obtain ⟨A,hAs,hAc,hAl⟩ := hs q hq hex D R had (U.image f) (UT.image g) n t b τ
    hn ht (by simpa only [hcU] using hnu) (by simpa only [hcT] using htu) hnt hnup hb hbu hτ hτu
  refine ⟨A.image (fun W => W.image f.symm),?_,?_,?_⟩
  · intro W hW
    obtain ⟨W₀,hW₀,rfl⟩ := mem_image.mp hW
    obtain ⟨hsub,hcard,_⟩ := pullback_cover f U U W₀ (hAs W₀ hW₀).1
    exact ⟨hsub,by simpa only [hcard] using (hAs W₀ hW₀).2⟩
  · intro S T hSU hSn hTU hTt hprod hsp
    have hcS : (S.image f).card=n := by rw [card_image_of_injective _ f.injective,hSn]
    have hcT' : (T.image g).card=t := by rw [card_image_of_injective _ g.injective,hTt]
    have hsp' : (incidenceCount (S.image f) (T.image g):ℝ)≤τ*(n:ℝ)*t/q := by
      simpa only [f,g,incidenceCount_mapEquiv] using hsp
    obtain ⟨W,hW,hcap⟩ := hAc (S.image f) (T.image g)
      (image_subset_image hSU) hcS (image_subset_image hTU) hcT' hprod hsp'
    refine ⟨W.image f.symm,mem_image.mpr ⟨W,hW,rfl⟩,?_⟩
    rw [(pullback_cover f U S W (hAs W hW).1).2.2]
    exact hcap
  · have hcard : ((A.image (fun W => W.image f.symm)).card:ℝ)≤A.card := by
      exact_mod_cast card_image_le (s:=A) (f:=fun W => W.image f.symm)
    have hl : log (((A.image (fun W => W.image f.symm)).card:ℝ)+1)≤log ((A.card:ℝ)+1) :=
      log_le_log (by positivity) (by linarith only [hcard])
    exact hl.trans (by simpa only [hcU,hcT] using hAl)

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialValidated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation
open scoped Classical Topology
noncomputable section

theorem validated_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V=4 → ∀ D R,Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) V))
      (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    (q:ℝ)^4*exp (-b)≤(n:ℝ)*t → (n:ℝ)*t≤2*(q:ℝ)^4 →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization (ZMod q) V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤100000*(q:ℝ)^4/t) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
        ∃ W∈caps,(99/100:ℝ)*n≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤7000*(q:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  have hdec : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [complete_cover_any hη C hC,
    eventually_uniform_L hη (eventually_ge_atTop (200000:ℝ)),eventually_uniform_R hη 1,
    eventually_training_loss hη C 1 (by linarith) (by norm_num),
    hdec.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/1000000)),
    eventually_ge_atTop (1:ℝ)]
    with σ hs hL hR hbsmall hτsmall hσ
  intro q _ hq hex V _ _ _ hdim D R had U UT n t b τ hn ht hnu htu hb hbu hτ hτu hplo hphi
  let P := scaleP σ η D R
  have hL' := hL D R had
  have hLP : scaleL σ η D≤P := le_mul_of_one_le_right (by linarith) (hR D R had)
  have hP : 200000≤P := hL'.trans hLP
  have hbP : b≤P := by
    have hh := hbsmall D R had b 0 hbu (mul_nonneg (by linarith) (rpow_nonneg (by linarith) _))
    simp only [mul_zero,add_zero,one_mul] at hh
    exact hh.trans hLP
  have hsmall : τ≤1/1000000 := hτu.trans hτsmall.le
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hcard : Nat.card (ZMod q)=q := by simp
  have hd4 : Module.finrank (ZMod q) V=1+3 := hdim
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr
    (by simpa using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have he : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr
    (by simpa using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  have hz : 0≤(q:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by positivity
  have hspval (S : Finset (Projectivization (ZMod q) V))
      (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (hsp : (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q) :
      (incidenceCount S T:ℝ)≤(n:ℝ)*t/(1000000*Nat.card (ZMod q)) := by
    rw [hcard]
    apply hsp.trans
    have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤(n:ℝ)*t/q by positivity)
    convert hh using 1 <;> ring
  by_cases hnt : n≤t
  · have hnup : (n:ℝ)≤2*(q:ℝ)^2 := by
      have hnt' : (n:ℝ)≤t := by exact_mod_cast hnt
      nlinarith [sq_nonneg ((n:ℝ)-2*(q:ℝ)^2),sq_nonneg ((q:ℝ)^2)]
    obtain ⟨A,hAs,hAc,hAl⟩ := hs q hq hex V hdim D R had U UT n t b τ
      hn ht hnu htu hnt hnup hb hbu hτ hτu
    obtain ⟨F,hFs,hFc,hFl⟩ := return_gap_cover hd4 A U UT n t hn ht hnu htu P b hP hb hbP
      (fun W hW => (hAs W hW).2) (by simpa only [hcard] using hphi)
      (by simpa only [hcard] using hplo)
    refine ⟨F,by simpa only [hcard] using hFs,?_,?_⟩
    · intro S T hSU hSn hTU hTt hsp
      exact hFc S T hSU hSn hTU hTt (hspval S T hsp) (hAc S T hSU hSn hTU hTt hplo hsp)
    · simp only [hcard,Nat.cast_one] at hFl
      dsimp only [P] at *
      nlinarith only [hFl,hAl,hz]
  · have htn : t≤n := le_of_not_ge hnt
    have htup : (t:ℝ)≤2*(q:ℝ)^2 := by
      have htn' : (t:ℝ)≤n := by exact_mod_cast htn
      nlinarith [sq_nonneg ((t:ℝ)-2*(q:ℝ)^2),sq_nonneg ((q:ℝ)^2)]
    let e := bidual (K:=ZMod q) (V:=V)
    have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
    have hddual : Module.finrank (ZMod q) (Module.Dual (ZMod q) V)=4 := Subspace.dual_finrank_eq.trans hdim
    obtain ⟨A,hAs,hAc,hAl⟩ := hs q hq hex (Module.Dual (ZMod q) V) hddual D R had UT (U.image e) t n b τ
      ht hn htu (by rwa [hcU]) htn htup hb hbu hτ hτu
    obtain ⟨F,hFs,hFc,hFl⟩ := reverse_gap_cover hd4 A U UT n t hn ht hnu htu P hP
      (fun W hW => (hAs W hW).2) (by simpa only [hcard] using hphi)
    refine ⟨F,by simpa only [hcard] using hFs,?_,?_⟩
    · intro S T hSU hSn hTU hTt hsp
      have hcS : (S.image e).card=n := (card_image_of_injective _ e.injective).trans hSn
      have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
      have hspread : (incidenceCount T (S.image e):ℝ)≤τ*(t:ℝ)*n/q := by
        rw [hinc]
        convert hsp using 1 <;> first | rfl | ring
      have hplo' : (q:ℝ)^4*exp (-b)≤(t:ℝ)*n := by simpa only [mul_comm] using hplo
      exact hFc S T hSU hSn hTt (hspval S T hsp)
        (hAc T (S.image e) hTU hTt (image_subset_image hSU) hcS hplo' hspread)
    · simp only [hcard,Nat.cast_one] at hFl
      rw [hcU] at hAl
      dsimp only [P] at *
      nlinarith only [hFl,hAl,hz]

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_GeometricInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation Projection
open scoped Classical Topology
noncomputable section

lemma uniform_four_oai : Uniform 4 7000 := by
  intro η hη C hC
  exact SpatialPublic.validated_cover hη C hC

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.GeometricCover.uniform_four_oai := @OAI.SharpLogRamsey.GeometricCover.uniform_four_oai
