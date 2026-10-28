-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.supplier_assignments
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:40:06.243964+00:00
-- url     : https://prove2.me/submissions/cb0a2c47-12c9-47e9-9ad7-609bf4c0a5ca

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K024
import Definitions.Def_OAIQ035K025

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem expect_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (f : Ω × Ξ → ℝ) :
    (joint μ κ).expect f=μ.expect (fun ω => (κ ω).expect (fun ξ => f (ω, ξ))) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem support_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (z : Ω × Ξ)
    (h : 0 < (joint μ κ).weight z) : 0 < μ.weight z.1 ∧ 0 < (κ z.1).weight z.2 := by
  exact ⟨pos_of_mul_pos_left h ((κ z.1).nonneg z.2), pos_of_mul_pos_right h (μ.nonneg z.1)⟩

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T E : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype E]

theorem supplier_partition (σ : E → I ⊕ T) (q : E → ℝ) :
    (∑ i, supplierOutside σ q i)+(∑ t, supplierBundle σ q t)=∑ e, q e := by
  simp only [supplierOutside,supplierBundle]
  rw [sum_comm, sum_comm (s := (univ : Finset T)), ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  cases h : σ e with
  | inl i => simp only [Sum.inl.injEq,Sum.inl_ne_inr,ite_false,sum_const_zero,add_zero,
      sum_ite_eq,mem_univ,ite_true]
  | inr t => simp only [Sum.inr.injEq,Sum.inr_ne_inl,ite_false,sum_const_zero,zero_add,
      sum_ite_eq,mem_univ,ite_true]

theorem supplier_charge (σ : E → I ⊕ T) (q : E → ℝ) (b : I → ℝ) (c : T → ℝ) :
    (∑ i, supplierOutside σ q i*b i)+(∑ t, supplierBundle σ q t*c t)=
      ∑ e, q e*(Sum.elim b c (σ e)) := by
  simp only [supplierOutside,supplierBundle,sum_mul]
  rw [sum_comm, sum_comm (s := (univ : Finset T)), ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  cases h : σ e with
  | inl i => simp only [Sum.inl.injEq,Sum.inl_ne_inr,ite_false,zero_mul,sum_const_zero,
      add_zero,ite_mul,sum_ite_eq,mem_univ,ite_true,Sum.elim_inl]
  | inr t => simp only [Sum.inr.injEq,Sum.inr_ne_inl,ite_false,zero_mul,sum_const_zero,
      zero_add,ite_mul,sum_ite_eq,mem_univ,ite_true,Sum.elim_inr]

theorem allocate_suppliers (σ : E → I ⊕ T) (q : E → ℝ) (s : T)
    (u : I → ℝ) (Y : T → I → ℝ) (p : T → ℝ) (d : I → ℝ) (R : E → ℝ)
    (hY : ∀ t i, 0 ≤ Y t i) (hp : ∀ t, ∑ i, Y t i=p t)
    (hhalf : ∀ t, (1/2:ℝ) ≤ p t) (hq : ∀ e, 0 ≤ q e)
    (htotal : (∑ e, q e)=1-p s)
    (hout : ∀ i, supplierOutside σ q i ≤ u i)
    (hself : supplierBundle σ q s=0)
    (hR : ∀ e, 0 < q e → match σ e with
      | .inl i => d i ≤ R e
      | .inr t => ∀ i, 0 < Y t i → d i ≤ R e) :
    ∃ r : I ⊕ (T × I) → ℝ,
      (∀ a, 0 ≤ r a ∧ r a ≤ Sum.elim u (fun ti => Y ti.1 ti.2) a) ∧
      (∑ a, r a)=1 ∧
      (∑ a, r a*(Sum.elim d (fun ti => d ti.2) a)) ≤
        (∑ i, Y s i*d i)+(∑ e, q e*R e) := by
  classical
  let U := supplierOutside σ q
  let B := supplierBundle σ q
  have hu0 : ∀ i, 0 ≤ U i := fun i => sum_nonneg (fun e _ => by
    split_ifs; exact hq e; exact le_rfl)
  have hb0 : ∀ t, 0 ≤ B t := fun t => sum_nonneg (fun e _ => by
    split_ifs; exact hq e; exact le_rfl)
  have hpp : ∀ t, 0 < p t := fun t => lt_of_lt_of_le (by norm_num) (hhalf t)
  have hbcap : ∀ t, B t ≤ p t := by
    intro t
    calc
      B t ≤ ∑ e, q e := sum_le_sum (fun e _ => by
        split_ifs; exact le_rfl; exact hq e)
      _ = 1-p s := htotal
      _ ≤ 1/2 := by linarith only [hhalf s]
      _ ≤ p t := hhalf t
  let r : I ⊕ (T × I) → ℝ := Sum.elim U
    (fun ti => (if ti.1=s then Y ti.1 ti.2 else 0)+(B ti.1/p ti.1)*Y ti.1 ti.2)
  have hr : ∀ a, 0 ≤ r a ∧ r a ≤ Sum.elim u (fun ti => Y ti.1 ti.2) a := by
    rintro (i | ⟨t,i⟩)
    · exact ⟨hu0 i,hout i⟩
    · change 0 ≤ (if t=s then Y t i else 0)+(B t/p t)*Y t i ∧
        (if t=s then Y t i else 0)+(B t/p t)*Y t i ≤ Y t i
      have hf0 : 0 ≤ B t/p t := div_nonneg (hb0 t) (hpp t).le
      have hf1 : B t/p t ≤ 1 := (div_le_one (hpp t)).mpr (hbcap t)
      by_cases ht : t=s
      · subst t
        simp only [ite_true,B,hself,zero_div,zero_mul,add_zero]
        exact ⟨hY s i,le_rfl⟩
      · simp only [ite_eq_right ht,zero_add]
        exact ⟨mul_nonneg hf0 (hY t i),mul_le_of_le_one_left (hY t i) hf1⟩
  have hmass : (∑ a, r a)=1 := by
    simp only [r,Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,
      sum_add_distrib,← mul_sum,hp]
    simp only [sum_ite_irrel,sum_const_zero,hp,sum_ite_eq',mem_univ,ite_true]
    have hcancel : ∀ t, B t/p t*p t=B t := fun t => div_mul_cancel₀ _ (hpp t).ne'
    simp only [hcancel]
    have ht := supplier_partition σ q
    rw [htotal] at ht
    dsimp only [U,B]
    linarith only [ht]
  refine ⟨r,hr,hmass,?_⟩
  let c := fun t => (∑ i, Y t i*d i)/p t
  have hcost : (∑ a, r a*(Sum.elim d (fun ti => d ti.2) a))=
      (∑ i, Y s i*d i)+(∑ i, U i*d i)+(∑ t, B t*c t) := by
    simp only [r,Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,
      add_mul,sum_add_distrib,ite_mul,zero_mul]
    simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq',mem_univ,ite_true]
    have he : ∀ t, (∑ i, (B t/p t)*Y t i*d i)=B t*c t := by
      intro t
      simp only [c,mul_assoc,← mul_sum]
      ring
    simp only [he]
    ring
  rw [hcost,add_assoc]
  apply add_le_add le_rfl
  change (∑ i, supplierOutside σ q i*d i)+(∑ t, supplierBundle σ q t*c t) ≤ _
  rw [supplier_charge]
  apply sum_le_sum
  intro e _
  by_cases hqe : q e=0
  · simp only [hqe,zero_mul,le_refl]
  · have hqe' : 0 < q e := lt_of_le_of_ne (hq e) (Ne.symm hqe)
    apply mul_le_mul_of_nonneg_left _ (hq e)
    have hc := hR e hqe'
    cases he : σ e with
    | inl i => simpa only [he,Sum.elim_inl] using hc
    | inr t =>
      simp only [Sum.elim_inr]
      simp only [he] at hc
      apply (div_le_iff₀ (hpp t)).mpr
      rw [← hp t,mul_sum]
      apply sum_le_sum
      intro i _
      by_cases hi : Y t i=0
      · simp only [hi,zero_mul,mul_zero,le_refl]
      · exact (mul_le_mul_of_nonneg_left (hc i (lt_of_le_of_ne (hY t i) (Ne.symm hi)))
          (hY t i)).trans_eq (mul_comm _ _)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem outside_supplier (next : T → T) (q : Star I T → ℝ) (i : I) :
    supplierOutside (supplier next) q i=q (.inl i) := by
  simp only [supplierOutside,Fintype.sum_sum_type,supplier,
    Sum.inl.injEq,Sum.inr_ne_inl,ite_false,sum_const_zero,add_zero,
    sum_ite_eq',mem_univ,ite_true]

theorem self_supplier_zero (P A : T → Finset I) (y : I → ℝ) (c : T → ℝ)
    (γ : ℝ) (next : T → T) (q : Star I T → ℝ) (s : T)
    (hAP : ∀ t, Disjoint (A t) (P t)) (hnext : ∀ t, next t=t → c t=0)
    (htarget : ∀ e, s ∉ targets A e → q e=0)
    (hzero : ∀ e, weight y P A c γ e=0 → q e=0) :
    supplierBundle (supplier next) q s=0 := by
  apply sum_eq_zero
  intro e _
  cases e with
  | inl i => simp only [supplier,Sum.inl_ne_inr,ite_false]
  | inr e =>
    cases e with
    | inl st =>
      dsimp only [supplier]
      by_cases ht : st.2=s
      · simp only [ht,ite_true]
        by_cases hs : st.1=s
        · apply hzero
          simp only [weight,hs,ht,disjoint_iff_inter_eq_empty.mp (hAP s),sum_empty]
        · exact htarget _ (by simpa only [targets,mem_singleton] using Ne.symm hs)
      · simp only [Sum.inr.injEq,ite_eq_right ht]
    | inr t =>
      dsimp only [supplier]
      by_cases ht : next t=s
      · simp only [ht,ite_true]
        by_cases hs : t=s
        · subst t
          apply hzero
          simp only [weight,hnext s ht,mul_zero]
        · exact htarget _ (by simpa only [targets,mem_singleton] using Ne.symm hs)
      · simp only [Sum.inr.injEq,ite_eq_right ht]

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem supplier_assignments_oai (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B : ℝ} {Δ : ℕ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (next : T → T) (hnext : ∀ t, next t=t → c t=0)
    (hAP : ∀ t, Disjoint (A t) (P t)) (s : T) (d : I → ℝ) (R : Star I T → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i) (hp : 0 < p s) (hR0 : ∀ e, 0 ≤ R e)
    (hradius : ∀ ω, 0 < L.ν.weight ω → ∀ ξ, 0 < (L.κ ω).weight ξ →
      ∀ e, 0 < L.R ω s e → match supplier next e with
      | .inl i => d i ≤ R e
      | .inr t => ∀ i, 0 < L.C ω ξ (t,i) → d i ≤ R e) :
    letI := L.finite
    ∃ r : (L.Ω × (T → Finset I)) → (I ⊕ (T × I)) → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ Sum.elim
          (fun i => g*(L.O z.1 (.inl i):ℝ))
          (fun ti => g*(L.C z.1 z.2 ti:ℝ)) a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
      (∑ i ∈ P s, y i*d i)/p s+
        (∑ e, (if s ∈ targets A e then weight y P A c γ e else 0)*R e) := by
  classical
  let := L.finite
  let μ := L.ν.joint L.κ
  let Y := fun z : L.Ω × (T → Finset I) => fun t i => g*(L.C z.1 z.2 (t,i):ℝ)
  let u := fun z : L.Ω × (T → Finset I) => fun i => g*(L.O z.1 (.inl i):ℝ)
  let q := fun z : L.Ω × (T → Finset I) => fun e => g*(L.R z.1 s e:ℝ)
  let b := fun ω t => g*(L.K ω t:ℝ)
  have halloc : ∀ z, 0 < μ.weight z → ∃ r : I ⊕ (T × I) → ℝ,
      (∀ a, 0 ≤ r a ∧ r a ≤ Sum.elim (u z) (fun ti => Y z ti.1 ti.2) a) ∧
      (∑ a, r a)=1 ∧
      (∑ a, r a*(Sum.elim d (fun ti => d ti.2) a)) ≤
        (∑ i, Y z s i*d i)+(∑ e, q z e*R e) := by
    intro z hz
    obtain ⟨hω,hξ⟩ := L.ν.support_joint L.κ z hz
    have hsum : ∀ t, ∑ i, Y z t i=b z.1 t := by
      intro t
      simp only [Y,b,← mul_sum,← Nat.cast_sum,(L.pieces z.1 z.2 hξ t).1]
    have hqt : (∑ e, q z e)=1-b z.1 s := by
      have he := congrArg (fun n : ℕ => g*(n:ℝ)) (L.exact_total z.1 s)
      simp only [Nat.cast_add,Nat.cast_sum,mul_add,hunit,mul_sum] at he
      dsimp only [q,b]
      linarith only [he]
    have hzero : ∀ e, weight y P A c γ e=0 → q z e=0 := by
      intro e he
      have ho := L.open_zero z.1 hω e he
      have hr := L.request_cap z.1 hω s e
      rw [ho] at hr
      simp only [q,Nat.eq_zero_of_le_zero hr,Nat.cast_zero,mul_zero]
    have htarget : ∀ e, s ∉ targets A e → q z e=0 := by
      intro e he
      simp only [q,L.request_target z.1 s e he,Nat.cast_zero,mul_zero]
    apply allocate_suppliers (supplier next) (q z) s (u z) (Y z) (b z.1) d R
      (fun t i => mul_nonneg hg.le (Nat.cast_nonneg _)) hsum (L.half z.1)
      (fun e => mul_nonneg hg.le (Nat.cast_nonneg _)) hqt
    · intro i
      rw [outside_supplier]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (L.request_cap z.1 hω s (.inl i))) hg.le
    · exact self_supplier_zero P A y c γ next (q z) s hAP hnext htarget hzero
    · intro e he
      have he' : 0 < L.R z.1 s e := by
        have hp' := (mul_pos_iff_of_pos_left hg).mp he
        exact_mod_cast hp'
      have hrad := hradius z.1 hω z.2 hξ e he'
      cases hh : supplier next e with
      | inl i => simpa only [hh] using hrad
      | inr t =>
        simp only [hh] at hrad
        intro i hi
        have hi' : 0 < L.C z.1 z.2 (t,i) := by
          have hv := (mul_pos_iff_of_pos_left hg).mp hi
          exact_mod_cast hv
        exact hrad i hi'
  choose r hr using fun z : {z // 0 < μ.weight z} => halloc z.1 z.2
  let r' := fun z => if hz : 0 < μ.weight z then r ⟨z,hz⟩ else fun _ => 0
  refine ⟨r',?_,?_⟩
  · intro z hz
    have hz' : 0 < μ.weight z := hz
    simp only [r',dite_eq_left hz']
    exact ⟨(hr ⟨z,hz'⟩).1,(hr ⟨z,hz'⟩).2.1⟩
  · have he : μ.expect (fun z => ∑ a, r' z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
        μ.expect (fun z => (∑ i, Y z s i*d i)+(∑ e, q z e*R e)) :=
      μ.expect_mono_support (fun z hz => by
        simpa only [r',dite_eq_left hz] using (hr ⟨z,hz⟩).2.2)
    apply he.trans
    rw [FiniteLaw.expect_add]
    apply add_le_add
    · have hmean : μ.expect (fun z => ∑ i, Y z s i*d i)=
          L.ν.expect (fun ω => (b ω s/p s)*(∑ i ∈ P s, y i*d i)) := by
        rw [FiniteLaw.expect_joint]
        apply congrArg L.ν.expect
        funext ω
        rw [FiniteLaw.expect_sum]
        simp only [Y,FiniteLaw.expect_mul_right,L.piece_mean]
        simp only [ite_mul,zero_mul,sum_ite_mem,univ_inter]
        rw [mul_sum]
        exact sum_congr rfl (fun i _ => by dsimp only [b]; ring)
      rw [hmean]
      have ha : 0 ≤ ∑ i ∈ P s, y i*d i := sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
      calc
        _ ≤ L.ν.expect (fun _ => (∑ i ∈ P s, y i*d i)/p s) := L.ν.expect_mono (fun ω => by
          have hcap : b ω s ≤ 1 := (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (L.total_cap ω s)) hg.le).trans_eq hunit
          calc
            _ ≤ (1/p s)*(∑ i ∈ P s, y i*d i) := mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right hcap hp.le) ha
            _ = _ := by ring)
        _ = _ := L.ν.expect_const _
    · rw [FiniteLaw.expect_joint]
      simp only [q,FiniteLaw.expect_const,FiniteLaw.expect_sum,FiniteLaw.expect_mul_right]
      exact sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right (L.request_mean s e) (hR0 e))

end MetricKMedian.Preparation
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.supplier_assignments_oai := @OAI.MetricKMedian.Preparation.supplier_assignments_oai
