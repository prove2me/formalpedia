-- Prove2me | solution 1 for OAI.GAD.exists_packed_measurement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:54:58.614282+00:00
-- url     : https://prove2.me/submissions/02507fe6-dde4-4704-89a0-134dac6e7932

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/FinitePacking.lean:L112-L183
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.exists_packed_measurement. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialDecoder
import Theorems.Thm_OAI_GAD_exists_le_weighted_average
import Theorems.Thm_OAI_GAD_sequential_decoder_bound
import Theorems.Thm_OAI_GAD_spectralFactor_gram

-- ---- from OAI.InformationTheory.AmplitudeDamping.EntropyContinuity ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem IsProjection.posSemidef {P : Matrix ι ι ℂ} (hP : IsProjection P) : P.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose P
  rwa [hP.1.eq,hP.2] at h

theorem IsProjection.complement {P : Matrix ι ι ℂ} (hP : IsProjection P) : IsProjection (1-P) := by
  refine ⟨(Matrix.isHermitian_one).sub hP.1, ?_⟩
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hP.2]
  simp

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

variable [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.BlockFactors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

end

variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq μ]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_8} [Fintype ι] [DecidableEq ι]

theorem trace_product_nonneg {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let L := spectralFactor hB
  have hL : L*Lᴴ=B := spectralFactor_gram hB
  have h := (hA.conjTranspose_mul_mul_same L).trace_nonneg
  rw [Matrix.trace_mul_cycle] at h
  rw [hL] at h
  simpa only [Matrix.trace_mul_comm B A] using (Complex.nonneg_iff.mp h).1

theorem trace_product_mono {P A B : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (hAB : (B-A).PosSemidef) : (P*A).trace.re ≤ (P*B).trace.re := by
  have h := trace_product_nonneg hP hAB
  simpa only [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,sub_nonneg] using h

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.TypicalSets ----
namespace OAI

noncomputable section

universe u_1 u_2

section
open scoped BigOperators
namespace GAD
variable {α : Type u_1} [Fintype α]

omit [Fintype α] in
theorem iidWeight_nonneg (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (n : ℕ) (x : Fin n → α) :
    0 ≤ iidWeight q n x := Finset.prod_nonneg (fun j _ ↦ hq (x j))

theorem iidWeight_total (q : α → ℝ) (hs : ∑ a, q a=1) (n : ℕ) :
    (∑ x : Fin n → α, iidWeight q n x)=1 := by
  rw [show (∑ x : Fin n → α, iidWeight q n x) = ∏ j : Fin n, ∑ a, q a from
    (Fintype.prod_sum (fun _ : Fin n ↦ q)).symm]
  simp only [hs,Finset.prod_const_one]

theorem iid_split_sum (q : α → ℝ) (n : ℕ) (f : (Fin (n+1) → α) → ℝ) :
    (∑ x, iidWeight q (n+1) x*f x) =
      ∑ a, ∑ x : Fin n → α, q a*iidWeight q n x*f (Fin.cons a x) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) ↦ α))
    (fun x ↦ iidWeight q (n+1) x*f x)]
  simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,iidWeight,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ]
  rfl

end GAD

end

open scoped BigOperators
namespace GAD
variable {α : Type u_2} [Fintype α]
attribute [local instance] OAI.GAD.instDecidablePred_oAI
end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.FinitePacking ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

universe u_1 u_2 u_3

section
open scoped BigOperators
namespace GAD
variable {α : Type u_1} [Fintype α]

theorem iid_coordinate (q : α → ℝ) (hs : ∑ a, q a=1) (f : α → ℝ) (n : ℕ) (i : Fin n) :
    (∑ x : Fin n → α, iidWeight q n x*f (x i))=∑ a, q a*f a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [iid_split_sum]
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp only [Fin.cons_zero,mul_assoc,← Finset.mul_sum,← Finset.sum_mul,
          iidWeight_total q hs n,one_mul]
      · simp only [Fin.cons_succ,mul_assoc,← Finset.mul_sum,ih,← Finset.sum_mul,hs,one_mul]

theorem iid_pair (q : α → ℝ) (hs : ∑ a, q a=1) (f : α → α → ℝ)
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∑ x : Fin n → α, iidWeight q n x*f (x i) (x j))=∑ a, ∑ b, q a*q b*f a b := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [iid_split_sum]
      revert hij
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · refine Fin.cases ?_ (fun j hij ↦ ?_) j
        · intro h; exact (h rfl).elim
        · simp only [Fin.cons_zero,Fin.cons_succ,mul_assoc,← Finset.mul_sum,
            iid_coordinate q hs]
      · refine Fin.cases ?_ (fun j hij ↦ ?_) j
        · intro _
          simp only [Fin.cons_zero,Fin.cons_succ,mul_assoc,← Finset.mul_sum]
          have he (b : α) := iid_coordinate q hs (fun a ↦ f a b) n i
          simp only [he,Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          ring
        · have hij' : i ≠ j := by intro h; exact hij (congrArg Fin.succ h)
          simp only [Fin.cons_succ,mul_assoc,← Finset.mul_sum,ih i j hij',
            ← Finset.sum_mul,hs,one_mul]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} {α : Type u_3} [Fintype ι] [Fintype α] [DecidableEq ι]

theorem packing_cross_bound (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (A Q : α → Matrix ι ι ℂ) (hQ : ∀ a, IsProjection (Q a))
    (P : Matrix ι ι ℂ) (hP : IsProjection P) {c r : ℝ} (hc : 0 ≤ c)
    (hr : ∀ a, (Q a).trace.re ≤ r)
    (hp : (c • P-P*(∑ a, q a • A a)*P).PosSemidef) :
    (∑ a, ∑ b, q a*q b*(Q b*(P*A a*P)).trace.re) ≤ c*r := by
  have hm (b : α) : (∑ a, q a*(Q b*(P*A a*P)).trace.re)=
      (Q b*(P*(∑ a, q a • A a)*P)).trace.re := by
    simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_sum,
      Matrix.trace_smul,Complex.re_sum,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
  have hb (b : α) : (∑ a, q a*(Q b*(P*A a*P)).trace.re) ≤ c*r := by
    rw [hm]
    have h1 := trace_product_mono (hQ b).posSemidef hp
    simp only [Matrix.mul_smul,Matrix.trace_smul,Complex.real_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h1
    have h2 := trace_product_mono (hQ b).posSemidef hP.complement.posSemidef
    simp only [Matrix.mul_one] at h2
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (hr b)) hc
    exact h1.trans h3
  calc
    _ = ∑ b, q b*(∑ a, q a*(Q b*(P*A a*P)).trace.re) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _; ring
    _ ≤ ∑ b, q b*(c*r) := Finset.sum_le_sum (fun b _ ↦ mul_le_mul_of_nonneg_left (hb b) (hq b))
    _ = _ := by rw [← Finset.sum_mul,hs,one_mul]

/-- Finite iid quantum packing, using an explicit sequential collective POVM. -/
theorem exists_packed_measurement (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (A Q : α → Matrix ι ι ℂ) (hA : ∀ a, IsState (A a)) (hQ : ∀ a, IsProjection (Q a))
    (P : Matrix ι ι ℂ) (hP : IsProjection P) {a b c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r)
    (hga : (∑ x, q x*(1-(P*A x).trace.re)) ≤ a)
    (hcb : (∑ x, q x*(1-(Q x*A x).trace.re)) ≤ b)
    (hr : ∀ x, (Q x).trace.re ≤ r)
    (hcp : (c • P-P*(∑ x, q x • A x)*P).PosSemidef)
    (M : ℕ) (hM : 0 < M) :
    ∃ (x : Fin M → α) (D : Fin M → Matrix ι ι ℂ),
      (∀ m, (D m).PosSemidef) ∧ (∑ m, D m=1) ∧
      1-(∑ m, (D m*A (x m)).trace.re)/(M:ℝ) ≤ 9*a+8*b+4*(M:ℝ)*c*r := by
  classical
  let ga : α → ℝ := fun x ↦ 1-(P*A x).trace.re
  let cb : α → ℝ := fun x ↦ 1-(Q x*A x).trace.re
  let cr : α → α → ℝ := fun x y ↦ (Q y*(P*A x*P)).trace.re
  let cost : (Fin M → α) → Fin M → ℝ := fun x m ↦
    9*ga (x m)+8*cb (x m)+4*∑ j : Fin M, if j=m then 0 else cr (x m) (x j)
  let B : (Fin M → α) → ℝ := fun x ↦ (∑ m, cost x m)/(M:ℝ)
  have hcross := packing_cross_bound q hq hs A Q hQ P hP hc hr hcp
  have hcross' (m j : Fin M) :
      (∑ x : Fin M → α, iidWeight q M x*(if j=m then 0 else cr (x m) (x j))) ≤ c*r := by
    by_cases hj : j=m
    · simp only [hj,ite_true,mul_zero,Finset.sum_const_zero]
      exact mul_nonneg hc hr0
    · simp only [ite_eq_right hj]
      rw [iid_pair q hs cr M m j (Ne.symm hj)]
      exact hcross
  have hcost (m : Fin M) : (∑ x, iidWeight q M x*cost x m) ≤ 9*a+8*b+4*(M:ℝ)*c*r := by
    have h1 := iid_coordinate q hs ga M m
    have h2 := iid_coordinate q hs cb M m
    have h3 : (∑ x, iidWeight q M x*(∑ j : Fin M, if j=m then 0 else cr (x m) (x j))) ≤ (M:ℝ)*c*r := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ ≤ ∑ _j : Fin M, c*r := Finset.sum_le_sum (fun j _ ↦ hcross' m j)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
    dsimp only [cost]
    have hex : (∑ x, iidWeight q M x*(9*ga (x m)+8*cb (x m)+4*∑ j : Fin M, if j=m then 0 else cr (x m) (x j))) =
        9*(∑ x, iidWeight q M x*ga (x m))+8*(∑ x, iidWeight q M x*cb (x m))+
          4*(∑ x, iidWeight q M x*(∑ j : Fin M, if j=m then 0 else cr (x m) (x j))) := by
      have hscl (d : ℝ) (f : (Fin M → α) → ℝ) :
          (∑ x, iidWeight q M x*(d*f x))=d*∑ x, iidWeight q M x*f x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _; ring
      simp only [mul_add,Finset.sum_add_distrib,hscl]
    rw [hex,h1,h2]
    change (∑ x, q x*ga x) ≤ a at hga
    change (∑ x, q x*cb x) ≤ b at hcb
    linarith
  have hB : (∑ x, iidWeight q M x*B x) ≤ 9*a+8*b+4*(M:ℝ)*c*r := by
    have hMp : 0 < (M:ℝ) := by exact_mod_cast hM
    simp only [B,← mul_div_assoc,Finset.mul_sum,← Finset.sum_div]
    rw [Finset.sum_comm]
    apply (div_le_iff₀ hMp).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun m _ ↦ hcost m)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh
  obtain ⟨x,hx⟩ := exists_le_weighted_average (iidWeight q M) (iidWeight_nonneg q hq M)
    (iidWeight_total q hs M) B
  obtain ⟨D,hD,hDs,herr⟩ := sequential_decoder_bound hM P hP (fun m ↦ Q (x m)) (fun m ↦ A (x m))
    (fun m ↦ hQ (x m)) (fun m ↦ hA (x m))
  refine ⟨x,D,hD,hDs,?_⟩
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun m _ ↦ herr m)
  change (∑ m, (1-(D m*A (x m)).trace.re)) ≤ ∑ m, cost x m at hh
  have hMt : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hi : 1-(∑ m, (D m*A (x m)).trace.re)/(M:ℝ) ≤ B x := by
    change _ ≤ (∑ m, cost x m)/(M:ℝ)
    rw [show (1:ℝ)=(M:ℝ)/(M:ℝ) from (div_self hMt).symm,← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hh
  exact hi.trans (hx.trans hB)

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.exists_packed_measurement := @_root_.OAI.GAD.exists_packed_measurement
