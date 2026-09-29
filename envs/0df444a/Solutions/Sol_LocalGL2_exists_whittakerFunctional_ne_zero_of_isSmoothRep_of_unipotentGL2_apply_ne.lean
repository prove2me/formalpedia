-- Prove2me | solution 1 for LocalGL2.exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/59123d78-1847-5b2b-a6a5-fb2340207743

import Mathlib
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 0

noncomputable section

open IsDedekindDomain NumberField
open FLT.SmoothAdmissibleSchurCommutant
open scoped WithZero

namespace WhittakerExistence

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

variable (K v) in

def unif : HeightOneSpectrum.adicCompletion K v :=
  ((Classical.choose (v.valuation_exists_uniformizer K) : K) : v.adicCompletion K)

theorem v_unif : Valued.v (unif K v) = WithZero.exp (-1 : ℤ) := by
  rw [unif, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact Classical.choose_spec (v.valuation_exists_uniformizer K)

theorem unif_ne_zero : unif K v ≠ 0 := by
  intro h
  have h1 := v_unif (K := K) (v := v)
  rw [h, Valuation.map_zero] at h1
  exact WithZero.exp_ne_zero h1.symm

theorem v_unif_zpow (n : ℤ) : Valued.v (unif K v ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, v_unif, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

variable (K v) in

def ball (j : ℤ) : AddSubgroup (HeightOneSpectrum.adicCompletion K v) where
  carrier := {x | Valued.v x ≤ WithZero.exp j}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rwa [Valuation.map_neg]

theorem mem_ball {j : ℤ} {x : F} : x ∈ ball K v j ↔ Valued.v x ≤ WithZero.exp j := Iff.rfl

theorem ball_mono {j j' : ℤ} (h : j ≤ j') : ball K v j ≤ ball K v j' :=
  fun _ hx => le_trans hx (WithZero.exp_le_exp.mpr h)

theorem exists_mem_ball (x : F) : ∃ j : ℤ, x ∈ ball K v j := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [mem_ball, hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), by rw [mem_ball, ← WithZero.exp_log hx, WithZero.log_exp]⟩

theorem coe_ball_eq_image (j : ℤ) :
    (ball K v j : Set F) = (fun x : F => unif K v ^ (-j) * x) '' (v.adicCompletionIntegers K : Set F) := by
  ext x
  constructor
  · intro hx
    refine ⟨unif K v ^ j * x, ?_, ?_⟩
    · show unif K v ^ j * x ∈ v.adicCompletionIntegers K
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_unif_zpow]
      calc WithZero.exp (-j) * Valued.v x ≤ WithZero.exp (-j) * WithZero.exp j :=
            mul_le_mul_right (show Valued.v x ≤ WithZero.exp j from hx) _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · show unif K v ^ (-j) * (unif K v ^ j * x) = x
      rw [← mul_assoc, ← zpow_add₀ unif_ne_zero, neg_add_cancel, zpow_zero, one_mul]
  · rintro ⟨y, hy, rfl⟩
    show Valued.v (unif K v ^ (-j) * y) ≤ WithZero.exp j
    have hy' : Valued.v y ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hy
    rw [Valuation.map_mul, v_unif_zpow, neg_neg]
    calc WithZero.exp j * Valued.v y ≤ WithZero.exp j * 1 := mul_le_mul_right hy' _
      _ = WithZero.exp j := mul_one _

theorem isCompact_ball (j : ℤ) : IsCompact (ball K v j : Set F) := by
  rw [coe_ball_eq_image]
  exact (NumberField.isCompactAdicCompletionIntegers K v).image (continuous_const.mul continuous_id)

theorem isOpen_ball (j : ℤ) : IsOpen (ball K v j : Set F) := by
  have h0 : Valued.v.restrict (unif K v ^ (-j)) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, v_unif_zpow, neg_neg]
    exact WithZero.exp_ne_zero
  have := Valued.isOpen_closedBall (R := F) h0
  convert this using 1
  ext x
  simp only [SetLike.mem_coe, mem_ball, Set.mem_setOf_eq]
  rw [Valuation.restrict_le_iff, v_unif_zpow, neg_neg]

scoped instance compactSpace_ball (j : ℤ) : CompactSpace (ball K v j) :=
  isCompact_iff_compactSpace.mp (isCompact_ball j)

variable (K v) in

abbrev Q (j k : ℤ) : Type := ↥(ball K v j) ⧸ (ball K v k).addSubgroupOf (ball K v j)

scoped instance finite_Q (j k : ℤ) : Finite (Q K v j k) :=
  AddSubgroup.quotient_finite_of_isOpen _ (AddSubgroup.addSubgroupOf_isOpen _ _ (isOpen_ball k))

scoped instance fintype_Q (j k : ℤ) : Fintype (Q K v j k) := Fintype.ofFinite _

abbrev cl (j k : ℤ) (x : F) (hx : x ∈ ball K v j) : Q K v j k := QuotientAddGroup.mk ⟨x, hx⟩

theorem cl_add (j k : ℤ) (x y : F) (hx : x ∈ ball K v j) (hy : y ∈ ball K v j) :
    cl j k (x + y) ((ball K v j).add_mem hx hy) = cl j k x hx + cl j k y hy := rfl

theorem cl_zero (j k : ℤ) : cl j k (0 : F) (ball K v j).zero_mem = 0 := rfl

section Rep

variable {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) →* Module.End ℂ V)

abbrev nU (x : HeightOneSpectrum.adicCompletion K v) : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) :=
  AutomorphicForm.unipotentGL2 x

theorem nU_add (x y : F) : (nU (x + y) : G) = nU x * nU y := AutomorphicForm.unipotentGL2_add x y

theorem nU_zero : (nU (0 : F) : G) = 1 := AutomorphicForm.unipotentGL2_zero

theorem act_mul (g h : G) (w : V) : π (g * h) w = π g (π h w) := by
  rw [map_mul, Module.End.mul_apply]

theorem nU_comm_apply (x y : F) (w : V) : π (nU x) (π (nU y) w) = π (nU y) (π (nU x) w) := by
  rw [← act_mul, ← nU_add, add_comm, nU_add, act_mul]

def Fix (k : ℤ) (w : V) : Prop := ∀ t : F, Valued.v t ≤ WithZero.exp k → π (nU t) w = w

theorem Fix.mono {k k' : ℤ} {w : V} (h : Fix π k w) (hk : k' ≤ k) : Fix π k' w :=
  fun t ht => h t (ht.trans (WithZero.exp_le_exp.mpr hk))

theorem Fix.act {k : ℤ} {w : V} (h : Fix π k w) (x : F) : Fix π k (π (nU x) w) := by
  intro t ht
  rw [nU_comm_apply, h t ht]

theorem Fix.zero (k : ℤ) : Fix π k (0 : V) := fun t _ => by rw [map_zero]

theorem exists_fix (hsm : IsSmoothRep π) (w : V) : ∃ k : ℤ, Fix π k w := by
  have hopen : IsOpen ((repStabilizer π w : Subgroup G) : Set G) := hsm w
  have hcont : Continuous fun t : F => (nU t : G) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [AutomorphicForm.unipotentGL2_coe] <;> first | exact continuous_const | exact continuous_id
    · have : ∀ t : F, ((nU t : G)⁻¹ : G) = nU (-t) := by
        intro t
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← nU_add, neg_add_cancel, nU_zero]
      simp_rw [this]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [AutomorphicForm.unipotentGL2_coe] <;> first | exact continuous_const | exact continuous_neg
  have hpre : (fun t : F => (nU t : G)) ⁻¹' ((repStabilizer π w : Subgroup G) : Set G) ∈ nhds (0 : F) := by
    refine (hopen.preimage hcont).mem_nhds ?_
    show (nU (0 : F) : G) ∈ (repStabilizer π w : Subgroup G)
    rw [nU_zero]
    exact Subgroup.one_mem _
  obtain ⟨γ, hγ⟩ := (Valued.mem_nhds_zero).mp hpre
  set δ : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    intro h0
    have h1 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 *
        MonoidWithZeroHom.ValueGroup₀.embedding (γ⁻¹).1 = (1 : ℤᵐ⁰) := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨WithZero.log δ - 1, fun x hx => ?_⟩
  have hxδ : Valued.v x < δ := by
    calc Valued.v x ≤ WithZero.exp (WithZero.log δ - 1) := hx
      _ < WithZero.exp (WithZero.log δ) := WithZero.exp_lt_exp.mpr (by omega)
      _ = δ := WithZero.exp_log hδ0
  have hx' : Valued.v.restrict x < γ.1 := by
    rw [Valuation.restrict_lt_iff_lt_embedding]; rw [hδ] at hxδ; exact hxδ
  have hmem := hγ hx'
  simpa only [Set.mem_preimage, SetLike.mem_coe, mem_repStabilizer] using hmem

theorem act_eq_of_cl_eq {j k : ℤ} {w : V} (hw : Fix π k w) {a b : ball K v j}
    (h : (QuotientAddGroup.mk a : Q K v j k) = QuotientAddGroup.mk b) :
    π (nU (a : F)) w = π (nU (b : F)) w := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  have h' : Valued.v (-(a : F) + b) ≤ WithZero.exp k := h
  have hb : (b : F) = a + (-(a : F) + b) := by abel
  rw [hb, nU_add, act_mul, hw _ h']

theorem act_out_cl {j k : ℤ} {w : V} (hw : Fix π k w) (a : ball K v j) :
    π (nU (((QuotientAddGroup.mk a : Q K v j k).out : ball K v j) : F)) w = π (nU (a : F)) w :=
  act_eq_of_cl_eq π hw (QuotientAddGroup.out_eq' _)

private def _root_.WhittakerExistence.P (j k : ℤ) (θ : AddChar (Q K v j k) ℂ) : V →ₗ[ℂ] V :=
  ∑ q : Q K v j k, θ (-q) • (π (nU ((q.out : ball K v j) : F)) : V →ₗ[ℂ] V)

p2m_export "WhittakerExistence" "P"
theorem P_apply (j k : ℤ) (θ : AddChar (Q K v j k) ℂ) (w : V) :
    P π j k θ w = ∑ q : Q K v j k, θ (-q) • π (nU ((q.out : ball K v j) : F)) w := by
  simp [P, LinearMap.sum_apply, LinearMap.smul_apply]

theorem P_act (j k : ℤ) (θ : AddChar (Q K v j k) ℂ) (x : F) (w : V) :
    P π j k θ (π (nU x) w) = π (nU x) (P π j k θ w) := by
  rw [P_apply, P_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, nU_comm_apply]

theorem Fix.P {j k : ℤ} {w : V} (hw : Fix π k w) (θ : AddChar (Q K v j k) ℂ) : Fix π k (P π j k θ w) := by
  intro t ht
  rw [← P_act, hw t ht]

theorem act_P {j k : ℤ} {w : V} (hw : Fix π k w) (θ : AddChar (Q K v j k) ℂ) {b : F} (hb : b ∈ ball K v j) :
    π (nU b) (P π j k θ w) = θ (cl j k b hb) • P π j k θ w := by
  classical
  set β : Q K v j k := cl j k b hb with hβ
  rw [P_apply, map_sum, Finset.smul_sum]
  rw [← Equiv.sum_comp (Equiv.subRight β)]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Equiv.subRight_apply, map_smul]
  have h1 : π (nU b) (π (nU (((q - β).out : ball K v j) : F)) w) = π (nU ((q.out : ball K v j) : F)) w := by
    rw [← act_mul, ← nU_add]
    have : b + (((q - β).out : ball K v j) : F) = ((⟨b, hb⟩ + (q - β).out : ball K v j) : F) := rfl
    rw [this]
    apply act_eq_of_cl_eq π hw
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    show β + (q - β) = q
    abel
  have h2 : θ (-(q - β)) = θ β * θ (-q) := by
    rw [neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [h1, h2, smul_smul]

theorem P_act_of_mem {j k : ℤ} {w : V} (hw : Fix π k w) (θ : AddChar (Q K v j k) ℂ) {x : F}
    (hx : x ∈ ball K v j) : P π j k θ (π (nU x) w) = θ (cl j k x hx) • P π j k θ w := by
  rw [P_act, act_P π hw θ hx]

theorem sum_P {j k : ℤ} {w : V} (hw : Fix π k w) :
    ∑ θ : AddChar (Q K v j k) ℂ, P π j k θ w = (Fintype.card (Q K v j k) : ℂ) • w := by
  classical
  simp_rw [P_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have key : ∀ q : Q K v j k, (∑ θ : AddChar (Q K v j k) ℂ, θ (-q)) =
      if q = 0 then (Fintype.card (Q K v j k) : ℂ) else 0 := by
    intro q
    rw [AddChar.sum_apply_eq_ite]
    simp only [neg_eq_zero]
  simp_rw [key, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  have h := act_out_cl π hw (k := k) (0 : ball K v j)
  rw [QuotientAddGroup.mk_zero] at h
  rw [h]
  show π (nU (0 : F)) w = w
  rw [nU_zero, map_one, Module.End.one_apply]

theorem P_one_of_fix {k k₀ : ℤ} {w : V} (hw : Fix π k w) :
    P π k k₀ 1 w = (Fintype.card (Q K v k k₀) : ℂ) • w := by
  classical
  rw [P_apply]
  have : ∀ q : Q K v k k₀, (1 : AddChar (Q K v k k₀) ℂ) (-q) • π (nU ((q.out : ball K v k) : F)) w = w := by
    intro q
    rw [AddChar.one_apply, one_smul]
    exact hw _ (q.out : ball K v k).2
  simp_rw [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

theorem fix_P_one {k k₀ : ℤ} {w : V} (hw : Fix π k₀ w) : Fix π k (P π k k₀ 1 w) := by
  intro t ht
  rw [act_P π hw 1 (show t ∈ ball K v k from ht), AddChar.one_apply, one_smul]

theorem P_P {j j' k : ℤ} (hjj : j ≤ j') {w : V} (hw : Fix π k w) (θ : AddChar (Q K v j k) ℂ)
    (θ' : AddChar (Q K v j' k) ℂ)
    (hext : ∀ (x : F) (hx : x ∈ ball K v j), θ' (cl j' k x (ball_mono hjj hx)) = θ (cl j k x hx)) :
    P π j' k θ' (P π j k θ w) = (Fintype.card (Q K v j k) : ℂ) • P π j' k θ' w := by
  classical
  conv_lhs => rw [P_apply π j k θ w]
  rw [map_sum]
  have : ∀ q : Q K v j k,
      P π j' k θ' (θ (-q) • π (nU ((q.out : ball K v j) : F)) w) = P π j' k θ' w := by
    intro q
    rw [map_smul, P_act_of_mem π hw θ' (ball_mono hjj (q.out : ball K v j).2), hext _ (q.out : ball K v j).2,
      smul_smul]
    have hq : cl j k ((q.out : ball K v j) : F) (q.out : ball K v j).2 = q := QuotientAddGroup.out_eq' q
    rw [hq, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]
  simp_rw [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

theorem ext_of_ne_zero {j j' k : ℤ} (hjj : j ≤ j') {w : V} (hw : Fix π k w) (θ : AddChar (Q K v j k) ℂ)
    (θ' : AddChar (Q K v j' k) ℂ) (hne : P π j' k θ' (P π j k θ w) ≠ 0) :
    ∀ (x : F) (hx : x ∈ ball K v j), θ' (cl j' k x (ball_mono hjj hx)) = θ (cl j k x hx) := by
  intro x hx
  have hu : Fix π k (P π j k θ w) := hw.P π θ
  have h1 := act_P π hu θ' (ball_mono hjj hx)
  have h2 : π (nU x) (P π j' k θ' (P π j k θ w)) = θ (cl j k x hx) • P π j' k θ' (P π j k θ w) := by
    rw [← P_act, act_P π hw θ hx, map_smul]
  exact smul_left_injective ℂ hne (h1.symm.trans h2)

theorem exists_next {j j' k : ℤ} (hjj : j ≤ j') {w : V} (hw : Fix π k w) (θ : AddChar (Q K v j k) ℂ)
    (hne : P π j k θ w ≠ 0) :
    ∃ θ' : AddChar (Q K v j' k) ℂ,
      (∀ (x : F) (hx : x ∈ ball K v j), θ' (cl j' k x (ball_mono hjj hx)) = θ (cl j k x hx)) ∧
        P π j' k θ' w ≠ 0 := by
  classical
  have hu : Fix π k (P π j k θ w) := hw.P π θ
  have hsum := sum_P π hu (j := j')
  have hne' : ∑ θ' : AddChar (Q K v j' k) ℂ, P π j' k θ' (P π j k θ w) ≠ 0 := by
    rw [hsum]
    exact smul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hne
  obtain ⟨θ', -, hθ'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have hext := ext_of_ne_zero π hjj hw θ θ' hθ'
  refine ⟨θ', hext, ?_⟩
  rw [P_P π hjj hw θ θ' hext] at hθ'
  exact (smul_ne_zero_iff.mp hθ').2

theorem exists_start {j₀ k : ℤ} {w₀ : V} (hw : Fix π k w₀) {x₀ : F} (hx₀ : x₀ ∈ ball K v j₀)
    (hne : π (nU x₀) w₀ ≠ w₀) :
    ∃ θ : AddChar (Q K v j₀ k) ℂ, θ (cl j₀ k x₀ hx₀) ≠ 1 ∧ P π j₀ k θ w₀ ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hne
  have hsum := sum_P π hw (j := j₀)
  have key : π (nU x₀) (∑ θ : AddChar (Q K v j₀ k) ℂ, P π j₀ k θ w₀) = ∑ θ : AddChar (Q K v j₀ k) ℂ, P π j₀ k θ w₀ := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [act_P π hw θ hx₀]
    by_cases hθ : θ (cl j₀ k x₀ hx₀) = 1
    · rw [hθ, one_smul]
    · rw [h θ hθ, smul_zero]
  rw [hsum, map_smul] at key
  exact smul_right_injective V (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) key

end Rep

section Glue

variable {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) →* Module.End ℂ V)

def extF (k j : ℤ) (θ : AddChar (Q K v j k) ℂ) : F → ℂ := fun x =>
  open scoped Classical in
  if hx : x ∈ ball K v j then θ (cl j k x hx) else 1

theorem extF_apply_of_mem (k j : ℤ) (θ : AddChar (Q K v j k) ℂ) {x : F} (hx : x ∈ ball K v j) :
    extF k j θ x = θ (cl j k x hx) := by
  unfold extF
  rw [dif_pos hx]

def Good (k : ℤ) (w₀ : V) (j : ℤ) (f : F → ℂ) : Prop :=
  ∃ θ : AddChar (Q K v j k) ℂ, f = extF k j θ ∧ P π j k θ w₀ ≠ 0

theorem good_step {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j : ℤ} {f : F → ℂ} (hf : Good π k w₀ j f) :
    ∃ f' : F → ℂ, Good π k w₀ (j + 1) f' ∧ ∀ x ∈ ball K v j, f' x = f x := by
  obtain ⟨θ, rfl, hne⟩ := hf
  obtain ⟨θ', hext, hne'⟩ := exists_next π (show j ≤ j + 1 by omega) hw θ hne
  refine ⟨extF k (j + 1) θ', ⟨θ', rfl, hne'⟩, fun x hx => ?_⟩
  rw [extF_apply_of_mem k (j + 1) θ' (ball_mono (show j ≤ j + 1 by omega) hx), extF_apply_of_mem k j θ hx]
  exact hext x hx

def seq {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀) :
    (n : ℕ) → {f : F → ℂ // Good π k w₀ (j₀ + n) f}
  | 0 => ⟨f₀, by simpa using h₀⟩
  | n + 1 =>
    ⟨Classical.choose (good_step π hw (seq hw h₀ n).2), by
      have h := (Classical.choose_spec (good_step π hw (seq hw h₀ n).2)).1
      have e : (j₀ : ℤ) + ((n + 1 : ℕ) : ℤ) = j₀ + (n : ℕ) + 1 := by push_cast; ring
      rw [e]
      exact h⟩

theorem seq_zero {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀) :
    (seq π hw h₀ 0).1 = f₀ := rfl

theorem seq_succ_apply {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀)
    (n : ℕ) (x : F) (hx : x ∈ ball K v (j₀ + n)) :
    (seq π hw h₀ (n + 1)).1 x = (seq π hw h₀ n).1 x :=
  (Classical.choose_spec (good_step π hw (seq π hw h₀ n).2)).2 x hx

theorem seq_apply_of_le {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀)
    {m n : ℕ} (hmn : m ≤ n) (x : F) (hx : x ∈ ball K v (j₀ + m)) :
    (seq π hw h₀ n).1 x = (seq π hw h₀ m).1 x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [seq_succ_apply π hw h₀ n x (ball_mono (by omega) hx), ih]

def lvl (j₀ : ℤ) (x : F) : ℕ := (WithZero.log (Valued.v x) - j₀).toNat

theorem mem_ball_lvl (j₀ : ℤ) (x : F) : x ∈ ball K v (j₀ + lvl j₀ x) := by
  rw [mem_ball]
  by_cases hx : Valued.v x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    have := Int.self_le_toNat (WithZero.log (Valued.v x) - j₀)
    simp only [lvl]
    omega

def psiFun {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀) (x : F) : ℂ :=
  (seq π hw h₀ (lvl j₀ x)).1 x

theorem psiFun_eq {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀)
    {x : F} {n : ℕ} (hx : x ∈ ball K v (j₀ + n)) : psiFun π hw h₀ x = (seq π hw h₀ n).1 x := by
  unfold psiFun
  rcases le_total n (lvl j₀ x) with h | h
  · exact seq_apply_of_le π hw h₀ h x hx
  · exact (seq_apply_of_le π hw h₀ h x (mem_ball_lvl j₀ x)).symm

def psi {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀) :
    AddChar (HeightOneSpectrum.adicCompletion K v) ℂ where
  toFun := psiFun π hw h₀
  map_zero_eq_one' := by
    obtain ⟨θ, hθ, -⟩ := (seq π hw h₀ 0).2
    have h0 : (0 : F) ∈ ball K v (j₀ + (0 : ℕ)) := AddSubgroup.zero_mem _
    rw [psiFun_eq π hw h₀ h0, hθ, extF_apply_of_mem _ _ θ h0]
    exact AddChar.map_zero_eq_one θ
  map_add_eq_mul' := by
    intro x y
    set n : ℕ := max (lvl j₀ x) (max (lvl j₀ y) (lvl j₀ (x + y))) with hn
    have h1 : lvl j₀ x ≤ n := le_max_left _ _
    have h2 : lvl j₀ y ≤ n := (le_max_left _ _).trans (le_max_right _ _)
    have h3 : lvl j₀ (x + y) ≤ n := (le_max_right _ _).trans (le_max_right _ _)
    have hx : x ∈ ball K v (j₀ + n) := ball_mono (by omega) (mem_ball_lvl j₀ x)
    have hy : y ∈ ball K v (j₀ + n) := ball_mono (by omega) (mem_ball_lvl j₀ y)
    have hxy : x + y ∈ ball K v (j₀ + n) := ball_mono (by omega) (mem_ball_lvl j₀ (x + y))
    obtain ⟨θ, hθ, -⟩ := (seq π hw h₀ n).2
    rw [psiFun_eq π hw h₀ hxy, psiFun_eq π hw h₀ hx, psiFun_eq π hw h₀ hy, hθ,
      extF_apply_of_mem _ _ θ hxy, extF_apply_of_mem _ _ θ hx, extF_apply_of_mem _ _ θ hy,
      ← AddChar.map_add_eq_mul]
    rfl

theorem psi_apply {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀) (x : F) :
    psi π hw h₀ x = psiFun π hw h₀ x := rfl

def Killed {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀) (y : V) : Prop :=
  ∃ (J₀ : ℕ) (K₀ : ℤ), ∀ k₀ : ℤ, k₀ ≤ K₀ → ∀ n : ℕ, J₀ ≤ n →
    ∀ θ : AddChar (Q K v (j₀ + n) k) ℂ, (seq π hw h₀ n).1 = extF k (j₀ + n) θ →
      P π (j₀ + n) k θ (P π k k₀ 1 y) = 0

theorem killed_zero {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀) :
    Killed π hw h₀ 0 :=
  ⟨0, 0, fun k₀ _ n _ θ _ => by rw [map_zero, map_zero]⟩

theorem killed_add {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀)
    {a b : V} (ha : Killed π hw h₀ a) (hb : Killed π hw h₀ b) : Killed π hw h₀ (a + b) := by
  obtain ⟨Ja, Ka, ha⟩ := ha
  obtain ⟨Jb, Kb, hb⟩ := hb
  refine ⟨max Ja Jb, min Ka Kb, fun k₀ hk₀ n hn θ hθ => ?_⟩
  rw [map_add, map_add, ha k₀ (hk₀.trans (min_le_left _ _)) n ((le_max_left _ _).trans hn) θ hθ,
    hb k₀ (hk₀.trans (min_le_right _ _)) n ((le_max_right _ _).trans hn) θ hθ, add_zero]

theorem killed_smul {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ} (h₀ : Good π k w₀ j₀ f₀)
    (c : ℂ) {a : V} (ha : Killed π hw h₀ a) : Killed π hw h₀ (c • a) := by
  obtain ⟨Ja, Ka, ha⟩ := ha
  refine ⟨Ja, Ka, fun k₀ hk₀ n hn θ hθ => ?_⟩
  rw [map_smul, map_smul, ha k₀ hk₀ n hn θ hθ, smul_zero]

theorem killed_gen (hsm : IsSmoothRep π) {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ}
    (h₀ : Good π k w₀ j₀ f₀) (x : F) (w : V) :
    Killed π hw h₀ (π (nU x) w - psi π hw h₀ x • w) := by
  obtain ⟨kw, hkw⟩ := exists_fix π hsm w
  refine ⟨lvl j₀ x, min kw k, fun k₀ hk₀ n hn θ hθ => ?_⟩
  have hx : x ∈ ball K v (j₀ + n) := ball_mono (by omega) (mem_ball_lvl j₀ x)
  have hwk₀ : Fix π k₀ w := hkw.mono π (hk₀.trans (min_le_left _ _))
  have hwbar : Fix π k (P π k k₀ 1 w) := fix_P_one π hwk₀
  have hψx : psi π hw h₀ x = θ (cl (j₀ + n) k x hx) := by
    rw [psi_apply, psiFun_eq π hw h₀ hx, hθ, extF_apply_of_mem _ _ θ hx]
  rw [map_sub, map_smul, P_act, map_sub, map_smul, P_act_of_mem π hwbar θ hx, hψx, sub_self]

theorem not_mem_span (hsm : IsSmoothRep π) {k : ℤ} {w₀ : V} (hw : Fix π k w₀) {j₀ : ℤ} {f₀ : F → ℂ}
    (h₀ : Good π k w₀ j₀ f₀) :
    w₀ ∉ Submodule.span ℂ {y : V | ∃ (x : F) (w : V), y = π (nU x) w - psi π hw h₀ x • w} := by
  intro hmem
  have hK : Killed π hw h₀ w₀ := by
    refine Submodule.span_induction (p := fun y _ => Killed π hw h₀ y) ?_ ?_ ?_ ?_ hmem
    · rintro y ⟨x, w, rfl⟩
      exact killed_gen π hsm hw h₀ x w
    · exact killed_zero π hw h₀
    · intro a b _ _ ha hb
      exact killed_add π hw h₀ ha hb
    · intro c a _ ha
      exact killed_smul π hw h₀ c ha
  obtain ⟨J₀, K₀, hJK⟩ := hK
  obtain ⟨θ, hθ, hne⟩ := (seq π hw h₀ J₀).2
  have h := hJK K₀ le_rfl J₀ le_rfl θ hθ
  rw [P_one_of_fix π hw, map_smul] at h
  exact hne ((smul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem main (hsm : IsSmoothRep π) (x₀ : F) (w₀ : V) (hw₀ : π (nU x₀) w₀ ≠ w₀) :
    ∃ ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ, ψ ≠ 1 ∧
      ∃ Λ : V →ₗ[ℂ] ℂ, Λ ≠ 0 ∧ ∀ (x : F) (w : V), Λ (π (nU x) w) = ψ x * Λ w := by
  obtain ⟨k, hw⟩ := exists_fix π hsm w₀
  obtain ⟨j₀, hx₀⟩ := exists_mem_ball x₀
  obtain ⟨θ₀, hθ₀, hne₀⟩ := exists_start π hw hx₀ hw₀
  have h₀ : Good π k w₀ j₀ (extF k j₀ θ₀) := ⟨θ₀, rfl, hne₀⟩
  refine ⟨psi π hw h₀, ?_, ?_⟩
  · intro h1
    apply hθ₀
    have hx₀' : x₀ ∈ ball K v (j₀ + (0 : ℕ)) := by simpa using hx₀
    have e1 : psi π hw h₀ x₀ = 1 := by rw [h1, AddChar.one_apply]
    rw [psi_apply, psiFun_eq π hw h₀ hx₀', seq_zero, extF_apply_of_mem _ _ θ₀ hx₀] at e1
    exact e1
  · have hnot := not_mem_span π hsm hw h₀
    obtain ⟨Λ, hΛw₀, hker⟩ := Submodule.exists_le_ker_of_notMem hnot
    refine ⟨Λ, ?_, fun x w => ?_⟩
    · intro h
      rw [h] at hΛw₀
      exact hΛw₀ rfl
    · have hgen : π (nU x) w - psi π hw h₀ x • w ∈
          Submodule.span ℂ {y : V | ∃ (x : F) (w : V), y = π (nU x) w - psi π hw h₀ x • w} :=
        Submodule.subset_span ⟨x, w, rfl⟩
      have h2 := hker hgen
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h2
      exact h2

end Glue

end WhittakerExistence
p2m_reactivate "P2MW.S_LocalGL2_exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne.WhittakerExistence"

end
p2m_reactivate "P2MW.S_LocalGL2_exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne.WhittakerExistence"

open IsDedekindDomain NumberField FLT.SmoothAdmissibleSchurCommutant in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : GL (Fin 2) (v.adicCompletion K) →* Module.End ℂ V)
    (hsm : IsSmoothRep π)
    (x₀ : v.adicCompletion K) (w₀ : V) (hw₀ : π (AutomorphicForm.unipotentGL2 x₀) w₀ ≠ w₀) :
    ∃ ψ : AddChar (v.adicCompletion K) ℂ, ψ ≠ 1 ∧
      ∃ Λ : V →ₗ[ℂ] ℂ, Λ ≠ 0 ∧
        ∀ (x : v.adicCompletion K) (w : V), Λ (π (AutomorphicForm.unipotentGL2 x) w) = ψ x * Λ w :=
  WhittakerExistence.main π hsm x₀ w₀ hw₀

end S_LocalGL2_exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne
end P2MW
export P2MW.S_LocalGL2_exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne (solution)
