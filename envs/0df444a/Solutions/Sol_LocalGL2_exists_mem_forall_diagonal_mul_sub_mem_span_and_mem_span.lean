-- Prove2me | solution 1 for LocalGL2.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c0b67258-77b6-5a6a-a26b-b0b0499a2a0e

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 0
set_option linter.style.longLine false

noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero

namespace KirillovBallCutoffFn

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
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

theorem v_mul_le {x y : F} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a) (hy : Valued.v y ≤ WithZero.exp b) :
    Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem v_sub_le {x y : F} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) : Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]
  refine (Valuation.map_add _ _ _).trans (max_le hx ?_)
  rwa [Valuation.map_neg]

theorem exp_succ_le_of_exp_lt {y : F} {i : ℤ} (h : WithZero.exp i < Valued.v y) :
    WithZero.exp (i + 1) ≤ Valued.v y := by
  have hy : Valued.v y ≠ 0 := (lt_of_le_of_lt zero_le' h).ne'
  rw [← WithZero.exp_log hy] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem exists_v_le_exp (x : F) : ∃ j : ℤ, Valued.v x ≤ WithZero.exp j := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), by rw [← WithZero.exp_log hx, WithZero.log_exp]⟩

theorem lt_exp_iff_le_exp_sub_one (x : ℤᵐ⁰) (d : ℤ) : x < WithZero.exp d ↔ x ≤ WithZero.exp (d - 1) := by
  by_cases hx : x = 0
  · rw [hx]; exact ⟨fun _ => zero_le', fun _ => WithZero.exp_pos⟩
  · rw [← WithZero.exp_log hx, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

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

theorem out_sub_mem {j k : ℤ} (q : Q K v j k) (x : ball K v j) (h : (QuotientAddGroup.mk x : Q K v j k) = q) :
    ((q.out : ball K v j) : F) - x ∈ ball K v k := by
  have h' : (QuotientAddGroup.mk x : Q K v j k) = QuotientAddGroup.mk q.out := by
    rw [h, QuotientAddGroup.out_eq']
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h'
  have : ((-x + q.out : ball K v j) : F) = ((q.out : ball K v j) : F) - x := by
    push_cast; ring
  rwa [this] at h'

theorem out_zero_mem (j k : ℤ) : (((0 : Q K v j k).out : ball K v j) : F) ∈ ball K v k := by
  simpa using out_sub_mem (0 : Q K v j k) 0 (by rw [QuotientAddGroup.mk_zero])

theorem exists_ball_of_eventually {p : F → Prop} (h : ∀ᶠ t in nhds (0 : F), p t) :
    ∃ m : ℤ, ∀ t : F, Valued.v t ≤ WithZero.exp m → p t := by
  obtain ⟨γ, hγ⟩ := (Valued.mem_nhds_zero).mp h
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
  exact hγ hx'

theorem exists_level (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (m₀ : ℤ)
    (hm₀ : ∀ x : F, Valued.v x ≤ WithZero.exp m₀ → ψ x = 1) :
    ∃ ℓ : ℤ, (∀ x : F, Valued.v x ≤ WithZero.exp ℓ → ψ x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp (ℓ + 1) ∧ ψ x ≠ 1 := by
  classical
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : F, ψ x₁ ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (DFunLike.ext ψ 1 fun x => by rw [h x, AddChar.one_apply])
  have hx₁0 : Valued.v x₁ ≠ 0 := by
    intro h0
    apply hx₁
    exact hm₀ x₁ (by rw [h0]; exact zero_le')
  set M : ℤ := WithZero.log (Valued.v x₁) with hM
  have hvx₁ : Valued.v x₁ = WithZero.exp M := by rw [hM, WithZero.exp_log hx₁0]
  let P : ℤ → Prop := fun m => ∀ x : F, Valued.v x ≤ WithZero.exp m → ψ x = 1
  have hPM : ¬ P M := fun h => hx₁ (h x₁ hvx₁.le)
  have hmono : ∀ m m' : ℤ, m' ≤ m → P m → P m' := fun m m' hle h x hx =>
    h x (hx.trans (WithZero.exp_le_exp.mpr hle))
  have hlt : m₀ < M := by
    by_contra hle
    push Not at hle
    exact hPM (hmono _ _ hle hm₀)
  have key : ∀ n : ℕ, P (m₀ + n) → ¬ P (m₀ + n + 1) →
      ∃ ℓ : ℤ, P ℓ ∧ ∃ x : F, Valued.v x ≤ WithZero.exp (ℓ + 1) ∧ ψ x ≠ 1 := by
    intro n hn hn1
    refine ⟨m₀ + n, hn, ?_⟩
    by_contra h
    push Not at h
    exact hn1 fun x hx => h x hx
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M = m₀ + N + 1 := ⟨(M - m₀ - 1).toNat, by omega⟩
  have : ∃ n : ℕ, n ≤ N ∧ P (m₀ + n) ∧ ¬ P (m₀ + n + 1) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ n : ℕ, n ≤ N + 1 → P (m₀ + n) := by
      intro n
      induction n with
      | zero => intro _; simpa using hm₀
      | succ n ih =>
        intro hn
        have h := hcon n (by omega) (ih (by omega))
        push_cast
        rwa [← add_assoc]
    have := hall (N + 1) le_rfl
    apply hPM
    rw [hN]
    push_cast at this
    rwa [← add_assoc] at this
  obtain ⟨n, -, hn, hn1⟩ := this
  exact key n hn hn1

structure LevelData (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ) (ℓ : ℤ) : Prop where
  triv : ∀ x : HeightOneSpectrum.adicCompletion K v, Valued.v x ≤ WithZero.exp ℓ → ψ x = 1
  wit : ∃ y : HeightOneSpectrum.adicCompletion K v, Valued.v y ≤ WithZero.exp (ℓ + 1) ∧ ψ y ≠ 1

theorem exists_levelData {ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ} (hψ : ψ ≠ 1)
    (hψ0 : ∀ᶠ t in nhds (0 : F), ψ t = 1) : ∃ ℓ : ℤ, LevelData ψ ℓ := by
  obtain ⟨m₀, hm₀⟩ := exists_ball_of_eventually hψ0
  obtain ⟨ℓ, h1, h2⟩ := exists_level ψ hψ m₀ hm₀
  exact ⟨ℓ, ⟨h1, h2⟩⟩

section Level

variable {ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ} {ℓ : ℤ} (hL : LevelData ψ ℓ)
include hL

theorem psi_mul_eq_one {b c : F} {i k : ℤ} (hb : Valued.v b ≤ WithZero.exp i) (hc : Valued.v c ≤ WithZero.exp k)
    (h : i + k ≤ ℓ) : ψ (b * c) = 1 :=
  hL.triv _ ((v_mul_le hb hc).trans (WithZero.exp_le_exp.mpr h))

theorem exists_freq {q : F} {k : ℤ} (hq : ¬ Valued.v q ≤ WithZero.exp k) :
    ∃ β : F, Valued.v β ≤ WithZero.exp (ℓ - k) ∧ ψ (β * q) ≠ 1 := by
  obtain ⟨y, hy, hψy⟩ := hL.wit
  have hq' : WithZero.exp (k + 1) ≤ Valued.v q := exp_succ_le_of_exp_lt (not_le.mp hq)
  have hq0 : Valued.v q ≠ 0 := (lt_of_lt_of_le WithZero.exp_pos hq').ne'
  have hq0' : q ≠ 0 := by intro h; apply hq0; rw [h, Valuation.map_zero]
  refine ⟨y * q⁻¹, ?_, ?_⟩
  · rw [Valuation.map_mul, map_inv₀]
    have h1 : (Valued.v q)⁻¹ ≤ WithZero.exp (-(k + 1)) := by
      rw [WithZero.exp_neg]
      exact inv_anti₀ WithZero.exp_pos hq'
    calc Valued.v y * (Valued.v q)⁻¹ ≤ WithZero.exp (ℓ + 1) * WithZero.exp (-(k + 1)) := mul_le_mul' hy h1
      _ = WithZero.exp (ℓ - k) := by rw [← WithZero.exp_add]; congr 1; ring
  · rwa [inv_mul_cancel_right₀ hq0']

theorem forall_psi_mul_eq_one_iff (c : F) (j : ℤ) :
    (∀ x : F, Valued.v x ≤ WithZero.exp j → ψ (c * x) = 1) ↔ Valued.v c ≤ WithZero.exp (ℓ - j) := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨β, hβ, hne⟩ := exists_freq hL hc
    have hβ' : Valued.v β ≤ WithZero.exp j := by
      have : ℓ - (ℓ - j) = j := by ring
      rwa [this] at hβ
    exact hne (by rw [mul_comm]; exact h β hβ')
  · intro hc x hx
    exact psi_mul_eq_one hL hc hx (by omega)

def theta (j k : ℤ) (c : F) (hc : Valued.v c ≤ WithZero.exp (ℓ - k)) : AddChar (Q K v j k) ℂ where
  toFun q := ψ (c * ((q.out : ball K v j) : F))
  map_zero_eq_one' := psi_mul_eq_one hL hc (out_zero_mem j k) (by omega)
  map_add_eq_mul' q q' := by
    have hmem : (((q + q').out : ball K v j) : F) - ((q.out : ball K v j) + (q'.out : ball K v j) : F) ∈
        ball K v k := by
      have := out_sub_mem (q + q') ((q.out : ball K v j) + q'.out)
        (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'])
      simpa using this
    have e : c * (((q + q').out : ball K v j) : F) =
        c * ((((q + q').out : ball K v j) : F) - ((q.out : ball K v j) + (q'.out : ball K v j) : F)) +
          (c * ((q.out : ball K v j) : F) + c * ((q'.out : ball K v j) : F)) := by ring
    rw [e, AddChar.map_add_eq_mul, psi_mul_eq_one hL hc hmem (by omega), one_mul, AddChar.map_add_eq_mul]

theorem theta_apply (j k : ℤ) (c : F) (hc : Valued.v c ≤ WithZero.exp (ℓ - k)) (q : Q K v j k) :
    theta hL j k c hc q = ψ (c * ((q.out : ball K v j) : F)) := rfl

theorem theta_cl (j k : ℤ) (c : F) (hc : Valued.v c ≤ WithZero.exp (ℓ - k)) (s : F) (hs : s ∈ ball K v j) :
    theta hL j k c hc (cl j k s hs) = ψ (c * s) := by
  rw [theta_apply]
  have hmem := out_sub_mem (cl j k s hs) ⟨s, hs⟩ rfl
  have e : c * (((cl j k s hs).out : ball K v j) : F) =
      c * ((((cl j k s hs).out : ball K v j) : F) - s) + c * s := by ring
  rw [e, AddChar.map_add_eq_mul, psi_mul_eq_one hL hc hmem (by omega), one_mul]

end Level

abbrev nU (x : HeightOneSpectrum.adicCompletion K v) : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) :=
  AutomorphicForm.unipotentGL2 x

theorem nU_coe (x : F) : ((nU x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem gl_eq_of_entries {g h : G}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G) (i j : Fin 2) :
    ((g * h : G) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem nU_add (x y : F) : (nU (x + y) : G) = nU x * nU y := AutomorphicForm.unipotentGL2_add x y

theorem nU_zero : (nU (0 : F) : G) = 1 := AutomorphicForm.unipotentGL2_zero

theorem torus_mul_nU (t : G) (h01 : (t : Mat) 0 1 = 0) (h10 : (t : Mat) 1 0 = 0) (h11 : (t : Mat) 1 1 = 1)
    (x : F) : t * nU x = nU ((t : Mat) 0 0 * x) * t := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, h01, h10, h11]

theorem continuous_nU : Continuous fun x : F => (nU x : G) := by
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

theorem eventually_nU_mem {S₀ : Subgroup G} (hS : IsOpen (S₀ : Set G)) : ∀ᶠ t in nhds (0 : F), (nU t : G) ∈ S₀ := by
  have : (fun t : F => (nU t : G)) ⁻¹' (S₀ : Set G) ∈ nhds (0 : F) := by
    refine (hS.preimage continuous_nU).mem_nhds ?_
    show (nU (0 : F) : G) ∈ S₀
    rw [nU_zero]; exact S₀.one_mem
  exact this

def R (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun U := fun g => U (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem R_apply (h : G) (U : G → ℂ) : R h U = fun g => U (g * h) := rfl

theorem R_mul (h k : G) (U : G → ℂ) : R (h * k) U = R h (R k U) := by
  simp only [R_apply, mul_assoc]

section Main

variable {ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ}
  {S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)}

variable (ψ S) in

def Dset : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ) :=
  {V | ∃ U ∈ S, ∃ x : F, V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - ψ x • U}

theorem R_nU_sub_mem_Dset {U : G → ℂ} (hU : U ∈ S) (x : F) : R (nU x) U - ψ x • U ∈ Dset ψ S :=
  ⟨U, hU, x, rfl⟩

theorem mem_span_of_fixed {U : G → ℂ} (hU : U ∈ S) {y : F} (hfix : R (nU y) U = U) (hy : ψ y ≠ 1) :
    U ∈ Submodule.span ℂ (Dset ψ S) := by
  have h1 : R (nU y) U - ψ y • U ∈ Submodule.span ℂ (Dset ψ S) := Submodule.subset_span (R_nU_sub_mem_Dset hU y)
  rw [hfix] at h1
  have h2 : U - ψ y • U = (1 - ψ y) • U := by rw [sub_smul, one_smul]
  rw [h2] at h1
  have h3 : (1 - ψ y) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have := Submodule.smul_mem _ (1 - ψ y)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ h3, one_smul] at this

theorem main (hψ : ψ ≠ 1) (hψ0 : ∀ᶠ t in nhds (0 : F), ψ t = 1)
    (hstab : ∀ U ∈ S, ∀ k : G, (fun g => U (g * k)) ∈ S)
    (W : G → ℂ) (hW : W ∈ S)
    (hsmW : ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W)
    (a₀ : F) (δ : (ℤᵐ⁰)ˣ) :
    ∃ W' ∈ S, ∀ t : G, (t : Mat) 0 1 = 0 → (t : Mat) 1 0 = 0 → (t : Mat) 1 1 = 1 →
      (Valued.v ((t : Mat) 0 0 - a₀) < (δ : ℤᵐ⁰) →
        (fun g => W' (g * t)) - (fun g => W (g * t)) ∈ Submodule.span ℂ (Dset ψ S)) ∧
      (¬ Valued.v ((t : Mat) 0 0 - a₀) < (δ : ℤᵐ⁰) →
        (fun g => W' (g * t)) ∈ Submodule.span ℂ (Dset ψ S)) := by
  classical

  obtain ⟨ℓ, hL⟩ := exists_levelData hψ hψ0

  set d : ℤ := WithZero.log (δ : ℤᵐ⁰) with hd
  have hδ : (δ : ℤᵐ⁰) = WithZero.exp d := by rw [hd, WithZero.exp_log δ.ne_zero]
  set j : ℤ := ℓ - d + 1 with hj
  have hball : ∀ c : F, Valued.v c < (δ : ℤᵐ⁰) ↔ ∀ x : F, Valued.v x ≤ WithZero.exp j → ψ (c * x) = 1 := by
    intro c
    rw [forall_psi_mul_eq_one_iff hL, hδ, lt_exp_iff_le_exp_sub_one]
    have : ℓ - j = d - 1 := by rw [hj]; ring
    rw [this]

  obtain ⟨K₀, hK₀, hfixW⟩ := hsmW
  obtain ⟨k₁, hk₁⟩ := exists_ball_of_eventually (eventually_nU_mem hK₀)
  obtain ⟨m₀, hm₀⟩ := exists_v_le_exp a₀
  set k : ℤ := min (min k₁ (ℓ - m₀)) j with hk
  have hkj : k ≤ j := min_le_right _ _
  have hk₁' : k ≤ k₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hkm : k ≤ ℓ - m₀ := (min_le_left _ _).trans (min_le_right _ _)
  have ha₀ : Valued.v a₀ ≤ WithZero.exp (ℓ - k) := hm₀.trans (WithZero.exp_le_exp.mpr (by omega))
  have hWfix : ∀ x : F, Valued.v x ≤ WithZero.exp k → R (nU x) W = W := fun x hx =>
    hfixW _ (hk₁ x (hx.trans (WithZero.exp_le_exp.mpr hk₁')))

  set N : ℕ := Fintype.card (Q K v j k) with hN
  have hN0 : (N : ℂ) ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_ne_zero
  set W' : G → ℂ := (N : ℂ)⁻¹ • ∑ q : Q K v j k, ψ (-(a₀ * ((q.out : ball K v j) : F))) • R (nU ((q.out : ball K v j) : F)) W
    with hW'
  have hW'S : W' ∈ S := by
    rw [hW']
    refine S.smul_mem _ (S.sum_mem fun q _ => S.smul_mem _ ?_)
    exact hstab W hW _
  refine ⟨W', hW'S, fun t h01 h10 h11 => ?_⟩

  set a : F := (t : Mat) 0 0 with ha
  have hRt : ∀ x : F, R t (R (nU x) W) = R (nU (a * x)) (R t W) := by
    intro x
    rw [← R_mul, ← R_mul, torus_mul_nU t h01 h10 h11]
  set U : G → ℂ := R t W with hU
  have hUS : U ∈ S := hstab W hW t

  have hRtW' : R t W' = (N : ℂ)⁻¹ • ∑ q : Q K v j k,
      ψ (-(a₀ * ((q.out : ball K v j) : F))) • R (nU (a * ((q.out : ball K v j) : F))) U := by
    rw [hW', map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, hRt]

  set c : ℂ := (N : ℂ)⁻¹ * ∑ q : Q K v j k, ψ ((a - a₀) * ((q.out : ball K v j) : F)) with hc
  have hcong : R t W' - c • U ∈ Submodule.span ℂ (Dset ψ S) := by
    have hpsi : ∀ q : Q K v j k, ψ (-(a₀ * ((q.out : ball K v j) : F))) * ψ (a * ((q.out : ball K v j) : F)) =
        ψ ((a - a₀) * ((q.out : ball K v j) : F)) := by
      intro q
      rw [← AddChar.map_add_eq_mul]
      congr 1; ring
    have e : R t W' - c • U = (N : ℂ)⁻¹ • ∑ q : Q K v j k, ψ (-(a₀ * ((q.out : ball K v j) : F))) •
        (R (nU (a * ((q.out : ball K v j) : F))) U - ψ (a * ((q.out : ball K v j) : F)) • U) := by
      rw [hRtW', hc, mul_smul, ← smul_sub, Finset.sum_smul, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_sub, smul_smul, hpsi]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span (R_nU_sub_mem_Dset hUS _)
  refine ⟨fun hlt => ?_, fun hnlt => ?_⟩
  ·
    have hc1 : c = 1 := by
      have hall := (hball (a - a₀)).mp hlt
      have : ∀ q : Q K v j k, ψ ((a - a₀) * ((q.out : ball K v j) : F)) = 1 := fun q =>
        hall _ (q.out : ball K v j).2
      rw [hc]
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [← hN, inv_mul_cancel₀ hN0]
    rw [hc1, one_smul] at hcong
    exact hcong
  ·
    by_cases hB : ∀ x : F, Valued.v x ≤ WithZero.exp k → ψ (a * x) = 1
    ·
      have hak : Valued.v a ≤ WithZero.exp (ℓ - k) := (forall_psi_mul_eq_one_iff hL a k).mp hB
      have hck : Valued.v (a - a₀) ≤ WithZero.exp (ℓ - k) := v_sub_le hak ha₀
      have hθ : theta hL j k (a - a₀) hck ≠ 1 := by
        intro h1
        apply hnlt
        rw [hball]
        intro x hx
        have := theta_cl hL j k (a - a₀) hck x hx
        rw [h1, AddChar.one_apply] at this
        exact this.symm
      have hsum : ∑ q : Q K v j k, ψ ((a - a₀) * ((q.out : ball K v j) : F)) = 0 := by
        have := AddChar.sum_eq_zero_of_ne_one hθ
        simpa only [theta_apply] using this
      have hc0 : c = 0 := by rw [hc, hsum, mul_zero]
      rw [hc0, zero_smul, sub_zero] at hcong
      exact hcong
    ·
      push Not at hB
      obtain ⟨x₀, hx₀, hne⟩ := hB
      have hfixU : R (nU (a * x₀)) U = U := by
        rw [hU, ← hRt, hWfix x₀ hx₀]
      have hUD : U ∈ Submodule.span ℂ (Dset ψ S) := mem_span_of_fixed hUS hfixU hne
      have e : R t W' = (R t W' - c • U) + c • U := by abel
      show R t W' ∈ Submodule.span ℂ (Dset ψ S)
      rw [e]
      exact Submodule.add_mem _ hcong (Submodule.smul_mem _ _ hUD)

end Main

end KirillovBallCutoffFn
p2m_reactivate "P2MW.S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span.KirillovBallCutoffFn"

end
p2m_reactivate "P2MW.S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span.KirillovBallCutoffFn"

open IsDedekindDomain NumberField in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (hψ : ψ ≠ 1)
    (hψ0 : ∀ᶠ t in nhds (0 : v.adicCompletion K), ψ t = 1)
    (S : Submodule ℂ (GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hstab : ∀ U ∈ S, ∀ k : GL (Fin 2) (v.adicCompletion K), (fun g => U (g * k)) ∈ S)
    (W : GL (Fin 2) (v.adicCompletion K) → ℂ) (hW : W ∈ S)
    (hsmW : ∃ K₀ : Subgroup (GL (Fin 2) (v.adicCompletion K)),
      IsOpen (K₀ : Set (GL (Fin 2) (v.adicCompletion K))) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W)
    (a₀ : v.adicCompletion K) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ W' ∈ S, ∀ t : GL (Fin 2) (v.adicCompletion K),
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = 1 →
      (Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) - (fun g => W (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (v.adicCompletion K) → ℂ | ∃ U ∈ S, ∃ x : v.adicCompletion K,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - ψ x • U}) ∧
      (¬ Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (v.adicCompletion K) → ℂ | ∃ U ∈ S, ∃ x : v.adicCompletion K,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - ψ x • U}) :=
  KirillovBallCutoffFn.main hψ hψ0 hstab W hW hsmW a₀ δ

end S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
end P2MW
export P2MW.S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span (solution)
