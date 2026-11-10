-- Prove2me | solution 1 for LindbladReach.MinDiss.theorem_2_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T18:55:51.124951+00:00
-- url     : https://prove2.me/submissions/22df3fb7-3e57-4388-a163-6f9fa4317198

import Mathlib
import Definitions.Def_LindbladReach_MinDiss_Setting

/-! Draft for ff92ed04 (LindbladReach.MinDiss.theorem_2_12). Map: scratch/probe/ff92ed04_skel.lean.
This file holds only PROVED children; the final theorem is added once all children compile. -/

set_option autoImplicit false

open LindbladReach.MinDiss
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

namespace FF92

/-! ## C1 basics of the closed class -/

theorem chan_closed {ι : Type} [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ)) :
    IsClosed (channelClosure S) :=
  isClosed_sInter fun _ hC => hC.1

theorem chan_comp {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set (Matrix ι ι ℂ)}
    {Φ Ψ : Superop ι} (h1 : Φ ∈ channelClosure S) (h2 : Ψ ∈ channelClosure S) :
    Φ.comp Ψ ∈ channelClosure S :=
  Set.mem_sInter.2 fun C hC =>
    hC.2.2.2 _ (Set.mem_sInter.1 h1 C hC) _ (Set.mem_sInter.1 h2 C hC)

theorem chan_unit {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set (Matrix ι ι ℂ)}
    {X : Matrix ι ι ℂ} (hX : X ∈ antiHermSpan S) {t : ℝ} (ht : 0 ≤ t) :
    unitaryConj (NormedSpace.exp ((t : ℂ) • X)) ∈ channelClosure S :=
  Set.mem_sInter.2 fun _ hC => hC.2.1 X hX t ht

theorem chan_jump {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set (Matrix ι ι ℂ)}
    {a : Matrix ι ι ℂ} (ha : a ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    NormedSpace.exp ((t : ℂ) • dissipator a) ∈ channelClosure S :=
  Set.mem_sInter.2 fun _ hC => hC.2.2.1 a ha t ht

theorem antiHermSpan_neg {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set (Matrix ι ι ℂ)}
    {X : Matrix ι ι ℂ} (hX : X ∈ antiHermSpan S) : -X ∈ antiHermSpan S :=
  ⟨Submodule.neg_mem _ hX.1, by rw [Matrix.conjTranspose_neg, hX.2]⟩

/-- A limit (t → ∞) of members of the class is a member (the class is closed). -/
theorem chan_limit {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set (Matrix ι ι ℂ)}
    {F : ℝ → Superop ι} {Φ : Superop ι} (hF : ∀ t : ℝ, 0 ≤ t → F t ∈ channelClosure S)
    (hlim : Filter.Tendsto F Filter.atTop (nhds Φ)) : Φ ∈ channelClosure S :=
  (chan_closed S).mem_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, hF⟩)

/-! ## exponentials of idempotents -/

theorem exp_smul_idem {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    {P : 𝔸} (hP : P * P = P) (s : ℂ) :
    NormedSpace.exp (s • P) = (1 - P) + Complex.exp s • P := by
  have hpow : ∀ n : ℕ, (s • P) ^ (n + 1) = s ^ (n + 1) • P := by
    intro n
    rw [smul_pow]
    congr 1
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hP]
  have key : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (s • P) ^ n)
      (NormedSpace.exp (s • P)) := NormedSpace.exp_series_hasSum_exp' (s • P)
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℂ)⁻¹) • s ^ n) • P)
      (NormedSpace.exp s • P) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) s).smul_const P
  have h3 : HasSum (fun n : ℕ => if n = 0 then (1 - P : 𝔸) else 0) (1 - P) :=
    hasSum_ite_eq 0 (1 - P)
  have h4 := h3.add h2
  have h5 : (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (s • P) ^ n) =
      fun n => (if n = 0 then (1 - P : 𝔸) else 0) + (((n.factorial : ℂ)⁻¹) • s ^ n) • P := by
    funext n
    cases n with
    | zero => simp
    | succ n => rw [hpow, if_neg (Nat.succ_ne_zero n), zero_add, smul_smul, smul_eq_mul]
  rw [h5] at key
  rw [Complex.exp_eq_exp_ℂ]
  exact key.unique h4

theorem exp_add_comm' {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    {x y : 𝔸} (h : Commute x y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) h
    ((NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _)

theorem tendsto_cexp_neg (c : ℂ) (hc : 0 < c.re) :
    Filter.Tendsto (fun t : ℝ => Complex.exp ((t : ℂ) * -c)) Filter.atTop (nhds 0) := by
  refine Complex.tendsto_exp_comap_re_atBot.comp (Filter.tendsto_comap_iff.2 ?_)
  have h : Filter.Tendsto (fun t : ℝ => -(t * c.re)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.atTop_mul_const hc)
  refine h.congr (fun t => ?_)
  simp only [Function.comp_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im]
  ring

/-! ## pinching, reset and the two jump generators -/

theorem reset_apply {k : ℕ} (i : Fin k) (ρ : Mat k) :
    resetQubit i ρ = Matrix.of fun ω ω' => if ω i = false ∧ ω' i = false then
      ∑ b : Bool, ρ (Function.update ω i b) (Function.update ω' i b) else 0 := rfl

theorem pinch_idem {k : ℕ} (i : Fin k) : pinch i * pinch i = pinch i := by
  ext ρ ω ω'
  by_cases h : ω i = ω' i <;> simp [ContinuousLinearMap.mul_def, h]

theorem pinch_mul_reset {k : ℕ} (i : Fin k) : pinch i * resetQubit i = resetQubit i := by
  ext ρ ω ω'
  cases h1 : ω i <;> cases h2 : ω' i <;> simp [ContinuousLinearMap.mul_def, reset_apply, h1, h2]

theorem reset_mul_pinch {k : ℕ} (i : Fin k) : resetQubit i * pinch i = resetQubit i := by
  ext ρ ω ω'
  simp [ContinuousLinearMap.mul_def, reset_apply, Fintype.sum_bool]

theorem reset_mul_reset {k : ℕ} (i : Fin k) : resetQubit i * resetQubit i = resetQubit i := by
  ext ρ ω ω'
  cases h1 : ω i <;> cases h2 : ω' i <;>
    simp [ContinuousLinearMap.mul_def, reset_apply, Fintype.sum_bool, h1, h2]

theorem dissipator_dephZ {k : ℕ} (i : Fin k) :
    dissipator (dephZ i) = (-4 : ℂ) • (1 - pinch i) := by
  ext ρ ω ω'
  cases h1 : ω i <;> cases h2 : ω' i <;>
    simp [dephZ, h1, h2, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring

theorem ampDamp_row {k : ℕ} (i : Fin k) (ω ζ : Idx k) :
    ampDamp i ω ζ = if ω i = false ∧ ζ = Function.update ω i true then 1 else 0 := by
  simp only [ampDamp, Matrix.of_apply]
  by_cases hc : ω i = false ∧ ζ i = true ∧ ∀ j, j ≠ i → ω j = ζ j
  · rw [if_pos hc, if_pos ⟨hc.1, Function.eq_update_iff.2 ⟨hc.2.1, fun x hx => (hc.2.2 x hx).symm⟩⟩]
  · rw [if_neg hc, if_neg]
    rintro ⟨h1, h2⟩
    obtain ⟨h3, h4⟩ := Function.eq_update_iff.1 h2
    exact hc ⟨h1, h3, fun x hx => (h4 x hx).symm⟩

theorem ampDamp_col {k : ℕ} (i : Fin k) (ζ ω : Idx k) :
    ampDamp i ζ ω = if ω i = true ∧ ζ = Function.update ω i false then 1 else 0 := by
  simp only [ampDamp, Matrix.of_apply]
  by_cases hc : ζ i = false ∧ ω i = true ∧ ∀ j, j ≠ i → ζ j = ω j
  · rw [if_pos hc, if_pos ⟨hc.2.1, Function.eq_update_iff.2 ⟨hc.1, hc.2.2⟩⟩]
  · rw [if_neg hc, if_neg]
    rintro ⟨h1, h2⟩
    obtain ⟨h3, h4⟩ := Function.eq_update_iff.1 h2
    exact hc ⟨h3, h1, h4⟩

theorem conjT_ampDamp {k : ℕ} (i : Fin k) (ω ζ : Idx k) :
    (ampDamp i)ᴴ ω ζ = if ω i = true ∧ ζ = Function.update ω i false then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, ampDamp_col]
  split_ifs <;> simp

theorem conjT_ampDamp' {k : ℕ} (i : Fin k) (ζ ω' : Idx k) :
    (ampDamp i)ᴴ ζ ω' = if ω' i = false ∧ ζ = Function.update ω' i true then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, ampDamp_row]
  split_ifs <;> simp

theorem ampDamp_mul {k : ℕ} (i : Fin k) (M : Mat k) (ω η : Idx k) :
    (ampDamp i * M) ω η = if ω i = false then M (Function.update ω i true) η else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [ampDamp_row]
  by_cases h : ω i = false <;> simp [h]

theorem mul_ampDamp {k : ℕ} (i : Fin k) (M : Mat k) (η ω' : Idx k) :
    (M * ampDamp i) η ω' = if ω' i = true then M η (Function.update ω' i false) else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [ampDamp_col]
  by_cases h : ω' i = true <;> simp [h]

theorem conjT_mul {k : ℕ} (i : Fin k) (M : Mat k) (ω η : Idx k) :
    ((ampDamp i)ᴴ * M) ω η = if ω i = true then M (Function.update ω i false) η else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [conjT_ampDamp]
  by_cases h : ω i = true <;> simp [h]

theorem mul_conjT {k : ℕ} (i : Fin k) (M : Mat k) (η ω' : Idx k) :
    (M * (ampDamp i)ᴴ) η ω' = if ω' i = false then M η (Function.update ω' i true) else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [conjT_ampDamp']
  by_cases h : ω' i = false <;> simp [h]

theorem dissipator_ampDamp {k : ℕ} (i : Fin k) :
    dissipator (ampDamp i) = (2 : ℂ) • resetQubit i - pinch i - 1 := by
  ext ρ ω ω'
  rw [dissipator_apply, Matrix.mul_assoc (ampDamp i)ᴴ (ampDamp i) ρ,
    ← Matrix.mul_assoc ρ (ampDamp i)ᴴ (ampDamp i)]
  have e1 := Function.update_eq_self i ω
  have e2 := Function.update_eq_self i ω'
  cases h1 : ω i <;> cases h2 : ω' i <;> rw [h1] at e1 <;> rw [h2] at e2 <;>
    simp [ampDamp_mul, mul_ampDamp, conjT_mul, mul_conjT, reset_apply, Fintype.sum_bool,
      h1, h2, e1, e2] <;> ring

/-! ## C5 and C4 -/

theorem chan_pinch {k : ℕ} (i : Fin k) (S : Set (Mat k)) (hz : dephZ i ∈ S) :
    pinch i ∈ channelClosure S := by
  have hA : (1 - pinch i) * (1 - pinch i) = 1 - pinch i :=
    IsIdempotentElem.one_sub (pinch_idem i)
  have hF : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • dissipator (dephZ i)) =
      (1 - (1 - pinch i)) + Complex.exp ((t : ℂ) * -4) • (1 - pinch i) := by
    intro t
    rw [dissipator_dephZ, smul_smul]
    exact exp_smul_idem (𝔸 := Superop (Idx k)) hA _
  have hl : Filter.Tendsto
      (fun t : ℝ => (1 - (1 - pinch i)) + Complex.exp ((t : ℂ) * -4) • (1 - pinch i))
      Filter.atTop (nhds ((1 - (1 - pinch i)) + (0 : ℂ) • (1 - pinch i))) :=
    tendsto_const_nhds.add ((tendsto_cexp_neg 4 (by norm_num)).smul_const _)
  have e0 : (0 : ℂ) • (1 - pinch i) = 0 := zero_smul ℂ (1 - pinch i : Superop (Idx k))
  have hv : (1 - (1 - pinch i)) + (0 : ℂ) • (1 - pinch i) = pinch i := by
    rw [e0, add_zero, sub_sub_cancel]
  rw [hv] at hl
  exact chan_limit (F := fun t : ℝ => NormedSpace.exp ((t : ℂ) • dissipator (dephZ i)))
    (fun t ht => chan_jump hz ht) (hl.congr fun t => (hF t).symm)

theorem chan_reset {k : ℕ} (i : Fin k) (S : Set (Mat k)) (ha : ampDamp i ∈ S) :
    resetQubit i ∈ channelClosure S := by
  have hQQ := pinch_idem i
  have hQR := pinch_mul_reset i
  have hRQ := reset_mul_pinch i
  have hRR := reset_mul_reset i
  have hA : (1 - pinch i) * (1 - pinch i) = 1 - pinch i := IsIdempotentElem.one_sub hQQ
  have hB : (pinch i - resetQubit i) * (pinch i - resetQubit i) = pinch i - resetQubit i := by
    simp only [sub_mul, mul_sub, hQQ, hQR, hRQ, hRR]; abel
  have hAB : (1 - pinch i) * (pinch i - resetQubit i) = 0 := by
    simp only [sub_mul, mul_sub, one_mul, hQQ, hQR]; abel
  have hBA : (pinch i - resetQubit i) * (1 - pinch i) = 0 := by
    simp only [sub_mul, mul_sub, mul_one, hQQ, hRQ]; abel
  have hL : dissipator (ampDamp i) =
      (-1 : ℂ) • (1 - pinch i) + (-2 : ℂ) • (pinch i - resetQubit i) := by
    rw [dissipator_ampDamp]; module
  have hAB' : ∀ ρ : Mat k, (1 - pinch i) ((pinch i - resetQubit i) ρ) = 0 := fun ρ =>
    congrArg (fun F : Superop (Idx k) => F ρ) hAB
  have hBA' : ∀ ρ : Mat k, (pinch i - resetQubit i) ((1 - pinch i) ρ) = 0 := fun ρ =>
    congrArg (fun F : Superop (Idx k) => F ρ) hBA
  have hcomm : ∀ s u : ℂ, Commute (s • (1 - pinch i)) (u • (pinch i - resetQubit i)) := by
    intro s u
    show (s • (1 - pinch i)) * (u • (pinch i - resetQubit i)) =
      (u • (pinch i - resetQubit i)) * (s • (1 - pinch i))
    ext ρ : 1
    show (s • (1 - pinch i)) ((u • (pinch i - resetQubit i)) ρ) =
      (u • (pinch i - resetQubit i)) ((s • (1 - pinch i)) ρ)
    simp only [smul_apply, map_smul, hAB', hBA', smul_zero]
  have hF : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • dissipator (ampDamp i)) =
      ((1 - (1 - pinch i)) + Complex.exp ((t : ℂ) * -1) • (1 - pinch i)) *
        ((1 - (pinch i - resetQubit i)) +
          Complex.exp ((t : ℂ) * -2) • (pinch i - resetQubit i)) := by
    intro t
    rw [hL, smul_add, smul_smul, smul_smul]
    exact (exp_add_comm' (𝔸 := Superop (Idx k)) (hcomm _ _)).trans
      (congrArg₂ (fun x y : Superop (Idx k) => x * y) (exp_smul_idem (𝔸 := Superop (Idx k)) hA _)
        (exp_smul_idem (𝔸 := Superop (Idx k)) hB _))
  have h1 : Filter.Tendsto
      (fun t : ℝ => (1 - (1 - pinch i)) + Complex.exp ((t : ℂ) * -1) • (1 - pinch i))
      Filter.atTop (nhds ((1 - (1 - pinch i)) + (0 : ℂ) • (1 - pinch i))) :=
    tendsto_const_nhds.add ((tendsto_cexp_neg 1 (by norm_num)).smul_const _)
  have h2 : Filter.Tendsto (fun t : ℝ => (1 - (pinch i - resetQubit i)) +
      Complex.exp ((t : ℂ) * -2) • (pinch i - resetQubit i))
      Filter.atTop (nhds ((1 - (pinch i - resetQubit i)) + (0 : ℂ) • (pinch i - resetQubit i))) :=
    tendsto_const_nhds.add ((tendsto_cexp_neg 2 (by norm_num)).smul_const _)
  have h3 := h1.mul h2
  have e0A : (0 : ℂ) • (1 - pinch i) = 0 := zero_smul ℂ (1 - pinch i : Superop (Idx k))
  have e0B : (0 : ℂ) • (pinch i - resetQubit i) = 0 :=
    zero_smul ℂ (pinch i - resetQubit i : Superop (Idx k))
  have hv : ((1 - (1 - pinch i)) + (0 : ℂ) • (1 - pinch i)) *
      ((1 - (pinch i - resetQubit i)) + (0 : ℂ) • (pinch i - resetQubit i)) = resetQubit i := by
    rw [e0A, e0B, add_zero, add_zero, sub_sub_cancel, mul_sub, mul_sub, mul_one, hQQ, hQR,
      sub_sub_cancel]
  rw [hv] at h3
  exact chan_limit (F := fun t : ℝ => NormedSpace.exp ((t : ℂ) • dissipator (ampDamp i)))
    (fun t ht => chan_jump ha ht) (h3.congr fun t => (hF t).symm)

/-- C4 -/
theorem chan_resetQubit0 {k : ℕ} (hk : 0 < k) (S : Set (Mat k))
    (ha : ampDamp ⟨0, hk⟩ ∈ S) : resetQubit ⟨0, hk⟩ ∈ channelClosure S :=
  chan_reset _ S ha

/-- C5 -/
theorem chan_pinch0 {k : ℕ} (hk : 0 < k) (S : Set (Mat k))
    (hz : dephZ ⟨0, hk⟩ ∈ S) : pinch ⟨0, hk⟩ ∈ channelClosure S :=
  chan_pinch _ S hz

/-! ## C6 qubit swaps, reset of all qubits, full pinching, Householder -/

/-- relabel bit strings by swapping qubits `a` and `i` -/
def qswap {k : ℕ} (a i : Fin k) : Idx k ≃ Idx k where
  toFun ω := ω ∘ Equiv.swap a i
  invFun ω := ω ∘ Equiv.swap a i
  left_inv ω := by funext j; simp
  right_inv ω := by funext j; simp

theorem qswap_qswap {k : ℕ} (a i : Fin k) (ω : Idx k) : qswap a i (qswap a i ω) = ω := by
  funext j; simp [qswap]

theorem qswap_at {k : ℕ} (a i : Fin k) (ω : Idx k) : (qswap a i ω) a = ω i := by
  simp [qswap]

theorem qswap_update {k : ℕ} (a i : Fin k) (ω : Idx k) (b : Bool) :
    qswap a i (Function.update (qswap a i ω) a b) = Function.update ω i b := by
  funext j
  simp only [qswap, Equiv.coe_fn_mk, Function.comp_apply, Function.update_apply,
    Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- permutation matrix of `qswap` -/
def qP {k : ℕ} (a i : Fin k) : Mat k :=
  Matrix.of fun ω ζ => if ζ = qswap a i ω then 1 else 0

theorem qP_mul {k : ℕ} (a i : Fin k) (M : Mat k) (ω η : Idx k) :
    (qP a i * M) ω η = M (qswap a i ω) η := by
  simp [Matrix.mul_apply, qP, ite_mul]

theorem mul_qPH {k : ℕ} (a i : Fin k) (M : Mat k) (η ω : Idx k) :
    (M * (qP a i)ᴴ) η ω = M η (qswap a i ω) := by
  simp [Matrix.mul_apply, qP, Matrix.conjTranspose_apply, apply_ite (star : ℂ → ℂ), mul_ite]

theorem qP_unitary {k : ℕ} (a i : Fin k) : qP a i ∈ Matrix.unitaryGroup (Idx k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext ω ω'
  rw [qP_mul]
  simp [qP, Matrix.conjTranspose_apply, Matrix.one_apply, apply_ite (star : ℂ → ℂ)]

theorem conj_qP {k : ℕ} (a i : Fin k) (M : Mat k) :
    unitaryConj (qP a i) M = Matrix.of fun ω ω' => M (qswap a i ω) (qswap a i ω') := by
  ext ω ω'
  rw [unitaryConj_apply, mul_qPH, qP_mul]
  rfl

theorem reset_conj {k : ℕ} (a i : Fin k) :
    resetQubit i = (unitaryConj (qP a i)).comp ((resetQubit a).comp (unitaryConj (qP a i))) := by
  refine ContinuousLinearMap.ext fun ρ => ?_
  ext ω ω'
  simp only [ContinuousLinearMap.comp_apply, conj_qP, reset_apply, Matrix.of_apply, qswap_at,
    qswap_update]

theorem pinch_conj {k : ℕ} (a i : Fin k) :
    pinch i = (unitaryConj (qP a i)).comp ((pinch a).comp (unitaryConj (qP a i))) := by
  refine ContinuousLinearMap.ext fun ρ => ?_
  ext ω ω'
  simp only [ContinuousLinearMap.comp_apply, conj_qP, pinch_apply, Matrix.of_apply, qswap_at,
    qswap_qswap]

section C6
variable {k : ℕ} {S : Set (Mat k)}

theorem chan_id (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S) :
    ContinuousLinearMap.id ℂ (Mat k) ∈ channelClosure S := by
  have h := hU 1 (one_mem _)
  convert h using 1
  refine ContinuousLinearMap.ext fun ρ => ?_
  simp [unitaryConj_apply]

theorem chan_conjP (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S)
    (a i : Fin k) {Φ : Superop (Idx k)} (hΦ : Φ ∈ channelClosure S) :
    (unitaryConj (qP a i)).comp (Φ.comp (unitaryConj (qP a i))) ∈ channelClosure S :=
  chan_comp (hU _ (qP_unitary a i)) (chan_comp hΦ (hU _ (qP_unitary a i)))

theorem sum_update (i : Fin k) (b : Bool) (f : Idx k → ℂ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Idx k => ω i = false), f (Function.update ω i b) =
    ∑ ω ∈ Finset.univ.filter (fun ω : Idx k => ω i = b), f ω := by
  apply Finset.sum_nbij' (fun ω => Function.update ω i b) (fun ω => Function.update ω i false)
  · intro ω _; simp
  · intro ω _; simp
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    simp [hω]
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    simp [hω]
  · intro ω _; rfl

theorem reset_trace (i : Fin k) (M : Mat k) : (resetQubit i M).trace = M.trace := by
  have h : (resetQubit i M).trace = ∑ ω ∈ Finset.univ.filter (fun ω : Idx k => ω i = false),
      ∑ b : Bool, M (Function.update ω i b) (Function.update ω i b) := by
    simp [Matrix.trace, reset_apply, Finset.sum_filter]
  rw [h, Finset.sum_comm]
  calc _ = ∑ b : Bool, ∑ ω ∈ Finset.univ.filter (fun ω : Idx k => ω i = b), M ω ω :=
        Finset.sum_congr rfl fun b _ => sum_update i b (fun ω => M ω ω)
    _ = M.trace := Finset.sum_fiberwise Finset.univ (fun ω : Idx k => ω i) (fun ω => M ω ω)

theorem reset_supp (i : Fin k) (T : Finset (Fin k)) (M : Mat k)
    (hM : ∀ ω ω', M ω ω' ≠ 0 → ∀ j ∈ T, ω j = false ∧ ω' j = false) :
    ∀ ω ω', resetQubit i M ω ω' ≠ 0 → ∀ j ∈ insert i T, ω j = false ∧ ω' j = false := by
  intro ω ω' h j hj
  rw [reset_apply, Matrix.of_apply] at h
  split_ifs at h with hi
  · rcases Finset.mem_insert.1 hj with rfl | hjT
    · exact hi
    · obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have := hM _ _ hb j hjT
      by_cases hji : j = i
      · subst hji; exact hi
      · simpa [Function.update_apply, hji] using this
  · exact absurd rfl h

/-- the all-zero bit string -/
def z0 (k : ℕ) : Idx k := fun _ => false

theorem eq_zeroState (M : Mat k) (h1 : M.trace = 1)
    (hM : ∀ ω ω', M ω ω' ≠ 0 → ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ω j = false ∧ ω' j = false) :
    M = zeroState k := by
  have h0 : ∀ ω ω', M ω ω' ≠ 0 → ω = z0 k ∧ ω' = z0 k := fun ω ω' h =>
    ⟨funext fun j => (hM ω ω' h j (Finset.mem_univ _)).1,
      funext fun j => (hM ω ω' h j (Finset.mem_univ _)).2⟩
  have htr : M (z0 k) (z0 k) = 1 := by
    rw [← h1, Matrix.trace, Finset.sum_eq_single (z0 k)]
    · rfl
    · intro ω _ hω
      by_contra h
      exact hω (h0 ω ω h).1
    · simp
  ext ω ω'
  simp only [zeroState, Matrix.of_apply]
  split_ifs with h
  · have e1 : ω = z0 k := funext h.1
    have e2 : ω' = z0 k := funext h.2
    rw [e1, e2, htr]
  · by_contra hne
    obtain ⟨e1, e2⟩ := h0 ω ω' hne
    exact h ⟨fun j => by rw [e1]; rfl, fun j => by rw [e2]; rfl⟩

theorem chan_reset_any (hk : 0 < k)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S)
    (hR : resetQubit ⟨0, hk⟩ ∈ channelClosure S) (i : Fin k) :
    resetQubit i ∈ channelClosure S := by
  rw [reset_conj ⟨0, hk⟩ i]
  exact chan_conjP hU _ _ hR

theorem chan_pinch_any (hk : 0 < k)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S)
    (hP : pinch ⟨0, hk⟩ ∈ channelClosure S) (i : Fin k) :
    pinch i ∈ channelClosure S := by
  rw [pinch_conj ⟨0, hk⟩ i]
  exact chan_conjP hU _ _ hP

theorem reset_many (hk : 0 < k)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S)
    (hR : resetQubit ⟨0, hk⟩ ∈ channelClosure S) (ρ : Mat k) (hρ : ρ.trace = 1)
    (T : Finset (Fin k)) :
    ∃ Φ ∈ channelClosure S, (Φ ρ).trace = 1 ∧
      ∀ ω ω', Φ ρ ω ω' ≠ 0 → ∀ j ∈ T, ω j = false ∧ ω' j = false := by
  induction T using Finset.induction_on with
  | empty => exact ⟨_, chan_id hU, by simpa using hρ, by simp⟩
  | @insert i T hi ih =>
    obtain ⟨Φ, hΦ, htr, hsupp⟩ := ih
    refine ⟨(resetQubit i).comp Φ, chan_comp (chan_reset_any hk hU hR i) hΦ, ?_, ?_⟩
    · rw [ContinuousLinearMap.comp_apply, reset_trace, htr]
    · exact reset_supp i T _ hsupp

/-- C6a every density can be sent to |0..0⟩. -/
theorem reach_zero (hk : 0 < k)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S)
    (hR : resetQubit ⟨0, hk⟩ ∈ channelClosure S) (ρ : Mat k) (hρ : IsDensity ρ) :
    ∃ Φ ∈ channelClosure S, Φ ρ = zeroState k := by
  obtain ⟨Φ, hΦ, htr, hs⟩ := reset_many hk hU hR ρ hρ.2 Finset.univ
  exact ⟨Φ, hΦ, eq_zeroState _ htr hs⟩

theorem pinch_many (hk : 0 < k)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S)
    (hP : pinch ⟨0, hk⟩ ∈ channelClosure S) (T : Finset (Fin k)) :
    ∃ Φ ∈ channelClosure S, ∀ M : Mat k,
      Φ M = Matrix.of fun ω ω' => if ∀ j ∈ T, ω j = ω' j then M ω ω' else 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨_, chan_id hU, fun M => by ext ω ω'; simp⟩
  | @insert i T hi ih =>
    obtain ⟨Φ, hΦ, hf⟩ := ih
    refine ⟨(pinch i).comp Φ, chan_comp (chan_pinch_any hk hU hP i) hΦ, fun M => ?_⟩
    ext ω ω'
    simp only [ContinuousLinearMap.comp_apply, hf, pinch_apply, Matrix.of_apply,
      Finset.forall_mem_insert, ite_and]

theorem chan_pinchAll (hk : 0 < k)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S)
    (hP : pinch ⟨0, hk⟩ ∈ channelClosure S) :
    (pinchAll : Superop (Idx k)) ∈ channelClosure S := by
  obtain ⟨Φ, hΦ, hf⟩ := pinch_many hk hU hP Finset.univ
  convert hΦ using 1
  refine ContinuousLinearMap.ext fun M => ?_
  rw [hf, pinchAll_apply]
  ext ω ω'
  by_cases h : ω = ω'
  · subst h; simp
  · have h' : ¬ ∀ j, ω j = ω' j := fun h' => h (funext h')
    simp [h, h']

/-- Householder reflection sending `e_0` to `-w` for a real unit vector `w` with `w_0 ≥ 0`. -/
theorem householder (w : Idx k → ℝ) (hw0 : 0 ≤ w (z0 k)) (hw1 : ∑ ω, w ω ^ 2 = 1) :
    ∃ H : Mat k, H ∈ Matrix.unitaryGroup (Idx k) ℂ ∧ ∀ ω, H ω (z0 k) = -((w ω : ℝ) : ℂ) := by
  set ur : Idx k → ℝ := fun ω => (if ω = z0 k then 1 else 0) + w ω with hur
  set N : ℝ := ∑ η, ur η ^ 2 with hN
  have hN2 : N = 2 + 2 * w (z0 k) := by
    have e : ∀ η, ur η ^ 2 = w η ^ 2 + (if η = z0 k then 1 + 2 * w η else 0) := by
      intro η; simp only [hur]; split_ifs <;> ring
    rw [hN, Finset.sum_congr rfl fun η _ => e η, Finset.sum_add_distrib, hw1,
      Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_univ _)]
    ring
  have hNpos : 0 < N := by rw [hN2]; linarith
  set c : ℝ := 2 / N with hc
  have hcN : c * N = 2 := by rw [hc, div_mul_cancel₀ _ hNpos.ne']
  have hcz : c * ur (z0 k) = 1 := by
    have : ur (z0 k) = 1 + w (z0 k) := by simp [hur]
    rw [this, hc, hN2, div_mul_eq_mul_div, div_eq_one_iff_eq (by linarith)]; ring
  set A : Mat k := Matrix.of fun ω ω' => ((ur ω * ur ω' : ℝ) : ℂ) with hA
  have hAA : A * A = (N : ℂ) • A := by
    ext ω ω'
    simp only [hA, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    congr 1
    rw [hN, Finset.sum_mul]
    exact Finset.sum_congr rfl fun η _ => by ring
  have hAH : Aᴴ = A := by
    ext ω ω'
    simp [hA, Matrix.conjTranspose_apply, mul_comm]
  set H : Mat k := 1 - (c : ℂ) • A with hH
  have hHH : Hᴴ = H := by
    rw [hH, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hAH]
    simp
  refine ⟨H, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hHH]
    have e1 : H * H = 1 - (c : ℂ) • A - (c : ℂ) • A + ((c : ℂ) * (c : ℂ) * (N : ℂ)) • A := by
      rw [hH, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, Matrix.smul_mul,
        Matrix.mul_smul, hAA]
      module
    have e2 : (c : ℂ) * (c : ℂ) * (N : ℂ) = 2 * (c : ℂ) := by
      rw [mul_assoc, ← Complex.ofReal_mul, hcN]; push_cast; ring
    rw [e1, e2]
    module
  · intro ω
    have : H ω (z0 k) = (((if ω = z0 k then 1 else 0) - c * (ur ω * ur (z0 k)) : ℝ) : ℂ) := by
      simp only [hH, hA, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [this, ← Complex.ofReal_neg]
    congr 1
    have : c * (ur ω * ur (z0 k)) = ur ω := by
      rw [mul_comm (ur ω), ← mul_assoc, hcz, one_mul]
    rw [this]
    simp only [hur]
    ring

theorem conj_zeroState (H : Mat k) (ω ω' : Idx k) :
    unitaryConj H (zeroState k) ω ω' = H ω (z0 k) * star (H ω' (z0 k)) := by
  have hZ : zeroState k = Matrix.of fun η η' => if η = z0 k ∧ η' = z0 k then 1 else 0 := by
    ext η η'
    simp [zeroState, z0, funext_iff]
  rw [unitaryConj_apply, hZ]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, ite_and, mul_ite, ite_mul,
    Finset.sum_ite_eq']

/-- C6b |0..0⟩ can be sent to every density (unitary, full pinching, unitary). -/
theorem reach_from_zero (hk : 0 < k)
    (hU : ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S)
    (hP : pinch ⟨0, hk⟩ ∈ channelClosure S) (σ : Mat k) (hσ : IsDensity σ) :
    ∃ Φ ∈ channelClosure S, Φ (zeroState k) = σ := by
  obtain ⟨hpsd, htr⟩ := hσ
  have hA := hpsd.1
  have hlam0 : ∀ ω, 0 ≤ hA.eigenvalues ω := hpsd.eigenvalues_nonneg
  have hlam1 : ∑ ω, hA.eigenvalues ω = 1 := by
    have h2 : ((∑ ω, hA.eigenvalues ω : ℝ) : ℂ) = 1 := by
      have h3 := hA.trace_eq_sum_eigenvalues
      rw [htr] at h3
      rw [Complex.ofReal_sum]
      exact h3.symm
    exact_mod_cast h2
  obtain ⟨H, hHu, hHcol⟩ := householder (fun ω => Real.sqrt (hA.eigenvalues ω))
    (Real.sqrt_nonneg _) (by
      simp only [Real.sq_sqrt (hlam0 _)]
      exact hlam1)
  refine ⟨(unitaryConj (hA.eigenvectorUnitary : Mat k)).comp
    ((pinchAll : Superop (Idx k)).comp (unitaryConj H)),
    chan_comp (hU _ (hA.eigenvectorUnitary).2)
      (chan_comp (chan_pinchAll hk hU hP) (hU H hHu)), ?_⟩
  have hD : (pinchAll : Superop (Idx k)) (unitaryConj H (zeroState k)) =
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [pinchAll_apply]
    congr 1
    funext ω
    rw [conj_zeroState, hHcol]
    simp only [Function.comp_apply]
    rw [star_neg, neg_mul_neg, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hlam0 ω)]
    rfl
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hD, unitaryConj_apply]
  refine Eq.trans ?_ hA.spectral_theorem.symm
  rw [Unitary.conjStarAlgAut_apply]
  simp [Matrix.star_eq_conjTranspose]

end C6

/-! ## C2 Lie-Trotter product formula -/

theorem exp_nsmul' {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (n : ℕ) (x : 𝔸) : NormedSpace.exp (n • x) = NormedSpace.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, exp_add_comm' (by rw [nsmul_eq_mul]; exact (Nat.cast_commute n x).mul_left (Commute.refl x)), ih, pow_succ]

theorem pow_sub_pow_norm_le {𝔸 : Type*} [NormedRing 𝔸] (X Y : 𝔸) (M : ℝ)
    (hX : ‖X‖ ≤ M) (hY : ‖Y‖ ≤ M) (n : ℕ) :
    ‖X ^ (n + 1) - Y ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * M ^ n * ‖X - Y‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hX
  induction n with
  | zero => simp
  | succ n ih =>
    have e : X ^ (n + 1 + 1) - Y ^ (n + 1 + 1) =
        X * (X ^ (n + 1) - Y ^ (n + 1)) + (X - Y) * Y ^ (n + 1) := by
      rw [pow_succ' X (n + 1), pow_succ' Y (n + 1), mul_sub, sub_mul]
      abel
    have hYn : ‖Y ^ (n + 1)‖ ≤ M ^ (n + 1) :=
      (norm_pow_le' Y n.succ_pos).trans (pow_le_pow_left₀ (norm_nonneg _) hY _)
    rw [e]
    calc _ ≤ ‖X * (X ^ (n + 1) - Y ^ (n + 1))‖ + ‖(X - Y) * Y ^ (n + 1)‖ := norm_add_le _ _
      _ ≤ ‖X‖ * ‖X ^ (n + 1) - Y ^ (n + 1)‖ + ‖X - Y‖ * ‖Y ^ (n + 1)‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M * (((n : ℝ) + 1) * M ^ n * ‖X - Y‖) + ‖X - Y‖ * M ^ (n + 1) := by
          gcongr
      _ = (((n + 1 : ℕ) : ℝ) + 1) * M ^ (n + 1) * ‖X - Y‖ := by push_cast; ring

/-- a function with derivative `A + B` at `0` and value `1` there grows at most linearly -/
theorem lin_bound {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸]
    (D : 𝔸) (Φ : ℂ → 𝔸) (hΦ : HasDerivAt Φ D 0) (h0 : Φ 0 = 1) :
    ∀ᶠ s in nhds (0 : ℂ), ‖Φ s‖ ≤ 1 + (‖D‖ + 1) * ‖s‖ := by
  have := (hasDerivAt_iff_isLittleO_nhds_zero.1 hΦ).def one_pos
  filter_upwards [this] with s hs
  simp only [zero_add, h0, one_mul] at hs
  calc ‖Φ s‖ = ‖1 + s • D + (Φ s - 1 - s • D)‖ := by congr 1; abel
    _ ≤ ‖1 + s • D‖ + ‖Φ s - 1 - s • D‖ := norm_add_le _ _
    _ ≤ (‖(1 : 𝔸)‖ + ‖s • D‖) + ‖s‖ := add_le_add (norm_add_le _ _) hs
    _ = 1 + (‖D‖ + 1) * ‖s‖ := by rw [norm_one, norm_smul]; ring

/-- C2 Lie-Trotter product formula in a complete normed ℂ-algebra with `‖1‖ = 1`. -/
theorem lie_trotter {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    [NormOneClass 𝔸] (A B : 𝔸) :
    Filter.Tendsto (fun n : ℕ => (NormedSpace.exp ((1 / (n : ℂ)) • A) *
      NormedSpace.exp ((1 / (n : ℂ)) • B)) ^ n) Filter.atTop
      (nhds (NormedSpace.exp (A + B))) := by
  set F : ℂ → 𝔸 := fun s => NormedSpace.exp (s • A) * NormedSpace.exp (s • B) with hF
  set G : ℂ → 𝔸 := fun s => NormedSpace.exp (s • (A + B)) with hG
  have hfd : HasDerivAt F (A + B) 0 := by
    rw [hF]
    convert (hasDerivAt_exp_smul_const A (0 : ℂ)).mul (hasDerivAt_exp_smul_const B (0 : ℂ))
      using 1
    all_goals first | rfl | simp
  have hgd : HasDerivAt G (A + B) 0 := by
    rw [hG]
    convert hasDerivAt_exp_smul_const (A + B) (0 : ℂ) using 1
    all_goals first | rfl | simp
  have hF0 : F 0 = 1 := by simp [hF]
  have hG0 : G 0 = 1 := by simp [hG]
  have hD : HasDerivAt (F - G) 0 0 := by
    simpa using hfd.sub hgd
  have hs : Filter.Tendsto (fun n : ℕ => (1 / (n : ℂ))) Filter.atTop (nhds 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
    simpa [Function.comp_def] using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℝ := ‖A + B‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  set c : ℝ := ε / (2 * Real.exp C) with hc
  have hcpos : 0 < c := by positivity
  have h1 : ∀ᶠ s in nhds (0 : ℂ), ‖F s - G s‖ ≤ c * ‖s‖ := by
    have := (hasDerivAt_iff_isLittleO_nhds_zero.1 hD).def hcpos
    filter_upwards [this] with s hs
    simpa [hF0, hG0] using hs
  have h2 := lin_bound (A + B) F hfd hF0
  have h3 := lin_bound (A + B) G hgd hG0
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hs.eventually (h1.and (h2.and h3)))
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b1, b2, b3⟩ := hN (m + 1) (by omega)
  set s : ℂ := 1 / ((m + 1 : ℕ) : ℂ) with hsdef
  have b1' : ‖F s - G s‖ ≤ c * ‖s‖ := b1
  have b2' : ‖F s‖ ≤ 1 + C * ‖s‖ := b2
  have b3' : ‖G s‖ ≤ 1 + C * ‖s‖ := b3
  have hns : ‖s‖ = ((m : ℝ) + 1)⁻¹ := by
    rw [hsdef, norm_div, norm_one, Complex.norm_natCast]
    push_cast
    ring
  rw [hns] at b1' b2' b3'
  have hY : G s ^ (m + 1) = NormedSpace.exp (A + B) := by
    rw [hG]
    simp only
    rw [← exp_nsmul']
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hsdef,
      mul_one_div_cancel (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)), one_smul]
  have hX : (NormedSpace.exp (s • A) * NormedSpace.exp (s • B)) = F s := rfl
  rw [hX, dist_eq_norm, ← hY]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hMexp : (1 + C * ((m : ℝ) + 1)⁻¹) ^ m ≤ Real.exp C := by
    have hM1 : 1 ≤ 1 + C * ((m : ℝ) + 1)⁻¹ := by
      have : 0 ≤ C * ((m : ℝ) + 1)⁻¹ := by positivity
      linarith
    calc (1 + C * ((m : ℝ) + 1)⁻¹) ^ m ≤ (1 + C * ((m : ℝ) + 1)⁻¹) ^ (m + 1) :=
          pow_le_pow_right₀ hM1 (Nat.le_succ m)
      _ ≤ (Real.exp (C * ((m : ℝ) + 1)⁻¹)) ^ (m + 1) := by
          gcongr
          linarith [Real.add_one_le_exp (C * ((m : ℝ) + 1)⁻¹)]
      _ = Real.exp C := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
  have hcE : c * Real.exp C = ε / 2 := by
    rw [hc]
    field_simp
  calc ‖F s ^ (m + 1) - G s ^ (m + 1)‖
      ≤ ((m : ℝ) + 1) * (1 + C * ((m : ℝ) + 1)⁻¹) ^ m * ‖F s - G s‖ :=
        pow_sub_pow_norm_le _ _ _ b2' b3' m
    _ ≤ ((m : ℝ) + 1) * (1 + C * ((m : ℝ) + 1)⁻¹) ^ m * (c * ((m : ℝ) + 1)⁻¹) := by
        gcongr
    _ = c * (1 + C * ((m : ℝ) + 1)⁻¹) ^ m := by
        field_simp
    _ ≤ c * Real.exp C := by gcongr
    _ < ε := by rw [hcE]; linarith


/-! ## C3: every unitary conjugation lies in the closed class -/

section C3
variable {k : ℕ} {S : Set (Mat k)}

theorem uc_mul (A B : Mat k) : unitaryConj (A * B) = (unitaryConj A).comp (unitaryConj B) := by
  ext1 ρ
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem chan_one : unitaryConj (1 : Mat k) ∈ channelClosure S := by
  have h0 : (0 : Mat k) ∈ antiHermSpan S := ⟨Submodule.zero_mem _, by simp⟩
  simpa using chan_unit h0 (le_refl (0 : ℝ))

theorem chan_pow {A : Mat k} (h : unitaryConj A ∈ channelClosure S) (n : ℕ) :
    unitaryConj (A ^ n) ∈ channelClosure S := by
  induction n with
  | zero => simpa using (chan_one (S := S))
  | succ n ih => rw [pow_succ, uc_mul]; exact chan_comp ih h

theorem uc_eq (A : Mat k) : unitaryConj A =
    (ContinuousLinearMap.mul ℂ (Mat k) A).comp ((ContinuousLinearMap.mul ℂ (Mat k)).flip Aᴴ) := by
  ext1 ρ
  simp [Matrix.mul_assoc]

theorem conjT_cont : Continuous (fun A : Mat k => Aᴴ) := by
  first
  | exact continuous_star
  | exact continuous_id.matrix_conjTranspose

theorem uc_cont : Continuous (fun A : Mat k => unitaryConj A) := by
  have : (fun A : Mat k => unitaryConj A) = fun A =>
      (ContinuousLinearMap.mul ℂ (Mat k) A).comp ((ContinuousLinearMap.mul ℂ (Mat k)).flip Aᴴ) :=
    funext uc_eq
  rw [this]
  exact ((ContinuousLinearMap.mul ℂ (Mat k)).continuous).clm_comp
    (((ContinuousLinearMap.mul ℂ (Mat k)).flip).continuous.comp conjT_cont)

theorem rsmul_eq (c : ℝ) (Y : Mat k) : c • Y = (c : ℂ) • Y := by
  ext i j
  simp [Complex.real_smul]

/-- Anti-Hermitian directions whose whole one-parameter unitary group lies in the class. -/
def Kset (S : Set (Mat k)) : Set (Mat k) :=
  {Y | Yᴴ = -Y ∧ ∀ t : ℝ, unitaryConj (NormedSpace.exp ((t : ℂ) • Y)) ∈ channelClosure S}

theorem exp_cont : Continuous (fun A : Mat k => NormedSpace.exp A) :=
  continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt

theorem K_closed : IsClosed (Kset S) := by
  have e : Kset S = {Y : Mat k | Yᴴ = -Y} ∩ ⋂ t : ℝ,
      (fun Y : Mat k => unitaryConj (NormedSpace.exp ((t : ℂ) • Y))) ⁻¹' channelClosure S := by
    ext Y
    simp [Kset]
  rw [e]
  exact (isClosed_eq conjT_cont continuous_neg).inter (isClosed_iInter fun t =>
    (chan_closed S).preimage (uc_cont.comp
      (exp_cont.comp (continuous_const_smul _))))

theorem K_zero : (0 : Mat k) ∈ Kset S :=
  ⟨by simp, fun t => by simpa using (chan_one (S := S))⟩

theorem K_smul (c : ℝ) {Y : Mat k} (hY : Y ∈ Kset S) : (c : ℂ) • Y ∈ Kset S := by
  refine ⟨?_, fun t => ?_⟩
  · rw [Matrix.conjTranspose_smul, hY.1]
    simp
  · rw [smul_smul, ← Complex.ofReal_mul]
    exact hY.2 (t * c)

theorem K_add
    (htrot : ∀ A B : Mat k, Filter.Tendsto (fun n : ℕ => (NormedSpace.exp ((1 / (n : ℂ)) • A) *
      NormedSpace.exp ((1 / (n : ℂ)) • B)) ^ n) Filter.atTop (nhds (NormedSpace.exp (A + B))))
    {Y Z : Mat k} (hY : Y ∈ Kset S) (hZ : Z ∈ Kset S) : Y + Z ∈ Kset S := by
  refine ⟨by rw [Matrix.conjTranspose_add, hY.1, hZ.1, neg_add], fun t => ?_⟩
  have hlim := (uc_cont.tendsto _).comp (htrot ((t : ℂ) • Y) ((t : ℂ) • Z))
  rw [← smul_add] at hlim
  refine (chan_closed S).mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  have e : ∀ W : Mat k, (1 / (n : ℂ)) • ((t : ℂ) • W) = ((t / n : ℝ) : ℂ) • W := by
    intro W
    rw [smul_smul]
    congr 1
    push_cast
    ring
  simp only [Function.comp_apply, e]
  exact chan_pow (by rw [uc_mul]; exact chan_comp (hY.2 _) (hZ.2 _)) n

def Ksub
    (htrot : ∀ A B : Mat k, Filter.Tendsto (fun n : ℕ => (NormedSpace.exp ((1 / (n : ℂ)) • A) *
      NormedSpace.exp ((1 / (n : ℂ)) • B)) ^ n) Filter.atTop (nhds (NormedSpace.exp (A + B))))
    (S : Set (Mat k)) : Submodule ℝ (Mat k) where
  carrier := Kset S
  zero_mem' := K_zero
  add_mem' := fun hY hZ => K_add htrot hY hZ
  smul_mem' := fun c Y hY => by
    rw [rsmul_eq]
    exact K_smul c hY

theorem ah_sub_K {X : Mat k} (hX : X ∈ antiHermSpan S) : X ∈ Kset S := by
  refine ⟨hX.2, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · exact chan_unit hX ht
  · have e : (t : ℂ) • X = ((-t : ℝ) : ℂ) • (-X) := by
      push_cast
      simp
    rw [e]
    exact chan_unit (antiHermSpan_neg hX) (by linarith)

theorem exp_mul_exp_neg (a : Mat k) : NormedSpace.exp a * NormedSpace.exp (-a) = 1 := by
  rw [← exp_add_comm' ((Commute.refl a).neg_right), add_neg_cancel,
    NormedSpace.exp_zero]

theorem conj_exp_in_K {P Q Y : Mat k} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hP : unitaryConj P ∈ channelClosure S) (hQ : unitaryConj Q ∈ channelClosure S)
    (hPQh : Pᴴ = Q) (hY : Y ∈ Kset S) : P * Y * Q ∈ Kset S := by
  have hQh : Qᴴ = P := by rw [← hPQh, Matrix.conjTranspose_conjTranspose]
  refine ⟨?_, fun t => ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQh, hPQh, hY.1]
    simp [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · let u : (Mat k)ˣ := ⟨P, Q, hPQ, hQP⟩
    have e : (t : ℂ) • (P * Y * Q) = (u : Mat k) * ((t : ℂ) • Y) * ↑u⁻¹ := by
      simp [u, Matrix.mul_smul, Matrix.smul_mul]
    rw [e, Matrix.exp_units_conj]
    simp only [u, Units.val_mk, Units.inv_mk]
    rw [uc_mul, uc_mul]
    exact chan_comp (chan_comp hP (hY.2 t)) hQ

theorem conj_mem_K {X Y : Mat k} (hX : X ∈ antiHermSpan S) (hY : Y ∈ Kset S) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • -X) ∈ Kset S := by
  have hXK := ah_sub_K hX
  have hnK := ah_sub_K (antiHermSpan_neg hX)
  refine conj_exp_in_K ?_ ?_ (hXK.2 s) (hnK.2 s) ?_ hY
  · rw [smul_neg]
    exact exp_mul_exp_neg _
  · rw [smul_neg]
    simpa using exp_mul_exp_neg (-((s : ℂ) • X))
  · rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hX.2]
    simp

theorem ad_mem_K
    (htrot : ∀ A B : Mat k, Filter.Tendsto (fun n : ℕ => (NormedSpace.exp ((1 / (n : ℂ)) • A) *
      NormedSpace.exp ((1 / (n : ℂ)) • B)) ^ n) Filter.atTop (nhds (NormedSpace.exp (A + B))))
    {X Y : Mat k} (hX : X ∈ antiHermSpan S) (hY : Y ∈ Kset S) :
    X * Y - Y * X ∈ Kset S := by
  let g : ℂ → Mat k := fun z => NormedSpace.exp (z • X) * Y * NormedSpace.exp (z • -X)
  have hd : HasDerivAt g (X * Y - Y * X) 0 := by
    have h1 := hasDerivAt_exp_smul_const X (0 : ℂ)
    have h2 := hasDerivAt_exp_smul_const (-X) (0 : ℂ)
    refine ((h1.mul_const Y).mul h2).congr_deriv ?_
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg]
    noncomm_ring
  have hg0 : g 0 = Y := by simp [g]
  have hof : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hT := (hasDerivAt_iff_tendsto_slope.1 hd).comp hof
  refine K_closed.mem_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, slope_def_module, sub_zero, hg0]
  have hs' : (s : ℂ)⁻¹ = ((s⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hs', ← rsmul_eq]
  exact (Ksub htrot S).smul_mem _ ((Ksub htrot S).sub_mem (conj_mem_K hX hY s) hY)

/-- The real Lie algebra generated by `A` lies in any real subspace containing `A` that is
stable under `ad_a` for `a ∈ A`. -/
theorem lieSpan_sub {A : Set (Mat k)} (K : Submodule ℝ (Mat k)) (hA : A ⊆ K)
    (had : ∀ a ∈ A, ∀ y ∈ K, a * y - y * a ∈ K) :
    (LieSubalgebra.lieSpan ℝ (Mat k) A : Set (Mat k)) ⊆ K := by
  let PP : Set (Submodule ℝ (Mat k)) := {P | A ⊆ P ∧ ∀ a ∈ A, ∀ y ∈ P, a * y - y * a ∈ P}
  let W := sInf PP
  have hWP : ∀ P ∈ PP, W ≤ P := fun P hP => sInf_le hP
  have hW : W ∈ PP := by
    refine ⟨fun a ha => ?_, fun a ha y hy => ?_⟩
    · exact Submodule.mem_sInf.2 fun P hP => hP.1 ha
    · rw [Submodule.mem_sInf] at hy ⊢
      exact fun P hP => hP.2 a ha y (hy P hP)
  let N : Submodule ℝ (Mat k) :=
    { carrier := {x | x ∈ W ∧ ∀ y ∈ W, x * y - y * x ∈ W}
      zero_mem' := ⟨W.zero_mem, fun y _ => by simpa using W.zero_mem⟩
      add_mem' := fun {x x'} hx hx' => ⟨W.add_mem hx.1 hx'.1, fun y hy => by
        have := W.add_mem (hx.2 y hy) (hx'.2 y hy)
        convert this using 1
        noncomm_ring⟩
      smul_mem' := fun c x hx => ⟨W.smul_mem c hx.1, fun y hy => by
        have := W.smul_mem c (hx.2 y hy)
        convert this using 1
        simp [smul_sub, smul_mul_assoc, mul_smul_comm]⟩ }
  have hN : N ∈ PP := by
    refine ⟨fun a ha => ⟨hW.1 ha, fun y hy => hW.2 a ha y hy⟩, fun a ha x hx => ?_⟩
    refine ⟨hW.2 a ha x hx.1, fun y hy => ?_⟩
    have h1 := hW.2 a ha _ (hx.2 y hy)
    have h2 := hx.2 _ (hW.2 a ha y hy)
    convert W.sub_mem h1 h2 using 1
    noncomm_ring
  let WL : LieSubalgebra ℝ (Mat k) :=
    { W with
      lie_mem' := fun {x y} hx hy => by
        rw [Ring.lie_def]
        exact ((hWP N hN) hx).2 y hy }
  have hle : LieSubalgebra.lieSpan ℝ (Mat k) A ≤ WL :=
    LieSubalgebra.lieSpan_le.2 fun a ha => hW.1 ha
  exact fun x hx => hWP K ⟨hA, had⟩ (hle hx)

theorem unitary_eq_exp {U : Mat k} (hU : U ∈ Matrix.unitaryGroup (Idx k) ℂ) :
    ∃ Y : Mat k, Yᴴ = -Y ∧ NormedSpace.exp Y = U := by
  have hU' : U ∈ unitary (Mat k) := hU
  have hfin := Matrix.finite_spectrum U
  have hN : IsStarNormal U := ⟨by
    rw [Commute, SemiconjBy, Unitary.star_mul_self_of_mem hU', Unitary.mul_star_self_of_mem hU']⟩
  let f : ℂ → ℂ := fun z => (Complex.arg z : ℂ) * Complex.I
  have hf : ContinuousOn f (spectrum ℂ U) := hfin.continuousOn _
  refine ⟨cfc f U, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose, ← cfc_star, ← cfc_neg]
    refine cfc_congr fun z _ => ?_
    simp [f]
  · have h1 : cfc (fun z => NormedSpace.exp (f z)) U = U := by
      conv_rhs => rw [← cfc_id' ℂ U]
      refine cfc_congr fun z hz => ?_
      have hz1 : ‖z‖ = 1 := by simpa using spectrum.subset_circle_of_unitary hU' hz
      have := Complex.norm_mul_exp_arg_mul_I z
      rw [hz1, Complex.ofReal_one, one_mul] at this
      simpa [f, ← Complex.exp_eq_exp_ℂ] using this
    conv_rhs => rw [← h1]
    rw [cfc_comp' (fun w : ℂ => NormedSpace.exp w) f U
        (Continuous.continuousOn (continuous_iff_continuousAt.2 fun x =>
          (NormedSpace.exp_analytic (𝕂 := ℂ) (x : ℂ)).continuousAt)) hf]
    exact (CFC.exp_eq_normedSpace_exp (𝕜 := ℂ)).symm

theorem uc_scalar (M : Mat k) (e : ℂ) (he : e * star e = 1) :
    unitaryConj (M * (e • (1 : Mat k))) = unitaryConj M := by
  have he' : (starRingEnd ℂ) e * e = 1 := by rw [mul_comm]; exact he
  ext1 ρ
  simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul, he, he']

theorem chan_all_unitaries'
    (htrot : ∀ A B : Mat k, Filter.Tendsto (fun n : ℕ => (NormedSpace.exp ((1 / (n : ℂ)) • A) *
      NormedSpace.exp ((1 / (n : ℂ)) • B)) ^ n) Filter.atTop (nhds (NormedSpace.exp (A + B))))
    (hH : IsHormander S) (U : Mat k) (hU : U ∈ Matrix.unitaryGroup (Idx k) ℂ) :
    unitaryConj U ∈ channelClosure S := by
  have hsu : suAlg (Idx k) ⊆ Kset S := hH.trans
    (lieSpan_sub (Ksub htrot S) (fun a ha => ah_sub_K ha) (fun a ha y hy => ad_mem_K htrot ha hy))
  obtain ⟨Y, hYh, hYU⟩ := unitary_eq_exp hU
  have hd : (Fintype.card (Idx k) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = Y.trace / (Fintype.card (Idx k) : ℂ) := ⟨_, rfl⟩
  have hc : star c = -c := by
    rw [hcdef, star_div₀, star_natCast, ← Matrix.trace_conjTranspose, hYh, Matrix.trace_neg,
      neg_div]
  have hY0 : Y - c • (1 : Mat k) ∈ suAlg (Idx k) := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hYh, hc,
        neg_smul]
      abel
    · rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, hcdef,
        div_mul_cancel₀ _ hd, sub_self]
  have he : NormedSpace.exp c * star (NormedSpace.exp c) = 1 := by
    rw [← Complex.exp_eq_exp_ℂ]
    have : star (Complex.exp c) = Complex.exp (-c) := by
      rw [← hc]
      exact (Complex.exp_conj c).symm
    rw [this, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hU' : U = NormedSpace.exp (Y - c • (1 : Mat k)) * (NormedSpace.exp c • (1 : Mat k)) := by
    have hsc : NormedSpace.exp c • (1 : Mat k) = NormedSpace.exp (c • (1 : Mat k)) := by
      simp only [← Algebra.algebraMap_eq_smul_one]
      exact NormedSpace.algebraMap_exp_comm c
    rw [hsc, ← exp_add_comm' ((Commute.one_right _).smul_right c), sub_add_cancel]
    exact hYU.symm
  rw [hU', uc_scalar _ _ he]
  simpa using (hsu hY0).2 1

end C3

/-- C3 Hörmander control gives every unitary conjugation. -/
theorem chan_all_unitaries {k : ℕ} (S : Set (Mat k)) (hS : ∀ a ∈ S, aᴴ ∈ S)
    (hH : IsHormander S) (U : Mat k) (hU : U ∈ Matrix.unitaryGroup (Idx k) ℂ) :
    unitaryConj U ∈ channelClosure S :=
  chan_all_unitaries' (fun A B => lie_trotter A B) hH U hU

end FF92

open LindbladReach.MinDiss Matrix ComplexOrder Matrix.Norms.L2Operator in
theorem solution {k : ℕ} (hk : 0 < k) (S : Set (Mat k)) (hS : ∀ a ∈ S, aᴴ ∈ S)
    (hH : IsHormander S) (ha : ampDamp ⟨0, hk⟩ ∈ S) (hz : dephZ ⟨0, hk⟩ ∈ S) :
    IsTransitive (channelClosure S) := by
  intro ρ σ hρ hσ
  have hU := fun U hU => FF92.chan_all_unitaries S hS hH U hU
  obtain ⟨Φ₁, h₁, e₁⟩ := FF92.reach_zero hk hU (FF92.chan_resetQubit0 hk S ha) ρ hρ
  obtain ⟨Φ₂, h₂, e₂⟩ := FF92.reach_from_zero hk hU (FF92.chan_pinch0 hk S hz) σ hσ
  exact ⟨Φ₂.comp Φ₁, FF92.chan_comp h₂ h₁, by simp [e₁, e₂]⟩
