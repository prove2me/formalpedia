-- Prove2me | solution 1 for MayersBC.bcjl_insecure
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:33:23.947096+00:00
-- url     : https://prove2.me/submissions/587877fc-d3aa-4c83-9bef-dd0cf1f2e6d9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_MayersBC_Opening
import Definitions.Def_MayersBC_IsConcealing
import Definitions.Def_MayersBC_cheatAccept
import Definitions.Def_MayersBC_bcjlDensity
import Definitions.Def_MayersBC_bobPOVM
import Definitions.Def_MayersBC_bcjlHonestAccept
import Theorems.Thm_MayersBC_attack_of_concealing
open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

namespace MayersBCGoalAux

lemma sum_zmod2 {M : Type} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ x : ZMod 2, f x = f 0 + f 1 := Fin.sum_univ_two f

lemma zmod2_cases {P : ZMod 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ c, P c := by
  intro c; fin_cases c
  · exact h0
  · exact h1

lemma z10 : (1 : ZMod 2) ≠ 0 := by decide
lemma z01 : (0 : ZMod 2) ≠ 1 := by decide
lemma zv1 : (1 : ZMod 2).val = 1 := rfl
lemma zv0 : (0 : ZMod 2).val = 0 := rfl

/-- One photon: `Σ_x |⟨x|c⟩_t|² = 1`. -/
lemma amp_normSq (t : Bool) (c : ZMod 2) : ∑ x : ZMod 2, ‖MayersBC.bb84Amp t c x‖ ^ 2 = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [sum_zmod2]
  revert c
  refine zmod2_cases ?_ ?_ <;> cases t <;>
    simp [MayersBC.bb84Amp, zv1, Complex.norm_real, h2, abs_of_pos hs] <;> norm_num

/-- One photon: each basis is orthonormal, `Σ_c ⟨x|c⟩_t ⟨c|x'⟩_t = [x = x']`. -/
lemma amp_complete (t : Bool) (x x' : ZMod 2) :
    ∑ c : ZMod 2, MayersBC.bb84Amp t c x * conj (MayersBC.bb84Amp t c x') =
      if x = x' then 1 else 0 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hinv : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 2⁻¹ := by
    rw [← mul_inv, h2]
  rw [sum_zmod2]
  revert x x'
  refine zmod2_cases ?_ ?_ <;> refine zmod2_cases ?_ ?_ <;> cases t <;>
    simp [MayersBC.bb84Amp, zv1, Complex.conj_ofReal, div_eq_mul_inv, hinv, neg_mul, mul_neg] <;>
    norm_num

/-- `|c⟩_θ` is a unit vector. -/
lemma bb84State_isState {n : ℕ} (θ : Fin n → Bool) (c : Fin n → ZMod 2) :
    IsState (MayersBC.bb84State θ c) := by
  have hsq : ‖MayersBC.bb84State θ c‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [MayersBC.bb84State, PiLp.toLp_apply, norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun i a => ‖MayersBC.bb84Amp (θ i) (c i) a‖ ^ 2)]
    simp [amp_normSq]
  have hn : 0 ≤ ‖MayersBC.bb84State θ c‖ := norm_nonneg _
  show ‖MayersBC.bb84State θ c‖ = 1
  nlinarith

/-- For a fixed basis string, `Σ_c |c⟩_θ⟨c|_θ = I`. -/
lemma sum_pureDensity_bb84 {n : ℕ} (θ : Fin n → Bool) :
    ∑ c : Fin n → ZMod 2, pureDensity (MayersBC.bb84State θ c) = 1 := by
  ext x x'
  simp only [Matrix.sum_apply, pureDensity, Matrix.of_apply, MayersBC.bb84State, PiLp.toLp_apply,
    map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => MayersBC.bb84Amp (θ i) a (x i) *
    conj (MayersBC.bb84Amp (θ i) a (x' i)))]
  simp only [amp_complete]
  rw [Fintype.prod_boole, Matrix.one_apply]
  congr 1
  exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- Bob's measurement in a random basis is a POVM. -/
lemma bobPOVM_isPOVM (n : ℕ) : IsPOVM (MayersBC.bobPOVM n) := by
  refine ⟨fun y => ?_, ?_⟩
  · have hpd : (pureDensity (MayersBC.bb84State y.1 y.2)).PosSemidef := by
      have := Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp (MayersBC.bb84State y.1 y.2))
      convert this using 1
      ext i j
      simp [pureDensity, Matrix.vecMulVec_apply]
    have hc : (0 : ℂ) ≤ (((1 : ℝ) / 2 ^ n : ℝ) : ℂ) := by
      exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / 2 ^ n)
    exact hpd.smul hc
  · simp only [MayersBC.bobPOVM, Fintype.sum_prod_type, ← Finset.smul_sum, sum_pureDensity_bb84,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ (2 ^ n) (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ),
      smul_smul]
    have : ((((1 : ℝ) / 2 ^ n : ℝ) : ℂ) * ((2 ^ n : ℕ) : ℂ)) = 1 := by
      push_cast
      field_simp
    rw [this, one_smul]

/-- The honest commitment law is a probability distribution whenever some codeword encodes `b`. -/
lemma bcjlProb_isProbDist {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (r : Fin n → ZMod 2)
    (b : ZMod 2) (hne : ∃ c : Fin n → ZMod 2, c ∈ C ∧ c ⬝ᵥ r = b) :
    FuchsVdGraaf.IsProbDist (MayersBC.bcjlProb C r b) := by
  classical
  have hcard : ((Finset.univ.filter fun c : Fin n → ZMod 2 => c ∈ C ∧ c ⬝ᵥ r = b).card : ℝ) ≠ 0 := by
    obtain ⟨c, hc⟩ := hne
    have : 0 < (Finset.univ.filter fun c : Fin n → ZMod 2 => c ∈ C ∧ c ⬝ᵥ r = b).card :=
      Finset.card_pos.mpr ⟨c, by simp [hc]⟩
    exact_mod_cast this.ne'
  refine ⟨fun w => ?_, ?_⟩
  · simp only [MayersBC.bcjlProb]
    split_ifs
    · positivity
    · exact le_refl 0
  · simp only [MayersBC.bcjlProb, Fintype.sum_prod_type]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
    rw [mul_zero, add_zero]
    push_cast
    field_simp

/-- `Tr(Σ_w p_w |ψ_w⟩⟨ψ_w|) = 1` for a probability vector and unit vectors. -/
lemma trace_mixtureDensity {W ι : Type} [Fintype W] [Fintype ι] (p : W → ℝ)
    (hp : FuchsVdGraaf.IsProbDist p) (ψ : W → EuclideanSpace ℂ ι) (hψ : ∀ w, IsState (ψ w)) :
    (MayersBC.mixtureDensity p ψ).trace = 1 := by
  have h1 : ∀ w, (pureDensity (ψ w)).trace = 1 := by
    intro w
    have hn : ‖ψ w‖ ^ 2 = 1 := by rw [(hψ w : ‖ψ w‖ = 1), one_pow]
    rw [EuclideanSpace.norm_sq_eq] at hn
    simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
    have : ∀ x, (ψ w) x * conj ((ψ w) x) = ((‖(ψ w) x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [this]
    rw [← Complex.ofReal_sum, hn, Complex.ofReal_one]
  simp only [MayersBC.mixtureDensity, Matrix.trace_sum, Matrix.trace_smul, h1, smul_eq_mul,
    mul_one]
  rw [← Complex.ofReal_sum, hp.2, Complex.ofReal_one]

/-- Measurements with positive semidefinite elements accept with nonnegative probability. -/
lemma cheatAccept_nonneg {A W Y ι : Type} [Fintype A] [DecidableEq A] [Fintype W] [Fintype Y]
    [Fintype ι] [DecidableEq ι] (φ : EuclideanSpace ℂ (A × ι)) (N : W → Matrix A A ℂ)
    (E : Y → Matrix ι ι ℂ) (hN : IsPOVM N) (hE : IsPOVM E) (T : ZMod 2 → W → Y → Prop)
    (b : ZMod 2) : 0 ≤ MayersBC.cheatAccept φ N E T b := by
  unfold MayersBC.cheatAccept
  refine Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun y _ => ?_
  split_ifs
  · have hk : (Matrix.kronecker (N w) (E y)).PosSemidef := (hN.1 w).kronecker (hE.1 y)
    have := hk.dotProduct_mulVec_nonneg (WithLp.ofLp φ)
    have htr : (Matrix.kronecker (N w) (E y) * pureDensity φ).trace =
        star (WithLp.ofLp φ) ⬝ᵥ (Matrix.kronecker (N w) (E y) *ᵥ WithLp.ofLp φ) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
        dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [effectProb, htr]
    exact (Complex.nonneg_iff.mp this).1
  · exact le_refl 0

end MayersBCGoalAux

open MayersBCGoalAux MayersBC in
theorem solution (n : ℕ) (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (r : Fin n → ZMod 2)
    (T : ZMod 2 → Opening n → Opening n → Prop) (ε ε' : ℝ)
    (hBob : IsConcealing ε (bcjlDensity C r 0) (bcjlDensity C r 1))
    (hcorrect : 1 - ε' ≤ bcjlHonestAccept C r T 1) :
    ∃ φ : EuclideanSpace ℂ (Opening n × (Fin n → ZMod 2)), IsState φ ∧
      traceLeft (pureDensity φ) = bcjlDensity C r 0 ∧
      ∃ N0 N1 : Opening n → Matrix (Opening n) (Opening n) ℂ, IsPOVM N0 ∧ IsPOVM N1 ∧
        cheatAccept φ N0 (bobPOVM n) T 0 = bcjlHonestAccept C r T 0 ∧
        bcjlHonestAccept C r T 1 - 4 * Real.sqrt ε ≤ cheatAccept φ N1 (bobPOVM n) T 1 ∧
        1 - ε' - 4 * Real.sqrt ε ≤ cheatAccept φ N1 (bobPOVM n) T 1 := by
  classical
  set ψ : Opening n → EuclideanSpace ℂ (Fin n → ZMod 2) := fun w => bb84State w.1 w.2 with hψdef
  have hψ : ∀ w, IsState (ψ w) := fun w => bb84State_isState w.1 w.2
  have hE : IsPOVM (bobPOVM n) := bobPOVM_isPOVM n
  have hp0 : FuchsVdGraaf.IsProbDist (bcjlProb C r 0) :=
    bcjlProb_isProbDist C r 0 ⟨0, C.zero_mem, zero_dotProduct r⟩
  by_cases hS1 : ∃ c : Fin n → ZMod 2, c ∈ C ∧ c ⬝ᵥ r = 1
  · -- some codeword encodes `1`: the general attack applies to BCJL as it stands
    have hp : ∀ b, FuchsVdGraaf.IsProbDist (bcjlProb C r b) :=
      zmod2_cases hp0 (bcjlProb_isProbDist C r 1 hS1)
    obtain ⟨φ, hφ, hred, N0, N1, hN0, hN1, h0, h1⟩ :=
      attack_of_concealing (bcjlProb C r) hp ψ hψ (bobPOVM n) hE T ε hBob
    refine ⟨φ, hφ, hred, N0, N1, hN0, hN1, h0, h1, ?_⟩
    have : bcjlHonestAccept C r T 1 = honestAccept (bcjlProb C r) ψ (bobPOVM n) T 1 := rfl
    linarith
  · -- no codeword encodes `1`: the honest opening of `1` is never accepted
    simp only [not_exists, not_and] at hS1
    have hzero : ∀ w, bcjlProb C r 1 w = 0 := by
      intro w
      simp only [bcjlProb]
      rw [if_neg]
      rintro ⟨hC, hr⟩
      exact hS1 w.2 hC hr
    have hH1 : bcjlHonestAccept C r T 1 = 0 := by
      simp [bcjlHonestAccept, honestAccept, hzero]
    -- `ε ≥ 0` (Bob's criterion at `Q = 0`)
    have hε : 0 ≤ ε := by
      have h0eff : IsEffect (0 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :=
        ⟨Matrix.PosSemidef.zero, by rw [sub_zero]; exact Matrix.PosSemidef.one⟩
      exact le_trans (abs_nonneg _) (hBob 0 h0eff)
    -- run the attack against the commitment to `0` twice: `ρ₀` conceals itself
    let p' : ZMod 2 → Opening n → ℝ := fun _ => bcjlProb C r 0
    have htr : (mixtureDensity (bcjlProb C r 0) ψ).trace = 1 :=
      trace_mixtureDensity _ hp0 ψ hψ
    have hBob' : IsConcealing ε (mixtureDensity (p' 0) ψ) (mixtureDensity (p' 1) ψ) := by
      intro Q _
      have : guessError (mixtureDensity (bcjlProb C r 0) ψ) (mixtureDensity (bcjlProb C r 0) ψ)
          Q = 1 / 2 := by
        simp only [guessError, effectProb, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
          Complex.sub_re, htr, Complex.one_re]
        ring
      simp only [p']
      rw [this, sub_self, abs_zero]
      exact hε
    obtain ⟨φ, hφ, hred, N0, N1, hN0, hN1, h0, -⟩ :=
      attack_of_concealing p' (fun _ => hp0) ψ hψ (bobPOVM n) hE T ε hBob'
    have hnn := cheatAccept_nonneg φ N1 (bobPOVM n) hN1 hE T 1
    have hs := Real.sqrt_nonneg ε
    refine ⟨φ, hφ, hred, N0, N1, hN0, hN1, h0, ?_, ?_⟩
    · rw [hH1]; linarith
    · rw [hH1] at hcorrect; linarith
