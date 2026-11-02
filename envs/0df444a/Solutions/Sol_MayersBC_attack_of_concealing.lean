-- Prove2me | solution 1 for MayersBC.attack_of_concealing
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:31:18.582609+00:00
-- url     : https://prove2.me/submissions/5c039036-ed88-427f-b22f-26139a2e9b32

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_MayersBC_mixtureDensity
import Definitions.Def_MayersBC_IsConcealing
import Definitions.Def_MayersBC_honestAccept
import Definitions.Def_MayersBC_cheatAccept
import Theorems.Thm_MayersBC_exists_unitary_inner_eq_rootFidelity
import Theorems.Thm_MayersBC_effectProb_sub_le_two_norm_sub
open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

namespace MayersBCAttackAux

/-- `Tr(M |φ⟩⟨φ|) = ⟨φ|M|φ⟩`, written with `dotProduct`. -/
lemma trace_mul_pureDensity' {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ)
    (φ : EuclideanSpace ℂ ι) :
    (M * pureDensity φ).trace = star (WithLp.ofLp φ) ⬝ᵥ (M *ᵥ WithLp.ofLp φ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `|Xφ⟩⟨Xφ| = X |φ⟩⟨φ| Xᴴ`. -/
lemma pureDensity_act {ι : Type} [Fintype ι] (X : Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) :
    pureDensity (act X φ) = X * pureDensity φ * Xᴴ := by
  ext i j
  simp only [pureDensity, act, Matrix.of_apply, PiLp.toLp_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, RCLike.star_def, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Conjugating the operator by `X` is the same as moving the state by `X`. -/
lemma effectProb_conj {ι : Type} [Fintype ι] (X M : Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) :
    effectProb (Xᴴ * M * X) (pureDensity φ) = effectProb M (pureDensity (act X φ)) := by
  rw [pureDensity_act, effectProb, effectProb, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

lemma effectProb_sum {ι J : Type} [Fintype ι] (s : Finset J) (M : J → Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) : effectProb (∑ j ∈ s, M j) ρ = ∑ j ∈ s, effectProb (M j) ρ := by
  simp only [effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

lemma effectProb_ite {ι : Type} [Fintype ι] (c : Prop) [Decidable c] (M ρ : Matrix ι ι ℂ) :
    effectProb (if c then M else 0) ρ = if c then effectProb M ρ else 0 := by
  split_ifs <;> simp [effectProb]

/-- The standard-basis projectors `|w⟩⟨w|`. -/
noncomputable def proj {W : Type} [DecidableEq W] (w : W) : Matrix W W ℂ :=
  Matrix.diagonal (Pi.single w 1)

lemma proj_posSemidef {W : Type} [Fintype W] [DecidableEq W] (w : W) : (proj w).PosSemidef := by
  rw [proj, Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases h : i = w
  · subst h; simp
  · simp [h]

lemma sum_proj {W : Type} [Fintype W] [DecidableEq W] : ∑ w : W, proj w = 1 := by
  ext i j
  simp only [proj, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [Pi.single_apply]
  · simp [h]

lemma proj_isPOVM {W : Type} [Fintype W] [DecidableEq W] : IsPOVM (proj (W := W)) :=
  ⟨proj_posSemidef, sum_proj⟩

/-- `((|w⟩⟨w| ⊗ E) v)(w₁, x₁) = [w₁ = w] Σ_{x₂} E x₁ x₂ v(w, x₂)`. -/
lemma kron_proj_mulVec_apply {W ι : Type} [Fintype W] [DecidableEq W] [Fintype ι]
    (w : W) (E : Matrix ι ι ℂ) (v : W × ι → ℂ) (w1 : W) (x1 : ι) :
    (Matrix.kronecker (proj w) E *ᵥ v) (w1, x1) =
      if w1 = w then ∑ x2, E x1 x2 * v (w, x2) else 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply, proj,
    Matrix.diagonal_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single w1]
  · by_cases h : w1 = w
    · subst h; simp
    · simp [h, Pi.single_apply]
  · intro w2 _ hw2
    simp [Ne.symm hw2]
  · simp

/-- The canonical purification `Σ_w √(q w) |w⟩ ⊗ |ψ_w⟩` of the mixture `Σ_w q_w |ψ_w⟩⟨ψ_w|`. -/
noncomputable def purif {W ι : Type} (q : W → ℝ) (ψ : W → EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (W × ι) :=
  WithLp.toLp 2 (fun x => ((Real.sqrt (q x.1) : ℝ) : ℂ) * ψ x.1 x.2)

lemma purif_traceLeft {W ι : Type} [Fintype W] (q : W → ℝ) (hq : ∀ w, 0 ≤ q w)
    (ψ : W → EuclideanSpace ℂ ι) :
    traceLeft (pureDensity (purif q ψ)) = MayersBC.mixtureDensity q ψ := by
  ext x x'
  simp only [traceLeft, pureDensity, purif, Matrix.of_apply, PiLp.toLp_apply,
    MayersBC.mixtureDensity, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hs : ((Real.sqrt (q w) : ℝ) : ℂ) * ((Real.sqrt (q w) : ℝ) : ℂ) = ((q w : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hq w)]
  calc ((Real.sqrt (q w) : ℝ) : ℂ) * ψ w x * (((Real.sqrt (q w) : ℝ) : ℂ) * conj (ψ w x')) =
        (((Real.sqrt (q w) : ℝ) : ℂ) * ((Real.sqrt (q w) : ℝ) : ℂ)) * (ψ w x * conj (ψ w x')) := by
        ring
    _ = ((q w : ℝ) : ℂ) * (ψ w x * conj (ψ w x')) := by rw [hs]

lemma purif_isState {W ι : Type} [Fintype W] [Fintype ι] (q : W → ℝ)
    (hq : FuchsVdGraaf.IsProbDist q) (ψ : W → EuclideanSpace ℂ ι) (hψ : ∀ w, IsState (ψ w)) :
    IsState (purif q ψ) := by
  have hsq : ‖purif q ψ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    have : ∀ w, ∑ x, ‖(purif q ψ) (w, x)‖ ^ 2 = q w := by
      intro w
      have hw : ‖ψ w‖ ^ 2 = 1 := by rw [(hψ w : ‖ψ w‖ = 1), one_pow]
      rw [EuclideanSpace.norm_sq_eq] at hw
      simp only [purif, PiLp.toLp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hq.1 w)]
      rw [← Finset.mul_sum, hw, mul_one]
    simp only [this]
    exact hq.2
  have hn : 0 ≤ ‖purif q ψ‖ := norm_nonneg _
  show ‖purif q ψ‖ = 1
  nlinarith

/-- Measuring the canonical purification with `|w⟩⟨w| ⊗ E` gives `q_w ⟨ψ_w|E|ψ_w⟩`. -/
lemma effectProb_kron_proj_purif {W ι : Type} [Fintype W] [DecidableEq W] [Fintype ι]
    (q : W → ℝ) (hq : ∀ w, 0 ≤ q w) (ψ : W → EuclideanSpace ℂ ι) (w : W) (E : Matrix ι ι ℂ) :
    effectProb (Matrix.kronecker (proj w) E) (pureDensity (purif q ψ)) =
      q w * effectProb E (pureDensity (ψ w)) := by
  rw [effectProb, effectProb, trace_mul_pureDensity', trace_mul_pureDensity']
  have hs : ((Real.sqrt (q w) : ℝ) : ℂ) * ((Real.sqrt (q w) : ℝ) : ℂ) = ((q w : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hq w)]
  have key : star (WithLp.ofLp (purif q ψ)) ⬝ᵥ
      (Matrix.kronecker (proj w) E *ᵥ WithLp.ofLp (purif q ψ)) =
      ((q w : ℝ) : ℂ) * (star (WithLp.ofLp (ψ w)) ⬝ᵥ (E *ᵥ WithLp.ofLp (ψ w))) := by
    conv_lhs => rw [dotProduct]
    simp only [Fintype.sum_prod_type, kron_proj_mulVec_apply]
    rw [Finset.sum_eq_single w]
    · simp only [if_true, purif, PiLp.toLp_apply, Pi.star_apply, RCLike.star_def, map_mul,
        Complex.conj_ofReal, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      refine Finset.sum_congr rfl fun x2 _ => ?_
      calc ((Real.sqrt (q w) : ℝ) : ℂ) * conj (ψ w x) *
            (E x x2 * (((Real.sqrt (q w) : ℝ) : ℂ) * ψ w x2)) =
          (((Real.sqrt (q w) : ℝ) : ℂ) * ((Real.sqrt (q w) : ℝ) : ℂ)) *
            (conj (ψ w x) * (E x x2 * ψ w x2)) := by ring
        _ = ((q w : ℝ) : ℂ) * (conj (ψ w x) * (E x x2 * ψ w x2)) := by rw [hs]
    · intro w' _ hw'
      simp [hw']
    · simp
  rw [key, Complex.re_ofReal_mul]

lemma conjTranspose_kronecker_one {A B : Type} [DecidableEq B] (V : Matrix A A ℂ) :
    (Matrix.kronecker V (1 : Matrix B B ℂ))ᴴ = Matrix.kronecker Vᴴ (1 : Matrix B B ℂ) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  by_cases h : b = b'
  · subst h
    simp [Matrix.kronecker]
  · have h' : b' ≠ b := Ne.symm h
    simp [Matrix.kronecker, h, h']

/-- `(UᴴPU) ⊗ E = (U ⊗ I)ᴴ (P ⊗ E) (U ⊗ I)`. -/
lemma kron_conj {W ι : Type} [Fintype W] [Fintype ι] [DecidableEq ι] (U P : Matrix W W ℂ)
    (E : Matrix ι ι ℂ) :
    Matrix.kronecker (Uᴴ * P * U) E =
      (Matrix.kronecker U (1 : Matrix ι ι ℂ))ᴴ * Matrix.kronecker P E *
        Matrix.kronecker U (1 : Matrix ι ι ℂ) := by
  rw [conjTranspose_kronecker_one]
  have h1 : E = 1 * E * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
  conv_lhs => rw [h1]
  unfold Matrix.kronecker
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

lemma sum_kron_eq_one {W Y ι : Type} [Fintype W] [DecidableEq W] [Fintype Y] [Fintype ι]
    [DecidableEq ι] (E : Y → Matrix ι ι ℂ) (hE : ∑ y, E y = 1) :
    ∑ w : W, ∑ y, Matrix.kronecker (proj w) (E y) = 1 := by
  have : ∀ w : W, ∑ y, Matrix.kronecker (proj w) (E y) = Matrix.kronecker (proj w) 1 := by
    intro w
    rw [← hE]
    ext i j
    simp [Matrix.kronecker, Matrix.sum_apply, Finset.mul_sum]
  simp only [this]
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [← Finset.sum_mul, ← Matrix.sum_apply, sum_proj]
  rw [← Matrix.one_kronecker_one (α := ℂ) (m := W) (n := ι)]
  simp

end MayersBCAttackAux

open MayersBCAttackAux MayersBC in
theorem solution {W Y ι : Type} [Fintype W] [DecidableEq W] [Fintype Y]
    [Fintype ι] [DecidableEq ι] (p : ZMod 2 → W → ℝ) (hp : ∀ b, FuchsVdGraaf.IsProbDist (p b))
    (ψ : W → EuclideanSpace ℂ ι) (hψ : ∀ w, IsState (ψ w)) (E : Y → Matrix ι ι ℂ)
    (hE : IsPOVM E) (T : ZMod 2 → W → Y → Prop) (ε : ℝ)
    (hBob : IsConcealing ε (mixtureDensity (p 0) ψ) (mixtureDensity (p 1) ψ)) :
    ∃ φ : EuclideanSpace ℂ (W × ι), IsState φ ∧
      traceLeft (pureDensity φ) = mixtureDensity (p 0) ψ ∧
      ∃ N0 N1 : W → Matrix W W ℂ, IsPOVM N0 ∧ IsPOVM N1 ∧
        cheatAccept φ N0 E T 0 = honestAccept p ψ E T 0 ∧
        honestAccept p ψ E T 1 - 4 * Real.sqrt ε ≤ cheatAccept φ N1 E T 1 := by
  -- canonical purifications of the two commitment states
  set φ0 := purif (p 0) ψ with hφ0def
  set φ1 := purif (p 1) ψ with hφ1def
  have hφ0 : IsState φ0 := purif_isState (p 0) (hp 0) ψ hψ
  have hφ1 : IsState φ1 := purif_isState (p 1) (hp 1) ψ hψ
  have hred0 : traceLeft (pureDensity φ0) = mixtureDensity (p 0) ψ :=
    purif_traceLeft (p 0) (hp 0).1 ψ
  have hred1 : traceLeft (pureDensity φ1) = mixtureDensity (p 1) ψ :=
    purif_traceLeft (p 1) (hp 1).1 ψ
  -- Uhlmann with Bob's criterion: a unitary on Alice's register with overlap `√F ≥ 1 - 2ε`
  obtain ⟨⟨U, hU, hov⟩, hF⟩ := exists_unitary_inner_eq_rootFidelity
    (mixtureDensity (p 0) ψ) (mixtureDensity (p 1) ψ) φ0 φ1 hφ0 hφ1 hred0 hred1 ε hBob
  have hUU : Uᴴ * U = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self ⟨U, hU⟩
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨φ0, hφ0, hred0, proj, fun w => Uᴴ * proj w * U, proj_isPOVM, ?_, ?_, ?_⟩
  · -- the rotated measurement is a POVM
    refine ⟨fun w => (proj_posSemidef w).conjTranspose_mul_mul_same U, ?_⟩
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_proj, Matrix.mul_one, hUU]
  · -- bit 0: measuring the purification in the standard basis is the honest opening
    unfold cheatAccept honestAccept
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases h : T 0 w y
    · rw [if_pos h, if_pos h, effectProb_kron_proj_purif (p 0) (hp 0).1 ψ w (E y)]
    · rw [if_neg h, if_neg h]
  · -- bit 1: the acceptance operator `G` and the perturbation bound
    classical
    set χ := act (Matrix.kronecker U (1 : Matrix ι ι ℂ)) φ0 with hχdef
    set G : Matrix (W × ι) (W × ι) ℂ :=
      ∑ w, ∑ y, if T 1 w y then Matrix.kronecker (proj w) (E y) else 0 with hGdef
    have hcheat : cheatAccept φ0 (fun w => Uᴴ * proj w * U) E T 1 =
        effectProb G (pureDensity χ) := by
      rw [hGdef, effectProb_sum]
      unfold cheatAccept
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [effectProb_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [effectProb_ite]
      by_cases h : T 1 w y
      · rw [if_pos h, if_pos h, kron_conj, effectProb_conj]
      · rw [if_neg h, if_neg h]
    have hhonest : honestAccept p ψ E T 1 = effectProb G (pureDensity φ1) := by
      rw [hGdef, effectProb_sum]
      unfold honestAccept
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [effectProb_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [effectProb_ite]
      by_cases h : T 1 w y
      · rw [if_pos h, if_pos h, effectProb_kron_proj_purif (p 1) (hp 1).1 ψ w (E y)]
      · rw [if_neg h, if_neg h]
    have hG : IsEffect G := by
      have hterm : ∀ w y, (if T 1 w y then Matrix.kronecker (proj w) (E y) else 0).PosSemidef := by
        intro w y
        split_ifs
        · exact (proj_posSemidef w).kronecker (hE.1 y)
        · exact Matrix.PosSemidef.zero
      refine ⟨Matrix.posSemidef_sum _ fun w _ => Matrix.posSemidef_sum _ fun y _ => hterm w y, ?_⟩
      have hcompl : 1 - G = ∑ w, ∑ y, if T 1 w y then 0 else Matrix.kronecker (proj w) (E y) := by
        rw [← sum_kron_eq_one (W := W) E hE.2, hGdef, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
      rw [hcompl]
      refine Matrix.posSemidef_sum _ fun w _ => Matrix.posSemidef_sum _ fun y _ => ?_
      split_ifs
      · exact Matrix.PosSemidef.zero
      · exact (proj_posSemidef w).kronecker (hE.1 y)
    have hk : Matrix.kronecker U (1 : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup (W × ι) ℂ :=
      Matrix.kronecker_mem_unitary hU (one_mem _)
    have hχ : IsState χ := by
      show ‖χ‖ = 1
      rw [hχdef, act_norm_of_mem_unitaryGroup hk]
      exact hφ0
    have hov' : 1 - 2 * ε ≤ (inner ℂ χ φ1).re := by
      rw [hχdef, hov, Complex.ofReal_re]
      exact hF
    obtain ⟨h1, h2, h3, h4⟩ := effectProb_sub_le_two_norm_sub χ φ1 hχ hφ1 G hG ε hov'
    rw [hcheat, hhonest]
    have h1' := (abs_sub_le_iff.mp h1).2
    linarith
