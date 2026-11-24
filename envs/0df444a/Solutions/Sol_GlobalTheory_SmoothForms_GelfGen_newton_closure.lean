-- Prove2me | solution 1 for GlobalTheory.SmoothForms.GelfGen.newton_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:45.551985+00:00
-- url     : https://prove2.me/submissions/0f35034e-2785-44ae-b26c-fd7019fc5aa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms
noncomputable section
open GlobalTheory.SmoothForms.PermWord
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.GelfGen
namespace GlobalTheory.SmoothForms.GelfGen
theorem _root_.solution {K : Type} [Field K] [Algebra ℂ K] {n : ℕ} (l : Fin n → K) (P : ℕ → K → Prop)
    (h1 : P 0 1) (h0 : ∀ j, P j 0) (hadd : ∀ j x y, P j x → P j y → P j (x + y))
    (hsmul : ∀ j (c : ℂ) x, P j x → P j (c • x)) (hmul : ∀ i j x y, P i x → P j y → P (i + j) (x * y))
    (hbase : ∀ j, 1 ≤ j → j ≤ n → P j (∑ i, l i ^ j)) : ∀ j, 1 ≤ j → P j (∑ i, l i ^ j) := by
  classical
  let Q : ℕ → MvPolynomial (Fin n) ℂ → Prop := fun j p => P j (MvPolynomial.aeval l p)
  have hps : ∀ j, MvPolynomial.aeval l (MvPolynomial.psum (Fin n) ℂ j) = ∑ i, l i ^ j := by
    intro j; simp [MvPolynomial.psum]
  have qadd : ∀ j x y, Q j x → Q j y → Q j (x + y) := fun j x y hx hy => by
    simpa [Q] using hadd j _ _ hx hy
  have qC : ∀ j (c : ℂ) x, Q j x → Q j (MvPolynomial.C c * x) := fun j c x hx => by
    rw [MvPolynomial.C_mul']; simpa [Q] using hsmul j c _ hx
  have qmul : ∀ i j x y, Q i x → Q j y → Q (i + j) (x * y) := fun i j x y hx hy => by
    simpa [Q] using hmul i j _ _ hx hy
  have qsign : ∀ j m x, Q j x → Q j ((-1) ^ m * x) := fun j m x hx => by
    have : ((-1 : MvPolynomial (Fin n) ℂ)) ^ m = MvPolynomial.C ((-1) ^ m) := by simp
    rw [this]; exact qC j _ x hx
  have qsub : ∀ j x y, Q j x → Q j y → Q j (x - y) := fun j x y hx hy => by
    rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← pow_one (-1 : MvPolynomial (Fin n) ℂ)]
    exact qadd j _ _ hx (qsign j 1 y hy)
  have qsum : ∀ j (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → MvPolynomial (Fin n) ℂ), (∀ a ∈ s, Q j (g a)) →
      Q j (∑ a ∈ s, g a) := fun j s g hg =>
    Finset.sum_induction _ (Q j) (qadd j) (by simpa [Q] using h0 j) hg
  have qbase : ∀ j, 1 ≤ j → j ≤ n → Q j (MvPolynomial.psum (Fin n) ℂ j) := fun j h1 h2 => by
    simpa [Q, hps] using hbase j h1 h2
  have hesymm : ∀ k, Q k (MvPolynomial.esymm (Fin n) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa [Q] using h1
      by_cases hkn : n < k
      · have : MvPolynomial.esymm (Fin n) ℂ k = 0 := by
          simp only [MvPolynomial.esymm]
          rw [Finset.powersetCard_eq_empty.2 (by rw [Finset.card_univ, Fintype.card_fin]; exact hkn), Finset.sum_empty]
        rw [this]; simpa [Q] using h0 k
      have hm := MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k
      have hQ : Q k ((k : MvPolynomial (Fin n) ℂ) * MvPolynomial.esymm (Fin n) ℂ k) := by
        rw [hm]
        refine qsign _ _ _ (qsum _ _ _ fun a ha => ?_)
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        rw [mul_assoc]
        refine qsign _ _ _ ?_
        have := qmul _ _ _ _ (ih a.1 ha.2) (qbase a.2 (by omega) (by omega))
        rwa [ha.1] at this
      have := qC k ((k : ℂ)⁻¹) _ hQ
      rwa [← mul_assoc, ← map_natCast MvPolynomial.C k, ← map_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk.ne'), map_one, one_mul] at this
  have hpsum : ∀ k, 1 ≤ k → Q k (MvPolynomial.psum (Fin n) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hkn : k ≤ n
      · exact qbase k hk hkn
      rw [MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℂ k (by omega)]
      refine qsub _ _ _ ?_ (qsum _ _ _ fun a ha => ?_)
      · rw [mul_assoc, ← map_natCast MvPolynomial.C k]
        exact qsign _ _ _ (qC _ _ _ (hesymm k))
      · rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo] at ha
        rw [mul_assoc]
        refine qsign _ _ _ ?_
        have := qmul _ _ _ _ (hesymm a.1) (ih a.2 (by omega) (by omega))
        rwa [ha.1] at this
  intro j hj
  simpa [Q, hps] using hpsum j hj
end GlobalTheory.SmoothForms.GelfGen
