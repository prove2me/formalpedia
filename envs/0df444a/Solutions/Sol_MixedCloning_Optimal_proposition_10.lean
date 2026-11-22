-- Prove2me | solution 1 for MixedCloning.Optimal.proposition_10
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T02:08:50.045642+00:00
-- url     : https://prove2.me/submissions/f8218f7e-f2eb-4ed8-a24f-7cc2dbac5f02

import Theorems.Thm_MixedCloning_Optimal_lemma_6
import Theorems.Thm_MixedCloning_Optimal_pct_isChannel
import Theorems.Thm_MixedCloning_Optimal_werner_pure_fidelity
import Theorems.Thm_MixedCloning_Optimal_fidelity_le_partialTrace
import Theorems.Thm_MixedCloning_Optimal_pct_fidelity_ge_of_purifications

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Tracing out `B_1,…,B_m` from `X^{⊗m}` gives `(tr_B X)^{⊗m}`. -/
lemma prop10_partialTrace_tensorPower {a b : Type} [Fintype b] (m : ℕ) (X : Op (a × b)) :
    partialTrace m (tensorPower m X) = tensorPower m (fun i j => ∑ z : b, X (i, z) (j, z)) := by
  ext i j
  simp only [partialTrace, tensorPower]
  rw [Fintype.prod_sum]

/-- `(|u⟩⟨u|)^{⊗m} = |u^{⊗m}⟩⟨u^{⊗m}|` is positive semidefinite. -/
lemma prop10_tensorPower_pure_posSemidef {a : Type} [Fintype a] (m : ℕ) (u : a → ℂ) :
    (tensorPower m (pure u)).PosSemidef := by
  have h : tensorPower m (pure u) =
      vecMulVec (fun i : Word a m => ∏ t, u (i t)) (star fun i : Word a m => ∏ t, u (i t)) := by
    ext i j
    simp only [tensorPower, MixedCloning.Optimal.pure, vecMulVec, Matrix.of_apply, Pi.star_apply,
      RCLike.star_def, Finset.prod_mul_distrib, map_prod]
  rw [h]
  exact posSemidef_vecMulVec_self_star _

theorem solution (d r n k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : 1 ≤ n)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n))
    (hR : IsRPC d r n R) (tau : Op (Word (Fin d × Fin r) (n+k))) (htau : IsState tau) :
    Clones d r n k ((k : ℝ)*r*d/n) (pct d r n k R tau) ∧
    ∀ eps : ℝ, 0 < eps → Nat.ceil ((k : ℝ)*r*d/eps) ≤ n →
      Clones d r n k eps (pct d r n k R tau) := by
  have hch : QAlgorithms.IsChannel (pct d r n k R tau) :=
    pct_isChannel d r n k hd hr R hR.1 tau htau
  have hmain : ∀ rho : Op (Fin d), IsState rho → rho.rank ≤ r →
      1 - (k : ℝ)*r*d/n ≤
        fidelity (pct d r n k R tau (tensorPower n rho)) (tensorPower (n+k) rho) := by
    intro rho hrho hrank
    apply pct_fidelity_ge_of_purifications d r n k R hR tau rho hrho hrank
    intro u hu hmarg
    obtain ⟨hstate, hfid⟩ := werner_pure_fidelity (a := Fin d × Fin r) n k tau u hu
    have hcard : Fintype.card (Fin d × Fin r) = d * r := by simp
    have h6 := lemma_6 n (d*r) k hn (Nat.mul_pos hd hr)
    have htp : tensorPower (n+k) rho = partialTrace (n+k) (tensorPower (n+k) (pure u)) := by
      rw [prop10_partialTrace_tensorPower, hmarg]
    have hratio : 1 - (k : ℝ)*r*d/n ≤ (symDimension (Fintype.card (Fin d × Fin r)) n : ℝ) /
        symDimension (Fintype.card (Fin d × Fin r)) (n+k) := by
      rw [hcard]
      calc 1 - (k : ℝ)*r*d/n = 1 - (k : ℝ)*((d*r : ℕ) : ℝ)/n := by push_cast; ring
        _ ≤ _ := h6
    have h7 := hratio.trans_eq hfid.symm
    have hdp := fidelity_le_partialTrace (a := Fin d) (b := Fin r) (n+k)
      (werner (Fin d × Fin r) n k tau (tensorPower n (pure u))) (tensorPower (n+k) (pure u))
      hstate.1 (prop10_tensorPower_pure_posSemidef (n+k) _)
    rw [htp]
    exact h7.trans hdp
  refine ⟨⟨hch, hmain⟩, ?_⟩
  intro eps heps hceil
  refine ⟨hch, fun rho hrho hrank => le_trans ?_ (hmain rho hrho hrank)⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (k : ℝ)*r*d/eps ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have h2 : (k : ℝ)*r*d/n ≤ eps := by
    rw [div_le_iff₀ hn']
    rw [div_le_iff₀ heps] at h1
    linarith
  linarith
