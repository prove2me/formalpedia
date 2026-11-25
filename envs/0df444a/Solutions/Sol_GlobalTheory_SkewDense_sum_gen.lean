-- Prove2me | solution 1 for GlobalTheory.SkewDense.sum_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:11:32.704057+00:00
-- url     : https://prove2.me/submissions/f383ac52-3fe3-4aa4-9064-0aa86d38939f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.SkewDense
namespace GlobalTheory.SkewDense
theorem _root_.solution {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {κ : Type} [Fintype κ] (b : κ → E)
    (g : E →+* ℂ) (z : Fin n × Fin n × κ → ℂ) (i j : Fin n) :
    ∑ G : Fin n × Fin n × κ, z G * g (gen σ G.1 G.2.1 (b G.2.2) i j) =
      ∑ k, z (i, j, k) * g (b k) - ∑ k, z (j, i, k) * g (σ (b k)) := by
  have e : ∀ (f : Fin n → Fin n → κ → ℂ) (p q : Fin n),
      (∑ G : Fin n × Fin n × κ, if G.1 = p ∧ G.2.1 = q then f G.1 G.2.1 G.2.2 else 0) = ∑ k, f p q k := by
    intro f p q
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single p (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single q (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [← e (fun u v k => z (u, v, k) * g (b k)) i j, ← e (fun u v k => z (u, v, k) * g (σ (b k))) j i,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun G _ => ?_
  simp only [gen, Matrix.sub_apply, Matrix.single_apply, map_sub, apply_ite g, map_zero, mul_sub, mul_ite, mul_zero,
    and_comm]
end GlobalTheory.SkewDense
