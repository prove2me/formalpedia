-- Prove2me | solution 1 for GlobalTheory.PolyNorm.ev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:06:31.255322+00:00
-- url     : https://prove2.me/submissions/7914d4c1-40b3-4f37-b3cd-cb58884075a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
import Theorems.Thm_GlobalTheory_PolyNorm_ev_map
import Theorems.Thm_GlobalTheory_PolyNorm_gen_map
import Theorems.Thm_GlobalTheory_PolyNorm_gen_coeff
import Theorems.Thm_GlobalTheory_PolyNorm_natDegree_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN
namespace GlobalTheory.PolyNorm
theorem _root_.solution (hm : ∀ F G, N (F * G) = N F * N G) {K : Type} [CommRing K] [Algebra ℚ K]
    (r₁ r₂ s : ℕ) (hs : r₁ + r₂ < s) (F G : K[X]) (hF : F.natDegree ≤ r₁)
    (hG : G.natDegree ≤ r₂) :
    ev (Φ s) (F * G) = ev (Φ (r₁ + 1)) F * ev (Φ (r₂ + 1)) G := by
  let R := MvPolynomial (Fin (r₁ + 1) ⊕ Fin (r₂ + 1)) ℚ
  let A : R[X] := gen fun i => MvPolynomial.X (Sum.inl i)
  let B : R[X] := gen fun i => MvPolynomial.X (Sum.inr i)
  have key : ev (Φ s) (A * B) = ev (Φ (r₁ + 1)) A * ev (Φ (r₂ + 1)) B := by
    apply MvPolynomial.funext_set (s := fun _ => Set.range (Int.cast : ℤ → ℚ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective)
    intro x hx
    choose y hy using fun i => hx i (Set.mem_univ i)
    have hA : A.map (MvPolynomial.eval x) =
        (gen fun i => y (Sum.inl i)).map (Int.castRingHom ℚ) := by
      simp [A, gen_map, hy]
    have hB : B.map (MvPolynomial.eval x) =
        (gen fun i => y (Sum.inr i)).map (Int.castRingHom ℚ) := by
      simp [B, gen_map, hy]
    have h1 := natDegree_gen fun i => y (Sum.inl i)
    have h2 := natDegree_gen fun i => y (Sum.inr i)
    rw [map_mul, ev_map, ev_map, ev_map, Polynomial.map_mul, hA, hB, ← Polynomial.map_mul,
      ← hN, ← hN, ← hN, hm]
    · omega
    · omega
    · exact lt_of_le_of_lt natDegree_mul_le (by omega)
  let φ : R →+* K := (MvPolynomial.aeval
    (Sum.elim (fun i : Fin (r₁ + 1) => F.coeff i) (fun i : Fin (r₂ + 1) => G.coeff i))).toRingHom
  have hA : A.map φ = F := by
    refine (gen_map _ _).trans (Eq.trans ?_ (gen_coeff F (Nat.lt_succ_of_le hF)))
    congr 1
    exact funext fun i => MvPolynomial.aeval_X _ _
  have hB : B.map φ = G := by
    refine (gen_map _ _).trans (Eq.trans ?_ (gen_coeff G (Nat.lt_succ_of_le hG)))
    congr 1
    exact funext fun i => MvPolynomial.aeval_X _ _
  have := congrArg φ key
  rwa [map_mul, ev_map, ev_map, ev_map, Polynomial.map_mul, hA, hB] at this
end GlobalTheory.PolyNorm
