-- Prove2me | solution 1 for KeystoneLadder.xLadderPair_same_xPair_EDS
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:40.530764+00:00
-- url     : https://prove2.me/submissions/7c2eec0d-e7a3-4569-a358-f20f7229e79e

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneLadder
import Definitions.Def_PsiInvariant
import Theorems.Thm_KeystoneLadder_SameP1Vec_refl
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
import Theorems.Thm_KeystoneLadder_XOnly_diffAddOrInfVec_congr
import Theorems.Thm_KeystoneLadder_XOnly_doubleVec_congr
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_three
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_four
import Theorems.Thm_KeystoneLadder_xPair_double_and_diffAddOrInf_EDS_core
import Definitions.Def_KeystoneCoprimality
import Definitions.Def_WardSomos
import Definitions.Def_KeystoneDoubling

/-! Proofs of the lemmas stated in `Theorems.Thm_XOnlyLadder_XPairSameAsLadder` and their helpers. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

variable {k : Type*} [Field k]

namespace KeystoneLadder

open XOnly

theorem _root_.solution
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W (n : ℤ) x ≠ 0 ∧
    xPair W ((n + 1 : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.xLadderPair (E := W⁄k) x n).1
      (xPair W (n : ℤ) x) ∧
    SameP1Vec
      (XOnly.xLadderPair (E := W⁄k) x n).2
      (xPair W ((n + 1 : ℕ) : ℤ) x) := by
    classical
    have hD :
        SameP1Vec (XOnly.xAffVec x) (xPair W (1 : ℤ) x) := by
      simpa [xPair, XOnly.xAffVec] using SameP1Vec.refl (![x, 1] : Fin 2 → k)
    induction n using Nat.strong_induction_on with
    | h n IH =>
        rcases n with _ | n
        · constructor
          · simp [xPair]
          · constructor
            · simp [xPair]
            · constructor
              · simpa [XOnly.xLadderPair, xPair, XOnly.xInfVec] using
                  SameP1Vec.refl (![1, 0] : Fin 2 → k)
              · simpa [XOnly.xLadderPair] using hD
        · rcases n with _ | n
          · have hcore := xPair_double_and_diffAddOrInf_EDS_core (W := W) 1 x h4 hψ_ne hc3
            have hdouble :
                SameP1Vec
                  (XOnly.doubleVec (E := W⁄k) (XOnly.xAffVec x))
                  (xPair W (2 : ℤ) x) := by
              exact SameP1Vec.trans (XOnly.doubleVec_congr (E := W⁄k) hD) hcore.2.1
            constructor
            · simp [xPair]
            · constructor
              · simpa using hcore.1
              · constructor
                · simpa [XOnly.xLadderPair] using hD
                · simpa [XOnly.xLadderPair] using hdouble
          · let N : ℕ := n + 2
            let m : ℕ := N / 2
            change
              xPair W (N : ℤ) x ≠ 0 ∧
              xPair W ((N + 1 : ℕ) : ℤ) x ≠ 0 ∧
              SameP1Vec
                (XOnly.xLadderPair (E := W⁄k) x N).1
                (xPair W (N : ℤ) x) ∧
              SameP1Vec
                (XOnly.xLadderPair (E := W⁄k) x N).2
                (xPair W ((N + 1 : ℕ) : ℤ) x)
            have hm_lt : m < N := by
              dsimp [m, N]
              omega
            have IHm := IH m (by
              dsimp [m, N]
              omega)
            have hcore_m := xPair_double_and_diffAddOrInf_EDS_core (W := W) m x h4 hψ_ne hc3
            have hcore_ms := xPair_double_and_diffAddOrInf_EDS_core (W := W) (m + 1) x h4 hψ_ne hc3
            have hdouble₀ :
                SameP1Vec
                  (XOnly.doubleVec (E := W⁄k) (XOnly.xLadderPair (E := W⁄k) x m).1)
                  (xPair W ((2 * m : ℕ) : ℤ) x) := by
              exact SameP1Vec.trans
                (XOnly.doubleVec_congr (E := W⁄k) IHm.2.2.1)
                hcore_m.2.1
            have hadd :
                SameP1Vec
                  (XOnly.diffAddOrInfVec (E := W⁄k)
                    (XOnly.xLadderPair (E := W⁄k) x m).1
                    (XOnly.xLadderPair (E := W⁄k) x m).2
                    (XOnly.xAffVec x))
                  (xPair W ((2 * m + 1 : ℕ) : ℤ) x) := by
              exact SameP1Vec.trans
                (XOnly.diffAddOrInfVec_congr (E := W⁄k) IHm.2.2.1 IHm.2.2.2 hD)
                hcore_m.2.2.2
            have hdouble₁ :
                SameP1Vec
                  (XOnly.doubleVec (E := W⁄k) (XOnly.xLadderPair (E := W⁄k) x m).2)
                  (xPair W ((2 * (m + 1) : ℕ) : ℤ) x) := by
              exact SameP1Vec.trans
                (XOnly.doubleVec_congr (E := W⁄k) IHm.2.2.2)
                hcore_ms.2.1
            by_cases hEven : Even N
            · have hN : N = 2 * m := by
                simpa [m] using (Nat.two_mul_div_two_of_even hEven).symm
              have hN1 : N + 1 = 2 * m + 1 := by omega
              constructor
              · simpa [hN] using hcore_m.1
              · constructor
                · simpa [hN1] using hcore_m.2.2.1
                · constructor
                  · have hfirst :
                      SameP1Vec
                        (XOnly.doubleVec (E := W⁄k)
                          (XOnly.xLadderPair (E := W⁄k) x m).1)
                        (xPair W (N : ℤ) x) := by
                      simpa [hN] using hdouble₀
                    simpa [XOnly.xLadderPair, N, m, hEven] using hfirst
                  · have hsecond :
                      SameP1Vec
                        (XOnly.diffAddOrInfVec (E := W⁄k)
                          (XOnly.xLadderPair (E := W⁄k) x m).1
                          (XOnly.xLadderPair (E := W⁄k) x m).2
                          (XOnly.xAffVec x))
                        (xPair W ((N + 1 : ℕ) : ℤ) x) := by
                      simpa [hN1] using hadd
                    simpa [XOnly.xLadderPair, N, m, hEven] using hsecond
            · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
              have hN : N = 2 * m + 1 := by
                simpa [m] using (Nat.two_mul_div_two_add_one_of_odd hOdd).symm
              have hN1 : N + 1 = 2 * (m + 1) := by omega
              constructor
              · simpa [hN] using hcore_m.2.2.1
              · constructor
                · simpa [hN1] using hcore_ms.1
                · constructor
                  · have hfirst :
                      SameP1Vec
                        (XOnly.diffAddOrInfVec (E := W⁄k)
                          (XOnly.xLadderPair (E := W⁄k) x m).1
                          (XOnly.xLadderPair (E := W⁄k) x m).2
                          (XOnly.xAffVec x))
                        (xPair W (N : ℤ) x) := by
                      simpa [hN] using hadd
                    simpa [XOnly.xLadderPair, N, m, hEven] using hfirst
                  · have hsecond :
                      SameP1Vec
                        (XOnly.doubleVec (E := W⁄k)
                          (XOnly.xLadderPair (E := W⁄k) x m).2)
                        (xPair W ((N + 1 : ℕ) : ℤ) x) := by
                      simpa [hN1] using hdouble₁
                    simpa [XOnly.xLadderPair, N, m, hEven] using hsecond

end KeystoneLadder
