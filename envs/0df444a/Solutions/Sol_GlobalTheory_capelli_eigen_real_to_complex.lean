-- Prove2me | solution 1 for GlobalTheory.capelli_eigen_real_to_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:45.915623+00:00
-- url     : https://prove2.me/submissions/aa8c175c-6a31-478e-8f56-5e780d1e18fc

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliEigenRealToComplex
import Theorems.Thm_GlobalTheory_entire_eq_of_eq_on_reals
import Theorems.Thm_Formalism_FourierDecayAlt_P_leading_term_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) f → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∀ Y : ℂ, ∀ g ∈ B.GV k r, Q.CV k r Y f g = (∏ s, (Y + (lam s : ℂ))) • f g := by
  intro k r Wp Wq _ _ _ _ _ _ lam f hf hR Y g hg
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hs : Q.SmoothLev k r 0 Set.univ f := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀.1.1
    exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩
  have hg0 : g ∈ Q.Glev k r 0 := ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  have h0 : Formalism.QuantumDeterminants.inWb k r 0 := by
    unfold Formalism.QuantumDeterminants.inWb
    simp
  obtain ⟨A, hA⟩ := Formalism.FourierDecayAlt.P.leading_term_alt (Wq →L[ℂ] Wp) k r 0 0 0 h0 h0
  have hpoly : (fun Y : ℂ => Q.CV k r Y f g) = fun Y : ℂ => Y ^ Q.mdim k r 0 • f g +
      ∑ j ∈ Finset.range (Q.mdim k r 0), Y ^ j • A 0 0 j f g := by
    funext Y
    exact (hA Set.univ f isOpen_univ hs g ⟨hg0, trivial⟩ Y).1
  have key := entire_eq_of_eq_on_reals (fun Y : ℂ => Q.CV k r Y f g)
    (fun Y : ℂ => (∏ s, (Y + (lam s : ℂ))) • f g) (by rw [hpoly]; fun_prop)
    (by
      refine Differentiable.smul_const ?_ _
      exact Differentiable.fun_finsetProd fun s _ => by fun_prop)
    (fun y => by
      show Q.CV k r (y : ℂ) f g = _
      rw [hR y g hg]; push_cast; rfl)
  exact congrFun key Y
end GlobalTheory
