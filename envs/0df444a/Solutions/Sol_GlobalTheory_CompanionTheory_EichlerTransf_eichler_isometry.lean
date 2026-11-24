-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EichlerTransf.eichler_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:00:06.196539+00:00
-- url     : https://prove2.me/submissions/ce466a81-f3a8-4a29-b7d8-ae5ee2256154

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.EichlerTransf
theorem _root_.solution (J : Matrix (Fin n) (Fin n) ℂ) (a d : Matrix (Fin n) (Fin m) ℂ)
    (F : Matrix (Fin m) (Fin m) ℂ) (hJh : Jᴴ = J) (h1 : aᴴ * J * a = 0) (h2 : aᴴ * J * d = 0)
    (hF : F + Fᴴ = dᴴ * J * d) :
    (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J))ᴴ * J *
      (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J)) = J := by
  have h3 : dᴴ * J * a = 0 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have key : (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J))ᴴ * J =
      J - J * d * (aᴴ * J) - J * a * Fᴴ * (aᴴ * J) + J * a * (dᴴ * J) := by
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_neg,
      conjTranspose_one, conjTranspose_conjTranspose, hJh, Matrix.add_mul, Matrix.sub_mul,
      Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [key]
  generalize hL : aᴴ * J = L at *
  generalize hD : dᴴ * J = D at *
  set N := 1 + a * (-D - F * L) + d * L with hN
  have hLN : L * N = L := by
    simp only [hN, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, h1, h2, Matrix.zero_mul,
      add_zero]
  have hDN : D * N = D + (F + Fᴴ) * L := by
    rw [hF]
    simp only [hN, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, h3, Matrix.zero_mul,
      add_zero]
  calc (J - J * d * L - J * a * Fᴴ * L + J * a * D) * N
      = J * N - J * d * (L * N) - J * a * Fᴴ * (L * N) + J * a * (D * N) := by
        simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    _ = J := by
        rw [hLN, hDN, hN]
        simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_neg, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
end GlobalTheory.CompanionTheory.EichlerTransf
