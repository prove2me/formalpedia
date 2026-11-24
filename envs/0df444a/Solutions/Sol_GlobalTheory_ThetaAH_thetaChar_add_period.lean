-- Prove2me | solution 1 for GlobalTheory.ThetaAH.thetaChar_add_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:30:04.554243+00:00
-- url     : https://prove2.me/submissions/72a8279d-8143-437b-8b2f-3fe9abbfca1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExpMulThetaCharAutomorphy
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q


section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
namespace GlobalTheory.ThetaAH
variable {g : ℕ}
open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma intCast_dotProduct' (k m : Fin g → ℤ) :
    ((k ⬝ᵥ m : ℤ) : ℂ) = (fun i => (k i : ℂ)) ⬝ᵥ (fun i => (m i : ℂ)) := by
  simp [dotProduct]
end GlobalTheory.ThetaAH
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.ThetaAH
variable {g : ℕ}
open NumberField
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix nonZeroDivisors
variable {g : ℕ}
namespace GlobalTheory.ThetaAH
namespace _root_.GlobalTheory.ThetaAH
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (a b w : Fin g → ℂ)
    (m n : Fin g → ℤ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b (w + ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))) =
      Complex.exp (Real.pi * Complex.I * (2 * (a ⬝ᵥ fun i => (m i : ℂ)) - 2 * ((fun i => (n i : ℂ)) ⬝ᵥ b)
        - ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ)) - 2 * ((fun i => (n i : ℂ)) ⬝ᵥ w))) *
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar
  rw [← (Equiv.subRight n).tsum_eq, ← tsum_mul_left]
  congr 1
  funext k
  set N : Fin g → ℂ := fun i => (n i : ℂ)
  set M : Fin g → ℂ := fun i => (m i : ℂ)
  set K : Fin g → ℂ := fun i => (k i : ℂ)
  have hc : (fun i => (((Equiv.subRight n k) i : ℤ) : ℂ)) = K - N := by
    funext i; simp [K, N]
  have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hs.eq]
  rw [hc, ← Complex.exp_add]
  have key : Real.pi * Complex.I * ((K - N + a) ⬝ᵥ τ *ᵥ (K - N + a)) +
      2 * Real.pi * Complex.I * ((K - N + a) ⬝ᵥ (w + (M + τ *ᵥ N) + b)) =
      Real.pi * Complex.I * (2 * (a ⬝ᵥ M) - 2 * (N ⬝ᵥ b) - (N ⬝ᵥ τ *ᵥ N) - 2 * (N ⬝ᵥ w)) +
      (Real.pi * Complex.I * ((K + a) ⬝ᵥ τ *ᵥ (K + a)) +
        2 * Real.pi * Complex.I * ((K + a) ⬝ᵥ (w + b))) +
      (((k ⬝ᵥ m - n ⬝ᵥ m : ℤ) : ℂ)) * (2 * Real.pi * Complex.I) := by
    have h1 := hsym N (K + a)
    push_cast
    rw [intCast_dotProduct', intCast_dotProduct']
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub, sub_dotProduct, dotProduct_add,
      add_dotProduct] at h1 ⊢
    linear_combination (-(Real.pi * Complex.I)) * h1
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end _root_.GlobalTheory.ThetaAH
end GlobalTheory.ThetaAH
