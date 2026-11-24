-- Prove2me | solution 1 for GlobalTheory.CuspCentre.exists_pos_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:04.789572+00:00
-- url     : https://prove2.me/submissions/7522b723-845a-44b9-82c8-0b3bb10a52b7

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SkewMatrixMultipleInLattice
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



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.CuspCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.CuspCentre
theorem _root_.solution (X : Data E r) (v : Fin r → E) : ∃ n : ℕ, 0 < n ∧ n • v ∈ X.Λ := by
  have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, mul_pos hm hn, ?_⟩
    have : (m * n) • (x + y) = n • m • x + m • n • y := by
      rw [smul_add, smul_smul, smul_smul, mul_comm n m]
    rw [this]
    exact X.Λ.add_mem (nsmul_mem hx _) (nsmul_mem hy _)
  | smul c x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
    have hki' : IsIntegral ℤ ((k * k) • c) := by
      rw [mul_smul]; exact hki.smul k
    refine ⟨(k.natAbs * k.natAbs) * m, mul_pos (mul_pos (Int.natAbs_pos.2 hk) (Int.natAbs_pos.2 hk)) hm, ?_⟩
    have h1 := X.Λ.smul_mem (⟨(k * k) • c, hki'⟩ : 𝓞 E) hx
    have h2 : ((k.natAbs * k.natAbs : ℕ) : E) = ((k * k : ℤ) : E) := by
      rw [← Int.natAbs_mul_self, Int.cast_natCast]
    convert h1 using 1
    funext i
    show ((k.natAbs * k.natAbs) * m) • (c * x i) = ((k * k) • c) * (m • x i)
    rw [nsmul_eq_mul, nsmul_eq_mul, zsmul_eq_mul, Nat.cast_mul, h2]
    ring
end GlobalTheory.CuspCentre
