-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.nm_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:09.213592+00:00
-- url     : https://prove2.me/submissions/4bf2e214-a2d2-4ff5-9c3e-b282464862ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex
variable {A B C : Type} [Field A] [Field B] [Field C]
namespace GlobalTheory.QuadSymbol.NormBaseChange
theorem _root_.solution [Algebra A B] [FiniteDimensional A B] {d : A} {x : B}
    (h : Nm (algebraMap A B d) x) : Nm d (Algebra.norm A x) := by
  classical
  obtain ⟨a, b, rfl⟩ := h
  let e := Module.finBasis A B
  let R := QuadraticAlgebra A d 0
  let φ : B →ₐ[A] Matrix (Fin (Module.finrank A B)) (Fin (Module.finrank A B)) R :=
    (AlgHom.mapMatrix (Algebra.ofId A R)).comp (Algebra.leftMulMatrix e)
  let t : R := QuadraticAlgebra.omega
  have ht : t * t = algebraMap A R d := by
    ext <;> simp [t, R]
  have hst : star t = -t := by
    ext <;> simp [t, R]
  have hφ : ∀ y : B, (φ y).map (starRingEnd R) = φ y := fun y => by
    ext1 i j
    ext <;> simp [φ, R, starRingEnd_apply]
  have h1 : φ (a ^ 2 - algebraMap A B d * b ^ 2) = (φ a + t • φ b) * (φ a - t • φ b) := by
    have hc : φ a * φ b = φ b * φ a := by rw [← map_mul, ← map_mul, mul_comm]
    rw [map_sub, map_mul, AlgHom.commutes, ← Algebra.smul_def, pow_two, pow_two, map_mul, map_mul,
      add_mul, mul_sub, mul_sub, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      smul_smul, ht, algebraMap_smul, hc]
    abel
  have h2 : (φ a - t • φ b).det = star (φ a + t • φ b).det := by
    rw [← starRingEnd_apply, RingHom.map_det]
    congr 1
    ext1 i j
    have ha := congrFun (congrFun (hφ a) i) j
    have hb := congrFun (congrFun (hφ b) i) j
    simp only [Matrix.map_apply] at ha hb
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, map_add, map_mul, ha, hb]
    rw [starRingEnd_apply, hst]
    ring
  have h3 : algebraMap A R (Algebra.norm A (a ^ 2 - algebraMap A B d * b ^ 2)) =
      (φ (a ^ 2 - algebraMap A B d * b ^ 2)).det := by
    rw [Algebra.norm_eq_matrix_det e, RingHom.map_det]
    rfl
  rw [h1, Matrix.det_mul, h2, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star] at h3
  rw [(algebraMap A R).injective h3, QuadraticAlgebra.norm_def]
  exact ⟨(φ a + t • φ b).det.re, (φ a + t • φ b).det.im, by ring⟩
end GlobalTheory.QuadSymbol.NormBaseChange
