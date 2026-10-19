-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.energyGradient_supported_path_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:22:56.397983+00:00
-- url     : https://prove2.me/submissions/2bb34f2f-6256-4d8f-bf7b-ca09d95ca3d8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Support.lean:L209-L235
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.energyGradient_supported_path_hasDerivAt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_add_projection
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rootCost_eq_of_solution
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_sqrt_smoothWithin_posDef

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

theorem traceReal_mul_comm (A B : Matrix ι ι ℂ) : traceReal (A * B) = traceReal (B * A) := by
  unfold traceReal; rw [Matrix.trace_mul_comm]
theorem traceReal_mul_cycle (A B C : Matrix ι ι ℂ) :
    traceReal (A * B * C) = traceReal (C * A * B) := by
  unfold traceReal; rw [Matrix.trace_mul_cycle]
theorem hsReal_symm (X Y : Matrix ι ι ℂ) : hsReal X Y = hsReal Y X := by
  unfold hsReal
  rw [← traceReal_star (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem hsReal_sylv_symm {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) : hsReal X (sylv A Y) = hsReal (sylv A X) Y := by
  simp only [hsReal, sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hA.eq, mul_add, add_mul, traceReal_add]
  rw [← Matrix.mul_assoc Xᴴ A Y, ← Matrix.mul_assoc Xᴴ Y A,
    traceReal_mul_cycle Xᴴ Y A]

variable [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sqrtInverse_solves {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    sylv (CFC.sqrt P) (sqrtInverse hP K) = K := by
  exact (sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).apply_symm_apply K

lemma hessianPairPD_symm {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    hessianPairPD hP K L = hessianPairPD hP L K := by
  have hs := hsReal_sylv_symm
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
    (sqrtInverse hP K) (sqrtInverse hP L)
  rw [sqrtInverse_solves, sqrtInverse_solves, hsReal_symm _ L] at hs
  exact congrArg ((3 / 2 : ℝ) * ·) hs.symm

lemma hessianPairPD_self {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    hessianPairPD hP K K = hessianCost P K := by
  exact (rootCost_eq_of_solution
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) (sqrtInverse_solves hP K)).symm

lemma hessianPairPD_eq_trace {P K L : Matrix ι ι ℂ}
    (hP : P.PosDef) (hK : K.IsHermitian) :
    hessianPairPD hP K L = (3 / 2 : ℝ) * traceReal (sqrtInverse hP L * K) := by
  simp only [hessianPairPD, hsReal, hK.eq, traceReal_mul_comm K]

theorem energyGradient_path_hasDerivAt {P K : ℝ → Matrix ι ι ℂ}
    {U V : Matrix ι ι ℂ} {x : ℝ}
    (hP : (P x).PosDef) (hn : ∀ᶠ t in 𝓝 x, 0 ≤ P t)
    (hK : (K x).IsHermitian) (hdP : HasDerivAt P U x) (hdK : HasDerivAt K V x) :
    HasDerivAt (fun t => energyGradient (P t) (K t))
      (hessianPairPD hP (K x) U + energyGradient (P x) V) x := by
  have hs : HasDerivAt (fun t => CFC.sqrt (P t)) (sqrtInverse hP U) x :=
    (sqrt_smoothWithin_posDef hP).2.comp_hasDerivAt x hdP hn
  have hm := hs.fun_mul hdK
  have ht := (traceRealCLM.hasFDerivAt.comp_hasDerivAt x hm).const_smul (3 / 2 : ℝ)
  convert! ht using 1
  simp only [hessianPairPD_eq_trace hP hK, energyGradient_apply,
    traceRealCLM_apply, traceReal_add, smul_eq_mul]
  ring

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Support ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sqrt_mul_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hPQ : P * Q = 0) : CFC.sqrt P * Q = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  change (CFC.sqrt P * Q)ᴴ * (CFC.sqrt P * Q) = 0
  rw [Matrix.conjTranspose_mul, hs.eq, ← Matrix.mul_assoc,
    Matrix.mul_assoc Qᴴ, CFC.sqrt_mul_sqrt_self P hP.nonneg,
    Matrix.mul_assoc, hPQ, mul_zero]

lemma mul_sqrt_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQP : Q * P = 0) : Q * CFC.sqrt P = 0 := by
  have ht : P * Qᴴ = 0 := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hQP
  have hz := sqrt_mul_eq_zero_of_mul_eq_zero hP ht
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  simpa only [Matrix.conjTranspose_mul, hs.eq, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hz

lemma sqrt_add_projection {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    CFC.sqrt (P + Q) = CFC.sqrt P + Q := by
  apply CFC.sqrt_unique
  · have hsQ := sqrt_mul_eq_zero_of_mul_eq_zero hP hPQ
    have hQs := mul_sqrt_eq_zero_of_mul_eq_zero hP hQP
    simp only [add_mul, mul_add, hsQ, hQs, hQQ,
      CFC.sqrt_mul_sqrt_self P hP.nonneg, add_zero, zero_add]
  · exact add_nonneg (CFC.sqrt_nonneg P) hQ.nonneg

lemma energyGradient_add_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hQK : Q * K = 0) :
    energyGradient (P + Q) K = energyGradient P K := by
  simp only [energyGradient_apply, sqrt_add_projection hP hQ hQQ hPQ hQP,
    add_mul, hQK, add_zero]

lemma deriv_mul_projection_eq_zero {P : ℝ → Matrix ι ι ℂ} {U Q : Matrix ι ι ℂ}
    {x : ℝ} (hd : HasDerivAt P U x) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0) : U * Q = 0 := by
  have hh := hd.mul_const Q
  have he : HasDerivAt (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (U * Q) x :=
    hh.congr_of_eventuallyEq (hz.mono fun _ ht => ht.symm)
  exact he.unique (hasDerivAt_const x 0)

lemma projection_mul_deriv_eq_zero {P : ℝ → Matrix ι ι ℂ} {U Q : Matrix ι ι ℂ}
    {x : ℝ} (hd : HasDerivAt P U x) (hz : ∀ᶠ t in 𝓝 x, Q * P t = 0) : Q * U = 0 := by
  have hh := hd.const_mul Q
  have he : HasDerivAt (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (Q * U) x :=
    hh.congr_of_eventuallyEq (hz.mono fun _ ht => ht.symm)
  exact he.unique (hasDerivAt_const x 0)

omit [DecidableEq ι] in
lemma hermitian_mul_zero_flip {P Q : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (h : P * Q = 0) : Q * P = 0 := by
  simpa only [Matrix.conjTranspose_mul, hP.eq, hQ.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose h

lemma hessianPair_eq_PD {P : Matrix ι ι ℂ} (hP : P.PosDef)
    (K L : Matrix ι ι ℂ) : hessianPair P K L = hessianPairPD hP K L := by
  have hs := hessianPairPD_symm hP K L
  unfold hessianPair
  rw [← hessianPairPD_self hP, ← hessianPairPD_self hP]
  simp only [hessianPairPD, map_add, map_sub, hsReal_add_left, hsReal_add_right,
    hsReal_sub_left, hsReal_sub_right] at hs ⊢
  linarith

lemma hessianPair_add_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hKQ : K * Q = 0) (hQK : Q * K = 0) (hLQ : L * Q = 0) (hQL : Q * L = 0)
    (hPD : (P + Q).PosDef) : hessianPair (P + Q) K L = hessianPair P K L := by
  unfold hessianPair
  rw [hessianCost_add_projection hP hQ hQQ hPQ hQP
    (by simp [add_mul, hKQ, hLQ]) (by simp [mul_add, hQK, hQL]) hPD,
    hessianCost_add_projection hP hQ hQQ hPQ hQP
    (by simp [sub_mul, hKQ, hLQ]) (by simp [mul_sub, hQK, hQL]) hPD]

theorem energyGradient_supported_path_hasDerivAt {P K : ℝ → Matrix ι ι ℂ}
    {Q U V : Matrix ι ι ℂ} {x : ℝ}
    (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (hPD : (P x + Q).PosDef)
    (hn : ∀ᶠ t in 𝓝 x, (P t).PosSemidef) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0)
    (hK : ∀ᶠ t in 𝓝 x, (K t).IsHermitian) (hkz : ∀ᶠ t in 𝓝 x, K t * Q = 0)
    (hdP : HasDerivAt P U x) (hdK : HasDerivAt K V x) :
    HasDerivAt (fun t => energyGradient (P t) (K t))
      (hessianPair (P x) (K x) U + energyGradient (P x) V) x := by
  have hzl : ∀ᶠ t in 𝓝 x, Q * P t = 0 := by
    filter_upwards [hn, hz] with t ht htz
    exact hermitian_mul_zero_flip ht.isHermitian hQ.isHermitian htz
  have hkzl : ∀ᶠ t in 𝓝 x, Q * K t = 0 := by
    filter_upwards [hK, hkz] with t ht htz
    exact hermitian_mul_zero_flip ht hQ.isHermitian htz
  have hUQ := deriv_mul_projection_eq_zero hdP hz
  have hQU := projection_mul_deriv_eq_zero hdP hzl
  have hQV := projection_mul_deriv_eq_zero hdK hkzl
  have hnonneg : ∀ᶠ t in 𝓝 x, 0 ≤ P t + Q := hn.mono fun _ ht => (ht.add hQ).nonneg
  have hh := energyGradient_path_hasDerivAt hPD hnonneg hK.self_of_nhds
    (hdP.add_const Q) hdK
  rw [← hessianPair_eq_PD, hessianPair_add_projection hn.self_of_nhds hQ hQQ
    hz.self_of_nhds hzl.self_of_nhds hkz.self_of_nhds hkzl.self_of_nhds hUQ hQU hPD,
    energyGradient_add_projection hn.self_of_nhds hQ hQQ hz.self_of_nhds
      hzl.self_of_nhds hQV] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hn, hz, hzl, hkzl] with t ht hr hl hkl
  exact (energyGradient_add_projection ht hQ hQQ hr hl hkl).symm

end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.energyGradient_supported_path_hasDerivAt.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.energyGradient_supported_path_hasDerivAt.{uι}
