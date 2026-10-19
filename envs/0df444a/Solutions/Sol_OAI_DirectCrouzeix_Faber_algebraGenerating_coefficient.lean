-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.algebraGenerating_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:33:12.498365+00:00
-- url     : https://prove2.me/submissions/0f7c0c70-e71b-4444-bd78-cf255c1ef697

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberCalculus.lean:L98-L141
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.algebraGenerating_coefficient. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus

-- ---- from OAI.Analysis.DirectCrouzeix.TaylorFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem taylorCoeff_congr {E : Type u_96} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} (h : f =ᶠ[𝓝 0] g) (k : ℕ) : taylorCoeff f k = taylorCoeff g k := by
  rw [taylorCoeff,taylorCoeff,h.iteratedDeriv_eq k]

theorem taylorCoeff_add {E : Type u_97} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    taylorCoeff (fun z => f z+g z) k = taylorCoeff f k+taylorCoeff g k := by
  simp only [taylorCoeff,iteratedDeriv_fun_add (n := k) hf.contDiffAt hg.contDiffAt,smul_add]

theorem taylorCoeff_sum {E : Type u_98} {ι : Type u_99} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (I : Finset ι) {f : ι → ℂ → E} (hf : ∀ i ∈ I, AnalyticAt ℂ (f i) 0) (k : ℕ) :
    taylorCoeff (fun z => ∑ i ∈ I, f i z) k = ∑ i ∈ I, taylorCoeff (f i) k := by
  simp only [taylorCoeff, iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt),Finset.smul_sum]

theorem taylorCoeff_smul_const {E : Type u_100} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (v : E) (k : ℕ) :
    taylorCoeff (fun z => f z • v) k = taylorCoeff f k • v := by
  rw [taylorCoeff,iteratedDeriv_smul_const hf.contDiffAt,taylorCoeff,smul_smul,smul_eq_mul]

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberPolynomials ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem analyticAt_localL {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localL c g) 0 := by
  apply (analyticAt_const.add (analyticAt_id.mul hg)).inv
  simpa using hc

theorem analyticAt_localW {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localW c g) 0 := analyticAt_id.mul (analyticAt_localL hc hg)

theorem analyticAt_localN {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localN c g) 0 :=
  (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).mul (analyticAt_localL hc hg)

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberCalculus ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_129 u_130

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

theorem analyticAt_ringInverse {x : 𝔄} (hx : IsUnit x) :
    AnalyticAt ℂ Ring.inverse x := by
  rcases hx with ⟨u,rfl⟩
  exact analyticAt_inverse u

theorem ringInverse_smul {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    [CompleteSpace 𝔄] {c : ℂ} (hc : c ≠ 0) (x : 𝔄) :
    Ring.inverse (c • x) = c⁻¹ • Ring.inverse x := by
  have hu : IsUnit (algebraMap ℂ 𝔄 c) := (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ 𝔄)
  have hi : Ring.inverse (algebraMap ℂ 𝔄 c) = algebraMap ℂ 𝔄 c⁻¹ := by
    have hm : algebraMap ℂ 𝔄 c * algebraMap ℂ 𝔄 c⁻¹ = 1 := by
      rw [← map_mul,mul_inv_cancel₀ hc,map_one]
    calc
      Ring.inverse (algebraMap ℂ 𝔄 c) = Ring.inverse (algebraMap ℂ 𝔄 c) *
          (algebraMap ℂ 𝔄 c * algebraMap ℂ 𝔄 c⁻¹) := by rw [hm,mul_one]
      _ = algebraMap ℂ 𝔄 c⁻¹ := by rw [← mul_assoc,Ring.inverse_mul_cancel _ hu,one_mul]
  rw [Algebra.smul_def,Ring.inverse_mul (Or.inl hu),hi,Algebra.smul_def,Algebra.commutes]

theorem ringInverse_geometric {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    [CompleteSpace 𝔄] (x : 𝔄) (hx : IsUnit (1-x)) (k : ℕ) :
    Ring.inverse (1-x) = (∑ j ∈ Finset.range (k+1),x^j) + x^(k+1)*Ring.inverse (1-x) := by
  have he := congrArg (fun y : 𝔄 => y * Ring.inverse (1-x)) (geom_sum_mul_neg x (k+1))
  rw [mul_assoc,Ring.mul_inverse_cancel _ hx,mul_one,sub_mul,one_mul] at he
  exact (eq_add_of_sub_eq he.symm)

theorem taylorCoeff_pow_smul_zero {E : Type u_130} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : AnalyticAt ℂ f 0) {j k : ℕ} (hjk : k < j) :
    taylorCoeff (fun u => u^j • f u) k = 0 := by
  have he := iteratedDerivWithin_smul (𝕜 := ℂ) (𝔸 := ℂ) (F := E) (n := k)
    (x := 0) (s := univ) (f := fun u : ℂ => u^j) (g := f)
    (mem_univ _) uniqueDiffOn_univ (by fun_prop) hf.contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at he
  change (k.factorial : ℂ)⁻¹ • iteratedDeriv k ((fun u : ℂ => u^j) • f) 0 = 0
  rw [he]
  have hz : (∑ i ∈ Finset.range (k+1), k.choose i •
      iteratedDeriv i (fun u : ℂ => u^j) 0 • iteratedDeriv (k-i) f 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by have := Finset.mem_range.mp hi; omega
    simp only [iteratedDeriv_fun_pow_zero,ite_eq_right hij,Nat.cast_zero,smul_zero,zero_smul]
  rw [hz,smul_zero]

theorem algebraGenerating_local {c : ℂ} {g : ℂ → ℂ} (A : 𝔄) {u : ℂ}
    (h : c+u*g u ≠ 0) :
    algebraGenerating c g A u = localN c g u • Ring.inverse (1-localW c g u • A) := by
  have he : algebraDenominator c g A u = (c+u*g u) • (1-localW c g u • A) := by
    simp only [algebraDenominator,smul_sub,smul_smul,localW,localL]
    congr 1
    congr 1
    field_simp
  rw [algebraGenerating,he,ringInverse_smul h,smul_smul]
  rfl

theorem algebraGenerating_coefficient {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (A : 𝔄) (k : ℕ) :
    taylorCoeff (algebraGenerating c g A) k = Polynomial.aeval A (faberBasis c g k) := by
  classical
  let L := localL c g
  let W := localW c g
  let N := localN c g
  let V := fun u => Ring.inverse (1-W u • A)
  have hL : AnalyticAt ℂ L 0 := analyticAt_localL hc hg
  have hW : AnalyticAt ℂ W 0 := analyticAt_localW hc hg
  have hN : AnalyticAt ℂ N 0 := analyticAt_localN hc hg
  have hd : AnalyticAt ℂ (fun u => (1:𝔄)-W u • A) 0 :=
    analyticAt_const.sub (hW.smul analyticAt_const)
  have hunit : IsUnit ((1:𝔄)-W 0 • A) := by simp [W]
  have hV : AnalyticAt ℂ V 0 := (analyticAt_ringInverse hunit).comp (f := fun u => (1:𝔄)-W u • A) hd
  have hlocal : ∀ᶠ u in 𝓝 0, c+u*g u ≠ 0 :=
    (analyticAt_const.add (analyticAt_id.mul hg)).continuousAt.eventually_ne (by simpa using hc)
  have hu : ∀ᶠ u in 𝓝 0, IsUnit ((1:𝔄)-W u • A) :=
    hd.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit)
  let T := fun u => (N u*L u^(k+1)) • (A^(k+1)*V u)
  have hT : AnalyticAt ℂ T 0 := (hN.mul (hL.pow (k+1))).smul (analyticAt_const.mul hV)
  have hs : AnalyticAt ℂ (fun u => ∑ j ∈ Finset.range (k+1), (N u*W u^j) • A^j) 0 :=
    Finset.analyticAt_fun_sum _ (fun j _ => (hN.mul (hW.pow j)).smul analyticAt_const)
  have he : algebraGenerating c g A =ᶠ[𝓝 0]
      (fun u => (∑ j ∈ Finset.range (k+1), (N u*W u^j) • A^j) + u^(k+1) • T u) := by
    filter_upwards [hlocal,hu] with u hlu huu
    rw [algebraGenerating_local A hlu,ringInverse_geometric (W u • A) huu k]
    simp only [smul_add,Finset.smul_sum,smul_pow,smul_smul,smul_mul_assoc]
    congr 1
    change (N u * W u^(k+1)) • (A^(k+1)*V u) =
      u^(k+1) • ((N u*L u^(k+1)) • (A^(k+1)*V u))
    rw [smul_smul]
    congr 1
    change N u * (u*L u)^(k+1) = _
    rw [mul_pow]
    ring
  have htail : AnalyticAt ℂ (fun u => u^(k+1) • T u) 0 := (analyticAt_id.pow (k+1)).smul hT
  rw [taylorCoeff_congr he k,taylorCoeff_add hs htail,
    taylorCoeff_pow_smul_zero hT (by omega : k < k+1),add_zero,taylorCoeff_sum]
  · simp only [faberBasis,map_sum,Polynomial.aeval_monomial,← Algebra.smul_def]
    apply Finset.sum_congr rfl
    intro j hj
    exact taylorCoeff_smul_const (hN.mul (hW.pow j)) (A^j) k
  · exact fun j _ => (hN.mul (hW.pow j)).smul analyticAt_const

end BanachAlgebra

end DirectCrouzeix.Faber

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

end DirectCrouzeix

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.algebraGenerating_coefficient := @_root_.OAI.DirectCrouzeix.Faber.algebraGenerating_coefficient
