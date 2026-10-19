-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.chordIntegral_deriv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:09:53.579908+00:00
-- url     : https://prove2.me/submissions/9e6617c0-67d4-4744-8b73-259c35ddf7b3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean:L162-L177
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.chordIntegral_deriv_mul. The node keeps its source
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

-- ---- from OAI.Analysis.DirectCrouzeix.CompactIntegrals ----
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem chord_mem {s : Set ℂ} (hs : Convex ℝ s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : chord u v t ∈ s :=
  hs hu hv (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)

theorem chordIntegral_one_eq_interval (f : ℂ → ℂ) (u v : ℂ) :
    chordIntegral f (fun _ => 1) u v = ∫ t in (0:ℝ)..1, f (chord u v t) := by
  simp only [chordIntegral, one_mul]
  rw [show (∫ t : Parameter, f (chord u v t)) = ∫ t in Icc (0:ℝ) 1, f (chord u v t) from
      integral_subtype measurableSet_Icc (fun t : ℝ => f (chord u v t)),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem hasDerivAt_chord_time (u v : ℂ) (t : ℝ) :
    HasDerivAt (chord u v) (v-u) t := by
  have hi : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := t))
  have hd := ((hi.const_sub 1).mul_const u).add (hi.mul_const v)
  change HasDerivAt (fun y => chord u v y) (v-u) t
  simpa [chord, Complex.real_smul, sub_eq_add_neg, add_comm] using! hd

theorem chordIntegral_deriv_mul {s : Set ℂ} (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    chordIntegral (deriv f) (fun _ => 1) u v * (v-u) = f v - f u := by
  rw [chordIntegral_one_eq_interval, ← intervalIntegral.integral_mul_const]
  have hc : ContinuousOn (fun t : ℝ => chord u v t) (Icc 0 1) := by unfold chord; fun_prop
  have hm : MapsTo (fun t : ℝ => chord u v t) (Icc 0 1) s := fun t ht => chord_mem hconv hu hv ht
  have hi : IntervalIntegrable (fun t : ℝ => deriv f (chord u v t) * (v-u)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (hf.deriv.continuousOn.comp hc hm).mul_const _
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (f := fun t => f (chord u v t))
    (f' := fun t => deriv f (chord u v t) * (v-u)) (fun t ht => by
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      simpa only [smul_eq_mul, mul_comm, Function.comp_def] using
        ((hf _ (hm ht')).differentiableAt.hasDerivAt.scomp t (hasDerivAt_chord_time u v t))) hi
  simpa [chord] using ht

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.chordIntegral_deriv_mul := @_root_.OAI.DirectCrouzeix.Faber.chordIntegral_deriv_mul
