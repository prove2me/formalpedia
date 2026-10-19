-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.hasDerivAt_chordIntegral_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:07:44.11175+00:00
-- url     : https://prove2.me/submissions/93ed9520-aa14-42b9-b9f1-791b96332949

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean:L107-L125
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.hasDerivAt_chordIntegral_left. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_Faber_hasDerivAt_integral_compact

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

theorem hasDerivAt_chord_left (u v : ℂ) (t : ℝ) :
    HasDerivAt (fun z => chord z v t) ((1-t : ℝ) : ℂ) u := by
  simpa [chord] using ((hasDerivAt_id u).const_smul (1-t : ℝ)).add_const (t • v)

theorem hasDerivAt_chordIntegral_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => chordIntegral f w z v)
      (chordIntegral (deriv f) (fun t => w t * ((1-(t : ℝ) : ℝ) : ℂ)) u v) u := by
  have hc : ContinuousOn (fun p : ℂ × Parameter => chord p.1 v p.2) (s ×ˢ univ) := by
    unfold chord
    fun_prop
  have hm : MapsTo (fun p : ℂ × Parameter => chord p.1 v p.2) (s ×ˢ univ) s :=
    fun p hp => chord_mem hconv hp.1 hv p.2.property
  apply hasDerivAt_integral_compact volume hs
    ((hw.comp continuous_snd).continuousOn.mul (hf.continuousOn.comp hc hm))
    (((hw.comp continuous_snd).continuousOn.mul
      (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_subtype_val.comp continuous_snd))).continuousOn).mul
        (hf.deriv.continuousOn.comp hc hm)) ?_ hu
  intro z hz t
  have hd := ((hf _ (chord_mem hconv hz hv t.property)).differentiableAt.hasDerivAt.comp z
    (hasDerivAt_chord_left z v t)).const_mul (w t)
  simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using hd

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.hasDerivAt_chordIntegral_left := @_root_.OAI.DirectCrouzeix.Faber.hasDerivAt_chordIntegral_left
