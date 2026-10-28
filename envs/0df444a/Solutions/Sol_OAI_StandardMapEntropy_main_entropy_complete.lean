-- Prove2me | solution 1 for OAI.StandardMapEntropy.main_entropy_complete
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:01:16.432203+00:00
-- url     : https://prove2.me/submissions/0bb5ef30-55e3-48ff-b173-3aa75ff77b98

import Mathlib
import Definitions.Def_StandardMapLyapunov
import Definitions.Def_OAIQ3St000
import Theorems.Thm_OAI_StandardMapEntropy_eventually_meanDeficit_small_q3

section
-- module Solutions.OAIQ3_Std.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

theorem measurePreserving_standardMap (k : ℝ) : MeasurePreserving (standardMap k) area area := by
  unfold area
  have hkick : MeasurePreserving
      (fun z : Torus => (z.1, z.2 + kick k z.1))
        ((volume : Measure Circle).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Circle)).skew_product
      (g := fun x y : Circle => y + kick k x) ?_ ?_
    · exact measurable_snd.add ((continuous_kick k).measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun x => map_add_right_eq_self volume (kick k x))
  convert (measurePreserving_add_prod (volume : Measure Circle) volume).comp hkick using 1
  funext z
  simp only [Function.comp_apply, standardMap, kick]
  congr 1
  abel

lemma recurrenceCoordinates_involutive : Function.Involutive recurrenceCoordinates := by
  intro z
  apply Prod.ext <;> simp [recurrenceCoordinates]

lemma standardMap_conjugacy (k : ℝ) (z : Torus) :
    recurrenceCoordinates (standardMap k z) =
      recurrenceMap k (recurrenceCoordinates z) := by
  apply Prod.ext <;> simp only [recurrenceCoordinates, recurrenceMap, standardMap, kick, two_smul]
  · abel
  · abel

lemma hasDerivAt_phi (k x : ℝ) : HasDerivAt (phi k) (potential k x) x := by
  have hs : HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * y))
      (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * Real.pi)).sin
  have hl : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  convert! hl.add (hs.const_mul k) using 1
  unfold potential
  ring

lemma potential_lipschitz (k x y : ℝ) (hk : 0 ≤ k) :
    |potential k y - potential k x| ≤ (2 * Real.pi * growthBase k) * |y - x| := by
  have hK : 0 ≤ 2 * Real.pi * k := by positivity
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hid : potential k y - potential k x =
      (2 * Real.pi * k) * (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)) := by
    unfold potential
    ring
  rw [hid, abs_mul, abs_of_nonneg hK]
  have hdiff : |2 * Real.pi * y - 2 * Real.pi * x| = (2 * Real.pi) * |y - x| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hπ]
  calc
    (2 * Real.pi * k) * |Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)| ≤
        (2 * Real.pi * k) * ((2 * Real.pi) * |y - x|) := by
      apply mul_le_mul_of_nonneg_left _ hK
      rw [← hdiff]
      exact Real.abs_cos_sub_cos_le _ _
    _ ≤ (2 * Real.pi * growthBase k) * |y - x| := by
      have h : 2 * Real.pi * k ≤ growthBase k := by unfold growthBase; linarith
      have h' := mul_le_mul_of_nonneg_right h (mul_nonneg hπ (abs_nonneg (y - x)))
      nlinarith only [h']

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_PlaneGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma abs_dot_le_norm_mul (z w : ℂ) : |dot z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have h0 := sq_nonneg (wedge z w)
  have hs : (dot z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma abs_wedge_le_norm_mul (z w : ℂ) : |wedge z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have hs : (wedge z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith [sq_nonneg (dot z w)]
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma wedge_add_left (z w a : ℂ) : wedge (z+w) a = wedge z a + wedge w a := by
  simp [wedge]; ring
lemma wedge_smul_left (t : ℝ) (z w : ℂ) : wedge (t • z) w = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_refl (z : ℂ) : wedge z z = 0 := by dsimp [wedge]; ring
lemma wedge_swap (z w : ℂ) : wedge z w = -wedge w z := by dsimp [wedge]; ring
lemma wedge_sine_triangle (a b c : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    |wedge a c| ≤ |wedge a b|+|wedge b c| := by
  have he : wedge a c = dot b a * wedge b c + wedge b a * wedge (quarterTurn b) c := by
    conv_lhs => rw [unit_expansion b a hb]
    rw [wedge_add_left, wedge_smul_left, wedge_smul_left]
  rw [he]
  calc
    _ ≤ |dot b a| * |wedge b c|+|wedge b a| * |wedge (quarterTurn b) c| := by
      simpa only [abs_mul] using abs_add_le (dot b a * wedge b c) (wedge b a * wedge (quarterTurn b) c)
    _ ≤ |wedge b c|+|wedge b a| := by
      have h1 : |dot b a|≤1 := by simpa [ha,hb] using abs_dot_le_norm_mul b a
      have h2 : |wedge (quarterTurn b) c|≤1 := by simpa [norm_quarterTurn,hb,hc] using abs_wedge_le_norm_mul (quarterTurn b) c
      nlinarith [abs_nonneg (wedge b c), abs_nonneg (wedge b a)]
    _ = _ := by rw [wedge_swap b a, abs_neg]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_PlaneTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma dot_quarterTurn_right (a z : ℂ) : dot a (quarterTurn z) = -wedge a z := by
  simp [dot,wedge,quarterTurn]; ring
lemma expanded_projection_bound {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A‖*|dot a z| ≤ ‖A z‖ := by
  have hs := h.norm_map_sq a ha hA z
  have hnon := mul_nonneg (sq_nonneg (wedge a z)) (sq_nonneg (‖A‖⁻¹))
  have hsq : (‖A‖*|dot a z|)^2≤‖A z‖^2 := by nlinarith [sq_abs (dot a z)]
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg A) (abs_nonneg _)) (norm_nonneg _)).mp hsq
lemma two_singular_upper {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A z‖ ≤ ‖A‖*|dot a z| + ‖A‖⁻¹*|wedge a z| := by
  have hd := orthogonal_image_of_max A a ha hA
  have hs := h.norm_map_sq a ha hA (quarterTurn a)
  rw [dot_quarterTurn,wedge_quarterTurn,ha] at hs
  have hb : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  conv_lhs => rw [unit_expansion a z ha]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(dot a z : ℝ) • A a‖+‖(wedge a z : ℝ) • A (quarterTurn a)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hA,hb]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_LiftDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma phi_lipschitz (k : ℝ) (hk : 0 ≤ k) :
    LipschitzWith (⟨growthBase k-1,by have := growthBase_ge_four k hk; linarith⟩ : NNReal) (phi k) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_phi k x).differentiableAt
  · intro x
    change |deriv (phi k) x| ≤ growthBase k-1
    rw [(hasDerivAt_phi k x).deriv]
    linarith [potential_bound k x hk]
lemma liftStep_lipschitz (k : ℝ) (hk : 0 ≤ k) :
    LipschitzWith (⟨growthBase k,by have := growthBase_ge_four k hk; linarith⟩ : NNReal) (liftStep k) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Prod.dist_eq, liftStep_apply,liftStep_apply]
  change max (dist (phi k z.1-z.2) (phi k w.1-w.2)) (dist z.1 w.1) ≤ _
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have h1 : dist z.1 w.1 ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist z.2 w.2 ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_right _ _
  refine max_le ?_ ?_
  · calc
      _ ≤ dist (phi k z.1) (phi k w.1)+dist z.2 w.2 := dist_sub_sub_le _ _ _ _
      _ ≤ (growthBase k-1)*dist z.1 w.1+dist z.2 w.2 := add_le_add ((phi_lipschitz k hk).dist_le_mul _ _) le_rfl
      _ ≤ (growthBase k-1)*dist z w+dist z w := add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith)) h2
      _ = _ := by change _ = growthBase k*dist z w; ring
  · exact h1.trans (le_mul_of_one_le_left (dist_nonneg) hM)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma affineParameter_mem_interval (a b : ℝ) (hab : a≤b)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : affineParameter a b t∈Icc a b := by
  dsimp [affineParameter]
  rcases ht with ⟨ht0,ht1⟩
  constructor <;> nlinarith
lemma hasDerivAt_affineParameter (a b t : ℝ) :
    HasDerivAt (affineParameter a b) (b-a) t := by
  convert! ((hasDerivAt_id t).const_mul (b-a)).const_add a using 1 ; simp
lemma affineParameter_range (a b : ℝ) (hab : a≤b) :
    affineParameter a b '' Icc (0:ℝ) 1=Icc a b := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩; exact affineParameter_mem_interval a b hab ht
  · intro hx
    by_cases h : a=b
    · subst b; have : x=a := le_antisymm hx.2 hx.1
      subst x; exact ⟨0,by norm_num,by simp [affineParameter]⟩
    · have hba : 0<b-a := sub_pos.mpr (lt_of_le_of_ne hab h)
      refine ⟨(x-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hx.1) hba.le,?_⟩,?_⟩
      · exact (div_le_one hba).mpr (by linarith [hx.2])
      · dsimp [affineParameter]; field_simp; ring
lemma curve_displacement (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (B : ℝ) (hB : ∀t∈Icc (0:ℝ) 1, ‖v t‖≤B)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    ‖g b-g a‖≤B*|b-a| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht=>(hv t).hasDerivWithinAt) hB ha hb
lemma curve_linear_error (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε : ℝ) (hε : ∀t∈Icc (0:ℝ) 1, ‖v t-v 0‖≤ε)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    ‖g b-g a-(b-a) • v 0‖≤ε*|b-a| := by
  have h := curve_displacement (fun t=>g t-t • v 0) (fun t=>v t-v 0)
    (fun t=>by
      convert! (hv t).sub ((hasDerivAt_id t).smul_const (v 0)) using 1 ; simp) ε hε ha hb
  convert h using 1 ; congr 1 ; simp only [sub_smul] ; abel
lemma curve_chord_lower (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε : ℝ) (hε : ∀t∈Icc (0:ℝ) 1, ‖v t-v 0‖≤ε)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    (‖v 0‖-ε)*|b-a|≤‖g b-g a‖ := by
  have he := curve_linear_error g v hv ε hε ha hb
  have hn := norm_sub_le (g b-g a) (g b-g a-(b-a) • v 0)
  rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs] at hn
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
namespace CurveInterval
lemma length_le_one (I : CurveInterval) : I.length≤1 := by dsimp [length]; linarith [I.left_nonneg,I.right_le]
lemma parameter_range (I : CurveInterval) : I.parameter '' Icc (0:ℝ) 1=Icc I.left I.right :=
  affineParameter_range _ _ I.ordered
lemma parameter_abs_sub (I : CurveInterval) (s t : ℝ) :
    |I.parameter s-I.parameter t|=I.length*|s-t| := by
  rw [I.parameter_sub,abs_mul,abs_of_nonneg I.length_nonneg]
lemma velocity_norm (I : CurveInterval) (v : ℝ → CurvePlane) (t : ℝ) :
    ‖I.velocity v t‖=I.length*‖v (I.parameter t)‖ := by
  rw [velocity,norm_smul,Real.norm_eq_abs,abs_of_nonneg I.length_nonneg]
lemma velocity_continuous (I : CurveInterval) {v : ℝ → CurvePlane} (hv : Continuous v) :
    Continuous (I.velocity v) := by
  have hp : Continuous I.parameter := by unfold parameter affineParameter; fun_prop
  exact (continuous_const : Continuous (fun _ : ℝ => I.length)).smul (hv.comp hp)
lemma hasDeriv (I : CurveInterval) {g v : ℝ → CurvePlane} (h : ∀t,HasDerivAt g (v t) t) (t : ℝ) :
    HasDerivAt (g ∘ I.parameter) (I.velocity v t) t := by
  convert! (h (I.parameter t)).scomp t (hasDerivAt_affineParameter I.left I.right t) using 1
lemma variation (I : CurveInterval) {v : ℝ → CurvePlane} {B : ℝ}
    (hB : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,‖v s-v t‖≤B*|s-t|)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    ‖I.velocity v s-I.velocity v t‖≤(I.length^2*B)*|s-t| := by
  rw [velocity,velocity,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg I.length_nonneg]
  calc
    _ ≤ I.length*(B*|I.parameter s-I.parameter t|) :=
      mul_le_mul_of_nonneg_left (hB _ (I.parameter_mem hs) _ (I.parameter_mem ht)) I.length_nonneg
    _ = _ := by rw [I.parameter_abs_sub]; ring
end CurveInterval

lemma curve_compact_hull (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε δ : ℝ) (hε : 0≤ε) (hδ : 3*δ≤ε)
    (hvar : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,‖v s-v t‖≤ε*|s-t|)
    (hfast : 2*ε<‖v 0‖) (S : Set ℝ) (hS : IsCompact S)
    (hne : S.Nonempty) (hsub : S⊆Icc (0:ℝ) 1)
    (hdiam : ∀s∈S,∀t∈S,‖g s-g t‖≤δ) :
    ∃I:CurveInterval, S⊆Icc I.left I.right ∧
      ∀t∈Icc (0:ℝ) 1,‖I.velocity v t‖≤ε := by
  obtain ⟨a,ha,hmin⟩:=hS.exists_isLeast hne
  obtain ⟨b,hb,hmax⟩:=hS.exists_isGreatest hne
  have hab:a≤b := hmin hb
  let I:CurveInterval:=⟨a,b,(hsub ha).1,hab,(hsub hb).2⟩
  have hclose:∀t∈Icc (0:ℝ) 1,‖v t-v 0‖≤ε := by
    intro t ht
    have h:=hvar t ht 0 (by norm_num)
    simp only [sub_zero,abs_of_nonneg ht.1] at h
    exact h.trans (mul_le_of_le_one_right hε ht.2)
  have hchord: (‖v 0‖-ε)*(b-a)≤δ := by
    have h:=curve_chord_lower g v hv ε hclose (hsub ha) (hsub hb)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    exact h.trans (hdiam b hb a ha)
  refine ⟨I,fun t ht=>⟨hmin ht,hmax ht⟩,?_⟩
  intro t ht
  have hs:‖v (I.parameter t)‖≤‖v 0‖+ε := by
    have h:=norm_sub_le (v (I.parameter t)-v 0) (-v 0)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at h
    have hc:=hclose _ (I.parameter_mem ht)
    linarith
  rw [I.velocity_norm]
  calc
    _ ≤ (b-a)*(‖v 0‖+ε) := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hab)
    _ ≤ 3*δ := by
      have h:=mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hfast.le)
      nlinarith
    _ ≤ ε := hδ
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
lemma subdivisionInterval_length (N : ℕ) (hN : 0<N) (i : Fin N) :
    (subdivisionInterval N hN i).length=1/(N:ℝ) := by
  dsimp [CurveInterval.length,subdivisionInterval]; ring
lemma subdivisionInterval_cover (N : ℕ) (hN : 0<N) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    ∃i:Fin N,x∈Icc (subdivisionInterval N hN i).left (subdivisionInterval N hN i).right := by
  have hNr:0<(N:ℝ) := by exact_mod_cast hN
  let q:=⌊(N:ℝ)*x⌋₊
  have hq0:(q:ℝ)≤N*x := Nat.floor_le (mul_nonneg hNr.le hx.1)
  have hq1:(N:ℝ)*x<(q:ℝ)+1 := Nat.lt_floor_add_one _
  by_cases hq:q<N
  · refine ⟨⟨q,hq⟩,?_⟩
    change (q:ℝ)/N≤x ∧ x≤((q:ℝ)+1)/N
    exact ⟨(div_le_iff₀ hNr).mpr (by nlinarith), (le_div_iff₀ hNr).mpr (by nlinarith)⟩
  · have hq2:(N:ℝ)≤q := by exact_mod_cast (show N≤q by omega)
    have hx1:x=1 := by nlinarith [hx.2]
    subst x
    refine ⟨⟨N-1,by omega⟩,?_⟩
    have he:((N-1:ℕ):ℝ)+1=N := by exact_mod_cast (show N-1+1=N by omega)
    change ((N-1:ℕ):ℝ)/N≤1 ∧ 1≤(((N-1:ℕ):ℝ)+1)/N
    constructor
    · apply (div_le_one hNr).mpr; linarith
    · rw [he,div_self hNr.ne']
lemma pointCurveInterval_speed (ε : ℝ) (hε : 0≤ε) (v : ℝ → CurvePlane) (t : ℝ) :
    ‖pointCurveInterval.velocity v t‖≤ε := by simpa [CurveInterval.velocity,CurveInterval.length,pointCurveInterval] using hε
lemma restricted_controlled_curve (ε : ℝ) (hε : 0≤ε) (g v : ℝ → CurvePlane)
    (hv : ∀t,HasDerivAt g (v t) t) (hc : Continuous v)
    (hvar : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,‖v s-v t‖≤ε*|s-t|)
    (I : CurveInterval) (hs : ∀t∈Icc (0:ℝ) 1,‖I.velocity v t‖≤ε) :
    ∃C:ControlledCurve ε,C.map=g ∘ I.parameter ∧ C.velocity=I.velocity v := by
  refine ⟨⟨g ∘ I.parameter,I.velocity v,I.hasDeriv hv,I.velocity_continuous hc,hs,?_⟩,rfl,rfl⟩
  intro s hs t ht
  apply (I.variation hvar hs ht).trans
  have hsq:I.length^2≤1 := by nlinarith [I.length_nonneg,I.length_le_one]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)

lemma curve_small_target_cover (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε δ : ℝ) (hε : 0≤ε) (hδ : 3*δ≤ε)
    (hvar : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,‖v s-v t‖≤ε*|s-t|)
    (S : Set ℝ) (hS : IsCompact S) (hsub : S⊆Icc (0:ℝ) 1)
    (hdiam : ∀s∈S,∀t∈S,‖g s-g t‖≤δ) :
    ∃I:Fin 4→CurveInterval,
      (∀s∈S,∃i,s∈Icc (I i).left (I i).right) ∧
      (∀i,∀t∈Icc (0:ℝ) 1,‖(I i).velocity v t‖≤ε) := by
  by_cases hne:S.Nonempty
  · by_cases hf:2*ε<‖v 0‖
    · obtain ⟨J,hJ,hs⟩:=curve_compact_hull g v hv ε δ hε hδ hvar hf S hS hne hsub hdiam
      exact ⟨fun _=>J,fun s hs=>⟨0,hJ hs⟩,fun _=>hs⟩
    · refine ⟨subdivisionInterval 4 (by norm_num),fun s hs=>subdivisionInterval_cover 4 (by norm_num) (hsub hs),?_⟩
      intro i t ht
      rw [CurveInterval.velocity_norm,subdivisionInterval_length]
      have hp: (subdivisionInterval 4 (by norm_num) i).parameter t∈Icc (0:ℝ) 1 := CurveInterval.parameter_mem _ ht
      have hv0:=hvar _ hp 0 (by norm_num)
      simp only [sub_zero,abs_of_nonneg hp.1] at hv0
      have hn:=norm_sub_le_norm_sub_add_norm_sub (v ((subdivisionInterval 4 (by norm_num) i).parameter t)) (v 0) 0
      simp only [sub_zero] at hn
      have he:=mul_le_of_le_one_right hε hp.2
      norm_num at *
      linarith
  · exact ⟨fun _=>pointCurveInterval,fun s hs=>(hne ⟨s,hs⟩).elim,
      fun _ t _=>pointCurveInterval_speed ε hε v t⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveCompose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
namespace CurveInterval
lemma comp_parameter (I J : CurveInterval) (t : ℝ) :
    (I.comp J).parameter t=I.parameter (J.parameter t) := by
  dsimp [parameter,comp,affineParameter]; ring
lemma comp_mem (I J : CurveInterval) {t : ℝ} (ht : t∈Icc J.left J.right) :
    I.parameter t∈Icc (I.comp J).left (I.comp J).right := by
  change I.parameter J.left≤I.parameter t ∧ I.parameter t≤I.parameter J.right
  constructor
  · apply sub_nonneg.mp
    rw [I.parameter_sub]
    exact mul_nonneg I.length_nonneg (sub_nonneg.mpr ht.1)
  · apply sub_nonneg.mp
    rw [I.parameter_sub]
    exact mul_nonneg I.length_nonneg (sub_nonneg.mpr ht.2)
end CurveInterval
lemma curve_wrap_integer (x y c δ : ℝ) (hxy : |x-y|≤1) (hδ : δ≤1)
    (m : ℤ) (hm : |y-(c+m)|≤δ) :
    ∃i:Fin 7,m=⌊x-c⌋+(i:ℤ)-3 := by
  have h1:=Int.floor_le (x-c)
  have h2:=Int.lt_floor_add_one (x-c)
  have hp:|x-c-(m:ℝ)|≤2 := by
    have h:=abs_add_le (x-y) (y-(c+m))
    have he:(x-y)+(y-(c+m))=x-c-m := by ring
    rw [he] at h
    linarith
  have hlo:⌊x-c⌋-3≤ m := by
    have h:((⌊x-c⌋:ℤ):ℝ)-3≤ m := by linarith [(abs_le.mp hp).1,(abs_le.mp hp).2]
    exact_mod_cast h
  have hhi:m≤⌊x-c⌋+3 := by
    have h:(m:ℝ)≤⌊x-c⌋+3 := by linarith [(abs_le.mp hp).1,(abs_le.mp hp).2]
    exact_mod_cast h
  let q:ℤ:=m-⌊x-c⌋+3
  have hq0:0≤q := by dsimp [q]; omega
  have hq7:q<7 := by dsimp [q]; omega
  refine ⟨⟨q.toNat,by omega⟩,?_⟩
  change m=⌊x-c⌋+(q.toNat:ℤ)-3
  rw [Int.toNat_of_nonneg hq0]
  dsimp [q]; ring
lemma wrappedBox_finite_cover (δ : ℝ) (hδ : δ≤1) (c x y : CurvePlane)
    (hxy : ‖x-y‖≤1) (hy : wrappedBox δ c y) :
    ∃i:Fin 7×Fin 7,‖y-wrappedCurveCenter c x i‖≤δ := by
  obtain ⟨m,hm⟩:=hy
  obtain ⟨i,hi⟩:=curve_wrap_integer x.1 y.1 c.1 δ
    ((norm_fst_le (x-y)).trans hxy) hδ m.1 ((norm_fst_le _).trans hm)
  obtain ⟨j,hj⟩:=curve_wrap_integer x.2 y.2 c.2 δ
    ((norm_snd_le (x-y)).trans hxy) hδ m.2 ((norm_snd_le _).trans hm)
  refine ⟨(i,j),?_⟩
  simpa only [wrappedCurveCenter,← hi,← hj] using hm
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma pairTransfer_bound (k : ℝ) (hk : 0≤k) (x : ℝ) (v : CurvePlane) :
    ‖pairTransfer (potential k x) v‖≤growthBase k*‖v‖ := by
  rw [Prod.norm_def]
  have hM:=growthBase_ge_four k hk
  have h1:=norm_fst_le v
  have h2:=norm_snd_le v
  change |v.1|≤‖v‖ at h1
  change |v.2|≤‖v‖ at h2
  change max |potential k x*v.1-v.2| |v.1|≤_
  refine max_le ?_ (h1.trans ?_)
  · calc
      _ ≤ |potential k x| *|v.1|+|v.2| := by simpa only [abs_mul] using abs_sub (potential k x*v.1) v.2
      _ ≤ |potential k x| *‖v‖+‖v‖ := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
      _ ≤ _ := by nlinarith [potential_bound k x hk,norm_nonneg v]
  · exact le_mul_of_one_le_left (norm_nonneg _) (by linarith)
lemma pairTransfer_sub (a : ℝ) (v w : CurvePlane) :
    pairTransfer a (v-w)=pairTransfer a v-pairTransfer a w := by ext <;> simp [pairTransfer] ; ring
lemma pairTransfer_parameter (a b : ℝ) (v : CurvePlane) :
    ‖pairTransfer a v-pairTransfer b v‖≤|a-b| *‖v‖ := by
  have he:pairTransfer a v-pairTransfer b v=((a-b)*v.1,0) := by ext <;> simp [pairTransfer] ; ring
  rw [he,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,abs_zero,max_eq_left (abs_nonneg _),abs_mul]
  exact mul_le_mul_of_nonneg_left (norm_fst_le v) (abs_nonneg _)
lemma liftCurve_hasDeriv (k : ℝ) (g v : ℝ → CurvePlane)
    (hv : ∀t,HasDerivAt g (v t) t) (t : ℝ) :
    HasDerivAt ((liftStep k) ∘ g) (liftCurveVelocity k g v t) t := by
  have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hv t)
  have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hv t)
  convert! (((hasDerivAt_phi k (g t).1).comp t h1).sub h2).prodMk h1 using 1
lemma liftCurve_velocity_continuous (k : ℝ) (g v : ℝ → CurvePlane)
    (hg : Continuous g) (hv : Continuous v) : Continuous (liftCurveVelocity k g v) := by
  unfold liftCurveVelocity pairTransfer potential
  fun_prop
lemma liftCurve_variation (k ε : ℝ) (hk : 0≤k) (hε : 0≤ε) (hsmall : 2*Real.pi*ε≤1)
    (g : ControlledCurve ε) {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    ‖liftCurveVelocity k g.map g.velocity s-liftCurveVelocity k g.map g.velocity t‖≤
      2*growthBase k*ε*|s-t| := by
  have hM:0≤growthBase k := (growthBase_ge_four k hk).trans' (by norm_num)
  have hd:‖g.map s-g.map t‖≤ε*|s-t| := curve_displacement _ _ g.hasDeriv _ g.speed ht hs
  have hp:|potential k (g.map s).1-potential k (g.map t).1|≤
      2*Real.pi*growthBase k*‖g.map s-g.map t‖ := by
    exact (potential_lipschitz k _ _ hk).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le (g.map s-g.map t)) (by positivity))
  calc
    _ ≤ ‖pairTransfer (potential k (g.map s).1) (g.velocity s)-
      pairTransfer (potential k (g.map s).1) (g.velocity t)‖+
      ‖pairTransfer (potential k (g.map s).1) (g.velocity t)-
      pairTransfer (potential k (g.map t).1) (g.velocity t)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ growthBase k*‖g.velocity s-g.velocity t‖+
      |potential k (g.map s).1-potential k (g.map t).1| *‖g.velocity t‖ := by
      rw [← pairTransfer_sub]
      exact add_le_add (pairTransfer_bound k hk _ _) (pairTransfer_parameter _ _ _)
    _ ≤ growthBase k*(ε*|s-t|)+(2*Real.pi*growthBase k*(ε*|s-t|))*ε := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (g.variation s hs t ht) hM
      · exact mul_le_mul (hp.trans (mul_le_mul_of_nonneg_left hd (by positivity)))
          (g.speed t ht) (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      have h:=mul_le_mul_of_nonneg_right hsmall
        (show 0≤growthBase k*ε*|s-t| by positivity)
      nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveOneStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma curveStepBranch_card (N : ℕ) : Fintype.card (CurveStepBranch N)=196*N := by
  simp [CurveStepBranch,Fintype.card_prod]; omega
lemma liftCurve_total_displacement (k ε : ℝ) (hk : 0≤k) (hε : 0≤ε)
    (hsmall : growthBase k*ε≤1) (g : ControlledCurve ε)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    ‖liftStep k (g.map s)-liftStep k (g.map t)‖≤1 := by
  have h:= (liftStep_lipschitz k hk).dist_le_mul (g.map s) (g.map t)
  simp only [dist_eq_norm] at h
  have hd:=curve_displacement _ _ g.hasDeriv ε g.speed ht hs
  have hab:|s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  have hM:0≤growthBase k := by have :=growthBase_ge_four k hk; linarith
  exact h.trans ((mul_le_mul_of_nonneg_left (hd.trans (mul_le_of_le_one_right hε hab)) hM).trans hsmall)

lemma curve_one_step_cover (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (_hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g : ControlledCurve ε) (c : CurvePlane) :
    ∃(I : CurveStepBranch N → CurveInterval) (C : CurveStepBranch N → ControlledCurve ε),
      (∀s∈Icc (0:ℝ) 1,wrappedBox δ c (liftStep k (g.map s))  →
        ∃i,s∈Icc (I i).left (I i).right) ∧
      ∀i,(C i).map=(liftStep k) ∘ g.map ∘ (I i).parameter := by
  let f:ℝ  →  CurvePlane:=(liftStep k) ∘ g.map
  let v:=liftCurveVelocity k g.map g.velocity
  have hv:∀t,HasDerivAt f (v t) t := liftCurve_hasDeriv k _ _ g.hasDeriv
  have hc:Continuous f := continuous_iff_continuousAt.mpr fun t=>(hv t).continuousAt
  have hcv:Continuous v := liftCurve_velocity_continuous k _ _
    (continuous_iff_continuousAt.mpr fun t=>(g.hasDeriv t).continuousAt) g.continuous_velocity
  let J:=subdivisionInterval N hN
  have hvar:∀i:Fin N,∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,
      ‖(J i).velocity v s-(J i).velocity v t‖≤ε*|s-t| := by
    intro i s hs t ht
    have h:=(J i).variation (fun s hs t ht=>liftCurve_variation k ε hk hε hε1 g hs ht) hs ht
    rw [show (J i).length=1/(N:ℝ) from subdivisionInterval_length N hN i] at h
    apply h.trans
    have hNp:0<(N:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hN)
    have hb:(1/(N:ℝ))^2*(2*growthBase k*ε)≤ε := by
      rw [one_div_pow,mul_comm,one_div,← div_eq_mul_inv,div_le_iff₀ hNp]
      nlinarith
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  let center (i : Fin N) (j : Fin 7×Fin 7) := wrappedCurveCenter c (f ((J i).parameter 0)) j
  let S (i : Fin N) (j : Fin 7×Fin 7) : Set ℝ:=
    Icc 0 1 ∩ {t | ‖f ((J i).parameter t)-center i j‖≤δ}
  have hex:∀i:Fin N,∀j:Fin 7×Fin 7,∃H:Fin 4 → CurveInterval,
      (∀s∈S i j,∃a,s∈Icc (H a).left (H a).right) ∧
      (∀a,∀t∈Icc (0:ℝ) 1,‖(H a).velocity ((J i).velocity v) t‖≤ε) := by
    intro i j
    apply curve_small_target_cover (f ∘ (J i).parameter) ((J i).velocity v)
      ((J i).hasDeriv hv) ε (2*δ) hε (by linarith) (hvar i) (S i j)
    · apply isCompact_Icc.inter_right
      apply isClosed_le _ continuous_const
      have hp:Continuous (J i).parameter := by unfold CurveInterval.parameter affineParameter; fun_prop
      exact ((hc.comp hp).sub continuous_const).norm
    · exact inter_subset_left
    · intro s hs t ht
      have h:=norm_sub_le_norm_sub_add_norm_sub (f ((J i).parameter s)) (center i j) (f ((J i).parameter t))
      rw [norm_sub_rev (center i j)] at h
      exact h.trans (add_le_add hs.2 ht.2 |>.trans_eq (by ring))
  choose H hcover hspeed using hex
  have hC:∀i:Fin N,∀j:Fin 7×Fin 7,∀a:Fin 4,∃C:ControlledCurve ε,
      C.map=(f ∘ (J i).parameter) ∘ (H i j a).parameter := by
    intro i j a
    obtain ⟨C,hC,_⟩:=restricted_controlled_curve ε hε (f ∘ (J i).parameter) ((J i).velocity v)
      ((J i).hasDeriv hv) ((J i).velocity_continuous hcv) (hvar i) (H i j a) (hspeed i j a)
    exact ⟨C,hC⟩
  choose C hC using hC
  refine ⟨fun b=>(J b.1).comp (H b.1 b.2.1 b.2.2),fun b=>C b.1 b.2.1 b.2.2,?_,?_⟩
  · intro s hs hwrap
    obtain ⟨i,hi⟩:=subdivisionInterval_cover N hN hs
    obtain ⟨t,ht,hts⟩:=(J i).parameter_range.superset hi
    have hdist:‖f ((J i).parameter 0)-f ((J i).parameter t)‖≤1 :=
      liftCurve_total_displacement k ε hk hε hε2 g ((J i).parameter_mem (by norm_num)) ((J i).parameter_mem ht)
    have hw:wrappedBox δ c (f ((J i).parameter t)) := by simpa only [hts,f,Function.comp_apply] using hwrap
    obtain ⟨j,hj⟩:=wrappedBox_finite_cover δ hδ1 c _ _ hdist hw
    obtain ⟨a,ha⟩:=hcover i j t ⟨ht,hj⟩
    refine ⟨(i,j,a),?_⟩
    rw [← hts]
    exact (J i).comp_mem (H i j a) ha
  · intro b
    rw [hC]
    funext t
    simp only [Function.comp_apply,CurveInterval.comp_parameter]
    rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveIterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
lemma curveTree_card (N n : ℕ) : Fintype.card (CurveTree N n)=(196*N)^n := by
  induction n with
  | zero => change Fintype.card Unit=_; simp
  | succ n ih =>
      change Fintype.card (CurveTree N n × CurveStepBranch N)=_
      rw [Fintype.card_prod,ih,curveStepBranch_card,pow_succ]
lemma fullCurveInterval_parameter : fullCurveInterval.parameter=id := by
  funext t; simp [fullCurveInterval,CurveInterval.parameter,affineParameter]
lemma curve_iterate_cover (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g : ControlledCurve ε) (c : ℕ → CurvePlane) (n : ℕ) :
    ∃(I : CurveTree N n → CurveInterval) (C : CurveTree N n → ControlledCurve ε),
      (∀s∈Icc (0:ℝ) 1,(∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (g.map s)))  →
        ∃i,s∈Icc (I i).left (I i).right) ∧
      ∀i,(C i).map=(liftStep k)^[n] ∘ g.map ∘ (I i).parameter := by
  induction n with
  | zero =>
      refine ⟨fun _=>fullCurveInterval,fun _=>g,fun s hs _=>⟨(),hs⟩,?_⟩
      intro i; simp only [Function.iterate_zero,fullCurveInterval_parameter,Function.comp_id,Function.id_comp]
  | succ n ih =>
      obtain ⟨I,C,hcover,hmap⟩:=ih
      have hex:∀i:CurveTree N n,∃(J : CurveStepBranch N → CurveInterval)
          (D : CurveStepBranch N → ControlledCurve ε),
          (∀s∈Icc (0:ℝ) 1,wrappedBox δ (c n) (liftStep k ((C i).map s))  →
            ∃j,s∈Icc (J j).left (J j).right) ∧
          ∀j,(D j).map=(liftStep k) ∘ (C i).map ∘ (J j).parameter :=
        fun i=>curve_one_step_cover k ε δ hk hε hδ0 hδ1 hδ hε1 hε2 N hN hN2 (C i) (c n)
      choose J D hcover' hmap' using hex
      refine ⟨fun b=>(I b.1).comp (J b.1 b.2),fun b=>D b.1 b.2,?_,?_⟩
      · intro s hs hc
        obtain ⟨i,hi⟩:=hcover s hs (fun j hj=>hc j (by omega))
        obtain ⟨t,ht,hts⟩:=(I i).parameter_range.superset hi
        have hh:wrappedBox δ (c n) (liftStep k ((C i).map t)) := by
          rw [hmap]
          simpa only [Function.comp_apply,hts,Function.iterate_succ_apply'] using hc n (by omega)
        obtain ⟨j,hj⟩:=hcover' i t ht hh
        refine ⟨(i,j),?_⟩
        rw [← hts]
        exact (I i).comp_mem (J i j) hj
      · intro b
        rw [hmap',hmap]
        funext t
        simp only [Function.comp_apply,CurveInterval.comp_parameter,Function.iterate_succ_apply']
lemma curveIter_hasDeriv (k : ℝ) (g v : ℝ → CurvePlane)
    (hv : ∀t,HasDerivAt g (v t) t) (n : ℕ) (t : ℝ) :
    HasDerivAt ((liftStep k)^[n] ∘ g) (curveIterVelocity k g v n t) t := by
  induction n generalizing t with
  | zero => simpa only [Function.iterate_zero,Function.id_comp,curveIterVelocity] using hv t
  | succ n ih =>
      have h:=liftCurve_hasDeriv k ((liftStep k)^[n] ∘ g) (curveIterVelocity k g v n) ih t
      convert h using 1
      · funext x
        simp only [Function.comp_apply,Function.iterate_succ_apply']
      · rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma curveInterval_lintegral_speed (I : CurveInterval) (v : ℝ → CurvePlane)
    (ε : ℝ) (hε : 0≤ε) (hv : ∀t∈Icc (0:ℝ) 1,‖I.velocity v t‖≤ε) :
    (∫⁻s in Icc I.left I.right,ENNReal.ofReal ‖v s‖)≤ENNReal.ofReal ε := by
  by_cases hzero:I.length=0
  · have hab:I.left=I.right := by dsimp [CurveInterval.length] at hzero; linarith
    simp only [hab,Icc_self,Measure.restrict_singleton,measure_singleton,zero_smul,lintegral_zero_measure]
    exact bot_le
  have hpos:0<I.length := lt_of_le_of_ne I.length_nonneg (Ne.symm hzero)
  have hpoint:∀s∈Icc I.left I.right,‖v s‖≤ε/I.length := by
    intro s hs
    obtain ⟨t,ht,rfl⟩:=I.parameter_range.superset hs
    have h:=hv t ht
    rw [I.velocity_norm] at h
    exact (le_div_iff₀ hpos).mpr (by nlinarith)
  calc
    _ ≤ ∫⁻s in Icc I.left I.right,ENNReal.ofReal (ε/I.length) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      exact ENNReal.ofReal_le_ofReal (hpoint s hs)
    _ = ENNReal.ofReal ε := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      change ENNReal.ofReal (ε/I.length)*ENNReal.ofReal I.length=ENNReal.ofReal ε
      rw [← ENNReal.ofReal_mul (div_nonneg hε hpos.le),div_mul_cancel₀ _ hpos.ne']
lemma curve_cover_lintegral_speed {ι : Type*} [Fintype ι]
    (I : ι → CurveInterval) (v : ℝ → CurvePlane) (ε : ℝ) (hε : 0≤ε)
    (hv : ∀i,∀t∈Icc (0:ℝ) 1,‖(I i).velocity v t‖≤ε)
    (S : Set ℝ) (hS : ∀s∈S,∃i,s∈Icc (I i).left (I i).right) :
    (∫⁻s in S,ENNReal.ofReal ‖v s‖)≤(Fintype.card ι:ℝ≥0∞)*ENNReal.ofReal ε := by
  calc
    _ ≤ ∫⁻s in ⋃i,Icc (I i).left (I i).right,ENNReal.ofReal ‖v s‖ :=
      lintegral_mono_set (fun s hs=>mem_iUnion.mpr (hS s hs))
    _ ≤ ∑'i,∫⁻s in Icc (I i).left (I i).right,ENNReal.ofReal ‖v s‖ :=
      lintegral_iUnion_le _ _
    _ ≤ ∑'i:ι,ENNReal.ofReal ε := ENNReal.tsum_le_tsum (fun i=>curveInterval_lintegral_speed (I i) v ε hε (hv i))
    _ = _ := by simp [tsum_fintype]
lemma controlled_curve_speed_from_map (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε : ℝ) (I : CurveInterval) (C : ControlledCurve ε) (hC : C.map=g ∘ I.parameter) :
    ∀t∈Icc (0:ℝ) 1,‖I.velocity v t‖≤ε := by
  intro t ht
  have h:=I.hasDeriv hv t
  rw [← hC] at h
  rw [h.unique (C.hasDeriv t)]
  exact C.speed t ht
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveCellIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma cell_curve_lintegral (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (J : CurveInterval) (C : ControlledCurve ε) (hC : C.map=g ∘ J.parameter)
    (c : ℕ → CurvePlane) (n : ℕ) (S : Set ℝ) (hS : S⊆Icc J.left J.right)
    (hword : ∀s∈S,∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (g s))) :
    (∫⁻s in S,ENNReal.ofReal ‖curveIterVelocity k g v n s‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
  obtain ⟨I,D,hcover,hmap⟩:=curve_iterate_cover k ε δ hk hε hδ0 hδ1 hδ hε1 hε2 N hN hN2 C c n
  let K:CurveTree N n → CurveInterval:=fun b=>J.comp (I b)
  have hD:∀b,(D b).map=(liftStep k)^[n] ∘ g ∘ (K b).parameter := by
    intro b
    rw [hmap,hC]
    funext t
    simp only [Function.comp_apply,K,CurveInterval.comp_parameter]
  have hK:∀s∈S,∃b,s∈Icc (K b).left (K b).right := by
    intro s hs
    obtain ⟨t,ht,hts⟩:=J.parameter_range.superset (hS hs)
    have hw:∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (C.map t)) := by
      intro j hj
      rw [hC]
      simpa only [Function.comp_apply,hts] using hword s hs j hj
    obtain ⟨a,ha⟩:=hcover t ht hw
    refine ⟨a,?_⟩
    rw [← hts]
    exact J.comp_mem (I a) ha
  have h:=curve_cover_lintegral_speed K (curveIterVelocity k g v n) ε hε
    (fun b=>controlled_curve_speed_from_map _ _ (curveIter_hasDeriv k g v hv n) ε (K b) (D b) (hD b)) S hK
  simpa only [curveTree_card,Nat.cast_pow] using h
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma wedge_quarterTurn_both (a b : ℂ) : wedge (quarterTurn a) (quarterTurn b)=wedge a b := by
  simp [wedge,quarterTurn]
  ring
lemma wedge_chain_bound (s : ℕ → ℂ) (e : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hu : ∀ i, a ≤ i → i ≤ b → ‖s i‖=1)
    (he : ∀ i, a ≤ i → i < b → |wedge (s i) (s (i+1))| ≤ e i) :
    |wedge (s a) (s b)| ≤ ∑ i ∈ Finset.Ico a b, e i := by
  induction b,hab using Nat.le_induction with
  | base => simp [wedge_refl]
  | succ b hab ih =>
    have hh:=ih (fun i hai hib => hu i hai (by omega)) (fun i hai hib => he i hai (by omega))
    have ht:=wedge_sine_triangle (s a) (s b) (s (b+1)) (hu a le_rfl (by omega))
      (hu b hab (by omega)) (hu (b+1) (by omega) le_rfl)
    rw [Finset.sum_Ico_succ_top hab]
    exact ht.trans (add_le_add hh (he b hab (by omega)))

lemma stable_direction_step {A B : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (a b : ℂ) (ha : ‖a‖=1) (_hb : ‖b‖=1)
    (hAa : ‖A a‖=‖A‖) (hBb : ‖B (quarterTurn b)‖=‖B‖⁻¹)
    (M : ℝ) (hB : 0 < ‖B‖) (hstep : ∀ z, ‖A z‖ ≤ M*‖B z‖) :
    |wedge (quarterTurn a) (quarterTurn b)| ≤ M/(‖A‖*‖B‖) := by
  have hpos : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  have hp:=expanded_projection_bound hA a ha hAa (quarterTurn b)
  rw [dot_quarterTurn_right] at hp
  have hs:=hstep (quarterTurn b)
  rw [hBb] at hs
  rw [wedge_quarterTurn_both]
  apply (le_div_iff₀ (mul_pos hpos hB)).mpr
  rw [abs_neg] at hp
  have hh := mul_le_mul_of_nonneg_right (hp.trans hs) hB.le
  calc
    _ = (‖A‖*|wedge a b|)*‖B‖ := by ring
    _  ≤  (M*‖B‖⁻¹)*‖B‖ := hh
    _ = M := by field_simp

lemma stable_prefix_finite_bound (A : ℕ → ℂ →L[ℝ] ℂ) (a : ℕ → ℂ)
    (D : ℕ → ℝ) (M : ℝ) (l B : ℕ) (hl : 1 ≤ l) (hlB : l ≤ B)
    (harea : ∀ i, 1 ≤ i → i ≤ B → PlaneAreaPreserving (A i))
    (hunit : ∀ i, 1 ≤ i → i ≤ B → ‖a i‖=1)
    (hnorm : ∀ i, 1 ≤ i → i ≤ B → ‖A i‖=D i)
    (hmax : ∀ i, 1 ≤ i → i ≤ B → ‖A i (a i)‖=D i)
    (hstable : ∀ i, 1 ≤ i → i ≤ B → ‖A i (quarterTurn (a i))‖=(D i)⁻¹)
    (hstep : ∀ i, 1 ≤ i → i < B → ∀ z, ‖A i z‖ ≤ M*‖A (i+1) z‖) :
    ‖A l (quarterTurn (a B))‖ ≤ (D l)⁻¹+D l*∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) := by
  have hpos (i : ℕ) (hi : 1 ≤ i) (hiB : i ≤ B) : 0 < ‖A i‖ :=
    lt_of_lt_of_le zero_lt_one (harea i hi hiB).singular_pair.choose_spec.2.2.2.2
  have hchain:=wedge_chain_bound (fun i => quarterTurn (a i))
    (fun i => M/(D i*D (i+1))) l B hlB
    (fun i hli hiB => by rw [norm_quarterTurn]; exact hunit i (by omega) hiB)
    (by
      intro i hli hiB
      have hh:=stable_direction_step (harea i (by omega) (by omega)) (a i) (a (i+1))
        (hunit i (by omega) (by omega)) (hunit (i+1) (by omega) (by omega))
        (by rw [hmax i (by omega) (by omega),hnorm i (by omega) (by omega)])
        (by rw [hstable (i+1) (by omega) (by omega),hnorm (i+1) (by omega) (by omega)])
        M (hpos (i+1) (by omega) (by omega)) (hstep i (by omega) hiB)
      simpa only [hnorm i (by omega) (by omega),hnorm (i+1) (by omega) (by omega)] using hh)
  rw [wedge_quarterTurn_both] at hchain
  have hup:=two_singular_upper (harea l hl hlB) (a l) (hunit l hl hlB)
    (by rw [hmax l hl hlB,hnorm l hl hlB]) (quarterTurn (a B))
  rw [dot_quarterTurn_right,abs_neg,hnorm l hl hlB] at hup
  have hw:=abs_wedge_le_norm_mul (a l) (quarterTurn (a B))
  rw [norm_quarterTurn,hunit l hl hlB,hunit B (by omega) le_rfl,mul_one] at hw
  have hD : 0 ≤ D l := by rw [← hnorm l hl hlB]; exact norm_nonneg _
  calc
    _  ≤  D l*|wedge (a l) (a B)|+(D l)⁻¹*|wedge (a l) (quarterTurn (a B))| := hup
    _  ≤  D l*(∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)))+(D l)⁻¹*1 :=
      add_le_add (mul_le_mul_of_nonneg_left hchain hD) (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hD))
    _ = _ := by ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_StablePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma Complex.norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re|+|z.im| := by
  have he : z = (z.re : ℂ)+z.im*Complex.I := by apply Complex.ext <;> simp
  calc
    ‖z‖ = ‖(z.re : ℂ)+z.im*Complex.I‖ := congrArg norm he
    _ ≤ ‖(z.re : ℂ)‖+‖(z.im : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = _ := by simp
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_WeightedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma product_slice_bound (E I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ≥0∞)
    (K : ℝ≥0∞) (hE : MeasurableSet E) (_hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I)
    (hslice : ∀ x ∈ E, ∫⁻ y in I, T.indicator f (x,y) ≤ K) :
    (∫⁻ z in T, f z) ≤ K*volume E := by
  have he : (∫⁻ z in T, f z) = ∫⁻ z in E ×ˢ I, T.indicator f z := by
    rw [lintegral_indicator hT,Measure.restrict_restrict hT,inter_eq_left.mpr hsub]
  rw [he]
  change (∫⁻ z, T.indicator f z ∂(volume.prod volume).restrict (E ×ˢ I)) ≤ _
  rw [← Measure.prod_restrict]
  calc
    _ ≤ ∫⁻ x in E, ∫⁻ y in I, T.indicator f (x,y) := lintegral_prod_le _
    _ ≤ ∫⁻ x in E, K := setLIntegral_mono' hE hslice
    _ = _ := by simp

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TorusIntegral
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy

lemma unit_cell_integral (g : Torus → ℝ≥0∞) (hg : Measurable g) (a b : ℝ) :
    (∫⁻ z in Ioc a (a+1) ×ˢ Ioc b (b+1), g (liftProjection z)) = ∫⁻ z, g z ∂area := by
  have h := (AddCircle.measurePreserving_mk (1:ℝ) a).prod (AddCircle.measurePreserving_mk (1:ℝ) b)
  rw [Measure.prod_restrict] at h
  exact h.lintegral_comp hg

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GridPartition
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma circleRep_coe_of_mem {x:ℝ} (hx:x∈Ico (0:ℝ) 1) : circleRep (x:Circle)=x := by
  rw [circleRep_coe,Int.fract_eq_self.mpr hx]
lemma gridLabel_eq_iff (Q:ℕ) (hQ:0<Q) (z w:Torus) :
    gridLabel Q hQ z=gridLabel Q hQ w ↔
      gridIndex Q hQ z.1=gridIndex Q hQ w.1 ∧ gridIndex Q hQ z.2=gridIndex Q hQ w.2 := by
  constructor
  · intro h
    have hv := congrArg (fun i:Fin (Q*Q+1)=>i.val) h
    have he:finProdFinEquiv (gridIndex Q hQ z.1,gridIndex Q hQ z.2)=
        finProdFinEquiv (gridIndex Q hQ w.1,gridIndex Q hQ w.2) := Fin.ext hv
    exact Prod.mk.inj (finProdFinEquiv.injective he)
  · rintro ⟨h1,h2⟩; simp only [gridLabel,h1,h2]
lemma gridIndex_bounds (Q:ℕ) (hQ:0<Q) (x:Circle) :
    (gridIndex Q hQ x:ℝ)/(Q:ℝ)≤circleRep x ∧ circleRep x<((gridIndex Q hQ x:ℝ)+1)/(Q:ℝ) := by
  have hq:(0:ℝ)<Q := Nat.cast_pos.mpr hQ
  constructor
  · apply (div_le_iff₀ hq).mpr
    simpa only [mul_comm,gridIndex] using Nat.floor_le (mul_nonneg hq.le (circleRep_mem x).1)
  · apply (lt_div_iff₀ hq).mpr
    simpa only [mul_comm,gridIndex] using Nat.lt_floor_add_one ((Q:ℝ)*circleRep x)
lemma gridIndex_close (Q:ℕ) (hQ:0<Q) {x y:Circle} (h:gridIndex Q hQ x=gridIndex Q hQ y) :
    |circleRep x-circleRep y|≤1/(Q:ℝ) := by
  have hx:=gridIndex_bounds Q hQ x
  have hy:=gridIndex_bounds Q hQ y
  rw [h] at hx
  rw [add_div] at hx hy
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma gridLabel_close (Q:ℕ) (hQ:0<Q) {z w:Torus} (h:gridLabel Q hQ z=gridLabel Q hQ w) :
    ‖torusRep z-torusRep w‖≤1/(Q:ℝ) := by
  obtain ⟨h1,h2⟩:=(gridLabel_eq_iff Q hQ z w).mp h
  exact max_le (gridIndex_close Q hQ h1) (gridIndex_close Q hQ h2)
lemma projection_wrappedBox (δ:ℝ) (x:CurvePlane) (z:Torus) (h:‖torusRep (liftProjection x)-torusRep z‖≤δ) :
    wrappedBox δ (torusRep z) x := by
  refine ⟨(⌊x.1⌋,⌊x.2⌋),?_⟩
  have he:x-((torusRep z).1+(⌊x.1⌋:ℝ),(torusRep z).2+(⌊x.2⌋:ℝ))=
      torusRep (liftProjection x)-torusRep z := by
    ext <;> simp only [torusRep,liftProjection,circleRep_coe,Prod.fst_sub,Prod.snd_sub,Int.fract] <;> ring
  rw [he]; exact h
lemma unit_ico_cell_integral (g:Torus → ℝ≥0∞) (hg:Measurable g) :
    (∫⁻z in Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1,g (liftProjection z))=∫⁻z,g z ∂area := by
  have h:=unit_cell_integral g hg 0 0
  simp only [zero_add] at h
  change (∫⁻z,g (liftProjection z) ∂(volume.prod volume).restrict (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1))=_
  rw [← Measure.prod_restrict,restrict_Ico_eq_restrict_Ioc,Measure.prod_restrict]
  exact h
lemma gridInterval_length (Q:ℕ) (hQ:0<Q) (i:Fin Q) : (gridInterval Q hQ i).length=1/(Q:ℝ) := by
  dsimp [gridInterval,CurveInterval.length]; ring
lemma gridInterval_mem (Q:ℕ) (hQ:0<Q) (x:Circle) :
    circleRep x∈Icc (gridInterval Q hQ (gridIndex Q hQ x)).left (gridInterval Q hQ (gridIndex Q hQ x)).right :=
  ⟨(gridIndex_bounds Q hQ x).1,(gridIndex_bounds Q hQ x).2.le⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveColumns
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma complexPair_norm (z:CurvePlane) : ‖complexPair z‖≤2*‖z‖ := by
  have h:=Complex.norm_le_abs_re_add_abs_im (complexPair z)
  have h1:=norm_fst_le z
  have h2:=norm_snd_le z
  change |z.1|≤‖z‖ at h1
  change |z.2|≤‖z‖ at h2
  change ‖complexPair z‖≤|z.1|+|z.2| at h
  linarith
lemma complexPair_transfer (a:ℝ) (z:CurvePlane) :
    complexPair (pairTransfer a z)=transferStep a (complexPair z) := rfl
lemma curveIterVelocity_transfer (k:ℝ) (g v:ℝ → CurvePlane) (n:ℕ) (t:ℝ) :
    complexPair (curveIterVelocity k g v n t)=liftSegmentTransfer k (g t) 0 n (complexPair (v t)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change complexPair (pairTransfer (potential k (((liftStep k)^[n]) (g t)).1)
      (curveIterVelocity k g v n t))=_
    rw [complexPair_transfer,ih]
    change _=transferStep (liftSegmentCoefficient k (g t) 0 (n+1))
      (liftSegmentTransfer k (g t) 0 n (complexPair (v t)))
    congr 2
    unfold liftSegmentCoefficient
    rw [show (0:ℤ)+((n+1:ℕ):ℤ)-1=(n:ℤ) by omega]
    simp only [liftIter,zpow_natCast,Equiv.Perm.coe_pow]
lemma complex_operator_columns (A:ℂ →L[ℝ] ℂ) : ‖A‖≤‖A 1‖+‖A Complex.I‖ := by
  apply A.opNorm_le_bound (by positivity)
  intro z
  have he:z=z.re • (1:ℂ)+z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    _ = ‖z.re • A 1+z.im • A Complex.I‖ := by conv_lhs => rw [he]; rw [map_add,map_smul,map_smul]
    _ ≤ ‖z.re • A 1‖+‖z.im • A Complex.I‖ := norm_add_le _ _
    _ = |z.re| *‖A 1‖+|z.im| *‖A Complex.I‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖z‖*‖A 1‖+‖z‖*‖A Complex.I‖ := add_le_add
      (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _))
    _ = _ := by ring
lemma horizontalVelocity_eq (k:ℝ) (n:ℕ) (z:CurvePlane) :
    complexPair (horizontalVelocity k n z)=liftSegmentTransfer k z 0 n 1 := by
  convert! curveIterVelocity_transfer k (fun t=>(t,z.2)) (fun _=>(1,0)) n z.1 using 1
lemma verticalVelocity_eq (k:ℝ) (n:ℕ) (z:CurvePlane) :
    complexPair (verticalVelocity k n z)=liftSegmentTransfer k z 0 n Complex.I := by
  convert! curveIterVelocity_transfer k (fun t=>(z.1,t)) (fun _=>(0,1)) n z.2 using 1
lemma liftTransfer_columns_bound (k:ℝ) (n:ℕ) (z:CurvePlane) :
    ‖liftSegmentTransfer k z 0 n‖≤2*(‖horizontalVelocity k n z‖+‖verticalVelocity k n z‖) := by
  have h:=complex_operator_columns (liftSegmentTransfer k z 0 n)
  rw [← horizontalVelocity_eq,← verticalVelocity_eq] at h
  linarith [complexPair_norm (horizontalVelocity k n z),complexPair_norm (verticalVelocity k n z)]
lemma continuous_horizontalVelocity (k:ℝ) (n:ℕ) : Continuous (horizontalVelocity k n) := by
  have h:horizontalVelocity k n=fun z=>Complex.equivRealProdCLM (torusSegmentTransfer k (liftProjection z) 0 n 1) := by
    funext z
    rw [torusSegmentTransfer_lift,← horizontalVelocity_eq]
    rfl
  rw [h]
  apply Complex.equivRealProdCLM.continuous.comp
  exact ((continuous_torusSegmentTransfer k 0 n).comp
    ((AddCircle.continuous_mk' (1:ℝ)).prodMap (AddCircle.continuous_mk' (1:ℝ)))).clm_apply continuous_const
lemma continuous_verticalVelocity (k:ℝ) (n:ℕ) : Continuous (verticalVelocity k n) := by
  have h:verticalVelocity k n=fun z=>Complex.equivRealProdCLM (torusSegmentTransfer k (liftProjection z) 0 n Complex.I) := by
    funext z
    rw [torusSegmentTransfer_lift,← verticalVelocity_eq]
    rfl
  rw [h]
  apply Complex.equivRealProdCLM.continuous.comp
  exact ((continuous_torusSegmentTransfer k 0 n).comp
    ((AddCircle.continuous_mk' (1:ℝ)).prodMap (AddCircle.continuous_mk' (1:ℝ)))).clm_apply continuous_const
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CurveLineIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma cell_line_lintegral (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g:ℝ → CurvePlane) (u:CurvePlane) (hu:‖u‖≤1) (hv : ∀t,HasDerivAt g u t)
    (J : CurveInterval) (hJ:J.length≤ε)
    (c : ℕ → CurvePlane) (n : ℕ) (S : Set ℝ) (hS : S⊆Icc J.left J.right)
    (hword : ∀s∈S,∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (g s))) :
    (∫⁻s in S,ENNReal.ofReal ‖curveIterVelocity k g (fun _=>u) n s‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
  obtain ⟨C,hC,_⟩:=restricted_controlled_curve ε hε g (fun _=>u) hv continuous_const
    (by intro s hs t ht; simp only [sub_self,norm_zero]; positivity) J (by
      intro t ht
      rw [J.velocity_norm]
      exact (mul_le_mul_of_nonneg_left hu J.length_nonneg).trans (by simpa only [mul_one] using hJ))
  exact cell_curve_lintegral k ε δ hk hε hδ0 hδ1 hδ hε1 hε2 N hN hN2 g (fun _=>u) hv J C hC c n S hS hword
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GridWordIntegrals
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma product_slice_bound_reverse (E I : Set ℝ) (T:Set CurvePlane) (f:CurvePlane → ℝ≥0∞)
    (K:ℝ≥0∞) (_hE:MeasurableSet E) (hI:MeasurableSet I) (hT:MeasurableSet T) (hf:Measurable f)
    (hsub:T⊆E ×ˢ I)
    (hslice:∀y∈I,∫⁻x in E,T.indicator f (x,y)≤K) :
    (∫⁻z in T,f z)≤K*volume I := by
  have he:(∫⁻z in T,f z)=∫⁻z in E ×ˢ I,T.indicator f z := by
    rw [lintegral_indicator hT,Measure.restrict_restrict hT,inter_eq_left.mpr hsub]
  rw [he]
  change (∫⁻z,T.indicator f z ∂(volume.prod volume).restrict (E ×ˢ I))≤_
  rw [← Measure.prod_restrict,lintegral_prod_symm' _ (hf.indicator hT)]
  calc
    _ ≤ ∫⁻y in I,K := setLIntegral_mono' hI hslice
    _ = _ := by simp
lemma fiber_indicator_bound (T:Set CurvePlane) (hT:MeasurableSet T) (f:CurvePlane → ℝ≥0∞)
    (g:ℝ → CurvePlane) (hg:Measurable g) (I:Set ℝ) :
    (∫⁻t in I,T.indicator f (g t))≤∫⁻t in g ⁻¹' T,f (g t) := by
  calc
    _ ≤ ∫⁻t,T.indicator f (g t) := by
      simpa only [Measure.restrict_univ] using (lintegral_mono_set (f:=fun t=>T.indicator f (g t)) (μ:=volume) (show I⊆univ from subset_univ _))
    _ = _ := by
      rw [← lintegral_indicator (hg hT)]
      congr 1

lemma grid_word_wrapped (k:ℝ) (Q:ℕ) (hQ:0<Q) (z:CurvePlane) (z0:Torus) (j:ℕ)
    (h:gridLabel Q hQ ((torusStep k)^[j] (liftProjection z))=gridLabel Q hQ ((torusStep k)^[j] z0)) :
    wrappedBox (1/(Q:ℝ)) (torusRep ((torusStep k)^[j] z0)) ((liftStep k)^[j] z) := by
  apply projection_wrappedBox
  have hp:liftProjection ((liftStep k)^[j] z)=(torusStep k)^[j] (liftProjection z) :=
    (show Function.Semiconj liftProjection (liftStep k) (torusStep k) from liftProjection_step k).iterate_right j z
  rw [hp]
  exact gridLabel_close Q hQ h
lemma grid_word_initial (Q:ℕ) (hQ:0<Q) (z:CurvePlane) (z0:Torus)
    (hz:z∈Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) (h:gridLabel Q hQ (liftProjection z)=gridLabel Q hQ z0) :
    z∈Icc (gridInterval Q hQ (gridIndex Q hQ z0.1)).left (gridInterval Q hQ (gridIndex Q hQ z0.1)).right ×ˢ
      Icc (gridInterval Q hQ (gridIndex Q hQ z0.2)).left (gridInterval Q hQ (gridIndex Q hQ z0.2)).right := by
  obtain ⟨h1,h2⟩:=(gridLabel_eq_iff Q hQ _ _).mp h
  have hx:=gridInterval_mem Q hQ (liftProjection z).1
  have hy:=gridInterval_mem Q hQ (liftProjection z).2
  rw [h1] at hx
  rw [h2] at hy
  simp only [liftProjection,circleRep_coe_of_mem hz.1] at hx
  simp only [liftProjection,circleRep_coe_of_mem hz.2] at hy
  exact ⟨hx,hy⟩
lemma grid_word_columns_integral (k ε:ℝ) (hk:0≤k) (hε:0≤ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) (z0:Torus) (T:Set CurvePlane) (hT:MeasurableSet T)
    (hunit:T⊆Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1)
    (hword:∀z∈T,∀j≤n,gridLabel Q hQ ((torusStep k)^[j] (liftProjection z))=
      gridLabel Q hQ ((torusStep k)^[j] z0)) :
    (∫⁻z in T,ENNReal.ofReal ‖horizontalVelocity k n z‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε*ENNReal.ofReal (1/(Q:ℝ)) ∧
    (∫⁻z in T,ENNReal.ofReal ‖verticalVelocity k n z‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε*ENNReal.ofReal (1/(Q:ℝ)) := by
  let Jx:=gridInterval Q hQ (gridIndex Q hQ z0.1)
  let Jy:=gridInterval Q hQ (gridIndex Q hQ z0.2)
  let E:=Icc Jx.left Jx.right
  let I:=Icc Jy.left Jy.right
  have hsub:T⊆E ×ˢ I := fun z hz=>grid_word_initial Q hQ z z0 (hunit hz) (hword z hz 0 (Nat.zero_le _))
  have hq:(0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hδ:0≤1/(Q:ℝ) := by positivity
  have hδ1:1/(Q:ℝ)≤1 := (div_le_one hq).mpr (by exact_mod_cast hQ)
  have hδe:6*(1/(Q:ℝ))≤ε := by simpa only [mul_one_div] using hQε
  have hlen:1/(Q:ℝ)≤ε := by linarith
  have hvolX:volume E=ENNReal.ofReal (1/(Q:ℝ)) := by
    rw [Real.volume_Icc]; exact congrArg ENNReal.ofReal (gridInterval_length Q hQ _)
  have hvolY:volume I=ENNReal.ofReal (1/(Q:ℝ)) := by
    rw [Real.volume_Icc]; exact congrArg ENNReal.ofReal (gridInterval_length Q hQ _)
  constructor
  · have hs:∀y∈I,∫⁻x in E,T.indicator (fun z=>ENNReal.ofReal ‖horizontalVelocity k n z‖) (x,y)≤
        ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
      intro y hy
      let g:ℝ → CurvePlane:=fun x=>(x,y)
      have hg:∀t,HasDerivAt g (1,0) t := fun t=>(hasDerivAt_id t).prodMk (hasDerivAt_const t y)
      have hc:=cell_line_lintegral k ε (1/(Q:ℝ)) hk hε hδ hδ1 hδe hε1 hε2 N hN hN2 g (1,0)
        (by simp) hg Jx (by rw [gridInterval_length]; exact hlen)
        (fun j=>torusRep ((torusStep k)^[j+1] z0)) n (g ⁻¹' T)
        (fun t ht=>(hsub ht).1) (fun t ht j hj=>grid_word_wrapped k Q hQ (g t) z0 (j+1) (hword (g t) ht _ (by omega)))
      exact (fiber_indicator_bound T hT _ g (measurable_id.prodMk measurable_const) E).trans hc
    have hh:=product_slice_bound_reverse E I T _ _ measurableSet_Icc measurableSet_Icc hT
      (ENNReal.measurable_ofReal.comp (continuous_horizontalVelocity k n).norm.measurable) hsub hs
    simpa only [hvolY,Function.comp_apply] using hh
  · have hs:∀x∈E,∫⁻y in I,T.indicator (fun z=>ENNReal.ofReal ‖verticalVelocity k n z‖) (x,y)≤
        ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
      intro x hx
      let g:ℝ → CurvePlane:=fun y=>(x,y)
      have hg:∀t,HasDerivAt g (0,1) t := fun t=>(hasDerivAt_const t x).prodMk (hasDerivAt_id t)
      have hc:=cell_line_lintegral k ε (1/(Q:ℝ)) hk hε hδ hδ1 hδe hε1 hε2 N hN hN2 g (0,1)
        (by simp) hg Jy (by rw [gridInterval_length]; exact hlen)
        (fun j=>torusRep ((torusStep k)^[j+1] z0)) n (g ⁻¹' T)
        (fun t ht=>(hsub ht).2) (fun t ht j hj=>grid_word_wrapped k Q hQ (g t) z0 (j+1) (hword (g t) ht _ (by omega)))
      exact (fiber_indicator_bound T hT _ g (measurable_const.prodMk measurable_id) I).trans hc
    have hh:=product_slice_bound E I T _ _ measurableSet_Icc measurableSet_Icc hT hsub hs
    simpa only [hvolX] using hh
lemma grid_word_transfer_integral (k ε:ℝ) (hk:0≤k) (hε:0≤ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) (z0:Torus) (T:Set CurvePlane) (hT:MeasurableSet T)
    (hunit:T⊆Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1)
    (hword:∀z∈T,∀j≤n,gridLabel Q hQ ((torusStep k)^[j] (liftProjection z))=
      gridLabel Q hQ ((torusStep k)^[j] z0)) :
    (∫⁻z in T,ENNReal.ofReal ‖liftSegmentTransfer k z 0 n‖)≤
      ENNReal.ofReal (4*ε/(Q:ℝ))*((196*N:ℕ):ℝ≥0∞)^n := by
  have hmX:Measurable (fun z=>ENNReal.ofReal ‖horizontalVelocity k n z‖) := ENNReal.measurable_ofReal.comp (continuous_horizontalVelocity k n).norm.measurable
  have hmY:Measurable (fun z=>ENNReal.ofReal ‖verticalVelocity k n z‖) := ENNReal.measurable_ofReal.comp (continuous_verticalVelocity k n).norm.measurable
  obtain ⟨hx,hy⟩:=grid_word_columns_integral k ε hk hε hε1 hε2 Q N hQ hQε hN hN2 n z0 T hT hunit hword
  calc
    _ ≤ ∫⁻z in T,(2:ℝ≥0∞)*(ENNReal.ofReal ‖horizontalVelocity k n z‖+ENNReal.ofReal ‖verticalVelocity k n z‖) := by
      apply lintegral_mono
      intro z
      have h:=ENNReal.ofReal_le_ofReal (liftTransfer_columns_bound k n z)
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)] using h
    _ = 2*((∫⁻z in T,ENNReal.ofReal ‖horizontalVelocity k n z‖)+
        (∫⁻z in T,ENNReal.ofReal ‖verticalVelocity k n z‖)) := by
      change (∫⁻z in T,(2:ℝ≥0∞)*((fun z=>ENNReal.ofReal ‖horizontalVelocity k n z‖)+(fun z=>ENNReal.ofReal ‖verticalVelocity k n z‖)) z)=_
      rw [lintegral_const_mul _ (hmX.add hmY)]
      simp only [Pi.add_apply]
      rw [lintegral_add_left hmX]
    _ ≤ 2*(((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε*ENNReal.ofReal (1/(Q:ℝ))+
        ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε*ENNReal.ofReal (1/(Q:ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hx hy) (by positivity)
    _ = _ := by
      rw [show 4*ε/(Q:ℝ)=4*(ε*(1/(Q:ℝ))) by ring,
        ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4), ENNReal.ofReal_mul hε,ENNReal.ofReal_ofNat]
      ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EntropyIntegral
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma blockAtom_measurable {r:ℕ} (f:Torus → Torus) (hf:Measurable f) (p:FinitePartition r)
    (n:ℕ) (w:Fin n → Fin (r+1)) : MeasurableSet (blockAtom f p n w) := by
  have h:=MeasurableSet.iInter (fun i:Fin n=>(p.property.comp (hf.iterate i.val)) (measurableSet_singleton (w i)))
  convert h using 1
  ext z
  simp only [blockAtom,mem_ofPred_eq,mem_iInter,mem_preimage,mem_singleton_iff,Function.comp_apply]
lemma blockAtom_iUnion {r:ℕ} (f:Torus → Torus) (p:FinitePartition r) (n:ℕ) :
    (⋃w:Fin n → Fin (r+1),blockAtom f p n w)=univ := by
  apply eq_univ_of_forall
  intro z
  exact mem_iUnion.mpr ⟨fun i=>p.val (f^[i.val] z),fun _=>rfl⟩
lemma blockAtom_disjoint {r:ℕ} (f:Torus → Torus) (p:FinitePartition r) (n:ℕ) :
    Pairwise (Function.onFun Disjoint (blockAtom f p n)) := by
  intro w v hne
  apply Set.disjoint_left.mpr
  intro z hz hv
  apply hne
  funext i
  exact (hz i).symm.trans (hv i)
lemma sum_block_integral {r:ℕ} (μ:Measure Torus) (f:Torus → Torus) (hf:Measurable f)
    (p:FinitePartition r) (n:ℕ) (g:Torus → ℝ) (hg:Integrable g μ) :
    (∑w:Fin n → Fin (r+1),∫z in blockAtom f p n w,g z ∂μ)=∫z,g z ∂μ := by
  have h:=integral_iUnion (blockAtom_measurable f hf p n) (blockAtom_disjoint f p n) hg.integrableOn
  rw [blockAtom_iUnion,Measure.restrict_univ,tsum_fintype] at h
  exact h.symm
lemma sum_block_mass {r:ℕ} (μ:Measure Torus) [IsProbabilityMeasure μ]
    (f:Torus → Torus) (hf:Measurable f) (p:FinitePartition r) (n:ℕ) :
    (∑w:Fin n → Fin (r+1),(μ (blockAtom f p n w)).toReal)=1 := by
  have h:=sum_block_integral μ f hf p n (fun _=>1) (integrable_const (1:ℝ))
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,measure_univ,ENNReal.toReal_one,smul_eq_mul,mul_one] using h
lemma atom_log_integral_bound (μ:Measure Torus) [IsFiniteMeasure μ] (A:Set Torus)
    (g:Torus → ℝ) (hg:Integrable g μ) (hlog:Integrable (fun z=>Real.log (g z)) μ)
    (hpos:∀z,0<g z) (B:ℝ) (hB:0<B) (hbound:(∫z in A,g z ∂μ)≤B) :
    (∫z in A,Real.log (g z) ∂μ)≤
      (μ A).toReal*Real.log B-(μ A).toReal*Real.log (μ A).toReal := by
  let p:ℝ:=(μ A).toReal
  by_cases he:p=0
  · have hzero:μ A=0 := ((ENNReal.toReal_eq_zero_iff (μ A)).mp he).resolve_right (measure_ne_top μ A)
    rw [Measure.restrict_eq_zero.mpr hzero,integral_zero_measure]
    simp only [← show p=(μ A).toReal from rfl,he,zero_mul,sub_self,le_refl]
  have hp:0<p := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm he)
  let a:ℝ:=B/p
  have ha:0<a := div_pos hB hp
  have hpoint:∀z,Real.log (g z)≤Real.log a+g z/a-1 := by
    intro z
    have h:=Real.log_le_sub_one_of_pos (div_pos (hpos z) ha)
    rw [Real.log_div (hpos z).ne' ha.ne'] at h
    linarith
  have hgA : Integrable g (μ.restrict A) := hg.integrableOn
  have hlA : Integrable (fun z=>Real.log (g z)) (μ.restrict A) := hlog.integrableOn
  have hcA : Integrable (fun _ : Torus => Real.log a) (μ.restrict A) := integrable_const _
  have h1A : Integrable (fun _ : Torus => (1:ℝ)) (μ.restrict A) := integrable_const _
  have hi:=integral_mono hlA ((hcA.add (hgA.div_const a)).sub h1A) hpoint
  simp only [Pi.add_apply,Pi.sub_apply] at hi
  rw [integral_sub (f:=fun z=>Real.log a+g z/a) (g:=fun _=>1) (hcA.add (hgA.div_const a)) h1A,
    integral_add (f:=fun _=>Real.log a) (g:=fun z=>g z/a) hcA (hgA.div_const a),integral_div,
    setIntegral_const,setIntegral_const] at hi
  simp only [smul_eq_mul,mul_one] at hi
  change (∫z in A,Real.log (g z) ∂μ)≤p*Real.log B-p*Real.log p
  have hdiv:(∫z in A,g z ∂μ)/a≤p := by
    apply (div_le_iff₀ ha).mpr
    calc
      _ ≤ B := hbound
      _ = p*a := by dsimp [a]; field_simp
  have hloga:Real.log a=Real.log B-Real.log p := Real.log_div hB.ne' hp.ne'
  change (∫z in A,Real.log (g z) ∂μ)≤p*Real.log a+(∫z in A,g z ∂μ)/a-p at hi
  rw [hloga] at hi
  nlinarith
lemma entropy_from_atom_integrals {r:ℕ} (μ:Measure Torus) [IsProbabilityMeasure μ]
    (f:Torus → Torus) (hf:Measurable f) (p:FinitePartition r) (n:ℕ)
    (g:Torus → ℝ) (hg:Integrable g μ) (hlog:Integrable (fun z=>Real.log (g z)) μ)
    (hpos:∀z,0<g z) (B:ℝ) (hB:0<B)
    (hbound:∀w:Fin n → Fin (r+1),(∫z in blockAtom f p n w,g z ∂μ)≤B) :
    (∫z,Real.log (g z) ∂μ)-Real.log B≤blockEntropy μ f p n := by
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun w _=>atom_log_integral_bound μ (blockAtom f p n w)
    g hg hlog hpos B hB (hbound w))
  rw [sum_block_integral μ f hf p n _ hlog,Finset.sum_sub_distrib,← Finset.sum_mul,
    sum_block_mass μ f hf p n,one_mul] at h
  unfold blockEntropy
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BackwardSlice
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_liftProjection : Continuous liftProjection :=
  (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GridAtomBound
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma atom_lift_lintegral (A:Set Torus) (hA:MeasurableSet A) (g:Torus → ℝ≥0∞) (hg:Measurable g) :
    (∫⁻z in A,g z ∂area)=∫⁻z in (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) ∩ liftProjection ⁻¹' A,g (liftProjection z) := by
  rw [← lintegral_indicator hA,← unit_ico_cell_integral _ (hg.indicator hA)]
  have hcomp:(fun z=>A.indicator g (liftProjection z))=
      (liftProjection ⁻¹' A).indicator (g ∘ liftProjection) := by
    funext z
    by_cases hz:liftProjection z∈A <;> simp [hz]
  rw [hcomp,lintegral_indicator (continuous_liftProjection.measurable hA),
    Measure.restrict_restrict (continuous_liftProjection.measurable hA),inter_comm]
  rfl
lemma grid_atom_lintegral (k ε:ℝ) (hk:0≤k) (hε:0≤ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) (w:Fin (n+1) → Fin (Q*Q+1)) :
    (∫⁻z in blockAtom (torusStep k) (gridPartition Q hQ) (n+1) w,
      ENNReal.ofReal ‖torusSegmentTransfer k z 0 n‖ ∂area)≤
      ENNReal.ofReal (4*ε/(Q:ℝ))*((196*N:ℕ):ℝ≥0∞)^n := by
  let A:=blockAtom (torusStep k) (gridPartition Q hQ) (n+1) w
  have hA:MeasurableSet A := blockAtom_measurable _ (continuous_torusStep k).measurable _ _ _
  by_cases he:A.Nonempty
  · obtain ⟨z0,hz0⟩:=he
    let T:Set CurvePlane:=(Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) ∩ liftProjection ⁻¹' A
    have hT:MeasurableSet T := (measurableSet_Ico.prod measurableSet_Ico).inter (continuous_liftProjection.measurable hA)
    have hword:∀z∈T,∀j≤n,gridLabel Q hQ ((torusStep k)^[j] (liftProjection z))=
        gridLabel Q hQ ((torusStep k)^[j] z0) := by
      intro z hz j hj
      exact ((hz.2 : liftProjection z∈A) ⟨j,by omega⟩).trans (hz0 ⟨j,by omega⟩).symm
    have h:=grid_word_transfer_integral k ε hk hε hε1 hε2 Q N hQ hQε hN hN2 n z0 T hT
      (fun _ hz=>hz.1) hword
    change (∫⁻z in A,ENNReal.ofReal ‖torusSegmentTransfer k z 0 n‖ ∂area)≤_
    rw [atom_lift_lintegral A hA (fun z=>ENNReal.ofReal ‖torusSegmentTransfer k z 0 n‖) (ENNReal.measurable_ofReal.comp (continuous_torusSegmentTransfer k 0 n).norm.measurable)]
    simpa only [torusSegmentTransfer_lift] using h
  · have hzero:A=∅ := not_nonempty_iff_eq_empty.mp he
    change (∫⁻z in A,ENNReal.ofReal ‖torusSegmentTransfer k z 0 n‖ ∂area)≤_
    rw [hzero,Measure.restrict_empty,lintegral_zero_measure]
    exact bot_le
lemma integrable_transfer_norm (k:ℝ) (n:ℕ) : Integrable (fun z=>‖torusSegmentTransfer k z 0 n‖) area :=
  (continuous_torusSegmentTransfer k 0 n).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma integrable_transfer_log (k:ℝ) (hk:0≤k) (n:ℕ) : Integrable (fun z=>Real.log ‖torusSegmentTransfer k z 0 n‖) area :=
  ((continuous_torusSegmentTransfer k 0 n).norm.log (fun z=>by
    have h:=(torusSegmentTransfer_norm_bounds k hk z 0 n).1; linarith)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma grid_atom_integral (k ε:ℝ) (hk:0≤k) (hε:0≤ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) (w:Fin (n+1) → Fin (Q*Q+1)) :
    (∫z in blockAtom (torusStep k) (gridPartition Q hQ) (n+1) w,
      ‖torusSegmentTransfer k z 0 n‖ ∂area)≤
      (4*ε/(Q:ℝ))*((196*N:ℕ):ℝ)^n := by
  have h:=grid_atom_lintegral k ε hk hε hε1 hε2 Q N hQ hQε hN hN2 n w
  have hC:0≤4*ε/(Q:ℝ) := by positivity
  have he:ENNReal.ofReal ((4*ε/(Q:ℝ))*((196*N:ℕ):ℝ)^n)=
      ENNReal.ofReal (4*ε/(Q:ℝ))*((196*N:ℕ):ℝ≥0∞)^n := by
    rw [ENNReal.ofReal_mul hC,ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_natCast]
  rw [← he] at h
  have hreal:=ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z=>norm_nonneg _)
    (integrable_transfer_norm k n).integrableOn.aestronglyMeasurable]
  exact hreal
lemma grid_block_entropy_growth (k ε:ℝ) (hk:0≤k) (hε:0<ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) :
    (∫z,Real.log ‖torusSegmentTransfer k z 0 n‖ ∂area)-
      Real.log (4*ε/(Q:ℝ))-(n:ℝ)*Real.log ((196*N:ℕ):ℝ)≤
      blockEntropy area (torusStep k) (gridPartition Q hQ) (n+1) := by
  have hC:0<4*ε/(Q:ℝ) := by positivity
  have hR:(0:ℝ)<(196*N:ℕ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0<196) hN
  have h:=entropy_from_atom_integrals area (torusStep k) (continuous_torusStep k).measurable (gridPartition Q hQ) (n+1)
    (fun z=>‖torusSegmentTransfer k z 0 n‖) (integrable_transfer_norm k n) (integrable_transfer_log k hk n)
    (fun z=>lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk z 0 n).1)
    ((4*ε/(Q:ℝ))*((196*N:ℕ):ℝ)^n) (by positivity)
    (grid_atom_integral k ε hk hε.le hε1 hε2 Q N hQ hQε hN hN2 n)
  rw [Real.log_mul hC.ne' (pow_pos hR n).ne',Real.log_pow] at h
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CancellationVector
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma torusPotential_bound (k : ℝ) (hk : 0 ≤ k) (x : Circle) : |torusPotential k x|+1 ≤ growthBase k := by
  obtain ⟨t,rfl⟩ := Quotient.mk_surjective x
  exact potential_bound k t hk
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EntropyConjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma coordinate_blockAtom {r:ℕ} (k:ℝ) (p:FinitePartition r) (n:ℕ) (w:Fin n → Fin (r+1)) :
    blockAtom (standardMap k) (coordinatePartition p) n w=
      recurrenceCoordinates ⁻¹' blockAtom (torusStep k) p n w := by
  have hc:Function.Semiconj recurrenceCoordinates (standardMap k) (torusStep k) := standardMap_conjugacy k
  ext z
  simp only [blockAtom,mem_ofPred_eq,mem_preimage,coordinatePartition,Function.comp_apply]
  simp only [hc.iterate_right _ _]
lemma coordinate_blockEntropy {r:ℕ} (k:ℝ) (p:FinitePartition r) (n:ℕ) :
    blockEntropy area (standardMap k) (coordinatePartition p) n=blockEntropy area (torusStep k) p n := by
  unfold blockEntropy
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [coordinate_blockAtom,measurePreserving_recurrenceCoordinates.measure_preimage
    (blockAtom_measurable _ (continuous_torusStep k).measurable p n w).nullMeasurableSet]
lemma coordinate_partitionEntropy {r:ℕ} (k:ℝ) (p:FinitePartition r) :
    partitionEntropy area (standardMap k) (coordinatePartition p)=partitionEntropy area (torusStep k) p := by
  unfold partitionEntropy
  simp only [coordinate_blockEntropy]
lemma metricEntropy_standardMap_ge_partition {r:ℕ} (k:ℝ) (p:FinitePartition r) :
    partitionEntropy area (torusStep k) p≤ metricEntropy area (standardMap k) := by
  rw [← coordinate_partitionEntropy]
  exact le_iSup_of_le r (le_iSup_of_le (coordinatePartition p) le_rfl)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EntropyParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma entropy_subdivision_parameters (M:ℝ) (hM:(1000:ℝ)^4≤M) :
    ∃N:ℕ,0<N ∧ 2*M≤(N:ℝ)^2 ∧ Real.log ((196*N:ℕ):ℝ)≤(3/4:ℝ)*Real.log M := by
  have hM1:1≤M := by nlinarith
  have hM0:0<M := by linarith
  let N:ℕ:=⌈Real.sqrt (2*M)⌉₊
  have hNp:0<N := Nat.ceil_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hNl:Real.sqrt (2*M)≤(N:ℝ) := Nat.le_ceil _
  have hNu:(N:ℝ)<Real.sqrt (2*M)+1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hMs:1≤Real.sqrt M := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hM1
  have hNs:Real.sqrt (2*M)≤2*Real.sqrt M := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hM0.le]
  have hN2:2*M≤(N:ℝ)^2 := by nlinarith [Real.sq_sqrt (show 0≤2*M by positivity),Real.sqrt_nonneg (2*M)]
  have hN3:(N:ℝ)≤3*Real.sqrt M := by linarith
  have hR:((196*N:ℕ):ℝ)≤1000*Real.sqrt M := by push_cast; nlinarith [Real.sqrt_nonneg M]
  have hRp:0<((196*N:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0<196) hNp
  have hlogM:(4:ℝ)*Real.log 1000≤Real.log M := by
    have h:=Real.log_le_log (by positivity : (0:ℝ)<1000^4) hM
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have hlogR:=Real.log_le_log hRp hR
  rw [Real.log_mul (by norm_num : (1000:ℝ)≠0) (Real.sqrt_pos.mpr hM0).ne',Real.log_sqrt hM0.le] at hlogR
  exact ⟨N,hNp,hN2,by linarith⟩
lemma entropy_grid_parameters (M:ℝ) (hM:1≤M) :
    ∃ε:ℝ,∃Q:ℕ,0<ε ∧ 0<Q ∧ 2*Real.pi*ε≤1 ∧ M*ε≤1 ∧ 6/(Q:ℝ)≤ε ∧
      Real.log (4*ε/(Q:ℝ))≤-Real.log M := by
  have hM0:0<M := by linarith
  let ε:ℝ:=1/(10*M)
  let Q:ℕ:=⌈60*M⌉₊
  have hε:0<ε := by dsimp [ε]; positivity
  have hQ:0<Q := Nat.ceil_pos.mpr (by positivity)
  have hQr:(0:ℝ)<Q := by exact_mod_cast hQ
  have hQ1:(1:ℝ)≤Q := by exact_mod_cast hQ
  have hQl:60*M≤(Q:ℝ) := Nat.le_ceil _
  have hε1:2*Real.pi*ε≤1 := by
    dsimp [ε]
    rw [← mul_div_assoc,mul_one]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<10*M)).mpr
    nlinarith [Real.pi_lt_four]
  have hε2:M*ε≤1 := by
    dsimp [ε]
    rw [← mul_div_assoc,mul_one]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<10*M)).mpr
    nlinarith
  have hQε:6/(Q:ℝ)≤ε := by
    calc
      _ ≤ 6/(60*M) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hQl
      _ = ε := by dsimp [ε]; field_simp; ring
  have hC:0<4*ε/(Q:ℝ) := by positivity
  have hCM:4*ε/(Q:ℝ)≤1/M := by
    calc
      _ ≤ 4*ε := div_le_self (by positivity) hQ1
      _ ≤ 1/M := by
        dsimp [ε]
        rw [← mul_div_assoc,mul_one]
        apply (div_le_div_iff₀ (show 0<10*M by positivity) hM0).mpr
        nlinarith
  have hlog:=Real.log_le_log hC hCM
  rw [one_div,Real.log_inv] at hlog
  exact ⟨ε,Q,hε,hQ,hε1,hε2,hQε,hlog⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EntropyEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma integral_log_growth_of_deficit (k:ℝ) (hk:0≤k)
    (hdef:∀n:ℕ,0<n → meanDeficit k n<(1/8:ℝ)) (n:ℕ) :
    (7/8:ℝ)*(n:ℝ)*Real.log (growthBase k)≤∫z,Real.log ‖torusSegmentTransfer k z 0 n‖ ∂area := by
  by_cases hn:0<n
  · have hnp:(0:ℝ)<n := by exact_mod_cast hn
    have hl:=log_growthBase_pos k hk
    have hI:(7/8:ℝ)*(n:ℝ)≤∫z,productDistance k z 0 (n:ℤ) ∂area := by
      have hd:=hdef n hn
      unfold meanDeficit at hd
      have hh:(7/8:ℝ)<(∫z,productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ) := by linarith
      exact ((lt_div_iff₀ hnp).mp hh).le
    have he:(∫z,productDistance k z 0 (n:ℤ) ∂area)=
        (∫z,Real.log ‖torusSegmentTransfer k z 0 n‖ ∂area)/Real.log (growthBase k) := by
      have hf:(fun z=>productDistance k z 0 (n:ℤ))=(fun z=>Real.log ‖torusSegmentTransfer k z 0 n‖/Real.log (growthBase k)) := by
        funext z
        simpa only [zero_add] using productDistance_forward k z 0 n
      rw [hf,integral_div]
    rw [he] at hI
    exact (le_div_iff₀ hl).mp hI
  · have he:n=0 := by omega
    subst n
    simp only [Nat.cast_zero,mul_zero,zero_mul]
    exact integral_nonneg fun z=>Real.log_nonneg (torusSegmentTransfer_norm_bounds k hk z 0 0).1

lemma positive_entropy_of_uniform_deficit (k:ℝ) (hk:0≤k) (hM:(1000:ℝ)^4≤growthBase k)
    (hdef:∀n:ℕ,0<n → meanDeficit k n<(1/8:ℝ)) : 0 < metricEntropy area (standardMap k) := by
  obtain ⟨N,hN,hN2,hNR⟩:=entropy_subdivision_parameters (growthBase k) hM
  obtain ⟨ε,Q,hε,hQ,hε1,hε2,hQε,hQC⟩:=entropy_grid_parameters (growthBase k) (by linarith [growthBase_ge_four k hk])
  have hlog:=log_growthBase_pos k hk
  have hblock (n:ℕ) : ((n:ℝ)+1)*(Real.log (growthBase k)/8)≤
      blockEntropy area (torusStep k) (gridPartition Q hQ) (n+1) := by
    have h:=grid_block_entropy_growth k ε hk hε hε1 hε2 Q N hQ hQε hN hN2 n
    have hg:=integral_log_growth_of_deficit k hk hdef n
    have hr:=mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg n : (0:ℝ)≤n)
    nlinarith
  have hp:ENNReal.ofReal (Real.log (growthBase k)/8)≤
      partitionEntropy area (torusStep k) (gridPartition Q hQ) := by
    apply le_iInf
    intro n
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ (show (0:ℝ)<(n:ℝ)+1 by positivity)).mpr
    nlinarith [hblock n]
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity))
    (hp.trans (metricEntropy_standardMap_ge_partition k (gridPartition Q hQ)))

theorem main_entropy : MainObligation := by
  obtain ⟨K,hK,hdef⟩:=eventually_meanDeficit_small_q3 (1/8:ℝ) (by norm_num)
  refine ⟨max K ((1000:ℝ)^4),lt_of_lt_of_le hK (le_max_left _ _),?_⟩
  intro k hk
  have hKk:K≤k := (le_max_left K ((1000:ℝ)^4)).trans hk
  have hlarge:(1000:ℝ)^4≤k := (le_max_right K ((1000:ℝ)^4)).trans hk
  have hk0:0≤k := le_of_lt (hK.trans_le hKk)
  apply positive_entropy_of_uniform_deficit k hk0
  · unfold growthBase
    nlinarith [Real.pi_gt_three]
  · exact hdef k hKk
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_Lyapunov_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardDerivativeProduct_zero (k : ℝ) (z : Torus) :
    standardDerivativeProduct k z 0 = ContinuousLinearMap.id ℝ ℂ := rfl

attribute [local instance] OAI.StandardMapEntropy.realTangentCompTriple
lemma standardDerivativeProduct_succ (k : ℝ) (z : Torus) (n : ℕ) :
    standardDerivativeProduct k z (n + 1) =
      (standardDerivative k ((standardMap k)^[n] z)).comp
        (standardDerivativeProduct k z n) := rfl

end StandardMapEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_Lyapunov_Subadditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace BoundedSubadditive

variable {X : Type*}

lemma excess_nonneg (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    0 ≤ excess T h δ n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma excess_succ_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    excess T h δ n x ≤ excess T h δ (n + 1) x := by
  induction n generalizing x with
  | zero => exact excess_nonneg T h δ 1 x
  | succ n ih =>
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma excess_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (x : X) :
    Monotone (fun n => excess T h δ n x) :=
  monotone_nat_of_le_succ (fun n => excess_succ_mono T h δ n x)

lemma sum_sub_le_excess (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T h n x - (n : ℝ) * δ ≤ excess T h δ n x := by
  induction n generalizing x with
  | zero => simp [birkhoffSum, excess]
  | succ n ih =>
    rw [birkhoffSum_succ']
    have hm : h x - δ + excess T h δ n (T x) ≤ excess T h δ (n + 1) x :=
      le_max_right _ _
    have hi := ih (T x)
    push_cast
    linarith

lemma excess_account (T : X → X) (h : X → ℝ) (δ : ℝ)
    (hh : ∀ x, 0 ≤ h x) (n : ℕ) (x : X) :
    (if 0 < excess T h δ (n + 1) x then δ else 0) ≤
      h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x := by
  split_ifs with hp
  · have he : excess T h δ (n + 1) x = h x - δ + excess T h δ n (T x) := by
      apply max_eq_right
      change 0 < max 0 (h x - δ + excess T h δ n (T x)) at hp
      exact (lt_max_iff.mp hp).resolve_left (lt_irrefl 0) |>.le
    rw [he]
    linarith [excess_succ_mono T h δ n (T x)]
  · have he : excess T h δ (n + 1) x = 0 :=
      le_antisymm (not_lt.mp hp) (excess_nonneg T h δ _ x)
    rw [he]
    linarith [hh x, excess_nonneg T h δ (n + 1) (T x)]

section Measure
variable [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {T : X → X} {h : X → ℝ} {δ : ℝ}

lemma measurable_excess (hT : Measurable T) (hh : Measurable h) (n : ℕ) :
    Measurable (excess T h δ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max ((hh.sub measurable_const).add (ih.comp hT))

lemma integrable_excess (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) (n : ℕ) :
    Integrable (excess T h δ n) μ := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (integrable_const (0 : ℝ)).sup
      ((hh.sub (integrable_const δ)).add (hT.integrable_comp_of_integrable ih))

omit [IsFiniteMeasure μ] in
lemma integral_comp (hT : MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : AEStronglyMeasurable g μ) : (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hg' : AEStronglyMeasurable g (Measure.map T μ) := by rwa [hT.map_eq]
  simpa only [hT.map_eq] using (integral_map hT.measurable.aemeasurable hg').symm

lemma excess_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) (n : ℕ) :
    μ {x | 0 < excess T h δ n x} ≤ ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  cases n with
  | zero => simp [excess]
  | succ n =>
    let s : Set X := {x | 0 < excess T h δ (n + 1) x}
    have hs : MeasurableSet s := measurableSet_lt measurable_const
      (measurable_excess hT.measurable hm _)
    have he := integrable_excess (δ := δ) hT hi (n + 1)
    have heT : Integrable (fun x => excess T h δ (n + 1) (T x)) μ :=
      hT.integrable_comp_of_integrable he
    have hb : (∫ x, s.indicator (fun _ => δ) x ∂μ) ≤
        ∫ x, h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x ∂μ := by
      apply integral_mono ((integrable_const δ).indicator hs)
        ((hi.add heT).sub he)
      intro x
      simpa only [Set.indicator, s, Set.mem_ofPred_eq, Pi.sub_apply, Pi.add_apply, Function.comp_apply] using excess_account T h δ h0 n x
    have hsub := integral_sub (hi.add heT) he
    have hadd := integral_add hi heT
    simp only [Pi.add_apply] at hsub hadd
    rw [integral_indicator_const δ hs, hsub, hadd,
      integral_comp hT he.aestronglyMeasurable] at hb
    have hb' : μ.real s ≤ (∫ x, h x ∂μ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      simpa only [smul_eq_mul, add_sub_cancel_right] using hb
    calc
      μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb'

lemma maximal_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) :
    μ {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ≤
      ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  have hsub : {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ⊆
      ⋃ n : ℕ, {x | 0 < excess T h δ n x} := by
    rintro x ⟨n, hn⟩
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    exact lt_of_lt_of_le (sub_pos.mpr hn) (sum_sub_le_excess T h δ n x)
  refine (measure_mono hsub).trans ?_
  have hm' : Monotone (fun n : ℕ => {x | 0 < excess T h δ n x}) := by
    intro m n hmn x hx
    exact lt_of_lt_of_le hx (excess_mono T h δ x hmn)
  rw [hm'.measure_iUnion]
  exact iSup_le (fun n => excess_measure_bound hT hm hi h0 hδ n)

end Measure

namespace Cocycle
variable [MeasurableSpace X] {T : X → X} (f : Cocycle X T)

lemma average_bounds (n : ℕ) (x : X) : 0 ≤ f.average n x ∧ f.average n x ≤ 1 := by
  refine ⟨div_nonneg (f.nonneg n x) (Nat.cast_nonneg n), ?_⟩
  by_cases hn : n = 0
  · simp [average, hn]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr (f.le_time n x)

lemma average_bdd_above (x : X) : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨1, fun n => (f.average_bounds n x).2⟩

lemma average_bdd_below (x : X) : IsBoundedUnder (· ≥ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨0, fun n => (f.average_bounds n x).1⟩

lemma lowerRate_bounds (x : X) : 0 ≤ f.lowerRate x ∧ f.lowerRate x ≤ 1 := by
  constructor
  · exact le_liminf_of_le (f.average_bdd_above x).isCoboundedUnder_ge
      (Eventually.of_forall fun n => (f.average_bounds n x).1)
  · have hh := liminf_le_liminf (Eventually.of_forall fun n => (f.average_bounds n x).2)
      (f.average_bdd_below x) (isBoundedUnder_const.isCoboundedUnder_ge)
    simpa only [liminf_const, lowerRate] using hh

lemma measurable_average (n : ℕ) : Measurable (f.average n) :=
  (f.measurable n).div_const _

lemma measurable_lowerRate : Measurable f.lowerRate :=
  Measurable.liminf (fun n => f.measurable_average n)

lemma average_shift_bound (n : ℕ) (x : X) :
    |f.average n (T x) - f.average n x| ≤ 2 / (n : ℝ) := by
  rw [average, average, ← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right (f.shift_bound n x) (Nat.cast_nonneg n)

lemma lowerRate_shift (x : X) : f.lowerRate (T x) = f.lowerRate x := by
  have hc : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have haux (a b : X) (hab : ∀ n, f.average n a - f.average n b ≤ 2 / (n : ℝ)) :
      f.lowerRate a ≤ f.lowerRate b := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have he : ∀ᶠ n : ℕ in atTop, f.average n a ≤ f.average n b + ε := by
      filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
      linarith [hab n]
    have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n b + ε) :=
      isBoundedUnder_of ⟨1 + ε, fun n => add_le_add (f.average_bounds n b).2 le_rfl⟩
    have hh := liminf_le_liminf he (f.average_bdd_below a) hb.isCoboundedUnder_ge
    rw [liminf_add_const atTop (fun n => f.average n b) ε
      (f.average_bdd_above b).isCoboundedUnder_ge (f.average_bdd_below b)] at hh
    exact hh
  apply le_antisymm
  · exact haux (T x) x (fun n => (abs_le.mp (f.average_shift_bound n x)).2)
  · apply haux x (T x)
    intro n
    have hh := (abs_le.mp (f.average_shift_bound n x)).1
    linarith

lemma lowerRate_iterate (n : ℕ) (x : X) : f.lowerRate (T^[n] x) = f.lowerRate x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', f.lowerRate_shift, ih]

lemma measurableSet_badSet (ε : ℝ) (N : ℕ) : MeasurableSet (f.badSet ε N) := by
  apply MeasurableSet.compl
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro n hn
  exact measurableSet_le (f.measurable n)
    (measurable_const.mul (f.measurable_lowerRate.add_const ε))

lemma measurable_badObservation (ε : ℝ) (N : ℕ) : Measurable (f.badObservation ε N) :=
  measurable_const.indicator (f.measurableSet_badSet ε N)

lemma badObservation_bounds (ε : ℝ) (N : ℕ) (x : X) :
    0 ≤ f.badObservation ε N x ∧ f.badObservation ε N x ≤ 1 := by
  classical
  by_cases hx : x ∈ f.badSet ε N <;> simp [badObservation, hx]

lemma exists_good_block (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) := by
  have hh : ∃ᶠ n : ℕ in atTop, f.average n x < f.lowerRate x + ε :=
    frequently_lt_of_liminf_lt (f.average_bdd_above x).isCoboundedUnder_ge (lt_add_of_pos_right _ hε)
  obtain ⟨n, hn, he⟩ := frequently_atTop.mp hh 1
  have hn' : 0 < n := by omega
  refine ⟨n, hn', ?_⟩
  have hi := (div_lt_iff₀ (Nat.cast_pos.mpr hn')).mp he
  nlinarith

lemma badObservation_tendsto_zero (x : X) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => f.badObservation ε N x) atTop (𝓝 0) := by
  obtain ⟨n, hn, hg⟩ := f.exists_good_block x ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  symm
  apply Set.indicator_of_notMem
  simp only [badSet, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_not]
  exact ⟨n, ⟨hn, hN⟩, hg⟩

lemma birkhoff_bad_nonneg (ε : ℝ) (N n : ℕ) (x : X) :
    0 ≤ birkhoffSum T (f.badObservation ε N) n x := by
  exact Finset.sum_nonneg fun i hi => (f.badObservation_bounds ε N (T^[i] x)).1

lemma block_bound (ε : ℝ) (hε : 0 ≤ ε) (N n : ℕ) (x : X) :
    f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) +
      birkhoffSum T (f.badObservation ε N) n x + (N : ℝ) := by
  classical
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have ha : 0 ≤ f.lowerRate x + ε := add_nonneg (f.lowerRate_bounds x).1 hε
    by_cases hn : n ≤ N
    · have hcast : (n : ℝ) ≤ N := by exact_mod_cast hn
      have hp := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ha
      linarith [f.le_time n x, f.birkhoff_bad_nonneg ε N n x]
    · by_cases hx : x ∈ f.badSet ε N
      · have hn0 : 1 ≤ n := by omega
        have he : 1 + (n - 1) = n := by omega
        have hs := f.subadd 1 (n - 1) x
        simp only [he, Function.iterate_one] at hs
        have hi := ih (n - 1) (by omega) (T x)
        rw [f.lowerRate_shift] at hi
        rw [Nat.cast_sub hn0, Nat.cast_one, sub_mul, one_mul] at hi
        have hb : f.badObservation ε N x = 1 := by simp [badObservation, hx]
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            1 + birkhoffSum T (f.badObservation ε N) (n - 1) (T x) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [birkhoffSum_succ', hb]
        rw [hsum]
        have h1 := f.le_time 1 x
        norm_num only [Nat.cast_one] at h1
        linarith
      · have hg : x ∈ ⋃ m ∈ Set.Ioc 0 N,
            {y | f.value m y ≤ (m : ℝ) * (f.lowerRate y + ε)} := not_not.mp hx
        obtain ⟨m, hgm⟩ := mem_iUnion.mp hg
        obtain ⟨hm, hfm⟩ := mem_iUnion.mp hgm
        have hmn : m ≤ n := by have := hm.2; omega
        have he : m + (n - m) = n := Nat.add_sub_of_le hmn
        have hs := f.subadd m (n - m) x
        rw [he] at hs
        have hi := ih (n - m) (by have := hm.1; omega) (T^[m] x)
        rw [f.lowerRate_iterate, Nat.cast_sub hmn, sub_mul] at hi
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            birkhoffSum T (f.badObservation ε N) m x +
              birkhoffSum T (f.badObservation ε N) (n - m) (T^[m] x) := by
          simpa only [he] using birkhoffSum_add T (f.badObservation ε N) m (n - m) x
        rw [hsum]
        have hp := f.birkhoff_bad_nonneg ε N m x
        change f.value m x ≤ (m : ℝ) * (f.lowerRate x + ε) at hfm
        linarith

lemma upperRate_le_of_bad_averages (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (δ : ℝ) (x : X)
    (hb : ∀ n, birkhoffSum T (f.badObservation ε N) n x ≤ (n : ℝ) * δ) :
    f.upperRate x ≤ f.lowerRate x + ε + δ := by
  apply le_of_forall_pos_le_add
  intro γ hγ
  have hc : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply limsup_le_of_le (f.average_bdd_below x).isCoboundedUnder_le
  filter_upwards [hc.eventually (gt_mem_nhds hγ), eventually_gt_atTop 0] with n hsmall hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hN := (div_lt_iff₀ hn').mp hsmall
  apply (div_le_iff₀ hn').mpr
  have hB := f.block_bound ε hε N n x
  have hbad := hb n
  nlinarith

section Measure
variable {μ : Measure X} [IsFiniteMeasure μ]

lemma integrable_badObservation (ε : ℝ) (N : ℕ) :
    Integrable (f.badObservation ε N) μ :=
  (integrable_const (1 : ℝ)).indicator (f.measurableSet_badSet ε N)

lemma integral_badObservation_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => ∫ x, f.badObservation ε N x ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1 : ℝ))
    (fun N => (f.measurable_badObservation ε N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.badObservation_bounds ε N x).1]
      exact (f.badObservation_bounds ε N x).2)
    (Eventually.of_forall fun x => f.badObservation_tendsto_zero x ε hε)
  simpa only [integral_zero] using hh

lemma ae_upperRate_le_add (hT : MeasurePreserving T μ μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, f.upperRate x ≤ f.lowerRate x + 2 * ε := by
  let E : Set X := {x | f.lowerRate x + 2 * ε < f.upperRate x}
  have hbound (N : ℕ) : μ E ≤
      ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε) := by
    have hsub : E ⊆ {x | ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x} := by
      intro x hx
      by_contra hn
      change ¬ ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x at hn
      push Not at hn
      have hh := f.upperRate_le_of_bad_averages ε hε.le N ε x hn
      change f.lowerRate x + 2 * ε < f.upperRate x at hx
      linarith
    exact (measure_mono hsub).trans
      (maximal_measure_bound hT (f.measurable_badObservation ε N)
        (f.integrable_badObservation ε N) (fun x => (f.badObservation_bounds ε N x).1) hε)
  have hc : Tendsto (fun N => ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε))
      atTop (𝓝 0) := by
    have hh := (f.integral_badObservation_tendsto_zero (μ := μ) ε hε).div_const ε
    simpa only [Function.comp_def, zero_div, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hzero : μ E = 0 := le_antisymm (ge_of_tendsto' hc hbound) zero_le
  simpa only [ae_iff, not_le] using hzero

theorem ae_tendsto_average (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f.average n x) atTop (𝓝 (f.lowerRate x)) := by
  have ha : ∀ᵐ x ∂μ, ∀ j : ℕ, f.upperRate x ≤ f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro j
    exact f.ae_upperRate_le_add hT _ (by positivity)
  filter_upwards [ha] with x hx
  have hc : Tendsto (fun j : ℕ => f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)))
      atTop (𝓝 (f.lowerRate x)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hu : f.upperRate x ≤ f.lowerRate x := ge_of_tendsto' hc hx
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hu
    (f.average_bdd_above x) (f.average_bdd_below x)

lemma integrable_lowerRate : Integrable f.lowerRate μ :=
  (integrable_const (1 : ℝ)).mono' f.measurable_lowerRate.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.lowerRate_bounds x).1]
      exact (f.lowerRate_bounds x).2)

theorem tendsto_integral_average (hT : MeasurePreserving T μ μ) :
    Tendsto (fun n => ∫ x, f.average n x ∂μ) atTop (𝓝 (∫ x, f.lowerRate x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ))
    (fun n => (f.measurable_average n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.average_bounds n x).1]
      exact (f.average_bounds n x).2)
    (f.ae_tendsto_average hT)

end Measure
end Cocycle
end BoundedSubadditive

namespace StandardMapEntropy
open BoundedSubadditive

lemma lognorm_average_eq (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    Real.log ‖torusSegmentTransfer k z 0 n‖ / (n : ℝ) =
      Real.log (growthBase k) * (transferCocycle k hk).average n z := by
  change _ = Real.log (growthBase k) * (productDistance k z 0 (n : ℤ) / (n : ℝ))
  have hf : productDistance k z 0 (n : ℤ) =
      Real.log ‖torusSegmentTransfer k z 0 n‖ / Real.log (growthBase k) := by
    simpa only [zero_add] using productDistance_forward k z 0 n
  rw [hf]
  have hlog := (log_growthBase_pos k hk).ne'
  calc
    _ = (Real.log (growthBase k) * (Real.log ‖torusSegmentTransfer k z 0 n‖ /
        Real.log (growthBase k))) / (n : ℝ) := by rw [mul_div_cancel₀ _ hlog]
    _ = _ := by ring

lemma transferLyapunov_limit (k : ℝ) (hk : 0 ≤ k) :
    TransferLimit k (transferLyapunov k hk) := by
  let f := transferCocycle k hk
  refine ⟨measurable_const.mul f.measurable_lowerRate,
    f.integrable_lowerRate.const_mul _, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (log_growthBase_pos k hk).le (f.lowerRate_bounds z).1
  · intro z
    exact congrArg (fun a => Real.log (growthBase k) * a) (f.lowerRate_shift z)
  · filter_upwards [f.ae_tendsto_average (measurePreserving_torusStep k)] with z hz
    have hh : Tendsto (fun n => Real.log (growthBase k) * f.average n z) atTop
        (𝓝 (Real.log (growthBase k) * f.lowerRate z)) := tendsto_const_nhds.mul hz
    simpa only [transferLyapunov, f, ← lognorm_average_eq] using hh

lemma integral_lowerRate_of_deficit (k : ℝ) (hk : 0 ≤ k) (η : ℝ)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < η) :
    1 - η ≤ ∫ z, (transferCocycle k hk).lowerRate z ∂area := by
  have hc := (transferCocycle k hk).tendsto_integral_average (measurePreserving_torusStep k)
  apply ge_of_tendsto hc
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hh := hdef n hn
  have he : (∫ z, (transferCocycle k hk).average n z ∂area) =
      (∫ z, productDistance k z 0 (n : ℤ) ∂area) / (n : ℝ) := by
    change (∫ z, productDistance k z 0 (n : ℤ) / (n : ℝ) ∂area) = _
    exact integral_div (n : ℝ) _
  rw [he]
  unfold meanDeficit at hh
  linarith

lemma positive_transferLyapunov_of_deficit (k : ℝ) (hk : 0 ≤ k)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < (1 / 8 : ℝ)) :
    0 < area {z | 0 < transferLyapunov k hk z} := by
  have hl := integral_lowerRate_of_deficit k hk (1 / 8) hdef
  have hI : 0 < ∫ z, transferLyapunov k hk z ∂area := by
    unfold transferLyapunov
    rw [integral_const_mul]
    exact mul_pos (log_growthBase_pos k hk) (by linarith)
  by_contra hh
  have hz : area {z | 0 < transferLyapunov k hk z} = 0 :=
    le_antisymm (not_lt.mp hh) zero_le
  have hae : ∀ᵐ z ∂area, transferLyapunov k hk z = 0 := by
    have hnone : ∀ᵐ z ∂area, ¬ 0 < transferLyapunov k hk z := by
      simpa only [ae_iff, not_not] using hz
    filter_upwards [hnone] with z hnot
    exact le_antisymm (not_lt.mp hnot) ((transferLyapunov_limit k hk).2.2.1 z)
  have hi : (∫ z, transferLyapunov k hk z ∂area) = 0 := by
    rw [integral_congr_ae hae, integral_zero]
  linarith

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_Lyapunov_DerivativeGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma tangentCoordinates_wedge (z w : ℂ) :
    wedge (tangentCoordinates z) (tangentCoordinates w) = -wedge z w := by
  simp only [wedge, tangentCoordinates_re, tangentCoordinates_im]
  ring

lemma tangentCoordinates_norm_le : ‖tangentCoordinates‖ ≤ 3 := by
  apply tangentCoordinates.opNorm_le_bound (by norm_num)
  intro z
  have hr := Complex.abs_re_le_norm z
  have hi := Complex.abs_im_le_norm z
  calc
    ‖tangentCoordinates z‖ ≤ |z.re| + |z.re-z.im| := by
      simpa only [tangentCoordinates_re, tangentCoordinates_im]
        using Complex.norm_le_abs_re_add_abs_im (tangentCoordinates z)
    _ ≤ |z.re| + (|z.re|+|z.im|) := add_le_add le_rfl (abs_sub _ _)
    _ ≤ 3*‖z‖ := by linarith

lemma standardDerivative_area (k : ℝ) (z : Torus) :
    PlaneAreaPreserving (standardDerivative k z) := by
  intro v w
  simp only [standardDerivative, ContinuousLinearMap.comp_apply, tangentCoordinates_wedge]
  rw [transferStep_area _ _ _, tangentCoordinates_wedge, neg_neg]

lemma standardDerivativeProduct_area (k : ℝ) (z : Torus) (n : ℕ) :
    PlaneAreaPreserving (standardDerivativeProduct k z n) := by
  induction n with
  | zero => intro v w; rfl
  | succ n ih => exact (standardDerivative_area k _).comp ih

lemma standardDerivativeProduct_norm_ge_one (k : ℝ) (z : Torus) (n : ℕ) :
    1 ≤ ‖standardDerivativeProduct k z n‖ :=
  (standardDerivativeProduct_area k z n).singular_pair.choose_spec.2.2.2.2

lemma recurrenceCoordinates_iterate (k : ℝ) (n : ℕ) (z : Torus) :
    recurrenceCoordinates ((standardMap k)^[n] z) =
      (torusStep k)^[n] (recurrenceCoordinates z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', standardMap_conjugacy, ih]
    rfl

lemma standardDerivativeProduct_conjugate (k : ℝ) (z : Torus) (n : ℕ) :
    standardDerivativeProduct k z n = tangentCoordinates.comp
      ((torusSegmentTransfer k (recurrenceCoordinates z) 0 n).comp tangentCoordinates) := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro w
    simpa only [standardDerivativeProduct_zero, torusSegmentTransfer, transferProduct,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      (tangentCoordinates_involutive w).symm
  | succ n ih =>
    have hcoeff : torusSegmentCoefficient k (recurrenceCoordinates z) 0 (n+1) =
        torusPotential k ((standardMap k)^[n] z).1 := by
      unfold torusSegmentCoefficient
      simp only [Nat.cast_add, Nat.cast_one, zero_add, add_sub_cancel_right]
      rw [torusIter_nat_apply, ← recurrenceCoordinates_iterate]
      rfl
    apply ContinuousLinearMap.ext
    intro w
    simp only [standardDerivativeProduct_succ, ih, standardDerivative, torusSegmentTransfer,
      transferProduct, ContinuousLinearMap.comp_apply, tangentCoordinates_involutive, hcoeff]

lemma conjugate_norm_le (A : ℂ →L[ℝ] ℂ) :
    ‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ ≤ 9*‖A‖ := by
  calc
    _ ≤ ‖tangentCoordinates‖ * (‖A‖ * ‖tangentCoordinates‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 3 * (‖A‖ * 3) := by gcongr <;> exact tangentCoordinates_norm_le
    _ = _ := by ring

lemma conjugate_norm_lower (A : ℂ →L[ℝ] ℂ) :
    ‖A‖ ≤ 9*‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ := by
  convert conjugate_norm_le (tangentCoordinates.comp (A.comp tangentCoordinates)) using 1
  congr 1
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, tangentCoordinates_involutive]

lemma derivative_log_difference_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    |Real.log ‖standardDerivativeProduct k z n‖-
      Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖| ≤ Real.log 9 := by
  have hA : 0 < ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖ :=
    lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk _ _ _).1
  have hB : 0 < ‖standardDerivativeProduct k z n‖ :=
    lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k z n)
  have h₁ := conjugate_norm_le (torusSegmentTransfer k (recurrenceCoordinates z) 0 n)
  have h₂ := conjugate_norm_lower (torusSegmentTransfer k (recurrenceCoordinates z) 0 n)
  rw [← standardDerivativeProduct_conjugate] at h₁ h₂
  have hlog₁ := Real.log_le_log hB h₁
  have hlog₂ := Real.log_le_log hA h₂
  rw [Real.log_mul (by norm_num) hA.ne'] at hlog₁
  rw [Real.log_mul (by norm_num) hB.ne'] at hlog₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma derivative_rate_of_transfer_rate (k : ℝ) (hk : 0 ≤ k) (z : Torus) (l : ℝ)
    (hl : Tendsto
      (fun n : ℕ => Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖ / (n : ℝ))
      atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 l) := by
  have hd : Tendsto (fun n : ℕ =>
      (Real.log ‖standardDerivativeProduct k z n‖ -
        Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖) / (n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log 9 / (n : ℝ)) atTop (𝓝 0))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (derivative_log_difference_bound k hk z n) (Nat.cast_nonneg _)
  have hh := hd.add hl
  simpa only [sub_div, sub_add_cancel, zero_add] using hh

lemma measurable_recurrenceCoordinates : Measurable recurrenceCoordinates :=
  measurable_fst.prodMk (measurable_fst.sub measurable_snd)

lemma measurable_standardLyapunov (k : ℝ) (hk : 0 ≤ k) :
    Measurable (standardLyapunov k hk) :=
  (transferLyapunov_limit k hk).1.comp measurable_recurrenceCoordinates

lemma integrable_standardLyapunov (k : ℝ) (hk : 0 ≤ k) :
    Integrable (standardLyapunov k hk) area :=
  measurePreserving_recurrenceCoordinates.integrable_comp_of_integrable
    (transferLyapunov_limit k hk).2.1

lemma standardLyapunov_nonneg (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    0 ≤ standardLyapunov k hk z := (transferLyapunov_limit k hk).2.2.1 _

lemma standardLyapunov_invariant (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    standardLyapunov k hk (standardMap k z) = standardLyapunov k hk z := by
  unfold standardLyapunov
  rw [standardMap_conjugacy]
  exact (transferLyapunov_limit k hk).2.2.2.1 _

lemma ae_standardLyapunov_rate (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 (standardLyapunov k hk z)) := by
  have hh := measurePreserving_recurrenceCoordinates.quasiMeasurePreserving.ae
    (transferLyapunov_limit k hk).2.2.2.2
  filter_upwards [hh] with z hz
  exact derivative_rate_of_transfer_rate k hk z _ hz

lemma positive_standardLyapunov_of_deficit (k : ℝ) (hk : 0 ≤ k)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < (1/8 : ℝ)) :
    0 < area {z | 0 < standardLyapunov k hk z} := by
  have hm : MeasurableSet {z | 0 < transferLyapunov k hk z} :=
    measurableSet_lt measurable_const (transferLyapunov_limit k hk).1
  have he := measurePreserving_recurrenceCoordinates.measure_preimage hm.nullMeasurableSet
  change 0 < area (recurrenceCoordinates ⁻¹' {z | 0 < transferLyapunov k hk z})
  rw [he]
  exact positive_transferLyapunov_of_deficit k hk hdef

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardDerivative_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    ‖standardDerivative k z‖ ≤ 9*growthBase k := by
  calc
    _ ≤ 9*‖transferStep (torusPotential k z.1)‖ := conjugate_norm_le _
    _ ≤ 9*(|torusPotential k z.1|+1) :=
      mul_le_mul_of_nonneg_left (transferStep_norm _) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (torusPotential_bound k hk z.1) (by norm_num)

lemma standardDerivativeProduct_step_lower (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) (v : ℂ) :
    ‖standardDerivativeProduct k z n v‖ ≤
      (9*growthBase k)*‖standardDerivativeProduct k z (n+1) v‖ := by
  exact ((standardDerivative_area k ((standardMap k)^[n] z)).norm_lower
    (standardDerivativeProduct k z n v)).trans
    (mul_le_mul_of_nonneg_right (standardDerivative_norm_bound k hk _) (norm_nonneg _))

end StandardMapEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_Lyapunov_PlaneLyapunov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace PlaneLyapunov

variable (A : ℕ → ℂ →L[ℝ] ℂ)

lemma norm_pos (hA : ∀ n, PlaneAreaPreserving (A n)) (n : ℕ) : 0 < ‖A n‖ :=
  lt_of_lt_of_le zero_lt_one (hA n).singular_pair.choose_spec.2.2.2.2

lemma image_norm_pos (hA : ∀ n, PlaneAreaPreserving (A n)) {v : ℂ} (hv : v ≠ 0) (n : ℕ) :
    0 < ‖A n v‖ := by
  have hh := (hA n).norm_lower v
  by_contra h
  have hz : ‖A n v‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
  rw [hz, mul_zero] at hh
  exact (norm_pos_iff.mpr hv).not_ge hh

lemma eventual_exp_lower (hA : ∀ n, PlaneAreaPreserving (A n)) {l α : ℝ}
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) (hα : α < l) :
    ∀ᶠ n : ℕ in atTop, Real.exp (α*(n : ℝ)) ≤ ‖A n‖ := by
  filter_upwards [(tendsto_order.mp hl).1 α hα, eventually_gt_atTop 0] with n hn hn0
  have hp : (0 : ℝ) < n := by exact_mod_cast hn0
  calc
    _ ≤ Real.exp (Real.log ‖A n‖) := Real.exp_le_exp.mpr ((le_div_iff₀ hp).mp hn.le)
    _ = _ := Real.exp_log (norm_pos A hA n)

lemma tailConstant_pos {M α : ℝ} (hM : 0 < M) (hα : 0 < α) : 0 < tailConstant M α := by
  unfold tailConstant
  apply div_pos (mul_pos hM (Real.exp_pos _))
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

lemma stable_error_exp_bound (D : ℕ → ℝ) (M α : ℝ) (hM : 0 ≤ M) (hα : 0 < α)
    (n B : ℕ) (_hnB : n ≤ B)
    (hD : ∀ i, n ≤ i → i ≤ B → Real.exp (α*(i : ℝ)) ≤ D i) :
    (∑ i ∈ Finset.Ico n B, M/(D i*D (i+1))) ≤
      tailConstant M α * Real.exp (-2*α*(n : ℝ)) := by
  have hq0 : 0 ≤ Real.exp (-2*α) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2*α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he (i : ℕ) (hi : i ∈ Finset.Ico n B) :
      M/(D i*D (i+1)) ≤ M*Real.exp (-α)*(Real.exp (-2*α))^i := by
    have hi0 := (Finset.mem_Ico.mp hi).1
    have hiB := (Finset.mem_Ico.mp hi).2
    have hl := hD i hi0 hiB.le
    have hr := hD (i+1) (by omega) (by omega)
    have hp := mul_le_mul hl hr (Real.exp_pos _).le ((Real.exp_pos _).trans_le hl).le
    calc
      _ ≤ M/(Real.exp (α*(i : ℝ))*Real.exp (α*((i+1 : ℕ) : ℝ))) :=
        div_le_div_of_nonneg_left hM (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hp
      _ = _ := by
        rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_nat_mul]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
  calc
    _ ≤ ∑ i ∈ Finset.Ico n B, M*Real.exp (-α)*(Real.exp (-2*α))^i :=
      Finset.sum_le_sum he
    _ = (M*Real.exp (-α)) * ∑ i ∈ Finset.Ico n B, (Real.exp (-2*α))^i := by
      rw [Finset.mul_sum]
    _ ≤ (M*Real.exp (-α)) * ((Real.exp (-2*α))^n/(1-Real.exp (-2*α))) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul]
      unfold tailConstant
      rw [show (n : ℝ)*(-2*α) = -2*α*(n : ℝ) by ring]
      ring

lemma inverse_bound_by_exp (D α : ℝ) (n : ℕ) (hD : Real.exp (α*(n : ℝ)) ≤ D) :
    D⁻¹ ≤ D*Real.exp (-2*α*(n : ℝ)) := by
  have hp : 0 < D := (Real.exp_pos _).trans_le hD
  calc
    _ ≤ (Real.exp (α*(n : ℝ)))⁻¹ := (inv_le_inv₀ hp (Real.exp_pos _)).mpr hD
    _ = Real.exp (α*(n : ℝ))*Real.exp (-2*α*(n : ℝ)) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le

lemma exists_stable_bound (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0 < M)
    (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) :
    ∃ s : ℂ, ‖s‖=1 ∧ ∀ α : ℝ, 0 < α → α < l →
      ∀ᶠ n : ℕ in atTop, ‖A n s‖ ≤
        ‖A n‖*(1+tailConstant M α)*Real.exp (-2*α*(n : ℝ)) := by
  classical
  choose a hau ham hao has hnorm using fun n => (hA n).singular_pair
  have hu (n : ℕ) : quarterTurn (a n) ∈ sphere (0 : ℂ) 1 := by
    simp only [mem_sphere, dist_zero_right, norm_quarterTurn, hau]
  obtain ⟨s, hs, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hu
  have hsunit : ‖s‖=1 := by simpa only [mem_sphere, dist_zero_right] using hs
  refine ⟨s, hsunit, ?_⟩
  intro α hα hαl
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventual_exp_lower A hA hl hαl)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hb : ‖A n s‖ ≤ ‖A n‖⁻¹ + ‖A n‖ *
      (tailConstant M α * Real.exp (-2*α*(n : ℝ))) := by
    apply le_of_tendsto ((A n).continuous.norm.tendsto s |>.comp hlim)
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop n)] with j hj
    have hh := stable_prefix_finite_bound A a (fun i => ‖A i‖) M n (φ j) hn1 hj
      (fun i _ _ => hA i) (fun i _ _ => hau i) (fun _ _ _ => rfl)
      (fun i _ _ => ham i) (fun i _ _ => has i) (fun i _ _ => hstep i)
    have ht := stable_error_exp_bound (fun i => ‖A i‖) M α hM.le hα n (φ j) hj
      (fun i hni _ => hN i (hnN.trans hni))
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (norm_nonneg _)))
  have hi := inverse_bound_by_exp ‖A n‖ α n (hN n hnN)
  calc
    _ ≤ ‖A n‖*Real.exp (-2*α*(n : ℝ)) +
        ‖A n‖*(tailConstant M α*Real.exp (-2*α*(n : ℝ))) := add_le_add hi le_rfl |>.trans' hb
    _ = _ := by ring

lemma all_growth_zero (hA : ∀ n, PlaneAreaPreserving (A n))
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 0))
    (v : ℂ) (hv : v ≠ 0) : Growth A v 0 := by
  refine ⟨hv, ?_⟩
  have hvpos := norm_pos_iff.mpr hv
  have hc : Tendsto (fun n : ℕ => Real.log ‖v‖ / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ =>
      Real.log ‖v‖/(n : ℝ)-Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [sub_zero] using hc.sub hl
  have hup : Tendsto (fun n : ℕ =>
      Real.log ‖A n‖/(n : ℝ)+Real.log ‖v‖/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero] using hl.add hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hh := Real.log_le_log hvpos ((hA n).norm_lower v)
    rw [Real.log_mul (norm_pos A hA n).ne' (image_norm_pos A hA hv n).ne'] at hh
    have hh' : Real.log ‖v‖-Real.log ‖A n‖ ≤ Real.log ‖A n v‖ := by linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hh' (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hh := Real.log_le_log (image_norm_pos A hA hv n) ((A n).le_opNorm v)
    rw [Real.log_mul (norm_pos A hA n).ne' hvpos.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)

lemma stable_growth (hA : ∀ n, PlaneAreaPreserving (A n)) (M : ℝ) (hM : 0 < M)
    {l : ℝ} (hlpos : 0 < l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l))
    (s : ℂ) (hs : ‖s‖=1)
    (hbound : ∀ α : ℝ, 0 < α → α < l →
      ∀ᶠ n : ℕ in atTop, ‖A n s‖ ≤
        ‖A n‖*(1+tailConstant M α)*Real.exp (-2*α*(n : ℝ))) : Growth A s (-l) := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs
  have hlow (n : ℕ) : -Real.log ‖A n‖/(n : ℝ) ≤ Real.log ‖A n s‖/(n : ℝ) := by
    have hh := (hA n).norm_lower s
    rw [hs] at hh
    have hhlog := Real.log_le_log zero_lt_one hh
    rw [Real.log_one, Real.log_mul (norm_pos A hA n).ne'
      (image_norm_pos A hA hsne n).ne'] at hhlog
    apply div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  refine ⟨hsne, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro b hb
    have hh : Tendsto (fun n : ℕ => -Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 (-l)) := by
      simpa only [neg_div] using hl.neg
    filter_upwards [(tendsto_order.mp hh).1 b hb] with n hn
    exact hn.trans_le (hlow n)
  · intro b hb
    have hc : max 0 ((l-b)/2) < l := max_lt hlpos (by linarith)
    obtain ⟨α, hαlo, hαhi⟩ := exists_between hc
    have hα : 0 < α := (le_max_left _ _).trans_lt hαlo
    have hαb : l-2*α < b := by
      have := (le_max_right 0 ((l-b)/2)).trans_lt hαlo
      linarith
    have hC : 0 < 1+tailConstant M α := by
      have := tailConstant_pos hM hα
      linarith
    have hu : Tendsto (fun n : ℕ =>
        Real.log ‖A n‖/(n : ℝ)+Real.log (1+tailConstant M α)/(n : ℝ)-2*α)
        atTop (𝓝 (l-2*α)) := by
      have hh := (hl.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log (1+tailConstant M α)/(n : ℝ)) atTop (𝓝 0))).sub
        (tendsto_const_nhds (x := 2*α))
      simpa only [add_zero] using hh
    filter_upwards [hbound α hα hαhi, (tendsto_order.mp hu).2 b hαb,
      eventually_gt_atTop 0] with n hn hnb hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hh := Real.log_le_log (image_norm_pos A hA hsne n) hn
    rw [Real.log_mul (mul_pos (norm_pos A hA n) hC).ne' (Real.exp_pos _).ne',
      Real.log_mul (norm_pos A hA n).ne' hC.ne', Real.log_exp] at hh
    have hdiv := div_le_div_of_nonneg_right hh hnpos.le
    have he : (Real.log ‖A n‖+Real.log (1+tailConstant M α)+ -2*α*(n : ℝ))/(n : ℝ) =
        Real.log ‖A n‖/(n : ℝ)+Real.log (1+tailConstant M α)/(n : ℝ)-2*α := by
      rw [add_div, add_div, mul_div_cancel_right₀ _ hnpos.ne']
      ring
    rw [he] at hdiv
    exact hdiv.trans_lt hnb

lemma growth_on_line (hA : ∀ n, PlaneAreaPreserving (A n))
    {s : ℂ} {l : ℝ} (hsunit : ‖s‖=1) (hs : Growth A s l)
    (v : ℂ) (hv : v ≠ 0) (halign : wedge s v=0) : Growth A v l := by
  have he : v = dot s v • s := by simpa only [halign, zero_smul, add_zero] using unit_expansion s v hsunit
  have hd : dot s v ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv he
  have hc : Tendsto (fun n : ℕ => Real.log |dot s v|/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨hv, ?_⟩
  have hh := hc.add hs.2
  simp only [zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    conv_rhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs,
      Real.log_mul (abs_pos.mpr hd).ne' (image_norm_pos A hA hs.1 n).ne', add_div]

lemma growth_off_line (hA : ∀ n, PlaneAreaPreserving (A n))
    {l : ℝ} (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l))
    {s : ℂ} (hs : Growth A s (-l)) (v : ℂ) (hv : v ≠ 0) (hoff : wedge s v ≠ 0) :
    Growth A v l := by
  have hws : 0 < |wedge s v| := abs_pos.mpr hoff
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlo : Tendsto (fun n : ℕ =>
      Real.log |wedge s v|/(n : ℝ)-Real.log ‖A n s‖/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => Real.log |wedge s v|/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hc.sub hs.2
  have hup : Tendsto (fun n : ℕ =>
      Real.log ‖A n‖/(n : ℝ)+Real.log ‖v‖/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => Real.log ‖v‖/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hl.add hc
  refine ⟨hv, tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup ?_ ?_⟩
  · intro n
    have hh := abs_wedge_le_norm_mul (A n s) (A n v)
    rw [hA n] at hh
    have hhlog := Real.log_le_log hws hh
    rw [Real.log_mul (image_norm_pos A hA hs.1 n).ne' (image_norm_pos A hA hv n).ne'] at hhlog
    have hsub : Real.log |wedge s v|-Real.log ‖A n s‖ ≤ Real.log ‖A n v‖ := by linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hsub (Nat.cast_nonneg n)
  · intro n
    have hh := Real.log_le_log (image_norm_pos A hA hv n) ((A n).le_opNorm v)
    rw [Real.log_mul (norm_pos A hA n).ne' hvpos.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)

theorem positive_flag (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0 < M) (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hlpos : 0 < l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 → Growth A v (if wedge s v=0 then -l else l) := by
  obtain ⟨s, hsunit, hsbound⟩ := exists_stable_bound A hA M hM hstep hl
  have hs := stable_growth A hA M hM hlpos hl s hsunit hsbound
  refine ⟨s, hs.1, ?_⟩
  intro v hv
  by_cases hw : wedge s v=0
  · simp only [ite_eq_left hw]
    exact growth_on_line A hA hsunit hs v hv hw
  · simp only [ite_eq_right hw]
    exact growth_off_line A hA hl hs v hv hw

end PlaneLyapunov
end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_Lyapunov_ActualLyapunov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma ae_standardLyapunov_spectrum (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, LyapunovSpectrumAt k z (standardLyapunov k hk z) := by
  filter_upwards [ae_standardLyapunov_rate k hk] with z hz
  refine ⟨standardLyapunov_nonneg k hk z, ?_⟩
  rcases eq_or_lt_of_le (standardLyapunov_nonneg k hk z) with hzero | hpos
  · refine Or.inl ⟨hzero.symm, ?_⟩
    intro v hv
    apply PlaneLyapunov.all_growth_zero (standardDerivativeProduct k z)
      (standardDerivativeProduct_area k z) _ v hv
    simpa only [← hzero] using hz
  · refine Or.inr ⟨hpos, ?_⟩
    exact PlaneLyapunov.positive_flag (standardDerivativeProduct k z)
      (standardDerivativeProduct_area k z) (9*growthBase k)
      (mul_pos (by norm_num) (by have := growthBase_ge_four k hk; linarith))
      (standardDerivativeProduct_step_lower k hk z) hpos hz

theorem actual_positive_lyapunov :
    ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k →
      ∃ L : Torus → ℝ, Measurable L ∧ Integrable L area ∧
        (∀ z, L (standardMap k z) = L z) ∧
        (∀ᵐ z ∂area, LyapunovSpectrumAt k z (L z)) ∧
        (∀ᵐ z ∂area, Tendsto
          (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
          atTop (𝓝 (L z))) ∧ 0 < area {z | 0 < L z} := by
  obtain ⟨K, hK, hdef⟩ := eventually_meanDeficit_small_q3 (1 / 8 : ℝ) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro k hk
  have hk0 : 0 ≤ k := hK.le.trans hk
  exact ⟨standardLyapunov k hk0, measurable_standardLyapunov k hk0,
    integrable_standardLyapunov k hk0, standardLyapunov_invariant k hk0,
    ae_standardLyapunov_spectrum k hk0, ae_standardLyapunov_rate k hk0,
    positive_standardLyapunov_of_deficit k hk0 (hdef k hk)⟩

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EntropyLyapunov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped ENNReal Topology

lemma positiveLargestLyapunov_of_ae_spectrum (k : ℝ) (L : Torus → ℝ)
    (hL : Measurable L)
    (hspec : ∀ᵐ z ∂area, LyapunovSpectrumAt k z (L z))
    (hrate : ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 (L z)))
    (hpos : 0 < area {z | 0 < L z}) : PositiveLargestLyapunov k := by
  classical
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp (hspec.and hrate))
  refine ⟨{z | 0 < L z} \ N,
    (measurableSet_lt measurable_const hL).diff hNmeas, ?_, ?_⟩
  · simpa only [measure_sdiff_null hNnull] using hpos
  · intro z hz
    have hzgood : LyapunovSpectrumAt k z (L z) ∧ Tendsto
        (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
        atTop (𝓝 (L z)) := by
      by_contra hbad
      exact hz.2 (hNsub hbad)
    exact ⟨L z, hz.1, hzgood.1, hzgood.2⟩

theorem main_entropy_complete_oai :
    ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k →
      0 < metricEntropy area (standardMap k) ∧
      PositiveLargestLyapunov k ∧
      (0 < metricEntropy area (standardMap k) ↔ PositiveLargestLyapunov k) := by
  obtain ⟨K₁, hK₁, hEntropy⟩ := main_entropy
  obtain ⟨K₂, hK₂, hLyapunov⟩ := actual_positive_lyapunov
  refine ⟨max K₁ K₂, lt_of_lt_of_le hK₁ (le_max_left _ _), ?_⟩
  intro k hk
  have hEnt := hEntropy k ((le_max_left K₁ K₂).trans hk)
  obtain ⟨L, hL, _hLint, _hLinv, hspec, hrate, hpos⟩ :=
    hLyapunov k ((le_max_right K₁ K₂).trans hk)
  have hLyap : PositiveLargestLyapunov k :=
    positiveLargestLyapunov_of_ae_spectrum k L hL hspec hrate hpos
  exact ⟨hEnt, hLyap, ⟨fun _ => hLyap, fun _ => hEnt⟩⟩

end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.main_entropy_complete_oai := @OAI.StandardMapEntropy.main_entropy_complete_oai
