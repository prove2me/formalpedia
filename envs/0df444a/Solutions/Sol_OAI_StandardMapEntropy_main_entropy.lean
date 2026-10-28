-- Prove2me | solution 1 for OAI.StandardMapEntropy.main_entropy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T00:30:30.215353+00:00
-- url     : https://prove2.me/submissions/07ddff53-a0cc-4263-bc91-2a4f12eb9486

import Mathlib
import Definitions.Def_StandardMapEntropy
import Definitions.Def_OAIQ2St000
import Theorems.Thm_OAI_StandardMapEntropy_eventually_meanDeficit_small

section
-- module Solutions.OAIQ2_Std.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

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
-- module Solutions.OAIQ2_Std.StandardMap_ObservationTransport
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
lemma transferStep_difference_bound (v w : ℝ) : ‖transferStep v-transferStep w‖ ≤ |v-w| := by
  apply (transferStep v-transferStep w).opNorm_le_bound (abs_nonneg _)
  intro z
  have he : (transferStep v-transferStep w) z=((v-w)*z.re : ℝ) := by
    apply Complex.ext <;> simp only [sub_apply,Complex.sub_re,Complex.sub_im,
      transferStep_re,transferStep_im,Complex.ofReal_re,Complex.ofReal_im] <;> ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_LiftDynamics
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveCore
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveCharts
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveSubdivision
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveCompose
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveLift
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveOneStep
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveIterate
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveIntegral
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveCellIntegral
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
-- module Solutions.OAIQ2_Std.StandardMap_StablePrefix
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
-- module Solutions.OAIQ2_Std.StandardMap_WeightedChart
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
-- module Solutions.OAIQ2_Std.StandardMap_TorusIntegral
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
-- module Solutions.OAIQ2_Std.StandardMap_GridPartition
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
-- module Solutions.OAIQ2_Std.StandardMap_ClosedEligibility
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

lemma continuous_transferStep : Continuous transferStep := by
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε,hε,?_⟩
  intro w hw
  rw [dist_eq_norm]
  exact (transferStep_difference_bound w v).trans_lt (by simpa only [Real.dist_eq] using hw)

lemma continuous_transferProduct_params {α : Type*} [TopologicalSpace α]
    (v : α → ℕ → ℝ) (hv : ∀ n, Continuous (fun x => v x n)) (n : ℕ) :
    Continuous (fun x => transferProduct (v x) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_transferStep.comp (hv (n+1))).clm_comp ih

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TorusObservations
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
lemma continuous_cosine : Continuous cosine := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  change Continuous (fun x : ℝ => cosine (x : Circle))
  simpa only [cosine_coe,Function.comp_def,Pi.mul_apply,id_eq] using
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
lemma continuous_torusPotential (k : ℝ) : Continuous (torusPotential k) :=
  continuous_const.add (continuous_const.mul continuous_cosine)
lemma continuous_torusSegmentCoefficient (k : ℝ) (a : ℤ) (i : ℕ) :
    Continuous (fun z => torusSegmentCoefficient k z a i) :=
  (continuous_torusPotential k).comp (continuous_fst.comp (continuous_torusIter k _))
lemma continuous_torusSegmentTransfer (k : ℝ) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusSegmentTransfer k z a n) :=
  continuous_transferProduct_params (fun z i => torusSegmentCoefficient k z a i)
    (fun i => continuous_torusSegmentCoefficient k a i) n
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CurveColumns
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveLineIntegral
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
-- module Solutions.OAIQ2_Std.StandardMap_GridWordIntegrals
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
-- module Solutions.OAIQ2_Std.StandardMap_EntropyIntegral
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
-- module Solutions.OAIQ2_Std.StandardMap_BackwardSlice
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
-- module Solutions.OAIQ2_Std.StandardMap_GridAtomBound
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
-- module Solutions.OAIQ2_Std.StandardMap_ProductDistances
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
lemma productDistance_forward (k : ℝ) (z : Torus) (i : ℤ) (n : ℕ) :
    productDistance k z i (i+(n:ℤ))=Real.log ‖torusSegmentTransfer k z i n‖/Real.log (growthBase k) := by
  simp only [productDistance,torusTransfer_forward]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_EntropyConjugacy
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
-- module Solutions.OAIQ2_Std.StandardMap_EntropyParameters
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
-- module Solutions.OAIQ2_Std.StandardMap_EntropyEndpoint
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

theorem main_entropy_oai : MainObligation := by
  obtain ⟨K,hK,hdef⟩:=eventually_meanDeficit_small (1/8:ℝ) (by norm_num)
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

theorem solution : type_of% @OAI.StandardMapEntropy.main_entropy_oai := @OAI.StandardMapEntropy.main_entropy_oai
