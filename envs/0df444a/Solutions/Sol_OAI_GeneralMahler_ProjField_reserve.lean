-- Prove2me | solution 1 for OAI.GeneralMahler.ProjField.reserve
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:45:18.296242+00:00
-- url     : https://prove2.me/submissions/739af9fa-64c5-4980-b4bd-61b93d70a8f8

import Mathlib
import Definitions.Def_GeneralMahler
import Definitions.Def_OAIQ026G002

section
-- module Solutions.OAIQ026_GM.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Growth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Elementary bounds used throughout the Gaussian and layer integrations.
We keep pointwise growth and measurability hypotheses separate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Real
open scoped Topology ENNReal RealInnerProductSpace NNReal
namespace GeneralMahler
section
variable {X Y E F : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

namespace PolyBound

variable {f g : X → E}
theorem prodMk {h : X → F} (hf : PolyBound f) (hh : PolyBound h) :
    PolyBound fun x => (f x,h x) := by
  obtain ⟨C,n,hc,hb⟩ := common hf hh
  exact ⟨C,n,hc,fun x => max_le (hb x).1 (hb x).2⟩
end PolyBound
end

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rapid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Polynomial growth and rapid layer decay with polynomial loss in
the Gaussian variables. Fubini and moment estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise
namespace GeneralMahler
section
variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace mixed
variable {f g : X → Y → E}

lemma poly (hf : mixed f) : PolyBound f.uncurry := by
  obtain ⟨C,k,hc,h⟩ := hf 0
  simp only [pow_zero,mul_one] at h
  refine ⟨C,k,hc,?_⟩
  rintro ⟨x,y⟩
  apply (h x y).trans
  gcongr; exact le_max_right ..

end mixed

section Integrals
variable [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsAddHaarMeasure μ]

variable [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  {ν : Measure Y} [IsGaussian ν]

lemma mixed_integrable {f : X → Y → E}
    (h : mixed f) (hf : AEStronglyMeasurable f.uncurry (μ.prod ν)) :
    Integrable f.uncurry (μ.prod ν) := by
  let p := Module.finrank ℝ X+1
  let g := fun x:X => ((1+‖x‖)^p)⁻¹
  obtain ⟨C,l,hc,H⟩ := h p
  have hg : Integrable g μ := envelope_inv_int
  have hi := (hg.mul_prod ((integrable_envelope l (μ := ν)).const_mul C))
  apply hi.mono' hf (ae_of_all _ ?_)
  rintro ⟨x,y⟩
  change ‖f x y‖ ≤ g x * (C*(1+‖y‖)^l)
  dsimp only [g]; rw [ mul_comm, ← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  apply H
end Integrals
end
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Spectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Order and functional calculus for real symmetric matrices. -/
noncomputable section
open Set Filter Matrix Real
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
variable {m : ℕ} {A B : Mat m}

variable {l r : ℝ}

lemma scalar_cfc_order (f : ℝ→ℝ) (A : Mat m) (hA : A.IsHermitian) :
    (scalar m l ≤ cfc f A ↔ ∀ x∈spectrum ℝ A, l ≤ f x) ∧
    (cfc f A ≤ scalar m r ↔ ∀ x∈spectrum ℝ A, f x ≤ r) := by
  rw [scalar_eq,scalar_eq]
  have hi : IsSelfAdjoint A := hA
  have hf : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  exact ⟨algebraMap_le_cfc_iff .., cfc_le_algebraMap_iff ..⟩

lemma spectrum_order (A : Mat m) (hA:A.IsHermitian) :
    (scalar m l ≤ A ↔ ∀ x∈spectrum ℝ A, l ≤ x) ∧
    (A ≤ scalar m r ↔ ∀ x∈spectrum ℝ A, x ≤ r) := by
  have hi : IsSelfAdjoint A := hA
  have h := scalar_cfc_order (l := l) (r := r) id A hA
  rw [cfc_id ℝ A] at h
  exact h

lemma spectrum_norm_box {K : ℝ} (hk : 0 ≤ K) (ha : A.IsHermitian)
    (hb : scalar m (-K) ≤ A) (ht : A ≤ scalar m K) : ‖A‖ ≤ K := by
  have hi : IsSelfAdjoint A := ha
  conv_lhs => rw [← cfc_id ℝ A]
  apply norm_cfc_le hk
  intro x hx
  rw [Real.norm_eq_abs,abs_le]; exact ⟨(spectrum_order (l := -K) (r := K) _ ha).1.mp hb x hx,
    (spectrum_order (l := -K) (r := K) _ ha).2.mp ht x hx⟩

lemma spectrum_poly_le (f : ℝ → ℝ) {C : ℝ} {n : ℕ} (hc : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^n) (ha : A.IsHermitian) :
    ‖cfc f A‖ ≤ C*(1+‖A‖)^n := by
  have hi : IsSelfAdjoint A := ha
  apply norm_cfc_le (by positivity)
  intro x hx
  apply (hf _).trans
  have he := norm_apply_le_norm_cfc (id : ℝ → ℝ) A hx
  rw [cfc_id ℝ A] at he
  change ‖x‖ ≤ ‖A‖ at he
  gcongr

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Update
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 covariance equation from scalar inequalities of §01. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler

variable {m : ℕ}

lemma sqPSD {A : Mat m} (ha:A.IsHermitian) : 0 ≤ A*A := by
  change IsSelfAdjoint A at ha
  conv_lhs => skip
  simpa only [ha.star_eq] using star_mul_self_nonneg A
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_TraceOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Matrix trace order calculus for layer inequalities. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}
lemma trN_cyclic (A B:Mat m) : trN (A*B)=trN (B*A) :=
  congrArg (fun x=>(x:ℝ)/m) (Matrix.trace_mul_comm ..)
lemma trN_add (A B:Mat m) : trN (A+B)=trN A+trN B := by unfold trN; rw [trace_add,add_div]
lemma trN_sub (A B:Mat m) : trN (A-B)=trN A-trN B := by unfold trN; rw [trace_sub,sub_div]
lemma trN_smul (a:ℝ) (A:Mat m) : trN (a•A)=a*trN A := by
  unfold trN; rw [trace_smul]; simp; ring
lemma trN_mono {A B:Mat m} (h:A≤B) : trN A≤trN B := by
  have hi := Matrix.le_iff.mp h
  unfold trN
  have he := hi.trace_nonneg
  rw [trace_sub] at he
  gcongr; linarith
lemma sand_nonneg {A B:Mat m} (ha:0≤A) (hb:B.IsHermitian) : 0 ≤ B*A*B := by
  have he := ha.posSemidef.mul_mul_conjTranspose_same B
  rw [show Bᴴ=B from hb] at he; exact he.nonneg

lemma trN_mul_nonneg {A B : Mat m} (ha:0≤A) (hb:0≤B) : 0 ≤ trN (A*B) := by
  let S := CFC.sqrt B
  have hs : S.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.1
  calc
    _ ≤ trN (S*A*S) := by
      simpa [trN] using trN_mono (sand_nonneg ha hs)
    _ = _ := by
      rw [mul_assoc,trN_cyclic S, mul_assoc,show S*S=B from CFC.sqrt_mul_sqrt_self B hb]
lemma trN_mul_mono {A B C:Mat m} (ha:A≤B) (hc:0≤C) : trN (A*C) ≤ trN (B*C) := by
  have h := trN_mul_nonneg (sub_nonneg.mpr ha) hc
  rwa [sub_mul,trN_sub,sub_nonneg] at h

lemma trN_j (A B:Mat m) : trN (jprod A B)=trN (A*B) := by
  rw [jprod,trN_smul,trN_add,trN_cyclic B]
  ring

-- b > 0 upper bound on I+A gives b⁻¹ A ≤ thresh A via eigenvectors or product of commuting
lemma mul_comm_nonneg {A B:Mat m} (ha:0≤A) (hb:0≤B) (hh:Commute A B) :
    0 ≤ A*B := by
  let S := CFC.sqrt B
  have he : Commute A S := by
    unfold S CFC.sqrt
    first | exact (hh.symm.cfc_nnreal _).symm | exact (hh.symm.cfcₙ_nnreal _).symm
  have hp : 0 ≤ S := CFC.sqrt_nonneg _
  calc
    _ ≤ S*A*S := sand_nonneg ha hp.posSemidef.1
    _ = _ := by rw [← he.eq,mul_assoc,show S*S=B from CFC.sqrt_mul_sqrt_self _ hb]

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Edge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Deterministic-endcut layer of PSD contractions. Carries the
precise data needed for log-Jacobian estimate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ}

variable [NeZero m]
namespace Edge
variable (e:Edge m)
omit [NeZero m] in
lemma r_poly : PolyBound e.radius := (PolyBound.const _).mul
  ((PolyBound.const _).add PolyBound.id.norm)
omit [NeZero m] in
lemma r_pos (x) : 0 < e.radius x := mul_pos (lt_of_lt_of_le zero_lt_one e.hp) (by positivity)
omit [NeZero m] in
lemma Pcont (x y) : ‖e.P x y‖ ≤ 1 := by
  apply spectrum_norm_box zero_le_one (e.psd ..).posSemidef.1
  · apply le_trans _ (e.psd ..)
    have he := scalar_le' (m:=m) (-1) 0 (by norm_num)
    simpa only [scalar, zero_smul] using he
  simpa [scalar] using e.le_one x y

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GainIndent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Exact linear and nonnegative surplus terms in the log identity. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
omit [NeZero m] in
lemma meas_trN : Measurable (@trN m) := by simp_rw [← funext trL_apply]; exact trL.continuous.measurable
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_NtLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Nonthreshold kernel and integration over the ordered halves.
We use (l,z) as pair of variables and ordinary product volume. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ}

namespace Edge
variable (e:Edge m)
lemma nt_pos (u x) : 0 ≤ e.nt0 u x := by
  unfold nt0 NTm; rw [trN_j]
  exact trN_mul_nonneg (e.psd ..) (sub_nonneg.mpr (e.le_one ..))
lemma nt_meas : Measurable e.NTm.uncurry := by
  let m₁ := fun v:Plane×Rn m=> e.P (min v.1.1 v.1.2) v.2
  let m₂ := fun v:Plane×Rn m=> 1-e.P (max v.1.1 v.1.2) v.2
  have he : Measurable m₁ := e.meas.comp (show Measurable (fun v:Plane×Rn m => (min v.1.1 v.1.2,v.2)) from by fun_prop)
  have hh : Measurable m₂ := measurable_const.sub (e.meas.comp (show Measurable (fun v:Plane×Rn m => (max v.1.1 v.1.2,v.2)) from by fun_prop))
  exact (show Measurable (fun _:Plane × Rn m=> (1/2:ℝ)) from measurable_const).smul ((he.mul hh).add (hh.mul he))
lemma nt_mixed : mixed e.NTm := by
  let f := fun v:Plane × Rn m => e.P (min v.1.1 v.1.2) v.2
  let g := fun v:Plane × Rn m => e.P (max v.1.1 v.1.2) v.2
  have hf : PolyBound f := PolyBound.of_bound 1 fun v=> e.Pcont ..
  have hg : PolyBound g := PolyBound.of_bound 1 fun v=> e.Pcont ..
  have hh := (PolyBound.const 1).sub hg
  have hp : PolyBound e.NTm.uncurry :=
    (PolyBound.const _).smul ((hf.mul hh).add (hh.mul hf))
  apply mixed.of_cutoff hp e.r_poly
  rintro ⟨z,w⟩ x hx
  let c := e.radius x
  change c < max ‖z‖ ‖w‖ at hx
  have hr : c< max z w ∨ min z w < -c := by
    simp only [Real.norm_eq_abs,lt_max_iff,lt_abs,min_lt_iff] at *
    grind
  rcases hr with h|h
  · simp only [NTm,e.tend_pos (max z w) x h,sub_self,jprod,mul_zero,zero_mul,add_zero,smul_zero]
  have he : e.P (min z w) x=0 := e.tend_neg _ _ (show c < -min z w by linarith)
  simp [NTm,he,jprod]

lemma n0_meas : StronglyMeasurable e.nt0.uncurry := (meas_trN.comp e.nt_meas).stronglyMeasurable
lemma n0_mixed : mixed e.nt0 := by
  let f := fun (_:Plane) (_:Rn m) => ‖(trL:Mat m→L[ℝ]ℝ)‖
  have hf : PolyBound f.uncurry := PolyBound.const _
  apply e.nt_mixed.product hf
  intro u x
  unfold nt0 f
  rw [← trL_apply,Real.norm_of_nonneg (norm_nonneg (trL:Mat m→L[ℝ]ℝ)),mul_comm]
  apply ContinuousLinearMap.le_opNorm
lemma n0_int : Integrable e.nt0.uncurry (volume.prod (normal m)) :=
  mixed_integrable e.n0_mixed e.n0_meas.aestronglyMeasurable

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Entropy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Entropy bound (10), in normalized trace notation. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma etL_apply (B A:Mat m) : etL B A=trN (B*A) := by simp [etL]

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_L2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar coefficient calculus. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ} [NeZero m]
omit [NeZero m] in
lemma qcf_ip' (f:G2 m) (a) : qcf f a=⟪f,ModL a⟫ := (qcf_ip ..).trans (real_inner_comm ..)

lemma qcf_sum {f g:Rn m→ℝ} (hf:MemLp f 2 (normal m)) (hg:MemLp g 2 (normal m)) :
    HasSum (fun a=> qcf f a*qcf g a) (∫ x,f x*g x ∂normal m) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hF : F=ᵐ[normal m] f := MemLp.coeFn_toLp ..
  have hG : G=ᵐ[normal m] g := MemLp.coeFn_toLp ..
  have hi (a) := qcf_congr hF a
  have hh (a) := qcf_congr hG a
  have hv := (HB m).hasSum_inner_mul_inner F G
  simp_rw [HB_eq,← qcf_ip', ← qcf_ip,hi,hh] at hv
  have he : ⟪F,G⟫ = ∫ x,f x*g x ∂normal m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF,hG] with x hx hy
    rw [hx,hy]
    exact mul_comm ..
  rwa [he] at hv
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Gradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Hermite coefficient recurrence for functions with suitable local
Lipschitz bounds. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric Real ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ}
variable {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

lemma p_sum {I X F:Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup F]
    {f:I→X→F} (h:∀ i,PolyBound (f i)) (s:Finset I) :
    PolyBound fun x=> ∑ i∈s, f i x := by
  classical
  induction s using Finset.induction with
  | empty=>simpa using PolyBound.const (X:=X) (0:F)
  | insert x u h' ih=>simpa [h'] using (h x).add ih

omit [FiniteDimensional ℝ F] in
lemma i_cof {f:Rn m→F} (hf:PolyBound f) (hm:AEStronglyMeasurable f (normal m)) (a:MI m) :
    Integrable (fun x=>MM a x • f x) (normal m) :=
  ((M_poly a).smul hf).gaussian_integrable ((M_cont a).aestronglyMeasurable.smul hm)
lemma qcf_cof (f:Rn m→ℝ) (a) : qcf f a=cof f a := by
  unfold qcf cof; congr 1; ext x; exact mul_comm ..
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Pair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Parseval identities for finite-dimensional Gaussian fields and bilinear pairings. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ} [NeZero m]
variable {F E:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace regular
variable {f:Rn m→F} (hf:regular f)
omit [NeZero m] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma ig (hf:regular f) : Integrable f (normal m) :=
  hf.p.gaussian_integrable hf.meas
omit [NeZero m] [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
lemma lin (hf:regular f) (l:F→L[ℝ]E) :
    regular (fun x=>l (f x)) := ⟨(PolyBound.clm _).comp hf.p,(l.integrable_comp hf.ig).aestronglyMeasurable⟩
omit [NeZero m] [FiniteDimensional ℝ F] in
lemma smul (hf:regular f) {g:Rn m→ℝ} (hg:regular g) : regular fun x=>g x • f x :=
  ⟨hg.p.smul hf.p,hg.meas.smul hf.meas⟩
omit [NeZero m] in
lemma mul {f g:Rn m→ℝ} (hf:regular f) (hg:regular g) : regular fun x=>f x*g x := hg.smul hf
end regular

variable {f:Rn m→E} {g:Rn m→F}
omit [NeZero m] in
lemma cof_clm (hf:regular f) (l:E→L[ℝ]F) (a:MI m) : l (cof f a)=cof (fun x=>l (f x)) a := by
  unfold cof
  rw [← l.integral_comp_comm (i_cof hf.p hf.meas a)]
  simp only [map_smul]
lemma cof_form (hf:regular f) (hg:regular g) (l:E→L[ℝ]ℝ) (k:F→L[ℝ]ℝ) :
    HasSum (fun a=> l (cof f a)*k (cof g a))
      (∫ x,l (f x)*k (g x) ∂normal m) := by
  have hi := hf.lin l
  have hh := hg.lin k
  simp_rw [cof_clm hf,cof_clm hg,← qcf_cof]
  exact qcf_sum (lp_poly hi.p hi.meas) (lp_poly hh.p hh.meas)

-- Function of a bilinear form, prove via finite-dimensional basis projections
lemma cof_bil (hf:regular f) (hg:regular g) (l:E→L[ℝ]F→L[ℝ]ℝ) :
    HasSum (fun a=>l (cof f a) (cof g a)) (∫ x,l (f x) (g x) ∂normal m) := by
  let b := Module.finBasis ℝ E
  let c := fun i=> (b.coord i).toContinuousLinearMap
  have he (x:E) (y:F) : l x y= ∑ i,c i x*l (b i) y := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [_root_.map_sum,_root_.sum_apply,_root_.map_smul,_root_.smul_apply,smul_eq_mul]
    rfl
  have h (i) := cof_form hf hg (c i) (l (b i))
  rw [show (fun x=> l (f x) (g x))=_ from funext (fun x=> he (f x) (g x)), show (fun a=> l (cof f a) (cof g a))=_ from funext (fun x=> he (cof f x) (cof g x))]
  rw [integral_finsetSum]
  · exact hasSum_sum fun i _=> h i
  exact fun i _=> ((hf.lin (c i)).mul (hg.lin (l (b i)))).ig

omit [NeZero m] in
lemma deg_inc (a:MI m) (i) : deg (inc a i)=deg a+1 := by
  simp only [deg,inc]
  classical
  simp only [← Finset.sum_erase_add _ _ (Finset.mem_univ i),Function.update_self]
  have hi : (∑ k∈Finset.univ.erase i,Function.update a i (a i+1) k) =
      ∑ k∈Finset.univ.erase i,a k := Finset.sum_congr rfl fun k hk=> Function.update_of_ne
        (Finset.ne_of_mem_erase hk) ..
  rw [hi]; omega
omit [NeZero m] in
lemma dz (a:MI m) : deg a=0 ↔ a=0 := by
  unfold deg; simp [Finset.sum_eq_zero_iff,funext_iff]
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_CovHerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq13 coefficient-pair (weighted K multiplier via coefficients). -/
noncomputable section
open Set Filter Metric MeasureTheory MeasureTheory.Measure Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma pJ_eq (B A C:Mat m) : PJ B A C=Pj B A C := by simp [PJ,Pj,jprod,mul_add, trN_add,trN_smul,etL_apply]

lemma pt_sum {B:Mat m} {A C:Rn m→Mat m} (ha:regular A) (hc:regular C) :
    HasSum (CpPair B A C) (Pt B A C) := by
  have hi := cof_bil ha hc (PJ B)
  simp_rw [pJ_eq] at hi; exact hi

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Frame_Diagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Borel choice of diagonalizing frame. Everything computed in a
diagonalization is defined on a full orthogonal matrix and its entries. -/
noncomputable section
open Set Filter MeasureTheory Metric Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m:ℕ}
namespace Frm
variable (u v:Frm m)
lemma m₂ : u.val*star u.val=1 := u.property.2

lemma fix_loc (A:Mat m) : u.fixMat (u.loc A)=A := by
  unfold loc fixMat; simp only [mul_assoc]
  rw [u.m₂,mul_one,← mul_assoc,u.m₂,one_mul]

lemma loc_inj : Function.Injective u.loc := fun _ b h =>
  (u.fix_loc _).symm.trans ((congrArg u.fixMat h).trans (u.fix_loc b))

lemma loc_mul (A B:Mat m) : u.loc (A*B)=u.loc A*u.loc B := by
  unfold loc; simp only [mul_assoc]
  rw [show u.val*(star u.val*(B*u.val))=B*u.val from by rw [← mul_assoc,u.m₂,one_mul]]

lemma loc_star (A:Mat m) : u.loc (star A)=star (u.loc A) := by
  unfold loc; rw [star_mul,star_mul,star_star,mul_assoc]
lemma loc_trace (A:Mat m) : trace (u.loc A) = trace A := by
  unfold loc; rw [trace_mul_comm,← mul_assoc,u.m₂,one_mul]

lemma fix_mul_cross (A:Mat m) :
    star u.val*A*v.val=u.loc A*(star u.val*v.val) := by
  unfold loc; simp only [mul_assoc]
  rw [show u.val*(star u.val*v.val)=v.val from by rw [← mul_assoc,u.m₂,one_mul]]
lemma fix_mul_cross' (A:Mat m) :
    star u.val*A*v.val= (star u.val*v.val)*v.loc A := by
  unfold loc
  simp only [mul_assoc]
  rw [show v.val*(star v.val*(A*v.val))=A*v.val from by rw [← mul_assoc,v.m₂,one_mul]]

lemma cross_cancel (A B:Mat m) (h:star u.val*A*v.val= star u.val*B*v.val) : A=B := by
  have hi (A:Mat m) : u.val*(star u.val*A*v.val)*star v.val=A := by
    simp only [mul_assoc]; rw [v.m₂,mul_one,← mul_assoc,u.m₂,one_mul]
  exact (hi A).symm.trans ((congrArg (fun x=> u.val*x*star v.val) h).trans (hi B))

lemma lSpecEq (A:Mat m) (f:ℝ→ℝ) : u.loc (u.specEval A f) = Matrix.diagonal (fun i=> f (u.eig A i)) :=
  u.loc_fix ..

lemma frame_cross {A:Mat m} (h:u.Dgn A) (g:v.Dgn A) (i j):
    u.eig A i*(star u.val*v.val) i j=(star u.val*v.val) i j*v.eig A j := by
  have hh := (u.fix_mul_cross v A).symm.trans (u.fix_mul_cross' v A)
  rw [show u.loc A=_ from h, show v.loc A=_ from g] at hh
  simpa only [Matrix.diagonal_mul,Matrix.mul_diagonal] using congrFun (congrFun hh i) j

lemma spec_unique {A:Mat m} (h:u.Dgn A) (g:v.Dgn A) (f:ℝ→ℝ) :
    u.specEval A f=v.specEval A f := by
  apply u.cross_cancel v
  rw [u.fix_mul_cross,u.fix_mul_cross',u.lSpecEq,v.lSpecEq]
  ext i j
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal]
  have hh := u.frame_cross v h g i j
  rcases eq_or_ne ((star u.val*v.val) i j) 0 with hz|hz
  · simp [hz]
  have he : u.eig A i=v.eig A j := mul_right_cancel₀ hz (hh.trans (mul_comm ..))
  rw [he,mul_comm]

lemma loc_cfc {A:Mat m} (h:A.IsHermitian) (hu:u.Dgn A) (f:ℝ→ℝ) :
    u.loc (cfc f A)= Matrix.diagonal (fun i=>f (u.eig A i)) := by
  rw [← u.lSpecEq A]
  congr 1
  rw [u.spec_unique (eu h) hu (eu_d h) f,specEval,eu_eig]
  open Unitary in
    rw [Matrix.IsHermitian.cfc_eq h,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    simp only [Function.comp_def]
    rfl

lemma fr_m : Measurable (@fr m) := selectU.choose_spec.1
lemma fr_d (A:SH m) : (fr A).Dgn A.val := selectU.choose_spec.2 A
end Frm
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Kernel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Kernel integrations for §04. Plane is Euclidean pair (with product
volume), split along diagonal. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile

lemma off_diag : ∀ᵐ u:Plane,u.1≠u.2 := by
  apply (ae_prod_iff_ae_ae (((isClosed_eq continuous_fst continuous_snd).measurableSet.compl))).mpr
  filter_upwards with x
  rw [ae_iff]; simp []
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Indicator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! p-to-indicator score and layer integration formulas. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile
lemma jump_m : Measurable (Function.uncurry jump) :=
  Measurable.ite ((isClosed_le continuous_snd continuous_fst).measurableSet)
    measurable_const measurable_const

lemma score_m : Measurable score.uncurry := (cp.measurable.comp measurable_fst).sub jump_m

lemma score_rapid : mixed score := by
  let f := fun z (_:ℝ)=> p z-st z
  let g := fun z y=>st z-jump z y
  rw [show score=fun z y=> f z y+g z y from funext fun x=>funext fun y=>by unfold score f g; ring]
  apply (mixed.of_rapid rapid_p).add
  apply mixed.of_cutoff (show PolyBound g.uncurry from PolyBound.of_bound 1 fun ⟨x,y⟩=>by
    change ‖st x-jump x y‖≤1; unfold st jump; split_ifs <;> norm_num)
    (show PolyBound (fun x:ℝ=>‖x‖) from PolyBound.id.norm)
  intro x y hx
  simp only [Real.norm_eq_abs] at hx
  unfold g st jump; split_ifs <;> grind

lemma ss_m {f:ℝ→ℝ} (hf:TestF f) : mixed (ss f) :=
  score_rapid.product (g:=fun x _=>deriv f x) (show PolyBound (fun u:Plane=> deriv f u.1) from hf.der.poly.comp PolyBound.fst)
    fun _x _y=> (norm_mul _ _).le
lemma ss_sm (f) : Measurable (ss f).uncurry :=
  score_m.mul ((measurable_deriv f).comp measurable_fst)

lemma centered_s {f:ℝ→ℝ} (hf:TestF f) (x:ℝ) :
    (∫ z,ss f z x)= f x-ga f := by
  let g := fun z=>ss f z x+phi z*f z
  have hg (t:ℝ) : HasDerivAt (fun z=>p z*f z)
      (phi t*f t+p t*deriv f t) t :=
    (d_p t).fun_mul (hf.diff t).hasDerivAt
  have hg' (t:ℝ) : HasDerivAt (fun z=>(p z-1)*f z)
      (phi t*f t+(p t-1)*deriv f t) t :=
    ((d_p t).sub_const 1).fun_mul (hf.diff t).hasDerivAt
  have ht := rapid_p.product hf.poly
  have hi := mixed_integrable_left (μ:=volume) (ss_m hf) x
    ((ss_sm f).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hh : Integrable g := hi.add (ga_i hf)
  have h₀ : Tendsto (fun x=>p x*f x) atBot (𝓝 0) := by
    apply Tendsto.congr' _ ht.tail_limit_bot
    filter_upwards [eventually_lt_atBot (0:ℝ)] with z hz; simp [st,not_le_of_gt hz]
  have h₁ : Tendsto (fun x=>(p x-1)*f x) atTop (𝓝 0) := by
    apply Tendsto.congr' _ ht.tail_limit
    filter_upwards [eventually_ge_atTop (0:ℝ)] with z hz; simp [st,hz]
  have ha : (∫ t in Iic x,g t)=p x*f x := by
    have hh := integral_Iic_of_hasDerivAt_of_tendsto ((hg x).continuousAt.continuousWithinAt)
      (fun t ht => ?_) hh.integrableOn h₀
    · simpa using hh
    have he : g t=phi t*f t+p t*deriv f t := by simp only [g,ss,score,jump,
      ite_eq_right (not_le_of_gt (mem_Iio.mp ht)),sub_zero]; ring
    exact he.symm ▸ hg t
  have hb : (∫ t in Ioi x,g t)= -((p x-1)*f x) := by
    have hh := integral_Ioi_of_hasDerivAt_of_tendsto ((hg' x).continuousAt.continuousWithinAt)
      (fun t ht => ?_) hh.integrableOn h₁
    · simpa using hh
    have he : g t=phi t*f t+(p t-1)*deriv f t :=
      by simp only [g,ss,score,jump,ite_eq_left (mem_Ioi.mp ht).le]; ring
    exact he.symm ▸ hg' t
  have hx : (∫ t,g t)=f x := by
    rw [← integral_add_compl measurableSet_Iic (s:=Iic x) hh,compl_Iic,ha,hb]; ring
  rw [show (∫ t,g t) = _ from integral_add hi (ga_i hf)] at hx
  unfold ga; linarith

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Threshold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Thresholds of arbitrary moderate-growth random Hermitian fields
(in particular A and L) §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

namespace FieldMat
variable (B:FieldMat m)
lemma reg : regular B.A := ⟨B.poly,B.hM.aestronglyMeasurable⟩

lemma Fr_D (x) : (B.Fr x).Dgn (B.A x) := Frm.fr_d _
lemma fr_m : Measurable B.Fr := Frm.fr_m.comp (B.hM.measurable.subtype_mk (h:=B.sym))
lemma ev_m (i) : Measurable fun x=> B.ev x i :=
  (measurable_pi_iff.mp (Frm.cdiag.measurable.comp
    (Frm.cont_loc.measurable.comp (B.hM.measurable.prodMk B.fr_m)))) i

lemma evfrm (x) (f) :
    (B.Fr x).loc (B.eval f x)= Matrix.diagonal (fun i=> f (B.ev x i)) :=
  Frm.loc_cfc _ (B.sym x) (B.Fr_D x) f
lemma evfrm' (x) (f) : B.eval f x= (B.Fr x).fixMat (Matrix.diagonal (fun i=> f (B.ev x i))) := by
  rw [← B.evfrm x f,Frm.fix_loc]

lemma theta_gen_meas {f:ℝ→ℝ→ℝ} (hf:Measurable f.uncurry) :
    Measurable (fun u:ℝ × Rn m=>B.eval (f u.1) u.2) := by
  simp_rw [B.evfrm',Frm.fixMat]
  have hg : Measurable (fun u:ℝ×Rn m=>(B.Fr u.2).val) :=
    measurable_subtype_coe.comp (B.fr_m.comp measurable_snd)
  have hh : Measurable fun u:ℝ×Rn m=> Matrix.diagonal (fun i=> f u.1 (B.ev u.2 i)) :=
    Frm.cdiagonal.measurable.comp (measurable_pi_iff.mpr fun i=> hf.comp
      (measurable_fst.prodMk ((B.ev_m _).comp measurable_snd)))
  exact (hg.mul hh).mul (continuous_star.measurable.comp hg)

lemma eval_reg {f:ℝ→ℝ} (hf:TestF f) : regular (B.eval f) := by
  have hm : Measurable (B.eval f) := by
    have h := B.theta_gen_meas (f:=fun _ x=>f x) (hf.cont.measurable.comp measurable_snd)
    exact h.comp (show Measurable (fun x:Rn m=>((0:ℝ),x)) by fun_prop)
  obtain ⟨C,n,hc,h⟩ := hf.poly
  have hp : PolyBound (fun x=>C*(1+‖B.A x‖)^n) :=
    (PolyBound.const _).mul (((PolyBound.const _).add B.poly.norm).pow _)
  refine ⟨hp.mono (fun x=>?_ ), hm.aestronglyMeasurable⟩
  apply le_trans (spectrum_poly_le f hc h (B.sym x)); exact le_abs_self _

lemma thetaM : StronglyMeasurable B.Θ.uncurry := (B.theta_gen_meas jump_m).stronglyMeasurable
lemma theta_nn (z x) : 0 ≤ B.Θ z x := by
  have hi : IsSelfAdjoint (B.A x) := B.sym x
  apply cfc_nonneg
  intro y _; unfold jump; split_ifs <;> norm_num
lemma theta_le (z x) : B.Θ z x ≤ 1 := by
  have hi := (scalar_cfc_order (jump z) (B.A x) (B.sym x) (l:=0) (r:=1)).2.mpr
    (fun y _=> by unfold jump; split_ifs <;> norm_num)
  simpa [Θ,eval,scalar] using hi
lemma theta_norm (z x) : ‖B.Θ z x‖ ≤ 1 := by
  apply spectrum_norm_box zero_le_one (B.theta_nn ..).posSemidef.1
  · apply le_trans _ (B.theta_nn z x)
    have he := scalar_le' (m:=m) (-1) 0 (by norm_num)
    simpa only [scalar, zero_smul] using he
  simpa [scalar] using B.theta_le z x

lemma theta_exact (z x) (hx : ‖B.A x‖< |z|) : B.QP z x=0 := by
  let A := B.A x
  have hi : IsSelfAdjoint A := B.sym x
  have he (t:ℝ) (ht:t∈spectrum ℝ A) : ‖t‖ ≤ ‖A‖ := by
    have h := norm_apply_le_norm_cfc id A ht
    rw [cfc_id ℝ A] at h
    exact h
  have hh : cfc (jump z) A=cfc (fun _=>st z) A := cfc_congr fun t ht=> by
    have hv := he t ht
    change ‖A‖<_ at hx
    unfold jump st; rw [Real.norm_eq_abs] at hv; split_ifs <;> grind
  unfold QP; change cfc (jump z) A-_ = _
  rw [hh,cfc_const (st z) A hi,Algebra.algebraMap_eq_smul_one,sub_self]
lemma qp_mixed : mixed B.QP := by
  apply mixed.of_cutoff
    (show PolyBound B.QP.uncurry from
      (PolyBound.of_bound (f:=B.Θ.uncurry) 1 (fun ⟨z,x⟩=>B.theta_norm z x)).sub
        ((poly_st.comp PolyBound.fst).smul (PolyBound.const (1:Mat m))))
    B.poly.norm
  exact fun z x=> B.theta_exact z x
end FieldMat
namespace ProjField
variable [NeZero m] (q:ProjField m) (B:FieldMat m)
lemma eM : mixed (q.EZ B) := by
  convert q.Pstep_mixed.sub B.qp_mixed using 1
  all_goals try with_reducible_and_instances rfl
  funext y x; simp only [EZ,Pstep,Gstep,FieldMat.QP]; abel
lemma eSM : StronglyMeasurable (q.EZ B).uncurry :=
  q.edge.meas.stronglyMeasurable.sub B.thetaM

lemma zm {f:ℝ→ℝ} (hf:TestF f) : mixed (q.zE B f) := by
  apply (q.eM B).product (g:=fun z _=>deriv f z)
    (show PolyBound (fun u:ℝ × Rn m=>deriv f u.1) from hf.der.poly.comp PolyBound.fst)
  intro z x; unfold zE; rw [norm_smul,mul_comm]
lemma zSM (f) : StronglyMeasurable (q.zE B f).uncurry :=
  (((measurable_deriv f).comp measurable_fst).stronglyMeasurable).smul (q.eSM B)
lemma zi {f:ℝ→ℝ} (hf:TestF f) (x) :
    Integrable fun z=>q.zE B f z x := mixed_integrable_left (q.zm B hf) x
      (((q.zSM B f).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)

lemma mb_eq {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    q.MB B f x= -(∫ z,q.zE B f z x) := by
  have iH := q.H_left_int hf.der.poly x; have iZ := q.zi B hf x
  let u := B.Fr x
  let g := fun z=> q.kerH f z x + q.zE B f z x
  have he (z) :
      u.loc (g z)=Matrix.diagonal (fun i=>ss f z (B.ev x i)) := by
    unfold g kerH zE PD EZ
    rw [← smul_add]
    have ht : p z • (1:Mat m)-q.Pmat z x+(q.Pmat z x-B.Θ z x)= p z • 1-B.Θ z x := by abel
    rw [ht, u.loc_smul,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.Θ z x)= _ from B.evfrm x _]
    ext i j
    by_cases h:i=j
    · subst j; simp [ss,score,mul_comm]
    simp [h]
  let l : Mat m→L[ℝ]Mat m := LinearMap.toContinuousLinearMap (𝕜:=ℝ)
    { toFun:=u.loc, map_add':=u.loc_add, map_smul':=u.loc_smul }
  have hl : ∫ z,g z = B.eval f x - scalar m (ga f) := by
    apply u.loc_inj
    rw [u.loc_sub,u.loc_smul, u.loc_one,show u.loc (B.eval f x)= _ from B.evfrm x f]
    have hi := iH.add iZ
    have ig : Integrable g := iH.add iZ
    change l _=_
    rw [← l.integral_comp_comm ig]
    have hh (z) : l (g z)= _ := he z
    have hh' (i j:Fin m) := (coeffMap i j).integral_comp_comm
      (l.integrable_comp ig)
    ext i j
    rw [show (∫ z,l (g z)) i j=(∫ z,l (g z) i j) from (hh' i j).symm]
    simp_rw [hh]
    by_cases h:i=j
    · subst j
      simpa using centered_s hf (B.ev x i)
    simp [h]
  have h := integral_add iH iZ
  change ∫ z,g z=_ at h
  rw [hl] at h
  unfold MB Hmat
  rw [show (∫ z,q.kerH f z x)=_ from eq_sub_of_add_eq h.symm]
  abel

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EvalGap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Primitive identities and notation for layer to spectral comparisons. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

lemma pj_sym (B A C:Mat m) : Pj B A C=Pj B C A := by simp only [Pj,jprod,add_comm]
lemma j_smul_left (A C:Mat m) (a:ℝ) : jprod (a•A) C=a•jprod A C := by
  simp only [jprod,smul_mul_assoc,mul_smul_comm,smul_add]; rw [smul_comm,smul_comm (1/2:ℝ) a]
lemma pj_norm {A B C:Mat m} :
    ‖Pj B A C‖ ≤ (‖etL B‖ * ‖A‖)*‖C‖ := by
  rw [Pj,← etL_apply]
  have h : ‖jprod A C‖≤‖A‖*‖C‖ := by
    unfold jprod; rw [norm_smul,Real.norm_of_nonneg (by norm_num)]
    have hh := norm_add_le (A*C) (C*A)
    linarith [norm_mul_le A C,norm_mul_le C A]
  apply ((etL B).le_opNorm _).trans
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
lemma pj_scale (a b:ℝ) (B A C:Mat m) :
    Pj B (a•A) (b•C)=a*(b*Pj B A C) := by
  unfold Pj
  have h (x y:Mat m):jprod x y=jprod y x := by unfold jprod; rw [add_comm]
  rw [j_smul_left,h A,j_smul_left,h C]
  simp only [mul_smul_comm,trN_smul]

lemma mixed_proj {X Y E F:Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f:X→Y→E} (hf:mixed f) (l:E→L[ℝ]F) :
    mixed fun x y=> l (f x y) := by
  apply hf.product (g:=fun _ _=>‖l‖)
    (show PolyBound (fun _:X×Y=>‖l‖) from PolyBound.const _)
  intro x y
  calc
    _ ≤ ‖l‖*‖f x y‖ := l.le_opNorm _
    _ = _ := by rw [Real.norm_of_nonneg (norm_nonneg l),mul_comm]

namespace FieldMat
variable (B:FieldMat m)
lemma pEval {f} (hf:TestF f) : PolyBound (B.eVal f).uncurry :=
  (((B.eval_reg hf).p).comp PolyBound.snd).sub
    ((hf.poly.comp PolyBound.fst).smul (PolyBound.const _))
lemma smEval {f} (hf:TestF f) : StronglyMeasurable (B.eVal f).uncurry :=
  ((B.theta_gen_meas (f:=fun _ y=>f y) (hf.cont.measurable.comp measurable_snd)).stronglyMeasurable).sub
    (((hf.cont.comp continuous_fst).stronglyMeasurable).smul stronglyMeasurable_const)

lemma Em : StronglyMeasurable B.EC.uncurry :=
  ((jump_m.comp (measurable_swap.comp measurable_fst)).stronglyMeasurable.smul stronglyMeasurable_const).sub
    (B.thetaM.comp_measurable ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
lemma Ep : PolyBound B.EC.uncurry :=
  ((PolyBound.of_bound (f:=fun v:Plane × Rn m=>jump v.1.2 v.1.1) 1
    (fun v=>by unfold jump; split_ifs <;> simp)).smul (PolyBound.const _)).sub
    (PolyBound.of_bound (f:=fun v:Plane × Rn m=>B.Θ v.1.2 v.2) 1 (fun v=>B.theta_norm ..))

lemma vanishEC (x:Rn m) (u:Plane) (h: max ‖u.1‖ ‖B.A x‖ < ‖u.2‖) :
    B.EC u x=0 := by
  unfold EC
  obtain ⟨hv,hx⟩ := max_lt_iff.mp h
  have he := B.theta_exact u.2 x hx
  unfold QP at he; rw [sub_eq_zero.mp he]
  have ht : jump u.2 u.1=st u.2 := by
    simp only [Real.norm_eq_abs] at hv
    unfold jump st; split_ifs <;> grind
  rw [ht,scalar,sub_self]

lemma gapM (x:Rn m) (z:ℝ) {f:ℝ→ℝ} (hf:TestF f) :
    Integrable fun y:ℝ=> deriv f y • B.EC (z,y) x := by
  let g := fun y (_:ℝ)=> deriv f y • B.EC (z,y) x
  have hi : mixed g := by
    have hh : PolyBound (fun v:ℝ×ℝ=>B.EC (z,v.1) x) :=
      PolyBound.of_bound 2 fun v=> by
        have h := norm_sub_le (scalar m (jump v.1 z)) (B.Θ v.1 x)
        have hh : ‖scalar m (jump v.1 z)‖≤1 := by
          rcases subsingleton_or_nontrivial (Mat m) with h | h
          · have h0 : scalar m (jump v.1 z) = 0 := @Subsingleton.elim _ h _ 0
            rw [h0, norm_zero]
            exact zero_le_one
          · let : Nontrivial (Mat m) := h
            unfold jump scalar
            split <;> simp
        apply h.trans
        linarith [B.theta_norm v.1 x]
    apply mixed.of_cutoff (show PolyBound g.uncurry from (hf.der.poly.comp PolyBound.fst).smul hh)
      (PolyBound.const (X:=ℝ) (max ‖z‖ ‖B.A x‖))
    intro y w h; unfold g; rw [B.vanishEC _ _ h,smul_zero]
  apply mixed_integrable_left hi 0
  exact ((hf.der.cont.stronglyMeasurable).smul (B.Em.comp_measurable
    ((measurable_const.prodMk measurable_id).prodMk measurable_const))).aestronglyMeasurable

lemma gap (x:Rn m) (z:ℝ) {f:ℝ→ℝ} (hf:TestF f) :
    B.eVal f z x= ∫ y,deriv f y • B.EC (z,y) x := by
  let u := B.Fr x
  let l := LL u
  let g := fun y=> deriv f y • B.EC (z,y) x
  have hi := B.gapM x z hf
  apply u.loc_inj
  rw [eVal,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.eval f x)= _ from B.evfrm x f]
  change _=l (∫ y,g y)
  rw [← l.integral_comp_comm hi]
  ext i j
  rw [show (∫ y,l (g y)) i j=∫ y,l (g y) i j from
    ((coeffMap i j).integral_comp_comm (l.integrable_comp hi)).symm]
  have he (y) : l (g y) = deriv f y • (scalar m (jump y z)-Matrix.diagonal (fun i=>jump y (B.ev x i))) := by
    change u.loc (deriv f y • (scalar m (jump y z)-B.Θ y x))=_
    rw [u.loc_smul,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.Θ y x)=_ from B.evfrm x (jump y)]
  simp_rw [he]
  by_cases h:i=j
  · subst j
    have ht (y) : (deriv f y • (scalar m (jump y z)-Matrix.diagonal (fun i=>jump y (B.ev x i)))) i i =
        ss f y (B.ev x i)-ss f y z := by
      simp [ss,score,scalar]; ring
    have hh (x) := centered_s hf x
    have hp (x:ℝ) : Integrable fun y=>ss f y x :=
      mixed_integrable_left (ss_m hf) x ((ss_sm f).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    simp_rw [ht]; rw [integral_sub (hp _) (hp _),hh,hh]; simp
  simp [scalar,h]

lemma nest (x:Rn m) (z y:ℝ) (hz:z≤y) :
    B.Θ z x* B.Θ y x=B.Θ z x ∧ B.Θ y x*B.Θ z x=B.Θ z x := by
  let u := B.Fr x
  have hi (t:ℝ) : u.loc (B.Θ t x)= Matrix.diagonal (fun i=>jump t (B.ev x i)) := B.evfrm x (jump t)
  constructor <;> apply u.loc_inj <;> rw [u.loc_mul] <;>
    simp only [hi,Matrix.diagonal_mul_diagonal] <;> congr 1 <;> funext i <;>
    unfold jump <;> split_ifs <;> grind
end FieldMat
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Beta
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §04 Eq15, threshold comparison. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

lemma pj_cont (W:Mat m) : Continuous (Pj W).uncurry := by
  change Continuous (fun p:Mat m × Mat m=>Pj W p.1 p.2)
  have he : Continuous (trN:Mat m→ℝ) := by simp_rw [← funext trL_apply]; exact trL.continuous
  unfold Pj jprod
  fun_prop

lemma pj_p {X:Type*} [NormedAddCommGroup X] {f g:X→Mat m}
    (hf:PolyBound f) (hg:PolyBound g) (W:Mat m) :
    PolyBound fun x=>Pj W (f x) (g x) := by
  let h := fun x=> ‖etL W‖*‖g x‖
  have hh : PolyBound h := (PolyBound.const _).mul hg.norm
  apply PolyBound.of_prod_le hf hh
  intro x
  apply pj_norm.trans
  unfold h; rw [Real.norm_of_nonneg (by positivity)]; exact le_of_eq (by ring)
lemma pj_M (W:Mat m) {X Y:Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {f g:X→Y→Mat m} (hf:mixed f) (hg:PolyBound g.uncurry) :
    mixed (fun x y=>Pj W (f x y) (g x y)) := by
  let h := fun x y=> ‖etL W‖*‖g x y‖
  apply hf.product (g:=h)
    (show PolyBound h.uncurry from (PolyBound.const _).mul hg.norm)
  intro x y; apply pj_norm.trans
  unfold h; rw [Real.norm_of_nonneg (by positivity)]; exact le_of_eq (by ring)

namespace ProjField
variable [NeZero m] (q:ProjField m) (B:FieldMat m) (W:Mat m)

lemma bMS {f j} (hf:TestF f) (hj:TestF j) : mixed (q.betaK B W f j) ∧
    StronglyMeasurable (q.betaK B W f j).uncurry :=
  by
    have hi := pj_M W (g:=B.eVal j) (q.zm B hf) (B.pEval hj)
    have hh := (pj_cont W).comp_stronglyMeasurable
      ((q.zSM B f).prodMk (B.smEval hj))
    exact ⟨hi,hh⟩

lemma nMS {f j} (hf:TestF f) (hj:TestF j) : mixed (q.nTK W f j) ∧
    StronglyMeasurable (q.nTK W f j).uncurry := by
  let h := fun u:Plane=>deriv f u.1*deriv j u.2
  let l := etL W
  have hm : mixed fun u x=> l (q.edge.NTm u x) := mixed_proj q.edge.nt_mixed l
  have hu : Continuous h := (hf.der.cont.comp continuous_fst).mul (hj.der.cont.comp continuous_snd)
  have hh : PolyBound h := (hf.der.poly.comp PolyBound.fst).mul (hj.der.poly.comp PolyBound.snd)
  have he : q.nTK W f j = fun u x=>h u*l (q.edge.NTm u x) := by
    ext; unfold h l nTK; rw [etL_apply]
  rw [he]
  exact ⟨hm.product (g:=fun u _=>h u) (hh.comp PolyBound.fst) (fun u x=>by rw [norm_mul,mul_comm]),
    (hu.comp continuous_fst).stronglyMeasurable.mul
      ((l.continuous.measurable.comp q.edge.nt_meas).stronglyMeasurable)⟩

lemma ER_P : PolyBound (q.RadiusE B) := q.edge.r_poly.add B.poly.norm
lemma ER_hi (x) :
    q.edge.radius x ≤ q.RadiusE B x ∧ ‖B.A x‖ ≤ q.RadiusE B x :=
  ⟨le_add_of_nonneg_right (norm_nonneg _),le_add_of_nonneg_left (q.edge.r_pos _).le⟩
lemma beyond (x) {z:ℝ} (h:q.RadiusE B x < ‖z‖) : q.EZ B z x=0 := by
  have he := (q.ER_hi B x).1.trans_lt h
  have hf := B.theta_exact z x ((q.ER_hi B x).2.trans_lt h)
  have hi : q.edge.P z x=scalar m (st z) := by
    rw [Real.norm_eq_abs] at he; unfold st; split_ifs with hx
    · rw [abs_of_nonneg hx] at he; rw [q.edge.tend_pos z x he,scalar,one_smul]
    rw [abs_of_neg (lt_of_not_ge hx)] at he; rw [q.edge.tend_neg z x he,scalar,zero_smul]
  change q.edge.P z x-B.Θ z x=_
  rw [hi,sub_eq_zero.mp (show B.Θ z x-scalar m (st z)=0 from hf),sub_self]

lemma crossMS {f j} (hf:TestF f) (hj:TestF j) :
    mixed (q.crossK B W f j) ∧ StronglyMeasurable (q.crossK B W f j).uncurry := by
  let c := fun u:Plane × Rn m=> (u.1.1,u.2)
  let h := fun u:Plane × Rn m=> u.1.2
  have hc : PolyBound c := ((PolyBound.fst.comp PolyBound.fst).prodMk PolyBound.snd)
  have hh : PolyBound h := PolyBound.snd.comp PolyBound.fst
  have he := pj_p (((q.zm B hf).poly).comp hc)
    (((hj.der.poly).comp hh).smul B.Ep) W
  have hm : mixed (q.crossK B W f j) := by
    apply mixed.of_cutoff (f:=q.crossK B W f j) he (q.ER_P B)
    intro u x hx
    by_cases hu : q.RadiusE B x < ‖u.1‖
    · unfold crossK; rw [zE,q.beyond B x hu,smul_zero,← pJ_eq,_root_.map_zero]; rfl
    change _ < max _ _ at hx
    have ht : max ‖u.1‖ ‖B.A x‖ < ‖u.2‖ := by
      have hh := q.ER_hi B x; grind
    unfold crossK; rw [B.vanishEC x u ht,smul_zero,← pJ_eq,_root_.map_zero]
  have h₁ : Measurable c := by unfold c; fun_prop
  have h₂ : Continuous h := by unfold h; fun_prop
  have hi := (pj_cont W).comp_stronglyMeasurable (((q.zSM B f).comp_measurable h₁).prodMk
    (((hj.der.cont.comp h₂).stronglyMeasurable).smul B.Em))
  exact ⟨hm,hi⟩

lemma point_expand_f (x) (f:ℝ→ℝ) (u:Plane) (hu:u.1<u.2) :
    q.nTK W f f u x+Pj W (q.zE B f u.1 x) (q.zE B f u.2 x)=
    q.crossK B W f f u x+q.crossK B W f f u.swap x := by
  set y := u.1; set z:=u.2
  have hh := B.nest x y z hu.le
  unfold nTK Edge.NTm crossK zE
  rw [min_eq_left hu.le,max_eq_right hu.le,pj_scale,pj_scale,pj_scale]
  have HH : u.1<u.2:=hu
  have ha : B.EC u x=1-B.Θ z x := by simp [FieldMat.EC,jump,HH.le,z,scalar]
  have hb : B.EC u.swap x= -B.Θ y x := by simp [FieldMat.EC,jump,not_le_of_gt HH,y,scalar]
  rw [ha,hb]
  let a := q.Pmat y x; let b := q.Pmat z x
  let t := B.Θ y x; let w := B.Θ z x
  have h :
      Pj W a (1-b)+Pj W (a-t) (b-w)=Pj W (a-t) (1-w)+Pj W (b-w) (-t) := by
    unfold Pj jprod
    have hh₁ : t*w=t := hh.1
    have hh₂ : w*t=t := hh.2
    rw [← trN_add, ← trN_add,← mul_add,← mul_add,← smul_add,← smul_add]
    congr 3
    simp only [sub_mul,mul_sub,mul_one,one_mul,neg_mul,mul_neg,hh₁,hh₂]; abel
  change deriv f y*deriv f z*Pj W a (1-b)+ _= _
  change deriv f y*deriv f z*_+deriv f y*(deriv f z*Pj W (a-t) (b-w))=
    deriv f y*(deriv f z*Pj W (a-t) (1-w))+deriv f z*(deriv f y*Pj W (b-w) (-t))
  linear_combination deriv f y*deriv f z*h

lemma point_expand (x) (f:ℝ→ℝ) :
    ∀ᵐ u:Plane,q.nTK W f f u x+Pj W (q.zE B f u.1 x) (q.zE B f u.2 x)=
    q.crossK B W f f u x+q.crossK B W f f u.swap x := by
  filter_upwards [off_diag] with u hu
  rcases lt_or_gt_of_ne hu with h|h; exact q.point_expand_f B W x f u h
  have he := q.point_expand_f B W x f u.swap h
  rw [pj_sym] at he
  simpa [nTK, Edge.NTm, min_comm,max_comm,mul_comm,add_comm] using he

lemma square_pt {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    Pj W (q.MB B f x) (q.MB B f x)+ (∫ u:Plane,q.nTK W f f u x) =
      2*∫ z,q.betaK B W f f z x := by
  let U := fun z=> q.zE B f z x
  let g := fun u:Plane=> q.crossK B W f f u x
  let h := fun u:Plane=> q.nTK W f f u x
  let s := fun u:Plane=> PJ W (U u.1) (U u.2)
  have ig : Integrable g := mixed_integrable_left (q.crossMS B W hf hf).1 x
    (((q.crossMS B W hf hf).2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have ih : Integrable h := mixed_integrable_left (q.nMS W hf hf).1 x
    (((q.nMS W hf hf).2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have iu : Integrable U := q.zi B hf x
  have ih' : Integrable s :=
    by
      have he := iu.op_fst_snd (pj_cont W) ⟨‖etL W‖,(fun x y=> pj_norm)⟩ iu
      unfold s; simp_rw [pJ_eq]; exact he
  have he : (∫ u:Plane,(h u+s u))= ∫ u:Plane,(g u+g u.swap) := by
    apply integral_congr_ae
    filter_upwards [q.point_expand B W x f] with u hu
    simpa only [h,s,g,U,pJ_eq] using hu
  have hs : (∫ u,s u)=Pj W (q.MB B f x) (q.MB B f x) := by
    rw [q.mb_eq B hf,← pJ_eq]
    simp only [_root_.map_neg,_root_.neg_apply,neg_neg]
    exact integral_prod_bilin (PJ W) iu iu
  have ha : (∫ u,g u)=∫ z,q.betaK B W f f z x := by
    rw [show (volume:Measure Plane)=volume.prod volume from rfl,integral_prod _ ig]
    congr 1
    ext z
    unfold betaK g crossK
    simp_rw [← pJ_eq]
    rw [B.gap x z hf]; exact (PJ W _).integral_comp_comm (B.gapM x z hf)
  rw [integral_add ih ih',integral_add ig (show Integrable (fun u:Plane=>g u.swap) volume from ig.swap),
    show (∫ u:Plane,g u.swap)=∫ u,g u from integral_prod_swap _,hs,ha] at he
  linarith
lemma eq15 {f:ℝ→ℝ} (hf:TestF f) :
    Pt W (q.MB B f) (q.MB B f)= 2*q.be B W f f-q.Nt W f f := by
  have he (x) : Pj W (q.MB B f x) (q.MB B f x)=
      2*(∫ z,q.betaK B W f f z x)-(∫ u:Plane,q.nTK W f f u x) :=
    eq_sub_of_add_eq (q.square_pt B W hf x)
  unfold Pt be Nt; simp_rw [he]
  have ih := q.bMS B W hf hf
  have hf := q.nMS W hf hf
  rw [integral_sub,integral_const_mul]
  · exact ((mixed_integrable (μ:=volume) (ν:=normal m) ih.1 ih.2.aestronglyMeasurable).integral_prod_right).const_mul _
  exact (mixed_integrable (μ:=volume) (ν:=normal m) hf.1 hf.2.aestronglyMeasurable).integral_prod_right
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Compare
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer evaluation comparisons (16). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)

omit [NeZero m] in
lemma proj_int (W:Mat m) {f g:Rn m→Mat m} (hf:regular f) (hg:regular g) :
    Integrable (fun x=>PJ W (f x) (g x)) (normal m) := by
  simp_rw [pJ_eq]
  have h := (pj_cont W).comp_aestronglyMeasurable (hf.meas.prodMk hg.meas)
  exact (pj_p hf.p hg.p W).gaussian_integrable
    h
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MatrixDeriv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Derivative of spectral function of linear field. Avoid polynomial
approximation by exact secant identity and Borel frame compactness. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Asymptotics
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

section p
variable {X:Type*} [NormedAddCommGroup X]

-- Tool: matrix-coordinate bounds for moderate functions
omit [NeZero m] in
lemma mat_poly {A:X→Mat m} (ha:∀ i j:Fin m,PolyBound (fun x=>A x i j)) :
    PolyBound A := by
  classical
  let b := fun i j:Fin m=> Matrix.single i j (1:ℝ)

  let h := fun i j (x:X)=> A x i j • b i j
  have he : A=fun x=>∑ i,∑ j,h i j x := by
    ext x i j; simp [h,b,Matrix.sum_apply,Matrix.single, ite_and]
  rw [he]
  apply p_sum (f:=fun i x=>∑ j,h i j x)
  intro i; exact p_sum (f:=h i) (fun j=> (ha i j).smul (PolyBound.const _)) _
lemma unitPoly (v:X→Frm m) :
    PolyBound (fun x=> (v x).val) := PolyBound.of_bound 1 (fun x=> le_of_eq
      (CStarRing.norm_of_mem_unitary (v x).property))
lemma unitStarPoly (v:X→Frm m) :
    PolyBound (fun x=> star (v x).val) := (unitPoly v).mono fun x=> by rw [norm_star]
lemma poly_eig {A:X→Mat m} (hA:PolyBound A) (u:X→Frm m) (i:Fin m) :
    PolyBound (fun x=> (u x).eig (A x) i) := by
  have he : PolyBound (fun x=> (u x).loc (A x)) :=
    ((unitStarPoly u).mul hA).mul (unitPoly u)
  exact (PolyBound.clm (coeffMap i i)).comp he
end p
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_BiWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer functional ℒ and polynomial-growth calculus. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers

namespace Bwt
variable {l g:Plane→ℝ}
lemma sub (h:Bwt l) (hh:Bwt g) : Bwt fun x=> l x-g x :=
  ⟨h.c.sub hh.c,h.p.sub hh.p⟩
lemma mul (h:Bwt l) (hh:Bwt g) : Bwt fun x=> l x*g x :=
  ⟨h.c.mul hh.c,h.p.mul hh.p⟩
lemma fst {f:ℝ→ℝ} (hf:TestF f) : Bwt fun u:Plane=> f u.1 :=
  ⟨hf.cont.comp continuous_fst,hf.poly.comp PolyBound.fst⟩
lemma snd {f:ℝ→ℝ} (hf:TestF f) : Bwt fun u:Plane=> f u.2 :=
  ⟨hf.cont.comp continuous_snd,hf.poly.comp PolyBound.snd⟩
lemma const (c:ℝ) : Bwt fun _=>c := ⟨continuous_const,PolyBound.const _⟩
lemma bar (h:Bwt g) : Bwt (bAv g) := by
  constructor
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f:=fun (u:Plane) t=>g (u.1,along u t)) (h.c.comp (show Continuous (fun u:Plane×ℝ=>(u.1.1,along u.1 u.2)) by unfold along; fun_prop)) _ _
  obtain ⟨C,n,hc,h⟩ := h.p
  refine ⟨C,n,hc,fun u=>?_⟩
  have he (t:ℝ) (hh:t∈Ι (0:ℝ) 1) : ‖g (u.1,along u t)‖≤ C*(1+‖u‖)^n := by
    apply le_trans (h _)
    rw [uIoc_of_le zero_le_one] at hh
    gcongr;
    have ht := mem_Ioc.mp hh
    change max ‖u.1‖ ‖along u t‖ ≤ max _ _
    apply max_le (le_max_left ..)
    change |(1-t)*u.1+t*u.2| ≤ max |u.1| |u.2|
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,abs_of_nonneg ht.1.le,abs_of_nonneg (by linarith [ht.2])]
    rcases max_choice |u.1| |u.2| with h|h
    · have hx := le_max_right |u.1| |u.2|
      rw [h] at *
      nlinarith [ht.1,ht.2]
    have hx := le_max_left |u.1| |u.2|
    rw [h] at *
    nlinarith [ht.1,ht.2]
  have hu := intervalIntegral.norm_integral_le_of_norm_le_const he
  unfold bAv; convert hu using 1 ; first | rfl | simp
lemma bar_eq (h:Bwt g) (u:Plane) :
    bInt g u=(u.2-u.1)*bAv g u := by
  let f := fun t=> ∫ z in u.1..t,g (u.1,z)
  have hf : Continuous (fun z=>g (u.1,z)) := h.c.comp (continuous_const.prodMk continuous_id)
  have hd (t:ℝ) : HasDerivAt f (g (u.1,t)) t := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable ..) (hf.stronglyMeasurableAtFilter volume _) hf.continuousAt
  have hi (t:ℝ) : HasDerivAt (f ∘ along u) (g (u.1,along u t)*(u.2-u.1)) t := by
    apply HasDerivAt.comp t (hd (along u t))
    convert ((((hasDerivAt_const t 1).sub (hasDerivAt_id' t)).mul_const u.1).fun_add
      ((hasDerivAt_id' t).mul_const u.2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | ring
  have HH := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> hi t)
    (((hf.comp (by unfold along; fun_prop)).mul continuous_const).intervalIntegrable (0:ℝ) 1)
  rw [intervalIntegral.integral_mul_const] at HH
  simp [along,f] at HH
  unfold bInt bAv; rw [mul_comm]
  convert HH.symm using 1 ; rfl
end Bwt
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Roots
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Exterior square-root kernel integrals in §05. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Roots

lemma u_pos {t:ℝ} (h:0≤t) : 0<u t := by unfold u; apply sub_pos.mpr; apply Real.sqrt_lt_sqrt h; linarith
lemma u_add {t:ℝ} (h:0≤t) : u t*(√(1+t)+√t)=1 := by
  unfold u
  nlinarith [Real.sq_sqrt h,Real.sq_sqrt (show 0≤1+t by linarith)]
lemma sqrt_top {t:ℝ} (h:0≤t) : √(1+t)=(1+p t)/(2*u t) := by
  have he := u_pos h
  have hh := u_add h
  field_simp
  unfold p; unfold u at *; nlinarith
lemma sqrt_bot {t:ℝ} (h:0≤t) : √t=(1-p t)/(2*u t) := by
  have he := u_pos h; have hh:= u_add h; field_simp
  unfold p; unfold u at *; nlinarith
lemma t_p {t:ℝ} (h:0≤t) : t=(1-p t)^2/(4*p t) := by
  have hp : 0<p t := pow_pos (u_pos h) _
  have he := Real.sq_sqrt h
  rw [sqrt_bot h,div_pow] at he
  calc
    t = _ := he.symm
    _ = _ := by unfold p; ring
lemma p_lt {t:ℝ} (h:0<t) : p t<1 := by
  have he := sqrt_bot h.le
  have hv := Real.sqrt_pos.2 h
  have hu := u_pos h.le
  field_simp at he
  nlinarith
lemma dp {t:ℝ} (h:0<t) :
    HasDerivAt p (-(4*p t^2)/(1-p t^2)) t := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  have hu := u_pos h.le
  have hl := p_lt h
  have ht : 0 <1+t := by linarith
  have he : HasDerivAt u ((1/(2*√(1+t)))-(1/(2*√t))) t :=
    by
      convert ((((hasDerivAt_id' t).const_add 1).sqrt ht.ne').sub ((hasDerivAt_id' t).sqrt h.ne')) using 1
      all_goals try with_reducible_and_instances rfl
      all_goals rfl
  convert he.pow 2 using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | skip
  rw [sqrt_top h.le,sqrt_bot h.le]
  have hs : 1-p t^2≠0 := by nlinarith
  have hv : 1-p t≠0 := by linarith
  norm_num
  field_simp
  unfold p; ring

lemma x_formula {t:ℝ} (h:0<t) :
    xk t=4*p t^3/(1+p t^2) := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  unfold xk
  conv_lhs=> rhs; rw [t_p h.le]
  field_simp
  unfold p; ring

lemma pu_limit : Tendsto p atTop (𝓝 0) := by
  let g := fun t:ℝ=> √(1+t)+√t
  have ht : Tendsto g atTop atTop := by
    apply tendsto_atTop_mono (g:=g) _ Real.tendsto_sqrt_atTop
    intro x; change √x ≤ √(1+x)+√x; linarith [Real.sqrt_nonneg (1+x)]
  have he : Tendsto u atTop (𝓝 0) := by
    apply Tendsto.congr' _ (tendsto_inv_atTop_zero.comp ht)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t h
    have ha := u_pos h; have hh := u_add h
    have hs : g t≠0 := by
      unfold g; positivity
    change (g t)⁻¹=u t
    field_simp
    linarith
  have h := he.pow 2; norm_num at h; exact h
lemma cu : Continuous p := by unfold p u; fun_prop

lemma dfx {t:ℝ} (h:0<t) : HasDerivAt fx (xk t) t := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  have he := ((((((dp h).pow 2).const_add 1).log (by change 1+p t^2≠0; positivity)).sub
    (((dp h).pow 2).div_const 2))).neg
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | skip
  rw [x_formula h]
  have hl:=p_lt h
  have hs : 1-p t^2≠0 := by nlinarith
  norm_num
  field_simp; ring
lemma area_template {f g:ℝ→ℝ} (hf:ContinuousAt f 0) (h:Tendsto f atTop (𝓝 0))
    (hp:∀ t,0<t→ 0≤g t) (hd:∀ t,0<t→HasDerivAt f (g t) t) :
    IntegrableOn g (Ioi 0) ∧ (∫ t in Ioi 0,g t)=-f 0 := by
  have he := integrableOn_Ioi_deriv_of_nonneg hf.continuousWithinAt hd hp h
  refine ⟨he,?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto hf.continuousWithinAt hd he h

lemma x_area :
    IntegrableOn xk (Ioi 0) ∧ (∫ t in Ioi 0,xk t)=Real.log 2 -1/2 := by
  let f := fun x:ℝ=> -(Real.log (1+x^2)-x^2/2)
  have hf : Continuous f := by unfold f; fun_prop (disch:= first | (intro x; positivity) | positivity)
  have hp : Continuous fx := hf.comp cu
  have ht : Tendsto fx atTop (𝓝 0) := by
    have h:= (hf.tendsto 0).comp pu_limit
    change Tendsto fx atTop (𝓝 (f 0)) at h; norm_num [f] at h; exact h
  have hh := area_template hp.continuousAt ht (fun t h=> show 0≤ xk t by unfold xk; positivity)
    (fun t h=>dfx h)
  norm_num [fx,p,u] at hh ⊢
  exact hh

end GeneralMahler.Roots

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Major
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Piecewise kernel square estimates will use these scaled integrable
majorants. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Roots
open Classical

lemma slab_int (f g:ℝ→ℝ) (hf:IntegrableOn f (Ioi 0))
    (hg:Continuous g) :
    Integrable (slab f g) ∧ (∫ x,slab f g x)=(2*∫ x in Ioi 0,f x)+∫ x in Icc 0 1,g x := by
  let l := (Ioi 0).indicator f
  let k := (Icc 0 1).indicator g
  have hl : Integrable l := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hk : Integrable k := (integrable_indicator_iff measurableSet_Icc).mpr hg.integrableOn_Icc
  have hi : Integrable (fun x=>l (-x)) :=
    ((measurePreserving_neg volume).integrable_comp_emb (Homeomorph.neg _).measurableEmbedding).mpr hl
  have hh : Integrable (fun x=>l (x-1)) := by
    simpa [sub_eq_add_neg] using hl.comp_add_right (-1)
  have he : slab f g=fun x=> l (-x)+k x+l (x-1) := by
    ext x
    unfold l k slab
    by_cases h:x<0
    · simp [h,indicator,show ¬0≤x by linarith,show ¬0<x-1 by linarith]
    by_cases ht:x≤1
    · simp [h,ht, indicator, show 0≤x by linarith, show ¬0<x-1 by linarith]
    simp [h,ht,indicator,show 0<x-1 by linarith]
  rw [he]
  refine ⟨(hi.add hk).add hh,?_⟩
  rw [integral_add,integral_add hi hk, integral_neg_eq_self, integral_sub_right_eq_self]
  · unfold l k
    simp_rw [integral_indicator measurableSet_Ioi,integral_indicator measurableSet_Icc]; ring
  all_goals first | exact hi.add hk | exact hh

lemma secU (f:ℝ→ℝ) (q:ℝ) {a:ℝ} (ha:0<a) (hf:Integrable f) :
    Integrable (fun z=>a*f ((z-q)/a)) ∧ (∫ z:ℝ,a*f ((z-q)/a))=a^2*∫ x,f x := by
  have h : Integrable (fun z=> f (z/a)) :=
    by simp_rw [div_eq_mul_inv]; exact (integrable_comp_mul_right_iff f (inv_pos.mpr ha).ne').2 hf
  let l := fun z:ℝ=>f (z/a)
  have hi : Integrable (fun z=>l (z-q)) := by simpa [l,sub_eq_add_neg] using h.comp_add_right (-q)
  constructor
  · exact hi.const_mul _
  rw [integral_const_mul]
  have ht : (∫ z:ℝ,l (z-q))=∫ z,l z := integral_sub_right_eq_self l q
  change a*(∫ z,l (z-q))=_
  rw [ht]
  unfold l
  rw [Measure.integral_comp_div]
  simp [abs_of_pos ha]; ring
lemma U_area (f g:ℝ→ℝ) (hf:IntegrableOn f (Ioi 0)) (hg:Continuous g) (x y:ℝ) :
    Integrable (U f g x y) ∧ (∫ z,U f g x y z)=(x-y)^2*((2*∫ t in Ioi 0,f t)+∫ t in Icc 0 1,g t) := by
  by_cases h:x=y
  · subst y; rw [show U f g x x=(fun _ => (0:ℝ)) from by ext; simp [U] ]; simp
  have hu := secU (slab f g) (min x y) (show 0< |y-x| from abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))) (slab_int f g hf hg).1
  unfold U; convert hu using 1
  rw [sq_abs, (slab_int f g hf hg).2]; ring_nf

lemma g_area : (∫ x in Icc (0:ℝ) 1,gx x)=2/3 := by
  let F := fun t:ℝ=>2*t-4*t^2+8/3*t^3
  have hd (x:ℝ) : HasDerivAt F (gx x) x := by
    convert ((((hasDerivAt_id' x).const_mul 2).sub (((hasDerivAt_id' x).pow 2).const_mul 4)).add
      (((hasDerivAt_id' x).pow 3).const_mul (8/3))) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (norm_num [F,gx]; ring)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>hd x) ((by unfold gx; fun_prop :
      Continuous gx).intervalIntegrable ..)]
  unfold F; ring

lemma Ux_area (x y:ℝ) :
    Integrable (Ux x y) ∧ (∫ z,Ux x y z)=(2*Real.log 2-1/3)*(x-y)^2 := by
  have h := U_area _ _ x_area.1 (by unfold gx; fun_prop : Continuous gx) x y
  rw [x_area.2,g_area] at h; exact ⟨h.1,h.2.trans (by ring)⟩
lemma U_swap (f g) (x y z) : U f g x y z=U f g y x z := by rw [U,U,abs_sub_comm,min_comm]
lemma U_outHi (f g) {x y z:ℝ} (hx:x<y) (hy:y<z) :
    U f g x y z=(y-x)*f ((z-y)/(y-x)) := by
  have h:= sub_pos.mpr hx
  have he : 1<(z-x)/(y-x) := by rw [lt_div_iff₀ h]; linarith
  rw [U,abs_of_pos h,min_eq_left hx.le,slab,ite_eq_right (by linarith),ite_eq_right (by linarith)]
  congr 2; field_simp; ring
lemma U_outLo (f g) {x y z:ℝ} (hx:x<y) (hy:z<x) :
    U f g x y z=(y-x)*f ((x-z)/(y-x)) := by
  have h:= sub_pos.mpr hx
  rw [U,abs_of_pos h,min_eq_left hx.le,slab,ite_eq_left (div_neg_of_neg_of_pos (sub_neg.mpr hy) h)]
  congr 2; ring
lemma U_mid (f g) {x y z:ℝ} (hx:x<z) (hy:z<y) :
    U f g x y z=(y-x)*g ((z-x)/(y-x)) := by
  have h:= sub_pos.mpr (hx.trans hy)
  rw [U,abs_of_pos h,min_eq_left (by linarith),slab,
    ite_eq_right (not_lt_of_ge (div_nonneg (by linarith) h.le)),ite_eq_left]; rw [div_le_iff₀ h]; linarith
end GeneralMahler.Roots

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Segment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar exterior and middle estimates via Cauchy--Schwarz. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Interval
namespace GeneralMahler.Seg
open Roots Layers

lemma integral_sq_le (f:ℝ→ℝ) (hf:Continuous f) (a b:ℝ) (h:a≤b) :
    (∫ x in a..b,f x)^2 ≤ (b-a)*∫ x in a..b,f x^2 := by
  rcases h.eq_or_lt with rfl|h
  · simp
  have ht : 0<b-a := sub_pos.mpr h
  let c := (∫ x in a..b,f x)/(b-a)
  have hq : (∫ x in a..b,f x)=c*(b-a) := by unfold c; field_simp
  have hp := intervalIntegral.integral_nonneg h.le (f:=fun x=>(f x-c)^2)
    (μ:=volume) (fun x _=>sq_nonneg _)
  have hi (x) : (f x-c)^2=f x^2-(2*c)*f x+c^2 := by ring
  simp_rw [hi] at hp
  rw [intervalIntegral.integral_add,intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hp
  · rw [hq] at *
    change 0≤ _-_+(b-a)*c^2 at hp
    nlinarith [mul_nonneg hp ht.le]
  all_goals first | exact (hf.pow _).intervalIntegrable .. |
    exact ((continuous_const.mul hf).intervalIntegrable ..) |
    exact (continuous_const.intervalIntegrable ..) |
    exact (((hf.pow _).sub (continuous_const.mul hf)).intervalIntegrable ..)
lemma bar_sq (g:Plane→ℝ) (hg:Bwt g) (u:Plane) :
    bAv g u^2 ≤ bAv (fun v=>g v^2) u := by
  have hh := integral_sq_le (fun x=>g (u.1,along u x)) (hg.c.comp
    (by unfold along; fun_prop)) 0 1 zero_le_one
  simpa [bAv] using hh

lemma r_swap (x y z) : rcoef x y z=rcoef y x z := by
  unfold rcoef
  by_cases h:signE x z=signE y z
  · simp only [h,↓reduceIte]; ring
  simp [h,Ne.symm h]
lemma K_swap (f) (x y z) : kz f x y z=kz f y x z := by
  unfold kz; rw [r_swap]; ring
lemma O_swap (f) (x y z) : Om f x y z=Om f y x z := by unfold Om; ring
lemma bar_const (x:Plane) : bAv (fun _=>1) x=1 := by unfold bAv; simp

lemma middle (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hx:x<z) (hy:z<y) :
    kz f x y z ^2≤Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2≤Om (fun _=>1) x y z* Ux x y z := by
  have ha : x≤ z := hx.le
  have he : rcoef x y z=0 := by unfold rcoef signE; norm_num [not_lt_of_ge ha,hy]
  let a := z-x
  let b := y-z
  let V := fun t => bAv f (z,t)
  let W := fun t => bAv (fun u=>f u^2) (z,t)
  have hp : 0<a := sub_pos.mpr hx
  have hh : 0<b := sub_pos.mpr hy
  have hu : y-x=a+b := by unfold a b; ring
  unfold kz Om Uy Ux
  rw [he,U_mid xk gx hx hy,U_mid yk _ hx hy,abs_of_neg (sub_neg.mpr hx),abs_of_pos (sub_pos.mpr hy)]
  have hh₁ : x-z= -a := by unfold a; ring
  rw [hh₁,neg_neg]
  constructor
  · change ((-a*V x+b*V y-0*_)/2)^2 ≤ (a*W x+b*W y)/2*((y-x)*(1/2))
    have hv : (a*V x-b*V y)^2 ≤ (a+b)*(a*W x+b*W y) :=
      calc
        _ ≤ (a+b)*(a*V x^2+b*V y^2) := by nlinarith [mul_nonneg (mul_nonneg hp.le hh.le) (sq_nonneg (V x+V y))]
        _ ≤ _ := by
          have hX : V x^2≤W x := bar_sq f hf _
          have hY : V y^2≤W y := bar_sq f hf _
          gcongr
    rw [hu]; nlinarith
  simp_rw [bar_const]
  unfold gx; rw [hu]
  have hh₂ : z-x=a := rfl
  rw [hh₂]; apply le_of_eq; field_simp; ring

-- parameterized ray ε, near z+ε*b, far z+ε*a.
lemma av_dist (f:Plane→ℝ) (z sig b:ℝ) (_hb:0<b) :
    bAv f (z,z+sig*b)*b = ∫ t in 0..b,f (z,z+sig*t) := by
  let g := fun t=>f (z,z+sig*t)
  have hh := intervalIntegral.smul_integral_comp_mul_left g (a:=0) (b:=1) b
  unfold bAv
  have he (t:ℝ) : f ((z,z+sig*b).1,along (z,z+sig*b) t) = g (b*t) := by
    unfold along g; dsimp; congr 2; ring
  simp_rw [he]
  simpa only [mul_zero,mul_one,smul_eq_mul,mul_comm b,zero_mul,one_mul,g] using hh

lemma ext_shape {a b:ℝ} (ha:0<b) (h:b<a) :
    let l:=a-b
    l*xk (b/l)=(√a-√b)^4/( (a+b)/2) ∧
      l*yk (b/l)=(√a-√b)^2/2*((a-b)/a+(1-√b/√a)^2/2) := by
  intro l
  have hl : 0<l:= sub_pos.mpr h
  have hp : 0<a:=ha.trans h
  have ht : 1+b/l=a/l := by field_simp; unfold l; ring
  unfold xk yk u
  rw [ht,Real.sqrt_div ha.le,Real.sqrt_div hp.le]
  have hk:= Real.sq_sqrt hl.le
  have he:= Real.sqrt_pos.mpr hp; have hh:=Real.sqrt_pos.mpr hl
  have hb : 1+2*(b/l)>0 := by positivity
  constructor
  all_goals field_simp
  · rw [show √l^4=l^2 by rw [show (4:ℕ)=2*2 from rfl,pow_mul,hk] ]
    unfold l; ring
  rw [hk]; unfold l; ring

-- exterior, parameterized orientation. U replaced analytic RHS.
lemma K_ext (f:Plane→ℝ) (hf:Bwt f) (z s a b:ℝ) (hs:s=1 ∨ s= -1)
    (hp:0<b) (h:b<a) :
    let x:=z+s*b
    let y:=z+s*a
    let l:=a-b
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z*(l*yk (b/l)) ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z*(l*xk (b/l)) := by
  intro x y l
  have ha : 0<a:=hp.trans h
  set A:=√a; set B:=√b
  have hA : 0<A:= Real.sqrt_pos.mpr ha
  have hB : 0<B:= Real.sqrt_pos.mpr hp
  have HB : B^2=b := Real.sq_sqrt hp.le
  have HA : A^2=a := Real.sq_sqrt ha.le
  let g := fun t=>f (z,z+s*t)
  have hg : Continuous g := hf.c.comp (by fun_prop)
  let R := fun t=> bAv f (z,z+s*t)
  let P := fun t=> bAv (fun u=> f u^2) (z,z+s*t)
  let x₁:=∫ t in b..a,g t
  let x₂:=∫ t in 0..b,g t
  let y₁:=∫ t in b..a,g t^2
  let y₂:=∫ t in 0..b,g t^2
  have hi : R b*b=x₂ ∧ R a*a=x₂+x₁ ∧ P b*b=y₂ ∧ P a*a=y₂+y₁ := by
    have he := hg.intervalIntegrable (μ:=volume)
    have hh := (hg.pow 2).intervalIntegrable (μ:=volume)
    exact ⟨av_dist f z s b hp,(av_dist f z s a ha).trans
      (intervalIntegral.integral_add_adjacent_intervals (he ..) (he ..)).symm,
      av_dist _ z s b hp,(av_dist _ z s a ha).trans
        (intervalIntegral.integral_add_adjacent_intervals (hh ..) (hh ..)).symm⟩
  obtain ⟨hx,hx',hy,hy'⟩:=hi
  have he : (A*R a-B*R b)^2 ≤ (a*P a+b*P b)*((a-b)/a+(1-B/A)^2/2) := by
    have h₁:= integral_sq_le g hg b a h.le
    have h₂:= integral_sq_le g hg 0 b hp.le; rw [sub_zero] at h₂
    change x₁^2≤l*y₁ at h₁
    change x₂^2≤b*y₂ at h₂
    have hl : 0<l:= sub_pos.mpr h
    let d:=1/A; let c:=1/A-1/B
    have hh : (d*x₁+c*x₂)^2 ≤ (d^2*l+c^2*b/2)*(y₁+2*y₂) := by
      have he := add_le_add ((div_le_iff₀ hl).mpr (h₁.trans_eq (mul_comm ..))) (mul_le_mul_of_nonneg_left ((div_le_iff₀ hp).mpr (h₂.trans_eq (mul_comm ..)))
        (show (0:ℝ)≤2 by norm_num))
      apply le_trans _ (mul_le_mul_of_nonneg_left he (by positivity))
      field_simp
      nlinarith [sq_nonneg (2*d*l*x₂-c*b*x₁)]
    have hz : d*x₁+c*x₂=A*R a-B*R b := by
      unfold d c
      rw [show x₁=R a*a-R b*b by linarith,← hx,← HA,← HB]
      field_simp; ring
    have hq : d^2*l+c^2*b/2=(a-b)/a+(1-B/A)^2/2 := by
      unfold d c l; rw [← HA,← HB]; field_simp; ring
    rw [hz,hq] at hh
    have hi : y₁+2*y₂=a*P a+b*P b := by linarith
    rw [hi] at hh; linarith
  have ht : |x-z|=b ∧ |y-z|=a ∧ x-z=s*b ∧ y-z=s*a ∧ rcoef x y z=s*B*A := by
    unfold x y rcoef signE
    rcases hs with h|h <;> subst s <;> simp [A,B,hp,ha,not_lt_of_ge hp.le,not_lt_of_ge ha.le,abs_of_pos]
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := ht
  obtain ⟨h₆,h₇⟩ := ext_shape hp h
  have hs' : s^2=1 := by rcases hs with rfl|rfl<;>ring
  unfold kz Om
  rw [h₅,h₁,h₂,h₃,h₄]
  constructor
  · change ((s*b*R b+s*a*R a-s*B*A*(R b+R a))/2)^2 ≤ (b*P b+a*P a)/2*(l*yk (b/l))
    rw [h₇]
    change _≤(b*P b+a*P a)/2*((A-B)^2/2*((a-b)/a+(1-B/A)^2/2))
    apply le_trans _ (by
      have h := mul_le_mul_of_nonneg_left he (show 0 ≤ (A-B)^2/4 by positivity)
      exact h.trans_eq (by ring))
    apply le_of_eq
    calc
      _ = s^2*((A-B)^2/4)*(A*R a-B*R b)^2 := by rw [← HA,← HB]; ring
      _ = _ := by rw [hs',one_mul]
  simp_rw [bar_const]
  rw [h₆]
  apply le_of_eq
  change _= _*((A-B)^4 / _)
  field_simp
  rw [← HA,← HB]
  rcases hs with h|h <;> rw [h] <;> ring

lemma k_same (f) (z x:ℝ) :
    kz f x x z=0 := by
  unfold kz rcoef
  rw [ite_eq_left rfl, mul_assoc (signE x z) (√|x-z|) (√|x-z|),← pow_two, Real.sq_sqrt (abs_nonneg _)]
  unfold signE; split_ifs with h
  · rw [abs_of_pos (sub_pos.mpr h)]; ring
  rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]; ring

lemma pairOrd (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hx:x<y) (hy:z≠x) (hz:z≠y) :
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z* Ux x y z := by
  unfold Uy Ux
  rcases lt_or_gt_of_ne hy with h|h
  · rw [U_outLo _ _ hx h,U_outLo _ _ hx h]
    have hh := K_ext f hf z 1 (y-z) (x-z) (Or.inl rfl) (sub_pos.mpr h)
      (show x-z<y-z by linarith)
    simpa only [one_mul,add_sub_cancel,sub_sub_sub_cancel_right] using hh
  rcases lt_or_gt_of_ne hz with h'|h'
  · exact middle f hf h h'
  rw [U_outHi _ _ hx h',U_outHi _ _ hx h',K_swap,O_swap,K_swap (fun _=>1),O_swap (fun _=>1)]
  have hh := K_ext f hf z (-1) (z-x) (z-y) (Or.inr rfl) (sub_pos.mpr h')
    (show z-y<z-x by linarith)
  simpa only [neg_one_mul,← sub_eq_add_neg,sub_sub_cancel,sub_sub_sub_cancel_left] using hh

lemma pairEst (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hy:z≠x) (hz:z≠y) :
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z* Ux x y z := by
  rcases lt_trichotomy x y with h|rfl|h
  · exact pairOrd f hf h hy hz
  · simp only [k_same,Ux,Uy,U,sub_self,abs_zero]; norm_num
  rw [K_swap,O_swap,K_swap (fun _=>1),O_swap (fun _=>1),Ux,U_swap,Uy,U_swap]
  exact pairOrd f hf h hz hy
end GeneralMahler.Seg

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LFun
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! ℒ evaluation; linearity and spectral form. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

lemma Bwt.indef {f:Plane→ℝ} (hf:Bwt f) : Bwt (bInt f) := by
  rw [show bInt f=_ from funext hf.bar_eq]
  apply Bwt.mul _ hf.bar
  exact (Bwt.snd TestF.id).sub (Bwt.fst TestF.id)

namespace FieldMat
variable (B:FieldMat m)
omit [NeZero m] in
lemma bmat_loc (f:Plane→ℝ) (z x) :
    (B.Fr x).loc (B.bmat f z x)=Matrix.diagonal (fun i=>f (z,B.ev x i)) := B.evfrm ..

omit [NeZero m] in
lemma bsmb {f:Plane→ℝ} (hf:Bwt f) :
    StronglyMeasurable (B.bmat f).uncurry :=
  (B.theta_gen_meas (f:=fun x y=>f (x,y)) (by exact hf.c.measurable)).stronglyMeasurable
lemma p_bmat {f:Plane→ℝ} (hf:Bwt f) :
    PolyBound (B.bmat f).uncurry := by
  let u := fun w:ℝ×Rn m=> B.Fr w.2
  let D := fun w:ℝ×Rn m=>Matrix.diagonal (fun i=>f (w.1,B.ev w.2 i))
  have he (w:ℝ×Rn m): (B.bmat f).uncurry w=(u w).val*D w*star (u w).val :=
    B.evfrm' w.2 _
  rw [funext he]
  have hp : PolyBound D := by
    apply mat_poly
    intro i j
    have hg : PolyBound (fun w:ℝ×Rn m=> f (w.1,B.ev w.2 i)) :=
      hf.p.comp (PolyBound.fst.prodMk
        ((poly_eig B.poly B.Fr i).comp PolyBound.snd))
    by_cases hi:i=j
    · subst j; simpa only [D,Matrix.diagonal_apply_eq] using hg
    · unfold D; simp_rw [Matrix.diagonal_apply_ne _ hi]; exact PolyBound.const _
  exact ((unitPoly u).mul hp).mul (unitStarPoly u)
end FieldMat

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)

lemma lkMS {f} (hf:Bwt f) :
    mixed (q.lk B W f) ∧ StronglyMeasurable (q.lk B W f).uncurry := by
  have he := pj_M W (q.eM B) (B.p_bmat hf.indef)
  have hh := (pj_cont W).comp_stronglyMeasurable ((q.eSM B).prodMk (B.bsmb hf.indef))
  exact ⟨he,hh⟩
lemma lk_slice_i {f} (hf:Bwt f) (x) : Integrable fun z=>q.lk B W f z x := by
  have he := q.lkMS B W hf
  exact mixed_integrable_left he.1 x
    ((he.2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
lemma Lbar_i {f} (hf:Bwt f) : Integrable (fun x=>∫ z,q.lk B W f z x) (normal m) := by
  have he := q.lkMS B W hf
  exact (mixed_integrable (μ:=volume) (ν:=normal m) he.1 he.2.aestronglyMeasurable).integral_prod_right

omit [NeZero m] in
lemma Le_id {f j} (_hf:TestF f) (hj:TestF j) :
    q.LLw B W (fun u=>deriv f u.1*deriv j u.2) = q.be B W f j := by
  let h := fun u:Plane=> deriv f u.1*deriv j u.2
  have he (u:Plane) : bInt h u=deriv f u.1*(j u.2-j u.1) := by
    unfold bInt h
    dsimp only; rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_deriv_eq_sub]
    · exact fun x _=>hj.diff x
    exact hj.der.cont.intervalIntegrable ..
  have h₁ (z x) : B.bmat (bInt h) z x = deriv f z • B.eVal j z x := by
    let u:=B.Fr x
    apply u.loc_inj; rw [u.loc_smul, show u.loc (B.bmat (bInt h) z x)=_ from B.bmat_loc ..,
      FieldMat.eVal,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.eval j x)=_ from B.evfrm x j]
    ext i k
    by_cases hh:i=k
    · subst k; simp [he]
    simp [hh]
  unfold LLw be
  change (∫ x,(∫ z,q.lk B W h z x) ∂normal m)= _
  have h₂ (x z) : q.lk B W h z x=q.betaK B W f j z x := by
    unfold lk betaK zE; rw [h₁]
    have hi := pj_scale 1 (deriv f z) W (q.EZ B z x) (B.eVal j z x)
    have hj := pj_scale (deriv f z) 1 W (q.EZ B z x) (B.eVal j z x)
    simp only [one_mul,one_smul] at hi hj
    rw [hi,hj]
  simp_rw [h₂]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Blocks
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Algebra of the positive layer blocks (with no commutation
assumptions). All entries here are in a fixed spectral frame. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Seg Roots Layers Profile
variable {m:ℕ}
lemma symm_entry {A:Mat m} (h:A.IsHermitian) (i j) : A i j=A j i := by
  have he:= congrFun (congrFun h i) j; simpa using he.symm
lemma trace_pair (A B:Mat m) : trN (A*B)=mats (fun i=>∑ j,A i j*B j i) := by
  unfold trN trace mats; rfl
lemma traceDiag (A:Mat m) (f:Fin m→ℝ) :
    trN (A*Matrix.diagonal f)=mats (fun i=>A i i*f i) := by
  unfold trN trace mats; simp only [Matrix.diag,Matrix.mul_diagonal]
lemma hsN_eq (A:Mat m) : hsN A=mats (fun i=>∑ j,A i j^2) := by
  rw [hsN,trace_pair]; congr 1; ext; simp [pow_two]
lemma hsN_pos (A:Mat m) : 0 ≤ hsN A := by rw [hsN_eq]; unfold mats; positivity
lemma hsN_loc (A:Mat m) (u:Frm m) : hsN (u.loc A)=hsN A := by
  rw [hsN,hsN,← u.loc_star,← u.loc_mul,trN,trN,u.loc_trace]

lemma cmu_eig (A B:Mat m) (u:Frm m) (he:u.Dgn A) :
    hsN (cmu A B)=mats (fun i=>∑ j,(u.eig A i-u.eig A j)^2 * (u.loc B i j)^2) := by
  rw [← hsN_loc (cmu A B) u,hsN_eq]
  unfold cmu
  rw [u.loc_sub,u.loc_mul,u.loc_mul,show u.loc A=_ from he]
  congr 1; ext i; apply Finset.sum_congr rfl; intro j _
  rw [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

lemma mats_add (f g:Fin m→ℝ) :
    mats (fun i=>f i+g i)=mats f+mats g := by unfold mats; rw [Finset.sum_add_distrib,add_div]
lemma mats_s (a:ℝ) (f:Fin m→ℝ) :
    mats (fun i=>a*f i)=a*mats f := by unfold mats; rw [← Finset.mul_sum]; ring
lemma mats_le {f g:Fin m→ℝ} (h:∀ i,f i≤g i) : mats f ≤ mats g := by unfold mats; gcongr; apply h

namespace block
variable (b:block m)

lemma az (i:Fin m) : b.a i*b.L i=b.x i-b.z := by
  unfold a L signE; split_ifs with h
  · rw [abs_of_pos (sub_pos.mpr h)]; ring
  rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]; ring
lemma Sspec (i j) :
    b.S i j = (if b.L i=b.L j then b.L i*√(b.a i)*√(b.a j) else 0)*b.E i j := rfl
lemma Her : b.E.IsHermitian :=
  b.hp.posSemidef.1.sub (Matrix.isHermitian_diagonal_iff.mpr fun _=> rfl)
lemma Spar : 0≤b.S := by
  let f := fun i=> if b.z<b.x i then √(b.a i) else 0
  let g := fun i=> if b.z<b.x i then 0 else √(b.a i)
  let F := Matrix.diagonal f
  let G := Matrix.diagonal g
  have hp (f:Fin m→ℝ) : (Matrix.diagonal f).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr fun _=> rfl
  have hi := add_nonneg (sand_nonneg b.hp (hp f)) (sand_nonneg (sub_nonneg.mpr b.hi) (hp g))
  apply hi.trans_eq
  change F*b.P*F+G*(1-b.P)*G=b.S
  ext i j
  unfold F G
  rw [Matrix.add_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.diagonal_mul,b.Sspec]
  unfold f g E jump L signE
  by_cases h:i=j
  · subst j
    rcases lt_or_ge b.z (b.x i) with h|h
    · simp [h,not_le_of_gt h]; ring
    simp [h,not_lt_of_ge h]; ring
  by_cases h₁:b.z<b.x i <;> by_cases h₂:b.z<b.x j <;>
    norm_num [h,h₁,h₂] <;> ring

lemma Sdiag (i) : b.S i i=b.a i*b.L i*b.E i i := by
  rw [b.Sspec,ite_eq_left rfl,mul_assoc (b.L i),← pow_two,Real.sq_sqrt]
  · ring
  exact abs_nonneg _
lemma Ed2 (i) :
    (∑ j,b.E i j^2) ≤ b.L i*b.E i i := by
  have he (A:Mat m) (h:A.IsHermitian) : (∑ j,A i j^2)=(A*A) i i := by
    rw [Matrix.mul_apply]; congr 1; ext j; rw [symm_entry h i j, pow_two]
  rw [he b.E b.Her,E,sub_mul,mul_sub,mul_sub]
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.diagonal_apply_eq]
  have hi : b.P*b.P ≤ b.P := by
    have hu : Commute b.P (1-b.P) := (Commute.one_right _).sub_right (Commute.refl _)
    have h := mul_comm_nonneg b.hp (sub_nonneg.mpr b.hi) hu
    rwa [mul_sub,mul_one,sub_nonneg] at h
  have hz : 0 ≤ (b.P-b.P*b.P) i i := (Matrix.le_iff.mp hi).diag_nonneg
  unfold L signE jump; split_ifs <;> simp only [Matrix.sub_apply] at * <;> grind

lemma tr_blk (w:Fin m→ℝ) (hw:∀ i,0≤w i) :
    mats (fun i=> ∑ j,(b.a i*w i+b.a j*w j)/2*b.E i j^2) ≤
    mats (fun i=>b.S i i*w i) := by
  have he :
      (∑ i,∑ j,(b.a i*w i+b.a j*w j)/2*b.E i j^2)=
      ∑ i,b.a i*w i*∑ j,b.E i j^2 := by
    have h (i j) :
        (b.a i*w i+b.a j*w j)/2*b.E i j^2=
        (b.a i*w i*b.E i j^2+b.a j*w j*b.E j i^2)/2 := by rw [symm_entry b.Her i j]; ring
    let F := fun i j=> b.a i*w i*b.E i j^2
    simp_rw [h,← Finset.sum_div,Finset.sum_add_distrib, Finset.mul_sum]
    change ((∑ i,∑ j,F i j)+(∑ j,∑ i,F i j))/2=∑ i,∑ j,F i j
    rw [Finset.sum_comm]; ring
  unfold mats
  rw [he]
  gcongr
  change _ ≤ b.S i i*w i
  rw [b.Sdiag]
  apply le_trans (mul_le_mul_of_nonneg_left (b.Ed2 _) (mul_nonneg (abs_nonneg _) (hw _)))
  apply le_of_eq; unfold a; ring

end block
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Prim
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar primitive conventions and calculus for §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Profile
open Layers
lemma id_ga : ga (fun x=>x)=0 := by
  simpa [ga] using ga_parts (TestF.const 1)
end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Forms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Forms on the Hermite coefficients. D and sigma in paper §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}

lemma pj_poly_part {f: Rn m→Mat m} (hf:regular f) (W:Mat m) :
    Integrable (fun x=>Pj W (f x) (f x)) (normal m) := by
  simp_rw [← pJ_eq]
  exact ProjField.proj_int W hf hf

namespace ProjField
variable [NeZero m] (q:ProjField m)

lemma R_reg : regular q.RR :=
  ⟨q.A_poly.sub q.L_poly,q.A_SM.aestronglyMeasurable.sub q.L_cont.aestronglyMeasurable⟩
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_FormSquare
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §04 profile quadratic identity. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]

namespace ProjField

variable (q:ProjField m)

lemma evId (x:Rn m) : q.FL.eval (fun x=> x) x=q.Lmat x := by
  unfold FieldMat.eval
  rw [cfc_id' ℝ _ (show IsSelfAdjoint (q.FL.A x) from q.FL.sym x)]; rfl

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LowDegree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Linear chaos coefficients for balance. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
omit [NeZero m] in
lemma Mzero (x:Rn m) : MM 0 x=1 := by simp only [MM]; simp [H]
omit [NeZero m] in
lemma Mi1 (i:Fin m) (x:Rn m) : MM (inc 0 i) x=x i := by
  rw [inc,factor_upd]; simp [H,sn]

omit [NeZero m] in
lemma cof_subm {f g:Rn m→Mat m} (hf:regular f) (hg:regular g) (a:MI m) :
    cof (fun x=>f x-g x) a=cof f a-cof g a := by
  unfold cof; simp_rw [smul_sub]; rw [integral_sub (i_cof hf.p hf.meas a) (i_cof hg.p hg.meas a)]

omit [NeZero m] in
lemma l_reg : regular q.Lmat := ⟨q.L_poly,q.L_cont.aestronglyMeasurable⟩
lemma a_reg : regular q.Amat := ⟨q.A_poly,q.A_SM.aestronglyMeasurable⟩
omit [NeZero m] in
lemma coL (a:MI m) :
    cof q.Lmat a=∑ i:Fin m,(if a=inc 0 i then (1:ℝ) else 0) • q.M i := by
  classical
  have hi (i:Fin m) : Integrable (fun x:Rn m=> (MM a x*x i) • q.M i) (normal m) := by
    have h := ((M_poly a).mul (PolyBound.clm (coord i)))
    exact ((h.gaussian_integrable (μ:=normal m)
      ((M_cont a).mul (coord i).continuous).aestronglyMeasurable).smul_const _)
  have he (x:Rn m) : MM a x • q.Lmat x=∑ i:Fin m,(MM a x*x i) • q.M i := by
    unfold Lmat; rw [Finset.smul_sum]; simp only [smul_smul]
  unfold cof; simp_rw [he]; rw [integral_finsetSum]
  · simp_rw [integral_smul_const, ← Mi1, M_inner]
  exact fun i _=>hi i

omit [NeZero m] in
lemma coL_o {a:MI m} (h:deg a ≠ 1) : cof q.Lmat a=0 := by
  have he (i:Fin m):a≠ inc 0 i := by
    intro h'; rw [h',deg_inc,dz _ |>.mpr rfl] at h; exact h rfl
  rw [q.coL]; simp [he]
lemma MB_id :
    q.MB q.FL (fun x=>x)=q.RR := by
  ext x
  unfold MB RR; rw [q.evId,Profile.id_ga]; simp [scalar,Amat]; rfl

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Parity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Parity of Gaussian fields and coefficient projections. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

namespace ProjField
variable (q:ProjField m)
variable [NeZero m]

lemma bal_cf (h:q.avgA=0) (a:MI m) (hd:deg a < 2) : cof q.RR a=0 := by
  unfold RR
  rw [cof_subm q.a_reg q.l_reg]
  by_cases hh:a=0
  · subst a; rw [q.coL_o (by simp [deg])]
    unfold cof; simp_rw [Mzero]; simp only [one_smul,sub_zero]; exact h
  obtain ⟨i,hi⟩ : ∃ i,a i≠0 := by by_contra! hb; exact hh (funext hb)
  set b := decM a i
  have he : a=inc b i := (inc_dec a i hi).symm
  have hb : b=0 := by
    rw [he,deg_inc] at hd
    apply (dz b).mp; omega
  rw [hb] at he
  rw [he,q.coL]
  have ht : cof q.Amat (inc 0 i)=q.M i := by
    unfold cof; simp_rw [Mi1]; rfl
  rw [ht,Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp
  intro j hj hj'
  have hh : inc (0:MI m) i≠ inc 0 j := by
    intro hi
    have he := congrFun hi i
    simp [inc, Ne.symm hj'] at he
  simp [hh]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Degree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Per Gaussian degree proof of the form estimate Eq19. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile HMode Layers
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma j_same (A:Mat m) : jprod A A=A*A := by unfold jprod; module
omit [NeZero m] in
lemma p_le_p {W T A:Mat m} (h:W≤T) (hh:A.IsHermitian) :
    Pj W A A≤ Pj T A A := by simp only [Pj,j_same]; apply trN_mul_mono h (sqPSD hh)
namespace ProjField
variable (q:ProjField m)
lemma r_sym (x) : (q.RR x).IsHermitian :=
  (q.H_hermitian poly_id_der x).sub (q.L_sym x)

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Extract
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Frame decomposition of layer functionals. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ}
lemma bjdiag (b:Fin m→ℝ) (A C:Mat m) :
    trN (A*jprod C (diagonal b)) =
      mats (fun i=>∑ j,A i j*C j i*((b i+b j)/2)) := by
  rw [trace_pair]
  unfold jprod
  congr 1; ext i
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply,Matrix.add_apply, Matrix.mul_diagonal,Matrix.diagonal_mul,smul_eq_mul]
  ring
lemma bjdiag' (b:Fin m→ℝ) (A C:Mat m) (ha:A.IsHermitian) (hc:C.IsHermitian) :
    trN (A*jprod C (diagonal b)) =
      mats (fun i=>∑ j,C i j*A j i*((b i+b j)/2)) := by
  rw [bjdiag]; congr 1
  ext i; apply Finset.sum_congr rfl
  intro j _; rw [symm_entry ha,symm_entry hc]; ring
lemma Frm.trNL (u:Frm m) (A:Mat m) : trN (u.loc A)=trN A := by unfold trN; rw [u.loc_trace]
lemma Frm.pjL (u:Frm m) (W A C:Mat m) : Pj (u.loc W) (u.loc A) (u.loc C)=Pj W A C := by
  have he : jprod (u.loc A) (u.loc C)=u.loc (jprod A C) := by
    unfold jprod; rw [u.loc_smul,u.loc_add,u.loc_mul,u.loc_mul]
  unfold Pj; rw [he,← u.loc_mul,u.trNL]
lemma Frm.HL (u:Frm m) {A:Mat m} (h:A.IsHermitian) :
    (u.loc A).IsHermitian := by
  change star (u.loc A)= _
  rw [← u.loc_star,show star A=A from h]

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

lemma BLe (x z) : (q.BL B x z).E=(B.Fr x).loc (q.EZ B z x) := by
  unfold BL block.E EZ
  rw [Frm.loc_sub,FieldMat.Θ,B.evfrm]

lemma lin_w {f} (h:Bwt f): Bwt (linW f) :=
  ((Bwt.snd TestF.id).sub (Bwt.fst TestF.id)).mul h
section
variable [NeZero m]

lemma bmMS {f} (h:Bwt f) : mixed (q.bmZ B f)∧StronglyMeasurable (q.bmZ B f).uncurry := by
  have hm := pj_M (1:Mat m) (q.eM B) (B.p_bmat (lin_w h))
  have hh := (pj_cont (1:Mat m)).comp_stronglyMeasurable ((q.eSM B).prodMk
    (B.bsmb (lin_w h)))
  exact ⟨hm,hh⟩
lemma bmh {f} (h:Bwt f) (x) : Integrable (fun z=>q.bmZ B f z x) := by
  have hi := q.bmMS B h
  exact mixed_integrable_left hi.1 x
    ((hi.2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
lemma bmah {f} (h:Bwt f) : Integrable (fun x=>∫ z,q.bmZ B f z x) (normal m) := by
  have hi := q.bmMS B h
  exact (mixed_integrable (μ:=volume) (ν:=normal m) hi.1 hi.2.aestronglyMeasurable).integral_prod_right

end

lemma bm_trace (x z f) :
    let b := q.BL B x z
    q.bmZ B f z x=mats (fun i=> b.S i i*f (z,b.x i)) := by
  intro b
  let u := B.Fr x
  rw [bmZ, ← u.pjL]
  rw [u.loc_one,← q.BLe,B.bmat_loc,Pj,one_mul,trN_j,traceDiag]
  congr 1; ext i
  change b.E i i *linW f (z,b.x i)=_
  unfold linW
  rw [b.Sdiag,b.az]
  rw [show b.z=z from rfl]; ring

lemma LL_Bw (x z) {f:Plane→ℝ} (hf:Bwt f) :
    q.lk B 1 f z x=q.bmZ B (bAv f) z x := by
  unfold lk bmZ
  congr 2
  funext u
  exact hf.bar_eq u

lemma pairing_layer (x z) {f:Plane→ℝ} (hf:Bwt f) (ht:T.IsHermitian) :
    let b:=q.BL B x z
    let u:=B.Fr x
    let t:=u.loc T
    q.lk B T f z x =
      trN (b.S*jprod t (diagonal (fun i=> bAv f (z,b.x i)))) +
        mats (fun i=>∑ j,b.E i j*t j i*kz f (b.x i) (b.x j) z) := by
  intro b u t
  rw [bjdiag,lk,← u.pjL,← q.BLe,B.bmat_loc,Pj,bjdiag']
  · rw [← mats_add]
    congr 1; ext i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    change b.E i j*t j i*((bInt f (z,b.x i)+bInt f (z,b.x j))/2)=_
    unfold kz
    have he : b.S i j=rcoef (b.x i) (b.x j) z*b.E i j := rfl
    rw [he,hf.bar_eq,hf.bar_eq]
    dsimp only []; ring
  · exact u.HL ht
  exact b.Her
lemma bm_scale (x z) (f:Plane→ℝ) (a:ℝ) :
    q.bmZ B (fun w=>a*f w) z x=a*q.bmZ B f z x := by
  simp_rw [bm_trace]; rw [← mats_s]; congr 1; ext; ring
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Klimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Pointwise Young estimate assembled before integrating; common
lemma for the two kernel estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Roots Seg
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma mats_s2 (a:ℝ) (f:Fin m→Fin m→ℝ) :
    a*mats (fun i=>∑ j,f i j) = mats (fun i=>∑ j,a*f i j) := by
  simp_rw [← Finset.mul_sum]; rw [mats_s]
omit [NeZero m] in
lemma mats_int (f:ℝ→Fin m→Fin m→ℝ) (hi:∀ i j,Integrable (fun x=> f x i j)) :
    Integrable (fun x=>mats (fun i=>∑ j,f x i j)) ∧
    (∫ x,mats (fun i=>∑ j,f x i j))=mats (fun i=>∑ j,∫ x,f x i j) := by
  unfold mats
  have hk (i:Fin m) : Integrable fun x:ℝ=>∑ j,f x i j :=
    integrable_finsetSum _ (fun j _=> hi i j)
  refine ⟨(integrable_finsetSum _ (fun i _=>hk i)).div_const _,?_⟩
  rw [integral_div,integral_finsetSum _ (fun i _=>hk i)]
  congr 1; apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun j _=>hi i j)]
lemma w_Young {a b c:ℝ} (hc:a^2≤b*c) (hb:0≤b) (he:0 ≤ c) {klm:ℝ}
    (h:0<klm) (x y:ℝ) : -(x*y*a) ≤ klm*(x^2*b) + (4*klm)⁻¹*(y^2*c) := by
  by_cases hi:b=0
  · have hv : a=0 := by rw [hi] at hc; nlinarith
    rw [hi,hv]; simp; positivity
  have hk : 0<b := lt_of_le_of_ne hb (Ne.symm hi)
  field_simp
  have HH := sq_nonneg (2*klm*b*x+y*a)
  have hp := mul_le_mul_of_nonneg_left hc (sq_nonneg y)
  nlinarith

omit [NeZero m] in
lemma Frm.loc_s (u:Frm m) (t:ℝ) : u.loc (scalar m t)=scalar m t := by
  simp only [scalar,u.loc_smul,u.loc_one]
omit [NeZero m] in
lemma ctR_box {T:Mat m} (h:T∈specBox m tmin tmax) (u:Frm m) :
    u.loc T∈specBox m tmin tmax := by
  exact ⟨u.HL h.1,by simpa only [u.loc_s] using u.loc_le h.2.1,
    by simpa only [u.loc_s] using u.loc_le h.2.2⟩
omit [NeZero m] in
lemma ck_i {A:Rn m→Mat m} (h:regular A) (T:Mat m) :
    Integrable (fun x=>hsN (cmu (A x) T)) (normal m) := by
  let g := fun x=>cmu (A x) T
  have hg : regular g := ⟨(h.p.mul (PolyBound.const _)).sub ((PolyBound.const _).mul h.p),
    (h.meas.mul aestronglyMeasurable_const).sub (aestronglyMeasurable_const.mul h.meas)⟩
  have hs : regular (fun x=>star (g x)) := by
    refine ⟨hg.p.mono (fun x=>by rw [norm_star]),?_⟩
    exact continuous_star.comp_aestronglyMeasurable hg.meas
  have hl : regular (fun x=>g x*star (g x)) := ⟨hg.p.mul hs.p,hg.meas.mul hs.meas⟩
  have hi := hl.lin (trL)
  have he : (fun x=>hsN (g x)) = fun x=> trL (g x*star (g x)) := by funext x; rw [trL_apply];rfl
  change Integrable (fun x=> hsN (g x)) _
  rw [he]
  exact hi.ig

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

-- f,b profiles in k; R profile for diagonal gain; bAv f gives matrix subtracted pairing.
-- κ₀ scales both f and U choice exposed
lemma Klimit (ht:T∈specBox m tmin tmax)
    {f w R:Plane→ℝ} (hf:Bwt f) (hw:Bwt w) (hR:Bwt R)
    (hp:∀ v:Plane,0≤w v)
    (c:ℝ) (_hc:0 ≤ c)
    (hmat:∀ (z:ℝ) (l:Fin m→ℝ) (t:Mat m), t∈specBox m tmin tmax →
      Matrix.diagonal (fun i=>R (z,l i)) ≤
        c • jprod t (diagonal (fun i=> bAv f (z,l i))))
    (U:ℝ→ℝ→ℝ→ℝ) (b₀:ℝ)
    (hU:∀ x y,Integrable (U x y) ∧ (∫ z,U x y z)=b₀*(x-y)^2)
    (hu:∀ x y z,z≠x→z≠y→0≤U x y z)
    (hK:∀ x y z,z≠x→z≠y→ (c*kz f x y z)^2≤
      ((|x-z| * w (z,x)+|y-z| * w (z,y))/2)*U x y z)
    {klm:ℝ} (h:0<klm) :
    q.BB B R - c*q.LLw B T f ≤ klm*q.BB B w + b₀/(4*klm)*Hcomm B.A T := by
  have he (x:Rn m) :
      (∫ z,q.bmZ B R z x)- c*(∫ z,q.lk B T f z x) ≤
      klm*(∫ z,q.bmZ B w z x)+ b₀/(4*klm)*hsN (cmu (B.A x) T) := by
    let u := B.Fr x
    let t := u.loc T
    let y := B.ev x
    let g := fun z:ℝ=> mats (fun i:Fin m=>∑ j:Fin m, (t j i)^2* U (y i) (y j) z)
    have hm (i j:Fin m) := hU (y i) (y j)
    have ha := mats_int (fun z i j=> (t j i)^2 * U (y i) (y j) z) (fun i j=>(hm i j).1.const_mul _)
    have hh : (∫ z,g z)=b₀*hsN (cmu (B.A x) T) := by
      unfold g
      rw [ha.2,cmu_eig (B.A x) T u (B.Fr_D x)]
      simp_rw [integral_const_mul]
      rw [← mats_s]
      congr 1; ext i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [(hm _ _).2,symm_entry (u.HL ht.1)]
      change _ = b₀*((y i-y j)^2 * (t j i)^2)
      ring
    have ha' : Integrable g := ha.1
    let m₁ := fun z=>q.bmZ B R z x - c*q.lk B T f z x
    let m₂ := fun z=>klm*q.bmZ B w z x +(4*klm)⁻¹*g z
    have hi₁ := q.bmh B hR x; have hi₂ := q.lk_slice_i B T hf x
    have hi₃ := q.bmh B hw x
    have he : ∀ᵐ z:ℝ, m₁ z≤ m₂ z := by
      have he : ∀ᵐ z:ℝ,∀ i:Fin m,z≠y i :=
        ae_all_iff.2 fun i=>by rw [ae_iff]; simp
      filter_upwards [he] with z hz
      let b := q.BL B x z
      let V := Matrix.diagonal fun i=> bAv f (z,y i)
      have hs := trN_mul_mono (hmat z y t (ctR_box ht u)) b.Spar
      rw [trN_cyclic _ b.S,trN_cyclic _ b.S,traceDiag,mul_smul_comm,trN_smul] at hs
      let J := fun i j:Fin m=> b.E i j*t j i*kz f (y i) (y j) z
      let d := fun i j:Fin m=>(|y i-z| * w (z,y i)+ |y j-z| * w (z,y j))/2
      let k:=fun i=>∑ j,b.E i j^2*d i j
      have hJ (i j) : (-c)*J i j ≤ klm*(b.E i j^2*d i j)+(4*klm)⁻¹*(t j i^2*U (y i) (y j) z) := by
        have hh := hp (z,y i); have hhh := hp (z,y j)
        have ht := hK (y i) (y j) z (hz _) (hz _)
        change _ ≤ d i j*_ at ht
        apply le_trans _ (w_Young ht (by unfold d; positivity) (hu _ _ _ (hz _) (hz _)) h (b.E i j) (t j i))
        unfold J; apply le_of_eq; ring
      have hi :
          (-c)*mats (fun i=> ∑ j,J i j)≤ klm*mats k+(4*klm)⁻¹*g z := by
        unfold g k; rw [mats_s2,mats_s2,mats_s2,← mats_add]
        apply mats_le; intro i; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun j _=>hJ _ _
      have he : mats k≤ q.bmZ B w z x := by
        have ht:= b.tr_blk (fun i=> w (z,y i)) (fun i=> hp _)
        rw [q.bm_trace]
        change _ ≤ mats (fun i=>b.S i i*w (z,y i))
        apply le_trans _ ht
        unfold k d
        apply le_of_eq; congr 1; funext i
        apply Finset.sum_congr rfl; intro j _
        exact mul_comm ..
      unfold m₁ m₂
      rw [q.pairing_layer B T x z hf ht.1,q.bm_trace B x z R]
      change mats (fun i=> b.S i i*R (z,y i))-c*(trN (b.S*jprod t V)+mats (fun i=>∑ j,J i j))
        ≤ klm*q.bmZ B w z x+(4*klm)⁻¹*g z
      change mats _≤ c*trN (b.S*jprod t V) at hs
      linarith [mul_le_mul_of_nonneg_left he h.le]
    have hp := integral_mono_ae (show Integrable m₁ volume from hi₁.sub (hi₂.const_mul c))
      (show Integrable m₂ volume from (hi₃.const_mul _).add (ha'.const_mul _)) he
    unfold m₁ m₂ at hp
    rw [integral_sub hi₁ (hi₂.const_mul _),integral_add (hi₃.const_mul _) (ha'.const_mul _)] at hp
    simp_rw [integral_const_mul,hh] at hp
    rw [div_eq_mul_inv]; linarith
  unfold BB LLw Hcomm
  have hi := q.bmah B hR; have hh := q.Lbar_i B T hf
  have hg := q.bmah B hw
  rw [← integral_const_mul,← integral_const_mul,← integral_const_mul]
  have hx := ck_i B.reg T
  rw [← integral_sub hi (hh.const_mul _), ← integral_add (hg.const_mul _) (hx.const_mul _)]
  exact integral_mono (hi.sub (hh.const_mul _)) ((hg.const_mul _).add (hx.const_mul _)) he
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Tbound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §05 the two layer estimates, retained penalties. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots

variable {m:ℕ}
lemma ux_nn {x y z:ℝ} : 0 ≤ Ux x y z := by
  unfold Ux U slab
  apply mul_nonneg (abs_nonneg _)
  generalize (z-min x y)/ |y-x|=t
  split_ifs with h h'
  · unfold xk; have hp : 0 < -t := by linarith
    positivity
  · unfold gx; positivity
  have hh : 0<t-1 := by linarith
  unfold xk; positivity

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

lemma BB_scale (f:Plane→ℝ) (c:ℝ) :
    q.BB B (fun w=>c*f w)=c*q.BB B f := by
  unfold BB; simp_rw [q.bm_scale,integral_const_mul]

lemma BB_bar {f} (hf:Bwt f) : q.LLw B 1 f=q.BB B (bAv f) := by
  unfold LLw BB; simp_rw [q.LL_Bw B _ _ hf]
lemma BB1 : q.LLw B 1 (fun _=>1)=q.BB B (fun _=>1) := by
  rw [q.BB_bar B (Bwt.const 1)]; simp_rw [show bAv (fun _=>1)=fun _=>(1:ℝ)
    from funext bar_const]

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Penalty
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Constant-layer penalty and commutator remainder accounting. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)
lemma nn_eq : q.NK 1=eNt q.edge := by
  rw [eNt, integral_integral_swap q.edge.n0_int]
  unfold NK Nt nTK Edge.nt0; simp
lemma NKpos : 0≤q.NK 1 := by
  rw [q.nn_eq]; unfold eNt
  apply integral_nonneg; intro u
  exact integral_nonneg (fun x=>q.edge.nt_pos ..)

lemma lm_pos : 0 < lm := by norm_num [lm,bb,eta,kar,tmin]
lemma karp : 0 < kar := by norm_num [kar]
omit [NeZero m] in
lemma LL1 (W:Mat m) :
    q.LLw B W (fun _=>1)=q.be B W (fun x=>x) (fun x=>x) := by
  have h := q.Le_id B W TestF.id TestF.id; simpa using h
lemma NZ_A (W:Mat m) :
    q.NK W=2*q.LLw q.FA W (fun _=>1) := by
  rw [q.LL1]
  have hh : q.MB q.FA (fun x=>x)=fun _ =>0 := by
    funext x
    rw [MB,id_ga]
    have he : q.FA.eval (fun x=>x) x=q.Amat x :=
      cfc_id' ℝ _ (ha:= show IsSelfAdjoint (q.FA.A x) from q.FA.sym _)
    rw [he]
    change q.Amat _-_+scalar _ _=_
    simp [scalar]
  have ht := q.eq15 q.FA W TestF.id
  rw [hh] at ht
  have hi : Pt W (fun _=>0) (fun _=>0)=0 := by simp [Pt,Pj,jprod,trN]
  rw [hi] at ht
  unfold NK; linarith
lemma NZ_L (W:Mat m) :
    Pt W q.RR q.RR+q.NK W=2*q.LLw q.FL W (fun _=>1) := by
  rw [q.LL1]
  have h := q.eq15 q.FL W TestF.id
  rw [q.MB_id] at h
  unfold NK; linarith

lemma const_limit (ht:T∈specBox m tmin tmax) :
    -kar*q.NK T≤ -kar*tmin*q.NK 1+lm*q.NK 1+e₀*Hcomm q.Amat T := by
  let f := fun _:Plane=> (1:ℝ)
  have he (z:ℝ) (l:Fin m→ℝ) (t:Mat m) (he:t∈specBox m tmin tmax) :
      Matrix.diagonal (fun i:Fin m=>2*tmin)≤
        (2:ℝ) • jprod t (Matrix.diagonal (fun i=> bAv f (z,l i))) := by
    unfold f; simp_rw [bar_const]
    rw [show (Matrix.diagonal (fun _:Fin m=> (1:ℝ)))=1 from rfl]
    have hi : jprod t 1=t := by unfold jprod; simp only [one_mul,mul_one]; module
    rw [hi]
    apply le_trans _ (smul_le_smul_of_nonneg_left he.2.1 (show (0:ℝ)≤2 by norm_num))
    apply le_of_eq
    unfold scalar; ext i j
    by_cases h:i=j
    · subst j; simp
    simp [h]
  have hl : 0 < 2*lm/kar := by have h := karp; have he := lm_pos; positivity
  have hf : Bwt f := Bwt.const _
  have h := q.Klimit q.FA T ht hf hf (Bwt.const (2*tmin)) (fun _=>zero_le_one)
    2 (by norm_num) he Ux (2*Real.log 2-1/3) Ux_area (fun _ _ _ _ _=> ux_nn)
    (fun x y z hx hy=> by
      have H := (pairEst f hf hx hy).2
      unfold Om at H; simp_rw [bar_const] at H; exact H) hl
  have hh : q.BB q.FA (fun _=>2*tmin)=2*tmin*q.BB q.FA f :=
    by simpa only [f,mul_one] using q.BB_scale q.FA f (2*tmin)
  rw [hh] at h
  have h₁:= q.NZ_A T
  have h₂ := q.NZ_A (1:Mat m)
  rw [q.BB1] at h₂
  have hi := mul_le_mul_of_nonneg_left h karp.le
  have hv : kar*((2 * Real.log 2-1/3)/(4*(2*lm/kar))) ≤ e₀ := by
    unfold kar lm e₀ bb eta tmin kar
    have hj:= Real.log_two_lt_d9; norm_num at *; linarith
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤ Hcomm q.Amat T from
    integral_nonneg fun _=> hsN_pos _)
  unfold f at *
  change -kar*q.NK T≤ -kar*tmin*q.NK 1+lm*q.NK 1+e₀*Hcomm q.FA.A T
  change kar* _ * Hcomm q.FA.A T≤ e₀*Hcomm q.FA.A T at hp
  unfold lm kar bb eta tmin e₀ at *; norm_num at *; linarith

omit [NeZero m] in
lemma cmCL (T:Mat m) : ∃ l: Mat m→L[ℝ]Mat m,(l:Mat m→Mat m)=fun x=>cmu x T := by
  let l := ContinuousLinearMap.mul ℝ (Mat m)
  exact ⟨l.flip T-l T,rfl⟩
lemma C_Hcomm (hT:T.IsHermitian) {A:Rn m→Mat m} (ha:regular A) (h:∀ x,(A x).IsHermitian) :
    HasSum (fun a=> (- CpPair 1 (fun x=> cmu (A x) T) (fun x=>cmu (A x) T) a)) (Hcomm A T) := by
  obtain ⟨l,hl⟩ := cmCL T
  have hc : regular (fun x=>cmu (A x) T) := by simp_rw [← congrFun hl]; exact ha.lin l
  have hi := (pt_sum (B:=(1:Mat m)) hc hc).neg
  have he (x) : hsN (cmu (A x) T) = -Pj 1 (cmu (A x) T) (cmu (A x) T) := by
    rw [hsN,Pj,one_mul,j_same]
    have hh : star (cmu (A x) T)= -cmu (A x) T := by
      unfold cmu; rw [star_sub,star_mul,star_mul, (show star (A x)=_ from h x), (show star T=T from hT),neg_sub]
    rw [hh,mul_neg]
    unfold trN; rw [trace_neg]; ring
  unfold Hcomm; simp_rw [he,integral_neg]
  exact hi

lemma comm_split (hT:T.IsHermitian) (h:q.avgA=0) :
    Hcomm q.Amat T= Hcomm q.Lmat T+Hcomm q.RR T := by
  obtain ⟨l,hl⟩ := cmCL T
  have hi := C_Hcomm T hT q.a_reg fun x=> q.H_hermitian poly_id_der _
  have h₁ := C_Hcomm T hT q.l_reg q.L_sym
  have h₂ := C_Hcomm T hT q.R_reg q.r_sym
  apply HasSum.unique hi
  apply (h₁.add h₂).congr_fun
  intro a
  have he {A:Rn m→Mat m} (ha:regular A) :
      CpPair 1 (fun x=>cmu (A x) T) (fun x=>cmu (A x) T) a=
        Pj 1 (l (cof A a)) (l (cof A a)) := by
    unfold CpPair
    simp_rw [cof_clm ha,congrFun hl]
  rw [he q.a_reg,he q.l_reg,he q.R_reg]
  have hh : cof q.Amat a = cof q.Lmat a + cof q.RR a := by
    unfold RR; rw [cof_subm q.a_reg q.l_reg]; abel
  by_cases ha:deg a=1
  · rw [hh,q.bal_cf h a (by omega)]; simp [Pj,jprod,trN]
  rw [hh,q.coL_o ha]; simp [Pj,jprod,trN]

omit [NeZero m] in
lemma comm_est (ht:T∈specBox m tmin tmax) {A:Mat m} (ha:A.IsHermitian) :
    hsN (cmu A T) ≤ (2*tr)^2*Pj 1 A A := by
  let t := T
  let u := Frm.eu ht.1
  have he := u.loc_s
  let f := u.eig T
  have hi (i:Fin m) : tmin≤f i ∧ f i≤tmax := by
    have h := spectrum_order T ht.1 (l:=tmin) (r:=tmax)
    have hi : f i∈ spectrum ℝ T := by
      unfold f u
      rw [ht.1.spectrum_real_eq_range_eigenvalues,Frm.eu_eig]; exact ⟨i,rfl⟩
    exact ⟨h.1.mp ht.2.1 _ hi,h.2.mp ht.2.2 _ hi⟩
  have hh : hsN (cmu A T)=hsN (cmu T A) := by
    rw [show cmu A T = -cmu T A from by unfold cmu; rw [neg_sub] ]
    simp [hsN]
  have hb : Pj 1 A A=hsN A := by rw [Pj, j_same,one_mul,hsN,show star A=A from ha]
  rw [hh,hb,cmu_eig T A u (Frm.eu_d _), ← hsN_loc A u,hsN_eq, mats_s2]
  apply mats_le
  intro i
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h₁:=hi i; have h₂:=hi j
  change (f i-f j)^2≤ _
  unfold tmin tmax Profile.tr at *
  nlinarith
lemma comm_bound (ht:T∈specBox m tmin tmax) :
    Hcomm q.RR T≤ (2*tr)^2*Pt 1 q.RR q.RR := by
  unfold Hcomm Pt; rw [← integral_const_mul]
  exact integral_mono (ck_i q.R_reg T) ((pj_poly_part q.R_reg _).const_mul _)
    fun x=> comm_est T ht (q.r_sym x)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Eq23
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §05 reduction to matrix functionals on linear field. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (T:Mat m)

lemma P_R_bd (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat) :
    (bb+eta)*Pt q.covMat q.RR q.RR-kar*Pt T q.RR q.RR ≤ ap*Pt 1 q.RR q.RR := by
  let P := fun W=>Pt W q.RR q.RR
  let f := fun W (x:Rn m)=> Pj W (q.RR x) (q.RR x)
  have hs (W) : Integrable (f W) (normal m) := pj_poly_part q.R_reg _
  have hi : P q.covMat= P 1+P T := by
    unfold P Pt; rw [← he]; simp_rw [Pj,add_mul,trN_add]; exact integral_add (hs _) (hs _)
  have ht : P T ≥ tmin * P 1 := by
    unfold P Pt
    rw [← integral_const_mul]
    apply integral_mono ((hs _).const_mul _) (hs _)
    intro x
    have h := p_le_p ht.2.1 (q.r_sym x)
    simpa only [f,Pj,scalar,smul_mul_assoc,trN_smul] using h
  unfold ap
  change _*P _-_*P _≤_*P _
  unfold bb eta kar tmin at *; linarith

lemma reserve_oai (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat) (hh:q.avgA=0) :
    (bb+eta)*Pt q.covMat q.RR q.RR -(2*kar)*q.LLw q.FL T (fun _=>1)-q.NK 1/8 ≤
      (2*ap+2*e₀*(2*tr)^2)*q.LLw q.FL 1 (fun _=>1)+e₀*Hcomm q.Lmat T := by
  have h := q.P_R_bd T ht he
  have h₁ := q.NZ_L T
  have h₂ := q.NZ_L 1
  have hp := q.NKpos
  have hi := q.const_limit T ht
  rw [q.comm_split T ht.1 hh] at hi
  have hk := q.comm_bound T ht
  unfold ap lm bb eta tmin tmax e₀ Profile.tr kar at *
  linarith

end ProjField
end GeneralMahler

end

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.ProjField.reserve_oai := @OAI.GeneralMahler.ProjField.reserve_oai
