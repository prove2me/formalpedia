-- Prove2me | solution 1 for OAI.SlotGeometry.ratio
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:55:41.742465+00:00
-- url     : https://prove2.me/submissions/a72a98c5-b603-42c5-af44-50a404c25ca8

import Mathlib
import Definitions.Def_OAIQ16Cd002
import Theorems.Thm_OAI_CapOverlap_cap_ratio_decay

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma continuous_act {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) : Continuous (act e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _

lemma cone_preimage {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n)) :
    Ioo (0 : ℝ) 1 • ((↑) '' (act e ⁻¹' S)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
  ext y
  constructor
  · rintro ⟨r, hr, x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨r, hr, e u.val, ⟨act e u, hu, rfl⟩, (e.map_smul r u.val).symm⟩
  · intro hy
    obtain ⟨r, hr, x, hx, he⟩ := hy
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨r, hr, e.symm u.val, ?_, ?_⟩
    · refine ⟨act e.symm u, ?_, rfl⟩
      change act e (act e.symm u) ∈ S
      have hh : act e (act e.symm u) = u := Subtype.ext (e.apply_symm_apply u.val)
      simpa only [hh] using hu
    · apply e.injective
      rw [e.map_smul, e.apply_symm_apply]
      exact he

lemma invariant {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n))
    (hS : MeasurableSet S) : σ n (act e ⁻¹' S) = σ n S := by
  simp only [σ, Measure.smul_apply]
  congr 1
  rw [Measure.toSphere_apply' _ ((continuous_act e).measurable hS),
    Measure.toSphere_apply' _ hS, cone_preimage]
  congr 1
  change volume (e.toHomeomorph ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' S))) = _
  rw [← e.toHomeomorph.measurableEmbedding.map_apply]
  exact congrArg (fun μ : Measure (Space n) => μ (Ioo (0:ℝ) 1 • ((↑) '' S)))
    e.measurePreserving.map_eq

lemma cap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (cap x t) :=
  isOpen_lt continuous_const ((continuous_subtype_val.inner continuous_const).abs)

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

lemma cap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (cap u.val t) := by
  apply positive_open _ (cap_open _ _) ⟨u, ?_⟩
  change t < |inner ℝ u.val u.val|
  have hnorm : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [real_inner_self_eq_norm_sq, hnorm, one_pow, abs_one] using ht

end SphericalLaw

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapGeometry
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapGeometry
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
open SphericalLaw

lemma halfcap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (halfcap x t) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

lemma halfcap_measurable {n : ℕ} (x : Space n) (t : ℝ) : MeasurableSet (halfcap x t) :=
  (halfcap_open x t).measurableSet

lemma halfcap_equal_norm {n : ℕ} {x y : Space n} (hxy : ‖x‖ = ‖y‖) (t : ℝ) :
    σ n (halfcap x t) = σ n (halfcap y t) := by
  let e := (Submodule.span ℝ ({x-y} : Set (Space n)))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : act e ⁻¹' halfcap y t = halfcap x t := by
    ext u
    change (t < inner ℝ (e u.val) y) ↔ (t < inner ℝ u.val x)
    rw [← he, e.inner_map_map]
  rw [← hp]
  exact invariant e _ (halfcap_measurable _ _)

end CapGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapLens
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace CapLens
open Set MeasureTheory Metric SphericalLaw CapGeometry
open scoped ENNReal Pointwise

lemma inner_unit {n : ℕ} (x : Space n) (hx : x ≠ 0) (y : Space n) :
    inner ℝ y (unit x hx).val = inner ℝ y x / ‖x‖ := by
  simp [unit, inner_smul_right, div_eq_mul_inv, mul_comm]

end CapLens

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapOverlap
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapOverlap
open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens

lemma cap_antimono {n : ℕ} [NeZero n] (e : Sphere n) {t s : ℝ} (hts : t ≤ s) :
    (σ n).real (halfcap e.val s) ≤ (σ n).real (halfcap e.val t) :=
  measureReal_mono (fun _ hw => hts.trans_lt hw) (measure_ne_top _ _)

lemma inter_subset_bisector {n : ℕ} (e f : Sphere n) {l t s k : ℝ}
    (hl : 0 < l) (hlt : l ≤ t) (hts : t ≤ s) (hk : 0 ≤ k) (hkl : k ≤ l/16)
    (hgap : s-t ≤ l*‖e.val-f.val‖^2/8) (hz : e.val+f.val ≠ 0) :
    halfcap e.val t ∩ halfcap f.val s ⊆
      halfcap (unit (e.val+f.val) hz).val (s+k*‖e.val-f.val‖^2) := by
  have he := mem_sphere_zero_iff_norm.mp e.property
  have hf := mem_sphere_zero_iff_norm.mp f.property
  have hr : ‖e.val+f.val‖ ≤ 2 := by
    have hh := norm_add_le e.val f.val
    rw [he, hf] at hh
    linarith
  have hd : ‖e.val-f.val‖^2 + ‖e.val+f.val‖^2 = 4 := by
    rw [norm_sub_sq_real, norm_add_sq_real, he, hf]; ring
  have hdr : ‖e.val-f.val‖^2 ≤ 4*(2-‖e.val+f.val‖) := by
    nlinarith [sq_nonneg (2-‖e.val+f.val‖)]
  have hs : 0 ≤ s := (hl.trans_le (hlt.trans hts)).le
  have hsr : s*‖e.val+f.val‖ ≤ 2*s-l*‖e.val-f.val‖^2/4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hlt.trans hts)) (sub_nonneg.mpr hr),
      mul_nonneg hl.le (sub_nonneg.mpr hdr)]
  have hkr : k*‖e.val-f.val‖^2*‖e.val+f.val‖ ≤ 2*k*‖e.val-f.val‖^2 :=
    by nlinarith [mul_nonneg (mul_nonneg hk (sq_nonneg ‖e.val-f.val‖)) (sub_nonneg.mpr hr)]
  have hbd : (s+k*‖e.val-f.val‖^2)*‖e.val+f.val‖ ≤ t+s := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ l-16*k) (sq_nonneg ‖e.val-f.val‖)]
  intro w hw
  change s+k*‖e.val-f.val‖^2 < inner ℝ w.val (unit (e.val+f.val) hz).val
  rw [inner_unit, lt_div_iff₀ (norm_pos_iff.mpr hz), inner_add_right]
  exact hbd.trans_lt (add_lt_add hw.1 hw.2)

lemma halfcap_overlap_sq_ordered {n : ℕ} [NeZero n] (e f : Sphere n)
    {l u U t s k : ℝ} (hl : 0 < l) (hU : U < 1)
    (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) :
    ((σ n).real (halfcap e.val t ∩ halfcap f.val s))^2 ≤
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2) *
        (σ n).real (halfcap e.val t) * (σ n).real (halfcap f.val s) := by
  let A := (σ n).real (halfcap e.val t)
  let B := (σ n).real (halfcap f.val s)
  let I := (σ n).real (halfcap e.val t ∩ halfcap f.val s)
  let d := ‖e.val-f.val‖^2
  have hA : 0 ≤ A := measureReal_nonneg
  have hB : 0 ≤ B := measureReal_nonneg
  have hI : 0 ≤ I := measureReal_nonneg
  have heq (r : ℝ) : (σ n).real (halfcap f.val r) = (σ n).real (halfcap e.val r) :=
    congrArg ENNReal.toReal (halfcap_equal_norm
      ((mem_sphere_zero_iff_norm.mp f.property).trans (mem_sphere_zero_iff_norm.mp e.property).symm) r)
  have hBA : B ≤ A := by dsimp [B, A]; rw [heq]; exact cap_antimono e hts
  have hIB : I ≤ B := measureReal_mono inter_subset_right (measure_ne_top _ _)
  have hd : 0 ≤ d := sq_nonneg _
  have hd4 : d ≤ 4 := by
    have hh : ‖e.val-f.val‖ ≤ 2 := by
      have hh := norm_sub_le e.val f.val
      rw [mem_sphere_zero_iff_norm.mp e.property, mem_sphere_zero_iff_norm.mp f.property] at hh
      linarith
    dsimp [d]; nlinarith [norm_nonneg (e.val-f.val)]
  change I^2 ≤ Real.exp (-(n:ℝ)*l*k*d)*A*B
  by_cases hgap : s-t ≤ l*d/8
  · by_cases hz : e.val+f.val = 0
    · have hemt : halfcap e.val t ∩ halfcap f.val s = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro w hw
        have ht : t < inner ℝ w.val e.val := hw.1
        have hs : s < inner ℝ w.val f.val := hw.2
        have hh := add_lt_add ht hs
        rw [← inner_add_right, hz, inner_zero_right] at hh
        linarith
      dsimp [I]; rw [hemt, measureReal_empty, zero_pow (by decide : 2 ≠ 0)]
      positivity
    · have hqU : s+k*d ≤ U := by nlinarith [mul_nonneg hk (sub_nonneg.mpr hd4)]
      have hsub := inter_subset_bisector e f hl hlt hts hk hkl hgap hz
      have hm := measureReal_mono hsub (measure_ne_top (σ n) _)
      have heq2 : (σ n).real (halfcap (unit (e.val+f.val) hz).val (s+k*d)) =
          (σ n).real (halfcap f.val (s+k*d)) :=
        congrArg ENNReal.toReal (halfcap_equal_norm
          ((mem_sphere_zero_iff_norm.mp (unit (e.val+f.val) hz).property).trans
            (mem_sphere_zero_iff_norm.mp f.property).symm) _)
      change I ≤ (σ n).real (halfcap (unit (e.val+f.val) hz).val (s+k*d)) at hm
      rw [heq2] at hm
      have hr := cap_ratio_decay f hl hU (hlt.trans hts)
        (by nlinarith [mul_nonneg hk hd] : s ≤ s+k*d) hqU hdim
      have hi : I ≤ Real.exp (-(n:ℝ)*l*k*d/2)*B := by
        have he : -(n:ℝ)*l*((s+k*d)-s)/2 = -(n:ℝ)*l*k*d/2 := by ring
        rw [he] at hr
        exact hm.trans hr
      have hisq : I^2 ≤ (Real.exp (-(n:ℝ)*l*k*d/2)*B)^2 :=
        pow_le_pow_left₀ hI hi 2
      have hE : (Real.exp (-(n:ℝ)*l*k*d/2))^2 = Real.exp (-(n:ℝ)*l*k*d) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      calc
        I^2 ≤ _ := hisq
        _ = Real.exp (-(n:ℝ)*l*k*d)*B*B := by rw [mul_pow,hE]; ring
        _ ≤ Real.exp (-(n:ℝ)*l*k*d)*A*B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBA (Real.exp_nonneg _)) hB
  · have hbig : 2*k*d ≤ s-t := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ l-16*k) hd]
    have hr := cap_ratio_decay e hl hU hlt hts (hsu.trans huU) hdim
    rw [← heq s] at hr
    have hE : Real.exp (-(n:ℝ)*l*(s-t)/2) ≤ Real.exp (-(n:ℝ)*l*k*d) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hl.le) (sub_nonneg.mpr hbig)]
    have hBexp : B ≤ Real.exp (-(n:ℝ)*l*k*d)*A :=
      hr.trans (mul_le_mul_of_nonneg_right hE hA)
    exact (pow_le_pow_left₀ hI hIB 2).trans (by
      simpa [sq] using mul_le_mul_of_nonneg_right hBexp hB)

end CapOverlap

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ProjectiveCaps
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace ProjectiveCaps
open InnerProductGeometry Real
variable {V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma angle_nonneg (x y : V) : 0 ≤ angle x y :=
  le_min (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_nonneg _ _)

end ProjectiveCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapAffinity
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapAffinity
open Set MeasureTheory Metric SphericalLaw CapGeometry CapOverlap

lemma chord_angle {n : ℕ} (e f : Sphere n) :
    (4/Real.pi^2) * (InnerProductGeometry.angle e.val f.val)^2 ≤ ‖e.val-f.val‖^2 := by
  have he := mem_sphere_zero_iff_norm.mp e.property
  have hf := mem_sphere_zero_iff_norm.mp f.property
  have ha := InnerProductGeometry.angle_nonneg e.val f.val
  have hb := InnerProductGeometry.angle_le_pi e.val f.val
  have hc := Real.cos_le_one_sub_mul_cos_sq (by rw [abs_of_nonneg ha]; exact hb)
  rw [norm_sub_sq_real, he, hf,
    InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one he hf]
  ring_nf at hc ⊢
  linarith

lemma halfcap_overlap {n : ℕ} [NeZero n] (e f : Sphere n)
    {l u U t s k : ℝ} (hl : 0 < l) (hU : U < 1)
    (hlt : l ≤ t) (htu : t ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val t ∩ halfcap f.val s) ≤
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2/2) *
        Real.sqrt ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)) := by
  have hsq : ((σ n).real (halfcap e.val t ∩ halfcap f.val s))^2 ≤
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2) *
        (σ n).real (halfcap e.val t) * (σ n).real (halfcap f.val s) := by
    rcases le_total t s with hts | hst
    · exact halfcap_overlap_sq_ordered e f hl hU hlt hts hsu huU hk hkl hku hdim
    · have hh := halfcap_overlap_sq_ordered f e hl hU hls hst htu huU hk hkl hku hdim
      rw [inter_comm, norm_sub_rev] at hh
      nlinarith [hh]
  have he : (Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2/2))^2 =
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hh : 0 ≤ Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2/2) *
      Real.sqrt ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)) := by positivity
  nlinarith [sq_nonneg ((σ n).real (halfcap e.val t ∩ halfcap f.val s)),
    show (Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2/2) *
      Real.sqrt ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)))^2 =
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2)*
        ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)) by
        rw [mul_pow, he, Real.sq_sqrt (by positivity)]]

lemma halfcap_signed_mass {n : ℕ} (e : Sphere n) (b : Bool) (t : ℝ) :
    σ n (halfcap (signed e b).val t) = σ n (halfcap e.val t) :=
  halfcap_equal_norm ((mem_sphere_zero_iff_norm.mp (signed e b).property).trans
    (mem_sphere_zero_iff_norm.mp e.property).symm) t

lemma cap_eq_union {n : ℕ} (e : Sphere n) (t : ℝ) :
    cap e.val t = ⋃ b : Bool, halfcap (signed e b).val t := by
  ext w
  simp only [cap, halfcap, mem_ofPred_eq, mem_iUnion, Bool.exists_bool,
    signed, Bool.false_eq_true, ↓reduceIte, inner_neg_right]
  exact lt_abs.trans (by tauto)

lemma cap_mass {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : 0 ≤ t) :
    (σ n).real (cap e.val t) = 2*(σ n).real (halfcap e.val t) := by
  rw [cap_eq_union]
  have he : (⋃ b : Bool, halfcap (signed e b).val t) =
      halfcap (signed e false).val t ∪ halfcap (signed e true).val t := by
    ext w; simp only [mem_iUnion, Bool.exists_bool, mem_union]
  rw [he]
  have hd : Disjoint (halfcap (signed e false).val t) (halfcap (signed e true).val t) := by
    apply disjoint_left.mpr
    intro w hw1 hw2
    change t < inner ℝ w.val (-e.val) at hw1
    rw [inner_neg_right] at hw1
    change t < inner ℝ w.val e.val at hw2
    linarith
  rw [measureReal_union hd (halfcap_measurable _ _), measureReal_def, halfcap_signed_mass]
  change (σ n).real (halfcap e.val t) + (σ n).real (halfcap e.val t) = _
  ring

lemma projective_le_signed {n : ℕ} (e f : Sphere n) (a b : Bool) :
    ProjectiveCaps.angle e.val f.val ≤
      InnerProductGeometry.angle (signed e a).val (signed f b).val := by
  cases a <;> cases b <;> dsimp [signed, ProjectiveCaps.angle]
  · rw [InnerProductGeometry.angle_neg_neg]
    exact min_le_left _ _
  · rw [InnerProductGeometry.angle_neg_left, ← InnerProductGeometry.angle_neg_right]
    exact min_le_right _ _
  · exact min_le_right _ _
  · exact min_le_left _ _

lemma doublecap_overlap {n : ℕ} [NeZero n] (e f : Sphere n)
    {l u U t s k : ℝ} (hl : 0 < l) (hU : U < 1)
    (hlt : l ≤ t) (htu : t ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) :
    (σ n).real (cap e.val t ∩ cap f.val s) ≤
      2*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(ProjectiveCaps.angle e.val f.val)^2) *
        Real.sqrt ((σ n).real (cap e.val t)*(σ n).real (cap f.val s)) := by
  let E := Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(ProjectiveCaps.angle e.val f.val)^2)
  let F := Real.sqrt ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s))
  have hbound (a b : Bool) :
      (σ n).real (halfcap (signed e a).val t ∩ halfcap (signed f b).val s) ≤ E*F := by
    have hh := halfcap_overlap (signed e a) (signed f b) hl hU hlt htu hls hsu huU hk hkl hku hdim
    have hm : Real.sqrt ((σ n).real (halfcap (signed e a).val t)*
        (σ n).real (halfcap (signed f b).val s)) = F := by
      simp only [measureReal_def, halfcap_signed_mass, F]
    rw [hm] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    have hc := chord_angle (signed e a) (signed f b)
    have hp := pow_le_pow_left₀ (ProjectiveCaps.angle_nonneg e.val f.val)
      (projective_le_signed e f a b) 2
    have hp2 := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 4/Real.pi^2)
    have hn : 0 ≤ (n:ℝ)*l*k := by positivity
    have hprod := mul_nonneg hn (sub_nonneg.mpr (hp2.trans hc))
    change -(n:ℝ)*l*k*‖(signed e a).val-(signed f b).val‖^2/2 ≤
      -(n:ℝ)*(2*l*k/Real.pi^2)*(ProjectiveCaps.angle e.val f.val)^2
    ring_nf at hprod ⊢
    nlinarith
  have heq : cap e.val t ∩ cap f.val s =
      ⋃ p : Bool × Bool, halfcap (signed e p.1).val t ∩ halfcap (signed f p.2).val s := by
    rw [cap_eq_union, cap_eq_union]
    ext w
    simp only [mem_inter_iff, mem_iUnion, Prod.exists]
    aesop
  have hb : (σ n).real (cap e.val t ∩ cap f.val s) ≤ 4*E*F := by
    rw [heq]
    calc
      _ ≤ ∑ p : Bool × Bool, (σ n).real (halfcap (signed e p.1).val t ∩
        halfcap (signed f p.2).val s) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : Bool × Bool, E*F := Finset.sum_le_sum fun p _ => hbound p.1 p.2
      _ = _ := by simp; ring
  have hm : Real.sqrt ((σ n).real (cap e.val t)*(σ n).real (cap f.val s)) = 2*F := by
    rw [cap_mass e (hl.trans_le hlt).le, cap_mass f (hl.trans_le hls).le]
    have he : (2*(σ n).real (halfcap e.val t))*(2*(σ n).real (halfcap f.val s)) =
        (2:ℝ)^2*((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)) := by ring
    rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hm]
  convert hb using 1 <;> first | rfl | ring

end CapAffinity

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapCost
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapCost
open MeasureTheory SphericalLaw CapGeometry CapAffinity
open scoped ENNReal NNReal

lemma intensity_real {n : ℕ} (e : Sphere n) (t : ℝ) (E : Set (Sphere n)) :
    (intensity e t).real E = (σ n).real E/(σ n).real (cap e.val t) := by
  change (((rate e t : ℝ≥0∞)*(σ n) E).toReal) = _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  change ((σ n).real (cap e.val t))⁻¹ * (σ n).real E = _
  ring

lemma cap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (cap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (cap_positive e ht)) (measure_ne_top _ _)

end CapCost

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_DecayNormalization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace DecayNormalization

lemma clipped_compare {x H : ℝ} (hx : 0 ≤ x) (hH : 1 ≤ H) (hxH : x ≤ H) :
    x ≤ 2*H*min x (1/2) := by
  by_cases h : x ≤ 1/2
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith

lemma sqrt_clipped {x y H : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hH : 1 ≤ H) (hxH : x ≤ H) (hyH : y ≤ H) :
    Real.sqrt (x*y) ≤ 2*H*Real.sqrt (min x (1/2)*min y (1/2)) := by
  have hbx := lt_min hx (by norm_num : (0:ℝ)<1/2)
  have hby := lt_min hy (by norm_num : (0:ℝ)<1/2)
  have hp := mul_le_mul (clipped_compare hx.le hH hxH) (clipped_compare hy.le hH hyH)
    hy.le (by positivity)
  have hs := Real.sqrt_le_sqrt hp
  have he : (2*H*min x (1/2))*(2*H*min y (1/2)) =
      (2*H)^2*(min x (1/2)*min y (1/2)) := by ring
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by linarith)] at hs
  exact hs

end DecayNormalization

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_NormalizedCaps
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace NormalizedCaps
open MeasureTheory SphericalLaw CapCost CapAffinity ProjectiveCaps
open scoped ENNReal NNReal

lemma scale_sqrt {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    Real.sqrt (a/c*(b/c)) = Real.sqrt (a*b)/c := by
  rw [div_mul_div_comm, Real.sqrt_div (mul_nonneg ha hb), ← pow_two,Real.sqrt_sq hc.le]

lemma intensity_overlap {n : ℕ} [NeZero n] (e f g : Sphere n)
    {l u U t r s k : ℝ} (hl : 0 < l) (hU : U < 1)
    (_ht : 0 ≤ t) (ht1 : t < 1)
    (hlr : l ≤ r) (hru : r ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) :
    (intensity e t).real (cap f.val r ∩ cap g.val s) ≤
      2*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2) *
        Real.sqrt ((intensity e t).real (cap f.val r)*(intensity e t).real (cap g.val s)) := by
  simp_rw [intensity_real]
  rw [scale_sqrt measureReal_nonneg measureReal_nonneg (cap_real_pos e ht1), ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (doublecap_overlap f g hl hU hlr hru hls hsu huU hk hkl hku hdim)
    (cap_real_pos e ht1).le

end NormalizedCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CrossSlots
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace CrossSlots
open MeasureTheory PoissonDiagrams
open scoped BigOperators Classical

lemma ratio {z c d x y p q A : ℝ} (hp : 0 < p) (hq : 0 < q) (hA : 0 ≤ A)
    (hc : p ≤ c) (hd : p ≤ d) (hx : q*c ≤ x) (hy : q*d ≤ y)
    (hz : z ≤ A*Real.sqrt (c*d)) : z/(x*y) ≤ A/(p*q^2) := by
  have hc0 := hp.trans_le hc
  have hd0 := hp.trans_le hd
  have hx0 := (mul_pos hq hc0).trans_le hx
  have hy0 := (mul_pos hq hd0).trans_le hy
  have hcd : p^2 ≤ c*d := by nlinarith only [mul_le_mul hc hd hp.le hc0.le]
  have hs : p ≤ Real.sqrt (c*d) := by
    apply (Real.le_sqrt hp.le (mul_nonneg hc0.le hd0.le)).mpr
    exact hcd
  have hs2 := Real.sq_sqrt (mul_nonneg hc0.le hd0.le)
  have hroot : p*Real.sqrt (c*d) ≤ c*d := by nlinarith only [mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (c*d)),hs2]
  have hxy : q^2*c*d ≤ x*y := by
    have hh := mul_le_mul hx hy (mul_nonneg hq.le hd0.le) hx0.le
    nlinarith only [hh]
  apply (div_le_div_iff₀ (mul_pos hx0 hy0) (by positivity)).mpr
  have h1 := mul_le_mul_of_nonneg_right hz (by positivity : 0 ≤ p*q^2)
  have h2 := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ A*q^2)
  have h3 := mul_le_mul_of_nonneg_left hxy hA
  nlinarith only [h1,h2,h3]

end CrossSlots

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SlotGeometry
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace SlotGeometry
open Set MeasureTheory SphericalLaw CapCost ProjectiveCaps
open scoped BigOperators

lemma ratio_oai {n : ℕ} [NeZero n] (e f g : Sphere n)
    {l u U t r s k H K P : ℝ} (hl : 0 < l) (hU : U < 1) (ht : 0 ≤ t) (ht1 : t < 1)
    (hlr : l ≤ r) (hru : r ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) (hH : 1 ≤ H)
    {E F : Set (Sphere n)} (hE : E ⊆ cap f.val r) (hF : F ⊆ cap g.val s)
    (hraw1 : (intensity e t).real (cap f.val r) ≤ H)
    (hraw2 : (intensity e t).real (cap g.val s) ≤ H)
    (hclip1 : Real.exp (-P*Real.log n) ≤ min ((intensity e t).real (cap f.val r)) (1/2))
    (hclip2 : Real.exp (-P*Real.log n) ≤ min ((intensity e t).real (cap g.val s)) (1/2))
    (hslot1 : Real.exp (-K*Real.log n)*min ((intensity e t).real (cap f.val r)) (1/2) ≤ (intensity e t).real E)
    (hslot2 : Real.exp (-K*Real.log n)*min ((intensity e t).real (cap g.val s)) (1/2) ≤ (intensity e t).real F) :
    (intensity e t).real (E ∩ F)/((intensity e t).real E*(intensity e t).real F) ≤
      4*H*Real.exp ((2*K+P)*Real.log n-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2) := by
  let μ := intensity e t
  let c := min (μ.real (cap f.val r)) (1/2)
  let d := min (μ.real (cap g.val s)) (1/2)
  have hc : 0 < μ.real (cap f.val r) := by
    rw [intensity_real]
    exact div_pos (cap_real_pos f ((hru.trans huU).trans_lt hU)) (cap_real_pos e ht1)
  have hd : 0 < μ.real (cap g.val s) := by
    rw [intensity_real]
    exact div_pos (cap_real_pos g ((hsu.trans huU).trans_lt hU)) (cap_real_pos e ht1)
  have hroot := DecayNormalization.sqrt_clipped hc hd hH hraw1 hraw2
  have hovering := NormalizedCaps.intensity_overlap e f g hl hU ht ht1 hlr hru hls hsu huU hk hkl hku hdim
  have hmono : μ.real (E ∩ F) ≤ μ.real (cap f.val r ∩ cap g.val s) :=
    measureReal_mono (inter_subset_inter hE hF)
  have hupper : μ.real (E ∩ F) ≤
      (4*H*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2))*Real.sqrt (c*d) := by
    have hm := mul_le_mul_of_nonneg_left hroot
      (by positivity : 0 ≤ 2*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2))
    apply (hmono.trans hovering).trans
    convert hm using 1 <;> first | rfl | ring
  have hrat := CrossSlots.ratio (Real.exp_pos (-P*Real.log n)) (Real.exp_pos (-K*Real.log n))
    (by positivity : 0 ≤ 4*H*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2))
    hclip1 hclip2 hslot1 hslot2 hupper
  apply hrat.trans_eq
  rw [← Real.exp_nat_mul,← Real.exp_add,mul_div_assoc,← Real.exp_sub]
  congr 2
  ring

end SlotGeometry

end OAI
end

theorem solution : type_of% @OAI.SlotGeometry.ratio_oai := @OAI.SlotGeometry.ratio_oai
