-- Prove2me | solution 1 for OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:55:22.20482+00:00
-- url     : https://prove2.me/submissions/c062afb9-22d3-44e1-9d78-e2eb49785521

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ15Sf012

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_PolarScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.PolarScalar


lemma max_pos {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 < max t r := hr.trans_le (le_max_right ..)
lemma continuous_invCut {r : ℝ} (hr : 0 < r) : Continuous (invCut r) :=
  ((continuous_id.max continuous_const).sqrt).inv₀ fun t => (Real.sqrt_pos.2 (max_pos hr t)).ne'
lemma continuous_cut {r : ℝ} (hr : 0 < r) : Continuous (cut r) :=
  continuous_id.div (continuous_id.max continuous_const) (fun t => (max_pos hr t).ne')

lemma invCut_nonneg {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 ≤ invCut r t := by unfold invCut; positivity
lemma cut_nonneg {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) : 0 ≤ cut r t := div_nonneg ht (max_pos hr t).le
lemma cut_le_one {r t : ℝ} (hr : 0 < r) : cut r t ≤ 1 :=
  (div_le_one (max_pos hr t)).mpr (le_max_left ..)

lemma cut_eq {r : ℝ} (hr : 0 < r) (t : ℝ) : invCut r t*t*invCut r t=cut r t := by
  have hs : (Real.sqrt (max t r))^2=max t r := Real.sq_sqrt (max_pos hr t).le
  unfold invCut cut
  calc
    (Real.sqrt (max t r))⁻¹ * t * (Real.sqrt (max t r))⁻¹ =
        t * ((Real.sqrt (max t r))^2)⁻¹ := by ring
    _ = t * (max t r)⁻¹ := by rw [hs]
    _ = t / max t r := by rw [div_eq_mul_inv]

lemma cut_mono {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 ≤ t) (hrs : r ≤ s) :
    cut s t ≤ cut r t :=
  (div_le_div_iff₀ (max_pos hs t) (max_pos hr t)).2
    (mul_le_mul_of_nonneg_left (max_le_max_left t hrs) ht)

lemma cut_gap {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    cut r t*(cut r t-1)^2 ≤ cut (r/2) t-cut r t := by
  have hg0 := cut_nonneg hr ht
  have hg1 := cut_le_one (t:=t) hr
  have h01 : (cut r t-1)^2 ≤ 1 := by nlinarith
  by_cases htr : t ≤ r/2
  · have htr' : t ≤ r := htr.trans (by linarith)
    have hm : cut (r/2) t = 2*cut r t := by
      simp only [cut,max_eq_right htr,max_eq_right htr']
      field_simp
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_left h01 hg0]
  · have htpos : 0 < t := lt_of_lt_of_le (half_pos hr) (not_le.mp htr).le
    have hm : cut (r/2) t=1 := by
      rw [cut,max_eq_left (not_le.mp htr).le,div_self htpos.ne']
    rw [hm]
    have hsq : (cut r t-1)^2 ≤ 1-cut r t := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg1)]
    have hm' := mul_le_mul_of_nonneg_right hg1 (sq_nonneg (cut r t-1))
    nlinarith

lemma cut_error {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ t*(invCut r t*Real.sqrt t-1)^2 ∧ t*(invCut r t*Real.sqrt t-1)^2 ≤ r := by
  refine ⟨mul_nonneg ht (sq_nonneg _),?_⟩
  by_cases htr : r ≤ t
  · have htpos : 0 < t := hr.trans_le htr
    have he : invCut r t*Real.sqrt t=1 := by
      unfold invCut
      rw [max_eq_left htr,inv_mul_cancel₀ (Real.sqrt_pos.2 htpos).ne']
    rw [he,sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero]
    exact hr.le
  · have htr' : t ≤ r := (not_le.mp htr).le
    have hs0 : 0 ≤ invCut r t*Real.sqrt t := mul_nonneg (invCut_nonneg hr t) (Real.sqrt_nonneg t)
    have hs1 : invCut r t*Real.sqrt t ≤ 1 := by
      rw [invCut,max_eq_right htr',mul_comm,← div_eq_mul_inv]
      exact (div_le_one (Real.sqrt_pos.2 hr)).mpr (Real.sqrt_le_sqrt htr')
    have hsq : (invCut r t*Real.sqrt t-1)^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq ht]


end KaplanskyConsequences.PolarScalar

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open scoped ComplexOrder
open Kaplansky SpectralKernel
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

namespace QuasiValue
variable {A : Type*} [CStarAlgebra A]

variable (V : QuasiValue A)

lemma q_nonneg (x : A) : 0≤V.q x := V.nonneg (star_mul_self_nonneg x)
lemma q_bound (x : A) : V.q x≤‖x‖^2 := by
  simpa only [q,CStarRing.norm_star_mul_self,pow_two] using
    (le_abs_self (V.val (star x*x))).trans (V.bound _)

end QuasiValue
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_ApproxPolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
open PolarScalar
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

lemma polarCut_square (x : A) {r : ℝ} (hr : 0 < r) :
    star (polarCut x r)*polarCut x r=spectralCut x r := by
  have hf := (continuous_invCut hr).continuousOn (s:=spectrum ℝ (star x*x))
  have hb : IsSelfAdjoint (star x*x) := (star_mul_self_nonneg x).isSelfAdjoint
  have hsa : IsSelfAdjoint (cfc (invCut r) (star x*x)) := IsSelfAdjoint.cfc
  unfold polarCut spectralCut
  rw [star_mul,hsa.star_eq]
  calc
    cfc (invCut r) (star x*x)*star x*(x*cfc (invCut r) (star x*x)) =
      cfc (invCut r) (star x*x)*(star x*x)*cfc (invCut r) (star x*x) := by noncomm_ring
    _ = cfc (fun t => invCut r t*t*invCut r t) (star x*x) := by
      rw [cfc_mul (fun t => invCut r t*t) (invCut r) _ (hf.mul continuousOn_id) hf,
        cfc_mul (invCut r) (fun t => t) _ hf continuousOn_id,cfc_id' ℝ (star x*x) hb]
    _ = cfc (cut r) (star x*x) := by congr 1; funext t; exact cut_eq hr t

lemma spectralCut_nonneg (x : A) {r : ℝ} (hr : 0 < r) : 0 ≤ spectralCut x r := by
  rw [← polarCut_square x hr]
  exact star_mul_self_nonneg _

lemma spectralCut_norm (x : A) {r : ℝ} (hr : 0 < r) : ‖spectralCut x r‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (cut_nonneg hr (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht))]
  exact cut_le_one hr

lemma polarCut_norm (x : A) {r : ℝ} (hr : 0 < r) : ‖polarCut x r‖ ≤ 1 := by
  have h := spectralCut_norm x hr
  rw [← polarCut_square x hr,CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (polarCut x r)]

lemma cfc_sqrt_real (a : A) (ha : 0 ≤ a) : cfc Real.sqrt a=CFC.sqrt a := by
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact (cfcₙ_eq_cfc (f:=Real.sqrt) (a:=a)).symm

lemma polarCut_error_square (x : A) {r : ℝ} (hr : 0 < r) :
    star (polarCut x r*CFC.sqrt (star x*x)-x)*(polarCut x r*CFC.sqrt (star x*x)-x) =
      cfc (fun t => t*(invCut r t*Real.sqrt t-1)^2) (star x*x) := by
  let b := star x*x
  have hb : IsSelfAdjoint b := (star_mul_self_nonneg x).isSelfAdjoint
  have hf := (continuous_invCut hr).continuousOn (s:=spectrum ℝ b)
  have hg : ContinuousOn (fun t => invCut r t*Real.sqrt t-1) (spectrum ℝ b) :=
    (hf.mul Real.continuous_sqrt.continuousOn).sub continuousOn_const
  have he : polarCut x r*CFC.sqrt b-x = x*cfc (fun t => invCut r t*Real.sqrt t-1) b := by
    rw [cfc_sub (fun t => invCut r t*Real.sqrt t) (fun _ => 1) b (hf.mul Real.continuous_sqrt.continuousOn) continuousOn_const,
      cfc_mul (invCut r) Real.sqrt _ hf Real.continuous_sqrt.continuousOn,cfc_const_one ℝ b,
      cfc_sqrt_real b (star_mul_self_nonneg x)]
    unfold polarCut
    noncomm_ring
  change star (polarCut x r*CFC.sqrt b-x)*(polarCut x r*CFC.sqrt b-x)=_
  rw [he,star_mul,(IsSelfAdjoint.cfc (f:=fun t => invCut r t*Real.sqrt t-1) (a:=b)).star_eq]
  calc
    cfc (fun t => invCut r t*Real.sqrt t-1) b*star x*(x*cfc (fun t => invCut r t*Real.sqrt t-1) b) =
      cfc (fun t => invCut r t*Real.sqrt t-1) b*b*cfc (fun t => invCut r t*Real.sqrt t-1) b := by dsimp [b]; noncomm_ring
    _ = cfc (fun t => (invCut r t*Real.sqrt t-1)*t*(invCut r t*Real.sqrt t-1)) b := by
      rw [cfc_mul (fun t => (invCut r t*Real.sqrt t-1)*t) (fun t => invCut r t*Real.sqrt t-1) _ (hg.mul continuousOn_id) hg,cfc_mul (fun t => invCut r t*Real.sqrt t-1) (fun t => t) _ hg continuousOn_id,cfc_id' ℝ b hb]
    _ = _ := by congr 1; funext t; ring

lemma polarCut_error_norm (x : A) {r : ℝ} (hr : 0 < r) :
    ‖polarCut x r*CFC.sqrt (star x*x)-x‖^2 ≤ r := by
  rw [pow_two,← CStarRing.norm_star_mul_self,polarCut_error_square x hr]
  apply norm_cfc_le hr.le
  intro t ht
  have h := cut_error hr (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht)
  simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_CornerPolarCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

open scoped CStarAlgebra in
lemma map_cfc_sqrt (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : 0 ≤ a) :
    φ (CFC.sqrt a)=CFC.sqrt (φ a) := by
  rw [← cfc_sqrt_real a ha,φ.map_cfc Real.sqrt a (ha:=ha.isSelfAdjoint)
    (hφa:=(map_nonneg φ ha).isSelfAdjoint),cfc_sqrt_real (φ a) (map_nonneg φ ha)]

open scoped CStarAlgebra in
lemma map_polarCut (φ : A →⋆ₐ[ℂ] B) (x : A) {r : ℝ} (hr : 0 < r) :
    φ (polarCut x r)=polarCut (φ x) r := by
  unfold polarCut
  rw [map_mul,φ.map_cfc (PolarScalar.invCut r) (star x*x)
    (hf:=(PolarScalar.continuous_invCut hr).continuousOn)
    (ha:=(star_mul_self_nonneg x).isSelfAdjoint)
    (hφa:=(map_nonneg φ (star_mul_self_nonneg x)).isSelfAdjoint),map_mul,map_star]

lemma polarCut_left_corner {x q : A} (hqx : q*x=x) (r : ℝ) :
    q*polarCut x r=polarCut x r := by
  unfold polarCut
  rw [← mul_assoc,hqx]

lemma polarCut_right_corner {x p : A} (hp : IsStarProjection p) (hxp : x*p=x) (r : ℝ) :
    polarCut x r*p=polarCut x r := by
  have hpx : p*star x=star x := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hxp
  have hpb : p*(star x*x)=star x*x := by rw [← mul_assoc,hpx]
  have hbp : (star x*x)*p=star x*x := by rw [mul_assoc,hxp]
  have hc : Commute (star x*x) p := hbp.trans hpb.symm
  have hf := hc.cfc_real (PolarScalar.invCut r)
  unfold polarCut
  rw [mul_assoc,hf.eq,← mul_assoc,hxp]


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_PolarDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
open PolarScalar
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

lemma polarCut_defect_square (x : A) {r : ℝ} (hr : 0 < r) :
    star (polarCut x r*star (polarCut x r)*polarCut x r-polarCut x r)*
      (polarCut x r*star (polarCut x r)*polarCut x r-polarCut x r) =
        cfc (fun t => cut r t*(cut r t-1)^2) (star x*x) := by
  let v := polarCut x r
  let e := spectralCut x r
  have hv : star v*v=e := polarCut_square x hr
  have he : IsSelfAdjoint e := (spectralCut_nonneg x hr).isSelfAdjoint
  have hf := (continuous_cut hr).continuousOn (s:=spectrum ℝ (star x*x))
  have hb : IsSelfAdjoint (star x*x) := (star_mul_self_nonneg x).isSelfAdjoint
  calc
    star (v*star v*v-v)*(v*star v*v-v) = (e-1)*e*(e-1) := by
      have h : v*star v*v-v=v*(e-1) := by rw [← hv]; noncomm_ring
      rw [h,star_mul,star_sub,he.star_eq,star_one]
      calc
        (e-1)*star v*(v*(e-1)) = (e-1)*(star v*v)*(e-1) := by noncomm_ring
        _ = _ := by rw [hv]
    _ = cfc (fun t => (cut r t-1)*cut r t*(cut r t-1)) (star x*x) := by
      rw [cfc_mul (fun t => (cut r t-1)*cut r t) (fun t => cut r t-1) _
        ((hf.sub continuousOn_const).mul hf) (hf.sub continuousOn_const),
        cfc_mul (fun t => cut r t-1) (cut r) _ (hf.sub continuousOn_const) hf,
        cfc_sub (cut r) (fun _ => 1) _ hf continuousOn_const,cfc_const_one ℝ (star x*x)]
      rfl
    _ = _ := by congr 1; funext t; ring

lemma val_sub_commute (V : QuasiValue A) {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hc : Commute a b) : V.val (a-b)=V.val a-V.val b := by
  have hn := V.smul (-1) b
  simp only [neg_one_smul,neg_mul,one_mul] at hn
  rw [sub_eq_add_neg,V.add_commute ha hb.neg hc.neg_right,hn,sub_eq_add_neg]

lemma spectralCut_commute (x : A) (r s : ℝ) : Commute (spectralCut x r) (spectralCut x s) :=
  (((Commute.refl (star x*x)).cfc_real (cut r)).symm.cfc_real (cut s)).symm

lemma polarCut_q_defect (V : QuasiValue A) (x : A) {r : ℝ} (hr : 0 < r) :
    V.q (polarCut x r*star (polarCut x r)*polarCut x r-polarCut x r) ≤
      V.val (spectralCut x (r/2))-V.val (spectralCut x r) := by
  have hf := (continuous_cut hr).continuousOn (s:=spectrum ℝ (star x*x))
  have hg := (continuous_cut (half_pos hr)).continuousOn (s:=spectrum ℝ (star x*x))
  have hc := spectralCut_commute x (r/2) r
  rw [← V.val_sub_commute (spectralCut_nonneg x (half_pos hr)).isSelfAdjoint
    (spectralCut_nonneg x hr).isSelfAdjoint hc]
  apply V.mono (star_mul_self_nonneg _)
  rw [polarCut_defect_square x hr]
  change _ ≤ cfc (cut (r/2)) (star x*x)-cfc (cut r) (star x*x)
  rw [← cfc_sub (cut (r/2)) (cut r) _ hg hf]
  apply (cfc_le_iff _ _ _ (hf.mul ((hf.sub continuousOn_const).pow 2)) (hg.sub hf)
    (star_mul_self_nonneg x).isSelfAdjoint).mpr
  intro t ht
  exact cut_gap hr (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht)

lemma spectralCut_val_bound (V : QuasiValue A) (x : A) {r : ℝ} (hr : 0 < r) :
    0 ≤ V.val (spectralCut x r) ∧ V.val (spectralCut x r) ≤ 1 :=
  ⟨V.nonneg (spectralCut_nonneg x hr),
    (le_abs_self _).trans ((V.bound _).trans (spectralCut_norm x hr))⟩

lemma spectralCut_val_mono (V : QuasiValue A) (x : A) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    V.val (spectralCut x s) ≤ V.val (spectralCut x r) := by
  apply V.mono (spectralCut_nonneg x hs)
  apply (cfc_le_iff _ _ _ (continuous_cut hs).continuousOn (continuous_cut hr).continuousOn
    (star_mul_self_nonneg x).isSelfAdjoint).mpr
  intro t ht
  exact cut_mono hr hs (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht) hrs

lemma exists_good_polarCut (V : QuasiValue A) (x : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ V.q (polarCut x r*star (polarCut x r)*polarCut x r-polarCut x r) < ε ∧
      ‖polarCut x r*CFC.sqrt (star x*x)-x‖^2 ≤ ε := by
  let S : Set ℝ := {t | ∃ r : ℝ, 0 < r ∧ t=V.val (spectralCut x r)}
  have hS : S.Nonempty := ⟨_,1,zero_lt_one,rfl⟩
  have hb : BddAbove S := ⟨1,by rintro t ⟨r,hr,rfl⟩; exact (spectralCut_val_bound V x hr).2⟩
  obtain ⟨_,⟨s,hs,rfl⟩,hlt⟩ := exists_lt_of_lt_csSup hS (sub_lt_self (sSup S) hε)
  let r := min s ε
  have hr : 0 < r := lt_min hs hε
  have hsup : V.val (spectralCut x (r/2)) ≤ sSup S :=
    le_csSup hb ⟨r/2,half_pos hr,rfl⟩
  have hmono := spectralCut_val_mono V x hr hs (min_le_left s ε)
  refine ⟨r,hr,?_,(polarCut_error_norm x hr).trans (min_le_right s ε)⟩
  have hq := polarCut_q_defect V x hr
  linarith


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Quotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma quotQ_nonneg (x : V.FaithfulQuotient) : 0≤V.quotQ x := by
  obtain ⟨a,rfl⟩ := V.nullIdeal.mk_surjective x
  exact V.q_nonneg a

lemma quotQ_eq_zero (x : V.FaithfulQuotient) : V.quotQ x=0 ↔ x=0 := by
  obtain ⟨a,rfl⟩ := V.nullIdeal.mk_surjective x
  exact (V.nullIdeal.mk_eq_zero a).symm


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_UltraDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology

lemma ultra_selector (u : Ultrafilter ℕ) (hu : (u : Filter ℕ)≤atTop)
    (s : ℕ → Set ℕ) (hs : ∀ n, s n ∈ u) :
    ∃ k : ℕ → ℕ, Tendsto k u atTop ∧ ∀ i, k i≠0 → ∀ j≤k i, i∈s j := by
  classical
  let P (i n : ℕ) := ∀ j≤n, i∈s j
  have he (n : ℕ) : ∀ᶠ i in (u : Filter ℕ), P i n := by
    induction n with
    | zero => simpa [P] using hs 0
    | succ n ih =>
      filter_upwards [ih,hs (n+1)] with i hi hin
      intro j hj
      rcases (Nat.le_succ_iff.mp hj) with hj | hj
      · exact hi j hj
      · simpa only [hj] using hin
  let k (i : ℕ) := Nat.findGreatest (P i) i
  refine ⟨k,?_,?_⟩
  · apply tendsto_atTop.2
    intro n
    filter_upwards [he n,hu (eventually_ge_atTop n)] with i hi hin
    exact Nat.le_findGreatest hin hi
  · intro i hi
    exact (Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest (P i) i=k i)).2.1 hi


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_UltraSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue
open Filter Topology
open scoped ComplexOrder ENNReal

namespace StarTerm
variable {C D E : Type*}
lemma map_eval [Ring D] [StarRing D] [Ring E] [StarRing E]
    {F : Type*} [FunLike F D E] [NonUnitalRingHomClass F D E] [StarHomClass F D E]
    (φ : F) (c : C → D) (x : D) (p : StarTerm C) :
    φ (p.eval c x)=p.eval (fun a => φ (c a)) (φ x) := by
  induction p <;> simp_all [eval,map_star]
end StarTerm

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

lemma ultra_q_tendsto (a : Sequences (A:=A) (ι:=ℕ)) :
    Tendsto (fun i => V.q (a i)) u (𝓝 (V.ultraQ u (V.ultraHom u a))) :=
  V.ultra_val_tendsto u (star a*a)

include hu in

lemma ultra_realize {ι : Type*} [Fintype ι] (P : ι → StarTerm (V.UltraQuotient u)) (t : ι → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ x : V.UltraQuotient u,
      ‖x‖ ≤ 1 ∧ ∀ j, |V.ultraQ u ((P j).eval id x)-t j| < ε) :
    ∃ x : V.UltraQuotient u, ∀ j, V.ultraQ u ((P j).eval id x)=t j := by
  classical
  let W := V.ultra u
  let Q := V.ultraHom u
  have lift (x : V.UltraQuotient u) : ∃ a : Sequences (A:=A) (ι:=ℕ), Q a=x := W.nullIdeal.mk_surjective x
  choose c hc using lift
  let ε (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose x hx hxt using fun n => h (ε n/2) (half_pos (hε n))
  have liftn (n : ℕ) : ∃ a : Sequences (A:=A) (ι:=ℕ), Q a=x n ∧ ‖a‖ < 2 := by
    obtain ⟨a,ha,hn⟩ := W.nullIdeal.norm_mk_lt (x n) zero_lt_one
    exact ⟨a,ha,hn.trans_le (by linarith [hx n])⟩
  choose a ha han using liftn
  let F (j : ι) (i : ℕ) (b : A) : ℝ := V.q ((P j).eval (fun d => c d i) b)-t j
  have ht (n : ℕ) (j : ι) :
      Tendsto (fun i => F j i (a n i)) u (𝓝 (V.ultraQ u ((P j).eval id (x n))-t j)) := by
    have he' : Q ((P j).eval c (a n))=(P j).eval id (x n) := by
      rw [StarTerm.map_eval Q,ha n]
      congr 2
      funext d
      exact hc d
    have heval (i : ℕ) : ((P j).eval c (a n)) i=(P j).eval (fun d => c d i) (a n i) := by
      have he := StarTerm.map_eval (seqEvalHom (A:=A) i) c (a n) (P j)
      simp only [seqEvalHom] at he
      exact he
    dsimp only [Q] at he'
    have hh := (V.ultra_q_tendsto u ((P j).eval c (a n))).sub_const (t j)
    simpa only [he',heval] using hh
  let s (n : ℕ) := {i | ∀ j, |F j i (a n i)| ≤ ε n}
  have hs (n : ℕ) : s n ∈ u := by
    have hj (j : ι) : ∀ᶠ i in (u : Filter ℕ), |F j i (a n i)| ≤ ε n := by
      have hlt : |V.ultraQ u ((P j).eval id (x n))-t j| < ε n := (hxt n j).trans (by linarith [hε n])
      exact ((ht n j).abs.eventually (eventually_lt_nhds hlt)).mono (fun _ h => h.le)
    exact Filter.eventually_all.mpr hj
  obtain ⟨k,hk,hgood⟩ := ultra_selector u hu s hs
  let b : Sequences (A:=A) (ι:=ℕ) := ⟨fun i => a (k i) i,memℓp_infty
    ⟨2,by rintro _ ⟨i,rfl⟩; exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (a (k i)) i).trans (han (k i)).le⟩⟩
  refine ⟨Q b,?_⟩
  intro j
  have hb : Tendsto (fun i => F j i (b i)) u (𝓝 0) := by
    have hbound : ∀ᶠ i in (u : Filter ℕ), |F j i (b i)| ≤ ε (k i) := by
      filter_upwards [hk (eventually_ge_atTop 1)] with i hi
      exact hgood i (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi)) (k i) le_rfl j
    apply squeeze_zero_norm' _ ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hk)
    simpa only [Real.norm_eq_abs,Function.comp_apply] using hbound
  have hqb : Q ((P j).eval c b)=(P j).eval id (Q b) := by
    rw [StarTerm.map_eval Q]
    congr 2
    funext d
    exact hc d
  have heval (i : ℕ) : ((P j).eval c b) i=(P j).eval (fun d => c d i) (b i) := by
    exact StarTerm.map_eval (seqEvalHom (A:=A) i) c b (P j)
  dsimp only [Q] at hqb
  have ht' := (V.ultra_q_tendsto u ((P j).eval c b)).sub_const (t j)
  have hz : V.ultraQ u ((P j).eval id (Q b))-t j=0 := by
    apply tendsto_nhds_unique _ hb
    simpa only [hqb,heval] using ht'
  exact sub_eq_zero.mp hz

end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
open scoped ComplexOrder ENNReal
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealSMulComm_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealTower_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealCFC_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraNonnegSpectrum_p0
include hu in

lemma ultra_polar_corner_oai (x p q : V.UltraQuotient u) (hp : IsStarProjection p)
    (hxp : x*p=x) (hqx : q*x=x) :
    ∃ v : V.UltraQuotient u, IsPartialIsometry v ∧
      v*CFC.sqrt (star x*x)=x ∧ q*v=v ∧ v*p=v := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (Sequences (A := A) (ι := ℕ)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (Sequences (A := A) (ι := ℕ)) :=
    CStarAlgebra.instNonnegSpectrumClass
  let W := V.ultra u
  let Q := V.ultraHom u
  let s := CFC.sqrt (star x*x)
  let z : StarTerm (V.UltraQuotient u) := .var
  let sub (a b : StarTerm (V.UltraQuotient u)) := StarTerm.add a (.neg b)
  let P : Fin 4 → StarTerm (V.UltraQuotient u) :=
    ![sub (.mul (.mul z (.star z)) z) z,
      sub (.mul z (.const s)) (.const x),
      sub (.mul (.const q) z) z,
      sub (.mul z (.const p)) z]
  have happ (ε : ℝ) (hε : 0 < ε) : ∃ v : V.UltraQuotient u,
      ‖v‖ ≤ 1 ∧ ∀ j : Fin 4, |V.ultraQ u ((P j).eval id v)-(0:ℝ)| < ε := by
    obtain ⟨a,ha⟩ := W.nullIdeal.mk_surjective x
    change Q a=x at ha
    obtain ⟨r,hr,hdef,herr⟩ := exists_good_polarCut W a (half_pos hε)
    let v := Q (polarCut a r)
    have hvcut : v=polarCut x r := by dsimp only [v]; rw [map_polarCut Q a hr,ha]
    have hnorm : ‖v‖ ≤ 1 :=
      (W.nullIdeal.norm_mk_le (polarCut a r)).trans (polarCut_norm a hr)
    have hsqmap : Q (CFC.sqrt (star a*a))=s := by
      refine (map_cfc_sqrt Q _ (star_mul_self_nonneg a)).trans ?_
      rw [map_mul, map_star, ha]
      rfl
    have hdefmap : W.quotQ (v*star v*v-v)=W.q (polarCut a r*star (polarCut a r)*polarCut a r-polarCut a r) := by
      rw [← W.quotQ_map]
      congr 1

    have herrmap : W.quotQ (v*s-x)=W.q (polarCut a r*CFC.sqrt (star a*a)-a) := by
      rw [← W.quotQ_map]
      congr 1
      change v*s-x=Q (polarCut a r*CFC.sqrt (star a*a)-a)
      rw [map_sub,map_mul,hsqmap,ha]

    refine ⟨v,hnorm,?_⟩
    intro j
    fin_cases j <;> simp [P,sub,z,StarTerm.eval,← sub_eq_add_neg]
    · change |W.quotQ (v*star v*v-v)| < ε
      rw [abs_of_nonneg (W.quotQ_nonneg _),hdefmap]
      exact hdef.trans (by linarith)
    · change |W.quotQ (v*s-x)| < ε
      rw [abs_of_nonneg (W.quotQ_nonneg _),herrmap]
      exact ((W.q_bound _).trans herr).trans_lt (by linarith)
    · change |W.quotQ (q*v-v)| < ε
      have he : q*v=v := hvcut ▸ polarCut_left_corner hqx r
      rw [he,sub_self,W.quotQ_zero,abs_zero]
      exact hε
    · change |W.quotQ (v*p-v)| < ε
      have he : v*p=v := hvcut ▸ polarCut_right_corner hp hxp r
      rw [he,sub_self,W.quotQ_zero,abs_zero]
      exact hε
  obtain ⟨v,hv⟩ := V.ultra_realize u hu P (fun _ => 0) happ
  have he0 := hv 0
  have he1 := hv 1
  have he2 := hv 2
  have he3 := hv 3
  simp [P,sub,z,StarTerm.eval,← sub_eq_add_neg] at he0 he1 he2 he3
  have h0 : v*star v*v-v=0 := (W.quotQ_eq_zero _).mp he0
  have h1 : v*s-x=0 := (W.quotQ_eq_zero _).mp he1
  have h2 : q*v-v=0 := (W.quotQ_eq_zero _).mp he2
  have h3 : v*p-v=0 := (W.quotQ_eq_zero _).mp he3
  exact ⟨v,sub_eq_zero.mp h0,sub_eq_zero.mp h1,sub_eq_zero.mp h2,sub_eq_zero.mp h3⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner_oai.{u_1} := @OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner_oai.{u_1}
