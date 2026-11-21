-- Prove2me | solution 1 for MasulloRH.theta_translate_density_of_mertens_bound
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:29:56.563172+00:00
-- url     : https://prove2.me/submissions/4bdbae60-2c51-4a6c-98af-6e656970db1f

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Theorems.Thm_MasulloAudit_window_mellin_evaluation_bounded
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

section StandaloneCyclicHilbertDensity

open MeasureTheory Set Filter
open MasulloRH.GaussianApproximation
open scoped ENNReal Topology
namespace MasulloCyclic
noncomputable section

def windowMeasure (c b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (2*c*x+2*b*|x|)))

private theorem cyclic_CyclicHilbertDensity_expWindow_continuous (c b : ℝ) :
    Continuous (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)) := by fun_prop

instance window_finite_on_compacts (c b : ℝ) : IsFiniteMeasureOnCompacts (windowMeasure c b) where
  lt_top_of_isCompact := by
    intro K hK
    rw [windowMeasure,withDensity_apply _ hK.measurableSet,←ofReal_integral_eq_lintegral_ofReal]
    · exact ENNReal.ofReal_lt_top
    · exact (cyclic_CyclicHilbertDensity_expWindow_continuous c b).continuousOn.integrableOn_compact hK
    · exact Eventually.of_forall (fun _ => (Real.exp_nonneg _))

theorem window_integral_norm_sq (c b : ℝ) (f : ℝ → ℂ) :
    (∫ x : ℝ, ‖f x‖^2 ∂windowMeasure c b) = energy c b f := by
  rw [windowMeasure,integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (2*c*x+2*b*|x|))) by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [energy,ENNReal.toReal_ofReal (Real.exp_nonneg _),smul_eq_mul]

theorem window_memLp_of_energy (c b : ℝ) {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (windowMeasure c b))
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2)) :
    MemLp f 2 (windowMeasure c b) := by
  apply (memLp_two_iff_integrable_sq_norm hf).2
  rw [windowMeasure,integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (2*c*x+2*b*|x|))) by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _),smul_eq_mul] using hi

theorem norm_toLp_sq_eq_energy (c b : ℝ) (f : ℝ → ℂ) (hf : MemLp f 2 (windowMeasure c b)) :
    ‖hf.toLp f‖^2 = energy c b f := by
  rw [←window_integral_norm_sq,Lp.norm_toLp,hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,←one_div (2:ℝ),←Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))]

theorem compact_window_dense (c b : ℝ) :
    Dense {u : Lp ℂ 2 (windowMeasure c b) | ∃ f : ℝ → ℂ, Continuous f ∧
      HasCompactSupport f ∧ (u : ℝ→ℂ) =ᵐ[windowMeasure c b] f} := by
  intro u
  apply (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2
  intro ε hε
  obtain ⟨g,hcs,herr,hc,hm⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num) hε.ne'
  refine ⟨hm.toLp g,⟨g,hc,hcs,hm.coeFn_toLp⟩,?_⟩
  rwa [Metric.mem_closedEBall',←Lp.toLp_coeFn u (Lp.memLp u),Lp.edist_toLp_toLp]

/-- Any continuous family which approximates compact targets in finite Gram energy
is dense in the Hilbert space of the actual weighted measure. -/
theorem dense_of_compact_energy_approx (c b : ℝ) (S : Set (ℝ→ℂ))
    (hc : ∀ g ∈ S, Continuous g)
    (ha : ∀ f : ℝ→ℂ, Continuous f → HasCompactSupport f → ∀ δ > (0:ℝ),
      ∃ g ∈ S, Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x-g x‖^2) ∧
        energy c b (fun x => f x-g x) < δ) :
    Dense {u : Lp ℂ 2 (windowMeasure c b) | ∃ g ∈ S, (u : ℝ→ℂ) =ᵐ[windowMeasure c b] g} := by
  let D : Set (Lp ℂ 2 (windowMeasure c b)) := {u | ∃ g ∈ S, (u:ℝ→ℂ) =ᵐ[windowMeasure c b] g}
  have hD : ∀ u : Lp ℂ 2 (windowMeasure c b), (∃ f : ℝ → ℂ, Continuous f ∧
      HasCompactSupport f ∧ (u : ℝ→ℂ) =ᵐ[windowMeasure c b] f) → u ∈ closure D := by
    rintro u ⟨f,hf,hcs,hu⟩
    have hfm := (memLp_congr_ae hu).mp (Lp.memLp u)
    have hu' : hfm.toLp f = u := by
      apply Lp.ext
      exact hfm.coeFn_toLp.trans hu.symm
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨g,hg,hI,he⟩ := ha f hf hcs (ε^2) (by positivity)
    have hm := window_memLp_of_energy c b (hf.sub (hc g hg)).aestronglyMeasurable hI
    have hgm : MemLp g 2 (windowMeasure c b) := by
      convert! hfm.sub hm using 1
      funext x
      change g x = f x - (f x - g x)
      abel
    refine ⟨hgm.toLp g,⟨g,hg,hgm.coeFn_toLp⟩,?_⟩
    rw [←hu',dist_eq_norm]
    have heq : ‖hfm.toLp f - hgm.toLp g‖^2 = energy c b (fun x => f x-g x) := by
      rw [←MemLp.toLp_sub]
      exact norm_toLp_sq_eq_energy c b _ _
    nlinarith only [heq,he,hε,norm_nonneg (hfm.toLp f-hgm.toLp g)]
  intro u
  have hmem := (compact_window_dense c b) u
  have hs := closure_mono (s := {v : Lp ℂ 2 (windowMeasure c b) | ∃ f : ℝ → ℂ,
    Continuous f ∧ HasCompactSupport f ∧ (v : ℝ→ℂ) =ᵐ[windowMeasure c b] f}) (t := closure D) (fun x hx => hD x hx)
  simpa only [closure_closure] using hs hmem

end
end MasulloCyclic

end StandaloneCyclicHilbertDensity

section StandaloneCyclicClosure

open Set Filter
open scoped Topology BigOperators
namespace MasulloCyclic
noncomputable section

abbrev F := ℝ → ℂ

def w (A B x : ℝ) := max (Real.exp (A*x)) (Real.exp (B*x))
theorem w_pos (A B x : ℝ) : 0 < w A B x := lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)

/-- The comparison constant when a real logarithmic shift is moved across the weight. -/
theorem w_shift (A B x y : ℝ) :
    w A B x ≤ max (Real.exp (-A*y)) (Real.exp (-B*y)) * w A B (x+y) := by
  unfold w
  apply max_le
  · calc
      _ = Real.exp (-A*y)*Real.exp (A*(x+y)) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul (le_max_left _ _) (le_max_left _ _) (Real.exp_nonneg _)
        (le_trans (Real.exp_nonneg _) (le_max_left _ _))
  · calc
      _ = Real.exp (-B*y)*Real.exp (B*(x+y)) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul (le_max_right _ _) (le_max_right _ _) (Real.exp_nonneg _)
        (le_trans (Real.exp_nonneg _) (le_max_right _ _))

def shift (y : ℝ) (f : F) : F := fun x => f (x+y)

def translates (f : F) : Submodule ℂ F := Submodule.span ℂ (Set.range (fun y : ℝ => shift y f))

def approx (A B : ℝ) (S : Submodule ℂ F) : Submodule ℂ F where
  carrier := {f | ∀ ε : ℝ, 0 < ε → ∃ g ∈ S, ∀ x, w A B x * ‖f x-g x‖ ≤ ε}
  zero_mem' := by intro ε h; exact ⟨0,S.zero_mem,fun x => by simpa using h.le⟩
  add_mem' := by
    intro f g hf hg ε hε
    obtain ⟨a,ha,he⟩ := hf (ε/2) (half_pos hε)
    obtain ⟨b,hb,hf'⟩ := hg (ε/2) (half_pos hε)
    refine ⟨a+b,S.add_mem ha hb,fun x => ?_⟩
    change w A B x * ‖f x+g x-(a x+b x)‖ ≤ ε
    rw [show f x+g x-(a x+b x) = (f x-a x)+(g x-b x) by abel]
    calc
      _ ≤ w A B x*(‖f x-a x‖+‖g x-b x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (w_pos _ _ _).le
      _ ≤ ε := by rw [mul_add]; linarith [he x,hf' x]
  smul_mem' := by
    intro c f hf ε hε
    by_cases hc : c=0
    · subst c; exact ⟨0,S.zero_mem,fun x => by simpa using hε.le⟩
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    obtain ⟨a,ha,he⟩ := hf (ε/‖c‖) (div_pos hε hcn)
    refine ⟨c • a,S.smul_mem c ha,fun x => ?_⟩
    change w A B x*‖c*f x-c*a x‖ ≤ ε
    rw [←mul_sub,norm_mul,mul_left_comm]
    exact (le_div_iff₀ hcn).mp (he x) |> fun h => by simpa only [mul_comm ‖c‖] using h

theorem mem_approx {A B : ℝ} {S : Submodule ℂ F} {f : F} :
    f ∈ approx A B S ↔ ∀ ε : ℝ, 0 < ε → ∃ g ∈ S, ∀ x, w A B x * ‖f x-g x‖ ≤ ε := Iff.rfl

theorem subset_approx {A B : ℝ} (S : Submodule ℂ F) : S ≤ approx A B S := by
  intro f hf ε hε
  exact ⟨f,hf,fun x => by simpa using hε.le⟩

theorem approx_mono {A B : ℝ} {S T : Submodule ℂ F} (h : S ≤ T) :
    approx A B S ≤ approx A B T := by
  intro f hf ε he
  obtain ⟨g,hg,hh⟩ := hf ε he
  exact ⟨g,h hg,hh⟩

theorem approx_idem {A B : ℝ} (S : Submodule ℂ F) :
    approx A B (approx A B S) ≤ approx A B S := by
  intro f hf ε hε
  obtain ⟨g,hg,e₁⟩ := hf (ε/2) (half_pos hε)
  obtain ⟨h,hh,e₂⟩ := hg (ε/2) (half_pos hε)
  refine ⟨h,hh,fun x => ?_⟩
  calc
    _ ≤ w A B x*(‖f x-g x‖+‖g x-h x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) (w_pos _ _ _).le
    _ ≤ ε := by rw [mul_add]; linarith [e₁ x,e₂ x]

theorem shift_translate_mem (f : F) (y : ℝ) : shift y f ∈ translates f :=
  Submodule.subset_span ⟨y,rfl⟩

theorem shift_preserves_span (f : F) (y : ℝ) {g : F} (hg : g ∈ translates f) :
    shift y g ∈ translates f := by
  induction hg using Submodule.span_induction with
  | mem g he =>
    obtain ⟨z,rfl⟩ := he
    exact (show shift y (shift z f) = shift (y+z) f by ext x; simp [shift,add_assoc]) ▸ shift_translate_mem f (y+z)
  | zero => exact (translates f).zero_mem
  | add a b _ _ ha hb => exact (translates f).add_mem ha hb
  | smul c a _ ha => exact (translates f).smul_mem c ha

theorem shift_preserves_approx {A B : ℝ} (f : F) (y : ℝ) {g : F}
    (hg : g ∈ approx A B (translates f)) : shift y g ∈ approx A B (translates f) := by
  intro ε hε
  let C := max (Real.exp (-A*y)) (Real.exp (-B*y))
  have hC : 0 < C := lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  obtain ⟨h,hh,he⟩ := hg (ε/C) (div_pos hε hC)
  refine ⟨shift y h,shift_preserves_span f y hh,fun x => ?_⟩
  change w A B x*‖g (x+y)-h (x+y)‖ ≤ _
  calc
    _ ≤ C*w A B (x+y)*‖g (x+y)-h (x+y)‖ :=
      mul_le_mul_of_nonneg_right (w_shift _ _ _ _) (norm_nonneg _)
    _ ≤ ε := by rw [mul_assoc,mul_comm C]; exact (le_div_iff₀ hC).mp (he _)

theorem generators_change {A B : ℝ} {f g : F} (h : g ∈ approx A B (translates f)) :
    approx A B (translates g) ≤ approx A B (translates f) := by
  apply (approx_mono (T:=approx A B (translates f)) ?_).trans (approx_idem _)
  apply Submodule.span_le.mpr
  rintro _ ⟨y,rfl⟩
  exact shift_preserves_approx f y h

end
end MasulloCyclic

end StandaloneCyclicClosure

section StandaloneCyclicQuant

open Set Filter
open scoped Topology BigOperators
namespace MasulloCyclic
noncomputable section

theorem finite_span {v f : F} (hf : f ∈ translates v) :
    ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → ℝ),
      ∀ x : ℝ, f x = ∑ i, a i*v (x+y i) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨z,rfl⟩ := h
    exact ⟨1,fun _ => 1,fun _ => z,fun x => by simp [shift]⟩
  | zero => exact ⟨0,Fin.elim0,Fin.elim0,by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨m,a,y,he⟩ := hf
    obtain ⟨n,b,z,hf⟩ := hg
    refine ⟨m+n,Fin.append a b,Fin.append y z,fun x => ?_⟩
    simp [Fin.sum_univ_add,he,hf]
  | smul c f _ hf =>
    obtain ⟨m,a,y,h⟩ := hf
    refine ⟨m,fun i => c*a i,y,fun x => ?_⟩
    simp [h,Finset.mul_sum,mul_assoc]

def ratc (p : ℚ × ℚ) : ℂ := (p.1:ℂ)+(p.2:ℂ)*Complex.I

private theorem cyclic_CyclicQuant_ratc_dense (c : ℂ) {ε : ℝ} (hε : 0<ε) : ∃ p : ℚ × ℚ, ‖c-ratc p‖ ≤ ε := by
  obtain ⟨r,hr1,hr2⟩ := exists_rat_btwn (show c.re-ε/2<c.re by linarith)
  obtain ⟨s,hs1,hs2⟩ := exists_rat_btwn (show c.im-ε/2<c.im by linarith)
  refine ⟨(r,s),?_⟩
  have h := Complex.norm_le_abs_re_add_abs_im (c-ratc (r,s))
  simp [ratc,Complex.sub_re,Complex.sub_im,abs_of_nonneg (sub_nonneg.mpr hr2.le),
    abs_of_nonneg (sub_nonneg.mpr hs2.le)] at h
  exact h.trans (by linarith)

private theorem cyclic_CyclicQuant_bounded_right_shift {A B C : ℝ} (hA : 0≤A) (hB : 0≤B)
    (v : ℝ → ℝ) (hv : ∀x, 0≤v x) (hC : ∀x, w A B x*v x ≤ C)
    (y : ℝ) {z : ℝ} (hz : y≤z) (x : ℝ) :
    w A B x*v (x+z) ≤ max (Real.exp (-A*y)) (Real.exp (-B*y)) * C := by
  let M := max (Real.exp (-A*y)) (Real.exp (-B*y))
  have hM : 0≤M := (Real.exp_nonneg _).trans (le_max_left _ _)
  have hmono : w A B (x+y) ≤ w A B (x+z) :=
    max_le_max (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hA (sub_nonneg.mpr hz)]))
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hB (sub_nonneg.mpr hz)]))
  have h := (w_shift A B x y).trans (mul_le_mul_of_nonneg_left hmono hM)
  calc
    _ ≤ (M * w A B (x+z))*v (x+z) := mul_le_mul_of_nonneg_right h (hv _)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hC _) hM

private theorem cyclic_CyclicQuant_approximate_column {A B C : ℝ} (hA : 0≤A) (hB : 0≤B) (v : F)
    (hd : Differentiable ℝ v) (hC : 0≤C)
    (hv : ∀x, w A B x * ‖v x‖ ≤ C) (hv' : ∀x, w A B x * ‖deriv v x‖ ≤ C)
    (a : ℂ) (y : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ (p : ℚ × ℚ) (q : ℚ), ∀ x : ℝ,
      w A B x * ‖a*v (x+y)-ratc p*v (x+q)‖ ≤ ε := by
  let L := max (Real.exp (-A*y)) (Real.exp (-B*y))*C
  have hL : 0 ≤ L := mul_nonneg ((Real.exp_nonneg _).trans (le_max_left _ _)) hC
  let η := ε/((‖a‖+1)*(L+1))
  have hη : 0<η := div_pos hε (mul_pos (by positivity) (by linarith))
  obtain ⟨q,hqy,hq⟩ := exists_rat_btwn (show y < y+η by linarith)
  obtain ⟨p,hp⟩ := cyclic_CyclicQuant_ratc_dense a hη
  refine ⟨p,q,fun x => ?_⟩
  have hww := w_pos A B x
  have hder (t : ℝ) (ht : t ∈ Icc (x+y) (x+q)) : ‖deriv v t‖ ≤ L / w A B x := by
    rw [le_div_iff₀ hww,mul_comm]
    have h := cyclic_CyclicQuant_bounded_right_shift hA hB (fun z => ‖deriv v z‖) (fun _ => norm_nonneg _) hv' y
      (show y≤t-x by linarith [ht.1]) x
    simpa only [show x+(t-x)=t by ring] using h
  have hxy : x+y ≤ x+(q:ℝ) := by linarith
  have hdif := (convex_Icc (x+y) (x+(q:ℝ))).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hd z) hder (right_mem_Icc.mpr hxy) (left_mem_Icc.mpr hxy)
  have hdiff : w A B x * ‖v (x+y)-v (x+q)‖ ≤ L*η := by
    rw [Real.norm_eq_abs,show x+y-(x+(q:ℝ))=y-q by ring,
      abs_of_nonpos (by linarith : y-(q:ℝ) ≤ 0)] at hdif
    have aux := (mul_le_mul_of_nonneg_left hdif hww.le)
    have hh : w A B x * ((L/w A B x) * -(y-(q:ℝ))) = L*((q:ℝ)-y) := by field_simp; ring
    rw [hh] at aux
    exact aux.trans (mul_le_mul_of_nonneg_left (by linarith) hL)
  have hvq := cyclic_CyclicQuant_bounded_right_shift hA hB (fun z => ‖v z‖) (fun _ => norm_nonneg _) hv y hqy.le x
  change w A B x*‖v (x+q)‖ ≤ L at hvq
  have hr := norm_add_le (a*(v (x+y)-v (x+q))) ((a-ratc p)*v (x+q))
  rw [show a*(v (x+y)-v (x+q))+(a-ratc p)*v (x+q)=a*v (x+y)-ratc p*v (x+q) by ring,
    norm_mul,norm_mul] at hr
  have hh := mul_le_mul_of_nonneg_left hr hww.le
  have h1 := mul_le_mul_of_nonneg_left hdiff (norm_nonneg a)
  have h2 := mul_le_mul hp hvq (mul_nonneg hww.le (norm_nonneg _)) hη.le
  have h3 := (div_mul_cancel₀ ε (by positivity : (‖a‖+1)*(L+1) ≠ 0))
  change η * ((‖a‖+1)*(L+1)) = ε at h3
  nlinarith [mul_nonneg hη.le (norm_nonneg a)]

theorem finite_rationalization {A B C : ℝ} (hA : 0≤A) (hB : 0≤B) (v : F)
    (hd : Differentiable ℝ v) (hC : 0≤C)
    (hv : ∀x, w A B x * ‖v x‖ ≤ C) (hv' : ∀x, w A B x * ‖deriv v x‖ ≤ C)
    {f : F} (hf : f ∈ approx A B (translates v)) {ε : ℝ} (hε : 0<ε) :
    ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ), ∀x,
      w A B x * ‖f x-∑i,ratc (a i)*v (x-(y i:ℝ))‖ ≤ ε := by
  classical
  obtain ⟨g,hg,hfg⟩ := hf (ε/2) (half_pos hε)
  obtain ⟨m,d,z,he⟩ := finite_span hg
  let η : ℝ := ε/(2*((m:ℝ)+1))
  have hh : 0<η := by dsimp [η]; positivity
  have hex := fun i => cyclic_CyclicQuant_approximate_column hA hB v hd hC hv hv' (d i) (z i) hh
  choose p q hp using hex
  refine ⟨m,p,fun i => -q i,fun x => ?_⟩
  simp only [Rat.cast_neg,sub_neg_eq_add]
  have hgerr : w A B x*‖g x-∑i,ratc (p i)*v (x+(q i:ℝ))‖ ≤ (m:ℝ)*η := by
    rw [he,←Finset.sum_sub_distrib]
    calc
      _ ≤ w A B x*∑ i, ‖d i*v (x+z i)-ratc (p i)*v (x+(q i:ℝ))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (w_pos _ _ _).le
      _ = ∑ i, w A B x*‖d i*v (x+z i)-ratc (p i)*v (x+(q i:ℝ))‖ := Finset.mul_sum ..
      _ ≤ ∑ _i : Fin m, η := Finset.sum_le_sum (fun i _ => hp i x)
      _ = _ := by simp
  have hn : (m:ℝ)*η ≤ ε/2 := by
    have h' : (m:ℝ)+1>0 := by positivity
    dsimp [η]; field_simp; nlinarith
  have ht := mul_le_mul_of_nonneg_left
    (norm_sub_le_norm_sub_add_norm_sub (f x) (g x) (∑i,ratc (p i)*v (x+(q i:ℝ)))) (w_pos A B x).le
  rw [mul_add] at ht
  linarith [hfg x]

end
end MasulloCyclic

end StandaloneCyclicQuant

section StandaloneCyclicHilbertRational

open MeasureTheory Set Filter
open MasulloRH.GaussianApproximation
open scoped ENNReal Topology
namespace MasulloCyclic
noncomputable section

theorem rational_theta_dense_of_compact_approx (c b : ℝ) (hθ : Continuous theta)
    (ha : ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → ∀ δ > (0:ℝ),
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        let r (x : ℝ) := f x - ∑ i, ratc (a i) * theta (x-(y i:ℝ))
        Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖r x‖^2) ∧ energy c b r < δ) :
    Dense {u : Lp ℂ 2 (windowMeasure c b) |
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        (u:ℝ→ℂ) =ᵐ[windowMeasure c b] fun x => ∑ i, ratc (a i)*theta (x-(y i:ℝ))} := by
  let S : Set (ℝ → ℂ) := {g | ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
    g = fun x => ∑ i, ratc (a i)*theta (x-(y i:ℝ))}
  have hc : ∀ g ∈ S, Continuous g := by
    rintro _ ⟨m,a,y,rfl⟩
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hθ.comp (continuous_id.sub continuous_const)))
  have h := dense_of_compact_energy_approx c b S hc (fun f hf hcs δ hδ => by
    obtain ⟨m,a,y,h⟩ := ha f hf hcs δ hδ
    exact ⟨_,⟨m,a,y,rfl⟩,h⟩)
  apply h.mono
  rintro u ⟨g,⟨m,a,y,rfl⟩,hg⟩
  exact ⟨m,a,y,hg⟩

/-- The diagonal Gram entry of one translate is its physical squared norm. -/
theorem theta_translate_memLp (c b : ℝ) (hlo : 0 < c-b) (hhi : c+b < 1)
    (hθ : Continuous theta) (y : ℚ) : MemLp (fun x : ℝ => theta (x-(y:ℝ))) 2 (windowMeasure c b) := by
  have hgram := (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1
    1 0 c b 1 (fun _ => 0) (fun _ => (y:ℝ)) (by norm_num) (by norm_num) hlo hhi).2.1
      (Fin.succ (0 : Fin 1)) (Fin.succ (0 : Fin 1))
  apply window_memLp_of_energy c b (f := fun x : ℝ => theta (x-(y:ℝ)))
    (hθ.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  simpa only [Fin.cons_succ,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _),pow_two,mul_assoc] using hgram.norm

/-- Density of rational finite sums also forces the closed complex span of the individual
rational translates in the Hilbert space to be all of that space. -/
theorem theta_span_eq_top_of_dense (c b : ℝ)
    (hm : ∀ y : ℚ, MemLp (fun x : ℝ => theta (x-(y:ℝ))) 2 (windowMeasure c b))
    (hd : Dense {u : Lp ℂ 2 (windowMeasure c b) |
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        (u:ℝ→ℂ) =ᵐ[windowMeasure c b] fun x => ∑ i, ratc (a i)*theta (x-(y i:ℝ))}) :
    (Submodule.span ℂ (Set.range (fun y : ℚ => (hm y).toLp _))).topologicalClosure = ⊤ := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  apply hd.mono
  rintro u ⟨m,a,y,hu⟩
  let v (i : Fin m) : Lp ℂ 2 (windowMeasure c b) :=
    ratc (a i) • (hm (y i)).toLp _
  have hv (i : Fin m) : ((v i) : ℝ→ℂ) =ᵐ[windowMeasure c b]
      fun x => ratc (a i)*theta (x-(y i:ℝ)) :=
    (Lp.coeFn_smul ..).trans ((hm (y i)).coeFn_toLp.fun_comp (fun z => ratc (a i)*z))
  have hsum : (↑(∑ i, v i : Lp ℂ 2 (windowMeasure c b)) : ℝ → ℂ) =ᵐ[windowMeasure c b]
      fun x => ∑ i, ratc (a i)*theta (x-(y i:ℝ)) := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ v,ae_all_iff.mpr hv] with x h₁ h₂
    simpa only [Finset.sum_apply] using h₁.trans (Finset.sum_congr rfl fun i _ => h₂ i)
  have hu' : u = ∑ i, v i := Lp.ext (hu.trans hsum.symm)
  rw [hu']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self (y i)))

/-- Closed span formulation without a choice of representatives of the translations. -/
theorem theta_ae_span_eq_top_of_dense (c b : ℝ) (hlo : 0<c-b) (hhi : c+b<1) (hθ : Continuous theta)
    (hd : Dense {u : Lp ℂ 2 (windowMeasure c b) |
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        (u:ℝ→ℂ) =ᵐ[windowMeasure c b] fun x => ∑ i, ratc (a i)*theta (x-(y i:ℝ))}) :
    (Submodule.span ℂ {u : Lp ℂ 2 (windowMeasure c b) | ∃ y : ℚ,
      (u:ℝ→ℂ) =ᵐ[windowMeasure c b] fun x => theta (x-(y:ℝ))}).topologicalClosure = ⊤ := by
  let hm := theta_translate_memLp c b hlo hhi hθ
  have hs : Set.range (fun y : ℚ => (hm y).toLp _) =
      {u : Lp ℂ 2 (windowMeasure c b) | ∃ y : ℚ, (u:ℝ→ℂ) =ᵐ[windowMeasure c b] fun x => theta (x-(y:ℝ))} := by
    ext u
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,(hm y).coeFn_toLp⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Lp.ext ((hm y).coeFn_toLp.trans hy.symm)⟩
  rw [←hs]
  exact theta_span_eq_top_of_dense c b hm hd

end
end MasulloCyclic

end StandaloneCyclicHilbertRational

section StandaloneCyclicWeightedEnergy

open MeasureTheory Set Filter
open MasulloRH.GaussianApproximation
open scoped Topology
namespace MasulloCyclic
noncomputable section

private theorem cyclic_CyclicWeightedEnergy_window_gap_bound (c b A' B' x : ℝ) :
    Real.exp (c*x+b*|x|) ≤
      Real.exp (-min (c-b-A') (B'-(c+b))*|x|) * w A' B' x := by
  let k := min (c-b-A') (B'-(c+b))
  change _ ≤ Real.exp (-k*|x|)*w A' B' x
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    calc
      _ ≤ Real.exp (-k*x) * Real.exp (B'*x) := by
        rw [←Real.exp_add,Real.exp_le_exp]
        have h : k ≤ B'-(c+b) := min_le_right _ _
        nlinarith only [mul_le_mul_of_nonneg_right h hx]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right ..) (Real.exp_nonneg _)
  · have hnx := le_of_not_ge hx
    rw [abs_of_nonpos hnx]
    calc
      _ ≤ Real.exp (-k*(-x)) * Real.exp (A'*x) := by
        rw [←Real.exp_add,Real.exp_le_exp]
        have h : k ≤ c-b-A' := min_le_left _ _
        nlinarith only [mul_le_mul_of_nonpos_right h hnx]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left ..) (Real.exp_nonneg _)

/-- A widened weighted sup bound controls the squared error in the interior physical norm. -/
theorem weighted_energy_le (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (c b A' B' ε : ℝ) (hL : A' < c-b) (hR : c+b < B')
    (hbound : ∀ x, w A' B' x*‖f x‖ ≤ ε) :
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2) ∧
      energy c b f ≤ ε^2 / min (c-b-A') (B'-(c+b)) := by
  let k := min (c-b-A') (B'-(c+b))
  have hk : 0 < k := lt_min (sub_pos.mpr hL) (sub_pos.mpr hR)
  obtain ⟨hK,hKI,_,_⟩ := MasulloAudit.window_mellin_evaluation_bounded k hk 0 (by simpa using hk)
  simp only [Complex.zero_re,mul_zero,zero_mul,zero_sub,sub_zero,add_zero] at hK hKI
  let E (x : ℝ) := Real.exp (2*c*x+2*b*|x|)*‖f x‖^2
  let K (x : ℝ) := ε^2*Real.exp (-(2*k*|x|))
  have hK' : Integrable K := hK.const_mul _
  have hE (x : ℝ) : E x ≤ K x := by
    have he : Real.exp (c*x+b*|x|)*‖f x‖ ≤ Real.exp (-k*|x|)*ε := by
      calc
        _ ≤ (Real.exp (-k*|x|)*w A' B' x)*‖f x‖ :=
          mul_le_mul_of_nonneg_right (cyclic_CyclicWeightedEnergy_window_gap_bound _ _ _ _ _) (norm_nonneg _)
        _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hbound x) (Real.exp_nonneg _)
    have hp := pow_le_pow_left₀ (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) he 2
    simp only [mul_pow,←Real.exp_nat_mul,Nat.cast_ofNat] at hp
    convert! hp using 1 <;> dsimp [E,K] <;> ring_nf
  have hmeas : AEStronglyMeasurable E volume :=
    (show Continuous (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)) by fun_prop).aestronglyMeasurable.mul
      (hf.norm.pow 2)
  have hEi : Integrable E := hK'.mono' hmeas (Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ E x from mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
    exact hE x))
  refine ⟨hEi,(integral_mono hEi hK' hE).trans_eq ?_⟩
  change (∫ x, ε^2*Real.exp (-(2*k*|x|))) = ε^2/k
  rw [integral_const_mul,hKI]
  field_simp
  ring

/-- Arbitrarily small errors in the widened sup norm give arbitrarily small interior energy. -/
theorem exists_small_energy_of_wide_approx {ι : Type*} (err : ι → ℝ → ℂ)
    (hm : ∀ i, AEStronglyMeasurable (err i) volume)
    {c b A' B' : ℝ} (hL : A' < c-b) (hR : c+b < B')
    (ha : ∀ ε > (0:ℝ), ∃ i, ∀ x, w A' B' x * ‖err i x‖ ≤ ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ i, Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖err i x‖^2) ∧
      energy c b (err i) < δ := by
  let k := min (c-b-A') (B'-(c+b))
  have hk : 0 < k := lt_min (sub_pos.mpr hL) (sub_pos.mpr hR)
  let ε := Real.sqrt (δ*k/2)
  have hdk : 0 < δ*k/2 := by positivity
  obtain ⟨i,hi⟩ := ha ε (Real.sqrt_pos.mpr hdk)
  obtain ⟨hI,hE⟩ := weighted_energy_le _ (hm i) c b A' B' ε hL hR hi
  refine ⟨i,hI,hE.trans_lt ?_⟩
  change ε^2/k < δ
  rw [div_lt_iff₀ hk,show ε^2 = δ*k/2 from Real.sq_sqrt hdk.le]
  linarith

/-- A window strictly inside (β,1) has enough room for weighted sup approximation
to imply approximation in the canonical Gram energy. -/
theorem exists_small_energy_of_interior_approx {ι : Type*} (err : ι → ℝ → ℂ)
    (hm : ∀ i, AEStronglyMeasurable (err i) volume)
    {β c b : ℝ} (hβ : β < c-b) (hb : 0 ≤ b) (h1 : c+b < 1)
    (ha : ∀ a d : ℝ, β<a → a≤d → d<1 → ∀ ε > (0:ℝ), ∃ i, ∀ x, w a d x*‖err i x‖ ≤ ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ i, Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖err i x‖^2) ∧
      energy c b (err i) < δ := by
  apply exists_small_energy_of_wide_approx err hm
    (A' := (β+(c-b))/2) (B' := (1+(c+b))/2) (by linarith) (by linarith) _ hδ
  exact ha _ _ (by linarith) (by linarith) (by linarith)

end
end MasulloCyclic

end StandaloneCyclicWeightedEnergy

section StandaloneCyclicMobiusShift

open Set Filter
open scoped Topology
namespace MasulloRH.Cyclic
noncomputable section

def endpointWeight (A B x : ℝ) : ℝ := max (Real.exp (A*x)) (Real.exp (B*x))

theorem endpointWeight_pos (A B x : ℝ) : 0 < endpointWeight A B x :=
  lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)

private theorem cyclic_CyclicMobiusShift_weight_le_translate {A B t : ℝ} (hAB : A ≤ B) (ht : 0 ≤ t) (x : ℝ) :
    endpointWeight A B x ≤ Real.exp (-A*t) * endpointWeight A B (x+t) := by
  unfold endpointWeight
  rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le,← Real.exp_add,← Real.exp_add]
  apply max_le_max <;> apply Real.exp_le_exp.mpr <;> nlinarith [mul_nonneg (sub_nonneg.mpr hAB) ht]

private theorem cyclic_CyclicMobiusShift_weighted_translate_bound {A B C : ℝ} (hAB : A ≤ B) (f : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, endpointWeight A B x*f x ≤ C)
    (x t : ℝ) (ht : 0 ≤ t) :
    endpointWeight A B x * f (x+t) ≤ C * Real.exp (-A*t) := by
  calc
    _ ≤ (Real.exp (-A*t) * endpointWeight A B (x+t)) * f (x+t) :=
      mul_le_mul_of_nonneg_right (cyclic_CyclicMobiusShift_weight_le_translate hAB ht x) (hf _)
    _ ≤ _ := by rw [mul_assoc,mul_comm C]; gcongr; exact hb _

private lemma cyclic_CyclicMobiusShift_exp_neg_log_rpow {n : ℝ} (hn : 0 < n) (A : ℝ) :
    Real.exp (-A*Real.log n) = n^(-A) := by rw [Real.rpow_def_of_pos hn,mul_comm]

theorem weighted_log_shift_estimates {A B C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hC : 0 ≤ C)
    {Θ : ℝ → ℂ} (hd : Differentiable ℝ Θ)
    (hb : ∀ x, endpointWeight A B x * (‖Θ x‖ + ‖deriv Θ x‖) ≤ C)
    (x : ℝ) {n : ℝ} (hn : 1 ≤ n) :
    endpointWeight A B x * ‖Θ (x+Real.log n)‖ ≤ C*n^(-A) ∧
    endpointWeight A B x * ‖Θ (x+Real.log (n+1)) - Θ (x+Real.log n)‖ ≤ C*n^(-A-1) := by
  have hn0 : 0<n := lt_of_lt_of_le zero_lt_one hn
  have hw := endpointWeight_pos A B x
  have hΘ (s : ℝ) : endpointWeight A B s * ‖Θ s‖ ≤ C :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (endpointWeight_pos A B s).le).trans (hb s)
  have hΘ' (s : ℝ) : endpointWeight A B s * ‖deriv Θ s‖ ≤ C :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (endpointWeight_pos A B s).le).trans (hb s)
  constructor
  · simpa only [cyclic_CyclicMobiusShift_exp_neg_log_rpow hn0] using cyclic_CyclicMobiusShift_weighted_translate_bound hAB (fun s => ‖Θ s‖) (fun _ => norm_nonneg _) hΘ x _ (Real.log_nonneg hn)
  · let L := (C*n^(-A)) / endpointWeight A B x
    have hL : 0 ≤ L := div_nonneg (mul_nonneg hC (Real.rpow_nonneg hn0.le _)) hw.le
    have hmono : Real.log n ≤ Real.log (n+1) := Real.log_le_log hn0 (by linarith)
    have hder (y : ℝ) (hy : y ∈ Icc (x+Real.log n) (x+Real.log (n+1))) : ‖deriv Θ y‖ ≤ L := by
      have ht : Real.log n ≤ y-x := by linarith [hy.1]
      have htrans := cyclic_CyclicMobiusShift_weighted_translate_bound hAB (fun s => ‖deriv Θ s‖) (fun _ => norm_nonneg _) hΘ' x
        (y-x) ((Real.log_nonneg hn).trans ht)
      rw [show x+(y-x)=y by ring] at htrans
      apply (le_div_iff₀ hw).mpr
      rw [mul_comm]
      apply htrans.trans
      exact mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hA (sub_nonneg.mpr ht)])).trans_eq (cyclic_CyclicMobiusShift_exp_neg_log_rpow hn0 A)) hC
    have hdiff := (convex_Icc (x+Real.log n) (x+Real.log (n+1))).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hd z) hder (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith),add_sub_add_left_eq_sub] at hdiff
    have hlog : Real.log (n+1) - Real.log n ≤ n⁻¹ := by
      rw [← Real.log_div (by positivity) hn0.ne']
      exact (Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by field_simp; ring)
    have hfinal := mul_le_mul_of_nonneg_left (hdiff.trans (mul_le_mul_of_nonneg_left hlog hL)) hw.le
    apply hfinal.trans_eq
    dsimp [L]
    rw [show -A-1=(-A)+(-1) by ring,Real.rpow_add hn0,Real.rpow_neg_one]
    field_simp

end
end MasulloRH.Cyclic

end StandaloneCyclicMobiusShift

section StandaloneCyclicMobius

open Set Filter Asymptotics
open scoped Topology
namespace MasulloRH.Cyclic
noncomputable section

private def cyclic_CyclicMobius_μ₁ (n : ℕ) : ℂ := (ArithmeticFunction.moebius (n+1) : ℂ)
private def cyclic_CyclicMobius_M (n : ℕ) : ℂ := ∑ j ∈ Finset.range n, cyclic_CyclicMobius_μ₁ j

private theorem cyclic_CyclicMobius_M_eq (n : ℕ) : cyclic_CyclicMobius_M n = ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i:ℂ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, cyclic_CyclicMobius_M, cyclic_CyclicMobius_μ₁, Nat.add_comm 1]

private theorem cyclic_CyclicMobius_uniform_abel {A B β C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hβ : β<A) (hC : 0 ≤ C)
    (hM : cyclic_CyclicMobius_M =O[atTop] fun n : ℕ => (n:ℝ)^β)
    {Θ target : ℝ → ℂ} (hd : Differentiable ℝ Θ)
    (hb : ∀ x, endpointWeight A B x*(‖Θ x‖ + ‖deriv Θ x‖) ≤ C)
    (hlim : ∀ x, Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, cyclic_CyclicMobius_μ₁ j*Θ (x+Real.log ((j:ℝ)+1)))
      atTop (𝓝 (target x))) : ∀ ε>0, ∃ N : ℕ, ∀ x : ℝ,
      endpointWeight A B x*‖(∑ j ∈ Finset.range N, cyclic_CyclicMobius_μ₁ j*Θ (x+Real.log ((j:ℝ)+1))) - target x‖ ≤ ε := by
  let w (x : ℝ) := endpointWeight A B x
  let F (n : ℕ) (x : ℝ) := (w x:ℂ)*Θ (x+Real.log ((n:ℝ)+1))
  let back (n : ℕ) (x : ℝ) := F n x * cyclic_CyclicMobius_M (n+1)
  let jumps (n : ℕ) (x : ℝ) := (F (n+1) x - F n x)*cyclic_CyclicMobius_M (n+1)
  let weighted (n : ℕ) (x : ℝ) := (w x:ℂ)*(∑ j ∈ Finset.range n, cyclic_CyclicMobius_μ₁ j*Θ (x+Real.log ((j:ℝ)+1)))
  have hw (x : ℝ) : 0 ≤ w x := (endpointWeight_pos _ _ _).le
  have hFn (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ C*((n:ℝ)+1)^(-A) := by
    simpa only [F,w,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw x)] using
      (weighted_log_shift_estimates hA hAB hC hd hb x (show 1 ≤ (n:ℝ)+1 by linarith [show (0:ℝ)≤n by positivity])).1
  have hdiff (n : ℕ) (x : ℝ) : ‖F (n+1) x-F n x‖ ≤ C*((n:ℝ)+1)^(-A-1) := by
    simp only [F,← mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw x),Nat.cast_add,Nat.cast_one]
    exact (weighted_log_shift_estimates hA hAB hC hd hb x (show 1 ≤ (n:ℝ)+1 by linarith [show (0:ℝ)≤n by positivity])).2
  obtain ⟨K,hK,hKbound⟩ := hM.exists_pos
  have hm : ∀ᶠ n : ℕ in atTop, ‖cyclic_CyclicMobius_M (n+1)‖ ≤ K*((n:ℝ)+1)^β := by
    have H := (tendsto_add_atTop_nat 1).eventually hKbound.bound
    filter_upwards [H] with n hn
    simpa only [Nat.cast_add,Nat.cast_one,Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0≤(n:ℝ)+1) β)] using hn
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ‖back n x‖ ≤ C*K*((n:ℝ)+1)^(β-A) := by
    filter_upwards [hm] with n hn
    intro x
    simp only [back,norm_mul]
    calc
      _ ≤ (C*((n:ℝ)+1)^(-A))*(K*((n:ℝ)+1)^β) :=
        mul_le_mul (hFn n x) hn (norm_nonneg _) (by positivity)
      _ = _ := by rw [show β-A = (-A)+β by ring,Real.rpow_add (by positivity)]; ring
  have hjump : ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ‖jumps n x‖ ≤ C*K*((n:ℝ)+1)^(β-A-1) := by
    filter_upwards [hm] with n hn
    intro x
    simp only [jumps,norm_mul]
    calc
      _ ≤ (C*((n:ℝ)+1)^(-A-1))*(K*((n:ℝ)+1)^β) :=
        mul_le_mul (hdiff n x) hn (norm_nonneg _) (by positivity)
      _ = _ := by rw [show β-A-1 = (-A-1)+β by ring,Real.rpow_add (by positivity)]; ring
  have hR : Tendsto (fun n : ℕ => C*K*((n:ℝ)+1)^(β-A)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).comp ht
    simpa only [Function.comp_def,neg_sub,mul_zero] using (tendsto_const_nhds (x:=C*K)).mul h
  have hback : TendstoUniformly back (fun _ => 0) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hbound,hR.eventually (Iio_mem_nhds hε)] with n hn he x
    simpa using (hn x).trans_lt he
  have hs : Summable (fun n : ℕ => C*K*((n:ℝ)+1)^(β-A-1)) := by
    apply Summable.mul_left
    have h := (summable_nat_add_iff 1 (f:=fun n : ℕ => (n:ℝ)^(β-A-1))).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have hj : TendstoUniformly (fun N x => ∑ j ∈ Finset.range N, jumps j x) (fun x => ∑' j, jumps j x) atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact tendstoUniformlyOn_tsum_nat_eventually hs (hjump.mono (fun n hn x _ => hn x))
  have habel (n : ℕ) (x : ℝ) : weighted (n+1) x = back n x - ∑ j ∈ Finset.range n, jumps j x := by
    calc
      _ = ∑ j ∈ Finset.range (n+1), F j x • cyclic_CyclicMobius_μ₁ j := by
        simp only [weighted,F,Finset.mul_sum,smul_eq_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by simpa only [smul_eq_mul,Nat.add_sub_cancel,cyclic_CyclicMobius_M,back,jumps] using
                    Finset.sum_range_by_parts (fun j => F j x) cyclic_CyclicMobius_μ₁ (n+1)
  let S (x : ℝ) := 0-∑' j, jumps j x
  have hU : TendstoUniformly (fun n x => weighted (n+1) x) S atTop := by
    simp only [habel]
    exact hback.sub hj
  have heq (x : ℝ) : S x = (w x:ℂ)*target x := by
    exact tendsto_nhds_unique (hU.tendsto_at x)
      ((tendsto_const_nhds.mul (hlim x)).comp (tendsto_add_atTop_nat 1))
  intro ε hε
  obtain ⟨n,hn⟩ := (Metric.tendstoUniformly_iff.mp hU ε hε).exists
  refine ⟨n+1,fun x => ?_⟩
  have h := (hn x).le
  rw [dist_comm,dist_eq_norm,heq] at h
  simpa only [weighted,← mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw x)] using h

/-- A summatory Möbius exponent below the lower endpoint gives uniform weighted convergence
of the truncated inverse on every test with a weighted first-derivative bound. -/
theorem mobius_uniform_of_mertens {A B β : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hβ : β < A)
    (hM : (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℂ)) =O[atTop]
      fun n : ℕ => (n:ℝ)^β) {Θ target : ℝ → ℂ} (hd : Differentiable ℝ Θ)
    (hb : ∃ C : ℝ, ∀ x : ℝ, max (Real.exp (A*x)) (Real.exp (B*x))*(‖Θ x‖+‖deriv Θ x‖) ≤ C)
    (hlim : ∀ x, Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (ArithmeticFunction.moebius (j+1):ℂ)*
      Θ (x+Real.log ((j:ℝ)+1))) atTop (𝓝 (target x))) : ∀ ε>0, ∃ N : ℕ, ∀ x : ℝ,
      max (Real.exp (A*x)) (Real.exp (B*x))*
        ‖(∑ j ∈ Finset.range N, (ArithmeticFunction.moebius (j+1):ℂ)*Θ (x+Real.log ((j:ℝ)+1)))-target x‖ ≤ ε := by
  obtain ⟨C,hC⟩ := hb
  have h0 : 0 ≤ C := (mul_nonneg (endpointWeight_pos A B 0).le (add_nonneg (norm_nonneg _) (norm_nonneg _))).trans (hC 0)
  exact cyclic_CyclicMobius_uniform_abel hA hAB hβ h0 (by simpa only [funext cyclic_CyclicMobius_M_eq] using hM) hd hC hlim

/-- The RH Mertens theorem supplies the exponent on every closed substrip strictly to the
right of one half. -/
theorem mobius_uniform_of_rh (hRH : RiemannHypothesis) {A B : ℝ} (hA : 1/2 < A) (hAB : A ≤ B)
    {Θ target : ℝ → ℂ} (hd : Differentiable ℝ Θ)
    (hb : ∃ C : ℝ, ∀ x : ℝ, max (Real.exp (A*x)) (Real.exp (B*x))*(‖Θ x‖+‖deriv Θ x‖) ≤ C)
    (hlim : ∀ x, Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (ArithmeticFunction.moebius (j+1):ℂ)*
      Θ (x+Real.log ((j:ℝ)+1))) atTop (𝓝 (target x))) : ∀ ε>0, ∃ N : ℕ, ∀ x : ℝ,
      max (Real.exp (A*x)) (Real.exp (B*x))*
        ‖(∑ j ∈ Finset.range N, (ArithmeticFunction.moebius (j+1):ℂ)*Θ (x+Real.log ((j:ℝ)+1)))-target x‖ ≤ ε :=
  mobius_uniform_of_mertens (by linarith) hAB (β:=1/2+(A-1/2)/2) (by linarith)
    (moebius_summatory_rpow_bound_of_riemannHypothesis hRH _ (by linarith)) hd hb hlim

end
end MasulloRH.Cyclic

end StandaloneCyclicMobius

section StandaloneCyclicDyadSpan

open Filter Asymptotics Set
open scoped Topology
namespace MasulloCyclic
noncomputable section

private theorem cyclic_CyclicDyadSpan_target_mem_approx_of_mobius {A B : ℝ} (Θ f : F)
    (H : ∀ ε>0, ∃ N : ℕ, ∀ x : ℝ,
      w A B x * ‖(∑ j ∈ Finset.range N, (ArithmeticFunction.moebius (j+1):ℂ)*
        Θ (x+Real.log ((j:ℝ)+1)))-2*f x‖ ≤ ε) :
    f ∈ approx A B (translates Θ) := by
  let K := approx A B (translates Θ)
  have htwo : (2:ℂ) • f ∈ K := by
    apply mem_approx.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := H ε hε
    let v := ∑ j ∈ Finset.range N, (ArithmeticFunction.moebius (j+1):ℂ) • shift (Real.log ((j:ℝ)+1)) Θ
    have hv : v ∈ translates Θ := Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (shift_translate_mem Θ _))
    refine ⟨v,hv,fun x => ?_⟩
    simp only [v,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,shift]
    rw [norm_sub_rev]
    exact hN x
  have h := K.smul_mem (1/2:ℂ) htwo
  simpa only [smul_smul,one_div,inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul] using h

theorem target_mem_approx_of_mertens {A B β : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hβ : β<A)
    (hM : (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℂ)) =O[atTop]
      fun n : ℕ => (n:ℝ)^β) (Θ f : F) (hd : Differentiable ℝ Θ)
    (hb : ∃ C : ℝ, ∀ x, w A B x*(‖Θ x‖+‖deriv Θ x‖) ≤ C)
    (hlim : ∀ x, Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (ArithmeticFunction.moebius (j+1):ℂ)*
      Θ (x+Real.log ((j:ℝ)+1))) atTop (𝓝 (2*f x))) : f ∈ approx A B (translates Θ) :=
  cyclic_CyclicDyadSpan_target_mem_approx_of_mobius Θ f (MasulloRH.Cyclic.mobius_uniform_of_mertens hA hAB hβ hM hd hb hlim)

end
end MasulloCyclic

end StandaloneCyclicDyadSpan

section StandaloneCyclicDifference

open Filter Set
open scoped Topology
namespace MasulloCyclic
noncomputable section

theorem difference_inversion {A B : ℝ} (v f : F) (c : ℂ) (y M : ℝ)
    (hM : ∀ x, w A B x * ‖f x‖ ≤ M)
    (hcontract : ‖c‖ * max (Real.exp (-A*y)) (Real.exp (-B*y)) < 1)
    (hd : f - c • shift y f ∈ approx A B (translates v)) :
    f ∈ approx A B (translates v) := by
  let K := approx A B (translates v)
  let R := ‖c‖ * max (Real.exp (-A*y)) (Real.exp (-B*y))
  let S (n : ℕ) : F := c^n • shift ((n:ℝ)*y) f
  have hS (n : ℕ) (x : ℝ) : S n x = c^n * f (x+n*y) := rfl
  have hmember (n : ℕ) : f-S n ∈ K := by
    induction n with
    | zero =>
      have h0 : S 0 = f := by funext x; simp [hS]
      rw [h0,sub_self]; exact K.zero_mem
    | succ n ih =>
      have h := K.smul_mem (c^n) (shift_preserves_approx v ((n:ℝ)*y) hd)
      have eq : (f-S n) + c^n • shift ((n:ℝ)*y) (f - c • shift y f) = f-S (n+1) := by
        ext x
        change f x-S n x+c^n*(f (x+n*y)-c*f (x+n*y+y))=f x-S (n+1) x
        simp only [hS,Nat.cast_add,Nat.cast_one,pow_succ]
        rw [show x+(n+1:ℝ)*y=x+n*y+y by ring]
        ring
      exact eq ▸ K.add_mem ih h
  have hC : 0 ≤ max (Real.exp (-A*y)) (Real.exp (-B*y)) :=
    (Real.exp_nonneg _).trans (le_max_left _ _)
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) hC
  have hsmall (n : ℕ) (x : ℝ) : w A B x * ‖S n x‖ ≤ R^n * M := by
    induction n generalizing x with
    | zero => simpa [hS] using hM x
    | succ n ih =>
      have he : S (n+1) x = c*S n (x+y) := by
        simp only [hS,Nat.cast_add,Nat.cast_one,pow_succ]
        rw [show x+(n+1:ℝ)*y=x+y+n*y by ring]; ring
      rw [he,norm_mul]
      calc
        _ ≤ (max (Real.exp (-A*y)) (Real.exp (-B*y)) * w A B (x+y)) *
            (‖c‖ * ‖S n (x+y)‖) :=
          mul_le_mul_of_nonneg_right (w_shift _ _ _ _) (by positivity)
        _ = R * (w A B (x+y) * ‖S n (x+y)‖) := by dsimp [R]; ring
        _ ≤ R*(R^n*M) := mul_le_mul_of_nonneg_left (ih (x+y)) hR
        _ = R^(n+1)*M := by ring
  apply (approx_idem (translates v))
  intro ε hε
  have ht : Tendsto (fun n : ℕ => R^n * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hR hcontract).mul_const M
  obtain ⟨n,hn⟩ := (ht.eventually_lt_const hε).exists
  refine ⟨f-S n,hmember n,fun x => ?_⟩
  simpa using (hsmall n x).trans hn.le

def gaussian (x : ℝ) : ℂ := (Real.exp (-Real.pi * Real.exp (2*x)) : ℝ)
def firstDifference : F := gaussian - (2:ℂ) • shift (Real.log 2) gaussian
def dyadDifference : F := firstDifference - shift (Real.log 2) firstDifference

theorem gauss_weight {A B : ℝ} (hA : 0 ≤ A) (hAB : A≤B) (hB : B≤1) (x : ℝ) :
    w A B x * ‖gaussian x‖ ≤ 1 := by
  simp only [gaussian,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have aux (d : ℝ) (hd0 : 0≤d) (hd1 : d≤1) : Real.exp (d*x)*Real.exp (-Real.pi*Real.exp (2*x)) ≤ 1 := by
    rw [← Real.exp_add,Real.exp_le_one_iff]
    by_cases hx : 0 ≤ x
    · have hoe := Real.add_one_le_exp (2*x)
      have hπ := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_nonneg (2*x))
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hx]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hd0 (le_of_not_ge hx),mul_nonneg Real.pi_pos.le (Real.exp_nonneg (2*x))]
  rcases le_total (Real.exp (A*x)) (Real.exp (B*x)) with h|h
  · simpa only [w,max_eq_right h] using aux B (hA.trans hAB) hB
  · simpa only [w,max_eq_left h] using aux A hA (hAB.trans hB)

theorem gauss_from_dyad {A B : ℝ} (hA : 0<A) (hAB : A≤B) (hB : B<1) (v : F)
    (hv : dyadDifference ∈ approx A B (translates v)) : gaussian ∈ approx A B (translates v) := by
  let a := Real.log 2
  let K := approx A B (translates v)
  have ha : 0<a := Real.log_pos (by norm_num)
  have haexp : Real.exp a = 2 := Real.exp_log (by norm_num)
  have hpos : max (Real.exp (-A*a)) (Real.exp (-B*a)) < 1 := by
    apply max_lt <;> rw [Real.exp_lt_one_iff] <;> nlinarith [mul_pos hA ha,mul_pos (hA.trans_le hAB) ha]
  have hF (x : ℝ) : w A B x * ‖firstDifference x‖ ≤ 3 := by
    have hg := gauss_weight hA.le hAB hB.le
    have hw := mul_le_mul_of_nonneg_right (w_shift A B x a) (norm_nonneg (gaussian (x+a)))
    have hu := mul_le_mul_of_nonneg_right hpos.le (mul_nonneg (w_pos A B (x+a)).le (norm_nonneg (gaussian (x+a))))
    have h1 : w A B x*‖gaussian (x+a)‖ ≤ 1 := by nlinarith [hg (x+a)]
    change w A B x*‖gaussian x-(2:ℂ)*gaussian (x+a)‖ ≤ 3
    have h := mul_le_mul_of_nonneg_left (norm_sub_le (gaussian x) ((2:ℂ)*gaussian (x+a))) (w_pos A B x).le
    rw [norm_mul,show ‖(2:ℂ)‖=(2:ℝ) by norm_num] at h
    nlinarith [hg x]
  have hfirst : firstDifference ∈ K := difference_inversion v firstDifference 1 a 3 hF
    (by simpa using hpos) (by rw [one_smul]; exact hv)
  have hneg : ‖(1/2:ℂ)‖ * max (Real.exp (-A* -a)) (Real.exp (-B* -a)) < 1 := by
    have hh (z : ℝ) (hz : z<1) : Real.exp (-z* -a) < 2 := by
      rw [←haexp]; apply Real.exp_lt_exp.mpr; nlinarith [mul_pos (sub_pos.mpr hz) ha]
    have hmax := max_lt (hh A (hAB.trans_lt hB)) (hh B hB)
    rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num]
    linarith
  apply difference_inversion v gaussian (1/2) (-a) 1 (gauss_weight hA.le hAB hB.le) hneg
  have h := K.smul_mem (-(1/2):ℂ) (shift_preserves_approx v (-a) hfirst)
  convert h using 1
  ext x
  change gaussian x-(1/2:ℂ)*gaussian (x + -a) = -(1/2:ℂ)*(gaussian (x+ -a)-2*gaussian (x+ -a+a))
  rw [neg_add_cancel_right]
  ring

end
end MasulloCyclic

end StandaloneCyclicDifference

section StandaloneThetaGeneralBounds

open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH
noncomputable section

private lemma cyclic_ThetaGeneralBounds_absInt_scale (f : ℝ → ℂ) (s : ℂ) (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f (a*x)‖ =
      a^(-s.re) * ∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f x‖ := by
  let F (u : ℝ) := ‖(u:ℂ)^(s-1) • f u‖
  have hpow : (a^(s.re-1))⁻¹ * a⁻¹ = a^(-s.re) := by
    rw [← Real.rpow_neg ha.le, ← Real.rpow_neg_one, ← Real.rpow_add ha]
    congr 1; ring
  calc
    _ = ∫ x : ℝ in Ioi 0, (a^(s.re-1))⁻¹ * F (a*x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      simp only [F, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
        Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha hx), Complex.sub_re, Complex.one_re, Real.mul_rpow ha.le hx.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos ha (s.re-1))]
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi F 0 ha, mul_zero, smul_eq_mul, ← mul_assoc, hpow]

/-- The Mellin transform of the positive integral dilates of an arbitrary test function,
in the half-plane of absolute Dirichlet convergence. -/
lemma mellin_pos_dilates (f : ℝ → ℂ) (s : ℂ) (hs : 1 < s.re) (hf : MellinConvergent f s) :
    mellin (fun x : ℝ => ∑' n : ℕ, f (((n:ℝ)+1)*x)) s = riemannZeta s * mellin f s := by
  let F (n : ℕ) (x : ℝ) : ℂ := (x:ℂ)^(s-1) • f (((n:ℝ)+1)*x)
  have hInt (n : ℕ) : Integrable (F n) (volume.restrict (Ioi 0)) :=
    (MellinConvergent.comp_mul_left (f:=f) (s:=s) (a:=(n:ℝ)+1) (by positivity)).mpr hf
  have hSum : Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0, ‖F n x‖) := by
    have h₀ : Summable (fun n : ℕ => ((n:ℝ)+1)^(-s.re)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    apply (h₀.mul_right (∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f x‖)).congr
    intro n
    exact (cyclic_ThetaGeneralBounds_absInt_scale f s ((n:ℝ)+1) (by positivity)).symm
  have he := hasSum_integral_of_summable_integral_norm hInt hSum
  calc
    _ = ∫ x : ℝ in Ioi 0, ∑' n, F n x := by simp [mellin,F,tsum_mul_left,smul_eq_mul]
    _ = ∑' n, ∫ x : ℝ in Ioi 0, F n x := he.tsum_eq.symm
    _ = ∑' n : ℕ, (1/((n:ℂ)+1)^s)*mellin f s := by
      apply tsum_congr
      intro n
      change mellin (fun x => f (((n:ℝ)+1)*x)) s = _
      rw [mellin_comp_mul_left f s (by positivity : (0:ℝ)<n+1)]
      simp [Complex.cpow_neg,smul_eq_mul]
    _ = _ := by rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

private def cyclic_ThetaGeneralBounds_latticeWeight (k : ℕ) (n : ℕ) : ℝ := (((n:ℝ)+1)^k)⁻¹

private lemma cyclic_ThetaGeneralBounds_summable_latticeWeight (k : ℕ) (hk : 1 < k) : Summable (cyclic_ThetaGeneralBounds_latticeWeight k) := by
  have h : -((k:ℕ):ℝ) < -1 := by exact_mod_cast (show -((k:ℕ):ℤ) < -1 by omega)
  have hz := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr h)
  apply hz.congr
  intro n
  dsimp [cyclic_ThetaGeneralBounds_latticeWeight]
  rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity), Real.rpow_natCast]

def thetaNat (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℕ, f (((n:ℝ)+1)*x)

private lemma cyclic_ThetaGeneralBounds_thetaTerm_bound (f : 𝓢(ℝ,ℂ)) (k n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖f (((n:ℝ)+1)*x)‖ ≤ ((SchwartzMap.seminorm ℝ k 0) f) * (x^k)⁻¹ * cyclic_ThetaGeneralBounds_latticeWeight k n := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k (((n:ℝ)+1)*x)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hn hx), mul_pow] at h
  rw [cyclic_ThetaGeneralBounds_latticeWeight, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hn _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx _)]
  nlinarith only [h]

private lemma cyclic_ThetaGeneralBounds_thetaNat_summable (f : 𝓢(ℝ,ℂ)) (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => f (((n:ℝ)+1)*x)) :=
  ((cyclic_ThetaGeneralBounds_summable_latticeWeight 2 (by norm_num)).mul_left _).of_norm_bounded (fun n => cyclic_ThetaGeneralBounds_thetaTerm_bound f 2 n hx)

private lemma cyclic_ThetaGeneralBounds_thetaNat_bound (f : 𝓢(ℝ,ℂ)) (k : ℕ) (hk : 1 < k) {x : ℝ} (hx : 0 < x) :
    ‖thetaNat f x‖ ≤ (((SchwartzMap.seminorm ℝ k 0) f) * ∑' n, cyclic_ThetaGeneralBounds_latticeWeight k n) * (x^k)⁻¹ := by
  apply (norm_tsum_le_tsum_norm ((cyclic_ThetaGeneralBounds_thetaNat_summable f x hx).norm)).trans
  apply (Summable.tsum_le_tsum (fun n => cyclic_ThetaGeneralBounds_thetaTerm_bound f k n hx) (cyclic_ThetaGeneralBounds_thetaNat_summable f x hx).norm
    ((cyclic_ThetaGeneralBounds_summable_latticeWeight k hk).mul_left _)).trans_eq
  rw [tsum_mul_left]; ring

lemma thetaNat_continuousOn (f : 𝓢(ℝ,ℂ)) : ContinuousOn (thetaNat f) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  have hu : Summable (fun n : ℕ => (SchwartzMap.seminorm ℝ 2 0 f) * ((x/2)^2)⁻¹ * cyclic_ThetaGeneralBounds_latticeWeight 2 n) :=
    (cyclic_ThetaGeneralBounds_summable_latticeWeight 2 (by norm_num)).mul_left _
  have hc : ContinuousOn (thetaNat f) (Ioi (x/2)) := by
    apply continuousOn_tsum (fun n => (f.continuous.comp (continuous_const.mul continuous_id)).continuousOn) hu
    intro n y hy
    have hx' : 0 < x/2 := by positivity
    have hy' : x/2 < y := hy
    apply (cyclic_ThetaGeneralBounds_thetaTerm_bound f 2 n (lt_trans hx' hy')).trans
    gcongr
    dsimp [cyclic_ThetaGeneralBounds_latticeWeight]; positivity
  exact ((hc.continuousAt (isOpen_Ioi.mem_nhds (show x/2 < x by linarith)))).continuousWithinAt

def reflectS (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

def theta (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℤ, f ((n:ℝ)*x)

lemma theta_split (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    theta f x = thetaNat (f + reflectS f) x := by
  have h₁ := cyclic_ThetaGeneralBounds_thetaNat_summable f x hx
  have h₂ := cyclic_ThetaGeneralBounds_thetaNat_summable (reflectS f) x hx
  have hpos : Summable (fun n : ℕ => f ((((n:ℤ)+1 : ℤ) : ℝ)*x)) := by simpa using h₁
  have hneg : Summable (fun n : ℕ => f (((-((n:ℤ)+1) : ℤ) : ℝ)*x)) := by
    apply h₂.congr
    intro n
    change f (-(((n:ℝ)+1)*x)) = _
    push_cast; congr 1; ring
  have hsum := tsum_of_add_one_of_neg_add_one (f:=fun n : ℤ => f ((n:ℝ)*x)) hpos hneg
  change (∑' n : ℤ, f ((n:ℝ)*x)) = _
  rw [hsum]
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero, zero_mul, hf, add_zero]
  change _ = ∑' n : ℕ, (f (((n:ℝ)+1)*x) + f (-(((n:ℝ)+1)*x)))
  rw [h₁.tsum_add (g:=fun n : ℕ => f (-(((n:ℝ)+1)*x))) h₂]
  simp only [neg_mul]

/-- Uniform positive-scale decay of the Schwartz lattice sum in every integral order above one. -/
theorem thetaSchwartz_bound (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * (x^k)⁻¹ := by
  refine ⟨(SchwartzMap.seminorm ℝ k 0) (f+reflectS f) * ∑' n, cyclic_ThetaGeneralBounds_latticeWeight k n, ?_, ?_⟩
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro n; dsimp [cyclic_ThetaGeneralBounds_latticeWeight]; positivity
  · intro x hx
    change ‖theta f x‖ ≤ _
    rw [theta_split f hf hx]
    exact cyclic_ThetaGeneralBounds_thetaNat_bound _ k hk hx

end
end MasulloRH

end StandaloneThetaGeneralBounds

section StandaloneThetaPoisson

open MeasureTheory Filter Set FourierTransform
open scoped SchwartzMap FourierTransform Topology
set_option autoImplicit false
namespace MasulloSynthesis
noncomputable section

theorem theta_poisson_scaled (f : 𝓢(ℝ,ℂ)) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, f ((n:ℝ)*a)) =
    (a⁻¹:ℝ) • ∑' n : ℤ, (𝓕 f) ((n:ℝ)*a⁻¹) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (x : ℝ) : g x = f (a*x) := rfl
  have hscale (ξ : ℝ) : (𝓕 g) ξ = (a⁻¹:ℝ) • (𝓕 f) (ξ*a⁻¹) := by
    change 𝓕 (⇑g) ξ = (a⁻¹:ℝ) • 𝓕 (⇑f) (ξ*a⁻¹)
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
    let F (x : ℝ) := Complex.exp (↑(-2*Real.pi*x*(ξ*a⁻¹)) * Complex.I) • f x
    calc
      _ = ∫ x : ℝ, F (a*x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [F]
          rw [hg]
          congr 3
          field_simp
      _ = _ := by
        have h := Measure.integral_comp_mul_left F a
        simpa only [abs_of_pos (inv_pos.mpr ha)] using h
  have h := g.tsum_eq_tsum_fourier 0
  simp only [zero_add, hg, hscale, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at h
  rw [← tsum_const_smul'']
  simpa [mul_comm a] using h
theorem theta_poisson_near_zero (f : 𝓢(ℝ,ℂ)) (hI : (∫ x : ℝ, f x) = 0) :
    (fun x : ℝ => ∑' n : ℤ, f ((n:ℝ)*x)) =O[𝓝[>] (0:ℝ)] (fun _ : ℝ => (1:ℝ)) := by
  have hF0 : (𝓕 f : 𝓢(ℝ,ℂ)) 0 = 0 := by
    change 𝓕 (⇑f) 0 = 0
    simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  obtain ⟨C,hC,hbound⟩ := MasulloRH.thetaSchwartz_bound (𝓕 f) hF0 2 (by decide)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with x hx hx1
  have hpos : 0 < x := hx
  have hxle : x ≤ 1 := le_of_lt hx1
  change ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * ‖(1:ℝ)‖
  rw [theta_poisson_scaled f hpos, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hpos).le]
  simp only [norm_one, mul_one]
  calc
    _ ≤ x⁻¹ * (C * ((x⁻¹)^2)⁻¹) := mul_le_mul_of_nonneg_left (hbound _ (inv_pos.mpr hpos)) (inv_pos.mpr hpos).le
    _ = C * x := by field_simp
    _ ≤ C := mul_le_of_le_one_right hC hxle
end
end MasulloSynthesis

end StandaloneThetaPoisson

section StandaloneCyclicThetaBounds

open Set Filter MeasureTheory FourierTransform
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH
noncomputable section
private def cyclic_CyclicThetaBounds_latticeWeight (k : ℕ) (n : ℕ) : ℝ := (((n:ℝ)+1)^k)⁻¹

private lemma cyclic_CyclicThetaBounds_summable_latticeWeight (k : ℕ) (hk : 1 < k) : Summable (cyclic_CyclicThetaBounds_latticeWeight k) := by
  have h : -((k:ℕ):ℝ) < -1 := by exact_mod_cast (show -((k:ℕ):ℤ) < -1 by omega)
  have hz := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr h)
  apply hz.congr
  intro n
  dsimp [cyclic_CyclicThetaBounds_latticeWeight]
  rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity), Real.rpow_natCast]

private lemma cyclic_CyclicThetaBounds_thetaTerm_bound (f : 𝓢(ℝ,ℂ)) (k n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖f (((n:ℝ)+1)*x)‖ ≤ ((SchwartzMap.seminorm ℝ k 0) f) * (x^k)⁻¹ * cyclic_CyclicThetaBounds_latticeWeight k n := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k (((n:ℝ)+1)*x)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hn hx), mul_pow] at h
  rw [cyclic_CyclicThetaBounds_latticeWeight, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hn _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx _)]
  nlinarith only [h]

private lemma cyclic_CyclicThetaBounds_thetaNat_summable (f : 𝓢(ℝ,ℂ)) (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => f (((n:ℝ)+1)*x)) :=
  ((cyclic_CyclicThetaBounds_summable_latticeWeight 2 (by norm_num)).mul_left _).of_norm_bounded (fun n => cyclic_CyclicThetaBounds_thetaTerm_bound f 2 n hx)


end
end MasulloRH
open Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform ContDiff
namespace MasulloRH
noncomputable section

private def cyclic_CyclicThetaBounds_logEuler (g : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (1 / 2 : ℂ) • g + SchwartzMap.smulLeftCLM ℂ Complex.ofReal (SchwartzMap.derivCLM ℂ ℂ g)

private lemma cyclic_CyclicThetaBounds_logEuler_apply (g : 𝓢(ℝ,ℂ)) (t : ℝ) :
    cyclic_CyclicThetaBounds_logEuler g t = (1/2:ℂ) * g t + (t:ℂ) * deriv g t := by
  simp [cyclic_CyclicThetaBounds_logEuler, SchwartzMap.smulLeftCLM_apply_apply (show Function.HasTemperateGrowth Complex.ofReal from Complex.ofRealCLM.hasTemperateGrowth), smul_eq_mul]

private def cyclic_CyclicThetaBounds_logTerm (g : 𝓢(ℝ,ℂ)) (n : ℕ) (x : ℝ) : ℂ :=
  (Real.exp (x/2) : ℂ) * g (((n:ℝ)+1)*Real.exp x)

private def cyclic_CyclicThetaBounds_logNat (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ := ∑' n : ℕ, cyclic_CyclicThetaBounds_logTerm g n x

private lemma cyclic_CyclicThetaBounds_logTerm_deriv (g : 𝓢(ℝ,ℂ)) (n : ℕ) (x : ℝ) :
    HasDerivAt (cyclic_CyclicThetaBounds_logTerm g n) (cyclic_CyclicThetaBounds_logTerm (cyclic_CyclicThetaBounds_logEuler g) n x) x := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (u/2)) (Real.exp (x/2)/2) x := by
    convert (Real.hasDerivAt_exp (x/2)).comp x ((hasDerivAt_id x).div_const 2) using 1 <;> try rfl
    all_goals ring
  have hc : HasDerivAt (fun u : ℝ => ((n:ℝ)+1)*Real.exp u) (((n:ℝ)+1)*Real.exp x) x :=
    (Real.hasDerivAt_exp x).const_mul _
  have h := he.ofReal_comp.mul ((g.hasDerivAt _).scomp x hc)
  convert h using 1 <;> try rfl
  all_goals try simp [cyclic_CyclicThetaBounds_logTerm, cyclic_CyclicThetaBounds_logEuler_apply, Complex.real_smul]
  all_goals ring

private lemma cyclic_CyclicThetaBounds_logTerm_summable (g : 𝓢(ℝ,ℂ)) (x : ℝ) : Summable (fun n => cyclic_CyclicThetaBounds_logTerm g n x) :=
  (cyclic_CyclicThetaBounds_thetaNat_summable g _ (Real.exp_pos x)).mul_left _

private lemma cyclic_CyclicThetaBounds_logTerm_bound (g : 𝓢(ℝ,ℂ)) (n : ℕ) (x : ℝ) :
    ‖cyclic_CyclicThetaBounds_logTerm g n x‖ ≤ (SchwartzMap.seminorm ℝ 2 0 g) * Real.exp (-3*x/2) * cyclic_CyclicThetaBounds_latticeWeight 2 n := by
  have h := cyclic_CyclicThetaBounds_thetaTerm_bound g 2 n (Real.exp_pos x)
  rw [cyclic_CyclicThetaBounds_logTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  calc
    _ = (SchwartzMap.seminorm ℝ 2 0 g) * (Real.exp (x/2) * Real.exp (-(2*x))) * cyclic_CyclicThetaBounds_latticeWeight 2 n := by norm_num; ring
    _ = _ := by rw [← Real.exp_add]; congr 3; ring

private lemma cyclic_CyclicThetaBounds_logNat_deriv (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    HasDerivAt (cyclic_CyclicThetaBounds_logNat g) (cyclic_CyclicThetaBounds_logNat (cyclic_CyclicThetaBounds_logEuler g) x) x := by
  let C := (SchwartzMap.seminorm ℝ 2 0 (cyclic_CyclicThetaBounds_logEuler g)) * Real.exp (-3*(x-1)/2)
  have hsum : Summable (fun n => C * cyclic_CyclicThetaBounds_latticeWeight 2 n) :=
    (cyclic_CyclicThetaBounds_summable_latticeWeight 2 (by decide)).mul_left _
  apply hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioi (isPreconnected_Ioi (a:=x-1))
    (fun n y _ => cyclic_CyclicThetaBounds_logTerm_deriv g n y) ?_ (y₀:=x) (show x ∈ Ioi (x-1) by simp) (cyclic_CyclicThetaBounds_logTerm_summable g x)
    (show x ∈ Ioi (x-1) by simp)
  intro n y hy
  have hxy : x-1 < y := hy
  apply (cyclic_CyclicThetaBounds_logTerm_bound _ n y).trans
  dsimp only [C]
  have hE : Real.exp (-3*y/2) ≤ Real.exp (-3*(x-1)/2) := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) (by dsimp [cyclic_CyclicThetaBounds_latticeWeight]; positivity)

private def cyclic_CyclicThetaBounds_logEulerIter : ℕ → 𝓢(ℝ,ℂ) → 𝓢(ℝ,ℂ)
  | 0, g => g
  | n+1, g => cyclic_CyclicThetaBounds_logEuler (cyclic_CyclicThetaBounds_logEulerIter n g)

private lemma cyclic_CyclicThetaBounds_logNat_iterated (g : 𝓢(ℝ,ℂ)) (n : ℕ) :
    iteratedDeriv n (cyclic_CyclicThetaBounds_logNat g) = cyclic_CyclicThetaBounds_logNat (cyclic_CyclicThetaBounds_logEulerIter n g) := by
  induction n with
  | zero => simp [cyclic_CyclicThetaBounds_logEulerIter]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun x => (cyclic_CyclicThetaBounds_logNat_deriv _ x).deriv

private lemma cyclic_CyclicThetaBounds_logNat_smooth (g : 𝓢(ℝ,ℂ)) : ContDiff ℝ ∞ (cyclic_CyclicThetaBounds_logNat g) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [cyclic_CyclicThetaBounds_logNat_iterated]
  exact fun x => (cyclic_CyclicThetaBounds_logNat_deriv _ x).differentiableAt

private lemma cyclic_CyclicThetaBounds_logNat_bound (g : 𝓢(ℝ,ℂ)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
    ‖cyclic_CyclicThetaBounds_logNat g x‖ ≤ C * Real.exp (-3*x/2) := by
  let C := SchwartzMap.seminorm ℝ 2 0 g * ∑' n, cyclic_CyclicThetaBounds_latticeWeight 2 n
  have h : 0 ≤ ∑' n, cyclic_CyclicThetaBounds_latticeWeight 2 n := tsum_nonneg (fun n => by dsimp [cyclic_CyclicThetaBounds_latticeWeight]; positivity)
  refine ⟨C, mul_nonneg (by positivity) h, fun x => ?_⟩
  apply (norm_tsum_le_tsum_norm (cyclic_CyclicThetaBounds_logTerm_summable g x).norm).trans
  apply (Summable.tsum_le_tsum (fun n => cyclic_CyclicThetaBounds_logTerm_bound g n x) (cyclic_CyclicThetaBounds_logTerm_summable g x).norm
    ((cyclic_CyclicThetaBounds_summable_latticeWeight 2 (by decide)).mul_left _)).trans_eq
  rw [tsum_mul_left]
  dsimp only [C]
  ring

private def cyclic_CyclicThetaBounds_thetaLogFun (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ := (Real.exp (x/2):ℂ) * theta g (Real.exp x)

private lemma cyclic_CyclicThetaBounds_thetaLog_split (g : 𝓢(ℝ,ℂ)) (hg : g 0=0) :
    cyclic_CyclicThetaBounds_thetaLogFun g = cyclic_CyclicThetaBounds_logNat (g + reflectS g) := by
  funext x
  rw [cyclic_CyclicThetaBounds_thetaLogFun, theta_split g hg (Real.exp_pos x), cyclic_CyclicThetaBounds_logNat]
  simp [cyclic_CyclicThetaBounds_logTerm,thetaNat,tsum_mul_left]

private lemma cyclic_CyclicThetaBounds_thetaLog_recip (g : 𝓢(ℝ,ℂ)) :
    cyclic_CyclicThetaBounds_thetaLogFun g = fun x => cyclic_CyclicThetaBounds_thetaLogFun (𝓕 g) (-x) := by
  funext x
  simp only [cyclic_CyclicThetaBounds_thetaLogFun, theta, MasulloSynthesis.theta_poisson_scaled g (Real.exp_pos x), Real.exp_neg,
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

private lemma cyclic_CyclicThetaBounds_center_order_bound (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hI : (∫ t : ℝ, g t)=0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖iteratedDeriv n (cyclic_CyclicThetaBounds_thetaLogFun g) x‖ ≤ C*Real.exp (-3*|x|/2) := by
  obtain ⟨C,hC,h⟩ := cyclic_CyclicThetaBounds_logNat_bound (cyclic_CyclicThetaBounds_logEulerIter n (g+reflectS g))
  obtain ⟨D,hD,h'⟩ := cyclic_CyclicThetaBounds_logNat_bound (cyclic_CyclicThetaBounds_logEulerIter n (𝓕 g+reflectS (𝓕 g)))
  have hF : (𝓕 g : 𝓢(ℝ,ℂ)) 0=0 := by
    change 𝓕 (⇑g) 0=0; simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  refine ⟨max C D,le_max_of_le_left hC,fun x => ?_⟩
  by_cases hx : 0 ≤ x
  · rw [cyclic_CyclicThetaBounds_thetaLog_split g h0, cyclic_CyclicThetaBounds_logNat_iterated, abs_of_nonneg hx]
    exact (h x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  · rw [cyclic_CyclicThetaBounds_thetaLog_recip g, cyclic_CyclicThetaBounds_thetaLog_split (𝓕 g) hF, iteratedDeriv_comp_neg]
    simp only [norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul,abs_of_neg (lt_of_not_ge hx),cyclic_CyclicThetaBounds_logNat_iterated]
    exact (h' (-x)).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))

private lemma cyclic_CyclicThetaBounds_abs_weight (A B x : ℝ) (hA : 0<A) (hAB : A≤B) (hB : B<1) :
    max (Real.exp (A*x)) (Real.exp (B*x)) * Real.exp (-x/2) * Real.exp (-3*|x|/2) ≤ 1 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAB hx)),abs_of_nonneg hx,
      ← Real.exp_add,← Real.exp_add,Real.exp_le_one_iff]
    nlinarith [mul_le_mul_of_nonneg_right hB.le hx]
  · have hn := le_of_lt (lt_of_not_ge hx)
    rw [max_eq_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hAB hn)),abs_of_nonpos hn,
      ← Real.exp_add,← Real.exp_add,Real.exp_le_one_iff]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hA.le hn]

private lemma cyclic_CyclicThetaBounds_thetaPhysical_estimates (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hI : (∫ t : ℝ, g t)=0) :
    let F (x : ℝ) := theta g (Real.exp x)
    Differentiable ℝ F ∧ ∀ {A B : ℝ}, 0<A → A≤B → B<1 → ∃ C : ℝ, 0<C ∧ ∀ x : ℝ,
      max (Real.exp (A*x)) (Real.exp (B*x)) * ‖F x‖ ≤ C ∧
      max (Real.exp (A*x)) (Real.exp (B*x)) * ‖deriv F x‖ ≤ C := by
  let V := cyclic_CyclicThetaBounds_thetaLogFun g
  have hV : Differentiable ℝ V := by
    dsimp only [V]; rw [cyclic_CyclicThetaBounds_thetaLog_split g h0]; exact fun x => (cyclic_CyclicThetaBounds_logNat_deriv _ x).differentiableAt
  let E (x:ℝ) : ℂ := Real.exp (-x/2)
  have hE (x:ℝ) : HasDerivAt E (-(1/2:ℂ)*E x) x := by
    have hl : HasDerivAt (fun t:ℝ => -t/2) (-(1/2:ℝ)) x := by simpa only [neg_div] using (hasDerivAt_neg x).div_const 2
    convert ((Real.hasDerivAt_exp (-x/2)).comp x hl).ofReal_comp using 1 <;> try rfl
    dsimp [E]; push_cast; ring
  have hF : (fun x : ℝ => theta g (Real.exp x)) = fun x => E x * V x := by
    funext x; dsimp [E,V,cyclic_CyclicThetaBounds_thetaLogFun]; rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
    rw [show -x/2+x/2=0 by ring,Real.exp_zero,Complex.ofReal_one,one_mul]
  dsimp only
  rw [hF]
  have hd (x:ℝ) := (hE x).mul (hV x).hasDerivAt
  refine ⟨fun x => (hd x).differentiableAt, fun {A B} hA hAB hB => ?_⟩
  obtain ⟨C,hC,h₀⟩ := cyclic_CyclicThetaBounds_center_order_bound g h0 hI 0
  obtain ⟨D,hD,h₁⟩ := cyclic_CyclicThetaBounds_center_order_bound g h0 hI 1
  have h₀' (x:ℝ) : ‖V x‖ ≤ C*Real.exp (-3*|x|/2) := by simpa only [V,iteratedDeriv_zero] using h₀ x
  have h₁' (x:ℝ) : ‖deriv V x‖ ≤ D*Real.exp (-3*|x|/2) := by simpa only [V,iteratedDeriv_one] using h₁ x
  refine ⟨C+D+1,by linarith,fun x => ?_⟩
  let W := max (Real.exp (A*x)) (Real.exp (B*x))
  have hW : 0≤W := le_max_of_le_left (Real.exp_nonneg _)
  have hNorm : ‖E x‖ = Real.exp (-x/2) := Complex.norm_real _ |>.trans (Real.norm_of_nonneg (Real.exp_nonneg _))
  have hfactor := cyclic_CyclicThetaBounds_abs_weight A B x hA hAB hB
  rw [show theta g (Real.exp x) = E x * V x from congrFun hF x]
  change W*‖E x*V x‖ ≤ _ ∧ W*‖deriv _ x‖ ≤ _
  have hbase {v:ℝ} {c:ℝ} (hc:0≤c) (hv:v≤c*Real.exp (-3*|x|/2)) : W*(Real.exp (-x/2)*v) ≤ c := by
    calc
      _ ≤ W*(Real.exp (-x/2)*(c*Real.exp (-3*|x|/2))) := by gcongr
      _ = c*(W*Real.exp (-x/2)*Real.exp (-3*|x|/2)) := by ring
      _ ≤ c*1 := mul_le_mul_of_nonneg_left hfactor hc
      _ = c := mul_one _
  constructor
  · rw [norm_mul,hNorm]; exact (hbase hC (h₀' x)).trans (by linarith)
  · change W * ‖deriv (E*V) x‖ ≤ _
    rw [(hd x).deriv]
    apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) hW).trans
    simp only [norm_mul,norm_neg,hNorm,norm_div,norm_one,Complex.norm_ofNat]
    have t₀ := hbase hC (h₀' x)
    have t₁ := hbase hD (h₁' x)
    nlinarith [mul_nonneg hW (mul_nonneg (Real.exp_nonneg (-x/2)) (norm_nonneg (V x)))]

end
end MasulloRH

namespace MasulloCyclic
open MasulloRH.GaussianApproximation
open scoped SchwartzMap

theorem theta_physical_bounds : Differentiable ℝ theta ∧ ∀ {A B : ℝ}, 0<A → A≤B → B<1 → ∃ C : ℝ,
    0<C ∧ ∀ x : ℝ, max (Real.exp (A*x)) (Real.exp (B*x))*‖theta x‖≤ C ∧
      max (Real.exp (A*x)) (Real.exp (B*x))*‖deriv theta x‖≤ C := by
  obtain ⟨g,hg,h0,hI,_,_⟩ := MasulloRH.dyadic_gaussian_theta_mellin
  have he : theta = fun x => MasulloRH.theta g (Real.exp x) := by
    funext x; unfold theta MasulloRH.theta; simp_rw [hg]
  rw [he]; exact MasulloRH.cyclic_CyclicThetaBounds_thetaPhysical_estimates g h0 hI

theorem theta_differentiable : Differentiable ℝ theta := theta_physical_bounds.1

theorem theta_weighted_bounds {A B : ℝ} (hA : 0<A) (hAB : A≤B) (hB : B<1) :
    ∃ C : ℝ, ∀ x : ℝ, max (Real.exp (A*x)) (Real.exp (B*x)) * (‖theta x‖ + ‖deriv theta x‖) ≤ C := by
  obtain ⟨C,_,h⟩ := theta_physical_bounds.2 hA hAB hB
  exact ⟨C+C,fun x => by rw [mul_add]; exact add_le_add (h x).1 (h x).2⟩

end MasulloCyclic

end StandaloneCyclicThetaBounds

section StandaloneCyclicThetaMobius

open ArithmeticFunction MeasureTheory Set Filter
open scoped Topology SchwartzMap
noncomputable section
namespace MasulloCyclic

/-- A Gaussian in the positive norm coordinate, as a function of its logarithm. -/
def G (x : ℝ) : ℂ := (Real.exp (-Real.pi * (Real.exp x)^2): ℝ)
/-- The dyadic test before summing over the rational lattice. -/
def generator (x : ℝ) : ℂ := G x - 3*G (x+Real.log 2) + 2*G (x+2*Real.log 2)

private lemma cyclic_CyclicThetaMobius_divisor_mu (k : ℕ) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℂ)) = if k=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f k) ArithmeticFunction.moebius_mul_coe_zeta
  change ((ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) k) = _ at h
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  push_cast [← Int.cast_sum]; split_ifs at * <;> exact_mod_cast h

private lemma cyclic_CyclicThetaMobius_inversion {b : ℕ → ℂ}
    (h : Summable (fun p : ℕ+ × ℕ+ => (ArithmeticFunction.moebius p.1 : ℂ) * b (p.1.val*p.2.val))) :
    HasSum (fun n : ℕ+ => (ArithmeticFunction.moebius n : ℂ)* ∑' m : ℕ+, b (n.val*m.val)) (b 1) := by
  classical
  let F (p : ℕ+ × ℕ+) := (ArithmeticFunction.moebius p.1 : ℂ)*b (p.1.val*p.2.val)
  have hs : Summable (fun p => F (sigmaAntidiagonalEquivProd p)) := sigmaAntidiagonalEquivProd.summable_iff.mpr h
  have he (n : ℕ+) : (∑' d : (n:ℕ).divisorsAntidiagonal,
      F (sigmaAntidiagonalEquivProd ⟨n,d⟩)) = if n=1 then b 1 else 0 := by
    rw [tsum_fintype]
    have hf (d : (n:ℕ).divisorsAntidiagonal) : F (sigmaAntidiagonalEquivProd ⟨n,d⟩) =
        (ArithmeticFunction.moebius d.val.1 : ℂ)*b n := by
      change (ArithmeticFunction.moebius d.val.1 : ℂ)*b (d.val.1*d.val.2) = _
      rw [(Nat.mem_divisorsAntidiagonal.mp d.property).1]
    simp_rw [hf]
    rw [← Finset.sum_mul,Finset.univ_eq_attach,Finset.sum_attach (f:=fun p : ℕ×ℕ => (ArithmeticFunction.moebius p.1 : ℂ)),
      Nat.sum_divisorsAntidiagonal (fun i _ => (ArithmeticFunction.moebius i:ℂ)),cyclic_CyclicThetaMobius_divisor_mu]
    by_cases hn : n=1
    · simp [hn]
    · have hnn : (n:ℕ)≠1 := fun hh => hn (Subtype.ext hh)
      simp [hn,hnn]
  have htotal : (∑' p : ℕ+ × ℕ+, F p) = b 1 := by
    rw [← sigmaAntidiagonalEquivProd.tsum_eq F, hs.tsum_sigma]; simp_rw [he]; simp
  have ht := h.prod.hasSum
  rw [← h.tsum_prod, show (∑' p : ℕ+ × ℕ+, (ArithmeticFunction.moebius p.1:ℂ)*b (p.1.val*p.2.val)) = b 1 from htotal] at ht
  simpa only [tsum_mul_left] using ht

private def cyclic_CyclicThetaMobius_dyad (t : ℝ) : ℂ :=
 ((Real.exp (-Real.pi*t^2)-3*Real.exp (-Real.pi*(2*t)^2)+2*Real.exp (-Real.pi*(4*t)^2):ℝ):ℂ)

private lemma cyclic_CyclicThetaMobius_generator_eq (x : ℝ) : generator x = cyclic_CyclicThetaMobius_dyad (Real.exp x) := by
  have he : Real.exp (2*Real.log 2) = 4 := by rw [two_mul,Real.exp_add,Real.exp_log (by norm_num : 0<(2:ℝ))]; norm_num
  simp only [generator,G,cyclic_CyclicThetaMobius_dyad,Real.exp_add,he,Real.exp_log (by norm_num : 0<(2:ℝ)), Complex.ofReal_add,
    Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat]; ring_nf

private lemma cyclic_CyclicThetaMobius_dyad_decay (g : 𝓢(ℝ,ℂ)) (hg : ∀ x, g x=cyclic_CyclicThetaMobius_dyad x) (x : ℝ) :
    Summable (fun p : ℕ+ × ℕ+ => (ArithmeticFunction.moebius p.1:ℂ) * cyclic_CyclicThetaMobius_dyad ((((p.1:ℕ)*(p.2:ℕ):ℕ):ℝ)*Real.exp x)) := by
  let v (n : ℕ+) := (((n:ℕ):ℝ)^2)⁻¹
  have hV : Summable v := by
    apply (summable_pnat_iff_summable_nat (f:=fun n : ℕ => ((n:ℝ)^2)⁻¹)).mpr
    have hz : Summable (fun n : ℕ => (n:ℝ)^(-(2:ℝ))) := Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two] using hz
  have hprod := summable_mul_of_summable_norm (f:=v) (g:=v) hV.norm hV.norm
  let C := (SchwartzMap.seminorm ℝ 2 0 g) * ((Real.exp x)^2)⁻¹
  apply ((hprod.mul_left C)).of_norm_bounded
  rintro ⟨n,m⟩
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=(n:ℕ))
  have hn : 0<((n:ℕ):ℝ) := by exact_mod_cast n.property
  have hm : 0<((m:ℕ):ℝ) := by exact_mod_cast m.property
  have hbd := SchwartzMap.norm_pow_mul_le_seminorm ℝ g 2 ((((n:ℕ)*(m:ℕ):ℕ):ℝ)*Real.exp x)
  rw [Real.norm_eq_abs,abs_of_pos (by positivity),hg] at hbd
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hmu).trans
  simp only [Nat.cast_mul] at hbd ⊢
  dsimp [C,v]; field_simp [hn.ne',hm.ne',Real.exp_ne_zero] <;> nlinarith only [hbd]


private lemma cyclic_CyclicThetaMobius_theta_as_pos (g : 𝓢(ℝ,ℂ)) (hg : ∀ x, g x=cyclic_CyclicThetaMobius_dyad x) (h0 : g 0=0) (x : ℝ) :
    MasulloRH.GaussianApproximation.theta x = 2 * (∑' m : ℕ+, cyclic_CyclicThetaMobius_dyad (((m:ℕ):ℝ) * Real.exp x)) := by
  have even (u : ℝ) : cyclic_CyclicThetaMobius_dyad (-u) = cyclic_CyclicThetaMobius_dyad u := by simp [cyclic_CyclicThetaMobius_dyad,mul_neg]
  have h : MasulloRH.GaussianApproximation.theta x = MasulloRH.theta g (Real.exp x) := by
    unfold MasulloRH.GaussianApproximation.theta MasulloRH.theta; simp_rw [hg]; rfl
  rw [h, MasulloRH.theta_split g h0 (Real.exp_pos x), tsum_pnat_eq_tsum_succ (f:=fun n:ℕ => cyclic_CyclicThetaMobius_dyad ((n:ℝ)*Real.exp x)), ← tsum_mul_left]
  apply tsum_congr
  intro n
  change g (((n:ℝ)+1)*Real.exp x) + g (-(((n:ℝ)+1)*Real.exp x)) = _
  rw [hg,hg,even,Nat.cast_add,Nat.cast_one,two_mul]

open MasulloRH.GaussianApproximation in
theorem theta_moebius_hasSum (x : ℝ) :
    HasSum (fun j : ℕ => (ArithmeticFunction.moebius (j+1):ℂ)*theta (x+Real.log ((j:ℝ)+1))) (2*generator x) := by
  obtain ⟨g,hg,h0,_,_,_⟩ := MasulloRH.dyadic_gaussian_theta_mellin
  let b (n : ℕ) := cyclic_CyclicThetaMobius_dyad ((n:ℝ)*Real.exp x)
  have hi := cyclic_CyclicThetaMobius_inversion (b:=b) (cyclic_CyclicThetaMobius_dyad_decay g hg x)
  have hh (n : ℕ+) : theta (x+Real.log ((n:ℕ):ℝ)) = 2* ∑' m : ℕ+, b (n.val*m.val) := by
    rw [cyclic_CyclicThetaMobius_theta_as_pos g hg h0,Real.exp_add,Real.exp_log (show 0<((n:ℕ):ℝ) by exact_mod_cast n.property)]
    congr 1; apply tsum_congr; intro m; dsimp [b]; push_cast; ring_nf
  have hsh : HasSum (fun n : ℕ+ => (ArithmeticFunction.moebius n : ℂ)*theta (x+Real.log ((n:ℕ):ℝ))) (2*generator x) := by
    have ht : HasSum (fun n : ℕ+ => (2:ℂ)*((ArithmeticFunction.moebius n : ℂ)*∑' m : ℕ+, b (n.val*m.val))) (2*b 1) := hi.mul_left (2:ℂ)
    have eq1 : b 1 = generator x := by simp [b,cyclic_CyclicThetaMobius_generator_eq]
    rw [eq1] at ht
    apply ht.congr_fun
    intro n; rw [hh]; ring
  have h := (hasSum_pnat_iff_hasSum_succ (f:=fun n : ℕ => (ArithmeticFunction.moebius n:ℂ)*theta (x+Real.log (n:ℝ)))).mp hsh
  simpa only [Nat.cast_add,Nat.cast_one] using h

open MasulloRH.GaussianApproximation in
theorem theta_moebius_tendsto (x : ℝ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (ArithmeticFunction.moebius (j+1):ℂ)*theta (x+Real.log ((j:ℝ)+1)))
      atTop (𝓝 (2*generator x)) := (theta_moebius_hasSum x).tendsto_sum_nat

end MasulloCyclic
end

end StandaloneCyclicThetaMobius

section StandaloneCyclicDyadApprox

open Filter Asymptotics Set MasulloRH.GaussianApproximation
open scoped Topology
namespace MasulloCyclic
noncomputable section

theorem generator_eq_dyadDifference : generator = dyadDifference := by
  have hG (x : ℝ) : G x = gaussian x := by
    unfold G gaussian
    rw [show 2*x=x+x by ring,Real.exp_add,pow_two]
  funext x
  change generator x = (gaussian x-2*gaussian (x+Real.log 2))-
    (gaussian (x+Real.log 2)-2*gaussian (x+Real.log 2+Real.log 2))
  simp only [generator,hG,show x+Real.log 2+Real.log 2 = x+2*Real.log 2 by ring]
  ring

/-- On strips above an exponent for the Mertens function, the physical dyadic difference
is in the weighted uniform closure of finite linear combinations of theta translates. -/
theorem dyadDifference_mem_approx_of_mertens {A B β : ℝ} (hA : 0<A) (hAB : A≤B)
    (hB : B<1) (hβ : β<A)
    (hM : (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℂ)) =O[atTop]
      fun n : ℕ => (n:ℝ)^β) : dyadDifference ∈ approx A B (translates theta) := by
  rw [← generator_eq_dyadDifference]
  exact target_mem_approx_of_mertens hA.le hAB hβ hM theta generator theta_differentiable
    (theta_weighted_bounds hA hAB hB) theta_moebius_tendsto

theorem dyadDifference_mem_approx_of_rh (hRH : RiemannHypothesis) {A B : ℝ} (hA : 1/2<A)
    (hAB : A≤B) (hB : B<1) : dyadDifference ∈ approx A B (translates theta) :=
  dyadDifference_mem_approx_of_mertens (by linarith) hAB hB (β:=1/2+(A-1/2)/2) (by linarith)
    (moebius_summatory_rpow_bound_of_riemannHypothesis hRH _ (by linarith))

end
end MasulloCyclic

end StandaloneCyclicDyadApprox

section StandaloneCyclicGramBridge

open Set Filter Asymptotics MeasureTheory
open scoped Topology ENNReal BigOperators
open MasulloRH.GaussianApproximation

namespace MasulloCyclic
noncomputable section

def RApprox (A B : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ ε > (0:ℝ), ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
    ∀ x, w A B x * ‖f x - ∑ i, ratc (a i)*theta (x-(y i:ℝ))‖ ≤ ε

theorem rational_energy_approx {β c b : ℝ} (hβ : β<c-b) (hb : 0≤b) (h1 : c+b<1)
    (f : ℝ → ℂ) (hf : Continuous f)
    (hu : ∀ A B : ℝ, β<A → A≤B → B<1 → RApprox A B f) {δ : ℝ} (hδ : 0<δ) :
    ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let r (x : ℝ) := f x - ∑ i, ratc (a i)*theta (x-(y i:ℝ))
      Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖r x‖^2) ∧ energy c b r < δ := by
  let J := Σ m : ℕ, (Fin m → ℚ × ℚ) × (Fin m → ℚ)
  let err (j : J) (x : ℝ) := f x - ∑ i, ratc (j.2.1 i)*theta (x-(j.2.2 i:ℝ))
  have hme (j : J) : AEStronglyMeasurable (err j) volume :=
    (hf.sub (continuous_finsetSum _ (fun i _ => continuous_const.mul
      (theta_differentiable.continuous.comp (continuous_id.sub continuous_const))))).aestronglyMeasurable
  obtain ⟨⟨m,a,y⟩,he⟩ := exists_small_energy_of_interior_approx err hme hβ hb h1 (by
    intro A B hA hAB hB ε hε
    obtain ⟨m,a,y,h⟩ := hu A B hA hAB hB ε hε
    exact ⟨⟨m,a,y⟩,h⟩) hδ
  exact ⟨m,a,y,he⟩

theorem cofinal_gram_of_pulse_approx
    (h : ∀ (A B : ℝ), 1/2<A → A≤B → B<1 → ∀ T : ℝ, 0≤T → RApprox A B (pulse T)) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      energy (3/4) (1/4-δ) (residual n
         (fun i => ((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I) (fun i => (y i : ℝ))) <
          δ * Real.exp (-(1/2:ℝ)) := by
  intro N
  refine ⟨N,le_rfl,?_⟩
  let δ : ℝ := 1/(16*((N:ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbound : δ ≤ 1/16 := by
    dsimp [δ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [Nat.cast_nonneg (α:=ℝ) N]
  obtain ⟨m,a,y,_,he⟩ := rational_energy_approx (β:=1/2) (c:=3/4) (b:=1/4-δ)
    (by linarith) (by linarith) (by linarith) (pulse N) (by unfold pulse; fun_prop)
    (fun A B hA hAB hB => h A B hA hAB hB N (by positivity))
    (δ:=δ*Real.exp (-(1/2:ℝ))) (by positivity)
  exact ⟨m,a,y,he⟩

end
end MasulloCyclic

end StandaloneCyclicGramBridge

section StandaloneCyclicPolynomial

open Set Filter Polynomial
open scoped Topology
namespace MasulloRH.Cyclic
noncomputable section

def gauss (x : ℝ) : ℝ := Real.exp (-Real.pi * Real.exp (2*x))

def weight (A B x : ℝ) : ℝ := max (Real.exp (A*x)) (Real.exp (B*x))

theorem weight_pos (A B x : ℝ) : 0 < weight A B x :=
  lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)

theorem gauss_pos (x : ℝ) : 0 < gauss x := Real.exp_pos _

theorem gauss_lt_one (x : ℝ) : gauss x < 1 := Real.exp_lt_one_iff.mpr (by
  nlinarith only [mul_pos Real.pi_pos (Real.exp_pos (2*x))])

theorem gauss_antitone : Antitone gauss := by
  intro x y h
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
    (Real.exp_le_exp.mpr (by linarith)) (neg_nonpos.mpr Real.pi_pos.le))

theorem weighted_gauss_le_one {A B : ℝ} (hA : 0 < A) (hAB : A≤B) (hB : B<1) (x : ℝ) :
    weight A B x * gauss x ≤ 1 := by
  have ht {a : ℝ} (ha : 0≤a) (ha' : a≤1) : Real.exp (a*x) * gauss x ≤ 1 := by
    rw [gauss,←Real.exp_add,Real.exp_le_one_iff]
    by_cases hx : x ≤ 0
    · have h := mul_nonpos_of_nonneg_of_nonpos ha hx
      nlinarith only [h,mul_pos Real.pi_pos (Real.exp_pos (2*x))]
    · have hx' := le_of_not_ge hx
      have hax := mul_le_mul_of_nonneg_right ha' hx'
      have he := Real.add_one_le_exp (2*x)
      have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (2*x)).le
      nlinarith
  rw [weight,max_mul_of_nonneg _ _ (gauss_pos x).le]
  exact max_le (ht hA.le (hAB.trans hB.le)) (ht (hA.le.trans hAB) hB.le)

private def cyclic_CyclicPolynomial_inverseGauss (z : ℝ) := Real.log ((-Real.log z) / Real.pi) / 2

private theorem cyclic_CyclicPolynomial_inverseGauss_gauss (x : ℝ) : cyclic_CyclicPolynomial_inverseGauss (gauss x) = x := by
  simp only [cyclic_CyclicPolynomial_inverseGauss,gauss,Real.log_exp,neg_mul,neg_neg,mul_div_cancel_left₀ _ Real.pi_ne_zero]
  ring

private theorem cyclic_CyclicPolynomial_factor_compact {f : ℝ → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∃ H : ℝ → ℂ, Continuous H ∧ ∀ x, f x = (gauss x:ℂ) * H (gauss x) := by
  obtain ⟨C,hC⟩ := hcs.isBounded.exists_norm_le
  let R := max 0 C + 1
  have hR : 0<R := by dsimp [R]; positivity
  have hzero {x : ℝ} (hx : R ≤ |x|) : f x = 0 := by
    by_contra hn
    have hh := hC x (subset_tsupport f (show x ∈ Function.support f from hn))
    rw [Real.norm_eq_abs] at hh
    have hc : C<R := by dsimp [R]; linarith only [le_max_right (0:ℝ) C]
    linarith
  let L := gauss R
  let U := gauss (-R)
  have hLU : L≤U := gauss_antitone (by linarith)
  let k (z : ℝ) := max L (min z U)
  have hk : Continuous k := continuous_const.max (continuous_id.min continuous_const)
  have hpos (z : ℝ) : 0 < k z := (gauss_pos R).trans_le (le_max_left ..)
  have hlt (z : ℝ) : k z < 1 := (max_le hLU (min_le_right z U)).trans_lt (gauss_lt_one _)
  have hlog : Continuous (fun z : ℝ => Real.log (k z)) := hk.log (fun z => (hpos z).ne')
  have hinner : Continuous (fun z : ℝ => (-Real.log (k z)) / Real.pi) := hlog.neg.div_const _
  have hInv : Continuous (fun z : ℝ => cyclic_CyclicPolynomial_inverseGauss (k z)) :=
    (hinner.log (fun z => (div_pos (neg_pos.mpr (Real.log_neg (hpos z) (hlt z))) Real.pi_pos).ne')).div_const _
  refine ⟨fun z => f (cyclic_CyclicPolynomial_inverseGauss (k z)) / (k z : ℂ),
    (hf.comp hInv).div (Complex.continuous_ofReal.comp hk) (fun z => by exact_mod_cast (hpos z).ne'), ?_⟩
  intro x
  dsimp only
  by_cases hlo : x < -R
  · have hg := gauss_antitone hlo.le
    have ha : k (gauss x)=gauss (-R) := by
      exact (congrArg (max L) (min_eq_right hg)).trans (max_eq_right hLU)
    rw [ha,cyclic_CyclicPolynomial_inverseGauss_gauss,hzero (x := -R) (by rw [abs_neg,abs_of_pos hR]),
      hzero (x := x) (by rw [abs_of_neg (by linarith)]; linarith),zero_div,mul_zero]
  by_cases hhi : R < x
  · have hg := gauss_antitone hhi.le
    have ha : k (gauss x)=gauss R := max_eq_left (le_trans (min_le_left _ _) hg)
    rw [ha,cyclic_CyclicPolynomial_inverseGauss_gauss,hzero (x := R) (by rw [abs_of_pos hR]),
      hzero (x := x) (by rw [abs_of_pos (lt_trans hR hhi)]; linarith),zero_div,mul_zero]
  · have h1 : L ≤ gauss x := gauss_antitone (le_of_not_gt hhi)
    have h2 : gauss x ≤ U := gauss_antitone (le_of_not_gt hlo)
    have ha : k (gauss x) = gauss x := (congrArg (max L) (min_eq_left h2)).trans (max_eq_right h1)
    rw [ha,cyclic_CyclicPolynomial_inverseGauss_gauss,mul_div_cancel₀ _ (by exact_mod_cast (gauss_pos x).ne' : (gauss x:ℂ) ≠ 0)]

private theorem cyclic_CyclicPolynomial_complex_poly_near {H : ℝ → ℂ} (hc : Continuous H) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ z ∈ Icc (0:ℝ) 1, ‖H z - P.eval (z:ℂ)‖ < ε := by
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun x => (H x).re)
    (Complex.continuous_re.comp hc).continuousOn (ε/2) (by positivity)
  obtain ⟨q,hq⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun x => (H x).im)
    (Complex.continuous_im.comp hc).continuousOn (ε/2) (by positivity)
  refine ⟨p.map Complex.ofRealHom + q.map Complex.ofRealHom * Polynomial.C Complex.I, ?_⟩
  intro z hz
  have he (p : Polynomial ℝ) : (p.map Complex.ofRealHom).eval (z:ℂ) = ((p.eval z : ℝ):ℂ) :=
    Polynomial.eval_map_apply (p := p) Complex.ofRealHom z
  apply lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,he,Complex.sub_re,
    Complex.sub_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
    sub_zero,add_zero,zero_add]
  linarith only [abs_sub_comm (H z).re (p.eval z) ▸ hp z hz,abs_sub_comm (H z).im (q.eval z) ▸ hq z hz]

theorem gauss_shift (x : ℝ) (n : ℕ) :
    gauss (x + Real.log ((n:ℝ)+1)/2) = (gauss x)^(n+1) := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  rw [gauss,gauss,show 2*(x+Real.log ((n:ℝ)+1)/2) = 2*x+Real.log ((n:ℝ)+1) by ring,
    Real.exp_add,Real.exp_log hn,←Real.exp_nat_mul]
  push_cast
  congr 1
  ring

private theorem cyclic_CyclicPolynomial_gaussian_polynomial_eval (P : Polynomial ℂ) (x : ℝ) :
    (∑ i : Fin (P.natDegree+1), P.coeff i * (gauss (x+Real.log ((i:ℝ)+1)/2):ℂ)) =
      (gauss x : ℂ) * P.eval (gauss x:ℂ) := by
  simp only [gauss_shift,Complex.ofReal_pow,Polynomial.eval_eq_sum_range,Finset.mul_sum]
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

theorem compact_gauss_approx (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) (hB : B < 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hcs : HasCompactSupport f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (y : Fin m → ℝ),
      ∀ x : ℝ, weight A B x * ‖f x - ∑ i, c i * (gauss (x+y i):ℂ)‖ < ε := by
  obtain ⟨H,hH,he⟩ := cyclic_CyclicPolynomial_factor_compact hf hcs
  obtain ⟨P,hP⟩ := cyclic_CyclicPolynomial_complex_poly_near hH hε
  refine ⟨P.natDegree+1,fun i => P.coeff i,fun i => Real.log ((i:ℝ)+1)/2,?_⟩
  intro x
  rw [cyclic_CyclicPolynomial_gaussian_polynomial_eval,he,←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (gauss_pos x),←mul_assoc]
  exact (mul_le_of_le_one_left (norm_nonneg _) (weighted_gauss_le_one hA hAB hB x)).trans_lt
    (hP _ ⟨(gauss_pos x).le,(gauss_lt_one x).le⟩)

end
end MasulloRH.Cyclic

end StandaloneCyclicPolynomial

section StandaloneCyclicPolynomialPulse

open Set Filter
open scoped Topology
open MasulloRH.GaussianApproximation
namespace MasulloRH.Cyclic
noncomputable section

private theorem cyclic_CyclicPolynomialPulse_weighted_small_tail_approx {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hB : B < 1)
    {f : ℝ → ℂ} (hf : Continuous f)
    (htail : ∀ δ > (0:ℝ), ∃ R : ℝ, ∀ x, R ≤ |x| → weight A B x * ‖f x‖ < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (y : Fin m → ℝ),
      ∀ x : ℝ, weight A B x * ‖f x - ∑ i, c i * (gauss (x+y i):ℂ)‖ < ε := by
  obtain ⟨R,hR⟩ := htail (ε/2) (by positivity)
  let k (x : ℝ) := max 0 (min 1 (R+1-|x|))
  have hkc : Continuous k := continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))
  have hk0 (x : ℝ) : 0 ≤ k x := le_max_left .. 
  have hk1 (x : ℝ) : k x ≤ 1 := max_le zero_le_one (min_le_left ..)
  let F (x : ℝ) := (k x:ℂ)*f x
  have hFc : Continuous F := (Complex.continuous_ofReal.comp hkc).mul hf
  have hFcs : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -(R+1)) (b := R+1))
    intro x hx
    have hab : R+1 ≤ |x| := le_of_not_gt (fun j => hx ⟨(abs_lt.mp j).1.le,(abs_lt.mp j).2.le⟩)
    have hk : k x = 0 := max_eq_left ((min_le_right _ _).trans (by linarith))
    simp [F,hk]
  obtain ⟨m,c,y,he⟩ := compact_gauss_approx A B hA hAB hB F hFc hFcs (ε/2) (by positivity)
  refine ⟨m,c,y,fun x => ?_⟩
  have hsub : weight A B x * ‖f x - F x‖ < ε/2 := by
    by_cases h : |x| ≤ R
    · have hk : k x = 1 := by
        dsimp [k]
        rw [min_eq_left (by linarith : 1 ≤ R + 1 - |x|),max_eq_right zero_le_one]
      simp only [F,hk,Complex.ofReal_one,one_mul,sub_self,norm_zero,mul_zero]
      positivity
    · have hf' : f x - F x = ((1-k x : ℝ):ℂ)*f x := by push_cast; dsimp [F]; ring
      rw [hf',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hk1 x))]
      exact (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hk0 x]))
        (weight_pos A B x).le).trans_lt (hR x (le_of_not_ge h))
  calc
    _ ≤ weight A B x * (‖f x-F x‖ + ‖F x - ∑ i, c i*(gauss (x+y i):ℂ)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub ..) (weight_pos A B x).le
    _ < ε := by rw [mul_add]; linarith only [hsub,he x]

private theorem cyclic_CyclicPolynomialPulse_weight_le_exp_abs {A B : ℝ} (hA : 0 < A) (hAB : A≤B) (hB : B<1) (x : ℝ) :
    weight A B x ≤ Real.exp |x| := by
  have hb {c : ℝ} (hc : 0≤c) (hc' : c≤1) : Real.exp (c*x) ≤ Real.exp |x| := by
    apply Real.exp_le_exp.mpr
    by_cases hx : 0≤x
    · rw [abs_of_nonneg hx]
      simpa using mul_le_mul_of_nonneg_right hc' hx
    · exact (mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_ge hx)).trans (abs_nonneg _)
  exact max_le (hb hA.le (hAB.trans hB.le)) (hb (hA.le.trans hAB) hB.le)

theorem pulse_gauss_approx (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) (hB : B < 1)
    (T : ℝ) (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (y : Fin m → ℝ),
      ∀ x : ℝ, weight A B x * ‖pulse T x - ∑ i, c i * (gauss (x+y i):ℂ)‖ < ε := by
  apply cyclic_CyclicPolynomialPulse_weighted_small_tail_approx hA hAB hB (by unfold pulse; fun_prop) _ ε hε
  intro δ hδ
  let C := (T+1)/Real.sqrt Real.pi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun z : ℝ => C*Real.exp (-z)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  obtain ⟨R,hR⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 δ hδ)
  refine ⟨max 2 R,fun x hx => ?_⟩
  have hx2 := (le_max_left (2:ℝ) R).trans hx
  have hnorm : ‖pulse T x‖ = C*Real.exp (-((T+1)*x)^2) := by
    rw [pulse,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,Complex.norm_exp,
      ←Complex.ofReal_pow,Complex.neg_re,Complex.ofReal_re]
  have he : |x| - ((T+1)*x)^2 ≤ -|x| := by
    have habs := mul_le_mul_of_nonneg_right hx2 (abs_nonneg x)
    rw [←sq,sq_abs] at habs
    have hTx := mul_le_mul_of_nonneg_right (by nlinarith : 1≤(T+1)^2) (sq_nonneg x)
    rw [mul_pow]
    linarith
  calc
    _ ≤ Real.exp |x| * (C*Real.exp (-((T+1)*x)^2)) := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right (cyclic_CyclicPolynomialPulse_weight_le_exp_abs hA hAB hB x) (by positivity)
    _ = C * Real.exp (|x| - ((T+1)*x)^2) := by rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ C * Real.exp (-|x|) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC
    _ < δ := hR _ ((le_max_right _ R).trans hx)

end
end MasulloRH.Cyclic

end StandaloneCyclicPolynomialPulse

section StandaloneCyclicUniformTheta

open Filter Asymptotics Set
open MasulloRH.GaussianApproximation
open scoped Topology
namespace MasulloCyclic
noncomputable section

private lemma cyclic_CyclicUniformTheta_mem_gaussian_approx {A B : ℝ} (f : ℝ → ℂ)
    (H : ∀ ε : ℝ, 0<ε → ∃ (m : ℕ) (c : Fin m → ℂ) (y : Fin m → ℝ), ∀ x,
      MasulloRH.Cyclic.weight A B x * ‖f x - ∑ i, c i*(MasulloRH.Cyclic.gauss (x+y i):ℂ)‖ < ε) :
    f ∈ approx A B (translates gaussian) := by
  apply mem_approx.mpr
  intro ε hε
  obtain ⟨m,c,y,he⟩ := H ε hε
  let v : F := ∑ i, c i • shift (y i) gaussian
  have hv : v ∈ translates gaussian :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (shift_translate_mem gaussian _))
  refine ⟨v,hv,fun x => ?_⟩
  simpa only [w,MasulloRH.Cyclic.weight,v,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,shift,
    gaussian,MasulloRH.Cyclic.gauss] using (he x).le

/-- Finite theta sums with rational pairs as coefficients and rational shifts approximate
every continuous compactly supported test and every normalized Gaussian pulse in the
two-endpoint uniform norm, assuming a Mertens exponent below the lower endpoint. -/
theorem theta_uniform_of_mertens {A B β : ℝ} (hA : 0<A) (hAB : A≤B) (hB : B<1) (hβ : β<A)
    (hM : (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℂ)) =O[atTop]
      fun n : ℕ => (n:ℝ)^β) :
    let P := fun f : ℝ → ℂ => ∀ ε : ℝ, 0<ε → ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      ∀ x : ℝ, max (Real.exp (A*x)) (Real.exp (B*x)) *
        ‖f x - ∑ i, (((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) * theta (x-(y i:ℝ))‖ ≤ ε
    (∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → P f) ∧
      (∀ T : ℝ, 0≤T → P (pulse T)) := by
  intro P
  have hg := gauss_from_dyad hA hAB hB theta (dyadDifference_mem_approx_of_mertens hA hAB hB hβ hM)
  obtain ⟨C,hC,hθ⟩ := theta_physical_bounds.2 hA hAB hB
  have happrox (f : F) (hf : f ∈ approx A B (translates gaussian)) : P f := by
    intro ε hε
    exact finite_rationalization hA.le (hA.le.trans hAB) theta theta_differentiable hC.le
      (fun x => (hθ x).1) (fun x => (hθ x).2) (generators_change hg hf) hε
  constructor
  · intro f hf hcs
    exact happrox f (cyclic_CyclicUniformTheta_mem_gaussian_approx f (MasulloRH.Cyclic.compact_gauss_approx A B hA hAB hB f hf hcs))
  · intro T hT
    exact happrox (pulse T) (cyclic_CyclicUniformTheta_mem_gaussian_approx _ (MasulloRH.Cyclic.pulse_gauss_approx A B hA hAB hB T hT))

/-- Under RH each closed interval interior to the right half of the critical strip admits
the same finite rational approximations. -/
theorem theta_uniform_of_rh (hRH : RiemannHypothesis) {A B : ℝ} (hA : 1/2<A)
    (hAB : A≤B) (hB : B<1) :
    let P := fun f : ℝ → ℂ => ∀ ε : ℝ, 0<ε → ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      ∀ x : ℝ, max (Real.exp (A*x)) (Real.exp (B*x)) *
        ‖f x - ∑ i, (((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) * theta (x-(y i:ℝ))‖ ≤ ε
    (∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → P f) ∧
      (∀ T : ℝ, 0≤T → P (pulse T)) :=
  theta_uniform_of_mertens (by linarith) hAB hB (β:=1/2+(A-1/2)/2) (by linarith)
    (moebius_summatory_rpow_bound_of_riemannHypothesis hRH _ (by linarith))

end
end MasulloCyclic

end StandaloneCyclicUniformTheta

section StandaloneCyclicFinal

open Set MeasureTheory Filter Asymptotics
open scoped Topology ENNReal BigOperators
open MasulloRH.GaussianApproximation

theorem solution :
    (∀ β c b : ℝ, 0≤β → 0≤b → β<c-b → c+b<1 →
      (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℂ)) =O[atTop]
        (fun n : ℕ => (n:ℝ)^β) →
      let μ := volume.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (2*c*x+2*b*|x|)))
      let P := fun f : ℝ → ℂ => ∀ ε > (0:ℝ),
        ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ), ∀ x : ℝ,
          max (Real.exp ((c-b)*x)) (Real.exp ((c+b)*x)) *
            ‖f x - ∑ i, (((a i).1:ℂ)+((a i).2:ℂ)*Complex.I)*theta (x-(y i:ℝ))‖ ≤ ε
      (∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → P f) ∧
      (∀ T : ℝ, 0≤T → P (pulse T)) ∧
      Dense {u : Lp ℂ 2 μ | ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        (u:ℝ→ℂ) =ᵐ[μ] fun x => ∑ i, (((a i).1:ℂ)+((a i).2:ℂ)*Complex.I)*theta (x-(y i:ℝ))} ∧
      (Submodule.span ℂ {u : Lp ℂ 2 μ | ∃ y : ℚ, (u:ℝ→ℂ) =ᵐ[μ] fun x => theta (x-(y:ℝ))}).topologicalClosure = ⊤) ∧
    (RiemannHypothesis ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        let δ : ℝ := 1/(16*((n:ℝ)+1))
        energy (3/4) (1/4-δ) (residual n
          (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) <
            δ*Real.exp (-(1/2:ℝ))) := by
  constructor
  · intro β c b hβ hb hlo hhi hM μ P
    have hu := MasulloCyclic.theta_uniform_of_mertens (lt_of_le_of_lt hβ hlo)
      (show c-b≤c+b by linarith) hhi hlo hM
    have hd := MasulloCyclic.rational_theta_dense_of_compact_approx c b
      MasulloCyclic.theta_differentiable.continuous (fun f hf hcs δ hδ =>
      MasulloCyclic.rational_energy_approx hlo hb hhi f hf (fun A B hA hAB hB =>
        (MasulloCyclic.theta_uniform_of_mertens (lt_of_le_of_lt hβ hA) hAB hB hA hM).1 f hf hcs) hδ)
    exact ⟨hu.1,hu.2,hd,MasulloCyclic.theta_ae_span_eq_top_of_dense c b (lt_of_le_of_lt hβ hlo)
      hhi MasulloCyclic.theta_differentiable.continuous hd⟩
  · exact ⟨fun hRH => MasulloCyclic.cofinal_gram_of_pulse_approx
      (fun A B hA hAB hB => (MasulloCyclic.theta_uniform_of_rh hRH hA hAB hB).2),
      MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.2⟩

end StandaloneCyclicFinal
