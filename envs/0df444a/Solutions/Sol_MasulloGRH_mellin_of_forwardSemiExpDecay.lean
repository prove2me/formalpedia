-- Prove2me | solution 1 for MasulloGRH.mellin_of_forwardSemiExpDecay
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:09:51.410178+00:00
-- url     : https://prove2.me/submissions/0377831d-10ad-4ed5-82b3-84ae126c4f38

import Definitions.Def_MasulloGRH_MellinRpos
open MeasureTheory Set Filter Topology Complex Asymptotics
open scoped ContDiff
namespace MellinLogProof
noncomputable section

def curve (φ : ℝ→ℂ) : ℝ→ℂ := fun x => φ (Real.exp x)
def twist (s : ℂ) (f : ℝ→ℂ) (x : ℝ) := Complex.exp (s*x)*f x
theorem twist_norm (s : ℂ) (f : ℝ→ℂ) (x : ℝ) :
    ‖twist s f x‖ = Real.exp (s.re*x)*‖f x‖ := by simp [twist,Complex.norm_exp,Complex.mul_re]

private theorem change_at (φ : ℝ→ℂ) (s : ℂ) (x : ℝ) :
    |Real.exp x| • (((Real.exp x : ℝ):ℂ)^(s-1) • φ (Real.exp x)) = twist s (curve φ) x := by
  rw [abs_of_pos (Real.exp_pos x),Complex.real_smul,smul_eq_mul,←mul_assoc,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),←Complex.ofReal_log (Real.exp_pos x).le,Real.log_exp,Complex.ofReal_exp,←Complex.exp_add]
  simp only [twist,curve];congr 2;ring

theorem mellin_log (φ : ℝ→ℂ) (s : ℂ) : mellin φ s = ∫ x,twist s (curve φ) x := by
  rw [mellin,←Real.range_exp,←Set.image_univ,integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,setIntegral_univ]
  exact integral_congr_ae (Eventually.of_forall (change_at φ s))

theorem conv_log (φ : ℝ→ℂ) (s : ℂ) : MellinConvergent φ s ↔ Integrable (twist s (curve φ)) := by
  rw [MellinConvergent,←Real.range_exp,←Set.image_univ,integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,integrableOn_univ]
  simp only [change_at]

theorem curve_smooth {φ : ℝ→ℂ} (h : MasulloGRH.IsSchwartzRpos φ) : ContDiff ℝ ∞ (curve φ) := by
  obtain ⟨ψ,hψ⟩ := h
  exact (funext hψ : (ψ:ℝ→ℂ)=curve φ) ▸ ψ.smooth ⊤

theorem phi_continuousOn {φ : ℝ→ℂ} (hf : Continuous (curve φ)) : ContinuousOn φ (Ioi 0) := by
  apply (hf.comp_continuousOn (Real.continuousOn_log.mono (by intro t ht;exact (show 0 < t from ht).ne'))).congr
  intro t ht;simp [curve,Real.exp_log (show 0 < t from ht)]

theorem analytic_between {φ : ℝ→ℂ} {a b : ℝ} (hφ : Continuous (curve φ))
    (ha : ∃ C : ℝ, ∀ x : ℝ, Real.exp (a*x)*‖curve φ x‖ ≤ C)
    (hb : ∃ C : ℝ, ∀ x : ℝ, Real.exp (b*x)*‖curve φ x‖ ≤ C)
    {s : ℂ} (h₁ : a < s.re) (h₂ : s.re < b) : DifferentiableAt ℂ (mellin φ) s := by
  have aux (u : ℝ) (hh : ∃ C : ℝ, ∀ x : ℝ, Real.exp (u*x)*‖curve φ x‖ ≤ C) :
      ∃ C : ℝ,∀ t : ℝ,0 < t → ‖φ t‖ ≤ C*‖t^(-u)‖ := by
    obtain ⟨C,hC⟩ := hh
    refine ⟨C,fun t ht=>?_⟩
    have h := hC (Real.log t)
    rw [curve,Real.exp_log ht] at h
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),Real.rpow_def_of_pos ht,
      show Real.log t * -u= -(u*Real.log t) by ring,Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
    simpa only [mul_comm] using h
  obtain ⟨A,hA⟩ := aux a ha
  obtain ⟨B,hB⟩ := aux b hb
  exact mellin_differentiableAt_of_isBigO_rpow ((phi_continuousOn hφ).locallyIntegrableOn measurableSet_Ioi)
    (isBigO_iff.mpr ⟨B,(eventually_gt_atTop (0:ℝ)).mono hB⟩) h₂
    (isBigO_iff.mpr ⟨A,eventually_mem_nhdsWithin.mono hA⟩) h₁

theorem integral_derivative (s : ℂ) (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f)
    (hi : ∀ k, Integrable (twist s (iteratedDeriv k f))) (k : ℕ) :
    (∫ x,twist s (iteratedDeriv k f) x)=(-s)^k * ∫ x,twist s f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    let u := fun x : ℝ => Complex.exp (s*x)
    let v := iteratedDeriv k f
    have hu (x : ℝ) : HasDerivAt u (s*u x) x := by
      have h := ((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul s).cexp
      simpa [u,mul_comm] using h
    have hv (x : ℝ) : HasDerivAt v (iteratedDeriv (k+1) f x) x := by
      rw [iteratedDeriv_succ]
      exact (hf.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k) x).hasDerivAt
    have ht : Integrable ((fun x=>s*u x)*v) := by
      change Integrable (fun x => (s*u x)*v x)
      have hh := (hi k).const_mul s
      simpa only [Pi.mul_apply,mul_assoc,u,v,twist] using hh
    have hstep := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _=>hu x) (fun x _=>hv x)
      (hi (k+1)) ht (hi k)
    change (∫ x,twist s (iteratedDeriv (k+1) f) x)=_ at hstep ⊢
    calc
      _ = -∫ x,(s*u x)*v x := hstep
      _ = -s*(∫ x,twist s (iteratedDeriv k f) x) := by simp [twist,u,v,mul_assoc,integral_const_mul]
      _ = _ := by rw [ih,pow_succ];ring

theorem derivative_budget (s : ℂ) (φ : ℝ→ℂ) (hf : ContDiff ℝ ∞ (curve φ))
    (hi : ∀ k, Integrable (twist s (iteratedDeriv k (curve φ)))) (k : ℕ) {C : ℝ}
    (hb : ‖∫ x,twist s (iteratedDeriv k (curve φ)) x‖ ≤ C) (hy : s.im ≠ 0) :
    ‖mellin φ s‖ ≤ C * |s.im|^(-(k:ℤ)) := by
  rw [integral_derivative s _ hf hi,norm_mul,norm_pow,norm_neg,←mellin_log] at hb
  rw [zpow_neg,zpow_natCast,←div_eq_mul_inv,le_div_iff₀ (pow_pos (abs_pos.mpr hy) _)]
  calc
    ‖mellin φ s‖*|s.im|^k ≤ ‖mellin φ s‖*‖s‖^k := by gcongr;exact Complex.abs_im_le_norm _
    _ ≤ C := by rwa [mul_comm]
end
end MellinLogProof
open MeasureTheory Set Filter Topology Complex MasulloGRH
open scoped ContDiff
namespace MellinLogProof
noncomputable section

theorem exp_abs_integrable : Integrable (fun x : ℝ=>Real.exp (-|x|)) := by
  rw [←integrableOn_univ,←Iic_union_Ioi (a:=(0:ℝ)),integrableOn_union]
  constructor
  · apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
    intro x hx;change Real.exp x=Real.exp (-|x|);rw [abs_of_nonpos (mem_Iic.mp hx),neg_neg]
  · apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
    intro x hx;change Real.exp (-x)=Real.exp (-|x|);rw [abs_of_pos (mem_Ioi.mp hx)]

def HasWall (φ : ℝ→ℂ) (k : ℕ) (S : Set ℝ) :=
  ∃ g : ℝ→ℝ, Integrable g ∧ ∀ σ ∈ S,∀ x,Real.exp (σ*x)*‖iteratedDeriv k (curve φ) x‖ ≤ g x

theorem wall_convergent {φ : ℝ→ℂ} (hf : Continuous (curve φ)) {S : Set ℝ}
    (h : HasWall φ 0 S) {s : ℂ} (hs : s.re ∈ S) : MellinConvergent φ s := by
  obtain ⟨G,hG,hh⟩ := h
  apply (conv_log φ s).mpr
  apply hG.mono' ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul hf).aestronglyMeasurable
  exact Eventually.of_forall (fun x=>by change ‖twist s (curve φ) x‖ ≤ G x;rw [twist_norm];simpa only [iteratedDeriv_zero] using hh s.re hs x)

theorem walls_budget {φ : ℝ→ℂ} (hf : ContDiff ℝ ∞ (curve φ)) {S : Set ℝ}
    (hwall : ∀ k,HasWall φ k S) (N : ℕ) :
    ∃ C : ℝ,∀ σ ∈ S,∀ y : ℝ,y ≠ 0 →
      ‖mellin φ (σ+y*Complex.I)‖ ≤ C*|y|^(-(N:ℤ)) := by
  obtain ⟨g,hg,hdom⟩ := hwall N
  refine ⟨∫ x,g x,fun σ hσ y hy=>?_⟩
  let s : ℂ := σ+y*I
  have hre : s.re=σ := by simp [s]
  have him : s.im=y := by simp [s]
  have hi (k : ℕ) : Integrable (twist s (iteratedDeriv k (curve φ))) := by
    obtain ⟨G,hG,hh⟩ := hwall k
    apply hG.mono'
    · exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        (hf.continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k:ℕ∞)≤⊤)))).aestronglyMeasurable
    · exact Eventually.of_forall (fun x=>by rw [twist_norm,hre];exact hh σ hσ x)
  have hb : ‖∫ x,twist s (iteratedDeriv N (curve φ)) x‖ ≤ ∫ x,g x :=
    norm_integral_le_of_norm_le hg (Eventually.of_forall (fun x=> by rw [twist_norm,hre];exact hdom σ hσ x))
  simpa only [him] using derivative_budget s φ hf hi N hb (him ▸ hy)

theorem decay_wall {φ : ℝ→ℂ} (hφ : HasExpDecay φ) (A : ℝ) (k : ℕ) {S : Set ℝ}
    (h : ∀ σ ∈ S,∀ x : ℝ,σ*x ≤ A*|x| ∨ iteratedDeriv k (curve φ) x=0) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ σ ∈ S,∀ x, Real.exp (σ*x)*‖iteratedDeriv k (curve φ) x‖ ≤ C*Real.exp (-|x|) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (A+1)
  obtain ⟨C,hC⟩ := hφ.2 M k
  refine ⟨max C 0,le_max_right _ _,fun σ hσ x=>?_⟩
  rcases h σ hσ x with hx|hz
  · have he : σ*x ≤ (M:ℝ)*|x| + -|x| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hM.le) (abs_nonneg x)]
    have hb := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (norm_nonneg (iteratedDeriv k (curve φ) x))
    rw [Real.exp_add] at hb
    have hh := mul_le_mul_of_nonneg_right ((hC x).trans (le_max_left C 0)) (Real.exp_pos (-|x|)).le
    change Real.exp ((M:ℝ)*|x|)*‖iteratedDeriv k (curve φ) x‖*Real.exp (-|x|) ≤ _ at hh
    exact hb.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh)
  · rw [hz,norm_zero,mul_zero];positivity

theorem from_decay {φ : ℝ→ℂ} (hφ : HasExpDecay φ) (A : ℝ) (k : ℕ) {S : Set ℝ}
    (h : ∀ σ ∈ S,∀ x : ℝ,σ*x ≤ A*|x| ∨ iteratedDeriv k (curve φ) x=0) : HasWall φ k S := by
  obtain ⟨C,hC,hh⟩ := decay_wall hφ A k h
  exact ⟨_,exp_abs_integrable.const_mul C,hh⟩

theorem point_decay {φ : ℝ→ℂ} (hφ : HasExpDecay φ) (σ : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, Real.exp (σ*x)*‖curve φ x‖ ≤ C := by
  obtain ⟨C,hC,hh⟩ := decay_wall hφ |σ| 0 (S:={σ}) (fun u hu x=>by
    have := mem_singleton_iff.mp hu;subst u;left;rw [←abs_mul];exact le_abs_self _)
  refine ⟨C,fun x=>?_⟩
  have h := hh σ (mem_singleton _) x
  simp only [iteratedDeriv_zero] at h
  exact h.trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))))

theorem supported_jets {φ : ℝ→ℂ} (hs : ∀ t : ℝ,0 < t → t≤1 → φ t=0)
    (k : ℕ) {x : ℝ} (hx : x<0) : iteratedDeriv k (curve φ) x=0 := by
  have he : curve φ =ᶠ[𝓝 x] fun _=>0 := by
    filter_upwards [gt_mem_nhds hx] with u hu
    exact hs _ (Real.exp_pos _) (Real.exp_le_one_iff.mpr hu.le)
  simpa only [iteratedDeriv_const,ite_self] using he.iteratedDeriv_eq k
end
end MellinLogProof
open MeasureTheory Set Filter Topology Complex MasulloGRH
open scoped ContDiff
namespace MellinLogProof
noncomputable section

theorem semi_envelope {φ : ℝ→ℂ} (hf : HasForwardSemiExpDecay φ) {a b : ℝ} (_ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc a b, ∀ x : ℝ,
      Real.exp (σ*x)*‖iteratedDeriv k (curve φ) x‖ ≤ C*Real.exp (-(a*|x|)) := by
  obtain ⟨ψ,hψ⟩ := hf.1
  have heq : (ψ:ℝ→ℂ)=curve φ := funext hψ
  let A := SchwartzMap.seminorm ℝ 0 k ψ
  have hA (x : ℝ) : ‖iteratedDeriv k (curve φ) x‖ ≤ A := by
    rw [←heq];simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℝ 0 k ψ x
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  obtain ⟨M,hM⟩ := exists_nat_gt (b+a)
  obtain ⟨B,hB⟩ := hf.2 M k
  refine ⟨max A B,hA0.trans (le_max_left _ _),fun σ hσ x=>?_⟩
  rcases le_total x 0 with hx|hx
  · rw [abs_of_nonpos hx, mul_neg,neg_neg]
    have he : σ*x ≤ a*x := mul_le_mul_of_nonpos_right hσ.1 hx
    rw [mul_comm (max A B)]
    exact mul_le_mul (Real.exp_le_exp.mpr he) ((hA x).trans (le_max_left _ _)) (norm_nonneg _) (Real.exp_pos _).le
  · rw [abs_of_nonneg hx]
    have he : σ*x ≤ (M:ℝ)*x + -(a*x) := by
      have hh := mul_le_mul_of_nonneg_right ((show σ+a ≤ b+a by linarith [hσ.2]).trans hM.le) hx
      linarith
    have h1 := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (norm_nonneg (iteratedDeriv k (curve φ) x))
    rw [Real.exp_add] at h1
    have h2 := mul_le_mul_of_nonneg_right ((hB x hx).trans (le_max_right A B)) (Real.exp_pos (-(a*x))).le
    change Real.exp ((M:ℝ)*x)*‖iteratedDeriv k (curve φ) x‖*Real.exp (-(a*x)) ≤ _ at h2
    exact h1.trans (by simpa only [mul_comm,mul_left_comm,mul_assoc] using h2)

theorem semi_wall {φ : ℝ→ℂ} (hf : HasForwardSemiExpDecay φ) {a : ℝ} (ha : 0 < a) (b : ℝ) (k : ℕ) :
    HasWall φ k (Icc a b) := by
  obtain ⟨C,hC,h⟩ := semi_envelope hf (b:=b) ha k
  refine ⟨_,?_,h⟩
  apply Integrable.const_mul
  have hh := (integrable_comp_mul_left_iff (fun x : ℝ=>Real.exp (-|x|)) ha.ne').mpr exp_abs_integrable
  simpa only [abs_mul,abs_of_pos ha] using hh

theorem semi_point {φ : ℝ→ℂ} (hf : HasForwardSemiExpDecay φ) {σ : ℝ} (hσ : 0<σ) :
    ∃ C : ℝ, ∀ x, Real.exp (σ*x)*‖curve φ x‖ ≤ C := by
  obtain ⟨C,hC,hh⟩ := semi_envelope hf (b:=σ) hσ 0
  refine ⟨C,fun x=>?_⟩
  have he := hh σ ⟨le_rfl,le_rfl⟩ x
  simp only [iteratedDeriv_zero] at he
  exact he.trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hσ.le (abs_nonneg _)))))

theorem semi_diff {φ : ℝ→ℂ} (hf : HasForwardSemiExpDecay φ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin φ) s :=
  analytic_between (curve_smooth hf.1).continuous (semi_point hf (by linarith : 0 < s.re/2))
    (semi_point hf (by linarith : 0 < s.re+1)) (by linarith) (by linarith)

theorem strip_unif_zero {φ : ℝ→ℂ} {a b : ℝ} (hw : HasWall φ 0 (Icc a b)) :
    ∃ B : ℝ,0 < B ∧ ∀ σ∈Icc a b,∀ y : ℝ,‖mellin φ (σ+y*I)‖ ≤ B := by
  obtain ⟨g,hg,hh⟩ := hw
  refine ⟨1+|∫ x,g x|,by positivity,fun σ hσ y=>?_⟩
  rw [mellin_log]
  apply (norm_integral_le_of_norm_le hg _).trans (by linarith [le_abs_self (∫ x,g x)])
  apply Eventually.of_forall;intro x
  rw [twist_norm];simpa only [add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,iteratedDeriv_zero] using hh σ hσ x

end
end MellinLogProof
open MeasureTheory Set Filter Topology Complex MasulloGRH
namespace MellinLogProof
noncomputable section

private theorem tail_power_integrable {q : ℝ} (hq : 1 < q) :
    IntegrableOn (fun y : ℝ=> |y| ^ (-q)) {y : ℝ | 1/2 ≤ |y|} := by
  let r : ℝ := 1/2
  have hr : 0 < r := by norm_num [r]
  have hpos : IntegrableOn (fun x : ℝ => x^(-q)) (Ici r) :=
    ((integrableOn_Ioi_rpow_iff hr).mpr (by linarith)).congr_set_ae Ioi_ae_eq_Ici.symm
  have hn := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding).mpr hpos
  have ht : {y : ℝ | 1/2 ≤ |y|}= Iic (-r) ∪ Ici r := by
    ext x;change r ≤ |x| ↔ x ≤ -r ∨ r ≤ x
    rw [le_abs];constructor <;> intro h <;> rcases h with h|h <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
  rw [ht,integrableOn_union]
  constructor
  · have he : Neg.neg ⁻¹' (Ici r) = Iic (-r) := by ext x;simp
    rw [he] at hn
    apply hn.congr_fun _ measurableSet_Iic
    intro x hx;change (-x)^(-q)=|x|^(-q);rw [abs_of_nonpos (by have := mem_Iic.mp hx;linarith)]
  · apply hpos.congr_fun _ measurableSet_Ici
    intro x hx;change x^(-q)=|x|^(-q);rw [abs_of_nonneg (hr.le.trans (mem_Ici.mp hx))]

theorem vertical_lp (F : ℝ→ℂ) (hF : Continuous F) (B C p : ℝ) (N : ℕ)
    (hB : 0<B) (hC : 0≤C) (hp : 1≤p) (hN : 1<N)
    (small : ∀ y, ‖F y‖ ≤ B) (large : ∀ y : ℝ, y ≠ 0 → ‖F y‖ ≤ C*|y|^(-(N:ℤ))) :
    Integrable (fun y : ℝ=> ‖F y‖^p) ∧ (∫ y : ℝ,‖F y‖^p)^(1/p) ≤
      (B^p+C^p*∫ y in {y : ℝ|1/2≤|y|},|y|^(-(p*N)))^(1/p) := by
  let A := Ioo (-(1/2):ℝ) (1/2)
  let T := {y : ℝ|1/2≤|y|}
  let W := fun y : ℝ => |y|^(-(p*N))
  let G := fun y : ℝ => A.indicator (fun _=>B^p) y+T.indicator (fun t=>C^p*W t) y
  have hA : MeasurableSet A := measurableSet_Ioo
  have hT : MeasurableSet T := measurableSet_le measurable_const measurable_id.abs
  have hpp : 0<p := by linarith
  have hq : 1<p*(N:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg N : (0:ℝ) ≤ N)
    have h' : (1:ℝ) < N := by exact_mod_cast hN
    linarith
  have ht : IntegrableOn W T := tail_power_integrable hq
  have ha : IntegrableOn (fun _ : ℝ=>B^p) A :=
    integrableOn_const (hs:=by dsimp [A];exact (measure_Ioo_lt_top (μ:=(volume : Measure ℝ))).ne)
  have hwt : IntegrableOn (fun y=>C^p*W y) T := ht.const_mul (C^p)
  have hG : Integrable G := (ha.integrable_indicator hA).add (hwt.integrable_indicator hT)
  have htarget (y : ℝ) (hy : y∈T) : ‖F y‖^p ≤ C^p*W y := by
    have hz : y≠0 := by intro he;subst y;norm_num [T] at hy
    calc
      _ ≤ (C*|y|^(-(N:ℤ)))^p := Real.rpow_le_rpow (norm_nonneg _) (large y hz) hpp.le
      _ = _ := by
        rw [Real.mul_rpow hC (zpow_nonneg (abs_nonneg _) _),←Real.rpow_intCast,←Real.rpow_mul (abs_nonneg _)]
        dsimp [W];push_cast;ring_nf
  have hdom (y : ℝ) : ‖F y‖^p ≤ G y := by
    by_cases hy : y∈T
    · change _ ≤ A.indicator _ y + T.indicator _ y
      rw [indicator_of_mem hy]
      exact (htarget _ hy).trans (le_add_of_nonneg_left (indicator_nonneg (fun _ _=>Real.rpow_nonneg hB.le _) _))
    · have hsmall : |y|<1/2 := lt_of_not_ge hy
      have hya : y∈A := abs_lt.mp hsmall
      simp only [G,indicator_of_mem hya,indicator_of_notMem hy,add_zero]
      exact Real.rpow_le_rpow (norm_nonneg _) (small y) hpp.le
  have hFi : Integrable (fun y : ℝ=>‖F y‖^p) := by
    apply hG.mono' (hF.norm.measurable.pow measurable_const).aestronglyMeasurable
    exact Eventually.of_forall (fun y=>by rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)];exact hdom y)
  refine ⟨hFi,Real.rpow_le_rpow (integral_nonneg fun _=>Real.rpow_nonneg (norm_nonneg _) _) ?_ (by positivity)⟩
  apply (integral_mono hFi hG hdom).trans_eq
  rw [show (∫ y,G y) = (∫ y in A,B^p)+(∫ y in T,C^p*W y) from by
    unfold G;rw [integral_add (ha.integrable_indicator hA) (hwt.integrable_indicator hT),
      integral_indicator hA,integral_indicator hT]]
  rw [integral_const_mul,setIntegral_const,Measure.real_def]
  norm_num [A,Real.volume_Ioo,W,T]
end
end MellinLogProof

open MellinLogProof MasulloGRH Set MeasureTheory Complex

theorem solution (ϕ : ℝ → ℂ) (hϕ : HasForwardSemiExpDecay ϕ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent ϕ s) ∧
    DifferentiableOn ℂ (mellin ϕ) {s : ℂ | 0 < s.re} ∧
    (∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ y : ℝ, y ≠ 0 →
      ‖mellin ϕ (σ + y * Complex.I)‖ ≤ C * |y| ^ (-(N : ℤ))) ∧
    (∀ p : ℝ, 1 ≤ p → ∀ N : ℕ, 1 < N → ∃ B C : ℝ, 0 < B ∧
      (∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ y : ℝ, y ≠ 0 →
        ‖mellin ϕ (σ + y * Complex.I)‖ ≤ C * |y| ^ (-(N : ℤ))) ∧
      ∀ σ : ℝ, a ≤ σ → σ ≤ b →
        MeasureTheory.Integrable (fun y : ℝ => ‖mellin ϕ (σ + y * Complex.I)‖ ^ p) ∧
        (∫ y : ℝ, ‖mellin ϕ (σ + y * Complex.I)‖ ^ p) ^ (1 / p) ≤
          (B ^ p + C ^ p * ∫ y in {y : ℝ | 1 / 2 ≤ |y|}, |y| ^ (-(p * N))) ^ (1 / p)) := by
  have hf := curve_smooth hϕ.1
  have hw := semi_wall hϕ ha b
  refine ⟨?_,?_,?_,?_⟩
  · intro s hs
    exact wall_convergent hf.continuous (semi_wall hϕ hs s.re 0) ⟨le_rfl,le_rfl⟩
  · intro s hs
    exact (semi_diff hϕ hs).differentiableWithinAt
  · intro N hN
    obtain ⟨C,hh⟩ := walls_budget hf hw N
    exact ⟨C,fun σ hσ hσ'=>hh σ ⟨hσ,hσ'⟩⟩
  · intro p hp N hN
    obtain ⟨B,hB,hsmall⟩ := strip_unif_zero (hw 0)
    obtain ⟨C,hlarge⟩ := walls_budget hf hw N
    have hlarge' (σ : ℝ) (hσ : σ∈Icc a b) (y : ℝ) (hy : y≠0) :
        ‖mellin ϕ (σ+y*I)‖ ≤ max C 0*|y|^(-(N:ℤ)) :=
      (hlarge σ hσ y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg (abs_nonneg _) _))
    refine ⟨B,max C 0,hB,fun σ hσ hσ' => hlarge' σ ⟨hσ,hσ'⟩,?_⟩
    intro σ hσ hσ'
    have hl : Continuous (fun y : ℝ => mellin ϕ (σ+y*I)) := by
      apply continuous_iff_continuousAt.mpr;intro y
      apply (semi_diff hϕ ?_).continuousAt.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      simpa using ha.trans_le hσ
    exact vertical_lp _ hl B _ p N hB (le_max_right _ _) hp hN (hsmall σ ⟨hσ,hσ'⟩) (hlarge' σ ⟨hσ,hσ'⟩)

