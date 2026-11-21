-- Prove2me | solution 1 for MasulloGRH.mellin_of_expDecay
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:06:46.617627+00:00
-- url     : https://prove2.me/submissions/0412cb03-277e-4a4f-b42a-047d843dd28f

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
open MellinLogProof MasulloGRH Set MeasureTheory Complex
open scoped ContDiff
namespace ExpDecayAppendix

private theorem abs_wall {a b u : ℝ} (hu : u∈Icc a b) :
    |u| ≤ max |a| |b| := by
  apply abs_le.mpr
  constructor
  · have h := neg_le_abs a;linarith [hu.1,le_max_left |a| |b|]
  · exact hu.2.trans ((le_abs_self b).trans (le_max_right _ _))

private theorem at_strip {φ : ℝ→ℂ} (hφ : HasExpDecay φ) (a b : ℝ) (k : ℕ) :
    HasWall φ k (Icc a b) := from_decay hφ (max |a| |b|) k (fun u hu x=>Or.inl (calc
      u*x ≤ |u*x| := le_abs_self _
      _ ≤ max |a| |b| * |x| := by rw [abs_mul];gcongr;exact abs_wall hu))

end ExpDecayAppendix
open ExpDecayAppendix

open MellinLogProof MasulloGRH Set MeasureTheory Complex

theorem solution (ϕ : ℝ → ℂ) (hϕ : HasExpDecay ϕ) :
    (∀ s : ℂ, MellinConvergent ϕ s) ∧
    Differentiable ℂ (mellin ϕ) ∧
    (∀ a b : ℝ, a < b → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ y : ℝ, y ≠ 0 →
      ‖mellin ϕ (σ + y * Complex.I)‖ ≤ C * |y| ^ (-(N : ℤ))) ∧
    ((∀ t : ℝ, 0 < t → t ≤ 1 → ϕ t = 0) →
      ∀ b : ℝ, ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ σ : ℝ, σ ≤ b → ∀ y : ℝ, y ≠ 0 →
        ‖mellin ϕ (σ + y * Complex.I)‖ ≤ C * |y| ^ (-(N : ℤ))) := by
  have hf := curve_smooth hϕ.1
  refine ⟨?_,?_,?_,?_⟩
  · intro s
    exact wall_convergent hf.continuous (at_strip hϕ s.re s.re 0) ⟨le_rfl,le_rfl⟩
  · intro s
    exact analytic_between hf.continuous (point_decay hϕ (s.re-1)) (point_decay hϕ (s.re+1)) (by linarith) (by linarith)
  · intro a b hab N hN
    obtain ⟨C,hC⟩ := walls_budget hf (at_strip hϕ a b) N
    exact ⟨C,fun σ hσ hσ' => hC σ ⟨hσ,hσ'⟩⟩
  · intro hs b N hN
    have hh (k : ℕ) : HasWall ϕ k (Iic b) := by
      apply from_decay hϕ |b|
      intro σ hσ x
      by_cases hx : 0 ≤ x
      · left
        rw [abs_of_nonneg hx]
        exact mul_le_mul_of_nonneg_right (hσ.trans (le_abs_self b)) hx
      · right;exact supported_jets hs k (lt_of_not_ge hx)
    obtain ⟨C,hC⟩ := walls_budget hf hh N
    exact ⟨C,fun σ hσ=>hC σ hσ⟩
