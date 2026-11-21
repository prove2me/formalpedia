-- Prove2me | solution 1 for MasulloGRH.trace_formula_integral_operators
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:31:55.177032+00:00
-- url     : https://prove2.me/submissions/6bbec8a8-12d8-421e-9b7e-56b5183db337

import Definitions.Def_MasulloGRH_HilbertNuclear
import Mathlib
import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series

open Set Filter MeasureTheory MasulloGRH
open scoped InnerProductSpace ENNReal Topology ComplexConjugate
namespace MasulloKernel
noncomputable section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
abbrev H (μ : Measure X) := Lp ℂ 2 μ

theorem sqnorm {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {f : Y → ℂ} (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖^2=∫ x,‖f x‖^2 ∂ν := by
  rw [Lp.norm_toLp,hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,←one_div (2:ℝ),←Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]

theorem lp_sqnorm {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} (f : H ν) :
    ‖f‖^2=∫ x,‖f x‖^2 ∂ν := by
  convert! sqnorm (Lp.memLp f) using 1
  rw [Lp.toLp_coeFn]

variable (k : X → X → ℂ)
def action (v : H μ) (x : X) := ∫ y,k x y*v y ∂μ
def rowEnergy (x : X) := ∫ y,‖k x y‖^2 ∂μ
def kernelNorm := (eLpNorm (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)).toReal
variable {k}
theorem rows (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ,MemLp (k x) 2 μ := by
  have h := (memLp_two_iff_integrable_sq_norm hk.1).mp hk
  filter_upwards [hk.1.prodMk_left,h.prod_right_ae] with x hx hi
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hi

theorem rowEnergy_integrable (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) :
    Integrable (rowEnergy (μ:=μ) k) μ :=
  ((memLp_two_iff_integrable_sq_norm hk.1).mp hk).integral_prod_left
theorem total_energy (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) :
    ∫ x,rowEnergy (μ:=μ) k x ∂μ=(kernelNorm (μ:=μ) k)^2 := by
  calc
    _ = ∫ z : X×X, ‖k z.1 z.2‖^2 ∂(μ.prod μ) :=
      (integral_prod _ ((memLp_two_iff_integrable_sq_norm hk.1).mp hk)).symm
    _ = ‖hk.toLp _‖^2 := (sqnorm hk).symm
    _ = _ := by rw [Lp.norm_toLp];rfl

theorem row_inner {f : X → ℂ} (hf : MemLp f 2 μ) (v : H μ) :
    (∫ y,f y*v y ∂μ) = inner ℂ (hf.star.toLp (star f)) v := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.star.coeFn_toLp] with y hy
  rw [hy,RCLike.inner_apply];simp [mul_comm]
theorem row_norm {f : X → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.star.toLp (star f)‖^2 = ∫ y,‖f y‖^2 ∂μ := by
  rw [sqnorm];simp
theorem action_bound (v : H μ) {x : X} (hx : MemLp (k x) 2 μ) :
    ‖action k v x‖^2 ≤ rowEnergy (μ:=μ) k x*‖v‖^2 := by
  rw [action,row_inner hx,rowEnergy,←row_norm hx,←mul_pow]
  gcongr;exact norm_inner_le_norm _ _
theorem action_meas (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) (v : H μ) :
    AEStronglyMeasurable (action k v) μ :=
  (hk.1.mul (Lp.aestronglyMeasurable v).comp_snd).integral_prod_right'
theorem action_mem (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) (v : H μ) :
    MemLp (action k v) 2 μ := by
  have hm := action_meas hk v
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply ((rowEnergy_integrable hk).mul_const (‖v‖^2)).mono'
  · exact (hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  · filter_upwards [rows hk] with x hx
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using action_bound v hx

def actLp (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) (v : H μ) : H μ :=
  (action_mem hk v).toLp _
theorem act_ae (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) (v : H μ) :
    (actLp hk v : X → ℂ)=ᵐ[μ] action k v := (action_mem hk v).coeFn_toLp

def op (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) : H μ →L[ℂ] H μ :=
  LinearMap.mkContinuous
    ({toFun := actLp hk
      map_add' := by
        intro f g;apply Lp.ext
        filter_upwards [act_ae hk (f+g),act_ae hk f,act_ae hk g,Lp.coeFn_add (actLp hk f) (actLp hk g),rows hk] with x h1 h2 h3 h4 hx
        rw [h1,h4,Pi.add_apply,h2,h3];simp only [action,row_inner hx,inner_add_right]
      map_smul' := by
        intro c f;apply Lp.ext
        filter_upwards [act_ae hk (c • f),act_ae hk f,Lp.coeFn_smul c (actLp hk f),rows hk] with x h1 h2 h3 hx
        rw [RingHom.id_apply,h1,h3,Pi.smul_apply,h2];simp only [action,row_inner hx,inner_smul_right,smul_eq_mul,RingHom.id_apply]
     } : H μ →ₗ[ℂ] H μ) (kernelNorm (μ:=μ) k) (by
        intro v
        apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _))).mp
        change ‖(action_mem hk v).toLp _‖^2 ≤ (kernelNorm (μ:=μ) k*‖v‖)^2
        rw [sqnorm,mul_pow,←total_energy hk,←integral_mul_const]
        apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm (action_meas hk v)).mp (action_mem hk v)) ((rowEnergy_integrable hk).mul_const _)
        filter_upwards [rows hk] with x hx using action_bound v hx)

theorem op_ae (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) (v : H μ) :
    (op hk v : X → ℂ) =ᵐ[μ] action k v := act_ae hk v
end
end MasulloKernel

open Set Filter MeasureTheory MasulloGRH
open scoped InnerProductSpace ENNReal Topology ComplexConjugate
namespace MasulloKernel
noncomputable section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
theorem count_basis {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] (b : HilbertBasis ι ℂ E) : Countable ι := by
  have hd : Pairwise (Function.onFun Disjoint (fun i => Metric.ball (b i) (1/2:ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have hsq := norm_sub_sq (𝕜:=ℂ) (b i) (b j)
    rw [b.orthonormal.norm_eq_one,b.orthonormal.norm_eq_one,b.orthonormal.inner_eq_zero hij] at hsq
    norm_num at hsq
    nlinarith [norm_nonneg (b i-b j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball) (fun i => ⟨b i,Metric.mem_ball_self (by norm_num)⟩)

private theorem parseval {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ x (b i)‖^2) (‖x‖^2) := by
  have h := Complex.hasSum_re (b.hasSum_inner_mul_inner x x)
  rw [inner_self_eq_norm_sq_to_K] at h
  convert! h using 1
  · ext i;rw [←inner_conj_symm (b i) x,Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]
  · change ‖x‖^2=((‖x‖:ℂ)^2).re
    simp [pow_two,Complex.mul_re]

theorem hs_parseval [TopologicalSpace.SeparableSpace (H μ)] {k : X → X → ℂ}
    (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ)) {ι : Type*} (b : HilbertBasis ι ℂ (H μ)) :
    HasSum (fun i => ‖op hk (b i)‖^2) (kernelNorm (μ:=μ) k ^ 2) := by
  classical
  letI : Countable ι := count_basis b
  let f := fun i (x : X) => ‖op hk (b i) x‖^2
  have hm (i : ι) : AEStronglyMeasurable (f i) μ := ((Lp.aestronglyMeasurable _).norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hrow : ∀ᵐ x ∂μ, HasSum (fun i => f i x) (rowEnergy (μ:=μ) k x) := by
    filter_upwards [rows hk,ae_all_iff.mpr (fun i => op_ae hk (b i))] with x hx heq
    change HasSum _ (∫ y,‖k x y‖^2 ∂μ)
    rw [←row_norm hx]
    apply (parseval b (hx.star.toLp (star (k x)))).congr_fun
    intro i;dsimp only [f];rw [heq,action,row_inner hx]
  have hint : Integrable (fun x => ∑' i,f i x) μ := (rowEnergy_integrable hk).congr (hrow.mono fun x hx => hx.tsum_eq.symm)
  have hsum := hasSum_integral_of_dominated_convergence (μ:=μ) f hm
    (fun i => ae_of_all _ fun x => (le_of_eq (Real.norm_of_nonneg (sq_nonneg _))))
    (hrow.mono fun x hx => hx.summable) hint hrow
  rw [total_energy hk] at hsum
  apply hsum.congr_fun
  intro i;exact lp_sqnorm _
end
end MasulloKernel

open Set Filter MeasureTheory MasulloGRH
open scoped InnerProductSpace ENNReal Topology ComplexConjugate
namespace MasulloKernel
noncomputable section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]

theorem balanced {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u v : E) :
    ∃ a b : E, ‖a‖^2=‖u‖*‖v‖ ∧ ‖b‖^2=‖u‖*‖v‖ ∧
      ∀ w : E,inner ℂ a w • b=inner ℂ u w • v := by
  by_cases hu : u=0
  · subst u;exact ⟨0,0,by simp,by simp,by simp⟩
  by_cases hv : v=0
  · subst v;exact ⟨0,0,by simp,by simp,by simp⟩
  let t := Real.sqrt (‖v‖/‖u‖)
  have ht : 0<t := Real.sqrt_pos.mpr (div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hu))
  have h2 : t^2=‖v‖/‖u‖ := Real.sq_sqrt (by positivity)
  refine ⟨(t:ℂ) • u,((t:ℂ)⁻¹) • v,?_,?_,?_⟩
  · rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,mul_pow,h2]
    field_simp [norm_ne_zero_iff.mpr hu]
  · rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,mul_pow,inv_pow,h2]
    field_simp [norm_ne_zero_iff.mpr hu,norm_ne_zero_iff.mpr hv]
  · intro w;rw [inner_smul_left,smul_smul,Complex.conj_ofReal]
    congr 1
    field_simp [show (t:ℂ)≠0 by exact_mod_cast ht.ne']

abbrev Feature := lp (fun _ : ℕ => ℂ) 2

theorem field_sq_ae (a : ℕ → H μ) (ha : Summable (fun n => ‖a n‖^2)) :
    ∀ᵐ x ∂μ,Summable (fun n => ‖a n x‖^2) := by
  let f := fun n (x : X) => ‖a n x‖^2
  have hm (n : ℕ) : Integrable (f n) μ := ((Lp.memLp (a n)).integrable_norm_pow (p:=2) (by norm_num))
  have hcol (n : ℕ) : eLpNorm (f n) 1 μ = ENNReal.ofReal (‖a n‖^2) := by
    rw [eLpNorm_one_eq_lintegral_enorm,←ofReal_integral_norm_eq_lintegral_enorm (hm n),lp_sqnorm (a n)]
    simp only [f,Real.norm_eq_abs,abs_pow,abs_norm]
  have hfinite : ∑' n,eLpNorm (f n) 1 μ ≠ ∞ := by
    simp_rw [hcol];rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) ha];exact ENNReal.ofReal_ne_top
  have h := summable_norm_of_tsum_eLpNorm_ne_top le_rfl (fun n => (hm n).1) hfinite
  simpa only [f,Real.norm_eq_abs,abs_pow,abs_norm] using h

def feature (a : ℕ → H μ) (x : X) : Feature :=
  ∑' n : ℕ,lp.single 2 n (a n x)

theorem feature_coord (a : ℕ → H μ) (ha : Summable (fun n => ‖a n‖^2)) :
    ∀ᵐ x ∂μ,∀ n,(feature a x) n=a n x := by
  filter_upwards [field_sq_ae a ha] with x hx
  have hm : Memℓp (fun n => a n x) 2 :=
    memℓp_gen <| by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hx
  let u : Feature := ⟨_,hm⟩
  have he : feature a x=u := (lp.hasSum_single (by simp) u).tsum_eq
  rw [he];exact fun _ => rfl

theorem feature_meas (a : ℕ → H μ) (ha : Summable (fun n => ‖a n‖^2)) :
    AEStronglyMeasurable (feature a) μ := by
  let t := fun n (x : X) => (lp.single 2 n (a n x) : Feature)
  have hm (n : ℕ) : AEStronglyMeasurable (t n) μ :=
    (lp.isometry_single (p:=2) (E:=fun _ : ℕ => ℂ) n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (a n))
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℕ)) (f:=fun s x => ∑ n∈s,t n x)
  · intro s;exact Finset.aestronglyMeasurable_fun_sum _ (fun n _ => hm n)
  · filter_upwards [feature_coord a ha] with x hx
    change HasSum (fun n => t n x) (feature a x)
    apply (lp.hasSum_single (by simp) (feature a x)).congr_fun
    intro n;dsimp only [t];rw [hx]

end
end MasulloKernel

open Set Filter MeasureTheory MasulloGRH
open scoped InnerProductSpace ENNReal Topology ComplexConjugate
namespace MasulloKernel
noncomputable section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]

theorem product_summable {r s : ℕ → ℝ} (hr : ∀ i,0≤r i) (hs : ∀ i,0 ≤ s i)
    (h₁ : Summable fun i => r i^2) (h₂ : Summable fun i => s i^2) :
    Summable fun i => r i*s i := by
  apply (h₁.add h₂).of_norm_bounded
  intro i;rw [Real.norm_of_nonneg (mul_nonneg (hr i) (hs i))]
  change r i*s i≤r i^2+s i^2
  nlinarith [sq_nonneg (r i-s i),sq_nonneg (r i+s i)]

private theorem smul_norms (c : ℕ → ℂ) (a : ℕ → H μ)
    (h : Summable (fun i => ‖c i‖*‖a i‖)) :
    Summable fun i => ‖c i • a i‖ := by simpa only [norm_smul] using h

private theorem eval_smul (c : ℕ → ℂ) (a : ℕ → H μ)
    (h : Summable (fun i => ‖c i‖*‖a i‖)) :
    ∀ᵐ y ∂μ,HasSum (fun i => c i * a i y) ((∑' i,c i • a i) y) := by
  have ht := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr (smul_norms c a h))
  filter_upwards [ht,ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (a i))] with y hy hsy
  apply hy.congr_fun;intro i;rw [hsy];rfl

private theorem basis_eval {ι : Type*} (B : HilbertBasis ι ℂ (H μ)) [Countable ι]
    {k : X → X → ℂ} (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ))
    (a b : ℕ → H μ) (hab : Summable fun n => ‖a n‖*‖b n‖)
    (hp : ∀ v : H μ, HasSum (fun n => inner ℂ (a n) v • b n) (op hk v)) :
    ∀ᵐ x ∂μ,∀ j,HasSum (fun n => inner ℂ (a n) (B j)*b n x) (action k (B j) x) := by
  apply ae_all_iff.mpr
  intro j
  have h : Summable (fun n => ‖inner ℂ (a n) (B j)‖*‖b n‖) := by
    apply hab.of_norm_bounded
    intro n;rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa [B.orthonormal.norm_eq_one] using norm_inner_le_norm (𝕜:=ℂ) (a n) (B j)
  have he := eval_smul (fun n => inner ℂ (a n) (B j)) b h
  rw [(hp (B j)).tsum_eq] at he
  filter_upwards [he,op_ae hk (B j)] with x hx hT; simpa only [hT] using hx

theorem kernel_rep [TopologicalSpace.SeparableSpace (H μ)] {k : X → X → ℂ}
    (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ))
    (a b : ℕ → H μ) (ha : Summable fun n => ‖a n‖^2) (hb : Summable fun n => ‖b n‖^2)
    (hab : Summable fun n => ‖a n‖*‖b n‖)
    (hp : ∀ v : H μ, HasSum (fun n => inner ℂ (a n) v • b n) (op hk v)) :
    ∀ᵐ x ∂μ,∀ᵐ y ∂μ,k x y=inner ℂ (feature a y) (feature b x) := by
  classical
  let B := chosenHilbertBasis (H μ)
  letI := count_basis B
  filter_upwards [basis_eval B hk a b hab hp,field_sq_ae b hb,feature_coord b hb,rows hk] with x hx hbx hB hxk
  let c := fun n => conj (b n x)
  have hs : Summable (fun n => ‖c n‖*‖a n‖) := by
    simpa only [c,RCLike.norm_conj] using product_summable (fun n => norm_nonneg (b n x)) (fun n => norm_nonneg (a n)) hbx ha
  let r : H μ := ∑' n,c n • a n
  have hr : HasSum (fun n => c n • a n) r := (smul_norms c a hs).of_norm.hasSum
  let u := hxk.star.toLp (star (k x))
  have he : r=u := by
    apply B.repr.injective;ext j
    rw [B.repr_apply_apply,B.repr_apply_apply]
    apply (starRingEnd ℂ).injective
    rw [inner_conj_symm,inner_conj_symm]
    have hI := hr.mapL (innerSLFlip ℂ (B j))
    have hs' : HasSum (fun n => inner ℂ (a n) (B j) * b n x) (inner ℂ r (B j)) := by
      apply hI.congr_fun
      intro n;dsimp only [innerSLFlip_apply_apply,c];rw [inner_smul_left,starRingEnd_self_apply];ring
    exact (hs'.unique (hx j)).trans (row_inner hxk (B j))
  have hrp := eval_smul c a hs
  change ∀ᵐ y ∂μ, HasSum (fun n => c n * a n y) (r y) at hrp
  filter_upwards [hrp,hxk.star.coeFn_toLp, feature_coord a ha] with y hy hu hA
  rw [he] at hy
  change u y=conj (k x y) at hu
  rw [hu] at hy
  have hconj := Complex.hasSum_conj'.mpr hy
  rw [starRingEnd_self_apply] at hconj
  apply hconj.unique
  apply (lp.hasSum_inner (feature a y) (feature b x)).congr_fun
  intro n;simp only [hA,hB,RCLike.inner_apply,c,map_mul,starRingEnd_self_apply] <;> ring

end
end MasulloKernel

open Set Filter MeasureTheory Topology
open scoped InnerProductSpace ENNReal Topology
namespace MasulloKernel
noncomputable section
variable {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure X}

private theorem graph_closure (V : X → E) (hV : AEMeasurable V μ) :
    ∀ᵐ x ∂μ, ∀ D ∈ ae μ, (x,V x) ∈ closure ((fun y => (y,V y)) '' D) := by
  let g := fun x => (x,V x)
  have hg : AEMeasurable g μ := aemeasurable_id.prodMk hV
  have htyp : ∀ᵐ x ∂μ, g x∈(μ.map g).support := ae_of_ae_map hg Measure.support_mem_ae
  filter_upwards [htyp] with x hx D hD
  apply mem_closure_iff.mpr
  intro W hW hxW
  have hm := (Measure.mem_support_iff_forall _).mp hx W (hW.mem_nhds hxW)
  rw [Measure.map_apply_of_aemeasurable hg hW.measurableSet] at hm
  by_contra hempty
  apply hm.ne'
  apply measure_mono_null (t:=Dᶜ) _ (mem_ae_iff.mp hD)
  intro y hy hyD
  exact hempty ⟨g y,hy,⟨y,hyD,rfl⟩⟩

theorem diagonal_eq (V U : X → E) (hV : AEMeasurable V μ) {k : X → X → ℂ}
    (hk : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, k x y = inner ℂ (V y) (U x))
    (hc : ∀ᵐ x ∂μ, ContinuousAt (fun p : X×X => k p.1 p.2) (x,x)) :
    ∀ᵐ x ∂μ,k x x=inner ℂ (V x) (U x) := by
  filter_upwards [graph_closure V hV,hk,hc] with x hx hrow hc
  let D := {y : X | k x y=inner ℂ (V y) (U x)}
  let q := fun z : X×E => k x z.1-inner ℂ z.2 (U x)
  have h1 : ContinuousAt (fun z : X×E => k x z.1) (x,V x) :=
    by
      have hm : ContinuousAt (fun z : X×E => (x,z.1)) (x,V x) := (continuous_const.prodMk continuous_fst).continuousAt
      exact hc.tendsto.comp hm.tendsto
  have hq : ContinuousAt q (x,V x) := h1.sub (continuous_snd.inner continuous_const).continuousAt
  have hz := mem_closure_image hq (hx D hrow)
  have hsub : q '' ((fun y => (y,V y)) '' D) ⊆ ({0} : Set ℂ) := by
    rintro _ ⟨_,⟨y,hy,rfl⟩,rfl⟩
    exact sub_eq_zero.mpr hy
  have hzero := closure_minimal hsub isClosed_singleton hz
  exact sub_eq_zero.mp hzero
end
end MasulloKernel

open Set Filter MeasureTheory MasulloGRH
open scoped InnerProductSpace ENNReal Topology ComplexConjugate
namespace MasulloKernel
noncomputable section
variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [SigmaFinite μ]

local instance : MeasurableSpace Feature := borel _
local instance : BorelSpace Feature := ⟨rfl⟩
local instance : SecondCountableTopology Feature := by
  let B : HilbertBasis ℕ ℂ Feature := ⟨LinearIsometryEquiv.refl ℂ _⟩
  have hsub : TopologicalSpace.IsSeparable (closure (Submodule.span ℂ (range B) : Set Feature)) :=
    ((countable_range B).isSeparable.span (R:=ℂ)).closure
  rw [show closure (Submodule.span ℂ (range B) : Set Feature) = univ from
    congrArg (fun s : Submodule ℂ Feature => (s:Set Feature)) B.dense_span] at hsub
  haveI := (TopologicalSpace.isSeparable_univ_iff).mp hsub
  exact UniformSpace.secondCountable_of_separable _
local instance : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

private theorem diag_aux (a b : ℕ → H μ) (ha : Summable fun n => ‖a n‖^2)
    (hb : Summable fun n => ‖b n‖^2) :
    Integrable (fun x => inner ℂ (feature a x) (feature b x)) μ ∧
    HasSum (fun n => inner ℂ (a n) (b n)) (∫ x,inner ℂ (feature a x) (feature b x) ∂μ) := by
  let g := fun n (x : X) => inner ℂ (a n x) (b n x)
  have hg (n : ℕ) : Integrable (g n) μ := MeasureTheory.L2.integrable_inner (𝕜:=ℂ) _ _
  have hn : Summable (fun n => ∫ x,‖g n x‖ ∂μ) := by
    apply (ha.add hb).of_norm_bounded
    intro n;rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    change _ ≤ ‖a n‖^2+‖b n‖^2
    rw [lp_sqnorm (a n),lp_sqnorm (b n),←integral_add ((Lp.memLp _).integrable_norm_pow (p:=2) (by norm_num)) ((Lp.memLp _).integrable_norm_pow (p:=2) (by norm_num))]
    apply integral_mono (hg n).norm (((Lp.memLp _).integrable_norm_pow (p:=2) (by norm_num)).add ((Lp.memLp _).integrable_norm_pow (p:=2) (by norm_num)))
    intro x
    change ‖inner ℂ (a n x) (b n x)‖≤‖a n x‖^2+‖b n x‖^2
    exact (norm_inner_le_norm _ _).trans (by nlinarith [sq_nonneg (‖a n x‖-‖b n x‖),sq_nonneg (‖a n x‖+‖b n x‖)])
  have heq : (fun x => ∑' n,g n x) =ᵐ[μ] fun x => inner ℂ (feature a x) (feature b x) := by
    filter_upwards [feature_coord a ha,feature_coord b hb] with x hx hy
    simp only [lp.inner_eq_tsum,hx,hy,g]
  let v := fun n => (hg n).toL1 (g n)
  have hv (n : ℕ) : (v n : X → ℂ) =ᵐ[μ] g n := (hg n).coeFn_toL1
  have hs : Summable (fun n => ‖v n‖) := by
    apply hn.congr;intro n;rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae ((hv n).symm.fun_comp norm)
  have hsum := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hs)
  have hfun : (⇑(∑' n,v n) : X→ℂ) =ᵐ[μ] fun x => ∑' n,g n x := by
    filter_upwards [hsum,ae_all_iff.mpr hv] with x hx h
    rw [hx];exact tsum_congr h
  refine ⟨(L1.integrable_coeFn (∑' n,v n)).congr (hfun.trans heq),?_⟩
  have hh := hasSum_integral_of_summable_integral_norm hg hn
  rw [integral_congr_ae heq] at hh
  exact hh

theorem kernel_trace {k : X → X → ℂ} (hk : MemLp (fun p : X×X => k p.1 p.2) 2 (μ.prod μ))
    (hn : IsNuclearOperator (op hk)) (hc : ∀ᵐ x ∂μ,ContinuousAt (fun p : X×X => k p.1 p.2) (x,x)) :
    Integrable (fun x => k x x) μ ∧ operatorTrace (op hk) = ∫ x,k x x ∂μ := by
  classical
  obtain ⟨u,v,hs,hT⟩ := hn
  choose a b ha hb he using fun n => balanced (u n) (v n)
  have hA : Summable (fun n => ‖a n‖^2) := hs.congr fun i => (ha i).symm
  have hB : Summable (fun n => ‖b n‖^2) := hs.congr fun i => (hb i).symm
  have hab := product_summable (fun n => norm_nonneg (a n)) (fun n => norm_nonneg (b n)) hA hB
  have hp (w : H μ) : HasSum (fun n => inner ℂ (a n) w • b n) (op hk w) :=
    (hT w).congr_fun fun n => he n w
  have hker := kernel_rep hk a b hA hB hab hp
  have hd := diagonal_eq (feature a) (feature b) (feature_meas a hA).aemeasurable hker hc
  change (fun x => k x x) =ᵐ[μ] (fun x => inner ℂ (feature a x) (feature b x)) at hd
  obtain ⟨hit,hint⟩ := diag_aux a b hA hB
  exact ⟨hit.congr hd.symm,(operatorTrace_of_nuclear_series (op hk) a b hab hp).trans (hint.tsum_eq.trans (integral_congr_ae hd.symm))⟩
end
end MasulloKernel

open MeasureTheory Filter Topology MasulloGRH MasulloKernel
open scoped ENNReal InnerProductSpace

theorem solution
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular] [SigmaFinite μ] (k : X → X → ℂ)
    (hk : MemLp (fun p : X × X => k p.1 p.2) 2 (μ.prod μ)) :
    ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      (∀ ϕ : Lp ℂ 2 μ, ∀ᵐ x ∂μ, T ϕ x = ∫ y, k x y * ϕ y ∂μ) ∧
      IsHilbertSchmidt T ∧
      hilbertSchmidtNorm T = (eLpNorm (fun p : X × X => k p.1 p.2) 2 (μ.prod μ)).toReal ∧
      (IsNuclearOperator T →
        (∀ᵐ x ∂μ, ContinuousAt (fun p : X × X => k p.1 p.2) (x, x)) →
        Integrable (fun x => k x x) μ ∧ operatorTrace T = ∫ x, k x x ∂μ)  := by
  classical
  haveI : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have h := hs_parseval hk (chosenHilbertBasis (Lp ℂ 2 μ))
  refine ⟨op hk,op_ae hk,h.summable,?_,kernel_trace hk⟩
  change Real.sqrt (∑' j,‖op hk (chosenHilbertBasis (Lp ℂ 2 μ) j)‖^2)=_
  rw [h.tsum_eq,Real.sqrt_sq (show 0≤kernelNorm (μ:=μ) k from ENNReal.toReal_nonneg)]
  rfl
