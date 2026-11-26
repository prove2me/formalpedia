-- Prove2me | solution 1 for LogLogJam.Supplement.squeezed_disk_readout
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:27:06.049223+00:00
-- url     : https://prove2.me/submissions/97eb2157-a578-4f27-a21e-e6f8958da966

import Mathlib
import Theorems.Thm_BosonicLearn_fockPOVM_of_effect
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
open MeasureTheory BosonicLearn Filter
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal Topology
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
namespace LogLogJam.Supplement.WeakProof
abbrev Idx := Occupation (Fin 1)
abbrev XY := ℝ × ℝ
def c (n : ℕ) : ℝ := Real.sqrt (n.centralBinom : ℝ) / 2^n
def freq (i : Idx) := Equiv.intEquivNat.symm (i 0)
def deg (i : Idx) := i 0 / 2
def factor (n : ℕ) (t : ℝ) : ℝ := Real.sin t ^ n / c n
def wave (i : Idx) (φ : ℝ) : ℂ := Complex.exp (-(freq i : ℂ)*Complex.I*φ)
def u (i : Idx) (x : XY) : ℂ := (factor (deg i) x.1 : ℂ)*wave i x.2
def arc (b : ℝ) : Measure ℝ := ENNReal.ofReal b⁻¹ • (volume.restrict (Set.Ico 0 b))
def nu : Measure XY := (arc Real.pi).prod (arc (2*Real.pi))
instance arc_finite (b : ℝ) : IsFiniteMeasure (arc b) := by
  constructor;simp [arc,Measure.smul_apply,Real.volume_Ico];finiteness
lemma arc_probability {b : ℝ} (hb : 0<b) : IsProbabilityMeasure (arc b) := by
  constructor; simp [arc,Measure.smul_apply,Real.volume_Ico,ENNReal.ofReal_inv_of_pos hb,ENNReal.ofReal_ne_top,(ENNReal.ofReal_pos.mpr hb).ne'];exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top
instance nu_probability : IsProbabilityMeasure nu := by
  unfold nu;let _ := arc_probability Real.pi_pos;let _ := arc_probability (show 0<2*Real.pi by positivity);infer_instance
lemma arc_int {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (b : ℝ) (hb : 0<b) :
    (∫ t, f t ∂arc b) = b⁻¹ • (∫ t in (0:ℝ)..b, f t) := by
  rw [arc,integral_smul_measure,ENNReal.toReal_ofReal (inv_nonneg.mpr hb.le),integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.le]
lemma arc_integrable {E : Type} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f) (b : ℝ) : Integrable f (arc b) := by
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  exact hf.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
lemma freq_inj : Function.Injective freq := by intro i j h;have e := Equiv.intEquivNat.symm.injective h;funext t;simpa [Subsingleton.elim t 0] using e
lemma freq_even (n : ℕ) : freq (fun _ => 2*n) = n := by
  apply Equiv.intEquivNat.injective;change Equiv.intEquivNat (Equiv.intEquivNat.symm (2*n))=Equiv.intEquivNat (n:ℤ);rw [Equiv.apply_symm_apply];rfl
lemma cpos (n) : 0 < c n := by dsimp [c];positivity [Nat.centralBinom_pos n]
lemma moment (n : ℕ) : (∫ t, Real.sin t^(2*n) ∂arc Real.pi) = (c n)^2 := by
  rw [arc_int _ _ Real.pi_pos,integral_sin_pow_even]
  simp only [smul_eq_mul,← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero,one_mul]
  have sq (n : ℕ) : (c n)^2 = (n.centralBinom:ℝ) / 4^n := by
    dsimp [c];rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)];congr 1;rw [← pow_mul,Nat.mul_comm,pow_mul];norm_num
  rw [sq];induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ,ih,pow_succ]
    have h : ((n:ℝ)+1) * (n.succ.centralBinom:ℝ) = 2*(2*(n:ℝ)+1)*n.centralBinom := by exact_mod_cast Nat.succ_mul_centralBinom_succ n
    field_simp; nlinarith [h]
lemma norm_factor (n : ℕ) : (∫ t, (factor n t)^2 ∂arc Real.pi) = 1 := by
  simp only [factor,div_pow,← pow_mul,show n*2=2*n by omega,integral_div,moment,div_self (pow_ne_zero _ (cpos n).ne')]
lemma phase_orth (i j : Idx) : (∫ t, conj (wave i t)*wave j t ∂arc (2*Real.pi)) = if i=j then 1 else 0 := by
  have h (t) : conj (wave i t) * wave j t = Complex.exp (((freq i-freq j : ℤ):ℂ)*Complex.I*t) := by
    dsimp [wave];rw [← Complex.exp_conj,← Complex.exp_add];push_cast;simp only [map_mul,map_neg,map_intCast,Complex.conj_I,Complex.conj_ofReal];congr 1;ring
  simp_rw [h];rw [arc_int _ _ (by positivity)]
  by_cases hij : i=j
  · subst j;simp [intervalIntegral.integral_const,Complex.real_smul,Real.pi_ne_zero];field_simp [show (Real.pi:ℂ)≠0 by exact_mod_cast Real.pi_ne_zero]
  · rw [if_neg hij,integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast sub_ne_zero.mpr (freq_inj.ne hij)) Complex.I_ne_zero)]
    have he : ((freq i-freq j : ℤ):ℂ)*Complex.I*(Complex.ofReal (2*Real.pi)) = (freq i-freq j:ℤ) * (2*Real.pi*Complex.I) := by push_cast;ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I];simp
lemma entries_int (i j : Idx) : Integrable (fun p => conj (u i p)*u j p) nu := by
  let f (t : ℝ) : ℂ := (factor (deg i) t : ℂ) * factor (deg j) t
  let g (t : ℝ) : ℂ := conj (wave i t)*wave j t
  have hf : Continuous f := by dsimp [f,factor];fun_prop
  have hg : Continuous g := by dsimp [g,wave];fun_prop
  have h := (arc_integrable hf Real.pi).mul_prod (arc_integrable hg (2*Real.pi))
  unfold nu;convert h using 1;funext p;dsimp [f,g,u];simp only [map_mul,Complex.conj_ofReal];ring
lemma orth (i j : Idx) : (∫ p, conj (u i p)*u j p ∂nu) = (1:Matrix Idx Idx ℂ) i j := by
  let f (t : ℝ) : ℂ := (factor (deg i) t : ℂ)*factor (deg j) t
  let g (t : ℝ) : ℂ := conj (wave i t)*wave j t
  have he (p : XY) : conj (u i p)*u j p = f p.1 * g p.2 := by dsimp [u,f,g];simp only [map_mul,Complex.conj_ofReal];ring
  simp_rw [he];rw [nu,integral_prod_mul];dsimp only [g];rw [phase_orth,Matrix.one_apply]
  by_cases e : i=j
  · subst j;simp only [if_true,mul_one];dsimp only [f];simp_rw [← sq,← Complex.ofReal_pow];calc
      _ = ((∫ t, (factor (deg i) t)^2 ∂arc Real.pi : ℝ) : ℂ) := integral_ofReal
      _ = _ := by rw [norm_factor];norm_num
  · simp [e]
end LogLogJam.Supplement.WeakProof

namespace LogLogJam.Supplement.WeakProof
def ix : Idx ≃ ℕ where
  toFun i := i 0
  invFun n := fun _ => n
  left_inv i := by funext t;simp [Subsingleton.elim t 0]
  right_inv _ := rfl
def zObs (x : XY) : ℂ := (Real.sin x.1 : ℂ)*Complex.exp (-Complex.I*x.2)
def psi (q : ℂ) (N : ℝ) (i : Idx) : ℂ := if Even (i 0) then ((N*c (deg i):ℝ):ℂ)*q^(deg i) else 0
def bounds (q : ℂ) (N : ℝ) (i : Idx) : ℝ := if Even (i 0) then |N| * ‖q‖^(deg i) else 0
lemma normZ (x : XY) : ‖zObs x‖ ≤ 1 := by
  rw [zObs,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp];simp only [Complex.neg_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,neg_zero,Real.exp_zero,mul_one]; simpa using Real.abs_sin_le_one x.1
lemma zsmall {q : ℂ} (hq : ‖q‖<1) (x) : ‖q*zObs x‖<1 := (norm_mul_le _ _).trans_lt ((show ‖q‖*‖zObs x‖ ≤ ‖q‖ by simpa using mul_le_mul_of_nonneg_left (normZ x) (norm_nonneg q)).trans_lt hq)
lemma evenA (q : ℂ) (N : ℝ) (n : ℕ) (x : XY) :
    psi q N (ix.symm (2*n))*u (ix.symm (2*n)) x = N*(q*zObs x)^n := by
  have hi : ix.symm (2*n) = fun _ => 2*n := rfl
  rw [hi];simp only [psi,deg,show Even (2*n) from even_two_mul _,if_true,Nat.mul_div_cancel_left _ (by decide : 0<2), u,wave,freq_even,zObs,factor]
  push_cast
  rw [mul_pow,mul_pow,← Complex.exp_nat_mul];push_cast;field_simp [show (c n:ℂ)≠0 by exact_mod_cast (cpos n).ne'] <;> ring_nf
lemma oddA (q : ℂ) (N : ℝ) (n : ℕ) (x : XY) : psi q N (ix.symm (2*n+1))*u (ix.symm (2*n+1)) x = 0 := by
  have hn : ¬ Even (2*n+1) := by simp
  simp [psi,ix,hn]
lemma sumA {q : ℂ} (hq : ‖q‖ < 1) (N : ℝ) (x : XY) :
    HasSum (fun i => psi q N i * u i x) ((N:ℂ)*(1-q*zObs x)⁻¹) := by
  apply (Equiv.hasSum_iff ix.symm).mp
  rw [← add_zero ((N:ℂ)*_)]
  apply HasSum.even_add_odd
  · simp only [Function.comp_apply,evenA];exact (hasSum_geometric_of_norm_lt_one (zsmall hq x)).mul_left _
  · simp only [Function.comp_apply,oddA];exact hasSum_zero
lemma bounds_sum {q : ℂ} (hq : ‖q‖<1) (N : ℝ) : Summable (bounds q N) := by
  apply (Equiv.summable_iff ix.symm).mp
  apply HasSum.summable (a := |N| * (1-‖q‖)⁻¹+0)
  apply HasSum.even_add_odd
  · simpa [bounds,ix,deg] using (hasSum_geometric_of_lt_one (norm_nonneg q) hq).mul_left |N|
  · simpa [bounds,ix] using (hasSum_zero (α:=ℝ) (β:=ℕ))
lemma bounds_ok (q : ℂ) (N : ℝ) (i : Idx) (x : XY) : ‖psi q N i*u i x‖ ≤ bounds q N i := by
  obtain ⟨n,hn⟩ := ix.symm.surjective i;subst i
  rcases Nat.even_or_odd' n with ⟨k,he|he⟩
  · rw [he,evenA];simp [bounds,ix,deg,norm_mul,norm_pow];gcongr; simpa using mul_le_mul_of_nonneg_left (normZ x) (norm_nonneg q)
  · rw [he,oddA];simp [bounds,ix]
end LogLogJam.Supplement.WeakProof

namespace LogLogJam.Supplement.WeakProof
lemma uniform_sum_integral {X I : Type} [MeasurableSpace X] [Countable I] (μ : Measure X) [IsFiniteMeasure μ]
    (f : I → X → ℂ) (F : X → ℂ) (b : I → ℝ) (hb : Summable b)
    (hm : ∀ i, Measurable (f i)) (hbound : ∀ i x, ‖f i x‖ ≤ b i) (hf : ∀ x, HasSum (fun i => f i x) (F x)) :
    (∑' i, ∫ x, f i x ∂μ) = ∫ x, F x ∂μ := by
  apply HasSum.tsum_eq
  exact hasSum_integral_of_dominated_convergence (fun i _ => b i) (fun i => (hm i).aestronglyMeasurable)
    (fun i => ae_of_all _ (hbound i)) (ae_of_all _ fun _ => hb) (integrable_const _) (ae_of_all _ hf)
lemma pure_readout {I X : Type} [DecidableEq I] [Countable I] [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (M : FockPOVM I X) (u : I → X → ℂ) (ψ : I → ℂ) (ρ : State I)
    (hM : ∀ B i j, M.effect B i j = ∫ x in B, conj (u i x)*u j x ∂μ)
    (hρ : ∀ i j, ρ.coefficients i j = ψ i*conj (ψ j))
    (F : X → ℂ) (b : I → ℝ) (K : ℝ) (hb : Summable b) (hb0 : ∀ i,0≤b i)
    (hm : ∀ i, Measurable (u i)) (hFm : Measurable F) (hK : ∀ x, ‖F x‖ ≤ K)
    (hbound : ∀ i x, ‖ψ i * u i x‖ ≤ b i) (hsum : ∀ x, HasSum (fun i => ψ i*u i x) (F x))
    (B : Set X) (hB : MeasurableSet B) :
    M.law ρ.coefficients B = ENNReal.ofReal (∫ x in B, ‖F x‖^2 ∂μ) := by
  let v i x := ψ i * u i x
  have hvm (i) : Measurable (v i) := measurable_const.mul (hm i)
  have hi (i j) : M.effect B i j * ρ.coefficients j i = ∫ x in B, conj (v i x) * v j x ∂μ := by
    rw [hρ,hM,← integral_mul_const]
    apply integral_congr_ae;filter_upwards with x;dsimp [v];rw [map_mul];ring
  have hj (i : I) : (∑' j, M.effect B i j * ρ.coefficients j i) = ∫ x in B, conj (v i x) * F x ∂μ := by
    simp_rw [hi]
    apply uniform_sum_integral _ _ _ (fun j => b i*b j) (hb.mul_left _)
    · intro j; exact ((Complex.continuous_conj.measurable.comp (hvm i)).mul (hvm j))
    · intro j x;rw [norm_mul,Complex.norm_conj]; exact mul_le_mul (hbound i x) (hbound j x) (norm_nonneg _) (hb0 i)
    · intro x;exact (hsum x).mul_left _
  have hsum' : (∑' i, ∫ x in B, conj (v i x)*F x ∂μ) = ∫ x in B, conj (F x)*F x ∂μ := by
    apply uniform_sum_integral _ _ _ (fun i => b i*K) (hb.mul_right K)
    · intro i; exact (Complex.continuous_conj.measurable.comp (hvm i)).mul hFm
    · intro i x;rw [norm_mul,Complex.norm_conj]; exact mul_le_mul (hbound i x) (hK x) (norm_nonneg _) (hb0 i)
    · intro x; exact ((hsum x).map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj).mul_right _
  rw [M.law_born _ ρ.density B hB]; simp_rw [hj]; rw [hsum']
  have hIF : (∫ x in B, conj (F x)*F x ∂μ) = ((∫ x in B, ‖F x‖^2 ∂μ : ℝ) : ℂ) := by
    simp_rw [Complex.conj_mul', ← Complex.ofReal_pow]; exact integral_ofReal
  rw [hIF];rfl
end LogLogJam.Supplement.WeakProof

private theorem orthogonal_readout {I X : Type} [DecidableEq I] [MeasurableSpace X]
    (ν : Measure X) (u : I → X → ℂ)
    (hi : ∀ i j, Integrable (fun x => conj (u i x) * u j x) ν)
    (ho : ∀ i j, ∫ x, conj (u i x) * u j x ∂ν = (1 : Matrix I I ℂ) i j) :
    ∃ M : FockPOVM I X, ∀ B : Set X, ∀ i j,
      M.effect B i j = ∫ x in B, conj (u i x) * u j x ∂ν := by
  classical
  let E := fun (B : Set X) (i j : I) => ∫ x in B, conj (u i x) * u j x ∂ν
  have hfull : E Set.univ = (1 : Matrix I I ℂ) := by
    ext i j
    simpa only [E, Measure.restrict_univ] using ho i j
  have hf (B : Set X) (s : Finset I) (z : I → ℂ) :
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j) =
        ((∫ x in B, ‖∑ i ∈ s, z i * u i x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    let F := fun (i j : I) (x : X) => conj (z i) * (conj (u i x) * u j x) * z j
    have hiF (i j : I) : Integrable (F i j) ν :=
      ((hi i j).const_mul _).mul_const _
    have hp (x : X) : (∑ i ∈ s, ∑ j ∈ s, F i j x) = ((‖∑ i ∈ s, z i * u i x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← Complex.conj_mul']
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [F]
      ring
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, ∫ x in B, F i j x ∂ν := by
        simp only [F, E, integral_mul_const, integral_const_mul, Complex.star_def]
      _ = ∫ x in B, ∑ i ∈ s, ∑ j ∈ s, F i j x ∂ν := by
        rw [integral_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => (hiF i j).integrableOn))]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum s (fun j _ => (hiF i j).integrableOn)]
      _ = _ := by simp_rw [hp]; exact integral_ofReal
  obtain ⟨M, hm⟩ := fockPOVM_of_effect E (by
    intro B hB s z
    rw [hf]
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
    refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
    have hplus (i j : I) : E B i j + E Bᶜ i j = E Set.univ i j := by
      simpa only [E, Measure.restrict_univ] using integral_add_compl hB (hi i j)
    have hadd : (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j) +
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E Bᶜ i j * z j) =
        ∑ i ∈ s, ∑ j ∈ s, star (z i) * E Set.univ i j * z j := by
      simp only [← Finset.sum_add_distrib, ← add_mul, ← mul_add, hplus]
    have hone : (∑ i ∈ s, ∑ j ∈ s, star (z i) * E Set.univ i j * z j) =
        ((∑ i ∈ s, ‖z i‖^2 : ℝ) : ℂ) := by
      rw [hfull, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro i hi'
      rw [Finset.sum_eq_single_of_mem i hi']
      · simp [Complex.conj_mul']
      · intro j _ hji
        simp [Ne.symm hji]
    rw [hone, hf, hf] at hadd
    have hsum := congrArg Complex.re hadd
    simp only [Complex.add_re, Complex.ofReal_re] at hsum
    exact le_of_le_of_eq (le_add_of_nonneg_right (integral_nonneg (fun x => sq_nonneg ‖∑ i ∈ s, z i * u i x‖))) hsum)
    hfull (fun i j f hm hd => hasSum_integral_iUnion hm hd (hi i j).integrableOn)
  exact ⟨M, fun B i j => congrFun (congrFun (congrFun hm B) i) j⟩




namespace LogLogJam.Supplement.WeakProof
theorem disk_measurement :
    ∃ M : FockPOVM Idx XY, ∀ (q : ℂ) (N : ℝ),
    ‖q‖ < 1 → ∀ ρ : State Idx, (∀ i j, ρ.coefficients i j = psi q N i * conj (psi q N j)) →
    ∀ B : Set XY, MeasurableSet B →
    M.law ρ.coefficients B = ENNReal.ofReal (∫ x in B, ‖(N:ℂ)*(1-q*zObs x)⁻¹‖^2 ∂nu) := by
  obtain ⟨M,hM⟩ := orthogonal_readout nu u entries_int orth
  refine ⟨M,?_⟩
  intro q N hq ρ hρ B hB
  let F (x : XY) := (N:ℂ)*(1-q*zObs x)⁻¹
  have hF : Measurable F := by dsimp [F,zObs];fun_prop
  have hn (x) : ‖q*zObs x‖ ≤ ‖q‖ := by rw [norm_mul];simpa using mul_le_mul_of_nonneg_left (normZ x) (norm_nonneg q)
  have hK (x) : ‖F x‖ ≤ |N| * (1-‖q‖)⁻¹ := by
    dsimp only [F];rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply inv_anti₀ (sub_pos.mpr hq)
    apply (sub_le_sub_left (hn x) 1).trans;simpa only [norm_one] using norm_sub_norm_le (1:ℂ) (q*zObs x)
  exact pure_readout nu M u _ ρ hM hρ F _ _ (bounds_sum hq N) (fun i => by dsimp [bounds];split <;> positivity)
    (fun i => by unfold u factor wave;fun_prop) hF hK (bounds_ok q N) (sumA hq N) B hB
end LogLogJam.Supplement.WeakProof

theorem solution :
    ∃ M : FockPOVM (Occupation (Fin 1)) (ℝ × ℝ), ∀ (q : ℂ) (N : ℝ),
    ‖q‖ < 1 → ∀ ρ : State (Occupation (Fin 1)),
    (let ψ (i : Occupation (Fin 1)) := if Even (i 0) then
      ((N * (Real.sqrt ((i 0 / 2).centralBinom : ℝ) / 2 ^ (i 0 / 2)) : ℝ) : ℂ) * q^(i 0 / 2) else 0
     ∀ i j, ρ.coefficients i j = ψ i * conj (ψ j)) →
    ∀ B : Set (ℝ × ℝ), MeasurableSet B →
      let arc := fun b : ℝ => ENNReal.ofReal b⁻¹ • (volume.restrict (Set.Ico 0 b))
      M.law ρ.coefficients B = ENNReal.ofReal (∫ x in B,
        ‖(N:ℂ)*(1-q*((Real.sin x.1:ℂ)*Complex.exp (-Complex.I*x.2)))⁻¹‖^2
          ∂((arc Real.pi).prod (arc (2*Real.pi)))) := LogLogJam.Supplement.WeakProof.disk_measurement
