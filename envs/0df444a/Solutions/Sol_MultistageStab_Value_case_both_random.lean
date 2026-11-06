-- Prove2me | solution 1 for MultistageStab.Value.case_both_random
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:18:58.241292+00:00
-- url     : https://prove2.me/submissions/f993c019-addd-4293-baa9-6780cb7308c1

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

set_option linter.unusedSectionVars false


open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value.SolAux
open MultistageStab.Value

lemma Xc_add {D : Data} {t : ℕ} {x y : E (D.m t)} (hx : x ∈ Xc D t) (hy : y ∈ Xc D t) :
    x + y ∈ Xc D t := by
  intro i
  rw [inner_add_right]
  linarith [hx i, hy i]

lemma Xc_smul {D : Data} {t : ℕ} {x : E (D.m t)} (hx : x ∈ Xc D t) {c : ℝ} (hc : 0 ≤ c) :
    c • x ∈ Xc D t := by
  intro i
  rw [inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos hc (hx i)

lemma Xc_zero {D : Data} {t : ℕ} : (0 : E (D.m t)) ∈ Xc D t := by
  intro i; simp

lemma Xc_sum {D : Data} {t : ℕ} {ι : Type*} (s : Finset ι) (f : ι → E (D.m t))
    (hf : ∀ i ∈ s, f i ∈ Xc D t) : ∑ i ∈ s, f i ∈ Xc D t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Xc_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Xc_add (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma Xc_isClosed (D : Data) (t : ℕ) : IsClosed (Xc D t) := by
  have : Xc D t = ⋂ i, {x : E (D.m t) | inner ℝ (D.C t i) x ≤ 0} := by
    ext x; simp [Xc]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

lemma Xc_convex (D : Data) (t : ℕ) : Convex ℝ (Xc D t) := by
  intro x hx y hy a c ha hc _
  exact Xc_add (Xc_smul hx ha) (Xc_smul hy hc)

lemma max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- A continuous, positively homogeneous right inverse of `A_{t,0}` with values in `X_t`. -/
lemma recourse_selector (D : Data) (hA1 : CompleteRecourse D) (t : ℕ)
    (ht : t ∈ Finset.Icc 2 D.T) :
    ∃ Z : E (D.n t) → E (D.m t), Continuous Z ∧ (∀ w, Z w ∈ Xc D t) ∧
      (∀ w, D.A₀ t (Z w) = w) ∧ ∃ C : NNReal, ∀ w, ‖Z w‖ ≤ C * ‖w‖ := by
  have hp : ∀ i : Fin (D.n t), ∃ z ∈ Xc D t, D.A₀ t z = EuclideanSpace.single i (1 : ℝ) :=
    fun i => hA1 t ht _
  have hm : ∀ i : Fin (D.n t), ∃ z ∈ Xc D t, D.A₀ t z = -EuclideanSpace.single i (1 : ℝ) :=
    fun i => hA1 t ht _
  choose zp hzp hAzp using hp
  choose zm hzm hAzm using hm
  refine ⟨fun w => ∑ i, (max (w i) 0 • zp i + max (-(w i)) 0 • zm i), ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro w
    exact Xc_sum _ _ fun i _ =>
      Xc_add (Xc_smul (hzp i) (le_max_right _ _)) (Xc_smul (hzm i) (le_max_right _ _))
  · intro w
    simp only [map_sum, map_add, map_smul, hAzp, hAzm, smul_neg]
    have : ∀ i : Fin (D.n t), max (w i) 0 • EuclideanSpace.single i (1 : ℝ) +
        -(max (-(w i)) 0 • EuclideanSpace.single i (1 : ℝ)) =
        w i • EuclideanSpace.single i (1 : ℝ) := by
      intro i
      rw [← sub_eq_add_neg, ← sub_smul, max_sub_max_neg]
    simp_rw [this]
    have := (EuclideanSpace.basisFun (Fin (D.n t)) ℝ).sum_repr w
    simpa using this
  · refine ⟨∑ i, (‖zp i‖₊ + ‖zm i‖₊), fun w => ?_⟩
    calc ‖∑ i, (max (w i) 0 • zp i + max (-(w i)) 0 • zm i)‖
        ≤ ∑ i, ‖max (w i) 0 • zp i + max (-(w i)) 0 • zm i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖w‖ * (‖zp i‖ + ‖zm i‖) := by
          gcongr with i
          have hwi : |w i| ≤ ‖w‖ := by
            have := PiLp.norm_apply_le w i
            simpa [Real.norm_eq_abs] using this
          have h1 : max (w i) 0 ≤ ‖w‖ := max_le ((le_abs_self _).trans hwi) (norm_nonneg _)
          have h2 : max (-(w i)) 0 ≤ ‖w‖ :=
            max_le ((neg_le_abs _).trans hwi) (norm_nonneg _)
          calc _ ≤ ‖max (w i) 0 • zp i‖ + ‖max (-(w i)) 0 • zm i‖ := norm_add_le _ _
            _ = max (w i) 0 * ‖zp i‖ + max (-(w i)) 0 * ‖zm i‖ := by
                rw [norm_smul, norm_smul, Real.norm_of_nonneg (le_max_right _ _),
                  Real.norm_of_nonneg (le_max_right _ _)]
            _ ≤ ‖w‖ * ‖zp i‖ + ‖w‖ * ‖zm i‖ := by gcongr
            _ = _ := by ring
      _ = (↑(∑ i, (‖zp i‖₊ + ‖zm i‖₊)) : ℝ) * ‖w‖ := by
          rw [← Finset.mul_sum, mul_comm]; push_cast; rfl

end MultistageStab.Value.SolAux


open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value.SolAux
open MultistageStab.Value

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sigmaGen_le {d T : ℕ} {ξ : ℕ → Ω → E d} (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable (ξ t))
    {t : ℕ} (ht : t ≤ T) : sigmaGen ξ t ≤ mΩ := by
  refine iSup₂_le fun τ hτ => ?_
  have hτ' : τ ∈ Finset.Icc 1 T := by
    simp only [Finset.mem_Icc] at hτ ⊢; omega
  exact (hξ τ hτ').comap_le

lemma sigmaGen_mono {d : ℕ} (ξ : ℕ → Ω → E d) {s t : ℕ} (hst : s ≤ t) :
    sigmaGen ξ s ≤ sigmaGen ξ t := by
  refine iSup₂_le fun τ hτ => ?_
  have hτ' : τ ∈ Finset.Icc 1 t := by
    simp only [Finset.mem_Icc] at hτ ⊢; omega
  exact le_iSup₂ (f := fun τ (_ : τ ∈ Finset.Icc 1 t) =>
    MeasurableSpace.comap (ξ τ) inferInstance) τ hτ'

lemma measurable_sigmaGen {d : ℕ} (ξ : ℕ → Ω → E d) {t : ℕ} (ht : 1 ≤ t) :
    Measurable[sigmaGen ξ t] (ξ t) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂ (f := fun τ (_ : τ ∈ Finset.Icc 1 t) =>
    MeasurableSpace.comap (ξ τ) inferInstance) t (by simp [ht])

lemma stronglyMeasurable_sigmaGen {d : ℕ} (ξ : ℕ → Ω → E d) {t : ℕ} (ht : 1 ≤ t) :
    StronglyMeasurable[sigmaGen ξ t] (ξ t) :=
  (measurable_sigmaGen ξ ht).stronglyMeasurable

/-! ## Pattern-dependent exponents -/

/-- The Hölder-conjugate exponent used for the cost vectors. -/
def q : Pattern → ℝ≥0∞
  | .costs => 1
  | .rhs => ⊤
  | .both => 2

lemma one_le_r (pat : Pattern) : 1 ≤ r pat := by cases pat <;> simp [r]
lemma one_le_r' (pat : Pattern) : 1 ≤ r' pat := by cases pat <;> simp [r']
lemma one_le_q (pat : Pattern) : 1 ≤ q pat := by cases pat <;> simp [q]

instance holder_q_r' (pat : Pattern) : ENNReal.HolderTriple (q pat) (r' pat) 1 := by
  cases pat
  · simp only [q, r']; infer_instance
  · simp only [q, r']; infer_instance
  · simp only [q, r']
    constructor
    norm_num [ENNReal.inv_two_add_inv_two]

variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma eLpNorm_const_le' {F : Type*} [NormedAddCommGroup F] (c : F) (p : ℝ≥0∞) :
    eLpNorm (fun _ : Ω => c) p P ≤ ‖c‖₊ := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [eLpNorm_const _ hp (NeZero.ne P)]
    simp

lemma memLp_h (D : Data) (pat : Pattern) (hpat : pat.Holds D) (t : ℕ) {ξ : Ω → E D.d}
    (hξ : MemLp ξ (r pat) P) : MemLp (fun ω => h D t (ξ ω)) (r' pat) P := by
  cases pat
  · have : D.H t = 0 := hpat t
    simp only [h, this, ContinuousLinearMap.zero_apply, add_zero]
    exact memLp_const _
  · change MemLp ξ 1 P at hξ
    change MemLp _ 1 P
    exact (memLp_const (D.h₀ t)).add ((D.H t).comp_memLp' hξ)
  · change MemLp ξ 2 P at hξ
    change MemLp _ 2 P
    exact (memLp_const (D.h₀ t)).add ((D.H t).comp_memLp' hξ)

lemma memLp_b (D : Data) (pat : Pattern) (hpat : pat.Holds D) (t : ℕ) {ξ : Ω → E D.d}
    (hξ : MemLp ξ (r pat) P) : MemLp (fun ω => b D t (ξ ω)) (q pat) P := by
  cases pat
  · change MemLp ξ 1 P at hξ
    change MemLp _ 1 P
    exact (memLp_const (D.b₀ t)).add ((D.B t).comp_memLp' hξ)
  · have : D.B t = 0 := hpat t
    simp only [b, this, ContinuousLinearMap.zero_apply, add_zero]
    exact memLp_const _
  · change MemLp ξ 2 P at hξ
    change MemLp _ 2 P
    exact (memLp_const (D.b₀ t)).add ((D.B t).comp_memLp' hξ)

lemma eLpNorm_clm_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) (f : Ω → F) (p : ℝ≥0∞) :
    eLpNorm (fun ω => L (f ω)) p P ≤ ‖L‖₊ * eLpNorm f p P := by
  have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := P) (p := p) (f := fun ω => L (f ω))
    (g := f) (c := ‖L‖₊) (Filter.Eventually.of_forall fun ω => L.le_opNNNorm (f ω))
  simpa [ENNReal.smul_def] using this

lemma eLpNorm_H_le (D : Data) (pat : Pattern) (hpat : pat.Holds D) (t : ℕ) (Δ : Ω → E D.d) :
    eLpNorm (fun ω => D.H t (Δ ω)) (r' pat) P ≤ ‖D.H t‖₊ * eLpNorm Δ (r pat) P := by
  cases pat
  · have : D.H t = 0 := hpat t
    simp [this]
  · exact eLpNorm_clm_le P _ _ _
  · exact eLpNorm_clm_le P _ _ _

lemma eLpNorm_B_le (D : Data) (pat : Pattern) (hpat : pat.Holds D) (t : ℕ) (Δ : Ω → E D.d) :
    eLpNorm (fun ω => D.B t (Δ ω)) (q pat) P ≤ ‖D.B t‖₊ * eLpNorm Δ (r pat) P := by
  cases pat
  · exact eLpNorm_clm_le P _ _ _
  · have : D.B t = 0 := hpat t
    simp [this]
  · exact eLpNorm_clm_le P _ _ _

lemma eLpNorm_b_le (D : Data) (pat : Pattern) (hpat : pat.Holds D) (t : ℕ) {ξ : Ω → E D.d}
    (hξ : AEStronglyMeasurable ξ P) :
    eLpNorm (fun ω => b D t (ξ ω)) (q pat) P ≤ ‖D.b₀ t‖₊ + ‖D.B t‖₊ * eLpNorm ξ (r pat) P := by
  have hsplit : (fun ω => b D t (ξ ω)) = (fun _ => D.b₀ t) + (fun ω => D.B t (ξ ω)) := by
    funext ω; simp [b]
  rw [hsplit]
  refine (eLpNorm_add_le aestronglyMeasurable_const ((D.B t).continuous.comp_aestronglyMeasurable hξ)
    (one_le_q pat)).trans ?_
  gcongr
  · exact eLpNorm_const_le' P _ _
  · exact eLpNorm_B_le P D pat hpat t ξ

end MultistageStab.Value.SolAux


open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value.SolAux
open MultistageStab.Value

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The recursive construction of the adapted policy `x̃` from `x̄` (proof of Theorem 2.1). -/
noncomputable def build (P : Measure Ω) (D : Data) (ξb : ℕ → Ω → E D.d) (xa : Policy D Ω)
    (Z : (t : ℕ) → E (D.n t) → E (D.m t)) : (t : ℕ) → Ω → E (D.m t)
  | 0 => xa 0
  | 1 => xa 1
  | (s + 2) => fun ω => P[xa (s + 2) | sigmaGen ξb (s + 2)] ω +
      Z (s + 2) (h D (s + 2) (ξb (s + 2) ω) - D.A₁ (s + 2) (build P D ξb xa Z (s + 1) ω) -
        D.A₀ (s + 2) (P[xa (s + 2) | sigmaGen ξb (s + 2)] ω))

/-- The residual whose image under `Z` corrects `E[x̄_t | F̃_t]`. -/
noncomputable def res (P : Measure Ω) (D : Data) (ξb : ℕ → Ω → E D.d) (xa : Policy D Ω)
    (Z : (t : ℕ) → E (D.n t) → E (D.m t)) (s : ℕ) : Ω → E (D.n (s + 2)) := fun ω =>
  h D (s + 2) (ξb (s + 2) ω) - D.A₁ (s + 2) (build P D ξb xa Z (s + 1) ω) -
    D.A₀ (s + 2) (P[xa (s + 2) | sigmaGen ξb (s + 2)] ω)

lemma build_one (P : Measure Ω) (D : Data) (ξb : ℕ → Ω → E D.d) (xa : Policy D Ω)
    (Z : (t : ℕ) → E (D.n t) → E (D.m t)) : build P D ξb xa Z 1 = xa 1 := rfl

lemma build_ss (P : Measure Ω) (D : Data) (ξb : ℕ → Ω → E D.d) (xa : Policy D Ω)
    (Z : (t : ℕ) → E (D.n t) → E (D.m t)) (s : ℕ) :
    build P D ξb xa Z (s + 2) = fun ω => P[xa (s + 2) | sigmaGen ξb (s + 2)] ω +
      Z (s + 2) (res P D ξb xa Z s ω) := rfl

/-- Properties of the selector `Z`. -/
structure SelProps (D : Data) (Z : (t : ℕ) → E (D.n t) → E (D.m t)) (C : ℕ → NNReal) : Prop where
  cont : ∀ t, Continuous (Z t)
  mem : ∀ t ∈ Finset.Icc 2 D.T, ∀ w, Z t w ∈ Xc D t
  inv : ∀ t ∈ Finset.Icc 2 D.T, ∀ w, D.A₀ t (Z t w) = w
  bound : ∀ t, ∀ w, ‖Z t w‖ ≤ C t * ‖w‖

lemma exists_sel (D : Data) (hA1 : CompleteRecourse D) :
    ∃ Z : (t : ℕ) → E (D.n t) → E (D.m t), ∃ C : ℕ → NNReal, SelProps D Z C := by
  classical
  have := fun t => recourse_selector D hA1 t
  refine ⟨fun t => if ht : t ∈ Finset.Icc 2 D.T then (this t ht).choose else 0,
    fun t => if ht : t ∈ Finset.Icc 2 D.T then (this t ht).choose_spec.2.2.2.choose else 0,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro t
    by_cases ht : t ∈ Finset.Icc 2 D.T
    · simpa [ht] using (this t ht).choose_spec.1
    · simp only [ht, dite_false]; exact continuous_const
  · intro t ht w
    simpa [ht] using (this t ht).choose_spec.2.1 w
  · intro t ht w
    simpa [ht] using (this t ht).choose_spec.2.2.1 w
  · intro t w
    by_cases ht : t ∈ Finset.Icc 2 D.T
    · simpa [ht] using (this t ht).choose_spec.2.2.2.choose_spec w
    · simp [ht]

variable (P : Measure Ω) [IsProbabilityMeasure P]

section
variable {D : Data} {pat : Pattern} (hpat : pat.Holds D)
  {ξa ξb : ℕ → Ω → E D.d} (hξa : Admissible P D pat ξa) (hξb : Admissible P D pat ξb)
  {xa : Policy D Ω} (hxa : xa ∈ feasible P D pat ξa)
  {Z : (t : ℕ) → E (D.n t) → E (D.m t)} {C : ℕ → NNReal} (hZ : SelProps D Z C)
include hpat hξa hξb hxa hZ

lemma build_props (s : ℕ) (hs : s + 1 ≤ D.T) :
    StronglyMeasurable[sigmaGen ξb (s + 1)] (build P D ξb xa Z (s + 1)) ∧
      MemLp (build P D ξb xa Z (s + 1)) (r' pat) P := by
  induction s with
  | zero =>
    obtain ⟨c, -, hc⟩ := hxa.1
    have : build P D ξb xa Z 1 = fun _ => c := by funext ω; exact hc ω
    refine ⟨by rw [this]; exact stronglyMeasurable_const, ?_⟩
    exact hxa.2.2 1 (by simp; omega)
  | succ s ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hle : sigmaGen ξb (s + 2) ≤ mΩ := sigmaGen_le hξb.1 hs
    have hxm : MemLp (xa (s + 2)) (r' pat) P := hxa.2.2 (s + 2) (by simp; omega)
    have hcm : MemLp (P[xa (s + 2) | sigmaGen ξb (s + 2)]) (r' pat) P :=
      hxm.condExp (one_le_r' pat)
    have hξm : MemLp (ξb (s + 2)) (r pat) P := hξb.2.1 (s + 2) (by simp; omega)
    have hres_sm : StronglyMeasurable[sigmaGen ξb (s + 2)] (res P D ξb xa Z s) := by
      unfold res
      refine StronglyMeasurable.sub (StronglyMeasurable.sub ?_ ?_) ?_
      · exact (show Continuous (h D (s + 2)) by unfold h; fun_prop).comp_stronglyMeasurable
          (stronglyMeasurable_sigmaGen ξb (by omega))
      · exact (D.A₁ (s + 2)).continuous.comp_stronglyMeasurable
          (ih1.mono (sigmaGen_mono ξb (by omega)))
      · exact (D.A₀ (s + 2)).continuous.comp_stronglyMeasurable stronglyMeasurable_condExp
    have hres_m : MemLp (res P D ξb xa Z s) (r' pat) P := by
      unfold res
      exact ((memLp_h P D pat hpat (s + 2) hξm).sub ((D.A₁ (s + 2)).comp_memLp' ih2)).sub
        ((D.A₀ (s + 2)).comp_memLp' hcm)
    refine ⟨?_, ?_⟩
    · show StronglyMeasurable[sigmaGen ξb (s + 2)] (build P D ξb xa Z (s + 2))
      rw [build_ss]
      exact stronglyMeasurable_condExp.add ((hZ.cont _).comp_stronglyMeasurable hres_sm)
    · show MemLp (build P D ξb xa Z (s + 2)) (r' pat) P
      rw [build_ss]
      refine hcm.add (hres_m.of_le_mul (c := C (s + 2))
        ((hZ.cont _).comp_aestronglyMeasurable hres_m.1) ?_)
      exact Filter.Eventually.of_forall fun ω => hZ.bound _ _

lemma build_feasible : build P D ξb xa Z ∈ feasible P D pat ξb := by
  refine ⟨hxa.1, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by simp at ht; omega⟩
    have hs : s + 2 ≤ D.T := by simp at ht; omega
    have hle : sigmaGen ξb (s + 2) ≤ mΩ := sigmaGen_le hξb.1 hs
    obtain ⟨hsm, -⟩ := build_props P hpat hξa hξb hxa hZ (s + 1) hs
    refine ⟨hsm, ?_⟩
    have hxm : MemLp (xa (s + 2)) (r' pat) P := hxa.2.2 (s + 2) (by simp; omega)
    have hmem := Convex.condExp_mem (m := sigmaGen ξb (s + 2)) (μ := P) hle
      (hxm.integrable (one_le_r' pat)) (Xc_isClosed D (s + 2)) (Xc_convex D (s + 2))
      ((hxa.2.1 (s + 2) ht).2.mono fun ω hω => hω.1)
    filter_upwards [hmem] with ω hω
    rw [build_ss]
    refine ⟨Xc_add hω (hZ.mem _ ht _), ?_⟩
    show D.A₀ (s + 2) _ + D.A₁ (s + 2) (build P D ξb xa Z (s + 1) ω) = _
    rw [map_add, hZ.inv _ ht]
    unfold res
    abel
  · intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by simp at ht; omega⟩
    exact (build_props P hpat hξa hξb hxa hZ s (by simp at ht; omega)).2

end

end MultistageStab.Value.SolAux


open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value.SolAux
open MultistageStab.Value

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma eLpNorm_stage_le_inputDist (P : Measure Ω) (D : Data) (pat : Pattern)
    (ξa ξb : ℕ → Ω → E D.d) {t : ℕ} (ht : t ∈ Finset.Icc 1 D.T) :
    eLpNorm (ξb t - ξa t) (r pat) P ≤ inputDist P D pat ξa ξb := by
  unfold inputDist
  refine eLpNorm_mono fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Pi.sub_apply, norm_sub_rev]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun τ => ‖ξa τ ω - ξb τ ω‖ ^ 2)
    (fun τ _ => by positivity) ht

lemma inputDist_comm (P : Measure Ω) (D : Data) (pat : Pattern) (ξa ξb : ℕ → Ω → E D.d) :
    inputDist P D pat ξa ξb = inputDist P D pat ξb ξa := by
  unfold inputDist
  congr 1
  funext ω
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [norm_sub_rev]

/-- The error `x̃_t − E[x̄_t | F̃_t]`. -/
noncomputable def wfun (P : Measure Ω) (D : Data) (ξb : ℕ → Ω → E D.d) (xa : Policy D Ω)
    (Z : (t : ℕ) → E (D.n t) → E (D.m t)) (t : ℕ) : Ω → E (D.m t) :=
  build P D ξb xa Z t - P[xa t | sigmaGen ξb t]

/-- The recursive constants. -/
noncomputable def Kc (D : Data) (C : ℕ → NNReal) : ℕ → NNReal
  | 0 => 0
  | 1 => 0
  | (s + 2) => C (s + 2) * (‖D.H (s + 2)‖₊ + ‖D.A₁ (s + 2)‖₊ * (Kc D C (s + 1) + 1))

variable (P : Measure Ω) [IsProbabilityMeasure P]

section
variable {D : Data} {pat : Pattern} (hpat : pat.Holds D)
  {ξa ξb : ℕ → Ω → E D.d} (hξa : Admissible P D pat ξa) (hξb : Admissible P D pat ξb)
  {xa : Policy D Ω} (hxa : xa ∈ feasible P D pat ξa)
  {Z : (t : ℕ) → E (D.n t) → E (D.m t)} {C : ℕ → NNReal} (hZ : SelProps D Z C)
include hpat hξa hξb hxa hZ

omit hpat hZ in
lemma condExp_stage_one (hT : 1 ≤ D.T) :
    P[xa 1 | sigmaGen ξb 1] =ᵐ[P] xa 1 := by
  obtain ⟨c, -, hc⟩ := hxa.1
  have : xa 1 = fun _ => c := funext hc
  rw [this, condExp_const (sigmaGen_le hξb.1 hT)]

omit hpat hZ in
lemma dterm_le {u : ℕ} (hu : u ∈ Finset.Icc 1 (D.T - 1)) :
    eLpNorm (xa u - P[xa u | sigmaGen ξb u]) (r' pat) P ≤
      ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xa τ - P[xa τ | sigmaGen ξb τ]) (r' pat) P := by
  by_cases h1 : u = 1
  · subst h1
    have hT : 1 ≤ D.T := by simp at hu; omega
    have : xa 1 - P[xa 1 | sigmaGen ξb 1] =ᵐ[P] 0 := by
      filter_upwards [condExp_stage_one P hξa hξb hxa hT] with ω hω
      simp [hω]
    rw [eLpNorm_congr_ae this, eLpNorm_zero]
    exact zero_le
  · exact Finset.single_le_sum (f := fun τ => eLpNorm (xa τ - P[xa τ | sigmaGen ξb τ]) (r' pat) P)
      (fun _ _ => zero_le) (by simp at hu ⊢; omega)

omit hpat hZ in
lemma w_one (hT : 1 ≤ D.T) : eLpNorm (wfun P D ξb xa Z 1) (r' pat) P = 0 := by
  have : wfun P D ξb xa Z 1 =ᵐ[P] 0 := by
    filter_upwards [condExp_stage_one P hξa hξb hxa hT] with ω hω
    simp [wfun, build_one, hω]
  rw [eLpNorm_congr_ae this, eLpNorm_zero]

lemma w_step (s : ℕ) (hs : s + 2 ≤ D.T) :
    eLpNorm (wfun P D ξb xa Z (s + 2)) (r' pat) P ≤
      C (s + 2) * (‖D.H (s + 2)‖₊ * inputDist P D pat ξa ξb +
        ‖D.A₁ (s + 2)‖₊ * (eLpNorm (wfun P D ξb xa Z (s + 1)) (r' pat) P +
          ∑ τ ∈ Finset.Icc 2 (D.T - 1),
            eLpNorm (xa τ - P[xa τ | sigmaGen ξb τ]) (r' pat) P)) := by
  have hp := one_le_r' pat
  have hle : sigmaGen ξb (s + 2) ≤ mΩ := sigmaGen_le hξb.1 hs
  have ht : s + 2 ∈ Finset.Icc 2 D.T := by simp; omega
  have hxm : MemLp (xa (s + 2)) (r' pat) P := hxa.2.2 (s + 2) (by simp; omega)
  have hxm1 : MemLp (xa (s + 1)) (r' pat) P := hxa.2.2 (s + 1) (by simp; omega)
  have hξbm : MemLp (ξb (s + 2)) (r pat) P := hξb.2.1 (s + 2) (by simp; omega)
  have hξam : MemLp (ξa (s + 2)) (r pat) P := hξa.2.1 (s + 2) (by simp; omega)
  obtain ⟨hb1s, hb1m⟩ := build_props P hpat hξa hξb hxa hZ s (by omega)
  -- step 1: `w = Z(res)`
  have hw : wfun P D ξb xa Z (s + 2) = fun ω => Z (s + 2) (res P D ξb xa Z s ω) := by
    funext ω; simp [wfun, build_ss]
  have h1 : eLpNorm (wfun P D ξb xa Z (s + 2)) (r' pat) P ≤
      C (s + 2) * eLpNorm (res P D ξb xa Z s) (r' pat) P := by
    rw [hw]
    have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := P) (p := r' pat)
      (f := fun ω => Z (s + 2) (res P D ξb xa Z s ω)) (g := res P D ξb xa Z s) (c := C (s + 2))
      (Filter.Eventually.of_forall fun ω => by
        have := hZ.bound (s + 2) (res P D ξb xa Z s ω)
        rw [← NNReal.coe_le_coe]; push_cast; exact this)
    simpa [ENNReal.smul_def] using this
  -- step 2: `res = E[F | G]`
  set g : Ω → E (D.n (s + 2)) := fun ω =>
    h D (s + 2) (ξb (s + 2) ω) - D.A₁ (s + 2) (build P D ξb xa Z (s + 1) ω) with hg
  have hg_sm : StronglyMeasurable[sigmaGen ξb (s + 2)] g := by
    refine StronglyMeasurable.sub ?_ ?_
    · exact (show Continuous (h D (s + 2)) by unfold h; fun_prop).comp_stronglyMeasurable
        (stronglyMeasurable_sigmaGen ξb (by omega))
    · exact (D.A₁ (s + 2)).continuous.comp_stronglyMeasurable
        (hb1s.mono (sigmaGen_mono ξb (by omega)))
  have hg_m : MemLp g (r' pat) P :=
    (memLp_h P D pat hpat (s + 2) hξbm).sub ((D.A₁ (s + 2)).comp_memLp' hb1m)
  have hA0m : MemLp (fun ω => D.A₀ (s + 2) (xa (s + 2) ω)) (r' pat) P :=
    (D.A₀ (s + 2)).comp_memLp' hxm
  have hres : res P D ξb xa Z s =ᵐ[P]
      P[fun ω => g ω - D.A₀ (s + 2) (xa (s + 2) ω) | sigmaGen ξb (s + 2)] := by
    have e1 := condExp_sub (m := sigmaGen ξb (s + 2)) (μ := P) (hg_m.integrable hp)
      (hA0m.integrable hp)
    have e2 : P[g | sigmaGen ξb (s + 2)] = g :=
      condExp_of_stronglyMeasurable hle hg_sm (hg_m.integrable hp)
    have e3 := (D.A₀ (s + 2)).comp_condExp_comm (m := sigmaGen ξb (s + 2)) (μ := P)
      (hxm.integrable hp)
    filter_upwards [e1, e3] with ω h1 h3
    have h1' : P[fun ω => g ω - D.A₀ (s + 2) (xa (s + 2) ω) | sigmaGen ξb (s + 2)] ω =
        P[g | sigmaGen ξb (s + 2)] ω - P[fun ω => D.A₀ (s + 2) (xa (s + 2) ω) |
          sigmaGen ξb (s + 2)] ω := by
      rw [← Pi.sub_apply, ← h1]; rfl
    rw [h1', e2]
    simp only [Function.comp_def] at h3
    rw [← h3]
    simp [res, hg]
  -- step 3: `F = HΔ − A₁(x̃_{t-1} − x̄_{t-1})` a.e.
  have hcons : ∀ᵐ ω ∂P, D.A₀ (s + 2) (xa (s + 2) ω) + D.A₁ (s + 2) (xa (s + 1) ω) =
      h D (s + 2) (ξa (s + 2) ω) := (hxa.2.1 (s + 2) ht).2.mono fun ω hω => hω.2
  have hF : (fun ω => g ω - D.A₀ (s + 2) (xa (s + 2) ω)) =ᵐ[P]
      (fun ω => D.H (s + 2) ((ξb (s + 2) - ξa (s + 2)) ω)) -
        (fun ω => D.A₁ (s + 2) ((build P D ξb xa Z (s + 1) - xa (s + 1)) ω)) := by
    filter_upwards [hcons] with ω hω
    have : D.A₀ (s + 2) (xa (s + 2) ω) =
        h D (s + 2) (ξa (s + 2) ω) - D.A₁ (s + 2) (xa (s + 1) ω) := by
      rw [← hω]; abel
    simp only [hg, this, Pi.sub_apply, map_sub, h]
    abel
  have h2 : eLpNorm (res P D ξb xa Z s) (r' pat) P ≤
      ‖D.H (s + 2)‖₊ * inputDist P D pat ξa ξb +
        ‖D.A₁ (s + 2)‖₊ * eLpNorm (build P D ξb xa Z (s + 1) - xa (s + 1)) (r' pat) P := by
    rw [eLpNorm_congr_ae hres]
    refine (eLpNorm_condExp_le_eLpNorm _ hp).trans ?_
    rw [eLpNorm_congr_ae hF]
    refine (eLpNorm_sub_le ((D.H (s + 2)).continuous.comp_aestronglyMeasurable
      (hξbm.1.sub hξam.1)) ((D.A₁ (s + 2)).continuous.comp_aestronglyMeasurable
      (hb1m.1.sub hxm1.1)) hp).trans ?_
    gcongr
    · refine (eLpNorm_H_le P D pat hpat (s + 2) _).trans ?_
      gcongr
      exact eLpNorm_stage_le_inputDist P D pat ξa ξb (by simp; omega)
    · exact eLpNorm_clm_le P _ _ _
  -- step 4: `x̃_{t-1} − x̄_{t-1} = w_{t-1} + (E[x̄_{t-1}|F̃_{t-1}] − x̄_{t-1})`
  have h3 : eLpNorm (build P D ξb xa Z (s + 1) - xa (s + 1)) (r' pat) P ≤
      eLpNorm (wfun P D ξb xa Z (s + 1)) (r' pat) P +
        ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xa τ - P[xa τ | sigmaGen ξb τ]) (r' pat) P := by
    have hsplit : build P D ξb xa Z (s + 1) - xa (s + 1) =
        wfun P D ξb xa Z (s + 1) + (P[xa (s + 1) | sigmaGen ξb (s + 1)] - xa (s + 1)) := by
      simp [wfun]
    rw [hsplit]
    refine (eLpNorm_add_le (hb1m.1.sub integrable_condExp.1)
      (integrable_condExp.1.sub hxm1.1) hp).trans ?_
    have hu : s + 1 ∈ Finset.Icc 1 (D.T - 1) := by simp only [Finset.mem_Icc]; omega
    refine add_le_add le_rfl ?_
    rw [eLpNorm_sub_comm]
    exact dterm_le P hξa hξb hxa (u := s + 1) hu
  calc eLpNorm (wfun P D ξb xa Z (s + 2)) (r' pat) P
      ≤ C (s + 2) * eLpNorm (res P D ξb xa Z s) (r' pat) P := h1
    _ ≤ _ := by
      gcongr
      refine h2.trans ?_
      gcongr

lemma w_bound (s : ℕ) (hs : s + 1 ≤ D.T) :
    eLpNorm (wfun P D ξb xa Z (s + 1)) (r' pat) P ≤
      Kc D C (s + 1) * (inputDist P D pat ξa ξb +
        ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xa τ - P[xa τ | sigmaGen ξb τ]) (r' pat) P) := by
  induction s with
  | zero => rw [w_one P hξa hξb hxa (by omega)]; exact zero_le
  | succ s ih =>
    refine (w_step P hpat hξa hξb hxa hZ s hs).trans ?_
    have ih' := ih (by omega)
    set I := inputDist P D pat ξa ξb
    set S := ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xa τ - P[xa τ | sigmaGen ξb τ]) (r' pat) P
    show _ ≤ ((C (s + 2) * (‖D.H (s + 2)‖₊ + ‖D.A₁ (s + 2)‖₊ * (Kc D C (s + 1) + 1)) : NNReal) :
      ℝ≥0∞) * (I + S)
    calc (C (s + 2) : ℝ≥0∞) * (‖D.H (s + 2)‖₊ * I + ‖D.A₁ (s + 2)‖₊ *
          (eLpNorm (wfun P D ξb xa Z (s + 1)) (r' pat) P + S))
        ≤ (C (s + 2) : ℝ≥0∞) * (‖D.H (s + 2)‖₊ * (I + S) + ‖D.A₁ (s + 2)‖₊ *
          (Kc D C (s + 1) * (I + S) + (I + S))) := by
          gcongr
          · exact le_self_add
          · exact le_add_self
      _ = _ := by push_cast; ring

end

end MultistageStab.Value.SolAux


open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value.SolAux
open MultistageStab.Value

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma integrable_inner {k : ℕ} (pat : Pattern) {f g : Ω → E k} (hf : MemLp f (q pat) P)
    (hg : MemLp g (r' pat) P) : Integrable (fun ω => inner ℝ (f ω) (g ω)) P := by
  rw [← memLp_one_iff_integrable]
  exact MemLp.of_bilin (fun u v => inner ℝ u v) 1 hf hg (hf.1.inner hg.1)
    (Filter.Eventually.of_forall fun ω => by
      rw [← NNReal.coe_le_coe]; push_cast
      simpa using norm_inner_le_norm (𝕜 := ℝ) (f ω) (g ω))

lemma ofReal_integral_inner_le {k : ℕ} (pat : Pattern) {f g : Ω → E k}
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P) :
    ENNReal.ofReal (∫ ω, inner ℝ (f ω) (g ω) ∂P) ≤ eLpNorm f (q pat) P * eLpNorm g (r' pat) P := by
  by_cases hi : Integrable (fun ω => inner ℝ (f ω) (g ω)) P
  · calc ENNReal.ofReal (∫ ω, inner ℝ (f ω) (g ω) ∂P)
        ≤ ENNReal.ofReal (∫ ω, ‖inner ℝ (f ω) (g ω)‖ ∂P) := by
          refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P)
              (fun ω => inner ℝ (f ω) (g ω))
      _ = eLpNorm (fun ω => inner ℝ (f ω) (g ω)) 1 P := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hi, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ (1 : NNReal) * eLpNorm f (q pat) P * eLpNorm g (r' pat) P :=
          eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hf hg (fun u v => inner ℝ u v) 1
            (Filter.Eventually.of_forall fun ω => by
              simpa using norm_inner_le_norm (𝕜 := ℝ) (f ω) (g ω))
      _ = _ := by simp
  · rw [integral_undef hi]; simp

/-- Pull-out property for the inner product. -/
lemma integral_inner_condExp {k : ℕ} {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {g f : Ω → E k}
    (hg : StronglyMeasurable[G] g) (hf : Integrable f P)
    (hgf : Integrable (fun ω => inner ℝ (g ω) (f ω)) P) :
    ∫ ω, inner ℝ (g ω) (f ω) ∂P = ∫ ω, inner ℝ (g ω) (P[f | G] ω) ∂P := by
  rw [← integral_condExp hG]
  refine integral_congr_ae ?_
  exact condExp_bilin_of_stronglyMeasurable_left (m := G) (μ := P) (innerSL ℝ) hg
    (hgf : Integrable (fun ω => innerSL ℝ (g ω) (f ω)) P) hf

lemma ofReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.ofReal_add_le).trans (add_le_add le_rfl ih)

section
variable {D : Data} {pat : Pattern} (hpat : pat.Holds D)
  {ξa ξb : ℕ → Ω → E D.d} (hξa : Admissible P D pat ξa) (hξb : Admissible P D pat ξb)
  {xa : Policy D Ω} (hxa : xa ∈ feasible P D pat ξa)
  {Z : (t : ℕ) → E (D.n t) → E (D.m t)} {C : ℕ → NNReal} (hZ : SelProps D Z C)
include hpat hξa hξb hxa hZ

lemma objective_diff :
    ENNReal.ofReal (objective P D ξb (build P D ξb xa Z) - objective P D ξa xa) ≤
      ∑ t ∈ Finset.Icc 1 D.T,
        (eLpNorm (fun ω => b D t (ξb t ω)) (q pat) P * eLpNorm (wfun P D ξb xa Z t) (r' pat) P +
          eLpNorm (fun ω => D.B t ((ξb t - ξa t) ω)) (q pat) P *
            eLpNorm (xa t) (r' pat) P) := by
  have hxb := build_feasible P hpat hξa hξb hxa hZ
  set xb := build P D ξb xa Z with hxb_def
  have hp := one_le_r' pat
  -- per-stage identity
  have key : ∀ t ∈ Finset.Icc 1 D.T,
      ∫ ω, inner ℝ (b D t (ξb t ω)) (xb t ω) ∂P - ∫ ω, inner ℝ (b D t (ξa t ω)) (xa t ω) ∂P =
        ∫ ω, inner ℝ (b D t (ξb t ω)) (wfun P D ξb xa Z t ω) ∂P +
          ∫ ω, inner ℝ (D.B t ((ξb t - ξa t) ω)) (xa t ω) ∂P := by
    intro t ht
    have hT : t ≤ D.T := (Finset.mem_Icc.1 ht).2
    have h1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    have hle : sigmaGen ξb t ≤ mΩ := sigmaGen_le hξb.1 hT
    have hbb := memLp_b P D pat hpat t (hξb.2.1 t ht)
    have hba := memLp_b P D pat hpat t (hξa.2.1 t ht)
    have hxat := hxa.2.2 t ht
    have hxbt := hxb.2.2 t ht
    have hcm : MemLp (P[xa t | sigmaGen ξb t]) (r' pat) P := hxat.condExp hp
    have hgsm : StronglyMeasurable[sigmaGen ξb t] (fun ω => b D t (ξb t ω)) :=
      (show Continuous (b D t) by unfold b; fun_prop).comp_stronglyMeasurable
        (stronglyMeasurable_sigmaGen ξb h1)
    have hpull := integral_inner_condExp P hle hgsm (hxat.integrable hp)
      (integrable_inner P pat hbb hxat)
    have hw : ∫ ω, inner ℝ (b D t (ξb t ω)) (wfun P D ξb xa Z t ω) ∂P =
        ∫ ω, inner ℝ (b D t (ξb t ω)) (xb t ω) ∂P -
          ∫ ω, inner ℝ (b D t (ξb t ω)) (P[xa t | sigmaGen ξb t] ω) ∂P := by
      rw [← integral_sub (integrable_inner P pat hbb hxbt) (integrable_inner P pat hbb hcm)]
      congr 1; funext ω
      simp [wfun, inner_sub_right, hxb_def]
    have hB : ∫ ω, inner ℝ (D.B t ((ξb t - ξa t) ω)) (xa t ω) ∂P =
        ∫ ω, inner ℝ (b D t (ξb t ω)) (xa t ω) ∂P -
          ∫ ω, inner ℝ (b D t (ξa t ω)) (xa t ω) ∂P := by
      rw [← integral_sub (integrable_inner P pat hbb hxat) (integrable_inner P pat hba hxat)]
      congr 1; funext ω
      simp only [b, Pi.sub_apply, map_sub, inner_sub_left, inner_add_left]; ring
    rw [hw, hB, hpull]
    ring
  have hint : ∀ (ξ : ℕ → Ω → E D.d) (x : Policy D Ω), Admissible P D pat ξ →
      x ∈ feasible P D pat ξ → ∀ t ∈ Finset.Icc 1 D.T,
        Integrable (fun ω => inner ℝ (b D t (ξ t ω)) (x t ω)) P := fun ξ x hξ hx t ht =>
    integrable_inner P pat (memLp_b P D pat hpat t (hξ.2.1 t ht)) (hx.2.2 t ht)
  unfold objective
  rw [integral_finsetSum _ (hint ξb xb hξb hxb), integral_finsetSum _ (hint ξa xa hξa hxa),
    ← Finset.sum_sub_distrib, Finset.sum_congr rfl key]
  refine (ofReal_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
  · exact ofReal_integral_inner_le P pat
      ((memLp_b P D pat hpat t (hξb.2.1 t ht)).1)
      ((hxb.2.2 t ht).1.sub integrable_condExp.1)
  · exact ofReal_integral_inner_le P pat
      ((D.B t).continuous.comp_aestronglyMeasurable
        ((hξb.2.1 t ht).1.sub (hξa.2.1 t ht).1))
      (hxa.2.2 t ht).1

end

end MultistageStab.Value.SolAux


open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value.SolAux
open MultistageStab.Value

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The one-sided estimate behind (12)–(13): from a feasible `x̄` for `ξa` we construct a feasible
`x̃` for `ξb` whose cost exceeds that of `x̄` by at most `L (‖ξa − ξb‖_r + Σ_t ‖x̄_t − E[x̄_t|F̃_t]‖)`. -/
lemma one_sided (D : Data) (pat : Pattern) (hpat : pat.Holds D) (hA1 : CompleteRecourse D)
    (R M : NNReal) : ∃ L : ℝ, 0 < L ∧
      ∀ ξa ξb : ℕ → Ω → E D.d, Admissible P D pat ξa → Admissible P D pat ξb →
      ∀ xa ∈ feasible P D pat ξa, (∀ t ∈ Finset.Icc 1 D.T, eLpNorm (xa t) (r' pat) P ≤ R) →
        (∀ t ∈ Finset.Icc 1 D.T, eLpNorm (ξb t) (r pat) P ≤ M) →
        ∃ xb ∈ feasible P D pat ξb,
          ENNReal.ofReal (objective P D ξb xb - objective P D ξa xa) ≤
            ENNReal.ofReal L * (inputDist P D pat ξa ξb +
              ∑ τ ∈ Finset.Icc 2 (D.T - 1),
                eLpNorm (xa τ - P[xa τ | sigmaGen ξb τ]) (r' pat) P) := by
  obtain ⟨Z, C, hZ⟩ := exists_sel D hA1
  set K : NNReal := ∑ t ∈ Finset.Icc 1 D.T,
    ((‖D.b₀ t‖₊ + ‖D.B t‖₊ * M) * Kc D C t + ‖D.B t‖₊ * R) with hK
  refine ⟨(K : ℝ) + 1, by positivity, fun ξa ξb hξa hξb xa hxa hxaR hξbM => ?_⟩
  refine ⟨build P D ξb xa Z, build_feasible P hpat hξa hξb hxa hZ, ?_⟩
  refine (objective_diff P hpat hξa hξb hxa hZ).trans ?_
  set I := inputDist P D pat ξa ξb
  set S := ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xa τ - P[xa τ | sigmaGen ξb τ]) (r' pat) P
  have hterm : ∀ t ∈ Finset.Icc 1 D.T,
      eLpNorm (fun ω => b D t (ξb t ω)) (q pat) P * eLpNorm (wfun P D ξb xa Z t) (r' pat) P +
        eLpNorm (fun ω => D.B t ((ξb t - ξa t) ω)) (q pat) P * eLpNorm (xa t) (r' pat) P ≤
      (((‖D.b₀ t‖₊ + ‖D.B t‖₊ * M) * Kc D C t + ‖D.B t‖₊ * R : NNReal) : ℝ≥0∞) * (I + S) := by
    intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by simp at ht; omega⟩
    have hs : s + 1 ≤ D.T := (Finset.mem_Icc.1 ht).2
    have e1 : eLpNorm (fun ω => b D (s + 1) (ξb (s + 1) ω)) (q pat) P ≤
        ((‖D.b₀ (s + 1)‖₊ + ‖D.B (s + 1)‖₊ * M : NNReal) : ℝ≥0∞) := by
      refine (eLpNorm_b_le P D pat hpat (s + 1) (hξb.2.1 (s + 1) ht).1).trans ?_
      push_cast
      gcongr
      exact hξbM _ ht
    have e2 := w_bound P hpat hξa hξb hxa hZ s hs
    have e3 : eLpNorm (fun ω => D.B (s + 1) ((ξb (s + 1) - ξa (s + 1)) ω)) (q pat) P ≤
        ‖D.B (s + 1)‖₊ * I :=
      (eLpNorm_B_le P D pat hpat (s + 1) _).trans
        (by gcongr; exact eLpNorm_stage_le_inputDist P D pat ξa ξb ht)
    have e4 := hxaR _ ht
    calc _ ≤ ((‖D.b₀ (s + 1)‖₊ + ‖D.B (s + 1)‖₊ * M : NNReal) : ℝ≥0∞) *
          (Kc D C (s + 1) * (I + S)) + ‖D.B (s + 1)‖₊ * I * R :=
          add_le_add (mul_le_mul' e1 e2) (mul_le_mul' e3 e4)
      _ ≤ ((‖D.b₀ (s + 1)‖₊ + ‖D.B (s + 1)‖₊ * M : NNReal) : ℝ≥0∞) *
          (Kc D C (s + 1) * (I + S)) + ‖D.B (s + 1)‖₊ * (I + S) * R := by
          gcongr
          exact le_self_add
      _ = _ := by push_cast; ring
  calc _ ≤ ∑ t ∈ Finset.Icc 1 D.T,
        (((‖D.b₀ t‖₊ + ‖D.B t‖₊ * M) * Kc D C t + ‖D.B t‖₊ * R : NNReal) : ℝ≥0∞) * (I + S) :=
        Finset.sum_le_sum hterm
    _ = (K : ℝ≥0∞) * (I + S) := by rw [← Finset.sum_mul, hK]; push_cast; rfl
    _ ≤ ENNReal.ofReal ((K : ℝ) + 1) * (I + S) := by
        gcongr
        rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_coe_nnreal]
        exact le_self_add

lemma inputDist_self (D : Data) (pat : Pattern) (ξ : ℕ → Ω → E D.d) :
    inputDist P D pat ξ ξ = 0 := by
  simp [inputDist]

lemma value_le_objective {D : Data} {pat : Pattern} {ξ : ℕ → Ω → E D.d} {x : Policy D Ω}
    (hx : x ∈ feasible P D pat ξ) : value P D pat ξ ≤ (objective P D ξ x : EReal) :=
  iInf₂_le (f := fun x (_ : x ∈ feasible P D pat ξ) => ((objective P D ξ x : ℝ) : EReal)) x hx

lemma value_toReal_le {D : Data} {pat : Pattern} {ξ : ℕ → Ω → E D.d} {x : Policy D Ω}
    (hx : x ∈ feasible P D pat ξ) (hbot : value P D pat ξ ≠ ⊥) :
    (value P D pat ξ).toReal ≤ objective P D ξ x := by
  have := EReal.toReal_le_toReal (value_le_objective P hx) hbot (EReal.coe_ne_top _)
  simpa using this

lemma exists_eps_opt {D : Data} {pat : Pattern} {ξ : ℕ → Ω → E D.d}
    (hbot : value P D pat ξ ≠ ⊥) (htop : value P D pat ξ ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ feasible P D pat ξ, objective P D ξ x ≤ (value P D pat ξ).toReal + ε := by
  have hlt : value P D pat ξ < (((value P D pat ξ).toReal + ε : ℝ) : EReal) := by
    conv_lhs => rw [← EReal.coe_toReal htop hbot]
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  unfold value at hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨x, hx⟩ := hlt
  rw [iInf_lt_iff] at hx
  obtain ⟨hxf, hx⟩ := hx
  exact ⟨x, hxf, (EReal.coe_lt_coe_iff.1 hx).le⟩

lemma ofReal_le_of_eps {a α : ℝ} (hα : 0 < α) {X : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ α → ENNReal.ofReal (a - ε) ≤ X) : ENNReal.ofReal a ≤ X := by
  by_cases hX : X = ⊤
  · simp [hX]
  rw [ENNReal.ofReal_le_iff_le_toReal hX]
  by_contra hcon
  push Not at hcon
  set ε := min α ((a - X.toReal) / 2)
  have hε : 0 < ε := lt_min hα (by linarith)
  have := (ENNReal.ofReal_le_iff_le_toReal hX).1 (h ε hε (min_le_left _ _))
  have : ε ≤ (a - X.toReal) / 2 := min_le_right _ _
  linarith

lemma eLpNorm_le_M (D : Data) (pat : Pattern) {ξ ξ' : ℕ → Ω → E D.d}
    (hξ : Admissible P D pat ξ) (hξ' : Admissible P D pat ξ') {δ : ℝ}
    (hd : inputDist P D pat ξ ξ' ≤ ENNReal.ofReal δ) :
    ∀ t ∈ Finset.Icc 1 D.T, eLpNorm (ξ' t) (r pat) P ≤
      ((∑ t ∈ Finset.Icc 1 D.T, (eLpNorm (ξ t) (r pat) P).toNNReal + δ.toNNReal : NNReal) :
        ℝ≥0∞) := by
  intro t ht
  have hsplit : ξ' t = ξ t + (ξ' t - ξ t) := by abel
  rw [hsplit]
  refine (eLpNorm_add_le (hξ.2.1 t ht).1 ((hξ'.2.1 t ht).1.sub (hξ.2.1 t ht).1)
    (one_le_r pat)).trans ?_
  push_cast
  gcongr
  · rw [← ENNReal.ofNNReal_finsetSum]
    refine le_trans ?_ (ENNReal.coe_le_coe.2 (Finset.single_le_sum
      (f := fun t => (eLpNorm (ξ t) (r pat) P).toNNReal) (fun _ _ => zero_le) ht))
    rw [ENNReal.coe_toNNReal (hξ.2.1 t ht).eLpNorm_ne_top]
  · refine (eLpNorm_stage_le_inputDist P D pat ξ ξ' ht).trans (hd.trans ?_)
    rw [ENNReal.ofReal]

end MultistageStab.Value.SolAux


open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value.SolAux
open MultistageStab.Value

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

section
variable (D : Data) (pat : Pattern) (hpat : pat.Holds D) (ξ : ℕ → Ω → E D.d)
  (hA1 : CompleteRecourse D)
  (hv_bot : value P D pat ξ ≠ ⊥) (hv_top : value P D pat ξ ≠ ⊤)
  (α δ : ℝ) (R : NNReal) (hα : 0 < α)
  (hA2 : LevelBoundedWith P D pat ξ α δ R) (hA3 : Admissible P D pat ξ)

include hpat hA1 hA2 hA3 in
lemma fwd : ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ α →
    ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
      inputDist P D pat ξ ξ' ≤ ENNReal.ofReal δ → value P D pat ξ' ≠ ⊥ →
      ∀ xbar ∈ levelSet P D pat ξ ((value P D pat ξ).toReal + ε),
        ENNReal.ofReal ((value P D pat ξ').toReal - (value P D pat ξ).toReal - ε) ≤
          ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
            ∑ τ ∈ Finset.Icc 2 (D.T - 1),
              eLpNorm (xbar τ - P[xbar τ | sigmaGen ξ' τ]) (r' pat) P) := by
  obtain ⟨L, hL, hone⟩ := one_sided P D pat hpat hA1 R
    (∑ t ∈ Finset.Icc 1 D.T, (eLpNorm (ξ t) (r pat) P).toNNReal + δ.toNNReal)
  refine ⟨L, hL, fun ε hε hεα ξ' hξ' hd hv'bot xbar hxbar => ?_⟩
  have hR := (hA2 ξ hA3 (by rw [inputDist_self]; exact zero_le)).2 xbar
    ⟨hxbar.1, hxbar.2.trans (by linarith)⟩
  obtain ⟨xb, hxb, hbd⟩ := hone ξ ξ' hA3 hξ' xbar hxbar.1 hR (eLpNorm_le_M P D pat hA3 hξ' hd)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbd
  linarith [value_toReal_le P hxb hv'bot, hxbar.2]

include hpat hA1 hA2 hA3 hv_bot in
lemma bwd : ∃ L : ℝ, 0 < L ∧
    ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
      inputDist P D pat ξ ξ' ≤ ENNReal.ofReal δ →
      ∀ xtil ∈ levelSet P D pat ξ' ((value P D pat ξ).toReal + α),
        ENNReal.ofReal ((value P D pat ξ).toReal - objective P D ξ' xtil) ≤
          ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
            ∑ τ ∈ Finset.Icc 2 (D.T - 1),
              eLpNorm (xtil τ - P[xtil τ | sigmaGen ξ τ]) (r' pat) P) := by
  obtain ⟨L, hL, hone⟩ := one_sided P D pat hpat hA1 R
    (∑ t ∈ Finset.Icc 1 D.T, (eLpNorm (ξ t) (r pat) P).toNNReal + (0 : ℝ).toNNReal)
  refine ⟨L, hL, fun ξ' hξ' hd xtil hxtil => ?_⟩
  have hR := (hA2 ξ' hξ' hd).2 xtil hxtil
  obtain ⟨xb, hxb, hbd⟩ := hone ξ' ξ hξ' hA3 xtil hxtil.1 hR
    (eLpNorm_le_M P D pat hA3 hA3 (by rw [inputDist_self]; exact zero_le))
  rw [inputDist_comm] at hbd
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbd
  linarith [value_toReal_le P hxb hv_bot]

include hpat hA1 hA2 hA3 hv_bot hv_top hα in
lemma fwd_sup : ∃ L : ℝ, 0 < L ∧
    ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
      inputDist P D pat ξ ξ' ≤ ENNReal.ofReal δ →
      value P D pat ξ' ≠ ⊥ → value P D pat ξ' ≠ ⊤ →
      ENNReal.ofReal ((value P D pat ξ').toReal - (value P D pat ξ).toReal) ≤
        ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
          ∑ t ∈ Finset.Icc 2 (D.T - 1),
            ⨆ xbar ∈ levelSet P D pat ξ ((value P D pat ξ).toReal + α),
              eLpNorm (xbar t - P[xbar t | sigmaGen ξ' t]) (r' pat) P) := by
  obtain ⟨L, hL, hf⟩ := fwd P D pat hpat ξ hA1 α δ R hA2 hA3
  refine ⟨L, hL, fun ξ' hξ' hd hv'bot _ => ?_⟩
  refine ofReal_le_of_eps hα fun ε hε hεα => ?_
  obtain ⟨xbar, hxf, hxo⟩ := exists_eps_opt P hv_bot hv_top hε
  refine (hf ε hε hεα ξ' hξ' hd hv'bot xbar ⟨hxf, hxo⟩).trans ?_
  gcongr with t ht
  exact le_iSup₂ (f := fun x (_ : x ∈ levelSet P D pat ξ ((value P D pat ξ).toReal + α)) =>
    eLpNorm (x t - P[x t | sigmaGen ξ' t]) (r' pat) P) xbar ⟨hxf, hxo.trans (by linarith)⟩

include hpat hA1 hA2 hA3 hv_bot hv_top hα in
lemma bwd_sup : ∃ L : ℝ, 0 < L ∧
    ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
      inputDist P D pat ξ ξ' ≤ ENNReal.ofReal δ →
      value P D pat ξ' ≠ ⊥ → value P D pat ξ' ≠ ⊤ →
      ENNReal.ofReal ((value P D pat ξ).toReal - (value P D pat ξ').toReal) ≤
        ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
          ∑ t ∈ Finset.Icc 2 (D.T - 1),
            ⨆ xtil ∈ levelSet P D pat ξ' ((value P D pat ξ).toReal + α),
              eLpNorm (xtil t - P[xtil t | sigmaGen ξ t]) (r' pat) P) := by
  obtain ⟨L, hL, hb⟩ := bwd P D pat hpat ξ hA1 hv_bot α δ R hA2 hA3
  refine ⟨L, hL, fun ξ' hξ' hd hv'bot hv'top => ?_⟩
  by_cases hvv : (value P D pat ξ).toReal ≤ (value P D pat ξ').toReal
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact zero_le
  push Not at hvv
  refine ofReal_le_of_eps hα fun ε hε hεα => ?_
  obtain ⟨xtil, hxf, hxo⟩ := exists_eps_opt P hv'bot hv'top hε
  have hmem : xtil ∈ levelSet P D pat ξ' ((value P D pat ξ).toReal + α) :=
    ⟨hxf, hxo.trans (by linarith)⟩
  refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) ((hb ξ' hξ' hd xtil hmem).trans ?_)
  gcongr with t ht
  exact le_iSup₂ (f := fun x (_ : x ∈ levelSet P D pat ξ' ((value P D pat ξ).toReal + α)) =>
    eLpNorm (x t - P[x t | sigmaGen ξ t]) (r' pat) P) xtil hmem

end

lemma main (D : Data) (pat : Pattern) (hpat : pat.Holds D)
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D) (hA2 : A2 P D pat ξ)
    (hA3 : Admissible P D pat ξ) :
    ∃ L : ℝ, 0 < L ∧ ∃ α : ℝ, 0 < α ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
        inputDist P D pat ξ ξ' ≤ ENNReal.ofReal δ →
        value P D pat ξ' ≠ ⊥ → value P D pat ξ' ≠ ⊤ →
        ENNReal.ofReal |(value P D pat ξ).toReal - (value P D pat ξ').toReal| ≤
          ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
            ∑ t ∈ Finset.Icc 2 (D.T - 1), filtDist P D pat ξ ξ' α t) := by
  obtain ⟨hvb, hvt, α, hα, δ, hδ, R, hLB⟩ := hA2
  obtain ⟨L1, hL1, h1⟩ := fwd_sup P D pat hpat ξ hA1 hvb hvt α δ R hα hLB hA3
  obtain ⟨L2, hL2, h2⟩ := bwd_sup P D pat hpat ξ hA1 hvb hvt α δ R hα hLB hA3
  refine ⟨max L1 L2, lt_max_of_lt_left hL1, α, hα, δ, hδ, fun ξ' hξ' hd hb ht => ?_⟩
  rw [abs_eq_max_neg, ENNReal.ofReal_max, neg_sub]
  refine max_le ((h2 ξ' hξ' hd hb ht).trans ?_) ((h1 ξ' hξ' hd hb ht).trans ?_)
  · gcongr
    · exact le_max_right _ _
    · exact le_max_right _ _
  · gcongr
    · exact le_max_left _ _
    · exact le_max_left _ _

end MultistageStab.Value.SolAux


open MeasureTheory ProbabilityTheory MultistageStab.Value in
theorem solution (D : Data) (hpat : Pattern.both.Holds D)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D)
    (hv_bot : value P D .both ξ ≠ ⊥) (hv_top : value P D .both ξ ≠ ⊤)
    (α δ : ℝ) (R : NNReal) (hα : 0 < α) (hδ : 0 < δ)
    (hA2 : LevelBoundedWith P D .both ξ α δ R)
    (hA3 : Admissible P D .both ξ) (hX1 : Bornology.IsBounded (X1 D)) :
    ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ α →
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D .both ξ' →
        inputDist P D .both ξ ξ' < ENNReal.ofReal δ →
        value P D .both ξ' ≠ ⊥ → value P D .both ξ' ≠ ⊤ →
        ∀ xbar ∈ levelSet P D .both ξ ((value P D .both ξ).toReal + ε),
          ENNReal.ofReal ((value P D .both ξ').toReal - (value P D .both ξ).toReal - ε) ≤
            ENNReal.ofReal L * (inputDist P D .both ξ ξ' +
              ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xbar τ - P[xbar τ | sigmaGen ξ' τ]) 2 P) := by
  obtain ⟨L, hL, h⟩ := MultistageStab.Value.SolAux.fwd P D .both hpat ξ hA1 α δ R hA2 hA3
  exact ⟨L, hL, fun ε hε hεα ξ' hξ' hd hb _ xbar hx => h ε hε hεα ξ' hξ' hd.le hb xbar hx⟩
