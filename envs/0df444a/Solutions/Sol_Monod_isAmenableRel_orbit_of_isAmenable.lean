-- Prove2me | solution 1 for Monod.isAmenableRel_orbit_of_isAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-30T13:16:27.206452+00:00
-- url     : https://prove2.me/submissions/09e2edd7-1e20-47ee-aa1a-6738088011be

import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_Garrido_satisfiesFoelnerCondition_iff_isAmenable
import Theorems.Thm_Garrido_satisfiesFoelnerCondition_iff_hasFoelnerSequence
import Mathlib

section
/-!
# Orbit relations of countable amenable groups are amenable (Schmidt 1.6(1))

Route: a left Følner sequence `T n` of the countable group `Λ` gives the Følner averages
`avg (T n) f x = |T n|⁻¹ ∑_{g ∈ T n} f (x, g⁻¹ • x)`, bounded measurable functions on `X`.
After replacing `μ` by an equivalent finite measure, these are bounded in `L²(μ)`; their weak
limit along a fixed free ultrafilter on `ℕ` (Riesz representation) is `P f`.  Positivity,
linearity, unitality and the congruence property pass to the weak limit.  For a partial
transformation `φ`, `avg (T n) (f^φ) - (avg (T n) f)^φ → 0` pointwise by the Følner property
(no measurable choice of the group element is needed), hence in `L¹` by dominated
convergence; the change of variables `y = φ x` is handled through the Radon–Nikodym
derivative of the transported measure, which is absolutely continuous by non-singularity.
-/

set_option linter.unusedSectionVars false

namespace Monod.Dev.Rel

open MeasureTheory Filter Topology Set
open scoped ENNReal symmDiff Pointwise

/-- A fixed free ultrafilter on `ℕ`. -/
noncomputable abbrev UF : Filter ℕ := ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ)

lemma UF_le_atTop : UF ≤ atTop := hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le

/-! ### Weak ultralimits in a real Hilbert space -/

section WL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `v` is the weak limit of `a` along `UF`. -/
def IsWL (a : ℕ → E) (v : E) : Prop :=
  ∀ w : E, Tendsto (fun n => inner ℝ (a n) w) UF (𝓝 (inner ℝ v w))

lemma isWL_unique {a : ℕ → E} {v v' : E} (h : IsWL a v) (h' : IsWL a v') : v = v' :=
  ext_inner_right ℝ fun w => tendsto_nhds_unique (h w) (h' w)

lemma exists_ulim {s : ℕ → ℝ} {B : ℝ} (hs : ∀ n, |s n| ≤ B) : ∃ t, Tendsto s UF (𝓝 t) := by
  obtain ⟨t, -, ht⟩ := (isCompact_Icc (a := -B) (b := B)).ultrafilter_le_nhds
    (Ultrafilter.map s (hyperfilter ℕ)) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact Filter.mem_map.2 (Eventually.of_forall fun n => abs_le.1 (hs n)))
  exact ⟨t, ht⟩

lemma exists_isWL {a : ℕ → E} {B : ℝ} (ha : ∀ n, ‖a n‖ ≤ B) : ∃ v, IsWL a v := by
  have hlim : ∀ w : E, Tendsto (fun n => inner ℝ (a n) w) UF
      (𝓝 (limUnder UF (fun n => inner ℝ (a n) w))) := by
    intro w
    obtain ⟨t, ht⟩ := exists_ulim (s := fun n => inner ℝ (a n) w) (B := B * ‖w‖)
      (fun n => (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)))
    exact tendsto_nhds_limUnder ⟨t, ht⟩
  let L : E →ₗ[ℝ] ℝ :=
    { toFun := fun w => limUnder UF (fun n => inner ℝ (a n) w)
      map_add' := fun w₁ w₂ => by
        have := (hlim w₁).add (hlim w₂)
        simp only [← inner_add_right] at this
        exact tendsto_nhds_unique (hlim _) this
      map_smul' := fun c w => by
        have := (hlim w).const_mul c
        simp only [← real_inner_smul_right] at this
        exact tendsto_nhds_unique (hlim _) this }
  have hL : ∀ w, ‖L w‖ ≤ B * ‖w‖ := by
    intro w
    have hmem := isClosed_Icc.mem_of_tendsto (hlim w) (Eventually.of_forall fun n =>
      abs_le.1 ((abs_real_inner_le_norm (a n) w).trans
        (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _))))
    rw [Real.norm_eq_abs]
    exact abs_le.2 hmem
  let Φ : StrongDual ℝ E := L.mkContinuous B hL
  refine ⟨(InnerProductSpace.toDual ℝ E).symm Φ, fun w => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hlim w

/-- The chosen weak limit (junk `0` if none). -/
noncomputable def V (a : ℕ → E) : E := by
  classical exact if h : ∃ v, IsWL a v then h.choose else 0

lemma V_eq {a : ℕ → E} {v : E} (h : IsWL a v) : V a = v := by
  have h' : ∃ v, IsWL a v := ⟨v, h⟩
  simp only [V, dif_pos h']
  exact isWL_unique h'.choose_spec h

lemma isWL_add {a b : ℕ → E} {v v' : E} (ha : IsWL a v) (hb : IsWL b v') :
    IsWL (fun n => a n + b n) (v + v') := fun w => by
  simpa only [inner_add_left] using (ha w).add (hb w)

lemma isWL_smul (c : ℝ) {a : ℕ → E} {v : E} (ha : IsWL a v) :
    IsWL (fun n => c • a n) (c • v) := fun w => by
  simpa only [real_inner_smul_left] using (ha w).const_mul c

lemma isWL_const (v : E) : IsWL (fun _ => v) v := fun _ => tendsto_const_nhds

end WL

/-! ### Følner averages and the weak limit `P` -/

section Avg

variable {X : Type*} [MeasurableSpace X] {Λ : Type} [Group Λ] [MulAction Λ X]

variable (Λ) in
/-- The orbit relation. -/
def orb : Set (X × X) := {p | ∃ l : Λ, l • p.1 = p.2}

/-- Følner average along the orbit. -/
noncomputable def avg (T : Finset Λ) (f : X × X → ℝ) (x : X) : ℝ :=
  (T.card : ℝ)⁻¹ * ∑ g ∈ T, f (x, g⁻¹ • x)

lemma mem_orb_smul (x : X) (g : Λ) : (x, g • x) ∈ orb Λ := ⟨g, rfl⟩

lemma abs_avg_le {T : Finset Λ} (hT : T.Nonempty) {f : X × X → ℝ} {C : ℝ}
    (hC : ∀ p ∈ orb Λ, |f p| ≤ C) (x : X) : |avg T f x| ≤ C := by
  unfold avg
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  rw [abs_mul, abs_inv, abs_of_pos hcard, inv_mul_le_iff₀ hcard]
  calc |∑ g ∈ T, f (x, g⁻¹ • x)| ≤ ∑ g ∈ T, |f (x, g⁻¹ • x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g ∈ T, C := Finset.sum_le_sum fun g _ => hC _ (mem_orb_smul x g⁻¹)
    _ = T.card * C := by simp

lemma avg_nonneg {T : Finset Λ} {f : X × X → ℝ} (hf : ∀ p ∈ orb Λ, 0 ≤ f p) (x : X) :
    0 ≤ avg T f x :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun g _ => hf _ (mem_orb_smul x g⁻¹))

lemma measurable_avg (hmeas : ∀ l : Λ, Measurable (fun x : X => l • x)) (T : Finset Λ)
    {f : X × X → ℝ} (hf : Measurable f) : Measurable (avg T f) := by
  unfold avg
  exact (Finset.measurable_sum _ fun g _ => hf.comp (measurable_id.prodMk (hmeas g⁻¹))).const_mul _

lemma avg_add (T : Finset Λ) (f g : X × X → ℝ) : avg T (f + g) = avg T f + avg T g := by
  funext x; simp [avg, Finset.sum_add_distrib, mul_add]

lemma avg_smul (T : Finset Λ) (c : ℝ) (f : X × X → ℝ) : avg T (c • f) = c • avg T f := by
  funext x; simp [avg, Finset.mul_sum]; ring_nf

lemma avg_one {T : Finset Λ} (hT : T.Nonempty) : avg T (1 : X × X → ℝ) = 1 := by
  funext x
  have hcard : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  simp [avg, hcard]

lemma bdd_nonneg {R : Set (X × X)} {f : X × X → ℝ} (hf : IsBddMeasOn R f) :
    ∃ C, 0 ≤ C ∧ ∀ p ∈ R, |f p| ≤ C := by
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

variable (μ : Measure X)

/-- The `L²` class of the `T`-average (junk `0` if not in `L²`). -/
noncomputable def aL (T : Finset Λ) (f : X × X → ℝ) : Lp ℝ 2 μ := by
  classical exact if h : MemLp (avg T f) 2 μ then h.toLp _ else 0

lemma aL_eq {T : Finset Λ} {f : X × X → ℝ} (h : MemLp (avg T f) 2 μ) : aL μ T f = h.toLp _ := by
  simp only [aL, dif_pos h]

/-- The candidate left invariant mean. -/
noncomputable def P (T : ℕ → Finset Λ) (f : X × X → ℝ) : X → ℝ :=
  ((V (fun n => aL μ (T n) f) : Lp ℝ 2 μ) : X → ℝ)

variable [IsFiniteMeasure μ] (hmeas : ∀ l : Λ, Measurable (fun x : X => l • x))
  {T : ℕ → Finset Λ} (hTne : ∀ n, (T n).Nonempty)

include hmeas in
lemma memLp_avg {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) {S : Finset Λ} (hS : S.Nonempty) :
    MemLp (avg S f) 2 μ := by
  obtain ⟨C, -, hC⟩ := bdd_nonneg hf
  exact MemLp.of_bound (measurable_avg hmeas S hf.1).aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_avg_le hS hC x)

include hmeas hTne in
lemma isWL_aL {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) :
    IsWL (fun n => aL μ (T n) f) (V (fun n => aL μ (T n) f)) := by
  obtain ⟨C, hC0, hC⟩ := bdd_nonneg hf
  obtain ⟨v, hv⟩ := exists_isWL (a := fun n => aL μ (T n) f)
    (B := (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * C) (fun n => by
      rw [aL_eq μ (memLp_avg μ hmeas hf (hTne n))]
      refine Lp.norm_le_of_ae_bound hC0 ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_avg μ hmeas hf (hTne n))] with x hx
      rw [hx, Real.norm_eq_abs]
      exact abs_avg_le (hTne n) hC x)
  rw [V_eq hv]
  exact hv

include hmeas hTne in
lemma tendsto_weight {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) {w : X → ℝ}
    (hw : Measurable w) {M : ℝ} (hM : ∀ x, |w x| ≤ M) :
    Tendsto (fun n => ∫ x, avg (T n) f x * w x ∂μ) UF (𝓝 (∫ x, P μ T f x * w x ∂μ)) := by
  have hwL : MemLp w 2 μ := MemLp.of_bound hw.aestronglyMeasurable M
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  have h := isWL_aL μ hmeas hTne hf (hwL.toLp w)
  have e1 : ∀ n, inner ℝ (aL μ (T n) f) (hwL.toLp w) = ∫ x, avg (T n) f x * w x ∂μ := by
    intro n
    rw [aL_eq μ (memLp_avg μ hmeas hf (hTne n)), L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_avg μ hmeas hf (hTne n)), MemLp.coeFn_toLp hwL]
      with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have e2 : inner ℝ (V (fun n => aL μ (T n) f)) (hwL.toLp w) = ∫ x, P μ T f x * w x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hwL] with x h2
    rw [h2]
    simp [P, mul_comm]
  simp only [e1, e2] at h
  exact h

lemma indicator_one_mul (A : Set X) (h : X → ℝ) :
    (fun x => h x * A.indicator 1 x) = A.indicator h := by
  funext x
  by_cases hx : x ∈ A <;> simp [hx]

include hmeas hTne in
lemma tendsto_setIntegral {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) {A : Set X}
    (hA : MeasurableSet A) :
    Tendsto (fun n => ∫ x in A, avg (T n) f x ∂μ) UF (𝓝 (∫ x in A, P μ T f x ∂μ)) := by
  have h := tendsto_weight μ hmeas hTne hf (measurable_const.indicator hA) (M := 1)
    (w := A.indicator 1) (fun x => by
      by_cases hx : x ∈ A <;> simp [hx])
  simp only [indicator_one_mul, integral_indicator hA] at h
  exact h

lemma integrable_P (f : X × X → ℝ) : Integrable (P μ T f) μ :=
  (Lp.memLp _).integrable (by norm_num)

include hmeas hTne in
lemma ae_abs_P_le {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) {C : ℝ}
    (hC : ∀ p ∈ orb Λ, |f p| ≤ C) : ∀ᵐ x ∂μ, |P μ T f x| ≤ C := by
  have key : ∀ A, MeasurableSet A → |∫ x in A, P μ T f x ∂μ| ≤ C * μ.real A := by
    intro A hA
    refine le_of_tendsto' (tendsto_setIntegral μ hmeas hTne hf hA).abs (fun n => ?_)
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const (measure_lt_top μ A)
      (fun x _ => by rw [Real.norm_eq_abs]; exact abs_avg_le (hTne n) hC x)
  have h1 : P μ T f ≤ᵐ[μ] fun _ => C :=
    ae_le_of_forall_setIntegral_le (integrable_P μ f) (integrable_const C) (fun A hA _ => by
      rw [setIntegral_const, smul_eq_mul]
      have := key A hA
      linarith [le_abs_self (∫ x in A, P μ T f x ∂μ)])
  have h2 : (fun _ => -C) ≤ᵐ[μ] P μ T f :=
    ae_le_of_forall_setIntegral_le (integrable_const (-C)) (integrable_P μ f) (fun A hA _ => by
      rw [setIntegral_const, smul_eq_mul]
      have := key A hA
      linarith [neg_abs_le (∫ x in A, P μ T f x ∂μ)])
  filter_upwards [h1, h2] with x h1 h2
  exact abs_le.2 ⟨h2, h1⟩

include hmeas hTne in
lemma ae_nonneg_P {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f)
    (hpos : ∀ p ∈ orb Λ, 0 ≤ f p) : ∀ᵐ x ∂μ, 0 ≤ P μ T f x := by
  have := ae_nonneg_of_forall_setIntegral_nonneg (integrable_P μ (T := T) f) (fun A hA _ =>
    ge_of_tendsto' (tendsto_setIntegral μ hmeas hTne hf hA)
      (fun n => setIntegral_nonneg hA (fun x _ => avg_nonneg hpos x)))
  filter_upwards [this] with x hx
  exact hx

lemma isBddMeasOn_add {R : Set (X × X)} {f g : X × X → ℝ} (hf : IsBddMeasOn R f)
    (hg : IsBddMeasOn R g) : IsBddMeasOn R (f + g) := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  exact ⟨hf.1.add hg.1, C + D, fun p hp => (abs_add_le _ _).trans (add_le_add (hC p hp) (hD p hp))⟩

lemma isBddMeasOn_smul {R : Set (X × X)} (c : ℝ) {f : X × X → ℝ} (hf : IsBddMeasOn R f) :
    IsBddMeasOn R (c • f) := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨hf.1.const_smul c, |c| * C, fun p hp => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg c)

include hmeas hTne in
lemma P_add {f g : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) (hg : IsBddMeasOn (orb Λ) g) :
    P μ T (f + g) =ᵐ[μ] P μ T f + P μ T g := by
  have hseq : (fun n => aL μ (T n) (f + g)) = fun n => aL μ (T n) f + aL μ (T n) g := by
    funext n
    have hf' := memLp_avg μ hmeas hf (hTne n)
    have hg' := memLp_avg μ hmeas hg (hTne n)
    rw [aL_eq μ (memLp_avg μ hmeas (isBddMeasOn_add hf hg) (hTne n)), aL_eq μ hf', aL_eq μ hg',
      ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by rw [avg_add])
  have hV : V (fun n => aL μ (T n) (f + g)) =
      V (fun n => aL μ (T n) f) + V (fun n => aL μ (T n) g) := by
    rw [hseq]
    exact V_eq (isWL_add (isWL_aL μ hmeas hTne hf) (isWL_aL μ hmeas hTne hg))
  unfold P
  rw [hV]
  exact Lp.coeFn_add _ _

include hmeas hTne in
lemma P_smul (c : ℝ) {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) :
    P μ T (c • f) =ᵐ[μ] c • P μ T f := by
  have hseq : (fun n => aL μ (T n) (c • f)) = fun n => c • aL μ (T n) f := by
    funext n
    have hf' := memLp_avg μ hmeas hf (hTne n)
    rw [aL_eq μ (memLp_avg μ hmeas (isBddMeasOn_smul c hf) (hTne n)), aL_eq μ hf',
      ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by rw [avg_smul])
  have hV : V (fun n => aL μ (T n) (c • f)) = c • V (fun n => aL μ (T n) f) := by
    rw [hseq]
    exact V_eq (isWL_smul c (isWL_aL μ hmeas hTne hf))
  unfold P
  rw [hV]
  exact Lp.coeFn_smul _ _

include hTne in
lemma P_one : P μ T (1 : X × X → ℝ) =ᵐ[μ] 1 := by
  have h1 : MemLp (1 : X → ℝ) 2 μ := memLp_const 1
  have hseq : (fun n => aL μ (T n) (1 : X × X → ℝ)) = fun _ => h1.toLp 1 := by
    funext n
    have h1' : MemLp (avg (T n) (1 : X × X → ℝ)) 2 μ := by rw [avg_one (hTne n)]; exact h1
    rw [aL_eq μ h1']
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by rw [avg_one (hTne n)])
  unfold P
  rw [hseq, V_eq (isWL_const _)]
  exact MemLp.coeFn_toLp h1

lemma P_congr {f g : X × X → ℝ} (hfg : RelNull μ (orb Λ) {p | f p ≠ g p}) :
    P μ T f = P μ T g := by
  have hae : ∀ S : Finset Λ, avg S f =ᵐ[μ] avg S g := by
    intro S
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hfg] with x hx
    unfold avg
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    by_contra hne
    exact hx ⟨(x, l⁻¹ • x), ⟨hne, mem_orb_smul x l⁻¹⟩, rfl⟩
  have hseq : (fun n => aL μ (T n) f) = fun n => aL μ (T n) g := by
    funext n
    classical
    unfold aL
    by_cases h : MemLp (avg (T n) f) 2 μ
    · have h' : MemLp (avg (T n) g) 2 μ := (memLp_congr_ae (hae (T n))).1 h
      rw [dif_pos h, dif_pos h']
      exact MemLp.toLp_congr _ _ (hae (T n))
    · have h' : ¬ MemLp (avg (T n) g) 2 μ := fun h' => h ((memLp_congr_ae (hae (T n))).2 h')
      rw [dif_neg h, dif_neg h']
  unfold P
  rw [hseq]

end Avg

/-! ### Invariance under partial transformations -/

section Inv

variable {X : Type*} [MeasurableSpace X] {Λ : Type} [Group Λ] [MulAction Λ X]
  (φ : PartialTransformation (orb Λ : Set (X × X)))

/-- `φ⁻¹` on the image of `φ`, extended by the identity. -/
noncomputable def psi (y : X) : X := by
  classical exact if h : y ∈ φ.cod then (φ.e.symm ⟨y, h⟩ : X) else y

lemma psi_of_mem {y : X} (h : y ∈ φ.cod) : psi φ y = φ.e.symm ⟨y, h⟩ := by
  simp only [psi, dif_pos h]

lemma psi_of_not_mem {y : X} (h : y ∉ φ.cod) : psi φ y = y := by
  simp only [psi, dif_neg h]

lemma measurable_psi : Measurable (psi φ) := by
  classical
  unfold psi
  exact Measurable.dite (measurable_subtype_coe.comp φ.e.symm.measurable) measurable_subtype_coe
    φ.measurableSet_cod

lemma shiftBase_eq (F : X → ℝ) : φ.shiftBase F = φ.cod.indicator (F ∘ psi φ) := by
  funext y
  by_cases h : y ∈ φ.cod
  · simp [PartialTransformation.shiftBase, h, psi_of_mem φ h]
  · simp [PartialTransformation.shiftBase, h]

open Classical in
lemma shiftRel_eq (f : X × X → ℝ) :
    φ.shiftRel f = fun p => if p.1 ∈ φ.cod then f (psi φ p.1, p.2) else 0 := by
  funext p
  by_cases h : p.1 ∈ φ.cod
  · simp [PartialTransformation.shiftRel, h, psi_of_mem φ h]
  · simp [PartialTransformation.shiftRel, h]

lemma exists_smul_psi {y : X} (h : y ∈ φ.cod) : ∃ k : Λ, k • psi φ y = y := by
  obtain ⟨k, hk⟩ := φ.graph_subset (φ.e.symm ⟨y, h⟩)
  refine ⟨k, ?_⟩
  rw [psi_of_mem φ h]
  simpa using hk

lemma null_preimage_psi [Countable Λ] (μ : Measure X)
    (hnull : ∀ (l : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => l • x) ⁻¹' s) = 0)
    {N : Set X} (hN : μ N = 0) : μ (psi φ ⁻¹' N) = 0 := by
  refine measure_mono_null (t := N ∪ ⋃ l : Λ, (fun z : X => l • z) ⁻¹' N) ?_
    (measure_union_null hN (measure_iUnion_null fun l => hnull l N hN))
  intro y hy
  by_cases h : y ∈ φ.cod
  · obtain ⟨k, hk⟩ := exists_smul_psi φ h
    right
    simp only [mem_iUnion, mem_preimage]
    refine ⟨k⁻¹, ?_⟩
    rw [inv_smul_eq_iff.2 hk.symm]
    exact hy
  · left
    rw [mem_preimage, psi_of_not_mem φ h] at hy
    exact hy

lemma qmp_psi [Countable Λ] (μ : Measure X)
    (hnull : ∀ (l : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => l • x) ⁻¹' s) = 0) :
    Measure.QuasiMeasurePreserving (psi φ) μ μ :=
  ⟨measurable_psi φ, Measure.AbsolutelyContinuous.mk fun s hs h0 => by
    rw [Measure.map_apply (measurable_psi φ) hs]
    exact null_preimage_psi φ μ hnull h0⟩

lemma isBddMeasOn_shiftRel {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) :
    IsBddMeasOn (orb Λ) (φ.shiftRel f) := by
  obtain ⟨C, hC0, hC⟩ := bdd_nonneg hf
  rw [shiftRel_eq]
  refine ⟨Measurable.ite (φ.measurableSet_cod.preimage measurable_fst)
    (hf.1.comp (((measurable_psi φ).comp measurable_fst).prodMk measurable_snd))
    measurable_const, C, fun p hp => ?_⟩
  by_cases h : p.1 ∈ φ.cod
  · simp only [if_pos h]
    obtain ⟨k, hk⟩ := exists_smul_psi φ h
    obtain ⟨l, hl⟩ := hp
    exact hC _ ⟨l * k, by simp only [mul_smul, hk, hl]⟩
  · simp only [if_neg h, abs_zero]
    exact hC0

lemma abs_sum_sub_sum_le [DecidableEq Λ] {S₁ S₂ : Finset Λ} {H : Λ → ℝ} {C : ℝ} (hC : ∀ g, |H g| ≤ C) :
    |∑ g ∈ S₂, H g - ∑ g ∈ S₁, H g| ≤ 2 * C * ((S₂ ∆ S₁).card : ℝ) := by
  classical
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  have h1 : (S₂ \ S₁).card ≤ (S₂ ∆ S₁).card :=
    Finset.card_le_card (by rw [Finset.symmDiff_def]; exact Finset.subset_union_left)
  have h2 : (S₁ \ S₂).card ≤ (S₂ ∆ S₁).card :=
    Finset.card_le_card (by rw [Finset.symmDiff_def]; exact Finset.subset_union_right)
  have b : ∀ S : Finset Λ, |∑ g ∈ S, H g| ≤ C * S.card := by
    intro S
    calc |∑ g ∈ S, H g| ≤ ∑ g ∈ S, |H g| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g ∈ S, C := Finset.sum_le_sum fun g _ => hC g
      _ = C * S.card := by simp [mul_comm]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1)
  have h1' : ((S₂ \ S₁).card : ℝ) ≤ (S₂ ∆ S₁).card := by exact_mod_cast h1
  have h2' : ((S₁ \ S₂).card : ℝ) ≤ (S₂ ∆ S₁).card := by exact_mod_cast h2
  calc _ ≤ |∑ g ∈ S₂ \ S₁, H g| + |∑ g ∈ S₁ \ S₂, H g| := abs_sub _ _
    _ ≤ C * (S₂ \ S₁).card + C * (S₁ \ S₂).card := add_le_add (b _) (b _)
    _ ≤ 2 * C * ((S₂ ∆ S₁).card : ℝ) := by nlinarith

lemma abs_avg_shiftRel_sub_le [DecidableEq Λ] {f : X × X → ℝ} {C : ℝ} (hC : ∀ p ∈ orb Λ, |f p| ≤ C)
    {S : Finset Λ} (hS : S.Nonempty) {y : X} (hy : y ∈ φ.cod) {k : Λ} (hk : k • psi φ y = y) :
    |avg S (φ.shiftRel f) y - avg S f (psi φ y)| ≤
      2 * C * (((k⁻¹ • S) ∆ S).card : ℝ) / S.card := by
  classical
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  set x := psi φ y
  set H : Λ → ℝ := fun g => f (x, g⁻¹ • x)
  have hH : ∀ g, |H g| ≤ C := fun g => hC _ (mem_orb_smul x g⁻¹)
  have e1 : avg S (φ.shiftRel f) y = (S.card : ℝ)⁻¹ * ∑ g ∈ k⁻¹ • S, H g := by
    unfold avg
    congr 1
    rw [Finset.smul_finset_def, Finset.sum_image (fun a _ b _ h => by
      simpa using h)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [shiftRel_eq]
    simp only [if_pos hy, H, smul_eq_mul, mul_inv_rev, inv_inv, mul_smul]
    rw [← hk]
    simp [x, hk]
  have e2 : avg S f x = (S.card : ℝ)⁻¹ * ∑ g ∈ S, H g := rfl
  rw [e1, e2, ← mul_sub, abs_mul, abs_inv, abs_of_pos hcard, inv_mul_le_iff₀ hcard,
    mul_div_cancel₀ _ hcard.ne']
  exact abs_sum_sub_sum_le hH

end Inv

/-! ### Integral estimates and the change of variables -/

section Est

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

lemma abs_integral_mul_sub_le {h D D' : X → ℝ} {C : ℝ} (hh : AEStronglyMeasurable h μ)
    (hC : ∀ᵐ x ∂μ, |h x| ≤ C) (hD : Integrable D μ) (hD' : Integrable D' μ) :
    |∫ x, h x * D x ∂μ - ∫ x, h x * D' x ∂μ| ≤ C * ∫ x, |D x - D' x| ∂μ := by
  have hC' : ∀ᵐ x ∂μ, ‖h x‖ ≤ C := by
    filter_upwards [hC] with x hx
    rwa [Real.norm_eq_abs]
  rw [← integral_sub (hD.bdd_mul hh hC') (hD'.bdd_mul hh hC'), ← integral_const_mul,
    ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hD.sub hD').abs.const_mul C) ?_
  filter_upwards [hC] with x hx
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

lemma abs_sub_clamp_le (d M : ℝ) (hM : 0 ≤ M) : |d - max (min d M) (-M)| ≤ |d| := by
  rcases le_total d M with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total d (-M) with h2 | h2
    · rw [max_eq_right h2, abs_of_nonpos (by linarith : d - -M ≤ 0),
        abs_of_nonpos (by linarith : d ≤ 0)]
      linarith
    · rw [max_eq_left h2]
      simp
  · rw [min_eq_right h1, max_eq_left (by linarith : -M ≤ M),
      abs_of_nonneg (by linarith : 0 ≤ d - M), abs_of_nonneg (by linarith : 0 ≤ d)]
    linarith

lemma clamp_eq {d M : ℝ} (h : |d| ≤ M) : max (min d M) (-M) = d := by
  rw [min_eq_left (abs_le.1 h).2, max_eq_left (abs_le.1 h).1]

end Est

section Main

variable {X : Type*} [MeasurableSpace X] {Λ : Type} [Group Λ] [MulAction Λ X]
  (μ : Measure X) [IsFiniteMeasure μ] (hmeas : ∀ l : Λ, Measurable (fun x : X => l • x))
  {T : ℕ → Finset Λ} (hTne : ∀ n, (T n).Nonempty)

include hmeas hTne in
lemma tendsto_weight_L1 {f : X × X → ℝ} (hf : IsBddMeasOn (orb Λ) f) {D : X → ℝ}
    (hD : Measurable D) (hDi : Integrable D μ) :
    Tendsto (fun n => ∫ x, avg (T n) f x * D x ∂μ) UF (𝓝 (∫ x, P μ T f x * D x ∂μ)) := by
  obtain ⟨C, hC0, hC⟩ := bdd_nonneg hf
  set cl : ℕ → X → ℝ := fun M x => max (min (D x) M) (-M) with hcl
  have hclm : ∀ M, Measurable (cl M) := fun M => (hD.min measurable_const).max measurable_const
  have hclb : ∀ M x, |cl M x| ≤ M := fun M x => abs_le.2 ⟨le_max_right _ _,
    max_le (min_le_right _ _) (by have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith)⟩
  have hcli : ∀ M, Integrable (cl M) μ := fun M =>
    Integrable.of_bound (hclm M).aestronglyMeasurable M
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hclb M x)
  have hconv : Tendsto (fun M : ℕ => ∫ x, |D x - cl M x| ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (M : ℕ) x => |D x - cl M x|) (f := fun _ => (0 : ℝ)) (fun x => |D x|)
      (fun M => (hD.sub (hclm M)).abs.aestronglyMeasurable) hDi.abs
      (fun M => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_abs]
        exact abs_sub_clamp_le _ _ (Nat.cast_nonneg M))
      (Eventually.of_forall fun x => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈|D x|⌉₊] with M hM
        have : |D x| ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast hM)
        simp only [hcl, clamp_eq this, sub_self, abs_zero])
    simpa using this
  have hu := ae_abs_P_le μ hmeas hTne hf hC
  have hum : AEStronglyMeasurable (P μ T f) μ := (integrable_P μ f).aestronglyMeasurable
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (3 * (C + 1)) := by positivity
  obtain ⟨M, hM⟩ := (hconv.eventually (gt_mem_nhds hδ)).exists
  have hK := tendsto_weight μ hmeas hTne hf (hclm M) (hclb M)
  filter_upwards [Metric.tendsto_nhds.1 hK (ε / 3) (by positivity)] with n hn
  have he0 : 0 ≤ ∫ x, |D x - cl M x| ∂μ := integral_nonneg fun x => abs_nonneg _
  have hCe : C * ∫ x, |D x - cl M x| ∂μ < ε / 3 := by
    calc C * ∫ x, |D x - cl M x| ∂μ ≤ (C + 1) * ∫ x, |D x - cl M x| ∂μ := by nlinarith
      _ < (C + 1) * (ε / (3 * (C + 1))) := mul_lt_mul_of_pos_left hM (by linarith)
      _ = ε / 3 := by field_simp
  have h1 := abs_integral_mul_sub_le μ (measurable_avg hmeas (T n) hf.1).aestronglyMeasurable
    (Eventually.of_forall fun x => abs_avg_le (hTne n) hC x) hDi (hcli M)
  have h3 := abs_integral_mul_sub_le μ hum hu hDi (hcli M)
  rw [Real.dist_eq] at hn ⊢
  have t1 := abs_sub_le (∫ x, avg (T n) f x * D x ∂μ) (∫ x, avg (T n) f x * cl M x ∂μ)
    (∫ x, P μ T f x * D x ∂μ)
  have t2 := abs_sub_le (∫ x, avg (T n) f x * cl M x ∂μ) (∫ x, P μ T f x * cl M x ∂μ)
    (∫ x, P μ T f x * D x ∂μ)
  have t3 := abs_sub_comm (∫ x, P μ T f x * cl M x ∂μ) (∫ x, P μ T f x * D x ∂μ)
  linarith

variable [Countable Λ] [DecidableEq Λ]
  (hnull : ∀ (l : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => l • x) ⁻¹' s) = 0)
  (hT : ∀ k : Λ, Tendsto (fun n => (((k • T n) ∆ T n).card : ℝ) / (T n).card) atTop (𝓝 0))

include hmeas hTne hT in
lemma tendsto_diff (φ : PartialTransformation (orb Λ : Set (X × X))) {f : X × X → ℝ}
    (hf : IsBddMeasOn (orb Λ) f) (A : Set X) :
    Tendsto (fun n => ∫ x in A, (avg (T n) (φ.shiftRel f) x - φ.shiftBase (avg (T n) f) x) ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := bdd_nonneg hf
  obtain ⟨C', hC'0, hC'⟩ := bdd_nonneg (isBddMeasOn_shiftRel φ hf)
  have := tendsto_integral_of_dominated_convergence (μ := μ.restrict A)
    (F := fun n x => avg (T n) (φ.shiftRel f) x - φ.shiftBase (avg (T n) f) x)
    (f := fun _ => 0) (fun _ => C' + C)
    (fun n => ((measurable_avg hmeas (T n) (isBddMeasOn_shiftRel φ hf).1).sub
      (by
        rw [shiftBase_eq]
        exact ((measurable_avg hmeas (T n) hf.1).comp (measurable_psi φ)).indicator
          φ.measurableSet_cod)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans (add_le_add (abs_avg_le (hTne n) hC' x) ?_)
      rw [shiftBase_eq]
      by_cases hx : x ∈ φ.cod
      · rw [indicator_of_mem hx]
        exact abs_avg_le (hTne n) hC _
      · rw [indicator_of_notMem hx, abs_zero]
        exact hC0)
    (Eventually.of_forall fun y => by
      by_cases hy : y ∈ φ.cod
      · obtain ⟨k, hk⟩ := exists_smul_psi φ hy
        have hsb : ∀ n, φ.shiftBase (avg (T n) f) y = avg (T n) f (psi φ y) := fun n => by
          rw [shiftBase_eq, indicator_of_mem hy]
          rfl
        simp only [hsb]
        have hlim := (hT k⁻¹).const_mul (2 * C)
        rw [mul_zero] at hlim
        refine squeeze_zero_norm (fun n => ?_) hlim
        rw [Real.norm_eq_abs]
        exact (abs_avg_shiftRel_sub_le φ hC (hTne n) hy hk).trans_eq (mul_div_assoc _ _ _)
      · have h0 : ∀ n, avg (T n) (φ.shiftRel f) y = 0 := fun n => by
          simp [avg, shiftRel_eq, hy]
        have h0' : ∀ n, φ.shiftBase (avg (T n) f) y = 0 := fun n => by
          rw [shiftBase_eq, indicator_of_notMem hy]
        simp [h0, h0'])
  simpa using this

include hnull in
lemma setIntegral_shiftBase (φ : PartialTransformation (orb Λ : Set (X × X))) (A : Set X)
    {F : X → ℝ} (hF : AEStronglyMeasurable F μ) :
    ∫ x in A, φ.shiftBase F x ∂μ =
      ∫ x, F x * ((Measure.map (psi φ) (μ.restrict (A ∩ φ.cod))).rnDeriv μ x).toReal ∂μ := by
  have hac : Measure.map (psi φ) (μ.restrict (A ∩ φ.cod)) ≪ μ :=
    (Measure.absolutelyContinuous_of_le
      (Measure.map_mono Measure.restrict_le_self (measurable_psi φ))).trans
      (qmp_psi φ μ hnull).absolutelyContinuous
  rw [shiftBase_eq, setIntegral_indicator φ.measurableSet_cod]
  simp only [Function.comp_apply]
  rw [← integral_map (measurable_psi φ).aemeasurable (hF.mono_ac hac),
    ← integral_rnDeriv_smul hac]
  simp only [smul_eq_mul, mul_comm]

include hmeas hTne hnull hT in
theorem P_invariant (φ : PartialTransformation (orb Λ : Set (X × X))) {f : X × X → ℝ}
    (hf : IsBddMeasOn (orb Λ) f) :
    P μ T (φ.shiftRel f) =ᵐ[μ] φ.shiftBase (P μ T f) := by
  obtain ⟨C, hC0, hC⟩ := bdd_nonneg hf
  have hf' := isBddMeasOn_shiftRel φ hf
  obtain ⟨C', hC'0, hC'⟩ := bdd_nonneg hf'
  have hu := ae_abs_P_le μ hmeas hTne hf hC
  have hum : AEStronglyMeasurable (P μ T f) μ := (integrable_P μ f).aestronglyMeasurable
  have hqmp := qmp_psi φ μ hnull
  have hint : Integrable (φ.shiftBase (P μ T f)) μ := by
    rw [shiftBase_eq]
    refine Integrable.indicator
      (Integrable.of_bound (hum.comp_quasiMeasurePreserving hqmp) C ?_) φ.measurableSet_cod
    filter_upwards [hqmp.ae hu] with x hx
    rw [Real.norm_eq_abs]
    exact hx
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ (integrable_P μ _) hint
    (fun A hA _ => ?_)
  set D : X → ℝ := fun x =>
    ((Measure.map (psi φ) (μ.restrict (A ∩ φ.cod))).rnDeriv μ x).toReal with hD
  have hDm : Measurable D := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hDi : Integrable D μ := Measure.integrable_toReal_rnDeriv
  have t1 := tendsto_setIntegral μ hmeas hTne hf' hA
  have hsplit : ∀ n, ∫ x in A, avg (T n) (φ.shiftRel f) x ∂μ =
      ∫ x in A, (avg (T n) (φ.shiftRel f) x - φ.shiftBase (avg (T n) f) x) ∂μ
        + ∫ x, avg (T n) f x * D x ∂μ := by
    intro n
    have hm1 : Integrable (avg (T n) (φ.shiftRel f)) (μ.restrict A) :=
      Integrable.of_bound (measurable_avg hmeas (T n) hf'.1).aestronglyMeasurable C'
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_avg_le (hTne n) hC' x)
    have hm2 : Integrable (φ.shiftBase (avg (T n) f)) (μ.restrict A) := by
      rw [shiftBase_eq]
      exact (Integrable.of_bound
        ((measurable_avg hmeas (T n) hf.1).comp (measurable_psi φ)).aestronglyMeasurable C
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact abs_avg_le (hTne n) hC _)).indicator φ.measurableSet_cod
    rw [integral_sub hm1 hm2,
      ← setIntegral_shiftBase μ hnull φ A (measurable_avg hmeas (T n) hf.1).aestronglyMeasurable]
    ring
  have t2 : Tendsto (fun n => ∫ x in A, avg (T n) (φ.shiftRel f) x ∂μ) UF
      (𝓝 (∫ x in A, φ.shiftBase (P μ T f) x ∂μ)) := by
    rw [setIntegral_shiftBase μ hnull φ A hum]
    simp only [hsplit]
    have := ((tendsto_diff μ hmeas hTne hT φ hf A).mono_left UF_le_atTop).add
      (tendsto_weight_L1 μ hmeas hTne hf hDm hDi)
    rw [zero_add] at this
    exact this
  exact tendsto_nhds_unique t1 t2

end Main

/-! ### The theorem -/

theorem isAmenableRel_orbit_of_isAmenable' {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (Λ : Type) [Group Λ] [Countable Λ] [MulAction Λ X]
    (hmeas : ∀ l : Λ, Measurable (fun x : X => l • x))
    (hnull : ∀ (l : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => l • x) ⁻¹' s) = 0)
    (hΛ : Garrido.IsAmenable Λ) :
    IsAmenableRel μ {p : X × X | ∃ l : Λ, l • p.1 = p.2} := by
  classical
  obtain ⟨F, hFne, hF⟩ := (Garrido.satisfiesFoelnerCondition_iff_hasFoelnerSequence Λ).1
    ((Garrido.satisfiesFoelnerCondition_iff_isAmenable Λ).2 hΛ)
  set T : ℕ → Finset Λ := fun n => (hFne n).1.toFinset with hTdef
  have hTne : ∀ n, (T n).Nonempty := fun n => (Set.Finite.toFinset_nonempty _).2 (hFne n).2
  have hT : ∀ k : Λ, Tendsto (fun n => (((k • T n) ∆ T n).card : ℝ) / (T n).card) atTop
      (𝓝 0) := by
    intro k
    refine (hF k).congr fun n => ?_
    simp only [T, ← Set.ncard_coe_finset, Finset.coe_symmDiff, Finset.coe_smul_finset,
      Set.Finite.coe_toFinset]
  set μ' := μ.toFinite
  have hae : ae μ' = ae μ := ae_toFinite
  have h0 : ∀ s, μ' s = 0 ↔ μ s = 0 := fun s => toFinite_apply_eq_zero_iff
  have hnull' : ∀ (l : Λ) (s : Set X), μ' s = 0 → μ' ((fun x : X => l • x) ⁻¹' s) = 0 :=
    fun l s hs => (h0 _).2 (hnull l s ((h0 s).1 hs))
  refine ⟨P μ' T, ?_⟩
  refine
    { aemeasurable := fun f _ => ?_
      congr := fun f g _ _ hfg => ?_
      add := fun f g hf hg => ?_
      smul := fun c f hf => ?_
      nonneg := fun f hf hpos => ?_
      one := ?_
      invariant := fun φ f hf => ?_ }
  · obtain ⟨g, hg, he⟩ := (integrable_P μ' (T := T) f).aestronglyMeasurable.aemeasurable
    exact ⟨g, hg, by rw [← hae]; exact he⟩
  · have := P_congr μ' (T := T) (f := f) (g := g) ((h0 _).2 hfg)
    rw [this]
  · have := P_add μ' hmeas hTne hf hg
    rwa [← hae]
  · have := P_smul μ' hmeas hTne c hf
    rwa [← hae]
  · have := ae_nonneg_P μ' hmeas hTne hf hpos
    rwa [← hae]
  · have := P_one μ' hTne
    rwa [← hae]
  · have := P_invariant μ' hmeas hTne hnull' hT φ hf
    rwa [← hae]

end Monod.Dev.Rel
end

open Monod in
theorem solution {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (Λ : Type) [Group Λ] [Countable Λ] [MulAction Λ X]
    (hmeas : ∀ l : Λ, Measurable (fun x : X => l • x))
    (hnull : ∀ (l : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => l • x) ⁻¹' s) = 0)
    (hΛ : Garrido.IsAmenable Λ) :
    IsAmenableRel μ {p : X × X | ∃ l : Λ, l • p.1 = p.2} := by
  exact Dev.Rel.isAmenableRel_orbit_of_isAmenable' μ Λ hmeas hnull hΛ
