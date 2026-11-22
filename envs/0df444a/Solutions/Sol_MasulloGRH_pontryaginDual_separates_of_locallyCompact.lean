-- Prove2me | solution 1 for MasulloGRH.pontryaginDual_separates_of_locallyCompact
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:32:48.425964+00:00
-- url     : https://prove2.me/submissions/c1c74f34-7e12-4673-a116-9baf612255b5

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma

open MeasureTheory Topology Filter ComplexConjugate
open scoped BoundedContinuousFunction CompactlySupported

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace MasulloGRHLCACharAux

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Left translation `(U s v)(y) = v (s * y)` on `L²(μ)`. -/
noncomputable def U (s : G) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun y => s * y) (measurePreserving_mul_left μ s)

theorem U_coeFn (s : G) (v : Lp ℂ 2 μ) : (U μ s v : G → ℂ) =ᵐ[μ] fun y => v (s * y) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem ae_comp_mul_left {s : G} {u v : G → ℂ} (h : u =ᵐ[μ] v) :
    (fun y => u (s * y)) =ᵐ[μ] fun y => v (s * y) :=
  (measurePreserving_mul_left μ s).quasiMeasurePreserving.ae_eq_comp h

theorem U_U (s t : G) (v : Lp ℂ 2 μ) : U μ s (U μ t v) = U μ (t * s) v := by
  apply Lp.ext
  filter_upwards [U_coeFn μ s (U μ t v), ae_comp_mul_left μ (s := s) (U_coeFn μ t v),
    U_coeFn μ (t * s) v] with y h1 h2 h3
  rw [h1, h2, h3, mul_assoc]

theorem U_comm (s t : G) (v : Lp ℂ 2 μ) : U μ s (U μ t v) = U μ t (U μ s v) := by
  rw [U_U, U_U, mul_comm]

theorem U_one (v : Lp ℂ 2 μ) : U μ 1 v = v := by
  apply Lp.ext
  filter_upwards [U_coeFn μ 1 v] with y h
  rw [h, one_mul]

theorem U_eq_smul (s : G) (v : Lp ℂ 2 μ) : U μ s v = DomMulAct.mk s • v := rfl

theorem continuous_U_apply (v : Lp ℂ 2 μ) : Continuous fun s => U μ s v := by
  simp only [U_eq_smul]
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : μ.InnerRegularCompactLTTop := inferInstance
  have : SMulInvariantMeasure G G μ := inferInstance
  exact (DomMulAct.continuous_mk.smul continuous_const)

/-! ### Convolution operators `L_f v = ∫ f(s) U_s v ds` -/

theorem integrable_smul_U (f : C_c(G, ℂ)) (v : Lp ℂ 2 μ) :
    Integrable (fun s => f s • U μ s v) μ := by
  refine Continuous.integrable_of_hasCompactSupport (f.continuous.smul (continuous_U_apply μ v)) ?_
  exact f.hasCompactSupport.smul_right

theorem integrable_norm_cc (f : C_c(G, ℂ)) : Integrable (fun s => ‖f s‖) μ :=
  Continuous.integrable_of_hasCompactSupport f.continuous.norm f.hasCompactSupport.norm

/-- `L f` as a linear map. -/
noncomputable def Llin (f : C_c(G, ℂ)) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun v := ∫ s, f s • U μ s v ∂μ
  map_add' v w := by
    simp only [map_add, smul_add]
    exact integral_add (integrable_smul_U μ f v) (integrable_smul_U μ f w)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply]
    rw [← integral_smul]
    congr 1 with s
    rw [smul_comm]

/-- The convolution operator `L f`. -/
noncomputable def L (f : C_c(G, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Llin μ f).mkContinuous (∫ s, ‖f s‖ ∂μ) fun v => by
    show ‖∫ s, f s • U μ s v ∂μ‖ ≤ _
    refine (norm_integral_le_of_norm_le ((integrable_norm_cc μ f).mul_const ‖v‖)
      (Eventually.of_forall fun s => ?_)).trans ?_
    · rw [norm_smul, LinearIsometry.norm_map]
    · rw [integral_mul_const]

theorem L_apply (f : C_c(G, ℂ)) (v : Lp ℂ 2 μ) : L μ f v = ∫ s, f s • U μ s v ∂μ := rfl

theorem norm_L_le (f : C_c(G, ℂ)) : ‖L μ f‖ ≤ ∫ s, ‖f s‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ => norm_nonneg _) _

theorem L_sub (f g : C_c(G, ℂ)) : L μ (f - g) = L μ f - L μ g := by
  ext1 v
  simp only [L_apply, ContinuousLinearMap.sub_apply, CompactlySupportedContinuousMap.coe_sub,
    Pi.sub_apply, sub_smul]
  exact integral_sub (integrable_smul_U μ f v) (integrable_smul_U μ g v)

/-- `U t` commutes with `L f`. -/
theorem U_L (t : G) (f : C_c(G, ℂ)) (v : Lp ℂ 2 μ) : U μ t (L μ f v) = L μ f (U μ t v) := by
  rw [L_apply, L_apply, ← LinearIsometry.integral_comp_comm]
  congr 1 with s
  rw [map_smul, U_comm]

/-- `L g` commutes with `L f`. -/
theorem L_L (f g : C_c(G, ℂ)) (v : Lp ℂ 2 μ) : L μ g (L μ f v) = L μ f (L μ g v) := by
  rw [L_apply μ f, ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_U μ f v), L_apply]
  congr 1 with s
  rw [map_smul, ← U_L]

/-- Translate of a compactly supported function: `s ↦ f (t⁻¹ * s)`. -/
noncomputable def transl (t : G) (f : C_c(G, ℂ)) : C_c(G, ℂ) where
  toFun s := f (t⁻¹ * s)
  continuous_toFun := f.continuous.comp (continuous_const_mul _)
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft t⁻¹)

theorem transl_apply (t : G) (f : C_c(G, ℂ)) (s : G) : transl t f s = f (t⁻¹ * s) := rfl

theorem U_L_eq (t : G) (f : C_c(G, ℂ)) (v : Lp ℂ 2 μ) :
    U μ t (L μ f v) = L μ (transl t f) v := by
  rw [L_apply, ← LinearIsometry.integral_comp_comm, L_apply]
  simp only [map_smul, U_U, transl_apply]
  conv_rhs => rw [← integral_mul_left_eq_self _ t]
  congr 1 with s
  rw [inv_mul_cancel_left, mul_comm s t]

/-! ### Adjoints -/

theorem U_adjoint (t : G) :
    ContinuousLinearMap.adjoint (U μ t).toContinuousLinearMap = (U μ t⁻¹).toContinuousLinearMap := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  calc inner ℂ (U μ t⁻¹ x) y = inner ℂ (U μ t (U μ t⁻¹ x)) (U μ t y) :=
        (LinearIsometry.inner_map_map _ _ _).symm
    _ = inner ℂ x (U μ t y) := by rw [U_U, inv_mul_cancel, U_one]

theorem Ladj_U (t : G) (f : C_c(G, ℂ)) (v : Lp ℂ 2 μ) :
    ContinuousLinearMap.adjoint (L μ f) (U μ t v) = U μ t (ContinuousLinearMap.adjoint (L μ f) v) := by
  have h : (U μ t⁻¹).toContinuousLinearMap.comp (L μ f) =
      (L μ f).comp (U μ t⁻¹).toContinuousLinearMap := by
    ext1 w; exact U_L μ t⁻¹ f w
  have h2 := congrArg ContinuousLinearMap.adjoint h
  simp only [ContinuousLinearMap.adjoint_comp, U_adjoint, inv_inv] at h2
  simpa using (congrArg (fun T => T v) h2)

theorem Ladj_L (f g : C_c(G, ℂ)) (v : Lp ℂ 2 μ) :
    ContinuousLinearMap.adjoint (L μ f) (L μ g v) = L μ g (ContinuousLinearMap.adjoint (L μ f) v) := by
  rw [L_apply μ g, ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_U μ g v), L_apply]
  congr 1 with s
  rw [map_smul, Ladj_U]

/-! ### Approximate identity -/

theorem exists_L_near (v : Lp ℂ 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : C_c(G, ℂ), ‖L μ f v - v‖ ≤ ε := by
  have hc : ContinuousAt (fun s => U μ s v) 1 := (continuous_U_apply μ v).continuousAt
  rw [ContinuousAt, U_one, Metric.tendsto_nhds] at hc
  obtain ⟨V, hV, hVo, h1V⟩ := mem_nhds_iff.mp (hc ε hε)
  have hV' : ∀ s ∈ V, ‖U μ s v - v‖ < ε := fun s hs => by
    have := hV hs; simpa [dist_eq_norm] using this
  obtain ⟨h, h1, h0, hcs, hrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hVo.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h h1V))
  have hpos : 0 < ∫ s, h s ∂μ := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    h.continuous hcs (fun s => (hrange s).1) (x := 1) (by rw [h1 rfl]; norm_num)
  set c := ∫ s, h s ∂μ
  let f : C_c(G, ℂ) :=
    { toFun := fun s => ((h s / c : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp (h.continuous.div_const c)
      hasCompactSupport' := by
        apply HasCompactSupport.comp_left (g := fun r : ℝ => ((r / c : ℝ) : ℂ)) hcs
        simp }
  refine ⟨f, ?_⟩
  have hint : ∫ s, f s ∂μ = 1 := by
    show ∫ s, ((h s / c : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_div, div_self hpos.ne', Complex.ofReal_one]
  have hfv : v = ∫ s, f s • v ∂μ := by rw [integral_smul_const, hint, one_smul]
  have hint2 : Integrable (fun s => f s • v) μ :=
    (Continuous.integrable_of_hasCompactSupport f.continuous f.hasCompactSupport).smul_const v
  rw [L_apply]
  have hsub : ∫ s, f s • U μ s v ∂μ - v = ∫ s, (f s • U μ s v - f s • v) ∂μ := by
    rw [integral_sub (integrable_smul_U μ f v) hint2, ← hfv]
  rw [hsub]
  have hb : ∀ s, ‖f s • U μ s v - f s • v‖ ≤ h s / c * ε := by
    intro s
    rw [← smul_sub, norm_smul]
    have hfs : ‖f s‖ = h s / c := by
      show ‖((h s / c : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hrange s).1 hpos.le)]
    rw [hfs]
    by_cases hs : s ∈ V
    · exact mul_le_mul_of_nonneg_left (hV' s hs).le (div_nonneg (hrange s).1 hpos.le)
    · rw [h0 hs]; simp
  refine (norm_integral_le_of_norm_le (((Continuous.integrable_of_hasCompactSupport
    h.continuous hcs).div_const c).mul_const ε) (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_div, div_self hpos.ne', one_mul]

theorem eq_zero_of_comp_L (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hT : ∀ f : C_c(G, ℂ), T ∘L L μ f = 0) :
    T = 0 := by
  ext1 v
  simp only [ContinuousLinearMap.zero_apply]
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  have hT1 : 0 < ‖T‖ + 1 := by positivity
  obtain ⟨f, hf⟩ := exists_L_near μ v (div_pos hε hT1)
  have : T (L μ f v) = 0 := by
    have := congrArg (fun S => S v) (hT f); simpa using this
  calc ‖T v‖ = ‖T (v - L μ f v)‖ := by rw [map_sub, this, sub_zero]
    _ ≤ ‖T‖ * ‖v - L μ f v‖ := T.le_opNorm _
    _ ≤ (‖T‖ + 1) * (ε / (‖T‖ + 1)) := by
        rw [norm_sub_rev]; gcongr; linarith
    _ = ε := by field_simp
    _ ≤ 0 + ε := by rw [zero_add]

/-! ### Norm continuity of translates of `L f` -/

/-- `f` as an element of `L¹`. -/
noncomputable def toL1 (f : C_c(G, ℂ)) : Lp ℂ 1 μ :=
  (Continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1) f.continuous f.hasCompactSupport).toLp f

theorem toL1_coeFn (f : C_c(G, ℂ)) : (toL1 μ f : G → ℂ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

theorem dmaL1_coeFn (t : G) (F : Lp ℂ 1 μ) :
    ((DomMulAct.mk t • F : Lp ℂ 1 μ) : G → ℂ) =ᵐ[μ] fun s => F (t * s) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem integral_norm_transl_sub (f : C_c(G, ℂ)) (t t₀ : G) :
    ∫ s, ‖transl t f s - transl t₀ f s‖ ∂μ =
      ‖DomMulAct.mk t⁻¹ • toL1 μ f - DomMulAct.mk t₀⁻¹ • toL1 μ f‖ := by
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (DomMulAct.mk t⁻¹ • toL1 μ f) (DomMulAct.mk t₀⁻¹ • toL1 μ f),
    dmaL1_coeFn μ t⁻¹ (toL1 μ f), dmaL1_coeFn μ t₀⁻¹ (toL1 μ f),
    ae_comp_mul_left μ (s := t⁻¹) (toL1_coeFn μ f),
    ae_comp_mul_left μ (s := t₀⁻¹) (toL1_coeFn μ f)] with s h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, h4, h5]
  rfl

theorem continuous_dmaL1 (F : Lp ℂ 1 μ) : Continuous fun t : G => DomMulAct.mk t⁻¹ • F := by
  have : Fact ((1 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact (DomMulAct.continuous_mk.comp continuous_inv).smul continuous_const

theorem continuous_L_transl (f : C_c(G, ℂ)) : Continuous fun t => L μ (transl t f) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hF := (continuous_dmaL1 μ (toL1 μ f)).continuousAt (x := t₀)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at hF
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hF
  rw [← L_sub]
  refine (norm_L_le μ _).trans (le_of_eq ?_)
  rw [← integral_norm_transl_sub]
  rfl

/-! ### The commutative C⋆-algebra generated by the convolution operators -/

/-- The generating set `{L f}`. -/
def gens : Set (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := Set.range (L μ)

theorem gens_comm : ∀ a ∈ gens μ, ∀ b ∈ gens μ, a * b = b * a := by
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  ext1 v
  exact (L_L μ g f v)

theorem gens_comm_star : ∀ a ∈ gens μ, ∀ b ∈ gens μ, a * star b = star b * a := by
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  ext1 v
  exact (Ladj_L μ g f v).symm

/-- The `*`-algebra generated by the `L f`. -/
noncomputable def A₀ : StarSubalgebra ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := StarAlgebra.adjoin ℂ (gens μ)

/-- Its norm closure. -/
noncomputable def Alg : StarSubalgebra ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := (A₀ μ).topologicalClosure

theorem A₀_comm (x y : A₀ μ) : x * y = y * x := by
  have := StarAlgebra.isMulCommutative_adjoin ℂ (gens_comm μ) (gens_comm_star μ)
  exact this.is_comm.comm x y

noncomputable instance : CommRing (Alg μ) :=
  StarSubalgebra.commRingTopologicalClosure _ (A₀_comm μ)

instance : IsClosed ((Alg μ : Set (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))) :=
  (A₀ μ).isClosed_topologicalClosure

noncomputable instance : NormedCommRing (Alg μ) :=
  { SubringClass.toNormedRing (Alg μ) with mul_comm := mul_comm }

noncomputable instance : CStarAlgebra (Alg μ) := StarSubalgebra.cstarAlgebra _

noncomputable instance : CommCStarAlgebra (Alg μ) where

theorem L_mem (f : C_c(G, ℂ)) : L μ f ∈ Alg μ :=
  (A₀ μ).le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ ⟨f, rfl⟩)

/-- `L f` as an element of the algebra. -/
noncomputable def Le (f : C_c(G, ℂ)) : Alg μ := ⟨L μ f, L_mem μ f⟩

/-! ### Some vectors in `L²` -/

/-- A compactly supported continuous function as an element of `L²`. -/
noncomputable def toL2 (f : C_c(G, ℂ)) : Lp ℂ 2 μ :=
  (Continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) f.continuous f.hasCompactSupport).toLp f

theorem toL2_coeFn (f : C_c(G, ℂ)) : (toL2 μ f : G → ℂ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

/-- A real bump `= 1` on a compact set and `= 0` on a disjoint closed set, as a `C_c` function. -/
theorem exists_cc_one_zero {s t : Set G} (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C_c(G, ℂ), (∀ x ∈ s, f x = 1) ∧ (∀ x ∈ t, f x = 0) := by
  obtain ⟨h, h1, h0, hcs, -⟩ := exists_continuous_one_zero_of_isCompact hs ht hd
  refine ⟨{ toFun := fun x => ((h x : ℝ) : ℂ)
            continuous_toFun := Complex.continuous_ofReal.comp h.continuous
            hasCompactSupport' := hcs.comp_left Complex.ofReal_zero },
    fun x hx => ?_, fun x hx => ?_⟩
  · show ((h x : ℝ) : ℂ) = 1
    rw [h1 hx]; simp
  · show ((h x : ℝ) : ℂ) = 0
    rw [h0 hx]; simp

theorem exists_U_ne (g : G) (hg : g ≠ 1) : ∃ v : Lp ℂ 2 μ, U μ g v ≠ v := by
  obtain ⟨f, f1, f0⟩ := exists_cc_one_zero (isCompact_singleton (x := (1 : G)))
    (isClosed_singleton (x := g)) (Set.disjoint_singleton.mpr hg.symm)
  refine ⟨toL2 μ f, fun h => ?_⟩
  have hae : (fun y => f (g * y)) =ᵐ[μ] f := by
    have h1 := U_coeFn μ g (toL2 μ f)
    have h2 := ae_comp_mul_left μ (s := g) (toL2_coeFn μ f)
    have h3 := toL2_coeFn μ f
    rw [h] at h1
    exact h2.symm.trans (h1.symm.trans h3)
  have := congrFun ((f.continuous.comp (continuous_const_mul g)).ae_eq_iff_eq μ f.continuous |>.mp
    hae) 1
  simp only [Function.comp_apply, mul_one] at this
  have h' : f g = f 1 := this
  rw [f0 g rfl, f1 1 rfl] at h'
  exact zero_ne_one h'

instance : Nontrivial (Lp ℂ 2 μ) := by
  obtain ⟨f, f1, -⟩ := exists_cc_one_zero (isCompact_singleton (x := (1 : G)))
    isClosed_empty (Set.disjoint_empty _)
  refine ⟨⟨toL2 μ f, 0, fun h => ?_⟩⟩
  have hae : (f : G → ℂ) =ᵐ[μ] (0 : G → ℂ) :=
    (toL2_coeFn μ f).symm.trans (by rw [h]; exact Lp.coeFn_zero _ _ _)
  have := congrFun ((f.continuous.ae_eq_iff_eq μ continuous_const).mp hae) 1
  have h' : f 1 = 0 := this
  rw [f1 1 rfl] at h'
  exact one_ne_zero h'

instance : NormOneClass (Alg μ) :=
  ⟨by
    show ‖((1 : Alg μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ = 1
    exact ContinuousLinearMap.norm_id⟩

/-! ### Characters of the algebra give characters of the group -/

theorem transl_mul (s t : G) (f : C_c(G, ℂ)) : transl (s * t) f = transl s (transl t f) := by
  ext x; simp only [transl_apply, mul_inv_rev, mul_assoc]

theorem transl_one (f : C_c(G, ℂ)) : transl 1 f = f := by
  ext x; simp only [transl_apply, inv_one, one_mul]

theorem Le_transl_mul (t : G) (f g : C_c(G, ℂ)) :
    Le μ (transl t f) * Le μ g = Le μ f * Le μ (transl t g) := by
  apply Subtype.ext
  ext1 v
  show L μ (transl t f) (L μ g v) = L μ f (L μ (transl t g) v)
  rw [← U_L_eq, ← U_L_eq, U_L]

theorem norm_Le_transl_le (t : G) (f : C_c(G, ℂ)) : ‖Le μ (transl t f)‖ ≤ ‖L μ f‖ := by
  show ‖L μ (transl t f)‖ ≤ ‖L μ f‖
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [← U_L_eq, LinearIsometry.norm_map]
  exact (L μ f).le_opNorm v

theorem continuous_Le_transl (f : C_c(G, ℂ)) : Continuous fun t => Le μ (transl t f) :=
  (continuous_L_transl μ f).subtype_mk _

abbrev Δ := WeakDual.characterSpace ℂ (Alg μ)

theorem norm_char_le (φ : Δ μ) (a : Alg μ) : ‖φ a‖ ≤ ‖a‖ :=
  spectrum.norm_le_norm_of_mem (WeakDual.CharacterSpace.apply_mem_spectrum φ a)

/-- The group character attached to `φ` and a base function `f` with `φ (L f) ≠ 0`. -/
noncomputable def chi (φ : Δ μ) (f : C_c(G, ℂ)) (t : G) : ℂ := φ (Le μ (transl t f)) / φ (Le μ f)

theorem chi_spec (φ : Δ μ) (f : C_c(G, ℂ)) (hf : φ (Le μ f) ≠ 0) (t : G) (g : C_c(G, ℂ)) :
    φ (Le μ (transl t g)) = chi μ φ f t * φ (Le μ g) := by
  have h := congrArg φ (Le_transl_mul μ t f g)
  simp only [map_mul] at h
  rw [chi, div_mul_eq_mul_div, h]
  field_simp

theorem chi_one (φ : Δ μ) (f : C_c(G, ℂ)) (hf : φ (Le μ f) ≠ 0) : chi μ φ f 1 = 1 := by
  rw [chi, transl_one, div_self hf]

theorem chi_mul (φ : Δ μ) (f : C_c(G, ℂ)) (hf : φ (Le μ f) ≠ 0) (s t : G) :
    chi μ φ f (s * t) = chi μ φ f s * chi μ φ f t := by
  have h1 := chi_spec μ φ f hf (s * t) f
  rw [transl_mul, chi_spec μ φ f hf s, chi_spec μ φ f hf t, ← mul_assoc] at h1
  exact (mul_right_cancel₀ hf h1).symm

theorem continuous_chi (φ : Δ μ) (f : C_c(G, ℂ)) : Continuous (chi μ φ f) :=
  ((map_continuous φ).comp (continuous_Le_transl μ f)).div_const _

theorem le_one_of_pow_bounded {x : ℂ} {M : ℝ} (h : ∀ n : ℕ, ‖x‖ ^ n ≤ M) : ‖x‖ ≤ 1 := by
  by_contra hx
  push Not at hx
  obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hx).eventually_gt_atTop M |>.exists
  exact absurd (h n) (not_le.mpr hn)

theorem norm_chi (φ : Δ μ) (f : C_c(G, ℂ)) (hf : φ (Le μ f) ≠ 0) (t : G) :
    ‖chi μ φ f t‖ = 1 := by
  have hbound : ∀ s, ‖chi μ φ f s‖ ≤ ‖L μ f‖ / ‖φ (Le μ f)‖ := fun s => by
    rw [chi, norm_div]
    exact div_le_div_of_nonneg_right ((norm_char_le μ φ _).trans (norm_Le_transl_le μ s f))
      (norm_nonneg _)
  have hpow : ∀ (s : G) (n : ℕ), chi μ φ f (s ^ n) = chi μ φ f s ^ n := by
    intro s n
    induction n with
    | zero => simp [chi_one μ φ f hf]
    | succ n ih => rw [pow_succ, chi_mul μ φ f hf, ih, pow_succ]
  have hle : ∀ s, ‖chi μ φ f s‖ ≤ 1 := fun s =>
    le_one_of_pow_bounded (M := ‖L μ f‖ / ‖φ (Le μ f)‖) fun n => by
      rw [← norm_pow, ← hpow]; exact hbound _
  refine le_antisymm (hle t) ?_
  have h1 : chi μ φ f t * chi μ φ f t⁻¹ = 1 := by
    rw [← chi_mul μ φ f hf, mul_inv_cancel, chi_one μ φ f hf]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  by_contra h3
  push Not at h3
  have := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h3 (hle t⁻¹) (norm_nonneg _) one_pos
  rw [h2, one_mul] at this
  exact lt_irrefl _ this

/-- The continuous character attached to `φ`. -/
noncomputable def toDual (φ : Δ μ) (f : C_c(G, ℂ)) (hf : φ (Le μ f) ≠ 0) : PontryaginDual G where
  toFun t := ⟨chi μ φ f t, mem_sphere_zero_iff_norm.mpr (norm_chi μ φ f hf t)⟩
  map_one' := Circle.ext (chi_one μ φ f hf)
  map_mul' s t := Circle.ext (chi_mul μ φ f hf s t)
  continuous_toFun := (continuous_chi μ φ f).subtype_mk _

theorem toDual_apply (φ : Δ μ) (f : C_c(G, ℂ)) (hf : φ (Le μ f) ≠ 0) (t : G) :
    ((toDual μ φ f hf t : Circle) : ℂ) = chi μ φ f t := rfl

theorem exists_char_ne_zero (a : Alg μ) (ha : a ≠ 0) : ∃ φ : Δ μ, φ a ≠ 0 := by
  by_contra! h
  apply ha
  apply (gelfandTransform_isometry (Alg μ)).injective
  ext φ
  simp [h φ]

include μ in
/-- **Gelfand–Raikov**: continuous characters separate points of a Hausdorff LCA group. -/
theorem exists_dual_ne_one (g : G) (hg : g ≠ 1) : ∃ χ : PontryaginDual G, χ g ≠ 1 := by
  have hf : ∃ f : C_c(G, ℂ), L μ (transl g f) ≠ L μ f := by
    by_contra! H
    obtain ⟨v, hv⟩ := exists_U_ne μ g hg
    have : (U μ g).toContinuousLinearMap - 1 = 0 := by
      apply eq_zero_of_comp_L
      intro f
      ext1 w
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
        LinearIsometry.coe_toContinuousLinearMap, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.zero_apply]
      rw [U_L_eq, H, sub_self]
    apply hv
    have := congrArg (fun T => T v) this
    simpa [sub_eq_zero] using this
  obtain ⟨f, hf⟩ := hf
  have hne : Le μ (transl g f) - Le μ f ≠ 0 := fun h =>
    hf (congrArg Subtype.val (sub_eq_zero.mp h))
  obtain ⟨φ, hφ⟩ := exists_char_ne_zero μ _ hne
  rw [map_sub] at hφ
  by_cases h0 : φ (Le μ f) = 0
  · exfalso
    have h1 : φ (Le μ (transl g f)) ≠ 0 := by rwa [h0, sub_zero] at hφ
    have := norm_chi μ φ (transl g f) h1 g⁻¹
    rw [chi, ← transl_mul, inv_mul_cancel, transl_one, h0, zero_div, norm_zero] at this
    exact zero_ne_one this
  · refine ⟨toDual μ φ f h0, fun h => hφ ?_⟩
    have := congrArg (fun z : Circle => (z : ℂ)) h
    simp only [toDual_apply, Circle.coe_one] at this
    rw [chi, div_eq_one_iff_eq h0] at this
    rw [this, sub_self]

end MasulloGRHLCACharAux

namespace MasulloGRHLCACharAux

/-- **Gelfand–Raikov** for a Hausdorff locally compact abelian group. -/
theorem exists_pontryaginDual_ne_one {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] (g : G) (hg : g ≠ 1) :
    ∃ χ : PontryaginDual G, χ g ≠ 1 := by
  borelize G
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  exact exists_dual_ne_one (Measure.haarMeasure K₀) g hg

/-- Annihilator separation for closed subgroups of a Hausdorff LCA group. -/
theorem exists_eq_one_on_subgroup_ne_one {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 := by
  have : IsClosed (H : Set G) := hH
  have hne : (QuotientGroup.mk g : G ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_ne_one (G := G ⧸ H) _ hne
  refine ⟨ψ.comp ⟨QuotientGroup.mk' H, continuous_quot_mk⟩, fun h hh => ?_, hψ⟩
  show ψ (QuotientGroup.mk h) = 1
  rw [(QuotientGroup.eq_one_iff h).mpr hh, _root_.map_one]

end MasulloGRHLCACharAux

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 :=
  MasulloGRHLCACharAux.exists_eq_one_on_subgroup_ne_one H hH g hg
