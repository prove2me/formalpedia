-- Prove2me | solution 1 for GlobalTheory.ValMul.value_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:31.833415+00:00
-- url     : https://prove2.me/submissions/9c0f671b-7436-403b-b16e-6ef66a9f1936

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_AbsNormEqProdCmTypeSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IndexRangeMulVecLinEqAbsNormDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetMul
import Theorems.Thm_GlobalTheory_abs_norm_eq_prod_cmType_sq
import Theorems.Thm_GlobalTheory_index_range_mulVecLin_eq_abs_norm_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
namespace GlobalTheory.ValMul
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma det_gram_mul_right_re {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (N : Matrix n ι ℂ) (B : Matrix ι ι ℂ) :
    ((N * B)ᴴ * (N * B)).det.re = Complex.normSq B.det * (Nᴴ * N).det.re := by
  rw [Matrix.conjTranspose_mul,
    show Bᴴ * Nᴴ * (N * B) = Bᴴ * (Nᴴ * N) * B by simp only [Matrix.mul_assoc],
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have h : star B.det * (Nᴴ * N).det * B.det = (Complex.normSq B.det : ℂ) * (Nᴴ * N).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  rw [h, Complex.re_ofReal_mul]
end GlobalTheory.ValMul
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.ValMul
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ValMul
namespace _root_.GlobalTheory.ValMul
theorem _root_.solution : ((∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ∀ A : Matrix ι ι (𝓞 E), A.det ≠ 0 → ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 ((fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 ((fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b))).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)))) := by
  intro r X x ι _ _ w hw hwΛ A hA
  classical
  set w' : ι → Fin r → E := fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b with hw'
  have hsmul : ∀ (c : 𝓞 E) (v : Fin r → E), c • v = (c : E) • v := fun c v => rfl

  have hmat : ∀ τ : X.Ψ, (Matrix.of fun k a => τ.1 (w' a k)) =
      (Matrix.of fun k a => τ.1 (w a k)) * A.map (fun c => τ.1 (c : E)) := by
    intro τ
    ext k a
    simp [Matrix.mul_apply, w', Finset.sum_apply, Algebra.smul_def, mul_comm]
  have hnum : ∀ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w' a k))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w' a k))).det.re) =
      ‖τ.1 (A.det : E)‖ ^ 2 * (((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    intro τ
    rw [hmat τ, ← Matrix.mul_assoc (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹, det_gram_mul_right_re]
    congr 1
    have hd : (A.map fun c => τ.1 (c : E)).det = τ.1 (A.det : E) := by
      have := RingHom.map_det (τ.1.comp (algebraMap (𝓞 E) E)) A
      exact this.symm
    rw [hd, Complex.normSq_eq_norm_sq]
  have hspanE : Submodule.span E (Set.range w') = Submodule.span E (Set.range w) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨c, rfl⟩
      set B : Matrix ι ι E := A.map fun t => (t : E) with hB
      have hBdet : IsUnit B.det := by
        have h := RingHom.map_det (algebraMap (𝓞 E) E) A
        have h0 : ((A.det : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hA
        refine isUnit_iff_ne_zero.mpr ?_
        have hB' : B.det = ((A.det : 𝓞 E) : E) := h.symm
        rw [hB']
        exact h0
      have hrec : ∑ a, B⁻¹ a c • w' a = w c := by
        calc ∑ a, B⁻¹ a c • w' a = ∑ a, ∑ b, (B b a * B⁻¹ a c) • w b := by
              refine Finset.sum_congr rfl fun a _ => ?_
              simp only [w', Finset.smul_sum, smul_smul, hB, Matrix.map_apply, mul_comm]
          _ = ∑ b, (B * B⁻¹) b c • w b := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Matrix.mul_apply, Finset.sum_smul]
          _ = w c := by
              rw [Matrix.mul_nonsing_inv B hBdet]
              simp [Matrix.one_apply]
      rw [← hrec]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hle1 : (Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup ≤
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [← hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hle2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by
    intro v hv
    have hv' : v ∈ Submodule.span (𝓞 E) (Set.range w) := hv
    refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Submodule.span_le.mpr ?_ hv'
      rintro _ ⟨a, rfl⟩
      exact hwΛ a
    · show v ∈ Submodule.span E (Set.range w)
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hv'
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hidx : (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup : ℕ) : ℚ) =
      |Algebra.norm ℚ ((A.det : 𝓞 E) : E)| := by
    let ψ : (ι → 𝓞 E) →+ (Fin r → E) :=
      { toFun := fun c => ∑ b, ((c b : 𝓞 E) : E) • w b
        map_zero' := by simp
        map_add' := by
          intro c d
          simp [add_smul, Finset.sum_add_distrib] }
    have hψ : ∀ c, ψ c = ∑ b, ((c b : 𝓞 E) : E) • w b := fun c => rfl
    have hψinj : Function.Injective ψ := by
      intro c d hcd
      have h0 : ∑ b, (((c b : 𝓞 E) : E) - ((d b : 𝓞 E) : E)) • w b = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hψ, ← hψ]
        exact sub_eq_zero.mpr hcd
      funext b
      have := Fintype.linearIndependent_iff.mp hw _ h0 b
      exact RingOfIntegers.coe_injective (sub_eq_zero.mp this)
    have hψmem : ∀ c, ψ c ∈ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup := by
      intro c
      show ψ c ∈ Submodule.span (𝓞 E) (Set.range w)
      rw [hψ]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [← hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    let φ : (ι → 𝓞 E) →+ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup :=
      ψ.codRestrict _ hψmem
    have hφsurj : Function.Surjective φ := by
      rintro ⟨v, hv⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hv
      refine ⟨c, Subtype.ext ?_⟩
      show ψ c = _
      rw [hψ]
      exact Finset.sum_congr rfl fun b _ => (hsmul (c b) (w b)).symm
    have hlin : ∀ v : ι → 𝓞 E, ∑ a, v a • w' a = ψ (A.mulVec v) := by
      intro v
      rw [hψ]
      calc ∑ a, v a • w' a = ∑ a, ∑ b, (((A b a : 𝓞 E) : E) * ((v a : 𝓞 E) : E)) • w b := by
            refine Finset.sum_congr rfl fun a _ => ?_
            simp only [w', hsmul, Finset.smul_sum, smul_smul, mul_comm]
        _ = ∑ b, ((A.mulVec v b : 𝓞 E) : E) • w b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            simp only [Matrix.mulVec, dotProduct]
            push_cast
            rw [Finset.sum_smul]
    have hcomap : ((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup).comap φ =
        (LinearMap.range A.mulVecLin).toAddSubgroup := by
      ext c
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      show ψ c ∈ Submodule.span (𝓞 E) (Set.range w') ↔ c ∈ LinearMap.range A.mulVecLin
      rw [Submodule.mem_span_range_iff_exists_fun, LinearMap.mem_range]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨v, hψinj (by rw [Matrix.mulVecLin_apply, ← hlin]; exact hv)⟩
      · rintro ⟨v, rfl⟩
        exact ⟨v, hlin v⟩
    rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφsurj, hcomap]
    exact _root_.GlobalTheory.index_range_mulVecLin_eq_abs_norm_det ι A hA
  have hidxR : (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup : ℕ) : ℝ) =
      ((|Algebra.norm ℚ ((A.det : 𝓞 E) : E)| : ℚ) : ℝ) := by
    exact_mod_cast hidx
  have hN : ((|Algebra.norm ℚ ((A.det : 𝓞 E) : E)| : ℚ) : ℝ) ≠ 0 := by
    have h0 : ((A.det : 𝓞 E) : E) ≠ 0 := by
      exact_mod_cast hA
    have := (Algebra.norm_ne_zero_iff (R := ℚ)).mpr h0
    positivity
  rw [Finset.prod_congr rfl (fun τ _ => hnum τ), Finset.prod_mul_distrib,
    ← _root_.GlobalTheory.abs_norm_eq_prod_cmType_sq r X, hspanE, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2,
    Nat.cast_mul, hidxR, mul_div_mul_left _ _ hN]
end _root_.GlobalTheory.ValMul
end GlobalTheory.ValMul
