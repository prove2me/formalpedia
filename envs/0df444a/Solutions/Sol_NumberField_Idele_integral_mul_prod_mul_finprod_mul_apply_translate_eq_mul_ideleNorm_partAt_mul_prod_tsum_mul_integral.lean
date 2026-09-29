-- Prove2me | solution 1 for NumberField.Idele.integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4871a551-d1e4-552e-a3f4-7f1bcd3ce0ee

import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_Idele_integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

namespace C1K25

variable (K : Type) [Field K] [NumberField K]

theorem norm_eq_one_iff_valued (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    ‖x‖ = 1 ↔ Valued.v x = 1 := by
  constructor
  · intro h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mp h.le
    · exact Valued.toNormedField.one_le_norm_iff.mp h.ge
  · intro h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mpr h.le
    · exact Valued.toNormedField.one_le_norm_iff.mpr h.ge

theorem ord_eq_zero_iff_norm (v : HeightOneSpectrum (𝓞 K)) (w : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.Idele.ord K v w = 0 ↔ ‖((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
  rw [norm_eq_one_iff_valued, NumberField.Idele.valued_snd_eq_exp_neg_ord, ← WithZero.exp_zero,
    WithZero.exp_inj]
  omega

theorem mem_unitIdelesOutside_iff_norm (S : Set (HeightOneSpectrum (𝓞 K))) (w : (AdeleRing (𝓞 K) K)ˣ) :
    w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K S ↔
      ∀ v ∉ S, ‖((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall₂_congr fun v _ => ?_
  rw [IsDedekindDomain.FiniteAdeleRing.integer_and_inv_integer_iff_valuation_eq_one, norm_eq_one_iff_valued]
  rfl

theorem finite_mulSupport_norm_snd (a : (AdeleRing (𝓞 K) K)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖).Finite := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K :=
    ((a : AdeleRing (𝓞 K) K).2).2
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K :=
    (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2).2
  have h := Filter.eventually_cofinite.mp (h1.and h2)
  refine h.subset fun v hv => ?_
  simp only [Set.mem_setOf_eq]
  intro hcon
  obtain ⟨hi, hi'⟩ := hcon
  apply hv
  have hle : ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hi
  have hle' : ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hi'
  have hmul : ((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
      (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
    have h2 := congrArg (fun x : AdeleRing (𝓞 K) K => (x.2 : FiniteAdeleRing (𝓞 K) K) v) a.mul_inv
    exact h2
  have hnm : ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ *
      ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  show ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1
  nlinarith [norm_nonneg (((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v),
    norm_nonneg ((((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)]

theorem snd_principal (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = algebraMap K (v.adicCompletion K) (a : K) := rfl

theorem finite_bad [DecidableEq (HeightOneSpectrum (𝓞 K))] (S T : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (w : (AdeleRing (𝓞 K) K)ˣ) (IU : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hUloc : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      IU w v = if ‖(((w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 ∧
          ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1
        then (((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ))⁻¹ else 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => if v ∉ S ∪ T then IU w v else 1).Finite := by
  have h1 : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have hA := finite_mulSupport_norm_snd K w
  have hB := finite_mulSupport_norm_snd K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)
  have hC := finite_mulSupport_norm_snd K
    (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))
  refine ((hA.union hB).union hC).subset fun v hv => ?_
  simp only [Function.mem_mulSupport, Set.mem_union] at hv ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨hA1, hB1⟩, hC1⟩ := hcon
  rw [snd_principal] at hB1 hC1
  simp only [Units.val_mk0, map_sub, map_one] at hC1
  apply hv
  by_cases hvm : v ∉ S ∪ T
  · rw [if_pos hvm]
    rw [Finset.mem_union, not_or] at hvm
    rw [hUloc v hvm.1 hvm.2 w, if_pos ⟨hA1, hB1⟩, hC1]
    simp
  · rw [if_neg hvm]

open scoped Classical in
theorem main [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (d : Kˣ)
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (IW : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (IU : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (B : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (IT : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hWloc : ∀ v ∈ T, ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →
      IW w v = IT v (NumberField.Idele.ord K v w))
    (hUloc : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      IU w v = if ‖(((w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 ∧ ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1
        then (((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ))⁻¹ else 0)
    (hBloc : ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →
      B w = B (NumberField.Idele.partAt K S w))
    (hBint : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * B zS) PZ.νS)
    (hITsum : ∀ v ∈ T, Summable fun e : ℤ =>
      ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e‖) :
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∏ v ∈ T, IW (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d)) v) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S ∪ T), IU (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d)) v) *
          B (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d))) ∂νZK =
      (PZ.c : ℂ) *
        (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
          then (1 : ℂ) else 0) *
        (if h1 : (u : K) - 1 ≠ 0 then
            ((NumberField.TateGlobal.ideleNorm K
                (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
          else 0) *
        (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
            ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e *
              IT v e) *
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * B zS ∂PZ.νS := by
  classical
  set dA : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d with hdA
  have huAv : ∀ v : HeightOneSpectrum (𝓞 K), (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
      algebraMap K (v.adicCompletion K) (u : K) := fun v => rfl

  have h1 : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu1
  set a1 : Kˣ := Units.mk0 ((u : K) - 1) h1 with ha1
  set nU : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    if v ∈ S ∪ T then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (a1 : K)‖ with hnU
  have hnUv : ∀ v ∉ S ∪ T, nU v = ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ := by
    intro v hv; simp only [hnU, if_neg hv, ha1, Units.val_mk0, map_sub, map_one]
  set N₀ : ℝ := ∏ᶠ v, nU v with hN₀
  have hFE : NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a1)) *
      (∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (a1 : K)‖) * N₀ = 1 :=
    NumberField.TateGlobal.ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one K S T hTS a1
  have hN₀ne : N₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hFE; exact zero_ne_one hFE

  have hnUfin : (Function.mulSupport nU).Finite := by
    have hC := finite_mulSupport_norm_snd K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a1)
    refine hC.subset fun v hv => ?_
    simp only [Function.mem_mulSupport] at hv ⊢
    intro hcon
    apply hv
    simp only [hnU]
    split_ifs with hvm
    · rfl
    · rw [snd_principal] at hcon; exact hcon
  set U : Set (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) :
      Set (AdeleRing (𝓞 K) K)ˣ) with hU
  set G : (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    U.indicator (fun w => B (NumberField.Idele.partAt K S w) * ∏ v ∈ T, IT v (NumberField.Idele.ord K v w)) with hGdef
  set cU : ℂ := (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
    then (1 : ℂ) else 0) with hcU
  set C : ℂ := ((N₀⁻¹ : ℝ) : ℂ) with hC

  have key : ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      (∏ v ∈ T, IW w v) * (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S ∪ T), IU w v) * B w = C * cU * G w := by
    intro w

    have hfp : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S ∪ T), IU w v) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), (if v ∉ S ∪ T then IU w v else 1) := by
      refine finprod_congr fun v => ?_
      exact finprod_eq_if
    have hfin := finite_bad K S T u hu1 w IU hUloc
    by_cases hgood : w ∈ U ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
    ·

      obtain ⟨hzU, hu0⟩ := hgood
      have hcU1 : cU = 1 := by simp only [hcU, if_pos hu0]
      have hGz : G w = B (NumberField.Idele.partAt K S w) * ∏ v ∈ T, IT v (NumberField.Idele.ord K v w) := by
        simp only [hGdef, Set.indicator_of_mem hzU]
      have hzU' : ∀ v ∉ S ∪ T, ‖((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
        intro v hv
        exact (mem_unitIdelesOutside_iff_norm K _ w).mp hzU v (by simpa using hv)
      have huv : ∀ v ∉ S ∪ T, ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1 := by
        intro v hv
        rw [Finset.mem_union, not_or] at hv
        rw [← huAv, ← ord_eq_zero_iff_norm]
        exact hu0 v hv.1 hv.2

      have hT : ∏ v ∈ T, IW w v = ∏ v ∈ T, IT v (NumberField.Idele.ord K v w) :=
        Finset.prod_congr rfl fun v hv => hWloc v hv w hzU
      have hBw : B w = B (NumberField.Idele.partAt K S w) := hBloc w hzU

      have hUprod : (∏ᶠ v : HeightOneSpectrum (𝓞 K), (if v ∉ S ∪ T then IU w v else 1)) =
          ∏ᶠ v : HeightOneSpectrum (𝓞 K), (((nU v)⁻¹ : ℝ) : ℂ) := by
        refine finprod_congr fun v => ?_
        by_cases hvm : v ∉ S ∪ T
        · rw [if_pos hvm, hnUv v hvm]
          have hvm' := hvm
          rw [Finset.mem_union, not_or] at hvm'
          rw [hUloc v hvm'.1 hvm'.2 w, if_pos ⟨hzU' v hvm, huv v hvm⟩, Complex.ofReal_inv]
        · rw [if_neg hvm]
          have : nU v = 1 := by simp only [hnU]; rw [if_pos (not_not.mp hvm)]
          rw [this, inv_one, Complex.ofReal_one]
      have hcast : (∏ᶠ v : HeightOneSpectrum (𝓞 K), (((nU v)⁻¹ : ℝ) : ℂ)) = ((N₀⁻¹ : ℝ) : ℂ) := by
        have hfin' : (Function.mulSupport fun v => (nU v)⁻¹).Finite := by
          refine hnUfin.subset fun v hv => ?_
          simp only [Function.mem_mulSupport] at hv ⊢
          intro h; apply hv; rw [h, inv_one]
        have e1 : (∏ᶠ v : HeightOneSpectrum (𝓞 K), (nU v)⁻¹ : ℝ) = N₀⁻¹ := by
          rw [hN₀]; exact finprod_inv_distrib _
        have e2 := (Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom.map_finprod hfin'
        rw [← e1]
        exact e2.symm
      rw [hfp, hUprod, hcast, hT, hBw, hcU1, mul_one, hGz, hC]
      ring
    ·

      have hR : C * cU * G w = 0 := by
        rcases not_and_or.mp hgood with hzU | hu0
        · simp only [hGdef, Set.indicator_of_notMem hzU, mul_zero]
        · simp only [hcU, if_neg hu0, mul_zero, zero_mul]
      rw [hR]
      have hbad : ∃ v₀, v₀ ∉ S ∪ T ∧
          ¬ (‖((w : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v₀‖ = 1 ∧
             ‖algebraMap K (v₀.adicCompletion K) (u : K)‖ = 1) := by
        by_contra hcon
        push Not at hcon
        apply hgood
        constructor
        · rw [hU, SetLike.mem_coe, mem_unitIdelesOutside_iff_norm]
          intro v hv
          exact (hcon v (by simpa using hv)).1
        · intro v hvS hvT
          rw [ord_eq_zero_iff_norm, huAv]
          exact (hcon v (by simp [hvS, hvT])).2
      obtain ⟨v₀, hv₀, hv₀bad⟩ := hbad
      have hIU0 : (if v₀ ∉ S ∪ T then IU w v₀ else 1) = 0 := by
        rw [if_pos hv₀]
        have hv₀' := hv₀
        rw [Finset.mem_union, not_or] at hv₀'
        rw [hUloc v₀ hv₀'.1 hv₀'.2 w, if_neg hv₀bad]
      have hP0 : (∏ᶠ v : HeightOneSpectrum (𝓞 K), (if v ∉ S ∪ T then IU w v else 1)) = 0 :=
        finprod_eq_zero _ v₀ hIU0 hfin
      rw [hfp, hP0, mul_zero, zero_mul]

  have hint : ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∏ v ∈ T, IW (z * dA) v) * (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S ∪ T), IU (z * dA) v) *
          B (z * dA)) ∂νZK =
      C * cU * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * G (z * dA) ∂νZK := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [key (z * dA)]; ring
  have hC0 := NumberField.Idele.integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
    K νZK ξ hξc hξt S T hTS hur PZ hPo hPp d B hBint IT hITsum
  rw [hint]
  erw [hC0]

  rw [dif_pos h1]
  have hN₀inv : (N₀⁻¹ : ℝ) = NumberField.TateGlobal.ideleNorm K
      (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a1)) *
      ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ := by
    have hT' : ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (a1 : K)‖ =
        ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ := by
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [ha1, Units.val_mk0, map_sub, map_one]
    rw [← hT']
    field_simp
    linarith [hFE]
  have hprodT : ∏ v ∈ T, (((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
      ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e) =
      ((∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
      ∏ v ∈ T, ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e := by
    rw [Finset.prod_mul_distrib]; push_cast; rfl
  rw [hprodT]
  simp only [hC]
  rw [hN₀inv]
  push_cast
  ring

end C1K25

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (d : Kˣ)

    (u : Kˣ) (hu1 : (u : K) ≠ 1)

    (IW : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (IU : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (B : (AdeleRing (𝓞 K) K)ˣ → ℂ)

    (IT : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hWloc : ∀ v ∈ T, ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →
      IW w v = IT v (NumberField.Idele.ord K v w))

    (hUloc : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      IU w v = if ‖(((w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 ∧ ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1
        then (((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ))⁻¹ else 0)

    (hBloc : ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →
      B w = B (NumberField.Idele.partAt K S w))

    (hBint : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * B zS) PZ.νS)

    (hITsum : ∀ v ∈ T, Summable fun e : ℤ =>
      ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e‖) :
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∏ v ∈ T, IW (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d)) v) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S ∪ T), IU (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d)) v) *
          B (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d))) ∂νZK =
      (PZ.c : ℂ) *
        (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
          then (1 : ℂ) else 0) *
        (if h1 : (u : K) - 1 ≠ 0 then
            ((NumberField.TateGlobal.ideleNorm K
                (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
          else 0) *
        (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
            ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e *
              IT v e) *
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * B zS ∂PZ.νS :=
  C1K25.main K νZK ξ hξc hξt S T hTS hur PZ hPo hPp d u hu1 IW IU B IT hWloc hUloc hBloc hBint hITsum

end S_NumberField_Idele_integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral
end P2MW
export P2MW.S_NumberField_Idele_integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral (solution)
