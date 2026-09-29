-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e53f695f-2681-592e-a5e1-f8cc199dfda0

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_LanglandsTunnell_DeltaLift

import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField NumberField.AdelicLevel NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField.AdelicFourier IsDedekindDomain AutomorphicForm LanglandsTunnell"
open scoped Classical

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing IsTotallyReal.isReal InfinitePlace.not_isComplex_iff_isReal place mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace_apply InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace IsTotallyReal AdeleRing AdelicBox.integralFiniteAdeles AdelicBox.isCompact_integralFiniteAdeles"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "schwartzBruhat2 tensor_mem_pureTensorSet2 mem_schwartzBruhat2_of_mem_pureTensorSet2"
namespace SB2Tensor
p2m_open "NumberField.AdelicFourier NumberField"

p2m_open "MeasureTheory NumberField.InfinitePlace"

scoped instance : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩

scoped instance instUniqueRealPlaces : Unique {w : InfinitePlace ℚ // w.IsReal} :=
  { default := ⟨default, IsTotallyReal.isReal _⟩, uniq := fun a => Subsingleton.elim _ _ }

def coordEquiv : mixedEmbedding.mixedSpace ℚ ≃ₗ[ℝ] ℝ :=
  (LinearEquiv.prodUnique).trans (LinearEquiv.funUnique {w : InfinitePlace ℚ // w.IsReal} ℝ ℝ)

theorem coordEquiv_apply (y : mixedEmbedding.mixedSpace ℚ) :
    coordEquiv y = y.1 ⟨default, IsTotallyReal.isReal _⟩ := by
  have h : (default : {w : InfinitePlace ℚ // w.IsReal}) = ⟨default, IsTotallyReal.isReal _⟩ := Subsingleton.elim _ _
  simp [coordEquiv, LinearEquiv.prodUnique, LinearEquiv.funUnique, h]

def pairEquiv : (Fin 2 → mixedEmbedding.mixedSpace ℚ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((LinearEquiv.piCongrRight fun _ : Fin 2 => coordEquiv).trans
    (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.symm).toContinuousLinearEquiv

theorem pairEquiv_apply (y : Fin 2 → mixedEmbedding.mixedSpace ℚ) (i : Fin 2) :
    (pairEquiv y).ofLp i = (y i).1 ⟨default, IsTotallyReal.isReal _⟩ := by
  simp [pairEquiv, LinearEquiv.piCongrRight, coordEquiv_apply]

theorem exists_schwartz_gaussian :
    ∃ ga : SchwartzMap (Fin 2 → mixedEmbedding.mixedSpace ℚ) ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ga (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace ℚ
            (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 i).1)) =
        (Real.exp (-(Real.pi *
          (((ratArchGL2 g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((ratArchGL2 g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2))) : ℂ) := by
  obtain ⟨g0, hg0⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin 2)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ pairEquiv g0, fun g => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  congr 1
  congr 1; congr 1; congr 1
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs, pairEquiv_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (m : HeightOneSpectrum (𝓞 ℚ) → ℕ)

def boxProp (z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) : Prop :=
  (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2, Valued.v ((z j) p) ≤ 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
      Valued.v ((z 0) p) ≤ WithZero.exp (-(m p : ℤ)) ∧ Valued.v ((z 1) p - 1) ≤ WithZero.exp (-(m p : ℤ)))

theorem isClopen_ball (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    IsClopen {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(n : ℤ))} := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  set a : p.adicCompletion ℚ := (((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation ℚ p)).symm π :
    WithVal (IsDedekindDomain.HeightOneSpectrum.valuation ℚ p)) : p.adicCompletion ℚ) ^ n with ha
  have hva : Valued.v a = WithZero.exp (-(n : ℤ)) := by
    rw [ha, map_pow, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_nsmul]
    simp
  have ha0 : Valued.v.restrict a ≠ 0 := by
    intro h
    have : Valued.v a = 0 := by
      have := (Valuation.restrict_le_iff Valued.v (x := a) (y := 0)).mp (by rw [h]; exact zero_le')
      simpa using this
    rw [hva] at this
    exact WithZero.coe_ne_zero this
  have hset : {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(n : ℤ))} =
      {x | Valued.v.restrict x ≤ Valued.v.restrict a} := by
    ext x; simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, hva]
  rw [hset]
  exact Valued.isClopen_closedBall _ ha0

theorem isClopen_boxProp : IsClopen {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ | boxProp S m z} := by
  have hev : ∀ (j : Fin 2) (p : HeightOneSpectrum (𝓞 ℚ)),
      Continuous fun z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => (z j) p :=
    fun j p => (RestrictedProduct.continuous_eval p).comp (continuous_apply j)

  have hoff : IsClopen {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ |
      ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2, Valued.v ((z j) p) ≤ 1} := by
    have hO : ∀ j : Fin 2, IsClopen {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ |
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → (z j).1 p ∈ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))} := by
      intro j
      have hOc : ∀ p : HeightOneSpectrum (𝓞 ℚ), IsClosed (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) :=
        fun p => (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (p.adicCompletionIntegers ℚ)))).isClosed
      constructor
      · have : {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ |
            ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → (z j).1 p ∈ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))} =
            ⋂ p ∈ (Sᶜ : Set (HeightOneSpectrum (𝓞 ℚ))), (fun z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => (z j) p) ⁻¹'
              (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe, SetLike.mem_coe]
          rfl
        rw [this]
        exact isClosed_biInter fun p _ => (hOc p).preimage (hev j p)
      · have h := (RestrictedProduct.isOpen_forall_imp_mem
          (R := fun p : HeightOneSpectrum (𝓞 ℚ) => p.adicCompletion ℚ)
          (A := fun p : HeightOneSpectrum (𝓞 ℚ) => (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)))
          Fact.out (p := fun p => p ∉ S)).preimage (continuous_apply (A := fun _ : Fin 2 => FiniteAdeleRing (𝓞 ℚ) ℚ) j)
        exact h
    have : {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2, Valued.v ((z j) p) ≤ 1} =
        ⋂ j : Fin 2, {z | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → (z j).1 p ∈ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact ⟨fun h j p hp => h p hp j, fun h p hp j => h j p hp⟩
    rw [this]
    exact isClopen_iInter_of_finite hO
  have hon : IsClopen {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
      Valued.v ((z 0) p) ≤ WithZero.exp (-(m p : ℤ)) ∧ Valued.v ((z 1) p - 1) ≤ WithZero.exp (-(m p : ℤ))} := by
    have : {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
        Valued.v ((z 0) p) ≤ WithZero.exp (-(m p : ℤ)) ∧ Valued.v ((z 1) p - 1) ≤ WithZero.exp (-(m p : ℤ))} =
        ⋂ p ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))),
          ((fun z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => (z 0) p) ⁻¹' {x | Valued.v x ≤ WithZero.exp (-(m p : ℤ))} ∩
           (fun z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => (z 1) p - 1) ⁻¹' {x | Valued.v x ≤ WithZero.exp (-(m p : ℤ))}) := by
      ext z; simp
    rw [this]
    exact isClopen_biInter_finset fun p _ =>
      ((isClopen_ball p (m p)).preimage (hev 0 p)).inter ((isClopen_ball p (m p)).preimage ((hev 1 p).sub continuous_const))
  have : {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ | boxProp S m z} =
      {z | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2, Valued.v ((z j) p) ≤ 1} ∩
      {z | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
        Valued.v ((z 0) p) ≤ WithZero.exp (-(m p : ℤ)) ∧ Valued.v ((z 1) p - 1) ≤ WithZero.exp (-(m p : ℤ))} := by
    ext z; simp [boxProp]
  rw [this]
  exact hoff.inter hon

theorem boxProp_subset :
    {z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ | boxProp S m z} ⊆
      Set.pi Set.univ fun _ => NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro j p
  show Valued.v ((z j) p) ≤ 1
  by_cases hp : p ∈ S
  · obtain ⟨ha, hb⟩ := h2 p hp
    have hle : WithZero.exp (-(m p : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)
    fin_cases j
    · exact ha.trans hle
    · have h1' : Valued.v ((z 1) p - 1) ≤ 1 := hb.trans hle
      have := Valuation.map_add Valued.v ((z 1) p - 1) 1
      rw [sub_add_cancel, map_one] at this
      exact this.trans (max_le h1' le_rfl)
  · exact h1 p hp j

open scoped Classical in
theorem isLocallyConstant_hasCompactSupport_indicator :
    IsLocallyConstant (fun z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => if boxProp S m z then (1 : ℂ) else 0) ∧
      HasCompactSupport (fun z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => if boxProp S m z then (1 : ℂ) else 0) := by
  have hc := isClopen_boxProp S m
  constructor
  · intro s
    have : (fun z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => if boxProp S m z then (1 : ℂ) else 0) ⁻¹' s =
        (if (1 : ℂ) ∈ s then {z | boxProp S m z} else ∅) ∪ (if (0 : ℂ) ∈ s then {z | boxProp S m z}ᶜ else ∅) := by
      ext z
      by_cases hz : boxProp S m z <;> by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;> simp [hz, h1, h0]
    rw [this]
    refine IsOpen.union ?_ ?_
    · split_ifs; exacts [hc.isOpen, isOpen_empty]
    · split_ifs; exacts [hc.compl.isOpen, isOpen_empty]
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_univ_pi fun _ => NumberField.AdelicBox.isCompact_integralFiniteAdeles ℚ) ?_
    intro z hz
    have hz' : boxProp S m z := by
      by_contra h
      simp [h] at hz
    exact boxProp_subset S m hz'

end NumberField.AdelicFourier.SB2Tensor
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField.AdelicFourier.SB2Tensor"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField.AdelicFourier"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat.NumberField.AdelicFourier.SB2Tensor"

open NumberField.AdelicFourier.SB2Tensor in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (m : HeightOneSpectrum (𝓞 ℚ) → ℕ) :
    ∃ Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Φ ∈ schwartzBruhat2 ℚ ∧
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Φ (bottomRowVec ℚ g 1) =
          (Real.exp (-(Real.pi *
              (((ratArchGL2 g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((ratArchGL2 g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2))) : ℂ) *
          (if (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
              (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤ WithZero.exp (-(m p : ℤ)) ∧
                Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤ WithZero.exp (-(m p : ℤ)))
            then (1 : ℂ) else 0) := by
  classical
  obtain ⟨ga, hga⟩ := exists_schwartz_gaussian
  obtain ⟨hlc, hcs⟩ := isLocallyConstant_hasCompactSupport_indicator S m
  refine ⟨fun x => ga (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (x i).1) *
      (fun z : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => if boxProp S m z then (1 : ℂ) else 0) (fun i => (x i).2),
    mem_schwartzBruhat2_of_mem_pureTensorSet2 (tensor_mem_pureTensorSet2 ga _ hlc hcs), fun g => ?_⟩
  simp only [bottomRowVec, one_mul]
  rw [hga g]
  congr 1
  by_cases hP : boxProp S m (fun i => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 i).2)
  · have hP' := hP
    simp only [boxProp] at hP'
    rw [if_pos hP, if_pos hP']
  · have hP' := hP
    simp only [boxProp] at hP'
    rw [if_neg hP, if_neg hP']

#print axioms solution

end S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat (solution)
