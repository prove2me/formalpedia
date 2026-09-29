-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/104d4fc0-1456-53c2-adf4-7fdcec18da24

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg MeasureTheory

noncomputable section

namespace P2mGoodPrimeLaw

section Plumbing

def ent (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2

theorem finite_setOf_not_mem_integers (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    {v : HeightOneSpectrum (𝓞 ℚ) | a v ∉ v.adicCompletionIntegers ℚ}.Finite :=
  Filter.eventually_cofinite.mp a.2

theorem componentAt3_coe_apply (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((componentAt3 (𝓞 ℚ) ℚ v g : GL (Fin 3) (v.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = ent g i j v := rfl

theorem componentAt3_inv_coe_apply (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    (((componentAt3 (𝓞 ℚ) ℚ v g)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = ent g⁻¹ i j v := by
  rw [← map_inv]
  rfl

theorem componentAt3_mem_localMaximalCompact3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (h₁ : ∀ i j, ent g i j v ∈ v.adicCompletionIntegers ℚ)
    (h₂ : ∀ i j, ent g⁻¹ i j v ∈ v.adicCompletionIntegers ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [componentAt3_coe_apply, ← HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h₁ i j
  · rw [componentAt3_inv_coe_apply, ← HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h₂ i j

theorem finite_setOf_exists_ent_not_mem (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ∃ i j, ent g i j v ∉ v.adicCompletionIntegers ℚ ∨
      ent g⁻¹ i j v ∉ v.adicCompletionIntegers ℚ}.Finite := by
  have : {v : HeightOneSpectrum (𝓞 ℚ) | ∃ i j, ent g i j v ∉ v.adicCompletionIntegers ℚ ∨
      ent g⁻¹ i j v ∉ v.adicCompletionIntegers ℚ} ⊆
      ⋃ i : Fin 3, ⋃ j : Fin 3, ({v | ent g i j v ∉ v.adicCompletionIntegers ℚ} ∪
        {v | ent g⁻¹ i j v ∉ v.adicCompletionIntegers ℚ}) := by
    rintro v ⟨i, j, h⟩
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq]
    exact ⟨i, j, h⟩
  refine Set.Finite.subset ?_ this
  exact Set.finite_iUnion fun i => Set.finite_iUnion fun j =>
    (finite_setOf_not_mem_integers _).union (finite_setOf_not_mem_integers _)

variable (v : HeightOneSpectrum (𝓞 ℚ))

def idl (x : (v.adicCompletion ℚ)ˣ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v x)

theorem localChar_eq_apply_idl (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (x : (v.adicCompletion ℚ)ˣ) :
    localChar χ v x = χ (idl v x) := rfl

abbrev sc (x : (v.adicCompletion ℚ)ˣ) : GL (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) x

theorem sc_coe_apply (x : (v.adicCompletion ℚ)ˣ) (i j : Fin 3) :
    ((sc v x : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
      if i = j then (x : v.adicCompletion ℚ) else 0 := by
  show (Matrix.scalar (Fin 3) (x : v.adicCompletion ℚ)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem centralScalarGL_coe_apply (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (i j : Fin 3) :
    ((centralScalarGL 3 (𝓞 ℚ) ℚ z : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      if i = j then (z : AdeleRing (𝓞 ℚ) ℚ) else 0 := by
  show (Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem componentAt3_centralScalarGL_idl_self (x : (v.adicCompletion ℚ)ˣ) :
    componentAt3 (𝓞 ℚ) ℚ v (centralScalarGL 3 (𝓞 ℚ) ℚ (idl v x)) = sc v x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sc_coe_apply]
  show ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ))
      (((centralScalarGL 3 (𝓞 ℚ) ℚ (idl v x) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) = _
  rw [centralScalarGL_coe_apply]
  split_ifs with h
  · show ((localUnit (𝓞 ℚ) ℚ v x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = x
    exact localUnit_apply_self (𝓞 ℚ) ℚ v x
  · exact map_zero _

theorem componentAt3_centralScalarGL_idl_of_ne (x : (v.adicCompletion ℚ)ˣ) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ v) : componentAt3 (𝓞 ℚ) ℚ w (centralScalarGL 3 (𝓞 ℚ) ℚ (idl v x)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show ((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ))
      (((centralScalarGL 3 (𝓞 ℚ) ℚ (idl v x) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) = _
  rw [centralScalarGL_coe_apply, Units.val_one]
  split_ifs with h
  · subst h
    rw [Matrix.one_apply_eq]
    show ((localUnit (𝓞 ℚ) ℚ v x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1
    exact localUnit_apply_of_ne (𝓞 ℚ) ℚ v x hw
  · rw [Matrix.one_apply_ne h]
    exact map_zero _

theorem archComponent3_centralScalarGL_idl (x : (v.adicCompletion ℚ)ˣ) :
    archComponent3 (𝓞 ℚ) ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (idl v x)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show (adeleArch (𝓞 ℚ) ℚ)
      (((centralScalarGL 3 (𝓞 ℚ) ℚ (idl v x) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) = _
  rw [centralScalarGL_coe_apply, Units.val_one]
  split_ifs with h
  · subst h
    rw [Matrix.one_apply_eq]
    rfl
  · rw [Matrix.one_apply_ne h]
    exact map_zero _

theorem sc_mem_localMaximalCompact3 (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    sc v u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have key : ∀ (t : (v.adicCompletion ℚ)ˣ), Valued.v (t : v.adicCompletion ℚ) = 1 →
      ∀ i j, Valued.v (((sc v t : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 := by
    intro t ht i j
    rw [sc_coe_apply]
    split_ifs
    · exact ht.le
    · rw [map_zero]
      exact zero_le'
  refine ⟨key u hu, ?_⟩
  have hinv : (sc v u)⁻¹ = sc v u⁻¹ := (map_inv _ _).symm
  rw [hinv]
  refine key u⁻¹ ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem sc_mul_comm (x : (v.adicCompletion ℚ)ˣ) (h : GL (Fin 3) (v.adicCompletion ℚ)) :
    sc v x * h = h * sc v x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (x : v.adicCompletion ℚ) (fun r' => Commute.all _ r') _).eq

theorem sc_uniformizerUnit_eq_centralGen : sc v (uniformizerUnit ℚ v) = centralGen v := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sc_coe_apply, centralGen, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.diagonal_apply]
  split_ifs with h
  · fin_cases i <;> rfl
  · rfl

theorem centralScalarGL_mul_comm (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    centralScalarGL 3 (𝓞 ℚ) ℚ z * g = g * centralScalarGL 3 (𝓞 ℚ) ℚ z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 ℚ) ℚ) (fun r' => Commute.all _ r') _).eq

end Plumbing

section Whittaker

variable {K : Type} [Field K] [NumberField K]
  {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  {pins : CarrierPins ℚ} (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X)
include X hX

theorem exists_whittaker_ne_zero (hF : X.form ≠ 0) : ∃ g, X.whittaker g ≠ 0 := by
  by_contra h
  push Not at h
  apply hF
  funext g
  have hs := hX.expansion g
  have h0 : (fun i : MirabolicIndex ℚ => X.whittaker (mirabolicTranslate i * g)) = fun _ => 0 :=
    funext fun i => h _
  rw [h0] at hs
  exact (hs.unique hasSum_zero)

theorem whittaker3_centralScalarGL_mul (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ X.form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
      ((X.centralChar z : ℂˣ) : ℂ) * whittaker3 pins ψ X.form g := by
  letI := pins.nS
  simp only [whittaker3]
  have hcomm : ∀ x y w : AdeleRing (𝓞 ℚ) ℚ,
      X.form (upperUnipotent3 x y w * (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) * ψ (-(x + y)) =
        ((X.centralChar z : ℂˣ) : ℂ) * (X.form (upperUnipotent3 x y w * g) * ψ (-(x + y))) := by
    intro x y w
    rw [← mul_assoc, ← centralScalarGL_mul_comm, mul_assoc, hX.central z, mul_assoc]
  simp_rw [hcomm, integral_const_mul]

theorem whittaker_centralScalarGL_mul (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    X.whittaker (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = ((X.centralChar z : ℂˣ) : ℂ) * X.whittaker g := by
  rw [hX.whittaker_eq, hX.whittaker_eq, whittaker3_centralScalarGL_mul X hX]

end Whittaker

end P2mGoodPrimeLaw

end

open P2mGoodPrimeLaw in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (hF : X.form ≠ 0)
    (T₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT₀ : ∀ v, IsBadPlace K μ v → v ∈ T₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v) :
    (∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        localChar X.centralChar v u = 1) ∧
      ((localChar X.centralChar v (uniformizerUnit ℚ v) : ℂˣ) : ℂ) =
        inducedE3 ℚ (inducedCoeff K μ) v := by
  classical

  obtain ⟨g₀, hg₀⟩ := exists_whittaker_ne_zero X hX hF

  have hbad := finite_setOf_exists_ent_not_mem g₀
  let T : Finset (HeightOneSpectrum (𝓞 ℚ)) := T₀ ∪ {v} ∪ hbad.toFinset
  have hvT : v ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self v))
  have hT₀T : ∀ w, IsBadPlace K μ w → w ∈ T := fun w hw =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (hT₀ w hw))
  have hint : ∀ w, w ∉ T → componentAt3 (𝓞 ℚ) ℚ w g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
    intro w hw
    have hw' : w ∉ hbad.toFinset := fun h => hw (Finset.mem_union_right _ h)
    rw [Set.Finite.mem_toFinset] at hw'
    simp only [Set.mem_setOf_eq, not_exists, not_or, not_not] at hw'
    exact componentAt3_mem_localMaximalCompact3 w g₀ (fun i j => (hw' i j).1) (fun i j => (hw' i j).2)

  set h : GL (Fin 3) (v.adicCompletion ℚ) := componentAt3 (𝓞 ℚ) ℚ v g₀ with hhdef
  set A : ℂ := X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g₀) with hAdef
  set B : ℂ := ∏ w ∈ T \ {v}, X.whittakerLoc w (componentAt3 (𝓞 ℚ) ℚ w g₀) with hBdef

  have hfac0 : X.whittaker g₀ = A * (X.whittakerLoc v h * B) := by
    rw [hX.factorizable g₀ T hT₀T hint, Finset.prod_eq_mul_prod_diff_singleton_of_mem hvT]
  have hne : A ≠ 0 ∧ X.whittakerLoc v h ≠ 0 ∧ B ≠ 0 := by
    have h1 := hg₀
    rw [hfac0] at h1
    obtain ⟨hA, h2⟩ := mul_ne_zero_iff.mp h1
    exact ⟨hA, mul_ne_zero_iff.mp h2⟩
  obtain ⟨hA, hWh, hB⟩ := hne

  have hkey : ∀ x : (v.adicCompletion ℚ)ˣ,
      X.whittakerLoc v (sc v x * h) = ((localChar X.centralChar v x : ℂˣ) : ℂ) * X.whittakerLoc v h := by
    intro x
    set z := idl v x with hzdef
    have hint' : ∀ w, w ∉ T → componentAt3 (𝓞 ℚ) ℚ w (centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀) ∈
        localMaximalCompact3 (𝓞 ℚ) ℚ w := by
      intro w hw
      have hwv : w ≠ v := fun h => hw (h ▸ hvT)
      rw [map_mul, componentAt3_centralScalarGL_idl_of_ne v x hwv, one_mul]
      exact hint w hw
    have hfac1 : X.whittaker (centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀) = A * (X.whittakerLoc v (sc v x * h) * B) := by
      rw [hX.factorizable _ T hT₀T hint', Finset.prod_eq_mul_prod_diff_singleton_of_mem hvT, map_mul,
        archComponent3_centralScalarGL_idl, one_mul, map_mul, componentAt3_centralScalarGL_idl_self]
      congr 2
      refine Finset.prod_congr rfl fun w hw => ?_
      have hwv : w ≠ v := by
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
        exact hw.2
      rw [map_mul, componentAt3_centralScalarGL_idl_of_ne v x hwv, one_mul]
    have hcen := whittaker_centralScalarGL_mul X hX z g₀
    rw [hfac1, hfac0, ← localChar_eq_apply_idl] at hcen
    apply mul_right_cancel₀ hB
    apply mul_left_cancel₀ hA
    rw [hcen]
    ring

  obtain ⟨hRinv, -, -, hcent⟩ := hX.spherical v hv
  refine ⟨?_, ?_⟩
  · intro u hu
    have h1 : X.whittakerLoc v (sc v u * h) = X.whittakerLoc v h := by
      rw [sc_mul_comm]
      exact hRinv h (sc v u) (sc_mem_localMaximalCompact3 v u hu)
    rw [hkey u] at h1
    have h2 : ((localChar X.centralChar v u : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hWh (h1.trans (one_mul _).symm)
      exact this
    exact Units.val_eq_one.mp h2
  · have h1 := hcent h
    rw [← sc_uniformizerUnit_eq_centralGen, hkey] at h1
    exact mul_right_cancel₀ hWh h1

end S_LanglandsTunnell_CubicInduction_localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn (solution)
