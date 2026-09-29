-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_eq_smul_of_isWhittakerFunctional3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/98b68e72-9321-5035-b19e-4d984aed8c8e

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.IntervalCases
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3

set_option autoImplicit false

open IsDedekindDomain NumberField

section

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction"

private def cornerChain (v : HeightOneSpectrum (𝓞 ℚ)) : Fin 7 → Set (LocalGL3 v) :=
  ![∅,
    {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 = 0 ∧ gl3Entry v g 2 1 = 0},
    {g | cornerEntry v g = 0 ∧ gl3Entry v g 2 1 = 0},
    {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0},
    {g | cornerEntry v g = 0},
    {g | cornerEntry v g * lowerMinor v g = 0},
    Set.univ]

private theorem mem_cornerChain_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    g ∈ cornerChain v 0 ↔ False :=
  Iff.rfl

private theorem mem_cornerChain_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    g ∈ cornerChain v 1 ↔ cornerEntry v g = 0 ∧ gl3Entry v g 1 0 = 0 ∧ gl3Entry v g 2 1 = 0 :=
  Iff.rfl

private theorem mem_cornerChain_two (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    g ∈ cornerChain v 2 ↔ cornerEntry v g = 0 ∧ gl3Entry v g 2 1 = 0 :=
  Iff.rfl

private theorem mem_cornerChain_three (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    g ∈ cornerChain v 3 ↔ cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 :=
  Iff.rfl

private theorem mem_cornerChain_four (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    g ∈ cornerChain v 4 ↔ cornerEntry v g = 0 :=
  Iff.rfl

private theorem mem_cornerChain_five (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    g ∈ cornerChain v 5 ↔ cornerEntry v g * lowerMinor v g = 0 :=
  Iff.rfl

private theorem mem_cornerChain_six (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    g ∈ cornerChain v 6 ↔ True :=
  Iff.rfl

private theorem mem_comap_iInf_ker_proj_iff (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (S : Set (LocalGL3 v)) (f : ↥(principalSeries3 v χ)) :
    f ∈ Submodule.comap (principalSeries3 v χ).subtype
        (⨅ g ∈ S, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)) ↔
      ∀ g ∈ S, (f : LocalGL3 v → ℂ) g = 0 := by
  simp [Submodule.mem_comap, Submodule.mem_iInf]

private theorem gl3Entry_mul_upperUnipotent3_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 0 = gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 1 = gl3Entry v g i 0 * x + gl3Entry v g i 1 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_two (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 2 =
      gl3Entry v g i 0 * z + gl3Entry v g i 1 * y + gl3Entry v g i 2 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_diagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (i j : Fin 3) :
    gl3Entry v (g * diagonal3 v a) i j = gl3Entry v g i j * (a j : v.adicCompletion ℚ) := by
  simp [gl3Entry, diagonal3_coe, Matrix.mul_diagonal]

private theorem cornerEntry_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (x y z : v.adicCompletion ℚ) : cornerEntry v (g * upperUnipotent3 x y z) = cornerEntry v g :=
  gl3Entry_mul_upperUnipotent3_zero v g x y z 2

private theorem gl3Entry_two_one_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (x y z : v.adicCompletion ℚ) :
    gl3Entry v (g * upperUnipotent3 x y z) 2 1 = cornerEntry v g * x + gl3Entry v g 2 1 :=
  gl3Entry_mul_upperUnipotent3_one v g x y z 2

private theorem lowerMinor_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (x y z : v.adicCompletion ℚ) : lowerMinor v (g * upperUnipotent3 x y z) = lowerMinor v g := by
  simp only [lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_one]
  ring

private theorem cornerEntry_mul_diagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (g * diagonal3 v a) = cornerEntry v g * (a 0 : v.adicCompletion ℚ) :=
  gl3Entry_mul_diagonal3 v g a 2 0

private theorem lowerMinor_mul_diagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (g * diagonal3 v a) = ((a 0 : v.adicCompletion ℚ) * a 1) * lowerMinor v g := by
  simp only [lowerMinor, gl3Entry_mul_diagonal3]
  ring

private theorem mul_upperUnipotent3_mem_cornerChain (v : HeightOneSpectrum (𝓞 ℚ)) (k : Fin 7)
    {g : LocalGL3 v} (hg : g ∈ cornerChain v k) (x y z : v.adicCompletion ℚ) :
    g * upperUnipotent3 x y z ∈ cornerChain v k := by
  fin_cases k
  · exact (hg : False).elim
  · obtain ⟨h₁, h₂, h₃⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · rwa [cornerEntry_mul_upperUnipotent3]
    · rwa [gl3Entry_mul_upperUnipotent3_zero]
    · rw [gl3Entry_two_one_mul_upperUnipotent3, h₁, zero_mul, zero_add]
      exact h₃
  · obtain ⟨h₁, h₂⟩ := hg
    refine ⟨?_, ?_⟩
    · rwa [cornerEntry_mul_upperUnipotent3]
    · rw [gl3Entry_two_one_mul_upperUnipotent3, h₁, zero_mul, zero_add]
      exact h₂
  · obtain ⟨h₁, h₂⟩ := hg
    refine ⟨?_, ?_⟩
    · rwa [cornerEntry_mul_upperUnipotent3]
    · rw [gl3Entry_mul_upperUnipotent3_zero, gl3Entry_two_one_mul_upperUnipotent3, h₁, zero_mul, zero_add]
      exact h₂
  · show cornerEntry v (g * upperUnipotent3 x y z) = 0
    rwa [cornerEntry_mul_upperUnipotent3]
  · show cornerEntry v (g * upperUnipotent3 x y z) * lowerMinor v (g * upperUnipotent3 x y z) = 0
    rwa [cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3]
  · exact Set.mem_univ _

private theorem mul_diagonal3_mem_cornerChain (v : HeightOneSpectrum (𝓞 ℚ)) (k : Fin 7) {g : LocalGL3 v}
    (hg : g ∈ cornerChain v k) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : g * diagonal3 v a ∈ cornerChain v k := by
  fin_cases k
  · exact (hg : False).elim
  · obtain ⟨h₁, h₂, h₃⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · rw [cornerEntry_mul_diagonal3, h₁, zero_mul]
    · rw [gl3Entry_mul_diagonal3, h₂, zero_mul]
    · rw [gl3Entry_mul_diagonal3, h₃, zero_mul]
  · obtain ⟨h₁, h₂⟩ := hg
    refine ⟨?_, ?_⟩
    · rw [cornerEntry_mul_diagonal3, h₁, zero_mul]
    · rw [gl3Entry_mul_diagonal3, h₂, zero_mul]
  · obtain ⟨h₁, h₂⟩ := hg
    refine ⟨?_, ?_⟩
    · rw [cornerEntry_mul_diagonal3, h₁, zero_mul]
    · rw [gl3Entry_mul_diagonal3, gl3Entry_mul_diagonal3, mul_mul_mul_comm, h₂, zero_mul]
  · show cornerEntry v (g * diagonal3 v a) = 0
    rw [cornerEntry_mul_diagonal3, (mem_cornerChain_four v g).1 hg, zero_mul]
  · show cornerEntry v (g * diagonal3 v a) * lowerMinor v (g * diagonal3 v a) = 0
    rw [cornerEntry_mul_diagonal3, lowerMinor_mul_diagonal3]
    rcases mul_eq_zero.1 ((mem_cornerChain_five v g).1 hg) with h | h
    · rw [h, zero_mul, zero_mul]
    · rw [h, mul_zero, mul_zero]
  · exact Set.mem_univ _

private theorem upperUnipotent3_mul_mem_cornerChain (v : HeightOneSpectrum (𝓞 ℚ)) (k : Fin 7)
    {g : LocalGL3 v} (hg : g ∈ cornerChain v k) (x y z : v.adicCompletion ℚ) :
    upperUnipotent3 x y z * g ∈ cornerChain v k := by
  fin_cases k
  · exact (hg : False).elim
  · obtain ⟨h₁, h₂, h₃⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · rwa [cornerEntry_upperUnipotent3_mul]
    · rw [gl3Entry_upperUnipotent3_mul_one, h₂, show gl3Entry v g 2 0 = 0 from h₁, mul_zero, add_zero]
    · rwa [gl3Entry_upperUnipotent3_mul_two]
  · obtain ⟨h₁, h₂⟩ := hg
    refine ⟨?_, ?_⟩
    · rwa [cornerEntry_upperUnipotent3_mul]
    · rwa [gl3Entry_upperUnipotent3_mul_two]
  · obtain ⟨h₁, h₂⟩ := hg
    refine ⟨?_, ?_⟩
    · rwa [cornerEntry_upperUnipotent3_mul]
    · rw [gl3Entry_upperUnipotent3_mul_one, gl3Entry_upperUnipotent3_mul_two, show gl3Entry v g 2 0 = 0 from h₁,
        mul_zero, add_zero]
      exact h₂
  · show cornerEntry v (upperUnipotent3 x y z * g) = 0
    rwa [cornerEntry_upperUnipotent3_mul]
  · show cornerEntry v (upperUnipotent3 x y z * g) * lowerMinor v (upperUnipotent3 x y z * g) = 0
    rwa [cornerEntry_upperUnipotent3_mul, lowerMinor_upperUnipotent3_mul]
  · exact Set.mem_univ _

private theorem diagonal3_mul_mem_cornerChain (v : HeightOneSpectrum (𝓞 ℚ)) (k : Fin 7) {g : LocalGL3 v}
    (hg : g ∈ cornerChain v k) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : diagonal3 v a * g ∈ cornerChain v k := by
  fin_cases k
  · exact (hg : False).elim
  · obtain ⟨h₁, h₂, h₃⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · rw [cornerEntry_diagonal3_mul, h₁, mul_zero]
    · rw [gl3Entry_diagonal3_mul, h₂, mul_zero]
    · rw [gl3Entry_diagonal3_mul, h₃, mul_zero]
  · obtain ⟨h₁, h₂⟩ := hg
    refine ⟨?_, ?_⟩
    · rw [cornerEntry_diagonal3_mul, h₁, mul_zero]
    · rw [gl3Entry_diagonal3_mul, h₂, mul_zero]
  · obtain ⟨h₁, h₂⟩ := hg
    refine ⟨?_, ?_⟩
    · rw [cornerEntry_diagonal3_mul, h₁, mul_zero]
    · rw [gl3Entry_diagonal3_mul, gl3Entry_diagonal3_mul, mul_mul_mul_comm, h₂, mul_zero]
  · show cornerEntry v (diagonal3 v a * g) = 0
    rw [cornerEntry_diagonal3_mul, (mem_cornerChain_four v g).1 hg, mul_zero]
  · show cornerEntry v (diagonal3 v a * g) * lowerMinor v (diagonal3 v a * g) = 0
    rw [cornerEntry_diagonal3_mul, lowerMinor_diagonal3_mul]
    rcases mul_eq_zero.1 ((mem_cornerChain_five v g).1 hg) with h | h
    · rw [h, mul_zero, zero_mul]
    · rw [h, mul_zero, mul_zero]
  · exact Set.mem_univ _

private theorem exists_eq_upperUnipotent3_mul_diagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (h₁₀ : gl3Entry v g 1 0 = 0) (h₂₀ : gl3Entry v g 2 0 = 0) (h₂₁ : gl3Entry v g 2 1 = 0) :
    ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 x y z * diagonal3 v a := by
  have hdet : gl3Det v g = gl3Entry v g 0 0 * gl3Entry v g 1 1 * gl3Entry v g 2 2 := by
    rw [gl3Det_eq_bottom_expansion, h₁₀, h₂₀, h₂₁]
    ring
  have h₀ : gl3Entry v g 0 0 ≠ 0 := fun h => gl3Det_ne_zero v g (by rw [hdet, h, zero_mul, zero_mul])
  have h₁ : gl3Entry v g 1 1 ≠ 0 := fun h => gl3Det_ne_zero v g (by rw [hdet, h, mul_zero, zero_mul])
  have h₂ : gl3Entry v g 2 2 ≠ 0 := fun h => gl3Det_ne_zero v g (by rw [hdet, h, mul_zero])
  have e₁₀ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 := h₁₀
  have e₂₀ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 := h₂₀
  have e₂₁ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 := h₂₁
  have e₁ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 ≠ 0 := h₁
  have e₂ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 ≠ 0 := h₂
  refine ⟨gl3Entry v g 0 1 / gl3Entry v g 1 1, gl3Entry v g 1 2 / gl3Entry v g 2 2,
    gl3Entry v g 0 2 / gl3Entry v g 2 2, ![Units.mk0 _ h₀, Units.mk0 _ h₁, Units.mk0 _ h₂], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl3Entry, Matrix.mul_diagonal, e₁₀, e₂₀, e₂₁, e₁, e₂]

private theorem exists_eq_upperUnipotent3_mul_diagonal3_of_mem_cornerChain_one (v : HeightOneSpectrum (𝓞 ℚ))
    {g : LocalGL3 v} (hg : g ∈ cornerChain v 1) :
    ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 x y z * diagonal3 v a :=
  exists_eq_upperUnipotent3_mul_diagonal3 v g hg.2.1 hg.1 hg.2.2

private noncomputable def permPoint102 (v : HeightOneSpectrum (𝓞 ℚ)) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion ℚ), 1, 0; 1, 0, 0; 0, 0, 1] (by
    simp [Matrix.det_fin_three])

private noncomputable def permPoint021 (v : HeightOneSpectrum (𝓞 ℚ)) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0, 0; 0, 0, 1; 0, 1, 0] (by
    simp [Matrix.det_fin_three])

private noncomputable def permPoint201 (v : HeightOneSpectrum (𝓞 ℚ)) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion ℚ), 0, 1; 1, 0, 0; 0, 1, 0] (by
    simp [Matrix.det_fin_three])

private noncomputable def permPoint120 (v : HeightOneSpectrum (𝓞 ℚ)) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion ℚ), 1, 0; 0, 0, 1; 1, 0, 0] (by
    simp [Matrix.det_fin_three])

private theorem permPoint102_coe (v : HeightOneSpectrum (𝓞 ℚ)) :
    (permPoint102 v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(0 : v.adicCompletion ℚ), 1, 0; 1, 0, 0; 0, 0, 1] :=
  rfl

private theorem permPoint021_coe (v : HeightOneSpectrum (𝓞 ℚ)) :
    (permPoint021 v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(1 : v.adicCompletion ℚ), 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

private theorem permPoint201_coe (v : HeightOneSpectrum (𝓞 ℚ)) :
    (permPoint201 v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(0 : v.adicCompletion ℚ), 0, 1; 1, 0, 0; 0, 1, 0] :=
  rfl

private theorem permPoint120_coe (v : HeightOneSpectrum (𝓞 ℚ)) :
    (permPoint120 v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(0 : v.adicCompletion ℚ), 1, 0; 0, 0, 1; 1, 0, 0] :=
  rfl

private noncomputable def cellPoint (v : HeightOneSpectrum (𝓞 ℚ)) : Fin 6 → LocalGL3 v :=
  ![1, permPoint102 v, permPoint021 v, permPoint201 v, permPoint120 v, antidiagonal3 v]

private theorem one_mem_cornerChain_one (v : HeightOneSpectrum (𝓞 ℚ)) : (1 : LocalGL3 v) ∈ cornerChain v 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cornerEntry, gl3Entry]

private theorem permPoint102_mem_cornerChain_two (v : HeightOneSpectrum (𝓞 ℚ)) : permPoint102 v ∈ cornerChain v 2 := by
  refine ⟨?_, ?_⟩ <;> simp [cornerEntry, gl3Entry, permPoint102_coe]

private theorem permPoint102_not_mem_cornerChain_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint102 v ∉ cornerChain v 1 :=
  fun h => by simpa [gl3Entry, permPoint102_coe] using h.2.1

private theorem permPoint021_mem_cornerChain_three (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint021 v ∈ cornerChain v 3 := by
  refine ⟨?_, ?_⟩ <;> simp [cornerEntry, gl3Entry, permPoint021_coe]

private theorem permPoint021_not_mem_cornerChain_two (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint021 v ∉ cornerChain v 2 :=
  fun h => by simpa [gl3Entry, permPoint021_coe] using h.2

private theorem permPoint201_mem_cornerChain_four (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint201 v ∈ cornerChain v 4 := by
  show cornerEntry v (permPoint201 v) = 0
  simp [cornerEntry, gl3Entry, permPoint201_coe]

private theorem permPoint201_not_mem_cornerChain_three (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint201 v ∉ cornerChain v 3 :=
  fun h => by simpa [gl3Entry, permPoint201_coe] using h.2

private theorem cornerEntry_permPoint120 (v : HeightOneSpectrum (𝓞 ℚ)) : cornerEntry v (permPoint120 v) = 1 := by
  simp [cornerEntry, gl3Entry, permPoint120_coe]

private theorem lowerMinor_permPoint120 (v : HeightOneSpectrum (𝓞 ℚ)) : lowerMinor v (permPoint120 v) = 0 := by
  simp [lowerMinor, gl3Entry, permPoint120_coe]

private theorem permPoint120_mem_cornerChain_five (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint120 v ∈ cornerChain v 5 := by
  show cornerEntry v (permPoint120 v) * lowerMinor v (permPoint120 v) = 0
  rw [lowerMinor_permPoint120, mul_zero]

private theorem permPoint120_not_mem_cornerChain_four (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint120 v ∉ cornerChain v 4 :=
  fun h => one_ne_zero ((cornerEntry_permPoint120 v).symm.trans ((mem_cornerChain_four v _).1 h))

private theorem antidiagonal3_not_mem_cornerChain_five (v : HeightOneSpectrum (𝓞 ℚ)) :
    antidiagonal3 v ∉ cornerChain v 5 := fun h => by
  have h' := (mem_cornerChain_five v _).1 h
  rw [cornerEntry_antidiagonal3, lowerMinor_antidiagonal3, one_mul, neg_eq_zero] at h'
  exact one_ne_zero h'

private theorem cellPoint_mem_cornerChain_succ (v : HeightOneSpectrum (𝓞 ℚ)) (i : Fin 6) :
    cellPoint v i ∈ cornerChain v i.succ := by
  fin_cases i
  · exact one_mem_cornerChain_one v
  · exact permPoint102_mem_cornerChain_two v
  · exact permPoint021_mem_cornerChain_three v
  · exact permPoint201_mem_cornerChain_four v
  · exact permPoint120_mem_cornerChain_five v
  · exact Set.mem_univ _

private theorem cellPoint_not_mem_cornerChain_castSucc (v : HeightOneSpectrum (𝓞 ℚ)) (i : Fin 6) :
    cellPoint v i ∉ cornerChain v i.castSucc := by
  fin_cases i
  · exact fun h => (h : False).elim
  · exact permPoint102_not_mem_cornerChain_one v
  · exact permPoint021_not_mem_cornerChain_two v
  · exact permPoint201_not_mem_cornerChain_three v
  · exact permPoint120_not_mem_cornerChain_four v
  · exact antidiagonal3_not_mem_cornerChain_five v
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction"

namespace UnipotentBox

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def IsPrincipalCongruence (t : ℕ) (k : LocalGL3 v) : Prop :=
  ∀ i j : Fin 3,
    Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(t : ℤ))

private def unipotentSet : Set (LocalGL3 v) := {g | ∃ x y z : v.adicCompletion ℚ, g = upperUnipotent3 x y z}

private def absorbedBy (p : LocalGL3 v) : Set (LocalGL3 v) :=
  {m | m ∈ unipotentSet v ∧ ∃ x y z : v.adicCompletion ℚ, p * m = upperUnipotent3 x y z * p}

private def boxSet (ρ₁ ρ₂ ρ₃ : WithZero (Multiplicative ℤ)) : Set (LocalGL3 v) :=
  {g | ∃ x y z : v.adicCompletion ℚ,
    Valued.v x ≤ ρ₁ ∧ Valued.v y ≤ ρ₂ ∧ Valued.v z ≤ ρ₃ ∧ g = upperUnipotent3 x y z}

private theorem unipotent_mul (x y z x' y' z' : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) * upperUnipotent3 x' y' z'
      = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem unipotent_inv (x y z : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  rw [inv_eq_iff_mul_eq_one, unipotent_mul v, show x + -x = 0 by ring, show y + -y = 0 by ring,
    show z + (x * y - z) + x * -y = 0 by ring, upperUnipotent3_zero]

private theorem gl3Entry_upperUnipotent3 (x y z : v.adicCompletion ℚ) (i j : Fin 3) :
    gl3Entry v (upperUnipotent3 x y z) i j = !![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] i j :=
  rfl

private def box (ρ₁ ρ₂ ρ₃ : WithZero (Multiplicative ℤ)) (hρ : ρ₁ * ρ₂ ≤ ρ₃) : Subgroup (LocalGL3 v) where
  carrier := boxSet v ρ₁ ρ₂ ρ₃
  one_mem' := ⟨0, 0, 0, by simp, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x, y, z, hx, hy, hz, rfl⟩ ⟨x', y', z', hx', hy', hz', rfl⟩
    refine ⟨x + x', y + y', z + z' + x * y', ?_, ?_, ?_, unipotent_mul v x y z x' y' z'⟩
    · exact (Valued.v.map_add x x').trans (max_le hx hx')
    · exact (Valued.v.map_add y y').trans (max_le hy hy')
    · refine (Valued.v.map_add _ _).trans (max_le ((Valued.v.map_add z z').trans (max_le hz hz')) ?_)
      rw [map_mul]
      exact (mul_le_mul' hx hy').trans hρ
  inv_mem' := by
    rintro _ ⟨x, y, z, hx, hy, hz, rfl⟩
    refine ⟨-x, -y, x * y - z, by simpa using hx, by simpa using hy, ?_, unipotent_inv v x y z⟩
    refine (Valued.v.map_sub _ _).trans (max_le ?_ hz)
    rw [map_mul]
    exact (mul_le_mul' hx hy).trans hρ

private theorem mem_box_iff {ρ₁ ρ₂ ρ₃ : WithZero (Multiplicative ℤ)} {hρ : ρ₁ * ρ₂ ≤ ρ₃} {g : LocalGL3 v} :
    g ∈ box v ρ₁ ρ₂ ρ₃ hρ ↔ ∃ x y z : v.adicCompletion ℚ,
      Valued.v x ≤ ρ₁ ∧ Valued.v y ≤ ρ₂ ∧ Valued.v z ≤ ρ₃ ∧ g = upperUnipotent3 x y z :=
  Iff.rfl

private theorem upperUnipotent3_mem_box {ρ₁ ρ₂ ρ₃ : WithZero (Multiplicative ℤ)} {hρ : ρ₁ * ρ₂ ≤ ρ₃}
    {x y z : v.adicCompletion ℚ} (hx : Valued.v x ≤ ρ₁) (hy : Valued.v y ≤ ρ₂) (hz : Valued.v z ≤ ρ₃) :
    (upperUnipotent3 x y z : LocalGL3 v) ∈ box v ρ₁ ρ₂ ρ₃ hρ :=
  ⟨x, y, z, hx, hy, hz, rfl⟩

private theorem mem_unipotentSet_of_mem_box {ρ₁ ρ₂ ρ₃ : WithZero (Multiplicative ℤ)} {hρ : ρ₁ * ρ₂ ≤ ρ₃}
    {g : LocalGL3 v} (hg : g ∈ box v ρ₁ ρ₂ ρ₃ hρ) : g ∈ unipotentSet v := by
  obtain ⟨x, y, z, -, -, -, rfl⟩ := hg
  exact ⟨x, y, z, rfl⟩

private theorem isCompact_setOf_valued_le (ρ : WithZero (Multiplicative ℤ)) :
    IsCompact {x : v.adicCompletion ℚ | Valued.v x ≤ ρ} := by
  by_cases hρ : ρ = 0
  · have h : {x : v.adicCompletion ℚ | Valued.v x ≤ ρ} = {0} := by
      subst hρ
      ext x
      constructor
      · intro hx
        have h0 : Valued.v x = 0 := le_antisymm hx zero_le'
        simpa using h0
      · rintro rfl
        simp
    rw [h]
    exact isCompact_singleton
  · have h : {x : v.adicCompletion ℚ | Valued.v x ≤ ρ}
        = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-WithZero.log ρ))} := by
      ext x
      simp [WithZero.exp_log hρ]
    rw [h]
    exact isCompact_setOf_valued_sub_le v 0 (-WithZero.log ρ)

private theorem continuous_upperUnipotent3 :
    Continuous (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (upperUnipotent3 q.1 q.2.1 q.2.2 : LocalGL3 v)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem boxSet_eq_image (ρ₁ ρ₂ ρ₃ : WithZero (Multiplicative ℤ)) :
    boxSet v ρ₁ ρ₂ ρ₃ = (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (upperUnipotent3 q.1 q.2.1 q.2.2 : LocalGL3 v)) ''
        ({x | Valued.v x ≤ ρ₁} ×ˢ ({y | Valued.v y ≤ ρ₂} ×ˢ {z | Valued.v z ≤ ρ₃})) := by
  ext g
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, rfl⟩
    exact ⟨(x, y, z), ⟨hx, hy, hz⟩, rfl⟩
  · rintro ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩
    exact ⟨x, y, z, hx, hy, hz, rfl⟩

private theorem isCompact_box (ρ₁ ρ₂ ρ₃ : WithZero (Multiplicative ℤ)) (hρ : ρ₁ * ρ₂ ≤ ρ₃) :
    IsCompact ((box v ρ₁ ρ₂ ρ₃ hρ : Set (LocalGL3 v))) := by
  show IsCompact (boxSet v ρ₁ ρ₂ ρ₃)
  rw [boxSet_eq_image]
  exact (((isCompact_setOf_valued_le v ρ₁).prod
    ((isCompact_setOf_valued_le v ρ₂).prod (isCompact_setOf_valued_le v ρ₃)))).image
      (continuous_upperUnipotent3 v)

private theorem exp_neg_mul_exp_neg_le (t : ℕ) :
    (WithZero.exp (-(t : ℤ)) : WithZero (Multiplicative ℤ)) * WithZero.exp (-(t : ℤ)) ≤ WithZero.exp (-(t : ℤ)) := by
  rw [← WithZero.exp_add, WithZero.exp_le_exp]
  omega

private def smallBox (t : ℕ) : Subgroup (LocalGL3 v) :=
  box v (WithZero.exp (-(t : ℤ))) (WithZero.exp (-(t : ℤ))) (WithZero.exp (-(t : ℤ))) (exp_neg_mul_exp_neg_le t)

private theorem isPrincipalCongruence_of_mem_smallBox {t : ℕ} {h : LocalGL3 v} (hh : h ∈ smallBox v t) :
    IsPrincipalCongruence v t h := by
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := hh
  intro i j
  rw [gl3Entry_upperUnipotent3]
  fin_cases i <;> fin_cases j <;> simp <;>
    first | simpa using hx | simpa using hy | simpa using hz

private theorem mem_smallBox_of_isPrincipalCongruence {t : ℕ} {x y z : v.adicCompletion ℚ}
    (hk : IsPrincipalCongruence v t (upperUnipotent3 x y z)) :
    (upperUnipotent3 x y z : LocalGL3 v) ∈ smallBox v t := by
  refine upperUnipotent3_mem_box v ?_ ?_ ?_
  · simpa [gl3Entry_upperUnipotent3, Matrix.one_apply] using hk 0 1
  · simpa [gl3Entry_upperUnipotent3, Matrix.one_apply] using hk 1 2
  · simpa [gl3Entry_upperUnipotent3, Matrix.one_apply] using hk 0 2

private theorem isOpen_setOf_isPrincipalCongruence (t : ℕ) :
    IsOpen {k : LocalGL3 v | IsPrincipalCongruence v t k} := by
  have h : {k : LocalGL3 v | IsPrincipalCongruence v t k} = ⋂ i : Fin 3, ⋂ j : Fin 3,
      (fun k : LocalGL3 v => gl3Entry v k i j) ⁻¹'
        {a : v.adicCompletion ℚ | Valued.v (a - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-((t : ℕ) : ℤ))} := by
    ext k
    simp [IsPrincipalCongruence]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isClopen_setOf_valued_sub_le v _ t).isOpen.preimage (continuous_gl3Entry v i j)

private theorem one_isPrincipalCongruence (t : ℕ) : IsPrincipalCongruence v t (1 : LocalGL3 v) := by
  intro i j
  simp [gl3Entry]

end UnipotentBox
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction"

namespace UnipotentBox

section CompactAveraging

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_finset_sum_mul_mul_eq_sum_mul (M H : Subgroup G) (hM : IsCompact (M : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (hUH : ∀ u ∈ U, u ∈ M → u ∈ H) :
    ∃ s : Finset G, s.Nonempty ∧ (∀ r ∈ s, r ∈ M) ∧
      ∀ φ : G → ℂ, (∀ h ∈ H, ∀ g : G, φ (g * h) = φ g) →
        ∀ g : G, ∀ m ∈ M, ∑ r ∈ s, φ (g * m * r) = ∑ r ∈ s, φ (g * r) := by
  classical
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hM
  let H' : Subgroup M := H.subgroupOf M
  have hopen : IsOpen (H' : Set M) := by
    refine Subgroup.isOpen_of_mem_nhds H' (g := (1 : M)) ?_
    have hUo : IsOpen ((fun m : M => (m : G)) ⁻¹' U) := hU.preimage continuous_subtype_val
    refine Filter.mem_of_superset (hUo.mem_nhds ?_) ?_
    · show ((1 : M) : G) ∈ U
      simpa using h1
    · intro m hm
      exact Subgroup.mem_subgroupOf.mpr (hUH (m : G) hm m.2)
  haveI : Finite (M ⧸ H') := H'.quotient_finite_of_isOpen hopen
  letI : Fintype (M ⧸ H') := Fintype.ofFinite _
  have hinj : Function.Injective (fun q : M ⧸ H' => ((Quotient.out q : M) : G)) :=
    Subtype.val_injective.comp Quotient.out_injective
  refine ⟨Finset.univ.image (fun q : M ⧸ H' => ((Quotient.out q : M) : G)), ?_, ?_, ?_⟩
  · exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (((1 : M) : M ⧸ H')))⟩
  · intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact (Quotient.out q).2
  · intro φ hφ g m hm
    rw [Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.sum_image (fun a _ b _ hab => hinj hab)]
    let m' : M := ⟨m, hm⟩
    have hshift : ∀ q : M ⧸ H',
        φ (g * m * ((Quotient.out q : M) : G)) = φ (g * ((Quotient.out (m' • q) : M) : G)) := by
      intro q
      have hq : ((m' * Quotient.out q : M) : M ⧸ H') = m' • q := MulAction.Quotient.mk_smul_out H' m' q
      have hmem : (m' * Quotient.out q)⁻¹ * Quotient.out (m' • q) ∈ H' :=
        QuotientGroup.eq.mp (hq.trans (QuotientGroup.out_eq' (m' • q)).symm)
      have hout : Quotient.out (m' • q) = m' * Quotient.out q * ((m' * Quotient.out q)⁻¹ * Quotient.out (m' • q)) := by
        rw [mul_inv_cancel_left]
      rw [hout, Subgroup.coe_mul, Subgroup.coe_mul, ← mul_assoc, hφ _ (Subgroup.mem_subgroupOf.mp hmem), mul_assoc]
    simp_rw [hshift]
    exact Fintype.sum_equiv (MulAction.toPerm m') _ _ (fun q => rfl)

end CompactAveraging

section PairRelation

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

private theorem le_one_of_forall_mem_exists_mul_eq_mul (W : Submodule ℂ E) (n : ℕ) (Λ : Fin n → (E →ₗ[ℂ] ℂ))
    (hpair : ∀ f ∈ W, ∀ f' ∈ W, ∃ c c' : ℂ, (∀ j, c' * Λ j f = c * Λ j f') ∧ (c = 0 → ∀ j, Λ j f = 0))
    (hli : LinearIndependent ℂ fun j => (Λ j).domRestrict W) : n ≤ 1 := by
  by_contra hn
  have h2 : 2 ≤ n := by omega
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  by_cases hzero : ∀ f ∈ W, Λ i₁ f = 0
  · apply hli.ne_zero i₁
    ext ⟨f, hf⟩
    simp [hzero f hf]
  · push Not at hzero
    obtain ⟨f₀, hf₀, hne₀⟩ := hzero
    have hrel : ∀ f ∈ W, Λ i₀ f = Λ i₀ f₀ / Λ i₁ f₀ * Λ i₁ f := by
      intro f hf
      obtain ⟨c, c', hcc, hc⟩ := hpair f₀ hf₀ f hf
      have hc0 : c ≠ 0 := fun h0 => hne₀ (hc h0 i₁)
      have e0 := hcc i₀
      have e1 := hcc i₁
      rw [div_mul_eq_mul_div, eq_div_iff hne₀]
      apply mul_left_cancel₀ hc0
      linear_combination (-(Λ i₁ f₀)) * e0 + (Λ i₀ f₀) * e1
    have hinj : Function.Injective (![i₀, i₁] : Fin 2 → Fin n) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hne.symm]
    have hdep := Fintype.linearIndependent_iff.mp (hli.comp ![i₀, i₁] hinj) ![1, -(Λ i₀ f₀ / Λ i₁ f₀)] ?_ 0
    · simp at hdep
    · ext ⟨f, hf⟩
      simp [Fin.sum_univ_two, hrel f hf]

end PairRelation

variable (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem isPrincipalCongruence_of_le {s t : ℕ} (hst : s ≤ t) {k : LocalGL3 v}
    (hk : IsPrincipalCongruence v t k) : IsPrincipalCongruence v s k := by
  intro i j
  refine (hk i j).trans ?_
  rw [WithZero.exp_le_exp]
  omega

private theorem mul_mem_unipotentSet {m r : LocalGL3 v} (hm : m ∈ unipotentSet v) (hr : r ∈ unipotentSet v) :
    m * r ∈ unipotentSet v := by
  obtain ⟨x, y, z, rfl⟩ := hm
  obtain ⟨x', y', z', rfl⟩ := hr
  exact ⟨_, _, _, unipotent_mul v x y z x' y' z'⟩

private def UniformlySmooth : Prop :=
  ∀ f : LocalGL3 v → ℂ, f ∈ principalSeries3 v χ → ∃ t : ℕ, ∀ k : LocalGL3 v,
    IsPrincipalCongruence v t k → gl3AmbientRightTranslate (R := ℂ) k f = f

private noncomputable def translateSection (g : LocalGL3 v) (F : ↥(principalSeries3 v χ)) : ↥(principalSeries3 v χ) :=
  ⟨gl3AmbientRightTranslate (R := ℂ) g F, rightTranslate_mem_principalSeries3 F.2 g⟩

private noncomputable def sumTranslate (s : Finset (LocalGL3 v)) (F : ↥(principalSeries3 v χ)) :
    ↥(principalSeries3 v χ) :=
  ∑ r ∈ s, translateSection v χ r F

private theorem sumTranslate_apply (s : Finset (LocalGL3 v)) (F : ↥(principalSeries3 v χ)) (h : LocalGL3 v) :
    (sumTranslate v χ s F : LocalGL3 v → ℂ) h = ∑ r ∈ s, (F : LocalGL3 v → ℂ) (h * r) := by
  simp [sumTranslate, translateSection]

private theorem sumTranslate_apply_eq_zero (s : Finset (LocalGL3 v)) {Zi : Set (LocalGL3 v)}
    (hN : ∀ g ∈ Zi, ∀ x y z : v.adicCompletion ℚ, g * upperUnipotent3 x y z ∈ Zi)
    (hs : ∀ r ∈ s, r ∈ unipotentSet v) {F : ↥(principalSeries3 v χ)}
    (hF : ∀ g ∈ Zi, (F : LocalGL3 v → ℂ) g = 0) {g : LocalGL3 v} (hg : g ∈ Zi) :
    (sumTranslate v χ s F : LocalGL3 v → ℂ) g = 0 := by
  rw [sumTranslate_apply]
  refine Finset.sum_eq_zero fun r hr => ?_
  obtain ⟨x, y, z, rfl⟩ := hs r hr
  exact hF _ (hN g hg x y z)

private theorem apply_eq_zero_of_forall_mul_eq_zero {Zi Zi1 : Set (LocalGL3 v)} {p : LocalGL3 v}
    (hcover : ∀ g ∈ Zi1, g ∉ Zi → ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
      (m : LocalGL3 v), m ∈ unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (p * m))
    {F : ↥(principalSeries3 v χ)} (hFZ : ∀ g ∈ Zi, (F : LocalGL3 v → ℂ) g = 0)
    (hFp : ∀ m ∈ unipotentSet v, (F : LocalGL3 v → ℂ) (p * m) = 0) {g : LocalGL3 v} (hg : g ∈ Zi1) :
    (F : LocalGL3 v → ℂ) g = 0 := by
  by_cases hgZ : g ∈ Zi
  · exact hFZ g hgZ
  obtain ⟨x, y, z, a, m, hm, rfl⟩ := hcover g hg hgZ
  rw [mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 F.2,
    apply_diagonal3_mul_of_mem_principalSeries3 F.2, hFp m hm, mul_zero]

private theorem apply_mul_eq_of_level {F : ↥(principalSeries3 v χ)} {t₀ t : ℕ}
    (hF : ∀ k : LocalGL3 v, IsPrincipalCongruence v t₀ k → gl3AmbientRightTranslate (R := ℂ) k F = F) (ht : t₀ ≤ t)
    {k : LocalGL3 v} (hk : IsPrincipalCongruence v t k) (g : LocalGL3 v) :
    (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g := by
  have h := congrFun (hF k (isPrincipalCongruence_of_le v ht hk)) g
  simpa using h

private theorem apply_mul_eq_zero_of_not_exists {Zi : Set (LocalGL3 v)} {p : LocalGL3 v}
    {M : Subgroup (LocalGL3 v)} {t : ℕ}
    (hM : ∀ m ∈ unipotentSet v, (∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
      ∃ k : LocalGL3 v, IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi)
    {F : ↥(principalSeries3 v χ)}
    (hF : ∀ k : LocalGL3 v, IsPrincipalCongruence v t k → ∀ g, (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g)
    (hFZ : ∀ g ∈ Zi, (F : LocalGL3 v → ℂ) g = 0) {m : LocalGL3 v} (hm : m ∈ unipotentSet v)
    (hout : ¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) : (F : LocalGL3 v → ℂ) (p * m) = 0 := by
  obtain ⟨k, hk, hkZ⟩ := (hM m hm).resolve_left hout
  rw [← hF k hk (p * m)]
  exact hFZ _ hkZ

private noncomputable def psiN (ψ : AddChar (v.adicCompletion ℚ) ℂ) (r : LocalGL3 v) : ℂ :=
  ψ (gl3Entry v r 0 1 + gl3Entry v r 1 2)

private noncomputable def wt (ψ : AddChar (v.adicCompletion ℚ) ℂ) (r : LocalGL3 v) : ℂ :=
  ψ (-(gl3Entry v r 0 1 + gl3Entry v r 1 2))

private theorem psiN_upperUnipotent3 (ψ : AddChar (v.adicCompletion ℚ) ℂ) (x y z : v.adicCompletion ℚ) :
    psiN v ψ (upperUnipotent3 x y z) = ψ (x + y) := by
  simp [psiN, gl3Entry_upperUnipotent3]

private theorem wt_upperUnipotent3 (ψ : AddChar (v.adicCompletion ℚ) ℂ) (x y z : v.adicCompletion ℚ) :
    wt v ψ (upperUnipotent3 x y z) = ψ (-(x + y)) := by
  simp [wt, gl3Entry_upperUnipotent3]

private theorem wt_mul_psiN (ψ : AddChar (v.adicCompletion ℚ) ℂ) {r : LocalGL3 v} (hr : r ∈ unipotentSet v) :
    wt v ψ r * psiN v ψ r = 1 := by
  obtain ⟨x, y, z, rfl⟩ := hr
  rw [wt_upperUnipotent3, psiN_upperUnipotent3, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

private theorem psiN_mul_wt (ψ : AddChar (v.adicCompletion ℚ) ℂ) {r : LocalGL3 v} (hr : r ∈ unipotentSet v) :
    psiN v ψ r * wt v ψ r = 1 := by
  rw [mul_comm]
  exact wt_mul_psiN v ψ hr

private theorem psiN_mul (ψ : AddChar (v.adicCompletion ℚ) ℂ) {a b : LocalGL3 v} (ha : a ∈ unipotentSet v)
    (hb : b ∈ unipotentSet v) : psiN v ψ (a * b) = psiN v ψ a * psiN v ψ b := by
  obtain ⟨x, y, z, rfl⟩ := ha
  obtain ⟨x', y', z', rfl⟩ := hb
  rw [unipotent_mul v, psiN_upperUnipotent3, psiN_upperUnipotent3, psiN_upperUnipotent3, ← AddChar.map_add_eq_mul]
  exact congrArg ψ (by ring)

private theorem wt_mul (ψ : AddChar (v.adicCompletion ℚ) ℂ) {a b : LocalGL3 v} (ha : a ∈ unipotentSet v)
    (hb : b ∈ unipotentSet v) : wt v ψ (a * b) = wt v ψ a * wt v ψ b := by
  obtain ⟨x, y, z, rfl⟩ := ha
  obtain ⟨x', y', z', rfl⟩ := hb
  rw [unipotent_mul v, wt_upperUnipotent3, wt_upperUnipotent3, wt_upperUnipotent3, ← AddChar.map_add_eq_mul]
  exact congrArg ψ (by ring)

private theorem wt_eq_one_of_mem_smallBox (ψ : AddChar (v.adicCompletion ℚ) ℂ) {L : ℕ}
    (hψ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → ψ x = 1) {h : LocalGL3 v}
    (hh : h ∈ smallBox v L) : wt v ψ h = 1 := by
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := hh
  rw [wt_upperUnipotent3]
  refine hψ _ ?_
  rw [Valuation.map_neg]
  exact (Valuation.map_add _ x y).trans (max_le hx hy)

private theorem one_mem_absorbedBy' (p : LocalGL3 v) : (1 : LocalGL3 v) ∈ absorbedBy v p :=
  ⟨⟨0, 0, 0, upperUnipotent3_zero.symm⟩, 0, 0, 0, by simp⟩

private theorem inv_mem_unipotentSet {m : LocalGL3 v} (hm : m ∈ unipotentSet v) : m⁻¹ ∈ unipotentSet v := by
  obtain ⟨x, y, z, rfl⟩ := hm
  exact ⟨_, _, _, unipotent_inv v x y z⟩

private theorem mul_mem_absorbedBy {p a b : LocalGL3 v} (ha : a ∈ absorbedBy v p) (hb : b ∈ absorbedBy v p) :
    a * b ∈ absorbedBy v p := by
  obtain ⟨haN, x, y, z, hpa⟩ := ha
  obtain ⟨hbN, x', y', z', hpb⟩ := hb
  refine ⟨mul_mem_unipotentSet v haN hbN, x + x', y + y', z + z' + x * y', ?_⟩
  rw [← unipotent_mul v, ← mul_assoc, hpa, mul_assoc, hpb, mul_assoc]

private theorem inv_mem_absorbedBy {p a : LocalGL3 v} (ha : a ∈ absorbedBy v p) : a⁻¹ ∈ absorbedBy v p := by
  obtain ⟨haN, x, y, z, hpa⟩ := ha
  refine ⟨inv_mem_unipotentSet v haN, -x, -y, x * y - z, ?_⟩
  rw [← unipotent_inv v]
  calc p * a⁻¹ = (upperUnipotent3 x y z : LocalGL3 v)⁻¹ * (upperUnipotent3 x y z * p) * a⁻¹ := by
        rw [inv_mul_cancel_left]
    _ = (upperUnipotent3 x y z : LocalGL3 v)⁻¹ * (p * a) * a⁻¹ := by rw [hpa]
    _ = (upperUnipotent3 x y z : LocalGL3 v)⁻¹ * p := by rw [mul_assoc, mul_inv_cancel_right]

private theorem apply_mul_absorbed (F : ↥(principalSeries3 v χ)) {p a : LocalGL3 v} (ha : a ∈ absorbedBy v p)
    (x : LocalGL3 v) : (F : LocalGL3 v → ℂ) (p * (a * x)) = (F : LocalGL3 v → ℂ) (p * x) := by
  obtain ⟨-, x', y', z', hpa⟩ := ha
  rw [← mul_assoc, hpa, mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 F.2]

private theorem translateSection_apply (g : LocalGL3 v) (F : ↥(principalSeries3 v χ)) (h : LocalGL3 v) :
    (translateSection v χ g F : LocalGL3 v → ℂ) h = (F : LocalGL3 v → ℂ) (h * g) :=
  rfl

private noncomputable def twSum (ψ : AddChar (v.adicCompletion ℚ) ℂ) (s : Finset (LocalGL3 v))
    (F : ↥(principalSeries3 v χ)) : ↥(principalSeries3 v χ) :=
  ∑ r ∈ s, wt v ψ r • translateSection v χ r F

private theorem twSum_apply (ψ : AddChar (v.adicCompletion ℚ) ℂ) (s : Finset (LocalGL3 v))
    (F : ↥(principalSeries3 v χ)) (h : LocalGL3 v) :
    (twSum v χ ψ s F : LocalGL3 v → ℂ) h = ∑ r ∈ s, wt v ψ r * (F : LocalGL3 v → ℂ) (h * r) := by
  simp [twSum, translateSection]

private theorem twSum_apply_eq_zero (ψ : AddChar (v.adicCompletion ℚ) ℂ) (s : Finset (LocalGL3 v))
    {Zi : Set (LocalGL3 v)} (hN : ∀ g ∈ Zi, ∀ x y z : v.adicCompletion ℚ, g * upperUnipotent3 x y z ∈ Zi)
    (hs : ∀ r ∈ s, r ∈ unipotentSet v) {F : ↥(principalSeries3 v χ)}
    (hF : ∀ g ∈ Zi, (F : LocalGL3 v → ℂ) g = 0) {g : LocalGL3 v} (hg : g ∈ Zi) :
    (twSum v χ ψ s F : LocalGL3 v → ℂ) g = 0 := by
  rw [twSum_apply]
  refine Finset.sum_eq_zero fun r hr => ?_
  obtain ⟨x, y, z, rfl⟩ := hs r hr
  rw [hF _ (hN g hg x y z), mul_zero]

private theorem apply_translateSection_of_isWhittakerFunctional3 (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ) {r : LocalGL3 v}
    (hr : r ∈ unipotentSet v) (F : ↥(principalSeries3 v χ)) :
    Λ (translateSection v χ r F) = psiN v ψ r * Λ F := by
  obtain ⟨x, y, z, rfl⟩ := hr
  rw [psiN_upperUnipotent3]
  exact hΛ x y z F

private theorem apply_twSum (ψ : AddChar (v.adicCompletion ℚ) ℂ) {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ}
    (hΛ : IsWhittakerFunctional3 ψ Λ) (s : Finset (LocalGL3 v)) (hs : ∀ r ∈ s, r ∈ unipotentSet v)
    (F : ↥(principalSeries3 v χ)) : Λ (twSum v χ ψ s F) = (s.card : ℂ) * Λ F := by
  unfold twSum
  rw [map_sum]
  have h : ∀ r ∈ s, Λ (wt v ψ r • translateSection v χ r F) = Λ F := by
    intro r hr
    rw [map_smul, smul_eq_mul, apply_translateSection_of_isWhittakerFunctional3 v χ ψ hΛ (hs r hr), ← mul_assoc,
      wt_mul_psiN v ψ (hs r hr), one_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

private noncomputable def twValue (ψ : AddChar (v.adicCompletion ℚ) ℂ) (s : Finset (LocalGL3 v)) (p : LocalGL3 v)
    (F : ↥(principalSeries3 v χ)) : ℂ :=
  ∑ r ∈ s, wt v ψ r * (F : LocalGL3 v → ℂ) (p * r)

private theorem exists_finset_twisted (ψ : AddChar (v.adicCompletion ℚ) ℂ) (L : ℕ)
    (hψL : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → ψ x = 1)
    (M : Subgroup (LocalGL3 v)) (hMc : IsCompact (M : Set (LocalGL3 v))) (hMN : ∀ m ∈ M, m ∈ unipotentSet v)
    (p : LocalGL3 v) :
    ∃ s : Finset (LocalGL3 v), s.Nonempty ∧ (∀ r ∈ s, r ∈ M) ∧
      ∀ F : ↥(principalSeries3 v χ),
        (∀ k : LocalGL3 v, IsPrincipalCongruence v L k →
          ∀ g, (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g) →
        ∀ m ∈ M, ∑ r ∈ s, wt v ψ r * (F : LocalGL3 v → ℂ) (p * m * r) = psiN v ψ m * twValue v χ ψ s p F := by
  classical
  have hUH : ∀ u ∈ {k : LocalGL3 v | IsPrincipalCongruence v L k}, u ∈ M → u ∈ M ⊓ smallBox v L := by
    intro u hu huM
    obtain ⟨x, y, z, rfl⟩ := hMN u huM
    exact Subgroup.mem_inf.mpr ⟨huM, mem_smallBox_of_isPrincipalCongruence v
      (hu : IsPrincipalCongruence v L (upperUnipotent3 x y z))⟩
  obtain ⟨s, hs0, hsM, hsum⟩ := exists_finset_sum_mul_mul_eq_sum_mul M (M ⊓ smallBox v L) hMc
    (isOpen_setOf_isPrincipalCongruence v L) (one_isPrincipalCongruence v _) hUH
  refine ⟨s, hs0, hsM, ?_⟩
  intro F hF m hm

  let φ : LocalGL3 v → ℂ := fun g =>
    if p⁻¹ * g ∈ unipotentSet v then wt v ψ (p⁻¹ * g) * (F : LocalGL3 v → ℂ) g else 0
  have hφ : ∀ h ∈ M ⊓ smallBox v L, ∀ g : LocalGL3 v, φ (g * h) = φ g := by
    intro h hh g
    obtain ⟨hhM, hhS⟩ := Subgroup.mem_inf.mp hh
    have hhN : h ∈ unipotentSet v := hMN h hhM
    have hFg : (F : LocalGL3 v → ℂ) (g * h) = (F : LocalGL3 v → ℂ) g :=
      hF h (isPrincipalCongruence_of_mem_smallBox v hhS) g
    have hw : wt v ψ h = 1 := wt_eq_one_of_mem_smallBox v ψ hψL hhS
    simp only [φ, ← mul_assoc]
    by_cases hg : p⁻¹ * g ∈ unipotentSet v
    · rw [if_pos (mul_mem_unipotentSet v hg hhN), if_pos hg, wt_mul v ψ hg hhN, hw, mul_one, hFg]
    · have hgh : ¬ p⁻¹ * g * h ∈ unipotentSet v := fun hc => by
        have h' := mul_mem_unipotentSet v hc (inv_mem_unipotentSet v hhN)
        rw [mul_inv_cancel_right] at h'
        exact hg h'
      rw [if_neg hgh, if_neg hg]
  have key := hsum φ hφ p m hm
  have hφ₁ : ∀ r ∈ s, φ (p * m * r) = wt v ψ m * (wt v ψ r * (F : LocalGL3 v → ℂ) (p * m * r)) := by
    intro r hr
    have hmr : m * r ∈ unipotentSet v := mul_mem_unipotentSet v (hMN m hm) (hMN r (hsM r hr))
    have e : p⁻¹ * (p * m * r) = m * r := by group
    simp only [φ]
    rw [e, if_pos hmr, wt_mul v ψ (hMN m hm) (hMN r (hsM r hr)), mul_assoc (wt v ψ m)]
  have hφ₂ : ∀ r ∈ s, φ (p * r) = wt v ψ r * (F : LocalGL3 v → ℂ) (p * r) := by
    intro r hr
    have e : p⁻¹ * (p * r) = r := by group
    simp only [φ, e, if_pos (hMN r (hsM r hr))]
  rw [Finset.sum_congr rfl hφ₁, Finset.sum_congr rfl hφ₂, ← Finset.mul_sum] at key

  have hm1 := psiN_mul_wt v ψ (hMN m hm)
  calc ∑ r ∈ s, wt v ψ r * (F : LocalGL3 v → ℂ) (p * m * r)
      = psiN v ψ m * wt v ψ m * ∑ r ∈ s, wt v ψ r * (F : LocalGL3 v → ℂ) (p * m * r) := by rw [hm1, one_mul]
    _ = psiN v ψ m * twValue v χ ψ s p F := by rw [mul_assoc, key]; rfl

private theorem twSum_apply_mul_of_decomposed (ψ : AddChar (v.adicCompletion ℚ) ℂ) {p : LocalGL3 v}
    (M : Subgroup (LocalGL3 v)) (s : Finset (LocalGL3 v)) {F : ↥(principalSeries3 v χ)}
    (hsF : ∀ m ∈ M, ∑ r ∈ s, wt v ψ r * (F : LocalGL3 v → ℂ) (p * m * r) = psiN v ψ m * twValue v χ ψ s p F)
    {m₁ m₂ : LocalGL3 v} (hm₁ : m₁ ∈ absorbedBy v p) (hm₂ : m₂ ∈ M) :
    (twSum v χ ψ s F : LocalGL3 v → ℂ) (p * (m₁ * m₂)) = psiN v ψ m₂ * twValue v χ ψ s p F := by
  rw [twSum_apply, ← hsF m₂ hm₂]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_assoc p m₂ r, mul_assoc p (m₁ * m₂) r, mul_assoc m₁ m₂ r, apply_mul_absorbed v χ F hm₁]

private theorem twSum_apply_mul_of_not_decomposed (ψ : AddChar (v.adicCompletion ℚ) ℂ) {p : LocalGL3 v}
    (M : Subgroup (LocalGL3 v)) (s : Finset (LocalGL3 v)) (hsM : ∀ r ∈ s, r ∈ M) (hMN : ∀ m ∈ M, m ∈ unipotentSet v)
    {F : ↥(principalSeries3 v χ)}
    (hvF : ∀ m ∈ unipotentSet v, (¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) →
      (F : LocalGL3 v → ℂ) (p * m) = 0)
    {m : LocalGL3 v} (hm : m ∈ unipotentSet v) (hout : ¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) :
    (twSum v χ ψ s F : LocalGL3 v → ℂ) (p * m) = 0 := by
  rw [twSum_apply]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [mul_assoc, hvF (m * r) (mul_mem_unipotentSet v hm (hMN r (hsM r hr))) ?_, mul_zero]
  rintro ⟨m₁, hm₁, m₂, hm₂, hmr⟩
  refine hout ⟨m₁, hm₁, m₂ * r⁻¹, M.mul_mem hm₂ (M.inv_mem (hsM r hr)), ?_⟩
  rw [← mul_assoc, ← hmr, mul_inv_cancel_right]

private theorem exists_cell_data (ψ : AddChar (v.adicCompletion ℚ) ℂ) {Zi : Set (LocalGL3 v)} {p : LocalGL3 v}
    (hsplit : ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ unipotentSet v) ∧ ∀ m ∈ unipotentSet v,
        (∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi)
    (L : ℕ) (hψL : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → ψ x = 1) :
    ∃ (M : Subgroup (LocalGL3 v)) (s : Finset (LocalGL3 v)), (∀ m ∈ M, m ∈ unipotentSet v) ∧ s.Nonempty ∧
      (∀ r ∈ s, r ∈ M) ∧
      (∀ m ∈ unipotentSet v, (∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
        ∃ k : LocalGL3 v, IsPrincipalCongruence v L k ∧ p * m * k ∈ Zi) ∧
      ∀ F : ↥(principalSeries3 v χ),
        (∀ k : LocalGL3 v, IsPrincipalCongruence v L k →
          ∀ g, (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g) →
        ∀ m ∈ M, ∑ r ∈ s, wt v ψ r * (F : LocalGL3 v → ℂ) (p * m * r) = psiN v ψ m * twValue v χ ψ s p F := by
  obtain ⟨M, hMc, hMN, hM⟩ := hsplit L
  obtain ⟨s, hs0, hsM, hs⟩ := exists_finset_twisted v χ ψ L hψL M hMc hMN p
  exact ⟨M, s, hMN, hs0, hsM, hM, hs⟩

private theorem exists_mul_apply_eq_mul_apply_twisted (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    {Zi Zi1 : Set (LocalGL3 v)} {p : LocalGL3 v}
    (hN : ∀ g ∈ Zi, ∀ x y z : v.adicCompletion ℚ, g * upperUnipotent3 x y z ∈ Zi)
    (hcover : ∀ g ∈ Zi1, g ∉ Zi → ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
      (m : LocalGL3 v), m ∈ unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (p * m))
    (hsplit : ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ unipotentSet v) ∧ ∀ m ∈ unipotentSet v,
        (∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi)
    (hlevel : UniformlySmooth v χ)
    {n : ℕ} (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) (hΛ : ∀ j, IsWhittakerFunctional3 ψ (Λ j))
    (hkill : ∀ j, ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ Zi1, (F : LocalGL3 v → ℂ) g = 0) → Λ j F = 0)
    (f f' : ↥(principalSeries3 v χ))
    (hfZ : ∀ g ∈ Zi, (f : LocalGL3 v → ℂ) g = 0) (hf'Z : ∀ g ∈ Zi, (f' : LocalGL3 v → ℂ) g = 0) :
    ∃ c c' : ℂ, (∀ j, c' * Λ j f = c * Λ j f') ∧ (c = 0 → ∀ j, Λ j f = 0) := by
  classical
  obtain ⟨t₀, ht₀⟩ := hψA
  obtain ⟨t₁, ht₁⟩ := hlevel f f.2
  obtain ⟨t₂, ht₂⟩ := hlevel f' f'.2
  set L : ℕ := max (max t₁ t₂) t₀ with hL
  have hψL : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → ψ x = 1 := by
    intro x hx
    refine ht₀ x (hx.trans ?_)
    rw [WithZero.exp_le_exp]
    have : t₀ ≤ L := le_max_right _ _
    omega
  have hf : ∀ k, IsPrincipalCongruence v L k → ∀ g, (f : LocalGL3 v → ℂ) (g * k) = (f : LocalGL3 v → ℂ) g :=
    fun k hk g => apply_mul_eq_of_level v χ ht₁ ((le_max_left _ _).trans (le_max_left _ _)) hk g
  have hf' : ∀ k, IsPrincipalCongruence v L k → ∀ g, (f' : LocalGL3 v → ℂ) (g * k) = (f' : LocalGL3 v → ℂ) g :=
    fun k hk g => apply_mul_eq_of_level v χ ht₂ ((le_max_right _ _).trans (le_max_left _ _)) hk g
  obtain ⟨M, s, hMN, hs0, hsM, hM, hs⟩ := exists_cell_data v χ ψ hsplit L hψL
  have hsN : ∀ r ∈ s, r ∈ unipotentSet v := fun r hr => hMN r (hsM r hr)
  have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs0.card_pos.ne'
  have hvf : ∀ m ∈ unipotentSet v, (¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) →
      (f : LocalGL3 v → ℂ) (p * m) = 0 :=
    fun m hm hout => apply_mul_eq_zero_of_not_exists v χ hM hf hfZ hm hout
  have hvf' : ∀ m ∈ unipotentSet v, (¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) →
      (f' : LocalGL3 v → ℂ) (p * m) = 0 :=
    fun m hm hout => apply_mul_eq_zero_of_not_exists v χ hM hf' hf'Z hm hout

  have horbit : ∀ m ∈ unipotentSet v,
      twValue v χ ψ s p f' * (twSum v χ ψ s f : LocalGL3 v → ℂ) (p * m)
        = twValue v χ ψ s p f * (twSum v χ ψ s f' : LocalGL3 v → ℂ) (p * m) := by
    intro m hm
    by_cases hin : ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂
    · obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := hin
      rw [twSum_apply_mul_of_decomposed v χ ψ M s (hs f hf) hm₁ hm₂,
        twSum_apply_mul_of_decomposed v χ ψ M s (hs f' hf') hm₁ hm₂]
      ring
    · rw [twSum_apply_mul_of_not_decomposed v χ ψ M s hsM hMN hvf hm hin,
        twSum_apply_mul_of_not_decomposed v χ ψ M s hsM hMN hvf' hm hin]
      ring
  refine ⟨twValue v χ ψ s p f, twValue v χ ψ s p f', fun j => ?_, fun hI j => ?_⟩
  · have hD : Λ j (twValue v χ ψ s p f' • twSum v χ ψ s f - twValue v χ ψ s p f • twSum v χ ψ s f') = 0 := by
      refine hkill j _ fun g hg => ?_
      refine apply_eq_zero_of_forall_mul_eq_zero v χ hcover (fun g' hg' => ?_) (fun m hm => ?_) hg
      · simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [twSum_apply_eq_zero v χ ψ s hN hsN hfZ hg', twSum_apply_eq_zero v χ ψ s hN hsN hf'Z hg']
        ring
      · simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [horbit m hm, sub_self]
    rw [map_sub, map_smul, map_smul, apply_twSum v χ ψ (hΛ j) s hsN, apply_twSum v χ ψ (hΛ j) s hsN, smul_eq_mul,
      smul_eq_mul, sub_eq_zero] at hD
    exact mul_left_cancel₀ hcard (by linear_combination hD)
  · have hF : Λ j (twSum v χ ψ s f) = 0 := by
      refine hkill j _ fun g hg => ?_
      refine apply_eq_zero_of_forall_mul_eq_zero v χ hcover (fun g' hg' => ?_) (fun m hm => ?_) hg
      · exact twSum_apply_eq_zero v χ ψ s hN hsN hfZ hg'
      · by_cases hin : ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂
        · obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := hin
          rw [twSum_apply_mul_of_decomposed v χ ψ M s (hs f hf) hm₁ hm₂, hI, mul_zero]
        · exact twSum_apply_mul_of_not_decomposed v χ ψ M s hsM hMN hvf hm hin
    rw [apply_twSum v χ ψ (hΛ j) s hsN] at hF
    exact (mul_eq_zero.mp hF).resolve_left hcard

private theorem le_one_of_cell_twisted (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    {Zi Zi1 : Set (LocalGL3 v)} {p : LocalGL3 v}
    (hN : ∀ g ∈ Zi, ∀ x y z : v.adicCompletion ℚ, g * upperUnipotent3 x y z ∈ Zi)
    (hcover : ∀ g ∈ Zi1, g ∉ Zi → ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
      (m : LocalGL3 v), m ∈ unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (p * m))
    (hsplit : ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ unipotentSet v) ∧ ∀ m ∈ unipotentSet v,
        (∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi)
    (hlevel : UniformlySmooth v χ)
    (W₀ : Submodule ℂ ↥(principalSeries3 v χ))
    (hW₀ : ∀ F : ↥(principalSeries3 v χ), F ∈ W₀ ↔ ∀ g ∈ Zi, (F : LocalGL3 v → ℂ) g = 0)
    {n : ℕ} (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) (hΛ : ∀ j, IsWhittakerFunctional3 ψ (Λ j))
    (hkill : ∀ j, ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ Zi1, (F : LocalGL3 v → ℂ) g = 0) → Λ j F = 0)
    (hli : LinearIndependent ℂ fun j => (Λ j).domRestrict W₀) : n ≤ 1 :=
  le_one_of_forall_mem_exists_mul_eq_mul W₀ n Λ
    (fun f hf f' hf' => exists_mul_apply_eq_mul_apply_twisted v χ ψ hψA hN hcover hsplit hlevel Λ hΛ hkill f f'
      ((hW₀ f).mp hf) ((hW₀ f').mp hf'))
    hli

private theorem apply_eq_zero_of_cell_twisted (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    {Zi Zi1 : Set (LocalGL3 v)} {p c : LocalGL3 v}
    (hN : ∀ g ∈ Zi, ∀ x y z : v.adicCompletion ℚ, g * upperUnipotent3 x y z ∈ Zi)
    (hcover : ∀ g ∈ Zi1, g ∉ Zi → ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
      (m : LocalGL3 v), m ∈ unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (p * m))
    (hc : c ∈ absorbedBy v p) (hcψ : psiN v ψ c ≠ 1)
    (hsplit : ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ unipotentSet v) ∧
      (∀ m ∈ unipotentSet v, (∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
        ∃ k : LocalGL3 v, IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi) ∧
      ∀ d : LocalGL3 v, (d = c ∨ d = c⁻¹) → ∀ m₂ ∈ M,
        ∃ a ∈ absorbedBy v p, ∃ m₂' ∈ M, d⁻¹ * m₂ * d = a * m₂' ∧ psiN v ψ m₂' = psiN v ψ m₂)
    (hlevel : UniformlySmooth v χ)
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (hkill : ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ Zi1, (F : LocalGL3 v → ℂ) g = 0) → Λ F = 0)
    (F : ↥(principalSeries3 v χ)) (hFZ : ∀ g ∈ Zi, (F : LocalGL3 v → ℂ) g = 0) : Λ F = 0 := by
  classical
  obtain ⟨t₀, ht₀⟩ := hψA
  obtain ⟨t₁, ht₁⟩ := hlevel F F.2
  set L : ℕ := max t₁ t₀ with hL
  have hψL : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → ψ x = 1 := by
    intro x hx
    refine ht₀ x (hx.trans ?_)
    rw [WithZero.exp_le_exp]
    have : t₀ ≤ L := le_max_right _ _
    omega
  have hF : ∀ k, IsPrincipalCongruence v L k → ∀ g, (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g :=
    fun k hk g => apply_mul_eq_of_level v χ ht₁ (le_max_left _ _) hk g
  obtain ⟨M, hMc, hMN, hM, hconj⟩ := hsplit L
  obtain ⟨s, hs0, hsM, hs⟩ := exists_finset_twisted v χ ψ L hψL M hMc hMN p
  have hsN : ∀ r ∈ s, r ∈ unipotentSet v := fun r hr => hMN r (hsM r hr)
  have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs0.card_pos.ne'
  have hsF := hs F hF
  have hvF : ∀ m ∈ unipotentSet v, (¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) →
      (F : LocalGL3 v → ℂ) (p * m) = 0 :=
    fun m hm hout => apply_mul_eq_zero_of_not_exists v χ hM hF hFZ hm hout
  have hcN : c ∈ unipotentSet v := by
    obtain ⟨h, -⟩ := hc
    exact h
  have hc' : c⁻¹ ∈ absorbedBy v p := inv_mem_absorbedBy v hc

  have horbit : ∀ m ∈ unipotentSet v,
      (twSum v χ ψ s F : LocalGL3 v → ℂ) (p * (m * c)) = (twSum v χ ψ s F : LocalGL3 v → ℂ) (p * m) := by
    intro m hm
    by_cases hin : ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂
    · obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := hin
      obtain ⟨a, ha, m₂', hm₂', hconj', hψ'⟩ := hconj c (Or.inl rfl) m₂ hm₂
      have e : m₁ * m₂ * c = m₁ * (c * (a * m₂')) := by
        rw [← hconj']
        group
      rw [e, apply_mul_absorbed v χ _ hm₁, apply_mul_absorbed v χ _ hc, apply_mul_absorbed v χ _ ha,
        apply_mul_absorbed v χ _ hm₁]
      have h₁ := twSum_apply_mul_of_decomposed v χ ψ M s hsF (one_mem_absorbedBy' v p) hm₂'
      have h₂ := twSum_apply_mul_of_decomposed v χ ψ M s hsF (one_mem_absorbedBy' v p) hm₂
      rw [one_mul] at h₁ h₂
      rw [h₁, h₂, hψ']
    · have hout' : ¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m * c = m₁ * m₂ := by
        rintro ⟨a, ha, m₂, hm₂, hmc⟩
        obtain ⟨a', ha', m₂', hm₂', hconj', -⟩ := hconj c⁻¹ (Or.inr rfl) m₂ hm₂
        refine hin ⟨a * c⁻¹ * a', mul_mem_absorbedBy v (mul_mem_absorbedBy v ha hc') ha', m₂', hm₂', ?_⟩
        have e : m = a * m₂ * c⁻¹ := by rw [← hmc, mul_inv_cancel_right]
        rw [e, mul_assoc (a * c⁻¹), ← hconj']
        group
      rw [twSum_apply_mul_of_not_decomposed v χ ψ M s hsM hMN hvF (mul_mem_unipotentSet v hm hcN) hout',
        twSum_apply_mul_of_not_decomposed v χ ψ M s hsM hMN hvF hm hin]

  obtain ⟨x, y, z, hcxyz⟩ := id hcN
  have hD : Λ (translateSection v χ c (twSum v χ ψ s F) - twSum v χ ψ s F) = 0 := by
    refine hkill _ fun g hg => ?_
    refine apply_eq_zero_of_forall_mul_eq_zero v χ hcover (fun g' hg' => ?_) (fun m hm => ?_) hg
    · rw [Submodule.coe_sub, Pi.sub_apply, translateSection_apply, twSum_apply_eq_zero v χ ψ s hN hsN hFZ hg',
        sub_zero, hcxyz]
      exact twSum_apply_eq_zero v χ ψ s hN hsN hFZ (hN g' hg' x y z)
    · rw [Submodule.coe_sub, Pi.sub_apply, translateSection_apply, mul_assoc, horbit m hm, sub_self]
  rw [map_sub, apply_translateSection_of_isWhittakerFunctional3 v χ ψ hΛ hcN, sub_eq_zero,
    apply_twSum v χ ψ hΛ s hsN] at hD

  have h1 : (psiN v ψ c - 1) * ((s.card : ℂ) * Λ F) = 0 := by linear_combination hD
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h) hcψ
  · exact (mul_eq_zero.mp h).resolve_left hcard

end UnipotentBox
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction"

section LowerUnipotent

variable {A : Type*} [CommRing A]

private def lowerUnipotent3 (a b c : A) : Matrix.GeneralLinearGroup (Fin 3) A where
  val := !![1, 0, 0; a, 1, 0; b, c, 1]
  inv := !![1, 0, 0; -a, 1, 0; a * c - b, -c, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals ring

@[scoped simp] private theorem lowerUnipotent3_coe (a b c : A) :
    (lowerUnipotent3 a b c : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; a, 1, 0; b, c, 1] :=
  rfl

end LowerUnipotent

private theorem gl3Entry_mul_lowerUnipotent3_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a b c : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * lowerUnipotent3 a b c) i 0 = gl3Entry v g i 0 + gl3Entry v g i 1 * a + gl3Entry v g i 2 * b := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_lowerUnipotent3_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a b c : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * lowerUnipotent3 a b c) i 1 = gl3Entry v g i 1 + gl3Entry v g i 2 * c := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_lowerUnipotent3_two (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a b c : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * lowerUnipotent3 a b c) i 2 = gl3Entry v g i 2 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem valued_gl3Entry_lowerUnipotent3_sub_one_le (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ)
    {a b c : v.adicCompletion ℚ} (ha : Valued.v a ≤ WithZero.exp (-(t : ℤ)))
    (hb : Valued.v b ≤ WithZero.exp (-(t : ℤ))) (hc : Valued.v c ≤ WithZero.exp (-(t : ℤ))) (i j : Fin 3) :
    Valued.v (gl3Entry v (lowerUnipotent3 a b c) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
      ≤ WithZero.exp (-(t : ℤ)) := by
  have ha' : Valued.v a ≤ (WithZero.exp (t : ℤ))⁻¹ := ha
  have hb' : Valued.v b ≤ (WithZero.exp (t : ℤ))⁻¹ := hb
  have hc' : Valued.v c ≤ (WithZero.exp (t : ℤ))⁻¹ := hc
  fin_cases i <;> fin_cases j <;> simp [gl3Entry, ha', hb', hc']

private theorem valued_zero_le_exp_neg (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) :
    Valued.v (0 : v.adicCompletion ℚ) ≤ WithZero.exp (-(t : ℤ)) := by
  rw [map_zero]
  exact zero_le'

private theorem valued_neg_inv_le_exp_neg (v : HeightOneSpectrum (𝓞 ℚ)) {t : ℕ} {y : v.adicCompletion ℚ}
    (h : WithZero.exp (t : ℤ) ≤ Valued.v y) : Valued.v (-y⁻¹) ≤ WithZero.exp (-(t : ℤ)) := by
  have hy : Valued.v y ≠ 0 := fun h0 => WithZero.exp_ne_zero (le_zero_iff.1 (h0 ▸ h))
  rw [Valuation.map_neg, map_inv₀, WithZero.exp_neg]
  exact (inv_le_inv₀ (zero_lt_iff.2 hy) (zero_lt_iff.2 WithZero.exp_ne_zero)).2 h

private theorem valued_mul_inv_le_exp_neg (v : HeightOneSpectrum (𝓞 ℚ)) {t : ℕ} {y z : v.adicCompletion ℚ}
    (hy : Valued.v y ≤ WithZero.exp (t : ℤ)) (hz : WithZero.exp (2 * (t : ℤ)) ≤ Valued.v z) :
    Valued.v (y * z⁻¹) ≤ WithZero.exp (-(t : ℤ)) := by
  have hz0 : 0 < Valued.v z := lt_of_lt_of_le (zero_lt_iff.2 WithZero.exp_ne_zero) hz
  rw [map_mul, map_inv₀, ← div_eq_mul_inv, div_le_iff₀ hz0]
  calc Valued.v y ≤ WithZero.exp (t : ℤ) := hy
    _ = WithZero.exp (-(t : ℤ)) * WithZero.exp (2 * (t : ℤ)) := by
        rw [← WithZero.exp_add]
        congr 1
        ring
    _ ≤ WithZero.exp (-(t : ℤ)) * Valued.v z := mul_le_mul' le_rfl hz

private theorem gl3Entry_mul_permPoint120_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint120 v) i 0 = gl3Entry v g i 2 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint120_coe]

private theorem gl3Entry_mul_permPoint120_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint120 v) i 1 = gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint120_coe]

private theorem gl3Entry_mul_permPoint120_two (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint120 v) i 2 = gl3Entry v g i 1 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint120_coe]

private theorem gl3Entry_mul_permPoint201_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint201 v) i 0 = gl3Entry v g i 1 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint201_coe]

private theorem gl3Entry_mul_permPoint201_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint201 v) i 1 = gl3Entry v g i 2 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint201_coe]

private theorem gl3Entry_mul_permPoint201_two (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint201 v) i 2 = gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint201_coe]

private theorem permPoint201_mul_permPoint120 (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint201 v * permPoint120 v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, permPoint201_coe, permPoint120_coe]

private theorem permPoint120_mul_permPoint201 (v : HeightOneSpectrum (𝓞 ℚ)) :
    permPoint120 v * permPoint201 v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, permPoint201_coe, permPoint120_coe]

private theorem gl3Entry_permPoint201_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ))
    (y z : v.adicCompletion ℚ) :
    gl3Entry v (permPoint201 v * upperUnipotent3 0 y z) 1 0 = 1 ∧
      gl3Entry v (permPoint201 v * upperUnipotent3 0 y z) 1 1 = 0 ∧
        gl3Entry v (permPoint201 v * upperUnipotent3 0 y z) 1 2 = z ∧
          gl3Entry v (permPoint201 v * upperUnipotent3 0 y z) 2 0 = 0 ∧
            gl3Entry v (permPoint201 v * upperUnipotent3 0 y z) 2 1 = 1 ∧
              gl3Entry v (permPoint201 v * upperUnipotent3 0 y z) 2 2 = y := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint201_coe]

private theorem exists_eq_mul_permPoint201_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hg : g ∈ cornerChain v 4) (hg' : g ∉ cornerChain v 3) :
    ∃ (x' y' z' : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (y z : v.adicCompletion ℚ),
      g = upperUnipotent3 x' y' z' * diagonal3 v a * (permPoint201 v * upperUnipotent3 0 y z) := by
  have hc : gl3Entry v g 2 0 = 0 := (mem_cornerChain_four v g).1 hg
  have hprod : gl3Entry v g 1 0 * gl3Entry v g 2 1 ≠ 0 := fun h => hg' ((mem_cornerChain_three v g).2 ⟨hc, h⟩)
  have h10 : gl3Entry v g 1 0 ≠ 0 := left_ne_zero_of_mul hprod
  have h21 : gl3Entry v g 2 1 ≠ 0 := right_ne_zero_of_mul hprod
  obtain ⟨y, hy⟩ : ∃ y : v.adicCompletion ℚ, y = gl3Entry v g 2 2 / gl3Entry v g 2 1 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : v.adicCompletion ℚ,
      z = (gl3Entry v g 1 2 - y * gl3Entry v g 1 1) / gl3Entry v g 1 0 := ⟨_, rfl⟩
  have ey : y * gl3Entry v g 2 1 = gl3Entry v g 2 2 := by
    rw [hy, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ h21, mul_one]
  have ez : z * gl3Entry v g 1 0 = gl3Entry v g 1 2 - y * gl3Entry v g 1 1 := by
    rw [hz, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ h10, mul_one]
  have hb10 : gl3Entry v (g * upperUnipotent3 0 (-y) (-z) * permPoint120 v) 1 0 = 0 := by
    rw [gl3Entry_mul_permPoint120_zero, gl3Entry_mul_upperUnipotent3_two]
    linear_combination -ez
  have hb20 : gl3Entry v (g * upperUnipotent3 0 (-y) (-z) * permPoint120 v) 2 0 = 0 := by
    rw [gl3Entry_mul_permPoint120_zero, gl3Entry_mul_upperUnipotent3_two, hc]
    linear_combination -ey
  have hb21 : gl3Entry v (g * upperUnipotent3 0 (-y) (-z) * permPoint120 v) 2 1 = 0 := by
    rw [gl3Entry_mul_permPoint120_one, gl3Entry_mul_upperUnipotent3_zero, hc]
  obtain ⟨x', y', z', a, hb⟩ :=
    exists_eq_upperUnipotent3_mul_diagonal3 v (g * upperUnipotent3 0 (-y) (-z) * permPoint120 v) hb10 hb20 hb21
  refine ⟨x', y', z', a, y, z, ?_⟩
  rw [← hb, mul_assoc (g * upperUnipotent3 0 (-y) (-z)), ← mul_assoc (permPoint120 v),
    permPoint120_mul_permPoint201, one_mul, mul_assoc g, UnipotentBox.unipotent_mul v]
  simp

private theorem exists_mul_mem_cornerChain_three (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (y z : v.adicCompletion ℚ)
    (h : ¬ (Valued.v y ≤ WithZero.exp (t : ℤ) ∧ Valued.v z ≤ WithZero.exp (2 * (t : ℤ)))) :
    ∃ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(t : ℤ))) ∧
      permPoint201 v * upperUnipotent3 0 y z * k ∈ cornerChain v 3 := by
  obtain ⟨s10, s11, s12, s20, s21, s22⟩ := gl3Entry_permPoint201_mul_upperUnipotent3 v y z
  by_cases hy : Valued.v y ≤ WithZero.exp (t : ℤ)
  · have hz : WithZero.exp (2 * (t : ℤ)) < Valued.v z := not_le.1 fun hz => h ⟨hy, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    have ht : WithZero.exp (t : ℤ) ≤ Valued.v z :=
      le_trans (WithZero.exp_le_exp.2 (by omega)) hz.le
    refine ⟨lowerUnipotent3 (y * z⁻¹) (-z⁻¹) 0, fun i j =>
      valued_gl3Entry_lowerUnipotent3_sub_one_le v t (valued_mul_inv_le_exp_neg v hy hz.le)
        (valued_neg_inv_le_exp_neg v ht) (valued_zero_le_exp_neg v t) i j, ?_⟩
    have e10 : gl3Entry v (permPoint201 v * upperUnipotent3 0 y z * lowerUnipotent3 (y * z⁻¹) (-z⁻¹) 0) 1 0 = 0 := by
      rw [gl3Entry_mul_lowerUnipotent3_zero, s10, s11, s12, zero_mul, add_zero, mul_neg, mul_inv_cancel₀ hz0,
        add_neg_cancel]
    refine (mem_cornerChain_three v _).2 ⟨?_, ?_⟩
    · show gl3Entry v (permPoint201 v * upperUnipotent3 0 y z * lowerUnipotent3 (y * z⁻¹) (-z⁻¹) 0) 2 0 = 0
      rw [gl3Entry_mul_lowerUnipotent3_zero, s20, s21, s22]
      ring
    · rw [e10, zero_mul]
  · have hy' : WithZero.exp (t : ℤ) < Valued.v y := not_le.1 hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy'
    refine ⟨lowerUnipotent3 0 0 (-y⁻¹), fun i j =>
      valued_gl3Entry_lowerUnipotent3_sub_one_le v t (valued_zero_le_exp_neg v t) (valued_zero_le_exp_neg v t)
        (valued_neg_inv_le_exp_neg v hy'.le) i j, ?_⟩
    have e21 : gl3Entry v (permPoint201 v * upperUnipotent3 0 y z * lowerUnipotent3 0 0 (-y⁻¹)) 2 1 = 0 := by
      rw [gl3Entry_mul_lowerUnipotent3_one, s21, s22, mul_neg, mul_inv_cancel₀ hy0, add_neg_cancel]
    refine (mem_cornerChain_three v _).2 ⟨?_, ?_⟩
    · show gl3Entry v (permPoint201 v * upperUnipotent3 0 y z * lowerUnipotent3 0 0 (-y⁻¹)) 2 0 = 0
      rw [gl3Entry_mul_lowerUnipotent3_zero, s20, s21, s22]
      ring
    · rw [e21, mul_zero]

private theorem gl3Entry_permPoint120_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ))
    (x z : v.adicCompletion ℚ) :
    gl3Entry v (permPoint120 v * upperUnipotent3 x 0 z) 2 0 = 1 ∧
      gl3Entry v (permPoint120 v * upperUnipotent3 x 0 z) 2 1 = x ∧
        gl3Entry v (permPoint120 v * upperUnipotent3 x 0 z) 2 2 = z := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint120_coe]

private theorem exists_eq_mul_permPoint120_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hg : g ∈ cornerChain v 5) (hg' : g ∉ cornerChain v 4) :
    ∃ (x' y' z' : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (x z : v.adicCompletion ℚ),
      g = upperUnipotent3 x' y' z' * diagonal3 v a * (permPoint120 v * upperUnipotent3 x 0 z) := by
  have hc : gl3Entry v g 2 0 ≠ 0 := fun h => hg' ((mem_cornerChain_four v g).2 h)
  have hm : gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0 = 0 :=
    (mul_eq_zero.1 ((mem_cornerChain_five v g).1 hg)).resolve_left hc
  obtain ⟨x, hx⟩ : ∃ x : v.adicCompletion ℚ, x = gl3Entry v g 2 1 / gl3Entry v g 2 0 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : v.adicCompletion ℚ, z = gl3Entry v g 2 2 / gl3Entry v g 2 0 := ⟨_, rfl⟩
  have ex : x * gl3Entry v g 2 0 = gl3Entry v g 2 1 := by
    rw [hx, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have ez : z * gl3Entry v g 2 0 = gl3Entry v g 2 2 := by
    rw [hz, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hb10 : gl3Entry v (g * upperUnipotent3 (-x) 0 (-z) * permPoint201 v) 1 0 = 0 := by
    rw [gl3Entry_mul_permPoint201_zero, gl3Entry_mul_upperUnipotent3_one]
    have h : (gl3Entry v g 1 0 * -x + gl3Entry v g 1 1) * gl3Entry v g 2 0 = 0 := by
      linear_combination (-gl3Entry v g 1 0) * ex - hm
    exact (mul_eq_zero.1 h).resolve_right hc
  have hb20 : gl3Entry v (g * upperUnipotent3 (-x) 0 (-z) * permPoint201 v) 2 0 = 0 := by
    rw [gl3Entry_mul_permPoint201_zero, gl3Entry_mul_upperUnipotent3_one]
    linear_combination -ex
  have hb21 : gl3Entry v (g * upperUnipotent3 (-x) 0 (-z) * permPoint201 v) 2 1 = 0 := by
    rw [gl3Entry_mul_permPoint201_one, gl3Entry_mul_upperUnipotent3_two]
    linear_combination -ez
  obtain ⟨x', y', z', a, hb⟩ :=
    exists_eq_upperUnipotent3_mul_diagonal3 v (g * upperUnipotent3 (-x) 0 (-z) * permPoint201 v) hb10 hb20 hb21
  refine ⟨x', y', z', a, x, z, ?_⟩
  rw [← hb, mul_assoc (g * upperUnipotent3 (-x) 0 (-z)), ← mul_assoc (permPoint201 v),
    permPoint201_mul_permPoint120, one_mul, mul_assoc g, UnipotentBox.unipotent_mul v]
  simp

private theorem exists_mul_mem_cornerChain_four (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (x z : v.adicCompletion ℚ)
    (h : ¬ (Valued.v x ≤ WithZero.exp (t : ℤ) ∧ Valued.v z ≤ WithZero.exp (t : ℤ))) :
    ∃ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(t : ℤ))) ∧
      permPoint120 v * upperUnipotent3 x 0 z * k ∈ cornerChain v 4 := by
  obtain ⟨s20, s21, s22⟩ := gl3Entry_permPoint120_mul_upperUnipotent3 v x z
  by_cases hx : Valued.v x ≤ WithZero.exp (t : ℤ)
  · have hz : WithZero.exp (t : ℤ) < Valued.v z := not_le.1 fun hz => h ⟨hx, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    refine ⟨lowerUnipotent3 0 (-z⁻¹) 0, fun i j =>
      valued_gl3Entry_lowerUnipotent3_sub_one_le v t (valued_zero_le_exp_neg v t) (valued_neg_inv_le_exp_neg v hz.le)
        (valued_zero_le_exp_neg v t) i j, (mem_cornerChain_four v _).2 ?_⟩
    show gl3Entry v (permPoint120 v * upperUnipotent3 x 0 z * lowerUnipotent3 0 (-z⁻¹) 0) 2 0 = 0
    rw [gl3Entry_mul_lowerUnipotent3_zero, s20, s21, s22, mul_zero, add_zero, mul_neg, mul_inv_cancel₀ hz0,
      add_neg_cancel]
  · have hx' : WithZero.exp (t : ℤ) < Valued.v x := not_le.1 hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx'
    refine ⟨lowerUnipotent3 (-x⁻¹) 0 0, fun i j =>
      valued_gl3Entry_lowerUnipotent3_sub_one_le v t (valued_neg_inv_le_exp_neg v hx'.le) (valued_zero_le_exp_neg v t)
        (valued_zero_le_exp_neg v t) i j, (mem_cornerChain_four v _).2 ?_⟩
    show gl3Entry v (permPoint120 v * upperUnipotent3 x 0 z * lowerUnipotent3 (-x⁻¹) 0 0) 2 0 = 0
    rw [gl3Entry_mul_lowerUnipotent3_zero, s20, s21, s22, mul_zero, add_zero, mul_neg, mul_inv_cancel₀ hx0,
      add_neg_cancel]
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction"

private theorem gl3Entry_mul_permPoint102_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint102 v) i 0 = gl3Entry v g i 1 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint102_coe]

private theorem gl3Entry_mul_permPoint102_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint102 v) i 1 = gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint102_coe]

private theorem permPoint102_mul_self (v : HeightOneSpectrum (𝓞 ℚ)) : permPoint102 v * permPoint102 v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, permPoint102_coe]

private theorem exists_eq_mul_permPoint102_mul_of_mem_cornerChain_two (v : HeightOneSpectrum (𝓞 ℚ))
    {g : LocalGL3 v} (hg : g ∈ cornerChain v 2) (hg' : g ∉ cornerChain v 1) :
    ∃ (x' y' z' : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      g = upperUnipotent3 x' y' z' * diagonal3 v a * (permPoint102 v * upperUnipotent3 x 0 0) := by
  have hc : gl3Entry v g 2 0 = 0 := ((mem_cornerChain_two v g).1 hg).1
  have h21 : gl3Entry v g 2 1 = 0 := ((mem_cornerChain_two v g).1 hg).2
  have h10 : gl3Entry v g 1 0 ≠ 0 := fun h => hg' ((mem_cornerChain_one v g).2 ⟨hc, h, h21⟩)
  obtain ⟨x, hx⟩ : ∃ x : v.adicCompletion ℚ, x = gl3Entry v g 1 1 / gl3Entry v g 1 0 := ⟨_, rfl⟩
  have ex : x * gl3Entry v g 1 0 = gl3Entry v g 1 1 := by
    rw [hx, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ h10, mul_one]
  have hb10 : gl3Entry v (g * upperUnipotent3 (-x) 0 0 * permPoint102 v) 1 0 = 0 := by
    rw [gl3Entry_mul_permPoint102_zero, gl3Entry_mul_upperUnipotent3_one]
    linear_combination -ex
  have hb20 : gl3Entry v (g * upperUnipotent3 (-x) 0 0 * permPoint102 v) 2 0 = 0 := by
    simp [gl3Entry_mul_permPoint102_zero, gl3Entry_mul_upperUnipotent3_one, hc, h21]
  have hb21 : gl3Entry v (g * upperUnipotent3 (-x) 0 0 * permPoint102 v) 2 1 = 0 := by
    simp [gl3Entry_mul_permPoint102_one, gl3Entry_mul_upperUnipotent3_zero, hc]
  obtain ⟨x', y', z', a, hb⟩ :=
    exists_eq_upperUnipotent3_mul_diagonal3 v (g * upperUnipotent3 (-x) 0 0 * permPoint102 v) hb10 hb20 hb21
  refine ⟨x', y', z', a, x, ?_⟩
  rw [← hb, mul_assoc (g * upperUnipotent3 (-x) 0 0), ← mul_assoc (permPoint102 v), permPoint102_mul_self,
    one_mul, mul_assoc g, UnipotentBox.unipotent_mul v]
  simp

private theorem exists_lowerUnipotent3_permPoint102_mul_mul_mem_cornerChain_one (v : HeightOneSpectrum (𝓞 ℚ))
    (t : ℕ) {x : v.adicCompletion ℚ} (y z : v.adicCompletion ℚ) (hx : WithZero.exp (t : ℤ) < Valued.v x) :
    ∃ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(t : ℤ))) ∧
        permPoint102 v * upperUnipotent3 x y z * k ∈ cornerChain v 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  refine ⟨lowerUnipotent3 (-x⁻¹) 0 0, valued_gl3Entry_lowerUnipotent3_sub_one_le v t
    (valued_neg_inv_le_exp_neg v hx.le) (valued_zero_le_exp_neg v t) (valued_zero_le_exp_neg v t), ?_, ?_, ?_⟩
  · simp [cornerEntry, gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint102_coe]
  · simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint102_coe, hx0]
  · simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint102_coe]

private theorem permPoint102_mul_diagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    permPoint102 v * diagonal3 v a = diagonal3 v (a ∘ ⇑(Equiv.swap (0 : Fin 3) 1)) * permPoint102 v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permPoint102_coe, Matrix.mul_apply, Fin.sum_univ_three, Equiv.swap_apply_of_ne_of_ne]

private theorem gl3Entry_mul_permPoint021_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint021 v) i 0 = gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint021_coe]

private theorem gl3Entry_mul_permPoint021_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * permPoint021 v) i 1 = gl3Entry v g i 2 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint021_coe]

private theorem permPoint021_mul_self (v : HeightOneSpectrum (𝓞 ℚ)) : permPoint021 v * permPoint021 v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, permPoint021_coe]

private theorem exists_eq_mul_permPoint021_mul_of_mem_cornerChain_three (v : HeightOneSpectrum (𝓞 ℚ))
    {g : LocalGL3 v} (hg : g ∈ cornerChain v 3) (hg' : g ∉ cornerChain v 2) :
    ∃ (x' y' z' : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (y : v.adicCompletion ℚ),
      g = upperUnipotent3 x' y' z' * diagonal3 v a * (permPoint021 v * upperUnipotent3 0 y 0) := by
  have hc : gl3Entry v g 2 0 = 0 := ((mem_cornerChain_three v g).1 hg).1
  have h21 : gl3Entry v g 2 1 ≠ 0 := fun h => hg' ((mem_cornerChain_two v g).2 ⟨hc, h⟩)
  have h10 : gl3Entry v g 1 0 = 0 := (mul_eq_zero.1 ((mem_cornerChain_three v g).1 hg).2).resolve_right h21
  obtain ⟨y, hy⟩ : ∃ y : v.adicCompletion ℚ, y = gl3Entry v g 2 2 / gl3Entry v g 2 1 := ⟨_, rfl⟩
  have ey : y * gl3Entry v g 2 1 = gl3Entry v g 2 2 := by
    rw [hy, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ h21, mul_one]
  have hb10 : gl3Entry v (g * upperUnipotent3 0 (-y) 0 * permPoint021 v) 1 0 = 0 := by
    simp [gl3Entry_mul_permPoint021_zero, gl3Entry_mul_upperUnipotent3_zero, h10]
  have hb20 : gl3Entry v (g * upperUnipotent3 0 (-y) 0 * permPoint021 v) 2 0 = 0 := by
    simp [gl3Entry_mul_permPoint021_zero, gl3Entry_mul_upperUnipotent3_zero, hc]
  have hb21 : gl3Entry v (g * upperUnipotent3 0 (-y) 0 * permPoint021 v) 2 1 = 0 := by
    rw [gl3Entry_mul_permPoint021_one, gl3Entry_mul_upperUnipotent3_two]
    linear_combination -ey
  obtain ⟨x', y', z', a, hb⟩ :=
    exists_eq_upperUnipotent3_mul_diagonal3 v (g * upperUnipotent3 0 (-y) 0 * permPoint021 v) hb10 hb20 hb21
  refine ⟨x', y', z', a, y, ?_⟩
  rw [← hb, mul_assoc (g * upperUnipotent3 0 (-y) 0), ← mul_assoc (permPoint021 v), permPoint021_mul_self,
    one_mul, mul_assoc g, UnipotentBox.unipotent_mul v]
  simp

private theorem exists_lowerUnipotent3_permPoint021_mul_mul_mem_cornerChain_two (v : HeightOneSpectrum (𝓞 ℚ))
    (t : ℕ) (x : v.adicCompletion ℚ) {y : v.adicCompletion ℚ} (z : v.adicCompletion ℚ)
    (hy : WithZero.exp (t : ℤ) < Valued.v y) :
    ∃ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(t : ℤ))) ∧
        permPoint021 v * upperUnipotent3 x y z * k ∈ cornerChain v 2 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  refine ⟨lowerUnipotent3 0 0 (-y⁻¹), valued_gl3Entry_lowerUnipotent3_sub_one_le v t
    (valued_zero_le_exp_neg v t) (valued_zero_le_exp_neg v t) (valued_neg_inv_le_exp_neg v hy.le), ?_, ?_⟩
  · simp [cornerEntry, gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint021_coe]
  · simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, permPoint021_coe, hy0]

private theorem permPoint021_mul_diagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    permPoint021 v * diagonal3 v a = diagonal3 v (a ∘ ⇑(Equiv.swap (1 : Fin 3) 2)) * permPoint021 v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permPoint021_coe, Matrix.mul_apply, Fin.sum_univ_three, Equiv.swap_apply_of_ne_of_ne]
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction"

private theorem gl3Entry_mul_antidiagonal3_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * antidiagonal3 v) i 0 = gl3Entry v g i 2 := by
  simp [gl3Entry, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_antidiagonal3_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * antidiagonal3 v) i 1 = gl3Entry v g i 1 := by
  simp [gl3Entry, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem antidiagonal3_mul_antidiagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    antidiagonal3 v * antidiagonal3 v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem one_mem_absorbedBy (v : HeightOneSpectrum (𝓞 ℚ)) (p : LocalGL3 v) :
    (1 : LocalGL3 v) ∈ UnipotentBox.absorbedBy v p :=
  ⟨⟨0, 0, 0, upperUnipotent3_zero.symm⟩, 0, 0, 0, by simp⟩

private theorem ne_zero_of_exp_lt_valued (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ} {s : ℤ}
    (hx : WithZero.exp s < Valued.v x) : x ≠ 0 := by
  rintro rfl
  simp at hx

private theorem exists_eq_mul_antidiagonal3_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hg : g ∉ cornerChain v 5) :
    ∃ (x' y' z' : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ),
      g = upperUnipotent3 x' y' z' * diagonal3 v a * (antidiagonal3 v * upperUnipotent3 x y z) := by
  have hcm : cornerEntry v g * lowerMinor v g ≠ 0 := fun h => hg ((mem_cornerChain_five v g).mpr h)
  have hc : gl3Entry v g 2 0 ≠ 0 := left_ne_zero_of_mul hcm
  have hm : gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0 ≠ 0 := right_ne_zero_of_mul hcm
  set x : v.adicCompletion ℚ := gl3Entry v g 2 1 / gl3Entry v g 2 0 with hx
  set z : v.adicCompletion ℚ := gl3Entry v g 2 2 / gl3Entry v g 2 0 with hz
  set y : v.adicCompletion ℚ := (gl3Entry v g 1 0 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 0)
    / (gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0) with hy
  have ex : x * gl3Entry v g 2 0 = gl3Entry v g 2 1 := by
    rw [hx, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have ez : z * gl3Entry v g 2 0 = gl3Entry v g 2 2 := by
    rw [hz, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have ey : y * (gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0)
      = gl3Entry v g 1 0 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 0 := by
    rw [hy, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hm, mul_one]
  set h : LocalGL3 v := g * upperUnipotent3 (-x) (-y) (x * y - z) * antidiagonal3 v with hh
  have h₁₀ : gl3Entry v h 1 0 = 0 := by
    rw [hh, gl3Entry_mul_antidiagonal3_zero, gl3Entry_mul_upperUnipotent3_two]
    apply mul_left_cancel₀ hc
    linear_combination (gl3Entry v g 1 0 * y) * ex - gl3Entry v g 1 0 * ez + ey
  have h₂₀ : gl3Entry v h 2 0 = 0 := by
    rw [hh, gl3Entry_mul_antidiagonal3_zero, gl3Entry_mul_upperUnipotent3_two]
    linear_combination y * ex - ez
  have h₂₁ : gl3Entry v h 2 1 = 0 := by
    rw [hh, gl3Entry_mul_antidiagonal3_one, gl3Entry_mul_upperUnipotent3_one]
    linear_combination -ex
  obtain ⟨x', y', z', a, hfac⟩ := exists_eq_upperUnipotent3_mul_diagonal3 v h h₁₀ h₂₀ h₂₁
  refine ⟨x', y', z', a, x, y, z, ?_⟩
  have hg' : g = h * antidiagonal3 v * upperUnipotent3 x y z := by
    rw [hh, mul_assoc (g * _), antidiagonal3_mul_antidiagonal3, mul_one, mul_assoc,
      ← UnipotentBox.unipotent_inv v x y z, inv_mul_cancel, mul_one]
  rw [hg', hfac]
  simp only [mul_assoc]

private theorem exists_antidiagonal3_mul_mul_mem_cornerChain_five (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ)
    (x y z : v.adicCompletion ℚ)
    (hfar : ¬ (Valued.v x ≤ WithZero.exp (t : ℤ) ∧ Valued.v y ≤ WithZero.exp (t : ℤ) ∧
      Valued.v z ≤ WithZero.exp (2 * (t : ℤ)))) :
    ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧
      antidiagonal3 v * upperUnipotent3 x y z * k ∈ cornerChain v 5 := by
  have h0 := valued_zero_le_exp_neg v t
  by_cases hx : WithZero.exp (t : ℤ) < Valued.v x
  · have hx0 : x ≠ 0 := ne_zero_of_exp_lt_valued v hx
    refine ⟨lowerUnipotent3 (-x⁻¹) 0 0,
      valued_gl3Entry_lowerUnipotent3_sub_one_le v t (valued_neg_inv_le_exp_neg v hx.le) h0 h0, ?_⟩
    show cornerEntry v _ * lowerMinor v _ = 0
    simp [cornerEntry, lowerMinor, gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, antidiagonal3_coe, hx0]
  by_cases hy : WithZero.exp (t : ℤ) < Valued.v y
  · have hy0 : y ≠ 0 := ne_zero_of_exp_lt_valued v hy
    refine ⟨lowerUnipotent3 0 0 (-y⁻¹),
      valued_gl3Entry_lowerUnipotent3_sub_one_le v t h0 h0 (valued_neg_inv_le_exp_neg v hy.le), ?_⟩
    show cornerEntry v _ * lowerMinor v _ = 0
    simp [cornerEntry, lowerMinor, gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, antidiagonal3_coe, hy0]
  have hz : WithZero.exp (2 * (t : ℤ)) < Valued.v z :=
    lt_of_not_ge fun hz => hfar ⟨not_lt.mp hx, not_lt.mp hy, hz⟩
  have hz0 : z ≠ 0 := ne_zero_of_exp_lt_valued v hz
  have hz' : WithZero.exp (t : ℤ) ≤ Valued.v z := by
    refine le_trans ?_ hz.le
    rw [WithZero.exp_le_exp]
    omega
  refine ⟨lowerUnipotent3 0 (-z⁻¹) 0,
    valued_gl3Entry_lowerUnipotent3_sub_one_le v t h0 (valued_neg_inv_le_exp_neg v hz') h0, ?_⟩
  show cornerEntry v _ * lowerMinor v _ = 0
  simp [cornerEntry, lowerMinor, gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, antidiagonal3_coe, hz0]

private theorem antidiagonal3_mul_diagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    antidiagonal3 v * diagonal3 v a = diagonal3 v (a ∘ ⇑(Equiv.swap (0 : Fin 3) 2)) * antidiagonal3 v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antidiagonal3_coe, diagonal3, Matrix.mul_apply, Matrix.diagonal, Equiv.swap_apply_def]
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction"

private theorem permPoint102_mul_upperUnipotent3_comm (v : HeightOneSpectrum (𝓞 ℚ)) (y z : v.adicCompletion ℚ) :
    permPoint102 v * upperUnipotent3 0 y z = upperUnipotent3 0 z y * permPoint102 v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, permPoint102_coe]

private theorem permPoint021_mul_upperUnipotent3_comm (v : HeightOneSpectrum (𝓞 ℚ)) (x z : v.adicCompletion ℚ) :
    permPoint021 v * upperUnipotent3 x 0 z = upperUnipotent3 z 0 x * permPoint021 v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, permPoint021_coe]

private theorem permPoint201_mul_upperUnipotent3_comm (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    permPoint201 v * upperUnipotent3 x 0 0 = upperUnipotent3 0 x 0 * permPoint201 v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, permPoint201_coe]

private theorem permPoint120_mul_upperUnipotent3_comm (v : HeightOneSpectrum (𝓞 ℚ)) (y : v.adicCompletion ℚ) :
    permPoint120 v * upperUnipotent3 0 y 0 = upperUnipotent3 y 0 0 * permPoint120 v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, permPoint120_coe]

private theorem exists_mul_one_mul_of_mem_cornerChain_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ g ∈ cornerChain v 1, g ∉ cornerChain v 0 →
      ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (m : LocalGL3 v),
        m ∈ UnipotentBox.unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (1 * m) := by
  intro g hg _
  obtain ⟨x, y, z, a, h⟩ := exists_eq_upperUnipotent3_mul_diagonal3_of_mem_cornerChain_one v hg
  refine ⟨x, y, z, a, upperUnipotent3 0 0 0, ⟨0, 0, 0, rfl⟩, ?_⟩
  rw [upperUnipotent3_zero, mul_one, mul_one]
  exact h

private theorem exists_box_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧ ∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v (1 : LocalGL3 v), ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧ 1 * m * k ∈ cornerChain v 0 := by
  intro t
  have hρ : (0 : WithZero (Multiplicative ℤ)) * 0 ≤ 0 := by simp
  refine ⟨UnipotentBox.box v 0 0 0 hρ, UnipotentBox.isCompact_box v _ _ _ hρ,
    fun m hm => UnipotentBox.mem_unipotentSet_of_mem_box v hm, fun m hm => Or.inl ⟨m, ⟨hm, ?_⟩, 1, Subgroup.one_mem _,
      (mul_one m).symm⟩⟩
  obtain ⟨x, y, z, rfl⟩ := hm
  exact ⟨x, y, z, by rw [one_mul, mul_one]⟩

private theorem exists_mul_permPoint102_mul_of_mem_cornerChain_two (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ g ∈ cornerChain v 2, g ∉ cornerChain v 1 →
      ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (m : LocalGL3 v),
        m ∈ UnipotentBox.unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (permPoint102 v * m) := by
  intro g hg hg'
  obtain ⟨x', y', z', a, x, h⟩ := exists_eq_mul_permPoint102_mul_of_mem_cornerChain_two v hg hg'
  exact ⟨x', y', z', a, _, ⟨x, 0, 0, rfl⟩, h⟩

private theorem exists_box_permPoint102 (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧ ∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v (permPoint102 v), ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧
            permPoint102 v * m * k ∈ cornerChain v 1 := by
  intro t
  have hρ : WithZero.exp (t : ℤ) * (0 : WithZero (Multiplicative ℤ)) ≤ 0 := by simp
  refine ⟨UnipotentBox.box v (WithZero.exp (t : ℤ)) 0 0 hρ, UnipotentBox.isCompact_box v _ _ _ hρ,
    fun m hm => UnipotentBox.mem_unipotentSet_of_mem_box v hm, ?_⟩
  rintro m ⟨x, y, z, rfl⟩
  have hdec : (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 0 y z * upperUnipotent3 x 0 0 := by
    rw [UnipotentBox.unipotent_mul v]
    congr 1 <;> ring
  by_cases hb : Valued.v x ≤ WithZero.exp (t : ℤ)
  · exact Or.inl ⟨upperUnipotent3 0 y z, ⟨⟨0, y, z, rfl⟩, 0, z, y, permPoint102_mul_upperUnipotent3_comm v y z⟩,
      upperUnipotent3 x 0 0, UnipotentBox.upperUnipotent3_mem_box v hb (by simp) (by simp), hdec⟩
  · obtain ⟨k, hk, hmem⟩ :=
      exists_lowerUnipotent3_permPoint102_mul_mul_mem_cornerChain_one v t y z (not_le.1 hb)
    exact Or.inr ⟨k, hk, hmem⟩

private theorem exists_mul_permPoint021_mul_of_mem_cornerChain_three (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ g ∈ cornerChain v 3, g ∉ cornerChain v 2 →
      ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (m : LocalGL3 v),
        m ∈ UnipotentBox.unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (permPoint021 v * m) := by
  intro g hg hg'
  obtain ⟨x', y', z', a, y, h⟩ := exists_eq_mul_permPoint021_mul_of_mem_cornerChain_three v hg hg'
  exact ⟨x', y', z', a, _, ⟨0, y, 0, rfl⟩, h⟩

private theorem exists_box_permPoint021 (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧ ∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v (permPoint021 v), ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧
            permPoint021 v * m * k ∈ cornerChain v 2 := by
  intro t
  have hρ : (0 : WithZero (Multiplicative ℤ)) * WithZero.exp (t : ℤ) ≤ 0 := by simp
  refine ⟨UnipotentBox.box v 0 (WithZero.exp (t : ℤ)) 0 hρ, UnipotentBox.isCompact_box v _ _ _ hρ,
    fun m hm => UnipotentBox.mem_unipotentSet_of_mem_box v hm, ?_⟩
  rintro m ⟨x, y, z, rfl⟩
  have hdec : (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 x 0 (z - x * y) * upperUnipotent3 0 y 0 := by
    rw [UnipotentBox.unipotent_mul v]
    congr 1 <;> ring
  by_cases hb : Valued.v y ≤ WithZero.exp (t : ℤ)
  · exact Or.inl ⟨upperUnipotent3 x 0 (z - x * y),
      ⟨⟨x, 0, z - x * y, rfl⟩, z - x * y, 0, x, permPoint021_mul_upperUnipotent3_comm v x (z - x * y)⟩,
      upperUnipotent3 0 y 0, UnipotentBox.upperUnipotent3_mem_box v (by simp) hb (by simp), hdec⟩
  · obtain ⟨k, hk, hmem⟩ :=
      exists_lowerUnipotent3_permPoint021_mul_mul_mem_cornerChain_two v t x z (not_le.1 hb)
    exact Or.inr ⟨k, hk, hmem⟩

private theorem exists_mul_permPoint201_mul_of_mem_cornerChain_four (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ g ∈ cornerChain v 4, g ∉ cornerChain v 3 →
      ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (m : LocalGL3 v),
        m ∈ UnipotentBox.unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (permPoint201 v * m) := by
  intro g hg hg'
  obtain ⟨x', y', z', a, y, z, h⟩ := exists_eq_mul_permPoint201_mul_upperUnipotent3 v hg hg'
  exact ⟨x', y', z', a, _, ⟨0, y, z, rfl⟩, h⟩

private theorem exists_box_permPoint201 (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧ ∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v (permPoint201 v), ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧
            permPoint201 v * m * k ∈ cornerChain v 3 := by
  intro t
  have hρ : (0 : WithZero (Multiplicative ℤ)) * WithZero.exp (t : ℤ) ≤ WithZero.exp (2 * (t : ℤ)) := by simp
  refine ⟨UnipotentBox.box v 0 (WithZero.exp (t : ℤ)) (WithZero.exp (2 * (t : ℤ))) hρ,
    UnipotentBox.isCompact_box v _ _ _ hρ, fun m hm => UnipotentBox.mem_unipotentSet_of_mem_box v hm, ?_⟩
  rintro m ⟨x, y, z, rfl⟩
  have hdec : (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 x 0 0 * upperUnipotent3 0 y (z - x * y) := by
    rw [UnipotentBox.unipotent_mul v]
    congr 1 <;> ring
  by_cases hb : Valued.v y ≤ WithZero.exp (t : ℤ) ∧ Valued.v (z - x * y) ≤ WithZero.exp (2 * (t : ℤ))
  · exact Or.inl ⟨upperUnipotent3 x 0 0, ⟨⟨x, 0, 0, rfl⟩, 0, x, 0, permPoint201_mul_upperUnipotent3_comm v x⟩,
      upperUnipotent3 0 y (z - x * y), UnipotentBox.upperUnipotent3_mem_box v (by simp) hb.1 hb.2, hdec⟩
  · obtain ⟨k, hk, hmem⟩ := exists_mul_mem_cornerChain_three v t y (z - x * y) hb
    refine Or.inr ⟨k, hk, ?_⟩
    have h : permPoint201 v * upperUnipotent3 x y z * k =
        upperUnipotent3 0 x 0 * (permPoint201 v * upperUnipotent3 0 y (z - x * y) * k) := by
      rw [hdec, ← mul_assoc (permPoint201 v), permPoint201_mul_upperUnipotent3_comm]
      simp only [mul_assoc]
    rw [h]
    exact upperUnipotent3_mul_mem_cornerChain v 3 hmem 0 x 0

private theorem exists_mul_permPoint120_mul_of_mem_cornerChain_five (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ g ∈ cornerChain v 5, g ∉ cornerChain v 4 →
      ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (m : LocalGL3 v),
        m ∈ UnipotentBox.unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (permPoint120 v * m) := by
  intro g hg hg'
  obtain ⟨x', y', z', a, x, z, h⟩ := exists_eq_mul_permPoint120_mul_upperUnipotent3 v hg hg'
  exact ⟨x', y', z', a, _, ⟨x, 0, z, rfl⟩, h⟩

private theorem exists_box_permPoint120 (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧ ∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v (permPoint120 v), ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧
            permPoint120 v * m * k ∈ cornerChain v 4 := by
  intro t
  have hρ : WithZero.exp (t : ℤ) * (0 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (t : ℤ) := by simp
  refine ⟨UnipotentBox.box v (WithZero.exp (t : ℤ)) 0 (WithZero.exp (t : ℤ)) hρ,
    UnipotentBox.isCompact_box v _ _ _ hρ, fun m hm => UnipotentBox.mem_unipotentSet_of_mem_box v hm, ?_⟩
  rintro m ⟨x, y, z, rfl⟩
  have hdec : (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 0 y 0 * upperUnipotent3 x 0 z := by
    rw [UnipotentBox.unipotent_mul v]
    congr 1 <;> ring
  by_cases hb : Valued.v x ≤ WithZero.exp (t : ℤ) ∧ Valued.v z ≤ WithZero.exp (t : ℤ)
  · exact Or.inl ⟨upperUnipotent3 0 y 0, ⟨⟨0, y, 0, rfl⟩, y, 0, 0, permPoint120_mul_upperUnipotent3_comm v y⟩,
      upperUnipotent3 x 0 z, UnipotentBox.upperUnipotent3_mem_box v hb.1 (by simp) hb.2, hdec⟩
  · obtain ⟨k, hk, hmem⟩ := exists_mul_mem_cornerChain_four v t x z hb
    refine Or.inr ⟨k, hk, ?_⟩
    have h : permPoint120 v * upperUnipotent3 x y z * k =
        upperUnipotent3 y 0 0 * (permPoint120 v * upperUnipotent3 x 0 z * k) := by
      rw [hdec, ← mul_assoc (permPoint120 v), permPoint120_mul_upperUnipotent3_comm]
      simp only [mul_assoc]
    rw [h]
    exact upperUnipotent3_mul_mem_cornerChain v 4 hmem y 0 0

private theorem exists_mul_antidiagonal3_mul_of_mem_cornerChain_six (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ g ∈ cornerChain v 6, g ∉ cornerChain v 5 →
      ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (m : LocalGL3 v),
        m ∈ UnipotentBox.unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (antidiagonal3 v * m) := by
  intro g _ hg'
  obtain ⟨x', y', z', a, x, y, z, h⟩ := exists_eq_mul_antidiagonal3_mul_upperUnipotent3 v hg'
  exact ⟨x', y', z', a, _, ⟨x, y, z, rfl⟩, h⟩

private theorem exists_box_antidiagonal3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧ ∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v (antidiagonal3 v), ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧
            antidiagonal3 v * m * k ∈ cornerChain v 5 := by
  intro t
  have hρ : WithZero.exp (t : ℤ) * WithZero.exp (t : ℤ) ≤ WithZero.exp (2 * (t : ℤ)) := by
    rw [← WithZero.exp_add, WithZero.exp_le_exp]
    omega
  refine ⟨UnipotentBox.box v (WithZero.exp (t : ℤ)) (WithZero.exp (t : ℤ)) (WithZero.exp (2 * (t : ℤ))) hρ,
    UnipotentBox.isCompact_box v _ _ _ hρ, fun m hm => UnipotentBox.mem_unipotentSet_of_mem_box v hm, ?_⟩
  rintro m ⟨x, y, z, rfl⟩
  by_cases hb : Valued.v x ≤ WithZero.exp (t : ℤ) ∧ Valued.v y ≤ WithZero.exp (t : ℤ) ∧
      Valued.v z ≤ WithZero.exp (2 * (t : ℤ))
  · exact Or.inl ⟨1, one_mem_absorbedBy v _, upperUnipotent3 x y z,
      UnipotentBox.upperUnipotent3_mem_box v hb.1 hb.2.1 hb.2.2, (one_mul _).symm⟩
  · obtain ⟨k, hk, hmem⟩ := exists_antidiagonal3_mul_mul_mem_cornerChain_five v t x y z hb
    exact Or.inr ⟨k, hk, hmem⟩

section TwistedCells

variable (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem exists_commutator_eq {d m : LocalGL3 v} (hd : d ∈ UnipotentBox.unipotentSet v)
    (hm : m ∈ UnipotentBox.unipotentSet v) : ∃ u : v.adicCompletion ℚ, d⁻¹ * m * d * m⁻¹ = upperUnipotent3 0 0 u := by
  obtain ⟨a, b, c, rfl⟩ := hd
  obtain ⟨x, y, z, rfl⟩ := hm
  refine ⟨x * b - a * y, ?_⟩
  rw [UnipotentBox.unipotent_inv v, UnipotentBox.unipotent_inv v, UnipotentBox.unipotent_mul v,
    UnipotentBox.unipotent_mul v, UnipotentBox.unipotent_mul v]
  congr 1 <;> ring

private theorem exists_conj_of_central (ψ : AddChar (v.adicCompletion ℚ) ℂ) {p : LocalGL3 v}
    (hcentral : ∀ u : v.adicCompletion ℚ, (upperUnipotent3 0 0 u : LocalGL3 v) ∈ UnipotentBox.absorbedBy v p)
    (M : Subgroup (LocalGL3 v)) (hMN : ∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) {d : LocalGL3 v}
    (hd : d ∈ UnipotentBox.unipotentSet v) : ∀ m₂ ∈ M, ∃ a ∈ UnipotentBox.absorbedBy v p, ∃ m₂' ∈ M,
      d⁻¹ * m₂ * d = a * m₂' ∧ UnipotentBox.psiN v ψ m₂' = UnipotentBox.psiN v ψ m₂ := by
  intro m₂ hm₂
  obtain ⟨u, hu⟩ := exists_commutator_eq v hd (hMN m₂ hm₂)
  refine ⟨d⁻¹ * m₂ * d * m₂⁻¹, ?_, m₂, hm₂, (inv_mul_cancel_right _ _).symm, rfl⟩
  rw [hu]
  exact hcentral u

private theorem exists_box_conj_of_central (ψ : AddChar (v.adicCompletion ℚ) ℂ) {p : LocalGL3 v}
    {Zi : Set (LocalGL3 v)}
    (hcentral : ∀ u : v.adicCompletion ℚ, (upperUnipotent3 0 0 u : LocalGL3 v) ∈ UnipotentBox.absorbedBy v p)
    (hbox : ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧ ∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi)
    {c : LocalGL3 v} (hc : c ∈ UnipotentBox.unipotentSet v) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧
      (∀ m ∈ UnipotentBox.unipotentSet v, (∃ m₁ ∈ UnipotentBox.absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
        ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi) ∧
      ∀ d : LocalGL3 v, (d = c ∨ d = c⁻¹) → ∀ m₂ ∈ M, ∃ a ∈ UnipotentBox.absorbedBy v p, ∃ m₂' ∈ M,
        d⁻¹ * m₂ * d = a * m₂' ∧ UnipotentBox.psiN v ψ m₂' = UnipotentBox.psiN v ψ m₂ := by
  intro t
  obtain ⟨M, hMc, hMN, hM⟩ := hbox t
  refine ⟨M, hMc, hMN, hM, ?_⟩
  rintro d (rfl | rfl)
  · exact exists_conj_of_central v ψ hcentral M hMN hc
  · exact exists_conj_of_central v ψ hcentral M hMN (UnipotentBox.inv_mem_unipotentSet v hc)

private theorem exists_apply_ne_one {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ : ψ ≠ 1) :
    ∃ x₀ : v.adicCompletion ℚ, ψ x₀ ≠ 1 := by
  by_contra h
  refine hψ ?_
  ext x
  rw [AddChar.one_apply]
  by_contra hx
  exact h ⟨x, hx⟩

private theorem psiN_upperUnipotent3_left (ψ : AddChar (v.adicCompletion ℚ) ℂ) {x₀ : v.adicCompletion ℚ}
    (hx₀ : ψ x₀ ≠ 1) : UnipotentBox.psiN v ψ (upperUnipotent3 x₀ 0 0) ≠ 1 := by
  rwa [UnipotentBox.psiN_upperUnipotent3, add_zero]

private theorem psiN_upperUnipotent3_middle (ψ : AddChar (v.adicCompletion ℚ) ℂ) {x₀ : v.adicCompletion ℚ}
    (hx₀ : ψ x₀ ≠ 1) : UnipotentBox.psiN v ψ (upperUnipotent3 0 x₀ 0) ≠ 1 := by
  rwa [UnipotentBox.psiN_upperUnipotent3, zero_add]

private theorem central_mem_absorbedBy_one (u : v.adicCompletion ℚ) :
    (upperUnipotent3 0 0 u : LocalGL3 v) ∈ UnipotentBox.absorbedBy v (1 : LocalGL3 v) :=
  ⟨⟨0, 0, u, rfl⟩, 0, 0, u, by rw [one_mul, mul_one]⟩

private theorem central_mem_absorbedBy_permPoint102 (u : v.adicCompletion ℚ) :
    (upperUnipotent3 0 0 u : LocalGL3 v) ∈ UnipotentBox.absorbedBy v (permPoint102 v) :=
  ⟨⟨0, 0, u, rfl⟩, 0, u, 0, permPoint102_mul_upperUnipotent3_comm v 0 u⟩

private theorem central_mem_absorbedBy_permPoint021 (u : v.adicCompletion ℚ) :
    (upperUnipotent3 0 0 u : LocalGL3 v) ∈ UnipotentBox.absorbedBy v (permPoint021 v) :=
  ⟨⟨0, 0, u, rfl⟩, u, 0, 0, permPoint021_mul_upperUnipotent3_comm v 0 u⟩

private theorem witness_mem_absorbedBy_one (x₀ : v.adicCompletion ℚ) :
    (upperUnipotent3 x₀ 0 0 : LocalGL3 v) ∈ UnipotentBox.absorbedBy v (1 : LocalGL3 v) :=
  ⟨⟨x₀, 0, 0, rfl⟩, x₀, 0, 0, by rw [one_mul, mul_one]⟩

private theorem witness_mem_absorbedBy_permPoint102 (x₀ : v.adicCompletion ℚ) :
    (upperUnipotent3 0 x₀ 0 : LocalGL3 v) ∈ UnipotentBox.absorbedBy v (permPoint102 v) :=
  ⟨⟨0, x₀, 0, rfl⟩, 0, 0, x₀, permPoint102_mul_upperUnipotent3_comm v x₀ 0⟩

private theorem witness_mem_absorbedBy_permPoint021 (x₀ : v.adicCompletion ℚ) :
    (upperUnipotent3 x₀ 0 0 : LocalGL3 v) ∈ UnipotentBox.absorbedBy v (permPoint021 v) :=
  ⟨⟨x₀, 0, 0, rfl⟩, 0, 0, x₀, permPoint021_mul_upperUnipotent3_comm v x₀ 0⟩

private theorem witness_mem_absorbedBy_permPoint201 (x₀ : v.adicCompletion ℚ) :
    (upperUnipotent3 x₀ 0 0 : LocalGL3 v) ∈ UnipotentBox.absorbedBy v (permPoint201 v) :=
  ⟨⟨x₀, 0, 0, rfl⟩, 0, x₀, 0, permPoint201_mul_upperUnipotent3_comm v x₀⟩

private theorem witness_mem_absorbedBy_permPoint120 (x₀ : v.adicCompletion ℚ) :
    (upperUnipotent3 0 x₀ 0 : LocalGL3 v) ∈ UnipotentBox.absorbedBy v (permPoint120 v) :=
  ⟨⟨0, x₀, 0, rfl⟩, x₀, 0, 0, permPoint120_mul_upperUnipotent3_comm v x₀⟩

private noncomputable def bigBox201 (R : WithZero (Multiplicative ℤ)) (t : ℕ) : Subgroup (LocalGL3 v) :=
  UnipotentBox.box v 0 (WithZero.exp (t : ℤ)) (WithZero.exp (2 * (t : ℤ)) ⊔ R * WithZero.exp (t : ℤ)) (by simp)

private noncomputable def bigBox120 (R : WithZero (Multiplicative ℤ)) (t : ℕ) : Subgroup (LocalGL3 v) :=
  UnipotentBox.box v (WithZero.exp (t : ℤ)) 0 (WithZero.exp (t : ℤ) ⊔ WithZero.exp (t : ℤ) * R) (by simp)

private theorem split_bigBox201 (R : WithZero (Multiplicative ℤ)) (t : ℕ) :
    ∀ m ∈ UnipotentBox.unipotentSet v,
      (∃ m₁ ∈ UnipotentBox.absorbedBy v (permPoint201 v), ∃ m₂ ∈ bigBox201 v R t, m = m₁ * m₂) ∨
        ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧ permPoint201 v * m * k ∈ cornerChain v 3 := by
  rintro m ⟨x, y, z, rfl⟩
  have hdec : (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 x 0 0 * upperUnipotent3 0 y (z - x * y) := by
    rw [UnipotentBox.unipotent_mul v]
    congr 1 <;> ring
  by_cases hb : Valued.v y ≤ WithZero.exp (t : ℤ) ∧ Valued.v (z - x * y) ≤ WithZero.exp (2 * (t : ℤ))
  · exact Or.inl ⟨upperUnipotent3 x 0 0, witness_mem_absorbedBy_permPoint201 v x, upperUnipotent3 0 y (z - x * y),
      UnipotentBox.upperUnipotent3_mem_box v (by simp) hb.1 (hb.2.trans le_sup_left), hdec⟩
  · obtain ⟨k, hk, hmem⟩ := exists_mul_mem_cornerChain_three v t y (z - x * y) hb
    refine Or.inr ⟨k, hk, ?_⟩
    have h : permPoint201 v * upperUnipotent3 x y z * k =
        upperUnipotent3 0 x 0 * (permPoint201 v * upperUnipotent3 0 y (z - x * y) * k) := by
      rw [hdec, ← mul_assoc (permPoint201 v), permPoint201_mul_upperUnipotent3_comm]
      simp only [mul_assoc]
    rw [h]
    exact upperUnipotent3_mul_mem_cornerChain v 3 hmem 0 x 0

private theorem split_bigBox120 (R : WithZero (Multiplicative ℤ)) (t : ℕ) :
    ∀ m ∈ UnipotentBox.unipotentSet v,
      (∃ m₁ ∈ UnipotentBox.absorbedBy v (permPoint120 v), ∃ m₂ ∈ bigBox120 v R t, m = m₁ * m₂) ∨
        ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧ permPoint120 v * m * k ∈ cornerChain v 4 := by
  rintro m ⟨x, y, z, rfl⟩
  have hdec : (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 0 y 0 * upperUnipotent3 x 0 z := by
    rw [UnipotentBox.unipotent_mul v]
    congr 1 <;> ring
  by_cases hb : Valued.v x ≤ WithZero.exp (t : ℤ) ∧ Valued.v z ≤ WithZero.exp (t : ℤ)
  · exact Or.inl ⟨upperUnipotent3 0 y 0, witness_mem_absorbedBy_permPoint120 v y, upperUnipotent3 x 0 z,
      UnipotentBox.upperUnipotent3_mem_box v hb.1 (by simp) (hb.2.trans le_sup_left), hdec⟩
  · obtain ⟨k, hk, hmem⟩ := exists_mul_mem_cornerChain_four v t x z hb
    refine Or.inr ⟨k, hk, ?_⟩
    have h : permPoint120 v * upperUnipotent3 x y z * k =
        upperUnipotent3 y 0 0 * (permPoint120 v * upperUnipotent3 x 0 z * k) := by
      rw [hdec, ← mul_assoc (permPoint120 v), permPoint120_mul_upperUnipotent3_comm]
      simp only [mul_assoc]
    rw [h]
    exact upperUnipotent3_mul_mem_cornerChain v 4 hmem y 0 0

private theorem conj_bigBox201 (ψ : AddChar (v.adicCompletion ℚ) ℂ) {R : WithZero (Multiplicative ℤ)} (t : ℕ)
    {w : v.adicCompletion ℚ} (hw : Valued.v w ≤ R) : ∀ m₂ ∈ bigBox201 v R t,
      ∃ a ∈ UnipotentBox.absorbedBy v (permPoint201 v), ∃ m₂' ∈ bigBox201 v R t,
        (upperUnipotent3 w 0 0 : LocalGL3 v)⁻¹ * m₂ * upperUnipotent3 w 0 0 = a * m₂' ∧
          UnipotentBox.psiN v ψ m₂' = UnipotentBox.psiN v ψ m₂ := by
  rintro m₂ ⟨x, y, z, hx, hy, hz, rfl⟩
  have e : (upperUnipotent3 w 0 0 : LocalGL3 v)⁻¹ * upperUnipotent3 x y z * upperUnipotent3 w 0 0
      = upperUnipotent3 x y (z - w * y) := by
    rw [UnipotentBox.unipotent_inv v, UnipotentBox.unipotent_mul v, UnipotentBox.unipotent_mul v]
    congr 1 <;> ring
  refine ⟨1, one_mem_absorbedBy v _, upperUnipotent3 x y (z - w * y), ?_, by rw [e, one_mul], ?_⟩
  · refine UnipotentBox.upperUnipotent3_mem_box v hx hy ((Valuation.map_sub _ _ _).trans (max_le hz ?_))
    rw [Valuation.map_mul]
    exact (mul_le_mul' hw hy).trans le_sup_right
  · rw [UnipotentBox.psiN_upperUnipotent3, UnipotentBox.psiN_upperUnipotent3]

private theorem conj_bigBox120 (ψ : AddChar (v.adicCompletion ℚ) ℂ) {R : WithZero (Multiplicative ℤ)} (t : ℕ)
    {w : v.adicCompletion ℚ} (hw : Valued.v w ≤ R) : ∀ m₂ ∈ bigBox120 v R t,
      ∃ a ∈ UnipotentBox.absorbedBy v (permPoint120 v), ∃ m₂' ∈ bigBox120 v R t,
        (upperUnipotent3 0 w 0 : LocalGL3 v)⁻¹ * m₂ * upperUnipotent3 0 w 0 = a * m₂' ∧
          UnipotentBox.psiN v ψ m₂' = UnipotentBox.psiN v ψ m₂ := by
  rintro m₂ ⟨x, y, z, hx, hy, hz, rfl⟩
  have e : (upperUnipotent3 0 w 0 : LocalGL3 v)⁻¹ * upperUnipotent3 x y z * upperUnipotent3 0 w 0
      = upperUnipotent3 x y (z + x * w) := by
    rw [UnipotentBox.unipotent_inv v, UnipotentBox.unipotent_mul v, UnipotentBox.unipotent_mul v]
    congr 1 <;> ring
  refine ⟨1, one_mem_absorbedBy v _, upperUnipotent3 x y (z + x * w), ?_, by rw [e, one_mul], ?_⟩
  · refine UnipotentBox.upperUnipotent3_mem_box v hx hy ((Valuation.map_add _ _ _).trans (max_le hz ?_))
    rw [Valuation.map_mul]
    exact (mul_le_mul' hx hw).trans le_sup_right
  · rw [UnipotentBox.psiN_upperUnipotent3, UnipotentBox.psiN_upperUnipotent3]

private theorem inv_upperUnipotent3_left (x₀ : v.adicCompletion ℚ) :
    (upperUnipotent3 x₀ 0 0 : LocalGL3 v)⁻¹ = upperUnipotent3 (-x₀) 0 0 := by
  rw [UnipotentBox.unipotent_inv v]
  congr 1 <;> ring

private theorem inv_upperUnipotent3_middle (x₀ : v.adicCompletion ℚ) :
    (upperUnipotent3 0 x₀ 0 : LocalGL3 v)⁻¹ = upperUnipotent3 0 (-x₀) 0 := by
  rw [UnipotentBox.unipotent_inv v]
  congr 1 <;> ring

private theorem exists_box_conj_permPoint201 (ψ : AddChar (v.adicCompletion ℚ) ℂ) (x₀ : v.adicCompletion ℚ) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧
      (∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v (permPoint201 v), ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧ permPoint201 v * m * k ∈ cornerChain v 3) ∧
      ∀ d : LocalGL3 v, (d = upperUnipotent3 x₀ 0 0 ∨ d = (upperUnipotent3 x₀ 0 0 : LocalGL3 v)⁻¹) →
        ∀ m₂ ∈ M, ∃ a ∈ UnipotentBox.absorbedBy v (permPoint201 v), ∃ m₂' ∈ M,
          d⁻¹ * m₂ * d = a * m₂' ∧ UnipotentBox.psiN v ψ m₂' = UnipotentBox.psiN v ψ m₂ := by
  intro t
  refine ⟨bigBox201 v (Valued.v x₀) t, UnipotentBox.isCompact_box v _ _ _ _,
    fun m hm => UnipotentBox.mem_unipotentSet_of_mem_box v hm, split_bigBox201 v _ t, ?_⟩
  rintro d (rfl | rfl)
  · exact conj_bigBox201 v ψ t le_rfl
  · rw [inv_upperUnipotent3_left]
    exact conj_bigBox201 v ψ t (Valuation.map_neg _ _).le

private theorem exists_box_conj_permPoint120 (ψ : AddChar (v.adicCompletion ℚ) ℂ) (x₀ : v.adicCompletion ℚ) :
    ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ UnipotentBox.unipotentSet v) ∧
      (∀ m ∈ UnipotentBox.unipotentSet v,
        (∃ m₁ ∈ UnipotentBox.absorbedBy v (permPoint120 v), ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, UnipotentBox.IsPrincipalCongruence v t k ∧ permPoint120 v * m * k ∈ cornerChain v 4) ∧
      ∀ d : LocalGL3 v, (d = upperUnipotent3 0 x₀ 0 ∨ d = (upperUnipotent3 0 x₀ 0 : LocalGL3 v)⁻¹) →
        ∀ m₂ ∈ M, ∃ a ∈ UnipotentBox.absorbedBy v (permPoint120 v), ∃ m₂' ∈ M,
          d⁻¹ * m₂ * d = a * m₂' ∧ UnipotentBox.psiN v ψ m₂' = UnipotentBox.psiN v ψ m₂ := by
  intro t
  refine ⟨bigBox120 v (Valued.v x₀) t, UnipotentBox.isCompact_box v _ _ _ _,
    fun m hm => UnipotentBox.mem_unipotentSet_of_mem_box v hm, split_bigBox120 v _ t, ?_⟩
  rintro d (rfl | rfl)
  · exact conj_bigBox120 v ψ t le_rfl
  · rw [inv_upperUnipotent3_middle]
    exact conj_bigBox120 v ψ t (Valuation.map_neg _ _).le

private theorem twisted_vanish_zero_one (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    (hlevel : UnipotentBox.UniformlySmooth v χ) {x₀ : v.adicCompletion ℚ} (hx₀ : ψ x₀ ≠ 1)
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (hkill : ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ cornerChain v 1, (F : LocalGL3 v → ℂ) g = 0) → Λ F = 0)
    (F : ↥(principalSeries3 v χ)) (hFZ : ∀ g ∈ cornerChain v 0, (F : LocalGL3 v → ℂ) g = 0) : Λ F = 0 :=
  UnipotentBox.apply_eq_zero_of_cell_twisted v χ ψ hψA (Zi := cornerChain v 0) (Zi1 := cornerChain v 1) (p := 1)
    (c := upperUnipotent3 x₀ 0 0) (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 0 hg x y z)
    (exists_mul_one_mul_of_mem_cornerChain_one v) (witness_mem_absorbedBy_one v x₀)
    (psiN_upperUnipotent3_left v ψ hx₀)
    (exists_box_conj_of_central v ψ (central_mem_absorbedBy_one v) (exists_box_one v) ⟨x₀, 0, 0, rfl⟩) hlevel hΛ
    hkill F hFZ

private theorem twisted_vanish_one_two (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    (hlevel : UnipotentBox.UniformlySmooth v χ) {x₀ : v.adicCompletion ℚ} (hx₀ : ψ x₀ ≠ 1)
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (hkill : ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ cornerChain v 2, (F : LocalGL3 v → ℂ) g = 0) → Λ F = 0)
    (F : ↥(principalSeries3 v χ)) (hFZ : ∀ g ∈ cornerChain v 1, (F : LocalGL3 v → ℂ) g = 0) : Λ F = 0 :=
  UnipotentBox.apply_eq_zero_of_cell_twisted v χ ψ hψA (Zi := cornerChain v 1) (Zi1 := cornerChain v 2)
    (p := permPoint102 v) (c := upperUnipotent3 0 x₀ 0)
    (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 1 hg x y z)
    (exists_mul_permPoint102_mul_of_mem_cornerChain_two v) (witness_mem_absorbedBy_permPoint102 v x₀)
    (psiN_upperUnipotent3_middle v ψ hx₀)
    (exists_box_conj_of_central v ψ (central_mem_absorbedBy_permPoint102 v) (exists_box_permPoint102 v)
      ⟨0, x₀, 0, rfl⟩) hlevel hΛ hkill F hFZ

private theorem twisted_vanish_two_three (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    (hlevel : UnipotentBox.UniformlySmooth v χ) {x₀ : v.adicCompletion ℚ} (hx₀ : ψ x₀ ≠ 1)
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (hkill : ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ cornerChain v 3, (F : LocalGL3 v → ℂ) g = 0) → Λ F = 0)
    (F : ↥(principalSeries3 v χ)) (hFZ : ∀ g ∈ cornerChain v 2, (F : LocalGL3 v → ℂ) g = 0) : Λ F = 0 :=
  UnipotentBox.apply_eq_zero_of_cell_twisted v χ ψ hψA (Zi := cornerChain v 2) (Zi1 := cornerChain v 3)
    (p := permPoint021 v) (c := upperUnipotent3 x₀ 0 0)
    (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 2 hg x y z)
    (exists_mul_permPoint021_mul_of_mem_cornerChain_three v) (witness_mem_absorbedBy_permPoint021 v x₀)
    (psiN_upperUnipotent3_left v ψ hx₀)
    (exists_box_conj_of_central v ψ (central_mem_absorbedBy_permPoint021 v) (exists_box_permPoint021 v)
      ⟨x₀, 0, 0, rfl⟩) hlevel hΛ hkill F hFZ

private theorem twisted_vanish_three_four (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    (hlevel : UnipotentBox.UniformlySmooth v χ) {x₀ : v.adicCompletion ℚ} (hx₀ : ψ x₀ ≠ 1)
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (hkill : ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ cornerChain v 4, (F : LocalGL3 v → ℂ) g = 0) → Λ F = 0)
    (F : ↥(principalSeries3 v χ)) (hFZ : ∀ g ∈ cornerChain v 3, (F : LocalGL3 v → ℂ) g = 0) : Λ F = 0 :=
  UnipotentBox.apply_eq_zero_of_cell_twisted v χ ψ hψA (Zi := cornerChain v 3) (Zi1 := cornerChain v 4)
    (p := permPoint201 v) (c := upperUnipotent3 x₀ 0 0)
    (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 3 hg x y z)
    (exists_mul_permPoint201_mul_of_mem_cornerChain_four v) (witness_mem_absorbedBy_permPoint201 v x₀)
    (psiN_upperUnipotent3_left v ψ hx₀) (exists_box_conj_permPoint201 v ψ x₀) hlevel hΛ hkill F hFZ

private theorem twisted_vanish_four_five (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    (hlevel : UnipotentBox.UniformlySmooth v χ) {x₀ : v.adicCompletion ℚ} (hx₀ : ψ x₀ ≠ 1)
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (hkill : ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ cornerChain v 5, (F : LocalGL3 v → ℂ) g = 0) → Λ F = 0)
    (F : ↥(principalSeries3 v χ)) (hFZ : ∀ g ∈ cornerChain v 4, (F : LocalGL3 v → ℂ) g = 0) : Λ F = 0 :=
  UnipotentBox.apply_eq_zero_of_cell_twisted v χ ψ hψA (Zi := cornerChain v 4) (Zi1 := cornerChain v 5)
    (p := permPoint120 v) (c := upperUnipotent3 0 x₀ 0)
    (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 4 hg x y z)
    (exists_mul_permPoint120_mul_of_mem_cornerChain_five v) (witness_mem_absorbedBy_permPoint120 v x₀)
    (psiN_upperUnipotent3_middle v ψ hx₀) (exists_box_conj_permPoint120 v ψ x₀) hlevel hΛ hkill F hFZ

private theorem apply_eq_zero_of_not_exists_level (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hA : ¬ ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1)
    (hlevel : UnipotentBox.UniformlySmooth v χ) {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ}
    (hΛ : IsWhittakerFunctional3 ψ Λ) (F : ↥(principalSeries3 v χ)) : Λ F = 0 := by
  obtain ⟨t, ht⟩ := hlevel F F.2
  have hx : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t : ℤ)) ∧ ψ x ≠ 1 := by
    by_contra h
    exact hA ⟨t, fun x hxv => by_contra fun hne => h ⟨x, hxv, hne⟩⟩
  obtain ⟨x, hxv, hxψ⟩ := hx
  have hk : UnipotentBox.IsPrincipalCongruence v t (upperUnipotent3 x 0 0) :=
    UnipotentBox.isPrincipalCongruence_of_mem_smallBox v
      (UnipotentBox.upperUnipotent3_mem_box v hxv (by simp) (by simp))
  have h1 := hΛ x 0 0 F
  have h2 : (⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x 0 0) F,
      rightTranslate_mem_principalSeries3 F.2 (upperUnipotent3 x 0 0)⟩ : ↥(principalSeries3 v χ)) = F :=
    Subtype.ext (ht _ hk)
  rw [h2, add_zero] at h1
  have h3 : (ψ x - 1) * Λ F = 0 := by linear_combination (-1 : ℂ) * h1
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) hxψ
  · exact h

end TwistedCells
end

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul cornerEntry_upperUnipotent3_mul lowerMinor_upperUnipotent3_mul cornerEntry_diagonal3_mul lowerMinor_diagonal3_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 continuous_gl3Entry gl3Det_eq_bottom_expansion gl3AmbientRightTranslate upperUnipotent3 upperUnipotent3_zero LocalGL3 isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem finrank_inf_dualAnnihilator_le_of_le (S : Submodule K (V →ₗ[K] K)) [FiniteDimensional K S]
    {W W' : Submodule K V} (hW : W' ≤ W) {d : ℕ}
    (hd : ∀ (n : ℕ) (Λ : Fin n → (V →ₗ[K] K)), (∀ j, Λ j ∈ S) → (∀ j, ∀ x ∈ W', Λ j x = 0) →
      LinearIndependent K (fun j => (Λ j).domRestrict W) → n ≤ d) :
    finrank K ↥(S ⊓ W'.dualAnnihilator) ≤ finrank K ↥(S ⊓ W.dualAnnihilator) + d := by

  letI : AddCommGroup (V →ₗ[K] K) := inferInstance
  letI : AddCommGroup ↥(S ⊓ W'.dualAnnihilator) := inferInstance
  have _ := hW

  let N : Submodule K ↥(S ⊓ W'.dualAnnihilator) := W.dualAnnihilator.comap (S ⊓ W'.dualAnnihilator).subtype
  have hq := Submodule.finrank_quotient_add_finrank N
  have hN : finrank K ↥N ≤ finrank K ↥(S ⊓ W.dualAnnihilator) := by
    rw [← Submodule.finrank_map_subtype_eq (S ⊓ W'.dualAnnihilator) N]
    refine Submodule.finrank_mono fun Λ hΛ => ?_
    obtain ⟨Λ', hΛ', rfl⟩ := Submodule.mem_map.1 hΛ
    exact Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 Λ'.2).1, Submodule.mem_comap.1 hΛ'⟩

  have hQ : finrank K (↥(S ⊓ W'.dualAnnihilator) ⧸ N) ≤ d := by
    haveI : Module.Free K (↥(S ⊓ W'.dualAnnihilator) ⧸ N) := Module.Free.of_divisionRing K _
    let b := Module.finBasis K (↥(S ⊓ W'.dualAnnihilator) ⧸ N)
    choose p hp using fun j => Submodule.mkQ_surjective N (b j)
    refine hd _ (fun j => ((p j : ↥(S ⊓ W'.dualAnnihilator)) : V →ₗ[K] K))
      (fun j => (Submodule.mem_inf.1 (p j).2).1)
      (fun j x hx => (Submodule.mem_dualAnnihilator _).1 (Submodule.mem_inf.1 (p j).2).2 x hx) ?_
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hmem : (∑ k, c k • p k) ∈ N := by
      refine Submodule.mem_comap.2 ((Submodule.mem_dualAnnihilator _).2 fun w hw => ?_)
      have h0 := LinearMap.congr_fun hc ⟨w, hw⟩
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.domRestrict_apply, LinearMap.zero_apply] at h0
      simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.subtype_apply] using h0
    have hzero : (∑ k, c k • b k) = 0 := by
      have h1 : N.mkQ (∑ k, c k • p k) = 0 := (Submodule.Quotient.mk_eq_zero N).2 hmem
      simpa only [map_sum, map_smul, hp] using h1
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c hzero j
  omega

private theorem card_le_sum_of_linearIndependent_of_chain (G : Submodule K (V →ₗ[K] K)) (r : ℕ)
    (W : ℕ → Submodule K V) (h0 : W 0 = ⊤) (hr : W r = ⊥) (hanti : ∀ i < r, W (i + 1) ≤ W i) (d : ℕ → ℕ)
    (hd : ∀ i < r, ∀ (n : ℕ) (Λ : Fin n → (V →ₗ[K] K)), (∀ j, Λ j ∈ G) → (∀ j, ∀ x ∈ W (i + 1), Λ j x = 0) →
      LinearIndependent K (fun j => (Λ j).domRestrict (W i)) → n ≤ d i)
    (s : Finset (V →ₗ[K] K)) (hs : ∀ Λ ∈ s, Λ ∈ G)
    (hind : LinearIndependent K (fun Λ : ↥s => (Λ : V →ₗ[K] K))) :
    s.card ≤ ∑ i ∈ Finset.range r, d i := by
  classical
  set S : Submodule K (V →ₗ[K] K) := Submodule.span K (s : Set (V →ₗ[K] K)) with hS
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K s.finite_toSet
  have hSG : S ≤ G := Submodule.span_le.2 fun Λ hΛ => hs Λ hΛ
  have hcard : finrank K S = s.card := by
    have h := finrank_span_eq_card (R := K) hind
    rw [Subtype.range_coe_subtype, Finset.setOf_mem] at h
    rw [hS, h, Fintype.card_coe]
  have hstep : ∀ i, i ≤ r → finrank K ↥(S ⊓ (W i).dualAnnihilator) ≤ ∑ j ∈ Finset.range i, d j := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [h0, Submodule.dualAnnihilator_top]
    | succ i ih =>
      intro hi
      have hi' : i < r := hi
      refine (finrank_inf_dualAnnihilator_le_of_le S (hanti i hi') (d := d i) ?_).trans ?_
      · intro n Λ hΛS hΛW hli
        exact hd i hi' n Λ (fun j => hSG (hΛS j)) hΛW hli
      · rw [Finset.sum_range_succ]
        exact Nat.add_le_add_right (ih hi'.le) _
  have hr' := hstep r le_rfl
  rwa [hr, Submodule.dualAnnihilator_bot, inf_top_eq, hcard] at hr'

end LanglandsTunnell.CubicInduction

section

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul cornerEntry_upperUnipotent3_mul lowerMinor_upperUnipotent3_mul cornerEntry_diagonal3_mul lowerMinor_diagonal3_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 continuous_gl3Entry gl3Det_eq_bottom_expansion gl3AmbientRightTranslate upperUnipotent3 upperUnipotent3_zero LocalGL3 isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
namespace T0cAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem apply_eq_zero_of_isWhittakerFunctional3_of_ne_five (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (i : Fin 6) (hi : i ≠ 5) (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (hΛ : IsWhittakerFunctional3 ψ Λ)
    (hkill : ∀ F : ↥(principalSeries3 v χ),
      (∀ g ∈ cornerChain v i.succ, (F : LocalGL3 v → ℂ) g = 0) → Λ F = 0) :
    ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ cornerChain v i.castSucc, (F : LocalGL3 v → ℂ) g = 0) → Λ F = 0 := by
  intro F hFZ
  have hlevel : UnipotentBox.UniformlySmooth v χ := fun f hf =>
    exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f hf
  by_cases hA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1
  · obtain ⟨x₀, hx₀⟩ := exists_apply_ne_one v hψ
    fin_cases i
    · exact twisted_vanish_zero_one v χ ψ hA hlevel hx₀ hΛ hkill F hFZ
    · exact twisted_vanish_one_two v χ ψ hA hlevel hx₀ hΛ hkill F hFZ
    · exact twisted_vanish_two_three v χ ψ hA hlevel hx₀ hΛ hkill F hFZ
    · exact twisted_vanish_three_four v χ ψ hA hlevel hx₀ hΛ hkill F hFZ
    · exact twisted_vanish_four_five v χ ψ hA hlevel hx₀ hΛ hkill F hFZ
    · exact absurd rfl hi
  · exact apply_eq_zero_of_not_exists_level v χ ψ hA hlevel hΛ F

private theorem le_one_of_isWhittakerFunctional3_of_linearIndependent_domRestrict (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (W₅ : Submodule ℂ ↥(principalSeries3 v χ))
    (hW₅ : ∀ F : ↥(principalSeries3 v χ), F ∈ W₅ ↔ ∀ g ∈ cornerChain v 5, (F : LocalGL3 v → ℂ) g = 0)
    (n : ℕ) (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) (hΛ : ∀ j, IsWhittakerFunctional3 ψ (Λ j))
    (hli : LinearIndependent ℂ fun j => (Λ j).domRestrict W₅) : n ≤ 1 := by
  have hlevel : UnipotentBox.UniformlySmooth v χ := fun f hf =>
    exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f hf
  by_cases hA : ∃ t₀ : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(t₀ : ℤ)) → ψ x = 1
  · refine UnipotentBox.le_one_of_cell_twisted v χ ψ hA (Zi := cornerChain v 5) (Zi1 := cornerChain v 6)
      (p := antidiagonal3 v) (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 5 hg x y z)
      (exists_mul_antidiagonal3_mul_of_mem_cornerChain_six v) (exists_box_antidiagonal3 v) hlevel W₅ hW₅ Λ hΛ
      (fun j F hF => ?_) hli
    have hF0 : F = 0 := Subtype.ext (funext fun g => hF g ((mem_cornerChain_six v g).mpr trivial))
    rw [hF0, map_zero]
  · rcases Nat.lt_or_ge 1 n with h | h
    · exfalso
      have h0 : (Λ ⟨0, by omega⟩).domRestrict W₅ = 0 :=
        LinearMap.ext fun F => apply_eq_zero_of_not_exists_level v χ ψ hA hlevel (hΛ ⟨0, by omega⟩) F
      exact hli.ne_zero ⟨0, by omega⟩ h0
    · exact h

private theorem card_le_one_of_isWhittakerFunctional3_of_linearIndependent (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ : ψ ≠ 1) (s : Finset (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) (hs : ∀ Λ ∈ s, IsWhittakerFunctional3 ψ Λ)
    (hind : LinearIndependent ℂ fun Λ : ↥s => (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) : s.card ≤ 1 := by
  classical

  let W : Fin 7 → Submodule ℂ ↥(principalSeries3 v χ) := fun k =>
    Submodule.comap (principalSeries3 v χ).subtype
      (⨅ g ∈ cornerChain v k, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ))
  have hWk : ∀ k : Fin 7, W k = Submodule.comap (principalSeries3 v χ).subtype
      (⨅ g ∈ cornerChain v k, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)) := fun k => rfl
  have hWmem : ∀ (k : Fin 7) (F : ↥(principalSeries3 v χ)),
      F ∈ W k ↔ ∀ g ∈ cornerChain v k, (F : LocalGL3 v → ℂ) g = 0 :=
    fun k F => mem_comap_iInf_ker_proj_iff v χ (cornerChain v k) F
  have hZ01 : cornerChain v 0 ⊆ cornerChain v 1 := fun g hg => ((mem_cornerChain_zero v g).mp hg).elim
  have hZ12 : cornerChain v 1 ⊆ cornerChain v 2 := fun g hg =>
    (mem_cornerChain_two v g).mpr ⟨((mem_cornerChain_one v g).mp hg).1, ((mem_cornerChain_one v g).mp hg).2.2⟩
  have hZ23 : cornerChain v 2 ⊆ cornerChain v 3 := fun g hg =>
    (mem_cornerChain_three v g).mpr
      ⟨((mem_cornerChain_two v g).mp hg).1, by rw [((mem_cornerChain_two v g).mp hg).2, mul_zero]⟩
  have hZ34 : cornerChain v 3 ⊆ cornerChain v 4 := fun g hg =>
    (mem_cornerChain_four v g).mpr ((mem_cornerChain_three v g).mp hg).1
  have hZ45 : cornerChain v 4 ⊆ cornerChain v 5 := fun g hg =>
    (mem_cornerChain_five v g).mpr (by rw [(mem_cornerChain_four v g).mp hg, zero_mul])
  have hZ56 : cornerChain v 5 ⊆ cornerChain v 6 := fun g _ => (mem_cornerChain_six v g).mpr trivial

  let G : Submodule ℂ (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) :=
    { carrier := {Λ | IsWhittakerFunctional3 ψ Λ}
      add_mem' := by
        intro Λ₁ Λ₂ h₁ h₂ x y z f
        rw [LinearMap.add_apply, LinearMap.add_apply, h₁ x y z f, h₂ x y z f, mul_add]
      zero_mem' := by
        intro x y z f
        simp
      smul_mem' := by
        intro c Λ h x y z f
        rw [LinearMap.smul_apply, LinearMap.smul_apply, h x y z f, smul_eq_mul, smul_eq_mul, mul_left_comm] }
  have hG : ∀ Λ ∈ s, Λ ∈ G := fun Λ hΛ => hs Λ hΛ

  let d : ℕ → ℕ := fun k => if k = 5 then 1 else 0
  let W' : ℕ → Submodule ℂ ↥(principalSeries3 v χ) := fun k => if h : k < 7 then W ⟨k, h⟩ else ⊥
  have h0 : W' 0 = ⊤ := by
    have h00 : W' 0 = W 0 := dif_pos (by omega)
    rw [h00, eq_top_iff]
    intro F _
    rw [hWmem]
    intro g hg
    exact ((mem_cornerChain_zero v g).mp hg).elim
  have hr : W' 6 = ⊥ := by
    have h66 : W' 6 = W 6 := dif_pos (by omega)
    rw [h66, eq_bot_iff]
    intro F hF
    rw [hWmem] at hF
    rw [Submodule.mem_bot]
    exact Subtype.ext (funext fun g => hF g ((mem_cornerChain_six v g).mpr trivial))
  have hanti : ∀ k < 6, W' (k + 1) ≤ W' k := by
    intro k hk
    have h1 : W' (k + 1) = W ⟨k + 1, by omega⟩ := dif_pos (by omega)
    have h2 : W' k = W ⟨k, by omega⟩ := dif_pos (by omega)
    rw [h1, h2, hWk, hWk]
    refine Submodule.comap_mono (biInf_mono ?_)
    interval_cases k
    · exact hZ01
    · exact hZ12
    · exact hZ23
    · exact hZ34
    · exact hZ45
    · exact hZ56
  have hd : ∀ k < 6, ∀ (n : ℕ) (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)), (∀ j, Λ j ∈ G) →
      (∀ j, ∀ x ∈ W' (k + 1), Λ j x = 0) →
      LinearIndependent ℂ (fun j => (Λ j).domRestrict (W' k)) → n ≤ d k := by
    intro k hk n Λ hΛG hkill hli
    have hΛψ : ∀ j, IsWhittakerFunctional3 ψ (Λ j) := fun j => hΛG j
    have e1 : W' (k + 1) = W (⟨k, hk⟩ : Fin 6).succ := dif_pos (by omega)
    have e2 : W' k = W (⟨k, hk⟩ : Fin 6).castSucc := dif_pos (by omega)
    rw [e1] at hkill
    rw [e2] at hli
    by_cases hk5 : k = 5
    · subst hk5
      have hdk : d 5 = 1 := if_pos rfl
      rw [hdk]
      exact le_one_of_isWhittakerFunctional3_of_linearIndependent_domRestrict v χ ψ _ (hWmem _) n Λ hΛψ hli
    · have hdk : d k = 0 := if_neg hk5
      rw [hdk, Nat.le_zero]
      by_contra hn
      have hi : (⟨k, hk⟩ : Fin 6) ≠ 5 := fun h => hk5 (by simpa using congrArg Fin.val h)
      have hvan := apply_eq_zero_of_isWhittakerFunctional3_of_ne_five v χ ψ hψ ⟨k, hk⟩ hi (Λ ⟨0, by omega⟩)
        (hΛψ _) (fun F hF => hkill _ F ((hWmem _ F).mpr hF))
      refine hli.ne_zero ⟨0, by omega⟩ (LinearMap.ext fun F => ?_)
      exact hvan F ((hWmem _ F).mp F.2)
  have hcard := card_le_sum_of_linearIndependent_of_chain G 6 W' h0 hr hanti d hd s hG hind
  have hsum : ∑ k ∈ Finset.range 6, d k = 1 := by
    simp [d]
  omega

private theorem exists_eq_smul_of_isWhittakerFunctional3 (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (Λ₀ Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (hΛ₀ : IsWhittakerFunctional3 ψ Λ₀) (hne : Λ₀ ≠ 0)
    (hΛ : IsWhittakerFunctional3 ψ Λ) : ∃ c : ℂ, Λ = c • Λ₀ := by
  classical
  by_contra hcon
  have hΛ0 : Λ ≠ 0 := fun h => hcon ⟨0, by rw [h, zero_smul]⟩
  have hne' : Λ₀ ≠ Λ := fun h => hcon ⟨1, by rw [h, one_smul]⟩

  have hnotspan : Λ₀ ∉ Submodule.span ℂ ({Λ} : Set (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have ha0 : a ≠ 0 := fun h => hne (by rw [← ha, h, zero_smul])
    exact hcon ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩
  have hnotin : Λ₀ ∉ ({Λ} : Set (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) := by
    rw [Set.mem_singleton_iff]
    exact hne'
  have hsingle : LinearIndepOn ℂ id ({Λ} : Set (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :=
    LinearIndepOn.singleton' fun r hr => (smul_eq_zero.mp hr).resolve_right hΛ0
  have hset₀ : LinearIndepOn ℂ id ({Λ₀, Λ} : Set (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :=
    (linearIndepOn_id_insert hnotin).mpr ⟨hsingle, hnotspan⟩

  have hind₀ : LinearIndepOn ℂ id
      ((({Λ₀, Λ} : Finset (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) : Set (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))) := by
    rw [Finset.coe_pair]
    exact hset₀
  have hind : LinearIndependent ℂ fun Λ' : ↥({Λ₀, Λ} : Finset (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) =>
      (Λ' : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) :=
    hind₀
  have hsW : ∀ Λ' ∈ ({Λ₀, Λ} : Finset (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)), IsWhittakerFunctional3 ψ Λ' := by
    intro Λ' hΛ'
    rw [Finset.mem_insert, Finset.mem_singleton] at hΛ'
    rcases hΛ' with rfl | rfl
    · exact hΛ₀
    · exact hΛ
  have h1 := card_le_one_of_isWhittakerFunctional3_of_linearIndependent v χ ψ hψ {Λ₀, Λ} hsW hind
  rw [Finset.card_pair hne'] at h1
  omega

end LanglandsTunnell.CubicInduction.T0cAux

end

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (Λ₀ Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (hΛ₀ : IsWhittakerFunctional3 ψ Λ₀) (hne : Λ₀ ≠ 0)
    (hΛ : IsWhittakerFunctional3 ψ Λ) : ∃ c : ℂ, Λ = c • Λ₀ :=
  LanglandsTunnell.CubicInduction.T0cAux.exists_eq_smul_of_isWhittakerFunctional3 v χ ψ hψ Λ₀ Λ hΛ₀ hne hΛ

end S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3 (solution)
