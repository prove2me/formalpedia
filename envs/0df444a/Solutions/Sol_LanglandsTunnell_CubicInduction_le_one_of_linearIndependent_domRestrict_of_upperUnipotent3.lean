-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.le_one_of_linearIndependent_domRestrict_of_upperUnipotent3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/cf081cb8-1e0f-55c3-a1b1-c12f4e4fda8c

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_le_one_of_linearIndependent_domRestrict_of_upperUnipotent3

set_option autoImplicit false

section

set_option autoImplicit false

open IsDedekindDomain NumberField
open LanglandsTunnell LanglandsTunnell.CubicInduction

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
open LanglandsTunnell.CubicInduction

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
open LanglandsTunnell.CubicInduction

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

private theorem apply_sumTranslate_eq_card_mul {n : ℕ} (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))
    (hinv : ∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f)
    (s : Finset (LocalGL3 v)) (hs : ∀ r ∈ s, r ∈ unipotentSet v) (F : ↥(principalSeries3 v χ)) (j : Fin n) :
    Λ j (sumTranslate v χ s F) = (s.card : ℂ) * Λ j F := by
  unfold sumTranslate
  rw [map_sum]
  have h : ∀ r ∈ s, Λ j (translateSection v χ r F) = Λ j F := by
    intro r hr
    obtain ⟨x, y, z, rfl⟩ := hs r hr
    exact hinv j x y z F
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

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

private theorem sum_mul_apply_eq_sum_mul_apply {Zi Zi1 : Set (LocalGL3 v)} {p : LocalGL3 v}
    (hN : ∀ g ∈ Zi, ∀ x y z : v.adicCompletion ℚ, g * upperUnipotent3 x y z ∈ Zi)
    (hcover : ∀ g ∈ Zi1, g ∉ Zi → ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
      (m : LocalGL3 v), m ∈ unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (p * m))
    {n : ℕ} (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))
    (hinv : ∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f)
    (hkill : ∀ j, ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ Zi1, (F : LocalGL3 v → ℂ) g = 0) → Λ j F = 0)
    (M : Subgroup (LocalGL3 v)) (hMN : ∀ m ∈ M, m ∈ unipotentSet v)
    (s : Finset (LocalGL3 v)) (hs0 : s.Nonempty) (hsM : ∀ r ∈ s, r ∈ M)
    (f f' : ↥(principalSeries3 v χ))
    (hfZ : ∀ g ∈ Zi, (f : LocalGL3 v → ℂ) g = 0) (hf'Z : ∀ g ∈ Zi, (f' : LocalGL3 v → ℂ) g = 0)
    (hsf : ∀ m ∈ M, ∑ r ∈ s, (f : LocalGL3 v → ℂ) (p * m * r) = ∑ r ∈ s, (f : LocalGL3 v → ℂ) (p * r))
    (hsf' : ∀ m ∈ M, ∑ r ∈ s, (f' : LocalGL3 v → ℂ) (p * m * r) = ∑ r ∈ s, (f' : LocalGL3 v → ℂ) (p * r))
    (hvf : ∀ m ∈ unipotentSet v, (¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) →
      (f : LocalGL3 v → ℂ) (p * m) = 0)
    (hvf' : ∀ m ∈ unipotentSet v, (¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) →
      (f' : LocalGL3 v → ℂ) (p * m) = 0) :
    (∀ j, (∑ r ∈ s, (f' : LocalGL3 v → ℂ) (p * r)) * Λ j f = (∑ r ∈ s, (f : LocalGL3 v → ℂ) (p * r)) * Λ j f') ∧
      ((∑ r ∈ s, (f : LocalGL3 v → ℂ) (p * r)) = 0 → ∀ j, Λ j f = 0) := by
  classical
  have hsN : ∀ r ∈ s, r ∈ unipotentSet v := fun r hr => hMN r (hsM r hr)
  have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs0.card_pos.ne'

  have horbit : ∀ (F : ↥(principalSeries3 v χ)),
      (∀ m ∈ M, ∑ r ∈ s, (F : LocalGL3 v → ℂ) (p * m * r) = ∑ r ∈ s, (F : LocalGL3 v → ℂ) (p * r)) →
      (∀ m ∈ unipotentSet v, (¬ ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) →
        (F : LocalGL3 v → ℂ) (p * m) = 0) →
      ∀ m ∈ unipotentSet v, (sumTranslate v χ s F : LocalGL3 v → ℂ) (p * m)
        = if ∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂ then ∑ r ∈ s, (F : LocalGL3 v → ℂ) (p * r) else 0 := by
    intro F hsF hvF m hm
    rw [sumTranslate_apply]
    split_ifs with hin
    · obtain ⟨m₁, ⟨-, x, y, z, hm₁⟩, m₂, hm₂, rfl⟩ := hin
      rw [← hsF m₂ hm₂]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← mul_assoc p m₁ m₂, hm₁, mul_assoc, mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 F.2,
        ← mul_assoc]
    · refine Finset.sum_eq_zero fun r hr => ?_
      rw [mul_assoc]
      refine hvF (m * r) (mul_mem_unipotentSet v hm (hsN r hr)) ?_
      rintro ⟨m₁, hm₁, m₂, hm₂, hmr⟩
      refine hin ⟨m₁, hm₁, m₂ * r⁻¹, M.mul_mem hm₂ (M.inv_mem (hsM r hr)), ?_⟩
      rw [← mul_assoc, ← hmr, mul_inv_cancel_right]
  have hFf := horbit f hsf hvf
  have hFf' := horbit f' hsf' hvf'
  have hΛf := apply_sumTranslate_eq_card_mul v χ Λ hinv s hsN f
  have hΛf' := apply_sumTranslate_eq_card_mul v χ Λ hinv s hsN f'
  constructor
  · intro j

    have hD : Λ j ((∑ r ∈ s, (f' : LocalGL3 v → ℂ) (p * r)) • sumTranslate v χ s f
        - (∑ r ∈ s, (f : LocalGL3 v → ℂ) (p * r)) • sumTranslate v χ s f') = 0 := by
      refine hkill j _ fun g hg => ?_
      refine apply_eq_zero_of_forall_mul_eq_zero v χ hcover (fun g' hg' => ?_) (fun m hm => ?_) hg
      · simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [sumTranslate_apply_eq_zero v χ s hN hsN hfZ hg', sumTranslate_apply_eq_zero v χ s hN hsN hf'Z hg']
        ring
      · simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hFf m hm, hFf' m hm]
        split_ifs <;> ring
    rw [map_sub, map_smul, map_smul, hΛf j, hΛf' j, smul_eq_mul, smul_eq_mul, sub_eq_zero] at hD
    exact mul_left_cancel₀ hcard (by linear_combination hD)
  · intro hI j
    have hF : Λ j (sumTranslate v χ s f) = 0 := by
      refine hkill j _ fun g hg => ?_
      refine apply_eq_zero_of_forall_mul_eq_zero v χ hcover (fun g' hg' => ?_) (fun m hm => ?_) hg
      · exact sumTranslate_apply_eq_zero v χ s hN hsN hfZ hg'
      · rw [hFf m hm, hI]
        split_ifs <;> rfl
    rw [hΛf j] at hF
    exact (mul_eq_zero.mp hF).resolve_left hcard

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

private theorem exists_mul_apply_eq_mul_apply {Zi Zi1 : Set (LocalGL3 v)} {p : LocalGL3 v}
    (hN : ∀ g ∈ Zi, ∀ x y z : v.adicCompletion ℚ, g * upperUnipotent3 x y z ∈ Zi)
    (hcover : ∀ g ∈ Zi1, g ∉ Zi → ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
      (m : LocalGL3 v), m ∈ unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (p * m))
    (hsplit : ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ unipotentSet v) ∧ ∀ m ∈ unipotentSet v,
        (∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi)
    (hlevel : UniformlySmooth v χ)
    {n : ℕ} (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))
    (hinv : ∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f)
    (hkill : ∀ j, ∀ F : ↥(principalSeries3 v χ), (∀ g ∈ Zi1, (F : LocalGL3 v → ℂ) g = 0) → Λ j F = 0)
    (f f' : ↥(principalSeries3 v χ))
    (hfZ : ∀ g ∈ Zi, (f : LocalGL3 v → ℂ) g = 0) (hf'Z : ∀ g ∈ Zi, (f' : LocalGL3 v → ℂ) g = 0) :
    ∃ c c' : ℂ, (∀ j, c' * Λ j f = c * Λ j f') ∧ (c = 0 → ∀ j, Λ j f = 0) := by
  obtain ⟨t₁, ht₁⟩ := hlevel f f.2
  obtain ⟨t₂, ht₂⟩ := hlevel f' f'.2

  have hf : ∀ k, IsPrincipalCongruence v (max t₁ t₂) k →
      ∀ g, (f : LocalGL3 v → ℂ) (g * k) = (f : LocalGL3 v → ℂ) g :=
    fun k hk g => apply_mul_eq_of_level v χ ht₁ (le_max_left _ _) hk g
  have hf' : ∀ k, IsPrincipalCongruence v (max t₁ t₂) k →
      ∀ g, (f' : LocalGL3 v → ℂ) (g * k) = (f' : LocalGL3 v → ℂ) g :=
    fun k hk g => apply_mul_eq_of_level v χ ht₂ (le_max_right _ _) hk g
  obtain ⟨M, hMc, hMN, hM⟩ := hsplit (max t₁ t₂)

  have hUH : ∀ u ∈ {k : LocalGL3 v | IsPrincipalCongruence v (max t₁ t₂) k},
      u ∈ M → u ∈ M ⊓ smallBox v (max t₁ t₂) := by
    intro u hu huM
    obtain ⟨x, y, z, rfl⟩ := hMN u huM
    exact Subgroup.mem_inf.mpr ⟨huM, mem_smallBox_of_isPrincipalCongruence v
      (hu : IsPrincipalCongruence v (max t₁ t₂) (upperUnipotent3 x y z))⟩
  obtain ⟨s, hs0, hsM, hsum⟩ := exists_finset_sum_mul_mul_eq_sum_mul M (M ⊓ smallBox v (max t₁ t₂)) hMc
    (isOpen_setOf_isPrincipalCongruence v (max t₁ t₂)) (one_isPrincipalCongruence v _) hUH
  ·
    have hsF : ∀ (F : ↥(principalSeries3 v χ)),
        (∀ k, IsPrincipalCongruence v (max t₁ t₂) k →
          ∀ g, (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g) →
        ∀ m ∈ M, ∑ r ∈ s, (F : LocalGL3 v → ℂ) (p * m * r) = ∑ r ∈ s, (F : LocalGL3 v → ℂ) (p * r) := by
      intro F hF m hm
      refine hsum F (fun h hh g => hF h ?_ g) p m hm
      exact isPrincipalCongruence_of_mem_smallBox v (Subgroup.mem_inf.mp hh).2
    obtain ⟨hrel, hzero⟩ := sum_mul_apply_eq_sum_mul_apply v χ hN hcover Λ hinv hkill M hMN s hs0 hsM f f' hfZ hf'Z
      (hsF f hf) (hsF f' hf') (fun m hm hout => apply_mul_eq_zero_of_not_exists v χ hM hf hfZ hm hout)
      (fun m hm hout => apply_mul_eq_zero_of_not_exists v χ hM hf' hf'Z hm hout)
    exact ⟨_, _, hrel, hzero⟩

private theorem le_one_of_cell {Zi Zi1 : Set (LocalGL3 v)} {p : LocalGL3 v}
    (hN : ∀ g ∈ Zi, ∀ x y z : v.adicCompletion ℚ, g * upperUnipotent3 x y z ∈ Zi)
    (hcover : ∀ g ∈ Zi1, g ∉ Zi → ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
      (m : LocalGL3 v), m ∈ unipotentSet v ∧ g = upperUnipotent3 x y z * diagonal3 v a * (p * m))
    (hsplit : ∀ t : ℕ, ∃ M : Subgroup (LocalGL3 v), IsCompact (M : Set (LocalGL3 v)) ∧
      (∀ m ∈ M, m ∈ unipotentSet v) ∧ ∀ m ∈ unipotentSet v,
        (∃ m₁ ∈ absorbedBy v p, ∃ m₂ ∈ M, m = m₁ * m₂) ∨
          ∃ k : LocalGL3 v, IsPrincipalCongruence v t k ∧ p * m * k ∈ Zi)
    (hlevel : UniformlySmooth v χ)
    (W₀ W₁ : Submodule ℂ ↥(principalSeries3 v χ))
    (hW₀ : ∀ F : ↥(principalSeries3 v χ), F ∈ W₀ ↔ ∀ g ∈ Zi, (F : LocalGL3 v → ℂ) g = 0)
    (hW₁ : ∀ F : ↥(principalSeries3 v χ), F ∈ W₁ ↔ ∀ g ∈ Zi1, (F : LocalGL3 v → ℂ) g = 0)
    {n : ℕ} (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))
    (hinv : ∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f)
    (hkill : ∀ j, ∀ F ∈ W₁, Λ j F = 0)
    (hli : LinearIndependent ℂ fun j => (Λ j).domRestrict W₀) : n ≤ 1 :=
  le_one_of_forall_mem_exists_mul_eq_mul W₀ n Λ
    (fun f hf f' hf' => exists_mul_apply_eq_mul_apply v χ hN hcover hsplit hlevel Λ hinv
      (fun j F hF => hkill j F ((hW₁ F).mpr hF)) f f' ((hW₀ f).mp hf) ((hW₀ f').mp hf'))
    hli

end UnipotentBox
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField
open LanglandsTunnell LanglandsTunnell.CubicInduction

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
open LanglandsTunnell LanglandsTunnell.CubicInduction

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
open LanglandsTunnell LanglandsTunnell.CubicInduction

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
open LanglandsTunnell LanglandsTunnell.CubicInduction

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

section LeOne

variable (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private def LeOneBetween (k : Fin 7) (k' : Fin 7) : Prop :=
  ∀ (W₀ W₁ : Submodule ℂ ↥(principalSeries3 v χ)),
    (∀ F : ↥(principalSeries3 v χ), F ∈ W₀ ↔ ∀ g ∈ cornerChain v k, (F : LocalGL3 v → ℂ) g = 0) →
    (∀ F : ↥(principalSeries3 v χ), F ∈ W₁ ↔ ∀ g ∈ cornerChain v k', (F : LocalGL3 v → ℂ) g = 0) →
    ∀ (n : ℕ) (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)),
      (∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
        Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
            rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f) →
      (∀ j, ∀ F ∈ W₁, Λ j F = 0) →
      LinearIndependent ℂ (fun j => (Λ j).domRestrict W₀) → n ≤ 1

private theorem leOneBetween_zero_one (hlevel : UnipotentBox.UniformlySmooth v χ) : LeOneBetween v χ 0 1 :=
  fun W₀ W₁ hW₀ hW₁ _ Λ hinv hkill hli =>
    UnipotentBox.le_one_of_cell v χ (Zi := cornerChain v 0) (Zi1 := cornerChain v 1) (p := 1)
      (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 0 hg x y z)
      (exists_mul_one_mul_of_mem_cornerChain_one v) (exists_box_one v) hlevel W₀ W₁ hW₀ hW₁ Λ hinv hkill hli

private theorem leOneBetween_one_two (hlevel : UnipotentBox.UniformlySmooth v χ) : LeOneBetween v χ 1 2 :=
  fun W₀ W₁ hW₀ hW₁ _ Λ hinv hkill hli =>
    UnipotentBox.le_one_of_cell v χ (Zi := cornerChain v 1) (Zi1 := cornerChain v 2) (p := permPoint102 v)
      (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 1 hg x y z)
      (exists_mul_permPoint102_mul_of_mem_cornerChain_two v) (exists_box_permPoint102 v) hlevel W₀ W₁ hW₀ hW₁ Λ
      hinv hkill hli

private theorem leOneBetween_two_three (hlevel : UnipotentBox.UniformlySmooth v χ) : LeOneBetween v χ 2 3 :=
  fun W₀ W₁ hW₀ hW₁ _ Λ hinv hkill hli =>
    UnipotentBox.le_one_of_cell v χ (Zi := cornerChain v 2) (Zi1 := cornerChain v 3) (p := permPoint021 v)
      (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 2 hg x y z)
      (exists_mul_permPoint021_mul_of_mem_cornerChain_three v) (exists_box_permPoint021 v) hlevel W₀ W₁ hW₀ hW₁ Λ
      hinv hkill hli

private theorem leOneBetween_three_four (hlevel : UnipotentBox.UniformlySmooth v χ) : LeOneBetween v χ 3 4 :=
  fun W₀ W₁ hW₀ hW₁ _ Λ hinv hkill hli =>
    UnipotentBox.le_one_of_cell v χ (Zi := cornerChain v 3) (Zi1 := cornerChain v 4) (p := permPoint201 v)
      (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 3 hg x y z)
      (exists_mul_permPoint201_mul_of_mem_cornerChain_four v) (exists_box_permPoint201 v) hlevel W₀ W₁ hW₀ hW₁ Λ
      hinv hkill hli

private theorem leOneBetween_four_five (hlevel : UnipotentBox.UniformlySmooth v χ) : LeOneBetween v χ 4 5 :=
  fun W₀ W₁ hW₀ hW₁ _ Λ hinv hkill hli =>
    UnipotentBox.le_one_of_cell v χ (Zi := cornerChain v 4) (Zi1 := cornerChain v 5) (p := permPoint120 v)
      (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 4 hg x y z)
      (exists_mul_permPoint120_mul_of_mem_cornerChain_five v) (exists_box_permPoint120 v) hlevel W₀ W₁ hW₀ hW₁ Λ
      hinv hkill hli

private theorem leOneBetween_five_six (hlevel : UnipotentBox.UniformlySmooth v χ) : LeOneBetween v χ 5 6 :=
  fun W₀ W₁ hW₀ hW₁ _ Λ hinv hkill hli =>
    UnipotentBox.le_one_of_cell v χ (Zi := cornerChain v 5) (Zi1 := cornerChain v 6) (p := antidiagonal3 v)
      (fun _ hg x y z => mul_upperUnipotent3_mem_cornerChain v 5 hg x y z)
      (exists_mul_antidiagonal3_mul_of_mem_cornerChain_six v) (exists_box_antidiagonal3 v) hlevel W₀ W₁ hW₀ hW₁ Λ
      hinv hkill hli

end LeOne

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Z : Fin 7 → Set (LocalGL3 v))
    (hZ : Z = ![∅,
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0},
      {g | cornerEntry v g * lowerMinor v g = 0},
      Set.univ])
    (W : Fin 7 → Submodule ℂ ↥(principalSeries3 v χ))
    (hW : ∀ k : Fin 7, W k = Submodule.comap (principalSeries3 v χ).subtype
      (⨅ g ∈ Z k, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)))
    (i : Fin 6) (n : ℕ)
    (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :
    (∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f) →
    (∀ j, ∀ f ∈ W i.succ, Λ j f = 0) →
    LinearIndependent ℂ (fun j => (Λ j).domRestrict (W i.castSucc)) →
    n ≤ 1 := by
  intro hinv hkill hli
  have hlevel : UnipotentBox.UniformlySmooth v χ := fun f hf =>
    exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f hf
  have hWk : ∀ (k : Fin 7) (F : ↥(principalSeries3 v χ)),
      F ∈ W k ↔ ∀ g ∈ cornerChain v k, (F : LocalGL3 v → ℂ) g = 0 := by
    intro k F
    rw [hW k, hZ]
    exact mem_comap_iInf_ker_proj_iff v χ (cornerChain v k) F
  fin_cases i
  · exact leOneBetween_zero_one v χ hlevel (W 0) (W 1) (hWk 0) (hWk 1) n Λ hinv hkill hli
  · exact leOneBetween_one_two v χ hlevel (W 1) (W 2) (hWk 1) (hWk 2) n Λ hinv hkill hli
  · exact leOneBetween_two_three v χ hlevel (W 2) (W 3) (hWk 2) (hWk 3) n Λ hinv hkill hli
  · exact leOneBetween_three_four v χ hlevel (W 3) (W 4) (hWk 3) (hWk 4) n Λ hinv hkill hli
  · exact leOneBetween_four_five v χ hlevel (W 4) (W 5) (hWk 4) (hWk 5) n Λ hinv hkill hli
  · exact leOneBetween_five_six v χ hlevel (W 5) (W 6) (hWk 5) (hWk 6) n Λ hinv hkill hli
end

end S_LanglandsTunnell_CubicInduction_le_one_of_linearIndependent_domRestrict_of_upperUnipotent3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_le_one_of_linearIndependent_domRestrict_of_upperUnipotent3 (solution)
