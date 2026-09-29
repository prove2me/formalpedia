-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.matFourier23_leftBlock_mul_lastCol_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4ef59165-f841-57d8-88a7-fa81a092c73a

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_matFourier23_leftBlock_mul_lastCol_mul_const

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar

open NumberField.AdelicLevel (diagOne)

namespace F2TensorFourier

variable (p : HeightOneSpectrum (𝓞 ℚ))

def lb (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
  Matrix.of fun a b => X a (Fin.castSucc b)

theorem lb_setCol23_two (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (u : p.adicCompletion ℚ × p.adicCompletion ℚ) :
    lb p (setCol23 p X 2 u) = lb p X := by
  ext a b
  simp only [lb, Matrix.of_apply, setCol23_apply]
  have : (Fin.castSucc b : Fin 3) ≠ 2 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [if_neg this]

theorem setCol23_two_apply_02 (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (u : p.adicCompletion ℚ × p.adicCompletion ℚ) :
    setCol23 p X 2 u 0 2 = u.1 := by
  simp [setCol23_apply]

theorem setCol23_two_apply_12 (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (u : p.adicCompletion ℚ × p.adicCompletion ℚ) :
    setCol23 p X 2 u 1 2 = u.2 := by
  simp [setCol23_apply]

theorem lb_setCol23_castSucc (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (j : Fin 2)
    (u : p.adicCompletion ℚ × p.adicCompletion ℚ) :
    lb p (setCol23 p X (Fin.castSucc j) u) = setCol22 p (lb p X) j u := by
  ext a b
  simp only [lb, Matrix.of_apply, setCol23_apply, setCol22_apply, Fin.castSucc_inj]

theorem setCol23_castSucc_apply_last (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (j : Fin 2)
    (u : p.adicCompletion ℚ × p.adicCompletion ℚ) (i : Fin 2) :
    setCol23 p X (Fin.castSucc j) u i 2 = X i 2 := by
  simp only [setCol23_apply]
  have : (2 : Fin 3) ≠ Fin.castSucc j := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [if_neg this]

theorem lb_apply (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (a b : Fin 2) : lb p X a b = X a (Fin.castSucc b) := rfl

end F2TensorFourier

open F2TensorFourier in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (p.adicCompletion ℚ) ℂ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (c : ℂ) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    matFourier23 p η (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => φ₁ (Matrix.of fun a b => Y a (Fin.castSucc b)) * φ₂ (Y 0 2, Y 1 2) * c) X =
      matFourier22 p η φ₁ (Matrix.of fun a b => X a (Fin.castSucc b)) *
        (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ u * η (u.1 * X 0 2 + u.2 * X 1 2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) * c := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p

  set I₂ : ℂ := ∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ u * η (u.1 * X 0 2 + u.2 * X 1 2)
    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) with hI₂

  have h2 : ∀ Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ), (∀ i : Fin 2, Y i 2 = X i 2) →
      colFourier23 p η 2 (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) =>
        φ₁ (Matrix.of fun a b => Y a (Fin.castSucc b)) * φ₂ (Y 0 2, Y 1 2) * c) Y = φ₁ (lb p Y) * I₂ * c := by
    intro Y hY
    rw [colFourier23_apply]
    have : ∀ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
        φ₁ (Matrix.of fun a b => setCol23 p Y 2 u a (Fin.castSucc b)) * φ₂ (setCol23 p Y 2 u 0 2, setCol23 p Y 2 u 1 2) * c *
          η (u.1 * Y 0 2 + u.2 * Y 1 2) =
        (φ₁ (lb p Y) * c) * (φ₂ u * η (u.1 * X 0 2 + u.2 * X 1 2)) := by
      intro u
      rw [show (Matrix.of fun a b => setCol23 p Y 2 u a (Fin.castSucc b)) = lb p (setCol23 p Y 2 u) from rfl,
        lb_setCol23_two, setCol23_two_apply_02, setCol23_two_apply_12, Prod.mk.eta, hY 0, hY 1]
      ring
    simp_rw [this]
    rw [integral_const_mul, hI₂]
    ring

  have h1 : ∀ Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ), (∀ i : Fin 2, Y i 2 = X i 2) →
      colFourier23 p η 1 (colFourier23 p η 2 (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) =>
        φ₁ (Matrix.of fun a b => Y a (Fin.castSucc b)) * φ₂ (Y 0 2, Y 1 2) * c)) Y =
        colFourier22 p η 1 φ₁ (lb p Y) * I₂ * c := by
    intro Y hY
    rw [colFourier23_apply, colFourier22_apply]
    have : ∀ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
        colFourier23 p η 2 (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) =>
            φ₁ (Matrix.of fun a b => Y a (Fin.castSucc b)) * φ₂ (Y 0 2, Y 1 2) * c) (setCol23 p Y 1 u) *
          η (u.1 * Y 0 1 + u.2 * Y 1 1) =
        (I₂ * c) * (φ₁ (setCol22 p (lb p Y) 1 u) * η (u.1 * lb p Y 0 1 + u.2 * lb p Y 1 1)) := by
      intro u
      rw [h2 (setCol23 p Y 1 u) (fun i => by
        rw [show (1 : Fin 3) = Fin.castSucc 1 from rfl, setCol23_castSucc_apply_last, hY]),
        show (1 : Fin 3) = Fin.castSucc 1 from rfl, lb_setCol23_castSucc]
      simp only [lb_apply]
      ring
    simp_rw [this]
    rw [integral_const_mul]
    ring

  rw [matFourier23_eq, matFourier22_eq, colFourier23_apply, colFourier22_apply]
  have h0 : ∀ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
      colFourier23 p η 1 (colFourier23 p η 2 (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) =>
          φ₁ (Matrix.of fun a b => Y a (Fin.castSucc b)) * φ₂ (Y 0 2, Y 1 2) * c)) (setCol23 p X 0 u) *
        η (u.1 * X 0 0 + u.2 * X 1 0) =
      (I₂ * c) * (colFourier22 p η 1 φ₁ (setCol22 p (Matrix.of fun a b => X a (Fin.castSucc b)) 0 u) *
        η (u.1 * (Matrix.of fun a b => X a (Fin.castSucc b) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 +
          u.2 * (Matrix.of fun a b => X a (Fin.castSucc b) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0)) := by
    intro u
    rw [h1 (setCol23 p X 0 u) (fun i => by
      rw [show (0 : Fin 3) = Fin.castSucc 0 from rfl, setCol23_castSucc_apply_last]),
      show (0 : Fin 3) = Fin.castSucc 0 from rfl, lb_setCol23_castSucc]
    simp only [lb, Matrix.of_apply]
    ring
  simp_rw [h0]
  rw [integral_const_mul]
  ring

end S_LanglandsTunnell_CubicInduction_matFourier23_leftBlock_mul_lastCol_mul_const
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_matFourier23_leftBlock_mul_lastCol_mul_const (solution)
