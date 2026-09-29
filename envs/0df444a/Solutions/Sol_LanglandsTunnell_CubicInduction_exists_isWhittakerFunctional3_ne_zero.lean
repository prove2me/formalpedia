-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e96e21ad-6b45-5c51-9389-d8f72c0e6a17

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe principalSeries3 isLocallyConstant_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det cornerEntry_upperUnipotent3_mul lowerMinor_upperUnipotent3_mul cornerEntry_diagonal3_mul lowerMinor_diagonal3_mul cellRatio cellCutoff cellValue cellSection antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 outerMinor_antidiagonal3 gl3Det_antidiagonal3 isClopen_valued_le_one continuous_cornerEntry continuous_lowerMinor cellSection_mem_principalSeries3 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe LocalGL3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section BigCell

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_mul_upperUnipotent3_zero (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 0 = gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_one (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 1 = gl3Entry v g i 0 * x + gl3Entry v g i 1 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem cornerEntry_mul_upperUnipotent3 (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    cornerEntry v (g * upperUnipotent3 x y z) = cornerEntry v g :=
  gl3Entry_mul_upperUnipotent3_zero v g x y z 2

private theorem lowerMinor_mul_upperUnipotent3 (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    lowerMinor v (g * upperUnipotent3 x y z) = lowerMinor v g := by
  simp only [lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_one]
  ring

private def bigCell : Set (LocalGL3 v) := {g | cornerEntry v g ≠ 0 ∧ lowerMinor v g ≠ 0}

private theorem isOpen_bigCell : IsOpen (bigCell v) :=
  (isOpen_ne.preimage (continuous_cornerEntry v)).inter (isOpen_ne.preimage (continuous_lowerMinor v))

private theorem mul_upperUnipotent3_mem_bigCell_iff (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    g * upperUnipotent3 x y z ∈ bigCell v ↔ g ∈ bigCell v := by
  simp only [bigCell, Set.mem_setOf_eq, cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3]

private theorem upperUnipotent3_mul_mem_bigCell_iff (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    upperUnipotent3 x y z * g ∈ bigCell v ↔ g ∈ bigCell v := by
  simp only [bigCell, Set.mem_setOf_eq, cornerEntry_upperUnipotent3_mul, lowerMinor_upperUnipotent3_mul]

private theorem diagonal3_mul_mem_bigCell_iff (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    diagonal3 v a * g ∈ bigCell v ↔ g ∈ bigCell v := by
  simp only [bigCell, Set.mem_setOf_eq, cornerEntry_diagonal3_mul, lowerMinor_diagonal3_mul, ne_eq, mul_eq_zero,
    Units.ne_zero, false_or]

private theorem antidiagonal3_mem_bigCell : antidiagonal3 v ∈ bigCell v := by
  refine ⟨?_, ?_⟩
  · rw [cornerEntry_antidiagonal3]
    exact one_ne_zero
  · rw [lowerMinor_antidiagonal3]
    exact neg_ne_zero.mpr one_ne_zero

private theorem cellCutoff_subset_bigCell : cellCutoff v ⊆ bigCell v := fun _ hg => ⟨hg.1, hg.2.1⟩

private def unipotentBall (c : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧
    Valued.v p.2.2 ≤ WithZero.exp (2 * c)}

private theorem upperUnipotent3_mul_upperUnipotent3 (x y z x' y' z' : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) * upperUnipotent3 x' y' z'
      = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end BigCell

section TranslatedSection

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_mul_upperUnipotent3_last (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 2
      = gl3Entry v g i 0 * z + gl3Entry v g i 1 * y + gl3Entry v g i 2 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem outerMinor_mul_upperUnipotent3 (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    outerMinor v (g * upperUnipotent3 x y z) = outerMinor v g + lowerMinor v g * y := by
  simp only [outerMinor, lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_last]
  ring

private theorem gl3Det_mul_upperUnipotent3 (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    gl3Det v (g * upperUnipotent3 x y z) = gl3Det v g := by
  have h1 : Matrix.det !![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] = 1 := by
    simp [Matrix.det_fin_three]
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, h1, mul_one]

private theorem gl3Entry_mul_diagonal3 (g : LocalGL3 v) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (i j : Fin 3) :
    gl3Entry v (g * diagonal3 v a) i j = gl3Entry v g i j * (a j : v.adicCompletion ℚ) := by
  simp [gl3Entry, diagonal3_coe, Matrix.mul_diagonal]

private theorem cornerEntry_mul_diagonal3 (g : LocalGL3 v) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (g * diagonal3 v a) = cornerEntry v g * (a 0 : v.adicCompletion ℚ) :=
  gl3Entry_mul_diagonal3 v g a 2 0

private theorem lowerMinor_mul_diagonal3 (g : LocalGL3 v) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (g * diagonal3 v a) = lowerMinor v g * ((a 0 : v.adicCompletion ℚ) * a 1) := by
  simp only [lowerMinor, gl3Entry_mul_diagonal3]
  ring

private theorem outerMinor_mul_diagonal3 (g : LocalGL3 v) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    outerMinor v (g * diagonal3 v a) = outerMinor v g * ((a 0 : v.adicCompletion ℚ) * a 2) := by
  simp only [outerMinor, gl3Entry_mul_diagonal3]
  ring

private theorem gl3Det_mul_diagonal3 (g : LocalGL3 v) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    gl3Det v (g * diagonal3 v a) = gl3Det v g * ((a 0 : v.adicCompletion ℚ) * a 1 * a 2) := by
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, diagonal3_coe, Matrix.det_diagonal, Fin.prod_univ_three]

private theorem cellValue_mul_upperUnipotent3_mul_diagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    cellValue v χ (g * upperUnipotent3 x y z * diagonal3 v a) = cellValue v χ (g * diagonal3 v a) := by
  simp only [cellValue, cornerEntry_mul_diagonal3, lowerMinor_mul_diagonal3, gl3Det_mul_diagonal3,
    cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, gl3Det_mul_upperUnipotent3]

private def scalingDiagonal (c : ℤ) : Fin 3 → (v.adicCompletion ℚ)ˣ :=
  ![1, uniformizerUnit ℚ v ^ c, uniformizerUnit ℚ v ^ (2 * c)]

private theorem scalingDiagonal_zero (c : ℤ) :
    ((scalingDiagonal v c 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  rw [show scalingDiagonal v c 0 = 1 from rfl, Units.val_one]

private theorem scalingDiagonal_one (c : ℤ) : ((scalingDiagonal v c 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
    = ((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ^ c := by
  rw [show scalingDiagonal v c 1 = uniformizerUnit ℚ v ^ c from rfl, Units.val_zpow_eq_zpow_val]

private theorem scalingDiagonal_two (c : ℤ) : ((scalingDiagonal v c 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
    = ((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ^ (2 * c) := by
  rw [show scalingDiagonal v c 2 = uniformizerUnit ℚ v ^ (2 * c) from rfl, Units.val_zpow_eq_zpow_val]

private def scaledCellSection (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : ℤ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (diagonal3 v (scalingDiagonal v c)) (cellSection v χ)

private def scaledCellValue (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : ℤ) : ℂ :=
  cellValue v χ (antidiagonal3 v * diagonal3 v (scalingDiagonal v c))

private theorem scaledCellSection_mem_principalSeries3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) (c : ℤ) : scaledCellSection v χ c ∈ principalSeries3 v χ :=
  rightTranslate_mem_principalSeries3 (cellSection_mem_principalSeries3 v χ hχ) _

private theorem valued_mul_zpow_uniformizerUnit_le_one_iff (t : v.adicCompletion ℚ) (e : ℤ) :
    Valued.v (t * ((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ^ e) ≤ 1 ↔
      Valued.v t ≤ WithZero.exp e := by
  have hpow : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ^ e = (WithZero.exp e)⁻¹ := by
    rw [← WithZero.exp_zsmul, ← WithZero.exp_neg]
    congr 1
    simp
  have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp e :=
    lt_of_le_of_ne zero_le' WithZero.exp_ne_zero.symm
  rw [Valuation.map_mul, map_zpow₀, valued_uniformizerUnit, hpow, mul_inv_le_iff₀ hpos, one_mul]

private theorem cornerEntry_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    cornerEntry v (antidiagonal3 v * upperUnipotent3 x y z) = 1 := by
  rw [cornerEntry_mul_upperUnipotent3, cornerEntry_antidiagonal3]

private theorem lowerMinor_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    lowerMinor v (antidiagonal3 v * upperUnipotent3 x y z) = -1 := by
  rw [lowerMinor_mul_upperUnipotent3, lowerMinor_antidiagonal3]

private theorem outerMinor_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    outerMinor v (antidiagonal3 v * upperUnipotent3 x y z) = -y := by
  rw [outerMinor_mul_upperUnipotent3, outerMinor_antidiagonal3, lowerMinor_antidiagonal3]
  ring

private theorem gl3Entry_antidiagonal3_mul_upperUnipotent3_two_one (x y z : v.adicCompletion ℚ) :
    gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 2 1 = x := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, antidiagonal3_coe]

private theorem gl3Entry_antidiagonal3_mul_upperUnipotent3_two_two (x y z : v.adicCompletion ℚ) :
    gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 2 2 = z := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three, antidiagonal3_coe]

private theorem antidiagonal3_mul_upperUnipotent3_mul_scalingDiagonal_mem_cellCutoff_iff (c : ℤ)
    (x y z : v.adicCompletion ℚ) :
    antidiagonal3 v * upperUnipotent3 x y z * diagonal3 v (scalingDiagonal v c) ∈ cellCutoff v ↔
      (x, y, z) ∈ unipotentBall v c := by
  set ϖ : v.adicCompletion ℚ := ((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) with hϖ
  have hϖ0 : ϖ ≠ 0 := Units.ne_zero _
  have ha0 : ((scalingDiagonal v c 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := scalingDiagonal_zero v c
  have ha1 : ((scalingDiagonal v c 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ϖ ^ c := scalingDiagonal_one v c
  have ha2 : ((scalingDiagonal v c 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ϖ ^ (2 * c) :=
    scalingDiagonal_two v c
  have hcorner : cornerEntry v (antidiagonal3 v * upperUnipotent3 x y z * diagonal3 v (scalingDiagonal v c)) = 1 := by
    rw [cornerEntry_mul_diagonal3, cornerEntry_antidiagonal3_mul_upperUnipotent3, ha0, one_mul]
  have hlower : lowerMinor v (antidiagonal3 v * upperUnipotent3 x y z * diagonal3 v (scalingDiagonal v c))
      = -(ϖ ^ c) := by
    rw [lowerMinor_mul_diagonal3, lowerMinor_antidiagonal3_mul_upperUnipotent3, ha0, ha1]
    ring
  have houter : outerMinor v (antidiagonal3 v * upperUnipotent3 x y z * diagonal3 v (scalingDiagonal v c))
      = -(y * ϖ ^ (2 * c)) := by
    rw [outerMinor_mul_diagonal3, outerMinor_antidiagonal3_mul_upperUnipotent3, ha0, ha2]
    ring
  have h21 : gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z * diagonal3 v (scalingDiagonal v c)) 2 1
      = x * ϖ ^ c := by
    rw [gl3Entry_mul_diagonal3, gl3Entry_antidiagonal3_mul_upperUnipotent3_two_one, ha1]
  have h22 : gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z * diagonal3 v (scalingDiagonal v c)) 2 2
      = z * ϖ ^ (2 * c) := by
    rw [gl3Entry_mul_diagonal3, gl3Entry_antidiagonal3_mul_upperUnipotent3_two_two, ha2]
  have hratio : cellRatio v (antidiagonal3 v * upperUnipotent3 x y z * diagonal3 v (scalingDiagonal v c))
      = ![x * ϖ ^ c, z * ϖ ^ (2 * c), y * ϖ ^ c] := by
    have hy : -(y * ϖ ^ (2 * c)) / -(ϖ ^ c) = y * ϖ ^ c := by
      rw [neg_div_neg_eq, two_mul, zpow_add₀ hϖ0, ← mul_assoc, mul_div_assoc,
        div_self (zpow_ne_zero c hϖ0), mul_one]
    simp only [cellRatio, hcorner, hlower, houter, h21, h22, div_one, hy]
  have hx' : Valued.v (x * ϖ ^ c) ≤ 1 ↔ Valued.v x ≤ WithZero.exp c :=
    valued_mul_zpow_uniformizerUnit_le_one_iff v x c
  have hy' : Valued.v (y * ϖ ^ c) ≤ 1 ↔ Valued.v y ≤ WithZero.exp c :=
    valued_mul_zpow_uniformizerUnit_le_one_iff v y c
  have hz' : Valued.v (z * ϖ ^ (2 * c)) ≤ 1 ↔ Valued.v z ≤ WithZero.exp (2 * c) :=
    valued_mul_zpow_uniformizerUnit_le_one_iff v z (2 * c)
  have hmem : (∀ i, Valued.v (![x * ϖ ^ c, z * ϖ ^ (2 * c), y * ϖ ^ c] i) ≤ 1) ↔
      (x, y, z) ∈ unipotentBall v c := by
    constructor
    · intro h
      exact ⟨hx'.mp (by simpa using h 0), hy'.mp (by simpa using h 2), hz'.mp (by simpa using h 1)⟩
    · rintro ⟨hx, hy, hz⟩ i
      fin_cases i
      · simpa using hx'.mpr hx
      · simpa using hz'.mpr hz
      · simpa using hy'.mpr hy
  rw [cellCutoff, Set.mem_setOf_eq, hcorner, hlower, hratio]
  constructor
  · rintro ⟨-, -, h⟩
    exact hmem.mp h
  · intro h
    exact ⟨one_ne_zero, neg_ne_zero.mpr (zpow_ne_zero c hϖ0), hmem.mpr h⟩

open scoped Classical in

private theorem scaledCellSection_antidiagonal3_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : ℤ)
    (x y z : v.adicCompletion ℚ) :
    scaledCellSection v χ c (antidiagonal3 v * upperUnipotent3 x y z)
      = if (x, y, z) ∈ unipotentBall v c then scaledCellValue v χ c else 0 := by
  rw [scaledCellSection, gl3AmbientRightTranslate_apply, cellSection]
  split_ifs with h
  · rw [Set.indicator_of_mem
      ((antidiagonal3_mul_upperUnipotent3_mul_scalingDiagonal_mem_cellCutoff_iff v c x y z).mpr h),
      cellValue_mul_upperUnipotent3_mul_diagonal3, scaledCellValue]
  · exact Set.indicator_of_notMem
      (fun hm => h ((antidiagonal3_mul_upperUnipotent3_mul_scalingDiagonal_mem_cellCutoff_iff v c x y z).mp hm)) _

private theorem scaledCellValue_ne_zero (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : ℤ) :
    scaledCellValue v χ c ≠ 0 := by
  set ϖ : v.adicCompletion ℚ := ((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) with hϖ
  have hϖ0 : ϖ ≠ 0 := Units.ne_zero _
  have ha0 : ((scalingDiagonal v c 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := scalingDiagonal_zero v c
  have ha1 : ((scalingDiagonal v c 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ϖ ^ c := scalingDiagonal_one v c
  have ha2 : ((scalingDiagonal v c 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ϖ ^ (2 * c) :=
    scalingDiagonal_two v c
  have hc0 : ϖ ^ c ≠ 0 := zpow_ne_zero c hϖ0
  have h2c0 : ϖ ^ (2 * c) ≠ 0 := zpow_ne_zero (2 * c) hϖ0
  have hdet : gl3Det v (antidiagonal3 v * diagonal3 v (scalingDiagonal v c))
      / lowerMinor v (antidiagonal3 v * diagonal3 v (scalingDiagonal v c)) = ϖ ^ (2 * c) := by
    rw [gl3Det_mul_diagonal3, lowerMinor_mul_diagonal3, gl3Det_antidiagonal3, lowerMinor_antidiagonal3, ha0, ha1, ha2]
    field_simp
  have hlow : lowerMinor v (antidiagonal3 v * diagonal3 v (scalingDiagonal v c))
      / cornerEntry v (antidiagonal3 v * diagonal3 v (scalingDiagonal v c)) = -(ϖ ^ c) := by
    rw [lowerMinor_mul_diagonal3, cornerEntry_mul_diagonal3, lowerMinor_antidiagonal3, cornerEntry_antidiagonal3,
      ha0, ha1]
    ring
  have hcor : cornerEntry v (antidiagonal3 v * diagonal3 v (scalingDiagonal v c)) = 1 := by
    rw [cornerEntry_mul_diagonal3, cornerEntry_antidiagonal3, ha0, one_mul]
  have hneg : -(ϖ ^ c) ≠ 0 := neg_ne_zero.mpr hc0
  rw [scaledCellValue, cellValue, hdet, hlow, hcor, charExt_of_ne_zero _ h2c0, charExt_of_ne_zero _ hneg,
    charExt_of_ne_zero _ one_ne_zero]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Units.ne_zero _)) ?_
  exact Complex.ofReal_ne_zero.mpr
    (div_ne_zero (norm_ne_zero_iff.mpr h2c0) (norm_ne_zero_iff.mpr one_ne_zero))

end TranslatedSection

section UnipotentBall

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem zero_mem_unipotentBall (c : ℤ) :
    ((0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ)) ∈ unipotentBall v c := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

private theorem exp_two_mul (c : ℤ) :
    (WithZero.exp (2 * c) : WithZero (Multiplicative ℤ)) = WithZero.exp c * WithZero.exp c := by
  rw [two_mul, WithZero.exp_add]

variable {v}

private theorem mem_unipotentBall_mul {c : ℤ} {x y z x' y' z' : v.adicCompletion ℚ} (h : (x, y, z) ∈ unipotentBall v c)
    (h' : (x', y', z') ∈ unipotentBall v c) : (x + x', y + y', z + z' + x * y') ∈ unipotentBall v c := by
  obtain ⟨hx, hy, hz⟩ := h
  obtain ⟨hx', hy', hz'⟩ := h'
  have hx : Valued.v x ≤ WithZero.exp c := hx
  have hy : Valued.v y ≤ WithZero.exp c := hy
  have hz : Valued.v z ≤ WithZero.exp (2 * c) := hz
  have hx' : Valued.v x' ≤ WithZero.exp c := hx'
  have hy' : Valued.v y' ≤ WithZero.exp c := hy'
  have hz' : Valued.v z' ≤ WithZero.exp (2 * c) := hz'
  refine ⟨(Valued.v.map_add x x').trans (max_le hx hx'), (Valued.v.map_add y y').trans (max_le hy hy'), ?_⟩
  refine (Valued.v.map_add (z + z') (x * y')).trans (max_le ((Valued.v.map_add z z').trans (max_le hz hz')) ?_)
  rw [Valuation.map_mul, exp_two_mul]
  exact mul_le_mul' hx hy'

private theorem mem_unipotentBall_inv {c : ℤ} {x y z : v.adicCompletion ℚ} (h : (x, y, z) ∈ unipotentBall v c) :
    (-x, -y, x * y - z) ∈ unipotentBall v c := by
  obtain ⟨hx, hy, hz⟩ := h
  have hx : Valued.v x ≤ WithZero.exp c := hx
  have hy : Valued.v y ≤ WithZero.exp c := hy
  have hz : Valued.v z ≤ WithZero.exp (2 * c) := hz
  refine ⟨?_, ?_, ?_⟩
  · rwa [Valuation.map_neg]
  · rwa [Valuation.map_neg]
  · refine (Valued.v.map_sub (x * y) z).trans (max_le ?_ hz)
    rw [Valuation.map_mul, exp_two_mul]
    exact mul_le_mul' hx hy

private theorem upperUnipotent3_mul_upperUnipotent3_neg (x y z : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) * upperUnipotent3 (-x) (-y) (x * y - z) = upperUnipotent3 0 0 0 := by
  rw [upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

end UnipotentBall

section WhittakerDetector

open MeasureTheory

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isClopen_valued_le (c : ℤ) :
    IsClopen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} := by
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp c)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero ((map_zero Valued.v).symm.trans ha).symm
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} =
      (fun x => a⁻¹ * x) ⁻¹' {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
    ext x
    have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v a := by
      rw [ha]
      exact zero_lt_iff.mpr WithZero.exp_ne_zero
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.map_mul, map_inv₀, ← ha]
    rw [inv_mul_le_iff₀ hpos, mul_one]
  rw [hset]
  exact (isClopen_valued_le_one v).preimage (continuous_const.mul continuous_id)

private theorem isCompact_valued_le (c : ℤ) :
    IsCompact {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} := by
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp c)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero ((map_zero Valued.v).symm.trans ha).symm
  have hint : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} =
      (fun y => a * y) '' (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    ext x
    have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v a := by
      rw [ha]
      exact zero_lt_iff.mpr WithZero.exp_ne_zero
    constructor
    · intro hx
      refine ⟨a⁻¹ * x, ?_, mul_inv_cancel_left₀ ha0 x⟩
      show Valued.v (a⁻¹ * x) ≤ 1
      rw [Valuation.map_mul, map_inv₀, inv_mul_le_iff₀ hpos, mul_one, ha]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      have hy' : Valued.v y ≤ 1 := hy
      show Valued.v (a * y) ≤ WithZero.exp c
      rw [Valuation.map_mul, ha]
      exact mul_le_of_le_one_right' hy'
  rw [hset]
  exact hint.image (continuous_const.mul continuous_id)

private theorem unipotentBall_eq_prod (c : ℤ) :
    unipotentBall v c =
      {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} ×ˢ
        ({y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} ×ˢ
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)}) := by
  ext p
  simp only [unipotentBall, Set.mem_setOf_eq, Set.mem_prod]

private theorem isClopen_unipotentBall (c : ℤ) : IsClopen (unipotentBall v c) := by
  rw [unipotentBall_eq_prod]
  exact (isClopen_valued_le v c).prod ((isClopen_valued_le v c).prod (isClopen_valued_le v (2 * c)))

private theorem isCompact_unipotentBall (c : ℤ) : IsCompact (unipotentBall v c) := by
  rw [unipotentBall_eq_prod]
  exact (isCompact_valued_le v c).prod ((isCompact_valued_le v c).prod (isCompact_valued_le v (2 * c)))

private theorem unipotentBall_mono {c d : ℤ} (hcd : c ≤ d) : unipotentBall v c ⊆ unipotentBall v d := by
  intro p hp
  simp only [unipotentBall, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨h₁, h₂, h₃⟩ := hp
  exact ⟨h₁.trans (WithZero.exp_le_exp.mpr hcd), h₂.trans (WithZero.exp_le_exp.mpr hcd),
    h₃.trans (WithZero.exp_le_exp.mpr (by omega))⟩

private theorem exists_valued_le_exp (x : v.adicCompletion ℚ) : ∃ n : ℤ, Valued.v x ≤ WithZero.exp n := by
  by_cases hx : Valued.v x = (0 : WithZero (Multiplicative ℤ))
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), (WithZero.exp_log hx).symm.le⟩

private theorem exists_mem_unipotentBall (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ∃ c : ℤ, p ∈ unipotentBall v c := by
  obtain ⟨a, ha⟩ := exists_valued_le_exp v p.1
  obtain ⟨b, hb⟩ := exists_valued_le_exp v p.2.1
  obtain ⟨d, hd⟩ := exists_valued_le_exp v p.2.2
  refine ⟨max (max a b) (max d 0), ?_⟩
  simp only [unipotentBall, Set.mem_setOf_eq]
  exact ⟨ha.trans (WithZero.exp_le_exp.mpr (by omega)), hb.trans (WithZero.exp_le_exp.mpr (by omega)),
    hd.trans (WithZero.exp_le_exp.mpr (by omega))⟩

private theorem valued_add_le_of_le {x y : v.adicCompletion ℚ} {γ : WithZero (Multiplicative ℤ)}
    (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) : Valued.v (x + y) ≤ γ :=
  (Valued.v.map_add x y).trans (max_le hx hy)

private def coordTranslate (q p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1)

private theorem upperUnipotent3_mul_eq_coordTranslate
    (p q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v) * upperUnipotent3 q.1 q.2.1 q.2.2 =
      upperUnipotent3 (coordTranslate v q p).1 (coordTranslate v q p).2.1 (coordTranslate v q p).2.2 :=
  upperUnipotent3_mul_upperUnipotent3 v p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2

private theorem coordTranslate_mem_unipotentBall_iff {c : ℤ}
    {q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ} (hq : q ∈ unipotentBall v c)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    coordTranslate v q p ∈ unipotentBall v c ↔ p ∈ unipotentBall v c := by
  obtain ⟨x, y, z⟩ := p
  obtain ⟨x', y', z'⟩ := q
  refine ⟨fun h => ?_, fun hp => mem_unipotentBall_mul hp hq⟩
  have h' := mem_unipotentBall_mul h (mem_unipotentBall_inv hq)
  convert h' using 1
  ext <;> simp
  ring

private def coordTranslateHomeomorph (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) ≃ₜ
      (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) where
  toFun := coordTranslate v q
  invFun := coordTranslate v (-q.1, -q.2.1, q.1 * q.2.1 - q.2.2)
  left_inv p := by
    obtain ⟨x, y, z⟩ := p
    ext <;> simp [coordTranslate] <;> ring
  right_inv p := by
    obtain ⟨x, y, z⟩ := p
    ext <;> simp [coordTranslate] <;> ring
  continuous_toFun := by
    show Continuous fun p => coordTranslate v q p
    simp only [coordTranslate]
    fun_prop
  continuous_invFun := by
    show Continuous fun p => coordTranslate v (-q.1, -q.2.1, q.1 * q.2.1 - q.2.2) p
    simp only [coordTranslate]
    fun_prop

private theorem continuous_upperUnipotent3_coords :
    Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (!![1, p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (!![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private abbrev borelAdicCompletion : MeasurableSpace (v.adicCompletion ℚ) := borel (v.adicCompletion ℚ)

attribute [local instance] borelAdicCompletion

private theorem borelSpace_adicCompletion : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩

attribute [local instance] borelSpace_adicCompletion

private noncomputable abbrev coordHaar :
    Measure (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  (Measure.addHaar : Measure (v.adicCompletion ℚ)).prod
    ((Measure.addHaar : Measure (v.adicCompletion ℚ)).prod (Measure.addHaar : Measure (v.adicCompletion ℚ)))

private theorem measurePreserving_coordTranslate
    (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    MeasurePreserving (coordTranslate v q) (coordHaar v) (coordHaar v) := by
  have hshear : MeasurePreserving
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (p.1, (p.2.1, p.2.2 + p.1 * q.2.1))) (coordHaar v) (coordHaar v) := by
    refine (MeasurePreserving.id _).skew_product
      (g := fun x (r : v.adicCompletion ℚ × v.adicCompletion ℚ) => (r.1, r.2 + x * q.2.1)) ?_ ?_
    · exact (by fun_prop : Continuous fun s : v.adicCompletion ℚ × (v.adicCompletion ℚ × v.adicCompletion ℚ) =>
        (s.2.1, s.2.2 + s.1 * q.2.1)).measurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have h := (measurePreserving_add_right
        ((Measure.addHaar : Measure (v.adicCompletion ℚ)).prod (Measure.addHaar : Measure (v.adicCompletion ℚ)))
        ((0 : v.adicCompletion ℚ), x * q.2.1)).map_eq
      convert h using 2
      funext r
      ext <;> simp
  have htrans := measurePreserving_add_right (coordHaar v) q
  have hcomp := htrans.comp hshear
  convert hcomp using 1
  funext p
  obtain ⟨x, y, z⟩ := p
  obtain ⟨x', y', z'⟩ := q
  ext <;> simp [coordTranslate]
  ring

private theorem integral_comp_coordTranslate
    (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ)
    (G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) :
    ∫ p, G (coordTranslate v q p) ∂(coordHaar v) = ∫ p, G p ∂(coordHaar v) :=
  (measurePreserving_coordTranslate v q).integral_comp
    (coordTranslateHomeomorph v q).measurableEmbedding G

private noncomputable def detectorIntegrand (ψ : AddChar (v.adicCompletion ℚ) ℂ) (c : ℤ) (u : LocalGL3 v → ℂ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) : ℂ :=
  (unipotentBall v c).indicator
    (fun p => ψ (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) p

private noncomputable def whittakerDetector (ψ : AddChar (v.adicCompletion ℚ) ℂ) (c : ℤ) (u : LocalGL3 v → ℂ) : ℂ :=
  ∫ p, detectorIntegrand v ψ c u p ∂(coordHaar v)

private theorem integrable_detectorIntegrand {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ : Continuous ψ) (c : ℤ)
    {u : LocalGL3 v → ℂ} (hu : Continuous u) : Integrable (detectorIntegrand v ψ c u) (coordHaar v) := by
  have hcont : Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      ψ (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) :=
    (hψ.comp (by fun_prop)).mul (hu.comp (continuous_const.mul (continuous_upperUnipotent3_coords v)))
  exact (integrable_indicator_iff (isClopen_unipotentBall v c).isOpen.measurableSet).mpr
    (hcont.continuousOn.integrableOn_compact (isCompact_unipotentBall v c))

private noncomputable def detectorForm (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ : Continuous ψ) (c : ℤ) : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ where
  toFun F := whittakerDetector v ψ c F.1
  map_add' F G := by
    have hF := integrable_detectorIntegrand v hψ c (isLocallyConstant_of_mem_principalSeries3 F.2).continuous
    have hG := integrable_detectorIntegrand v hψ c (isLocallyConstant_of_mem_principalSeries3 G.2).continuous
    simp only [whittakerDetector, Submodule.coe_add]
    rw [← integral_add hF hG]
    congr 1
    funext p
    by_cases hp : p ∈ unipotentBall v c <;> simp [detectorIntegrand, hp, mul_add]
  map_smul' a F := by
    have hF := integrable_detectorIntegrand v hψ c (isLocallyConstant_of_mem_principalSeries3 F.2).continuous
    simp only [whittakerDetector, Submodule.coe_smul, RingHom.id_apply]
    rw [← integral_smul]
    congr 1
    funext p
    by_cases hp : p ∈ unipotentBall v c <;> simp [detectorIntegrand, hp]
    ring

private theorem detectorForm_apply (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ : Continuous ψ) (c : ℤ) (F : ↥(principalSeries3 v χ)) :
    detectorForm v χ hψ c F = whittakerDetector v ψ c F.1 := rfl

private theorem detector_rightTranslate (ψ : AddChar (v.adicCompletion ℚ) ℂ) {c : ℤ}
    {q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ} (hq : q ∈ unipotentBall v c)
    (u : LocalGL3 v → ℂ) :
    whittakerDetector v ψ c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 q.1 q.2.1 q.2.2) u) =
      ψ (q.1 + q.2.1) * whittakerDetector v ψ c u := by
  have hψq : ψ (q.1 + q.2.1) * ψ (-(q.1 + q.2.1)) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hpt : ∀ p, detectorIntegrand v ψ c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 q.1 q.2.1 q.2.2) u) p =
      ψ (q.1 + q.2.1) * detectorIntegrand v ψ c u (coordTranslate v q p) := by
    intro p
    by_cases hp : p ∈ unipotentBall v c
    · have hp' : coordTranslate v q p ∈ unipotentBall v c := (coordTranslate_mem_unipotentBall_iff v hq p).mpr hp
      simp only [detectorIntegrand, Set.indicator_of_mem hp, Set.indicator_of_mem hp',
        gl3AmbientRightTranslate_apply, mul_assoc (antidiagonal3 v), upperUnipotent3_mul_eq_coordTranslate]
      have hsplit : ψ (-((coordTranslate v q p).1 + (coordTranslate v q p).2.1)) =
          ψ (-(p.1 + p.2.1)) * ψ (-(q.1 + q.2.1)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        simp only [coordTranslate]
        ring
      have hscal : ψ (q.1 + q.2.1) * ψ (-((coordTranslate v q p).1 + (coordTranslate v q p).2.1)) =
          ψ (-(p.1 + p.2.1)) := by
        rw [hsplit]
        linear_combination ψ (-(p.1 + p.2.1)) * hψq
      rw [← mul_assoc, hscal]
    · have hp' : coordTranslate v q p ∉ unipotentBall v c := fun h =>
        hp ((coordTranslate_mem_unipotentBall_iff v hq p).mp h)
      simp only [detectorIntegrand, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp', mul_zero]
  simp only [whittakerDetector]
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_coordTranslate]

open scoped Classical in

private theorem detector_eq_of_apply_eq_ite (ψ : AddChar (v.adicCompletion ℚ) ℂ) {m : ℤ}
    (hm : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψ x = 1) {c₀ c : ℤ} (hc₀m : c₀ ≤ m)
    (hc₀c : c₀ ≤ c) {u : LocalGL3 v → ℂ} {C : ℂ}
    (hu : ∀ x y z : v.adicCompletion ℚ,
      u (antidiagonal3 v * upperUnipotent3 x y z) = if (x, y, z) ∈ unipotentBall v c₀ then C else 0) :
    whittakerDetector v ψ c u = (coordHaar v).real (unipotentBall v c₀) • C := by
  have hpt : ∀ p, detectorIntegrand v ψ c u p = (unipotentBall v c₀).indicator (fun _ => C) p := by
    intro p
    by_cases hp₀ : p ∈ unipotentBall v c₀
    · have hpc : p ∈ unipotentBall v c := unipotentBall_mono v hc₀c hp₀
      have hψ1 : ψ (-(p.1 + p.2.1)) = 1 := by
        have hball := hp₀
        simp only [unipotentBall, Set.mem_setOf_eq] at hball
        refine hm _ ?_
        rw [Valuation.map_neg]
        exact (valued_add_le_of_le v hball.1 hball.2.1).trans (WithZero.exp_le_exp.mpr hc₀m)
      rw [detectorIntegrand, Set.indicator_of_mem hpc, Set.indicator_of_mem hp₀, hu, if_pos hp₀, hψ1, one_mul]
    · rw [Set.indicator_of_notMem hp₀]
      by_cases hpc : p ∈ unipotentBall v c
      · rw [detectorIntegrand, Set.indicator_of_mem hpc, hu, if_neg hp₀, mul_zero]
      · rw [detectorIntegrand, Set.indicator_of_notMem hpc]
  simp only [whittakerDetector]
  simp_rw [hpt]
  exact integral_indicator_const C (isClopen_unipotentBall v c₀).isOpen.measurableSet

private theorem coordHaar_real_unipotentBall_pos (c : ℤ) : 0 < (coordHaar v).real (unipotentBall v c) := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ (isCompact_unipotentBall v c).measure_lt_top.ne
  exact ((isClopen_unipotentBall v c).isOpen.measure_pos (coordHaar v) ⟨_, zero_mem_unipotentBall v c⟩).ne'

private theorem continuous_addChar_of_eq_one_on_ball (ψ : AddChar (v.adicCompletion ℚ) ℂ) (m : ℤ)
    (hm : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψ x = 1) : Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_)
  have hopen : IsOpen ((fun y : v.adicCompletion ℚ => y - x) ⁻¹'
      {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp m}) :=
    (isClopen_valued_le v m).isOpen.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ (fun y : v.adicCompletion ℚ => y - x) ⁻¹' {t : v.adicCompletion ℚ | Valued.v t ≤ WithZero.exp m} := by
    simp only [Set.mem_preimage, Set.mem_setOf_eq, sub_self, Valuation.map_zero]
    exact zero_le'
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hy' : ψ (y - x) = 1 := hm _ hy
  calc ψ y = ψ (x + (y - x)) := by rw [show x + (y - x) = y by ring]
    _ = ψ x * ψ (y - x) := AddChar.map_add_eq_mul ψ x (y - x)
    _ = ψ x := by rw [hy', mul_one]

open scoped Classical in

private theorem exists_isWhittakerFunctional3_ne_zero_of_apply_eq_ite (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (v.adicCompletion ℚ) ℂ) {m : ℤ}
    (hm : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψ x = 1) (f : ↥(principalSeries3 v χ))
    {c₀ : ℤ} (hc₀ : c₀ ≤ m) {C : ℂ} (hC : C ≠ 0)
    (hf : ∀ x y z : v.adicCompletion ℚ,
      (f : LocalGL3 v → ℂ) (antidiagonal3 v * upperUnipotent3 x y z) =
        if (x, y, z) ∈ unipotentBall v c₀ then C else 0) :
    ∃ L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ, L ≠ 0 ∧ IsWhittakerFunctional3 ψ L := by
  classical
  have hψ : Continuous ψ := continuous_addChar_of_eq_one_on_ball v ψ m hm
  let relations : ℤ → Submodule ℂ ↥(principalSeries3 v χ) := fun c =>
    Submodule.span ℂ {r | ∃ (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ)
      (F : ↥(principalSeries3 v χ)), q ∈ unipotentBall v c ∧
        r = ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 q.1 q.2.1 q.2.2) F,
          rightTranslate_mem_principalSeries3 F.2 (upperUnipotent3 q.1 q.2.1 q.2.2)⟩ - ψ (q.1 + q.2.1) • F}
  have hmono : Monotone relations := fun c d hcd =>
    Submodule.span_mono fun r hr => by
      obtain ⟨q, F, hq, rfl⟩ := hr
      exact ⟨q, F, unipotentBall_mono v hcd hq, rfl⟩
  have hf_notMem : f ∉ ⨆ c, relations c := by
    intro hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_iSup_of_directed relations hmono.directed_le).mp hmem
    have hc' : f ∈ relations (max c c₀) := hmono (le_max_left c c₀) hc
    have hkill : relations (max c c₀) ≤ LinearMap.ker (detectorForm v χ hψ (max c c₀)) := by
      refine Submodule.span_le.mpr ?_
      rintro r ⟨q, F, hq, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, detectorForm_apply, detectorForm_apply,
        smul_eq_mul]
      exact sub_eq_zero.mpr (detector_rightTranslate v ψ hq F.1)
    have h0 := LinearMap.mem_ker.mp (hkill hc')
    rw [detectorForm_apply, detector_eq_of_apply_eq_ite v ψ hm hc₀ (le_max_right c c₀) hf] at h0
    exact smul_ne_zero (coordHaar_real_unipotentBall_pos v c₀).ne' hC h0
  have hlt : (⨆ c, relations c) < ⊤ :=
    lt_top_iff_ne_top.mpr fun htop => hf_notMem (by rw [htop]; exact Submodule.mem_top)
  obtain ⟨L, hL0, hLmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  refine ⟨L, hL0, fun x y z F => ?_⟩
  obtain ⟨c, hc⟩ := exists_mem_unipotentBall v (x, y, z)
  have hrel : (⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) F,
      rightTranslate_mem_principalSeries3 F.2 (upperUnipotent3 x y z)⟩ - ψ (x + y) • F :
        ↥(principalSeries3 v χ)) ∈ ⨆ c, relations c :=
    Submodule.mem_iSup_of_mem c (Submodule.subset_span ⟨(x, y, z), F, hc, rfl⟩)
  have hzero : L (⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) F,
      rightTranslate_mem_principalSeries3 F.2 (upperUnipotent3 x y z)⟩ - ψ (x + y) • F) = 0 := by
    have hmem : L _ ∈ (⨆ c, relations c).map L := Submodule.mem_map_of_mem hrel
    rw [hLmap] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hzero
  exact hzero

end WhittakerDetector

end LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero.LanglandsTunnell.CubicInduction"

theorem solution (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψball : ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψv x = 1) :
    ∃ L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ, L ≠ 0 ∧ IsWhittakerFunctional3 ψv L := by
  obtain ⟨m, hm⟩ := hψball
  exact exists_isWhittakerFunctional3_ne_zero_of_apply_eq_ite v χ ψv hm
    ⟨scaledCellSection v χ m, scaledCellSection_mem_principalSeries3 v χ hχ m⟩ le_rfl
    (scaledCellValue_ne_zero v χ m) (scaledCellSection_antidiagonal3_mul_upperUnipotent3 v χ m)

end

end S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero (solution)
